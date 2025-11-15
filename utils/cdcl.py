from utils.types import Clauses
from .sat import *

class CDCL(FirstPick):
    def __init__(self, clauses: Clauses, num_vars: int):
        """
        CDCL constructor: add reason and level tracking for conflict analysis and clause learning.
        """
        super().__init__(clauses, num_vars)
        self.reason_of = {var: None for var in range(1, num_vars + 1)}
        self.level_of = {var: -1 for var in range(1, num_vars + 1)}

    def solve(self) -> tuple[str, list[int] | None]:
        """
        CDCL also has two main loops.
        Like DPLL, the first loop is about making decisions,
        and the second loop is about handling conflicts.

        CDCL differs in that conflicts are analyzed to learn new clauses,
        """
        # Run initial propagation
        if self.propagate() is not None:
            self.progress_bar.close()
            return 'UNSAT', None # Conflict at root level

        # main loop
        while True:
            decision_lit = self.pick_unassigned_literal()
            
            if decision_lit is None:
                # No unassigned vars, no conflict -> SAT
                self.progress_bar.close()
                true_vars = [i for i, v in self.assignment.items() if v == 1]
                return 'SAT', true_vars

            # Pick a decision literal post. var
            decision_lit = self.pick_unassigned_literal()
            if decision_lit is None:
                # all assigned but not solved, so it UNSAT
                self.progress_bar.close()
                return 'UNSAT', None

            # Make a decision
            self.push_decision_level(decision_lit)
            
            # Inner conflict loop
            while True:
                conflicting_clause_idx = self.propagate()
                
                if conflicting_clause_idx is None:
                    break # no conflict, keep searching
                
                learnt_clause, backjump_level = self.analyze_conflict(conflicting_clause_idx)
                
                # Conflict at root level -> UNSAT
                if backjump_level < 0:
                    self.progress_bar.close()
                    return 'UNSAT', None
                
                # Add the new clause to the knowledge base
                new_ci = self.add_clause(learnt_clause)
                
                # Backjump and assert the 1UIP
                asserting_lit = learnt_clause[0] # 1UIP is always at index 0
                self.backjump(backjump_level, new_ci, asserting_lit)

    def _assign_internal(self, lit: int, level: int, reason: int | None):
        """
        Expand internal assignment to record conflict data.
        """
        var = abs(lit)
        self.level_of[var] = level
        self.reason_of[var] = reason
        self.assign(lit, 1 if lit > 0 else -1)

    def _unassign_internal(self, var: int):
        """Overrides SATSolver.unassign to clear CDCL data."""
        self.reason_of[var] = None
        self.level_of[var] = -1
        self.unassign(var)

    def analyze_conflict(self, conflict_clause_index: int) -> tuple[list[int], int]:
        """
        Analyzes a conflict (using 1UIP) to find a new clause to learn
        and a level to backjump to.
        
        Args:
            conf_ci: The index of the clause that caused the conflict.
            
        Returns:
            Tuple[List[int], int]:
            - The new learnt clause (list of lits), with the 1UIP at index 0.
            - The level (int) to backjump to. (-1 for root conflict).
        """
        current_level = self.get_current_level()
        if current_level == 0:
            return [], -1  # Conflict at root level

        # get literals of the conflicting clause
        current_clause_lits = set(self.clauses[conflict_clause_index]) 
        
        learnt_clause_lits = set()
        
        # vars at the current level that we still need to process
        lits_at_current_level = set() 
        
        # set of all vars we've seen to avoid redundant processing
        seen_variables = set() 
        
        # level we will backjump to (the 2nd highest level in the clause)
        backjump_level = 0 
        
        for lit in current_clause_lits:
            var = abs(lit)
            seen_variables.add(var)
            if self.level_of[var] == current_level:
                lits_at_current_level.add(var)
            else:
                learnt_clause_lits.add(lit)
                backjump_level = max(backjump_level, self.level_of[var])

        # To learn from the conflict, we need to look through the assignment trail in reverse,
        # trying to find the firstUIP (Unique Implication Point).
        trail_idx = len(self.assignment_trail) - 1
        
        first_uip_lit = None  # This will hold our firstUIP

        while True:
            # Find the most recent assignment on the trail that is in our
            # "to process" set.
            lit_on_trail = self.assignment_trail[trail_idx]
            var_on_trail = abs(lit_on_trail)
            trail_idx -= 1
            
            if var_on_trail not in lits_at_current_level:
                continue # Skip variables not in the current level set

            # This is the variable we are "resolving".
            lits_at_current_level.remove(var_on_trail)
            
            # if all vars on the trail are removed, we found the first one
            if not lits_at_current_level:
                # The asserting literal is its negation.
                first_uip_lit = -lit_on_trail 
                break
            
            # --- 4. Resolve: Add reason clause lits ---
            reason_clause_index = self.reason_of[var_on_trail]
            
            for reason_literal in self.clauses[reason_clause_index]:
                reason_variable = abs(reason_literal)
                if reason_variable == var_on_trail:
                    continue  # Skip the variable we're resolving
                
                if reason_variable not in seen_variables:
                    seen_variables.add(reason_variable)
                    
                    if self.level_of[reason_variable] == current_level:
                        lits_at_current_level.add(reason_variable)
                    else:
                        learnt_clause_lits.add(reason_literal)
                        backjump_level = max(backjump_level, self.level_of[reason_variable])

        # Build Clause
        final_learnt_clause = list(learnt_clause_lits)
        
        # Put first_uip at the front as the asserting literal
        final_learnt_clause.insert(0, first_uip_lit)
        
        return final_learnt_clause, backjump_level

    def add_clause(self, clause_literals: list[int]) -> int:
        """
        Adds a new learnt clause to the solver's database.
        """
        new_clause_index = len(self.clauses)
        self.clauses.append(list(clause_literals)) # Store a new copy
        
        # Only build watchers if clause has more than 2 literals
        if len(clause_literals) >= 2:
            w1, w2 = clause_literals[0], clause_literals[1]
            self.watches[w1].append(new_clause_index)
            self.watches[w2].append(new_clause_index)
        
        return new_clause_index

    def backjump(self, backjump_level: int, learnt_clause_index: int, asserting_literal: int):
        """
        Performs a backjump.
        
        - Unwinds the decision stack and assignment trail to backjump_level.
        - Calls self.unassign() on all cleared variables.
        - Resets self.prop_index.
        - Asserts the 'asserting_literal' at the backjump_level,
          setting its reason to 'learnt_clause_index'.
        """
        
        if backjump_level == 0:
            target_trail_idx = 0 # Unassign everything
        else:
            target_trail_idx = self.level_start[backjump_level] # Start of the backjump level

        
        # Unassign everything until the target trail index
        while len(self.assignment_trail) > target_trail_idx:
            lit = self.assignment_trail.pop()
            self._unassign_internal(abs(lit))
        
        self.decisions = self.decisions[:backjump_level]
        self.level_start = self.level_start[:backjump_level]
        self.prop_index = len(self.assignment_trail)
        
        # Assert the asserting literal at the backjump level
        self._assign_internal(asserting_literal, backjump_level, learnt_clause_index)


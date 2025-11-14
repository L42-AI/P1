from utils.types import Clauses
from .sat import SATSolver

class CDCL(SATSolver):
    def __init__(self, clauses: Clauses, num_vars: int):
        super().__init__(clauses, num_vars)
        self.reason_of = {var: None for var in range(1, num_vars + 1)}
        self.level_of = {var: -1 for var in range(1, num_vars + 1)}

    def solve(self) -> tuple[str, list[int] | None]:
        """
        Overrides the parent's solve method to implement the full CDCL loop.
        
        The loop is:
        1. Propagate.
        2. If conflict -> analyze -> learn clause -> backjump. Loop to 1.
        3. If no conflict -> pick decision -> push decision. Loop to 1.
        4. If no conflict & no decision -> SAT.
        """
        # Run initial propagation at level 0
        conflicting_clause_idx = self.propagate()
        if conflicting_clause_idx is not None:
            self.progress_bar.close()
            return 'UNSAT', None # Conflict at root level

        # Main CDCL loop
        while True:
            decision_lit = self.pick_unassigned_literal()
            
            if decision_lit is None:
                # No unassigned vars, no conflict -> SAT
                self.progress_bar.close()
                true_vars = [i for i, v in self.assignment.items() if v == 1]
                return 'SAT', true_vars

            # Make a decision
            self.push_decision_level(decision_lit)
            
            # Inner conflict loop
            while True:
                conflicting_clause_idx = self.propagate()
                
                if conflicting_clause_idx is None:
                    # No conflict, break to make another decision
                    break 
                
                # --- CONFLICT DETECTED ---
                learnt_clause, backjump_level = self.analyze_conflict(conflicting_clause_idx)
                
                if backjump_level < 0:
                    # Conflict at root level (level 0)
                    self.progress_bar.close()
                    return 'UNSAT', None
                
                # Add the new clause to our database
                new_ci = self.add_clause(learnt_clause)
                
                # Backjump and assert the 1UIP
                asserting_lit = learnt_clause[0] # 1UIP is always at index 0
                self.backjump(backjump_level, new_ci, asserting_lit)
                
                # Loop again to propagate the newly asserted literal

    # --- 2. Core CDCL Components ---

    def _assign_internal(self, lit: int, level: int, reason: int | None):
        """Helper to set CDCL bookkeeping and call assign()."""
        var = abs(lit)
        self.level_of[var] = level
        self.reason_of[var] = reason
        self.assign(lit, 1 if lit > 0 else -1)

    def propagate(self) -> int | None:
        """
        Performs 2WL unit propagation and records CDCL bookkeeping.
        
        - Updates self.reason_of[var] = ci for all new propagations.
        - Updates self.level_of[var] = current_level for all new propagations.
        
        Returns:
            None if no conflict.
            int (conflicting_clause_idx) if a conflict is found.
        """
        current_level = self.get_current_level()
        
        # 1. Initial unit clauses (root-level)
        while self.unit_clause_lits:
            lit = self.unit_clause_lits.popleft()
            if self.lit_is_true(lit):
                continue
            if self.lit_is_false(lit):
                return -1 # Conflict (use a dummy index)
            
            self._assign_internal(lit, 0, None)

        # 2. Main propagation over the trail
        while self.prop_index < len(self.assignment_trail):
            lit = self.assignment_trail[self.prop_index]
            self.prop_index += 1
            falsified_lit = -lit
            
            for ci in list(self.watches[falsified_lit]):
                clause = self.clauses[ci]
                # ensure clause[0] is the falsified watch
                w1, w2 = clause[0], clause[1]
                if w1 != falsified_lit:
                    w1, w2 = w2, w1
                    clause[0], clause[1] = w1, w2
                
                if self.lit_is_true(w2):
                    continue
                    
                found_new_watch = False
                for i in range(2, len(clause)):
                    new_lit = clause[i]
                    if not self.lit_is_false(new_lit):
                        self.watches[w1].remove(ci)
                        self.watches[new_lit].append(ci)
                        clause[0], clause[i] = new_lit, w1
                        found_new_watch = True
                        break
                
                if found_new_watch:
                    continue 
                    
                # No new watcher found
                if self.lit_is_unassigned(w2):
                    # Unit clause! Propagate w2.
                    self._assign_internal(w2, current_level, ci)
                
                elif self.lit_is_false(w2):
                    # Conflict!
                    return ci 
        
        return None # No conflict

    def analyze_conflict(self, conf_ci: int) -> tuple[list[int], int]:
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

        # --- 1. Initialize ---
        # lits from the conflicting clause
        current_clause_lits = set(self.clauses[conf_ci]) 
        
        # lits for the new clause we are learning
        learnt_clause_lits = set()
        
        # vars at the current level that we still need to process
        lits_at_current_level = set() 
        
        # set of all vars we've seen to avoid redundant processing
        seen_vars = set() 
        
        # level we will backjump to (the 2nd highest level in the clause)
        backjump_level = 0 
        
        for lit in current_clause_lits:
            var = abs(lit)
            seen_vars.add(var)
            if self.level_of[var] == current_level:
                lits_at_current_level.add(var)
            else:
                learnt_clause_lits.add(lit)
                backjump_level = max(backjump_level, self.level_of[var])

        # --- 2. Resolve backward through the trail ---
        # We start from the end of the assignment trail and work backward
        trail_idx = len(self.assignment_trail) - 1
        
        uip_lit = None  # This will hold our 1UIP

        while True:
            # Find the most recent assignment on the trail that is in our
            # "to process" set.
            lit_on_trail = self.assignment_trail[trail_idx]
            var_on_trail = abs(lit_on_trail)
            trail_idx -= 1
            
            if var_on_trail not in lits_at_current_level:
                continue

            # This is the variable we are "resolving".
            lits_at_current_level.remove(var_on_trail)
            
            # --- 3. Check for 1UIP ---
            if not lits_at_current_level:
                # This is the 1UIP!
                # It's the *first* (working backward) variable that,
                # once resolved, leaves no other lits from the current level.
                # The asserting literal is its negation.
                uip_lit = -lit_on_trail 
                break
            
            # --- 4. Resolve: Add reason clause lits ---
            reason_ci = self.reason_of[var_on_trail]
            
            for r_lit in self.clauses[reason_ci]:
                r_var = abs(r_lit)
                if r_var == var_on_trail:
                    continue  # Skip the variable we're resolving
                
                if r_var not in seen_vars:
                    seen_vars.add(r_var)
                    
                    if self.level_of[r_var] == current_level:
                        lits_at_current_level.add(r_var)
                    else:
                        learnt_clause_lits.add(r_lit)
                        backjump_level = max(backjump_level, self.level_of[r_var])

        # --- 5. Construct final clause ---
        final_learnt_clause = list(learnt_clause_lits)
        
        # Put the asserting 1UIP literal at index 0.
        # This is a common convention that add_clause/backjump will rely on.
        final_learnt_clause.insert(0, uip_lit)
        
        return final_learnt_clause, backjump_level

    def add_clause(self, clause_lits: list[int]) -> int:
        """
        Adds a new learnt clause to the solver's database.
        
        - Appends the clause to self.clauses.
        - Sets up the 2WL watchers for the new clause.
        
        Returns:
            int: The index (ci) of the newly added clause.
        """
        new_ci = len(self.clauses)
        self.clauses.append(list(clause_lits)) # Store a new copy
        
        # We only need to set up watchers if the clause has 2 or more literals.
        # If len == 1, it's an asserting clause. backjump() will
        # assign it, and propagate() will handle it from the trail.
        if len(clause_lits) >= 2:
            # Watch the 1UIP (index 0) and the literal at index 1.
            # The propagation invariant will be maintained.
            w1, w2 = clause_lits[0], clause_lits[1]
            self.watches[w1].append(new_ci)
            self.watches[w2].append(new_ci)
        
        return new_ci

    def backjump(self, backjump_level: int, learnt_clause_ci: int, asserting_lit: int):
        """
        Performs a non-chronological backtrack.
        
        - Unwinds the decision stack and assignment trail to backjump_level.
        - Calls self.unassign() on all cleared variables.
        - Resets self.prop_index.
        - Asserts the 'asserting_lit' at the backjump_level,
          setting its reason to 'learnt_clause_ci'.
        """
        
        # --- 1. Find the trail index to jump to ---
        # We need to unassign all variables assigned *after* this level.
        # `backjump_level` is 0 for root, 1 for first decision, etc.
        # `self.level_start[k]` stores the trail index where level k+1 *began*.
        
        if backjump_level == 0:
            target_trail_idx = 0 # Unassign everything
        else:
            # We jump TO level `backjump_level`. We want to keep all
            # assignments from level 0 up to and including `backjump_level`.
            # `self.level_start[backjump_level - 1]` is the decision for level `backjump_level`.
            # `self.level_start[backjump_level]` is the decision for level `backjump_level + 1`.
            # We want to undo back to the *start* of the *next* level.
            target_trail_idx = self.level_start[backjump_level]

        
        # --- 2. Unwind assignment trail ---
        # Unassign all variables from the end of the trail
        # back to the target index.
        while len(self.assignment_trail) > target_trail_idx:
            lit = self.assignment_trail.pop()
            self.unassign(abs(lit))
        
        # --- 3. Unwind decision/level stacks ---
        # Trim the stacks to the correct level
        self.decisions = self.decisions[:backjump_level]
        self.level_start = self.level_start[:backjump_level]
        
        # --- 4. Reset propagation queue ---
        # The propagation index should now point to the end of the
        # *new* trail. The asserting lit will be added *after* this.
        self.prop_index = len(self.assignment_trail)
        
        # --- 5. Assert the 1UIP (asserting_lit) ---
        # This is the "unit propagation" forced by the new clause.
        var = abs(asserting_lit)
        
        # We set the level to the level we jumped to.
        self.level_of[var] = backjump_level
        self.reason_of[var] = learnt_clause_ci
        self.assign(asserting_lit, 1 if asserting_lit > 0 else -1)

    # --- 3. Bookkeeping Helpers ---

    def push_decision_level(self, lit: int):
        """
        Makes a new decision.
        
        - Records the decision in self.decisions and self.level_start.
        - Sets self.level_of[var] = new_level.
        - Sets self.reason_of[var] = None.
        - Calls self.assign() to assign the literal.
        """
        current_level_idx = self.get_current_level()
        new_level = current_level_idx + 1 # Levels are 1-based
        
        self.level_start.append(len(self.assignment_trail))

        var = abs(lit)
        self.decisions.append({'var': var, 'tried_false': (lit < 0)})

        # Set CDCL bookkeeping for the decision
        self.reason_of[var] = None # Decisions have no reason
        self.level_of[var] = new_level
        
        self.assign(lit, 1 if lit > 0 else -1) 
        self.progress_bar.explored += 1
        # self.progress_bar.update(self.assignment) # assign() already does this

    def unassign(self, var: int):
        """Overrides SATSolver.unassign to clear CDCL data."""
        if self.assignment[var] == 0:
            return
            
        # Clear the CDCL-specific "bookkeeping"
        self.reason_of[var] = None
        self.level_of[var] = -1
        
        # Call the parent's unassign logic
        super().unassign(var)
    
    def get_current_level(self) -> int:
        """Returns the current decision level (1-based index)."""
        # Level 0 = root, Level 1 = first decision, etc.
        return len(self.decisions)

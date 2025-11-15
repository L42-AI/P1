
from utils.types import Clause

from .sat import *

class DPLL(FirstPick):

    def process_initial_unit_clauses(self) -> bool:
        while self.unit_clause_lits:
            lit = self.unit_clause_lits.popleft()
            
            # Check for consistency
            if self.lit_is_true(lit):
                continue  # Already assigned, no problem
            if self.lit_is_false(lit):
                return False  # Conflict: (X) and (-X) are both unit clauses
            
            # Assign the new literal. This adds it to the assignment_trail,
            # where the main propagate() loop will pick it up.
            self.assign(lit, 1 if lit > 0 else -1)
        return True

    def _find_new_watcher_for_clause(self, clause: Clause, falsified_watcher: int, clause_index: int) -> bool:
        for i in range(2, len(clause)): # Start searching from index 2. The first two (0, 1) are the watchers.
            new_lit = clause[i]
            
            # We are looking for any literal that is NOT False.
            # (It can be True or Unassigned)
            if not self.lit_is_false(new_lit):
                
                # Stop watching w1
                self.watches[falsified_watcher].remove(clause_index)
                
                # Start watching new_lit
                self.watches[new_lit].append(clause_index)
                
                # Update the clause: swap new_lit into w1's spot
                clause[0], clause[i] = new_lit, falsified_watcher
                
                return True  
                
        return False
    
    def propagate(self) -> bool:
        """
        Performs unit propagation based on the 2-Watched Literals scheme.
        Returns True if propagation is successful, False if a conflict is found.
        """
        
        if not self.process_initial_unit_clauses():
            return False

        # One propagation run is until the prop_index reaches the end of the current assignment trail
        while self.prop_index < len(self.assignment_trail):
            # Get the next assigned literal from the trail
            lit = self.assignment_trail[self.prop_index]
            self.prop_index += 1
            
            # The literal that is falsified is the opposite of the assigned one
            falsified_lit = -lit
            
            # Loop over copy to avoid changing during runtime
            for ci in list(self.watches[falsified_lit]):
                clause = self.clauses[ci]
                w1, w2 = clause[0], clause[1]
                
                # Put falsified_lit in first watcher position
                if w1 != falsified_lit:
                    w1, w2 = w2, w1 # Swap them
                    clause[0], clause[1] = w1, w2 # Sync with clause
                
                # If w2 is true, the clause is automically true and we can ignore logic
                if self.lit_is_true(w2):
                    continue
                    
                found_new_watch = self._find_new_watcher_for_clause(clause, w1, ci)
                
                if found_new_watch:
                    continue # We're done with this clause
                    
                if self.lit_is_unassigned(w2):
                    self.assign(w2, 1 if w2 > 0 else -1)
                
                elif self.lit_is_false(w2):
                    return False
        
        return True # Propagation finished with no conflicts
            
    def push_decision_level(self, lit: int):
        # Know where level starts in the assignment trail
        self.level_start.append(len(self.assignment_trail))

        # Remember the decision literal
        var = abs(lit)
        tried_false = (lit < 0) # if literal is negative, we are trying false first
        self.decisions.append({'var': var, 'tried_false': tried_false})

        # Assign the decision literal the correct sign
        val = 1 if lit > 0 else -1
        self.assign(lit, val)

        self.progress_bar.explored += 1
        self.progress_bar.update(self.assignment)

    def backtrack(self) -> bool:
        if not self.decisions:
            return False  # nothing to backtrack as UNSAT
        
        # Pop last decision and its level start
        decision = self.decisions.pop()
        level_start_index = self.level_start.pop()

        # Undo assignments at and after this level start
        while len(self.assignment_trail) > level_start_index:
            lit = self.assignment_trail.pop()
            self.unassign(abs(lit))

        self.prop_index = level_start_index

        # If we have not tried teh False decision, do it now
        if not decision['tried_false']:
            # introduce level for this flipped decision
            self.level_start.append(len(self.assignment_trail))
            decision['tried_false'] = True
            self.decisions.append(decision)

            # Assign the var to false (negative literal)
            var = decision['var']
            self.assign(-var, -1)
            return True  # backtrack successful, flipped decision
        
        self.progress_bar.explored += 1
        self.progress_bar.update(self.assignment)

        # Both decision tried, go back further with backtracking
        return self.backtrack()
        
    def solve(self) -> tuple[str, list[int] | None]:

        # Run initial propagation
        if not self.propagate():
            return 'UNSAT', None
        
        while True:
            # If solved, return the model
            decision_lit = self.pick_unassigned_literal()
            if decision_lit is None:
                # All variables are assigned and no conflicts found
                true_vars = [i for i, v in self.assignment.items() if v == 1]
                return 'SAT', true_vars
            
            # Pick a decision literal post. var
            decision_lit = self.pick_unassigned_literal()
            if decision_lit is None:
                # all assigned but not solved, so it UNSAT
                return 'UNSAT', None
            
            # Decide post. var and propagate
            self.push_decision_level(decision_lit)
            if self.propagate():
                continue  # no conflict, keep searching

            # Conflict due to propagation, backtrack until flip or no more decisions
            while True:
                flipped = self.backtrack()
                if not flipped:
                    return 'UNSAT', None  # no more decisions to backtrack, UNSAT
                
                if self.propagate():
                    break  # flipped branch is successful with backtrack and propagate, continue main loop

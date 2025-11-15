
from utils.types import Clause

from .sat import *

class DPLL(FirstPick):
    
    def solve(self) -> tuple[str, list[int] | None]:
        """
        DPLL solving procedure
        """

        # Run initial propagation
        if not self.propagate():
            self.progress_bar.close()
            return 'UNSAT', None # Conflict at root level
        
        while True:
            # If solved, return the model
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

            # Conflict due to propagation, backtrack until flip or no more decisions
            while True:
                if self.propagate():
                    break  # no conflict, keep searching

                if not self.backtrack():
                    self.progress_bar.close()
                    return 'UNSAT', None  # no more decisions to backtrack, UNSAT

    def propagate(self) -> bool:
        """
        Performs 2WL based unit propagation.
        Return True if no conflict found, False otherwise.
        """
        return super().propagate() is None

    def backtrack(self) -> bool:
        if not self.decisions:
            return False  # nothing to backtrack as UNSAT
        
        # Pop last decision and its level start
        decision = self.decisions.pop()
        level_start_index = self.level_start.pop()

        # Undo assignments at and after this level start
        while len(self.assignment_trail) > level_start_index:
            lit = self.assignment_trail.pop()
            self._unassign_internal(abs(lit))

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
        
        self.progress_bar.update(self.assignment)

        # Both decision tried, go back further with backtracking
        return self.backtrack()
        
from collections import deque
from abc import abstractmethod, ABC
import random as r

# from utils.progress_bar import ProgressBar
from utils.types import Clauses, Clause

__all__ = [
    'FirstPick',
    'LastPick',
    'RandomPick',
    'HeuristicPick',
]

class MockProgressBar:
    def __init__(self, num_vars: int, on: bool = True):
        pass

    def update(self, assignment: dict[int, int]):
        pass

    def close(self):
        pass

class SATSolver(ABC):
    clauses: Clauses
    assignment: dict[int, int]
    assignment_trail: deque[int]
    decisions: list[int]
    level_start: list[int]

    watches: dict[int, list[int]]
    prop_index: int

    progress_bar: MockProgressBar

    def __init__(self, clauses: Clauses, num_vars: int):
        """
        Initialize base solver.
        - Set up assignment setting logic; setting dict, trail and decisions cacher
        - Set up 2WL watchers and propagation index for efficient unit propagation
        - Initialize progress bar

        - Build unit_clause_lits deque for initial unit clause processing
        """

        self.clauses = [list(c) for c in clauses]

        # Initialize assignment structures
        self.assignment = {var: 0 for var in range(1, num_vars + 1)}
        self.assignment_trail = deque()
        self.decisions = []

        # Set up 2-Watched Literals data structures
        self.watches = {lit: [] for lit in range(-num_vars, num_vars + 1) if lit != 0}
        self.prop_index = 0
        self.level_start = []

        self.unit_clause_lits = deque()

        # Initialize progress bar
        self.progress_bar = MockProgressBar(num_vars, on=False)
        self.progress_bar.update(self.assignment)

        # Save clause indexes being watched
        # Save clause values into unit_clause_lits to process initially
        for clause_index, clause in enumerate(self.clauses):

            # Make CNF impossible by adding contradiction
            if len(clause) == 0:
                self.unit_clause_lits.append(1)
                self.unit_clause_lits.append(-1)
                continue

            # Save unit clause literals for initial processing
            if len(clause) == 1:
                self.unit_clause_lits.append(clause[0])
                continue

            # Setup watchers for clauses with >= 2 literals
            first_literal, second_literal = clause[0], clause[1]
            self.watches[first_literal].append(clause_index)
            self.watches[second_literal].append(clause_index)

    def assign(self, variable: int, value: int) -> int:
        """
        Assign a value to a variable.

        - Update assignment dict and trail accordingly.
        - Update progress bar.
        """
        var = abs(variable)

        self.assignment[var] = value

        self.assignment_trail.append(variable)
        self.progress_bar.update(self.assignment)
        return var

    def unassign(self, variable: int):
        """
        Unassign a variable.

        - Update assignment dict accordingly.
        - Update progress bar.
        """

        self.assignment[variable] = 0
        self.progress_bar.update(self.assignment)


    def lit_is_true(self, lit: int) -> bool:
        """
        Check if a literal is currently assigned True.
        """
        val = self.assignment[abs(lit)]
        return val == (1 if lit > 0 else -1)

    def lit_is_false(self, lit: int) -> bool:
        """
        Check if a literal is currently assigned False.
        """
        val = self.assignment[abs(lit)]
        return val == (-1 if lit > 0 else 1)

    def lit_is_unassigned(self, lit: int) -> bool:
        """
        Check if a literal is currently unassigned.
        """
        return self.assignment[abs(lit)] == 0

    def _assign_internal(self, lit: int, level: int, reason: int | None):
        """
        helper to assign a literal during propagation.
        expanded in cdcl
        """
        self.assign(lit, 1 if lit > 0 else -1)

    def _unassign_internal(self, var: int):
        """
        helper to unassign a literal during backtracking.
        expanded in cdcl
        """
        self.unassign(var)

    def process_initial_unit_clauses(self) -> bool:
        """
        Process initial unit clauses before main propagation loop.
        Returns False if a conflict is detected, True otherwise.
        """
        while self.unit_clause_lits:
            lit = self.unit_clause_lits.popleft()
            
            # Check for consistency
            if self.lit_is_true(lit):
                continue  # Already assigned, no problem
            if self.lit_is_false(lit):
                return False  # Conflict: (X) and (-X) are both unit clauses
            
            # Assign the new literal. This adds it to the assignment_trail,
            # where the main propagate() loop will pick it up.
            self._assign_internal(lit, 0, None)
        return True

    def _find_new_watcher_for_clause(self, clause: Clause, falsified_watcher: int, clause_index: int) -> bool:
        """
        Helper function to find new watcher for a clause if possible.
        returns True if new watcher found, False otherwise.
        """
       
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

    def get_current_level(self) -> int:
        """
        Get the current decision level.
        """
        return len(self.decisions)

    def propagate(self) -> int | None:
        """
        Performs 2WL based unit propagation.
        
        Returns:
            None if no conflict.
            int (conflicting_clause_index) if a conflict is found.
        """

        if not self.process_initial_unit_clauses():
            return -1  # Conflict detected during initial unit clause processing

        current_level = self.get_current_level()
        
        # Propagation over the trail
        while self.prop_index < len(self.assignment_trail):
            lit = self.assignment_trail[self.prop_index]
            self.prop_index += 1
            falsified_lit = -lit
            
            for clause_index in list(self.watches[falsified_lit]):
                clause = self.clauses[clause_index]

                # ensure clause[0] is the falsified watch
                w1, w2 = clause[0], clause[1]
                if w1 != falsified_lit:
                    w1, w2 = w2, w1
                    clause[0], clause[1] = w1, w2
                
                if self.lit_is_true(w2):
                    continue
                    
                found_new_watch = self._find_new_watcher_for_clause(clause, w1, clause_index)
                
                if found_new_watch:
                    continue 
                    
                # No new watcher found
                if self.lit_is_unassigned(w2):
                    # Unit clause! Propagate w2.
                    self._assign_internal(w2, current_level, clause_index)
                
                elif self.lit_is_false(w2):
                    # Conflict!
                    return clause_index 
        
        return None # No conflict


    def push_decision_level(self, lit: int):
        """
        Makes a new decision.
        
        - Records the decision in self.decisions and self.level_start.
        - Sets self.level_of[var] = new_level.
        - Sets self.reason_of[var] = None.
        - Calls self.assign() to assign the literal.
        """
        current_level_idx = self.get_current_level()
        
        self.level_start.append(len(self.assignment_trail))

        var = abs(lit)
        self.decisions.append({'var': var, 'tried_false': (lit < 0)})
        
        self._assign_internal(lit, current_level_idx + 1, None) # Levels are 1-based
        self.progress_bar.update(self.assignment) # assign() already does this

    @abstractmethod
    def pick_unassigned_literal(self) -> int | None:
        """
        Abstract method to pick an unassigned literal.
        """
        raise NotImplementedError

    @abstractmethod
    def solve(self) -> tuple[str, list[int] | None]:
        """
        Abstract method to solve the SAT problem.
        """
        raise NotImplementedError

class FirstPick(SATSolver):
    def pick_unassigned_literal(self) -> int | None:
        """
        Pick the first unassigned literal.
        """
        for var, val in self.assignment.items():
            if val == 0:
                return var 
        return None
    
class LastPick(SATSolver):
    def pick_unassigned_literal(self) -> int | None:
        """
        Pick the last unassigned literal.
        """
        for var, val in reversed(self.assignment.items()):
            if val == 0:
                return var
        return None
    
class RandomPick(SATSolver):
    def pick_unassigned_literal(self) -> int | None:
        """
        Pick a random unassigned literal.
        """
        unassigned_vars = [var for var, val in self.assignment.items() if val == 0]
        if not unassigned_vars:
            return None
        return r.choice(unassigned_vars)

class HeuristicPick(SATSolver):
    phase: dict[int, int]
    var_frequency: dict[int, int]
    
    def __init__(self, clauses: Clauses, num_vars: int):
        """
        Initialize heuristic-based solver.
        """
        super().__init__(clauses, num_vars)

        # Frequency heuristic: count how often each variable appears
        self.var_frequency = {i: 0 for i in range(1, num_vars + 1)}
        for clause in self.clauses:
            for lit in clause:
                v = abs(lit)
                self.var_frequency[v] += 1

        # Phase saving: remember last assigned polarity
        self.phase = {i: 1 for i in range(1, num_vars + 1)}

    def assign(self, variable: int, value: int):
        """
        Assign a value to a variable with phase saving.
        """
        var = super().assign(variable, value)
        self.phase[var] = value
        return var
    
    def pick_unassigned_literal(self) -> int | None:
        """
        Frequency + phase saving heuristic:
        - pick variable with highest frequency among unassigned vars
        - choose polarity using phase saving
        """
        best_var = None
        best_score = -1

        for var, val in self.assignment.items():
            if val != 0:
                continue

            score = self.var_frequency[var]
            if score > best_score:
                best_score = score
                best_var = var

        if best_var is None:
            return None

        # use phase saving for the sign
        return best_var * self.phase.get(best_var, 1)
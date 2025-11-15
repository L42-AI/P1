from collections import deque
from abc import abstractmethod, ABC

from utils.progress_bar import ProgressBar
from utils.types import Clauses

__all__ = [
    'FirstPick',
    'LastPick',
    'RandomPick',
    'HeuristicPick',
]

class SATSolver(ABC):
    def __init__(self, clauses: Clauses, num_vars: int):
        self.clauses = [list(c) for c in clauses]

        self.assignment = {var: 0 for var in range(1, num_vars + 1)}
        self.assignment_trail = deque()
        self.level_start = []
        self.decisions = []

        self.watches = {lit: [] for lit in range(-num_vars, num_vars + 1) if lit != 0}
        self.unit_clause_lits = deque()
        self.prop_index = 0

        self.progress_bar = ProgressBar(num_vars, on=True)
        self.progress_bar.update(self.assignment)

        for ci, clause in enumerate(self.clauses):
            if len(clause) == 0:
                # Handle empty clause -> immediately UNSAT
                self.unit_clause_lits.append(1)
                self.unit_clause_lits.append(-1)
                continue

            if len(clause) == 1:
                self.unit_clause_lits.append(clause[0])
                continue

            # Setup watchers for clauses with >= 2 literals
            w1, w2 = clause[0], clause[1]
            self.watches[w1].append(ci)
            self.watches[w2].append(ci)

    def assign(self, variable: int, value: int):
        var = abs(variable)

        self.assignment[var] = value

        self.assignment_trail.append(variable)
        self.progress_bar.update(self.assignment)
        return var

    def unassign(self, var: int):
        if self.assignment[var] == 0:
            return

        self.assignment[var] = 0
        self.progress_bar.update(self.assignment)

    def lit_is_true(self, lit: int) -> bool:
        val = self.assignment[abs(lit)]
        return val == (1 if lit > 0 else -1)

    def lit_is_false(self, lit: int) -> bool:
        val = self.assignment[abs(lit)]
        return val == (-1 if lit > 0 else 1)

    def lit_is_unassigned(self, lit: int) -> bool:
        return self.assignment[abs(lit)] == 0

    @abstractmethod
    def pick_unassigned_literal(self) -> int | None:
        raise NotImplementedError

class FirstPick(SATSolver):
    def pick_unassigned_literal(self) -> int | None:
        for var, val in self.assignment.items():
            if val == 0:
                return var  # always return positive literal
        return None
    
class LastPick(SATSolver):
    def pick_unassigned_literal(self) -> int | None:
        for var, val in reversed(self.assignment.items()):
            if val == 0:
                return var  # always return positive literal
        return None
    
class RandomPick(SATSolver):
    import random

    def pick_unassigned_literal(self) -> int | None:
        unassigned_vars = [var for var, val in self.assignment.items() if val == 0]
        if not unassigned_vars:
            return None
        return self.random.choice(unassigned_vars)

class HeuristicPick(SATSolver):
    def __init__(self, clauses: Clauses, num_vars: int):
        super().__init__(clauses, num_vars)

        # Frequency heuristic: count how often each variable appears
        self.var_frequency: dict[int, int] = {i: 0 for i in range(1, num_vars + 1)}
        for clause in self.clauses:
            for lit in clause:
                v = abs(lit)
                self.var_frequency[v] += 1

        # Phase saving (no JW)
        self.phase: dict[int, int] = {i: 1 for i in range(1, num_vars + 1)}

    def assign(self, variable: int, value: int):
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
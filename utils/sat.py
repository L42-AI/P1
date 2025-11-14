from collections import deque

from utils.progress_bar import ProgressBar
from utils.types import Clauses

class SATSolver:
    def __init__(self, clauses: Clauses, num_vars: int):
        self.clauses = [list(c) for c in clauses]

        self.assignment = {var: 0 for var in range(1, num_vars + 1)}
        self.assignment_trail = deque()
        self.level_start = []
        self.decisions = []

        self.watches = {lit: [] for lit in range(-num_vars, num_vars + 1) if lit != 0}
        self.unit_clause_lits = deque()
        self.prop_index = 0

        self.progress_bar = ProgressBar(num_vars, on=False)
        self.progress_bar.update(self.assignment)

        for ci, clause in enumerate(self.clauses):
            if len(clause) == 0:
                # Handle empty clause -> immediately UNSAT
                # We add a conflicting unit clause pair (e.g., [1], [-1])
                self.unit_clause_lits.append(1)
                self.unit_clause_lits.append(-1)
                continue

            if len(clause) == 1:
                # Handle unit clause
                self.unit_clause_lits.append(clause[0])
                continue
            
            # Clause has 2 or more literals. Set up watchers.
            # Watchers are always at index 0 and 1.
            w1, w2 = clause[0], clause[1]
            self.watches[w1].append(ci)
            self.watches[w2].append(ci)

        # Precompute hoe vaak elke variabele voorkomt (positief + negatief)
        self.var_frequency: dict[int, int] = {i: 0 for i in range(1, num_vars + 1)}
        for clause in self.clauses:
            for lit in clause:
                v = abs(lit)
                self.var_frequency[v] += 1



    def assign(self, variable: int, value: int):
        self.assignment[abs(variable)] = value

        self.assignment_trail.append(variable)
        
        self.progress_bar.update(self.assignment)

    def unassign(self, var: int):
        if self.assignment[var] == 0:
            return
        
        self.assignment[var] = 0

        self.progress_bar.update(self.assignment)

    def lit_is_true(self, lit: int) -> bool:
        """Returns True if the literal is satisfied by the current assignment."""
        val = self.assignment[abs(lit)]
        return val == (1 if lit > 0 else -1)

    def lit_is_false(self, lit: int) -> bool:
        """Returns True if the literal is falsified by the current assignment."""
        val = self.assignment[abs(lit)]
        return val == (-1 if lit > 0 else 1)

    def lit_is_unassigned(self, lit: int) -> bool:
        """Returns True if the literal is not yet assigned."""
        return self.assignment[abs(lit)] == 0

    def pick_unassigned_literal(self) -> int | None:
        """
        Goedkope heuristic:
        - kies de nog niet geassigneerde variabele met de hoogste var_frequency
          (dus die in de meeste clauses voorkomt).
        - we nemen gewoon de positieve literal (True) als eerste keuze.
        """

        best_var = None
        best_score = -1

        for var, val in self.assignment.items():
            if val != 0:
                continue  # al geassigned

            score = self.var_frequency.get(var, 0)
            if score > best_score:
                best_score = score
                best_var = var

        if best_var is None:
            return None  # alles geassigned

        return best_var  # positieve literal als decision


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

        self.progress_bar = ProgressBar(num_vars, on=True)
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
        Kies een decision literal met een simpele DLCS-achtige heuristic:

        - Voor elke on-geassigneerde variabele v:
            * tel hoe vaak v positief voorkomt in nog niet-gesatisficede clauses
            * tel hoe vaak v negatief voorkomt in nog niet-gesatisficede clauses
            * score = pos + neg
        - Kies v met grootste score.
        - Kies sign:
            * als pos >= neg -> literal = +v
            * anders -> literal = -v

        Geeft een literal (met sign) terug, of None als alles al geassignd is.
        """

        best_var: int | None = None
        best_score = -1
        best_sign = 1  # 1 = positief, -1 = negatief

        for var, val in self.assignment.items():
            if val != 0:
                continue  # al geassignd

            pos = 0
            neg = 0

            # Loop over clauses en tel alleen in clauses die nog niet satisfied zijn
            for clause in self.clauses:
                # als clause al satisfied is, heeft hij geen impact meer
                if any(self.lit_is_true(l) for l in clause):
                    continue

                for lit in clause:
                    if abs(lit) != var:
                        continue
                    if lit > 0:
                        pos += 1
                    else:
                        neg += 1

            score = pos + neg
            if score > best_score:
                best_score = score
                best_var = var
                best_sign = 1 if pos >= neg else -1

        if best_var is None:
            # geen on-geassigneerde variabelen meer
            return None

        # Geef een literal terug, niet alleen de variabele:
        return best_var if best_sign == 1 else -best_var


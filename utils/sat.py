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

        # Precompute hoe vaak elke variabele voorkomt (positief + negatief)
        self.var_frequency: dict[int, int] = {i: 0 for i in range(1, num_vars + 1)}
        for clause in self.clauses:
            for lit in clause:
                v = abs(lit)
                self.var_frequency[v] += 1

        # Phase saving: onthoud de laatst gebruikte "richting" per variabele
        # 1 = True, -1 = False. Initieel gewoon allemaal True.
        self.phase: dict[int, int] = {i: 1 for i in range(1, num_vars + 1)}

        # Jeroslow–Wang weights per literal sign
        self.pos_weight: dict[int, float] = {i: 0.0 for i in range(1, num_vars + 1)}
        self.neg_weight: dict[int, float] = {i: 0.0 for i in range(1, num_vars + 1)}

        for clause in self.clauses:
            # shorter clauses get higher weight
            w = 2.0 ** (-len(clause))
            for lit in clause:
                v = abs(lit)
                if lit > 0:
                    self.pos_weight[v] += w
                else:
                    self.neg_weight[v] += w

    def assign(self, variable: int, value: int):
        var = abs(variable)

        # zet de assignment
        self.assignment[var] = value

        # phase saving: onthoud de laatst gebruikte kant (True/False)
        self.phase[var] = value  # 1 voor True, -1 voor False

        # trail voor backtracking
        self.assignment_trail.append(variable)

        # optioneel: voor performance kun je deze later uitzetten
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
        Jeroslow–Wang + phase saving:

        - score(v) = pos_weight[v] + neg_weight[v]
          (variables that occur in many short clauses get higher score)
        - pick variable with highest score among unassigned vars
        - polarity = last used phase (phase saving)
        """

        best_var = None
        best_score = -1.0

        for var, val in self.assignment.items():
            if val != 0:
                continue  # already assigned

            # JW score: positive + negative weight
            score = self.pos_weight[var] + self.neg_weight[var]
            if score > best_score:
                best_score = score
                best_var = var

        if best_var is None:
            return None  # all assigned

        # use phase saving for sign (1 = True, -1 = False)
        phase = self.phase.get(best_var, 1)
        return best_var * phase




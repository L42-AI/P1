"""
SAT Assignment Part 2 - Non-consecutive Sudoku Solver (Puzzle -> SAT/UNSAT)

THIS is the file to edit.

Implement: solve_cnf(clauses) -> (status, model_or_None)"""

from typing import Iterable, List, Tuple
from collections import deque

Clause = Iterable[int]
Clauses = Iterable[Clause]

def flip(value: int) -> int:
    """
    Logical negation for values in the set {1, -1}.

    The project uses 1 for True and -1 for False. This helper returns the
    negated value (so flip(1) == -1 and flip(-1) == 1). The original code
    had a bug that always returned -1; we've fixed that to return -value.
    """
    return -value 

class SATSolver:
    def __init__(self, clauses: Clauses, num_vars: int):
        # Keep the clauses reference. Clauses may be any iterable of iterables.
        self.clauses = clauses

        # assignment[var] = 0 (unassigned), 1 (True), -1 (False)
        self.assignment = {var: 0 for var in range(1, num_vars + 1)}

        # trail of assigned signed literals (example: 5 means var 5 set True,
        # -3 means var 3 set False). This can be used later for backtracking.
        self.assignment_trail = deque()

    def _assign(self, variable: int, value: int):
        """
        Assign a variable to a value (1 or -1).

        Parameter `variable` may be a signed literal (e.g. -3 or 4). We take
        abs(variable) as the variable index and store `value` in
        `self.assignment`.
        """
        self.assignment[abs(variable)] = value
        self.assignment_trail.append(abs(variable) * value)
    
    def element_true(self, variable: int) -> bool:
        """
        Return True if the literal `variable` is currently satisfied by the
        current assignment.

        A literal is satisfied when:
        - it is a positive literal (x) and assignment[x] == 1
        - it is a negative literal (-x) and assignment[x] == -1
        """
        val = self.assignment[abs(variable)]

        if val == 0:
            return False
        
        if val == 1 and variable > 0:
            return True
        
        if val == -1 and variable < 0:
            return True
        
        return False

    def clause_is_true(self, clause: Clause) -> bool:
        """Return True if at least one literal in `clause` is satisfied."""
        for element in clause:
            if self.element_true(element):
                return True
        return False

    def get_pending_variables(self, clause: Clause) -> set[int]:
        """
        Return the set of unassigned literals (signed) present in `clause`.

        We return the signed literals so that unit propagation can directly use
        the sign to decide which value to assign.
        """
        pending_variables = set()
        for element in clause:
            if self.assignment[abs(element)] == 0:
                pending_variables.add(element)

        return pending_variables
    
class CDCL(SATSolver):
    pass

class DPLL(SATSolver):
    """
    Minimal DPLL-style SAT solver.

    Attributes
    - clauses: iterable of clauses; each clause is an iterable of ints where
      a positive int x represents variable x, and negative int -x represents
      ¬x.
    - assignment: dict mapping variable index -> {0, 1, -1} where 0 is
      unassigned, 1 is True, -1 is False.
    - assignment_trail: deque recording the literal assignments in order. Values
      pushed are signed integers representing the literal assigned (positive
      means variable set True, negative means set False).

    Limitations / TODOs
    - No decision heuristic (no branching): this solver only performs unit
      propagation and then checks for satisfaction. For many CNFs this will
      not be sufficient to find a satisfying assignment.
    - No conflict analysis or backtracking implemented.
    """

    def propagate(self):
        """
        Perform unit propagation until fixpoint.

        For every clause not yet satisfied, if it has exactly one unassigned
        literal then that literal must be set to make the clause true. We
        iterate until no new propagation occurs.
        """
        must_propagate = False
        for clause in self.clauses:
            # If the clause is already satisfied, skip it.
            if self.clause_is_true(clause):
                continue

            pending_variables = self.get_pending_variables(clause)

            # If a clause has exactly one pending literal, that literal must
            # become True (so assign it accordingly). We translate the signed
            # literal to a stored value: literal < 0 -> assign -1, else 1.
            if len(pending_variables) == 1:
                v = list(pending_variables)[0]
                self._assign(v, -1 if v < 0 else 1)
                must_propagate = True

        # Recurse/loop until no more unit propagation is possible.
        if not must_propagate:
            return

        self.propagate()

    def is_solved(self) -> bool:
        """
        Check whether all clauses are satisfied under the current
        assignment.

        This is an expensive check (scans all clauses) but acceptable for this
        small educational solver.
        """
        for clause in self.clauses:
            if not self.clause_is_true(clause):
                return False
        return True

    def solve(self) -> Tuple[str, List[int] | None]:
        """
        Attempt to solve the CNF using unit propagation only.

        Returns:
        - ('SAT', model) where model is a list of variables that are True
          (represented by their variable indices) when a satisfying
          assignment is found.
        - ('UNSAT', None) if unsatisfiable.

        Note: This method currently does not implement a full DPLL search
        (no decisions/backtracking). It only applies unit propagation and
        then tests for satisfaction. For many CNFs this will return no result
        even though the CNF is satisfiable; extending this to a full DPLL
        search is a recommended next step.
        """
        is_solved = False
        must_propagate = True
        while not is_solved:

            if must_propagate:
                self.propagate()
                must_propagate = False

            if self.is_solved():
                is_solved = True

        # Build a simple model listing variables set to True.
        true_vars = [i for i, v in self.assignment.items() if v == 1]
        return 'SAT', true_vars


def solve_cnf(clauses: Iterable[Iterable[int]], num_vars: int) -> Tuple[str, List[int] | None]:
    """Convenience wrapper: construct a DPLL solver and solve the CNF.

    Parameters
    - clauses: iterable of clauses (each clause an iterable of signed ints)
    - num_vars: maximum variable index (variables are 1..num_vars)

    Returns the same tuple as `DPLL.solve()`.
    """
    return DPLL(clauses, num_vars).solve()

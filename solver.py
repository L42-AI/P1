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

                # Stores the trial index where each decision level starts
        self.level_start = []

        # stores the decision literals chosen at each level
        self.decisions = []

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
        while True:
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
            
                if len(pending_variables) == 0:
                # then tehre is a conflict as all literals are assigned false --> Must trigger backtracking
                    return(False)
            
            # Recurse/loop until no more unit propagation is possible --> We are at the fixed point
            if not must_propagate:
                return True

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

    def pick_unassigned_literal(self) -> int | None:
        """
        Pick an unassigned literal to branch on. This is where a decision for the value/cell starts

        This chooses the first unassigned variable and returns it as a positive literal. 
        Very simple, can be improved later
        """
        for var in self.assignment:
            if self.assignment[var] == 0:
                return var  # Return as positive literal
        return None  # All variables are assigned

    
    def push_decision_level(self, lit: int):
        """
        Start a new decision level with the given literal
        Where this level starts on the trial is noted and the decision literal is stored and assigned its value/sign
        """
        # Know where level starts in the assignment trail
        self.level_start.append(len(self.assignment_trail))

        # Remember the deicision literal
        var = abs(lit)
        tried_false = (lit < 0) # if literal is negative, we are trying false first
        self.decisions.append({'var': var, 'tried_false': tried_false})

        # ASsign the decision literal the correct sign
        val = 1 if lit > 0 else -1
        self._assign(lit, val)

    
    def backtrack(self) -> bool:
        """
        Backtrack to the previous decision level.
        If last decision still has an untried opposite branch, flip to false and return true.
        If no more decisions, return false as it is UNSAT

        1. Undo the decisions start
        2. if the false branch not tried, we re push this decision with tried_false = true and assign var = False and let it propagte again
        3. Else keep going back up
        """
        if not self.decisions:
            return False  # nothing to backtrack as UNSAT
        
        # Pop last decision and its level start
        decision = self.decisions.pop()
        level_start_index = self.level_start.pop()

        # Undo assignments at and after this level start
        while len(self.assignment_trail) > level_start_index:
            lit = self.assignment_trail.pop()
            self.assignment[abs(lit)] = 0  # unassign

        # If we have not tried teh False decision, do it now
        if not decision['tried_false']:
            # introduce level for this flipped decision
            self.level_start.append(len(self.assignment_trail))
            decision['tried_false'] = True
            self.decisions.append(decision)

            # Assign the var to false (negative literal)
            var = decision['var']
            self._assign(-var, -1)
            return True  # backtrack successful, flipped decision
        
        # Both decision tried, go back further with backtracking
        return self.backtrack()
        

    
    def solve(self) -> Tuple[str, List[int] | None]:
        """
        Attempt to solve the CNF using unit propagation only.

        Returns:
        - ('SAT', model) where model is a list of variables that are True
          (represented by their variable indices) when a satisfying
          assignment is found.
        - ('UNSAT', None) if unsatisfiable.

        Full DPLL loop starting with uni propagation at level 0, if it is not solved, pick unassigned literal to branch on, push decision level and propagate again.
        If there is a conflict during propagation, backtrack one level/flip the sign and prop again
        """
        # initial propogation at level 0 for unit clauses
        if not self.propagate():
            return 'UNSAT', None
        
        while True:
            # If solved, return the model
            if self.is_solved():
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



def solve_cnf(clauses: Iterable[Iterable[int]], num_vars: int) -> Tuple[str, List[int] | None]:
    """Convenience wrapper: construct a DPLL solver and solve the CNF.

    Parameters
    - clauses: iterable of clauses (each clause an iterable of signed ints)
    - num_vars: maximum variable index (variables are 1..num_vars)

    Returns the same tuple as `DPLL.solve()`.
    """
    return DPLL(clauses, num_vars).solve()

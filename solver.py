"""
SAT Assignment Part 2 - Non-consecutive Sudoku Solver (Puzzle -> SAT/UNSAT)

THIS is the file to edit.

Implement: solve_cnf(clauses) -> (status, model_or_None)"""


from typing import Iterable, List, Tuple
from collections import deque

Clause = Iterable[int]
Clauses = Iterable[Clause]

def flip(value: int) -> int:
    return -1 if value == 1 else -1

class DPLL:
    def __init__(self, clauses: Clauses, num_vars: int):
        self.clauses = clauses
        
        self.assignment = {var: 0 for var in range(1, num_vars + 1)} # 0: None 1: True -1: False
        self.assignment_trail = deque()

    def _assign(self, variable: int, value: int):
        self.assignment[abs(variable)] = value
        self.assignment_trail.append(variable)

    def element_true(self, variable: int):
        return (variable < 0 and self.assignment[abs(variable)] == -1) or (variable > 0 and self.assignment[abs(variable)] == 1)

    def clause_is_true(self, clause: Clause):
        for element in clause:
            if self.element_true(element):
                return True
            
        return False

    def get_pending_variables(self, clause: Clause) -> set[int]:
        pending_variables = set()
        for element in clause:
            if self.assignment[abs(element)] == 0:
                pending_variables.add(element)

        return pending_variables
    

    def propagate(self):
        must_propogate = False
        for clause in self.clauses:
            if self.clause_is_true(clause):
                continue
            
            pending_variables = self.get_pending_variables(clause)

            if len(pending_variables) == 1:
                v = list(pending_variables)[0]
                self._assign(v, -1 if v < 0 else 1)
                must_propogate = True
                
        if not must_propogate:
            return 
        
        self.propagate()

    def is_solved(self):
        for clause in self.clauses:
            if not self.clause_is_true(clause):
                return False
        return True

    def solve(self):
        is_solved = False
        must_propogate = True
        while not is_solved:

            if must_propogate:
                self.propagate()
                must_propogate = False

            if self.is_solved():
                is_solved = True
            
        return 'SAT', [v for v in self.assignment.values() if v == 1]
        return 'UNSAT', None
    
def solve_cnf(clauses: Iterable[Iterable[int]], num_vars: int) -> Tuple[str, List[int] | None]:
    return DPLL(clauses, num_vars).solve()

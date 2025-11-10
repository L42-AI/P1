"""
SAT Assignment Part 2 - Non-consecutive Sudoku Solver (Puzzle -> SAT/UNSAT)

THIS is the file to edit.

Implement: solve_cnf(clauses) -> (status, model_or_None)"""


from typing import Iterable, List, Tuple
import random as r



def solve_cnf(clauses: Iterable[Iterable[int]], num_vars: int) -> Tuple[str, List[int] | None]:
    """
    Implement your SAT solver here.
    Must return:
      ("SAT", model)  where model is a list of ints (DIMACS-style), or
      ("UNSAT", None)
    """ 

    def element_true(element, assignment):
        return (element < 0 and assignment[abs(element)] == -1) or (element > 0 and assignment[abs(element)] == 1)

    def get_pending_variables(clause, assignment) -> set[int]:
        pending_variables = set()
        for element in clause:
            if assignment[abs(element)] == 0:
                pending_variables.add(element)

        return pending_variables
    
    def clause_is_true(clause, assignment):
        for element in clause:
            if element_true(element, assignment):
                return True
            
        return False

    def propogate(clauses, assignment):
        
        must_propogate = False
        for clause in clauses:
            if clause_is_true(clause, assignment):
                continue
            
            pending_variables = get_pending_variables(clause, assignment)

            if len(pending_variables) == 1:
                v = list(pending_variables)[0]
                assignment[abs(v)] = -1 if v < 0 else 1
                must_propogate = True
                
        if not must_propogate:
            return clauses, assignment
        
        propogate(clauses, assignment)

    def get_variable(clauses, assignment): # TO BE IMPROVED WITH HEURISTIC
        for clause in clauses:
            for element in clause:
                if assignment[abs(element)] == 0:
                  return element

    def solved(clauses, assignment):
        for clause in clauses:
            if not clause_is_true(clause, assignment):
                return False
        return True

    assignment = {var: 0 for var in range(1, num_vars + 1)} # 0: None 1: True -1: False

    choices_made = {}

    is_solved = False
    while not is_solved:

        v = get_variable(clauses, assignment)
        if v is None:
            for v, choice in choices_made.items():
                assignment[v] = flip(choice)
                choices_made[v] = flip(choice)
        else:
            choice = 1 if r.random() < 0.5 else -1
            assignment[abs(v)] = choice
            choices_made[abs(v)] = choice


        must_propogate = True
      
        if must_propogate:
            propogate(clauses, assignment)
            must_propogate = False
        
        if solved(clauses, assignment):
            is_solved = True
        
    return 'SAT', [v for v in assignment.values() if v == 1]
    return 'UNSAT', None

def flip(value: int) -> int:
    return -1 if value == 1 else -1
"""
SAT Assignment Part 2 - Non-consecutive Sudoku Solver (Puzzle -> SAT/UNSAT)

THIS is the file to edit.

Implement: solve_cnf(clauses) -> (status, model_or_None)"""

from typing import Iterable, List, Tuple

from utils.visualize_sudoku import visualize_sudoku
from utils.cdcl import CDCL
from utils.dpll import DPLL

def solve_cnf(clauses: Iterable[Iterable[int]], num_vars: int) -> Tuple[str, List[int] | None]:
    """
    Convenience wrapper: construct a DPLL solver and solve the CNF.

    Parameters
    - clauses: iterable of clauses (each clause an iterable of signed ints)
    - num_vars: maximum variable index (variables are 1..num_vars)

    Returns the same tuple as `DPLL.solve()`.
    """
    solved, result = CDCL(clauses, num_vars).solve()

    if solved == 'SAT':
        n = int(round(num_vars ** (1/3)))
        visualize_sudoku(result, n)
    return solved, result

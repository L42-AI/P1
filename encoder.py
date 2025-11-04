"""
SAT Assignment Part 1 - Non-consecutive Sudoku Encoder (Puzzle -> CNF)

THIS is the file to edit.

Implement: to_cnf(input_path) -> (clauses, num_vars)

You're required to use a variable mapping as follows:
    var(r,c,v) = r*N*N + c*N + v
where r,c are in range (0...N-1) and v in (1...N).

You must encode:
  (1) Exactly one value per cell
  (2) For each value v and each row r: exactly one column c has v
  (3) For each value v and each column c: exactly one row r has v
  (4) For each value v and each sqrt(N)×sqrt(N) box: exactly one cell has v
  (5) Non-consecutive: orthogonal neighbors cannot differ by 1
  (6) Clues: unit clauses for the given puzzle
"""


from typing import Tuple, Iterable
import math

def to_cnf(input_path: str) -> Tuple[Iterable[Iterable[int]], int]:
    """
    Read puzzle from input_path and return (clauses, num_vars).

    - clauses: iterable of iterables of ints (each clause), no trailing 0s
    - num_vars: must be N^3 with N = grid size
    """
    grid = []
    with open(input_path, "r") as sudoku:
        for line in sudoku:
            line = line.strip()
            row = [int(x) for x in line.split()]
            grid.append(row)

    N = len(grid)
    B = int(math.sqrt(N))  # Box size
    NUMBER_OF_VALUES = 9

    print("N =", N, "B =", B)

    # Make every variable unique
    def var_id(row, column, value):
      return row*N*N + column*N + value

    clauses = [] # Represents all the disjunctions

    # Constraints
    # (1) Exactly one value per cell
    def one_value_per_cell():
        """
        There are N*N cells and each cell can take 9 values (1 to 9).
        So we create clauses to ensure that each cell has exactly one of the 9 value.
        """
        for r in range(N):
            for c in range(N):
                # At least one value in the cell
                clause = [var_id(r, c, v) for v in range(NUMBER_OF_VALUES)]
                clauses.append(clause)

                # At most one value in the cell
                for v1 in range(NUMBER_OF_VALUES):
                    for v2 in range(v1 + 1, NUMBER_OF_VALUES):
                        clauses.append([-var_id(r, c, v1), -var_id(r, c, v2)])

    # (2) Row constraint
    def row_constraint(r, v):
        """
        There are N rows and each row must contain each value v exactly once.
        """

        for c in range(N):
            clauses.append([var_id(r, c, v) for c in range(N)])
    
    def col_constraint(c, v):
        """
        There are N columns and each column must contain each value v exactly once.
        """
        for r in range(N):
            clauses.append([var_id(r, c, v) for r in range(N)])

    def box_constraint(br, bc, v):
        """
        There are B*B boxes and each box must contain each value v exactly once.
        """
        for i in range(B):
            for j in range(B):
                clauses.append([var_id(br*B + i, bc*B + j, v) for i in range(B) for j in range(B)])


    # Call the functions to add constraints
    one_value_per_cell()
    for v in range(NUMBER_OF_VALUES):
        for r in range(N):
            row_constraint(r, v)
        for c in range(N):
            col_constraint(c, v)
        for br in range(B):
            for bc in range(B):
                box_constraint(br, bc, v)

    return clauses, N*N*NUMBER_OF_VALUES

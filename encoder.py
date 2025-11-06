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

from typing import Tuple, Iterable, List
import math

def to_cnf(input_path: str) -> Tuple[Iterable[Iterable[int]], int]:
    # Read puzzle
    grid: List[List[int]] = []
    with open(input_path, "r") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            grid.append([int(x) for x in line.split()])

    N = len(grid)
    assert all(len(r) == N for r in grid), "Input must be an N×N grid"
    B = int(math.isqrt(N))
    assert B * B == N, "N must be a perfect square (e.g., 9, 16, 25)"

    def var_id(r: int, c: int, v: int) -> int:
        # r,c in 0..N-1 ; v in 1..N
        return r * N * N + c * N + v

    clauses: List[List[int]] = []

    def exactly_one(lits: List[int]) -> None:
        # at least one
        clauses.append(list(lits))
        # at most one (pairwise)
        for i in range(len(lits)):
            for j in range(i + 1, len(lits)):
                clauses.append([-lits[i], -lits[j]])

    # (1) Exactly one value per cell
    for r in range(N):
        for c in range(N):
            exactly_one([var_id(r, c, v) for v in range(1, N + 1)])

    # (2) Row: for each value v and each row r, exactly one column c has v
    for v in range(1, N + 1):
        for r in range(N):
            exactly_one([var_id(r, c, v) for c in range(N)])

    # (3) Column: for each value v and each column c, exactly one row r has v
    for v in range(1, N + 1):
        for c in range(N):
            exactly_one([var_id(r, c, v) for r in range(N)])

    # (4) Box: for each value v and each B×B box, exactly one cell has v
    for v in range(1, N + 1):
        for br in range(B):
            for bc in range(B):
                box_lits = []
                for i in range(B):
                    for j in range(B):
                        r = br * B + i
                        c = bc * B + j
                        box_lits.append(var_id(r, c, v))
                exactly_one(box_lits)

    # (5) Non-consecutive rule: orthogonal neighbors cannot differ by 1
    # For each adjacent pair, forbid (r,c)=v together with neighbor = v±1
    for r in range(N):
        for c in range(N):
            if c + 1 < N:
                for v in range(1, N + 1):
                    if v - 1 >= 1:
                        clauses.append([-var_id(r, c, v), -var_id(r, c + 1, v - 1)])
                    if v + 1 <= N:
                        clauses.append([-var_id(r, c, v), -var_id(r, c + 1, v + 1)])
            if r + 1 < N:
                for v in range(1, N + 1):
                    if v - 1 >= 1:
                        clauses.append([-var_id(r, c, v), -var_id(r + 1, c, v - 1)])
                    if v + 1 <= N:
                        clauses.append([-var_id(r, c, v), -var_id(r + 1, c, v + 1)])

    # (6) Clues: unit clauses for given digits
    for r in range(N):
        for c in range(N):
            v = grid[r][c]
            if v > 0:
                clauses.append([var_id(r, c, v)])

    num_vars = N ** 3
    return clauses, num_vars


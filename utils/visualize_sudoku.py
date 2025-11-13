import math

def visualize_sudoku(model: list[int], n: int):
    """
    Visualize a Sudoku solution from the SAT model. Supports 9x9, 16x16, 25x25
    (block sizes 3, 4, 5) as well as any n that is a perfect square.
    """
    
    # Determine block size
    block = int(math.isqrt(n))
    if block * block != n:
        print(f"Warning: Grid size {n} is not a perfect square. Using block=1.")
        block = 1

    # Initialize empty Sudoku grid
    grid = [[0 for _ in range(n)] for _ in range(n)]
    print(f"Sudoku Solution ({n}x{n}):")

    # Map positive literals to (row, col, value)
    for literal in model:
        if literal <= 0:
            continue
        var = literal - 1  # convert to 0-based index
        
        row = var // (n * n)
        col = (var % (n * n)) // n
        val = (var % n) + 1
        
        if 0 <= row < n and 0 <= col < n:
            grid[row][col] = val

    # Cell width depends on max digits (e.g., 2 for 16x16 or 25x25)
    cell_width = len(str(n))

    # --- THIS IS THE CORRECTED SECTION ---

    # Build a sample printed row (using empty cells) the same way real rows are formatted,
    # then convert that sample row into a separator line by mapping '|' -> '+' and every
    # other character -> '-' so lengths exactly match the printed row (including spaces).
    sample_parts = []
    for j in range(n):
        if j % block == 0:
            sample_parts.append('| ')
        sample_parts.append('.' * cell_width)  # fmt_cell(0) -> dots
        sample_parts.append(' ')
    sample_parts.append('|')
    sample_row = ''.join(sample_parts)
    sep_line = ''.join('+' if ch == '|' else '-' for ch in sample_row)
    # --- END OF CORRECTION ---

    # Helper to format a single cell
    def fmt_cell(num: int) -> str:
        if num == 0:
            return '.' * cell_width
        return str(num).rjust(cell_width)

    # Print the grid
    print(sep_line)
    for i, row in enumerate(grid):
        parts = []
        for j, num in enumerate(row):
            if j % block == 0:
                parts.append('| ')
            parts.append(fmt_cell(grid[i][j]))
            parts.append(' ')
        parts.append('|')
        print(''.join(parts))
        if (i + 1) % block == 0:
            print(sep_line)

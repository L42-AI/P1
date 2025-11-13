import math

def visualize_sudoku(model: list[int], n: int):
    """
    Visualize a Sudoku solution from the SAT model. Supports 9x9, 16x16, 25x25
    (block sizes 3, 4, 5) as well as any n that is a perfect square.
    """
    print("\n" + "="*40)
    
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

    # 1. Build a pattern for separator line
    row_pattern = []
    for j in range(n):
        if j % block == 0:
            row_pattern.append('|')
        row_pattern.append('X' * cell_width) # e.g., 'X' or 'XX'
        row_pattern.append(' ')                # e.g., ' '
    row_pattern.append('|')

    # 2. Convert pattern to the separator line
    #    This now respects the length of each part of the pattern
    sep_line_parts = []
    for p in row_pattern:
        if p == '|':
            sep_line_parts.append('+')
        else:
            # Replaces 'XX' with '--' and ' ' with '-'
            sep_line_parts.append('-' * len(p)) 
            
    sep_line = ''.join(sep_line_parts)
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
                parts.append('|')
            parts.append(fmt_cell(grid[i][j]))
            parts.append(' ')
        parts.append('|')
        print(''.join(parts))
        if (i + 1) % block == 0:
            print(sep_line)
            
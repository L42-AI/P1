from tqdm import tqdm

class ProgressBar:
    def __init__(self, num_vars: int, on: bool = True):
        self.explored = 0
        self._progress_bar = tqdm(total=num_vars, desc="Assigned vars", unit="var") if on else None

    def update(self, assignment: dict):
        assigned = sum(1 for v in assignment.values() if v != 0)
        # update bar and show nodes explored as postfix
        if self._progress_bar is not None:
            self._progress_bar.n = assigned
            self._progress_bar.set_postfix(nodes=self.explored)
            self._progress_bar.refresh()

    def close(self):
        if self._progress_bar is not None:
            self._progress_bar.close()

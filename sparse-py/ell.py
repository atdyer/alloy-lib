class ELL:

    def __init__(self, rows, cols, maxnz):

        self.rows = rows
        self.cols = cols
        self.maxnz = maxnz
        self.columns = []
        self.values = []

    def get(self, row, col):

        if not (0 <= row < self.rows) or not (0 <= col < self.cols):
            raise IndexError

        a = row * self.maxnz
        b = a + self.maxnz

        try:
            i = self.columns.index(col, a, b)
        except ValueError:
            return 0
        return self.values[i]


t = ELL(2, 2, 2)
print(t.get(0, 0))

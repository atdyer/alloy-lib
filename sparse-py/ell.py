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

    def to_yale(self):

        a = []
        ia = [0]
        ja = []
        kpos = 0
        for row in range(self.rows):
            for colindex in range(self.maxnz):
                index = row * self.maxnz + colindex
                column = self.columns[index]
                value = self.values[index]
                if value != 0.0:
                    a[kpos] = value
                    ja[kpos] = column
                    kpos += 1
            ia[row+1] = kpos
        return a, ia, ja


t = ELL(2, 2, 2)
print(t.get(0, 0))
print(t.to_yale())

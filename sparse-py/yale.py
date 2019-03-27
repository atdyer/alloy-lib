class Yale:

    def __init__(self, rows, cols):

        self.rows = rows
        self.cols = cols
        self.A = []
        self.IA = [0]
        self.JA = []

    def get(self, row, col):

        a = self.IA[row] if row < len(self.IA) else None
        b = self.IA[row+1] if row+1 < len(self.IA) else None

        if a is None or b is None or a == b:
            return 0

        j = self.JA[a:b]
        v = self.A[a:b]
        i = j.index(col) if col in j else None

        return 0 if i is None else v[i]

    def multiply(self, vector):

        length = len(vector)
        solution = [0] * length

        for row in range(length):

            a = self.IA[row] if row < len(self.IA) else None
            b = self.IA[row+1] if row+1 < len(self.IA) else None

            if a is None or b is None or a == b:
                continue

            j = self.JA[a:b]
            v = self.A[a:b]

            for col, val in zip(j, v):

                solution[row] += vector[col]*val

        return solution

    def update(self, row, col, value):

        curr = self.get(row, col)

        if curr != 0 and value != 0:
            self._nz_to_nz(row, col, value)
        if curr != 0 and value == 0:
            self._nz_to_z(row, col)
        if curr == 0 and value != 0:
            self._z_to_nz(row, col, value)
        if curr == 0 and value == 0:
            self._z_to_z(row, col)

    def _nz_to_nz(self, row, col, value):

        a = self.IA[row]
        b = self.IA[row+1]
        j = self.JA[a:b]
        i = a + j.index(col)
        self.A[i] = value

    def _nz_to_z(self, row, col):

        ai = row
        bi = row + 1
        li = len(self.IA) - 1
        a = self.IA[ai]
        b = self.IA[bi]
        j = self.JA[a:b]
        i = a + j.index(col)
        del self.A[i]
        del self.JA[i]
        if bi == li:
            bn = b - 1
            self.IA[bi] = bn
            bf = self.IA.index(bn)
            self.IA = self.IA[0:bf+1]
        else:
            self.IA[bi:li+1] = [v-1 for v in self.IA[bi:li+1]]

    def _z_to_nz(self, row, col, value):

        a = self.IA[row] if row < len(self.IA) else None
        b = self.IA[row+1] if row+1 < len(self.IA) else None

        if a is not None:

            if b is not None:

                bi = row + 1
                li = len(self.IA)
                self.A.insert(b, value)
                self.JA.insert(b, col)
                self.IA[bi:li] = [v+1 for v in self.IA[bi:li]]

            else:

                self.A.append(value)
                self.JA.append(col)
                self.IA.append(a+1)

        else:

            self.A.append(value)
            self.JA.append(col)
            an = self.IA[-1]
            bn = an + 1
            s = len(self.IA) - 1
            t = row
            self.IA = self.IA + [an]*(t-s) + [bn]

    def _z_to_z(self, row, col):

        pass

    def _rep_inv(self):

        inv = (
            0 not in self.A
            and all([value <= self.rows*self.cols for value in self.IA])
            and all([value < self.cols for value in self.JA])
            and self.IA[0] == 0
            and self.IA[-1] == len(self.A)
            and (True if len(self.IA) <= 1 else self.IA[-1] > self.IA[-2])
            and len(self.A) == len(self.JA)
            and len(self.A) <= self.rows*self.cols
            and len(self.IA) <= self.rows + 1
        )

        if not inv:
            return False

        for i in range(len(self.IA)-1):
            a = i
            b = i+1
            if b < a:
                return False
            if b-a > self.cols:
                return False
            vals = set(self.JA[a:b])
            if len(vals) != b-a:
                return False

        return True


t = Yale(2, 2)
t.update(0, 0, 1)
t.update(0, 1, 2)
t.update(1, 0, 3)
t.update(1, 1, 4)
r = t.multiply([1, 1])
print(r)


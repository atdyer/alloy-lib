class Yale:

    def __init__(self, rows, cols):

        if rows < 0 or cols < 0:
            raise ValueError('rows and cols must be >= 0')

        self.rows = rows
        self.cols = cols
        self.A = []
        self.IA = [0]
        self.JA = []

    def __repr__(self):

        return '<Yale> Sparse {}x{} matrix'.format(self.rows, self.cols)

    def __str__(self):

        string = ''
        maxval = max(self.A) if len(self.A) else 0
        length = len(str(maxval))

        for row in range(self.rows):
            for col in range(self.cols):
                string += '{:<{width}}  '.format(self.get(row, col), width=length)
            string += '\n'

        return string

    def get(self, row, col):

        range_check(self, row, col)

        # let a = y.IA[row], b = y.IA[add[row, 1]]
        a = self.IA[row] if row < len(self.IA) else None
        b = self.IA[row+1] if row+1 < len(self.IA) else None

        # (no a or no b or a = b) => Zero
        if a is None or b is None or a == b:

            return 0

        # j = JA[a, b)
        # v = A[a, b)
        # i = j.idxOf[col]
        j = self.JA[a:b]
        v = self.A[a:b]
        i = j.index(col) if col in j else None

        # no i => Zero else v[i]
        if i is None:

            return 0

        return v[i]

    def update(self, row, col, value):

        range_check(self, row, col)

        curr = self.get(row, col)

        if curr != 0 and value != 0:
            nz_to_nz(self, row, col, value)
        if curr != 0 and value == 0:
            nz_to_z(self, row, col)
        if curr == 0 and value != 0:
            z_to_nz(self, row, col, value)
        if curr == 0 and value == 0:
            z_to_z(self, row, col)


def nz_to_nz(y, row, col, val):

    # y'.IA = y.IA
    # y'.JA = y.JA

    # a = y.IA[row]
    # b = y.IAIA[add[row, 1]]
    # j = y.JA.subseq[a, sub[b, 1]]
    # i = add[a, j.idxOf[col]]
    a = y.IA[row]
    b = y.IA[row+1]
    j = y.JA[a:b]
    i = a + j.index(col)

    # y'.A = y.A.setAt[i, val]
    y.A[i] = val


def nz_to_z(y, row, col):

    # ai = row
    # bi = add[row, 1]
    # li = sub[#y.IA, 1]
    # a = y.IA[ai]
    # b = y.IA[bi]
    # c = y.JA.subseq[a, sub[b, 1]].idxOf[col]
    # i = add[a, c]
    ai = row
    bi = row + 1
    li = len(y.IA) - 1
    a = y.IA[ai]
    b = y.IA[bi]
    c = y.JA[a:b].index(col)
    i = a + c

    # y'.A = y.A.delete[i]
    del y.A[i]

    # y'.JA = y.JA.delete[i]
    del y.JA[i]

    if bi == li:

        # bn = sub[b, 1]
        # ia = y.IA.setAt[bi, bn]
        # bf = ia.idxOf[bn]
        bn = b - 1
        y.IA[bi] = bn
        bf = y.IA.index(bn)
        y.IA = y.IA[0:bf+1]

    else:

        # subEach[y.IA.subseq[bi, li], y'.IA.subseq[bi, li], 1]
        y.IA[bi:li+1] = [v-1 for v in y.IA[bi:li+1]]


def z_to_nz(y, row, col, val):

    # a = y.IA[row]
    # b = y.IA[add[row, 1]]
    a = y.IA[row] if row < len(y.IA) else None
    b = y.IA[row+1] if row+1 < len(y.IA) else None

    if a is not None:

        if b is not None:

            # bi = add[row, 1]
            # li = sub[#y.IA, 1]
            bi = row + 1
            li = len(y.IA) - 1

            # y'.A = y.A.insert[b, val]
            # y'.JA = y.JA.insert[b, col]
            y.A.insert(b, val)
            y.JA.insert(b, col)

            # addEach[y.IA.subseq[bi, li], y'.IA.subseq[bi, li], 1]
            y.IA[bi:li+1] = [v+1 for v in y.IA[bi:li+1]]

        else:

            # y'.A = y.A.add[val]
            # y'.JA = y.JA.add[col]
            # y'.IA = y.IA.add[add[a, 1]]
            y.A.append(val)
            y.JA.append(col)
            y.IA.append(a+1)

    else:

        # y'.A = y.A.add[val]
        # y'.JA = y.JA.add[col]
        y.A.append(val)
        y.JA.append(col)

        # an = y.IA.last
        # bn = add[an, 1]
        an = y.IA[-1]
        bn = an + 1

        # s = sub[#y.IA, 1]
        # t = sub[#y'.IA, 2]
        s = len(y.IA) - 1
        t = row

        # y'.IA.subseq[s, t].elems = an
        # y'.IA.last = bn
        y.IA = y.IA + [an] * (t-s) + [bn]


def z_to_z(y, row, col):

    pass


def row_in_range(yale, row):

    return 0 <= row <= yale.rows


def col_in_range(yale, col):

    return 0 <= col <= yale.cols


def range_check(yale, row, col):

    if not row_in_range(yale, row):

        raise_row_range_error(yale, row)

    if not col_in_range(yale, col):

        raise_col_range_error(yale, col)


def raise_row_range_error(yale, row):

    raise ValueError('Row {} not in range. Matrix has {} rows.'.format(row, yale.rows))


def raise_col_range_error(yale, col):

    raise ValueError('Column {} not in range. Matrix has {} columns.'.format(col, yale.cols))


test = Yale(4, 2)
test.A = [1, 1]
test.IA = [0, 2]
test.JA = [1, 0]
print(test)
test.update(0, 0, 100)
print(test)
test.update(0, 1, 10000)
print(test)
test.update(0, 1, 0)
print(test)
test.update(0, 0, 0)
print(test)
test.update(0, 0, 1)
print(test)
test.update(3, 1, 1)
print(test)

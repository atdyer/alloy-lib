cols = [1, -1, 0, 2, -1, 1]
vals = [1, -1, 2, 3, -1, 4]


def genkpos(rows, maxnz):

    kpos = 0
    kposseq = [0] * (rows * maxnz)
    for i in range(rows):
        for k in range(maxnz):
            kposseq[i * maxnz + k] = kpos
            if vals[i * maxnz + k] != -1:
                kpos += 1
    kposseq.append(kpos)
    return kposseq


def ellcsr(nrow, ncol, maxnz, cols, vals):

    A = [-1] * 4
    IA = [0] * 4
    JA = [-1] * 4
    kpos = 0
    step = 0
    for i in range(nrow):
        for k in range(maxnz):
            if vals[i * maxnz + k] != -1:
                A[kpos] = vals[i * maxnz + k]
                JA[kpos] = cols[i * maxnz + k]
                kpos += 1
            print('step = {}, i = {}, k = {}, kpos = {}'.format(step, i, k, kpos))
            step += 1
        IA[i+1] = kpos
    return A, IA, JA


# A, IA, JA = ellcsr(3, 3, 2, cols, vals)
# print('---')
# print(A)
# print(JA)
# print(IA)

print(genkpos(3, 2))

columns = [1, -1, 0, 2, -1, 1]
values = [1, -1, 2, 3, -1, 4]


# def ellcsr(cols, vals, nrows, maxnz):
#
#     IA = [0] * (nrows + 1)
#     kpos = 0
#
#     for i in range(nrows):
#         IA[i+1] = IA[i]
#         for k in range(maxnz):
#             idx = i * maxnz + k
#             col = columns[idx]
#             val = values[idx]
#             if col != -1:
#                 IA[i+1] += 1
#                 if idx != kpos:
#                     vals[kpos] = val
#                     cols[kpos] = col
#                 kpos += 1
#     return vals, cols, IA


def ellcsrip(cols, vals, nrows, maxnz):

    IA = [0] * (nrows + 1)
    kpos = 0

    for i in range(nrows):
        for k in range(maxnz):
            idx = i * maxnz + k
            if cols[idx] != -1:
                vals[kpos] = vals[idx]
                cols[kpos] = cols[idx]
                kpos += 1
            IA[i+1] = kpos
    return vals, cols, IA


A, JA, IA = ellcsrip(columns, values, 3, 2)
print('A  = {}'.format(A))
print('JA = {}'.format(JA))
print('IA = {}'.format(IA))

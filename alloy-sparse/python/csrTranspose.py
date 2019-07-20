import numpy as np


def csr_transpose(n, a, ja, ia, ao, jao, iao):

    iao[:] = 0

    # count values in each column
    for i in range(n):
        for k in range(ia[i], ia[i+1]):
            j = ja[k] + 1
            iao[j] = iao[j] + 1

    # set pointers from lengths
    iao[0] = 0
    for i in range(n):
        iao[i+1] = iao[i] + iao[i+1]

    # copy values
    for i in range(n):
        for k in range(ia[i], ia[i+1]):
            j = ja[k]
            nxt = iao[j]
            ao[nxt] = a[k]
            jao[nxt] = i
            iao[j] = nxt + 1

    # reshift iao
    for i in reversed(range(n)):
        iao[i+1] = iao[i]
    iao[0] = 0


# 0 1 0
# 2 0 3
# 0 4 0
A = np.array([1, 2, 3, 4])
JA = np.array([1, 0, 2, 1])
IA = np.array([0, 1, 3, 4])
AO = np.array([0, 0, 0, 0])
JAO = np.array([0, 0, 0, 0])
IAO = np.array([0, 0, 0, 0])
N = 3

csr_transpose(N, A, JA, IA, AO, JAO, IAO)
print('IA: {}'.format(IAO))
print('A:  {}'.format(AO))
print('JA: {}'.format(JAO))

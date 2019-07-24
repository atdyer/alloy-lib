# ia must have even number of values
def increment_ranges(ia):
    it = 0
    n = len(ia)
    arr = [0]*max(ia)
    for i in range(0, n, 2):
        s = ia[i]
        t = ia[i+1]
        for k in range(s, t):
            arr[k] += 1
            it += 1
            print(it, i, k, arr)
    return arr


# IA = [0, 5, 1, 5, 2, 5, 3, 5, 4, 5]
IA = [0, 3, 1, 2]
print(increment_ranges(IA))
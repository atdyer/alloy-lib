# ia must have even number of values
def increment_ranges(ia):
    it = 0
    arr = [0]*max(ia)
    for i in range(0, len(ia), 2):
        for k in range(ia[i], ia[i+1]):
            arr[k] += 1
            it += 1
            print(i, k, it, arr)
    return arr

# IA = [0, 3, 1, 2]
IA = [0, 3, 1, 3, 2, 3]
print('i k t')
print(increment_ranges(IA))

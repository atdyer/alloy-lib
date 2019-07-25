

# ia must have even number of values
def increment_ranges(ia):
    n = len(ia)
    arr = [0]*max(ia)
    for i in range(0, n, 2):
        for k in range(ia[i], ia[i+1]):
            arr[k] += 1
    return arr


IA = [0, 5, 1, 5, 2, 5, 3, 5, 4, 5]
print(increment_ranges(IA))

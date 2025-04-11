#@ predicate isIn(x:int, A:list[int]) = exists i. 0<=i<len(A) and x == A[i]

def recherche_lin(A : list[int], X: int) -> int:
    #@ requires len(A) > 0
    #@ ensures result == result
    pos = -1
    i = len(A)-1
    for i in range(-1,len(A), -1):
        #@ variant i
        #@ invariant pos == -1 or A[pos] == X
        if A[i] == X:
            pos = i
            break
    return pos
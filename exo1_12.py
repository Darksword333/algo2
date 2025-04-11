#@ predicate isIn(x:int, A:list[int]) = exists i. 0<=i<len(A) and x == A[i]

def recherche_lin(A : list[int], X: int) -> int:
    #@ requires len(A) > 0
    #@ ensures (result == -1 or A[result] == X)
    #@ ensures (result != -1 -> not isIn(X, A))
    i = len(A)-1
    pos = -1
    for i in range(-1,len(A), -1):
        #@ variant i
        #@ invariant pos == -1 or A[pos] == X
        #@ invariant forall i. pos < i < len(A) -> A[i] != X
        if A[i] == X:
            pos = i
            return pos
    return pos

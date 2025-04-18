def recherche_lin(A : list[int], X: int) -> int:
    #@ensures 0 <= result <= len(A)
    #@ensures result == len(A) -> (forall I. 0 <= I < len(A) -> X != A[I])
    #@ensures result < len(A) -> X == A[result]
    pos = 0
    while (pos < len(A) and A[pos] != X):
        #@variant len(A) - pos
        #@invariant 0 <= pos <= len(A)
        #@invariant forall I. 0 <= I < pos -> X != A[I]
        pos = pos + 1
    return pos
l1 = [5, 4, 3, 2, 1]
r = recherche_lin(l1, 3)
#@ assert r == 2
l2 = [-1, 0, 6, 4, 2]
r = recherche_lin(l2, 4)
#@ assert r == 3
r = recherche_lin(l2, 100)
#@ assert r == 5
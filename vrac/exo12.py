#@predicate isIn(x:int,a:list[int]) = exists i. 0<=i<len(a) and x==a[i]
def recherche_lin(A : list[int], X: int) -> int:
    #@requires len(A) > 0
    #@ensures result == len(A) or A[result] == X
    pos = 0
    while (pos < len(A) and A[pos] != X):
        #@variant len(A) - pos
        #@invariant 0 <= pos <= len(A)
        #@invariant forall I. 0 <= I < pos -> A[I] != X
        pos = pos + 1
    return pos

l1 = [ 5 , 4 , 3 , 2 , 1 ]
r = recherche_lin( l1 , 3 ) 
#@assert r == 2
l2 = [ -1 , 0 , 6 , 4 , 2 ]
r = recherche_lin( l2 , 4 ) 
#@ assert r == 3
r = recherche_lin( l2 , 9 ) 
#@ assert r == 5
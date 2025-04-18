#@ predicate sorted(A:list[int]) = forall x,y. 0 <= x < y < len(A) -> A[x] <= A[y]
#@ predicate isInSub(X:int, A:list[int], D:int, F:int) = exists K. D <= K < F and A[K] == X
#@ predicate isIn(X:int, A:list[int]) = exists k. 0 <= k < len(A) and A[k] == X
def recherche_dichotomique(A:list[int], X:int) -> int:
    #@ requires len(A) > 0
    #@ requires sorted(A)
    #@ ensures (0 <= result < len(A) and A[result] == X) or (result == len(A) and not isIn(X, A))
    i, j = 0, len(A)-1
    m = (i + j)//2
    while i <= j:
        #@ variant j-i
        #@ invariant 0 <= i <= len(A)
        #@ invariant -1 <= j < len(A)
        #@ invariant j < len(A)
        #@ invariant not isInSub(X, A, 0, i) 
        #@ invariant not isInSub(X, A, j+1, len(A)) 
        #@ invariant 0 <= m < len(A)
        m = (i + j)//2
        if A[m] == X:
            return m
        elif A[m] < X:
            i = m + 1
        else:
            j = m -1
    return len(A)
    
l1 = [1,2,3,4,5]
r = recherche_dichotomique(l1,3) 
#@assert r == 2

l2 = [1,3,4,7,8]
r = recherche_dichotomique(l2,8) 
#@assert r == 4

l3 = [1,3,4,7,8]
r = recherche_dichotomique(l3,1) 
#@assert r == 0

l4 = [1,3,4,7,9]
r = recherche_dichotomique(l4,8) 
#@assert r == 5
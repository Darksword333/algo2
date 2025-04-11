#@ predicate sorted(A: list[int]) = forall I, J. 0 <= I <= J < len(A) -> A[I] <= A[J]
#@ predicate isIn(X: int, A: list[int]) = exists i. 0 <= i < len(A) and A[i] == X
#@ predicate hasCommonSub(A: list[int], ad: int, af: int, B: list[int], bd: int, bf: int) = exists i, j. ad <= i < af and bd <= j < bf and A[i] == B[j]

def recherche_commun(A: list[int], B: list[int]) -> int:
    #@ requires sorted(A) and sorted(B) and hasCommonSub(A, 0, len(A), B, 0, len(B))
    #@ ensures isIn(result, A) and isIn(result, B)
    i, j = 0, 0
    while i < len(A) and j < len(B):
        #@ variant len(A) - i + len(B) - j  
        #@ invariant 0 <= i < len(A)  
        #@ invariant 0 <= j < len(B) 
        #@ invariant hasCommonSub(A, i, len(A), B, j, len(B))
        if A[i] == B[j]:
            return A[i] 
        elif A[i] < B[j]:
            i += 1 
        else:
            j += 1 
    return -1 


r = recherche_commun ([3] , [3])
#@ assert r == 3
r = recherche_commun ([4,5,7,9,18,19] , [3,6,8,9,10])
#@ assert r == 9
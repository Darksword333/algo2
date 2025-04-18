#@predicate sorted(A: list[int]) = forall I, J. 0 <= I <= J < len(A) -> A[I] <= A[J]
#@predicate isIn(X: int, A: list[int]) = exists i. 0 <= i < len(A) and A[i] == X
#@predicate hasCommonSub(A: list[int], ad: int, af: int, B: list[int], bd: int, bf: int) = exists i, j. ad <= i <= af and bd <= j <= bf and A[i] == B[j]

def recherche_commun(A: list[int], B: list[int]) -> int:
    
    #@requires sorted(A) and sorted(B)
    #@requires hasCommonSub(A, 0, len(A) - 1, B, 0, len(B) - 1)
    #@ensures isIn(result, A) and isIn(result, B)
    i, j = 0, 0  # Initialisation des indices
    
    while i < len(A) and j < len(B):
        #@variant len(A) - i + len(B) - j  # Variant de la recherche pour garantir la terminaison
        #@invariant 0 <= i < len(A)  # L'indice i reste dans les bornes de A
        #@invariant 0 <= j < len(B)  # L'indice j reste dans les bornes de B
        #@invariant hasCommonSub(A, i, len(A) - 1, B, j, len(B) - 1)  # Un élément commun entre les indices i et j et la fin des deux listes
        if A[i] == B[j]:
            return A[i]  # Si un élément commun est trouvé, on le retourne
        elif A[i] < B[j]:
            i += 1  # Si A[i] est plus petit, on avance dans A
        else:
            j += 1  # Si B[j] est plus petit, on avance dans B
    
    return -1  # Si aucun élément commun n'est trouvé 


r = recherche_commun ( [ 3 ] , [ 3 ] )
#@assert r ==3
r = recherche_commun ( [4,5,7,9,18,19] , [3,6,8,9,10])
#@assert r ==9
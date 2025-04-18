#@predicate isIn(X: int, A: list[int]) = exists i. 0 <= i < len(A) and A[i] == X
#@predicate isInSub(X: int, A: list[int], D: int, F: int) = 0 <= D <= F <= len(A) -> exists i. D <= i < F and A[i] == X


#@function NotIsInSubNext(X: int, A: list[int], D: int, F: int) -> unit
# @requires 0 <= D <= F < len(A) and not isInSub(X, A, D, F) and not (A[F] == X)
# @ensures not isInSub(X, A, D, F + 1)
def NotIsInSubNext(X: int, A: list[int], D: int, F: int):
    return None

def recherche_simultanee(n: int, liste: list[int], c: int, k: int) -> int:
    #@requires len(liste) % (c * k) == 0 and c > 0 and k > 0
    # @requires forall x. 0 <= x < len(liste) -> liste[x] is int
    # @ensures isIn(result, liste) if result < len(liste) else not isIn(n, liste)
    i = 0
    #@assert forall S. 0<=S<c -> not isInSub(n, liste, S*k, S*k)
    while i < c:
        #@variant c - i  # Le nombre de secteurs restants diminue
        #@invariant 0 <= i <= c  # L'indice i reste dans les bornes des secteurs
        #@invariant not isInSub(n, liste, 0, i * k)  # Aucun élément avant i*k n'a été trouvé
        s = 0
        while s < k:
            #@variant k - s  # Le nombre d'éléments restants dans le secteur diminue
            #@invariant 0 <= s <= k  # L'indice s reste dans les bornes du secteur actuel
            #@invariant not isInSub(n, liste, i * k, i * k + s)  # Aucun élément avant i*k + s dans ce secteur n'a été trouvé

            #@assert forall i. 0<=i<c*k -> (i//k)*k <=i <((i//k)+1)*k
            if liste[i * k + s] == n:
                return i * k + s
            #@call NotIsInSubNext(n, liste, 0, len(liste))
            s += 1
        i += 1
    #@assert forall i. 0<=i<c*k -> (forall I. (i//k)*k <=I<((i//k)+1)*k and I==i -> liste[I]!=n)
    #@assert s*k+k == (s+1)*k
    return len(liste)

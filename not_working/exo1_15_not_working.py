#@ predicate isInSub(X:int, A:list[int], D:int, F:int) = exists K. D <= K < F and A[K] == X
#@ predicate isIn(X:int, A:list[int]) = exists k. 0 <= k < len(A) and A[k] == X

def NotIsInSubNext(X: int, A: list[int], D: int, F: int) -> unit:
    #@ requires 0 <= D <= F < len(A) and not isInSub(X,A,D,F) and not (A[F] == X)
    #@ ensures not isInSub(X,A,D,F+1)
    return None

def recherche_simultanee(n: int, liste: list[int], c: int, k: int) -> int:
    #@ requires len(liste) % (c * k) == 0 and c > 0 and k > 0
    #@ ensures result < len(liste) -> isIn(result, liste) and result >= len(liste) -> not isIn(n, liste)
    i = 0
    s = 0
    #@ assert forall S. 0<=S<c -> not isInSub(n, liste, S*k, S*k)
    while i < c:
        #@ variant c - i  
        #@ invariant 0 <= i <= c 
        #@ invariant not isInSub(n, liste, 0, i * k)  
        s = 0
        while s < k:
            #@ variant k - s 
            #@ invariant 0 <= s <= k
            #@ invariant 0 <= i <= c
            #@ invariant not isInSub(n, liste, i * k, i * k + s)  

            #@ assert forall i. 0<=i<c*k -> (i//k)*k <=i <((i//k)+1)*k
            if liste[i*k+s] == n:
                return i * k + s
            #@ call NotIsInSubNext(n, liste, 0, len(liste))
            s += 1
        i += 1
    #@ assert forall i. 0<=i<c*k -> (forall I. (i//k)*k <=I<((i//k)+1)*k and I==i -> liste[I]!=n)
    #@ assert s*k+k == (s+1)*k
    return len(liste)
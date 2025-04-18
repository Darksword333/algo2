#@predicate sorted(A:list[int]) = forall I,J. 0<=I<=J<len(A) -> A[I] <= A[J]
#@predicate isInSub(X:int, A:list[int], D:int, F:int) = 0<=D<=F<=len(A) -> exists I. D<=I<F and X==A[I]
#@predicate isIn(X:int, A:list[int]) = isInSub(X, A, 0, len(A))


def recherche_dicho(N, A, X):
  #@requires len(A) == N
  #@requires N > 0
  #@requires sorted(A)
  #@ensures 0<=result<=N
  #@ensures result < N -> X==A[result]
  #@ensures result == N -> not isIn(X,A)
  i = 0
  j = N
  while (i < j-1):
    #@variant j-i
    #@invariant j>=i
    #@invariant 0<=i<=j<=N
    #@invariant isIn(X, A) -> isInSub(X, A,i,j)
    m = (i+j) // 2
    if (X < A[m]):
      j =  m
    else:
      i = m
  if (i < N and X==A[i]):
    return i
  else:
    return N

l1=[1,2,3,5,18]
r = recherche_dicho(5, l1, 3)
#@assert r == 3

r = recherche_dicho(5, l1, 20)
#@assert r == 5

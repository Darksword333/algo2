#@ predicate requires_sqrt(n:int) = n >= 0
#@ predicate ensures_sqrt(n:int, r:int) = r*r <= n < (r+1)*(r+1)



def sqrt(n:int) -> int:
    #@requires requires_sqrt(n)
    #@ensures ensures_sqrt(n, result)
    i = 0
    j = n+1
    while (i + 1)< j:
        #@variant j-i
        #@invariant i + 1 <= j
        #@invariant i*i <= n < j*j
        m = (i+j)//2
        if m*m <= n:
            i = m
        else:
            j = m
    return i
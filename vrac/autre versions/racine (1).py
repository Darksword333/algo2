def racine(n):
    #@requires n >=0
    #@ensures forall r.result ==r -> r*r <= n <= (r+1)*(r+1)
    s = n+1
    r = 0
    while s>r+1:
        #@variant s-r
        #@invariant r >= 0 and r*r <= n <= s*s and s >= r+1
        m = (r+s)//2
        x = m*m
        if (x >n):
            s = m
        else:
            r = m
    return r
    
a = racine(2)
#@assert a == 1


def racine(n):
    #@requires n >=0
    #@ensures result*result <= n < (result+1)*(result+1)
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
a = racine(4)
#@assert a == 2
a = racine(6)
#@assert a == 2
a = racine(56)
#@assert a == 7
a = racine(49)
#@assert a == 7
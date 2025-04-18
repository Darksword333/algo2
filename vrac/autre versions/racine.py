def racine(n):
    #@requires n >=0
    #@ensures forall r.result ==r -> r*r <= n < (r+1)*(r+1)
    r = 0
    while (r+1)*(r+1) <=n:
        #@variant n-r
        #@invariant r*r <= n 
        r +=1
    return r
a = racine(2)
#@assert a == 1
a = racine(36)
#@assert a == 6
a = racine(6)
#@assert a == 2
a = racine(56)
#@assert a == 7
a = racine(49)
#@assert a != 5
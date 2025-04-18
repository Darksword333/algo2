def div_mod(a:int, b:int) -> Tuple[int,int]:
    #@ requires a>=0 and b>=1
    #@ ensures forall q,r. result==(q,r) -> r<b
    #@ ensures forall q,r. result==(q,r) -> r>=0
    #@ ensures forall q,r. result == (q, r) -> q * b + r == a
    q , r = 0 , a
    while r>=b:
        #@ invariant r>=0
        #@ invariant a==b*q+r
        #@ variant r
        #@ assert (r-b) >= 0 and a==b*q+r 
        q += 1 
        #@ assert (r-b) >= 0 and a==b*q+r-b 
        r -= b 
        #@ assert r >= 0 and a==b*q+r
    return ( q , r )

r= div_mod(5,3)
#@assert r == (1,2)
r =div_mod(2,2)
#@assert r == (1,0)
r =div_mod(17,5)
#@assert r == (3,2)
r =div_mod(24,5)
#@assert r == (4,4)
r =div_mod(1,4)
#@assert r == (0,1)
 
#contre exemples
 
r =div_mod(7,5)
#@assert r != (2,-2)
r =div_mod(14,4)
#@assert r != (3,1)
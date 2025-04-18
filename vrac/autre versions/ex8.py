#@function
def power(n:int, m:int)->int:
    #@requires m>=0
    #@variant m
    return 1 if m == 0 else n*power(n,m-1)

#@lemma pow_sqr : forall x,y. y>=0 -> power(x*x,y) == power(x,2*y)

def pow_sqr(x:int,y:int):
    #@requires y>=0
    #@variant y
    #@ensures power(x*x,y) == power(x,2*y)
    if (y>0):
        pow_sqr(x*x,y//2)

def expR(A:int, B:int)->int:
    #@requires B>=0
    #@ensures result == power(A,B)
    x,y = A,B
    z=1
    while(y>0):
        #@variant y
        #@invariant z*power(x,y)==power(A,B)
        #@invariant y>=0
        #@invariant B>=y
        if (y%2==0):
            #@use pow_sqr(x,y)
            #@assert z*power(x*x,y//2)== power(A,B)
            x,y=x*x,y//2
            #@assert z*power(x,y)==power(A,B)
        else :
            #@assert z*x*power(x,y-1)==power(A,B)
            z,y = z*x,y-1
            #@assert z*power(x,y) == power(A,B)
        #@assert z*power(x,y) == power(A,B)
    return z


r = expR(1,2)
#@assert r == power(1,2)

r = expR(2,2)
#@assert r == power(2,2)

r = expR(2,3)
#@assert r == power(2,3)
#@function
def power(n:int,m:int) -> int:
    #@variant m
    return 1 if m <= 0 else n*power(n,m-1)


def pow_sqr(x:int, y:int):
    #@requires x >= 0
    #@requires y >= 0
    #@variant y
    #@ensures power(x * x, y) == power(x, 2 * y)
    if y != 0:
        pow_sqr(x, y - 1)

def expR(A: int, B:int) -> int:
    #@requires A>=0 and B>=0
    #@ensures result == power(A,B)
    x , y = A, B
    z = 1
    while ( y>0) :
        #@variant y
        #@invariant z * power(x, y) == power(A , B)
        #@invariant B >= y and y >= 0 and x>=0
        if ( y%2 == 0 ):
            #@call pow_sqr(x,y//2)
            #@assert z*power(x, y)==power(A, B)
            x , y = x*x , y//2
            #@assert z*power(x, y) == power(A, B)
        else:
            #@assert z*power(x, y)==power(A, B)
            z , y = z*x , y-1
            #@assert z*power(x, y) == power(A, B)
        #@assert z*power(x, y) == power(A, B)
    return z

r = expR(2,2) 
#@ assert r==4
r = expR(1,5) 
#@ assert r==1

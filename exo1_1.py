#@ predicate carres_post(n:int, sum:int) = sum == (n*(n+1)*(2*n+1)) // 6

def carres(n:int) -> int:
    #@ requires n >= 0
    #@ ensures carres_post(n,result)
    pass

r = carres(0)
#@ assert r==0
r = carres(1)
#@ assert r==1
r = carres(2)
#@ assert r==5
r = carres(3)
#@ assert r==14
r = carres(4)
#@ assert r==30

r = carres(7)
#@ assert r!=26
r = carres(8)
#@ assert r!=21
r = carres(9)
#@ assert r!=13
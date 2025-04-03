#@ function abs(n:int) -> int = if n >= 0 then n else -n

def abs_max(a:int, b:int, c:int) -> int:
    #@ ensures result == abs(a) or result == abs(b) or result == abs(c)
    #@ ensures result >= abs(a)
    #@ ensures result >= abs(b)
    #@ ensures result >= abs(c)
    pass

r = abs_max (5, 8, 2)
#@ assert r == 8 

r = abs_max(-2, 4, -6)
#@ assert r == 6

r = abs_max (17, -3, 2)
#@ assert r == 17 

r = abs_max (-2, -4, -10)
#@ assert r == 10

r = abs_max (4, -10, 8)
#@ assert r != 8

r = abs_max (7, -1, -9)
#@ assert r != -9
#@ function fib(n:int)->int 
#@ assume fib(0) == 0
#@ assume fib(1) == 1
#@ assume forall n. n>1 -> fib(n) == fib(n-1)+fib(n-2)
def m_fib(n: int) -> int:
    #@ requires n >= 0  
    #@ ensures result==fib(n)
    pass
r = m_fib ( 0 )
#@ assert r == 0
r = m_fib ( 1 )
#@ assert r == 1
r = m_fib ( 2 )
#@ assert r == 1
r = m_fib ( 3 )
#@ assert r == 2
r = m_fib ( 4 )
#@ assert r == 3
# contre exemples
r = m_fib ( 3 )
#@ assert r != 5
r = m_fib ( 4 )
#@ assert r != 7
r = m_fib ( 5 )
#@ assert r != 13

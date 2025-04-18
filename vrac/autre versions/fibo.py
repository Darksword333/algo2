#@function
def fib ( n : int )->int :
    #@variant n
    return n if n <= 1 else fib(n-1)+fib(n-2)
def fib_pos(n):
    #@requires n > 0
    #@ensures fib(n) > 0
    #@ variant n
    if n>2:
        fib_pos(n-1)
        fib_pos(n-2)
def m_fib ( n : int )->int :
    #@requires n>=0
    #@ensures result == fib(n)
    if n==0 :
        return 0
    elif n <= 2:
        return 1
    else:
        i = 1
        fp = 0
        fn = 1
        while i < n:
            #@variant n-i
            #@invariant 1 <= i <= n
            #@invariant fp == fib(i-1)
            #@invariant fn == fib(i)
            fp , fn = fn , fp + fn
            i = i+1
        return fn
r = m_fib ( 0 )
#@assert r == 0
r = m_fib ( 1 )
#@assert r == 1
r = m_fib ( 2 )
#@assert r == 1
r = m_fib ( 3 )
#@assert r == 2
r = m_fib ( 4 )
#@assert r == 3
# contre exemples
r = m_fib ( 3 )
#@ assert r != 5
r = m_fib ( 4 )
#@ assert r != 7
r = m_fib ( 5 )
#@ assert r != 13

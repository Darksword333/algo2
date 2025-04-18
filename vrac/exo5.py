#@ function 
def fib(n: int) -> int:
    #@variant n
    return n if n <= 1 else fib(n - 1) + fib(n - 2) 
    
def fib_pos(n):
  #@ requires n>0
  #@ ensures fib(n)>0
  #@ variant n
  if n>2:
    fib_pos(n-1)
    fib_pos(n-2)

def m_fib(n:int)->int:
    #@requires n >= 0
    #@ensures result == fib(n)
    if n==0:
      return 0 
    else:
      fp,fn,i,stock=0,1,1,0
      while(i<n):
          #@ variant n-i
          #@ invariant 1<=i and i <= n
          #@ invariant fn==fib(i)
          #@ invariant fp==fib(i-1)
          #@assert 1<= i+1 <=n and fn == fib(i) and fn+fp== fib(i+1)
          stock=fn
          #@assert 1<= i+1 <=n and stock== fib(i) and fn+fp== fib(i+1)
          fn=fn + fp
          #@assert 1<= i+1 <=n and stock== fib(i) and fn== fib(i+1)
          fp=stock
          #@assert 1<= i+1 <=n and fp== fib(i) and fn== fib(i+1)
          i= i + 1
          #@assert 1<= n <= n and fp==fib(i-1) and fn ==fib(i)
      return fn
    

# Tests pour vérifier le comportement de m_fib
r = m_fib(0)
#@assert r == 0
r = m_fib(1)
#@assert r == 1
r = m_fib(2)
#@assert r == 1
r = m_fib(3)
#@assert r == 2
r = m_fib(4)
#@assert r == 3

# Contre-exemples pour vérifier des valeurs incorrectes
r = m_fib(3)
#@assert r != 5
r = m_fib(4)
#@assert r != 7
r = m_fib(5)
#@assert r != 13

def racine( n : int) -> int :
  #@requires n >= 0
  #@ensures forall r. result == r -> r*r <=n<(r+1)*(r+1)
  pass
  
def racine( n : int) -> int :
  #@requires n >= 0
  #@ensures result*result <=n<(result+1)*(result+1)
  r , f , m = 0 , n+1,n//2
  while (r+1<f) :
    #@invariant r*r <=n <f*f
    #@invariant r+1 <= f
    #@variant f-r
    m = (r+f)//2
    if m*m <= n:
      r = m 
    else:
      f = m
  return r
  
  
r = racine (10)
#@assert r == 3
r = racine (9)
#@assert r == 3
r = racine (25)
#@assert r == 5
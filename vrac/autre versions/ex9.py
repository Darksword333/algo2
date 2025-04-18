#@lemma diff_mod1: forall u,v. u>=v>=0 -> forall i.i>0 and (u-v)%i==0 and v%i==0 -> u%i==0
#@lemma diff_mod2: forall u,v. u>=v>=0 -> forall i.i>0 and u%i==0 and v%i==0 -> (u-v)%i==0
#@function
def pgcd1( a : int , b : int ) -> int :
  #@requires a >=0 and b >= 0
  #@requires a > 0 or b > 0
  #@ensures result > 0
  while b!= 0:
    #@variant b
    a,b = b,a%b
  return a

def pgcd(u: int, v: int) -> int:
    #@requires u > 0 and v > 0
    #@ensures result >= 0
    #@ensures u%result == 0 and v%result == 0
    while u != 0 and v != 0:
        #@variant u + v + 1
        #@invariant v>=0
        #@invariant u >= pgcd(u,v)
        #@invariant u>=0
        if u >= v:
          u = u - v
        else:
          v = v - u
    if u >= v:
        return u
    else:
       return v
r = pgcd(1,1)
#@assert r==1
r = pgcd(6,10)
#@assert r==2
r = pgcd(8,4)
#@assert r==4
#@lemma add_mod : forall u,v. forall i . i >0 and u%i ==0 and v%i ==0 -> (u+v)%i ==0
#@lemma diff_mod1 : forall u,v. forall i . i >0 and (u-v)%i ==0 and v%i ==0 -> u%i ==0
#@axiom opp_mod : forall u,i. i >0 and u%i ==0 -> (-u)%i ==0
#@lemma diff_mod2 : forall u,v. forall i . i >0 and u%i ==0 and v%i ==0 -> (u-v)%i ==0

def pgcd ( a:int, b:int) -> int:
    #@requires a >=0 and b >= 0
    #@requires a > 0 or b > 0
    #@ensures result > 0 
    #@ensures a%result==0
    #@ensures b%result==0
    #@ensures forall i . i >0 and a%i==0 and b%i==0 -> result%i==0
    u,v = a,b
    while u > 0 and v > 0:
        #@variant u+v
        #@invariant forall i. i > 0  -> ((a % i == 0 and b % i == 0) <-> (u % i == 0 and v % i == 0))
        #@invariant u >= 0 and v >= 0
        #@invariant u> 0 or v >0
        if ( u > v ):      
            u,v = u - v, v
        elif u == 0:
            p=v
        elif v==0: 
            p=u
        else:
            u, v = v, v - u
    p = u+v
    return p

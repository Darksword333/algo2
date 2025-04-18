#@predicate subT(s:list[int],t:list[int],p:int) = forall x. 0<=x<len(s) -> (p+x<len(t) and t[p+x] == s[x])

def sous_tableau(s:list[int],t:list[int],p:int)->bool:
    #@requires len(s)>0
    #@requires len(t)>0
    #@requires 0<=p<len(t)
    #@requires len(t)>=len(s)
    #@requires len(t)>=len(s) + p
    #@ensures result == subT(s,t,p)
    i=0
    while i < len(s):
      #@variant len(s)-i
      #@invariant len(t)>=len(s)
      #@invariant 0<=i<=len(s)
      #@invariant 0<=p<len(t)
      #@invariant subT(s[:i],t,p)
      if t[i+p] != s[i]:
        return False
      i=i+1
    return True

def recherche_derniere_position(s:list[int],t:list[int])->int:
    #@requires len(s)>0
    #@requires len(t)>0
    #@requires len(s)<=len(t)
    #@requires exists k. 0<=k<=len(t)-len(s) and subT(s,t,k)
    #@ensures 0<=result<=len(t)-len(s)
    #@ensures subT(s,t,result) or result == 0
    #@ensures forall k. result<k<=len(t) -> not subT(s,t,k)
    pos = len(t)-len(s)
    while pos>0:
        #@variant pos
        #@invariant len(t)>=len(s)
        #@invariant 0<=pos<=len(t)-len(s)
        #@invariant forall k. pos<k<=len(t) -> not subT(s,t,k)
        if sous_tableau(s,t,pos):
            return pos
        pos = pos-1
    return pos
    
    
s1 = [1,-1,5]
t = [7,1,-1,5,6,7]
r = sous_tableau(s1,t,1) 
#@assert r==True

s2 = [-1,6,5]
r = sous_tableau(s2,t,2) 
#@assert r!=True
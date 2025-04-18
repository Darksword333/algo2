#@ predicate subT(l1: list[int], l2:list[int], p:int) = 0 <= p <= len(l2)-len(l1) and forall I. 0<=I<len(l1) -> l1[I] == l2[I+p]
def sous_tableau(s,t,p):
    #@ requires 0 <= p <= len(t)-len(s)
    #@ ensures result == subT(s,t,p)
    i = 0
    while (i < len(s)):
        #@ invariant 0 <= i <= len(s)
        #@ invariant subT(s[:i], t, p)
        #@ variant len(s)-i
        if s[i] != t[p + i]:
            return False
        i += 1
    return True
s1 = [1,-1,5]
t = [7,1,-1,5,6,7]
r = sous_tableau(s1,t,1)
#@ assert r == True
s2 = [-1,6,5]
r = sous_tableau(s2,t,2)
#@ assert r != True
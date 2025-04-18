#@predicate appartient(T:list[int],B:int)=exists c. 0<=c<len(T) and T[c]==B
def recherche_lin(A:list[int],X:int)->int:
    #@ensures 0<=result<=len(A)
    #@ensures (result<len(A) and appartient(A,X) and A[result]==X) or (result == len(A) and not appartient(A,X))
    
    pos=0
    while pos<len(A):
        #@variant len(A)-pos
        #@invariant 0<=pos <=len(A)
        #@invariant forall d. 0<=d<pos -> A[d]!=X
        #@invariant not appartient(A[:pos],X)
        if A[pos]==X:
            #@ assert appartient(A,X)
            return pos
        pos = pos+1

    return pos
    
l1 = [5,4,3,2,1]
r = recherche_lin(l1,3) 
#@assert r==2

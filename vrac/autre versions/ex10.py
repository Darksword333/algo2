#@predicate appartient(T:list[int],B:int)=exists c. 0<=c<len(T) and T[c]==B

def recherche_lin_present(A:list[int],X:int)->int:
    #@requires len(A)>0
    #@requires appartient(A,X)
    #@ensures 0<=result<=len(A)
    #@ensures A[result] == X

    # @ensures (result<len(A) and appartient(A,X) and A[result]==X) or (result == len(A) and not appartient(A,X)) 
    pos=0
    while pos<len(A):
        #@variant len(A)-pos
        #@invariant 0<=pos <=len(A)
        #@invariant forall d. 0<=d<pos -> A[d]!=X
        if A[pos]==X:
            return pos
        pos = pos+1
    return pos
    
l1 = [5,4,3,2,1]
r = recherche_lin_present(l1,3)
# @assert r==2

l2 = [-1,0,6,4,2]
r = recherche_lin_present(l2,4) 
# @ assert r==3

l3 = [8]
r = recherche_lin_present(l3,8)
# @assert r==0
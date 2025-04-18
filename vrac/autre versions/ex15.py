def plateau(A:list[int])->int:
    #@requires len(A)>0    
    #@requires forall i. 0<=i<len(A)-1 -> A[i]<=A[i+1]
    #@ensures 1<=result<=len(A)
    
    i=1
    l=1
    p=1
    while i<len(A):
        #@variant len(A)-i
        #@invariant 1<=i<=len(A)
        #@invariant 1<=l<=i
        #@invariant 1<=l<=len(A)
        #@invariant 1<=p<=len(A)
        #@invariant p>=l
        if A[i-1]==A[i]:
            l = l+1
        else :
            l=1
        if p < l:
            p=l
        i = i+1
    return p
        

t1 = [1,2,2,3,3,3,4]
r = plateau(t1)
#@assert r == 3

t2 = [2]
r = plateau(t2)
#@assert r == 1

t3 = [0,0,0,0,0]
r = plateau(t3)
#@assert r == 5
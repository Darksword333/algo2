#@function
def sum(a:list[int], i:int)->int:
    #@ variant i
    return a[i-1]+sum(a,i-1) if 0<i and i<=len(a) else 0
    
def pmax(a:list[int])->int:
    #@requires len(a)>0
    #@requires a[0]==0
    #@ensures 0<=result<len(a)
    #@ensures a[result] == sum(a,result-1)
    i=0
    max_somme = 0
    max_indice = 0
    while i<len(a):
        #@variant len(a)-i
        #@invariant 0<=i<=len(a)
        #@invariant 0<=max_indice<len(a)
        #@invariant max_indice<=i
        #@invariant a[max_indice] == sum(a,max_indice-1)
        #@invariant max_somme == a[max_indice]
        if sum(a,i-1)==a[i] and a[i]>max_somme:
            max_somme = a[i]
            max_indice = i
        i=i+1
        
    return max_indice
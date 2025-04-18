#@function 
def sum(a:list[int], i:int) -> int:
  #@requires len(a) > i >= -1
  #@variant i
  return a[i] + sum(a, i - 1) if 0 < i and i <= len(a) else 0
def pmax(t:list[int]) -> int:
    #@requires len(t) > 0
    #@requires t[0]==0
    #@ensures 0<=result<len(t)
    #@ensures t[result] == sum(t, result-1)
    #@ensures forall I.0 <= I < len(t) and t[I]==sum(t,I-1) -> t[I] <= t[result]
    i,s,p = 1,0,0
    while i<len(t):
        #@invariant 1 <= i <= len(t)
        #@invariant 0 <= p < i
        #@invariant t[p] == sum(t,p-1)
        #@invariant s == sum(t,i-1)
        #@invariant forall I.0<=I<i and t[I]==sum(t,I-1) -> t[I] <= t[p]
        #@variant len(t)-i
        if (s == t[i] and s >= t[p]):
            p = i
        i = i+1
        s = s+t[i-1]
    return p
#@predicate sum_pre(n:int) = n>=0
#@predicate sum_post(n:int, sum:int) = sum == (n*(n-1))//2

def sum(n:int)->int:
    #@requires sum_pre(n)
    #@ensures sum_post(n, sum)
    pass

r = sum( 0 )
#@assert r ==0
r = sum( 1 )
#@assert r ==1
r = sum( 2 )
#@assert r ==3
r = sum( 3 )
#@assert r ==6
r = sum( 4 )
#@ assert r ==10
r = sum( 5 )
#@ assert r ==15

# contre exemples
r = sum( 7 )
#@ assert r != 26
r = sum( 8 )
#@ assert r != 21
r = sum( 9 )
#@ assert r != 13
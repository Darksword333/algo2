def div_mod ( a : int , b : int ) -> Tuple [ int , int ] :
    #@requires b > 0
    #@ensures r =  # proprietes du reste
    #@ensures ...
    q , r = 0 , a
    while ( r >=b ) :
        #@invariant a == q*b+r
        #@invariant r >= 0
        #@variant r
        q += 1
        r -= b
    return ( q , r )

r = div_mod ( 5 , 3 )
#@assert r == (1 ,2)
r = div_mod ( 2 , 2 )
#@assert r == (1 ,0)
r = div_mod ( 17 , 5 )
#@assert r == (3 ,2)
r = div_mod ( 24 , 5 )
#@assert r == (4 ,4)
r = div_mod ( 1 , 4 )
#@assert r == (0 ,1)
# contre exemples
r = div_mod ( 7 , 5 )
#@assert r != (2 , -2)
r = div_mod ( 14 , 4 )
#@assert r != (3 ,2)

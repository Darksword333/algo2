def pgcd ( a : int , b : int ) −> int :
    #@requires a >=0 and b >= 0
    #@requires a > 0 or b > 0
    #@ensures result > 0
    
    
r = pgcd ( 1 , 1 )
#@ assert r == 1
r = pgcd ( 6 , 1 0 )
#@ assert r == 2
r = pgce ( 8 , 4 )
#@ assert r == 4
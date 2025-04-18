
#@ predicate oneOf(x: int, a: int, b: int, c: int) = x == a or x == b or x == c
#@ predicate exch(x: int, y: int, z: int, a: int, b: int, c: int) = oneOf(x, a, b, c) and oneOf(y, a, b, c) and oneOf(z, a, b, c)

#@ function gt(x: int, y: int) -> int = if x > y then 1 else 0

def tri3V2(a: int, b: int, c: int) -> Tuple[int, int, int]:
    #@requires a != b and b != c and a != c
    #@requires a>=0 and b>=0 and c>=0
    #@ensures forall x, y, z. result == (x, y, z) -> x < y < z
    #@ensures forall x, y, z. result == (x, y, z) -> exch(x, y, z, a, b, c)
    
    x, y, z = a, b, c
    
    # Boucle pour trier les valeurs en utilisant des échanges
    while x >= y or y >= z:
        #@variant x,y,z #remplacement 
        #@invariant x >= 0 and y >= 0 and z>=0
        #@invariant x != y and y != z and x != z
        #@invariant exch(x, y, z, a, b, c)
        
        if x >= y:
            x, y = y, x
        elif y >= z:
            y, z = z, y
    
    return (x, y, z)

#pourquoi ca marche pas : car x,y, nest pas un variant strict qui diminue a chaque iteration 

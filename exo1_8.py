def racine_entiere(N : int) -> int:
    #@ requires N >= 0
    #@ ensures result*result <= N < (result+1)*(result+1)
    inf, sup = 0, N+1
    while (sup-inf>1):
        #@ invariant 0<= inf < sup <= N+1
        #@ invariant inf*inf<=N<sup*sup
        #@ variant sup-inf
        milieu = (sup+inf)//2
        if milieu*milieu <= N :
            inf = milieu
        else:
            sup = milieu          
    return inf
r = racine_entiere(10)
#@ assert r == 3
r = racine_entiere(14)
#@ assert r == 3
r = racine_entiere(21)
#@ assert r == 4
r = racine_entiere(33)
#@ assert r == 5
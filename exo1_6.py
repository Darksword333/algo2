#@ function fib(n:int)->int 
#@ assume fib(0) == 0
#@ assume fib(1) == 1
#@ assume forall n. n>1 -> fib(n) == fib(n-1)+fib(n-2)

#@ function
def signe(n: int) -> int:
    #@ requires n > 0
    #@ variant n
    #@ ensures result == (-1) or result == 1
    return -1 if n == 1 else -signe(n-1)

def ocagne(n: int) -> unit:
    #@ requires n >= 2
    #@ variant n
    #@ ensures fib(n)*fib(n) - fib(n-1)*fib(n+1) == signe(n+1)
    if n > 2:
        ocagne(n-1)
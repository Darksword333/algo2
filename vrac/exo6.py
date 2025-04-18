#@function
def fib(n: int) -> int:
    #@requires n >= 0
    #@variant n
    return n if n <= 1 else fib(n - 1) + fib(n - 2)

#@function
def signe(n: int) -> int:
    #@requires n >= 0
    #@variant n
    #@ensures (n % 2 == 0 and result == 1) or (n % 2 != 0 and result == -1)
    return 1 if n == 0 else -1 * signe(n - 1)

def ocagne(n: int) -> unit:
    #@requires n >= 2
    #@variant n
    #@ensures fib(n) * fib(n) - fib(n - 1) * fib(n + 1) == signe(n + 1)
    if n > 2:
        ocagne(n - 1)

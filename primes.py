import sys

def sieve_of_eratosthenes(n):
    is_prime = [True] * (n + 1)
    is_prime[0] = False
    is_prime[1] = False

    for p in range(2, int(n**0.5) + 1):
        if is_prime[p]:
            for i in range(p * p, n + 1, p):
                is_prime[i] = False

    primes = [i for i in range(2, n + 1) if is_prime[i]]

    return primes

def main():
    if len(sys.argv) != 2:
        print("Usage: python primes.py <k>")
        sys.exit(1)

    try:
        k = int(sys.argv[1])
    except ValueError:
        print("Error: k should be a valid integer")
        sys.exit(1)

    primes = sieve_of_eratosthenes(k)
    print(f"Prime numbers not greater than {k}: {primes}")

if __name__ == "__main__":
    main()

package main

import (
	"fmt"
	"os"
	"strconv"
)

func sieveOfEratosthenes(n int) []int {
	isPrime := make([]bool, n+1)
	for i := 2; i <= n; i++ {
		isPrime[i] = true
	}

	for p := 2; p*p <= n; p++ {
		if isPrime[p] {
			for i := p * p; i <= n; i += p {
				isPrime[i] = false
			}
		}
	}

	var primes []int
	for i := 2; i <= n; i++ {
		if isPrime[i] {
			primes = append(primes, i)
		}
	}

	return primes
}

func main() {
	if len(os.Args) != 2 {
		fmt.Println("Usage: go run primes.go <k>")
		os.Exit(1)
	}

	k, err := strconv.Atoi(os.Args[1])
	if err != nil {
		fmt.Println("Error: k should be a valid integer")
		os.Exit(1)
	}

	primes := sieveOfEratosthenes(k)
	fmt.Printf("Prime numbers not greater than %d: %v\n", k, primes)
}

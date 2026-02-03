"""A human-written Python program to numerically verify the conjecture."""


def N(k: int, n: int) -> int:
    m = (k - 1) // 2
    count = 0
    for b1 in range(1, m + 1):
        for b2 in range(1, m + 1):
            if b1 + b2 >= m + 1 and b2 % k == n * b1 % k:
                count += 1
    return count


def F(k: int, a: int) -> int:
    m = (k - 1) // 2
    return sum((a * i + m) // k for i in range(1, m + 1))


def verify(k: int) -> int:
    m = (k - 1) // 2
    print(f"k={k}, m={m}")
    print("n | N_k(n) | F_k(n+1)-F_k(n) | Verdict")
    count = 0
    for n in range(1, 100):
        LHS = N(k, n)
        RHS = F(k, n + 1) - F(k, n)
        verdict = "✅" if LHS == RHS else "❌"
        count += 1 if LHS == RHS else 0
        print(f"{n}\t{LHS}\t{RHS}\t\t{verdict}")
    print()
    return count


if __name__ == "__main__":
    count = 0
    for k in range(3, 100, 2):
        count += verify(k)
    print(f"{count} / 4851 cases verified")

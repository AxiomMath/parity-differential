import Mathlib

/-
# Problem Description

Let $k \ge 3$ be an odd integer and let $m = (k-1)/2$.

For $n \in \mathbb{N}$ with $\gcd(n, k) = 1$ and $\gcd(n+1, k) = 1$, define $N_k(n)$ to be the
number of pairs $(b_1, b_2) \in \mathbb{N} \times \mathbb{N}$ such that:
1. $1 \le b_1 \le m$
2. $1 \le b_2 \le m$
3. $b_1 + b_2 \ge m + 1$
4. $b_2 \equiv n \cdot b_1 \pmod{k}$

For any $a \in \mathbb{N}$, define:
$$F_k(a) := \sum_{i=1}^{m} \left\lfloor \frac{a \cdot i + m}{k} \right\rfloor$$

The theorem states: $N_k(n) = F_k(n+1) - F_k(n)$
-/

-- Parameters:
-- k: an odd integer with k ≥ 3
-- m = (k - 1) / 2

-- Main Definition(s)

/-- The counting function N_k(n): counts pairs (b₁, b₂) with 1 ≤ b₁, b₂ ≤ m,
    b₁ + b₂ ≥ m + 1, and b₂ ≡ n · b₁ (mod k). -/
def countingFunctionN (k : ℕ) (n : ℕ) : ℕ :=
  let m := (k - 1) / 2
  Finset.card (Finset.filter
    (fun p : ℕ × ℕ => m + 1 ≤ p.1 + p.2 ∧ p.2 % k = (n * p.1) % k)
    (Finset.Icc 1 m ×ˢ Finset.Icc 1 m))

/-- The floor sum function F_k(a) = ∑_{i=1}^{m} ⌊(a·i + m)/k⌋ -/
def floorSumF (k : ℕ) (a : ℕ) : ℕ :=
  let m := (k - 1) / 2
  ∑ i ∈ Finset.Icc 1 m, (a * i + m) / k

-- Main Statement(s)

/-- For k ≥ 3 odd, m = (k-1)/2, and n coprime to both k and k (ensuring gcd(n,k) = 1 and
    gcd(n+1,k) = 1), we have N_k(n) = F_k(n+1) - F_k(n).

    The equation is stated in ℤ to avoid issues with truncated natural number subtraction. -/
theorem main_theorem (k : ℕ) (n : ℕ)
    (hk_ge : 3 ≤ k)
    (hk_odd : Odd k)
    (hn_coprime : Nat.Coprime n k)
    (hn1_coprime : Nat.Coprime (n + 1) k) :
    (countingFunctionN k n : ℤ) = (floorSumF k (n + 1) : ℤ) - (floorSumF k n : ℤ) := by
  sorry

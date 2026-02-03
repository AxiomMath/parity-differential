Let $\mathbb{N} = \{0, 1, 2, \cdots\}$ be the set of natural numbers.

Let $k \ge 3$ be an odd integer and set $m = \frac{k-1}{2}$.

For $n \in \mathbb{N}$ with $\mathrm{gcd}(n,k) = \mathrm{gcd}(n+1,k) = 1$, define $N_k(n)$ to be the number of pairs $(b_1, b_2) \in \mathbb{N} \times \mathbb{N}$ such that:
$$1 \le b_1, b_2 \le m; b_1 + b_2 \ge m + 1; b_2 \equiv nb_1 \pmod k$$

Furthermore, for any $a \in \mathbb{N}$ ($k, m$ as above) define:
$$\displaystyle F_k(a) := \sum_{i=1}^m \left\lfloor \dfrac{ai+m}{k} \right\rfloor$$

Prove the following lemma (again assumptions as above):
$$N_k(n) = F_k(n+1) - F_k(n)$$

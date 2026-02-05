import Mathlib

def countingFunctionN (k : Nat) (n : Nat) : Nat :=
  let m := (k - 1) / 2
  Finset.card (Finset.filter
    (fun p : Nat × Nat => m + 1 ≤ p.1 + p.2 ∧ p.2 % k = (n * p.1) % k)
    (Finset.Icc 1 m ×ˢ Finset.Icc 1 m))

def floorSumF (k : Nat) (a : Nat) : Nat :=
  let m := (k - 1) / 2
  ∑ i ∈ Finset.Icc 1 m, (a * i + m) / k

lemma two_mul_m_eq (k : ℕ) (hk_odd : Odd k) : 2 * ((k - 1) / 2) = k - 1 := by
  obtain ⟨t, ht⟩ := hk_odd; omega

lemma div_of_succ_mul (k n i m : ℕ) (hk_pos : 0 < k) :
    ((n + 1) * i + m) / k = (n * i + m) / k + ((n * i + m) % k + i) / k := by
  set q := (n * i + m) / k; set r := (n * i + m) % k
  have h_div_alg : k * q + r = n * i + m := Nat.div_add_mod (n * i + m) k
  have h_expand : (n + 1) * i + m = k * q + (r + i) := by
    calc (n + 1) * i + m = n * i + i + m := by ring
      _ = n * i + m + i := by ring
      _ = (k * q + r) + i := by rw [← h_div_alg]
      _ = k * q + (r + i) := by ring
  rw [h_expand, Nat.add_div_of_dvd_right (dvd_mul_right k q), Nat.mul_div_cancel_left q hk_pos]

lemma floor_diff_eq (k n i : ℕ) (hk_pos : 0 < k) :
    ((n + 1) * i + (k - 1) / 2) / k - (n * i + (k - 1) / 2) / k =
      ((n * i + (k - 1) / 2) % k + i) / k := by
  simp only [div_of_succ_mul k n i ((k - 1) / 2) hk_pos, add_tsub_cancel_left]

lemma floor_sum_diff_nonneg (k n i : ℕ) :
    (n * i + (k - 1) / 2) / k ≤ ((n + 1) * i + (k - 1) / 2) / k := by
  exact Nat.div_le_div_right (by have h := Nat.mul_le_mul_right i (Nat.le_succ n); linarith)

lemma mod_eq_sub_when_large (k n i : ℕ) (hk_ge : 3 ≤ k) (hk_odd : Odd k)
    (hr_large : (n * i) % k > (k - 1) / 2) :
    (n * i + (k - 1) / 2) % k + k = (n * i) % k + (k - 1) / 2 := by
  have h1 : ((k - 1) / 2) % k = (k - 1) / 2 := Nat.mod_eq_of_lt (by omega)
  have h2 : k ≤ (n * i) % k + ((k - 1) / 2) % k := by obtain ⟨t, ht⟩ := hk_odd; omega
  have h3 := Nat.add_mod_add_of_le_add_mod h2
  omega

lemma floor_term_eq_indicator (k n i : ℕ) (hk_ge : 3 ≤ k) (hk_odd : Odd k)
    (_hi_lo : 1 ≤ i) (hi_hi : i ≤ (k-1)/2) :
    ((n * i + (k - 1) / 2) % k + i) / k =
    if (n * i) % k ∈ Finset.Icc 1 ((k-1)/2) ∧ i + (n * i) % k ≥ (k-1)/2 + 1 then 1 else 0 := by
  by_cases h : (n * i) % k ∈ Finset.Icc 1 ((k-1)/2) ∧ i + (n * i) % k ≥ (k-1)/2 + 1
  · rw [if_pos h]
    have h1 : (n * i) % k ≤ (k - 1) / 2 := (Finset.mem_Icc.mp h.1).2
    have h2 : (n * i + (k - 1) / 2) % k = (n * i) % k + (k - 1) / 2 := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : (k - 1) / 2 < k)]
      exact Nat.mod_eq_of_lt (by obtain ⟨t, ht⟩ := hk_odd; omega)
    rw [h2]
    apply Nat.div_eq_of_lt_le <;> (obtain ⟨t, ht⟩ := hk_odd; omega)
  · rw [if_neg h]; push_neg at h
    by_cases hr_small : (n * i) % k ≤ (k-1)/2
    · by_cases hr_zero : (n * i) % k = 0
      · simp only [Nat.add_mod, hr_zero, zero_add, Nat.mod_eq_of_lt (by omega : (k - 1) / 2 < k)]
        exact Nat.div_eq_of_lt (by obtain ⟨m, hm⟩ := hk_odd; omega)
      · have hr_in : (n * i) % k ∈ Finset.Icc 1 ((k-1)/2) := Finset.mem_Icc.mpr ⟨by omega, hr_small⟩
        have hr_sum_small := h hr_in
        have h1 : (n * i + (k - 1) / 2) % k = (n * i) % k + (k - 1) / 2 := by
          rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : (k - 1) / 2 < k)]
          exact Nat.mod_eq_of_lt (by obtain ⟨t, ht⟩ := hk_odd; omega)
        rw [h1]
        apply Nat.div_eq_of_lt
        obtain ⟨t, ht⟩ := hk_odd
        omega
    · have h_mod_eq := mod_eq_sub_when_large k n i hk_ge hk_odd (by omega)
      have h_2m := two_mul_m_eq k hk_odd
      have h_r_lt_k : (n * i) % k < k := Nat.mod_lt _ (by omega)
      exact Nat.div_eq_of_lt (by omega)

lemma count_for_fixed_i (k n i : ℕ) (hk_ge : 3 ≤ k) (_hi_lo : 1 ≤ i) (_hi_hi : i ≤ (k-1)/2) :
    (Finset.filter (fun j => (k-1)/2 + 1 ≤ i + j ∧ j % k = (n * i) % k)
      (Finset.Icc 1 ((k-1)/2))).card =
    if (n * i) % k ∈ Finset.Icc 1 ((k-1)/2) ∧ i + (n * i) % k ≥ (k-1)/2 + 1 then 1 else 0 := by
  have h1 : (Finset.filter (fun j => (k-1)/2 + 1 ≤ i + j ∧ j % k = (n * i) % k)
      (Finset.Icc 1 ((k-1)/2))) =
      if (n * i) % k ∈ Finset.Icc 1 ((k-1)/2) ∧ i + (n * i) % k ≥ (k-1)/2 + 1
      then {(n * i) % k} else ∅ := by
    split_ifs with h
    · ext j
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
      constructor
      · intro ⟨⟨hj_lo, hj_hi⟩, _, hj_mod⟩
        rw [Nat.mod_eq_of_lt (by omega : j < k)] at hj_mod
        exact hj_mod
      · intro hj
        have h_r_lo : 1 ≤ (n * i) % k := (Finset.mem_Icc.mp h.1).1
        have h_r_hi : (n * i) % k ≤ (k - 1) / 2 := (Finset.mem_Icc.mp h.1).2
        exact ⟨⟨by omega, by omega⟩, by omega, by simp [hj, Nat.mod_eq_of_lt (by omega : (n * i) % k < k)]⟩
    · apply Finset.filter_eq_empty_iff.mpr
      intro j hj; simp only [Finset.mem_Icc] at hj
      intro hc
      have hj_mod : j % k = j := Nat.mod_eq_of_lt (by omega)
      have h_r_in : (n * i) % k ∈ Finset.Icc 1 ((k-1)/2) := by simp only [Finset.mem_Icc]; rw [hj_mod] at hc; omega
      exact h ⟨h_r_in, by rw [hj_mod] at hc; omega⟩
  rw [h1]; split_ifs <;> simp

lemma countingN_as_sum_over_i (k n : ℕ) :
    countingFunctionN k n = ∑ i ∈ Finset.Icc 1 ((k-1)/2),
      (Finset.filter (fun j => (k-1)/2 + 1 ≤ i + j ∧ j % k = (n * i) % k)
        (Finset.Icc 1 ((k-1)/2))).card := by
  simp only [countingFunctionN]
  calc
    (Finset.filter (fun p : ℕ × ℕ => (k - 1) / 2 + 1 ≤ p.1 + p.2 ∧ p.2 % k = (n * p.1) % k)
        (Finset.Icc 1 ((k - 1) / 2) ×ˢ Finset.Icc 1 ((k - 1) / 2))).card
      = ∑ x ∈ Finset.Icc 1 ((k - 1) / 2) ×ˢ Finset.Icc 1 ((k - 1) / 2),
          if (k - 1) / 2 + 1 ≤ x.1 + x.2 ∧ x.2 % k = (n * x.1) % k then 1 else 0 := by
        rw [← Finset.sum_filter]; simp
    _ = ∑ i ∈ Finset.Icc 1 ((k - 1) / 2), ∑ j ∈ Finset.Icc 1 ((k - 1) / 2),
          if (k - 1) / 2 + 1 ≤ i + j ∧ j % k = (n * i) % k then 1 else 0 := by rw [Finset.sum_product]
    _ = ∑ i ∈ Finset.Icc 1 ((k - 1) / 2),
          (Finset.filter (fun j => (k - 1) / 2 + 1 ≤ i + j ∧ j % k = (n * i) % k)
            (Finset.Icc 1 ((k - 1) / 2))).card := by
        apply Finset.sum_congr rfl; intro i _; rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]

lemma countingN_eq_sum (k n : ℕ) (hk_ge : 3 ≤ k) (hk_odd : Odd k) :
    countingFunctionN k n =
      ∑ i ∈ Finset.Icc 1 ((k - 1) / 2), ((n * i + (k - 1) / 2) % k + i) / k := by
  rw [countingN_as_sum_over_i]
  apply Finset.sum_congr rfl; intro i hi
  rw [Finset.mem_Icc] at hi
  rw [count_for_fixed_i k n i hk_ge hi.1 hi.2, floor_term_eq_indicator k n i hk_ge hk_odd hi.1 hi.2]

lemma floorSum_diff_eq_sum (k n : ℕ) (hk_ge : 3 ≤ k) :
    floorSumF k (n + 1) - floorSumF k n =
      ∑ i ∈ Finset.Icc 1 ((k - 1) / 2), ((n * i + (k - 1) / 2) % k + i) / k := by
  unfold floorSumF
  rw [← Finset.sum_tsub_distrib]
  · apply Finset.sum_congr rfl; intro i _; exact floor_diff_eq k n i (by omega)
  · intro i _; exact floor_sum_diff_nonneg k n i

lemma cast_floorSum_diff (k n : ℕ) :
    (floorSumF k (n + 1) : ℤ) - (floorSumF k n : ℤ) =
      ((floorSumF k (n + 1) - floorSumF k n : ℕ) : ℤ) := by
  have h1 : floorSumF k (n + 1) ≥ floorSumF k n := by
    simp only [floorSumF]; apply Finset.sum_le_sum; intro i _
    exact Nat.div_le_div_right (by have h := Nat.mul_le_mul_right i (Nat.le_succ n); linarith)
  omega

theorem main_theorem (k : ℕ) (n : ℕ)
    (hk_ge : 3 ≤ k) (hk_odd : Odd k)
    (_hn_coprime : Nat.Coprime n k) (_hn1_coprime : Nat.Coprime (n + 1) k) :
    (countingFunctionN k n : ℤ) = (floorSumF k (n + 1) : ℤ) - (floorSumF k n : ℤ) := by
  rw [cast_floorSum_diff k n, floorSum_diff_eq_sum k n hk_ge, countingN_eq_sum k n hk_ge hk_odd]

import PalindromicPowers.Assumptions

/-!
# HFF blocks 2–8: digits, reversal, geometric and harmonic sums
-/

namespace PalindromicPowers

open Finset Real

variable {g k : ℕ}

/-- Auxiliary for [HFF 2].  A digit tuple of length `j` gives a number `< g^j`
(its value is at most `(g-1)∑_{i<j} gⁱ = g^j - 1`). -/
private theorem digits_sum_lt :
    ∀ (j : ℕ) (d : ℕ → ℕ), (∀ i < j, d i < g) → ∑ i ∈ range j, d i * g ^ i < g ^ j := by
  intro j
  induction j with
  | zero => intro d _; simp
  | succ j ih =>
    intro d hd
    have h1 := ih d (fun i hi => hd i (by omega))
    have h2 : d j + 1 ≤ g := hd j (by omega)
    have h3 : (d j + 1) * g ^ j ≤ g * g ^ j := Nat.mul_le_mul_right _ h2
    rw [sum_range_succ, pow_succ]
    nlinarith

/-- Auxiliary for [HFF 2].  The digit in position `i` of `∑_{r<j} d_r g^r` is `d_i`
(reduce modulo `g`, subtract, divide by `g`, and induct on `j`). -/
private theorem digits_sum_digit (hg : 2 ≤ g) :
    ∀ (j : ℕ) (d : ℕ → ℕ), (∀ i < j, d i < g) →
      ∀ i < j, (∑ r ∈ range j, d r * g ^ r) / g ^ i % g = d i := by
  have hg0 : 0 < g := by omega
  intro j
  induction j with
  | zero => intro d _ i hi; omega
  | succ j ih =>
    intro d hd i hi
    -- `∑_{r<j+1} d_r g^r = d_0 + g · ∑_{r<j} d_{r+1} g^r`
    have hsplit : ∑ r ∈ range (j + 1), d r * g ^ r
        = d 0 + g * ∑ r ∈ range j, d (r + 1) * g ^ r := by
      rw [sum_range_succ', mul_sum, pow_zero, mul_one, add_comm]
      congr 1
      refine sum_congr rfl fun r _ => ?_
      rw [pow_succ]; ring
    have hd0 : d 0 < g := hd 0 (by omega)
    rw [hsplit]
    rcases i with _ | i
    · -- reducing modulo `g` gives `d_0`
      rw [pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd0]
    · -- subtract `d_0` and divide by `g`
      rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hg0,
        Nat.div_eq_of_lt hd0, zero_add]
      exact ih (fun r => d (r + 1)) (fun r hr => hd (r + 1) (by omega)) i (by omega)

/-- Auxiliary for [HFF 2].  `n mod g^i = ∑_{r<i} (⌊n/g^r⌋ mod g) g^r`. -/
private theorem mod_pow_eq_sum (n : ℕ) :
    ∀ i : ℕ, n % g ^ i = ∑ r ∈ range i, n / g ^ r % g * g ^ r := by
  intro i
  induction i with
  | zero => simp [Nat.mod_one]
  | succ i ih => rw [Nat.mod_pow_succ, ih, sum_range_succ, mul_comm (g ^ i)]

/-- **[HFF 2] Lemma (Digits).**  The map `(n₀,…,n_{j-1}) ↦ ∑ nᵢ gⁱ` is a bijection from
`{0,…,g-1}^j` onto `{0,…,g^j-1}`: it maps into `[0, g^j)`, it is injective on digit tuples, and
every `n < g^j` is in its image.  (Tuples are functions `ℕ → ℕ` read on the indices `< j`.) -/
theorem digits_bijection (hg : 2 ≤ g) (j : ℕ) :
    (∀ d : ℕ → ℕ, (∀ i < j, d i < g) → ∑ i ∈ range j, d i * g ^ i < g ^ j) ∧
    (∀ d d' : ℕ → ℕ, (∀ i < j, d i < g) → (∀ i < j, d' i < g) →
      ∑ i ∈ range j, d i * g ^ i = ∑ i ∈ range j, d' i * g ^ i → ∀ i < j, d i = d' i) ∧
    (∀ n < g ^ j, ∃ d : ℕ → ℕ, (∀ i < j, d i < g) ∧ ∑ i ∈ range j, d i * g ^ i = n) := by
  refine ⟨digits_sum_lt j, ?_, ?_⟩
  · -- injectivity: the digits of the common value are both `dᵢ` and `d'ᵢ`
    intro d d' hd hd' heq i hi
    rw [← digits_sum_digit hg j d hd i hi, heq, digits_sum_digit hg j d' hd' i hi]
  · -- surjectivity: take `dᵢ = ⌊n/gⁱ⌋ mod g`
    intro n hn
    refine ⟨fun i => n / g ^ i % g, fun i _ => Nat.mod_lt _ (by omega), ?_⟩
    rw [← mod_pow_eq_sum n j, Nat.mod_eq_of_lt hn]

/-- **[HFF 3] Definition (Digits and reversal).**  The `i`-th digit of `n` in base `g`,
`nᵢ = ⌊n / gⁱ⌋ mod g`.  For `n < g^j` these are the digits of `n` in the sense of Lemma 2
(see `digit_window`). -/
def digit (g n i : ℕ) : ℕ := n / g ^ i % g

/-- **[HFF 3] Definition (Digits and reversal).**  `rev_j(n) = ∑_{i<j} nᵢ g^{j-1-i}`. -/
def rev (g j n : ℕ) : ℕ := ∑ i ∈ range j, digit g n i * g ^ (j - 1 - i)

/-- **[HFF 4] Lemma (Blocks of digits).**  `n mod gⁱ = ∑_{r<i} n_r g^r` and
`⌊n/gⁱ⌋ mod g^{i'-i} = ∑_{i≤r<i'} n_r g^{r-i}`; moreover, for a digit tuple `d` of length `j`,
the digits of `∑_{r<j} d_r g^r` are the `d_r`. -/
theorem digit_window (hg : 2 ≤ g) :
    (∀ n i : ℕ, n % g ^ i = ∑ r ∈ range i, digit g n r * g ^ r) ∧
    (∀ n i i' : ℕ, i ≤ i' → n / g ^ i % g ^ (i' - i) = ∑ r ∈ Ico i i', digit g n r * g ^ (r - i)) ∧
    (∀ (j : ℕ) (d : ℕ → ℕ), (∀ i < j, d i < g) →
      ∀ i < j, digit g (∑ r ∈ range j, d r * g ^ r) i = d i) := by
  refine ⟨fun n i => mod_pow_eq_sum n i, ?_, fun j d hd i hi => digits_sum_digit hg j d hd i hi⟩
  -- `⌊n/gⁱ⌋ mod g^{i'-i}` is the low part of `⌊n/gⁱ⌋`, whose digits are `n_{i+r}`
  intro n i i' _
  rw [mod_pow_eq_sum (n / g ^ i) (i' - i), sum_Ico_eq_sum_range]
  refine sum_congr rfl fun r _ => ?_
  rw [digit, Nat.div_div_eq_div_mul, ← pow_add, Nat.add_sub_cancel_left]

/-- **[HFF 5] Lemma (Reversal is an involution).**  `rev_j` maps `[0, g^j)` into itself, the
digits of `rev_j(n)` are those of `n` in reverse order, and `rev_j(rev_j(n)) = n`. -/
theorem rev_involution (hg : 2 ≤ g) (j : ℕ) :
    (∀ n, rev g j n < g ^ j) ∧
    (∀ n i, i < j → digit g (rev g j n) i = digit g n (j - 1 - i)) ∧
    (∀ n < g ^ j, rev g j (rev g j n) = n) := by
  -- `rev_j(n) = ∑_{i<j} n_{j-1-i} gⁱ`
  have hrefl : ∀ n, rev g j n = ∑ i ∈ range j, digit g n (j - 1 - i) * g ^ i := fun n => by
    rw [rev, ← sum_range_reflect]
    refine sum_congr rfl fun i hi => ?_
    have : j - 1 - (j - 1 - i) = i := by have := mem_range.mp hi; omega
    rw [this]
  have hdig : ∀ n, ∀ i < j, digit g n (j - 1 - i) < g := fun n i _ => Nat.mod_lt _ (by omega)
  -- so by Lemma 2 it lies in `[0, g^j)` and has digits `n_{j-1-i}`
  have hlt : ∀ n, rev g j n < g ^ j := fun n => by
    rw [hrefl]; exact digits_sum_lt j _ (hdig n)
  have hrd : ∀ n i, i < j → digit g (rev g j n) i = digit g n (j - 1 - i) := fun n i hi => by
    rw [hrefl]; exact digits_sum_digit hg j _ (hdig n) i hi
  refine ⟨hlt, hrd, ?_⟩
  -- reversing twice restores the digits of `n`
  intro n hn
  calc rev g j (rev g j n) = ∑ i ∈ range j, digit g n i * g ^ i := by
        rw [hrefl]
        refine sum_congr rfl fun i hi => ?_
        have hi' := mem_range.mp hi
        rw [hrd n (j - 1 - i) (by omega), show j - 1 - (j - 1 - i) = i by omega]
    _ = n % g ^ j := (mod_pow_eq_sum n j).symm
    _ = n := Nat.mod_eq_of_lt hn

/-- **[HFF 6] Lemma (Geometric sums).**  `|∑_{z<n} e(zθ)| ≤ min(n, 1/(2‖θ‖))`. -/
theorem geom_sum_le (KR : KnownResults) (θ : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ‖∑ z ∈ range n, e (z * θ)‖ ≤ minDiv n 1 (2 * distZ θ) := by
  -- each term has modulus `1`
  have htriv : ‖∑ z ∈ range n, e (z * θ)‖ ≤ n := by
    calc ‖∑ z ∈ range n, e (z * θ)‖ ≤ ∑ z ∈ range n, ‖e (z * θ)‖ := norm_sum_le _ _
      _ = n := by simp [norm_e]
  rcases eq_or_lt_of_le (distZ_nonneg θ) with h0 | hpos
  · rw [← h0, mul_zero, minDiv_zero]; exact htriv
  have h2 : (2 * distZ θ) ≠ 0 := by positivity
  rw [minDiv_of_ne h2]
  refine le_min htriv ?_
  -- if `θ ∉ ℤ`, the sum is `(e(nθ) - 1)/(e(θ) - 1)`
  have hne : e θ ≠ 1 := by
    intro h
    obtain ⟨m, hm⟩ := (e_eq_one_iff θ).mp h
    exact (distZ_pos_iff θ).mp hpos m hm
  have hsum : ∑ z ∈ range n, e (z * θ) = (e θ ^ n - 1) / (e θ - 1) := by
    rw [← geom_sum_eq hne n]
    exact sum_congr rfl fun z _ => e_nat_mul z θ
  have hnum : ‖e θ ^ n - 1‖ ≤ 2 := by
    calc ‖e θ ^ n - 1‖ ≤ ‖e θ ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_e, one_pow, norm_one]; norm_num
  -- `|e(θ) - 1| = 2|sin πθ| ≥ 4‖θ‖`
  have hden : 4 * distZ θ ≤ ‖e θ - 1‖ := by
    rw [KR.norm_e_sub_one θ]
    have := KR.sin_pi_ge θ
    linarith
  have hden0 : 0 < ‖e θ - 1‖ := by linarith
  rw [hsum, norm_div, div_le_div_iff₀ hden0 (by positivity)]
  nlinarith

/-- **[HFF 7] Lemma (Harmonic numbers).**  `∑_{j=1}^n 1/j ≤ 1 + log n`. -/
theorem harmonic_le (KR : KnownResults) (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Icc 1 n, (1 : ℝ) / j ≤ 1 + Real.log n := by
  have h := harmonic_le_one_add_log n
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h

/-- Auxiliary for [HFF 8].  `1/(2m+3) ≤ (log(2m+3) - log(2m+1))/2`, from `log y ≤ y - 1`
with `y = (2m+1)/(2m+3)`. -/
private theorem odd_recip_le_log (m : ℕ) :
    (1 : ℝ) / (2 * m + 3) ≤ (Real.log (2 * m + 3) - Real.log (2 * m + 1)) / 2 := by
  have h1 : (0 : ℝ) < 2 * m + 1 := by positivity
  have h3 : (0 : ℝ) < 2 * m + 3 := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos h1 h3)
  rw [Real.log_div h1.ne' h3.ne'] at hlog
  have : (2 * m + 1 : ℝ) / (2 * m + 3) - 1 = -(2 / (2 * m + 3)) := by
    field_simp; ring
  rw [this] at hlog
  have : (1 : ℝ) / (2 * m + 3) = (2 / (2 * m + 3)) / 2 := by ring
  rw [this]
  linarith

/-- Auxiliary for [HFF 8].  `∑_{j=1}^{m+1} 1/(2j-1) ≤ 1 + log(2m+1)/2` (telescoping). -/
private theorem odd_harmonic_aux (m : ℕ) :
    ∑ n ∈ range (m + 1), (1 : ℝ) / (2 * n + 1) ≤ 1 + Real.log (2 * m + 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have := odd_recip_le_log m
    push_cast
    have e1 : (2 * ((m : ℝ) + 1) + 1) = 2 * m + 3 := by ring
    rw [e1]
    linarith

/-- **[HFF 8] Lemma (An odd harmonic sum).**  `∑_{0<|j|≤R/2} 1/(2|j|-1) ≤ 2 + log R`. -/
theorem odd_harmonic_le (KR : KnownResults) (R : ℕ) (hR : 1 ≤ R) :
    ∑ j ∈ (Icc (-(R : ℤ)) R).filter (fun j : ℤ => j ≠ 0 ∧ 2 * |j| ≤ R),
      (1 : ℝ) / (2 * |(j : ℝ)| - 1) ≤ 2 + Real.log R := by
  -- the index set is `{±1, …, ±⌊R/2⌋}`
  have hS : (Icc (-(R : ℤ)) R).filter (fun j : ℤ => j ≠ 0 ∧ 2 * |j| ≤ R)
      = (range (R / 2)).image (fun n : ℕ => (n : ℤ) + 1) ∪
        (range (R / 2)).image (fun n : ℕ => -((n : ℤ) + 1)) := by
    ext j
    simp only [mem_filter, mem_Icc, mem_union, mem_image, mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      rcases le_or_gt 0 j with hj | hj
      · rw [abs_of_nonneg hj] at h4
        exact Or.inl ⟨(j - 1).toNat, by omega, by omega⟩
      · rw [abs_of_neg hj] at h4
        exact Or.inr ⟨(-j - 1).toNat, by omega, by omega⟩
    · rintro (⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩)
      · rw [abs_of_pos (show (0 : ℤ) < (n : ℤ) + 1 by positivity)]
        omega
      · rw [abs_neg, abs_of_pos (show (0 : ℤ) < (n : ℤ) + 1 by positivity)]
        omega
  have hdisj : Disjoint ((range (R / 2)).image (fun n : ℕ => (n : ℤ) + 1))
      ((range (R / 2)).image (fun n : ℕ => -((n : ℤ) + 1))) := by
    rw [disjoint_left]
    simp only [mem_image, mem_range]
    rintro _ ⟨a, _, rfl⟩ ⟨b, _, h⟩
    omega
  -- so the sum is `2 ∑_{1 ≤ j ≤ R/2} 1/(2j-1) = 2 ∑_{n<⌊R/2⌋} 1/(2n+1)`
  have hsum : ∑ j ∈ (Icc (-(R : ℤ)) R).filter (fun j : ℤ => j ≠ 0 ∧ 2 * |j| ≤ R),
      (1 : ℝ) / (2 * |(j : ℝ)| - 1) = 2 * ∑ n ∈ range (R / 2), (1 : ℝ) / (2 * n + 1) := by
    rw [hS, sum_union hdisj, sum_image (fun a _ b _ h => by simpa using h),
      sum_image (fun a _ b _ h => by simpa using h), two_mul]
    congr 1 <;> refine sum_congr rfl fun n _ => ?_ <;>
      simp only [Int.cast_add, Int.cast_neg, Int.cast_natCast, Int.cast_one, abs_neg] <;>
      rw [abs_of_pos (show (0 : ℝ) < (n : ℝ) + 1 by positivity)] <;> congr 1 <;> ring
  rw [hsum]
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg (by exact_mod_cast hR)
  cases hm : R / 2 with
  | zero => simp; linarith
  | succ m =>
    -- for `R ≥ 2`: `2 ∑ ≤ 2 + log(2m+1) ≤ 2 + log R`, where `m + 1 = ⌊R/2⌋`
    have h1 := odd_harmonic_aux m
    have h2 : (2 * m + 1 : ℝ) ≤ R := by
      have : 2 * m + 1 ≤ R := by omega
      exact_mod_cast this
    have h3 : Real.log (2 * m + 1) ≤ Real.log R := Real.log_le_log (by positivity) h2
    linarith

end PalindromicPowers

import PalindromicPowers.Conventions

/-!
# Basic API for the notation of Block 1

Elementary facts about `e`, `distZ` (= `‖·‖`) and `minDiv` that follow directly from the
definitions.  They are not HFF blocks (the HFF uses them silently), and they are not among the
prerequisites of `KnownResults`.
-/

namespace PalindromicPowers

open Real

/-! ### The additive character `e` -/

theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem e_zero : e 0 = 1 := by simp [e]

theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  rw [show (2 * (π : ℂ) * Complex.I * (x : ℂ)) = ((2 * π * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem e_ne_zero (x : ℝ) : e x ≠ 0 := by
  intro h; have := norm_e x; rw [h, norm_zero] at this; exact zero_ne_one this

theorem e_int (n : ℤ) : e n = 1 := by
  unfold e
  rw [Complex.exp_eq_one_iff]
  exact ⟨n, by push_cast; ring⟩

theorem e_add_int (x : ℝ) (n : ℤ) : e (x + n) = e x := by
  rw [e_add, e_int, mul_one]

theorem e_neg (x : ℝ) : e (-x) = (e x)⁻¹ := by
  have h := e_add (-x) x
  rw [neg_add_cancel, e_zero] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem e_sub (x y : ℝ) : e (x - y) = e x * (e y)⁻¹ := by
  rw [sub_eq_add_neg, e_add, e_neg]

theorem e_nat_mul (n : ℕ) (x : ℝ) : e (n * x) = e x ^ n := by
  induction n with
  | zero => simp [e_zero]
  | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, e_add, ih, pow_succ]

theorem e_int_mul (n : ℤ) (x : ℝ) : e (n * x) = e x ^ n := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · simp [e_nat_mul]
  · rw [Int.cast_neg, neg_mul, e_neg, Int.cast_natCast, e_nat_mul, zpow_neg, zpow_natCast]

theorem e_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) : e (∑ i ∈ s, f i) = ∏ i ∈ s, e (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [e_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, e_add, ih]

theorem e_eq_one_iff (x : ℝ) : e x = 1 ↔ ∃ n : ℤ, x = n := by
  unfold e
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h2 : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : (x : ℂ) = n := by
      apply mul_left_cancel₀ h2; rw [hn]; ring
    exact_mod_cast this
  · rintro ⟨n, rfl⟩; exact ⟨n, by push_cast; ring⟩

theorem e_conj (x : ℝ) : (starRingEnd ℂ) (e x) = e (-x) := by
  unfold e
  rw [← Complex.exp_conj]; congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]; push_cast; ring

/-! ### The distance to the nearest integer -/

theorem distZ_nonneg (x : ℝ) : 0 ≤ distZ x := abs_nonneg _

theorem distZ_le_half (x : ℝ) : distZ x ≤ 1 / 2 := abs_sub_round x

theorem distZ_le_abs_sub (x : ℝ) (n : ℤ) : distZ x ≤ |x - n| := round_le x n

theorem distZ_le_abs (x : ℝ) : distZ x ≤ |x| := by
  simpa using distZ_le_abs_sub x 0

theorem distZ_add_int (x : ℝ) (n : ℤ) : distZ (x + n) = distZ x := by
  unfold distZ
  rw [round_add_intCast]; push_cast; ring_nf

theorem distZ_sub_int (x : ℝ) (n : ℤ) : distZ (x - n) = distZ x := by
  rw [sub_eq_add_neg, ← Int.cast_neg, distZ_add_int]

theorem distZ_int (n : ℤ) : distZ n = 0 := by
  unfold distZ; simp [round_intCast]

theorem distZ_neg (x : ℝ) : distZ (-x) = distZ x := by
  apply le_antisymm
  · calc distZ (-x) ≤ |-x - ((-round x : ℤ) : ℝ)| := distZ_le_abs_sub _ _
      _ = distZ x := by unfold distZ; push_cast; rw [← abs_neg]; ring_nf
  · calc distZ x ≤ |x - ((-round (-x) : ℤ) : ℝ)| := distZ_le_abs_sub _ _
      _ = distZ (-x) := by unfold distZ; push_cast; rw [← abs_neg]; ring_nf

/-- `‖x‖ = min_n |x - n|`, attained at `round x`. -/
theorem distZ_eq_abs_sub_iff (x : ℝ) (n : ℤ) (h : ∀ m : ℤ, |x - n| ≤ |x - m|) :
    distZ x = |x - n| :=
  le_antisymm (distZ_le_abs_sub x n) (h _)

theorem distZ_eq_abs_of_abs_le_half {x : ℝ} (hx : |x| ≤ 1 / 2) : distZ x = |x| := by
  apply le_antisymm (distZ_le_abs x)
  unfold distZ
  rcases eq_or_ne (round x) 0 with h | h
  · simp [h]
  · have h1 : (1 : ℝ) ≤ |(round x : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h
    have h2 : |(round x : ℝ)| ≤ |x| + |x - round x| := by
      calc |(round x : ℝ)| = |x - (x - round x)| := by ring_nf
        _ ≤ |x| + |x - round x| := abs_sub _ _
    linarith

theorem distZ_eq_abs_sub_of_mem {x : ℝ} (n : ℤ) (h1 : (n : ℝ) - 1 / 2 < x) (h2 : x ≤ n + 1 / 2) :
    distZ x = |x - n| := by
  rw [← distZ_sub_int x n]
  apply distZ_eq_abs_of_abs_le_half
  rw [abs_le]; constructor <;> linarith

theorem distZ_eq_zero_iff (x : ℝ) : distZ x = 0 ↔ ∃ n : ℤ, x = n := by
  constructor
  · intro h
    refine ⟨round x, ?_⟩
    have := abs_eq_zero.mp h
    linarith
  · rintro ⟨n, rfl⟩; exact distZ_int n

theorem distZ_pos_iff (x : ℝ) : 0 < distZ x ↔ ∀ n : ℤ, x ≠ n := by
  rw [lt_iff_le_and_ne, ne_comm, Ne, distZ_eq_zero_iff]
  simp [distZ_nonneg]

/-! ### `minDiv A H y = min(A, H/y)` with `H/0 = ∞` -/

theorem minDiv_le_left (A H y : ℝ) : minDiv A H y ≤ A := by
  unfold minDiv; split_ifs <;> simp

theorem minDiv_le_div {A H y : ℝ} (hy : y ≠ 0) : minDiv A H y ≤ H / y := by
  unfold minDiv; simp only [hy, ite_false]; exact min_le_right _ _

theorem minDiv_zero (A H : ℝ) : minDiv A H 0 = A := by simp [minDiv]

theorem minDiv_of_ne {A H y : ℝ} (hy : y ≠ 0) : minDiv A H y = min A (H / y) := by
  simp [minDiv, hy]

theorem minDiv_nonneg {A H y : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H) (hy : 0 ≤ y) : 0 ≤ minDiv A H y := by
  unfold minDiv; split_ifs
  · exact hA
  · exact le_min hA (div_nonneg hH hy)

theorem minDiv_mono_left {A A' H y : ℝ} (h : A ≤ A') : minDiv A H y ≤ minDiv A' H y := by
  unfold minDiv; split_ifs
  · exact h
  · exact min_le_min_right _ h

/-- `minDiv` is non-increasing in `y ≥ 0` (for `H ≥ 0`). -/
theorem minDiv_anti {A H y y' : ℝ} (hH : 0 ≤ H) (hy : 0 ≤ y) (hyy' : y ≤ y') :
    minDiv A H y' ≤ minDiv A H y := by
  rcases eq_or_lt_of_le hy with h | h
  · rw [← h, minDiv_zero]; exact minDiv_le_left _ _ _
  · have hy' : y' ≠ 0 := (lt_of_lt_of_le h hyy').ne'
    rw [minDiv_of_ne hy', minDiv_of_ne h.ne']
    exact min_le_min_left _ (div_le_div_of_nonneg_left hH h hyy')

theorem mul_minDiv {c : ℝ} (hc : 0 ≤ c) (A H y : ℝ) : c * minDiv A H y = minDiv (c * A) (c * H) y := by
  unfold minDiv; split_ifs
  · rfl
  · rw [mul_min_of_nonneg _ _ hc, mul_div_assoc]

/-- `minDiv A H y ≤ minDiv A H' y'` when `H/y ≤ H'/y'` (both `y, y' > 0`). -/
theorem minDiv_le_minDiv_of_div_le {A H H' y y' : ℝ} (hy : y ≠ 0) (hy' : y' ≠ 0)
    (h : H / y ≤ H' / y') : minDiv A H y ≤ minDiv A H' y' := by
  rw [minDiv_of_ne hy, minDiv_of_ne hy']; exact min_le_min_left _ h

theorem minDiv_scale {A H y c : ℝ} (hc : 0 < c) : minDiv A (c * H) (c * y) = minDiv A H y := by
  unfold minDiv
  by_cases hy : y = 0
  · simp [hy]
  · simp only [mul_ne_zero hc.ne' hy, hy, ite_false, mul_div_mul_left _ _ hc.ne']

end PalindromicPowers

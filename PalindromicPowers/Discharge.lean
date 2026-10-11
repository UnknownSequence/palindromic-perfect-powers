import PalindromicPowers.Assumptions

/-!
# Discharging `KnownResults` from Mathlib

Each analytic prerequisite of the HFF document (the fields of `KnownResults`, see
`Assumptions.lean` and `assumptions.md`) is proved here from Mathlib.  Combined with
`main_theorem`, this gives the unconditional `main_theorem_unconditional` in
`MainTheorem.lean`.
-/

namespace PalindromicPowers

open Real

/-- Auxiliary for KnownResults.taylor2.  (Proof by Rolle's theorem applied to
`φ(x) = f b - f x - f'(x)(b - x) - K(b - x)²/2`, with `K` chosen so that `φ a = 0`.) -/
private theorem taylor2_aux (f : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hf : ContDiff ℝ 2 f) :
    ∃ c ∈ Set.Ioo a b, f b = f a + deriv f a * (b - a) + deriv (deriv f) c * (b - a) ^ 2 / 2 := by
  have h1 : Differentiable ℝ f := hf.differentiable two_ne_zero
  have h2 : ContDiff ℝ 1 (deriv f) := by
    have hf' : ContDiff ℝ (1 + 1) f := by simpa [one_add_one_eq_two] using hf
    exact ((contDiff_succ_iff_deriv).1 hf').2.2
  have h3 : Differentiable ℝ (deriv f) := h2.differentiable one_ne_zero
  have hba : b - a ≠ 0 := sub_ne_zero.2 hab.ne'
  set K : ℝ := (f b - f a - deriv f a * (b - a)) * 2 / (b - a) ^ 2 with hK
  set φ : ℝ → ℝ := fun x => f b - f x - deriv f x * (b - x) - K * (b - x) ^ 2 / 2 with hφ
  have hder : ∀ x, HasDerivAt φ ((b - x) * (K - deriv (deriv f) x)) x := by
    intro x
    have hA := (h1 x).hasDerivAt
    have hB := (h3 x).hasDerivAt
    have hC : HasDerivAt (fun y : ℝ => b - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub b
    have := (((hasDerivAt_const x (f b)).sub hA).sub (hB.mul hC)).sub
      (((hC.pow 2).const_mul K).div_const 2)
    convert this using 1
    simp only [Nat.cast_ofNat]
    ring
  have hcont : ContinuousOn φ (Set.Icc a b) :=
    fun x _ => (hder x).continuousAt.continuousWithinAt
  have hφa : φ a = φ b := by
    simp only [hφ, hK, sub_self]
    field_simp
    ring
  obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hab hcont hφa (fun x _ => hder x)
  refine ⟨c, hc, ?_⟩
  have hbc : b - c ≠ 0 := sub_ne_zero.2 hc.2.ne'
  have hKc : K = deriv (deriv f) c := by
    have := (mul_eq_zero.1 hc0).resolve_left hbc
    linarith
  rw [← hKc, hK]
  field_simp
  ring

/-- All the analytic prerequisites of the HFF document hold (proved from Mathlib). -/
theorem knownResults_ofMathlib : KnownResults where
  mvt := fun f a b hab hfc hfd => exists_deriv_eq_slope f hab hfc hfd
  taylor2 := taylor2_aux
  max_attained := by
    intro f a b hab hf
    obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hab) hf
    exact ⟨c, hc, fun x hx => hmax hx⟩
  integral_inv := by
    intro x hx
    rw [integral_inv_of_pos one_pos (by linarith), div_one]
  norm_e_sub_one := by
    intro y
    have h := Complex.norm_exp_I_mul_ofReal_sub_one (2 * π * y)
    have he : e y = Complex.exp (Complex.I * ((2 * π * y : ℝ) : ℂ)) := by
      unfold e; congr 1; push_cast; ring
    rw [he, h, Real.norm_eq_abs, abs_mul, abs_two, show 2 * π * y / 2 = π * y by ring]
  sin_pi_ge := by
    intro y
    set z : ℝ := y - round y with hz
    have hzle : |z| ≤ 1 / 2 := abs_sub_round y
    have hdist : distZ y = |z| := rfl
    have hsin : |Real.sin (π * y)| = |Real.sin (π * z)| := by
      have : π * y = π * z + (round y : ℤ) * π := by rw [hz]; ring
      rw [this, Real.sin_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
    have hz2 := abs_le.1 hzle
    have habs : |Real.sin (π * z)| = Real.sin (π * |z|) := by
      have h1 : |Real.sin (π * z)| = |Real.sin (π * |z|)| := by
        rcases le_total 0 z with h | h
        · rw [abs_of_nonneg h]
        · rw [abs_of_nonpos h, mul_neg, Real.sin_neg, abs_neg]
      rw [h1]
      exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
        (by nlinarith [Real.pi_pos, abs_nonneg z]))
    rw [hsin, habs, hdist]
    have hJ := Real.mul_le_sin (x := π * |z|) (by positivity) (by nlinarith [Real.pi_pos])
    have : 2 / π * (π * |z|) = 2 * |z| := by field_simp
    linarith
  abs_sin_le := fun y => Real.abs_sin_le_abs
  jordan := by
    intro y hy0 hy
    have := Real.mul_le_sin hy0 hy
    calc 2 * y / π = 2 / π * y := by ring
      _ ≤ Real.sin y := this
  distZ_sub_le := by
    intro x y
    calc distZ (x - y) ≤ |x - y - ((round x - round y : ℤ) : ℝ)| := distZ_le_abs_sub _ _
      _ = |(x - round x) - (y - round y)| := by push_cast; ring_nf
      _ ≤ |x - round x| + |y - round y| := abs_sub _ _
      _ = distZ x + distZ y := rfl
  distZ_zmul_le := by
    intro n x
    calc distZ (n * x) ≤ |n * x - ((n * round x : ℤ) : ℝ)| := distZ_le_abs_sub _ _
      _ = |(n : ℝ)| * |x - round x| := by push_cast; rw [← abs_mul]; ring_nf
      _ = |(n : ℝ)| * distZ x := rfl

end PalindromicPowers

import PalindromicPowers.Basic

/-!
# Assumptions: published hypotheses and known results

This file is the trust boundary of the formalization.  See `assumptions.md` for
the full discussion.

**Published hypotheses.**  None.  The HFF document imports no theorem from the
literature: the papers [CLS], [Col], [TP], [DMRSS], [BhS] and [Pal] are cited
only for context and comparison, and no computer calculation is used.

**Known results.**  The *Prerequisites* paragraph of the HFF document lists the
textbook facts the proof takes as known.  The algebraic ones (division with
remainder, congruences, greatest common divisors, `p`-adic valuations, the
Chinese remainder theorem and the binomial theorem) are part of Lean core and
Mathlib and are used directly.  The analytic ones are the fields of the
structure `KnownResults` below, each stated in the form in which the HFF uses
it.  Every lemma whose HFF proof relies on one of them (directly or through a
cited block) takes an explicit hypothesis `KR : KnownResults`, and the main
theorem does too.  There is no `axiom` and no global instance: the statements
are honest implications.

`PalindromicPowers/Discharge.lean` proves `KnownResults` from Mathlib, which
turns the main theorem into an unconditional statement.
-/

namespace PalindromicPowers

open Real

/-- The analytic prerequisites of the HFF document (paragraph *Prerequisites*),
one field per fact, in the form the proof uses them. -/
structure KnownResults : Prop where
  /-- The mean value theorem. -/
  mvt : ∀ (f : ℝ → ℝ) (a b : ℝ), a < b → ContinuousOn f (Set.Icc a b) →
    DifferentiableOn ℝ f (Set.Ioo a b) → ∃ c ∈ Set.Ioo a b, deriv f c = (f b - f a) / (b - a)
  /-- Taylor's theorem with the Lagrange remainder, to second order, for `C²` functions. -/
  taylor2 : ∀ (f : ℝ → ℝ) (a b : ℝ), a < b → ContDiff ℝ 2 f →
    ∃ c ∈ Set.Ioo a b, f b = f a + deriv f a * (b - a) + deriv (deriv f) c * (b - a) ^ 2 / 2
  /-- A continuous function on a compact interval attains its maximum. -/
  max_attained : ∀ (f : ℝ → ℝ) (a b : ℝ), a ≤ b → ContinuousOn f (Set.Icc a b) →
    ∃ c ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f x ≤ f c
  /-- `∫₁ˣ dy/y = log x`. -/
  integral_inv : ∀ x : ℝ, 1 ≤ x → ∫ y in (1 : ℝ)..x, y⁻¹ = Real.log x
  /-- `|e(y) - 1| = 2|sin πy|`. -/
  norm_e_sub_one : ∀ y : ℝ, ‖e y - 1‖ = 2 * |Real.sin (π * y)|
  /-- `|sin πy| ≥ 2‖y‖`. -/
  sin_pi_ge : ∀ y : ℝ, 2 * distZ y ≤ |Real.sin (π * y)|
  /-- `|sin y| ≤ |y|`. -/
  abs_sin_le : ∀ y : ℝ, |Real.sin y| ≤ |y|
  /-- `sin y ≥ 2y/π` for `0 ≤ y ≤ π/2` (Jordan's inequality). -/
  jordan : ∀ y : ℝ, 0 ≤ y → y ≤ π / 2 → 2 * y / π ≤ Real.sin y
  /-- `‖x - y‖ ≤ ‖x‖ + ‖y‖` for the distance to the nearest integer. -/
  distZ_sub_le : ∀ x y : ℝ, distZ (x - y) ≤ distZ x + distZ y
  /-- `‖nx‖ ≤ |n| ‖x‖` for `n ∈ ℤ`. -/
  distZ_zmul_le : ∀ (n : ℤ) (x : ℝ), distZ (n * x) ≤ |(n : ℝ)| * distZ x

end PalindromicPowers

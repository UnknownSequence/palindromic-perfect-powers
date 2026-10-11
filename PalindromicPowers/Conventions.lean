import Mathlib

/-!
# HFF block 1: Conventions

Every Lean declaration that formalizes a block of the HFF document
`palindromic_powers_hff.tex` carries a docstring beginning with `[HFF n]`,
where `n` is the block number.  Auxiliary lemmas used only inside the proof of
a block say so in their docstring.

Lean-friendly conventions (see `hff/LEAN_CONVENTIONS.md`):

* `e x = exp(2πix)` and `distZ x = ‖x‖`, the distance to the nearest integer.
* The convention `H/0 = ∞` of the HFF is implemented by `minDiv A H y`, which is
  `min(A, H / y)` for `y ≠ 0` and `A` for `y = 0`.
* `A ≪ B` and "for `L` large" are written out: `∃ C₁ L₀, ∀ L ≥ L₀, A ≤ C₁ * B`.
* `g ≥ 2` and `k ≥ 2` are explicit hypotheses `hg : 2 ≤ g`, `hk : 2 ≤ k`.
-/

namespace PalindromicPowers

open Real

/-- **[HFF 1]** `e(x) = exp(2πix)`. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)

/-- **[HFF 1]** `‖x‖`, the distance from `x` to the nearest integer. -/
noncomputable def distZ (x : ℝ) : ℝ := |x - round x|

/-- **[HFF 1]** `min(A, H/y)` with the convention `H/0 = ∞`: the value is `A` when `y = 0`. -/
noncomputable def minDiv (A H y : ℝ) : ℝ := if y = 0 then A else min A (H / y)

end PalindromicPowers

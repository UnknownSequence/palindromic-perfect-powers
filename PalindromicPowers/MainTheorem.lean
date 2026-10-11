import PalindromicPowers.Final
import PalindromicPowers.Discharge

/-!
# The main theorem, unconditionally and in Mathlib's language

* `main_theorem_unconditional`: HFF Theorem 101 with the hypothesis `KnownResults` discharged
  by `knownResults_ofMathlib` (`Discharge.lean`).
* `main_theorem_digits`: the same statement with the palindromes described by Mathlib's
  `Nat.digits` instead of the project's `palSet`/`digit`, so that the statement can be read
  without any definition from this project.
-/

namespace PalindromicPowers

open Finset

variable {g k : ℕ}

/-- **[HFF 101]** Theorem 101, unconditionally. -/
theorem main_theorem_unconditional (hg : 2 ≤ g) (hk : 2 ≤ k) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ ∃ C' : ℝ, ∀ L : ℕ, 1 ≤ L →
      (((palSet g L).filter (fun n => ∃ x ≤ n, x ^ k = n)).card : ℝ) ≤
        C' * ((palSet g L).card : ℝ) ^ (γ / k) :=
  main_theorem knownResults_ofMathlib hg hk

/-- `𝒫_L` (Definition 28) described with Mathlib's `Nat.digits` (least significant digit first):
the `n < g^L` with exactly `L` digits whose digit list is a palindrome. -/
theorem palSet_eq_digits (hg : 2 ≤ g) {L : ℕ} (hL : 1 ≤ L) :
    palSet g L = (range (g ^ L)).filter
      (fun n => (Nat.digits g n).length = L ∧ (Nat.digits g n).reverse = Nat.digits g n) := by
  have hg1 : 1 < g := by omega
  -- the `i`-th entry of `Nat.digits g n` is `digit g n i`
  have hget : ∀ n i (h : i < (Nat.digits g n).length), (Nat.digits g n)[i] = digit g n i := by
    intro n i h
    rw [digit, ← Nat.getD_digits n i hg, List.getD_eq_getElem _ _ h]
  -- `n` has exactly `L` digits iff `g^(L-1) ≤ n < g^L`
  have hlen : ∀ n, n < g ^ L → ((Nat.digits g n).length = L ↔ g ^ (L - 1) ≤ n) := by
    intro n hn
    constructor
    · intro h
      have hn0 : n ≠ 0 := by
        rintro rfl; simp at h; omega
      rw [Nat.length_digits g n hg1 hn0] at h
      have : Nat.log g n = L - 1 := by omega
      rw [← this]; exact Nat.pow_log_le_self g hn0
    · intro h
      have hn0 : n ≠ 0 := by
        have : 0 < g ^ (L - 1) := by positivity
        omega
      rw [Nat.length_digits g n hg1 hn0]
      have : Nat.log g n = L - 1 := by
        rw [Nat.log_eq_iff (Or.inr ⟨hg1, hn0⟩)]
        exact ⟨h, by rwa [Nat.sub_add_cancel hL]⟩
      omega
  ext n
  simp only [palSet, mem_filter, mem_Ico, mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, hpal⟩
    have hl : (Nat.digits g n).length = L := (hlen n h2).mpr h1
    refine ⟨h2, hl, ?_⟩
    apply List.ext_getElem (by simp)
    intro i hi1 hi2
    rw [List.getElem_reverse, hget, hget, hl]
    have hi : i < L := by simpa [hl] using hi1
    rw [hpal i hi]
  · rintro ⟨h2, hl, hrev⟩
    refine ⟨⟨(hlen n h2).mp hl, h2⟩, fun i hi => ?_⟩
    have hi' : i < (Nat.digits g n).length := by omega
    have key : (Nat.digits g n)[i]? = (Nat.digits g n)[L - 1 - i]? := by
      conv_lhs => rw [← hrev]
      rw [List.getElem?_reverse hi', hl]
    rw [digit, digit, ← Nat.getD_digits n i hg, ← Nat.getD_digits n (L - 1 - i) hg,
      List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, key]

/-- **[HFF 101]** Theorem 101 in Mathlib's language: for all `g ≥ 2`, `k ≥ 2` there are
`0 < γ < 1` and `C'` such that, for every `L ≥ 1`, the number of `L`-digit base-`g`
palindromes (as `Nat.digits` lists) that are perfect `k`-th powers is at most
`C' · (number of L-digit palindromes)^{γ/k}`. -/
theorem main_theorem_digits (hg : 2 ≤ g) (hk : 2 ≤ k) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ ∃ C' : ℝ, ∀ L : ℕ, 1 ≤ L →
      ((((range (g ^ L)).filter (fun n => (Nat.digits g n).length = L ∧
            (Nat.digits g n).reverse = Nat.digits g n)).filter
            (fun n => ∃ x ≤ n, x ^ k = n)).card : ℝ) ≤
        C' * (((range (g ^ L)).filter (fun n => (Nat.digits g n).length = L ∧
            (Nat.digits g n).reverse = Nat.digits g n)).card : ℝ) ^ (γ / k) := by
  obtain ⟨γ, h0, h1, C', h⟩ := main_theorem_unconditional hg hk
  refine ⟨γ, h0, h1, C', fun L hL => ?_⟩
  rw [← palSet_eq_digits hg hL]
  exact h L hL

end PalindromicPowers

import PalindromicPowers.Majorant

/-!
# HFF blocks 56–59: sums over residues
-/

namespace PalindromicPowers

open Finset Real

variable {g k : ℕ}

/-- Auxiliary for [HFF 56].  The sum of an `R`-periodic function over `0 ≤ a < qR` is `q` times
its sum over one period. -/
private lemma sum_range_mul_periodic {R : ℕ} (f : ℕ → ℝ) (hf : ∀ a, f a = f (a % R)) (q : ℕ) :
    ∑ a ∈ range (q * R), f a = q * ∑ a ∈ range R, f a := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, sum_range_add, ih]
    have h : ∀ x, f (q * R + x) = f x := by
      intro x
      rw [hf (q * R + x), hf x, Nat.mul_comm q R, Nat.mul_add_mod]
    simp only [h]
    push_cast
    ring

/-- Auxiliary for [HFF 56].  If `gcd(c, R) = 1`, then `a ↦ ac mod R` permutes `{0, …, R-1}`. -/
private lemma sum_range_mul_mod {R c : ℕ} (hR : 1 ≤ R) (hc : Nat.Coprime c R) (ψ : ℕ → ℝ) :
    ∑ a ∈ range R, ψ (a * c % R) = ∑ a ∈ range R, ψ a := by
  have hinj : Set.InjOn (fun a => a * c % R) (range R : Set ℕ) := by
    intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    have h1 : a * c ≡ b * c [MOD R] := hab
    have h2 : a ≡ b [MOD R] :=
      Nat.ModEq.cancel_right_of_coprime (by rw [Nat.gcd_comm]; exact hc) h1
    rwa [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2
  have himg : (range R).image (fun a => a * c % R) = range R := by
    apply eq_of_subset_of_card_le
    · intro x hx
      simp only [mem_image, mem_range] at hx ⊢
      obtain ⟨a, -, rfl⟩ := hx
      exact Nat.mod_lt _ (by omega)
    · rw [card_image_of_injOn hinj]
  rw [← sum_image (f := ψ) hinj, himg]

/-- **[HFF 56] Lemma (Multiples).**  Let `d = gcd(β, Q)`.  As `a` runs over `0,…,Q-1`,
`aβ mod Q` runs over the multiples `rd`, `0 ≤ r < Q/d`, each exactly `d` times; equivalently,
`∑_{a<Q} φ(aβ mod Q) = d ∑_{r<Q/d} φ(rd)` for every function `φ`. -/
theorem multiples_sum {Q : ℕ} (hQ : 1 ≤ Q) (β : ℤ) (φ : ℤ → ℝ) :
    ∑ a ∈ range Q, φ (((a : ℤ) * β) % (Q : ℤ)) =
      (Int.gcd β Q : ℝ) * ∑ r ∈ range (Q / Int.gcd β Q), φ ((r : ℤ) * (Int.gcd β Q : ℤ)) := by
  -- Replace `β` by its residue `B = β mod Q ∈ [0, Q)`.
  have hQ0 : (0 : ℤ) < Q := by exact_mod_cast hQ
  obtain ⟨B, hB⟩ : ∃ B : ℕ, (B : ℤ) = β % Q :=
    ⟨(β % (Q : ℤ)).toNat, Int.toNat_of_nonneg (Int.emod_nonneg _ hQ0.ne')⟩
  have hgcd : Int.gcd β Q = Nat.gcd B Q := by
    rw [← Int.gcd_emod, ← hB, Int.gcd_natCast_natCast]
  rw [hgcd]
  -- Write `Q = dR` and `B = dB'` with `gcd(B', R) = 1`.
  have hd0 : 0 < Nat.gcd B Q := Nat.gcd_pos_of_pos_right _ (by omega)
  obtain ⟨R, hR⟩ : ∃ R, R = Q / Nat.gcd B Q := ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ B', B' = B / Nat.gcd B Q := ⟨_, rfl⟩
  have hcop : Nat.Coprime B' R := by rw [hB', hR]; exact Nat.coprime_div_gcd_div_gcd hd0
  have hQdR : Q = Nat.gcd B Q * R := by rw [hR, Nat.mul_div_cancel' (Nat.gcd_dvd_right B Q)]
  have hBdB : B = Nat.gcd B Q * B' := by rw [hB', Nat.mul_div_cancel' (Nat.gcd_dvd_left B Q)]
  rw [← hR]
  set d := Nat.gcd B Q with hd
  have hR1 : 1 ≤ R := by
    rcases Nat.eq_zero_or_pos R with h | h
    · rw [h, Nat.mul_zero] at hQdR; omega
    · exact h
  -- Each term: `aβ mod Q = d (aB' mod R)`.
  have hterm : ∀ a : ℕ, ((a : ℤ) * β) % (Q : ℤ) = (((a * B' % R : ℕ) : ℤ) * (d : ℤ)) := by
    intro a
    have h1 : ((a : ℤ) * β) % (Q : ℤ) = ((a * B % Q : ℕ) : ℤ) := by
      push_cast
      rw [hB]
      exact ((Int.mod_modEq β Q).mul_left (a : ℤ)).symm
    rw [h1, hBdB, hQdR, show a * (d * B') = d * (a * B') by ring, Nat.mul_mod_mul_left]
    push_cast
    ring
  simp only [hterm]
  -- Sum over `d` periods, then permute the residues.
  set ψ : ℕ → ℝ := fun r => φ ((r : ℤ) * (d : ℤ)) with hψ
  have hper : ∀ a, ψ (a * B' % R) = ψ (a % R * B' % R) := by
    intro a; rw [Nat.mod_mul_mod]
  conv_lhs => rw [hQdR]
  rw [sum_range_mul_periodic (fun a => ψ (a * B' % R)) hper d, sum_range_mul_mod hR1 hcop ψ]

/-- **[HFF 57] Lemma (Distances).**  For `0 < |j| ≤ R/2` and `|w₀| ≤ 1/2`:
`‖(j + w₀)/R‖ ≥ (2|j|-1)/(2R)`. -/
theorem dist_lower {R : ℕ} (hR : 1 ≤ R) {j : ℤ} (hj0 : j ≠ 0) (hjR : 2 * |j| ≤ R) {w₀ : ℝ}
    (hw : |w₀| ≤ 1 / 2) :
    (2 * |(j : ℝ)| - 1) / (2 * R) ≤ distZ ((j + w₀) / R) := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hjR' : 2 * |(j : ℝ)| ≤ R := by
    rw [← Int.cast_abs]; exact_mod_cast hjR
  set n := round (((j : ℝ) + w₀) / R)
  -- For every integer `n`: `|j + w₀ - nR| ≥ |j| - 1/2`.
  have key : |(j : ℝ)| - 1 / 2 ≤ |(j : ℝ) + w₀ - n * R| := by
    rcases eq_or_ne n 0 with hn | hn
    · -- `n = 0`
      have h := abs_sub_abs_le_abs_sub (j : ℝ) (-w₀)
      rw [abs_neg, sub_neg_eq_add] at h
      rw [hn, Int.cast_zero, zero_mul, sub_zero]
      linarith
    · -- `n ≠ 0`: `|j + w₀ - nR| ≥ R - |j| - 1/2 ≥ |j| - 1/2`
      have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
      have h2 : (R : ℝ) ≤ |(n : ℝ) * R| := by
        rw [abs_mul, abs_of_pos hRpos]; nlinarith
      have h3 : |(n : ℝ) * R| ≤ |(j : ℝ) + w₀ - n * R| + |(j : ℝ)| + |w₀| := by
        calc |(n : ℝ) * R| = |-((j : ℝ) + w₀ - n * R) + j + w₀| := by ring_nf
          _ ≤ |-((j : ℝ) + w₀ - n * R) + j| + |w₀| := abs_add_le _ _
          _ ≤ |-((j : ℝ) + w₀ - n * R)| + |(j : ℝ)| + |w₀| := by
              gcongr; exact abs_add_le _ _
          _ = |(j : ℝ) + w₀ - n * R| + |(j : ℝ)| + |w₀| := by rw [abs_neg]
      linarith
  -- Divide by `R`.
  unfold distZ
  rw [show ((j : ℝ) + w₀) / R - n = ((j : ℝ) + w₀ - n * R) / R by field_simp, abs_div,
    abs_of_pos hRpos, div_le_div_iff₀ (by positivity) hRpos]
  nlinarith

/-- **[HFF 58] Lemma (Sum over residues).**  For `R ≥ 1`, `w ∈ ℝ` and `A ≥ 1`:
`∑_{r<R} min(A, 1/(2‖(w+r)/R‖)) ≤ min(A, R/(2‖w‖)) + R(2 + log R)`. -/
theorem residue_sum (KR : KnownResults) {R : ℕ} (hR : 1 ≤ R) (w : ℝ) {A : ℝ} (hA : 1 ≤ A) :
    ∑ r ∈ range R, minDiv A 1 (2 * distZ ((w + r) / R)) ≤
      minDiv A R (2 * distZ w) + R * (2 + Real.log R) := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hRz : (0 : ℤ) < R := by exact_mod_cast hR
  -- Write `w = n₀ + w₀` with `n₀ = round w` and `|w₀| = ‖w‖ ≤ 1/2`.
  set n₀ : ℤ := round w with hn₀
  set w₀ : ℝ := w - n₀ with hw₀def
  have hw₀ : |w₀| = distZ w := rfl
  have hw₀' : |w₀| ≤ 1 / 2 := distZ_le_half w
  -- `j(r) ≡ n₀ + r (mod R)` with `j(r) ∈ (-R/2, R/2]`.
  set c : ℤ := ((R : ℤ) - 1) / 2 with hc
  set J : ℕ → ℤ := fun r => (n₀ + r + c) % R - c with hJ
  set f : ℤ → ℝ := fun j => minDiv A 1 (2 * distZ ((j + w₀) / R)) with hf
  have hf0 : ∀ j, 0 ≤ f j := fun j =>
    minDiv_nonneg (by linarith) zero_le_one (by have := distZ_nonneg ((j + w₀) / R); linarith)
  -- `‖(w + r)/R‖ = ‖(j(r) + w₀)/R‖`.
  have hterm : ∀ r : ℕ, minDiv A 1 (2 * distZ ((w + r) / R)) = f (J r) := by
    intro r
    have hq := Int.emod_add_mul_ediv (n₀ + r + c) R
    have hq' : (((n₀ + r + c) % R : ℤ) : ℝ) = n₀ + r + c - R * (((n₀ + r + c) / R : ℤ) : ℝ) := by
      rw [eq_sub_iff_add_eq]; exact_mod_cast hq
    simp only [hf, hJ]
    rw [← distZ_add_int ((((J r : ℤ) : ℝ) + w₀) / R) ((n₀ + r + c) / R)]
    congr 3
    simp only [hJ]
    rw [Int.cast_sub, hq', hw₀def]
    field_simp
    ring
  -- `j` is injective on `{0, …, R-1}`.
  have hJinj : Set.InjOn J (range R : Set ℕ) := by
    intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    have h1 : (n₀ + a + c) % R = (n₀ + b + c) % R := by
      simp only [hJ] at hab; linarith
    have h4 : (n₀ + c) + a ≡ (n₀ + c) + b [ZMOD R] := by
      have h3 : n₀ + a + c ≡ n₀ + b + c [ZMOD R] := h1
      convert h3 using 1 <;> ring
    have h5 : (a : ℤ) % R = b % R := Int.ModEq.add_left_cancel' _ h4
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast ha),
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hb)] at h5
    exact_mod_cast h5
  -- The `j(r)` lie in `(-R/2, R/2]`, i.e. in `{0} ∪ S`, `S` the index set of Lemma 8.
  set S : Finset ℤ := (Icc (-(R : ℤ)) R).filter (fun j : ℤ => j ≠ 0 ∧ 2 * |j| ≤ R) with hS
  have h0S : (0 : ℤ) ∉ S := by simp [hS]
  have himg : (range R).image J ⊆ insert 0 S := by
    intro j hj
    simp only [mem_image, mem_range] at hj
    obtain ⟨r, -, rfl⟩ := hj
    have hm0 := Int.emod_nonneg (n₀ + r + c) hRz.ne'
    have hm1 := Int.emod_lt_of_pos (n₀ + r + c) hRz
    simp only [hJ]
    generalize (n₀ + r + c) % R = m at hm0 hm1 ⊢
    rw [mem_insert, hS, mem_filter, mem_Icc]
    by_cases h : m - c = 0
    · exact Or.inl h
    · right
      refine ⟨⟨by omega, by omega⟩, h, ?_⟩
      rcases abs_cases (m - c) with ⟨h', _⟩ | ⟨h', _⟩ <;> rw [h'] <;> omega
  -- The terms `j ≠ 0`, by Lemma 57.
  have hbound : ∀ j ∈ S, f j ≤ R * (1 / (2 * |(j : ℝ)| - 1)) := by
    intro j hj
    simp only [hS, mem_filter, mem_Icc] at hj
    obtain ⟨-, hj0, hjR⟩ := hj
    have hd := dist_lower hR hj0 hjR hw₀'
    have hj1 : (1 : ℝ) ≤ |(j : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hj0
    have hpos : 0 < (2 * |(j : ℝ)| - 1) / (2 * R) := by apply div_pos <;> linarith
    have hdpos : 0 < 2 * distZ ((j + w₀) / R) := by linarith
    calc f j ≤ 1 / (2 * distZ ((j + w₀) / R)) := minDiv_le_div hdpos.ne'
      _ ≤ 1 / (2 * ((2 * |(j : ℝ)| - 1) / (2 * R))) :=
          one_div_le_one_div_of_le (by linarith) (by linarith)
      _ = R * (1 / (2 * |(j : ℝ)| - 1)) := by field_simp
  -- The term `j = 0` is `min(A, R/(2‖w‖))`.
  have hf00 : f 0 = minDiv A R (2 * distZ w) := by
    have hsmall : |w₀ / R| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos hRpos]
      calc |w₀| / R ≤ |w₀| := div_le_self (abs_nonneg _) (by exact_mod_cast hR)
        _ ≤ 1 / 2 := hw₀'
    simp only [hf, Int.cast_zero, zero_add]
    rw [distZ_eq_abs_of_abs_le_half hsmall, ← hw₀, abs_div, abs_of_pos hRpos,
      ← minDiv_scale (c := (R : ℝ)) hRpos (A := A) (H := 1) (y := 2 * (|w₀| / R))]
    congr 1
    · ring
    · field_simp
  calc ∑ r ∈ range R, minDiv A 1 (2 * distZ ((w + r) / R))
      = ∑ r ∈ range R, f (J r) := sum_congr rfl (fun r _ => hterm r)
    _ = ∑ j ∈ (range R).image J, f j := (sum_image hJinj).symm
    _ ≤ ∑ j ∈ insert 0 S, f j := sum_le_sum_of_subset_of_nonneg himg (fun j _ _ => hf0 j)
    _ = f 0 + ∑ j ∈ S, f j := sum_insert h0S
    _ ≤ f 0 + ∑ j ∈ S, R * (1 / (2 * |(j : ℝ)| - 1)) := by
        gcongr with j hj; exact hbound j hj
    _ = f 0 + R * ∑ j ∈ S, (1 : ℝ) / (2 * |(j : ℝ)| - 1) := by rw [mul_sum]
    _ ≤ f 0 + R * (2 + Real.log R) := by gcongr; exact odd_harmonic_le KR R hR
    _ = minDiv A R (2 * distZ w) + R * (2 + Real.log R) := by rw [hf00]

/-- **[HFF 59] Lemma (Sum over a).**  For `y ∈ ℝ`, `β ∈ ℤ`, `d = gcd(β, Q)` and `A ≥ 1`:
`∑_{a<Q} min(A, 1/(2‖(y+aβ)/Q‖)) ≤ min(dA, Q/(2‖y/d‖)) + Q(2 + log Q)`. -/
theorem a_sum (KR : KnownResults) (hg : 2 ≤ g) (s : ℕ) (y : ℝ) (β : ℤ) {A : ℝ} (hA : 1 ≤ A) :
    ∑ a ∈ range (g ^ s), minDiv A 1 (2 * distZ ((y + a * β) / (g : ℝ) ^ s)) ≤
      minDiv (Int.gcd β (g ^ s) * A) ((g : ℝ) ^ s) (2 * distZ (y / Int.gcd β (g ^ s))) +
        (g : ℝ) ^ s * (2 + Real.log ((g : ℝ) ^ s)) := by
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = g ^ s := ⟨_, rfl⟩
  have hQ1 : 1 ≤ Q := hQ ▸ Nat.one_le_pow _ _ (by omega)
  have hQR : (g : ℝ) ^ s = Q := by rw [hQ]; push_cast; rfl
  have hQZ : (g : ℤ) ^ s = Q := by rw [hQ]; push_cast; rfl
  rw [hQR, hQZ, ← hQ]
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ1
  -- `φ(c) = min(A, 1/(2‖(y + c)/Q‖))` depends only on `c mod Q`.
  set φ : ℤ → ℝ := fun c => minDiv A 1 (2 * distZ ((y + c) / Q)) with hφ
  have h1 : ∀ a : ℕ, minDiv A 1 (2 * distZ ((y + a * β) / Q)) = φ (((a : ℤ) * β) % (Q : ℤ)) := by
    intro a
    have hq := Int.emod_add_mul_ediv ((a : ℤ) * β) Q
    have hq' : ((((a : ℤ) * β) % Q : ℤ) : ℝ) = a * β - Q * ((((a : ℤ) * β) / Q : ℤ) : ℝ) := by
      rw [eq_sub_iff_add_eq]; exact_mod_cast hq
    simp only [hφ]
    rw [← distZ_add_int ((y + ((((a : ℤ) * β) % Q : ℤ) : ℝ)) / Q) (((a : ℤ) * β) / Q), hq']
    congr 3
    field_simp
    ring
  -- Lemma 56.
  rw [sum_congr rfl (fun a _ => h1 a), multiples_sum hQ1 β φ]
  set d := Int.gcd β Q with hd
  have hdQ : d ∣ Q := by
    have := Int.gcd_dvd_right β Q
    exact_mod_cast this
  have hd1 : 1 ≤ d := Nat.pos_of_ne_zero (fun h => by
    rw [h] at hdQ; exact absurd (Nat.eq_zero_of_zero_dvd hdQ) (by omega))
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  set R := Q / d with hR
  have hR1 : 1 ≤ R := Nat.div_pos (Nat.le_of_dvd (by omega) hdQ) (by omega)
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR1
  have hRd : (R : ℝ) * d = Q := by
    rw [hR, Nat.cast_div hdQ hdpos.ne']; field_simp
  -- `(y + rd)/Q = (y/d + r)/(Q/d)`.
  have h2 : ∀ r : ℕ, φ ((r : ℤ) * (d : ℤ)) = minDiv A 1 (2 * distZ ((y / d + r) / R)) := by
    intro r
    simp only [hφ]
    congr 3
    rw [← hRd]
    push_cast
    field_simp
  rw [sum_congr rfl (fun r _ => h2 r)]
  -- Lemma 58 with `R = Q/d`, `w = y/d`.
  have h3 := residue_sum KR hR1 (y / d) hA
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hlog : Real.log R ≤ Real.log Q :=
    Real.log_le_log hRpos (by rw [← hRd]; nlinarith)
  calc (d : ℝ) * ∑ r ∈ range R, minDiv A 1 (2 * distZ ((y / d + r) / R))
      ≤ d * (minDiv A R (2 * distZ (y / d)) + R * (2 + Real.log R)) := by gcongr
    _ = minDiv (d * A) Q (2 * distZ (y / d)) + Q * (2 + Real.log R) := by
        rw [mul_add, mul_minDiv hdpos.le, ← hRd]; ring_nf
    _ ≤ minDiv (d * A) Q (2 * distZ (y / d)) + Q * (2 + Real.log Q) := by gcongr

end PalindromicPowers

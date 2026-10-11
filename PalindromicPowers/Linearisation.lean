import PalindromicPowers.Tree

/-!
# HFF blocks 37–45: phases and the linearisation
-/

namespace PalindromicPowers

open Finset Real

variable {g k : ℕ}

/-- **[HFF 37] Definition (Phases).**  The setting: integers `t, s` with `1 ≤ s ≤ t-2` and
`2(t+s) ≤ L`. -/
def Admissible (L t s : ℕ) : Prop := 1 ≤ s ∧ s + 2 ≤ t ∧ 2 * (t + s) ≤ L

/-- **[HFF 37]** `Λ = 1 + log(1 + 6g^t)`. -/
noncomputable def LambdaT (g t : ℕ) : ℝ := 1 + Real.log (1 + 6 * (g : ℝ) ^ t)

/-- **[HFF 37]** `α_b = ⌊x_b^k / g^t⌋ mod Q`. -/
def alphaB (g k L t s b : ℕ) : ℕ := xb g k L t b ^ k / g ^ t % g ^ s

/-- **[HFF 37]** `β_b = k b^{k-1} mod Q`. -/
def betaB (g k s b : ℕ) : ℕ := k * b ^ (k - 1) % g ^ s

/-- **[HFF 37]** `d_b = gcd(β_b, Q)`. -/
def dB (g k s b : ℕ) : ℕ := Nat.gcd (betaB g k s b) (g ^ s)

/-- **[HFF 37]** `δ_b = k x_b^{k-1} g^{2t+s-L}`. -/
noncomputable def deltaB (g k L t s b : ℕ) : ℝ :=
  k * (xb g k L t b : ℝ) ^ (k - 1) * (g : ℝ) ^ (((2 * t + s : ℕ) : ℤ) - L)

/-- **[HFF 37]** `θ_{b,ℓ,a} = (ℓ δ_b + a β_b)/Q`. -/
noncomputable def thetaB (g k L t s b : ℕ) (ℓ a : ℤ) : ℝ :=
  ((ℓ : ℝ) * deltaB g k L t s b + (a : ℝ) * betaB g k s b) / (g : ℝ) ^ s

/-- **[HFF 37]** `n_b(z) = (α_b + β_b z) mod Q`. -/
def nB (g k L t s b z : ℕ) : ℕ := (alphaB g k L t s b + betaB g k s b * z) % g ^ s

/-- **[HFF 38] Definition (Archimedean phases).**
`φ_b(z) = (x_b + g^t z)^k / g^{L-t-s} - T_b g^s` for real `z ≥ 0`. -/
noncomputable def phiB (g k L t s b : ℕ) (z : ℝ) : ℝ :=
  ((xb g k L t b : ℝ) + (g : ℝ) ^ t * z) ^ k / (g : ℝ) ^ (L - t - s) - (Tb g k t b : ℝ) * (g : ℝ) ^ s

/-- **[HFF 38]** `λ_b(z) = φ_b(0) + δ_b z`. -/
noncomputable def lambdaB (g k L t s b : ℕ) (z : ℝ) : ℝ :=
  phiB g k L t s b 0 + deltaB g k L t s b * z

/-- **[HFF 38]** `δ(T) = k (T g^{L-t})^{1-1/k} g^{2t+s-L}` for real `T > 0`. -/
noncomputable def deltaT (g k L t s : ℕ) (T : ℝ) : ℝ :=
  k * (T * (g : ℝ) ^ (L - t)) ^ (1 - (1 : ℝ) / k) * (g : ℝ) ^ (((2 * t + s : ℕ) : ℤ) - L)


/-- Auxiliary for [HFF 39].  `(g : ℝ) > 0` (also used for blocks 40, 43 and 44). -/
private lemma g_pos (hg : 2 ≤ g) : (0 : ℝ) < g := by
  have : (2 : ℝ) ≤ g := by exact_mod_cast hg
  linarith

/-- **[HFF 39] Lemma (Formula for δ(T)).**  `δ(T) = (kQ/Z)(T/g^t)^{1-1/k}`; hence
`kQ/(gZ) ≤ δ(T) ≤ kQ/Z` for `g^{t-1} ≤ T ≤ g^t`. -/
theorem deltaT_formula (hg : 2 ≤ g) (hk : 2 ≤ k) {L t s : ℕ} (hA : Admissible L t s) :
    (∀ T : ℝ, 0 < T →
      deltaT g k L t s T = k * (g : ℝ) ^ s / Zt g k L t * (T / (g : ℝ) ^ t) ^ (1 - (1 : ℝ) / k)) ∧
    (∀ T : ℝ, (g : ℝ) ^ (t - 1) ≤ T → T ≤ (g : ℝ) ^ t →
      k * (g : ℝ) ^ s / (g * Zt g k L t) ≤ deltaT g k L t s T ∧
        deltaT g k L t s T ≤ k * (g : ℝ) ^ s / Zt g k L t) := by
  obtain ⟨hs1, hst, htsL⟩ := hA
  have hG := g_pos hg
  have hk0 : (0 : ℝ) < k := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hZpos : 0 < Zt g k L t := by unfold Zt Xr; positivity
  -- As `T g^{L-t} = (T/g^t) g^L`, `g^{L(1-1/k)} = g^L/X` and `g^{2t}/X = 1/Z`:
  have hform : ∀ T : ℝ, 0 < T →
      deltaT g k L t s T = k * (g : ℝ) ^ s / Zt g k L t * (T / (g : ℝ) ^ t) ^ (1 - (1 : ℝ) / k) := by
    intro T hT
    have hL : (g : ℝ) ^ L = (g : ℝ) ^ t * (g : ℝ) ^ (L - t) := by
      rw [← pow_add]; congr 1; omega
    have h1 : T * (g : ℝ) ^ (L - t) = T / (g : ℝ) ^ t * (g : ℝ) ^ L := by
      rw [hL]; field_simp
    have key : ((g : ℝ) ^ (L : ℝ)) ^ (1 - (1 : ℝ) / k) * (g : ℝ) ^ (((2 * t + s : ℕ) : ℤ) - L) =
        (g : ℝ) ^ s / (Xr g k L / (g : ℝ) ^ (2 * t)) := by
      unfold Xr
      rw [← Real.rpow_mul hG.le, ← Real.rpow_intCast, ← Real.rpow_add hG,
        ← Real.rpow_natCast (g : ℝ) s, ← Real.rpow_natCast (g : ℝ) (2 * t),
        ← Real.rpow_sub hG, ← Real.rpow_sub hG]
      congr 1; push_cast; ring
    unfold deltaT Zt
    rw [h1, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast (g : ℝ) L]
    calc (k : ℝ) * ((T / (g : ℝ) ^ t) ^ (1 - (1 : ℝ) / k) * ((g : ℝ) ^ (L : ℝ)) ^ (1 - (1 : ℝ) / k)) *
          (g : ℝ) ^ (((2 * t + s : ℕ) : ℤ) - L)
        = k * (T / (g : ℝ) ^ t) ^ (1 - (1 : ℝ) / k) * (((g : ℝ) ^ (L : ℝ)) ^ (1 - (1 : ℝ) / k) *
          (g : ℝ) ^ (((2 * t + s : ℕ) : ℤ) - L)) := by ring
      _ = _ := by rw [key]; ring
  refine ⟨hform, fun T hT1 hT2 => ?_⟩
  -- If `T/g^t ∈ [1/g, 1]` then `(T/g^t)^{1-1/k} ∈ [1/g, 1]`.
  have hT : 0 < T := lt_of_lt_of_le (by positivity) hT1
  have hgt : (g : ℝ) ^ t = (g : ℝ) ^ (t - 1) * g := by rw [← pow_succ]; congr 1; omega
  have hu1 : T / (g : ℝ) ^ t ≤ 1 := by rw [div_le_one (by positivity)]; exact hT2
  have hu0 : 1 / (g : ℝ) ≤ T / (g : ℝ) ^ t := by
    rw [hgt, div_le_div_iff₀ hG (by positivity), one_mul]
    exact mul_le_mul_of_nonneg_right hT1 hG.le
  have hupos : 0 < T / (g : ℝ) ^ t := by positivity
  have hexp0 : 0 ≤ 1 - (1 : ℝ) / k := by
    rw [sub_nonneg, div_le_one hk0]; exact_mod_cast (by omega : 1 ≤ k)
  have hr1 : (T / (g : ℝ) ^ t) ^ (1 - (1 : ℝ) / k) ≤ 1 := Real.rpow_le_one hupos.le hu1 hexp0
  have hr0 : T / (g : ℝ) ^ t ≤ (T / (g : ℝ) ^ t) ^ (1 - (1 : ℝ) / k) := by
    calc T / (g : ℝ) ^ t = (T / (g : ℝ) ^ t) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (T / (g : ℝ) ^ t) ^ (1 - (1 : ℝ) / k) :=
        Real.rpow_le_rpow_of_exponent_ge hupos hu1 (by have : 0 < (1 : ℝ) / k := by positivity
                                                       linarith)
  rw [hform T hT]
  have hc : 0 < k * (g : ℝ) ^ s / Zt g k L t := by positivity
  constructor
  · calc k * (g : ℝ) ^ s / (g * Zt g k L t) = k * (g : ℝ) ^ s / Zt g k L t * (1 / g) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hu0.trans hr0) hc.le
  · calc _ ≤ k * (g : ℝ) ^ s / Zt g k L t * 1 := mul_le_mul_of_nonneg_left hr1 hc.le
      _ = _ := mul_one _

/-- Auxiliary for [HFF 40].  If `Z_b ≥ 1`, then `x_b` is one of the integers counted by `Z_b`:
`x_b ≡ b (mod g^t)` and `x_b ∈ I_b`.  (Also used for blocks 41 and 43.) -/
private lemma xb_spec {L t b : ℕ} (hZ : 1 ≤ Zb g k L t b) :
    xb g k L t b % g ^ t = b ∧ InI g k L t b (xb g k L t b) := by
  have hne : (nodeElems g k L t b).Nonempty := Finset.card_pos.mp hZ
  have hmem : xb g k L t b ∈ nodeElems g k L t b := by
    unfold xb
    split_ifs
    exact Finset.min'_mem _ _
  exact (Finset.mem_filter.mp hmem).2

/-- **[HFF 40] Lemma (δ_b is near δ(T_b)).**  `δ(T_b) ≤ δ_b ≤ (1 + g^{1-t}) δ(T_b)`. -/
theorem deltaB_near (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) {L t s b : ℕ}
    (hA : Admissible L t s) (hb : IsNode g k t b) (hZ : 1 ≤ Zb g k L t b) :
    deltaT g k L t s (Tb g k t b) ≤ deltaB g k L t s b ∧
      deltaB g k L t s b ≤ (1 + (g : ℝ) ^ ((1 : ℤ) - t)) * deltaT g k L t s (Tb g k t b) := by
  obtain ⟨hs1, hst, htsL⟩ := hA
  obtain ⟨-, hx0, hx1⟩ := xb_spec hZ
  obtain ⟨hT0, -⟩ := leading_digit hg (by omega : 1 ≤ t) hb
  have hG := g_pos hg
  have hk0 : (0 : ℝ) < k := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hexp0 : 0 ≤ 1 - (1 : ℝ) / k := by
    rw [sub_nonneg, div_le_one hk0]; exact_mod_cast (by omega : 1 ≤ k)
  have hTge : (g : ℝ) ^ (t - 1) ≤ (Tb g k t b : ℝ) := by exact_mod_cast hT0
  have hTpos : 0 < (Tb g k t b : ℝ) := lt_of_lt_of_le (by positivity) hTge
  have hY0pos : 0 < (Tb g k t b : ℝ) * (g : ℝ) ^ (L - t) := by positivity
  -- `x_b ∈ I_b`: `y₀ ≤ x_b^k < y₁ = y₀ (1 + 1/T_b)`
  have hlo : (Tb g k t b : ℝ) * (g : ℝ) ^ (L - t) ≤ (xb g k L t b : ℝ) ^ k := by
    have := (Nat.cast_le (α := ℝ)).mpr hx0
    unfold y0 at this; push_cast at this; exact this
  have hhi : (xb g k L t b : ℝ) ^ k ≤
      (Tb g k t b : ℝ) * (g : ℝ) ^ (L - t) * (1 + 1 / (Tb g k t b : ℝ)) := by
    have := (Nat.cast_lt (α := ℝ)).mpr hx1
    unfold y1 y0 at this; push_cast at this
    rw [mul_add, mul_one, mul_comm _ (1 / _), ← mul_assoc, one_div_mul_cancel hTpos.ne', one_mul]
    exact this.le
  -- `x_b^{k-1} = (x_b^k)^{1-1/k}`
  have hpow : (xb g k L t b : ℝ) ^ (k - 1) = ((xb g k L t b : ℝ) ^ k) ^ (1 - (1 : ℝ) / k) := by
    rw [← Real.rpow_natCast (xb g k L t b : ℝ) k, ← Real.rpow_mul (Nat.cast_nonneg _),
      ← Real.rpow_natCast]
    congr 1; rw [Nat.cast_sub (by omega)]; field_simp; push_cast; ring
  -- `1/T_b ≤ g^{1-t}` (Lemma 32)
  have hgt : 1 / (Tb g k t b : ℝ) ≤ (g : ℝ) ^ ((1 : ℤ) - t) := by
    rw [show (1 : ℤ) - t = -((t - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, one_div]
    exact inv_anti₀ (by positivity) hTge
  have hE : 0 < (g : ℝ) ^ (((2 * t + s : ℕ) : ℤ) - L) := zpow_pos hG _
  unfold deltaB deltaT
  rw [hpow]
  constructor
  · apply mul_le_mul_of_nonneg_right _ hE.le
    apply mul_le_mul_of_nonneg_left _ hk0.le
    exact Real.rpow_le_rpow hY0pos.le hlo hexp0
  · -- the ratio lies in `[1, (y₁/y₀)^{1-1/k}] ⊂ [1, 1 + 1/T_b] ⊂ [1, 1 + g^{1-t}]`
    have h1 : ((xb g k L t b : ℝ) ^ k) ^ (1 - (1 : ℝ) / k) ≤
        (1 + (g : ℝ) ^ ((1 : ℤ) - t)) * ((Tb g k t b : ℝ) * (g : ℝ) ^ (L - t)) ^ (1 - (1 : ℝ) / k) := by
      have hone : (1 : ℝ) ≤ 1 + 1 / (Tb g k t b : ℝ) := by
        have : 0 < 1 / (Tb g k t b : ℝ) := by positivity
        linarith
      calc ((xb g k L t b : ℝ) ^ k) ^ (1 - (1 : ℝ) / k)
          ≤ ((Tb g k t b : ℝ) * (g : ℝ) ^ (L - t) * (1 + 1 / (Tb g k t b : ℝ))) ^ (1 - (1 : ℝ) / k) :=
            Real.rpow_le_rpow (by positivity) hhi hexp0
        _ = ((Tb g k t b : ℝ) * (g : ℝ) ^ (L - t)) ^ (1 - (1 : ℝ) / k) *
              (1 + 1 / (Tb g k t b : ℝ)) ^ (1 - (1 : ℝ) / k) :=
            Real.mul_rpow hY0pos.le (by positivity)
        _ ≤ ((Tb g k t b : ℝ) * (g : ℝ) ^ (L - t)) ^ (1 - (1 : ℝ) / k) *
              (1 + 1 / (Tb g k t b : ℝ)) ^ (1 : ℝ) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Real.rpow_le_rpow_of_exponent_le hone (by
              have : 0 < (1 : ℝ) / k := by positivity
              linarith)
        _ ≤ ((Tb g k t b : ℝ) * (g : ℝ) ^ (L - t)) ^ (1 - (1 : ℝ) / k) *
              (1 + (g : ℝ) ^ ((1 : ℤ) - t)) := by
            rw [Real.rpow_one]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith
        _ = _ := mul_comm _ _
    calc (k : ℝ) * ((xb g k L t b : ℝ) ^ k) ^ (1 - (1 : ℝ) / k) *
          (g : ℝ) ^ (((2 * t + s : ℕ) : ℤ) - L)
        ≤ k * ((1 + (g : ℝ) ^ ((1 : ℤ) - t)) *
            ((Tb g k t b : ℝ) * (g : ℝ) ^ (L - t)) ^ (1 - (1 : ℝ) / k)) *
          (g : ℝ) ^ (((2 * t + s : ℕ) : ℤ) - L) := by
          apply mul_le_mul_of_nonneg_right _ hE.le
          exact mul_le_mul_of_nonneg_left h1 hk0.le
      _ = _ := by ring

/-- Auxiliary for [HFF 41].  The binomial theorem to second order over `ℕ`:
`(x + y)^k = x^k + k x^{k-1} y + y² N` for some `N ∈ ℕ`. -/
private lemma binom_two_terms (x y : ℕ) :
    ∀ k : ℕ, ∃ N : ℕ, (x + y) ^ k = x ^ k + k * x ^ (k - 1) * y + y ^ 2 * N
  | 0 => ⟨0, by simp⟩
  | 1 => ⟨0, by simp⟩
  | k + 2 => by
    obtain ⟨N, hN⟩ := binom_two_terms x y (k + 1)
    refine ⟨x * N + y * N + (k + 1) * x ^ k, ?_⟩
    rw [pow_succ, hN, show k + 2 - 1 = k + 1 by omega, show k + 1 - 1 = k by omega]
    ring

/-- **[HFF 41] Lemma (Lower block).**  For `x = x_b + g^t z`: `⌊x^k/g^t⌋ mod Q = n_b(z)`. -/
theorem lower_block (hg : 2 ≤ g) (hk : 2 ≤ k) {L t s b : ℕ} (hA : Admissible L t s)
    (hb : IsNode g k t b) (hZ : 1 ≤ Zb g k L t b) (z : ℕ) :
    (xb g k L t b + g ^ t * z) ^ k / g ^ t % g ^ s = nB g k L t s b z := by
  obtain ⟨hs1, hst, htsL⟩ := hA
  obtain ⟨hxb, -⟩ := xb_spec hZ
  have hgt : 0 < g ^ t := by positivity
  -- binomial theorem: `x^k = x_b^k + k x_b^{k-1} g^t z + g^{2t} N`
  obtain ⟨N, hN⟩ := binom_two_terms (xb g k L t b) (g ^ t * z) k
  have hdiv : (xb g k L t b + g ^ t * z) ^ k / g ^ t =
      xb g k L t b ^ k / g ^ t + (k * xb g k L t b ^ (k - 1) * z + g ^ t * (z ^ 2 * N)) := by
    rw [hN, show xb g k L t b ^ k + k * xb g k L t b ^ (k - 1) * (g ^ t * z) + (g ^ t * z) ^ 2 * N =
      xb g k L t b ^ k + g ^ t * (k * xb g k L t b ^ (k - 1) * z + g ^ t * (z ^ 2 * N)) by ring,
      Nat.add_mul_div_left _ _ hgt]
  rw [hdiv]
  -- reduce modulo `Q = g^s`, using `s ≤ t` and `x_b ≡ b (mod g^t)`
  have hdvd : g ^ s ∣ g ^ t := pow_dvd_pow g (by omega)
  have hxbQ : xb g k L t b ≡ b [MOD g ^ s] := by
    have h := Nat.mod_modEq (xb g k L t b) (g ^ t)
    rw [hxb] at h
    exact (h.of_dvd hdvd).symm
  unfold nB alphaB betaB
  show _ ≡ _ [MOD g ^ s]
  have h1 : xb g k L t b ^ k / g ^ t ≡ xb g k L t b ^ k / g ^ t % g ^ s [MOD g ^ s] :=
    (Nat.mod_modEq _ _).symm
  have h2 : k * xb g k L t b ^ (k - 1) * z ≡ k * b ^ (k - 1) % g ^ s * z [MOD g ^ s] :=
    Nat.ModEq.mul_right z (((hxbQ.pow (k - 1)).mul_left k).trans (Nat.mod_modEq _ _).symm)
  have h3 : g ^ t * (z ^ 2 * N) ≡ 0 [MOD g ^ s] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hdvd _)
  have := h1.add (h2.add h3)
  rwa [add_zero] at this

/-- **[HFF 42] Lemma (Upper block).**  For `x = x_b + g^t z ∈ I_b`:
`⌊x^k/g^{L-t-s}⌋ mod Q = ⌊φ_b(z)⌋`. -/
theorem upper_block (hg : 2 ≤ g) (hk : 2 ≤ k) {L t s b : ℕ} (hA : Admissible L t s)
    (hb : IsNode g k t b) (hZ : 1 ≤ Zb g k L t b) {z : ℕ}
    (hx : InI g k L t b (xb g k L t b + g ^ t * z)) :
    (((xb g k L t b + g ^ t * z) ^ k / g ^ (L - t - s) % g ^ s : ℕ) : ℤ) = ⌊phiB g k L t s b z⌋ := by
  obtain ⟨hs1, hst, htsL⟩ := hA
  obtain ⟨hx0, hx1⟩ := hx
  have hgpos : 0 < g := by omega
  -- As `x ∈ I_b`, `T_b g^{L-t} ≤ x^k < (T_b + 1) g^{L-t}`, so `⌊x^k/g^{L-t}⌋ = T_b`.
  have hT : (xb g k L t b + g ^ t * z) ^ k / g ^ (L - t) = Tb g k t b := by
    apply Nat.div_eq_of_lt_le
    · exact hx0
    · unfold y1 y0 at hx1; rw [add_mul, one_mul]; exact hx1
  have hT' : (xb g k L t b + g ^ t * z) ^ k / g ^ (L - t - s) / g ^ s = Tb g k t b := by
    rw [Nat.div_div_eq_div_mul, ← pow_add, show L - t - s + s = L - t by omega, hT]
  have hmod := Nat.mod_add_div ((xb g k L t b + g ^ t * z) ^ k / g ^ (L - t - s)) (g ^ s)
  rw [hT'] at hmod
  -- `⌊x^k/g^{L-t-s}⌋ mod g^s = ⌊x^k/g^{L-t-s}⌋ - g^s T_b = ⌊x^k/g^{L-t-s} - T_b g^s⌋`
  have hphi : phiB g k L t s b z = (((xb g k L t b + g ^ t * z) ^ k : ℕ) : ℝ) /
      ((g ^ (L - t - s) : ℕ) : ℝ) - ((Tb g k t b * g ^ s : ℕ) : ℝ) := by
    unfold phiB; push_cast; ring
  rw [hphi, Int.floor_sub_natCast, Int.floor_div_natCast, Int.floor_natCast, ← Int.natCast_div]
  have := congrArg (Nat.cast : ℕ → ℤ) hmod
  push_cast at this ⊢
  linarith

/-- Auxiliary for [HFF 43].  For `a, h ≥ 0` and `k = m + 2`:
`0 ≤ (a+h)^k - a^k - k a^{k-1} h ≤ (k(k-1)/2) (a+h)^{k-2} h²`.  This is the second order Taylor
bound used in the HFF proof, for the polynomial `y ↦ y^k`, proved by induction on `m`. -/
private lemma pow_taylor_bound {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) (m : ℕ) :
    0 ≤ (a + h) ^ (m + 2) - a ^ (m + 2) - (m + 2) * a ^ (m + 1) * h ∧
      (a + h) ^ (m + 2) - a ^ (m + 2) - (m + 2) * a ^ (m + 1) * h ≤
        (m + 2) * (m + 1) / 2 * (a + h) ^ m * h ^ 2 := by
  induction m with
  | zero =>
    have : (a + h) ^ (0 + 2) - a ^ (0 + 2) - ((0 : ℕ) + 2 : ℝ) * a ^ (0 + 1) * h = h ^ 2 := by
      push_cast; ring
    rw [this]; push_cast
    exact ⟨by positivity, by nlinarith⟩
  | succ m ih =>
    obtain ⟨ih0, ih1⟩ := ih
    have hrec : (a + h) ^ (m + 1 + 2) - a ^ (m + 1 + 2) - (((m + 1 : ℕ) : ℝ) + 2) * a ^ (m + 1 + 1) * h
        = (a + h) * ((a + h) ^ (m + 2) - a ^ (m + 2) - (m + 2) * a ^ (m + 1) * h) +
          (m + 2) * a ^ (m + 1) * h ^ 2 := by
      push_cast; ring
    have hpow : a ^ (m + 1) ≤ (a + h) ^ (m + 1) := pow_le_pow_left₀ ha (by linarith) _
    rw [hrec]
    have hah : 0 ≤ a + h := by linarith
    constructor
    · exact add_nonneg (mul_nonneg hah ih0) (by positivity)
    · calc (a + h) * ((a + h) ^ (m + 2) - a ^ (m + 2) - (m + 2) * a ^ (m + 1) * h) +
            (m + 2) * a ^ (m + 1) * h ^ 2
          ≤ (a + h) * ((m + 2) * (m + 1) / 2 * (a + h) ^ m * h ^ 2) +
            (m + 2) * (a + h) ^ (m + 1) * h ^ 2 := by
            gcongr
        _ = (((m + 1 : ℕ) : ℝ) + 2) * (((m + 1 : ℕ) : ℝ) + 1) / 2 * (a + h) ^ (m + 1) * h ^ 2 := by
            push_cast; ring

/-- **[HFF 43] Lemma (Taylor bound).**  For real `z ≥ 0` with `x_b + g^t z ∈ I_b`:
`0 ≤ φ_b(z) - λ_b(z) ≤ (k(k-1)/2) y₁^{1-2/k} |I_b|² g^{t+s-L}`. -/
theorem taylor_bound (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) {L t s b : ℕ}
    (hA : Admissible L t s) (hb : IsNode g k t b) (hZ : 1 ≤ Zb g k L t b) {z : ℝ} (hz : 0 ≤ z)
    (hx0 : (y0 g k L t b : ℝ) ≤ ((xb g k L t b : ℝ) + (g : ℝ) ^ t * z) ^ k)
    (hx1 : ((xb g k L t b : ℝ) + (g : ℝ) ^ t * z) ^ k < y1 g k L t b) :
    0 ≤ phiB g k L t s b z - lambdaB g k L t s b z ∧
      phiB g k L t s b z - lambdaB g k L t s b z ≤
        k * (k - 1) / 2 * (y1 g k L t b : ℝ) ^ (1 - (2 : ℝ) / k) * Ilen g k L t b ^ 2 *
          (g : ℝ) ^ (((t + s : ℕ) : ℤ) - L) := by
  obtain ⟨hs1, hst, htsL⟩ := hA
  obtain ⟨-, hxb0, -⟩ := xb_spec hZ
  have hG := g_pos hg
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have ha0 : (0 : ℝ) ≤ (xb g (m + 2) L t b : ℝ) := Nat.cast_nonneg _
  have hh0 : (0 : ℝ) ≤ (g : ℝ) ^ t * z := by positivity
  have hDpos : (0 : ℝ) < (g : ℝ) ^ (L - t - s) := by positivity
  -- `φ_b(z) - λ_b(z) = ((x_b + g^t z)^k - x_b^k - k x_b^{k-1} g^t z) / g^{L-t-s}`
  have hdiff : phiB g (m + 2) L t s b z - lambdaB g (m + 2) L t s b z =
      (((xb g (m + 2) L t b : ℝ) + (g : ℝ) ^ t * z) ^ (m + 2) - (xb g (m + 2) L t b : ℝ) ^ (m + 2) -
        (m + 2) * (xb g (m + 2) L t b : ℝ) ^ (m + 1) * ((g : ℝ) ^ t * z)) / (g : ℝ) ^ (L - t - s) := by
    have hz' : (g : ℝ) ^ (((2 * t + s : ℕ) : ℤ) - L) = (g : ℝ) ^ t / (g : ℝ) ^ (L - t - s) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hG.ne']; congr 1; omega
    unfold lambdaB phiB deltaB
    rw [hz', show m + 2 - 1 = m + 1 by omega]
    push_cast
    field_simp
    ring
  -- Taylor's bound for `y ↦ y^k`
  obtain ⟨hF0, hF1⟩ := pow_taylor_bound ha0 hh0 m
  rw [hdiff]
  refine ⟨div_nonneg hF0 hDpos.le, ?_⟩
  have hexp : (0 : ℝ) ≤ 1 - (2 : ℝ) / ((m + 2 : ℕ) : ℝ) := by
    rw [sub_nonneg, div_le_one (by positivity)]; push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  -- `x_b + g^t ζ ≤ y₁^{1/k}`, so `(x_b + g^t z)^{k-2} ≤ y₁^{1-2/k}`
  have hY1 : ((xb g (m + 2) L t b : ℝ) + (g : ℝ) ^ t * z) ^ m ≤
      (y1 g (m + 2) L t b : ℝ) ^ (1 - (2 : ℝ) / ((m + 2 : ℕ) : ℝ)) := by
    have : ((xb g (m + 2) L t b : ℝ) + (g : ℝ) ^ t * z) ^ m =
        (((xb g (m + 2) L t b : ℝ) + (g : ℝ) ^ t * z) ^ (m + 2)) ^ (1 - (2 : ℝ) / ((m + 2 : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast _ (m + 2), ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]
      congr 1; push_cast; field_simp; ring
    rw [this]
    exact Real.rpow_le_rpow (by positivity) hx1.le hexp
  -- `g^t z ≤ |I_b|`
  have hI : (g : ℝ) ^ t * z ≤ Ilen g (m + 2) L t b := by
    unfold Ilen
    have e1 : (xb g (m + 2) L t b : ℝ) + (g : ℝ) ^ t * z <
        (y1 g (m + 2) L t b : ℝ) ^ ((1 : ℝ) / ((m + 2 : ℕ) : ℝ)) := by
      calc (xb g (m + 2) L t b : ℝ) + (g : ℝ) ^ t * z =
            (((xb g (m + 2) L t b : ℝ) + (g : ℝ) ^ t * z) ^ (m + 2)) ^ ((1 : ℝ) / ((m + 2 : ℕ) : ℝ)) := by
            rw [one_div, Real.pow_rpow_inv_natCast (by positivity) (by omega)]
        _ < _ := Real.rpow_lt_rpow (by positivity) hx1 (by positivity)
    have e2 : (y0 g (m + 2) L t b : ℝ) ^ ((1 : ℝ) / ((m + 2 : ℕ) : ℝ)) ≤ (xb g (m + 2) L t b : ℝ) := by
      have hxb0' : (y0 g (m + 2) L t b : ℝ) ≤ (xb g (m + 2) L t b : ℝ) ^ (m + 2) := by
        exact_mod_cast hxb0
      calc (y0 g (m + 2) L t b : ℝ) ^ ((1 : ℝ) / ((m + 2 : ℕ) : ℝ))
          ≤ ((xb g (m + 2) L t b : ℝ) ^ (m + 2)) ^ ((1 : ℝ) / ((m + 2 : ℕ) : ℝ)) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) hxb0' (by positivity)
        _ = (xb g (m + 2) L t b : ℝ) := by
            rw [one_div, Real.pow_rpow_inv_natCast ha0 (by omega)]
    linarith
  have hzpow : (g : ℝ) ^ (((t + s : ℕ) : ℤ) - L) = 1 / (g : ℝ) ^ (L - t - s) := by
    rw [← zpow_natCast, one_div, ← zpow_neg]; congr 1; omega
  rw [hzpow, div_eq_mul_one_div _ ((g : ℝ) ^ (L - t - s))]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc _ ≤ (m + 2) * (m + 1) / 2 * ((xb g (m + 2) L t b : ℝ) + (g : ℝ) ^ t * z) ^ m *
          ((g : ℝ) ^ t * z) ^ 2 := hF1
    _ ≤ (m + 2) * (m + 1) / 2 * (y1 g (m + 2) L t b : ℝ) ^ (1 - (2 : ℝ) / ((m + 2 : ℕ) : ℝ)) *
          Ilen g (m + 2) L t b ^ 2 := by
        gcongr
    _ = _ := by push_cast; ring

/-- **[HFF 44] Lemma (Archimedean linearisation).**  In the setting of Lemma 43,
`0 ≤ φ_b(z) - λ_b(z) ≤ 1/g`. -/
theorem arch_linearisation (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) {L t s b : ℕ}
    (hA : Admissible L t s) (hb : IsNode g k t b) (hZ : 1 ≤ Zb g k L t b) {z : ℝ} (hz : 0 ≤ z)
    (hx0 : (y0 g k L t b : ℝ) ≤ ((xb g k L t b : ℝ) + (g : ℝ) ^ t * z) ^ k)
    (hx1 : ((xb g k L t b : ℝ) + (g : ℝ) ^ t * z) ^ k < y1 g k L t b) :
    0 ≤ phiB g k L t s b z - lambdaB g k L t s b z ∧
      phiB g k L t s b z - lambdaB g k L t s b z ≤ 1 / g := by
  obtain ⟨h0, h1⟩ := taylor_bound KR hg hk hA hb hZ hz hx0 hx1
  refine ⟨h0, h1.trans ?_⟩
  obtain ⟨hs1, hst, htsL⟩ := hA
  have hG := g_pos hg
  have hG1 : (1 : ℝ) ≤ g := by
    have : (2 : ℝ) ≤ g := by exact_mod_cast hg
    linarith
  -- Lemma 34: `g^{L-1} ≤ y₀ < y₁ ≤ 2y₀` and `|I_b| = g^{L-t}/(k ξ^{1-1/k})` with `ξ ≥ y₀`
  obtain ⟨hy0, hy01, -, hy12, ξ, hξ0, -, hIlen⟩ :=
    interval_endpoints KR hg hk (by omega : 1 ≤ t) (by omega : t ≤ L) hb
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hY0ge : (g : ℝ) ^ (L - 1) ≤ (y0 g (m + 2) L t b : ℝ) := by exact_mod_cast hy0
  have hY0pos : (0 : ℝ) < (y0 g (m + 2) L t b : ℝ) := lt_of_lt_of_le (by positivity) hY0ge
  have hY01 : (y0 g (m + 2) L t b : ℝ) ≤ (y1 g (m + 2) L t b : ℝ) := by exact_mod_cast hy01.le
  have hY1pos : (0 : ℝ) < (y1 g (m + 2) L t b : ℝ) := lt_of_lt_of_le hY0pos hY01
  have hY12 : (y1 g (m + 2) L t b : ℝ) ≤ 2 * (y0 g (m + 2) L t b : ℝ) := by exact_mod_cast hy12
  have hexp1 : (0 : ℝ) ≤ 1 - (1 : ℝ) / ((m + 2 : ℕ) : ℝ) := by
    rw [sub_nonneg, div_le_one (by positivity)]; push_cast
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  -- `u = y₀^{1/k}` and `v = y₁^{1/k}`, so that `u^k = y₀`, `v^k = y₁` and `u ≤ v`
  set u := (y0 g (m + 2) L t b : ℝ) ^ ((1 : ℝ) / ((m + 2 : ℕ) : ℝ)) with hu_def
  set v := (y1 g (m + 2) L t b : ℝ) ^ ((1 : ℝ) / ((m + 2 : ℕ) : ℝ)) with hv_def
  have hupos : 0 < u := Real.rpow_pos_of_pos hY0pos _
  have hu : u ^ (m + 2) = (y0 g (m + 2) L t b : ℝ) := by
    rw [hu_def, one_div]; exact Real.rpow_inv_natCast_pow hY0pos.le (by omega)
  have hv : v ^ (m + 2) = (y1 g (m + 2) L t b : ℝ) := by
    rw [hv_def, one_div]; exact Real.rpow_inv_natCast_pow hY1pos.le (by omega)
  have huv : u ≤ v := Real.rpow_le_rpow hY0pos.le hY01 (by positivity)
  -- `y₁^{1-2/k} = v^{k-2}`
  have hY1v : (y1 g (m + 2) L t b : ℝ) ^ (1 - (2 : ℝ) / ((m + 2 : ℕ) : ℝ)) = v ^ m := by
    rw [hv_def, ← Real.rpow_natCast _ m, ← Real.rpow_mul hY1pos.le]
    congr 1; push_cast; field_simp; ring
  -- `|I_b| ≤ g^{L-t}/(k y₀^{1-1/k}) = g^{L-t}/(k u^{k-1})`
  have hξu : u ^ (m + 1) ≤ ξ ^ (1 - (1 : ℝ) / ((m + 2 : ℕ) : ℝ)) := by
    have : u ^ (m + 1) = (y0 g (m + 2) L t b : ℝ) ^ (1 - (1 : ℝ) / ((m + 2 : ℕ) : ℝ)) := by
      rw [hu_def, ← Real.rpow_natCast _ (m + 1), ← Real.rpow_mul hY0pos.le]
      congr 1; push_cast; field_simp; ring
    rw [this]; exact Real.rpow_le_rpow hY0pos.le hξ0 hexp1
  have hIle : Ilen g (m + 2) L t b ≤ (g : ℝ) ^ (L - t) / (((m + 2 : ℕ) : ℝ) * u ^ (m + 1)) := by
    rw [hIlen]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hξu (by positivity))
  have hI0 : 0 ≤ Ilen g (m + 2) L t b := by
    rw [hIlen]
    have : 0 < ξ := lt_of_lt_of_le hY0pos hξ0
    positivity
  -- `(y₁/y₀)^{1-2/k} ≤ 2`, in the form `v^{k-2} ≤ 2u^{k-2}` (as `v^k = y₁ ≤ 2y₀ = 2u^k`, `u ≤ v`)
  have hvu : v ^ m ≤ 2 * u ^ m := by
    have : v ^ m * v ^ 2 ≤ 2 * u ^ m * v ^ 2 := by
      calc v ^ m * v ^ 2 = (y1 g (m + 2) L t b : ℝ) := by rw [← hv]; ring
        _ ≤ 2 * (y0 g (m + 2) L t b : ℝ) := hY12
        _ = 2 * u ^ m * u ^ 2 := by rw [← hu]; ring
        _ ≤ 2 * u ^ m * v ^ 2 := by gcongr
    exact le_of_mul_le_mul_right this (by positivity)
  -- powers of `g`: `g^{t+s-L} = 1/g^{L-t-s}`, `g^{L-t} = g^{L-t-s} g^s`,
  -- `g^{L-1} = g^{L-t-s} g^s g^s g^{t-s-1}` and `g ≤ g^{t-s-1}` (as `s ≤ t-2`)
  have hzpow : (g : ℝ) ^ (((t + s : ℕ) : ℤ) - L) = 1 / (g : ℝ) ^ (L - t - s) := by
    rw [← zpow_natCast, one_div, ← zpow_neg]; congr 1; omega
  have hP : (g : ℝ) ^ (L - t) = (g : ℝ) ^ (L - t - s) * (g : ℝ) ^ s := by
    rw [← pow_add]; congr 1; omega
  have hPL : (g : ℝ) ^ (L - 1) =
      (g : ℝ) ^ (L - t - s) * (g : ℝ) ^ s * (g : ℝ) ^ s * (g : ℝ) ^ (t - s - 1) := by
    rw [← pow_add, ← pow_add, ← pow_add]; congr 1; omega
  have hgts : (g : ℝ) ≤ (g : ℝ) ^ (t - s - 1) := by
    calc (g : ℝ) = (g : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hG1 (by omega)
  have hk1 : (0 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) * (((m + 2 : ℕ) : ℝ) - 1) / 2 := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast
    apply div_nonneg _ (by norm_num)
    apply mul_nonneg <;> linarith
  have hkk : (((m + 2 : ℕ) : ℝ) - 1) / ((m + 2 : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  rw [hY1v, hzpow]
  -- the bound of Lemma 43 is at most `((k-1)/k) g^{L-t+s}/y₀ ≤ g^{s+1-t} ≤ 1/g`
  calc ((m + 2 : ℕ) : ℝ) * (((m + 2 : ℕ) : ℝ) - 1) / 2 * v ^ m * Ilen g (m + 2) L t b ^ 2 *
        (1 / (g : ℝ) ^ (L - t - s))
      ≤ ((m + 2 : ℕ) : ℝ) * (((m + 2 : ℕ) : ℝ) - 1) / 2 * (2 * u ^ m) *
          ((g : ℝ) ^ (L - t) / (((m + 2 : ℕ) : ℝ) * u ^ (m + 1))) ^ 2 *
        (1 / (g : ℝ) ^ (L - t - s)) := by
        gcongr
    _ = (((m + 2 : ℕ) : ℝ) - 1) / ((m + 2 : ℕ) : ℝ) *
          ((g : ℝ) ^ (L - t - s) * (g : ℝ) ^ s * (g : ℝ) ^ s) / u ^ (m + 2) := by
        rw [hP]; field_simp; ring
    _ ≤ 1 * ((g : ℝ) ^ (L - t - s) * (g : ℝ) ^ s * (g : ℝ) ^ s) / u ^ (m + 2) := by
        gcongr
    _ = ((g : ℝ) ^ (L - t - s) * (g : ℝ) ^ s * (g : ℝ) ^ s) / (y0 g (m + 2) L t b : ℝ) := by
        rw [hu, one_mul]
    _ ≤ ((g : ℝ) ^ (L - t - s) * (g : ℝ) ^ s * (g : ℝ) ^ s) / (g : ℝ) ^ (L - 1) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hY0ge
    _ ≤ 1 / g := by
        rw [hPL, div_le_div_iff₀ (by positivity) hG, one_mul]
        exact mul_le_mul_of_nonneg_left hgts (by positivity)

/-- Auxiliary for [HFF 45].  The digits of `⌊n/g^a⌋` are those of `n` shifted by `a`. -/
private lemma digit_div_pow (n a i : ℕ) : digit g (n / g ^ a) i = digit g n (a + i) := by
  unfold digit; rw [Nat.div_div_eq_div_mul, ← pow_add]

/-- Auxiliary for [HFF 45].  For `i < s`, the `i`-th digit of `n mod g^s` is that of `n`. -/
private lemma digit_mod_pow (n : ℕ) {s i : ℕ} (hi : i < s) :
    digit g (n % g ^ s) i = digit g n i := by
  unfold digit
  rw [show g ^ s = g ^ i * g ^ (s - i) by rw [← pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self g (by omega))]

/-- **[HFF 45] Lemma (The palindrome condition).**  For `x = x_b + g^t z ∈ 𝒬_L ∩ I_b`:
`λ_b(z) - rev_s(n_b(z)) ∈ [-1/g, 1)`. -/
theorem palindrome_condition (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) {L t s b : ℕ}
    (hA : Admissible L t s) (hb : IsNode g k t b) (hZ : 1 ≤ Zb g k L t b) {z : ℕ}
    (hQ : xb g k L t b + g ^ t * z ∈ powSet g k L) (hI : InI g k L t b (xb g k L t b + g ^ t * z)) :
    -1 / (g : ℝ) ≤ lambdaB g k L t s b z - rev g s (nB g k L t s b z) ∧
      lambdaB g k L t s b z - rev g s (nB g k L t s b z) < 1 := by
  have hst := hA.2.1
  have htsL := hA.2.2
  -- the digits `N_r` of `x^k` satisfy `N_r = N_{L-1-r}` (Definition 28)
  have hpal : ∀ i < L, digit g ((xb g k L t b + g ^ t * z) ^ k) i =
      digit g ((xb g k L t b + g ^ t * z) ^ k) (L - 1 - i) :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hQ).2).2
  -- Lemmas 41 and 4: `n_b(z) = ∑_{i<s} N_{t+i} gⁱ`; Lemma 4: `⌊x^k/g^{L-t-s}⌋ mod Q =
  -- ∑_{i<s} N_{L-t-s+i} gⁱ`, which is `rev_s(n_b(z))` as `N_r = N_{L-1-r}`
  have hrev : (xb g k L t b + g ^ t * z) ^ k / g ^ (L - t - s) % g ^ s =
      rev g s (nB g k L t s b z) := by
    rw [← lower_block hg hk hA hb hZ z, (digit_window hg).1 _ s, rev]
    conv_rhs => rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mem_range] at hr
    rw [digit_div_pow, digit_mod_pow _ (by omega : s - 1 - r < s), digit_div_pow,
      hpal (L - t - s + r) (by omega)]
    congr 2 <;> omega
  -- Lemma 42: `⌊φ_b(z)⌋ = rev_s(n_b(z))`
  have hfl : ((rev g s (nB g k L t s b z) : ℕ) : ℤ) = ⌊phiB g k L t s b z⌋ := by
    rw [← hrev]; exact upper_block hg hk hA hb hZ hI
  -- `0 ≤ φ_b(z) - ⌊φ_b(z)⌋ < 1`
  have hle : (rev g s (nB g k L t s b z) : ℝ) ≤ phiB g k L t s b z := by
    have := Int.floor_le (phiB g k L t s b z)
    rw [← hfl] at this; exact_mod_cast this
  have hlt : phiB g k L t s b z < (rev g s (nB g k L t s b z) : ℝ) + 1 := by
    have := Int.lt_floor_add_one (phiB g k L t s b z)
    rw [← hfl] at this; exact_mod_cast this
  -- Lemma 44: `0 ≤ φ_b(z) - λ_b(z) ≤ 1/g`
  have hx0 : (y0 g k L t b : ℝ) ≤ ((xb g k L t b : ℝ) + (g : ℝ) ^ t * (z : ℝ)) ^ k := by
    exact_mod_cast hI.1
  have hx1 : ((xb g k L t b : ℝ) + (g : ℝ) ^ t * (z : ℝ)) ^ k < y1 g k L t b := by
    exact_mod_cast hI.2
  obtain ⟨h0, h1⟩ := arch_linearisation KR hg hk hA hb hZ (Nat.cast_nonneg z) hx0 hx1
  have hneg : -1 / (g : ℝ) = -(1 / g) := by ring
  constructor <;> linarith

end PalindromicPowers

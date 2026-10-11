import PalindromicPowers.Frequencies

/-!
# HFF blocks 74–86: the phase curve, spacing, and the bound for E
-/

namespace PalindromicPowers

open Finset Real

variable {g k : ℕ}

/-- **[HFF 74] Definition (Phase curve).**  `h_d(T) = ℓ δ(T)/d`. -/
noncomputable def hd (g k L t s : ℕ) (ℓ : ℤ) (d : ℕ) (T : ℝ) : ℝ := ℓ * deltaT g k L t s T / d

/-- **[HFF 74]** `𝒯_d`, the integers `T ∈ [g^{t-1}, g^t)` with `|h_d(T)| ≥ 1/3`. -/
noncomputable def Tset (g k L t s : ℕ) (ℓ : ℤ) (d : ℕ) : Finset ℕ :=
  (Ico (g ^ (t - 1)) (g ^ t)).filter (fun T => 1 / 3 ≤ |hd g k L t s ℓ d T|)

/-- **[HFF 74]** `μ = |h_d'(g^t)| = (1 - 1/k)|h_d(g^t)|/g^t` (see Lemma 77). -/
noncomputable def muD (g k L t s : ℕ) (ℓ : ℤ) (d : ℕ) : ℝ :=
  (1 - 1 / (k : ℝ)) * |hd g k L t s ℓ d ((g : ℝ) ^ t)| / (g : ℝ) ^ t

/-- **[HFF 74]** `Δ = |h_d(g^t) - h_d(g^{t-1})|`, the length of `h_d([g^{t-1}, g^t])`. -/
noncomputable def DeltaD (g k L t s : ℕ) (ℓ : ℤ) (d : ℕ) : ℝ :=
  |hd g k L t s ℓ d ((g : ℝ) ^ t) - hd g k L t s ℓ d ((g : ℝ) ^ (t - 1))|

/-- **[HFF 75]** `ε_b = k g^{s-1}/(d_b Z)`. -/
noncomputable def epsB (g k L t s b : ℕ) : ℝ := k * (g : ℝ) ^ (s - 1) / (dB g k s b * Zt g k L t)

/-- Auxiliary for [HFF 75].  `Z(t) > 0` (also used in blocks 76–86). -/
private lemma sp_Zt_pos (hg : 2 ≤ g) (k L t : ℕ) : 0 < Zt g k L t := by
  unfold Zt Xr
  have : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  positivity

/-- Auxiliary for [HFF 75].  `d_b ≥ 1` (also used in blocks 76 and 84). -/
private lemma sp_dB_pos (hg : 2 ≤ g) (k s b : ℕ) : 0 < dB g k s b :=
  Nat.gcd_pos_of_pos_right _ (pow_pos (by omega) s)

/-- **[HFF 75] Lemma (Perturbation).**  If `b ∈ ℬ` and `|ℓ| δ_b > d_b/2`, then
`T_b ∈ 𝒯_{d_b}` and `|y_b - h_{d_b}(T_b)| ≤ ε_b`. -/
theorem perturbation (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) {L t s : ℕ} {ℓ : ℤ} {D : ℝ}
    {B : Finset ℕ} (hF : FreqSetting g k L t s ℓ D B) {b : ℕ} (hbB : b ∈ B)
    (hlarge : (dB g k s b : ℝ) / 2 < |(ℓ : ℝ)| * deltaB g k L t s b) :
    Tb g k t b ∈ Tset g k L t s ℓ (dB g k s b) ∧
      |yB g k L t s b ℓ - hd g k L t s ℓ (dB g k s b) (Tb g k t b)| ≤ epsB g k L t s b := by
  obtain ⟨hA, -, hℓ, -, -, hZ, hBn⟩ := hF
  obtain ⟨hb, -⟩ := hBn b hbB
  have hs1 : 1 ≤ s := hA.1
  have hst : s + 2 ≤ t := hA.2.1
  have htL : 2 * (t + s) ≤ L := hA.2.2
  -- Lemmas 36, 32, 40 and 39
  have hZb := (nodes_nonempty KR hg hk (by omega : 1 ≤ t) (by omega : t ≤ L) hZ hb).1
  obtain ⟨hT1, hT2⟩ := leading_digit hg (by omega : 1 ≤ t) hb
  obtain ⟨hδ1, hδ2⟩ := deltaB_near KR hg hk hA hb hZb
  have hTR1 : (g : ℝ) ^ (t - 1) ≤ (Tb g k t b : ℝ) := by exact_mod_cast hT1
  have hTR2 : (Tb g k t b : ℝ) ≤ (g : ℝ) ^ t := by exact_mod_cast hT2.le
  obtain ⟨hδlo, hδhi⟩ := (deltaT_formula hg hk hA).2 _ hTR1 hTR2
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hZ0 := sp_Zt_pos hg k L t
  have hdb : (0 : ℝ) < dB g k s b := by exact_mod_cast sp_dB_pos hg k s b
  have hδT : 0 < deltaT g k L t s (Tb g k t b) := lt_of_lt_of_le (by positivity) hδlo
  have hℓR : |(ℓ : ℝ)| ≤ (g : ℝ) ^ s := by
    rw [← Int.cast_abs]; exact_mod_cast hℓ.le
  -- `g^{1-t} = g/g^t ≤ 1/2`, as `t ≥ 3`
  have hε' : (g : ℝ) ^ ((1 : ℤ) - t) = g / (g : ℝ) ^ t := by
    rw [zpow_sub₀ hg0.ne', zpow_one, zpow_natCast]
  rw [hε'] at hδ2
  have hgt : 2 * (g : ℝ) ≤ (g : ℝ) ^ t := by
    have h2 : (g : ℝ) ^ 2 ≤ (g : ℝ) ^ t :=
      pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ g)) (by omega)
    have h3 : (2 : ℝ) ≤ g := by exact_mod_cast hg
    nlinarith
  have hε2 : (g : ℝ) / (g : ℝ) ^ t ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hε0 : 0 ≤ (g : ℝ) / (g : ℝ) ^ t := by positivity
  constructor
  · -- `|h| ≥ |ℓ| δ_b/((1 + g^{1-t}) d_b) > 1/(2 + 2g^{1-t}) ≥ 1/3`, and `g^{t-1} ≤ T_b < g^t`
    simp only [Tset, mem_filter, mem_Ico]
    refine ⟨⟨hT1, hT2⟩, ?_⟩
    unfold hd
    rw [abs_div, abs_mul, abs_of_pos hδT, abs_of_pos hdb, le_div_iff₀ hdb]
    have h1 : |(ℓ : ℝ)| * deltaB g k L t s b ≤
        |(ℓ : ℝ)| * ((1 + g / (g : ℝ) ^ t) * deltaT g k L t s (Tb g k t b)) :=
      mul_le_mul_of_nonneg_left hδ2 (abs_nonneg _)
    have h2 : 0 ≤ |(ℓ : ℝ)| * deltaT g k L t s (Tb g k t b) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hε2 h2]
  · -- `|y_b - h| ≤ |ℓ| g^{1-t} δ(T_b)/d_b ≤ g^s g^{1-t} kQ/(Z d_b) ≤ ε_b`, as `s ≤ t - 2`
    have hy : yB g k L t s b ℓ - hd g k L t s ℓ (dB g k s b) (Tb g k t b) =
        ℓ * (deltaB g k L t s b - deltaT g k L t s (Tb g k t b)) / dB g k s b := by
      unfold yB hd; ring
    have hkey : (g : ℝ) ^ s * (g / (g : ℝ) ^ t) * (g : ℝ) ^ s ≤ (g : ℝ) ^ (s - 1) := by
      have hnat : g ^ s * g * g ^ s ≤ g ^ (s - 1) * g ^ t := by
        rw [← pow_succ, ← pow_add, ← pow_add]
        exact Nat.pow_le_pow_right (by omega) (by omega)
      have hR : (g : ℝ) ^ s * g * (g : ℝ) ^ s ≤ (g : ℝ) ^ (s - 1) * (g : ℝ) ^ t := by
        exact_mod_cast hnat
      calc (g : ℝ) ^ s * (g / (g : ℝ) ^ t) * (g : ℝ) ^ s
          = (g : ℝ) ^ s * g * (g : ℝ) ^ s / (g : ℝ) ^ t := by ring
        _ ≤ (g : ℝ) ^ (s - 1) * (g : ℝ) ^ t / (g : ℝ) ^ t :=
          div_le_div_of_nonneg_right hR (by positivity)
        _ = (g : ℝ) ^ (s - 1) := by field_simp
    rw [hy, abs_div, abs_mul, abs_of_nonneg (sub_nonneg.mpr hδ1), abs_of_pos hdb]
    unfold epsB
    have h1 : deltaB g k L t s b - deltaT g k L t s (Tb g k t b) ≤
        g / (g : ℝ) ^ t * (k * (g : ℝ) ^ s / Zt g k L t) := by
      nlinarith [mul_le_mul_of_nonneg_left hδhi hε0]
    have h2 : |(ℓ : ℝ)| * (deltaB g k L t s b - deltaT g k L t s (Tb g k t b)) ≤
        (g : ℝ) ^ s * (g / (g : ℝ) ^ t * (k * (g : ℝ) ^ s / Zt g k L t)) :=
      mul_le_mul hℓR h1 (sub_nonneg.mpr hδ1) (by positivity)
    calc |(ℓ : ℝ)| * (deltaB g k L t s b - deltaT g k L t s (Tb g k t b)) / dB g k s b
        ≤ (g : ℝ) ^ s * (g / (g : ℝ) ^ t * (k * (g : ℝ) ^ s / Zt g k L t)) / dB g k s b :=
          div_le_div_of_nonneg_right h2 hdb.le
      _ = k * ((g : ℝ) ^ s * (g / (g : ℝ) ^ t) * (g : ℝ) ^ s) / (dB g k s b * Zt g k L t) := by
          ring
      _ ≤ k * (g : ℝ) ^ (s - 1) / (dB g k s b * Zt g k L t) := by gcongr

/-- **[HFF 76] Lemma (Replacement).**  In the setting of Lemma 75,
`Φ_b ≤ 5 min(d_b Z₊, Q/(2‖h_{d_b}(T_b)‖))`. -/
theorem replacement (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) {L t s : ℕ} {ℓ : ℤ} {D : ℝ}
    {B : Finset ℕ} (hF : FreqSetting g k L t s ℓ D B) {b : ℕ} (hbB : b ∈ B)
    (hlarge : (dB g k s b : ℝ) / 2 < |(ℓ : ℝ)| * deltaB g k L t s b) :
    PhiB g k L t s b ℓ ≤
      5 * minDiv (dB g k s b * Zplus g k L t) ((g : ℝ) ^ s)
        (2 * distZ (hd g k L t s ℓ (dB g k s b) (Tb g k t b))) := by
  obtain ⟨-, hclose⟩ := perturbation KR hg hk hF hbB hlarge
  obtain ⟨hA, -, -, -, -, hZ, -⟩ := hF
  have hs1 : 1 ≤ s := hA.1
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hg2 : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hZ0 := sp_Zt_pos hg k L t
  have hdb : (0 : ℝ) < dB g k s b := by exact_mod_cast sp_dB_pos hg k s b
  have hQ : (0 : ℝ) < (g : ℝ) ^ s := by positivity
  have hε0 : 0 < epsB g k L t s b := by unfold epsB; positivity
  -- `u = gZ/k ≥ 4`, as `Z ≥ 2k`
  have hu : 4 ≤ (g : ℝ) * Zt g k L t / k := by
    rw [le_div_iff₀ hk0]; nlinarith
  have hA0 : 0 ≤ (dB g k s b : ℝ) * Zplus g k L t := by unfold Zplus; positivity
  have hmin0 : 0 ≤ minDiv ((dB g k s b : ℝ) * Zplus g k L t) ((g : ℝ) ^ s)
      (2 * distZ (hd g k L t s ℓ (dB g k s b) (Tb g k t b))) :=
    minDiv_nonneg hA0 hQ.le (by have := distZ_nonneg (hd g k L t s ℓ (dB g k s b) (Tb g k t b)); positivity)
  unfold PhiB
  set h := hd g k L t s ℓ (dB g k s b) (Tb g k t b) with hh
  set y := yB g k L t s b ℓ with hy
  set A := (dB g k s b : ℝ) * Zplus g k L t with hAdef
  by_cases hcase : 2 * epsB g k L t s b ≤ distZ h
  · -- `‖h‖ ≥ 2ε_b`: then `‖y_b‖ ≥ ‖h‖/2`, which gives the factor `2`
    have htri : distZ h ≤ distZ y + epsB g k L t s b := by
      have h1 := KR.distZ_sub_le y (y - h)
      rw [sub_sub_cancel] at h1
      have h2 := distZ_le_abs (y - h)
      linarith
    have hx : 0 < distZ h := by linarith
    calc minDiv A ((g : ℝ) ^ s) (2 * distZ y) ≤ minDiv A ((g : ℝ) ^ s) (distZ h) :=
          minDiv_anti hQ.le (distZ_nonneg h) (by linarith)
      _ ≤ 2 * minDiv A ((g : ℝ) ^ s) (2 * distZ h) := by
          rw [minDiv_of_ne hx.ne', minDiv_of_ne (by positivity),
            mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
          refine min_le_min (by linarith) (le_of_eq ?_)
          field_simp
      _ ≤ 5 * minDiv A ((g : ℝ) ^ s) (2 * distZ h) := by linarith
  · -- `‖h‖ < 2ε_b`: then `Q/(2‖h‖) > Q/(4ε_b) = g d_b Z/(4k)` and `d_b Z₊ ≥ g d_b Z/k`
    replace hcase := not_le.mp hcase
    have hQeq : (g : ℝ) ^ s = g * (g : ℝ) ^ (s - 1) := by
      rw [← pow_succ']; congr 1; omega
    have e : (g : ℝ) * dB g k s b * Zt g k L t / (4 * k) =
        dB g k s b * ((g : ℝ) * Zt g k L t / k) / 4 := by ring
    have hlowA : (g : ℝ) * dB g k s b * Zt g k L t / (4 * k) ≤ A := by
      rw [hAdef, e]; unfold Zplus; nlinarith
    have hlow : (g : ℝ) * dB g k s b * Zt g k L t / (4 * k) ≤ minDiv A ((g : ℝ) ^ s) (2 * distZ h) := by
      by_cases h0 : distZ h = 0
      · rw [h0, mul_zero, minDiv_zero]; exact hlowA
      · have hx : 0 < distZ h := lt_of_le_of_ne (distZ_nonneg h) (Ne.symm h0)
        rw [minDiv_of_ne (by positivity)]
        refine le_min hlowA ?_
        have e2 : (g : ℝ) * dB g k s b * Zt g k L t / (4 * k) =
            (g : ℝ) ^ s / (4 * epsB g k L t s b) := by
          rw [hQeq]; unfold epsB; field_simp
        rw [e2]
        exact div_le_div_of_nonneg_left hQ.le (by positivity) (by linarith)
    calc minDiv A ((g : ℝ) ^ s) (2 * distZ y) ≤ A := minDiv_le_left _ _ _
      _ ≤ 5 * ((g : ℝ) * dB g k s b * Zt g k L t / (4 * k)) := by
          rw [hAdef, e]; unfold Zplus
          nlinarith [mul_le_mul_of_nonneg_left hu hdb.le]
      _ ≤ 5 * minDiv A ((g : ℝ) ^ s) (2 * distZ h) := by linarith

/-- Auxiliary for [HFF 77].  By Lemma 39, `h_d(T) = (ℓkQ/(dZ))(T/g^t)^{1-1/k}`, that is,
`h_d(T) = c T^{1-1/k}` for `T > 0`, with a constant `c`. -/
private lemma sp_hd_eq_rpow (hg : 2 ≤ g) (hk : 2 ≤ k) {L t s : ℕ} (hA : Admissible L t s)
    (ℓ : ℤ) (d : ℕ) :
    ∃ c : ℝ, ∀ T : ℝ, 0 < T → hd g k L t s ℓ d T = c * T ^ (1 - 1 / (k : ℝ)) := by
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  refine ⟨ℓ * (k * (g : ℝ) ^ s / Zt g k L t) / d / ((g : ℝ) ^ t) ^ (1 - 1 / (k : ℝ)),
    fun T hT => ?_⟩
  unfold hd
  rw [(deltaT_formula hg hk hA).1 T hT, Real.div_rpow hT.le (by positivity)]
  ring

/-- Auxiliary for [HFF 77].  The derivative of `c T^p` is `p (c T^p)/T`. -/
private lemma sp_hasDerivAt_mul_rpow (c p : ℝ) {T : ℝ} (hT : 0 < T) :
    HasDerivAt (fun x => c * x ^ p) (p * (c * T ^ p) / T) T := by
  have h := (Real.hasDerivAt_rpow_const (p := p) (Or.inl hT.ne')).const_mul c
  convert h using 1
  rw [Real.rpow_sub_one hT.ne']
  ring

/-- **[HFF 77] Lemma (Shape of h_d).**  On `[g^{t-1}, g^t]`: `|h_d|` is non-decreasing,
`h_d'(T) = (1-1/k) h_d(T)/T`, `|h_d'|` is non-increasing, and `|h_d'(T)| ≤ g |h_d'(g^t)| = gμ`. -/
theorem hd_shape (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) {L t s : ℕ} (hA : Admissible L t s)
    (ℓ : ℤ) {d : ℕ} (hd1 : 1 ≤ d) :
    MonotoneOn (fun T => |hd g k L t s ℓ d T|) (Set.Icc ((g : ℝ) ^ (t - 1)) ((g : ℝ) ^ t)) ∧
    (∀ T ∈ Set.Icc ((g : ℝ) ^ (t - 1)) ((g : ℝ) ^ t),
      HasDerivAt (hd g k L t s ℓ d) ((1 - 1 / (k : ℝ)) * hd g k L t s ℓ d T / T) T) ∧
    AntitoneOn (fun T => |(1 - 1 / (k : ℝ)) * hd g k L t s ℓ d T / T|)
      (Set.Icc ((g : ℝ) ^ (t - 1)) ((g : ℝ) ^ t)) ∧
    (∀ T ∈ Set.Icc ((g : ℝ) ^ (t - 1)) ((g : ℝ) ^ t),
      |(1 - 1 / (k : ℝ)) * hd g k L t s ℓ d T / T| ≤ g * muD g k L t s ℓ d) := by
  -- By Lemma 39, `h_d(T) = c T^p` with `p = 1 - 1/k`.
  obtain ⟨c, hc⟩ := sp_hd_eq_rpow hg hk hA ℓ d
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hp0 : 0 ≤ 1 - 1 / (k : ℝ) := by
    have : 1 / (k : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hk'
    linarith
  have hp1 : 1 - 1 / (k : ℝ) - 1 ≤ 0 := by
    have : 0 ≤ 1 / (k : ℝ) := by positivity
    linarith
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast (by omega : 1 ≤ g)
  have hg0 : (0 : ℝ) < g := by linarith
  have ht : 1 ≤ t := by have := hA.2.1; omega
  have hG' : (0 : ℝ) < (g : ℝ) ^ (t - 1) := by positivity
  have hpos : ∀ T ∈ Set.Icc ((g : ℝ) ^ (t - 1)) ((g : ℝ) ^ t), 0 < T :=
    fun T hT => lt_of_lt_of_le hG' hT.1
  -- `|h_d'(T)| = p |c| T^{p-1} = p |c| T^{-1/k}`
  have hder_abs : ∀ T : ℝ, 0 < T → |(1 - 1 / (k : ℝ)) * hd g k L t s ℓ d T / T| =
      (1 - 1 / (k : ℝ)) * |c| * T ^ (1 - 1 / (k : ℝ) - 1) := by
    intro T hT
    rw [hc T hT, Real.rpow_sub_one hT.ne', abs_div, abs_mul, abs_mul, abs_of_nonneg hp0,
      abs_of_pos (Real.rpow_pos_of_pos hT _), abs_of_pos hT]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    dsimp only
    rw [hc a (hpos a ha), hc b (hpos b hb), abs_mul, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (hpos a ha).le _), abs_of_nonneg (Real.rpow_nonneg (hpos b hb).le _)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hpos a ha).le hab hp0) (abs_nonneg c)
  · intro T hT
    have hT0 := hpos T hT
    have hev : hd g k L t s ℓ d =ᶠ[nhds T] fun x => c * x ^ (1 - 1 / (k : ℝ)) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hT0) (fun x hx => hc x hx)
    have h := (sp_hasDerivAt_mul_rpow c (1 - 1 / (k : ℝ)) hT0).congr_of_eventuallyEq hev
    rwa [← hc T hT0] at h
  · intro a ha b hb hab
    dsimp only
    rw [hder_abs a (hpos a ha), hder_abs b (hpos b hb)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (hpos a ha) hab hp1)
      (mul_nonneg hp0 (abs_nonneg c))
  · intro T hT
    have hT0 := hpos T hT
    have hGt : (g : ℝ) ^ t = g * (g : ℝ) ^ (t - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hmu : muD g k L t s ℓ d = (1 - 1 / (k : ℝ)) * |c| * ((g : ℝ) ^ t) ^ (1 - 1 / (k : ℝ) - 1) := by
      rw [← hder_abs ((g : ℝ) ^ t) (by positivity)]
      unfold muD
      rw [abs_div, abs_mul, abs_of_nonneg hp0, abs_of_pos (by positivity : (0 : ℝ) < (g : ℝ) ^ t)]
    rw [hder_abs T hT0, hmu]
    -- `(g^t/T)^{1/k} ≤ g`
    have h1 : T ^ (1 - 1 / (k : ℝ) - 1) ≤ ((g : ℝ) ^ (t - 1)) ^ (1 - 1 / (k : ℝ) - 1) :=
      Real.rpow_le_rpow_of_nonpos hG' hT.1 hp1
    have h2 : ((g : ℝ) ^ (t - 1)) ^ (1 - 1 / (k : ℝ) - 1) ≤
        g * ((g : ℝ) ^ t) ^ (1 - 1 / (k : ℝ) - 1) := by
      rw [hGt, Real.mul_rpow hg0.le hG'.le, ← mul_assoc, Real.rpow_sub_one hg0.ne',
        mul_div_cancel₀ _ hg0.ne']
      exact le_mul_of_one_le_left (by positivity) (Real.one_le_rpow hg1 hp0)
    calc (1 - 1 / (k : ℝ)) * |c| * T ^ (1 - 1 / (k : ℝ) - 1)
        ≤ (1 - 1 / (k : ℝ)) * |c| * (g * ((g : ℝ) ^ t) ^ (1 - 1 / (k : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (mul_nonneg hp0 (abs_nonneg c))
      _ = g * ((1 - 1 / (k : ℝ)) * |c| * ((g : ℝ) ^ t) ^ (1 - 1 / (k : ℝ) - 1)) := by ring

/-- Auxiliary for [HFF 78] (also used for [HFF 79]).  The mean value theorem for `h_d` on a
subinterval `[a, b]` of `[g^{t-1}, g^t]`: `h_d(b) - h_d(a) = h_d'(c)(b - a)`. -/
private lemma sp_hd_mvt (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) {L t s : ℕ}
    (hA : Admissible L t s) (ℓ : ℤ) {d : ℕ} (hd1 : 1 ≤ d) {a b : ℝ} (hab : a < b)
    (ha : (g : ℝ) ^ (t - 1) ≤ a) (hb : b ≤ (g : ℝ) ^ t) :
    ∃ c ∈ Set.Icc ((g : ℝ) ^ (t - 1)) ((g : ℝ) ^ t),
      hd g k L t s ℓ d b - hd g k L t s ℓ d a =
        (1 - 1 / (k : ℝ)) * hd g k L t s ℓ d c / c * (b - a) := by
  have hder := (hd_shape KR hg hk hA ℓ hd1).2.1
  have hsub : Set.Icc a b ⊆ Set.Icc ((g : ℝ) ^ (t - 1)) ((g : ℝ) ^ t) := Set.Icc_subset_Icc ha hb
  obtain ⟨c, hc, hcd⟩ := KR.mvt (hd g k L t s ℓ d) a b hab
    (fun x hx => (hder x (hsub hx)).continuousAt.continuousWithinAt)
    (fun x hx => (hder x (hsub (Set.Ioo_subset_Icc_self hx))).differentiableAt.differentiableWithinAt)
  have hcI := hsub (Set.Ioo_subset_Icc_self hc)
  refine ⟨c, hcI, ?_⟩
  rw [(hder c hcI).deriv] at hcd
  rw [hcd, div_mul_cancel₀ _ (sub_pos.mpr hab).ne']

/-- **[HFF 78] Lemma (Gaps).**  If `𝒯_d ≠ ∅` then `μ ≥ 1/(6g^t)`, and
`|h_d(T') - h_d(T)| ≥ μ` for distinct `T, T' ∈ 𝒯_d`. -/
theorem gaps (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) {L t s : ℕ} (hA : Admissible L t s)
    (ℓ : ℤ) {d : ℕ} (hd1 : 1 ≤ d) (hne : (Tset g k L t s ℓ d).Nonempty) :
    1 / (6 * (g : ℝ) ^ t) ≤ muD g k L t s ℓ d ∧
    ∀ T ∈ Tset g k L t s ℓ d, ∀ T' ∈ Tset g k L t s ℓ d, T ≠ T' →
      muD g k L t s ℓ d ≤ |hd g k L t s ℓ d T' - hd g k L t s ℓ d T| := by
  obtain ⟨hmono, -, hanti, -⟩ := hd_shape KR hg hk hA ℓ hd1
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : 1 / 2 ≤ 1 - 1 / (k : ℝ) := by
    have : 1 / (k : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hk'
    linarith
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hGpos : (0 : ℝ) < (g : ℝ) ^ t := by positivity
  have hGle : (g : ℝ) ^ (t - 1) ≤ (g : ℝ) ^ t :=
    pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ g)) (Nat.sub_le t 1)
  have htop : (g : ℝ) ^ t ∈ Set.Icc ((g : ℝ) ^ (t - 1)) ((g : ℝ) ^ t) := ⟨hGle, le_rfl⟩
  have hmem : ∀ T ∈ Tset g k L t s ℓ d,
      (T : ℝ) ∈ Set.Icc ((g : ℝ) ^ (t - 1)) ((g : ℝ) ^ t) ∧ 1 / 3 ≤ |hd g k L t s ℓ d T| := by
    intro T hT
    simp only [Tset, mem_filter, mem_Ico] at hT
    obtain ⟨⟨h1, h2⟩, h3⟩ := hT
    exact ⟨⟨by exact_mod_cast h1, by exact_mod_cast h2.le⟩, h3⟩
  -- `μ = |h_d'(g^t)|`
  have hmu : muD g k L t s ℓ d =
      |(1 - 1 / (k : ℝ)) * hd g k L t s ℓ d ((g : ℝ) ^ t) / (g : ℝ) ^ t| := by
    unfold muD
    rw [abs_div, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - 1 / (k : ℝ)), abs_of_pos hGpos]
  constructor
  · -- `|h_d(g^t)| ≥ |h_d(T)| ≥ 1/3`, so `μ ≥ 1/(6g^t)`
    obtain ⟨T, hT⟩ := hne
    obtain ⟨hTI, hT3⟩ := hmem T hT
    have h1 : 1 / 3 ≤ |hd g k L t s ℓ d ((g : ℝ) ^ t)| := hT3.trans (hmono hTI htop hTI.2)
    have h6 : 1 / 6 ≤ (1 - 1 / (k : ℝ)) * |hd g k L t s ℓ d ((g : ℝ) ^ t)| := by
      have := mul_le_mul hp h1 (by norm_num) (by linarith)
      linarith
    unfold muD
    rw [show 1 / (6 * (g : ℝ) ^ t) = (1 / 6) / (g : ℝ) ^ t by rw [div_div]]
    exact div_le_div_of_nonneg_right h6 hGpos.le
  · -- `|h_d'| ≥ μ` on `[g^{t-1}, g^t]` and `|T' - T| ≥ 1`; mean value theorem
    have key : ∀ a ∈ Tset g k L t s ℓ d, ∀ b ∈ Tset g k L t s ℓ d, a < b →
        muD g k L t s ℓ d ≤ |hd g k L t s ℓ d b - hd g k L t s ℓ d a| := by
      intro a ha b hb hab
      have ha' := (hmem a ha).1
      have hb' := (hmem b hb).1
      have hab' : (a : ℝ) < b := by exact_mod_cast hab
      have hab1 : (1 : ℝ) ≤ (b : ℝ) - a := by
        have h1 : a + 1 ≤ b := hab
        have h2 : (a : ℝ) + 1 ≤ b := by exact_mod_cast h1
        linarith
      obtain ⟨c, hcI, hc⟩ := sp_hd_mvt KR hg hk hA ℓ hd1 hab' ha'.1 hb'.2
      rw [hc, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < b - a), hmu]
      calc |(1 - 1 / (k : ℝ)) * hd g k L t s ℓ d ((g : ℝ) ^ t) / (g : ℝ) ^ t|
          ≤ |(1 - 1 / (k : ℝ)) * hd g k L t s ℓ d c / c| := hanti hcI htop hcI.2
        _ = |(1 - 1 / (k : ℝ)) * hd g k L t s ℓ d c / c| * 1 := (mul_one _).symm
        _ ≤ |(1 - 1 / (k : ℝ)) * hd g k L t s ℓ d c / c| * ((b : ℝ) - a) :=
          mul_le_mul_of_nonneg_left hab1 (abs_nonneg _)
    intro T hT T' hT' hTT'
    rcases lt_or_gt_of_ne hTT' with h | h
    · exact key T hT T' hT' h
    · rw [abs_sub_comm]; exact key T' hT' T hT h

/-- **[HFF 79] Lemma (Range).**  If `𝒯_d ≠ ∅`, then `h_d(𝒯_d)` lies in the interval with
endpoints `h_d(g^{t-1})`, `h_d(g^t)`, of length `Δ`, where `Δ ≤ g^{t+1} μ` and
`Δ ≤ k g^{2s}/(dZ)`. -/
theorem range_bound (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) {L t s : ℕ}
    (hA : Admissible L t s) {ℓ : ℤ} (hℓ : |ℓ| < (g : ℤ) ^ s) {d : ℕ} (hd1 : 1 ≤ d)
    (hne : (Tset g k L t s ℓ d).Nonempty) :
    (∀ T ∈ Tset g k L t s ℓ d,
      min (hd g k L t s ℓ d ((g : ℝ) ^ (t - 1))) (hd g k L t s ℓ d ((g : ℝ) ^ t)) ≤ hd g k L t s ℓ d T ∧
      hd g k L t s ℓ d T ≤ max (hd g k L t s ℓ d ((g : ℝ) ^ (t - 1))) (hd g k L t s ℓ d ((g : ℝ) ^ t))) ∧
    DeltaD g k L t s ℓ d ≤ (g : ℝ) ^ (t + 1) * muD g k L t s ℓ d ∧
    DeltaD g k L t s ℓ d ≤ k * (g : ℝ) ^ (2 * s) / (d * Zt g k L t) := by
  obtain ⟨-, -, -, hbound⟩ := hd_shape KR hg hk hA ℓ hd1
  obtain ⟨hmu, -⟩ := gaps KR hg hk hA ℓ hd1 hne
  obtain ⟨c, hc⟩ := sp_hd_eq_rpow hg hk hA ℓ d
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hp0 : 0 ≤ 1 - 1 / (k : ℝ) := by
    have : 1 / (k : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hk'
    linarith
  have hg1 : (1 : ℝ) < g := by exact_mod_cast (by omega : 1 < g)
  have hg0 : (0 : ℝ) < g := by linarith
  have ht : 1 ≤ t := by have := hA.2.1; omega
  have hG'0 : (0 : ℝ) < (g : ℝ) ^ (t - 1) := by positivity
  have hGG : (g : ℝ) ^ (t - 1) < (g : ℝ) ^ t := pow_lt_pow_right₀ hg1 (by omega)
  have hG0 : (0 : ℝ) < (g : ℝ) ^ t := by positivity
  have hpow_le : ((g : ℝ) ^ (t - 1)) ^ (1 - 1 / (k : ℝ)) ≤ ((g : ℝ) ^ t) ^ (1 - 1 / (k : ℝ)) :=
    Real.rpow_le_rpow hG'0.le hGG.le hp0
  refine ⟨?_, ?_, ?_⟩
  · -- `h_d = c T^p` is monotone, so `h_d(𝒯_d)` lies between `h_d(g^{t-1})` and `h_d(g^t)`
    intro T hT
    simp only [Tset, mem_filter, mem_Ico] at hT
    have hT1 : (g : ℝ) ^ (t - 1) ≤ T := by exact_mod_cast hT.1.1
    have hT2 : (T : ℝ) ≤ (g : ℝ) ^ t := by exact_mod_cast hT.1.2.le
    have hT0 : (0 : ℝ) < T := lt_of_lt_of_le hG'0 hT1
    rw [hc _ hT0, hc _ hG'0, hc _ hG0]
    have h1 := Real.rpow_le_rpow hG'0.le hT1 hp0
    have h2 := Real.rpow_le_rpow hT0.le hT2 hp0
    rcases le_total 0 c with hc0 | hc0
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left h1 hc0),
        (mul_le_mul_of_nonneg_left h2 hc0).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left h2 hc0),
        (mul_le_mul_of_nonpos_left h1 hc0).trans (le_max_left _ _)⟩
  · -- Lemma 77 and the mean value theorem: `Δ ≤ g^t · gμ`
    obtain ⟨x, hxI, hx⟩ := sp_hd_mvt KR hg hk hA ℓ hd1 hGG le_rfl le_rfl
    unfold DeltaD
    rw [hx, abs_mul, abs_of_pos (sub_pos.mpr hGG)]
    have hμ0 : 0 ≤ muD g k L t s ℓ d := le_trans (by positivity) hmu
    calc |(1 - 1 / (k : ℝ)) * hd g k L t s ℓ d x / x| * ((g : ℝ) ^ t - (g : ℝ) ^ (t - 1))
        ≤ (g * muD g k L t s ℓ d) * (g : ℝ) ^ t :=
          mul_le_mul (hbound x hxI) (by linarith) (by linarith) (by positivity)
      _ = (g : ℝ) ^ (t + 1) * muD g k L t s ℓ d := by ring
  · -- `h_d` has constant sign and `|h_d| ≤ |ℓ| kQ/(dZ) ≤ k g^{2s}/(dZ)` (Lemma 39)
    have hZ0 := sp_Zt_pos hg k L t
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    obtain ⟨-, hδ⟩ := deltaT_formula hg hk hA
    obtain ⟨hδlo, hδhi⟩ := hδ ((g : ℝ) ^ t) hGG.le le_rfl
    have hδ0 : 0 ≤ deltaT g k L t s ((g : ℝ) ^ t) := le_trans (by positivity) hδlo
    have hℓR : |(ℓ : ℝ)| ≤ (g : ℝ) ^ s := by rw [← Int.cast_abs]; exact_mod_cast hℓ.le
    have hΔle : DeltaD g k L t s ℓ d ≤ |hd g k L t s ℓ d ((g : ℝ) ^ t)| := by
      unfold DeltaD
      rw [hc _ hG0, hc _ hG'0, ← mul_sub, abs_mul, abs_mul,
        abs_of_nonneg (sub_nonneg.mpr hpow_le), abs_of_nonneg (Real.rpow_nonneg hG0.le _)]
      exact mul_le_mul_of_nonneg_left
        (by linarith [Real.rpow_nonneg hG'0.le (1 - 1 / (k : ℝ))]) (abs_nonneg c)
    refine hΔle.trans ?_
    unfold hd
    rw [abs_div, abs_mul, abs_of_nonneg hδ0, abs_of_pos hd0]
    calc |(ℓ : ℝ)| * deltaT g k L t s ((g : ℝ) ^ t) / d
        ≤ (g : ℝ) ^ s * (k * (g : ℝ) ^ s / Zt g k L t) / d :=
          div_le_div_of_nonneg_right (mul_le_mul hℓR hδhi hδ0 (by positivity)) hd0.le
      _ = k * (g : ℝ) ^ (2 * s) / (d * Zt g k L t) := by ring

/-- Auxiliary for [HFF 80].  If `|y - n| ≥ jμ`, then `min(A, H/|y-n|) ≤ c_j`, where `c_0 = A`
and `c_j = H/(jμ)` for `j ≥ 1`. -/
private lemma sp_minDiv_le_c {A H μ x : ℝ} (hH : 0 < H) (hμ : 0 < μ) (j : ℕ) (hjx : j * μ ≤ x) :
    minDiv A H x ≤ if j = 0 then A else H / (j * μ) := by
  split_ifs with hj
  · exact minDiv_le_left A H x
  · have hj' : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hj
    have hjpos : 0 < (j : ℝ) * μ := mul_pos hj' hμ
    have hxpos : 0 < x := lt_of_lt_of_le hjpos hjx
    exact (minDiv_le_div hxpos.ne').trans (div_le_div_of_nonneg_left hH.le hjpos hjx)

/-- Auxiliary for [HFF 80].  `∑_{1 ≤ j ≤ J'} 1/j ≤ 1 + log(1 + 1/μ)` when `J' ≤ 1/(2μ)`
(Lemma 7). -/
private lemma sp_harmonic (KR : KnownResults) {μ : ℝ} (hμ : 0 < μ) (J' : ℕ)
    (hJ' : (J' : ℝ) ≤ 1 / (2 * μ)) :
    ∑ j ∈ range J', (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 + Real.log (1 + 1 / μ) := by
  have hμ1 : 0 < 1 / μ := by positivity
  have hlog : 0 ≤ Real.log (1 + 1 / μ) := Real.log_nonneg (by linarith)
  rcases Nat.eq_zero_or_pos J' with h0 | hpos
  · subst h0; simp only [range_zero, sum_empty]; linarith
  · have h1 : ∑ j ∈ range J', (1 : ℝ) / ((j : ℝ) + 1) = ∑ j ∈ Icc 1 J', (1 : ℝ) / j := by
      apply sum_nbij' (· + 1) (· - 1)
      · intro a ha; simp only [mem_range, mem_Icc] at ha ⊢; omega
      · intro a ha; simp only [mem_range, mem_Icc] at ha ⊢; omega
      · intro a _; simp
      · intro a ha; simp only [mem_Icc] at ha; omega
      · intro a _; push_cast; ring
    rw [h1]
    refine (harmonic_le KR J' hpos).trans ?_
    have hJpos : (0 : ℝ) < J' := by exact_mod_cast hpos
    have h2 : 1 / (2 * μ) ≤ 1 / μ := one_div_le_one_div_of_le hμ (by linarith)
    linarith [Real.log_le_log hJpos (by linarith : (J' : ℝ) ≤ 1 + 1 / μ)]

/-- **[HFF 80] Lemma (Spacing near one integer).**  Let `μ > 0`, `m ≥ 1`, `A, H > 0`, `n ∈ ℤ`,
and let reals `y_i ∈ (n - 1/2, n + 1/2]` with weights `w_i ∈ ℕ` be such that every half-open
interval of length `μ` carries total weight at most `m`.  Then
`∑ w_i min(A, H/|y_i - n|) ≤ 2mA + 2m (H/μ)(1 + log(1 + 1/μ))`. -/
theorem spacing_one {ι : Type*} (KR : KnownResults) (S : Finset ι) (y : ι → ℝ) (w : ι → ℕ)
    {μ m A H : ℝ} (n : ℤ) (hμ : 0 < μ) (hm : 1 ≤ m) (hA : 0 < A) (hH : 0 < H)
    (hy : ∀ i ∈ S, (n : ℝ) - 1 / 2 < y i ∧ y i ≤ n + 1 / 2)
    (hsp : ∀ a : ℝ, (∑ i ∈ S.filter (fun i => a ≤ y i ∧ y i < a + μ), (w i : ℝ)) ≤ m) :
    ∑ i ∈ S, (w i : ℝ) * minDiv A H |y i - n| ≤
      2 * m * A + 2 * m * (H / μ) * (1 + Real.log (1 + 1 / μ)) := by
  classical
  -- `J = J' + 1` with `J' = ⌊1/(2μ)⌋`
  set J' : ℕ := ⌊1 / (2 * μ)⌋₊ with hJ'
  have hJ'le : (J' : ℝ) ≤ 1 / (2 * μ) := Nat.floor_le (by positivity)
  set c : ℕ → ℝ := fun j => if j = 0 then A else H / (j * μ) with hc
  have hc0 : ∀ j, 0 ≤ c j := by
    intro j; simp only [hc]; split_ifs
    · exact hA.le
    · positivity
  -- Each `y_i` lies in one of the intervals `[n + jμ, n + (j+1)μ)`, `[n - (j+1)μ, n - jμ)`,
  -- `0 ≤ j < J`, and then `|y_i - n| ≥ jμ`.
  have hpt : ∀ i ∈ S, minDiv A H |y i - n| ≤ ∑ j ∈ range (J' + 1),
      ((if (n : ℝ) + j * μ ≤ y i ∧ y i < (n : ℝ) + j * μ + μ then c j else 0) +
       (if (n : ℝ) - (j + 1) * μ ≤ y i ∧ y i < (n : ℝ) - (j + 1) * μ + μ then c j else 0)) := by
    intro i hi
    obtain ⟨hy1, hy2⟩ := hy i hi
    have hterm : ∀ j ∈ range (J' + 1), 0 ≤
        ((if (n : ℝ) + j * μ ≤ y i ∧ y i < (n : ℝ) + j * μ + μ then c j else 0) +
         (if (n : ℝ) - (j + 1) * μ ≤ y i ∧ y i < (n : ℝ) - (j + 1) * μ + μ then c j else 0)) := by
      intro j _; have := hc0 j; split_ifs <;> linarith
    have hf1 : (⌊(y i - n) / μ⌋ : ℝ) * μ ≤ y i - n := by
      have := Int.floor_le ((y i - n) / μ); rwa [le_div_iff₀ hμ] at this
    have hf2 : y i - n < ((⌊(y i - n) / μ⌋ : ℝ) + 1) * μ := by
      have := Int.lt_floor_add_one ((y i - n) / μ); rwa [div_lt_iff₀ hμ] at this
    rcases le_or_gt 0 ⌊(y i - n) / μ⌋ with hj0 | hj0
    · -- `y_i ≥ n`: the interval `[n + jμ, n + (j+1)μ)` with `j = ⌊(y_i - n)/μ⌋`
      obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = ⌊(y i - n) / μ⌋ := ⟨_, Int.toNat_of_nonneg hj0⟩
      have hjR : ((⌊(y i - n) / μ⌋ : ℤ) : ℝ) = (j : ℝ) := by rw [← hj]; norm_cast
      rw [hjR] at hf1 hf2
      have hjμ : 0 ≤ (j : ℝ) * μ := by positivity
      have hjJ : j ∈ range (J' + 1) := by
        rw [mem_range, Nat.lt_succ_iff]
        apply Nat.le_floor
        rw [le_div_iff₀ (by positivity)]
        linarith
      have hP : (n : ℝ) + j * μ ≤ y i ∧ y i < (n : ℝ) + j * μ + μ :=
        ⟨by linarith, by linarith⟩
      calc minDiv A H |y i - n| ≤ c j := by
            apply sp_minDiv_le_c hH hμ j
            rw [abs_of_nonneg (by linarith)]; exact hf1
        _ ≤ _ := by rw [ite_eq_left hP]; have := hc0 j; split_ifs <;> linarith
        _ ≤ _ := single_le_sum hterm hjJ
    · -- `y_i < n`: the interval `[n - (j+1)μ, n - jμ)` with `j = -⌊(y_i - n)/μ⌋ - 1`
      obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = -⌊(y i - n) / μ⌋ - 1 :=
        ⟨_, Int.toNat_of_nonneg (by omega)⟩
      have hjR : ((⌊(y i - n) / μ⌋ : ℤ) : ℝ) = -(j : ℝ) - 1 := by
        have : ((j : ℤ) : ℝ) = (((-⌊(y i - n) / μ⌋ - 1 : ℤ)) : ℝ) := by rw [hj]
        push_cast at this; linarith
      rw [hjR] at hf1 hf2
      have hjμ : 0 ≤ (j : ℝ) * μ := by positivity
      have hjJ : j ∈ range (J' + 1) := by
        rw [mem_range, Nat.lt_succ_iff]
        apply Nat.le_floor
        rw [le_div_iff₀ (by positivity)]
        linarith
      have hM : (n : ℝ) - (j + 1) * μ ≤ y i ∧ y i < (n : ℝ) - (j + 1) * μ + μ :=
        ⟨by linarith, by linarith⟩
      calc minDiv A H |y i - n| ≤ c j := by
            apply sp_minDiv_le_c hH hμ j
            rw [abs_of_neg (by linarith)]; linarith
        _ ≤ _ := by rw [ite_eq_left hM]; have := hc0 j; split_ifs <;> linarith
        _ ≤ _ := single_le_sum hterm hjJ
  -- Each interval carries weight at most `m`; sum over the intervals.
  have hm0 : 0 ≤ m := by linarith
  calc ∑ i ∈ S, (w i : ℝ) * minDiv A H |y i - n|
      ≤ ∑ i ∈ S, (w i : ℝ) * ∑ j ∈ range (J' + 1),
          ((if (n : ℝ) + j * μ ≤ y i ∧ y i < (n : ℝ) + j * μ + μ then c j else 0) +
           (if (n : ℝ) - (j + 1) * μ ≤ y i ∧ y i < (n : ℝ) - (j + 1) * μ + μ then c j else 0)) :=
        sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hpt i hi) (Nat.cast_nonneg _)
    _ = ∑ j ∈ range (J' + 1), c j *
          ((∑ i ∈ S.filter (fun i => (n : ℝ) + j * μ ≤ y i ∧ y i < (n : ℝ) + j * μ + μ), (w i : ℝ)) +
           (∑ i ∈ S.filter (fun i => (n : ℝ) - (j + 1) * μ ≤ y i ∧
              y i < (n : ℝ) - (j + 1) * μ + μ), (w i : ℝ))) := by
        simp_rw [mul_sum]
        rw [sum_comm (s := S)]
        refine sum_congr rfl fun j _ => ?_
        rw [sum_filter, sum_filter, mul_add, mul_sum, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun i _ => ?_
        split_ifs <;> ring
    _ ≤ ∑ j ∈ range (J' + 1), c j * (m + m) :=
        sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (add_le_add (hsp _) (hsp _)) (hc0 j)
    _ = 2 * m * (A + H / μ * ∑ j ∈ range J', (1 : ℝ) / ((j : ℝ) + 1)) := by
        rw [← sum_mul, sum_range_succ', mul_sum]
        have e1 : c 0 = A := by simp [hc]
        have e2 : ∀ j : ℕ, c (j + 1) = H / μ * (1 / ((j : ℝ) + 1)) := by
          intro j
          have hcj : c (j + 1) = H / (((j + 1 : ℕ) : ℝ) * μ) := by simp [hc]
          rw [hcj]; push_cast; field_simp
        rw [e1, sum_congr rfl fun j _ => e2 j]
        ring
    _ ≤ 2 * m * A + 2 * m * (H / μ) * (1 + Real.log (1 + 1 / μ)) := by
        have hh := sp_harmonic KR hμ J' hJ'le
        have h2 : 0 ≤ 2 * m * (H / μ) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hh h2]

/-- **[HFF 81] Lemma (Spacing sum).**  Let `μ > 0`, `m ≥ 1`, `A, H > 0`, and let weighted reals
`y_i` lie in an interval of length `Δ`, every half-open interval of length `μ` carrying total
weight at most `m`.  Then `∑ w_i min(A, H/‖y_i‖) ≤ m(Δ+2)(2A + 2(H/μ)(1 + log(1 + 1/μ)))`. -/
theorem spacing_sum {ι : Type*} (KR : KnownResults) (S : Finset ι) (y : ι → ℝ) (w : ι → ℕ)
    {μ m A H Δ : ℝ} (a₀ : ℝ) (hμ : 0 < μ) (hm : 1 ≤ m) (hA : 0 < A) (hH : 0 < H) (hΔ : 0 ≤ Δ)
    (hy : ∀ i ∈ S, a₀ ≤ y i ∧ y i ≤ a₀ + Δ)
    (hsp : ∀ a : ℝ, (∑ i ∈ S.filter (fun i => a ≤ y i ∧ y i < a + μ), (w i : ℝ)) ≤ m) :
    ∑ i ∈ S, (w i : ℝ) * minDiv A H (distZ (y i)) ≤
      m * (Δ + 2) * (2 * A + 2 * (H / μ) * (1 + Real.log (1 + 1 / μ))) := by
  classical
  have hm0 : 0 ≤ m := by linarith
  have hlog : 0 ≤ Real.log (1 + 1 / μ) :=
    Real.log_nonneg (by have : 0 < 1 / μ := by positivity
                        linarith)
  have hB0 : 0 ≤ 2 * m * A + 2 * m * (H / μ) * (1 + Real.log (1 + 1 / μ)) := by positivity
  -- `y_i ∈ (n_i - 1/2, n_i + 1/2]` for `n_i = ⌈y_i - 1/2⌉`, and then `‖y_i‖ = |y_i - n_i|`
  have hnn : ∀ i, ((⌈y i - 1 / 2⌉ : ℤ) : ℝ) - 1 / 2 < y i ∧ y i ≤ ((⌈y i - 1 / 2⌉ : ℤ) : ℝ) + 1 / 2 := by
    intro i
    have h1 := Int.ceil_lt_add_one (y i - 1 / 2)
    have h2 := Int.le_ceil (y i - 1 / 2)
    constructor <;> linarith
  -- the `n_i` lie in `[⌈a₀ - 1/2⌉, ⌈a₀ + Δ - 1/2⌉]`, a set of at most `Δ + 2` integers
  have hmaps : ∀ i ∈ S, ⌈y i - 1 / 2⌉ ∈ Icc ⌈a₀ - 1 / 2⌉ ⌈a₀ + Δ - 1 / 2⌉ := by
    intro i hi
    obtain ⟨h1, h2⟩ := hy i hi
    rw [mem_Icc]
    exact ⟨Int.ceil_mono (by linarith), Int.ceil_mono (by linarith)⟩
  have hcard : (((Icc ⌈a₀ - 1 / 2⌉ ⌈a₀ + Δ - 1 / 2⌉).card : ℕ) : ℝ) ≤ Δ + 2 := by
    rw [Int.card_Icc]
    have h1 := Int.ceil_lt_add_one (a₀ + Δ - 1 / 2)
    have h2 := Int.le_ceil (a₀ - 1 / 2)
    rcases le_or_gt 0 (⌈a₀ + Δ - 1 / 2⌉ + 1 - ⌈a₀ - 1 / 2⌉) with h | h
    · have e : (((⌈a₀ + Δ - 1 / 2⌉ + 1 - ⌈a₀ - 1 / 2⌉).toNat : ℕ) : ℝ) =
          ((⌈a₀ + Δ - 1 / 2⌉ + 1 - ⌈a₀ - 1 / 2⌉ : ℤ) : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg h
      rw [e]; push_cast; linarith
    · rw [Int.toNat_of_nonpos h.le]; simp only [Nat.cast_zero]; linarith
  rw [← sum_fiberwise_of_maps_to hmaps]
  calc ∑ n ∈ Icc ⌈a₀ - 1 / 2⌉ ⌈a₀ + Δ - 1 / 2⌉, ∑ i ∈ S with ⌈y i - 1 / 2⌉ = n,
        (w i : ℝ) * minDiv A H (distZ (y i))
      ≤ ∑ n ∈ Icc ⌈a₀ - 1 / 2⌉ ⌈a₀ + Δ - 1 / 2⌉,
          (2 * m * A + 2 * m * (H / μ) * (1 + Real.log (1 + 1 / μ))) := by
        refine sum_le_sum fun n _ => ?_
        have e : ∑ i ∈ S with ⌈y i - 1 / 2⌉ = n, (w i : ℝ) * minDiv A H (distZ (y i)) =
            ∑ i ∈ S with ⌈y i - 1 / 2⌉ = n, (w i : ℝ) * minDiv A H |y i - n| := by
          refine sum_congr rfl fun i hi => ?_
          have hin := (mem_filter.mp hi).2
          obtain ⟨h1, h2⟩ := hnn i
          rw [hin] at h1 h2
          rw [distZ_eq_abs_sub_of_mem n h1 h2]
        rw [e]
        -- Lemma 80 for each `n`
        refine spacing_one KR _ y w n hμ hm hA hH (fun i hi => ?_) (fun a => ?_)
        · have := hnn i; rw [(mem_filter.mp hi).2] at this; exact this
        · refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.cast_nonneg _)) (hsp a)
          intro i hi
          simp only [mem_filter] at hi ⊢
          exact ⟨hi.1.1, hi.2⟩
    _ = ((Icc ⌈a₀ - 1 / 2⌉ ⌈a₀ + Δ - 1 / 2⌉).card : ℝ) *
          (2 * m * A + 2 * m * (H / μ) * (1 + Real.log (1 + 1 / μ))) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (Δ + 2) * (2 * m * A + 2 * m * (H / μ) * (1 + Real.log (1 + 1 / μ))) :=
        mul_le_mul_of_nonneg_right hcard hB0
    _ = m * (Δ + 2) * (2 * A + 2 * (H / μ) * (1 + Real.log (1 + 1 / μ))) := by ring

/-- **[HFF 82] Lemma (Count over T).**  Let `d ≥ 1` with `𝒯_d ≠ ∅`, `κ ≥ 1`, and integers
`0 ≤ N_T ≤ κ` for `T ∈ 𝒯_d`.  Then
`∑_{T∈𝒯_d} N_T min(dZ₊, Q/(2‖h_d(T)‖)) ≤ κ(Δ+2)(2dZ₊ + (Q/μ)Λ)`. -/
theorem count_over_T (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) {L t s : ℕ}
    (hA : Admissible L t s) {ℓ : ℤ} (hℓ0 : ℓ ≠ 0) (hℓ : |ℓ| < (g : ℤ) ^ s) {d : ℕ} (hd1 : 1 ≤ d)
    (hne : (Tset g k L t s ℓ d).Nonempty) {κ : ℝ} (hκ : 1 ≤ κ) (N : ℕ → ℕ)
    (hN : ∀ T ∈ Tset g k L t s ℓ d, (N T : ℝ) ≤ κ) :
    ∑ T ∈ Tset g k L t s ℓ d, (N T : ℝ) *
        minDiv (d * Zplus g k L t) ((g : ℝ) ^ s) (2 * distZ (hd g k L t s ℓ d T)) ≤
      κ * (DeltaD g k L t s ℓ d + 2) *
        (2 * d * Zplus g k L t + (g : ℝ) ^ s / muD g k L t s ℓ d * LambdaT g t) := by
  classical
  obtain ⟨hmu, hgap⟩ := gaps KR hg hk hA ℓ hd1 hne
  obtain ⟨hrange, -, -⟩ := range_bound KR hg hk hA hℓ hd1 hne
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hGpos : (0 : ℝ) < (g : ℝ) ^ t := by positivity
  have hμ : 0 < muD g k L t s ℓ d := lt_of_lt_of_le (by positivity) hmu
  have hZ0 := sp_Zt_pos hg k L t
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hAp : 0 < (d : ℝ) * Zplus g k L t := by unfold Zplus; positivity
  have hH : (0 : ℝ) < (g : ℝ) ^ s / 2 := by positivity
  have hΔ0 : 0 ≤ DeltaD g k L t s ℓ d := by unfold DeltaD; positivity
  -- the values `h_d(T)` lie in an interval of length `Δ` (Lemma 79) ...
  have hy : ∀ T ∈ Tset g k L t s ℓ d,
      min (hd g k L t s ℓ d ((g : ℝ) ^ (t - 1))) (hd g k L t s ℓ d ((g : ℝ) ^ t)) ≤
        hd g k L t s ℓ d T ∧
      hd g k L t s ℓ d T ≤
        min (hd g k L t s ℓ d ((g : ℝ) ^ (t - 1))) (hd g k L t s ℓ d ((g : ℝ) ^ t)) +
          DeltaD g k L t s ℓ d := by
    intro T hT
    obtain ⟨h1, h2⟩ := hrange T hT
    refine ⟨h1, ?_⟩
    have := max_sub_min_eq_abs (hd g k L t s ℓ d ((g : ℝ) ^ (t - 1))) (hd g k L t s ℓ d ((g : ℝ) ^ t))
    unfold DeltaD
    linarith
  -- ... and each half-open interval of length `μ` contains `h_d(T)` for at most one `T`
  -- (Lemma 78), so it carries weight at most `κ`
  have hsp : ∀ a : ℝ, (∑ T ∈ (Tset g k L t s ℓ d).filter (fun T : ℕ => a ≤ hd g k L t s ℓ d T ∧
      hd g k L t s ℓ d T < a + muD g k L t s ℓ d), (N T : ℝ)) ≤ κ := by
    intro a
    have hcard : ((Tset g k L t s ℓ d).filter (fun T : ℕ => a ≤ hd g k L t s ℓ d T ∧
        hd g k L t s ℓ d T < a + muD g k L t s ℓ d)).card ≤ 1 := by
      rw [card_le_one]
      intro T hT T' hT'
      by_contra hTT
      obtain ⟨hT1, hT2, hT3⟩ := mem_filter.mp hT
      obtain ⟨hT1', hT2', hT3'⟩ := mem_filter.mp hT'
      have h1 := hgap T hT1 T' hT1' hTT
      have h2 : |hd g k L t s ℓ d T' - hd g k L t s ℓ d T| < muD g k L t s ℓ d :=
        abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
      linarith
    calc ∑ T ∈ (Tset g k L t s ℓ d).filter (fun T : ℕ => a ≤ hd g k L t s ℓ d T ∧
          hd g k L t s ℓ d T < a + muD g k L t s ℓ d), (N T : ℝ)
        ≤ ∑ T ∈ (Tset g k L t s ℓ d).filter (fun T : ℕ => a ≤ hd g k L t s ℓ d T ∧
            hd g k L t s ℓ d T < a + muD g k L t s ℓ d), κ :=
          sum_le_sum fun T hT => hN T (mem_filter.mp hT).1
      _ = ((Tset g k L t s ℓ d).filter (fun T : ℕ => a ≤ hd g k L t s ℓ d T ∧
            hd g k L t s ℓ d T < a + muD g k L t s ℓ d)).card * κ := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ 1 * κ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by linarith)
      _ = κ := one_mul κ
  -- Lemma 81 with `m = κ`, `A = dZ₊`, `H = Q/2`
  have hsum := spacing_sum (μ := muD g k L t s ℓ d) (m := κ) (A := d * Zplus g k L t)
    (H := (g : ℝ) ^ s / 2) (Δ := DeltaD g k L t s ℓ d) KR (Tset g k L t s ℓ d)
    (fun T : ℕ => hd g k L t s ℓ d T) N
    (min (hd g k L t s ℓ d ((g : ℝ) ^ (t - 1))) (hd g k L t s ℓ d ((g : ℝ) ^ t)))
    hμ hκ hAp hH hΔ0 hy hsp
  have hscale : ∀ T ∈ Tset g k L t s ℓ d, (N T : ℝ) *
      minDiv (d * Zplus g k L t) ((g : ℝ) ^ s) (2 * distZ (hd g k L t s ℓ d T)) =
      (N T : ℝ) * minDiv (d * Zplus g k L t) ((g : ℝ) ^ s / 2) (distZ (hd g k L t s ℓ d T)) := by
    intro T _
    congr 1
    conv_lhs => rw [show (g : ℝ) ^ s = 2 * ((g : ℝ) ^ s / 2) by ring]
    exact minDiv_scale (by norm_num)
  rw [sum_congr rfl hscale]
  refine hsum.trans ?_
  -- `1 + log(1 + 1/μ) ≤ Λ`, as `1/μ ≤ 6g^t`
  have hlogle : 1 + Real.log (1 + 1 / muD g k L t s ℓ d) ≤ LambdaT g t := by
    unfold LambdaT
    have h1 : 1 / muD g k L t s ℓ d ≤ 6 * (g : ℝ) ^ t := by
      rw [div_le_iff₀ hμ]; rw [div_le_iff₀ (by positivity)] at hmu; linarith
    have := Real.log_le_log (by positivity)
      (by linarith : 1 + 1 / muD g k L t s ℓ d ≤ 1 + 6 * (g : ℝ) ^ t)
    linarith
  have hκΔ : 0 ≤ κ * (DeltaD g k L t s ℓ d + 2) := mul_nonneg (by linarith) (by linarith)
  have hQμ : 0 ≤ (g : ℝ) ^ s / muD g k L t s ℓ d := by positivity
  calc κ * (DeltaD g k L t s ℓ d + 2) * (2 * (d * Zplus g k L t) +
        2 * ((g : ℝ) ^ s / 2 / muD g k L t s ℓ d) * (1 + Real.log (1 + 1 / muD g k L t s ℓ d)))
      = κ * (DeltaD g k L t s ℓ d + 2) * (2 * d * Zplus g k L t +
          (g : ℝ) ^ s / muD g k L t s ℓ d * (1 + Real.log (1 + 1 / muD g k L t s ℓ d))) := by
        ring
    _ ≤ κ * (DeltaD g k L t s ℓ d + 2) *
        (2 * d * Zplus g k L t + (g : ℝ) ^ s / muD g k L t s ℓ d * LambdaT g t) := by
        apply mul_le_mul_of_nonneg_left _ hκΔ
        linarith [mul_le_mul_of_nonneg_left hlogle hQμ]

/-- Auxiliary for [HFF 83] (also used in [HFF 84]).  `Λ > 0`. -/
private lemma sp_LambdaT_pos (g t : ℕ) : 0 < LambdaT g t := by
  unfold LambdaT
  have : 0 ≤ Real.log (1 + 6 * (g : ℝ) ^ t) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ 6 * (g : ℝ) ^ t := by positivity
                        linarith)
  linarith

/-- **[HFF 83] Lemma (Count over T, explicitly).**  If moreover `Z ≥ 2k` and `d ≤ kD^{k-1}`,
the bound of Lemma 82 is at most `κ(4g^{2s+1} + 8gD^{k-1}Z + 7g^{t+1}QΛ)`. -/
theorem count_over_T_explicit (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) {L t s : ℕ}
    (hA : Admissible L t s) {ℓ : ℤ} (hℓ0 : ℓ ≠ 0) (hℓ : |ℓ| < (g : ℤ) ^ s) {d : ℕ} (hd1 : 1 ≤ d)
    (hne : (Tset g k L t s ℓ d).Nonempty) {κ : ℝ} (hκ : 1 ≤ κ) {D : ℝ} (hD : 1 ≤ D)
    (hdD : (d : ℝ) ≤ k * D ^ (k - 1)) (hZ : 2 * (k : ℝ) ≤ Zt g k L t) :
    κ * (DeltaD g k L t s ℓ d + 2) *
        (2 * d * Zplus g k L t + (g : ℝ) ^ s / muD g k L t s ℓ d * LambdaT g t) ≤
      κ * (4 * (g : ℝ) ^ (2 * s + 1) + 8 * g * D ^ (k - 1) * Zt g k L t +
        7 * (g : ℝ) ^ (t + 1) * (g : ℝ) ^ s * LambdaT g t) := by
  obtain ⟨hmu, -⟩ := gaps KR hg hk hA ℓ hd1 hne
  obtain ⟨-, hΔ1, hΔ2⟩ := range_bound KR hg hk hA hℓ hd1 hne
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hg2 : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hZ0 := sp_Zt_pos hg k L t
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hGpos : (0 : ℝ) < (g : ℝ) ^ t := by positivity
  have hμ : 0 < muD g k L t s ℓ d := lt_of_lt_of_le (by positivity) hmu
  have hΔ0 : 0 ≤ DeltaD g k L t s ℓ d := by unfold DeltaD; positivity
  have hΛ : 0 ≤ LambdaT g t := (sp_LambdaT_pos g t).le
  have hQ : (0 : ℝ) < (g : ℝ) ^ s := by positivity
  -- `Z₊ ≤ 2gZ/k`, as `Z ≥ 2k`
  have hZp : Zplus g k L t ≤ 2 * g * Zt g k L t / k := by
    unfold Zplus
    have : 1 ≤ (g : ℝ) * Zt g k L t / k := by rw [le_div_iff₀ hk0]; nlinarith
    have e : 2 * (g : ℝ) * Zt g k L t / k = 2 * ((g : ℝ) * Zt g k L t / k) := by ring
    rw [e]; linarith
  have hZp0 : 0 ≤ Zplus g k L t := by unfold Zplus; positivity
  -- `dZ₊Δ ≤ (2gZ/k)(k g^{2s}/Z) = 2g^{2s+1}` by Lemma 79
  have h1 : (d : ℝ) * Zplus g k L t * DeltaD g k L t s ℓ d ≤ 2 * (g : ℝ) ^ (2 * s + 1) := by
    calc (d : ℝ) * Zplus g k L t * DeltaD g k L t s ℓ d
        ≤ d * (2 * g * Zt g k L t / k) * (k * (g : ℝ) ^ (2 * s) / (d * Zt g k L t)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hZp hd0.le) hΔ2 hΔ0 (by positivity)
      _ = 2 * (g : ℝ) ^ (2 * s + 1) := by field_simp; ring
  -- `dZ₊ ≤ 2gD^{k-1}Z`
  have h2 : (d : ℝ) * Zplus g k L t ≤ 2 * g * D ^ (k - 1) * Zt g k L t := by
    calc (d : ℝ) * Zplus g k L t ≤ (k * D ^ (k - 1)) * (2 * g * Zt g k L t / k) :=
          mul_le_mul hdD hZp hZp0 (by positivity)
      _ = 2 * g * D ^ (k - 1) * Zt g k L t := by field_simp
  -- `(Δ + 2)/μ ≤ g^{t+1} + 12g^t ≤ 7g^{t+1}` by Lemmas 78 and 79
  have h3 : (DeltaD g k L t s ℓ d + 2) * ((g : ℝ) ^ s / muD g k L t s ℓ d) ≤
      7 * (g : ℝ) ^ (t + 1) * (g : ℝ) ^ s := by
    have h6 : 1 ≤ 6 * (g : ℝ) ^ t * muD g k L t s ℓ d := by
      rw [div_le_iff₀ (by positivity)] at hmu; linarith
    have hgt : (g : ℝ) ^ (t + 1) = g * (g : ℝ) ^ t := by ring
    have h7 : DeltaD g k L t s ℓ d + 2 ≤ 7 * (g : ℝ) ^ (t + 1) * muD g k L t s ℓ d := by
      rw [hgt] at hΔ1 ⊢
      nlinarith [mul_nonneg (sub_nonneg.mpr hg2) (mul_nonneg hGpos.le hμ.le)]
    calc (DeltaD g k L t s ℓ d + 2) * ((g : ℝ) ^ s / muD g k L t s ℓ d)
        = (DeltaD g k L t s ℓ d + 2) / muD g k L t s ℓ d * (g : ℝ) ^ s := by ring
      _ ≤ 7 * (g : ℝ) ^ (t + 1) * (g : ℝ) ^ s := by
          apply mul_le_mul_of_nonneg_right _ hQ.le
          rw [div_le_iff₀ hμ]; exact h7
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  have h4 := mul_le_mul_of_nonneg_right h3 hΛ
  nlinarith [h1, h2, h4]

/-- **[HFF 84] Lemma (Large phases).**  With `ℬ₂ = {b ∈ ℬ : |ℓ| δ_b > d_b/2}`,
`∑_{b∈ℬ₂} Φ_b ≤ 5 τ(kD^{k-1}) k g² D^{k-1} (4g^{2s+1} + 8gD^{k-1}Z + 7g^{t+1}QΛ)`. -/
theorem large_phases (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) {L t s : ℕ} {ℓ : ℤ} {D : ℝ}
    {B : Finset ℕ} (hF : FreqSetting g k L t s ℓ D B) :
    ∑ b ∈ B.filter (fun b => (dB g k s b : ℝ) / 2 < |(ℓ : ℝ)| * deltaB g k L t s b), PhiB g k L t s b ℓ ≤
      5 * tauG g (k * D ^ (k - 1)) * k * (g : ℝ) ^ 2 * D ^ (k - 1) *
        (4 * (g : ℝ) ^ (2 * s + 1) + 8 * g * D ^ (k - 1) * Zt g k L t +
          7 * (g : ℝ) ^ (t + 1) * (g : ℝ) ^ s * LambdaT g t) := by
  classical
  obtain ⟨hA, hℓ0, hℓ, hD, hDt, hZ, hBn⟩ := id hF
  have hs1 : 1 ≤ s := hA.1
  have hg2 : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hZ0 := sp_Zt_pos hg k L t
  have hΛ := sp_LambdaT_pos g t
  set B₂ := B.filter (fun b => (dB g k s b : ℝ) / 2 < |(ℓ : ℝ)| * deltaB g k L t s b) with hB₂
  set κ : ℝ := k * (g : ℝ) ^ 2 * D ^ (k - 1) with hκ
  set U := 4 * (g : ℝ) ^ (2 * s + 1) + 8 * g * D ^ (k - 1) * Zt g k L t +
    7 * (g : ℝ) ^ (t + 1) * (g : ℝ) ^ s * LambdaT g t with hU
  -- the possible values of `d_b`: `g`-smooth integers in `[1, kD^{k-1}]`
  set Dset := (Icc 1 ⌊(k : ℝ) * D ^ (k - 1)⌋₊).filter (fun m => m.primeFactors ⊆ g.primeFactors)
    with hDset
  have hD1 : (1 : ℝ) ≤ D ^ (k - 1) := one_le_pow₀ hD
  have hκ1 : 1 ≤ κ := by
    have h4 : (4 : ℝ) ≤ (g : ℝ) ^ 2 := by nlinarith
    have h8 : (1 : ℝ) ≤ k * (g : ℝ) ^ 2 := by nlinarith
    rw [hκ]; nlinarith
  have hU0 : 0 ≤ U := by positivity
  -- By Lemma 62, `d_b ∣ Q` and `d_b ≤ k m_g(b)^{k-1} ≤ kD^{k-1}`
  have hmapD : ∀ b ∈ B₂, dB g k s b ∈ Dset := by
    intro b hb
    obtain ⟨hnode, hm⟩ := hBn b (mem_filter.mp hb).1
    obtain ⟨hdQ, hdk⟩ := dB_dvd (s := s) hg hk hnode
    have hmpos : 0 < mg g b :=
      Finset.prod_pos (fun p hp => pow_pos (Nat.pos_of_mem_primeFactors hp) _)
    have hle := Nat.le_of_dvd (by positivity) hdk
    rw [hDset, mem_filter, mem_Icc]
    refine ⟨⟨sp_dB_pos hg k s b, Nat.le_floor ?_⟩, ?_⟩
    · calc ((dB g k s b : ℕ) : ℝ) ≤ ((k * mg g b ^ (k - 1) : ℕ) : ℝ) := by exact_mod_cast hle
        _ ≤ k * D ^ (k - 1) := by push_cast; gcongr
    · have := Nat.primeFactors_mono hdQ (pow_ne_zero _ (by omega))
      rwa [Nat.primeFactors_pow g (by omega : s ≠ 0)] at this
  -- For each value `d`: Lemmas 82 and 83 with `κ = kg²D^{k-1}` and
  -- `N_T = #{b ∈ ℬ₂ : d_b = d, T_b = T} ≤ κ` (Lemma 68)
  have hper : ∀ d ∈ Dset, ∑ b ∈ B₂ with dB g k s b = d,
      5 * minDiv (dB g k s b * Zplus g k L t) ((g : ℝ) ^ s)
        (2 * distZ (hd g k L t s ℓ (dB g k s b) (Tb g k t b))) ≤ 5 * (κ * U) := by
    intro d hdD
    have hd1 : 1 ≤ d := (mem_Icc.mp (mem_filter.mp hdD).1).1
    have hdk : (d : ℝ) ≤ k * D ^ (k - 1) :=
      (Nat.cast_le.mpr (mem_Icc.mp (mem_filter.mp hdD).1).2).trans (Nat.floor_le (by positivity))
    set Bd := B₂.filter (fun b => dB g k s b = d) with hBd
    have hmapT : ∀ b ∈ Bd, Tb g k t b ∈ Tset g k L t s ℓ d := by
      intro b hb
      obtain ⟨hb2, hbd⟩ := mem_filter.mp hb
      obtain ⟨hbB, hbl⟩ := mem_filter.mp hb2
      have := (perturbation KR hg hk hF hbB hbl).1
      rwa [hbd] at this
    set N : ℕ → ℕ := fun T => (Bd.filter (fun b => Tb g k t b = T)).card with hN
    have hNκ : ∀ T ∈ Tset g k L t s ℓ d, (N T : ℝ) ≤ κ := by
      intro T _
      rcases (Bd.filter (fun b => Tb g k t b = T)).eq_empty_or_nonempty with he | ⟨b0, hb0⟩
      · simp only [hN, he, card_empty, Nat.cast_zero]; linarith
      · obtain ⟨hb0d, hb0T⟩ := mem_filter.mp hb0
        have hb0B : b0 ∈ B := (mem_filter.mp (mem_filter.mp hb0d).1).1
        obtain ⟨hn0, hm0⟩ := hBn b0 hb0B
        have hsub : Bd.filter (fun b => Tb g k t b = T) ⊆
            (range (g ^ t)).filter (fun b' => IsNode g k t b' ∧ Tb g k t b' = Tb g k t b0) := by
          intro b' hb'
          obtain ⟨hb'd, hb'T⟩ := mem_filter.mp hb'
          have hb'B : b' ∈ B := (mem_filter.mp (mem_filter.mp hb'd).1).1
          obtain ⟨hn', -⟩ := hBn b' hb'B
          exact mem_filter.mpr ⟨mem_range.mpr hn'.1, hn', by rw [hb'T, hb0T]⟩
        have hfib := fibre_bound hg hk hD hDt hn0 hm0
        calc (N T : ℝ) ≤ (((range (g ^ t)).filter
              (fun b' => IsNode g k t b' ∧ Tb g k t b' = Tb g k t b0)).card : ℝ) := by
              exact_mod_cast card_le_card hsub
          _ ≤ ((k * g ^ 2 * mg g b0 ^ (k - 1) : ℕ) : ℝ) := by exact_mod_cast hfib
          _ ≤ κ := by rw [hκ]; push_cast; gcongr
    calc ∑ b ∈ Bd, 5 * minDiv (dB g k s b * Zplus g k L t) ((g : ℝ) ^ s)
          (2 * distZ (hd g k L t s ℓ (dB g k s b) (Tb g k t b)))
        = 5 * ∑ T ∈ Tset g k L t s ℓ d, (N T : ℝ) *
            minDiv (d * Zplus g k L t) ((g : ℝ) ^ s) (2 * distZ (hd g k L t s ℓ d T)) := by
          rw [← mul_sum, ← sum_fiberwise_of_maps_to hmapT]
          congr 1
          refine sum_congr rfl fun T _ => ?_
          rw [show (N T : ℝ) * minDiv (d * Zplus g k L t) ((g : ℝ) ^ s)
              (2 * distZ (hd g k L t s ℓ d T)) =
              ∑ b ∈ Bd with Tb g k t b = T, minDiv (d * Zplus g k L t) ((g : ℝ) ^ s)
                (2 * distZ (hd g k L t s ℓ d T)) by rw [sum_const, nsmul_eq_mul]]
          refine sum_congr rfl fun b hb => ?_
          obtain ⟨hb1, hbT⟩ := mem_filter.mp hb
          rw [(mem_filter.mp hb1).2, hbT]
      _ ≤ 5 * (κ * U) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          rcases (Tset g k L t s ℓ d).eq_empty_or_nonempty with he | hne
          · rw [he, sum_empty]; positivity
          · exact (count_over_T KR hg hk hA hℓ0 hℓ hd1 hne hκ1 N hNκ).trans
              (count_over_T_explicit KR hg hk hA hℓ0 hℓ hd1 hne hκ1 hD hdk hZ)
  calc ∑ b ∈ B₂, PhiB g k L t s b ℓ
      ≤ ∑ b ∈ B₂, 5 * minDiv (dB g k s b * Zplus g k L t) ((g : ℝ) ^ s)
          (2 * distZ (hd g k L t s ℓ (dB g k s b) (Tb g k t b))) :=
        -- Lemmas 75 and 76
        sum_le_sum fun b hb => replacement KR hg hk hF (mem_filter.mp hb).1 (mem_filter.mp hb).2
    _ = ∑ d ∈ Dset, ∑ b ∈ B₂ with dB g k s b = d, 5 * minDiv (dB g k s b * Zplus g k L t)
          ((g : ℝ) ^ s) (2 * distZ (hd g k L t s ℓ (dB g k s b) (Tb g k t b))) :=
        (sum_fiberwise_of_maps_to hmapD _).symm
    _ ≤ ∑ d ∈ Dset, 5 * (κ * U) := sum_le_sum hper
    _ = (Dset.card : ℝ) * (5 * (κ * U)) := by rw [sum_const, nsmul_eq_mul]
    _ = 5 * tauG g (k * D ^ (k - 1)) * k * (g : ℝ) ^ 2 * D ^ (k - 1) * U := by
        rw [show Dset.card = tauG g (k * D ^ (k - 1)) from rfl, hκ]; ring

/-- **[HFF 85] Lemma (Bound for W_ℓ).** -/
theorem W_bound (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) {L t s : ℕ} {ℓ : ℤ} {D : ℝ}
    {B : Finset ℕ} (hF : FreqSetting g k L t s ℓ D B) :
    Wl g k L t s B ℓ ≤
      (g : ℝ) ^ t * (g : ℝ) ^ s * (2 + Real.log ((g : ℝ) ^ s)) +
        g * tauG g D * D ^ (k - 2) * Zt g k L t * (g : ℝ) ^ t / (2 * |(ℓ : ℝ)|) +
        5 * tauG g (k * D ^ (k - 1)) * k * (g : ℝ) ^ 2 * D ^ (k - 1) *
          (4 * (g : ℝ) ^ (2 * s + 1) + 8 * g * D ^ (k - 1) * Zt g k L t +
            7 * (g : ℝ) ^ (t + 1) * (g : ℝ) ^ s * LambdaT g t) := by
  classical
  -- Lemma 71 reduces to bounding `∑_{b∈ℬ} Φ_b`
  have hW := W_to_Phi KR hg hk hF
  have hL := large_phases KR hg hk hF
  have hS := sum_dB KR hg hk hF
  obtain ⟨-, hℓ0, -, hD, -, -, -⟩ := id hF
  have hZ0 := sp_Zt_pos hg k L t
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hℓpos : 0 < |(ℓ : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hℓ0)
  -- `b ∈ ℬ ∖ ℬ₂`: Lemmas 72 and 73
  have hsmall : ∑ b ∈ B with ¬ ((dB g k s b : ℝ) / 2 < |(ℓ : ℝ)| * deltaB g k L t s b),
      PhiB g k L t s b ℓ ≤ g * tauG g D * D ^ (k - 2) * Zt g k L t * (g : ℝ) ^ t / (2 * |(ℓ : ℝ)|) := by
    calc ∑ b ∈ B with ¬ ((dB g k s b : ℝ) / 2 < |(ℓ : ℝ)| * deltaB g k L t s b), PhiB g k L t s b ℓ
        ≤ ∑ b ∈ B with ¬ ((dB g k s b : ℝ) / 2 < |(ℓ : ℝ)| * deltaB g k L t s b),
            (g * Zt g k L t / (2 * k * |(ℓ : ℝ)|)) * (dB g k s b : ℝ) := by
          refine sum_le_sum fun b hb => ?_
          obtain ⟨hbB, hbs⟩ := mem_filter.mp hb
          calc PhiB g k L t s b ℓ ≤ g * Zt g k L t * dB g k s b / (2 * k * |(ℓ : ℝ)|) :=
                small_phases KR hg hk hF hbB (not_lt.mp hbs)
            _ = (g * Zt g k L t / (2 * k * |(ℓ : ℝ)|)) * (dB g k s b : ℝ) := by ring
      _ = (g * Zt g k L t / (2 * k * |(ℓ : ℝ)|)) *
            ∑ b ∈ B with ¬ ((dB g k s b : ℝ) / 2 < |(ℓ : ℝ)| * deltaB g k L t s b), (dB g k s b : ℝ) := by
          rw [mul_sum]
      _ ≤ (g * Zt g k L t / (2 * k * |(ℓ : ℝ)|)) * ∑ b ∈ B, (dB g k s b : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ (g * Zt g k L t / (2 * k * |(ℓ : ℝ)|)) * (k * tauG g D * D ^ (k - 2) * (g : ℝ) ^ t) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = g * tauG g D * D ^ (k - 2) * Zt g k L t * (g : ℝ) ^ t / (2 * |(ℓ : ℝ)|) := by
          field_simp
  -- `b ∈ ℬ₂`: Lemma 84
  rw [← sum_filter_add_sum_filter_not B
    (fun b => (dB g k s b : ℝ) / 2 < |(ℓ : ℝ)| * deltaB g k L t s b)] at hW
  linarith

/-- **[HFF 86]** The set of all nodes `b` of level `t` with `m_g(b) ≤ D`. -/
noncomputable def nodesSmall (g k t : ℕ) (D : ℝ) : Finset ℕ :=
  (range (g ^ t)).filter (fun b => IsNode g k t b ∧ (mg g b : ℝ) ≤ D)

/-- **[HFF 86]** `V`, the sum of the first and last terms in Lemma 85. -/
noncomputable def Vterm (g k L t s : ℕ) (D : ℝ) : ℝ :=
  (g : ℝ) ^ t * (g : ℝ) ^ s * (2 + Real.log ((g : ℝ) ^ s)) +
    5 * tauG g (k * D ^ (k - 1)) * k * (g : ℝ) ^ 2 * D ^ (k - 1) *
      (4 * (g : ℝ) ^ (2 * s + 1) + 8 * g * D ^ (k - 1) * Zt g k L t +
        7 * (g : ℝ) ^ (t + 1) * (g : ℝ) ^ s * LambdaT g t)

/-- Auxiliary for [HFF 86].  `∑_{0<|ℓ|<Q} 1/(2|ℓ|) ≤ 1 + log Q` (Lemma 7). -/
private lemma sp_sum_inv_abs (KR : KnownResults) {Q : ℕ} (hQ : 2 ≤ Q) :
    ∑ j ∈ (Ioo (-(Q : ℤ)) Q).erase 0, (1 : ℝ) / (2 * |(j : ℝ)|) ≤ 1 + Real.log Q := by
  classical
  -- the terms with `ℓ > 0` and those with `ℓ < 0` both give `∑_{1 ≤ n ≤ Q-1} 1/(2n)`
  have hpos : ∑ j ∈ ((Ioo (-(Q : ℤ)) Q).erase 0).filter (fun j => 0 < j),
      (1 : ℝ) / (2 * |(j : ℝ)|) = ∑ n ∈ Icc 1 (Q - 1), (1 : ℝ) / (2 * n) := by
    apply sum_nbij' (fun j : ℤ => j.toNat) (fun n : ℕ => (n : ℤ))
    · intro j hj; simp only [mem_filter, mem_erase, mem_Ioo, mem_Icc] at hj ⊢; omega
    · intro n hn; simp only [mem_filter, mem_erase, mem_Ioo, mem_Icc] at hn ⊢; omega
    · intro j hj; simp only [mem_filter] at hj; exact Int.toNat_of_nonneg hj.2.le
    · intro n _; simp
    · intro j hj
      simp only [mem_filter] at hj
      have e : ((j.toNat : ℕ) : ℝ) = (j : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hj.2.le
      rw [e, abs_of_pos (by exact_mod_cast hj.2)]
  have hneg : ∑ j ∈ ((Ioo (-(Q : ℤ)) Q).erase 0).filter (fun j => ¬ 0 < j),
      (1 : ℝ) / (2 * |(j : ℝ)|) = ∑ n ∈ Icc 1 (Q - 1), (1 : ℝ) / (2 * n) := by
    apply sum_nbij' (fun j : ℤ => (-j).toNat) (fun n : ℕ => -(n : ℤ))
    · intro j hj; simp only [mem_filter, mem_erase, mem_Ioo, mem_Icc] at hj ⊢; omega
    · intro n hn; simp only [mem_filter, mem_erase, mem_Ioo, mem_Icc] at hn ⊢; omega
    · intro j hj
      simp only [mem_filter, mem_erase] at hj
      have : 0 ≤ -j := by omega
      simp [Int.toNat_of_nonneg this]
    · intro n _; simp
    · intro j hj
      simp only [mem_filter, mem_erase] at hj
      have h0 : 0 ≤ -j := by omega
      have e : (((-j).toNat : ℕ) : ℝ) = -(j : ℝ) := by
        have := Int.toNat_of_nonneg h0
        have e2 : (((-j).toNat : ℤ) : ℝ) = ((-j : ℤ) : ℝ) := by rw [this]
        push_cast at e2; exact e2
      have hj' : (j : ℝ) < 0 := by
        have : j < 0 := by omega
        exact_mod_cast this
      rw [e, abs_of_neg hj']
  rw [← sum_filter_add_sum_filter_not _ (fun j : ℤ => 0 < j), hpos, hneg, ← sum_add_distrib]
  have hh := harmonic_le KR (Q - 1) (by omega)
  calc ∑ n ∈ Icc 1 (Q - 1), ((1 : ℝ) / (2 * n) + 1 / (2 * n))
      = ∑ n ∈ Icc 1 (Q - 1), (1 : ℝ) / n := by
        refine sum_congr rfl fun n _ => ?_; ring
    _ ≤ 1 + Real.log ((Q - 1 : ℕ) : ℝ) := hh
    _ ≤ 1 + Real.log Q := by
        have h1 : (0 : ℝ) < ((Q - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < Q - 1)
        have h2 : ((Q - 1 : ℕ) : ℝ) ≤ Q := by exact_mod_cast Nat.sub_le Q 1
        linarith [Real.log_le_log h1 h2]

/-- **[HFF 86] Lemma (Bound for E).**  With `ℬ` the set of all nodes of level `t` with
`m_g(b) ≤ D`: `E(ℬ) ≤ S(s) V + (1 + log Q) Q g τ(D) D^{k-2} Z g^t`. -/
theorem E_bound (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) {L t s : ℕ} {D : ℝ}
    (hA : Admissible L t s) (hD : 1 ≤ D) (hDt : D ^ k < 2 ^ t) (hZ : 2 * (k : ℝ) ≤ Zt g k L t) :
    Eerr g k L t s (nodesSmall g k t D) ≤
      Ssum g s * Vterm g k L t s D +
        (1 + Real.log ((g : ℝ) ^ s)) * (g : ℝ) ^ s * g * tauG g D * D ^ (k - 2) * Zt g k L t * (g : ℝ) ^ t := by
  classical
  have hs1 : 1 ≤ s := hA.1
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hZ0 := sp_Zt_pos hg k L t
  have hQ : (0 : ℝ) < (g : ℝ) ^ s := by positivity
  have hDk : (0 : ℝ) ≤ D ^ (k - 2) := by have := one_le_pow₀ (n := k - 2) hD; linarith
  have hC0 : (0 : ℝ) ≤ g * tauG g D * D ^ (k - 2) * Zt g k L t * (g : ℝ) ^ t := by positivity
  -- each `ℓ` with `0 < |ℓ| < Q` gives the setting of Definition 70
  have hsetting : ∀ j ∈ (Ioo (-((g : ℤ) ^ s)) ((g : ℤ) ^ s)).erase 0,
      FreqSetting g k L t s j D (nodesSmall g k t D) := by
    intro j hj
    obtain ⟨hj0, hjI⟩ := mem_erase.mp hj
    obtain ⟨hj1, hj2⟩ := mem_Ioo.mp hjI
    refine ⟨hA, hj0, abs_lt.mpr ⟨hj1, hj2⟩, hD, hDt, hZ, fun b hb => ?_⟩
    obtain ⟨-, hn, hm⟩ := mem_filter.mp hb
    exact ⟨hn, hm⟩
  -- `|Ψ_ℓ(a)| ≤ M(ℓ)` for `0 < a < Q`
  have hM : ∀ j : ℤ, ∀ a ∈ Ioo (0 : ℤ) ((g : ℤ) ^ s), ‖Psi g s j a‖ ≤ Mmax g s j := by
    intro j a ha
    obtain ⟨ha0, haQ⟩ := mem_Ioo.mp ha
    have ha' : a.toNat ∈ range (g ^ s) := by
      rw [mem_range]
      have : (a.toNat : ℤ) < ((g ^ s : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg ha0.le]; push_cast; exact haQ
      exact_mod_cast this
    have hle := Finset.le_sup (f := fun a : ℕ => ‖Psi g s j a‖₊) ha'
    rw [Int.toNat_of_nonneg ha0.le] at hle
    unfold Mmax
    rw [← coe_nnnorm]
    exact_mod_cast hle
  -- `M(ℓ) ≤ Q`, as each term of `Ψ_ℓ(a)` has modulus `1`
  have hMQ : ∀ j : ℤ, Mmax g s j ≤ (g : ℝ) ^ s := by
    intro j
    unfold Mmax
    have hle : (range (g ^ s)).sup (fun a : ℕ => ‖Psi g s j a‖₊) ≤ ((g ^ s : ℕ) : NNReal) := by
      refine Finset.sup_le fun a _ => ?_
      rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_natCast]
      unfold Psi
      refine (norm_sum_le _ _).trans ?_
      simp [norm_e]
    have := NNReal.coe_le_coe.mpr hle
    rw [NNReal.coe_natCast] at this
    exact_mod_cast this
  have hM0 : ∀ j : ℤ, 0 ≤ Mmax g s j := fun j => NNReal.coe_nonneg _
  -- `E(ℬ) ≤ ∑_{0<|ℓ|<Q} M(ℓ) W_ℓ`
  have h1 : Eerr g k L t s (nodesSmall g k t D) ≤
      ∑ j ∈ (Ioo (-((g : ℤ) ^ s)) ((g : ℤ) ^ s)).erase 0,
        Mmax g s j * Wl g k L t s (nodesSmall g k t D) j := by
    unfold Eerr Wl
    simp_rw [mul_sum]
    rw [sum_comm (s := nodesSmall g k t D)]
    refine sum_le_sum fun j _ => sum_le_sum fun b _ => sum_le_sum fun a ha => ?_
    exact mul_le_mul_of_nonneg_right (hM j a ha)
      (minDiv_nonneg (Nat.cast_nonneg _) zero_le_one (mul_nonneg zero_le_two (distZ_nonneg _)))
  -- Lemma 85: `W_ℓ ≤ V + g τ(D) D^{k-2} Z g^t/(2|ℓ|)`
  have h2 : ∀ j ∈ (Ioo (-((g : ℤ) ^ s)) ((g : ℤ) ^ s)).erase 0,
      Wl g k L t s (nodesSmall g k t D) j ≤ Vterm g k L t s D +
        g * tauG g D * D ^ (k - 2) * Zt g k L t * (g : ℝ) ^ t / (2 * |(j : ℝ)|) := by
    intro j hj
    have := W_bound KR hg hk (hsetting j hj)
    unfold Vterm
    linarith
  -- `∑_{0<|ℓ|<Q} 1/(2|ℓ|) ≤ 1 + log Q`
  have h3 : ∑ j ∈ (Ioo (-((g : ℤ) ^ s)) ((g : ℤ) ^ s)).erase 0, (1 : ℝ) / (2 * |(j : ℝ)|) ≤
      1 + Real.log ((g : ℝ) ^ s) := by
    have := sp_sum_inv_abs KR (Q := g ^ s) (le_trans hg (Nat.le_self_pow (by omega) g))
    push_cast at this
    exact this
  calc Eerr g k L t s (nodesSmall g k t D)
      ≤ ∑ j ∈ (Ioo (-((g : ℤ) ^ s)) ((g : ℤ) ^ s)).erase 0,
          Mmax g s j * Wl g k L t s (nodesSmall g k t D) j := h1
    _ ≤ ∑ j ∈ (Ioo (-((g : ℤ) ^ s)) ((g : ℤ) ^ s)).erase 0,
          (Mmax g s j * Vterm g k L t s D + (g : ℝ) ^ s *
            (g * tauG g D * D ^ (k - 2) * Zt g k L t * (g : ℝ) ^ t / (2 * |(j : ℝ)|))) := by
        refine sum_le_sum fun j hj => ?_
        have hc : 0 ≤ g * tauG g D * D ^ (k - 2) * Zt g k L t * (g : ℝ) ^ t / (2 * |(j : ℝ)|) := by
          positivity
        have e1 := mul_le_mul_of_nonneg_left (h2 j hj) (hM0 j)
        have e2 := mul_le_mul_of_nonneg_right (hMQ j) hc
        rw [mul_add] at e1
        linarith
    _ = Ssum g s * Vterm g k L t s D + (g : ℝ) ^ s * (g * tauG g D * D ^ (k - 2) * Zt g k L t *
          (g : ℝ) ^ t) * ∑ j ∈ (Ioo (-((g : ℤ) ^ s)) ((g : ℤ) ^ s)).erase 0,
            (1 : ℝ) / (2 * |(j : ℝ)|) := by
        rw [sum_add_distrib, ← sum_mul]
        unfold Ssum
        congr 1
        rw [mul_sum]
        refine sum_congr rfl fun j _ => ?_
        ring
    _ ≤ Ssum g s * Vterm g k L t s D + (g : ℝ) ^ s * (g * tauG g D * D ^ (k - 2) * Zt g k L t *
          (g : ℝ) ^ t) * (1 + Real.log ((g : ℝ) ^ s)) := by
        gcongr
    _ = _ := by ring

end PalindromicPowers

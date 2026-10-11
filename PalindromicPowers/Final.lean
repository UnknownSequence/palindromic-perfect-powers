import PalindromicPowers.LargeGPart

/-!
# HFF blocks 90–101: parameters, bookkeeping, and the main theorem
(Block 102 is a remark and has no Lean counterpart.)

"For `L` large: `A ≪ B`" is written `∃ C₁ : ℝ, ∃ L₀ : ℕ, ∀ L ≥ L₀, A ≤ C₁ * B`, the constants
depending only on `g` and `k` (they are chosen after `g`, `k`, before `L`).
-/

namespace PalindromicPowers

open Finset Real

variable {g k : ℕ}

/-- **[HFF 90] Definition (Parameters).**  `η = c/(32k)`. -/
noncomputable def eta (g k : ℕ) : ℝ := cSave g / (32 * k)

/-- **[HFF 90]** `ν = (2-c)/(4-c)`. -/
noncomputable def nu (g : ℕ) : ℝ := (2 - cSave g) / (4 - cSave g)

/-- **[HFF 90]** `D = X^η`. -/
noncomputable def Dpar (g k L : ℕ) : ℝ := Xr g k L ^ eta g k

/-- **[HFF 90]** `t = ⌊log_g X/(4-c)⌋ = ⌊L/(k(4-c))⌋`. -/
noncomputable def tpar (g k L : ℕ) : ℕ := ⌊(L : ℝ) / (k * (4 - cSave g))⌋₊

/-- **[HFF 90]** `s = t - 2`. -/
noncomputable def spar (g k L : ℕ) : ℕ := tpar g k L - 2

/-! ### Auxiliary facts on the parameters (used from Lemma 91 on) -/

/-- Auxiliary for [HFF 91].  Elementary facts on `c` (Lemma 26) and on `log g`:
`0 < c ≤ 1/2`, `c log g ≤ log 2 / 2`, `0 < log 2 ≤ log g`. -/
private lemma cSave_facts (KR : KnownResults) (hg : 2 ≤ g) :
    0 < cSave g ∧ cSave g ≤ 1 / 2 ∧ cSave g * Real.log g ≤ Real.log 2 / 2 ∧
      0 < Real.log g ∧ Real.log 2 ≤ Real.log g := by
  obtain ⟨hc0, hc1, -, -⟩ := power_saving KR hg
  have hg2 : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlg : Real.log 2 ≤ Real.log g := Real.log_le_log (by norm_num) hg2
  have hlgpos : 0 < Real.log g := lt_of_lt_of_le hlog2 hlg
  refine ⟨hc0, ?_, ?_, hlgpos, hlg⟩
  · calc cSave g ≤ Real.log 2 / (2 * Real.log g) := hc1
      _ ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  · have h := hc1
    rw [le_div_iff₀ (by positivity)] at h
    linarith

/-- Auxiliary for [HFF 91].  `g^n = exp(n log g)`. -/
private lemma gpow_eq_exp (hg : 2 ≤ g) (n : ℕ) : (g : ℝ) ^ n = Real.exp (n * Real.log g) := by
  rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast (show 0 < g by omega))]

/-- Auxiliary for [HFF 91].  `X^p = exp(log g · (L/k) p)`. -/
private lemma Xr_rpow_eq (hg : 2 ≤ g) (L : ℕ) (p : ℝ) :
    Xr g k L ^ p = Real.exp (Real.log g * ((L : ℝ) / k * p)) := by
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  unfold Xr
  rw [← Real.rpow_mul hg0.le, Real.rpow_def_of_pos hg0]

/-- Auxiliary for [HFF 91].  `X = exp(log g · L/k)`. -/
private lemma Xr_eq_exp (hg : 2 ≤ g) (L : ℕ) : Xr g k L = Real.exp (Real.log g * ((L : ℝ) / k)) := by
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  unfold Xr
  rw [Real.rpow_def_of_pos hg0]

/-- Auxiliary for [HFF 91].  `X > 0`. -/
private lemma Xr_pos (hg : 2 ≤ g) (L : ℕ) : 0 < Xr g k L := by
  rw [Xr_eq_exp hg]; exact Real.exp_pos _

/-- Auxiliary for [HFF 91].  `X ≥ 1`. -/
private lemma one_le_Xr (hg : 2 ≤ g) (L : ℕ) : 1 ≤ Xr g k L :=
  Real.one_le_rpow (by exact_mod_cast (show 1 ≤ g by omega)) (by positivity)

/-- Auxiliary for [HFF 92].  `D = X^η ≥ 1` (as `η ≥ 0`). -/
private lemma one_le_Dpar (KR : KnownResults) (hg : 2 ≤ g) (L : ℕ) : 1 ≤ Dpar g k L := by
  have hc0 := (power_saving KR hg).1
  exact Real.one_le_rpow (one_le_Xr hg L) (by unfold eta; positivity)

/-- Auxiliary for [HFF 91].  Polynomial factors are eventually dominated by any positive power
of `X = g^{L/k}`: for `p > 0`, eventually `C L^n ≤ X^p`. -/
private lemma eventually_le_Xr (hg : 2 ≤ g) (hk : 1 ≤ k) {p : ℝ} (hp : 0 < p) (C : ℝ) (n : ℕ) :
    ∀ᶠ L : ℕ in Filter.atTop, C * (L : ℝ) ^ n ≤ Xr g k L ^ p := by
  have hlg : 0 < Real.log g := Real.log_pos (by exact_mod_cast (show 1 < g by omega))
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hb : 0 < Real.log g * p / k := by positivity
  have hC : 0 < |C| + 1 := by positivity
  have h1 := (isLittleO_pow_exp_pos_mul_atTop n hb).bound (c := 1 / (|C| + 1)) (by positivity)
  have h3 := h1.and (Filter.eventually_ge_atTop (0 : ℝ))
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually h3] with L hL
  obtain ⟨hL1, hL2⟩ := hL
  rw [Xr_rpow_eq hg]
  have e : Real.log g * ((L : ℝ) / k * p) = Real.log g * p / k * L := by
    field_simp
  rw [e]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hL2 n),
    abs_of_pos (Real.exp_pos _)] at hL1
  have hCC : C ≤ |C| + 1 := by linarith [le_abs_self C]
  calc C * (L : ℝ) ^ n ≤ (|C| + 1) * (L : ℝ) ^ n := by gcongr
    _ ≤ (|C| + 1) * (1 / (|C| + 1) * Real.exp (Real.log g * p / k * L)) := by gcongr
    _ = Real.exp (Real.log g * p / k * L) := by field_simp

/-- **[HFF 91] Lemma (Admissible parameters).**  For `L` large: `t ≥ 3`, `1 ≤ s ≤ t-2`,
`2(t+s) ≤ L`, `Z(t) ≥ 2k`, `g^t ≤ X^{1/(4-c)} < g^{t+1}`, and `Z(t) ≤ g² X^ν`. -/
theorem admissible_params (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀,
      3 ≤ tpar g k L ∧ Admissible L (tpar g k L) (spar g k L) ∧
      2 * (k : ℝ) ≤ Zt g k L (tpar g k L) ∧
      (g : ℝ) ^ tpar g k L ≤ Xr g k L ^ (1 / (4 - cSave g)) ∧
      Xr g k L ^ (1 / (4 - cSave g)) < (g : ℝ) ^ (tpar g k L + 1) ∧
      Zt g k L (tpar g k L) ≤ (g : ℝ) ^ 2 * Xr g k L ^ nu g := by
  obtain ⟨hc0, hc1, -, hlg, -⟩ := cSave_facts KR hg
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have h4c : 0 < 4 - cSave g := by linarith
  have hnu : 0 < nu g := by unfold nu; apply div_pos <;> linarith
  -- `X^ν → ∞`, as `ν > 0`
  obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.1
    (eventually_le_Xr (k := k) hg (by omega) hnu (2 * k) 0)
  refine ⟨max L₁ (12 * k), fun L hL => ?_⟩
  have hXnu := hL₁ L (le_trans (le_max_left _ _) hL)
  simp only [pow_zero, mul_one] at hXnu
  have hL12 : ((12 * k : ℕ) : ℝ) ≤ L := by exact_mod_cast le_trans (le_max_right _ _) hL
  push_cast at hL12
  -- `u = log_g X / (4 - c) = L/(k(4-c))`, and `t = ⌊u⌋`
  have hu0 : (0 : ℝ) ≤ (L : ℝ) / (k * (4 - cSave g)) := by positivity
  have htu : (tpar g k L : ℝ) ≤ (L : ℝ) / (k * (4 - cSave g)) := Nat.floor_le hu0
  have hut : (L : ℝ) / (k * (4 - cSave g)) < tpar g k L + 1 := Nat.lt_floor_add_one _
  -- `t ≥ 3`
  have ht3 : 3 ≤ tpar g k L := by
    apply Nat.le_floor
    rw [le_div_iff₀ (by positivity)]
    push_cast
    nlinarith
  -- `7 t ≤ L`, as `k(4-c) ≥ 7`
  have ht7 : 7 * tpar g k L ≤ L := by
    have h7 : (L : ℝ) / (k * (4 - cSave g)) ≤ L / 7 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by nlinarith)
    have : ((7 * tpar g k L : ℕ) : ℝ) ≤ L := by push_cast; linarith
    exact_mod_cast this
  have hs : spar g k L = tpar g k L - 2 := rfl
  -- `L/k · ν = L/k - 2u`
  have hnu_eq : (L : ℝ) / k * nu g = L / k - 2 * ((L : ℝ) / (k * (4 - cSave g))) := by
    unfold nu; field_simp; ring
  have hinv : (L : ℝ) / k * (1 / (4 - cSave g)) = (L : ℝ) / (k * (4 - cSave g)) := by
    field_simp
  -- `Z(t) = exp(log g · L/k - 2t log g)`
  have hZt : Zt g k L (tpar g k L) =
      Real.exp (Real.log g * ((L : ℝ) / k) - 2 * tpar g k L * Real.log g) := by
    unfold Zt
    rw [Xr_eq_exp hg, gpow_eq_exp hg, ← Real.exp_sub]
    push_cast; ring_nf
  have hmul1 := mul_le_mul_of_nonneg_left htu hlg.le
  have hmul2 := mul_lt_mul_of_pos_left hut hlg
  refine ⟨ht3, ⟨by omega, by omega, by omega⟩, ?_, ?_, ?_, ?_⟩
  · -- `Z(t) ≥ X^ν ≥ 2k`
    refine le_trans hXnu ?_
    rw [Xr_rpow_eq hg, hZt, hnu_eq, Real.exp_le_exp]
    nlinarith
  · -- `g^t ≤ X^{1/(4-c)}`
    rw [Xr_rpow_eq hg, gpow_eq_exp hg, hinv, Real.exp_le_exp]
    nlinarith
  · -- `X^{1/(4-c)} < g^{t+1}`
    rw [Xr_rpow_eq hg, gpow_eq_exp hg, hinv, Real.exp_lt_exp]
    push_cast
    nlinarith
  · -- `Z(t) ≤ g² X^ν`
    rw [Xr_rpow_eq hg, gpow_eq_exp hg, hZt, hnu_eq, ← Real.exp_add, Real.exp_le_exp]
    push_cast
    nlinarith

/-- **[HFF 92] Lemma (Admissible D).**  For `L` large: `D^k < 2^t` and
`PD ≤ X^{log 2/(2 log g)}`. -/
theorem admissible_D (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀,
      Dpar g k L ^ k < 2 ^ tpar g k L ∧
      Pmax g * Dpar g k L ≤ Xr g k L ^ (Real.log 2 / (2 * Real.log g)) := by
  obtain ⟨hc0, hc1, hcl, hlg, -⟩ := cSave_facts KR hg
  obtain ⟨-, hca, -, -⟩ := power_saving KR hg
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4c : 0 < 4 - cSave g := by linarith
  -- `η < log 2/(2 log g)`
  have heta_a : eta g k < Real.log 2 / (2 * Real.log g) := by
    calc eta g k = cSave g / (32 * k) := rfl
      _ < cSave g := by rw [div_lt_iff₀ (by positivity)]; nlinarith
      _ ≤ _ := hca
  obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.1
    (eventually_le_Xr (k := k) hg (by omega) (sub_pos.2 heta_a) (Pmax g) 0)
  refine ⟨max L₁ (5 * k), fun L hL => ⟨?_, ?_⟩⟩
  · -- `D^k = X^{c/32} ≤ 2^{L/(64k)} < 2^{L/(4k) - 1} < 2^t`
    have hL5 : ((5 * k : ℕ) : ℝ) ≤ L := by exact_mod_cast le_trans (le_max_right _ _) hL
    push_cast at hL5
    have hut : (L : ℝ) / (k * (4 - cSave g)) < tpar g k L + 1 := Nat.lt_floor_add_one _
    have hu4 : (L : ℝ) / k / 4 ≤ (L : ℝ) / (k * (4 - cSave g)) := by
      rw [div_div]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
    have hw5 : 5 ≤ (L : ℝ) / k := by rw [le_div_iff₀ hk0]; linarith
    rw [show Dpar g k L ^ k = Real.exp (k * (Real.log g * ((L : ℝ) / k * eta g k))) by
      rw [Dpar, Xr_rpow_eq hg, ← Real.exp_nat_mul]]
    rw [show (2 : ℝ) ^ tpar g k L = Real.exp (tpar g k L * Real.log 2) by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]]
    rw [Real.exp_lt_exp]
    have e1 : (k : ℝ) * (Real.log g * ((L : ℝ) / k * eta g k)) =
        (cSave g * Real.log g) * ((L : ℝ) / k) / 32 := by
      unfold eta; field_simp
    rw [e1]
    have h1 : (cSave g * Real.log g) * ((L : ℝ) / k) / 32 ≤ Real.log 2 / 2 * ((L : ℝ) / k) / 32 := by
      gcongr
    have h2 : (L : ℝ) / k / 64 < (L : ℝ) / k / 4 - 1 := by linarith
    have h3 : ((L : ℝ) / k / 4 - 1) * Real.log 2 < tpar g k L * Real.log 2 := by
      apply mul_lt_mul_of_pos_right _ hlog2; linarith
    have h4 := mul_lt_mul_of_pos_left h2 hlog2
    linarith
  · -- `PD ≤ X^{log 2/(2 log g) - η} X^η`
    have h := hL₁ L (le_trans (le_max_left _ _) hL)
    simp only [pow_zero, mul_one] at h
    have hX := Xr_pos (k := k) hg L
    calc (Pmax g : ℝ) * Dpar g k L
        ≤ Xr g k L ^ (Real.log 2 / (2 * Real.log g) - eta g k) * Xr g k L ^ eta g k := by
          unfold Dpar; gcongr
      _ = Xr g k L ^ (Real.log 2 / (2 * Real.log g)) := by
          rw [← Real.rpow_add hX]; congr 1; ring

/-- **[HFF 93] Definition (The main set of nodes).**  `ℬ`, the nodes `b` of level `t` with
`m_g(b) ≤ D`, for the parameters of Definition 90. -/
noncomputable def Bmain (g k L : ℕ) : Finset ℕ := nodesSmall g k (tpar g k L) (Dpar g k L)

/-- **[HFF 94] Lemma (Main term).**  For `L` large: `(8/Q) ∑_{b∈ℬ} Z_b ≪ X^ν`. -/
theorem main_term (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) :
    ∃ C₁ : ℝ, ∃ L₀ : ℕ, ∀ L ≥ L₀,
      8 / (g : ℝ) ^ spar g k L * ∑ b ∈ Bmain g k L, (Zb g k L (tpar g k L) b : ℝ) ≤
        C₁ * Xr g k L ^ nu g := by
  obtain ⟨L₁, hL₁⟩ := admissible_params KR hg hk
  refine ⟨16 * (g : ℝ) ^ 5 / k, L₁, fun L hL => ?_⟩
  obtain ⟨ht3, hAdm, hZ, -, -, hZle⟩ := hL₁ L hL
  have hts : tpar g k L = spar g k L + 2 := by unfold spar; omega
  have htL : tpar g k L ≤ L := by have := hAdm.2.2; omega
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hZ0 : 0 ≤ Zt g k L (tpar g k L) := by linarith
  -- Lemma 36: `Z_b ≤ 2gZ/k` for every node `b`; and `#ℬ ≤ g^t`
  have hsum : ∑ b ∈ Bmain g k L, (Zb g k L (tpar g k L) b : ℝ) ≤
      (g : ℝ) ^ tpar g k L * (2 * g * Zt g k L (tpar g k L) / k) := by
    calc ∑ b ∈ Bmain g k L, (Zb g k L (tpar g k L) b : ℝ)
        ≤ ∑ _b ∈ Bmain g k L, (2 * g * Zt g k L (tpar g k L) / k) := by
          apply Finset.sum_le_sum
          intro b hb
          have hb' : IsNode g k (tpar g k L) b := (Finset.mem_filter.1 hb).2.1
          exact (nodes_nonempty KR hg hk (by omega) htL hZ hb').2
      _ = ((Bmain g k L).card : ℝ) * (2 * g * Zt g k L (tpar g k L) / k) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (g : ℝ) ^ tpar g k L * (2 * g * Zt g k L (tpar g k L) / k) := by
          gcongr
          have : (Bmain g k L).card ≤ g ^ tpar g k L := by
            unfold Bmain nodesSmall
            exact (Finset.card_filter_le _ _).trans (Finset.card_range _).le
          exact_mod_cast this
  -- `g^t/Q = g²` and `Z ≤ g² X^ν` (Lemma 91)
  calc 8 / (g : ℝ) ^ spar g k L * ∑ b ∈ Bmain g k L, (Zb g k L (tpar g k L) b : ℝ)
      ≤ 8 / (g : ℝ) ^ spar g k L * ((g : ℝ) ^ tpar g k L * (2 * g * Zt g k L (tpar g k L) / k)) := by
        gcongr
    _ = 16 * (g : ℝ) ^ 3 / k * Zt g k L (tpar g k L) := by
        rw [hts, pow_add]; field_simp; ring
    _ ≤ 16 * (g : ℝ) ^ 3 / k * ((g : ℝ) ^ 2 * Xr g k L ^ nu g) := by gcongr
    _ = 16 * (g : ℝ) ^ 5 / k * Xr g k L ^ nu g := by ring

/-- **[HFF 95] Lemma (Auxiliary bounds).**  For `L` large: `S(s) ≤ CQ²`, `S(s) ≤ C X^ν`,
`g^t = g² Q`, `2 + log Q ≤ Λ ≪ L`, and `τ(D) ≤ τ(kD^{k-1}) ≪ L^{ω(g)}`. -/
theorem aux_bounds (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) :
    ∃ C₁ : ℝ, ∃ L₀ : ℕ, ∀ L ≥ L₀,
      Ssum g (spar g k L) ≤ CSave g * ((g : ℝ) ^ spar g k L) ^ 2 ∧
      Ssum g (spar g k L) ≤ CSave g * Xr g k L ^ nu g ∧
      (g : ℝ) ^ tpar g k L = (g : ℝ) ^ 2 * (g : ℝ) ^ spar g k L ∧
      2 + Real.log ((g : ℝ) ^ spar g k L) ≤ LambdaT g (tpar g k L) ∧
      LambdaT g (tpar g k L) ≤ C₁ * L ∧
      tauG g (Dpar g k L) ≤ tauG g (k * Dpar g k L ^ (k - 1)) ∧
      (tauG g (k * Dpar g k L ^ (k - 1)) : ℝ) ≤ C₁ * (L : ℝ) ^ omegaG g := by
  obtain ⟨hc0, hc1, -, hlg, -⟩ := cSave_facts KR hg
  obtain ⟨-, -, hC1, hS⟩ := power_saving KR hg
  obtain ⟨L₁, hL₁⟩ := admissible_params KR hg hk
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hg2 : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hg0 : (0 : ℝ) < g := by linarith
  have hC0 : 0 ≤ CSave g := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have heta : 0 ≤ eta g k := by unfold eta; positivity
  have hlk : 0 ≤ Real.log k := Real.log_nonneg (by linarith)
  refine ⟨max (1 + 4 * Real.log g)
      ((1 + (Real.log k + Real.log g * eta g k) / Real.log 2) ^ omegaG g),
    max L₁ 1, fun L hL => ?_⟩
  obtain ⟨ht3, hAdm, -, -, -, -⟩ := hL₁ L (le_trans (le_max_left _ _) hL)
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hts : tpar g k L = spar g k L + 2 := by unfold spar; omega
  have hs1 : 1 ≤ spar g k L := hAdm.1
  have htL : tpar g k L ≤ L := by have := hAdm.2.2; omega
  have h4c : 0 < 4 - cSave g := by linarith
  have htu : (tpar g k L : ℝ) ≤ (L : ℝ) / (k * (4 - cSave g)) := Nat.floor_le (by positivity)
  have hgt : (g : ℝ) ^ tpar g k L = (g : ℝ) ^ 2 * (g : ℝ) ^ spar g k L := by
    rw [hts, pow_add, mul_comm]
  have hQ1 : (1 : ℝ) ≤ (g : ℝ) ^ spar g k L := one_le_pow₀ (by linarith)
  have hD1 := one_le_Dpar (k := k) KR hg L
  have hSs := hS (spar g k L) hs1
  refine ⟨?_, ?_, hgt, ?_, ?_, ?_, ?_⟩
  · -- `S(s) ≤ C g^{(2-c)s} ≤ C g^{2s} = CQ²` (Lemma 26)
    refine hSs.trans ?_
    gcongr
    rw [← pow_mul, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    push_cast
    nlinarith
  · -- `S(s) ≤ C g^{(2-c)s} ≤ C g^{(2-c)t} ≤ C X^ν` (Lemmas 26 and 91)
    refine hSs.trans ?_
    gcongr
    rw [Real.rpow_def_of_pos hg0, Xr_rpow_eq hg, Real.exp_le_exp]
    apply mul_le_mul_of_nonneg_left _ hlg.le
    have hst : (spar g k L : ℝ) ≤ tpar g k L := by
      exact_mod_cast (by omega : spar g k L ≤ tpar g k L)
    have hnu_eq : (L : ℝ) / k * nu g = (2 - cSave g) * ((L : ℝ) / (k * (4 - cSave g))) := by
      unfold nu; field_simp
    rw [hnu_eq]
    have h2c : 0 ≤ 2 - cSave g := by linarith
    calc (2 - cSave g) * (spar g k L : ℝ) ≤ (2 - cSave g) * tpar g k L := by gcongr
      _ ≤ _ := by gcongr
  · -- `2 + log Q ≤ 1 + log(24 Q) ≤ Λ`, as `g^t = g² Q ≥ 4Q`
    unfold LambdaT
    have h : 1 + Real.log ((g : ℝ) ^ spar g k L) ≤ Real.log (1 + 6 * (g : ℝ) ^ tpar g k L) := by
      have e : Real.log (Real.exp 1 * (g : ℝ) ^ spar g k L) =
          1 + Real.log ((g : ℝ) ^ spar g k L) := by
        rw [Real.log_mul (Real.exp_pos 1).ne' (pow_pos hg0 _).ne', Real.log_exp]
      rw [← e]
      apply Real.log_le_log (mul_pos (Real.exp_pos 1) (pow_pos hg0 _))
      rw [hgt]
      have he := Real.exp_one_lt_d9
      have hg4 : (4 : ℝ) ≤ (g : ℝ) ^ 2 := by nlinarith
      have hQ0 : (0 : ℝ) ≤ (g : ℝ) ^ spar g k L := by linarith
      nlinarith [mul_le_mul_of_nonneg_right hg4 hQ0, mul_le_mul_of_nonneg_right he.le hQ0]
    linarith
  · -- `Λ ≤ 1 + log(g^{t+3}) ≤ (1 + 4 log g) L`
    unfold LambdaT
    have hgt1 : (1 : ℝ) ≤ (g : ℝ) ^ tpar g k L := one_le_pow₀ (by linarith)
    have h1 : 1 + 6 * (g : ℝ) ^ tpar g k L ≤ (g : ℝ) ^ (tpar g k L + 3) := by
      rw [pow_add]
      have hg8 : (8 : ℝ) ≤ (g : ℝ) ^ 3 := by
        have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hg2 3
        norm_num at this; linarith
      nlinarith [mul_le_mul_of_nonneg_left hg8 (by linarith : (0 : ℝ) ≤ (g : ℝ) ^ tpar g k L)]
    have h2 : Real.log (1 + 6 * (g : ℝ) ^ tpar g k L) ≤ (tpar g k L + 3) * Real.log g := by
      calc Real.log (1 + 6 * (g : ℝ) ^ tpar g k L) ≤ Real.log ((g : ℝ) ^ (tpar g k L + 3)) :=
            Real.log_le_log (by positivity) h1
        _ = _ := by rw [Real.log_pow]; push_cast; ring
    have h3 : (tpar g k L + 3 : ℝ) ≤ 4 * L := by
      have : (tpar g k L : ℝ) ≤ L := by exact_mod_cast htL
      linarith
    have h4 := mul_le_mul_of_nonneg_right h3 hlg.le
    calc 1 + Real.log (1 + 6 * (g : ℝ) ^ tpar g k L) ≤ (1 + 4 * Real.log g) * L := by nlinarith
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · -- `τ(D) ≤ τ(kD^{k-1})`, as `τ` is non-decreasing (Lemma 61)
    apply (tauG_bound hg).1
    calc Dpar g k L ≤ Dpar g k L ^ (k - 1) := le_self_pow₀ hD1 (by omega)
      _ ≤ k * Dpar g k L ^ (k - 1) := le_mul_of_one_le_left (by positivity) (by linarith)
  · -- `τ(kD^{k-1}) ≤ (1 + log₂(kX^{kη}))^{ω(g)} ≪ L^{ω(g)}` (Lemma 61)
    have hDk : 1 ≤ Dpar g k L ^ (k - 1) := one_le_pow₀ hD1
    have hy1 : 1 ≤ (k : ℝ) * Dpar g k L ^ (k - 1) := by nlinarith
    have hlogD : Real.log (Dpar g k L) = Real.log g * ((L : ℝ) / k * eta g k) := by
      rw [Dpar, Xr_rpow_eq hg, Real.log_exp]
    have hlogy : Real.logb 2 ((k : ℝ) * Dpar g k L ^ (k - 1)) =
        (Real.log k + ((k - 1 : ℕ) : ℝ) * (Real.log g * ((L : ℝ) / k * eta g k))) / Real.log 2 := by
      rw [Real.logb, Real.log_mul hk0.ne' (pow_pos (by linarith) _).ne', Real.log_pow, hlogD]
    have hkk : ((k - 1 : ℕ) : ℝ) * ((L : ℝ) / k) ≤ L := by
      have : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
      calc ((k - 1 : ℕ) : ℝ) * ((L : ℝ) / k) ≤ k * ((L : ℝ) / k) := by gcongr
        _ = L := by field_simp
    have hE : ((k - 1 : ℕ) : ℝ) * (Real.log g * ((L : ℝ) / k * eta g k)) ≤
        Real.log g * eta g k * L := by
      have h0 : 0 ≤ Real.log g * eta g k := by positivity
      calc ((k - 1 : ℕ) : ℝ) * (Real.log g * ((L : ℝ) / k * eta g k))
          = Real.log g * eta g k * (((k - 1 : ℕ) : ℝ) * ((L : ℝ) / k)) := by ring
        _ ≤ Real.log g * eta g k * L := by gcongr
    have hA : 1 + Real.logb 2 ((k : ℝ) * Dpar g k L ^ (k - 1)) ≤
        (1 + (Real.log k + Real.log g * eta g k) / Real.log 2) * L := by
      rw [hlogy]
      have h1 : Real.log k + ((k - 1 : ℕ) : ℝ) * (Real.log g * ((L : ℝ) / k * eta g k)) ≤
          (Real.log k + Real.log g * eta g k) * L := by
        have : Real.log k ≤ Real.log k * L := le_mul_of_one_le_right hlk hLr
        linarith
      have h2 := div_le_div_of_nonneg_right h1 hlog2.le
      have e : (1 + (Real.log k + Real.log g * eta g k) / Real.log 2) * L =
          L + (Real.log k + Real.log g * eta g k) * L / Real.log 2 := by ring
      rw [e]; linarith
    calc (tauG g ((k : ℝ) * Dpar g k L ^ (k - 1)) : ℝ)
        ≤ (1 + Real.logb 2 ((k : ℝ) * Dpar g k L ^ (k - 1))) ^ omegaG g :=
          (tauG_bound hg).2 _ hy1
      _ ≤ ((1 + (Real.log k + Real.log g * eta g k) / Real.log 2) * L) ^ omegaG g := by
          apply pow_le_pow_left₀ _ hA
          have := Real.logb_nonneg (b := 2) (by norm_num) hy1
          linarith
      _ = (1 + (Real.log k + Real.log g * eta g k) / Real.log 2) ^ omegaG g *
            (L : ℝ) ^ omegaG g := mul_pow _ _ _
      _ ≤ _ := by gcongr; exact le_max_right _ _

/-- Auxiliary for [HFF 96].  `S(s) ≥ 0`. -/
private lemma Ssum_nonneg (s : ℕ) : 0 ≤ Ssum g s := by
  unfold Ssum Mmax
  exact Finset.sum_nonneg (fun _ _ => NNReal.coe_nonneg _)

/-- Auxiliary for [HFF 96].  The algebra of Lemma 96: with `Q = g^s`, `g^t = g²Q`,
`g^{2s+1} = gQ²`, `g^{t+1} = g³Q` (here `D` stands for `D^{k-1}`, `Lw` for `L^{ω(g)}`), the bounds
`S ≤ CQ²`, `S ≤ CY`, `2 + log Q ≤ Λ ≤ PL`, `τ ≤ PL^{ω(g)}`, `Z ≤ g²Y` give the claim. -/
private lemma err1_alg {g k S Q gt g2s1 gt1 l Λ τ D Z Y Lw L C P : ℝ}
    (hg : 0 ≤ g) (hk : 0 ≤ k) (hQ : 0 < Q) (hgt : gt = g ^ 2 * Q) (hg2s1 : g2s1 = g * Q ^ 2)
    (hgt1 : gt1 = g ^ 3 * Q) (hS0 : 0 ≤ S) (hSQ : S ≤ C * Q ^ 2) (hSY : S ≤ C * Y)
    (hl0 : 0 ≤ 2 + l) (hlΛ : 2 + l ≤ Λ) (hΛ : Λ ≤ P * L) (hτ : τ ≤ P * Lw)
    (hD : 1 ≤ D) (hZ0 : 0 ≤ Z) (hZ : Z ≤ g ^ 2 * Y) (hY : 0 ≤ Y) (hL : 1 ≤ L) (hLw : 1 ≤ Lw)
    (hC : 0 ≤ C) (hP : 0 ≤ P) :
    S * (gt * Q * (2 + l) + 5 * τ * k * g ^ 2 * D * (4 * g2s1 + 8 * g * D * Z + 7 * gt1 * Q * Λ)) /
        Q ^ 2 ≤
      C * P * (g ^ 2 + 20 * k * g ^ 3 + 40 * k * g ^ 5 + 35 * P * k * g ^ 5) * (Lw * L) * D ^ 2 * Y := by
  subst hgt hg2s1 hgt1
  have hQ0 : Q ≠ 0 := hQ.ne'
  have hR : S / Q ^ 2 ≤ C := by rw [div_le_iff₀ (by positivity)]; exact hSQ
  have hR0 : 0 ≤ S / Q ^ 2 := by positivity
  have hD0 : 0 ≤ D := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hLw0 : 0 ≤ Lw := by linarith
  have hΛ0 : 0 ≤ Λ := by linarith
  have expand : S * (g ^ 2 * Q * Q * (2 + l) + 5 * τ * k * g ^ 2 * D *
      (4 * (g * Q ^ 2) + 8 * g * D * Z + 7 * (g ^ 3 * Q) * Q * Λ)) / Q ^ 2 =
      g ^ 2 * (S * (2 + l)) + 20 * k * g ^ 3 * (τ * D * S) + 35 * k * g ^ 5 * (τ * D * S * Λ) +
        40 * k * g ^ 3 * (τ * D ^ 2 * Z * (S / Q ^ 2)) := by
    field_simp; ring
  rw [expand]
  have hLD : 1 ≤ L * D := by nlinarith
  have hLwD : 1 ≤ Lw * D ^ 2 := by nlinarith
  -- `S g^t Q (2 + log Q)/Q² ≤ g² S Λ ≪ L X^ν`
  have h1 : S * (2 + l) ≤ C * P * (Lw * L * D ^ 2 * Y) := by
    calc S * (2 + l) ≤ (C * Y) * (P * L) := mul_le_mul hSY (hlΛ.trans hΛ) hl0 (by positivity)
      _ = C * P * (L * Y) * 1 := by ring
      _ ≤ C * P * (L * Y) * (Lw * D ^ 2) := by gcongr
      _ = C * P * (Lw * L * D ^ 2 * Y) := by ring
  -- `S g^{2s+1}/Q² = gS ≪ X^ν`, times `τ(kD^{k-1}) D^{k-1}`
  have h2 : τ * D * S ≤ C * P * (Lw * L * D ^ 2 * Y) := by
    calc τ * D * S ≤ (P * Lw) * D * (C * Y) := by gcongr
      _ = C * P * (Lw * D * Y) * 1 := by ring
      _ ≤ C * P * (Lw * D * Y) * (L * D) := by gcongr
      _ = C * P * (Lw * L * D ^ 2 * Y) := by ring
  -- `S g^{t+1} Q Λ/Q² = g³ S Λ ≪ L X^ν`, times `τ(kD^{k-1}) D^{k-1}`
  have h3 : τ * D * S * Λ ≤ P * (C * P * (Lw * L * D ^ 2 * Y)) := by
    calc τ * D * S * Λ ≤ (P * Lw) * D * (C * Y) * (P * L) := by gcongr
      _ = P * (C * P * (Lw * L * D * Y)) * 1 := by ring
      _ ≤ P * (C * P * (Lw * L * D * Y)) * D := by gcongr
      _ = P * (C * P * (Lw * L * D ^ 2 * Y)) := by ring
  -- `S D^{k-1} Z/Q² ≤ C D^{k-1} Z ≪ D^{k-1} X^ν`, times `τ(kD^{k-1}) D^{k-1}`
  have h4 : τ * D ^ 2 * Z * (S / Q ^ 2) ≤ g ^ 2 * (C * P * (Lw * L * D ^ 2 * Y)) := by
    calc τ * D ^ 2 * Z * (S / Q ^ 2) ≤ (P * Lw) * D ^ 2 * (g ^ 2 * Y) * C := by gcongr
      _ = g ^ 2 * (C * P * (Lw * D ^ 2 * Y)) * 1 := by ring
      _ ≤ g ^ 2 * (C * P * (Lw * D ^ 2 * Y)) * L := by gcongr
      _ = g ^ 2 * (C * P * (Lw * L * D ^ 2 * Y)) := by ring
  have e1 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ g ^ 2)
  have e2 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 20 * k * g ^ 3)
  have e3 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 35 * k * g ^ 5)
  have e4 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 40 * k * g ^ 3)
  linarith

/-- **[HFF 96] Lemma (First error piece).**  For `L` large:
`S(s) V / Q² ≪ L^{ω(g)+1} D^{2k-2} X^ν`. -/
theorem err_piece1 (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) :
    ∃ C₁ : ℝ, ∃ L₀ : ℕ, ∀ L ≥ L₀,
      Ssum g (spar g k L) * Vterm g k L (tpar g k L) (spar g k L) (Dpar g k L) /
          ((g : ℝ) ^ spar g k L) ^ 2 ≤
        C₁ * (L : ℝ) ^ (omegaG g + 1) * Dpar g k L ^ (2 * k - 2) * Xr g k L ^ nu g := by
  obtain ⟨-, -, hC1, -⟩ := power_saving KR hg
  obtain ⟨L₁, hL₁⟩ := admissible_params KR hg hk
  obtain ⟨C₂, L₂, hL₂⟩ := aux_bounds KR hg hk
  refine ⟨CSave g * max C₂ 1 * ((g : ℝ) ^ 2 + 20 * k * (g : ℝ) ^ 3 + 40 * k * (g : ℝ) ^ 5 +
      35 * max C₂ 1 * k * (g : ℝ) ^ 5), max (max L₁ L₂) 1, fun L hL => ?_⟩
  have hL1 : L₁ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hL2 : L₂ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL3 : 1 ≤ L := le_trans (le_max_right _ _) hL
  obtain ⟨ht3, -, hZ, -, -, hZle⟩ := hL₁ L hL1
  obtain ⟨hSQ, hSY, hgt, hlΛ, hΛ, -, hτ⟩ := hL₂ L hL2
  have hts : tpar g k L = spar g k L + 2 := by unfold spar; omega
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL3
  have hP1 : (1 : ℝ) ≤ max C₂ 1 := le_max_right _ _
  have hQ1 : (1 : ℝ) ≤ (g : ℝ) ^ spar g k L := one_le_pow₀ (by exact_mod_cast (show 1 ≤ g by omega))
  have hD1 := one_le_Dpar (k := k) KR hg L
  have hΛ' : LambdaT g (tpar g k L) ≤ max C₂ 1 * L :=
    hΛ.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  have hτ' : (tauG g (k * Dpar g k L ^ (k - 1)) : ℝ) ≤ max C₂ 1 * (L : ℝ) ^ omegaG g :=
    hτ.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have key := err1_alg (g := (g : ℝ)) (k := (k : ℝ)) (S := Ssum g (spar g k L))
    (Q := (g : ℝ) ^ spar g k L) (gt := (g : ℝ) ^ tpar g k L)
    (g2s1 := (g : ℝ) ^ (2 * spar g k L + 1)) (gt1 := (g : ℝ) ^ (tpar g k L + 1))
    (l := Real.log ((g : ℝ) ^ spar g k L)) (Λ := LambdaT g (tpar g k L))
    (τ := (tauG g (k * Dpar g k L ^ (k - 1)) : ℝ)) (D := Dpar g k L ^ (k - 1))
    (Z := Zt g k L (tpar g k L)) (Y := Xr g k L ^ nu g) (Lw := (L : ℝ) ^ omegaG g) (L := (L : ℝ))
    (C := CSave g) (P := max C₂ 1)
    hg0.le hk0.le (by positivity) hgt (by ring) (by rw [hts]; ring) (Ssum_nonneg _) hSQ hSY
    (by have := Real.log_nonneg hQ1; linarith) hlΛ hΛ' hτ' (one_le_pow₀ hD1)
    (by linarith) hZle (Real.rpow_nonneg (Xr_pos hg L).le _) hLr (one_le_pow₀ hLr)
    (by linarith) (by linarith)
  have e1 : (L : ℝ) ^ (omegaG g + 1) = (L : ℝ) ^ omegaG g * L := pow_succ _ _
  have e2 : Dpar g k L ^ (2 * k - 2) = (Dpar g k L ^ (k - 1)) ^ 2 := by
    rw [← pow_mul]; congr 1; omega
  rw [e1, e2]
  exact key

/-- Auxiliary for [HFF 97].  The algebra of Lemma 97 (`E` stands for `D^{k-2}`, `Lw` for
`L^{ω(g)}`): with `g^t = g²Q`, `1 + log Q ≤ PL`, `τ(D) ≤ PL^{ω(g)}` and `Z ≤ g²Y`. -/
private lemma err2_alg {g Q gt l τ E Z Y Lw L P : ℝ} (hg : 0 ≤ g) (hQ : 0 < Q)
    (hgt : gt = g ^ 2 * Q) (hl : 1 + l ≤ P * L) (hτ0 : 0 ≤ τ) (hτ : τ ≤ P * Lw)
    (hE : 0 ≤ E) (hZ0 : 0 ≤ Z) (hZ : Z ≤ g ^ 2 * Y) (hL : 0 ≤ L) (hLw : 0 ≤ Lw)
    (hP : 0 ≤ P) :
    (1 + l) * Q * g * τ * E * Z * gt / Q ^ 2 ≤ P ^ 2 * g ^ 5 * (Lw * L) * E * Y := by
  subst hgt
  have hQ0 : Q ≠ 0 := hQ.ne'
  have expand : (1 + l) * Q * g * τ * E * Z * (g ^ 2 * Q) / Q ^ 2 =
      g ^ 3 * ((1 + l) * τ * E * Z) := by
    field_simp
  rw [expand]
  calc g ^ 3 * ((1 + l) * τ * E * Z) ≤ g ^ 3 * ((P * L) * (P * Lw) * E * (g ^ 2 * Y)) := by
        gcongr
    _ = P ^ 2 * g ^ 5 * (Lw * L) * E * Y := by ring

/-- **[HFF 97] Lemma (Second error piece).**  For `L` large:
`(1 + log Q) Q g τ(D) D^{k-2} Z g^t / Q² ≪ L^{ω(g)+1} D^{k-2} X^ν`. -/
theorem err_piece2 (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) :
    ∃ C₁ : ℝ, ∃ L₀ : ℕ, ∀ L ≥ L₀,
      (1 + Real.log ((g : ℝ) ^ spar g k L)) * (g : ℝ) ^ spar g k L * g * tauG g (Dpar g k L) *
          Dpar g k L ^ (k - 2) * Zt g k L (tpar g k L) * (g : ℝ) ^ tpar g k L /
          ((g : ℝ) ^ spar g k L) ^ 2 ≤
        C₁ * (L : ℝ) ^ (omegaG g + 1) * Dpar g k L ^ (k - 2) * Xr g k L ^ nu g := by
  obtain ⟨L₁, hL₁⟩ := admissible_params KR hg hk
  obtain ⟨C₂, L₂, hL₂⟩ := aux_bounds KR hg hk
  refine ⟨max C₂ 1 ^ 2 * (g : ℝ) ^ 5, max (max L₁ L₂) 1, fun L hL => ?_⟩
  have hL1 : L₁ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hL2 : L₂ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL3 : 1 ≤ L := le_trans (le_max_right _ _) hL
  obtain ⟨-, -, hZ, -, -, hZle⟩ := hL₁ L hL1
  obtain ⟨-, -, hgt, hlΛ, hΛ, hττ, hτ⟩ := hL₂ L hL2
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL3
  have hD1 := one_le_Dpar (k := k) KR hg L
  -- `1 + log Q ≤ Λ ≪ L` and `τ(D) ≤ τ(kD^{k-1}) ≪ L^{ω(g)}` (Lemma 95)
  have hl : 1 + Real.log ((g : ℝ) ^ spar g k L) ≤ max C₂ 1 * L := by
    have := hΛ.trans (mul_le_mul_of_nonneg_right (le_max_left C₂ 1) (by linarith))
    linarith
  have hτ' : (tauG g (Dpar g k L) : ℝ) ≤ max C₂ 1 * (L : ℝ) ^ omegaG g := by
    have h1 : (tauG g (Dpar g k L) : ℝ) ≤ tauG g (k * Dpar g k L ^ (k - 1)) := by
      exact_mod_cast hττ
    exact h1.trans (hτ.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  have key := err2_alg (g := (g : ℝ)) (Q := (g : ℝ) ^ spar g k L) (gt := (g : ℝ) ^ tpar g k L)
    (l := Real.log ((g : ℝ) ^ spar g k L)) (τ := (tauG g (Dpar g k L) : ℝ))
    (E := Dpar g k L ^ (k - 2)) (Z := Zt g k L (tpar g k L)) (Y := Xr g k L ^ nu g)
    (Lw := (L : ℝ) ^ omegaG g) (L := (L : ℝ)) (P := max C₂ 1)
    hg0.le (by positivity) hgt hl (by positivity) hτ' (by positivity) (by linarith) hZle
    (by linarith)
    (by positivity) (by positivity)
  rw [pow_succ]
  calc _ ≤ _ := key
    _ = _ := by ring

/-- Auxiliary for [HFF 98].  If `x ≠ 0`, `b = x mod g^t ≠ 0` and `m_g(x) ≤ D < 2^t`, then
`m_g(b) = m_g(x)`: for `p ∣ g`, `p^{v_p(x)} ≤ D < 2^t ≤ p^t ∣ g^t`, so `v_p(b) = v_p(x)`. -/
private lemma mg_mod_eq {x t : ℕ} {D : ℝ} (hx : x ≠ 0) (hb : x % g ^ t ≠ 0)
    (hm : (mg g x : ℝ) ≤ D) (hDt : D < 2 ^ t) : mg g (x % g ^ t) = mg g x := by
  unfold mg
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpg : p ∣ g := Nat.dvd_of_mem_primeFactors hp
  congr 1
  -- `p^{v_p(x)} ≤ m_g(x) ≤ D < 2^t ≤ p^t`, so `v_p(x) < t`
  have hpv : p ^ x.factorization p ∣ ∏ q ∈ g.primeFactors, q ^ x.factorization q :=
    Finset.dvd_prod_of_mem (fun q => q ^ x.factorization q) hp
  have hmg_pos : 0 < ∏ q ∈ g.primeFactors, q ^ x.factorization q :=
    Finset.prod_pos (fun q hq => pow_pos (Nat.prime_of_mem_primeFactors hq).pos _)
  have hle : p ^ x.factorization p ≤ mg g x := Nat.le_of_dvd hmg_pos hpv
  have hlt : p ^ x.factorization p < 2 ^ t := by
    have h : ((p ^ x.factorization p : ℕ) : ℝ) < ((2 ^ t : ℕ) : ℝ) := by
      calc ((p ^ x.factorization p : ℕ) : ℝ) ≤ (mg g x : ℝ) := by exact_mod_cast hle
        _ ≤ D := hm
        _ < 2 ^ t := hDt
        _ = ((2 ^ t : ℕ) : ℝ) := by push_cast; ring
    exact_mod_cast h
  have hvt : x.factorization p + 1 ≤ t := by
    have h : p ^ x.factorization p < p ^ t :=
      lt_of_lt_of_le hlt (Nat.pow_le_pow_left hpp.two_le t)
    have := (Nat.pow_lt_pow_iff_right hpp.one_lt).1 h
    omega
  -- hence `p^{v_p(x)+1} ∣ g^t`
  have hgt : p ^ (x.factorization p + 1) ∣ g ^ t :=
    (pow_dvd_pow p hvt).trans (pow_dvd_pow_of_dvd hpg t)
  have hsplit : x % g ^ t + g ^ t * (x / g ^ t) = x := Nat.mod_add_div x (g ^ t)
  apply le_antisymm
  · by_contra h
    have h' : x.factorization p + 1 ≤ (x % g ^ t).factorization p := by omega
    have h1 : p ^ (x.factorization p + 1) ∣ x % g ^ t :=
      (hpp.pow_dvd_iff_le_factorization hb).2 h'
    have h2 : p ^ (x.factorization p + 1) ∣ x := by
      have := dvd_add h1 (dvd_mul_of_dvd_left hgt (x / g ^ t))
      rwa [hsplit] at this
    have := (hpp.pow_dvd_iff_le_factorization hx).1 h2
    omega
  · apply (hpp.pow_dvd_iff_le_factorization hb).1
    have h2 : p ^ x.factorization p ∣ g ^ t :=
      (pow_dvd_pow p (by omega)).trans (pow_dvd_pow_of_dvd hpg t)
    exact (Nat.dvd_mod_iff h2).2 (Nat.ordProj_dvd x p)

/-- Auxiliary for [HFF 98].  Combining Lemmas 55, 86, 94, 96 and 97: if `a ≤ C_a Y`,
`E ≤ SV + R`, `SV/Q² ≤ C_b M₀ A₁ Y` and `R/Q² ≤ C_c M₀ A₂ Y` with `M₀, A₁ ≥ 1`, `0 ≤ A₂ ≤ A₁`, then
`a + (8/Q²) E ≤ (|C_a| + 8|C_b| + 8|C_c|) M₀ A₁ Y`. -/
private lemma combine_alg {a E SV R Q Ca Cb Cc M0 A1 A2 Y : ℝ} (hQ : 0 < Q) (hE : E ≤ SV + R)
    (ha : a ≤ Ca * Y) (hb : SV / Q ^ 2 ≤ Cb * M0 * A1 * Y) (hc : R / Q ^ 2 ≤ Cc * M0 * A2 * Y)
    (hM0 : 1 ≤ M0) (hA1 : 1 ≤ A1) (hA2 : 0 ≤ A2) (hA : A2 ≤ A1) (hY : 0 ≤ Y) :
    a + 8 / Q ^ 2 * E ≤ (|Ca| + 8 * |Cb| + 8 * |Cc|) * M0 * A1 * Y := by
  have hE8 : 8 / Q ^ 2 * E ≤ 8 * (SV / Q ^ 2) + 8 * (R / Q ^ 2) := by
    calc 8 / Q ^ 2 * E ≤ 8 / Q ^ 2 * (SV + R) := by gcongr
      _ = 8 * (SV / Q ^ 2) + 8 * (R / Q ^ 2) := by ring
  have hMA : 1 ≤ M0 * A1 := by nlinarith
  have hMAY : 0 ≤ M0 * A1 * Y := by positivity
  have hY1 : Y ≤ M0 * A1 * Y := by nlinarith
  have h1 : Ca * Y ≤ |Ca| * (M0 * A1 * Y) :=
    (mul_le_mul_of_nonneg_right (le_abs_self Ca) hY).trans
      (mul_le_mul_of_nonneg_left hY1 (abs_nonneg Ca))
  have h2 : Cb * M0 * A1 * Y ≤ |Cb| * (M0 * A1 * Y) := by
    calc Cb * M0 * A1 * Y = Cb * (M0 * A1 * Y) := by ring
      _ ≤ |Cb| * (M0 * A1 * Y) := mul_le_mul_of_nonneg_right (le_abs_self Cb) hMAY
  have h3 : Cc * M0 * A2 * Y ≤ |Cc| * (M0 * A1 * Y) := by
    calc Cc * M0 * A2 * Y = Cc * (M0 * A2 * Y) := by ring
      _ ≤ |Cc| * (M0 * A2 * Y) := mul_le_mul_of_nonneg_right (le_abs_self Cc) (by positivity)
      _ ≤ |Cc| * (M0 * A1 * Y) := by gcongr
  linarith

/-- **[HFF 98] Lemma (Small g-part).**  For `L` large:
`#{x ∈ 𝒬_L : m_g(x) ≤ D} ≪ L^{ω(g)+1} D^{2k-2} X^ν`. -/
theorem small_gpart (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) :
    ∃ C₁ : ℝ, ∃ L₀ : ℕ, ∀ L ≥ L₀,
      (((powSet g k L).filter (fun x => (mg g x : ℝ) ≤ Dpar g k L)).card : ℝ) ≤
        C₁ * (L : ℝ) ^ (omegaG g + 1) * Dpar g k L ^ (2 * k - 2) * Xr g k L ^ nu g := by
  obtain ⟨L₁, hL₁⟩ := admissible_params KR hg hk
  obtain ⟨L₂, hL₂⟩ := admissible_D KR hg hk
  obtain ⟨Ca, La, hLa⟩ := main_term KR hg hk
  obtain ⟨Cb, Lb, hLb⟩ := err_piece1 KR hg hk
  obtain ⟨Cc, Lc, hLc⟩ := err_piece2 KR hg hk
  refine ⟨|Ca| + 8 * |Cb| + 8 * |Cc|, max (max (max L₁ L₂) (max La Lb)) (max Lc 1),
    fun L hL => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hL
  obtain ⟨⟨⟨hL1, hL2⟩, hLa', hLb'⟩, hLc', hL3⟩ := hL
  obtain ⟨ht3, hAdm, hZ, -, -, -⟩ := hL₁ L hL1
  obtain ⟨hDt, -⟩ := hL₂ L hL2
  have hD1 := one_le_Dpar (k := k) KR hg L
  have ht1 : 1 ≤ tpar g k L := by omega
  have htL : tpar g k L ≤ L := by have := hAdm.2.2; omega
  have hg0 : 0 < g := by omega
  -- If `m_g(x) ≤ D` then `b := x mod g^t` is a node (Lemma 33) with `m_g(b) = m_g(x)`: `b ∈ ℬ`
  have hsub : (powSet g k L).filter (fun x => (mg g x : ℝ) ≤ Dpar g k L) ⊆
      (powSet g k L).filter (fun x => x % g ^ tpar g k L ∈ Bmain g k L) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨hx.1, ?_⟩
    obtain ⟨hnode, -, -⟩ := tree hg hk ht1 htL hx.1
    have hx0 : x ≠ 0 := by
      rintro rfl
      have hp := (Finset.mem_filter.1 hx.1).2
      rw [zero_pow (by omega)] at hp
      have h1 := (Finset.mem_Ico.1 (Finset.mem_filter.1 hp).1).1
      have h2 : 0 < g ^ (L - 1) := pow_pos hg0 _
      omega
    have hb0 : x % g ^ tpar g k L ≠ 0 := by
      intro h
      apply hnode.2
      rw [h, zero_pow (by omega)]
      exact dvd_zero g
    have hDt' : Dpar g k L < 2 ^ tpar g k L :=
      lt_of_le_of_lt (le_self_pow₀ hD1 (by omega)) hDt
    have hmg := mg_mod_eq hx0 hb0 hx.2 hDt'
    unfold Bmain nodesSmall
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_range.2 (Nat.mod_lt _ (pow_pos hg0 _)), hnode, by rw [hmg]; exact hx.2⟩
  -- Lemmas 91 and 36: `Z_b ≥ 1` on `ℬ`
  have hB : ∀ b ∈ Bmain g k L, IsNode g k (tpar g k L) b ∧ 1 ≤ Zb g k L (tpar g k L) b := by
    intro b hb
    have hnode : IsNode g k (tpar g k L) b := (Finset.mem_filter.1 hb).2.1
    exact ⟨hnode, (nodes_nonempty KR hg hk ht1 htL hZ hnode).1⟩
  have hcard : (((powSet g k L).filter (fun x => (mg g x : ℝ) ≤ Dpar g k L)).card : ℝ) ≤
      (((powSet g k L).filter (fun x => x % g ^ tpar g k L ∈ Bmain g k L)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  -- Lemma 55, then Lemmas 94, 86, 96 and 97
  have hred := reduction KR hg hk hAdm (Bmain g k L) hB
  have hE := E_bound KR hg hk hAdm hD1 hDt hZ
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL3
  refine hcard.trans (hred.trans (combine_alg (by positivity) hE (hLa L hLa') (hLb L hLb')
    (hLc L hLc') (one_le_pow₀ hLr) (one_le_pow₀ hD1) (by positivity)
    (pow_le_pow_right₀ hD1 (by omega)) (Real.rpow_nonneg (Xr_pos hg L).le _)))

/-- **[HFF 99] Lemma (Exponents).**  `ν + (2k-2)η ≤ 1/2 - η`. -/
theorem exponents (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) :
    nu g + (2 * k - 2) * eta g k ≤ 1 / 2 - eta g k := by
  obtain ⟨hc0, hc1, -, -, -⟩ := cSave_facts KR hg
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have h4c : 0 < 4 - cSave g := by linarith
  -- `ν = 1/2 - c/(2(4-c)) ≤ 1/2 - c/8 = 1/2 - 4kη`, and `(2k-2)η + η < 2kη ≤ 4kη`
  have hnu : nu g = 1 / 2 - cSave g / (2 * (4 - cSave g)) := by
    unfold nu; field_simp; ring
  have hc8 : cSave g / 8 ≤ cSave g / (2 * (4 - cSave g)) :=
    div_le_div_of_nonneg_left hc0.le (by positivity) (by linarith)
  have heta : 4 * k * eta g k = cSave g / 8 := by
    unfold eta; field_simp; ring
  have heta0 : 0 ≤ eta g k := by unfold eta; positivity
  linarith

/-- **[HFF 100] Lemma (Counting solutions).**  For `L` large: `#𝒬_L ≪ X^{(1-η)/2}`. -/
theorem count_solutions (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) :
    ∃ C₁ : ℝ, ∃ L₀ : ℕ, ∀ L ≥ L₀,
      ((powSet g k L).card : ℝ) ≤ C₁ * Xr g k L ^ ((1 - eta g k) / 2) := by
  obtain ⟨hc0, -, -, hlg, -⟩ := cSave_facts KR hg
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have heta : 0 < eta g k := by unfold eta; positivity
  have hexp := exponents KR hg hk
  obtain ⟨L₂, hL₂⟩ := admissible_D KR hg hk
  obtain ⟨Cs, Ls, hLs⟩ := small_gpart KR hg hk
  -- `L^{ω(g)+1} ≤ X^{η/2}` for `L` large, as `η > 0`
  obtain ⟨L₃, hL₃⟩ := Filter.eventually_atTop.1
    (eventually_le_Xr (k := k) hg (by omega) (half_pos heta) 1 (omegaG g + 1))
  refine ⟨|Cs| + 2 ^ omegaG g * ((g : ℝ) / k + 1) * g, max (max L₂ Ls) (max L₃ 1),
    fun L hL => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hL
  obtain ⟨⟨hL2, hLs'⟩, hL3, hL1⟩ := hL
  obtain ⟨-, hPD⟩ := hL₂ L hL2
  have hsmall := hLs L hLs'
  have hpoly := hL₃ L hL3
  rw [one_mul] at hpoly
  have hD1 := one_le_Dpar (k := k) KR hg L
  have hX := Xr_pos (k := k) hg L
  have hX1 := one_le_Xr (k := k) hg L
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hY0 : 0 ≤ Xr g k L ^ (1 / 2 - eta g k) := Real.rpow_nonneg hX.le _
  -- Small g-part (Lemmas 98 and 99): `≪ L^{ω(g)+1} D^{2k-2} X^ν ≤ L^{ω(g)+1} X^{1/2-η}`
  have h1 : (((powSet g k L).filter (fun x => (mg g x : ℝ) ≤ Dpar g k L)).card : ℝ) ≤
      |Cs| * (L : ℝ) ^ (omegaG g + 1) * Xr g k L ^ (1 / 2 - eta g k) := by
    have hDY : Dpar g k L ^ (2 * k - 2) * Xr g k L ^ nu g ≤ Xr g k L ^ (1 / 2 - eta g k) := by
      rw [Dpar, ← Real.rpow_mul_natCast hX.le, ← Real.rpow_add hX]
      apply Real.rpow_le_rpow_of_exponent_le hX1
      have : ((2 * k - 2 : ℕ) : ℝ) = 2 * k - 2 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [this]; linarith
    calc _ ≤ Cs * (L : ℝ) ^ (omegaG g + 1) * Dpar g k L ^ (2 * k - 2) * Xr g k L ^ nu g := hsmall
      _ = Cs * (L : ℝ) ^ (omegaG g + 1) * (Dpar g k L ^ (2 * k - 2) * Xr g k L ^ nu g) := by ring
      _ ≤ |Cs| * (L : ℝ) ^ (omegaG g + 1) * (Dpar g k L ^ (2 * k - 2) * Xr g k L ^ nu g) := by
          gcongr
          exact le_abs_self _
      _ ≤ |Cs| * (L : ℝ) ^ (omegaG g + 1) * Xr g k L ^ (1 / 2 - eta g k) := by gcongr
  -- Large g-part (Lemmas 89, 92 and 61): `≤ τ(PD)(g/k+1) g X^{1/2}/D ≪ L^{ω(g)} X^{1/2-η}`
  have h2 : (((powSet g k L).filter (fun x => Dpar g k L < mg g x)).card : ℝ) ≤
      2 ^ omegaG g * ((g : ℝ) / k + 1) * g * ((L : ℝ) ^ omegaG g * Xr g k L ^ (1 / 2 - eta g k)) := by
    have hlarge := large_gpart KR hg hk hL1 hD1 hPD
    -- `τ(PD) ≤ τ(X^{log 2/(2 log g)}) ≤ (1 + L/(2k))^{ω(g)} ≤ (2L)^{ω(g)}`
    have hτ : (tauG g (Pmax g * Dpar g k L) : ℝ) ≤ 2 ^ omegaG g * (L : ℝ) ^ omegaG g := by
      have hmono : tauG g (Pmax g * Dpar g k L) ≤
          tauG g (Xr g k L ^ (Real.log 2 / (2 * Real.log g))) := (tauG_bound hg).1 hPD
      have hXa1 : 1 ≤ Xr g k L ^ (Real.log 2 / (2 * Real.log g)) :=
        Real.one_le_rpow hX1 (by positivity)
      have hlogb : Real.logb 2 (Xr g k L ^ (Real.log 2 / (2 * Real.log g))) = (L : ℝ) / (2 * k) := by
        rw [Xr_rpow_eq hg, Real.logb, Real.log_exp]
        field_simp
      calc (tauG g (Pmax g * Dpar g k L) : ℝ)
          ≤ tauG g (Xr g k L ^ (Real.log 2 / (2 * Real.log g))) := by exact_mod_cast hmono
        _ ≤ (1 + Real.logb 2 (Xr g k L ^ (Real.log 2 / (2 * Real.log g)))) ^ omegaG g :=
            (tauG_bound hg).2 _ hXa1
        _ ≤ (2 * L) ^ omegaG g := by
            rw [hlogb]
            apply pow_le_pow_left₀ (by positivity)
            have : (L : ℝ) / (2 * k) ≤ L := by
              rw [div_le_iff₀ (by positivity)]; nlinarith
            linarith
        _ = 2 ^ omegaG g * (L : ℝ) ^ omegaG g := mul_pow _ _ _
    -- `X^{1/2}/D = X^{1/2-η}`
    have hsq : Real.sqrt (Xr g k L) / Dpar g k L = Xr g k L ^ (1 / 2 - eta g k) := by
      rw [Real.sqrt_eq_rpow, Dpar, ← Real.rpow_sub hX]
    calc _ ≤ tauG g (Pmax g * Dpar g k L) * ((g : ℝ) / k + 1) * g * Real.sqrt (Xr g k L) /
          Dpar g k L := hlarge
      _ = tauG g (Pmax g * Dpar g k L) * ((g : ℝ) / k + 1) * g *
          (Real.sqrt (Xr g k L) / Dpar g k L) := by ring
      _ ≤ (2 ^ omegaG g * (L : ℝ) ^ omegaG g) * ((g : ℝ) / k + 1) * g *
          Xr g k L ^ (1 / 2 - eta g k) := by rw [hsq]; gcongr
      _ = _ := by ring
  -- `#𝒬_L` splits according to `m_g(x) ≤ D` or `m_g(x) > D`
  have hsplit := Finset.card_filter_add_card_filter_not (s := powSet g k L)
    (fun x => (mg g x : ℝ) ≤ Dpar g k L)
  simp only [not_le] at hsplit
  have hcard : ((powSet g k L).card : ℝ) =
      (((powSet g k L).filter (fun x => (mg g x : ℝ) ≤ Dpar g k L)).card : ℝ) +
        (((powSet g k L).filter (fun x => Dpar g k L < mg g x)).card : ℝ) := by
    exact_mod_cast hsplit.symm
  have hK : (0 : ℝ) ≤ 2 ^ omegaG g * ((g : ℝ) / k + 1) * g := by positivity
  have hLw : (L : ℝ) ^ omegaG g * Xr g k L ^ (1 / 2 - eta g k) ≤
      (L : ℝ) ^ (omegaG g + 1) * Xr g k L ^ (1 / 2 - eta g k) := by
    gcongr
    · omega
  have h3 := mul_le_mul_of_nonneg_left hLw hK
  -- finally `L^{ω(g)+1} ≤ X^{η/2}`
  calc ((powSet g k L).card : ℝ)
      ≤ (|Cs| + 2 ^ omegaG g * ((g : ℝ) / k + 1) * g) *
          ((L : ℝ) ^ (omegaG g + 1) * Xr g k L ^ (1 / 2 - eta g k)) := by
        rw [hcard]; nlinarith
    _ ≤ (|Cs| + 2 ^ omegaG g * ((g : ℝ) / k + 1) * g) *
          (Xr g k L ^ (eta g k / 2) * Xr g k L ^ (1 / 2 - eta g k)) := by gcongr
    _ = (|Cs| + 2 ^ omegaG g * ((g : ℝ) / k + 1) * g) * Xr g k L ^ ((1 - eta g k) / 2) := by
        rw [← Real.rpow_add hX]; congr 2; ring

/-- **[HFF 101] Theorem (Palindromic perfect powers).**  For all integers `g ≥ 2` and `k ≥ 2`
there are `γ = γ(g,k) < 1` (in fact `0 < γ`) and `C' = C'(g,k)` such that, for every `L ≥ 1`, the
number of `L`-digit palindromes in base `g` that are perfect `k`-th powers is at most
`C' (#𝒫_L)^{γ/k}`. -/
theorem main_theorem (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ ∃ C' : ℝ, ∀ L : ℕ, 1 ≤ L →
      (((palSet g L).filter (fun n => ∃ x ≤ n, x ^ k = n)).card : ℝ) ≤
        C' * ((palSet g L).card : ℝ) ^ (γ / k) := by
  obtain ⟨hc0, hc1, -, -, -⟩ := cSave_facts KR hg
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast (show 1 ≤ g by omega)
  have hg0 : (0 : ℝ) < g := by linarith
  have heta : 0 < eta g k := by unfold eta; positivity
  have heta1 : eta g k < 1 := by
    unfold eta; rw [div_lt_one (by positivity)]; nlinarith
  obtain ⟨C₁, L₀, hL₀⟩ := count_solutions KR hg hk
  -- `γ = 1 - η`
  refine ⟨1 - eta g k, by linarith, by linarith,
    max C₁ 0 * (g : ℝ) ^ ((1 - eta g k) / k) + (g : ℝ) ^ L₀, fun L hL => ?_⟩
  -- `x ↦ x^k` maps `𝒬_L` onto the palindromes that are perfect `k`-th powers
  have hsub : (palSet g L).filter (fun n => ∃ x ≤ n, x ^ k = n) ⊆
      (powSet g k L).image (fun x => x ^ k) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnP, x, hxn, rfl⟩ := hn
    rw [Finset.mem_image]
    refine ⟨x, ?_, rfl⟩
    unfold powSet
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨lt_of_le_of_lt hxn (Finset.mem_Ico.1 (Finset.mem_filter.1 hnP).1).2, hnP⟩
  have hcardQ : (((palSet g L).filter (fun n => ∃ x ≤ n, x ^ k = n)).card : ℝ) ≤
      (powSet g k L).card := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
  -- `#𝒫_L ≥ 1` (Lemma 29)
  obtain ⟨hPL, hXP⟩ := many_palindromes hg hk hL
  have hP1 : (1 : ℝ) ≤ (palSet g L).card := by
    have h0 : (0 : ℝ) < (palSet g L).card := lt_of_lt_of_le (Real.rpow_pos_of_pos hg0 _) hPL
    have : 0 < (palSet g L).card := by exact_mod_cast h0
    exact_mod_cast this
  have hγk : 0 ≤ (1 - eta g k) / k := div_nonneg (by linarith) hk0.le
  have hγ2 : 0 ≤ (1 - eta g k) / 2 := div_nonneg (by linarith) (by norm_num)
  have hPγ : 1 ≤ ((palSet g L).card : ℝ) ^ ((1 - eta g k) / k) := Real.one_le_rpow hP1 hγk
  have hC0 : 0 ≤ max C₁ 0 * (g : ℝ) ^ ((1 - eta g k) / k) := by positivity
  have hgL0 : (0 : ℝ) ≤ (g : ℝ) ^ L₀ := by positivity
  by_cases hLL : L₀ ≤ L
  · -- `L` large: `#𝒬_L ≪ X^{(1-η)/2} ≤ (g #𝒫_L)^{γ/k}` (Lemmas 100 and 29)
    have hX0 : 0 ≤ Xr g k L := (Xr_pos hg L).le
    calc _ ≤ ((powSet g k L).card : ℝ) := hcardQ
      _ ≤ C₁ * Xr g k L ^ ((1 - eta g k) / 2) := hL₀ L hLL
      _ ≤ max C₁ 0 * Xr g k L ^ ((1 - eta g k) / 2) := by
          gcongr; exact le_max_left _ _
      _ ≤ max C₁ 0 * (((g : ℝ) * (palSet g L).card) ^ ((2 : ℝ) / k)) ^ ((1 - eta g k) / 2) := by
          gcongr
      _ = max C₁ 0 * (g : ℝ) ^ ((1 - eta g k) / k) *
            ((palSet g L).card : ℝ) ^ ((1 - eta g k) / k) := by
          rw [← Real.rpow_mul (by positivity), Real.mul_rpow (by positivity) (by positivity)]
          have e : (2 : ℝ) / k * ((1 - eta g k) / 2) = (1 - eta g k) / k := by
            field_simp
          rw [e]; ring
      _ ≤ _ := by gcongr; linarith
  · -- the finitely many `L < L₀`: `#𝒬_L ≤ #𝒫_L ≤ g^L ≤ g^{L₀}`; enlarge `C'`
    push Not at hLL
    have hPcard : (palSet g L).card ≤ g ^ L := by
      unfold palSet
      exact (Finset.card_filter_le _ _).trans (by rw [Nat.card_Ico]; exact Nat.sub_le _ _)
    calc _ ≤ ((palSet g L).card : ℝ) := by exact_mod_cast Finset.card_filter_le _ _
      _ ≤ (g : ℝ) ^ L := by exact_mod_cast hPcard
      _ ≤ (g : ℝ) ^ L₀ := pow_le_pow_right₀ hg1 hLL.le
      _ ≤ (g : ℝ) ^ L₀ * ((palSet g L).card : ℝ) ^ ((1 - eta g k) / k) :=
          le_mul_of_one_le_right hgL0 hPγ
      _ ≤ _ := by gcongr; linarith

end PalindromicPowers

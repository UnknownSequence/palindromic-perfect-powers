import PalindromicPowers.Roots

/-!
# HFF blocks 69–73: data for one frequency
(Block 69 is a remark and has no Lean counterpart.)
-/

namespace PalindromicPowers

open Finset Real

variable {g k : ℕ}

/-- **[HFF 70] Definition (Data for one frequency).**  The hypotheses of the setting:
`t, s` as in Definition 37, `0 < |ℓ| < Q`, `D ≥ 1` with `D^k < 2^t`, `Z ≥ 2k`, and `ℬ` a set of
nodes `b` of level `t` with `m_g(b) ≤ D`. -/
def FreqSetting (g k L t s : ℕ) (ℓ : ℤ) (D : ℝ) (B : Finset ℕ) : Prop :=
  Admissible L t s ∧ ℓ ≠ 0 ∧ |ℓ| < (g : ℤ) ^ s ∧ 1 ≤ D ∧ D ^ k < 2 ^ t ∧
    2 * (k : ℝ) ≤ Zt g k L t ∧ ∀ b ∈ B, IsNode g k t b ∧ (mg g b : ℝ) ≤ D

/-- **[HFF 70]** `Z₊ = gZ/k + 1`. -/
noncomputable def Zplus (g k L t : ℕ) : ℝ := g * Zt g k L t / k + 1

/-- **[HFF 70]** `y_b = ℓ δ_b / d_b`. -/
noncomputable def yB (g k L t s b : ℕ) (ℓ : ℤ) : ℝ := ℓ * deltaB g k L t s b / dB g k s b

/-- **[HFF 70]** `Φ_b = min(d_b Z₊, Q/(2‖y_b‖))`. -/
noncomputable def PhiB (g k L t s b : ℕ) (ℓ : ℤ) : ℝ :=
  minDiv (dB g k s b * Zplus g k L t) ((g : ℝ) ^ s) (2 * distZ (yB g k L t s b ℓ))

/-- **[HFF 70]** `W_ℓ = ∑_{b∈ℬ} ∑_{0<a<Q} min(Z_b, 1/(2‖θ_{b,ℓ,a}‖))`. -/
noncomputable def Wl (g k L t s : ℕ) (B : Finset ℕ) (ℓ : ℤ) : ℝ :=
  ∑ b ∈ B, ∑ a ∈ Ioo (0 : ℤ) ((g : ℤ) ^ s), minDiv (Zb g k L t b) 1 (2 * distZ (thetaB g k L t s b ℓ a))

/-- **[HFF 71] Lemma (From W_ℓ to Φ_b).**  `W_ℓ ≤ ∑_{b∈ℬ} Φ_b + g^t Q (2 + log Q)`. -/
theorem W_to_Phi (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) {L t s : ℕ} {ℓ : ℤ} {D : ℝ}
    {B : Finset ℕ} (hF : FreqSetting g k L t s ℓ D B) :
    Wl g k L t s B ℓ ≤
      ∑ b ∈ B, PhiB g k L t s b ℓ + (g : ℝ) ^ t * (g : ℝ) ^ s * (2 + Real.log ((g : ℝ) ^ s)) := by
  obtain ⟨hA, -, -, -, -, hZ, hB⟩ := hF
  obtain ⟨hs1, hst, hL⟩ := hA
  have ht1 : 1 ≤ t := by omega
  have htL : t ≤ L := by omega
  have hQ1 : (1 : ℝ) ≤ (g : ℝ) ^ s := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ g))
  set E : ℝ := (g : ℝ) ^ s * (2 + Real.log ((g : ℝ) ^ s)) with hE
  have hE0 : 0 ≤ E := by
    have := Real.log_nonneg hQ1
    positivity
  -- For each node `b ∈ ℬ`: the inner sum is at most `Φ_b + Q(2 + log Q)`.
  have hnode : ∀ b ∈ B, ∑ a ∈ Ioo (0 : ℤ) ((g : ℤ) ^ s),
      minDiv (Zb g k L t b) 1 (2 * distZ (thetaB g k L t s b ℓ a)) ≤ PhiB g k L t s b ℓ + E := by
    intro b hb
    obtain ⟨hbn, -⟩ := hB b hb
    -- `1 ≤ Z_b ≤ Z₊` (Lemmas 36 and 35).
    have hZb1 : (1 : ℝ) ≤ Zb g k L t b := by exact_mod_cast (nodes_nonempty KR hg hk ht1 htL hZ hbn).1
    have hZb2 : (Zb g k L t b : ℝ) ≤ Zplus g k L t := (node_sizes KR hg hk ht1 htL hbn).2.2.2
    set F : ℤ → ℝ := fun a => minDiv (Zb g k L t b) 1 (2 * distZ (thetaB g k L t s b ℓ a)) with hFdef
    have hF0 : ∀ a, 0 ≤ F a := fun a =>
      minDiv_nonneg (by linarith) zero_le_one
        (by have := distZ_nonneg (thetaB g k L t s b ℓ a); linarith)
    -- Add the term `a = 0`.
    have h1 : ∑ a ∈ Ioo (0 : ℤ) ((g : ℤ) ^ s), F a ≤ ∑ a ∈ range (g ^ s), F (a : ℤ) := by
      rw [← sum_image (f := F) (Nat.cast_injective.injOn)]
      apply sum_le_sum_of_subset_of_nonneg
      · intro a ha
        have hQZ : (g : ℤ) ^ s = ((g ^ s : ℕ) : ℤ) := by push_cast; rfl
        rw [mem_Ioo, hQZ] at ha
        rw [mem_image]
        exact ⟨a.toNat, by rw [mem_range]; omega, by omega⟩
      · intro a _ _; exact hF0 a
    -- Lemma 59 with `y = ℓδ_b`, `β = β_b`, `A = Z_b`.
    have h2 := a_sum KR hg s ((ℓ : ℝ) * deltaB g k L t s b) (betaB g k s b : ℤ) hZb1
    have hgcd : Int.gcd (betaB g k s b : ℤ) ((g : ℤ) ^ s) = dB g k s b := by
      rw [← Nat.cast_pow, Int.gcd_natCast_natCast]; rfl
    rw [hgcd] at h2
    have h3 : ∑ a ∈ range (g ^ s), F (a : ℤ) = ∑ a ∈ range (g ^ s),
        minDiv (Zb g k L t b) 1 (2 * distZ (((ℓ : ℝ) * deltaB g k L t s b +
          (a : ℝ) * ((betaB g k s b : ℤ) : ℝ)) / (g : ℝ) ^ s)) := by
      simp only [hFdef, thetaB, Int.cast_natCast]
    calc ∑ a ∈ Ioo (0 : ℤ) ((g : ℤ) ^ s), F a ≤ ∑ a ∈ range (g ^ s), F (a : ℤ) := h1
      _ ≤ minDiv ((dB g k s b : ℝ) * Zb g k L t b) ((g : ℝ) ^ s)
            (2 * distZ ((ℓ : ℝ) * deltaB g k L t s b / dB g k s b)) + E := by rw [h3]; exact h2
      _ ≤ PhiB g k L t s b ℓ + E := by
        unfold PhiB yB
        gcongr
        exact minDiv_mono_left (by gcongr)
  -- Sum over `b ∈ ℬ`, with `#ℬ ≤ g^t`.
  have hcard : (B.card : ℝ) ≤ (g : ℝ) ^ t := by
    have : B ⊆ range (g ^ t) := fun b hb => mem_range.mpr (hB b hb).1.1
    have := card_le_card this
    rw [card_range] at this
    exact_mod_cast this
  calc Wl g k L t s B ℓ ≤ ∑ b ∈ B, (PhiB g k L t s b ℓ + E) := sum_le_sum hnode
    _ = ∑ b ∈ B, PhiB g k L t s b ℓ + B.card * E := by rw [sum_add_distrib, sum_const, nsmul_eq_mul]
    _ ≤ ∑ b ∈ B, PhiB g k L t s b ℓ + (g : ℝ) ^ t * E := by gcongr
    _ = ∑ b ∈ B, PhiB g k L t s b ℓ + (g : ℝ) ^ t * (g : ℝ) ^ s * (2 + Real.log ((g : ℝ) ^ s)) := by
        rw [hE]; ring

/-- **[HFF 72] Lemma (Small phases).**  If `b ∈ ℬ` and `|ℓ| δ_b ≤ d_b/2`, then
`Φ_b ≤ g Z d_b / (2k|ℓ|)`. -/
theorem small_phases (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) {L t s : ℕ} {ℓ : ℤ} {D : ℝ}
    {B : Finset ℕ} (hF : FreqSetting g k L t s ℓ D B) {b : ℕ} (hbB : b ∈ B)
    (hsmall : |(ℓ : ℝ)| * deltaB g k L t s b ≤ dB g k s b / 2) :
    PhiB g k L t s b ℓ ≤ g * Zt g k L t * dB g k s b / (2 * k * |(ℓ : ℝ)|) := by
  obtain ⟨hA, hℓ0, -, -, -, hZ, hB⟩ := hF
  obtain ⟨hs1, hst, hL⟩ := id hA
  obtain ⟨hbn, -⟩ := hB b hbB
  have ht1 : 1 ≤ t := by omega
  have htL : t ≤ L := by omega
  have hZb := (nodes_nonempty KR hg hk ht1 htL hZ hbn).1
  -- `δ_b ≥ δ(T_b) ≥ kQ/(gZ)` (Lemmas 40, 39 and 32).
  have hlead := leading_digit hg ht1 hbn
  have hδ1 := (deltaB_near KR hg hk hA hbn hZb).1
  have hδ2 := ((deltaT_formula hg hk hA).2 (Tb g k t b) (by exact_mod_cast hlead.1)
    (by exact_mod_cast hlead.2.le)).1
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hZpos : 0 < Zt g k L t := by linarith
  have hQpos : (0 : ℝ) < (g : ℝ) ^ s := by positivity
  have hkQ : 0 < k * (g : ℝ) ^ s / (g * Zt g k L t) := by positivity
  have hδ : k * (g : ℝ) ^ s / (g * Zt g k L t) ≤ deltaB g k L t s b := by linarith
  have hδpos : 0 < deltaB g k L t s b := by linarith
  have hdpos : (0 : ℝ) < dB g k s b := by
    exact_mod_cast Nat.gcd_pos_of_pos_right _ (pow_pos (by omega) _)
  have hℓpos : 0 < |(ℓ : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hℓ0)
  -- `|y_b| ≤ 1/2`, so `‖y_b‖ = |ℓ| δ_b / d_b`.
  have hy : |yB g k L t s b ℓ| = |(ℓ : ℝ)| * deltaB g k L t s b / dB g k s b := by
    unfold yB; rw [abs_div, abs_mul, abs_of_pos hδpos, abs_of_pos hdpos]
  have hy2 : |yB g k L t s b ℓ| ≤ 1 / 2 := by
    rw [hy, div_le_iff₀ hdpos]; linarith
  have hdist : distZ (yB g k L t s b ℓ) = |(ℓ : ℝ)| * deltaB g k L t s b / dB g k s b := by
    rw [distZ_eq_abs_of_abs_le_half hy2, hy]
  have hpos : 0 < 2 * distZ (yB g k L t s b ℓ) := by rw [hdist]; positivity
  unfold PhiB
  calc minDiv (dB g k s b * Zplus g k L t) ((g : ℝ) ^ s) (2 * distZ (yB g k L t s b ℓ))
      ≤ (g : ℝ) ^ s / (2 * distZ (yB g k L t s b ℓ)) := minDiv_le_div hpos.ne'
    _ = (g : ℝ) ^ s * dB g k s b / (2 * |(ℓ : ℝ)| * deltaB g k L t s b) := by
        rw [hdist]; field_simp
    _ ≤ (g : ℝ) ^ s * dB g k s b / (2 * |(ℓ : ℝ)| * (k * (g : ℝ) ^ s / (g * Zt g k L t))) := by
        gcongr
    _ = g * Zt g k L t * dB g k s b / (2 * k * |(ℓ : ℝ)|) := by
        field_simp

/-- Auxiliary for [HFF 73].  `m_g(n) ≥ 1`. -/
private lemma mg_pos (g n : ℕ) : 0 < mg g n :=
  prod_pos fun _ hp => pow_pos (Nat.pos_of_mem_primeFactors hp) _

/-- Auxiliary for [HFF 73].  `m_g(n)` divides `n` (for `n ≠ 0`). -/
private lemma mg_dvd (g : ℕ) {n : ℕ} (hn : n ≠ 0) : mg g n ∣ n := by
  unfold mg
  have h1 : ∏ p ∈ g.primeFactors, p ^ n.factorization p =
      ∏ p ∈ g.primeFactors ∩ n.primeFactors, p ^ n.factorization p := by
    refine (prod_subset inter_subset_left fun p hp hpn => ?_).symm
    have : p ∉ n.primeFactors := fun h => hpn (mem_inter.mpr ⟨hp, h⟩)
    rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at this
    rw [this, pow_zero]
  rw [h1]
  calc ∏ p ∈ g.primeFactors ∩ n.primeFactors, p ^ n.factorization p
      ∣ ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
        prod_dvd_prod_of_subset _ _ _ inter_subset_right
    _ = n := by
        conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
        rw [Finsupp.prod, Nat.support_factorization]

/-- Auxiliary for [HFF 73].  All prime factors of `m_g(n)` divide `g`. -/
private lemma mg_primeFactors (g n : ℕ) : (mg g n).primeFactors ⊆ g.primeFactors := by
  intro q hq
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hqd := Nat.dvd_of_mem_primeFactors hq
  unfold mg at hqd
  obtain ⟨p, hp, hqp'⟩ := (Prime.dvd_finsetProd_iff hqp.prime _).mp hqd
  have := (Nat.prime_dvd_prime_iff_eq hqp (Nat.prime_of_mem_primeFactors hp)).mp
    (hqp.dvd_of_dvd_pow hqp')
  rwa [this]

/-- **[HFF 73] Lemma (Sum of d_b).**  `∑_{b∈ℬ} d_b ≤ k τ(D) D^{k-2} g^t`. -/
theorem sum_dB (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) {L t s : ℕ} {ℓ : ℤ} {D : ℝ}
    {B : Finset ℕ} (hF : FreqSetting g k L t s ℓ D B) :
    ∑ b ∈ B, (dB g k s b : ℝ) ≤ k * tauG g D * D ^ (k - 2) * (g : ℝ) ^ t := by
  obtain ⟨-, -, -, hD1, -, -, hB⟩ := hF
  -- (The HFF also notes `m ∣ g^t` (Lemma 67), which makes the count of multiples exact; for the
  -- upper bound `⌊g^t/m⌋ ≤ g^t/m` it is not needed.)
  -- `M`: the integers `1 ≤ m ≤ D` all of whose prime factors divide `g`; `#M = τ(D)`.
  set M := (Icc 1 ⌊D⌋₊).filter (fun m => m.primeFactors ⊆ g.primeFactors) with hM
  have hτ : tauG g D = M.card := rfl
  have hnode0 : ∀ b ∈ B, b ≠ 0 := by
    intro b hb h0
    apply (hB b hb).1.2
    rw [h0, zero_pow (by omega)]
    exact dvd_zero g
  -- `b ↦ m_g(b)` maps `ℬ` into `M`.
  have hmaps : ∀ b ∈ B, mg g b ∈ M := by
    intro b hb
    rw [hM, mem_filter, mem_Icc]
    exact ⟨⟨mg_pos g b, Nat.le_floor (hB b hb).2⟩, mg_primeFactors g b⟩
  -- `d_b ≤ k m_g(b)^{k-1}` (Lemma 62).
  have hdb : ∀ b ∈ B, (dB g k s b : ℝ) ≤ k * (mg g b : ℝ) ^ (k - 1) := by
    intro b hb
    have h := (dB_dvd (s := s) hg hk (hB b hb).1).2
    have hpos : 0 < k * mg g b ^ (k - 1) := Nat.mul_pos (by omega) (pow_pos (mg_pos g b) _)
    exact_mod_cast Nat.le_of_dvd hpos h
  -- For `m ∈ M`: the `b ∈ ℬ` with `m_g(b) = m` are multiples of `m` in `(0, g^t)`.
  have hfib : ∀ m ∈ M, ∑ b ∈ B with mg g b = m, (k : ℝ) * (mg g b : ℝ) ^ (k - 1) ≤
      k * D ^ (k - 2) * (g : ℝ) ^ t := by
    intro m hm
    rw [hM, mem_filter, mem_Icc] at hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.1.1
    have hmD : (m : ℝ) ≤ D := (Nat.cast_le.mpr hm.1.2).trans (Nat.floor_le (by linarith))
    rw [sum_congr rfl (fun b hb => by rw [(mem_filter.mp hb).2]), sum_const, nsmul_eq_mul]
    have hsub : B.filter (fun b => mg g b = m) ⊆ (Ioc 0 (g ^ t)).filter (fun x => m ∣ x) := by
      intro b hb
      rw [mem_filter] at hb ⊢
      refine ⟨mem_Ioc.mpr ⟨Nat.pos_of_ne_zero (hnode0 b hb.1), (hB b hb.1).1.1.le⟩, ?_⟩
      rw [← hb.2]; exact mg_dvd g (hnode0 b hb.1)
    have hcard := card_le_card hsub
    rw [Nat.Ioc_filter_dvd_card_eq_div] at hcard
    have hcard' : ((B.filter (fun b => mg g b = m)).card : ℝ) ≤ (g : ℝ) ^ t / m := by
      calc ((B.filter (fun b => mg g b = m)).card : ℝ) ≤ ((g ^ t / m : ℕ) : ℝ) := by
            exact_mod_cast hcard
        _ ≤ ((g ^ t : ℕ) : ℝ) / m := Nat.cast_div_le
        _ = (g : ℝ) ^ t / m := by push_cast; rfl
    have hpow : (m : ℝ) ^ (k - 1) = (m : ℝ) ^ (k - 2) * m := by
      rw [← pow_succ]; congr 1; omega
    calc ((B.filter (fun b => mg g b = m)).card : ℝ) * (k * (m : ℝ) ^ (k - 1))
        ≤ (g : ℝ) ^ t / m * (k * (m : ℝ) ^ (k - 1)) := by gcongr
      _ = k * (m : ℝ) ^ (k - 2) * (g : ℝ) ^ t := by
          rw [hpow]; field_simp
      _ ≤ k * D ^ (k - 2) * (g : ℝ) ^ t := by gcongr
  calc ∑ b ∈ B, (dB g k s b : ℝ) ≤ ∑ b ∈ B, (k : ℝ) * (mg g b : ℝ) ^ (k - 1) := sum_le_sum hdb
    _ = ∑ m ∈ M, ∑ b ∈ B with mg g b = m, (k : ℝ) * (mg g b : ℝ) ^ (k - 1) :=
        (sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ m ∈ M, (k : ℝ) * D ^ (k - 2) * (g : ℝ) ^ t := sum_le_sum hfib
    _ = k * tauG g D * D ^ (k - 2) * (g : ℝ) ^ t := by
        rw [sum_const, nsmul_eq_mul, hτ]; ring

end PalindromicPowers

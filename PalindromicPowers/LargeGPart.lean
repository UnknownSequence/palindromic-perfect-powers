import PalindromicPowers.Spacing

/-!
# HFF blocks 87–89: the large g-part
-/

namespace PalindromicPowers

open Finset Real

variable {g k : ℕ}

/-- Auxiliary for [HFF 88]. `m_g(n) ≠ 0`. -/
private theorem mg_ne_zero' (g n : ℕ) : mg g n ≠ 0 := by
  unfold mg
  exact Finset.prod_ne_zero_iff.2 fun p hp => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero

/-- Auxiliary for [HFF 87]. Every prime factor of `m_g(n)` divides `g`. -/
private theorem mem_primeFactors_of_dvd_mg {g n p : ℕ} (hp : p.Prime) (h : p ∣ mg g n) :
    p ∈ g.primeFactors := by
  unfold mg at h
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 h
  have := (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hq)).1
    (hp.dvd_of_dvd_pow hpq)
  rwa [this]

/-- Auxiliary for [HFF 89]. `m_g(n) ∣ n` for `n ≠ 0`. -/
private theorem mg_dvd_self (g : ℕ) {n : ℕ} (hn : n ≠ 0) : mg g n ∣ n := by
  have h1 : mg g n = ∏ p ∈ g.primeFactors ∩ n.primeFactors, p ^ n.factorization p := by
    unfold mg
    refine (Finset.prod_subset Finset.inter_subset_left fun p hp hpn => ?_).symm
    have : p ∉ n.primeFactors := fun h => hpn (Finset.mem_inter.2 ⟨hp, h⟩)
    rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at this
    rw [this, pow_zero]
  have h2 : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    rw [Finsupp.prod, Nat.support_factorization]
  rw [h1]
  calc _ ∣ ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
        Finset.prod_dvd_prod_of_subset _ _ _ Finset.inter_subset_right
    _ = n := h2

/-- Auxiliary for [HFF 87]. If all prime factors of `m` are at most `P`, `D ≥ 1` and `m > D`,
then `m` has a divisor `m'` with `D < m' ≤ PD` (peel off one prime factor at a time). -/
private theorem window_aux (P : ℕ) {D : ℝ} (hD : 1 ≤ D) :
    ∀ m : ℕ, (∀ p, p.Prime → p ∣ m → p ≤ P) → D < m →
      ∃ m' : ℕ, m' ∣ m ∧ D < m' ∧ (m' : ℝ) ≤ P * D := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hP hDm
  by_cases hle : (m : ℝ) ≤ P * D
  · exact ⟨m, dvd_rfl, hDm, hle⟩
  rw [not_le] at hle
  have hm1 : 1 < m := by
    have : (1 : ℝ) < m := lt_of_le_of_lt hD hDm
    exact_mod_cast this
  set p := m.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime hm1.ne'
  have hpm : p ∣ m := Nat.minFac_dvd m
  have hpP : p ≤ P := hP p hp hpm
  obtain ⟨m₁, hm₁⟩ := hpm
  have hm₁0 : 0 < m₁ := by
    rcases Nat.eq_zero_or_pos m₁ with h | h
    · rw [h, mul_zero] at hm₁; omega
    · exact h
  have hlt : m₁ < m := by
    rw [hm₁]; have := hp.two_le; nlinarith
  have hDm₁ : D < m₁ := by
    have hP0 : (0 : ℝ) < P := by
      have : 2 ≤ P := le_trans hp.two_le hpP
      exact_mod_cast (by omega : 0 < P)
    have h1 : (P : ℝ) * D < P * m₁ := by
      calc (P : ℝ) * D < m := hle
        _ = (p : ℝ) * m₁ := by rw [hm₁]; push_cast; ring
        _ ≤ P * m₁ := by gcongr
    exact lt_of_mul_lt_mul_left h1 hP0.le
  obtain ⟨m', hdvd, hD', hle'⟩ := ih m₁ hlt
    (fun q hq hqd => hP q hq (hqd.trans ⟨p, by rw [hm₁, mul_comm]⟩)) hDm₁
  exact ⟨m', hdvd.trans ⟨p, by rw [hm₁, mul_comm]⟩, hD', hle'⟩

/-- **[HFF 87] Lemma (A divisor in a window).**  If `n ≠ 0`, `D ≥ 1` and `m_g(n) > D`, then
`m_g(n)` has a divisor `m'` with `D < m' ≤ PD`. -/
theorem divisor_window (hg : 2 ≤ g) {D : ℝ} (hD : 1 ≤ D) {n : ℕ} (hn : n ≠ 0)
    (hm : D < mg g n) :
    ∃ m' : ℕ, m' ∣ mg g n ∧ D < m' ∧ (m' : ℝ) ≤ Pmax g * D := by
  -- Lemma 87: every prime factor of `m_g(n)` divides `g`, hence is at most `P`.
  refine window_aux (Pmax g) hD (mg g n) (fun p hp hpd => ?_) hm
  have := mem_primeFactors_of_dvd_mg hp hpd
  exact Finset.le_sup (f := id) this

/-- **[HFF 88]** `t' = ⌈L/(2k)⌉`, the integer with `X^{1/2} ≤ g^{t'} < g X^{1/2}`. -/
noncomputable def tPrime (k L : ℕ) : ℕ := ⌈(L : ℝ) / (2 * k)⌉₊

/-- **[HFF 88] Lemma (A good level).**  Let `L ≥ 1` and `D ≥ 1` with `PD ≤ X^{log 2/(2 log g)}`.
Then `X^{1/2} ≤ g^{t'} < g X^{1/2}`, `1 ≤ t' ≤ L`, `Z(t') ≤ 1`, and every divisor `m' ≤ PD`
of some `m_g(n)` divides `g^{t'}`. -/
theorem good_level (hg : 2 ≤ g) (hk : 2 ≤ k) {L : ℕ} (hL : 1 ≤ L) {D : ℝ} (hD : 1 ≤ D)
    (hPD : Pmax g * D ≤ Xr g k L ^ (Real.log 2 / (2 * Real.log g))) :
    Real.sqrt (Xr g k L) ≤ (g : ℝ) ^ tPrime k L ∧ (g : ℝ) ^ tPrime k L < g * Real.sqrt (Xr g k L) ∧
    1 ≤ tPrime k L ∧ tPrime k L ≤ L ∧ Zt g k L (tPrime k L) ≤ 1 ∧
    ∀ n m' : ℕ, n ≠ 0 → m' ∣ mg g n → (m' : ℝ) ≤ Pmax g * D → m' ∣ g ^ tPrime k L := by
  set a : ℝ := (L : ℝ) / (2 * k) with ha_def
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hL0 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have ha : 0 < a := by rw [ha_def]; positivity
  have hgR : (1 : ℝ) < g := by exact_mod_cast (by omega : 1 < g)
  have hg0 : (0 : ℝ) < g := by linarith
  have ht' : tPrime k L = ⌈a⌉₊ := rfl
  have hsqrt : Real.sqrt (Xr g k L) = (g : ℝ) ^ a := by
    unfold Xr
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hg0.le, ha_def]
    congr 1
    field_simp
  have hpow : (g : ℝ) ^ tPrime k L = (g : ℝ) ^ (tPrime k L : ℝ) := (Real.rpow_natCast _ _).symm
  -- `X^{1/2} ≤ g^{t'} < g X^{1/2}`
  have h1 : Real.sqrt (Xr g k L) ≤ (g : ℝ) ^ tPrime k L := by
    rw [hsqrt, hpow, ht']
    exact Real.rpow_le_rpow_of_exponent_le hgR.le (Nat.le_ceil a)
  have h2 : (g : ℝ) ^ tPrime k L < g * Real.sqrt (Xr g k L) := by
    rw [hsqrt, hpow, ht', mul_comm, ← Real.rpow_add_one hg0.ne']
    exact Real.rpow_lt_rpow_of_exponent_lt hgR (Nat.ceil_lt_add_one ha.le)
  -- `1 ≤ t' ≤ L`
  have h3 : 1 ≤ tPrime k L := by rw [ht']; exact Nat.one_le_ceil_iff.2 ha
  have h4 : tPrime k L ≤ L := by
    rw [ht']
    refine Nat.ceil_le.2 ?_
    rw [ha_def]
    refine div_le_self (by positivity) ?_
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  -- `Z(t') ≤ 1`
  have h5 : Zt g k L (tPrime k L) ≤ 1 := by
    unfold Zt
    have hX0 : 0 ≤ Xr g k L := by unfold Xr; positivity
    rw [div_le_one (by positivity), pow_mul', ← Real.sq_sqrt hX0]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  -- `X^{log 2/(2 log g)} = 2^{L/(2k)}`
  have hXc : Xr g k L ^ (Real.log 2 / (2 * Real.log g)) = (2 : ℝ) ^ a := by
    have hlg : Real.log g ≠ 0 := (Real.log_pos hgR).ne'
    unfold Xr
    rw [← Real.rpow_mul hg0.le, Real.rpow_def_of_pos hg0, Real.rpow_def_of_pos two_pos, ha_def]
    congr 1
    field_simp
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  -- every divisor `m' ≤ PD` of some `m_g(n)` divides `g^{t'}`
  intro n m' hn hdvd hle
  have hm0 : m' ≠ 0 := fun h => mg_ne_zero' g n (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
  have hgt0 : g ^ tPrime k L ≠ 0 := pow_ne_zero _ (by omega)
  rw [← Nat.factorization_prime_le_iff_dvd hm0 hgt0]
  intro p hp
  by_cases hv : m'.factorization p = 0
  · rw [hv]; exact Nat.zero_le _
  have hpm : p ∣ m' := Nat.dvd_of_factorization_pos hv
  have hpg : p ∈ g.primeFactors := mem_primeFactors_of_dvd_mg hp (hpm.trans hdvd)
  have hvg : 1 ≤ g.factorization p :=
    hp.factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hpg)
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  rw [← Nat.pow_le_pow_iff_right hp.one_lt]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have key : ((p ^ m'.factorization p : ℕ) : ℝ) ≤ ((p ^ (tPrime k L * g.factorization p) : ℕ) : ℝ) :=
    calc ((p ^ m'.factorization p : ℕ) : ℝ) ≤ m' := by exact_mod_cast Nat.ordProj_le p hm0
      _ ≤ Pmax g * D := hle
      _ ≤ (2 : ℝ) ^ a := hPD.trans hXc.le
      _ ≤ (2 : ℝ) ^ (tPrime k L : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le one_le_two (by rw [ht']; exact Nat.le_ceil a)
      _ = (2 : ℝ) ^ tPrime k L := Real.rpow_natCast _ _
      _ ≤ (p : ℝ) ^ tPrime k L := pow_le_pow_left₀ zero_le_two hp2 _
      _ ≤ (p : ℝ) ^ (tPrime k L * g.factorization p) :=
          pow_le_pow_right₀ (by linarith) (Nat.le_mul_of_pos_right _ hvg)
      _ = ((p ^ (tPrime k L * g.factorization p) : ℕ) : ℝ) := by push_cast; ring
  exact_mod_cast key

/-- Auxiliary for [HFF 89].  The nodes of level `t` that are multiples of `m` number at most
`g^t / m`. -/
private theorem card_node_multiples_le (hk : 2 ≤ k) {t m : ℕ} :
    ((range (g ^ t)).filter (fun b => m ∣ b ∧ IsNode g k t b)).card ≤ g ^ t / m := by
  have hsub : (range (g ^ t)).filter (fun b => m ∣ b ∧ IsNode g k t b) ⊆
      (Icc 1 (g ^ t / m)).image (fun j => m * j) := by
    intro b hb
    rw [mem_filter, mem_range] at hb
    obtain ⟨hbt, hmb, hnode⟩ := hb
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hnode.2 (by rw [zero_pow (by omega)]; exact dvd_zero g)
    rw [mem_image]
    refine ⟨b / m, mem_Icc.2 ⟨?_, Nat.div_le_div_right hbt.le⟩, Nat.mul_div_cancel' hmb⟩
    rcases Nat.eq_zero_or_pos (b / m) with h | h
    · exact absurd (by rw [← Nat.mul_div_cancel' hmb, h, mul_zero]) hb0
    · exact h
  calc _ ≤ ((Icc 1 (g ^ t / m)).image (fun j => m * j)).card := card_le_card hsub
    _ ≤ (Icc 1 (g ^ t / m)).card := card_image_le
    _ = g ^ t / m := by rw [Nat.card_Icc, Nat.add_sub_cancel]

/-- **[HFF 89] Lemma (Large g-part).**  Under the hypotheses of Lemma 88,
`#{x ∈ 𝒬_L : m_g(x) > D} ≤ τ(PD)(g/k + 1) g X^{1/2}/D`. -/
theorem large_gpart (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) {L : ℕ} (hL : 1 ≤ L) {D : ℝ}
    (hD : 1 ≤ D) (hPD : Pmax g * D ≤ Xr g k L ^ (Real.log 2 / (2 * Real.log g))) :
    (((powSet g k L).filter (fun x => D < mg g x)).card : ℝ) ≤
      tauG g (Pmax g * D) * ((g : ℝ) / k + 1) * g * Real.sqrt (Xr g k L) / D := by
  obtain ⟨-, hX2, ht1, htL, hZ, hdiv⟩ := good_level hg hk hL hD hPD
  set t' := tPrime k L with ht'
  set S := (powSet g k L).filter (fun x => D < mg g x) with hS
  -- the possible values of `m'`
  set M := (Icc 1 ⌊(Pmax g : ℝ) * D⌋₊).filter
    (fun m : ℕ => m.primeFactors ⊆ g.primeFactors ∧ D < (m : ℝ)) with hM
  -- the nodes of level `t'` that are multiples of `m`
  set B : ℕ → Finset ℕ := fun m => (range (g ^ t')).filter (fun b => m ∣ b ∧ IsNode g k t' b)
    with hB
  have hD0 : (0 : ℝ) < D := by linarith
  -- each `x` lies in a node `b = x mod g^{t'}` that is a multiple of some `m' ∈ M`
  have hsub : S ⊆ M.biUnion (fun m => (B m).biUnion (fun b => nodeElems g k L t' b)) := by
    intro x hxS
    rw [hS, mem_filter] at hxS
    obtain ⟨hx, hxD⟩ := hxS
    obtain ⟨hnode, hInI, -⟩ := tree hg hk ht1 htL hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      apply hnode.2
      rw [Nat.zero_mod, zero_pow (by omega)]
      exact dvd_zero g
    obtain ⟨m', hm'dvd, hDm', hm'le⟩ := divisor_window hg hD hx0 hxD
    have hm'g : m' ∣ g ^ t' := hdiv x m' hx0 hm'dvd hm'le
    have hm'x : m' ∣ x := hm'dvd.trans (mg_dvd_self g hx0)
    have hm'1 : 1 ≤ m' := by
      have : (1 : ℝ) < m' := lt_of_le_of_lt hD hDm'
      exact_mod_cast this.le
    rw [mem_biUnion]
    refine ⟨m', ?_, ?_⟩
    · rw [hM, mem_filter, mem_Icc]
      refine ⟨⟨hm'1, Nat.le_floor hm'le⟩, fun p hp => ?_, hDm'⟩
      exact mem_primeFactors_of_dvd_mg (Nat.prime_of_mem_primeFactors hp)
        ((Nat.dvd_of_mem_primeFactors hp).trans hm'dvd)
    · rw [mem_biUnion]
      refine ⟨x % g ^ t', ?_, ?_⟩
      · rw [hB, mem_filter, mem_range]
        exact ⟨Nat.mod_lt _ (pos_of_ne_zero (pow_ne_zero _ (by omega))),
          (Nat.dvd_mod_iff hm'g).2 hm'x, hnode⟩
      · unfold nodeElems
        rw [mem_filter]
        exact ⟨(mem_filter.1 hx).1, rfl, hInI⟩
  -- `Z_b ≤ g/k + 1` for every node of level `t'` (Lemma 35 and `Z(t') ≤ 1`)
  have hZb : ∀ b, IsNode g k t' b → (Zb g k L t' b : ℝ) ≤ (g : ℝ) / k + 1 := by
    intro b hb
    have h := (node_sizes KR hg hk ht1 htL hb).2.2.2
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have : (g : ℝ) * Zt g k L t' / k ≤ (g : ℝ) / k :=
      div_le_div_of_nonneg_right (mul_le_of_le_one_right (Nat.cast_nonneg g) hZ) hk0
    linarith
  -- at most `g^{t'}/m' < g X^{1/2}/D` nodes per `m'`
  have hBm : ∀ m ∈ M, ((B m).card : ℝ) ≤ (g : ℝ) * Real.sqrt (Xr g k L) / D := by
    intro m hm
    rw [hM, mem_filter, mem_Icc] at hm
    obtain ⟨⟨hm1, -⟩, -, hDm⟩ := hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    calc ((B m).card : ℝ) ≤ ((g ^ t' / m : ℕ) : ℝ) := by
          exact_mod_cast card_node_multiples_le hk
      _ ≤ ((g ^ t' : ℕ) : ℝ) / m := Nat.cast_div_le
      _ = (g : ℝ) ^ t' / m := by push_cast; ring
      _ ≤ (g : ℝ) ^ t' / D := div_le_div_of_nonneg_left (by positivity) hD0 hDm.le
      _ ≤ (g : ℝ) * Real.sqrt (Xr g k L) / D := div_le_div_of_nonneg_right hX2.le hD0.le
  -- at most `τ(PD)` values of `m'`
  have hMcard : M.card ≤ tauG g (Pmax g * D) := by
    unfold tauG
    refine card_le_card fun m hm => ?_
    rw [hM, mem_filter] at hm
    exact mem_filter.2 ⟨hm.1, hm.2.1⟩
  -- the count
  have hcount : (S.card : ℝ) ≤ ∑ m ∈ M, ∑ b ∈ B m, (Zb g k L t' b : ℝ) := by
    have h1 := card_le_card hsub
    have h2 := card_biUnion_le (s := M) (t := fun m => (B m).biUnion (fun b => nodeElems g k L t' b))
    have h3 : ∀ m ∈ M, ((B m).biUnion (fun b => nodeElems g k L t' b)).card ≤
        ∑ b ∈ B m, Zb g k L t' b := fun m _ => card_biUnion_le
    have h4 := sum_le_sum h3
    exact_mod_cast h1.trans (h2.trans h4)
  have hsum : ∑ m ∈ M, ∑ b ∈ B m, (Zb g k L t' b : ℝ) ≤
      ∑ m ∈ M, (g : ℝ) * Real.sqrt (Xr g k L) / D * ((g : ℝ) / k + 1) := by
    refine sum_le_sum fun m hm => ?_
    calc ∑ b ∈ B m, (Zb g k L t' b : ℝ) ≤ ∑ b ∈ B m, ((g : ℝ) / k + 1) := by
          refine sum_le_sum fun b hb => hZb b ?_
          rw [hB, mem_filter] at hb
          exact hb.2.2
      _ = ((B m).card : ℝ) * ((g : ℝ) / k + 1) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (g : ℝ) * Real.sqrt (Xr g k L) / D * ((g : ℝ) / k + 1) := by
          gcongr
          exact hBm m hm
  have hfin : ∑ m ∈ M, (g : ℝ) * Real.sqrt (Xr g k L) / D * ((g : ℝ) / k + 1) ≤
      tauG g (Pmax g * D) * ((g : ℝ) / k + 1) * g * Real.sqrt (Xr g k L) / D := by
    rw [sum_const, nsmul_eq_mul]
    have hMc : (M.card : ℝ) ≤ tauG g (Pmax g * D) := by exact_mod_cast hMcard
    have hnn : 0 ≤ (g : ℝ) * Real.sqrt (Xr g k L) / D * ((g : ℝ) / k + 1) := by positivity
    calc (M.card : ℝ) * ((g : ℝ) * Real.sqrt (Xr g k L) / D * ((g : ℝ) / k + 1))
        ≤ tauG g (Pmax g * D) * ((g : ℝ) * Real.sqrt (Xr g k L) / D * ((g : ℝ) / k + 1)) :=
          mul_le_mul_of_nonneg_right hMc hnn
      _ = _ := by ring
  exact hcount.trans (hsum.trans hfin)

end PalindromicPowers

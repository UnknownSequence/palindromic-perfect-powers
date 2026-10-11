import PalindromicPowers.Residues

/-!
# HFF blocks 60–68: g-parts and the count of roots
-/

namespace PalindromicPowers

open Finset Real

variable {g k : ℕ}

/-- **[HFF 60] Definition (g-parts).**  `m_g(n) = ∏_{p∣g} p^{v_p(n)}`. -/
def mg (g n : ℕ) : ℕ := ∏ p ∈ g.primeFactors, p ^ n.factorization p

/-- **[HFF 60]** `ω(g)`, the number of primes dividing `g`. -/
def omegaG (g : ℕ) : ℕ := g.primeFactors.card

/-- **[HFF 60]** `P`, the largest prime dividing `g`. -/
def Pmax (g : ℕ) : ℕ := g.primeFactors.sup id

/-- **[HFF 60]** `τ(D)`, the number of integers `1 ≤ m ≤ D` all of whose prime factors
divide `g`. -/
noncomputable def tauG (g : ℕ) (D : ℝ) : ℕ := ((Icc 1 ⌊D⌋₊).filter (fun m => m.primeFactors ⊆ g.primeFactors)).card


/-- Auxiliary for [HFF 61].  If `p` is not a prime factor of `n`, then `v_p(n) = 0`. -/
private lemma factorization_eq_zero_of_notMem {n p : ℕ} (h : p ∉ n.primeFactors) :
    n.factorization p = 0 := by
  rwa [← Nat.support_factorization, Finsupp.notMem_support_iff] at h

/-- **[HFF 61] Lemma (Few g-smooth numbers).**  `τ` is non-decreasing, and
`τ(D) ≤ (1 + log₂ D)^{ω(g)}` for `D ≥ 1`. -/
theorem tauG_bound (hg : 2 ≤ g) :
    Monotone (tauG g) ∧ ∀ D : ℝ, 1 ≤ D → (tauG g D : ℝ) ≤ (1 + Real.logb 2 D) ^ omegaG g := by
  refine ⟨fun D D' hDD' => ?_, fun D hD => ?_⟩
  · -- Monotonicity is clear.
    unfold tauG
    exact Finset.card_le_card
      (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor hDD')))
  · -- Each `m` counted is `∏_{p ∣ g} p^{e_p}` with `p^{e_p} ≤ D`, so `0 ≤ e_p ≤ log₂ D`.
    set E := ⌊Real.logb 2 D⌋₊ with hE
    have hlog : 0 ≤ Real.logb 2 D := Real.logb_nonneg (by norm_num) hD
    have key : tauG g D ≤ (E + 1) ^ omegaG g := by
      unfold tauG omegaG
      calc _ ≤ (g.primeFactors.pi (fun _ => range (E + 1))).card := by
            apply Finset.card_le_card_of_injOn
              (fun m p (_ : p ∈ g.primeFactors) => m.factorization p)
            · intro m hm
              simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Icc] at hm
              simp only [Finset.mem_coe, Finset.mem_pi, Finset.mem_range]
              intro p hp
              have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
              -- `2^{e_p} ≤ p^{e_p} ≤ m ≤ D`
              have h1 : 2 ^ m.factorization p ≤ m :=
                (Nat.pow_le_pow_left hp2 _).trans (Nat.ordProj_le p (by omega))
              have h2 : (2 : ℝ) ^ (m.factorization p : ℝ) ≤ D := by
                rw [Real.rpow_natCast]
                calc (2 : ℝ) ^ m.factorization p ≤ m := by exact_mod_cast h1
                  _ ≤ ⌊D⌋₊ := by exact_mod_cast hm.1.2
                  _ ≤ D := Nat.floor_le (by linarith)
              have h3 : (m.factorization p : ℝ) ≤ Real.logb 2 D :=
                (Real.le_logb_iff_rpow_le (by norm_num) (by linarith)).2 h2
              have := Nat.le_floor h3
              omega
            · intro m hm m' hm' hmm'
              simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Icc] at hm hm'
              apply Nat.eq_of_factorization_eq (by omega) (by omega)
              intro p
              by_cases hp : p ∈ g.primeFactors
              · exact congrFun (congrFun hmm' p) hp
              · rw [factorization_eq_zero_of_notMem (fun h => hp (hm.2 h)),
                  factorization_eq_zero_of_notMem (fun h => hp (hm'.2 h))]
        _ = (E + 1) ^ g.primeFactors.card := by
            rw [Finset.card_pi, Finset.prod_const, Finset.card_range]
    calc (tauG g D : ℝ) ≤ ((E + 1) ^ omegaG g : ℕ) := by exact_mod_cast key
      _ = (1 + (E : ℝ)) ^ omegaG g := by push_cast; ring
      _ ≤ (1 + Real.logb 2 D) ^ omegaG g := by
          gcongr
          linarith [Nat.floor_le hlog]

/-- Auxiliary for [HFF 62].  For every finite set `S`, `∏_{p ∈ S} p^{v_p(n)}` divides `n`. -/
private lemma prod_pow_factorization_dvd (S : Finset ℕ) (n : ℕ) :
    ∏ p ∈ S, p ^ n.factorization p ∣ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact dvd_zero _
  have h1 : ∏ p ∈ S ∩ n.primeFactors, p ^ n.factorization p = ∏ p ∈ S, p ^ n.factorization p := by
    apply Finset.prod_subset Finset.inter_subset_left
    intro p hpS hp
    have : p ∉ n.primeFactors := fun h => hp (Finset.mem_inter.2 ⟨hpS, h⟩)
    rw [factorization_eq_zero_of_notMem this, pow_zero]
  have h2 : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
    have := Nat.prod_factorization_pow_eq_self hn.ne'
    rwa [Finsupp.prod, Nat.support_factorization] at this
  rw [← h1]
  calc ∏ p ∈ S ∩ n.primeFactors, p ^ n.factorization p
        ∣ ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
          Finset.prod_dvd_prod_of_subset _ _ _ Finset.inter_subset_right
    _ = n := h2

/-- Auxiliary for [HFF 62].  `m_g(b) ∣ b`. -/
private lemma mg_dvd (g b : ℕ) : mg g b ∣ b := prod_pow_factorization_dvd _ _

/-- Auxiliary for [HFF 62].  For `b ≠ 0`, `u = b / m_g(b)` is coprime to `g`. -/
private lemma coprime_div_mg (hg : g ≠ 0) {b : ℕ} (hb : b ≠ 0) : Nat.Coprime (b / mg g b) g := by
  apply Nat.coprime_of_dvd
  intro p hp hpu hpg
  have hpg' : p ∈ g.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpg, hg⟩
  have h1 : p ^ b.factorization p ∣ mg g b := Finset.dvd_prod_of_mem _ hpg'
  have h2 : p ^ (b.factorization p + 1) ∣ b :=
    calc p ^ (b.factorization p + 1) = p ^ b.factorization p * p := pow_succ _ _
      _ ∣ mg g b * (b / mg g b) := mul_dvd_mul h1 hpu
      _ = b := Nat.mul_div_cancel' (mg_dvd g b)
  exact Nat.pow_succ_factorization_not_dvd hb hp h2

/-- Auxiliary for [HFF 62].  A node is nonzero. -/
private lemma node_ne_zero (hk : 1 ≤ k) {t b : ℕ} (hb : IsNode g k t b) : b ≠ 0 := by
  rintro rfl
  exact hb.2 (by rw [zero_pow (by omega)]; exact dvd_zero g)

/-- **[HFF 62] Lemma (Common factor of β_b).**  For a node `b` with `m = m_g(b)`:
`d_b ∣ Q` and `d_b ∣ k m^{k-1}`. -/
theorem dB_dvd (hg : 2 ≤ g) (hk : 2 ≤ k) {t s b : ℕ} (hb : IsNode g k t b) :
    dB g k s b ∣ g ^ s ∧ dB g k s b ∣ k * mg g b ^ (k - 1) := by
  refine ⟨Nat.gcd_dvd_right _ _, ?_⟩
  -- As `g ∤ b^k`, `b ≠ 0`; write `b = m u` with `gcd(u, g) = 1`.
  have hb0 : b ≠ 0 := node_ne_zero (by omega) hb
  have hbmu : b = mg g b * (b / mg g b) := (Nat.mul_div_cancel' (mg_dvd g b)).symm
  have hu : Nat.Coprime (b / mg g b) g := coprime_div_mg (by omega) hb0
  -- `d_b ∣ β_b ≡ k b^{k-1} = k m^{k-1} u^{k-1} (mod Q)`
  have h1 : dB g k s b ∣ k * mg g b ^ (k - 1) * (b / mg g b) ^ (k - 1) := by
    have : dB g k s b ∣ k * b ^ (k - 1) :=
      (Nat.dvd_mod_iff (Nat.gcd_dvd_right _ _)).1 (Nat.gcd_dvd_left _ _)
    have e : k * b ^ (k - 1) = k * mg g b ^ (k - 1) * (b / mg g b) ^ (k - 1) := by
      conv_lhs => rw [hbmu]
      ring
    rwa [e] at this
  -- `u` is coprime to `Q`, so it can be dropped.
  have h2 : Nat.Coprime (dB g k s b) ((b / mg g b) ^ (k - 1)) :=
    (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _) (hu.pow_right s).symm).pow_right _
  exact h2.dvd_of_dvd_mul_right h1

/-- Auxiliary for [HFF 63].  For `2 ≤ i ≤ k` and `j ≥ 2`:
`v_p(k) + j + 1 ≤ v_p(C(k,i)) + i j`. -/
private lemma choose_factorization_bound {p : ℕ} (hp : p.Prime) {k i j : ℕ} (hi : 2 ≤ i)
    (hik : i ≤ k) (hj : 2 ≤ j) :
    k.factorization p + j + 1 ≤ (k.choose i).factorization p + i * j := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, i = r + 1 := ⟨i - 1, by omega⟩
  have hC : (n + 1).choose (r + 1) ≠ 0 := (Nat.choose_pos hik).ne'
  -- `i C(k,i) = k C(k-1,i-1)`, so `v_p(k) ≤ v_p(i) + v_p(C(k,i))`
  have h1 : n + 1 ∣ (r + 1) * (n + 1).choose (r + 1) :=
    ⟨n.choose r, by rw [Nat.add_one_mul_choose_eq]; ring⟩
  have h2 : (n + 1).factorization p ≤ ((r + 1) * (n + 1).choose (r + 1)).factorization p :=
    (Nat.factorization_le_iff_dvd (by omega) (by positivity)).2 h1 p
  rw [Nat.factorization_mul (by omega) hC, Finsupp.add_apply] at h2
  -- `v_p(i) ≤ i - 1`, as `p^{v_p(i)} ≤ i < 2^i ≤ p^i`
  have h3 : (r + 1).factorization p < r + 1 := by
    have : p ^ (r + 1).factorization p < p ^ (r + 1) :=
      calc p ^ (r + 1).factorization p ≤ r + 1 := Nat.ordProj_le p (by omega)
        _ < 2 ^ (r + 1) := Nat.lt_two_pow_self
        _ ≤ p ^ (r + 1) := Nat.pow_le_pow_left hp.two_le _
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).1 this
  -- `(i - 1)(j - 1) ≥ 1`
  have h4 : (r + 1) + j ≤ (r + 1) * j := by nlinarith
  have h3' : (r + 1).factorization p + 1 ≤ r + 1 := h3
  linarith

/-- **[HFF 63] Lemma (Binomial congruence).**  For a prime `p`, `j ≥ 2` and `u, w ∈ ℤ`:
`(u + p^j w)^k ≡ u^k + k u^{k-1} p^j w (mod p^{v_p(k)+j+1})`. -/
theorem binomial_congr (k : ℕ) {p : ℕ} (hp : p.Prime) {j : ℕ} (hj : 2 ≤ j) (u w : ℤ) :
    (u + (p : ℤ) ^ j * w) ^ k ≡ u ^ k + k * u ^ (k - 1) * (p : ℤ) ^ j * w
      [ZMOD (p : ℤ) ^ (k.factorization p + j + 1)] := by
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd]
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k <;> simp
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
  -- The other terms are `C(k,i) u^{k-i} p^{ij} w^i`, `2 ≤ i ≤ k`.
  have hsum : (u + (p : ℤ) ^ j * w) ^ (n + 2) - (u ^ (n + 2) + ((n + 2 : ℕ) : ℤ) * u ^ (n + 2 - 1)
      * (p : ℤ) ^ j * w) = ∑ i ∈ range (n + 1),
        ((p : ℤ) ^ j * w) ^ (i + 2) * u ^ (n + 2 - (i + 2)) * ((n + 2).choose (i + 2) : ℤ) := by
    rw [add_comm u, add_pow, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one, pow_one,
      Nat.choose_one_right, Nat.sub_zero, zero_add]
    have : n + 2 - 1 = n + 1 := by omega
    rw [this]
    push_cast
    ring
  rw [hsum]
  apply Finset.dvd_sum
  intro i hi
  have hi' : i + 2 ≤ n + 2 := by simp only [Finset.mem_range] at hi; omega
  have hb := choose_factorization_bound hp (by omega : 2 ≤ i + 2) hi' hj
  set c := (n + 2).choose (i + 2)
  have hc : (p : ℤ) ^ c.factorization p ∣ (c : ℤ) := by
    exact_mod_cast Nat.ordProj_dvd c p
  have hpw : (p : ℤ) ^ ((i + 2) * j) ∣ ((p : ℤ) ^ j * w) ^ (i + 2) :=
    ⟨w ^ (i + 2), by rw [mul_pow, ← pow_mul, mul_comm j]⟩
  calc (p : ℤ) ^ ((n + 2).factorization p + j + 1)
        ∣ (p : ℤ) ^ (c.factorization p + (i + 2) * j) := pow_dvd_pow _ hb
    _ = (p : ℤ) ^ c.factorization p * (p : ℤ) ^ ((i + 2) * j) := pow_add _ _ _
    _ ∣ (c : ℤ) * ((p : ℤ) ^ j * w) ^ (i + 2) := mul_dvd_mul hc hpw
    _ ∣ ((p : ℤ) ^ j * w) ^ (i + 2) * u ^ (n + 2 - (i + 2)) * (c : ℤ) :=
        ⟨u ^ (n + 2 - (i + 2)), by ring⟩

/-- **[HFF 64] Lemma (Close roots agree).**  If `N > v_p(k)`, `p ∤ u`, `u^k ≡ u'^k (mod p^N)`
and `u ≡ u' (mod p²)`, then `u ≡ u' (mod p^{N-v_p(k)})`. -/
theorem close_roots_agree (hk : 1 ≤ k) {p : ℕ} (hp : p.Prime) {N : ℕ} (hN : k.factorization p < N)
    {u u' : ℤ} (hu : ¬ (p : ℤ) ∣ u) (hkN : u ^ k ≡ u' ^ k [ZMOD (p : ℤ) ^ N])
    (h2 : u ≡ u' [ZMOD (p : ℤ) ^ 2]) :
    u ≡ u' [ZMOD (p : ℤ) ^ (N - k.factorization p)] := by
  set v := k.factorization p with hv
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  -- write `k = p^v k'` with `p ∤ k'`
  have hkk' : (k : ℤ) = (p : ℤ) ^ v * ((k / p ^ v : ℕ) : ℤ) := by
    exact_mod_cast (Nat.ordProj_mul_ordCompl_eq_self k p).symm
  have hk' : ¬ (p : ℤ) ∣ ((k / p ^ v : ℕ) : ℤ) := by
    rw [Int.natCast_dvd_natCast]; exact Nat.not_dvd_ordCompl hp (by omega)
  -- We show `p^j ∣ u' - u` for every `j ≤ N - v`, by induction on `j`: if `p^j ∣ u' - u` with
  -- `2 ≤ j < N - v`, write `u' = u + p^j w`; Lemma 63 forces `p ∣ w`.
  suffices H : ∀ j, j ≤ N - v → (p : ℤ) ^ j ∣ u' - u from Int.modEq_iff_dvd.2 (H _ le_rfl)
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    by_cases hj2 : j + 1 ≤ 2
    · exact (pow_dvd_pow _ hj2).trans (Int.modEq_iff_dvd.1 h2)
    obtain ⟨w, hw⟩ := ih (by omega)
    have hu' : u + (p : ℤ) ^ j * w = u' := by rw [← hw]; ring
    -- Lemma 63: `u'^k ≡ u^k + k u^{k-1} p^j w (mod p^{v+j+1})`
    have hb := binomial_congr k hp (j := j) (by omega) u w
    rw [hu'] at hb
    have h3 : (p : ℤ) ^ (v + j + 1) ∣ (k : ℤ) * u ^ (k - 1) * (p : ℤ) ^ j * w := by
      have h4 : u ^ k ≡ u ^ k + k * u ^ (k - 1) * (p : ℤ) ^ j * w [ZMOD (p : ℤ) ^ (v + j + 1)] :=
        (hkN.of_dvd (pow_dvd_pow _ (by omega))).trans hb
      simpa using Int.modEq_iff_dvd.1 h4
    -- the valuation of `k u^{k-1} p^j w` would be `v + j` if `p ∤ w`
    have h5 : (p : ℤ) ^ (v + j) * p ∣ (p : ℤ) ^ (v + j) * (((k / p ^ v : ℕ) : ℤ) * u ^ (k - 1) * w) := by
      rw [← pow_succ]
      convert h3 using 1
      rw [hkk']
      ring
    have h6 := (mul_dvd_mul_iff_left (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))).1 h5
    have hpw : (p : ℤ) ∣ w := by
      rcases hpZ.dvd_or_dvd h6 with h7 | h7
      · rcases hpZ.dvd_or_dvd h7 with h8 | h8
        · exact absurd h8 hk'
        · exact absurd (hpZ.dvd_of_dvd_pow h8) hu
      · exact h7
    rw [hw, pow_succ]
    exact mul_dvd_mul_left _ hpw

/-- **[HFF 65] Lemma (Few roots modulo p^N).**  If `p ∤ w`, then `u^k ≡ w (mod p^N)` has at
most `p^{v_p(k)+2}` solutions `u mod p^N`. -/
theorem roots_mod_prime_pow (hk : 1 ≤ k) {p : ℕ} (hp : p.Prime) {N : ℕ} (hN : 1 ≤ N) {w : ℤ}
    (hw : ¬ (p : ℤ) ∣ w) :
    ((range (p ^ N)).filter (fun u : ℕ => (u : ℤ) ^ k ≡ w [ZMOD (p : ℤ) ^ N])).card ≤
      p ^ (k.factorization p + 2) := by
  set v := k.factorization p with hv
  set S := (range (p ^ N)).filter (fun u : ℕ => (u : ℤ) ^ k ≡ w [ZMOD (p : ℤ) ^ N]) with hS_def
  have hp0 : 0 < p := hp.pos
  -- every solution has `p ∤ u`
  have hS : ∀ u ∈ S, ¬ (p : ℤ) ∣ (u : ℤ) := by
    intro u hu hpu
    rw [Finset.mem_filter] at hu
    apply hw
    have h1 : (p : ℤ) ∣ (u : ℤ) ^ k := dvd_pow hpu (by omega)
    have h2 : (p : ℤ) ∣ w - (u : ℤ) ^ k :=
      (dvd_pow_self (p : ℤ) (by omega : N ≠ 0)).trans (Int.modEq_iff_dvd.1 hu.2)
    simpa using dvd_add h2 h1
  -- Solutions in the same class mod `p²` agree mod `p^{N-v}` (Lemma 64), so the map
  -- `u ↦ (u mod p², ⌊u / p^{N-v}⌋)` is injective on the solutions.
  calc S.card ≤ (range (p ^ 2) ×ˢ range (p ^ v)).card := by
        apply Finset.card_le_card_of_injOn (fun u => (u % p ^ 2, u / p ^ (N - v)))
        · intro u hu
          have hu' := (Finset.mem_filter.1 hu).1
          simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hu' ⊢
          refine ⟨Nat.mod_lt _ (by positivity), ?_⟩
          rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
          calc u < p ^ N := hu'
            _ ≤ p ^ (v + (N - v)) := Nat.pow_le_pow_right hp0 (by omega)
        · intro u hu u' hu' huu'
          simp only [Prod.mk.injEq] at huu'
          have hmod : u % p ^ (N - v) = u' % p ^ (N - v) := by
            by_cases hvN : v < N
            · have h22 : (u : ℤ) ≡ u' [ZMOD (p : ℤ) ^ 2] := by
                have := Int.natCast_modEq_iff.2 (show u ≡ u' [MOD p ^ 2] from huu'.1)
                push_cast at this
                exact this
              have h := close_roots_agree hk hp hvN (hS u hu)
                (((Finset.mem_filter.1 hu).2).trans ((Finset.mem_filter.1 hu').2).symm) h22
              have h' : (u : ℤ) ≡ u' [ZMOD ((p ^ (N - v) : ℕ) : ℤ)] := by push_cast; exact h
              exact Int.natCast_modEq_iff.1 h'
            · rw [show N - v = 0 by omega, pow_zero, Nat.mod_one, Nat.mod_one]
          calc u = p ^ (N - v) * (u / p ^ (N - v)) + u % p ^ (N - v) := (Nat.div_add_mod _ _).symm
            _ = p ^ (N - v) * (u' / p ^ (N - v)) + u' % p ^ (N - v) := by rw [huu'.2, hmod]
            _ = u' := Nat.div_add_mod _ _
    _ = p ^ (v + 2) := by
        rw [Finset.card_product, Finset.card_range, Finset.card_range, ← pow_add, add_comm]

/-- **[HFF 66] Lemma (Few roots modulo n).**  If all prime factors of `n ≥ 1` divide `g` and
`gcd(w, n) = 1`, then `u^k ≡ w (mod n)` has at most `k g²` solutions `u mod n`. -/
theorem roots_mod_n (hg : 2 ≤ g) (hk : 2 ≤ k) {n : ℕ} (hn : 1 ≤ n)
    (hng : n.primeFactors ⊆ g.primeFactors) {w : ℤ} (hw : Int.gcd w n = 1) :
    ((range n).filter (fun u : ℕ => (u : ℤ) ^ k ≡ w [ZMOD (n : ℤ)])).card ≤ k * g ^ 2 := by
  set S := (range n).filter (fun u : ℕ => (u : ℤ) ^ k ≡ w [ZMOD (n : ℤ)]) with hS_def
  -- the solutions modulo `p^{v_p(n)}`
  set Sp : ℕ → Finset ℕ := fun p => (range (p ^ n.factorization p)).filter
      (fun u : ℕ => (u : ℤ) ^ k ≡ w [ZMOD (p : ℤ) ^ n.factorization p]) with hSp_def
  have hn0 : n ≠ 0 := by omega
  have hnprod : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
    have := Nat.prod_factorization_pow_eq_self hn0
    rwa [Finsupp.prod, Nat.support_factorization] at this
  -- Chinese remainder theorem (injectivity): `u ↦ (u mod p^{v_p(n)})_p` is injective on `[0, n)`.
  have h1 : S.card ≤ (n.primeFactors.pi Sp).card := by
    apply Finset.card_le_card_of_injOn
      (fun u p (_ : p ∈ n.primeFactors) => u % p ^ n.factorization p)
    · intro u hu
      rw [Finset.mem_coe, Finset.mem_filter] at hu
      rw [Finset.mem_coe, Finset.mem_pi]
      intro p hp
      have hpn : p ^ n.factorization p ∣ n := Nat.ordProj_dvd n p
      have hppos : 0 < p ^ n.factorization p := pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
      simp only [hSp_def, Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.mod_lt _ hppos, ?_⟩
      have h2 : (u : ℤ) ^ k ≡ w [ZMOD (p : ℤ) ^ n.factorization p] :=
        hu.2.of_dvd (by exact_mod_cast hpn)
      have h3 : ((u % p ^ n.factorization p : ℕ) : ℤ) ≡ u [ZMOD (p : ℤ) ^ n.factorization p] := by
        have := Int.natCast_modEq_iff.2 (Nat.mod_modEq u (p ^ n.factorization p))
        push_cast at this
        exact this
      exact (h3.pow k).trans h2
    · intro u hu u' hu' huu'
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hu hu'
      have h2 : (n : ℤ) ∣ (u' : ℤ) - u := by
        rw [← hnprod]
        push_cast
        apply Finset.prod_dvd_of_coprime
        · intro p hp q hq hpq
          exact IsCoprime.pow (Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes
            (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hq)).2 hpq))
        · intro p hp
          have h4 : u ≡ u' [MOD p ^ n.factorization p] := congrFun (congrFun huu' p) hp
          have := Int.natCast_modEq_iff.2 h4
          push_cast at this
          exact Int.modEq_iff_dvd.1 this
      exact (Int.natCast_modEq_iff.1 (Int.modEq_iff_dvd.2 h2)).eq_of_lt_of_lt hu.1 hu'.1
  -- each local count is at most `p^{v_p(k)+2}` (Lemma 65)
  have h5 : ∀ p ∈ n.primeFactors, (Sp p).card ≤ p ^ (k.factorization p + 2) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    apply roots_mod_prime_pow (by omega) hpp
    · exact (hpp.dvd_iff_one_le_factorization hn0).1 (Nat.dvd_of_mem_primeFactors hp)
    · intro hpw
      have : p ∣ Int.gcd w n :=
        Int.dvd_gcd hpw (by exact_mod_cast Nat.dvd_of_mem_primeFactors hp)
      rw [hw] at this
      exact hpp.one_lt.ne' (Nat.dvd_one.1 this)
  calc S.card ≤ (n.primeFactors.pi Sp).card := h1
    _ = ∏ p ∈ n.primeFactors, (Sp p).card := Finset.card_pi _ _
    _ ≤ ∏ p ∈ n.primeFactors, p ^ (k.factorization p + 2) := Finset.prod_le_prod h5
    _ = (∏ p ∈ n.primeFactors, p ^ k.factorization p) * (∏ p ∈ n.primeFactors, p) ^ 2 := by
        rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
        simp only [pow_add]
    -- `∏_{p ∣ n} p^{v_p(k)} ≤ k` and `∏_{p ∣ n} p² ≤ g²`
    _ ≤ k * g ^ 2 := by
        gcongr
        · exact Nat.le_of_dvd (by omega) (prod_pow_factorization_dvd _ _)
        · exact Nat.le_of_dvd (by omega)
            ((Finset.prod_dvd_prod_of_subset _ _ _ hng).trans (Nat.prod_primeFactors_dvd g))

/-- Auxiliary for [HFF 67].  By Lemma 5, `T_b = T_{b'}` implies `b^k ≡ b'^k (mod g^t)`. -/
private lemma pow_modEq_of_Tb_eq (hg : 2 ≤ g) {t b b' : ℕ} (hT : Tb g k t b = Tb g k t b') :
    b ^ k ≡ b' ^ k [MOD g ^ t] := by
  have h := (rev_involution hg t).2.2
  have hpos : 0 < g ^ t := by positivity
  calc b ^ k % g ^ t = rev g t (rev g t (b ^ k % g ^ t)) := (h _ (Nat.mod_lt _ hpos)).symm
    _ = rev g t (rev g t (b' ^ k % g ^ t)) := by
        rw [show rev g t (b ^ k % g ^ t) = rev g t (b' ^ k % g ^ t) from hT]
    _ = b' ^ k % g ^ t := h _ (Nat.mod_lt _ hpos)

/-- Auxiliary for [HFF 67].  If `m_g(b)^k < 2^t` and `p ∣ g`, then `k v_p(b) < t v_p(g)`:
indeed `p^{k v_p(b)} ≤ m^k < 2^t ≤ p^{v_p(g) t}`. -/
private lemma mul_factorization_lt {t b p : ℕ} (hp : p ∈ g.primeFactors)
    (hm : mg g b ^ k < 2 ^ t) : k * b.factorization p < t * g.factorization p := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have h1 : p ^ b.factorization p ∣ mg g b := Finset.dvd_prod_of_mem _ hp
  have hm0 : 0 < mg g b :=
    Finset.prod_pos (fun q hq => pow_pos (Nat.prime_of_mem_primeFactors hq).pos _)
  have hg1 : 1 ≤ g.factorization p :=
    (hpp.dvd_iff_one_le_factorization (Nat.mem_primeFactors.1 hp).2.2).1
      (Nat.dvd_of_mem_primeFactors hp)
  have h2 : p ^ (k * b.factorization p) < p ^ (t * g.factorization p) :=
    calc p ^ (k * b.factorization p) = (p ^ b.factorization p) ^ k := by rw [← pow_mul, mul_comm]
      _ ≤ mg g b ^ k := Nat.pow_le_pow_left (Nat.le_of_dvd hm0 h1) _
      _ < 2 ^ t := hm
      _ ≤ p ^ t := Nat.pow_le_pow_left hpp.two_le _
      _ ≤ p ^ (t * g.factorization p) :=
          Nat.pow_le_pow_right hpp.pos (Nat.le_mul_of_pos_right _ hg1)
  exact (Nat.pow_lt_pow_iff_right hpp.one_lt).1 h2

/-- **[HFF 67] Lemma (Rigid g-part).**  Let `D ≥ 1` with `D^k < 2^t`, and `b, b'` nodes of level
`t` with `T_b = T_{b'}` and `m = m_g(b) ≤ D`.  Then `m^k ∣ g^t` and `m_g(b') = m`. -/
theorem rigid_gpart (hg : 2 ≤ g) (hk : 2 ≤ k) {t b b' : ℕ} {D : ℝ} (hD : 1 ≤ D)
    (hDt : D ^ k < 2 ^ t) (hb : IsNode g k t b) (hb' : IsNode g k t b')
    (hT : Tb g k t b = Tb g k t b') (hm : (mg g b : ℝ) ≤ D) :
    mg g b ^ k ∣ g ^ t ∧ mg g b' = mg g b := by
  -- `m^k ≤ D^k < 2^t`
  have hmk : mg g b ^ k < 2 ^ t := by
    have : ((mg g b ^ k : ℕ) : ℝ) < ((2 ^ t : ℕ) : ℝ) := by
      push_cast
      calc (mg g b : ℝ) ^ k ≤ D ^ k := pow_le_pow_left₀ (Nat.cast_nonneg _) hm _
        _ < 2 ^ t := hDt
    exact_mod_cast this
  -- for `p ∣ g` and `v = v_p(b)`: `k v < v_p(g) t`
  have hv : ∀ p ∈ g.primeFactors, k * b.factorization p < t * g.factorization p :=
    fun p hp => mul_factorization_lt hp hmk
  refine ⟨?_, ?_⟩
  · -- hence `m^k ∣ g^t`
    have hgprod : ∏ p ∈ g.primeFactors, p ^ g.factorization p = g := by
      have := Nat.prod_factorization_pow_eq_self (show g ≠ 0 by omega)
      rwa [Finsupp.prod, Nat.support_factorization] at this
    calc mg g b ^ k = ∏ p ∈ g.primeFactors, p ^ (k * b.factorization p) := by
          unfold mg
          rw [← Finset.prod_pow]
          refine Finset.prod_congr rfl (fun p _ => ?_)
          rw [← pow_mul, mul_comm]
      _ ∣ ∏ p ∈ g.primeFactors, p ^ (t * g.factorization p) :=
          Finset.prod_dvd_prod_of_dvd _ _ (fun p hp => pow_dvd_pow _ (hv p hp).le)
      _ = (∏ p ∈ g.primeFactors, p ^ g.factorization p) ^ t := by
          rw [← Finset.prod_pow]
          refine Finset.prod_congr rfl (fun p _ => ?_)
          rw [← pow_mul, mul_comm]
      _ = g ^ t := by rw [hgprod]
  · -- By Lemma 5, `b^k ≡ b'^k (mod g^t)`, so `v_p(b'^k) = k v` and `v_p(b') = v`.
    have hb0 : b ≠ 0 := node_ne_zero (by omega) hb
    have hb'0 : b' ≠ 0 := node_ne_zero (by omega) hb'
    have hmod : b ^ k ≡ b' ^ k [MOD g ^ t] := pow_modEq_of_Tb_eq hg hT
    unfold mg
    refine Finset.prod_congr rfl (fun p hp => ?_)
    congr 1
    have hpp := Nat.prime_of_mem_primeFactors hp
    -- `p^e ∣ g^t` for `e ≤ v_p(g) t`
    have hdvd : ∀ e, e ≤ t * g.factorization p → p ^ e ∣ g ^ t := fun e he =>
      (pow_dvd_pow p he).trans (by rw [pow_mul']; exact pow_dvd_pow_of_dvd (Nat.ordProj_dvd g p) t)
    have h1 : p ^ (k * b.factorization p) ∣ b' ^ k := by
      rw [← hmod.dvd_iff (hdvd _ (hv p hp).le), mul_comm, pow_mul]
      exact pow_dvd_pow_of_dvd (Nat.ordProj_dvd b p) k
    have h2 : ¬ p ^ (k * b.factorization p + 1) ∣ b' ^ k := by
      rw [← hmod.dvd_iff (hdvd _ (hv p hp))]
      have : (b ^ k).factorization p = k * b.factorization p := by
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
      rw [← this]
      exact Nat.pow_succ_factorization_not_dvd (pow_ne_zero _ hb0) hpp
    have h3 : (b' ^ k).factorization p = k * b.factorization p := by
      have a1 := (hpp.pow_dvd_iff_le_factorization (pow_ne_zero _ hb'0)).1 h1
      have a2 : ¬ (k * b.factorization p + 1 ≤ (b' ^ k).factorization p) := fun h =>
        h2 ((hpp.pow_dvd_iff_le_factorization (pow_ne_zero _ hb'0)).2 h)
      omega
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at h3
    exact Nat.eq_of_mul_eq_mul_left (by omega) h3

/-- **[HFF 68] Lemma (Fibres).**  Let `D ≥ 1` with `D^k < 2^t`, and `b` a node of level `t` with
`m = m_g(b) ≤ D`.  At most `k g² m^{k-1}` nodes `b'` of level `t` satisfy `T_{b'} = T_b`. -/
theorem fibre_bound (hg : 2 ≤ g) (hk : 2 ≤ k) {t b : ℕ} {D : ℝ} (hD : 1 ≤ D) (hDt : D ^ k < 2 ^ t)
    (hb : IsNode g k t b) (hm : (mg g b : ℝ) ≤ D) :
    ((range (g ^ t)).filter (fun b' => IsNode g k t b' ∧ Tb g k t b' = Tb g k t b)).card ≤
      k * g ^ 2 * mg g b ^ (k - 1) := by
  -- By Lemma 67, `m^k ∣ g^t`.
  have hmk : mg g b ^ k ∣ g ^ t := (rigid_gpart hg hk hD hDt hb hb rfl hm).1
  have hb0 : b ≠ 0 := node_ne_zero (by omega) hb
  set m := mg g b with hm_def
  have hm0 : 0 < m := Nat.pos_of_dvd_of_pos (mg_dvd g b) (Nat.pos_of_ne_zero hb0)
  -- `n = g^t / m^k`
  set n := g ^ t / m ^ k with hn_def
  have hgt : g ^ t = m ^ k * n := (Nat.mul_div_cancel' hmk).symm
  have hng' : n ∣ g ^ t := ⟨m ^ k, by rw [hgt, mul_comm]⟩
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by
    rintro h
    rw [h, mul_zero] at hgt
    exact pow_ne_zero t (by omega : g ≠ 0) hgt)
  -- `b = m u` with `u` coprime to `g`
  set u := b / m with hu_def
  have hbu : b = m * u := (Nat.mul_div_cancel' (mg_dvd g b)).symm
  have hu : Nat.Coprime u g := coprime_div_mg (by omega) hb0
  have hun : Nat.Coprime (u ^ k) n := ((hu.pow_right t).coprime_dvd_right hng').pow_left k
  have hng : n.primeFactors ⊆ g.primeFactors := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    exact Nat.mem_primeFactors.2
      ⟨hpp, hpp.dvd_of_dvd_pow ((Nat.dvd_of_mem_primeFactors hp).trans hng'), by omega⟩
  -- By Lemma 66, `u'^k ≡ u^k (mod n)` has at most `k g²` solutions `u' mod n`.
  set S := (range n).filter (fun u' : ℕ => (u' : ℤ) ^ k ≡ (u : ℤ) ^ k [ZMOD (n : ℤ)]) with hS_def
  have hS : S.card ≤ k * g ^ 2 := by
    apply roots_mod_n hg hk hn0 hng
    rw [← Nat.cast_pow, Int.gcd_natCast_natCast]
    exact hun
  have hmk1 : m ^ k = m * m ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  -- by Lemma 67, every `b'` in the fibre has `m_g(b') = m`, so `b' = m u'`
  have hmdvd : ∀ b', IsNode g k t b' → Tb g k t b' = Tb g k t b → m ∣ b' := by
    intro b' hb'node hT
    have hm' : mg g b' = mg g b := (rigid_gpart hg hk hD hDt hb hb'node hT.symm hm).2
    rw [hm_def, ← hm']
    exact mg_dvd g b'
  -- Each `b' = m u'` is determined by `u' mod n` and `⌊u'/n⌋ < m^{k-1}`
  -- (the `m^{k-1}` lifts of `u' mod n` to `[0, g^t/m)`).
  calc _ ≤ (S ×ˢ range (m ^ (k - 1))).card := by
        apply Finset.card_le_card_of_injOn (fun b' => ((b' / m) % n, (b' / m) / n))
        · intro b' hb'
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hb'
          obtain ⟨hb'lt, hb'node, hT⟩ := hb'
          have hb'u : b' = m * (b' / m) := (Nat.mul_div_cancel' (hmdvd b' hb'node hT)).symm
          simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hS_def, Finset.mem_filter,
            Finset.mem_range]
          refine ⟨⟨Nat.mod_lt _ hn0, ?_⟩, ?_⟩
          · -- `b'^k ≡ b^k (mod g^t)` gives `u'^k ≡ u^k (mod n)`
            have h1 : m ^ k * (b' / m) ^ k ≡ m ^ k * u ^ k [MOD m ^ k * n] := by
              rw [← mul_pow, ← mul_pow, ← hb'u, ← hbu, ← hgt]
              exact pow_modEq_of_Tb_eq hg hT
            have h2 := Nat.ModEq.mul_left_cancel' (pow_ne_zero k hm0.ne') h1
            have h3 : (b' / m) % n ≡ b' / m [MOD n] := Nat.mod_modEq _ _
            have h4 := Int.natCast_modEq_iff.2 ((h3.pow k).trans h2)
            push_cast at h4
            exact h4
          · -- `u' < g^t / m = m^{k-1} n`
            rw [Nat.div_lt_iff_lt_mul hn0]
            have : m * (b' / m) < m * (m ^ (k - 1) * n) := by
              rw [← hb'u, ← mul_assoc, ← hmk1, ← hgt]
              exact hb'lt
            exact Nat.lt_of_mul_lt_mul_left this
        · intro b' hb' b'' hb'' h
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hb' hb''
          simp only [Prod.mk.injEq] at h
          have hmb' : m ∣ b' := hmdvd b' hb'.2.1 hb'.2.2
          have hmb'' : m ∣ b'' := hmdvd b'' hb''.2.1 hb''.2.2
          have hq : b' / m = b'' / m := by
            rw [← Nat.div_add_mod (b' / m) n, ← Nat.div_add_mod (b'' / m) n, h.1, h.2]
          rw [← Nat.mul_div_cancel' hmb', ← Nat.mul_div_cancel' hmb'', hq]
    _ = S.card * m ^ (k - 1) := by rw [Finset.card_product, Finset.card_range]
    _ ≤ k * g ^ 2 * m ^ (k - 1) := Nat.mul_le_mul_right _ hS

end PalindromicPowers

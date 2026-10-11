import PalindromicPowers.ReversalTransform

/-!
# HFF blocks 16–27: the power saving
-/

namespace PalindromicPowers

open Finset Real

variable {g k : ℕ}

/-- **[HFF 16] Lemma (Consecutive arguments).**  For `0 ≤ i ≤ s-2`,
`g θᵢ - θ_{i+1} = (g²-1)ℓ/g^{i+2}`. -/
theorem theta_consecutive (hg : 2 ≤ g) {s i : ℕ} (hi : i + 2 ≤ s) (ℓ a : ℤ) :
    (g : ℝ) * theta g s ℓ a i - theta g s ℓ a (i + 1) = ((g : ℝ) ^ 2 - 1) * ℓ / (g : ℝ) ^ (i + 2) := by
  -- write `s = i + 2 + t`, so `s - 1 - i = t + 1` and `s - 1 - (i+1) = t`
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hi
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  have h1 : i + 2 + t - 1 - i = t + 1 := by omega
  have h2 : i + 2 + t - 1 - (i + 1) = t := by omega
  unfold theta
  rw [h1, h2]
  field_simp
  ring

/-- **[HFF 17] Lemma (One of two is far).**
`max(‖θᵢ‖, ‖θ_{i+1}‖) ≥ ‖(g²-1)ℓ/g^{i+2}‖/(g+1)`. -/
theorem one_of_two_far (KR : KnownResults) (hg : 2 ≤ g) {s i : ℕ} (hi : i + 2 ≤ s) (ℓ a : ℤ) :
    distZ (((g : ℝ) ^ 2 - 1) * ℓ / (g : ℝ) ^ (i + 2)) / (g + 1) ≤
      max (distZ (theta g s ℓ a i)) (distZ (theta g s ℓ a (i + 1))) := by
  -- Lemma 16: the argument is `g θᵢ - θ_{i+1}`
  rw [← theta_consecutive hg hi ℓ a]
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  have hg1 : (0 : ℝ) < g + 1 := by positivity
  rw [div_le_iff₀ hg1]
  -- `‖x - y‖ ≤ ‖x‖ + ‖y‖` and `‖g x‖ ≤ g ‖x‖`
  have h1 := KR.distZ_sub_le ((g : ℝ) * theta g s ℓ a i) (theta g s ℓ a (i + 1))
  have h2 := KR.distZ_zmul_le (g : ℤ) (theta g s ℓ a i)
  push_cast at h2
  rw [abs_of_nonneg hg0] at h2
  have hx := le_max_left (distZ (theta g s ℓ a i)) (distZ (theta g s ℓ a (i + 1)))
  have hy := le_max_right (distZ (theta g s ℓ a i)) (distZ (theta g s ℓ a (i + 1)))
  have hx' := mul_le_mul_of_nonneg_left hx hg0
  linarith

/-- **[HFF 18] Definition (Bad indices).**  `ℓ' = (g²-1)ℓ mod Q`. -/
def twist (g s : ℕ) (ℓ : ℤ) : ℕ := ((((g : ℤ) ^ 2 - 1) * ℓ) % ((g : ℤ) ^ s)).toNat

/-- **[HFF 18]** The index `i` is *bad* for `r` if `(r_{i+1}, r_i)` is neither `(0,0)` nor
`(g-1,g-1)`, where `r_i` are the digits of `r`. -/
def IsBad (g r i : ℕ) : Prop :=
  ¬ ((digit g r (i + 1) = 0 ∧ digit g r i = 0) ∨ (digit g r (i + 1) = g - 1 ∧ digit g r i = g - 1))

instance (g r i : ℕ) : Decidable (IsBad g r i) := by unfold IsBad; infer_instance

/-- **[HFF 18]** `β_n(r)`: the number of bad indices `0 ≤ i ≤ n-2` of `r`. -/
def badCount (g n r : ℕ) : ℕ := ((range (n - 1)).filter (fun i => IsBad g r i)).card

/-- **[HFF 18]** `b(ℓ) = β_s(ℓ')`, the number of bad indices of `ℓ' = (g²-1)ℓ mod Q`. -/
def bBad (g s : ℕ) (ℓ : ℤ) : ℕ := badCount g s (twist g s ℓ)

/-- Auxiliary for [HFF 19]. `ℓ'`, read in `ℤ`, is `(g²-1)ℓ mod Q`. -/
private lemma twist_coe (hg : 2 ≤ g) (s : ℕ) (ℓ : ℤ) :
    ((twist g s ℓ : ℕ) : ℤ) = ((g : ℤ) ^ 2 - 1) * ℓ % (g : ℤ) ^ s := by
  have hQ : (0 : ℤ) < (g : ℤ) ^ s := pow_pos (by exact_mod_cast (show 0 < g by omega)) s
  unfold twist
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ hQ.ne')

/-- Auxiliary for [HFF 19]. `0 ≤ ℓ' < Q`. -/
private lemma twist_lt (hg : 2 ≤ g) (s : ℕ) (ℓ : ℤ) : twist g s ℓ < g ^ s := by
  have hQ : (0 : ℤ) < (g : ℤ) ^ s := pow_pos (by exact_mod_cast (show 0 < g by omega)) s
  have h1 := twist_coe hg s ℓ
  have h2 : ((g : ℤ) ^ 2 - 1) * ℓ % (g : ℤ) ^ s < (g : ℤ) ^ s := Int.emod_lt_of_pos _ hQ
  have : ((twist g s ℓ : ℕ) : ℤ) < ((g ^ s : ℕ) : ℤ) := by push_cast; omega
  exact_mod_cast this

/-- **[HFF 19] Lemma (Twisting is bijective).**  `ℓ ↦ ℓ'` induces a bijection of `ℤ/Qℤ`
(here: of `{0,…,Q-1}`), and `ℓ'` (hence `b(ℓ)`) depends only on `ℓ mod Q`. -/
theorem twist_bijective (hg : 2 ≤ g) (s : ℕ) :
    Set.BijOn (fun ℓ : ℕ => twist g s ℓ) (range (g ^ s) : Set ℕ) (range (g ^ s) : Set ℕ) ∧
    ∀ ℓ ℓ' : ℤ, ℓ ≡ ℓ' [ZMOD (g : ℤ) ^ s] → twist g s ℓ = twist g s ℓ' := by
  -- `gcd(g²-1, Q) = 1`: `(-1)(g²-1) + g·g = 1`
  have hcop : IsCoprime ((g : ℤ) ^ s) ((g : ℤ) ^ 2 - 1) := by
    apply IsCoprime.symm
    apply IsCoprime.pow_right
    exact ⟨-1, g, by ring⟩
  have hQ : (0 : ℤ) < (g : ℤ) ^ s := pow_pos (by exact_mod_cast (show 0 < g by omega)) s
  -- injectivity of multiplication by `g²-1` modulo `Q`
  have hinj : Set.InjOn (fun ℓ : ℕ => twist g s ℓ) (range (g ^ s) : Set ℕ) := by
    intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    have h1 : ((g : ℤ) ^ 2 - 1) * (a : ℤ) % (g : ℤ) ^ s = ((g : ℤ) ^ 2 - 1) * (b : ℤ) % (g : ℤ) ^ s := by
      rw [← twist_coe hg, ← twist_coe hg]; exact_mod_cast hab
    have h2 : (g : ℤ) ^ s ∣ ((g : ℤ) ^ 2 - 1) * ((b : ℤ) - a) := by
      rw [mul_sub]; exact Int.ModEq.dvd h1
    have h3 : (g : ℤ) ^ s ∣ (b : ℤ) - a := hcop.dvd_of_dvd_mul_left h2
    have h4 : (a : ℤ) % (g : ℤ) ^ s = (b : ℤ) % (g : ℤ) ^ s := Int.modEq_iff_dvd.mpr h3
    have ha' : (a : ℤ) < (g : ℤ) ^ s := by exact_mod_cast ha
    have hb' : (b : ℤ) < (g : ℤ) ^ s := by exact_mod_cast hb
    rw [Int.emod_eq_of_lt (by positivity) ha', Int.emod_eq_of_lt (by positivity) hb'] at h4
    exact_mod_cast h4
  have hmaps : Set.MapsTo (fun ℓ : ℕ => twist g s ℓ) (range (g ^ s) : Set ℕ) (range (g ^ s) : Set ℕ) := by
    intro a _
    simp only [coe_range, Set.mem_Iio]
    exact twist_lt hg s a
  refine ⟨(Set.Finite.injOn_iff_bijOn_of_mapsTo (finite_toSet _) hmaps).mp hinj, ?_⟩
  -- `ℓ'` depends only on `ℓ mod Q`
  intro ℓ ℓ' h
  have h' : ((g : ℤ) ^ 2 - 1) * ℓ % (g : ℤ) ^ s = ((g : ℤ) ^ 2 - 1) * ℓ' % (g : ℤ) ^ s :=
    Int.ModEq.mul_left _ h
  unfold twist
  rw [h']

/-- Auxiliary for [HFF 21]. Digits are `< g`. -/
private lemma digit_lt (hg : 2 ≤ g) (n i : ℕ) : digit g n i < g :=
  Nat.mod_lt _ (by omega)

/-- **[HFF 20] Lemma (Fractional parts).**  `(g²-1)ℓ/g^{i+2} ≡ vᵢ + wᵢ (mod 1)` with
`vᵢ = ℓ'_{i+1}/g + ℓ'_i/g²` and `0 ≤ wᵢ < 1/g²`. -/
theorem frac_parts (hg : 2 ≤ g) {s i : ℕ} (hi : i + 2 ≤ s) (ℓ : ℤ) :
    ∃ n : ℤ, ∃ w : ℝ, 0 ≤ w ∧ w < 1 / (g : ℝ) ^ 2 ∧
      ((g : ℝ) ^ 2 - 1) * ℓ / (g : ℝ) ^ (i + 2) =
        n + ((digit g (twist g s ℓ) (i + 1) : ℝ) / g + (digit g (twist g s ℓ) i : ℝ) / (g : ℝ) ^ 2) + w := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hi
  have hgpos : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  -- `(g²-1)ℓ = Q q + ℓ'`
  have hX := Int.mul_ediv_add_emod (((g : ℤ) ^ 2 - 1) * ℓ) ((g : ℤ) ^ (i + 2 + t))
  rw [← twist_coe hg] at hX
  set L := twist g (i + 2 + t) ℓ with hLdef
  set q := ((g : ℤ) ^ 2 - 1) * ℓ / (g : ℤ) ^ (i + 2 + t) with hqdef
  -- `ℓ' mod g^{i+2} = ℓ' mod gⁱ + ℓ'_i gⁱ + ℓ'_{i+1} g^{i+1}` (Definition 3)
  have hL1 : L % g ^ (i + 1) = L % g ^ i + g ^ i * digit g L i := by
    rw [pow_succ, Nat.mod_mul]; rfl
  have hL2 : L % g ^ (i + 2) = L % g ^ (i + 1) + g ^ (i + 1) * digit g L (i + 1) := by
    rw [show i + 2 = (i + 1) + 1 by ring, pow_succ g (i + 1), Nat.mod_mul]; rfl
  have hL3 := Nat.div_add_mod L (g ^ (i + 2))
  have hR : L % g ^ i < g ^ i := Nat.mod_lt _ (by positivity)
  -- cast everything to `ℝ`
  have hXR : (g : ℝ) ^ (i + 2 + t) * (q : ℝ) + (L : ℝ) = ((g : ℝ) ^ 2 - 1) * ℓ := by
    exact_mod_cast hX
  have hL1R : ((L % g ^ (i + 1) : ℕ) : ℝ) = ((L % g ^ i : ℕ) : ℝ) + (g : ℝ) ^ i * (digit g L i : ℝ) := by
    exact_mod_cast hL1
  have hL2R : ((L % g ^ (i + 2) : ℕ) : ℝ) =
      ((L % g ^ (i + 1) : ℕ) : ℝ) + (g : ℝ) ^ (i + 1) * (digit g L (i + 1) : ℝ) := by
    exact_mod_cast hL2
  have hL3R : (g : ℝ) ^ (i + 2) * ((L / g ^ (i + 2) : ℕ) : ℝ) + ((L % g ^ (i + 2) : ℕ) : ℝ) = (L : ℝ) := by
    exact_mod_cast hL3
  have hRR : ((L % g ^ i : ℕ) : ℝ) < (g : ℝ) ^ i := by exact_mod_cast hR
  -- `n = q g^t + ⌊ℓ'/g^{i+2}⌋` and `wᵢ = (ℓ' mod gⁱ)/g^{i+2}`
  refine ⟨q * (g : ℤ) ^ t + ((L / g ^ (i + 2) : ℕ) : ℤ), ((L % g ^ i : ℕ) : ℝ) / (g : ℝ) ^ (i + 2),
    by positivity, ?_, ?_⟩
  · rw [div_lt_div_iff₀ (by positivity) (by positivity), one_mul, pow_add]
    exact mul_lt_mul_of_pos_right hRR (by positivity)
  · rw [div_eq_iff (by positivity)]
    have e1 : ((((q * (g : ℤ) ^ t + ((L / g ^ (i + 2) : ℕ) : ℤ) : ℤ) : ℝ) +
        ((digit g L (i + 1) : ℝ) / g + (digit g L i : ℝ) / (g : ℝ) ^ 2) +
        ((L % g ^ i : ℕ) : ℝ) / (g : ℝ) ^ (i + 2)) * (g : ℝ) ^ (i + 2)) =
        ((q : ℝ) * (g : ℝ) ^ t + ((L / g ^ (i + 2) : ℕ) : ℝ)) * (g : ℝ) ^ (i + 2) +
          (digit g L (i + 1) : ℝ) * (g : ℝ) ^ (i + 1) + (digit g L i : ℝ) * (g : ℝ) ^ i +
          ((L % g ^ i : ℕ) : ℝ) := by
      simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
      field_simp
      ring
    rw [e1]
    linear_combination -hXR - hL3R + hL2R + hL1R

/-- Auxiliary for [HFF 21]. If `a ≤ y ≤ 1 - a` then `‖y‖ ≥ a`. -/
private lemma le_distZ_of_mem {a y : ℝ} (h1 : a ≤ y) (h2 : y ≤ 1 - a) : a ≤ distZ y := by
  unfold distZ
  rcases le_or_gt (round y) 0 with h | h
  · have : (round y : ℝ) ≤ 0 := by exact_mod_cast h
    have := le_abs_self (y - round y)
    linarith
  · have : (1 : ℝ) ≤ round y := by exact_mod_cast h
    have := neg_abs_le (y - round y)
    linarith

/-- **[HFF 21] Lemma (Bad indices are far).**  If `i` is bad, `‖(g²-1)ℓ/g^{i+2}‖ ≥ 1/g²`. -/
theorem bad_far (hg : 2 ≤ g) {s i : ℕ} (hi : i + 2 ≤ s) (ℓ : ℤ) (hbad : IsBad g (twist g s ℓ) i) :
    1 / (g : ℝ) ^ 2 ≤ distZ (((g : ℝ) ^ 2 - 1) * ℓ / (g : ℝ) ^ (i + 2)) := by
  -- Lemma 20
  obtain ⟨n, w, hw0, hw1, hx⟩ := frac_parts hg hi ℓ
  have hd1 := digit_lt hg (twist g s ℓ) (i + 1)
  have hd0 := digit_lt hg (twist g s ℓ) i
  set d1 := digit g (twist g s ℓ) (i + 1) with hd1def
  set d0 := digit g (twist g s ℓ) i with hd0def
  have hbad' : ¬ ((d1 = 0 ∧ d0 = 0) ∨ (d1 = g - 1 ∧ d0 = g - 1)) := hbad
  have hG : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hGpos : (0 : ℝ) < g := by linarith
  have hd0R : (0 : ℝ) ≤ d0 := Nat.cast_nonneg d0
  -- `vᵢ = (ℓ'_{i+1} g + ℓ'_i)/g²`
  have hv : (d1 : ℝ) / g + (d0 : ℝ) / (g : ℝ) ^ 2 = ((d1 : ℝ) * g + d0) / (g : ℝ) ^ 2 := by
    field_simp
  -- `vᵢ ≠ 0`, i.e. `vᵢ ≥ 1/g²`
  have hlow : (1 : ℝ) ≤ (d1 : ℝ) * g + d0 := by
    rcases Nat.eq_zero_or_pos d1 with h | h
    · have h0 : 1 ≤ d0 := by omega
      have : (1 : ℝ) ≤ d0 := by exact_mod_cast h0
      rw [h]; simp only [Nat.cast_zero, zero_mul, zero_add]; exact this
    · have : (1 : ℝ) ≤ d1 := by exact_mod_cast h
      nlinarith
  -- `vᵢ ≠ 1 - 1/g²`, i.e. `vᵢ ≤ 1 - 2/g²`
  have hup : (d1 : ℝ) * g + d0 ≤ (g : ℝ) ^ 2 - 2 := by
    by_cases h : d1 + 1 = g
    · have h0 : d0 + 2 ≤ g := by omega
      have h' : (d1 : ℝ) + 1 = g := by exact_mod_cast h
      have : (d0 : ℝ) + 2 ≤ g := by exact_mod_cast h0
      nlinarith
    · have h1 : d1 + 2 ≤ g := by omega
      have h1' : (d1 : ℝ) + 2 ≤ g := by exact_mod_cast h1
      have h0' : (d0 : ℝ) + 1 ≤ g := by exact_mod_cast hd0
      nlinarith
  rw [hx, show (n : ℝ) + ((d1 : ℝ) / g + (d0 : ℝ) / (g : ℝ) ^ 2) + w =
      (((d1 : ℝ) / g + (d0 : ℝ) / (g : ℝ) ^ 2) + w) + n by ring, distZ_add_int, hv]
  have hG2 : (0 : ℝ) < (g : ℝ) ^ 2 := by positivity
  apply le_distZ_of_mem
  · have : 1 / (g : ℝ) ^ 2 ≤ ((d1 : ℝ) * g + d0) / (g : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hlow hG2.le
    linarith
  · have h1 : ((d1 : ℝ) * g + d0) / (g : ℝ) ^ 2 ≤ ((g : ℝ) ^ 2 - 2) / (g : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hup hG2.le
    have h2 : ((g : ℝ) ^ 2 - 2) / (g : ℝ) ^ 2 = 1 - 2 * (1 / (g : ℝ) ^ 2) := by
      field_simp
    linarith

/-- **[HFF 22] Lemma (Bad pair product).**  If `i` is bad, `f(θᵢ) f(θ_{i+1}) ≤ u_*²` for all `a`. -/
theorem bad_pair_prod (KR : KnownResults) (hg : 2 ≤ g) {s i : ℕ} (hi : i + 2 ≤ s) (ℓ : ℤ)
    (hbad : IsBad g (twist g s ℓ) i) (a : ℤ) :
    fdig g (theta g s ℓ a i) * fdig g (theta g s ℓ a (i + 1)) ≤ uStar g ^ 2 := by
  -- Lemmas 17 and 21: `max(‖θᵢ‖, ‖θ_{i+1}‖) ≥ 1/(g²(g+1)) = ε_*`
  have h17 := one_of_two_far KR hg hi ℓ a
  have h21 := bad_far hg hi ℓ hbad
  have hG : (0 : ℝ) < (g : ℝ) + 1 := by positivity
  have heps : epsStar g ≤ max (distZ (theta g s ℓ a i)) (distZ (theta g s ℓ a (i + 1))) := by
    calc epsStar g = (1 / (g : ℝ) ^ 2) / (g + 1) := by rw [epsStar, div_div]
      _ ≤ distZ (((g : ℝ) ^ 2 - 1) * ℓ / (g : ℝ) ^ (i + 2)) / (g + 1) :=
          div_le_div_of_nonneg_right h21 hG.le
      _ ≤ _ := h17
  -- Lemma 15 for the far factor, Lemma 14 (`0 ≤ f ≤ 1`) for the other
  obtain ⟨-, -, hgap⟩ := uStar_spec KR hg
  obtain ⟨-, -, hf01, -⟩ := fdig_shape hg
  have hA := hf01 (theta g s ℓ a i)
  have hB := hf01 (theta g s ℓ a (i + 1))
  rcases le_max_iff.mp heps with h | h
  · calc _ ≤ uStar g ^ 2 * 1 := mul_le_mul (hgap _ h) hB.2 hB.1 (sq_nonneg _)
      _ = _ := mul_one _
  · calc _ ≤ 1 * uStar g ^ 2 := mul_le_mul hA.2 (hgap _ h) hB.1 zero_le_one
      _ = _ := one_mul _

/-- Auxiliary for [HFF 23]. For `φᵢ ∈ [0,1]`,
`(∏_{i≤n} φᵢ)² ≤ φₙ ∏_{i<n} φᵢφ_{i+1}`. -/
private lemma sq_prod_le_aux (φ : ℕ → ℝ) (h0 : ∀ i, 0 ≤ φ i) (h1 : ∀ i, φ i ≤ 1) (n : ℕ) :
    (∏ i ∈ range (n + 1), φ i) ^ 2 ≤ φ n * ∏ i ∈ range n, (φ i * φ (i + 1)) := by
  induction n with
  | zero =>
    simp only [zero_add, prod_range_one, range_zero, prod_empty, mul_one]
    nlinarith [h0 0, h1 0]
  | succ n ih =>
    rw [prod_range_succ φ (n + 1), mul_pow, prod_range_succ (fun i => φ i * φ (i + 1)) n]
    calc (∏ i ∈ range (n + 1), φ i) ^ 2 * φ (n + 1) ^ 2
        ≤ (φ n * ∏ i ∈ range n, (φ i * φ (i + 1))) * φ (n + 1) ^ 2 :=
          mul_le_mul_of_nonneg_right ih (sq_nonneg _)
      _ = φ (n + 1) * ((∏ i ∈ range n, (φ i * φ (i + 1))) * (φ n * φ (n + 1))) := by ring

/-- Auxiliary for [HFF 23]. For `φᵢ ∈ [0,1]`, `(∏_{i<s} φᵢ)² ≤ ∏_{i≤s-2} φᵢφ_{i+1}`
(the HFF's `φ ≤ φ^{1/2}` step, squared). -/
private lemma sq_prod_le (φ : ℕ → ℝ) (h0 : ∀ i, 0 ≤ φ i) (h1 : ∀ i, φ i ≤ 1) (s : ℕ) :
    (∏ i ∈ range s, φ i) ^ 2 ≤ ∏ i ∈ range (s - 1), (φ i * φ (i + 1)) := by
  rcases s with _ | n
  · simp
  · have h := sq_prod_le_aux φ h0 h1 n
    have hP : 0 ≤ ∏ i ∈ range n, (φ i * φ (i + 1)) :=
      prod_nonneg fun i _ => mul_nonneg (h0 i) (h0 (i + 1))
    rw [Nat.add_sub_cancel]
    calc _ ≤ _ := h
      _ ≤ 1 * ∏ i ∈ range n, (φ i * φ (i + 1)) := mul_le_mul_of_nonneg_right (h1 n) hP
      _ = _ := one_mul _

/-- **[HFF 23] Lemma (Sup bound).**  `M(ℓ) ≤ Q u_*^{b(ℓ)}`. -/
theorem Mmax_le (KR : KnownResults) (hg : 2 ≤ g) (s : ℕ) (ℓ : ℤ) :
    Mmax g s ℓ ≤ (g : ℝ) ^ s * uStar g ^ bBad g s ℓ := by
  obtain ⟨hu0, -, -⟩ := uStar_spec KR hg
  obtain ⟨-, -, hf01, -⟩ := fdig_shape hg
  have key : ∀ a : ℤ, ‖Psi g s ℓ a‖ ≤ (g : ℝ) ^ s * uStar g ^ bBad g s ℓ := by
    intro a
    -- Lemma 11
    rw [norm_Psi_eq hg s ℓ a]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    -- `φᵢ = f(θᵢ) ∈ [0,1]` (Lemma 14)
    set φ : ℕ → ℝ := fun i => fdig g (theta g s ℓ a i) with hφ
    have h0 : ∀ i, 0 ≤ φ i := fun i => (hf01 _).1
    have h1 : ∀ i, φ i ≤ 1 := fun i => (hf01 _).2
    have hsq := sq_prod_le φ h0 h1 s
    -- Lemma 22 for the bad `i`, `φᵢφ_{i+1} ≤ 1` for the others
    have hpairs : ∏ i ∈ range (s - 1), (φ i * φ (i + 1)) ≤ (uStar g ^ bBad g s ℓ) ^ 2 := by
      calc ∏ i ∈ range (s - 1), (φ i * φ (i + 1))
          ≤ ∏ i ∈ range (s - 1), (if IsBad g (twist g s ℓ) i then uStar g ^ 2 else 1) := by
            apply prod_le_prod₀
            · intro i _; exact mul_nonneg (h0 _) (h0 _)
            · intro i hi
              split_ifs with hb
              · exact bad_pair_prod KR hg (by simp only [mem_range] at hi; omega) ℓ hb a
              · calc φ i * φ (i + 1) ≤ 1 * 1 := mul_le_mul (h1 _) (h1 _) (h0 _) zero_le_one
                  _ = 1 := one_mul 1
        _ = (uStar g ^ 2) ^ bBad g s ℓ := by
            rw [prod_ite, prod_const, prod_const_one, mul_one]; rfl
        _ = (uStar g ^ bBad g s ℓ) ^ 2 := by ring
    exact le_of_pow_le_pow_left₀ two_ne_zero (pow_nonneg hu0 _) (hsq.trans hpairs)
  -- `M(ℓ)` is the maximum over `0 ≤ a < Q`
  obtain ⟨a, -, ha⟩ := exists_mem_eq_sup (range (g ^ s))
    (nonempty_range_iff.mpr (pow_ne_zero _ (by omega))) (fun a : ℕ => ‖Psi g s ℓ a‖₊)
  unfold Mmax
  rw [ha, coe_nnnorm]
  exact key a

/-- Auxiliary for [HFF 24]. Splitting `r < N m` as `r = r' + N d` with `r' < N`, `d < m`. -/
private lemma sum_range_mul_split {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N m : ℕ) :
    ∑ r ∈ range (N * m), f r = ∑ d ∈ range m, ∑ r ∈ range N, f (r + N * d) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [mul_add_one, sum_range_add, ih, sum_range_succ]
    congr 1
    apply sum_congr rfl
    intro r _
    rw [add_comm]

/-- Auxiliary for [HFF 24]. The digits `j < n` of `r + gⁿ d` are those of `r`. -/
private lemma digit_add_low (hg : 0 < g) {n r d j : ℕ} (hj : j < n) :
    digit g (r + g ^ n * d) j = digit g r j := by
  unfold digit
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hj
  rw [show g ^ (j + t + 1) * d = g ^ j * (g * (g ^ t * d)) by ring,
    Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

/-- Auxiliary for [HFF 24]. The digit `n` of `r + gⁿ d` is `d` (for `r < gⁿ`, `d < g`). -/
private lemma digit_add_top (hg : 0 < g) {n r d : ℕ} (hr : r < g ^ n) (hd : d < g) :
    digit g (r + g ^ n * d) n = d := by
  unfold digit
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hr, zero_add, Nat.mod_eq_of_lt hd]

/-- Auxiliary for [HFF 24]. Appending the digit `d` to `r` adds the index `m` to the bad
indices iff it is bad. -/
private lemma badCount_succ (hg : 2 ≤ g) {m r d : ℕ} :
    badCount g (m + 2) (r + g ^ (m + 1) * d) =
      badCount g (m + 1) r + if IsBad g (r + g ^ (m + 1) * d) m then 1 else 0 := by
  unfold badCount
  rw [show m + 2 - 1 = m + 1 by omega, show m + 1 - 1 = m by omega, card_filter, card_filter,
    sum_range_succ]
  congr 1
  apply sum_congr rfl
  intro i hi
  have hi' : i < m := mem_range.mp hi
  have e1 : digit g (r + g ^ (m + 1) * d) i = digit g r i := digit_add_low (by omega) (by omega)
  have e2 : digit g (r + g ^ (m + 1) * d) (i + 1) = digit g r (i + 1) :=
    digit_add_low (by omega) (by omega)
  have : IsBad g (r + g ^ (m + 1) * d) i ↔ IsBad g r i := by
    unfold IsBad; rw [e1, e2]
  exact if_congr this rfl rfl

/-- Auxiliary for [HFF 24]. `∑_{d<g} u^{β(r,d)} ≤ u^{β(r)} (1 + (g-1)u)`. -/
private lemma sum_append_digit (hg : 2 ≤ g) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) {m r : ℕ}
    (hr : r < g ^ (m + 1)) :
    ∑ d ∈ range g, u ^ badCount g (m + 2) (r + g ^ (m + 1) * d) ≤
      u ^ badCount g (m + 1) r * (1 + (g - 1) * u) := by
  have hcg : digit g r m < g := digit_lt hg r m
  have hterm : ∀ d ∈ range g, u ^ badCount g (m + 2) (r + g ^ (m + 1) * d) =
      u ^ badCount g (m + 1) r * u ^ (if IsBad g (r + g ^ (m + 1) * d) m then 1 else 0) := by
    intro d _
    rw [badCount_succ hg, pow_add]
  rw [sum_congr rfl hterm, ← mul_sum]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hu0 _)
  -- the digit `d = r_m` contributes at most `1`, every other digit contributes `u`
  rw [← add_sum_erase _ _ (mem_range.mpr hcg)]
  have h1 : u ^ (if IsBad g (r + g ^ (m + 1) * digit g r m) m then 1 else 0) ≤ 1 :=
    pow_le_one₀ hu0 hu1
  have h2 : ∀ d ∈ (range g).erase (digit g r m),
      u ^ (if IsBad g (r + g ^ (m + 1) * d) m then 1 else 0) = u := by
    intro d hd
    obtain ⟨hdc, hdg⟩ := mem_erase.mp hd
    have hdg' := mem_range.mp hdg
    have hbad : IsBad g (r + g ^ (m + 1) * d) m := by
      unfold IsBad
      rw [digit_add_top (by omega) hr hdg', digit_add_low (by omega) (show m < m + 1 by omega)]
      omega
    simp [hbad]
  rw [sum_congr rfl h2, sum_const, card_erase_of_mem (mem_range.mpr hcg), card_range, nsmul_eq_mul,
    Nat.cast_sub (by omega : 1 ≤ g), Nat.cast_one]
  linarith

/-- Auxiliary for [HFF 24]. The statement with `n = m + 1`. -/
private lemma weighted_strings_aux (hg : 2 ≤ g) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (m : ℕ) :
    ∑ r ∈ range (g ^ (m + 1)), u ^ badCount g (m + 1) r ≤ g * (1 + (g - 1) * u) ^ m := by
  have hρ : 0 ≤ 1 + ((g : ℝ) - 1) * u := by
    have : (1 : ℝ) ≤ g := by exact_mod_cast (show 1 ≤ g by omega)
    nlinarith
  induction m with
  | zero =>
    -- `n = 1`: there are no indices `i ≤ n - 2`, and the sum is `g`
    have h : ∀ r, badCount g 1 r = 0 := fun r => by simp [badCount]
    simp [h]
  | succ m ih =>
    -- write `r < g^{m+2}` as `r' + g^{m+1} d`
    rw [pow_succ g (m + 1), sum_range_mul_split, sum_comm]
    calc ∑ r ∈ range (g ^ (m + 1)), ∑ d ∈ range g, u ^ badCount g (m + 1 + 1) (r + g ^ (m + 1) * d)
        ≤ ∑ r ∈ range (g ^ (m + 1)), u ^ badCount g (m + 1) r * (1 + (g - 1) * u) :=
          sum_le_sum fun r hr => sum_append_digit hg hu0 hu1 (mem_range.mp hr)
      _ = (∑ r ∈ range (g ^ (m + 1)), u ^ badCount g (m + 1) r) * (1 + (g - 1) * u) := by
          rw [sum_mul]
      _ ≤ g * (1 + (g - 1) * u) ^ m * (1 + (g - 1) * u) := mul_le_mul_of_nonneg_right ih hρ
      _ = g * (1 + (g - 1) * u) ^ (m + 1) := by ring

/-- **[HFF 24] Lemma (Weighted digit strings).**  For `0 ≤ u ≤ 1` and `n ≥ 1`,
`∑_{r<gⁿ} u^{β_n(r)} ≤ g(1+(g-1)u)^{n-1}` (digit strings of length `n` are the digits of the
`r < gⁿ`, Lemma 2). -/
theorem weighted_strings (hg : 2 ≤ g) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    ∑ r ∈ range (g ^ n), u ^ badCount g n r ≤ g * (1 + (g - 1) * u) ^ (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [Nat.add_sub_cancel]
  exact weighted_strings_aux hg hu0 hu1 m

/-- **[HFF 25]** `ρ = 1 + (g-1)u_*`. -/
noncomputable def rho (g : ℕ) : ℝ := 1 + (g - 1) * uStar g

/-- Auxiliary for [HFF 25]. For `F ≥ 0` of period `N ≥ 0`,
`∑_{0<|ℓ|<N} F(ℓ) ≤ 2 ∑_{0≤ℓ<N} F(ℓ)` (each residue is hit at most twice). -/
private lemma sum_symm_le_two_mul (F : ℤ → ℝ) (N : ℤ) (hN : 0 ≤ N) (hF0 : ∀ ℓ, 0 ≤ F ℓ)
    (hper : ∀ ℓ, F (ℓ + N) = F ℓ) :
    ∑ ℓ ∈ (Ioo (-N) N).erase 0, F ℓ ≤ 2 * ∑ ℓ ∈ Ico 0 N, F ℓ := by
  have h1 : ∑ ℓ ∈ (Ioo (-N) N).erase 0, F ℓ ≤ ∑ ℓ ∈ Ico (-N) N, F ℓ := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro x hx
      simp only [mem_erase, mem_Ioo] at hx
      simp only [mem_Ico]
      constructor <;> linarith [hx.2.1, hx.2.2]
    · intro i _ _; exact hF0 i
  have h2 : ∑ ℓ ∈ Ico (-N) N, F ℓ = ∑ ℓ ∈ Ico (-N) 0, F ℓ + ∑ ℓ ∈ Ico 0 N, F ℓ := by
    rw [← sum_union (Ico_disjoint_Ico_consecutive _ _ _),
      Ico_union_Ico_eq_Ico (by linarith) hN]
  have h3 : ∑ ℓ ∈ Ico (-N) 0, F ℓ = ∑ ℓ ∈ Ico 0 N, F ℓ := by
    apply sum_nbij' (fun ℓ => ℓ + N) (fun ℓ => ℓ - N)
    · intro a ha; simp only [mem_Ico] at ha ⊢; constructor <;> linarith [ha.1, ha.2]
    · intro a ha; simp only [mem_Ico] at ha ⊢; constructor <;> linarith [ha.1, ha.2]
    · intro a _; ring
    · intro a _; ring
    · intro a _; exact (hper a).symm
  linarith

/-- Auxiliary for [HFF 25]. `∑_{ℓ ∈ [0, N) ∩ ℤ} F(ℓ) = ∑_{r < N} F(r)`. -/
private lemma sum_Ico_int_eq_sum_range (F : ℤ → ℝ) (N : ℕ) :
    ∑ ℓ ∈ Ico (0 : ℤ) N, F ℓ = ∑ r ∈ range N, F r := by
  symm
  apply sum_nbij' (fun r : ℕ => (r : ℤ)) (fun ℓ => ℓ.toNat)
  · intro a ha; simp only [mem_range] at ha; simp only [mem_Ico]; omega
  · intro a ha; simp only [mem_Ico] at ha; simp only [mem_range]; omega
  · intro a _; simp
  · intro a ha; simp only [mem_Ico] at ha; omega
  · intro a _; rfl

/-- **[HFF 25] Lemma (Sum over frequencies).**  `S(s) ≤ 2gQρ^{s-1}`, and `ρ < g`. -/
theorem Ssum_le (KR : KnownResults) (hg : 2 ≤ g) {s : ℕ} (hs : 1 ≤ s) :
    Ssum g s ≤ 2 * g * (g : ℝ) ^ s * rho g ^ (s - 1) ∧ rho g < g := by
  obtain ⟨hu0, hu1, -⟩ := uStar_spec KR hg
  have hG : (2 : ℝ) ≤ g := by exact_mod_cast hg
  refine ⟨?_, by unfold rho; nlinarith⟩
  -- Lemma 10: `M(ℓ)` depends only on `ℓ mod Q`
  have hM0 : ∀ ℓ, 0 ≤ Mmax g s ℓ := fun ℓ => NNReal.coe_nonneg _
  have hMper : ∀ ℓ, Mmax g s (ℓ + (g : ℤ) ^ s) = Mmax g s ℓ := by
    intro ℓ
    unfold Mmax
    congr 1
    apply Finset.sup_congr rfl
    intro a _
    rw [Psi_periodic hg s Int.add_modEq_right (Int.ModEq.refl _)]
  -- each residue is hit by at most two `ℓ` with `0 < |ℓ| < Q`
  have hS : Ssum g s ≤ 2 * ∑ r ∈ range (g ^ s), Mmax g s r := by
    unfold Ssum
    have := sum_symm_le_two_mul (Mmax g s) ((g : ℤ) ^ s) (by positivity) hM0 hMper
    rw [show ((g : ℤ) ^ s) = ((g ^ s : ℕ) : ℤ) by push_cast; rfl, sum_Ico_int_eq_sum_range] at this
    simpa using this
  -- Lemmas 23 and 19
  have h3 : ∑ r ∈ range (g ^ s), Mmax g s r ≤
      ∑ r ∈ range (g ^ s), (g : ℝ) ^ s * uStar g ^ badCount g s r := by
    calc ∑ r ∈ range (g ^ s), Mmax g s r
        ≤ ∑ r ∈ range (g ^ s), (g : ℝ) ^ s * uStar g ^ bBad g s r :=
          sum_le_sum fun r _ => Mmax_le KR hg s r
      _ = ∑ r ∈ range (g ^ s), (g : ℝ) ^ s * uStar g ^ badCount g s r := by
          obtain ⟨hbij, -⟩ := twist_bijective hg s
          exact sum_nbij (fun ℓ : ℕ => twist g s ℓ) (fun a ha => hbij.mapsTo ha) hbij.injOn
            hbij.surjOn (fun a _ => rfl)
  -- Lemma 24 with `u = u_*`, `n = s`
  have h4 := weighted_strings hg hu0 hu1.le hs
  rw [← mul_sum] at h3
  calc Ssum g s ≤ 2 * ∑ r ∈ range (g ^ s), Mmax g s r := hS
    _ ≤ 2 * ((g : ℝ) ^ s * (g * (1 + (g - 1) * uStar g) ^ (s - 1))) := by
        gcongr
        exact h3.trans (mul_le_mul_of_nonneg_left h4 (by positivity))
    _ = 2 * g * (g : ℝ) ^ s * rho g ^ (s - 1) := by unfold rho; ring

/-- **[HFF 26]** `c = min(1 - log_g ρ, log 2/(2 log g))`. -/
noncomputable def cSave (g : ℕ) : ℝ :=
  min (1 - Real.logb g (rho g)) (Real.log 2 / (2 * Real.log g))

/-- **[HFF 26]** `C = 2g`. -/
noncomputable def CSave (g : ℕ) : ℝ := 2 * g

/-- **[HFF 26] Lemma (Power saving).**  `0 < c ≤ log 2/(2 log g)`, `C ≥ 1`, and
`S(s) ≤ C g^{(2-c)s}` for all `s ≥ 1`. -/
theorem power_saving (KR : KnownResults) (hg : 2 ≤ g) :
    0 < cSave g ∧ cSave g ≤ Real.log 2 / (2 * Real.log g) ∧ 1 ≤ CSave g ∧
    ∀ s : ℕ, 1 ≤ s → Ssum g s ≤ CSave g * (g : ℝ) ^ ((2 - cSave g) * s) := by
  obtain ⟨hu0, -, -⟩ := uStar_spec KR hg
  have hG : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hG1 : (1 : ℝ) < g := by linarith
  have hGpos : (0 : ℝ) < g := by linarith
  have hlogg : 0 < Real.log g := Real.log_pos hG1
  -- `1 ≤ ρ < g` (Lemmas 15 and 25)
  have hρ1 : 1 ≤ rho g := by
    unfold rho
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ g - 1) hu0
    linarith
  have hρg : rho g < g := (Ssum_le KR hg le_rfl).2
  have hlogb : Real.logb g (rho g) < 1 := by
    rw [Real.logb_lt_iff_lt_rpow hG1 (by linarith), Real.rpow_one]; exact hρg
  have hc_pos : 0 < cSave g :=
    lt_min (by linarith) (div_pos (Real.log_pos (by norm_num)) (by linarith))
  have hc_le : cSave g ≤ 1 - Real.logb g (rho g) := min_le_left _ _
  refine ⟨hc_pos, min_le_right _ _, ?_, ?_⟩
  · unfold CSave; linarith
  · intro s hs
    have h25 := (Ssum_le KR hg hs).1
    -- `ρ ≤ g^{1-c}`
    have hρle : rho g ≤ (g : ℝ) ^ (1 - cSave g) := by
      calc rho g = (g : ℝ) ^ (Real.logb g (rho g)) :=
            (Real.rpow_logb hGpos hG1.ne' (by linarith)).symm
        _ ≤ (g : ℝ) ^ (1 - cSave g) := Real.rpow_le_rpow_of_exponent_le hG1.le (by linarith)
    have h1 : rho g ^ (s - 1) ≤ rho g ^ s := pow_le_pow_right₀ hρ1 (Nat.sub_le s 1)
    have h2 : rho g ^ s ≤ (g : ℝ) ^ ((1 - cSave g) * s) := by
      rw [Real.rpow_mul hGpos.le, Real.rpow_natCast]
      exact pow_le_pow_left₀ (by linarith) hρle s
    have h3 : (g : ℝ) ^ s * (g : ℝ) ^ ((1 - cSave g) * s) = (g : ℝ) ^ ((2 - cSave g) * s) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hGpos]
      congr 1
      ring
    calc Ssum g s ≤ 2 * g * (g : ℝ) ^ s * rho g ^ (s - 1) := h25
      _ ≤ 2 * g * (g : ℝ) ^ s * (g : ℝ) ^ ((1 - cSave g) * s) := by
          gcongr
          exact h1.trans h2
      _ = CSave g * (g : ℝ) ^ ((2 - cSave g) * s) := by
          rw [mul_assoc (2 * (g : ℝ)), h3]
          rfl

end PalindromicPowers

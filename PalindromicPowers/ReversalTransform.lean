import PalindromicPowers.Digits

/-!
# HFF blocks 9–15: the reversal transform
-/

namespace PalindromicPowers

open Finset Real

variable {g k : ℕ}

/-- **[HFF 9] Definition (Reversal transform).**  With `Q = g^s`,
`Ψ_ℓ(a) = ∑_{m<Q} e(-(ℓ rev_s(m) + a m)/Q)`. -/
noncomputable def Psi (g s : ℕ) (ℓ a : ℤ) : ℂ :=
  ∑ m ∈ range (g ^ s), e (-(((ℓ * (rev g s m : ℤ) + a * (m : ℤ) : ℤ) : ℝ) / (g : ℝ) ^ s))

/-- **[HFF 9]** `M(ℓ) = max_{0≤a<Q} |Ψ_ℓ(a)|`. -/
noncomputable def Mmax (g s : ℕ) (ℓ : ℤ) : ℝ :=
  (((range (g ^ s)).sup fun a : ℕ => ‖Psi g s ℓ a‖₊ : NNReal) : ℝ)

/-- **[HFF 9]** `S(s) = ∑_{0<|ℓ|<Q} M(ℓ)`. -/
noncomputable def Ssum (g s : ℕ) : ℝ :=
  ∑ ℓ ∈ (Ioo (-((g : ℤ) ^ s)) ((g : ℤ) ^ s)).erase 0, Mmax g s ℓ

/-- **[HFF 9]** `f(θ) = (1/g) |∑_{d<g} e(dθ)|`. -/
noncomputable def fdig (g : ℕ) (θ : ℝ) : ℝ := ‖∑ d ∈ range g, e (d * θ)‖ / g

/-- **[HFF 9]** `θᵢ(ℓ,a) = (ℓ g^{s-1-i} + a gⁱ)/Q` (used for `0 ≤ i < s`). -/
noncomputable def theta (g s : ℕ) (ℓ a : ℤ) (i : ℕ) : ℝ :=
  ((ℓ : ℝ) * (g : ℝ) ^ (s - 1 - i) + (a : ℝ) * (g : ℝ) ^ i) / (g : ℝ) ^ s

/-- **[HFF 10] Lemma (Periodicity).**  `Ψ_ℓ(a)` depends only on `ℓ mod Q` and `a mod Q`. -/
theorem Psi_periodic (hg : 2 ≤ g) (s : ℕ) {ℓ ℓ' a a' : ℤ}
    (hℓ : ℓ ≡ ℓ' [ZMOD (g : ℤ) ^ s]) (ha : a ≡ a' [ZMOD (g : ℤ) ^ s]) :
    Psi g s ℓ a = Psi g s ℓ' a' := by
  obtain ⟨k₁, hk₁⟩ := hℓ.dvd
  obtain ⟨k₂, hk₂⟩ := ha.dvd
  have hℓ' : ℓ' = ℓ + (g : ℤ) ^ s * k₁ := by linarith
  have ha' : a' = a + (g : ℤ) ^ s * k₂ := by linarith
  have hQ : (g : ℝ) ^ s ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : g ≠ 0))
  unfold Psi
  refine Finset.sum_congr rfl fun m _ => ?_
  -- the arguments differ by the integer `-(k₁ rev_s(m) + k₂ m)`, and `e` has period `1`
  conv_lhs => rw [← e_add_int _ (-(k₁ * (rev g s m : ℤ) + k₂ * (m : ℤ)))]
  congr 1
  rw [hℓ', ha']
  push_cast
  field_simp
  ring

/-- Auxiliary for [HFF 11].  Summing a product of functions of the digits over `m < g^s`
factorises: `∑_{m<g^s} ∏_{i<s} hᵢ(mᵢ) = ∏_{i<s} ∑_{d<g} hᵢ(d)` (the digit map is a bijection,
Lemma 2; here realised by `finFunctionFinEquiv`). -/
private theorem sum_prod_digit (s : ℕ) (h : ℕ → ℕ → ℂ) :
    ∑ m ∈ range (g ^ s), ∏ i ∈ range s, h i (digit g m i) =
      ∏ i ∈ range s, ∑ d ∈ range g, h i d := by
  classical
  rw [Finset.sum_range (fun m => ∏ i ∈ range s, h i (digit g m i)),
    ← (finFunctionFinEquiv (m := g) (n := s)).sum_comp,
    ← Fin.prod_univ_eq_prod_range (fun i => ∑ d ∈ range g, h i d)]
  simp_rw [Finset.sum_range (h _), Fintype.prod_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [← Fin.prod_univ_eq_prod_range (fun i => h i (digit g _ i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  have := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv f) i
  rw [Equiv.symm_apply_apply] at this
  rw [digit, ← this]

/-- **[HFF 11] Lemma (Product formula).**  `|Ψ_ℓ(a)| = Q ∏_{i<s} f(θᵢ(ℓ,a))`. -/
theorem norm_Psi_eq (hg : 2 ≤ g) (s : ℕ) (ℓ a : ℤ) :
    ‖Psi g s ℓ a‖ = (g : ℝ) ^ s * ∏ i ∈ range s, fdig g (theta g s ℓ a i) := by
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
  have hQ : (g : ℝ) ^ s ≠ 0 := pow_ne_zero _ hg0
  -- `ℓ rev_s(m) + a m = Q ∑ᵢ mᵢ θᵢ`, so `Ψ_ℓ(a) = ∏_{i<s} ∑_{d<g} e(-d θᵢ)` (Lemma 2)
  have hPsi : Psi g s ℓ a =
      ∏ i ∈ range s, ∑ d ∈ range g, e ((d : ℝ) * -theta g s ℓ a i) := by
    rw [← sum_prod_digit]
    unfold Psi
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [← e_sum]
    congr 1
    have hm' : (m : ℝ) = ∑ i ∈ range s, (digit g m i : ℝ) * (g : ℝ) ^ i := by
      have := (digit_window hg).1 m s
      rw [Nat.mod_eq_of_lt (mem_range.mp hm)] at this
      exact_mod_cast this
    have hrev : (rev g s m : ℝ) = ∑ i ∈ range s, (digit g m i : ℝ) * (g : ℝ) ^ (s - 1 - i) := by
      unfold rev; push_cast; rfl
    push_cast
    rw [hm', hrev]
    simp only [theta, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  -- each factor is the conjugate of `∑_{d<g} e(d θᵢ)`, of modulus `g f(θᵢ)`
  rw [hPsi, norm_prod, show (g : ℝ) ^ s = ∏ _i ∈ range s, (g : ℝ) by simp,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hconj : ∑ d ∈ range g, e ((d : ℝ) * -theta g s ℓ a i) =
      starRingEnd ℂ (∑ d ∈ range g, e ((d : ℝ) * theta g s ℓ a i)) := by
    rw [map_sum]; simp_rw [e_conj, mul_neg]
  rw [hconj, Complex.norm_conj, fdig, mul_div_cancel₀ _ hg0]

/-- **[HFF 12] Lemma (Fourier inversion).**  For `0 ≤ n < Q`,
`e(-ℓ rev_s(n)/Q) = Q⁻¹ ∑_{a<Q} Ψ_ℓ(a) e(an/Q)`. -/
theorem fourier_inversion (hg : 2 ≤ g) (s : ℕ) (ℓ : ℤ) {n : ℕ} (hn : n < g ^ s) :
    e (-((ℓ : ℝ) * (rev g s n : ℝ) / (g : ℝ) ^ s)) =
      ((g : ℂ) ^ s)⁻¹ * ∑ a ∈ range (g ^ s), Psi g s ℓ a * e ((a : ℝ) * n / (g : ℝ) ^ s) := by
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
  have hQ : (g : ℝ) ^ s ≠ 0 := pow_ne_zero _ hg0
  have hQC : (g : ℂ) ^ s ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : g ≠ 0))
  -- the inner sum `∑_{a<Q} e(a(n-m)/Q)` is `Q` if `m = n` and `0` otherwise
  have hinner : ∀ m ∈ range (g ^ s),
      ∑ a ∈ range (g ^ s), e ((a : ℝ) * (((n : ℝ) - m) / (g : ℝ) ^ s)) =
        if m = n then (g : ℂ) ^ s else 0 := by
    intro m hm
    split_ifs with hmn
    · subst hmn; simp [e_zero]
    · simp_rw [e_nat_mul]
      have hω : e (((n : ℝ) - m) / (g : ℝ) ^ s) ≠ 1 := by
        rw [Ne, e_eq_one_iff]
        rintro ⟨k, hk⟩
        have hk' : ((n : ℤ) - m : ℤ) = k * (g : ℤ) ^ s := by
          have : (n : ℝ) - m = k * (g : ℝ) ^ s := by rw [← hk]; field_simp
          exact_mod_cast this
        have hQpos : (0 : ℤ) < (g : ℤ) ^ s := by positivity
        have hnQ : (n : ℤ) < (g : ℤ) ^ s := by exact_mod_cast hn
        have hmQ : (m : ℤ) < (g : ℤ) ^ s := by exact_mod_cast mem_range.mp hm
        rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
        · nlinarith
        · subst hk0; apply hmn; omega
        · nlinarith
      rw [geom_sum_eq hω, ← e_nat_mul]
      have : ((g ^ s : ℕ) : ℝ) * (((n : ℝ) - m) / (g : ℝ) ^ s) = (((n : ℤ) - m : ℤ) : ℝ) := by
        push_cast; field_simp
      rw [this, e_int, sub_self, zero_div]
  -- expand `Ψ_ℓ(a)` (Definition 9) and exchange the sums
  have hexp : ∀ a ∈ range (g ^ s), Psi g s ℓ a * e ((a : ℝ) * n / (g : ℝ) ^ s) =
      ∑ m ∈ range (g ^ s), e (-((ℓ : ℝ) * (rev g s m : ℝ) / (g : ℝ) ^ s)) *
        e ((a : ℝ) * (((n : ℝ) - m) / (g : ℝ) ^ s)) := by
    intro a _
    unfold Psi
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← e_add, ← e_add]
    congr 1
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun m hm => congrArg (e _ * ·) (hinner m hm)]
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' (range (g ^ s)) n]
  simp only [mem_range.mpr hn, ↓reduceIte]
  field_simp

/-- **[HFF 13] Lemma (Zero frequency).**  If `Q ∤ ℓ` then `Ψ_ℓ(0) = 0`. -/
theorem Psi_zero (hg : 2 ≤ g) (s : ℕ) {ℓ : ℤ} (hℓ : ¬ (g : ℤ) ^ s ∣ ℓ) : Psi g s ℓ 0 = 0 := by
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
  have hQ : (g : ℝ) ^ s ≠ 0 := pow_ne_zero _ hg0
  obtain ⟨hrlt, -, hrr⟩ := rev_involution hg s
  set ω := e (-(ℓ : ℝ) / (g : ℝ) ^ s) with hω
  -- `n = rev_s(m)` runs over `{0,…,Q-1}` as `m` does (Lemma 5), so `Ψ_ℓ(0) = ∑_{n<Q} ωⁿ`
  have h1 : Psi g s ℓ 0 = ∑ n ∈ range (g ^ s), ω ^ n := by
    unfold Psi
    refine Finset.sum_nbij' (rev g s) (rev g s) (fun m _ => mem_range.mpr (hrlt m))
      (fun m _ => mem_range.mpr (hrlt m)) (fun m hm => hrr m (mem_range.mp hm))
      (fun m hm => hrr m (mem_range.mp hm)) fun m _ => ?_
    rw [hω, ← e_nat_mul]
    congr 1
    push_cast
    ring
  -- `ω ≠ 1` as `Q ∤ ℓ`
  have hω1 : ω ≠ 1 := by
    rw [hω, Ne, e_eq_one_iff]
    rintro ⟨k, hk⟩
    apply hℓ
    refine ⟨-k, ?_⟩
    have : (ℓ : ℝ) = (g : ℝ) ^ s * -k := by
      rw [div_eq_iff hQ] at hk; linarith
    exact_mod_cast this
  -- `ω^Q = 1`
  have hωQ : ω ^ (g ^ s) = 1 := by
    rw [hω, ← e_nat_mul]
    have : ((g ^ s : ℕ) : ℝ) * (-(ℓ : ℝ) / (g : ℝ) ^ s) = ((-ℓ : ℤ) : ℝ) := by
      push_cast; field_simp
    rw [this, e_int]
  rw [h1, geom_sum_eq hω1, hωQ, sub_self, zero_div]

/-- Auxiliary for [HFF 14].  `e` is continuous. -/
private theorem continuous_e_aux : Continuous e := by
  unfold e; fun_prop

/-- Auxiliary for [HFF 14].  For a unit complex number `z ≠ 1`, `|1 + z| < 2`. -/
private theorem norm_one_add_lt_two {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) : ‖1 + z‖ < 2 := by
  have h := (not_sameRay_iff_norm_add_lt (x := (1 : ℂ)) (y := z)).mp fun hr =>
    hz1 (hr.eq_of_norm_eq (by rw [norm_one, hz])).symm
  rw [norm_one, hz] at h
  linarith

/-- **[HFF 14] Lemma (Shape of f).**  `f` is continuous and `1`-periodic, `0 ≤ f ≤ 1`, and
`f(θ) < 1` for `θ ∉ ℤ`. -/
theorem fdig_shape (hg : 2 ≤ g) :
    Continuous (fdig g) ∧ (∀ θ, fdig g (θ + 1) = fdig g θ) ∧
    (∀ θ, 0 ≤ fdig g θ ∧ fdig g θ ≤ 1) ∧ (∀ θ : ℝ, (∀ n : ℤ, θ ≠ n) → fdig g θ < 1) := by
  have hgpos : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- continuity
    unfold fdig
    have := continuous_e_aux
    fun_prop
  · -- periodicity: `e(d(θ+1)) = e(dθ + d) = e(dθ)`
    intro θ
    unfold fdig
    congr 2
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [show (d : ℝ) * (θ + 1) = d * θ + ((d : ℤ) : ℝ) by push_cast; ring, e_add_int]
  · -- `0 ≤ f ≤ 1` by the triangle inequality
    intro θ
    refine ⟨div_nonneg (norm_nonneg _) hgpos.le, ?_⟩
    rw [fdig, div_le_one hgpos]
    calc ‖∑ d ∈ range g, e (d * θ)‖ ≤ ∑ d ∈ range g, ‖e (d * θ)‖ := norm_sum_le _ _
      _ = g := by simp [norm_e]
  · -- `f(θ) < 1` for `θ ∉ ℤ`: the terms `d = 0, 1` already lose, as `e(θ) ≠ 1 = e(0)`
    intro θ hθ
    have he1 : e θ ≠ 1 := by
      rw [Ne, e_eq_one_iff]; rintro ⟨n, hn⟩; exact hθ n hn
    rw [fdig, div_lt_one hgpos]
    obtain ⟨n, rfl⟩ : ∃ n, g = n + 2 := ⟨g - 2, by omega⟩
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have hrest : ‖∑ d ∈ range n, e (((d + 1 + 1 : ℕ) : ℝ) * θ)‖ ≤ n := by
      calc ‖∑ d ∈ range n, e (((d + 1 + 1 : ℕ) : ℝ) * θ)‖
          ≤ ∑ d ∈ range n, ‖e (((d + 1 + 1 : ℕ) : ℝ) * θ)‖ := norm_sum_le _ _
        _ = n := by simp [norm_e]
    have h01 : ‖e (((0 + 1 : ℕ) : ℝ) * θ) + e (((0 : ℕ) : ℝ) * θ)‖ < 2 := by
      rw [add_comm]
      simpa [e_zero] using norm_one_add_lt_two (norm_e θ) he1
    calc ‖∑ d ∈ range n, e (((d + 1 + 1 : ℕ) : ℝ) * θ) + e (((0 + 1 : ℕ) : ℝ) * θ) +
          e (((0 : ℕ) : ℝ) * θ)‖
        ≤ ‖∑ d ∈ range n, e (((d + 1 + 1 : ℕ) : ℝ) * θ)‖ +
          ‖e (((0 + 1 : ℕ) : ℝ) * θ) + e (((0 : ℕ) : ℝ) * θ)‖ := by
          rw [add_assoc]; exact norm_add_le _ _
      _ < n + 2 := by linarith
      _ = ((n + 2 : ℕ) : ℝ) := by push_cast; ring

/-- **[HFF 15]** `ε_* = 1/(g²(g+1))`. -/
noncomputable def epsStar (g : ℕ) : ℝ := 1 / ((g : ℝ) ^ 2 * (g + 1))

/-- **[HFF 15]** `u_* = (max_{ε_* ≤ θ ≤ 1-ε_*} f(θ))^{1/2}` (the maximum is attained, Lemma 15). -/
noncomputable def uStar (g : ℕ) : ℝ :=
  Real.sqrt (sSup (fdig g '' Set.Icc (epsStar g) (1 - epsStar g)))

/-- **[HFF 15] Lemma (Uniform gap).**  `0 ≤ u_* < 1`, and `f(θ) ≤ u_*²` whenever `‖θ‖ ≥ ε_*`. -/
theorem uStar_spec (KR : KnownResults) (hg : 2 ≤ g) :
    0 ≤ uStar g ∧ uStar g < 1 ∧ ∀ θ, epsStar g ≤ distZ θ → fdig g θ ≤ uStar g ^ 2 := by
  obtain ⟨hcont, hper, hbd, hlt⟩ := fdig_shape hg
  -- `0 < ε_* < 1/2`
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hε0 : 0 < epsStar g := by unfold epsStar; positivity
  have hε2 : epsStar g < 1 / 2 := by
    unfold epsStar
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- the maximum of `f` on `[ε_*, 1-ε_*]` is attained at some `c`
  obtain ⟨c, hc, hmax⟩ := KR.max_attained (fdig g) (epsStar g) (1 - epsStar g) (by linarith)
    hcont.continuousOn
  have hsup : sSup (fdig g '' Set.Icc (epsStar g) (1 - epsStar g)) = fdig g c :=
    IsGreatest.csSup_eq ⟨⟨c, hc, rfl⟩, by rintro _ ⟨x, hx, rfl⟩; exact hmax x hx⟩
  have hu : uStar g = Real.sqrt (fdig g c) := by rw [uStar, hsup]
  have hu2 : uStar g ^ 2 = fdig g c := by rw [hu, Real.sq_sqrt (hbd c).1]
  -- `c ∉ ℤ`, so `f(c) < 1`
  have hc1 : fdig g c < 1 := by
    apply hlt
    intro n hn
    have h0 : (0 : ℝ) < n := by rw [← hn]; linarith [hc.1]
    have h1 : (n : ℝ) < 1 := by rw [← hn]; linarith [hc.2]
    have h0' : (0 : ℤ) < n := by exact_mod_cast h0
    have h1' : n < (1 : ℤ) := by exact_mod_cast h1
    omega
  refine ⟨by rw [hu]; exact Real.sqrt_nonneg _, ?_, ?_⟩
  · rw [hu, Real.sqrt_lt' one_pos, one_pow]; exact hc1
  · -- if `‖θ‖ ≥ ε_*` then `θ - ⌊θ⌋ ∈ [ε_*, 1-ε_*]`, and `f` has period `1`
    intro θ hθ
    have hP : Function.Periodic (fdig g) 1 := hper
    have hfr : fdig g θ = fdig g (Int.fract θ) := by
      rw [← Int.self_sub_floor, ← hP.sub_int_mul_eq ⌊θ⌋ (x := θ), mul_one]
    have hd : distZ (Int.fract θ) = distZ θ := by
      rw [← Int.self_sub_floor, distZ_sub_int]
    have hmem : Int.fract θ ∈ Set.Icc (epsStar g) (1 - epsStar g) := by
      have hnn := Int.fract_nonneg θ
      have hlt1 := Int.fract_lt_one θ
      have ha := distZ_le_abs_sub (Int.fract θ) 0
      have hb := distZ_le_abs_sub (Int.fract θ) 1
      rw [hd] at ha hb
      push_cast at ha hb
      rw [sub_zero, abs_of_nonneg hnn] at ha
      rw [abs_of_neg (by linarith)] at hb
      constructor <;> linarith
    rw [hfr, hu2]
    exact hmax _ hmem

end PalindromicPowers

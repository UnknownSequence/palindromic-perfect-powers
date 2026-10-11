import PalindromicPowers.Linearisation

/-!
# HFF blocks 46–55: the Fejér majorant and the reduction
-/

namespace PalindromicPowers

open Finset Real

variable {g k : ℕ}

/-- Auxiliary for [HFF 46]: for `|j| < K` there are exactly `K - |j|` pairs `(i, i')` with
`0 ≤ i, i' < K` and `i - i' = j`. -/
private lemma fejer_card (K : ℕ) (j : ℤ) (hj : j ∈ Ioo (-(K : ℤ)) K) :
    (((range K ×ˢ range K).filter (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2 = j)).card : ℤ) =
      K - |j| := by
  rw [mem_Ioo] at hj
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · have hnK : n < K := by omega
    have h : (range K ×ˢ range K).filter (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2 = n) =
        (range (K - n)).image (fun m => (m + n, m)) := by
      ext ⟨a, b⟩
      simp only [mem_filter, mem_product, mem_range, mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨ha, hb⟩, hab⟩
        exact ⟨b, by omega, by omega, rfl⟩
      · rintro ⟨m, hm, rfl, rfl⟩
        refine ⟨⟨by omega, by omega⟩, by push_cast; ring⟩
    rw [h, card_image_of_injective _ (fun m m' hmm => by simpa using hmm), card_range]
    rw [abs_of_nonneg (by positivity)]; omega
  · have hnK : n < K := by omega
    have h : (range K ×ˢ range K).filter (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2 = -n) =
        (range (K - n)).image (fun m => (m, m + n)) := by
      ext ⟨a, b⟩
      simp only [mem_filter, mem_product, mem_range, mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨ha, hb⟩, hab⟩
        exact ⟨a, by omega, rfl, by omega⟩
      · rintro ⟨m, hm, rfl, rfl⟩
        refine ⟨⟨by omega, by omega⟩, by push_cast; ring⟩
    rw [h, card_image_of_injective _ (fun m m' hmm => by simpa using hmm), card_range]
    rw [abs_neg, abs_of_nonneg (by positivity)]; omega

/-- Auxiliary for [HFF 46]: regrouping `∑_{i,i'<K} f(i - i')` by `j = i - i'`. -/
private lemma fejer_regroup (K : ℕ) (f : ℤ → ℂ) :
    ∑ i ∈ range K, ∑ i' ∈ range K, f ((i : ℤ) - i') =
      ∑ j ∈ Ioo (-(K : ℤ)) K, (((K : ℤ) - |j| : ℤ) : ℂ) * f j := by
  rw [← sum_product' (f := fun i i' : ℕ => f ((i : ℤ) - i'))]
  rw [← sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => (p.1 : ℤ) - p.2) (t := Ioo (-(K : ℤ)) K)]
  · refine sum_congr rfl fun j hj => ?_
    rw [sum_congr rfl (g := fun _ => f j) (fun p hp => by rw [(mem_filter.mp hp).2]),
      sum_const, nsmul_eq_mul, ← fejer_card K j hj]
    push_cast; ring
  · rintro ⟨a, b⟩ hp
    simp only [mem_product, mem_range] at hp
    simp only [mem_Ioo]; omega

/-- **[HFF 46] Lemma (Fejér identity).**
`∑_{|j|<K} (1 - |j|/K) e(jx) = K⁻¹ |∑_{i<K} e(ix)|²`. -/
theorem fejer_identity (K : ℕ) (hK : 1 ≤ K) (x : ℝ) :
    ∑ j ∈ Ioo (-(K : ℤ)) K, (((1 - |(j : ℝ)| / K : ℝ)) : ℂ) * e (j * x) =
      ((‖∑ i ∈ range K, e (i * x)‖ ^ 2 / K : ℝ) : ℂ) := by
  have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  -- `|S|² = S · conj S = ∑_{i,i'} e((i - i')x)`
  have h1 : ((‖∑ i ∈ range K, e (i * x)‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ range K, ∑ i' ∈ range K, e ((((i : ℤ) - i' : ℤ) : ℝ) * x) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, sum_mul_sum]
    refine sum_congr rfl fun i _ => sum_congr rfl fun i' _ => ?_
    rw [e_conj, ← e_add]; congr 1; push_cast; ring
  rw [Complex.ofReal_div, h1, Complex.ofReal_natCast, fejer_regroup K (fun j => e (j * x)), sum_div]
  refine sum_congr rfl fun j _ => ?_
  rw [← Complex.ofReal_intCast, Int.cast_sub, Int.cast_abs, Int.cast_natCast]
  push_cast
  field_simp

/-- **[HFF 47] Lemma (Fejér lower bound).**  If `|x| ≤ 1/(2K)` then
`K⁻¹ |∑_{i<K} e(ix)|² ≥ 4K/π²`. -/
theorem fejer_lower (KR : KnownResults) (K : ℕ) (hK : 1 ≤ K) {x : ℝ} (hx : |x| ≤ 1 / (2 * K)) :
    4 * K / π ^ 2 ≤ ‖∑ i ∈ range K, e (i * x)‖ ^ 2 / K := by
  set S := ∑ i ∈ range K, e (i * x) with hS
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  -- It suffices to show `|S| ≥ 2K/π`.
  have key : 2 * K ≤ π * ‖S‖ := by
    rcases eq_or_ne x 0 with rfl | hx0
    · -- For `x = 0`, `S = K`.
      have : S = K := by simp [hS, e_zero]
      rw [this, Complex.norm_natCast]
      nlinarith [pi_gt_three]
    · -- Geometric sum: `S (e(x) - 1) = e(Kx) - 1`, so `|S| |sin πx| = |sin πKx|`.
      have hgeom : S * (e x - 1) = e (K * x) - 1 := by
        rw [hS, e_nat_mul]; simp_rw [e_nat_mul]; exact geom_sum_mul _ _
      have hnorm : ‖S‖ * (2 * |sin (π * x)|) = 2 * |sin (π * (K * x))| := by
        rw [← KR.norm_e_sub_one, ← KR.norm_e_sub_one, ← norm_mul, hgeom]
      -- `|sin πx| ≤ π|x|`
      have h1 : |sin (π * x)| ≤ π * |x| := by
        have := KR.abs_sin_le (π * x); rwa [abs_mul, abs_of_pos pi_pos] at this
      -- `|sin πKx| ≥ 2K|x|`, by Jordan's inequality
      have h2 : 2 * K * |x| ≤ |sin (π * (K * x))| := by
        have hy0 : 0 ≤ π * (K * |x|) := by positivity
        have hKx : K * |x| ≤ 1 / 2 := by
          rw [le_div_iff₀ (by positivity)] at hx
          nlinarith
        have hy1 : π * (K * |x|) ≤ π / 2 := by nlinarith [pi_pos]
        have hJ := KR.jordan _ hy0 hy1
        have habs : |sin (π * (K * x))| = sin (π * (K * |x|)) := by
          have hsin : 0 ≤ sin (π * (K * |x|)) :=
            sin_nonneg_of_nonneg_of_le_pi hy0 (by linarith [pi_pos])
          rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
          · rw [h] at hsin ⊢; exact abs_of_nonneg hsin
          · rw [h, mul_neg, mul_neg, sin_neg] at hsin ⊢; exact abs_of_nonpos (by linarith)
        rw [habs]
        calc 2 * K * |x| = 2 * (π * (K * |x|)) / π := by field_simp
          _ ≤ _ := hJ
      have hxpos : 0 < |x| := abs_pos.mpr hx0
      have h3 : 2 * K * |x| ≤ π * ‖S‖ * |x| := by nlinarith [norm_nonneg S]
      exact le_of_mul_le_mul_right h3 hxpos
  calc 4 * K / π ^ 2 = (2 * K) ^ 2 / π ^ 2 / K := by field_simp; ring
    _ ≤ (π * ‖S‖) ^ 2 / π ^ 2 / K := by gcongr
    _ = ‖S‖ ^ 2 / K := by field_simp

/-- **[HFF 48]** `K = ⌊2Q/3⌋`. -/
def Kq (g s : ℕ) : ℕ := 2 * g ^ s / 3

/-- **[HFF 48] Lemma (Size of K).**  `Q/3 ≤ K ≤ 2Q/3 < Q` (and so `K ≥ 1`). -/
theorem Kq_size (hg : 2 ≤ g) {s : ℕ} (hs : 1 ≤ s) :
    (g : ℝ) ^ s / 3 ≤ Kq g s ∧ (Kq g s : ℝ) ≤ 2 * (g : ℝ) ^ s / 3 ∧ Kq g s < g ^ s ∧ 1 ≤ Kq g s := by
  -- `Q = g^s ≥ 2`
  have hQ : 2 ≤ g ^ s := le_trans hg (Nat.le_self_pow (by omega) g)
  have h1 : g ^ s ≤ 3 * Kq g s := by unfold Kq; omega
  have h2 : 3 * Kq g s ≤ 2 * g ^ s := by unfold Kq; omega
  refine ⟨?_, ?_, by omega, by omega⟩
  · have : ((g ^ s : ℕ) : ℝ) ≤ ((3 * Kq g s : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at this; linarith
  · have : ((3 * Kq g s : ℕ) : ℝ) ≤ ((2 * g ^ s : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at this; linarith

/-- **[HFF 49] Definition (Majorant).**
`F(y) = π²/(4K²) |∑_{i<K} e(i(y-1/4)/Q)|²`. -/
noncomputable def Fmaj (g s : ℕ) (y : ℝ) : ℝ :=
  π ^ 2 / (4 * (Kq g s : ℝ) ^ 2) * ‖∑ i ∈ range (Kq g s), e (i * (y - 1 / 4) / (g : ℝ) ^ s)‖ ^ 2

/-- **[HFF 49]** `F̂_j = π²/(4K) (1 - |j|/K) e(-j/(4Q))` for `|j| < K`. -/
noncomputable def Fhat (g s : ℕ) (j : ℤ) : ℂ :=
  ((π ^ 2 / (4 * (Kq g s : ℝ)) * (1 - |(j : ℝ)| / Kq g s) : ℝ) : ℂ) * e (-(j : ℝ) / (4 * (g : ℝ) ^ s))

/-- Auxiliary for [HFF 50] (also used for [HFF 51]): `F(y) = π²/(4K) · K⁻¹ |∑_{i<K} e(ix)|²`
with `x = (y - 1/4)/Q`. -/
private lemma Fmaj_eq (g s : ℕ) (y : ℝ) :
    Fmaj g s y = π ^ 2 / (4 * Kq g s) *
      (‖∑ i ∈ range (Kq g s), e (i * ((y - 1 / 4) / (g : ℝ) ^ s))‖ ^ 2 / Kq g s) := by
  unfold Fmaj
  simp_rw [mul_div_assoc]
  ring

/-- **[HFF 50] Lemma (The majorant is large).**  `F ≥ 0`, and `F(y) ≥ 1` for `y ∈ [-1/2, 1]`. -/
theorem maj_large (KR : KnownResults) (hg : 2 ≤ g) {s : ℕ} (hs : 1 ≤ s) :
    (∀ y, 0 ≤ Fmaj g s y) ∧ ∀ y : ℝ, -1 / 2 ≤ y → y ≤ 1 → 1 ≤ Fmaj g s y := by
  obtain ⟨-, hK2, -, hK4⟩ := Kq_size hg hs
  have hKpos : (0 : ℝ) < Kq g s := by exact_mod_cast hK4
  have hQpos : (0 : ℝ) < (g : ℝ) ^ s := by positivity
  refine ⟨fun y => by unfold Fmaj; positivity, fun y hy1 hy2 => ?_⟩
  -- `x = (y - 1/4)/Q` satisfies `|x| ≤ 3/(4Q) ≤ 1/(2K)` (Lemma 48)
  have hxK : |(y - 1 / 4) / (g : ℝ) ^ s| ≤ 1 / (2 * Kq g s) := by
    rw [abs_div, abs_of_pos hQpos, div_le_div_iff₀ hQpos (by positivity)]
    have : |y - 1 / 4| ≤ 3 / 4 := by rw [abs_le]; constructor <;> linarith
    nlinarith [abs_nonneg (y - 1 / 4)]
  -- Lemma 47
  have hF := fejer_lower KR (Kq g s) hK4 hxK
  rw [Fmaj_eq g s]
  calc (1 : ℝ) = π ^ 2 / (4 * Kq g s) * (4 * Kq g s / π ^ 2) := by field_simp
    _ ≤ _ := by gcongr

/-- **[HFF 51] Lemma (Majorant coefficients).**  `F(y) = ∑_{|j|<K} F̂_j e(jy/Q)`, with
`|F̂_j| ≤ 8/Q` for `|j| < K`. -/
theorem maj_coeffs (hg : 2 ≤ g) {s : ℕ} (hs : 1 ≤ s) :
    (∀ y : ℝ, (Fmaj g s y : ℂ) =
      ∑ j ∈ Ioo (-(Kq g s : ℤ)) (Kq g s), Fhat g s j * e (j * y / (g : ℝ) ^ s)) ∧
    ∀ j : ℤ, |j| < Kq g s → ‖Fhat g s j‖ ≤ 8 / (g : ℝ) ^ s := by
  obtain ⟨hK1, -, -, hK4⟩ := Kq_size hg hs
  have hKpos : (0 : ℝ) < Kq g s := by exact_mod_cast hK4
  have hQpos : (0 : ℝ) < (g : ℝ) ^ s := by positivity
  refine ⟨fun y => ?_, fun j hj => ?_⟩
  · -- Lemma 46 with `x = (y - 1/4)/Q`
    have hid := fejer_identity (Kq g s) hK4 ((y - 1 / 4) / (g : ℝ) ^ s)
    rw [Fmaj_eq g s, Complex.ofReal_mul, ← hid, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    unfold Fhat
    rw [show (j : ℝ) * ((y - 1 / 4) / (g : ℝ) ^ s) =
        -(j : ℝ) / (4 * (g : ℝ) ^ s) + j * y / (g : ℝ) ^ s by field_simp; ring, e_add]
    push_cast; ring
  · -- `|F̂_j| ≤ π²/(4K) ≤ 3π²/(4Q) < 8/Q`
    unfold Fhat
    rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hj' : |(j : ℝ)| < Kq g s := by rw [← Int.cast_abs]; exact_mod_cast hj
    have h0 : 0 ≤ 1 - |(j : ℝ)| / Kq g s := by
      rw [sub_nonneg, div_le_one hKpos]; exact hj'.le
    have h1 : 1 - |(j : ℝ)| / Kq g s ≤ 1 := by
      have : 0 ≤ |(j : ℝ)| / Kq g s := by positivity
      linarith
    rw [abs_of_nonneg (by positivity)]
    have hpi : π ^ 2 < 10 := by nlinarith [pi_lt_d2, pi_pos]
    calc π ^ 2 / (4 * Kq g s) * (1 - |(j : ℝ)| / Kq g s) ≤ π ^ 2 / (4 * Kq g s) * 1 := by gcongr
      _ ≤ 8 / (g : ℝ) ^ s := by
        rw [mul_one, div_le_div_iff₀ (by positivity) hQpos]
        nlinarith

/-- **[HFF 52] Lemma (Counting in a node).**
`#{x ∈ 𝒬_L : x ≡ b (mod g^t)} ≤ ∑_{z<Z_b} F(λ_b(z) - rev_s(n_b(z)))`. -/
theorem count_in_node (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) {L t s b : ℕ}
    (hA : Admissible L t s) (hb : IsNode g k t b) (hZ : 1 ≤ Zb g k L t b) :
    (((powSet g k L).filter (fun x => x % g ^ t = b)).card : ℝ) ≤
      ∑ z ∈ range (Zb g k L t b), Fmaj g s (lambdaB g k L t s b z - rev g s (nB g k L t s b z)) := by
  obtain ⟨hs, hst, hL⟩ := id hA
  have ht1 : 1 ≤ t := by omega
  have htL : t ≤ L := by omega
  have hgt : 0 < g ^ t := by positivity
  obtain ⟨hF0, hF1⟩ := maj_large KR hg hs
  -- By Lemma 33, each `x` is `x_b + g^t z` with `z = (x - x_b)/g^t < Z_b`, and `x ∈ I_b`.
  have hmem : ∀ x ∈ (powSet g k L).filter (fun x => x % g ^ t = b),
      x = xb g k L t b + g ^ t * ((x - xb g k L t b) / g ^ t) ∧
        (x - xb g k L t b) / g ^ t < Zb g k L t b ∧ InI g k L t b x ∧ x ∈ powSet g k L := by
    intro x hx
    rw [mem_filter] at hx
    obtain ⟨hxQ, hxb⟩ := hx
    obtain ⟨-, hI, z, hz, hxz⟩ := tree hg hk ht1 htL hxQ
    rw [hxb] at hI hz hxz
    have hz' : (x - xb g k L t b) / g ^ t = z := by
      rw [hxz, Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hgt]
    rw [hz']
    exact ⟨hxz, hz, hI, hxQ⟩
  -- distinct `x` give distinct `z`
  have hinj : Set.InjOn (fun x => (x - xb g k L t b) / g ^ t)
      ((powSet g k L).filter (fun x => x % g ^ t = b)) := by
    intro x hx x' hx' h
    rw [(hmem x hx).1, (hmem x' hx').1]
    simp only at h
    rw [h]
  have hg' : (2 : ℝ) ≤ g := by exact_mod_cast hg
  calc (((powSet g k L).filter (fun x => x % g ^ t = b)).card : ℝ)
      = ∑ x ∈ (powSet g k L).filter (fun x => x % g ^ t = b), (1 : ℝ) := by simp
    _ ≤ ∑ x ∈ (powSet g k L).filter (fun x => x % g ^ t = b),
          Fmaj g s (lambdaB g k L t s b ((x - xb g k L t b) / g ^ t : ℕ) -
            rev g s (nB g k L t s b ((x - xb g k L t b) / g ^ t))) := by
        refine sum_le_sum fun x hx => ?_
        obtain ⟨hxz, -, hI, hxQ⟩ := hmem x hx
        rw [hxz] at hI hxQ
        -- Lemma 45: the argument lies in `[-1/g, 1) ⊂ [-1/2, 1]`; then Lemma 50
        obtain ⟨h1, h2⟩ := palindrome_condition KR hg hk hA hb hZ hxQ hI
        refine hF1 _ (le_trans ?_ h1) h2.le
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        linarith
    _ = ∑ z ∈ ((powSet g k L).filter (fun x => x % g ^ t = b)).image
          (fun x => (x - xb g k L t b) / g ^ t),
          Fmaj g s (lambdaB g k L t s b z - rev g s (nB g k L t s b z)) :=
        (sum_image (f := fun z : ℕ => Fmaj g s (lambdaB g k L t s b z - rev g s (nB g k L t s b z)))
          hinj).symm
    _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro z hz
          rw [mem_image] at hz
          obtain ⟨x, hx, rfl⟩ := hz
          exact mem_range.mpr (hmem x hx).2.1
        · intro z _ _
          exact hF0 _

/-- Auxiliary for [HFF 53]: a sum over `0 ≤ a < N` whose `a = 0` term vanishes is a sum over
`0 < a < N`. -/
private lemma sum_range_eq_sum_Ioo (N : ℕ) (h : ℤ → ℝ) (h0 : h 0 = 0) :
    ∑ a ∈ range N, h a = ∑ a ∈ Ioo (0 : ℤ) N, h a := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hIco : ∑ a ∈ Ico (0 : ℤ) N, h a = ∑ a ∈ Ioo (0 : ℤ) N, h a := by
    rw [← Ioo_insert_left (by exact_mod_cast hN), sum_insert left_notMem_Ioo, h0, zero_add]
  rw [← hIco]
  refine sum_nbij' (fun a : ℕ => (a : ℤ)) (fun a : ℤ => a.toNat) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [mem_range, mem_Ico] at ha ⊢; omega
  · intro a ha; simp only [mem_range, mem_Ico] at ha ⊢; omega
  · intro a _; simp
  · intro a ha; simp only [mem_Ico] at ha; omega
  · intro a _; rfl

/-- **[HFF 53] Lemma (Twisted sums).**  For `0 < |j| < Q`,
`|∑_{z<Z_b} e(j(λ_b(z) - rev_s(n_b(z)))/Q)| ≤ Q⁻¹ ∑_{0<a<Q} |Ψ_j(a)| min(Z_b, 1/(2‖θ_{b,j,a}‖))`. -/
theorem twisted_sum (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) {L t s b : ℕ}
    (hA : Admissible L t s) (hb : IsNode g k t b) (hZ : 1 ≤ Zb g k L t b) {j : ℤ} (hj0 : j ≠ 0)
    (hjQ : |j| < (g : ℤ) ^ s) :
    ‖∑ z ∈ range (Zb g k L t b),
        e (j * (lambdaB g k L t s b z - rev g s (nB g k L t s b z)) / (g : ℝ) ^ s)‖ ≤
      1 / (g : ℝ) ^ s * ∑ a ∈ Ioo (0 : ℤ) ((g : ℤ) ^ s),
        ‖Psi g s j a‖ * minDiv (Zb g k L t b) 1 (2 * distZ (thetaB g k L t s b j a)) := by
  have hQpos : (0 : ℝ) < (g : ℝ) ^ s := by positivity
  have hQ0 : 0 < g ^ s := by positivity
  -- the phases `ω_a = j φ_b(0)/Q + a α_b/Q`
  set ω : ℕ → ℝ := fun a =>
    (j : ℝ) * phiB g k L t s b 0 / (g : ℝ) ^ s + (a : ℝ) * alphaB g k L t s b / (g : ℝ) ^ s
    with hω
  -- Lemma 12 with `n = n_b(z)`, and `λ_b(z) = λ_b(0) + δ_b z`
  have hz : ∀ z : ℕ,
      e (j * (lambdaB g k L t s b z - rev g s (nB g k L t s b z)) / (g : ℝ) ^ s) =
        ((g : ℂ) ^ s)⁻¹ * ∑ a ∈ range (g ^ s),
          Psi g s j a * e (ω a) * e (z * thetaB g k L t s b j a) := by
    intro z
    have hn : nB g k L t s b z < g ^ s := Nat.mod_lt _ hQ0
    rw [show (j : ℝ) * (lambdaB g k L t s b z - rev g s (nB g k L t s b z)) / (g : ℝ) ^ s =
        j * lambdaB g k L t s b z / (g : ℝ) ^ s +
          -((j : ℝ) * (rev g s (nB g k L t s b z) : ℝ) / (g : ℝ) ^ s) by ring,
      e_add, fourier_inversion hg s j hn, mul_left_comm, mul_sum]
    congr 1
    refine sum_congr rfl fun a _ => ?_
    -- `α_b + β_b z = n_b(z) + Q m`
    have hdm := Nat.div_add_mod (alphaB g k L t s b + betaB g k s b * z) (g ^ s)
    set m := (alphaB g k L t s b + betaB g k s b * z) / g ^ s
    have hdmR : (g : ℝ) ^ s * m + nB g k L t s b z =
        alphaB g k L t s b + betaB g k s b * z := by
      unfold nB; exact_mod_cast hdm
    have key : e (j * lambdaB g k L t s b z / (g : ℝ) ^ s) * e (a * nB g k L t s b z / (g : ℝ) ^ s) =
        e (ω a) * e (z * thetaB g k L t s b j a) := by
      rw [← e_add, ← e_add, ← e_add_int _ ((a : ℤ) * m)]
      congr 1
      simp only [hω, lambdaB, thetaB]
      push_cast
      field_simp
      linear_combination (a : ℝ) * hdmR
    calc _ = Psi g s j a * (e (j * lambdaB g k L t s b z / (g : ℝ) ^ s) *
          e (a * nB g k L t s b z / (g : ℝ) ^ s)) := by ring
      _ = _ := by rw [key]; ring
  -- sum over `z`, swap the sums, and apply Lemma 6
  rw [sum_congr rfl fun z _ => hz z, ← mul_sum, sum_comm]
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast, one_div]
  gcongr
  -- the term `a = 0` vanishes by Lemma 13
  have hdvd : ¬ (g : ℤ) ^ s ∣ j := fun h => hj0 (Int.eq_zero_of_abs_lt_dvd h hjQ)
  have hsum := sum_range_eq_sum_Ioo (g ^ s)
    (fun a => ‖Psi g s j a‖ * minDiv (Zb g k L t b) 1 (2 * distZ (thetaB g k L t s b j a)))
    (by simp [Psi_zero hg s hdvd])
  push_cast at hsum
  rw [← hsum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun a _ => ?_)
  rw [← mul_sum, norm_mul, norm_mul, norm_e, mul_one]
  gcongr
  exact geom_sum_le KR _ _ hZ

/-- **[HFF 54] Definition (Error term).**
`E(ℬ) = ∑_{b∈ℬ} ∑_{0<|j|<Q} ∑_{0<a<Q} |Ψ_j(a)| min(Z_b, 1/(2‖θ_{b,j,a}‖))`. -/
noncomputable def Eerr (g k L t s : ℕ) (B : Finset ℕ) : ℝ :=
  ∑ b ∈ B, ∑ j ∈ (Ioo (-((g : ℤ) ^ s)) ((g : ℤ) ^ s)).erase 0, ∑ a ∈ Ioo (0 : ℤ) ((g : ℤ) ^ s),
    ‖Psi g s j a‖ * minDiv (Zb g k L t b) 1 (2 * distZ (thetaB g k L t s b j a))

/-- **[HFF 55] Lemma (Reduction).**  For a set `ℬ` of nodes of level `t` with `Z_b ≥ 1`:
`#{x ∈ 𝒬_L : x mod g^t ∈ ℬ} ≤ (8/Q) ∑_{b∈ℬ} Z_b + (8/Q²) E(ℬ)`. -/
theorem reduction (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) {L t s : ℕ} (hA : Admissible L t s)
    (B : Finset ℕ) (hB : ∀ b ∈ B, IsNode g k t b ∧ 1 ≤ Zb g k L t b) :
    (((powSet g k L).filter (fun x => x % g ^ t ∈ B)).card : ℝ) ≤
      8 / (g : ℝ) ^ s * ∑ b ∈ B, (Zb g k L t b : ℝ) + 8 / ((g : ℝ) ^ s) ^ 2 * Eerr g k L t s B := by
  have hs : 1 ≤ s := hA.1
  obtain ⟨-, -, hKQ, hK1⟩ := Kq_size hg hs
  obtain ⟨hFeq, hFhat⟩ := maj_coeffs hg hs
  have hQpos : (0 : ℝ) < (g : ℝ) ^ s := by positivity
  have hKQ' : (Kq g s : ℤ) < (g : ℤ) ^ s := by exact_mod_cast hKQ
  -- the bound for one node `b ∈ ℬ`
  have hnode : ∀ b ∈ B, (((powSet g k L).filter (fun x => x % g ^ t = b)).card : ℝ) ≤
      8 / (g : ℝ) ^ s * Zb g k L t b + 8 / ((g : ℝ) ^ s) ^ 2 *
        ∑ j ∈ (Ioo (-((g : ℤ) ^ s)) ((g : ℤ) ^ s)).erase 0, ∑ a ∈ Ioo (0 : ℤ) ((g : ℤ) ^ s),
          ‖Psi g s j a‖ * minDiv (Zb g k L t b) 1 (2 * distZ (thetaB g k L t s b j a)) := by
    intro b hbB
    obtain ⟨hb, hZ⟩ := hB b hbB
    have hG : ∀ j : ℤ, 0 ≤ ∑ a ∈ Ioo (0 : ℤ) ((g : ℤ) ^ s),
        ‖Psi g s j a‖ * minDiv (Zb g k L t b) 1 (2 * distZ (thetaB g k L t s b j a)) :=
      fun j => sum_nonneg fun a _ => mul_nonneg (norm_nonneg _)
        (minDiv_nonneg (Nat.cast_nonneg _) zero_le_one
          (mul_nonneg zero_le_two (distZ_nonneg _)))
    -- Lemmas 52 and 51: the count is at most `∑_{|j|<K} |F̂_j| |∑_z e(j(λ_b(z) - rev_s(n_b(z)))/Q)|`
    have h2 : (((powSet g k L).filter (fun x => x % g ^ t = b)).card : ℝ) ≤
        ∑ j ∈ Ioo (-(Kq g s : ℤ)) (Kq g s), ‖Fhat g s j‖ *
          ‖∑ z ∈ range (Zb g k L t b),
            e (j * (lambdaB g k L t s b z - rev g s (nB g k L t s b z)) / (g : ℝ) ^ s)‖ := by
      refine (count_in_node KR hg hk hA hb hZ).trans ?_
      calc ∑ z ∈ range (Zb g k L t b),
            Fmaj g s (lambdaB g k L t s b z - rev g s (nB g k L t s b z))
          ≤ ‖((∑ z ∈ range (Zb g k L t b),
            Fmaj g s (lambdaB g k L t s b z - rev g s (nB g k L t s b z)) : ℝ) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
        _ = ‖∑ j ∈ Ioo (-(Kq g s : ℤ)) (Kq g s), Fhat g s j *
              ∑ z ∈ range (Zb g k L t b),
                e (j * (lambdaB g k L t s b z - rev g s (nB g k L t s b z)) / (g : ℝ) ^ s)‖ := by
            rw [Complex.ofReal_sum]
            simp_rw [hFeq, mul_sum]
            rw [sum_comm]
        _ ≤ _ := by
            refine (norm_sum_le _ _).trans (le_of_eq ?_)
            simp_rw [norm_mul]
    -- split off the term `j = 0`
    have h0mem : (0 : ℤ) ∈ Ioo (-(Kq g s : ℤ)) (Kq g s) := by
      rw [mem_Ioo]; constructor <;> omega
    rw [← add_sum_erase _ _ h0mem] at h2
    -- the term `j = 0` is at most `8 Z_b/Q`
    have h3 : ‖Fhat g s 0‖ * ‖∑ z ∈ range (Zb g k L t b),
        e (((0 : ℤ) : ℝ) * (lambdaB g k L t s b z - rev g s (nB g k L t s b z)) / (g : ℝ) ^ s)‖ ≤
        8 / (g : ℝ) ^ s * Zb g k L t b := by
      simp only [Int.cast_zero, zero_mul, zero_div, e_zero, sum_const, card_range, nsmul_eq_mul,
        mul_one, Complex.norm_natCast]
      gcongr
      exact hFhat 0 (by simp; omega)
    -- the others by Lemma 53, as `K < Q` (Lemma 48)
    have h4 : ∑ j ∈ (Ioo (-(Kq g s : ℤ)) (Kq g s)).erase 0, ‖Fhat g s j‖ *
          ‖∑ z ∈ range (Zb g k L t b),
            e (j * (lambdaB g k L t s b z - rev g s (nB g k L t s b z)) / (g : ℝ) ^ s)‖ ≤
        8 / ((g : ℝ) ^ s) ^ 2 *
          ∑ j ∈ (Ioo (-((g : ℤ) ^ s)) ((g : ℤ) ^ s)).erase 0, ∑ a ∈ Ioo (0 : ℤ) ((g : ℤ) ^ s),
            ‖Psi g s j a‖ * minDiv (Zb g k L t b) 1 (2 * distZ (thetaB g k L t s b j a)) := by
      rw [mul_sum]
      calc _ ≤ ∑ j ∈ (Ioo (-(Kq g s : ℤ)) (Kq g s)).erase 0, 8 / ((g : ℝ) ^ s) ^ 2 *
              ∑ a ∈ Ioo (0 : ℤ) ((g : ℤ) ^ s),
                ‖Psi g s j a‖ * minDiv (Zb g k L t b) 1 (2 * distZ (thetaB g k L t s b j a)) := by
            refine sum_le_sum fun j hj => ?_
            rw [mem_erase, mem_Ioo] at hj
            have hjK : |j| < Kq g s := abs_lt.mpr ⟨hj.2.1, hj.2.2⟩
            have hjQ : |j| < (g : ℤ) ^ s := lt_trans hjK hKQ'
            calc _ ≤ 8 / (g : ℝ) ^ s * (1 / (g : ℝ) ^ s * ∑ a ∈ Ioo (0 : ℤ) ((g : ℤ) ^ s),
                  ‖Psi g s j a‖ * minDiv (Zb g k L t b) 1 (2 * distZ (thetaB g k L t s b j a))) :=
                  mul_le_mul (hFhat j hjK) (twisted_sum KR hg hk hA hb hZ hj.1 hjQ)
                    (norm_nonneg _) (by positivity)
              _ = _ := by field_simp
        _ ≤ _ := by
            apply sum_le_sum_of_subset_of_nonneg
            · intro j hj
              simp only [mem_erase, mem_Ioo] at hj ⊢
              exact ⟨hj.1, by linarith, by linarith⟩
            · intro j _ _
              have := hG j
              positivity
    linarith
  -- sum over `b ∈ ℬ`
  rw [card_eq_sum_card_fiberwise (f := fun x => x % g ^ t) (t := B)
    (s := (powSet g k L).filter (fun x => x % g ^ t ∈ B))
    (by intro x hx; rw [mem_coe, mem_filter] at hx; exact mem_coe.mpr hx.2)]
  push_cast
  calc ∑ b ∈ B, ((((powSet g k L).filter (fun x => x % g ^ t ∈ B)).filter
        (fun x => x % g ^ t = b)).card : ℝ)
      = ∑ b ∈ B, (((powSet g k L).filter (fun x => x % g ^ t = b)).card : ℝ) := by
        refine sum_congr rfl fun b hb => ?_
        rw [filter_filter]
        congr 2
        refine filter_congr fun x _ => ?_
        constructor
        · exact fun h => h.2
        · intro h; exact ⟨h ▸ hb, h⟩
    _ ≤ _ := (sum_le_sum hnode).trans (le_of_eq (by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum]; rfl))

end PalindromicPowers

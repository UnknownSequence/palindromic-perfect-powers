import PalindromicPowers.PowerSaving

/-!
# HFF blocks 28–36: palindromes and the tree of nodes
-/

namespace PalindromicPowers

open Finset Real

variable {g k : ℕ}

/-- **[HFF 28] Definition (Palindromes).**  `𝒫_L`: the integers `g^{L-1} ≤ n < g^L` with
`nᵢ = n_{L-1-i}` for all `i < L`. -/
def palSet (g L : ℕ) : Finset ℕ :=
  (Ico (g ^ (L - 1)) (g ^ L)).filter (fun n => ∀ i < L, digit g n i = digit g n (L - 1 - i))

/-- **[HFF 28]** `𝒬_L = {x ∈ ℕ : x^k ∈ 𝒫_L}`.  (Such `x` satisfy `x ≤ x^k < g^L`, so the
filter over `range (g^L)` loses nothing; see `mem_powSet_iff`.) -/
def powSet (g k L : ℕ) : Finset ℕ := (range (g ^ L)).filter (fun x => x ^ k ∈ palSet g L)

/-- **[HFF 28]** `X = g^{L/k}`. -/
noncomputable def Xr (g k L : ℕ) : ℝ := (g : ℝ) ^ ((L : ℝ) / k)

/-- Auxiliary for [HFF 29] (also used in [HFF 30] and [HFF 32]).  Two numbers `< g^t` with the
same digits `nᵢ`, `i < t`, are equal (Lemma 4: `n = n mod g^t = ∑_{r<t} n_r g^r`). -/
private lemma eq_of_digits_eq (hg : 2 ≤ g) {t a b : ℕ} (ha : a < g ^ t) (hb : b < g ^ t)
    (h : ∀ i < t, digit g a i = digit g b i) : a = b := by
  have h1 := (digit_window hg).1
  calc a = a % g ^ t := (Nat.mod_eq_of_lt ha).symm
    _ = ∑ r ∈ range t, digit g a r * g ^ r := h1 a t
    _ = ∑ r ∈ range t, digit g b r * g ^ r :=
        Finset.sum_congr rfl (fun r hr => by rw [h r (Finset.mem_range.mp hr)])
    _ = b % g ^ t := (h1 b t).symm
    _ = b := Nat.mod_eq_of_lt hb

/-- Auxiliary for [HFF 29] (also used in [HFF 30] and [HFF 32]).  If the digit `n_j` is nonzero
then `g^j ≤ n`. -/
private lemma pow_le_of_digit_ne_zero {n j : ℕ} (h : digit g n j ≠ 0) : g ^ j ≤ n := by
  by_contra hlt
  rw [not_le] at hlt
  unfold digit at h
  rw [Nat.div_eq_of_lt hlt, Nat.zero_mod] at h
  exact h rfl

/-- Auxiliary for [HFF 29] (also used in [HFF 30]).  If `g^{L-1} ≤ n < g^L` with `L ≥ 1`, the
leading digit `n_{L-1} = ⌊n/g^{L-1}⌋` is nonzero. -/
private lemma top_digit_pos {L n : ℕ} (hg : 2 ≤ g) (hL : 1 ≤ L) (hlo : g ^ (L - 1) ≤ n)
    (hhi : n < g ^ L) : 0 < digit g n (L - 1) := by
  have hgp : 0 < g ^ (L - 1) := pow_pos (by omega) _
  have h1 : 1 ≤ n / g ^ (L - 1) := (Nat.le_div_iff_mul_le hgp).2 (by simpa using hlo)
  have h2 : n / g ^ (L - 1) < g := by
    rw [Nat.div_lt_iff_lt_mul hgp, ← pow_succ', Nat.sub_add_cancel hL]
    exact hhi
  unfold digit
  rw [Nat.mod_eq_of_lt h2]
  omega

/-- Auxiliary for [HFF 29].  The digit tuple `(n_0, …, n_{L-1})` of the palindrome whose top
`H = ⌈L/2⌉` digits are those of `m`: `n_{L-H+j} = m_j` for `j < H` and `n_i = n_{L-1-i}` for
`i < L - H`. -/
private def palDigits (g L m i : ℕ) : ℕ :=
  if i < L - (L + 1) / 2 then digit g m ((L + 1) / 2 - 1 - i)
  else digit g m (i - (L - (L + 1) / 2))

/-- **[HFF 29] Lemma (Many palindromes).**  `#𝒫_L ≥ g^{L/2-1}`, hence `X ≤ (g #𝒫_L)^{2/k}`. -/
theorem many_palindromes (hg : 2 ≤ g) (hk : 2 ≤ k) {L : ℕ} (hL : 1 ≤ L) :
    (g : ℝ) ^ ((L : ℝ) / 2 - 1) ≤ (palSet g L).card ∧
    Xr g k L ≤ ((g : ℝ) * (palSet g L).card) ^ ((2 : ℝ) / k) := by
  have hg0 : 0 < g := by omega
  -- `H = ⌈L/2⌉` digits are chosen freely (the top one nonzero), the others are mirrored.
  obtain ⟨H, hH⟩ : ∃ H, H = (L + 1) / 2 := ⟨_, rfl⟩
  have hH1 : 1 ≤ H := by omega
  let φ : ℕ → ℕ := fun m => ∑ i ∈ range L, palDigits g L m i * g ^ i
  have hdig : ∀ m, ∀ i < L, palDigits g L m i < g := by
    intro m i _
    unfold palDigits digit
    split_ifs <;> exact Nat.mod_lt _ hg0
  -- Lemma 4: the digits of `φ m` are the `palDigits`.
  have hφdig : ∀ m, ∀ i < L, digit g (φ m) i = palDigits g L m i :=
    fun m => (digit_window hg).2.2 L (palDigits g L m) (hdig m)
  have htop : ∀ m, ∀ j < H, digit g (φ m) (L - H + j) = digit g m j := by
    intro m j hj
    rw [hφdig m (L - H + j) (by omega)]
    unfold palDigits
    split_ifs with h
    · omega
    · congr 1; omega
  have hmaps : ∀ m ∈ Ico (g ^ (H - 1)) (g ^ H), φ m ∈ palSet g L := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    unfold palSet
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨?_, (digits_bijection hg L).1 _ (hdig m)⟩, ?_⟩
    · -- the leading digit `n_{L-1} = m_{H-1}` is nonzero
      apply pow_le_of_digit_ne_zero
      have h := htop m (H - 1) (by omega)
      rw [show L - H + (H - 1) = L - 1 by omega] at h
      rw [h]
      exact (top_digit_pos hg hH1 hm.1 hm.2).ne'
    · intro i hi
      rw [hφdig m i hi, hφdig m (L - 1 - i) (by omega)]
      unfold palDigits
      split_ifs <;> congr 1 <;> omega
  -- distinct choices give distinct palindromes (Lemma 2)
  have hinj : Set.InjOn φ (Ico (g ^ (H - 1)) (g ^ H) : Set ℕ) := by
    intro m hm m' hm' h
    simp only [Finset.coe_Ico, Set.mem_Ico] at hm hm'
    apply eq_of_digits_eq hg hm.2 hm'.2
    intro j hj
    rw [← htop m j hj, ← htop m' j hj, h]
  have hcard : g ^ (H - 1) ≤ (palSet g L).card := by
    have h1 := Finset.card_le_card_of_injOn φ (fun m hm => hmaps m hm) hinj
    rw [Nat.card_Ico] at h1
    have h2 : g ^ H = g * g ^ (H - 1) := by rw [← pow_succ', Nat.sub_add_cancel hH1]
    have h3 : 2 * g ^ (H - 1) ≤ g * g ^ (H - 1) := Nat.mul_le_mul_right _ hg
    omega
  have hG1 : (1 : ℝ) ≤ g := by exact_mod_cast (by omega : 1 ≤ g)
  have hG0 : (0 : ℝ) < g := by linarith
  have hP : (g : ℝ) ^ ((L : ℝ) / 2 - 1) ≤ (palSet g L).card := by
    calc (g : ℝ) ^ ((L : ℝ) / 2 - 1) ≤ (g : ℝ) ^ (((H - 1 : ℕ)) : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hG1
          rw [Nat.cast_sub hH1]
          have : (L : ℝ) ≤ 2 * H := by exact_mod_cast (by omega : L ≤ 2 * H)
          push_cast
          linarith
      _ = ((g ^ (H - 1) : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; rfl
      _ ≤ (palSet g L).card := by exact_mod_cast hcard
  refine ⟨hP, ?_⟩
  -- `X = (g^{L/2})^{2/k} ≤ (g #𝒫_L)^{2/k}`
  have h1 : (g : ℝ) ^ ((L : ℝ) / 2) ≤ (g : ℝ) * (palSet g L).card := by
    calc (g : ℝ) ^ ((L : ℝ) / 2) = (g : ℝ) * (g : ℝ) ^ ((L : ℝ) / 2 - 1) := by
          rw [Real.rpow_sub_one hG0.ne']
          field_simp
      _ ≤ (g : ℝ) * (palSet g L).card := mul_le_mul_of_nonneg_left hP hG0.le
  calc Xr g k L = ((g : ℝ) ^ ((L : ℝ) / 2)) ^ ((2 : ℝ) / k) := by
        unfold Xr
        rw [← Real.rpow_mul hG0.le]
        congr 1
        ring
    _ ≤ ((g : ℝ) * (palSet g L).card) ^ ((2 : ℝ) / k) :=
        Real.rpow_le_rpow (by positivity) h1 (by positivity)

/-- Auxiliary for [HFF 30] (also used in [HFF 32]).  For `i < t`, the digit `i` of `n mod g^t`
is the digit `i` of `n` (Lemma 4). -/
private lemma digit_mod_pow (hg : 2 ≤ g) (n t i : ℕ) (hi : i < t) :
    digit g (n % g ^ t) i = digit g n i := by
  rw [(digit_window hg).1 n t]
  exact (digit_window hg).2.2 t (digit g n) (fun j _ => Nat.mod_lt _ (by omega)) i hi

/-- **[HFF 30] Lemma (First digits of palindromes).**  For `n ∈ 𝒫_L` and `1 ≤ t ≤ L`:
`g ∤ n` and `⌊n/g^{L-t}⌋ = rev_t(n mod g^t)`. -/
theorem first_digits (hg : 2 ≤ g) {L n t : ℕ} (hn : n ∈ palSet g L) (ht1 : 1 ≤ t) (htL : t ≤ L) :
    ¬ g ∣ n ∧ n / g ^ (L - t) = rev g t (n % g ^ t) := by
  unfold palSet at hn
  rw [Finset.mem_filter, Finset.mem_Ico] at hn
  obtain ⟨⟨hlo, hhi⟩, hpal⟩ := hn
  have hg0 : 0 < g := by omega
  constructor
  · -- `n mod g = n_0 = n_{L-1} = ⌊n/g^{L-1}⌋ ≥ 1`, as `n ≥ g^{L-1}`
    intro hdvd
    have h0 : digit g n 0 = 0 := by
      simp only [digit, pow_zero, Nat.div_one]
      exact Nat.mod_eq_zero_of_dvd hdvd
    have h1 := hpal 0 (by omega)
    simp only [Nat.sub_zero] at h1
    have h2 := top_digit_pos hg (by omega) hlo hhi
    omega
  · -- the digits of `⌊n/g^{L-t}⌋` are `n_{L-t+r} = n_{t-1-r}`, those of `rev_t(n mod g^t)`
    have hgt : 0 < g ^ (L - t) := pow_pos hg0 _
    have hq : n / g ^ (L - t) < g ^ t := by
      rw [Nat.div_lt_iff_lt_mul hgt, ← pow_add, Nat.add_sub_of_le htL]
      exact hhi
    apply eq_of_digits_eq hg hq ((rev_involution hg t).1 _)
    intro i hi
    rw [(rev_involution hg t).2.1 _ i hi, digit_mod_pow hg n t (t - 1 - i) (by omega)]
    have e1 : digit g (n / g ^ (L - t)) i = digit g n (L - t + i) := by
      simp only [digit, Nat.div_div_eq_div_mul, ← pow_add]
    rw [e1, hpal (L - t + i) (by omega)]
    congr 1
    omega

/-- **[HFF 31] Definition (Nodes).**  A node of level `t` is an integer `0 ≤ b < g^t`
with `g ∤ b^k`. -/
def IsNode (g k t b : ℕ) : Prop := b < g ^ t ∧ ¬ g ∣ b ^ k

instance (g k t b : ℕ) : Decidable (IsNode g k t b) := by unfold IsNode; infer_instance

/-- **[HFF 31]** `T_b = rev_t(b^k mod g^t)`. -/
def Tb (g k t b : ℕ) : ℕ := rev g t (b ^ k % g ^ t)

/-- **[HFF 31]** `y₀ = T_b g^{L-t}`. -/
def y0 (g k L t b : ℕ) : ℕ := Tb g k t b * g ^ (L - t)

/-- **[HFF 31]** `y₁ = y₀ + g^{L-t}`. -/
def y1 (g k L t b : ℕ) : ℕ := y0 g k L t b + g ^ (L - t)

/-- **[HFF 31]** `I_b = [y₀^{1/k}, y₁^{1/k})`; an integer `x ≥ 0` lies in `I_b` iff
`y₀ ≤ x^k < y₁`. -/
def InI (g k L t b x : ℕ) : Prop := y0 g k L t b ≤ x ^ k ∧ x ^ k < y1 g k L t b

instance (g k L t b x : ℕ) : Decidable (InI g k L t b x) := by unfold InI; infer_instance

/-- **[HFF 31]** `|I_b| = y₁^{1/k} - y₀^{1/k}`. -/
noncomputable def Ilen (g k L t b : ℕ) : ℝ :=
  (y1 g k L t b : ℝ) ^ ((1 : ℝ) / k) - (y0 g k L t b : ℝ) ^ ((1 : ℝ) / k)

/-- **[HFF 31]** The integers `x ∈ I_b` with `x ≡ b (mod g^t)`. -/
def nodeElems (g k L t b : ℕ) : Finset ℕ :=
  (range (g ^ L)).filter (fun x => x % g ^ t = b ∧ InI g k L t b x)

/-- **[HFF 31]** `Z_b`, the number of integers `x ∈ I_b` with `x ≡ b (mod g^t)`. -/
def Zb (g k L t b : ℕ) : ℕ := (nodeElems g k L t b).card

/-- **[HFF 31]** `x_b`, the least integer `x ∈ I_b` with `x ≡ b (mod g^t)` (if `Z_b ≥ 1`). -/
def xb (g k L t b : ℕ) : ℕ :=
  if h : (nodeElems g k L t b).Nonempty then (nodeElems g k L t b).min' h else 0

/-- **[HFF 31]** `Z(t) = X g^{-2t}`. -/
noncomputable def Zt (g k L t : ℕ) : ℝ := Xr g k L / (g : ℝ) ^ (2 * t)

/-- **[HFF 32] Lemma (Leading digit).**  For a node `b` of level `t ≥ 1`: `g^{t-1} ≤ T_b < g^t`. -/
theorem leading_digit (hg : 2 ≤ g) {t b : ℕ} (ht : 1 ≤ t) (hb : IsNode g k t b) :
    g ^ (t - 1) ≤ Tb g k t b ∧ Tb g k t b < g ^ t := by
  obtain ⟨-, hbk⟩ := hb
  have hR := rev_involution hg t
  refine ⟨?_, hR.1 _⟩
  -- `n_0 = b^k mod g ≠ 0`
  have h0 : digit g (b ^ k % g ^ t) 0 ≠ 0 := by
    rw [digit_mod_pow hg (b ^ k) t 0 (by omega)]
    simp only [digit, pow_zero, Nat.div_one]
    intro h
    exact hbk (Nat.dvd_of_mod_eq_zero h)
  -- so the digit `t-1` of `T_b = rev_t(n)` is `n_0 ≠ 0`
  have h1 : digit g (Tb g k t b) (t - 1) ≠ 0 := by
    unfold Tb
    rw [hR.2.1 (b ^ k % g ^ t) (t - 1) (by omega), Nat.sub_self]
    exact h0
  exact pow_le_of_digit_ne_zero h1

/-- **[HFF 33] Lemma (The tree).**  For `1 ≤ t ≤ L` and `x ∈ 𝒬_L`: `b = x mod g^t` is a node,
`x ∈ I_b`, and `x = x_b + g^t z` for an integer `0 ≤ z < Z_b`. -/
theorem tree (hg : 2 ≤ g) (hk : 2 ≤ k) {L t x : ℕ} (ht1 : 1 ≤ t) (htL : t ≤ L)
    (hx : x ∈ powSet g k L) :
    IsNode g k t (x % g ^ t) ∧ InI g k L t (x % g ^ t) x ∧
      ∃ z, z < Zb g k L t (x % g ^ t) ∧ x = xb g k L t (x % g ^ t) + g ^ t * z := by
  unfold powSet at hx
  rw [Finset.mem_filter, Finset.mem_range] at hx
  obtain ⟨hxL, hpal⟩ := hx
  have hg0 : 0 < g := by omega
  have hgt : 0 < g ^ t := pow_pos hg0 t
  generalize hb : x % g ^ t = b
  -- Lemma 30 with `n = x^k`
  obtain ⟨hndvd, hfirst⟩ := first_digits hg hpal ht1 htL
  have hbg : b % g = x % g := by
    rw [← hb]
    exact Nat.mod_mod_of_dvd x (dvd_pow_self g (by omega))
  have hnode : IsNode g k t b := by
    refine ⟨hb ▸ Nat.mod_lt _ hgt, ?_⟩
    intro hdvd
    apply hndvd
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.pow_mod, ← hbg, ← Nat.pow_mod]
    exact Nat.mod_eq_zero_of_dvd hdvd
  -- `b^k mod g^t = x^k mod g^t`, so `⌊x^k/g^{L-t}⌋ = T_b`
  have hT : x ^ k / g ^ (L - t) = Tb g k t b := by
    rw [hfirst]
    unfold Tb
    rw [← hb, ← Nat.pow_mod]
  have hI : InI g k L t b x := by
    have hgLt : 0 < g ^ (L - t) := pow_pos hg0 _
    unfold InI y1 y0
    rw [← hT]
    constructor
    · exact Nat.div_mul_le_self _ _
    · have h := Nat.lt_mul_div_succ (x ^ k) hgLt
      rw [mul_add, mul_one, Nat.mul_comm (g ^ (L - t))] at h
      exact h
  refine ⟨hnode, hI, ?_⟩
  -- `x` is one of the integers `x_b + g^t z`, `0 ≤ z < Z_b`, in `I_b`
  have hmem : x ∈ nodeElems g k L t b := by
    unfold nodeElems
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hxL, hb, hI⟩
  have hne : (nodeElems g k L t b).Nonempty := ⟨x, hmem⟩
  have hxb : xb g k L t b = (nodeElems g k L t b).min' hne := by
    unfold xb
    split_ifs
    rfl
  obtain ⟨x0, hx0⟩ : ∃ x0, (nodeElems g k L t b).min' hne = x0 := ⟨_, rfl⟩
  have hx0mem : x0 ∈ nodeElems g k L t b := hx0 ▸ Finset.min'_mem _ _
  have hx0le : x0 ≤ x := hx0 ▸ Finset.min'_le _ _ hmem
  unfold nodeElems at hx0mem
  rw [Finset.mem_filter, Finset.mem_range] at hx0mem
  obtain ⟨-, hx0b, hx0I⟩ := hx0mem
  have hmod : x0 ≡ x [MOD g ^ t] := by
    unfold Nat.ModEq
    rw [hx0b, hb]
  obtain ⟨z, hz⟩ := (Nat.modEq_iff_dvd' hx0le).1 hmod
  have hxz : x = x0 + g ^ t * z := by omega
  refine ⟨z, ?_, by rw [hxb, hx0]; exact hxz⟩
  -- the `z + 1` integers `x_b + g^t j`, `j ≤ z`, all lie in `I_b` and are `≡ b`
  unfold Zb
  have hcard : (range (z + 1)).card ≤ (nodeElems g k L t b).card := by
    apply Finset.card_le_card_of_injOn (fun j => x0 + g ^ t * j)
    · intro j hj
      simp only [Finset.coe_range, Set.mem_Iio] at hj
      simp only [Finset.mem_coe]
      unfold nodeElems
      rw [Finset.mem_filter, Finset.mem_range]
      have hjz : g ^ t * j ≤ g ^ t * z := Nat.mul_le_mul_left _ (by omega)
      have hle : x0 + g ^ t * j ≤ x := by omega
      unfold InI at hx0I hI ⊢
      refine ⟨by omega, ?_, ?_, ?_⟩
      · rw [Nat.add_mul_mod_self_left]
        exact hx0b
      · exact le_trans hx0I.1 (Nat.pow_le_pow_left (by omega) k)
      · exact lt_of_le_of_lt (Nat.pow_le_pow_left hle k) hI.2
    · intro j1 _ j2 _ h
      simp only at h
      exact Nat.eq_of_mul_eq_mul_left hgt (by omega)
  rw [Finset.card_range] at hcard
  exact hcard

/-- Auxiliary for [HFF 34].  The integer inequalities `g^{L-1} ≤ y₀ < y₁ ≤ min(g^L, 2y₀)`,
from `g^{t-1} ≤ T_b < g^t` (Lemma 32). -/
private lemma endpoints_nat (hg : 2 ≤ g) {L t b : ℕ} (ht1 : 1 ≤ t) (htL : t ≤ L)
    (hb : IsNode g k t b) :
    g ^ (L - 1) ≤ y0 g k L t b ∧ y0 g k L t b < y1 g k L t b ∧ y1 g k L t b ≤ g ^ L ∧
    y1 g k L t b ≤ 2 * y0 g k L t b := by
  obtain ⟨hT1, hT2⟩ := leading_digit hg ht1 hb
  have hp : 0 < g ^ (L - t) := pow_pos (by omega) _
  have hT0 : 1 ≤ Tb g k t b := le_trans (Nat.one_le_pow _ _ (by omega)) hT1
  have e1 : g ^ (L - 1) = g ^ (t - 1) * g ^ (L - t) := by
    rw [← pow_add]; congr 1; omega
  have e2 : g ^ L = g ^ t * g ^ (L - t) := by
    rw [← pow_add]; congr 1; omega
  unfold y1 y0
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1]
    exact Nat.mul_le_mul_right _ hT1
  · omega
  · rw [e2]
    calc Tb g k t b * g ^ (L - t) + g ^ (L - t) = (Tb g k t b + 1) * g ^ (L - t) := by ring
      _ ≤ g ^ t * g ^ (L - t) := Nat.mul_le_mul_right _ hT2
  · have := Nat.mul_le_mul_right (g ^ (L - t)) hT0
    omega

/-- Auxiliary for [HFF 34].  The mean value theorem for `y ↦ y^{1/k}` on `[a, c]`, `0 < a < c`:
`c^{1/k} - a^{1/k} = (c - a)/(k ξ^{1-1/k})` for some `ξ ∈ [a, c]`. -/
private lemma rpow_inv_mvt (KR : KnownResults) (hk : 2 ≤ k) {a c : ℝ} (ha : 0 < a) (hac : a < c) :
    ∃ ξ : ℝ, a ≤ ξ ∧ ξ ≤ c ∧
      c ^ ((1 : ℝ) / k) - a ^ ((1 : ℝ) / k) = (c - a) / (k * ξ ^ (1 - (1 : ℝ) / k)) := by
  have hderiv : ∀ y : ℝ, 0 < y →
      HasDerivAt (fun y : ℝ => y ^ ((1 : ℝ) / k)) ((1 : ℝ) / k * y ^ ((1 : ℝ) / k - 1)) y :=
    fun y hy => Real.hasDerivAt_rpow_const (Or.inl hy.ne')
  obtain ⟨ξ, hξ, hξd⟩ := KR.mvt (fun y : ℝ => y ^ ((1 : ℝ) / k)) a c hac
    (Real.continuous_rpow_const (by positivity)).continuousOn
    (fun y hy => (hderiv y (ha.trans hy.1)).differentiableAt.differentiableWithinAt)
  have hξ0 : 0 < ξ := ha.trans hξ.1
  rw [(hderiv ξ hξ0).deriv] at hξd
  refine ⟨ξ, hξ.1.le, hξ.2.le, ?_⟩
  rw [eq_div_iff (sub_pos.2 hac).ne'] at hξd
  rw [← hξd, show (1 : ℝ) / k - 1 = -(1 - 1 / k) by ring, Real.rpow_neg hξ0.le]
  ring

/-- **[HFF 34] Lemma (Interval endpoints).**  `g^{L-1} ≤ y₀ < y₁ ≤ min(g^L, 2y₀)`, and
`|I_b| = g^{L-t}/(k ξ^{1-1/k})` for some `ξ ∈ [y₀, y₁]`. -/
theorem interval_endpoints (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) {L t b : ℕ}
    (ht1 : 1 ≤ t) (htL : t ≤ L) (hb : IsNode g k t b) :
    g ^ (L - 1) ≤ y0 g k L t b ∧ y0 g k L t b < y1 g k L t b ∧ y1 g k L t b ≤ g ^ L ∧
    y1 g k L t b ≤ 2 * y0 g k L t b ∧
    ∃ ξ : ℝ, (y0 g k L t b : ℝ) ≤ ξ ∧ ξ ≤ y1 g k L t b ∧
      Ilen g k L t b = (g : ℝ) ^ (L - t) / (k * ξ ^ (1 - (1 : ℝ) / k)) := by
  obtain ⟨hA, hB, hC, hD⟩ := endpoints_nat hg ht1 htL hb
  have hy0pos : (0 : ℝ) < y0 g k L t b := by
    have : 0 < g ^ (L - 1) := pow_pos (by omega) _
    exact_mod_cast this.trans_le hA
  -- the mean value theorem for `y ↦ y^{1/k}` on `[y₀, y₁]`
  obtain ⟨ξ, h1, h2, h3⟩ := rpow_inv_mvt KR hk hy0pos
    (by exact_mod_cast hB : (y0 g k L t b : ℝ) < y1 g k L t b)
  refine ⟨hA, hB, hC, hD, ξ, h1, h2, ?_⟩
  unfold Ilen
  rw [h3]
  congr 1
  unfold y1
  push_cast
  ring

/-- Auxiliary for [HFF 35].  An interval `[α, β)` (`0 ≤ α ≤ β`) contains between
`(β - α)/q - 1` and `(β - α)/q + 1` natural numbers `≡ b (mod q)`. -/
private lemma count_residue_class {q b : ℕ} (hq : 0 < q) (hb : b < q) {α β : ℝ} (hα : 0 ≤ α)
    (hαβ : α ≤ β) (S : Finset ℕ) (hS : ∀ x : ℕ, x ∈ S ↔ x % q = b ∧ α ≤ x ∧ (x : ℝ) < β) :
    (β - α) / q - 1 ≤ S.card ∧ (S.card : ℝ) ≤ (β - α) / q + 1 := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hbq : (b : ℝ) < q := by exact_mod_cast hb
  -- `S = {b + q j : u ≤ j < v}` with `u = (α - b)/q`, `v = (β - b)/q`
  have hSeq : S = (Ico ⌈(α - b) / q⌉₊ ⌈(β - b) / q⌉₊).image (fun j => b + q * j) := by
    ext x
    rw [hS, Finset.mem_image]
    constructor
    · rintro ⟨hxb, hαx, hxβ⟩
      have hx' : b + q * (x / q) = x := by
        have := Nat.mod_add_div x q
        rwa [hxb] at this
      have hx : (x : ℝ) = b + q * ((x / q : ℕ) : ℝ) := by exact_mod_cast hx'.symm
      refine ⟨x / q, ?_, hx'⟩
      rw [Finset.mem_Ico, Nat.ceil_le, Nat.lt_ceil, div_le_iff₀ hqr, lt_div_iff₀ hqr]
      rw [hx] at hαx hxβ
      constructor <;> linarith
    · rintro ⟨j, hj, rfl⟩
      rw [Finset.mem_Ico, Nat.ceil_le, Nat.lt_ceil, div_le_iff₀ hqr, lt_div_iff₀ hqr] at hj
      refine ⟨?_, ?_, ?_⟩
      · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
      · push_cast
        linarith [hj.1]
      · push_cast
        linarith [hj.2]
  have hinj : Function.Injective (fun j : ℕ => b + q * j) := by
    intro j1 j2 h
    simp only at h
    exact Nat.eq_of_mul_eq_mul_left hq (by omega)
  rw [hSeq, Finset.card_image_of_injective _ hinj, Nat.card_Ico]
  have huv : (α - b) / q ≤ (β - b) / q := by gcongr
  rw [Nat.cast_sub (Nat.ceil_mono huv)]
  have hvu : (β - α) / q = (β - b) / q - (α - b) / q := by
    rw [div_sub_div_same]
    congr 1
    ring
  rw [hvu]
  have hu : -1 < (α - b) / q := by
    rw [lt_div_iff₀ hqr]
    linarith
  have h1 := Nat.le_ceil ((α - b) / q)
  have h2 := Nat.le_ceil ((β - b) / q)
  have h3 : (⌈(α - b) / q⌉₊ : ℝ) < (α - b) / q + 1 := by
    rcases le_or_gt 0 ((α - b) / q) with h | h
    · exact Nat.ceil_lt_add_one h
    · rw [Nat.ceil_eq_zero.2 h.le]
      push_cast
      linarith
  have h4 : (⌈(β - b) / q⌉₊ : ℝ) < (β - b) / q + 1 := by
    rcases le_or_gt 0 ((β - b) / q) with h | h
    · exact Nat.ceil_lt_add_one h
    · rw [Nat.ceil_eq_zero.2 h.le]
      push_cast
      linarith
  constructor <;> linarith

/-- Auxiliary for [HFF 35].  An integer `x ≥ 0` lies in `I_b` iff `y₀^{1/k} ≤ x < y₁^{1/k}`, and
such `x` satisfy `x ≤ x^k < y₁ ≤ g^L`; so `Z_b` counts the integers `≡ b (mod g^t)` in the real
interval `I_b`. -/
private lemma mem_nodeElems_iff (hk : 2 ≤ k) {L t b : ℕ} (hy1 : y1 g k L t b ≤ g ^ L) (x : ℕ) :
    x ∈ nodeElems g k L t b ↔ x % g ^ t = b ∧ (y0 g k L t b : ℝ) ^ ((1 : ℝ) / k) ≤ x ∧
      (x : ℝ) < (y1 g k L t b : ℝ) ^ ((1 : ℝ) / k) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have e1 : (y0 g k L t b : ℝ) ^ ((1 : ℝ) / k) ≤ x ↔ y0 g k L t b ≤ x ^ k := by
    rw [one_div, Real.rpow_inv_le_iff_of_pos (Nat.cast_nonneg _) hx0 hkpos, Real.rpow_natCast,
      ← Nat.cast_pow, Nat.cast_le]
  have e2 : (x : ℝ) < (y1 g k L t b : ℝ) ^ ((1 : ℝ) / k) ↔ x ^ k < y1 g k L t b := by
    rw [one_div, Real.lt_rpow_inv_iff_of_pos hx0 (Nat.cast_nonneg _) hkpos, Real.rpow_natCast,
      ← Nat.cast_pow, Nat.cast_lt]
  unfold nodeElems InI
  rw [Finset.mem_filter, Finset.mem_range, e1, e2]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h1, h2, h3⟩
    calc x ≤ x ^ k := Nat.le_self_pow (by omega) x
      _ < y1 g k L t b := h3
      _ ≤ g ^ L := hy1

/-- **[HFF 35] Lemma (Node sizes).**  `Z(t)/k ≤ |I_b| g^{-t} ≤ g Z(t)/k` and
`Z(t)/k - 1 ≤ Z_b ≤ g Z(t)/k + 1`. -/
theorem node_sizes (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) {L t b : ℕ}
    (ht1 : 1 ≤ t) (htL : t ≤ L) (hb : IsNode g k t b) :
    Zt g k L t / k ≤ Ilen g k L t b / (g : ℝ) ^ t ∧ Ilen g k L t b / (g : ℝ) ^ t ≤ g * Zt g k L t / k ∧
    Zt g k L t / k - 1 ≤ Zb g k L t b ∧ (Zb g k L t b : ℝ) ≤ g * Zt g k L t / k + 1 := by
  obtain ⟨hA, hB, hC, -, ξ, hξ0, hξ1, hI⟩ := interval_endpoints KR hg hk ht1 htL hb
  have hg0 : 0 < g := by omega
  have hG : (1 : ℝ) ≤ g := by exact_mod_cast (by omega : 1 ≤ g)
  have hG0 : (0 : ℝ) < g := by linarith
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hGt : (0 : ℝ) < (g : ℝ) ^ t := pow_pos hG0 t
  have hs0 : 0 ≤ 1 - (1 : ℝ) / k := by
    rw [sub_nonneg, div_le_one hkpos]
    exact_mod_cast (by omega : 1 ≤ k)
  have hξpos : 0 < ξ := by
    have : (0 : ℝ) < y0 g k L t b := by exact_mod_cast (pow_pos hg0 (L - 1)).trans_le hA
    linarith
  have hP : 0 < ξ ^ (1 - (1 : ℝ) / k) := Real.rpow_pos_of_pos hξpos _
  have hGL : (g : ℝ) ^ L = (g : ℝ) ^ (L - t) * (g : ℝ) ^ t := by
    rw [← pow_add, Nat.sub_add_cancel htL]
  -- `g^{(L-1)(1-1/k)} ≤ ξ^{1-1/k} ≤ g^{L(1-1/k)}`, as `g^{L-1} ≤ y₀ ≤ ξ ≤ y₁ ≤ g^L`
  have hξup : ξ ^ (1 - (1 : ℝ) / k) ≤ (g : ℝ) ^ ((L : ℝ) * (1 - (1 : ℝ) / k)) := by
    rw [Real.rpow_mul hG0.le, Real.rpow_natCast]
    apply Real.rpow_le_rpow hξpos.le _ hs0
    calc ξ ≤ y1 g k L t b := hξ1
      _ ≤ (g : ℝ) ^ L := by exact_mod_cast hC
  have hξlow : (g : ℝ) ^ (((L : ℝ) - 1) * (1 - (1 : ℝ) / k)) ≤ ξ ^ (1 - (1 : ℝ) / k) := by
    rw [Real.rpow_mul hG0.le]
    apply Real.rpow_le_rpow (by positivity) _ hs0
    calc (g : ℝ) ^ ((L : ℝ) - 1) = (g : ℝ) ^ (L - 1) := by
          rw [← Real.rpow_natCast, Nat.cast_sub (by omega : 1 ≤ L), Nat.cast_one]
      _ ≤ y0 g k L t b := by exact_mod_cast hA
      _ ≤ ξ := hξ0
  have hX1 : (g : ℝ) ^ ((L : ℝ) / k) * (g : ℝ) ^ ((L : ℝ) * (1 - (1 : ℝ) / k)) = (g : ℝ) ^ L := by
    rw [← Real.rpow_add hG0, ← Real.rpow_natCast]
    congr 1
    ring
  have hX2 : (g : ℝ) ^ L ≤
      (g : ℝ) * (g : ℝ) ^ ((L : ℝ) / k) * (g : ℝ) ^ (((L : ℝ) - 1) * (1 - (1 : ℝ) / k)) := by
    rw [← Real.rpow_one_add' hG0.le, ← Real.rpow_add hG0, ← Real.rpow_natCast]
    · apply Real.rpow_le_rpow_of_exponent_le hG
      have : (0 : ℝ) ≤ 1 / k := by positivity
      have e : 1 + (L : ℝ) / k + ((L : ℝ) - 1) * (1 - 1 / k) = L + 1 / k := by ring
      rw [e]
      linarith
    · positivity
  have hZt : Zt g k L t = (g : ℝ) ^ ((L : ℝ) / k) / ((g : ℝ) ^ t) ^ 2 := by
    unfold Zt Xr
    ring
  -- `|I_b| g^{-t}` lies between `Z(t)/k` and `g Z(t)/k`
  have hlow : Zt g k L t / k ≤ Ilen g k L t b / (g : ℝ) ^ t := by
    rw [hZt, hI, div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    calc (g : ℝ) ^ ((L : ℝ) / k) * (k * ξ ^ (1 - (1 : ℝ) / k) * (g : ℝ) ^ t)
        = ((g : ℝ) ^ ((L : ℝ) / k) * ξ ^ (1 - (1 : ℝ) / k)) * (k * (g : ℝ) ^ t) := by ring
      _ ≤ ((g : ℝ) ^ ((L : ℝ) / k) * (g : ℝ) ^ ((L : ℝ) * (1 - (1 : ℝ) / k))) *
            (k * (g : ℝ) ^ t) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hξup (by positivity))
            (by positivity)
      _ = (g : ℝ) ^ (L - t) * (((g : ℝ) ^ t) ^ 2 * k) := by rw [hX1, hGL]; ring
  have hup : Ilen g k L t b / (g : ℝ) ^ t ≤ g * Zt g k L t / k := by
    have eL : Ilen g k L t b / (g : ℝ) ^ t =
        (g : ℝ) ^ (L - t) / (k * ξ ^ (1 - (1 : ℝ) / k) * (g : ℝ) ^ t) := by
      rw [hI, div_div]
    have eR : g * Zt g k L t / k = g * (g : ℝ) ^ ((L : ℝ) / k) / (((g : ℝ) ^ t) ^ 2 * k) := by
      rw [hZt]
      ring
    rw [eL, eR, div_le_div_iff₀ (by positivity) (by positivity)]
    calc (g : ℝ) ^ (L - t) * (((g : ℝ) ^ t) ^ 2 * k) = (g : ℝ) ^ L * (k * (g : ℝ) ^ t) := by
          rw [hGL]; ring
      _ ≤ ((g : ℝ) * (g : ℝ) ^ ((L : ℝ) / k) * (g : ℝ) ^ (((L : ℝ) - 1) * (1 - (1 : ℝ) / k))) *
            (k * (g : ℝ) ^ t) := mul_le_mul_of_nonneg_right hX2 (by positivity)
      _ ≤ ((g : ℝ) * (g : ℝ) ^ ((L : ℝ) / k) * ξ ^ (1 - (1 : ℝ) / k)) * (k * (g : ℝ) ^ t) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hξlow (by positivity))
            (by positivity)
      _ = g * (g : ℝ) ^ ((L : ℝ) / k) * (k * ξ ^ (1 - (1 : ℝ) / k) * (g : ℝ) ^ t) := by ring
  -- an interval of length `|I_b|` contains `|I_b| g^{-t} ± 1` integers `≡ b (mod g^t)`
  have hα : (0 : ℝ) ≤ (y0 g k L t b : ℝ) ^ ((1 : ℝ) / k) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hαβ : (y0 g k L t b : ℝ) ^ ((1 : ℝ) / k) ≤ (y1 g k L t b : ℝ) ^ ((1 : ℝ) / k) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hB.le) (by positivity)
  have hbt : b < g ^ t := hb.1
  obtain ⟨hc1, hc2⟩ := count_residue_class (pow_pos hg0 t) hbt hα hαβ (nodeElems g k L t b)
    (mem_nodeElems_iff hk hC)
  have hIlen : Ilen g k L t b =
      (y1 g k L t b : ℝ) ^ ((1 : ℝ) / k) - (y0 g k L t b : ℝ) ^ ((1 : ℝ) / k) := rfl
  rw [← hIlen, Nat.cast_pow] at hc1 hc2
  refine ⟨hlow, hup, ?_, ?_⟩
  · unfold Zb
    linarith
  · unfold Zb
    linarith

/-- **[HFF 36] Lemma (Nodes are not empty).**  If `Z(t) ≥ 2k`, every node `b` of level `t`
has `1 ≤ Z_b ≤ 2g Z(t)/k`. -/
theorem nodes_nonempty (KR : KnownResults) (hg : 2 ≤ g) (hk : 2 ≤ k) {L t b : ℕ}
    (ht1 : 1 ≤ t) (htL : t ≤ L) (hZ : 2 * (k : ℝ) ≤ Zt g k L t) (hb : IsNode g k t b) :
    1 ≤ Zb g k L t b ∧ (Zb g k L t b : ℝ) ≤ 2 * g * Zt g k L t / k := by
  obtain ⟨-, -, h3, h4⟩ := node_sizes KR hg hk ht1 htL hb
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hG : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have h2 : (2 : ℝ) ≤ Zt g k L t / k := by
    rw [le_div_iff₀ hkpos]
    linarith
  have e : g * Zt g k L t / k = g * (Zt g k L t / k) := by ring
  have h5 : (1 : ℝ) ≤ g * Zt g k L t / k := by
    rw [e]
    nlinarith
  constructor
  · have : (1 : ℝ) ≤ Zb g k L t b := by linarith
    exact_mod_cast this
  · have e2 : 2 * g * Zt g k L t / k = 2 * (g * Zt g k L t / k) := by ring
    rw [e2]
    linarith

end PalindromicPowers

# HFF notation and the Lean formalization

The Lean-friendly HFF document `out/palindromic_powers_hff_lean.pdf` (built by `build.py` from
`blocks.py` and `overview.py`) has the same 102 blocks as `palindromic_powers_hff.tex`, and its
statements are those of the Lean files `../PalindromicPowers/*.lean`. Every Lean declaration that
formalizes block *n* has a docstring beginning `**[HFF n]**`; the PDF and the map name these
declarations in a grey line under each statement. Remarks (blocks 27, 69, 102) have no Lean
counterpart.

## General rules

| HFF | Lean |
|---|---|
| `g ≥ 2`, `k ≥ 2` fixed (Definition 1) | explicit hypotheses `hg : 2 ≤ g`, `hk : 2 ≤ k` |
| the analytic prerequisites (overview, *Prerequisites*) | the fields of `KR : KnownResults` (`Assumptions.lean`; proved from Mathlib in `Discharge.lean`) |
| `A ≪ B` for `L` large | `∃ C₁ L₀, ∀ L ≥ L₀, A ≤ C₁ * B` (all such `A` are `≥ 0`, so `\|A\| ≤ C₁B` and `A ≤ C₁B` agree) |
| for `L` large: *P* | `∃ L₀, ∀ L ≥ L₀, P` |
| `min(A, H/y)`, with `min(A, H/0) := A` (the convention `H/0 = ∞`) | `minDiv A H y` |
| finite sets, `#S`, `∑`, `∏` | `Finset`, `S.card`, `∑ x ∈ S`, `∏ x ∈ S` |
| `0 < \|j\| < Q`, `0 < a < Q` | `(Ioo (-Q) Q).erase 0`, `Ioo 0 Q` |
| `Q = g^s` | `g ^ s` (in ℕ) or `(g : ℝ) ^ s` |
| `n mod q`, `⌊n/q⌋` for integers `n ≥ 0` | `n % q`, `n / q` (natural-number division) |
| the setting of Definition 37 | `Admissible L t s` (plus a node `b` with `1 ≤ Zb g k L t b` where needed) |
| the setting of Definition 70 | `FreqSetting g k L t s ℓ D B` |

## Notation (Definitions 1–93)

| HFF | Lean | Block |
|---|---|---|
| `e(x) = e^{2πix}` | `e x` | D1 |
| `‖x‖` (distance to the nearest integer) | `distZ x` | D1 |
| `min(A, H/y)` | `minDiv A H y` | D1 |
| `n_i` (the `i`-th digit, `⌊n/gⁱ⌋ mod g`) | `digit g n i` | D3 |
| `rev_j(n)` | `rev g j n` | D3 |
| `Ψ_ℓ(a)` | `Psi g s ℓ a` | D9 |
| `M(ℓ)` | `Mmax g s ℓ` | D9 |
| `S(s)` | `Ssum g s` | D9 |
| `f(θ)` | `fdig g θ` | D9 |
| `θ_i = θ_i(ℓ, a)` | `theta g s ℓ a i` | D9 |
| `ε_*`, `u_*` | `epsStar g`, `uStar g` | L15 |
| `ℓ' = (g²-1)ℓ mod Q` | `twist g s ℓ` | D18 |
| `i` is bad for `r` | `IsBad g r i` | D18 |
| `β_n(r)` | `badCount g n r` | D18 |
| `b(ℓ) = β_s(ℓ')` | `bBad g s ℓ` | D18 |
| `ρ` | `rho g` | L25 |
| `c`, `C` | `cSave g`, `CSave g` | L26 |
| `𝒫_L` | `palSet g L` | D28 |
| `𝒬_L` | `powSet g k L` | D28 |
| `X = g^{L/k}` | `Xr g k L` | D28 |
| `b` is a node of level `t` | `IsNode g k t b` | D31 |
| `T_b` | `Tb g k t b` | D31 |
| `y_0`, `y_1` | `y0 g k L t b`, `y1 g k L t b` | D31 |
| `x ∈ I_b` (integer `x ≥ 0`) | `InI g k L t b x` | D31 |
| `\|I_b\|` | `Ilen g k L t b` | D31 |
| the integers `x ∈ I_b` with `x ≡ b (mod g^t)` | `nodeElems g k L t b` | D31 |
| `Z_b` | `Zb g k L t b` | D31 |
| `x_b` | `xb g k L t b` | D31 |
| `Z(t)` (and `Z = Z(t)`) | `Zt g k L t` | D31 |
| `1 ≤ s ≤ t-2`, `2(t+s) ≤ L` | `Admissible L t s` | D37 |
| `Λ` | `LambdaT g t` | D37 |
| `α_b`, `β_b`, `d_b` | `alphaB g k L t s b`, `betaB g k s b`, `dB g k s b` | D37 |
| `δ_b` | `deltaB g k L t s b` | D37 |
| `θ_{b,ℓ,a}` | `thetaB g k L t s b ℓ a` | D37 |
| `n_b(z)` | `nB g k L t s b z` | D37 |
| `φ_b(z)`, `λ_b(z)` | `phiB g k L t s b z`, `lambdaB g k L t s b z` | D38 |
| `δ(T)` | `deltaT g k L t s T` | D38 |
| `K = ⌊2Q/3⌋` | `Kq g s` | L48 |
| `F(y)` | `Fmaj g s y` | D49 |
| `F̂_j` | `Fhat g s j` | D49 |
| `E(ℬ)` | `Eerr g k L t s B` | D54 |
| `v_p(n)` | `n.factorization p` (Mathlib) | D60 |
| `m_g(n)` | `mg g n` | D60 |
| `ω(g)` | `omegaG g` | D60 |
| `P` | `Pmax g` | D60 |
| `τ(D)` | `tauG g D` | D60 |
| the setting of D70 | `FreqSetting g k L t s ℓ D B` | D70 |
| `Z_+` | `Zplus g k L t` | D70 |
| `y_b` | `yB g k L t s b ℓ` | D70 |
| `Φ_b` | `PhiB g k L t s b ℓ` | D70 |
| `W_ℓ` | `Wl g k L t s B ℓ` | D70 |
| `h_d(T)` | `hd g k L t s ℓ d T` | D74 |
| `𝒯_d` | `Tset g k L t s ℓ d` | D74 |
| `μ` | `muD g k L t s ℓ d` | D74 |
| `Δ` | `DeltaD g k L t s ℓ d` | D74 |
| `ε_b` | `epsB g k L t s b` | L75 |
| `ℬ₂` | `B.filter (fun b => d_b/2 < \|ℓ\| δ_b)` | L84 |
| the nodes `b` of level `t` with `m_g(b) ≤ D` | `nodesSmall g k t D` | L86 |
| `V` | `Vterm g k L t s D` | L86 |
| `t' = ⌈L/(2k)⌉` | `tPrime k L` | L88 |
| `η`, `ν` | `eta g k`, `nu g` | D90 |
| `D = X^η` | `Dpar g k L` | D90 |
| `t = ⌊L/(k(4-c))⌋`, `s = t-2` | `tpar g k L`, `spar g k L` | D90 |
| `ℬ` (the main set of nodes) | `Bmain g k L` | D93 |

## Lean-friendly changes relative to the original HFF document

The block order, labels and numbering (1–102) are unchanged. Statements were changed as follows
(proofs were adjusted minimally; all stay under 300 characters).

* **D1** Conventions: `min(A, H/0) := A` (the convention `H/0 = ∞`) is stated explicitly;
  "`A ≪ B` for `L` large" means: there are `C₁`, `L₀` depending only on `g`, `k` with
  `|A| ≤ C₁B` for all `L ≥ L₀`.
* **L2** Digits: stated for every `j ≥ 0` (Lean `digits_bijection` has no `j ≥ 1`).
* **D3** Digits are defined for all `n, i ≥ 0` by `n_i := ⌊n/gⁱ⌋ mod g`, and
  `rev_j(n) := ∑_{i<j} n_i g^{j-1-i}` for every `n` (D3 no longer cites L2).
* **L4** Blocks of digits: holds for all `n ≥ 0` (no `n < g^j`); new third claim: if
  `d_r ∈ {0,…,g-1}` for `r < j`, the digits of `∑_{r<j} d_r g^r` are `d_0,…,d_{j-1}`. New proof
  (induction via `n mod g^{i+1} = n mod g^i + g^i n_i`; third claim from the first with `i = j` and
  the uniqueness in L2).
* **L5** `rev_j` maps every `n` into `[0, g^j)`; the digits of `rev_j(n)` are `n_{j-1-i}`;
  `rev_j(rev_j(n)) = n` for `n < g^j` (the sentence "so `rev_j` is a bijection" was dropped).
* **L15** `ε_* := 1/(g²(g+1))` and `u_* := (sup_{ε_*≤θ≤1-ε_*} f(θ))^{1/2}` are defined in the
  statement; claim `0 ≤ u_* < 1` and `f(θ) ≤ u_*²` when `‖θ‖ ≥ ε_*`.
* **D18** `β_n(r)` := the number of `0 ≤ i ≤ n-2` with `(r_{i+1}, r_i) ∉ {(0,0), (g-1,g-1)}`
  (for `n ≥ 1`, `r ≥ 0`), and `b(ℓ) := β_s(ℓ')`.
* **L19** `ℓ ↦ ℓ'` is a bijection of `{0,…,Q-1}`, and `ℓ'` (hence `b(ℓ)`) depends only on
  `ℓ mod Q`.
* **L21, L22** "if `i` is bad" became "if `0 ≤ i ≤ s-2` is bad for `ℓ'`".
* **L24** `∑_{0≤r<gⁿ} u^{β_n(r)} ≤ g(1+(g-1)u)^{n-1}` (digit strings are the digits of the
  `r < gⁿ`, by L2 and L4).
* **L25** `ρ := 1+(g-1)u_*` is defined in the statement; claims `ρ < g` and `S(s) ≤ 2gQρ^{s-1}`.
* **L26** `c := min(1 - log_g ρ, log 2/(2 log g))` and `C := 2g` are defined in the statement;
  claims `0 < c ≤ log 2/(2 log g)`, `C ≥ 1`, `S(s) ≤ C g^{(2-c)s}` for `s ≥ 1`.
* **D31** also defines `y_0 := T_b g^{L-t}`, `y_1 := y_0 + g^{L-t}`, `I_b := [y_0^{1/k}, y_1^{1/k})`
  (an integer `x ≥ 0` lies in `I_b` iff `y_0 ≤ x^k < y_1`) and `|I_b| := y_1^{1/k} - y_0^{1/k}`;
  **L34** no longer defines `y_0`, `y_1`, and L40, L43 take them from D31.
* **D37** `β_b` and `d_b` are defined for every node `b` (as Lean's `betaB`, `dB`), the other
  quantities for nodes with `Z_b ≥ 1`; **L62** accordingly drops the hypothesis `Z_b ≥ 1`.
* **L48** adds `K ≥ 1`.
* **D49** also defines `F̂_j := (π²/(4K))(1 - |j|/K) e(-j/(4Q))` for `|j| < K`; **L51** states
  `F(y) = ∑_{|j|<K} F̂_j e(jy/Q)` and `|F̂_j| ≤ 8/Q`.
* **L56** stated for any integer `Q ≥ 1`, with the equivalent form
  `∑_{0≤a<Q} φ(aβ mod Q) = d ∑_{0≤r<Q/d} φ(rd)` for every function `φ`.
* **D60** `m_g(n)` is defined for integers `n ≥ 1` (Lean `mg` lives on ℕ); **L87**, **L88** say
  `n ≥ 1` instead of `n ≠ 0`.
* **D74** `h_d(T)` is defined for all real `T > 0`, and `μ := (1-1/k)|h_d(gᵗ)|/gᵗ`,
  `Δ := |h_d(gᵗ) - h_d(g^{t-1})|` are defined here. **L77**: `|h_d|` non-decreasing,
  `h_d' = (1-1/k)h_d/T`, `|h_d'|` non-increasing, `|h_d'(T)| ≤ gμ` (`μ = |h_d'(gᵗ)|`).
  **L78** uses `μ` from D74. **L79**: `h_d(T)` lies between `h_d(g^{t-1})` and `h_d(gᵗ)` for
  `T ∈ 𝒯_d`, `Δ ≤ g^{t+1}μ` and `Δ ≤ kg^{2s}/(dZ)`.
* **L80, L81** weighted form: finitely many reals `y_i` with integer weights `w_i ≥ 0`, every
  half-open interval of length `μ` carrying total weight `≤ m` (`m ≥ 1` real); conclusions
  `∑ w_i min(A, H/|y_i - n|) ≤ …` and `∑ w_i min(A, H/‖y_i‖) ≤ …`; in L81 the interval is
  `[a_0, a_0 + Δ]` with `Δ ≥ 0`.
* **L82** `κ ≥ 1` real, integers `0 ≤ N_T ≤ κ`; proof applies L81 with weights `N_T`;
  `μ`, `Δ` from D74 (L83 now cites D74 too).
* **L88** `t' := ⌈L/(2k)⌉` is defined in the statement, with the new claim
  `X^{1/2} ≤ g^{t'} < gX^{1/2}`; hypothesis `L ≥ 1` instead of "`L` large".
* **D90** `t := ⌊L/(k(4-c))⌋` (`= ⌊log_g X/(4-c)⌋`); the proof of **L91** says why
  `gᵗ ≤ X^{1/(4-c)} < g^{t+1}`.
* **T101** `γ ∈ (0, 1)` (Lean also states `0 < γ`).
* **Overview**: the subtitle names the Lean-friendly version; *Prerequisites* says where the
  prerequisites live in Lean (Lean/Mathlib; `KnownResults` in `PalindromicPowers/Assumptions.lean`,
  documented in `assumptions.md`, proved in `PalindromicPowers/Discharge.lean`) and that no
  published result is assumed; *About this document* describes the correspondence.
* Proof-only changes, to use the digit facts of L4 (D3 now defines digits by a formula): L11, L20,
  L29, L30.

## Remaining differences (Lean is more general)

These are not changes of meaning: in each case the Lean statement implies the HFF statement.

* Definition 9 fixes `s ≥ 1`, as do all blocks after it; the Lean lemmas `Psi_periodic`,
  `norm_Psi_eq`, `fourier_inversion`, `Psi_zero`, `twist_bijective` and `Mmax_le` (blocks 10–13,
  19, 23) hold for every `s ≥ 0`.
* Definition 31 fixes `1 ≤ t ≤ L`; `leading_digit` (L32) only needs `1 ≤ t`, and `dB_dvd` (L62)
  needs no relation between `t`, `s` and `L`.
* Definition 1 fixes `k ≥ 2`; `binomial_congr` (L63) holds for every `k`, and
  `close_roots_agree`, `roots_mod_prime_pow` (L64, L65) for `k ≥ 1`.
* Lemmas 77–79 are stated in the setting of Definition 70; `hd_shape`, `gaps` and `range_bound`
  need only `Admissible L t s` (and `|ℓ| < Q` for L79).
* `A ≪ B` is `|A| ≤ C₁B` in the HFF and `A ≤ C₁ * B` in Lean; every such `A` is non-negative.

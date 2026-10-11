# Palindromic perfect powers: a power saving over the Cilleruelo–Luca–Shparlinski bound

How many palindromes with `L` digits in base `g` are perfect `k`-th powers? Cilleruelo, Luca and
Shparlinski [CLS] showed that there are at most a constant times `(#𝒫_L)^{1/k}` of them, where
`𝒫_L` is the set of `L`-digit palindromes (`#𝒫_L ≈ g^{L/2}`). This repository contains a proof
that the exponent `1/k` can be lowered to `γ/k` for some `γ < 1`, **for every base `g ≥ 2` and
every exponent `k ≥ 2`**. It has three parts:

| | |
|---|---|
| **Paper** with explicit exponents (`γ = 0.9674` for `g = 2`) and the certified computation behind them | [`paper/palindromic_powers.pdf`](paper/palindromic_powers.pdf) ([tex](paper/palindromic_powers.tex), [scripts](paper/scripts/)) |
| **HFF document**: a short, self-contained proof that `γ < 1` exists, in Human Friendly Form | [`hff/out/palindromic_powers_hff_lean.pdf`](hff/out/palindromic_powers_hff_lean.pdf) ([tex](hff/out/palindromic_powers_hff_lean.tex)) |
| **Interactive map** of the HFF proof's dependency graph, with the Lean status of every block | [`hff/out/palindromic_powers_hff_lean_map.html`](hff/out/palindromic_powers_hff_lean_map.html) (download and open in a browser) |
| **Lean 4 formalization** of the HFF document: complete, no `sorry`, only Lean's standard axioms | [`PalindromicPowers/`](PalindromicPowers/), trust boundary in [`assumptions.md`](assumptions.md) |

## The result

Fix a base `g ≥ 2` and an exponent `k ≥ 2`. Let `𝒫_L` be the set of palindromes with exactly
`L` digits in base `g`, and let `𝒬_L` be the set of those that are perfect `k`-th powers.

**Theorem.** There are `γ = γ(g,k) < 1` and `C′ = C′(g,k)` such that for every `L ≥ 1`,

    #𝒬_L ≤ C′ · (#𝒫_L)^{γ/k}.

**What this means.** Since `#𝒫_L` grows like `g^{L/2}`, the bound `(#𝒫_L)^{γ/k}` is smaller than
the Cilleruelo–Luca–Shparlinski bound `(#𝒫_L)^{1/k}` by the factor `(#𝒫_L)^{(1−γ)/k}`, which
tends to infinity with `L`. So palindromic perfect powers are rarer, by a power of `#𝒫_L`, than
the previous bound allowed, in every base and for every exponent.

**Explicit exponents** (paper, Corollary 1.3; these rely on a certified numerical computation):

| prime-power base `g` (every `k`) | 2 | 3 | 4 | 5 | 7 | 8 | 9 | 16 |
|---|---|---|---|---|---|---|---|---|
| `γ` | 0.9674 | 0.9744 | 0.9794 | 0.9820 | 0.9849 | 0.9863 | 0.9870 | 0.9904 |

| other base `g` | 6 | 10 | 12 |
|---|---|---|---|
| `γ`, `k = 2` | 0.9893 | 0.9917 | 0.9924 |
| `γ`, `k = 3` | 0.9936 | 0.9950 | 0.9954 |

For example, the number of `L`-digit palindromic squares in base 10 is `≪ (#𝒫_L)^{0.4959}`,
where [CLS] gives `(#𝒫_L)^{0.5}`.

The HFF document and the Lean formalization prove the qualitative statement (some `γ < 1`,
namely `γ = 1 − c/(32k)` for an explicit but tiny `c = c(g) > 0`) without any computer
calculation. The explicit values above come from the paper's certified computation and are not
part of the Lean formalization.

## How it improves on Cilleruelo–Luca–Shparlinski

[CLS] sort the candidates `x` (with `x^k ∈ 𝒫_L`) by their last `t` digits. Those determine the
last `t` digits of `x^k`, hence, by the palindrome condition, its first `t` digits, which confine
`x` to a short arithmetic progression. Counting all of these progressions gives `(#𝒫_L)^{1/k}`.

The new argument also uses the **next `s` digits from both ends**:

1. Inside one progression, the digits of `x^k` just above the last `t` are an affine function of
   the progression index modulo `g^s`. The digits just below the first `t` are, up to an error
   of `1/g`, an affine function over the reals. The palindrome condition says the second block
   is the digit reversal of the first.
2. This condition is detected with a Fejér-kernel majorant, and the digit-reversal map is expanded
   in additive characters. The coefficients are the **reversal transform**
   `Ψ_ℓ(a) = Σ_m e(−(ℓ·rev_s(m) + a·m)/g^s)`. The main term is smaller than the [CLS] count by a
   factor `g^s`.
3. The error term needs two inputs:
   * a **power saving** `Σ_ℓ max_a |Ψ_ℓ(a)| ≪ g^{(2−c)s}`. It comes from an identity between
     consecutive digit factors in which `a` cancels, an idea that goes back to Col [Col] and also
     appears in [TP], [DMRSS] and [BhS];
   * an elementary **equidistribution of the archimedean phases** across the progressions. It
     rests on a count of `k`-th roots modulo prime powers.
4. Integers sharing a large factor with a power of `g` are counted separately. This only matters
   when `g` is not a prime power.

Choosing `g^t ≈ (g^{L/k})^{1/(4−c)}` and `s = t − 2` balances the terms and gives `γ < 1`.

## The Lean formalization

```lean
-- PalindromicPowers/MainTheorem.lean: stated with Mathlib's `Nat.digits` only
theorem PalindromicPowers.main_theorem_digits {g k : ℕ} (hg : 2 ≤ g) (hk : 2 ≤ k) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ ∃ C' : ℝ, ∀ L : ℕ, 1 ≤ L →
      ((((range (g ^ L)).filter (fun n => (Nat.digits g n).length = L ∧
            (Nat.digits g n).reverse = Nat.digits g n)).filter
            (fun n => ∃ x ≤ n, x ^ k = n)).card : ℝ) ≤
        C' * (((range (g ^ L)).filter (fun n => (Nat.digits g n).length = L ∧
            (Nat.digits g n).reverse = Nat.digits g n)).card : ℝ) ^ (γ / k)
```

* **Status:** complete. `lake build` succeeds, there is no `sorry`, `axiom`, `admit` or
  `native_decide`, and `#print axioms` reports only `propext`, `Classical.choice` and
  `Quot.sound` (see [`PalindromicPowers/Audit.lean`](PalindromicPowers/Audit.lean)).
* **One block, one declaration:** each of the 101 blocks of the HFF document has a Lean
  counterpart whose docstring starts with `[HFF n]`. Lemma `n` is proved from the statements of
  the blocks it cites. The Lean-friendly HFF document prints the Lean name under every block, and
  the map shows its status.
* **Size:** about 6,700 lines of Lean 4 on Mathlib (v4.34.0).

### Assumptions

The full trust boundary is in [`assumptions.md`](assumptions.md). In short:

* **No published result is assumed.** In particular, [CLS] is cited for comparison only: the
  improved bound is proved from scratch, and it implies theirs.
* **Known results.** The analytic textbook facts that the HFF document lists as prerequisites
  form an explicit hypothesis `KnownResults` ([`PalindromicPowers/Assumptions.lean`](PalindromicPowers/Assumptions.lean)):
  the mean value theorem, Taylor's theorem with Lagrange remainder, attainment of the maximum on a
  compact interval, `∫₁ˣ dy/y = log x`, `|e(y) − 1| = 2|sin πy|`, `|sin πy| ≥ 2‖y‖`,
  `|sin y| ≤ |y|`, Jordan's inequality `sin y ≥ 2y/π` on `[0, π/2]`, and two properties of the
  distance to the nearest integer `‖·‖`. The proof uses eight of these ten; Taylor's theorem and
  the logarithm integral are avoided by more elementary arguments. The algebraic prerequisites
  (division with remainder, congruences, gcd, `p`-adic valuations, the Chinese remainder theorem,
  the binomial theorem) are used directly from Lean and Mathlib.
* **All ten known results are proved from Mathlib** in
  [`PalindromicPowers/Discharge.lean`](PalindromicPowers/Discharge.lean). So
  `main_theorem_unconditional` and `main_theorem_digits` have no hypotheses beyond `g ≥ 2` and
  `k ≥ 2`. To trust them, a reader has to trust the Lean kernel, Mathlib, and that the statement
  above says what the theorem says.

### Building

Install Lean with [elan](https://github.com/leanprover/elan), then:

```
lake exe cache get                           # download the compiled Mathlib
lake build                                   # build the formalization
lake env lean PalindromicPowers/Audit.lean   # axioms, KnownResults usage, per-block status
```

| File | HFF blocks | Content |
|---|---|---|
| `Conventions.lean`, `Basic.lean` | 1 | notation `e`, `‖·‖` (`distZ`), `min(A, H/y)` (`minDiv`) and their basic API |
| `Assumptions.lean`, `Discharge.lean` | – | `KnownResults`, and its proof from Mathlib |
| `Digits.lean` | 2–8 | digits, reversal, geometric and harmonic sums |
| `ReversalTransform.lean` | 9–15 | `Ψ_ℓ(a)`, product formula, Fourier inversion |
| `PowerSaving.lean` | 16–26 | bad indices, digit strings, the power saving |
| `Tree.lean` | 28–36 | palindromes, nodes and the CLS tree |
| `Linearisation.lean` | 37–45 | the two digit blocks and the palindrome condition |
| `Majorant.lean` | 46–55 | Fejér majorant and the reduction to the error term |
| `Residues.lean`, `Frequencies.lean` | 56–59, 70–73 | sums over residues, data for one frequency |
| `Roots.lean` | 60–68 | `g`-parts, roots modulo prime powers, fibres |
| `Spacing.lean` | 74–86 | phase curve, spacing, bound for the error term |
| `LargeGPart.lean` | 87–89 | integers with a large `g`-part |
| `Final.lean`, `MainTheorem.lean` | 90–101 | parameters, bookkeeping, the main theorem |

## The HFF document and the map

The HFF document follows *Human Friendly Form* [HFF]. After an overview, the proof consists
only of definitions, lemmas and remarks, each lemma proved directly below its statement in fewer
than 300 visible characters, each block citing the earlier blocks it uses. This is the
**Lean-friendly version**: its statements are exactly those of the Lean formalization, and
[`hff/LEAN_CONVENTIONS.md`](hff/LEAN_CONVENTIONS.md) lists the notation and how the statements
were adapted. The source and build scripts are in [`hff/`](hff/).

The map shows the dependency graph like the map of a strategy game. Download the HTML file and
open it in a browser. It loads MathJax from a CDN for formulas.

## References

* **[CLS]** J. Cilleruelo, F. Luca and I. E. Shparlinski, *Power values of palindromes*,
  J. Comb. Number Theory **1** (2009), no. 2, 101–107.
* **[Col]** S. Col, *Palindromes dans les progressions arithmétiques*, Acta Arith. **137** (2009),
  no. 1, 1–41.
* **[TP]** A. Tuxanidy and D. Panario, *Infinitude of palindromic almost-prime numbers*,
  Int. Math. Res. Not. IMRN **2024**, no. 18, 12466–12503.
* **[DMRSS]** C. Dartyge, B. Martin, J. Rivat, I. E. Shparlinski and C. Swaenepoel,
  *Reversible primes*, J. Lond. Math. Soc. (2) **109** (2024), no. 3, e12883; arXiv:2309.11380.
* **[BhS]** G. Bhowmik and Y. Suzuki, *On Telhcirid's theorem on arithmetic progressions*,
  preprint, arXiv:2406.13334 (2024).
* **[HFF]** S. Iyer, *Checking AI-generated proofs: the Human Friendly Form*, note, October 2026.

The paper has the full bibliography.

## Authorship and use of AI

The mathematics and computations of the paper, the HFF write-up of the proof, the map and the
Lean formalization were produced by Claude, an AI model made by Anthropic, working as agents.
Siddharth Iyer directed the agents and did the bookkeeping. The Human Friendly Form format is
from [HFF]. The Lean proof is machine-checked. The paper's explicit constants rest on a
certified floating-point computation (see [`paper/scripts/README.md`](paper/scripts/README.md)),
which is not formally verified.

## License

MIT; see [`LICENSE`](LICENSE).

# Scripts for "Palindromic perfect powers"

Computation and verification scripts for the paper *Palindromic perfect powers: an improvement of the Cilleruelo–Luca–Shparlinski bound* (`palindromic_powers.tex`). Section, lemma and table numbers below refer to that paper.

**Requirements:** Python 3.9 or later and NumPy. No other packages are needed.

## Main tools

| Script | What it does | Paper | Typical run |
|---|---|---|---|
| `window_constants.py` | Certified upper bounds for S∞(s) by the window / transfer-matrix method. `table` reproduces Table 2. `run g w r [N]` computes one base. `check g s w r [N]` compares the bound of Lemma 5.6 with the exact max over a of \|Ψ_ℓ(a)\| for every ℓ. | §5.3–5.4, §7.1, Tables 1–2 | `table`: about 1 hour on one core. `run 2 10 5`: 15 s. `check 2 12 8 5 4096`: 10 s |
| `make_tables.py` | Turns the output of `window_constants.py table` into Table 1, Table 2 and the γ values of Corollary 1.3, with the paper's rounding conventions. | Tables 1–2, Cor. 1.3 | `python3 make_tables.py logs/table_run_A.txt logs/table_run_B.txt` |
| `window_independent.py` | A separately written implementation of the same bound, for cross-checking. It agrees with `window_constants.py` to 9 digits. | §5.4 | `python3 window_independent.py 2 5 8192 tri10` |
| `window_stress.py` | Random stress test of the window bound against brute force. The worst ratio must stay ≤ 1. | Lemma 5.6 | `python3 window_stress.py 1 60` |
| `sinf_exact.py` | Exact S∞(s) by FFT, with local growth exponents. These are the "observed" values of c. | Remark 5.8 | `python3 sinf_exact.py 2 8,9,10,11,12` |
| `pairing_constant.py` | Numerical constants from the pairing bound. These are not certified. | Prop. 5.4 | `python3 pairing_constant.py 2 2,4,6` |
| `literature_constants.py` | What the bounds of Dartyge–Martin–Rivat–Shparlinski–Swaenepoel (Lemma 2.6) and Bhowmik–Suzuki (Lemma 4.9) give for S∞, for comparison. | §1.4 | about 1 min |
| `check_orbit.py` | Exact checks of the identity and of the forced orbit. | Lemmas 5.1–5.2 | seconds |
| `check_nodes.py` | Exhaustive check of the nodes lemma (small g-part, fibres of b ↦ T_b). | Lemma 4.2 | about 1 min |
| `check_linearisation.py` | Randomised exact checks of node sizes and of both linearisations, then Lemma 3.3(c) on actual palindromic powers. | Lemmas 3.2–3.3 | a few minutes |
| `palpowers_count.py` | Enumerates the L-digit base-g palindromes that are k-th powers, via the CLS tree. | §1 | `python3 palpowers_count.py 10 2 24` |

## Notation used in the code

The code follows the paper's notation:

- f(θ) = \|sin πgθ\| / (g \|sin πθ\|).
- Ψ_ℓ(a) = Σ_m e(−(ℓ rev_s(m) + a m)/g^s), and S∞(s) = Σ_{0<\|ℓ\|<g^s} max_a \|Ψ_ℓ(a)\|.
- ℓ' = (g²−1)ℓ mod g^s.
- D_i = ℓ'/g^{i+2} mod 1.
- A window has length w, weights λ_j and K = Σλ_j. The parameter r is the number of digits that localise D_0, and ν = w + r − 2 (the code requires ν ≥ 2).
- A pattern σ = (σ_0, …, σ_{ν−1}) has index Σ σ_j g^{ν−1−j}, with σ_0 the most significant digit.
- v(σ) = 0.σ_{r−1}…σ_0 in base g.
- The matrix M is indexed by the (ν−1)-digit states and is built from the bounds Ubar(σ)^{1/K}.

The certification in `window_constants.py` works as follows:

- The cell bounds for f are computed in 40-digit decimal arithmetic, multiplied by 1 + 10⁻¹², and rounded up to double precision.
- The preimage covers are computed in exact integer arithmetic.
- The final Collatz–Wielandt ratio is multiplied by 1 + 10⁻¹².
- The script asserts that every Ubar(σ) exceeds 10⁻²⁸⁰, so underflow cannot occur.

## Computing c_g for a new base or new parameters

1. Choose a window length w and a number of digits r.
   - The cost grows like g^{w+r−1}·N.
   - Memory and time are fine up to g^{w+r−2} ≈ 3·10⁵ patterns.
   - Larger w helps most; r = 2 or 3 is usually enough.
2. Run `python3 window_constants.py run g w r` to compute ρ_CW and c_g = 1 − log_g ρ_CW. The default is N = 8192 with triangular weights λ_j = min(j+1, w−j).
3. Convert c_g into the exponent of Corollary 1.3:
   - If g is a prime power: γ = 1 − c/(4−c).
   - Otherwise: γ = 1 − c/((k−1)(4−c)+2), which requires c ≤ log 2/(2 log g).
   - The bound for the number of palindromic k-th powers is then ≪ (#P)^{γ/k}.

Increasing N tightens the bound slowly. For g = 2 with (w, r) = (14, 5), the Table 2 parameters:

| N | ρ |
|---|---|
| 256 | 1.8650 (5 s) |
| 2048 | 1.8373 (40 s) |
| 8192 | 1.8323 (4 min) |

## Logs (`logs/`)

| File | Contents |
|---|---|
| `table_run_A.txt`, `table_run_B.txt` | Output of the final `table` run. `sha256.txt` records the hash of the script that produced it, which is the script in this folder. |
| `table_values.txt` | Output of `make_tables.py` on those logs: the exact entries of Tables 1–2 and Corollary 1.3. |
| `check_runs.txt` | The seven brute-force checks quoted in §7.1. The largest ratio is 0.99995, for g = 16. |
| `remark_runs_g2.txt` | The base-2 runs quoted in Remark 5.8, with uniform and triangular weights for w = 10, 12, 14. They were made with the previous version of `window_constants.py`, which computed the cell bounds in double precision. The values agree with the current version to all printed digits where both were run. |

## Archive

The exploratory scripts from the earlier notes (Parts I–III) and from the referee passes are not
included in this repository. They are not maintained, and the scripts above are the ones the
paper relies on.

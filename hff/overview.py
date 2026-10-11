# Part I (overview) of the HFF document (Lean-friendly version), and the references.
# Cross references @D:xxx / @L:xxx / @T:xxx as in blocks.py.

TITLE = r"Palindromic perfect powers in Human Friendly Form"
SUBTITLE = (r"A power saving over the Cilleruelo--Luca--Shparlinski bound\\[0.3em]"
            r"\normalsize Lean-friendly version, matched block by block to the Lean formalization")

OVERVIEW_THEOREM = r"""
Fix a base $g\ge2$ and an exponent $k\ge2$, and consider the palindromes with $L$ digits in base $g$; there are
about $g^{L/2}$ of them. Cilleruelo, Luca and Shparlinski~\cite{CLS} proved that at most a constant times
$(\#\cP_L)^{1/k}$ of them are perfect $k$-th powers. We prove (@T:main) that the exponent $1/k$ can be replaced
by $\gamma/k$ for some $\gamma=\gamma(g,k)<1$, for every base and every exponent. This is a weak form of the
main result of the accompanying paper~\cite{Pal}, which gives explicit values such as $\gamma=0.9674$ for $g=2$;
those values need a certified computer calculation, while the argument here needs none.
"""

OVERVIEW_START = r"""
If $x^k$ is a palindrome with $L$ digits, its first $t$ digits are the reversal of its last $t$ digits. We sort
the candidates $x$ by their residue class $b$ modulo $g^t$, that is, by the last $t$ digits of $x$ (a
\emph{node}). The last $t$ digits of $x^k$ depend only on $b$, hence so do the first $t$ digits of $x^k$, and
these confine $x$ to a short interval. So the possible $x$ in a node form an arithmetic progression of length
about $Z=g^{L/k}g^{-2t}$ (@L:tree and @L:sizes), and counting all of them gives the bound of~\cite{CLS}.
"""

OVERVIEW_STRATEGY = r"""
We also use the next $s$ digits from both ends. Inside a node write $x=x_b+g^tz$. The digits of $x^k$ in
positions $t,\dots,t+s-1$ form an affine function of $z$ modulo $g^s$ (@L:low), and the digits in positions
$L-t-s,\dots,L-t-1$ form the integer part of a function of $z$ that lies within $1/g$ of an affine function
over the reals (@L:up and @L:arch). The palindrome condition says that the second block is the reversal of the
first (@L:local). We detect this with a Fej\'er-kernel majorant (@L:majlarge and @L:majcoef) and expand the
reversal map in additive characters modulo $g^s$ (@L:fourier). The coefficients of this expansion are the values
of the \emph{reversal transform} $\Psi_\ell(a)$, a discrete Fourier transform of digit reversal. Summing the
resulting geometric series in $z$ splits the count into a main term, smaller than the bound of~\cite{CLS} by
the factor $g^s$, and an error term (@L:red).
"""

OVERVIEW_ERROR = r"""
Two ingredients control the error term. First, a power saving for the sum over $\ell$ of
$\max_a|\Psi_\ell(a)|$ (@L:saving). The modulus of $\Psi_\ell(a)$ is a product of digit factors (@L:prod), and
consecutive factors satisfy an identity in which $a$ cancels (@L:ident). So whenever two neighbouring digits of
$(g^2-1)\ell\bmod g^s$ are not both $0$ or both $g-1$, one of two consecutive factors is bounded away from $1$,
whatever $a$ is (@L:badprod), and a count of digit strings (@L:strings) gives the saving. Arguments of this kind
go back to Col~\cite{Col} and appear in~\cite{TP}, \cite{DMRSS} and~\cite{BhS}. Second, after replacing
$|\Psi_\ell(a)|$ by its maximum over $a$, the sums over $a$ are taken node by node (@L:asum), and the averaging
over the nodes comes from the archimedean phases alone: they are close to the values of a smooth monotone
function of the first $t$ digits, these values are well spaced (@L:gaps and @L:space), and few nodes share the
same first digits (@L:fibre). The last point rests on an elementary count of $k$-th roots modulo prime powers
(@L:binom--@L:rootsn) and on the $g$-part of a node, its largest divisor composed of primes dividing $g$
(@L:rigid).
"""

OVERVIEW_PARAMS = r"""
Integers $x$ that share a large factor with a power of $g$ are counted separately by a direct argument
(@L:largeg); this matters only when $g$ is not a prime power. Finally we choose $t$ with $g^{(4-c)t}$ about
$g^{L/k}$, $s=t-2$, and a threshold $D=g^{\eta L/k}$ for the $g$-part (@D:par), and the bookkeeping
(blocks @D:par--@L:final) gives the theorem (@T:main).
"""

OVERVIEW_ROUTINE = r"""
Routine: digits, reversal and harmonic sums (blocks @D:conv--@L:harm); the elementary properties of the
reversal transform (blocks @D:psi--@L:gap); the tree of nodes (blocks @D:pal--@L:nonempty); the linearisation
(blocks @D:phase--@L:local); the Fej\'er majorant (blocks @L:fejer--@L:red); the sums over residues
(blocks @L:mult--@L:asum); the count of roots (blocks @D:gpart--@L:rootsn); the reduction to the quantities
$\Phi_b$ (blocks @D:count--@L:sumd); and the final bookkeeping with the deduction of the theorem (blocks @D:par--@T:main). Delicate: the power
saving (blocks @L:ident--@L:saving); the rigidity of $g$-parts and the fibre bound (@L:rigid and @L:fibre); the
replacement of the phases $\delta_b$ by values of a smooth function, and the spacing argument
(blocks @D:curve--@L:E); and the large $g$-part (blocks @L:mdiv--@L:largeg). The key lemmas are @L:saving,
@L:red, @L:fibre, @L:E, @L:largeg and @L:final.
"""

OVERVIEW_PREREQ = r"""
Division with remainder, congruences, greatest common divisors, $p$-adic valuations and the Chinese remainder
theorem; the binomial theorem; the mean value theorem, Taylor's theorem with the Lagrange remainder, the fact
that a continuous function on a compact interval attains its maximum, and $\int_1^x\frac{dy}y=\log x$; the
identity $|e(y)-1|=2|\sin\pi y|$ and the inequalities $|\sin\pi y|\ge2\|y\|$, $|\sin y|\le|y|$ and
$\sin y\ge2y/\pi$ for $0\le y\le\pi/2$; and the properties $\|x-y\|\le\|x\|+\|y\|$ and $\|nx\|\le|n|\,\|x\|$
($n\in\Z$) of the distance to the nearest integer. No result from the literature is imported, and no computer
calculation is used. In the Lean formalization the algebraic prerequisites are taken from Lean and Mathlib,
and the analytic ones are the fields of the structure \texttt{KnownResults} in
\texttt{PalindromicPowers/\allowbreak Assumptions.lean}, documented in
\texttt{palindromic\_powers\_lean/\allowbreak assumptions.md} and proved from Mathlib in
\texttt{PalindromicPowers/\allowbreak Discharge.lean}; no published result is assumed.
"""

OVERVIEW_ABOUT = r"""
This document follows the Human Friendly Form of~\cite{HFF}. After the mark $\maltese$ the proof consists only
of definitions, lemmas and remarks, numbered in one sequence; every lemma is proved directly below its
statement in fewer than $300$ visible characters (the length is shown in grey at the end of each proof); every
block cites, by number, each earlier block whose notation or results it uses; and remarks carry no logical
weight. This is the \emph{Lean-friendly version}: its statements are those of the Lean formalization
\texttt{palindromic\_powers\_lean}, and every definition, lemma and theorem names its Lean counterpart in a grey
line below the statement (the Lean declarations of block $n$ have docstrings beginning \texttt{[HFF n]}). The
correspondence follows fixed conventions: the digit $n_i$ is \texttt{digit g n i}; $\min(A,H/y)$ is
\texttt{minDiv A H y}, which is $A$ for $y=0$ (the convention $H/0=\infty$); $\|x\|$ is \texttt{distZ x}; and all
constants are explicit: ``$A\ll B$ for $L$ large'' becomes $\exists\,C_1,L_0\ \forall L\ge L_0:\ A\le C_1B$,
and $\varepsilon_*$, $u_*$, $c$, $C$, $t'$ and the parameters of @D:par are given by formulas. A table of
notation is in \texttt{hff/LEAN\_CONVENTIONS.md}. The dependency graph can be explored in the accompanying map,
\texttt{palindromic\_powers\_hff\_lean\_map.html}. The document was written by Claude (Anthropic), from the
accompanying paper~\cite{Pal}, and revised to match the Lean statements.
"""

OVERVIEW = [
    ('The theorem', OVERVIEW_THEOREM),
    ('The starting point', OVERVIEW_START),
    ('The strategy', OVERVIEW_STRATEGY),
    ('The error term', OVERVIEW_ERROR),
    ('Large $g$-parts and parameters', OVERVIEW_PARAMS),
    ('Routine and delicate steps', OVERVIEW_ROUTINE),
    ('Prerequisites', OVERVIEW_PREREQ),
    ('About this document', OVERVIEW_ABOUT),
]

REFERENCES = [
    ('BhS', r"G.~Bhowmik and Y.~Suzuki, \emph{On Telhcirid's theorem on arithmetic progressions}, preprint, arXiv:2406.13334 (2024)."),
    ('CLS', r"J.~Cilleruelo, F.~Luca and I.~E. Shparlinski, \emph{Power values of palindromes}, J. Comb. Number Theory \textbf{1} (2009), no.~2, 101--107."),
    ('Col', r"S.~Col, \emph{Palindromes dans les progressions arithm\'etiques}, Acta Arith. \textbf{137} (2009), no.~1, 1--41."),
    ('DMRSS', r"C.~Dartyge, B.~Martin, J.~Rivat, I.~E. Shparlinski and C.~Swaenepoel, \emph{Reversible primes}, J. Lond. Math. Soc. (2) \textbf{109} (2024), no.~3, e12883."),
    ('HFF', r"S.~Iyer, \emph{Checking AI-generated proofs: the Human Friendly Form}, note, October 2026."),
    ('Pal', r"\emph{Palindromic perfect powers: an improvement of the Cilleruelo--Luca--Shparlinski bound}, manuscript, October 2026 (\texttt{palindromic\_powers.pdf})."),
    ('TP', r"A.~Tuxanidy and D.~Panario, \emph{Infinitude of palindromic almost-prime numbers}, Int. Math. Res. Not. IMRN \textbf{2024}, no.~18, 12466--12503."),
]

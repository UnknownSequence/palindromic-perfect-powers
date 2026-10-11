# Source of the HFF document "Palindromic perfect powers" (gamma < 1 version),
# Lean-friendly revision: the statements are those of the Lean formalization in
# ../PalindromicPowers/*.lean, and every block names its Lean declarations (lean=...).
# Each block: kind in {def, lem, thm, rem}, label, header, statement, proof, lean.
# Cross references are written @D:xxx, @L:xxx, @T:xxx and are turned into
# "Definition N", "Lemma N", "Theorem N" (with hyperlinks) by build.py.
# Every block cites, by number, each earlier block whose notation or content it uses.
# lean= lists the Lean declarations whose docstrings begin with **[HFF n]** (n = block
# number), in the order of the Lean files; remarks have none.

BLOCKS = []


def B(kind, label, header, statement, proof=None, lean=None):
    if isinstance(lean, str):
        lean = lean.split()
    BLOCKS.append(dict(kind=kind, label=label, header=header,
                       statement=statement.strip(), proof=(proof or '').strip(),
                       lean=list(lean or [])))


# ---------------------------------------------------------------- basics
B('def', 'D:conv', r'Conventions', r"""
Throughout, $g\ge2$ and $k\ge2$ are fixed integers. We write $e(x)=e^{2\pi ix}$, $\|x\|$ for the distance
from $x\in\R$ to the nearest integer, $\log$ for the natural logarithm, and $n\bmod q\in\{0,\dots,q-1\}$ for
the remainder of $n\in\Z$ on division by an integer $q\ge1$. For real $A$, $H$, $y$, $\min(A,H/y)$ has its
usual meaning if $y\ne0$, and $\min(A,H/0):=A$ (the convention $H/0=\infty$). ``For $L$ large'' means for
all $L\ge L_0$, where $L_0$ depends only on $g$ and $k$; and ``$A\ll B$ for $L$ large'' means: there are
$C_1$ and $L_0$, depending only on $g$ and $k$, with $|A|\le C_1B$ for all $L\ge L_0$.
""", lean='e distZ minDiv')

B('lem', 'L:digits', r'Digits', r"""
For $j\ge0$, the map $(n_0,\dots,n_{j-1})\mapsto\sum_{i<j}n_ig^i$ is a bijection from $\{0,\dots,g-1\}^j$
onto $\{0,\dots,g^j-1\}$ (@D:conv).
""", r"""
The image lies in $[0,(g-1)\sum_{i<j}g^i]=[0,g^j-1]$, and both sets have $g^j$ elements, so it suffices to
show injectivity. If $\sum_in_ig^i=\sum_in'_ig^i$, reducing modulo $g$ gives $n_0=n'_0$; subtract, divide by
$g$, and use induction on $j$.
""", lean='digits_bijection')

B('def', 'D:digits', r'Digits and reversal', r"""
For integers $n,i\ge0$, the $i$-th \emph{digit} of $n$ is $n_i:=\lfloor n/g^i\rfloor\bmod g\in\{0,\dots,g-1\}$.
For $j\ge0$ put $\rev_j(n):=\sum_{i<j}n_ig^{j-1-i}$ (@D:conv).
""", lean='digit rev')

B('lem', 'L:window', r'Blocks of digits', r"""
Let $n\ge0$ have digits $n_r$, and let $0\le i\le i'$ (@D:digits). Then $n\bmod g^i=\sum_{r<i}n_rg^r$ and
$\lfloor n/g^i\rfloor\bmod g^{i'-i}=\sum_{i\le r<i'}n_rg^{r-i}$ (@D:conv). Moreover, if $j\ge0$ and
$d_r\in\{0,\dots,g-1\}$ for $r<j$, then the digits of $\sum_{r<j}d_rg^r$ are $d_0,\dots,d_{j-1}$ (in
positions $0,\dots,j-1$).
""", r"""
The first claim follows by induction on $i$ from $n\bmod g^{i+1}=n\bmod g^i+g^in_i$. The second is the first
for $\lfloor n/g^i\rfloor$, whose $r$-th digit is $n_{i+r}$, as $\lfloor\lfloor n/g^i\rfloor/g^r\rfloor=
\lfloor n/g^{i+r}\rfloor$. For the third, $m:=\sum_{r<j}d_rg^r<g^j$ (@L:digits), so $m=m\bmod g^j=\sum_{r<j}m_rg^r$;
now use the uniqueness in @L:digits.
""", lean='digit_window')

B('lem', 'L:inv', r'Reversal is an involution', r"""
Let $j\ge0$. For every $n\ge0$, $\rev_j(n)<g^j$ and the digits of $\rev_j(n)$ in positions $i<j$ are
$n_{j-1-i}$; and $\rev_j(\rev_j(n))=n$ if $n<g^j$ (@D:conv and @D:digits).
""", r"""
As $\rev_j(n)=\sum_{i<j}n_{j-1-i}g^i$ with all $n_{j-1-i}\le g-1$, $\rev_j(n)<g^j$ by @L:digits, and its
digits are the $n_{j-1-i}$ by @L:window. So $\rev_j(\rev_j(n))=\sum_{i<j}n_ig^i=n\bmod g^j$ (@L:window), which is
$n$ if $n<g^j$.
""", lean='rev_involution')

B('lem', 'L:geom', r'Geometric sums', r"""
For $\theta\in\R$ and an integer $n\ge1$,
$\bigl|\sum_{z=0}^{n-1}e(z\theta)\bigr|\le\min\bigl(n,\frac1{2\|\theta\|}\bigr)$ (@D:conv).
""", r"""
Each term has modulus $1$. If $\theta\notin\Z$, the sum is $(e(n\theta)-1)/(e(\theta)-1)$, of modulus at most
$2/|e(\theta)-1|=1/|\sin\pi\theta|\le1/(2\|\theta\|)$, since $|\sin\pi\theta|\ge2\|\theta\|$.
""", lean='geom_sum_le')

B('lem', 'L:harm1', r'Harmonic numbers', r"""
For every integer $n\ge1$, $\sum_{j=1}^n\frac1j\le1+\log n$ (@D:conv).
""", r"""
For $j\ge2$, $\frac1j\le\int_{j-1}^j\frac{dx}x$, as $\frac1x\ge\frac1j$ on $[j-1,j]$. Summing over
$2\le j\le n$ gives $\sum_{j=1}^n\frac1j\le1+\int_1^n\frac{dx}x=1+\log n$.
""", lean='harmonic_le')

B('lem', 'L:harm', r'An odd harmonic sum', r"""
For every integer $R\ge1$, $\sum_{0<|j|\le R/2}\frac1{2|j|-1}\le2+\log R$ (@D:conv).
""", r"""
For $R=1$ the sum is empty. For $R\ge2$ it is $2\sum_{1\le j\le R/2}\frac1{2j-1}\le
2+2\int_1^{R/2}\frac{dx}{2x-1}=2+\log(R-1)$, since $\frac1{2j-1}\le\int_{j-1}^{j}\frac{dx}{2x-1}$ for $j\ge2$.
""", lean='odd_harmonic_le')

# ---------------------------------------------------------------- the reversal transform
B('def', 'D:psi', r'Reversal transform', r"""
Let $s\ge1$ and $Q:=g^s$. For $\ell,a\in\Z$ put
$\Psi_\ell(a):=\sum_{m=0}^{Q-1}e\bigl(-(\ell\rev_s(m)+am)/Q\bigr)$, $M(\ell):=\max_{0\le a<Q}|\Psi_\ell(a)|$ and
$S(s):=\sum_{0<|\ell|<Q}M(\ell)$. For $\theta\in\R$ let
$f(\theta):=\frac1g\bigl|\sum_{d=0}^{g-1}e(d\theta)\bigr|$, and for $0\le i<s$ let
$\theta_i=\theta_i(\ell,a):=(\ell g^{s-1-i}+ag^i)/Q$ (@D:conv and @D:digits).
""", lean='Psi Mmax Ssum fdig theta')

B('lem', 'L:per', r'Periodicity', r"""
$\Psi_\ell(a)$ depends only on $\ell\bmod Q$ and $a\bmod Q$ (@D:conv, @D:digits and @D:psi).
""", r"""
Changing $\ell$ or $a$ by a multiple of $Q$ changes each argument $-(\ell\rev_s(m)+am)/Q$ by an integer, as
$\rev_s(m)$ and $m$ are integers, and $e$ has period $1$.
""", lean='Psi_periodic')

B('lem', 'L:prod', r'Product formula', r"""
For all $\ell,a\in\Z$: $|\Psi_\ell(a)|=Q\prod_{i=0}^{s-1}f(\theta_i(\ell,a))$ (@D:conv and @D:psi).
""", r"""
For $0\le m<Q$, $m=\sum_{i<s}m_ig^i$ (@D:digits and @L:window), so
$\ell\rev_s(m)+am=\sum_im_i(\ell g^{s-1-i}+ag^i)=Q\sum_im_i\theta_i$; and $(m_i)_{i<s}$ runs over
$\{0,\dots,g-1\}^s$ as $m$ does (@L:digits and @L:window). So $\Psi_\ell(a)=\prod_{i<s}\sum_{d<g}e(-d\theta_i)$;
each factor is the conjugate of $\sum_{d<g}e(d\theta_i)$, of modulus $gf(\theta_i)$.
""", lean='norm_Psi_eq')

B('lem', 'L:fourier', r'Fourier inversion', r"""
For $\ell\in\Z$ and $0\le n<Q$ (@D:conv, @D:digits and @D:psi):
\[e(-\ell\rev_s(n)/Q)=Q^{-1}\sum_{a=0}^{Q-1}\Psi_\ell(a)e(an/Q).\]
""", r"""
By @D:psi the right side is $Q^{-1}\sum_{m<Q}e(-\ell\rev_s(m)/Q)\sum_{a<Q}e(a(n-m)/Q)$. The inner sum is $Q$ if
$m=n$, and $0$ otherwise, since it sums the powers of the $Q$-th root of unity $e((n-m)/Q)\ne1$.
""", lean='fourier_inversion')

B('lem', 'L:zero', r'Zero frequency', r"""
If $Q\nmid\ell$, then $\Psi_\ell(0)=0$ (@D:conv, @D:digits and @D:psi).
""", r"""
By @L:inv, $n=\rev_s(m)$ runs over $\{0,\dots,Q-1\}$ as $m$ does. So $\Psi_\ell(0)=\sum_{n<Q}\omega^n$ with
$\omega:=e(-\ell/Q)$, and $\omega\ne1=\omega^Q$; the sum is $(\omega^Q-1)/(\omega-1)=0$.
""", lean='Psi_zero')

B('lem', 'L:f', r'Shape of $f$', r"""
$f$ is continuous and $1$-periodic, $0\le f\le1$, and $f(\theta)<1$ for $\theta\notin\Z$ (@D:conv and @D:psi).
""", r"""
Continuity and periodicity are clear, and $f\le1$ by the triangle inequality. If $f(\theta)=1$, equality holds
there, so the unit vectors $e(d\theta)$, $d<g$, coincide; as $g\ge2$, $e(\theta)=e(0)=1$, i.e.\ $\theta\in\Z$.
""", lean='fdig_shape')

B('lem', 'L:gap', r'Uniform gap', r"""
Let $\varepsilon_*:=1/(g^2(g+1))$ and
$u_*:=\bigl(\sup_{\varepsilon_*\le\theta\le1-\varepsilon_*}f(\theta)\bigr)^{1/2}$. Then $0\le u_*<1$, and
$f(\theta)\le u_*^2$ whenever $\|\theta\|\ge\varepsilon_*$ (@D:conv and @D:psi).
""", r"""
As $g\ge2$, $0<\varepsilon_*<1/2$. By @L:f, $f$ is continuous, $\ge0$, and $<1$ on the compact set
$[\varepsilon_*,1-\varepsilon_*]$, which contains no integer; so the supremum is a maximum, and
$0\le u_*^2<1$. If $\|\theta\|\ge\varepsilon_*$ then $\theta-\lfloor\theta\rfloor\in[\varepsilon_*,1-\varepsilon_*]$,
and $f$ has period $1$.
""", lean='epsStar uStar uStar_spec')

B('lem', 'L:ident', r'Consecutive arguments', r"""
For $\ell,a\in\Z$ and $0\le i\le s-2$: $g\theta_i-\theta_{i+1}=(g^2-1)\ell/g^{i+2}$, where
$\theta_i=\theta_i(\ell,a)$ (@D:psi).
""", r"""
By @D:psi, $g\theta_i=\ell/g^{i}+a/g^{s-1-i}$ and $\theta_{i+1}=\ell/g^{i+2}+a/g^{s-1-i}$. Subtracting gives
$\ell/g^i-\ell/g^{i+2}=(g^2-1)\ell/g^{i+2}$.
""", lean='theta_consecutive')

B('lem', 'L:far2', r'One of two is far', r"""
For $0\le i\le s-2$: $\max(\|\theta_i\|,\|\theta_{i+1}\|)\ge\|(g^2-1)\ell/g^{i+2}\|/(g+1)$ (@D:conv and @D:psi).
""", r"""
For $x,y\in\R$ and integers $n\ge1$, $\|x-y\|\le\|x\|+\|y\|$ and $\|nx\|\le n\|x\|$. By @L:ident,
$\|(g^2-1)\ell/g^{i+2}\|=\|g\theta_i-\theta_{i+1}\|\le g\|\theta_i\|+\|\theta_{i+1}\|$, which is at most
$(g+1)\max(\|\theta_i\|,\|\theta_{i+1}\|)$.
""", lean='one_of_two_far')

B('def', 'D:bad', r'Bad indices', r"""
For $\ell\in\Z$ let $\ell':=(g^2-1)\ell\bmod Q$. For integers $n\ge1$ and $r\ge0$ with digits $r_i$, an index
$0\le i\le n-2$ is \emph{bad} for $r$ if $(r_{i+1},r_i)$ is neither $(0,0)$ nor $(g-1,g-1)$; let $\beta_n(r)$
be the number of these bad indices, and $b(\ell):=\beta_s(\ell')$ (@D:conv, @D:digits and @D:psi).
""", lean='twist IsBad badCount bBad')

B('lem', 'L:twist', r'Twisting is bijective', r"""
The map $\ell\mapsto\ell'$ is a bijection of $\{0,\dots,Q-1\}$, and $\ell'$ (hence $b(\ell)$) depends only on
$\ell\bmod Q$ (@D:conv, @D:psi and @D:bad).
""", r"""
A prime factor of $Q=g^s$ divides $g^2$, hence not $g^2-1$; so $\gcd(g^2-1,Q)=1$, and multiplication by $g^2-1$
is invertible modulo $Q$. Also $\ell'$, and hence $b(\ell)$, depends only on $\ell\bmod Q$.
""", lean='twist_bijective')

B('lem', 'L:frac', r'Fractional parts', r"""
For $0\le i\le s-2$: $(g^2-1)\ell/g^{i+2}\equiv v_i+w_i\pmod1$, where $v_i:=\ell'_{i+1}/g+\ell'_i/g^2$ and
$0\le w_i<1/g^2$ (@D:conv, @D:digits, @D:psi and @D:bad).
""", r"""
As $i+2\le s$ and $(g^2-1)\ell\equiv\ell'\pmod{g^s}$, the number $((g^2-1)\ell-\ell')/g^{i+2}$ is an integer, and
$\ell'/g^{i+2}\equiv(\ell'\bmod g^{i+2})/g^{i+2}=\sum_{j\le i+1}\ell'_jg^{j-i-2}\pmod1$ (@L:window). This is
$v_i+w_i$ with $w_i:=\sum_{j<i}\ell'_jg^{j-i-2}<g^{-2}$.
""", lean='frac_parts')

B('lem', 'L:badfar', r'Bad indices are far', r"""
If $0\le i\le s-2$ is bad for $\ell'$, then $\|(g^2-1)\ell/g^{i+2}\|\ge1/g^2$ (@D:conv and @D:bad).
""", r"""
By @L:frac it suffices that $1/g^2\le v_i+w_i\le1-1/g^2$. Now $v_i$ is a multiple of $1/g^2$ in
$[0,1-1/g^2]$; it is $0$ only if $\ell'_{i+1}=\ell'_i=0$, and $1-1/g^2$ only if both are $g-1$. So
$1/g^2\le v_i\le1-2/g^2$, while $0\le w_i<1/g^2$.
""", lean='bad_far')

B('lem', 'L:badprod', r'Bad pair product', r"""
If $0\le i\le s-2$ is bad for $\ell'$ (@D:bad), then $f(\theta_i)f(\theta_{i+1})\le u_*^2$ for every $a\in\Z$
(@D:psi and @L:gap).
""", r"""
By @L:far2 and @L:badfar, $\max(\|\theta_i\|,\|\theta_{i+1}\|)\ge1/(g^2(g+1))=\varepsilon_*$ (@D:conv). By @L:gap
that factor is at most $u_*^2$, and the other is at most $1$ by @L:f.
""", lean='bad_pair_prod')

B('lem', 'L:sup', r'Sup bound', r"""
For every $\ell\in\Z$: $M(\ell)\le Q\,u_*^{b(\ell)}$ (@D:psi, @D:bad and @L:gap).
""", r"""
Fix $a$ and let $\varphi_i:=f(\theta_i)\in[0,1]$ (@L:f). As $\varphi\le\varphi^{1/2}$ on $[0,1]$,
$\prod_{i<s}\varphi_i\le\prod_{i\le s-2}(\varphi_i\varphi_{i+1})^{1/2}$, the right side being
$(\varphi_0\varphi_{s-1})^{1/2}\prod_{0<i<s-1}\varphi_i$ if $s\ge2$. Use @L:badprod for bad $i$, then @L:prod.
""", lean='Mmax_le')

B('lem', 'L:strings', r'Weighted digit strings', r"""
Let $0\le u\le1$ and $n\ge1$. Then $\sum_{0\le r<g^n}u^{\beta_n(r)}\le g(1+(g-1)u)^{n-1}$ (@D:digits and
@D:bad).
""", r"""
By @L:digits and @L:window, $r\mapsto(r_i)_{i<n}$ maps $[0,g^n)$ bijectively onto $\{0,\dots,g-1\}^n$, and
$\beta_n(r)=:\beta(d)$ depends only on $d=(r_i)_{i<n}$. Induct on $n$; for $n=1$ the sum is $g$. Appending
$d_n$ to $d$ raises $\beta$ by $1$ unless $d_n=d_{n-1}\in\{0,g-1\}$, so
$\sum_{d_n}u^{\beta(d,d_n)}\le u^{\beta(d)}(1+(g-1)u)$, as $gu\le1+(g-1)u$.
""", lean='weighted_strings')

B('lem', 'L:twsum', r'Sum over frequencies', r"""
Let $\rho:=1+(g-1)u_*$. Then $\rho<g$, and $S(s)\le2gQ\rho^{s-1}$ (@D:psi and @L:gap).
""", r"""
$\rho<g$ as $u_*<1$. By @L:per, each residue mod $Q$ is $\ell\bmod Q$ for at most two $\ell$ with $0<|\ell|<Q$,
so $S(s)\le2\sum_{0\le\ell<Q}M(\ell)$ (@D:conv). By @L:sup, @L:twist and @D:bad this is at most
$2Q\sum_{0\le r<Q}u_*^{\beta_s(r)}$, and @L:strings ($u=u_*$, $n=s$) applies.
""", lean='rho Ssum_le')

B('lem', 'L:saving', r'Power saving', r"""
Let $\rho$ be as in @L:twsum, $c:=\min\bigl(1-\log_g\rho,\frac{\log2}{2\log g}\bigr)$ and $C:=2g$. Then
$0<c\le\frac{\log2}{2\log g}$, $C\ge1$, and $S(s)\le Cg^{(2-c)s}$ for all $s\ge1$ (@D:conv and @D:psi).
""", r"""
As $\rho<g$ (@L:twsum), $c>0$. Also $1\le\rho\le g^{1-c}$, as $u_*\ge0$ (@L:gap), so @L:twsum gives
$S(s)\le2gQ\rho^{s-1}\le2g\cdot g^s\cdot g^{(1-c)s}=Cg^{(2-c)s}$; and $C=2g\ge1$.
""", lean='cSave CSave power_saving')

B('rem', 'R:saving', r'The size of $c$', r"""
Digit reversal is used in an essential way only in @L:prod and @L:ident, in which $a$ cancels. The constant
$c$ of @L:saving is tiny; the accompanying paper~\cite{Pal} bounds $S(s)$ much more precisely, with a certified
computation over windows of consecutive digits. Here only $c>0$ matters.
""")

# ---------------------------------------------------------------- palindromes and the tree
B('def', 'D:pal', r'Palindromes', r"""
For $L\ge1$ let $\cP_L$ be the set of integers $g^{L-1}\le n<g^L$ whose digits $n_i$ ($i<L$) satisfy
$n_i=n_{L-1-i}$ for all $i<L$. Let $\cQ_L:=\{x\in\N:x^k\in\cP_L\}$ and $X:=g^{L/k}$ (@D:conv and @D:digits).
""", lean='palSet powSet Xr')

B('lem', 'L:npal', r'Many palindromes', r"""
For $L\ge1$: $\#\cP_L\ge g^{L/2-1}$, and hence $X\le(g\#\cP_L)^{2/k}$ (@D:conv and @D:pal).
""", r"""
Choose digits $n_i$ for $(L-1)/2\le i<L$ with $n_{L-1}\ne0$, and put $n_i:=n_{L-1-i}$ for smaller $i$. Then
$n:=\sum_in_ig^i\in[g^{L-1},g^L)$ has these digits (@L:window), so it lies in $\cP_L$, and distinct choices give
distinct $n$ (@L:digits). So $\#\cP_L\ge(g-1)g^{\lceil L/2\rceil-1}\ge g^{L/2-1}$, and $X=(g^{L/2})^{2/k}$.
""", lean='many_palindromes')

B('lem', 'L:first', r'First digits of palindromes', r"""
Let $n\in\cP_L$ and $1\le t\le L$. Then $g\nmid n$ and $\lfloor n/g^{L-t}\rfloor=\rev_t(n\bmod g^t)$
(@D:conv, @D:digits and @D:pal).
""", r"""
Let $n_r$ be the digits of $n$. By @L:window, $n\bmod g^t=\sum_{r<t}n_rg^r$ has digits $n_r$, $r<t$, and
$\lfloor n/g^{L-t}\rfloor=\sum_{r<t}n_{L-t+r}g^r$ as $n<g^L$. As $n_{L-t+r}=n_{t-1-r}$, the latter is
$\rev_t(n\bmod g^t)$. For $t=1$: $n\bmod g=\lfloor n/g^{L-1}\rfloor\ge1$, as $n\ge g^{L-1}$.
""", lean='first_digits')

B('def', 'D:node', r'Nodes', r"""
Let $1\le t\le L$. A \emph{node} (of level $t$) is an integer $0\le b<g^t$ with $g\nmid b^k$. For a node $b$
put $T_b:=\rev_t(b^k\bmod g^t)$, $y_0:=T_bg^{L-t}$, $y_1:=y_0+g^{L-t}$, $I_b:=[y_0^{1/k},y_1^{1/k})$ (so an
integer $x\ge0$ lies in $I_b$ iff $y_0\le x^k<y_1$) and $|I_b|:=y_1^{1/k}-y_0^{1/k}$; let $Z_b$ be the number
of integers $x\in I_b$ with $x\equiv b\pmod{g^t}$, and if $Z_b\ge1$ let $x_b$ be the least of them. Let
$Z(t):=Xg^{-2t}$ (@D:conv, @D:digits and @D:pal).
""", lean='IsNode Tb y0 y1 InI Ilen nodeElems Zb xb Zt')

B('lem', 'L:lead', r'Leading digit', r"""
For a node $b$: $g^{t-1}\le T_b<g^t$ (@D:node).
""", r"""
Let $n:=b^k\bmod g^t$, with digits $n_i$ (@D:digits). By @L:window, $n_0=n\bmod g=b^k\bmod g\ne0$, as
$g\nmid b^k$ (@D:conv). So $T_b=\rev_t(n)\ge n_0g^{t-1}\ge g^{t-1}$, and $T_b<g^t$ by @L:inv.
""", lean='leading_digit')

B('lem', 'L:tree', r'The tree', r"""
Let $1\le t\le L$ and $x\in\cQ_L$. Then $b:=x\bmod g^t$ is a node, $x\in I_b$, and $x=x_b+g^tz$ for an integer
$0\le z<Z_b$ (@D:conv, @D:pal and @D:node).
""", r"""
By @L:first with $n=x^k$, $g\nmid x^k$, so $g\nmid b^k$ as $b\equiv x\pmod g$. Also $b^k\bmod g^t=x^k\bmod g^t$,
so @L:first gives $\lfloor x^k/g^{L-t}\rfloor=T_b$, i.e.\ $x\in I_b$. As $x\equiv b\pmod{g^t}$, $x$ is one of the
$Z_b$ integers $x_b+g^tz$, $0\le z<Z_b$, in $I_b$.
""", lean='tree')

B('lem', 'L:mvt', r'Interval endpoints', r"""
For a node $b$: $g^{L-1}\le y_0<y_1\le\min(g^L,2y_0)$, and $|I_b|=g^{L-t}/(k\xi^{1-1/k})$ for some
$\xi\in[y_0,y_1]$ (@D:node).
""", r"""
By @L:lead, $g^{t-1}\le T_b$ and $T_b+1\le g^t$, which gives the inequalities, as $y_1/y_0=1+1/T_b\le2$. The
formula for $|I_b|=y_1^{1/k}-y_0^{1/k}$ is the mean value theorem for $y\mapsto y^{1/k}$.
""", lean='interval_endpoints')

B('lem', 'L:sizes', r'Node sizes', r"""
For a node $b$: $Z(t)/k\le|I_b|g^{-t}\le gZ(t)/k$ and $Z(t)/k-1\le Z_b\le gZ(t)/k+1$ (@D:pal and @D:node).
""", r"""
By @L:mvt, $g^{(L-1)(1-1/k)}\le\xi^{1-1/k}\le g^{L(1-1/k)}$, so $|I_b|$ lies between $g^{L/k-t}/k=g^tZ(t)/k$ and
$g^{L/k-t+1}/k$. An interval of length $\lambda$ contains between $\lambda g^{-t}-1$ and $\lambda g^{-t}+1$
integers $\equiv b\pmod{g^t}$.
""", lean='node_sizes')

B('lem', 'L:nonempty', r'Nodes are not empty', r"""
Let $1\le t\le L$ with $Z(t)\ge2k$. Then every node $b$ of level $t$ has $1\le Z_b\le2gZ(t)/k$ (@D:node).
""", r"""
By @L:sizes, $Z_b\ge Z(t)/k-1\ge1$ and $Z_b\le gZ(t)/k+1\le2gZ(t)/k$, as $gZ(t)/k\ge1$.
""", lean='nodes_nonempty')

# ---------------------------------------------------------------- linearisation
B('def', 'D:phase', r'Phases', r"""
Fix integers $t,s$ with $1\le s\le t-2$ and $2(t+s)\le L$; let $Q:=g^s$ (as in @D:psi), $Z:=Z(t)$ and
$\Lambda:=1+\log(1+6g^t)$. For a node $b$ of level $t$ put $\beta_b:=kb^{k-1}\bmod Q$ and
$d_b:=\gcd(\beta_b,Q)$. If moreover $Z_b\ge1$, then for $\ell,a\in\Z$ and an integer $z\ge0$ put
$\alpha_b:=\lfloor x_b^k/g^t\rfloor\bmod Q$, $\delta_b:=kx_b^{k-1}g^{2t+s-L}$,
$\theta_{b,\ell,a}:=(\ell\delta_b+a\beta_b)/Q$ and $n_b(z):=(\alpha_b+\beta_bz)\bmod Q$ (@D:conv and @D:node).
""", lean='Admissible LambdaT alphaB betaB dB deltaB thetaB nB')

B('def', 'D:arch', r'Archimedean phases', r"""
In the setting of @D:phase, for real $z\ge0$ put $\phi_b(z):=(x_b+g^tz)^k/g^{L-t-s}-T_bg^s$ and
$\lambda_b(z):=\phi_b(0)+\delta_bz$; and for real $T>0$ put $\delta(T):=k(Tg^{L-t})^{1-1/k}g^{2t+s-L}$
(@D:node).
""", lean='phiB lambdaB deltaT')

B('lem', 'L:delta', r'Formula for $\delta(T)$', r"""
For $T>0$: $\delta(T)=\frac{kQ}Z(T/g^t)^{1-1/k}$; hence $kQ/(gZ)\le\delta(T)\le kQ/Z$ for
$g^{t-1}\le T\le g^t$ (@D:pal, @D:node, @D:phase and @D:arch).
""", r"""
As $Tg^{L-t}=(T/g^t)g^L$, $g^{L(1-1/k)}=g^L/X$ and $g^{2t}/X=1/Z$,
\[\delta(T)=k\Bigl(\frac T{g^t}\Bigr)^{1-1/k}\frac{g^L}X\,g^{2t+s-L}=\frac{kQ}Z\Bigl(\frac T{g^t}\Bigr)^{1-1/k}.\]
Finally, if $T/g^t\in[1/g,1]$ then $(T/g^t)^{1-1/k}\in[1/g,1]$.
""", lean='deltaT_formula')

B('lem', 'L:deltab', r'$\delta_b$ is near $\delta(T_b)$', r"""
For a node $b$ of level $t$ with $Z_b\ge1$: $\delta(T_b)\le\delta_b\le(1+g^{1-t})\delta(T_b)$ (@D:node, @D:phase
and @D:arch).
""", r"""
With $y_0,y_1$ as in @D:node, $\delta_b/\delta(T_b)=(x_b/y_0^{1/k})^{k-1}$ and $x_b\in I_b=[y_0^{1/k},y_1^{1/k})$.
So the ratio lies in $[1,(y_1/y_0)^{1-1/k}]\subset[1,1+1/T_b]\subset[1,1+g^{1-t}]$, by @L:lead.
""", lean='deltaB_near')

B('lem', 'L:low', r'Lower block', r"""
Let $b$ be a node of level $t$ with $Z_b\ge1$, and $x=x_b+g^tz$ with an integer $z\ge0$. Then
$\lfloor x^k/g^t\rfloor\bmod Q=n_b(z)$ (@D:conv, @D:node and @D:phase).
""", r"""
By the binomial theorem $x^k=x_b^k+kx_b^{k-1}g^tz+g^{2t}N$ with $N\in\Z$, so
$\lfloor x^k/g^t\rfloor=\lfloor x_b^k/g^t\rfloor+kx_b^{k-1}z+g^tN$. Reduce modulo $Q=g^s$, using $s\le t$ and
$x_b\equiv b\pmod{g^t}$.
""", lean='lower_block')

B('lem', 'L:up', r'Upper block', r"""
Let $b$ be a node of level $t$ with $Z_b\ge1$, and $x=x_b+g^tz\in I_b$ with an integer $z\ge0$. Then
$\lfloor x^k/g^{L-t-s}\rfloor\bmod Q=\lfloor\phi_b(z)\rfloor$ (@D:conv, @D:node, @D:phase and @D:arch).
""", r"""
As $x\in I_b$, $T_bg^{L-t}\le x^k<(T_b+1)g^{L-t}$, so $\lfloor x^k/g^{L-t}\rfloor=T_b$. Hence
$\lfloor x^k/g^{L-t-s}\rfloor\bmod g^s=\lfloor x^k/g^{L-t-s}\rfloor-g^s\lfloor x^k/g^{L-t}\rfloor
=\lfloor x^k/g^{L-t-s}-T_bg^s\rfloor=\lfloor\phi_b(z)\rfloor$.
""", lean='upper_block')

B('lem', 'L:taylor', r'Taylor bound', r"""
Let $b$ be a node of level $t$ with $Z_b\ge1$, $z\ge0$ real and $x_b+g^tz\in I_b$. Then
$0\le\phi_b(z)-\lambda_b(z)\le\frac{k(k-1)}2y_1^{1-2/k}|I_b|^2g^{t+s-L}$, with $y_1$ as in @D:node (@D:conv,
@D:node, @D:phase and @D:arch).
""", r"""
$\phi_b$ is convex with $\phi_b'(0)=\delta_b$, so $\phi_b\ge\lambda_b$. By Taylor,
$\phi_b(z)-\lambda_b(z)=\phi_b''(\zeta)z^2/2$ with $\zeta\in[0,z]$, and
$\phi_b''(\zeta)z^2=k(k-1)(x_b+g^t\zeta)^{k-2}(g^tz)^2g^{t+s-L}$, where $x_b+g^t\zeta\le y_1^{1/k}$ and
$g^tz\le|I_b|$.
""", lean='taylor_bound')

B('lem', 'L:arch', r'Archimedean linearisation', r"""
In the setting of @L:taylor, $0\le\phi_b(z)-\lambda_b(z)\le1/g$ (@D:node, @D:phase and @D:arch).
""", r"""
By @L:mvt, $|I_b|\le g^{L-t}/(ky_0^{1-1/k})$, $y_1\le2y_0$ and $y_0\ge g^{L-1}$. So the bound of @L:taylor is
at most $\frac{k-1}{2k}(y_1/y_0)^{1-2/k}y_0^{-1}g^{L-t+s}\le\frac{k-1}kg^{s+1-t}\le\frac1g$, as $s\le t-2$.
""", lean='arch_linearisation')

B('lem', 'L:local', r'The palindrome condition', r"""
Let $b$ be a node of level $t$ with $Z_b\ge1$, and $x=x_b+g^tz\in\cQ_L\cap I_b$ with an integer $z\ge0$. Then
$\lambda_b(z)-\rev_s(n_b(z))\in[-1/g,1)$ (@D:digits, @D:pal, @D:node, @D:phase and @D:arch).
""", r"""
Let $N_r$ be the digits of $x^k$. By @L:low, @L:up and @L:window, $n_b(z)=\sum_{i<s}N_{t+i}g^i$ and
$\lfloor\phi_b(z)\rfloor=\sum_{i<s}N_{L-t-s+i}g^i$, which is $\rev_s(n_b(z))$ as $N_r=N_{L-1-r}$. Now use
$0\le\phi_b(z)-\lfloor\phi_b(z)\rfloor<1$ and @L:arch.
""", lean='palindrome_condition')

# ---------------------------------------------------------------- detection
B('lem', 'L:fejer', r'Fej\'er identity', r"""
For an integer $K\ge1$ and $x\in\R$:
$\sum_{|j|<K}(1-|j|/K)e(jx)=K^{-1}\bigl|\sum_{i=0}^{K-1}e(ix)\bigr|^2$ (@D:conv).
""", r"""
The right side is $K^{-1}\sum_{i,i'<K}e((i-i')x)$, and for $|j|<K$ there are exactly $K-|j|$ pairs $(i,i')$
with $0\le i,i'<K$ and $i-i'=j$.
""", lean='fejer_identity')

B('lem', 'L:fejerlow', r'Fej\'er lower bound', r"""
If $K\ge1$ is an integer and $|x|\le1/(2K)$, then (@D:conv)
\[K^{-1}\Bigl|\sum_{i<K}e(ix)\Bigr|^2\ge4K/\pi^2.\]
""", r"""
For $x=0$ the left side is $K$. Otherwise
\[\Bigl|\sum_{i<K}e(ix)\Bigr|=\frac{|\sin\pi Kx|}{|\sin\pi x|}\ge\frac{2K|x|}{\pi|x|}=\frac{2K}\pi,\]
as $\sin y\ge2y/\pi$ for $0\le y\le\pi/2$ and $|\sin y|\le|y|$.
""", lean='fejer_lower')

B('lem', 'L:K', r'Size of $K$', r"""
For $Q$ as in @D:psi, $K:=\lfloor2Q/3\rfloor$ satisfies $Q/3\le K\le2Q/3<Q$ and $K\ge1$.
""", r"""
$K\le2Q/3$ by definition, and $Q=g^s\ge2$ (@D:conv). If $Q=2$ then $K=1\ge2/3$, and if $Q\ge3$ then
$K>2Q/3-1\ge Q/3\ge1$.
""", lean='Kq Kq_size')

B('def', 'D:maj', r'Majorant', r"""
With $Q$ and $K$ as in @L:K, let
$F(y):=\frac{\pi^2}{4K^2}\bigl|\sum_{i=0}^{K-1}e(i(y-1/4)/Q)\bigr|^2$ for $y\in\R$, and
$\hat F_j:=\frac{\pi^2}{4K}\bigl(1-\frac{|j|}K\bigr)e\bigl(-\frac j{4Q}\bigr)$ for integers $|j|<K$ (@D:conv and
@D:psi).
""", lean='Fmaj Fhat')

B('lem', 'L:majlarge', r'The majorant is large', r"""
$F\ge0$, and $F(y)\ge1$ for $y\in[-1/2,1]$ (@D:conv, @D:psi and @D:maj).
""", r"""
$F\ge0$ is clear. For $y\in[-1/2,1]$, $x:=(y-1/4)/Q$ satisfies $|x|\le3/(4Q)\le1/(2K)$ by @L:K, so by
@L:fejerlow, $F(y)=\frac{\pi^2}{4K}\cdot K^{-1}\bigl|\sum_{i<K}e(ix)\bigr|^2\ge\frac{\pi^2}{4K}\cdot\frac{4K}{\pi^2}=1$.
""", lean='maj_large')

B('lem', 'L:majcoef', r'Majorant coefficients', r"""
$F(y)=\sum_{|j|<K}\hat F_je(jy/Q)$ for all $y\in\R$, and $|\hat F_j|\le8/Q$ for $|j|<K$ (@D:conv, @D:psi and
@D:maj).
""", r"""
By @L:fejer with $x=(y-1/4)/Q$,
$F(y)=\frac{\pi^2}{4K}\sum_{|j|<K}(1-|j|/K)e(-j/(4Q))e(jy/Q)=\sum_{|j|<K}\hat F_je(jy/Q)$. And
$|\hat F_j|\le\pi^2/(4K)\le3\pi^2/(4Q)<8/Q$ by @L:K.
""", lean='maj_coeffs')

B('lem', 'L:innode', r'Counting in a node', r"""
For a node $b$ of level $t$ with $Z_b\ge1$:
$\#\{x\in\cQ_L:x\equiv b\pmod{g^t}\}\le\sum_{z=0}^{Z_b-1}F(\lambda_b(z)-\rev_s(n_b(z)))$ (@D:digits, @D:pal,
@D:node, @D:phase, @D:arch and @D:maj).
""", r"""
By @L:tree each such $x$ is $x_b+g^tz$ for some $0\le z<Z_b$, and lies in $I_b$; distinct $x$ give distinct
$z$. For these $z$ the summand is $\ge1$ by @L:local and @L:majlarge, as $[-1/g,1)\subset[-1/2,1]$ (@D:conv),
and all summands are $\ge0$.
""", lean='count_in_node')

B('lem', 'L:twisted', r'Twisted sums', r"""
For a node $b$ of level $t$ with $Z_b\ge1$ and $0<|j|<Q$ (@D:conv, @D:digits, @D:psi, @D:node, @D:phase and
@D:arch):
\[\Bigl|\sum_{z<Z_b}e\Bigl(\frac{j(\lambda_b(z)-\rev_s(n_b(z)))}Q\Bigr)\Bigr|\le
\frac1Q\sum_{0<a<Q}|\Psi_j(a)|\min\Bigl(Z_b,\frac1{2\|\theta_{b,j,a}\|}\Bigr).\]
""", r"""
By @L:fourier with $n=n_b(z)\equiv\alpha_b+\beta_bz$, and as $\lambda_b(z)=\lambda_b(0)+\delta_bz$, the sum is
$Q^{-1}\sum_{a<Q}\Psi_j(a)e(\omega_a)\sum_{z<Z_b}e(z\theta_{b,j,a})$ with real $\omega_a$. Apply @L:geom; the
term $a=0$ vanishes by @L:zero.
""", lean='twisted_sum')

B('def', 'D:err', r'Error term', r"""
For a set $\cB$ of nodes $b$ of level $t$ with $Z_b\ge1$ let
\[E(\cB):=\sum_{b\in\cB}\sum_{0<|j|<Q}\sum_{0<a<Q}|\Psi_j(a)|\min\Bigl(Z_b,\frac1{2\|\theta_{b,j,a}\|}\Bigr)\]
(@D:conv, @D:psi, @D:node and @D:phase).
""", lean='Eerr')

B('lem', 'L:red', r'Reduction', r"""
For $\cB$ as in @D:err:
$\#\{x\in\cQ_L:x\bmod g^t\in\cB\}\le\frac8Q\sum_{b\in\cB}Z_b+\frac8{Q^2}E(\cB)$ (@D:conv, @D:pal and @D:node).
""", r"""
For $b\in\cB$, by @L:innode and @L:majcoef the count is at most
$\sum_{|j|<K}|\hat F_j|\bigl|\sum_{z<Z_b}e(j(\lambda_b(z)-\rev_s(n_b(z)))/Q)\bigr|$ (@D:digits, @D:phase,
@D:arch and @D:maj). The term $j=0$ is at most $8Z_b/Q$; bound the others by @L:twisted, as $K<Q$ (@L:K). Sum over $\cB$.
""", lean='reduction')

# ---------------------------------------------------------------- sums over a
B('lem', 'L:mult', r'Multiples', r"""
Let $Q\ge1$ be any integer, $\beta\in\Z$ and $d:=\gcd(\beta,Q)$. As $a$ runs over $0,\dots,Q-1$,
$a\beta\bmod Q$ runs over the multiples $rd$, $0\le r<Q/d$, each exactly $d$ times; equivalently,
$\sum_{0\le a<Q}\varphi(a\beta\bmod Q)=d\sum_{0\le r<Q/d}\varphi(rd)$ for every function $\varphi$ (@D:conv).
""", r"""
$a\mapsto a\beta\bmod Q$ is a homomorphism of $\Z/Q\Z$ whose image is generated by $\beta$, hence by
$\gcd(\beta,Q)=d$; so the image is $d\Z/Q\Z$, of size $Q/d$, and each value is taken $Q/(Q/d)=d$ times. The
second form follows by grouping the $a$ by the value $rd$.
""", lean='multiples_sum')

B('lem', 'L:dist', r'Distances', r"""
Let $R\ge1$ and $j$ be integers with $0<|j|\le R/2$, and let $|w_0|\le1/2$. Then
$\|(j+w_0)/R\|\ge(2|j|-1)/(2R)$ (@D:conv).
""", r"""
For $n\in\Z$: if $n=0$ then $|j+w_0-nR|\ge|j|-1/2$; if $n\ne0$ then $|j+w_0-nR|\ge R-|j|-1/2\ge|j|-1/2$.
Divide by $R$.
""", lean='dist_lower')

B('lem', 'L:ressum', r'Sum over residues', r"""
Let $R\ge1$ be an integer, $w\in\R$ and $A\ge1$. Then
$\sum_{r=0}^{R-1}\min\bigl(A,\frac1{2\|(w+r)/R\|}\bigr)\le\min\bigl(A,\frac R{2\|w\|}\bigr)+R(2+\log R)$ (@D:conv).
""", r"""
Write $w=n_0+w_0$ with $n_0\in\Z$ and $|w_0|=\|w\|\le1/2$. As $r$ runs mod $R$, $j\equiv n_0+r$ runs over the
integers in $(-R/2,R/2]$, and $\|(w+r)/R\|=\|(j+w_0)/R\|$. The term $j=0$ is $\min(A,R/(2\|w\|))$; bound the
others by @L:dist and @L:harm.
""", lean='residue_sum')

B('lem', 'L:asum', r'Sum over $a$', r"""
Let $y\in\R$, $\beta\in\Z$, $d:=\gcd(\beta,Q)$ and $A\ge1$. Then (@D:conv and @D:psi)
\[\sum_{a=0}^{Q-1}\min\Bigl(A,\frac1{2\|(y+a\beta)/Q\|}\Bigr)\le\min\Bigl(dA,\frac Q{2\|y/d\|}\Bigr)+Q(2+\log Q).\]
""", r"""
By @L:mult the sum is $d\sum_{r<Q/d}\min(A,\frac1{2\|(y+rd)/Q\|})$, and $(y+rd)/Q=(y/d+r)/(Q/d)$. By
@L:ressum with $R=Q/d$ and $w=y/d$, it is at most $d\min(A,\frac{Q/d}{2\|y/d\|})+d\frac Qd(2+\log\frac Qd)$.
""", lean='a_sum')

# ---------------------------------------------------------------- g-parts and fibres
B('def', 'D:gpart', r'$g$-parts', r"""
For a prime $p$ let $v_p$ be the $p$-adic valuation. For an integer $n\ge1$ let
$m_g(n):=\prod_{p\mid g}p^{v_p(n)}$, the product over the primes $p$ dividing $g$. Let $\omega(g)$ be the number
of primes dividing $g$, $P$ the largest of them, and for real $D\ge1$ let $\tau(D)$ be the number of integers
$1\le m\le D$ all of whose prime factors divide $g$ (@D:conv).
""", lean='mg omegaG Pmax tauG')

B('lem', 'L:tau', r'Few $g$-smooth numbers', r"""
$\tau$ is non-decreasing, and $\tau(D)\le(1+\log_2D)^{\omega(g)}$ for $D\ge1$ (@D:gpart).
""", r"""
Monotonicity is clear. Each $m$ counted is $\prod_{p\mid g}p^{e_p}$ with $p^{e_p}\le D$, so
$0\le e_p\le\log_2D$: at most $1+\log_2D$ choices for each of the $\omega(g)$ exponents.
""", lean='tauG_bound')

B('lem', 'L:gcd', r'Common factor of $\beta_b$', r"""
If $b$ is a node of level $t$ and $m:=m_g(b)$, then $d_b$ divides $Q$ and $km^{k-1}$ (@D:node, @D:phase and
@D:gpart).
""", r"""
As $g\nmid b^k$, $b\ne0$; write $b=mu$ with $\gcd(u,g)=1$. Then $\beta_b\equiv km^{k-1}u^{k-1}\pmod Q$, so
$d_b=\gcd(km^{k-1}u^{k-1},Q)=\gcd(km^{k-1},Q)$, as $u$ is coprime to $Q$.
""", lean='dB_dvd')

B('lem', 'L:binom', r'Binomial congruence', r"""
Let $p$ be a prime, $j\ge2$ and $u,w\in\Z$. Then
$(u+p^jw)^k\equiv u^k+ku^{k-1}p^jw\pmod{p^{v_p(k)+j+1}}$ (@D:gpart).
""", r"""
The other terms are $\binom kiu^{k-i}p^{ij}w^i$, $2\le i\le k$. From $i\binom ki=k\binom{k-1}{i-1}$ and
$v_p(i)\le i-1$ we get $v_p\binom ki\ge v_p(k)-i+1$, and $ij-i+1\ge j+1$, as $(i-1)(j-1)\ge1$.
""", lean='binomial_congr')

B('lem', 'L:close', r'Close roots agree', r"""
Let $p$ be a prime, $N>v_p(k)$, and $u,u'\in\Z$ with $p\nmid u$, $u^k\equiv u'^k\pmod{p^N}$ and
$u\equiv u'\pmod{p^2}$. Then $u\equiv u'\pmod{p^{N-v_p(k)}}$ (@D:gpart).
""", r"""
If not, let $j$ be maximal with $p^j\mid u'-u$; then $2\le j<N-v_p(k)$ and $u'=u+p^jw$ with $p\nmid w$. By
@L:binom, $u'^k-u^k\equiv ku^{k-1}p^jw\pmod{p^{v_p(k)+j+1}}$, whose valuation is $v_p(k)+j<N$, contradicting
$p^N\mid u'^k-u^k$.
""", lean='close_roots_agree')

B('lem', 'L:rootsp', r'Few roots modulo $p^N$', r"""
Let $p$ be a prime, $N\ge1$ and $w\in\Z$ with $p\nmid w$. Then $u^k\equiv w\pmod{p^N}$ has at most
$p^{v_p(k)+2}$ solutions $u\bmod p^N$ (@D:conv and @D:gpart).
""", r"""
If $N\le v_p(k)+2$ this is clear. Otherwise every solution has $p\nmid u$, and by @L:close, solutions in the
same class mod $p^2$ agree mod $p^{N-v_p(k)}$. So each of the $p^2$ classes contains at most $p^{v_p(k)}$
solutions mod $p^N$.
""", lean='roots_mod_prime_pow')

B('lem', 'L:rootsn', r'Few roots modulo $n$', r"""
Let $n\ge1$ have all its prime factors dividing $g$, and $\gcd(w,n)=1$. Then $u^k\equiv w\pmod n$ has at most
$kg^2$ solutions $u\bmod n$ (@D:conv and @D:gpart).
""", r"""
By the Chinese remainder theorem the number of solutions is the product over $p\mid n$ of the numbers of
solutions mod $p^{v_p(n)}$, each at most $p^{v_p(k)+2}$ by @L:rootsp. Finally
$\prod_{p\mid g}p^{v_p(k)}\le k$ and $\prod_{p\mid g}p^2\le g^2$.
""", lean='roots_mod_n')

B('lem', 'L:rigid', r'Rigid $g$-part', r"""
Let $D\ge1$ with $D^k<2^t$, and let $b,b'$ be nodes of level $t$ with $T_b=T_{b'}$ and $m:=m_g(b)\le D$
(@D:node and @D:gpart). Then $m^k\mid g^t$ and $m_g(b')=m$.
""", r"""
Let $p\mid g$ and $v:=v_p(b)$. Then $p^{kv}\le m^k<2^t\le p^{v_p(g)t}$, so $kv<v_p(g)t$; hence $m^k\mid g^t$.
By @L:inv, $b^k\equiv b'^k\pmod{g^t}$, so $b'^k\equiv b^k\pmod{p^{v_p(g)t}}$, $v_p(b'^k)=kv$ and $v_p(b')=v$.
""", lean='rigid_gpart')

B('lem', 'L:fibre', r'Fibres', r"""
Let $D\ge1$ with $D^k<2^t$, and $b$ a node of level $t$ with $m:=m_g(b)\le D$. Then at most $kg^2m^{k-1}$
nodes $b'$ of level $t$ satisfy $T_{b'}=T_b$ (@D:node and @D:gpart).
""", r"""
By @L:rigid, $m^k\mid g^t$, $b=mu$, $b'=mu'$ with $u,u'$ coprime to $g$. By @L:inv, $b'^k\equiv b^k\pmod{g^t}$,
so $u'^k\equiv u^k\pmod n$, $n:=g^t/m^k$. By @L:rootsn, $u'$ lies in at most $kg^2$ classes mod $n$, each with
$m^{k-1}$ lifts mod $g^t/m$, which fix $b'$.
""", lean='fibre_bound')

# ---------------------------------------------------------------- the archimedean count
B('rem', 'R:arch', r'The archimedean count', r"""
The next blocks bound the sums over $a$ and over the nodes. The $g$-adic phases $a\beta_b$ are summed for each
node separately (@L:asum). The averaging over nodes comes from the archimedean phases $\ell\delta_b$: they are
close to the values of the monotone function $\ell\delta(T)$ at $T=T_b$, these values are well spaced, and few
nodes share the same $T_b$ (@L:fibre).
""")

B('def', 'D:count', r'Data for one frequency', r"""
In the setting of @D:phase, let $0<|\ell|<Q$ and $D\ge1$ with $D^k<2^t$, and suppose $Z\ge2k$, so that every
node $b$ of level $t$ has $Z_b\ge1$ (@L:nonempty). Let $\cB$ be a set of nodes $b$ of level $t$ with
$m_g(b)\le D$ (@D:node and @D:gpart). Let $Z_+:=gZ/k+1$, and for $b\in\cB$ let $y_b:=\ell\delta_b/d_b$,
$\Phi_b:=\min\bigl(d_bZ_+,\frac Q{2\|y_b\|}\bigr)$ and
$W_\ell:=\sum_{b\in\cB}\sum_{0<a<Q}\min\bigl(Z_b,\frac1{2\|\theta_{b,\ell,a}\|}\bigr)$ (@D:conv).
""", lean='FreqSetting Zplus yB PhiB Wl')

B('lem', 'L:wphi', r'From $W_\ell$ to $\Phi_b$', r"""
$W_\ell\le\sum_{b\in\cB}\Phi_b+g^tQ(2+\log Q)$ (@D:conv, @D:phase and @D:count).
""", r"""
By @L:nonempty and @L:sizes, $1\le Z_b\le Z_+$. For each $b\in\cB$ apply @L:asum with $y=\ell\delta_b$,
$\beta=\beta_b$ and $A=Z_b$, after adding the term $a=0$, and use $\min(d_bZ_b,\cdot)\le\min(d_bZ_+,\cdot)$.
Finally $\#\cB\le g^t$ (@D:node).
""", lean='W_to_Phi')

B('lem', 'L:small', r'Small phases', r"""
If $b\in\cB$ and $|\ell|\delta_b\le d_b/2$, then $\Phi_b\le gZd_b/(2k|\ell|)$ (@D:conv, @D:phase and @D:count).
""", r"""
Then $|y_b|\le1/2$, so $\|y_b\|=|\ell|\delta_b/d_b$ and $\Phi_b\le Qd_b/(2|\ell|\delta_b)$. By @L:deltab,
@L:delta and @L:lead, $\delta_b\ge\delta(T_b)\ge kQ/(gZ)$ (@D:node and @D:arch).
""", lean='small_phases')

B('lem', 'L:sumd', r'Sum of $d_b$', r"""
$\sum_{b\in\cB}d_b\le k\tau(D)D^{k-2}g^t$ (@D:conv, @D:phase, @D:gpart and @D:count).
""", r"""
For $b\in\cB$ let $m:=m_g(b)\le D$. By @L:gcd, $d_b\le km^{k-1}$, and $m\mid g^t$ by @L:rigid (with $b'=b$).
Exactly $g^t/m$ integers in $[0,g^t)$ are divisible by $m$, and $m$ takes at most $\tau(D)$ values; so the sum
is at most $\tau(D)\max_m(g^t/m)km^{k-1}\le k\tau(D)D^{k-2}g^t$, as $k\ge2$.
""", lean='sum_dB')

B('def', 'D:curve', r'Phase curve', r"""
In the setting of @D:count, for an integer $d\ge1$ and real $T>0$ let $h_d(T):=\ell\delta(T)/d$; let $\cT_d$ be
the set of integers $T\in[g^{t-1},g^t)$ with $|h_d(T)|\ge1/3$, and put $\mu:=(1-1/k)|h_d(g^t)|/g^t$ and
$\Delta:=|h_d(g^t)-h_d(g^{t-1})|$ (both depend on $d$) (@D:conv and @D:arch).
""", lean='hd Tset muD DeltaD')

B('lem', 'L:pert', r'Perturbation', r"""
If $b\in\cB$ and $|\ell|\delta_b>d_b/2$, then $T_b\in\cT_{d_b}$ and
$|y_b-h_{d_b}(T_b)|\le\varepsilon_b:=kg^{s-1}/(d_bZ)$ (@D:conv, @D:node, @D:phase, @D:arch, @D:count and
@D:curve).
""", r"""
Let $h:=h_{d_b}(T_b)$. By @L:deltab, @L:delta and @L:lead, $|y_b-h|\le|\ell|g^{1-t}\delta(T_b)/d_b\le
g^sg^{1-t}kQ/(Zd_b)\le\varepsilon_b$, as $s\le t-2$. Also $|h|\ge|\ell|\delta_b/((1+g^{1-t})d_b)>1/(2+2g^{1-t})\ge1/3$,
as $t\ge3$; and $g^{t-1}\le T_b<g^t$.
""", lean='epsB perturbation')

B('lem', 'L:repl', r'Replacement', r"""
In the setting of @L:pert, $\Phi_b\le5\min\bigl(d_bZ_+,\frac Q{2\|h_{d_b}(T_b)\|}\bigr)$ (@D:conv, @D:node,
@D:phase, @D:count and @D:curve).
""", r"""
Let $h:=h_{d_b}(T_b)$. If $\|h\|\ge2\varepsilon_b$ then $\|y_b\|\ge\|h\|/2$, which gives the factor $2$.
Otherwise $\frac Q{2\|h\|}>\frac Q{4\varepsilon_b}=\frac{gd_bZ}{4k}$ and $d_bZ_+\ge\frac{gd_bZ}k$, so the right
side is at least $\frac{5gd_bZ}{4k}\ge d_bZ_+\ge\Phi_b$, as $gZ\ge4k$.
""", lean='replacement')

B('lem', 'L:shape', r'Shape of $h_d$', r"""
On $[g^{t-1},g^t]$, $|h_d|$ is non-decreasing, $h_d'(T)=(1-1/k)h_d(T)/T$, $|h_d'|$ is non-increasing, and
$|h_d'(T)|\le g\mu$, where $\mu=|h_d'(g^t)|$ (@D:conv, @D:phase and @D:curve).
""", r"""
By @L:delta, $h_d(T)=\frac{\ell kQ}{dZ}(T/g^t)^{1-1/k}$. This gives the first two claims, and $|h_d'(T)|$ is a
constant times $T^{-1/k}$, so it is non-increasing, $|h_d'(g^t)|=(1-\frac1k)|h_d(g^t)|/g^t=\mu$, and
$|h_d'(T)|/\mu=(g^t/T)^{1/k}\le g$.
""", lean='hd_shape')

B('lem', 'L:gaps', r'Gaps', r"""
Suppose $\cT_d\ne\emptyset$. Then $\mu\ge1/(6g^t)$, and $|h_d(T')-h_d(T)|\ge\mu$ for distinct $T,T'\in\cT_d$
(@D:conv and @D:curve).
""", r"""
By @L:shape, $|h_d(g^t)|\ge|h_d(T)|\ge1/3$ for $T\in\cT_d$, so $\mu=(1-\frac1k)|h_d(g^t)|/g^t\ge1/(6g^t)$. Also
$|h_d'|\ge\mu$ on $[g^{t-1},g^t]$, and $|T'-T|\ge1$; apply the mean value theorem.
""", lean='gaps')

B('lem', 'L:range', r'Range', r"""
If $\cT_d\ne\emptyset$, then $h_d(T)$ lies between $h_d(g^{t-1})$ and $h_d(g^t)$ for every $T\in\cT_d$; moreover
$\Delta\le g^{t+1}\mu$ and $\Delta\le kg^{2s}/(dZ)$ (@D:phase, @D:count and @D:curve).
""", r"""
By @L:delta, $h_d(T)=\frac{\ell kQ}{dZ}(T/g^t)^{1-1/k}$ is monotone and of constant sign on $[g^{t-1},g^t]$. This
gives the first claim, and $\Delta\le|h_d(g^t)|\le|\ell|kQ/(dZ)\le kg^{2s}/(dZ)$, as $|\ell|<Q=g^s$. By @L:shape
and the mean value theorem, $\Delta\le g^t\cdot g\mu$.
""", lean='range_bound')

B('lem', 'L:space1', r'Spacing near one integer', r"""
Let $\mu>0$, $m\ge1$, $A,H>0$ be real and $n\in\Z$. Let finitely many reals $y_i\in(n-\frac12,n+\frac12]$ with
integer weights $w_i\ge0$ be such that every half-open interval $[a,a+\mu)$ carries total weight
$\sum_{y_i\in[a,a+\mu)}w_i\le m$. Then
$\sum_iw_i\min(A,\frac H{|y_i-n|})\le2mA+2m\frac H\mu(1+\log(1+\frac1\mu))$ (@D:conv).
""", r"""
Let $J:=\lfloor1/(2\mu)\rfloor+1$. The intervals $[n+j\mu,n+(j+1)\mu)$ and $[n-(j+1)\mu,n-j\mu)$, $0\le j<J$,
cover $(n-\frac12,n+\frac12]$, each carries weight at most $m$, and the $y_i$ in them have $|y_i-n|\ge j\mu$.
Use $\sum_{1\le j<J}\frac1j\le1+\log(1+\frac1\mu)$ (@L:harm1).
""", lean='spacing_one')

B('lem', 'L:space', r'Spacing sum', r"""
Let $\mu>0$, $m\ge1$, $A,H>0$, $\Delta\ge0$ and $a_0$ be real. Let finitely many reals
$y_i\in[a_0,a_0+\Delta]$ with integer weights $w_i\ge0$ be such that every half-open interval of length $\mu$
carries total weight at most $m$. Then
$\sum_iw_i\min(A,\frac H{\|y_i\|})\le m(\Delta+2)\bigl(2A+2\frac H\mu(1+\log(1+\frac1\mu))\bigr)$ (@D:conv).
""", r"""
Each $y_i$ lies in $(n-\frac12,n+\frac12]$ for a unique $n\in\Z$, and then $\|y_i\|=|y_i-n|$. These $n$ lie in
$[a_0-\frac12,a_0+\Delta+\frac12)$, so at most $\Delta+2$ of them occur. Apply @L:space1 for each $n$.
""", lean='spacing_sum')

B('lem', 'L:countT', r'Count over $T$', r"""
Let $d\ge1$ be an integer with $\cT_d\ne\emptyset$, let $\kappa\ge1$ be real, and let integers $0\le N_T\le\kappa$
be given for $T\in\cT_d$. Then (@D:conv, @D:phase, @D:count and @D:curve)
\[\sum_{T\in\cT_d}N_T\min\Bigl(dZ_+,\frac Q{2\|h_d(T)\|}\Bigr)\le\kappa(\Delta+2)\Bigl(2dZ_++\frac Q\mu\Lambda\Bigr).\]
""", r"""
Apply @L:space to the numbers $h_d(T)$, $T\in\cT_d$, with weights $N_T$, $m=\kappa$, $A=dZ_+$, $H=Q/2$, and the
interval between $h_d(g^{t-1})$ and $h_d(g^t)$ (@L:range): by @L:gaps, $\mu>0$, each half-open interval of
length $\mu$ contains $h_d(T)$ for at most one $T$, and $1+\log(1+1/\mu)\le\Lambda$.
""", lean='count_over_T')

B('lem', 'L:countT2', r'Count over $T$, explicitly', r"""
If moreover $d\le kD^{k-1}$, the bound in @L:countT is at most
$\kappa(4g^{2s+1}+8gD^{k-1}Z+7g^{t+1}Q\Lambda)$ (@D:conv, @D:phase, @D:count and @D:curve).
""", r"""
By @L:range, $dZ_+\Delta\le\frac{2gZ}k\cdot\frac{kg^{2s}}Z=2g^{2s+1}$, as $Z_+\le2gZ/k$ (since $Z\ge2k$). Next
$4dZ_+\le8gD^{k-1}Z$. Finally $(\Delta+2)/\mu\le g^{t+1}+2/\mu\le g^{t+1}+12g^t\le7g^{t+1}$ by @L:gaps.
""", lean='count_over_T_explicit')

B('lem', 'L:large', r'Large phases', r"""
Let $\cB_2:=\{b\in\cB:|\ell|\delta_b>d_b/2\}$. Then (@D:conv, @D:node, @D:phase, @D:gpart and @D:count)
\[\sum_{b\in\cB_2}\Phi_b\le5\tau(kD^{k-1})kg^2D^{k-1}(4g^{2s+1}+8gD^{k-1}Z+7g^{t+1}Q\Lambda).\]
""", r"""
By @L:pert and @L:repl, $\Phi_b\le5\min(d_bZ_+,\frac Q{2\|h_{d_b}(T_b)\|})$, $T_b\in\cT_{d_b}$ (@D:curve). By
@L:gcd, $d_b\mid Q$ and $d_b\le kD^{k-1}$: at most $\tau(kD^{k-1})$ values. For each value $d$ use @L:countT2
with $\kappa:=kg^2D^{k-1}$ and $N_T:=\#\{b\in\cB_2:d_b=d,T_b=T\}\le\kappa$ (@L:fibre).
""", lean='large_phases')

B('lem', 'L:W', r'Bound for $W_\ell$', r"""
In the setting of @D:count (with @D:conv, @D:phase and @D:gpart),
\[\begin{gathered}W_\ell\le g^tQ(2+\log Q)+\frac{g\tau(D)D^{k-2}Zg^t}{2|\ell|}\\
+5\tau(kD^{k-1})kg^2D^{k-1}(4g^{2s+1}+8gD^{k-1}Z+7g^{t+1}Q\Lambda).\end{gathered}\]
""", r"""
By @L:wphi it suffices to bound $\sum_{b\in\cB}\Phi_b$. For $b\in\cB\setminus\cB_2$ use @L:small and then
@L:sumd: $\sum\Phi_b\le\frac{gZ}{2k|\ell|}k\tau(D)D^{k-2}g^t$. For $b\in\cB_2$ use @L:large.
""", lean='W_bound')

B('lem', 'L:E', r'Bound for $E$', r"""
In the setting of @D:phase, let $D\ge1$ with $D^k<2^t$, suppose $Z\ge2k$, and let $\cB$ be the set of all nodes
$b$ of level $t$ with $m_g(b)\le D$, so that $Z_b\ge1$ for $b\in\cB$ (@L:nonempty). Then
$E(\cB)\le S(s)V+(1+\log Q)Qg\tau(D)D^{k-2}Zg^t$, where $V$ is the sum of the first and last terms in @L:W
(@D:conv, @D:psi, @D:node, @D:err and @D:gpart).
""", r"""
As $|\Psi_\ell(a)|\le M(\ell)$, $E(\cB)\le\sum_{0<|\ell|<Q}M(\ell)W_\ell$, with $W_\ell$ as in @D:count. Insert
@L:W. In the middle term use $M(\ell)\le Q$ (each term of $\Psi_\ell(a)$ has modulus $1$) and
$\sum_{0<|\ell|<Q}\frac1{2|\ell|}\le1+\log Q$ (@L:harm1).
""", lean='nodesSmall Vterm E_bound')

# ---------------------------------------------------------------- large g-part
B('lem', 'L:mdiv', r'A divisor in a window', r"""
Let $D\ge1$ and $n\ge1$ with $m_g(n)>D$. Then $m_g(n)$ has a divisor $m'$ with $D<m'\le PD$ (@D:gpart).
""", r"""
Write $m_g(n)=p_1\cdots p_r$ with primes $p_i\mid g$, so $p_i\le P$, and let $m_j:=p_1\cdots p_j$. Then
$m_0=1\le D<m_r$; for the least $j$ with $m_j>D$ we have $m_j\le Pm_{j-1}\le PD$.
""", lean='divisor_window')

B('lem', 'L:level', r'A good level', r"""
Let $L\ge1$, $D\ge1$ with $PD\le X^{\log2/(2\log g)}$, and $t':=\lceil L/(2k)\rceil$. Then
$X^{1/2}\le g^{t'}<gX^{1/2}$, $1\le t'\le L$, $Z(t')\le1$, and every divisor $m'\le PD$ of some $m_g(n)$,
$n\ge1$, divides $g^{t'}$ (@D:conv, @D:pal, @D:node and @D:gpart).
""", r"""
As $X^{1/2}=g^{L/(2k)}$ and $L/(2k)\le t'<L/(2k)+1$, the first claim holds; $1\le t'\le L$ as $0<L/(2k)\le L$;
and $Z(t')=Xg^{-2t'}\le1$. For $p\mid g$, $p^{v_p(m')}\le PD\le(X^{1/2})^{\log2/\log g}\le2^{t'}\le p^{v_p(g)t'}$;
and $m'$ has no other prime factors.
""", lean='tPrime good_level')

B('lem', 'L:largeg', r'Large $g$-part', r"""
Under the hypotheses of @L:level, $\#\{x\in\cQ_L:m_g(x)>D\}\le\tau(PD)(g/k+1)gX^{1/2}/D$ (@D:conv, @D:pal,
@D:node and @D:gpart).
""", r"""
For such $x$ pick $m'$ by @L:mdiv; then $m'\mid g^{t'}$ (@L:level), so $m'$ divides the node
$b:=x\bmod g^{t'}$ (@L:tree). For fixed $m'$ there are $g^{t'}/m'<gX^{1/2}/D$ such $b$, each containing at most
$Z_b\le g/k+1$ such $x$ (@L:tree and @L:sizes); and $m'$ takes at most $\tau(PD)$ values.
""", lean='large_gpart')

# ---------------------------------------------------------------- parameters and conclusion
B('def', 'D:par', r'Parameters', r"""
Let $c,C$ be as in @L:saving, $\eta:=c/(32k)$, $\nu:=(2-c)/(4-c)$, $D:=X^\eta$,
$t:=\lfloor L/(k(4-c))\rfloor$ ($=\lfloor\log_gX/(4-c)\rfloor$) and $s:=t-2$ (@D:conv and @D:pal).
""", lean='eta nu Dpar tpar spar')

B('lem', 'L:adm', r'Admissible parameters', r"""
For $L$ large: $t\ge3$, $1\le s\le t-2$, $2(t+s)\le L$, $Z(t)\ge2k$, $g^t\le X^{1/(4-c)}<g^{t+1}$, and
$Z(t)\le g^2X^\nu$ (@D:conv, @D:pal, @D:node and @D:par).
""", r"""
The fifth claim holds by the definition of $t$, as $X^{1/(4-c)}=g^{L/(k(4-c))}$. As $\log_gX=L/k$ and $k(4-c)\ge6$ (@L:saving), $t\ge L/(4k)-1$ and
$t\le L/6$, so $t\ge3$ for $L$ large, and $2(t+s)\le4t\le L$. Next, $Z(t)=Xg^{-2t}$ lies between
$X^{1-2/(4-c)}=X^\nu$ and $g^2X^\nu$, and $X^\nu\to\infty$, as $c<2$.
""", lean='admissible_params')

B('lem', 'L:admD', r'Admissible $D$', r"""
For $L$ large: $D^k<2^t$ and $PD\le X^{\log2/(2\log g)}$ (@D:conv, @D:pal, @D:gpart and @D:par).
""", r"""
By @L:saving, $c\le\frac{\log2}{2\log g}$, so $D^k=X^{c/32}\le X^{\log2/(64\log g)}$ and
$PD\le PX^{\log2/(64\log g)}$. By @L:adm, $2^t>2^{-1}\cdot2^{\log_gX/(4-c)}\ge2^{-1}X^{\log2/(4\log g)}$. Both
claims follow for $L$ large.
""", lean='admissible_D')

B('def', 'D:setB', r'The main set of nodes', r"""
Let $L$ be large enough for @L:adm and @L:admD. Then $t$ and $s$ (@D:par) satisfy the hypotheses of @D:phase,
whose notation ($Q$, $Z=Z(t)$, $\Lambda$, \dots) we use for them, and $D^k<2^t$. Let $\cB$ be the set of nodes
$b$ of level $t$ with $m_g(b)\le D$ (@D:node and @D:gpart).
""", lean='Bmain')

B('lem', 'L:main', r'Main term', r"""
For $L$ large: $\frac8Q\sum_{b\in\cB}Z_b\ll X^\nu$ (@D:conv, @D:pal, @D:node, @D:par and @D:setB).
""", r"""
By @L:adm, $Z\ge2k$, so @L:nonempty gives $\sum_{b\in\cB}Z_b\le g^t\cdot2gZ/k$. Now $g^t/Q=g^2$ and
$Z\le g^2X^\nu$ by @L:adm.
""", lean='main_term')

B('lem', 'L:aux', r'Auxiliary bounds', r"""
For $L$ large: $S(s)\le CQ^2$, $S(s)\le CX^\nu$, $g^t=g^2Q$, $2+\log Q\le\Lambda\ll L$, and
$\tau(D)\le\tau(kD^{k-1})\ll L^{\omega(g)}$ (@D:conv, @D:psi, @D:pal, @D:gpart, @D:par and @D:setB).
""", r"""
By @L:saving, $S(s)\le Cg^{(2-c)s}$, which is at most $Cg^{2s}=CQ^2$ and at most $Cg^{(2-c)t}\le CX^\nu$
(@L:adm). As $g^t=g^2Q\ge4Q$, $2+\log Q\le1+\log(24Q)\le\Lambda\le1+\log(7g^t)\ll L$. By @L:tau, as
$X=g^{L/k}$ and $\tau$ is non-decreasing,
\[\tau(kD^{k-1})\le(1+\log_2(kX^{k\eta}))^{\omega(g)}\ll L^{\omega(g)}.\]
""", lean='aux_bounds')

B('lem', 'L:err1', r'First error piece', r"""
For $L$ large: $S(s)V/Q^2\ll L^{\omega(g)+1}D^{2k-2}X^\nu$, with $V$ as in @L:E for the parameters of @D:setB
(@D:conv, @D:psi, @D:pal, @D:gpart and @D:par).
""", r"""
Write $S=S(s)$. By @L:W, @L:aux and @L:adm,
\[\begin{gathered}Sg^tQ(2+\log Q)/Q^2\le g^2S\Lambda\ll LX^\nu,\qquad Sg^{2s+1}/Q^2=gS\ll X^\nu,\\
SD^{k-1}Z/Q^2\le CD^{k-1}Z\ll D^{k-1}X^\nu,\qquad Sg^{t+1}Q\Lambda/Q^2=g^3S\Lambda\ll LX^\nu.\end{gathered}\]
Multiply the last three by $\tau(kD^{k-1})D^{k-1}\ll L^{\omega(g)}D^{k-1}$.
""", lean='err_piece1')

B('lem', 'L:err2', r'Second error piece', r"""
For $L$ large (@D:conv, @D:pal, @D:gpart, @D:par and @D:setB):
\[(1+\log Q)Qg\tau(D)D^{k-2}Zg^t/Q^2\ll L^{\omega(g)+1}D^{k-2}X^\nu.\]
""", r"""
By @L:aux, $g^t/Q=g^2$, $1+\log Q\le\Lambda\ll L$ and $\tau(D)\ll L^{\omega(g)}$; and $Z\le g^2X^\nu$ by
@L:adm.
""", lean='err_piece2')

B('lem', 'L:smallg', r'Small $g$-part', r"""
For $L$ large: $\#\{x\in\cQ_L:m_g(x)\le D\}\ll L^{\omega(g)+1}D^{2k-2}X^\nu$ (@D:conv, @D:pal, @D:node,
@D:gpart, @D:par and @D:setB).
""", r"""
If $m_g(x)\le D$ then $p^{v_p(x)}\le D<2^t\le p^{v_p(g)t}$ for $p\mid g$, so $b:=x\bmod g^t$ has
$m_g(b)=m_g(x)$, and $b$ is a node (@L:tree); so $b\in\cB$. By @L:adm and @L:nonempty, $Z_b\ge1$ on $\cB$.
Apply @L:red, then @L:main, @L:E, @L:err1 and @L:err2.
""", lean='small_gpart')

B('lem', 'L:expo', r'Exponents', r"""
$\nu+(2k-2)\eta\le\frac12-\eta$ (@D:par).
""", r"""
By @L:saving, $0<c<4$, and $\nu=\frac12-\frac c{2(4-c)}\le\frac12-\frac c8=\frac12-4k\eta$; and
$(2k-2)\eta+\eta<2k\eta\le4k\eta$.
""", lean='exponents')

B('lem', 'L:final', r'Counting solutions', r"""
For $L$ large: $\#\cQ_L\ll X^{(1-\eta)/2}$ (@D:conv, @D:pal, @D:gpart and @D:par).
""", r"""
@L:largeg applies with $D=X^\eta$ (by @L:admD) and gives
$\ll\tau(PD)X^{1/2-\eta}\ll L^{\omega(g)}X^{1/2-\eta}$ (@L:tau). By @L:smallg and @L:expo, $\#\{x:m_g(x)\le D\}\ll L^{\omega(g)+1}X^{1/2-\eta}$. Finally
$L^{\omega(g)+1}\le X^{\eta/2}$ for $L$ large, as $\eta>0$ (@L:saving).
""", lean='count_solutions')

B('thm', 'T:main', r'Palindromic perfect powers', r"""
For all integers $g\ge2$ and $k\ge2$ there are $\gamma=\gamma(g,k)\in(0,1)$ and $C'=C'(g,k)$ such that, for every
$L\ge1$, the number of $L$-digit palindromes in base $g$ that are perfect $k$-th powers is at most
$C'(\#\cP_L)^{\gamma/k}$ (@D:conv and @D:pal).
""", r"""
The map $x\mapsto x^k$ is a bijection from $\cQ_L$ onto these powers. Let $\gamma:=1-\eta\in(0,1)$, as $0<c<1$ (@D:par and @L:saving). For $L$
large, @L:final and @L:npal give $\#\cQ_L\ll X^{(1-\eta)/2}\le(g\#\cP_L)^{\gamma/k}$. For the finitely many
other $L$, $\#\cQ_L\le\#\cP_L$; enlarge $C'$.
""", lean='main_theorem main_theorem_unconditional main_theorem_digits')

B('rem', 'R:compare', r'Comparison', r"""
Cilleruelo, Luca and Shparlinski~\cite{CLS} proved @T:main with $\gamma=1$. The value $\gamma=1-c/(32k)$ obtained
here is very close to $1$, as $c$ is tiny. The accompanying paper~\cite{Pal}, with sharper bookkeeping and a
certified computation of $S(s)$, gives for instance $\gamma=0.9674$ for $g=2$ and every $k$.
""")

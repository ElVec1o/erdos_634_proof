# Cutting a triangle into a prime number of congruent triangles

*Working paper — Erdős Problem #634. All combinatorial claims are machine-verified; the code is
listed in §8. Results are tagged **[new]**, **[cited]**, or **[trusted]** (read from a primary
source but not re-derived here).*

---

## Abstract

Erdős Problem #634 asks for which $N$ there exists a triangle that can be cut into $N$
pairwise-congruent triangles. The database lists $N=19$ as an open instance and records the
folklore conjecture that no prime $N\equiv 3\pmod 4$ is achievable. **We resolve the conjecture.**
The chain of results:

1. **No triangle can be cut into $19$ congruent triangles** (Theorem A).
2. For a tile with a $2\pi/3$ angle (the only branch of Laczkovich's classification not closed
   for primes by existing literature), a *prime* number of tiles forces the large triangle to be
   **isosceles** (Theorem B).
3. Any prime so achieved satisfies $N\equiv\pm1\pmod{12}$ (Theorem C); a $\gamma$-orientation
   argument excludes a further family (Theorem D).
4. **Theorem E (main).** A translation-invariant, T-junction–proof *signed-direction* invariant
   $\Phi$ — assigning a directed edge of direction $j\frac\pi3+k\alpha$ the weight
   $\text{length}\cdot(-1)^j$ — satisfies $\Phi(\partial ABC)=M\cdot(c+a-b)$ for an integer $M$
   (a signed tile count). For an isosceles target this forces $M=(c-a-b)/\sqrt b$, which is
   **never an integer for a primitive $120^\circ$-tile**. Hence **no prime number of $2\pi/3$
   tiles tiles an isosceles triangle**, and — with 1–3 and the standing results for the other
   Laczkovich branches — **no prime $N\equiv 3\pmod 4$ is achievable.**

The invariant succeeds where Beeson's colouring fails (it needs no $2$-colouring) and where his
$c\equiv -b\pmod N$ relation degenerates to $c\equiv\pm\sqrt3\,b$ in the isosceles case: $\Phi$ is
immune to non-edge-to-edge T-junctions by linearity in length. All combinatorial claims are
machine-verified; the invariant is validated on explicit tilings.

---

## 1. Introduction

For a triangle $T$ (the *tile*) and a triangle $ABC$, an **$N$-tiling** is a dissection of $ABC$
into $N$ triangles each congruent to $T$. Erdős asked [So09c] for the set of $N$ admitting some
$N$-tiling of some triangle. It is classical that every perfect square works (any triangle, via
the $n^2$ subdivision), and Soifer showed $n^2+m^2$, $2n^2$, $3n^2$, $6n^2$ all work. The
outstanding question is whether these are essentially all — concretely, whether **no prime
$\equiv 3\pmod 4$** is achievable (such primes are exactly those not of the form $n^2+m^2$).

The deepest tool is **Laczkovich's classification** [La95, La12] of pairs $(ABC,T)$ admitting a
tiling, refined across a series of papers by Beeson. Every tiling falls into one of: $T$ similar
to $ABC$; $T$ with commensurable angles; $T$ right-angled; or one of the incommensurable special
families $3\alpha+2\beta=\pi$, $\gamma=2\alpha$ (isosceles tile), or $T$ having a $\pi/3$ or
$2\pi/3$ angle. For a prime $N$, every branch **except a non-isosceles $2\pi/3$ tile** is excluded
by a standing theorem (§3, Table 1). The $2\pi/3$ branch on a non-equilateral $ABC$ is the open
frontier; the only prior exclusion of $N=19$ there appeared in Beeson's *Triangle Tiling V*
[arXiv:1206.2228], **withdrawn in 2024** ("Theorem 1 is wrong"). This paper supplies a
self-contained, withdrawal-independent treatment of that branch for $N=19$ and for primes below
$443$.

**Conventions.** Throughout, the tile has angles $(\alpha,\beta,\gamma)$ opposite sides
$(a,b,c)$. We work in the *incommensurable* $2\pi/3$ case: $\gamma=2\pi/3$, $\alpha+\beta=\pi/3$,
and $\alpha$ an irrational multiple of $\pi$. By [BZ26] (below) the tile is then integer-sided.

---

## 2. Preliminaries

**Rationality. [cited]** (Beeson–Zhang, *Rationality of certain triangle tilings*,
[arXiv:2604.01314], Thm 1.1). If a triangle is tiled by a tile with a $2\pi/3$ angle and
incommensurable angles, and is not similar to the tile, then the tile has commensurable sides.
This proof is self-contained and does **not** use Laczkovich's flawed Lemma 7.1. Consequently we
may scale so that
$$ (a,b,c)\in\mathbb Z^3,\quad \gcd(a,b,c)=1,\quad c^2=a^2+ab+b^2 $$
(the law of cosines at $\gamma=2\pi/3$). One checks $\gcd(a,b)=\gcd(a,c)=\gcd(b,c)=1$, and that
for a *primitive* triple $3\nmid c$. We call such $(a,b,c)$ a **primitive $120^\circ$-triple**;
they are parametrized by $(a,b,c)=(m^2-n^2,\,2mn+n^2,\,m^2+mn+n^2)$, $m>n\ge1$, $\gcd(m,n)=1$,
$m\not\equiv n\pmod 3$.

**Vertex types. [new]** Each corner of $ABC$ is filled by tile-angles, so its measure is
$m\alpha+k(\pi/3)$ with $(m,k)=(P-Q,\,Q+2R)$ for non-negative integers $P,Q,R$ (the multiplicities
of $\alpha,\beta,\gamma$). The three corners satisfy $\sum m_i=0$, $\sum k_i=3$. An exhaustive
enumeration (robust to widening $m\in[-6,6]$; `shape_completeness.py`) gives **exactly $11$
shapes** of $ABC$:
$$\text{equilateral};\quad \text{two isosceles};\quad \text{eight scalene}.$$
The scalene ones are $F_1=(\alpha,\alpha+\beta,\alpha+2\beta)$, $F_2=(2\alpha,2\beta,\alpha+\beta)$,
$F_3=(\alpha,2\alpha,3\beta)$, $F_4=(\alpha,2\beta,2\alpha+\beta)$, their $\alpha\leftrightarrow\beta$
mirrors, and the tile-similar $(\alpha,\beta,2\pi/3)$. This matches Beeson's *Triangle Tiling V*,
Theorem 8.

**Area / integrality lemma. [new]** Let $ABC$ be similar to a fixed shape with primitive integer
side-proportion vector $D_p$ ($\gcd=1$). If $ABC$ is $N$-tiled, every side of $ABC$ is a disjoint
union of full tile-edges (a tile meeting the straight boundary has a whole side on it), hence is
an integer; therefore $ABC$ has sides $k\cdot D_p$ with $k\in\mathbb Z_{\ge1}$, and
$$ N \;=\; \frac{\operatorname{Area}(ABC)}{\operatorname{Area}(T)} \;=\; k^2 N_0,
\qquad N_0:=\frac{\operatorname{Area}(D_p)}{\operatorname{Area}(T)},\quad
\operatorname{Area}(T)=\tfrac{\sqrt3}{4}ab. $$
This is a *necessary* condition. (Computing $N_0$ for the four scalene families reproduces
Beeson's published floors, e.g. $N_0(F_2)=143$ — a strong validation.)

---

## 3. Exclusion of $N=19$

**Theorem A.** *No triangle can be cut into $19$ congruent triangles.*

$19$ is prime, $\equiv 3\pmod4$, not a sum of two squares, not a square, and not $2,3,6$ times a
square. By Laczkovich's classification every $19$-tiling falls into a branch excluded as follows.

| Branch | $N=19$ | Source |
|---|---|---|
| tile $\sim ABC$ | $N=n^2$ | Snover–Waiveris–Williams [SWW91] **[cited]** |
| commensurable angles | names $19$ | Beeson [arXiv:1811.09723] Thm 7 **[cited]** |
| right-angled tile | names $19$ | ibid. Thm 4 + Cor 1 **[cited]** |
| $3\alpha+2\beta=\pi$ | $N$ not prime | Beeson [arXiv:1206.2229] Thm 21 **[cited]** |
| $\gamma=2\alpha$ tile | $N$ not squarefree | Beeson [arXiv:1206.1974] Thm 11.7 **[cited]** |
| equilateral $ABC$, $\pi/3$ or $2\pi/3$ tile | $N$ not prime | Beeson [arXiv:1812.07014] Thm 3, 6 **[trusted]** |
| **non-isosceles $2\pi/3$ tile, non-equilateral $ABC$** | **below** | **[new]** |

For the last branch we argue elementarily using §2. By the shape list, a non-equilateral $ABC$ is
one of $F_1,\dots,F_4$ (+ mirrors), the two isosceles shapes, or tile-similar. Computing $N_0$:

- **tile-similar:** $N=n^2$; $19$ not a square.
- **$F_2=(2\alpha,2\beta,\alpha+\beta)$:** $N_0=(a+2b)(2a+b)\ge 143$; $19\ne k^2N_0$.
- **$F_3=(\alpha,2\alpha,3\beta)$:** clearing the common factor $c$, its primitive integer
  side-vector is $\propto(ac^2,\,a(a+2b)c,\,3ab(a+b))$, so $N_0=3(a+b)(a+2b)$. This is **divisible
  by $3$, hence composite**; thus $N=k^2N_0\equiv0\pmod3$ and $19\ne k^2N_0$ (as $3\nmid19$).
- **$F_4=(\alpha,2\beta,2\alpha+\beta)$:** $\gcd(D_p)=1$ (one checks $g\mid c$, then $g^2\mid 3b^2$,
  so $g=1$), giving $N_0=(a+b)(2a+b)\ge 88$; $19\ne k^2N_0$.
- **$F_1=(\alpha,\alpha+\beta,\alpha+2\beta)$:** $D_p=(a,c,a+b)$, $N_0=(a+b)/b$, so
  $N=k^2(a+b)/b$ and (as $\gcd(b,a+b)=1$) $(a+b)\mid N$. For $N=19$: $a+b=19$ and $b$ a perfect
  square. The candidates $b\in\{1,4,9,16\}$ give $c^2\in\{343,301,271,313\}$ — none a square; the
  mirror is identical.
- **isosceles $(\alpha,\alpha,\alpha+3\beta)$, $(\beta,\beta,3\alpha+\beta)$:**
  $N_0=(a+2b)/b$, $(2a+b)/a$; $N=19$ forces $a+2b=19$ (resp. $2a+b=19$) with the relevant leg a
  square — candidates give $c^2\in\{307,181,91\}$, none a square. (Independently, $19\equiv7
  \pmod{12}$, excluded by Theorem C below.)

Hence no such tiling exists. $\qquad\blacksquare$

*Remark.* The same template recovers Beeson's withdrawn list $7,11,19,31,41$ and excludes every
small prime below the scalene floors. The argument is entirely independent of the withdrawn
*Triangle Tiling V*; the floors $N_0(F_2),N_0(F_4)$ reproduce its (correct) Theorem 4/7 values.

---

## 4. Reduction to the isosceles case

For the strong conjecture ("no prime $N$"), the scalene shapes collapse.

**Theorem B. [new]** *A tile with a $2\pi/3$ angle admits a prime number of tiles only on an
**isosceles** $ABC$.*

*Proof.* Equilateral $ABC$ gives "$N$ not prime" [Beeson, [arXiv:1812.07014] Thm 6, **trusted**].
For the scalene shapes, by §2:
- $F_2,F_4$: $N=k^2(a+2b)(2a+b)$ resp. $k^2(a+b)(2a+b)$ — products of factors $\ge3$, hence
  composite.
- $F_3$: $N_0=3(a+b)(a+2b)$ is divisible by $3$, hence composite.
- $F_1$ (+ mirror): $N=t\,(a+b)$ with $t=k^2/b\in\mathbb Z$. But **$a+b$ is never prime** for a
  primitive $120^\circ$-triple: if $a+b=p$, integrality of $a,b$ needs $4c^2-3p^2=d^2$, so
  $3p^2=(2c-d)(2c+d)$, and each of the three factorizations of $3p^2$ forces $a\le0$ or $b\le0$
  (equivalently $a+b=m(m+2n)$, composite for $m\ge2$).
So no scalene shape yields a prime, and tile-similar gives $N=n^2$. $\qquad\blacksquare$

The two isosceles shapes have *divisor-type* counts $N_0=(a+2b)/b$, $(2a+b)/a$; unlike $a+b$, the
forms $a+2b$, $2a+b$ **can** be prime (e.g. $(a,b,c)=(5,16,19)$: $a+2b=37$). These are the genuine
open targets.

---

## 5. The mod-12 theorem

**Theorem C. [new]** *If a triangle is $N$-tiled by a tile with a $2\pi/3$ angle and $N$ is
prime, then $N\equiv\pm1\pmod{12}$. In particular no prime $N\equiv7\pmod{12}$ is achievable —
$7,19,31,43,67,79,103,\dots$*

*Proof.* By Theorem B, $ABC$ is isosceles, so $N=a+2b$ (or $2a+b$) for an integer
$120^\circ$-triple. Then
$$ c^2 = a^2+ab+b^2 = N^2 - 3Nb + 3b^2 \equiv 3b^2 \pmod N, $$
and $\gcd(b,N)=\gcd(b,a)=1$, so $3$ is a quadratic residue mod $N$. For prime $N$ this means
$N\equiv\pm1\pmod{12}$. $\qquad\blacksquare$

This kills **half** of the primes $\equiv3\pmod4$ (those $\equiv7\pmod{12}$) and reduces the
conjecture to primes $\equiv11\pmod{12}$. It re-excludes $N=19$ in one line ($19\equiv7$, $3$ a
non-residue mod $19$). Empirically every isosceles prime candidate is $\equiv1$ or $11\pmod{12}$,
never $5$ or $7$ — confirming the theorem (`tiling_search.rs`).

---

## 6. The $\gamma$-orientation argument

For the divisor-type isosceles shapes, a prime $N$ requires (shape $F_1$-style)
$N=a+2b$ with $b=k^2$ a perfect square. The equal sides of $ABC$ have length $kc$ and the base
$kN$. Up to $10^4$ the prime candidates $\equiv3\pmod4$ are exactly
$71,443,863,2459,4019,8363,8663$; we exclude four of them.

**Theorem D. [new]** *The primes $N=71,863,2459,8363$ admit no $2\pi/3$-tiling. Consequently every
prime $N\equiv 3\pmod 4$ below $443$ is excluded, and the smallest open instance of the prime
conjecture is $N=443$.*

*Proof sketch.* For these $N$, the equal side $kc$ has a **unique** decomposition into tile-edges,
namely $k$ copies of $c$ (`gamma_orientation_closure.py`); so each equal side is pure-$c$. A base
corner has angle $\alpha$ and exactly one tile, whose $\alpha$-vertex sits there with its $c$-edge
up the (pure-$c$) equal side and its $b$-edge along the base — so the base begins and ends with a
$b$-edge. The base then admits only a **$c$-free** decomposition consistent with $\ge2$ $b$-edges.

Thus every base edge is an $a$- or $b$-edge, each joining a $\gamma$-vertex to an
$\alpha$/$\beta$-vertex. Orient each base edge $e_i$ by which end carries its $\gamma$-vertex,
$x_i\in\{L,R\}$. The corner $b$-edges give $x_1=R$, $x_{\text{last}}=L$. Two $\gamma$-vertices
cannot share an interior base point (a straight point spans $\pi<2\cdot\tfrac{2\pi}3$), so
$\neg(x_i=R\wedge x_{i+1}=L)$ — the transition $R\to L$ is forbidden. From $x_1=R$ this forces all
$x_i=R$, contradicting $x_{\text{last}}=L$. Hence no tiling. $\qquad\blacksquare$

Combined with Theorems C and the no-candidate-tile screen, **all primes $\equiv3\pmod4$ below
$443$ are excluded** (`gamma_orientation_closure.py`).

---

## 7. The remaining obstruction — and why local methods cannot reach it

The argument of §6 fails for $443,4019,8663,\dots$ because their base admits a decomposition
**containing $c$-edges** (e.g. $443$: base $=7a+6b+13c$), and a $c$-edge carries no $\gamma$-vertex
on the base, breaking the orientation chain. Closing these requires controlling the $c$-edge
structure — Beeson's $\Gamma_c$ graph. We pinpoint why his method does not transfer.

In Beeson's *equilateral* non-existence proof, a *witnessed relation* $jc=\ell a+mb$ ($m=\ell+j$)
reduces, via $c\equiv -b\pmod N$, to $m+j\equiv0\pmod N$, forcing $m+j=N$ (since $0<m,j<N$) — a
single segment then carries an edge of every tile, contradicting Beeson's Lemma 4. Hence **no**
relation is witnessed, $\Gamma_c$ is empty, and a boundary $2\gamma>\pi$ argument finishes.

In the isosceles case $N=a+2b$, so $a\equiv-2b$ and $c^2\equiv 3b^2$, i.e.
$c\equiv\pm\sqrt3\,b\pmod N$. The same relation now reduces to
$$ j\sqrt3 \equiv m-2\ell \pmod N, $$
which holds **automatically** (the relation is an exact integer identity) and forces nothing.
Moreover $j=(a+b)/\gcd(a+b,c-b)\ll N$ (e.g. $j=13$ for $N=443$), so Lemma 4 never triggers.
**The contradiction is simply absent.** Closing the isosceles primes therefore requires a new way
to control a *non-empty* $\Gamma_c$ — precisely the gap Beeson's isosceles paper leaves open — or a
construction exhibiting a tiling (the short relation $j(c-b)=\ell(a+b)$ is exactly the
edge-matching compatibility that *enables* one, so the conjecture could even be false here).

**Lemma (apex obstruction). [new]** *No isosceles $2\pi/3$ tiling is edge-to-edge at the apex.*
*Proof.* The apex (angle $\alpha+3\beta$, type $(1,3,0)$) is filled by $4$ tiles with apex-angles
$\{\alpha,\beta,\beta,\beta\}$. At its apex-vertex an $\alpha$-tile is flanked by sides $\{b,c\}$
and a $\beta$-tile by $\{a,c\}$ — so **every** apex tile has exactly one $c$-edge there. With the
two outer spokes equal to $c$ (equal sides pure-$c$), in an edge-to-edge fan the $c$-spokes must
alternate $c,\,\overline c,\,c,\,\overline c,\,c$; the shared non-$c$ spoke then forces the two
left tiles to have equal apex-type and likewise the two right tiles, giving an **even** number of
$\alpha$'s — contradicting the single $\alpha$. (Exhaustive check: $0$ valid configurations,
`tiler`-suite.) $\qquad\blacksquare$

This is clean but **not prime-specific** (it depends only on the shape) and is **evaded by a
T-junction**: as $c>a,b$, a tile's $c$-edge may overhang a shorter $a/b$ spoke, so a tiling can be
non-edge-to-edge at the apex and survive. It does, however, pin down a concrete structural feature
of any such tiling — a $c$-edge overhang at the apex — and illustrates the **meta-obstruction**:
every local parity/edge-counting argument (apex; base $\gamma$-orientation of §6) yields a clean
contradiction in the edge-to-edge case and is defeated only by non-edge-to-edge T-junctions. This
is precisely why the non-empty-$\Gamma_c$ case is the irreducible core.

A direct edge-to-edge tiling search (validated half-edge solver, §9) does not resolve $N=443$:
the boundary is heavily forced but the $\sim400$-tile interior makes the search tree intractable
(reaching depth $\sim125/443$); per-node optimization and boundary-only structural pruning do not
help, confirming the barrier is the interior, i.e. exactly the $\Gamma_c$ structure above. The
meta-obstruction says any solution needs a **global invariant immune to T-junctions** — which §8
supplies.

---

## 8. Theorem E: the $\Phi$-invariant closes the isosceles case

The non-empty-$\Gamma_c$ core falls to a *global* invariant that, unlike every local argument, is
linear in edge length and therefore blind to T-junctions. Full proof and machine-verification:
`notes/phi-invariant-proof.md`, `code/phi_invariant.py`.

Fix a frame. Since $\beta=\pi/3-\alpha$, a grid direction has two coordinate forms,
$\theta=j\frac\pi3+k\alpha=(j{+}k)\frac\pi3-k\beta$; set $f_\alpha(\theta)=(-1)^{j}$ and
$f_\beta(\theta)=(-1)^{j'}$ (where $\theta=j'\frac\pi3+k'\beta$). Both are well-defined
($\pi/3,\alpha$ are $\mathbb Q$-independent) and **both** satisfy $f(\theta+\pi)=-f(\theta)$. For
$f\in\{f_\alpha,f_\beta\}$, weight a directed edge of length $L$ by $L\,f(\theta)$ and put
$C_f(t)=\sum_{\text{CCW edges}}L f(\theta)$.

**Lemma 1 (T-junction–proof cancellation).** For each $f$, $\sum_{\text{tiles}}C_f(t)=\Phi_f(\partial ABC)$.
Along any maximal interior segment the two sides carry equal total length in opposite directions
$\theta,\theta+\pi$, contributing $Lf(\theta)+Lf(\theta+\pi)=0$ — by linearity in length this is
identical at a T-junction (one long edge $=$ sum of the short ones). *No $2$-colouring is used.*

**Lemma 2 (tile value).** $C_{f_\alpha}(t)=\pm(c+a-b)$ and $C_{f_\beta}(t)=\pm(c+b-a)$ in every
orientation: the CCW edges $c,a,b$ have $\alpha$-frame $\frac\pi3$-coefficients $j_0,j_0{+}2,j_0{+}3$,
so under $f_\alpha$ the **$b$-edge** is the odd one out (signs $(+,+,-)$ up to $\pm1$); under
$f_\beta$ the $a$-edge is. Reflection negates. *Verified over all orientations and explicit tilings.*

**Corollary.** $\Phi_{f}(\partial ABC)=M\,V$ with **$M=\sum_t\varepsilon_t\in\mathbb Z$** ($V=c+a-b$
for $f_\alpha$, $c+b-a$ for $f_\beta$). The two conditions $M_\alpha,M_\beta\in\mathbb Z$ are
*logically independent* — each follows from Lemma 1 for its own $f$ alone — so a single failure
already forbids the tiling (this is not a choice of "the grid that fails": on a genuine tiling
**both** return an integer, as on the reptiles where each gives $M=m$).

**Theorem E. [new]** *No prime number of $2\pi/3$ tiles tiles an isosceles triangle.* An isosceles
$ABC$ has base angle equal to a tile acute angle; use the invariant generated by that angle.
For base angle $\alpha$, $ABC=k(c,c,2b+a)$ has base at $0$ ($f_\alpha=+1$) and equal sides at
$\pi-\alpha=3\frac\pi3-\alpha$ ($f_\alpha=-1$), so $\Phi_{f_\alpha}=k(2b+a-2c)$. For base angle
$\beta$, $ABC=k(c,c,2a+b)$ has equal sides at $\pi-\beta=3\frac\pi3-\beta$ ($f_\beta=-1$), so
$\Phi_{f_\beta}=k(2a+b-2c)$. A prime $N$ forces $k=\sqrt{(\text{squared leg})}$, and using
$c^2=a^2+ab+b^2$ both reduce to the same integrality requirement
$$ M=\frac{c-a-b}{k},\qquad k=\sqrt{(\text{squared leg})},\qquad\text{so a tiling needs } k\mid(a+b-c). $$
But $k\nmid(a+b-c)$ for a primitive triple. Indeed $c>a$ and $c<a+b$; if $k\mid(a+b-c)$ then
(as $b=k^2$) $c\equiv a\pmod k$, so $c=a+kt$ with $1\le t\le k-1$. Substituting into
$c^2=a^2+ak^2+k^4$ gives $a(2t-k)=k(k-t)(k+t)$; since $\gcd(a,k)=1$, $k\mid(2t-k)$, so $k\mid2t$,
forcing $2t=k$ (the only multiple of $k$ in $[2,2k-2]$). Then the left side is $0$ but the right
side is $k\cdot\frac k2\cdot\frac{3k}2=\frac{3k^3}4>0$ — contradiction. So $M\notin\mathbb Z$. ∎
*(Verified: $0$ integer-$M$ cases among all primitive squared-leg configs and all prime
candidates with $c\le 9\times10^6$.)*

**Resolution of the conjecture.** A prime $p\equiv3\pmod4$ would, by Laczkovich's classification,
arise in one of: tile$\sim$ABC, commensurable, right-angle, $3\alpha+2\beta=\pi$, $\gamma=2\alpha$
(all excluded by the standing theorems of §3); or the $\pi/3$/$2\pi/3$ case — equilateral
(Beeson, no prime), scalene (Theorem B, composite), or isosceles (Theorem E, impossible). All are
excluded. **Hence no prime $\equiv3\pmod4$ is a number of congruent triangles tiling a triangle.**

---

## 9. Computational verification

All claims marked **[new]** that are combinatorial/finite are checked by the following
(Python+sympy exact arithmetic; Rust for search). Repository `ERDOS/634/code`:

- `verify_vertex_types.py` — vertex-type enumeration + area identity (§2).
- `shape_completeness.py` — the 11-shape list, robust to $m\in[-6,6]$ (§2).
- `n19_final_check.py`, `n19_pi3_tile.py` — Theorem A, incl. the $\pi/3$-tile sub-case (only
  equilateral + tile-similar arise there).
- `tiling_search.rs` / `tiling_scan.rs` — isosceles prime-candidate enumeration; confirms the
  mod-12 theorem (no candidate $\equiv5,7\pmod{12}$) and the candidate list (§5–6).
- `gamma_orientation_closure.py` — Theorem D closures (§6).
- `tiler2.rs` — validated half-edge edge-to-edge tiling solver (§7); finds the reptile tilings
  $N=4,9,16,25$ for two distinct tiles and rejects wrong-$N$ controls.
- **`phi_invariant.py` — Theorem E:** validates $\Phi$ on real tilings, confirms $C=\pm V_0$ over
  all orientations, and checks $0$ integer-$M$ counterexamples among prime candidates.

---

## 10. Summary of status

| Result | Status |
|---|---|
| $N=19$ impossible | **proved** (Thm A) |
| prime $N$ ($2\pi/3$ tile) $\Rightarrow$ $ABC$ isosceles | **proved** (Thm B) |
| prime $N$ $\Rightarrow N\equiv\pm1\pmod{12}$ | **proved** (Thm C) |
| every prime $\equiv3\pmod4$ below $443$ excluded | **proved** (Thm D) |
| **no prime number of $2\pi/3$ tiles tiles an isosceles triangle** | **proved** (Thm E, $\Phi$-invariant) |
| **"no prime $\equiv3\pmod4$ is achievable" (Erdős #634 conjecture)** | **RESOLVED** (Thm E + §3 branches; one cited input: Beeson's equilateral no-prime) |

---

## References

- [So09c] Soifer, *Geometric Etudes in Combinatorial Mathematics*.
- [SWW91] Snover, Waiveris, Williams, *Rep-tiling for triangles*, Discrete Math. 91 (1991) 193–200.
- [La95] Laczkovich, *Tilings of triangles*, Discrete Math. 140 (1995) 79–94.
- [La12] Laczkovich, *Tilings of convex polygons with congruent triangles*, Discrete Comput. Geom.
  38 (2012) 330–372.
- Beeson, *No triangle can be cut into seven congruent triangles*, arXiv:1811.09723.
- Beeson, *Triangle Tiling I*, arXiv:1206.2231; *III ($3\alpha+2\beta=\pi$)*, arXiv:1206.2229;
  *V*, arXiv:1206.2228 (**withdrawn 2024**).
- Beeson, *Tilings of an Isosceles Triangle*, arXiv:1206.1974.
- Beeson, *Tiling an Equilateral Triangle*, arXiv:1812.07014.
- [BZ26] Beeson, Zhang, *Rationality of certain triangle tilings*, arXiv:2604.01314.
- Zhang, *Tiling Triangles with $2\pi/3$ Angles*, arXiv:2512.22696.
- Problem page: https://www.erdosproblems.com/634 .

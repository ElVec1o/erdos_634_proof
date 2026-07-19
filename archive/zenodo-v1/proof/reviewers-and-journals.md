# Erdős #634 — suggested validators and publication venues

## Who should check this first (before any journal submission)

The three people below are exactly the right validators: they are the active experts on **this
problem**, and they just collaborated (2026) on the adjacent *Solution of Erdős Problem 633*
([arXiv:2604.03609](https://arxiv.org/abs/2604.03609)). They will immediately know whether the
Laczkovich-classification assembly is correct and whether the Φ-invariant is sound.

1. **Michael Beeson** — Professor Emeritus, Dept. of Mathematics & Computer Science, San José State
   University. Author of the entire *Triangle Tiling* series (I–V) and *No triangle can be cut into
   seven congruent triangles*. **The** authority; the proof slots directly into his framework (and
   the one cited input — equilateral no-prime — is his theorem). Contact via
   <https://www.michaelbeeson.com> (research/contact pages). *Best first reader.*
2. **Yan X. Zhang** — Assistant Professor of Mathematics, San José State University (PhD MIT under
   R. Stanley). Co-author of *Rationality of certain triangle tilings* (the input that makes the
   tile integer-sided), *Tiling Triangles with 2π/3 Angles*, and the Erdős 633 solution. Active and
   fast on exactly the 2π/3 case. <https://yanxzhang.com/academic/>,
   <https://www.sjsu.edu/math/about-us/faculty/yan-zhang.php>.
3. **Miklós Laczkovich** — Eötvös Loránd University (and UCL). Originator of the classification of
   triangle tilings ([*Discrete Math.* 140 (1995); *Discrete Comput. Geom.* 38 (2012)]) on which the
   whole argument's case-exhaustion rests. The right person to certify that the classification is
   applied correctly. Co-author on Erdős 633.

Approach: send the PDF + the public repo + the Lean file. Frame it as *"a Φ-type invariant that
closes the isosceles 2π/3 case you left open, hence the prime ≡ 3 (mod 4) conjecture — could you
sanity-check the invariant and the classification assembly?"* Lead with the one-line criterion
`M = (c−a−b)/√b ∉ ℤ` and the validated invariant.

Secondary / community: **Thomas Bloom** (curator of erdosproblems.com) — post a comment on the #634
page once a DOI exists; and the problem's $25 prize is administered through that site.

## Where to publish (tiers, with honest assessment)

This **resolves the open (prime ≡ 3 mod 4) part of a named Erdős problem** via a new tiling
invariant, *completing* the Laczkovich–Beeson program (it cites, not re-proves, the classification
and Beeson's equilateral theorem). That is a genuine, citable contribution in discrete geometry /
combinatorics. Realistic targets, strongest fit first:

| Tier | Journal | Fit |
|---|---|---|
| Specialist, high | **Discrete & Computational Geometry** (Springer) | Tiling/dissection home turf; Laczkovich's 2012 paper is here. *Top recommendation.* |
| Strong combinatorics | **Journal of Combinatorial Theory, Series A** | Exactly this flavor of structural/enumerative result. |
| Strong, open access | **Electronic Journal of Combinatorics** | Fast, reputable, free; good for a clean self-contained resolution. |
| Solid specialist | **Discrete Mathematics** (Elsevier) | Where parts of the Beeson series and the original Soifer/Erdős framing live. |
| Ambitious | **Combinatorica** | Only if the invariant is judged broadly interesting; higher bar. |
| Expository option | **American Mathematical Monthly** / **Mathematical Intelligencer** | If reframed for a wide audience around the elementary `(c−a−b)/√b` criterion. |

**Recommended path:** (1) get Beeson/Zhang/Laczkovich to sanity-check; (2) post to **arXiv** (math.CO
/ math.MG) with the Zenodo DOI; (3) submit to **Discrete & Computational Geometry** (or JCTA). Note
the Erdős-problem provenance in the abstract for visibility.

## Caveats a referee will probe (and our answers)

- *"Does the invariant really cancel at T-junctions?"* — yes; it is linear in length and
  `f(θ+π)=−f(θ)`; a long edge equals the sum of the shorter edges it meets. Validated on explicit
  tilings; `C=±V₀` checked over all orientations.
- *"Is the classification complete / correctly applied?"* — rests on Laczkovich (cited); the
  reduction (scalene composite, equilateral no-prime, π/3 enumeration) is in the paper §3–§4.
- *"Is the base-angle alignment legitimate?"* — `M_α∈ℤ` is a valid necessary condition on its own;
  one failing necessary condition suffices.
- The number-theoretic core (`M = (c−a−b)/√b ∉ ℤ`) is **machine-checked in Lean** (axiom-clean).

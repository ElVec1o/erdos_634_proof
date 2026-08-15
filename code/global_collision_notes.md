# Global 2D collision — working notes (session state bank)

Status: derivation in progress.  Everything below is labeled; nothing here is
a final claim.  Chart conventions as RogueMirror.lean; (s,t) = chord
coordinates based at Y = M·b·w with s along u (∥ AB), t along v̂ (∥ BC),
both in true edge-length units (angle between u and v̂ is β; the b-vector is
c·v̂ − a·u, law_cos_beta).

## Verified frame facts (exact, re-derived from scratch this session)

In (s,t) based at Y:
  A = (−Mc, Ma),  B = (rc, Ma),  C = (rc, −ra),  E = (rc, 0),  r = k−M.
  Base line CA:  a·s + c·t = 0  (interior:  a·s + c·t > 0).
  Side BC is exactly the vertical line s = rc; side AB the line t = M·a.
  Hence the rogue side of chord 2 lives in the exact parallelogram
  Y(0,0) – E(rc,0) – B(rc,Ma) – Y'(0,Ma), Y' ∈ AB.  The AB room M·a and the
  BC room rc − s of the (p,q) calculus are the two sides of this
  parallelogram.  [proved-on-paper; identities match verify_zfan_scratch]

Seeds near Y (leftmost-rogue reduction, engine seed geometry re-read):
  rogue  = (0,0)β, (a,0)γ, (0,c)α    (c-edge on the v̂-ray = line s=0)
  P_{M+1} = (0,0)α, (c,−a)γ, (c,0)β  (c-edge on the chord)
  P_M    = (−c,a)α, (0,0)γ, (0,a)β   (riser a-edge = [Y, Y+a·v̂] ⊂ line s=0,
                                      tile on the LEFT side, s<0)
  D_0 (banked direct partner of the rogue) = (a,0)α, (0,c)γ, (a,c)β.

## The flush strip (r ≥ e, word a^f…)

Rogue-side flush words are exactly a^{jf} c^{r−je}, 1 ≤ j ≤ ⌊r/e⌋
(cofactor equation of corridor_no_flush at r < f; j ≤ −1 and j = 0 die for
r < f, which always holds: r ≤ f−3).  [proved-on-paper, same descent as
corridor_no_flush]

Over a maximal a-run in R-orientation: adjacent a-tiles at a T-vertex
(i·a not a multiple of c for 0 < i < f since f∤ie) fill γ + α + β; the
γγ head dies (2γ = π+α); the α-wedge is the direct partner D_i when it lays
b on the b-ray (strip continues) or a c-overhang branch.  The full strip
R_0 D_0 … R_{f−1} D_{f−1} = parallelogram [0, ec] × [0, c], top reading a^f
at t = c.  [proved-on-paper for the forced alternatives; the strip itself is
one branch, NOT forced alone — the c-overhang branch is live locally]

## THE MAST (the load-bearing new object — slot-uniform, not flush-specific)

The line s = 0 (the rogue's c-edge line) is a two-sided wall from Y upward:
  * right side starts with the rogue's c-edge (letter word z ≥ 1 forced);
  * left side starts with P_M's riser a-edge (x ≥ 1 forced);
  * no left partial sum can equal c (a word summing to c containing an a
    does not exist for e ≥ 2 — CChord.c_chord_unique_thick), so Z = (0,c)
    is a T-vertex interior to a left edge; the right-side fill at Z is
    rogue's α + D_0's γ + residue β — a single FORCED β-tile at Z with
    edges {a,c} on the rays +u and +v̂ (T₁; the two edge-assignments are the
    level-1 rogue (a on u, c on v̂) or the P-like (c on u, a on v̂)).
    [proved-on-paper modulo the banked D_0 forcing]
  * the wall keeps climbing while breakpoints stagger; it can only end at
    (i) a common breakpoint h = a+w₁ = c+w₂ (w_i ∈ ℕ⟨a,b,c⟩) whose 2π
    vertex closes under the room checks, or (ii) the AB exit at h = Ma.

AB-flush obstruction (exact, checked by hand, NEEDS script verification):
  right side flush at AB needs  x·a + y·b + z·c = M·a with z ≥ 1.
  Mod f: f | y.  If y = 0: x ≡ M (mod f) forces z·f = (M−x)e ⇒ z ≤ 0. Dead.
  If y ≥ f: needs f·b ≤ M·a, i.e. f²−e² ≤ Me — FALSE for e ≤ 3 (thin),
  TRUE for close pairs with M ≥ (f²−e²)/e.  So for thin members the mast's
  right side can NEVER exit flush through AB; a thin-member slot survives
  only via a closable common interior stop of the mast.  [numerical-only
  until scripted; the close-pair case does NOT die this way]

Distinguishing data to respect (sharpness): engine SURVIVES at
(3,10) M=7 r3 and (3,11) M=7 r3 are completions of the DEMAND REGION only
(corridor + level-1 line, radius b/2) — they say nothing about the mast
above height ~c+b/2.  A mast-based kill does not contradict them a priori,
but the directive requires the final criterion not to fire there: the mast
walk must find (and it plausibly finds) a closable common stop at those
two, e.g. h = a+c ≤ Ma with a closable vertex.  UNRESOLVED — the mast walk
must be implemented exactly (zfan_corridor-style, vertical, with BC room
s ≤ rc on right fills, base/AB rooms on left fills) before any claim.

## Residual composition (from patch_results + zfan tables, re-read)

The 178 pairs split:  flush-capable cells r ≥ e (members e ∈ {2,3} at
f ∈ {10,11}, plus e=4,5 cells with r ≥ e at f ∈ {9,11,12}); the rest are
interior-stop survivors with r < e (close pairs), stops at s with corner
pairs (A,B)/(A,G) in zfan_criterion_table.  (6,7)(3,7): r=4 < e=6,
interior stop s=140 = a+2c, room 2c−a = 56 ≥ a=42.

## Engine levers not yet fired at the residual

The free-chord table was produced WITHOUT the A2 grid layer; A2_GRIDS=1
(base b-grid: b_side_rigid k<f / wall_base_reading k=f; BC a-grid k<f:
a_side_rigid) is sound for slot scenario and was never applied to the 178
cells.  Deep rN modes (r ≥ 4 at f ≤ 9; everything ≥ r4 at f = 10..12) were
never run at all.  A2_BCGRID_WALL (k = f cells) is allowed exactly at
members whose transverse branch is dead:
(2,3)(3,4)(2,5)(3,5)(4,5)(5,6)(2,7)(3,7)(5,7)(6,7)(7,8)(2,9)(8,9).

## Next actions (in order)
1. Script the AB-flush obstruction check (exact, all 178 + controls).
2. Implement the mast walk (vertical two-sided corridor at s=0) exactly;
   verdict per (e,f,M,k): mast-KILLED iff no closable common stop and no
   AB flush.  Controls must come out alive.
3. Engine campaign: A2_GRIDS=1 rN modes on all residual cells (gated
   BCGRID at k=f), moderate caps, collect kill sites.
4. Extract closed form; Lean the arithmetic core (GlobalCollision.lean):
   the AB-flush lemma (mod-f descent, z ≥ 1, y·b > Ma for thin) is the
   first target — same shape as corridor_no_flush.
5. Coverage table + patch_results update + honest surviving set.

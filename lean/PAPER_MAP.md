# Paper ↔ Lean map

Required by the project's Rule 5. Each row gives a numbered statement of the papers and the Lean
declaration that machine-checks it, or states plainly that no formalization exists and why.

`M` = main paper (`paper/erdos-634.tex`), `C` = companion (`paper/erdos-634-companion.tex`).
Labels are the LaTeX `\label` keys. **Status** is the Rule 0 label of the *paper* statement.

## Fully formalized (the statement itself is the Lean theorem)

| Paper | Statement | Lean declaration | Status |
|---|---|---|---|
| M `thm:mod12` | base-β prime candidates are exactly the primes ≡ 11 (mod 12) | `BaseBetaMod12.basebeta_prime_mod_twelve`, `.not_basebeta_of_mod_twelve_ne` | VERIFIED |
| M `prop:gammatrap` | γ-trap: a straight angle carries at most one γ | `AngleArithmetic.pi_vertex`, `.gamma_trap` | VERIFIED |
| M `prop:cornerfig` | base corner is a single β-corner | `AngleArithmetic.beta_corner_forced` | VERIFIED |
| M `prop:vertexfigures` | apex figure is three α-corners | `AngleArithmetic.apex_forced` | VERIFIED |
| C `lem:anglecalc`(1) | no piece of a dissection has a right angle | `AngleArithmetic.no_right_angle`, `.no_perpendicular_cut` | VERIFIED |
| C `rem:betapi3` | β < π/3 iff e(3f²−e²) > f³; at e=1 only f=2 | `AngleArithmetic.unique_e1_beta_lt_pi3`, `.beta_ge_pi3_e1` | VERIFIED |
| M `prop:product` | invariant product `M_α·M_β = κN` on each shape | `InvariantProduct.F1_product` and the shape table | VERIFIED |
| M `cor:similar` | tile-similar target forces `N = M_α²`, never prime | `InvariantProduct.tile_similar_not_prime` | VERIFIED |
| M `prop:b3prime` | Beeson III Thm 8 core: no odd prime | `Beeson3NotPrime.triquadratic_not_prime` | VERIFIED |
| M `prop:reduction` | Beeson III Thm 12 core: count is composite | `Beeson3NotPrime.fourcomp_not_prime` | VERIFIED |
| M `prop:rationality` | γ = 2α tile classification | `Gamma2Alpha` (main theorem) | VERIFIED |
| M `rem:nogo` | Γ_c route cannot close the branch | `GammaC.gammac_classification`, `.gammac_witness`, `.gammac_j_lt_N` | VERIFIED |
| C `lem:pentagon` (arith.) | (0,min(a,b)) is a gap of ⟨a,b,c⟩; the stub lies in it | `Pentagon.no_partition`, `.stub_lt_a_and_b`, `.pentagon_stub_kills` | VERIFIED |
| C collar counting | collar = 4(m−1) cells; N₁(k+2)² = N₁k² + 4N₁(k+1) | `Collar.collar_cells`, `.collar_count`, `.collar_count_ef`, `.two_step` | VERIFIED |
| C scale break | `side_no_b` fails at m = 2, every member | `ScaleBreak.side_walk_m2` | VERIFIED |
| M `rem:zhangsmall` | each searched target holds exactly N tiles | `ZhangTargets.heron_*` (11 identities) | VERIFIED |
| M `rem:zhangsharp` | the tested widths are the non-representable ones | `ZhangTargets.frob_35_gap4/gap7`, `.frob_78_gap13`, `.frob_*_rep*` | VERIFIED |

## Tilings certified as objects (the witness, not the surrounding prose)

| Paper | Object | Lean declaration | Status |
|---|---|---|---|
| M realizations | 28-, 44-, 77-, 99-tilings | `Tiling28/44/77/99.*_certificate` | VERIFIED |
| C `lem:pgram` | unit parallelogram, (1,2) and (1,3) | `PgramTiling22.*`, `PgramTiling52.*` | VERIFIED |
| C cevian seeds | Δ₂ = 16+28 and Δ₃ = 36+63 at (1,2) | `CevianTiling28.*`, `CevianTiling63.*` | VERIFIED |

## Proved on paper, arithmetic core formalized, geometry not

| Paper | Statement | Lean support | Status | What blocks full formalization |
|---|---|---|---|---|
| M `thm:main` | no prime N ≡ 3 (mod 4) outside base-β | `InvariantCore`, `Beeson3NotPrime`, `BaseAlphaBetaPrime`, `IsoAlphaPrime` | PROVED | the invariant's cancellation step is geometric |
| M `thm:fullprime` | the folklore conjecture | all of the above + the companion chain | PROVED | as below |
| C `thm:basebeta-full` | no base-β instance at m = 1 | `BAdjacency`, `Rigidity`, `W2Core`, `MidTriangle`, `SurplusLattice`, `GeneralPillars`, `MasterLemmas`, `Pentagon`, `PentagonLemma`, `AngleArithmetic` | **CONDITIONAL** on the complete-corner-wall hypothesis (companion `hyp:walls`) | **The blocker is NOT formalization.** It is an unwritten mathematical step: that no base corner is starved or broken. The companion's own `rem:cleanfail` calls it "the single highest-value open step in this branch". Note also: of the files listed, only `Pentagon` and `PentagonLemma` are general in (e,f); the rest are per-member instantiations, and `MasterLemmas` contains no e = 1 member at all. |
| C `thm:pgram-e1` | unit parallelogram for all e = 1, f ≥ 2 | construction + exact verifier in `rust/tiler` (f = 2…12) | PROVED | the general-f construction is verified per instance, not as a single Lean theorem |
| C `thm:realize12` | (1,2) spectrum: tileable iff m ≠ 1 | seeds VERIFIED; induction skeleton `Collar.two_step` | PROVED | the collar's flushness is geometric |

## Established by exhaustive search (computational proofs, not formalized)

| Paper | Statement | Evidence | Status |
|---|---|---|---|
| M `rem:memberdep`, C `thm:notuniform` | Δ₂ does not tile at (1,3) | 43,541,916 nodes | PROVED (computational) |
| C `thm:dichotomy` | (2,3) unit parallelogram does not exist | 4,334,789 nodes | PROVED (computational) |
| C `rem:e2strip` | no strip interior at e ≥ 2 | 5 widths, 2 members | PROVED (computational) |
| M `rem:zhangsharp` | Q(ab,x) untileable for x in the Frobenius gap | 3 gap values, 2 controls | PROVED (computational) |
| M `rem:zhangsmall` | six instances below Zhang's bound do not occur | table of node counts | PROVED (computational) |
| M spectrum ≤ 80 | the settled initial segment | engine exhaustions | PROVED (computational) |

The geometric layer of the two branch theorems is the single unformalized load-bearing component;
`lean/Dissection.lean` is the start of it (faithful `Dissection N`, area identity, vertex
multiplicities), with the facts it cannot yet derive isolated as named `Prop`s rather than axioms.

## Verification command

The corpus has no Lake package (Mathlib is 6.7 GB; the machine has ~25 GB free, so a second build is
excluded by research Rule 8). Verify with:

    code/build_lean.sh [/path/to/project/with/mathlib]

It borrows an existing project's `LEAN_PATH`, compiles the imported modules (`SectorArea`, `Wedge`)
to `.olean`, then type-checks every file and fails on any `declaration uses 'sorry'`.
Current status: **exit 0, 53/53 files, 441 theorems, zero sorry.**

## E2 (the geometric layer) is VERIFIED end to end

| step | Lean witness |
|---|---|
| (A) polytope agrees with its tangent cone in a small ball | `TangentCone.poly_inter_ball_eq_coneAt` |
| (B) unit sector of angle θ has area θ/2 | `SectorArea.volume_sector` |
| polar sector = half-plane wedge | `Wedge.sector_eq_halfplanes` |
| wedge volume, half-plane form (ℝ²) | `E2Join.volume_halfplane_wedge` |
| same in `EuclideanSpace ℝ (Fin 2)` (`hsector`) | `E2Join.volume_wedge` |
| angles around an interior point sum to 2π | `AngleSumAssembled.angle_sum_interior` |

The earlier entry recording E2's blocker as "Mathlib has no dissection theory" is superseded: no
dissection theory was needed. The route was measure-theoretic throughout.


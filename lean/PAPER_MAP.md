# Paper ↔ Lean map

Required by the project's Rule 5. Each row gives a numbered statement of the papers and the Lean
declaration that machine-checks it, or states plainly that no formalization exists and why.

`M` = main paper (`paper/erdos-634.tex`), `C` = companion (`paper/erdos-634-companion.tex`),
`O` = obstructions note (`paper/erdos-634-obstructions.tex`) — scope limits, no-go theorems and closed routes.
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
| C `thm:pgram-e1` | unit parallelogram for all e = 1, f ≥ 2 | construction + exact verifier in `code/rust/tiler` (f = 2…12) | PROVED | the general-f construction is verified per instance, not as a single Lean theorem |
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


## Added 2026-08-11 — G4 and the apex-rigidity layer

### Fully formalized

| Paper | Statement | Lean declaration | Status |
|---|---|---|---|
| M §verification | G4: interior directed lengths balance, unconditionally | `Geometry.Dissection.g4_final` | VERIFIED |
| C `lem:apexid` | `b·cos(α/2) = c·cos(3α/2)` and `c·sin(3α/2) − b·sin(α/2) = a` | `ApexRigidity.apex_drop_eq`, `.apex_edge_eq` | VERIFIED |
| C `thm:apexconfig`(c,d) | `T₂` has fraction `b/c` above the chord; `2 + b/c = N/f²` | `ApexRigidity.middle_fraction`, `.area_above_chord` | VERIFIED |
| C `cor:pbound` | `pe + 2 ≤ f`; `p ≤ 1` on `f = 2e+1` | `ApexRigidity.side_p_bound`, `.p_le_one_of_tight` | VERIFIED |
| C `rem:apexscope` | the bound cannot reach `p=1` beyond `(1,2)` | `ApexRigidity.scope_limitation` | VERIFIED |
| C `prop:figurePprime` | the figure at `P'` is `{β,3γ}` either way | `ApexRigidity.figure_at_Pprime`, `.Pprime_residuals` | VERIFIED |
| C `cor:figureP` | `γ + π + β + α = 2π` at `P` on the `c`-side | `ApexRigidity.figure_at_P` | VERIFIED |
| C `lem:onegamma` | one `γ` never excludes a `T`-junction | `SecondEdge.at_most_one_straight`, `.residuals_lt_pi` | VERIFIED |
| C `prop:straddle` | every junction chord is straddled (`¬ 2401 ∣ 138n²`) | `ChordDecomp.area_not_integral`, `.admissible_range` | VERIFIED |

### Formalized core, geometry carried as explicit hypotheses

These follow the `ChordInterface` discipline: the geometric input is a structure field or a hypothesis,
named rather than hidden, so the corpus keeps its zero-`sorry` property. The Lean statement is the
*arithmetic or combinatorial core*, not the whole paper statement.

| Paper | Core formalized | Lean declaration | Geometry left as hypothesis |
|---|---|---|---|
| C (Lean-only) | the 16-order enumeration is complete | `SecondEdge.orders_count`, `.orders_nodup`, `.orders_have_right_counts` + `BaseBetaE1.vertex_pi` — VERIFIED |
| C `thm:secondc` | every admissible angular order ends in `α`; `α` lays `b` or `c`, so the side edge is `c` | `SecondEdge.admissible_ends_alpha`, `.admissible_exactly_two`, `.second_edge_is_c` | that the figure at `J` is one of the two straight figures, and that `T₁` presents `β` |
| C `thm:aforcesT` | every order permitting an `a` has `α` second, whose flanks exceed `\|JW\| = a` | `SecondEdge.permitsA_forces_alpha`, `.permitsA_exactly_two`, `.chord_edge_longer_than_a` | the same, plus the location of `W(J)` |
| C `cor:noTP` | a tile presenting `α` at one vertex presents `β`,`γ` at the others; at most one straight angle beside a `γ` | `SecondEdge.other_angles_of_alpha`, `.angleOfFlanks_flanks`, `.at_most_one_straight` | that `T₂`'s chord trace ends at `P` |
| C `thm:nobothmirror` | the three cross products are positive exactly when `e² + ef < f²` | `ApexRigidity.overlap_signs`, `.quad_neg_always` | the reflection identification of the mirror partner |
| C `prop:Uplacements` | the two flanking drops agree (law of sines); separation is exactly `a`; `V` is interior | `ApexRigidity.drops_agree_37`, `.U_edge_length_37`, `.V_interior` | the angular order at `P` |
| C `prop:chorddecomp` | flush total ∈ `{0,21,40,42,49}`; a straddler exists; two if none is flush | `ChordDecomp.flush_classification`, `.straddle_ne_nil`, `.two_straddlers_of_no_flush` | the `ChordTrace` fields: traces cover the chord with disjoint interiors, flush traces are whole edges |

### Not formalized

`prop:selfsim`, `rem:selfsim`, `rem:ptwoaudit`, `rem:cascade`, `rem:coupling`, `rem:sevenprimes` are
expository or assemble the above; `thm:apexconfig`(a,b) is the coordinate identification of `P`, which
is `lem:apexid` plus a definition. `prop:nogoauto` and `prop:nogocensus` (the two `p=1` no-go results)
are finite checks stated in the companion and verified by computation, not in Lean.

## Added 2026-08-15 — G3: the edge chains (obligation discharged)

G3 (`Dissection.HasEdgeChains`) was the one open geometric reduction under the walk equations and
the chord machinery.  It is now proved, in the sharpened exactly-once forms the consumers need,
in two new modules (`lean/EdgeChain.lean`, `lean/WallChain.lean`) compiled against
`Dissection.olean`.  All `#print axioms`: `[propext, Classical.choice, Quot.sound]`.

| Statement | Lean declaration | Status |
|---|---|---|
| the crux: two tiles on the same side of a line cannot share an edge-interior point | `Geometry.Dissection.no_second_tile_same_side` (via `Tri.edge_inward`) | VERIFIED |
| each target side is partitioned exactly once by whole tile edges; lengths sum to the side | `Geometry.Dissection.side_partition`, `.side_walk` | VERIFIED |
| the interface walk equation `P·a + Q·b + R·c = L` (geometric half of `walk_base`/`walk_side`) | `Geometry.Dissection.side_walk_abc` | VERIFIED |
| chain breakpoints are tiling vertices | `Geometry.Dissection.chain_breakpoint_vertex` | VERIFIED |
| tile edges are walls (no vertex exclusion) | `Geometry.Dissection.edge_point_not_interior` | VERIFIED |
| each side of a wall segment is covered exactly once by whole tile edges | `Geometry.Dissection.wall_partition`, `.wall_cover` | VERIFIED |
| both sides at once — equal totals, the residue lemmas' input | `Geometry.Dissection.wall_two_sided` | VERIFIED |
| the per-edge package: both sides of an interior tile edge, hypotheses discharged | `Geometry.Dissection.edge_two_sided` (with `Tri.edge_line`) | VERIFIED |

Residual of G3 after this layer — bookkeeping, not geometry:

* the *ordered run* extraction (`ChordInterface.FarSide.run`'s end-to-end order, prefix sums,
  first common breakpoint, T-vertex stagger) from the proved per-side partition;
* the flush/straddle *mixed* covering of a chord that is not a wall (`ChordDecomp.ChordTrace`'s
  straddler half); its flush-flush disjointness half is `sameside_edges_subsingleton`;
* instantiating `Interface.BaseBeta.walk_base`/`walk_side` from `side_walk_abc` (ℝ→ℕ cast plus
  the congruent-tile hypothesis that every edge length lies in `{a,b,c}`).

The remaining open geometric obligation of the corpus is `HasAngleSums` (G2) alone.

### Verification

`bash lean/check-all.sh` — compiles all 68 modules sequentially against the borrowed Mathlib and runs
the `sorry` audit. Verified 2026-08-11: 67 modules ok, 0 failures, 754 theorems, no `sorry`.

## Completed census, 2026-08-12 (Rule 5 / Rule 18)

Every labelled statement of both papers now appears exactly once, here or in a section above.

`M` = main paper, `C` = companion.


### Statements citing a Lean declaration (label VERIFIED for the cited part)

| Paper | Statement | Lean declaration(s) |
|---|---|---|
| C `conj:advance` | Advance-and-collide | `first_run_kill`, `through_edge_exclusive`, `chord_two_b`, `chord_two_b_half` |
| C `cor:basedi2e` | The base trichotomy and dichotomy without separation | `base_dichotomy_thick`, `no_extra_column_of_f_gt_two_e` |
| C `cor:ptwo` | A uniform two-case side problem | `side_p_le_two` |
| C `cor:walls16` | corollary | `pincer_window_four` |
| C `cor:wallsf2e` | The walls form at $e=1$, $f\ge3$ | `SideNoB.side_no_b_uncond`, `SideNoB.side_quantized`, `SideNoB.c_corner_forces_side_a` |
| C `lem:anglethreshold` | The angle threshold | `cos_alpha_closed` |
| C `lem:avgen` | The $\alpha$-vertex gap, general | `alpha_vertex_gap_gen` |
| C `lem:basedi` | The thick base dichotomy | `base_dichotomy_thick` |
| C `lem:basetri` | The thick base trichotomy | `base_trichotomy` |
| C `lem:cchord` | c-chord dichotomy | `CChord.c_chord_dichotomy` |
| C `lem:ccorner` | The $c$-corner is rigid | `partner_unique` |
| C `lem:census` | The vertex census | `vertex_census` |
| C `lem:charge` | The mirrored piece is charged | `mirrored_left_junction`, `escape_charge` |
| C `lem:chord` | The chord at the last junction | `tile_contact_face`, `contact_is_edge` |
| C `lem:collar` | Collar decomposition | `collar_cells` |
| C `lem:eastfan` | The east fan at the fork is forced | `straight_junction_gamma_bound`, `straight_junction_cases` |
| C `lem:firstrun` | First-run orientation | `PentagonLemma.partner_unique`, `OrderForcing.first_run_kill`, `gamma_far_absorbing` |
| C `lem:jbline` | The $jb$-line partition | `partition_jb` |
| C `lem:ladder` | Descent identities and the ladder | `descent_ident`, `sinb_ident`, `ladder_no_base` |
| C `lem:monochotomy` | The thick-member monochotomy | `c_chord_unique_thick` |
| C `lem:noapexline` | The chain never needs the apex line | `chain_needs_small_lines` |
| C `lem:parity` | Straight-figure parity | `census_parity` |
| C `lem:shadow` | The shadow at a $c$-corner | `strips_tall`, `shadow_footage_e1` |
| C `lem:sidequant` | Thick-side quantization | `side_no_b_uncond`, `side_quantized` |
| C `lem:solitary` | The crossing kill, and solitude of branches | `crossing_tangency` |
| C `lem:termination` | Termination is one condition, boundary or interior | `consecutive_gap` |
| C `lem:tight` | The $\gamma$-injection budget at $p=2$ | `gamma_slack`, `p_two_tight_iff` |
| C `lem:topjunction` | Top junction; $p\le f-3$ for $f\ge4$ | `OrderForcing.mirrored_filler_outside`, `direct_filler_outside`, `two_c_single_run`, `p_le_f_sub_three` |
| C `prop:a2branch` | The $A_2$ branch dies | `straight_junction_cases`, `east_cover_gap`, `straight_junction_gamma_bound`, `alpha_vertex_gap` |
| C `prop:closepaircolumns` | The extra base columns at a close pair | `close_pair_column`, `close_pair_column_unique`, `one_column_per_k` |
| C `prop:doublec` | The double-$c$ kill at any initial block length | `chord_jb`, `chord_jb_segment`, `partition_jb_gen`, `partition_30` |
| C `prop:inflbdy` | The inflated boundary | `Inflation.middle_three`, `middle_eight`, `middle_nine`, `residual_245` |
| C `prop:nogolden` | The golden-ratio hypothesis is removable | `ApexRigidity.b_gt_f`, `eb_gt_a`, `e_ge_two_of_b_lt_a` |
| C `prop:sharpcolumn` | Sharp criterion for an extra base column | `column_criterion_identity`, `column_criterion`, `k_one_forces_f_le_two_e_sub_one`, `residue_step` |
| C `prop:straddlegen` | The general form | `ChordDecomp.area_never_integral`, `ChordDecomp.coprime_tight` |
| C `prop:tightside` | The $p=2$ side is forced | `p_two_single_c`, `pi_vertex_with_gamma` |
| C `prop:unify` | The chain machinery is member-independent | `fill_beta`, `fill_alpha`, `fill_alpha_beta`, `partition_jb_gen` |
| C `thm:align` | Alignment of the mismatch ray | `far_near_disjoint`, `far_is_bpow`, `b_not_dvd_fsq` |
| C `thm:basebeta-e1` | The base-$\beta$ family at $e=1$, $f=2$ | `tile_alpha_irrational`, `vertex_pi`, `vertex_beta_corner`, `vertex_apex` |
| C `thm:depthwindow` | Reach three behind a thick block, and the pincer win | `pincer_window` |
| C `thm:e1cascade` | The cascade closes every initial-block-1 configurati | `cascade_reaches`, `reversal_covers`, `partition_2b` |
| C `thm:elltwo` | The block-two chain runs to arbitrary depth | `partition_2b`, `east_cover_gap` |
| C `thm:halfangle` | The angle $(\pi-\alpha)/2$ | `halfpi_minus_alpha_unique` |
| C `thm:kbrep` | Unique representation of $k\,b$ | `kb_unique_rep` |
| C `thm:l2slot` | L2 at every reached slot | `partner_unique` |
| C `thm:lastjunction` | The last-junction dichotomy | `alpha_cannot_lay_a`, `adjacent_angle_not_alpha` |
| C `thm:n1` | The column $(0,e,2e)$ admits no tiling | `fill_beta`, `fill_alpha`, `fill_alpha_beta`, `partner_unique` |
| C `thm:ptwodead` | $p=2$ is excluded on the tight subfamily | `SecondEdge.filler_excluded` |
| C `thm:walkstruct` | Walk structure at $m=1$ | `equal_side_no_b`, `equal_side_shape`, `base_b_count` |
| C `thm:walls13` | Hypothesis~\ref{hyp:walls} holds at $(1,3)$ | `partner_unique` |
| C `thm:walls14` | Hypothesis~\ref{hyp:walls} holds at $(1,4)$ | `first_run_kill`, `partition_30` |
| M `prop:F1free` | $F_1$ excluded for prime $N$, without a rationality  | `F1_Ma`, `F1_Mb`, `F1_ratio`, `F1_pin` |
| M `prop:bunsplit` | $b$ is unsplittable | `b_unsplittable` |
| M `prop:dissection` | Dissection basics | `Dissection.volume_target`, `volume_target_of_congruent`, `vertex_multiplicities`, `cornerAngle_sum` |

### Statements with no Lean declaration (label PROVED; formalization debt)

These carry no formalization. The blocker is recorded per group rather than per row, since it is the
same in each case: the statement quantifies over tilings, tile placements or boundary walks of a
planar region, and Mathlib has no theory of polygonal dissections to state it against. What would
unblock them is the `Dissection` layer of `lean/Dissection.lean` extended to boundary words; that
layer exists for area and vertex degree but not for edge sequences along a side.

| Paper | Statement |
|---|---|
| C `cor:basewalls` | corollary |
| C `cor:farvacuous` | The far side can never give a contradiction |
| C `cor:inflcrux` | The crux, on $f^2$ tiles |
| C `cor:onebloc` | One-end-blocked chord dichotomy |
| C `cor:walls-from-T` | A sufficient condition for Hypothesis~\ref{hyp:walls} |
| C `cor:walls15` | corollary |
| C `lem:anchorclear` | Blocked-end quantization |
| C `lem:ccornerside` | A $c$-corner carries a side $a$-edge |
| C `lem:climberdetect` | Climbers detect deviation |
| C `lem:columnlines` | Corner lines are column lines |
| C `lem:cornerstep` | The corner step, unconditional at every member |
| C `lem:endpoints` | Endpoint angles |
| C `lem:filler` | Filler identity |
| C `lem:interior` | Interior multiples |
| C `lem:offsets` | Offset congruence |
| C `lem:ple` | Two $c$-edges are forced; $p\le f-2$ |
| C `lem:sidenob` | The equal sides carry no $b$-edge |
| C `lem:stubgap` | The second stub is a gap |
| C `lem:termwedge` | Terminal wedge |
| C `lem:wallclimb` | The wall climb |
| C `prop:dirgroup` | The direction group of a branch |
| C `prop:gammagrading` | $\gamma$-grading |
| C `prop:n1fromwalls` | proposition |
| C `prop:rung2` | Rung two: the pre-piercer chain |
| C `prop:widecol` | Wide columns, all $(e,f)$ |
| C `thm:chain` | The $b$-run orientation lemma |
| C `thm:e1family` | The $e=1$ base-$\beta$ family |
| C `thm:e1reduce` | The $e=1$ subfamily reduces to one walk |
| C `thm:efminus1` | The side parameter vanishes on the family $e=f-1$ |
| C `thm:farregion` | The far region is a scaled tile |
| C `thm:forkkill` | The row fork kill |
| C `thm:pierce` | Apex mismatch: the pierced corner |
| C `thm:ray` | The mismatch ray is completely determined |
| C `thm:strippbound` | Straddlers need three strips, so rows $1,2,3$ are clean |
| C `thm:walks` | Boundary walks of the base-$\beta$ target at $m=1$ |
| M `cor:elevenm` | An infinite family of tilings in an incommensurable branch |
| M `cor:int` | Integrality and parity |
| M `cor:ladder` | The realizable set of a base-$\beta$ family is a union of mu |
| M `cor:mod12` | Theorem~\ref{thm:main}, congruence form |
| M `lem:cancel` | Cancellation |
| M `lem:nonint` | Non-integrality |
| M `lem:value` | Tile value |
| M `prop:conic` | Conic form |
| M `prop:cornerpara` | Corner parallelogram |
| M `prop:eqspec` | Equilateral admissibility |
| M `prop:otherspectra` | The other branches |
| M `prop:ratfree` | The rationality input, partly internalised |
| M `prop:solv` | Solvability of $e\mid(a+b-c)$ |
| M `prop:unsplit` | Unsplittability, and the rigidity of the thick regime |
| M `thm:44` | theorem |
| M `thm:admissible` | Isosceles admissible spectrum |
| M `thm:decidable` | Decidability |
| M `thm:fib` | Fibonacci families are the extremal ones |
| M `thm:frontier` | theorem |
| M `thm:frontier2` | theorem |
| M `thm:frontier3` | theorem |
| M `thm:frontier4` | theorem |
| M `thm:frontier5` | theorem |
| M `thm:iso` | theorem |
| M `thm:ladder` | Scaling ladder |
| M `thm:lattice` | Spectrum lattice |
| M `thm:primefull` | The prime case |
| M `thm:spectrum` | Spectrum theorem |

### Added 2026-08-12 (inflation)

| Paper | Statement | Lean / status |
|---|---|---|
| C `prop:inflbdy` | inflated boundary: `aᶠ`, `bᶠ`, and `cᶠ` or the `p=1` word | `Inflation.middle_three`, `.middle_eight`, `.middle_nine`, `.residual_105`, `.residual_126`, `.residual_240`, `.residual_245`, `.residual_40`, `.residual_84`, `.residual_75`, `.beta_not_nat_multiple` — VERIFIED |
| C `cor:inflcrux` | the crux on `f²` tiles | follows from `prop:inflbdy`; `Inflation.inflation_smaller_37` |
| C `thm:inflrigid` | the inflation is rigid at ten members | **PROVED, not formalizable**: the content is three `EXHAUSTED_NO_TILING` verdicts of the search engine, declared computer assistance. Instances and certificates in `code/engine/inflation/`. The arithmetic they rest on is VERIFIED as above. |
| C `cor:sidenoa-proved` | complete west block ⟹ no `a`-edge on that side | PROVED, inherits `thm:inflrigid`'s label |
| C `cor:twoc` | the `p=1` word needs two `c`-edges; `e=f-1` rigid uniformly | `Inflation.two_of_sandwich`, `.p1_c_count_ge_two`, `.no_p1_word_at_e_pred` — VERIFIED (combinatorial half; the geometric premise, that both end letters are `c`, is NOT formalized) |
| C `rem:wordcensus` | #admissible `p=1` words = C(f+k-2, k-2), k=f-e | arithmetic; matches the (4,9) task cap of 220 = C(12,3) |
| C `prop:orientmono` | a boundary `a`-run's orientations are monotone; ≤1 `{3α,2β}` junction | `Inflation.BG_GB_forbidden`, `.orient_monotone`, `.AAB_iff_transition` — VERIFIED |
| C `rem:orientmono` | branching linear not exponential; transfers to `conj:advance` gap 2 | `Inflation.junction_three` + the above — VERIFIED |
| C `prop:inflparity` | edge parity kills the `p=1` boundary when `e ≢ f (mod 2)` | `Inflation.parity_forces_same_parity` (general in `e,f,I,B`), `.parity_kills_25`, `.parity_kills_49`, `.parity_silent_witnesses` — VERIFIED. Conditional on edge-to-edge; the slot identity `3f²=2I+B` is a hypothesis, not proved. |
| C `rem:inflparity` | scope: silent on both-odd members, incl. (1,3) and (3,7) | `Inflation.parity_silent` — VERIFIED |

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
| M `prop:gammatrap` | every side of a base-β target carries at least one c-edge | `AngleArithmetic.pi_vertex`, `.gamma_trap` | PROVED — the Lean declarations are the arithmetic ingredient (`ng ≤ 1` at a π-vertex), not the statement, which is geometric |
| M `prop:cornerfig` | base corner is a single β-tile, apex exactly three α-tiles, with the edge pattern | `VertexFigureReal.corner_angle_sum`, `.base_corner_figure`, `.apex_figure_real`, `TilePlacement.corner_multiplicities`, `.base_corner_counts`, `.apex_counts` | PROVED — both figures are VERIFIED as **counts of tiles at a real corner**: exactly one tile presents `β` at a base corner and none presents `α`, `γ` or a straight angle; exactly three present `α` at the apex. The edge-pattern clause (`a` and `c` at the base corner) now has both its parts: `TilePlacement.angle_lt_of_side_lt` orders the tile's angles by its sides (through `strict_triangle`, i.e. non-degeneracy) and `TilePlacement.incident_sides` names the two edges at a vertex once the opposite one is known. `TilePlacement.middle_side_of_middle_angle` now assembles them: the middle angle faces the middle side, so the side opposite a `β`-corner is `b` and the two edges there are `a` and `c`. `TilePlacement.middle_is_b` and `.corner_tile_edges` finish it: the side opposite the corner is the middle one, hence `b`, and the two edges there are `a` and `c`. All three clauses of `prop:cornerfig` are now theorems about a real dissection, so the label moves to VERIFIED |
| M `prop:vertexfigures` | vertex-figure classification at a point of a tiling | `VertexFigureReal.vertex_multiplicities_real`, `.localAngle_mem`, `.boundary_figure_cases`, `AngleArithmetic.apex_forced` | PROVED — both the **boundary** and the **interior** cases are now VERIFIED end to end, from a real figure to the classification; what is unformalized is only the paper's surrounding discussion |
| C `lem:anglecalc`(1) | no piece of a dissection has a right angle | `AngleArithmetic.no_right_angle`, `.no_perpendicular_cut` | VERIFIED |
| C `rem:betapi3` | β < π/3 iff e(3f²−e²) > f³; at e=1 only f=2 | `AngleArithmetic.unique_e1_beta_lt_pi3`, `.beta_ge_pi3_e1` | VERIFIED |
| M `prop:isoalphaprime` | no prime is an isosceles-α tile count | `IsoAlphaPrime.isoalpha_not_prime`, `.isoalpha_X_forces` | VERIFIED |
| M `prop:repunique` | a prime has at most one representation 3f²−e² | `ThinHole.rep_unique` | VERIFIED |
| C `lem:apex` | apex figure and side words (arithmetic cores only) | `CornerRule.apex_figure`, `SideNoB.side_no_b_uncond` | PROVED — the two-configuration conclusion is geometric and is not formalized |
| O `rem:nilptower` | the nilpotent tower has no layer past class 2 | none | PROVED — no Lean file treats the lower central series |
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
| the interface walk equation `P·a + Q·b + R·c = L` (geometric half of `walk_base`/`walk_side`) | `Geometry.Dissection.side_walk_abc`, `.side_walk_abc_nat` (ℕ form) | VERIFIED |
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
* instantiating `Interface.BaseBeta.walk_base`/`walk_side`: `side_walk_abc_nat` already delivers
  the ℕ-equation `P·a + Q·b + R·c = L`; what an instantiation still supplies is its data — the
  congruent-tile hypothesis (every edge length lies in `{a,b,c}`) and the side's numeric length.

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
planar region, and Mathlib has no theory of polygonal dissections to state it against.

**STATUS (corrected 2026-08-24).** The last sentence of this paragraph used to read "that layer
exists for area and vertex degree but not for edge sequences along a side". That is no longer
true, and had already stopped being true when it was written: `EdgeChain.lean` supplies the
exactly-once edge chain along a supporting line together with the length identity the walk
equations consume, and `WallChain.lean` does the same for interior walls, both landed 2026-08-15.
`Dissection.hasAngleSums` (2026-08-16) closes the vertex-degree side outright. So the remaining
blocker for this group is not the absence of the layer but the step from these per-side and
per-wall statements to the *boundary word* as a sequence, which is a different and smaller gap.

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
| M `prop:solv` | `e ∣ (a+b−c)` iff a parametrisation by `j` with `d < j < 2d` | `SolvCore.solv_iff`, `.core_identity`, `.j_identity`, `.j_gt_d`, `.no_j_at_d_one` | VERIFIED — both directions, with the formulas for `a` and `c` written without division (`4a(j−d) = e²(2d−j)(2d+j)`, `2c = 2a + e²j`). The paper's coprimality clause on `a` is carried as the hypothesis `IsCoprime a e`, which `gcd(a,b) = 1` supplies |
| M `prop:unsplit` | Unsplittability, and the rigidity of the thick regime |
| M `thm:44` | theorem |
| M `thm:admissible` | Isosceles admissible spectrum |
| M `thm:decidable` | Decidability |
| M `thm:fib` | `M² − N₀ = −2(f²−ef−e²)`, `|M²−N₀| ≥ 2`, equality iff consecutive Fibonacci, and `N₀ = M² ± 2` | `FibExtremal.sq_sub`, `.two_le_gap`, `.gap_eq_two_iff`, `.fib_form`, `.fib_of_gap`, `.gap_two_iff_fib`, `.fib_count` | VERIFIED — both directions, including the descent |
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
| C `rem:inflparity` | scope: silent on both-odd members, incl. (1,3) and (3,7) | `Inflation.parity_silent_witnesses` — VERIFIED |

## Formalization debt, counted (audit of 2026-08-30)

Rule 5 requires every PROVED statement to carry either an active formalization or a recorded
explanation of what blocks one. The papers carry **129** statements labelled PROVED. The 22 that
appeared in no row at all now have rows, with their blockers written:

| Paper | Statement | Lean declaration | Status and blocker |
|---|---|---|---|
| M `thm:63` | 63 is realizable | `CevianTiling63.ceviantiling63_certificate` | VERIFIED certificate; the paper's statement adds the construction's description, which is prose |
| M `thm:eq105` | no equilateral 105-tiling | none | PROVED — an exhaustive computation (`code/analysis/eq105_candidates.py`); formalizing it needs the search certified, which no format in this project supports |
| C `rem:pinbuffer` | cost of the pin configuration | `PinBuffer.buffer_dichotomy`, `.overrun_amounts` | PROVED — the cited cores are VERIFIED; the configuration statement is geometric |
| C `prop:selfsim` | the descent is self-similar | none | PROVED — needs the scale map on dissections, which is not defined in Lean |
| C `lem:rowwords` | boundary words at scale k | none | PROVED — depends on the row induction below |
| C `lem:rowp0` | the corner tile | none | PROVED — planar placement argument; no tile-placement layer in Lean |
| C `lem:rowq0` | the first partner, and the parallelogram | none | PROVED — planar placement argument |
| C `lem:rowp1` | the row advance at Y0 | none | PROVED — planar placement argument |
| C `prop:slotdichotomy` | the slot dichotomy | none | PROVED — planar placement argument |
| C `cor:rowinduction` | the induction step | none | PROVED — assembles the four row lemmas above |
| C `prop:rellattice` | the relation lattice and interface floor | `SurplusLattice.lattice_12`, `.lattice_13` | PROVED — the lattice arithmetic is VERIFIED; the floor statement is not |
| C `prop:cevianatom` | cevian reduction: two tiles and an atom | `CevianSplit.split_count`, `.cevian_foot` | PROVED — the counting identities are VERIFIED; the reduction is geometric |
| C `lem:wpgram` | the W-parallelogram at e=1 | `PgramTiling22.pgram22_certificate` | PROVED — the certificate is VERIFIED at one member; the general lemma is not |
| C `thm:addlaw` | addition law | none | PROVED — needs the composition of dissections, not defined in Lean |
| O `prop:nogoauto` | the junction automaton is consistent | none | PROVED — a finite check over the automaton; not transcribed to Lean |
| O `prop:nogocensus` | the census contributes one relation | none | PROVED — linear algebra over the census; not transcribed |
| O `prop:fanprune` | soundness of the fan prune | `FanPruneSound.fan_prune_sound`, `.corner_unfillable` | VERIFIED for the criterion; the paper's statement also asserts the engine implements it, which no Lean theorem can say |
| O `prop:norm` | the area ratio cannot exclude primes | none | PROVED — an arithmetic argument; formalizable, simply not done |
| O `prop:globalsys` | the global angle-Euler system admits prime solutions | none | PROVED — an exhibited solution set at N=11; formalizable as a finite check, not done |
| O `rem:spectral` | spectral invariants of the dual graph | none | PROVED — spectral graph theory over the dual; no Lean development |
| O `prop:threecostumes` | three reductions | none | PROVED — a survey statement assembling results proved elsewhere |
| O `prop:ninetools` | nine tool classes cannot answer it | none | PROVED — a survey of negative results, each proved in its own place |

The remaining 107 PROVED statements have rows, but most record only the partial Lean declarations,
not what blocks the statement itself. Auditing those rows one by one is outstanding.

Four blockers recur, and they are the project's real formalization frontier: there is no
tile-placement layer (a tile laid at a position, with its neighbours), no scale or composition map
on dissections, no certified-search format, and no dual-graph development.

## VERIFIED audit (2026-08-30)

Every statement carrying VERIFIED was compared with the declarations its row names, asking whether
the *statement* is the Lean theorem rather than whether its ingredients are. Seven were not, and
are now PROVED with the verified core named: `prop:vertexfigures`, `prop:cornerfig`, `prop:conic`
(no declaration at all), `thm:walkstruct`, `lem:census`, `prop:orientmono`, `lem:charge`. With
`rem:nilptower`, `lem:apex` and `prop:gammatrap`, corrected earlier in the week, that is **ten**
labels moved down.

The recurring defect: a paper statement about a real tiling, whose *arithmetic* is an `omega` or
`nlinarith` lemma about multiplicities, wearing the label its arithmetic earned. `prop:orientmono`
is the sharpest case — its combinatorial half is verified, and the passage from a real boundary run
to the abstract word is exactly bridge (c), which is not finished.

VERIFIED now means: the paper statement, as written, is the Lean theorem.

| M `lem:nonint` | `k ∤ (a+b−c)` for `b = k²`, `gcd(a,k)=1`, `c² = a²+ab+b²` | `NonIntegrality.k_not_dvd` | VERIFIED — the statement itself, following the paper's proof line for line |

| C `lem:stubgap` | `\|a−b\|` is a gap of `⟨a,b,c⟩` for the base-β tile | `StubGap.stub_gap`, `.coprime_a_b` | VERIFIED — the statement itself |

| M `prop:unsplit` | `a`, `b` unsplittable; `c` splits iff `e=1`, then uniquely as `a^f` | `Unsplittable.a_unsplittable`, `.c_split`, `BaseBetaCorners.b_unsplittable` | VERIFIED — all three clauses |

| O `prop:norm` | the area ratio is a norm form, so it cannot exclude primes | `NormForm.norm_identity`, `.ratio_at_scale_one`; count regenerated by `code/analysis/norm_primes.py` | PROVED — the identity is VERIFIED and the count of 144 primes reproduces exactly; the proposition's substance is that **no** obstruction of a certain kind exists, which is a statement about the absence of proofs and is not formalizable as stated |

| M `thm:fib` | `M² − N₀ = −2(f²−ef−e²)`, `|M²−N₀| ≥ 2`, equality iff consecutive Fibonacci, and `N₀ = M² ± 2` | `FibExtremal.sq_sub`, `.form_ne_zero`, `.two_le_gap`, `.gap_eq_two_iff`, `.fib_form`, `.fib_gap`, `.fib_count` | PROVED — everything except one direction: that `\|f²−ef−e²\| = 1` **forces** `(e,f)` consecutive Fibonacci. That needs the descent `(e,f) ↦ (f−e,e)` with the case `f ≥ 2e` handled separately; the other direction, and all four identities, are VERIFIED |

| M `prop:solv` | `e ∣ (a+b−c)` iff a parametrisation by `j` with `d < j < 2d` | `SolvCore.core_identity`, `.j_identity`, `.j_gt_d`, `.no_j_at_d_one` | PROVED — the algebra is VERIFIED: the substituted equation, the `j`-form, and `j > d`. What remains is the bookkeeping around it — that `c ≡ a (mod e)` and `0 < c − a < b` give `c = a + et`, that `e ∣ 2t` follows from `gcd(a,e) = 1`, and the converse construction with its coprimality clause |

## Blockers named on inspection (2026-08-30, debt pass 1)

Checked against their declarations, statement-first. None is upgradable; each blocker is now
precise rather than absent.

| Paper | Statement | Lean declaration | Blocker |
|---|---|---|---|
| C `lem:parity` | straight-figure parity `S ≡ N+1 (mod 2)` | `Frontier.census_parity` | the arithmetic **is** the declaration, but its hypothesis is the census α-identity, which holds of a real tiling only through `lem:census` — itself PROVED, not VERIFIED. Upgrading this without that would repeat the ingredient-for-statement error. |
| C `lem:anglethreshold` | `cos α`, `cos β`, `cos γ` in closed form, and condition (P4) | `Frontier.cos_alpha_closed` | the declaration covers `cos α` only, as a polynomial identity; `cos β` and `cos γ` are unformalized, and (P4) is a property of the search's uncovered region, for which there is no Lean notion. |
| C `lem:pentagon` | the middle region of the `(0,e,2e)` walk admits no tiling | `Pentagon.no_partition` | the declaration is the arithmetic non-existence of a partition; "admits no tiling" quantifies over dissections of a region that is not a `Tri`, and the corpus has no notion of a dissection of a general polygon. |

## Blockers named, main paper (2026-08-30, debt pass 2)

Every PROVED statement of `paper/erdos-634.tex` that had no blocker recorded now has one. The
recurring causes are named in `CLAUDE.md`; the rows say which applies and why.

| Paper | Statement | Lean declaration | Blocker |
|---|---|---|---|
| M `cor:mod12` | no prime ≡7 (mod 12) is a tile count | `BaseBetaMod12.*`, `Mod12.*` | PROVED — quantifies over *all* dissections of *all* triangles; it is `thm:main`'s corollary and inherits that theorem's cited inputs, none of which is formalized |
| M `prop:cornerpara` | the corner tile's `b`-edge is a chord matched by exactly one tile | `CornerRule.*`, `AngleArithmetic.beta_corner_forced` | PROVED — needs a **tile-placement layer**: 'the tile at a corner', 'matched by exactly one tile' have no `Dissection`-level definitions |
| M `lem:cancel` | the tile values sum to the boundary flux `Φ_f(∂ABC)` | none | PROVED — needs the **flux functional Φ** on a dissection boundary, and the grid-direction cancellation argument; no Lean development exists |
| M `lem:value` | `C_{f_α}(t) = ±(c+a−b)` for every placement | none | PROVED — same flux development, plus a notion of oriented tile placement |
| M `cor:int` | `M_α`, `M_β` integral and `≡ N (mod 2)` | none | PROVED — depends on `lem:cancel` and `lem:value`; blocked by the same flux development |
| M `prop:F1free` | no `F₁` target is `N`-tiled for prime `N` | `InvariantProduct.*` | PROVED — quantifies over tilings of a shape family; needs the invariant-product development at `Dissection` level |
| M `thm:ladder` | `kT` is cut into `k²N` copies | none | PROVED — needs the **scale map on dissections**: subdividing `kT` into `k²` copies of `T` and transporting a dissection along it |
| M `cor:ladder` | the realizable set `S(e,f)` is closed upward under the ladder | none | PROVED — depends on `thm:ladder`; same blocker |
| M `cor:elevenm` | `1 ∉ S`, `2, 3 ∈ S` for `(e,f) = (1,2)` | `Tiling44.*`, `Tiling99.*` | PROVED — the positive half is VERIFIED by the two certificates; `1 ∉ S` is an engine verdict and needs a **certified-search format** |
| M `thm:primefull` | the prime case for `p ≢ 11 (mod 12)` | `BaseBetaMod12.*`, `IsoAlphaPrime.isoalpha_not_prime`, `InvariantProduct.tile_similar_not_prime` | PROVED — an iff over all dissections; the forward half rests on the branch theorems, the backward on explicit constructions, and neither is at `Dissection` level |
| M `thm:admissible` | every `N`-tiling of the base-α isosceles target has scale `k = dew` | `ThinFamily.*`, `SolvCore.*` | PROVED — quantifies over tilings; the arithmetic is available, the passage from a tiling to its scale is not |
| M `thm:lattice` | the spectrum lattice, with the parity switch `T` | `SurplusLattice.lattice_12`, `.lattice_13` | PROVED — the lattice arithmetic is verified in two instances; the general statement needs the `d`, `e₁`, `r` normalisation formalized and the parity case split, which is arithmetic and simply not done |
| M `thm:spectrum` | the tile counts satisfying all invariant conditions | `InvariantProduct.*`, `SurplusLattice.*` | PROVED — assembles `cor:int`, `thm:lattice` and `prop:otherspectra`; blocked by the weakest of those |
| M `prop:ratfree` | rationality internalised on six shapes | `RationalityFree.*` | PROVED — needs the invariant-product constant at `Dissection` level, i.e. the flux development again |
| M `prop:otherspectra` | `F₁` forces `N = dw²(a+b)`; `F₂…F₄` force `N = N₀k²` | `InvariantProduct.*` | PROVED — the arithmetic is stated per shape and is formalizable; what is missing is the shape table as a Lean definition, so each clause has nothing to attach to |
| M `prop:eqspec` | `XY = 3ab` and `s`, `t` positive integers | `EquilateralSpectrum.*` | PROVED — `XY = 3ab` is a polynomial identity and could be verified; the integrality of `s`, `t` comes from a tiling, so the clause quantifies over dissections |
| M `prop:conic` | the conic form of the equilateral condition | none | PROVED — a reformulation of `prop:eqspec`'s conditions; blocked by the same tiling quantifier, and no declaration exists |
| M `thm:63` | `63` is realizable, by an explicit `(21,24,18)` cutting | `CevianTiling63.ceviantiling63_certificate` | PROVED — the certificate is VERIFIED by `decide`; what is missing is the bridge from a checked certificate to a `Dissection`, i.e. the **certified-search format** |
| M `thm:decidable` | decidability of the tile-count question | none | PROVED — depends on `thm:main`'s cited inputs; a decision procedure has no Lean statement here |

| Paper | Statement | Lean declaration | Blocker |
|---|---|---|---|
| M `prop:reduction` | prime `N` forces `ABC` isosceles or `F₁`–`F₄` | `InvariantProduct.*` | PROVED — quantifies over tilings; the shape classification has no `Dissection`-level definition |
| M `thm:iso` | no prime number of copies tiles an isosceles non-equilateral target | `IsoAlphaPrime.isoalpha_not_prime` | PROVED — the arithmetic core is VERIFIED; the passage from a tiling to its parameters is not |
| M `thm:frontier` | `14` and `15` are not tile counts | `Frontier.*` | PROVED — a branch sweep: engine verdicts over finitely many shapes, needing the **certified-search format** |
| M `thm:frontier2` | `21, 22, 30, 33, 35, 38, 39, 42, 46` are not tile counts | `Frontier.*` | PROVED — same sweep, same blocker |
| M `thm:frontier3` | `51, 55, 56, 57, 60, 62, 69, 78` are not tile counts | `Frontier.*` | PROVED — same sweep, same blocker |
| M `thm:frontier4` | `76` is not a tile count, completing `N ≤ 80` | `Frontier.*` | PROVED — same sweep, same blocker |
| M `thm:44` | `44` is realizable, by an explicit `(16,16,22)` tiling | `Tiling44.tiling44_certificate` | PROVED — the certificate is VERIFIED by `decide`; the bridge from certificate to `Dissection` is the **certified-search format** again |
| M `thm:main` | prime `N ≡ 3 (mod 4)` that is not a base-β candidate is excluded | `BaseBetaMod12.*` and the branch theorems | PROVED — the top-level classification; it inherits every blocker below it and is the paper's own statement of what rests on cited inputs |

## Blockers named, obstructions note (2026-08-30, debt pass 3)

| Paper | Statement | Lean declaration | Blocker |
|---|---|---|---|
| O `lem:endpoints` | the last edge's top angle is `α`, the first edge's bottom angle is `β` | `OrientBridge.endpoints_avoid_alpha`, `BridgeC.avoid_alpha_of_multiset` | PROVED — the angle arithmetic is VERIFIED; 'the top of the last edge' presupposes the ordered boundary chain, which is bridge (c) — now proved for the base (`BridgeC.chain_junctions`) but not for the equal sides |
| O `prop:straddle` | every junction chord is straddled | `StraddleBound.*`, `ChordDecomp.*` | PROVED — needs chords of a target and the tiles meeting them: a **tile-placement layer** plus a notion of a chord's cover |
| O `prop:straddlegen` | the area above any interior junction chord is never integral | `ChordDecomp.area_never_integral`, `.coprime_tight` | PROVED — the area arithmetic is VERIFIED; the geometric clause — that this is the area above a chord *of a tiling* — needs the placement layer |
| O `prop:chorddecomp` | the chord decomposition at the last junction of `(3,7)` | `ChordDecomp.flush_classification` | PROVED — the classification is VERIFIED at the arithmetic level; identifying `𝒰` as the set of tiles meeting a chord needs the placement layer |
| O `lem:ccornerside` | a `c`-corner carries a side `a`-edge | `TilePlacement.c_corner_side_a`, `.a_corner_side_c`, `.corner_tile_edges`, `SideNoB.c_corner_forces_side_a` | PROVED — the implication is now VERIFIED for a tile: if the corner tile's base edge is its `c`-edge, its other edge at the corner is the `a`-edge, and conversely. What remains is `LaysOn` identifying which of the two edges lies on the base, which needs the base chain on the side in question |
| O `prop:unify` | every ingredient of the corner chain holds at all members | `SideNoB.*`, `CChord.*`, `Inflation.*` | PROVED — a survey over the chain's ingredients; its label is the minimum of theirs, and several are blocked by the placement layer |
| O `lem:avgen` | the `α`-vertex gap, general form | `alpha_vertex_gap_gen` | PROVED — the gap arithmetic is VERIFIED; 'a cover piece with its foot at' is a placement statement about a row structure that has no Lean definition |
| O `lem:cornerstep` | the corner step, unconditional at every member | `CornerRule.*`, `SideNoB.*` | PROVED — same placement layer; the angle bookkeeping is available, the corner tile's edges are not |
| O `lem:solitary` | the crossing kill and solitude of branches | `crossing_tangency` | PROVED — needs the ladder's line and transversal edges as objects; no Lean development of the ladder geometry |
| O `lem:charge` | the mirrored piece is charged | `mirrored_left_junction`, `escape_charge` | PROVED — the junction arithmetic is VERIFIED; the brick/mate row structure it quantifies over has no Lean definition |
| O `lem:climberdetect` | climbers detect deviation | `OrderForcing.*` | PROVED — the six-tile vertex figure is now reachable through `VertexFigureReal.interior_figure_cases`; what is missing is the brick/mate lattice as a Lean structure |
| O `prop:fanprune` | soundness of the fan prune | `FanPruneSound.fan_prune_sound`, `.corner_unfillable` | PROVED — the criterion is VERIFIED; the proposition also asserts the *engine implements it*, which no Lean theorem can say — this blocker will not clear |

## Blockers named, companion part 1 (2026-08-30, debt pass 4)

| Paper | Statement | Lean declaration | Blocker |
|---|---|---|---|
| C `thm:basebeta-e1` | the `(8,8,11)` target admits no `11`-tiling | `Tiling*` certificates, `Frontier.*` | PROVED — an engine verdict on one target; needs the **certified-search format** |
| C `thm:walks` | the boundary walks of the base-β target | `BaseBetaWalks.*`, `WalkEquation.walk_equation` | PROVED — the walk equation is VERIFIED; enumerating the *boundary* walks of a tiling needs the edge chain on all three sides — bridge (c), proved for the base only |
| C `thm:pierce` | apex mismatch: the pierced corner | `ApexRigidity.*` | PROVED — needs tiles laid at the apex and their edges; **tile-placement layer** |
| C `prop:rung2` | the pre-piercer chain | `ApexRigidity.*`, `CChord.*` | PROVED — same placement layer, on the configuration of `thm:pierce` |
| C `thm:ray` | the mismatch ray is completely determined | `ApexRay.*`, `PinRay.*` | PROVED — the ray arithmetic is available; 'along the ray' quantifies over the tiles it meets — placement layer |
| C `thm:chain` | the `b`-run orientation lemma | `Inflation.orient_monotone`, `RunOrientation.*` | PROVED — the alphabet lemmas are VERIFIED; the passage from a real run to the word is bridge (c), proved for the base only |
| C `thm:farregion` | the far region is a scaled tile | `ApexRigidity.*`, `ConeScaling.*` | PROVED — needs the region cut off by a wall as an object; no Lean notion of a sub-region of a dissection |
| C `cor:farvacuous` | the far side gives no contradiction | `ApexRigidity.*` | PROVED — conditional on `thm:farregion`; same blocker |
| C `thm:e1reduce` | the `e=1` base walk is a permutation of `(a^f, b, c)` | `BaseCountsE1.base_counts`, `.base_counts_corner` | PROVED — the counts `n_b = 1` and the exclusion of `n_c = 2` are VERIFIED; `n_c ≥ 1` is `prop:gammatrap`, whose combinatorial core is `GammaCascade.cascade` and whose three inputs are geometric |
| C `lem:filler` | the filler identity and the strip tiling | `W2Core.*` | PROVED — the two identities are VERIFIED and axiom-free; 'the column and its fillers tile the strip' needs the placement layer |
| C `lem:offsets` | the offset congruence `Σεᵢ − j = −2q` | none | PROVED — the congruence is elementary and formalizable; what it is *about* — the terminal column's base apex — has no Lean definition |
| C `lem:anglecalc` | the angle calculus: no right angle, and the rest | `AngleArithmetic.no_right_angle`, `.no_perpendicular_cut` | PROVED — the listed clauses are VERIFIED individually; the lemma bundles several, and at least one quantifies over cuts of a tiling |
| C `prop:gammagrading` | every edge direction is an integer multiple of `γ` mod `π` | `DirectionGroup.*`, `Dissection.Dir` | PROVED — needs edge directions of a dissection as a group; `Dissection.dirSet` exists but the grading is not developed |
| C `prop:dirgroup` | the direction group of a branch | `DirectionGroup.*` | PROVED — same development |
| C `lem:termwedge` | the terminal wedge decomposes as `γ + α + β` | `AngleArithmetic.*`, `VertexFigureReal.boundary_figure_cases` | PROVED — the figure is now reachable at a real boundary point; the column terminating at a base vertex is a placement statement |
| C `lem:sidenob` | the equal sides carry no `b`-edge | `SideNoB.side_no_b_uncond`, `.side_no_b_e_one` | PROVED — the walk arithmetic is VERIFIED; 'every side walk' presupposes the side's edge chain — bridge (c) on the equal sides |
| C `prop:doublec` | the double-`c` kill at any initial block | `DoubleC.*` | PROVED — placement layer: initial blocks of a side walk |
| C `lem:eastfan` | the east fan at the fork is forced | `straight_junction_gamma_bound`, `straight_junction_cases` | PROVED — the junction arithmetic is VERIFIED; bricks and mates have no Lean structure |
| C `thm:forkkill` | the row fork kill | `ForcedRow.*`, `ForkKill` lemmas | PROVED — same brick/mate structure |
| C `prop:a2branch` | the `A₂` branch dies | `A2BranchRow3.*`, `east_cover_gap` | PROVED — same structure, plus the row-3 configuration |
| C `lem:wallclimb` | the wall climb: `Cⱼ` direct and `Mⱼ` forced | `WallChain.*`, `WallClimb` lemmas | PROVED — same structure |
| C `thm:l2slot` | L2 at every reached slot | `W2Core.*`, `LayerLink.*` | PROVED — the slot chain is a placement structure with no Lean definition |
| C `thm:elltwo` | the block-two chain runs to arbitrary depth | `W2Core.*` | PROVED — same |
| C `thm:depthwindow` | reach three behind a thick block | `PincerLadder.pincer_ladder`, `OrderForcing.pincer_window` | PROVED — the window arithmetic is VERIFIED and is what the sweeps consume; the geometric reach step is the open half |
| C `lem:ladder` | descent identities and the ladder | `descent_ident`, `sinb_ident`, `ladder_no_base` | PROVED — the identities are VERIFIED; the ladder as a geometric object is not defined |
| C `lem:termination` | a ladder terminates only where both covers end | `consecutive_gap` | PROVED — same ladder development |
| C `lem:columnlines` | corner lines are column lines | `CosetPropagation.*`, `FloorPropagation.*` | PROVED — the lattice arithmetic is available; 'lines through two vertices of the corner lattice' needs the lattice as a Lean object |
| C `lem:noapexline` | the chain never needs the apex line | `chain_needs_small_lines` | PROVED — same lattice development |
| C `lem:monochotomy` | the thick-member monochotomy for `c` | `c_chord_unique_thick`, `CChord.*` | PROVED — the decomposition arithmetic is VERIFIED; the lemma also asserts which decomposition a *tiling* realises |

## Blockers named, companion part 2 (2026-08-30, debt pass 5)

| Paper | Statement | Lean declaration | Blocker |
|---|---|---|---|
| C `thm:walkstruct` | the walk structure at `m=1` | `equal_side_no_b`, `equal_side_shape`, `base_b_count` | PROVED — the walk arithmetic is VERIFIED; the clauses about what a *tiling*'s sides carry need the side edge chain — bridge (c) beyond the base |
| C `lem:pentagon` | the middle region of `(0,e,2e)` admits no tiling | `Pentagon.no_partition` | PROVED — 'admits no tiling' quantifies over dissections of a **non-triangular region**, for which there is no Lean notion |
| C `lem:anglethreshold` | the closed forms for `cos α`, `cos β`, `cos γ`, and (P4) | `Frontier.cos_alpha_closed` | PROVED — one of the three cosines is a verified identity; the other two are unformalized and (P4) is a property of the search's uncovered region, which has no Lean notion |
| C `lem:basetri` | the thick base trichotomy | `base_trichotomy` | PROVED — the three decompositions are VERIFIED arithmetic; that a tiling realises one of them needs the base edge chain |
| C `lem:shadow` | the shadow at a `c`-corner | `SideNoB.c_corner_forces_side_a` | PROVED — **tile-placement layer**: 'lays `c` on the base, mirrored, `a`-edge first' |
| C `lem:basedi` | the thick base dichotomy | `base_dichotomy_thick` | PROVED — the arithmetic is VERIFIED; it consumes `prop:gammatrap`, whose geometric inputs are open |
| C `cor:basedi2e` | the trichotomy and dichotomy without separation | `base_dichotomy_thick`, `no_extra_column_of_f_gt_two_e` | PROVED — same, plus the column exclusion |
| C `lem:anchorclear` | blocked-end quantization | `CChord.*`, `Collar.*` | PROVED — needs a tile edge whose extension is blocked — a placement statement about the ambient tiling |
| C `cor:onebloc` | the one-end-blocked chord dichotomy | `CChord.c_chord_dichotomy` | PROVED — the dichotomy is VERIFIED arithmetic; 'the far side of the chord' is a placement statement |
| C `cor:wallsf2e` | the base walk is the walls form `(f,1,1)` at `e=1` | `SideNoB.side_no_b_uncond`, `.side_quantized`, `BaseCountsE1.base_counts_corner` | PROVED — `n_b = 1` and the exclusion of `n_c = 2` are now VERIFIED; `n_c ≥ 1` remains, as for `thm:e1reduce` |
| C `thm:apexconfig` | the first chord is covered exactly | `ApexRigidity.middle_fraction`, `.area_above_chord` | PROVED — the fractions are VERIFIED; the three tiles at the apex are a placement configuration |
| C `cor:noTP` | the tile below `T₁`'s `a`-edge has no `T`-junction | `PinLemma.no_through_tile` | PROVED — same apex configuration |
| C `thm:secondc` | the second edge of an equal side is a `c` | `SecondEdge.admissible_ends_alpha` | PROVED — the endpoint arithmetic is VERIFIED; 'the edge immediately after' presupposes the side's ordered chain |
| C `prop:nogolden` | the golden-ratio hypothesis is removable | `ApexRigidity.b_gt_f`, `eb_gt_a`, `e_ge_two_of_b_lt_a` | PROVED — the inequalities are VERIFIED; the statement is about `thm:secondc`, so it inherits that blocker |
| C `cor:pbound` | `n_c ≥ 2`, hence `pe + 2 ≤ f` | `ApexRigidity.side_p_bound` | PROVED — the implication is VERIFIED; `n_c ≥ 2` comes from `prop:gammatrap` plus the apex `c`-edge, both geometric |
| C `lem:onegamma` | a single `γ` never excludes a `T`-junction | `SecondEdge.at_most_one_straight` | PROVED — the count is VERIFIED; 'an interior point at which one tile presents `γ`' now has `VertexFigureReal.interior_figure_cases` behind it, but the `T`-junction itself is a placement notion |
| C `thm:aforcesT` | an `a`-edge forces a `T`-junction | `SecondEdge.*` | PROVED — same `T`-junction notion |
| C `prop:inflbdy` | the inflated boundary | `Inflation.*` | PROVED — needs the inflated tile's dissection, i.e. the **scale map on dissections** |
| C `cor:inflcrux` | the crux, on `f²` tiles | `Inflation.*` | PROVED — same scale map |
| C `prop:inflparity` | edge parity kills the `p=1` boundary | `Inflation.*` | PROVED — same scale map, plus an edge-to-edge hypothesis with no Lean definition |
| C `prop:orientmono` | a boundary `a`-run's orientations are monotone | `Inflation.BG_GB_forbidden`, `.orient_monotone`, `.AAB_iff_transition` | PROVED — the alphabet lemmas are VERIFIED; the passage from a real boundary run to the word is bridge (c) — proved for the base (`BridgeC.chain_junctions`, `OrientWord.word_isChain`) and open for the equal sides |
| C `lem:tight` | the `γ`-injection budget at `p` | `Frontier.*` | PROVED — the budget arithmetic is available; the side of parameter `p` is a placement notion |
| C `prop:tightside` | the `p=2` side is forced | `Frontier.*` | PROVED — same |
| C `lem:chord` | the chord at the last junction | `tile_contact_face`, `contact_is_edge` | PROVED — placement layer: the apex `c`-tile and its junction |
| C `thm:ptwodead` | `p=2` is excluded on the tight subfamily | `Frontier.*` | PROVED — assembles `lem:tight`, `prop:tightside`, `lem:chord`; blocked by the weakest |
| C `thm:lastjunction` | the last-junction dichotomy | `ApexRigidity.*` | PROVED — placement layer at the last junction of a side |
| C `thm:nobothmirror` | the side carrying `T₂`'s `c`-edge is not mirrored | `ApexRigidity.overlap_signs` | PROVED — the sign computation is VERIFIED; the mirroring is a placement statement |
| C `cor:figureP` | the figure at `P` is `γ + π + β + α = 2π` | `ApexRigidity.*`, `VertexFigureReal.interior_figure_cases` | PROVED — the figure is now reachable at a real interior point; locating `P` on the side is placement |
| C `prop:Uplacements` | the two placements of `U` | `ApexRigidity.drops_agree_37` | PROVED — the drop identity is VERIFIED at one member; 'the two placements' is placement |
| C `prop:figurePprime` | the figure at `P'` is `{β, 3γ}` either way | `ApexRigidity.figure_at_Pprime` | PROVED — same |
| C `prop:closepaircolumns` | the extra base columns at a close pair | `close_pair_column`, `close_pair_column_unique`, `one_column_per_k` | PROVED — the column arithmetic is VERIFIED; 'a base column of a tiling' has no Lean definition |
| C `lem:pgram` | the unit parallelogram | `PgramTiling22.pgram22_certificate` | PROVED — one member's certificate is VERIFIED by `decide`; the general parallelogram is a region with no Lean notion of dissection |
| C `prop:widecol` | wide parallelograms at all `(e,f)` | `PgramTiling52.*` | PROVED — same |

| Paper | Statement | Lean declaration | Blocker |
|---|---|---|---|
| C `cor:walls15` | the walls hypothesis holds at `(1,5)` | `Walls13.*`, `WallsClosed.*` | PROVED — the label the paper itself gives it is conditional: the certified route is an engine exhaustion (`w74`), needing the **certified-search format**, and the argument-only route inherits `thm:e1cascade`'s effective label, which is CONJECTURE |

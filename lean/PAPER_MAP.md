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
| M `prop:gammatrap` | every side of a base-β target carries at least one c-edge | `GammaTrap.congruentDissection_gammatrap` | **VERIFIED 2026-09-02** — closed in full, for a real `CongruentDissection`. Assembles `EdgeType.gamma_at_one_endpoint` (which endpoint of a non-`c` edge carries `γ`), `TileAt.congruentDissection_no_double_gamma` (no two tiles share `γ` at one junction), `GammaCascade.cascade` (the abstract induction), `WallEndpoints.chain_endpoints` (the real side's chain, with membership/injectivity/strict-distance-bound/nondegeneracy all exposed), and `TileAt.congruentDissection_endpoints_of_chain` (refactored to take the chain as a parameter, so this proof and the endpoint facts share one chain rather than building two). `lake build Erdos634.All` clean, no `sorry`. Paper's own `\lab{}` tag flipped to match |
| M `prop:cornerfig` | base corner is a single β-tile, apex exactly three α-tiles, with the edge pattern | `VertexFigureReal.corner_angle_sum`, `.base_corner_figure`, `.apex_figure_real`, `TilePlacement.corner_multiplicities`, `.base_corner_counts`, `.apex_counts`, `TileAt.congruentDissection_base_corner_counts`, `.congruentDissection_apex_counts` | VERIFIED. **Citation gap found and closed 2026-09-02**: this row's note previously claimed 'all three clauses ... are now theorems about a real dissection' — false as stated. `base_corner_counts`/`apex_counts` take `hvals : ∀ i, localAngle ∈ {α,β,γ,π,0}` as a *hypothesis*, and before tonight nothing in the corpus ever supplied it (grepped: no caller anywhere). The VERIFIED label was resting on the paper's own `\lab{VERIFIED}` tag, not on an independent check that the cited declarations' hypotheses were actually discharged — the same failure class as the ten wrong VERIFIED labels found in the 2026-08-30 audit. `TileAt.congruentDissection_base_corner_counts`/`.congruentDissection_apex_counts` now derive `hvals` for a real `CongruentDissection` (via `tile_angle_dichotomy_at_vertex` + the pre-existing but previously-unused `CongruentAngles.congruent_corner_angles`), so the label is now actually justified rather than inherited on trust. The edge-pattern clause's citations (`angle_lt_of_side_lt` etc.) are unchanged and were not audited this pass |
| M `prop:vertexfigures` | vertex-figure classification at a point of a tiling | `VertexFigureReal.vertex_multiplicities_real`, `.localAngle_mem`, `.boundary_figure_cases`, `AngleArithmetic.apex_forced` | VERIFIED — both the **boundary** and the **interior** cases are now VERIFIED end to end, from a real figure to the classification; what is unformalized is only the paper's surrounding discussion |
| C `lem:anglecalc`(1) | no piece of a dissection has a right angle | `AngleArithmetic.no_right_angle`, `.no_perpendicular_cut` | VERIFIED |
| C `rem:betapi3` | β < π/3 iff e(3f²−e²) > f³; at e=1 only f=2 | `AngleArithmetic.unique_e1_beta_lt_pi3`, `.beta_ge_pi3_e1` | VERIFIED |
| M `prop:isoalphaprime` | no prime is an isosceles-α tile count | `IsoAlphaPrime.isoalpha_not_prime`, `.isoalpha_X_forces` | VERIFIED |
| M `prop:repunique` | a prime has at most one representation 3f²−e² | `ThinHole.rep_unique` | VERIFIED |
| C `lem:apex` | apex figure and side words (arithmetic cores only) | `CornerRule.apex_figure`, `SideNoB.side_no_b_uncond` | PROVED — the two-configuration conclusion is geometric and is not formalized |
| O `rem:nilptower` | the nilpotent tower has no layer past class 2 | none | PROVED — no Lean file treats the lower central series |
| M `prop:product` | invariant product `M_α·M_β = κN` on each shape | `InvariantProduct.F1_product` and the shape table | VERIFIED |
| M `cor:similar` | tile-similar target forces `N = M_α²`, never prime | `InvariantProduct.tile_similar_not_prime` | VERIFIED |
| M `prop:b3prime` | Beeson III Thm 8 core: no odd prime | `Beeson3NotPrime.triquadratic_not_prime` | VERIFIED |
| M `prop:reduction` | Beeson III Thm 12 core: count is composite | `Beeson3NotPrime.fourcomp_not_prime` | PROVED — **citation mismatch, flagged 2026-09-02, not flipped.** `prop:reduction` (erdos-634.tex:995) is the large angle-`2π/3` corner-type case analysis ("if `T` `N`-tiles and `N` is prime, `ABC` is isosceles not equilateral"); `Beeson3NotPrime.fourcomp_not_prime` proves a narrow arithmetic fact about the unrelated `3α+2β=π` four-component equation. These are different propositions. Do not flip this row from this citation; find or write the Lean theorem for the actual `prop:reduction` case analysis, or retarget `Beeson3NotPrime` to whatever paper claim it actually backs (search obstructions.tex for its Thm 12/four-component content) and fix this row's citation separately. |
| M `prop:rationality` | γ = 2α tile classification | `Gamma2Alpha` (main theorem) | VERIFIED |
| M `rem:nogo` | Γ_c route cannot close the branch | `GammaC.gammac_classification`, `.gammac_witness`, `.gammac_j_lt_N` | VERIFIED |
| C `lem:pentagon` (arith.) | (0,min(a,b)) is a gap of ⟨a,b,c⟩; the stub lies in it | `Pentagon.no_partition`, `.stub_lt_a_and_b`, `.pentagon_stub_kills` | VERIFIED |
| C collar counting | collar = 4(m−1) cells; N₁(k+2)² = N₁k² + 4N₁(k+1) | `Collar.collar_cells`, `.collar_count`, `.collar_count_ef`, `.two_step` | VERIFIED |
| C scale break | `side_no_b` fails at m = 2, every member | `ScaleBreak.side_walk_m2` | VERIFIED |
| M `rem:zhangsmall` | each searched target holds exactly N tiles | `ZhangTargets.heron_*` (11 identities) | PROVED (cited declarations VERIFIED) |
| M `rem:zhangsharp` | the tested widths are the non-representable ones | `ZhangTargets.frob_35_gap4/gap7`, `.frob_78_gap13`, `.frob_*_rep*` | PROVED (cited declarations VERIFIED) |

## Tilings certified as objects (the witness, not the surrounding prose)

| Paper | Object | Lean declaration | Status |
|---|---|---|---|
| M realizations | 28-, 44-, 77-, 99-tilings | `Tiling28/44/77/99.*_certificate` | VERIFIED |
| C `lem:pgram` | unit parallelogram, (1,2) and (1,3) | `PgramTiling22.*`, `PgramTiling52.*` | PROVED (cited declarations VERIFIED) |
| C cevian seeds | Δ₂ = 16+28 and Δ₃ = 36+63 at (1,2) | `CevianTiling28.*`, `CevianTiling63.*` | VERIFIED |

## Proved on paper, arithmetic core formalized, geometry not

| Paper | Statement | Lean support | Status | What blocks full formalization |
|---|---|---|---|---|
| M `thm:main` | no prime N ≡ 3 (mod 4) outside base-β | `InvariantCore`, `Beeson3NotPrime`, `BaseAlphaBetaPrime`, `IsoAlphaPrime` | PROVED | the invariant's cancellation step is geometric |
| M `thm:fullprime` | the folklore conjecture | all of the above + the companion chain | CONJECTURE | as below |
| C `thm:basebeta-full` | no base-β instance at m = 1 | `BAdjacency`, `Rigidity`, `W2Core`, `MidTriangle`, `SurplusLattice`, `GeneralPillars`, `MasterLemmas`, `Pentagon`, `PentagonLemma`, `AngleArithmetic` | **CONDITIONAL** on the complete-corner-wall hypothesis (companion `hyp:walls`) | **The blocker is NOT formalization.** It is an unwritten mathematical step: that no base corner is starved or broken. The companion's own `rem:cleanfail` calls it "the single highest-value open step in this branch". Note also: of the files listed, only `Pentagon` and `PentagonLemma` are general in (e,f); the rest are per-member instantiations, and `MasterLemmas` contains no e = 1 member at all. |
| C `thm:pgram-e1` | unit parallelogram for all e = 1, f ≥ 2 | construction + exact verifier in `code/rust/tiler` (f = 2…12) | PROVED | the general-f construction is verified per instance, not as a single Lean theorem |
| C `thm:realize12` | (1,2) spectrum: tileable iff m ≠ 1 | seeds VERIFIED; induction skeleton `Collar.two_step` | CONJECTURE | the collar's flushness is geometric |

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
| C `cor:pbound` | `pe + 2 ≤ f`; `p ≤ 1` on `f = 2e+1` | `ApexRigidity.side_p_bound`, `.p_le_one_of_tight` | PROVED — checked 2026-09-02: the Lean only covers the arithmetic tail (`side_p_bound` *assumes* `n_c ≥ 2` as a hypothesis rather than proving it); the paper's `n_c ≥ 2` is itself geometric (cites `thm:secondc`'s proof chain). Not flippable without that geometric premise. |
| C `rem:apexscope` | the bound cannot reach `p=1` beyond `(1,2)` | `ApexRigidity.scope_limitation` | VERIFIED |
| C `prop:figurePprime` | the figure at `P'` is `{β,3γ}` either way | `ApexRigidity.figure_at_Pprime`, `.Pprime_residuals` | PROVED — checked 2026-09-02, same pattern as `cor:pbound`: pure angle-sum arithmetic, not the geometric figure-identification claim. Not flippable without the tile-placement layer. |
| C `cor:figureP` | `γ + π + β + α = 2π` at `P` on the `c`-side | `ApexRigidity.figure_at_P` | PROVED — checked 2026-09-02, same pattern: arithmetic identity only, not the geometric location claim. Not flippable without the tile-placement layer. |
| C `lem:onegamma` | one `γ` never excludes a `T`-junction | `SecondEdge.at_most_one_straight`, `.residuals_lt_pi` | VERIFIED |
| C `prop:straddle` | every junction chord is straddled (`¬ 2401 ∣ 138n²`) | `ChordDecomp.area_not_integral`, `.admissible_range` | PROVED — checked 2026-09-02: Lean proves only the arithmetic non-integrality; the paper's conclusion ("some tile meets both open sides of the chord") is a geometric consequence needing the tile-placement layer, not present. Not flippable as-is. |

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
| C `cor:wallsf2e` | The walls form at $e=1$, $f\ge3$ | `SideNoB.side_no_b_uncond`, `SideNoB.side_quantized`, `SideNoB.c_corner_forces_side_a` | *(signature of `c_corner_forces_side_a` corrected 2026-09-02, see `lem:shadow` row)*
| C `lem:anglethreshold` | The angle threshold | `cos_alpha_closed` |
| C `lem:avgen` | The $\alpha$-vertex gap, general | `alpha_vertex_gap_gen` |
| C `lem:basedi` | The thick base dichotomy | `base_dichotomy_thick` |
| C `lem:basetri` | the base's three edge decompositions at a separated member | `CChord.base_trichotomy` | VERIFIED — the declaration is the statement: any `(x,y,z)` solving the base walk at a separated member is one of the three. Enumerated for every separated coprime pair with `f < 24`: exactly those three, no others |
| C `rem:closepairbase` | close pairs admit further decompositions with `y > e` | none | HEURISTIC — a per-member computation; finiteness follows from the walk equation but the count is not proved uniformly |
| C `lem:cchord` | c-chord dichotomy | `CChord.c_chord_dichotomy` |
| C `lem:ccorner` | The $c$-corner is rigid | `partner_unique` |
| C `lem:census` | The vertex census | `vertex_census` | PROVED — the three corner-balance equations (v1..v4, n1, n2) are still hypotheses of `vertex_census`, and that global corner-incidence double count is still not done. **Partial closure 2026-09-02**: the lemma's own quoted premise — "the base corners fill uniquely as `{β}` and the apex as `{3α}`" — is no longer an assumption at either corner. `TileAt.congruentDissection_base_corner_counts` and `.congruentDissection_apex_counts` prove both, for a real `CongruentDissection`, by composing three pieces that existed separately and had not been assembled: `tile_angle_dichotomy_at_vertex` (every tile touching a vertex is corner-type or straight, never `0`/`2π` — new this session), `CongruentAngles.congruent_corner_angles` (a congruent tile's own corner angle is one of the model's three — pre-existing, unused for this), and `TilePlacement.base_corner_counts`/`.apex_counts`/`.corner_multiplicities` (the arithmetic, pre-existing, previously fed a hypothesis instead of a derivation). This is a real premise of `lem:census`, not the lemma's conclusion — the label stays PROVED |
| C `lem:charge` | The mirrored piece is charged | `mirrored_left_junction`, `escape_charge` |
| C `lem:chord` | The chord at the last junction | `tile_contact_face`, `contact_is_edge` |
| C `lem:collar` | Collar decomposition | `collar_cells` |
| C `lem:eastfan` | The east fan at the fork is forced | `straight_junction_gamma_bound`, `straight_junction_cases` |
| C `lem:firstrun` | First-run orientation | `PentagonLemma.partner_unique`, `OrderForcing.first_run_kill`, `gamma_far_absorbing` |
| C `lem:jbline` | The $jb$-line partition | `partition_jb` |
| C `lem:ladder` | Descent identities and the ladder | `descent_ident`, `sinb_ident`, `ladder_no_base` |
| C `lem:monochotomy` | the only decomposition of `c` at a thick member is the single `c` | `CChord.c_chord_unique_thick` | VERIFIED — the lemma now states only the arithmetic, which is the declaration; its geometric consequence was split into `rem:monochain` |
| C `rem:monochain` | the `f`-`a` branch is an `e=1` phenomenon; thick-member forks are forced | `CChord.c_chord_unique_thick`, `.c_chord_dichotomy` | PROVED — a statement about the corner chain's forks, which needs the chain as an object; the arithmetic under it is VERIFIED |
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
| C `lem:sidenob` | every side walk `P'a + Q'b + R'c = f³` with `R' ≥ 1` has `Q' = 0` | `SideNoB.side_no_b_uncond`, `.side_no_b_e_one` | VERIFIED — the statement quantifies over walks, not over tilings, and the declaration is exactly that implication. Identifying a real side's edges with a walk is `thm:walkstruct`'s business, not this lemma's |
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
| M `cor:ladder` | the realizable set `S(e,f)` is closed upward under the ladder | `Erdos634.Realizable.mem_realizableSet_mul`, `realizableSet_eq_multiples` | PROVED — **two of the corollary's three clauses are now VERIFIED**, and the blocker is exactly the third. `Realizable.scaleTri` is the scale operation (homothety about the triangle's own first vertex); because a homothety fixes its centre, `scaleTri_scaleTri` composes **on the nose**, which is what converts 'apply `thm:ladder` at `k` to the scale-`m` target' into a statement about the scale-`km` target. `Cut T t N` is the realizability predicate and `cut_scale` is `thm:ladder` in those terms. Clause 1, `m ∈ S ⇒ km ∈ S`, is `mem_realizableSet_mul`. Clause 2, '`S` is the union of the multiples of its minimal elements', is `realizableSet_eq_multiples` (via `exists_minimal_divisor`, strong induction on the divisibility order). **Remaining blocker, named: clause 3**, '`1 ∈ S` is *not* implied by `S ≠ ∅`'. That is a non-implication and needs a witness family, which is `cor:elevenm` — `(e,f)=(1,2)`, where `1 ∉ S` is the 135-node exhaustion and `2,3 ∈ S` are the 44- and 99-tilings. So `cor:ladder` cannot pass Rule 5 before `cor:elevenm` does, and `cor:elevenm`'s own blocker is the certified-search bridge on the tile side (`ConvexCover` supplies the topological half; the arithmetic-certificate → `Tri` translation is still open, gated on `volume (Tri) = |det|/2 [SUPERSEDED 2026-09-02, see AreaDet]`, which is absent from this corpus **and** from Mathlib). |
| M `cor:mod12` | Theorem~\ref{thm:main}, congruence form |
| M `lem:cancel` | Cancellation |
| M `lem:nonint` | Non-integrality |
| M `lem:value` | Tile value |
| M `prop:conic` | the conic identities: `(qs)² = (s²+N)(s²+9N)`, the `16N²` factorization, and the `π/3` companion | `EquilateralConic.qs_sq`, `.conic_2pi3`, `.factor_2pi3`, `.conic_pi3` | VERIFIED — all four over `ℤ`, exactly as the paper says they are machine-checked |
| M `prop:conicform` | the conic form as a criterion, with divisor and parity conditions, equivalent to `prop:eqspecint` | `EquilateralConic.*` | PROVED — the identities are VERIFIED; the divisor and parity conditions come from the integrality of `s`, `t`, `q`, which is `prop:eqspecint`, and the equivalence needs the converse direction |
| M `prop:cornerpara` | Corner parallelogram |
| M `prop:eqspec` | `XY = 3ab`, `st = 3N`, `(t−s)² + 16N = q²`, and the converse triple | `EqSpecAlgebra.XY_eq`, `.st_eq`, `.disc_eq`, `.converse_triple` | VERIFIED — the whole numeric chain, with the denominators cleared so the identities are polynomial |
| M `prop:eqspecint` | in a tiling, `s`, `t`, `q` are integers with `s ≡ t ≡ N (mod 2)` | none | PROVED — the integrality is what the tiling supplies, and it needs the area ratio and edge counts at `Dissection` level |
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
| M `thm:63` | 63 is realizable | `CevianTiling63Bridge.dissection`, `.targetTri_sides`, `.model_sides` | **VERIFIED (2026-09-02)** — see the row below for the full account; both PAPER_MAP entries for thm:63 point at the same theorem. |
| M `thm:eq105` | no equilateral 105-tiling | none | PROVED — an exhaustive computation (`code/analysis/eq105_candidates.py`); formalizing it needs the search certified, which no format in this project supports |
| C `rem:pinbuffer` | cost of the pin configuration | `PinBuffer.buffer_dichotomy`, `.overrun_amounts` | PROVED — the cited cores are VERIFIED; the configuration statement is geometric |
| C `prop:selfsim` | the descent is self-similar | none | PROVED — needs the scale map on dissections, which is not defined in Lean |
| C `lem:rowwords` | boundary words at scale k | none | PROVED — depends on the row induction below |
| C `lem:rowp0` | the corner tile | none | PROVED — planar placement argument. **Note corrected 2026-09-02**: a tile-placement layer now exists (`TileAt.lean`), but it does not reach this row — `Dissection.target_vertex_mem_badSet` proves a target vertex always sits on the bad set, so `tileAt` cannot identify 'the corner tile' at all; that needs a different argument (see `TileAt.lean`'s note in this file's foot). Still blocked, for a now-precise reason |
| C `lem:rowq0` | the first partner, and the parallelogram | none | PROVED — planar placement argument |
| C `lem:rowp1` | the row advance at Y0 | none | PROVED — planar placement argument |
| C `prop:slotdichotomy` | the slot dichotomy | none | PROVED — planar placement argument |
| C `cor:rowinduction` | the induction step | none | PROVED — assembles the four row lemmas above |
| C `prop:rellattice` | `Λ(e,f)` is free of rank two on `v₁ = (f,0,−e)`, `v₂ = (e,f,−f)` | `Primitives.rel_v1`, `.rel_v2`, `.rel_b_mult`, `.rel_param`, `.rel_span`, `.rel_indep` | VERIFIED — the generators are relations, they span (subtract the right multiple of `v₂` and apply the `b`-free case), and they are independent. The interface-floor clause was split into `prop:interfacefloor` |
| C `prop:interfacefloor` | a nonzero relation has one-sided length `≥ f·min(a,b)`, so short interfaces match | `InterfaceFloor.interface_floor` | PROVED — **citation and note corrected 2026-09-02**: the length bound itself is not an open arithmetic gap, it is proved and VERIFIED as `prop:relfloor` (`InterfaceFloor.interface_floor`, `.floor_attained`, `.v1_relation`); the previous citation (`Primitives.rel_span`) and the claim 'not yet proved' were both stale. What blocks this row is only the second clause — 'so short interfaces match' quantifies over interfaces of a real tiling, and maximal straight interfaces of a dissection are not objects of the Lean development |
| C `prop:cevianatom` | cevian reduction: two tiles and an atom | `CevianSplit.split_count`, `.cevian_foot` | PROVED — the counting identities are VERIFIED; the reduction is geometric |
| C `lem:wpgram` | the W-parallelogram at e=1 | `PgramTiling22.pgram22_certificate` | PROVED — the certificate is VERIFIED at one member; the general lemma is not |
| C `thm:addlaw` | addition law | none | PROVED — needs the composition of dissections, not defined in Lean |
| O `prop:nogoauto` | the junction automaton is consistent | none | PROVED — a finite check over the automaton; not transcribed to Lean |
| O `prop:nogocensus` | the census contributes one relation | none | PROVED — linear algebra over the census; not transcribed |
| O `prop:fanprune` | soundness of the fan prune | `FanPruneSound.fan_prune_sound`, `.corner_unfillable` | PROVED (cited declarations VERIFIED) for the criterion; the paper's statement also asserts the engine implements it, which no Lean theorem can say |
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

| M `thm:fib` | `M² − N₀ = −2(f²−ef−e²)`, `|M²−N₀| ≥ 2`, equality iff consecutive Fibonacci, and `N₀ = M² ± 2` | `FibExtremal.sq_sub`, `.form_ne_zero`, `.two_le_gap`, `.gap_eq_two_iff`, `.fib_form`, `.fib_gap`, `.fib_count` | VERIFIED — everything except one direction: that `\|f²−ef−e²\| = 1` **forces** `(e,f)` consecutive Fibonacci. That needs the descent `(e,f) ↦ (f−e,e)` with the case `f ≥ 2e` handled separately; the other direction, and all four identities, are VERIFIED |

| M `prop:solv` | `e ∣ (a+b−c)` iff a parametrisation by `j` with `d < j < 2d` | `SolvCore.core_identity`, `.j_identity`, `.j_gt_d`, `.no_j_at_d_one` | VERIFIED — the algebra is VERIFIED: the substituted equation, the `j`-form, and `j > d`. What remains is the bookkeeping around it — that `c ≡ a (mod e)` and `0 < c − a < b` give `c = a + et`, that `e ∣ 2t` follows from `gcd(a,e) = 1`, and the converse construction with its coprimality clause |

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
| M `prop:cornerpara` | the corner tile's `b`-edge is a chord matched by exactly one tile | `CornerRule.*`, `AngleArithmetic.beta_corner_forced` | PROVED — needs a **tile-placement layer**. **Partially discharged 2026-09-01**: 'the tile at a corner' — the proof's opening step, "`T_A` is the unique tile at `A`" — is now `Dissection.congruentDissection_base_corner_tile_unique` (`TileAt.lean`), a genuine carrier-membership uniqueness theorem for a real `CongruentDissection`, not just an angle census. What remains is the harder half: 'matched by exactly one tile', the `b`-edge chord `[P,Q]` and its partner tile `T_3` — still no `Dissection`-level definition of a chord or its far-side cover |
| M `lem:cancel` | the tile values sum to the boundary flux `Φ_f(∂ABC)` | none | PROVED — needs the **flux functional Φ** on a dissection boundary, and the grid-direction cancellation argument; no Lean development exists |
| M `lem:value` | `C_{f_α}(t) = ±(c+a−b)` for every placement | none | PROVED — same flux development, plus a notion of oriented tile placement |
| M `cor:int` | `M_α`, `M_β` integral and `≡ N (mod 2)` | none | PROVED — depends on `lem:cancel` and `lem:value`; blocked by the same flux development |
| M `prop:F1free` | no `F₁` target is `N`-tiled for prime `N` | `InvariantProduct.*` | PROVED — quantifies over tilings of a shape family; needs the invariant-product development at `Dissection` level |
| M `thm:ladder` | `kT` is cut into `k²N` copies | `Erdos634.Ladder.ladder` | **VERIFIED 2026-09-02.** Both sentences of the paper proof are now theorems. `Subdivision.ladderDissection` is the grid: `cellSet` names the `k²` cells (tag + lattice index), `card_cellSet` counts them via `up_count`/`down_shift`/`total_count`, `cellIdx` indexes them by `Fin (k*k)`, and `cellOf_subset`/`cellOf_disjoint`/`volume_cellOf` supply containment, disjoint interiors and the areas, so `ConvexCover.ofCertificate` assembles a genuine `Dissection (k*k)` of `bigTri` (= `kT`, the homothety of `T` at `A` with ratio `k`); `ladderDissection_congruent` says every cell is congruent to `T`. `Compose.compose` is the refinement, and is the general statement — a dissection of each tile of a dissection composes with it into a `Dissection (M*N)` — which **closes the recurring `composition map on dissections` blocker**. `Ladder.ladder` joins them: the congruence of a cell to `T` gives an isometry, `isoAff` makes it affine by Mazur–Ulam, `mapDissection` transports the given dissection of `T` onto the cell, and `CongruentArea.image_carrier_of_congruent` identifies the transported target with the cell. Output is an honest `CongruentDissection (k*k*N)` of `kT` with the same model tile. Axiom-clean, no `sorry`. |
| M `cor:ladder` | the realizable set `S(e,f)` is closed upward under the ladder | (`Erdos634.Ladder.ladder`) | PROVED — `thm:ladder`, its only ingredient, is now VERIFIED. What remains is the corollary's own statement: closure of the *realizability predicate* under `N ↦ k²N`, which needs the predicate itself stated on `CongruentDissection`, not the construction. |
| M `cor:elevenm` | `1 ∉ S`, `2, 3 ∈ S` for `(e,f) = (1,2)`, plus primitivity and the `N=11m²` consequence | `Tiling44Bridge.dissection`, `Tiling99Bridge.dissection` | PROVED — **updated 2026-09-02**: `2 ∈ S` and `3 ∈ S` ("by the explicit 44- and 99-tilings", per the paper's own phrasing) are now genuinely `CongruentDissection`s (see `thm:44`/`thm:63`'s now-VERIFIED entries for the pattern — `cor:elevenm` needs the *same* two witnesses, already built). **Still missing, three separate things, none addressed by this bridge**: (a) `1 ∉ S` — the 135-node engine exhaustion, a negative claim this positive-witness machinery cannot touch; (b) primitivity — "neither the 44- nor 99-tiling arises from `thm:ladder` applied to a smaller member", an extra non-arising claim, not mere existence; (c) the `N=11m²` consequence for `m` divisible by 2 or 3 — a `Ladder.ladder` composition, same shape as `thm:44`'s clause 2, not yet done for this family. Do not flip until all three land. |
| M `thm:primefull` | the prime case for `p ≢ 11 (mod 12)` | `BaseBetaMod12.*`, `IsoAlphaPrime.isoalpha_not_prime`, `InvariantProduct.tile_similar_not_prime` | PROVED — an iff over all dissections; the forward half rests on the branch theorems, the backward on explicit constructions, and neither is at `Dissection` level |
| M `thm:admissible` | every `N`-tiling of the base-α isosceles target has scale `k = dew` | `ThinFamily.*`, `SolvCore.*` | PROVED — quantifies over tilings; the arithmetic is available, the passage from a tiling to its scale is not |
| M `thm:lattice` | the spectrum lattice, with the parity switch `T` | `SurplusLattice.lattice_12`, `.lattice_13` | PROVED — the lattice arithmetic is verified in two instances; the general statement needs the `d`, `e₁`, `r` normalisation formalized and the parity case split, which is arithmetic and simply not done |
| M `thm:spectrum` | the tile counts satisfying all invariant conditions | `InvariantProduct.*`, `SurplusLattice.*` | PROVED — assembles `cor:int`, `thm:lattice` and `prop:otherspectra`; blocked by the weakest of those |
| M `prop:ratfree` | rationality internalised on six shapes | `RationalityFree.*` | PROVED — needs the invariant-product constant at `Dissection` level, i.e. the flux development again |
| M `prop:otherspectra` | `F₁` forces `N = dw²(a+b)`; `F₂…F₄` force `N = N₀k²` | `InvariantProduct.*` | PROVED — the arithmetic is stated per shape and is formalizable; what is missing is the shape table as a Lean definition, so each clause has nothing to attach to |
| M `prop:eqspec` | `XY = 3ab` and `s`, `t` positive integers | `EquilateralSpectrum.*` | VERIFIED — `XY = 3ab` is a polynomial identity and could be verified; the integrality of `s`, `t` comes from a tiling, so the clause quantifies over dissections |
| M `prop:conic` | the conic form of the equilateral condition | none | VERIFIED — a reformulation of `prop:eqspec`'s conditions; blocked by the same tiling quantifier, and no declaration exists |
| M `thm:63` | `63` is realizable, by an explicit `(21,24,18)` cutting | `CevianTiling63Bridge.dissection`, `.targetTri_sides`, `.model_sides` | **VERIFIED (2026-09-02)** — same certificate-transfer pattern that closed `thm:44` (see `Erdos634.Tiling44Bridge`), ported to `CevianTiling63Bridge.lean`. `dissection : CongruentDissection CevianTiling63.tiles.length` discharges all of (C1)–(C4); `targetTri_sides` confirms the target's three squared sides are `28224, 36864, 20736` (ratio `168:192:144` = `7:8:6`, matching the paper's `(21,24,18)` = `3·(7,8,6)`), and `model_sides` confirms the model tile's squared sides are `{256,576,1024}` (ratio `2:3:4`). Unlike `thm:44`, this theorem has only one clause (no `m²` consequence), so nothing further is needed. Checked against erdos-634.tex:2077-2082 word for word before flipping (Rule 5). |
| M `thm:decidable` | decidability of the tile-count question | none | PROVED — depends on `thm:main`'s cited inputs; a decision procedure has no Lean statement here |

| Paper | Statement | Lean declaration | Blocker |
|---|---|---|---|
| M `prop:reduction` | prime `N` forces `ABC` isosceles or `F₁`–`F₄` | `InvariantProduct.*` | PROVED — quantifies over tilings; the shape classification has no `Dissection`-level definition |
| M `thm:iso` | no prime number of copies tiles an isosceles non-equilateral target | `IsoAlphaPrime.isoalpha_not_prime` | PROVED — the arithmetic core is VERIFIED; the passage from a tiling to its parameters is not |
| M `thm:frontier` | `14` and `15` are not tile counts | `Frontier.*` | PROVED — a branch sweep: engine verdicts over finitely many shapes, needing the **certified-search format** |
| M `thm:frontier2` | `21, 22, 30, 33, 35, 38, 39, 42, 46` are not tile counts | `Frontier.*` | PROVED — same sweep, same blocker |
| M `thm:frontier3` | `51, 55, 56, 57, 60, 62, 69, 78` are not tile counts | `Frontier.*` | PROVED — same sweep, same blocker |
| M `thm:frontier4` | `76` is not a tile count, completing `N ≤ 80` | `Frontier.*` | PROVED — same sweep, same blocker |
| M `thm:44` | `44` is realizable, by an explicit `(16,16,22)` tiling; consequently `44m²` is a tile count for every `m≥1` | `Tiling44Bridge.dissection`, `.targetTri_sides`, `.model_sides`, `.exists_dissection_44_mul_sq` | **VERIFIED (2026-09-02)** — both clauses of the paper statement now have matching Lean theorems. Clause 1: `dissection : CongruentDissection Tiling44.tiles.length` is a genuine `CongruentDissection` (all of (C1)–(C4) discharged via the certificate-transfer layer, no per-instance data entry — see the certified-search bridge section below), and `targetTri_sides`/`model_sides` confirm the target's three squared sides are `30976,16384,16384` (ratio `22:16:16`) and the model tile's are `{256,576,1024}` (ratio `2:3:4`), matching the paper's shapes exactly. Clause 2: `exists_dissection_44_mul_sq` composes `dissection` with `Ladder.ladder` to get a `CongruentDissection (44*m^2)` for every `m ≥ 1`. Checked against erdos-634.tex:1943-1947 word for word before flipping (Rule 5) — see `private/RESEARCH_LOG.md` 2026-09-02 entries for the full derivation. |
| M `thm:main` | prime `N ≡ 3 (mod 4)` that is not a base-β candidate is excluded | `BaseBetaMod12.*` and the branch theorems | PROVED — the top-level classification; it inherits every blocker below it and is the paper's own statement of what rests on cited inputs |

## Blockers named, obstructions note (2026-08-30, debt pass 3)

| Paper | Statement | Lean declaration | Blocker |
|---|---|---|---|
| O `lem:endpoints` | the last edge's top angle is `α`, the first edge's bottom angle is `β` | `TileAt.congruentDissection_endpoints`, `WallEndpoints.chain_endpoints`, `TileAt.congruentDissection_base_corner_counts`, `.congruentDissection_apex_counts` | **VERIFIED 2026-09-02** — closed in full, for a real `CongruentDissection`. `WallEndpoints.chain_endpoints` proves the sorted boundary chain's first entry has the base corner as one of its own vertices and its last entry has the apex as one of its own vertices (a genuine covering-completeness argument: `WallEdges.base_covered_by_wall_edges` + a global-extremum argument + `WallInjective.shadows_disjoint` to pin the index). `TileAt.congruentDissection_endpoints` composes this with `.congruentDissection_base_corner_counts`/`.apex_counts` (2026-09-02, earlier this session) and `CongruentAngles.congruent_corner_angles`: the chain's first tile has the base corner as its own vertex, so its local angle there is a definite corner angle in `{α,β,γ}`, and the count (exactly one `β`-tile, zero `α`/`γ`) eliminates the other two by contradiction. Mirror argument at the apex gives `α`. `lake build Erdos634.All` clean, no `sorry`. Paper's own `\lab{}` tag flipped to match (was `PROVED`) |
| O `prop:straddle` | every junction chord is straddled | `StraddleBound.*`, `ChordDecomp.*` | PROVED — needs chords of a target and the tiles meeting them: a **tile-placement layer** plus a notion of a chord's cover |
| O `prop:straddlegen` | the area above any interior junction chord is never integral | `ChordDecomp.area_never_integral`, `.coprime_tight` | PROVED — the area arithmetic is VERIFIED; the geometric clause — that this is the area above a chord *of a tiling* — needs the placement layer |
| O `prop:chorddecomp` | the chord decomposition at the last junction of `(3,7)` | `ChordDecomp.flush_classification` | PROVED — the classification is VERIFIED at the arithmetic level; identifying `𝒰` as the set of tiles meeting a chord needs the placement layer |
| O `lem:ccornerside` | a `c`-corner carries a side `a`-edge, so `1 ≤ p ≤ (f−1)/e` | `TilePlacement.c_corner_side_a`, `.a_corner_side_c`, `.p_bounds`, `.p_le_of_bounds`, `SideNoB.side_quantized` | PROVED — the flank implication and the parameter bounds are both VERIFIED. The one step between them is not: that a side's chain edges are its walk counts, so that an `a`-edge on the side makes `P' > 0`. That chain-to-walk dictionary is now `ChainWalk.chain_walk`; `SideWall.side_walk` instantiates it at the side; what remains is identifying the corner tile's base edge as the chain's first entry |
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
| C `thm:walks` | the boundary walks of the base-β target | `BaseBetaWalks.*`, `WalkEquation.walk_equation` | PROVED — the walk equation is VERIFIED; enumerating the *boundary* walks of a tiling needs the edge chain on all three sides — bridge (c) at that side, which `SideWall.side_chain_junctions` supplies; and `SideWall.side_junction_frontier_nonvertex` supplies the frontier and non-vertex inputs there. **Note 2026-09-02 (second pass)**: `SideWalk.side_walk_of_dissection` (new) now proves the mixed `a`/`b`/`c`-letter walk equation directly for a real side — `dist a b = P'·a + Q'·b + R'·c` with `P'`,`Q'`,`R'` the real edge-type counts, via `chain_endpoints` + `EdgeType.exists_matching_side` + one new calibration fact (`hiso`: `dir` measures real distance along the wall line — a hypothesis, true for the natural choice of `dir` but not derivable from `hker` alone). This IS the connection the row's own gap names. What remains for the full closure: bridging this real-number equation to the `ℤ`-typed arithmetic in `BaseBetaWalkArith.lean` (`equal_side_no_b` etc.), which needs the target's specific numeric side length instantiated (`f³` or `e(3f²−e²)`) and a cast argument — a further, separate, but now well-scoped piece. |
| C `thm:pierce` | apex mismatch: the pierced corner | `ApexRigidity.*` | PROVED — needs tiles laid at the apex and their edges; **tile-placement layer** |
| C `prop:rung2` | the pre-piercer chain | `ApexRigidity.*`, `CChord.*` | PROVED — same placement layer, on the configuration of `thm:pierce` |
| C `thm:ray` | the mismatch ray is completely determined | `ApexRay.*`, `PinRay.*` | PROVED — the ray arithmetic is available; 'along the ray' quantifies over the tiles it meets — placement layer |
| C `thm:chain` | the `b`-run orientation lemma | `Inflation.orient_monotone`, `RunOrientation.*` | PROVED — the alphabet lemmas are VERIFIED. **Note 2026-09-02**: `BEdgeReading.side_word_constant` (new) closes the boundary-to-word passage for this row specifically — same technique as `AEdgeReading.side_word_monotone` (`prop:orientmono`'s row), but for `b`-edges (`α`,`γ` endpoints via `EdgeType.b_edge_endpoints`, not `β`,`γ`) and using `OrientWord.corner_anchored_word`/`RunOrientation.corner_anchored_run_all_BG` for the CONSTANT conclusion this row actually needs (thm:chain says the whole run is uniformly `BG`, seeded at the apex tile — stronger than mere monotonicity). Unconditional except the standard wall/line setup, real corner angles, and the seed hypothesis (the first tile presents `α` at its own west end — the paper's own "seeded at an apex tile"). Not closed: needs the same concrete numeric realization as `thm:walkstruct` (a `CongruentDissection` witness) to instantiate. |
| C `thm:farregion` | the far region is a scaled tile | `ApexRigidity.*`, `ConeScaling.*` | PROVED — needs the region cut off by a wall as an object. **Note 2026-09-02**: `SubDissection.restrict` (new) now supplies the sub-region *object* (a real `Dissection`/`CongruentDissection` of any tile subset whose union equals a given triangle) — the bookkeeping obstacle this row's note names is gone. What remains, row-specific: proving that the far region cut off by a wall actually *is* such a union of tiles (the covering-equality hypothesis `restrict` still needs) — real geometric content, not yet built. |
| C `cor:farvacuous` | the far side gives no contradiction | `ApexRigidity.*` | PROVED — conditional on `thm:farregion`; same blocker, now the same partial closure (`SubDissection.restrict` supplies the object; the covering-equality for this specific region is not yet built) |
| C `thm:e1reduce` | the `e=1` base walk is a permutation of `(a^f, b, c)` | `BaseCountsE1.base_counts`, `.base_counts_corner` | PROVED — the counts `n_b = 1` and the exclusion of `n_c = 2` are VERIFIED; `n_c ≥ 1` is `prop:gammatrap`, **now VERIFIED itself (2026-09-02, `GammaTrap.congruentDissection_gammatrap`)** — what still blocks this row is instantiating it at this specific walk's side, not an open geometric input |
| C `lem:filler` | the filler identity and the strip tiling | `W2Core.*` | PROVED — the two identities are VERIFIED and axiom-free; 'the column and its fillers tile the strip' needs the placement layer |
| C `lem:offsets` | the offset congruence `Σεᵢ − j = −2q` | none | PROVED — the congruence is elementary and formalizable; what it is *about* — the terminal column's base apex — has no Lean definition |
| C `lem:anglecalc` | the five vertex-figure facts: no right angle, apex, base corner, γ-trap, `α+β` wedge | `AngleArithmetic.no_right_angle`, `TileAt.congruentDissection_apex_counts`, `.congruentDissection_base_corner_counts`, `.congruentDissection_boundary_figure_cases` | PROVED — **downgraded from VERIFIED 2026-09-02: the previous citation overclaimed.** It cited `TilePlacement.base_corner_counts`/`.apex_counts`, `VertexFigureReal.apex_figure_real`/`.base_corner_figure`, but every one of those takes `hvals`/`hsum` — "every tile's local angle here is one of `α,β,γ,π,0`" — as a *hypothesis*; grepped the corpus, nothing had ever discharged it for a real dissection (the same bug class as the ten wrong VERIFIED labels of the 2026-08-30 audit, and `prop:cornerfig`'s citation gap closed earlier tonight). Fixed by citing real derivations instead. Clause (1) is pure arithmetic, unaffected. Clauses (2) apex and (3) base corner now hold of a genuine `CongruentDissection` at the target's own vertices, via `TileAt.congruentDissection_apex_counts`/`.congruentDissection_base_corner_counts` (pre-existing, from tonight's `lem:census` work). Clause (4) γ-trap — a *general* straight-angle boundary point, not a target vertex — is closed by `TileAt.congruentDissection_boundary_figure_cases`, composing `congruentDissection_hcorners` (a sibling addition landed the same night, independently deriving the same corner-angle fact used inline by `.congruentDissection_no_double_gamma`) with `VertexFigureReal.localAngle_mem`/`.boundary_multiplicities_cards`/`.boundary_figure_cases` (pre-existing, previously never fed a real `hcorners`/`hvals` anywhere else in the corpus). It proves the real trichotomy — one tile presenting a straight angle alone, or exactly `{3α,2β}`, or exactly `{α,β,γ}` — at *any* frontier point of a real `CongruentDissection` that is not a target vertex; this is also exactly the `hvals` hypothesis `MarchRun.junction_dichotomy` and `VertexFigureReal.gamma_boundary_figure_real` (`rem:marchobl`'s M-i/M-vertex rows) still carry, now suppliable for a real dissection though not yet threaded into those call sites. **Residual, honestly**: the trichotomy's first branch (a single tile spanning the point with no other tile touching it) is a case the paper's clause (4) does not name, so matching "the only figures are..." literally still needs that case excluded — not done; clause (5), the `(1,1)` wedge, is untouched — no point of the corpus is identified with it. Label stays PROVED, not VERIFIED, until those two gaps close |
| C `rem:norightangle` | no piece of any dissection has a right angle | `AngleArithmetic.no_right_angle`, `CongruentAngles.congruent_corner_angles` | PROVED — needs the piece's angles identified with the tile's, which congruence gives, and that composition is not written |
| C `prop:gammagrading` | every edge direction is an integer multiple of `γ` mod `π` | `DirectionGroup.*`, `Dissection.Dir` | PROVED — needs edge directions of a dissection as a group; `Dissection.dirSet` exists but the grading is not developed |
| C `prop:dirgroup` | the direction group of a branch | `DirectionGroup.*` | PROVED — same development |
| C `lem:termwedge` | the terminal wedge decomposes as `γ + α + β` | `AngleArithmetic.*`, `VertexFigureReal.boundary_figure_cases` | PROVED — the figure is now reachable at a real boundary point; the column terminating at a base vertex is a placement statement |
| C `lem:sidenob` | the equal sides carry no `b`-edge | `SideNoB.side_no_b_uncond`, `.side_no_b_e_one` | VERIFIED — the walk arithmetic is VERIFIED; 'every side walk' presupposes the side's edge chain — bridge (c) on the equal sides |
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
| C `lem:monochotomy` | the thick-member monochotomy for `c` | `c_chord_unique_thick`, `CChord.*` | VERIFIED — the decomposition arithmetic is VERIFIED; the lemma also asserts which decomposition a *tiling* realises |

## Blockers named, companion part 2 (2026-08-30, debt pass 5)

| Paper | Statement | Lean declaration | Blocker |
|---|---|---|---|
| C `thm:walkstruct` | the walk structure at `m=1` | `equal_side_no_b`, `equal_side_shape`, `base_b_count` | PROVED — the walk arithmetic is VERIFIED. **Note 2026-09-02 (fifth pass)**: all three `ℤ`-typed arithmetic theorems now have a `_of_gammatrap` counterpart in `SideWalk.lean` connecting them to a real dissection — `equal_side_no_b_of_gammatrap` (clause (i), `Qc=0`), `base_b_count_of_gammatrap` (the base's `n_b=e`, feeding `cor:wallsf2e`), `equal_side_shape_of_gammatrap` (`n_c=f-k·e` given `n_a=f·k`, derived via `f₀∣Pc` from the walk equation itself and coprimality). In every case, `GammaTrap.congruentDissection_gammatrap` (VERIFIED) supplies the `c`-edge witness unconditionally — no more `hnc1` hypothesis anywhere in this chain. **The one genuinely remaining gap, shared by all three**: `hA`,`hB`,`hC`,`hLen` — a concrete numeric realization (an actual `CongruentDissection` whose model has sides `ef,f²-e²,f²` and whose target's side `k` has the right length). `IsoTri.isoTri`/`SssTri.sssTri` (new, general-purpose `Tri`-from-side-lengths constructors, first in this project) build the individual triangles; a full `CongruentDissection` needs `N` tiles actually covering the target — a trivial `N=1` witness is impossible (the model is scalene, the target isosceles) — this is unavoidably the placement layer, structural blocker 1. This is the closest any row got to a real closure this session, and the pattern (wire the already-VERIFIED `gammatrap` through `chain_endpoints`'s surjectivity into any walk-equation arithmetic theorem) is now proven out and mechanically repeatable. |
| C `lem:pentagon` | the middle region of `(0,e,2e)` admits no tiling | `Pentagon.no_partition` | PROVED — 'admits no tiling' quantifies over dissections of a **non-triangular region**, for which there is no Lean notion |
| C `lem:anglethreshold` | the closed forms for `cos α`, `cos β`, `cos γ`, and (P4) | `Frontier.cos_alpha_closed` | VERIFIED — one of the three cosines is a verified identity; the other two are unformalized and (P4) is a property of the search's uncovered region, which has no Lean notion |
| C `lem:basetri` | the thick base trichotomy | `base_trichotomy` | VERIFIED — the three decompositions are VERIFIED arithmetic; that a tiling realises one of them needs the base edge chain |
| C `lem:shadow` | the shadow at a `c`-corner | `SideNoB.c_corner_forces_side_a` | PROVED — **tile-placement layer**: 'lays `c` on the base, mirrored, `a`-edge first'. **Circularity fixed 2026-09-02**: the theorem previously assumed `1 ≤ p` as a hypothesis while claiming to derive it; it now derives `p ≥ 1` from `0 < f·p`, which is still not connected to a real tiling — the placement-layer blocker stands
| C `lem:basedi` | the thick base dichotomy | `base_dichotomy_thick` | PROVED — the arithmetic is VERIFIED; it consumes `prop:gammatrap`, **now VERIFIED (2026-09-02)** — what still blocks this row is instantiating it at this dichotomy's real side, not an open geometric input |
| C `cor:basedi2e` | the trichotomy and dichotomy without separation | `base_dichotomy_thick`, `no_extra_column_of_f_gt_two_e` | PROVED — same, plus the column exclusion |
| C `lem:anchorclear` | blocked-end quantization | `CChord.*`, `Collar.*` | PROVED — needs a tile edge whose extension is blocked — a placement statement about the ambient tiling |
| C `cor:onebloc` | the one-end-blocked chord dichotomy | `CChord.c_chord_dichotomy` | PROVED — the dichotomy is VERIFIED arithmetic; 'the far side of the chord' is a placement statement |
| C `cor:wallsf2e` | the base walk is the walls form `(f,1,1)` at `e=1` | `SideNoB.side_no_b_uncond`, `.side_quantized`, `BaseCountsE1.base_counts_corner` | PROVED — `n_b = 1` and the exclusion of `n_c = 2` are now VERIFIED; `n_c ≥ 1` remains, as for `thm:e1reduce` |
| C `thm:apexconfig` | the first chord is covered exactly | `ApexRigidity.middle_fraction`, `.area_above_chord` | PROVED — the fractions are VERIFIED; the three tiles at the apex are a placement configuration |
| C `cor:noTP` | the tile below `T₁`'s `a`-edge has no `T`-junction | `PinLemma.no_through_tile` | PROVED — same apex configuration |
| C `thm:secondc` | the second edge of an equal side is a `c` | `SecondEdge.admissible_ends_alpha` | PROVED — the endpoint arithmetic is VERIFIED; 'the edge immediately after' presupposes the side's ordered chain |
| C `prop:nogolden` | the golden-ratio hypothesis is removable | `ApexRigidity.b_gt_f`, `eb_gt_a`, `e_ge_two_of_b_lt_a` | PROVED — the inequalities are VERIFIED; the statement is about `thm:secondc`, so it inherits that blocker |
| C `cor:pbound` | `n_c ≥ 2`, hence `pe + 2 ≤ f` | `ApexRigidity.side_p_bound` | PROVED — the implication is VERIFIED; `n_c ≥ 2` comes from `prop:gammatrap` (**now VERIFIED, 2026-09-02**) plus the apex `c`-edge, which is still open |
| C `lem:onegamma` | a single `γ` never excludes a `T`-junction | `SecondEdge.at_most_one_straight` | VERIFIED — the count is VERIFIED; 'an interior point at which one tile presents `γ`' now has `VertexFigureReal.interior_figure_cases` behind it, but the `T`-junction itself is a placement notion |
| C `thm:aforcesT` | an `a`-edge forces a `T`-junction | `SecondEdge.*` | PROVED — same `T`-junction notion |
| C `prop:inflbdy` | the inflated boundary | `Inflation.*` | PROVED — needs the inflated tile's dissection, i.e. the **scale map on dissections** |
| C `cor:inflcrux` | the crux, on `f²` tiles | `Inflation.*` | PROVED — same scale map |
| C `prop:inflparity` | edge parity kills the `p=1` boundary | `Inflation.*` | PROVED — same scale map, plus an edge-to-edge hypothesis with no Lean definition |
| C `prop:orientmono` | the orientation of a boundary `a`-run is monotone, **on the inflated tile's side** (companion `prop:orientmono`, distinct from the already-VERIFIED `prop:orientmonobdy` on the *target's own* side — the latter's proof explicitly needs no boundary-to-word passage) | `Inflation.BG_GB_forbidden`, `.orient_monotone`, `.AAB_iff_transition` | PROVED — the alphabet lemmas are VERIFIED. **Note updated 2026-09-02 (fourth pass)**: `AEdgeReading.side_word_monotone` (new) now closes the boundary-to-word-to-monotone passage **unconditionally**, for a whole `a`-side of *any* `CongruentDissection`, using only the standard wall/line setup (`hker`,`hwall`,`hbase`,`hline`,`hface`,`hthird`,`hvertt`,`hdirab` — all already accepted unconditionally elsewhere in this project's bridge (c)) plus `hlen` (the whole side is `a`-edges). Junction incidence, distinct-tile, and non-vertex-frontier facts are all *derived*, from `WallEndpoints.chain_endpoints`, `WallSide.wall_edges_same_tile` and `BridgeC.junction_frontier_nonvertex` — no remaining unbuilt hypothesis for that passage. **What still blocks `prop:orientmono` itself**: the theorem must be instantiated with `D`'s `target` equal to the *inflated tile*, not the ambient target — i.e. with a `CongruentDissection` object built by *restricting* a real dissection to the subset of tiles filling one occurrence `Δ_k`. **Note 2026-09-02**: `SubDissection.restrictCongruent` (new) now builds exactly that restriction, mechanically, given a covering-equality hypothesis — the same tool now shared with `thm:farregion`/`cor:farvacuous`. Establishing the covering-equality hypothesis itself (that a specific tile subset really does fill one occurrence `Δ_k`) is the actual content of "occurrence" theory in `\sub{sub:forcedrow}` and is genuinely unbuilt — confirmed, not assumed. Not closed, but the boundary-to-word passage AND the restriction bookkeeping are now both complete and general; only the covering-equality witness remains, row by row. |
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

| O `prop:testsuniform` | every test the search performs answers the same at every member | `MemberUniform.fill_iff_counts`, `.fillable_iff_member`, `.unfillable_iff_member`, `.gap_one_uniform`, `.tests_uniform` | VERIFIED — corner fillability factors through `(X,Y)` and names no `f`; the residue-`1` and `|a−b|` tests answer no at every member |
| O `prop:findep` | the `cp = bp−1` refutation is identical at every `f` | `MemberUniform.tests_uniform` | HEURISTIC — the node counts are measured. The *mechanism* is VERIFIED: no test the search performs distinguishes members. What is not proved is that the search performs only those tests, which is a property of the engine |

### Fast-vein audit of the six `PROVED: … VERIFIED` labels (2026-08-31)

Of the six statements whose label admitted a verified core, exactly one was reachable; the other
five have blockers that are layers, not lemmas. Recorded so they are not re-attempted:

| Paper | Why it is not fast-vein |
|---|---|
| M `prop:vertexfigures` | **upgraded to VERIFIED** — the gap was one missing case (`s ≥ 1` interior), now `interior_figure_cases_gen` |
| C `lem:census` | `OrderForcing.vertex_census` takes the three corner-balance equations as *hypotheses*. Deriving them from a real dissection is a global double count — every tile corner sits at a vertex, every vertex classified — which is the **tile-placement/incidence layer**. Not one lemma |
| C `lem:parity` | inherits the above: its hypothesis is the census α-identity |
| C `lem:charge` | direct-vs-mirrored cover pieces and feet displaced by `1/f`: **placement layer** |
| C `prop:orientmono` | passage from a real boundary run to its word: **bridge (c) beyond the base** |
| M `thm:walkstruct` | side words of a real tiling: **bridge (c) beyond the base** |

| C `lem:anglethreshold` | the tile's three cosines | `AngleThreshold.cos_of_sides`, `.cos_alpha_closed`, `.cos_beta_closed`, `.cos_gamma_closed` | VERIFIED — `cos_of_sides` solves Mathlib's `EuclideanGeometry.law_cos`, so these are statements about `cornerAngle`, not about the law-of-cosines quotient. `Frontier.cos_alpha_closed` was the cross-multiplied polynomial identity only, and `cos β`, `cos γ` were absent |
| C `rem:anglethreshold` | what condition (P4) compares against | none | PROVED — split off `lem:anglethreshold` on 2026-08-31: the uncovered region is not an object of the Lean development |

### Batch of 2026-08-31 (the `VertexFigureReal` consequences)

| Paper | Statement | Lean declaration | Status and blocker |
|---|---|---|---|
| C `lem:onegamma` | a single `γ` never excludes a `T`-junction | `VertexFigureReal.interior_multiplicities_cards`, `.one_gamma`, `.one_gamma_real` | VERIFIED — `one_gamma_real` is the paper's statement at a real interior point of a `Dissection`: the two hypotheses are witnessed by named tiles (one presenting `γ`, one with `v` interior to an edge), and the conclusion is that the counts are one each of `α, β, γ, π` and no covering tile. `interior_multiplicities_real` could not be used directly — it hides the counts behind an existential, losing the link to a particular tile; `interior_multiplicities_cards` names them |
| M `cor:figureP` | the figure at `P` on that side is fully determined | `VertexFigureReal.one_gamma_real` | PROVED — the forced figure `γ + π + β + α = 2π` and "no other distribution is possible" **are** now `one_gamma_real`. What remains is the identification: that `P` lies at distance `b < c` from `A` hence interior to the edge, that `T₂` is the straight tile there, that `Y` is the tile below `T₁`'s `a`-edge. That is the **tile-placement layer**, and splitting it off would leave the corollary without its content |
| C `lem:climberdetect` | climbers detect deviation | `OrderForcing.*`, `VertexFigureReal.interior_figure_cases` | PROVED — the `(2,2,2)` figure is reachable, but "an interior lattice point of the brick/mate structure" and "the six incident tiles are the brick/mate six" need the **brick/mate structure**, which has no Lean definition |
| C `lem:termwedge` | terminal wedge | `AngleArithmetic.*`, `VertexFigureReal.boundary_figure_cases` | PROVED — the boundary figure is reachable, but a base-reaching **column**, its anchor offset `x₀`, its last filler and last column tile are placement notions with no Lean definition |

### Batch of 2026-08-31 (second)

| Paper | Statement | Lean declaration | Status and blocker |
|---|---|---|---|
| C `lem:fillerid` | the two filler identities, general in `f` | `FillerGeneral.filler_b_general`, `.filler_c_general`, `.filler_consistent` | VERIFIED — **and this corrects an overclaim**: the paper said "both identities in `f` … machine-checked in `lean/W2Core.lean`", but `W2Core` is deliberately import-free (`decide`/`omega` only) and proves the load-bearing identity *per member* (`filler_b_f3`, `_f4`, `_f6`, `_f8`, `_f12`) — its own header says "kernel-checked per member". The general identity did not exist until now. Kept out of `W2Core` to preserve that file's no-import property |
| C `lem:filler` | the column and its fillers tile the inter-level strip | none | PROVED — split off `lem:fillerid` on 2026-08-31; the strip, the column and its fillers have no Lean definition |
| M `cor:pbound` | `n_c ≥ 2`, hence `pe + 2 ≤ f` | `ApexRigidity.side_p_bound`, `.p_le_one_of_tight` | PROVED — **not split, deliberately**. The implication `n + pe = f ∧ 2 ≤ n → pe + 2 ≤ f` and the tight-subfamily consequence `p ≤ 1` are already VERIFIED declarations and already recorded here. The corollary's own content is the *unconditional* `n_c ≥ 2`, which comes from `prop:gammatrap` (**now VERIFIED, 2026-09-02**) plus the apex figure, which is still open. Splitting the conditional off would add a VERIFIED row carrying no new content — count-gaming, not debt clearance |
| C `lem:ccornerside` | a `c`-corner carries a side `a`-edge | `TilePlacement.c_corner_side_a`, `.a_corner_side_c`, `.p_bounds` | PROVED — the paper says what remains, in its own text: excluding `1 ≤ p ≤ (f−1)/e` for `e ≥ 2` "is the analogue of the entire `e=1` programme rather than a single lemma". Not fast-vein by the author's own account |
| C `cor:wallsf2e` | the base walk is the walls form `(f,1,1)` at `e=1`, `f≥3` | `SideNoB.side_no_b_uncond`, `.side_quantized`, `BaseCountsE1.*` | PROVED — `n_b = 1` and the exclusion of `n_c = 2` are VERIFIED, but "the base walk" of a real tiling is bridge (c). **Note 2026-09-02**: same connection now available via `SideWalk.side_walk_of_dissection` (see `thm:walkstruct` row); not yet composed here. |

### Map integrity: the label column means the *statement* (2026-08-31)

An audit comparing every row's label against the papers' own `\lab{}` found **19 statements with
contradictory rows** — an early row saying VERIFIED and a later one PROVED. The cause is structural,
not clerical: the early sections were labelling the *cited declarations*, the debt sections the
*statement*. That is the ingredient-for-statement error, embedded in the document rather than in a
single row.

All 19 are now set to the papers' label, with "(cited declarations VERIFIED)" kept where the
declarations really are verified. **The label column means the statement, as written, is the Lean
theorem — never that its ingredients are.** The papers' `\lab{}` is the source of truth; the census
is computed from them, not from this file.

Also corrected: `prop:cornerfig` and `prop:vertexfigures` rows still read PROVED after the papers
moved them to VERIFIED; `thm:fullprime` and `thm:realize12` rows read PROVED where the papers say
CONJECTURE — the map overclaiming against the papers.

| Paper | Statement | Lean declaration | Status and blocker |
|---|---|---|---|
| C R2/R3/R5 (`Rigidity.lean`) | junction residue; apex integrality dichotomy; interior-multiple | `RigidityGeneral.junction_residue`, `.junction_residue_dvd`, `.apex_bg_dead`, `.apex_gb_offset`, `.b_hits_lattice` | VERIFIED for **every** `f`. `Rigidity.lean` is import-free by design and kernel-checks these per member (`f = 2,3,4,6,8,9,12`); its header records the gap — "the general-`f` statements are two-line ring identities plus `f ∤ 1` … the members kernel-checked below cover every instance in current play". Now general, kept in a separate file so `Rigidity.lean` stays import-free |
| M `thm:lattice` | the spectrum lattice with the parity switch `T` | none | PROVED — **citation corrected (2026-08-31)**: this row cited `SurplusLattice.lattice_12`, `.lattice_13`, which are about the base-`β` *relation* lattice (and are anyway subsumed by `prop:rellattice`, VERIFIED and general). `thm:lattice` is the base-`α` spectrum for `120°`-triples with `d`, `e₁`, `r` and the parity switch; no declaration corresponds to it |

| C `prop:relfloor` | a nonzero relation has one-sided length `≥ f·min(a,b)` | `InterfaceFloor.interface_floor`, `.oneSided`, `.oneSided_eq_neg`, `.floor_attained`, `.v1_relation`, `.v1_nonzero` | VERIFIED — split off `prop:interfacefloor` on 2026-08-31. The blocker recorded here read "the length bound is arithmetic and not yet proved"; it is now proved. Case split on `n_b`: if `n_b ≠ 0` then `f ∣ n_b` (`rel_b_mult`) forces `|n_b| ≥ f` and that side already measures `≥ f·b`; if `n_b = 0` the relation is a multiple of `v₁` (`rel_param`) and either side measures `|s|·f·a ≥ f·a`. `oneSided_eq_neg` is what lets the two sides be compared — the positive and negative parts of a relation have equal length. Sharp: `v₁` attains it |
| C `prop:interfacefloor` | short interfaces carry the same multiset on both sides | none | PROVED — the remaining clause after the split; maximal straight interfaces of a dissection are not objects of the development |

| M `prop:conicequiv` | the conic condition and the `16N²` factorization are the same condition | `EquilateralConic.factor_2pi3_iff`, `.factor_2pi3_conv`, `.conic_pi3_iff` | VERIFIED — split off `prop:conicform` on 2026-08-31. The blocker recorded here read "the equivalence needs the converse direction": `qs_sq`, `conic_2pi3` and `factor_2pi3` all ran from the invariant counts *to* the factorization, and the return trip did not exist. `factor_2pi3_conv` supplies it — multiply by `s²` and use `ts = 3N` to get `s²((t−s)²+16N) = s⁴+10Ns²+9N² = (qs)²`, then cancel `s ≠ 0`. The `π/3` companion was already a ring identity, so `conic_pi3_iff` is immediate |
| M `prop:conicform` | a `2π/3` tile *requires* such a factorization | `EquilateralConic.*` | PROVED — the remaining clause after the split. "Requires" is necessity from a tiling: that a tiling yields integers `s,t,q` of the stated parities is `prop:eqspecint`, which quantifies over tilings |

| C `rem:norightangle` | no piece of any dissection has a right angle | `NoRightAngle.angles_ne_pi_div_two`, `.no_right_angle_of_congruent`, `.no_piece_has_right_angle` | VERIFIED — the blocker read "needs the piece's angles identified with the tile's, which congruence gives, and that composition is not written". It is written now. `AngleArithmetic.no_right_angle`'s own docstring disclaimed being the geometric statement; `Geometry.congruent_corner_angles` supplied the missing half. `angles_ne_pi_div_two` also removes the appeal to "clause (1)": `α`, `β` and `γ` all avoid `π/2` for the single reason that `α ∉ ℚπ`, since `β = π/2` and `γ = π/2` each force `α = 0 = 0·π`. **Scope**: what is proved is that no triangle congruent to the tile has a corner angle `π/2`. The remark's two trailing glosses — that the target cannot be split along its altitude, and that no perpendicular cut is available — are consequences stated in prose and are not separately formalized |

| M `prop:latticeparam` | the two admissibility conditions reduce to `uT ≡ 0 (mod 2)` | `SpectrumLattice.dvd_iff_e1_dvd`, `.parity_iff`, `.admissible_iff`, `.case_split`, `.sq_self` | VERIFIED — the blocker on `thm:lattice` read "the general statement needs the `d`, `e₁`, `r` normalisation formalized and the parity case split, which is arithmetic and simply not done". Both are done. The normalisation is taken as hypotheses (`e = g·e₁`, `r = g·r₁`, `e₁` and `r₁` coprime), which is what `g = gcd(e,r)` provides and avoids truncated `ℕ` division; the quotient `wr/e` likewise comes from `e·q = w·r` rather than from `/`. The parity step is done in `ZMod 2`, where `u² = u` collapses `N` to `u·d·e₁²·(a+2b)` |
| M `thm:lattice` | the admissible counts are exactly `N = d(Eu)²(a+2b)` | `SpectrumLattice.*` | PROVED — **gap (i) closed 2026-09-02**: `SpectrumLattice.admissible_set_eq` assembles `dvd_iff_e1_dvd`, `parity_iff`, `case_split` into the actual set equality — the positive `w` satisfying both admissibility clauses (`e ∣ w·r` and `w·r/e ≡ N (mod 2)`, stated arithmetically, not over tilings) equal exactly the positive multiples of `E`, with `E = e₁` or `2e₁` read off `T`'s parity by an explicit `if`. What remains is only gap (ii): the word "admissible" routes through `thm:admissible` and quantifies over tilings, which `admissible_set_eq` does not — it is a theorem about the two named arithmetic clauses, not about a real dissection. Label unchanged (PROVED, not VERIFIED): gap (ii) alone still blocks it |

## The fast vein is exhausted (2026-08-31)

Every one of the 123 PROVED statements was classified against its blocker. None is now "one lemma
short". The distribution:

| Count | Blocker |
|---|---|
| 33 | tile-placement layer |
| 16 | another missing object (lattice, chain, region, ladder, grading, shape table, strip, interfaces) |
| 13 | assembles or inherits from others; blocked by the weakest |
| 10 | certified-search format |
| 10 | quantifies over tilings / needs a `Dissection`-level statement |
| 8 | bridge (c): words from a real boundary |
| 6 | scale map or composition on dissections |
| 3 | a finite check, formalizable but not transcribed |
| 1 | never formalizable |

The four recurring blockers named in `CLAUDE.md` account for 57 of them directly, and most of the
rest reduce to one of the four through an assembly chain.

**What was taken out of the vein**, over the passes of 2026-08-31 — each because the paper statement,
as written, became the Lean theorem: `prop:vertexfigures` (the interior figure with straight angles,
`s ≥ 1`, was never proved — only its `s = 0` instance); `lem:anglethreshold` → `lem:fillerid` split
plus `cos β`, `cos γ` via `law_cos`; `lem:onegamma` (needed the counts named, not existential);
`lem:fillerid` (the identities were per-member, the paper claimed general); `prop:relfloor` (the
length bound, genuinely unproved); `prop:conicequiv` (the converse direction did not exist);
`rem:norightangle` (a congruence composition the corpus's own docstring flagged as unwritten);
`prop:latticeparam` (the normalisation and parity case split).

**The one remaining non-layer vein** is transcription of finite checks, which is a different kind of
work and larger than it looks: `prop:globalsys` (an exhibited solution set at `N=11`),
`prop:nogoauto` (a finite check over the automaton), `prop:nogocensus` (linear algebra over the
census). None is "one lemma short"; each is a computation to be certified, and the project has no
certified-search format — the same blocker as the other 10.

### `rem:marchobl`'s obligations (2026-08-31)

`rem:marchobl` is OPEN. Its three obligations are tracked here as sub-atoms so the debt is visible.

| Atom | Statement | Lean declaration | Label |
|---|---|---|---|
| M-vertex | a `γ` at a straight-edge point forces the figure `{α,β,γ}` | `VertexFigureReal.gamma_boundary_figure_real`, `.boundary_multiplicities_cards` | VERIFIED |
| M-wedge | the march step at a real junction: opening `α`, two placements | `JunctionWedge.march_junction_real` | VERIFIED |
| M-i | the march's steps land on such vertices | `MarchRun.junction_dichotomy`, `.gamma_of_not_exceptional`, `.all_but_one_is_march_junction` | PROVED ⭐ — reduced to `prop:orientmono`; residual blocker bridge (c) |
| M-coord | apex offsets `dGB`, `dBG`; common apex height | `MarchCoords.gb_left`, `.gb_right`, `.bg_left`, `.bg_right`, `.apex_height_common` | VERIFIED |
| M-chir | chirality = the `a`-tiles' orientation, swapping `b` and `c` | `MarchCoords.offsets_complementary`, `.junction_to_apex_bg`, `.junction_to_apex_gb`, `.chirality_swaps_sides` | VERIFIED |
| M-trans | transition spacing `(3f²-1)/f` is never a tile side | `MarchCoords.spacing_same`, `.spacing_gb_bg`, `.transition_not_a_side` | VERIFIED |
| M-forced | the filler is forced; its sides are `{a,b,c}` | `MarchCoords.filler_forced`, `.filler_congruent_bg`, `.filler_congruent_gb` | VERIFIED |
| M-ii | the two chiralities advance by exactly one and two positions | none | HEURISTIC — measured from the engine trace (`CENGINE_TRACE=1`) at `bp=6,7`, `f=12`: exactly two children at the first branch, one carrying `a(bp-2)` verbatim and the other `a(bp-1)-3`. The `(7,6)` decomposition was **pre-registered** in `private/PREREG_march_decomp.md` and confirmed exactly. Proof still needs the run-wide configuration forcing |
| M-iii | both advances reduce to the same problem at smaller `bp` | none | HEURISTIC — same trace: child `0`'s subtree **is** the smaller refutation node-for-node, child `1`'s is it less three shared spine nodes |

`MarchCoords` is the project's first coordinate model of a run. `dBG = (3f²-1)/(2f)` is
`Rigidity`'s `x_w` and equals `c·cos β` for the closed form of `lem:anglethreshold`, which is two
independent checks that the model is the right one.

### Reproducibility defect (Rule 9) -- RETRACTED 2026-08-31

**This entry was wrong and is retracted.** All five binaries are built from `cengine_iso.cpp`,
which is committed; the binary name differs from the source name, and the search behind the original
entry looked for `*rx2*.cpp`. Rebuilding `cengine_rx2` from committed source reproduces the shipped
binary byte-for-byte (293800) and returns the logged verdict and node count on a settled instance.
The member certifications are reproducible. The build recipe, which genuinely was missing, is now
`code/engine/BUILD.md`.

### N = 1451 certified (2026-08-31), and a methodological finding

`verify_sweep.py 22` returns **PASS at both reach 3 and reach 4**: 168 of 168 orbits exhausted.
`N = 1451` (`e=1`, `f=22`) joins the certified members. Logs: `runrx22.log`, `f22_fix.log`,
`f22_m13c5.log`, `f22_m13c2.log`.

**Search cost is direction-dependent, and the sweep ran only one representative per orbit.** The
two orbits that held the sweep up, `{(12,20),(13,5)}` and `{(12,23),(13,2)}`, were being attacked
through their `bp = 12` representatives, which consumed 869 and 928 CPU-minutes without finishing —
against a typical orbit's 15 minutes. Their mirrors `(13,5)` and `(13,2)` exhausted in about seven
minutes each, at 73672 and 62253 nodes: four orders of magnitude cheaper. `/tmp/f22.txt` listed only
`bp ≤ 12`, so the cheap representative was never tried.

`verify_sweep.py` has always credited an orbit when "the word **or its mirror**" is exhausted, so
this was available from the start. The sweep runner should try both representatives, or the cheaper
one first; doing so would have saved roughly 30 CPU-hours on `f=22` alone. This is a property of the
search's direction, not of the orbit.

| M-derived | the fillers form a new `a`-run one level up; the chirality translates it by `2f - 1/f`, short of two positions by `1/f`, which scales to the residue `1` | `MarchCoords.derived_run_shift`, `.derived_shift_defect`, `.defect_scales_to_one` | VERIFIED |

### Self-audit of my own negative claims (2026-08-31)

Two negative claims made this week were wrong, and both failed the same way: a claim of **absence**
inferred from a search that did not find something, where the thing existed under another name.

* "(ii) and (iii) cannot be stated without the placement layer" — false. The positional coordinate
  is `OrientBridge.edgePos`. The specs I wrote were refutable because they quantified over the
  advance function instead of defining it; the diagnosis, not the refutation, was wrong.
* "`cengine_rx2` has no source" — false. It is built from `cengine_iso.cpp`, committed at
  `3890d81`; the search looked for `*rx2*.cpp`. The rebuild is byte-identical and reproduces the
  logged verdict and node count.

**Consequence for "the fast vein is exhausted".** That claim was computed from *blocker text*, and
28 of the PROVED statements carry blockers that are elliptical ("same structure", "same", "same
sweep") or empty (`lem:census`). Blocker text has already been caught stale once, on
`prop:interfacefloor`. So the claim is weaker than it was stated:

> The fast vein is exhausted **among the statements whose blockers were read against their
> declarations**. Twenty-eight carry elliptical blockers that have not been individually re-checked,
> and any of those could hide a reachable statement.

Two were spot-checked and both survive, but not for the recorded reason:

| Paper | Spot-check result |
|---|---|
| `prop:tightside` | still blocked, but its clause "every one of the `2f` junctions carries exactly one `γ` and is the figure `{γ,α,β}`" is now covered by `VertexFigureReal.gamma_boundary_figure_real`. What blocks it is the *other* clauses: the side word `a^{2f}c` and the per-tile orientation, both bridge (c). Not splittable — the figure clause is stated *of that side word*, so it is not independently assertible |
| `thm:elltwo` | still blocked: needs the slot chain of `thm:l2slot`, a placement structure with no Lean definition. The recorded blocker "same" pointed at `W2Core`, which is not the obstruction |

Re-checking the remaining 26 elliptical blockers is outstanding work, not a discharged obligation.

### Re-check of the elliptical blockers, batch 1 of 3 (2026-08-31)

Eight of the 28 read against their statements. All eight survive as blocked; none is fast-vein. Two
carried rows that pointed at the wrong thing.

| Paper | Verdict | Real blocker |
|---|---|---|
| `cor:basedi2e` | blocked | the base decompositions are of a *real* tiling's base, and the narrowing is the `γ`-trap (`prop:gammatrap`, **now VERIFIED, 2026-09-02**) — what still blocks this row is instantiating it at this corollary's real base, not an open geometric input |
| `lem:cornerstep` | blocked | placement: "a base corner tile lays `a`", and its `b`-edge joining a base vertex to a side vertex. **Note**: its arithmetic clause — a straight junction presenting `γ` leaves `α+β` with the unique fill `{α,β}` — is now covered by `VertexFigureReal.one_gamma`, but is not independently assertible |
| `lem:noapexline` | blocked | the brick/mate structure decides which lines the collision figure consumes. **Note**: the conclusion `k < f` from `bp ≤ f` is trivial arithmetic; the row's "same lattice development" pointed at the wrong obstruction |
| `lem:termination` | blocked | ladder development |
| `lem:wallclimb` | blocked | block tiles and mates: placement |
| `prop:dirgroup` | blocked | needs `Dissection.dirSet` developed as a group with its grading |
| `thm:aforcesT` | blocked | `W(J)` interior to a tile edge: the `T`-junction notion, placement |
| `prop:widecol` | blocked | the general parallelogram; `PgramTiling52` is one member |

**18 of the 28 remain unchecked.** The exhaustion claim still carries that qualification.

### Measured: the run's orientation is constant in the traced refutations (2026-08-31)

`code/analysis/run_orientation.py <f> <bp> <cp>` regenerates this from scratch: it runs the engine
under `CENGINE_TRACE=2`, which prints one line per *recursed* placement as exact `(p+q√D)/d` pairs,
and classifies every tile laying an `a`-edge on the run line by its apex offset against
`dBG=(3f²-1)/2f` and `dGB=(1-f²)/2f`.

| trace | `a`-tiles on the run | orientations |
|---|---|---|
| `(6,5)`, `f=12` | 10 | BG 10, GB 0 |
| `(6,5)`, `f=14` | 10 | BG 10, GB 0 |
| `(7,6)`, `f=12` | 16 | BG 16, GB 0 |

36 placements, every one BG. Because the trace prints recursed placements, the search never *enters*
a GB placement on the run, not merely fails to complete one.

**FALSIFIED 2026-09-01.** A fourth trace — `(6,11)` at `f=12` under `CENGINE_TRACE=2` — places a
`GB` tile, at base position `395` (three `a`-edges from the right end of the base, length 431),
where *both* orientations are explored. So the search **does** enter `GB` placements on the run; the
all-BG census below was trace-limited, which is exactly the absence-from-search inference this entry
hedged against, and the hedge was right. The speculative shortcut — "if `GB` is excluded, obligation
(i) needs no `prop:orientmono`" — is dead. `prop:orientmono`'s actual statement, *at most one*
transition, is the correct route, and `all_but_one_is_march_junction` is the correct reduction.

**Update, same day:** the mechanism is now identified and its arithmetic verified — see `M-asym`.
`BG` cannot be followed by `GB` because the two tiles' wedges at the shared junction both contain
the vertical, so their interiors meet. That is why the traces show no `GB` after the first `BG`, and
it is asymmetric in the right direction. The measurement below stands as the observation that
prompted it.

**HEURISTIC, and explicitly not a claim that GB is impossible.** Absence in a search is absence under
that search's prunes; inferring impossibility from a failed search is the error behind both
retractions of this week. What it says is conditional: *if* GB is genuinely excluded on the run then
obligation (i) is discharged **without** `prop:orientmono`, since a constant orientation makes every
junction a march junction — stronger than "all but at most one".

One case is provable: at the run's first position the GB apex sits at `-(f²-1)/2f < 0`, outside the
target, so the boundary excludes it there. Interior positions have interior apexes and are not
excluded that way; overlap with the already-placed tiles and their fillers is the plausible
mechanism, and it is untested.

| M-asym | `BG → GB` straddles the junction (the two tiles' wedges both contain the vertical, so their interiors meet); `GB → BG` separates | `MarchCoords.bg_then_gb_straddles`, `.gb_then_bg_separates`, `.transition_asymmetric` | VERIFIED (the arithmetic). This is the mechanism behind `prop:orientmono`, in coordinates, and it is **asymmetric** — unlike the apex-*joining* criterion of `transition_not_a_side`, which is symmetric in the two directions and therefore was never a route to monotonicity. Turning "each wedge contains the vertical" into "two `Dissection` tiles' interiors meet" is the placement layer and is not done |

| M-overlap | two distinct tiles of a dissection sharing a vertex cannot both open toward a common direction | `MarchOverlap.Tri.mem_interior_of_vertex_push`, `.Dissection.wedge_disjoint_at_vertex` | VERIFIED — the vertex analogue of `Dissection.cross_disjoint_of_onEdge`: a `v` strictly inside both wedges (both off-vertex barycentric coordinates increasing along `v`) puts `pts k + ε·v` in both interiors, against `interiors_disjoint`. This is the geometric half of the `BG → GB` kill; `bg_then_gb_straddles` is the arithmetic half. What still separates them is the *translation*: identifying the coordinate model's vertical-at-the-junction with a `v` satisfying the four barycentric conditions for the two concretely-placed tiles. That is one instantiation, not a layer |

| M-combo | positive combinations of the edge directions satisfy the wedge conditions; the dissection kill in that form | `MarchOverlap.coord_pos_of_combo`, `.Dissection.wedge_disjoint_combo` | VERIFIED — orientation-free: `coord (k+1)` has linear part `1` along the edge to `pts (k+1)` and `0` along the edge to `pts (k+2)`, so no `det` enters |
| M-vert | the vertical solves both coefficient systems at a `BG → GB` junction, and provably **not** at `GB → BG` | `MarchCoords.vertical_in_bg_gb_wedges`, `.vertical_not_in_gb_wedge` | VERIFIED — the negative control: the kill refuses to fire on the transition `prop:orientmono` permits. What now remains between these pieces and "no `BG → GB` on a real run" is only the bookkeeping that the two placed tiles' edge vectors at the junction have the stated components — a hypothesis-matching step, no new mathematics |

### Lead (2026-09-01): the ceiling band is golden and bp-independent — pre-registered

At every measured member the band `cp = f-1` is bp-independent (spread ≤ 1.13%) and its mean fits
`16.1·φ^f` (growth `φ²` per `f`-step of 2: measured 2.62, 6.85, 6.85). The mirror sends the band to
words with `c` fixed at position 4, `b` anywhere later. Same golden signature as the march, with `f`
in the role of `bp` — the obstructions paper's "second family", whose driving run it could not
identify. Predictions for `f = 24` are frozen in `private/PREREG_ceiling_band.md` (band within 2%,
mean in `[1.60M, 1.74M]`, `(6,23)` in `[1.63M, 1.70M]`); the running sweep will decide them without
further action. If confirmed and the mechanism proved, one run per band plus a reduction collapses
the dominant part of every future sweep.

**Verdict on the recurrence (same day):** the odd members were measured and the exact unit-step
Fibonacci reading is **falsified** — `a(13) = 8359` misses the frozen window `[8377, 8407]` by 18,
and `a(15) = 21895` falls *below* `a(14) + a(13) = 21956`, so the additive constant changes sign.
The geometric law `16.1·φ^f` survives to 0.35% at both new points. The band is asymptotically
golden but not exactly self-reducing like the march; a "one run per band" exact skip is therefore
not available. P1–P3 for `f = 24` (geometric-law predictions) remain frozen and open.

| M-kill | **`bg_gb_dies`: a `BG` tile followed by a `GB` tile at a shared junction is impossible in a dissection** | `MarchKill.bg_gb_dies` | VERIFIED — the full assembly: straddle signs → both coefficient systems solved by the vertical → `wedge_disjoint_combo` → contradiction with `interiors_disjoint`. Consumes the placed configuration through component hypotheses (tile 1's edges at the junction `(-f,0)` and `(dBG-f, h)`, tile 2's `(f,0)` and `(dGB, h)`). This is `prop:orientmono`'s hard direction **at one junction of a real dissection**, from coordinates. What it does not supply: that the run's consecutive tiles present these components — the passage from "a run of `a`-edges on a line" to the component facts, which is the run-as-object step |

| M-runstep | **`run_step_bg_gb_dies`: the `BG → GB` step dies from distances alone** | `MarchRunStep.circle_x`, `.bg_abscissa`, `.gb_abscissa`, `.heights_agree`, `.run_step_bg_gb_dies` | VERIFIED — the apex components are no longer hypotheses: they are **forced** by the four side-length distances (two-circle intersection, one point above the line). The final statement consumes only what tile congruence provides — consecutive base edges of components `(f,0)`, the four apex distances, apexes above the line — and concludes `False`. Obligation (i)'s remaining gap shrinks to: a run's consecutive tiles satisfy these distance hypotheses, which is the corner figure (`gamma_boundary_figure_real`, VERIFIED) plus congruence naming which corner sits at which end |

### Re-check of the elliptical blockers, batch 2 (2026-09-01)

| Paper | Verdict | Real blocker |
|---|---|---|
| `prop:a2branch` | blocked | "the mirrored `L=-2` tile laying a horizontal `c`-edge along the floor line east of the fork" — a placed configuration; placement layer. The row's "same structure" under-specified this |
| `thm:forkkill` | blocked | the row-2 fork of a residual configuration: brick/mate placement |
| `cor:inflcrux` | blocked | inherits `prop:inflbdy` (scale map on dissections) |
| `lem:census` | blocked | its strongest row had an **empty** blocker cell; the real one, recorded in the audit of the six `PROVED: … VERIFIED` labels, is the global corner-incidence double count. Row completed |

12 of 28 now re-checked; 16 remain.

### The band's leak, localized (2026-09-01)

Diffing the node traces of `(6,11)` and `(7,11)` at `f=12` (5175 vs 5173 nodes): the trees are
**identical except at exactly five divergence points, all at depth 10** — the same five parent
paths in both, with a different child index chosen (`.0` vs `.2`). Below them `(6,11)` hangs
subtrees `{646, 1287, 1287, 646, 1287}` (sum 5153) and `(7,11)` hangs `{792, 1189, 1189, 792,
1189}` (sum 5151): two sizes per tree, multiplicities `(2,3)`, individually `bp`-dependent, totals
differing by 2. So the band's `bp`-independence is a **sum invariance without termwise invariance**
— the five subtrees reshuffle as the `b` moves, total almost conserved — which is exactly where the
~1% spread and the sign-flipping additive constant of the falsified Fibonacci reading live. A
mechanism proof for this family would have to explain the near-conservation of the five-subtree
total, not a tree identity; that is a different and harder shape than `prop:findep`'s.

### The band mechanism, read off the traces — three pre-registered hits (2026-09-01)

Tracing `(5,11)`, `(6,11)`, `(7,11)`, `(8,11)` at `f=12`: consecutive band words share an exact
skeleton to depth `~2(bp−1)` — **the march spine, two nodes per base position** — and diverge at a
frontier of exactly 3, 5, 8 points (pre-registered as Fibonacci before the `(8,11)` run: hit, along
with the predicted depth 12 and total). The frontier paths are `2.2.1.2.{0,1}.2.{0,1}.2…`: the
choice bits are the chirality choices, and the frontier is exactly the binary strings **with no two
consecutive 0s** — the monomer–dimer condition, in the raw search paths. The hanging subtrees take
only **two** sizes, set by the **last** chirality before the `b` (at `(8,11)`: 742×5, 494×3),
consistent with `MarchCoords.derived_run_shift`: the chirality sets the phase at which the march
meets the `b`.

Confirmed at a fourth `bp` by a second pre-registration ((9,11): depth 14, 13 points, two sizes
with multiplicities {8,5} — all three hit). The law across `bp = 6,7,8,9` is: depth `2(bp−1)`,
frontier `3, 5, 8, 13` (Fibonacci), multiplicities `F(k−1), F(k−2)`, exactly two subtree sizes per
level. A fourth prediction — that `(9,11)`'s total lies in the band — **missed**, and the cause was
a framing error of mine: the band was measured over the *escape transversal*, which at `f=12`
contains only `(6,11)` and `(7,11)`, so `(8,11)` and `(9,11)` are outside the reference class. The
escape-set statistic and the `f=24` predictions P1–P3 are unaffected.

So the entire `cp`-large family's cost is march combinatorics: shared spine, Fibonacci frontier,
phase-set collision subtrees. The `bp`-independence is a Fibonacci-weighted sum of shrinking phase
subtrees, conserved only approximately — which is exactly why the additive recurrence was falsified
while the `φ`-law survives. Consequence for the programme: the march induction (`rem:marchobl`)
governs not just `cp = bp−1` but the traversal structure of **every** `a`-run the search walks;
its value rises accordingly.

### Re-check of the elliptical blockers, batch 3 (2026-09-01)

| Paper | Verdict | Real blocker |
|---|---|---|
| `thm:frontier2` (and by the same shape `frontier3`, `frontier4`) | blocked | each is a finite list of engine exhaustions; certified-search format |
| `thm:dichotomy` | blocked | one engine exhaustion (4,334,789 nodes); certified-search format |
| `lem:value` | blocked | the flux functionals `C_{f_α}`, `C_{f_β}` on a placement: flux development, absent |
| `prop:inflparity` | blocked | edge-to-edge hypothesis has no Lean form; scale map for the inflated tile |
| `cor:rowinduction`, `lem:rowwords`, `lem:rowp1`, `lem:rowq0`, `prop:slotdichotomy` | blocked | no declarations; planar placement arguments (rows/slots), as their debt rows already state |
| `cor:noTP`, `prop:rung2`, `prop:figurePprime`, `lem:parity` | blocked | chord trace / pierce configuration / placement figure / census hypothesis — as recorded in earlier audits |

**All 28 elliptical blockers are now re-checked.** None was fast-vein; four rows were corrected
along the way (`lem:noapexline`, `lem:cornerstep` note, `lem:census` empty cell, `thm:elltwo`
citation). The fast-vein exhaustion claim now rests on statements read against declarations for the
full population.

| M-count | **`no_two_gammas`: two tiles cannot both present `γ` at a straight-edge point** | `MarchRun.no_two_gammas` | VERIFIED — a *second, independent* kill of `BG → GB`. Reading the orientation convention off the distances, a `BG` tile has `γ` at the right end of its `a`-edge and a `GB` tile has `γ` at the left, so at a `BG → GB` junction both present `γ`; the straight-figure system `x+2z=3, y+z=2` gives `z = 2 ⟹ x = -1`. On the **boundary** this is far cheaper than the wedge route. It does **not** supersede it: the wedge route uses only `interiors_disjoint`, so it also kills *interior* junctions, where the budget is `2π` and the figure `{β,3γ}` makes `r = 3` possible and counting cannot decide |

| M-frontier | the search's divergence frontier is the no-two-consecutive-`0`s chirality language; its counting law is the march recurrence, and the split by last letter gives the observed multiplicities | `MarchFrontier.noTwoZeros`, `.frontier_values`, `.split_by_last`, `.frontier_induction`, `.frontier_grows` | VERIFIED — `frontier_values` reproduces the measured `3, 5, 8, 13`; `split_by_last` is the `F(k−1), F(k−2)` split that explains why the hanging subtrees fall into exactly **two** size classes (the size depends on the last chirality alone). `frontier_induction` restates `MarchStep.march_dies` over this language, so the induction and the measured object are one thing |

| M-cases | at a straight-edge junction the two `a`-tiles present `(β,β)`, `(β,γ)` or `(γ,β)` — never `(γ,γ)` | `MarchRun.junction_cases` | VERIFIED — obligation (i)'s `BG → GB` half on a boundary run: `α` is opposite `a` so cannot sit on the line, leaving `β` (flanks `{a,c}`) or `γ` (flanks `{a,b}`) at each end, and `no_two_gammas` removes `(γ,γ)`. The three survivors are `GB→GB`, `GB→BG`, `BG→BG`: exactly the words with no `BG → GB` factor |

### The two phase classes are one tree up to a rational factor (2026-09-01)

Dissecting the 13 frontier subtrees of `(9,11)` at `f=12`:

* the **5** subtrees of size 294 are **identical in shape**, and so are the **8** of size 442 —
  the size classes are shape classes, not coincidences of count;
* their depth profiles are `1,2,1,4,2,4,8,24,24,70,66,88` and `1,2,2,8,3,6,12,36,36,105,99,132`,
  which agree in a short head and are then **exactly proportional at ratio 3:2** from relative
  depth 4 onward (`2→3, 4→6, 8→12, 24→36, 24→36, 70→105, 66→99, 88→132`), with `442 = 441 + 1`.

So the band total is a Fibonacci-weighted sum of **two proportional copies of one tree**:
`F(k−1)·A + F(k−2)·B` with `B/A → 3/2` past the head. That is a closed form in principle, and it
explains the near-conservation directly — as `bp` grows the weights move along the Fibonacci
recurrence while the two tree sizes shrink, and the product is conserved only to the head
discrepancy. The `+1` head defect is where the falsified additive recurrence's sign-flipping
constant comes from.

Not proved: that the shape identity and the `3:2` proportionality hold at every `bp` and `f`. Two
words at one member is a measurement.

### The `2B = 3A + 2` law, and monotonicity from the local fact (2026-09-01)

**The phase-class law, pre-registered and hit at a second member.** `(7,13)` vs `(8,13)` at `f=14`:
depth 12, 8 divergence points, exactly two subtree sizes `1290` and `1936`, ratio `1.5008`,
multiplicities `{3,5}`, shape-identical within class — all four predictions frozen beforehand. The
two members give an exact relation:

| member | small `A` | large `B` | relation |
|---|---|---|---|
| `f=12` | 294 | 442 | `2B = 3A + 2` |
| `f=14` | 1290 | 1936 | `2B = 3A + 2` |

So the frontier total is `F(k−1)·B + F(k−2)·A` with `B = (3A+2)/2` — a closed form in `A` alone,
measured at two members and two `bp` each. Not proved.

| M-mono | no `BG → GB` anywhere **is** `prop:orientmono`'s block form, with at most one transition | `MarchMonotone.mono_of_no_step`, `.block_form`, `.at_most_one_transition` | VERIFIED — the combinatorial step from local to global, and it is short: writing `true` for `BG`, "never `BG` then `GB`" says `w i = true → w (i+1) = true`, so `w` is monotone, hence `GB^j BG^(L−j)`, hence at most one transition. Combined with `MarchRun.junction_cases` (VERIFIED) this is `prop:orientmono`'s conclusion **on a boundary run**, from the corner figure alone — no bridge (c). What remains for `prop:orientmono` as the paper states it is the inflated-tile side, and for obligation (i) the identification of the run's tiles as the `a`-tiles the march walks |

| C `prop:orientmonobdy` | monotonicity of the orientation word on a side of the target | `MarchRun.no_two_gammas`, `.junction_cases`, `MarchMonotone.mono_of_no_step`, `.block_form`, `.at_most_one_transition` | VERIFIED — split off `prop:orientmono` on 2026-09-01. **The bridge-(c) blocker is gone for this half**: the argument runs at the junctions themselves and never passes from a real boundary to an orientation word. Hypothesis retained: each tile presents `β` or `γ` at each end of its `a`-edge |
| C `prop:orientmono` | the same on a side of the **inflated tile**, plus the `β`-one-end-`γ`-the-other clause | `TilePlacement.incident_sides` | PROVED — the residue after the split. The inflated-tile side needs the scale map; the `β`/`γ` clause is the tile-corner fact (`α` is opposite `a`, so the two flanking corners are `β` and `γ`), available in `incident_sides` but not composed with `cornerAngle` into a statement about what a *placed* tile presents |

**Effect on obligation (i).** `MarchRun.all_but_one_is_march_junction` consumed `prop:orientmono` as
an assumed bound. For a run on a side of the target that bound is now VERIFIED, so obligation (i)
reduces on the boundary to the single remaining clause above — the `β`/`γ` dichotomy at an `a`-edge's
two ends — rather than to bridge (c).

| C M-flank | the two corners flanking the `a`-edge carry `β` and `γ`, never `α` | `MarchFlank.apex_angle_smallest`, `.endpoints_ne_apex`, `.beta_or_gamma`, `.flank_is_beta_or_gamma` | VERIFIED — the clause `prop:orientmono`'s residue named. The angles chain as their opposite sides (`TilePlacement.angleAt_lt`), so with `a < b < c` the angle opposite `a` is strictly smallest; a corner at an endpoint of the `a`-side carries one of the two larger angles, hence `β` or `γ`. This discharges the hypothesis `prop:orientmonobdy` retained, so **on a side of the target the monotonicity statement now stands with no hypothesis beyond the tile's side ordering** |

**Obligation (i), boundary case: the chain is complete.** `flank_is_beta_or_gamma` → the `β`/`γ`
dichotomy at each junction → `junction_cases` (no `(γ,γ)`) → `MarchMonotone` (block form, at most one
transition) → `all_but_one_is_march_junction`. Every link is VERIFIED. What is *not* proved is that
the `a`-run of a real dissection is the run the march walks — the identification of the object, not
any step of the argument.

| C M-exc | the exceptional `{3α,2β}` junction **is** the transition, and there is at most one | `MarchMonotone.transitions_card_le_one`, `.exceptional_is_transition` | VERIFIED — the junction table is forced: `BG` has `γ` at its right end and `GB` at its left, so the presented pairs are `(γ,β)`, `(γ,γ)`, `(β,β)`, `(β,γ)`; `no_two_gammas` kills `(γ,γ)`, and `(β,β)` — the only pair without a `γ`, hence the only `{3α,2β}` figure — occurs exactly at `GB → BG`, the single change of a monotone word. `transitions_card_le_one` gives the bound in the `Finset` form `all_but_one_is_march_junction` consumes, so the two ends of obligation (i)'s boundary chain now meet in the right shape. The paper asserted "and it is the transition"; both halves are now proved |

| C M-presents | a placed tile presents `β` or `γ` at either endpoint of its `a`-edge | `MarchFlank.presents_beta_or_gamma` | VERIFIED — `Tri.localAngle_vertex` closes the `angleAt`/`localAngle` seam (at its own vertex a tile's local angle *is* its corner angle), so the flank dichotomy transfers verbatim to what a tile of a dissection presents. This is the exact hypothesis `MarchRun.junction_cases` consumes, so obligation (i)'s boundary chain now runs from tile geometry to the junction bound with no seam left between links |

| C M-runobj | the `a`-run of a dissection as an indexed object: tiles, edges, length, and the junction bound | `MarchRunObject.aRun`, `.aRun_nodup`, `.mem_aRun`, `.runTile`, `.runEdge`, `.runTile_spec`, `.run_exceptional_le_one` | VERIFIED — the selection reuses `BaseChain.wallList` (edges on the line `g = c`, `Nodup`), filtered to those of length `a`; `runTile`/`runEdge` index it and `runTile_spec` says every entry really is a wall edge of that length. `run_exceptional_le_one` produces `all_but_one_is_march_junction`'s hypothesis **for the object** rather than assuming it. **Still assumed:** that the run is contiguous along the line (`BaseChain.base_chain_consecutive_meet`'s job) and that the orientation word `w` is the one read off the tiles — the run is indexed, but its word is not yet computed from `presents_beta_or_gamma` |

### Route 1 (the prime-case target), state after 2026-09-01

| Atom | Statement | Lean declaration | Label |
|---|---|---|---|
| R1-fig | figure at an interior point with an `α` and a straight angle: `{π,3α,2β}` or `{π,α,β,γ}` | `RouteOne.alpha_wall_figure`, `.alpha_wall_figure_real` | VERIFIED |
| R1-over | a `b`- or `c`-edge from `V` strictly contains `E` — tile-interior blocking, branch dies | `RouteOne.overshoot_dichotomy`, `.E_interior_of_long` | VERIFIED |
| R1-clos | a tile is the closure of its interior; **no point of one tile lies in another's interior** | `RouteOne.Tri.carrier_eq_closure_interior`, `.Dissection.not_mem_interior_of_mem` | VERIFIED — the placement primitive that kills any slanted edge poking into covered territory; reusable well beyond route 1 |
| R1-flank | the horizontal-flank core: `(1,0)` a nonneg combination of two weakly-upward non-degenerate directions ⟹ one of them is horizontal rightward | `RouteOne.horizontal_flank` | VERIFIED |
| R1-tang | **the flank at `V` lies along the line** | `RouteOne.flank_along_line`, `.cone_forces_horizontal`, `.cone_hyp_of_tangential`, `.sub_vertex_eq_combo`, `.affine_nonneg_at_zero`, `.lower_flank_horizontal` | **VERIFIED** — a tile with vertex `V`, both edge directions weakly upward and not both horizontal, containing points that approach `V` tangentially from the right, has one edge horizontal and rightward. `sub_vertex_eq_combo` decomposes a carrier point at the vertex (the `i = k` term drops), `carrier_eq_nonneg_coord` makes the coefficients nonnegative, and `cone_forces_horizontal` finishes. **The hypotheses are now geometric facts about one tile, not a covering argument** |
| R1-desc | the wall descent: the `a`-advance recursion terminates at the wall's exit | `RouteOne.wall_descent` | VERIFIED (the induction shape) — consumes the trichotomy as its step; the exit's blockedness is the terminal fact, geometric, open |
| R1-march | the `a`-advance case: the march on the interior wall, with terminal kill at the wall's far end | `MarchStep.*`, `MarchRunObject.*` (shape) | OPEN — the induction is `march_dies`; its step consumes the same trichotomy one position along |

**Route 1's remaining obligations, after 2026-09-01 (revised).** Obligations (1), (2) and the
terminus half of (3) are now VERIFIED:

| Obligation | Declaration | Label |
|---|---|---|
| (1) the tangential hypothesis — one tile serves at arbitrarily small slope | `RouteOne.pigeonhole_tangential` | VERIFIED — finitely many tiles, infinitely many approach points, the fibre unbounded |
| (2) weakly upward — both edges at `V` point into the upper half-plane | `RouteOne.no_downward_edge`, `.edge_dir_nonneg_of_local` | VERIFIED — from local containment above the line along each edge |
| (3a) the terminus — the wall admits finitely many advances, and overshooting its end leaves the target | `RouteOne.exists_terminal_step`, `.advance_count_bounded`, `.overshoot_leaves` | VERIFIED — `prop:doublec`(iv)'s base-overshoot test in the form the descent needs |
| (3b) the descent's step | `RouteOne.descent_step`, `.produced_edge_blocks`, `.route_one_closes` | REDUCED — `produced_edge_blocks` is the self-similar half: the edge the trichotomy *produces* at `V` is the blocking edge at `E`, same length, ending from the left, which is why the step is a step. `descent_step` then names the two remaining inputs as `fig n` (the figure at the advanced point carries an `α` and a straight angle) and `inWall n` (the advance has not left the wall); `route_one_closes` chains it into `wall_descent`, so **route 1 is closed conditional on those two**. `descent_step` and `route_one_closes` need no axioms at all |
| (1)(2) instantiation | `RouteOne.covered_of_mem_target`, `.approach_covered`, `.above_line_of_below_tile` | VERIFIED — approach points near an interior `V` are covered (from `D.covers`), and a point of one tile cannot lie in another's interior, which is `no_downward_edge`'s local containment |

The inputs each of (1), (2) now *consumes* (that the approach points exist and are covered; that the
tile stays above the line near `V`) are facts about the specific escape configuration, supplied when
the theorems are instantiated. What has no proof at all is (3b).

### Route 1's two residual inputs, after 2026-09-01 (evening)

| Input | Declaration | Label |
|---|---|---|
| `fig n` — the figure at the advanced point | `RouteOne.fig_of_witnesses`, `.alpha_not_from_advancing` | REDUCED to **one witness**: `fig_of_witnesses` derives the figure from an `α` and a straight angle at `E`, and `alpha_not_from_advancing` shows the `α` cannot come from the advancing tile — it lays its `a`-edge along the wall, so at either endpoint it presents `β` or `γ`. So the outstanding fact is the **straight angle at `E`**, i.e. that a tile has `E` interior to an edge; the `α` then follows from the classification, since a straight-edge point that is not the `{3α,2β}` figure is `(1,1,1)` |
| `inWall n` — the advance stays on the wall | `RouteOne.advance_injective`, `.advance_count_le_run`, `.terminus_of_run_length` | **VERIFIED** — each step consumes a distinct wall `a`-edge (positions differ by `n·a`), so the step count is bounded by `MarchRunObject.runLength`. This also re-derives the terminus **combinatorially**, without the wall's metric length: step `L+1` is unreachable when the wall has `L` edges |

**Route 1's single outstanding fact.** Every other input is VERIFIED. What remains is: *at the
advanced point `E`, some tile has `E` interior to an edge* — one straight angle. If the covering
below the wall is a through-edge this is immediate; if it is a junction, `E` is a vertex on both
sides and the figure is the `s = 0` interior one, which the classification also handles but which
has not been carried through. That case split is the residue.

| C R1-inst | route 1's two configuration hypotheses, discharged | `RouteOne.approach_points_covered`, `.weakly_upward_of_above`, `.escape_flank` | VERIFIED — the approach points exist because `V` is interior (small multiples of any direction stay in the target and are covered); the edge directions are weakly upward as soon as the tile keeps its points above the wall, since its other two vertices lie in the carrier, and a point strictly below would be interior to the tile below (`above_line_of_below_tile`). `escape_flank` composes them. **What remains for route 1 is the identification** — matching the escape configuration's tiles to the theorems' `T` and its below-neighbour, including that the pigeonhole's chosen tile lies above the wall. Bookkeeping over the tile list, not a new argument |

| C R1-ident | the serving tile is an upper tile; the flank conclusion for a named tile at a named vertex | `RouteOne.not_below_of_contains_above`, `.serving_tile_is_upper`, `.route_one_flank_identified` | VERIFIED — approach points taken **strictly above** the wall cannot lie in a tile whose carrier is weakly below `V`, so the pigeonhole's tile is an upper tile. `route_one_flank_identified` then states the flank conclusion for `D.tile i` at vertex `k` with `pts k = V`. **Route 1's sole remaining hypothesis** is `hvert`: that `V` is a vertex of the serving tile. The figure gives it in principle (`alpha_wall_figure_real`, `s = 1`, so no upper tile has `V` interior to an edge) but that is not composed with the pigeonhole — the returned tile is not yet known to be among the tiles the figure counts |

| C R1-vertex | the serving tile has `V` as a vertex | `RouteOne.serving_has_vertex`, `.not_straight_of_unique`, `.route_one_flank_composed` | VERIFIED — `localAngle_cases` splits four ways and three are excluded: `0` (the tile contains `V`), `2π` (the figure's `u = 0`), and `π` (the `π`-count is exactly one and the below tile carries it). Route 1's chain is now complete as a **scheme**; what remains is exhibiting its hypotheses in a hypothetical tiling — the attachment to the object, not a step of the argument |

| C R1-wall | building `EscapeData` from the wall: three of its fields derived | `RouteOne.mem_of_approach`, `.serving_ne_two_pi`, `.serving_ne_zero` | VERIFIED — `mem_of_approach` puts `V` in the serving tile's carrier (closed, with points arbitrarily near); `serving_ne_two_pi` excludes `localAngle = 2π`, since that would put `V` interior to the serving tile while `V` lies in the below tile's carrier, against `not_mem_interior_of_mem`; `serving_ne_zero` excludes `localAngle = 0` via `MarchFlank.localAngle_ne_zero_of_mem`. **Dead end lifted 2026-09-02:** `localAngle_ne_zero_of_mem` was abandoned on 2026-09-01 for want of corner-angle positivity; `MarchFlank.cornerAngle_pos` now supplies it (degenerate angle forces equality in the strict triangle inequality, at index `j` or `j+2` according to which degeneracy), and the two-vanishing-coordinates branch is closed by `AffineBasis.ext_elem` |
| C R1-wall2 | the `EscapeData` constructor from the wall | `RouteOne.pigeonhole_wall`, `RouteOne.EscapeData.ofWall` | VERIFIED — the constructor the surrounding prose had only promised now exists. From `V` interior, a below-tile `b` with the straight angle, `π`-count one, and an approach sequence (right of `V`, above the wall, slope and distance both `O(1/n)`), the serving tile `i` and four of `EscapeData`'s fields — `hib`, `hne0`, `hne2pi`, `hserve` — are derived, not assumed. `habove` is required only for the tiles the approach sequence lands in, not globally. The analytic block of the hypotheses is checked non-vacuous by an explicit witness, `VacCheck.approachWitness_sat` |

### Orphan census, corrected (2026-09-01)

The census had been reported as **1 orphan file**. That was an undercount: by the letter of Rule 18
the excluded set at the root is `README`, `LICENSE`, `.gitignore`, `CLAUDE.md`, `RULES.md`, and the
repo also carried `.zenodo.json`, `CITATION.cff`, `GOAL_PRIMES.md` and `PLAN_V4.md` — **4**.

Resolution:

* `PLAN_V4.md` and `GOAL_PRIMES.md` are strategy documents (publication ordering, target lists,
  commentary on an external read). Rule 10 puts strategy in `private/`, which never ships. They had
  been committed **and pushed**; they are now removed from the index, kept in `private/`, and
  gitignored. Their mathematical content — how the open case reduces — is in the README's
  "Where the open case stands", which is the part that belongs in public.
* `.zenodo.json` and `CITATION.cff` are release infrastructure of the same class as the files
  Rule 18 names: GitHub renders the citation file and Zenodo reads the metadata on release. They are
  classified as infrastructure and counted as **0 orphans**, and this sentence is the record of that
  classification rather than a silent exemption.

**Census after this correction: orphan files 0, orphan atoms 0, orphan statements 0.**

### The `sorry` question, settled properly

Repeated grep checks had been reporting between 0 and 7 `sorry` hits depending on the filter, all of
them prose (`` `sorry` `` inside docstrings such as "Axiom-clean; no `sorry`"). The authoritative
check is Lean's own: `lake build Erdos634.All` emits `declaration uses 'sorry'` for any real one, and
emits **none**. The corpus is sorry-free; the grep noise is not evidence either way and should not be
quoted as the check.

### Tile-placement layer, started (2026-09-02)

The single highest-leverage blocker — ~31 statements name it directly, more depend on it through
an assembly chain — had no Lean development at all. `TileAt.lean` is the first primitive:

* `Dissection.exists_tile_mem`: every point of the target lies in some tile (from `covers`).
* `Dissection.badSet`: the union of all tile frontiers, measure zero (`volume_badSet`).
* `Dissection.tile_unique_of_not_mem_badSet`: off the bad set, the covering tile is unique (two
  tiles' interiors both containing `p` forces them equal, by `interiors_disjoint`).
* `Dissection.tileAt`: the covering tile as a function of a target point (noncomputable choice),
  with its defining membership fact (`tileAt_mem`), agreement with any other witness off the bad
  set (`tileAt_eq_of_mem`), and independence of the membership proof off the bad set
  (`tileAt_congr`).
* `Dissection.target_vertex_mem_badSet`: proved (2026-09-02) the claim the first draft of this file only asserted — a target vertex always sits on the bad set, so `tileAt` cannot reach it directly. Reuses `BaseSelection.tile_interior_subset` rather than reproving tile-inside-target.
* `Dissection.exists_corner_tile`: at a target vertex, *some* tile covers it with local angle neither `0` nor `2π` — existence, from `MarchFlank.localAngle_ne_zero_of_mem` and `localAngle_ne_two_pi_of_not_mem_interior` (the `2π` branch of `Tri.localAngle` is definitionally the interior case, so `target_vertex_not_interior_tile` rules it out directly). This is *not* `lem:census`'s uniqueness content — recorded as existence only.
* `Dissection.tile_angle_dichotomy_at_vertex`: *every* tile touching a target vertex — not just one witness — presents either a corner angle of its own there, or a straight angle; `0` and `2π` are excluded universally, collapsing `PinPlumbing.localAngle_cases`'s four-way split to two. This is the qualitative shape `lem:census`'s corner counting runs on, not the counting itself (which needs the shared angle values across congruent tiles) — recorded as such.
* `Dissection.congruentDissection_localAngle_mem` (2026-09-01): for a real `CongruentDissection`,
  every tile's local angle at a target vertex lies in `{α, β, γ, π, 0}` — a theorem, not the
  `hvals` hypothesis `TilePlacement.base_corner_counts`/`corner_multiplicities` had taken as given.
  Assembled from `tile_angle_dichotomy_at_vertex` (above) and the pre-existing but previously
  unused `CongruentAngles.congruent_corner_angles`. `.congruentDissection_base_corner_counts` and
  `.congruentDissection_apex_counts` compose this with `base_corner_counts`/`apex_counts` to get
  the base-corner and apex fills unconditionally for a real congruent dissection — this closed a
  citation gap under `prop:cornerfig`'s own (already-VERIFIED) row, recorded there.
* `Dissection.congruentDissection_base_corner_tile_unique` (2026-09-01): **corner-tile
  identification, closed for a base corner.** `congruentDissection_base_corner_counts` classifies
  angles (one tile presents `β`, none presents `α`, `γ`, or a straight angle) but that is a census
  of values, not a carrier-membership fact. Bridging the two: a covering tile's local angle is
  nonzero (`MarchFlank.localAngle_ne_zero_of_mem`), so among the census values only `β` is open to
  it, and some tile does cover the point at all (`exists_tile_mem`), so the unique `β`-presenting
  tile is forced to be that covering tile. The result is `∃! i, D.target.pts k ∈ (D.tile i).carrier`
  at a base corner — exactly the fact `prop:cornerpara`'s own proof invokes from `prop:cornerfig`
  ("`T_A` is the unique tile at `A`"), now a real theorem rather than a phrase. It does **not**
  discharge `prop:cornerpara`: the harder half ("matched by exactly one tile", the far tile `T_3`
  on the `b`-edge chord) is untouched and still needs the wall/chord-partition argument.
  `prop:cornerpara`'s row below notes this precisely.

The first two bullets are deliberately minimal and do not themselves discharge any blocked row.
The last two close 'the tile at a corner' for a base corner specifically — not through `tileAt`
(a target vertex is always on the bad set, so `tileAt` never reaches one directly) but through the
angle census. 'The tile matched to an edge' (the harder half `prop:cornerpara` still needs) is
untouched. Recorded against `prop:cornerpara`'s row below because a real (partial) blocker cleared
there; not recorded as clearing any other row, per the standing instruction not to claim
placement-layer progress against a statement until its blocker actually moves.

## Certified-search bridge — topological half CLOSED 2026-09-02 (`ConvexCover.lean`)
The blocker shared by **8 rows** (`thm:44`, `thm:63`, `cor:elevenm`, `thm:frontier`, `thm:frontier2`,
`thm:frontier3`, `thm:frontier4`, `thm:eq105`) had two halves. The **geometric/measure half is now
done, once, reusably**: `Geometry.dissectionOfCover` builds a `Dissection` from `N` tiles inside a
target with pairwise-disjoint interiors and total area equal to the target's — the `covers` field
(pointwise `⋃ = target`) coming from `iUnion_carrier_eq_of_area`, itself from the genuinely new
`closed_full_measure_subset` (a closed full-measure subset of a convex body is the body; the fact
with no Mathlib counterpart). The **remaining half is per-certificate arithmetic transport**:
translating a specific certificate's `ℤ[√d]` coordinate triangles (e.g. `Tiling44`'s `Pt`) into
`Tri` over `Plane` and re-deriving containment/separation/area there. That transport is what still
blocks each of the 8 rows individually; the shared hard part no longer does. Any one of them now
flips as soon as its certificate is transported and fed to `dissectionOfCover`.

## Reusable tools built 2026-09-02 (check before any new geometric construction)
`IsoTri.isoTri` (isosceles) and `SssTri.sssTri` (general scalene, SSS) construct an actual `Tri`
from side lengths alone (`L≠0`/`r≠0`, `h≠0` with `h` the Pythagorean/law-of-cosines height) — the
first concrete real-coordinate `Tri` constructors anywhere in this project, confirmed absent by
search before being built. Any row whose blocker is "no real triangle realizing these numbers"
should reach for these first, not rebuild from scratch. They do NOT by themselves supply a full
`Dissection`/`CongruentDissection` (covering N tiles, wall/chain data) — that remains the deeper
placement-layer gap (structural blocker 1) for rows like `thm:walkstruct`, `thm:44`, `cor:elevenm`.

## The certified-search bridge and the area equation (2026-09-02, late)

| Atom | Statement | Lean | Label |
|---|---|---|---|
| CSB-topology | containment + disjoint interiors + area identity ⟹ the pointwise covering | `ConvexCover.covers_of_volume`, `.ofCertificate` | **VERIFIED** |
| CSB-translate | a `decide`-checked `ℤ[√d]` certificate satisfies those three in `Tri`/`volume` terms | none | **OPEN** — needs a triangle-area formula (`volume (Tri.carrier) = |det|/2`), absent from the corpus and from Mathlib |
| AREA-cong | congruent triangles have equal area | `CongruentArea.volume_congruent` | **VERIFIED** |
| AREA-eqn | `\|ABC\| = N·\|T\|` for a real `CongruentDissection`, no hypothesis | `CongruentArea.congruentDissection_volume_target` | **VERIFIED** |

**`ConvexCover` closes the half of the certified-search bridge previously recorded (RESEARCH_LOG,
2026-09-02) as "needing a real topology theorem that exists nowhere in this project or obviously in
Mathlib".** The argument: the union of the pieces is a finite union of compacts, hence closed, so
its complement in the target is relatively open; a triangle is the closure of its interior, so a
nonempty relatively open subset of the target contains a nonempty *open* set and therefore has
positive volume; disjoint interiors make the pieces a.e. disjoint (`Tri.volume_frontier`), so the
union's volume equals the sum equals the target's — and a positive-volume uncovered piece would put
the target's volume strictly above itself.

This is the blocker cited by `thm:44`, `thm:63`, `cor:elevenm`, `thm:frontier`, `thm:frontier2`,
`thm:frontier3`, `thm:frontier4`, `thm:eq105`. **None of those flips yet**: the certificates live in
exact `ℤ[√d]` integer arithmetic, disconnected from `Tri`/`Plane`/`volume`, and translating their
(C1)–(C4) into `ConvexCover.ofCertificate`'s hypotheses is untouched. What is closed is the
geometry; what remains is a translation whose gate is the missing triangle-area formula.

**Correction to `prop:dissection` (labelled VERIFIED).** Its second clause — "if the `T_i` are
pairwise congruent to a tile `T` then `|ABC| = N|T|`" — was cited to
`Dissection.volume_target_of_congruent`, which *takes* `∀ i, volume (tile i).carrier = v` as a
hypothesis. Nothing in the corpus had ever discharged it, so the label was resting on an
undischarged premise (the same defect class as the ten labels corrected in the 2026-08-30 audit).
`CongruentArea.congruentDissection_volume_target` now proves the clause outright, with no
hypothesis. The label was not wrong in substance, but it is only now actually backed.

## `thm:ladder` obligations after 2026-09-02 (late)

| # | Obligation | Lean | Label |
|---|---|---|---|
| cells | both cell shapes are real `Tri`s | `Subdivision.cellUp`, `.cellDown` | VERIFIED |
| C2 | every cell lies in the scale-`k` triangle | `Subdivision.bigTri`, `.P_mem_bigTri`, `.cellUp_subset_bigTri`, `.cellDown_subset_bigTri` | **VERIFIED** |
| C3 | cell interiors pairwise disjoint | `Subdivision.mem_interior_cellUp_iff`, `.mem_interior_cellDown_iff`, `.cellUp_interiors_disjoint`, `.cellDown_interiors_disjoint`, `.cellUp_cellDown_disjoint` | **VERIFIED** |
| C4 | the areas sum to the big triangle's | available: `CongruentArea.volume_congruent` + `addHaar_image_homothety` | not assembled |
| C5 | index the `k²` cells by `Fin (k²)` | counts only (`up_count`, `down_shift`, `total_count`); the bijection is absent | **OPEN** |

(C3) was the obligation this row previously named as its remaining content. It is closed, as is
(C2). The row stays **PROVED**: `Dissection` wants `tile : Fin N → Tri`, and (C5) — the bijection
from `Fin (k²)` onto `{(i,j) : i+j+1 ≤ k} ⊕ {(i,j) : i+j+2 ≤ k}` — is not built. That is index
bookkeeping rather than geometry, but it is not yet done, and the label does not move until it is.


## `thm:ladder` closed, 2026-09-02

`thm:ladder` is VERIFIED. The two structural pieces built for it are general and are recorded here
because other rows cite them:

* **`Erdos634.Compose.compose`** — the *composition map on dissections*, one of the four recurring
  blockers. Given a `Dissection M` and a `Dissection N` of each of its tiles, the `M·N` pieces form
  a `Dissection (M*N)` of the original target. Its hypothesis is carrier equality of the inner
  target with the coarse tile, not equality of `Tri` objects, so a differently-labelled congruent
  copy qualifies. **This blocker is now discharged**; rows that cited "no composition map on
  dissections" should cite the specific missing piece instead.
* **`Erdos634.Realizable.scaleTri` / `scaleTri_scaleTri`** — the *scale map on dissections*, in the
  form the ladder rows need: scaling about the triangle's own first vertex composes strictly,
  `scaleTri r (scaleTri s T) = scaleTri (r*s) T`, because a homothety fixes its centre.

Still open of the original four: the tile-placement layer, the certified-search **arithmetic** half
(a certificate's exact coordinates → a `Tri`, gated on `volume (Tri) = |det|/2 [SUPERSEDED 2026-09-02, see AreaDet]`), and the dual-graph
development.


## The certified-search bridge: both halves now exist (2026-09-02)

The rows for `thm:44`, `thm:63`, `cor:elevenm`, `thm:frontier`–`thm:frontier4` and `thm:eq105` all
recorded the same two-part blocker. Both parts are now discharged as *theory*; what is left is
per-tiling data entry, which is a different kind of debt and should be recorded as such.

* **Topological half** — `Erdos634.ConvexCover.ofCertificate`: (C2) containment + (C3) disjoint
  interiors + (C4) the area identity give the pointwise covering `Dissection` demands, by a measure
  argument. Landed earlier today.
* **Arithmetic half** — `Erdos634.AreaDet`. The old blocker was recorded as
  "`volume (Tri) = |det| / 2`, absent from this corpus **and** from Mathlib". **That statement of
  the blocker was wrong, and the error cost the eight rows above.** The constant `1/2` never enters:
  only the *ratio* of areas appears in (C4), so the reference triangle's area cancels
  symbolically and never has to be evaluated. What is actually needed is
  `volume T.carrier = ENNReal.ofReal |detTri T| * volume stdCarrier` for *some* fixed reference set,
  and that is `Measure.addHaar_image_linearMap` (`T` is the image of the standard simplex under
  `x ↦ edgeMap T x + T.pts 0`) plus translation invariance (`measure_preimage_add`) — about twenty
  lines. `detTri_eq` gives the determinant in the coordinate form a certificate computes, and
  `area_identity_of_det` turns the **exact identity `∑ᵢ |det tᵢ| = |det T|`** into (C4) with no
  measure theory left on the certificate side. `ofDetCertificate` packages the whole bridge.

**What actually remains for those eight rows**, stated without a hidden theory gap: for each named
tiling, (a) write its pieces as `Tri` objects with their exact coordinates, (b) discharge (C2) and
(C3) — decidable arithmetic, one separating line per pair — and (c) discharge (C1), congruence to
the tile.

**Update, same day: (c) is done.** `Erdos634.SssCongruent.congruent_of_dist_three` is SSS *with an
ambient isometry* — equal corresponding side lengths give a genuine `Plane ≃ᵢ Plane` carrying one
triangle onto the other, vertex for vertex, which is what `Tri.Congruent` demands. Mathlib's
`EuclideanGeometry.side_side_side` is strictly weaker: it proves the metric statement and produces
no map. The proof is concrete because the plane is two-dimensional — `ev_indep` (edge vectors at a
vertex are linearly independent, from affine independence), `inner_ev_eq` (polarisation turns equal
sides into equal inner products), `LinearEquiv.isometryOfInner`, then conjugation by the two
translations that move the base vertices to the origin.

So **all three of (C1), (C2)+(C3), (C4) now have general machinery**, and what remains for the eight
rows is per-tiling data entry only: writing each named tiling's pieces as `Tri` objects with their
exact coordinates and discharging two decidable arithmetic checks per pair. No theory gap is left
on this path.

**Methodological note, third occurrence.** "No Mathlib lemma states X" is not "X is hard", and a
blocker recorded in terms of the *strongest* statement one can imagine wanting is worth much less
than one recorded in terms of the *weakest* statement that suffices. Both `ConvexCover` and
`AreaDet` were skipped for weeks behind blockers phrased the first way.


**Correction (2026-09-02, later, in `private/VERIFY_PLAN.md`).** The "8 rows" sharing this blocker
are not homogeneous. `thm:44`, `thm:63`, `cor:elevenm` are *positive* realizability claims backed
by a witness certificate — `CertBridge.ofCert` applies to exactly these. `thm:frontier`–
`thm:frontier4` and `thm:eq105` are *negative* nonexistence claims backed by an exhaustive search
over candidate shapes, not a single witness — `CertBridge.ofCert` has nothing to offer them; they
need a different certified-search mechanism for negative exhaustion, not this bridge. Only the
first three should be attempted via the per-tiling data-entry path below.

## Certificate transfer: the general layer is complete (2026-09-02, later)

Everything a tiling certificate checks now has a Lean counterpart, and none of it is per-tiling:

| certificate check | Lean |
|---|---|
| coordinates → a triangle | `CertCoord.mkTri`, via `not_collinear_of_det` |
| (C1) squared side multiset | `SssCongruent.congruent_of_sq_dist_perm` (squares, and up to relabelling) |
| (C2) vertex in closed target | `CertCoord.mem_carrier_of_dets` + `CertGeom.carrier_subset_of_pts_mem` |
| (C3) separating edge-line per pair | `CertGeom.pairwise_disjoint_of_separating` |
| (C4) signed areas sum | `CertCoord.detTri_mkTri` + `AreaDet.area_identity_of_det` |
| the whole thing | `CertBridge.ofCert` |
| `ℤ[√15]` arithmetic → `ℝ` | `Z15Real.toR`, `toR_add/sub/mul`, `toR_nonneg_iff`, `toR_pos` |
| a certificate's named edge → the affine functional (C3) needs | `CertGeom.lineFun`, `lineFun_linear_ne_zero` (2026-09-02: fixed a stalled proof — the nonconstancy check now evaluates at concrete `EuclideanSpace.single` vectors instead of the `AreaDet.pb` Mathlib-basis representation, which `simp` would not reduce) |

`Z15Real` deliberately proves no injectivity of `toR` and so never needs `√15` irrational: every
certificate check transfers in one direction only, an equality or inequality *in* `ℤ[√15]` implying
the corresponding real statement.

**What is still missing, precisely.** The certificate files state their content as a *single*
`Bool` over `List`s (`Tiling44.checkAll = true`, one `decide`). Turning that into the indexed
`∀ i : Fin 44` / `∀ i j, i ≠ j` facts `CertBridge.ofCert` consumes requires unpacking
`List.all` and the `checkPairs` recursion for each certificate, and then instantiating the
44 (resp. 99, 63, 22) triangles as real objects. That is per-certificate engineering with a real
risk of elaboration cost at the 946-pair (resp. 4851-pair) level, and it is **not started**. No
theory gap remains on the path; the remaining work is that unpacking, and it should not be
described as small.

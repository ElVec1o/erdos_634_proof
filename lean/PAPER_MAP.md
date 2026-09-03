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
| M `prop:b3prime` | Beeson III Thm 8 core: no odd prime | `Beeson3NotPrime.triquadratic_not_prime` | VERIFIED. **Note 2026-09-03**: `Beeson3NotPrime.lean` also has `.fourcomp_not_prime`, Beeson III Thm 12's arithmetic core for the *other* scalene `3α+2β` target shape, `(2α,α,2β)` — read `erdos-634.tex:404-416` (`rem:b3prime`) closely: it cites both `triquadratic_not_prime` (Thm 8, this row's target `(2α,β,α+β)`) and `fourcomp_not_prime` (Thm 12) side by side for the branch's two scalene targets. `rem:b3prime` itself carries no `\lab{}` tag (a remark, not a tracked statement) and neither scalene target has its own named proposition — `prop:b3prime` (this row) and `prop:isoalphaprime` cover the *other* two target shapes of the same `3α+2β` branch (isosceles `α+β` and isosceles `α`), so `fourcomp_not_prime` has no `\lab`-tracked row of its own to attach to. **Corrected a real citation error**: `fourcomp_not_prime` was previously mis-cited (below, now removed) against `prop:reduction`, an unrelated `γ=2π/3` case-analysis statement it has nothing to do with — see `prop:reduction`'s correctly-cited row further down (`InvariantProduct.*`, line ~442). Duplicate/wrong row deleted from this table; no label changed by this correction, only a stale citation fixed. |
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
| C `lem:pgram` | unit parallelogram, (1,2) and (1,3) | `PgramTiling22.*`/`PgramTiling22Bridge.*`, `PgramTiling52.*`/`PgramTiling52Bridge.*` | (1,2) member **VERIFIED (2026-09-02)** — see the detailed row above. (1,3) member: `PgramTiling52Bridge.lean` (2026-09-02) now has the **same full real-coordinate bridge** (carrier, (C1)-(C4), volume identity, `pgram52_covers` the actual covering) — but this member is cited only in an *untagged* remark (`rem:collarprogram`, no `\lab`), not a separate formally-tracked claim, so there is no independent row to flip; this strengthens that remark's citation without changing the census |
| C cevian seeds | Δ₂ = 16+28 and Δ₃ = 36+63 at (1,2) | `CevianTiling28.*`, `CevianTiling63.*` | VERIFIED |

## Proved on paper, arithmetic core formalized, geometry not

| Paper | Statement | Lean support | Status | What blocks full formalization |
|---|---|---|---|---|
| M `thm:main` | no prime N ≡ 3 (mod 4) outside base-β | `InvariantCore`, `Beeson3NotPrime`, `BaseAlphaBetaPrime`, `IsoAlphaPrime` | PROVED | the invariant's cancellation step is geometric |
| M `thm:fullprime` | the folklore conjecture | all of the above + the companion chain | CONJECTURE | as below |
| C `thm:basebeta-full` | no base-β instance at m = 1 | `BAdjacency`, `Rigidity`, `W2Core`, `MidTriangle`, `SurplusLattice`, `GeneralPillars`, `MasterLemmas`, `Pentagon`, `PentagonLemma`, `AngleArithmetic` | **CONDITIONAL** on the complete-corner-wall hypothesis (companion `hyp:walls`) | **The blocker is NOT formalization.** It is an unwritten mathematical step: that no base corner is starved or broken. The companion's own `rem:cleanfail` calls it "the single highest-value open step in this branch". Note also: of the files listed, only `Pentagon` and `PentagonLemma` are general in (e,f); the rest are per-member instantiations, and `MasterLemmas` contains no e = 1 member at all. |
| C `thm:pgram-e1` | unit parallelogram for all e = 1, f ≥ 2 | construction + exact verifier in `code/rust/tiler` (f = 2…12) | PROVED | the general-f construction is verified per instance, not as a single Lean theorem |
| C `thm:realize12` | (1,2) spectrum: tileable iff m ≠ 1 | seeds VERIFIED; induction skeleton `Collar.two_step` | CONJECTURE | **Scoped precisely 2026-09-04**: the theorem splits into an *existence* half (`N=11m²` realizable for every `m≥2`) and a *non-existence* half (`m=1` excluded, via `thm:basebeta-full`, itself blocked on `hyp:walls` — genuinely open, no route). The existence half is closer than the old note suggested: both induction bases are real, already-VERIFIED `CongruentDissection` witnesses (`Tiling44Bridge.dissection`, N=44=11·2²; `Tiling99Bridge.dissection`, N=99=11·3²; confirmed by direct read of both files), and the abstract two-base induction skeleton `Collar.two_step` is a real, general, already-built tool (`P 2 → P 3 → (∀m≥2, P m → P(m+2)) → ∀m≥2, P m`). What is actually missing, precisely: the induction *step* itself — `∀m≥2, (∃ CongruentDissection of size 11m²) → (∃ CongruentDissection of size 11(m+2)²)` — needs composing a real `Δ_m` witness with a collar (two `PgramTiling22`-shaped columns plus an `m=2`-shaped corner) into one `Δ_{m+2}` witness, and **no general "disjoint union of two `Dissection`s whose carriers partition a bigger region" composition tool exists in the corpus** — `Compose.compose` (checked) is a *refinement* composer (subdivides each macro-tile of one dissection uniformly by the same inner dissection), not a union-of-different-regions composer, which is what the collar step needs. This is real missing infrastructure, not a citation or bookkeeping gap. **First piece built 2026-09-04**: `UnionDissection.unionDissection`/`.unionCongruentDissection` (new) supply exactly that missing primitive — given two `Dissection`s (resp. two same-model `CongruentDissection`s) whose targets' carriers have disjoint interiors and union to a bigger triangle, produces a genuine `Dissection`/`CongruentDissection` of the bigger triangle with `M+N` tiles, `Fin.append`-indexed. `lake build Erdos634.All` clean, no `sorry`. **What remains**: this is the general *tool*, not the collar step itself — actually building `Δ_{m+2}` from `Δ_m` still needs (a) a concrete collar-shaped `CongruentDissection` (two `PgramTiling22`-shaped columns + an `m=2`-shaped corner, real coordinates) and (b) the disjointness/union-carrier hypotheses discharged for that specific geometry, at every `m`. Real, substantial work remains; this session built the reusable tool, not the instantiation. **Correction, 2026-09-05**: worked out the exact `m=2→m=4` geometry by hand (pure translations of `Tiling44`/`PgramTiling22`, verified one coordinate in Lean — `mapDissection`+`AffineEquiv.constVAdd` correctly places `Δ_2^apex`'s apex at the predicted point) — but then found `unionDissection`/`unionCongruentDissection` **cannot actually glue this construction's intermediate pieces**: `Dissection`'s `target` field is `Tri`-only, and neither a `PgramTiling22`-shaped column (a parallelogram) nor the collar as a whole (a trapezoid) is triangular, so `UnionDissection`'s tool, while correctly built, doesn't apply to them. The real route is a flat-list, direct-certificate construction (like `Tiling44Bridge`/`PgramTiling22Bridge` themselves use) for the combined 176-triangle list, not composition of sub-`Dissection`s — a substantial, still-unattempted undertaking, now precisely scoped with the design question resolved. **Placement tool built 2026-09-05**: `TranslateDissection.translateCongruentDissection` (new) rigidly translates a whole `CongruentDissection` by a vector — target, every tile, and the model together, preserving `tiles_congruent` via the new `Tri.Congruent.map_left`. Verified against real data: translating `Tiling44Bridge.dissection` by the hand-derived vector places its apex at exactly the predicted coordinate for `Δ_2^apex` inside `Δ_4`. `lake build Erdos634.All` clean, no `sorry`. This is the placement primitive the flat-list construction needs; still infrastructure, not the construction itself. **Placement geometry checked 2026-09-05, later**: `CollarGeometryM4.lean` (new) verifies, against real coordinate data, all three of the `m=2→m=4` step's non-column pieces exactly as hand-derived — `pgram_scaled_corners` (`PgramTiling22`'s four corners ×2-rescaled land at `(0,0),(88,0),(132,12√15),(44,12√15)`), `apex_copy_pts` (`Δ_2^apex` = `Tiling44Bridge.dissection` translated by `(88,24√15)`, vertices `(88,24√15),(264,24√15)`, apex `(176,48√15)`), `corner_copy_pts` (the corner triangle = `Tiling44Bridge.dissection` translated by `(176,0)`, vertices `(176,0),(352,0),(264,24√15)`). All three match the hand-derivation exactly; `lake build Erdos634.All` clean, no `sorry`. Only the two column pieces (four translated `PgramTiling22` copies) remain unchecked before the full containment/disjointness/area-sum proof can be attempted. **Piece-level route confirmed 2026-09-05, later still**: `piece0_scaled_pts` checks `PgramTiling22`'s first raw piece (of 22) rescaled `×2` via the homothety about the origin, landing at `(0,0),(16,0),(22,6√15)` — consistent with the aggregate corner check and confirming the piece-level approach (needed since `PgramTiling22` has no `CongruentDissection` wrapper) works correctly through the same certificate-transfer layer. `lake build Erdos634.All` clean, no `sorry`. All placement geometry needed for the `m=2→m=4` step is now confirmed correct at both the aggregate and piece level; only the (much larger) containment/disjointness/area-sum certificate for all 176 pieces remains. **First disjointness proof done 2026-09-06**: `CollarDisjointM4.apex_corner_disjoint` proves `Δ_2^apex` and the corner triangle have disjoint interiors, separated by the horizontal line `y=24√15` (`Δ_2^apex`'s base = the corner triangle's apex height) — the same "separating-affine-functional" pattern (`CertGeom.interiors_disjoint_of_separating`) every certificate in this project already uses, now composed with the `y`-coordinate as an affine functional (`yFun`/`yAff`, new, reusable) and `Tri.carrier_subset_halfplane_affine` (pre-existing). `lake build Erdos634.All` clean, no `sorry`. First of many region-pairs the full 176-piece certificate needs; the same pattern applies to the rest. **Uniform column bound built 2026-09-07**: `piece_yBound` proves every one of `PgramTiling22`'s 22 raw pieces has `y ∈ [0, 6√15]` (before rescale/translation), derived once via convexity (`carrier_yBound` from the four corners, composed with the pre-existing `pieceTri_subset_carrier`) rather than per-piece — after the `×2` rescale and a column's own translation this becomes `y ∈ [0, 24√15]`, matching `apex_corner_disjoint`'s separating line exactly, so this one fact will cover *every* column piece against `Δ_2^apex` at once (not 88 separate checks). `lake build Erdos634.All` clean, no `sorry`. **Composed through 2026-09-07, later**: `column_piece_apex_disjoint` finishes the composition — a raw `PgramTiling22` piece, scaled ×2 about the origin then translated by any vector with `y ∈ {0, 12√15}` (covering both halves of both columns), is disjoint from `Δ_2^apex`. Covers all `88` column pieces against the apex in one theorem. `lake build Erdos634.All` clean, no `sorry`. Roughly half of `Δ_4`'s 176-piece disjointness certificate (apex-vs-column) is now done. **Within-column disjointness done 2026-09-07, later**: `DissectionMap.mapTri_interiors_disjoint`/`.mapTri_mapTri_interiors_disjoint` (new, general — extracted from `mapDissection`'s own proof) show an affine equivalence (or a composition of two) preserves interior-disjointness; `CollarDisjointM4.placed_pieces_interiors_disjoint` composes this with `PgramTiling22Bridge.pieces_interiors_disjoint` to get within-copy disjointness for any placed column, with no new separating-line argument. `lake build Erdos634.All` clean, no `sorry`. **Within-corner/within-apex done 2026-09-07, later still**: `translated_tiling44_interiors_disjoint` transports `Tiling44Bridge.dissection.interiors_disjoint` through any translation, closing both cases at once (instantiate at `(88,24√15)` for `Δ_2^apex`, `(176,0)` for the corner). `lake build Erdos634.All` clean, no `sorry`. **Corner-vs-column done 2026-09-07, next**: `column_piece_corner_disjoint` builds the slanted separating functional `g(x,y) = 24√15·x − 88·y` (hand-derived from the shared diagonal edge) and proves every placed column piece (all 88, both columns) is disjoint from the corner triangle — the corner has `g ≥ 4224√15`, every column piece has `g ∈ [2112√15·j, 2112√15·(j+1)]` for column `j ∈ {0,1}`, so this one line separates the corner from both columns at once. `lake build Erdos634.All` clean, no `sorry`. **Disjointness for all 176 pieces of `Δ_4` is now fully done.** **Containment started 2026-09-07, next**: `CollarContainM4.lean` defines `Δ_4` as a real `Tri` (`delta4`, vertices `(0,0),(352,0),(176,48√15)`) and proves `apex_subset_delta4` — `Δ_2^apex` sits inside `Δ_4`, since `Δ_2^apex`'s own vertices turn out to be the midpoints of two of `Δ_4`'s edges (plus `Δ_4`'s own apex), so membership follows from `midpoint_mem_segment`/`segment_subset_convexHull` directly, no half-plane argument needed. `lake build Erdos634.All` clean, no `sorry`. **Corner containment done too, same turn**: `corner_subset_delta4` — the corner triangle's vertices are also midpoints/vertices of `Δ_4`'s own edges, so the same shortcut applies, no half-plane argument needed for this piece either. `lake build Erdos634.All` clean, no `sorry`. **Column containment done 2026-09-08, later**: `column_piece_subset_delta4` builds the general half-plane route (`lFun`/`rFun`, `Δ_4`'s left/right leg functionals, plus `mem_delta4_of_bounds` via the pre-existing `CertCoord.mem_carrier_of_dets`) and closes containment for every one of the 88 column pieces. `lake build Erdos634.All` clean, no `sorry`. **Containment for all 176 pieces of `Δ_4` is now fully done**, alongside the already-complete disjointness. Only the area-sum identity remains before the `CongruentDissection 176` witness can be assembled. **Area-transport built 2026-09-08, later**: `CollarAreaM4.lean` (new) proves the general fact `detTri (mapTri e T) = det(e.linear) * detTri T` for any affine equivalence `e` (via a new `edgeMap_mapTri`), then specializes it to the two placement maps actually used — `detTri_transEquiv` (translation, `det=1`, area exactly preserved — covers the apex/corner pieces) and `detTri_homothetyEquiv` (ratio-`r` homothety, `det=r²`, area scaled by `r²` — covers the ratio-2 column pieces, area ×4, via a new `homothety_linear_det` proved from `AffineMap.homothety_linear`). `lake build Erdos634.All` clean, no `sorry`. **Still missing**: the per-region area sums in Lean (apex/corner each contribute `4224√15` via translation-invariance of `Tiling44Bridge`'s own area identity; each of the 4 column copies contributes `4×528√15=2112√15` via the homothety scaling of `PgramTiling22Bridge`'s own area identity — confirmed correct by hand, total `16896√15`, matching `delta4`'s own `detTri` exactly, but not yet stated as Lean theorems), and the combined flat `Fin 176 → Tri` piece list (not started) needed to state the single sum `∑ i, |detTri (tile i)| = |detTri delta4|` that `AreaDet.area_identity_of_det` consumes. **Per-region sums done 2026-09-08, later still**: `apex_area_sum` (any translated copy of `Tiling44Bridge`'s 44 pieces sums to `Tiling44Bridge`'s own target area exactly — one theorem covers both apex, `v=(88,24√15)`, and corner, `v=(176,0)`) and `column_area_sum` (one translated, ×2-homothety-scaled copy of `PgramTiling22Bridge`'s 22 pieces sums to `4×` its own target, `2112√15` per copy) both proved and landed. `lake build Erdos634.All` clean, no `sorry`. This confirms in Lean (not just by hand) that the total is `4224√15 (apex) + 4224√15 (corner) + 4×2112√15 (columns) = 16896√15`, matching `delta4`'s own `detTri`. **Still missing**: the combined flat `Fin 176 → Tri` piece list (concatenating 1 apex tile + 1 corner tile + 4×22 column tiles) and the single sum identity stated over it, which alone is what `AreaDet.area_identity_of_det` consumes — the per-region facts above are ingredients, not that statement itself. **Flat piece list + area-sum identity done 2026-09-08, later still**: `CollarPiecesM4.lean` builds `delta4Pieces : Fin 176 → Tri` (the actual flat piece function, apex ++ corner ++ four 22-piece column copies, via `Fin.append`) and proves `delta4_area_sum : ∑ i, |detTri (delta4Pieces i)| = |detTri delta4|` — exactly `AreaDet.ofDetCertificate`'s (C4) hypothesis, closed. Needed one new general combinator (`sum_fin_append`, splits a sum over `Fin.append` back into its two component sums — no ready-made Mathlib lemma covers it) plus three small numeric closures. `lake build Erdos634.All` clean, no `sorry`. **This closes all three certificate ingredients for `Δ_4` as a `Dissection 176`** — (C2) containment, (C3) disjointness, (C4) area — each proved, in Lean, as a separate fact. **What remains**: the three ingredients were proved with different hypothesis shapes (`CollarContainM4`/`CollarDisjointM4`'s column facts are `List`-membership-indexed, `t ∈ PgramTiling22.tiles`, not `Fin`-indexed like `delta4Pieces`; the apex/corner containment facts are stated as whole-region-subset, not per-piece) — reconciling all of them into the single `Fin 176`-indexed `∀ i, ...`/`Pairwise`/`∑` form `AreaDet.ofDetCertificate` actually needs, to call it and produce the real `CongruentDissection 176` witness, is real remaining work, not yet attempted. Only after that concrete `m=4` witness exists would generalizing to `∀m≥2` (needs an `m=3` base too, via `Collar.two_step`) be the next honest step. **Bug found and fixed, containment reconciled, 2026-09-08, later still**: `CollarPiecesM4.lean`'s `colVec` used translation vector `(88j, 12√15·h)`, but the hand-derived geometry is `w=(88j+44h, 12√15·h)` — the `+44h` term was missing (harmless to `delta4_area_sum`, since translation preserves area for any vector, but load-bearing for containment). Fixed. New file `CollarPieceContainM4.lean` then bridges the two remaining shape mismatches for the (C2) containment hypothesis `AreaDet.ofDetCertificate` needs: `apexPieceAt_subset_delta4`/`cornerPieceAt_subset_delta4` (per-piece containment, via a new general `mapTri_subset` composed with the existing region-level `apex_subset_delta4`/`corner_subset_delta4`) and `columnPieceAt_subset_delta4` (bridges `column_piece_subset_delta4`'s `List`-membership index to `Fin`, discharges its bound hypotheses at the corrected `colVec`). `lake build Erdos634.All` clean, no `sorry`. **Containment is now fully available at `delta4Pieces`'s own `Fin 176` indexing.** **Still missing**: the same reconciliation for (C3) disjointness (`CollarDisjointM4`'s facts are also `List`-membership-indexed for columns), plus the index bookkeeping to turn all of it into one `Pairwise`-over-`Fin 176` statement — genuinely the larger remaining piece. **Last region-pair closed, 2026-09-08, later still**: `CollarDisjointColM4.lean` — two column pieces from *different* `(j,h)` positions among the four column copies were never checked against each other, the one genuinely new geometric case in the whole construction (needed its own separating functional, not a port). New functional `hFun := 12√15·x − 44·y` (matching column `0`'s own slanted right edge, invariant under the `h`-shift direction) gives `column_j_disjoint`; the pre-existing `yAff` pattern gives `column_h_disjoint` (same column, different half); `columnPieceAt_disjoint` combines both. `lake build Erdos634.All` clean, no `sorry`. **Every pair of the 6 append-blocks (apex, corner, 4 column copies) — within-block and cross-block — now has a disjointness fact.** **Still missing**: assembling all of it (plus the already-done per-piece containment from `CollarPieceContainM4.lean`) into the single `Pairwise (fun i j : Fin 176 => ...)`/`∀ i, ... ⊆ ...` statement `AreaDet.ofDetCertificate` literally needs — dispatching an arbitrary `i ≠ j : Fin 176` to the right one of these ~9 lemmas by index case-split is index bookkeeping, not new geometry, but nontrivial. **Assembled, 2026-09-08, later still**: `CollarAssembleM4.lean` — two general combinators (`forall_fin_append`, `pairwise_fin_append`) chained through `delta4PiecesAux`'s six-block tree close both `hsub` (`delta4Pieces_subset_delta4`) and `hdisj` (`delta4Pieces_pairwise`, via a new `disjoint_of_subset` bridging containment to disjointness plus one new fact per block-pair). **With `hsub`, `hdisj`, and `hdet` (`delta4_area_sum`) all in hand, `AreaDet.ofDetCertificate` assembles `delta4Dissection : Dissection 176` — a genuine, complete, Lean-checked flat dissection of `Δ_4` into 176 triangles.** `lake build Erdos634.All` clean, no `sorry`. This is real: a specific 176-triangle `Dissection` object, with (C2)/(C3)/(C4) all discharged, exists in the kernel — the concrete `m=4` witness for the `m=2→m=4` step. **Still not a label flip**: `thm:realize12` needs the full `∀m≥2` statement (this closes one induction step for one `m`; an `m=3` base and its own step remain), and `delta4Dissection` is not yet wrapped as a `CongruentDissection 176` (needs `model`/`tiles_congruent`, not yet attempted — the pieces come from two different congruence classes, `Tiling44`-shaped and `PgramTiling22`-shaped-then-scaled, so "congruent to one fixed model" needs checking whether these are actually all mutually congruent, which is not obvious and not yet verified). **Settled, 2026-09-08, later still**: yes, they are congruent — `Tiling44`'s model has squared sides `{256,576,1024}` (sides `16,24,32`), `PgramTiling22`'s raw model has squared sides `{64,144,256}` (sides `8,12,16`, exactly half), and the column pieces are already placed via the same `×2` homothety this construction uses throughout, so the scaled model matches `Tiling44`'s exactly, same cyclic edge order, no relabelling. `CollarCongruentM4.lean` builds the full congruence chain and assembles **`delta4CongruentDissection : CongruentDissection 176`** — the complete witness, all four certificate ingredients (C1)–(C4) discharged. `lake build Erdos634.All` clean, no `sorry`. This is a concrete, Lean-checked realization of `N=176=11·4²`, the `m=2→m=4` step of `thm:realize12`'s existence half, fully assembled — going beyond the `m=2` (`N=44`) and `m=3` (`N=99`) bases this project already had. **Still not a label flip**: `thm:realize12` is the general `∀m≥2` statement (this closes one induction step for one `m`; an `m=3→m=5` base-plus-step, or the step proved in general rather than just instantiated at `m=2`, would still be needed for the full statement — no route to genericize the hardcoded coordinates like `88`, `24√15` etc. to arbitrary `m` has been attempted). **Scoping pass, 2026-09-08, next**: checked several other CONJECTURE/PROVED rows for a smaller reachable target before committing to the comparably-sized `m=3→m=5` repeat; none found (each is either already accounted for, blocked on a named standing blocker, or itself a multi-iteration undertaking — see `private/VERIFY_PLAN.md`). No Lean changes this pass. **Important correction, 2026-09-08, next**: before starting `m=3→m=5`, checked whether `delta4CongruentDissection` (`N=176`, `m=4`) was actually new coverage — **it was not.** `Tiling44Bridge.exists_dissection_mul_sq` (pre-existing, long before this session, a direct application of `Ladder.ladder` to `Tiling44Bridge.dissection`) already gives a `CongruentDissection (m²·44)` for *every* `m > 0`, and `ElevenMBridge.exists_dissection_11_mul_sq` (also pre-existing, commit `587be94`) already packages this (plus the `m=3` analogue) as "`N=11m²` realizable for every `m` with `2∣m` or `3∣m`" — which includes `m=4` for free. **The entire `CollarGeometryM4`–`CollarCongruentM4` arc (9 files, this session) reconstructed a result that one existing `Ladder.ladder` application already gave.** This does not make that work *incorrect* — `delta4CongruentDissection` is a genuine, independently-verified `CongruentDissection 176`, and the collar-decomposition *technique* (attaching a fixed-shape collar around an existing witness) is exactly the shape `Collar.two_step`'s general `∀m, P m → P(m+2)` step will eventually need — but it was **not new coverage** of `thm:realize12`'s existence half, since `m=4` (divisible by `2`) was already reachable via `Ladder.ladder`, with no new construction required. **What `Ladder.ladder`/`exists_dissection_11_mul_sq` do NOT cover**: any `m` coprime to `6` — `5, 7, 11, 13, 17, 19, 23, 25, ...` — since scaling only ever reaches multiples of the base `m`. Those are the genuinely open cases, and only a real `+2`-style step (or some other route) closes them — a single further instance (e.g. `m=3→m=5`, since `5` is not a multiple of `2` or `3`) would be the first *actually new* case, at the same construction cost this session's arc already paid once. |

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
| V `cor:basedi2e` | The base trichotomy and dichotomy without separation | `CChord.base_trichotomy_2e`, `.base_dichotomy_2e` — see full row below, VERIFIED 2026-09-03 |
| C `cor:ptwo` | A uniform two-case side problem | `side_p_le_two`, `Frontier.floor_eq_two` | **VERIFIED 2026-09-08.** `side_p_le_two` only gave the upper bound `p ≤ 2` (its own docstring noted the matching equality `⌊(f-1)/e⌋=2` was checked computationally, 126003 close pairs, not proved). `floor_eq_two` (new) closes the equality for real: the upper bound via `side_p_le_two` instantiated at `p := (f-1)/e`, the lower bound via the paper's own one-line argument (`f > 2e ⟹ (f-1)/e ≥ 2`, `Nat.le_div_iff_mul_le`). Matches `cor:ptwo`'s own stated conclusion word for word. `lake build Erdos634.All` clean, no `sorry`. |
| C `cor:walls16` | corollary | `pincer_window_four` |
| C `cor:wallsf2e` | The walls form at $e=1$, $f\ge3$ | `SideNoB.side_no_b_uncond`, `SideNoB.side_quantized`, `SideNoB.c_corner_forces_side_a` | *(`c_corner_forces_side_a` is `SideNoB.lean`'s own side-parameter fact — `0 < f·p → 1 ≤ p`, i.e. a `c`-corner fails `hyp:walls`'s `p=0` side condition — genuinely relevant here, not a mis-citation. **Note 2026-09-04**: the stale cross-reference to `lem:shadow`'s row was removed; `lem:shadow`'s own citation was corrected to `OrderForcing.strips_tall`/`.shadow_footage_e1` and no longer mentions this theorem at all, so the old pointer was dangling.)*
| C `lem:anglethreshold` | The angle threshold | `cos_alpha_closed` |
| C `lem:avgen` | The $\alpha$-vertex gap, general | `alpha_vertex_gap_gen` |
| C `lem:basedi` | The thick base dichotomy | `base_dichotomy_thick` |
| C `lem:basetri` | the base's three edge decompositions at a separated member | `CChord.base_trichotomy` | VERIFIED — the declaration is the statement: any `(x,y,z)` solving the base walk at a separated member is one of the three. Enumerated for every separated coprime pair with `f < 24`: exactly those three, no others |
| C `rem:closepairbase` | close pairs admit further decompositions with `y > e` | none | HEURISTIC — a per-member computation; finiteness follows from the walk equation but the count is not proved uniformly |
| C `lem:cchord` | c-chord dichotomy | `CChord.c_chord_dichotomy` |
| C `lem:ccorner` | The $c$-corner is rigid | `partner_unique` | **Checked 2026-09-08**: needs chord endpoints, junction figures, reflected-partner exclusion via `2γ>π` — deep tile-placement-layer territory, no route found. `partner_unique` (`PentagonLemma.lean`) covers only one arithmetic sub-fact cited mid-proof. |
| C `lem:census` | The vertex census | `vertex_census` | PROVED — the three corner-balance equations (v1..v4, n1, n2) are still hypotheses of `vertex_census`, and that global corner-incidence double count is still not done. **Partial closure 2026-09-02**: the lemma's own quoted premise — "the base corners fill uniquely as `{β}` and the apex as `{3α}`" — is no longer an assumption at either corner. `TileAt.congruentDissection_base_corner_counts` and `.congruentDissection_apex_counts` prove both, for a real `CongruentDissection`, by composing three pieces that existed separately and had not been assembled: `tile_angle_dichotomy_at_vertex` (every tile touching a vertex is corner-type or straight, never `0`/`2π` — new this session), `CongruentAngles.congruent_corner_angles` (a congruent tile's own corner angle is one of the model's three — pre-existing, unused for this), and `TilePlacement.base_corner_counts`/`.apex_counts`/`.corner_multiplicities` (the arithmetic, pre-existing, previously fed a hypothesis instead of a derivation). This is a real premise of `lem:census`, not the lemma's conclusion — the label stays PROVED |
| C `lem:charge` | The mirrored piece is charged | `mirrored_left_junction`, `escape_charge` |
| C `lem:chord` | The chord at the last junction | `tile_contact_face`, `contact_is_edge` |
| C `lem:collar` | Collar decomposition | `collar_cells` |
| C `lem:eastfan` | The east fan at the fork is forced | `straight_junction_gamma_bound`, `straight_junction_cases` |
| C `lem:firstrun` | First-run orientation | `PentagonLemma.partner_unique`, `OrderForcing.first_run_kill`, `gamma_far_absorbing` | **Checked 2026-09-08**: needs chord endpoints (corner tile's `b`-edge as a two-boundary-point chord) and junction-figure exclusion — deep tile-placement-layer territory, no route found. The three cited declarations are each real arithmetic sub-facts the proof invokes mid-argument, not the geometric claim itself. |
| C `lem:jbline` | The $jb$-line partition | `partition_jb` |
| C `lem:ladder` | Descent identities and the ladder | `descent_ident`, `sinb_ident`, `ladder_no_base` |
| C `lem:monochotomy` | the only decomposition of `c` at a thick member is the single `c` | `CChord.c_chord_unique_thick` | VERIFIED — the lemma now states only the arithmetic, which is the declaration; its geometric consequence was split into `rem:monochain` |
| C `rem:monochain` | the `f`-`a` branch is an `e=1` phenomenon; thick-member forks are forced | `CChord.c_chord_unique_thick`, `.c_chord_dichotomy` | PROVED — a statement about the corner chain's forks, which needs the chain as an object; the arithmetic under it is VERIFIED |
| C `lem:noapexline` | The chain never needs the apex line | `chain_needs_small_lines` |
| C `lem:parity` | Straight-figure parity | `census_parity` |
| C `lem:shadow` | The shadow at a $c$-corner | `strips_tall`, `shadow_footage_e1` |
| C `lem:sidequant` | Thick-side quantization | `side_no_b_uncond`, `side_quantized`, `SideNoB.side_a_quantized` | **VERIFIED 2026-09-08.** `side_no_b_uncond` and `side_quantized` each existed, and each one's own docstring described the bridge between them in prose (substitute `Q=0` into the `f³`-scale walk, divide by `f`, reach `side_quantized`'s `f²`-scale hypothesis) — but that bridge was never assembled as Lean. `side_a_quantized` (new) closes it: from the `f³`-scale walk plus the `γ`-trap, concludes `f ∣ P` directly, matching the lemma's own text word for word. `lake build Erdos634.All` clean, no `sorry`. |
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
| C `thm:e1cascade` | The cascade closes every initial-block-1 configurati | `cascade_reaches`, `reversal_covers`, `partition_2b` | **Checked 2026-09-08**: a three-lemma cascade argument (chord induction, `f`-`a` branch, reversal), deeply geometric throughout — no route found. |
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
| C `prop:n1fromwalls` | proposition | | **Checked 2026-09-08**: its entire two-line proof depends on `lem:ccorner` ("the column `(0,e,2e)` forces `p≥1` on each equal side") — blocked transitively, same reason. |
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
| M `cor:ladder` | the realizable set `S(e,f)` is closed upward under the ladder | `Erdos634.Realizable.mem_realizableSet_mul`, `realizableSet_eq_multiples` | PROVED — **two of the corollary's three clauses are now VERIFIED**, and the blocker is exactly the third. `Realizable.scaleTri` is the scale operation (homothety about the triangle's own first vertex); because a homothety fixes its centre, `scaleTri_scaleTri` composes **on the nose**, which is what converts 'apply `thm:ladder` at `k` to the scale-`m` target' into a statement about the scale-`km` target. `Cut T t N` is the realizability predicate and `cut_scale` is `thm:ladder` in those terms. Clause 1, `m ∈ S ⇒ km ∈ S`, is `mem_realizableSet_mul`. Clause 2, '`S` is the union of the multiples of its minimal elements', is `realizableSet_eq_multiples` (via `exists_minimal_divisor`, strong induction on the divisibility order). **Remaining blocker, named: clause 3**, '`1 ∈ S` is *not* implied by `S ≠ ∅`'. That is a non-implication and needs a witness family, which is `cor:elevenm` — `(e,f)=(1,2)`, where `1 ∉ S` is the 135-node exhaustion and `2,3 ∈ S` are the 44- and 99-tilings. So `cor:ladder` cannot pass Rule 5 before `cor:elevenm` does. **Corrected 2026-09-02**: the old text here ("gated on `volume (Tri) = |det|/2`, absent from this corpus and Mathlib") was itself stale — that gap is long closed (`AreaDet.volume_eq_det_mul`, and now also `AreaDet.volume_stdCarrier_half` for non-`Tri` targets). `cor:elevenm`'s `2,3 ∈ S` witnesses, its `N=11m²` consequence, and (in general form) its primitivity are all now proven (`Tiling44Bridge.dissection`, `Tiling99Bridge.dissection`, `ElevenMBridge.exists_dissection_11_mul_sq`, `Realizable.isMinimal_of_prime_of_one_not_mem`) — the *only* thing left for both `cor:ladder` and `cor:elevenm` is the single negative fact `1 ∉ S` (the 135-node engine exhaustion), permanently blocked on the missing certified-search format (see the dedicated scoping note below, reconfirmed 2026-09-02 by reading `code/engine/cengine.cpp` directly — a from-scratch verified-backtracking-search project, not a quick lemma). |
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
| C `prop:orientmono` | a boundary `a`-run's orientations are monotone; ≤1 `{3α,2β}` junction | `Inflation.BG_GB_forbidden`, `.orient_monotone`, `.AAB_iff_transition` | **STALE, WRONG "VERIFIED" claim — corrected 2026-09-02.** The paper's own `\lab{}` tag for `prop:orientmono` is `PROVED`, not `VERIFIED` (checked directly in erdos-634-companion.tex). The real, current status is split across two rows further down: `prop:orientmonobdy` (the target-side half) is genuinely VERIFIED, but `prop:orientmono` itself (the inflated-tile-side half, line ~930) is still PROVED, blocked on an inflated-tile `Dissection` object that doesn't exist yet. This row's "VERIFIED" was never true of the paper statement — do not treat it as done. |
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
| C `rem:pinbuffer` | cost of the pin configuration | `PinLemma.pin_forces_single_alpha`, `PinBuffer.buffer_overflow_b_is_gap`, `.buffer_dichotomy`, `.overrun_amounts` | PROVED — the cited cores are VERIFIED; the configuration statement is geometric. **Citation completed 2026-09-04**: the row previously listed only `buffer_dichotomy`/`.overrun_amounts`; the paper's own proof (`erdos-634-companion.tex:2293-2301`) also names `PinLemma.pin_forces_single_alpha` (the single-`α`-wedge fact) and `PinBuffer.buffer_overflow_b_is_gap` (the `b`-chirality death), both pre-existing and matching. No label change — the geometric configuration itself remains unformalized either way. |
| C `prop:selfsim` | the descent is self-similar | none | PROVED — **checked 2026-09-02: the old blocker text was wrong.** This is not about a scale map on dissections (that's now built: `Realizable.scaleTri`); it is a specific trigonometric vertex-position claim about the base-β wall chain (companion.tex:3431-3447): a tile `Z` laying a `c`-edge between junctions `J'`/`J` has its third vertex `W` exactly on the chord through `J`, via the identity `b·cos(α/2) = c·cos(3α/2)` from `lem:apexid`. Genuinely blocked on formalizing that identity chain (`lem:apexid`, `thm:apexconfig`) — real trigonometric geometry, not reachable by anything built this session. |
| C `lem:rowwords` | boundary words at scale k | none | PROVED — depends on the row induction below |
| C `lem:rowp0` | the corner tile | none | PROVED — planar placement argument. **Note corrected 2026-09-02**: a tile-placement layer now exists (`TileAt.lean`), but it does not reach this row — `Dissection.target_vertex_mem_badSet` proves a target vertex always sits on the bad set, so `tileAt` cannot identify 'the corner tile' at all; that needs a different argument (see `TileAt.lean`'s note in this file's foot). Still blocked, for a now-precise reason |
| C `lem:rowq0` | the first partner, and the parallelogram | `Geometry.Dissection.wall_two_sided`, `.edge_point_not_interior`, `Inflation.a_unsplittable`, `BaseBetaCorners.pi_vertex_gamma_le_one`, `ForcedRow.pgram_x` | PROVED — **citation added 2026-09-06**: row previously listed no citation; the paper's own proof (`erdos-634-companion.tex:3833-3849`) cites these five, all pre-existing (`wall_two_sided`/`edge_point_not_interior` are genuine `Dissection`-level theorems in `WallChain.lean`; the rest as named) and matching. Not independently checked whether these fully discharge the lemma's own real-dissection instantiation ("P₀'s `a`-edge... is matched by a single tile Q₀" — the row/junction *object* itself, `P_0`/`Q_0`/`Y_0`, still has no `Dissection`-level definition) — this citation fix does not by itself justify a flip; a real Rule 5 check against the full statement is separate future work |
| C `lem:rowp1` | the row advance at Y0 | none | PROVED — planar placement argument |
| C `prop:slotdichotomy` | the slot dichotomy | `ForcedRow.overrun_x`, `RogueChord.delta_identities` | PROVED — **citation added 2026-09-06**: row previously listed no citation; the paper's own proof (`erdos-634-companion.tex:3866-3880`) cites these two, both pre-existing and matching (`overrun_x`: the rogue branch's overhang `Δ=c-a`; `delta_identities`: its arithmetic). Planar placement argument otherwise — the junction/row structure itself has no `Dissection`-level definition |
| C `cor:rowinduction` | the induction step | none | PROVED — assembles the four row lemmas above |
| C `prop:rellattice` | `Λ(e,f)` is free of rank two on `v₁ = (f,0,−e)`, `v₂ = (e,f,−f)` | `Primitives.rel_v1`, `.rel_v2`, `.rel_b_mult`, `.rel_param`, `.rel_span`, `.rel_indep` | VERIFIED — the generators are relations, they span (subtract the right multiple of `v₂` and apply the `b`-free case), and they are independent. The interface-floor clause was split into `prop:interfacefloor` |
| C `prop:interfacefloor` | a nonzero relation has one-sided length `≥ f·min(a,b)`, so short interfaces match | `InterfaceFloor.interface_floor` | PROVED — **citation and note corrected 2026-09-02**: the length bound itself is not an open arithmetic gap, it is proved and VERIFIED as `prop:relfloor` (`InterfaceFloor.interface_floor`, `.floor_attained`, `.v1_relation`); the previous citation (`Primitives.rel_span`) and the claim 'not yet proved' were both stale. What blocks this row is only the second clause — 'so short interfaces match' quantifies over interfaces of a real tiling, and maximal straight interfaces of a dissection are not objects of the Lean development |
| C `prop:cevianatom` | cevian reduction: two tiles and an atom | `Primitives.two_tiles_plus_atom` | PROVED — **citation corrected 2026-09-04**: previously cited `CevianSplit.split_count`/`.cevian_foot`, which prove a *different*, two-piece split (scaled tile + west piece `W_m`, `split_count_m`'s shape) — related but not this row's actual identity. The paper's own proof (`erdos-634-companion.tex:4570`) cites `\texttt{two\_tiles\_plus\_atom}` in `lean/Primitives.lean`, which exists exactly as `m²N₁ = 2(fm)² + bm²` (matching the displayed identity word-for-word), plus `west_split` for the intermediate `W_m = (fm)`-tile + atom step. The counting identities are pure arithmetic (`ring`); the geometric reduction (that the cevian and wall actually cut the target into these three pieces) remains unformalized, so the row correctly stays PROVED, not VERIFIED — only the citation was wrong. |
| C `lem:wpgram` | the W-parallelogram at e=1 | `Primitives.w_slab_counts` | PROVED — **citation corrected 2026-09-04**: previously cited `PgramTiling22.pgram22_certificate`, a specific-member (`f=2`) full tiling certificate the paper's own proof text never mentions. Checked `erdos-634-companion.tex:4589-4597` directly: the paper's own proof cites `\texttt{w\_slab\_counts}` in `lean/Primitives.lean`, general in `f`, and `w_slab_counts` exists exactly as described — the slab-count arithmetic identity `2f²−1 = f·a+b` (with `a=f`, `b=f²−1`) and `2(f·f+(f²−1)) = 2(2f²−1)`, for every `f`. This is the *arithmetic core only*: the lemma's actual claim ("admits a tiling by `2(2f²−1)` tiles, every interface a full straight segment") is a geometric covering fact `w_slab_counts` does not touch, so the row correctly stays PROVED, not VERIFIED — but now cites the paper's own general-`f` declaration rather than an unrelated one-member certificate. **Feasibility scoped, 2026-09-09**: checked whether an explicit-coordinate route (the `ℤ[√15]`-style certificate every fixed-member construction in this corpus uses — `Tiling44Bridge`, `PgramTiling22Bridge`, etc.) generalizes to arbitrary `f`. It does not obviously: those certificates work because a *specific* `(e,f)` gives `cos β`/`cos α` a fixed algebraic form in one fixed radical (`√15` throughout this corpus); at general `f`, `cos α = (2f²−1)/(2f²)` (from `BaseBetaE1`'s law-of-cosines identity, `e=1`) varies with `f`, and there is no reason the resulting `cos β`/`sin β` stay expressible in one fixed extension field uniformly in `f` — each `f` could need its own radical. The more promising route, not yet attempted: an **abstract vector/`Tri` construction** — build the "c-glued two-tile brick" as one parallelogram directly from the tile's own edge vectors (no explicit numeric coordinates needed), then tile the `f×1`/`1×b` grid by pure **translation copies** of that brick, following the same abstract-grid pattern `Subdivision.ladderDissection` already uses for `thm:ladder` (general in `k`, no explicit coordinates). **Abstract brick built, 2026-09-09, later**: `ReflectBrick.lean` — `reflectThroughEdge` point-reflects a general `Tri` through one edge's midpoint (via Mathlib's `AffineEquiv.pointReflection`, no coordinates), and `carrier_union_reflectThroughEdge1` shows the triangle glued to its own reflection through edge `(1,2)` exactly tiles `placeMap T '' stdSquare` (the affine image of the unit square) — reusing `AreaDet`'s pre-existing `stdCarrier_union_stdCarrier2` (the unit square's own diagonal split) rather than a hand-rolled argument. This is the "c-glued two-tile brick" the paper's proof names, in fully general form (any `Tri`, not one fixed member). **Still needed for the full construction**: tiling the `f×1`/`1×b` grid with translation copies of this brick, and connecting the abstract brick back to the actual `(2,3,4)`-type tile's own vertex data (this file is fully general in `T`, doesn't yet specialize to the base-β tile). **Checked, 2026-09-09, later**: `Dissection`'s `target` field (and `ConvexCover.ofCertificate`'s `target` argument) is typed `Tri`, not a general convex set — confirmed by reading `Dissection.lean` and `ConvexCover.lean` directly — so `UnionDissection`'s tools cannot wrap the brick itself (a parallelogram, not a `Tri`) as a `Dissection`, exactly the restriction that blocked the `m=2→m=4` collar step's own parallelogram pieces. `PgramTiling22Bridge` solved this for its own one fixed parallelogram by building a **separate, parallel framework** outside `Dissection` entirely (`carrier_eq_image`, `covers_of_volume`, its own certificate checks) rather than reusing `Dissection`/`UnionDissection`. The general-`f` grid tiling needs the analogous parallel framework, generalized — real, substantial remaining work, not a quick reuse of what exists. **De-duplicated, 2026-09-09, later still**: `CoversGeneral.covers_of_volume_general` extracts the measure argument `ConvexCover.covers_of_volume` and `PgramTiling22Bridge.covers_of_volume` both separately proved (the latter's own docstring already noted "none of which was actually triangle-specific"), over any convex-compact-positive-interior-finite-volume `Set Plane`, not just `Tri` — `ConvexCover.covers_of_volume` is now a one-line corollary. This is real reusable infrastructure for covering a non-`Tri` target without hand-deriving the argument again, directly relevant to `lem:wpgram`'s eventual grid; the containment/disjointness/area-sum hypotheses it still needs for that specific grid are not yet built. **Translation transport built, 2026-09-09, later still**: `ReflectBrickTranslate.lean` — `reflectThroughEdge_mapTri` (commutes with any affine equivalence) specialized to translation gives `carrier_union_reflectThroughEdge1_translate`: gluing a translated tile to its own reflection is exactly the translated brick (simple vector addition), not an independently-constructed congruent one. This is what placing brick copies at grid lattice positions needs. **Still not started**: the actual grid index set (general `f`: `f` slabs of height `a` + one slab of height `b`), containment of each translated copy in the big parallelogram, pairwise disjointness between distinct lattice positions (needs a separating-functional argument per adjacent pair, the same pattern the `m=2→m=4` collar work used repeatedly), and the area-sum identity via `CoversGeneral`. |
| C `thm:addlaw` | addition law | `Primitives.add_count` | PROVED — **checked 2026-09-02**: `Compose.compose` (general composition on dissections) and `Realizable.scaleTri` (the scale map) both exist now, but this row needs much more than either alone — the proof cuts a trapezoid by a line parallel to a leg, splits it into an upright scale-`m₂` triangle plus a parallelogram, and tiles the parallelogram via `prop:widecol`/`thm:pgram-e1` (both themselves blocked, parallelogram targets, see `lem:pgram`'s row). Genuinely blocked on that placement geometry, not on composition/scaling. **Citation added 2026-09-04**: the row previously listed no citation at all; the paper's own proof (`erdos-634-companion.tex:4735`) cites `add_count`, the count bookkeeping, pre-existing in `Primitives.lean` — the one piece that is pure arithmetic. |
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
| C `lem:anglethreshold` | `cos α`, `cos β`, `cos γ` in closed form, and condition (P4) | `AngleThreshold.cos_of_sides`, `.cos_alpha_closed`, `.cos_beta_closed`, `.cos_gamma_closed` | **STALE, corrected 2026-09-02 — see the row below (line ~562), which is the current, accurate entry: this triple is VERIFIED (real `cornerAngle` statements, not just the cross-multiplied polynomial form in `Frontier.lean`).** (P4) is split into `rem:anglethreshold`, still blocked (no Lean notion of the search's uncovered region). |
| C `lem:pentagon` | the middle region of the `(0,e,2e)` walk admits no tiling | `Pentagon.no_partition` | the declaration is the arithmetic non-existence of a partition; "admits no tiling" quantifies over dissections of a region that is not a `Tri`, and the corpus has no notion of a dissection of a general polygon. |

## Blockers named, main paper (2026-08-30, debt pass 2)

Every PROVED statement of `paper/erdos-634.tex` that had no blocker recorded now has one. The
recurring causes are named in `CLAUDE.md`; the rows say which applies and why.

| Paper | Statement | Lean declaration | Blocker |
|---|---|---|---|
| M `cor:mod12` | no prime ≡7 (mod 12) is a tile count | `BaseBetaMod12.*`, `Mod12.*` | PROVED — quantifies over *all* dissections of *all* triangles; it is `thm:main`'s corollary and inherits that theorem's cited inputs, none of which is formalized |
| M `prop:cornerpara` | the corner tile's `b`-edge is a chord matched by exactly one tile | `CornerRule.*`, `AngleArithmetic.beta_corner_forced` | PROVED — needs a **tile-placement layer**. **Partially discharged 2026-09-01**: 'the tile at a corner' — the proof's opening step, "`T_A` is the unique tile at `A`" — is now `Dissection.congruentDissection_base_corner_tile_unique` (`TileAt.lean`), a genuine carrier-membership uniqueness theorem for a real `CongruentDissection`, not just an angle census. What remains is the harder half: 'matched by exactly one tile', the `b`-edge chord `[P,Q]` and its partner tile `T_3` — still no `Dissection`-level definition of a chord or its far-side cover. **Scoped precisely 2026-09-08**: `WallChain.wall_two_sided`/`.edge_two_sided` (pre-existing, general — found while scoping this row) already give that any tile edge in the target's interior is covered, on each side, by a *chain* of other tiles' edges whose combined length equals the edge's own — real tile-placement-layer machinery, further-reaching than expected — but not that the chain has exactly one element. **Correction, same day**: the natural next step — combine unsplittability with `edge_two_sided` to conclude the far-side chain has exactly one element — is a **documented dead end already recorded in this codebase**. `BaseBetaWalks.lean:797–808` withdraws exactly this argument: *"It is tempting to conclude that an interior `b`-edge is matched by exactly one further `b`-edge... This does not follow, and the theorem is withdrawn. Unsplittability forbids an exact partition of an edge; it does not forbid a STRADDLE, in which a longer edge contains the `b`-edge in its interior and overhangs it... the 44-tiling has six unmatched `b`-edges but no boundary `b`-edge, and the 99-tiling has thirty-three unmatched against eleven on the boundary."* The unsplittability fact itself (`b` is never a nontrivial sum of `{a,b,c}`-lengths) also already exists, more generally than what was (briefly) built here — `BaseBetaWalks.edge_ab_unsplittable`, general in `(e,f)`, not just `e=1`. **What remains, precisely**: closing `prop:cornerpara` (if possible at all) needs something specific to the CORNER tile's `b`-edge — not a general interior `b`-edge — that rules out straddles there specifically; no such argument is known or has been attempted. This is a materially different, harder question than "unsplittable ⟹ matched," and may be genuinely blocked without further geometric input the paper's own proof supplies but this corpus doesn't yet formalize. |
| M `lem:cancel` | the tile values sum to the boundary flux `Φ_f(∂ABC)` | none | PROVED — needs the **flux functional Φ** on a dissection boundary, and the grid-direction cancellation argument; no Lean development exists |
| M `lem:value` | `C_{f_α}(t) = ±(c+a−b)` for every placement | none | PROVED — same flux development, plus a notion of oriented tile placement |
| M `cor:int` | `M_α`, `M_β` integral and `≡ N (mod 2)` | none | PROVED — depends on `lem:cancel` and `lem:value`; blocked by the same flux development |
| M `prop:F1free` | no `F₁` target is `N`-tiled for prime `N` | `InvariantProduct.*` | PROVED — quantifies over tilings of a shape family; needs the invariant-product development at `Dissection` level |
| M `thm:ladder` | `kT` is cut into `k²N` copies | `Erdos634.Ladder.ladder` | **VERIFIED 2026-09-02.** Both sentences of the paper proof are now theorems. `Subdivision.ladderDissection` is the grid: `cellSet` names the `k²` cells (tag + lattice index), `card_cellSet` counts them via `up_count`/`down_shift`/`total_count`, `cellIdx` indexes them by `Fin (k*k)`, and `cellOf_subset`/`cellOf_disjoint`/`volume_cellOf` supply containment, disjoint interiors and the areas, so `ConvexCover.ofCertificate` assembles a genuine `Dissection (k*k)` of `bigTri` (= `kT`, the homothety of `T` at `A` with ratio `k`); `ladderDissection_congruent` says every cell is congruent to `T`. `Compose.compose` is the refinement, and is the general statement — a dissection of each tile of a dissection composes with it into a `Dissection (M*N)` — which **closes the recurring `composition map on dissections` blocker**. `Ladder.ladder` joins them: the congruence of a cell to `T` gives an isometry, `isoAff` makes it affine by Mazur–Ulam, `mapDissection` transports the given dissection of `T` onto the cell, and `CongruentArea.image_carrier_of_congruent` identifies the transported target with the cell. Output is an honest `CongruentDissection (k*k*N)` of `kT` with the same model tile. Axiom-clean, no `sorry`. |
| M `cor:ladder` | the realizable set `S(e,f)` is closed upward under the ladder | (`Erdos634.Ladder.ladder`) | **STALE — superseded 2026-09-06, see the row citing `Realizable.mem_realizableSet_mul`/`realizableSet_eq_multiples` above (line ~290), the current accurate entry.** This duplicate row predates that update (two of the corollary's three clauses are now VERIFIED there; only clause 3, gated on `cor:elevenm`, remains) and was never removed — same bug class as `prop:reduction`'s duplicate row, found and fixed 2026-09-04. |
| M `cor:elevenm` | `1 ∉ S`, `2, 3 ∈ S` for `(e,f) = (1,2)`, plus primitivity and the `N=11m²` consequence | `Tiling44Bridge.dissection`, `Tiling99Bridge.dissection`, `ElevenMBridge.exists_dissection_11_mul_sq`, `Realizable.isMinimal_of_prime_of_one_not_mem` | PROVED — **corrected 2026-09-02: item (c) below was already done, this row was stale.** `2 ∈ S` and `3 ∈ S` are genuine `CongruentDissection`s (`Tiling44Bridge.dissection`, `Tiling99Bridge.dissection`), and the `N=11m²` consequence for `m` divisible by 2 or 3 is `ElevenMBridge.exists_dissection_11_mul_sq` (commit `587be94`, an earlier session — `lake build Erdos634.ElevenMBridge` confirmed clean 2026-09-02, this row's blocker text just hadn't been updated to reflect it). **Correction 2026-09-03**: the "still missing, two things" note below was itself stale — cross-checked against the more current `cor:ladder` row (line ~290): primitivity is *not* a second, independent gap. `Realizable.isMinimal_of_prime_of_one_not_mem` (already in the corpus, `Realizable.lean:147`) shows that for a **prime** scale `p`, `p ∈ S ∧ 1 ∉ S ⟹ p` is minimal — and `2`, `3` are both prime, so "neither the 44- nor 99-tiling arises from `thm:ladder` applied to a smaller member" is an immediate corollary of `1 ∉ S` itself, not an extra claim. **The one genuine remaining gap is `1 ∉ S`** — the 135-node engine exhaustion, permanently blocked on the missing certified-search format (see the dedicated scoping note, `lean/PAPER_MAP.md` line ~1073 area). Do not flip until that lands. |
| M `thm:primefull` | the prime case for `p ≢ 11 (mod 12)` | `BaseBetaMod12.*`, `IsoAlphaPrime.isoalpha_not_prime`, `InvariantProduct.tile_similar_not_prime` | PROVED — an iff over all dissections; the forward half rests on the branch theorems, the backward on explicit constructions, and neither is at `Dissection` level |
| M `thm:admissible` | every `N`-tiling of the base-α isosceles target has scale `k = dew` | `ThinFamily.*`, `SolvCore.*` | PROVED — quantifies over tilings; the arithmetic is available, the passage from a tiling to its scale is not |
| M `thm:lattice` | the spectrum lattice, with the parity switch `T` | `SurplusLattice.lattice_12`, `.lattice_13` | **STALE — superseded, see the row citing `SpectrumLattice.*` further down (line ~615), the current accurate entry.** The citation here was corrected once already (2026-08-31) and the blocker text is now out of date too (gap (i) closed 2026-09-02). |
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
| O `lem:ccornerside` | a `c`-corner carries a side `a`-edge, so `1 ≤ p ≤ (f−1)/e` | `TilePlacement.c_corner_side_a`, `.a_corner_side_c`, `.p_bounds`, `.p_le_of_bounds`, `SideNoB.side_quantized`, `SidePRange.side_p_range` | PROVED — the flank implication and the parameter bounds are both VERIFIED. The one step between them is not: that a side's chain edges are its walk counts, so that an `a`-edge on the side makes `P' > 0`. **Arithmetic core closed 2026-09-08**: `SidePRange.side_p_range` (new) derives the level equation and the full bound `1≤p≤(f-1)/e` directly from `P>0` plus the raw walk (composing the just-landed `lem:sidequant` with `p_le_of_bounds`) — everything the paper's proof does *after* asserting `P'>0`. **Still missing**: connecting a real corner tile's forced `a`-edge (`c_corner_side_a`, a single-triangle fact) to `P>0` for an *actual* `CongruentDissection`'s side walk. **Found 2026-09-08**: `SideWalk.side_walk_of_dissection` (pre-existing) already IS the abstract-to-real bridge — for any real dissection with a discharged geometric setup (`g,c,dir,hker,hwall,hbase,hline,hface,hthird,hiso,hscalene`), it gives the real walk with genuine counts. It has never been instantiated anywhere in the corpus (confirmed by grep — zero call sites; its own docstring names this the same open gap `thm:walkstruct`/`cor:wallsf2e` share). **Three of ~7 hypotheses discharged, 2026-09-08**: `Tiling44Scalene.tiling44_model_scalene` gives `hscalene` (side lengths `16,24,32`, pairwise distinct). `Tiling44WallSetup.lean` picks the concrete wall line — the equal side from `(176,0)` to the apex `(88,24√15)` (target vertices confirmed exact by `decide`), `gWall(x,y)=24√15x+88y` its defining functional, `dirWall` the normalized direction along it — and discharges `hker` (the two functionals' gradients form a basis, determinant `16384≠0`) and `hwall` (the whole target satisfies `gWall≤4224√15`, via `Tri.carrier_subset_halfplane_affine`, the same pattern this session's collar work used throughout). **Six of ~7 hypotheses now discharged, 2026-09-08, later**: `hbase` (the wall segment is exactly the equal side's own edge, hence on the frontier, via the pre-existing general `SideWall.edge_subset_frontier`), `hline` (`gWall` equals `4224√15` on the whole segment, direct from agreement at both endpoints plus affineness), and `hface` (any target point attaining `gWall`'s max lies on the segment — via the pre-existing general `SupportFace.mem_convexHull_max`, a convex-hull point attaining a linear functional's bound is a combination of only the vertices that also attain it, and here only `pts 1`/`pts 2` do). **`hiso` also closed, 2026-09-08, later still**: `hiso_wall` — any two points on `gWall=4224√15` have their difference forced into `gWall`'s kernel (the wall's own direction, length exactly `128`), and `dirWall`'s `/128` normalization makes `dist p q = |dirWall p − dirWall q|` exactly (confirmed by direct coordinate computation, both quantities equal `16/11` times the raw `x`-coordinate difference). **Only `hthird` remains**, and its first piece is built, 2026-09-08, later still: `gWallZ`/`gWallZ_correct` transfer `gWall`'s value to exact `ℤ[√15]` arithmetic (matching how every other check in this project — `Tiling44.dist2`, `.area2` — works; sanity-checked against the known apex vertex), the bridge needed to apply `Z15Real.toR_ne_zero_of_sq_ne` (pre-existing) per concrete tile. **`hthird`'s arithmetic core closed, 2026-09-08, later still**: `all_hthird_ok` — decide-checked across ALL 44 of `Tiling44`'s tiles (the same whole-family `decide` pattern this project's (C1)–(C4) checks already use): every wall-edge tile's third vertex genuinely satisfies `toR_ne_zero_of_sq_ne`'s hypothesis. Confirms the geometric fact is true, not just plausible. **Backward-direction dichotomy closed, 2026-09-09**: `vertexDichotomyOK`/`all_vertex_dichotomy_ok` (decide-checked over all 44 tiles) — every vertex's `ℤ[√15]` value either IS the wall value `(0,4224)` exactly or is provably off it (the `z.1²≠15z.2²` test). Combined with `gWallZ_correct` this gives `g_eq_iff_wallVal`: the real biconditional `gWall(vertex)=4224√15 ↔ wallVal(vertex)=(0,4224)`, for every vertex of every tile — the missing piece to translate between the real-valued `WallEdge`/`hthird` hypotheses `side_walk_of_dissection` needs and the Bool-valued `isWallEdge`/`all_hthird_ok` facts already proven. **`hthird_wall` closed, 2026-09-09, later**: `Tiling44WallFinal.hthird_wall` translates `all_hthird_ok` (the Bool, `Tiling44.tiles`-indexed fact) into `side_walk_of_dissection`'s exact real-valued, `BaseChain.wallList`-indexed `hthird` shape, via `g_eq_iff_wallVal` and the definitional equality `dissection.tile p.1 = pieceTri ht`. All seven of `side_walk_of_dissection`'s hypotheses (`hker`,`hwall`,`hbase`,`hline`,`hface`,`hthird`,`hiso`) plus `hscalene` are now discharged. **`side_walk_of_dissection` actually called, 2026-09-09, later still**: `Tiling44EqualSideWalk.equal_side_walk` — the first real instantiation anywhere in the corpus, giving `∃ Pc Qc Rc, dist(pts1,pts2) = Pc·s₀+Qc·s₁+Rc·s₂` for `Tiling44Bridge.dissection`'s actual equal side (target's edge from `(176,0)` to the apex). **Still missing, and the only thing left**: `Pc>0` (or whichever count matches the corner tile's forced `a`-edge) is not part of `equal_side_walk`'s conclusion — `∃` gives existence of *some* nonneg counts, not that the specific corner-forced one is positive. Closing this needs `TilePlacement.c_corner_side_a` (a real corner tile has a side `a`-edge) connected to `WallEndpoints.chain_starts_at_a` (the chain's first edge starts at the corner) to force the matching count `>0`, then `SidePRange.side_p_range` applies. **Corner tile identified, 2026-09-09, later still**: `Tiling44CornerTile.lean` — `Tiling44.tiles[13]` is the actual tile sitting at `targetTri.pts 1 = (176,0)` (the wall's own start point), decide-checked. Its two vertex-1-incident edges have squared lengths `256=16²` and `1024=32²`, never `576=24²` — the `b`-side is not incident to this corner at all, matching the paper's own `c`-corner structure. **`side_walk_pos1_of_dissection` built, 2026-09-09, later still**: `SideWalk.side_walk_pos0_of_dissection`/`.side_walk_pos1_of_dissection` (new, general — not specific to any one target) generalize `side_walk_of_dissection`: given a witness wall edge whose length matches a named model side, the corresponding walk count is `≥1`, not just that some count exists (via `chain_endpoints`'s `hsurj` locating the witness among the enumerated wall edges, then `ChainWalk.count_pos`). Applied to `Tiling44Bridge.dissection`'s equal side with `tiles[13]`'s edge as witness: `Tiling44EqualSideWalkPos.equal_side_walk_pos` gives `Qc≥1`. **IMPORTANT CORRECTION, 2026-09-09, same iteration**: checked against the paper text directly (`erdos-634-obstructions.tex:957-966`) — `lem:ccornerside` is a statement about the **general base-β family** (`(e,f)` a base-β pair, "the base corner angle is `β`"), not about any single fixed target. `Tiling44Bridge`'s target is the **isosceles `16-16-22` triangle** (`thm:44`'s own family, a different geometric object entirely — no base-β angle `β`, no `(e,f)` parametrization). So `equal_side_walk_pos` is a genuine worked example of the abstract machinery, not itself part of `lem:ccornerside`'s proof — closing the general lemma needs a real-coordinate realization of an actual base-β `(e,f)` target, which **does not exist yet in this project** (confirmed by search; `SideWalk.lean`'s own docstring for `int_walk_of_dissection` already flagged this same gap). The general, reusable tools (`side_walk_pos0/1_of_dissection`, `SidePRange.side_p_range`) ARE real progress; the specific application to Tiling44 is not. Landed in `Tiling44WallSetup.lean` / `Tiling44WallFinal.lean` / `Tiling44EqualSideWalk.lean` / `Tiling44CornerTile.lean` / `SideWalk.lean` / `Tiling44EqualSideWalkPos.lean`. **Placement-layer progress, 2026-09-09, later still**: `TileAt.congruentDissection_base_corner_tile_vertex` identifies the base corner point as an actual vertex `(D.tile i).pts j` of the (now-known-unique) corner tile, not merely contained in its carrier. `Congruence.Tri.Congruent.sideMultiset_eq` + `CongruentTileEdges.Tri.sideMultiset_shift` bridge "the corner tile is congruent to the model" to the model's own named side lengths at ANY vertex index, and `CongruentTileEdges.congruentDissection_lays_a` assembles all of it with `c_corner_side_a` into a real-dissection-level "lays `c` ⟹ lays `a`" fact. **Still not flippable**: this closes the *flank-implication* half of `lem:ccornerside` for any real `CongruentDissection`, but the lemma needs a real base-β `(e,f)` target to apply it to — the same missing real-coordinate witness named throughout this row and `lem:wpgram`'s row. Real, general, reusable placement-layer infrastructure; not yet a witness. **MAJOR CORRECTION, 2026-09-09, later still**: that "missing real-coordinate witness" framing was itself wrong for `side_walk_of_dissection`'s own hypotheses — checked `SideWall.wallFun` directly: it already builds `hker`/`hwall`'s functional `g` for *any* `Tri` and side, via barycentric-coordinate functionals, no explicit numeric coordinates at all. `WallDir.lean` (new) supplies the missing `dir`/`hiso` half the same way, fully generally: `eq_lineMap_of_wallFun_eq_zero` (any point on a triangle's wall line is `lineMap` between the side's two vertices, at its own barycentric coordinate) and `dirFun`/`hiso_wallFun` (that coordinate, scaled by the side's own length via Mathlib's `dist_lineMap_lineMap`, calibrates to real distance) — for *any* `Tri`, no coordinates, no fixed target. This directly unblocks `side_walk_of_dissection`'s `hiso` hypothesis for any real `CongruentDissection`, not only a specific certified member. **`hker` also closed generally, 2026-09-09, later still**: `WallDir.hker_wallFun` — `wallFun`'s and `dirFun`'s linear parts have trivial joint kernel, for any `Tri` and side, proved directly from the barycentric basis (a killed vector forces `v +ᵥ T.pts k` to share every barycentric coordinate with `T.pts k`, hence to equal it via `AffineBasis.ext_elem`). **`hface` closed too, 2026-09-09, later still**: `WallDir.mem_convexHull_max_affine` generalizes `SupportFace.mem_convexHull_max` from linear to affine functionals (via `f(y)=f(0)+f.linear(y)`), and `hface_wallFun` applies it to `wallFun T k` over `T`'s three vertices. `hbase`/`hline` need no new Lean at all — direct instantiations of the pre-existing general `SideWall.edge_subset_frontier`/`wallFun_eq_zero`. **`hthird` closed too, 2026-09-09, later still, CORRECTING the earlier "genuinely dissection-specific" verdict**: `WallThird.hthird_general` — if a wall edge's third vertex also had `g=c`, all three of the tile's vertices would share one *nonconstant* affine functional's value, forcing them collinear and contradicting the tile's own nondegeneracy (`Tri.indep`); combined with `hwall` this forces the strict inequality, for *any* dissection, *any* wall functional, *any* tile — no `decide`, no fixed target. `wallFun_linear_ne_zero` discharges the one side condition (`wallFun`'s linear part is nonzero) generally too. **All ~7 of `side_walk_of_dissection`'s hypotheses (`hker`, `hwall`, `hbase`, `hline`, `hface`, `hiso`, `hthird`) are now available for *any* real `CongruentDissection`, using `wallFun`/`dirFun` as `g`/`dir` — no coordinates, no fixed target, no per-target `decide` check.** Only `hscalene` (the model's 3 sides pairwise distinct — trivial once a target/model is fixed) remains for a caller to supply. **Checked whether this flips anything outright**: `cor:wallsf2e` (closest candidate) still inherits `cor:basedi2e`'s separate blocker (the base's own decomposition into exactly `{(0,e,2e),(f,e,e)}}` is combinatorial content about a real tiling, not part of what `side_walk_of_dissection`'s setup supplies) — not flippable from this alone. This is major, genuinely general infrastructure; the next step to convert it into a flip is finding a row whose *entire* remaining content is the geometric-setup connection this machinery now supplies outright. |
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
| C `thm:pierce` | apex mismatch: the pierced corner | `BaseBetaWalks.apex_leftover_nonrepresentable`, `.pierced_corner_types` | PROVED — **citation corrected 2026-09-04**: previously cited `ApexRigidity.*`, a file that does not contain either of the paper's own cited declarations. The paper's own proof (`erdos-634-companion.tex:214-231`) cites `apex_leftover_nonrepresentable` (clause (ii)'s no-solution arithmetic) and `pierced_corner_types` (clause (iii)'s `{α,γ}`/`{3α,β}` case split), both pre-existing in `BaseBetaWalks.lean` and matching exactly. Still needs tiles laid at the apex and their edges connected to a real dissection; **tile-placement layer** blocker genuinely stands |
| C `prop:rung2` | the pre-piercer chain | `BaseBetaWalks.far_near_disjoint`, `.far_is_bpow`, `.b_not_dvd_fsq` | PROVED — **citation corrected 2026-09-04**, same bug and fix as `thm:pierce` above: previously cited `ApexRigidity.*`/`CChord.*`; the paper's own proof (`erdos-634-companion.tex:262-271`) cites these three declarations, all pre-existing in `BaseBetaWalks.lean` and matching. Same placement layer blocker, on the configuration of `thm:pierce` |
| C `thm:ray` | the mismatch ray is completely determined | `ApexRay.*`, `PinRay.*` | PROVED — the ray arithmetic is available; 'along the ray' quantifies over the tiles it meets — placement layer |
| C `thm:chain` | the `b`-run orientation lemma | `BEdgeReading.side_alpha_gamma`, `BEdgeReading.side_junction_figure` | **VERIFIED 2026-09-02**. Paper statement has two clauses: (1) "every `b`-edge of the run carries `α` at its apex end and `γ` at its far end" and (2) "every junction interior to the run is an `(α,β,γ)` π-vertex" (the "in particular the `3α+2β` figure never occurs" is a trivial corollary of (2)'s exact card counts, not independent content). Both are now composed Lean theorems, checked word-for-word against the paper statement, not just their ingredients (Rule 5): `side_alpha_gamma` gives clause (1) directly — combines `side_word_constant` (word-level `BG` constancy) with `OrientWord.word_apply` and `tile_orient_BG_east_gamma`. `side_junction_figure` gives clause (2) — combines `side_alpha_gamma`'s per-edge `γ` reading at each interior junction with `VertexFigureReal.gamma_boundary_figure_real` (a pre-existing theorem built for `lem:onegamma`/the march step, discovered to already prove exactly this shape: a `γ` at a real boundary non-vertex point forces the figure `{α,β,γ}`, one tile each, no straight angle) via `TileAt.congruentDissection_hcorners`/`VertexFigureReal.localAngle_mem` for the generic `hvals` bridge. Both theorems are unconditional except the standard wall/line/seed hypotheses (the paper's own conditional premises — "seeded at an apex tile" is `hseed`), not an existence claim; no witness needed. `lake build Erdos634.All` clean, no `sorry`. Paper `\lab{}` tag flipped PROVED→VERIFIED. **Correction history**: the "needs a concrete numeric witness like `thm:walkstruct`" note (multiple prior sessions) was stale from before `thm:walkstruct`'s own correction; the actual remaining gap was pure composition of already-built pieces, not a missing witness. |
| C `thm:farregion` | the far region is a scaled tile | `ApexRigidity.*`, `ConeScaling.*` | PROVED — needs the region cut off by a wall as an object. **Note 2026-09-02**: `SubDissection.restrict` (new) now supplies the sub-region *object* (a real `Dissection`/`CongruentDissection` of any tile subset whose union equals a given triangle) — the bookkeeping obstacle this row's note names is gone. What remains, row-specific: proving that the far region cut off by a wall actually *is* such a union of tiles (the covering-equality hypothesis `restrict` still needs) — real geometric content, not yet built. |
| C `cor:farvacuous` | the far side gives no contradiction | `ApexRigidity.*` | PROVED — conditional on `thm:farregion`; same blocker, now the same partial closure (`SubDissection.restrict` supplies the object; the covering-equality for this specific region is not yet built) |
| C `thm:e1reduce` | the `e=1` base walk is a permutation of `(a^f, b, c)` | `BaseCountsE1.base_counts`, `.base_counts_corner` | PROVED — the counts `n_b = 1` and the exclusion of `n_c = 2` are VERIFIED; `n_c ≥ 1` is `prop:gammatrap`, VERIFIED (`GammaTrap.congruentDissection_gammatrap`), and `SideWalk.lean`'s `_of_gammatrap` family (`equal_side_no_b_of_gammatrap`, `base_b_count_of_gammatrap`, `equal_side_shape_of_gammatrap`) already wires it through a real side's walk equation. **Corrected 2026-09-02**: the prior "not an open geometric input" phrasing was imprecise — checked `thm:walkstruct`'s row (line ~507) for the precise name: what remains is a *concrete* `CongruentDissection` witness realizing the base-β model/target with matching side lengths, which is structural blocker 1 (the tile-placement layer) — genuinely open, not mere bookkeeping |
| C `lem:filler` | the filler identity and the strip tiling | `W2Core.*` | PROVED — the two identities are VERIFIED and axiom-free; 'the column and its fillers tile the strip' needs the placement layer |
| C `lem:offsets` | the offset congruence `Σεᵢ − j = −2q` | none | PROVED — the congruence is elementary and formalizable; what it is *about* — the terminal column's base apex — has no Lean definition |
| C `lem:anglecalc` | the five vertex-figure facts: no right angle, apex, base corner, γ-trap, `α+β` wedge | `AngleArithmetic.no_right_angle`, `TileAt.congruentDissection_apex_counts`, `.congruentDissection_base_corner_counts`, `.congruentDissection_boundary_figure_cases`, `.congruentDissection_boundary_figure_cases_at_vertex`, `AngleArithmetic.alpha_beta_corner` | PROVED — **downgraded from VERIFIED 2026-09-02: the previous citation overclaimed.** It cited `TilePlacement.base_corner_counts`/`.apex_counts`, `VertexFigureReal.apex_figure_real`/`.base_corner_figure`, but every one of those takes `hvals`/`hsum` — "every tile's local angle here is one of `α,β,γ,π,0`" — as a *hypothesis*; grepped the corpus, nothing had ever discharged it for a real dissection (the same bug class as the ten wrong VERIFIED labels of the 2026-08-30 audit, and `prop:cornerfig`'s citation gap closed earlier tonight). Fixed by citing real derivations instead. Clause (1) is pure arithmetic, unaffected. Clauses (2) apex and (3) base corner now hold of a genuine `CongruentDissection` at the target's own vertices, via `TileAt.congruentDissection_apex_counts`/`.congruentDissection_base_corner_counts` (pre-existing, from tonight's `lem:census` work). Clause (4) γ-trap — a *general* straight-angle boundary point, not a target vertex — is closed by `TileAt.congruentDissection_boundary_figure_cases`, composing `congruentDissection_hcorners` (a sibling addition landed the same night, independently deriving the same corner-angle fact used inline by `.congruentDissection_no_double_gamma`) with `VertexFigureReal.localAngle_mem`/`.boundary_multiplicities_cards`/`.boundary_figure_cases` (pre-existing, previously never fed a real `hcorners`/`hvals` anywhere else in the corpus). It proves the real trichotomy — one tile presenting a straight angle alone, or exactly `{3α,2β}`, or exactly `{α,β,γ}` — at *any* frontier point of a real `CongruentDissection` that is not a target vertex; this is also exactly the `hvals` hypothesis `MarchRun.junction_dichotomy` and `VertexFigureReal.gamma_boundary_figure_real` (`rem:marchobl`'s M-i/M-vertex rows) still carry, now suppliable for a real dissection though not yet threaded into those call sites. **Residual gap 1 closed 2026-09-02**: `TileAt.congruentDissection_boundary_figure_cases_at_vertex` (new) excludes the trichotomy's degenerate single-tile branch given a witness that some tile actually presents a corner angle (`α`, `β`, or `γ`) at the point — a trivial cardinality argument once such a witness exists (any nonzero card among `α,β,γ` rules out the all-zero branch). Matches clause (4)'s literal "the only figures are `{3α,2β}` and `{α,β,γ}`" two-way dichotomy. `lake build Erdos634.All` clean, no `sorry`. **Residual gap 2, investigated 2026-09-03, still open**: clause (5)'s pure-arithmetic content (`nα+2nγ=1, nβ+nγ=1 ⟹ nα=nβ=1, nγ=0`) already exists as `AngleArithmetic.alpha_beta_corner` (pre-existing, uncited before this pass — added to the citation list above), matching clause (1)'s "no right angle" in being pure arithmetic requiring no real point. But the *real* content — that some actual point of a `CongruentDissection` has local angles summing to exactly `α+β` — is not the same shape as clauses (2)–(4)'s target-vertex/boundary-point derivations: `Interface.lean`'s only use of `alpha_beta_corner` is inside the `T_mid` kill's combinatorial argument (a specific placement-layer configuration, not a generic real point), and the paper's own comment ("the strip's corner") ties clause (5) to the deferred strip-and-column exposition named in `thm:e1family`'s own `\lab{CONJECTURE: ... deferred}` tag — confirmed by grep, `strip` never appears as a built Lean object anywhere in the corpus. Genuinely blocked on deferred content, not mere bookkeeping; no further attempt is worthwhile until the strip-and-column exposition itself is built. Label stays PROVED. |
| C `rem:norightangle` | no piece of any dissection has a right angle | `AngleArithmetic.no_right_angle`, `CongruentAngles.congruent_corner_angles` | **STALE — superseded 2026-09-06, see the row citing `NoRightAngle.*` further down (line ~611), the current accurate `VERIFIED` entry.** This duplicate row predates the composition that closed the blocker (`NoRightAngle.no_right_angle_of_congruent` etc.) and was never removed — same bug class as `prop:reduction`'s/`cor:ladder`'s duplicate rows. |
| C `prop:gammagrading` | every edge direction is an integer multiple of `γ` mod `π` | `DirectionGroup.*`, `Dissection.Dir` | PROVED — needs edge directions of a dissection as a group; `Dissection.dirSet` exists but the grading is not developed |
| C `prop:dirgroup` | the direction group of a branch | `DirectionGroup.*` | PROVED — same development |
| C `lem:termwedge` | the terminal wedge decomposes as `γ + α + β` | `AngleArithmetic.*`, `VertexFigureReal.boundary_figure_cases` | PROVED — the figure is now reachable at a real boundary point; the column terminating at a base vertex is a placement statement |
| C `lem:sidenob` | the equal sides carry no `b`-edge | `SideNoB.side_no_b_uncond`, `.side_no_b_e_one` | VERIFIED — the walk arithmetic is VERIFIED; 'every side walk' presupposes the side's edge chain — bridge (c) on the equal sides |
| C `prop:doublec` | the double-`c` kill at any initial block | `DoubleC.*` | PROVED — placement layer: initial blocks of a side walk |
| C `lem:eastfan` | the east fan at the fork is forced | `straight_junction_gamma_bound`, `straight_junction_cases` | PROVED — the junction arithmetic is VERIFIED; bricks and mates have no Lean structure |
| C `thm:forkkill` | the row fork kill | `ForcedRow.*`, `ForkKill` lemmas | PROVED — same brick/mate structure |
| C `prop:a2branch` | the `A₂` branch dies | `OrderForcing.straight_junction_cases`, `.east_cover_gap`, `.straight_junction_gamma_bound`, `.alpha_vertex_gap`, `.anti_brick_side` | PROVED — **citation corrected 2026-09-06**: previously cited `A2BranchRow3.*`/`east_cover_gap`, but `A2BranchRow3.lean`'s own docstring explicitly says the five lemmas the paper's proof cites are "already formalized... in `OrderForcing`" — checked, all five exist there, not in `A2BranchRow3.lean`. `A2BranchRow3.lean` is a *different* thing: an attempted extension of the row-1 case (which the five `OrderForcing` lemmas fully cover) to row 3, honestly recorded by its own docstring as incomplete — "the descent... reach[ing] the base" is a global structural fact not yet closed, distinct from the local angular content the citation covers. Placement layer still blocks a real-dissection instantiation either way |
| C `lem:wallclimb` | the wall climb: `Cⱼ` direct and `Mⱼ` forced | `WallChain.*`, `WallClimb` lemmas | PROVED — same structure |
| C `thm:l2slot` | L2 at every reached slot | `PentagonLemma.partner_unique` | PROVED — **citation corrected 2026-09-04**: previously cited `W2Core.*`/`LayerLink.*`, neither of which contains the paper's own cited declaration. The paper's own proof (`erdos-634-companion.tex:1974-1987`) cites `partner_unique`, pre-existing in `PentagonLemma.lean` (general in coprime `e,f`), matching. The slot chain itself is still a placement structure with no Lean definition — blocker stands |
| C `thm:elltwo` | the block-two chain runs to arbitrary depth | `OrderForcing.partition_2b`, `.east_cover_gap` | PROVED — **citation corrected 2026-09-04**, same bug as `thm:l2slot` above: previously cited `W2Core.*`. The paper's own proof (`erdos-634-companion.tex:1990-2005`) cites `partition_2b` and `east_cover_gap`, both pre-existing in `OrderForcing.lean`, matching. Same placement-layer blocker |
| C `thm:depthwindow` | reach three behind a thick block | `PincerLadder.pincer_ladder`, `OrderForcing.pincer_window` | PROVED — the window arithmetic is VERIFIED and is what the sweeps consume; the geometric reach step is the open half |
| C `lem:ladder` | descent identities and the ladder | `descent_ident`, `sinb_ident`, `ladder_no_base` | PROVED — the identities are VERIFIED; **checked 2026-09-02**: `Realizable.scaleTri`/`Ladder.ladder` now exist as *general* scale/ladder constructions on `CongruentDissection`s, but this row's "ladder" is a specific base-β descent-chain object (companion.tex), not literally `thm:ladder`'s construction — connecting the two, if even possible, is unstarted work, not a citation fix. |
| C `lem:termination` | a ladder terminates only where both covers end | `consecutive_gap` | PROVED — same ladder development |
| C `lem:columnlines` | corner lines are column lines | `CosetPropagation.*`, `FloorPropagation.*` | PROVED — the lattice arithmetic is available; 'lines through two vertices of the corner lattice' needs the lattice as a Lean object |
| C `lem:noapexline` | the chain never needs the apex line | `chain_needs_small_lines` | PROVED — same lattice development |
| C `lem:monochotomy` | the thick-member monochotomy for `c` | `c_chord_unique_thick`, `CChord.*` | VERIFIED — the decomposition arithmetic is VERIFIED; the lemma also asserts which decomposition a *tiling* realises |

## Blockers named, companion part 2 (2026-08-30, debt pass 5)

| Paper | Statement | Lean declaration | Blocker |
|---|---|---|---|
| C `thm:walkstruct` | the walk structure at `m=1` | `equal_side_no_b`, `equal_side_shape`, `base_b_count` | PROVED — the walk arithmetic is VERIFIED. **Note 2026-09-02 (fifth pass)**: all three `ℤ`-typed arithmetic theorems now have a `_of_gammatrap` counterpart in `SideWalk.lean` connecting them to a real dissection — `equal_side_no_b_of_gammatrap` (clause (i), `Qc=0`), `base_b_count_of_gammatrap` (the base's `n_b=e`, feeding `cor:wallsf2e`), `equal_side_shape_of_gammatrap` (`n_c=f-k·e` given `n_a=f·k`, derived via `f₀∣Pc` from the walk equation itself and coprimality). In every case, `GammaTrap.congruentDissection_gammatrap` (VERIFIED) supplies the `c`-edge witness unconditionally — no more `hnc1` hypothesis anywhere in this chain. **The one genuinely remaining gap, shared by all three**: `hA`,`hB`,`hC`,`hLen` — a concrete numeric realization (an actual `CongruentDissection` whose model has sides `ef,f²-e²,f²` and whose target's side `k` has the right length). `IsoTri.isoTri`/`SssTri.sssTri` (new, general-purpose `Tri`-from-side-lengths constructors, first in this project) build the individual triangles; a full `CongruentDissection` needs `N` tiles actually covering the target — a trivial `N=1` witness is impossible (the model is scalene, the target isosceles) — this is unavoidably the placement layer, structural blocker 1. This is the closest any row got to a real closure this session, and the pattern (wire the already-VERIFIED `gammatrap` through `chain_endpoints`'s surjectivity into any walk-equation arithmetic theorem) is now proven out and mechanically repeatable. **Correction (2026-09-02, later)**: "structural blocker 1" as a description of what `hA,hB,hC,hLen` need was itself imprecise. Checked the paper text (companion.tex:466): `thm:walkstruct` is explicitly conditional — "Let `m=1`... consider a tiling of the base-β target" — about a *hypothetical* tiling of `Δ₁`, which never exists (`m=1` is excluded, `1 ∉ S`). `hLen`'s `f0³` is `Δ₁`'s own leg length (confirmed: `L=f³` in the paper's own proof text, and `Δ₁`'s leg is `X₁=8=2³` for member `(1,2)`). So **no `CongruentDissection` can or should instantiate `hLen`** — `D` is a hypothesis these Lean theorems take, not something requiring an existence witness, exactly matching the paper's own conditional. A concrete candidate witness (`Tiling44Bridge.dissection`, of `Δ₂`, not `Δ₁`) was explored two turns ago and correctly abandoned once this was noticed — see `private/VERIFY_PLAN.md`'s dated entry. **What actually remains, precisely**: whether `equal_side_no_b_of_gammatrap`/`equal_side_shape_of_gammatrap` together match clause (i) *as a conditional* — they give `n_b=0` and the `n_a=fk,n_c=f-ke` shape, but not yet "ends with a `c`-edge at the apex" (clause (i)'s last clause). **Update 2026-09-02, later**: clause (ii) fully closed as a conditional. `BaseBetaWalkArith.base_shape`/`.base_shape_ell_le_one` (the `ℤ`-typed arithmetic, mirroring `equal_side_shape`) plus `SideWalk.base_shape_of_gammatrap` (the dissection-level wrapper, composing `base_b_count_of_gammatrap`'s strengthened conclusion — now also exposes `Rc` and the full walk equation — with `base_shape` via the same `f0∣Pc`-by-coprimality argument `equal_side_shape_of_gammatrap` used) together give `n_a=fℓ⟹n_c=e(2-ℓ)` for a real dissection's wall, given only the numeric instantiation. Clause (i) still needs its own residual (the apex-edge piece). **Resolved 2026-09-02, later**: checked the paper's exact `\lab{}` tag — `\lab{PROVED: the walk arithmetic VERIFIED}`, a compound label distinguishing the full geometric theorem (`PROVED`) from a named sub-part ("the walk arithmetic", already `VERIFIED` in the paper's own accounting, matching the pre-existing `BaseBetaWalkArith` arithmetic theorems its own proof text cites as machine-checked). Since this project's convention tracks the paper's primary label, the row correctly stays `PROVED` overall. **Update, later still**: clause (i)'s apex-edge residual is now also closed — `equal_side_no_b_of_gammatrap` (strengthened) now proves the wall's apex-end edge is a `c`-edge, via `TileAt.congruentDissection_apex_counts` + `EdgeType.edge_excludes_own_angle`'s contrapositive + elimination against the already-known `n_b=0`. **Both clauses (i) and (ii) of `thm:walkstruct` are now fully proven as conditionals.** Label stays `PROVED` regardless (per the resolved compound-`\lab` question above) — the paper's own primary tag is what this project tracks, and nothing above changes it. |
| C `lem:pentagon` | the middle region of `(0,e,2e)` admits no tiling | `Pentagon.no_partition` | PROVED — 'admits no tiling' quantifies over dissections of a **non-triangular region**, for which there is no Lean notion |
| C `lem:anglethreshold` | the closed forms for `cos α`, `cos β`, `cos γ`, and (P4) | `AngleThreshold.cos_of_sides`, `.cos_alpha_closed`, `.cos_beta_closed`, `.cos_gamma_closed` | **STALE, corrected 2026-09-02 — see the row below (line ~562): all three cosines are VERIFIED via `AngleThreshold.lean`, not just one.** (P4) is `rem:anglethreshold`, still blocked. |
| C `lem:basetri` | the thick base trichotomy | `base_trichotomy` | VERIFIED — the three decompositions are VERIFIED arithmetic; that a tiling realises one of them needs the base edge chain |
| C `lem:shadow` | the shadow at a `c`-corner | `OrderForcing.strips_tall`, `.shadow_footage_e1` | PROVED — **citation corrected 2026-09-04**: previously cited `SideNoB.c_corner_forces_side_a`, an unrelated theorem (`0 < f·p → 1 ≤ p`) with a note about a stale "circularity fix" that does not match this lemma's actual content at all — an editing error, not a real audit finding. The paper's own text (`erdos-634-companion.tex:2743-2753`) cites `strips_tall` (the tile-height identity `f³=f·f²`) and `shadow_footage_e1` (the `e=1` window comparison `3f²>1`, both pre-existing, checked, matching exactly). **Tile-placement layer blocker genuinely stands**: the lemma's real content — that a base corner tile laying `c` forces a rigid strip structure and every base edge meeting the shadow is a `c`-edge — is geometric placement reasoning neither arithmetic fact touches
| C `lem:basedi` | the thick base dichotomy | `BaseDecomposition.base_decomposition_general`, `CChord.base_dichotomy_thick`, `GammaTrap.congruentDissection_gammatrap` | **VERIFIED 2026-09-09.** Corrected the 2026-09-02 "needs a concrete `CongruentDissection` witness" verdict — `lem:basedi`'s own statement ("at a separated thick member only two base decompositions survive") is itself conditional on a real tiling, matching the paper's own necessary-condition framing throughout this section, not an existence claim; no coordinate witness was ever needed, only the *conditional* theorem. `base_decomposition_general` builds exactly that: given any real `CongruentDissection` whose model has the base-β `(e,f)` side lengths `ef,f²-e²,f²` (standard `a`/`b`/`c` opposite-side convention, `sideOpp D.model 0/1/2`) and whose target's side `k` is the base (angle `β` at one end, `3α` at the apex end, length `e(3f²-e²)`) at a separated member (`f²>2ef+e²`), the base decomposes as exactly `(0,e,2e)` or `(f,e,e)` — composing `GammaTrap.congruentDissection_gammatrap`'s `c`-edge witness (already VERIFIED, general) with `SideWalk.side_walk_pos2_of_dissection` (new, general witness-positivity) via `wallFun`/`dirFun` (all of `side_walk_of_dissection`'s hypotheses now general, see `lem:ccornerside`'s row) to get the real walk equation with `Rc≥1`, casting to `ℤ` arithmetic (`base_walk_pos_int`), then applying the already-VERIFIED `base_dichotomy_thick`. **Checked against `cor:basedi2e`'s own row too**: that corollary's stated hypothesis is the *weaker* `f>2e` (not the separated `f²>2ef+e²`), proved by a genuinely different, harder argument (checked directly: `erdos-634-companion.tex:2757-2843`) — this closes `lem:basedi` only, not `cor:basedi2e`. |
| C `cor:basedi2e` | the trichotomy and dichotomy without separation | `CChord.base_trichotomy_2e`, `.base_dichotomy_2e`, `BaseDecomposition.base_decomposition_2e` | **VERIFIED 2026-09-03.** The harder argument the row previously said didn't exist yet, now built: `CChord.base_trichotomy_2e` (ℤ-typed, ported directly from `erdos-634-companion.tex:2837-2867`) replaces `base_trichotomy`'s separation step with the weaker `f>2e`. `mod f` still gives `f∣(y−e)` unconditionally (reused). Writing `y=e+k·f`, `k≥1` needs excluding: a second `mod f` reduction on the resulting `xe+zf=2ef−k(f²−e²)` gives `f∣(x−ke)`, write `x=ke+cf`; the bounds from `x,z≥0` give `−2c<k` and `2k<2−c`, jointly unsatisfiable with `k≥1` — `omega` closes it once both are in hand. `base_dichotomy_2e` (ℕ cast) then composes with the γ-trap's `z≥1` exactly as `base_dichotomy_thick` does. `BaseDecomposition.base_decomposition_2e` (new) is the dissection-level conditional, mirroring `base_decomposition_general`'s composition with `wallFun`/`dirFun`/`side_walk_pos2_of_dissection` but for this weaker hypothesis. This is real new arithmetic, not a port of existing machinery — the `−2c<k`/`2k<2−c` bounding chain has no prior counterpart in the corpus. |
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
| C `prop:inflbdy` | the inflated boundary | `Inflation.*` | PROVED — **checked 2026-09-02**: same as `cor:inflcrux`/`prop:inflparity` — the scale map (`Realizable.scaleTri`) exists as an operation, but `Inflation.lean` has no geometric `Dissection` object of the inflated tile to apply it to yet; that construction is unstarted, not a citation fix. |
| C `cor:inflcrux` | the crux, on `f²` tiles | `Inflation.*` | PROVED — **checked 2026-09-02**: `Realizable.scaleTri` exists as an operation, but `Inflation.lean` itself is pure combinatorics on boundary-word sums (`isSide`, `residual_*`, etc.) with no geometric `Tri`/`Dissection` content at all — building "the inflated tile's dissection" as a real object using `scaleTri` is unstarted geometric-placement work, not a citation fix. |
| C `prop:inflparity` | edge parity kills the `p=1` boundary | `Inflation.*` | PROVED — same as `cor:inflcrux` (checked 2026-09-02: `Inflation.lean` is pure combinatorics, no dissection object yet), plus an edge-to-edge hypothesis with no Lean definition |
| C `prop:orientmono` | the orientation of a boundary `a`-run is monotone, **on the inflated tile's side** (companion `prop:orientmono`, distinct from the already-VERIFIED `prop:orientmonobdy` on the *target's own* side — the latter's proof explicitly needs no boundary-to-word passage) | `Inflation.BG_GB_forbidden`, `.orient_monotone`, `.AAB_iff_transition` | PROVED — the alphabet lemmas are VERIFIED. **Note updated 2026-09-02 (fourth pass)**: `AEdgeReading.side_word_monotone` (new) now closes the boundary-to-word-to-monotone passage **unconditionally**, for a whole `a`-side of *any* `CongruentDissection`, using only the standard wall/line setup (`hker`,`hwall`,`hbase`,`hline`,`hface`,`hthird`,`hvertt`,`hdirab` — all already accepted unconditionally elsewhere in this project's bridge (c)) plus `hlen` (the whole side is `a`-edges). Junction incidence, distinct-tile, and non-vertex-frontier facts are all *derived*, from `WallEndpoints.chain_endpoints`, `WallSide.wall_edges_same_tile` and `BridgeC.junction_frontier_nonvertex` — no remaining unbuilt hypothesis for that passage. **What still blocks `prop:orientmono` itself**: the theorem must be instantiated with `D`'s `target` equal to the *inflated tile*, not the ambient target — i.e. with a `CongruentDissection` object built by *restricting* a real dissection to the subset of tiles filling one occurrence `Δ_k`. **Note 2026-09-02**: `SubDissection.restrictCongruent` (new) now builds exactly that restriction, mechanically, given a covering-equality hypothesis — the same tool now shared with `thm:farregion`/`cor:farvacuous`. Establishing the covering-equality hypothesis itself (that a specific tile subset really does fill one occurrence `Δ_k`) is the actual content of "occurrence" theory in `\sub{sub:forcedrow}` and is genuinely unbuilt — confirmed, not assumed. Not closed, but the boundary-to-word passage AND the restriction bookkeeping are now both complete and general; only the covering-equality witness remains, row by row. |
| C `lem:tight` | the `γ`-injection budget at `p` | `Frontier.*` | PROVED — the budget arithmetic is available; the side of parameter `p` is a placement notion |
| C `prop:tightside` | the `p=2` side is forced | `Frontier.*` | PROVED — **re-read against the paper's own proof 2026-09-03** (elliptical "same" blocker, per the audit at line ~726, re-confirmed with more precision). The proof composes: `p_two_single_c` (profile arithmetic, likely trivial), `lem:sidenob` (VERIFIED), the apex/base-corner figures (now real via `TileAt.congruentDissection_apex_counts`/`.congruentDissection_base_corner_counts`), and — the actual remaining obstruction — "tightness makes the γ-injection a bijection, so every junction carries exactly one γ": a global count across all `2f` junctions of a specific member `(e, 2e+1)`, the same *global corner-incidence double count* shape as `lem:census`'s blocker, not merely "bridge (c)" as the 2026-08-31 spot-check phrased it. Needs a concrete `CongruentDissection` witness of a tight member with `p=2` — structural blocker 1, genuinely unbuilt, not a citation gap. |
| C `lem:chord` | the chord at the last junction | `tile_contact_face`, `contact_is_edge` | PROVED — placement layer: the apex `c`-tile and its junction |
| C `thm:ptwodead` | `p=2` is excluded on the tight subfamily | `Frontier.*` | PROVED — assembles `lem:tight`, `prop:tightside`, `lem:chord`; blocked by the weakest |
| C `thm:lastjunction` | the last-junction dichotomy | `Walls13.alpha_cannot_lay_a`, `.adjacent_angle_not_alpha` | PROVED — **citation corrected 2026-09-04**: previously cited `ApexRigidity.*`, which does not contain the paper's own cited declarations. The paper's own proof (`erdos-634-companion.tex:4048-4054`) cites `alpha_cannot_lay_a`/`adjacent_angle_not_alpha`, pre-existing in `Walls13.lean` and matching exactly (the flank dichotomy, packaged). Placement layer at the last junction of a side — blocker stands |
| C `thm:nobothmirror` | the side carrying `T₂`'s `c`-edge is not mirrored | `ApexRigidity.overlap_signs` | PROVED — the sign computation is VERIFIED; the mirroring is a placement statement |
| C `cor:figureP` | the figure at `P` is `γ + π + β + α = 2π` | `ApexRigidity.*`, `VertexFigureReal.interior_figure_cases` | PROVED — the figure is now reachable at a real interior point; locating `P` on the side is placement |
| C `prop:Uplacements` | the two placements of `U` | `ApexRigidity.drops_agree_37` | PROVED — the drop identity is VERIFIED at one member; 'the two placements' is placement |
| C `prop:figurePprime` | the figure at `P'` is `{β, 3γ}` either way | `ApexRigidity.figure_at_Pprime` | PROVED — same |
| C `prop:closepaircolumns` | the extra base columns at a close pair | `close_pair_column`, `close_pair_column_unique_general`, `one_column_per_k` | **VERIFIED 2026-09-09.** Corrected the prior "no Lean definition" blocker: the proposition's own statement never needs "a base column of a tiling" as a geometric object — checked `erdos-634-companion.tex:4315-4327` directly, "let `(x,y,z)` be a base column with `y=e+kf`..." is itself just naming a solution triple of the base equation `x·(ef)+y·(f²−e²)+z·f²=e(3f²−e²)`, an integer identity taken as a hypothesis — all four clauses are pure arithmetic. Clauses (i)–(iii) already matched `close_pair_column` exactly. Clause (iv) (uniqueness for fixed `k`) previously only had `close_pair_column_unique`, which needed `z≤e`/`z'≤e` supplied as *extra* hypotheses not in the paper's own statement (only `x,z≥1`). Closed by `close_pair_column_unique_general` (new): `z≤e` is now derived, not assumed, via `one_column_per_k` ported to `ℤ` and applied to *any* representative of `x`'s residue class (not only the canonical least-positive one) — since `e(m+1)` is monotone in the residue parameter `m`, the bound at the canonical maximal `m=q=⌊ke/f⌋` dominates every valid `m`. All four clauses now match the paper's statement exactly, with no extra hypotheses. `lake build Erdos634.All` clean, no `sorry`. |
| C `lem:pgram` | the unit parallelogram | `PgramTiling22Bridge.pgram22_covers`, `.pieceTri_congruent`, `.model_sides`, `.pieces_interiors_disjoint`, `.abs_detTri_sum_eq_target` | **VERIFIED (2026-09-02)** — checked word-for-word against erdos-634-companion.tex:4407-4416 before flipping (Rule 5). Every clause of the paper statement now has a matching real-coordinate Lean theorem, not just a `decide`-level certificate: "admits a tiling by 22 congruent copies" is `pgram22_covers` (the union of the 22 real pieces equals the carrier exactly) plus `pieceTri_congruent` (every piece congruent to the model); "congruent copies of the tile" is anchored to the actual tile shape `(2,3,4)` by `model_sides` (model's real squared sides are `64,144,256`, not just mutual self-consistency among the 22 pieces); "containment in the closed parallelogram (4 half-planes)" is `pieceTri_subset_carrier`/`mem_carrier_of_cross`; "an explicit separating edge-line for each of the 231 tile pairs" is `pieces_interiors_disjoint`; "the exact area identity ∑2Aᵢ=528√15" is `abs_detTri_sum_eq_target` (`528√15 = toR area2target`, confirmed via `area2target_eq_two_Ddet`). The vertex coordinates `(0,0),(Y₁,0),(Y₁+X₁cosβ,X₁sinβ),(X₁cosβ,X₁sinβ)` scaled by 4 match the certificate's `q1..q4` numerically (`Y₁=11,X₁=8`, `cosβ=11/16,sinβ=3√15/16`, checked `cos²β+sin²β=1`). Does **not** cover the general parallelogram (that's `prop:widecol`, a separate, still-`PROVED` row) — this is one concrete member, same standing as `thm:44`/`thm:63`'s single-member flips. |
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
| C `lem:ccornerside` | a `c`-corner carries a side `a`-edge | `TilePlacement.c_corner_side_a`, `.a_corner_side_c`, `.p_bounds` | **STALE/MISLEADING, corrected 2026-09-08** — reads as "not fast-vein", but checked directly against `paper/erdos-634-obstructions.tex:957-966`: the lemma BOX itself concludes with `1 ≤ p ≤ (f−1)/e` — full stop. The sentence about "excluding `1≤p≤(f−1)/e`... the analogue of the entire `e=1` programme" is the paper's own text, but sits OUTSIDE the lemma's formal claim, as a forward-looking remark about a *separate, later* result, not part of what `lem:ccornerside` itself asserts. This row conflated the two — same duplicate-row bug class as `cor:ladder`/`prop:reduction`. **The accurate, current entry is the other `lem:ccornerside` row (tag `O`, ~line 458)**, whose scope (the flank implication plus the parameter bounds) matches the lemma's actual statement. |
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
| `cor:basedi2e` | RESOLVED 2026-09-03 | see the full row above — `base_trichotomy_2e` built the harder `f>2e` argument directly, VERIFIED |
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
| C `prop:orientmono` | the same on a side of the **inflated tile**, plus the `β`-one-end-`γ`-the-other clause | `TilePlacement.incident_sides` | PROVED — the residue after the split. **Checked 2026-09-02**: the inflated-tile side still needs an actual inflated-tile `Dissection` object (see `prop:inflbdy`'s row — `Inflation.lean` has none yet; `Realizable.scaleTri` alone isn't the missing piece). The `β`/`γ` clause is the tile-corner fact (`α` is opposite `a`, so the two flanking corners are `β` and `γ`), available in `incident_sides` but not composed with `cornerAngle` into a statement about what a *placed* tile presents |

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

## The tile-placement layer: what already exists, corrected (2026-09-03)

**Correction, same day, after building `TileAdjacency.lean`**: on closer reading, most of what
this section originally claimed as new was already in `Dissection.lean`, just never cross-
referenced from any of the blocked rows' notes. `Dissection.second_tile_at_edge_point` already
gives existence of the other tile at an edge point (my `otherTile` adds only the `∃!`/function
packaging and the involution fact — real, but a much smaller increment than first stated).
More importantly, `Dissection.leftDir_antiparallel` (with `.leftUnit_neg`) already proves the
*direction* fact I had scoped as "not yet attempted": at a shared edge point, the two tiles' edge
directions are exact negative scalar multiples of each other — i.e. the edges *are* collinear
there, proved from `proportional_of_disjoint_pos` on the two tiles' `crossL` functionals. This
machinery is already assembled into a full theorem, `Dissection.g4_final` (checked to depend only
on the standard axioms, no `sorry`).

So the direction/collinearity step some of these rows need is **not** the blocker — it already
exists, general, for any dissection. What actually still blocks `cor:noTP`/`thm:secondc`/
`prop:cornerpara` is more specific: a **chord trace** object (line 878's own note: "chord trace /
pierce configuration / placement figure"), i.e. tracking a *specific* boundary segment's full
cover by possibly many tile edges in sequence (not just the immediate neighbor at one point), plus
matching an edge's *length* to a named value (`a`, `b`, or `c`), which needs `hausdorff_edge`-style
length bookkeeping combined with the direction fact above. `otherTile`/`leftDir_antiparallel`
together are the true first two bricks; the chord-trace object is the next, larger one.

**`ChordTraceReal.lean` landed, 2026-09-03**: `Tri.sign_trichotomy` (any tile against any external
line either lies weakly below it, weakly above it, or straddles — vertices strictly on both sides),
proved cleanly from convexity alone (`Tri.le_iff_forall_vertices_le`/`.ge_iff_forall_vertices_ge`,
extrema of a linear functional over a triangle occur at its vertices). This is real progress
`tile_contact_face` couldn't supply (it assumes one-sidedness, false exactly for a straddling
tile). Committed, builds clean.

**Segment-extraction COMPLETED, 2026-09-03, later**: `isSegment_of_convex_inter_hyperplane` is now
a real, fully proved theorem in `ChordTraceReal.lean` — any convex compact subset of the plane
lying entirely on a line `f = c` (`f ≠ 0`) equals `segment ℝ p q` for two of its own points. The
step 5 blocker (properness of `t ↦ x0 + t•v`) was resolved *without* a general "proper map" lemma:
direct norm bookkeeping instead (`‖t‖ • ‖v‖ ≤ ‖x0+t•v‖ + ‖x0‖` by the triangle inequality, so a
bound on `S` gives a bound on the pulled-back `S' ⊆ ℝ` directly, then `IsCompact` in `ℝ` from
closed+bounded). `Tri.convex_inter_hyperplane`/`.isCompact_inter_hyperplane` supply the two
hypotheses (`Convex`, `IsCompact`) for a tile's own trace specifically. `lake build Erdos634.All`
clean, no `sorry`, `#print axioms` confirms only the standard three.

This is real progress on the chord-trace bridge: any tile's intersection with any chord line is now
provably a single honest segment (not merely assumed as a `ChordTrace` field).

**Straddle-disjointness closed, 2026-09-03, later**: `trace_disjoint_of_straddle` — if *either* of
two different tiles straddles the chord line, their traces meet in at most one point, regardless of
the other tile's type. This is the piece `Dissection.sameside_edges_subsingleton` (pre-existing)
could not supply: that lemma needs *both* tiles to lie weakly on one side of the line, false
whenever a straddler is involved. `Tri.straddle_midpoint_interior` puts a shared pair's midpoint in
the straddler's interior; density of a convex body's interior near any of its own points
(`Convex.combo_interior_self_mem_interior`, sliding from an interior point of the *other* tile
towards that midpoint) produces a point interior to both, contradicting `interiors_disjoint` — no
case-split on which edge the line crosses, and no need for the other tile to straddle too (the
lemma first built this session, `straddle_trace_disjoint`, needed both; this one subsumes it and
replaced it). `lake build Erdos634.All` clean, no `sorry`, `#print axioms` confirms only the
standard three.

**A genuine subtlety found while scoping the final assembly, same pass**: two *opposite*-side
flush tiles (one weakly below the chord, one weakly above) *can* legitimately share a full edge
lying on the chord — ordinary adjacency, not a violation of `interiors_disjoint`. So summing every
touching tile's trace length naively would double-count that shared edge. A correct chord-length
theorem needs a one-sided convention — matching the one `Dissection.dirSet`/`horient` already use
for wall segments (only counting a direction's edges from one canonical side) — not naive
summation over all touching tiles. This is why `ChordDecomp.lean`'s own paper statement
(`prop:chorddecomp`) tracks "flush total" and "straddle total" as separate combinatorial
quantities rather than one undifferentiated sum: that structure is necessary, not an artifact of
the `(3,7)`-specific proof.

**What's left for a real `ChordTrace`, not yet attempted**: `contacts_cover_side`/
`length_sum_of_cover` already supply the fully general covering and summation machinery (confirmed
general-purpose, not restricted to supporting lines); what remains is assembling them, respecting
the one-sidedness above, with the segment (`isSegment_of_convex_inter_hyperplane`) and disjointness
(`trace_disjoint_of_straddle` for any straddle pair, `sameside_edges_subsingleton` for same-side
flush pairs) facts now in hand.

**The straddle-total half closed, 2026-09-03, later still (`ChordStraddleTotal.lean`, new)**: the
one-sided-convention subtlety above is specifically a *flush-flush* problem — it never arises among
straddling tiles, since `trace_disjoint_of_straddle` already makes any two tiles pairwise disjoint
(in the measure sense) the moment *either* one straddles, with no side convention needed at all.
`straddle_total_eq_sum` makes this precise and general, for *any* `Dissection` and *any* line: the
one-dimensional Hausdorff measure of the union of every straddling tile's trace equals the sum of
their individual lengths — via `MeasureTheory.measure_biUnion_finset₀` fed by
`hausdorffMeasure_one_subsingleton_eq_zero` (a subsingleton set has measure zero, since `NoAtoms`
holds for `μH[d]` at `d > 0`) applied pairwise. This is the general, member-independent form of
exactly the "straddle total" half of `prop:chorddecomp`'s own bookkeeping (that proposition's other
half, the flush total, is where the one-sided convention is actually needed — still open).
`lake build Erdos634.All` clean, no `sorry`, `#print axioms` confirms only the standard three.

**Not yet attempted, and now the last piece**: the flush total, which needs the one-sided
convention (`Dissection.dirSet`/`horient`-style) to avoid double-counting a shared edge between
opposite-side flush neighbors, plus showing flush ∪ straddle actually exhausts the chord (via
`contacts_cover_side`) to get the *total* chord length as flush total + straddle total.

**The flush-total argument, worked out precisely but NOT built, 2026-09-03**: sketched here so it
doesn't need re-deriving. Partition tiles into `lowerFlush` (all `≤ c`), `upperFlush` (all `≥ c`),
`straddlers` — exclusive by `sign_trichotomy` (a tile can't be both flush types: that would force
`f` constant on a 2D set, contradicting `f.linear ≠ 0`). Claim: `lowerFlush ∪ straddlers` alone
already covers the chord (minus the finite vertex set) — `upperFlush` tiles are never *needed*.
Proof sketch: take a chord point `x`, non-vertex, covered by tile `j` (via the already-general
`contacts_cover_side`). If `j` straddles or is `lowerFlush`, done. If `j` is `upperFlush`, then (a
nonconstant affine function can't attain its max at an interior point) `x` is on `j`'s boundary,
i.e. `OnEdge D x j` via `tile_contact_face`'s edge characterization, on an edge lying entirely on
the chord line. `Dissection.two_tiles_at_edge_point` then gives exactly one *other* tile `j'` at
`x`, and `Dissection.leftDir_antiparallel`/`.leftUnit_neg` (already general, already VERIFIED)
force `j'`'s local edge orientation *opposite* to `j`'s — meaning `j'` extends to the side with
`f < c` near `x`, so `j'` cannot itself be `upperFlush` (that would put it on the same side as
`j`, contradicting the antiparallel fact). Hence `j'` is `lowerFlush` or straddles, and `x` is
covered by `lowerFlush ∪ straddlers` via `j'` instead. Once this covering fact is built, the flush
total follows the same shape as `straddle_total_eq_sum`: `sameside_edges_subsingleton` (already
VERIFIED, general) gives pairwise disjointness *within* `lowerFlush`, `trace_disjoint_of_straddle`
gives disjointness between any `lowerFlush` tile and any straddler, so
`MeasureTheory.measure_biUnion_finset₀` applies to `lowerFlush ∪ straddlers` directly, and
`length_sum_of_cover`'s covering half (already general) finishes it against the chord's own length.
**Correction, same session, later**: the sketch above has a real gap, caught before building
anything on top of it. The "leftDir_antiparallel forces `j'` off `upperFlush`" step is not quite
right: `sameside_edges_subsingleton` only forbids two same-side tiles' edges from overlapping in
*more than one point* — it does not forbid two different `upperFlush` tiles from meeting at exactly
one shared point (e.g. two adjacent `upperFlush` tiles whose flush edges are collinear extensions
of each other, meeting end-to-end at a T-junction-style point). At such an isolated point, `x`
genuinely can be covered only by `upperFlush` tiles, so "`upperFlush` is never needed" is false as
a *pointwise* claim. It survives as a *measure-theoretic* one, though: such points are isolated
(vertices or edge-endpoints of the dissection, hence finitely many), and `length_sum_of_cover`
already tolerates a finite exceptional set `F` in its own covering hypothesis
(`σ \ F ⊆ ⋃ i, E i`) — so the fix is to fold these finitely many bad points into that `F`, not to
strengthen the pointwise claim.

**Correction to the correction, same session, later still**: on rebuilding this carefully
(`ChordFlushCover.lean`, new), the "T-junction" concern turns out to be a false alarm too, once the
**standard non-vertex convention already used everywhere else in this project**
(`Dissection.two_tiles_at_edge_point`/`chain_endpoints`'s own `hxv`) is applied consistently. If `x`
is not a vertex of *any* tile and both tiles at `x` were `upperFlush`, each tile's edge through `x`
is non-vertex-relative to that tile too, so `sameside_edges_subsingleton` would force the *two
edges themselves* (not just the point `x`) to overlap in more than one point — which the lemma
already rules out. The only way to actually reach an `upperFlush`-`upperFlush` junction is at a
*vertex* of one of the tiles, and vertices are exactly the exceptional set already excluded.
`upperFlush_edge_endpoints_eq_c` builds the key local fact this needs: a non-vertex point on an
`upperFlush` tile's edge forces *both* of that edge's endpoints exactly onto the chord line (a
strict convex combination of two values `≥ c` equals `c` only if both do). `lake build Erdos634.All`
clean, no `sorry`, `#print axioms` confirms only the standard three.

**What still isn't built**: turning the local fact into the full "`upperFlush` is never needed"
covering theorem needs walking along a maximal run of same-side flush edges sharing collinear
endpoints, to reach the genuine dissection vertex where a run must end — a chain-style induction
comparable to `BaseChain`/`WallChain`'s existing wall development, not yet attempted.

**MAJOR FIND, same session, later still**: that chain-style induction is not "not yet attempted" —
it already exists, general, in `WallChain.lean`, and does *far more* than what
`upperFlush_edge_endpoints_eq_c` alone was reaching for. `Dissection.wall_cover`/`.wall_partition`
prove, for **any line** `(f, c)` (not only a wall of the target!) and **any segment** `[u₁, u₂]` on
that line: *if* no tile's interior meets the open segment (`hwall`), the near-side chain
(`D.lineChain f c`, tile edges with both endpoints on the line and the whole tile on the `f ≤ c`
side) covers the segment exactly, with lengths summing to the segment's own length —
`wall_partition`'s proof *already* resolves the near/far-side ambiguity at every point via
`leftDir_antiparallel`/`no_second_tile_same_side`, i.e. it already contains the chain-walking
argument this row asked for, done once, generally.

This reduces the remaining work for the *full* chord-decomposition theorem from "build a chain
induction from scratch" to **assembly**: (1) get the chord's own endpoints `p, q` via
`isSegment_of_convex_inter_hyperplane` applied to `D.target.carrier` itself; (2) get each
straddler's trace as a segment the same way (already available per-tile); (3) order the finitely
many straddler segments along the chord (via the `ℝ`-parametrization `isSegment_of_convex_inter_hyperplane`'s
proof already builds); (4) the complementary gaps between consecutive straddler segments are
exactly the pieces satisfying `wall_cover`'s `hwall` hypothesis (no straddler's interior meets
them, by construction) — apply `wall_partition` to each; (5) total chord length = `straddle_total_eq_sum`'s
straddle total + the sum of `wall_partition`'s gap totals.

**Two assembly pieces landed, same session, later still**: `ChordAssembly.chord_isSegment` — item
(1) above, applying `isSegment_of_convex_inter_hyperplane` to `D.target.carrier` itself (via
`Tri.convex_inter_hyperplane`/`.isCompact_inter_hyperplane`, already built for tiles, reused
verbatim for the target). `ChordInteriorStraddle.interior_on_line_straddles` — the precise link for
item (4): a tile with an *interior* point on the chord line must straddle it (moving a small
distance along a direction where `f` increases, resp. decreases, from that interior point stays in
the tile while leaving `f ≤ c`, resp. `f ≥ c`, so `sign_trichotomy`'s two flush branches both fail).
This makes "`wall_cover`'s `hwall`" and "no straddler's trace meets here" the same condition,
exactly what item (4)'s gap construction needs. Both axiom-clean, no `sorry`,
`lake build Erdos634.All` clean.

**Item (2) landed, same session, later still**: `ChordStraddlerSegment.straddle_trace_isSegment` —
a straddling tile's own trace is a genuine segment, via `straddle_trace_nonempty` (the intermediate
value theorem along the segment between a below-`c` and an above-`c` vertex gives a witness point
on the line) feeding `isSegment_of_convex_inter_hyperplane`. Axiom-clean, no `sorry`,
`lake build Erdos634.All` clean.

**The boundary lemma landed too, same session, later still**: `ChordEndpointFrontier.chord_endpoint_not_interior`
— a chord's own extreme point is never interior to the target. If it were, a small ball around it
would contain a point of the line strictly past it (away from the other endpoint), which the ball
puts in the target and the chord identity then forces into `segment ℝ p q` — but that point's own
`AffineMap.lineMap` parameter is negative, while every point of the segment has parameter in
`[0, 1]`, contradicting `AffineMap.lineMap_injective`. Together with `chord_isSegment`, this gives
exactly the boundary control `wall_cover`'s `hint` hypothesis needs for the *outer* two points of
the chord (the target-straddling case, where the chord genuinely cuts through the interior between
its two frontier endpoints, is the only case this assembly needs — the degenerate case where the
"chord" coincides with a target edge is excluded by the target itself being required to straddle).
`lake build Erdos634.All` clean, no `sorry`, `#print axioms` confirms only the standard three.

**A first fully complete case landed, same session, later still**:
`ChordDecompositionNoStraddle.chord_decomposition_of_no_straddlers` — a genuine, standalone,
member-independent theorem: given the chord's own two distinct endpoints and a target that
straddles the line, if **no tile at all** straddles it, the near-side chain covers the whole chord
exactly, with lengths summing to the chord's own length. This is exactly `prop:chorddecomp`'s
"flush total" in the case where it *is* the whole total — realistic whenever a chord lies entirely
along tile boundaries. The generalized interior lemma this needed,
`ChordOpenSegmentInterior.Tri.straddle_openSegment_interior` (any point strictly between two of a
straddler's own chord points is interior — `straddle_midpoint_interior`'s argument with the fixed
weight `1/2` replaced by a general `s ∈ (0, 1)`), supplies `wall_cover`'s `hint` for the *whole*
open chord at once. `lake build Erdos634.All` clean, no `sorry`, `#print axioms` confirms only the
standard three.

**`p ≠ q` also closed, same session, later still**: `ChordEndpointsDistinct.straddle_two_distinct_points`
derives the chord's two distinct points directly from the straddle hypothesis, closing the one
remaining input `chord_decomposition_of_no_straddlers` took as a caller-supplied hypothesis. Among
the three vertices, straddling gives `i` below and `j` above `c`; the third vertex `k` has some
sign too, and pairing it with whichever of `i, j` has the opposite sign gives a *second* crossing
edge (via IVT along `AffineMap.lineMap`, same construction as `straddle_trace_nonempty`). Two
crossings on different vertex-pairs are automatically distinct: a point `lineMap a b r`
(`r ∈ (0,1)`, `a ≠ b`) has the excluded third vertex's barycentric coordinate exactly `0` and its
own two coordinates `1 - r` and `r` (both positive) — so a point shared between crossings built
from different pairs would need to be simultaneously zero and strictly positive at the same
coordinate. `lake build Erdos634.All` clean, no `sorry`, `#print axioms` confirms only the standard
three.

**Generalized to any gap, same session, later still**: `ChordDecompositionGap.chord_decomposition_of_gap`
— the same theorem for *any* two distinct points of the chord, not only its own extreme points
`p, q`. Nothing in `chord_decomposition_of_no_straddlers`'s proof actually needed `p, q` specifically:
`Tri.straddle_openSegment_interior` works for any two points of `D.target.carrier ∩ {f = c}`
(the target still straddles regardless of which two chord points are chosen), and `wall_cover`'s
`hwall` only ever needs to hold on the particular segment in question. This *is* the exact building
block the multi-straddler induction needs: applied to two consecutive straddler-trace endpoints (a
gap with no straddler crossing strictly inside it), it gives that gap's own near-side-chain total,
ready to be summed against `straddle_total_eq_sum`. `lake build Erdos634.All` clean, no `sorry`,
`#print axioms` confirms only the standard three.

**The ordering question resolved, same session, later still**: the finite ordering of straddler
segments along the chord doesn't need `isSegment_of_convex_inter_hyperplane`'s internal
`ℝ`-parametrization (built from a `Classical.choice`d kernel generator, not exposed as a reusable
function) — since every relevant point lies on the *same* segment `[p, q]`, plain Euclidean
`dist p x` is already a faithful, monotonic real-valued position along it, and needs no new
infrastructure to state or use.

**The gluing lemma landed too, same session, later still**: `ChordLengthAdditivity.hausdorff_segment_split`
— if `y ∈ segment ℝ x z`, the segment's own `μH¹` length splits additively into the two
sub-segments' lengths, via `MeasureTheory.hausdorffMeasure_segment` (length = `edist` of endpoints)
and the classical "triangle inequality is equality along a segment"
(`dist_add_dist_eq_iff`/`Wbtw`, needing `Plane`'s `StrictConvexSpace` instance, which
`EuclideanSpace` supplies). Combined with `chord_decomposition_of_gap` (per-gap total) and
`straddle_total_eq_sum` (straddle total), this is the last *general* ingredient: for exactly one
straddler with its own trace `[r, s]`, splitting `[p, q]` at `r` then at `s` gives
`length[p,q] = length[p,r] + length[r,s] + length[s,q]`, matching a gap total, the straddle total,
and a second gap total. `lake build Erdos634.All` clean, no `sorry`, `#print axioms` confirms only
the standard three.

**The concrete one-straddler theorem assembled, same session, later still**:
`ChordDecompositionOneStraddler.chord_decomposition_one_straddler` — a real, complete, assembled
result: given the chord's endpoints `p, q`, the one straddler's own trace endpoints `r, s`, the
betweenness order (`Wbtw p r q`, `Wbtw r s q`), and that no tile's interior meets either open gap
`(p, r)` or `(s, q)`, the near-side chain's total over the whole chord splits exactly into the two
gap totals (`chord_decomposition_of_gap`, applied twice) plus the straddler's own trace length —
glued via `hausdorff_segment_split` applied twice and `ring`. `lake build Erdos634.All` clean, no
`sorry`, `#print axioms` confirms only the standard three.

The two gaps' "no tile straddles inside" conditions were taken directly as hypotheses there
(matching `chord_decomposition_of_gap`'s own style) rather than derived from "no *other* tile
straddles anywhere" — that reduction needed one small lemma, now built:
`ChordBetweennessDisjoint.openSegment_disjoint_segment_of_wbtw` — if `r` is weakly between `p` and
`s` (`p ≠ r`), the open segment `(p, r)` and the closed segment `[r, s]` are disjoint. Proved via
distance additivity along betweenness chains (`dist_add_dist_eq_iff`, the same fact
`hausdorff_segment_split` uses, plus `Wbtw.trans_right_left` for the transitivity step): a point of
`(p, r)` is strictly closer to `p` than `r` is, while a point of `[r, s]` is weakly farther from `p`
than `r` is (since `r` lies between `p` and that point too, by transitivity). `lake build
Erdos634.All` clean, no `sorry`, `#print axioms` confirms only the standard three. With this,
`chord_decomposition_one_straddler`'s two `hgap` hypotheses (currently taken directly) can be
derived from "no other tile straddles" plus the betweenness order in a follow-up pass — not yet
wired together, but the blocking fact no longer needs deriving.

**The wiring done, same session, later still (2026-09-03)**:
`ChordDecompositionOneStraddlerFinal.chord_decomposition_one_straddler'` — the follow-up pass
flagged above. Same conclusion as `chord_decomposition_one_straddler`, but its two `hgap`
hypotheses are now *derived* rather than assumed: given only the natural global condition
`hunique` ("no tile other than the one straddler `m` straddles anywhere," i.e.
`∀ k ≠ m, ¬(tile k has a point strictly below and a point strictly above the line)`) plus the
betweenness order and `m`'s own trace `= segment r s`, it proves both open gaps `(p, r)` and
`(s, q)` are free of every tile's interior, then calls `chord_decomposition_one_straddler`
directly. The derivation: for `y` in an open gap with `y` interior to some tile `k`,
`interior_on_line_straddles` gives that `k` straddles; if `k ≠ m`, `hunique` contradicts that
directly; if `k = m`, `openSegment_disjoint_segment_of_wbtw` (applied to the gap-side betweenness
order, using `Wbtw.trans_right_left`/`Wbtw.symm`/`segment_symm`/`openSegment_symm` to put each gap
into the lemma's `(p,r)`/`[r,s]` shape) shows `y` can't lie in `m`'s own trace, contradicting
`hymem`. `lake build Erdos634.All` clean, no `sorry`, `#print axioms` confirms only the standard
three. This closes out the one-straddler case completely from the natural hypothesis — no
remaining gap between what's assumed and what a real dissection actually gives you.

**The two-straddler instance, same session, later still (2026-09-03)**:
`ChordDecompositionTwoStraddlers.chord_decomposition_two_straddlers` — the next concrete instance
beyond one straddler, same style as `chord_decomposition_one_straddler`'s first pass (the three
gap-freedom conditions taken directly as hypotheses, not yet derived from a single global
"no other tile straddles anywhere" condition): given two straddlers' trace endpoints `r₁,s₁` and
`r₂,s₂` occupying consecutive stretches of the chord in the order `p, r₁, s₁, r₂, s₂, q`, the
near-side chain's total splits into three gap totals (`chord_decomposition_of_gap`, on `[p,r₁]`,
`[s₁,r₂]`, `[s₂,q]`) plus the two straddlers' own trace lengths, glued via
`hausdorff_segment_split` applied four times. `lake build Erdos634.All` clean, no `sorry`,
`#print axioms` confirms only the standard three.

Deriving this one's three gap-freedom conditions from a global `hunique` (as
`ChordDecompositionOneStraddlerFinal` did for the one-straddler case) is strictly harder than that
case: the *middle* gap `(s₁,r₂)` must be shown disjoint from *both* straddlers' own traces, not
just one, which needs a transitive betweenness argument beyond what
`openSegment_disjoint_segment_of_wbtw` gives directly (that lemma handles one adjacent pair; the
middle gap sits between two). Not attempted this pass — recorded as the next piece rather than
forced through.

**The far-gap disjointness lemma, same session, later still (2026-09-03)**:
`ChordBetweennessDisjointFar.openSegment_disjoint_segment_of_wbtw_far` — generalizes
`openSegment_disjoint_segment_of_wbtw` from a far segment `[r, s]` sharing its endpoint with the
gap's own right endpoint `r`, to a far segment `[u, v]` merely starting at or beyond a point `r`
weakly between `p` and `u` (`r ≠ u`): the open gap `(p, r)` and `[u, v]` are still disjoint. Same
distance-additivity proof shape, with `Wbtw.trans_expand_left` folding the extra `r → u` hop into
a single `Wbtw p r y` fact. `lake build Erdos634.All` clean, no `sorry`, `#print axioms` confirms
only the standard three.

This is exactly the fact `chord_decomposition_two_straddlers`'s middle gap `(s₁, r₂)` needs to rule
out *both* straddlers' traces from a global `hunique` condition (not just the adjacent one, as the
one-straddler case only needed): applied one way it rules out `m₁`'s trace `[r₁, s₁]` reached via
the reversed gap `(r₂, s₁)`; applied the other way it rules out `m₂`'s trace `[r₂, s₂]` directly.
Not yet wired into a `chord_decomposition_two_straddlers'` (the two-straddler analogue of
`chord_decomposition_one_straddler'`) — the lemma exists, the assembly doesn't.

**The two-straddler wiring done, same session, later still (2026-09-03)**:
`ChordDecompositionTwoStraddlersFinal.chord_decomposition_two_straddlers'` — closes the two-straddler
case the same way `ChordDecompositionOneStraddlerFinal` closed the one-straddler case: all three
`hgap` hypotheses are now derived from the natural `hunique` condition ("no tile other than `m₁` or
`m₂` straddles anywhere") plus the betweenness order, instead of assumed directly. The key
observation that made this tractable: the *middle* gap `(s₁, r₂)` is actually adjacent to **both**
straddlers' traces (it shares `s₁` with `m₁`'s trace `[r₁, s₁]` and `r₂` with `m₂`'s trace
`[r₂, s₂]`), so `openSegment_disjoint_segment_of_wbtw` (the plain adjacent lemma) handles it on both
sides — the initial plan to reach for the "far" lemma here was wrong; `ChordBetweennessDisjointFar`
is needed only for the two *outer* gaps reaching the *non-adjacent* straddler (gap `(p, r₁)` vs
`m₂`'s trace, and gap `(s₂, q)` vs `m₁`'s trace). One extra hypothesis beyond
`chord_decomposition_two_straddlers`'s own was needed to make the betweenness chain derivable:
`hw_r1s1r2 : Wbtw ℝ r₁ s₁ r₂` (the two traces occupy their stretches in the stated order, not just
each individually between `p` and `q`), plus two nondegeneracy hypotheses `r₁ ≠ s₁`, `s₁ ≠ s₂`
ruling out collapsed traces. `lake build Erdos634.All` clean, no `sorry`, `#print axioms` confirms
only the standard three.

Two straddlers are now closed from the natural hypothesis exactly as one straddler is. The pattern
for arbitrary many straddlers is now visible: each interior gap sits adjacent to its two flanking
straddlers (handled by the plain lemma) and reaches every *other* straddler only through the "far"
lemma chained across however many intervening trace-and-gap stretches lie between them — a genuine
finite induction on the sorted list of trace endpoints, not yet built.

**The three-straddler instance, same session, later still (2026-09-03)**:
`ChordDecompositionThreeStraddlers.chord_decomposition_three_straddlers` — the next rung of the
ladder, mechanically extending the two-straddler assembly: three straddlers' trace endpoints
occupying consecutive stretches in the order `p, r₁, s₁, r₂, s₂, r₃, s₃, q`, the near-side chain's
total splits into four gap totals plus the three straddlers' own trace lengths, glued via
`hausdorff_segment_split` applied six times. Gap-freedom taken directly as hypotheses (not yet
derived from `hunique` — the two *middle* gaps here each reach a non-adjacent straddler across one
more intervening stretch than the two-straddler case ever needed, the next scaling-up of the
`ChordDecompositionTwoStraddlersFinal` derivation). `lake build Erdos634.All` clean, no `sorry`,
`#print axioms` confirms only the standard three.

**The three-straddler wiring done, same session, later still (2026-09-03)**:
`ChordDecompositionThreeStraddlersFinal.chord_decomposition_three_straddlers'` — closes the
three-straddler case the same way the two-straddler case closed, confirming the pattern
generalizes without changing the far lemma itself: `openSegment_disjoint_segment_of_wbtw_far`
needed no modification to reach two hops away (gap `(p,r₁)` vs `m₃`'s trace, and gap `(s₃,q)` vs
`m₁`'s trace) — only the betweenness-chain bookkeeping grows, built via repeated
`Wbtw.trans_expand_left`/`Wbtw.trans_right` composition and three `dist`-additivity nondegeneracy
arguments (`r₁≠r₂`, `r₂≠r₃`, `r₁≠r₃`, `s₁≠s₃` derived, not assumed). Two extra linking hypotheses
(`hw_r1s1r2`, `hw_r2s2r3`) and `hwr3q : Wbtw r₃ s₃ q` (mirroring `hwr2`'s reach to `q`) round out
what `chord_decomposition_three_straddlers`'s own hypotheses didn't supply. `lake build
Erdos634.All` clean, no `sorry`, `#print axioms` confirms only the standard three.

Three straddlers now closed from the natural hypothesis exactly as one and two are. The scaling
pattern is now confirmed across N=1,2,3: each gap is adjacent to its immediate neighbor(s) (plain
lemma) and reaches every other straddler through the far lemma with betweenness facts chained one
hop per intervening stretch. This is exactly the recursive step a real induction on the sorted list
of trace endpoints would formalize — the concrete instances now make that induction's shape fully
visible, though the induction itself (arbitrary `n`, not spelled out three times by hand) is still
not built.

**The reusable chain lemma, same session, later still (2026-09-03)**:
`WbtwChain.wbtw_chain` — extracts the pattern repeated by hand three times (once per straddler
count) in the `*Final` files above: given a sequence `g : ℕ → Plane` where every consecutive triple
satisfies `Wbtw`, every consecutive pair is distinct, and `g` is injective, `Wbtw ℝ (g i) (g j)
(g k)` holds for *every* `i ≤ j ≤ k`, not just indices a fixed small distance apart. Built via a
genuine two-stage induction: `wbtw_chain_step` first shows the chain reaches one index further
(`Wbtw (g i) (g j) (g (j+1))` for `i < j`, by `Nat.le_induction` composing `Wbtw.trans_expand_right`
at each step), then `wbtw_chain` induces on the third index using `wbtw_chain_step` as its own step
lemma (`Wbtw.trans_expand_left`), handling the index-collision at the base of each induction
explicitly. `lake build Erdos634.All` clean, no `sorry`, `#print axioms` confirms only the standard
three for both theorems.

This is the reusable tool the one/two/three-straddler `*Final` files each re-derived by hand at
their own fixed length (`hpr1r2`, `hpr1r3`, `hr1r2r3`, ... in `ChordDecompositionThreeStraddlersFinal`
are all instances of `wbtw_chain` applied to the sequence `p, r₁, s₁, r₂, s₂, r₃, s₃, q`). Not yet
retrofitted into those files (their hand derivations still stand, verified independently) — the
value is unlocking the *general* induction over an arbitrary straddler count, which no longer needs
a fresh by-hand betweenness argument at every new length once the straddler traces are packaged as
such a sequence `g`.

**The bounded variant, same session, later still (2026-09-03)**:
`WbtwChain.wbtw_chain_bounded` / `wbtw_chain_step_bounded` — `wbtw_chain` itself needs
`Function.Injective g` on *all* of `ℕ`, which no genuinely finite chain of straddler trace
endpoints can supply (any sensible packaging of a finite straddler list into `g : ℕ → Plane` is
eventually constant or repeats, breaking global injectivity outright). This finite-range version
threads a bound `K` through both theorems and their induction, needing `hchain`, `hne` and
injectivity only for indices `≤ K`: `Wbtw ℝ (g i) (g j) (g k)` for every `i ≤ j ≤ k ≤ K`. `lake
build Erdos634.All` clean, no `sorry`, `#print axioms` confirms only the standard three for both.

This is the form the general induction will actually call: a `Dissection`'s straddler set is a
`Finset (Fin N)` (`ChordStraddleTotal.straddlers`), always finite, so packaging its sorted trace
endpoints as `g : Fin (2n+2) → Plane` (or `g : ℕ → Plane` constant past `2n+1`) and invoking
`wbtw_chain_bounded` with `K = 2n+1` is now a closed, checkable step — no infinite-injectivity
obligation left to discharge first.

**The sorting tool, same session, later still (2026-09-03)**:
`WbtwChain.wbtw_trichotomy_of_wbtw` — the piece still missing after `wbtw_chain_bounded`: given a
straddler set (a `Finset (Fin N)`, always finite, `ChordStraddleTotal.straddlers`), packaging its
traces into a sequence `g` in the *correct order* first needs a total order on the chord's own
points to sort by. This theorem supplies exactly that: any two points `x, y` both weakly between
`p` and `q` are comparable from `p` (`Wbtw p x y ∨ Wbtw p y x`) — proved via
`wbtw_total_of_sameRay_vsub_left` (an existing Mathlib total-order-from-a-ray fact) applied to the
same-ray facts `Wbtw.sameRay_vsub_left` gives from `hx`, `hy`, transitively composed through the
common direction `q -ᵥ p` (with the degenerate `p = q` case handled via `wbtw_self_iff`). `lake
build Erdos634.All` clean, no `sorry`, `#print axioms` confirms only the standard three.

With `wbtw_trichotomy_of_wbtw` (sorting) and `wbtw_chain_bounded` (the ordered chain's betweenness
facts) both in hand, the three missing pieces for the general induction are down to: (1) actually
building the sorted `List`/`Fin`-indexed sequence of straddler trace endpoints from a `Finset`
straddler set via this order (a `Finset.sort`/`List.Sorted` construction, not yet done), (2)
checking that construction's output satisfies `wbtw_chain_bounded`'s three hypotheses (mechanical
given the sorting is genuinely by this order), and (3) the sum-over-Finset bookkeeping combining
`chord_decomposition_of_gap` on each gap with `straddle_total_eq_sum` on the straddler traces
themselves (this piece has no new geometry left, per `ChordDecompositionGap.lean`'s own docstring —
it is `Finset.sum` induction over a sorted list, order-theory not geometry).

**The antisymmetry companion, same session, later still (2026-09-03)**:
`WbtwChain.wbtw_antisymm_of_wbtw` — `wbtw_trichotomy_of_wbtw` alone gives only a total *preorder*
(both disjuncts can hold at once, e.g. trivially when `x = y`); this closes it into an honest
comparator: `Wbtw p x y` and `Wbtw p y x` together force `x = y`, by the same distance-additivity
trick used throughout this session's chain lemmas (`dist p x + dist x y = dist p y`, its mirror
image, and `dist x y = dist y x` force `dist x y = 0`). `lake build Erdos634.All` clean, no `sorry`,
`#print axioms` confirms only the standard three.

**The transitivity companion, same session, later still (2026-09-03)**:
`WbtwChain.wbtw_trans_of_wbtw` — the last order axiom (after trichotomy and antisymmetry) needed to
sort a chord's points by `wbtw_trichotomy_of_wbtw`: if `x, y, z` all lie weakly between `p` and `q`,
`Wbtw p x y`, and `Wbtw p y z`, then `Wbtw p x z`. Proved by taking the trichotomy for `x, z`
directly and ruling out its "wrong" branch (`Wbtw p z x`) via the same three-equation
distance-additivity trick as the other two companions — that branch forces `z = x`, collapsing to
the trivial case. `lake build Erdos634.All` clean, no `sorry`, `#print axioms` confirms only the
standard three.

`WbtwChain.lean` now has all three order axioms (`wbtw_trichotomy_of_wbtw`, `_antisymm_`,
`_trans_`) that a real sort of a straddler set's trace endpoints needs, plus the chain-of-Wbtw
consumer (`wbtw_chain_bounded`) that sorted sequence must satisfy. What remains for the general
induction is purely mechanical at this point: (1) build the sorted `List`/`Fin`-indexed sequence
from a `Finset` straddler set using these three facts (a `List.Sorted` / insertion-sort-style
construction, not yet done — no new geometry, only combinatorics), (2) check that construction
satisfies `wbtw_chain_bounded`'s hypotheses, (3) the `Finset.sum` induction combining
`chord_decomposition_of_gap` with `straddle_total_eq_sum`.

**The oriented-trace lemma, same session, later still (2026-09-03)**:
`WbtwOrientedTrace.oriented_trace_of_wbtw` — `straddle_trace_isSegment` hands back a trace as
`segment ℝ r s` with `r, s` in no particular order relative to the chord's own endpoints `p, q`;
this reorders it into the canonical "near, far" form the chain assembly needs (`r'` weakly between
`p` and `s'`), via `wbtw_trichotomy_of_wbtw` plus `segment_symm` to swap when the given order is
backwards. `lake build Erdos634.All` clean, no `sorry`, `#print axioms` confirms only the standard
three.

With this, every straddling tile's trace can be canonically oriented, `WbtwChain`'s three order
facts let those oriented traces be sorted, and `wbtw_chain_bounded` consumes the sorted sequence.
What remains for the general induction is now purely the combinatorial assembly: build the sorted
list from the `Finset` straddler set (via `Finset.sort` or an insertion-sort-style induction using
`wbtw_trichotomy_of_wbtw`/`wbtw_antisymm_of_wbtw`/`wbtw_trans_of_wbtw` as the order), verify it
satisfies `wbtw_chain_bounded`'s hypotheses, and run the `Finset.sum` induction combining
`chord_decomposition_of_gap` with `straddle_total_eq_sum`. No further individual geometric facts
are missing — every piece this session built is aimed at exactly this remaining assembly.

**Two more chain-composition lemmas, same session, later still (2026-09-03)**:
`WbtwChain.wbtw_of_wbtw_wbtw` / `wbtw_middle_of_wbtw_wbtw` — built while trying to separate two
straddlers' traces (the next combinatorial piece the general induction needs): `wbtw_of_wbtw_wbtw`
reproves `wbtw_trans_of_wbtw`'s conclusion (`Wbtw p a b, Wbtw p b c ⟹ Wbtw p a c`) *without* an
external upper-bound point playing `q`'s role — composing the two `SameRay` facts directly through
`b` and ruling out the wrong branch the same distance-additivity way. `wbtw_middle_of_wbtw_wbtw`
then converts that "closer to `p`" order information into actual segment membership: `Wbtw p a b`
and `Wbtw p b c` together give `Wbtw a b c` (`b` is genuinely between `a` and `c`, no reference to
`p` in the conclusion) — combining the three distance-additivity equations directly. `lake build
Erdos634.All` clean, no `sorry`, `#print axioms` confirms only the standard three for both.

This is exactly the fact needed to show two straddlers' near/far trace endpoints, once compared via
`wbtw_trichotomy_of_wbtw`, actually land *inside* each other's trace segments — the step toward
proving two straddlers' traces (known disjoint in at most one point, via `trace_disjoint_of_straddle`)
must be entirely separated (one trace's far endpoint precedes the other's near endpoint), which is
the combinatorial fact the sorted-gap construction needs. Not yet assembled into that separation
theorem — this is its key ingredient, not the theorem itself.

**The separation theorem, same session, later still (2026-09-03)**:
`WbtwTracesSeparated.traces_separated_of_disjoint` — the combinatorial fact the sorted assembly
needs, now proved: two straddlers' oriented traces (near endpoint first, both on the chord `[p,q]`)
that meet in at most one point (`trace_disjoint_of_straddle`) are *entirely* separated — one
trace's far endpoint weakly precedes the other's near endpoint. Proved by contradiction: assuming
neither separation, a 2×2 case split comparing `r₁` vs `r₂` and `s₁` vs `s₂` (via
`wbtw_trichotomy_of_wbtw`) always produces, via `wbtw_middle_of_wbtw_wbtw`, two points landing in
*both* traces; the disjointness hypothesis forces them equal, contradicting either the assumed
non-separation directly (that point would trivially satisfy `Wbtw`'s reflexivity) or the traces'
own nondegeneracy. `lake build Erdos634.All` clean, no `sorry`, `#print axioms` confirms only the
standard three.

This is the last individual combinatorial fact the sorted multi-straddler assembly needs. What
remains is now genuinely just the induction/bookkeeping itself: order a `Finset` straddler set's
oriented traces via `wbtw_trichotomy_of_wbtw` (now known total on this set, thanks to
`traces_separated_of_disjoint` ruling out interleaving), package the sorted list into
`wbtw_chain_bounded`'s `g`, and close the `Finset.sum` induction against `chord_decomposition_of_gap`
+ `straddle_total_eq_sum`. No further per-pair geometric lemma is missing.

**The distance-coordinate identification, same session, later still (2026-09-03)**:
`WbtwDistCoord.wbtw_iff_dist_le_of_wbtw` — identifies `Wbtw p · ·` concretely as the order of
`dist p ·`: for `x, y` both weakly between `p` and `q`, `Wbtw p x y ↔ dist p x ≤ dist p y`. Forward
via `dist_add_dist_eq_iff` and nonnegativity; backward via `wbtw_trichotomy_of_wbtw`, ruling out the
wrong branch through the same distance-collapse trick as the other companions. `lake build
Erdos634.All` clean, no `sorry`, `#print axioms` confirms only the standard three.

This is what lets a `Finset` of straddler trace endpoints be sorted using `ℝ`'s own decidable
linear order (`Finset.sort`/`List.sort` on `dist p ·`) instead of building bespoke `Preorder`/
`LinearOrder` instances on `Plane` directly — the last piece of order-theoretic scaffolding; what
remains is the actual sort-and-sum construction.

**The recursive step itself, same session, later still (2026-09-03)**:
`ChordDecompositionCons.chord_decomposition_cons` — the genuine recursive step of the general
finite induction, stated once and reusable at any depth: given the leading gap `(p, r)`'s own total
(via `chord_decomposition_of_gap`), the trace length `[r, s]`, and *whatever total already holds*
for the rest of the chord `[s, q]` (taken as a hypothesis `hrest : hausdorff(segment s q) = Trest`,
established however that sub-chord total was itself proved — directly by
`chord_decomposition_of_no_straddlers`, or recursively by this same lemma), the whole chord's total
splits as their sum. Proved by two `hausdorff_segment_split` applications plus substitution — no new
geometry, exactly the "no new geometry left" bookkeeping this file's own header predicted. `lake
build Erdos634.All` clean, no `sorry`, `#print axioms` confirms only the standard three.

This one lemma, applied once per straddler, *is* the induction: `chord_decomposition_one_straddler`
= `chord_decomposition_cons` applied once with `Trest` supplied by `chord_decomposition_of_gap`
directly on `[s, q]`; `_two_straddlers` = applied twice, etc. What is genuinely still missing is not
another geometric fact but the *packaging*: given a `Finset` straddler set, sort it (via
`wbtw_trichotomy_of_wbtw`/`wbtw_iff_dist_le_of_wbtw`, `Finset.sort` or `List` induction) into the
sequence `chord_decomposition_cons` consumes one straddler at a time, and prove by induction on that
sorted list's length that repeated application closes the whole chord — a `List.rec`/`Finset.sum`
argument over data this session's lemmas fully support, not yet written.

**The base-case gap-freedom fact, same session, later still (2026-09-03)**:
`WbtwGapFreeOfMinimal.gap_free_of_minimal` — the `hgap` hypothesis
`chord_decomposition_cons` needs at each step of the induction: if a straddler `m`'s oriented trace
`[r, s]` is *first* (every point of every other straddler's own trace is weakly farther from `p`
than `r`), no tile's interior meets the open gap `(p, r)`. Any interior point there must belong to a
straddling tile (`interior_on_line_straddles`); if that tile is `m`, `openSegment_disjoint_segment_
of_wbtw` rules it out; otherwise minimality plus `wbtw_antisymm_of_wbtw` collapses the point to `r`
itself, contradicting the gap's own openness. `lake build Erdos634.All` clean, no `sorry`,
`#print axioms` confirms only the standard three.

With this, `chord_decomposition_cons`'s `hgap` hypothesis is *derived*, not assumed, at every step
of a sort-and-recurse construction: pick the straddler minimizing "how far its trace starts from
`p`" (well-defined by `Finset.exists_min_image` on the finite straddler set, tie-broken
lexicographically by far-endpoint distance if two straddlers share a near endpoint — the one
remaining subtlety identified, not yet needed since no instance forces it), apply
`gap_free_of_minimal` for its gap-freedom, `chord_decomposition_cons` to peel it off, and recurse on
the remaining straddler set restricted to `[s, q]` by strong induction on `Finset.card`. Every
individual fact this recursion needs now exists; assembling the induction itself (the
`Finset.card`-recursion, the choice-function packaging of each straddler's oriented trace, and
verifying the recursive call's straddler set is exactly the right restriction) is real remaining
work, sized like a standalone small project rather than one more lemma.

**The recursive-restriction fact, same session, later still (2026-09-03)**:
`WbtwMinimalPrecedesRest.far_precedes_of_minimal` — the fact needed to set up the recursive call
correctly: given a minimal straddler `m` (near endpoint `r` first among all straddlers) with
oriented trace `[r, s]`, and any *other* straddler's own nondegenerate oriented trace `[rk, sk]`
meeting `m`'s in at most one point, `m`'s far endpoint `s` weakly precedes `rk`. Proved via
`traces_separated_of_disjoint`: the other separation direction would force, via `wbtw_of_wbtw_wbtw`
and `wbtw_antisymm_of_wbtw` applied twice, the other straddler's *entire* trace to collapse onto `r`
itself — contradicting its nondegeneracy. `lake build Erdos634.All` clean, no `sorry`, `#print
axioms` confirms only the standard three.

This is exactly what guarantees the recursive sub-chord `[s, q]` in the induction contains *all* the
remaining straddlers' traces (not just excludes `m`'s own) — the invariant the recursion needs to
be well-founded. Every individual fact for the general N-straddler theorem is now built: the
recursive step (`chord_decomposition_cons`), its gap-freedom (`gap_free_of_minimal`), its recursive
restriction (`far_precedes_of_minimal`), and the sort order
(`wbtw_trichotomy_of_wbtw`/`_antisymm_`/`_trans_`/`_iff_dist_le_`/`oriented_trace_of_wbtw`). What
remains is exclusively the `Finset.card` strong-induction wrapper gluing these together with a
choice-function packaging of each straddler's oriented trace — an engineering task, not a
mathematical gap.

**The exact remaining specification, worked out precisely (2026-09-03, late)**: attempting the
wrapper induction directly (rather than continuing to describe it abstractly) surfaced the real
obstacle: a clean statement over a `Finset (Fin N)` of straddlers needs an *exclusion invariant*
("every straddler not in the current set has its whole trace outside the current sub-chord") that
is exactly as hard to maintain correctly through the recursion as the induction itself — restating
it does not shrink it. The tractable split is the one `straddle_total_eq_sum`'s own docstring
already pointed at: separate "prove the sum splits *given* a sorted chain" from "sort a `Finset`
into that chain." The first half is what `wbtw_chain_bounded` was built for: package the straddler
data as `pts : List Plane` (`p :: r₁ :: s₁ :: ⋯ :: rₙ :: sₙ :: [q]`, length `2n+2`) with `tiles :
List (Fin N)` (length `n`), hypotheses `hchain : ∀ i, i + 2 ≤ 2n+1 → Wbtw ℝ (pts.get i) (pts.get
(i+1)) (pts.get (i+2))` (exactly `wbtw_chain_bounded`'s own shape, `K = 2n+1`), `hmtrace : ∀ i < n,
(D.tile (tiles.get i)).carrier ∩ line = segment ℝ (pts.get (2i+1)) (pts.get (2i+2))`, and `hgap : ∀
i ≤ n, gap_free_of_minimal`'s conclusion on `(pts.get (2i), pts.get (2i+1))` — then prove by
induction on `n` (peeling the front pair off `pts` and `tiles`, one call to `chord_decomposition_cons`
per step) that the total splits. This is genuinely just index bookkeeping over `List.get`/`Fin`
arithmetic now — no further geometric fact is missing, and it does not need the exclusion invariant
at all (that invariant is only needed to justify a sort *exists* with the right shape, the second,
separate half). Not written this session: the index arithmetic alone is real work, and forcing it
through under time pressure risks exactly the kind of rushed, unchecked claim `/goal` forbids.

**The general induction, built (2026-09-03, later still)**: `ChordDecompositionChain.
chord_decomposition_of_chain` — the "sum splits given a sorted chain" half specified precisely
above, now proved by genuine induction on `n` (arbitrary straddler count), not spelled out by hand
at any fixed length. Packaged exactly as specified: `g : ℕ → Plane` (`g 0 = p`, `g(2i+1), g(2i+2)`
the `i`-th straddler's oriented trace, `g(2n+1) = q`), consecutive-triple `Wbtw` facts
(`wbtw_chain_bounded`'s own hypothesis shape), and gap-freedom for each of the `n+1` gaps. The
`succ` step: shift `g`/`tiles` by one pair to get the induction hypothesis's own hypotheses (pure
index arithmetic, `ring`/`omega`), invoke `wbtw_chain_bounded` once for the single non-consecutive
fact needed (`Wbtw (g 0) (g 2) (g (2(n+1)+1))`, i.e. `Wbtw p s q`), apply `chord_decomposition_cons`
with the shifted IH as `Trest`, then reindex both `Finset.sum`s via `Finset.sum_range_succ'` to
match. `lake build Erdos634.All` clean, no `sorry`, `#print axioms` confirms only the standard
three.

This closes the "given a sorted chain" half completely for arbitrary `n`. The remaining half — given
a `Finset` straddler set, produce such a chain (`g`, `tiles`) satisfying `chord_decomposition_of_chain`'s
own hypotheses — needs the exclusion invariant flagged above (`gap_free_of_minimal` and
`far_precedes_of_minimal` supply exactly the per-step facts a `Finset.card` strong induction would
need to construct it) but is not yet built. `prop:chorddecomp` itself further needs the flush total
and the member-specific `(3,7)` numerics on top of this — this file is the general,
member-independent skeleton, not the full proposition.

**The global-bound simplification, same session, later still (2026-09-03, later still)**:
`WbtwTraceInTarget.wbtw_of_mem_tile_trace` — the key simplification for the `Finset`-sort
construction: fixing the target's own chord endpoints `P, Q` (`chord_isSegment`) once for the whole
dissection, *any* point of *any* tile's trace satisfies `Wbtw ℝ P x Q` — via `tile_subset_target`
(a tile's carrier ⊆ the target's) plus `mem_segment_iff_wbtw`. `lake build Erdos634.All` clean, no
`sorry`, `#print axioms` confirms only the standard three.

This removes the awkwardness that would otherwise recur throughout the sort construction: every
`wbtw_trichotomy_of_wbtw`/`_antisymm_`/`_trans_` call needs a *common* upper bound between the two
points compared, and without this lemma that bound would need to be re-derived (or re-threaded) for
each shifting recursive sub-chord `[p, q]`. With it, `Q` (the target's own far endpoint) serves as
that common bound throughout the whole construction unconditionally, for every straddler
simultaneously — comparisons only ever need `Wbtw P p Q` (how far the current sub-chord start has
advanced) tracked alongside the recursion, not a fresh bound per straddler.

**A real attempt at the `Finset` wrapper, and what it found (2026-09-03, later still)**: attempted
the full construction directly. It surfaced a genuine correction to the plan recorded above: the
exclusion invariant must bound an excluded straddler's *far* endpoint (`Wbtw ℝ P (S k) p`), not its
near endpoint — bounding only `R k` leaves room for the excluded straddler's trace to still reach
past `p` into the current gap, which is not actually excluded. `far_precedes_of_minimal` already
proves the right thing to *maintain* this invariant across steps; the base case (`T` empty) needing
it correctly is what exposed the near/far distinction. Also needed and now built:
`WbtwChain.wbtw_global_of_local` — the converse of `wbtw_middle_of_wbtw_wbtw`: if `a` lies weakly
between a fixed reference `P` and `c`, and `b` lies weakly between `a` and `c` (e.g. a point of the
trace `[a, c]`), then `b` (and `a`) are themselves weakly ordered from `P` too
(`hac.trans_right_left hlocal`, `hac.trans_right hlocal` — both already-existing Mathlib
combinators, just newly composed). `lake build Erdos634.All` clean, no `sorry`, `#print axioms`
confirms only the standard three.

The full wrapper attempt itself did not survive contact with the base case's actual proof
obligations cleanly — assembling `wbtw_global_of_local`, `far_precedes_of_minimal`, and
`gap_free_of_minimal` correctly into one `Finset.strongInduction` produced tactic-level errors that
a rushed fix would have papered over with unsound term combinators; the attempt was discarded rather
than committed with a `sorry` or a wrong proof, per this project's standing rule. The corrected
exclusion invariant above is the real, usable output of the attempt and is recorded precisely so the
next attempt does not re-derive it. What remains unbuilt: the actual `Finset.strongInduction`
assembly, redone carefully with the corrected invariant.

**The base-case contradiction, isolated and verified (2026-09-03, later still)**:
`ChordFinsetBaseCase.not_mem_gap_of_far_precedes` — rebuilding the `Finset` wrapper attempt in small
individually-verified pieces this time (per the previous attempt's own lesson): with the corrected
exclusion invariant (`Wbtw P (S_k) p`, far endpoint), no point of an excluded straddler's own trace
can lie in the current open gap `(p, Q)`. Proved via the same distance-additivity "sandwich" plus
two antisymmetry collapses used throughout this session's chain lemmas. `lake build Erdos634.All`
clean, no `sorry`, `#print axioms` confirms only the standard three.

This is exactly the base case (`T` empty) of the `Finset.strongInduction` the full wrapper needs.
Verifying it standalone, in isolation from the rest of the construction, before assembling the
induction is the deliberate fix for the previous attempt's failure mode. The induction step itself
(extracting a minimal element via `Finset.exists_min_image`, applying `gap_free_of_minimal` and
`chord_decomposition_cons`, and maintaining the invariant via `far_precedes_of_minimal` and
`wbtw_global_of_local`) is the next piece, not yet assembled.

**All four induction pieces built and independently verified (2026-09-03, later still)**: rebuilt
the `Finset` wrapper attempt in small, separately-checked pieces (the deliberate fix from the
earlier failed attempt): `ChordFinsetBaseCase.not_mem_gap_of_far_precedes` and
`ChordFinsetBaseCaseGap.gap_free_of_all_excluded` (base case: `T` empty), `ChordFinsetStepGap.
gap_free_of_finset_step` (induction step's leading-gap-freedom, converting the *global* minimality
comparison `Finset.exists_min_image` actually produces into what `gap_free_of_minimal` needs), and
`ChordFinsetInvariant.excl_new_self` / `excl_carries_forward` (the exclusion invariant survives one
step, for the newly- and previously-excluded straddlers respectively). All four `lake build
Erdos634.All` clean, no `sorry`.

**What stopped the final assembly**: wiring these four into one `Finset.strongInduction` surfaced
two genuine degenerate edge cases neither previous pass had accounted for: (1) the base case's own
`p ≠ Q` side condition (needed to invoke `chord_decomposition_of_gap`) can fail exactly when the
whole remaining chord has been consumed with nothing left over — a legitimate, not vacuous,
terminating state that needs its own trivial (both totals `0`) branch, not a bare hypothesis; (2)
the induction step's `p ≠ R m` side condition (needed to invoke `chord_decomposition_cons`) can
similarly fail when a straddler's near endpoint exactly coincides with the current position — two
tiles' traces genuinely touching at a shared vertex is not excludable by the hypotheses already in
hand. Both are real, checkable geometric edge cases (not proof-technique gaps), and handling them
correctly needs its own short argument each, not a rushed `by_cases` bolted on under time pressure.
Recorded precisely rather than pushed through incompletely, per this project's standing rule against
committing unsound term combinators or `sorry` to force a deadline.

**A real design flaw found and fixed (2026-09-03, later still)**: wiring the pieces above together
surfaced that `gap_free_of_minimal` (and `ChordFinsetStepGap.gap_free_of_finset_step` built on it)
implicitly assumed *no* straddler is yet excluded — its `hmin` hypothesis quantifies over every
straddling tile uniformly, which is only satisfiable on the very first induction step. Once the
recursion has excluded some straddlers, they need `not_mem_gap_of_far_precedes`'s entirely different
argument, not a minimality comparison (an excluded straddler can have an arbitrarily *small*
`dist P (R k)`, since its whole trace sits behind `p`). `ChordFinsetStepCombined.
gap_free_of_finset_step'` is the corrected version, built directly (not via `gap_free_of_minimal`),
casing on whether a tile is the chosen minimal one, another still-remaining `T`-member (minimality
argument), or already excluded (`not_mem_gap_of_far_precedes`, applied with the *current* `r` in
place of the outer `Q` — the lemma never actually needed its bound to be the outermost point).
`lake build Erdos634.All` clean, no `sorry`, `#print axioms` confirms only the standard three.

`ChordFinsetStepGap.gap_free_of_finset_step` (the earlier, first-step-only version) is now
superseded by this one and should not be used in the final assembly.

**The final assembly attempt, and the one piece it's actually missing (2026-09-03, later still)**:
assembled `gap_free_of_all_excluded`, `gap_free_of_finset_step'`, `excl_new_self`/
`excl_carries_forward`, `far_precedes_of_minimal`, and `chord_decomposition_of_trivial_gap` into one
`Finset.strongInduction`. The degenerate branch (`p = R m`, reusing the IH directly) checks out on
paper cleanly. The nondegenerate branch (via `chord_decomposition_cons`) reduces, after combining
with the IH, to one remaining identity neither this session nor any earlier one has built: the
*flush* sum itself splits the same way the raw length does —
`∑ e ∈ lineChain, hausdorff(edge e ∩ segment p Q) = (∑ ... ∩ segment p r) + (∑ ... ∩ segment s Q)`
for the straddler's own `r, s` — because no flush edge (belonging to a *non*-straddling tile) can
touch a point interior to the straddling tile `m`, by interior-disjointness. This is very likely
already true and probably provable from existing `Dissection` API (`tile_subset_target` plus
whatever states disjoint tiles' interiors exclude each other's frontiers), but it has not been
checked or built, and asserting it without checking would be exactly the kind of unverified claim
`/goal` forbids. The attempt file was discarded (not committed) rather than left with a `sorry`.

This is now the *only* missing piece for `chord_decomposition_of_finset`, precisely located: a
flush-sum additivity lemma splitting `∑ e ∈ lineChain, hausdorff(edge e ∩ segment u v)` at any point
known to lie in a straddler's open trace-interior gap. Every other piece — base case, step
gap-freedom (both minimality and exclusion cases), both invariant-maintenance directions, the
degenerate collapse, and the recursive restriction — is built and independently verified.

**The corrected target, found by checking whether the missing piece is actually easy (2026-09-03,
later still)**: checked whether `Dissection.wall_partition` (the machinery underlying
`chord_decomposition_of_gap`) already gives the missing flush-sum split. It cannot: `wall_partition`
itself requires `hwall` — no tile's interior meets the *whole* open range — which is false by
construction across a range containing a straddler. Proving the flush-sum split directly would need
a comparably-sized proof to `wall_partition` itself (a fresh `sum_hausdorff_of_partition` argument
with the range pre-split into three pieces), not a quick corollary.

This means the flat single-sum statement `chord_decomposition_of_finset` was aimed at was the
**wrong target** — a convenience simplification that turned out to need real new machinery. The
correct fix is to avoid it entirely: build the `Finset.strongInduction` to *produce* the point
sequence `g : ℕ → Plane` and `tiles : ℕ → Fin N` that `chord_decomposition_of_chain` already
consumes (existence, by induction, rather than a flat equality) — its own conclusion is stated
gap-by-gap and never needs a flush-sum splitting fact, since `chord_decomposition_cons`'s recursive
structure keeps each gap's flush contribution separate throughout. Every geometric and
order-theoretic piece already built this session (`gap_free_of_finset_step'`, `excl_new_self`/
`excl_carries_forward`, `far_precedes_of_minimal`, `not_mem_gap_of_far_precedes`, the degenerate
collapse) transfers directly to this corrected target unchanged — what needs rebuilding is only the
top-level induction's *conclusion* (an existence statement producing `g`, `tiles`, and a proof they
satisfy `chord_decomposition_of_chain`'s hypotheses) and the final application, not the supporting
lemmas. Attempted under this corrected framing: the base case (`T = ∅`) needs `g 0 = p`, `g 1 = Q`,
`g 0 ≠ g 1` — i.e. `p ≠ Q` — exactly the same degenerate case (`p = Q`, nothing left over) that
`ChordFinsetDegenerate` resolved for the flat-sum formulation, but here it breaks the *sequence*
itself (`g` would need `g 0 = g 1`, violating the distinctness `wbtw_chain_bounded` needs), not
just one summand. It needs its own resolution in this formulation — likely `chord_decomposition_of_
chain` itself tolerating `n` such that the final gap is degenerate, or the existence statement
returning `n = 0` with `g` collapsing to a single point when `p = Q`. Also needs `Fin N` nonempty
(a `tiles : ℕ → Fin N` function must exist even when unused for `n = 0`) as a standing hypothesis —
true for any genuine dissection but not otherwise available. Both are real, small, but unresolved;
a second attempt file was discarded rather than committed with a `sorry` or a hand-waved
`Classical.arbitrary` over a possibly-empty type.

**The actual root cause, traced precisely**: `chord_decomposition_of_chain`'s own `hne` hypothesis
(`∀i, i+1≤2n+1 → g i ≠ g(i+1)`) is *unconditionally* required, including at `i=0` when `n=0` — so it
can never be invoked with `p = Q` (`g 0 = g 1`) regardless of how the wrapper is phrased; this isn't
an artifact of the flat-sum or the existence framing, it's a real limitation of the already-committed
general theorem. The correct fix is at the *use site*, not `chord_decomposition_of_chain` itself:
when `T = ∅`, never call it at all — `chord_decomposition_of_gap` / `chord_decomposition_of_trivial_gap`
already directly handle *both* `p ≠ Q` and `p = Q` without needing any chain machinery (this is
exactly what `gap_free_of_all_excluded` plus `ChordFinsetDegenerate` were built for). Only the
`T` nonempty branch should ever reach for `chord_decomposition_of_chain`, and it should build `g`
by recursing down to a `T = ∅` base case handled the *first* way, not by asking
`chord_decomposition_of_chain` to also cover it. The `Fin N` nonemptiness need disappears entirely
under this fix, since a `tiles` function is only needed once a real straddler exists to place at
index `0`.

**Correction after re-checking**: this is *not* a bug in `chord_decomposition_of_chain` itself. Its
`hne` hypothesis is supplied *once*, for the whole original `n`, by the caller — including
`g (2n) ≠ g (2n+1)`, i.e. "the last straddler's far endpoint ≠ `Q`". The theorem's own internal
recursion never needs to *re-derive* this; it only needs the caller to have been able to supply it
up front. So the real remaining question is squarely a hypothesis-discharge one for the eventual
top-level application: can the last straddler's far endpoint be shown to differ from `Q` in
general? Plausibly yes — `Q` is one of the target's own extreme chord points, while trace endpoints
come from `straddle_trace_isSegment`'s IVT construction on a tile's own vertices, and coincidence
would need an actual dissection vertex to land exactly there — but this has not been checked and is
exactly the kind of claim `/goal` forbids asserting without verification. Recorded as the concrete
next question, not resolved.

**The actual resolution, found by re-reading `chord_decomposition_of_chain`'s own statement**: it
was a self-imposed constraint, not a real one. `chord_decomposition_of_chain` never requires its
final point `g (2n+1)` to literally *be* `Q` — that naming was the wrapper's own choice, not
something the theorem demands. The fix: run the chain over exactly the `n` straddlers, ending at
`g (2n+1) := S (m_last)` (the *last* straddler's own far endpoint, not `Q`) — `g (2n) ≠ g (2n+1)` is
then just `R (m_last) ≠ S (m_last)`, already guaranteed by trace nondegeneracy, no coincidence-with-`Q`
question involved at all. Then add the final leftover bit `[S(m_last), Q]` as one *more* step
*outside* `chord_decomposition_of_chain`, using exactly the already-verified `T = ∅` machinery
(`gap_free_of_all_excluded` when `S(m_last) ≠ Q`, `chord_decomposition_of_trivial_gap` when
`S(m_last) = Q`) — precisely the case split that machinery was already built to handle. This needs
no modification to `chord_decomposition_of_chain`, no new geometric fact, and resolves the
degenerate case in *both* the flat-sum and the existence-of-chain framings identically: the whole
wrapper is `chain's total over the n straddlers` + `one final gap/trivial-gap total`, combined via a
single `hausdorff_segment_split`-style addition at the very end. Not yet implemented.

**`chord_decomposition_of_gap'` / `chord_decomposition_cons'` built (2026-09-03, later still)**:
implementing the fix directly — `ChordDecompositionGapGeneral.chord_decomposition_of_gap'` unifies
`chord_decomposition_of_gap` and `chord_decomposition_of_trivial_gap` into one lemma needing no
`u₁ ≠ u₂` hypothesis at all (the degenerate case contributes `0` automatically), and
`ChordDecompositionConsGeneral.chord_decomposition_cons'` rebuilds `chord_decomposition_cons` on top
of it, needing no `p ≠ r` hypothesis either. Both `lake build Erdos634.All` clean, no `sorry`,
`#print axioms` confirms only the standard three for both.

**But this does not fully resolve `chord_decomposition_of_chain`'s `hne` requirement**: re-reading
its own proof shows `hne` is *also* required directly by `wbtw_chain_bounded` (the betweenness-chain
composition tool from `WbtwChain.lean`), independently of `chord_decomposition_cons`'s own former
need for it — `Wbtw.trans_expand_left`/`_right`, which `wbtw_chain_bounded`'s induction is built
from, fundamentally require consecutive distinctness to compose. So `chord_decomposition_cons'`
removes *one* of the two places degenerate consecutive points caused trouble, but not the other;
fully generalizing `chord_decomposition_of_chain` for arbitrary degenerate coincidences would also
need a degenerate-tolerant variant of `wbtw_chain_bounded` itself — core betweenness-chain
infrastructure, not a small follow-up. This is now the precisely-located remaining obstacle.

**Why it resists a quick fix**: checked whether `wbtw_chain_bounded`'s distinctness requirement
could be dropped by rebuilding it from `wbtw_of_wbtw_wbtw`/`wbtw_middle_of_wbtw_wbtw` (both already
fully degenerate-tolerant, needing no distinctness anywhere in their own proofs). It cannot, cleanly:
those two compose a *fixed* triple of points into another fact about the *same* points, never
advancing which index plays which role, so they cannot substitute for the genuine combinatorial
content `wbtw_chain_bounded` supplies — reaching an arbitrary index `k` from a chain of only
*consecutive* facts, which is what actually needs `Wbtw.trans_expand_left`/`_right`'s own
distinctness side-condition to advance the "middle" role from one index to the next. This looks like
a real structural fact, not a proof-search gap: indexing an ordered chain by raw `ℕ` position and
asking for full pairwise `Wbtw` from only consecutive data seems to inherently need consecutive
points distinct, unless the sequence is first de-duplicated (a genuinely different, coarser
indexing, not a small patch to `WbtwChain.lean`). Recorded as a real mathematical obstacle to the
fully general (arbitrary-coincidence-tolerant) form of `chord_decomposition_of_chain`, not merely an
unfinished proof.

**The practical resolution: `hinj` doesn't need to be derived at all.** `chord_decomposition_of_chain`
already takes `hinj` directly from its caller — it is never derived internally from weaker data. So
the obstacle above only means "the general infrastructure can't derive distinctness from consecutive
facts alone," not that the wrapper is stuck: a standard "general position" nondegeneracy hypothesis
on the straddler trace-endpoint data (every two distinct trace endpoints, across all remaining
straddlers and the current position, are literally different points) supplies `hinj` directly, no
derivation needed. This is ordinary mathematical practice (many general theorems carry such a
hypothesis) and not a gap.

**`ChordFinsetPrependInj.injective_prepend_two` built (2026-09-03, later still)**: the one genuinely
reusable mechanical piece this resolution needs — prepending two new points `p, r` (distinct from
each other and from every point already in a bounded injective sequence) to that sequence keeps the
whole extended sequence injective. Pure index bookkeeping (no geometry, no `Classical.choice` even),
verified via explicit case analysis on which of the four index regions (`0`, `1`, shifted-old vs
shifted-old) a given pair falls into. `lake build Erdos634.All` clean, no `sorry`, `#print axioms`
confirms only `[propext, Quot.sound]` (no choice needed at all).

This is the key step of the induction's injectivity discharge, isolated and verified standalone
(mirroring the "verify in small pieces" fix from the earlier failed full-assembly attempt). Wiring
it into the full `exists_chain_of_finset` induction — threading the nondegeneracy hypothesis through
each step, deriving each step's "new point distinct from all remaining" facts from the pairwise
assumption, and combining with `chord_decomposition_cons'`/`gap_free_of_finset_step'`/the invariant
lemmas already built — is the next concrete task; a first attempt at writing the full statement was
sized correctly but its proof was not completed this pass.

**Correcting an error in that first attempt's design**: it tried to end the chain at the *last*
straddler's own far endpoint `S(m_last)` instead of `Q`, to dodge the question of whether
`S(m_last)` could coincide with `Q`. Re-checking `chord_decomposition_of_chain`'s actual indexing
shows this doesn't typecheck: for `n` straddlers, the `n`-th trace occupies `g(2n-1), g(2n)`, and
`g(2n+1)` is a *separate*, required trailing point with its own `hne` obligation
(`g(2n) ≠ g(2n+1)`) — setting `g(2n+1) := S(m_last) = g(2n)` violates that directly, it does not
sidestep it. The actually-correct fix is simpler and needs no special-casing of the last straddler
at all: keep `g(2n+1) := Q` throughout, and fold "no trace endpoint coincides with `P` or `Q`" into
the *same* general-position nondegeneracy hypothesis already being assumed for every other pair.
Since `chord_decomposition_of_chain` takes `hinj` (hence `hne`) directly from the caller regardless
of how it's discharged, this closes the question with no changes to `chord_decomposition_of_chain`,
`chord_decomposition_cons`, or `chord_decomposition_of_gap` needed — `chord_decomposition_cons'`/
`chord_decomposition_of_gap'` turn out not to be required for this particular fix either (they
remain useful in their own right, for the *leading*-gap and `T = ∅` cases, which are genuinely
different situations). The plan in `exists_chain_of_finset`'s statement above should use `Q` as
written, with the nondegeneracy hypothesis list extended by `∀ k, straddles k → P ≠ R k ∧ P ≠ S k ∧
Q ≠ R k ∧ Q ≠ S k`.

**`ChordFinsetChainInj.exists_injective_chain` built (2026-09-03, later still)**: the pure
combinatorial fact `exists_chain_of_finset` needs beyond `injective_prepend_two` itself: given a
`List` of point-pairs (each internally nondegenerate, pairwise cross-distinct, and distinct from a
fixed bound point), the sequence built by concatenating `bound :: pair₁.1 :: pair₁.2 :: pair₂.1 ::
⋯` is injective on its own range — by induction on the list, applying `injective_prepend_two` once
per element. Generalized `injective_prepend_two` itself along the way: its bound was hardcoded to
the `2m+1` shape `chord_decomposition_of_chain` uses, which didn't match this lemma's own natural
`2·length` convention (no trailing point); it now takes an arbitrary bound `B` (with conclusion
bound `B + 2`), matching either convention. `lake build Erdos634.All` clean, no `sorry`,
`#print axioms` confirms only the standard three (`exists_injective_chain`) / `[propext,
Quot.sound]` (the still-choice-free `injective_prepend_two`).

With this, the *entire* combinatorial core of `exists_chain_of_finset` is done: given the straddler
data as a `List` (sorted, via `wbtw_trichotomy_of_wbtw`/`Finset.sort`/`List.insertionSort` — not yet
built) satisfying the nondegeneracy hypotheses, `exists_injective_chain` produces the injective `g`
directly. What remains is: (1) actually sorting the `Finset` into such a `List` (order-theoretic
`Finset`/`List` API work, not geometry), and (2) proving that `List`'s consecutive elements satisfy
`chord_decomposition_of_chain`'s `hchain` (`Wbtw` between consecutive triples) and `hgap`
(gap-freedom) — exactly what `gap_free_of_finset_step'` / `far_precedes_of_minimal` /
`excl_new_self` / `excl_carries_forward` already supply per-step, needing only to be threaded
through the same `List` induction `exists_injective_chain` already demonstrates the shape of.

**Checked how much of that threading is actually direct**: `gap_free_of_finset_step'` and
`far_precedes_of_minimal` are stated in terms of a `Finset (Fin N)` (the *remaining* straddler set
`T`, used for `hmin`/`hexcl`'s own quantifiers), not a `List` — restating the induction over a
`List` (as `exists_injective_chain` does, for good reason: `List.get`/index access is what
`chord_decomposition_of_chain` itself consumes) means every per-step call to those two lemmas needs
`T := (the tail of the list, as a Finset)`, and the membership/exclusion facts translated between
"in the list's tail" and "in that Finset" at each step. **Checked, and it's smaller than that paragraph feared**: neither
`gap_free_of_finset_step'` nor `far_precedes_of_minimal` ever uses any `Finset`-specific API
(`Finset.sum`, `.card`, etc.) — `T : Finset (Fin N)` is used *only* via plain membership (`k ∈ T`,
`k ∉ T`), which `List.toFinset` (`Fin N` has `DecidableEq`) plus the one-line simp lemma
`List.mem_toFinset` (`a ∈ l.toFinset ↔ a ∈ l`) bridges directly — inserting `.toFinset` at each call
site and rewriting membership through that lemma, not a genuine reconciliation of two different
notions of "remaining." Retracting the previous entry's caution; this is a small, mechanical
plug-in after all. Not yet written.

**One more check before implementing, and a broader finding**: `chord_decomposition_of_chain`'s
`hne` hypothesis is required *unconditionally*, for every consecutive pair from `i = 0` to
`i = 2n`, supplied by the caller — the theorem does not internally tolerate or skip a degenerate
consecutive pair anywhere, not just at the trailing end. So the "end at `S(m_last)`, not `Q`" fix
above resolves the *trailing* degeneracy, but the *same* question recurs at every interior boundary:
could a straddler's own near endpoint coincide with the previous straddler's far endpoint (`p = r`
mid-recursion, the second degenerate case flagged earlier), or could two straddlers even share a
trace endpoint outright? `ChordFinsetDegenerate` and the "skip the leading gap" branch sketched in
the discarded assembly attempt show *how* to handle a single such collapse when it's known to occur,
but `chord_decomposition_of_chain` itself has no built-in tolerance for it — the wrapper would need
to either rule out every such coincidence in general (a genuine geometric question, not yet checked)
or dynamically merge/skip degenerate points while constructing `g`, which changes the induction's
bookkeeping non-trivially. This is a real, larger piece of remaining work than the single trailing
case alone, and is not resolved by the fix above — it only closes the one instance of it that this
session's investigation happened to focus on first.

**Still not built**: sorting a `Finset` straddler set into the chain `chord_decomposition_of_chain`
now consumes
(order their trace endpoints by `dist p ·`, identify consecutive gaps, apply
`chord_decomposition_of_gap` to each, sum against `straddle_total_eq_sum` via repeated
`hausdorff_segment_split`) — the one-straddler case above is the concrete instance it generalizes.
Every individual geometric and measure-theoretic fact the *full* assembly could need now exists and
is proved; what remains is genuine finite combinatorial bookkeeping (a `Finset.sort`-style
induction), no new geometry left to discover anywhere in this chain. Deprioritized further
construction this session in favor of hunting further PROVED→VERIFIED flips per the standing
`/goal`, since this piece, even finished, is infrastructure toward `prop:chorddecomp` and not
itself a flip.

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

## `thm:ladder` obligations after 2026-09-02 (late) — SUPERSEDED, stale as of 2026-09-09

This sub-table described an intermediate, incomplete state (C4/C5 still open). It is now stale:
the main `thm:ladder` row (see "`M thm:ladder` | `kT` is cut into `k²N` copies" above, dated
**VERIFIED 2026-09-02**) records that `Subdivision.ladderDissection`'s `cellIdx` closed the C5
indexing gap and `volume_cellOf` closed C4, later the same day — this leftover table was never
deleted after the flip. Left here, struck through, only so a future session doesn't re-read it as
a live obligation list; the authoritative status is the VERIFIED row above.


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
44 (resp. 99, 63, 22) triangles as real objects. **Update 2026-09-02: this is done for Tiling44,
CevianTiling63 and Tiling99** — see `Tiling44Bridge.lean`/`CevianTiling63Bridge.lean`/
`Tiling99Bridge.lean`, each a `dissection : CongruentDissection N`. The `checkPairs`/`wit`
recursion turned out unnecessary to unpack directly: `decide`-ing the *existence* of a working
separating edge among 6 candidates per pair (rather than extracting the certificate's own witness)
was far cheaper (12s/25s/68s at 946/1953/4851 pairs respectively) and needed no per-pair data
entry at all. `thm:44` and `thm:63` are VERIFIED; `cor:elevenm`'s positive half and its `N=11m²`
consequence are done (`ElevenMBridge.lean`).

## Scoping note: the negative certified-search format (2026-09-02)

`thm:frontier`–`thm:frontier4`, `thm:eq105`, and `cor:elevenm`'s `1 ∉ S` clause all cite an engine
verdict of the shape `EXHAUSTED_NO_TILING` — a claim that an exhaustive backtracking search over
*all* candidate dissections found none. Scoped what this would take to formalize, precisely:

`code/engine/cengine.cpp` (~790 lines) implements the search as a depth-first backtracking
procedure (`dfs`) over exact-rational polygon state (`QD`, GMP `mpz_class`), with polygon surgery
(`subtract`: cut a placed tile out of the remaining region), a containment predicate
(`containment_ok`), and several pruning heuristics (`pruneA`, `pruneR`, `pruneP4` — area,
rotational-symmetry and minimum-angle pruning) that cut the search space without changing its
result. `EXHAUSTED_NO_TILING` means the DFS exhausted every branch without `has_found` ever
becoming true.

**This is not reachable by a small lemma or a `decide` call.** Certifying it in Lean needs one of:
1. **Re-implement the search in Lean** and prove the reimplementation matches the engine's result
   *and* prove the pruning heuristics are sound (don't discard a branch that could contain a
   tiling) — a from-scratch verified-backtracking-search project, realistically months, not a
   "modest task".
2. **Redesign the engine to emit a checkable certificate** of the search itself — e.g. a compact
   trace or a summary invariant strong enough that a much cheaper Lean-side check (ideally
   `decide`/`native_decide`) can confirm no tiling exists without replaying the whole search. No
   such trace format exists today; designing one is itself a nontrivial verification-engineering
   problem (what invariant is both cheap to check and sound?), separate from anything built this
   session.

Neither is a natural extension of the positive-witness `CertBridge`/`Tiling*Bridge` machinery
built 2026-09-02 — that machinery consumes a single witness object and checks it; a nonexistence
claim has no witness to consume. **Recorded here as a precise, permanent blocker**: do not
re-scope this from scratch in a future session assuming it might be a quick lemma. If it is ever
attempted, option 2 (redesign the engine to emit a certificate) is the more promising route, since
option 1 duplicates ~790 lines of exact-arithmetic geometry code inside Lean's kernel, which is a
much larger undertaking than anything else in this corpus.

## Two untracked CONJECTURE rows, added 2026-09-09

Found while scanning for a reachable target after the `lem:ccornerside`/Tiling44 correction: these
two rows were not previously listed in this map at all (a gap in the debt tracking itself, not a
missing proof).

| Paper | Statement | Evidence | Status |
|---|---|---|---|
| C `cor:wfamily` (erdos-634.tex) | The cevian spectrum at `(1,2)` is complete: `N=7m²` realized for every `m≥2`, no other `m` | `CevianTiling28`/`CevianTiling63` (VERIFIED, the two certified seeds), `code/engine/gen_cevian.py` exhaustions (14 at 678 nodes, 46 at 4,685, 56 at 4,890,763, 62 at 12,872,188 nodes) | **CORRECTED, 2026-09-09, same session**: the "no composition layer" claim below was checked against the corpus and is **wrong** — `UnionDissection.unionDissection`/`.unionCongruentDissection` (pre-existing, 2026-09-04) already glue two `CongruentDissection`s of disjoint-interior targets into one, exactly the primitive W-addition needs. The real remaining gap is narrower: a genuine `CongruentDissection` of the specific W-connecting-parallelogram at scale `m₁×m₂` (a new geometric realization, comparable effort to `PgramTiling22Bridge` but a different concrete shape — not yet built, not yet scoped in detail), plus (unavoidably) the certified `N=11` exhaustion for the `m=1` case (the standing certified-search-format blocker). Blocked on one narrow, real construction gap plus one standing blocker — not two fundamental missing primitives. |
| C `thm:wfamily` (erdos-634-companion.tex) | W-addition: `S_W` closed under addition; `W_m` tileable iff `m≠1` | `Primitives.w_slab_counts`/`.w_counts` (VERIFIED, but trivial `ring` identities — no geometric content), `UnionDissection.unionCongruentDissection` (general gluing, now identified as the right tool), same certified exhaustions as `cor:wfamily` | **Same corrected status as `cor:wfamily`**: `unionCongruentDissection` supplies the addition step generically; what's missing is the concrete W-bridge parallelogram's own `CongruentDissection` (its interfaces being full straight segments is itself part of what a real construction must show, not assumed) plus the `m=1` certified exhaustion. `w_slab_counts` only checks the slab's arithmetic census (`2f²−1 = f·a+b`), not the geometric assembly. |

Neither is flippable yet, but the blocker is now precisely scoped: build a `CongruentDissection`
of the W-connecting-parallelogram (reusing `PgramTiling22Bridge`'s certificate-bridge pattern for a
new concrete shape), not a new composition primitive — that part already exists. No label change
this iteration; this is a real re-scoping, not a proof.

## ChordEndpointFrontierGeneral, session of 2026-09-03 continued

**`ChordEndpointFrontierGeneral.chord_endpoint_not_interior'` built**: attempting the base case of
the geometric threading (`exists_geometric_chain`, `L = []`) surfaced a missing fact: a straddler's
own trace endpoint is never interior to *that tile itself* — needed to rule out the current
position `p` (always `P` or a previous straddler's far endpoint) from being interior to the very
last straddler placed. `ChordEndpointFrontier.chord_endpoint_not_interior` already proves exactly
this shape of fact, but only for `D.target` specifically; checking its proof shows it never uses
anything about `D.target` beyond the carrier and the chord identity, so it generalizes verbatim to
*any* `Tri` (in particular, `D.tile k`). `lake build Erdos634.All` clean, no `sorry`, `#print axioms`
confirms only the standard three.

A first attempt at writing `exists_geometric_chain` itself (mirroring `exists_injective_chain`'s
proven structure, adding the `Wbtw`/gap-freedom payload) produced unsound tactic combinations under
time pressure in its base case and was discarded rather than committed with a `sorry` — the same
failure mode as the very first full-assembly attempt earlier in this file, now recurring at smaller
scale. `chord_endpoint_not_interior'` is the one genuinely reusable fact that attempt surfaced;
`exists_geometric_chain` itself remains unwritten.

## ChordFinsetGeometricChainBase, session of 2026-09-03 continued

**`not_interior_of_all_excluded` built** — the actual base case of `exists_geometric_chain` (`L =
[]`), completed this time (small, self-contained, verified on the first attempt after
`chord_endpoint_not_interior'` supplied the missing fact): if every straddling tile's far endpoint
weakly precedes the current position `bound`, no tile's interior meets `bound` itself. If some tile
`k`'s interior did contain `bound`, `bound` would lie in `k`'s own trace (a local betweenness fact),
placing it — via `wbtw_global_of_local` — weakly between `P` and `k`'s far endpoint `S k`; combined
with the exclusion bound (`S k` weakly precedes `bound`) via `wbtw_antisymm_of_wbtw`, this forces
`S k = bound` exactly. But `chord_endpoint_not_interior'` already rules out `S k` (a trace's own
extreme point) from being interior to its own tile — contradiction. `lake build Erdos634.All`
clean, no `sorry`, `#print axioms` confirms only the standard three.

This, together with `chord_decomposition_of_gap'`/`chord_decomposition_of_trivial_gap`, fully
closes the base case of `exists_geometric_chain`. What remains is the `cons` (successor) case,
mirroring `exists_injective_chain`'s own successor case but threading the `Wbtw`/gap-freedom
payload via `gap_free_of_finset_step'` (bridged to the list's tail through `List.toFinset`) and
`far_precedes_of_minimal`/`excl_new_self`/`excl_carries_forward` for the invariant's continuation.

## exists_geometric_chain's cons case, session of 2026-09-03 continued

Attempted the successor case directly. It needs `L.Nodup` as an additional hypothesis (not
previously listed) — `far_precedes_of_minimal` needs `m ≠ k` for `k` in the tail `L'`, which only
follows from `m ∉ L'`, itself only guaranteed if the list has no duplicate straddler indices.
Reasonable (a straddler is placed once), but must be threaded through the whole induction
(preserved into the recursive call on `L'` via `List.nodup_cons`), not assumed silently.

Separately, `far_precedes_of_minimal`'s own hypotheses (`hr, hs, hrk, hsk : Wbtw P · Q`) need the
outer chord endpoint `Q`, not `bound` — requiring the same `hglobalWQ`/`hglobalSQ` helper functions
(`Wbtw P (R k) Q` / `Wbtw P (S k) Q` for every straddling `k`, via `wbtw_of_mem_tile_trace`) built
inline in the discarded full-assembly attempts earlier in this file. These are small, mechanical,
and already known to work (verified in isolation there) — the remaining task is assembling them
correctly inside this induction, not discovering new content. A second attempt at writing the
successor case was discarded (unsound tactic combinators under time pressure) rather than
committed with a `sorry`, per this project's standing rule.

**Precise remaining task**: add `L.Nodup` to `exists_geometric_chain`'s hypothesis list; inline the
`hglobalWQ`/`hglobalSQ` helpers; derive `m ∉ L'` from `List.nodup_cons`; call
`far_precedes_of_minimal` with `Q` (not `bound`) as the outer bound to get `hle'` for the recursive
call; call `gap_free_of_finset_step'` (bridging its `Finset` parameter via `L'.toFinset` and
`List.mem_toFinset`) for the leading gap; combine with the recursive `ih` call exactly as
`exists_injective_chain`'s own successor case does for injectivity, in parallel.

## exists_geometric_chain's successor case, precisely mapped (2026-09-03, later still)

Wrote the full setup for the successor case and verified it compiles (all of: extracting `m`'s
trace, `hle'` via `far_precedes_of_minimal` using the sortedness hypothesis at index `0` vs `j+1`,
`hexcl'` via `excl_new_self`/`excl_carries_forward`, `hsorted'` by reindexing, and the recursive
`ih` call itself) — the *only* missing hypothesis, `L.Nodup` (needed for `far_precedes_of_minimal`'s
`m ≠ k`), is now added and threaded correctly via `List.nodup_cons`.

What remains is exactly the final combination step, and it is now precisely specified: define
`g := fun i => if i = 0 then bound else if i = 1 then R m else g' (i - 2)` (mirroring
`exists_injective_chain`'s own construction) and discharge `hchain`/`hpts`/`hmtrace`/`hgap` for it.
The one new fact needed beyond what `ChordDecompositionChain.lean`'s own index-shift lemmas already
demonstrate the shape of: a "reach" lemma `∀ i, i ≤ 2 * L'.length + 1 → Wbtw ℝ P (S m) (g' i)`,
proved by cases on `i` (`i = 0`: trivial, `g' 0 = S m`; `i = 2j+1`: `hle'` applied to `L'.get j` via
`hg'match`; `i = 2j+2`: `hle'` at `L'.get j` composed with that element's own `Wbtw (R ·) (S ·)`
via `wbtw_of_wbtw_wbtw`). With that reach lemma in hand, `hchain` at `i = 1` follows from
`wbtw_middle_of_wbtw_wbtw hgom (reach 1)`, and `hchain` at `i ≥ 2` follows from `hg'chain` shifted
by 2 exactly as in `ChordDecompositionChain.lean`'s own succ case. `hpts`/`hmtrace`/`hgap` follow the
same shift pattern already proven there, index-for-index. This is genuine remaining work (roughly
comparable in size to what's already written for this successor case) but no new mathematical
content — every fact it needs is already an established lemma; it is pure assembly.

## ChordFinsetReachLemma, session of 2026-09-03 continued

**`reach_of_le_all` built** — the one new fact identified above as missing for
`exists_geometric_chain`'s final assembly, now proved and verified standalone: given `g'`'s own
shape (matching `L'`'s near/far endpoints) and that `bound'` weakly precedes every element's near
endpoint, `bound'` weakly precedes every point of `g'`'s range up to `2 * L'.length` (not `2 *
L'.length + 1` — that extra trailing index is `g'`'s own outer bound, not covered by any list
element's near/far point, and correctly excluded rather than forced through). Proved by cases on
the index's parity, reaching the far endpoint from the near one via `wbtw_of_wbtw_wbtw` when needed.
`lake build Erdos634.All` clean, no `sorry`, `#print axioms` confirms only the standard three.

With this, every individual fact `exists_geometric_chain`'s successor case needs is now built and
independently verified. What remains is exactly the mechanical combination step described above
(defining `g`, applying `wbtw_middle_of_wbtw_wbtw hgom (reach_of_le_all ... 1)` for the `hchain` case
at `i = 1`, and the same index-shift pattern `ChordDecompositionChain.lean` already demonstrates for
everything else) — no further lemma is missing.

## Full-assembly attempt of exists_geometric_chain, session of 2026-09-03 continued

Attempted the complete theorem, reusing every piece now built. Two hypotheses were found genuinely
missing during the attempt and are worth recording precisely: (1) `bound ≠ R k` for every `k ∈ L`
(needed by `gap_free_of_finset_step'`'s own `hpr`, which is not degeneracy-tolerant the way
`chord_decomposition_cons'`/`chord_decomposition_of_gap'` are); (2) full pairwise point-distinctness
across the list (`R k ≠ R l ∧ R k ≠ S l ∧ S k ≠ R l ∧ S k ≠ S l` for `k ≠ l` in `L`) rather than just
the segment-disjointness `Pairwise` already present — needed to get `S m ≠ R k` for the recursive
call's own `bound ≠ R k` obligation. Both are natural "general position" assumptions, added directly
to the theorem statement (matching the project's established pattern for such facts) — this part of
the attempt is settled, not open.

The final combination step itself (constructing `g`, discharging `hchain`/`hpts`/`hmtrace`/`hgap` by
index-shift case analysis) produced several genuine but small index-arithmetic mismatches — nested
`match i, hi with | 0, _ | (n+1), hi` patterns combined with an inner `by_cases hn0 : n = 0` do not
automatically simplify `2 * (n' + 1 + 1)`-shaped terms to match the `ring`-derived rewrite targets,
requiring the case structure to be flattened (e.g. a single `match i with | 0 | 1 | (n+2)` rather
than nesting), which was not completed this pass. `reach_of_le_all` was also invoked with the wrong
argument (`hg'mtrace` needs to be adapted to match `hg'match`'s exact stated shape, not passed
directly) — a naming/shape mismatch, not a mathematical one. The attempt file was discarded rather
than committed with a `sorry`, per this project's standing rule.

**Precise remaining task**: redo the final combination with the two hypotheses above added, using a
flat (non-nested) `match i with | 0 | 1 | (n+2)` case split for each of `hchain`/`hpts`/`hmtrace`/
`hgap`, mirroring `ChordDecompositionChain.lean`'s own (already-proven) index-shift style exactly
rather than the more compact nested form attempted here. No further lemma is missing; this is
finishing a mechanical case-by-case rewrite that this attempt got most, but not all, of the way
through.

## Second full-assembly attempt, session of 2026-09-03 continued -- a real design gap found

Rewrote with a flat (non-nested) case split as specified above. It surfaced a genuine design gap
in `exists_geometric_chain`'s own statement, not an arithmetic slip: its `hmtrace` conclusion
asserts `(D.tile (L.get i)).carrier ∩ line = segment ℝ (g (2i+1)) (g (2i+2))` — segment *equality*
only. `reach_of_le_all` needs the *specific point identity* `g' (2i+1) = R (...) ∧ g' (2i+2) = S
(...)`, which segment equality does not give (two point-pairs can define the same segment without
being the same pair — swapped orientation is not excluded by the set equality alone). The fix is to
state `exists_geometric_chain`'s `hmtrace` conclusion as the stronger point-identity form directly
(which trivially implies the segment form the caller, `chord_decomposition_of_chain`, actually
needs) — not a new mathematical fact, but a genuine restatement needed before the proof can close.

Remaining smaller issues from this attempt, for completeness: two missing hypotheses in the `nil`
case's `intro` line (undercounted after adding `hbne`/`hptdist` to the signature); a doubled
`List.mem_cons_of_mem m h` application; `hglobal`'s 3-way tuple destructured inconsistently in one
spot; and a couple of `rw` calls needing `show`/`change` instead, since rewriting under a dependent
`⟨_a, h⟩` `Fin` index is not motive-correct the way a direct `rw` expects. All are small and
mechanical once the `hmtrace` shape is fixed first — none reopen new mathematical content.

Two attempts at the full assembly now agree on every piece except this one structural point. The
attempt was discarded rather than committed with a `sorry`, per this project's standing rule.
Restating `hmtrace` as the point-identity form is the concrete next step, before re-attempting the
same flat-case-split proof.

## exists_geometric_chain: COMPLETE, session of 2026-09-03 continued

**`ChordFinsetGeometricChain.exists_geometric_chain` built and fully verified.** Third attempt at
the full assembly, after two design gaps found and fixed:

1. `gap_free_of_finset_step'`'s own `T` parameter must include `m` itself (`(m :: L').toFinset`, not
   `L'.toFinset`) — its `hexcl` hypothesis is universally quantified over *all* `k ∉ T`, and if `T`
   excludes `m`, the type checker demands a proof of `Wbtw P (S m) bound` (generally false — `S m`
   comes *after* `bound`, not before) even though the theorem's own proof never actually invokes
   `hexcl` at `k = m` internally. Fixed by including `m` in `T` (with `hmin` at `k = m` trivial via
   `le_refl`), matching how `T` conceptually means "every candidate for minimality," `m` included.
2. `hmtrace`'s conclusion needed restating as the specific point identity
   (`g (2i+1) = R (L.get i) ∧ g (2i+2) = S (L.get i)`), not just segment equality — the weaker form
   doesn't pin down orientation, which `reach_of_le_all` needs directly.
3. `hchain`'s domain needed narrowing to `i + 2 ≤ 2 * L.length` (dropping chain's own `+1`): the
   trailing index `2 * L.length + 1` is not determined by the recursion on `L` at all (it's `Q`,
   supplied by whichever future top-level wrapper appends the final `[S(last), Q]` segment
   separately, exactly as the "corrected plan" entry above already specifies) — trying to prove
   anything about it here was asking for a fact with no content to prove it from.

Every one of the ~15 remaining small mechanical issues (index arithmetic, `List.get` reduction,
tuple-shape mismatches between `hglobal`'s 3-way and `gap_free_of_finset_step'`'s 2-way) was fixed
by finding the actual root cause rather than patching symptoms. `lake build Erdos634.All` clean, no
`sorry`, `#print axioms` confirms only the standard three.

**What this closes**: the entire `Finset`/`List`-sort combinatorial core for the general straddler
induction. Given a `List` of straddler indices in sorted order (nearest-to-`bound` first — assumed
directly, matching `chord_decomposition_of_chain`'s own established pattern for `hinj`) satisfying
the natural nondegeneracy/general-position hypotheses, `exists_geometric_chain` produces the point
sequence with the exact properties needed to feed `chord_decomposition_of_chain` (up to the trailing
segment, appended separately). What remains for the *complete* `prop:chorddecomp` skeleton is: (1)
actually sorting a `Finset` straddler set into such a `List` (pure order-theoretic `Finset`/`List`
API work — `wbtw_trichotomy_of_wbtw`/`wbtw_iff_dist_le_of_wbtw` already supply the order,
`Finset.sort`/`List.insertionSort` do the rest), and (2) the small top-level wrapper appending the
final `[S(last), Q]` segment via `chord_decomposition_of_gap'`. Neither needs any further geometric
fact — every one is already built and verified in this corpus.

## FinsetSortedList, session of 2026-09-03 continued

**`exists_sorted_list_of_finset` built** — the "sorting a `Finset` straddler set into a `List`"
task flagged above as the last remaining bookkeeping piece, now done for the general (key-based)
case: any `Finset (Fin N)` can be sorted into a `List` (matching it as a set via `toFinset`, `Nodup`,
same `length`) non-decreasing in an arbitrary real-valued key. Proved by strong induction on the
`Finset`, extracting the minimal remaining element via `Finset.exists_min_image` and prepending —
pure order-theoretic bookkeeping, no geometry, exactly as anticipated. `lake build Erdos634.All`
clean, no `sorry`, `#print axioms` confirms only the standard three.

Instantiating this with `key := fun k => dist P (R k)` and combining with `exists_geometric_chain`
(supplying its own `hle`/`hsorted`/`hbne`/etc. hypotheses from the sort's own guarantees plus the
straddler set's own general-position facts) is the remaining top-level wiring — the very last piece
before a complete, fully general `prop:chorddecomp` skeleton (still needing the flush total and the
member-specific `(3,7)` numerics on top, as always noted). Not yet done, but every fact either side
needs is now built and independently verified.

## ChordFinsetWrapper, session of 2026-09-03 continued

**`exists_geometric_chain_of_finset` built** — the top-level wiring identified as the last piece:
instantiates `exists_sorted_list_of_finset` with `key := fun k => dist P (R k)` on a straddler
`Finset T`, then feeds the resulting sorted `List` into `exists_geometric_chain`. Discharges
`exists_geometric_chain`'s `hle`/`hbne`/`hsorted`/`hpairwise`/`hptdist`/`hexcl` hypotheses from the
sort's own guarantees plus `T`'s general-position hypotheses (`hle`, `hbne`, `hcross`, `hptcross`,
`hexcl`, all stated directly over `T` rather than a `List`). The `hsorted` case needed
`wbtw_near_endpoint_to_Q` (already built) plus `WbtwDistCoord.wbtw_iff_dist_le_of_wbtw` to convert
the sort's `dist`-order into the required `Wbtw`-order — both already-verified facts, no new
geometric content. The tile-trace conjunct is stated as `∀ i < T.card, ∃ t, ...` rather than a total
`ℕ → Fin N` function, since a total default value doesn't exist when `N = 0` — this is bookkeeping,
not a strength loss for `prop:chorddecomp`'s own use.

This closes the general N-straddler combinatorial core end to end: given a straddler `Finset` and
its own general-position facts, the point sequence `g`, its gap-freedom, its interior-exclusion, and
its match to each straddler's own trace, all fall out. `lake build Erdos634.All` clean, no `sorry`,
`#print axioms` confirms only the standard three.

**What is still missing for `prop:chorddecomp` itself** (unchanged from every prior entry): appending
the final `[S(last), Q]` trailing segment to bridge to the full chord `[P,Q]`; the flush total; the
member-specific `(3,7)` numerics. None of those are started. This file is infrastructure — it does
not move any paper statement's label.

## rem:route1uniform, session of 2026-09-03 continued (prime-case pivot)

**Found already machine-checked, never recorded.** `Frontier.route1_spacings` and
`.side_tile_third_vertex` (both pre-existing, axiom-clean, no `sorry`) together are exactly
`rem:route1uniform`'s stated content: `side_tile_third_vertex` fixes `V`'s position as the second
side tile's third vertex (`|V-B|=b`, given the tile's own cosine identity and `cb²+sb²=1`); the
companion `|V-A|=c` is definitional (`V-A` is horizontal of length `c`). `route1_spacings` gives the
five spacings the remark names: consecutive gaps `a, c-a, a` along `A,R₁,V,E` and `|AV|=|R₁E|=c` —
in particular `E_x - V_x = f` (the remark's headline: the chord's endpoint overshoots the blocking
edge by exactly one `a`-length, identically in `f`, with no threshold in `f` where it stops). Adding
`| C \`rem:route1uniform\` | Route 1 escapes by exactly \`a\`, uniformly in \`f\` |
\`Frontier.route1_spacings\`, \`.side_tile_third_vertex\` | VERIFIED |` to the table (previously
absent — this remark had no row at all).

**What this does NOT touch**: the remark's own forward-looking sentence — "What route 1 needs is
therefore a statement about what covers `[V,E]`... We do not prove that here" — names exactly the
open content that `conj:advance`'s own text and `rem:routeoneopen` (OPEN) already carry: (a) that a
through-edge, not a junction, runs below the line at `V` (the `iπ`/`hiπ` witness `RouteOne.
alpha_wall_figure_real` still takes as a hypothesis, not derived), and (b) that the exactly-filled
wedge's last flank lies along the line. Neither is touched by this entry. I looked for a way to
derive (a) from the already-built chord-decomposition machinery (`ChordTraceReal.*`): the natural
guess — that `V` is interior to some *other* tile's straddling chord `[R₁,E]` on this same line,
giving the straight angle from that tile — is **wrong**: `R₁` is a wall-junction point from a
different (`(1,3)`-style) chord construction, not the endpoint of a straddling tile's trace through
`E`, so no chord-interior argument places `V` there. This is a real, checked negative finding, not a
proof; the paper's own "we do not prove that here" stands, and no shortcut through the recently-built
chord machinery closes it. `GOAL_PRIMES.md`'s target 1 (cases (a)/(b)/(c)) remains fully open.

This is genuine formalization-debt progress (a remark flips PROVED-by-prose → VERIFIED) but is
**not** progress on the `/goal`: neither outcome (full proof, prime case) moved, and the crossing
question that blocks `conj:advance` is exactly as far away as before.

## RouteOneThroughEdge, session of 2026-09-03 (prime-case pivot, second pass)

**A real narrowing of `conj:advance`'s open case (a).** New file `Erdos634/RouteOneThroughEdge.lean`,
seven theorems, `lake build Erdos634.All` clean, all axiom-clean, no `sorry`.

**Where case (a) actually enters.** `route_one_flank_composed` takes `hcard` (the `π`-count at `V` is
one) and `hb` (the tile below the line carries the straight angle) — jointly, `conj:advance`'s
unproved "a through-edge, rather than a junction, runs below the line at `V`". Tracing the proof,
those two are consumed at exactly one place: `not_straight_of_unique`, to give `hnepi`, which
excludes `localAngle (serving tile) V = π` so that `serving_has_vertex` can conclude `V` is a vertex.
Nothing else in the chain uses them. (`serving_ne_two_pi`, by contrast, needs only that *some* other
tile's carrier contains `V` — not that it carries a straight angle. So the below tile's *existence*
is cheap; only its straight angle is the open fact.)

**The `π` branch does not need excluding — it is pinned.** `through_edge_lays_rightward`: if `V` is
not a vertex of `T`, `T.localAngle V = π`, and every point of `T` is weakly above `V` (`habove`,
already a hypothesis of `route_one_flank_composed`), then `T` contains a point strictly to the right
of `V` at exactly `V`'s height. Proof: `coords_of_localAngle_pi` puts one barycentric coordinate at
`0` and the other two strictly positive; `sub_vertex_eq_combo` at each of the two flanking vertices
writes the displacements to them as *opposite* positive multiples of a single vector `w`; `habove`
makes both second components `≥ 0`, and antiparallel forces `w` horizontal; `w ≠ 0` since otherwise
`V` is a vertex. Then `serving_lays_rightward` combines this with `escape_flank` for the vertex
branch: **with only `localAngle ≠ 0` and `localAngle ≠ 2π` — both already discharged independently
(`serving_ne_zero`, `serving_ne_two_pi`) — the serving tile lays a horizontal rightward segment at
`V`. No `π`-count, no below tile, no straight angle.**

**Non-vacuity, machine-checked** (the standing rule): `midpoint_localAngle_pi` proves that the
midpoint of *any* edge of *any* triangle has local angle `π` (with `coord_midpoint`,
`coord_midpoint_edge`, `midpoint_not_vertex` — reusable on their own); `through_edge_hyps_satisfiable`
shows the three hypotheses follow from two elementary sign conditions on the vertices; and
`through_edge_witness` exhibits a concrete triangle `(0,0), (2,0), (1,1)` with `V` the midpoint
`(1,0)` of its bottom edge satisfying all three at once.

**What this does NOT do — stated flatly.** It does not close case (a); it does not close
`conj:advance`; it does not close `e = 1`; the prime case is untouched. In the vertex branch the
rightward segment is a whole edge with `V` as endpoint, so its length is `a`, `b` or `c` and
`overshoot_dichotomy` runs. In the `π` branch it is a *suffix* of an edge, of unconstrained length,
and `overshoot_dichotomy` does **not** apply to it as it stands. What changed is the shape of the
gap: case (a) is no longer needed to put a horizontal rightward segment at `V`, only to know that
segment is a whole edge from `V`. The residual sub-question — the reach `t` of that suffix against
`a`, in the three cases `t > a`, `t = a`, `t < a` — is new, is not formalized here, and nothing in
this file bears on it. `GOAL_PRIMES.md` target 1 remains open.

| C `conj:advance` (case (a) role) | the straight angle below the line is used only to exclude the serving tile's own `π`; the `π` branch is instead pinned horizontal | `RouteOne.through_edge_lays_rightward`, `.serving_lays_rightward`, `.coords_of_localAngle_pi`, `.midpoint_localAngle_pi`, `.through_edge_witness` | VERIFIED (the narrowing; the conjecture itself remains CONJECTURE) |

### RouteOneThroughEdge, second increment (same session)

Five more theorems in the same file, all axiom-clean, `Erdos634.All` clean.

**The sharper exclusion.** `PinPlumbing.at_most_two_through` says three straight angles at an
interior point are impossible. `two_through_excludes_third` sharpens it to what the wall argument
needs: **two** straight angles already exhaust the `2π`, so any third tile has local angle `0` there;
`two_through_excludes_mem` restates it as "no third tile may even *contain* the point"
(via `MarchFlank.localAngle_ne_zero_of_mem`).

**Edge interiors.** `openSegment_localAngle_pi`: *every* point of an open edge has local angle `π`,
not just the midpoint — with `localAngle_pi_of_coords` and `not_vertex_of_coord_zero` factored out,
and the earlier `midpoint_localAngle_pi` now a special case. `through_edge_data` upgrades
`through_edge_lays_rightward`'s output from "a point to the right" to the edge itself: it names `k`
with `V ∈ openSegment ℝ (pts (k+1)) (pts (k+2))` and that edge horizontal (the coefficients sum to
`1` by adding the two displacements and cancelling the nonzero edge vector).

**The mechanism, stated.** `shared_edge_interior_excludes_third`: two distinct tiles cannot share a
point in the relative interior of an edge of each while a third tile contains it. This is the
location-sensitive statement the configuration wants — the serving tile's through-edge at `V` is
horizontal, so it runs *along the wall line* and overlaps the `α`-tile's own horizontal edge `VA`
on a whole stretch left of `V`, and the tiles below the wall contain that stretch.

**Still not closed, precisely.** The overlap point is *hypothesised*, not constructed: turning
`shared_edge_interior_excludes_third` into an unconditional exclusion of the `π` branch needs a
point `W` exhibited in both open edges (elementary horizontal-coordinate bookkeeping, not new
mathematics — the two segments share a leftward stretch from `V`), plus the configuration facts
that the `α`-tile has its horizontal edge from `V` and that wall points carry a tile below. None of
that is done here. `conj:advance` remains CONJECTURE; `GOAL_PRIMES.md` target 1 remains open.

### RouteOneThroughEdge, third increment: case (a) removed from the flank step

Three more theorems (`mem_openSegment_of_horizontal`, `serving_ne_pi_of_left_edge`,
`route_one_flank_no_straight`), all axiom-clean, `Erdos634.All` clean, no `sorry`. Sixteen theorems
in the file now.

**The result.** `route_one_flank_no_straight` is `route_one_flank_composed` with `hcard` (the
`π`-count is one) and `hb` (the tile below the line carries the straight angle) **deleted** — the two
that are jointly `conj:advance`'s case (a). The serving tile still comes out with `V` as a vertex and
a horizontal rightward edge there, which is what `overshoot_dichotomy` consumes.

**How.** The `π` branch is not excluded but *pinned*: `through_edge_data` makes the through-edge
horizontal (from `habove` alone), so it runs along the wall line and overlaps the `α`-tile's own
horizontal edge `VA` on a stretch left of `V`. `mem_openSegment_of_horizontal` exhibits a point of
that overlap explicitly. At that point two distinct tiles each have local angle `π`, which exhausts
the `2π`, so no third tile may contain it (`two_through_excludes_mem`) — but the tiles below the wall
do. `serving_ne_pi_of_left_edge` is that contradiction.

**What replaced case (a).** (i) The `α`-tile lays a horizontal edge from `V` leftward to `A` — this
is `rem:route1uniform`'s own geometry, algebra already VERIFIED (`Frontier.route1_spacings`,
`.side_tile_third_vertex`). (ii) `hthird`: the open stretch `VA` is interior to the target and every
point of it lies in a tile other than the two.

**What is still open, precisely.**
* `hthird` is a **hypothesis, not a theorem**. Deriving it is the routine covering argument (points
  just below the wall are covered by `D.covers`; the covering tile is neither upper tile, by
  `habove`; it contains the limit point by closedness, `mem_of_approach`). Standard dissection
  bookkeeping — but **not done here**, and it must not be counted as done.
* No `Dissection` witness is constructed for the configuration, so the vacuity check stands where
  `VacCheck` leaves `EscapeData.ofWall`: the through-edge block is witnessed
  (`through_edge_witness`), the wall configuration is not.
* The attachment obligation of `rem:routeoneopen` (OPEN) is untouched; so are case (b), case (c),
  the descent's remaining inputs, and all of `e ≥ 2`.
* **`conj:advance` remains CONJECTURE. `e = 1` is not closed. The prime case is not advanced.**

**Why it is nevertheless worth recording.** `prop:ninetools`' admission test is location-sensitivity:
the crossing question asks *where* an edge lies, and every closed tool class computes something
invariant under relocating edges. This step meets that test — the mechanism is that two horizontal
edges through the same wall point exhaust the angle there — and it converts the obligation at this
step from a crossing-question fact (where the edge below `V` lies) into a covering fact (that
*something* lies below the wall), which is a change of kind, not merely of wording.

| C `conj:advance` (case (a), flank step) | Route 1's flank at `V` needs no straight angle below the line | `RouteOne.route_one_flank_no_straight`, `.serving_ne_pi_of_left_edge`, `.shared_edge_interior_excludes_third`, `.through_edge_data` | VERIFIED (the flank step, modulo the `hthird` covering hypothesis; `conj:advance` itself remains CONJECTURE) |

### RouteOneThroughEdge, fourth increment: `hthird` discharged, case (a) gone from the flank step

Six more declarations (`downVec` + three coordinate facts, `exists_tile_below`,
`third_tile_of_interior`, `route_one_flank_from_configuration`). Twenty-three in the file, all
axiom-clean, `Erdos634.All` clean, no `sorry`.

**`hthird` is now a theorem.** `exists_tile_below`: a point interior to the target lies in a tile
that also contains points strictly below it — proved from `D.covers` and the same
`Finite.exists_infinite_fiber` pigeonhole the approach argument uses, with `mem_of_approach` closing
the limit. `third_tile_of_interior` then supplies the third tile the exclusion needs, since a tile
holding a point below the line is neither of the two tiles that keep to the upper side.

**The composite.** `route_one_flank_from_configuration` gives Route 1's flank conclusion at `V` —
the serving tile has `V` as a vertex with a horizontal rightward edge, the input
`overshoot_dichotomy` consumes — from: the three standard serving-tile facts already discharged
elsewhere (`hne0`, `hne2pi`, `hserve`); that tiles `i` and `j` keep to the upper side of the wall;
that the `α`-tile `j` lays its horizontal edge from `V` leftward to `A`; and that `V`, `A` are
interior to the target (interiority of the stretch follows by convexity of the interior). **No
straight angle below the line, no `π`-count, no covering assumption.**

**What this is not.** It removes `conj:advance`'s case (a) **at the flank step at `V`, and nowhere
else.** Specifically it does *not* touch:
* **the attachment** — every hypothesis above must still be exhibited in a hypothetical base-`β`
  tiling; that is `rem:routeoneopen` (OPEN), untouched;
* **the straight angle at `E`** — the descent's `fig n` input needs one at the *advanced* point (see
  the `fig n` row above, "the outstanding fact is the straight angle at `E`"). That is a separate
  instance of the same kind of fact and nothing here bears on it. Whether the same
  two-horizontal-edges mechanism applies there is an open question, not a claim;
* case (b), case (c), the rest of the descent, and all of `e ≥ 2`.

**`conj:advance` remains CONJECTURE. `e = 1` is not closed. The prime case is not advanced.** No
`Dissection` witness is constructed for the wall configuration, so the vacuity position is exactly
`VacCheck`'s for `EscapeData.ofWall`: the through-edge block is witnessed
(`through_edge_witness`, `midpoint_localAngle_pi`), the wall configuration is not.

### RouteOneThroughEdge, fifth increment: the mechanism transfers to `E` — as propagation, not production

**The probe, answered.** The obvious transfer fails. `two_through_excludes_mem` *excludes* straight
angles; the descent's `fig n` input wants to *produce* one at the advanced point `E`. Opposite
directions, no transfer.

**What does transfer is the flank argument itself.** `route_one_flank_from_configuration` needs, at
its point, some other tile laying a horizontal edge from that point **leftward**. At `V` that is the
`α`-tile's edge `VA`. At `E` it is *the edge just produced*: the serving tile at `V` lays a
horizontal edge from `V` rightward to `E`, and that same edge read from `E` runs horizontally
leftward to `V`. So each step supplies its successor's hypothesis.

`flank_propagates` is that statement, machine-checked: from the flank conclusion at `V` (tile `i`
has `V` as a vertex, horizontal edge to `E`), the flank conclusion holds at `E` for the tile serving
the approach there — **with no figure at `E` and no straight angle at `E`.** The generalisation
needed was only orientational: `serving_ne_pi_of_side_edge` / the composites now take a
segment-*subset* hypothesis instead of two vertex equations, so the previous step's edge can be read
in either direction (`openSegment_symm`).

**Where this lands.** `route_one_closes'` — the descent scheme *without* a `fig` argument — already
exists and is VERIFIED. The reason it could not be used was that `htri`, the trichotomy step at the
advanced point, needed the flank there, and the only route to that flank went through the figure,
hence through a straight angle at `E`, hence through case (a) again. `flank_propagates` supplies
that flank directly. **The descent's step no longer needs a figure at the advanced point.**

**What this does not do.** (i) The attachment is untouched and has in fact acquired a *uniformity*
obligation: `flank_propagates`' per-step hypotheses — an approach at each advanced point, each new
serving tile weakly above the wall, interiority of each point — must be produced for every `n`, and
that is not done. (ii) Composing `flank_propagates` with `overshoot_dichotomy` and
`produced_edge_blocks` into an actual `htri` for a real configuration is likewise not done.
(iii) Case (b), case (c), and all of `e ≥ 2` are untouched.

**`conj:advance` remains CONJECTURE. `e = 1` is not closed. The prime case is not advanced.**

| C `conj:advance` (descent step) | the flank at the advanced point propagates from the previous step; no figure, no straight angle at `E` | `RouteOne.flank_propagates`, `.route_one_flank_from_configuration`, `.serving_ne_pi_of_side_edge` | VERIFIED (the propagation; the uniform-in-`n` attachment is not done and `conj:advance` remains CONJECTURE) |

### `conj:advance`'s "Unproved:" sentence is now stale in *both* clauses

The conjecture's text names two facts as unproved for the `[V,E]` question: "(a) that a through-edge,
rather than a junction, runs below the line at `V`, and (b) that the exactly-filled wedge's last
flank lies along the line".

* **(a) is removed** by this session's `route_one_flank_from_configuration` — the flank at `V` needs
  no straight angle below the line (see the four increments above).
* **(b) is superseded, and was already superseded before this session.** `RouteOne.escape_flank`
  reaches the very conclusion (b) was meant to supply — some tile lays a horizontal rightward edge at
  the point — from exactly two hypotheses: the tile lies weakly above the wall, and it contains
  tangential approach points. It runs through `flank_along_line'` → `flank_along_line`, whose
  non-degeneracy input is `not_both_horizontal` (the tile's own determinant), **not** a wedge. Its
  own docstring says so: "no assumption about the figure, and none about the tile below beyond its
  keeping `T` above the wall". The exactly-filled-wedge argument is a *route* to that conclusion; a
  different route exists and is verified. Nothing new was needed for this — it was simply never
  checked against the conjecture's own sentence, the same oversight as `rem:route1uniform` having no
  row at all (fixed earlier today).

**This does not prove `conj:advance`, and the distinction matters.** The two clauses were the named
obstacles *to the `[V,E]` question*; the conjecture's other obligation — `rem:routeoneopen`'s
attachment, exhibiting the configuration in a hypothetical base-`β` tiling — was always separate and
is still OPEN. What has changed is that the `[V,E]` question's own stated obstacles are gone, and
the remaining work is attachment and uniformity, both of a different kind.

**Next obstacle, identified precisely.** Every per-step hypothesis of `flank_propagates` except one
is routine at an interior wall point. The exception is `habove` — that each serving tile lies
*weakly above the wall globally*, not merely near the point. In the corpus that is the consequence of
the wall being **edged** (no tile's interior meets it): a tile with vertices on both sides of the
line has interior meeting the line, which an edged wall forbids, so every tile lies on one side
(`StraightEdgeSums`' prose; `Tri.carrier_subset_halfplane_affine` is the half of it that is proved).
That is one hypothesis about the wall, uniform in `n`, not a per-step family — and it is not yet a
theorem here.

### RouteOneThroughEdge, sixth increment: the uniformity worry dissolves

Three more theorems (`height_eq_coord_combo`, `carrier_above_of_vertices`,
`route_one_flank_of_vertices`); 31 declarations in the file, all axiom-clean, `Erdos634.All` clean.

The obstacle flagged in the fifth increment was `habove` — that each serving tile lies weakly above
the wall *globally*, which looked like it needed the wall to be edged (an unproved straddle theorem).
It does not. The second coordinate is affine and the barycentric coordinates are nonnegative on the
carrier, so `height_eq_coord_combo` writes a carrier point's height as the barycentric average of the
vertices' heights, and `carrier_above_of_vertices` concludes: **a tile whose three vertices lie
weakly above the wall lies weakly above it.** `habove` is therefore three sign conditions on
vertices, not a global assumption — and three sign conditions on vertices is exactly what the
corpus's own `no_downward_edge` / `edge_dir_nonneg_of_local` produce from local containment.
`route_one_flank_of_vertices` restates the flank theorem in that form.

So the edged-wall straddle theorem is **not needed** for this purpose. That was a false alarm in the
previous entry, corrected here rather than left standing.

**Position after six increments.** For the `[V,E]` question at `e = 1`:
* case (a) — removed (`route_one_flank_from_configuration`);
* case (b) — superseded, and already was (`escape_flank`);
* case (c) — its step is `flank_propagates`, its terminus is `terminus_of_run_length` (VERIFIED),
  its `inWall` is VERIFIED, and the figure-free descent scheme `route_one_closes'` is VERIFIED;
* the per-step `habove` is now three vertex sign conditions, not a global or uniform assumption.

**What is still not done, and is now the whole of it: the attachment.** Every hypothesis of
`route_one_flank_of_vertices` and `flank_propagates` — the vertex sign conditions, the tangential
approach at each point, interiority, the `α`-tile's horizontal edge, and `i ≠ j` — must be exhibited
in a hypothetical base-`β` tiling, and composed with `overshoot_dichotomy` and
`produced_edge_blocks` into an `htri` for `route_one_closes'`. That is `rem:routeoneopen`, still
OPEN, and nothing in this session touches it. Case (b)'s and case (a)'s removal does not shrink it.

**`conj:advance` remains CONJECTURE. `e = 1` is not closed. `e ≥ 2` is untouched. The prime case is
not advanced.**

### RouteOneThroughEdge, seventh increment: the `[V,E]` question itself, answered

Five more theorems (`edge_length_mem_model`, `edge_length_mem_model'`, `dist_eq_x_of_horizontal`,
`VE_dichotomy`, `VE_dichotomy_of_flank`); 36 declarations in the file, all axiom-clean,
`Erdos634.All` clean, no `sorry`.

`rem:route1uniform` reduces route 1 to one question — *what covers the segment `[V,E]` of length
exactly `a`?* — and says "We do not prove that here". With the flank in hand it is now forced.
`edge_length_mem_model` uses `Congruence.Tri.Congruent.sideMultiset_eq` and
`CongruentTileEdges.Tri.sideMultiset_shift` to put any tile edge's length among the model's three
sides; `dist_eq_x_of_horizontal` identifies a horizontal edge's length with its `x`-offset; and
`overshoot_dichotomy` closes:

> **`VE_dichotomy_of_flank`.** For a tile of a `CongruentDissection` whose model has sides
> `f, f²−1, f²` (the `e = 1` base-`β` family in `rem:route1uniform`'s own scaling), a horizontal
> rightward edge from `V` either has length exactly `a = f` — its far endpoint *is* `E`, so `E` is a
> junction and the march advances — or its length exceeds `f`, so `E` lies strictly inside it, which
> is the tile-interior blocking whose failure defined the escape, and the branch dies.

It is stated over the flank's own disjunction (either neighbour of `V`), so it composes directly with
`route_one_flank_of_vertices` and `flank_propagates`. **No straight angle is assumed anywhere in the
chain.**

**Where route 1 now stands, as a chain of machine-checked steps.** flank at `V`
(`route_one_flank_of_vertices`, from vertex signs + approach + the `α`-tile's edge + interiority) →
`[V,E]` dichotomy (`VE_dichotomy_of_flank`, from congruence) → on the surviving branch, flank at `E`
(`flank_propagates`, the previous step's edge in the `α`-tile's role) → terminus
(`terminus_of_run_length`, VERIFIED) → descent (`route_one_closes'`, VERIFIED, figure-free).

**What is still missing — unchanged and now isolated.** The *attachment*: every hypothesis of these
theorems (the vertex sign conditions, the tangential approach at each point, interiority, the
`α`-tile's horizontal edge, `i ≠ j`, and the model's side lengths) has to be exhibited in a
hypothetical base-`β` tiling, and the steps composed into an `htri` for `route_one_closes'`. That is
`rem:routeoneopen` (OPEN), and it is blocked on the standing "no tile-placement layer" blocker
recorded in `CLAUDE.md`. Nothing in this session touches it.

**`conj:advance` remains CONJECTURE. `e = 1` is not closed. `e ≥ 2` is untouched. The prime case is
not advanced.**

| C `rem:route1uniform` (the `[V,E]` question) | what covers `[V,E]`: length `a` (junction, march advances) or longer (`E` interior, branch dies) | `RouteOne.VE_dichotomy_of_flank`, `.VE_dichotomy`, `.edge_length_mem_model` | VERIFIED (given the flank and the model's sides; the attachment remains OPEN) |

### RouteOneThroughEdge, eighth increment: the straight-angle count is a theorem, not an assumption

`pi_count_le_one`, `pi_count_eq_one`; 38 declarations in the file, all axiom-clean, `Erdos634.All`
clean.

`two_through_excludes_mem` is not route-1-specific. Read as a bound it says: **at an interior point
where some tile sits without a straight angle, at most one tile has one** — two would already exhaust
the `2π` and leave no room for that tile. `pi_count_eq_one` adds a tile that does carry one and gets
the count exactly.

This is the `hcard` hypothesis of `route_one_flank_composed` and the `s = 1` conclusion of
`alpha_wall_figure` — obtained here **geometrically from the angle sum, with no appeal to the
irrationality of `α` and no vertex-figure classification**. Consequence for the record: of the pair
`hcard`/`hb` that together made up `conj:advance`'s case (a) in the old chain, only `hb` — a tile
below actually carrying the straight angle — was ever an independent assumption; `hcard` follows
from it plus any tile at the point without a straight angle, which in the configuration is the
`α`-tile. (The new chain needs neither, so this is a statement about the old one.)

Reusable beyond route 1: any vertex-figure argument in the corpus that assumes `s ≤ 1` at a junction
can now cite `pi_count_le_one` instead.

**No label moves. `conj:advance` remains CONJECTURE; the prime case is not advanced.** The
attachment (`rem:routeoneopen`, OPEN, blocked on the tile-placement layer) is untouched.

### Scan result: `pi_count_le_one` makes **no** named target fall — previous entry overstated it

Applied `CLAUDE.md`'s own test to the eighth increment. Every π-count hypothesis actually assumed in
the corpus is `card = 0` (`MarchRun.lean:45`, `.74`; `JunctionWedge.lean:157`) — *no* tile has a
straight angle at the point — which is strictly stronger than `pi_count_le_one`'s `≤ 1` and is the
crossing question at that point, untouched by it. The `card = 1` occurrences
(`RouteOne.alpha_wall_figure_real`) are **conclusions**, not hypotheses, so there is nothing there to
discharge either.

So the previous entry's line — "any vertex-figure argument in the corpus that assumes `s ≤ 1` at a
junction can now cite `pi_count_le_one`" — is **wrong as written**: there are no such call sites.
Corrected here rather than left standing. `pi_count_le_one` remains a correct and cheap geometric
derivation of a fact the figure route gets from the classification, and it is used inside this
file's own chain; it is not, on the evidence of the scan, a lever on anything else.

No label moves. Recorded as a tool, not as progress.

### Probe: does this session's mechanism reach `e ≥ 2`'s `V_k`?  **No — and the reason is sharp**

`rem:n1gapexact` reduces `thm:n1`'s induction at `e ≥ 2` to: nothing overruns `V_k`. The tile `Q`
across `T_k`'s `b`-edge lays `a`, `b` or `c` from the anchored base end; `b` is the wanted match,
`a` fails because `b − a` is unrepresentable (`gap_b_sub_a`), and `c` overruns by `e²` — which means
exactly that **`Q` has a straight angle at `V_k`**. So the gap is "exclude one straight angle", the
same shape this session's `serving_ne_pi_of_side_edge` handles at `V`.

**It does not transfer, and the obstruction is structural.** The leverage at `V` was never "a tile
has a through-edge"; it was that a *second* tile — the `α`-tile — lays an edge **collinear with it and
on the same side**, so two upper half-discs would overlap and `two_through_excludes_mem` fires. At
`V_k` no second such tile exists: `T_k`'s `b`-edge *ends* at `V_k`, so `T_k` contributes a corner
angle there, not a straight angle. Taking a point `W` strictly between the base end and `V_k` does
give two straight angles (`T_k`'s and `Q`'s) — but those are the two tiles adjacent along that edge,
the ordinary situation, and `two_through_excludes_mem` correctly yields nothing. And `pi_count_le_one`
permits exactly one straight angle at `V_k`, which is precisely what `Q` would use.

**So: this session's machinery is silent on `e ≥ 2`.** Recorded as a closed-off route, not a
difficulty. The precise admission test it suggests for future attempts on `V_k`: find a *second edge
collinear with the overrunning one, on the same side*. Route 1 had one for free; `e ≥ 2` does not,
and nothing in the residue computation of `rem:n1gap` supplies one.

`GOAL_PRIMES` target 3 is untouched. No label moves.

### Scoping the attachment: the blocker is sharper than "no tile-placement layer"

Route 1's chain is complete; what it needs is its hypotheses produced from a hypothetical tiling.
Mapping them against what exists:

| hypothesis | status |
|---|---|
| `V`, `A` interior to the target | routine (`approach_points_covered` works at interior points) |
| tangential approach at each point | `pigeonhole_wall`, `approach_points_covered` — available |
| vertex sign conditions (tiles above the wall) | `above_line_of_below_tile`, `no_downward_edge` give the mechanism |
| `i ≠ j` | trivial once both tiles are named |
| model sides `{f, f²−1, f²}` | member data |
| **the `α`-tile: a named tile laying a horizontal edge from `V` leftward to `A`** | **missing** |

So the attachment reduces to producing **one named object**: the second side tile of the corner
cascade, the one `rem:route1uniform` describes as carrying its `a`-edge `AB` on the side, mirrored
(`lem:firstrun`), with third vertex `V = c·u + (c,0)`. Its *coordinates* are already verified
(`Frontier.side_tile_third_vertex`, `.route1_spacings`); what is missing is the tile as an object of
a `Dissection`.

**Two findings worth recording.**

1. `TilePlacement.HasVertex` / `.PresentsAt` / `.LaysOn` — the placement vocabulary — exist but have
   **zero consumers**: a grep across the corpus finds no theorem outside their own file that
   mentions them. So they are names, not a layer, and `CLAUDE.md`'s "no tile-placement layer"
   blocker is accurate in substance despite the definitions existing.
2. `TileAt.lean` does have real structure for a `CongruentDissection`'s corner: `exists_corner_tile`,
   `congruentDissection_base_corner_tile_unique`, `.base_corner_tile_vertex`,
   `.congruentDissection_endpoints_of_chain`. That is the corner cascade's **first** tile. The
   partner and the second side tile — `lem:firstrun`'s mirrored-orientation content — are not there;
   `OrderForcing.first_run_kill` is only that lemma's *arithmetic* core (a vertex-figure count), not
   its placement.

**Named blocker, replacing the vague one for this route:** *the second side tile of the corner
cascade does not exist as a `Dissection` object; producing it needs `lem:firstrun`'s orientation
forcing at the placement level, on top of `TileAt.congruentDissection_base_corner_tile_vertex`.*
That is one object, not a general layer — a materially smaller obligation than "build tile
placement", and it is the whole of what stands between route 1's chain and `conj:advance` at `e = 1`.

No label moves. `conj:advance` remains CONJECTURE; the prime case is not advanced.

### `partner_unique` is arithmetic, not placement — and the geometric half is *known false* in general

Checked `OrderForcing.lean:127`'s claim that the corner tile's `b`-partner is "forced onto the far
side of the corner tile's `b`-edge by `PentagonLemma.partner_unique`".

`PentagonLemma.partner_unique` is a real theorem and it is **pure semigroup arithmetic**: the only
way to write `b` as `x·a + y·b + z·c` in `ℕ` is `y = 1`. It says nothing about tiles, sides, or
placement. Forcing the partner needs that *plus* the geometric premise that the chord is covered by
**whole edges** — and that premise is exactly what `lem:jbline`'s own parenthetical defers
("Whether a given line is so covered is a separate question: see Remark `rem:straddle`").

`rem:straddle` then says something stronger than "open": the no-straddle hypothesis
(DL) — *if a segment carries a whole `b`-edge at each end, no tile straddles it* — **is false**,
tested against the three exhibited base-`β` tilings with tile `(2,3,4)`, all verified exactly. Tiles
do straddle.

**Consequence for the attachment.** The corner cascade's second tile cannot be produced by
`partner_unique` plus a general no-straddle fact, because no such fact holds. What can rescue the
specific case is that the cascade's chord is *boundary-anchored at both ends* — a straddling tile
there would have to leave the target — which is the mechanism `prop:doublec`(iv) and the overshoot
tests use. That boundary-anchored argument is a different piece of machinery from `partner_unique`,
and **it is not in the corpus**.

So the named blocker sharpens once more: *producing the corner cascade's partner needs a
boundary-anchored no-straddle theorem; the general form is refuted (`rem:straddle`), and the anchored
form is unformalised.* The docstring at `OrderForcing.lean:127` overstates what it cites and should
be read with this correction.

Recorded as a negative structural finding. No label moves; `conj:advance` remains CONJECTURE.

### Correction: the partner's geometric half is **not** blocked — `edge_two_sided` discharges it

The previous entry concluded that forcing the corner cascade's partner needs a boundary-anchored
no-straddle theorem that "is not in the corpus". **That is wrong, and this entry corrects it.**

`Dissection.edge_two_sided` (VERIFIED, axiom-clean) already does the work, and its own docstring says
so: *"All wall hypotheses are discharged: `edge_point_not_interior` makes any tile edge a wall."* For
a tile edge the no-straddle premise is free — an edge point lies in that tile's carrier, so it is in
no tile's interior (`not_mem_interior_of_mem`) — and the theorem returns that **both** the near- and
far-side line chains cover the edge exactly once in `μH¹`. Its only hypothesis is `hint`: the edge's
open segment lies in the target's interior. It even notes that composite chords of several collinear
tile edges follow the same way.

My error was conflating two different segments. `rem:straddle` refutes no-straddle for an *arbitrary*
segment carrying whole `b`-edges at its two ends — a segment nobody owns. The corner cascade's chord
is the corner tile's **own `b`-edge**, and for a tile's own edge the straddle question does not arise
at all. The refutation does not apply to it.

**So the partner is reachable, and the assembly is now named:**
1. `edge_two_sided` on the corner tile's `b`-edge → the far side is covered exactly once by a chain
   of whole tile edges, total `μH¹`-length `b`;
2. `RouteOne.edge_length_mem_model` (built this session) → every chain edge's length is `a`, `b` or
   `c`;
3. `PentagonLemma.partner_unique` → the only `ℕ`-combination summing to `b` is a single `b`;
4. hence exactly one tile lays a whole `b`-edge there: **the partner, as an object.**

What genuinely remains: discharging `hint` for the corner tile's `b`-edge (its open segment interior
to the target — real but modest, and specific to the corner geometry), and turning the `μH¹` measure
equation of (1) into the edge *count* of (3) — `PinPlumbing.wall_run_equation` is the existing tool
for that step. Neither is a crossing question.

This is the first genuine crack in the attachment. `conj:advance` remains CONJECTURE and no label
moves — but the blocker named two entries ago was overstated and is retracted here.

### The partner assembly hits the wall again — at `hwhole`. "Three routes, one wall" confirmed.

Checked `PinPlumbing.wall_run_equation`, the measure-to-count step named in the previous entry. It
does exactly what is wanted — `∃ x y z : ℕ, x·A + y·B + z·C = edist u₁ u₂` in the model's three edge
lengths — but it carries a hypothesis the previous entry did not account for:

> `hwhole : ∀ e ∈ D.lineChain f c, (D.tile e.1).edge e.2 ⊆ segment ℝ u₁ u₂`

**every chain edge lies wholly inside the wall segment.** Without it the summands in
`edge_two_sided`'s conclusion are partial intersections, not whole edge lengths, and no semigroup
identity follows.

For the corner tile's `b`-edge, `hwhole` says: no chain edge overruns either endpoint. One endpoint
lies on the target's boundary, where an overrunning edge would leave the target — killable by
containment, the mechanism `prop:doublec`(iv) uses. **The other endpoint is interior, and excluding
an overrun there is the crossing question**, verbatim.

**So the previous entry was too optimistic, and this corrects it.** `edge_two_sided` genuinely
discharges `hwall` for a tile's own edge — that part stands. But the step from its measure identity
to an edge *count* needs `hwhole`, and `hwhole` at the interior end is exactly what
`rem:n1gapexact` calls the one-end-anchored pinning question: *the base end cannot be overrun,
because the continuation would leave the target, while the interior end is not blocked by anything
already forced.*

**Honest consequence for this session's work.** Route 1's chain now answers the `[V,E]` instance of
the crossing question without assuming a straight angle. Attaching it requires answering a
*different* instance — no overrun at the interior end of the corner tile's `b`-edge. The session did
not get around the wall; it **moved which instance you must answer**, from the one at `V` to the one
at the cascade's first `b`-edge. `rem:n1gapexact`'s summary — "Three routes, one wall" — is
confirmed, not refuted, by this work.

That is the honest terminal position for this line. `conj:advance` remains CONJECTURE, `e = 1` is not
closed, and the prime case is not advanced.

### Census reconciled — and it is now reproducible

Flagged three times this session as unreliable; fixed. The authoritative source is the `\lab{...}`
tags in `paper/*.tex`, one per tracked statement, with the **leading word** being the label (tags may
carry a qualifier: `\lab{PROVED: the walk arithmetic VERIFIED}` is a PROVED statement, not a VERIFIED
one — counting the word "VERIFIED" anywhere in the tag is what inflates naive greps).

`code/census.sh` now computes it. Current, checked:

```
PROVED 116   VERIFIED 57   CONJECTURE 30   HEURISTIC 4   OPEN 3      (210 tagged statements)
```

**The discrepancy is explained.** `private/RESEARCH_LOG.md` carried `119/54/30/4/3` while this thread
carried `116/57/30/4/3`. Both total 210 and both agree on CONJECTURE/HEURISTIC/OPEN; they differ only
in three statements counted PROVED by one and VERIFIED by the other. The `\lab{}` tags — the thing
Rule 0 actually labels — say 57 VERIFIED. So the `.tex` figure is correct and the log's is three
short; the log was evidently counting `PAPER_MAP.md` rows, which lag the papers. Future ticks should
run `code/census.sh` rather than quote either.

**This session's Route-1 work does not move the census**, and it is worth being explicit about why:
`rem:route1uniform` carries no `\lab{}` tag at all (remarks frequently don't), so the VERIFIED row
added for it earlier today is a `PAPER_MAP` record, not a census entry. Same for the
`conj:advance` sub-claim rows. `conj:advance` itself remains CONJECTURE, tagged as such in the
companion.

### Debt triage: the PROVED rows are already triaged; one buildable blocker identified

Scanned the `\lab{PROVED}` statements whose subject matter this session's tools touch (straight
angles, through-edges, walls, junctions) for the "unassembled bridge" pattern that produced earlier
flips. **The pattern is exhausted at this depth** — the rows are already triaged with named
blockers by previous sessions, and the triage is correct:

* `lem:parity` — blocked on `lem:census`'s α-identity; the row already warns that upgrading without
  it would repeat the ingredient-for-statement error.
* `lem:census` — blocked on *the global corner-incidence double count*.
* `lem:anglecalc` — clause (5) blocked on the deferred strip-and-column exposition; the row's own
  conclusion, "no further attempt is worthwhile until the strip-and-column exposition itself is
  built", stands.

**One of these is buildable, and it is the only one.** `lem:census`'s blocker is a *finite* double
count, not deferred content:

> Every tile of a `CongruentDissection` has exactly one `α`-corner, one `β`-corner and one
> `γ`-corner (the model's three angles being distinct). Summing over tiles gives `N` corners of each
> type. Summing instead over the finitely many points that are vertices of some tile — the set
> `⋃ i, range (D.tile i).pts`, finite because `N` is — gives `∑_v #{i : (D.tile i).localAngle v = α}`.
> The two totals are equal. Those are the corner-balance equations that `OrderForcing.vertex_census`
> (`OrderForcing.lean:765`) currently takes as **hypotheses**.

Feasibility, checked: `PinPlumbing.localAngle_cases` already gives that a tile's local angle at a
point is a corner angle exactly at its vertices; `CongruentAngles.congruent_corner_angles` gives that
a congruent tile's corner angles are the model's three. No vertex-set or double-count infrastructure
exists yet (grep: nothing named `vertexSet`/`allVertices`; `Finset.sum_comm` appears only
incidentally). So this is new but bounded work — a `Finset` double count over `⋃ i, range pts`.

**Closing it would flip `lem:census`, and `lem:parity` behind it — two census moves.** That meets
`CLAUDE.md`'s test that machinery only counts when a named target falls. Recorded as the next
build target.

Census (`code/census.sh`): PROVED 116, VERIFIED 57, CONJECTURE 30, HEURISTIC 4, OPEN 3. Unmoved.

### `lem:census` double count, piece 1: corner angles match under one permutation

New file `Erdos634/CornerAnglePerm.lean`, one theorem, axiom-clean, `Erdos634.All` clean.

`Tri.Congruent.cornerAngle_perm`: congruent triangles match **all three** corner angles under a
*single* permutation of vertex indices. This is the uniform form the double count needs;
`Congruence.Tri.Congruent.dist_eq` gives the uniform permutation for *distances* only, and
`CongruentAngles.congruent_corner_angles` gives corner angles only one vertex at a time,
existentially — neither suffices to say "each tile has exactly one `α`-corner".

The route is the isometry, not the distances: a `Tri.Congruent` carries an `IsometryEquiv` of the
plane; **Mazur–Ulam** (`IsometryEquiv.toRealAffineIsometryEquiv`, Mathlib) makes it affine, and
`AffineIsometry.angle_map` transports corner angles directly. The residual combinatorics — that `σ`
carries the two vertices other than `k` to the two other than `σ k`, in one order or the other — is a
`Fin 3` fact settled by `decide`, with `EuclideanGeometry.angle_comm` absorbing the swap.

**Remaining for the double count:** (2) from distinct model angles, exactly one corner of each tile
carries each angle — a counting consequence of piece 1; (3) the finite vertex set
`⋃ i, range (D.tile i).pts` and the `Finset` double count against `localAngle`; (4) discharging
`OrderForcing.vertex_census`'s corner-balance hypotheses with the result. Then `lem:census` flips,
and `lem:parity` behind it.

Census (`code/census.sh`): PROVED 116, VERIFIED 57, CONJECTURE 30, HEURISTIC 4, OPEN 3. Unmoved —
this is piece 1 of 4.

### `lem:census` double count, pieces 2 and 3a: the tile side is done

Two more theorems in `CornerAnglePerm.lean` (three total), axiom-clean, `Erdos634.All` clean.

* `Tri.Congruent.corner_count_eq_one` — given the model's three corner angles pairwise distinct, a
  congruent tile has **exactly one** corner carrying each model angle. From piece 1's permutation:
  `σ k` witnesses existence, and uniqueness is distinctness pulled back through `σ`.
* `congruentDissection_corner_total` — summing that over the dissection: the tiles carry exactly
  **`N` corners of each of the three angles**.

That is the **tile side** of the corner-incidence double count, complete. What remains is the
*vertex* side — grouping the same corners by the point they sit at:

* (3b) the finite vertex set `⋃ i, range (D.tile i).pts` as a `Finset`, and the double count
  `∑_i #{j : corner j of tile i is θ} = ∑_v #{i : (D.tile i).localAngle v = θ}`. The bridge is
  `PinPlumbing.localAngle_cases`, which puts a tile's local angle at a corner angle exactly at its
  vertices; the sum exchange is `Finset.sum_comm` over the incidence pairs `(i, v)`.
* (4) feed the resulting balance equations to `OrderForcing.vertex_census`, whose corner-balance
  hypotheses they are.

Then `lem:census` flips, and `lem:parity` behind it.

Census (`code/census.sh`): PROVED 116, VERIFIED 57, CONJECTURE 30, HEURISTIC 4, OPEN 3. Unmoved —
pieces 1–3a of 4.

### `lem:census` double count, piece 3 complete: the corner balance is a theorem

`CornerAnglePerm.lean` now has seven declarations, axiom-clean, `Erdos634.All` clean.

* `cornerPts` / `mem_cornerPts` — the finite set of points that are a vertex of some tile.
* `tile_corner_card` — for an angle that is not `0`, `π` or `2π`, one tile's corners of that angle
  counted **by index** equal the same corners counted **by point**: `localAngle_cases` puts the
  angle at the tile's own vertices, `Tri.localAngle_vertex` identifies the value there, and
  `indep.injective` makes the vertices distinct.
* `corner_double_count` — the exchange itself, `Finset.card_filter` + `Finset.sum_comm`.
* **`congruentDissection_corner_balance`** — for each model corner angle, the multiplicities of that
  angle summed over all vertex points equal `N`.

**That last one is the corner-incidence identity `lem:census` balances "across the `N` tiles",
obtained as a theorem rather than assumed.** It was the named blocker on `lem:census`'s row (*"that
global corner-incidence double count is still not done"*) — it is now done.

**What is left is piece 4, and it is bookkeeping of a specific kind:** `OrderForcing.vertex_census`
takes the balance in terms of the *figure counts* `n₁, n₂, v₁…v₄` — the numbers of points carrying
each named vertex figure — not as a sum of multiplicities over points. Bridging the two means
partitioning `cornerPts` by figure type and evaluating the multiplicity sum on each class. That
needs the figure classification at every vertex point, which for a real dissection is
`TileAt.congruentDissection_boundary_figure_cases` and the interior counterpart — available, but
not yet threaded. Only when that is done does `lem:census` flip; **it has not flipped yet, and the
label stays PROVED.**

Census (`code/census.sh`): PROVED 116, VERIFIED 57, CONJECTURE 30, HEURISTIC 4, OPEN 3. Unmoved.

### `hvals` discharged at every point — and piece 4 re-scoped honestly

`congruentDissection_localAngle_mem_all` (`CornerAnglePerm.lean`, eight declarations now,
axiom-clean, `Erdos634.All` clean): for a `CongruentDissection`, **any** tile's local angle at
**any** point is one of `α, β, γ, π, 2π, 0`.

This matters beyond `lem:census`. `TileAt.congruentDissection_localAngle_mem` proves it only at the
*target's own vertices*, and the `lem:anglecalc` row above records that the `hvals` hypothesis — every
tile's local angle here is one of those six — is carried unproved at general points by essentially
every vertex-figure lemma in `VertexFigureReal`. It needed nothing new: `localAngle_cases` splits
four ways, and in the corner branch `congruent_corner_angles` sends the tile's own corner angle to
one of the model's three. **It had simply never been stated in general.**

**Correction to the previous entry.** I called piece 4 "bookkeeping of a specific kind". That
understates it. Piece 4 needs `cornerPts` partitioned into the *eight* figure classes
`vertex_census` names (apex, two base corners, `n₁`, `n₂`, `v₁…v₄`) with the per-class multiplicity
evaluated — and the interior classification for a real dissection does not exist:
`VertexFigureReal.interior_figure_cases` takes the multiplicity data `p q r s u` and `hsum` as
*hypotheses*, and the corpus has no real-dissection instantiation at an arbitrary interior point.
`congruentDissection_localAngle_mem_all` supplies the first missing ingredient (`hvals`); the second
— the angle sum at an arbitrary interior point, feeding `hsum` — is `PinPlumbing
.pin_angle_sum_interior`, which exists. So the classification is now assemblable, but assembling it
and then the eight-way partition is a substantial build, **not** a tick's bookkeeping.

`lem:census` has **not** flipped; its label stays PROVED. What has changed is that its named
blocker (the double count) is a theorem, and `hvals` — a blocker for a much wider set of rows — is
now discharged in general.

Census (`code/census.sh`): PROVED 116, VERIFIED 57, CONJECTURE 30, HEURISTIC 4, OPEN 3. Unmoved.

### The interior vertex figure, for a real dissection at last

`congruentDissection_interior_figure_cases` (`CornerAnglePerm.lean`, nine declarations,
axiom-clean, `Erdos634.All` clean): at **any** interior point of the target of a
`CongruentDissection`, the multiplicities of `α, β, γ, π, 2π` are one of the classified
solutions — a single covering tile, two straight angles, one straight angle with a boundary figure
`{3α,2β}`/`{α,β,γ}`, or one of the four interior figures `{6α,4β}`, `{4α,3β,γ}`, `{2α,2β,2γ}`,
`{β,3γ}`.

Both halves already existed and had never been joined: `VertexFigureReal.interior_figure_cases_gen`
proves the classification *from* the multiplicity equation, and `.interior_multiplicities_cards`
proves that equation *from* `hvals`. Nothing had ever supplied `hvals` at a general interior point —
which is why the classification had never been instantiated for a real dissection anywhere in the
corpus. The previous entry's `congruentDissection_localAngle_mem_all` supplies it; this is the
composition, three lines.

This is the interior counterpart of `TileAt.congruentDissection_boundary_figure_cases` (which does
the frontier), so the vertex-figure classification is now available for a real dissection at
*every* point: target corners (`congruentDissection_base_corner_counts`/`.apex_counts`), other
frontier points (`boundary_figure_cases`), and interior points (this).

**For `lem:census` piece 4** that is the classification input; what remains is partitioning
`cornerPts` by which case holds and evaluating the multiplicity sum per class. **`lem:census` has
not flipped; label stays PROVED.**

Census (`code/census.sh`): PROVED 116, VERIFIED 57, CONJECTURE 30, HEURISTIC 4, OPEN 3. Unmoved.

### The falls-a-target test on the new classification: one real gap closed, and it is *not* the one I expected

Applied `CLAUDE.md`'s test to `congruentDissection_interior_figure_cases`. The scan turned up
something the previous entry had wrong.

**The junction lemmas do not take the `hvals` I proved.** `MarchRun.junction_dichotomy`
(`MarchRun.lean:44`, `:74`) and `JunctionWedge` (`:147`) carry
`hvals : ∀ i, localAngle v ∈ ({α, β, γ, π, 0} : Finset ℝ)` — **without `2π`**.
`congruentDissection_localAngle_mem_all` gives the *larger* set `{α, β, γ, π, 2π, 0}`, which does not
fit them. So the previous entry's implication that it discharges those call sites was wrong.

**Closed properly now.** `congruentDissection_localAngle_mem_at_corner`: at a point that is a vertex
of *some* tile, no tile covers the point, so every tile's local angle is in `{α, β, γ, π, 0}` — the
`2π`-free form those lemmas actually want. `2π` is excluded by
`Dissection.target_vertex_not_interior` (a vertex is not interior to its own triangle) for the tile
owning the vertex, and by `not_mem_interior_of_mem` for every other tile, then
`localAngle_ne_two_pi_of_not_mem_interior`.

**Does a named target fall? Not yet, and I am not going to claim one.** The `rem:marchobl` M-i /
M-vertex rows note this `hvals` is "suppliable for a real dissection though not yet threaded into
those call sites". It is now suppliable *in the right shape*, but threading it — instantiating
`junction_dichotomy` and the `JunctionWedge` lemmas at real march junctions — is a separate step and
is not done. Until it is, no row moves.

Ten declarations in `CornerAnglePerm.lean`, axiom-clean, `Erdos634.All` clean.

Census (`code/census.sh`): PROVED 116, VERIFIED 57, CONJECTURE 30, HEURISTIC 4, OPEN 3. Unmoved.

### The threading done: `junction_dichotomy` for a real dissection, `hvals` discharged

Two theorems (`CornerAnglePerm.lean`, twelve declarations, axiom-clean, `Erdos634.All` clean).

* `frontier_junction_is_vertex` — a frontier point carrying **no** straight angle is a vertex of some
  tile. A tile containing it has nonzero local angle there (`MarchFlank.localAngle_ne_zero_of_mem`);
  the `π` branch is excluded by hypothesis, the `0` branch by containment, and the `2π` branch
  because a tile's interior lies in the target's interior, which misses the frontier.
* **`congruentDissection_junction_dichotomy`** — `MarchRun.junction_dichotomy` for a real
  `CongruentDissection`, with `hvals` **derived rather than assumed**: the point is a tile vertex by
  the above, and `congruentDissection_localAngle_mem_at_corner` then gives the `2π`-free membership
  in the exact shape the lemma takes.

The `rem:marchobl` M-i row records this `hvals` as "suppliable for a real dissection though not yet
threaded into those call sites". **It is now threaded** for `junction_dichotomy`.

**What has not changed, and why no label moves.** The dichotomy still carries `hns` — that the
`π`-count at the junction is `0`, i.e. *no tile has a straight angle there*. That is not
bookkeeping: it is the crossing question at that point, and the earlier scan in this session already
identified `card = 0` hypotheses as exactly that. So `rem:marchobl`'s M-i row keeps its status; what
has been removed is one of its two unproved inputs, not both.

Census (`code/census.sh`): PROVED 116, VERIFIED 57, CONJECTURE 30, HEURISTIC 4, OPEN 3. Unmoved.

### `hvals` now discharged at every call site that carried it

Two more theorems (`CornerAnglePerm.lean`, fifteen declarations, axiom-clean, `Erdos634.All` clean).

* `vertex_of_localAngle_corner` — a tile presenting a corner-sized angle (not `0`, `π`, `2π`) at a
  point has that point among its vertices.
* **`congruentDissection_march_junction_real`** — `JunctionWedge.march_junction_real` for a real
  `CongruentDissection`, `hvals` derived. Here the discharge comes from the lemma's *own* `γ`-witness
  rather than from a `π`-count: a tile presenting `γ` has the point as a vertex, and
  `congruentDissection_localAngle_mem_at_corner` finishes.

With this and the previous entry, **every corpus site that carried the `hvals` hypothesis now has a
real-dissection version with it discharged**: `MarchRun.junction_dichotomy` (via
`congruentDissection_junction_dichotomy`) and `JunctionWedge.march_junction_real` (via this one).
That closes the gap `lem:anglecalc`'s row identified as a bug class in the 2026-08-30 audit — "every
one of those takes `hvals` as a *hypothesis*; grepped the corpus, nothing had ever discharged it for
a real dissection" — at general points, not only at target vertices.

**Still no label moves, and the reason differs between the two.** `congruentDissection_junction_
dichotomy` retains `hns` (no straight angle at the junction), which is the crossing question.
`congruentDissection_march_junction_real` retains the `γ`-witness `hiγ` and the wedge data
`hφ/hψ/hcorner`, which are configuration inputs about a march junction, not general facts. Neither
is bookkeeping; both must come from the march construction.

Census (`code/census.sh`): PROVED 116, VERIFIED 57, CONJECTURE 30, HEURISTIC 4, OPEN 3. Unmoved.

### `lem:census` piece 4a: the interior figure at a tile vertex is exactly the census's classification

`congruentDissection_interior_figure_at_corner` (`CornerAnglePerm.lean`, sixteen declarations,
axiom-clean, `Erdos634.All` clean).

At an interior point that is a vertex of some tile, **two of the four branches** of
`congruentDissection_interior_figure_cases` are impossible, and both are killed by tools built
earlier in this session:

* `u = 1` (a tile covers the point) — excluded by `congruentDissection_localAngle_mem_at_corner`:
  every tile's angle there lies in `{α, β, γ, π, 0}`, and `2π` is none of those.
* `s = 2` (two straight angles) — excluded by `RouteOne.two_through_excludes_mem`: two straight
  angles exhaust the `2π`, leaving no room for the tile that owns the vertex — and that tile is not
  itself a straight-angle tile, since `Tri.localAngle_vertex` and `congruent_corner_angles` make its
  angle there one of `α, β, γ`, each `≠ π`.

What survives is exactly the census's own list: a straight figure `{3α,2β}` or `{α,β,γ}` (`n₂`, `n₁`),
or one of the four interior figures `{6α,4β}`, `{4α,3β,γ}`, `{2α,2β,2γ}`, `{β,3γ}` (`v₄, v₃, v₂, v₁`).

**Remaining for piece 4:** the same classification at the *frontier* points of `cornerPts` (target
corners via `base_corner_counts`/`apex_counts`, other frontier points via `boundary_figure_cases`),
then the partition of `cornerPts` into the eight classes and evaluation of the multiplicity sum on
each. `lem:census` has **not** flipped; label stays PROVED.

Census (`code/census.sh`): PROVED 116, VERIFIED 57, CONJECTURE 30, HEURISTIC 4, OPEN 3. Unmoved.

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
| C `cor:basedi2e` | The base trichotomy and dichotomy without separation | `base_dichotomy_thick`, `no_extra_column_of_f_gt_two_e` |
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
| M `cor:elevenm` | `1 ∉ S`, `2, 3 ∈ S` for `(e,f) = (1,2)`, plus primitivity and the `N=11m²` consequence | `Tiling44Bridge.dissection`, `Tiling99Bridge.dissection`, `ElevenMBridge.exists_dissection_11_mul_sq` | PROVED — **corrected 2026-09-02: item (c) below was already done, this row was stale.** `2 ∈ S` and `3 ∈ S` are genuine `CongruentDissection`s (`Tiling44Bridge.dissection`, `Tiling99Bridge.dissection`), and the `N=11m²` consequence for `m` divisible by 2 or 3 is `ElevenMBridge.exists_dissection_11_mul_sq` (commit `587be94`, an earlier session — `lake build Erdos634.ElevenMBridge` confirmed clean 2026-09-02, this row's blocker text just hadn't been updated to reflect it). **Still missing, two things**: (a) `1 ∉ S` — the 135-node engine exhaustion, a negative claim this positive-witness machinery cannot touch; (b) primitivity — "neither the 44- nor 99-tiling arises from `thm:ladder` applied to a smaller member", an extra non-arising claim, not mere existence. Do not flip until both land. |
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
| O `lem:ccornerside` | a `c`-corner carries a side `a`-edge, so `1 ≤ p ≤ (f−1)/e` | `TilePlacement.c_corner_side_a`, `.a_corner_side_c`, `.p_bounds`, `.p_le_of_bounds`, `SideNoB.side_quantized`, `SidePRange.side_p_range` | PROVED — the flank implication and the parameter bounds are both VERIFIED. The one step between them is not: that a side's chain edges are its walk counts, so that an `a`-edge on the side makes `P' > 0`. **Arithmetic core closed 2026-09-08**: `SidePRange.side_p_range` (new) derives the level equation and the full bound `1≤p≤(f-1)/e` directly from `P>0` plus the raw walk (composing the just-landed `lem:sidequant` with `p_le_of_bounds`) — everything the paper's proof does *after* asserting `P'>0`. **Still missing**: connecting a real corner tile's forced `a`-edge (`c_corner_side_a`, a single-triangle fact) to `P>0` for an *actual* `CongruentDissection`'s side walk. **Found 2026-09-08**: `SideWalk.side_walk_of_dissection` (pre-existing) already IS the abstract-to-real bridge — for any real dissection with a discharged geometric setup (`g,c,dir,hker,hwall,hbase,hline,hface,hthird,hiso,hscalene`), it gives the real walk with genuine counts. It has never been instantiated anywhere in the corpus (confirmed by grep — zero call sites; its own docstring names this the same open gap `thm:walkstruct`/`cor:wallsf2e` share). **Three of ~7 hypotheses discharged, 2026-09-08**: `Tiling44Scalene.tiling44_model_scalene` gives `hscalene` (side lengths `16,24,32`, pairwise distinct). `Tiling44WallSetup.lean` picks the concrete wall line — the equal side from `(176,0)` to the apex `(88,24√15)` (target vertices confirmed exact by `decide`), `gWall(x,y)=24√15x+88y` its defining functional, `dirWall` the normalized direction along it — and discharges `hker` (the two functionals' gradients form a basis, determinant `16384≠0`) and `hwall` (the whole target satisfies `gWall≤4224√15`, via `Tri.carrier_subset_halfplane_affine`, the same pattern this session's collar work used throughout). **Six of ~7 hypotheses now discharged, 2026-09-08, later**: `hbase` (the wall segment is exactly the equal side's own edge, hence on the frontier, via the pre-existing general `SideWall.edge_subset_frontier`), `hline` (`gWall` equals `4224√15` on the whole segment, direct from agreement at both endpoints plus affineness), and `hface` (any target point attaining `gWall`'s max lies on the segment — via the pre-existing general `SupportFace.mem_convexHull_max`, a convex-hull point attaining a linear functional's bound is a combination of only the vertices that also attain it, and here only `pts 1`/`pts 2` do). **`hiso` also closed, 2026-09-08, later still**: `hiso_wall` — any two points on `gWall=4224√15` have their difference forced into `gWall`'s kernel (the wall's own direction, length exactly `128`), and `dirWall`'s `/128` normalization makes `dist p q = |dirWall p − dirWall q|` exactly (confirmed by direct coordinate computation, both quantities equal `16/11` times the raw `x`-coordinate difference). **Only `hthird` remains**, and its first piece is built, 2026-09-08, later still: `gWallZ`/`gWallZ_correct` transfer `gWall`'s value to exact `ℤ[√15]` arithmetic (matching how every other check in this project — `Tiling44.dist2`, `.area2` — works; sanity-checked against the known apex vertex), the bridge needed to apply `Z15Real.toR_ne_zero_of_sq_ne` (pre-existing) per concrete tile. **`hthird`'s arithmetic core closed, 2026-09-08, later still**: `all_hthird_ok` — decide-checked across ALL 44 of `Tiling44`'s tiles (the same whole-family `decide` pattern this project's (C1)–(C4) checks already use): every wall-edge tile's third vertex genuinely satisfies `toR_ne_zero_of_sq_ne`'s hypothesis. Confirms the geometric fact is true, not just plausible. **Backward-direction dichotomy closed, 2026-09-09**: `vertexDichotomyOK`/`all_vertex_dichotomy_ok` (decide-checked over all 44 tiles) — every vertex's `ℤ[√15]` value either IS the wall value `(0,4224)` exactly or is provably off it (the `z.1²≠15z.2²` test). Combined with `gWallZ_correct` this gives `g_eq_iff_wallVal`: the real biconditional `gWall(vertex)=4224√15 ↔ wallVal(vertex)=(0,4224)`, for every vertex of every tile — the missing piece to translate between the real-valued `WallEdge`/`hthird` hypotheses `side_walk_of_dissection` needs and the Bool-valued `isWallEdge`/`all_hthird_ok` facts already proven. **`hthird_wall` closed, 2026-09-09, later**: `Tiling44WallFinal.hthird_wall` translates `all_hthird_ok` (the Bool, `Tiling44.tiles`-indexed fact) into `side_walk_of_dissection`'s exact real-valued, `BaseChain.wallList`-indexed `hthird` shape, via `g_eq_iff_wallVal` and the definitional equality `dissection.tile p.1 = pieceTri ht`. All seven of `side_walk_of_dissection`'s hypotheses (`hker`,`hwall`,`hbase`,`hline`,`hface`,`hthird`,`hiso`) plus `hscalene` are now discharged. **`side_walk_of_dissection` actually called, 2026-09-09, later still**: `Tiling44EqualSideWalk.equal_side_walk` — the first real instantiation anywhere in the corpus, giving `∃ Pc Qc Rc, dist(pts1,pts2) = Pc·s₀+Qc·s₁+Rc·s₂` for `Tiling44Bridge.dissection`'s actual equal side (target's edge from `(176,0)` to the apex). **Still missing, and the only thing left**: `Pc>0` (or whichever count matches the corner tile's forced `a`-edge) is not part of `equal_side_walk`'s conclusion — `∃` gives existence of *some* nonneg counts, not that the specific corner-forced one is positive. Closing this needs `TilePlacement.c_corner_side_a` (a real corner tile has a side `a`-edge) connected to `WallEndpoints.chain_starts_at_a` (the chain's first edge starts at the corner) to force the matching count `>0`, then `SidePRange.side_p_range` applies. **Corner tile identified, 2026-09-09, later still**: `Tiling44CornerTile.lean` — `Tiling44.tiles[13]` is the actual tile sitting at `targetTri.pts 1 = (176,0)` (the wall's own start point), decide-checked. Its two vertex-1-incident edges have squared lengths `256=16²` and `1024=32²`, never `576=24²` — the `b`-side is not incident to this corner at all, matching the paper's own `c`-corner structure. **`side_walk_pos1_of_dissection` built, 2026-09-09, later still**: `SideWalk.side_walk_pos0_of_dissection`/`.side_walk_pos1_of_dissection` (new, general — not specific to any one target) generalize `side_walk_of_dissection`: given a witness wall edge whose length matches a named model side, the corresponding walk count is `≥1`, not just that some count exists (via `chain_endpoints`'s `hsurj` locating the witness among the enumerated wall edges, then `ChainWalk.count_pos`). Applied to `Tiling44Bridge.dissection`'s equal side with `tiles[13]`'s edge as witness: `Tiling44EqualSideWalkPos.equal_side_walk_pos` gives `Qc≥1`. **IMPORTANT CORRECTION, 2026-09-09, same iteration**: checked against the paper text directly (`erdos-634-obstructions.tex:957-966`) — `lem:ccornerside` is a statement about the **general base-β family** (`(e,f)` a base-β pair, "the base corner angle is `β`"), not about any single fixed target. `Tiling44Bridge`'s target is the **isosceles `16-16-22` triangle** (`thm:44`'s own family, a different geometric object entirely — no base-β angle `β`, no `(e,f)` parametrization). So `equal_side_walk_pos` is a genuine worked example of the abstract machinery, not itself part of `lem:ccornerside`'s proof — closing the general lemma needs a real-coordinate realization of an actual base-β `(e,f)` target, which **does not exist yet in this project** (confirmed by search; `SideWalk.lean`'s own docstring for `int_walk_of_dissection` already flagged this same gap). The general, reusable tools (`side_walk_pos0/1_of_dissection`, `SidePRange.side_p_range`) ARE real progress; the specific application to Tiling44 is not. Landed in `Tiling44WallSetup.lean` / `Tiling44WallFinal.lean` / `Tiling44EqualSideWalk.lean` / `Tiling44CornerTile.lean` / `SideWalk.lean` / `Tiling44EqualSideWalkPos.lean`. |
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
| C `lem:basedi` | the thick base dichotomy | `base_dichotomy_thick` | PROVED — the arithmetic is VERIFIED; it consumes `prop:gammatrap`, VERIFIED. **Corrected 2026-09-02**: same fix as `thm:e1reduce`'s row — what blocks this is a concrete `CongruentDissection` witness (structural blocker 1, the placement layer), not mere bookkeeping |
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
| C `prop:closepaircolumns` | the extra base columns at a close pair | `close_pair_column`, `close_pair_column_unique`, `one_column_per_k` | PROVED — the column arithmetic is VERIFIED; 'a base column of a tiling' has no Lean definition |
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
| `cor:basedi2e` | blocked | the base decompositions are of a *real* tiling's base, and the narrowing is the `γ`-trap (`prop:gammatrap`, VERIFIED). **Corrected 2026-09-02**: same fix as `thm:e1reduce`'s row — blocked on a concrete `CongruentDissection` witness (structural blocker 1), not mere bookkeeping |
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

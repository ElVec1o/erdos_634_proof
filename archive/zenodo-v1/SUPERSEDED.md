# 🔴 SUPERSEDED — do not cite, do not build on

This directory is the **earlier Zenodo / referee package** for Erdős #634, preserved verbatim for
provenance. It is **not** the current state of the project. For that, see `STATUS_TABLE.md` and
`paper/` at the top level of the `634` folder.

## What is wrong with it

### `proof/phi-invariant-proof.md` — contains a false claim

Its closing section states:

> "Therefore **no prime ≡ 3 (mod 4) is a number of congruent triangles tiling a triangle** — the
> folklore conjecture, and the open part of Erdős #634, is resolved."

**This is false.** The mathematics *original to that note* — the Φ-invariant, the cancellation
lemma, the tile-value lemma, and the isosceles `2π/3` obstruction — is sound and survives verbatim
in the current paper. The error is in the **assembly**: it disposes of the `3α+2β = π` family "by
standing theorems", and those theorems are defective.

We have since proved:

- **Beeson, *Triangle Tiling III*, Theorem 14 is FALSE.** Its divisibility `g ∣ M` is refuted by an
  explicit 99-tiling of the `(24,24,33)` triangle by `(2,3,4)` tiles, constructed and verified in
  exact `ℚ(√15)` arithmetic. The certificate is at `engine/tilings/tiling_99_isobeta_24_24_33.txt`.
- **Theorems 18, 19 and 20 have unsound proofs**, and **Lemma 8's squarefree half is false**
  (counterexample tile `(4,15,16)`), and **Lemma 6 is false as quoted**.

With those removed, the base-`β` sub-branch of `3α+2β = π` is **open**. It is exactly the primes
`≡ 11 (mod 12)`. Forty-two of them lie below 1000; only six are settled, all by exhaustive computer
search, none by theorem.

### `proof/N19-citable-note.md` — conclusion correct, justification since repaired

This note is more careful and explicitly says the general conjecture "remains open". Its
conclusion — **no triangle can be cut into 19 congruent triangles** — **is still correct** and is
the headline of the current paper. But it routed the `3α+2β = π` row through the same defective
Beeson citations. The current paper repairs this: `19 ≡ 7 (mod 12)`, so 19 is not a base-`β`
candidate at all, and the remaining `3α+2β` sub-branches are excluded by our own machine-checked
propositions that *replace* Beeson's unsound Theorems 18 and 20.

### `proof/reviewers-and-journals.md`

Submission-process notes from that period. If anyone was contacted on the basis of the
"conjecture resolved" claim, **that claim needs retracting**. The defensible statement now is:

> No prime `≡ 7 (mod 12)` is a tile count — in particular not 19. The class `11 (mod 12)` is open.
> Five defects in Beeson's *Triangle Tiling III*, one of them refuted by an explicit tiling.

## What here is still of value

- `code/tiler2.rs`, `code/tiling_search.rs` — early Rust search code, superseded by
  `engine/cengine_iso.cpp` but kept in case the Rust route is revived.
- `code/phi_invariant.py`, `verify_vertex_types.py`, `shape_completeness.py`,
  `n19_final_check.py`, `n19_pi3_tile.py`, `apex_obstruction.py`,
  `gamma_orientation_closure.py` — the original verification scripts.
- `Erdos634.lean` (102 lines) — the ancestor of the current 697-line `lean/Erdos634.lean`. The
  theorem `k_not_dvd_sum_sub` cited in the Φ-note is still present in the current file.
- `paper/erdos-634.md` — the markdown ancestor of the current LaTeX paper.
- `ZENODO.md` — the DOI-minting procedure, still accurate as a procedure.

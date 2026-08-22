import Mathlib.Tactic

/-!
# Order forcing on the equal side (Erdős #634, base-β branch)

Arithmetic cores of the two order results of the crux ledger, general in `(e,f)`:

* **Adjacency label bound.** A tile's three edge labels are `{L−2, L, L+1}` (direct chirality) or
  `{L−1, L, L+2}` (mirrored). Two adjacent tiles share an edge, hence a label, so their tile labels
  differ by at most `4`. The bound is attained (mixed chirality), matching the measured maximum
  `|ΔL| = 4` on the true adjacency graphs of `N44C`, the `99`-tiling and `T77`.

* **A-run rigidity.** At a straight interior junction the vertex figure solves
  `n_α + 2n_γ = 3`, `n_β + n_γ = 2` (the encoding `α ↦ (1,0)`, `β ↦ (0,1)`, `γ = 2α+β`,
  `π = 3α+2β`), so the figure is `{α,α,α,β,β}` or `{γ,α,β}` — in particular at most one `γ`.
  An a-edge's flanking angles are `β` and `γ` (`a` is opposite `α`), so consecutive a-tiles cannot
  both present `γ` at their shared junction: "γ at the far end" is an absorbing orientation, and the
  orientation word of an a-run is monotone (`β`-far tiles first, then `γ`-far tiles).
-/

namespace Erdos634.OrderForcing

/-! ## The adjacency label bound -/

/-- Edge-label offsets of a tile: direct chirality carries `L−2, L, L+1`, mirrored `L−1, L, L+2`. -/
def offsets (mirrored : Bool) : List ℤ := if mirrored then [-1, 0, 2] else [-2, 0, 1]

theorem offset_range {m : Bool} {o : ℤ} (h : o ∈ offsets m) : -2 ≤ o ∧ o ≤ 2 := by
  cases m <;> simp [offsets] at h <;> rcases h with h | h | h <;> omega

/-- **Adjacent tiles' labels differ by at most 4.** The shared edge has a single label, presented
with offset `o` by one tile and `o'` by the other, so `L + o = L' + o'`. -/
theorem adjacent_label_bound {L L' o o' : ℤ} {m m' : Bool}
    (ho : o ∈ offsets m) (ho' : o' ∈ offsets m')
    (hshare : L + o = L' + o') : |L - L'| ≤ 4 := by
  have h1 := offset_range ho
  have h2 := offset_range ho'
  rw [abs_le]
  omega

/-- The bound is attained: a direct tile at label `4` and a mirrored tile at label `0` can share
the edge of label `2`. -/
theorem adjacent_label_bound_sharp :
    ∃ (L L' o o' : ℤ), o ∈ offsets false ∧ o' ∈ offsets true ∧ L + o = L' + o' ∧ L - L' = 4 :=
  ⟨4, 0, -2, 2, by simp [offsets], by simp [offsets], by norm_num, by norm_num⟩

/-! ## A-run rigidity -/

/-- **The straight-junction dichotomy.** The vertex system at a straight angle has exactly two
solutions: `{α,α,α,β,β}` and `{γ,α,β}`. -/
theorem straight_junction_cases (na nb ng : ℕ) (h1 : na + 2 * ng = 3) (h2 : nb + ng = 2) :
    (na = 3 ∧ nb = 2 ∧ ng = 0) ∨ (na = 1 ∧ nb = 1 ∧ ng = 1) := by omega

/-- At most one `γ` meets a straight junction. -/
theorem straight_junction_gamma_bound (na nb ng : ℕ)
    (h1 : na + 2 * ng = 3) (h2 : nb + ng = 2) : ng ≤ 1 := by omega

/-- **A-run rigidity.** Model an a-run of length `k` by `orient : ℕ → Bool`, where `orient i = true`
means tile `i` places its `γ` at the far end (in run direction). The γ-trap forbids consecutive
tiles from presenting `γ` at the shared junction, which is exactly the absorption hypothesis: once
`γ`-far, the next tile is `γ`-far. Conclusion: `γ`-far propagates to the end of the run, so the
orientation word is `β`-far${}^j$ `γ`-far${}^{k-j}$ for some threshold `j`. -/
theorem gamma_far_absorbing (k : ℕ) (orient : ℕ → Bool)
    (habs : ∀ i, i + 1 < k → orient i = true → orient (i + 1) = true) :
    ∀ i j, i ≤ j → j < k → orient i = true → orient j = true := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => intro _ hi; exact hi
  | succ n hn ih =>
      intro hjk hi
      exact habs n hjk (ih (Nat.lt_of_succ_lt hjk) hi)

/-! ## The full-vertex classification, via the label identities

Writing the real-angle identities `α = 2γ − π`, `β = −3γ + 2π`, a vertex figure with counts
`(n_α, n_β, n_γ)` summing to `2π` gives `ℓ·γ + (2n_β − n_α)π = 2π` with `ℓ = 2n_α − 3n_β + n_γ`;
irrationality of `γ/π` forces `ℓ = 0` and `2n_β − n_α = 2`. These two linear equations are
equivalent to the classical system `n_α + 2n_γ = 6`, `n_β + n_γ = 4`, and have exactly four
solutions: the four interior vertex figures. -/

/-- The label form of the vertex equations is equivalent to the classical form. -/
theorem full_vertex_equiv (na nb ng : ℕ) :
    (na + 2 * ng = 6 ∧ nb + ng = 4) ↔ (2 * na + ng = 3 * nb ∧ na + 2 = 2 * nb) := by omega

/-- **The four interior vertex figures**: `{β,3γ}`, `{2α,2β,2γ}`, `{4α,3β,γ}`, `{6α,4β}`. -/
theorem full_vertex_cases (na nb ng : ℕ) (h1 : 2 * na + ng = 3 * nb) (h2 : na + 2 = 2 * nb) :
    (na = 0 ∧ nb = 1 ∧ ng = 3) ∨ (na = 2 ∧ nb = 2 ∧ ng = 2) ∨
    (na = 4 ∧ nb = 3 ∧ ng = 1) ∨ (na = 6 ∧ nb = 4 ∧ ng = 0) := by omega

/-! ## The chained run-label theorem

The side dictionary (verified exactly for the members (1,2), (1,3), (1,4), (2,3), (3,4); the
correspondence is fixed by planar orientation, hence member-independent):

| side edge | γ/α position | chirality | tile label |
|---|---|---|---|
| `a` | γ at upper end | mirrored | **−2** |
| `a` | γ at lower end | direct | **−4** |
| `c` | α at upper end | direct | **−1** |
| `c` | α at lower end | mirrored | **−5** |

Composing with `gamma_far_absorbing`: in a maximal a-run the γ-upper orientation is absorbing, so
the label word of the run is `(−4)^j (−2)^{k−j}` — all direct tiles precede all mirrored ones. -/

/-- **Run label word.** With labels assigned by the dictionary (`γ`-upper ↦ −2, `γ`-lower ↦ −4),
absorption forces the label word of an a-run to be `(−4)^j (−2)^{k−j}`: once a tile carries −2,
every later tile in the run carries −2. -/
theorem run_label_word (k : ℕ) (orient : ℕ → Bool)
    (habs : ∀ i, i + 1 < k → orient i = true → orient (i + 1) = true)
    (label : ℕ → ℤ) (hlab : ∀ i, label i = if orient i then -2 else -4) :
    ∀ i j, i ≤ j → j < k → label i = -2 → label j = -2 := by
  intro i j hij hjk hi
  have hoi : orient i = true := by
    cases hcase : orient i with
    | false =>
        exfalso
        rw [hlab i, hcase] at hi
        norm_num at hi
    | true => rfl
  have := gamma_far_absorbing k orient habs i j hij hjk hoi
  simp [hlab j, this]

/-! ## The first-run kill

At the junction `J` between the corner tile's side flank (a `c`-edge) and the first a-run, three
corners are already pinned: the corner tile contributes `α` (its `c`-edge's upper end), the partner
tile — forced onto the far side of the corner tile's `b`-edge by `PentagonLemma.partner_unique`,
the chord being boundary-anchored at both ends — contributes `α` or `γ` (the ends of a `b`-edge),
and the first a-tile contributes `γ` if it is direct. No straight-angle figure accommodates
`{α, γ}` plus another corner from `{α, γ}`: -/

/-- **First-run kill.** A straight junction hosting one `α`, one `γ`, and a further corner that is
`α` or `γ` is impossible. Hence the first a-tile after the corner block is mirrored, and by
`gamma_far_absorbing` the entire first run is mirrored. -/
theorem first_run_kill (na nb ng : ℕ) (h1 : na + 2 * ng = 3) (h2 : nb + ng = 2)
    (h : (2 ≤ na ∧ 1 ≤ ng) ∨ (1 ≤ na ∧ 2 ≤ ng)) : False := by omega

/-! ## The top-junction kill and `p ≤ f − 3`

At a junction where an a-run ends against the final c-edge with the run's last tile mirrored, the
`{γ,α,β}` filler's edge along the top tile's a-ray is `c = f²` (mirrored filler) or `b = f²−1`
(direct filler), with endpoint `J + (f², 0)` resp. `J + (f²−1, 0)`. The outside-test against the
right side reduces exactly (companion, `lem:topjunction`) to the signs of

    f³ − 3f² + 1        (mirrored filler outside  ⟺  > 0  ⟺  f ≥ 3),
    f³ − 3f² − f + 1    (direct filler outside    ⟺  > 0  ⟺  f ≥ 4).

The first polynomial is the thin/thick discriminant of the branch. Consequences: for `f ≥ 4` a
final c-block of length 1 with mirrored last tile is impossible; `p = f−2` forces c-count 2, hence
the single-run word `c a^{f(f−2)} c`, all-mirrored by the first-run lemma, final block 1 — dead. So
`p ≤ f − 3` for `f ≥ 4`, and at `f = 3` the filler is forced direct. -/

/-- The mirrored-filler discriminant is positive from `f = 3`. -/
theorem mirrored_filler_outside {f : ℕ} (hf : 3 ≤ f) : 3 * f^2 < f^3 + 1 := by nlinarith

/-- The direct-filler discriminant is positive from `f = 4`. -/
theorem direct_filler_outside {f : ℕ} (hf : 4 ≤ f) : 3 * f^2 + f < f^3 + 1 := by nlinarith

/-- With two c-edges pinned at the ends, the a-edges form a single run: every position strictly
between the ends is an a-edge. -/
theorem two_c_single_run (n : ℕ) (w : ℕ → Bool)
    (hc : ∀ i, i < n → (w i = false ↔ (i = 0 ∨ i = n - 1)))
    {k : ℕ} (h0 : 0 < k) (hk : k < n - 1) : w k = true := by
  have := hc k (by omega)
  rcases hcase : w k with _ | _
  · have := (this).mp hcase
    omega
  · rfl

/-- **`p ≤ f − 3` for `f ≥ 4`**: the c-count is `f − p`, and `p = f − 2` (c-count 2) is dead by the
single-run + top-junction argument, so the c-count is at least 3. -/
theorem p_le_f_sub_three {f p R : ℕ} (hR : R + p = f) (h3 : 3 ≤ R) : p ≤ f - 3 := by omega

/-! ## Wedge classifications consumed by the (1,3) kill

The cascade's "the rest of the figure is exactly …" steps, as representation facts. The one
non-unique case, `π − β − α`, is exactly where the Rule-6 review found the hole; its second
representation `{2α, β}` is killed by the 2γ-overflow at the next base point. -/

/-- `π − γ − α = β`, uniquely. -/
theorem beta_slot_unique (na nb ng : ℕ) (h1 : na + 2 * ng = 0) (h2 : nb + ng = 1) :
    na = 0 ∧ nb = 1 ∧ ng = 0 := by omega

/-- `π − γ − β = α`, uniquely. -/
theorem alpha_slot_unique (na nb ng : ℕ) (h1 : na + 2 * ng = 1) (h2 : nb + ng = 0) :
    na = 1 ∧ nb = 0 ∧ ng = 0 := by omega

/-- `π − β − α` has exactly two representations: `{γ}` and `{2α, β}`. -/
theorem wedge_gamma_cases (na nb ng : ℕ) (h1 : na + 2 * ng = 2) (h2 : nb + ng = 1) :
    (na = 0 ∧ nb = 0 ∧ ng = 1) ∨ (na = 2 ∧ nb = 1 ∧ ng = 0) := by omega

/-- **Through-edge exclusivity.** At an interior point of a tile edge, each side of the line totals
`π`. A tile edge passing straight through contributes the whole `π` on its side, so that side admits
NO other corner: in the encoding, `(na + 2ng) + 3 = 3` and `(nb + ng) + 2 = 2` force all counts to
zero. An edge can cross a vertex-carrying side only if that side is empty. -/
theorem through_edge_exclusive (na nb ng : ℕ)
    (h1 : na + 2 * ng + 3 = 3) (h2 : nb + ng + 2 = 2) :
    na = 0 ∧ nb = 0 ∧ ng = 0 := by omega

/-- The three semigroup gaps of `⟨4,15,16⟩` consumed by the `(1,4)` double-`c` kill. -/
theorem gaps_4_15_16 :
    (∀ x y z : ℕ, x * 4 + y * 15 + z * 16 ≠ 11) ∧
    (∀ x y z : ℕ, x * 4 + y * 15 + z * 16 ≠ 14) ∧
    (∀ x y z : ℕ, x * 4 + y * 15 + z * 16 ≠ 26) := by
  refine ⟨fun x y z => ?_, fun x y z => ?_, fun x y z => ?_⟩ <;> omega

/-- The right-side line-total at `(1,4)`: the only partition of `30 = 2b` is `15 + 15`, so the far
side of the doubled b-line splits exactly at the mid-junction into two partner b-edges. -/
theorem partition_30 (x y z : ℕ) (h : x * 4 + y * 15 + z * 16 = 30) :
    x = 0 ∧ y = 2 ∧ z = 0 := by omega

/-! ## The three lemma cores of the general e = 1 cascade -/

/-- **L1 reach.** The `k`-th chord's upper end sits at offset `kf` of the second side tile's
horizontal `c`-edge; blocking needs `kf < f²`, and the collision position `q ≤ f` is reached at
step `q − 2 ≤ f − 2`, so every needed chord is blocked. -/
theorem cascade_reaches {f q : ℕ} (h3 : 3 ≤ q) (hqf : q ≤ f) : (q - 2) * f < f * f := by
  have h1 : q - 2 < f := by omega
  have h2 : 0 < f := by omega
  exact (Nat.mul_lt_mul_right h2).mpr h1

/-- **L3 core: the reversal trichotomy.** Every admissible base word — `b` at position
`bp ∈ [3,f]`, `c` at position `cp ∈ [2,f+1]`, `bp ≠ cp` — has `b` before `c` (the L1 class), or
`c` immediately before `b` (the L2 class), or `c` before `b` with a gap, in which case the REVERSED
word's `b`-position `f+3−bp` again lies in `[3,f]` and precedes its `c`: the reversal is in the L1
class, and the mirrored cascade kills it. -/
theorem reversal_covers {f bp cp : ℕ} (hf : 3 ≤ f) (hb3 : 3 ≤ bp) (hbf : bp ≤ f)
    (hc2 : 2 ≤ cp) (hcf : cp ≤ f + 1) (hne : bp ≠ cp) :
    bp < cp ∨ cp + 1 = bp ∨
    (cp + 1 < bp ∧ 3 ≤ f + 3 - bp ∧ f + 3 - bp ≤ f ∧ f + 3 - bp < f + 3 - cp) := by omega

/-- **The all-`c` right side forcing, general.** The doubled `b`-line's far side partitions
`2b = 2f²−2` into whole edges; the unique decomposition is `b + b`, so the split falls at the
mid-junction and the two `b`-partners exist. -/
theorem partition_2b {f x y z : ℕ} (hf : 3 ≤ f)
    (h : x * f + y * (f * f - 1) + z * (f * f) = 2 * (f * f) - 2) :
    x = 0 ∧ y = 2 ∧ z = 0 := by
  have hff : 9 ≤ f * f := by nlinarith
  have hz : z ≤ 1 := by
    by_contra hz2
    have h1 : 2 ≤ z := by omega
    have h2 : 2 * (f * f) ≤ z * (f * f) := Nat.mul_le_mul_right _ h1
    omega
  have hfd2 : ¬ f ∣ 2 := fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega
  have hfd1 : ¬ f ∣ 1 := fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega
  interval_cases z
  · have hy : y ≤ 2 := by
      by_contra hy3
      have h1 : 3 ≤ y := by omega
      have h2 : 3 * (f * f - 1) ≤ y * (f * f - 1) := Nat.mul_le_mul_right _ h1
      omega
    interval_cases y
    · exfalso
      have h2 : f ∣ x * f := ⟨x, Nat.mul_comm x f⟩
      have h3 : f ∣ 2 * (f * f) := ⟨2 * f, by ring⟩
      have h5 : 2 * (f * f) - x * f = 2 := by omega
      have h4 : f ∣ 2 := by have h6 := Nat.dvd_sub h3 h2; rwa [h5] at h6
      exact hfd2 h4
    · exfalso
      have h2 : f ∣ x * f := ⟨x, Nat.mul_comm x f⟩
      have h3 : f ∣ f * f := ⟨f, rfl⟩
      have h5 : f * f - x * f = 1 := by omega
      have h4 : f ∣ 1 := by have h6 := Nat.dvd_sub h3 h2; rwa [h5] at h6
      exact hfd1 h4
    · have hx : x * f = 0 := by omega
      rcases Nat.mul_eq_zero.mp hx with h0 | h0
      · exact ⟨h0, rfl, rfl⟩
      · omega
  · exfalso
    have hy : y ≤ 1 := by
      by_contra hy2
      have h1 : 2 ≤ y := by omega
      have h2 : 2 * (f * f - 1) ≤ y * (f * f - 1) := Nat.mul_le_mul_right _ h1
      omega
    interval_cases y
    · have h2 : f ∣ x * f := ⟨x, Nat.mul_comm x f⟩
      have h3 : f ∣ f * f := ⟨f, rfl⟩
      have h5 : f * f - x * f = 2 := by omega
      have h4 : f ∣ 2 := by have h6 := Nat.dvd_sub h3 h2; rwa [h5] at h6
      exact hfd2 h4
    · omega

/-- **The `j·b`-line partition, general depth.** For `1 ≤ j < f` the only decomposition of `j·b`
into whole edges is `j` copies of `b`: a fully-edged line of length `jb` splits into exactly `j`
`b`-partners. Applies wherever the line is known to be covered by whole edges on the relevant side; a
straddling tile voids the hypothesis, not the arithmetic. -/
theorem partition_jb {f j x y z : ℕ} (hf : 3 ≤ f) (hj1 : 1 ≤ j) (hjf : j < f)
    (h : x * f + y * (f * f - 1) + z * (f * f) = j * (f * f - 1)) :
    x = 0 ∧ y = j ∧ z = 0 := by
  have hff : 9 ≤ f * f := by nlinarith
  have hy : y ≤ j := by
    by_contra hyj
    have h1 : j + 1 ≤ y := by omega
    have h2 : (j + 1) * (f * f - 1) ≤ y * (f * f - 1) := Nat.mul_le_mul_right _ h1
    have h3 : (j + 1) * (f * f - 1) = j * (f * f - 1) + (f * f - 1) := by
      rw [Nat.add_mul, Nat.one_mul]
    omega
  have hexp : y * (f * f - 1) + (j - y) * (f * f - 1) = j * (f * f - 1) := by
    rw [← Nat.add_mul]; congr 1; omega
  have hxz : x * f + z * (f * f) = (j - y) * (f * f - 1) := by omega
  have hdvd : f ∣ (j - y) * (f * f - 1) := by
    rw [← hxz]
    exact Nat.dvd_add ⟨x, Nat.mul_comm x f⟩ ⟨z * f, by ring⟩
  have hsucc : (j - y) * (f * f) = (j - y) * (f * f - 1) + (j - y) := by
    obtain ⟨B, hB⟩ : ∃ B, f * f = B + 1 := ⟨f * f - 1, by omega⟩
    rw [hB, Nat.add_sub_cancel, Nat.mul_add, Nat.mul_one]
  have hdvd2 : f ∣ (j - y) := by
    have h4 : f ∣ (j - y) * (f * f) := ⟨(j - y) * f, by ring⟩
    have h5 : (j - y) * (f * f) - (j - y) * (f * f - 1) = j - y := by omega
    have h6 := Nat.dvd_sub h4 hdvd
    rwa [h5] at h6
  have hyj : y = j := by
    rcases Nat.eq_zero_or_pos (j - y) with h0 | h0
    · omega
    · exact absurd (Nat.le_of_dvd h0 hdvd2) (by omega)
  subst hyj
  have h8 : (y - y) * (f * f - 1) = 0 := by rw [Nat.sub_self, Nat.zero_mul]
  have hx0 : x * f = 0 ∧ z * (f * f) = 0 := by omega
  rcases Nat.mul_eq_zero.mp hx0.1 with h0 | h0
  · rcases Nat.mul_eq_zero.mp hx0.2 with h1 | h1
    · exact ⟨h0, rfl, h1⟩
    · omega
  · omega

/-- **The south-cover gap.** In the row recursion, a row `f`-`a` fork lays a horizontal `c`-edge
whose south side starts with a forced `a` (the mate's top); the remainder `f² − f` admits NO edge
decomposition containing a `b` or a `c` — it is exactly `f − 1` more `a`-edges. -/
theorem south_cover {f x y z : ℕ} (hf : 3 ≤ f)
    (h : x * f + y * (f * f - 1) + z * (f * f) = f * f - f) :
    x = f - 1 ∧ y = 0 ∧ z = 0 := by
  have hff : 9 ≤ f * f := by nlinarith
  have hy : y = 0 := by
    by_contra hy1
    have h1 : 1 ≤ y := by omega
    have h2 : 1 * (f * f - 1) ≤ y * (f * f - 1) := Nat.mul_le_mul_right _ h1
    omega
  have hz : z = 0 := by
    by_contra hz1
    have h1 : 1 ≤ z := by omega
    have h2 : 1 * (f * f) ≤ z * (f * f) := Nat.mul_le_mul_right _ h1
    omega
  subst hy; subst hz
  have hx : x * f = f * f - f := by omega
  have hfe : (f - 1) * f + f = f * f := by
    obtain ⟨g, hg⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    subst hg
    simp only [Nat.add_sub_cancel]
    ring
  have : x * f = (f - 1) * f := by omega
  have hxf : x = f - 1 := Nat.eq_of_mul_eq_mul_right (by omega) this
  exact ⟨hxf, rfl, rfl⟩

/-- **Anchored straddle guard.** With the forced mate-top `a` anchoring the left end, a south
cover of a row `c`-edge cannot end in a partial edge: the residue `f² − f − t` with `0 < t < f`
admits no decomposition (no `b`, no `c`, and all-`a` forces `f ∣ t`). -/
theorem south_cover_straddle {f x y z t : ℕ} (hf : 3 ≤ f) (ht1 : 1 ≤ t) (htf : t < f)
    (h : x * f + y * (f * f - 1) + z * (f * f) + t = f * f - f) :
    False := by
  have hff : 9 ≤ f * f := by nlinarith
  have hy : y = 0 := by
    by_contra hy1
    have h1 : 1 ≤ y := by omega
    have h2 : 1 * (f * f - 1) ≤ y * (f * f - 1) := Nat.mul_le_mul_right _ h1
    omega
  have hz : z = 0 := by
    by_contra hz1
    have h1 : 1 ≤ z := by omega
    have h2 : 1 * (f * f) ≤ z * (f * f) := Nat.mul_le_mul_right _ h1
    omega
  subst hy; subst hz
  have hdvd : f ∣ t := by
    have h2 : f ∣ x * f := ⟨x, Nat.mul_comm x f⟩
    have h3 : f ∣ f * f := ⟨f, rfl⟩
    have h4 : f ∣ f := dvd_refl f
    have h5 : f * f - f - (x * f) = t := by omega
    have h6 := Nat.dvd_sub (Nat.dvd_sub h3 h4) h2
    rwa [h5] at h6
  exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)

/-- **The α-vertex gap.** A mirrored `a`-up tile on a row line has its `α`-vertex on the base at
abscissa `(m+3)f − 1/f`: integrality would give `n·f + 1 = K·f²`, forcing `f ∣ 1`. -/
theorem alpha_vertex_gap {f n K : ℕ} (hf : 2 ≤ f) (h : n * f + 1 = K * (f * f)) : False := by
  have h2 : f ∣ n * f := ⟨n, Nat.mul_comm n f⟩
  have h3 : f ∣ K * (f * f) := ⟨K * f, by ring⟩
  have h5 : K * (f * f) - n * f = 1 := by omega
  have h4 : f ∣ 1 := by have h6 := Nat.dvd_sub h3 h2; rwa [h5] at h6
  exact absurd (Nat.le_of_dvd (by norm_num) h4) (by omega)

/-- **The α-vertex gap, general form** (companion `lem:avgen`).  At a general member the mirrored
cover piece has its foot at `(k+3)a − e³/f`, so the foot is a lattice point only if `f² ∣ e²`, and
at row `1` it is a junction only if `f ∣ e³`.  Coprimality kills both: a modulus coprime to `e` that
divides a power of `e` is `1`, contradicting `f ≥ 2`.  So the mirrored placement is excluded at row
`1` for every member with `f ≥ 2`, with `e³` playing the role that `1` plays at `e = 1`.

This is the general counterpart of `alpha_vertex_gap`, which is the `e = 1` instance: there `e³ = 1`
and the condition degenerates to `f ∣ 1`. -/
theorem alpha_vertex_gap_gen {e f : ℕ} (hf : 2 ≤ f) (hco : Nat.Coprime e f) :
    ¬ (f * f ∣ e * e) ∧ ¬ (f ∣ e * e * e) := by
  have hfe : Nat.Coprime f e := hco.symm
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hff : f ∣ f * f := ⟨f, rfl⟩
    have h1 : f ∣ e * e := hff.trans h
    have := (hfe.mul_right hfe).eq_one_of_dvd h1
    omega
  · have := ((hfe.mul_right hfe).mul_right hfe).eq_one_of_dvd h
    omega

/-- **The anti-brick side.** The direct `γ`-right placement of an `a`-up tile has squared third
side `f⁴ − 2f² + 2`, which is no tile side: it misses `b²` by exactly `1`, `c²` by `2f² − 2`, and
`a²` by `(f²−1)(f²−2)`. -/
theorem anti_brick_side {f : ℕ} (hf : 2 ≤ f) :
    (f * f) * (f * f) - 2 * (f * f) + 2 ≠ f * f ∧
    (f * f) * (f * f) - 2 * (f * f) + 2 ≠ (f * f - 1) * (f * f - 1) ∧
    (f * f) * (f * f) - 2 * (f * f) + 2 ≠ (f * f) * (f * f) := by
  have hG : 4 ≤ f * f := by nlinarith
  obtain ⟨H, hH⟩ : ∃ H, f * f = H + 4 := ⟨f * f - 4, by omega⟩
  rw [hH]
  have e0 : (H + 4) * (H + 4) = 2 * (H + 4) + (H * H + 6 * H + 8) := by ring
  have e1 : (H + 4) * (H + 4) - 2 * (H + 4) + 2 = H * H + 6 * H + 10 := by omega
  have e2 : (H + 4 - 1) * (H + 4 - 1) = H * H + 6 * H + 9 := by
    have : H + 4 - 1 = H + 3 := by omega
    rw [this]; ring
  refine ⟨?_, ?_, ?_⟩ <;> rw [e1] <;> [skip; rw [e2]; rw [e0]] <;> omega

/-- **Label arithmetic for a tile flanked by labels −3 and 0.** Of the four chirality/flank
assignments exactly two close, at `L = −1` and `L = −2`. NOTE: this is not the justification for
the fork dichotomy — no single tile is adjacent to both the chord and the floor there (its angle
would be `α+β`). The dichotomy is derived instead from the forced east fan (companion
`lem:eastfan`); this lemma is retained as the label-arithmetic fact it is. -/
theorem fork_label_pin (L : ℤ) :
    ((L + 1 = -3 ∧ L - 2 = 0) ∨ (L - 2 = -3 ∧ L + 1 = 0) ∨
     (L - 1 = -3 ∧ L + 2 = 0) ∨ (L + 2 = -3 ∧ L - 1 = 0)) ↔ (L = -1 ∨ L = -2) := by omega

/-- **The east-cover gap (weapon W1).** A leak tile laying its `a` as first element of the east
cover of an `X`-cell's `b`-edge leaves `f² − 1 − f`, which admits no completion: no `b` or `c`
fits, and all-`a` needs `f ∣ f² − f − 1`, i.e. `f ∣ 1`. Kills the `b`-floor fills wherever the segment is
known to be covered by whole edges (e.g. below a tile edge). -/
theorem east_cover_gap {f x y z : ℕ} (hf : 3 ≤ f)
    (h : x * f + y * (f * f - 1) + z * (f * f) = f * f - 1 - f) : False := by
  have hff : 9 ≤ f * f := by nlinarith
  have hy : y = 0 := by
    by_contra hy1
    have h1 : 1 ≤ y := by omega
    have h2 : 1 * (f * f - 1) ≤ y * (f * f - 1) := Nat.mul_le_mul_right _ h1
    omega
  have hz : z = 0 := by
    by_contra hz1
    have h1 : 1 ≤ z := by omega
    have h2 : 1 * (f * f) ≤ z * (f * f) := Nat.mul_le_mul_right _ h1
    omega
  subst hy; subst hz
  simp only [Nat.zero_mul, Nat.add_zero] at h
  have hgf : f + 1 ≤ f * f := by nlinarith
  have hxf : x * f + f + 1 = f * f := by omega
  have h2 : f ∣ x * f := ⟨x, Nat.mul_comm x f⟩
  have h3 : f ∣ f * f := ⟨f, rfl⟩
  have h5 : f * f - x * f - f = 1 := by omega
  have h4 : f ∣ 1 := by
    have h6 := Nat.dvd_sub (Nat.dvd_sub h3 h2) (dvd_refl f)
    rwa [h5] at h6
  exact absurd (Nat.le_of_dvd (by norm_num) h4) (by omega)

/-- **The `2b − c` gap.** Laying a `c` along a chord of length `2b` leaves `f² − 2`, which is a
gap for `f ≥ 3`: it is below `b`, so only `a`'s could cover it, and `f ∤ f² − 2`. At `f = 2` it
equals `a`, which is exactly the coincidence the `(1,2)` tilings exploit. -/
theorem gap_2b_minus_c {f x y z : ℕ} (hf : 3 ≤ f)
    (h : x * f + y * (f * f - 1) + z * (f * f) = f * f - 2) : False := by
  have hff : 9 ≤ f * f := by nlinarith
  have hy : y = 0 := by
    by_contra hy1
    have h1 : 1 ≤ y := by omega
    have h2 : 1 * (f * f - 1) ≤ y * (f * f - 1) := Nat.mul_le_mul_right _ h1
    omega
  have hz : z = 0 := by
    by_contra hz1
    have h1 : 1 ≤ z := by omega
    have h2 : 1 * (f * f) ≤ z * (f * f) := Nat.mul_le_mul_right _ h1
    omega
  subst hy; subst hz
  simp only [Nat.zero_mul, Nat.add_zero] at h
  have hgf : 2 ≤ f * f := by nlinarith
  have h2 : f ∣ x * f := ⟨x, Nat.mul_comm x f⟩
  have h3 : f ∣ f * f := ⟨f, rfl⟩
  have h5 : f * f - x * f = 2 := by omega
  have h4 : f ∣ 2 := by have h6 := Nat.dvd_sub h3 h2; rwa [h5] at h6
  exact absurd (Nat.le_of_dvd (by norm_num) h4) (by omega)

/-- **The `2b − a` gap.** The third of the three runs left by the double-`c` configuration: when
the `β`-slot tile is direct its `a`-edge is laid first along the `2b` chord and the whole far side
must then partition `2b − a = 2f² − f − 2`. Stated subtraction-free, as `n + f + 2 = 2f²`.

Together with `east_cover_gap` (which is `b − a = f² − f − 1`) and `gap_2b_minus_c` (which is
`f² − 2`) this completes the arithmetic core of the double-`c` kill for **every** `f ≥ 3`. At
`f = 4` the three read `11`, `26`, `14` against `⟨4,15,16⟩`, which is the machine-checked instance
`gaps_4_15_16` used in the `(1,4)` argument; the point here is that the pattern is not special to
`f = 4`. At `f = 2` this run equals `4 = 2a` and the kill genuinely fails — which is exactly why
the `e = 1` reduction carries the hypothesis `f ≥ 3`. -/
theorem gap_2b_minus_a {f x y z : ℕ} (hf : 3 ≤ f)
    (h : x * f + y * (f * f - 1) + z * (f * f) + f + 2 = 2 * (f * f)) : False := by
  have hff : 9 ≤ f * f := by nlinarith
  -- Size bounds: three `b`'s already overshoot, and two `c`'s already overshoot.
  have hy2 : y ≤ 2 := by
    by_contra hy
    have h1 : 3 ≤ y := by omega
    have h2 : 3 * (f * f - 1) ≤ y * (f * f - 1) := Nat.mul_le_mul_right _ h1
    omega
  have hz1 : z ≤ 1 := by
    by_contra hz
    have h1 : 2 ≤ z := by omega
    have h2 : 2 * (f * f) ≤ z * (f * f) := Nat.mul_le_mul_right _ h1
    omega
  have hxf : f ∣ x * f := ⟨x, Nat.mul_comm x f⟩
  have hf2 : f ∣ f * f := ⟨f, rfl⟩
  have hzf : f ∣ z * (f * f) := Dvd.dvd.mul_left hf2 z
  have hbig : f ∣ 2 * (f * f) := Dvd.dvd.mul_left hf2 2
  have hsum : f ∣ x * f + z * (f * f) + f := dvd_add (dvd_add hxf hzf) (dvd_refl f)
  interval_cases y
  · -- `y = 0`: the residue is `f + 2`, forcing `f ∣ 2`.
    have heq : 2 * (f * f) - (x * f + z * (f * f) + f) = 2 := by omega
    have hd : f ∣ 2 := by have h6 := Nat.dvd_sub hbig hsum; rwa [heq] at h6
    exact absurd (Nat.le_of_dvd (by norm_num) hd) (by omega)
  · -- `y = 1`: one `b` absorbs `f² − 1`, leaving residue `f + 1`, so `f ∣ 1`.
    have heq : f * f - (x * f + z * (f * f) + f) = 1 := by omega
    have hd : f ∣ 1 := by have h6 := Nat.dvd_sub hf2 hsum; rwa [heq] at h6
    exact absurd (Nat.le_of_dvd (by norm_num) hd) (by omega)
  · -- `y = 2`: `2b = 2f² − 2` already overshoots the target by `f`, so there is no room at all.
    omega

/-- **The `jb` chord gap, uniform in the block length.**

A side whose initial `c`-block has length `j` puts a chord of length exactly `jb` from `j c·u` down
to `(jf,0)`, cut into `j` segments of length `b` (companion; `Frontier.chord_jb`). The `β`-slot tile
lays one of its edges first along that chord, and every tile edge that can start there has length
divisible by `f` — `a = f` and `c = f²` both do. The run left over is `jb − t`, and it is never in
the semigroup.

Proof: reducing `x·f + y·(f²−1) + z·f² + t = j(f²−1)` modulo `f` forces `y ≡ j`, so `y ≥ j` and
`y(f²−1) ≥ jb > jb − t`, contradicting `y(f²−1) ≤ jb − t`. Carried out below without any modular
reasoning: the same content appears as `f ∣ s + z` with `0 < s + z ≤ j < f`.

This subsumes the three runs of the double-`c` configuration — `b − a` is `(j,t) = (1,a)`,
`2b − a` is `(2,a)` and `2b − c` is `(2,c)`, which at `f = 4` read `11`, `26`, `14` against
`⟨4,15,16⟩` — and extends them to every initial block length at once.

The bound `j < f` is sharp, not an artifact: at `j = f` both `jb − a = f(f²−2)` and
`jb − c = f(f²−f−1)` are multiples of `f` and so lie in the semigroup. It is also automatic in the
intended application, since `j ≤ n_c = f − k` and an escaping side carries an `a`-edge, so `k ≥ 1`. -/
theorem gap_jb_minus_multiple {f j t x y z : ℕ} (hf : 3 ≤ f) (hj : 1 ≤ j) (hjf : j < f)
    (ht : 0 < t) (htf : f ∣ t)
    (h : x * f + y * (f * f - 1) + z * (f * f) + t = j * (f * f - 1)) : False := by
  have hff : 9 ≤ f * f := by nlinarith
  obtain ⟨B, hB⟩ : ∃ B, f * f = B + 1 := ⟨f * f - 1, by omega⟩
  rw [hB] at h
  simp only [Nat.add_sub_cancel] at h
  -- h : x * f + y * B + z * (B + 1) + t = j * B
  have hB1 : 8 ≤ B := by omega
  -- Normalise `z * (B+1)` away first: omega treats it as an atom unrelated to `z * B` otherwise.
  have hzB : z * (B + 1) = z * B + z := by ring
  have h' : x * f + y * B + z * B + z + t = j * B := by omega
  -- Size: `y + z` copies of `B` already fit under `j * B`, with `t > 0` left over.
  have hyz : y + z < j := by
    by_contra hc
    push_neg at hc
    have hle : j * B ≤ (y + z) * B := Nat.mul_le_mul_right _ hc
    have hsplit : (y + z) * B = y * B + z * B := by ring
    omega
  obtain ⟨s, hs⟩ : ∃ s, j = y + z + s := ⟨j - (y + z), by omega⟩
  have hs1 : 1 ≤ s := by omega
  -- Cancel the `y` and `z` copies of `B`: what remains is `x*f + z + t = s*B`.
  have key : x * f + z + t = s * B := by
    have e : j * B = y * B + z * B + s * B := by rw [hs]; ring
    omega
  -- `s*B = s*f² − s`, so `s*f² = x*f + s + z + t`; `f` divides the two outer terms.
  have key2 : s * (f * f) = x * f + s + z + t := by rw [hB]; nlinarith [key]
  have hdvd : f ∣ s + z + t := by
    have h1 : f ∣ s * (f * f) := ⟨s * f, by ring⟩
    have h2 : f ∣ x * f := ⟨x, Nat.mul_comm x f⟩
    have h3 : s * (f * f) - x * f = s + z + t := by omega
    have h4 := Nat.dvd_sub h1 h2
    rwa [h3] at h4
  have hsz : f ∣ s + z := by
    have h5 := Nat.dvd_sub hdvd htf
    have h6 : s + z + t - t = s + z := by omega
    rwa [h6] at h5
  -- `0 < s + z ≤ j < f`, so `f ∣ s + z` is impossible.
  exact absurd (Nat.le_of_dvd (by omega) hsz) (by omega)

/-- **The `jb` chord gap, general in `(e,f)`.**

The `e = 1` case is `gap_jb_minus_multiple`. Nothing in that argument used `e = 1` beyond the
cancellation of `e^2` modulo `f`, so with `gcd(f, e^2) = 1` it runs verbatim for every member
`(a,b,c) = (ef,\ f^2-e^2,\ f^2)`.

Reducing `x(ef) + y(f^2-e^2) + z f^2 + t = j(f^2-e^2)` modulo `f`: both `a = ef` and `c = f^2`
vanish, `b \equiv -e^2`, and `f \mid t`, so `e^2(y-j) \equiv 0`; coprimality gives `y \equiv j`.
The size bound gives `y < j`, and then `0 < j-y \le j < f` contradicts `f \mid (j-y)`.

Both edges a `β`-slot tile can lay first are multiples of `f` here as well (`a = ef`, `c = f^2`), so
the lemma applies to each. Checked against every coprime member with `e \le 5`, `f \le e+9`: the
range is exactly `1 \le j \le f-1` in each, the sole exception being `jb - c` at `(e,f) = (1,2)`,
where the run is negative. This is the arithmetic the thick (`e \ge 2`) branch needs. -/
theorem gap_jb_minus_multiple_gen {e f j t x y z B : ℕ} (he : 1 ≤ e) (hef : e < f)
    (hco : Nat.Coprime f (e * e)) (hj : 1 ≤ j) (hjf : j < f) (ht : 0 < t) (htf : f ∣ t)
    (hB : f * f = B + e * e)
    (h : x * (e * f) + y * B + z * (f * f) + t = j * B) : False := by
  have hBpos : 0 < B := by nlinarith
  have e1 : z * (f * f) = z * B + z * (e * e) := by rw [hB]; ring
  -- `y + z` copies of `B` already fit under `j * B`, with `t > 0` left over
  have hyz : y + z < j := by
    by_contra hcon
    push_neg at hcon
    have h2 : j * B ≤ (y + z) * B := Nat.mul_le_mul_right _ hcon
    have h3 : (y + z) * B = y * B + z * B := by ring
    omega
  obtain ⟨s, hs⟩ : ∃ s, j = y + z + s := ⟨j - (y + z), by omega⟩
  have hs1 : 1 ≤ s := by omega
  have key : x * (e * f) + z * (e * e) + t = s * B := by
    have e2 : j * B = y * B + z * B + s * B := by rw [hs]; ring
    omega
  have key2 : s * (f * f) = x * (e * f) + e * e * (s + z) + t := by
    have e4 : s * (f * f) = s * B + s * (e * e) := by rw [hB]; ring
    have e3 : e * e * (s + z) = s * (e * e) + z * (e * e) := by ring
    omega
  have hdvd : f ∣ e * e * (s + z) := by
    have h1 : f ∣ s * (f * f) := ⟨s * f, by ring⟩
    have h2 : f ∣ x * (e * f) := ⟨x * e, by ring⟩
    have h3 : s * (f * f) - x * (e * f) - t = e * e * (s + z) := by omega
    have h5 := Nat.dvd_sub (Nat.dvd_sub h1 h2) htf
    rwa [h3] at h5
  have hsz : f ∣ (s + z) := (Nat.Coprime.dvd_of_dvd_mul_left hco) hdvd
  have hpos : 0 < s + z := by omega
  exact absurd (Nat.le_of_dvd hpos hsz) (by omega)

/-- **The pincer window.** With chain reach 3 on thick-block sides (and full reach on blocks
`≤ 2`), a base word dies unless it escapes all four kills: left direct-`b` (`bp ≤ 4` when the `b`
comes first), right direct-`b` (`f+3−bp ≤ 4` when the `c` comes first), right L2 (`cp = bp+1`
near the far corner), left L2 (`bp = cp+1` near the near corner). For `f ≤ 5` no admissible
`(bp, cp)` escapes: the window is empty and `hyp:walls (1,5)` follows. -/
theorem pincer_window {f bp cp : ℕ} (hf : 3 ≤ f) (hf5 : f ≤ 5)
    (hb3 : 3 ≤ bp) (hbf : bp ≤ f) (hc2 : 2 ≤ cp) (hcf : cp ≤ f + 1) (hne : bp ≠ cp) :
    (bp < cp ∧ bp ≤ 4) ∨ (cp < bp ∧ f + 3 - bp ≤ 4) ∨
    (cp = bp + 1 ∧ f + 3 - cp ≤ 4) ∨ (bp = cp + 1 ∧ cp ≤ 4) := by omega

/-- **The apex figure.** The target's apex angle is `π − 2β = 3α` (branch relation), and the
only vertex figure summing to `3α` is three `α`-corners: `z = 0` is forced (`γ = 2α+β` alone
exceeds the budget in `β`), then `y = 0`, then `x = 3`. With `side_no_b`, the two outer apex
tiles lay `c` on the sides and the fan rays sit at labels `−3, −1, +1, +3`: the apex admits
exactly two configurations (the middle tile's chirality). -/
theorem apex_figure (x y z : ℕ) (h1 : x + 2 * z = 3) (h2 : y + z = 0) :
    x = 3 ∧ y = 0 ∧ z = 0 := by omega

/-- **Descent identities.** A straddler's `c`-line (direction label `−2`) crosses the strip
lines at intervals of exactly `b` along itself, advancing exactly `c` horizontally per crossing:
`fu_x + b·|cos 2γ| = c` reduces to `(3f²−1) + (f²−1)(2f²−1) = 2f⁴`. And `sin β` has the closed
form `b√D/(2f³)`, `D = 4f²−1`: `4f⁶ − (3f²−1)² = (f²−1)²(4f²−1)`. -/
theorem descent_ident (f : ℤ) :
    (3 * f ^ 2 - 1) + (f ^ 2 - 1) * (2 * f ^ 2 - 1) = 2 * f ^ 4 := by ring

/-- **The sin β discriminant identity**: `4f⁶ − (3f²−1)² = (f²−1)²(4f²−1)` over ℤ. -/
theorem sinb_ident (f : ℤ) :
    4 * f ^ 6 - (3 * f ^ 2 - 1) ^ 2 = (f ^ 2 - 1) ^ 2 * (4 * f ^ 2 - 1) := by ring

/-- **No base exit.** A strip-junction ladder terminating on the base needs `f² ∣ K` with
`K = (j−1)f + i`, `1 ≤ i ≤ f−1`; but then `f ∣ K` while `K ≡ i ≢ 0 (mod f)`. -/
theorem ladder_no_base {f K : ℕ} (h : K % f ≠ 0) : ¬ (f * f ∣ K) := by
  intro hd
  have h2 : f ∣ K := dvd_trans (Dvd.intro f rfl) hd
  omega

/-! ## The ladder termination bound

A ladder terminates (at the boundary or at an interior mutual vertex) only where BOTH of its
staggered covers end. With `c = b+1` that says `T−b` and `T−c` are consecutive members of
`S = ⟨f, f²−1, f²⟩`. Consecutive members of `S` are far apart: -/

/-- **Consecutive members of `S` start at `f²`.** If `m` and `m+1` both lie in
`S = ⟨f, f²−1, f²⟩` then `m+1 ≥ f²`. Hence a ladder's termination parameter satisfies
`T = b + (m+1) ≥ b + c = 2f²−1`. -/
theorem consecutive_gap {f m x1 y1 z1 x2 y2 z2 : ℕ} (hf : 3 ≤ f)
    (h1 : x1 * f + y1 * (f * f - 1) + z1 * (f * f) = m)
    (h2 : x2 * f + y2 * (f * f - 1) + z2 * (f * f) = m + 1) :
    f * f ≤ m + 1 := by
  have hff : 9 ≤ f * f := by nlinarith
  by_contra hcon
  push_neg at hcon
  have hy2 : y2 ≤ 1 := by
    by_contra h
    have hh : 2 ≤ y2 := by omega
    have := Nat.mul_le_mul_right (f * f - 1) hh
    omega
  have hz2 : z2 = 0 := by
    by_contra h
    have hh : 1 ≤ z2 := by omega
    have := Nat.mul_le_mul_right (f * f) hh
    omega
  have hy1 : y1 ≤ 1 := by
    by_contra h
    have hh : 2 ≤ y1 := by omega
    have := Nat.mul_le_mul_right (f * f - 1) hh
    omega
  have hz1 : z1 = 0 := by
    by_contra h
    have hh : 1 ≤ z1 := by omega
    have := Nat.mul_le_mul_right (f * f) hh
    omega
  subst hz1; subst hz2
  simp only [Nat.zero_mul, Nat.one_mul, Nat.add_zero] at h1 h2
  have hfm : f ∣ f * f := ⟨f, rfl⟩
  interval_cases y1 <;> interval_cases y2 <;>
    simp only [Nat.zero_mul, Nat.one_mul, Nat.add_zero] at h1 h2
  · -- m = x1 f and m+1 = x2 f : f ∣ 1
    have d1 : f ∣ m := by rw [← h1]; exact ⟨x1, Nat.mul_comm x1 f⟩
    have d2 : f ∣ m + 1 := by rw [← h2]; exact ⟨x2, Nat.mul_comm x2 f⟩
    have hd : f ∣ 1 := by have h6 := Nat.dvd_sub d2 d1; simpa using h6
    have := Nat.le_of_dvd (by norm_num) hd; omega
  · -- m = x1 f and m+1 = x2 f + (f²−1) : forces m+2 = f², so f ∣ 2
    have hx2 : x2 * f = 0 := by omega
    have d1 : f ∣ m := by rw [← h1]; exact ⟨x1, Nat.mul_comm x1 f⟩
    have hm : m + 2 = f * f := by omega
    have hd : f ∣ 2 := by
      have hdm : f ∣ m + 2 := hm ▸ hfm
      have h6 := Nat.dvd_sub hdm d1; simpa using h6
    have := Nat.le_of_dvd (by norm_num) hd; omega
  · omega
  · omega

/-- **The ladder needs more than two strips.** `T ≥ b + c > 2b`: the minimal termination
parameter strictly exceeds two strip-crossings, so a straddler needs at least three strips of
clearance below it and cannot sit at rows 1, 2 or 3. -/
theorem ladder_three_strips (f : ℕ) : 2 * (f * f - 1) < (f * f - 1) + f * f ∨ f = 0 := by
  rcases Nat.eq_zero_or_pos f with h | h
  · right; exact h
  · left
    have : 1 ≤ f * f := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega

/-- **The target is exactly `f` strips tall**: height `f³ sin β` over strip height `c sin β = f²
sin β`. -/
theorem strips_tall (f : ℕ) : f ^ 3 = f * f ^ 2 := by ring

/-- **The reach-four window is empty for `f ≤ 6`.** With the row-3 fork closed the chains reach
slot 4, so the four kills cover depth `≤ 5`; no admissible `(bp, cp)` escapes. -/
theorem pincer_window_four {f bp cp : ℕ} (hf : 3 ≤ f) (hf6 : f ≤ 6)
    (hb3 : 3 ≤ bp) (hbf : bp ≤ f) (hc2 : 2 ≤ cp) (hcf : cp ≤ f + 1) (hne : bp ≠ cp) :
    (bp < cp ∧ bp ≤ 5) ∨ (cp < bp ∧ f + 3 - bp ≤ 5) ∨
    (cp = bp + 1 ∧ f + 3 - cp ≤ 5) ∨ (bp = cp + 1 ∧ cp ≤ 5) := by omega

/-- **The chain never needs the apex line.** The base `b`-letter sits at position `bp ∈ [3,f]`;
with the preceding letters all `a` it begins at `((bp−1)f, 0)`, and the collision figure there
consumes only the lines `L_k` with `k ≤ bp − 1`. Every such `k` is `< f`, so
`partition_jb` applies to all of them and the apex line `L_f` is never required. -/
theorem chain_needs_small_lines {f bp k : ℕ} (hf : 3 ≤ f) (hb3 : 3 ≤ bp) (hbf : bp ≤ f)
    (hk : k ≤ bp - 1) : k < f := by omega

/-- **The vertex census identity.** Every tile contributes one `α`, one `β`, one `γ`. The base
corners consume `{β}` each (unique fill of the angle `β`), the apex `{3α}` (unique fill of `3α`);
straight figures are `{γ,α,β}` (n₁) or `{3α,2β}` (n₂); interior figures are `{β,3γ}` (v₁),
`{2α,2β,2γ}` (v₂), `{4α,3β,γ}` (v₃), `{6α,4β}` (v₄). Balancing the three corner types:

    v₁ − v₃ − 2·v₄ − n₂ = 1.

In particular `v₁ ≥ 1`: every tiling of the base-β target contains a `{β,3γ}` vertex, and each
`{3α,2β}` junction or `γ`-poor interior figure demands one more. Verified exactly on all five
kernel-checked tilings (each gives 1). -/
theorem vertex_census {N n1 n2 v1 v2 v3 v4 : ℕ}
    (ha : 3 + n1 + 3 * n2 + 2 * v2 + 4 * v3 + 6 * v4 = N)
    (hb : 2 + n1 + 2 * n2 + v1 + 2 * v2 + 3 * v3 + 4 * v4 = N)
    (hg : n1 + 3 * v1 + 2 * v2 + v3 = N) :
    v1 = 1 + n2 + v3 + 2 * v4 := by omega

/-- Corollary: the climber is mandatory — `v₁ ≥ 1` in every tiling. -/
theorem climber_mandatory {N n1 n2 v1 v2 v3 v4 : ℕ}
    (ha : 3 + n1 + 3 * n2 + 2 * v2 + 4 * v3 + 6 * v4 = N)
    (hb : 2 + n1 + 2 * n2 + v1 + 2 * v2 + 3 * v3 + 4 * v4 = N)
    (hg : n1 + 3 * v1 + 2 * v2 + v3 = N) : 1 ≤ v1 := by omega

/-! ## The frontier invariant (read off the search engine)

The exhaustive engine prunes a frontier `F` (the uncovered polygons plus per-side boundary
edge-type counts) by five conditions, all `f`-uniform and decidable:

* **P1** each uncovered polygon has area a positive integer multiple of the tile area, and the
  multiples sum to the number of tiles remaining;
* **P2** every maximal straight run of the uncovered boundary joining two convex corners has
  integral length lying in `⟨a,b,c⟩`;
* **P4** every convex corner of the uncovered region has angle at least `α`;
* **P5** the per-side boundary edge-type counts are dominated by an admissible walk profile;
* **P6** an edge lying in a target side and meeting that side's corner has the forced type.

An `EXHAUSTED` verdict is the assertion that every branch violates one of these. The translation
of P4 from code to mathematics rests on `cosmin2` being `cos²α`, which for this family has the
closed form below. -/

/-- **`cos α` in closed form.** For the tile `(a,b,c) = (f, f²−1, f²)` the law of cosines gives
`cos α = (2f²−1)/(2f²)`; cleared of denominators this is a ring identity. Consequently the
engine's `cosmin2` threshold is exactly `cos²α`, and its P4 prune is the statement that no convex
corner of the uncovered region is smaller than the tile's smallest angle. -/
theorem cos_alpha_closed (f : ℤ) :
    2 * f ^ 2 * ((f ^ 2 - 1) ^ 2 + (f ^ 2) ^ 2 - f ^ 2)
      = (2 * f ^ 2 - 1) * (2 * (f ^ 2 - 1) * f ^ 2) := by ring

/-- `cos γ = −1/(2f)` and `cos β = (3f²−1)/(2f³)` in the same cleared form, for reference
alongside `cos_alpha_closed`. -/
theorem cos_beta_gamma_closed (f : ℤ) :
    (2 * f ^ 3 * (f ^ 2 + (f ^ 2) ^ 2 - (f ^ 2 - 1) ^ 2) = (3 * f ^ 2 - 1) * (2 * f * f ^ 2))
    ∧ (2 * f * (f ^ 2 + (f ^ 2 - 1) ^ 2 - (f ^ 2) ^ 2) = -(2 * f * (f ^ 2 - 1)) + 0) := by
  constructor <;> ring_nf <;> ring

/-- **The shadow footage inequality at `e = 1`.** If both base corners were `c`-corners with
first runs of length `≥ 2`, the base `b`-edge would be confined to the window
`Y − 2(c + a·cosβ)`; the comparison `b·f² + 2f⁴ > B(f²−1)` (with `B = 3f²−1`) reduces to
`3f² > 1`: the window is ALWAYS too small at `e = 1`. An independent kill of `c`-corners,
consistent with the γ-cascade of `thm:e1reduce`. At `e ≥ 2` the same comparison reverses and the
`b`-edges fit: the thick case genuinely differs. -/
theorem shadow_footage_e1 (f : ℤ) (hf : 2 ≤ f) :
    (3 * f ^ 2 - 1) * (f ^ 2 - 1) - 2 * f ^ 4 < (f ^ 2 - 1) * f ^ 2 := by nlinarith

/-- **Crossing tangency.** A strip-junction ladder's `k`-th strip crossing sits exactly
`(k−1)c` east of the `k`-th-lower ceiling's endpoint: the crossings are endpoint-tangent, never
transversal. Scaled form of `descent_ident`; this is what defeats the self-crossing kill. -/
theorem crossing_tangency (f k : ℤ) :
    k * ((f ^ 2 - 1) * (2 * f ^ 2 - 1) + (3 * f ^ 2 - 1)) - 2 * f ^ 4
      = (k - 1) * (2 * f ^ 4) := by ring

/-- **The mirrored piece's junction.** A mirrored cover piece presents `β` at its left junction
(its foot-to-left edge is `c`, not `b`), and so does the direct piece to its left: the junction
carries `n_β ≥ 2`, which forces the figure `{3α, 2β}` — the second straight figure. Every
mirrored piece therefore creates an `n₂`-junction. -/
theorem mirrored_left_junction (na nb ng : ℕ) (h1 : na + 2 * ng = 3) (h2 : nb + ng = 2)
    (hb : 2 ≤ nb) : na = 3 ∧ nb = 2 ∧ ng = 0 := by omega

/-- **The escape is charged.** Combining `mirrored_left_junction` with the vertex census: a single
mirrored cover piece forces `n₂ ≥ 1`, hence `v₁ ≥ 2` — a second `{β,3γ}` climber vertex must exist
somewhere in the tiling. The off-lattice escape is not free. -/
theorem escape_charge {N n1 n2 v1 v2 v3 v4 : ℕ} (hn2 : 1 ≤ n2)
    (ha : 3 + n1 + 3 * n2 + 2 * v2 + 4 * v3 + 6 * v4 = N)
    (hb : 2 + n1 + 2 * n2 + v1 + 2 * v2 + 3 * v3 + 4 * v4 = N)
    (hg : n1 + 3 * v1 + 2 * v2 + v3 = N) : 2 ≤ v1 := by omega

/-- **The forced-region vertex figure.** At an interior lattice point of the brick/mate
structure exactly six tiles meet, contributing `β, γ, α` from the row above and `α, γ, β` from the
row below (translation structure), so the counts are `(2,2,2)`: the figure is `{2α,2β,2γ}`, and it
solves the full-vertex system. Consequently a `{β,3γ}` climber at an interior vertex certifies
that the six tiles there are NOT the brick/mate six: climbers detect deviation from the forced
pattern. -/
theorem brick_mate_vertex : 2 + 2 * 2 = 6 ∧ 2 + 2 = 4 := by omega

/-- **`partition_jb`, general in `(e,f)`, self-contained.** With `(a,b,c) = (ef, B, f²)` and
`f² = B + e²`, the only decomposition of `j·b` for `j < f` is `j` copies of `b`. Both reductions
are derived here rather than assumed: the size bound `y + z ≤ j` from positivity of `B`, and the
congruence from `e²(z+w) + x·ef = w·f²`, which gives `f ∣ e²(z+w)` and hence `f ∣ z+w` by
coprimality; since `z + w ≤ j < f` this forces `z = w = 0`, so `y = j` and `x = 0`. -/
theorem partition_jb_gen {e f j x y z B : ℕ} (he : 1 ≤ e) (hef : e < f) (hjf : j < f)
    (hco : Nat.Coprime f (e * e)) (hB : f * f = B + e * e)
    (h : x * (e * f) + y * B + z * (f * f) = j * B) :
    x = 0 ∧ y = j ∧ z = 0 := by
  have hBpos : 0 < B := by nlinarith
  have e1 : z * (f * f) = z * B + z * (e * e) := by rw [hB]; ring
  have hyz : y + z ≤ j := by
    by_contra hcon
    have h1 : j + 1 ≤ y + z := by omega
    have h2 : (j + 1) * B ≤ (y + z) * B := Nat.mul_le_mul_right _ h1
    have h3 : (y + z) * B = y * B + z * B := by ring
    have h4 : (j + 1) * B = j * B + B := by ring
    omega
  obtain ⟨w, hw⟩ : ∃ w, j = y + z + w := ⟨j - y - z, by omega⟩
  have e2 : (y + z + w) * B = y * B + z * B + w * B := by ring
  have e3 : w * (f * f) = w * B + w * (e * e) := by rw [hB]; ring
  have e4 : e * e * (z + w) = z * (e * e) + w * (e * e) := by ring
  have hkey : e * e * (z + w) + x * (e * f) = w * (f * f) := by
    subst hw; omega
  have hdvd : f ∣ e * e * (z + w) := by
    have h1 : f ∣ w * (f * f) := ⟨w * f, by ring⟩
    have h2 : f ∣ x * (e * f) := ⟨x * e, by ring⟩
    have hle : x * (e * f) ≤ w * (f * f) := by omega
    have h3 : w * (f * f) - x * (e * f) = e * e * (z + w) := by omega
    have h5 := Nat.dvd_sub h1 h2
    rwa [h3] at h5
  have hzw : f ∣ (z + w) := (Nat.Coprime.dvd_of_dvd_mul_left hco) hdvd
  have hzw0 : z + w = 0 := by
    rcases Nat.eq_zero_or_pos (z + w) with h0 | h0
    · exact h0
    · exact absurd (Nat.le_of_dvd h0 hzw) (by omega)
  have hz : z = 0 := by omega
  have hw0 : w = 0 := by omega
  have hy : y = j := by omega
  rw [hz, hw0] at hkey
  simp only [Nat.add_zero, Nat.mul_zero, Nat.zero_mul, Nat.zero_add] at hkey
  have hx : x * (e * f) = 0 := hkey
  refine ⟨?_, hy, hz⟩
  rcases Nat.mul_eq_zero.mp hx with h0 | h0
  · exact h0
  · exfalso
    have : 0 < e * f := Nat.mul_pos (by omega) (by omega)
    omega

end Erdos634.OrderForcing

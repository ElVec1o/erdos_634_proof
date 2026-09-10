import Erdos634.N1Gap

/-!
# The crossing branch at `V_k` is finitely parametrised (subatomising `rem:n1gapexact`)

Erdős #634, `e ≥ 2` branch of `thm:n1`.  `N1Gap.step_reduces_to_crossing` reduces the induction
step to one assertion: *no tile edge overruns `V_k`*.  The two arithmetic escapes are closed
(`Frontier.gap_b_sub_a`, `Frontier.gap_e_squared`) and what is left — "an edge simply passes
through `V_k`, no closure equation imposed" — has been carried as a **single monolithic case for
all `(e,f)`**.

This file shows it is not monolithic.  The crossing edge `Q'` is pinned by two data: the distance
`s` of its near end from the anchored base end of the chord, and its own length `L ∈ {a,b,c}`.
Both are forced into an explicit finite range:

* **`prefix_all_a`** — every far-side partial sum strictly below `b` is a multiple of `a`.  No `b`
  and no `c` can precede the crossing edge, because either already exceeds `b`.  So `s = x·a`.
* **`adm_iff`** — with `X := b / a`, the admissible pairs are exactly
  `L = c` with `0 ≤ x ≤ X`, `L = b` with `1 ≤ x ≤ X`, and `L = a` with `x = X` and nothing else.
* **`card_adm`** — hence exactly `2X + 2 = 2⌊b/a⌋ + 2` sub-configurations, `X ≥ 1` always and
  `X` growing like `f/e`.
* **`overhang_*`** — the distance `t` by which the edge passes `V_k` is computed in each:
  `t = x·a + e²` (`L = c`), `t = x·a` (`L = b`), `t = a − b % a` (`L = a`, one configuration).

The `e`-dependence asked of this branch is real and is isolated in **`a_overhang_eq_e_sq_iff`**:
the `L = a` sub-case's overhang equals `e²` — the overhang of the canonical `L = c, x = 0`
sub-case of `rem:n1gapexact` — **iff `e = 1`**.  At `e = 1` the fall-short and overrun branches
produce the *same* configuration past `V_k`; from `e = 2` on they are genuinely distinct points,
and the branch carries `2⌊(f²−e²)/(ef)⌋ + 2 ≥ 6` configurations rather than the two the prose
suggests.

**What this does not do, stated plainly.**  It does not kill any sub-case.  `rem:overrunshape`'s
vertex figure at `V_k` — `{γ, α, β}` with exactly one further tile `R`, presenting `α`, its two
edges at `V_k` being `b` and `c` — is derived from *a* passing edge contributing `π` there, and is
therefore **identical in all `2X + 2` sub-configurations**: the two-hop constraint at `V_k` does
not separate them.  Nor does the far endpoint `V_k + t·u` separate them: it lies on the interface
between `Q'` and `R`'s chord-extension edge, and for every `t` above it is a legal `T`-junction
(`t < L'`), shared vertex (`t = L'`), or straddled end (`t > L'`), with `L' ∈ {b,c}` free.  The
narrowing is in the *index set*, not in any exclusion.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.N1GapSubcases

open Erdos634.N1Gap

variable {e f a b c : ℕ}

/-! ## The shortest side does not divide `b` -/

/-- `a = ef` never divides `b = f² − e²` at a member: `ef ∣ f² − e²` gives `f ∣ e²`, hence `f = 1`
by coprimality, against `e < f` and `1 ≤ e`.  This is what makes `⌊b/a⌋` the sharp bound below. -/
theorem a_not_dvd_b (M : Member e f a b c) : ¬ (a ∣ b) := by
  obtain ⟨he, hef, hco, ha, hb, _, _⟩ := M
  rintro ⟨k, hk⟩
  have hkey : f * (k * e) + e * e = f * f := by
    rw [ha] at hk; rw [← hb, hk]; ring
  have hdvd : f ∣ e * e := ⟨f - k * e, by
    have hle : k * e ≤ f := by nlinarith
    rw [Nat.mul_sub]
    omega⟩
  have hfe : Nat.Coprime f e := hco.symm
  have : f = 1 := Nat.Coprime.eq_one_of_dvd (hfe.mul_right hfe) hdvd
  omega

theorem a_pos (M : Member e f a b c) : 0 < a := by
  obtain ⟨he, hef, _, ha, _, _, _⟩ := M
  rw [ha]; exact Nat.mul_pos (by omega) (by omega)

/-! ## The prefix before the crossing edge is all `a`'s -/

/-- **No `b` and no `c` can precede the crossing edge.**  Any far-side partial sum `s` strictly
below `b` has `y = z = 0`, because a single `b` or `c` already reaches `b`.  So the near end of
the edge that passes `V_k` sits at `x·a` for some `x`.

This is the `N1Gap` analogue of `OrderForcing.partition_c_sub_a` (which does the same job for the
Route 1 wall at length `c − a`); here no divisibility input is needed, only `a < b < c`. -/
theorem prefix_all_a (M : Member e f a b c) {x y z s : ℕ}
    (hs : x * a + y * b + z * c = s) (hlt : s < b) : y = 0 ∧ z = 0 ∧ s = x * a := by
  have hbc : b < c := M.b_lt_c
  have hy : y = 0 := by
    rcases Nat.eq_zero_or_pos y with h | h
    · exact h
    · exfalso; have := Nat.le_mul_of_pos_left b h; omega
  have hz : z = 0 := by
    rcases Nat.eq_zero_or_pos z with h | h
    · exact h
    · exfalso; have := Nat.le_mul_of_pos_left c h; omega
  subst hy; subst hz; exact ⟨rfl, rfl, by omega⟩

/-! ## The admissible `(x, L)` are exactly `2⌊b/a⌋ + 2` -/

/-- The near end sits before `V_k` exactly when `x ≤ ⌊b/a⌋`. -/
theorem start_iff (M : Member e f a b c) (x : ℕ) : x * a < b ↔ x ≤ b / a := by
  have hpa := a_pos M
  constructor
  · intro h; exact (Nat.le_div_iff_mul_le hpa).mpr (by omega)
  · intro h
    have hle : x * a ≤ b := (Nat.le_div_iff_mul_le hpa).mp h
    rcases Nat.lt_or_ge (x * a) b with h' | h'
    · exact h'
    · exact absurd (Dvd.intro_left x (by omega)) (a_not_dvd_b M)

/-- **The enumeration.**  For a tile side `L`, the pair `(x, L)` describes a crossing at `V_k` —
near end at `x·a` strictly before `V_k`, far end strictly past it — exactly in the listed cases.
Writing `X = ⌊b/a⌋`: `L = c` for every `x ≤ X`, `L = b` for every `1 ≤ x ≤ X`, and `L = a` for the
single value `x = X`. -/
theorem adm_iff (M : Member e f a b c) {x L : ℕ} (hL : L = a ∨ L = b ∨ L = c) :
    (x * a < b ∧ b < x * a + L) ↔
      (L = c ∧ x ≤ b / a) ∨ (L = b ∧ 1 ≤ x ∧ x ≤ b / a) ∨ (L = a ∧ x = b / a) := by
  have hpa := a_pos M
  have hbc : b < c := M.b_lt_c
  have hstart := start_iff M x
  rcases hL with rfl | rfl | rfl
  · -- L = a : `b < x·a + a` is `¬ (x+1 ≤ b/a)`
    have hsucc : b < x * L + L ↔ b / L ≤ x := by
      constructor
      · intro h
        by_contra hcon
        have : x + 1 ≤ b / L := by omega
        have := (Nat.le_div_iff_mul_le hpa).mp this
        nlinarith
      · intro h
        rcases Nat.lt_or_ge b (x * L + L) with h' | h'
        · exact h'
        · exfalso
          have : x + 1 ≤ b / L := (Nat.le_div_iff_mul_le hpa).mpr (by nlinarith)
          omega
    constructor
    · rintro ⟨h1, h2⟩
      exact Or.inr (Or.inr ⟨rfl, le_antisymm (hstart.mp h1) (hsucc.mp h2)⟩)
    · rintro (⟨h, -⟩ | ⟨h, -, -⟩ | ⟨-, hx⟩)
      · exact absurd h.symm (by have := M.a_lt_b; omega)
      · exact absurd h.symm (by have := M.a_lt_b; omega)
      · exact ⟨hstart.mpr (by omega), hsucc.mpr (by omega)⟩
  · -- L = b : `b < x·a + b` is `1 ≤ x`
    constructor
    · rintro ⟨h1, h2⟩
      refine Or.inr (Or.inl ⟨rfl, ?_, hstart.mp h1⟩)
      rcases Nat.eq_zero_or_pos x with rfl | h; · simp at h2
      exact h
    · rintro (⟨h, -⟩ | ⟨-, hx1, hx2⟩ | ⟨h, -⟩)
      · exact absurd h (by omega)
      · refine ⟨hstart.mpr hx2, ?_⟩
        have : a ≤ x * a := Nat.le_mul_of_pos_left a hx1
        omega
      · exact absurd h (by have := M.a_lt_b; omega)
  · -- L = c : always past, since c > b
    constructor
    · rintro ⟨h1, -⟩; exact Or.inl ⟨rfl, hstart.mp h1⟩
    · rintro (⟨-, hx⟩ | ⟨h, -, -⟩ | ⟨h, -⟩)
      · exact ⟨hstart.mpr hx, by omega⟩
      · exact absurd h (by omega)
      · exact absurd h (by have := M.a_lt_b; omega)

/-- **The branch has exactly `2⌊b/a⌋ + 2` sub-configurations.**  The admissible set, as a `Finset`
of pairs `(x, L)` with `x ≤ ⌊b/a⌋` and `L` a tile side, has that cardinality — so the open branch
is a finite explicit list, not one case.  `⌊b/a⌋ ≥ 1` at every separated member, so the list has
at least four entries and grows like `2f/e`. -/
theorem card_adm (M : Member e f a b c) :
    ((Finset.range (b / a + 1) ×ˢ ({a, b, c} : Finset ℕ)).filter
      (fun p => p.1 * a < b ∧ b < p.1 * a + p.2)).card = 2 * (b / a) + 2 := by
  classical
  have hab := M.a_lt_b
  have hbc := M.b_lt_c
  have hab' : a ≠ b := by omega
  have hac' : a ≠ c := by omega
  have hbc' : b ≠ c := by omega
  set X := b / a with hX
  have hset :
      (Finset.range (X + 1) ×ˢ ({a, b, c} : Finset ℕ)).filter
        (fun p => p.1 * a < b ∧ b < p.1 * a + p.2)
      = ((Finset.range (X + 1)).image (fun x => (x, c)))
        ∪ (((Finset.Icc 1 X).image (fun x => (x, b))) ∪ {(X, a)}) := by
    ext ⟨x, L⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_union, Finset.mem_image, Finset.mem_Icc,
      Prod.ext_iff]
    constructor
    · rintro ⟨⟨-, hLmem⟩, hcond⟩
      have hL : L = a ∨ L = b ∨ L = c := by tauto
      rcases (adm_iff M hL).mp hcond with ⟨rfl, hx⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, hx⟩
      · exact Or.inl ⟨x, by omega, rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨x, ⟨h1, h2⟩, rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨hx, rfl⟩)
    · intro h
      have key : (L = a ∨ L = b ∨ L = c) ∧ (x * a < b ∧ b < x * a + L) := by
        rcases h with ⟨x', hx', rfl, rfl⟩ | ⟨x', hx', rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨Or.inr (Or.inr rfl), (adm_iff M (Or.inr (Or.inr rfl))).mpr
            (Or.inl ⟨rfl, by omega⟩)⟩
        · exact ⟨Or.inr (Or.inl rfl), (adm_iff M (Or.inr (Or.inl rfl))).mpr
            (Or.inr (Or.inl ⟨rfl, hx'.1, hx'.2⟩))⟩
        · exact ⟨Or.inl rfl, (adm_iff M (Or.inl rfl)).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
      refine ⟨⟨?_, by tauto⟩, key.2⟩
      have := (start_iff M x).mp key.2.1
      omega
  rw [hset]
  have hinjc : Function.Injective (fun x : ℕ => (x, c)) := fun u v h => congrArg Prod.fst h
  have hinjb : Function.Injective (fun x : ℕ => (x, b)) := fun u v h => congrArg Prod.fst h
  have hdisj2 : Disjoint (((Finset.Icc 1 X).image (fun x => (x, b)))) ({(X, a)} : Finset (ℕ × ℕ)) := by
    rw [Finset.disjoint_singleton_right]
    intro hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨x, -, hx⟩ := hmem
    exact hab' (congrArg Prod.snd hx).symm
  have hdisj1 : Disjoint ((Finset.range (X + 1)).image (fun x => (x, c)))
      ((((Finset.Icc 1 X).image (fun x => (x, b))) ∪ {(X, a)})) := by
    rw [Finset.disjoint_union_right]
    refine ⟨?_, ?_⟩
    · rw [Finset.disjoint_left]
      rintro ⟨u, L⟩ h1 h2
      rw [Finset.mem_image] at h1 h2
      obtain ⟨x, -, hx⟩ := h1
      obtain ⟨y, -, hy⟩ := h2
      exact hbc' ((congrArg Prod.snd hy).trans (congrArg Prod.snd hx).symm)
    · rw [Finset.disjoint_singleton_right]
      intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨x, -, hx⟩ := hmem
      exact hac' (congrArg Prod.snd hx).symm
  have hXpos : 1 ≤ X := by
    have : 1 ≤ b / a := (Nat.le_div_iff_mul_le (a_pos M)).mpr (by omega)
    omega
  rw [Finset.card_union_of_disjoint hdisj1, Finset.card_union_of_disjoint hdisj2,
    Finset.card_image_of_injective _ hinjc, Finset.card_image_of_injective _ hinjb,
    Finset.card_range, Nat.card_Icc, Finset.card_singleton]
  omega

/-! ## The overhang past `V_k`, sub-case by sub-case -/

/-- `L = c`: the edge passes `V_k` by `x·a + e²`.  At `x = 0` this is `rem:n1gapexact`'s
`c`-branch, overhang `c − b = e²`. -/
theorem overhang_c (M : Member e f a b c) (x : ℕ) :
    x * a + c - b = x * a + e * e := by
  have := c_overrun M; have := M.b_lt_c; omega

/-- `L = b`: the edge passes `V_k` by exactly `x·a`, the distance of its own near end from the
anchored base end — the crossing edge is a translate of the chord along the chord. -/
theorem overhang_b (x : ℕ) : x * a + b - b = x * a := by omega

/-- `L = a`: the single admissible configuration, `x = ⌊b/a⌋`, passes `V_k` by `a − b % a`, which
is strictly less than `a`.  This is `rem:n1gapexact`'s `a`-branch after `Frontier.gap_b_sub_a` has
forced the shortfall `b − a` to be straddled rather than closed. -/
theorem overhang_a (M : Member e f a b c) :
    (b / a) * a + a - b = a - b % a ∧ 0 < a - b % a ∧ a - b % a < a := by
  have hpa := a_pos M
  have hdm : b % a + a * (b / a) = b := Nat.mod_add_div b a
  have hmod : b % a < a := Nat.mod_lt _ hpa
  have hne : b % a ≠ 0 := fun h => a_not_dvd_b M (Nat.dvd_of_mod_eq_zero h)
  refine ⟨?_, by omega, by omega⟩
  have : (b / a) * a = a * (b / a) := Nat.mul_comm _ _
  omega

/-! ## Where `e = 1` and `e ≥ 2` part company inside the branch -/

/-- **The `e`-split of the open branch.**  The `L = a` sub-case's overhang `a − b % a` equals the
`L = c, x = 0` sub-case's overhang `e²` **iff `e = 1`**.

At `e = 1` the two crossings that `rem:n1gapexact` derives — the `a`-fall-short and the
`c`-overrun — put the crossing edge's far end at the *same* point past `V_k` (distance `1`), so
the "two branches" are one configuration.  From `e = 2` on they are distinct, and the `L = a`
overhang is never `e²`.  This is the only place where the surviving branch's structure is
`e`-dependent: the vertex figure at `V_k` (`rem:overrunshape`) is not.

Proof: `a − b % a = e²` unfolds to `(⌊b/a⌋+1)·ef = f²`, hence `e ∣ f`, hence `e = 1`; conversely at
`e = 1`, `a = f`, `b = f² − 1`, `⌊b/a⌋ = f − 1` and the overhang is `1`. -/
theorem a_overhang_eq_e_sq_iff (M : Member e f a b c) :
    (a - b % a = e * e) ↔ e = 1 := by
  obtain ⟨he, hef, hco, ha, hb, hc, hsep⟩ := M
  have M' : Member e f a b c := ⟨he, hef, hco, ha, hb, hc, hsep⟩
  have hpa := a_pos M'
  have hdm : b % a + a * (b / a) = b := Nat.mod_add_div b a
  have hmod : b % a < a := Nat.mod_lt _ hpa
  have hf0 : 0 < f := by omega
  constructor
  · intro h
    -- `a − b % a = e²` and `b + e² = f²` give `a·(⌊b/a⌋ + 1) = f²`
    have hA : a + a * (b / a) = f * f := by omega
    have h2 : f * (e * (b / a + 1)) = f * f := by
      have hexp : f * (e * (b / a + 1)) = a + a * (b / a) := by rw [ha]; ring
      omega
    have h3 : e * (b / a + 1) = f := Nat.eq_of_mul_eq_mul_left hf0 h2
    exact Nat.Coprime.eq_one_of_dvd hco ⟨b / a + 1, h3.symm⟩
  · rintro rfl
    have hf2 : 2 ≤ f := by nlinarith
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    have ha1 : a = g + 1 := by omega
    have hbg : b = g + (g + 1) * g := by nlinarith
    have hmod1 : b % a = g := by
      rw [ha1, hbg, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by omega)
    omega

/-! ## Non-vacuity -/

/-- **A witness for `Member`**, so nothing above is a statement about an empty hypothesis:
`(e,f) = (2,5)` gives the tile `(a,b,c) = (10,21,25)`, separated (`2·2·5 + 4 = 24 < 25`).  There
`⌊b/a⌋ = 2`, so the branch carries `2·2 + 2 = 6` sub-configurations, the `L = a` overhang is
`10 − 21 % 10 = 9`, and `9 ≠ 4 = e²` — the `e ≥ 2` side of `a_overhang_eq_e_sq_iff`, exhibited. -/
theorem member_witness : Member 2 5 10 21 25 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem witness_six_subcases :
    ((Finset.range (21 / 10 + 1) ×ˢ ({10, 21, 25} : Finset ℕ)).filter
      (fun p => p.1 * 10 < 21 ∧ 21 < p.1 * 10 + p.2)).card = 6 := by
  have := card_adm member_witness
  norm_num at this ⊢
  exact this

theorem witness_a_overhang : (10 : ℕ) - 21 % 10 = 9 ∧ (9 : ℕ) ≠ 2 * 2 := by norm_num

end Erdos634.N1GapSubcases

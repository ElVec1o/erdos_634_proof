import Erdos634.E1NormalForm
import Erdos634.WallThird
import Erdos634.BaseCountsE1

/-!
# The positional base word of a congruent dissection of the `e = 1` target

Written 2026-09-12, sequential step 6 after `MarchCompose.lean` and `E1NormalForm.lean`.
`MarchCompose.base_word_dies` needs the base laid as `a^p b a^q c a^r` or `a^p c a^q b a^r`
(`p, r ≥ 1`) — `thm:e1reduce`(ii) in **positional** form.  The corpus had the arithmetic of the
counts (`BaseCountsE1`, counts only, never tied to a dissection — see `PAPER_MAP.md`'s
2026-09-10 vacuity finding) and the base chain as an ordered list of junctions
(`WallEndpoints.chain_endpoints`), but not their composition, and not the two end letters.

## What is proved (see the section headers)

* §A `base_chain` — **the base of the target is exactly partitioned by whole tile edges**: an
  increasing sequence `0 = X 0 < X 1 < … < X n = L` of junctions such that every `[X m, X (m+1)]`
  is an edge of a tile of `D` (two distinct vertices at the ends) of length `f`, `f²−1` or `f²`.
  This is `WallEndpoints.chain_endpoints` on the base line with the explicit functionals `−y`
  and `x`.
* §B `base_counts_of_chain` — the letter counts of that chain: exactly one `b`, and
  `(n_a, n_c) ∈ {(0,2), (f,1), (2f,0)}` (`BaseCountsE1.base_counts` on the **actual** counts of
  the chain, not an existentially packed triple).
* §C `first_edge_not_b`, `last_edge_not_b` — the edge at either base corner is an `a`- or a
  `c`-edge (the corner tile presents `β`; `MarchSlots.beta_corner_data`).
* §D the corner `c`-slot: with the slot's left end at the target's vertex there is no filler, and
  the two placements `junction_c_a`/`junction_c_b` leave at `V = (f², 0)` die differently — the
  cap's far vertex `(1/2, h_b)` is outside the target (`corner_bCapM_dies`), and the overshoot's
  run `[K, A]` is clamped at `A` by the **target boundary**, clamp (c) of `run_partition`
  (`corner_ext_outside`, `cslot_run_kill_outside`, `corner_bOverM_dies`).  This is exactly the
  "extension leaves `ABC`" step of `prop:cornerpara`'s proof, in coordinates, at the corner
  tile's `b`-edge.
* §E the four words the counts and §C leave that `base_word_dies` does not cover, each dead:
  `word_aba_dies` (`a^p b a^q`, `n_c = 0`), `word_c_p0_dies` (`c a^q b a^r`), `word_cbc_dies`
  (`c b c`, `n_c = 2`; one reflection via `reflCD`), `word_bfirst_r0_dies` (`a^p b a^q c`, the
  reflection of the second).  `laysARun_reflCD` transports a laid run through `reflCD`.
* §F `e1_family_f_ge_3` — **the composite, unconditional**: no `CongruentDissection` of
  `baseBetaTarget 1 f` (`f = n₀ ≥ 3`) with `ModelData`/`AngleData` exists.  The chain's word is
  read off its junction sequence (`X_run`, `laysARun_of_chain`) and every case is one of
  `base_word_dies`/§E.
* §G `e1_family_f_ge_3_congruent` — for a target merely *congruent* to `baseBetaTarget 1 n` and a
  model merely *congruent* to `modelTri n` (`E1NormalForm.normal_form`); `e1_family_f_ge_3_of_sides`
  — the model given by its three side lengths (SSS).

## What is NOT proved

`f = 2` (`N = 11`): `BaseCountsE1.base_counts` needs `f ≥ 3` (at `f = 2` the walk equation also
admits `n_b = 3`); that member is `tab:basebeta`'s search, not formalized.  `thm:e1reduce`(ii)'s
own clauses "`n_c = 1`" and "first and last are `a`" are **not** proved as statements: the cases
`n_c ∈ {0, 2}` and a `c` at an end are killed downstream instead (§E), and every statement about
a tiling of this target is now provable by ex falso — which is why no label is moved on that
account.  `prop:cornerpara` (the `b`-chord matched by exactly one tile) is not proved; only its
boundary clamp is realised, at one end, for the `c`-corner.  Nothing here touches `e ≥ 2`.

Axiom-clean beyond the standard three; no `sorry`.
-/

namespace Erdos634.E1BaseWord

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.RunPartition.CSlot Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Set

/-! ## A. The base chain, in coordinates -/

/-- The functional `−y`. -/
noncomputable def negY : Plane →ₗ[ℝ] ℝ where
  toFun p := -(p 1)
  map_add' := by intro a b; simp only [PiLp.add_apply]; ring
  map_smul' := by intro c a; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The functional `x`. -/
noncomputable def xco : Plane →ₗ[ℝ] ℝ where
  toFun p := p 0
  map_add' := by intro a b; simp only [PiLp.add_apply]
  map_smul' := by intro c a; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]

@[simp] theorem negY_apply (p : Plane) : negY p = -(p 1) := rfl
@[simp] theorem xco_apply (p : Plane) : xco p = p 0 := rfl

/-- `−y` as an affine map: the wall functional of the base. -/
noncomputable def gY : Plane →ᵃ[ℝ] ℝ := negY.toAffineMap

@[simp] theorem gY_apply (p : Plane) : gY p = -(p 1) := rfl
theorem gY_linear : gY.linear = negY := rfl

theorem negY_ne_zero : negY ≠ 0 := by
  intro h
  have := congrArg (fun F : Plane →ₗ[ℝ] ℝ => F (mkPt 0 1)) h
  simp at this

theorem hker_base : ∀ v : Plane, gY.linear v = 0 → xco v = 0 → v = 0 := by
  intro v h1 h2
  rw [gY_linear, negY_apply] at h1
  rw [xco_apply] at h2
  exact plane_ext (by simpa using h2) (by simp; linarith)

/-- A point with `y = 0` is `(x, 0)`. -/
theorem eq_mkPt_of_y_zero {p : Plane} (h : p 1 = 0) : p = mkPt (p 0) 0 :=
  plane_ext (by simp) (by simp [h])

theorem hiso_base : ∀ p q : Plane, gY p = 0 → gY q = 0 → dist p q = |xco p - xco q| := by
  intro p q hp hq
  rw [gY_apply, neg_eq_zero] at hp hq
  have h := dist_sq_pts p q
  rw [hp, hq, sub_zero] at h
  simp only [xco_apply]
  rw [← Real.sqrt_sq dist_nonneg, h, zero_pow two_ne_zero, add_zero, Real.sqrt_sq_eq_abs]

theorem lineMap_base (L t : ℝ) :
    AffineMap.lineMap (mkPt 0 0) (mkPt L 0) t = mkPt (t * L) 0 := by
  rw [lineMap_mkPt]; exact mkPt_congr (by ring) (by ring)

/-- The base segment, parametrised. -/
theorem mem_base_segment_iff {L : ℝ} (hL : 0 < L) (y : Plane) :
    y ∈ segment ℝ (mkPt 0 0) (mkPt L 0) ↔ y 1 = 0 ∧ 0 ≤ y 0 ∧ y 0 ≤ L := by
  rw [segment_eq_image_lineMap]
  constructor
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    rw [lineMap_base]
    refine ⟨by simp, by simp; positivity, by simp; nlinarith⟩
  · rintro ⟨h1, h0, hL'⟩
    refine ⟨y 0 / L, ⟨by positivity, by rw [div_le_one hL]; exact hL'⟩, ?_⟩
    rw [lineMap_base, div_mul_cancel₀ _ hL.ne']
    exact (eq_mkPt_of_y_zero h1).symm

theorem edgeWest_edgeEast_pts {N : ℕ} (D : Dissection N) (dir : Plane →ₗ[ℝ] ℝ)
    (e : Fin N × Fin 3) :
    (edgeWest D dir e = (D.tile e.1).pts e.2 ∧ edgeEast D dir e = (D.tile e.1).pts (e.2 + 1)) ∨
    (edgeWest D dir e = (D.tile e.1).pts (e.2 + 1) ∧ edgeEast D dir e = (D.tile e.1).pts e.2) := by
  classical
  unfold edgeWest edgeEast
  split
  · left; exact ⟨rfl, rfl⟩
  · right; exact ⟨rfl, rfl⟩

/-- **THE BASE CHAIN.**  For a congruent dissection of the `e = 1` target with `ModelData`, there
are `n ≥ 1` junctions `0 = X 0, X 1, …, X n = L` such that each `[X m, X (m+1)]` is the edge of
some tile between two of its distinct vertices, of length `f`, `f²−1` or `f²`. -/
theorem base_chain {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ) :
    ∃ (n : ℕ) (X : ℕ → ℝ), 0 < n ∧ X 0 = 0 ∧ X n = baseLen 1 f ∧
      (∀ m, m < n → X (m + 1) - X m = f ∨ X (m + 1) - X m = f ^ 2 - 1 ∨
        X (m + 1) - X m = f ^ 2) ∧
      (∀ m, m < n → ∃ (i : Fin N) (k k' : Fin 3), k ≠ k' ∧
        (D.tile i).pts k = mkPt (X m) 0 ∧ (D.tile i).pts k' = mkPt (X (m + 1)) 0) := by
  classical
  have hf1 : 1 < f := by linarith
  have hN : 0 < N := D.toDissection.pos
  have hL := baseLen_pos one_pos hf1
  have hH := height_pos one_pos hf1
  -- the wall setup on the base line `y = 0`
  have hwall : ∀ y ∈ D.target.carrier, gY y ≤ 0 := by
    intro y hy
    rw [htgt] at hy
    have := target_height_nonneg one_pos hf1 y hy
    rw [gY_apply]; linarith
  have hab : (mkPt 0 0 : Plane) ≠ mkPt (baseLen 1 f) 0 := mkPt_ne_of_fst hL.ne
  have hdirab : xco (mkPt 0 0) ≤ xco (mkPt (baseLen 1 f) 0) := by
    simp only [xco_apply, mkPt_zero]; exact hL.le
  have hbase : segment ℝ (mkPt 0 0) (mkPt (baseLen 1 f) 0) ⊆ frontier D.target.carrier := by
    intro y hy
    obtain ⟨h1, h0, hL'⟩ := (mem_base_segment_iff hL y).mp hy
    rw [htgt, eq_mkPt_of_y_zero h1]
    exact base_point_mem_frontier hf1 h0 hL'
  have hline : ∀ y ∈ segment ℝ (mkPt 0 0) (mkPt (baseLen 1 f) 0), gY y = 0 := by
    intro y hy
    obtain ⟨h1, -, -⟩ := (mem_base_segment_iff hL y).mp hy
    rw [gY_apply, h1, neg_zero]
  have hface : ∀ y ∈ D.target.carrier, gY y = 0 →
      y ∈ segment ℝ (mkPt 0 0) (mkPt (baseLen 1 f) 0) := by
    intro y hy hgy
    rw [gY_apply, neg_eq_zero] at hgy
    rw [htgt] at hy
    have hl := leftFunctional_carrier one_pos hf1 y hy
    have hr := rightFunctional_carrier one_pos hf1 y hy
    rw [hgy, mul_zero, sub_zero] at hl hr
    refine (mem_base_segment_iff hL y).mpr ⟨hgy, ?_, ?_⟩
    · by_contra h; push Not at h; nlinarith
    · by_contra h; push Not at h; nlinarith
  have hthird := hthird_general D.toDissection gY 0 (by rw [gY_linear]; exact negY_ne_zero) hwall
  obtain ⟨E, n, hneq, hn0, hwest, heast, hjunc, hmem, -, -, -, -, -⟩ :=
    chain_endpoints hN D.toDissection gY 0 xco hker_base hwall (mkPt 0 0) (mkPt (baseLen 1 f) 0)
      hab hdirab hbase hline hface hthird
  -- the endpoints of every chain edge are base points
  have hW0 : ∀ m, m < n → (edgeWest D.toDissection xco (E m)) 1 = 0 ∧
      (edgeEast D.toDissection xco (E m)) 1 = 0 := by
    intro m hm
    obtain ⟨hw1, hw2⟩ := (mem_wallList D.toDissection gY 0 (E m)).mp (hmem m hm)
    rw [gY_apply, neg_eq_zero] at hw1 hw2
    rcases edgeWest_edgeEast_pts D.toDissection xco (E m) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact ⟨hw1, hw2⟩
    · rw [h1, h2]; exact ⟨hw2, hw1⟩
  have hWeq : ∀ m, m < n → edgeWest D.toDissection xco (E m)
      = mkPt (edgePos D.toDissection xco (E m)) 0 := by
    intro m hm
    rw [← dir_edgeWest, xco_apply]
    exact eq_mkPt_of_y_zero (hW0 m hm).1
  have hEeq : ∀ m, m < n → edgeEast D.toDissection xco (E m)
      = mkPt (edgeEnd D.toDissection xco (E m)) 0 := by
    intro m hm
    rw [← dir_edgeEast, xco_apply]
    exact eq_mkPt_of_y_zero (hW0 m hm).2
  have hlen : ∀ m, m < n → edgeEnd D.toDissection xco (E m) - edgePos D.toDissection xco (E m)
      = dist ((D.tile (E m).1).pts (E m).2) ((D.tile (E m).1).pts ((E m).2 + 1)) := by
    intro m hm
    obtain ⟨hw1, hw2⟩ := (mem_wallList D.toDissection gY 0 (E m)).mp (hmem m hm)
    rw [hiso_base _ _ hw1 hw2]
    show _ = |xco ((D.tile (E m).1).pts (E m).2) - xco ((D.tile (E m).1).pts ((E m).2 + 1))|
    unfold edgeEnd edgePos
    rcases le_total (xco ((D.tile (E m).1).pts (E m).2))
        (xco ((D.tile (E m).1).pts ((E m).2 + 1))) with h | h
    · rw [min_eq_left h, max_eq_right h, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left h, abs_of_nonneg (by linarith)]
  set X : ℕ → ℝ := fun m => if m < n then edgePos D.toDissection xco (E m) else baseLen 1 f
    with hXdef
  have hXlt : ∀ m, m < n → X m = edgePos D.toDissection xco (E m) := fun m hm => if_pos hm
  have hXsucc : ∀ m, m < n → X (m + 1) = edgeEnd D.toDissection xco (E m) := by
    intro m hm
    rcases Nat.lt_or_ge (m + 1) n with h | h
    · rw [hXlt _ h, ← dir_edgeWest, ← hjunc m h, dir_edgeEast]
    · have hmn : m = n - 1 := by omega
      show (if m + 1 < n then _ else baseLen 1 f) = _
      rw [if_neg (by omega), ← dir_edgeEast, hmn, heast, xco_apply, mkPt_zero]
  refine ⟨n, X, hn0, ?_, ?_, ?_, ?_⟩
  · rw [hXlt 0 hn0, ← dir_edgeWest, hwest, xco_apply, mkPt_zero]
  · show (if n < n then _ else baseLen 1 f) = _
    rw [if_neg (lt_irrefl n)]
  · intro m hm
    rw [hXsucc m hm, hXlt m hm, hlen m hm]
    exact edge_length_cases D hM (E m).1 (E m).2
  · intro m hm
    have hne := fin3_succ_ne (E m).2
    rcases edgeWest_edgeEast_pts D.toDissection xco (E m) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨(E m).1, (E m).2, (E m).2 + 1, hne.2.1.symm, ?_, ?_⟩
      · rw [← h1, hWeq m hm, hXlt m hm]
      · rw [← h2, hEeq m hm, hXsucc m hm]
    · refine ⟨(E m).1, (E m).2 + 1, (E m).2, hne.2.1, ?_, ?_⟩
      · rw [← h1, hWeq m hm, hXlt m hm]
      · rw [← h2, hEeq m hm, hXsucc m hm]

/-! ## B. The counts of the chain -/

/-- The chain's junction sequence is strictly increasing, and telescopes to `L`. -/
theorem chain_sum {n : ℕ} (hn : 0 < n) (X : ℕ → ℝ) :
    ∑ m ∈ Finset.range n, (X (m + 1) - X m) = X n - X 0 := by
  have := Erdos634.ChainWalk.telescope n hn X (fun m => X (m + 1)) (fun _ _ => rfl)
  rw [this]; show X (n - 1 + 1) - X 0 = X n - X 0; rw [Nat.sub_add_cancel hn]

/-- **The letter counts of the base chain.**  With `f = n₀ ≥ 3`: exactly one `b`, and
`(n_a, n_c) ∈ {(0, 2), (n₀, 1), (2n₀, 0)}` — the counts are the *actual* filter cardinalities
of the chain. -/
theorem base_counts_of_chain {f : ℝ} {n₀ : ℕ} (hn : (n₀ : ℝ) = f) (hn3 : 3 ≤ n₀)
    {n : ℕ} (hn0 : 0 < n) (X : ℕ → ℝ) (hX0 : X 0 = 0) (hXn : X n = baseLen 1 f)
    (hℓ : ∀ m, m < n → X (m + 1) - X m = f ∨ X (m + 1) - X m = f ^ 2 - 1 ∨
        X (m + 1) - X m = f ^ 2) :
    ((Finset.range n).filter (fun m => X (m + 1) - X m = f ^ 2 - 1)).card = 1 ∧
    ((((Finset.range n).filter (fun m => X (m + 1) - X m = f)).card = 0 ∧
        ((Finset.range n).filter (fun m => X (m + 1) - X m = f ^ 2)).card = 2) ∨
      (((Finset.range n).filter (fun m => X (m + 1) - X m = f)).card = n₀ ∧
        ((Finset.range n).filter (fun m => X (m + 1) - X m = f ^ 2)).card = 1) ∨
      (((Finset.range n).filter (fun m => X (m + 1) - X m = f)).card = 2 * n₀ ∧
        ((Finset.range n).filter (fun m => X (m + 1) - X m = f ^ 2)).card = 0)) := by
  classical
  subst hn
  have hf : (3:ℝ) ≤ n₀ := by exact_mod_cast hn3
  have h1 : (n₀ : ℝ) ≠ (n₀ : ℝ) ^ 2 - 1 := by nlinarith
  have h2 : (n₀ : ℝ) ≠ (n₀ : ℝ) ^ 2 := by nlinarith
  have h3 : (n₀ : ℝ) ^ 2 - 1 ≠ (n₀ : ℝ) ^ 2 := by linarith
  have hwalk := Erdos634.ChainWalk.chain_walk n hn0 X (fun m => X (m + 1)) (n₀ : ℝ)
    ((n₀ : ℝ) ^ 2 - 1) ((n₀ : ℝ) ^ 2) h1 h2 h3 (fun _ _ => rfl)
    (fun m hm => by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact hℓ m (Finset.mem_range.mp hm))
  simp only at hwalk
  rw [show n - 1 + 1 = n by omega, hXn, hX0, baseLen_one, sub_zero] at hwalk
  set na := ((Finset.range n).filter (fun m => X (m + 1) - X m = (n₀ : ℝ))).card
  set nb := ((Finset.range n).filter (fun m => X (m + 1) - X m = (n₀ : ℝ) ^ 2 - 1)).card
  set nc := ((Finset.range n).filter (fun m => X (m + 1) - X m = (n₀ : ℝ) ^ 2)).card
  have hint : (na : ℤ) * n₀ + (nb : ℤ) * ((n₀ : ℤ) ^ 2 - 1) + (nc : ℤ) * (n₀ : ℤ) ^ 2
      = 3 * (n₀ : ℤ) ^ 2 - 1 := by
    have : ((na : ℤ) * n₀ + (nb : ℤ) * ((n₀ : ℤ) ^ 2 - 1) + (nc : ℤ) * (n₀ : ℤ) ^ 2 : ℤ)
        = ((3 * (n₀ : ℤ) ^ 2 - 1 : ℤ) : ℝ) := by
      push_cast; linarith [hwalk]
    exact_mod_cast this
  obtain ⟨hb, hcases⟩ := Erdos634.BaseCountsE1.base_counts n₀ na nb nc (by exact_mod_cast hn3)
    (by positivity) (by positivity) (by positivity) hint
  refine ⟨by exact_mod_cast hb, ?_⟩
  rcases hcases with ⟨ha, hc⟩ | ⟨ha, hc⟩ | ⟨ha, hc⟩
  · left; exact ⟨by exact_mod_cast ha, by exact_mod_cast hc⟩
  · right; left; exact ⟨by exact_mod_cast ha, by exact_mod_cast hc⟩
  · right; right; exact ⟨by exact_mod_cast ha, by exact_mod_cast hc⟩

/-! ## C. The corner edges are not `b` -/

/-- `β` is the model angle `modelBeta 1 f`, for any model with `ModelData` — the law of cosines
on the model's own vertex `1`. -/
theorem beta_eq_modelBeta {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (hM : ModelData D f α β γ) : β = modelBeta 1 f := by
  have hf1 : 1 < f := by linarith
  have hf0 : (0:ℝ) < f := by linarith
  have hs0 : dist (D.model.pts 1) (D.model.pts 2) = f := hM.hs0
  have hs1 : dist (D.model.pts 2) (D.model.pts 0) = f ^ 2 - 1 := hM.hs1
  have hs2 : dist (D.model.pts 0) (D.model.pts 1) = f ^ 2 := hM.hs2
  have hcos := Erdos634.AngleThreshold.cos_of_sides (D.model.pts 2) (D.model.pts 1) (D.model.pts 0)
    (by rw [dist_comm, hs0]; exact hf0.ne') (by rw [hs2]; positivity)
  rw [hM.hβ', dist_comm (D.model.pts 2), hs0, hs2, hs1] at hcos
  have hb := cos_modelBeta one_pos hf1
  rw [← hM.hβ']
  refine cornerAngle_eq_of_cos (modelBeta_mem one_pos hf1).1.le
    (by linarith [(modelBeta_mem one_pos hf1).2, Real.pi_pos]) ?_
  rw [hM.hβ', hcos, hb, baseLen_one]
  field_simp
  ring

/-- The eleven distinctness facts `TileAt` consumes, from `AngleData`. -/
theorem distinct_of_angleData {α β γ : ℝ} (hA : AngleData α β γ) :
    α ≠ β ∧ α ≠ γ ∧ α ≠ Real.pi ∧ α ≠ 0 ∧ β ≠ γ ∧ β ≠ Real.pi ∧ β ≠ 0 ∧ β ≠ 2 * Real.pi ∧
      γ ≠ Real.pi ∧ γ ≠ 0 ∧ Real.pi ≠ 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    distinct_of_pos_ne hA.hα hA.hβ hA.hαβ hA.hγdef hA.hrel
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_, h8, h9, h10⟩
  have := hA.hrel; have := hA.hα; have := Real.pi_pos
  intro h; linarith

/-- **The tile with a vertex at the left base corner `(0,0)` presents `β` there.** -/
theorem corner_tile_beta {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {i : Fin N} {k : Fin 3} (hk : (D.tile i).pts k = mkPt 0 0) :
    (D.tile i).localAngle (mkPt 0 0) = β := by
  have hf1 : 1 < f := by linarith
  obtain ⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hβ2π, hγπ, hγ0, hπ0⟩ := distinct_of_angleData hA
  have hcorner : cornerAngle (D.target.pts (0 + 1)) (D.target.pts 0) (D.target.pts (0 + 2)) = β := by
    rw [htgt, beta_eq_modelBeta D hf hM]
    exact cornerAngle_base₀ one_pos hf1
  obtain ⟨i₀, j₀, hij, hang, huniq⟩ := congruentDissection_base_corner_tile_vertex D α β γ hαβ hαγ
    hαπ hα0 hβγ hβπ hβ0 hβ2π hγπ hγ0 hπ0 hA.hγdef hA.hrel hA.hirr hM.hα' hM.hβ' hM.hγ' 0 hcorner
  have h0 : D.target.pts 0 = mkPt 0 0 := by rw [htgt]; rfl
  rw [h0] at hang huniq
  have hi : i = i₀ := huniq i (by rw [← hk]; exact subset_convexHull ℝ _ ⟨k, rfl⟩)
  rw [hi]; exact hang

/-- **The tile with a vertex at the right base corner `(L,0)` presents `β` there.** -/
theorem corner_tile_beta' {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {i : Fin N} {k : Fin 3}
    (hk : (D.tile i).pts k = mkPt (baseLen 1 f) 0) :
    (D.tile i).localAngle (mkPt (baseLen 1 f) 0) = β := by
  have hf1 : 1 < f := by linarith
  obtain ⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hβ2π, hγπ, hγ0, hπ0⟩ := distinct_of_angleData hA
  have hcorner : cornerAngle (D.target.pts (1 + 1)) (D.target.pts 1) (D.target.pts (1 + 2)) = β := by
    rw [htgt, beta_eq_modelBeta D hf hM]
    have h := cornerAngle_base₁ one_pos hf1
    rwa [show ((1 : Fin 3) + 1) = 2 by decide, show ((1 : Fin 3) + 2) = 0 by decide]
  obtain ⟨i₀, j₀, hij, hang, huniq⟩ := congruentDissection_base_corner_tile_vertex D α β γ hαβ hαγ
    hαπ hα0 hβγ hβπ hβ0 hβ2π hγπ hγ0 hπ0 hA.hγdef hA.hrel hA.hirr hM.hα' hM.hβ' hM.hγ' 1 hcorner
  have h1 : D.target.pts 1 = mkPt (baseLen 1 f) 0 := by rw [htgt]; rfl
  rw [h1] at hang huniq
  have hi : i = i₀ := huniq i (by rw [← hk]; exact subset_convexHull ℝ _ ⟨k, rfl⟩)
  rw [hi]; exact hang

/-- An edge from a vertex where the tile presents `β` has length `a` or `c`. -/
theorem edge_at_beta_vertex {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (hM : ModelData D f α β γ) (hA : AngleData α β γ) {i : Fin N} {k k' : Fin 3} (hkk : k ≠ k')
    (hβ : (D.tile i).localAngle ((D.tile i).pts k) = β) :
    dist ((D.tile i).pts k) ((D.tile i).pts k') = f ∨
    dist ((D.tile i).pts k) ((D.tile i).pts k') = f ^ 2 := by
  obtain ⟨k₀, hk₀, -, hsides⟩ := beta_corner_data D hf hM hA hβ
  have hkk₀ : k₀ = k := (D.tile i).indep.injective hk₀
  subst hkk₀
  have hcov : ∀ a b : Fin 3, a ≠ b → b = a + 1 ∨ b = a + 2 := by decide
  rcases hcov k₀ k' hkk with rfl | rfl
  · rcases hsides with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  · rcases hsides with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inr h
    · exact Or.inl h

/-- **The first base edge is not `b`.** -/
theorem first_edge_not_b {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {i : Fin N} {k k' : Fin 3} (hkk : k ≠ k')
    (hk : (D.tile i).pts k = mkPt 0 0) {x : ℝ} (hk' : (D.tile i).pts k' = mkPt x 0) :
    x = f ∨ x = f ^ 2 := by
  have hβ : (D.tile i).localAngle ((D.tile i).pts k) = β := by
    rw [hk]; exact corner_tile_beta D hf htgt hM hA hk
  have h := edge_at_beta_vertex D hf hM hA hkk hβ
  have hx : 0 ≤ x := by
    have := pts_mem_target D.toDissection i k'
    rw [hk', htgt] at this
    have := leftFunctional_carrier one_pos (by linarith) _ this
    simp only [mkPt_zero, mkPt_one, mul_zero, sub_zero] at this
    have hH := height_pos one_pos (by linarith : 1 < f)
    by_contra hc; push Not at hc; nlinarith
  rw [hk, hk', show x = 0 + x by ring, dist_mkPt_base 0 x hx] at h
  rcases h with h | h
  · left; linarith
  · right; linarith

/-- **The last base edge is not `b`.** -/
theorem last_edge_not_b {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {i : Fin N} {k k' : Fin 3} (hkk : k ≠ k') {x : ℝ}
    (hk : (D.tile i).pts k = mkPt x 0) (hk' : (D.tile i).pts k' = mkPt (baseLen 1 f) 0) :
    baseLen 1 f - x = f ∨ baseLen 1 f - x = f ^ 2 := by
  have hβ : (D.tile i).localAngle ((D.tile i).pts k') = β := by
    rw [hk']; exact corner_tile_beta' D hf htgt hM hA hk'
  have h := edge_at_beta_vertex D hf hM hA hkk.symm hβ
  have hx : x ≤ baseLen 1 f := by
    have := pts_mem_target D.toDissection i k
    rw [hk, htgt] at this
    have := rightFunctional_carrier one_pos (by linarith) _ this
    simp only [mkPt_zero, mkPt_one, mul_zero, sub_zero] at this
    have hH := height_pos one_pos (by linarith : 1 < f)
    by_contra hc; push Not at hc; nlinarith
  rw [hk, hk', dist_comm, show baseLen 1 f = x + (baseLen 1 f - x) by ring,
    dist_mkPt_base x _ (by linarith)] at h
  rcases h with h | h
  · left; linarith
  · right; linarith


/-! ## D. The corner `c`-slot: the cap and the overshoot die at the corner

`junction_c_a`/`junction_c_b` at the right end `V = (f², 0)` of a corner `c`-slot deliver, on the
`GB`/`bSlotTile` branch, a `β`-tile at `V` with vertex set `bCapMSet f² f` or `bOverMSet f² f`.
Inside the base (`MarchCompose`) those die against the filler at the slot's left end `B`; at the
corner there is no filler — `B = (0, 0)` is the target's vertex — and the kills are different:
the cap's far vertex `(1/2, h_b)` lies outside the target (across the left side), and the
overshoot's run `[K, A]` of length `b − a` is clamped at `A` by the **target boundary** (clamp
(c) of `RunPartition`): `A` is on the left side and the extension `(A, A')` leaves the target.
This is `prop:cornerpara`'s own "the extension leaves `ABC`" argument, at the corner tile's
`b`-edge. -/

/-- The left-side functional of the `e = 1` target: `≥ 0` on the target. -/
noncomputable def leftF (f : ℝ) (p : Plane) : ℝ := p 0 * height 1 f - baseLen 1 f / 2 * p 1

theorem leftF_A' {f : ℝ} (hf : 2 ≤ f) :
    leftF f (Apt' (f ^ 2) f) = -(height 1 f * f ^ 2 / (2 * (f ^ 2 - 1))) := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have hb : f ^ 2 - 1 ≠ 0 := (by nlinarith : (0:ℝ) < f ^ 2 - 1).ne'
  simp only [leftF, Apt', mkPt_zero, mkPt_one]; unfold apexH; rw [baseLen_one]; field_simp; ring

theorem leftF_A {f : ℝ} (hf : 2 ≤ f) : leftF f (Apt (f ^ 2) f) = 0 := by
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  simp only [leftF, Apt, mkPt_zero, mkPt_one, hC]; unfold apexH Erdos634.MarchCoords.dBG; rw [baseLen_one]
  field_simp; ring

theorem leftF_smul_add (f a b : ℝ) (p q : Plane) :
    leftF f (a • p + b • q) = a * leftF f p + b * leftF f q := by
  simp only [leftF, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- **The extension `(A, A')` of the corner slot's `b`-edge beyond `A` leaves the target.** -/
theorem corner_ext_outside {N : ℕ} (D : CongruentDissection N) {f : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) :
    ∀ y ∈ openSegment ℝ (Apt' (f ^ 2) f) (Apt (f ^ 2) f), y ∉ D.target.carrier := by
  have hf1 : 1 < f := by linarith
  rintro y ⟨a, b, ha, hb, hab, rfl⟩ hmem
  rw [htgt] at hmem
  have h := leftFunctional_carrier one_pos hf1 _ hmem
  change 0 ≤ leftF f (a • Apt' (f ^ 2) f + b • Apt (f ^ 2) f) at h
  rw [leftF_smul_add, leftF_A' hf, leftF_A hf] at h
  have hb2 : (0:ℝ) < f ^ 2 - 1 := by nlinarith
  have hH := height_pos one_pos hf1
  have : 0 < height 1 f * f ^ 2 / (2 * (f ^ 2 - 1)) := by positivity
  nlinarith

/-- **The corner cap dies**: its far vertex `(1/2, h_b)` is outside the target. -/
theorem corner_bCapM_dies {N : ℕ} (D : CongruentDissection N) {f : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith))
    {l : Fin N} (hl : Set.range (D.tile l).pts = bCapMSet (f ^ 2) f) : False := by
  have hf1 : 1 < f := by linarith
  have hf0 : f ≠ 0 := (by linarith : (0:ℝ) < f).ne'
  have hb : (0:ℝ) < f ^ 2 - 1 := by nlinarith
  obtain ⟨k, hk⟩ := mem_range_of_eq hl
    (P := mkPt (f ^ 2 - (f ^ 2 - 1) - 1 / 2) (hB f)) (by simp [bCapMSet])
  have hmem := pts_mem_target D.toDissection l k
  rw [hk, htgt] at hmem
  have h := leftFunctional_carrier one_pos hf1 _ hmem
  simp only [mkPt_zero, mkPt_one] at h
  have e : (f ^ 2 - (f ^ 2 - 1) - 1 / 2) * height 1 f - baseLen 1 f / 2 * hB f
      = -(height 1 f * f ^ 2 / (f ^ 2 - 1)) := by
    simp only [hB]; unfold apexH; rw [baseLen_one]; field_simp; ring
  rw [e] at h
  have hH := height_pos one_pos hf1
  have : 0 < height 1 f * f ^ 2 / (f ^ 2 - 1) := by positivity
  linarith

/-- **The `c`-slot run kill with the clamp at `A` by the target boundary** —
`RunPartition.cslot_run_kill` with its filler hypothesis replaced by "the extension `(A, A')`
is outside the target" (clamp (c)).  Same proof otherwise. -/
theorem cslot_run_kill_outside {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    {n : ℕ} (hn : (n : ℝ) = f) (hn3 : 3 ≤ n)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    {x₀ : ℝ} (hx : f ^ 2 ≤ x₀) (hL : x₀ + f ≤ baseLen 1 f) {i l : Fin N}
    (hi : Set.range (D.tile i).pts = Set.range (cSlotTile (x₀ - f ^ 2) f (by linarith)).pts)
    {W : Plane} (hW : Fc f W < cc x₀ f)
    (hl : Set.range (D.tile l).pts = {Vpt x₀, Kpt x₀ f, W})
    (hout : ∀ y ∈ openSegment ℝ (Apt' x₀ f) (Apt x₀ f), y ∉ D.target.carrier) : False := by
  classical
  have hf1 : 1 < f := by linarith
  have hX := Xc_pos hf
  have hF : Fc f ≠ 0 := lineF_ne_zero hX.ne'
  have hFV := Fc_V hf x₀
  have hFA := Fc_A hf x₀
  have hFK := Fc_K hf x₀
  have hFA' := Fc_A' hf x₀
  have hKA := K_ne_A hf x₀
  have hVA := V_ne_A hf x₀
  have hKopen := K_mem_open hf x₀
  have hAopen := A_mem_open hf x₀
  rw [cSlot_range_eq hf1] at hi
  obtain ⟨ki, hki, -⟩ := edge_index_of_range hi
  have hVA_edge : segment ℝ (Vpt x₀) (Apt x₀ f) ⊆ (D.tile i).edge ki := by
    rcases hki with h | h
    · rw [h]
    · rw [h, segment_symm]
  obtain ⟨kl, hkl, hklW⟩ := edge_index_of_range hl
  have hVK_edge : (D.tile l).edge kl = segment ℝ (Vpt x₀) (Kpt x₀ f) := by
    rcases hkl with h | h
    · exact h
    · rw [h, segment_symm]
  have hle_l : ∀ y ∈ (D.tile l).carrier, Fc f y ≤ cc x₀ f := by
    refine (D.tile l).carrier_subset_halfplane _ _ ?_
    intro idx
    have hmem : (D.tile l).pts idx ∈ ({Vpt x₀, Kpt x₀ f, W} : Set Plane) := hl ▸ ⟨idx, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h | h <;> rw [h]
    · exact hFV.le
    · exact hFK.le
    · exact hW.le
  have hE_l : ∀ y ∈ (D.tile l).edge kl, Fc f y = cc x₀ f := by
    rw [hVK_edge]; exact fun y hy => segment_subset_level _ _ hFV hFK hy
  have hS : segment ℝ (Kpt x₀ f) (Apt x₀ f) ⊆ {y | Fc f y = cc x₀ f} :=
    segment_subset_level _ _ hFK hFA
  have hKA_sub : segment ℝ (Kpt x₀ f) (Apt x₀ f) ⊆ segment ℝ (Vpt x₀) (Apt x₀ f) :=
    (convex_segment _ _).segment_subset (openSegment_subset_segment ℝ _ _ hKopen)
      (right_mem_segment ℝ _ _)
  have hint : openSegment ℝ (Kpt x₀ f) (Apt x₀ f) ⊆ interior D.target.carrier := by
    rw [htgt]
    exact (baseBetaTarget 1 f one_pos hf1).convex.openSegment_interior_closure_subset_interior
      (K_mem_interior hf x₀ hx hL) (subset_closure (A_mem_target hf x₀ hx hL))
  have hwall : ∀ y ∈ openSegment ℝ (Kpt x₀ f) (Apt x₀ f), ∀ j, y ∉ interior (D.tile j).carrier := by
    intro y hy j
    exact D.edge_point_not_interior (hVA_edge (hKA_sub (openSegment_subset_segment ℝ _ _ hy))) j
  have hP : ∀ e ∈ D.lineChain (Fc f) (cc x₀ f),
      ¬ Straddles ((D.tile e.1).edge e.2) (Vpt x₀) (Kpt x₀ f) (Apt x₀ f) := by
    intro e he
    by_cases hel : e.1 = l
    · by_cases hek : e.2 = kl
      · have heq : e = (l, kl) := Prod.ext hel hek
        rw [heq]
        exact not_straddles_extension (Fc f) hF (cc x₀ f) hKA hFK hFA hFV hKopen
          (by rw [hVK_edge])
      · exfalso
        have hWe : W ∈ (D.tile e.1).edge e.2 := by rw [hel]; exact hklW e.2 hek
        have := D.lineChain_edge_subset he W hWe
        linarith
    · exact not_straddles_of_sameside_edge D.toDissection (Fc f) hF (cc x₀ f) hKA hFK hFA hFV
        hKopen hle_l hE_l (by rw [hVK_edge]) he (fun h => hel (by rw [h]))
  have hQ : ∀ e ∈ D.lineChain (Fc f) (cc x₀ f),
      ¬ Straddles ((D.tile e.1).edge e.2) (Apt' x₀ f) (Apt x₀ f) (Kpt x₀ f) :=
    fun e _ => not_straddles_of_outside D.toDissection hout e.1 e.2
  exact run_b_sub_a_dies D hM hn hn3 (Fc f) hF (cc x₀ f) hKA hFV hFA' hKopen hAopen hS hint hwall
    hP hQ (dist_K_A hf x₀)

/-- **The corner overshoot dies**: the run `[K, A]` clamped at `A` by the target boundary. -/
theorem corner_bOverM_dies {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    {n : ℕ} (hn : (n : ℝ) = f) (hn3 : 3 ≤ n)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    {i l : Fin N}
    (hi : Set.range (D.tile i).pts = Set.range (cSlotTile (f ^ 2 - f ^ 2) f (by linarith)).pts)
    (hl : Set.range (D.tile l).pts = bOverMSet (f ^ 2) f) : False :=
  cslot_run_kill_outside D hf hn hn3 htgt hM le_rfl (by rw [baseLen_one]; nlinarith) hi
    (Fc_O_lt hf _) (by rw [hl, bOverMSet_eq]) (corner_ext_outside D hf htgt)

/-- **The tile laying `[0, f²]` from the corner is `cSlotTile 0`** (`β` at the corner; the other
reflection presents `α` there). -/
theorem corner_c_tile {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {i : Fin N} {k m : Fin 3} (hkm : k ≠ m)
    (hk : (D.tile i).pts k = mkPt 0 0) (hm : (D.tile i).pts m = mkPt (f ^ 2) 0) :
    Set.range (D.tile i).pts = Set.range (cSlotTile (f ^ 2 - f ^ 2) f (by linarith)).pts := by
  have hm' : (D.tile i).pts m = mkPt (0 + f ^ 2) 0 := by rw [hm, zero_add]
  rcases c_letter_tile D hf htgt hM hkm hk hm' with h | h
  · rw [h]; congr 3; ring
  · exfalso
    have hβ := corner_tile_beta D hf htgt hM hA hk
    have hα := (cSlot'_angles D hf hM h).1
    exact hA.hαβ (hα.symm.trans hβ)

/-! ## E. The words the counts leave that `base_word_dies` does not cover -/

/-- **`a^p b a^q` (`n_c = 0`, `p + q = 2f`, `p, q ≥ 1`) dies**: `first_run`, `junction_a_b`
(the `b`-tile is `bSlotTile'`), `bslot'_then_run_dies`. -/
theorem word_aba_dies {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    {n : ℕ} (hn : (n : ℝ) = f) (hn3 : 3 ≤ n)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : p + q = 2 * n)
    (hrun1 : LaysARun D f 0 p)
    {jb : Fin N} {kb mb : Fin 3} (hkmb : kb ≠ mb)
    (hkb : (D.tile jb).pts kb = mkPt (p * f) 0)
    (hmb : (D.tile jb).pts mb = mkPt (p * f + (f ^ 2 - 1)) 0)
    (hrun2 : LaysARun D f (p * f + (f ^ 2 - 1)) q) : False := by
  have hf1 : 1 < f := by linarith
  have hf0 : (0:ℝ) < f := by linarith
  have hb : (0:ℝ) < f ^ 2 - 1 := by nlinarith
  have hp' : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hsum : (p:ℝ) + q = 2 * f := by rw [← hn]; exact_mod_cast hpq
  have hL' := baseLen_one f
  have hfit : p * f + (f ^ 2 - 1) + q * f = baseLen 1 f := by
    rw [hL']; linear_combination f * hsum
  have hpf : f ≤ p * f := by nlinarith
  have hqf : f ≤ q * f := by nlinarith
  obtain ⟨-, ⟨i1, hi1⟩, -⟩ := first_run D hf htgt hM hA hp (by linarith) hrun1
  have hi1' : Set.range (D.tile i1).pts = Set.range (aTileBG (p * f - f) f hf1).pts := hi1
  obtain ⟨hjb, -⟩ := junction_a_b D hf htgt hM hA (x₀ := p * f) (by linarith) (by linarith)
    hi1' hkmb hkb hmb
  exact bslot'_then_run_dies D hf htgt hM hA (Y := p * f) (by linarith) hq hfit hrun2 hjb

/-- **`c a^q b a^r` (`p = 0`, `r ≥ 1`, `q + r = f`) dies** at the corner slot: the corner tile is
`cSlotTile 0`; at `V = (f², 0)` the `GB`/`bSlotTile` branch leaves a cap or overshoot, both dead
at the corner; the `BG`/`bSlotTile'` branch restarts the march and dies at the far corner. -/
theorem word_c_p0_dies {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    {n : ℕ} (hn : (n : ℝ) = f) (hn3 : 3 ≤ n)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {q r : ℕ} (hr : 1 ≤ r) (hqr : q + r = n)
    {jc : Fin N} {kc mc : Fin 3} (hkmc : kc ≠ mc)
    (hkc : (D.tile jc).pts kc = mkPt 0 0) (hmc : (D.tile jc).pts mc = mkPt (f ^ 2) 0)
    (hrun2 : LaysARun D f (f ^ 2) q)
    {jb : Fin N} {kb mb : Fin 3} (hkmb : kb ≠ mb)
    (hkb : (D.tile jb).pts kb = mkPt (f ^ 2 + q * f) 0)
    (hmb : (D.tile jb).pts mb = mkPt (f ^ 2 + q * f + (f ^ 2 - 1)) 0)
    (hrun3 : LaysARun D f (f ^ 2 + q * f + (f ^ 2 - 1)) r) : False := by
  have hf1 : 1 < f := by linarith
  have hf0 : (0:ℝ) < f := by linarith
  have hb : (0:ℝ) < f ^ 2 - 1 := by nlinarith
  have hc0 : (0:ℝ) < f ^ 2 := by positivity
  have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hqf : 0 ≤ (q:ℝ) * f := by positivity
  have hrf : f ≤ r * f := by nlinarith
  have hsum : (q:ℝ) + r = f := by rw [← hn]; exact_mod_cast hqr
  have hL' := baseLen_one f
  have hfit : f ^ 2 + q * f + (f ^ 2 - 1) + r * f = baseLen 1 f := by
    rw [hL']; linear_combination f * hsum
  have hc := corner_c_tile D hf htgt hM hA hkmc hkc hmc
  have hxL : f ^ 2 < baseLen 1 f := by linarith
  rcases Nat.eq_zero_or_pos q with hq0 | hq1
  · subst hq0
    simp only [Nat.cast_zero, zero_mul, add_zero] at hkb hmb hrun3 hfit
    rcases junction_c_b D hf htgt hM hA (x₀ := f ^ 2) hc0 hxL hc hkmb hkb hmb with
      ⟨-, l, -, -, -, -, hcap | hover⟩ | ⟨hjb, -⟩
    · exact corner_bCapM_dies D hf htgt hcap
    · exact corner_bOverM_dies D hf hn hn3 htgt hM hc hover
    · exact bslot'_then_run_dies D hf htgt hM hA (Y := f ^ 2) hc0 hr hfit hrun3 hjb
  · obtain ⟨ja, ka, ma, hkma, hka, hma⟩ := run_first D hq1 hrun2
    rcases junction_c_a D hf htgt hM hA (x₀ := f ^ 2) hc0 hxL hc hkma hka hma with
      ⟨-, l, -, -, -, -, hcap | hover⟩ | ⟨hja, -⟩
    · exact corner_bCapM_dies D hf htgt hcap
    · exact corner_bOverM_dies D hf hn hn3 htgt hM hc hover
    · exact bg_then_b_then_run_dies D hf htgt hM hA (x₀ := f ^ 2) hc0 hq1 hrun2 ⟨ja, hja⟩
        hkmb hkb hmb hr hfit hrun3

/-- **`c b …` with the `b`-tile `bSlotTile f²` dies** at the corner: `junction_c_b` leaves the cap
or the overshoot (dead at the corner) or the other reflection (a different vertex set). -/
theorem cbc_bslot_dies {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    {n : ℕ} (hn : (n : ℝ) = f) (hn3 : 3 ≤ n)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {i j : Fin N}
    (hi : Set.range (D.tile i).pts = Set.range (cSlotTile (f ^ 2 - f ^ 2) f (by linarith)).pts)
    {kb mb : Fin 3} (hkmb : kb ≠ mb)
    (hkb : (D.tile j).pts kb = mkPt (f ^ 2) 0)
    (hmb : (D.tile j).pts mb = mkPt (f ^ 2 + (f ^ 2 - 1)) 0)
    (hj : Set.range (D.tile j).pts = Set.range (bSlotTile (f ^ 2) f (by linarith)).pts) :
    False := by
  have hf1 : 1 < f := by linarith
  have hc0 : (0:ℝ) < f ^ 2 := by positivity
  have hxL : f ^ 2 < baseLen 1 f := by rw [baseLen_one]; nlinarith
  rcases junction_c_b D hf htgt hM hA (x₀ := f ^ 2) hc0 hxL hi hkmb hkb hmb with
    ⟨-, l, -, -, -, -, hcap | hover⟩ | ⟨hj', -⟩
  · exact corner_bCapM_dies D hf htgt hcap
  · exact corner_bOverM_dies D hf hn hn3 htgt hM hi hover
  · rw [hj, range_bSlotTile, range_bSlotTile'] at hj'
    have hmem : mkPt (f ^ 2 - 1 / 2) (f / (f ^ 2 - 1) * apexH f) ∈
        ({mkPt (f ^ 2) 0, mkPt (f ^ 2 + (f ^ 2 - 1)) 0,
          mkPt (f ^ 2 + (f ^ 2 - 1) + 1 / 2) (f / (f ^ 2 - 1) * apexH f)} : Set Plane) := by
      rw [← hj']; simp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h | h
    · exact absurd h (mkPt_ne_of_fst (by linarith))
    · exact absurd h (mkPt_ne_of_fst (by nlinarith))
    · exact absurd h (mkPt_ne_of_fst (by nlinarith))

/-! ### The reflection transports the laid letters -/

theorem reflCD_pts {N : ℕ} (D : CongruentDissection N) {f : ℝ} (hf1 : 1 < f)
    (htgt : D.target = baseBetaTarget 1 f one_pos hf1) (t : Fin N) (k : Fin 3) :
    ((reflCD D hf1 htgt).tile t).pts k
      = (reflX (baseLen 1 f)).toAffineEquiv ((D.tile t).pts k) := rfl

theorem reflCD_pts_base {N : ℕ} (D : CongruentDissection N) {f : ℝ} (hf1 : 1 < f)
    (htgt : D.target = baseBetaTarget 1 f one_pos hf1) {t : Fin N} {k : Fin 3} {x : ℝ}
    (h : (D.tile t).pts k = mkPt x 0) :
    ((reflCD D hf1 htgt).tile t).pts k = mkPt (baseLen 1 f - x) 0 := by
  rw [reflCD_pts, h, reflX_toAffineEquiv_apply]

/-- A laid `a`-run `[t, t + mf]` reflects to the laid run `[L − t − mf, L − t]`. -/
theorem laysARun_reflCD {N : ℕ} (D : CongruentDissection N) {f : ℝ} (hf1 : 1 < f)
    (htgt : D.target = baseBetaTarget 1 f one_pos hf1) {t : ℝ} {m : ℕ}
    (h : LaysARun D f t m) :
    LaysARun (reflCD D hf1 htgt) f (baseLen 1 f - t - m * f) m := by
  intro j hj
  obtain ⟨i, k, k', hkk, hk, hk'⟩ := h (m - 1 - j) (by omega)
  have hcast : ((m - 1 - j : ℕ) : ℝ) = m - 1 - j := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  refine ⟨i, k', k, hkk.symm, ?_, ?_⟩
  · rw [reflCD_pts_base D hf1 htgt hk', hcast]; exact mkPt_congr (by ring) rfl
  · rw [reflCD_pts_base D hf1 htgt hk, hcast]; exact mkPt_congr (by ring) rfl

/-- **`c b c` (`n_c = 2`, `n_a = 0`) dies.**  The `b`-tile is `bSlotTile f²` (then
`cbc_bslot_dies`) or `bSlotTile' f²`; in the reflection the latter is `bSlotTile f²` at the
mirrored corner slot, and `cbc_bslot_dies` applies there. -/
theorem word_cbc_dies {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    {n : ℕ} (hn : (n : ℝ) = f) (hn3 : 3 ≤ n)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ)
    {i : Fin N} {ki mi : Fin 3} (hkmi : ki ≠ mi)
    (hki : (D.tile i).pts ki = mkPt 0 0) (hmi : (D.tile i).pts mi = mkPt (f ^ 2) 0)
    {j : Fin N} {kj mj : Fin 3} (hkmj : kj ≠ mj)
    (hkj : (D.tile j).pts kj = mkPt (f ^ 2) 0)
    (hmj : (D.tile j).pts mj = mkPt (f ^ 2 + (f ^ 2 - 1)) 0)
    {i' : Fin N} {ki' mi' : Fin 3} (hkmi' : ki' ≠ mi')
    (hki' : (D.tile i').pts ki' = mkPt (f ^ 2 + (f ^ 2 - 1)) 0)
    (hmi' : (D.tile i').pts mi' = mkPt (f ^ 2 + (f ^ 2 - 1) + f ^ 2) 0) : False := by
  have hf1 : 1 < f := by linarith
  have hc := corner_c_tile D hf htgt hM hA hkmi hki hmi
  rcases b_letter_tile D hf htgt hM hkmj hkj hmj with hj | hj
  · exact cbc_bslot_dies D hf hn hn3 htgt hM hA hc hkmj hkj hmj hj
  · have hL := baseLen_one f
    have hM' := reflCD_modelData D hf1 htgt hM
    have hki'' : ((reflCD D hf1 htgt).tile i').pts mi' = mkPt 0 0 := by
      rw [reflCD_pts_base D hf1 htgt hmi', hL]; exact mkPt_congr (by ring) rfl
    have hmi'' : ((reflCD D hf1 htgt).tile i').pts ki' = mkPt (f ^ 2) 0 := by
      rw [reflCD_pts_base D hf1 htgt hki', hL]; exact mkPt_congr (by ring) rfl
    have hc' := corner_c_tile (reflCD D hf1 htgt) hf rfl hM' hA hkmi'.symm hki'' hmi''
    have hkj' : ((reflCD D hf1 htgt).tile j).pts mj = mkPt (f ^ 2) 0 := by
      rw [reflCD_pts_base D hf1 htgt hmj, hL]; exact mkPt_congr (by ring) rfl
    have hmj' : ((reflCD D hf1 htgt).tile j).pts kj = mkPt (f ^ 2 + (f ^ 2 - 1)) 0 := by
      rw [reflCD_pts_base D hf1 htgt hkj, hL]; exact mkPt_congr (by ring) rfl
    have hj' : Set.range ((reflCD D hf1 htgt).tile j).pts
        = Set.range (bSlotTile (f ^ 2) f hf1).pts := by
      rw [reflCD_range, hj, range_bSlotTile', image_triple, range_bSlotTile]
      simp only [reflX_toAffineEquiv_apply]
      rw [Set.insert_comm]
      exact triple_congr (mkPt_congr (by rw [hL]; ring) rfl) (mkPt_congr (by rw [hL]; ring) rfl)
        (mkPt_congr (by rw [hL]; ring) rfl)
    exact cbc_bslot_dies (reflCD D hf1 htgt) hf hn hn3 rfl hM' hA hc' hkmj.symm hkj' hmj' hj'

/-- **`a^p b a^q c` (`r = 0`, `p ≥ 1`, `p + q = f`) dies**: it is `c a^q b a^p` in the
reflection, and `word_c_p0_dies` applies there. -/
theorem word_bfirst_r0_dies {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    {n : ℕ} (hn : (n : ℝ) = f) (hn3 : 3 ≤ n)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) {p q : ℕ} (hp : 1 ≤ p) (hpq : p + q = n)
    (hrun1 : LaysARun D f 0 p)
    {jb : Fin N} {kb mb : Fin 3} (hkmb : kb ≠ mb)
    (hkb : (D.tile jb).pts kb = mkPt (p * f) 0)
    (hmb : (D.tile jb).pts mb = mkPt (p * f + (f ^ 2 - 1)) 0)
    (hrun2 : LaysARun D f (p * f + (f ^ 2 - 1)) q)
    {jc : Fin N} {kc mc : Fin 3} (hkmc : kc ≠ mc)
    (hkc : (D.tile jc).pts kc = mkPt (p * f + (f ^ 2 - 1) + q * f) 0)
    (hmc : (D.tile jc).pts mc = mkPt (p * f + (f ^ 2 - 1) + q * f + f ^ 2) 0) : False := by
  have hf1 : 1 < f := by linarith
  have hL := baseLen_one f
  have hsum : (p:ℝ) + q = f := by rw [← hn]; exact_mod_cast hpq
  have hfit : p * f + (f ^ 2 - 1) + q * f + f ^ 2 = baseLen 1 f := by
    rw [hL]; linear_combination f * hsum
  have hM' := reflCD_modelData D hf1 htgt hM
  have hkc' : ((reflCD D hf1 htgt).tile jc).pts mc = mkPt 0 0 := by
    rw [reflCD_pts_base D hf1 htgt hmc]; exact mkPt_congr (by linarith) rfl
  have hmc' : ((reflCD D hf1 htgt).tile jc).pts kc = mkPt (f ^ 2) 0 := by
    rw [reflCD_pts_base D hf1 htgt hkc]; exact mkPt_congr (by linarith) rfl
  have hrun2' := laysARun_reflCD D hf1 htgt hrun2
  rw [show baseLen 1 f - (p * f + (f ^ 2 - 1)) - q * f = f ^ 2 by linarith] at hrun2'
  have hkb' : ((reflCD D hf1 htgt).tile jb).pts mb = mkPt (f ^ 2 + q * f) 0 := by
    rw [reflCD_pts_base D hf1 htgt hmb]; exact mkPt_congr (by linarith) rfl
  have hmb' : ((reflCD D hf1 htgt).tile jb).pts kb
      = mkPt (f ^ 2 + q * f + (f ^ 2 - 1)) 0 := by
    rw [reflCD_pts_base D hf1 htgt hkb]; exact mkPt_congr (by linarith) rfl
  have hrun1' := laysARun_reflCD D hf1 htgt hrun1
  rw [show baseLen 1 f - 0 - p * f = f ^ 2 + q * f + (f ^ 2 - 1) by linarith] at hrun1'
  exact word_c_p0_dies (reflCD D hf1 htgt) hf hn hn3 rfl hM' hA hp (by omega) hkmc.symm hkc'
    hmc' hrun2' hkmb.symm hkb' hmb' hrun1'

/-! ## F. From the chain to the word: the composite -/

/-- On a stretch of `a`-letters the junctions advance by `f`. -/
theorem X_run {X : ℕ → ℝ} {f : ℝ} {s t : ℕ}
    (h : ∀ m, s ≤ m → m < t → X (m + 1) - X m = f) :
    ∀ j, s + j ≤ t → X (s + j) = X s + j * f := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    have h2 := h (s + j) (by omega) (by omega)
    rw [← add_assoc]; push_cast; linear_combination h1 + h2

/-- A stretch of `a`-letters of the chain is a laid run. -/
theorem laysARun_of_chain {N : ℕ} (D : CongruentDissection N) {f : ℝ} {n : ℕ} {X : ℕ → ℝ}
    (hT : ∀ m, m < n → ∃ (i : Fin N) (k k' : Fin 3), k ≠ k' ∧
      (D.tile i).pts k = mkPt (X m) 0 ∧ (D.tile i).pts k' = mkPt (X (m + 1)) 0)
    {s t : ℕ} (ht : t ≤ n) (h : ∀ m, s ≤ m → m < t → X (m + 1) - X m = f) :
    LaysARun D f (X s) (t - s) := by
  intro j hj
  obtain ⟨i, k, k', hkk, hk, hk'⟩ := hT (s + j) (by omega)
  refine ⟨i, k, k', hkk, ?_, ?_⟩
  · rw [hk, X_run h j (by omega)]
  · have := X_run h (j + 1) (by omega)
    rw [← add_assoc] at this
    rw [hk', this]; exact mkPt_congr (by push_cast; ring) rfl

/-- **THE `e = 1` FAMILY, `f = n₀ ≥ 3`, in normal position.**  No `CongruentDissection` of
`baseBetaTarget 1 f` with `ModelData`/`AngleData` exists: the base chain (`base_chain`) has the
counts of `base_counts_of_chain`, its end letters are not `b` (`first_edge_not_b`,
`last_edge_not_b`), so its word is `a^p b a^q c a^r`/`a^p c a^q b a^r` with `p, r ≥ 1`
(`MarchCompose.base_word_dies`), or one of `c a^q b a^r`, `a^p b a^q c`, `c b c`, `a^p b a^q`
(§E). -/
theorem e1_family_f_ge_3 {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    {n₀ : ℕ} (hn : (n₀ : ℝ) = f) (hn3 : 3 ≤ n₀)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith)) (hM : ModelData D f α β γ)
    (hA : AngleData α β γ) : False := by
  have hf1 : 1 < f := by linarith
  have hb : (0:ℝ) < f ^ 2 - 1 := by nlinarith
  have hfb : f ≠ f ^ 2 - 1 := by nlinarith
  have hfc : f ≠ f ^ 2 := by nlinarith
  have hbc : f ^ 2 - 1 ≠ f ^ 2 := by linarith
  obtain ⟨n, X, hn0, hX0, hXn, hℓ, hT⟩ := base_chain D hf htgt hM
  obtain ⟨hb1, hcases⟩ := base_counts_of_chain hn hn3 hn0 X hX0 hXn hℓ
  set Sa := (Finset.range n).filter (fun m => X (m + 1) - X m = f) with hSa
  set Sb := (Finset.range n).filter (fun m => X (m + 1) - X m = f ^ 2 - 1) with hSb
  set Sc := (Finset.range n).filter (fun m => X (m + 1) - X m = f ^ 2) with hSc
  -- the three letter sets partition `range n`
  have hpart : n = Sa.card + Sb.card + Sc.card := by
    have h1 := Finset.card_filter_add_card_filter_not (s := Finset.range n)
      (fun m => X (m + 1) - X m = f)
    have h2 := Finset.card_filter_add_card_filter_not
      (s := (Finset.range n).filter (fun m => ¬ (X (m + 1) - X m = f)))
      (fun m => X (m + 1) - X m = f ^ 2 - 1)
    rw [Finset.filter_filter, Finset.filter_filter] at h2
    have e1 : (Finset.range n).filter
        (fun m => ¬ (X (m + 1) - X m = f) ∧ X (m + 1) - X m = f ^ 2 - 1) = Sb := by
      rw [hSb]; apply Finset.filter_congr; intro m _; constructor
      · exact fun h => h.2
      · intro h; exact ⟨by rw [h]; exact hfb.symm, h⟩
    have e2 : (Finset.range n).filter
        (fun m => ¬ (X (m + 1) - X m = f) ∧ ¬ (X (m + 1) - X m = f ^ 2 - 1)) = Sc := by
      rw [hSc]; apply Finset.filter_congr; intro m hm; constructor
      · rintro ⟨h1, h2⟩
        rcases hℓ m (Finset.mem_range.mp hm) with h | h | h
        · exact absurd h h1
        · exact absurd h h2
        · exact h
      · intro h; exact ⟨by rw [h]; exact hfc.symm, by rw [h]; exact hbc.symm⟩
    rw [e1, e2] at h2
    rw [Finset.card_range, ← hSa] at h1
    omega
  -- the unique `b`
  obtain ⟨ib, hib⟩ := Finset.card_eq_one.mp hb1
  have hstep_b : ∀ m, m < n → (X (m + 1) - X m = f ^ 2 - 1 ↔ m = ib) := by
    intro m hm; constructor
    · intro h
      have hm' : m ∈ Sb := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm, h⟩
      rw [hib, Finset.mem_singleton] at hm'; exact hm'
    · rintro rfl
      have : m ∈ Sb := by rw [hib]; exact Finset.mem_singleton_self _
      exact (Finset.mem_filter.mp this).2
  have hibn : ib < n := by
    have : ib ∈ Sb := by rw [hib]; exact Finset.mem_singleton_self _
    exact Finset.mem_range.mp (Finset.mem_filter.mp this).1
  have hstep_ib : X (ib + 1) - X ib = f ^ 2 - 1 := (hstep_b ib hibn).mpr rfl
  have hnotb : ∀ m, m < n → m ≠ ib → X (m + 1) - X m ≠ f ^ 2 - 1 :=
    fun m hm hne h => hne ((hstep_b m hm).mp h)
  -- neither end letter is `b`
  have hib0 : ib ≠ 0 := by
    intro h
    obtain ⟨i, k, k', hkk, hk, hk'⟩ := hT 0 hn0
    rw [hX0] at hk
    have h1 := first_edge_not_b D hf htgt hM hA hkk hk hk'
    have h2 : X (0 + 1) - X 0 = f ^ 2 - 1 := (hstep_b 0 hn0).mpr h.symm
    rw [hX0, sub_zero, zero_add] at h2
    rcases h1 with h1 | h1
    · exact hfb (by linarith)
    · exact hbc (by linarith)
  have hibl : ib ≠ n - 1 := by
    intro h
    obtain ⟨i, k, k', hkk, hk, hk'⟩ := hT (n - 1) (by omega)
    rw [Nat.sub_add_cancel hn0, hXn] at hk'
    have h1 := last_edge_not_b D hf htgt hM hA hkk hk hk'
    have h2 : X (n - 1 + 1) - X (n - 1) = f ^ 2 - 1 := (hstep_b (n - 1) (by omega)).mpr h.symm
    rw [Nat.sub_add_cancel hn0, hXn] at h2
    rcases h1 with h1 | h1
    · exact hfb (by linarith)
    · exact hbc (by linarith)
  rcases hcases with ⟨ha0, hc2⟩ | ⟨haf, hc1⟩ | ⟨ha2, hc0⟩
  · -- `(n_a, n_c) = (0, 2)`: the word is `c b c`
    have hn3' : n = 3 := by omega
    have hnota : ∀ m, m < n → X (m + 1) - X m ≠ f := by
      intro m hm h
      have : m ∈ Sa := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm, h⟩
      rw [Finset.card_eq_zero.mp ha0] at this
      exact Finset.notMem_empty m this
    have hib1 : ib = 1 := by omega
    subst hib1
    have e01 : (0:ℕ) + 1 = 1 := rfl
    have e12 : (1:ℕ) + 1 = 2 := rfl
    have e23 : (2:ℕ) + 1 = 3 := rfl
    have hs0 : X 1 - X 0 = f ^ 2 := by
      rcases hℓ 0 (by omega) with h | h | h
      · exact absurd h (hnota 0 (by omega))
      · exact absurd h (hnotb 0 (by omega) (by omega))
      · exact h
    have hs1 : X 2 - X 1 = f ^ 2 - 1 := hstep_ib
    have hs2 : X 3 - X 2 = f ^ 2 := by
      rcases hℓ 2 (by omega) with h | h | h
      · exact absurd h (hnota 2 (by omega))
      · exact absurd h (hnotb 2 (by omega) (by omega))
      · exact h
    have hX1 : X 1 = f ^ 2 := by linarith
    have hX2 : X 2 = f ^ 2 + (f ^ 2 - 1) := by linarith
    have hX3 : X 3 = f ^ 2 + (f ^ 2 - 1) + f ^ 2 := by linarith
    obtain ⟨i, ki, mi, hkmi, hki, hmi⟩ := hT 0 (by omega)
    obtain ⟨j, kj, mj, hkmj, hkj, hmj⟩ := hT 1 (by omega)
    obtain ⟨i', ki', mi', hkmi', hki', hmi'⟩ := hT 2 (by omega)
    rw [e01] at hmi; rw [e12] at hmj; rw [e23] at hmi'
    rw [hX0] at hki; rw [hX1] at hmi hkj; rw [hX2] at hmj hki'; rw [hX3] at hmi'
    exact word_cbc_dies D hf hn hn3 htgt hM hA hkmi hki hmi hkmj hkj hmj hkmi' hki' hmi'
  · -- `(n_a, n_c) = (f, 1)`: the word is a permutation of `(a^f, b, c)`
    obtain ⟨ic, hic⟩ := Finset.card_eq_one.mp hc1
    have hstep_c : ∀ m, m < n → (X (m + 1) - X m = f ^ 2 ↔ m = ic) := by
      intro m hm; constructor
      · intro h
        have hm' : m ∈ Sc := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm, h⟩
        rw [hic, Finset.mem_singleton] at hm'; exact hm'
      · rintro rfl
        have : m ∈ Sc := by rw [hic]; exact Finset.mem_singleton_self _
        exact (Finset.mem_filter.mp this).2
    have hicn : ic < n := by
      have : ic ∈ Sc := by rw [hic]; exact Finset.mem_singleton_self _
      exact Finset.mem_range.mp (Finset.mem_filter.mp this).1
    have hstep_ic : X (ic + 1) - X ic = f ^ 2 := (hstep_c ic hicn).mpr rfl
    have hne : ib ≠ ic := by
      intro h; rw [h] at hstep_ib; exact hbc (hstep_ib.symm.trans hstep_ic)
    have hna : ∀ m, m < n → m ≠ ib → m ≠ ic → X (m + 1) - X m = f := by
      intro m hm h1 h2
      rcases hℓ m hm with h | h | h
      · exact h
      · exact absurd h (hnotb m hm h1)
      · exact absurd ((hstep_c m hm).mp h) h2
    have hn' : n = n₀ + 2 := by omega
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · -- `ib < ic`: `a^p b a^q c a^r`, `p = ib`, `q = ic − ib − 1`, `r = n − 1 − ic`
      have hA1 : ∀ m, 0 ≤ m → m < ib → X (m + 1) - X m = f :=
        fun m _ hm => hna m (by omega) (by omega) (by omega)
      have hA2 : ∀ m, ib + 1 ≤ m → m < ic → X (m + 1) - X m = f :=
        fun m hm hm' => hna m (by omega) (by omega) (by omega)
      have hA3 : ∀ m, ic + 1 ≤ m → m < n → X (m + 1) - X m = f :=
        fun m hm hm' => hna m hm' (by omega) (by omega)
      have hrun1 : LaysARun D f 0 ib := by
        have := laysARun_of_chain D hT (s := 0) (t := ib) (by omega) hA1
        rwa [hX0, Nat.sub_zero] at this
      have hXib : X ib = ib * f := by
        have := X_run hA1 ib (by omega)
        rwa [zero_add, hX0, zero_add] at this
      have hXib1 : X (ib + 1) = ib * f + (f ^ 2 - 1) := by linarith
      obtain ⟨jb, kb, mb, hkmb, hkb, hmb⟩ := hT ib hibn
      rw [hXib] at hkb; rw [hXib1] at hmb
      have hrun2 : LaysARun D f (ib * f + (f ^ 2 - 1)) (ic - (ib + 1)) := by
        have := laysARun_of_chain D hT (s := ib + 1) (t := ic) hicn.le hA2
        rwa [hXib1] at this
      have hXic : X ic = ib * f + (f ^ 2 - 1) + ((ic - (ib + 1) : ℕ) : ℝ) * f := by
        have := X_run hA2 (ic - (ib + 1)) (by omega)
        rwa [show ib + 1 + (ic - (ib + 1)) = ic by omega, hXib1] at this
      have hXic1 : X (ic + 1)
          = ib * f + (f ^ 2 - 1) + ((ic - (ib + 1) : ℕ) : ℝ) * f + f ^ 2 := by linarith
      obtain ⟨jc, kc, mc, hkmc, hkc, hmc⟩ := hT ic hicn
      rw [hXic] at hkc; rw [hXic1] at hmc
      have hrun3 : LaysARun D f (ib * f + (f ^ 2 - 1) + ((ic - (ib + 1) : ℕ) : ℝ) * f + f ^ 2)
          (n - (ic + 1)) := by
        have := laysARun_of_chain D hT (s := ic + 1) (t := n) le_rfl hA3
        rwa [hXic1] at this
      rcases Nat.eq_zero_or_pos (n - (ic + 1)) with hr0 | hr1
      · exact word_bfirst_r0_dies D hf hn hn3 htgt hM hA (p := ib) (q := ic - (ib + 1))
          (by omega) (by omega) hrun1 hkmb hkb hmb hrun2 hkmc hkc hmc
      · exact base_word_dies D hf hn hn3 htgt hM hA (p := ib) (q := ic - (ib + 1))
          (r := n - (ic + 1)) (by omega) hr1 (by omega)
          (Or.inl ⟨hrun1, ⟨jb, kb, mb, hkmb, hkb, hmb⟩, hrun2, ⟨jc, kc, mc, hkmc, hkc, hmc⟩,
            hrun3⟩)
    · -- `ic < ib`: `a^p c a^q b a^r`, `p = ic`, `q = ib − ic − 1`, `r = n − 1 − ib ≥ 1`
      have hA1 : ∀ m, 0 ≤ m → m < ic → X (m + 1) - X m = f :=
        fun m _ hm => hna m (by omega) (by omega) (by omega)
      have hA2 : ∀ m, ic + 1 ≤ m → m < ib → X (m + 1) - X m = f :=
        fun m hm hm' => hna m (by omega) (by omega) (by omega)
      have hA3 : ∀ m, ib + 1 ≤ m → m < n → X (m + 1) - X m = f :=
        fun m hm hm' => hna m hm' (by omega) (by omega)
      have hrun1 : LaysARun D f 0 ic := by
        have := laysARun_of_chain D hT (s := 0) (t := ic) (by omega) hA1
        rwa [hX0, Nat.sub_zero] at this
      have hXic : X ic = ic * f := by
        have := X_run hA1 ic (by omega)
        rwa [zero_add, hX0, zero_add] at this
      have hXic1 : X (ic + 1) = ic * f + f ^ 2 := by linarith
      obtain ⟨jc, kc, mc, hkmc, hkc, hmc⟩ := hT ic hicn
      rw [hXic] at hkc; rw [hXic1] at hmc
      have hrun2 : LaysARun D f (ic * f + f ^ 2) (ib - (ic + 1)) := by
        have := laysARun_of_chain D hT (s := ic + 1) (t := ib) hibn.le hA2
        rwa [hXic1] at this
      have hXib : X ib = ic * f + f ^ 2 + ((ib - (ic + 1) : ℕ) : ℝ) * f := by
        have := X_run hA2 (ib - (ic + 1)) (by omega)
        rwa [show ic + 1 + (ib - (ic + 1)) = ib by omega, hXic1] at this
      have hXib1 : X (ib + 1)
          = ic * f + f ^ 2 + ((ib - (ic + 1) : ℕ) : ℝ) * f + (f ^ 2 - 1) := by linarith
      obtain ⟨jb, kb, mb, hkmb, hkb, hmb⟩ := hT ib hibn
      rw [hXib] at hkb; rw [hXib1] at hmb
      have hrun3 : LaysARun D f (ic * f + f ^ 2 + ((ib - (ic + 1) : ℕ) : ℝ) * f + (f ^ 2 - 1))
          (n - (ib + 1)) := by
        have := laysARun_of_chain D hT (s := ib + 1) (t := n) le_rfl hA3
        rwa [hXib1] at this
      have hr1 : 1 ≤ n - (ib + 1) := by omega
      rcases Nat.eq_zero_or_pos ic with hp0 | hp1
      · subst hp0
        simp only [Nat.cast_zero, zero_mul, zero_add] at hkc hmc hrun2 hkb hmb hrun3
        exact word_c_p0_dies D hf hn hn3 htgt hM hA hr1 (by omega) hkmc hkc hmc hrun2 hkmb hkb
          hmb hrun3
      · exact base_word_dies D hf hn hn3 htgt hM hA (p := ic) (q := ib - (ic + 1))
          (r := n - (ib + 1)) hp1 hr1 (by omega)
          (Or.inr ⟨hrun1, ⟨jc, kc, mc, hkmc, hkc, hmc⟩, hrun2, ⟨jb, kb, mb, hkmb, hkb, hmb⟩,
            hrun3⟩)
  · -- `(n_a, n_c) = (2f, 0)`: the word is `a^p b a^q`
    have hnotc : ∀ m, m < n → X (m + 1) - X m ≠ f ^ 2 := by
      intro m hm h
      have : m ∈ Sc := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm, h⟩
      rw [Finset.card_eq_zero.mp hc0] at this
      exact Finset.notMem_empty m this
    have hna : ∀ m, m < n → m ≠ ib → X (m + 1) - X m = f := by
      intro m hm hne
      rcases hℓ m hm with h | h | h
      · exact h
      · exact absurd h (hnotb m hm hne)
      · exact absurd h (hnotc m hm)
    have hn' : n = 2 * n₀ + 1 := by omega
    have hA1 : ∀ m, 0 ≤ m → m < ib → X (m + 1) - X m = f :=
      fun m _ hm => hna m (by omega) (by omega)
    have hA3 : ∀ m, ib + 1 ≤ m → m < n → X (m + 1) - X m = f :=
      fun m hm hm' => hna m hm' (by omega)
    have hrun1 : LaysARun D f 0 ib := by
      have := laysARun_of_chain D hT (s := 0) (t := ib) (by omega) hA1
      rwa [hX0, Nat.sub_zero] at this
    have hXib : X ib = ib * f := by
      have := X_run hA1 ib (by omega)
      rwa [zero_add, hX0, zero_add] at this
    have hXib1 : X (ib + 1) = ib * f + (f ^ 2 - 1) := by linarith
    obtain ⟨jb, kb, mb, hkmb, hkb, hmb⟩ := hT ib hibn
    rw [hXib] at hkb; rw [hXib1] at hmb
    have hrun2 : LaysARun D f (ib * f + (f ^ 2 - 1)) (n - (ib + 1)) := by
      have := laysARun_of_chain D hT (s := ib + 1) (t := n) le_rfl hA3
      rwa [hXib1] at this
    exact word_aba_dies D hf hn hn3 htgt hM hA (p := ib) (q := n - (ib + 1)) (by omega)
      (by omega) (by omega) hrun1 hkmb hkb hmb hrun2

/-! ## G. The family for an arbitrary congruent dissection, and non-vacuity -/

/-- **THE `e = 1` FAMILY, `f = n ≥ 3`: no congruent dissection whose target is congruent to
`baseBetaTarget 1 n` and whose model is congruent to the tile `(n, n²−1, n²)` exists.**
Normal position, `ModelData` and `AngleData` are derived by `E1NormalForm.normal_form`. -/
theorem e1_family_f_ge_3_congruent {N : ℕ} (D₀ : CongruentDissection N) {n : ℕ} (hn3 : 3 ≤ n)
    (htgt : D₀.target.Congruent
      (baseBetaTarget 1 n one_pos (by exact_mod_cast (show 1 < n by omega))))
    (hmod : D₀.model.Congruent (modelTri n (by exact_mod_cast (show 1 < n by omega)))) :
    False := by
  obtain ⟨g, D, hD, -, hM, hA, -⟩ := Erdos634.E1NormalForm.normal_form D₀ n (by omega) htgt hmod
  exact e1_family_f_ge_3 D (f := (n : ℝ)) (by exact_mod_cast (show 2 ≤ n by omega)) rfl hn3 hD
    hM hA

/-- The same from side lengths alone: a model with sides `n, n²−1, n²` in `ModelData`'s
labelling (SSS, `E1NormalForm.congruent_modelTri_of_sides`). -/
theorem e1_family_f_ge_3_of_sides {N : ℕ} (D₀ : CongruentDissection N) {n : ℕ} (hn3 : 3 ≤ n)
    (htgt : D₀.target.Congruent
      (baseBetaTarget 1 n one_pos (by exact_mod_cast (show 1 < n by omega))))
    (h0 : sideOpp D₀.model 0 = n) (h1 : sideOpp D₀.model 1 = (n : ℝ) ^ 2 - 1)
    (h2 : sideOpp D₀.model 2 = (n : ℝ) ^ 2) : False :=
  e1_family_f_ge_3_congruent D₀ hn3 htgt
    (Erdos634.E1NormalForm.congruent_modelTri_of_sides n (by omega) _ h0 h1 h2)

/-! ### Non-vacuity

The conclusion is `False`, so "non-vacuity" here means: every hypothesis is *individually*
satisfiable — jointly they are not, which is the theorem.  `hf`, `hn`, `hn3`: `f = 4`.
`hM`/`hA`: `MarchCompose.bundle_witness` (the tile `modelTri n` has `ModelData`'s side lengths
and corner angles, and those angles satisfy `AngleData`, every natural `n ≥ 2`),
`E1NormalForm.bundle_f4`.  The congruence hypotheses of `e1_family_f_ge_3_congruent`:
`E1NormalForm.target_self_congruent`, `.model_self_congruent`.  `htgt`: any
`Dissection` of `baseBetaTarget 1 f` has it (e.g. `SubDissection`'s one-tile dissections of a
triangle by itself, with a different model).  No `CongruentDissection` satisfying all of them
is exhibited — none exists, and that is the statement. -/

theorem hyps_f4 : (2:ℝ) ≤ ((4:ℕ):ℝ) ∧ ((4:ℕ):ℝ) = (4:ℝ) ∧ 3 ≤ (4:ℕ) ∧
    ∃ α β γ : ℝ, AngleData α β γ := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  obtain ⟨T, α, β, γ, -, -, -, -, -, -, hA, -⟩ := bundle_witness 4 (by norm_num)
  exact ⟨α, β, γ, hA⟩

end Erdos634.E1BaseWord

#print axioms Erdos634.E1BaseWord.base_chain
#print axioms Erdos634.E1BaseWord.base_counts_of_chain
#print axioms Erdos634.E1BaseWord.first_edge_not_b
#print axioms Erdos634.E1BaseWord.last_edge_not_b
#print axioms Erdos634.E1BaseWord.corner_bCapM_dies
#print axioms Erdos634.E1BaseWord.corner_bOverM_dies
#print axioms Erdos634.E1BaseWord.word_aba_dies
#print axioms Erdos634.E1BaseWord.word_c_p0_dies
#print axioms Erdos634.E1BaseWord.word_cbc_dies
#print axioms Erdos634.E1BaseWord.word_bfirst_r0_dies
#print axioms Erdos634.E1BaseWord.e1_family_f_ge_3
#print axioms Erdos634.E1BaseWord.e1_family_f_ge_3_congruent
#print axioms Erdos634.E1BaseWord.e1_family_f_ge_3_of_sides
#print axioms Erdos634.E1BaseWord.hyps_f4

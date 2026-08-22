/-
BAdjacency.lean — the combinatorial core of Theorem A1 (the b-adjacency kill) and the two
room-kill inequalities of Program A (Erdős #634, base-β, e = 1).
No imports, no axioms: kernel-checked with the core toolchain only.

THEOREM A1 (research notes 2026-07-26). At m = 1, e = 1, the starved base walk (f,1,1) writes as
`a^kL ++ M ++ a^kR` with `kL, kR ≥ 1` maximal, so `M` is nonempty and its first and last letters
are not `a`. If both corner blocks' first break is a base-break, the forced β-tile at the end of
each corner run owns the adjacent base edge with flank in {a, c} — never `b`. Hence both ends of
`M` would have to be `c`; but the walk contains exactly ONE `c`. Formalized as `b_adjacency`:
a nonempty letter list with non-`a` ends, at most one `c`, and at least one `b`, has `b` at an
end. (The geometric forcing lives in the research notes; this file pins the combinatorial step,
with a self-contained count function to avoid any library dependence.)

ROOM KILLS (subtraction-free forms). `ladder_room_kill`: `3f² + f < f³ + f² + 1` for `f ≥ 3`,
i.e. c + f·b > Y: horizontal b-ladders exceed every chord. `no_full_phantom`: `3f² < f³ + 1`
for `f ≥ 3`: a phantom block's side never fits along the base. Nonlinear seeds proved by hand
(`cube_ge`, `sq_ge`), the rest by `omega` over the products as atoms.
-/

namespace Erdos634.BAdjacency

inductive Letter | a | b | c
deriving DecidableEq, Repr

open Letter

/-- self-contained occurrence count (no library dependence) -/
def cnt (x : Letter) : List Letter → Nat
  | []      => 0
  | y :: l  => (if y = x then 1 else 0) + cnt x l

theorem cnt_append (x : Letter) (l₁ l₂ : List Letter) :
    cnt x (l₁ ++ l₂) = cnt x l₁ + cnt x l₂ := by
  induction l₁ with
  | nil => simp [cnt]
  | cons y l ih => simp [cnt, ih]; omega

/-- first element of a nonempty list (default irrelevant) -/
def hd : List Letter → Letter
  | []     => Letter.a
  | x :: _ => x

/-- last element of a nonempty list -/
def lst : List Letter → Letter
  | []          => Letter.a
  | [x]         => x
  | _ :: y :: l => lst (y :: l)

theorem lst_cons_cons (x y : Letter) (l : List Letter) :
    lst (x :: y :: l) = lst (y :: l) := rfl

/-- a list with ≥ 2 elements decomposes as head :: (mid ++ [last]) -/
theorem two_ends : ∀ (y : Letter) (l : List Letter) (x : Letter),
    ∃ mid, x :: y :: l = x :: (mid ++ [lst (y :: l)])
  | y, [], x => ⟨[], rfl⟩
  | y, z :: l, x => by
    obtain ⟨mid, hm⟩ := two_ends z l y
    refine ⟨y :: mid, ?_⟩
    have h2 : lst (y :: z :: l) = lst (z :: l) := rfl
    rw [h2]
    have : y :: z :: l = y :: (mid ++ [lst (z :: l)]) := hm
    rw [List.cons_append]
    exact congrArg (x :: ·) this

/-- **Theorem A1, combinatorial core.** A nonempty word whose ends are not `a`, containing at
most one `c` and at least one `b`, has `b` as its first or last letter. (Applied to the middle
block `M` of the starved walk (f,1,1): the forced β-tiles forbid `b` at both slots, which would
force two `c`s — absurd.) -/
theorem b_adjacency (M : List Letter) (hne : M ≠ [])
    (hhd : hd M ≠ Letter.a) (hlst : lst M ≠ Letter.a)
    (hc : cnt Letter.c M ≤ 1) (hb : 1 ≤ cnt Letter.b M) :
    hd M = Letter.b ∨ lst M = Letter.b := by
  match M, hne with
  | [x], _ =>
    cases x with
    | a => exact absurd rfl hhd
    | b => exact Or.inl rfl
    | c => simp [cnt] at hb
  | x :: y :: l, _ =>
    -- head is b: done; head is a: absurd; head is c: examine the last letter
    cases x with
    | a => exact absurd rfl hhd
    | b => exact Or.inl rfl
    | c =>
      cases hx2 : lst (y :: l) with
      | a => exact absurd ((lst_cons_cons Letter.c y l).trans hx2) hlst
      | b => exact Or.inr ((lst_cons_cons Letter.c y l).trans hx2)
      | c =>
        -- both ends are c: the word contains two c's, contradicting hc ≤ 1
        exact absurd hc (by
          obtain ⟨mid, hm⟩ := two_ends y l Letter.c
          rw [hx2] at hm
          rw [hm]
          have hcount : cnt Letter.c (Letter.c :: (mid ++ [Letter.c]))
              = 1 + (cnt Letter.c mid + 1) := by
            simp [cnt, cnt_append]
          omega)

/-- nonlinear seeds for the room kills -/
theorem cube_ge (f : Nat) (h : 3 ≤ f) : 3 * (f * f) ≤ f * (f * f) :=
  Nat.mul_le_mul_right (f * f) h

theorem sq_ge (f : Nat) (h : 1 ≤ f) : f ≤ f * f := by
  calc f = f * 1 := by omega
  _ ≤ f * f := Nat.mul_le_mul_left f h

/-- **Horizontal ladder kill** (subtraction-free): `3f² + f < f³ + f² + 1` for `f ≥ 3`,
i.e. c + f·b = f³ + f² − f exceeds Y = 3f² − 1: no chord carries a b-ladder. -/
theorem ladder_room_kill (f : Nat) (h : 3 ≤ f) :
    3 * (f * f) + f < f * (f * f) + f * f + 1 := by
  have h1 := cube_ge f h
  have h2 := sq_ge f (by omega)
  omega

/-- **No full phantom**: `3f² < f³ + 1` for `f ≥ 3`: the phantom's side (length `f³`) never
fits along the base (length `3f² − 1`). -/
theorem no_full_phantom (f : Nat) (h : 3 ≤ f) :
    3 * (f * f) < f * (f * f) + 1 := by
  have h1 := cube_ge f h
  omega

end Erdos634.BAdjacency

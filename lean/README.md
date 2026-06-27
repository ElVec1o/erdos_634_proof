# Lean formalization — arithmetic core of the Erdős #634 proof

`Erdos634.lean` machine-checks the novel number-theoretic heart of the proof:
for a primitive 120°-triple with squared leg `b = k²`, `k ∤ (a+b−c)`; equivalently the
Φ-invariant tile count `M = (c−a−b)/k` is never an integer. Axiom-clean (`propext`,
`Classical.choice`, `Quot.sound`); no `sorry`.

The geometric ingredients (the Φ-invariant, the shape classification, Laczkovich's case analysis,
Beeson's equilateral input) are **not** formalized — there is no theory of triangle dissections in
Mathlib — and remain in the human-checked paper.

## Build
```
lake exe cache get      # download precompiled Mathlib (v4.30.0)
lake build              # checks Erdos634.lean
```
Toolchain: Lean 4.30.0, Mathlib rev v4.30.0.

# Euler's polyhedron formula in Lean

This project proves **V − E + F = 2** for every convex polytope in
`EuclideanSpace ℝ (Fin 3)` with affine dimension 3. The theorem
[`EulerPolyhedron.euler_polyhedron`](EulerPolyhedron.lean) has exactly two
geometric hypotheses:

```lean
(hp : EulersGem.IsPolytope p)
(hdim : EulersGem.affDim p = 3)
```

Here `IsPolytope p` means that `p` is the convex hull of a finite set.
V, E, and F are the cardinalities of the actual sets of geometric faces
satisfying `EulersGem.IsFaceOf p f` and `EulersGem.affDim f = 0`, `1`, or `2`.
The original upstream proof that these sets are finite is preserved and
exposed as `EulerPolyhedron.faces_finite`.

The new representation theorem
[`EulersGem.IsPolytope.isPolyhedron`](EulerPolyhedron/Halfspaces.lean)
proves that **every finite convex hull in any finite-dimensional real inner
product space** is an intersection of finitely many closed halfspaces. It
also covers empty and lower-dimensional polytopes. Its halfspaces are
exactly `EulersGem.closedHalfspace a b = {x | ⟪a, x⟫ ≤ b}`.

## Build and verify

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
./scripts/verify.sh
```

The verification script builds the complete proof chain and checks Lean's
axiom reports for the representation theorem, face finiteness, and Euler's
formula. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
It also rejects proof placeholders and additional axiom declarations in
all project and vendored Lean sources.

Dependencies are locked in `lean-toolchain` and `lake-manifest.json`:

- Lean: `leanprover/lean4:v4.35.0-rc1`
- Mathlib: `09a9e06e4e5ccd5b783f25e52ad3ebecfb1e2d68`
- Vendored Euler proof: `tangentproofs/eulers-gem` at
  `02c67906ae6b427f7c5c73fab0c89e7956a8a3c1`

## Proof

1. [`Elimination.lean`](EulerPolyhedron/Elimination.lean) proves a real
   Fourier–Motzkin elimination step. Zero coefficients retain their
   inequalities; every negative/positive coefficient pair contributes a
   new inequality. Finite lower and upper bounds prove the converse.
   Iterating this step eliminates any finite number of auxiliary variables.
2. [`Representation.lean`](EulerPolyhedron/Representation.lean) represents a
   finite convex hull as the linear image of the simplex of nonnegative
   barycentric weights summing to one. Its graph is a finite inequality
   system; eliminating the weights gives a finite halfspace presentation.
3. [`Halfspaces.lean`](EulerPolyhedron/Halfspaces.lean) uses finite-dimensional
   Riesz representation to turn the linear functionals into the geometric
   inner-product halfspaces expected by the upstream proof.
4. [`EulerPolyhedron.lean`](EulerPolyhedron.lean) applies the original
   `EulersGem.euler_relation_convex_3polytope` to this proved presentation.

The final theorem takes no supplied halfspace presentation, triangulation,
combinatorial realization, or Euler-characteristic assumption.

## Upstream and attribution

The Euler argument and face-finiteness proof are reused from Michal Wallace's
[`tangentproofs/eulers-gem`](https://github.com/tangentproofs/eulers-gem/tree/02c67906ae6b427f7c5c73fab0c89e7956a8a3c1).
The 14 necessary modules are vendored without modification, with their
original attribution and licences; see [`vendor/README.md`](vendor/README.md).
The Euler argument follows Lawrence C. Paulson's
[AFP formalization](https://isa-afp.org/entries/Euler_Polyhedron_Formula.html)
(2023), ported from HOL Light and crediting Jim Lawrence.
The new representation proof was developed with Codex and checked by Lean.

On 2026-10-13, upstream's default branch still pointed to the audited commit.
Mathlib's current default branch was also inspected at
`54c01c3314d33d15d77893cbe4e0472ff26bb34d`. Its
[`DualFinite.lean`](https://github.com/leanprover-community/mathlib4/blob/54c01c3314d33d15d77893cbe4e0472ff26bb34d/Mathlib/Geometry/Convex/Cone/DualFinite.lean)
still defines dually finitely generated cones without proving the
Minkowski–Weyl equivalence. The new proof uses elementary elimination and
the audited dependency versions.

New code is under Apache 2.0; upstream licensing notices are preserved.

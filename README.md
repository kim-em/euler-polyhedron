# Euler's polyhedron formula: final layers for eulers-gem

**The main formalization is Michal Wallace's
[`eulers-gem`](https://github.com/tangentproofs/eulers-gem) development.**
Upstream supplies the geometric definitions, hyperplane arrangements,
Euler–Poincaré argument, Euler's formula for a polytope with a finite
halfspace presentation, and the proof that its geometric face sets are finite.
The substantial Euler proof lives there and is imported directly as a pinned
Lake dependency.

This small companion repository adds the final layers needed to apply that
existing proof to every finite convex hull: a finite-vertex-to-finite-halfspace
representation theorem and a short corollary that discharges upstream's extra
halfspace hypotheses. The resulting **V − E + F = 2** theorem applies to every
convex polytope in `EuclideanSpace ℝ (Fin 3)` with affine dimension 3.
The theorem
[`EulerPolyhedron.euler_polyhedron`](EulerPolyhedron.lean) has exactly two
geometric hypotheses:

```lean
(hp : EulersGem.IsPolytope p)
(hdim : EulersGem.affDim p = 3)
```

Here `IsPolytope p` means that `p` is the convex hull of a finite set.
V, E, and F are the cardinalities of the actual sets of geometric faces
satisfying `EulersGem.IsFaceOf p f` and `EulersGem.affDim f = 0`, `1`, or `2`.
`EulerPolyhedron.faces_finite` directly reuses upstream's original proof
that these sets are finite.

The new representation theorem
[`EulersGem.IsPolytope.isPolyhedron`](EulerPolyhedron/Halfspaces.lean)
proves that **every finite convex hull in any finite-dimensional real inner
product space** is an intersection of finitely many closed halfspaces. It
also covers empty and lower-dimensional polytopes. Its halfspaces are
exactly `EulersGem.closedHalfspace a b = {x | ⟪a, x⟫ ≤ b}`. The algebraic
elimination and representation layers work over any linearly ordered field;
only the geometric bridge uses real inner products.

All of these mathematical additions are proposed upstream in
[`eulers-gem` PR #2](https://github.com/tangentproofs/eulers-gem/pull/2).
The PR also removes the supplied halfspace presentation from upstream's public
Euler and Platonic-solid results. Once merged, upstream will contain all the
mathematical results added here, making this companion repository redundant
as a formalization. The dependency below remains pinned to the original
audited upstream commit until that integration is merged.

## Build and verify

Install [elan](https://github.com/leanprover/elan) and Python 3.11 or newer, then run:

```sh
lake exe cache get
./scripts/verify.sh
```

The verification script checks that dependency checkouts are clean and match
the committed pins, builds the proof chain, and elaborates the exact promised
Euler, representation, and face-finiteness statements. It audits axiom
dependencies directly in Lean, allowing only `propext`, `Classical.choice`,
and `Quot.sound`, then replays the project and imported upstream declarations
through Lean's kernel with `leanchecker`. CI runs the same checks.

Dependencies are locked in `lean-toolchain` and `lake-manifest.json`:

- Lean: `leanprover/lean4:v4.35.0-rc1`
- Mathlib: `09a9e06e4e5ccd5b783f25e52ad3ebecfb1e2d68`
- Euler proof dependency: `tangentproofs/eulers-gem` at
  `02c67906ae6b427f7c5c73fab0c89e7956a8a3c1`

## Upstream proof and the added layers

The Euler argument is upstream's
[`EulersGem.euler_relation_convex_3polytope`](https://github.com/tangentproofs/eulers-gem/blob/02c67906ae6b427f7c5c73fab0c89e7956a8a3c1/lean/EulersGem/Embed.lean),
built on its Euler–Poincaré development. Geometric face finiteness is upstream's
[`facesOfDim_finite_of_isPolytope`](https://github.com/tangentproofs/eulers-gem/blob/02c67906ae6b427f7c5c73fab0c89e7956a8a3c1/lean/EulersGem/PolytopeFaces.lean).
This repository's additions supply the missing representation theorem and
then invoke those results:

1. [`Elimination.lean`](EulerPolyhedron/Elimination.lean) proves a
   Fourier–Motzkin elimination step. Zero coefficients retain their
   inequalities; every negative/positive coefficient pair contributes a
   new inequality. Finite lower and upper bounds prove the converse.
   Iterating this step eliminates any finite number of auxiliary variables.
2. [`Representation.lean`](EulerPolyhedron/Representation.lean) represents a
   finite convex hull as the linear image of the simplex of nonnegative
   barycentric weights summing to one. Its graph is a finite inequality
   system; eliminating the weights gives a finite halfspace presentation.
   The public API uses Mathlib's `Fintype.linearCombination`.
3. [`Halfspaces.lean`](EulerPolyhedron/Halfspaces.lean) uses finite-dimensional
   Riesz representation to turn the linear functionals into the geometric
   inner-product halfspaces expected by the upstream proof.
4. [`EulerPolyhedron.lean`](EulerPolyhedron.lean) applies the original
   `EulersGem.euler_relation_convex_3polytope` to this proved presentation.

The final theorem takes no supplied halfspace presentation, triangulation,
combinatorial realization, or Euler-characteristic assumption.

## Upstream and attribution

The main Lean formalization, including the Euler argument and face-finiteness
proof, is Michal Wallace's
[`tangentproofs/eulers-gem`](https://github.com/tangentproofs/eulers-gem/tree/02c67906ae6b427f7c5c73fab0c89e7956a8a3c1).
Lake depends directly on upstream's `lean/` package at the audited commit,
using `subDir = "lean"`. Only the modules needed by the theorem are imported;
upstream's source, attribution, and licences stay in that dependency.
The Euler argument follows Lawrence C. Paulson's
[AFP formalization](https://isa-afp.org/entries/Euler_Polyhedron_Formula.html)
(2023), ported from HOL Light and crediting Jim Lawrence.
The new representation proof was developed with Codex and checked by Lean.

New code is under Apache 2.0; the upstream dependency retains its own licensing notices.

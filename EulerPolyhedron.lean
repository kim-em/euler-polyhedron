/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import EulerPolyhedron.Halfspaces
import EulersGem.Embed
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Euler's polyhedron formula without a halfspace hypothesis

The counts below are the actual geometric faces of `p`, using the original
`IsFaceOf` and `affDim` definitions. Finiteness is the original upstream
face-finiteness proof. The only geometric hypotheses are `IsPolytope p` and
`affDim p = 3`.
-/

open Set

namespace EulerPolyhedron

/-- Euler's formula for every full-dimensional convex polytope in real
three-space, with no supplied halfspace presentation. -/
theorem euler_polyhedron {p : Set (EuclideanSpace ℝ (Fin 3))}
    (hp : EulersGem.IsPolytope p) (hdim : EulersGem.affDim p = 3) :
    ({f : Set (EuclideanSpace ℝ (Fin 3)) |
      EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 0}.ncard : ℤ) -
    ({f : Set (EuclideanSpace ℝ (Fin 3)) |
      EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 1}.ncard : ℤ) +
    ({f : Set (EuclideanSpace ℝ (Fin 3)) |
      EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 2}.ncard : ℤ) = 2 := by
  obtain ⟨H, hH, hrep⟩ := hp.isPolyhedron
  exact EulersGem.euler_relation_convex_3polytope hH hrep hp hdim (by simp)

/-- The geometric face sets being counted really are finite. This retains the
original upstream proof, which follows directly from the finite vertex set. -/
theorem faces_finite {p : Set (EuclideanSpace ℝ (Fin 3))}
    (hp : EulersGem.IsPolytope p) (d : ℤ) :
    {f : Set (EuclideanSpace ℝ (Fin 3)) |
      EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = d}.Finite :=
  EulersGem.facesOfDim_finite_of_isPolytope hp d

end EulerPolyhedron

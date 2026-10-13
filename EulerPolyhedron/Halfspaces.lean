/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Codex
-/
import EulerPolyhedron.Representation
import EulersGem.Polytope

import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The geometric V-to-H representation theorem

We turn linear functionals into inner products by finite-dimensional Riesz
representation, obtaining exactly `EulersGem.closedHalfspace`.
-/

open Set
open scoped RealInnerProductSpace

namespace EulersGem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A geometric halfspace presentation is a linear-inequality presentation. -/
theorem IsPolyhedron.isPolyhedral {p : Set E} (hp : IsPolyhedron p) :
    EulerPolyhedron.IsPolyhedral ℝ p := by
  obtain ⟨H, hH, rfl⟩ := hp
  let := hH.fintype
  have h : EulerPolyhedron.IsPolyhedral ℝ
      (⋂ h : H, closedHalfspace h.1.1 h.1.2) := by
    apply EulerPolyhedron.IsPolyhedral.iInter
    intro h
    exact EulerPolyhedron.IsPolyhedral.halfspace
      (innerSL ℝ h.1.1).toLinearMap h.1.2
  simpa only [iInter_subtype] using h

end EulersGem

namespace EulerPolyhedron

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private noncomputable def normal (f : E →ₗ[ℝ] ℝ) : E :=
  (InnerProductSpace.toDual ℝ E).symm f.toContinuousLinearMap

private theorem normal_inner (f : E →ₗ[ℝ] ℝ) (x : E) :
    ⟪normal f, x⟫ = f x :=
  InnerProductSpace.toDual_symm_apply

/-- A finite linear-inequality presentation gives precisely the geometric
halfspaces used in the original Euler proof. -/
theorem IsPolyhedral.isPolyhedron {s : Set E} (hs : IsPolyhedral ℝ s) :
    EulersGem.IsPolyhedron s := by
  classical
  obtain ⟨S, rfl⟩ := hs
  let h : ((E →ₗ[ℝ] ℝ) × ℝ) → EulersGem.Hyperplane E :=
    fun q => (normal q.1, q.2)
  refine ⟨h '' (S : Set ((E →ₗ[ℝ] ℝ) × ℝ)), S.finite_toSet.image h, ?_⟩
  ext x
  constructor
  · intro hx
    simp only [mem_iInter]
    intro k hk
    obtain ⟨q, hq, rfl⟩ := hk
    change ⟪normal q.1, x⟫ ≤ q.2
    rw [normal_inner]
    exact hx q hq
  · intro hx q hq
    have hmem := mem_iInter₂.mp hx (h q) (mem_image_of_mem h hq)
    change ⟪normal q.1, x⟫ ≤ q.2 at hmem
    simpa only [normal_inner] using hmem

end EulerPolyhedron

namespace EulersGem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- In finite-dimensional real inner product spaces, the two halfspace
presentation predicates coincide. -/
theorem isPolyhedron_iff_isPolyhedral {p : Set E} :
    IsPolyhedron p ↔ EulerPolyhedron.IsPolyhedral ℝ p :=
  ⟨IsPolyhedron.isPolyhedral, EulerPolyhedron.IsPolyhedral.isPolyhedron⟩

/-- **Finite-vertex-to-finite-halfspace representation.** Every convex hull of
finitely many points is an intersection of finitely many closed halfspaces.
This includes empty and lower-dimensional polytopes. -/
theorem IsPolytope.isPolyhedron {p : Set E} (hp : IsPolytope p) : IsPolyhedron p := by
  obtain ⟨V, hV, rfl⟩ := hp
  exact (EulerPolyhedron.isPolyhedral_convexHull_of_finite hV).isPolyhedron

end EulersGem

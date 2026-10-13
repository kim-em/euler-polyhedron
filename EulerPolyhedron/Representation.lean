/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Codex
-/
module

public import EulerPolyhedron.Elimination
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Finite convex hulls have finite halfspace presentations

A finite convex hull is the linear image of the simplex of barycentric weights.
Its graph is a finite inequality system; eliminating the weights gives a
finite halfspace presentation over any linearly ordered field.

## Main declarations

* `IsPolyhedral.linear_image`: finite-dimensional linear images are polyhedral.
* `convexHull_range_eq_image_linearCombination`: finite hulls as barycentric images.
* `isPolyhedral_convexHull_of_finite`: finite convex hulls are polyhedral.
-/

@[expose] public section

open Set

namespace EulerPolyhedron

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

/-- Every finite intersection of affine halfspaces is convex. -/
theorem IsPolyhedral.convex {s : Set E} (hs : IsPolyhedral 𝕜 s) : Convex 𝕜 s := by
  obtain ⟨S, rfl⟩ := hs
  have h : {x | ∀ q ∈ S, q.1 x ≤ q.2} = ⋂ q ∈ S, {x | q.1 x ≤ q.2} := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter]
  rw [h]
  exact convex_iInter fun q ↦ convex_iInter fun _ ↦ convex_halfSpace_le q.1.isLinear q.2

/-- The simplex of all nonnegative weights with sum one is polyhedral. -/
theorem IsPolyhedral.weights (ι : Type*) [Fintype ι] :
    IsPolyhedral 𝕜 {w : ι → 𝕜 | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} := by
  have hnonneg := IsPolyhedral.of_finite
    (fun i : ι ↦ -(LinearMap.proj i : (ι → 𝕜) →ₗ[𝕜] 𝕜)) (fun _ ↦ (0 : 𝕜))
  have hsum := IsPolyhedral.hyperplane (∑ i : ι, LinearMap.proj i) (1 : 𝕜)
  convert hnonneg.inter hsum using 1
  ext w
  simp only [mem_ofPred_eq, mem_inter_iff, LinearMap.neg_apply, neg_nonpos,
    LinearMap.sum_apply, LinearMap.proj_apply]

/-- The finite convex hull is precisely the set of barycentric combinations. -/
theorem convexHull_range_eq_image_linearCombination {ι : Type*} [Fintype ι] (v : ι → E) :
    convexHull 𝕜 (range v) =
      Fintype.linearCombination 𝕜 v '' {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} := by
  classical
  refine subset_antisymm (convexHull_min ?_
    ((IsPolyhedral.weights ι).convex.linear_image (Fintype.linearCombination 𝕜 v))) ?_
  · rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ⟨?_, ?_⟩, by simp⟩
    · intro j
      by_cases h : j = i <;> simp [h]
    · simp [Pi.single_apply, Finset.sum_ite_eq']
  · rintro x ⟨w, hw, rfl⟩
    exact (convex_convexHull 𝕜 (range v)).sum_mem (fun i _ => hw.1 i) hw.2
      (fun i _ => subset_convexHull 𝕜 _ (mem_range_self i))

section FiniteDimensional

variable [FiniteDimensional 𝕜 E]

/-- A point is cut out by finitely many coordinate equalities, each expressed
as two closed halfspaces. -/
theorem IsPolyhedral.singleton_zero : IsPolyhedral 𝕜 {(0 : E)} := by
  classical
  let b := Module.finBasis 𝕜 E
  have hp := IsPolyhedral.of_finite (fun i => b.coord i) (fun _ => (0 : 𝕜))
  have hn := IsPolyhedral.of_finite (fun i => -b.coord i) (fun _ => (0 : 𝕜))
  convert hp.inter hn using 1
  ext x
  constructor
  · rintro rfl
    simp
  · intro hx
    apply mem_singleton_iff.mpr
    apply b.ext_elem
    intro i
    have h₁ := hx.1 i
    have h₂ := hx.2 i
    simpa using le_antisymm h₁ (by simpa using h₂)

/-- A linear equality in a finite-dimensional codomain is polyhedral. -/
theorem IsPolyhedral.linear_eq_zero {F : Type*} [AddCommGroup F] [Module 𝕜 F]
    (f : F →ₗ[𝕜] E) : IsPolyhedral 𝕜 {x | f x = 0} := by
  convert (IsPolyhedral.singleton_zero (E := E)).preimage f using 1
  ext x
  simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]

/-- Linear images from a finite real coordinate space preserve polyhedrality. -/
theorem IsPolyhedral.image_fin {n : ℕ} {s : Set (Fin n → 𝕜)}
    (hs : IsPolyhedral 𝕜 s) (f : (Fin n → 𝕜) →ₗ[𝕜] E) :
    IsPolyhedral 𝕜 (f '' s) := by
  let g : ((Fin n → 𝕜) × E) →ₗ[𝕜] E :=
    LinearMap.snd 𝕜 (Fin n → 𝕜) E - f.comp (LinearMap.fst 𝕜 (Fin n → 𝕜) E)
  have h := (hs.preimage (LinearMap.fst 𝕜 (Fin n → 𝕜) E)).inter
    (IsPolyhedral.linear_eq_zero g)
  convert h.project_fin n using 1
  ext x
  simp only [mem_image, mem_ofPred_eq, mem_inter_iff, mem_preimage, LinearMap.fst_apply,
    g, LinearMap.sub_apply, LinearMap.snd_apply, LinearMap.comp_apply, sub_eq_zero]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, hx⟩
    exact ⟨w, hw, hx.symm⟩

/-- Finite-dimensional linear images preserve polyhedrality. -/
theorem IsPolyhedral.linear_image {F : Type*} [AddCommGroup F] [Module 𝕜 F]
    [FiniteDimensional 𝕜 F] {s : Set F} (hs : IsPolyhedral 𝕜 s) (f : F →ₗ[𝕜] E) :
    IsPolyhedral 𝕜 (f '' s) := by
  let e := (Module.finBasis 𝕜 F).equivFun
  have h := (hs.preimage e.symm.toLinearMap).image_fin (f.comp e.symm.toLinearMap)
  convert h using 1
  ext x
  change (∃ y, y ∈ s ∧ f y = x) ↔ ∃ w, e.symm w ∈ s ∧ f (e.symm w) = x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨e y, by simpa, by simp⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨e.symm w, hw, rfl⟩

/-- Every finite convex hull in a finite-dimensional vector space is polyhedral. -/
theorem isPolyhedral_convexHull_of_finite {V : Set E} (hV : V.Finite) :
    IsPolyhedral 𝕜 (convexHull 𝕜 V) := by
  classical
  let := hV.fintype
  have hr : range (Subtype.val : V → E) = V := Subtype.range_coe_subtype
  rw [← hr, convexHull_range_eq_image_linearCombination]
  exact (IsPolyhedral.weights V).linear_image (Fintype.linearCombination 𝕜 Subtype.val)

end FiniteDimensional

end EulerPolyhedron

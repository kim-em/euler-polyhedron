/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import EulerPolyhedron.Elimination
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# A finite convex hull has a finite halfspace presentation

A finite convex hull is the image of the standard simplex of barycentric
weights. We express its graph by finitely many linear inequalities and
eliminate the weights. This works in every finite dimension.
-/

open Set
open scoped BigOperators

namespace EulerPolyhedron

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- A point is cut out by finitely many coordinate equalities, each expressed
as two closed halfspaces. -/
theorem Polyhedral.zero : Polyhedral E {0} := by
  classical
  let b := Module.finBasis ℝ E
  have hp := Polyhedral.of_finite (fun i => b.coord i) (fun _ => (0 : ℝ))
  have hn := Polyhedral.of_finite (fun i => -b.coord i) (fun _ => (0 : ℝ))
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
theorem Polyhedral.linear_eq_zero {F : Type*} [AddCommGroup F] [Module ℝ F]
    (f : F →ₗ[ℝ] E) : Polyhedral F {x | f x = 0} := by
  convert (Polyhedral.zero (E := E)).preimage f using 1
  ext x
  simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]

/-- Linear images from a finite real coordinate space preserve polyhedrality. -/
theorem Polyhedral.image_fin {n : ℕ} {s : Set (Fin n → ℝ)}
    (hs : Polyhedral (Fin n → ℝ) s) (f : (Fin n → ℝ) →ₗ[ℝ] E) :
    Polyhedral E (f '' s) := by
  let g : ((Fin n → ℝ) × E) →ₗ[ℝ] E :=
    LinearMap.snd ℝ (Fin n → ℝ) E - f.comp (LinearMap.fst ℝ (Fin n → ℝ) E)
  have h := (hs.preimage (LinearMap.fst ℝ (Fin n → ℝ) E)).inter
    (Polyhedral.linear_eq_zero g)
  convert h.project_fin n using 1
  ext x
  simp only [mem_image, mem_ofPred_eq, mem_inter_iff, mem_preimage, LinearMap.fst_apply,
    g, LinearMap.sub_apply, LinearMap.snd_apply, LinearMap.comp_apply, sub_eq_zero]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, hx⟩
    exact ⟨w, hw, hx.symm⟩

/-- The simplex of all nonnegative weights with sum one is polyhedral. -/
theorem Polyhedral.weights (n : ℕ) :
    Polyhedral (Fin n → ℝ) {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} := by
  have hnonneg := Polyhedral.of_finite
    (fun i : Fin n => -(LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ)) (fun _ => (0 : ℝ))
  let sum : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ i, LinearMap.proj i
  have hle := Polyhedral.of_finite (fun _ : Unit => sum) (fun _ => (1 : ℝ))
  have hge := Polyhedral.of_finite (fun _ : Unit => -sum) (fun _ => (-1 : ℝ))
  convert hnonneg.inter (hle.inter hge) using 1
  ext w
  change ((∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1) ↔
    (∀ i : Fin n, (-(LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ)) w ≤ 0) ∧
      (∀ _ : Unit, sum w ≤ 1) ∧ (∀ _ : Unit, (-sum) w ≤ -1)
  have hsum : sum w = ∑ i, w i := by simp [sum, LinearMap.sum_apply]
  simp only [LinearMap.neg_apply, LinearMap.proj_apply, neg_nonpos,
    forall_const, hsum, neg_le_neg_iff, le_antisymm_iff]

private def weightedSum {n : ℕ} (v : Fin n → E) : (Fin n → ℝ) →ₗ[ℝ] E where
  toFun w := ∑ i, w i • v i
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a w := by simp [mul_smul, Finset.smul_sum]

omit [FiniteDimensional ℝ E] in
/-- The finite convex hull is precisely the set of barycentric combinations. -/
theorem convexHull_range_weights {n : ℕ} (v : Fin n → E) :
    convexHull ℝ (range v) =
      weightedSum v '' {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} := by
  classical
  apply subset_antisymm (convexHull_min ?_ ?_) ?_
  · rintro _ ⟨i, rfl⟩
    refine ⟨(Pi.single i (1 : ℝ) : Fin n → ℝ), ⟨?_, ?_⟩, ?_⟩
    · intro j
      by_cases h : j = i <;> simp [h]
    · simp [Pi.single_apply, Finset.sum_ite_eq']
    · change ∑ j, (Pi.single i (1 : ℝ) : Fin n → ℝ) j • v j = v i
      simp [Pi.single_apply, ite_smul, Finset.sum_ite_eq']
  · rintro x ⟨w, ⟨hw, hw1⟩, rfl⟩ y ⟨z, ⟨hz, hz1⟩, rfl⟩ a b ha hb hab
    refine ⟨a • w + b • z, ⟨?_, ?_⟩, ?_⟩
    · intro i
      exact add_nonneg (mul_nonneg ha (hw i)) (mul_nonneg hb (hz i))
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hw1, hz1, mul_one, hab]
    · simp [weightedSum, add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
  · rintro x ⟨w, ⟨hw, hw1⟩, rfl⟩
    exact (convex_convexHull ℝ (range v)).sum_mem (fun i _ => hw i) hw1
      (fun i _ => subset_convexHull ℝ _ (mem_range_self i))

/-- Every finite convex hull in a finite-dimensional real vector space is polyhedral. -/
theorem polyhedral_convexHull_finite {V : Set E} (hV : V.Finite) :
    Polyhedral E (convexHull ℝ V) := by
  classical
  let := hV.fintype
  let e := (Fintype.equivFin V).symm
  let v : Fin (Fintype.card V) → E := fun i => (e i).val
  have hr : range v = V := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp [v]⟩
  rw [← hr, convexHull_range_weights]
  exact (Polyhedral.weights _).image_fin (weightedSum v)

end EulerPolyhedron

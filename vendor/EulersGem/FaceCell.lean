/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.Cone
import Mathlib.Analysis.Convex.Segment
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Topology.MetricSpace.Basic

/-!
# Face ↔ cell substrate for halfspace cones (Paulson `hyper1` / `hyper2`)

Proved for nontrivial closed halfspace cones `{⟪a,x⟫ ≤ 0}`:

* cells of `{(a,0)}` inside the cone = `{open halfspace, hyperplane}`
* affine faces of an affine subspace are trivial
* interior / affDim of the halfspace cone
* nonempty faces contained in the bounding hyperplane equal that hyperplane
* the full cone is a face; meeting the open halfspace forces the face to be the cone
  (via a small radial step into the interior)
* therefore nonempty faces = `{cone, hyperplane}`, and `faceEulerSum = 0`

General polyhedral cones: **hyper2** (cell → face via closure) is in `ConeFaceCell`;
hyper1 / RI recovery / `faceEulerSum` still open.
-/

open scoped RealInnerProductSpace BigOperators
open Classical Set AffineSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace EulersGem

/-- Faces of the carrier of an affine subspace are empty or the whole carrier.
Isabelle: `face_of_affine_trivial`. -/
lemma isFaceOf_coe_affineSubspace {T : AffineSubspace ℝ E} {F : Set E}
    (hF : IsFaceOf (T : Set E) F) (hne : F.Nonempty) : F = (T : Set E) := by
  obtain ⟨z, hz⟩ := hne
  refine subset_antisymm hF.isExtreme.subset ?_
  intro x hx
  let y : E := AffineMap.lineMap x z (2 : ℝ)
  have hyT : y ∈ (T : Set E) := AffineMap.lineMap_mem (2 : ℝ) hx (hF.isExtreme.subset hz)
  have hzEq : AffineMap.lineMap x y ((1 : ℝ) / 2) = z := by
    simp [y, AffineMap.lineMap_apply_module]
    module
  have hzSeg : z ∈ openSegment ℝ x y := by
    rw [← hzEq]
    exact lineMap_mem_openSegment (𝕜 := ℝ) x y (t := (1 : ℝ) / 2)
      ⟨by norm_num, by norm_num⟩
  exact hF.isExtreme.left_mem_of_mem_openSegment hx hyT hz hzSeg

lemma interior_closedHalfspace_zero {a : E} (ha : a ≠ 0) :
    interior (closedHalfspace a 0) = {x : E | ⟪a, x⟫ < 0} := by
  apply subset_antisymm
  · intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
    by_contra hnot
    have hxS : x ∈ closedHalfspace a 0 := interior_subset hx
    change ⟪a, x⟫ ≤ 0 at hxS
    have hx0 : ⟪a, x⟫ = 0 := le_antisymm hxS (le_of_not_gt hnot)
    let t : ℝ := ε / (2 * ‖a‖)
    have ht : 0 < t := div_pos hε (by positivity)
    have hdist : dist (x + t • a) x < ε := by
      simp [dist_eq_norm, norm_smul, Real.norm_of_nonneg ht.le]
      have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
      have hteq : t * ‖a‖ = ε / 2 := by simp only [t]; field_simp [hna]
      linarith [hteq]
    have hin : x + t • a ∈ closedHalfspace a 0 := hball hdist
    change ⟪a, x + t • a⟫ ≤ 0 at hin
    have hcalc : ⟪a, x⟫ + t * ⟪a, a⟫ ≤ 0 := by
      simpa [inner_add_right, inner_smul_right] using hin
    have hpos : 0 < ⟪a, a⟫ := real_inner_self_pos.mpr ha
    rw [hx0] at hcalc
    nlinarith
  · intro x hx
    rw [mem_interior]
    exact ⟨{y | ⟪a, y⟫ < 0},
      fun y (hy : ⟪a, y⟫ < 0) => (le_of_lt hy : y ∈ closedHalfspace a 0),
      isOpen_halfSpace_lt a 0, hx⟩

lemma affineSpan_closedHalfspace_zero [FiniteDimensional ℝ E] [Nonempty E]
    {a : E} (ha : a ≠ 0) :
    affineSpan ℝ (closedHalfspace a 0) = ⊤ := by
  have hine : (interior (closedHalfspace a 0)).Nonempty := by
    rw [interior_closedHalfspace_zero ha]
    refine ⟨-a, ?_⟩
    change ⟪a, -a⟫ < 0
    have : 0 < ⟪a, a⟫ := real_inner_self_pos.mpr ha
    simpa [inner_neg_right] using neg_lt_zero.mpr this
  exact (Convex.interior_nonempty_iff_affineSpan_eq_top
    (convex_closedHalfspace a 0)).mp hine

lemma affDim_closedHalfspace_zero [FiniteDimensional ℝ E] [Nonempty E]
    {a : E} (ha : a ≠ 0) :
    affDim (closedHalfspace a 0) = Module.finrank ℝ E := by
  have hspan := affineSpan_closedHalfspace_zero ha
  have : affineSpan ℝ (closedHalfspace a 0) = affineSpan ℝ (univ : Set E) :=
    hspan.trans (affineSpan_univ (E := E)).symm
  exact (affDim_eq_of_affineSpan_eq this).trans affDim_univ

lemma closedHalfspace_ne_hyperplane {a : E} (ha : a ≠ 0) :
    closedHalfspace a 0 ≠ {x : E | ⟪a, x⟫ = 0} := by
  intro heq
  have hin : (-a) ∈ closedHalfspace a 0 := by
    change ⟪a, -a⟫ ≤ 0
    simp [inner_neg_right]
  have : ⟪a, -a⟫ = 0 := by
    have : (-a) ∈ {x : E | ⟪a, x⟫ = 0} := by simpa [← heq] using hin
    exact this
  have : ⟪a, a⟫ = 0 := by simpa [inner_neg_right] using this
  exact ha (inner_self_eq_zero.mp this)

lemma affDim_openHalfspace_lt [FiniteDimensional ℝ E] [Nonempty E]
    {a : E} (ha : a ≠ 0) :
    affDim {x : E | ⟪a, x⟫ < 0} = Module.finrank ℝ E := by
  have hne : ({x : E | ⟪a, x⟫ < 0}).Nonempty :=
    ⟨-a, by
      change ⟪a, -a⟫ < 0
      have : 0 < ⟪a, a⟫ := real_inner_self_pos.mpr ha
      simpa [inner_neg_right] using neg_lt_zero.mpr this⟩
  have hopen : IsOpen {x : E | ⟪a, x⟫ < 0} := isOpen_halfSpace_lt a 0
  have hspan : affineSpan ℝ {x : E | ⟪a, x⟫ < 0} = ⊤ := by
    have := affineSpan_isOpen_inter (T := ⊤) hopen (by simpa using hne)
    simpa using this
  have : affineSpan ℝ {x : E | ⟪a, x⟫ < 0} = affineSpan ℝ (univ : Set E) :=
    hspan.trans (affineSpan_univ (E := E)).symm
  exact (affDim_eq_of_affineSpan_eq this).trans affDim_univ

/-- Arrangement cells contained in the closed halfspace (nontrivial case). -/
lemma cells_subset_closedHalfspace_zero {a : E} (ha : a ≠ 0) :
    {C : Set E | IsHyperplaneCell {(a, (0 : ℝ))} C ∧ C ⊆ closedHalfspace a 0} =
      ({{x : E | ⟪a, x⟫ < 0}, {x : E | ⟪a, x⟫ = 0}} : Set (Set E)) := by
  ext C
  constructor
  · intro ⟨hC, hsub⟩
    rcases isHyperplaneCell_singleton_cases hC with heq | hlt | hgt
    · exact Or.inr (by simp [heq])
    · exact Or.inl (by simp [hlt])
    · obtain ⟨x, hx⟩ := nonempty_isHyperplaneCell hC
      have hxgt : (0 : ℝ) < ⟪a, x⟫ := by simpa [hgt] using hx
      have hxS : x ∈ closedHalfspace a 0 := hsub hx
      change ⟪a, x⟫ ≤ 0 at hxS
      exact (not_lt_of_ge hxS hxgt).elim
  · intro hC
    rcases (show C = {x | ⟪a, x⟫ < 0} ∨ C = {x | ⟪a, x⟫ = 0} by
      simpa [mem_insert_iff, mem_singleton_iff] using hC) with rfl | rfl
    · exact ⟨isHyperplaneCell_eq_halfSpace_lt ha,
        fun x (hx : ⟪a, x⟫ < 0) => (le_of_lt hx : x ∈ closedHalfspace a 0)⟩
    · exact ⟨isHyperplaneCell_eq_hyperplane ha, fun _ hx => le_of_eq hx⟩

/-- A face that meets the open halfspace equals the whole closed halfspace. -/
lemma isFaceOf_closedHalfspace_of_mem_open {a : E} (ha : a ≠ 0) {F : Set E}
    (hF : IsFaceOf (closedHalfspace a 0) F)
    (hmeet : (F ∩ {x : E | ⟪a, x⟫ < 0}).Nonempty) :
    F = closedHalfspace a 0 := by
  refine subset_antisymm hF.isExtreme.subset ?_
  intro x hx
  obtain ⟨z, hzF, hzlt⟩ := hmeet
  by_cases hxz : x = z
  · simpa [hxz] using hzF
  · have hzInt : z ∈ interior (closedHalfspace a 0) := by
      rwa [interior_closedHalfspace_zero ha]
    obtain ⟨ε, hε, hball⟩ :=
      Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzInt)
    have hnz : z - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxz)
    let δ : ℝ := min (1 / 2) (ε / (2 * ‖z - x‖))
    have hδ0 : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
    let y : E := z + δ • (z - x)
    have hyS : y ∈ closedHalfspace a 0 := by
      refine hball ?_
      have hdist : dist y z = δ * ‖z - x‖ := by
        simp [y, dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hδ0.le]
      have hna : ‖z - x‖ ≠ 0 := norm_ne_zero_iff.mpr hnz
      have hle : δ ≤ ε / (2 * ‖z - x‖) := min_le_right _ _
      have hhalf : ε / (2 * ‖z - x‖) * ‖z - x‖ = ε / 2 := by field_simp [hna]
      have hmul : δ * ‖z - x‖ ≤ ε / 2 := by
        have := mul_le_mul_of_nonneg_right hle (norm_nonneg (z - x))
        rwa [hhalf] at this
      calc dist y z = δ * ‖z - x‖ := hdist
        _ ≤ ε / 2 := hmul
        _ < ε := by linarith
    have hzSeg : z ∈ openSegment ℝ x y := by
      have hden : (1 + δ : ℝ) ≠ 0 := by linarith
      have hy_line : y = AffineMap.lineMap x z (1 + δ) := by
        simp only [y, AffineMap.lineMap_apply_module]
        module
      have hcomp :
          AffineMap.lineMap x y (1 / (1 + δ)) =
            AffineMap.lineMap x z ((1 + δ) * (1 / (1 + δ))) := by
        simp only [hy_line, AffineMap.lineMap_apply_module]
        module
      have hmul : (1 + δ) * (1 / (1 + δ) : ℝ) = 1 := by field_simp [hden]
      have hzEq : AffineMap.lineMap x y (1 / (1 + δ)) = z := by
        rw [hcomp, hmul, AffineMap.lineMap_apply_one]
      rw [← hzEq]
      exact lineMap_mem_openSegment (𝕜 := ℝ) x y (t := 1 / (1 + δ))
        ⟨div_pos one_pos (by linarith), by
          rw [div_lt_one (by linarith)]; linarith⟩
    exact hF.isExtreme.left_mem_of_mem_openSegment hx hyS hzF hzSeg

/-- Nonempty faces of a nontrivial closed halfspace cone are exactly the cone and its
bounding hyperplane. -/
lemma isFaceOf_closedHalfspace_zero_eq {a : E} (ha : a ≠ 0) {F : Set E}
    (hF : IsFaceOf (closedHalfspace a 0) F) (hne : F.Nonempty) :
    F = closedHalfspace a 0 ∨ F = {x : E | ⟪a, x⟫ = 0} := by
  by_cases hmeet : (F ∩ {x : E | ⟪a, x⟫ < 0}).Nonempty
  · exact Or.inl (isFaceOf_closedHalfspace_of_mem_open ha hF hmeet)
  · refine Or.inr ?_
    have hsub : F ⊆ {x : E | ⟪a, x⟫ = 0} := by
      intro x hxF
      have hxS : x ∈ closedHalfspace a 0 := hF.isExtreme.subset hxF
      change ⟪a, x⟫ ≤ 0 at hxS
      have : ¬ ⟪a, x⟫ < 0 := fun hlt => hmeet ⟨x, hxF, hlt⟩
      exact le_antisymm hxS (le_of_not_gt this)
    have hH : IsFaceOf {x : E | ⟪a, x⟫ = 0} F :=
      ⟨IsExtreme.mono hF.isExtreme
        (isFaceOf_closedHalfspace_hyperplane a).isExtreme.subset hsub, hF.convex⟩
    obtain ⟨p, hp⟩ := exists_mem_hyperplane (b := (0 : ℝ)) ha
    let H := affineHyperplane a 0 p hp
    have hcoe : (H : Set E) = {x | ⟪a, x⟫ = 0} := coe_affineHyperplane a 0 p hp
    have hF' : IsFaceOf (H : Set E) F := by simpa [hcoe] using hH
    have : F = (H : Set E) := isFaceOf_coe_affineSubspace hF' hne
    simpa [hcoe] using this

lemma faces_closedHalfspace_zero_eq {a : E} (ha : a ≠ 0) :
    {F : Set E | IsFaceOf (closedHalfspace a 0) F ∧ F.Nonempty} =
      ({closedHalfspace a 0, {x : E | ⟪a, x⟫ = 0}} : Set (Set E)) := by
  ext F
  constructor
  · intro ⟨hF, hne⟩
    rcases isFaceOf_closedHalfspace_zero_eq ha hF hne with h | h <;> simp [h]
  · intro hF
    rcases (show F = closedHalfspace a 0 ∨ F = {x | ⟪a, x⟫ = 0} by
      simpa [mem_insert_iff, mem_singleton_iff] using hF) with rfl | rfl
    · refine ⟨isFaceOf_refl (convex_closedHalfspace a 0), ⟨0, ?_⟩⟩
      change ⟪a, (0 : E)⟫ ≤ 0
      simp [inner_zero_right]
    · exact ⟨isFaceOf_closedHalfspace_hyperplane a, ⟨0, by simp⟩⟩

/-- Combinatorial face Euler sum of a nontrivial halfspace cone is `0`.
Special case of Paulson `Euler_polyhedral_cone`. -/
theorem faceEulerSum_halfspace_cone [FiniteDimensional ℝ E] [Nonempty E]
    {a : E} (ha : a ≠ 0) :
    faceEulerSum (closedHalfspace a 0) (Module.finrank ℝ E) = 0 := by
  set n := Module.finrank ℝ E
  have hnpos : 0 < n := by
    by_contra h
    have : Subsingleton E :=
      Module.finrank_zero_iff.mp (Nat.eq_zero_of_not_pos h)
    exact ha (Subsingleton.elim a 0)
  have hS : affDim (closedHalfspace a 0) = (n : ℤ) := affDim_closedHalfspace_zero ha
  have hH : affDim {x : E | ⟪a, x⟫ = 0} = (n : ℤ) - 1 := affDim_linear_hyperplane ha
  have hcard_n :
      {F : Set E | IsFaceOf (closedHalfspace a 0) F ∧ affDim F = (n : ℤ)}.ncard = 1 := by
    have hset :
        {F : Set E | IsFaceOf (closedHalfspace a 0) F ∧ affDim F = (n : ℤ)} =
          {closedHalfspace a 0} := by
      ext F; constructor
      · intro ⟨hF, hdim⟩
        have hne : F.Nonempty := by
          by_contra hempty
          simp [not_nonempty_iff_eq_empty.mp hempty, affDim_empty] at hdim
        rcases isFaceOf_closedHalfspace_zero_eq ha hF hne with rfl | rfl
        · rfl
        · exact absurd hdim (by rw [hH]; omega)
      · rintro rfl
        exact ⟨isFaceOf_refl (convex_closedHalfspace a 0), hS⟩
    simp [hset]
  have hcard_n1 :
      {F : Set E | IsFaceOf (closedHalfspace a 0) F ∧ affDim F = ((n - 1 : ℕ) : ℤ)}.ncard = 1 := by
    have hdim : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    have hset :
        {F : Set E | IsFaceOf (closedHalfspace a 0) F ∧ affDim F = ((n - 1 : ℕ) : ℤ)} =
          {{x : E | ⟪a, x⟫ = 0}} := by
      ext F; constructor
      · intro ⟨hF, hdimF⟩
        have hne : F.Nonempty := by
          by_contra hempty
          simp [not_nonempty_iff_eq_empty.mp hempty, affDim_empty] at hdimF
        rcases isFaceOf_closedHalfspace_zero_eq ha hF hne with rfl | rfl
        · exact absurd hdimF (by rw [hS, hdim]; omega)
        · rfl
      · rintro rfl
        exact ⟨isFaceOf_closedHalfspace_hyperplane a, by rw [hdim, hH]⟩
    simp [hset]
  have hcard_other : ∀ d < n + 1, d ≠ n → d ≠ n - 1 →
      {F : Set E | IsFaceOf (closedHalfspace a 0) F ∧ affDim F = (d : ℤ)}.ncard = 0 := by
    intro d _hd hdn hdn1
    have hset :
        {F : Set E | IsFaceOf (closedHalfspace a 0) F ∧ affDim F = (d : ℤ)} = ∅ := by
      ext F
      simp only [mem_empty_iff_false, mem_ofPred_eq, iff_false]
      intro ⟨hF, hdim⟩
      have hne : F.Nonempty := by
        by_contra hempty
        simp [not_nonempty_iff_eq_empty.mp hempty, affDim_empty] at hdim
      rcases isFaceOf_closedHalfspace_zero_eq ha hF hne with rfl | rfl
      · exact hdn (by omega)
      · exact hdn1 (by omega)
    simp [hset]
  unfold faceEulerSum
  have hsub : ({n - 1, n} : Finset ℕ) ⊆ Finset.range (n + 1) := by
    intro x hx; simp at hx ⊢; omega
  rw [← Finset.sum_sdiff hsub]
  have hrest :
      ∑ d ∈ Finset.range (n + 1) \ {n - 1, n},
        (-1 : ℤ) ^ d *
          ({F : Set E | IsFaceOf (closedHalfspace a 0) F ∧ affDim F = (d : ℤ)}.ncard : ℤ) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    have hd' : d ∈ Finset.range (n + 1) ∧ d ≠ n - 1 ∧ d ≠ n := by
      simpa [Finset.mem_sdiff] using hd
    rw [hcard_other d (Finset.mem_range.mp hd'.1) hd'.2.2 hd'.2.1]; simp
  have hpair :
      ∑ d ∈ ({n - 1, n} : Finset ℕ),
        (-1 : ℤ) ^ d *
          ({F : Set E | IsFaceOf (closedHalfspace a 0) F ∧ affDim F = (d : ℤ)}.ncard : ℤ) =
        (-1 : ℤ) ^ (n - 1) + (-1 : ℤ) ^ n := by
    have hnin : n - 1 ∉ ({n} : Finset ℕ) := by simp; omega
    simp [Finset.sum_insert hnin, hcard_n, hcard_n1]
  rw [hrest, hpair, zero_add]
  -- (-1)^{n-1} + (-1)^n = 0; avoid rewriting `n` inside `n-1`
  have hpow : (-1 : ℤ) ^ n = -((-1 : ℤ) ^ (n - 1)) := by
    have hn' : n = (n - 1) + 1 := (Nat.sub_add_cancel hnpos).symm
    conv_lhs => rw [hn']
    rw [pow_succ]; ring
  rw [hpow]; ring

end EulersGem

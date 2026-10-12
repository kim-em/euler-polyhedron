/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.FaceCell
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Order.OrderClosed

/-!
# General cone face ↔ cell substrate (Paulson `hyper1` / `hyper2`)

Beyond the halfspace special case in `FaceCell`:

* closure of a nontrivial open halfspace
* sign-pattern dichotomy for cone-arrangement cells inside a polyhedral cone
* supporting-hyperplane faces from finite zero-sets
* **hyper2 (face direction):** closure of a cell ⊆ cone is a face of the cone

Beyond hyper2:

* face characterization via vanishing normals
* RI of a face is the open sign-pattern cell (Paulson `hyper1`)
* hence `faceEulerSum = eulerCharacteristic = 0` for proper full-dim cones
-/

open scoped RealInnerProductSpace BigOperators
open Classical Set AffineSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace EulersGem

/-! ### Closure of open halfspaces -/

lemma isClosed_closedHalfspace (a : E) (b : ℝ) : IsClosed (closedHalfspace a b) :=
  isClosed_le (continuous_const.inner continuous_id) continuous_const

/-- Nontrivial open halfspace `{⟪a,x⟫ < 0}` has closure the closed halfspace. -/
lemma closure_halfSpace_lt {a : E} (ha : a ≠ 0) :
    closure {x : E | ⟪a, x⟫ < 0} = closedHalfspace a 0 := by
  apply subset_antisymm
  · exact closure_minimal (fun x (hx : ⟪a, x⟫ < 0) => (le_of_lt hx : x ∈ closedHalfspace a 0))
      (isClosed_closedHalfspace a 0)
  · intro x hx
    change ⟪a, x⟫ ≤ 0 at hx
    refine mem_closure_iff_nhds.2 fun U hU => ?_
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
    let t : ℝ := ε / (2 * ‖a‖)
    have ht : 0 < t := div_pos hε (by positivity)
    refine ⟨x - t • a, hball ?_, ?_⟩
    · simp [norm_smul, Real.norm_of_nonneg ht.le]
      have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
      have : t * ‖a‖ = ε / 2 := by simp only [t]; field_simp [hna]
      linarith
    · change ⟪a, x - t • a⟫ < 0
      have hpos : 0 < ⟪a, a⟫ := real_inner_self_pos.mpr ha
      have : ⟪a, x⟫ - t * ⟪a, a⟫ < 0 := by
        have : 0 < t * ⟪a, a⟫ := by positivity
        linarith
      simpa [inner_sub_right, inner_smul_right] using this

/-- Finite intersection of open halfspaces: closure is the closed orthant. -/
lemma closure_iInter_halfSpace_lt {As : Set E} (hAs : As.Finite)
    (hne : ({x : E | ∀ a ∈ As, ⟪a, x⟫ < 0}).Nonempty) :
    closure {x : E | ∀ a ∈ As, ⟪a, x⟫ < 0} =
      {x : E | ∀ a ∈ As, ⟪a, x⟫ ≤ 0} := by
  apply subset_antisymm
  · refine closure_minimal (fun x hx a ha => le_of_lt (hx a ha)) ?_
    classical
    have hEq : {x : E | ∀ a ∈ As, ⟪a, x⟫ ≤ 0} =
        ⋂ a ∈ hAs.toFinset, closedHalfspace a 0 := by
      ext x; simp [Finite.mem_toFinset, closedHalfspace]
    rw [hEq]
    exact isClosed_biInter fun _ _ => isClosed_closedHalfspace _ _
  · intro x hx
    obtain ⟨z, hz⟩ := hne
    refine mem_closure_iff_nhds.2 fun U hU => ?_
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
    let t : ℝ := min (1 / 2) (ε / (2 * (‖z - x‖ + 1)))
    have ht0 : 0 < t := lt_min (by norm_num) (div_pos hε (by positivity))
    have ht1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
    let y : E := (1 - t) • x + t • z
    have hyOpen : ∀ a ∈ As, ⟪a, y⟫ < 0 := by
      intro a ha
      have hxA : ⟪a, x⟫ ≤ 0 := hx a ha
      have hzA : ⟪a, z⟫ < 0 := hz a ha
      have : ⟪a, y⟫ = (1 - t) * ⟪a, x⟫ + t * ⟪a, z⟫ := by
        simp only [y, inner_add_right, inner_smul_right]
      rw [this]
      have h1 : (1 - t) * ⟪a, x⟫ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht1) hxA
      have h2 : t * ⟪a, z⟫ < 0 := mul_neg_of_pos_of_neg ht0 hzA
      linarith
    have hdist : dist y x < ε := by
      have hdist' : dist y x = t * ‖z - x‖ := by
        simp only [y, dist_eq_norm]
        have : (1 - t) • x + t • z - x = t • (z - x) := by module
        rw [this, norm_smul, Real.norm_of_nonneg ht0.le]
      have hle : t ≤ ε / (2 * (‖z - x‖ + 1)) := min_le_right _ _
      have hden : 0 < ‖z - x‖ + 1 := by positivity
      have hfrac : ε / (2 * (‖z - x‖ + 1)) * ‖z - x‖ ≤ ε / 2 := by
        have hnn : 0 ≤ ‖z - x‖ := norm_nonneg _
        have hε0 : 0 ≤ ε := le_of_lt hε
        field_simp
        nlinarith
      have hmul : t * ‖z - x‖ ≤ ε / 2 := by
        have := mul_le_mul_of_nonneg_right hle (norm_nonneg (z - x))
        linarith
      calc dist y x = t * ‖z - x‖ := hdist'
        _ ≤ ε / 2 := hmul
        _ < ε := by linarith
    exact ⟨y, hball hdist, hyOpen⟩

/-! ### Sign patterns on cone-arrangement cells -/

/-- Normals that vanish identically on a cell. -/
def coneCellZeros (As : Set E) (C : Set E) : Set E :=
  {a ∈ As | ∀ x ∈ C, ⟪a, x⟫ = 0}

/-- Normals that are strictly negative on a cell. -/
def coneCellNegs (As : Set E) (C : Set E) : Set E :=
  {a ∈ As | ∀ x ∈ C, ⟪a, x⟫ < 0}

lemma coneCellZeros_subset (As : Set E) (C : Set E) : coneCellZeros As C ⊆ As :=
  fun _a ha => ha.1

lemma coneCellNegs_subset (As : Set E) (C : Set E) : coneCellNegs As C ⊆ As :=
  fun _a ha => ha.1

lemma coneCellZeros_disjoint_negs {As C : Set E} (hne : C.Nonempty) :
    Disjoint (coneCellZeros As C) (coneCellNegs As C) := by
  refine disjoint_left.mpr ?_
  intro a haZ haN
  obtain ⟨x, hx⟩ := hne
  have hlt := haN.2 x hx
  have heq := haZ.2 x hx
  linarith

/-- On a cone-arrangement cell contained in the polyhedral cone, every normal is either
identically zero or strictly negative. -/
lemma coneCell_sign_dichotomy {As : Set E} {C : Set E}
    (hC : IsHyperplaneCell (coneArrangement As) C)
    (hsub : C ⊆ ⋂ a ∈ As, closedHalfspace a 0) :
    As = coneCellZeros As C ∪ coneCellNegs As C := by
  obtain ⟨x, rfl⟩ := hC
  ext a
  constructor
  · intro ha
    have hxS : x ∈ closedHalfspace a 0 :=
      (mem_iInter.mp ((mem_iInter.mp (hsub (hyperplaneEquiv_refl _ x))) a)) ha
    change ⟪a, x⟫ ≤ 0 at hxS
    by_cases h0 : ⟪a, x⟫ = 0
    · refine Or.inl ⟨ha, ?_⟩
      intro y hy
      have hside : hyperplaneSide (a, (0 : ℝ)) x = hyperplaneSide (a, (0 : ℝ)) y :=
        hy (a, (0 : ℝ)) ⟨a, ha, rfl⟩
      have hxside : hyperplaneSide (a, (0 : ℝ)) x = 0 :=
        (hyperplaneSide_eq_zero_iff a 0 x).mpr h0
      exact (hyperplaneSide_eq_zero_iff a 0 y).mp (hside ▸ hxside)
    · have hlt : ⟪a, x⟫ < 0 := lt_of_le_of_ne hxS h0
      refine Or.inr ⟨ha, ?_⟩
      intro y hy
      have hside : hyperplaneSide (a, (0 : ℝ)) x = hyperplaneSide (a, (0 : ℝ)) y :=
        hy (a, (0 : ℝ)) ⟨a, ha, rfl⟩
      have hxside : hyperplaneSide (a, (0 : ℝ)) x = -1 :=
        (hyperplaneSide_eq_neg_one_iff a 0 x).mpr hlt
      exact (hyperplaneSide_eq_neg_one_iff a 0 y).mp (hside ▸ hxside)
  · rintro (h | h) <;> exact h.1

/-- Explicit sign-pattern description of a cone-arrangement cell inside the cone. -/
lemma coneCell_eq_sign_pattern {As : Set E} {C : Set E}
    (hC : IsHyperplaneCell (coneArrangement As) C)
    (hsub : C ⊆ ⋂ a ∈ As, closedHalfspace a 0) :
    C = {x : E | (∀ a ∈ coneCellNegs As C, ⟪a, x⟫ < 0) ∧
      (∀ a ∈ coneCellZeros As C, ⟪a, x⟫ = 0)} := by
  obtain ⟨z, rfl⟩ := hC
  set C : Set E := {y | HyperplaneEquiv (coneArrangement As) z y}
  have hdich := coneCell_sign_dichotomy (C := C) ⟨z, rfl⟩ hsub
  ext y
  constructor
  · intro hy
    exact ⟨fun a ha => ha.2 y hy, fun a ha => ha.2 y hy⟩
  · intro ⟨hyNeg, hyZero⟩ h hh
    obtain ⟨a, ha, rfl⟩ := hh
    have ha' : a ∈ coneCellZeros As C ∪ coneCellNegs As C := by
      rw [← hdich]; exact ha
    rcases ha' with haZ | haN
    · have hz0 : ⟪a, z⟫ = 0 := haZ.2 z (hyperplaneEquiv_refl _ z)
      have hy0 : ⟪a, y⟫ = 0 := hyZero a haZ
      rw [(hyperplaneSide_eq_zero_iff a 0 z).mpr hz0,
        (hyperplaneSide_eq_zero_iff a 0 y).mpr hy0]
    · have hzlt : ⟪a, z⟫ < 0 := haN.2 z (hyperplaneEquiv_refl _ z)
      have hylt : ⟪a, y⟫ < 0 := hyNeg a haN
      rw [(hyperplaneSide_eq_neg_one_iff a 0 z).mpr hzlt,
        (hyperplaneSide_eq_neg_one_iff a 0 y).mpr hylt]

/-! ### Supporting-hyperplane faces (finite intersections) -/

/-- Intersection of a polyhedral cone with finitely many defining hyperplanes is a face. -/
lemma isFaceOf_polyhedralCone_inter_zeros {As : Set E} {J : Set E} (hJ : J ⊆ As)
    (hJfin : J.Finite) :
    IsFaceOf (⋂ a ∈ As, closedHalfspace a 0)
      ((⋂ a ∈ As, closedHalfspace a 0) ∩ ⋂ a ∈ J, {x : E | ⟪a, x⟫ = 0}) := by
  classical
  refine Set.Finite.induction_on
    (motive := fun J' _ => J' ⊆ As →
      IsFaceOf (⋂ a ∈ As, closedHalfspace a 0)
        ((⋂ a ∈ As, closedHalfspace a 0) ∩ ⋂ a ∈ J', {x : E | ⟪a, x⟫ = 0}))
    J hJfin ?empty ?insert hJ
  · intro _
    have hEq : (⋂ a ∈ As, closedHalfspace a 0) ∩ ⋂ a ∈ (∅ : Set E), {x : E | ⟪a, x⟫ = 0} =
        ⋂ a ∈ As, closedHalfspace a 0 := by
      ext x; simp
    rw [hEq]
    exact isFaceOf_refl (convex_iInter fun a => convex_iInter fun _ => convex_closedHalfspace a 0)
  · intro a J' _haJ' _hJ'fin ih hsub
    have ha : a ∈ As := hsub (mem_insert a J')
    have hrest : J' ⊆ As := (subset_insert _ _).trans hsub
    have hEq :
        (⋂ b ∈ As, closedHalfspace b 0) ∩ ⋂ b ∈ insert a J', {x : E | ⟪b, x⟫ = 0} =
          ((⋂ b ∈ As, closedHalfspace b 0) ∩ ⋂ b ∈ J', {x : E | ⟪b, x⟫ = 0}) ∩
            ((⋂ b ∈ As, closedHalfspace b 0) ∩ {x : E | ⟪a, x⟫ = 0}) := by
      ext x
      simp only [mem_inter_iff, mem_iInter, mem_insert_iff, mem_ofPred_eq]
      constructor
      · intro ⟨hxS, hxJ⟩
        exact ⟨⟨hxS, fun b hb => hxJ b (Or.inr hb)⟩, hxS, hxJ a (Or.inl rfl)⟩
      · rintro ⟨⟨hxS, hxJ'⟩, -, hxa⟩
        refine ⟨hxS, ?_⟩
        intro b hb
        rcases hb with rfl | hb
        · exact hxa
        · exact hxJ' b hb
    rw [hEq]
    exact isFaceOf_inter (ih hrest) (isFaceOf_polyhedralCone_eq_hyperplane ha)

lemma isClosed_iInter_hyperplanes {J : Set E} (hJ : J.Finite) :
    IsClosed (⋂ a ∈ J, {x : E | ⟪a, x⟫ = 0}) := by
  classical
  have hEq : (⋂ a ∈ J, {x : E | ⟪a, x⟫ = 0}) =
      ⋂ a ∈ hJ.toFinset, {x : E | ⟪a, x⟫ = 0} := by
    ext x; simp [Finite.mem_toFinset]
  rw [hEq]
  exact isClosed_biInter fun _ _ =>
    isClosed_eq (continuous_const.inner continuous_id) continuous_const

lemma cone_face_eq_closed_pattern {As : Set E} {C : Set E}
    (hC : IsHyperplaneCell (coneArrangement As) C)
    (hsub : C ⊆ ⋂ a ∈ As, closedHalfspace a 0) :
    (⋂ a ∈ As, closedHalfspace a 0) ∩ ⋂ a ∈ coneCellZeros As C, {x : E | ⟪a, x⟫ = 0} =
      {x : E | (∀ a ∈ coneCellNegs As C, ⟪a, x⟫ ≤ 0) ∧
        (∀ a ∈ coneCellZeros As C, ⟪a, x⟫ = 0)} := by
  have hdich := coneCell_sign_dichotomy hC hsub
  ext x
  constructor
  · intro hx
    have hxS := hx.1
    have hxZ := hx.2
    refine ⟨?_, ?_⟩
    · intro a haN
      exact (mem_iInter₂.mp hxS a haN.1 : x ∈ closedHalfspace a 0)
    · intro a haZ
      exact (mem_iInter₂.mp hxZ a haZ : ⟪a, x⟫ = 0)
  · intro ⟨hxN, hxZ⟩
    constructor
    · refine mem_iInter₂.mpr fun a haAs => ?_
      have ha' : a ∈ coneCellZeros As C ∪ coneCellNegs As C := by
        rw [← hdich]; exact haAs
      rcases ha' with haZz | haNn
      · exact le_of_eq (hxZ a haZz)
      · exact hxN a haNn
    · exact mem_iInter₂.mpr hxZ

/-- `closure (U ∩ H) = closure U ∩ H` for open orthant `U` and closed flat `H`. -/
lemma closure_inter_closedOrthant_flat {Neg Zero : Set E}
    (hNeg : Neg.Finite)
    (hne : ({x : E | (∀ a ∈ Neg, ⟪a, x⟫ < 0) ∧ (∀ a ∈ Zero, ⟪a, x⟫ = 0)}).Nonempty)
    (hZero : Zero.Finite) :
    closure ({x : E | ∀ a ∈ Neg, ⟪a, x⟫ < 0} ∩ ⋂ a ∈ Zero, {x : E | ⟪a, x⟫ = 0}) =
      closure {x : E | ∀ a ∈ Neg, ⟪a, x⟫ < 0} ∩ ⋂ a ∈ Zero, {x : E | ⟪a, x⟫ = 0} := by
  set U : Set E := {x : E | ∀ a ∈ Neg, ⟪a, x⟫ < 0}
  set H : Set E := ⋂ a ∈ Zero, {x : E | ⟪a, x⟫ = 0}
  apply subset_antisymm
  · exact closure_minimal (fun _x hx => ⟨subset_closure hx.1, hx.2⟩)
      (isClosed_closure.inter (isClosed_iInter_hyperplanes hZero))
  · intro x hx
    have hxU : x ∈ closure U := hx.1
    have hxH : x ∈ H := hx.2
    obtain ⟨z, hzU, hzH⟩ := hne
    have hclU : closure U = {y : E | ∀ a ∈ Neg, ⟪a, y⟫ ≤ 0} :=
      closure_iInter_halfSpace_lt hNeg ⟨z, hzU⟩
    have hxN : ∀ a ∈ Neg, ⟪a, x⟫ ≤ 0 := by
      have : x ∈ closure U := hxU
      rwa [hclU] at this
    refine mem_closure_iff_nhds.2 fun V hV => ?_
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
    let t : ℝ := min (1 / 2) (ε / (2 * (‖z - x‖ + 1)))
    have ht0 : 0 < t := lt_min (by norm_num) (div_pos hε (by positivity))
    have ht1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
    let y : E := (1 - t) • x + t • z
    have hyH : y ∈ H := by
      refine mem_iInter₂.mpr fun a ha => ?_
      change ⟪a, y⟫ = 0
      have hx0 : ⟪a, x⟫ = 0 := mem_iInter₂.mp hxH a ha
      have hz0 : ⟪a, z⟫ = 0 := hzH a ha
      have : ⟪a, y⟫ = (1 - t) * ⟪a, x⟫ + t * ⟪a, z⟫ := by
        simp only [y, inner_add_right, inner_smul_right]
      rw [this, hx0, hz0]; ring
    have hyU : y ∈ U := by
      intro a ha
      have hzA : ⟪a, z⟫ < 0 := hzU a ha
      have hxA : ⟪a, x⟫ ≤ 0 := hxN a ha
      have : ⟪a, y⟫ = (1 - t) * ⟪a, x⟫ + t * ⟪a, z⟫ := by
        simp only [y, inner_add_right, inner_smul_right]
      rw [this]
      have h1 : (1 - t) * ⟪a, x⟫ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht1) hxA
      have h2 : t * ⟪a, z⟫ < 0 := mul_neg_of_pos_of_neg ht0 hzA
      linarith
    have hdist : dist y x < ε := by
      have hdist' : dist y x = t * ‖z - x‖ := by
        simp only [y, dist_eq_norm]
        have : (1 - t) • x + t • z - x = t • (z - x) := by module
        rw [this, norm_smul, Real.norm_of_nonneg ht0.le]
      have hle : t ≤ ε / (2 * (‖z - x‖ + 1)) := min_le_right _ _
      have hden : 0 < ‖z - x‖ + 1 := by positivity
      have hfrac : ε / (2 * (‖z - x‖ + 1)) * ‖z - x‖ ≤ ε / 2 := by
        have hnn : 0 ≤ ‖z - x‖ := norm_nonneg _
        have hε0 : 0 ≤ ε := le_of_lt hε
        field_simp
        nlinarith
      have hmul : t * ‖z - x‖ ≤ ε / 2 := by
        have := mul_le_mul_of_nonneg_right hle (norm_nonneg (z - x))
        linarith
      calc dist y x = t * ‖z - x‖ := hdist'
        _ ≤ ε / 2 := hmul
        _ < ε := by linarith
    exact ⟨y, hball hdist, ⟨hyU, hyH⟩⟩

/-- Closure of a cone-arrangement cell inside the cone equals the supporting-hyperplane face
cut out by the cell's zero normals. Paulson `hyper2` (closure). -/
theorem closure_coneCell_eq_face {As : Set E} (hAs : As.Finite) {C : Set E}
    (hC : IsHyperplaneCell (coneArrangement As) C)
    (hsub : C ⊆ ⋂ a ∈ As, closedHalfspace a 0) :
    closure C =
      (⋂ a ∈ As, closedHalfspace a 0) ∩
        ⋂ a ∈ coneCellZeros As C, {x : E | ⟪a, x⟫ = 0} := by
  set Neg := coneCellNegs As C
  set Zero := coneCellZeros As C
  set U : Set E := {x : E | ∀ a ∈ Neg, ⟪a, x⟫ < 0}
  set H : Set E := ⋂ a ∈ Zero, {x : E | ⟪a, x⟫ = 0}
  have hpat := coneCell_eq_sign_pattern hC hsub
  have hCeq : C = U ∩ H := by
    rw [hpat]
    ext x
    constructor
    · intro ⟨hN, hZ⟩
      exact ⟨hN, mem_iInter₂.mpr hZ⟩
    · intro ⟨hN, hZ⟩
      exact ⟨hN, fun a ha => mem_iInter₂.mp hZ a ha⟩
  have hneAnd : ({x : E | (∀ a ∈ Neg, ⟪a, x⟫ < 0) ∧ (∀ a ∈ Zero, ⟪a, x⟫ = 0)}).Nonempty := by
    obtain ⟨x, hx⟩ := nonempty_isHyperplaneCell hC
    have hx' : x ∈ C := hx
    rw [hpat] at hx'
    exact ⟨x, hx'.1, hx'.2⟩
  have hNegfin : Neg.Finite := hAs.subset (coneCellNegs_subset As C)
  have hZerofin : Zero.Finite := hAs.subset (coneCellZeros_subset As C)
  have hclUH :=
    closure_inter_closedOrthant_flat (Neg := Neg) (Zero := Zero) hNegfin hneAnd hZerofin
  obtain ⟨z0, hz0U, _⟩ := hneAnd
  have hclU : closure U = {x : E | ∀ a ∈ Neg, ⟪a, x⟫ ≤ 0} :=
    closure_iInter_halfSpace_lt hNegfin ⟨z0, hz0U⟩
  have hpatClosed := cone_face_eq_closed_pattern hC hsub
  have hEq : {x : E | ∀ a ∈ Neg, ⟪a, x⟫ ≤ 0} ∩ H =
      {x : E | (∀ a ∈ Neg, ⟪a, x⟫ ≤ 0) ∧ (∀ a ∈ Zero, ⟪a, x⟫ = 0)} := by
    ext x
    constructor
    · intro ⟨hN, hH⟩
      exact ⟨hN, fun a ha => mem_iInter₂.mp hH a ha⟩
    · intro ⟨hN, hZ⟩
      exact ⟨hN, mem_iInter₂.mpr hZ⟩
  calc
    closure C = closure (U ∩ H) := by rw [hCeq]
    _ = closure U ∩ H := hclUH
    _ = {x : E | ∀ a ∈ Neg, ⟪a, x⟫ ≤ 0} ∩ H := by rw [hclU]
    _ = {x : E | (∀ a ∈ Neg, ⟪a, x⟫ ≤ 0) ∧ (∀ a ∈ Zero, ⟪a, x⟫ = 0)} := hEq
    _ = (⋂ a ∈ As, closedHalfspace a 0) ∩ ⋂ a ∈ Zero, {x : E | ⟪a, x⟫ = 0} := by
        simpa [Neg, Zero] using hpatClosed.symm

/-- Paulson `hyper2`: the closure of a cone-arrangement cell inside the cone is a face. -/
theorem isFaceOf_closure_coneCell {As : Set E} (hAs : As.Finite) {C : Set E}
    (hC : IsHyperplaneCell (coneArrangement As) C)
    (hsub : C ⊆ ⋂ a ∈ As, closedHalfspace a 0) :
    IsFaceOf (⋂ a ∈ As, closedHalfspace a 0) (closure C) := by
  rw [closure_coneCell_eq_face hAs hC hsub]
  exact isFaceOf_polyhedralCone_inter_zeros (coneCellZeros_subset As C)
    (hAs.subset (coneCellZeros_subset As C))

/-! ### Face zeros and relative-interior sign constraints (hyper1) -/

/-- Normals that vanish identically on a face. -/
def coneFaceZeros (As : Set E) (F : Set E) : Set E :=
  {a ∈ As | ∀ x ∈ F, ⟪a, x⟫ = 0}

lemma coneFaceZeros_subset (As : Set E) (F : Set E) : coneFaceZeros As F ⊆ As :=
  fun _a ha => ha.1

lemma isClosed_polyhedralCone {As : Set E} (hAs : As.Finite) :
    IsClosed (⋂ a ∈ As, closedHalfspace a 0) := by
  classical
  have hEq : (⋂ a ∈ As, closedHalfspace a 0) =
      ⋂ a ∈ hAs.toFinset, closedHalfspace a 0 := by
    ext x; simp [Finite.mem_toFinset]
  rw [hEq]
  exact isClosed_biInter fun _ _ => isClosed_closedHalfspace _ _

lemma convex_polyhedralCone (As : Set E) :
    Convex ℝ (⋂ a ∈ As, closedHalfspace a 0) :=
  convex_iInter fun a => convex_iInter fun _ => convex_closedHalfspace a 0

/-- Open sign pattern cut out by a face's active (non-vanishing) normals. -/
def coneFaceOpenPattern (As : Set E) (F : Set E) : Set E :=
  {x : E | (∀ a ∈ As \ coneFaceZeros As F, ⟪a, x⟫ < 0) ∧
    (∀ a ∈ coneFaceZeros As F, ⟪a, x⟫ = 0)}

/-- A relative-interior point of a face is strictly negative on every defining normal
that does not vanish on the whole face. -/
lemma coneFace_ri_neg {As : Set E} {F : Set E}
    (hF : IsFaceOf (⋂ a ∈ As, closedHalfspace a 0) F)
    {z : E} (hz : z ∈ intrinsicInterior ℝ F) {a : E} (ha : a ∈ As)
    (hnot : ¬∀ x ∈ F, ⟪a, x⟫ = 0) :
    ⟪a, z⟫ < 0 := by
  have hzF : z ∈ F := intrinsicInterior_subset hz
  have hzS : z ∈ ⋂ b ∈ As, closedHalfspace b 0 := hF.isExtreme.subset hzF
  have hzle : ⟪a, z⟫ ≤ 0 := (mem_iInter₂.mp hzS a ha : z ∈ closedHalfspace a 0)
  refine lt_of_le_of_ne hzle ?_
  intro hz0
  obtain ⟨p, hpF, hpne⟩ : ∃ p ∈ F, ⟪a, p⟫ ≠ 0 := by
    simpa [not_forall] using hnot
  have hplt : ⟪a, p⟫ < 0 := by
    have hpS : p ∈ ⋂ b ∈ As, closedHalfspace b 0 := hF.isExtreme.subset hpF
    have hple : ⟪a, p⟫ ≤ 0 := (mem_iInter₂.mp hpS a ha : p ∈ closedHalfspace a 0)
    exact lt_of_le_of_ne hple hpne
  obtain ⟨z', hz'int, rfl⟩ := (mem_intrinsicInterior (𝕜 := ℝ) (s := F)).1 hz
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz'int)
  have hpSpan : p ∈ (affineSpan ℝ F : Set E) := subset_affineSpan ℝ F hpF
  have hzSpan : (z' : E) ∈ (affineSpan ℝ F : Set E) := Subtype.property z'
  have hnz : (z' : E) - p ≠ 0 := by
    intro heq
    have hzp : (z' : E) = p := sub_eq_zero.mp heq
    have habs : ⟪a, p⟫ = 0 := by
      have : ⟪a, (z' : E)⟫ = ⟪a, p⟫ := by rw [hzp]
      linarith [this, hz0]
    linarith [hplt, habs]
  let t : ℝ := min (1 / 2) (ε / (2 * (‖(z' : E) - p‖ + 1)))
  have ht0 : 0 < t := lt_min (by norm_num) (div_pos hε (by positivity))
  let y : E := (z' : E) + t • ((z' : E) - p)
  have hySpan : y ∈ (affineSpan ℝ F : Set E) := by
    have hyEq : y = AffineMap.lineMap p (z' : E) (1 + t) := by
      simp only [y, AffineMap.lineMap_apply_module]
      module
    rw [hyEq]
    exact AffineMap.lineMap_mem (1 + t) hpSpan hzSpan
  let y' : affineSpan ℝ F := ⟨y, hySpan⟩
  have hdist : dist y' z' < ε := by
    have hdist' : dist y' z' = t * ‖(z' : E) - p‖ := by
      have hdiff : y - (z' : E) = t • ((z' : E) - p) := by
        simp only [y]; module
      calc dist y' z' = dist (y' : E) (z' : E) := Subtype.dist_eq y' z'
        _ = ‖y - (z' : E)‖ := by simp [dist_eq_norm, y']
        _ = ‖t • ((z' : E) - p)‖ := by rw [hdiff]
        _ = t * ‖(z' : E) - p‖ := by rw [norm_smul, Real.norm_of_nonneg ht0.le]
    have hle : t ≤ ε / (2 * (‖(z' : E) - p‖ + 1)) := min_le_right _ _
    have hmul : t * ‖(z' : E) - p‖ ≤ ε / 2 := by
      have h1 := mul_le_mul_of_nonneg_right hle (norm_nonneg ((z' : E) - p))
      have hfrac : ε / (2 * (‖(z' : E) - p‖ + 1)) * ‖(z' : E) - p‖ ≤ ε / 2 := by
        have hnn : 0 ≤ ‖(z' : E) - p‖ := norm_nonneg _
        have hε0 : 0 ≤ ε := le_of_lt hε
        field_simp; nlinarith
      linarith
    calc dist y' z' = t * ‖(z' : E) - p‖ := hdist'
      _ ≤ ε / 2 := hmul
      _ < ε := by linarith
  have hyF : y ∈ F := hball hdist
  have hyS : y ∈ ⋂ b ∈ As, closedHalfspace b 0 := hF.isExtreme.subset hyF
  have hyle : ⟪a, y⟫ ≤ 0 := (mem_iInter₂.mp hyS a ha : y ∈ closedHalfspace a 0)
  have hypos : 0 < ⟪a, y⟫ := by
    have hycalc : ⟪a, y⟫ = t * (-⟪a, p⟫) := by
      simp only [y, inner_add_right, inner_smul_right, inner_sub_right, hz0]
      ring
    rw [hycalc]
    exact mul_pos ht0 (neg_pos.mpr hplt)
  exact not_lt_of_ge hyle hypos

/-- Nonempty faces of a polyhedral cone equal the cone cut by the face's vanishing normals. -/
theorem face_eq_polyhedralCone_inter_zeros {As : Set E} (hAs : As.Finite) {F : Set E}
    (hF : IsFaceOf (⋂ a ∈ As, closedHalfspace a 0) F) (hne : F.Nonempty)
    [FiniteDimensional ℝ E] :
    F = (⋂ a ∈ As, closedHalfspace a 0) ∩
      ⋂ a ∈ coneFaceZeros As F, {x : E | ⟪a, x⟫ = 0} := by
  classical
  set S := ⋂ a ∈ As, closedHalfspace a 0
  set J := coneFaceZeros As F
  apply subset_antisymm
  · intro x hxF
    exact ⟨hF.isExtreme.subset hxF, mem_iInter₂.mpr fun a ha => ha.2 x hxF⟩
  · intro y hy
    have hyS : y ∈ S := hy.1
    have hyJ : ∀ a ∈ J, ⟪a, y⟫ = 0 := fun a ha => mem_iInter₂.mp hy.2 a ha
    obtain ⟨z, hz⟩ := hne.intrinsicInterior hF.convex
    have hzF : z ∈ F := intrinsicInterior_subset hz
    have hzNeg : ∀ a ∈ As, a ∉ J → ⟪a, z⟫ < 0 := by
      intro a ha hnotJ
      have hnot : ¬∀ x ∈ F, ⟪a, x⟫ = 0 := fun hall => hnotJ ⟨ha, hall⟩
      exact coneFace_ri_neg hF hz ha hnot
    -- t > 0 small: w = z + t•(z - y) stays in S
    let ts : Finset ℝ := insert (1 : ℝ) (hAs.toFinset.image fun a =>
      if 0 < ⟪a, z⟫ - ⟪a, y⟫ then
        (-⟪a, z⟫) / (2 * (⟪a, z⟫ - ⟪a, y⟫))
      else
        (1 : ℝ))
    have htsNe : ts.Nonempty := Finset.insert_nonempty _ _
    have hts_pos : ∀ u ∈ ts, 0 < u := by
      intro u hu
      rw [Finset.mem_insert] at hu
      rcases hu with rfl | hu
      · norm_num
      · obtain ⟨a, haAs, rfl⟩ := Finset.mem_image.mp hu
        have ha : a ∈ As := by simpa [Finite.mem_toFinset] using haAs
        split_ifs with hpos
        · have hza : ⟪a, z⟫ < 0 := by
            by_cases hJ : a ∈ J
            · have hz0 : ⟪a, z⟫ = 0 := hJ.2 z hzF
              have hy0 : ⟪a, y⟫ = 0 := hyJ a hJ
              linarith
            · exact hzNeg a ha hJ
          exact div_pos (neg_pos.mpr hza) (mul_pos (by norm_num) hpos)
        · norm_num
    let t : ℝ := min (1 / 2) (ts.min' htsNe)
    have ht0 : 0 < t := lt_min (by norm_num) (hts_pos _ (Finset.min'_mem _ htsNe))
    have ht_le : ∀ a ∈ As, 0 < ⟪a, z⟫ - ⟪a, y⟫ →
        t ≤ (-⟪a, z⟫) / (2 * (⟪a, z⟫ - ⟪a, y⟫)) := by
      intro a ha hpos
      have haF : a ∈ hAs.toFinset := by simpa [Finite.mem_toFinset] using ha
      have hmem : (-⟪a, z⟫) / (2 * (⟪a, z⟫ - ⟪a, y⟫)) ∈ ts := by
        refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a, haF, ?_⟩)
        simp [hpos]
      have hmin : ts.min' htsNe ≤ (-⟪a, z⟫) / (2 * (⟪a, z⟫ - ⟪a, y⟫)) :=
        Finset.min'_le _ _ hmem
      exact (min_le_right _ _).trans hmin
    let w : E := z + t • (z - y)
    have hwS : w ∈ S := by
      refine mem_iInter₂.mpr fun a ha => ?_
      change ⟪a, w⟫ ≤ 0
      have hwcalc : ⟪a, w⟫ = ⟪a, z⟫ + t * (⟪a, z⟫ - ⟪a, y⟫) := by
        calc ⟪a, w⟫ = ⟪a, z + t • (z - y)⟫ := rfl
          _ = ⟪a, z⟫ + ⟪a, t • (z - y)⟫ := inner_add_right _ _ _
          _ = ⟪a, z⟫ + t * ⟪a, z - y⟫ := by rw [inner_smul_right]
          _ = ⟪a, z⟫ + t * (⟪a, z⟫ - ⟪a, y⟫) := by rw [inner_sub_right]
      rw [hwcalc]
      by_cases hJ : a ∈ J
      · have hz0 : ⟪a, z⟫ = 0 := hJ.2 z hzF
        have hy0 : ⟪a, y⟫ = 0 := hyJ a hJ
        simp [hz0, hy0]
      · have hzlt : ⟪a, z⟫ < 0 := hzNeg a ha hJ
        have hyle : ⟪a, y⟫ ≤ 0 := (mem_iInter₂.mp hyS a ha : y ∈ closedHalfspace a 0)
        by_cases hpos : 0 < ⟪a, z⟫ - ⟪a, y⟫
        · have hle := ht_le a ha hpos
          have hden : 0 < ⟪a, z⟫ - ⟪a, y⟫ := hpos
          have hnum : 0 < -⟪a, z⟫ := neg_pos.mpr hzlt
          -- α + t(α-β) ≤ α + ((-α)/(2(α-β))) * (α-β) = α - α/2 = α/2 < 0
          have htbound : t * (⟪a, z⟫ - ⟪a, y⟫) ≤ (-⟪a, z⟫) / 2 := by
            have := mul_le_mul_of_nonneg_right hle hden.le
            have hsimp : (-⟪a, z⟫) / (2 * (⟪a, z⟫ - ⟪a, y⟫)) * (⟪a, z⟫ - ⟪a, y⟫) =
                (-⟪a, z⟫) / 2 := by
              have hne : (⟪a, z⟫ - ⟪a, y⟫) ≠ 0 := ne_of_gt hden
              field_simp [hne]
            linarith
          linarith
        · -- α - β ≤ 0 ⇒ t(α-β) ≤ 0 ⇒ α + t(α-β) ≤ α < 0
          have : ⟪a, z⟫ - ⟪a, y⟫ ≤ 0 := le_of_not_gt hpos
          nlinarith
    have hzSeg : z ∈ openSegment ℝ y w := by
      have hwEq : w = AffineMap.lineMap y z (1 + t) := by
        simp only [w, AffineMap.lineMap_apply_module]
        module
      have hden : (1 + t : ℝ) ≠ 0 := by linarith
      have hzEq : AffineMap.lineMap y w (1 / (1 + t)) = z := by
        have hcomp :
            AffineMap.lineMap y w (1 / (1 + t)) =
              AffineMap.lineMap y z ((1 + t) * (1 / (1 + t))) := by
          simp only [hwEq, AffineMap.lineMap_apply_module]
          module
        have hmul : (1 + t) * (1 / (1 + t) : ℝ) = 1 := by field_simp [hden]
        rw [hcomp, hmul, AffineMap.lineMap_apply_one]
      rw [← hzEq]
      exact lineMap_mem_openSegment (𝕜 := ℝ) y w (t := 1 / (1 + t))
        ⟨div_pos one_pos (by linarith), by rw [div_lt_one (by linarith)]; linarith⟩
    exact hF.isExtreme.left_mem_of_mem_openSegment hyS hwS hzF hzSeg


lemma coneFaceOpenPattern_subset_face {As : Set E} (hAs : As.Finite) {F : Set E}
    (hF : IsFaceOf (⋂ a ∈ As, closedHalfspace a 0) F) (hne : F.Nonempty)
    [FiniteDimensional ℝ E] :
    coneFaceOpenPattern As F ⊆ F := by
  intro x hx
  have hEq := face_eq_polyhedralCone_inter_zeros hAs hF hne
  rw [hEq]
  constructor
  · refine mem_iInter₂.mpr fun a ha => ?_
    by_cases hJ : a ∈ coneFaceZeros As F
    · exact le_of_eq (hx.2 a hJ)
    · exact le_of_lt (hx.1 a ⟨ha, hJ⟩)
  · exact mem_iInter₂.mpr hx.2

lemma intrinsicInterior_subset_coneFaceOpenPattern {As : Set E} {F : Set E}
    (hF : IsFaceOf (⋂ a ∈ As, closedHalfspace a 0) F) :
    intrinsicInterior ℝ F ⊆ coneFaceOpenPattern As F := by
  intro z hz
  refine ⟨?_, ?_⟩
  · intro a ha
    exact coneFace_ri_neg hF hz ha.1 (fun hall => ha.2 ⟨ha.1, hall⟩)
  · intro a ha
    exact ha.2 z (intrinsicInterior_subset hz)

lemma coneFaceOpenPattern_nonempty {As : Set E} {F : Set E}
    (hF : IsFaceOf (⋂ a ∈ As, closedHalfspace a 0) F) (hne : F.Nonempty)
    [FiniteDimensional ℝ E] :
    (coneFaceOpenPattern As F).Nonempty :=
  (hne.intrinsicInterior hF.convex).mono
    (intrinsicInterior_subset_coneFaceOpenPattern hF)


lemma isOpen_coneFaceNegs {As F : Set E} (hAs : As.Finite) :
    IsOpen {x : E | ∀ a ∈ As \ coneFaceZeros As F, ⟪a, x⟫ < 0} := by
  classical
  have hNeg : (As \ coneFaceZeros As F).Finite := hAs.subset sdiff_subset
  have hEq : {x : E | ∀ a ∈ As \ coneFaceZeros As F, ⟪a, x⟫ < 0} =
      ⋂ a ∈ hNeg.toFinset, {x : E | ⟪a, x⟫ < 0} := by
    ext x; simp [Finite.mem_toFinset]
  rw [hEq]
  exact isOpen_biInter_finset fun _ _ => isOpen_halfSpace_lt _ 0

/-- The open sign pattern of a nonempty face is a cone-arrangement cell. -/
theorem isHyperplaneCell_coneFaceOpenPattern {As : Set E} (_hAs : As.Finite) {F : Set E}
    (hF : IsFaceOf (⋂ a ∈ As, closedHalfspace a 0) F) (hne : F.Nonempty)
    [FiniteDimensional ℝ E] :
    IsHyperplaneCell (coneArrangement As) (coneFaceOpenPattern As F) := by
  obtain ⟨z, hz⟩ := coneFaceOpenPattern_nonempty hF hne
  refine ⟨z, ?_⟩
  ext y
  constructor
  · intro hy h hh
    obtain ⟨a, ha, rfl⟩ := hh
    by_cases hJ : a ∈ coneFaceZeros As F
    · have hzside : hyperplaneSide (a, (0 : ℝ)) z = 0 :=
        (hyperplaneSide_eq_zero_iff a 0 z).mpr (hz.2 a hJ)
      have hyside : hyperplaneSide (a, (0 : ℝ)) y = 0 :=
        (hyperplaneSide_eq_zero_iff a 0 y).mpr (hy.2 a hJ)
      exact hzside.trans hyside.symm
    · have haN : a ∈ As \ coneFaceZeros As F := ⟨ha, hJ⟩
      have hzside : hyperplaneSide (a, (0 : ℝ)) z = -1 :=
        (hyperplaneSide_eq_neg_one_iff a 0 z).mpr (hz.1 a haN)
      have hyside : hyperplaneSide (a, (0 : ℝ)) y = -1 :=
        (hyperplaneSide_eq_neg_one_iff a 0 y).mpr (hy.1 a haN)
      exact hzside.trans hyside.symm
  · intro hy
    constructor
    · intro a ha
      have hside : hyperplaneSide (a, (0 : ℝ)) z = hyperplaneSide (a, (0 : ℝ)) y :=
        hy (a, (0 : ℝ)) ⟨a, ha.1, rfl⟩
      have hzside : hyperplaneSide (a, (0 : ℝ)) z = -1 :=
        (hyperplaneSide_eq_neg_one_iff a 0 z).mpr (hz.1 a ha)
      exact (hyperplaneSide_eq_neg_one_iff a 0 y).mp (hside ▸ hzside)
    · intro a ha
      have hside : hyperplaneSide (a, (0 : ℝ)) z = hyperplaneSide (a, (0 : ℝ)) y :=
        hy (a, (0 : ℝ)) ⟨a, ha.1, rfl⟩
      have hzside : hyperplaneSide (a, (0 : ℝ)) z = 0 :=
        (hyperplaneSide_eq_zero_iff a 0 z).mpr (hz.2 a ha)
      exact (hyperplaneSide_eq_zero_iff a 0 y).mp (hside ▸ hzside)

lemma coneCellZeros_coneFaceOpenPattern {As : Set E} (_hAs : As.Finite) {F : Set E}
    (hF : IsFaceOf (⋂ a ∈ As, closedHalfspace a 0) F) (hne : F.Nonempty)
    [FiniteDimensional ℝ E] :
    coneCellZeros As (coneFaceOpenPattern As F) = coneFaceZeros As F := by
  ext a
  constructor
  · intro ⟨ha, hvan⟩
    refine ⟨ha, ?_⟩
    by_contra hnot
    have hnotJ : a ∉ coneFaceZeros As F := fun hJ => hnot hJ.2
    have haN : a ∈ As \ coneFaceZeros As F := ⟨ha, hnotJ⟩
    obtain ⟨z, hz⟩ := coneFaceOpenPattern_nonempty hF hne
    have hlt : ⟪a, z⟫ < 0 := hz.1 a haN
    have heq : ⟪a, z⟫ = 0 := hvan z hz
    linarith
  · intro ⟨ha, hvan⟩
    exact ⟨ha, fun x hx => hx.2 a ⟨ha, hvan⟩⟩

/-- Closure of the open sign-pattern cell recovers the face (hyper1 closure). -/
theorem closure_coneFaceOpenPattern {As : Set E} (hAs : As.Finite) {F : Set E}
    (hF : IsFaceOf (⋂ a ∈ As, closedHalfspace a 0) F) (hne : F.Nonempty)
    [FiniteDimensional ℝ E] :
    closure (coneFaceOpenPattern As F) = F := by
  have hcell := isHyperplaneCell_coneFaceOpenPattern hAs hF hne
  have hsub : coneFaceOpenPattern As F ⊆ ⋂ a ∈ As, closedHalfspace a 0 :=
    (coneFaceOpenPattern_subset_face hAs hF hne).trans hF.isExtreme.subset
  have hcl := closure_coneCell_eq_face hAs hcell hsub
  rw [hcl, coneCellZeros_coneFaceOpenPattern hAs hF hne,
    ← face_eq_polyhedralCone_inter_zeros hAs hF hne]

lemma affineSpan_closure [FiniteDimensional ℝ E] (s : Set E) :
    affineSpan ℝ (closure s) = affineSpan ℝ s := by
  refine le_antisymm ?_ (affineSpan_mono ℝ subset_closure)
  have hsub : closure s ⊆ (affineSpan ℝ s : Set E) :=
    closure_minimal (subset_affineSpan ℝ s)
      (AffineSubspace.closed_of_finiteDimensional (affineSpan ℝ s))
  exact affineSpan_le.2 hsub

/-- Relative interior of a nonempty face equals its open sign-pattern cell. -/
theorem intrinsicInterior_face_eq_coneFaceOpenPattern {As : Set E} (hAs : As.Finite)
    {F : Set E} (hF : IsFaceOf (⋂ a ∈ As, closedHalfspace a 0) F) (hne : F.Nonempty)
    [FiniteDimensional ℝ E] :
    intrinsicInterior ℝ F = coneFaceOpenPattern As F := by
  apply subset_antisymm
  · exact intrinsicInterior_subset_coneFaceOpenPattern hF
  · intro x hx
    set P := coneFaceOpenPattern As F
    have hcell : IsHyperplaneCell (coneArrangement As) P :=
      isHyperplaneCell_coneFaceOpenPattern hAs hF hne
    have hAfin : (coneArrangement As).Finite := coneArrangement_finite hAs
    obtain ⟨U, hU, hPeq⟩ := isHyperplaneCell_isOpen_affineSpan hAfin hcell
    have hspan : affineSpan ℝ P = affineSpan ℝ F := by
      rw [← closure_coneFaceOpenPattern hAs hF hne, affineSpan_closure]
    have hPeq' : P = U ∩ (affineSpan ℝ F : Set E) := by
      rw [← hspan]; exact hPeq
    have hxU : x ∈ U := by
      have : x ∈ U ∩ (affineSpan ℝ F : Set E) := by rwa [← hPeq']
      exact this.1
    have hxAff : x ∈ (affineSpan ℝ F : Set E) := by
      have : x ∈ U ∩ (affineSpan ℝ F : Set E) := by rwa [← hPeq']
      exact this.2
    refine (mem_intrinsicInterior (𝕜 := ℝ) (s := F)).2 ⟨⟨x, hxAff⟩, ?_, rfl⟩
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
    refine ⟨ε, hε, ?_⟩
    intro y hy
    have hyU : (y : E) ∈ U := hball (by
      change dist (y : E) x < ε
      simpa [Subtype.dist_eq] using hy)
    have hyAff : (y : E) ∈ (affineSpan ℝ F : Set E) := Subtype.property y
    have hyP : (y : E) ∈ P := by
      rw [hPeq']
      exact ⟨hyU, hyAff⟩
    exact coneFaceOpenPattern_subset_face hAs hF hne hyP

/-- Paulson `hyper1`: RI of a nonempty face is a cone-arrangement cell inside the cone,
with the same affine dimension, and its closure recovers the face. -/
theorem hyper1_polyhedral_cone {As : Set E} (hAs : As.Finite) {F : Set E}
    (hF : IsFaceOf (⋂ a ∈ As, closedHalfspace a 0) F) (hne : F.Nonempty)
    [FiniteDimensional ℝ E] :
    IsHyperplaneCell (coneArrangement As) (intrinsicInterior ℝ F) ∧
      intrinsicInterior ℝ F ⊆ ⋂ a ∈ As, closedHalfspace a 0 ∧
      affDim (intrinsicInterior ℝ F) = affDim F ∧
      closure (intrinsicInterior ℝ F) = F := by
  have hRI := intrinsicInterior_face_eq_coneFaceOpenPattern hAs hF hne
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hRI]; exact isHyperplaneCell_coneFaceOpenPattern hAs hF hne
  · exact intrinsicInterior_subset.trans hF.isExtreme.subset
  · set P := coneFaceOpenPattern As F
    have hcl : closure P = F := closure_coneFaceOpenPattern hAs hF hne
    have hspan : affineSpan ℝ (intrinsicInterior ℝ F) = affineSpan ℝ F := by
      rw [hRI, ← hcl, affineSpan_closure]
    exact affDim_eq_of_affineSpan_eq hspan
  · rw [hRI, closure_coneFaceOpenPattern hAs hF hne]



lemma coneFaceZeros_closure_coneCell {As : Set E} {C : Set E}
    (_hC : IsHyperplaneCell (coneArrangement As) C)
    (_hsub : C ⊆ ⋂ a ∈ As, closedHalfspace a 0) :
    coneFaceZeros As (closure C) = coneCellZeros As C := by
  ext a
  constructor
  · intro ⟨ha, hvan⟩
    exact ⟨ha, fun x hx => hvan x (subset_closure hx)⟩
  · intro ⟨ha, hvan⟩
    refine ⟨ha, fun x hx => ?_⟩
    have hcont : Continuous fun y : E => ⟪a, y⟫ := continuous_const.inner continuous_id
    exact closure_minimal (s := C) (t := {y | ⟪a, y⟫ = 0}) hvan
      (isClosed_eq hcont continuous_const) hx

lemma coneFaceOpenPattern_closure_coneCell {As : Set E} (_hAs : As.Finite) {C : Set E}
    (hC : IsHyperplaneCell (coneArrangement As) C)
    (hsub : C ⊆ ⋂ a ∈ As, closedHalfspace a 0) :
    coneFaceOpenPattern As (closure C) = C := by
  have hzeros := coneFaceZeros_closure_coneCell hC hsub
  have hdich := coneCell_sign_dichotomy hC hsub
  have hpat := coneCell_eq_sign_pattern hC hsub
  have hNeg : As \ coneFaceZeros As (closure C) = coneCellNegs As C := by
    rw [hzeros]
    ext a
    constructor
    · intro ⟨ha, hnotZ⟩
      have : a ∈ coneCellZeros As C ∪ coneCellNegs As C := by rw [← hdich]; exact ha
      rcases this with hZ | hN
      · exact (hnotZ hZ).elim
      · exact hN
    · intro hN
      refine ⟨hN.1, fun hZ =>
        (coneCellZeros_disjoint_negs (nonempty_isHyperplaneCell hC)).le_bot ⟨hZ, hN⟩⟩
  have hNeg' : As \ coneCellZeros As C = coneCellNegs As C := by
    rwa [← hzeros]
  rw [coneFaceOpenPattern, hzeros, hNeg', ← hpat]

/-- Paulson hyper2 RI recovery: RI of the closure of a cone cell is the cell. -/
theorem intrinsicInterior_closure_coneCell {As : Set E} (hAs : As.Finite) {C : Set E}
    (hC : IsHyperplaneCell (coneArrangement As) C)
    (hsub : C ⊆ ⋂ a ∈ As, closedHalfspace a 0)
    [FiniteDimensional ℝ E] :
    intrinsicInterior ℝ (closure C) = C := by
  have hF := isFaceOf_closure_coneCell hAs hC hsub
  have hne : (closure C).Nonempty :=
    (nonempty_isHyperplaneCell hC).mono subset_closure
  rw [intrinsicInterior_face_eq_coneFaceOpenPattern hAs hF hne,
    coneFaceOpenPattern_closure_coneCell hAs hC hsub]



lemma ncard_faces_eq_ncard_cells {As : Set E} (hAs : As.Finite)
    [FiniteDimensional ℝ E] (d : ℤ) :
    {F : Set E | IsFaceOf (⋂ a ∈ As, closedHalfspace a 0) F ∧
        F.Nonempty ∧ affDim F = d}.ncard =
      {C : Set E | IsHyperplaneCell (coneArrangement As) C ∧
        C ⊆ (⋂ a ∈ As, closedHalfspace a 0) ∧ affDim C = d}.ncard := by
  classical
  set S := ⋂ a ∈ As, closedHalfspace a 0
  set A := coneArrangement As
  have hAfin : A.Finite := coneArrangement_finite hAs
  set faces : Set (Set E) := {F | IsFaceOf S F ∧ F.Nonempty ∧ affDim F = d}
  set cells : Set (Set E) := {C | IsHyperplaneCell A C ∧ C ⊆ S ∧ affDim C = d}
  have hfinCells : cells.Finite :=
    (finite_isHyperplaneCell_restrict hAfin (fun C => C ⊆ S)).subset
      fun _C h => ⟨h.1, h.2.1⟩
  have himage : intrinsicInterior ℝ '' faces = cells := by
    apply subset_antisymm
    · rintro _ ⟨F, ⟨hFace, hne, hdim⟩, rfl⟩
      have h1 := hyper1_polyhedral_cone hAs hFace hne
      exact ⟨h1.1, h1.2.1, by rw [h1.2.2.1, hdim]⟩
    · intro C ⟨hC, hsub, hdim⟩
      refine ⟨closure C, ⟨?_, ?_, ?_⟩, ?_⟩
      · exact isFaceOf_closure_coneCell hAs hC hsub
      · exact (nonempty_isHyperplaneCell hC).mono subset_closure
      · have : affDim (closure C) = affDim C :=
          affDim_eq_of_affineSpan_eq (affineSpan_closure (E := E) C)
        rw [this, hdim]
      · exact intrinsicInterior_closure_coneCell hAs hC hsub
  have hinj : InjOn (intrinsicInterior ℝ) faces := by
    intro F₁ hF₁ F₂ hF₂ heq
    have h1 := (hyper1_polyhedral_cone hAs hF₁.1 hF₁.2.1).2.2.2
    have h2 := (hyper1_polyhedral_cone hAs hF₂.1 hF₂.2.1).2.2.2
    calc F₁ = closure (intrinsicInterior ℝ F₁) := h1.symm
      _ = closure (intrinsicInterior ℝ F₂) := by rw [heq]
      _ = F₂ := h2
  have hfinFaces : faces.Finite := by
    rwa [← finite_image_iff hinj, himage]
  exact (hinj.ncard_image).symm.trans (by rw [himage])

lemma affDim_toNat_lt_finrank_succ [FiniteDimensional ℝ E]
    {C : Set E} (hne : C.Nonempty) :
    (affDim C).toNat < Module.finrank ℝ E + 1 := by
  have hnn : 0 ≤ affDim C := affDim_nonneg_of_nonempty hne
  have hle : affDim C ≤ Module.finrank ℝ E := by
    cases hfd : (affineSpan ℝ C).finDim with
    | bot =>
      have : affDim C = -1 := by simp [affDim, hfd]
      rw [this] at hnn; omega
    | coe m =>
      have hm : affDim C = (m : ℤ) := by simp [affDim, hfd]
      rw [hm]
      by_cases hbot : affineSpan ℝ C = ⊥
      · simp [hbot, AffineSubspace.finDim_bot] at hfd
      · have hEq := finDim_eq_finrank (R := ℝ) (s := affineSpan ℝ C) hbot
        -- hEq : finDim = ↑(finrank direction); hfd : finDim = ↑m
        have hm' : m = Module.finrank ℝ (affineSpan ℝ C).direction := by
          have : (m : WithBot ℕ) = (Module.finrank ℝ (affineSpan ℝ C).direction : WithBot ℕ) := by
            rwa [hfd] at hEq
          exact WithBot.coe_eq_coe.mp this
        have hle := Submodule.finrank_le (affineSpan ℝ C).direction
        exact Nat.cast_le.mpr (by omega)
  have : (affDim C).toNat ≤ Module.finrank ℝ E := by omega
  exact Nat.lt_succ_of_le this

/-- Combinatorial face Euler sum equals the cell-complex Euler characteristic. -/
theorem faceEulerSum_eq_eulerCharacteristic {As : Set E} (hAs : As.Finite)
    [FiniteDimensional ℝ E] [Nonempty E] :
    faceEulerSum (⋂ a ∈ As, closedHalfspace a 0) (Module.finrank ℝ E) =
      eulerCharacteristic (coneArrangement As) (⋂ a ∈ As, closedHalfspace a 0) := by
  classical
  set S := ⋂ a ∈ As, closedHalfspace a 0
  set A := coneArrangement As
  set n := Module.finrank ℝ E
  have hAfin : A.Finite := coneArrangement_finite hAs
  set cellsFin := (finite_isHyperplaneCell_restrict hAfin (fun C => C ⊆ S)).toFinset
  have hLHS :
      faceEulerSum S n =
        ∑ d ∈ Finset.range (n + 1),
          (-1 : ℤ) ^ d *
            ({C : Set E | IsHyperplaneCell A C ∧ C ⊆ S ∧ affDim C = (d : ℤ)}.ncard : ℤ) := by
    unfold faceEulerSum
    refine Finset.sum_congr rfl fun d _ => ?_
    have hEq :
        {F : Set E | IsFaceOf S F ∧ affDim F = (d : ℤ)} =
          {F : Set E | IsFaceOf S F ∧ F.Nonempty ∧ affDim F = (d : ℤ)} := by
      ext F; constructor
      · intro ⟨hF, hdim⟩
        refine ⟨hF, ?_, hdim⟩
        by_contra hempty
        simp [not_nonempty_iff_eq_empty.mp hempty, affDim_empty] at hdim
      · exact fun ⟨hF, _, hdim⟩ => ⟨hF, hdim⟩
    rw [hEq, ncard_faces_eq_ncard_cells (As := As) hAs]
  have hRHS :
      eulerCharacteristic A S =
        ∑ d ∈ Finset.range (n + 1),
          (-1 : ℤ) ^ d *
            ({C : Set E | IsHyperplaneCell A C ∧ C ⊆ S ∧ affDim C = (d : ℤ)}.ncard : ℤ) := by
    rw [eulerCharacteristic_eq_sum hAfin]
    have hmaps : ∀ C ∈ cellsFin, (affDim C).toNat ∈ Finset.range (n + 1) := by
      intro C hC
      have ⟨hcell, _⟩ : IsHyperplaneCell A C ∧ C ⊆ S := by
        simpa [cellsFin, Finite.mem_toFinset] using hC
      exact Finset.mem_range.mpr
        (affDim_toNat_lt_finrank_succ (nonempty_isHyperplaneCell hcell))
    have hfiber := (Finset.sum_fiberwise_of_maps_to hmaps cellSign).symm
    refine hfiber.trans ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    have hsign : ∀ C ∈ cellsFin.filter (fun C => (affDim C).toNat = d),
        cellSign C = (-1 : ℤ) ^ d := by
      intro C hC
      have ⟨hC0, hf⟩ := Finset.mem_filter.mp hC
      have ⟨hcell, _⟩ : IsHyperplaneCell A C ∧ C ⊆ S := by
        simpa [cellsFin, Finite.mem_toFinset] using hC0
      have hnn := affDim_nonneg_of_nonempty (nonempty_isHyperplaneCell hcell)
      unfold cellSign
      have hdim : affDim C = (d : ℤ) := by rw [← Int.toNat_of_nonneg hnn, hf]
      rw [hdim]; simp
    rw [Finset.sum_congr rfl hsign, Finset.sum_const, nsmul_eq_mul, mul_comm]
    congr 1
    have hfin :
        {C : Set E | IsHyperplaneCell A C ∧ C ⊆ S ∧ affDim C = (d : ℤ)}.Finite :=
      (finite_isHyperplaneCell_restrict hAfin (fun C => C ⊆ S)).subset
        fun _ h => ⟨h.1, h.2.1⟩
    have hEq :
        cellsFin.filter (fun C => (affDim C).toNat = d) = hfin.toFinset := by
      ext C
      simp only [Finset.mem_filter, cellsFin, Finite.mem_toFinset, mem_ofPred_eq]
      constructor
      · intro ⟨⟨hC, hsub⟩, hf⟩
        have hnn := affDim_nonneg_of_nonempty (nonempty_isHyperplaneCell hC)
        refine ⟨hC, hsub, ?_⟩
        rw [← Int.toNat_of_nonneg hnn, hf]
      · intro ⟨hC, hsub, hdim⟩
        refine ⟨⟨hC, hsub⟩, ?_⟩
        simp [hdim]
    rw [hEq]
    exact congrArg Nat.cast (Set.ncard_eq_toFinset_card _ hfin).symm
  exact hLHS.trans hRHS.symm

/-- Combinatorial face Euler sum of a proper full-dimensional polyhedral cone is `0`.
Paulson `Euler_polyhedral_cone`. -/
theorem faceEulerSum_polyhedral_cone [FiniteDimensional ℝ E] [Nonempty E]
    {As : Set E} (hAs : As.Finite) (hneAs : As.Nonempty)
    (hpos : ({x : E | ∀ a ∈ As, 0 < ⟪a, x⟫}).Nonempty) :
    faceEulerSum (⋂ a ∈ As, closedHalfspace a 0) (Module.finrank ℝ E) = 0 := by
  rw [faceEulerSum_eq_eulerCharacteristic hAs,
    eulerCharacteristic_polyhedral_cone hAs hneAs hpos]

end EulersGem

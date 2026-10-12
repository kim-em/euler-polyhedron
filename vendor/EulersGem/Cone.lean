/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.EulerChar
import EulersGem.Polytope
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Combinatorics.Enumerative.InclusionExclusion

/-!
# Conical cell structure toward Euler–Poincaré (Paulson)

Port of the cone step of AFP `Euler_Formula`:

* polyhedral cones as cell complexes of their supporting arrangement
  (see `EulersGem.Polytope`)
* Euler characteristic of `univ` equals `(-1)^{finrank}`
* soft inclusion-exclusion identity `EC(S ∪ T) = EC(S)+EC(T)-EC(S ∩ T)`
* **proved:** cell-complex Euler char of a single nontrivial halfspace cone is `0`
* **proved (halfspace):** face ↔ cell bijection and `faceEulerSum = 0`
  (see `EulersGem.FaceCell`)
* **proved:** two-halfspace polyhedral cone cell EC = 0 (soft IE)
* **proved:** indexed inclusion-exclusion + general polyhedral-cone cell EC = 0
* **proved (hyper2):** cell ⊆ cone ⇒ closure is a face (`ConeFaceCell`)
* **proved (hyper1):** every nonempty face = closure of its RI-cell; `faceEulerSum = 0`
* face-lattice substrate in `Polytope` (`isFaceOf_trans/inter/of_isExposed`,
  supporting-hyperplane faces, cone-arrangement cell characterisation)
* targets stated as docs (not Results): `Euler_Poincare_full`, 3D `V−E+F=2`

Next for Euler–Poincaré: lift cone faceEulerSum to full-dimensional polytopes.
-/

open scoped RealInnerProductSpace BigOperators
open Classical Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace EulersGem

/-! ### Euler char of the ambient space -/

/-- For any finite arrangement, `eulerCharacteristic A univ = (-1)^{finrank}`. -/
lemma eulerCharacteristic_univ [FiniteDimensional ℝ E] [Nonempty E]
    {A : Set (Hyperplane E)} (hA : A.Finite) :
    eulerCharacteristic A (univ : Set E) = (-1 : ℤ) ^ Module.finrank ℝ E := by
  have hEmpty : (∅ : Set (Hyperplane E)).Finite := finite_empty
  have hAuniv : IsHyperplaneCellComplex A (univ : Set E) :=
    isHyperplaneCellComplex_univ A
  have hEuniv : IsHyperplaneCellComplex (∅ : Set (Hyperplane E)) (univ : Set E) :=
    isHyperplaneCellComplex_univ _
  have hInv := eulerCharacteristic_invariant hA hEmpty hAuniv hEuniv
  rw [hInv, eulerCharacteristic_empty_arrangement_univ]

/-! ### Soft inclusion-exclusion -/

/-- Soft inclusion-exclusion from disjoint additivity:
`EC(S ∪ T) = EC(S) + EC(T) - EC(S ∩ T)`. -/
lemma eulerCharacteristic_union_inter {A : Set (Hyperplane E)} {S T : Set E}
    (hA : A.Finite)
    (hS : IsHyperplaneCellComplex A S) (hT : IsHyperplaneCellComplex A T) :
    eulerCharacteristic A (S ∪ T) =
      eulerCharacteristic A S + eulerCharacteristic A T -
        eulerCharacteristic A (S ∩ T) := by
  have hDiff : IsHyperplaneCellComplex A (T \ S) :=
    isHyperplaneCellComplex_diff hT hS
  have hInter : IsHyperplaneCellComplex A (S ∩ T) :=
    isHyperplaneCellComplex_inter hS hT
  have hdisj₁ : Disjoint S (T \ S) := disjoint_sdiff_right
  have hdisj₂ : Disjoint (S ∩ T) (T \ S) :=
    disjoint_left.mpr fun _x hx hx' => hx'.2 hx.1
  have hEq1 : S ∪ T = S ∪ (T \ S) := by
    ext x; by_cases hxS : x ∈ S <;> simp [hxS]
  have hEq2 : T = (S ∩ T) ∪ (T \ S) := by
    ext x; by_cases hxS : x ∈ S <;> simp [hxS]
  have h1 :=
    (eulerCharacteristic_cellcomplex_union hA hS hDiff hdisj₁).symm.trans
      (congrArg (eulerCharacteristic A) hEq1.symm)
  -- h1 : EC(S) + EC(T\S) = EC(S ∪ T)
  have h2 :=
    (eulerCharacteristic_cellcomplex_union hA hInter hDiff hdisj₂).symm.trans
      (congrArg (eulerCharacteristic A) hEq2.symm)
  -- h2 : EC(S∩T) + EC(T\S) = EC(T)
  have h1' : eulerCharacteristic A (S ∪ T) =
      eulerCharacteristic A S + eulerCharacteristic A (T \ S) := h1.symm
  have h2' : eulerCharacteristic A T =
      eulerCharacteristic A (S ∩ T) + eulerCharacteristic A (T \ S) := h2.symm
  linarith

/-! ### Halfspace cone: cell Euler char = 0 -/

lemma compl_closedHalfspace_zero (a : E) :
    (closedHalfspace a 0)ᶜ = {x : E | 0 < ⟪a, x⟫} := by
  ext x
  change ¬⟪a, x⟫ ≤ 0 ↔ 0 < ⟪a, x⟫
  constructor <;> intro h <;> linarith

lemma affDim_openHalfspace_gt [FiniteDimensional ℝ E] [Nonempty E]
    {a : E} (ha : a ≠ 0) :
    affDim {x : E | 0 < ⟪a, x⟫} = Module.finrank ℝ E := by
  have hne : (univ ∩ {x : E | (0 : ℝ) < ⟪a, x⟫}).Nonempty :=
    ⟨a, mem_univ a, real_inner_self_pos.mpr ha⟩
  have h := affDim_cell_inter_halfSpace_gt
    (A := (∅ : Set (Hyperplane E))) (C := (univ : Set E))
    finite_empty ((isHyperplaneCell_empty_arrangement univ).mpr rfl) a 0 hne
  have hEq : (univ : Set E) ∩ {x | (0 : ℝ) < ⟪a, x⟫} = {x | 0 < ⟪a, x⟫} := by
    ext; simp
  rw [← hEq, h, affDim_univ]

/-- Cell-complex Euler characteristic of a nontrivial closed halfspace cone is `0`.
Special case of the cone step toward Paulson `Euler_polyhedral_cone`. -/
theorem eulerCharacteristic_halfspace_cone [FiniteDimensional ℝ E] [Nonempty E]
    {a : E} (ha : a ≠ 0) :
    eulerCharacteristic {(a, (0 : ℝ))} (closedHalfspace a 0) = 0 := by
  have hA : ({(a, (0 : ℝ))} : Set (Hyperplane E)).Finite := finite_singleton _
  have hS : IsHyperplaneCellComplex {(a, (0 : ℝ))} (closedHalfspace a 0) :=
    isHyperplaneCellComplex_closedHalfspace_zero a
  have hComplCx : IsHyperplaneCellComplex {(a, (0 : ℝ))} (closedHalfspace a 0)ᶜ :=
    isHyperplaneCellComplex_compl hS
  have hUniv := eulerCharacteristic_univ (A := {(a, (0 : ℝ))}) hA
  have hdisj : Disjoint (closedHalfspace a 0) (closedHalfspace a 0)ᶜ :=
    disjoint_compl_right
  have hUnion : closedHalfspace a 0 ∪ (closedHalfspace a 0)ᶜ = univ :=
    union_compl_self _
  have hAdd :=
    eulerCharacteristic_cellcomplex_union hA hS hComplCx hdisj
  rw [hUnion, hUniv] at hAdd
  have hComplCell : IsHyperplaneCell {(a, (0 : ℝ))} (closedHalfspace a 0)ᶜ := by
    rw [compl_closedHalfspace_zero]
    exact isHyperplaneCell_eq_halfSpace_gt ha
  have hECcompl :
      eulerCharacteristic {(a, (0 : ℝ))} (closedHalfspace a 0)ᶜ =
        (-1 : ℤ) ^ Module.finrank ℝ E := by
    rw [eulerCharacteristic_cell hA hComplCell, cellSign,
      compl_closedHalfspace_zero, affDim_openHalfspace_gt ha]
    simp
  omega

lemma convex_linear_hyperplane (a : E) : Convex ℝ {x : E | ⟪a, x⟫ = 0} :=
  convex_hyperplane (isLinearMap_inner a) 0

/-- Bounding hyperplane is a face of the closed halfspace cone. -/
lemma isFaceOf_closedHalfspace_hyperplane (a : E) :
    IsFaceOf (closedHalfspace a 0) {x : E | ⟪a, x⟫ = 0} := by
  refine ⟨⟨fun x hx => le_of_eq hx, ?_⟩, convex_linear_hyperplane a⟩
  intro x hxA y hyA z hzB hzSeg
  obtain ⟨b, c, hb, hc, _hbc, rfl⟩ := hzSeg
  change ⟪a, x⟫ ≤ 0 at hxA
  change ⟪a, y⟫ ≤ 0 at hyA
  have hz : ⟪a, b • x + c • y⟫ = 0 := hzB
  have hsum : b * ⟪a, x⟫ + c * ⟪a, y⟫ = 0 := by
    simpa [inner_add_right, inner_smul_right] using hz
  have hx0 : ⟪a, x⟫ = 0 := by
    have hbax : b * ⟪a, x⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb.le hxA
    have hcoy : c * ⟪a, y⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc.le hyA
    nlinarith
  exact hx0

/-- Affine dimension of a nontrivial linear hyperplane is `finrank - 1`. -/
lemma affDim_linear_hyperplane [FiniteDimensional ℝ E] [Nonempty E]
    {a : E} (ha : a ≠ 0) :
    affDim {x : E | ⟪a, x⟫ = 0} = Module.finrank ℝ E - 1 := by
  have hne : (((⊤ : AffineSubspace ℝ E) : Set E) ∩ {x | ⟪a, x⟫ = 0}).Nonempty := by
    obtain ⟨p, hp⟩ := exists_mem_hyperplane (b := 0) ha
    exact ⟨p, trivial, hp⟩
  have hnot : ¬ ((⊤ : AffineSubspace ℝ E) : Set E) ⊆ {x | ⟪a, x⟫ = 0} := by
    intro h
    have : ⟪a, a⟫ = 0 := h (by trivial : a ∈ (⊤ : AffineSubspace ℝ E))
    exact ha (inner_self_eq_zero.mp this)
  have h := affDim_affine_inter_hyperplane (⊤ : AffineSubspace ℝ E) a 0 hne hnot
  -- (⊤ : Set) = univ
  have hTop : ((⊤ : AffineSubspace ℝ E) : Set E) = univ := rfl
  rw [hTop, univ_inter, affDim_univ] at h
  exact h

/-! ### Two-halfspace polyhedral cone: cell EC = 0 -/

lemma isHyperplaneCellComplex_closedHalfspace_zero_mono {As : Set E} {a : E}
    (ha : a ∈ As) :
    IsHyperplaneCellComplex (coneArrangement As) (closedHalfspace a 0) :=
  isHyperplaneCellComplex_mono (isHyperplaneCellComplex_closedHalfspace_zero a)
    (Set.singleton_subset_iff.mpr ⟨a, ha, rfl⟩)

/-- Cell Euler char of a closed halfspace cone relative to any larger cone arrangement. -/
lemma eulerCharacteristic_closedHalfspace_zero_of_mem [FiniteDimensional ℝ E] [Nonempty E]
    {As : Set E} (hAs : As.Finite) {a : E} (ha : a ∈ As) (ha0 : a ≠ 0) :
    eulerCharacteristic (coneArrangement As) (closedHalfspace a 0) = 0 := by
  have hA := coneArrangement_finite hAs
  have hSing := eulerCharacteristic_halfspace_cone ha0
  have hCxS : IsHyperplaneCellComplex {(a, (0 : ℝ))} (closedHalfspace a 0) :=
    isHyperplaneCellComplex_closedHalfspace_zero a
  have hCxA : IsHyperplaneCellComplex (coneArrangement As) (closedHalfspace a 0) :=
    isHyperplaneCellComplex_closedHalfspace_zero_mono ha
  exact (eulerCharacteristic_invariant hA (finite_singleton _) hCxA hCxS).trans hSing

lemma openPositive_two (a b : E) :
    (closedHalfspace a 0)ᶜ ∩ (closedHalfspace b 0)ᶜ =
      {x : E | 0 < ⟪a, x⟫ ∧ 0 < ⟪b, x⟫} := by
  ext x
  simp [compl_closedHalfspace_zero]

/-- Cell-complex Euler characteristic of the intersection of two nontrivial halfspace cones
is `0` when the open dual is nonempty. Stepping stone toward general
`Euler_polyhedral_cone` face sum (face↔cell still open; cell EC general is proved). -/
theorem eulerCharacteristic_two_halfspace_cone [FiniteDimensional ℝ E] [Nonempty E]
    {a b : E} (ha : a ≠ 0) (hb : b ≠ 0)
    (hpos : ∃ x : E, ⟪a, x⟫ < 0 ∧ ⟪b, x⟫ < 0) :
    eulerCharacteristic (coneArrangement ({a, b} : Set E))
      (closedHalfspace a 0 ∩ closedHalfspace b 0) = 0 := by
  classical
  set As : Set E := {a, b}
  set A : Set (Hyperplane E) := coneArrangement As
  set Ha := closedHalfspace a 0
  set Hb := closedHalfspace b 0
  have hAs : As.Finite := (Set.finite_singleton b).insert a
  have hAfin : A.Finite := coneArrangement_finite hAs
  have haAs : a ∈ As := Set.mem_insert a _
  have hbAs : b ∈ As := Set.mem_insert_of_mem _ rfl
  have hHa : eulerCharacteristic A Ha = 0 :=
    eulerCharacteristic_closedHalfspace_zero_of_mem hAs haAs ha
  have hHb : eulerCharacteristic A Hb = 0 :=
    eulerCharacteristic_closedHalfspace_zero_of_mem hAs hbAs hb
  have hHaCx : IsHyperplaneCellComplex A Ha :=
    isHyperplaneCellComplex_closedHalfspace_zero_mono haAs
  have hHbCx : IsHyperplaneCellComplex A Hb :=
    isHyperplaneCellComplex_closedHalfspace_zero_mono hbAs
  -- Soft IE: EC(Ha ∩ Hb) = EC(Ha)+EC(Hb)-EC(Ha ∪ Hb)
  have hIE := eulerCharacteristic_union_inter (A := A) (S := Ha) (T := Hb) hAfin hHaCx hHbCx
  -- Ha ∪ Hb = univ \ openPositive; EC(univ) = EC(Ha∪Hb) + EC(P)
  set P : Set E := Haᶜ ∩ Hbᶜ
  have hPeq : P = {x : E | 0 < ⟪a, x⟫ ∧ 0 < ⟪b, x⟫} := openPositive_two a b
  have hneP : P.Nonempty := by
    obtain ⟨x, hxa, hxb⟩ := hpos
    refine ⟨-x, ?_⟩
    simp only [hPeq, Set.mem_ofPred_eq]
    exact ⟨by simpa [inner_neg_right] using neg_pos.mpr hxa,
      by simpa [inner_neg_right] using neg_pos.mpr hxb⟩
  have hPcell : IsHyperplaneCell A P := by
    -- P = {y | ∀ c ∈ {a,b}, 0 < ⟪c,y⟫}
    have hEq : P = {y : E | ∀ c ∈ As, 0 < ⟪c, y⟫} := by
      ext y
      simp only [hPeq, As, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
      constructor
      · intro ⟨hya, hyb⟩ c hc; rcases hc with rfl | rfl <;> assumption
      · intro hy; exact ⟨hy a (Or.inl rfl), hy b (Or.inr rfl)⟩
    rw [hEq]
    exact isHyperplaneCell_openPositive (by simpa [← hEq] using hneP)
  have hPcx : IsHyperplaneCellComplex A P := isHyperplaneCell_cellComplex hPcell
  have hUnionCx : IsHyperplaneCellComplex A (Ha ∪ Hb) :=
    isHyperplaneCellComplex_union hHaCx hHbCx
  have hdisj : Disjoint (Ha ∪ Hb) P := by
    refine Set.disjoint_left.mpr ?_
    intro x hxU hxP
    have hxP' : x ∈ Haᶜ ∧ x ∈ Hbᶜ := by simpa [P] using hxP
    rcases hxU with hxA | hxB
    · exact hxP'.1 hxA
    · exact hxP'.2 hxB
  have hcover : Ha ∪ Hb ∪ P = (Set.univ : Set E) := by
    ext x
    constructor
    · intro; trivial
    · intro
      by_cases hxa : x ∈ Ha
      · exact Or.inl (Or.inl hxa)
      · by_cases hxb : x ∈ Hb
        · exact Or.inl (Or.inr hxb)
        · exact Or.inr ⟨hxa, hxb⟩
  have hAdd :=
    eulerCharacteristic_cellcomplex_union hAfin hUnionCx hPcx hdisj
  rw [hcover, eulerCharacteristic_univ hAfin] at hAdd
  have hECP : eulerCharacteristic A P = (-1 : ℤ) ^ Module.finrank ℝ E := by
    have hEq : P = {y : E | ∀ c ∈ As, 0 < ⟪c, y⟫} := by
      ext y
      simp only [hPeq, As, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
      constructor
      · intro ⟨hya, hyb⟩ c hc; rcases hc with rfl | rfl <;> assumption
      · intro hy; exact ⟨hy a (Or.inl rfl), hy b (Or.inr rfl)⟩
    rw [hEq, eulerCharacteristic_cell hAfin (by
      simpa [← hEq] using hPcell), cellSign]
    -- affDim of open positive on {a,b}
    have hne : ({y : E | ∀ c ∈ As, 0 < ⟪c, y⟫}).Nonempty := by
      simpa [← hEq] using hneP
    have hopen : IsOpen {y : E | ∀ c ∈ As, 0 < ⟪c, y⟫} := by
      have : {y : E | ∀ c ∈ As, 0 < ⟪c, y⟫} =
          {y | 0 < ⟪a, y⟫} ∩ {y | 0 < ⟪b, y⟫} := by
        ext y
        simp only [As, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_inter_iff,
          Set.mem_ofPred_eq]
        constructor
        · intro hy; exact ⟨hy a (Or.inl rfl), hy b (Or.inr rfl)⟩
        · intro ⟨hya, hyb⟩ c hc; rcases hc with rfl | rfl <;> assumption
      rw [this]
      exact (isOpen_halfSpace_gt a 0).inter (isOpen_halfSpace_gt b 0)
    have hspan := hopen.affineSpan_eq_top hne
    have hdim := (affDim_eq_of_affineSpan_eq
      (hspan.trans (affineSpan_univ (E := E)).symm)).trans affDim_univ
    simp [hdim]
  have hECunion : eulerCharacteristic A (Ha ∪ Hb) = 0 := by omega
  -- rearrange soft IE: EC(Ha ∪ Hb) = EC(Ha)+EC(Hb)-EC(Ha ∩ Hb)
  -- so EC(Ha ∩ Hb) = EC(Ha)+EC(Hb)-EC(Ha ∪ Hb) = 0
  have : eulerCharacteristic A (Ha ∪ Hb) =
      eulerCharacteristic A Ha + eulerCharacteristic A Hb -
        eulerCharacteristic A (Ha ∩ Hb) := hIE
  omega

/-! ### Indexed inclusion-exclusion -/

/-- Alternating powerset sum over nonempty subsets equals `1` when `s` is nonempty. -/
lemma sum_powerset_filter_nonempty_neg_one_pow_card_add_one {α : Type*} [DecidableEq α]
    {s : Finset α} (hs : s.Nonempty) :
    ∑ t ∈ s.powerset.filter (·.Nonempty), (-1 : ℤ) ^ (t.card + 1) = 1 := by
  set F : Finset (Finset α) := s.powerset.filter (·.Nonempty)
  have hfull := Finset.sum_powerset_neg_one_pow_card_of_nonempty (x := s) hs
  have hpartition : s.powerset = insert (∅ : Finset α) F := by
    ext t
    simp only [F, Finset.mem_insert, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro ht
      by_cases hne : t.Nonempty
      · exact Or.inr ⟨ht, hne⟩
      · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp hne)
    · rintro (rfl | ⟨ht, _⟩)
      · exact Finset.empty_subset _
      · exact ht
  have hnot : (∅ : Finset α) ∉ F := by
    simp [F, Finset.not_nonempty_empty]
  have hsplit : ∑ t ∈ s.powerset, (-1 : ℤ) ^ t.card = 1 + ∑ t ∈ F, (-1 : ℤ) ^ t.card := by
    rw [hpartition, Finset.sum_insert hnot]
    simp
  have hneg : ∑ t ∈ F, (-1 : ℤ) ^ t.card = -1 := by linarith
  calc
    ∑ t ∈ F, (-1 : ℤ) ^ (t.card + 1)
        = ∑ t ∈ F, (-((-1 : ℤ) ^ t.card)) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [pow_succ]; ring
    _ = -∑ t ∈ F, (-1 : ℤ) ^ t.card := by simp [Finset.sum_neg_distrib]
    _ = -(-1) := by rw [hneg]
    _ = 1 := by ring

/-- Cells of `A` contained in `S`, as a finset. -/
noncomputable def cellsBelow (A : Set (Hyperplane E)) (S : Set E) (hA : A.Finite) :
    Finset (Set E) :=
  (finite_isHyperplaneCell_restrict hA (fun C => C ⊆ S)).toFinset

lemma mem_cellsBelow_iff {A : Set (Hyperplane E)} {S C : Set E} (hA : A.Finite) :
    C ∈ cellsBelow A S hA ↔ IsHyperplaneCell A C ∧ C ⊆ S := by
  simp [cellsBelow, Finite.mem_toFinset]

lemma eulerCharacteristic_eq_sum_cellsBelow {A : Set (Hyperplane E)} {S : Set E}
    (hA : A.Finite) :
    eulerCharacteristic A S = ∑ C ∈ cellsBelow A S hA, cellSign C :=
  (eulerCharacteristic_eq_sum hA (S := S)).trans (by simp [cellsBelow])

lemma cellsBelow_biUnion {ι : Type*} {A : Set (Hyperplane E)} (hA : A.Finite)
    (s : Finset ι) (S : ι → Set E)
    (hS : ∀ i ∈ s, IsHyperplaneCellComplex A (S i)) :
    cellsBelow A (⋃ i ∈ s, S i) hA = s.biUnion fun i => cellsBelow A (S i) hA := by
  classical
  ext C
  simp only [mem_cellsBelow_iff, Finset.mem_biUnion]
  constructor
  · intro ⟨hC, hsub⟩
    obtain ⟨x, hx⟩ := nonempty_isHyperplaneCell hC
    obtain ⟨i, hi, hxS⟩ := Set.mem_iUnion₂.mp (hsub hx)
    exact ⟨i, hi, hC, (cell_subset_cellcomplex hC (hS i hi)).mpr ⟨x, hx, hxS⟩⟩
  · rintro ⟨i, hi, hC, hCS⟩
    exact ⟨hC, hCS.trans (Set.subset_biUnion_of_mem hi)⟩

lemma biInter_cellsBelow {ι : Type*} {A : Set (Hyperplane E)} (hA : A.Finite)
    (t : Finset ι) (S : ι → Set E) (ht : t.Nonempty) :
    (t.inf' ht (fun i => cellsBelow A (S i) hA)) = cellsBelow A (⋂ i ∈ t, S i) hA := by
  classical
  ext C
  constructor
  · intro hC
    have hmem : ∀ i ∈ t, C ∈ cellsBelow A (S i) hA := (Finset.mem_inf' _).1 hC
    obtain ⟨i₀, hi₀⟩ := ht
    have hCcell : IsHyperplaneCell A C := ((mem_cellsBelow_iff hA).1 (hmem i₀ hi₀)).1
    refine (mem_cellsBelow_iff hA).2 ⟨hCcell, ?_⟩
    intro x hx
    exact Set.mem_iInter₂.2 fun i hi => ((mem_cellsBelow_iff hA).1 (hmem i hi)).2 hx
  · intro hC
    refine (Finset.mem_inf' _).2 fun i hi => ?_
    have ⟨hcell, hsub⟩ := (mem_cellsBelow_iff hA).1 hC
    exact (mem_cellsBelow_iff hA).2 ⟨hcell, hsub.trans (Set.biInter_subset_of_mem hi)⟩

/-- Indexed inclusion-exclusion for Euler characteristic of a finite union of cell complexes.
Paulson: `Euler_characteristic_inclusion_exclusion`. -/
lemma eulerCharacteristic_biUnion_inclusion_exclusion {ι : Type*} [DecidableEq ι]
    {A : Set (Hyperplane E)} (hA : A.Finite) (s : Finset ι) (S : ι → Set E)
    (hS : ∀ i ∈ s, IsHyperplaneCellComplex A (S i)) :
    eulerCharacteristic A (⋃ i ∈ s, S i) =
      ∑ t ∈ s.powerset.filter (·.Nonempty),
        (-1 : ℤ) ^ (t.card + 1) * eulerCharacteristic A (⋂ i ∈ t, S i) := by
  classical
  have hL : eulerCharacteristic A (⋃ i ∈ s, S i) =
      ∑ C ∈ s.biUnion fun i => cellsBelow A (S i) hA, cellSign C := by
    rw [eulerCharacteristic_eq_sum_cellsBelow (hA := hA), cellsBelow_biUnion hA s S hS]
  have hIE := Finset.inclusion_exclusion_sum_biUnion (G := ℤ) s
    (fun i => cellsBelow A (S i) hA) cellSign
  rw [hL, hIE, ← Finset.sum_attach (s.powerset.filter (·.Nonempty))]
  refine Finset.sum_congr rfl fun t _ => ?_
  have ht_ne : t.1.Nonempty := (Finset.mem_filter.mp t.2).2
  have hinf : (t.1.inf' ht_ne (fun i => cellsBelow A (S i) hA)) =
      cellsBelow A (⋂ i ∈ t.1, S i) hA := biInter_cellsBelow hA t.1 S ht_ne
  simp only [zsmul_eq_mul, Int.cast_id]
  rw [hinf, eulerCharacteristic_eq_sum_cellsBelow (hA := hA)]

set_option linter.unusedSectionVars false in
lemma coneArrangement_mono {As Bs : Set E} (h : As ⊆ Bs) :
    coneArrangement As ⊆ coneArrangement Bs :=
  Set.image_mono h

lemma isOpen_openPositive {As : Set E} (hAs : As.Finite) :
    IsOpen {x : E | ∀ a ∈ As, 0 < ⟪a, x⟫} := by
  classical
  have hEq : {x : E | ∀ a ∈ As, 0 < ⟪a, x⟫} =
      ⋂ a ∈ hAs.toFinset, {x : E | 0 < ⟪a, x⟫} := by
    ext x
    simp [Finite.mem_toFinset]
  rw [hEq]
  exact isOpen_biInter_finset fun a _ => isOpen_halfSpace_gt a (0 : ℝ)

lemma affDim_openPositive [FiniteDimensional ℝ E] [Nonempty E]
    {As : Set E} (hAs : As.Finite)
    (hne : ({x : E | ∀ a ∈ As, 0 < ⟪a, x⟫}).Nonempty) :
    affDim {x : E | ∀ a ∈ As, 0 < ⟪a, x⟫} = Module.finrank ℝ E := by
  have hopen := isOpen_openPositive hAs
  have hspan := hopen.affineSpan_eq_top hne
  exact (affDim_eq_of_affineSpan_eq
    (hspan.trans (affineSpan_univ (E := E)).symm)).trans affDim_univ

/-- Open dual of a finite set of normals has cell Euler char `(-1)^{finrank}`,
relative to any larger cone arrangement. -/
lemma eulerCharacteristic_openPositive [FiniteDimensional ℝ E] [Nonempty E]
    {As Bs : Set E} (hAs : As.Finite) (hBs : Bs.Finite) (hsub : As ⊆ Bs)
    (hne : ({x : E | ∀ a ∈ As, 0 < ⟪a, x⟫}).Nonempty) :
    eulerCharacteristic (coneArrangement Bs) {x : E | ∀ a ∈ As, 0 < ⟪a, x⟫} =
      (-1 : ℤ) ^ Module.finrank ℝ E := by
  set P : Set E := {x : E | ∀ a ∈ As, 0 < ⟪a, x⟫}
  have hPcell : IsHyperplaneCell (coneArrangement As) P :=
    isHyperplaneCell_openPositive (As := As) hne
  have hPcxAs : IsHyperplaneCellComplex (coneArrangement As) P :=
    isHyperplaneCell_cellComplex hPcell
  have hPcxBs : IsHyperplaneCellComplex (coneArrangement Bs) P :=
    isHyperplaneCellComplex_mono hPcxAs (coneArrangement_mono hsub)
  have hAfin := coneArrangement_finite hAs
  have hBfin := coneArrangement_finite hBs
  have hinv := eulerCharacteristic_invariant hBfin hAfin hPcxBs hPcxAs
  have hcell : eulerCharacteristic (coneArrangement As) P = cellSign P :=
    eulerCharacteristic_cell hAfin hPcell
  have hdim := affDim_openPositive hAs hne
  calc
    eulerCharacteristic (coneArrangement Bs) P
        = eulerCharacteristic (coneArrangement As) P := hinv
    _ = cellSign P := hcell
    _ = (-1 : ℤ) ^ Module.finrank ℝ E := by
      unfold cellSign
      rw [hdim]
      simp

/-- Cell-complex Euler characteristic of a proper full-dimensional polyhedral cone
(finite homogeneous H-rep with nonempty open dual) is `0`.
Generalises the 1- and 2-halfspace theorems via indexed inclusion-exclusion. -/
theorem eulerCharacteristic_polyhedral_cone [FiniteDimensional ℝ E] [Nonempty E]
    {As : Set E} (hAs : As.Finite) (hneAs : As.Nonempty)
    (hpos : ({x : E | ∀ a ∈ As, 0 < ⟪a, x⟫}).Nonempty) :
    eulerCharacteristic (coneArrangement As) (⋂ a ∈ As, closedHalfspace a 0) = 0 := by
  classical
  set A : Set (Hyperplane E) := coneArrangement As
  have hAfin : A.Finite := coneArrangement_finite hAs
  set Fs := hAs.toFinset
  have hFs_ne : Fs.Nonempty := by
    simpa [Fs, Finite.toFinset_nonempty] using hneAs
  have hConeEq : (⋂ a ∈ As, closedHalfspace a 0) = ⋂ a ∈ Fs, closedHalfspace a 0 := by
    ext x
    simp [Fs, Finite.mem_toFinset]
  have hConeCx : IsHyperplaneCellComplex A (⋂ a ∈ As, closedHalfspace a 0) :=
    isHyperplaneCellComplex_polyhedralCone hAs
  have hComplEq :
      (⋂ a ∈ As, closedHalfspace a 0)ᶜ = ⋃ a ∈ Fs, (closedHalfspace a 0)ᶜ := by
    rw [hConeEq]
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iInter, Set.mem_iUnion, not_forall]
  have hComplFam : ∀ a ∈ Fs, IsHyperplaneCellComplex A (closedHalfspace a 0)ᶜ := fun a ha => by
    have haAs : a ∈ As := by simpa [Fs] using ha
    exact isHyperplaneCellComplex_compl
      (isHyperplaneCellComplex_closedHalfspace_zero_mono haAs)
  have hIE := eulerCharacteristic_biUnion_inclusion_exclusion hAfin Fs
    (fun a => (closedHalfspace a 0)ᶜ) hComplFam
  have hterm : ∀ t ∈ Fs.powerset.filter (·.Nonempty),
      eulerCharacteristic A (⋂ a ∈ t, (closedHalfspace a 0)ᶜ) =
        (-1 : ℤ) ^ Module.finrank ℝ E := by
    intro t ht
    have ht_sub : (t : Set E) ⊆ As := by
      intro a ha
      have : a ∈ Fs := Finset.mem_of_subset
        (Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1) ha
      simpa [Fs] using this
    have hEq : (⋂ a ∈ t, (closedHalfspace a 0)ᶜ) =
        {x : E | ∀ a ∈ (t : Set E), 0 < ⟪a, x⟫} := by
      ext x
      simp [compl_closedHalfspace_zero]
    have hneP : ({x : E | ∀ a ∈ (t : Set E), 0 < ⟪a, x⟫}).Nonempty := by
      obtain ⟨x, hx⟩ := hpos
      exact ⟨x, fun a ha => hx a (ht_sub ha)⟩
    rw [hEq]
    exact eulerCharacteristic_openPositive t.finite_toSet hAs ht_sub hneP
  have hECcompl :
      eulerCharacteristic A (⋃ a ∈ Fs, (closedHalfspace a 0)ᶜ) =
        (-1 : ℤ) ^ Module.finrank ℝ E := by
    rw [hIE]
    have hcongr :
        ∑ t ∈ Fs.powerset.filter (·.Nonempty),
            (-1 : ℤ) ^ (t.card + 1) *
              eulerCharacteristic A (⋂ a ∈ t, (closedHalfspace a 0)ᶜ) =
          ∑ t ∈ Fs.powerset.filter (·.Nonempty),
            (-1 : ℤ) ^ (t.card + 1) * ((-1 : ℤ) ^ Module.finrank ℝ E) :=
      Finset.sum_congr rfl fun t ht => by rw [hterm t ht]
    rw [hcongr, ← Finset.sum_mul,
      sum_powerset_filter_nonempty_neg_one_pow_card_add_one hFs_ne, one_mul]
  have hdisj :
      Disjoint (⋂ a ∈ As, closedHalfspace a 0)
        (⋃ a ∈ Fs, (closedHalfspace a 0)ᶜ) := by
    rw [← hComplEq]; exact disjoint_compl_right
  have hcover :
      (⋂ a ∈ As, closedHalfspace a 0) ∪ ⋃ a ∈ Fs, (closedHalfspace a 0)ᶜ = univ := by
    rw [← hComplEq, union_compl_self]
  have hComplCx : IsHyperplaneCellComplex A (⋃ a ∈ Fs, (closedHalfspace a 0)ᶜ) :=
    isHyperplaneCellComplex_biUnion_finset Fs _ hComplFam
  have hAdd :=
    eulerCharacteristic_cellcomplex_union hAfin hConeCx hComplCx hdisj
  rw [hcover, eulerCharacteristic_univ hAfin, hECcompl] at hAdd
  omega

/-- Stated Paulson targets (not claimed in Results.lean until proved in full). -/
def EulerPolyhedralConeGoal : String :=
  "faceEulerSum S (finrank) = 0 for full-dim proper polyhedral cones"

def EulerPoincareFullGoal : String :=
  "faceEulerSum p (finrank) = 1 for full-dimensional convex polytopes"

def EulerRelation3DGoal : String :=
  "V - E + F = 2 for convex 3-polytopes (after Euler_Poincare_full)"

end EulersGem

/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Basic.Sign.Defs

/-!
# Hyperplane arrangements (Paulson substrate)

Lean port of the opening of Lawrence C. Paulson's AFP
[*Euler's Polyhedron Formula*](https://isa-afp.org/entries/Euler_Polyhedron_Formula.html)
(theory `Euler_Formula`):

* `hyperplaneSide` — which side of an affine hyperplane a point lies on
* `HyperplaneEquiv` — same side of every hyperplane in an arrangement
* `IsHyperplaneCell` — equivalence classes (= cells of the arrangement)

Isabelle names: `hyperplane_side`, `hyperplane_equiv`, `hyperplane_cell`.

This file proves the elementary structural lemmas (equivalence relation, empty
arrangement, disjointness, singleton classification, convexity). Cell complexes,
Euler characteristic, and invariance come next.
-/

open scoped RealInnerProductSpace
open Set SignType

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace EulersGem

/-- An affine hyperplane given in H-description by `⟪a, x⟫ = b`.
Degenerate when `a = 0` (matches Paulson: the whole space or empty, via `sgn`). -/
abbrev Hyperplane (E : Type*) := E × ℝ

/-- Which side of the hyperplane `(a, b)` the point `x` lies on:
`sign (⟪a, x⟫ − b) ∈ {−1, 0, 1}`. Isabelle: `hyperplane_side`. -/
noncomputable def hyperplaneSide (h : Hyperplane E) (x : E) : SignType :=
  SignType.sign (⟪h.1, x⟫ - h.2)

/-- Points equivalent under arrangement `A`: same side of every hyperplane in `A`.
Isabelle: `hyperplane_equiv`. -/
def HyperplaneEquiv (A : Set (Hyperplane E)) (x y : E) : Prop :=
  ∀ h ∈ A, hyperplaneSide h x = hyperplaneSide h y

lemma hyperplaneEquiv_refl (A : Set (Hyperplane E)) (x : E) :
    HyperplaneEquiv A x x := fun _ _ => rfl

lemma hyperplaneEquiv_symm {A : Set (Hyperplane E)} {x y : E}
    (h : HyperplaneEquiv A x y) : HyperplaneEquiv A y x := by
  intro hp hpA
  exact (h hp hpA).symm

lemma hyperplaneEquiv_trans {A : Set (Hyperplane E)} {x y z : E}
    (hxy : HyperplaneEquiv A x y) (hyz : HyperplaneEquiv A y z) :
    HyperplaneEquiv A x z := by
  intro hp hpA
  exact (hxy hp hpA).trans (hyz hp hpA)

lemma hyperplaneEquiv_union (A B : Set (Hyperplane E)) (x y : E) :
    HyperplaneEquiv (A ∪ B) x y ↔ HyperplaneEquiv A x y ∧ HyperplaneEquiv B x y := by
  constructor
  · intro h
    exact ⟨fun hp hpA => h hp (Or.inl hpA), fun hp hpB => h hp (Or.inr hpB)⟩
  · rintro ⟨hA, hB⟩ hp hpAB
    cases hpAB with
    | inl h => exact hA hp h
    | inr h => exact hB hp h

/-- `C` is a cell of arrangement `A` iff it is an equivalence class of
`HyperplaneEquiv A`. Isabelle: `hyperplane_cell`. -/
def IsHyperplaneCell (A : Set (Hyperplane E)) (C : Set E) : Prop :=
  ∃ x, C = {y | HyperplaneEquiv A x y}

lemma isHyperplaneCell_iff (A : Set (Hyperplane E)) (C : Set E) :
    IsHyperplaneCell A C ↔ ∃ x, C = {y | HyperplaneEquiv A x y} :=
  Iff.rfl

lemma not_isHyperplaneCell_empty (A : Set (Hyperplane E)) :
    ¬ IsHyperplaneCell A (∅ : Set E) := by
  rintro ⟨x, hx⟩
  have : x ∈ (∅ : Set E) := by
    rw [hx]
    exact hyperplaneEquiv_refl A x
  exact this

lemma nonempty_isHyperplaneCell {A : Set (Hyperplane E)} {C : Set E}
    (h : IsHyperplaneCell A C) : C.Nonempty := by
  obtain ⟨x, rfl⟩ := h
  exact ⟨x, hyperplaneEquiv_refl A x⟩

lemma iUnion_isHyperplaneCell (A : Set (Hyperplane E)) :
    ⋃₀ {C | IsHyperplaneCell A C} = univ := by
  ext x
  constructor
  · intro; trivial
  · intro
    refine ⟨{y | HyperplaneEquiv A x y}, ?_, hyperplaneEquiv_refl A x⟩
    exact ⟨x, rfl⟩

lemma disjoint_isHyperplaneCell {A : Set (Hyperplane E)} {C₁ C₂ : Set E}
    (h₁ : IsHyperplaneCell A C₁) (h₂ : IsHyperplaneCell A C₂) (hne : C₁ ≠ C₂) :
    Disjoint C₁ C₂ := by
  obtain ⟨x₁, rfl⟩ := h₁
  obtain ⟨x₂, rfl⟩ := h₂
  rw [disjoint_iff_inter_eq_empty]
  ext y
  simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
  intro ⟨hy₁, hy₂⟩
  -- hy₁ : x₁ ~ y, hy₂ : x₂ ~ y  ⇒  the two classes coincide
  apply hne
  ext z
  simp only [mem_ofPred_eq]
  constructor
  · -- x₁ ~ z ⇒ x₂ ~ z   via  x₂ ~ y ~ x₁ ~ z
    intro hz
    have h_yx₁ : HyperplaneEquiv A y x₁ := hyperplaneEquiv_symm (A := A) hy₁
    have h_x₂y : HyperplaneEquiv A x₂ y := hy₂
    have h_yx₁z : HyperplaneEquiv A y z :=
      hyperplaneEquiv_trans (A := A) h_yx₁ hz
    exact hyperplaneEquiv_trans (A := A) h_x₂y h_yx₁z
  · -- x₂ ~ z ⇒ x₁ ~ z   via  x₁ ~ y ~ x₂ ~ z
    intro hz
    have h_yx₂ : HyperplaneEquiv A y x₂ := hyperplaneEquiv_symm (A := A) hy₂
    have h_x₁y : HyperplaneEquiv A x₁ y := hy₁
    have h_yx₂z : HyperplaneEquiv A y z :=
      hyperplaneEquiv_trans (A := A) h_yx₂ hz
    exact hyperplaneEquiv_trans (A := A) h_x₁y h_yx₂z

lemma isHyperplaneCell_empty_arrangement (C : Set E) :
    IsHyperplaneCell (∅ : Set (Hyperplane E)) C ↔ C = univ := by
  constructor
  · rintro ⟨x, rfl⟩
    ext y
    simp [HyperplaneEquiv]
  · intro h
    refine ⟨(0 : E), ?_⟩
    rw [h]
    ext y
    simp [HyperplaneEquiv]

/-- Linear map `x ↦ ⟪a, x⟫`. -/
lemma isLinearMap_inner (a : E) : IsLinearMap ℝ (fun x : E => ⟪a, x⟫) where
  map_add := fun x y => by simp [inner_add_right]
  map_smul := fun c x => by simp [inner_smul_right]

lemma hyperplaneSide_eq_zero_iff (a : E) (b : ℝ) (x : E) :
    hyperplaneSide (a, b) x = 0 ↔ ⟪a, x⟫ = b := by
  simp [hyperplaneSide, sign_eq_zero_iff, sub_eq_zero]

lemma hyperplaneSide_eq_one_iff (a : E) (b : ℝ) (x : E) :
    hyperplaneSide (a, b) x = 1 ↔ b < ⟪a, x⟫ := by
  simp [hyperplaneSide, sign_eq_one_iff, sub_pos]

lemma hyperplaneSide_eq_neg_one_iff (a : E) (b : ℝ) (x : E) :
    hyperplaneSide (a, b) x = -1 ↔ ⟪a, x⟫ < b := by
  simp [hyperplaneSide, sign_eq_neg_one_iff, sub_neg]

/-- Fixed hyperplane `(a,b)`: the set of points with a given side is a hyperplane
or an open half-space (hence convex). -/
lemma convex_hyperplaneSide_eq (a : E) (b : ℝ) (s : SignType) :
    Convex ℝ {y : E | hyperplaneSide (a, b) y = s} := by
  have hlin : IsLinearMap ℝ (fun x : E => ⟪a, x⟫) := isLinearMap_inner a
  rcases (trichotomy s) with hs | hs | hs
  · have : {y : E | hyperplaneSide (a, b) y = s} = {y | ⟪a, y⟫ < b} := by
      ext y; simp [hs, hyperplaneSide_eq_neg_one_iff]
    rw [this]; exact convex_halfSpace_lt hlin b
  · have : {y : E | hyperplaneSide (a, b) y = s} = {y | ⟪a, y⟫ = b} := by
      ext y; simp [hs, hyperplaneSide_eq_zero_iff]
    rw [this]; exact convex_hyperplane hlin b
  · have : {y : E | hyperplaneSide (a, b) y = s} = {y | b < ⟪a, y⟫} := by
      ext y; simp [hs, hyperplaneSide_eq_one_iff]
    rw [this]; exact convex_halfSpace_gt hlin b

/-- Cells of a singleton arrangement `{ (a,b) }` are the hyperplane or one of the
two open half-spaces. Isabelle: `hyperplane_cell_singleton_cases`. -/
lemma isHyperplaneCell_singleton_cases {a : E} {b : ℝ} {C : Set E}
    (h : IsHyperplaneCell {(a, b)} C) :
    C = {x | ⟪a, x⟫ = b} ∨ C = {x | ⟪a, x⟫ < b} ∨ C = {x | b < ⟪a, x⟫} := by
  obtain ⟨x, rfl⟩ := h
  have tri := trichotomy (hyperplaneSide (a, b) x)
  rcases tri with h0 | h0 | h0
  · refine Or.inr (Or.inl ?_)
    ext y
    simp only [mem_ofPred_eq, HyperplaneEquiv, mem_singleton_iff, forall_eq]
    constructor
    · intro hy
      exact (hyperplaneSide_eq_neg_one_iff a b y).mp (by simpa [h0] using hy.symm)
    · intro hy
      have : hyperplaneSide (a, b) y = -1 :=
        (hyperplaneSide_eq_neg_one_iff a b y).mpr hy
      simp [h0, this]
  · refine Or.inl ?_
    ext y
    simp only [mem_ofPred_eq, HyperplaneEquiv, mem_singleton_iff, forall_eq]
    constructor
    · intro hy
      exact (hyperplaneSide_eq_zero_iff a b y).mp (by simpa [h0] using hy.symm)
    · intro hy
      have : hyperplaneSide (a, b) y = 0 :=
        (hyperplaneSide_eq_zero_iff a b y).mpr hy
      simp [h0, this]
  · refine Or.inr (Or.inr ?_)
    ext y
    simp only [mem_ofPred_eq, HyperplaneEquiv, mem_singleton_iff, forall_eq]
    constructor
    · intro hy
      exact (hyperplaneSide_eq_one_iff a b y).mp (by simpa [h0] using hy.symm)
    · intro hy
      have : hyperplaneSide (a, b) y = 1 :=
        (hyperplaneSide_eq_one_iff a b y).mpr hy
      simp [h0, this]

/-- Every cell is convex. Isabelle: `hyperplane_cell_convex`. -/
lemma isHyperplaneCell_convex {A : Set (Hyperplane E)} {C : Set E}
    (hC : IsHyperplaneCell A C) : Convex ℝ C := by
  obtain ⟨c, rfl⟩ := hC
  have eq : {y | HyperplaneEquiv A c y} =
      ⋂ h ∈ A, {y | hyperplaneSide h c = hyperplaneSide h y} := by
    ext y; simp [HyperplaneEquiv]
  rw [eq]
  refine convex_iInter fun h => convex_iInter fun _ => ?_
  have : {y : E | hyperplaneSide h c = hyperplaneSide h y} =
      {y | hyperplaneSide h y = hyperplaneSide h c} := by
    ext y; constructor <;> intro hy <;> exact hy.symm
  rw [this]
  obtain ⟨a, b⟩ := h
  exact convex_hyperplaneSide_eq a b (hyperplaneSide (a, b) c)

/-- Cell complex: a union of cells of arrangement `A`.
Isabelle: `hyperplane_cellcomplex`. -/
def IsHyperplaneCellComplex (A : Set (Hyperplane E)) (S : Set E) : Prop :=
  ∃ 𝒯 : Set (Set E), (∀ C ∈ 𝒯, IsHyperplaneCell A C) ∧ S = ⋃₀ 𝒯

lemma isHyperplaneCellComplex_empty (A : Set (Hyperplane E)) :
    IsHyperplaneCellComplex A (∅ : Set E) :=
  ⟨∅, by simp⟩

lemma isHyperplaneCell_cellComplex {A : Set (Hyperplane E)} {C : Set E}
    (h : IsHyperplaneCell A C) : IsHyperplaneCellComplex A C :=
  ⟨{C}, by simp [h]⟩

lemma isHyperplaneCellComplex_univ (A : Set (Hyperplane E)) :
    IsHyperplaneCellComplex A (univ : Set E) :=
  ⟨{C | IsHyperplaneCell A C}, ⟨fun _ h => h, (iUnion_isHyperplaneCell A).symm⟩⟩

lemma isHyperplaneCellComplex_sUnion {A : Set (Hyperplane E)}
    {𝒞 : Set (Set E)} (h : ∀ S ∈ 𝒞, IsHyperplaneCellComplex A S) :
    IsHyperplaneCellComplex A (⋃₀ 𝒞) := by
  -- Flatten the witnessing cell collections.
  let 𝒯 : Set (Set E) :=
    {C | ∃ S ∈ 𝒞, ∃ ℱ, (∀ D ∈ ℱ, IsHyperplaneCell A D) ∧ S = ⋃₀ ℱ ∧ C ∈ ℱ}
  refine ⟨𝒯, ⟨?_, ?_⟩⟩
  · intro C hC
    obtain ⟨S, _, ℱ, hcells, _, hCℱ⟩ := hC
    exact hcells C hCℱ
  · ext x
    constructor
    · intro hx
      obtain ⟨S, hS, hxS⟩ := hx
      obtain ⟨ℱ, hcells, hSeq⟩ := h S hS
      have : x ∈ ⋃₀ ℱ := by simpa [hSeq] using hxS
      obtain ⟨C, hC, hxC⟩ := this
      exact ⟨C, ⟨S, hS, ℱ, hcells, hSeq, hC⟩, hxC⟩
    · intro hx
      obtain ⟨C, ⟨S, hS, ℱ, hcells, hSeq, hC⟩, hxC⟩ := hx
      refine ⟨S, hS, ?_⟩
      have : x ∈ ⋃₀ ℱ := ⟨C, hC, hxC⟩
      simpa [hSeq] using this

lemma isHyperplaneCellComplex_union {A : Set (Hyperplane E)} {S T : Set E}
    (hS : IsHyperplaneCellComplex A S) (hT : IsHyperplaneCellComplex A T) :
    IsHyperplaneCellComplex A (S ∪ T) := by
  simpa [sUnion_pair] using
    isHyperplaneCellComplex_sUnion (𝒞 := {S, T}) (by
      intro U hU
      simp only [mem_insert_iff, mem_singleton_iff] at hU
      rcases hU with rfl | rfl <;> assumption)


/-! ### Union characterisation & finiteness -/

/-- Cells of a union arrangement are nonempty intersections of an `A`-cell and a `B`-cell.
Isabelle: `hyperplane_cell_Un`. -/
lemma isHyperplaneCell_union (A B : Set (Hyperplane E)) (C : Set E) :
    IsHyperplaneCell (A ∪ B) C ↔
      C.Nonempty ∧
        ∃ C1 C2, IsHyperplaneCell A C1 ∧ IsHyperplaneCell B C2 ∧ C = C1 ∩ C2 := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨⟨x, hyperplaneEquiv_refl (A ∪ B) x⟩,
      {y | HyperplaneEquiv A x y}, {y | HyperplaneEquiv B x y},
      ⟨x, rfl⟩, ⟨x, rfl⟩, ?_⟩
    ext y
    simp only [mem_inter_iff, mem_ofPred_eq]
    exact hyperplaneEquiv_union A B x y
  · rintro ⟨⟨z, hz⟩, C1, C2, hC1, hC2, rfl⟩
    obtain ⟨x1, rfl⟩ := hC1
    obtain ⟨x2, rfl⟩ := hC2
    refine ⟨z, ?_⟩
    ext y
    constructor
    · intro ⟨hyA, hyB⟩
      exact (hyperplaneEquiv_union A B z y).mpr
        ⟨hyperplaneEquiv_trans (hyperplaneEquiv_symm hz.1) hyA,
          hyperplaneEquiv_trans (hyperplaneEquiv_symm hz.2) hyB⟩
    · intro hy
      have hy' := (hyperplaneEquiv_union A B z y).mp hy
      exact ⟨hyperplaneEquiv_trans hz.1 hy'.1, hyperplaneEquiv_trans hz.2 hy'.2⟩

lemma isHyperplaneCell_singleton_subset (a : E) (b : ℝ) :
    {C : Set E | IsHyperplaneCell {(a, b)} C} ⊆
      {{x | ⟪a, x⟫ = b}, {x | ⟪a, x⟫ < b}, {x | b < ⟪a, x⟫}} := by
  intro C hC
  rcases isHyperplaneCell_singleton_cases hC with h | h | h <;> simp [h]

lemma finite_isHyperplaneCell_singleton (h : Hyperplane E) :
    {C : Set E | IsHyperplaneCell {h} C}.Finite := by
  obtain ⟨a, b⟩ := h
  exact (Finite.insert _ (Finite.insert _ (finite_singleton _))).subset
    (isHyperplaneCell_singleton_subset a b)

/-- A finite arrangement has finitely many cells. Isabelle: `finite_hyperplane_cells`. -/
lemma finite_isHyperplaneCell {A : Set (Hyperplane E)} (hA : A.Finite) :
    {C : Set E | IsHyperplaneCell A C}.Finite := by
  refine Set.Finite.induction_on (motive := fun A _ =>
    ({C : Set E | IsHyperplaneCell A C}).Finite) A hA ?empty ?insert
  · refine (finite_singleton (univ : Set E)).subset ?_
    intro C hC
    exact (isHyperplaneCell_empty_arrangement C).mp hC
  · intro p A hp hA ih
    have hfin_p := finite_isHyperplaneCell_singleton p
    let cells : Set (Set E) :=
      ⋃ C1 ∈ {C | IsHyperplaneCell A C},
        ⋃ C2 ∈ {C | IsHyperplaneCell {p} C}, {C1 ∩ C2}
    have hsub : {C : Set E | IsHyperplaneCell (insert p A) C} ⊆ cells := by
      intro C hC
      have hC' : IsHyperplaneCell ({p} ∪ A) C := by
        rwa [show insert p A = {p} ∪ A from insert_eq p A] at hC
      obtain ⟨-, Cp, CA, hCp, hCA, rfl⟩ := (isHyperplaneCell_union {p} A C).mp hC'
      -- cells indexes A-cell first, then {p}-cell; goal is Cp ∩ CA ∈ cells
      rw [inter_comm]
      exact mem_biUnion hCA (mem_biUnion hCp rfl)
    have hfin : cells.Finite :=
      Finite.biUnion ih fun _ _ => Finite.biUnion hfin_p fun _ _ => finite_singleton _
    exact hfin.subset hsub

lemma finite_isHyperplaneCell_restrict {A : Set (Hyperplane E)} (hA : A.Finite)
    (P : Set E → Prop) :
    {C : Set E | IsHyperplaneCell A C ∧ P C}.Finite :=
  (finite_isHyperplaneCell hA).subset fun _ h => h.1

lemma pairwise_disjoint_isHyperplaneCell {A : Set (Hyperplane E)} {Cs : Set (Set E)}
    (h : ∀ C ∈ Cs, IsHyperplaneCell A C) :
    Cs.Pairwise Disjoint :=
  fun _ h1 _ h2 hne => disjoint_isHyperplaneCell (h _ h1) (h _ h2) hne

/-- Intersection of two cells of the same arrangement is a cell when nonempty. -/
lemma isHyperplaneCell_inter {A : Set (Hyperplane E)} {S T : Set E}
    (hS : IsHyperplaneCell A S) (hT : IsHyperplaneCell A T) (hne : (S ∩ T).Nonempty) :
    IsHyperplaneCell A (S ∩ T) := by
  by_cases hEq : S = T
  · simpa [hEq] using hS
  · have : S ∩ T = ∅ := disjoint_iff_inter_eq_empty.mp (disjoint_isHyperplaneCell hS hT hEq)
    exact absurd hne (this.symm ▸ Set.not_nonempty_empty)

/-- Cell complexes are closed under binary intersection. -/
lemma isHyperplaneCellComplex_inter {A : Set (Hyperplane E)} {S T : Set E}
    (hS : IsHyperplaneCellComplex A S) (hT : IsHyperplaneCellComplex A T) :
    IsHyperplaneCellComplex A (S ∩ T) := by
  obtain ⟨FS, hcellsS, hSeq⟩ := hS
  obtain ⟨FT, hcellsT, hTeq⟩ := hT
  let Ts : Set (Set E) :=
    {C | ∃ C1 ∈ FS, ∃ C2 ∈ FT, C = C1 ∩ C2 ∧ (C1 ∩ C2).Nonempty}
  refine ⟨Ts, ⟨?_, ?_⟩⟩
  · intro C hC
    obtain ⟨C1, hC1, C2, hC2, rfl, hne⟩ := hC
    exact isHyperplaneCell_inter (hcellsS C1 hC1) (hcellsT C2 hC2) hne
  · ext x
    constructor
    · intro ⟨hxS, hxT⟩
      have hxS' : x ∈ ⋃₀ FS := by simpa [hSeq] using hxS
      have hxT' : x ∈ ⋃₀ FT := by simpa [hTeq] using hxT
      obtain ⟨C1, hC1, hx1⟩ := hxS'
      obtain ⟨C2, hC2, hx2⟩ := hxT'
      exact ⟨C1 ∩ C2, ⟨C1, hC1, C2, hC2, rfl, ⟨x, hx1, hx2⟩⟩, ⟨hx1, hx2⟩⟩
    · rintro ⟨C, ⟨C1, hC1, C2, hC2, rfl, _⟩, hx1, hx2⟩
      constructor
      · rw [hSeq]; exact ⟨C1, hC1, hx1⟩
      · rw [hTeq]; exact ⟨C2, hC2, hx2⟩

/-- An `A`-cell is a `B`-cell-complex whenever `A ⊆ B`. -/
lemma isHyperplaneCell_cellComplex_of_subset {A B : Set (Hyperplane E)} {C : Set E}
    (hC : IsHyperplaneCell A C) (hAB : A ⊆ B) :
    IsHyperplaneCellComplex B C := by
  let Diff : Set (Hyperplane E) := B \ A
  let Ts : Set (Set E) :=
    {D | ∃ D0, IsHyperplaneCell Diff D0 ∧ D = D0 ∩ C ∧ (D0 ∩ C).Nonempty}
  have hBeq : A ∪ Diff = B := by
    change A ∪ (B \ A) = B
    exact union_sdiff_cancel hAB
  refine ⟨Ts, ⟨?_, ?_⟩⟩
  · intro D hD
    obtain ⟨D0, hD0, rfl, hne⟩ := hD
    have : IsHyperplaneCell (A ∪ Diff) (C ∩ D0) := by
      rw [isHyperplaneCell_union]
      exact ⟨by simpa [inter_comm] using hne, C, D0, hC, hD0, rfl⟩
    simpa [hBeq, inter_comm] using this
  · ext x
    constructor
    · intro hx
      refine ⟨{y | HyperplaneEquiv Diff x y} ∩ C, ?_, ?_⟩
      · exact ⟨{y | HyperplaneEquiv Diff x y}, ⟨x, rfl⟩, rfl,
          ⟨x, hyperplaneEquiv_refl Diff x, hx⟩⟩
      · exact ⟨hyperplaneEquiv_refl Diff x, hx⟩
    · intro ⟨D, hD, hxD⟩
      obtain ⟨_, _, rfl, _⟩ := hD
      exact hxD.2

/-- Cell complexes are monotonic in the arrangement. -/
lemma isHyperplaneCellComplex_mono {A B : Set (Hyperplane E)} {S : Set E}
    (hS : IsHyperplaneCellComplex A S) (hAB : A ⊆ B) :
    IsHyperplaneCellComplex B S := by
  obtain ⟨Cs, hcells, rfl⟩ := hS
  exact isHyperplaneCellComplex_sUnion fun C hC =>
    isHyperplaneCell_cellComplex_of_subset (hcells C hC) hAB

/-- A cell meets a cell complex iff it is contained in it. -/
lemma cell_subset_cellcomplex {A : Set (Hyperplane E)} {C S : Set E}
    (hC : IsHyperplaneCell A C) (hS : IsHyperplaneCellComplex A S) :
    C ⊆ S ↔ (C ∩ S).Nonempty := by
  obtain ⟨Ts, hcells, rfl⟩ := hS
  constructor
  · intro hsub
    obtain ⟨x, hx⟩ := nonempty_isHyperplaneCell hC
    exact ⟨x, hx, hsub hx⟩
  · intro ⟨x, hxC, hxS⟩
    obtain ⟨C', hC', hxC'⟩ := hxS
    have hEq : C = C' := by
      by_contra hne
      have hd : Disjoint C C' := disjoint_isHyperplaneCell hC (hcells C' hC') hne
      exact (disjoint_left.mp hd) hxC hxC'
    intro y hy
    exact ⟨C', hC', hEq ▸ hy⟩


/-! ### Complements and differences of cell complexes -/

/-- Complement of a single cell is a cell complex. -/
lemma isHyperplaneCellComplex_compl_cell {A : Set (Hyperplane E)} {C : Set E}
    (hC : IsHyperplaneCell A C) :
    IsHyperplaneCellComplex A (Cᶜ : Set E) := by
  refine ⟨{D | IsHyperplaneCell A D ∧ D ≠ C}, ⟨fun D hD => hD.1, ?_⟩⟩
  ext x
  constructor
  · intro hx
    refine ⟨{y | HyperplaneEquiv A x y}, ⟨⟨x, rfl⟩, ?_⟩, hyperplaneEquiv_refl A x⟩
    intro hEq
    exact hx (by rw [← hEq]; exact hyperplaneEquiv_refl A x)
  · intro ⟨D, ⟨hD, hne⟩, hxD⟩ hxC
    exact (disjoint_left.mp (disjoint_isHyperplaneCell hD hC hne)) hxD hxC

/-- Complement of a cell complex is a cell complex.
Isabelle: `hyperplane_cellcomplex_Compl`. -/
lemma isHyperplaneCellComplex_compl {A : Set (Hyperplane E)} {S : Set E}
    (hS : IsHyperplaneCellComplex A S) :
    IsHyperplaneCellComplex A (Sᶜ : Set E) := by
  refine ⟨{D | IsHyperplaneCell A D ∧ Disjoint D S}, ⟨fun D hD => hD.1, ?_⟩⟩
  ext x
  constructor
  · intro hx
    refine ⟨{y | HyperplaneEquiv A x y}, ⟨⟨x, rfl⟩, ?_⟩, hyperplaneEquiv_refl A x⟩
    refine Set.disjoint_left.mpr ?_
    intro y hyA hyS
    have hmeet : ({y | HyperplaneEquiv A x y} ∩ S).Nonempty := ⟨y, hyA, hyS⟩
    have hsub : {y | HyperplaneEquiv A x y} ⊆ S :=
      (cell_subset_cellcomplex ⟨x, rfl⟩ hS).mpr hmeet
    exact hx (hsub (hyperplaneEquiv_refl A x))
  · intro ⟨D, ⟨_hD, hd⟩, hxD⟩ hxS
    exact (Set.disjoint_left.mp hd) hxD hxS

/-- Difference of cell complexes is a cell complex.
Isabelle: `hyperplane_cellcomplex_diff`. -/
lemma isHyperplaneCellComplex_diff {A : Set (Hyperplane E)} {S T : Set E}
    (hS : IsHyperplaneCellComplex A S) (hT : IsHyperplaneCellComplex A T) :
    IsHyperplaneCellComplex A (S \ T) := by
  simpa [Set.sdiff_eq] using
    isHyperplaneCellComplex_inter hS (isHyperplaneCellComplex_compl hT)

/-- Finite intersection of cell complexes (by induction on a finset). -/
lemma isHyperplaneCellComplex_finset_inf {A : Set (Hyperplane E)}
    (Ss : Finset (Set E))
    (h : ∀ S ∈ Ss, IsHyperplaneCellComplex A S) :
    IsHyperplaneCellComplex A (Ss.inf id) := by
  classical
  induction Ss using Finset.induction_on with
  | empty =>
    change IsHyperplaneCellComplex A ⊤
    simpa using isHyperplaneCellComplex_univ A
  | insert S Ss hSmem ih =>
    rw [Finset.inf_insert]
    exact isHyperplaneCellComplex_inter
      (h S (Finset.mem_insert_self _ _))
      (ih fun T hT => h T (Finset.mem_insert_of_mem hT))

/-- Finite union of cell complexes (by induction on a finset). -/
lemma isHyperplaneCellComplex_finset_sup {A : Set (Hyperplane E)}
    (Ss : Finset (Set E))
    (h : ∀ S ∈ Ss, IsHyperplaneCellComplex A S) :
    IsHyperplaneCellComplex A (Ss.sup id) := by
  classical
  induction Ss using Finset.induction_on with
  | empty =>
    change IsHyperplaneCellComplex A ⊥
    simpa using isHyperplaneCellComplex_empty A
  | insert S Ss hSmem ih =>
    rw [Finset.sup_insert]
    exact isHyperplaneCellComplex_union
      (h S (Finset.mem_insert_self _ _))
      (ih fun T hT => h T (Finset.mem_insert_of_mem hT))

/-- Indexed finite union of cell complexes. -/
lemma isHyperplaneCellComplex_biUnion_finset {ι : Type*} {A : Set (Hyperplane E)}
    (s : Finset ι) (S : ι → Set E)
    (h : ∀ i ∈ s, IsHyperplaneCellComplex A (S i)) :
    IsHyperplaneCellComplex A (⋃ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isHyperplaneCellComplex_empty A
  | insert i s hi ih =>
    have hEq : (⋃ j ∈ insert i s, S j) = S i ∪ ⋃ j ∈ s, S j := by
      ext x; simp [Finset.mem_insert]
    rw [hEq]
    exact isHyperplaneCellComplex_union
      (h i (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- Indexed finite intersection of cell complexes. -/
lemma isHyperplaneCellComplex_biInter_finset {ι : Type*} {A : Set (Hyperplane E)}
    (s : Finset ι) (S : ι → Set E)
    (h : ∀ i ∈ s, IsHyperplaneCellComplex A (S i)) :
    IsHyperplaneCellComplex A (⋂ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isHyperplaneCellComplex_univ A
  | insert i s hi ih =>
    have hEq : (⋂ j ∈ insert i s, S j) = S i ∩ ⋂ j ∈ s, S j := by
      ext x; simp [Finset.mem_insert]
    rw [hEq]
    exact isHyperplaneCellComplex_inter
      (h i (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end EulersGem

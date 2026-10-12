/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.AffDim
import EulersGem.Hyperplane
import EulersGem.CellGeometry
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Combinatorial Euler characteristic of a hyperplane cell complex

Lean port of Paulson AFP `Euler_characteristic`:

```
Euler_characteristic A S = ∑_{C cell of A, C ⊆ S} (-1)^{affDim C}
```

Plus additivity over disjoint cell complexes, evaluation on the empty arrangement,
and scaffolding toward **invariance under refining arrangements**. Geometric
substrate for the insert/cutting lemma lives in `EulersGem.CellGeometry`
(open∩affine, relative interior, halfspace affDim preservation).
-/

open scoped BigOperators RealInnerProductSpace
open Classical Set Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace EulersGem

/-- Sign of a cell in the combinatorial Euler sum: `(-1)^{affDim C}`. -/
noncomputable def cellSign (C : Set E) : ℤ :=
  (-1 : ℤ) ^ (affDim C).toNat

/-- Combinatorial Euler characteristic of `S` relative to arrangement `A`.
Isabelle: `Euler_characteristic`. Returns `0` if there are infinitely many cells
(Paulson always assumes `finite A`). -/
noncomputable def eulerCharacteristic (A : Set (Hyperplane E)) (S : Set E) : ℤ :=
  if h : {C : Set E | IsHyperplaneCell A C ∧ C ⊆ S}.Finite then
    ∑ C ∈ h.toFinset, cellSign C
  else
    0

lemma eulerCharacteristic_of_finite {A : Set (Hyperplane E)} {S : Set E}
    (h : {C : Set E | IsHyperplaneCell A C ∧ C ⊆ S}.Finite) :
    eulerCharacteristic A S = ∑ C ∈ h.toFinset, cellSign C := by
  simp [eulerCharacteristic, h]

lemma eulerCharacteristic_eq_sum {A : Set (Hyperplane E)} {S : Set E}
    (hA : A.Finite) :
    eulerCharacteristic A S =
      ∑ C ∈ (finite_isHyperplaneCell_restrict hA (fun C => C ⊆ S)).toFinset, cellSign C :=
  eulerCharacteristic_of_finite _

@[simp] lemma eulerCharacteristic_empty (A : Set (Hyperplane E)) :
    eulerCharacteristic A (∅ : Set E) = 0 := by
  unfold eulerCharacteristic
  split_ifs with h
  · have hempty : h.toFinset = ∅ := by
      ext C
      simp only [Finite.mem_toFinset, mem_ofPred_eq, Finset.notMem_empty, iff_false]
      intro ⟨hC, hsub⟩
      obtain ⟨x, hx⟩ := nonempty_isHyperplaneCell hC
      exact hsub hx
    rw [hempty, Finset.sum_empty]
  · rfl

/-- The cells of `A` contained in a cell `C` are exactly `{C}`. -/
lemma cells_subset_cell {A : Set (Hyperplane E)} {C : Set E}
    (hC : IsHyperplaneCell A C) :
    {D : Set E | IsHyperplaneCell A D ∧ D ⊆ C} = {C} := by
  ext D
  simp only [mem_ofPred_eq, mem_singleton_iff]
  constructor
  · intro ⟨hD, hsub⟩
    by_contra hne
    obtain ⟨x, hx⟩ := nonempty_isHyperplaneCell hD
    exact (disjoint_left.mp (disjoint_isHyperplaneCell hD hC hne)) hx (hsub hx)
  · rintro rfl
    exact ⟨hC, Subset.rfl⟩

/-- Euler characteristic of a single cell is its sign. Isabelle: `Euler_characteristic_cell`. -/
lemma eulerCharacteristic_cell {A : Set (Hyperplane E)} {C : Set E}
    (hA : A.Finite) (hC : IsHyperplaneCell A C) :
    eulerCharacteristic A C = cellSign C := by
  have hfin := finite_isHyperplaneCell_restrict hA (fun D => D ⊆ C)
  rw [eulerCharacteristic_of_finite hfin]
  have hset := cells_subset_cell hC
  have : hfin.toFinset = ({C} : Finset (Set E)) := by
    ext D
    simp [hset]
  simp [this]

/-- Cells contained in a union of `A`-cells are exactly those cells. -/
lemma cells_subset_sUnion {A : Set (Hyperplane E)} {Cs : Set (Set E)}
    (hCs : ∀ C ∈ Cs, IsHyperplaneCell A C) :
    {D : Set E | IsHyperplaneCell A D ∧ D ⊆ ⋃₀ Cs} = Cs := by
  ext D
  simp only [mem_ofPred_eq]
  constructor
  · intro ⟨hD, hsub⟩
    obtain ⟨x, hx⟩ := nonempty_isHyperplaneCell hD
    obtain ⟨C, hC, hxC⟩ := hsub hx
    have hEq : D = C := by
      by_contra hne
      exact (disjoint_left.mp (disjoint_isHyperplaneCell hD (hCs C hC) hne)) hx hxC
    rwa [hEq]
  · intro hD
    exact ⟨hCs D hD, subset_sUnion_of_mem hD⟩

/-- Euler characteristic of a union of cells is the sum of their signs.
Isabelle: `Euler_characteristic_cell_Union`. -/
lemma eulerCharacteristic_cell_sUnion {A : Set (Hyperplane E)} {Cs : Set (Set E)}
    (hA : A.Finite) (hCs : ∀ C ∈ Cs, IsHyperplaneCell A C) :
    eulerCharacteristic A (⋃₀ Cs) =
      ∑ C ∈ (show Cs.Finite from
        (finite_isHyperplaneCell hA).subset fun C hC => hCs C hC).toFinset,
        cellSign C := by
  have hfinCs : Cs.Finite :=
    (finite_isHyperplaneCell hA).subset fun C hC => hCs C hC
  have hfin := finite_isHyperplaneCell_restrict hA (fun D => D ⊆ ⋃₀ Cs)
  rw [eulerCharacteristic_of_finite hfin]
  have hset := cells_subset_sUnion hCs
  congr 1
  ext D
  simp [hset]

/-- Additivity for a disjoint union of two cell complexes.
Isabelle: `Euler_characteristic_cellcomplex_Un`. -/
lemma eulerCharacteristic_cellcomplex_union {A : Set (Hyperplane E)} {S T : Set E}
    (hA : A.Finite) (hS : IsHyperplaneCellComplex A S) (hT : IsHyperplaneCellComplex A T)
    (hd : Disjoint S T) :
    eulerCharacteristic A (S ∪ T) =
      eulerCharacteristic A S + eulerCharacteristic A T := by
  have hfinST := finite_isHyperplaneCell_restrict hA (fun C => C ⊆ S ∪ T)
  have hfinS := finite_isHyperplaneCell_restrict hA (fun C => C ⊆ S)
  have hfinT := finite_isHyperplaneCell_restrict hA (fun C => C ⊆ T)
  rw [eulerCharacteristic_of_finite hfinST, eulerCharacteristic_of_finite hfinS,
    eulerCharacteristic_of_finite hfinT]
  have hEq : {C : Set E | IsHyperplaneCell A C ∧ C ⊆ S ∪ T} =
      {C | IsHyperplaneCell A C ∧ C ⊆ S} ∪ {C | IsHyperplaneCell A C ∧ C ⊆ T} := by
    ext C
    simp only [mem_union, mem_ofPred_eq]
    constructor
    · intro ⟨hC, hsub⟩
      -- C meets S or T; by cell_subset_cellcomplex it is contained in that side
      by_cases hCS : (C ∩ S).Nonempty
      · have : C ⊆ S := (cell_subset_cellcomplex hC hS).mpr hCS
        exact Or.inl ⟨hC, this⟩
      · have hCT : (C ∩ T).Nonempty := by
          obtain ⟨x, hx⟩ := nonempty_isHyperplaneCell hC
          have : x ∈ S ∨ x ∈ T := hsub hx
          cases this with
          | inl hxS => exact absurd ⟨x, hx, hxS⟩ hCS
          | inr hxT => exact ⟨x, hx, hxT⟩
        exact Or.inr ⟨hC, (cell_subset_cellcomplex hC hT).mpr hCT⟩
    · rintro (⟨hC, hS'⟩ | ⟨hC, hT'⟩)
      · exact ⟨hC, hS'.trans subset_union_left⟩
      · exact ⟨hC, hT'.trans subset_union_right⟩
  have hdisj' :
      Disjoint {C : Set E | IsHyperplaneCell A C ∧ C ⊆ S}
        {C | IsHyperplaneCell A C ∧ C ⊆ T} := by
    refine Set.disjoint_left.mpr ?_
    intro C ⟨hC, hCS⟩ ⟨_, hCT⟩
    obtain ⟨x, hx⟩ := nonempty_isHyperplaneCell hC
    exact (Set.disjoint_left.mp hd) (hCS hx) (hCT hx)
  have hfin_eq :
      hfinST.toFinset = hfinS.toFinset ∪ hfinT.toFinset := by
    ext C
    simp only [Finite.mem_toFinset, Finset.mem_union]
    simpa [Set.mem_union] using (Set.ext_iff.mp hEq C)
  have hdisjF : Disjoint hfinS.toFinset hfinT.toFinset := by
    refine Finset.disjoint_left.mpr ?_
    intro C hS' hT'
    have hS'' : C ∈ {C : Set E | IsHyperplaneCell A C ∧ C ⊆ S} :=
      (Finite.mem_toFinset _).mp hS'
    have hT'' : C ∈ {C : Set E | IsHyperplaneCell A C ∧ C ⊆ T} :=
      (Finite.mem_toFinset _).mp hT'
    exact (Set.disjoint_left.mp hdisj') hS'' hT''
  rw [hfin_eq, Finset.sum_union hdisjF]

/-- Empty arrangement: the only cell is `univ`, so Euler char of `univ` is
`(-1)^{finrank}`. -/
lemma eulerCharacteristic_empty_arrangement_univ
    [FiniteDimensional ℝ E] [Nonempty E] :
    eulerCharacteristic (∅ : Set (Hyperplane E)) (univ : Set E) =
      (-1 : ℤ) ^ Module.finrank ℝ E := by
  have hA : (∅ : Set (Hyperplane E)).Finite := finite_empty
  have hC : IsHyperplaneCell (∅ : Set (Hyperplane E)) (univ : Set E) :=
    (isHyperplaneCell_empty_arrangement univ).mpr rfl
  rw [eulerCharacteristic_cell hA hC, cellSign, affDim_univ]
  simp

/-- Trivial invariance: same arrangement. -/
lemma eulerCharacteristic_invariant_refl {A : Set (Hyperplane E)} {S : Set E} :
    eulerCharacteristic A S = eulerCharacteristic A S :=
  rfl

/-- If `A ⊆ B` and every `A`-cell inside `S` remains an `A`-cell that is also a
`B`-cell (i.e. refining does not split those cells), Euler chars agree.
Special case of refinement invariance when the new hyperplanes do not cut `S`. -/
lemma eulerCharacteristic_eq_of_same_cells {A B : Set (Hyperplane E)} {S : Set E}
    (hA : A.Finite) (hB : B.Finite)
    (hEq : {C : Set E | IsHyperplaneCell A C ∧ C ⊆ S} =
           {C : Set E | IsHyperplaneCell B C ∧ C ⊆ S}) :
    eulerCharacteristic A S = eulerCharacteristic B S := by
  rw [eulerCharacteristic_eq_sum hA, eulerCharacteristic_eq_sum hB]
  congr 1
  ext C
  simp only [Finite.mem_toFinset]
  change (IsHyperplaneCell A C ∧ C ⊆ S) ↔ (IsHyperplaneCell B C ∧ C ⊆ S)
  simpa using (Set.ext_iff.mp hEq C)

/-- Refinement invariance when `A = B` as sets of hyperplanes (finite). -/
lemma eulerCharacteristic_invariant_of_eq {A B : Set (Hyperplane E)} {S : Set E}
    (_hA : A.Finite) (_hB : B.Finite) (hEq : A = B) :
    eulerCharacteristic A S = eulerCharacteristic B S := by
  subst hEq
  rfl


/-! ### Toward refinement invariance (insert one hyperplane) -/

lemma cellSign_cell_inter_halfSpace_lt {A : Set (Hyperplane E)} {C : Set E}
    (hA : A.Finite) (hC : IsHyperplaneCell A C) (a : E) (b : ℝ)
    (hne : (C ∩ {x | ⟪a, x⟫ < b}).Nonempty) :
    cellSign (C ∩ {x | ⟪a, x⟫ < b}) = cellSign C := by
  simp only [cellSign, affDim_cell_inter_halfSpace_lt hA hC a b hne]

lemma cellSign_cell_inter_halfSpace_gt {A : Set (Hyperplane E)} {C : Set E}
    (hA : A.Finite) (hC : IsHyperplaneCell A C) (a : E) (b : ℝ)
    (hne : (C ∩ {x | b < ⟪a, x⟫}).Nonempty) :
    cellSign (C ∩ {x | b < ⟪a, x⟫}) = cellSign C := by
  simp only [cellSign, affDim_cell_inter_halfSpace_gt hA hC a b hne]

/-- If every `A`-cell inside `S` remains a cell of `insert h A`, Euler chars agree.
Special case of insert when the new hyperplane does not cut any cell of `S`. -/
lemma eulerCharacteristic_insert_of_cells_preserved {A : Set (Hyperplane E)}
    {h : Hyperplane E} {S : Set E}
    (hA : A.Finite)
    (hPres : {C : Set E | IsHyperplaneCell A C ∧ C ⊆ S} =
             {C : Set E | IsHyperplaneCell (insert h A) C ∧ C ⊆ S}) :
    eulerCharacteristic (insert h A) S = eulerCharacteristic A S := by
  have hB : (insert h A).Finite := hA.insert _
  exact eulerCharacteristic_eq_of_same_cells hB hA hPres.symm

/-- Inserting a hyperplane already in the arrangement does nothing. -/
lemma eulerCharacteristic_insert_mem {A : Set (Hyperplane E)} {h : Hyperplane E}
    {S : Set E} (_hA : A.Finite) (hh : h ∈ A) :
    eulerCharacteristic (insert h A) S = eulerCharacteristic A S := by
  have : insert h A = A := insert_eq_of_mem hh
  simp [this]

/-- Degenerate hyperplane `(0, b)` does not refine the arrangement's cells
(singleton cell is `univ`), so Euler char is unchanged on any cell complex. -/
lemma eulerCharacteristic_insert_zero {A : Set (Hyperplane E)} {b : ℝ} {S : Set E}
    (hA : A.Finite) (_hS : IsHyperplaneCellComplex A S) :
    eulerCharacteristic (insert ((0 : E), b) A) S = eulerCharacteristic A S := by
  -- Cells of insert = cells of A, via union with degenerate singleton {univ}
  -- Use: insert (0,b) A = {(0,b)} ∪ A, and cells of {(0,b)} is {univ}
  refine eulerCharacteristic_insert_of_cells_preserved hA ?_
  ext C
  constructor
  · intro ⟨hC, hsub⟩
    -- An A-cell is an (insert)-cell-complex; need it to be a single cell
    -- When the new hyperplane is degenerate, HyperplaneEquiv is unchanged
    have hEq : HyperplaneEquiv (insert ((0 : E), b) A) = HyperplaneEquiv A := by
      ext x y
      simp only [HyperplaneEquiv, mem_insert_iff]
      constructor
      · intro h hp hpA
        exact h hp (Or.inr hpA)
      · intro h hp hpA
        rcases hpA with rfl | hpA
        · -- side of (0,b) is constant
          simp [hyperplaneSide, inner_zero_left]
        · exact h hp hpA
    -- So cells coincide
    obtain ⟨x, rfl⟩ := hC
    refine ⟨⟨x, ?_⟩, hsub⟩
    ext y
    simp only [mem_ofPred_eq]
    exact Iff.of_eq (congrFun (congrFun hEq x) y).symm
  · intro ⟨hC, hsub⟩
    obtain ⟨x, rfl⟩ := hC
    refine ⟨⟨x, ?_⟩, hsub⟩
    ext y
    simp only [mem_ofPred_eq]
    have hEq : HyperplaneEquiv (insert ((0 : E), b) A) = HyperplaneEquiv A := by
      ext u v
      simp only [HyperplaneEquiv, mem_insert_iff]
      constructor
      · intro h hp hpA; exact h hp (Or.inr hpA)
      · intro h hp hpA
        rcases hpA with rfl | hpA
        · simp [hyperplaneSide, inner_zero_left]
        · exact h hp hpA
    exact Iff.of_eq (congrFun (congrFun hEq x) y)


/-! ### Cut-into-three sign identity

Paulson cutting arithmetic: a dim-`n` cell split by a hyperplane contributes
`(-1)^{n-1} + 2(-1)^n = (-1)^n`, so the combinatorial Euler characteristic is
unchanged on that cell.
-/

lemma toNat_affDim_sub_one {n : ℤ} (hn : 0 < n) :
    (n - 1).toNat = n.toNat - 1 := by
  have h1le : (1 : ℤ) ≤ n := by omega
  have hn0 : 0 ≤ n := le_of_lt hn
  have hpos : 0 < n.toNat := Nat.pos_of_ne_zero fun hz => by
    have := Int.toNat_eq_zero.mp hz
    omega
  apply Int.ofNat_inj.mp
  have eq1 : ((n - 1).toNat : ℤ) = n - 1 := Int.toNat_sub_of_le h1le
  have eq2 : ((n.toNat - 1 : ℕ) : ℤ) = ↑n.toNat - 1 :=
    Nat.cast_sub (Nat.succ_le_of_lt hpos)
  have eq3 : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
  omega

/-- Sign identity: `(-1)^{n-1} + 2(-1)^n = (-1)^n` for `n > 0`. -/
lemma sign_cut_identity {n : ℤ} (hn : 0 < n) :
    (-1 : ℤ) ^ (n - 1).toNat + 2 * ((-1 : ℤ) ^ n.toNat) =
      (-1 : ℤ) ^ n.toNat := by
  have h1 : (n - 1).toNat = n.toNat - 1 := toNat_affDim_sub_one hn
  have hpos : 0 < n.toNat := Nat.pos_of_ne_zero fun hz => by
    have := Int.toNat_eq_zero.mp hz
    omega
  rw [h1]
  set k := n.toNat - 1
  have hk : n.toNat = k + 1 := by omega
  rw [hk, pow_succ]
  ring

/-- When a cell is properly cut by a hyperplane (all three pieces nonempty), the
three signs sum to the original cell sign. -/
lemma cellSign_cut_into_three [FiniteDimensional ℝ E]
    {A : Set (Hyperplane E)} {C : Set E}
    (hA : A.Finite) (hC : IsHyperplaneCell A C) (a : E) (b : ℝ)
    (hlt : (C ∩ {x | ⟪a, x⟫ < b}).Nonempty)
    (heq : (C ∩ {x | ⟪a, x⟫ = b}).Nonempty)
    (hgt : (C ∩ {x | b < ⟪a, x⟫}).Nonempty) :
    cellSign (C ∩ {x | ⟪a, x⟫ < b}) +
      cellSign (C ∩ {x | ⟪a, x⟫ = b}) +
      cellSign (C ∩ {x | b < ⟪a, x⟫}) =
      cellSign C := by
  have hnot : ¬ C ⊆ {x | ⟪a, x⟫ = b} := by
    intro hsub
    obtain ⟨x, hxC, hxlt⟩ := hlt
    have heq' : ⟪a, x⟫ = b := hsub hxC
    have hlt' : ⟪a, x⟫ < b := hxlt
    linarith
  have hlt' : affDim (C ∩ {x | ⟪a, x⟫ < b}) = affDim C :=
    affDim_cell_inter_halfSpace_lt hA hC a b hlt
  have hgt' : affDim (C ∩ {x | b < ⟪a, x⟫}) = affDim C :=
    affDim_cell_inter_halfSpace_gt hA hC a b hgt
  have hdrop : affDim (C ∩ {x | ⟪a, x⟫ = b}) = affDim C - 1 :=
    affDim_cell_inter_hyperplane hA hC a b heq hnot
  have hn1 : 0 < affDim C := by
    have hslice : 0 ≤ affDim (C ∩ {x | ⟪a, x⟫ = b}) :=
      affDim_nonneg_of_nonempty heq
    omega
  simp only [cellSign, hlt', hgt', hdrop]
  have h := sign_cut_identity (n := affDim C) hn1
  convert h using 1
  ring

/-- Insert-cells inside an `A`-cell are the nonempty intersections with singleton cells. -/
lemma cells_insert_subset_of_cell {A : Set (Hyperplane E)} {a : E} {b : ℝ} {C : Set E}
    (hC : IsHyperplaneCell A C) :
    {D : Set E | IsHyperplaneCell (insert (a, b) A) D ∧ D ⊆ C} =
      {D | ∃ C1, IsHyperplaneCell {(a, b)} C1 ∧ D = C1 ∩ C ∧ (C1 ∩ C).Nonempty} := by
  ext D
  constructor
  · intro ⟨hD, hsub⟩
    have hD' : IsHyperplaneCell ({(a, b)} ∪ A) D := by
      rwa [show insert (a, b) A = {(a, b)} ∪ A from Set.insert_eq _ _] at hD
    obtain ⟨hne, C1, C2, hC1, hC2, rfl⟩ := (isHyperplaneCell_union {(a, b)} A D).mp hD'
    have hEq : C2 = C := by
      by_contra hne'
      obtain ⟨x, hx1, hx2⟩ := hne
      have hxC : x ∈ C := hsub ⟨hx1, hx2⟩
      exact (disjoint_left.mp (disjoint_isHyperplaneCell hC2 hC hne')) hx2 hxC
    subst hEq
    exact ⟨C1, hC1, rfl, hne⟩
  · rintro ⟨C1, hC1, rfl, hne⟩
    refine ⟨?_, inter_subset_right⟩
    have : IsHyperplaneCell ({(a, b)} ∪ A) (C1 ∩ C) := by
      rw [isHyperplaneCell_union]
      exact ⟨hne, C1, C, hC1, hC, rfl⟩
    rwa [show {(a, b)} ∪ A = insert (a, b) A from (Set.insert_eq _ _).symm] at this

/-- If `C` lies in one side of `(a,b)`, then `C` remains a single cell of `insert (a,b) A`. -/
lemma isHyperplaneCell_insert_of_subset_side {A : Set (Hyperplane E)} {a : E} {b : ℝ}
    {C : Set E} (hC : IsHyperplaneCell A C) (ha : a ≠ 0)
    (hside : C ⊆ {x | ⟪a, x⟫ < b} ∨ C ⊆ {x | b < ⟪a, x⟫} ∨ C ⊆ {x | ⟪a, x⟫ = b}) :
    IsHyperplaneCell (insert (a, b) A) C := by
  have hIns : insert (a, b) A = {(a, b)} ∪ A := Set.insert_eq _ _
  rcases hside with h | h | h
  · have hne : ({x | ⟪a, x⟫ < b} ∩ C).Nonempty := by
      obtain ⟨x, hx⟩ := nonempty_isHyperplaneCell hC
      exact ⟨x, h hx, hx⟩
    have : IsHyperplaneCell ({(a, b)} ∪ A) ({x | ⟪a, x⟫ < b} ∩ C) := by
      rw [isHyperplaneCell_union]
      exact ⟨hne, _, _, isHyperplaneCell_eq_halfSpace_lt ha, hC, rfl⟩
    rw [hIns, ← inter_eq_right.mpr h]; exact this
  · have hne : ({x | b < ⟪a, x⟫} ∩ C).Nonempty := by
      obtain ⟨x, hx⟩ := nonempty_isHyperplaneCell hC
      exact ⟨x, h hx, hx⟩
    have : IsHyperplaneCell ({(a, b)} ∪ A) ({x | b < ⟪a, x⟫} ∩ C) := by
      rw [isHyperplaneCell_union]
      exact ⟨hne, _, _, isHyperplaneCell_eq_halfSpace_gt ha, hC, rfl⟩
    rw [hIns, ← inter_eq_right.mpr h]; exact this
  · have hne : ({x | ⟪a, x⟫ = b} ∩ C).Nonempty := by
      obtain ⟨x, hx⟩ := nonempty_isHyperplaneCell hC
      exact ⟨x, h hx, hx⟩
    have : IsHyperplaneCell ({(a, b)} ∪ A) ({x | ⟪a, x⟫ = b} ∩ C) := by
      rw [isHyperplaneCell_union]
      exact ⟨hne, _, _, isHyperplaneCell_eq_hyperplane ha, hC, rfl⟩
    rw [hIns, ← inter_eq_right.mpr h]; exact this

/-- Cells of `insert` inside a one-sided `A`-cell are exactly `{C}`. -/
lemma cells_insert_of_subset_side {A : Set (Hyperplane E)} {a : E} {b : ℝ} {C : Set E}
    (hC : IsHyperplaneCell A C) (ha : a ≠ 0)
    (hside : C ⊆ {x | ⟪a, x⟫ < b} ∨ C ⊆ {x | b < ⟪a, x⟫} ∨ C ⊆ {x | ⟪a, x⟫ = b}) :
    {D : Set E | IsHyperplaneCell (insert (a, b) A) D ∧ D ⊆ C} = {C} := by
  ext D
  constructor
  · intro ⟨hD, hsub⟩
    obtain ⟨C1, hC1, rfl, hne⟩ :=
      (Set.ext_iff.mp (cells_insert_subset_of_cell (a := a) (b := b) hC) D).mp ⟨hD, hsub⟩
    -- C ⊆ C1 because C lies in one side and C1 is that side (or we'd get empty)
    have hCsub : C ⊆ C1 := by
      rcases hside with hs | hs | hs
      · rcases isHyperplaneCell_singleton_cases hC1 with h1 | h1 | h1
        · exact False.elim (by
            obtain ⟨x, hx1, hxC⟩ := hne
            have : ⟪a, x⟫ = b := by simpa [h1] using hx1
            have : ⟪a, x⟫ < b := hs hxC
            linarith)
        · simpa [h1] using hs
        · exact False.elim (by
            obtain ⟨x, hx1, hxC⟩ := hne
            have : b < ⟪a, x⟫ := by simpa [h1] using hx1
            have : ⟪a, x⟫ < b := hs hxC
            linarith)
      · rcases isHyperplaneCell_singleton_cases hC1 with h1 | h1 | h1
        · exact False.elim (by
            obtain ⟨x, hx1, hxC⟩ := hne
            have : ⟪a, x⟫ = b := by simpa [h1] using hx1
            have : b < ⟪a, x⟫ := hs hxC
            linarith)
        · exact False.elim (by
            obtain ⟨x, hx1, hxC⟩ := hne
            have : ⟪a, x⟫ < b := by simpa [h1] using hx1
            have : b < ⟪a, x⟫ := hs hxC
            linarith)
        · simpa [h1] using hs
      · rcases isHyperplaneCell_singleton_cases hC1 with h1 | h1 | h1
        · simpa [h1] using hs
        · exact False.elim (by
            obtain ⟨x, hx1, hxC⟩ := hne
            have : ⟪a, x⟫ < b := by simpa [h1] using hx1
            have : ⟪a, x⟫ = b := hs hxC
            linarith)
        · exact False.elim (by
            obtain ⟨x, hx1, hxC⟩ := hne
            have : b < ⟪a, x⟫ := by simpa [h1] using hx1
            have : ⟪a, x⟫ = b := hs hxC
            linarith)
    simp [inter_eq_right.mpr hCsub]
  · rintro rfl
    exact ⟨isHyperplaneCell_insert_of_subset_side hC ha hside, Subset.rfl⟩

/-- Proper cut: if an `A`-cell is not contained in any singleton side, it meets all three. -/
lemma cell_cut_meets_all_three {A : Set (Hyperplane E)} {C : Set E}
    (hA : A.Finite) (hC : IsHyperplaneCell A C) {a : E} {b : ℝ} (_ha : a ≠ 0)
    (hnot : ¬ (C ⊆ {x | ⟪a, x⟫ < b} ∨ C ⊆ {x | b < ⟪a, x⟫} ∨ C ⊆ {x | ⟪a, x⟫ = b})) :
    (C ∩ {x | ⟪a, x⟫ < b}).Nonempty ∧
      (C ∩ {x | ⟪a, x⟫ = b}).Nonempty ∧
      (C ∩ {x | b < ⟪a, x⟫}).Nonempty := by
  push Not at hnot
  obtain ⟨hnlt, hngt, hneq⟩ := hnot
  have hconvex : Convex ℝ C := isHyperplaneCell_convex hC
  obtain ⟨u, huC, hu⟩ : ∃ u ∈ C, ¬ ⟪a, u⟫ < b := by
    by_contra! h; exact hnlt fun x hx => h x hx
  obtain ⟨v, hvC, hv⟩ : ∃ v ∈ C, ¬ b < ⟪a, v⟫ := by
    by_contra! h; exact hngt fun x hx => h x hx
  -- Meet the hyperplane
  have heqNe : (C ∩ {x | ⟪a, x⟫ = b}).Nonempty := by
    by_cases hu0 : ⟪a, u⟫ = b
    · exact ⟨u, huC, hu0⟩
    · by_cases hv0 : ⟪a, v⟫ = b
      · exact ⟨v, hvC, hv0⟩
      · have hu'' : b < ⟪a, u⟫ := lt_of_le_of_ne (le_of_not_gt (by simpa using hu)) (Ne.symm hu0)
        have hv'' : ⟪a, v⟫ < b := lt_of_le_of_ne (le_of_not_gt (by simpa using hv)) hv0
        have huv : ⟪a, v⟫ < ⟪a, u⟫ := by linarith
        let t : ℝ := (b - ⟪a, v⟫) / (⟪a, u⟫ - ⟪a, v⟫)
        have ht0 : 0 ≤ t := le_of_lt (div_pos (by linarith) (by linarith))
        have ht1 : t ≤ 1 := by
          refine (div_le_one (by linarith)).mpr (by linarith)
        have hw : (1 - t) • v + t • u ∈ C :=
          hconvex hvC huC (sub_nonneg.mpr ht1) ht0 (by ring)
        refine ⟨(1 - t) • v + t • u, hw, ?_⟩
        have hden : ⟪a, u⟫ - ⟪a, v⟫ ≠ 0 := by linarith
        change ⟪a, (1 - t) • v + t • u⟫ = b
        rw [inner_add_right, inner_smul_right, inner_smul_right]
        have hcancel : t * (⟪a, u⟫ - ⟪a, v⟫) = b - ⟪a, v⟫ :=
          div_mul_cancel₀ _ hden
        linear_combination hcancel
  -- Relative openness ⇒ both open halves
  have heqNe' := heqNe
  obtain ⟨U, hU, hCeq⟩ := isHyperplaneCell_isOpen_affineSpan hA hC
  obtain ⟨w, hwC, hw0⟩ := heqNe'
  change ⟪a, w⟫ = b at hw0
  have hwU : w ∈ U := ((hCeq ▸ hwC) : w ∈ U ∩ _).1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU w hwU
  obtain ⟨z, hzC, hzne⟩ : ∃ z ∈ C, ⟪a, z⟫ ≠ b := by
    by_contra! h; exact hneq fun x hx => h x hx
  have hznorm : z ≠ w := fun hzw => hzne (hzw ▸ hw0)
  let δ : ℝ := ε / 2 / ‖z - w‖
  have hδ : 0 < δ := div_pos (by linarith) (norm_pos_iff.mpr (sub_ne_zero.mpr hznorm))
  have hδball : δ * ‖z - w‖ < ε := by
    have hnnz : ‖z - w‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hznorm)
    have : δ * ‖z - w‖ = ε / 2 := by
      simp only [δ, div_mul_cancel₀ _ hnnz]
    linarith
  let ξp : E := AffineMap.lineMap w z δ
  let ξm : E := AffineMap.lineMap w z (-δ)
  have hline : ∀ t : ℝ, AffineMap.lineMap w z t ∈ (affineSpan ℝ C : Set E) := fun t =>
    AffineMap.lineMap_mem _ (subset_affineSpan ℝ C hwC) (subset_affineSpan ℝ C hzC)
  have hξpU : ξp ∈ U := by
    apply hball
    change dist (δ • (z - w) + w) w < ε
    simp [dist_eq_norm, norm_smul, Real.norm_of_nonneg (le_of_lt hδ), hδball]
  have hξmU : ξm ∈ U := by
    apply hball
    change dist ((-δ) • (z - w) + w) w < ε
    simp [dist_eq_norm, norm_smul, norm_neg, Real.norm_of_nonneg (le_of_lt hδ), hδball]
  have hξpC : ξp ∈ C := by
    have : ξp ∈ U ∩ (affineSpan ℝ C : Set E) := ⟨hξpU, hline δ⟩
    rwa [← hCeq] at this
  have hξmC : ξm ∈ C := by
    have : ξm ∈ U ∩ (affineSpan ℝ C : Set E) := ⟨hξmU, hline (-δ)⟩
    rwa [← hCeq] at this
  have hξp_inner : ⟪a, ξp⟫ = b + δ * (⟪a, z⟫ - b) := by
    change ⟪a, δ • (z - w) + w⟫ = _
    rw [inner_add_right, inner_smul_right, inner_sub_right, hw0]
    ring
  have hξm_inner : ⟪a, ξm⟫ = b - δ * (⟪a, z⟫ - b) := by
    change ⟪a, (-δ) • (z - w) + w⟫ = _
    rw [inner_add_right, inner_smul_right, inner_sub_right, hw0]
    ring
  refine ⟨?lt, heqNe, ?gt⟩
  · -- lt nonempty
    by_cases hzpos : b < ⟪a, z⟫
    · -- ξm has smaller inner product
      refine ⟨ξm, hξmC, ?_⟩
      have : ⟪a, ξm⟫ < b := by
        rw [hξm_inner]
        nlinarith [hδ]
      exact this
    · -- ⟪a,z⟫ < b (since ≠)
      have hzneg : ⟪a, z⟫ < b := lt_of_le_of_ne (le_of_not_gt hzpos) hzne
      refine ⟨ξp, hξpC, ?_⟩
      have : ⟪a, ξp⟫ < b := by
        rw [hξp_inner]
        nlinarith [hδ]
      exact this
  · -- gt nonempty
    by_cases hzpos : b < ⟪a, z⟫
    · refine ⟨ξp, hξpC, ?_⟩
      have : b < ⟪a, ξp⟫ := by
        rw [hξp_inner]
        nlinarith [hδ]
      exact this
    · have hzneg : ⟪a, z⟫ < b := lt_of_le_of_ne (le_of_not_gt hzpos) hzne
      refine ⟨ξm, hξmC, ?_⟩
      have : b < ⟪a, ξm⟫ := by
        rw [hξm_inner]
        nlinarith [hδ]
      exact this


/-! ### Inserting one hyperplane and refinement invariance -/

/-- Helper: nonempty of `C ∩ H` gives nonempty of `H ∩ C`. -/
lemma nonempty_inter_comm {α : Type*} {s t : Set α} (h : (s ∩ t).Nonempty) :
    (t ∩ s).Nonempty := by
  simpa [Set.inter_comm] using h

/-- On a single `A`-cell, inserting `(a,b)` leaves the Euler characteristic unchanged. -/
lemma eulerCharacteristic_insert_cell [FiniteDimensional ℝ E]
    {A : Set (Hyperplane E)} {a : E} {b : ℝ} {C : Set E}
    (hA : A.Finite) (hC : IsHyperplaneCell A C) :
    eulerCharacteristic (insert (a, b) A) C = cellSign C := by
  have hB : (insert (a, b) A).Finite := hA.insert _
  by_cases ha : a = 0
  · subst ha
    simpa [eulerCharacteristic_cell hA hC] using
      eulerCharacteristic_insert_zero (A := A) (b := b) (S := C) hA
        (isHyperplaneCell_cellComplex hC)
  · by_cases hside :
        C ⊆ {x | ⟪a, x⟫ < b} ∨ C ⊆ {x | b < ⟪a, x⟫} ∨ C ⊆ {x | ⟪a, x⟫ = b}
    · have hcells := cells_insert_of_subset_side (a := a) (b := b) hC ha hside
      have hfin := finite_isHyperplaneCell_restrict hB (fun D => D ⊆ C)
      rw [eulerCharacteristic_of_finite hfin]
      have hto : hfin.toFinset = {C} := by
        ext D
        simp only [Finite.mem_toFinset, Finset.mem_singleton]
        change (IsHyperplaneCell (insert (a, b) A) D ∧ D ⊆ C) ↔ D = C
        have hmem : (IsHyperplaneCell (insert (a, b) A) D ∧ D ⊆ C) ↔ D ∈ ({C} : Set (Set E)) := by
          rw [← hcells]; rfl
        rw [hmem, Set.mem_singleton_iff]
      simp [hto]
    · obtain ⟨hlt0, heq0, hgt0⟩ := cell_cut_meets_all_three hA hC ha hside
      -- Work with order matching `isHyperplaneCell_union` (singleton ∩ A-cell)
      let Slt : Set E := {x | ⟪a, x⟫ < b} ∩ C
      let Seq : Set E := {x | ⟪a, x⟫ = b} ∩ C
      let Sgt : Set E := {x | b < ⟪a, x⟫} ∩ C
      have hlt : Slt.Nonempty := nonempty_inter_comm hlt0
      have heq : Seq.Nonempty := nonempty_inter_comm heq0
      have hgt : Sgt.Nonempty := nonempty_inter_comm hgt0
      have hIns : insert (a, b) A = {(a, b)} ∪ A := Set.insert_eq _ _
      have hSlt : IsHyperplaneCell (insert (a, b) A) Slt := by
        have : IsHyperplaneCell ({(a, b)} ∪ A) Slt := by
          rw [isHyperplaneCell_union]
          exact ⟨hlt, _, _, isHyperplaneCell_eq_halfSpace_lt ha, hC, rfl⟩
        rwa [← hIns] at this
      have hSeq : IsHyperplaneCell (insert (a, b) A) Seq := by
        have : IsHyperplaneCell ({(a, b)} ∪ A) Seq := by
          rw [isHyperplaneCell_union]
          exact ⟨heq, _, _, isHyperplaneCell_eq_hyperplane ha, hC, rfl⟩
        rwa [← hIns] at this
      have hSgt : IsHyperplaneCell (insert (a, b) A) Sgt := by
        have : IsHyperplaneCell ({(a, b)} ∪ A) Sgt := by
          rw [isHyperplaneCell_union]
          exact ⟨hgt, _, _, isHyperplaneCell_eq_halfSpace_gt ha, hC, rfl⟩
        rwa [← hIns] at this
      have hset :
          {D : Set E | IsHyperplaneCell (insert (a, b) A) D ∧ D ⊆ C} =
            ({Slt, Seq, Sgt} : Set (Set E)) := by
        ext D
        constructor
        · intro ⟨hD, hsub⟩
          obtain ⟨C1, hC1, rfl, _hne⟩ :=
            (Set.ext_iff.mp (cells_insert_subset_of_cell (a := a) (b := b) hC) D).mp
              ⟨hD, hsub⟩
          rcases isHyperplaneCell_singleton_cases hC1 with h1 | h1 | h1
          · refine Or.inr (Or.inl ?_); simp [Seq, h1]
          · refine Or.inl ?_; simp [Slt, h1]
          · refine Or.inr (Or.inr ?_); simp [Sgt, h1]
        · intro hD
          rcases (show D = Slt ∨ D = Seq ∨ D = Sgt by
            simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hD) with rfl | rfl | rfl
          · exact ⟨hSlt, inter_subset_right⟩
          · exact ⟨hSeq, inter_subset_right⟩
          · exact ⟨hSgt, inter_subset_right⟩
      have hne_lt_eq : Slt ≠ Seq := by
        intro h; obtain ⟨x, hxlt, hxC⟩ := hlt
        have hxSeq : x ∈ Seq := by simpa [← h, Slt] using ⟨hxlt, hxC⟩
        have h1 : ⟪a, x⟫ < b := hxlt
        have h2 : ⟪a, x⟫ = b := hxSeq.1
        exact (h1.ne h2).elim
      have hne_lt_gt : Slt ≠ Sgt := by
        intro h; obtain ⟨x, hxlt, hxC⟩ := hlt
        have hxSgt : x ∈ Sgt := by simpa [← h, Slt] using ⟨hxlt, hxC⟩
        have h1 : ⟪a, x⟫ < b := hxlt
        have h2 : b < ⟪a, x⟫ := hxSgt.1
        exact (not_lt_of_gt h2 h1).elim
      have hne_eq_gt : Seq ≠ Sgt := by
        intro h; obtain ⟨x, hxeq, hxC⟩ := heq
        have hxSgt : x ∈ Sgt := by simpa [← h, Seq] using ⟨hxeq, hxC⟩
        have h1 : ⟪a, x⟫ = b := hxeq
        have h2 : b < ⟪a, x⟫ := hxSgt.1
        exact (h2.ne' h1).elim
      have hfin := finite_isHyperplaneCell_restrict hB (fun D => D ⊆ C)
      rw [eulerCharacteristic_of_finite hfin]
      have hto : hfin.toFinset = ({Slt, Seq, Sgt} : Finset (Set E)) := by
        ext D
        simp only [Finite.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
        change (IsHyperplaneCell (insert (a, b) A) D ∧ D ⊆ C) ↔ D = Slt ∨ D = Seq ∨ D = Sgt
        have := Set.ext_iff.mp hset D
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
      have hnotin₁ : Seq ∉ ({Sgt} : Finset (Set E)) := by simp [hne_eq_gt]
      have hnotin₂ : Slt ∉ ({Seq, Sgt} : Finset (Set E)) := by
        simp [hne_lt_eq, hne_lt_gt]
      rw [hto, Finset.sum_insert hnotin₂, Finset.sum_insert hnotin₁, Finset.sum_singleton]
      -- Reorient intersections for cellSign_cut_into_three
      have hlt' : (C ∩ {x | ⟪a, x⟫ < b}).Nonempty := hlt0
      have heq' : (C ∩ {x | ⟪a, x⟫ = b}).Nonempty := heq0
      have hgt' : (C ∩ {x | b < ⟪a, x⟫}).Nonempty := hgt0
      have hEqlt : Slt = C ∩ {x | ⟪a, x⟫ < b} := by simp [Slt, Set.inter_comm]
      have hEqeq : Seq = C ∩ {x | ⟪a, x⟫ = b} := by simp [Seq, Set.inter_comm]
      have hEqgt : Sgt = C ∩ {x | b < ⟪a, x⟫} := by simp [Sgt, Set.inter_comm]
      simp only [hEqlt, hEqeq, hEqgt]
      simpa [add_assoc, add_left_comm, add_comm] using
        cellSign_cut_into_three hA hC a b hlt' heq' hgt'

/-- `Finset.sup id` of sets is their `sUnion`. -/
lemma Finset.sup_id_eq_sUnion {α : Type*} (s : Finset (Set α)) :
    s.sup id = ⋃₀ (s : Set (Set α)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert t s ht ih =>
    simp [Finset.sup_insert, Set.sUnion_insert, ih]

/-- Euler characteristic of a finite pairwise-disjoint union of cell complexes. -/
lemma eulerCharacteristic_cellcomplex_finsetSum {A : Set (Hyperplane E)}
    (hA : A.Finite) (Cs : Finset (Set E))
    (hCs : ∀ C ∈ Cs, IsHyperplaneCellComplex A C)
    (hdisj : ∀ C ∈ Cs, ∀ D ∈ Cs, C ≠ D → Disjoint C D) :
    eulerCharacteristic A (Cs.sup id) = ∑ C ∈ Cs, eulerCharacteristic A C := by
  classical
  induction Cs using Finset.induction_on with
  | empty =>
    simp only [Finset.sup_empty, Finset.sum_empty]
    change eulerCharacteristic A (⊥ : Set E) = 0
    simp [eulerCharacteristic_empty]
  | insert C Cs hCmem ih =>
    rw [Finset.sup_insert, Finset.sum_insert hCmem]
    change eulerCharacteristic A (C ∪ Cs.sup id) =
      eulerCharacteristic A C + ∑ x ∈ Cs, eulerCharacteristic A x
    have hCcx : IsHyperplaneCellComplex A C := hCs C (Finset.mem_insert_self _ _)
    have hRest : IsHyperplaneCellComplex A (Cs.sup id) := by
      rw [Finset.sup_id_eq_sUnion]
      exact isHyperplaneCellComplex_sUnion fun D hD =>
        hCs D (Finset.mem_insert_of_mem (Finset.mem_coe.mp hD))
    have hdisjC : Disjoint C (Cs.sup id) := by
      rw [Finset.sup_id_eq_sUnion, Set.disjoint_sUnion_right]
      intro D hD
      exact hdisj C (Finset.mem_insert_self _ _) D
        (Finset.mem_insert_of_mem (Finset.mem_coe.mp hD))
        (Ne.symm (ne_of_mem_of_not_mem (Finset.mem_coe.mp hD) hCmem))
    rw [eulerCharacteristic_cellcomplex_union hA hCcx hRest hdisjC,
      ih (fun D hD => hCs D (Finset.mem_insert_of_mem hD))
        (fun D hD E hE hne =>
          hdisj D (Finset.mem_insert_of_mem hD) E (Finset.mem_insert_of_mem hE) hne)]

/-- Isabelle: `Euler_characterstic_lemma`. -/
lemma eulerCharacteristic_insert [FiniteDimensional ℝ E]
    {A : Set (Hyperplane E)} {h : Hyperplane E} {S : Set E}
    (hA : A.Finite) (hS : IsHyperplaneCellComplex A S) :
    eulerCharacteristic (insert h A) S = eulerCharacteristic A S := by
  obtain ⟨a, b⟩ := h
  by_cases ha : a = 0
  · subst ha; exact eulerCharacteristic_insert_zero hA hS
  · obtain ⟨Cs, hcells, rfl⟩ := hS
    have hfinCs : Cs.Finite :=
      (finite_isHyperplaneCell hA).subset fun C hC => hcells C hC
    have hsumA :
        eulerCharacteristic A (⋃₀ Cs) =
          ∑ C ∈ hfinCs.toFinset, cellSign C :=
      eulerCharacteristic_cell_sUnion hA hcells
    have hB : (insert (a, b) A).Finite := hA.insert _
    have hCx : ∀ C ∈ hfinCs.toFinset,
        IsHyperplaneCellComplex (insert (a, b) A) C := fun C hC => by
      have hCA : IsHyperplaneCell A C := hcells C (hfinCs.mem_toFinset.mp hC)
      exact isHyperplaneCellComplex_mono (isHyperplaneCell_cellComplex hCA) (subset_insert _ _)
    have hdisj : ∀ C ∈ hfinCs.toFinset, ∀ D ∈ hfinCs.toFinset, C ≠ D → Disjoint C D := by
      intro C hC D hD hne
      exact disjoint_isHyperplaneCell
        (hcells C (hfinCs.mem_toFinset.mp hC))
        (hcells D (hfinCs.mem_toFinset.mp hD)) hne
    have hsup : hfinCs.toFinset.sup id = ⋃₀ Cs := by
      rw [Finset.sup_id_eq_sUnion]
      ext x
      simp only [Set.mem_sUnion, Finset.mem_coe]
      exact ⟨fun ⟨C, hC, hx⟩ => ⟨C, hfinCs.mem_toFinset.mp hC, hx⟩,
        fun ⟨C, hC, hx⟩ => ⟨C, hfinCs.mem_toFinset.mpr hC, hx⟩⟩
    have hsumIns :
        eulerCharacteristic (insert (a, b) A) (⋃₀ Cs) =
          ∑ C ∈ hfinCs.toFinset, cellSign C := by
      have h := eulerCharacteristic_cellcomplex_finsetSum (A := insert (a, b) A)
        hB hfinCs.toFinset hCx hdisj
      rw [← hsup, h]
      refine Finset.sum_congr rfl ?_
      intro C hC
      exact eulerCharacteristic_insert_cell hA (hcells C (hfinCs.mem_toFinset.mp hC))
    exact hsumIns.trans hsumA.symm

/-- Inserting all hyperplanes of a finite set `B`, one by one. -/
lemma eulerCharacteristic_union_right [FiniteDimensional ℝ E]
    {A B : Set (Hyperplane E)} {S : Set E}
    (hA : A.Finite) (hB : B.Finite) (hS : IsHyperplaneCellComplex A S) :
    eulerCharacteristic (A ∪ B) S = eulerCharacteristic A S := by
  have go : ∀ (B : Set (Hyperplane E)) (hB : B.Finite),
      IsHyperplaneCellComplex A S →
        eulerCharacteristic (A ∪ B) S = eulerCharacteristic A S := by
    intro B hB
    refine Set.Finite.induction_on
      (motive := fun B _ =>
        IsHyperplaneCellComplex A S → eulerCharacteristic (A ∪ B) S = eulerCharacteristic A S)
      B hB ?empty ?insert
    · intro _hS; simp
    · intro p B _hpB hB ih hS
      have hEq : A ∪ insert p B = insert p (A ∪ B) := by
        ext; simp only [Set.mem_union, Set.mem_insert_iff]; tauto
      have hAUB : (A ∪ B).Finite := hA.union hB
      have hS' : IsHyperplaneCellComplex (A ∪ B) S :=
        isHyperplaneCellComplex_mono hS Set.subset_union_left
      rw [hEq, eulerCharacteristic_insert hAUB hS', ih hS]
  exact go B hB hS

/-- Isabelle: `Euler_characterstic_invariant`. -/
lemma eulerCharacteristic_invariant [FiniteDimensional ℝ E]
    {A B : Set (Hyperplane E)} {S : Set E}
    (hA : A.Finite) (hB : B.Finite)
    (hAS : IsHyperplaneCellComplex A S) (hBS : IsHyperplaneCellComplex B S) :
    eulerCharacteristic A S = eulerCharacteristic B S := by
  have hAU : eulerCharacteristic (A ∪ B) S = eulerCharacteristic A S :=
    eulerCharacteristic_union_right hA hB hAS
  have hBU : eulerCharacteristic (B ∪ A) S = eulerCharacteristic B S :=
    eulerCharacteristic_union_right hB hA hBS
  rw [Set.union_comm B A] at hBU
  exact hAU.symm.trans hBU

end EulersGem

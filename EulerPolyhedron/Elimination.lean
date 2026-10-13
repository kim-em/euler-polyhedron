/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Codex
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.LinearAlgebra.Pi

import Mathlib.Data.Finset.Order
import Mathlib.Tactic.Linarith

/-!
# Finite elimination of linear inequalities

`IsPolyhedral 𝕜 s` expresses that a set has a finite linear-inequality
presentation. Fourier–Motzkin elimination proves that projecting away one
scalar coordinate, or any finite number of coordinates, preserves this property.
The elimination argument works over every linearly ordered field.

## Main declarations

* `IsPolyhedral`: a finite intersection of affine halfspaces.
* `exists_forall_mul_le_iff`: elimination of one scalar from a finite inequality system.
* `IsPolyhedral.project`: elimination of one coordinate in a module.
* `IsPolyhedral.project_fin`: elimination of finitely many auxiliary coordinates.
-/

@[expose] public section

open Set

namespace EulerPolyhedron

variable {𝕜 E : Type*}

/-- A set has a finite halfspace presentation by linear functionals over `𝕜`. -/
def IsPolyhedral (𝕜 : Type*) [Semiring 𝕜] [LE 𝕜]
    {E : Type*} [AddCommMonoid E] [Module 𝕜 E] (s : Set E) : Prop :=
  ∃ S : Finset ((E →ₗ[𝕜] 𝕜) × 𝕜), s = {x | ∀ q ∈ S, q.1 x ≤ q.2}

section Basic

variable [Semiring 𝕜] [LE 𝕜] [AddCommMonoid E] [Module 𝕜 E]

/-- A single affine halfspace has a finite presentation. -/
theorem IsPolyhedral.halfspace (f : E →ₗ[𝕜] 𝕜) (b : 𝕜) :
    IsPolyhedral 𝕜 {x | f x ≤ b} := by
  classical
  refine ⟨{(f, b)}, ?_⟩
  ext x
  simp

/-- The whole space is the intersection of an empty family of halfspaces. -/
theorem IsPolyhedral.univ : IsPolyhedral 𝕜 (univ : Set E) := by
  refine ⟨∅, ?_⟩
  ext x
  simp

/-- Finite families of linear inequalities are polyhedral. -/
theorem IsPolyhedral.of_finite {ι : Type*} [Finite ι]
    (L : ι → E →ₗ[𝕜] 𝕜) (b : ι → 𝕜) :
    IsPolyhedral 𝕜 {x | ∀ i, L i x ≤ b i} := by
  classical
  let := Fintype.ofFinite ι
  refine ⟨Finset.univ.image (fun i => (L i, b i)), ?_⟩
  ext x
  simp

/-- Linear inverse images preserve finite halfspace presentations. -/
theorem IsPolyhedral.preimage {F : Type*} [AddCommGroup F] [Module 𝕜 F]
    {s : Set E} (hs : IsPolyhedral 𝕜 s) (f : F →ₗ[𝕜] E) :
    IsPolyhedral 𝕜 (f ⁻¹' s) := by
  classical
  obtain ⟨S, rfl⟩ := hs
  refine ⟨S.image (fun q => (q.1.comp f, q.2)), ?_⟩
  ext x
  change (∀ q ∈ S, q.1 (f x) ≤ q.2) ↔ _
  simp only [mem_ofPred_eq, Finset.forall_mem_image, LinearMap.comp_apply]

/-- Intersections preserve finite halfspace presentations. -/
theorem IsPolyhedral.inter {s t : Set E} (hs : IsPolyhedral 𝕜 s) (ht : IsPolyhedral 𝕜 t) :
    IsPolyhedral 𝕜 (s ∩ t) := by
  classical
  obtain ⟨S, rfl⟩ := hs
  obtain ⟨T, rfl⟩ := ht
  refine ⟨S ∪ T, ?_⟩
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq, Finset.forall_mem_union]

/-- Intersections indexed by a finite type preserve finite presentations. -/
theorem IsPolyhedral.iInter {ι : Type*} [Finite ι] {s : ι → Set E}
    (hs : ∀ i, IsPolyhedral 𝕜 (s i)) : IsPolyhedral 𝕜 (⋂ i, s i) := by
  classical
  let := Fintype.ofFinite ι
  choose S hS using hs
  refine ⟨Finset.univ.biUnion S, ?_⟩
  simp_rw [hS]
  ext x
  simp only [mem_iInter, mem_ofPred_eq]
  constructor
  · intro hx q hq
    obtain ⟨i, _, hqi⟩ := Finset.mem_biUnion.mp hq
    exact hx i q hqi
  · intro hx i q hq
    exact hx q (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hq⟩)

end Basic

private theorem finite_between {α : Type*} [LinearOrder α] [Nonempty α]
    (L U : Finset α)
    (h : ∀ l ∈ L, ∀ u ∈ U, l ≤ u) :
    ∃ t : α, (∀ l ∈ L, l ≤ t) ∧ (∀ u ∈ U, t ≤ u) := by
  classical
  induction L using Finset.induction_on with
  | empty =>
    -- A lower bound for the upper constraints starts the induction.
    obtain ⟨t, ht⟩ := Finset.exists_le (α := OrderDual α) U
    exact ⟨t, by simp, ht⟩
  | @insert a L ha ih =>
    obtain ⟨t, htL, htU⟩ := ih (fun l hl => h l (Finset.mem_insert_of_mem hl))
    refine ⟨max a t, ?_, ?_⟩
    · intro l hl
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact le_max_left _ _
      · exact (htL l hl).trans (le_max_right _ _)
    · intro u hu
      exact max_le (h a (Finset.mem_insert_self _ _) u hu) (htU u hu)

section OrderedRing

variable [Ring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

/-- A hyperplane is the intersection of two opposite halfspaces. -/
theorem IsPolyhedral.hyperplane (f : E →ₗ[𝕜] 𝕜) (b : 𝕜) :
    IsPolyhedral 𝕜 {x | f x = b} := by
  convert (IsPolyhedral.halfspace f b).inter (IsPolyhedral.halfspace (-f) (-b)) using 1
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff, LinearMap.neg_apply, neg_le_neg_iff,
    le_antisymm_iff]

end OrderedRing

section Scalar

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Eliminate one unknown over a linearly ordered field from finitely many scalar inequalities. -/
theorem exists_forall_mul_le_iff {ι : Type*} (s : Finset ι) (a b : ι → 𝕜) :
    (∃ t : 𝕜, ∀ i ∈ s, a i * t ≤ b i) ↔
      (∀ i ∈ s, a i = 0 → 0 ≤ b i) ∧
      (∀ i ∈ s, ∀ j ∈ s, a i < 0 → 0 < a j →
        a i * b j ≤ a j * b i) := by
  classical
  constructor
  · rintro ⟨t, ht⟩
    constructor
    · intro i hi hai
      simpa [hai] using ht i hi
    · intro i hi j hj hai haj
      calc
        a i * b j ≤ a i * (a j * t) :=
          mul_le_mul_of_nonpos_left (ht j hj) hai.le
        _ = a j * (a i * t) := mul_left_comm _ _ _
        _ ≤ a j * b i := mul_le_mul_of_nonneg_left (ht i hi) haj.le
  · rintro ⟨hz, hp⟩
    let L := (s.filter fun i => a i < 0).image fun i => b i / a i
    let U := (s.filter fun i => 0 < a i).image fun i => b i / a i
    have hLU : ∀ l ∈ L, ∀ u ∈ U, l ≤ u := by
      intro l hl u hu
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨hi, hai⟩ := Finset.mem_filter.mp hi
      obtain ⟨hj, haj⟩ := Finset.mem_filter.mp hj
      apply (le_div_iff₀ haj).mpr
      rw [div_mul_eq_mul_div]
      apply (div_le_iff_of_neg hai).mpr
      simpa only [mul_comm] using hp i hi j hj hai haj
    obtain ⟨t, htL, htU⟩ := finite_between L U hLU
    refine ⟨t, fun i hi => ?_⟩
    rcases lt_trichotomy (a i) 0 with hai | hai | hai
    · have h := htL (b i / a i) (Finset.mem_image.mpr
        ⟨i, Finset.mem_filter.mpr ⟨hi, hai⟩, rfl⟩)
      simpa [mul_comm] using (div_le_iff_of_neg hai).mp h
    · simpa [hai] using hz i hi hai
    · have h := htU (b i / a i) (Finset.mem_image.mpr
        ⟨i, Finset.mem_filter.mpr ⟨hi, hai⟩, rfl⟩)
      simpa [mul_comm] using (le_div_iff₀ hai).mp h

end Scalar

section Algebra

variable [CommRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

private def tailMap (q : ((𝕜 × E) →ₗ[𝕜] 𝕜) × 𝕜) : (E →ₗ[𝕜] 𝕜) × 𝕜 :=
  (q.1.comp (LinearMap.inr 𝕜 𝕜 E), q.2)

private def eliminatePair (q r : ((𝕜 × E) →ₗ[𝕜] 𝕜) × 𝕜) :
    (E →ₗ[𝕜] 𝕜) × 𝕜 :=
  (r.1 (1, 0) • (tailMap q).1 - q.1 (1, 0) • (tailMap r).1,
    r.1 (1, 0) * q.2 - q.1 (1, 0) * r.2)

private theorem split_apply (f : (𝕜 × E) →ₗ[𝕜] 𝕜) (t : 𝕜) (x : E) :
    f (t, x) = f (1, 0) * t + f (0, x) := by
  have h : (t, x) = t • (1, (0 : E)) + (0, x) := by simp
  rw [h, map_add, map_smul]
  simp [mul_comm]

end Algebra

section Projection

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

/-- The projection of a finite system of inequalities along one scalar coordinate
is another finite system of inequalities. -/
theorem IsPolyhedral.project {s : Set (𝕜 × E)} (hs : IsPolyhedral 𝕜 s) :
    IsPolyhedral 𝕜 {x | ∃ t : 𝕜, (t, x) ∈ s} := by
  classical
  obtain ⟨S, rfl⟩ := hs
  let Z := S.filter fun q => q.1 (1, 0) = 0
  let P := (S ×ˢ S).filter fun qr => qr.1.1 (1, 0) < 0 ∧ 0 < qr.2.1 (1, 0)
  let T := Z.image tailMap ∪ P.image fun qr => eliminatePair qr.1 qr.2
  refine ⟨T, ?_⟩
  ext x
  change (∃ t : 𝕜, ∀ q ∈ S, q.1 (t, x) ≤ q.2) ↔ _
  have hsplit (t : 𝕜) (q : ((𝕜 × E) →ₗ[𝕜] 𝕜) × 𝕜) :
      q.1 (t, x) ≤ q.2 ↔ q.1 (1, 0) * t ≤ q.2 - q.1 (0, x) := by
    rw [split_apply, le_sub_iff_add_le]
  simp_rw [hsplit]
  rw [exists_forall_mul_le_iff]
  have hT : (∀ q ∈ T, q.1 x ≤ q.2) ↔
      (∀ q ∈ S, q.1 (1, 0) = 0 → q.1 (0, x) ≤ q.2) ∧
      (∀ q ∈ S, ∀ r ∈ S, q.1 (1, 0) < 0 → 0 < r.1 (1, 0) →
        r.1 (1, 0) * q.1 (0, x) - q.1 (1, 0) * r.1 (0, x) ≤
          r.1 (1, 0) * q.2 - q.1 (1, 0) * r.2) := by
    constructor
    · intro ht
      constructor
      · intro q hq hz
        have := ht (tailMap q) (Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨hq, hz⟩, rfl⟩))
        simpa [tailMap] using this
      · intro q hq r hr hn hpos
        have := ht (eliminatePair q r) (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨(q, r),
            Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hq, hr⟩, hn, hpos⟩, rfl⟩))
        simpa [eliminatePair, tailMap, LinearMap.smul_apply, smul_eq_mul] using this
    · rintro ⟨hz, hp⟩ q hq
      rcases Finset.mem_union.mp hq with hq | hq
      · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
        obtain ⟨hr, h0⟩ := Finset.mem_filter.mp hr
        simpa [tailMap] using hz r hr h0
      · obtain ⟨⟨r, t⟩, hrt, rfl⟩ := Finset.mem_image.mp hq
        obtain ⟨hrt, hn, hpos⟩ := Finset.mem_filter.mp hrt
        obtain ⟨hr, ht⟩ := Finset.mem_product.mp hrt
        simpa [eliminatePair, tailMap, LinearMap.smul_apply, smul_eq_mul]
          using hp r hr t ht hn hpos
  change _ ↔ ∀ q ∈ T, q.1 x ≤ q.2
  rw [hT]
  constructor
  · rintro ⟨hz, hp⟩
    exact ⟨fun q hq h0 => by linarith [hz q hq h0],
      fun q hq r hr hn hpos => by linarith only [hp q hq r hr hn hpos]⟩
  · rintro ⟨hz, hp⟩
    exact ⟨fun q hq h0 => by linarith [hz q hq h0],
      fun q hq r hr hn hpos => by linarith only [hp q hq r hr hn hpos]⟩

private def consLinear (n : ℕ) :
    (𝕜 × ((Fin n → 𝕜) × E)) →ₗ[𝕜] ((Fin (n + 1) → 𝕜) × E) :=
  ((Fin.consLinearEquiv 𝕜 (fun _ : Fin (n + 1) ↦ 𝕜)).prodCongr
    (LinearEquiv.refl 𝕜 E)).toLinearMap.comp
      (LinearEquiv.prodAssoc 𝕜 𝕜 (Fin n → 𝕜) E).symm.toLinearMap

/-- Eliminate any finite number of auxiliary real coordinates. -/
theorem IsPolyhedral.project_fin (n : ℕ) {s : Set ((Fin n → 𝕜) × E)}
    (hs : IsPolyhedral 𝕜 s) :
    IsPolyhedral 𝕜 {x | ∃ w : Fin n → 𝕜, (w, x) ∈ s} := by
  induction n with
  | zero =>
    let f : E →ₗ[𝕜] ((Fin 0 → 𝕜) × E) := LinearMap.inr 𝕜 (Fin 0 → 𝕜) E
    have h := hs.preimage f
    convert h using 1
    ext x
    constructor
    · rintro ⟨w, hw⟩
      have hw0 : w = 0 := Subsingleton.elim _ _
      simpa [f, hw0] using hw
    · intro hx
      exact ⟨0, hx⟩
  | succ n ih =>
    have h := ih ((hs.preimage (consLinear n)).project)
    convert h using 1
    ext x
    change (∃ w : Fin (n + 1) → 𝕜, (w, x) ∈ s) ↔
      ∃ w : Fin n → 𝕜, ∃ t : 𝕜, (Fin.cons t w, x) ∈ s
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨Fin.tail w, w 0, by simpa only [Fin.cons_self_tail] using hw⟩
    · rintro ⟨w, t, ht⟩
      exact ⟨Fin.cons t w, ht⟩

end Projection

end EulerPolyhedron

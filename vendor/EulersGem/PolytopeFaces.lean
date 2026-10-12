/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.Polytope
import EulersGem.AffDim
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Set.Finite.Powerset

/-!
# Faces of a V-polytope are hulls of their vertices; the face lattice is finite

The classical structure theorem for the face lattice of a polytope:

* `face_eq_convexHull_inter` — a face `F` of `convexHull ℝ V` satisfies
  `F = convexHull ℝ (V ∩ F)`; a face is the hull of the generating points it contains.
* `faces_finite_of_isPolytope` — hence `F ↦ V ∩ F` is injective on faces, so an
  `IsPolytope` has only finitely many faces.
* `facesOfDim_finite_of_isPolytope` — in particular the vertex / edge / 2-face sets
  counted by `euler_relation_convex_3polytope` are finite.

This discharges the face-finiteness hypotheses that `PlatonicOfEuler` would otherwise
have to assume. Everything here is proved from Mathlib convexity (`IsExtreme`,
`convexHull_eq`); nothing is postulated.

The key step (`mem_of_pos_weight`) is the standard argument: if an extreme set contains
a convex combination `∑ wᵢ zᵢ` of points of the ambient set with `w j > 0`, split the
combination as `w j • z j + (1 - w j) • y` and apply extremeness to the open segment
from `z j` to `y`.
-/

open Set
open scoped RealInnerProductSpace

namespace EulersGem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## `affDim` via the direction of the affine span -/

/-- For a nonempty set, `affDim` is the `finrank` of the direction of its affine span. -/
lemma affDim_eq_finrank_direction {s : Set E} (hs : s.Nonempty) :
    affDim s = (Module.finrank ℝ (affineSpan ℝ s).direction : ℤ) := by
  have hspanNe : (affineSpan ℝ s : Set E).Nonempty :=
    (affineSpan_nonempty (k := ℝ) (V := E) (P := E)).mpr hs
  have hneBot : affineSpan ℝ s ≠ ⊥ := (AffineSubspace.nonempty_iff_ne_bot _).mp hspanNe
  have hfd := AffineSubspace.finDim_eq_finrank hneBot
  simp only [affDim]
  cases hmatch : (affineSpan ℝ s).finDim with
  | bot => exact absurd (AffineSubspace.finDim_eq_bot_iff.mp hmatch) hneBot
  | coe n =>
    rw [hmatch] at hfd
    have hn : n = Module.finrank ℝ (affineSpan ℝ s).direction := WithBot.coe_inj.mp hfd
    simp [hn]

/-! ## Positive weights in a convex combination land in an extreme set -/

/-- If `F` is extreme in a convex set `A`, and a convex combination `∑ wᵢ • zᵢ` of points
of `A` lies in `F`, then every point with strictly positive weight lies in `F`. -/
theorem mem_of_pos_weight {A F : Set E} (hFext : IsExtreme ℝ A F) (hA : Convex ℝ A)
    {ι : Type*} [DecidableEq ι] {t : Finset ι} {w : ι → ℝ} {z : ι → E}
    (hw : ∀ i ∈ t, 0 ≤ w i) (hsum : ∑ i ∈ t, w i = 1) (hz : ∀ i ∈ t, z i ∈ A)
    (hx : ∑ i ∈ t, w i • z i ∈ F) {j : ι} (hj : j ∈ t) (hwj : 0 < w j) :
    z j ∈ F := by
  classical
  have hwj1 : w j ≤ 1 := by
    have h := Finset.single_le_sum (f := w) hw hj
    rwa [hsum] at h
  have hsplit : ∑ i ∈ t, w i • z i = w j • z j + ∑ i ∈ t.erase j, w i • z i :=
    (Finset.add_sum_erase t (fun i => w i • z i) hj).symm
  have hrest : ∑ i ∈ t.erase j, w i = 1 - w j := by
    have h := Finset.add_sum_erase t w hj
    rw [hsum] at h
    linarith
  rcases eq_or_lt_of_le hwj1 with hone | hlt
  · -- `w j = 1`: every other weight vanishes, so the combination *is* `z j`
    have hzero : ∀ i ∈ t.erase j, w i = 0 := by
      intro i hi
      have hnn : ∀ k ∈ t.erase j, 0 ≤ w k := fun k hk => hw k (Finset.mem_of_mem_erase hk)
      have hle := Finset.single_le_sum (f := w) hnn hi
      rw [hrest, hone] at hle
      have := hw i (Finset.mem_of_mem_erase hi)
      linarith
    have hz0 : ∑ i ∈ t.erase j, w i • z i = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [hzero i hi, zero_smul]
    rw [hsplit, hz0, add_zero, hone, one_smul] at hx
    exact hx
  · -- `w j < 1`: `x` is interior to the segment from `z j` to the rescaled remainder
    have hcpos : (0 : ℝ) < 1 - w j := by linarith
    set y : E := ∑ i ∈ t.erase j, ((1 - w j)⁻¹ * w i) • z i with hy
    have hyA : y ∈ A := by
      refine hA.sum_mem (fun i hi => ?_) ?_ fun i hi => hz i (Finset.mem_of_mem_erase hi)
      · exact mul_nonneg (inv_nonneg.mpr hcpos.le) (hw i (Finset.mem_of_mem_erase hi))
      · rw [← Finset.mul_sum, hrest, inv_mul_cancel₀ hcpos.ne']
    have hcy : (1 - w j) • y = ∑ i ∈ t.erase j, w i • z i := by
      rw [hy, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul]
      congr 1
      field_simp
    have hseg : ∑ i ∈ t, w i • z i ∈ openSegment ℝ (z j) y :=
      ⟨w j, 1 - w j, hwj, hcpos, by ring, by rw [hcy, hsplit]⟩
    exact hFext.left_mem_of_mem_openSegment (hz j hj) hyA hx hseg

/-! ## A face of a V-polytope is the hull of the generators it contains -/

/-- **Faces of a V-polytope are hulls of their vertices.** If `F` is a face of
`convexHull ℝ V` then `F = convexHull ℝ (V ∩ F)`. -/
theorem face_eq_convexHull_inter {V F : Set E}
    (hF : IsFaceOf (convexHull ℝ V) F) :
    F = convexHull ℝ (V ∩ F) := by
  classical
  refine subset_antisymm ?_ (convexHull_min inter_subset_right hF.convex)
  intro x hxF
  have hxhull : x ∈ convexHull ℝ V := hF.isExtreme.subset hxF
  rw [convexHull_eq] at hxhull
  obtain ⟨ι, t, w, z, hw0, hw1, hzV, hcm⟩ := hxhull
  rw [Finset.centerMass_eq_of_sum_1 _ _ hw1] at hcm
  -- discard the zero weights
  set t' := t.filter fun i => 0 < w i with ht'
  have hsub : t' ⊆ t := Finset.filter_subset _ _
  have hzeroOut : ∀ i ∈ t, i ∉ t' → w i = 0 := by
    intro i hi hni
    have hnot : ¬ 0 < w i := by
      intro hpos
      exact hni (Finset.mem_filter.mpr ⟨hi, hpos⟩)
    have := hw0 i hi
    linarith [not_lt.mp hnot]
  have hsum' : ∑ i ∈ t', w i = 1 := by
    rw [Finset.sum_subset hsub hzeroOut]; exact hw1
  have hcm' : ∑ i ∈ t', w i • z i = x := by
    rw [Finset.sum_subset hsub fun i hi hni => by rw [hzeroOut i hi hni, zero_smul]]
    exact hcm
  -- every surviving generator lies in the face
  have hmem : ∀ j ∈ t', z j ∈ V ∩ F := by
    intro j hj
    refine ⟨hzV j (hsub hj), ?_⟩
    refine mem_of_pos_weight hF.isExtreme (convex_convexHull ℝ V)
      (fun i hi => hw0 i (hsub hi)) hsum'
      (fun i hi => subset_convexHull ℝ V (hzV i (hsub hi))) ?_ hj
      (Finset.mem_filter.mp hj).2
    rw [hcm']; exact hxF
  rw [← hcm']
  exact (convex_convexHull ℝ (V ∩ F)).sum_mem (fun i hi => hw0 i (hsub hi)) hsum'
    fun i hi => subset_convexHull ℝ _ (hmem i hi)


/-! ## Supporting hyperplanes cut out faces

A general tool for computing the face lattice of an explicitly given polytope: the part of
a convex set where a supporting linear functional attains its bound is a face, and for a
V-polytope that face is the hull of the generators attaining the bound.
-/

/-- **A supporting hyperplane cuts out a face.** If `⟪a, ·⟫ ≤ c` on a convex set `A`, then
`{x ∈ A | ⟪a, x⟫ = c}` is a face of `A`. -/
theorem isFaceOf_inter_hyperplane {A : Set E} (hA : Convex ℝ A) {a : E} {c : ℝ}
    (hle : ∀ x ∈ A, ⟪a, x⟫ ≤ c) :
    IsFaceOf A {x ∈ A | ⟪a, x⟫ = c} := by
  refine ⟨⟨fun x hx => hx.1, ?_⟩, ?_⟩
  · intro y hy z hz w hw hseg
    obtain ⟨s, t, hs, ht, hst, hcomb⟩ := hseg
    refine ⟨hy, ?_⟩
    have hsplit : ⟪a, w⟫ = s * ⟪a, y⟫ + t * ⟪a, z⟫ := by
      rw [← hcomb, inner_add_right, inner_smul_right, inner_smul_right]
    have hyc : ⟪a, y⟫ ≤ c := hle y hy
    have hzc : ⟪a, z⟫ ≤ c := hle z hz
    rw [hw.2] at hsplit
    by_contra hne
    have hlt : ⟪a, y⟫ < c := lt_of_le_of_ne hyc hne
    have hsc : s * c + t * c = c := by linear_combination c * hst
    linarith [mul_pos hs (sub_pos.mpr hlt), mul_nonneg ht.le (sub_nonneg.mpr hzc),
      mul_sub s c ⟪a, y⟫, mul_sub t c ⟪a, z⟫]
  · intro x hx y hy s t hs ht hst
    refine ⟨hA hx.1 hy.1 hs ht hst, ?_⟩
    rw [inner_add_right, inner_smul_right, inner_smul_right, hx.2, hy.2]
    linear_combination c * hst

/-- For a V-polytope, a functional bounded on the generators is bounded on the hull. -/
lemma inner_le_of_mem_convexHull {V : Set E} {a : E} {c : ℝ}
    (h : ∀ v ∈ V, ⟪a, v⟫ ≤ c) :
    ∀ x ∈ convexHull ℝ V, ⟪a, x⟫ ≤ c := fun _ hx =>
  convexHull_min (fun v hv => h v hv) (convex_halfSpace_le (isLinearMap_inner a) c) hx

/-- A functional constant on the generators is constant on the hull. -/
lemma inner_eq_of_mem_convexHull {V : Set E} {a : E} {c : ℝ}
    (h : ∀ v ∈ V, ⟪a, v⟫ = c) :
    ∀ x ∈ convexHull ℝ V, ⟪a, x⟫ = c := fun _ hx =>
  convexHull_min (fun v hv => h v hv)
    (convex_hyperplane (f := fun y => ⟪a, y⟫) (isLinearMap_inner a) c) hx

/-- **The supported face of a V-polytope is the hull of the generators it contains.** -/
theorem inter_hyperplane_eq_convexHull_argmax {V : Set E} {a : E} {c : ℝ}
    (hle : ∀ v ∈ V, ⟪a, v⟫ ≤ c) :
    {x ∈ convexHull ℝ V | ⟪a, x⟫ = c} = convexHull ℝ {v ∈ V | ⟪a, v⟫ = c} := by
  classical
  refine subset_antisymm ?_ ?_
  · rintro x ⟨hxhull, hxc⟩
    rw [convexHull_eq] at hxhull
    obtain ⟨ι, t, w, z, hw0, hw1, hzV, hcm⟩ := hxhull
    rw [Finset.centerMass_eq_of_sum_1 _ _ hw1] at hcm
    have hzle : ∀ i ∈ t, ⟪a, z i⟫ ≤ c := fun i hi => hle _ (hzV i hi)
    have hlin : ⟪a, x⟫ = ∑ i ∈ t, w i * ⟪a, z i⟫ := by
      rw [← hcm, inner_sum]
      exact Finset.sum_congr rfl fun i _ => inner_smul_right _ _ _
    have hsum : ∑ i ∈ t, w i * ⟪a, z i⟫ = c := by rw [← hlin, hxc]
    -- a generator with positive weight must attain the bound
    have hattain : ∀ i ∈ t, 0 < w i → ⟪a, z i⟫ = c := by
      intro i hi hwi
      by_contra hne
      have hlt : ⟪a, z i⟫ < c := lt_of_le_of_ne (hzle i hi) hne
      have hstrict : ∑ j ∈ t, w j * ⟪a, z j⟫ < ∑ j ∈ t, w j * c := by
        refine Finset.sum_lt_sum (fun j hj => ?_) ⟨i, hi, ?_⟩
        · exact mul_le_mul_of_nonneg_left (hzle j hj) (hw0 j hj)
        · exact mul_lt_mul_of_pos_left hlt hwi
      rw [hsum, ← Finset.sum_mul, hw1, one_mul] at hstrict
      exact absurd hstrict (lt_irrefl c)
    -- discard the zero weights and rebuild `x`
    set t' := t.filter fun i => 0 < w i with ht'
    have hsub : t' ⊆ t := Finset.filter_subset _ _
    have hzeroOut : ∀ i ∈ t, i ∉ t' → w i = 0 := by
      intro i hi hni
      have hnot : ¬ 0 < w i := fun hpos => hni (Finset.mem_filter.mpr ⟨hi, hpos⟩)
      have := hw0 i hi
      linarith [not_lt.mp hnot]
    have hsum1' : ∑ i ∈ t', w i = 1 := by
      rw [Finset.sum_subset hsub hzeroOut]; exact hw1
    have hcm' : ∑ i ∈ t', w i • z i = x := by
      rw [Finset.sum_subset hsub fun i hi hni => by rw [hzeroOut i hi hni, zero_smul]]
      exact hcm
    rw [← hcm']
    refine (convex_convexHull ℝ _).sum_mem (fun i hi => hw0 i (hsub hi)) hsum1' fun i hi => ?_
    exact subset_convexHull ℝ _
      ⟨hzV i (hsub hi), hattain i (hsub hi) (Finset.mem_filter.mp hi).2⟩
  · refine convexHull_min (fun v hv => ⟨subset_convexHull ℝ V hv.1, hv.2⟩) ?_
    intro x hx y hy s t hs ht hst
    refine ⟨(convex_convexHull ℝ V) hx.1 hy.1 hs ht hst, ?_⟩
    rw [inner_add_right, inner_smul_right, inner_smul_right, hx.2, hy.2]
    linear_combination c * hst

/-- **Face lattice tool for explicit V-polytopes:** the hull of the generators on a
supporting hyperplane is a face. -/
theorem isFaceOf_convexHull_argmax {V : Set E} {a : E} {c : ℝ}
    (hle : ∀ v ∈ V, ⟪a, v⟫ ≤ c) :
    IsFaceOf (convexHull ℝ V) (convexHull ℝ {v ∈ V | ⟪a, v⟫ = c}) := by
  rw [← inter_hyperplane_eq_convexHull_argmax hle]
  exact isFaceOf_inter_hyperplane (convex_convexHull ℝ V) (inner_le_of_mem_convexHull hle)


/-- Counting a decidable subset of a `Fintype` as a `Finset` card, so counts can be decided. -/
lemma ncard_setOf_fintype {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    {x : α | p x}.ncard = ((Finset.univ : Finset α).filter p).card := by
  have h : {x : α | p x} = ↑((Finset.univ : Finset α).filter p) := by
    ext x; simp
  rw [h, Set.ncard_coe_finset]

/-! ## Finiteness of the face lattice -/

/-- **The face lattice of a polytope is finite.** `F ↦ V ∩ F` is injective on faces by
`face_eq_convexHull_inter`, and lands in the (finite) powerset of the generating set. -/
theorem faces_finite_of_isPolytope {p : Set E} (hP : IsPolytope p) :
    {f : Set E | IsFaceOf p f}.Finite := by
  obtain ⟨V, hVfin, rfl⟩ := hP
  refine Set.Finite.of_finite_image (f := fun f => V ∩ f) ?_ ?_
  · refine hVfin.finite_subsets.subset ?_
    rintro s ⟨f, -, rfl⟩
    exact inter_subset_left
  · intro f₁ h₁ f₂ h₂ heq
    have heq' : V ∩ f₁ = V ∩ f₂ := heq
    rw [face_eq_convexHull_inter h₁, face_eq_convexHull_inter h₂, heq']

/-- The faces of a polytope of a given affine dimension form a finite set: exactly the
`V`, `E`, `F` counts of `euler_relation_convex_3polytope`. -/
theorem facesOfDim_finite_of_isPolytope {p : Set E} (hP : IsPolytope p) (d : ℤ) :
    {f : Set E | IsFaceOf p f ∧ affDim f = d}.Finite :=
  (faces_finite_of_isPolytope hP).subset fun _ hf => hf.1

end EulersGem

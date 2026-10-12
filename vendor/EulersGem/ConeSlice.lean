/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.EulerPoincare
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.AffineSpace.Dimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Geometric cone↔slice correspondence (Paulson)

Geometric discharge of `ConeSliceFaceBijection` (Paulson slice lemma):

* `affDim = 0` ⇒ singleton (under `FiniteDimensional`)
* faces of conic sets are conic (`face_of_conic`)
* apex `{0}` is the unique 0-face of `conicHull p` on a height-1 convex slice
* face-lift: `IsFaceOf p F → IsFaceOf (conicHull p) (conicHull F)`
* `affDim (conicHull F) = affDim F + 1` (nonempty height-1 faces)
* homogenization H-rep **equality** (under a height-0 triviality hypothesis, e.g. polytopes)
* height-1 slice of a cone-face is a face of `p`; recover conic face from its slice
* `InjOn conicHull` on height-1 faces; assembled `ConeSliceFaceBijection`
-/

open scoped RealInnerProductSpace
open Classical Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace EulersGem

lemma eq_singleton_of_affDim_eq_zero [FiniteDimensional ℝ E]
    {s : Set E} (h : affDim s = 0) : ∃ a, s = {a} := by
  have hsne : s.Nonempty := by
    by_contra hempty
    have : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    subst this
    simp [affDim_empty] at h
  have hspanNe : (affineSpan ℝ s : Set E).Nonempty :=
    (affineSpan_nonempty (k := ℝ) (V := E) (P := E)).mpr hsne
  have hneBot : affineSpan ℝ s ≠ ⊥ := (AffineSubspace.nonempty_iff_ne_bot _).mp hspanNe
  have hfd : (affineSpan ℝ s).finDim = (0 : WithBot ℕ) := by
    cases hmatch : (affineSpan ℝ s).finDim with
    | bot => exact absurd (AffineSubspace.finDim_eq_bot_iff.mp hmatch) hneBot
    | coe n =>
      simp only [affDim, hmatch] at h
      have : n = 0 := by exact_mod_cast h
      simp [this]
  have : FiniteDimensional ℝ (affineSpan ℝ s).direction := inferInstance
  have hsub : (affineSpan ℝ s : Set E).Subsingleton :=
    (AffineSubspace.finDim_le_zero_iff_subsingleton (s := affineSpan ℝ s)).mp (by simp [hfd])
  obtain ⟨a, ha⟩ := hsne
  refine ⟨a, Subset.antisymm ?_ (singleton_subset_iff.mpr ha)⟩
  intro x hx
  exact hsub (mem_affineSpan ℝ hx) (mem_affineSpan ℝ ha) ▸ rfl

lemma isConic_of_isFaceOf {S F : Set E} (hS : IsConic S) (hF : IsFaceOf S F) :
    IsConic F := by
  intro x hxF c hc
  by_cases hx0 : x = 0
  · subst hx0; simpa using hxF
  · by_cases hc1 : c = 1
    · subst hc1; simpa using hxF
    · obtain ⟨d, e, hd0, he0, hdlt, hegt, hdc⟩ :
          ∃ d e : ℝ, 0 ≤ d ∧ 0 ≤ e ∧ d < 1 ∧ 1 < e ∧ (d = c ∨ e = c) := by
        by_cases hclt : c < 1
        · exact ⟨c, 2, hc, by norm_num, hclt, by norm_num, Or.inl rfl⟩
        · exact ⟨0, c, le_rfl, hc, by norm_num,
            lt_of_le_of_ne (not_lt.mp hclt) (Ne.symm hc1), Or.inr rfl⟩
      have hde : d < e := by rcases hdc with rfl | rfl <;> linarith
      have hxS : x ∈ S := hF.isExtreme.subset hxF
      have hdS : d • x ∈ S := hS hxS d hd0
      have heS : e • x ∈ S := hS hxS e he0
      set a : ℝ := (e - 1) / (e - d)
      set b : ℝ := (1 - d) / (e - d)
      have hden : e - d ≠ 0 := by linarith
      have ha : 0 < a := div_pos (by linarith) (by linarith)
      have hb : 0 < b := div_pos (by linarith) (by linarith)
      have hab : a + b = 1 := by
        dsimp [a, b]
        rw [← add_div, show (e - 1) + (1 - d) = e - d by ring, div_self hden]
      have hcoef : a * d + b * e = 1 := by
        dsimp [a, b]
        have := mul_div_cancel₀ ((e - 1) * d + (1 - d) * e) hden
        -- Direct computation
        field_simp [hden]
        ring
      have hcomb : a • (d • x) + b • (e • x) = x := by
        calc
          a • (d • x) + b • (e • x) = (a * d + b * e) • x := by module
          _ = (1 : ℝ) • x := by rw [hcoef]
          _ = x := one_smul _ _
      have hseg : x ∈ openSegment ℝ (d • x) (e • x) := ⟨a, b, ha, hb, hab, hcomb⟩
      have hdF := hF.isExtreme.left_mem_of_mem_openSegment hdS heS hxF hseg
      have heF := hF.isExtreme.right_mem_of_mem_openSegment hdS heS hxF hseg
      rcases hdc with rfl | rfl
      · exact hdF
      · exact heF

lemma height_pos_of_mem_conicHull {p : Set E} {i : E}
    (hp : ∀ x ∈ p, ⟪i, x⟫ = 1) {y : E}
    (hy : y ∈ conicHull p) (hne : y ≠ 0) : 0 < ⟪i, y⟫ := by
  obtain ⟨c, x, hc, hx, rfl⟩ := hy
  have hcne : c ≠ 0 := fun h => by subst h; exact hne (by simp)
  have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hcne)
  simpa [inner_smul_right, hp x hx] using hcpos

lemma convex_conicHull {s : Set E} (hs : Convex ℝ s) : Convex ℝ (conicHull s) := by
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab
  obtain ⟨c₁, x₁, hc₁, hx₁, rfl⟩ := hy₁
  obtain ⟨c₂, x₂, hc₂, hx₂, rfl⟩ := hy₂
  by_cases hsum : a * c₁ + b * c₂ = 0
  · have ha0 : a * c₁ = 0 := by nlinarith [mul_nonneg ha hc₁, mul_nonneg hb hc₂]
    have hb0 : b * c₂ = 0 := by nlinarith [mul_nonneg ha hc₁, mul_nonneg hb hc₂]
    refine ⟨0, x₁, le_rfl, hx₁, ?_⟩
    simp [smul_smul, ha0, hb0]
  · set t := a * c₁ + b * c₂
    have htpos : 0 < t :=
      lt_of_le_of_ne (add_nonneg (mul_nonneg ha hc₁) (mul_nonneg hb hc₂)) (Ne.symm hsum)
    set w₁ : ℝ := (a * c₁) / t
    set w₂ : ℝ := (b * c₂) / t
    have hw1 : 0 ≤ w₁ := div_nonneg (mul_nonneg ha hc₁) htpos.le
    have hw2 : 0 ≤ w₂ := div_nonneg (mul_nonneg hb hc₂) htpos.le
    have hw12 : w₁ + w₂ = 1 := by
      dsimp [w₁, w₂]
      have ht0 : t ≠ 0 := htpos.ne'
      field_simp [ht0]
      rfl
    have hx : w₁ • x₁ + w₂ • x₂ ∈ s := hs hx₁ hx₂ hw1 hw2 hw12
    refine ⟨t, w₁ • x₁ + w₂ • x₂, htpos.le, hx, ?_⟩
    -- a • (c₁ • x₁) + b • (c₂ • x₂) = t • (w₁ • x₁ + w₂ • x₂)
    dsimp [w₁, w₂]
    have ht0 : t ≠ 0 := htpos.ne'
    simp only [smul_add, smul_smul]
    -- Goal: (a * c₁) • x₁ + (b * c₂) • x₂ = (t * (a * c₁ / t)) • x₁ + (t * (b * c₂ / t)) • x₂
    rw [mul_div_cancel₀ _ ht0, mul_div_cancel₀ _ ht0]

lemma coneSlice_zero_face [FiniteDimensional ℝ E] {p : Set E} {i : E}
    (hp : ∀ x ∈ p, ⟪i, x⟫ = 1) (hne : p.Nonempty) (hConv : Convex ℝ p) :
    {f : Set E | IsFaceOf (conicHull p) f ∧ affDim f = 0} =
      ({({0} : Set E)} : Set (Set E)) :=
  faces_dim_zero_eq_singleton_zero (isConic_conicHull p) (convex_conicHull hConv)
    (zero_mem_conicHull hne)
    (fun _x hx hxne => height_pos_of_mem_conicHull hp hx hxne)
    (fun _f _hf hd => eq_singleton_of_affDim_eq_zero hd)

lemma zero_not_mem_affineSpan_of_height {s : Set E} {i : E}
    (hs : ∀ x ∈ s, ⟪i, x⟫ = 1) :
    (0 : E) ∉ affineSpan ℝ s := by
  intro h0
  have hall : ∀ z, z ∈ affineSpan ℝ s → ⟪i, z⟫ = 1 := by
    intro z hz
    refine affineSpan_induction (k := ℝ) (P := E) (p := fun w => ⟪i, w⟫ = 1) hz
      hs fun c u v w hu hv hw => by
        simp [inner_add_right, inner_smul_right, inner_sub_right, hu, hv, hw]
  have : ⟪i, (0 : E)⟫ = 1 := hall 0 h0
  simp [inner_zero_right] at this

lemma conicHull_subset_homogenized_cone {H : Set (Hyperplane E)} {i : E} {p : Set E}
    (hp : p = ⋂ h ∈ H, closedHalfspace h.1 h.2)
    (hht : ∀ x ∈ p, ⟪i, x⟫ = 1) :
    conicHull p ⊆ ⋂ a ∈ homogenizeNormals H i, closedHalfspace a 0 := by
  intro y hy
  obtain ⟨c, x, hc, hx, rfl⟩ := hy
  refine mem_iInter.mpr fun a => mem_iInter.mpr fun ha => ?_
  unfold homogenizeNormals at ha
  rcases ha with hpos | hneg
  · obtain ⟨h, hh, rfl⟩ := hpos
    have hxH : ⟪h.1, x⟫ ≤ h.2 := by
      exact (mem_iInter.mp ((mem_iInter.mp (hp ▸ hx)) h)) hh
    have hle : ⟪h.1 - h.2 • i, c • x⟫ ≤ 0 := by
      have : ⟪h.1 - h.2 • i, c • x⟫ = c * (⟪h.1, x⟫ - h.2) := by
        simp [inner_sub_left, inner_smul_right, inner_smul_left, hht x hx]
      rw [this]
      exact mul_nonpos_of_nonneg_of_nonpos hc (sub_nonpos.mpr hxH)
    simpa [closedHalfspace] using hle
  · have ha' : a = -i := by simpa using hneg
    subst ha'
    have hle : ⟪(-i), c • x⟫ ≤ 0 := by
      have hrew : ⟪(-i), c • x⟫ = -(c * ⟪i, x⟫) := by
        simp [inner_smul_right, inner_neg_left]
      rw [hrew, hht x hx, mul_one, neg_nonpos]; exact hc
    simpa [closedHalfspace] using hle

lemma isPolyhedralCone_of_conicHull_eq_homogenized {H : Set (Hyperplane E)} {i : E} {p : Set E}
    (hH : H.Finite)
    (heq : conicHull p = ⋂ a ∈ homogenizeNormals H i, closedHalfspace a 0) :
    IsPolyhedralCone (conicHull p) :=
  ⟨homogenizeNormals H i, homogenizeNormals_finite hH i, heq⟩

lemma isFaceOf_slice_of_isFaceOf_conicHull {p G : Set E} {i : E}
    (hht : ∀ x ∈ p, ⟪i, x⟫ = 1)
    (hG : IsFaceOf (conicHull p) G) :
    IsFaceOf p (G ∩ {x : E | ⟪i, x⟫ = 1}) := by
  set F := G ∩ {x : E | ⟪i, x⟫ = 1}
  have hsub : F ⊆ p := by
    intro x hx
    have : x ∈ conicHull p ∩ {y | ⟪i, y⟫ = 1} :=
      ⟨hG.isExtreme.subset hx.1, hx.2⟩
    rwa [conicHull_inter_height_one hht] at this
  refine ⟨⟨hsub, ?_⟩, hG.convex.inter (convex_hyperplane (isLinearMap_inner i) 1)⟩
  intro x hxP y hyP z hzF hzSeg
  exact ⟨hG.isExtreme.left_mem_of_mem_openSegment
    (subset_conicHull p hxP) (subset_conicHull p hyP) hzF.1 hzSeg, hht x hxP⟩

lemma conicHull_inter_height_eq_of_isConic {G : Set E} {i : E}
    (hG : IsConic G)
    (hpos : ∀ x ∈ G, x ≠ 0 → 0 < ⟪i, x⟫)
    (hne_nz : ∃ z ∈ G, z ≠ 0) :
    conicHull (G ∩ {x : E | ⟪i, x⟫ = 1}) = G := by
  apply subset_antisymm
  · rintro _ ⟨c, x, hc, hx, rfl⟩
    exact hG hx.1 c hc
  · intro y hy
    by_cases hy0 : y = 0
    · subst hy0
      obtain ⟨z, hz, hzne⟩ := hne_nz
      have hzpos := hpos z hz hzne
      refine ⟨0, (⟪i, z⟫)⁻¹ • z, le_rfl,
        ⟨hG hz _ (inv_nonneg.mpr hzpos.le), ?_⟩, by simp⟩
      simp [inner_smul_right, inv_mul_cancel₀ hzpos.ne']
    · have hypos := hpos y hy hy0
      refine ⟨⟪i, y⟫, (⟪i, y⟫)⁻¹ • y, hypos.le,
        ⟨hG hy _ (inv_nonneg.mpr hypos.le), ?_⟩, ?_⟩
      · simp [inner_smul_right, inv_mul_cancel₀ hypos.ne']
      · simp [smul_smul, mul_inv_cancel₀ hypos.ne']

lemma injOn_conicHull_faces {p : Set E} {i : E}
    (hht : ∀ F, IsFaceOf p F → ∀ x ∈ F, ⟪i, x⟫ = 1) (d : ℕ) :
    InjOn conicHull {F : Set E | IsFaceOf p F ∧ affDim F = (d : ℤ)} := by
  intro F₁ hF₁ F₂ hF₂ hEq
  have h1 := (conicHull_inter_height_one (hht F₁ hF₁.1)).symm
  have h2 := (conicHull_inter_height_one (hht F₂ hF₂.1)).symm
  calc
    F₁ = conicHull F₁ ∩ {x | ⟪i, x⟫ = 1} := h1
    _ = conicHull F₂ ∩ {x | ⟪i, x⟫ = 1} := by rw [hEq]
    _ = F₂ := h2.symm


/-! ### Height-zero characterisation on conic hulls of height-1 sets -/

lemma eq_zero_of_mem_conicHull_of_height_zero {p : Set E} {i : E} {y : E}
    (hht : ∀ x ∈ p, ⟪i, x⟫ = 1) (hy : y ∈ conicHull p) (hyi : ⟪i, y⟫ = 0) :
    y = 0 := by
  obtain ⟨c, x, hc, hx, rfl⟩ := hy
  have : c * ⟪i, x⟫ = 0 := by simpa [inner_smul_right] using hyi
  have hc0 : c = 0 := by
    rw [hht x hx, mul_one] at this; exact this
  simp [hc0]

lemma height_nonneg_of_mem_conicHull {p : Set E} {i : E} {y : E}
    (hht : ∀ x ∈ p, ⟪i, x⟫ = 1) (hy : y ∈ conicHull p) : 0 ≤ ⟪i, y⟫ := by
  obtain ⟨c, x, hc, hx, rfl⟩ := hy
  simpa [inner_smul_right, hht x hx] using hc

lemma inv_smul_mem_of_mem_conicHull {p : Set E} {i : E} {y : E}
    (hht : ∀ x ∈ p, ⟪i, x⟫ = 1) (hy : y ∈ conicHull p) (hne : y ≠ 0) :
    (⟪i, y⟫)⁻¹ • y ∈ p := by
  obtain ⟨c, x, hc, hx, rfl⟩ := hy
  have hcne : c ≠ 0 := fun h => by subst h; exact hne (by simp)
  have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hcne)
  have hiy : ⟪i, c • x⟫ = c := by simp [inner_smul_right, hht x hx]
  simpa [hiy, smul_smul, inv_mul_cancel₀ hcpos.ne'] using hx

/-! ### Face-lift -/

lemma isFaceOf_conicHull_of_isFaceOf {p F : Set E} {i : E}
    (hht : ∀ x ∈ p, ⟪i, x⟫ = 1) (hF : IsFaceOf p F) :
    IsFaceOf (conicHull p) (conicHull F) := by
  have hFsub : F ⊆ p := isFaceOf_subset hF
  have hhtF : ∀ x ∈ F, ⟪i, x⟫ = 1 := fun x hx => hht x (hFsub hx)
  refine ⟨⟨conicHull_mono hFsub, ?_⟩, convex_conicHull hF.convex⟩
  intro x hxS y hyS z hzG hzSeg
  obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hzSeg
  have hx_h := height_nonneg_of_mem_conicHull hht hxS
  have hy_h := height_nonneg_of_mem_conicHull hht hyS
  by_cases hz0 : z = 0
  · -- Heights sum to 0 ⇒ both endpoints have height 0 ⇒ both are 0 ∈ conicHull F.
    have hz_h : ⟪i, z⟫ = 0 := by simp [hz0]
    have hsum : a * ⟪i, x⟫ + b * ⟪i, y⟫ = 0 := by
      have := congrArg (fun w => ⟪i, w⟫) hcomb
      simpa [inner_add_right, inner_smul_right, hz_h] using this
    have hx0i : ⟪i, x⟫ = 0 := by
      nlinarith [mul_nonneg ha.le hx_h, mul_nonneg hb.le hy_h]
    have hy0i : ⟪i, y⟫ = 0 := by
      nlinarith [mul_nonneg ha.le hx_h, mul_nonneg hb.le hy_h]
    have hx0 : x = 0 := eq_zero_of_mem_conicHull_of_height_zero hht hxS hx0i
    -- Need F nonempty to know 0 ∈ conicHull F; follows from z ∈ conicHull F.
    have hFne : F.Nonempty := by
      obtain ⟨c, w, _, hw, _⟩ := hzG
      exact ⟨w, hw⟩
    exact hx0 ▸ zero_mem_conicHull hFne
  · -- z ≠ 0. If an endpoint is 0, scale the other back into the face-cone.
    by_cases hxeq0 : x = 0
    · -- z = b • y with 0 < b < 1; goal is x ∈ conicHull F and x = 0.
      have hFne : F.Nonempty := by
        obtain ⟨c, w, _, hw, _⟩ := hzG
        exact ⟨w, hw⟩
      exact hxeq0 ▸ zero_mem_conicHull hFne
    · by_cases hyeq0 : y = 0
      · -- y = 0 ⇒ z = a • x ⇒ x = a⁻¹ • z ∈ conicHull F.
        have hx_eq : x = a⁻¹ • z := by
          have : z = a • x := by
            simpa [hyeq0, smul_zero, add_zero] using hcomb.symm
          have ha0 : a ≠ 0 := ha.ne'
          calc
            x = a⁻¹ • (a • x) := by simp [smul_smul, inv_mul_cancel₀ ha0]
            _ = a⁻¹ • z := by rw [← this]
        rw [hx_eq]
        exact (isConic_conicHull F) hzG a⁻¹ (inv_nonneg.mpr ha.le)
      · -- Both endpoints nonzero: reduce to the height-1 slice.
        have hxpos := height_pos_of_mem_conicHull hht hxS hxeq0
        have hypos := height_pos_of_mem_conicHull hht hyS hyeq0
        have hzpos := height_pos_of_mem_conicHull hht
          ((conicHull_mono hFsub) hzG) hz0
        set x' := (⟪i, x⟫)⁻¹ • x
        set y' := (⟪i, y⟫)⁻¹ • y
        set z' := (⟪i, z⟫)⁻¹ • z
        have hx'p : x' ∈ p := inv_smul_mem_of_mem_conicHull hht hxS hxeq0
        have hy'p : y' ∈ p := inv_smul_mem_of_mem_conicHull hht hyS hyeq0
        have hz'F : z' ∈ F := by
          have : z' ∈ conicHull F ∩ {w | ⟪i, w⟫ = 1} := by
            refine ⟨(isConic_conicHull F) hzG _ (inv_nonneg.mpr hzpos.le), ?_⟩
            simp [z', inner_smul_right, inv_mul_cancel₀ hzpos.ne']
          rwa [conicHull_inter_height_one hhtF] at this
        have hiz : ⟪i, z⟫ = a * ⟪i, x⟫ + b * ⟪i, y⟫ := by
          have := congrArg (fun w => ⟪i, w⟫) hcomb.symm
          simpa [inner_add_right, inner_smul_right] using this
        set a' : ℝ := a * ⟪i, x⟫ / ⟪i, z⟫
        set b' : ℝ := b * ⟪i, y⟫ / ⟪i, z⟫
        have ha' : 0 < a' := div_pos (mul_pos ha hxpos) hzpos
        have hb' : 0 < b' := div_pos (mul_pos hb hypos) hzpos
        have hab' : a' + b' = 1 := by
          dsimp [a', b']
          rw [← add_div, ← hiz, div_self hzpos.ne']
        have hcomb' : a' • x' + b' • y' = z' := by
          dsimp [a', b', x', y', z']
          calc
            (a * ⟪i, x⟫ / ⟪i, z⟫) • ((⟪i, x⟫)⁻¹ • x) +
                (b * ⟪i, y⟫ / ⟪i, z⟫) • ((⟪i, y⟫)⁻¹ • y) =
              ((a * ⟪i, x⟫ / ⟪i, z⟫) * (⟪i, x⟫)⁻¹) • x +
                ((b * ⟪i, y⟫ / ⟪i, z⟫) * (⟪i, y⟫)⁻¹) • y := by
              simp only [smul_smul]
            _ = (a / ⟪i, z⟫) • x + (b / ⟪i, z⟫) • y := by
              field_simp [hxpos.ne', hypos.ne']
            _ = (⟪i, z⟫)⁻¹ • (a • x + b • y) := by
              simp [smul_add, smul_smul, div_eq_inv_mul, mul_comm]
            _ = (⟪i, z⟫)⁻¹ • z := by rw [hcomb]
        have hseg' : z' ∈ openSegment ℝ x' y' := ⟨a', b', ha', hb', hab', hcomb'⟩
        have hx'F := hF.isExtreme.left_mem_of_mem_openSegment hx'p hy'p hz'F hseg'
        have : x = ⟪i, x⟫ • x' := by
          dsimp [x']
          simp [smul_smul, mul_inv_cancel₀ hxpos.ne']
        rw [this]
        exact ⟨⟪i, x⟫, x', hxpos.le, hx'F, rfl⟩


/-! ### Affine dimension: `affDim (conicHull F) = affDim F + 1` -/

lemma conicHull_subset_span (F : Set E) :
    conicHull F ⊆ (Submodule.span ℝ F : Set E) := by
  rintro _ ⟨c, x, _, hx, rfl⟩
  exact Submodule.smul_mem _ _ (Submodule.subset_span hx)

lemma conicHull_subset_affineSpan_insert_zero (F : Set E) :
    conicHull F ⊆ (affineSpan ℝ (insert (0 : E) F) : Set E) := by
  intro y hy
  rw [affineSpan_insert_zero]
  exact conicHull_subset_span F hy

lemma affDim_le_of_subset [FiniteDimensional ℝ E] {s t : Set E} (h : s ⊆ t) :
    affDim s ≤ affDim t := by
  have hspan : affineSpan ℝ s ≤ affineSpan ℝ t := affineSpan_mono _ h
  unfold affDim
  cases hs : (affineSpan ℝ s).finDim with
  | bot =>
    show -1 ≤ _
    cases (affineSpan ℝ t).finDim <;> simp
  | coe m =>
    have hsne : affineSpan ℝ s ≠ ⊥ := by
      intro hb; simp [hb] at hs
    have htne : affineSpan ℝ t ≠ ⊥ := fun hb => hsne (le_bot_iff.mp (hb ▸ hspan))
    have hle := AffineSubspace.finDim_mono (R := ℝ) (s := affineSpan ℝ s) (t := affineSpan ℝ t) hspan
    cases ht : (affineSpan ℝ t).finDim with
    | bot => exact absurd (AffineSubspace.finDim_eq_bot_iff.mp ht) htne
    | coe n =>
      change (m : ℤ) ≤ n
      have : (m : WithBot ℕ) ≤ n := by
        simpa [hs, ht] using hle
      exact_mod_cast this

lemma affDim_insert_zero_of_not_mem [FiniteDimensional ℝ E] {F : Set E}
    (hne : F.Nonempty) (h0 : (0 : E) ∉ affineSpan ℝ F) :
    affDim (insert (0 : E) F) = affDim F + 1 := by
  obtain ⟨p₀, hp₀F⟩ := hne
  have hp₀ : p₀ ∈ affineSpan ℝ F := mem_affineSpan ℝ hp₀F
  have hdir :
      (affineSpan ℝ (insert (0 : E) F)).direction =
        Submodule.span ℝ {(0 : E) -ᵥ p₀} ⊔ (affineSpan ℝ F).direction := by
    rw [← affineSpan_insert_affineSpan, AffineSubspace.direction_affineSpan_insert hp₀]
  have hnot : (0 : E) -ᵥ p₀ ∉ (affineSpan ℝ F).direction := by
    intro hv
    exact h0 ((AffineSubspace.vsub_right_mem_direction_iff_mem hp₀ (0 : E)).mp hv)
  have hneBotF : affineSpan ℝ F ≠ ⊥ :=
    (AffineSubspace.nonempty_iff_ne_bot _).mp ⟨p₀, hp₀⟩
  have hneBotI : affineSpan ℝ (insert (0 : E) F) ≠ ⊥ :=
    (AffineSubspace.nonempty_iff_ne_bot _).mp ⟨0, mem_affineSpan ℝ (Or.inl rfl)⟩
  have hrank :
      Module.finrank ℝ (affineSpan ℝ (insert (0 : E) F)).direction =
        Module.finrank ℝ (affineSpan ℝ F).direction + 1 := by
    have : Module.Finite ℝ E := inferInstance
    rw [hdir, sup_comm, Submodule.finrank_sup_span_singleton hnot]
  unfold affDim
  have hfdF := AffineSubspace.finDim_eq_finrank hneBotF
  have hfdI := AffineSubspace.finDim_eq_finrank hneBotI
  rw [hfdF, hfdI, hrank]
  simp

lemma affineSpan_conicHull_eq_affineSpan_insert_zero {F : Set E} (hne : F.Nonempty) :
    affineSpan ℝ (conicHull F) = affineSpan ℝ (insert (0 : E) F) := by
  apply le_antisymm
  · -- conicHull ⊆ affineSpan(insert 0 F) ⇒ span ≤ span
    have h := affineSpan_mono (k := ℝ) (conicHull_subset_affineSpan_insert_zero F)
    rwa [AffineSubspace.affineSpan_coe] at h
  · rw [affineSpan_le, insert_subset_iff]
    exact ⟨mem_affineSpan ℝ (zero_mem_conicHull hne),
      fun x hx => mem_affineSpan ℝ (subset_conicHull F hx)⟩

lemma affDim_conicHull_eq [FiniteDimensional ℝ E] {F : Set E} {i : E}
    (hht : ∀ x ∈ F, ⟪i, x⟫ = 1) (hne : F.Nonempty) :
    affDim (conicHull F) = affDim F + 1 := by
  have h0 : (0 : E) ∉ affineSpan ℝ F := zero_not_mem_affineSpan_of_height hht
  have hspan := affineSpan_conicHull_eq_affineSpan_insert_zero hne
  rw [affDim_eq_of_affineSpan_eq hspan, affDim_insert_zero_of_not_mem hne h0]


/-! ### Homogenized H-rep equality -/

lemma homogenized_cone_subset_conicHull {H : Set (Hyperplane E)} {i : E} {p : Set E}
    (hp : p = ⋂ h ∈ H, closedHalfspace h.1 h.2)
    (_hht : ∀ x ∈ p, ⟪i, x⟫ = 1) (hpne : p.Nonempty)
    (h0sec : ∀ y, y ∈ (⋂ a ∈ homogenizeNormals H i, closedHalfspace a 0) →
      ⟪i, y⟫ = 0 → y = 0) :
    (⋂ a ∈ homogenizeNormals H i, closedHalfspace a 0) ⊆ conicHull p := by
  intro y hy
  have hyi_nonneg : 0 ≤ ⟪i, y⟫ := by
    have hineg : (-i) ∈ homogenizeNormals H i := Or.inr rfl
    have : ⟪(-i), y⟫ ≤ 0 := by
      simpa [closedHalfspace] using (mem_iInter.mp ((mem_iInter.mp hy) (-i))) hineg
    simpa [inner_neg_left, neg_nonpos] using this
  by_cases hyi0 : ⟪i, y⟫ = 0
  · simpa [h0sec y hy hyi0] using zero_mem_conicHull hpne
  · have hypos : 0 < ⟪i, y⟫ := lt_of_le_of_ne hyi_nonneg (Ne.symm hyi0)
    set c := ⟪i, y⟫
    set x := c⁻¹ • y
    have hx1 : ⟪i, x⟫ = 1 := by
      simp [x, c, inner_smul_right, inv_mul_cancel₀ hypos.ne']
    have hy_eq : y = c • x := by
      simp [x, smul_smul, mul_inv_cancel₀ hypos.ne']
    have hxp : x ∈ p := by
      rw [hp]
      refine mem_iInter.mpr fun h => mem_iInter.mpr fun hh => ?_
      have ha : (h.1 - h.2 • i) ∈ homogenizeNormals H i := Or.inl ⟨h, hh, rfl⟩
      have hyh : ⟪h.1 - h.2 • i, y⟫ ≤ 0 := by
        simpa [closedHalfspace] using (mem_iInter.mp ((mem_iInter.mp hy) _)) ha
      change ⟪h.1, x⟫ ≤ h.2
      have hrew : ⟪h.1 - h.2 • i, y⟫ = c * (⟪h.1, x⟫ - h.2) := by
        rw [hy_eq, inner_smul_right, inner_sub_left, real_inner_smul_left, hx1, mul_one, mul_sub]
      have hcpos : 0 < c := hypos
      nlinarith [hyh, hcpos, hrew]
    exact ⟨c, x, hypos.le, hxp, hy_eq⟩

lemma conicHull_eq_homogenized_cone {H : Set (Hyperplane E)} {i : E} {p : Set E}
    (hp : p = ⋂ h ∈ H, closedHalfspace h.1 h.2)
    (hht : ∀ x ∈ p, ⟪i, x⟫ = 1) (hpne : p.Nonempty)
    (h0sec : ∀ y, y ∈ (⋂ a ∈ homogenizeNormals H i, closedHalfspace a 0) →
      ⟪i, y⟫ = 0 → y = 0) :
    conicHull p = ⋂ a ∈ homogenizeNormals H i, closedHalfspace a 0 :=
  subset_antisymm (conicHull_subset_homogenized_cone hp hht)
    (homogenized_cone_subset_conicHull hp hht hpne h0sec)

lemma homogenized_height_zero_eq_zero_of_isPolytope
    {H : Set (Hyperplane E)} {i : E} {p : Set E}
    (hp : p = ⋂ h ∈ H, closedHalfspace h.1 h.2)
    (_hht : ∀ x ∈ p, ⟪i, x⟫ = 1)
    (hP : IsPolytope p) (hpne : p.Nonempty) {y : E}
    (hy : y ∈ ⋂ a ∈ homogenizeNormals H i, closedHalfspace a 0)
    (hyi : ⟪i, y⟫ = 0) :
    y = 0 := by
  by_contra hyne
  obtain ⟨V, hV, hpeq⟩ := hP
  have hBdd : Bornology.IsBounded p := by
    rw [hpeq]
    exact (isBounded_convexHull (E := E)).2 hV.isBounded
  obtain ⟨C, hCpos, hC⟩ := hBdd.exists_pos_norm_le
  obtain ⟨x₀, hx₀⟩ := hpne
  have hray : ∀ t : ℝ, 0 ≤ t → x₀ + t • y ∈ p := by
    intro t ht
    rw [hp]
    refine mem_iInter.mpr fun h => mem_iInter.mpr fun hh => ?_
    have hx₀h : ⟪h.1, x₀⟫ ≤ h.2 := by
      have : x₀ ∈ closedHalfspace h.1 h.2 :=
        (mem_iInter.mp ((mem_iInter.mp (hp ▸ hx₀)) h)) hh
      simpa [closedHalfspace] using this
    have ha : (h.1 - h.2 • i) ∈ homogenizeNormals H i := Or.inl ⟨h, hh, rfl⟩
    have hyh : ⟪h.1 - h.2 • i, y⟫ ≤ 0 := by
      simpa [closedHalfspace] using (mem_iInter.mp ((mem_iInter.mp hy) _)) ha
    have hy1 : ⟪h.1, y⟫ ≤ 0 := by
      have : ⟪h.1 - h.2 • i, y⟫ = ⟪h.1, y⟫ - h.2 * ⟪i, y⟫ := by
        simp [inner_sub_left, inner_smul_left]
      simpa [this, hyi] using hyh
    change ⟪h.1, x₀ + t • y⟫ ≤ h.2
    have : ⟪h.1, x₀ + t • y⟫ = ⟪h.1, x₀⟫ + t * ⟪h.1, y⟫ := by
      simp [inner_add_right, inner_smul_right]
    rw [this]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ht hy1]
  have hynorm : 0 < ‖y‖ := norm_pos_iff.mpr hyne
  set t : ℝ := (C + ‖x₀‖ + 1) / ‖y‖
  have hnum : 0 ≤ C + ‖x₀‖ + 1 := by positivity
  have ht0 : 0 ≤ t := div_nonneg hnum hynorm.le
  have ht_ge : t * ‖y‖ - ‖x₀‖ ≤ ‖x₀ + t • y‖ := by
    have htri : ‖t • y‖ ≤ ‖x₀ + t • y‖ + ‖x₀‖ := by
      have h := norm_sub_le (x₀ + t • y) x₀
      have heq : (x₀ + t • y) - x₀ = t • y := by simp
      rwa [heq] at h
    have hnorm : ‖t • y‖ = t * ‖y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    linarith
  have hval : t * ‖y‖ - ‖x₀‖ = C + 1 := by
    dsimp [t]
    field_simp [hynorm.ne']
    ring
  have hmem := hray t ht0
  have hle : ‖x₀ + t • y‖ ≤ C := hC _ hmem
  linarith

lemma conicHull_eq_homogenized_cone_of_isPolytope
    {H : Set (Hyperplane E)} {i : E} {p : Set E}
    (hp : p = ⋂ h ∈ H, closedHalfspace h.1 h.2)
    (hht : ∀ x ∈ p, ⟪i, x⟫ = 1) (hpne : p.Nonempty) (hP : IsPolytope p) :
    conicHull p = ⋂ a ∈ homogenizeNormals H i, closedHalfspace a 0 :=
  conicHull_eq_homogenized_cone hp hht hpne
    (fun _y hy hyi => homogenized_height_zero_eq_zero_of_isPolytope hp hht hP hpne hy hyi)

/-! ### Assemble `ConeSliceFaceBijection` -/

lemma exists_mem_ne_zero_of_affDim_pos {G : Set E} {d : ℕ}
    (hdim : affDim G = ((d + 1 : ℕ) : ℤ)) : ∃ z ∈ G, z ≠ 0 := by
  by_contra hall
  push Not at hall
  have hsub : G ⊆ ({0} : Set E) := hall
  have hneG : G.Nonempty := by
    by_contra hempty
    have : G = ∅ := not_nonempty_iff_eq_empty.mp hempty
    simp [this, affDim_empty] at hdim
    omega
  obtain ⟨z, hz⟩ := hneG
  have hz0 : z = 0 := hsub hz
  have : G = ({0} : Set E) :=
    Subset.antisymm hsub (singleton_subset_iff.mpr (by simpa [hz0] using hz))
  simp [this, affDim_singleton] at hdim
  omega

lemma faces_succ_conicHull [FiniteDimensional ℝ E] {p : Set E} {i : E} (d : ℕ)
    (hht : ∀ x ∈ p, ⟪i, x⟫ = 1) :
    {f : Set E | IsFaceOf (conicHull p) f ∧ affDim f = ((d + 1 : ℕ) : ℤ)} =
      conicHull '' {F : Set E | IsFaceOf p F ∧ affDim F = (d : ℤ)} := by
  apply subset_antisymm
  · intro G ⟨hG, hdim⟩
    obtain ⟨z, hzG, hzne⟩ := exists_mem_ne_zero_of_affDim_pos (d := d) hdim
    have hConicG : IsConic G := isConic_of_isFaceOf (isConic_conicHull p) hG
    have hpos : ∀ x ∈ G, x ≠ 0 → 0 < ⟪i, x⟫ := fun x hx hxne =>
      height_pos_of_mem_conicHull hht (hG.isExtreme.subset hx) hxne
    set F := G ∩ {x : E | ⟪i, x⟫ = 1}
    have hFaceF : IsFaceOf p F := isFaceOf_slice_of_isFaceOf_conicHull hht hG
    have hEq : conicHull F = G :=
      conicHull_inter_height_eq_of_isConic hConicG hpos ⟨z, hzG, hzne⟩
    have hhtF : ∀ x ∈ F, ⟪i, x⟫ = 1 := fun _ hx => hx.2
    have hFne : F.Nonempty := by
      refine ⟨(⟪i, z⟫)⁻¹ • z, ?_⟩
      have hzpos := hpos z hzG hzne
      refine ⟨hConicG hzG _ (inv_nonneg.mpr hzpos.le), ?_⟩
      simp [inner_smul_right, inv_mul_cancel₀ hzpos.ne']
    have hdimF : affDim F = (d : ℤ) := by
      have h := affDim_conicHull_eq (F := F) (i := i) hhtF hFne
      rw [hEq] at h
      -- h: affDim G = affDim F + 1; hdim: affDim G = ↑(d+1)
      have : affDim F + 1 = ((d + 1 : ℕ) : ℤ) := by rw [← h, hdim]
      omega
    refine ⟨F, ⟨hFaceF, hdimF⟩, hEq⟩
  · intro G hG
    obtain ⟨F, ⟨hF, hdimF⟩, rfl⟩ := hG
    have hFace := isFaceOf_conicHull_of_isFaceOf hht hF
    have hFne : F.Nonempty := by
      by_contra hempty
      have : F = ∅ := not_nonempty_iff_eq_empty.mp hempty
      simp [this, affDim_empty] at hdimF
    have hhtF : ∀ x ∈ F, ⟪i, x⟫ = 1 := fun x hx => hht x (isFaceOf_subset hF hx)
    refine ⟨hFace, ?_⟩
    have h := affDim_conicHull_eq hhtF hFne
    rw [h, hdimF]
    norm_cast

/-- Paulson cone↔slice face bijection for a height-1 convex set. -/
theorem coneSliceFaceBijection [FiniteDimensional ℝ E] {p : Set E} {i : E} (n : ℕ)
    (hht : ∀ x ∈ p, ⟪i, x⟫ = 1) (hne : p.Nonempty) (hConv : Convex ℝ p) :
    ConeSliceFaceBijection (conicHull p) p n where
  zero_face := coneSlice_zero_face hht hne hConv
  faces_succ := fun d _hd => faces_succ_conicHull d hht
  conic_inj := fun d _hd =>
    injOn_conicHull_faces (fun _F hF x hx => hht x (isFaceOf_subset hF hx)) d

lemma iInter_closedHalfspace_diff_zero (As : Set E) :
    (⋂ a ∈ As, closedHalfspace a 0) = (⋂ a ∈ As \ ({0} : Set E), closedHalfspace a 0) := by
  ext x
  constructor
  · intro hx
    exact mem_iInter₂.mpr fun a ha => (mem_iInter₂.mp hx a) ha.1
  · intro hx
    refine mem_iInter₂.mpr fun a ha => ?_
    by_cases ha0 : a = 0
    · subst ha0
      change ⟪(0 : E), x⟫ ≤ 0
      simp [inner_zero_left]
    · exact (mem_iInter₂.mp hx a) ⟨ha, ha0⟩

lemma faceEulerSum_polyhedral_cone_diff_zero [FiniteDimensional ℝ E] [Nonempty E]
    {As : Set E} (hAs : As.Finite) (hneAs : (As \ ({0} : Set E)).Nonempty)
    (hpos : ({x : E | ∀ a ∈ As \ ({0} : Set E), 0 < ⟪a, x⟫}).Nonempty) :
    faceEulerSum (⋂ a ∈ As, closedHalfspace a 0) (Module.finrank ℝ E) = 0 := by
  rw [iInter_closedHalfspace_diff_zero]
  exact faceEulerSum_polyhedral_cone hAs.sdiff hneAs hpos

/-- With homogenized equality, the cone is polyhedral so `faceEulerSum_polyhedral_cone`
applies; combined with the bijection this yields the slice Euler sum.

`hpos` is required only on nonzero homogenized normals (`0` arises harmlessly from
encoding a height hyperplane as a pair of opposite halfspaces). -/
theorem faceEulerSum_of_height_one_polytope [FiniteDimensional ℝ E] [Nonempty E]
    {H : Set (Hyperplane E)} {i : E} {p : Set E}
    (hH : H.Finite)
    (hp : p = ⋂ h ∈ H, closedHalfspace h.1 h.2)
    (hht : ∀ x ∈ p, ⟪i, x⟫ = 1) (hpne : p.Nonempty) (hConv : Convex ℝ p)
    (h0sec : ∀ y, y ∈ (⋂ a ∈ homogenizeNormals H i, closedHalfspace a 0) →
      ⟪i, y⟫ = 0 → y = 0)
    (hpos : ({x : E | ∀ a ∈ homogenizeNormals H i \ ({0} : Set E), 0 < ⟪a, x⟫}).Nonempty)
    (hn : 1 ≤ Module.finrank ℝ E) :
    faceEulerSum p (Module.finrank ℝ E - 1) = 1 := by
  set n := Module.finrank ℝ E
  have heq := conicHull_eq_homogenized_cone hp hht hpne h0sec
  have hBij := coneSliceFaceBijection n hht hpne hConv
  have hAsNe : (homogenizeNormals H i \ ({0} : Set E)).Nonempty := by
    refine ⟨-i, Or.inr rfl, ?_⟩
    intro hi0
    have hi : i = 0 := neg_eq_zero.mp hi0
    obtain ⟨x, hx⟩ := hpne
    have h1 := hht x hx
    rw [hi, inner_zero_left] at h1
    exact zero_ne_one h1
  have hCone : faceEulerSum (conicHull p) n = 0 := by
    rw [heq]
    exact faceEulerSum_polyhedral_cone_diff_zero
      (homogenizeNormals_finite hH i) hAsNe hpos
  exact faceEulerSum_slice_of_cone hBij hCone hn

end EulersGem

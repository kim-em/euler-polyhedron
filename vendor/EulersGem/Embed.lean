/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.ConeSlice
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Embedding a full-dimensional polytope as a height-1 slice (Paulson)

Paulson `Euler_Poincare_full`: embed `p ⊆ E` into `WithLp 2 (E × ℝ)` via
`x ↦ (x, 1)`, apply the height-1 EP lemma, transfer face counts back.
-/

open scoped RealInnerProductSpace BigOperators
open Classical Set WithLp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace EulersGem

/-! ### Ambient product space -/

abbrev ProdR := WithLp 2 (E × ℝ)

noncomputable def heightVec : ProdR (E := E) := toLp 2 ((0 : E), (1 : ℝ))

noncomputable def augmLinear : E →ₗ[ℝ] ProdR (E := E) :=
  (WithLp.linearEquiv 2 ℝ (E × ℝ)).symm ∘ₗ LinearMap.inl ℝ E ℝ

lemma augmLinear_apply (x : E) : augmLinear (E := E) x = toLp 2 (x, (0 : ℝ)) := rfl

lemma augmLinear_injective : Function.Injective (augmLinear (E := E)) := by
  intro x y h
  simpa [augmLinear_apply, toLp.injEq, Prod.mk.injEq] using h

noncomputable def heightOneAffine : E →ᵃ[ℝ] ProdR (E := E) :=
  (AffineEquiv.constVAdd ℝ (ProdR (E := E)) (heightVec (E := E))).toAffineMap.comp
    augmLinear.toAffineMap

lemma heightOneAffine_apply (x : E) :
    heightOneAffine (E := E) x = toLp 2 (x, (1 : ℝ)) := by
  simp only [heightOneAffine, AffineMap.comp_apply, LinearMap.coe_toAffineMap,
    AffineEquiv.coe_toAffineMap, AffineEquiv.constVAdd_apply, augmLinear_apply, heightVec]
  change toLp 2 ((0 : E), (1 : ℝ)) + toLp 2 (x, (0 : ℝ)) = toLp 2 (x, (1 : ℝ))
  rw [← toLp_add]
  simp [Prod.mk_add_mk]

lemma heightOneAffine_injective : Function.Injective (heightOneAffine (E := E)) := by
  intro x y h
  simpa [heightOneAffine_apply, toLp.injEq, Prod.mk.injEq] using h

lemma heightOneAffine_inner (x : E) :
    ⟪heightVec (E := E), heightOneAffine x⟫ = 1 := by
  simp [heightOneAffine_apply, heightVec, prod_inner_apply, inner_zero_left]

lemma finrank_prodR [FiniteDimensional ℝ E] :
    Module.finrank ℝ (ProdR (E := E)) = Module.finrank ℝ E + 1 := by
  have h := (WithLp.linearEquiv 2 ℝ (E × ℝ)).finrank_eq
  rw [h, Module.finrank_prod, Module.finrank_self]

/-! ### Face / affDim transfer -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma isFaceOf_image_linear {f : E →ₗ[ℝ] F} (hf : Function.Injective f)
    {S T : Set E} (h : IsFaceOf S T) :
    IsFaceOf (f '' S) (f '' T) := by
  refine ⟨⟨image_mono h.isExtreme.subset, ?_⟩, h.convex.linear_image f⟩
  intro x hxS y hyS z hzT hzSeg
  obtain ⟨x', hx', rfl⟩ := hxS
  obtain ⟨y', hy', rfl⟩ := hyS
  obtain ⟨z', hz', rfl⟩ := hzT
  obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hzSeg
  have hcomb' : a • x' + b • y' = z' := hf (by
    simpa only [map_add, map_smul] using hcomb)
  exact mem_image_of_mem _
    (h.isExtreme.left_mem_of_mem_openSegment hx' hy' hz' ⟨a, b, ha, hb, hab, hcomb'⟩)

lemma isFaceOf_of_image_linear {f : E →ₗ[ℝ] F} (hf : Function.Injective f)
    {S T : Set E} (h : IsFaceOf (f '' S) (f '' T)) :
    IsFaceOf S T := by
  have hsub : T ⊆ S := by
    intro t ht
    obtain ⟨s, hs, heq⟩ := h.isExtreme.subset (mem_image_of_mem f ht)
    exact hf heq ▸ hs
  refine ⟨⟨hsub, ?_⟩, ?_⟩
  · intro x hxS y hyS z hzT hzSeg
    obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hzSeg
    have hseg' : f z ∈ openSegment ℝ (f x) (f y) :=
      ⟨a, b, ha, hb, hab, by simp only [← map_smul, ← map_add, hcomb]⟩
    obtain ⟨t, htT, heq⟩ := h.isExtreme.left_mem_of_mem_openSegment
      (mem_image_of_mem _ hxS) (mem_image_of_mem _ hyS)
      (mem_image_of_mem _ hzT) hseg'
    exact hf heq ▸ htT
  · intro x hx y hy a b ha hb hab
    have hmem : f (a • x + b • y) ∈ f '' T := by
      have := h.convex (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha hb hab
      simpa only [map_add, map_smul] using this
    obtain ⟨t, ht, heq⟩ := hmem
    have : a • x + b • y = t := hf (by simpa only [map_add, map_smul] using heq.symm)
    exact this ▸ ht

lemma isFaceOf_vadd (v : E) {S T : Set E} (h : IsFaceOf S T) :
    IsFaceOf ((fun x => v + x) '' S) ((fun x => v + x) '' T) := by
  refine ⟨⟨image_mono h.isExtreme.subset, ?_⟩, h.convex.translate v⟩
  intro x hxS y hyS z hzT hzSeg
  obtain ⟨x', hx', rfl⟩ := hxS
  obtain ⟨y', hy', rfl⟩ := hyS
  obtain ⟨z', hz', rfl⟩ := hzT
  obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hzSeg
  have hcomb' : a • x' + b • y' = z' := by
    have hrew : a • (v + x') + b • (v + y') =
        (a + b) • v + (a • x' + b • y') := by module
    rw [hrew, hab, one_smul] at hcomb
    exact add_left_cancel hcomb
  exact ⟨x', h.isExtreme.left_mem_of_mem_openSegment hx' hy' hz'
    ⟨a, b, ha, hb, hab, hcomb'⟩, rfl⟩

lemma isFaceOf_of_vadd (v : E) {S T : Set E}
    (h : IsFaceOf ((fun x => v + x) '' S) ((fun x => v + x) '' T)) :
    IsFaceOf S T := by
  have hS : (fun x => (-v) + x) '' ((fun x => v + x) '' S) = S := by
    ext z; simp [add_assoc, add_neg_cancel, add_zero]
  have hT : (fun x => (-v) + x) '' ((fun x => v + x) '' T) = T := by
    ext z; simp [add_assoc, add_neg_cancel, add_zero]
  have h' := isFaceOf_vadd (-v) h
  rwa [hS, hT] at h'

lemma affineMap_eq_vadd_linear (f : E →ᵃ[ℝ] F) (x : E) :
    f x = f 0 + f.linear x := by
  have h := AffineMap.map_vadd f (0 : E) x
  -- h : f.linear x +ᵥ f 0 = f x
  simpa [vadd_eq_add, add_comm] using h

lemma image_eq_vadd_linear_image (f : E →ᵃ[ℝ] F) (U : Set E) :
    f '' U = (fun y => f 0 + y) '' (f.linear '' U) := by
  ext y; constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨f.linear x, mem_image_of_mem _ hx, (affineMap_eq_vadd_linear f x).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (affineMap_eq_vadd_linear f x).symm ▸ rfl⟩

lemma isFaceOf_image_affine {f : E →ᵃ[ℝ] F} (hf : Function.Injective f)
    {S T : Set E} (h : IsFaceOf S T) :
    IsFaceOf (f '' S) (f '' T) := by
  rw [image_eq_vadd_linear_image f S, image_eq_vadd_linear_image f T]
  exact isFaceOf_vadd _ (isFaceOf_image_linear (f.linear_injective_iff.mpr hf) h)

lemma isFaceOf_of_image_affine {f : E →ᵃ[ℝ] F} (hf : Function.Injective f)
    {S T : Set E} (h : IsFaceOf (f '' S) (f '' T)) :
    IsFaceOf S T := by
  rw [image_eq_vadd_linear_image f S, image_eq_vadd_linear_image f T] at h
  exact isFaceOf_of_image_linear (f.linear_injective_iff.mpr hf) (isFaceOf_of_vadd _ h)

lemma affDim_image_affine (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) (s : Set E) :
    affDim (f '' s) = affDim s := by
  have hspan : affineSpan ℝ (f '' s) = AffineSubspace.map f (affineSpan ℝ s) :=
    (AffineSubspace.map_span f s).symm
  simp only [affDim, hspan, AffineSubspace.finDim_map_of_injective hf]

lemma faces_image_affine (f : E →ᵃ[ℝ] F) (hf : Function.Injective f)
    (p : Set E) (d : ℤ) :
    {g : Set F | IsFaceOf (f '' p) g ∧ affDim g = d} =
      (fun F : Set E => f '' F) '' {F : Set E | IsFaceOf p F ∧ affDim F = d} := by
  apply subset_antisymm
  · intro G ⟨hG, hdim⟩
    set F : Set E := f ⁻¹' G
    have hGeq : G = f '' F := by
      apply subset_antisymm
      · intro y hyG
        obtain ⟨x, _, rfl⟩ := (isFaceOf_subset hG) hyG
        exact ⟨x, by simpa [F] using hyG, rfl⟩
      · exact image_preimage_subset f G
    refine ⟨F, ⟨isFaceOf_of_image_affine hf (by rwa [← hGeq]), ?_⟩, hGeq.symm⟩
    rw [← affDim_image_affine f hf F, ← hGeq, hdim]
  · rintro _ ⟨F, ⟨hF, hdimF⟩, rfl⟩
    exact ⟨isFaceOf_image_affine hf hF, by rw [affDim_image_affine f hf, hdimF]⟩

lemma faceEulerSum_image_affine (f : E →ᵃ[ℝ] F) (hf : Function.Injective f)
    (p : Set E) (n : ℕ) :
    faceEulerSum (f '' p) n = faceEulerSum p n := by
  unfold faceEulerSum
  refine Finset.sum_congr rfl fun d _ => ?_
  have hEq := faces_image_affine f hf p (d : ℤ)
  have hinj : InjOn (fun F : Set E => f '' F)
      {F : Set E | IsFaceOf p F ∧ affDim F = (d : ℤ)} :=
    fun _ _ _ _ h => hf.image_injective h
  rw [hEq, hinj.ncard_image]

/-! ### Basic height-1 properties -/

lemma convex_heightOneAffine_image {p : Set E} (hp : Convex ℝ p) :
    Convex ℝ (heightOneAffine (E := E) '' p) :=
  hp.affine_image _

lemma isPolytope_heightOneAffine_image {p : Set E} (hP : IsPolytope p) :
    IsPolytope (heightOneAffine (E := E) '' p) := by
  obtain ⟨V, hV, rfl⟩ := hP
  refine ⟨heightOneAffine '' V, hV.image _, ?_⟩
  exact AffineMap.image_convexHull (heightOneAffine (E := E)) V

lemma height_one_of_mem_image {p : Set E} {y : ProdR (E := E)}
    (hy : y ∈ heightOneAffine '' p) :
    ⟪heightVec (E := E), y⟫ = 1 := by
  obtain ⟨x, _, rfl⟩ := hy; exact heightOneAffine_inner x

/-! ### H-rep of the embedding -/

lemma inner_toLp (u v : E × ℝ) :
    ⟪toLp 2 u, toLp 2 v⟫ = ⟪u.1, v.1⟫ + u.2 * v.2 := by
  simp [prod_inner_apply, mul_comm]

noncomputable def embedHyperplanes (H : Set (Hyperplane E)) :
    Set (Hyperplane (ProdR (E := E))) :=
  (fun h : Hyperplane E => (toLp 2 (h.1, (0 : ℝ)), h.2)) '' H ∪
    {(heightVec (E := E), (1 : ℝ)), (-heightVec (E := E), (-1 : ℝ))}

omit [InnerProductSpace ℝ E] in
lemma embedHyperplanes_finite {H : Set (Hyperplane E)} (hH : H.Finite) :
    (embedHyperplanes (E := E) H).Finite :=
  (hH.image _).union ((finite_singleton _).union (finite_singleton _))

lemma mem_embedHalfspace_side (h : Hyperplane E) (x : E) :
    ⟪toLp 2 (h.1, (0 : ℝ)), heightOneAffine (E := E) x⟫ = ⟪h.1, x⟫ := by
  rw [heightOneAffine_apply, inner_toLp]; simp

lemma heightOneAffine_image_subset_iInter {H : Set (Hyperplane E)} {p : Set E}
    (hp : p = ⋂ h ∈ H, closedHalfspace h.1 h.2) :
    heightOneAffine (E := E) '' p ⊆
      ⋂ k ∈ embedHyperplanes (E := E) H, closedHalfspace k.1 k.2 := by
  rintro _ ⟨x, hx, rfl⟩
  refine mem_iInter₂.mpr fun k hk => ?_
  unfold embedHyperplanes at hk
  rcases hk with hpos | hht
  · obtain ⟨h, hh, rfl⟩ := hpos
    have hxle : x ∈ closedHalfspace h.1 h.2 := (mem_iInter₂.mp (hp ▸ hx) h) hh
    change ⟪toLp 2 (h.1, (0 : ℝ)), heightOneAffine x⟫ ≤ h.2
    rw [mem_embedHalfspace_side]
    simpa [closedHalfspace] using hxle
  · rcases hht with rfl | hneg
    · change ⟪heightVec (E := E), heightOneAffine x⟫ ≤ 1
      exact (le_of_eq (heightOneAffine_inner x))
    · have : k = (-heightVec (E := E), (-1 : ℝ)) := by simpa using hneg
      subst this
      change ⟪-heightVec (E := E), heightOneAffine x⟫ ≤ -1
      have h1 := heightOneAffine_inner x
      simp only [inner_neg_left, h1, neg_le_neg_iff, le_refl]

lemma iInter_subset_heightOneAffine_image {H : Set (Hyperplane E)} {p : Set E}
    (hp : p = ⋂ h ∈ H, closedHalfspace h.1 h.2) :
    (⋂ k ∈ embedHyperplanes (E := E) H, closedHalfspace k.1 k.2) ⊆
      heightOneAffine (E := E) '' p := by
  intro y hy
  set xy := ofLp y
  have hyeq : y = toLp 2 xy := (WithLp.toLp_ofLp (p := 2) y).symm
  have ht : xy.2 = 1 := by
    have hle : ⟪heightVec (E := E), y⟫ ≤ 1 := by
      have hk : (heightVec (E := E), (1 : ℝ)) ∈ embedHyperplanes (E := E) H :=
        Or.inr (Or.inl rfl)
      simpa [closedHalfspace] using (mem_iInter₂.mp hy _ hk)
    have hge' : ⟪-heightVec (E := E), y⟫ ≤ -1 := by
      have hk : (-heightVec (E := E), (-1 : ℝ)) ∈ embedHyperplanes (E := E) H :=
        Or.inr (Or.inr rfl)
      simpa [closedHalfspace] using (mem_iInter₂.mp hy _ hk)
    have hge : 1 ≤ ⟪heightVec (E := E), y⟫ := by
      simpa [inner_neg_left] using hge'
    have heq : ⟪heightVec (E := E), y⟫ = 1 := le_antisymm hle hge
    -- expand: ⟪heightVec, toLp xy⟫ = xy.2
    have : ⟪heightVec (E := E), toLp 2 xy⟫ = xy.2 := by
      simp [heightVec, inner_toLp]
    rw [hyeq, this] at heq
    exact heq
  have hx : xy.1 ∈ p := by
    rw [hp]
    refine mem_iInter₂.mpr fun h hh => ?_
    have hk : (toLp 2 (h.1, (0 : ℝ)), h.2) ∈ embedHyperplanes (E := E) H :=
      Or.inl ⟨h, hh, rfl⟩
    have hle : ⟪toLp 2 (h.1, (0 : ℝ)), y⟫ ≤ h.2 := by
      simpa [closedHalfspace] using (mem_iInter₂.mp hy _ hk)
    change ⟪h.1, xy.1⟫ ≤ h.2
    have : ⟪toLp 2 (h.1, (0 : ℝ)), toLp 2 xy⟫ = ⟪h.1, xy.1⟫ := by
      simp [inner_toLp]
    rwa [hyeq, this] at hle
  refine ⟨xy.1, hx, ?_⟩
  rw [heightOneAffine_apply, hyeq]; congr 1; exact Prod.ext rfl ht.symm

lemma heightOneAffine_image_eq_iInter {H : Set (Hyperplane E)} {p : Set E}
    (hp : p = ⋂ h ∈ H, closedHalfspace h.1 h.2) :
    heightOneAffine (E := E) '' p =
      ⋂ k ∈ embedHyperplanes (E := E) H, closedHalfspace k.1 k.2 :=
  subset_antisymm (heightOneAffine_image_subset_iInter hp)
    (iInter_subset_heightOneAffine_image hp)

/-! ### Affine span / interior -/

lemma affineSpan_eq_top_of_affDim_eq_finrank [FiniteDimensional ℝ E] [Nonempty E]
    {s : Set E} (h : affDim s = Module.finrank ℝ E) :
    affineSpan ℝ s = ⊤ := by
  have hne : s.Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hs
    simp [hs, affDim_empty] at h
  have hneBot : affineSpan ℝ s ≠ ⊥ :=
    (AffineSubspace.nonempty_iff_ne_bot _).mp
      ((affineSpan_nonempty (k := ℝ) (V := E) (P := E)).mpr hne)
  have hne' : (affineSpan ℝ s : Set E).Nonempty :=
    (affineSpan_nonempty (k := ℝ) (V := E) (P := E)).mpr hne
  unfold affDim at h
  cases hmatch : (affineSpan ℝ s).finDim with
  | bot => exact absurd (AffineSubspace.finDim_eq_bot_iff.mp hmatch) hneBot
  | coe n =>
    have hfd := AffineSubspace.finDim_eq_finrank hneBot
    simp only [hmatch] at h hfd
    -- h : ↑n = ↑(finrank); hfd : ↑(finrank direction) = ↑n
    have hn : n = Module.finrank ℝ E := Nat.cast_injective h
    have hdir' : Module.finrank ℝ (affineSpan ℝ s).direction = n :=
      Nat.cast_injective hfd.symm
    have hdirTop : (affineSpan ℝ s).direction = ⊤ :=
      Submodule.eq_top_of_finrank_eq (hdir'.trans hn)
    exact (AffineSubspace.direction_eq_top_iff_of_nonempty hne').mp hdirTop

lemma interior_nonempty_of_affDim_eq_finrank [FiniteDimensional ℝ E] [Nonempty E]
    {s : Set E} (hConv : Convex ℝ s) (h : affDim s = Module.finrank ℝ E) :
    (interior s).Nonempty :=
  (hConv.interior_nonempty_iff_affineSpan_eq_top).mpr
    (affineSpan_eq_top_of_affDim_eq_finrank h)

lemma interior_closedHalfspace {a : E} (ha : a ≠ 0) (b : ℝ) :
    interior (closedHalfspace a b) = {x : E | ⟪a, x⟫ < b} := by
  apply subset_antisymm
  · intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
    by_contra hnot
    have hxS : ⟪a, x⟫ ≤ b := by simpa [closedHalfspace] using interior_subset hx
    have hxeq : ⟪a, x⟫ = b := le_antisymm hxS (le_of_not_gt hnot)
    let t : ℝ := ε / (2 * ‖a‖)
    have ht : 0 < t := div_pos hε (by positivity)
    have hdist : dist (x + t • a) x < ε := by
      simp [dist_eq_norm, norm_smul, Real.norm_of_nonneg ht.le]
      have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
      have : t * ‖a‖ = ε / 2 := by simp only [t]; field_simp [hna]
      linarith
    have hin : ⟪a, x + t • a⟫ ≤ b := by simpa [closedHalfspace] using hball hdist
    have hcalc : ⟪a, x⟫ + t * ⟪a, a⟫ ≤ b := by
      simpa [inner_add_right, inner_smul_right] using hin
    nlinarith [hxeq, real_inner_self_pos.mpr ha]
  · intro x hx
    refine mem_interior.mpr ⟨{y | ⟪a, y⟫ < b}, ?_, isOpen_halfSpace_lt a b, hx⟩
    intro y hy; simpa [closedHalfspace] using (le_of_lt hy)

/-! ### Open dual certificate -/

lemma exists_openDual_embed [FiniteDimensional ℝ E] [Nonempty E]
    {H : Set (Hyperplane E)} {p : Set E}
    (hp : p = ⋂ h ∈ H, closedHalfspace h.1 h.2)
    (hConv : Convex ℝ p) (hdim : affDim p = Module.finrank ℝ E) :
    ({z : ProdR (E := E) |
        ∀ a ∈ homogenizeNormals (embedHyperplanes (E := E) H) (heightVec (E := E)) \
            ({0} : Set (ProdR (E := E))),
          0 < ⟪a, z⟫}).Nonempty := by
  obtain ⟨x₀, hx₀⟩ := interior_nonempty_of_affDim_eq_finrank hConv hdim
  refine ⟨toLp 2 (-x₀, (-1 : ℝ)), ?_⟩
  intro a ha
  have ha0 : a ≠ 0 := ha.2
  rcases ha.1 with hpos | hneg
  · obtain ⟨k, hk, rfl⟩ := hpos
    unfold embedHyperplanes at hk
    rcases hk with hside | hht
    · obtain ⟨h, hh, rfl⟩ := hside
      have hval :
          ⟪toLp 2 (h.1, (0 : ℝ)) - h.2 • heightVec (E := E), toLp 2 (-x₀, (-1 : ℝ))⟫ =
            h.2 - ⟪h.1, x₀⟫ := by
        simp [heightVec, inner_toLp, inner_sub_left, inner_smul_left, inner_neg_right]
        ring
      rw [hval]
      have hint : x₀ ∈ interior (closedHalfspace h.1 h.2) :=
        interior_mono (fun x hx => (mem_iInter₂.mp (hp ▸ hx) h) hh) hx₀
      by_cases hh0 : h.1 = 0
      · have hxle : (0 : ℝ) ≤ h.2 := by
          simpa [closedHalfspace, hh0, inner_zero_left] using interior_subset hint
        have hbne : h.2 ≠ 0 := by
          intro hb0
          apply ha0
          simp [hh0, hb0, heightVec, sub_eq_add_neg]
        -- Goal after hval: 0 < h.2 - ⟪0, x₀⟫ = h.2
        simpa [hh0, inner_zero_left] using lt_of_le_of_ne hxle (Ne.symm hbne)
      · have : ⟪h.1, x₀⟫ < h.2 := by
          simpa [interior_closedHalfspace hh0] using hint
        linarith
    · rcases hht with rfl | hk
      · exact absurd (by simp : heightVec (E := E) - (1 : ℝ) • heightVec = 0) ha0
      · have : k = (-heightVec (E := E), (-1 : ℝ)) := by simpa using hk
        subst this
        exact absurd (by simp : -heightVec (E := E) - (-1 : ℝ) • heightVec = 0) ha0
  · have : a = -heightVec (E := E) := by simpa using hneg
    subst this
    simp [heightVec, inner_toLp, inner_neg_left]

/-! ### Euler–Poincaré full -/

lemma faceEulerSum_heightOneAffine_eq_one [FiniteDimensional ℝ E] [Nonempty E]
    {H : Set (Hyperplane E)} {p : Set E}
    (hH : H.Finite)
    (hp : p = ⋂ h ∈ H, closedHalfspace h.1 h.2)
    (hP : IsPolytope p) (hConv : Convex ℝ p) (hpne : p.Nonempty)
    (hdim : affDim p = Module.finrank ℝ E)
    (_hn : 1 ≤ Module.finrank ℝ E) :
    faceEulerSum (heightOneAffine (E := E) '' p)
      (Module.finrank ℝ (ProdR (E := E)) - 1) = 1 := by
  set P := heightOneAffine (E := E) '' p
  set He := embedHyperplanes (E := E) H
  have hPeq : P = ⋂ k ∈ He, closedHalfspace k.1 k.2 :=
    heightOneAffine_image_eq_iInter hp
  have hht : ∀ y ∈ P, ⟪heightVec (E := E), y⟫ = 1 := fun _ hy => height_one_of_mem_image hy
  have hPpoly : IsPolytope P := isPolytope_heightOneAffine_image hP
  have h0sec : ∀ y, y ∈ (⋂ a ∈ homogenizeNormals He (heightVec (E := E)), closedHalfspace a 0) →
      ⟪heightVec (E := E), y⟫ = 0 → y = 0 :=
    fun y hy hyi => homogenized_height_zero_eq_zero_of_isPolytope hPeq hht hPpoly
      (hpne.image _) hy hyi
  have hr : 1 ≤ Module.finrank ℝ (ProdR (E := E)) := by
    rw [finrank_prodR]; omega
  exact faceEulerSum_of_height_one_polytope (embedHyperplanes_finite hH) hPeq
    hht (hpne.image _) (convex_heightOneAffine_image hConv) h0sec
    (exists_openDual_embed hp hConv hdim) hr

/-- Paulson `Euler_Poincare_full`. -/
theorem Euler_Poincare_full [FiniteDimensional ℝ E] [Nonempty E]
    {H : Set (Hyperplane E)} {p : Set E}
    (hH : H.Finite)
    (hp : p = ⋂ h ∈ H, closedHalfspace h.1 h.2)
    (hP : IsPolytope p)
    (hdim : affDim p = Module.finrank ℝ E)
    (hn : 1 ≤ Module.finrank ℝ E) :
    faceEulerSum p (Module.finrank ℝ E) = 1 := by
  have hConv : Convex ℝ p := by obtain ⟨V, _, rfl⟩ := hP; exact convex_convexHull _ _
  have hpne : p.Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hs
    simp [hs, affDim_empty] at hdim
  have hsum := faceEulerSum_heightOneAffine_eq_one hH hp hP hConv hpne hdim hn
  have htransfer :=
    faceEulerSum_image_affine (heightOneAffine (E := E)) heightOneAffine_injective p
      (Module.finrank ℝ (ProdR (E := E)) - 1)
  rw [finrank_prodR, Nat.add_sub_cancel] at hsum htransfer
  exact htransfer.symm.trans hsum

/-! ### Unique solid face + geometric 3D -/

lemma faces_dim_eq_finrank_eq_singleton [FiniteDimensional ℝ E] [Nonempty E]
    {p : Set E} (hConv : Convex ℝ p) (hdim : affDim p = Module.finrank ℝ E) :
    {f : Set E | IsFaceOf p f ∧ affDim f = Module.finrank ℝ E} = ({p} : Set (Set E)) := by
  apply subset_antisymm
  · intro f ⟨hF, hfdim⟩
    have hsub : f ⊆ p := isFaceOf_subset hF
    have heq : f = p := by
      apply Subset.antisymm hsub
      have hspanF : affineSpan ℝ f = ⊤ :=
        affineSpan_eq_top_of_affDim_eq_finrank (by simpa using hfdim)
      obtain ⟨y, hyint⟩ :=
        (hF.convex.interior_nonempty_iff_affineSpan_eq_top).mpr hspanF
      have hyF : y ∈ f := interior_subset hyint
      intro x hxp
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hyint)
      set t : ℝ := min (1 / 2) (ε / (2 * (‖y - x‖ + 1)))
      have ht0 : 0 < t := lt_min (by norm_num) (div_pos hε (by positivity))
      set z : E := y + t • (y - x)
      have hdist : dist z y < ε := by
        simp [z, dist_eq_norm, norm_smul, Real.norm_of_nonneg ht0.le]
        have htbound : t ≤ ε / (2 * (‖y - x‖ + 1)) := min_le_right _ _
        have hden : 0 < ‖y - x‖ + 1 := by positivity
        have : t * ‖y - x‖ ≤ ε / 2 := by
          calc
            t * ‖y - x‖ ≤ (ε / (2 * (‖y - x‖ + 1))) * ‖y - x‖ :=
              mul_le_mul_of_nonneg_right htbound (norm_nonneg _)
            _ ≤ (ε / (2 * (‖y - x‖ + 1))) * (‖y - x‖ + 1) := by
              gcongr; linarith [norm_nonneg (y - x)]
            _ = ε / 2 := by field_simp [hden.ne']
        linarith
      have hzF : z ∈ f := hball hdist
      have htne : 1 + t ≠ 0 := by linarith
      have hab : (1 + t)⁻¹ + t * (1 + t)⁻¹ = 1 := by field_simp [htne]
      have hz : z = (1 + t) • y - t • x := by
        dsimp [z]; module
      have hcomb : (1 + t)⁻¹ • z + (t * (1 + t)⁻¹) • x = y := by
        rw [hz, smul_sub, smul_smul, inv_mul_cancel₀ htne, one_smul, smul_smul,
          mul_comm (1 + t)⁻¹ t]
        simp
      have hseg : y ∈ openSegment ℝ z x :=
        ⟨(1 + t)⁻¹, t * (1 + t)⁻¹,
          inv_pos.mpr (by linarith),
          mul_pos ht0 (inv_pos.mpr (by linarith)), hab, hcomb⟩
      exact hF.isExtreme.right_mem_of_mem_openSegment (hsub hzF) hxp hyF hseg
    simpa [heq]
  · intro f hf
    have : f = p := by simpa using hf
    subst this
    exact ⟨isFaceOf_refl hConv, hdim⟩

theorem euler_relation_convex_3polytope [FiniteDimensional ℝ E] [Nonempty E]
    {H : Set (Hyperplane E)} {p : Set E}
    (hH : H.Finite)
    (hp : p = ⋂ h ∈ H, closedHalfspace h.1 h.2)
    (hP : IsPolytope p)
    (hdim : affDim p = 3)
    (hE : Module.finrank ℝ E = 3) :
    ({f : Set E | IsFaceOf p f ∧ affDim f = 0}.ncard : ℤ) -
      ({f : Set E | IsFaceOf p f ∧ affDim f = 1}.ncard : ℤ) +
      ({f : Set E | IsFaceOf p f ∧ affDim f = 2}.ncard : ℤ) = 2 := by
  have hn : 1 ≤ Module.finrank ℝ E := by rw [hE]; norm_num
  have hdim' : affDim p = Module.finrank ℝ E := by simpa [hE] using hdim
  have hsum := Euler_Poincare_full hH hp hP hdim' hn
  rw [hE] at hsum
  have hConv : Convex ℝ p := by obtain ⟨V, _, rfl⟩ := hP; exact convex_convexHull _ _
  have hSolid : ({f : Set E | IsFaceOf p f ∧ affDim f = 3}.ncard) = 1 := by
    have hEq : {f : Set E | IsFaceOf p f ∧ affDim f = 3} =
        {f : Set E | IsFaceOf p f ∧ affDim f = Module.finrank ℝ E} := by simp [hE]
    rw [hEq, faces_dim_eq_finrank_eq_singleton hConv hdim', ncard_singleton]
  exact euler_relation_of_faceEulerSum p _ _ _ hsum rfl rfl rfl hSolid

end EulersGem

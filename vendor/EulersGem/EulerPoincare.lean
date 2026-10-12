/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.ConeFaceCell
import EulersGem.SimplexEuler
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Cone → polytope lift toward Euler–Poincaré (Paulson)

Paulson AFP outline after `Euler_polyhedral_cone`:

1. **Slice lemma** (`Euler_Poincare_lemma`): cone faces ↔ height-1 slice faces via
   `conicHull`, and `faceEulerSum S n = 0` ⇒ `faceEulerSum p (n-1) = 1`.
2. **Embedding** (`Euler_Poincare_full`): full-dim polytope ↦ codim-1 in `E × ℝ`.
3. **3D** (`Euler_relation`): `faceEulerSum p 3 = 1` + unique solid ⇒ `V − E + F = 2`.

Landed here: conic-hull substrate, homogenization normals, **combinatorial cone→slice
reduction**, simplex face-sum `= 1`, and 3D bookkeeping. `ConeSlice.lean` discharges
the geometric bijection and height-1 EP. `Embed.lean` supplies the `E × ℝ` embedding
and `Euler_Poincare_full` / geometric 3D.
-/

open scoped RealInnerProductSpace BigOperators
open Classical Set Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace EulersGem

/-! ### Conic hull (Paulson `conic hull`) -/

/-- Nonnegative ray span of a set. Isabelle: `conic hull`. -/
def conicHull (s : Set E) : Set E :=
  {y | ∃ (c : ℝ) (x : E), 0 ≤ c ∧ x ∈ s ∧ y = c • x}

lemma subset_conicHull (s : Set E) : s ⊆ conicHull s :=
  fun x hx => ⟨1, x, zero_le_one, hx, (one_smul _ x).symm⟩

lemma isConic_conicHull (s : Set E) : IsConic (conicHull s) := by
  intro y hy t ht
  obtain ⟨c, x, hc, hx, rfl⟩ := hy
  exact ⟨t * c, x, mul_nonneg ht hc, hx, by rw [mul_smul]⟩

lemma zero_mem_conicHull {s : Set E} (hs : s.Nonempty) : (0 : E) ∈ conicHull s := by
  obtain ⟨x, hx⟩ := hs
  exact ⟨0, x, le_rfl, hx, (zero_smul _ x).symm⟩

lemma conicHull_mono {s t : Set E} (h : s ⊆ t) : conicHull s ⊆ conicHull t := by
  rintro _ ⟨c, x, hc, hx, rfl⟩
  exact ⟨c, x, hc, h hx, rfl⟩

/-- Recovering a point of height `1` from its ray. -/
lemma conicHull_inter_height_one {s : Set E} {i : E}
    (hs : ∀ x ∈ s, ⟪i, x⟫ = 1) :
    conicHull s ∩ {y : E | ⟪i, y⟫ = 1} = s := by
  apply subset_antisymm
  · rintro y ⟨⟨c, x, hc, hx, rfl⟩, hy⟩
    have : c * ⟪i, x⟫ = 1 := by
      simpa [inner_smul_right] using hy
    have hx1 : ⟪i, x⟫ = 1 := hs x hx
    have hc1 : c = 1 := by
      rw [hx1, mul_one] at this; exact this
    simpa [hc1] using hx
  · intro x hx
    exact ⟨subset_conicHull s hx, by simpa using hs x hx⟩

/-! ### Combinatorial cone → slice reduction -/

/-- Face bijection hypotheses for the Paulson cone→slice Euler identity. -/
structure ConeSliceFaceBijection (S p : Set E) (n : ℕ) : Prop where
  zero_face : {f : Set E | IsFaceOf S f ∧ affDim f = 0} = ({({0} : Set E)} : Set (Set E))
  faces_succ :
    ∀ d : ℕ, d < n →
      {f : Set E | IsFaceOf S f ∧ affDim f = ((d + 1 : ℕ) : ℤ)} =
        conicHull '' {F : Set E | IsFaceOf p F ∧ affDim F = (d : ℤ)}
  conic_inj :
    ∀ d : ℕ, d < n →
      InjOn conicHull {F : Set E | IsFaceOf p F ∧ affDim F = (d : ℤ)}

/-- Cone Euler sum `0` + face bijection ⇒ slice Euler sum `1`.
Paulson `Euler_Poincare_lemma` bookkeeping. -/
theorem faceEulerSum_slice_of_cone {S p : Set E} {n : ℕ}
    (hBij : ConeSliceFaceBijection S p n)
    (hCone : faceEulerSum S n = 0)
    (hn : 1 ≤ n) :
    faceEulerSum p (n - 1) = 1 := by
  classical
  have h0 :
      ({f : Set E | IsFaceOf S f ∧ affDim f = (0 : ℤ)}).ncard = 1 := by
    rw [hBij.zero_face, ncard_singleton]
  -- sum_range_succ': ∑_{k=0}^n f k = (∑_{d=0}^{n-1} f (d+1)) + f 0
  have hsplit :
      faceEulerSum S n =
        (1 : ℤ) +
          ∑ d ∈ range n,
            (-1 : ℤ) ^ (d + 1) *
              ({f : Set E | IsFaceOf S f ∧ affDim f = ((d + 1 : ℕ) : ℤ)}.ncard : ℤ) := by
    unfold faceEulerSum
    rw [sum_range_succ']
    -- Goal: ∑ term(d+1) + term 0 = 1 + ∑ term(d+1)
    have hterm0 :
        (-1 : ℤ) ^ (0 : ℕ) *
            ({f : Set E | IsFaceOf S f ∧ affDim f = ((0 : ℕ) : ℤ)}.ncard : ℤ) = 1 := by
      simpa using congrArg (fun n : ℕ => (n : ℤ)) h0
    rw [hterm0, add_comm]
  have hrewritten :
      faceEulerSum S n =
        (1 : ℤ) +
          ∑ d ∈ range n,
            (-1 : ℤ) ^ (d + 1) *
              ({F : Set E | IsFaceOf p F ∧ affDim F = (d : ℤ)}.ncard : ℤ) := by
    rw [hsplit]
    congr 1
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd' : d < n := Finset.mem_range.mp hd
    have hEq := hBij.faces_succ d hd'
    have hinj := hBij.conic_inj d hd'
    rw [hEq, hinj.ncard_image]
  have hrel : faceEulerSum S n = 1 - faceEulerSum p (n - 1) := by
    rw [hrewritten]
    unfold faceEulerSum
    have hrange : range ((n - 1) + 1) = range n := by
      rw [Nat.sub_add_cancel hn]
    rw [hrange]
    have hneg :
        ∑ d ∈ range n,
            (-1 : ℤ) ^ (d + 1) *
              ({F : Set E | IsFaceOf p F ∧ affDim F = (d : ℤ)}.ncard : ℤ) =
          -∑ d ∈ range n,
              (-1 : ℤ) ^ d *
                ({F : Set E | IsFaceOf p F ∧ affDim F = (d : ℤ)}.ncard : ℤ) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [pow_succ]; ring
    rw [hneg]; ring
  linarith

/-! ### Homogenization normals -/

/-- Homogeneous normals for the cone over a height-1 slice of an H-rep polyhedron. -/
def homogenizeNormals (H : Set (Hyperplane E)) (i : E) : Set E :=
  (fun h : Hyperplane E => h.1 - h.2 • i) '' H ∪ {(-i)}

lemma homogenizeNormals_finite {H : Set (Hyperplane E)} (hH : H.Finite) (i : E) :
    (homogenizeNormals H i).Finite :=
  (hH.image _).union (finite_singleton _)

/-! ### Simplex combinatorial Euler–Poincaré -/

/-- `∑_{d=0}^{n} (-1)^d C(n+1, d+1) = 1`. -/
theorem faceEulerSum_simplex_faceCount (n : ℕ) :
    ∑ d ∈ range (n + 1), (-1 : ℤ) ^ d * (faceCount n d : ℤ) = 1 := by
  have hbin :
      ∑ j ∈ range (n + 2), (-1 : ℤ) ^ j * ((n + 1).choose j : ℤ) = 0 := by
    have hne : n + 1 ≠ 0 := Nat.succ_ne_zero n
    simpa [Nat.add_assoc] using (Int.alternating_sum_range_choose_of_ne hne)
  -- sum_range_succ': … + 1 = 0 at the end
  have hpeel :
      ∑ j ∈ range (n + 1),
          (-1 : ℤ) ^ (j + 1) * ((n + 1).choose (j + 1) : ℤ) + 1 = 0 := by
    rw [sum_range_succ'] at hbin
    simpa [pow_zero, one_mul] using hbin
  have hneg :
      ∑ j ∈ range (n + 1),
          (-1 : ℤ) ^ (j + 1) * ((n + 1).choose (j + 1) : ℤ) =
        -∑ j ∈ range (n + 1),
            (-1 : ℤ) ^ j * ((n + 1).choose (j + 1) : ℤ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ]; ring
  have : ∑ d ∈ range (n + 1),
      (-1 : ℤ) ^ d * ((n + 1).choose (d + 1) : ℤ) = 1 := by
    linarith
  simpa [faceCount] using this

/-! ### 3D Euler relation from faceEulerSum = 1 -/

private lemma faceEulerSum_three_expand (p : Set E) :
    faceEulerSum p 3 =
      ({f : Set E | IsFaceOf p f ∧ affDim f = 0}.ncard : ℤ) -
        ({f : Set E | IsFaceOf p f ∧ affDim f = 1}.ncard : ℤ) +
        ({f : Set E | IsFaceOf p f ∧ affDim f = 2}.ncard : ℤ) -
        ({f : Set E | IsFaceOf p f ∧ affDim f = 3}.ncard : ℤ) := by
  unfold faceEulerSum
  rw [show range 4 = ({0, 1, 2, 3} : Finset ℕ) from by decide]
  simp [Finset.sum_insert, Finset.sum_singleton, pow_succ]
  ring

/-- If a 3-polytope has `faceEulerSum = 1` and a unique solid 3-face, then `V − E + F = 2`. -/
theorem euler_relation_of_faceEulerSum
    (p : Set E) (V E_ F : ℕ)
    (hsum : faceEulerSum p 3 = 1)
    (hV : ({f : Set E | IsFaceOf p f ∧ affDim f = 0}.ncard) = V)
    (hE : ({f : Set E | IsFaceOf p f ∧ affDim f = 1}.ncard) = E_)
    (hF : ({f : Set E | IsFaceOf p f ∧ affDim f = 2}.ncard) = F)
    (hSolid : ({f : Set E | IsFaceOf p f ∧ affDim f = 3}.ncard) = 1) :
    (V : ℤ) - E_ + F = 2 := by
  have hexpand := faceEulerSum_three_expand p
  rw [hexpand, hV, hE, hF, hSolid, Nat.cast_one] at hsum
  linarith

/-- Tetrahedron face counts: `V − E + F = 2`. -/
theorem tetrahedron_euler_relation_from_faceCount :
    (faceCount 3 0 : ℤ) - faceCount 3 1 + faceCount 3 2 = 2 := by
  decide

/-! ### Stated targets -/

def EulerPoincareLemmaGoal : String :=
  "faceEulerSum (S ∩ {⟪i,·⟫ = 1}) (n-1) = 1 when ConeSliceFaceBijection holds"

def EulerPoincareFullGoal' : String :=
  "faceEulerSum p (finrank) = 1 for full-dimensional convex polytopes"

/-! ### Apex face via a strictly positive height functional -/

/-- If every nonzero point of a convex set `S` has strictly positive height `⟪i,·⟫`,
then `{0}` is a face of `S` (Paulson apex for cones over height-1 polytopes). -/
lemma isFaceOf_singleton_zero_of_height {S : Set E} {i : E}
    (_hConv : Convex ℝ S) (h0 : (0 : E) ∈ S)
    (hpos : ∀ x ∈ S, x ≠ 0 → 0 < ⟪i, x⟫) :
    IsFaceOf S ({0} : Set E) := by
  refine ⟨⟨by simpa using h0, ?_⟩, convex_singleton (0 : E)⟩
  intro x hxS y hyS z hzFace hzSeg
  have hz0 : z = 0 := by simpa using hzFace
  obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hzSeg
  have hsum : a • x + b • y = 0 := by simpa [hz0] using hcomb
  have hinner : a * ⟪i, x⟫ + b * ⟪i, y⟫ = 0 := by
    have := congrArg (fun w => ⟪i, w⟫) hsum
    simpa [inner_add_right, inner_smul_right] using this
  have hx0 : x = 0 := by
    by_contra hxne
    have hxpos : 0 < ⟪i, x⟫ := hpos x hxS hxne
    have hy_le : 0 ≤ ⟪i, y⟫ := by
      by_cases hy0 : y = 0
      · subst hy0; simp
      · exact le_of_lt (hpos y hyS hy0)
    have : 0 < a * ⟪i, x⟫ + b * ⟪i, y⟫ := by
      have h1 : 0 < a * ⟪i, x⟫ := mul_pos ha hxpos
      have h2 : 0 ≤ b * ⟪i, y⟫ := mul_nonneg hb.le hy_le
      linarith
    linarith
  exact hx0

/-- On a cone with strictly positive height off the apex, every singleton face is `{0}`. -/
lemma eq_zero_of_singleton_face_of_isConic {S : Set E} {a : E}
    (hS : IsConic S)
    (hFace : IsFaceOf S ({a} : Set E)) :
    a = 0 := by
  have haS : a ∈ S := hFace.isExtreme.subset (by simp)
  by_contra hne
  -- 2•a and (1/2)•a are in S; a lies in the open segment between them
  have h2 : (2 : ℝ) • a ∈ S := hS haS (2 : ℝ) (by norm_num)
  have hhalf : ((1 : ℝ) / 2) • a ∈ S := hS haS ((1 : ℝ) / 2) (by norm_num)
  have hseg : a ∈ openSegment ℝ (((1 : ℝ) / 2) • a) ((2 : ℝ) • a) := by
    refine ⟨(2 : ℝ) / 3, (1 : ℝ) / 3, by norm_num, by norm_num, by norm_num, ?_⟩
    module
  -- Extremality forces both endpoints into {a}, so 2•a = a, contradiction
  have h2eq : (2 : ℝ) • a = a := by
    have := hFace.isExtreme.right_mem_of_mem_openSegment hhalf h2 (by simp : a ∈ ({a} : Set E)) hseg
    simpa using this
  have : (2 : ℝ) • a ≠ a := by
    intro h
    have ha0 : a = 0 := by
      have : a + a - a = 0 := by
        rw [← two_smul ℝ a, h, sub_self]
      simpa using this
    exact hne ha0
  exact this h2eq


/-- Under strict positive height, every nonempty face of affine dimension `0` is `{0}`.
This discharges `ConeSliceFaceBijection.zero_face` once one knows all `0`-faces are singletons
(automatic for convex sets: `affDim = 0` ⇒ singleton). -/
lemma faces_dim_zero_eq_singleton_zero {S : Set E} {i : E}
    (hS : IsConic S) (hConv : Convex ℝ S) (h0 : (0 : E) ∈ S)
    (hpos : ∀ x ∈ S, x ≠ 0 → 0 < ⟪i, x⟫)
    (hSing : ∀ f, IsFaceOf S f → affDim f = 0 → ∃ a, f = {a}) :
    {f : Set E | IsFaceOf S f ∧ affDim f = 0} = ({({0} : Set E)} : Set (Set E)) := by
  apply subset_antisymm
  · intro f ⟨hFace, hdim⟩
    obtain ⟨a, rfl⟩ := hSing f hFace hdim
    have ha0 := eq_zero_of_singleton_face_of_isConic hS hFace
    subst ha0
    rfl
  · intro f hf
    have : f = ({0} : Set E) := by simpa using hf
    subst this
    refine ⟨isFaceOf_singleton_zero_of_height hConv h0 hpos, ?_⟩
    simp [affDim_singleton]



end EulersGem

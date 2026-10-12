/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Order
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Convert

/-!
# Finite elimination of linear inequalities

A proof of Fourier–Motzkin elimination over the reals. These lemmas concern
finite systems of actual linear inequalities, with no geometric assumptions.
-/

open Set

namespace EulerPolyhedron

private theorem finite_between (L U : Finset ℝ)
    (h : ∀ l ∈ L, ∀ u ∈ U, l ≤ u) :
    ∃ t : ℝ, (∀ l ∈ L, l ≤ t) ∧ (∀ u ∈ U, t ≤ u) := by
  classical
  induction L using Finset.induction_on with
  | empty =>
    obtain ⟨t, ht⟩ := Finset.exists_le (α := OrderDual ℝ) U
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

/-- Eliminate one real unknown from finitely many scalar inequalities. -/
theorem exists_scalar_iff {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    (∃ t : ℝ, ∀ i ∈ s, a i * t ≤ b i) ↔
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
      have h₁ := mul_le_mul_of_nonneg_left (ht i hi) haj.le
      have h₂ := mul_le_mul_of_nonpos_left (ht j hj) hai.le
      nlinarith
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
      nlinarith [hp i hi j hj hai haj]
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

variable (E : Type*) [AddCommGroup E] [Module ℝ E]

/-- A finite intersection of affine closed halfspaces, expressed by linear functionals. -/
def Polyhedral (s : Set E) : Prop :=
  ∃ S : Finset ((E →ₗ[ℝ] ℝ) × ℝ), s = {x | ∀ q ∈ S, q.1 x ≤ q.2}

variable {E}

private def tailMap (q : ((ℝ × E) →ₗ[ℝ] ℝ) × ℝ) : (E →ₗ[ℝ] ℝ) × ℝ :=
  (q.1.comp (LinearMap.inr ℝ ℝ E), q.2)

private def eliminatePair (q r : ((ℝ × E) →ₗ[ℝ] ℝ) × ℝ) :
    (E →ₗ[ℝ] ℝ) × ℝ :=
  (r.1 (1, 0) • (tailMap q).1 - q.1 (1, 0) • (tailMap r).1,
    r.1 (1, 0) * q.2 - q.1 (1, 0) * r.2)

private theorem split_apply (f : (ℝ × E) →ₗ[ℝ] ℝ) (t : ℝ) (x : E) :
    f (t, x) = f (1, 0) * t + f (0, x) := by
  have h : (t, x) = t • (1, (0 : E)) + (0, x) := by simp
  rw [h, map_add, map_smul]
  simp [mul_comm]

/-- The projection of a finite system of inequalities along one real coordinate
is another finite system of inequalities. -/
theorem Polyhedral.project {s : Set (ℝ × E)} (hs : Polyhedral (ℝ × E) s) :
    Polyhedral E {x | ∃ t : ℝ, (t, x) ∈ s} := by
  classical
  obtain ⟨S, rfl⟩ := hs
  let Z := S.filter fun q => q.1 (1, 0) = 0
  let P := (S.product S).filter fun qr => qr.1.1 (1, 0) < 0 ∧ 0 < qr.2.1 (1, 0)
  let T := Z.image tailMap ∪ P.image fun qr => eliminatePair qr.1 qr.2
  refine ⟨T, ?_⟩
  ext x
  change (∃ t : ℝ, ∀ q ∈ S, q.1 (t, x) ≤ q.2) ↔ _
  have hsplit (t : ℝ) (q : ((ℝ × E) →ₗ[ℝ] ℝ) × ℝ) :
      q.1 (t, x) ≤ q.2 ↔ q.1 (1, 0) * t ≤ q.2 - q.1 (0, x) := by
    rw [split_apply]
    constructor <;> intro h <;> linarith
  simp_rw [hsplit]
  rw [exists_scalar_iff]
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
      fun q hq r hr hn hpos => by nlinarith [hp q hq r hr hn hpos]⟩
  · rintro ⟨hz, hp⟩
    exact ⟨fun q hq h0 => by linarith [hz q hq h0],
      fun q hq r hr hn hpos => by nlinarith [hp q hq r hr hn hpos]⟩

/-- Finite families of linear inequalities are polyhedral. -/
theorem Polyhedral.of_finite {ι : Type*} [Fintype ι]
    (L : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) :
    Polyhedral E {x | ∀ i, L i x ≤ b i} := by
  classical
  refine ⟨Finset.univ.image (fun i => (L i, b i)), ?_⟩
  ext x
  simp

/-- Linear inverse images preserve finite halfspace presentations. -/
theorem Polyhedral.preimage {F : Type*} [AddCommGroup F] [Module ℝ F]
    {s : Set E} (hs : Polyhedral E s) (f : F →ₗ[ℝ] E) :
    Polyhedral F (f ⁻¹' s) := by
  classical
  obtain ⟨S, rfl⟩ := hs
  refine ⟨S.image (fun q => (q.1.comp f, q.2)), ?_⟩
  ext x
  change (∀ q ∈ S, q.1 (f x) ≤ q.2) ↔ _
  simp only [mem_ofPred_eq, Finset.forall_mem_image, LinearMap.comp_apply]

/-- Intersections preserve finite halfspace presentations. -/
theorem Polyhedral.inter {s t : Set E} (hs : Polyhedral E s) (ht : Polyhedral E t) :
    Polyhedral E (s ∩ t) := by
  classical
  obtain ⟨S, rfl⟩ := hs
  obtain ⟨T, rfl⟩ := ht
  refine ⟨S ∪ T, ?_⟩
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq, Finset.forall_mem_union]

private def consLinear (n : ℕ) :
    (ℝ × ((Fin n → ℝ) × E)) →ₗ[ℝ] ((Fin (n + 1) → ℝ) × E) where
  toFun y := (Fin.cons y.1 y.2.1, y.2.2)
  map_add' a b := by
    apply Prod.ext
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    · rfl
  map_smul' t a := by
    apply Prod.ext
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    · rfl

/-- Eliminate any finite number of auxiliary real coordinates. -/
theorem Polyhedral.project_fin (n : ℕ) {s : Set ((Fin n → ℝ) × E)}
    (hs : Polyhedral ((Fin n → ℝ) × E) s) :
    Polyhedral E {x | ∃ w : Fin n → ℝ, (w, x) ∈ s} := by
  induction n with
  | zero =>
    let f : E →ₗ[ℝ] ((Fin 0 → ℝ) × E) := LinearMap.inr ℝ (Fin 0 → ℝ) E
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
    change (∃ w : Fin (n + 1) → ℝ, (w, x) ∈ s) ↔
      ∃ w : Fin n → ℝ, ∃ t : ℝ, (Fin.cons t w, x) ∈ s
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨Fin.tail w, w 0, by simpa only [Fin.cons_self_tail] using hw⟩
    · rintro ⟨w, t, ht⟩
      exact ⟨Fin.cons t w, ht⟩

end EulerPolyhedron

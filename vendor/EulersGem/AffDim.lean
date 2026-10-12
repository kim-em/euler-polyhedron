/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.Dimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Set-level affine dimension (Isabelle `aff_dim`)

Mathlib exposes `AffineSubspace.finDim : WithBot ℕ` (empty subspace ↦ `⊥`).
Paulson's development applies `aff_dim` to arbitrary *sets* via the affine hull,
returning an integer with `aff_dim ∅ = -1`.

This module is the thin wrapper needed for combinatorial Euler sums
`∑ (-1)^{affDim C}` over hyperplane cells.
-/

open Set AffineSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace EulersGem

/-- Affine dimension of a set, Isabelle-style:
* empty set ↦ `-1`
* otherwise ↦ `finDim` of its affine span (as `ℤ`).

Junk value `0` when the direction is infinite-dimensional (inherited from
`Module.finrank` / `AffineSubspace.finDim`). Prefer a `[FiniteDimensional ℝ E]`
context for Euler-characteristic arguments. -/
noncomputable def affDim (s : Set E) : ℤ :=
  match (affineSpan ℝ s).finDim with
  | ⊥ => -1
  | (n : ℕ) => n

@[simp] lemma affDim_empty : affDim (∅ : Set E) = -1 := by
  simp [affDim, span_empty, finDim_bot]

@[simp] lemma affDim_singleton (x : E) : affDim ({x} : Set E) = 0 := by
  simp [affDim, affineSpan_singleton, finDim_singleton]

lemma affDim_eq_neg_one_iff_empty (s : Set E) : affDim s = -1 ↔ s = ∅ := by
  constructor
  · intro h
    by_contra hs
    have hne : s.Nonempty := nonempty_iff_ne_empty.mpr hs
    have hspanNe : (affineSpan ℝ s : Set E).Nonempty :=
      (affineSpan_nonempty (k := ℝ) (V := E) (P := E)).mpr hne
    have hneBot : affineSpan ℝ s ≠ ⊥ := (nonempty_iff_ne_bot _).mp hspanNe
    cases hfd : (affineSpan ℝ s).finDim with
    | bot => exact absurd (finDim_eq_bot_iff.mp hfd) hneBot
    | coe n =>
      simp only [affDim, hfd] at h
      have : (0 : ℤ) ≤ (n : ℤ) := Nat.cast_nonneg n
      omega
  · rintro rfl; simp

lemma affDim_nonneg_of_nonempty {s : Set E} (hs : s.Nonempty) : 0 ≤ affDim s := by
  have hspanNe : (affineSpan ℝ s : Set E).Nonempty :=
    (affineSpan_nonempty (k := ℝ) (V := E) (P := E)).mpr hs
  have hneBot : affineSpan ℝ s ≠ ⊥ := (nonempty_iff_ne_bot _).mp hspanNe
  cases hfd : (affineSpan ℝ s).finDim with
  | bot => exact absurd (finDim_eq_bot_iff.mp hfd) hneBot
  | coe n => simp [affDim, hfd]

lemma affineSpan_univ [Nonempty E] : affineSpan ℝ (univ : Set E) = ⊤ :=
  top_unique fun x _ => mem_affineSpan ℝ (mem_univ x)

/-- On a finite-dimensional space, the whole space has affine dimension `finrank`. -/
lemma affDim_univ [FiniteDimensional ℝ E] [Nonempty E] :
    affDim (univ : Set E) = Module.finrank ℝ E := by
  have htop := affineSpan_univ (E := E)
  have hneBot : (⊤ : AffineSubspace ℝ E) ≠ ⊥ := bot_ne_top.symm
  have hfd : (⊤ : AffineSubspace ℝ E).finDim =
      (Module.finrank ℝ E : WithBot ℕ) := by
    rw [finDim_eq_finrank hneBot, direction_top, finrank_top]
  simp only [affDim, htop]
  cases hmatch : (⊤ : AffineSubspace ℝ E).finDim with
  | bot => exact absurd (finDim_eq_bot_iff.mp hmatch) hneBot
  | coe n =>
    rw [hmatch] at hfd
    have : n = Module.finrank ℝ E := WithBot.coe_inj.mp hfd
    simp [this]

end EulersGem

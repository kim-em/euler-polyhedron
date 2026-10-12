/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card

/-!
# Face counts for simplices

Vocabulary mirroring Michal's Isabelle `Poly100.thy` (`d_faces`, `d_face_count`),
in combinatorial form (vertex subsets). Geometric faces via Mathlib
`Affine.Simplex.face` can be wired later; Paulson AFP is the primary general path.
-/

namespace EulersGem

/-- Number of `m`-faces of an abstract `n`-simplex (by vertex subsets). -/
def faceCount (n m : ℕ) : ℕ := (n + 1).choose (m + 1)

/-- The empty face is unique. -/
def emptyFaceCount : ℕ := 1

lemma faceCount_eq_choose (n m : ℕ) : faceCount n m = (n + 1).choose (m + 1) := rfl

@[simp] lemma faceCount_of_lt {n m : ℕ} (h : n < m) : faceCount n m = 0 := by
  unfold faceCount
  exact Nat.choose_eq_zero_of_lt (Nat.succ_lt_succ h)

@[simp] lemma faceCount_self (n : ℕ) : faceCount n n = 1 := by
  simp [faceCount]

@[simp] lemma faceCount_zero (n : ℕ) : faceCount n 0 = n + 1 := by
  simp [faceCount]

/-- Vertex subsets of size `m+1` indexing the combinatorial `m`-faces of an `n`-simplex. -/
def combinatorialFaces (n m : ℕ) : Finset (Finset (Fin (n + 1))) :=
  Finset.powersetCard (m + 1) (Finset.univ : Finset (Fin (n + 1)))

lemma card_combinatorialFaces (n m : ℕ) :
    (combinatorialFaces n m).card = faceCount n m := by
  simp [combinatorialFaces, faceCount, Finset.card_univ]

end EulersGem

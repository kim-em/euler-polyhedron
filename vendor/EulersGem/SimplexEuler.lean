/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.Faces
import Mathlib.Data.Nat.Choose.Sum

/-!
# Euler characteristic of a simplex

Following Isabelle `Poly100.thy` (`euler_char`, `euler_nsimplex_eq0`):

The Euler characteristic of an `n`-simplex, **including the empty face**, is

```
∑_{c = 0}^{n+1} (-1)^c · C(n+1, c)
```

where the summand for `c` counts faces with `c` vertices (affine dimension `c-1`).
This equals `0` for every `n`.

This is the combinatorial special case; the general polytope theorem follows the
Paulson AFP route (hyperplane arrangements) — see `Polyhedron.lean`.
-/

open Finset

namespace EulersGem

/-- Euler characteristic of an `n`-simplex, including the empty face.

Index `c` runs over vertex-counts `0, …, n+1` (affine dimensions `-1, …, n`),
with sign `(-1)^c`. Matches Isabelle's `euler_char` for simplices. -/
def eulerChar (n : ℕ) : ℤ :=
  ∑ c ∈ range (n + 2), ((-1 : ℤ) ^ c) * ((n + 1).choose c : ℤ)

/-- **Main proved theorem (simplex case):** Euler characteristic of any `n`-simplex is `0`.

Corresponds to Isabelle `euler_0simplex_eq0` / `euler_nsimplex_eq0` and the binomial
identity `∑_{c=0}^{n+1} (-1)^c C(n+1,c) = 0` for `n+1 ≠ 0`. -/
theorem eulerChar_simplex (n : ℕ) : eulerChar n = 0 := by
  unfold eulerChar
  have hne : n + 1 ≠ 0 := Nat.succ_ne_zero n
  -- `range (n+2)` = `range ((n+1)+1)`; apply Mathlib alternating-sum identity
  simpa [Nat.add_assoc] using (Int.alternating_sum_range_choose_of_ne hne)

/-- Classical 3-simplex (tetrahedron) check: `1 - 4 + 6 - 4 + 1 = 0`. -/
example : eulerChar 3 = 0 := eulerChar_simplex 3

/-- Face counts of a tetrahedron: 4 vertices, 6 edges, 4 triangles, 1 cell. -/
example : faceCount 3 0 = 4 ∧ faceCount 3 1 = 6 ∧ faceCount 3 2 = 4 ∧ faceCount 3 3 = 1 := by
  decide

/-- From face counts, the classical `V - E + F = 2` for a tetrahedron
(excluding empty face and the solid itself): `4 - 6 + 4 = 2`. -/
theorem tetrahedron_polyhedron_numbers :
    (faceCount 3 0 : ℤ) - faceCount 3 1 + faceCount 3 2 = 2 := by
  decide

end EulersGem

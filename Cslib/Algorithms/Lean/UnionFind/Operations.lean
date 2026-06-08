/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module

public import Cslib.Init
public import Cslib.Algorithms.Lean.UnionFind.Basic

/-!
# Union-Find Operations

This file constructs the initial `singleton` forest, in which every element is its own
root with rank `0`, and proves it well-formed. This witnesses that the `WellFormed`
hypothesis used throughout the rank-bound development is satisfiable, so the
`findDepth_le_log` bound is non-vacuous.

## Main definitions

* `UnionFind.singleton`: The forest where every element is its own root with rank `0`.

## Main results

* `UnionFind.singleton_wellFormed`: The singleton forest is well-formed.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UnionFind

variable {n : ℕ}

/-- The forest where every element is its own root with rank `0`. -/
def singleton (n : ℕ) : UnionFind n where
  parent := id
  rank := fun _ => 0

/-- The parent function of the singleton forest is the identity. -/
@[simp] lemma singleton_parent (i : Fin n) : (singleton n).parent i = i := rfl

/-- Every element of a singleton forest is a root. -/
@[simp] lemma singleton_isRoot (i : Fin n) : (singleton n).IsRoot i := rfl

/-- The singleton forest is well-formed, so the `WellFormed` hypothesis is satisfiable. -/
theorem singleton_wellFormed : (singleton n).WellFormed where
  rank_lt i h := absurd (singleton_isRoot i) h
  size_ge i := by
    change 2 ^ 0 ≤ (singleton n).subtreeSize i
    simp only [Nat.pow_zero]
    exact (singleton n).one_le_subtreeSize i

end Cslib.Algorithms.Lean.UnionFind

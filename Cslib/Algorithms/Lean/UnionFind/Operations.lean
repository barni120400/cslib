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

It also defines the `link` operation (union by rank) and the reusable helper lemmas about
reachability under a parent-pointer `Function.update` that underpin its correctness.

## Main definitions

* `UnionFind.singleton`: The forest where every element is its own root with rank `0`.
* `UnionFind.link`: Union by rank, attaching the lower-rank root under the higher-rank one.

## Main results

* `UnionFind.singleton_wellFormed`: The singleton forest is well-formed.
* `UnionFind.iterate_parent_isRoot`: Following parents from a root stays at that root.
* `UnionFind.reaches_root_unique`: Each node reaches a unique root.
* `UnionFind.iterate_update_eq_of_forall_ne`: Updating a parent pointer leaves a path
  unchanged as long as the path avoids the updated key.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UnionFind

variable {n : ℕ} (uf : UnionFind n)

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

/-- Link two roots `a` and `b` using union by rank: attach the lower-rank root under the
  higher-rank one; on a tie, attach `a` under `b` and increment `b`'s rank. Only the parent of
  the demoted root, and (on a tie) the rank of `b`, change. -/
def link (uf : UnionFind n) (a b : Fin n) : UnionFind n :=
  if uf.rank a < uf.rank b then
    { uf with parent := Function.update uf.parent a b }
  else if uf.rank b < uf.rank a then
    { uf with parent := Function.update uf.parent b a }
  else
    { uf with
      parent := Function.update uf.parent a b
      rank := Function.update uf.rank b (uf.rank b + 1) }

/-- Following parents from a root stays at that root. -/
lemma iterate_parent_isRoot {x : Fin n} (hx : uf.IsRoot x) (m : ℕ) :
    uf.parent^[m] x = x := by
  induction m with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; exact hx

/-- A node reaches at most one root: the root reached by following parents is unique. -/
lemma reaches_root_unique {j r₁ r₂ : Fin n}
    (h₁ : uf.reaches j r₁) (hr₁ : uf.IsRoot r₁)
    (h₂ : uf.reaches j r₂) (hr₂ : uf.IsRoot r₂) : r₁ = r₂ := by
  obtain ⟨k₁, hk₁⟩ := h₁
  obtain ⟨k₂, hk₂⟩ := h₂
  rcases le_total k₁ k₂ with hle | hle
  · have heq : uf.parent^[k₂] j = uf.parent^[k₂ - k₁] (uf.parent^[k₁] j) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle]
    rw [hk₁, uf.iterate_parent_isRoot hr₁] at heq
    rw [hk₂] at heq
    exact heq.symm
  · have heq : uf.parent^[k₁] j = uf.parent^[k₁ - k₂] (uf.parent^[k₂] j) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle]
    rw [hk₂, uf.iterate_parent_isRoot hr₂] at heq
    rw [hk₁] at heq
    exact heq

/-- Iterating an updated parent function agrees with the original as long as the path from
`j` never visits the updated key `a` (within the first `k` steps). -/
lemma iterate_update_eq_of_forall_ne {p : Fin n → Fin n} {a b j : Fin n} {k : ℕ}
    (h : ∀ m, m < k → p^[m] j ≠ a) :
    (Function.update p a b)^[k] j = p^[k] j := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih (fun m hm => h m (by omega))]
    exact Function.update_of_ne (h k (by omega)) b p

end Cslib.Algorithms.Lean.UnionFind

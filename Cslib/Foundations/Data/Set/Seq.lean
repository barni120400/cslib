/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/
module

public import Cslib.Init
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Seq.Basic
public import Mathlib.Data.Set.Card

/-!
# Increasing enumeration of a set of natural numbers

`Set.toSeq` lists the elements of a set in increasing order, as a possibly infinite sequence.
-/

@[expose] public section

namespace Set

/-- The elements of a set of natural numbers in increasing order. -/
noncomputable def toSeq (s : Set ℕ) : Stream'.Seq ℕ := by
  classical
  refine ⟨fun n => if (n : ℕ∞) < s.encard then some (Nat.nth (· ∈ s) n) else none, ?_⟩
  intro n
  simp only [ite_eq_right_iff, Option.some_ne_none, imp_false, not_lt]
  exact fun h => h.trans (by exact_mod_cast Nat.le_succ n)

/-- The enumeration has no entry at `n` exactly when the set has at most `n` elements. -/
@[simp]
lemma terminatedAt_toSeq (s : Set ℕ) (n : ℕ) :
    s.toSeq.TerminatedAt n ↔ s.encard ≤ n := by
  classical
  simp [toSeq, Stream'.Seq.TerminatedAt, Stream'.Seq.get?, not_lt]

/-- The index of an element is the number of elements of the set strictly below it. -/
lemma get?_toSeq {s : Set ℕ} [DecidablePred (· ∈ s)] {n t : ℕ} :
    s.toSeq.get? n = some t ↔ t ∈ s ∧ Nat.count (· ∈ s) t = n := by
  classical
  constructor
  · intro h
    have hn : (n : ℕ∞) < s.encard := by
      by_contra hn
      simp [toSeq, Stream'.Seq.get?, hn] at h
    have hn' (hf : s.Finite) : n < hf.toFinset.card := by
      simpa only [hf.encard_eq_coe_toFinset_card, ENat.natCast_lt_natCast] using hn
    have hnt : Nat.nth (· ∈ s) n = t := by simpa [toSeq, Stream'.Seq.get?, hn] using h
    rw [← hnt]
    exact ⟨Nat.nth_mem n hn', Nat.count_nth hn'⟩
  · rintro ⟨ht, rfl⟩
    have hn : (Nat.count (· ∈ s) t : ℕ∞) < s.encard := by
      by_cases hf : s.Finite
      · simpa only [hf.encard_eq_coe_toFinset_card, ENat.natCast_lt_natCast] using
          Nat.count_lt_card (p := (· ∈ s)) hf ht
      · simp [Set.Infinite.encard_eq hf]
    simp [toSeq, Stream'.Seq.get?, hn, Nat.nth_count ht]

/-- Equal sequences indexed by increasing enumerations pair the indices in order. -/
lemma exists_orderIso_of_toSeq_map_eq {α : Type*} {s t : Set ℕ} {f g : ℕ → α}
    (hseq : s.toSeq.map f = t.toSeq.map g) :
    ∃ e : s ≃o t, ∀ i : s, f i = g (e i) := by
  classical
  have hmatch (i : s) : ∃ j : t,
      Nat.count (· ∈ s) i = Nat.count (· ∈ t) j ∧ f i = g j := by
    have h := congrArg (·.get? (Nat.count (· ∈ s) i)) hseq
    rw [Stream'.Seq.map_get?, get?_toSeq.mpr ⟨i.property, rfl⟩, Option.map_some,
      Stream'.Seq.map_get?] at h
    obtain ⟨j, hj, hfg⟩ := Option.map_eq_some_iff.mp h.symm
    obtain ⟨hj, hn⟩ := get?_toSeq.mp hj
    exact ⟨⟨j, hj⟩, hn.symm, hfg.symm⟩
  choose e he hfg using hmatch
  have hmono : StrictMono e := fun i j h => Nat.lt_of_count_lt_count (by
    rw [← he i, ← he j]
    exact Nat.count_strict_mono i.property h)
  have hsurj : Function.Surjective e := by
    intro j
    have h := congrArg (·.get? (Nat.count (· ∈ t) j)) hseq
    rw [Stream'.Seq.map_get?, Stream'.Seq.map_get?,
      get?_toSeq.mpr ⟨j.property, rfl⟩, Option.map_some] at h
    obtain ⟨i, hi, _⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hi, hn⟩ := get?_toSeq.mp hi
    exact ⟨⟨i, hi⟩, Subtype.ext (Nat.count_injective (e ⟨i, hi⟩).property j.property
      ((he ⟨i, hi⟩).symm.trans hn))⟩
  exact ⟨OrderIso.ofSurjective (OrderEmbedding.ofStrictMono e hmono) hsurj, hfg⟩

end Set

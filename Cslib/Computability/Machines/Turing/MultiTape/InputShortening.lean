/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.ConfigBound
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Seq.Basic
public import Mathlib.Order.Atoms.Finite
public import Mathlib.Order.Cover
public import Mathlib.Order.Interval.Basic

/-!
# Input shortening for multi-tape Turing machines

Consider a deterministic Turing machine and an input on which it halts. For each input cell,
we record the sequence of space configurations (`Storage`) at the times when the input head
visits that cell. We show that if two distinct cells contain the same symbol and have the same
sequence, then the run on the input obtained by deleting the symbols after the first cell through
the second reaches every space configuration reached by the original run while its input head
is outside the deleted interval. This property is the main ingredient in the proof of
`SPACE(o(log log n)) = SPACE(1)`.

## Main definitions

* `visitTimes`: all times at which a run's input head is at a given position.
* `visitSequence`: the sequence of space configurations at those times, in chronological order.
* `InputCut`: an ordered pair of input-symbol indices describing the endpoints of a deletion.
* `InputCut.left`, `InputCut.right`: the corresponding input-head positions.
* `InputCut.shortened`: the input with the symbols after the first endpoint through the second
  deleted.
* `InputCut.position`: collapses the deleted interval to its left endpoint and shifts later
  input-head positions left.
* `InputCut.SameSide`: two positions lie on the same retained side of the cut.
* `InputCut.MapsCore`: configurations on the original and shortened inputs have equal storage
  and input-head positions related by the cut's position map.
* `InputCut.VisitPairing`: an order-preserving pairing of boundary visits with equal storages
  and equal boundary symbols.

## Main results

* `InputCut.MapsCore.step`: matching configurations remain matched after a step on a retained side
  when the boundary symbols agree.
* `exists_storage_cut`: equal boundary symbols and visit sequences preserve every storage reached
  outside the deleted interval.
* `finite_visitTimes_of_halt`: every position other than the final input-head position has finitely
  many visits in a halting run.
* `storage_runFrom_injOn_visitTimes`: distinct visits to a finitely visited position have distinct
  storages.
* `encard_visitTimes_le`: the number of visits to such a position is at most `storageBound`.
* `exists_shorter_input_storage`: a sufficiently long input to a halting space-bounded machine
  has a shorter input whose run reaches a chosen storage from the original run.

## Implementation notes

The proof adapts Katz's cell-visit crossing-sequence argument. His semi-configurations include
the scanned input symbol, whose equality is required separately here. Our sequences cover the
whole run, so counting excludes the final head position after halting.

## References

* [Jonathan Katz, *Notes on Complexity Theory, Lecture 5*][Katz2007],
  §1.2, Theorem 4, pp. 5-2–5-4.
-/

@[expose] public section

namespace Turing.MultiTapeTM

open Relation Set

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}
variable {tm : MultiTapeTM k Symbol State}

/-- All times at which the input head is at `p`. -/
def visitTimes (cfg : Cfg k Symbol State input) (p : ℕ) : Set ℕ :=
  {t | (tm.runFrom cfg t).inputPos.val = p}

@[simp]
lemma mem_visitTimes {cfg : Cfg k Symbol State input} {p t : ℕ} :
    t ∈ tm.visitTimes cfg p ↔ (tm.runFrom cfg t).inputPos.val = p := Iff.rfl

/-- The storages encountered at input position `p`, in chronological order. -/
noncomputable def visitSequence (cfg : Cfg k Symbol State input) (p : ℕ) :
    Stream'.Seq (Storage Symbol State k) := by
  classical
  let s := tm.visitTimes cfg p
  refine ⟨fun n => if (n : ℕ∞) < s.encard then
    some (tm.runFrom cfg (Nat.nth (· ∈ s) n)).storage else none, ?_⟩
  intro n
  simp only [ite_eq_right_iff, Option.some_ne_none, imp_false, not_lt]
  exact fun h => h.trans (by exact_mod_cast Nat.le_succ n)

/-- An entry records a visit's storage, indexed by the number of earlier visits. -/
private lemma get?_visitSequence {cfg : Cfg k Symbol State input} {p n : ℕ}
    {storage : Storage Symbol State k}
    [DecidablePred (· ∈ tm.visitTimes cfg p)] :
    (tm.visitSequence cfg p).get? n = some storage ↔
      ∃ t ∈ tm.visitTimes cfg p, Nat.count (· ∈ tm.visitTimes cfg p) t = n ∧
        (tm.runFrom cfg t).storage = storage := by
  classical
  let s := tm.visitTimes cfg p
  change (if (n : ℕ∞) < s.encard then
    some (tm.runFrom cfg (Nat.nth (· ∈ s) n)).storage else none) = some storage ↔
      ∃ t ∈ s, Nat.count (· ∈ s) t = n ∧ (tm.runFrom cfg t).storage = storage
  constructor
  · intro h
    have hn : (n : ℕ∞) < s.encard := by grind
    have hn' (hf : s.Finite) : n < hf.toFinset.card := by
      simpa only [hf.encard_eq_coe_toFinset_card, ENat.natCast_lt_natCast] using hn
    refine ⟨Nat.nth (· ∈ s) n, Nat.nth_mem n hn', Nat.count_nth hn', ?_⟩
    simpa [hn] using h
  · rintro ⟨t, ht, rfl, rfl⟩
    have hn : (Nat.count (· ∈ s) t : ℕ∞) < s.encard := by
      by_cases hf : s.Finite
      · simpa only [hf.encard_eq_coe_toFinset_card, ENat.natCast_lt_natCast] using
          Nat.count_lt_card (p := (· ∈ s)) hf ht
      · simp [Set.Infinite.encard_eq hf]
    simp [hn, Nat.nth_count ht]

/-- Between consecutive visits, the input head stays on the side chosen by its first step. -/
private lemma inputPos_bounds_of_covBy {cfg : Cfg k Symbol State input} {p t : ℕ}
    {u v : tm.visitTimes cfg p} (h : u ⋖ v) (ht : t ∈ Icc u.val v.val) :
    ((tm.runFrom cfg (u.val + 1)).inputPos.val ≤ p → (tm.runFrom cfg t).inputPos.val ≤ p) ∧
      (p ≤ (tm.runFrom cfg (u.val + 1)).inputPos.val → p ≤ (tm.runFrom cfg t).inputPos.val) := by
  rcases eq_or_lt_of_le ht.1 with rfl | hut
  · simp [tm.mem_visitTimes.mp u.property]
  · apply tm.inputPos_bounds_of_forall_ne hut
    intro r hur hrt hp
    exact h.2 (c := ⟨r, hp⟩) (Nat.lt_of_succ_le hur) (hrt.trans_le ht.2)

/-- An ordered pair of input-symbol indices. The cut deletes the symbols after the first
through the second. Equal endpoints give an empty deletion.
`fst` and `snd` are zero-based list indices. `left` and `right` are the corresponding
input-head positions, offset by one because position `0` is the left endmarker. -/
abbrev InputCut (input : List Symbol) := NonemptyInterval (Fin input.length)

namespace InputCut

variable (cut : InputCut input)

/-- The head position of the retained endpoint: position `0` is the left endmarker. -/
def left : ℕ := cut.fst.val + 1

/-- The head position of the right endpoint: input symbol `i` is read at position `i + 1`. -/
def right : ℕ := cut.snd.val + 1

/-- The input obtained by deleting the cells after `left` through `right`. -/
def shortened : List Symbol :=
  input.take cut.left ++ input.drop cut.right

/-- Collapse the deleted interval to its left endpoint and shift subsequent positions left. -/
def position (p : ℕ) : ℕ :=
  min p cut.left + (p - cut.right)

/-- Two input positions lie on the same retained side of the cut. -/
def SameSide (p q : ℕ) : Prop :=
  (p ≤ cut.left ∧ q ≤ cut.left) ∨ (cut.right ≤ p ∧ cut.right ≤ q)

/-- A one-cell move ending outside the cut, away from its boundaries, stays on a retained side. -/
lemma sameSide_of_not_boundary {p q : ℕ} (hstep : |(q : ℤ) - p| ≤ 1)
    (hq : q ≤ cut.left ∨ cut.right ≤ q) (hne : ¬ (q = cut.left ∨ q = cut.right)) :
    cut.SameSide p q := by
  grind [SameSide, abs_le]

/-- Adding back the deleted cells recovers the original input length. -/
private lemma length_shortened_add :
    cut.shortened.length + (cut.right - cut.left) = input.length := by
  grind [shortened, left, right, cut.fst_le_snd]

/-- Positions at or left of the cut do not move. -/
private lemma position_left {p : ℕ} (hp : p ≤ cut.left) : cut.position p = p := by
  grind [position, left, right, cut.fst_le_snd]

/-- Positions at or right of the cut shift by the number of deleted cells. -/
private lemma position_right {p : ℕ} (hp : cut.right ≤ p) :
    cut.position p = p - (cut.right - cut.left) := by
  grind [position, left, right, cut.fst_le_snd]

/-- The cut preserves the left endmarker and maps positive positions to positive positions. -/
@[simp]
lemma position_eq_zero {p : ℕ} : cut.position p = 0 ↔ p = 0 := by
  grind [position, left]

/-- Indexing the retained prefix is unchanged. -/
lemma getElem?_left {i : ℕ} (hi : i < cut.left) : cut.shortened[i]? = input[i]? := by
  have hle : cut.left ≤ input.length := cut.fst.isLt
  simp [shortened, List.getElem?_append, hle, hi]

/-- Indexing the retained suffix shifts by the number of deleted symbols. -/
lemma getElem?_right (i : ℕ) :
    cut.shortened[cut.left + i]? = input[cut.right + i]? := by
  have hle : cut.left ≤ input.length := cut.fst.isLt
  simp [shortened, List.getElem?_append, hle]

/-- The removed right endpoint is represented by the retained left endpoint. -/
lemma getElem?_boundary (hsym : input[cut.fst] = input[cut.snd]) :
    cut.shortened[cut.left - 1]? = input[cut.right - 1]? := by
  rw [cut.getElem?_left (Nat.sub_lt (Nat.succ_pos _) (by decide))]
  simpa [left, right, Fin.getElem_fin] using congrArg some hsym

/-- Outside the deleted interval, the position map preserves the indexed symbol. -/
lemma getElem?_position (hsym : input[cut.fst] = input[cut.snd]) {p : ℕ}
    (hp : p ≤ cut.left ∨ cut.right ≤ p) :
    cut.shortened[cut.position p - 1]? = input[p - 1]? := by
  have := cut.getElem?_right (p - cut.right - 1)
  grind [position_left, position_right, getElem?_left, getElem?_boundary, left, right,
    cut.fst_le_snd]

/-- On either retained side, mapping positions commutes with an input-head move. -/
lemma position_moveInputPos {p : Fin (input.length + 2)}
    {p' : Fin (cut.shortened.length + 2)} (hp : p'.val = cut.position p.val) (m : SignType)
    (hside : cut.SameSide p.val (moveInputPos p m).val) :
    cut.position (moveInputPos p m).val = (moveInputPos p' m).val := by
  have hlen := cut.length_shortened_add
  cases m <;> grind [SameSide, position, left, right, moveInputPos_val, SignType.cast,
    cut.fst_le_snd]

/-- The cut maps the input position of the first configuration to that of the second,
preserving storage. -/
def MapsCore (c : Cfg k Symbol State input)
    (c' : Cfg k Symbol State cut.shortened) : Prop :=
  c'.inputPos.val = cut.position c.inputPos.val ∧ c'.storage = c.storage

namespace MapsCore

variable {cut}

/-- Matching configurations outside the cut scan the same symbol when its endpoints agree. -/
lemma inputSymbol (hsym : input[cut.fst] = input[cut.snd])
    {c : Cfg k Symbol State input} {c' : Cfg k Symbol State cut.shortened}
    (h : cut.MapsCore c c') (hp : c.inputPos.val ≤ cut.left ∨ cut.right ≤ c.inputPos.val) :
    c.inputSymbol = c'.inputSymbol := by
  have hsym := cut.getElem?_position hsym hp
  have hzero := cut.position_eq_zero (p := c.inputPos.val)
  grind [Cfg.inputSymbol, MapsCore]

/-- Equal boundary symbols preserve matching configurations across a retained step. -/
lemma step {c : Cfg k Symbol State input} {c' : Cfg k Symbol State cut.shortened}
    (h : cut.MapsCore c c') (hsym : input[cut.fst] = input[cut.snd])
    (hside : cut.SameSide c.inputPos.val (tm.step c).inputPos.val) :
    cut.MapsCore (tm.step c) (tm.step c') := by
  obtain ⟨m, hs, hm, hm'⟩ := tm.exists_step_move_of_storage_eq h.2.symm
    (h.inputSymbol hsym (hside.imp And.left And.left))
  grind [MapsCore, position_moveInputPos]

/-- Matching configurations simulate any run segment contained in one retained side. -/
lemma reaches_runFrom (hsym : input[cut.fst] = input[cut.snd])
    {cfg : Cfg k Symbol State input} {c' : Cfg k Symbol State cut.shortened} {u v : ℕ}
    (h : cut.MapsCore (tm.runFrom cfg u) c') (huv : u ≤ v)
    (hside : MapsTo (fun t => (tm.runFrom cfg t).inputPos.val) (Icc u v) (Iic cut.left) ∨
      MapsTo (fun t => (tm.runFrom cfg t).inputPos.val) (Icc u v) (Ici cut.right)) :
    ∃ d, ReflTransGen tm.Step c' d ∧ cut.MapsCore (tm.runFrom cfg v) d := by
  induction v, huv using Nat.le_induction with
  | base => exact ⟨c', .refl, h⟩
  | succ v huv ih =>
    obtain ⟨d, hd, hm⟩ := ih (by grind [MapsTo])
    have hstep : cut.SameSide (tm.runFrom cfg v).inputPos.val
        (tm.runFrom cfg (v + 1)).inputPos.val := by grind [MapsTo, SameSide]
    refine ⟨tm.step d, hd.tail (step_iff.mpr rfl), ?_⟩
    simp only [runFrom, Function.iterate_succ_apply'] at hstep ⊢
    exact hm.step hsym hstep

end MapsCore

/-- The initial configurations match because the cut retains the first input symbol. -/
lemma mapsCore_init : cut.MapsCore (tm.initCfg input) (tm.initCfg cut.shortened) := by
  constructor
  · exact (cut.position_left (p := 1) (Nat.succ_le_succ (Nat.zero_le _))).symm
  · rfl

/-- An order-preserving pairing of boundary visits with equal symbols and storages. -/
structure VisitPairing (tm : MultiTapeTM k Symbol State) where
  /-- The paired boundary positions carry the same input symbol. -/
  symbol_eq : input[cut.fst] = input[cut.snd]
  /-- The visits to the two boundaries correspond in chronological order. -/
  orderIso : tm.visitTimes (tm.initCfg input) cut.left ≃o
    tm.visitTimes (tm.initCfg input) cut.right
  /-- Corresponding visits have the same storage. -/
  storage_eq (u : tm.visitTimes (tm.initCfg input) cut.left) :
    (tm.runFrom (tm.initCfg input) u).storage =
      (tm.runFrom (tm.initCfg input) (orderIso u)).storage

/-- Equal visit sequences pair visits of the same index, preserving their storages. -/
private noncomputable def visitPairing (hsym : input[cut.fst] = input[cut.snd])
    (hseq : tm.visitSequence (tm.initCfg input) cut.left =
      tm.visitSequence (tm.initCfg input) cut.right) : cut.VisitPairing tm := by
  classical
  let s := tm.visitTimes (tm.initCfg input) cut.left
  let t := tm.visitTimes (tm.initCfg input) cut.right
  have hmatch (i : s) : ∃ j : t,
      Nat.count (· ∈ s) i = Nat.count (· ∈ t) j ∧
        (tm.runFrom (tm.initCfg input) i).storage = (tm.runFrom (tm.initCfg input) j).storage := by
    have h := get?_visitSequence.mpr ⟨i.val, i.property, rfl, rfl⟩
    rw [hseq] at h
    obtain ⟨j, hj, hn, hstore⟩ := get?_visitSequence.mp h
    exact ⟨⟨j, hj⟩, hn.symm, hstore.symm⟩
  choose e he hstore using hmatch
  have hmono : StrictMono e := fun i j h => Nat.lt_of_count_lt_count (by
    rw [← he i, ← he j]
    exact Nat.count_strict_mono i.property h)
  have hsurj : Function.Surjective e := by
    intro j
    have h := get?_visitSequence.mpr ⟨j.val, j.property, rfl, rfl⟩
    rw [← hseq] at h
    obtain ⟨i, hi, hn, _⟩ := get?_visitSequence.mp h
    exact ⟨⟨i, hi⟩, Subtype.ext (Nat.count_injective (e ⟨i, hi⟩).property j.property
      ((he ⟨i, hi⟩).symm.trans hn))⟩
  exact ⟨hsym, hmono.orderIsoOfSurjective e hsurj, hstore⟩

/-- The retained prefix reaches the first visit to the left boundary. -/
private lemma exists_mapsCore_first_visit (hsym : input[cut.fst] = input[cut.snd])
    {u : tm.visitTimes (tm.initCfg input) cut.left} (hu : IsMin u) :
    ∃ c', ReflTransGen tm.Step (tm.initCfg cut.shortened) c' ∧
      cut.MapsCore (tm.runFrom (tm.initCfg input) u) c' := by
  apply cut.mapsCore_init.reaches_runFrom hsym (cfg := tm.initCfg input) (u := 0) (Nat.zero_le _)
  left
  rintro v ⟨_, hv⟩
  apply tm.inputPos_le_of_forall_ne (Nat.zero_le v) (by simp [left, runFrom])
  intro r _ hrv hp
  exact hu.not_lt (b := ⟨r, hp⟩) (hrv.trans_le hv)

namespace VisitPairing

variable {cut} (pairing : cut.VisitPairing tm)

include pairing

/-- Paired visits represent the same storage at the collapsed boundary. -/
private lemma mapsCore_iff (u : tm.visitTimes (tm.initCfg input) cut.left)
    {c' : Cfg k Symbol State cut.shortened} :
    cut.MapsCore (tm.runFrom (tm.initCfg input) u) c' ↔
      cut.MapsCore (tm.runFrom (tm.initCfg input) (pairing.orderIso u)) c' := by
  grind [MapsCore, position, left, right, visitTimes, pairing.storage_eq u, cut.fst_le_snd]

/-- At a paired visit, at least one of the two next steps enters a retained side. -/
private lemma step_sides (u : tm.visitTimes (tm.initCfg input) cut.left) :
    (tm.runFrom (tm.initCfg input) (u.val + 1)).inputPos.val ≤ cut.left ∨
      cut.right ≤ (tm.runFrom (tm.initCfg input) ((pairing.orderIso u).val + 1)).inputPos.val := by
  have hleft := tm.mem_visitTimes.mp u.property
  have hright := tm.mem_visitTimes.mp (pairing.orderIso u).property
  have hsym : (tm.runFrom (tm.initCfg input) u).inputSymbol =
      (tm.runFrom (tm.initCfg input) (pairing.orderIso u)).inputSymbol := by
    grind [Cfg.inputSymbol, left, right, pairing.symbol_eq]
  obtain ⟨m, _, hm, hm'⟩ := tm.exists_step_move_of_storage_eq (pairing.storage_eq u) hsym
  cases m <;> grind [runFrom, Function.iterate_succ_apply', moveInputPos_val, SignType.cast,
    left, right]

/-- Between consecutive paired visits, follow the excursion on a retained side. -/
private lemma reaches_next_visit {u v : tm.visitTimes (tm.initCfg input) cut.left}
    (huv : u ⋖ v) {c' : Cfg k Symbol State cut.shortened}
    (h : cut.MapsCore (tm.runFrom (tm.initCfg input) u) c') :
    ∃ d, ReflTransGen tm.Step c' d ∧
      cut.MapsCore (tm.runFrom (tm.initCfg input) v) d := by
  rcases pairing.step_sides u with hleft | hright
  · exact h.reaches_runFrom pairing.symbol_eq huv.le
      (.inl fun t ht => (inputPos_bounds_of_covBy huv ht).1 hleft)
  · have he := (apply_covBy_apply_iff pairing.orderIso).mpr huv
    obtain ⟨d, hd, hm⟩ := ((pairing.mapsCore_iff u).mp h).reaches_runFrom
      pairing.symbol_eq he.le (.inr fun t ht => (inputPos_bounds_of_covBy he ht).2 hright)
    exact ⟨d, hd, (pairing.mapsCore_iff v).mpr hm⟩

/-- Induct over the paired visits, starting with the retained prefix. -/
private lemma exists_mapsCore_left_visit (u : tm.visitTimes (tm.initCfg input) cut.left) :
    ∃ c', ReflTransGen tm.Step (tm.initCfg cut.shortened) c' ∧
      cut.MapsCore (tm.runFrom (tm.initCfg input) u) c' := by
  classical
  induction u using WellFoundedLT.induction with | ind u ih =>
  by_cases hu : IsMin u
  · exact cut.exists_mapsCore_first_visit pairing.symbol_eq hu
  · obtain ⟨w, hwu⟩ := not_isMin_iff.mp hu
    obtain ⟨v, _, hvu⟩ := exists_le_covBy_of_lt hwu
    obtain ⟨c', hr, hm⟩ := ih v hvu.lt
    obtain ⟨d, hd, hm'⟩ := pairing.reaches_next_visit hvu hm
    exact ⟨d, hr.trans hd, hm'⟩

/-- Every boundary visit has a reachable matching configuration on the shortened input. -/
lemma exists_mapsCore_visit {t : ℕ}
    (ht : t ∈ tm.visitTimes (tm.initCfg input) cut.left ∪
      tm.visitTimes (tm.initCfg input) cut.right) :
    ∃ c', ReflTransGen tm.Step (tm.initCfg cut.shortened) c' ∧
      cut.MapsCore (tm.runFrom (tm.initCfg input) t) c' := by
  rcases ht with ht | ht
  · exact pairing.exists_mapsCore_left_visit ⟨t, ht⟩
  · let v := pairing.orderIso.symm ⟨t, ht⟩
    obtain ⟨c', hr, hm⟩ := pairing.exists_mapsCore_left_visit v
    exact ⟨c', hr, by
      simpa only [v, pairing.orderIso.apply_symm_apply] using (pairing.mapsCore_iff v).mp hm⟩

/-- A pairing of boundary visits gives every configuration outside the cut a reachable
matching configuration on the shortened input. -/
theorem exists_mapsCore {t : ℕ}
    (hp : (tm.runFrom (tm.initCfg input) t).inputPos.val ≤ cut.left ∨
      cut.right ≤ (tm.runFrom (tm.initCfg input) t).inputPos.val) :
    ∃ c', ReflTransGen tm.Step (tm.initCfg cut.shortened) c' ∧
      cut.MapsCore (tm.runFrom (tm.initCfg input) t) c' := by
  induction t with
  | zero => exact ⟨_, .refl, cut.mapsCore_init⟩
  | succ t ih =>
    by_cases hb : (tm.runFrom (tm.initCfg input) (t + 1)).inputPos.val = cut.left ∨
        (tm.runFrom (tm.initCfg input) (t + 1)).inputPos.val = cut.right
    · exact pairing.exists_mapsCore_visit hb
    have hbounds : |((tm.runFrom (tm.initCfg input) (t + 1)).inputPos.val : ℤ) -
        (tm.runFrom (tm.initCfg input) t).inputPos.val| ≤ 1 := by
      simpa only [runFrom, Function.iterate_succ_apply'] using
        tm.inputPos_step_le (tm.runFrom (tm.initCfg input) t)
    have hside := cut.sameSide_of_not_boundary hbounds hp hb
    obtain ⟨c', hr, hm⟩ := ih (hside.imp And.left And.left)
    refine ⟨tm.step c', hr.tail (step_iff.mpr rfl), ?_⟩
    simp only [runFrom, Function.iterate_succ_apply']
    exact hm.step pairing.symbol_eq
      (by simpa only [runFrom, Function.iterate_succ_apply'] using hside)

end VisitPairing

end InputCut

/-- Equal symbols and visit sequences at the endpoints of a cut preserve every storage reached
outside the deleted interval. -/
theorem exists_storage_cut (cut : InputCut input)
    (hsym : input[cut.fst] = input[cut.snd])
    (hseq : tm.visitSequence (tm.initCfg input) cut.left =
      tm.visitSequence (tm.initCfg input) cut.right)
    {t : ℕ}
    (hp : (tm.runFrom (tm.initCfg input) t).inputPos.val ≤ cut.left ∨
      cut.right ≤ (tm.runFrom (tm.initCfg input) t).inputPos.val) :
    ∃ u, (tm.runFrom (tm.initCfg cut.shortened) u).storage =
      (tm.runFrom (tm.initCfg input) t).storage := by
  obtain ⟨c', hr, hm⟩ := (InputCut.visitPairing cut hsym hseq).exists_mapsCore hp
  obtain ⟨u, rfl⟩ : ∃ u, tm.runFrom (tm.initCfg cut.shortened) u = c' := by
    clear hm
    induction hr with
    | refl => exact ⟨0, rfl⟩
    | @tail c d hr hstep ih =>
      obtain ⟨u, rfl⟩ := ih
      exact ⟨u + 1, by simpa only [runFrom, Function.iterate_succ_apply'] using step_iff.mp hstep⟩
  exact ⟨u, hm.2⟩

/-- After halting, only the final input position can have infinitely many visits. -/
lemma finite_visitTimes_of_halt {cfg : Cfg k Symbol State input} {T p : ℕ}
    (hhalt : (tm.runFrom cfg T).Halted) (hp : p ≠ (tm.runFrom cfg T).inputPos.val) :
    (tm.visitTimes cfg p).Finite := by
  apply (Set.finite_Iio T).subset
  intro t ht
  grind [mem_visitTimes, tm.runFrom_eq_of_halt cfg]

/-- At a finitely visited position, two visits cannot have the same storage. -/
lemma storage_runFrom_injOn_visitTimes {cfg : Cfg k Symbol State input} {p : ℕ}
    (hf : (tm.visitTimes cfg p).Finite) :
    Set.InjOn (fun t => (tm.runFrom cfg t).storage) (tm.visitTimes cfg p) := by
  intro a ha b hb heq
  wlog hab : a ≤ b generalizing a b
  · exact (this hb ha heq.symm (le_of_not_ge hab)).symm
  obtain ⟨T, haT, hT, hmax⟩ := hf.exists_le_maximal ha
  have hcore := tm.core_runFrom_eq_of_core_eq
    (Prod.ext (Fin.ext (ha.trans hb.symm)) heq) (T - a)
  simp only [runFrom] at hcore
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
    Nat.sub_add_cancel haT] at hcore
  have hvisit : T - a + b ∈ tm.visitTimes cfg p := by grind [mem_visitTimes, Cfg.core, runFrom]
  grind

/-- A finitely visited position has at most as many visits as there are bounded storages. -/
lemma encard_visitTimes_le [Fintype Symbol] [Fintype State] {s p : ℕ}
    (hs : ∀ t, tm.spaceUsed (tm.initCfg input) t ≤ s)
    (hf : (tm.visitTimes (tm.initCfg input) p).Finite) :
    (tm.visitTimes (tm.initCfg input) p).encard ≤ storageBound Symbol State k s :=
  (Set.encard_le_encard_of_injOn
    (t := Set.range fun t => (tm.runFrom (tm.initCfg input) t).storage)
    (fun t _ => ⟨t, rfl⟩) (tm.storage_runFrom_injOn_visitTimes hf)).trans
    (tm.encard_storages_le hs)

/-- A sufficiently long input to a halting space-bounded machine can be shortened while
preserving any storage reached by the run. -/
theorem exists_shorter_input_storage [Fintype Symbol] [Fintype State] {s : ℕ}
    (hhalt : ∃ T, (tm.runFrom (tm.initCfg input) T).Halted)
    (hs : ∀ t, tm.spaceUsed (tm.initCfg input) t ≤ s)
    (hlen : 2 * Fintype.card Symbol *
      (storageBound Symbol State k s + 1) ^ storageBound Symbol State k s + 1 < input.length)
    (t : ℕ) :
    ∃ input' : List Symbol, input'.length < input.length ∧
      ∃ u, (tm.runFrom (tm.initCfg input') u).storage =
        (tm.runFrom (tm.initCfg input) t).storage := by
  classical
  obtain ⟨T, hT⟩ := hhalt
  let D := {i : Fin input.length //
    i.val + 1 ≠ (tm.runFrom (tm.initCfg input) T).inputPos.val}
  have hsize : input.length - 1 ≤ Fintype.card D := by
    have hbad : Fintype.card {i : Fin input.length //
        i.val + 1 = (tm.runFrom (tm.initCfg input) T).inputPos.val} ≤ 1 := by
      apply Fintype.card_le_one_iff.mpr
      grind
    dsimp only [D]
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    omega
  have hfinite (i : D) := tm.finite_visitTimes_of_halt hT i.property
  let B := storageBound Symbol State k s
  let S := Set.range (fun u => (tm.runFrom (tm.initCfg input) u).storage)
  have hbound : S.encard ≤ B := tm.encard_storages_le hs
  let : Fintype S := (Set.finite_of_encard_le_coe hbound).fintype
  have hcard : Fintype.card S ≤ B := by
    exact_mod_cast (Set.coe_fintypeCard (s := S)).le.trans hbound
  let seq (p : ℕ) : Stream'.Seq S := ⟨fun n =>
    if (n : ℕ∞) < (tm.visitTimes (tm.initCfg input) p).encard then
      some ⟨(tm.runFrom (tm.initCfg input)
        (Nat.nth (· ∈ tm.visitTimes (tm.initCfg input) p) n)).storage, ⟨_, rfl⟩⟩ else none, by
    intro n
    simp only [ite_eq_right_iff, Option.some_ne_none, imp_false, not_lt]
    exact fun h => h.trans (by exact_mod_cast Nat.le_succ n)⟩
  have hseq_map (p : ℕ) : (seq p).map Subtype.val = tm.visitSequence (tm.initCfg input) p := by
    ext1 n
    rw [Stream'.Seq.map_get?]
    simp only [seq, visitSequence, Stream'.Seq.get?]
    split <;> rfl
  have hterm (i : D) : (seq (i.val.val + 1)).TerminatedAt B :=
    ite_eq_right (not_lt.mpr (tm.encard_visitTimes_le hs (hfinite i)))
  let p := (tm.runFrom (tm.initCfg input) t).inputPos.val
  -- Matching positions on the same side of `p` give a cut that avoids `p`.
  let f (i : D) : Bool × Symbol × (Fin B → Option S) :=
    (decide (i.val.val + 1 < p), input[i.val], fun j => (seq (i.val.val + 1)).get? j.val)
  have hsig : Fintype.card (Bool × Symbol × (Fin B → Option S)) < Fintype.card D := by
    calc
      _ = 2 * Fintype.card Symbol * (Fintype.card S + 1) ^ B := by simp [mul_assoc]
      _ ≤ 2 * Fintype.card Symbol * (B + 1) ^ B := by gcongr; omega
      _ < input.length - 1 := by dsimp only [B]; omega
      _ ≤ Fintype.card D := hsize
  obtain ⟨i, j, hij, hf⟩ : ∃ i j, i < j ∧ f i = f j := by
    obtain ⟨i, j, hne, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hsig
    grind
  obtain ⟨hside, hsym, hseq⟩ := (by simpa only [f, Prod.mk.injEq, decide_eq_decide] using hf)
  have hseq' : seq (i.val.val + 1) = seq (j.val.val + 1) := by
    ext1 r
    by_cases hr : r < B
    · exact congrFun hseq ⟨r, hr⟩
    · grind only [Stream'.Seq.le_stable, Stream'.Seq.TerminatedAt, hterm i, hterm j]
  change i.val.val < j.val.val at hij
  let cut : InputCut input := ⟨⟨i.val, j.val⟩, hij.le⟩
  refine ⟨cut.shortened, ?_, tm.exists_storage_cut cut hsym ?_ ?_⟩
  · have := cut.length_shortened_add
    change cut.shortened.length + (j.val.val + 1 - (i.val.val + 1)) = input.length at this
    omega
  · change tm.visitSequence _ (i.val.val + 1) = tm.visitSequence _ (j.val.val + 1)
    rw [← hseq_map, ← hseq_map, hseq']
  · change p ≤ i.val.val + 1 ∨ j.val.val + 1 ≤ p
    omega

end Turing.MultiTapeTM

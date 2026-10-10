/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.ConfigBound
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Order.Atoms.Finite
public import Mathlib.Order.Cover
public import Mathlib.Order.Interval.Basic

/-!
# Input shortening for multi-tape Turing machines

Consider a deterministic Turing machine and an input on which it halts. For each input cell, we
record the sequence of space configurations (`Storage`) at the times when the input head visits that
cell, stopping at the first halting configuration. We show that if two distinct cells contain the
same symbol and have the same sequence, then the run on the input obtained by deleting the symbols
after the first cell through the second reaches every space configuration reached by the original
run while its input head is outside the deleted interval. This property is the main ingredient in
the proof of `SPACE(o(log log n)) = SPACE(1)`.

The proof idea follows [Katz2007], §1.2, Theorem 4.

## Main definitions

* `visitTimes`: times at which a run's input head is at a given position, through its first halt.
* `visitSequence`: the finite list of space configurations at those times, in chronological order.
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
* `finite_visitTimes_of_halt`: every position has finitely many visits in a halting run.
* `storage_runFrom_injOn_visitTimes`: distinct visits to a position in a halting run have distinct
  storages.
* `encard_visitTimes_le`: the number of visits to a position is at most `storageBound`.
* `exists_shorter_input_storage`: a sufficiently long input to a halting space-bounded machine
  has a shorter input whose run reaches a chosen storage from the original run.

## References

* [Jonathan Katz, *Notes on Complexity Theory, Lecture 5*][Katz2007],
  §1.2, Theorem 4, pp. 5-2–5-4.
-/

@[expose] public section

namespace Turing.MultiTapeTM

open Relation Set

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}
variable {tm : MultiTapeTM k Symbol State}

/-- Times at which the input head is at `p`, up to and including the first halting time. -/
def visitTimes (cfg : Cfg k Symbol State input) (p : ℕ) : Set ℕ :=
  {t | (tm.runFrom cfg t).inputPos.val = p ∧ ∀ u < t, ¬(tm.runFrom cfg u).Halted}

@[simp]
lemma mem_visitTimes {cfg : Cfg k Symbol State input} {p t : ℕ} :
    t ∈ tm.visitTimes cfg p ↔
      (tm.runFrom cfg t).inputPos.val = p ∧ ∀ u < t, ¬(tm.runFrom cfg u).Halted := Iff.rfl

/-- Earlier occurrences of a position also precede the first halt. -/
private lemma mem_visitTimes_of_le {cfg : Cfg k Symbol State input} {p q t u : ℕ}
    (hu : u ∈ tm.visitTimes cfg q) (htu : t ≤ u)
    (hp : (tm.runFrom cfg t).inputPos.val = p) : t ∈ tm.visitTimes cfg p :=
  ⟨hp, fun r hr ↦ hu.2 r (hr.trans_le htu)⟩

/-- Every input position has finitely many visits in a halting run. -/
lemma finite_visitTimes_of_halt {cfg : Cfg k Symbol State input}
    (hhalt : ∃ T, (tm.runFrom cfg T).Halted) (p : ℕ) : (tm.visitTimes cfg p).Finite := by
  obtain ⟨T, hT⟩ := hhalt
  exact (Set.finite_Iic T).subset fun _ ht ↦ le_of_not_gt fun h ↦ ht.2 T h hT

/-- The list of storages encountered at input position `p`, in chronological order.
The first halting configuration is included once, at its input-head position. -/
noncomputable def visitSequence (cfg : Cfg k Symbol State input) (p : ℕ)
    (hhalt : ∃ T, (tm.runFrom cfg T).Halted) : List (Storage Symbol State k) :=
  ((tm.finite_visitTimes_of_halt hhalt p).toFinset.sort (· ≤ ·)).map
    (fun t ↦ (tm.runFrom cfg t).storage)

/-- Between consecutive visits, the input head stays on the side chosen by its first step. -/
private lemma inputPos_bounds_of_covBy {cfg : Cfg k Symbol State input} {p t : ℕ}
    {u v : tm.visitTimes cfg p} (h : u ⋖ v) (ht : t ∈ Icc u.val v.val) :
    ((tm.runFrom cfg (u.val + 1)).inputPos.val ≤ p → (tm.runFrom cfg t).inputPos.val ≤ p) ∧
      (p ≤ (tm.runFrom cfg (u.val + 1)).inputPos.val → p ≤ (tm.runFrom cfg t).inputPos.val) := by
  rcases eq_or_lt_of_le ht.1 with rfl | hut
  · simp [u.property.1]
  · apply tm.inputPos_bounds_of_forall_ne hut
    intro r hur hrt hp
    exact h.2 (c := ⟨r, mem_visitTimes_of_le v.property (hrt.trans_le ht.2).le hp⟩)
      (Nat.lt_of_succ_le hur) (hrt.trans_le ht.2)

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
private noncomputable def visitPairing
    (hhalt : ∃ T, (tm.runFrom (tm.initCfg input) T).Halted)
    (hsym : input[cut.fst] = input[cut.snd])
    (hseq : tm.visitSequence (tm.initCfg input) cut.left hhalt =
      tm.visitSequence (tm.initCfg input) cut.right hhalt) : cut.VisitPairing tm := by
  classical
  let e (p : ℕ) : Fin (tm.visitSequence (tm.initCfg input) p hhalt).length ≃o
      tm.visitTimes (tm.initCfg input) p :=
    ((tm.finite_visitTimes_of_halt hhalt p).toFinset.orderIsoOfFin
      (by simp [visitSequence])).trans (Set.orderIsoOfEq _ _ (by simp))
  have he (p : ℕ) (i : Fin (tm.visitSequence (tm.initCfg input) p hhalt).length) :
      (tm.runFrom (tm.initCfg input) (e p i)).storage =
        (tm.visitSequence (tm.initCfg input) p hhalt)[i.val] := by
    simp only [visitSequence, List.getElem_map]
    rfl
  let cast := Fin.castOrderIso (congrArg List.length hseq)
  refine ⟨hsym, (e cut.left).symm.trans (cast.trans (e cut.right)), ?_⟩
  intro u
  have h := he cut.left ((e cut.left).symm u)
  rw [(e cut.left).apply_symm_apply] at h
  calc
    _ = _ := h
    _ = (tm.visitSequence (tm.initCfg input) cut.right hhalt)[(cast ((e cut.left).symm u)).1] := by
      congr 1
    _ = _ := (he cut.right (cast ((e cut.left).symm u))).symm

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
  exact hu.not_lt (b := ⟨r, mem_visitTimes_of_le u.property (hrv.trans_le hv).le hp⟩)
    (hrv.trans_le hv)

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
  have hleft := u.property.1
  have hright := (pairing.orderIso u).property.1
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
    by_cases hh : (tm.runFrom (tm.initCfg input) t).Halted
    · have heq := tm.runFrom_eq_of_halt (tm.initCfg input) (Nat.le_succ t) hh
      rw [heq] at hp ⊢
      exact ih hp
    have hbefore : ∀ u < t + 1, ¬(tm.runFrom (tm.initCfg input) u).Halted := by
      intro u hu hhalt
      exact hh (by rwa [tm.runFrom_eq_of_halt (tm.initCfg input) (by omega) hhalt])
    by_cases hb : (tm.runFrom (tm.initCfg input) (t + 1)).inputPos.val = cut.left ∨
        (tm.runFrom (tm.initCfg input) (t + 1)).inputPos.val = cut.right
    · exact pairing.exists_mapsCore_visit (hb.imp (fun h ↦ ⟨h, hbefore⟩) (fun h ↦ ⟨h, hbefore⟩))
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
    (hhalt : ∃ T, (tm.runFrom (tm.initCfg input) T).Halted)
    (hsym : input[cut.fst] = input[cut.snd])
    (hseq : tm.visitSequence (tm.initCfg input) cut.left hhalt =
      tm.visitSequence (tm.initCfg input) cut.right hhalt)
    {t : ℕ}
    (hp : (tm.runFrom (tm.initCfg input) t).inputPos.val ≤ cut.left ∨
      cut.right ≤ (tm.runFrom (tm.initCfg input) t).inputPos.val) :
    ∃ u, (tm.runFrom (tm.initCfg cut.shortened) u).storage =
      (tm.runFrom (tm.initCfg input) t).storage := by
  obtain ⟨c', hr, hm⟩ := (InputCut.visitPairing cut hhalt hsym hseq).exists_mapsCore hp
  obtain ⟨u, rfl⟩ : ∃ u, tm.runFrom (tm.initCfg cut.shortened) u = c' := by
    clear hm
    induction hr with
    | refl => exact ⟨0, rfl⟩
    | @tail c d hr hstep ih =>
      obtain ⟨u, rfl⟩ := ih
      exact ⟨u + 1, by simpa only [runFrom, Function.iterate_succ_apply'] using step_iff.mp hstep⟩
  exact ⟨u, hm.2⟩

/-- Distinct visits in a halting run have distinct storages. -/
lemma storage_runFrom_injOn_visitTimes {cfg : Cfg k Symbol State input} {p : ℕ}
    (hhalt : ∃ T, (tm.runFrom cfg T).Halted) :
    Set.InjOn (fun t ↦ (tm.runFrom cfg t).storage) (tm.visitTimes cfg p) := by
  obtain ⟨T, hT⟩ := hhalt
  obtain ⟨T, _, hT⟩ := tm.exists_haltsAt hT
  intro a ha b hb heq
  wlog hab : a ≤ b generalizing a b
  · exact (this hb ha heq.symm (le_of_not_ge hab)).symm
  have hbT : b ≤ T := le_of_not_gt fun h ↦ hb.2 T h hT.halted
  have hcore := tm.core_runFrom_eq_of_core_eq
    (Prod.ext (Fin.ext (ha.1.trans hb.1.symm)) heq) (T - b)
  simp only [runFrom] at hcore
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
    Nat.sub_add_cancel hbT] at hcore
  have hhalt : (tm.runFrom cfg (T - b + a)).Halted := by
    have := congrArg (fun c ↦ c.2.state) hcore
    exact this.trans hT.halted
  have := hT.le_of_halted hhalt
  omega

/-- A position has at most as many visits as there are bounded storages. -/
lemma encard_visitTimes_le [Fintype Symbol] [Fintype State] {s p : ℕ}
    (hs : ∀ t, tm.spaceUsed (tm.initCfg input) t ≤ s)
    (hhalt : ∃ T, (tm.runFrom (tm.initCfg input) T).Halted) :
    (tm.visitTimes (tm.initCfg input) p).encard ≤ storageBound Symbol State k s :=
  (Set.encard_le_encard_of_injOn
    (t := Set.range fun t ↦ (tm.runFrom (tm.initCfg input) t).storage)
    (fun t _ ↦ ⟨t, rfl⟩) (tm.storage_runFrom_injOn_visitTimes hhalt)).trans
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
  let B := storageBound Symbol State k s
  let S := Set.range (fun u ↦ (tm.runFrom (tm.initCfg input) u).storage)
  have hbound : S.encard ≤ B := tm.encard_storages_le hs
  let : Fintype S := (Set.finite_of_encard_le_coe hbound).fintype
  have hcard : Fintype.card S ≤ B := by
    exact_mod_cast (Set.coe_fintypeCard (s := S)).le.trans hbound
  let seq (p : ℕ) : List S :=
    ((tm.finite_visitTimes_of_halt hhalt p).toFinset.sort (· ≤ ·)).map
      (fun u ↦ ⟨(tm.runFrom (tm.initCfg input) u).storage, ⟨u, rfl⟩⟩)
  have hseq_map (p : ℕ) : (seq p).map Subtype.val =
      tm.visitSequence (tm.initCfg input) p hhalt := by
    simp [seq, visitSequence, List.map_map]
  have hlength (p : ℕ) : (seq p).length ≤ B := by
    simp only [seq, List.length_map, Finset.length_sort]
    exact_mod_cast (tm.finite_visitTimes_of_halt hhalt p).encard_eq_coe_toFinset_card ▸
      tm.encard_visitTimes_le hs hhalt (p := p)
  let p := (tm.runFrom (tm.initCfg input) t).inputPos.val
  -- Matching positions on the same side of `p` give a cut that avoids `p`.
  let f (i : Fin input.length) : Bool × Symbol × (Fin B → Option S) :=
    (decide (i.val + 1 < p), input[i], fun j ↦ (seq (i.val + 1))[j.val]?)
  have hsig : Fintype.card (Bool × Symbol × (Fin B → Option S)) < input.length := by
    calc
      _ = 2 * Fintype.card Symbol * (Fintype.card S + 1) ^ B := by simp [mul_assoc]
      _ ≤ 2 * Fintype.card Symbol * (B + 1) ^ B := by gcongr; omega
      _ < input.length := by dsimp only [B]; omega
  obtain ⟨i, j, hij, hf⟩ : ∃ i j, i < j ∧ f i = f j := by
    obtain ⟨i, j, hne, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simpa using hsig)
    grind
  obtain ⟨hside, hsym, hseq⟩ := (by simpa only [f, Prod.mk.injEq, decide_eq_decide] using hf)
  have hseq' : seq (i.val + 1) = seq (j.val + 1) := by
    apply List.ext_getElem?
    intro r
    by_cases hr : r < B
    · exact congrFun hseq ⟨r, hr⟩
    · rw [List.getElem?_eq_none ((hlength _).trans (Nat.le_of_not_gt hr)),
        List.getElem?_eq_none ((hlength _).trans (Nat.le_of_not_gt hr))]
  let cut : InputCut input := ⟨⟨i, j⟩, hij.le⟩
  refine ⟨cut.shortened, ?_, tm.exists_storage_cut cut hhalt hsym ?_ ?_⟩
  · have := cut.length_shortened_add
    change cut.shortened.length + (j.val + 1 - (i.val + 1)) = input.length at this
    omega
  · change tm.visitSequence _ (i.val + 1) hhalt = tm.visitSequence _ (j.val + 1) hhalt
    rw [← hseq_map, ← hseq_map, hseq']
  · change p ≤ i.val + 1 ∨ j.val + 1 ≤ p
    omega

end Turing.MultiTapeTM

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

Consider a deterministic Turing machine and a halting computation path on an input. For each input
cell, we record the sequence of space configurations (`Storage`) at the times when the running
machine visits that cell. We show that if two distinct cells contain the same symbol and have the
same sequence, then deleting the symbols after the first cell through the second preserves the space
configurations reached by steps that stay on either retained side. This property is the main
ingredient in the proof of `SPACE(o(log log n)) = SPACE(1)`.

The proof idea follows [Katz2007], §1.2, Theorem 4.

## Main definitions

* `ComputationPath.visitTimes`: the indices of running visits to an input position.
* `ComputationPath.visitSequence`: the chronological list of space configurations at those visits.
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
* `exists_storage_cut`: equal boundary symbols and visit sequences preserve the storage reached
  after a step on a retained side, including a step that halts.
* `storage_injOn_visitTimes`: distinct running visits to a position in a halting computation have
  distinct storages.
* `exists_shorter_input_storage`: a sufficiently long input to a halting space-bounded machine
  has a shorter input whose run reaches a chosen storage from the original run.

## References

* [Jonathan Katz, *Notes on Complexity Theory, Lecture 5*][Katz2007],
  §1.2, Theorem 4, pp. 5-2–5-4.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}
variable {tm : MultiTapeTM k Symbol State}

namespace ComputationPath

/-- The indices at which a computation path visits `p` in a running configuration. -/
def visitTimes (path : tm.ComputationPath input) (p : ℕ) : Finset (Fin (path.length + 1)) :=
  Finset.univ.filter fun i ↦ (path i).inputPos.val = p ∧ ¬(path i).Halted

@[simp]
lemma mem_visitTimes {path : tm.ComputationPath input} {p : ℕ} {i : Fin (path.length + 1)} :
    i ∈ path.visitTimes p ↔ (path i).inputPos.val = p ∧ ¬(path i).Halted := by
  simp [visitTimes]

/-- The storages at the running visits to `p`, in chronological order. -/
def visitSequence (path : tm.ComputationPath input) (p : ℕ) : List (Storage Symbol State k) :=
  ((path.visitTimes p).sort (· ≤ ·)).map fun i ↦ (path i).storage

/-- Earlier occurrences of a position are also running visits. -/
private lemma mem_visitTimes_of_le {path : tm.ComputationPath input} {p q : ℕ}
    {i j : Fin (path.length + 1)} (hj : j ∈ path.visitTimes q) (hij : i ≤ j)
    (hp : (path i).inputPos.val = p) : i ∈ path.visitTimes p := by
  exact mem_visitTimes.mpr
    ⟨hp, MultiTapeNTM.RunPath.not_halted_of_le path.toRunPath hij (mem_visitTimes.mp hj).2⟩

end ComputationPath

open Relation Set ComputationPath
open MultiTapeNTM.ComputationPath (apply_zero)

/-- Between consecutive visits, the input head stays on the side chosen by its first step. -/
private lemma inputPos_bounds_of_covBy {path : tm.ComputationPath input} {p : ℕ}
    {u v : path.visitTimes p} {t : Fin (path.length + 1)} (h : u ⋖ v) (ht : t ∈ Icc u.val v.val) :
    ((tm.step (path u.val)).inputPos.val ≤ p → (path t).inputPos.val ≤ p) ∧
      (p ≤ (tm.step (path u.val)).inputPos.val → p ≤ (path t).inputPos.val) := by
  rcases eq_or_lt_of_le ht.1 with rfl | hut
  · simp [(mem_visitTimes.mp u.property).1]
  · have hne (r : ℕ) (hur : u.val.val + 1 ≤ r) (hrt : r < t.val) :
        (tm.runFrom (tm.initCfg input) r).inputPos.val ≠ p := by
      intro hp
      let i : Fin (path.length + 1) := ⟨r, hrt.trans t.isLt⟩
      have hi : i ∈ path.visitTimes p := mem_visitTimes_of_le v.property
        (by exact (hrt.trans_le ht.2).le)
        (by simpa only [computationPath_apply_eq_runFrom] using hp)
      exact h.2 (c := ⟨i, hi⟩) (by exact Nat.lt_of_succ_le hur) (by exact hrt.trans_le ht.2)
    simpa only [computationPath_apply_eq_runFrom, runFrom, Function.iterate_succ_apply'] using
      tm.inputPos_bounds_of_forall_ne (show u.val.val < t.val from hut) hne

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

/-- Matching configurations simulate any path segment contained in one retained side. -/
lemma reaches_path (hsym : input[cut.fst] = input[cut.snd])
    {path : tm.ComputationPath input} {c' : Cfg k Symbol State cut.shortened}
    {u v : Fin (path.length + 1)} (h : cut.MapsCore (path u) c') (huv : u ≤ v)
    (hside : MapsTo (fun i ↦ (path i).inputPos.val) (Icc u v) (Iic cut.left) ∨
      MapsTo (fun i ↦ (path i).inputPos.val) (Icc u v) (Ici cut.right)) :
    ∃ d, ReflTransGen tm.Step c' d ∧ cut.MapsCore (path v) d := by
  induction v using Fin.induction with
  | zero =>
    obtain rfl : u = 0 := le_antisymm huv (Fin.zero_le _)
    exact ⟨c', .refl, h⟩
  | succ v ih =>
    by_cases hu : u ≤ v.castSucc
    · obtain ⟨d, hd, hm⟩ := ih hu (by grind [MapsTo])
      have hstep : cut.SameSide (path v.castSucc).inputPos.val
          (path v.succ).inputPos.val := by grind [MapsTo, SameSide]
      have heq := step_iff.mp (path.step v)
      refine ⟨tm.step d, hd.tail (step_iff.mpr rfl), ?_⟩
      rw [← heq] at hstep ⊢
      exact hm.step hsym hstep
    · have huv' : u.val ≤ v.val + 1 := huv
      have hu' : ¬u.val ≤ v.val := hu
      obtain rfl : u = v.succ :=
        Fin.ext (by simpa only [Fin.val_succ] using Nat.le_antisymm huv' (by omega))
      exact ⟨c', .refl, h⟩

end MapsCore

/-- The initial configurations match because the cut retains the first input symbol. -/
lemma mapsCore_init : cut.MapsCore (tm.initCfg input) (tm.initCfg cut.shortened) := by
  constructor
  · exact (cut.position_left (p := 1) (Nat.succ_le_succ (Nat.zero_le _))).symm
  · rfl

/-- An order-preserving pairing of running boundary visits with equal symbols and storages. -/
structure VisitPairing {tm : MultiTapeTM k Symbol State} (path : tm.ComputationPath input) where
  /-- The paired boundary positions carry the same input symbol. -/
  symbol_eq : input[cut.fst] = input[cut.snd]
  /-- The visits to the two boundaries correspond in chronological order. -/
  orderIso : path.visitTimes cut.left ≃o path.visitTimes cut.right
  /-- Corresponding visits have the same storage. -/
  storage_eq (u : path.visitTimes cut.left) :
    (path u.val).storage = (path (orderIso u).val).storage

/-- Equal visit sequences pair visits of the same index, preserving their storages. -/
private def visitPairing {path : tm.ComputationPath input}
    (hsym : input[cut.fst] = input[cut.snd])
    (hseq : path.visitSequence cut.left = path.visitSequence cut.right) :
    cut.VisitPairing path := by
  let e (p : ℕ) : Fin (path.visitSequence p).length ≃o path.visitTimes p :=
    (path.visitTimes p).orderIsoOfFin (by simp [visitSequence])
  have he (p : ℕ) (i : Fin (path.visitSequence p).length) :
      (path (e p i).val).storage = (path.visitSequence p)[i.val] := by
    simp only [visitSequence, List.getElem_map]
    rfl
  let cast := Fin.castOrderIso (congrArg List.length hseq)
  refine ⟨hsym, (e cut.left).symm.trans (cast.trans (e cut.right)), ?_⟩
  intro u
  have h := he cut.left ((e cut.left).symm u)
  rw [(e cut.left).apply_symm_apply] at h
  calc
    _ = _ := h
    _ = (path.visitSequence cut.right)[(cast ((e cut.left).symm u)).1] := by congr 1
    _ = _ := (he cut.right (cast ((e cut.left).symm u))).symm

/-- The retained prefix reaches the first running visit to the left boundary. -/
private lemma exists_mapsCore_first_visit {path : tm.ComputationPath input}
    (hsym : input[cut.fst] = input[cut.snd])
    {u : path.visitTimes cut.left} (hu : IsMin u) :
    ∃ c', ReflTransGen tm.Step (tm.initCfg cut.shortened) c' ∧ cut.MapsCore (path u.val) c' := by
  have hinit : cut.MapsCore (path 0) (tm.initCfg cut.shortened) := by
    simpa only [apply_zero] using cut.mapsCore_init
  apply hinit.reaches_path hsym (Fin.zero_le _)
  left
  rintro v ⟨_, hv⟩
  change (path v).inputPos.val ≤ cut.left
  rw [tm.computationPath_apply_eq_runFrom path v]
  apply tm.inputPos_le_of_forall_ne (Nat.zero_le v.val) (by simp [left, runFrom])
  intro r _ hrv hp
  let i : Fin (path.length + 1) := ⟨r, hrv.trans v.isLt⟩
  have hi : i ∈ path.visitTimes cut.left := mem_visitTimes_of_le u.property
    (by exact (hrv.trans_le hv).le)
    (by simpa only [computationPath_apply_eq_runFrom] using hp)
  exact hu.not_lt (b := ⟨i, hi⟩) (by exact hrv.trans_le hv)

namespace VisitPairing

variable {cut} {path : tm.ComputationPath input} (pairing : cut.VisitPairing path)

include pairing

/-- Paired visits represent the same storage at the collapsed boundary. -/
private lemma mapsCore_iff (u : path.visitTimes cut.left)
    {c' : Cfg k Symbol State cut.shortened} :
    cut.MapsCore (path u.val) c' ↔
      cut.MapsCore (path (pairing.orderIso u).val) c' := by
  grind [MapsCore, position, left, right, visitTimes, pairing.storage_eq u, cut.fst_le_snd]

/-- At a paired visit, at least one of the two next steps enters a retained side. -/
private lemma step_sides (u : path.visitTimes cut.left) :
    (tm.step (path u.val)).inputPos.val ≤ cut.left ∨
      cut.right ≤ (tm.step (path (pairing.orderIso u).val)).inputPos.val := by
  have hleft := (mem_visitTimes.mp u.property).1
  have hright := (mem_visitTimes.mp (pairing.orderIso u).property).1
  have hsym : (path u.val).inputSymbol =
      (path (pairing.orderIso u).val).inputSymbol := by
    grind [Cfg.inputSymbol, left, right, pairing.symbol_eq]
  obtain ⟨m, _, hm, hm'⟩ := tm.exists_step_move_of_storage_eq (pairing.storage_eq u) hsym
  cases m <;> grind [moveInputPos_val, SignType.cast,
    left, right]

/-- Between consecutive paired visits, follow the excursion on a retained side. -/
private lemma reaches_next_visit {u v : path.visitTimes cut.left}
    (huv : u ⋖ v) {c' : Cfg k Symbol State cut.shortened}
    (h : cut.MapsCore (path u.val) c') :
    ∃ d, ReflTransGen tm.Step c' d ∧
      cut.MapsCore (path v.val) d := by
  rcases pairing.step_sides u with hleft | hright
  · exact h.reaches_path pairing.symbol_eq huv.le
      (.inl fun t ht => (inputPos_bounds_of_covBy huv ht).1 hleft)
  · have he := (apply_covBy_apply_iff pairing.orderIso).mpr huv
    obtain ⟨d, hd, hm⟩ := ((pairing.mapsCore_iff u).mp h).reaches_path
      pairing.symbol_eq he.le (.inr fun t ht => (inputPos_bounds_of_covBy he ht).2 hright)
    exact ⟨d, hd, (pairing.mapsCore_iff v).mpr hm⟩

/-- Induct over the paired visits, starting with the retained prefix. -/
private lemma exists_mapsCore_left_visit (u : path.visitTimes cut.left) :
    ∃ c', ReflTransGen tm.Step (tm.initCfg cut.shortened) c' ∧
      cut.MapsCore (path u.val) c' := by
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
lemma exists_mapsCore_visit {t : Fin (path.length + 1)}
    (ht : t ∈ path.visitTimes cut.left ∪
      path.visitTimes cut.right) :
    ∃ c', ReflTransGen tm.Step (tm.initCfg cut.shortened) c' ∧
      cut.MapsCore (path t) c' := by
  rcases Finset.mem_union.mp ht with ht | ht
  · exact pairing.exists_mapsCore_left_visit ⟨t, ht⟩
  · let v := pairing.orderIso.symm ⟨t, ht⟩
    obtain ⟨c', hr, hm⟩ := pairing.exists_mapsCore_left_visit v
    exact ⟨c', hr, by
      simpa only [v, pairing.orderIso.apply_symm_apply] using (pairing.mapsCore_iff v).mp hm⟩

/-- Paired boundary visits preserve every running configuration outside the cut. -/
theorem exists_mapsCore {t : Fin (path.length + 1)} (ht : ¬(path t).Halted)
    (hp : (path t).inputPos.val ≤ cut.left ∨ cut.right ≤ (path t).inputPos.val) :
    ∃ c', ReflTransGen tm.Step (tm.initCfg cut.shortened) c' ∧ cut.MapsCore (path t) c' := by
  induction t using Fin.induction with
  | zero => exact ⟨_, .refl, by simpa only [apply_zero] using cut.mapsCore_init⟩
  | succ t ih =>
    by_cases hb : (path t.succ).inputPos.val = cut.left ∨
        (path t.succ).inputPos.val = cut.right
    · apply pairing.exists_mapsCore_visit
      simpa only [Finset.mem_union, mem_visitTimes] using
        hb.imp (fun h ↦ ⟨h, ht⟩) (fun h ↦ ⟨h, ht⟩)
    have heq := step_iff.mp (path.step t)
    have hbounds := tm.inputPos_step_le (path t.castSucc)
    rw [heq] at hbounds
    have hside := cut.sameSide_of_not_boundary hbounds hp hb
    obtain ⟨c', hr, hm⟩ := ih
      (MultiTapeNTM.RunPath.not_halted_of_le path.toRunPath (by exact Nat.le_succ t.val) ht)
      (hside.imp And.left And.left)
    refine ⟨tm.step c', hr.tail (step_iff.mpr rfl), ?_⟩
    rw [← heq] at hside ⊢
    exact hm.step pairing.symbol_eq hside

end VisitPairing

end InputCut

/-- Equal boundary symbols and visit sequences preserve a step on a retained side. -/
theorem exists_storage_cut (cut : InputCut input) {path : tm.ComputationPath input}
    (hsym : input[cut.fst] = input[cut.snd])
    (hseq : path.visitSequence cut.left = path.visitSequence cut.right)
    (i : Fin path.length) (hi : ¬(path i.castSucc).Halted)
    (hp : cut.SameSide (path i.castSucc).inputPos.val (path i.succ).inputPos.val) :
    ∃ u, (tm.runFrom (tm.initCfg cut.shortened) u).storage = (path i.succ).storage := by
  obtain ⟨c', hr, hm⟩ := (InputCut.visitPairing cut hsym hseq).exists_mapsCore hi
    (hp.imp And.left And.left)
  have heq := step_iff.mp (path.step i)
  rw [← heq] at hp
  have hm := hm.step hsym hp
  have hr := hr.tail (step_iff.mpr (rfl : tm.step c' = tm.step c'))
  obtain ⟨u, hu⟩ : ∃ u, tm.runFrom (tm.initCfg cut.shortened) u = tm.step c' := by
    generalize hd : tm.step c' = d at hr ⊢
    clear hd
    induction hr with
    | refl => exact ⟨0, rfl⟩
    | @tail c d hr hstep ih =>
      obtain ⟨u, rfl⟩ := ih
      exact ⟨u + 1, by simpa only [runFrom, Function.iterate_succ_apply'] using step_iff.mp hstep⟩
  exact ⟨u, by rw [hu, ← heq]; exact hm.2⟩

/-- Distinct running visits in a halting computation have distinct storages. -/
lemma storage_injOn_visitTimes {path : tm.ComputationPath input} {p : ℕ}
    (hhalt : path.last.Halted) :
    Set.InjOn (fun i ↦ (path i).storage) (path.visitTimes p) := by
  have hh : (tm.runFrom (tm.initCfg input) path.time).Halted :=
    tm.computationPath_last_eq_runFrom path ▸ hhalt
  obtain ⟨T, _, hT⟩ := tm.exists_haltsAt hh
  intro a ha b hb heq
  wlog hab : a ≤ b generalizing a b
  · exact (this hb ha heq.symm (le_of_not_ge hab)).symm
  have ha := mem_visitTimes.mp ha
  have hb := mem_visitTimes.mp hb
  simp only [computationPath_apply_eq_runFrom] at ha hb heq
  have hbT : b.val ≤ T := by
    by_contra h
    exact hb.2 (by
      rw [tm.runFrom_eq_of_halt (tm.initCfg input) (by omega) hT.halted]
      exact hT.halted)
  have hcore := tm.core_runFrom_eq_of_core_eq
    (Prod.ext (Fin.ext (ha.1.trans hb.1.symm)) heq) (T - b.val)
  simp only [runFrom] at hcore
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
    Nat.sub_add_cancel hbT] at hcore
  have hh : (tm.runFrom (tm.initCfg input) (T - b.val + a.val)).Halted := by
    have := congrArg (fun c ↦ c.2.state) hcore
    exact this.trans hT.halted
  have := hT.le_of_halted hh
  exact Fin.ext (by omega)

/-- A sufficiently long input to a halting space-bounded machine can be shortened while
preserving any storage reached by the run. -/
theorem exists_shorter_input_storage [Fintype Symbol] [Fintype State] {s : ℕ}
    (hhalt : tm.Halts input)
    (hs : ∀ t, tm.spaceUsed (tm.initCfg input) t ≤ s)
    (hlen : 2 * Fintype.card Symbol *
      (storageBound Symbol State k s + 1) ^ storageBound Symbol State k s + 1 < input.length)
    (t : ℕ) :
    ∃ input' : List Symbol, input'.length < input.length ∧
      ∃ u, (tm.runFrom (tm.initCfg input') u).storage =
        (tm.runFrom (tm.initCfg input) t).storage := by
  classical
  obtain ⟨T, hT⟩ := tm.halts_iff_exists_runFrom.mp hhalt
  obtain ⟨T, _, hT⟩ := tm.exists_haltsAt hT
  have hTpos : 0 < T := by
    by_contra h
    have := hT.halted
    simp_all [Nat.eq_zero_of_not_pos h, runFrom, Cfg.Halted, Cfg.init]
  rcases t with _ | t
  · exact ⟨[], by simpa using (show 0 < input.length by omega), 0, rfl⟩
  let path := tm.computationPath input T
  let i : Fin path.length := ⟨min t (T - 1), by change min t (T - 1) < T; omega⟩
  have hi : ¬(path i.castSucc).Halted := hT.not_halted i.isLt
  have hlast : path.last.Halted := hT.halted
  have htarget : path i.succ = tm.runFrom (tm.initCfg input) (t + 1) := by
    change tm.runFrom (tm.initCfg input) (min t (T - 1) + 1) = _
    by_cases ht : t < T
    · rw [min_eq_left (by omega)]
    · rw [min_eq_right (by omega), Nat.sub_add_cancel hTpos]
      exact (hT.runFrom_eq (by omega)).symm
  let B := storageBound Symbol State k s
  let S := Set.range (fun u : Fin (path.length + 1) ↦ (path u).storage)
  have hbound : S.encard ≤ B := by
    apply (Set.encard_mono (b := Set.range fun u ↦
      (tm.runFrom (tm.initCfg input) u).storage) ?_).trans (tm.encard_storages_le hs)
    rintro _ ⟨u, rfl⟩
    exact ⟨u.val, (congrArg Cfg.storage (tm.computationPath_apply_eq_runFrom path u)).symm⟩
  let : Fintype S := (Set.finite_of_encard_le_coe hbound).fintype
  have hcard : Fintype.card S ≤ B := by
    exact_mod_cast (Set.coe_fintypeCard (s := S)).le.trans hbound
  let seq (p : ℕ) : List S := ((path.visitTimes p).sort (· ≤ ·)).map
    (fun u ↦ ⟨(path u).storage, ⟨u, rfl⟩⟩)
  have hseq_map (p : ℕ) : (seq p).map Subtype.val = path.visitSequence p := by
    simp [seq, visitSequence, List.map_map]
  have hlength (p : ℕ) : (seq p).length ≤ B := by
    simp only [seq, List.length_map, Finset.length_sort]
    rw [← Fintype.card_coe]
    apply le_trans (Fintype.card_le_of_injective
      (fun u : path.visitTimes p ↦ (⟨(path u.val).storage, ⟨u.val, rfl⟩⟩ : S)) ?_) hcard
    intro u v huv
    exact Subtype.ext (tm.storage_injOn_visitTimes hlast u.property v.property
      (congrArg Subtype.val huv))
  let p := max (path i.castSucc).inputPos.val (path i.succ).inputPos.val
  -- Matching positions on the same side of both configurations retain their connecting step.
  let f (j : Fin input.length) : Bool × Symbol × (Fin B → Option S) :=
    (decide (j.val + 1 < p), input[j], fun n ↦ (seq (j.val + 1))[n.val]?)
  have hsig : Fintype.card (Bool × Symbol × (Fin B → Option S)) < input.length := by
    calc
      _ = 2 * Fintype.card Symbol * (Fintype.card S + 1) ^ B := by simp [mul_assoc]
      _ ≤ 2 * Fintype.card Symbol * (B + 1) ^ B := by gcongr; omega
      _ < input.length := by dsimp only [B]; omega
  obtain ⟨a, b, hab, hf⟩ : ∃ a b, a < b ∧ f a = f b := by
    obtain ⟨a, b, hne, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simpa using hsig)
    grind
  obtain ⟨hside, hsym, hseq⟩ := (by simpa only [f, Prod.mk.injEq, decide_eq_decide] using hf)
  have hseq' : seq (a.val + 1) = seq (b.val + 1) := by
    apply List.ext_getElem?
    intro r
    by_cases hr : r < B
    · exact congrFun hseq ⟨r, hr⟩
    · rw [List.getElem?_eq_none ((hlength _).trans (Nat.le_of_not_gt hr)),
        List.getElem?_eq_none ((hlength _).trans (Nat.le_of_not_gt hr))]
  let cut : InputCut input := ⟨⟨a, b⟩, hab.le⟩
  refine ⟨cut.shortened, ?_, ?_⟩
  · have := cut.length_shortened_add
    change cut.shortened.length + (b.val + 1 - (a.val + 1)) = input.length at this
    omega
  rw [← htarget]
  refine tm.exists_storage_cut cut hsym ?_ i hi ?_
  · change path.visitSequence (a.val + 1) = path.visitSequence (b.val + 1)
    rw [← hseq_map, ← hseq_map, hseq']
  · have hbounds := tm.inputPos_step_le (path i.castSucc)
    rw [step_iff.mp (path.step i)] at hbounds
    have hbounds := abs_le.mp hbounds
    dsimp only [InputCut.SameSide, cut, InputCut.left, InputCut.right] at ⊢
    dsimp only [p] at hside
    omega

end Turing.MultiTapeTM

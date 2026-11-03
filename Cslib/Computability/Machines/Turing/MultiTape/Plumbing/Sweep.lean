/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential

/-!
# Sweeping pairs of work tapes

A machine with `k + k` work tapes groups them into `k` pairs: the work tape `Fin.castAdd k i` and
its helper tape `Fin.natAdd k i`, whose heads move together. `sweep go fW fH d gH e` walks every
pair in direction `d` while the helper symbol under it satisfies `go`, rewriting the work cell by
`fW` and the helper cell by `fH` on the way. A pair whose helper fails `go` waits, so the pairs may
stop at different times. Once all of them have stopped, every pair rewrites its helper cell by `gH`
and moves by `e`, and the machine halts.

## Main definitions

* `Turing.MultiTapeTM.pairCfg`: a configuration of `k` pairs of tapes.
* `Turing.MultiTapeTM.sweep`: the sweeping machine.
* `Turing.MultiTapeTM.walked`: a tape after a walk that rewrites the cells it leaves.

## Main results

* `Turing.MultiTapeTM.sweep_runsWithin`: if pair `i` meets the first cell failing `go` after
  `m i ≤ n` cells, the machine runs to the walked tapes in at most `n + 1` steps.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The configuration of `k` pairs of tapes: work tape `i` holds `W i`, its helper holds `H i`, and
both heads of pair `i` stand at `x i`. -/
@[simps]
def pairCfg (q : Option State) (ip : Fin (input.length + 2)) (W H : Fin k → ℤ → Option Symbol)
    (x : Fin k → ℤ) (out : List Symbol) : Cfg (k + k) Symbol State input :=
  ⟨q, ip, Fin.append W H, Fin.append x x, out⟩

/-- `Fin.append` at `i.addNat k`, the simp normal form of `Fin.natAdd k i` in `Fin (k + k)`. -/
@[simp] lemma _root_.Fin.append_addNat {α : Sort*} (u v : Fin k → α) (i : Fin k) :
    Fin.append u v (i.addNat k) = v i := by
  rw [← Fin.natAdd_eq_addNat, Fin.append_right]

/-- The sweeping machine. While some pair reads a helper symbol `h` with `go h`, every such pair
writes `fW` of its work symbol and `fH h`, and moves by `d`; the other pairs wait. Once no pair
goes, every pair writes `gH h` on its helper and moves by `e`, and the machine halts. -/
def sweep (go : Option Symbol → Bool) (fW fH : Option Symbol → Option Symbol) (d : SignType)
    (gH : Option Symbol → Option Symbol) (e : SignType) : MultiTapeTM (k + k) Symbol Unit :=
  ofTr () fun _ _ w =>
    let h i := w (Fin.natAdd k i)
    if ∀ i, go (h i) = false then
      ⟨0, Fin.append (fun _ => (none, e)) fun i => (some (gH (h i)), e), none, none⟩
    else
      ⟨0, Fin.append (fun i => if go (h i) then (some (fW (w (Fin.castAdd k i))), d) else (none, 0))
        fun i => if go (h i) then (some (fH (h i)), d) else (none, 0), none, some ()⟩

variable {d : SignType} {f : Option Symbol → Option Symbol} {x : ℤ} {n : ℕ}
  {T : ℤ → Option Symbol}

/-- The tape `T` after walking `n` cells from `x` in direction `d`, rewriting each cell left by
`f`. -/
def walked (d : SignType) (f : Option Symbol → Option Symbol) (x : ℤ) (n : ℕ)
    (T : ℤ → Option Symbol) (z : ℤ) : Option Symbol :=
  if 0 ≤ d * (z - x) ∧ d * (z - x) < n then f (T z) else T z

@[simp] lemma walked_zero : walked d f x 0 T = T := by
  funext z
  simp [walked]

@[simp] lemma walked_id : walked d id x n T = T := by
  funext z
  simp [walked]

private lemma walked_self (hd : d ≠ 0) : walked d f x n T (x + d * n) = T (x + d * n) := by
  rcases d <;> simp_all [walked]

private lemma walked_succ (hd : d ≠ 0) :
    walked d f x (n + 1) T =
      Function.update (walked d f x n T) (x + d * n) (f (T (x + d * n))) := by
  funext z
  rcases d <;> simp_all [walked, Function.update_apply] <;> split_ifs <;> grind

variable {go : Option Symbol → Bool} {fW fH gH : Option Symbol → Option Symbol} {e : SignType}
  {ip : Fin (input.length + 2)} {W H W' H' : Fin k → ℤ → Option Symbol} {x y : Fin k → ℤ}
  {out : List Symbol}

/-- **The run of a sweep.** If pair `i` reads helper symbols satisfying `go` on its first
`m i ≤ n` cells in direction `d` and fails `go` on the next, the sweep walks each pair over those
cells, leaving the tapes `W'` and `H'` and the heads at `y`, in at most `n + 1` steps. The heads
stay in `S` if the cells walked over and the ends are in `S`. -/
theorem sweep_runsWithin (hd : d ≠ 0) (m : Fin k → ℕ) {n : ℕ} (hn : ∀ i, m i ≤ n)
    (hgo : ∀ i, ∀ j < m i, go (H i (x i + d * j)))
    (hstop : ∀ i, go (H i (x i + d * m i)) = false)
    (hW : ∀ i, walked d fW (x i) (m i) (W i) = W' i)
    (hH : ∀ i, Function.update (walked d fH (x i) (m i) (H i)) (x i + d * m i)
      (gH (H i (x i + d * m i))) = H' i)
    (hy : ∀ i, x i + d * m i + e = y i) {S : Fin k → Finset ℤ}
    (hS : ∀ i, ∀ j ≤ m i, x i + d * j ∈ S i) (hS' : ∀ i, y i ∈ S i) :
    (sweep go fW fH d gH e).RunsWithin (pairCfg (some ()) ip W H x out)
      (pairCfg none ip W' H' y out) (n + 1) (Fin.append S S) := by
  obtain rfl : W' = _ := funext fun i => (hW i).symm
  obtain rfl : H' = _ := funext fun i => (hH i).symm
  obtain rfl : y = _ := funext fun i => (hy i).symm
  -- the configuration after `j` steps, while some pair walks: pair `i` has walked `min j (m i)`
  let c (j : ℕ) : Cfg (k + k) Symbol Unit input := pairCfg (some ()) ip
    (fun i => walked d fW (x i) (min j (m i)) (W i))
    (fun i => walked d fH (x i) (min j (m i)) (H i)) (fun i => x i + d * min j (m i)) out
  have hgo' j i : go (walked d fH (x i) (min j (m i)) (H i) (x i + d * (min j (m i) : ℕ))) =
      decide (j < m i) := by
    rw [walked_self hd]
    by_cases h : j < m i
    · simpa [h, min_eq_left h.le] using hgo i j h
    · simpa [h, min_eq_right (not_lt.mp h)] using hstop i
  have hstep j (hj : j < Finset.univ.sup m) : (sweep go fW fH d gH e).Step (c j) (c (j + 1)) := by
    obtain ⟨i₀, -, hi₀⟩ := Finset.lt_sup_iff.mp hj
    have hrun : ¬ ∀ i, decide (j < m i) = false := fun h => by simpa [hi₀] using h i₀
    rw [step_iff, step_of_state rfl]
    simp only [c, sweep, tr_ofTr, Cfg.workTapeSymbols, pairCfg_workTapes, pairCfg_workTapePos,
      Fin.append_right, Fin.append_left, hgo', hrun, ite_false]
    refine Cfg.ext rfl (by simp [Action.apply]) (funext fun l => ?_) (funext fun l => ?_)
      (by simp [Action.apply]) <;> refine Fin.addCases (fun i => ?_) (fun i => ?_) l <;>
      by_cases h : j < m i <;>
      simp [Action.apply, pairCfg, h, walked_succ hd, walked_self hd, add_assoc, mul_add,
        show j < m i → min (j + 1) (m i) = j + 1 by omega,
        show j < m i → min j (m i) = j by omega, show ¬j < m i → min (j + 1) (m i) = m i by omega,
        show ¬j < m i → min j (m i) = m i by omega]
  have hlast : (sweep go fW fH d gH e).Step (c (Finset.univ.sup m)) (pairCfg none ip
      (fun i => walked d fW (x i) (m i) (W i))
      (fun i => Function.update (walked d fH (x i) (m i) (H i)) (x i + d * m i)
        (gH (H i (x i + d * m i)))) (fun i => x i + d * m i + e) out) := by
    rw [step_iff, step_of_state rfl]
    simp only [c, fun i => min_eq_right (Finset.le_sup (f := m) (Finset.mem_univ i)), sweep,
      tr_ofTr, Cfg.workTapeSymbols, pairCfg_workTapes, pairCfg_workTapePos, Fin.append_right,
      walked_self hd, hstop, implies_true, ite_true]
    refine Cfg.ext rfl (by simp [Action.apply]) (funext fun l => ?_) (funext fun l => ?_)
      (by simp [Action.apply]) <;> refine Fin.addCases (fun i => ?_) (fun i => ?_) l <;>
      simp [Action.apply, pairCfg]
  -- every head of every configuration stays in `S`
  have hc j : ∀ l, (c j).workTapePos l ∈ Fin.append S S l := Fin.addCases
    (fun i => by simpa [c] using hS i _ (min_le_right _ _))
    (fun i => by simpa [c] using hS i _ (min_le_right _ _))
  have hrun j (hj : j ≤ Finset.univ.sup m) :
      (sweep go fW fH d gH e).RunsWithin (c 0) (c j) j (Fin.append S S) := by
    induction j with
    | zero => exact .refl (hc 0)
    | succ j ih => exact (ih (by omega)).trans (.single (hstep j hj) (hc j) (hc (j + 1)))
  simpa [c] using ((hrun _ le_rfl).trans (.single hlast (hc _)
    (Fin.addCases (by simpa using hS' ·) (by simpa using hS' ·)))).mono
    (Nat.succ_le_succ (Finset.sup_le fun i _ => hn i)) fun _ => subset_rfl

end Turing.MultiTapeTM

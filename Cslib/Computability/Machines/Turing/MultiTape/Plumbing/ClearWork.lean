/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ForwardWork
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential

/-!
# A machine that clears a work tape

`clearWork Symbol` erases the word on its work tape and returns the head to the start. It never
moves the input head and never outputs. It is the sequential composition of two one-tape machines:

* `forwardWork Symbol` moves the head right over the word until it reads the first blank, the
  frontier just past the word, and halts there (see `Plumbing.ForwardWork`).
* `rewindWork Symbol (some none)` rewinds the head to the start, erasing every symbol it walks
  over.

On a word of length `l` the forward pass takes `l + 1` steps and the erasing rewind `l + 2` steps.
The head stays within the cells `-1, …, l`, so the machine runs in time `3 * (l + 1)` and space
`l + 2`; placed on tape `i` of `k` tapes, the remaining tapes contribute one cell each.

## Main results

* `Turing.MultiTapeTM.clearWork`: the one-tape machine that clears its tape.
* `Turing.MultiTapeTM.transformsTapes_clearWork`: a run of `clearWork` replaces the word on its
  tape by the empty word.
* `Turing.MultiTapeTM.transformsTapes_clearWork_tapeEmb`: placed on tape `i` of a `k`-tape machine
  it does so on that tape and leaves every other tape unchanged.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol : Type*} {input : List Symbol}

/-- The one-tape machine that clears its tape: it moves to the end of the word and erases it on
the way back. -/
public noncomputable def clearWork (Symbol : Type*) :
    MultiTapeTM 1 Symbol (Unit ⊕ RewindWorkState) :=
  (forwardWork Symbol).seq (rewindWork Symbol (some none))

open Sequential MultiTapeNTM in
/-- **The machine that clears its work tape** replaces the word `w` on it by the empty word, in at
most `3 * (w.length + 1)` steps and `w.length + 2` cells. -/
public theorem transformsTapes_clearWork (w input out : List Symbol) :
    ∃ p : (clearWork Symbol).RunPath input, p.TransformsTapes (fun _ => w) (fun _ => []) out [] ∧
      p.time ≤ 3 * (w.length + 1) ∧ p.space ≤ w.length + 2 := by
  unfold clearWork
  -- the forward pass takes `w.length + 1` steps, the erasing rewind `w.length + 2`
  let p₀ := RunPath.ofDeterministic (forwardWork Symbol)
    (wordsCfg input (some ()) (fun _ => w) out) (w.length + 1)
  let p₁ := RunPath.ofDeterministic (rewindWork Symbol (some none))
    (⟨some (rewindWork Symbol (some none)).q₀, 1, fun _ => tapeOfList w, fun _ => w.length, out⟩ :
      Cfg 1 Symbol RewindWorkState input) (w.length + 2)
  have h₀ : p₀.last = _ := runFrom_forwardWork (input := input) 1 w out (zero_add _)
  have h₁ : p₁.last = _ := runFrom_rewindWork_erase (input := input) 1 (tapeOfList w) out rfl
  refine ⟨p₀.seqPath p₁ (by rw [h₀]) (by rw [h₀]; rfl), ⟨by simp [p₀, leftCfg]; rfl,
    by simp [h₁, rightCfg, Cfg.mapState, wordsCfg]⟩,
    RunPath.time_seqPath_le.trans (show w.length + 1 + (w.length + 2) ≤ _ by lia), ?_⟩
  -- every head position of the two passes is in `[-1, w.length]`
  rw [RunPath.space, Fin.sum_univ_one]
  refine (RunPath.spaceUsedByTape_le_card _ (S := .Icc (-1) (w.length : ℤ)) fun c hc => ?_).trans
    (by simp; lia)
  rcases RunPath.mem_seqPath hc with ⟨_, ⟨m, rfl⟩, he⟩ | ⟨_, ⟨m, rfl⟩, he⟩ <;>
    rw [show c.workTapePos 0 = _ from congrArg (·.workTapePos 0) he]
  · exact Finset.mem_Icc.2 (Set.Icc_subset_Icc_left (by lia)
      (workTapePos_runFrom_forwardWork (input := input) 1 w out (Nat.zero_le w.length) m))
  · exact Finset.mem_Icc.2
      (workTapePos_runFrom_rewindWork (some none) (input := input) 1 (tapeOfList w) out rfl
        le_rfl m)

/-! ### Clearing one of several work tapes -/

/-- **The machine that clears a work tape**, placed on tape `i` of a `k`-tape machine, replaces the
word on that tape by the empty word and leaves every other tape unchanged, in at most
`3 * ((ws i).length + 1)` steps and `(ws i).length + 1 + k` cells. -/
public theorem transformsTapes_clearWork_tapeEmb (i : Fin k) (ws : Fin k → List Symbol)
    (input out : List Symbol) :
    ∃ p : ((clearWork Symbol).extendTapes (tapeEmb i)).RunPath input,
      p.TransformsTapes ws (Function.update ws i []) out [] ∧ p.time ≤ 3 * ((ws i).length + 1) ∧
        p.space ≤ (ws i).length + 1 + k := by
  obtain ⟨p, hp, htime, hspace⟩ := transformsTapes_clearWork (ws i) input out
  exact ⟨p.onTape i ws, hp.onTape, htime, (p.space_onTape_le i ws).trans (by have := i.pos; lia)⟩

end Turing.MultiTapeTM

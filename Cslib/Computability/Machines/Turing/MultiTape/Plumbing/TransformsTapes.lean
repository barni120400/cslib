/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# Machines as transformers of tape words

The interface through which combinators use machines: a machine reads words from its work tapes
and leaves words on them. A combinator composing such machines talks about words only, never about
individual cells, head positions or the set of tapes a machine has touched.

Configurations are described by *equalities*: `wordsCfg input q ws out` is the configuration whose
work tape `i` holds exactly the word `ws i` (contents `tapeOfList (ws i)`, head at the start), with
the input head at the start of the input and output `out`. A run path `p` transforms the words `ws`
into `ws'`, `p.TransformsTapes ws ws' out emitted`, when it runs from the initial state on `ws` to
the halted *normal form* `wordsCfg input none ws' (out ++ emitted)` (every head reset to its initial
position, tapes blank outside their words, the word `emitted` appended to the output it was
handed). Its time and space are those of the path, `p.time` and `p.space`.
Requiring this normal form is what lets run paths compose by rewriting: the halting configuration
of one machine is already a valid start for the next, so which words survived a step is read off
the equation, not re-established cell by cell.

The output is described as the word the machine *appends*, never as an absolute value, so that a
run is insensitive to the output it is handed — which is what lets runs compose: along a sequence
the emitted words concatenate.

## Main definitions

* `Turing.MultiTapeNTM.RunPath.TransformsTapes`: a run path transforming tape words.
* `Turing.MultiTapeTM.nop`: the machine that does nothing.

## Main results

* `Turing.MultiTapeTM.transformsTapes_nop`: `nop` leaves every word as it was, the first machine of
  the interface and the check that the format is inhabited as intended.
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

namespace MultiTapeNTM.RunPath

/-- The run path `p` transforms the words `ws` into the words `ws'`, appending `emitted` to the
output `out`: it runs from the initial state on `ws` to the halted configuration on `ws'`. -/
structure TransformsTapes {ntm : MultiTapeNTM k Symbol State} (p : ntm.RunPath input)
    (ws ws' : Fin k → List Symbol) (out emitted : List Symbol) : Prop where
  /-- the path starts in the initial state on `ws`, with output `out` -/
  head_eq : p.head = wordsCfg input (some ntm.q₀) ws out
  /-- the path ends halted on `ws'`, with `emitted` appended to `out` -/
  last_eq : p.last = wordsCfg input none ws' (out ++ emitted)

/-- A run path transforming tape words ends halted. -/
lemma TransformsTapes.halted {ntm : MultiTapeNTM k Symbol State} {p : ntm.RunPath input}
    {ws ws' : Fin k → List Symbol} {out emitted : List Symbol}
    (h : p.TransformsTapes ws ws' out emitted) : p.last.Halted := by
  rw [h.last_eq]
  rfl

end MultiTapeNTM.RunPath

namespace MultiTapeTM

open MultiTapeNTM

section Nop

/-- The machine that does nothing: it halts on its first step, leaving the configuration
unchanged. -/
def nop (k : ℕ) (Symbol : Type*) : MultiTapeTM k Symbol Unit :=
  ofTr () fun _ _ _ =>
    { inputTape := 0, workTapes := fun _ => (none, 0), output := none, state := none }

/-- A single step of `nop` halts and leaves the words alone. -/
@[simp]
lemma step_nop (ws : Fin k → List Symbol) (out : List Symbol) :
    (nop k Symbol).step (wordsCfg input (some ()) ws out) = wordsCfg input none ws out := by
  rw [step_of_state (by rfl)]
  simp [nop, Action.apply, wordsCfg, SignType.cast]

/-- `nop` reaches its halting configuration after exactly one step. -/
@[simp]
lemma runFrom_nop_one (ws : Fin k → List Symbol) (out : List Symbol) :
    (nop k Symbol).runFrom (wordsCfg input (some ()) ws out) 1 = wordsCfg input none ws out := by
  simpa only [runFrom, Function.iterate_one] using step_nop ws out

/-- **The machine that does nothing** halts in one step, leaving every word as it was and emitting
nothing. Its heads never move, so it visits one cell per tape. This is the first machine of the
interface: it checks that the format is inhabited exactly as intended. -/
theorem transformsTapes_nop (input : List Symbol) (ws : Fin k → List Symbol) (out : List Symbol) :
    ∃ p : (nop k Symbol).RunPath input, p.TransformsTapes ws ws out [] ∧ p.time = 1 ∧
      p.space ≤ k := by
  refine ⟨.ofDeterministic _ (wordsCfg input (some ()) ws out) 1,
    ⟨rfl, by rw [List.append_nil]; exact runFrom_nop_one ws out⟩, rfl, ?_⟩
  -- the heads never move, so each head visits only the single cell `0`
  refine (RunPath.space_le_sum_card _ (S := fun _ => {0}) ?_).trans_eq (by simp)
  rintro _ ⟨⟨m, hm⟩, rfl⟩ i
  change m < 2 at hm
  rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl <;>
    simp [RunPath.ofDeterministic]

end Nop

end MultiTapeTM

end Turing

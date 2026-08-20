/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module

public import Mathlib.Data.List.Chain
public import Mathlib.Order.RelSeries
public import Cslib.Computability.Machines.Turing.MultiTape.Configuration

/-!
# Nondeterministic Multi-Tape Turing Machines

Defines nondeterministic Turing machines with a read-only input tape, `k` work tapes and one
write-only output tape, and what it means for one to compute an output within a time and space
bound.

## Design

Following [Papadimitriou94], chapter 2.7, a nondeterministic machine is a Turing machine whose
transition function is replaced by a transition relation: `Tr q input work action` holds when
`action` is one of the actions permitted in that situation.

A halted configuration steps to itself, so once a machine has halted it has a run of every length.
A time bound is therefore an upper bound, with no separate account of the step at which it halted.

The transition relation may be empty at a running configuration, so a machine can get stuck. Every
notion below asks for a computation ending in a halted configuration, so a stuck one is not a
witness.

## Important Declarations

* `MultiTapeNTM`: the machine, an initial state and a transition relation
* `Step`: the one-step relation on configurations
* `IsDeterministic`: every situation permits exactly one transition
* `ComputationPath`: a run of the machine: a series of configurations from the initial one, each
    reached from the previous by a step
* `ComputesSuchThat`: some computation halts, emits a given output and meets a given constraint
* `Computes`, `ComputesInTime`, `ComputesInSpace`, `ComputesInTimeAndSpace`: its instances, whose
    bounds all refer to a single computation

## References

* [C. Papadimitriou, *Computational Complexity*][Papadimitriou94]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Turing

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}

/--
A nondeterministic multi-tape Turing machine with `k` work tapes over the alphabet of
`Option Symbol` (where `none` is the blank symbol). Neither `Symbol` nor `State` is required to be
finite.
-/
structure MultiTapeNTM (k : ℕ) (Symbol State : Type*) where
  /-- initial state -/
  q₀ : State
  /-- transition relation: which combinations of state, current input symbol, tuple of work head
  symbols and resulting actions are valid transitions -/
  Tr (q : State) (input : Option Symbol) (work : Fin k → Option Symbol)
    (action : Action k Symbol State) : Prop

namespace MultiTapeNTM

variable {ntm : MultiTapeNTM k Symbol State}

/-- The one-step relation on configurations. A halted configuration steps to itself; a running one
steps by any permitted transition. -/
@[scoped grind =]
def Step (ntm : MultiTapeNTM k Symbol State) (c₁ c₂ : Cfg k Symbol State input) : Prop :=
  match c₁.state with
  | none => c₂ = c₁
  | some q => ∃ out, ntm.Tr q c₁.inputSymbol c₁.workTapeSymbols out ∧ c₂ = out.apply c₁

/-- A halted configuration steps only to itself. -/
lemma step_of_halt {c c' : Cfg k Symbol State input} (h : c.Halted) :
    ntm.Step c c' ↔ c' = c := by
  simp [Step, h]

/-- A machine is deterministic when every situation permits exactly one transition. A deterministic
multi-tape Turing machine is exactly a machine of this kind, see
`MultiTapeTM.isDeterministic`. -/
def IsDeterministic (ntm : MultiTapeNTM k Symbol State) : Prop :=
  ∀ (q : State) (input : Option Symbol) (work : Fin k → Option Symbol),
    ∃! out, ntm.Tr q input work out

/-- The initial configuration corresponding to an input string. -/
@[simp]
def initCfg (ntm : MultiTapeNTM k Symbol State) (input : List Symbol) :
    Cfg k Symbol State input :=
  Cfg.init ntm.q₀ input

/-- A run of `ntm` on `input`: a series of configurations in which each is reached from the
previous by a step. It may start anywhere; a `ComputationPath` is one that starts at the initial
configuration. `RelSeries` supplies the series itself, so `length` is the number of steps taken,
`toList` the configurations passed through, and `head` and `last` the ones it starts and ends at. -/
structure Run (ntm : MultiTapeNTM k Symbol State) (input : List Symbol)
  extends RelSeries {(c₁, c₂) : Cfg k Symbol State input × _ | ntm.Step c₁ c₂}

namespace Run

variable {ntm : MultiTapeNTM k Symbol State} {input : List Symbol}

/-- The work tape cells the head of tape `i` visits during the run. -/
def visited (p : ntm.Run input) (i : Fin k) : Finset ℤ :=
  (p.toList.map (·.workTapePos i)).toFinset

/-- The number of work tape cells the head of tape `i` touches during the run. -/
def spaceByTape (p : ntm.Run input) (i : Fin k) : ℕ := (p.visited i).card

/-- The number of work tape cells the run touches, its space usage. -/
def space (p : ntm.Run input) : ℕ := ∑ i, p.spaceByTape i

end Run

/-- A computation of `ntm` on `input`: a run starting at the initial configuration. -/
structure ComputationPath (ntm : MultiTapeNTM k Symbol State) (input : List Symbol)
    extends Run ntm input where
  /-- a computation starts at the initial configuration -/
  head_eq : toRun.head = ntm.initCfg input

/-- `ntm` has a computation on `input` that starts at the initial configuration, halts, emits
`output` and satisfies `P`. The notions below are its instances, so their constraints all refer to
a single computation. -/
def ComputesSuchThat (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol)
    (P : ntm.ComputationPath input → Prop) : Prop :=
  ∃ p : ntm.ComputationPath input, p.last.Halted ∧ p.last.output = output ∧ P p

/-- `ntm` computes `output` from `input`, with no bound on resources. -/
def Computes (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol) : Prop :=
  ntm.ComputesSuchThat input output fun _ => True

/-- `ntm` computes `output` from `input` in exactly `t` steps. -/
def ComputesInTime (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol) (t : ℕ) :
    Prop :=
  ntm.ComputesSuchThat input output fun p => p.length = t

/-- `ntm` computes `output` from `input` touching exactly `s` work tape cells. -/
def ComputesInSpace (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol) (s : ℕ) :
    Prop :=
  ntm.ComputesSuchThat input output fun p => p.space = s

/-- `ntm` computes `output` from `input` in `t` steps and `s` work tape cells, by a single
computation. Nondeterministic analogue of `MultiTapeTM.ComputesInTimeAndSpace`. -/
def ComputesInTimeAndSpace (ntm : MultiTapeNTM k Symbol State) (input output : List Symbol)
    (t s : ℕ) : Prop :=
  ntm.ComputesSuchThat input output fun p => p.length = t ∧ p.space = s

end MultiTapeNTM

end Turing

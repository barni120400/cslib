/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Mathlib.Data.Fintype.Option
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-!
# Repeating a machine until a tape goes blank

`repeatUntilBlank i tm` runs `tm` repeatedly. After each round it reads the cell under the head of
work tape `i` and halts if that cell is blank. Each run of `tm` transforming tapes ends with every
head on the first cell of its word, so the loop halts exactly when the word on tape `i` is empty.
The body always runs at least once.

## Main results

* `Turing.MultiTapeNTM.RunPath.TransformsTapes.roundPath`: one round of the loop on a run of `tm`.
* `Turing.MultiTapeTM.transformsTapes_repeatUntilBlank`: a loop invariant preserved by every round
  gives a run of `repeatUntilBlank i tm`, of at most `(rounds + 1) * (t + 1)` steps and
  `2 * k * s + k` cells.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The states of `repeatUntilBlank i tm`: those of `tm`, and a state `check` for reading tape `i`
between rounds. -/
public inductive RepeatUntilBlankState (State : Type*) where
  /-- The repeated machine is running, in its state `q`. -/
  | run (q : State)
  /-- Tape `i` is being read, between two rounds. -/
  | check

public instance [Finite State] : Finite (RepeatUntilBlankState State) :=
  Finite.of_injective (fun q => match q with | .run q => some q | .check => none)
    fun q q' h => by cases q <;> cases q' <;> simp_all

/-- `tm`, with its halting transitions sent to the state `check`. From `check`, the machine halts
if the cell under the head of tape `i` is blank and otherwise restarts `tm`, moving no head. -/
public noncomputable def repeatUntilBlank (i : Fin k) (tm : MultiTapeTM k Symbol State) :
    MultiTapeTM k Symbol (RepeatUntilBlankState State) :=
  ofTr (.run tm.q₀) fun q inp work =>
    match q with
    | .run q =>
      let a := tm.tr q inp work
      { a with state := some (a.state.elim .check .run) }
    | .check =>
      { inputTape := 0, workTapes := fun _ => (none, 0), output := none,
        state := (work i).map fun _ => .run tm.q₀ }

namespace RepeatUntilBlank

variable {i : Fin k} {tm : MultiTapeTM k Symbol State}

/-- A configuration of `tm` as a configuration of `repeatUntilBlank i tm`: a live state `q` becomes
`run q` and the halted state becomes `check`. -/
def runCfg (cfg : Cfg k Symbol State input) :
    Cfg k Symbol (RepeatUntilBlankState State) input :=
  cfg.mapState (fun st => some (st.elim .check .run))

@[simp]
lemma workTapePos_runCfg (cfg : Cfg k Symbol State input) :
    (runCfg cfg).workTapePos = cfg.workTapePos := rfl

@[simp]
lemma runCfg_wordsCfg_some (q : State) (ws : Fin k → List Symbol) (out : List Symbol) :
    runCfg (input := input) (wordsCfg input (some q) ws out) =
      wordsCfg input (some (.run q)) ws out := rfl

@[simp]
lemma runCfg_wordsCfg_none (ws : Fin k → List Symbol) (out : List Symbol) :
    runCfg (State := State) (input := input) (wordsCfg input none ws out) =
      wordsCfg input (some .check) ws out := rfl

lemma q₀_repeatUntilBlank : (repeatUntilBlank i tm).q₀ = .run tm.q₀ := rfl

/-- On `tm`'s live configurations, the looping machine mirrors `tm` step for step. -/
lemma step_runCfg (cfg : Cfg k Symbol State input) (h : ¬ cfg.Halted) :
    (repeatUntilBlank i tm).step (runCfg cfg) = runCfg (tm.step cfg) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp h
  have hstate : (runCfg cfg).state = some (RepeatUntilBlankState.run q) := by
    simp [runCfg, Cfg.mapState, hq]
  rw [step_of_state hstate, step_of_state hq]
  simp only [repeatUntilBlank, tr_ofTr]
  rfl

/-- From `check` on a `wordsCfg` configuration, the machine halts if the word on tape `i` is empty
and otherwise restarts `tm`, leaving the words unchanged. -/
lemma step_check (ws : Fin k → List Symbol) (out : List Symbol) :
    (repeatUntilBlank i tm).step (wordsCfg input (some .check) ws out) =
      wordsCfg input (if ws i = [] then none else some (.run tm.q₀)) ws out := by
  rw [step_of_state rfl]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> cases h : ws i <;>
    simp [repeatUntilBlank, Cfg.workTapeSymbols, tapeOfList_zero, wordsCfg, Action.apply,
      SignType.cast, h]

end RepeatUntilBlank

end Turing.MultiTapeTM

namespace Turing.MultiTapeNTM.RunPath.TransformsTapes

open MultiTapeTM MultiTapeTM.RepeatUntilBlank

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol} {tm : MultiTapeTM k Symbol State}
  {p : tm.RunPath input} {ws ws' : Fin k → List Symbol} {out e : List Symbol}

/-- One round of the loop on a run of `tm`: the running steps of the run, then reading tape `i`,
which halts the loop if the word left on it is empty and otherwise restarts `tm`. -/
noncomputable def roundPath (h : p.TransformsTapes ws ws' out e) (i : Fin k) :
    (repeatUntilBlank i tm).RunPath input :=
  ((p.untilHalt h.halted).map (runningStepHom runCfg step_runCfg)).snoc
    (wordsCfg input (if ws' i = [] then none else some (.run tm.q₀)) ws' (out ++ e))
    (by simp [h.last_eq, step_check])

variable (h : p.TransformsTapes ws ws' out e) (i : Fin k)

@[simp]
lemma head_roundPath : (h.roundPath i).head = wordsCfg input (some (.run tm.q₀)) ws out := by
  simp [roundPath, h.head_eq]

@[simp]
lemma last_roundPath : (h.roundPath i).last =
    wordsCfg input (if ws' i = [] then none else some (.run tm.q₀)) ws' (out ++ e) := by
  simp [roundPath]

/-- A round takes one step more than the run of `tm` at most. -/
lemma time_roundPath_le : (h.roundPath i).time ≤ p.time + 1 :=
  Nat.add_le_add_right (length_untilHalt_le (h := h.halted)) 1

/-- A round on a run visiting at most `s` cells keeps every head within `[-s, s]`, since the run
starts with every head at cell `0` and reading tape `i` moves none of them. -/
lemma inWindow_roundPath {s : ℕ} (hs : p.space ≤ s) : (h.roundPath i).InWindow s := by
  have hwin := inWindow_of_space_le (p := p) (by simp [h.head_eq]) hs
  intro c hc
  rcases RelSeries.mem_snoc.mp hc with hc | rfl
  · obtain ⟨c₀, hc₀, rfl⟩ := RelSeries.exists_of_mem_map hc
    exact hwin c₀ (mem_of_mem_untilHalt hc₀)
  · simp [mem_window]

end Turing.MultiTapeNTM.RunPath.TransformsTapes

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*}

open MultiTapeNTM in
/-- Let `P n` be a loop invariant after `n` rounds, on the words on the tapes and the word emitted
so far. If each round `n < rounds` runs `tm` from `P n` to `P (n + 1)` and leaves tape `i`
non-empty, and the round after that runs `tm` from `P rounds` to `R` and empties tape `i`, then
`repeatUntilBlank i tm` runs from `P 0` to `R`.

Each of the `rounds + 1` rounds takes at most `t + 1` steps. No head leaves `[-s, s]`, since every
round starts with all heads at cell `0` and uses at most `s` cells. -/
public theorem transformsTapes_repeatUntilBlank (i : Fin k) {tm : MultiTapeTM k Symbol State}
    {P : ℕ → (input : List Symbol) → (Fin k → List Symbol) → List Symbol → Prop}
    {R : (input : List Symbol) → (Fin k → List Symbol) → List Symbol → Prop} {rounds t s : ℕ}
    (hround : ∀ n < rounds, ∀ input ws out emitted, P n input ws emitted →
      ∃ ws' e, ∃ p : tm.RunPath input, p.TransformsTapes ws ws' out e ∧
        P (n + 1) input ws' (emitted ++ e) ∧ ws' i ≠ [] ∧ p.time ≤ t ∧ p.space ≤ s)
    (hstop : ∀ input ws out emitted, P rounds input ws emitted →
      ∃ ws' e, ∃ p : tm.RunPath input, p.TransformsTapes ws ws' out e ∧
        R input ws' (emitted ++ e) ∧ ws' i = [] ∧ p.time ≤ t ∧ p.space ≤ s)
    {input : List Symbol} {ws : Fin k → List Symbol} (out : List Symbol) (hP : P 0 input ws []) :
    ∃ ws' e, ∃ p : (repeatUntilBlank i tm).RunPath input, p.TransformsTapes ws ws' out e ∧
      R input ws' e ∧ p.time ≤ (rounds + 1) * (t + 1) ∧ p.space ≤ 2 * k * s + k := by
  -- after `n ≤ rounds` rounds, the loop has a run path of at most `n * (t + 1)` steps within
  -- `[-s, s]` back to `tm`'s initial state, with `P n` holding
  have hrec : ∀ n ≤ rounds, ∃ wsn acc, P n input wsn acc ∧
      ∃ p : (repeatUntilBlank i tm).RunPath input,
        p.head = wordsCfg input (some (.run tm.q₀)) ws out ∧
        p.last = wordsCfg input (some (.run tm.q₀)) wsn (out ++ acc) ∧
        p.time ≤ n * (t + 1) ∧ p.InWindow s := by
    intro n hn
    induction n with
    | zero =>
      refine ⟨ws, [], hP, .singleton _ (wordsCfg input (some (.run tm.q₀)) ws out), rfl, by simp,
        Nat.zero_le _, ?_⟩
      rintro _ ⟨_, rfl⟩ l
      change (wordsCfg input (some (RepeatUntilBlankState.run tm.q₀)) ws out).workTapePos l ∈ _
      simp [mem_window]
    | succ n ih =>
      obtain ⟨wsn, acc, hPn, p, hhead, hlast, htime, hwin⟩ := ih (by lia)
      obtain ⟨wsn', e, q, hq, hPn', hne, hqtime, hqspace⟩ :=
        hround n (by lia) input wsn (out ++ acc) acc hPn
      have := hq.time_roundPath_le i
      refine ⟨wsn', acc ++ e, hPn', p.smash (hq.roundPath i) (by simp [hlast]), by simp [hhead],
        by simp [hne, List.append_assoc], ?_, hwin.smash (hq.inWindow_roundPath i hqspace)⟩
      simp only [RunPath.time, RelSeries.smash_length] at htime hqtime this ⊢
      lia
  -- the last round halts the loop
  obtain ⟨wsr, acc, hPr, p, hhead, hlast, htime, hwin⟩ := hrec rounds le_rfl
  obtain ⟨ws', e, q, hq, hR, hempty, hqtime, hqspace⟩ := hstop input wsr (out ++ acc) acc hPr
  have := hq.time_roundPath_le i
  refine ⟨ws', acc ++ e, p.smash (hq.roundPath i) (by simp [hlast]),
    ⟨by simp [hhead]; rfl, by simp [hempty, List.append_assoc]⟩, hR, ?_,
    (hwin.smash (hq.inWindow_roundPath i hqspace)).space_le.trans (by lia)⟩
  simp only [RunPath.time, RelSeries.smash_length] at htime hqtime this ⊢
  lia

end Turing.MultiTapeTM

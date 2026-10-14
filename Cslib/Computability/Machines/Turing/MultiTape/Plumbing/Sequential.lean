/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-!
# Sequential composition of machines on shared tapes

`seq tm₀ tm₁` behaves like `tm₀` until `tm₀` would halt, at which point it continues as `tm₁`,
started in its initial state on the tapes as `tm₀` left them. The state space is
`State₀ ⊕ State₁`, and the *halting transition* of the first phase is mapped to the initial state
of the second, so the handoff costs no extra step.

On run paths this is `TransformsTapes.seqPath`: a run of `tm₀` and a run of `tm₁` on the words it
leaves give a run of `seq`, the running steps of the first followed by those of the second, with the
time and space of the two runs adding. The first run ends halted in a full `wordsCfg`, which is
exactly a starting configuration for the second.

## Main results

* `Turing.MultiTapeTM.seq`: the composed machine.
* `Turing.MultiTapeNTM.RunPath.TransformsTapes.seq`: runs transforming tapes compose.
* `Turing.MultiTapeNTM.RunPath.TransformsTapes.space_seqPath_le`: the space of the two runs adds.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State₀ State₁ : Type*} {input : List Symbol}

/-- The sequential composition of `tm₀` and `tm₁`: it behaves like `tm₀` until `tm₀` would halt,
at which point it switches to the initial state of `tm₁` and behaves like `tm₁`. The switch is
folded into the halting transition of `tm₀`, so it costs no step. -/
noncomputable def seq (tm₀ : MultiTapeTM k Symbol State₀) (tm₁ : MultiTapeTM k Symbol State₁) :
    MultiTapeTM k Symbol (State₀ ⊕ State₁) :=
  ofTr (.inl tm₀.q₀) fun q inp work =>
    match q with
    | .inl q₀ =>
      let a := tm₀.tr q₀ inp work
      { a with state := some (a.state.elim (.inr tm₁.q₀) .inl) }
    | .inr q₁ =>
      let a := tm₁.tr q₁ inp work
      { a with state := a.state.map .inr }

variable {tm₀ : MultiTapeTM k Symbol State₀} {tm₁ : MultiTapeTM k Symbol State₁}

namespace Sequential

/-- A configuration of the first phase: a configuration of `tm₀`, with a halted state mapped to
the initial state of the second phase. Under this map, the whole first phase of `seq` mirrors the
run of `tm₀`, *including* its halting step. -/
def leftCfg (tm₁ : MultiTapeTM k Symbol State₁) (cfg : Cfg k Symbol State₀ input) :
    Cfg k Symbol (State₀ ⊕ State₁) input :=
  cfg.mapState (fun st => some (st.elim (.inr tm₁.q₀) .inl))

/-- A configuration of the second phase. Under this map, the second phase of `seq` mirrors the
run of `tm₁`. -/
def rightCfg (cfg : Cfg k Symbol State₁ input) :
    Cfg k Symbol (State₀ ⊕ State₁) input :=
  cfg.mapState (Option.map .inr)

lemma step_leftCfg (cfg : Cfg k Symbol State₀ input) (h : cfg.state ≠ none) :
    (tm₀.seq tm₁).step (leftCfg tm₁ cfg) = leftCfg tm₁ (tm₀.step cfg) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp h
  have h1 : (leftCfg tm₁ cfg).state = some (Sum.inl q : State₀ ⊕ State₁) := by
    simp [leftCfg, Cfg.mapState, hq]
  rw [step_of_state h1, step_of_state hq]
  simp only [seq, tr_ofTr]
  rfl

lemma step_rightCfg (cfg : Cfg k Symbol State₁ input) :
    (tm₀.seq tm₁).step (rightCfg cfg) = rightCfg (tm₁.step cfg) := by
  cases hq : cfg.state with
  | none =>
    have h1 : (rightCfg (State₀ := State₀) cfg).state = none := by simp [rightCfg, Cfg.mapState, hq]
    rw [step_of_halt h1, step_of_halt hq]
  | some q =>
    have h1 : (rightCfg (State₀ := State₀) cfg).state = some (Sum.inr q : State₀ ⊕ State₁) := by
      simp [rightCfg, hq]
    rw [step_of_state h1, step_of_state hq]
    simp only [seq, tr_ofTr]
    rfl

@[simp]
lemma forgetState_leftCfg (cfg : Cfg k Symbol State₀ input) :
    (leftCfg tm₁ cfg).forgetState = cfg.forgetState := rfl

@[simp]
lemma forgetState_rightCfg (cfg : Cfg k Symbol State₁ input) :
    (rightCfg (State₀ := State₀) cfg).forgetState = cfg.forgetState := rfl

/-- A halted configuration of the first phase is the start of the second phase. -/
lemma leftCfg_of_halt {cfg : Cfg k Symbol State₀ input} (h : cfg.state = none) :
    leftCfg tm₁ cfg = rightCfg (cfg.withState (some tm₁.q₀)) := by
  simp [leftCfg, rightCfg, Cfg.withState, Cfg.mapState, h]

end Sequential

end Turing.MultiTapeTM

namespace Turing.MultiTapeNTM.RunPath

open MultiTapeTM MultiTapeTM.Sequential

variable {k : ℕ} {Symbol State₀ State₁ : Type*} {input : List Symbol}
  {tm₀ : MultiTapeTM k Symbol State₀} {tm₁ : MultiTapeTM k Symbol State₁}
  {p₀ : tm₀.RunPath input} {p₁ : tm₁.RunPath input}

/-- The run of `seq` made of a run of `tm₀` to a halted configuration and a run of `tm₁` from
there: the running steps of the first, then the second. -/
noncomputable def seqPath (p₀ : tm₀.RunPath input) (p₁ : tm₁.RunPath input) (h₀ : p₀.last.Halted)
    (h : p₁.head = p₀.last.withState (some tm₁.q₀)) : (tm₀.seq tm₁).RunPath input :=
  ((p₀.untilHalt h₀).map (runningStepHom (leftCfg tm₁) step_leftCfg)).smash
    (p₁.map (stepHom rightCfg fun c => (step_rightCfg c).symm))
    (by simp [h, leftCfg_of_halt h₀, stepHom])

variable {h₀ : p₀.last.Halted} {h : p₁.head = p₀.last.withState (some tm₁.q₀)}

@[simp]
lemma head_seqPath : (p₀.seqPath p₁ h₀ h).head = leftCfg tm₁ p₀.head := by
  simp [seqPath]

@[simp]
lemma last_seqPath : (p₀.seqPath p₁ h₀ h).last = rightCfg p₁.last := by
  simp [seqPath, stepHom]

/-- The run of `seq` takes at most the steps of the two runs. -/
lemma time_seqPath_le : (p₀.seqPath p₁ h₀ h).time ≤ p₀.time + p₁.time :=
  Nat.add_le_add_right (length_untilHalt_le (h := h₀)) _

/-- Each configuration of the run of `seq` is one of the two runs, up to its state. -/
lemma mem_seqPath {c : Cfg k Symbol (State₀ ⊕ State₁) input} (hc : c ∈ p₀.seqPath p₁ h₀ h) :
    (∃ c₀ ∈ p₀, c.forgetState = c₀.forgetState) ∨ ∃ c₁ ∈ p₁, c.forgetState = c₁.forgetState := by
  rcases RelSeries.mem_or_mem_of_mem_smash hc with hc | hc <;>
    obtain ⟨c', hc', rfl⟩ := RelSeries.exists_of_mem_map hc
  · exact .inl ⟨c', mem_of_mem_untilHalt hc', rfl⟩
  · exact .inr ⟨c', hc', rfl⟩

/-- The run of `seq` visits at most the cells of the two runs. -/
lemma space_seqPath_le : (p₀.seqPath p₁ h₀ h).space ≤ p₀.space + p₁.space := by
  refine ((p₀.seqPath p₁ h₀ h).space_le_sum_card
    (S := fun i => p₀.visitedByTapeHead i ∪ p₁.visitedByTapeHead i) fun c hc i => ?_).trans
    ((Finset.sum_le_sum fun i _ => Finset.card_union_le _ _).trans_eq Finset.sum_add_distrib)
  rcases mem_seqPath hc with ⟨_, ⟨n, rfl⟩, he⟩ | ⟨_, ⟨n, rfl⟩, he⟩ <;>
    rw [show c.workTapePos i = _ from congrArg (·.workTapePos i) he]
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ n))
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ n))

section TransformsTapes

variable {ws ws' ws'' : Fin k → List Symbol} {out e₀ e₁ : List Symbol}

/-- A run on the words another run leaves starts where that run halted, restarted. -/
lemma TransformsTapes.head_eq_withState (h₀ : p₀.TransformsTapes ws ws' out e₀)
    (h₁ : p₁.TransformsTapes ws' ws'' (out ++ e₀) e₁) :
    p₁.head = p₀.last.withState (some tm₁.q₀) := by
  rw [h₁.head_eq, h₀.last_eq]
  rfl

/-- **Sequential composition.** Runs transforming tapes one after the other give a run of `seq`
transforming them in turn, the emitted words concatenating. -/
theorem TransformsTapes.seq (h₀ : p₀.TransformsTapes ws ws' out e₀)
    (h₁ : p₁.TransformsTapes ws' ws'' (out ++ e₀) e₁) :
    (p₀.seqPath p₁ h₀.halted (h₀.head_eq_withState h₁)).TransformsTapes ws ws'' out (e₀ ++ e₁) :=
  ⟨by simp [h₀.head_eq, leftCfg]; rfl, by simp [h₁.last_eq, rightCfg]⟩

end TransformsTapes

end Turing.MultiTapeNTM.RunPath

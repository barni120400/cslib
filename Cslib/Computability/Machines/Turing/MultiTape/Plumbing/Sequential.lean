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

At the specification level this is `transformsTapes_seq`: transformations compose, with the time
and space bounds adding. The postcondition of `TransformsTapes` is what makes the proof direct:
the first machine halts in a full `wordsCfg`, which is exactly a starting configuration for the
second.

## Main results

* `Turing.MultiTapeTM.seq`: the composed machine.
* `Turing.MultiTapeTM.exists_runPath_seq`: run paths compose, and the composed path visits only
  cells that the two paths visit.
* `Turing.MultiTapeTM.RunsWithin.seq`: runs between arbitrary configurations compose, bounds
  adding.
* `Turing.MultiTapeTM.transformsTapes_seq`: transformations compose, bounds adding.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State₀ State₁ : Type*} {input : List Symbol}

/-- The sequential composition of `tm₀` and `tm₁`: it behaves like `tm₀` until `tm₀` would halt,
at which point it switches to the initial state of `tm₁` and behaves like `tm₁`. The switch is
folded into the halting transition of `tm₀`, so it costs no step. -/
noncomputable abbrev seq (tm₀ : MultiTapeTM k Symbol State₀) (tm₁ : MultiTapeTM k Symbol State₁) :
    MultiTapeTM k Symbol (State₀ ⊕ State₁) :=
  combine tm₀ tm₁ (handOver tm₁.q₀) (Option.map .inr) (.inl tm₀.q₀)

variable {tm₀ : MultiTapeTM k Symbol State₀} {tm₁ : MultiTapeTM k Symbol State₁}

/-- **Sequential composition of runs.** A run path of `tm₀` to a halted configuration and a run path
of `tm₁` started where `tm₀` halted combine into a run path of `seq`: the first path up to its first
halted configuration, followed by the second. It takes at most as many steps as the two paths
together, and visits only cells that they visit. -/
theorem exists_runPath_seq {p₀ : tm₀.RunPath input} (h₀ : p₀.last.Halted)
    {p₁ : tm₁.RunPath input} (h₁ : p₁.head = p₀.last.withState (some tm₁.q₀)) :
    ∃ p : (tm₀.seq tm₁).RunPath input, p.head = p₀.head.mapState (handOver tm₁.q₀) ∧
      p.last = p₁.last.mapState (Option.map .inr) ∧ p.length ≤ p₀.length + p₁.length ∧
      ∀ i, p.visitedByTapeHead i ⊆ p₀.visitedByTapeHead i ∪ p₁.visitedByTapeHead i := by
  -- `seq` takes the running steps of `tm₀`, then the steps of `tm₁`
  obtain ⟨q₀, hh₀, hl₀, hlen₀, hmem₀⟩ := p₀.exists_running h₀
  refine ⟨(q₀.map (combineLeftHom (handOver_some _))).smash (p₁.map combineRightHom)
    (by simp [hl₀, h₁, Cfg.mapState, Cfg.withState, show p₀.last.state = none from h₀]),
    by simp [hh₀], by simp, by simp; lia,
    fun i z hz => ?_⟩
  obtain ⟨c, hc, rfl⟩ := (MultiTapeNTM.RunPath.mem_visitedByTapeHead _).mp hz
  rcases RelSeries.mem_or_mem_of_mem_smash hc with hc | hc <;>
    obtain ⟨c', hc', rfl⟩ := RelSeries.exists_of_mem_map hc
  · exact Finset.mem_union_left _ (p₀.mem_visitedByTapeHead.mpr ⟨c', hmem₀ c' hc', rfl⟩)
  · exact Finset.mem_union_right _ (p₁.mem_visitedByTapeHead.mpr ⟨c', hc', rfl⟩)

/-- `tm` runs from `c` to `c'` in at most `t` steps, the head of each work tape `i` staying within
`S i`. Unlike `TransformsTapes`, the configurations need not hold words. -/
def RunsWithin {k : ℕ} {State : Type*} (tm : MultiTapeTM k Symbol State)
    (c c' : Cfg k Symbol State input) (t : ℕ) (S : Fin k → Finset ℤ) : Prop :=
  ∃ p : tm.RunPath input, p.head = c ∧ p.last = c' ∧ p.length ≤ t ∧
    ∀ c ∈ p, ∀ i, c.workTapePos i ∈ S i

/-- A run within some cells is a run within more. -/
theorem RunsWithin.mono {c c' : Cfg k Symbol State₀ input} {t : ℕ} {S S' : Fin k → Finset ℤ}
    (h : tm₀.RunsWithin c c' t S) (hS : ∀ i, S i ⊆ S' i) : tm₀.RunsWithin c c' t S' :=
  let ⟨p, hh, hl, ht, hp⟩ := h
  ⟨p, hh, hl, ht, fun c hc i => hS i (hp c hc i)⟩

/-- **Sequential composition of runs.** A run of `tm₀` to a halted configuration, followed by a run
of `tm₁` from there, is a run of `seq`, the times adding. -/
theorem RunsWithin.seq {c c' : Cfg k Symbol State₀ input} {c'' : Cfg k Symbol State₁ input}
    {t₀ t₁ : ℕ} {S : Fin k → Finset ℤ} (h₀ : tm₀.RunsWithin c c' t₀ S) (hc' : c'.Halted)
    (h₁ : tm₁.RunsWithin (c'.withState (some tm₁.q₀)) c'' t₁ S) :
    (tm₀.seq tm₁).RunsWithin (c.mapState (handOver tm₁.q₀)) (c''.mapState (Option.map .inr))
      (t₀ + t₁) S := by
  obtain ⟨p₀, rfl, rfl, ht₀, hS₀⟩ := h₀
  obtain ⟨p₁, hh₁, rfl, ht₁, hS₁⟩ := h₁
  obtain ⟨p, hh, hl, ht, hv⟩ := exists_runPath_seq hc' hh₁
  refine ⟨p, hh, hl, ht.trans (add_le_add ht₀ ht₁), fun c hc i => ?_⟩
  rcases Finset.mem_union.mp (hv i (p.mem_visitedByTapeHead.mpr ⟨c, hc, rfl⟩)) with h | h <;>
    obtain ⟨c', hc', h⟩ := MultiTapeNTM.RunPath.mem_visitedByTapeHead _ |>.mp h <;> rw [← h]
  exacts [hS₀ c' hc' i, hS₁ c' hc' i]

/-- **Sequential composition of transformations.** If the postcondition of the first
transformation implies the precondition of the second, the composed machine performs the two
transformations one after the other, with the time and space bounds adding and the emitted words
concatenating. -/
theorem transformsTapes_seq
    {P₀ P₁ : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q₀ Q₁ : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop}
    {t₀ s₀ t₁ s₁ : ℕ}
    (h₀ : TransformsTapes tm₀ P₀ Q₀ t₀ s₀) (h₁ : TransformsTapes tm₁ P₁ Q₁ t₁ s₁)
    (hmid : ∀ input ws ws' e, P₀ input ws → Q₀ input ws ws' e → P₁ input ws') :
    TransformsTapes (tm₀.seq tm₁) P₀
      (fun input ws ws'' e => ∃ ws' e₀ e₁, Q₀ input ws ws' e₀ ∧ Q₁ input ws' ws'' e₁ ∧
        e = e₀ ++ e₁)
      (t₀ + t₁) (s₀ + s₁) := by
  intro input ws out hP₀
  obtain ⟨ws', e₀, hQ₀, p₀, hh₀, hl₀, ht₀, hs₀⟩ := h₀ input ws out hP₀
  obtain ⟨ws'', e₁, hQ₁, p₁, hh₁, hl₁, ht₁, hs₁⟩ :=
    h₁ input ws' (out ++ e₀) (hmid input ws ws' e₀ hP₀ hQ₀)
  obtain ⟨p, hh, hl, ht, hvisited⟩ := exists_runPath_seq (p₀ := p₀) (p₁ := p₁)
    (by rw [hl₀]; rfl) (by simp [hh₁, hl₀])
  -- the composed run visits only cells that one of the two runs visits
  exact ⟨ws'', e₀ ++ e₁, ⟨ws', e₀, e₁, hQ₀, hQ₁, rfl⟩, p, by simp [hh, hh₀]; rfl,
    by simp [hl, hl₁], ht.trans (Nat.add_le_add ht₀ ht₁),
    ((Finset.sum_le_sum fun i _ => (Finset.card_le_card (hvisited i)).trans
      (Finset.card_union_le _ _)).trans_eq Finset.sum_add_distrib).trans (Nat.add_le_add hs₀ hs₁)⟩

end Turing.MultiTapeTM

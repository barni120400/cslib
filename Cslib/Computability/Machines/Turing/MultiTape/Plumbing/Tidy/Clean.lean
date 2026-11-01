/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Finite.Sum
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindInput
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sweep
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Defs

/-!
# Every computation can be made tidy

`tidy tm origin mark` runs `tm` and then clears its work tapes and returns every head to its start,
so it computes tidily whatever `tm` computes. Each work tape of `tm` gets a helper tape, and the two
form a pair in the sense of `Turing.MultiTapeTM.sweep`. The machine first writes `origin` on every
helper. It then runs `tm` on the work tapes while marking, on the helper of each tape, every cell
its head stands on (`track`). A head moves at most one cell per step, so the marked cells form an
interval around the origin, and the work tape is blank outside of it. The work tape alone cannot
tell where its contents end, since `tm` may leave blanks inside them, and a single mark cannot tell
where the origin is, hence the two symbols.

Cleaning then takes five sweeps: mark the cell under each head (the head may stand just outside
the interval), walk right to the end of the marks, walk left erasing the work tape and the marks,
and walk right to the origin, erasing it. Last, `Turing.MultiTapeTM.rewindInput` returns the input
head.

## Main definitions

* `Turing.MultiTapeTM.track`: `tm`, marking the cells its heads visit on helper tapes.
* `Turing.MultiTapeTM.tidy`: `tm`, followed by cleaning its tapes.

## Main results

* `Turing.MultiTapeTM.ComputesInTimeAndSpace.computesTidily_tidy`: a computation in time `t` and
  space `s` is a tidy computation of `tidy` in time `2 * t + 3 * s + 7` and space `6 * s`.
* `Turing.MultiTapeTM.ComputableInTimeAndSpace.computableTidilyInTimeAndSpace`: a computable
  function is computable tidily within these bounds.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- `tm` on the work tapes `Fin.castAdd k i`, writing `mark` on the helper tape `Fin.natAdd k i`
under head `i` at every step, unless the helper cell already holds a symbol. The helper heads move
with the work heads. -/
@[expose] public noncomputable def track (tm : MultiTapeTM k Symbol State) (mark : Symbol) :
    MultiTapeTM (k + k) Symbol State :=
  tm.adapt
    { read := fun heads => ⟨heads.inputSymbol, heads.workTapeSymbols ∘ Fin.castAdd k⟩
      action := fun heads a => { a with workTapes := Fin.append a.workTapes fun i =>
        (some (some ((heads.workTapeSymbols (Fin.natAdd k i)).getD mark)), (a.workTapes i).2) } }

/-- **Tidying a machine.** Write `origin` on every helper, run `tm` marking the visited cells
(`track`), mark the cells under the heads, walk right to the ends of the marks, walk left erasing
the work tapes and the marks, walk right to the origin and erase it, and rewind the input head. -/
@[expose] public noncomputable def tidy [DecidableEq Symbol] (tm : MultiTapeTM k Symbol State)
    (origin mark : Symbol) :=
  ((((((sweep (fun _ => false) id id 1 (fun _ => some origin) 0).seq (track tm mark)).seq
    (sweep (fun _ => false) id id 1 (fun h => some (h.getD mark)) 0)).seq
    (sweep Option.isSome id id 1 id (-1))).seq
    (sweep Option.isSome (fun _ => none) (fun h => if h = some origin then h else none) (-1) id
      0)).seq
    (sweep Option.isNone id id 1 (fun _ => none) 0)).seq
    ((rewindInput Symbol).extendTapes (noTapes (k + k)))

namespace Tidy

variable {origin mark : Symbol}

/-- A helper tape marking `[l, r]`: `origin` at `0` and `mark` on the other cells. -/
def helperTape (origin mark : Symbol) (l r z : ℤ) : Option Symbol :=
  if l ≤ z ∧ z ≤ r then some (if z = 0 then origin else mark) else none

lemma helperTape_zero :
    Function.update (fun _ => none) 0 (some origin) = helperTape origin mark 0 0 := by
  funext z
  grind [helperTape, Function.update_apply]

/-- Marking a cell next to or within a marked interval around `0` extends the interval to it. -/
lemma helperTape_update {l r x : ℤ} (hl : l ≤ 0) (hr : 0 ≤ r) (hx : l - 1 ≤ x ∧ x ≤ r + 1) :
    Function.update (helperTape origin mark l r) x
        (some ((helperTape origin mark l r x).getD mark)) =
      helperTape origin mark (min l x) (max r x) := by
  funext z
  grind [helperTape, Function.update_apply]

variable (origin mark) in
/-- `C` is `c` with marks on `[l i, r i]` around the origin, which lie in `V i`, contain the
nonblank cells of work tape `i` and reach to the cells next to head `i`. -/
def Tracks (V : Fin k → Finset ℤ) (c : Cfg k Symbol State input)
    (C : Cfg (k + k) Symbol State input) : Prop :=
  ∃ l r : Fin k → ℤ, C = pairCfg c.state c.inputPos c.workTapes
      (fun i => helperTape origin mark (l i) (r i)) c.workTapePos c.output ∧
    ∀ i, l i ≤ 0 ∧ 0 ≤ r i ∧ l i - 1 ≤ c.workTapePos i ∧ c.workTapePos i ≤ r i + 1 ∧
      Finset.Icc (l i) (r i) ⊆ V i ∧ ∀ z, c.workTapes i z ≠ none → l i ≤ z ∧ z ≤ r i

/-- **Tracking a run.** A run of `tm` to a halted configuration lifts to a run of `track tm mark`
of at most the same length within the cells the run of `tm` visits, ending in a configuration that
tracks its end. -/
lemma runsWithin_track {tm : MultiTapeTM k Symbol State} (p : tm.RunPath input)
    (hp : p.last.Halted) {C : Cfg (k + k) Symbol State input}
    (hC : Tracks origin mark p.visitedByTapeHead p.head C) :
    ∃ C', (track tm mark).RunsWithin C C' p.length
      (Fin.append p.visitedByTapeHead p.visitedByTapeHead) ∧
      Tracks origin mark p.visitedByTapeHead p.last C' := by
  -- a running step of `tm` is a step of `track tm mark`, which marks the cell it leaves
  have hR {c c' : Cfg k Symbol State input} {C : Cfg (k + k) Symbol State input}
      (hstep : (c, c') ∈ tm.runningStepRel input)
      (hc : ∀ i, c.workTapePos i ∈ p.visitedByTapeHead i)
      (hC : Tracks origin mark p.visitedByTapeHead c C) :
      ∃ C', (C, C') ∈ (track tm mark).stepRel input ∧
        Tracks origin mark p.visitedByTapeHead c' C' := by
    obtain ⟨l, r, rfl, hinv⟩ := hC
    obtain ⟨hrun, hs⟩ := hstep
    refine ⟨_, follows_adapt.step hs Option.map_id_apply (absurd · hrun) ?_ fun a ha => ?_,
      fun i => min (l i) (c.workTapePos i), fun i => max (r i) (c.workTapePos i), rfl, fun i => ?_⟩
    · exact HeadSymbols.ext rfl (funext fun i => by simp [Cfg.workTapeSymbols, pairCfg])
    · subst ha
      refine Cfg.ext rfl rfl (funext fun j => ?_) (funext fun j => ?_) rfl <;>
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
        simp [Action.apply, pairCfg, Cfg.workTapeSymbols,
          helperTape_update (hinv i).1 (hinv i).2.1 ⟨(hinv i).2.2.1, (hinv i).2.2.2.1⟩]
    · have := abs_le.mp (MultiTapeNTM.Step.workTapePos_le hs i)
      have := hinv i; have := hc i
      have := fun z (hz : z ≠ c.workTapePos i) => MultiTapeNTM.Step.workTapes_eq_of_ne hs hz
      grind
  obtain ⟨q, hqh, hql, hqlen, hqmem⟩ := p.exists_running hp
  have hV {c} (hc : c ∈ q) i : c.workTapePos i ∈ p.visitedByTapeHead i :=
    p.mem_visitedByTapeHead.2 ⟨c, hqmem c hc, rfl⟩
  obtain ⟨P, hPh, hPlen, hPlast, hPmem⟩ := RelSeries.exists_lift _ _ hR q (fun _ => hV) (hqh ▸ hC)
  refine ⟨_, ⟨P, hPh, rfl, hPlen.trans_le hqlen, fun D hD j => ?_⟩, hql ▸ hPlast⟩
  obtain ⟨c, hc, -, -, rfl, -⟩ := hPmem D hD
  exact Fin.addCases (fun i => by simpa using hV hc i) (fun i => by simpa using hV hc i) j

/-- Blank word tapes, as pairs of tapes. -/
lemma wordsCfg_eq_pairCfg (q : Option State) (out : List Symbol) :
    wordsCfg input q (fun _ : Fin (k + k) => []) out =
      pairCfg q 1 (fun _ _ => none) (fun _ _ => none) (fun _ => 0) out := by
  refine Cfg.ext rfl rfl (funext fun j => ?_) (funext fun j => ?_) rfl <;>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [pairCfg, wordsCfg]

variable {ip : Fin (input.length + 2)} {W : Fin k → ℤ → Option Symbol} {out : List Symbol}
  {S : Fin k → Finset ℤ} {l r : Fin k → ℤ} {n : ℕ}

/-- Rewinding the input head leaves the pairs of tapes alone. -/
lemma rewind_runsWithin (H : Fin k → ℤ → Option Symbol) {x : Fin k → ℤ} (hS : ∀ i, x i ∈ S i) :
    ((rewindInput Symbol).extendTapes (noTapes (k + k))).RunsWithin
      (pairCfg (some (rewindInput Symbol).q₀) ip W H x out) (pairCfg none 1 W H x out)
      (ip.val - 1 + 2) (Fin.append S S) := by
  have h : (rewindInput Symbol).RunsWithin ⟨some (rewindInput Symbol).q₀, ip, nofun, nofun, out⟩
      ⟨none, 1, nofun, nofun, out⟩ (ip.val - 1 + 2) (fun _ => ∅) :=
    ⟨.ofDeterministic _ _ (ip.val - 1 + 2), rfl, runFrom_rewindInput ip nofun nofun out, le_rfl,
      fun _ _ i => i.elim0⟩
  have := h.map (S' := Fin.append S S) (embedHom _ (noTapes (k + k)) (Fin.append W H)
      (Fin.append x x)) fun d _ l => by
    rw [embedHom_apply, embed_noTapes]
    exact Fin.addCases (by simpa using hS ·) (by simpa using hS ·) l
  rwa [embedHom_apply, embedHom_apply, embed_noTapes, embed_noTapes] at this

/-- A sweep in which no pair walks rewrites the helper cell under each head by `g`, in one step. -/
lemma mark_runsWithin (g : Option Symbol → Option Symbol) {H H' : Fin k → ℤ → Option Symbol}
    {x : Fin k → ℤ} (hH : ∀ i, Function.update (H i) (x i) (g (H i (x i))) = H' i)
    (hS : ∀ i, x i ∈ S i) :
    (sweep (fun _ => false) id id 1 g 0).RunsWithin (pairCfg (some ()) ip W H x out)
      (pairCfg none ip W H' x out) (0 + 1) (Fin.append S S) :=
  sweep_runsWithin one_ne_zero 0 (fun _ => le_rfl) (by simp) (fun _ => rfl) (fun _ => walked_zero)
    (by simpa using hH) (by simp) (by simpa using hS) hS

/-- Proves a walk over marked intervals by `sweep_runsWithin` with `m i` steps on pair `i`, from
the bounds `h` and the cells `hS`. -/
local macro "sweep_tac " m:term:max h:ident hS:ident : tactic => `(tactic|
  (refine sweep_runsWithin (by decide) $m ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intro i <;> have := $h i <;>
    intros <;> (try funext z) <;> (try refine $hS i ?_) <;> (try simp only [walked_id]) <;>
    grind [walked, helperTape, Function.update_apply, SignType.coe_zero, SignType.coe_one,
      SignType.coe_neg_one]))

/-- Walking right from heads within the marked intervals to their right ends. -/
lemma right_runsWithin {x : Fin k → ℤ} (h : ∀ i, l i ≤ x i ∧ x i ≤ r i ∧ r i - l i + 1 ≤ n)
    (hS : ∀ i, Finset.Icc (l i - 1) (r i + 1) ⊆ S i) :
    (sweep Option.isSome id id 1 id (-1)).RunsWithin
      (pairCfg (some ()) ip W (fun i => helperTape origin mark (l i) (r i)) x out)
      (pairCfg none ip W (fun i => helperTape origin mark (l i) (r i)) r out) (n + 1)
      (Fin.append S S) := by
  sweep_tac (fun i => (r i - x i + 1).toNat) h hS

/-- Walking right from left of the marked intervals to the origin, and erasing it. -/
lemma home_runsWithin (h : ∀ i, l i ≤ 0 ∧ 0 ≤ r i ∧ r i - l i + 1 ≤ n)
    (hS : ∀ i, Finset.Icc (l i - 1) (r i + 1) ⊆ S i) :
    (sweep Option.isNone id id 1 (fun _ => none) 0).RunsWithin
      (pairCfg (some ()) ip (fun _ _ => none) (fun _ => helperTape origin mark 0 0)
        (fun i => l i - 1) out)
      (pairCfg none ip (fun _ _ => none) (fun _ _ => none) (fun _ => 0) out) (n + 1)
      (Fin.append S S) := by
  sweep_tac (fun i => (1 - l i).toNat) h hS

variable [DecidableEq Symbol]

/-- Walking left from the right ends of the marked intervals past their left ends, erasing the
work tapes and every mark but the origin. -/
lemma erase_runsWithin (hom : origin ≠ mark) (h : ∀ i, l i ≤ 0 ∧ 0 ≤ r i ∧ r i - l i + 1 ≤ n)
    (hW : ∀ i z, W i z ≠ none → l i ≤ z ∧ z ≤ r i)
    (hS : ∀ i, Finset.Icc (l i - 1) (r i + 1) ⊆ S i) :
    (sweep Option.isSome (fun _ => none) (fun h => if h = some origin then h else none) (-1) id
      0).RunsWithin
      (pairCfg (some ()) ip W (fun i => helperTape origin mark (l i) (r i)) r out)
      (pairCfg none ip (fun _ _ => none) (fun _ => helperTape origin mark 0 0) (fun i => l i - 1)
        out) (n + 1) (Fin.append S S) := by
  sweep_tac (fun i => (r i - l i + 1).toNat) h hS

end Tidy

open Tidy in
/-- **Every computation can be made tidy.** If `tm` computes `output` from `input` in time `t` and
space `s`, then `tidy tm origin mark` computes it tidily in time `2 * t + 3 * s + 7` and space
`6 * s`. The marked interval of each tape lies within the cells `tm` visits, so the three walks
take at most `s + 1` steps each, and each pair of tapes visits at most two cells more than the
tape of `tm`; the input head is rewound in at most `t + 2` steps. -/
public theorem ComputesInTimeAndSpace.computesTidily_tidy [DecidableEq Symbol]
    {tm : MultiTapeTM k Symbol State} {origin mark : Symbol} (hom : origin ≠ mark)
    {output : List Symbol} {t s : ℕ} (h : tm.ComputesInTimeAndSpace input output t s) :
    (tidy tm origin mark).ComputesTidilyInTimeAndSpace input output (2 * t + 3 * s + 7)
      (6 * s) := by
  obtain ⟨c₀, hp, hout, ht, hs⟩ := h.exists_computationPath
  set p : tm.RunPath input := c₀.toRunPath
  have hp0 : p.head = tm.initCfg input := c₀.head_eq
  change p.length ≤ t at ht
  change p.space ≤ s at hs
  have hV0 i : (0 : ℤ) ∈ p.visitedByTapeHead i :=
    p.mem_visitedByTapeHead.2 ⟨_, p.head_mem, by rw [hp0]; rfl⟩
  -- the run of `tm`, tracked: the helpers mark intervals `[l i, r i]` of visited cells
  obtain ⟨_, h₁, l, r, rfl, hinv⟩ := runsWithin_track (origin := origin) (mark := mark) p hp
    (C := pairCfg (some tm.q₀) 1 (fun _ _ => none) (fun _ => helperTape origin mark 0 0)
      (fun _ => 0) []) ⟨0, 0, by rw [hp0]; rfl, fun i => by simp [hp0, hV0]⟩
  rw [show p.last.state = none from hp] at h₁
  set x := p.last.workTapePos
  obtain ⟨L, hL⟩ : ∃ L : Fin k → ℤ, ∀ i, L i = min (l i) (x i) := ⟨_, fun _ => rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : Fin k → ℤ, ∀ i, R i = max (r i) (x i) := ⟨_, fun _ => rfl⟩
  -- marking the cells under the heads extends the intervals to `[L i, R i]`, still visited
  have hIcc i : Finset.Icc (L i) (R i) ⊆ p.visitedByTapeHead i := by
    have := hinv i; have := hL i; have := hR i
    have : x i ∈ p.visitedByTapeHead i := p.mem_visitedByTapeHead.2 ⟨_, p.last_mem, rfl⟩
    grind
  have hw i : L i ≤ 0 ∧ 0 ≤ R i ∧ R i - L i + 1 ≤ s := by
    have := (Finset.card_le_card (hIcc i)).trans
      ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hs)
    rw [Int.card_Icc] at this
    have := hL i; have := hR i; have := hinv i
    omega
  have hx i : L i ≤ x i ∧ x i ≤ R i ∧ R i - L i + 1 ≤ s := by
    have := hL i; have := hR i; have := hw i; omega
  have hmark i : Function.update (helperTape origin mark (l i) (r i)) (x i)
      (some ((helperTape origin mark (l i) (r i) (x i)).getD mark)) =
      helperTape origin mark (L i) (R i) := by
    rw [hL i, hR i]
    exact helperTape_update (hinv i).1 (hinv i).2.1 ⟨(hinv i).2.2.1, (hinv i).2.2.2.1⟩
  -- every head of every phase stays in `S' i`, two cells more than `tm` visits
  set S' : Fin k → Finset ℤ := fun i => insert (L i - 1) (insert (R i + 1) (p.visitedByTapeHead i))
  have hS i : Finset.Icc (L i - 1) (R i + 1) ⊆ S' i := by have := hIcc i; grind
  have hmem i z (hz : L i - 1 ≤ z ∧ z ≤ R i + 1) : z ∈ S' i := hS i (Finset.mem_Icc.mpr hz)
  have hVS i : p.visitedByTapeHead i ⊆ S' i :=
    (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
  obtain ⟨Q, hQh, hQl, hQt, hQS⟩ :=
    ((((((mark_runsWithin (input := input) (ip := 1) (W := fun _ _ => none) (out := [])
      (fun _ => some origin) (fun _ => helperTape_zero)
      fun i => hmem i 0 (by have := hw i; omega)).seq rfl
    (h₁.mono le_rfl (Fin.addCases (by simpa using hVS ·) (by simpa using hVS ·)))).seq rfl
    (mark_runsWithin (fun h => some (h.getD mark)) hmark
      fun i => hmem i (x i) (by have := hx i; omega))).seq rfl
    (right_runsWithin hx hS)).seq rfl
    (erase_runsWithin hom hw (fun i z hz => by
      have := (hinv i).2.2.2.2.2 z hz; have := hL i; have := hR i; omega) hS)).seq rfl
    (home_runsWithin hw hS)).seq rfl
    (rewind_runsWithin (ip := p.last.inputPos) (W := fun _ _ => none) (out := p.last.output)
      (fun _ _ => none) fun i => hmem i 0 (by have := hw i; omega))
  -- the input head moved at most `t` cells
  have hip := p.inputPos_last_le
  simp only [hp0, MultiTapeNTM.initCfg, Cfg.init, Fin.val_one] at hip
  refine computesTidily_iff.mpr ⟨Q, by rw [wordsCfg_eq_pairCfg]; exact hQh,
    by rw [wordsCfg_eq_pairCfg, ← hout]; exact hQl, by change Q.length ≤ _; omega, ?_⟩
  calc Q.space ≤ ∑ j, (Fin.append S' S' j).card := Q.space_le_sum_card hQS
    _ = 2 * ∑ i, (S' i).card := by rw [Fin.sum_univ_add]; simp [two_mul]
    _ ≤ 2 * ∑ i, (p.spaceUsedByTape i + 2) := by
      gcongr with i
      exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ (Finset.card_insert_le _ _))
    _ = 2 * (p.space + 2 * k) := by
      simp [Finset.sum_add_distrib, MultiTapeNTM.RunPath.space, mul_comm]
    _ ≤ 6 * s := by have := p.le_space; omega

/-- **Every computable function is computable tidily**, in time `2 * t + 3 * s + 7` and space
`6 * s`. -/
public theorem ComputableInTimeAndSpace.computableTidilyInTimeAndSpace {α β : Type*} {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t s) :
    ComputableTidilyInTimeAndSpace f encIn encOut (fun a => 2 * t a + 3 * s a + 7)
      (fun a => 6 * s a) :=
  let ⟨k, _, _, tm, htm⟩ := h
  ⟨k + k, _, inferInstance, tidy tm false true,
    fun a => (htm a).computesTidily_tidy Bool.false_ne_true⟩

end Turing.MultiTapeTM

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

/-- A helper tape holding `origin` at `0` and `mark` on the rest of `[l, r]`. -/
def helperTape (origin mark : Symbol) (l r z : ℤ) : Option Symbol :=
  if z = 0 then some origin else if l ≤ z ∧ z ≤ r then some mark else none

lemma helperTape_zero : Function.update (fun _ => none) 0 (some origin) =
    helperTape origin mark 0 0 := by
  funext z
  by_cases hz : z = 0 <;> simp [helperTape, hz]
  omega

/-- Marking a cell next to or within the marked interval extends the interval to it. -/
lemma helperTape_update {l r x : ℤ} (hl : l ≤ 0) (hr : 0 ≤ r) (hx : l - 1 ≤ x ∧ x ≤ r + 1) :
    Function.update (helperTape origin mark l r) x
        (some ((helperTape origin mark l r x).getD mark)) =
      helperTape origin mark (min l x) (max r x) := by
  funext z
  by_cases hz : z = x
  · subst hz
    simp only [Function.update_self, helperTape]
    split_ifs <;> simp_all
  · simp only [Function.update_of_ne hz, helperTape]
    split_ifs <;> simp_all
    omega

lemma helperTape_isSome {l r z : ℤ} (hl : l ≤ 0) (hr : 0 ≤ r) :
    (helperTape origin mark l r z).isSome = decide (l ≤ z ∧ z ≤ r) := by
  unfold helperTape
  split_ifs <;> simp_all

variable (origin mark) in
/-- `C` is the configuration `c` with marks on `[l i, r i]` around the origin, which contains the
nonblank cells of work tape `i` and the cells next to head `i`. -/
def Tracks (c : Cfg k Symbol State input) (C : Cfg (k + k) Symbol State input) : Prop :=
  ∃ l r : Fin k → ℤ, C = pairCfg c.state c.inputPos c.workTapes
      (fun i => helperTape origin mark (l i) (r i)) c.workTapePos c.output ∧
    ∀ i, l i ≤ 0 ∧ 0 ≤ r i ∧ l i - 1 ≤ c.workTapePos i ∧ c.workTapePos i ≤ r i + 1 ∧
      ∀ z, c.workTapes i z ≠ none → l i ≤ z ∧ z ≤ r i

/-- **Tracking a run.** A run of `tm` to a halted configuration lifts to a run of `track tm mark`,
each of whose configurations tracks one of the run of `tm`. -/
lemma exists_runPath_track {tm : MultiTapeTM k Symbol State} (p : tm.RunPath input)
    (hp : p.last.Halted) {C : Cfg (k + k) Symbol State input} (hC : Tracks origin mark p.head C) :
    ∃ P : (track tm mark).RunPath input, P.head = C ∧ P.length ≤ p.length ∧
      Tracks origin mark p.last P.last ∧ ∀ D ∈ P, ∃ c ∈ p, Tracks origin mark c D := by
  -- a running step of `tm` is a step of `track tm mark`, which marks the cell it leaves
  have hR {c c' : Cfg k Symbol State input} {C : Cfg (k + k) Symbol State input}
      (hstep : (c, c') ∈ tm.runningStepRel input) (hC : Tracks origin mark c C) :
      ∃ C', (C, C') ∈ (track tm mark).stepRel input ∧ Tracks origin mark c' C' := by
    obtain ⟨l, r, rfl, hinv⟩ := hC
    obtain ⟨hrun, hs⟩ := hstep
    refine ⟨_, follows_adapt.step hs Option.map_id_apply (absurd · hrun) ?_ fun a ha => ?_,
      fun i => min (l i) (c.workTapePos i), fun i => max (r i) (c.workTapePos i), rfl, fun i => ?_⟩
    · exact HeadSymbols.ext rfl (funext fun i => by
        simp [-Fin.natAdd_eq_addNat, Cfg.workTapeSymbols, pairCfg])
    · subst ha
      refine Cfg.ext rfl rfl (funext fun j => ?_) (funext fun j => ?_) rfl <;>
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
        simp [-Fin.natAdd_eq_addNat, Action.apply, pairCfg, Cfg.workTapeSymbols,
          helperTape_update (hinv i).1 (hinv i).2.1 ⟨(hinv i).2.2.1, (hinv i).2.2.2.1⟩]
    · have hm := abs_le.mp (MultiTapeNTM.Step.workTapePos_le hs i)
      obtain ⟨h1, h2, h3, h4, h5⟩ := hinv i
      dsimp only
      refine ⟨by omega, by omega, by omega, by omega, fun z hz => ?_⟩
      by_cases hzi : z = c.workTapePos i
      · omega
      · have := h5 z (MultiTapeNTM.Step.workTapes_eq_of_ne hs hzi ▸ hz)
        omega
  obtain ⟨q, hqh, hql, hqlen, hqmem⟩ := p.exists_running hp
  obtain ⟨P, hPh, hPlen, hPlast, hPmem⟩ := RelSeries.exists_lift _ hR q (hqh ▸ hC)
  exact ⟨P, hPh, hPlen.trans_le hqlen, hql ▸ hPlast, fun D hD =>
    let ⟨c, hc, hcD⟩ := hPmem D hD; ⟨c, hqmem c hc, hcD⟩⟩

/-- Blank word tapes, as pairs of tapes. -/
lemma wordsCfg_eq_pairCfg (q : Option State) (out : List Symbol) :
    wordsCfg input q (fun _ : Fin (k + k) => []) out =
      pairCfg q 1 (fun _ _ => none) (fun _ _ => none) (fun _ => 0) out := by
  refine Cfg.ext rfl rfl (funext fun j => ?_) (funext fun j => ?_) rfl <;>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp [-Fin.natAdd_eq_addNat, pairCfg, wordsCfg]

variable {ip : Fin (input.length + 2)} {W : Fin k → ℤ → Option Symbol} {out : List Symbol}
  {S : Fin k → Finset ℤ}

/-- Rewinding the input head leaves the pairs of tapes alone. -/
lemma rewind_runsWithin (H : Fin k → ℤ → Option Symbol) {x : Fin k → ℤ} (hS : ∀ i, x i ∈ S i) :
    ((rewindInput Symbol).extendTapes (noTapes (k + k))).RunsWithin
      (pairCfg (some (rewindInput Symbol).q₀) ip W H x out) (pairCfg none 1 W H x out)
      (ip.val - 1 + 2) (Fin.append S S) := by
  have e : noTapesCfg (pairCfg (some (rewindInput Symbol).q₀) ip W H x out) =
      ⟨some (rewindInput Symbol).q₀, ip, nofun, nofun, out⟩ :=
    Cfg.ext rfl rfl (Subsingleton.elim _ _) (Subsingleton.elim _ _) rfl
  refine ⟨.ofDeterministic _ (pairCfg (some (rewindInput Symbol).q₀) ip W H x out)
    (ip.val - 1 + 2), rfl, (runFrom_noTapes _ _ (ip.val - 1 + 2)).trans ?_, le_rfl, ?_⟩
  · rw [e, runFrom_rewindInput]
    rfl
  · rintro _ ⟨n, rfl⟩ j
    change (runFrom _ n.val).workTapePos j ∈ _
    rw [runFrom_noTapes]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simpa [-Fin.natAdd_eq_addNat] using hS i

/-- A sweep in which no pair walks rewrites the helper cell under each head by `g`, in one step. -/
lemma mark_runsWithin (g : Option Symbol → Option Symbol) {H H' : Fin k → ℤ → Option Symbol}
    {x : Fin k → ℤ} (hH : ∀ i, Function.update (H i) (x i) (g (H i (x i))) = H' i)
    (hS : ∀ i, x i ∈ S i) :
    (sweep (fun _ => false) id id 1 g 0).RunsWithin (pairCfg (some ()) ip W H x out)
      (pairCfg none ip W H' x out) 1 (Fin.append S S) := by
  have h := sweep_runsWithin (go := fun _ => false) (fW := id) (fH := id) (d := 1) (gH := g)
    (e := 0) (by decide) ip W H x out (fun _ => 0) (by simp) (by simp)
    (fun i j hj => by simpa [show j = 0 by omega] using hS i) (fun i => by simpa using hS i)
  rw [show Finset.univ.sup (fun _ : Fin k => 0) = 0 from Finset.sup_bot _] at h
  simpa [hH] using h

/-- Walking right from heads within the marked intervals to their right ends. -/
lemma right_runsWithin {l r x : Fin k → ℤ} (hl : ∀ i, l i ≤ 0) (hr : ∀ i, 0 ≤ r i)
    (hx : ∀ i, l i ≤ x i ∧ x i ≤ r i) (hS : ∀ i, Finset.Icc (l i - 1) (r i + 1) ⊆ S i) :
    (sweep Option.isSome id id 1 id (-1)).RunsWithin
      (pairCfg (some ()) ip W (fun i => helperTape origin mark (l i) (r i)) x out)
      (pairCfg none ip W (fun i => helperTape origin mark (l i) (r i)) r out)
      (Finset.univ.sup (fun i => (r i - x i + 1).toNat) + 1) (Fin.append S S) := by
  have h := sweep_runsWithin (go := Option.isSome) (fW := id) (fH := id) (d := 1) (gH := id)
    (e := -1) (by decide) ip W (fun i => helperTape origin mark (l i) (r i)) x out
    (fun i => (r i - x i + 1).toNat)
    (fun i j hj => by simp [helperTape_isSome (hl i) (hr i)]; have := hx i; omega)
    (fun i => by simp [helperTape_isSome (hl i) (hr i)]; have := hx i; omega)
    (fun i j hj => hS i (by simp [SignType.cast]; have := hx i; omega))
    (fun i => hS i (by simp [SignType.cast]; have := hx i; omega))
  convert h using 2 <;> funext i
  · simp
  · simp
  · have := hx i
    simp [SignType.cast]
    omega

/-- Walking right from left of the marked intervals to the origin, and erasing it. -/
lemma home_runsWithin {l r : Fin k → ℤ} (hl : ∀ i, l i ≤ 0) (hr : ∀ i, 0 ≤ r i)
    (hS : ∀ i, Finset.Icc (l i - 1) (r i + 1) ⊆ S i) :
    (sweep Option.isNone id id 1 (fun _ => none) 0).RunsWithin
      (pairCfg (some ()) ip (fun _ _ => none) (fun _ => helperTape origin mark 0 0)
        (fun i => l i - 1) out)
      (pairCfg none ip (fun _ _ => none) (fun _ _ => none) (fun _ => 0) out)
      (Finset.univ.sup (fun i => (1 - l i).toNat) + 1) (Fin.append S S) := by
  have hm : ∀ i, ((1 - l i).toNat : ℤ) = 1 - l i := fun i =>
    Int.toNat_of_nonneg (by have := hl i; omega)
  have h := sweep_runsWithin (go := Option.isNone) (fW := id) (fH := id) (d := 1)
    (gH := fun _ => none) (e := 0) (by decide) ip (fun _ _ => none)
    (fun _ => helperTape origin mark 0 0) (fun i => l i - 1) out (fun i => (1 - l i).toNat)
    (fun i j hj => by
      have := hm i
      simp only [helperTape, SignType.coe_one, one_mul]
      split_ifs <;> first | rfl | omega)
    (fun i => by simp [helperTape, SignType.cast, hm])
    (fun i j hj => hS i (by have := hm i; have := hr i; simp [SignType.cast]; omega))
    (fun i => hS i (by have := hl i; have := hr i; simp [SignType.cast, hm]; omega))
  convert h using 2 <;> funext i
  · simp
  · funext z
    simp only [walked_id, Function.update_apply, helperTape, SignType.cast, hm]
    split_ifs <;> first | rfl | omega
  · simp [SignType.cast, hm]

variable [DecidableEq Symbol]

/-- Walking left from the right ends of the marked intervals past their left ends, erasing the
work tapes and every mark but the origin. -/
lemma erase_runsWithin (hom : origin ≠ mark) {l r : Fin k → ℤ} (hl : ∀ i, l i ≤ 0)
    (hr : ∀ i, 0 ≤ r i) (hW : ∀ i z, W i z ≠ none → l i ≤ z ∧ z ≤ r i)
    (hS : ∀ i, Finset.Icc (l i - 1) (r i + 1) ⊆ S i) :
    (sweep Option.isSome (fun _ => none) (fun h => if h = some origin then h else none) (-1) id
      0).RunsWithin
      (pairCfg (some ()) ip W (fun i => helperTape origin mark (l i) (r i)) r out)
      (pairCfg none ip (fun _ _ => none) (fun _ => helperTape origin mark 0 0) (fun i => l i - 1)
        out)
      (Finset.univ.sup (fun i => (r i - l i + 1).toNat) + 1) (Fin.append S S) := by
  have h := sweep_runsWithin (go := Option.isSome) (fW := fun _ => none)
    (fH := fun h => if h = some origin then h else none) (d := -1) (gH := id) (e := 0)
    (by decide)
    ip W (fun i => helperTape origin mark (l i) (r i)) r out (fun i => (r i - l i + 1).toNat)
    (fun i j hj => by simp [helperTape_isSome (hl i) (hr i), SignType.cast]; have := hr i; omega)
    (fun i => by simp [helperTape_isSome (hl i) (hr i), SignType.cast]; have := hr i; omega)
    (fun i j hj => hS i (by simp [SignType.cast]; have := hr i; have := hl i; omega))
    (fun i => hS i (by simp [SignType.cast]; have := hr i; have := hl i; omega))
  have hm : ∀ i, ((r i - l i + 1).toNat : ℤ) = r i - l i + 1 := fun i =>
    Int.toNat_of_nonneg (by have := hr i; have := hl i; omega)
  convert h using 2 <;> funext i
  · funext z
    simp only [walked, SignType.cast, hm]
    split_ifs with hz
    · rfl
    · by_contra hne
      have := hW i z (Ne.symm hne)
      omega
  · funext z
    have := hl i
    have := hr i
    simp only [walked, SignType.cast, hm, Function.update_apply, helperTape, id]
    split_ifs <;> simp_all [Ne.symm hom] <;> omega
  · simp [SignType.cast, hm]
    omega

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
  -- the run of `tm`, tracked: the helpers mark intervals `[l i, r i]`
  obtain ⟨P, hPh, hPlen, ⟨l, r, hPl, hinv⟩, hPmem⟩ := exists_runPath_track (origin := origin)
    (mark := mark) p hp (C := pairCfg (some tm.q₀) 1 (fun _ _ => none)
      (fun _ => helperTape origin mark 0 0) (fun _ => 0) [])
    ⟨fun _ => 0, fun _ => 0, by rw [hp0]; rfl, fun _ => by simp [hp0]⟩
  set x := p.last.workTapePos
  obtain ⟨L, hL⟩ : ∃ L : Fin k → ℤ, ∀ i, L i = min (l i) (x i) := ⟨_, fun _ => rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : Fin k → ℤ, ∀ i, R i = max (r i) (x i) := ⟨_, fun _ => rfl⟩
  have hPpos : ∀ D ∈ P, ∃ c ∈ p, D.workTapePos = Fin.append c.workTapePos c.workTapePos :=
    fun D hD => let ⟨c, hc, _, _, hcD, _⟩ := hPmem D hD; ⟨c, hc, hcD ▸ rfl⟩
  -- the cells between the ends of the marks were visited by `tm`
  have hIcc : ∀ i, Finset.Icc (L i) (R i) ⊆ p.visitedByTapeHead i := by
    intro i z hz
    rw [Finset.mem_Icc, hL, hR] at hz
    obtain ⟨h1, h2, h3, h4, -⟩ := hinv i
    rw [MultiTapeNTM.RunPath.mem_visitedByTapeHead]
    by_cases hzx : z = x i
    · exact ⟨p.last, RelSeries.last_mem _, hzx.symm⟩
    by_cases hz0 : z = 0
    · exact ⟨p.head, RelSeries.head_mem _, by rw [hz0, hp0]; rfl⟩
    have hlr : l i ≤ z ∧ z ≤ r i := by omega
    obtain ⟨D, hD, hDz⟩ := P.mem_visitedByTapeHead.mp (P.mem_visitedByTapeHead_of_workTapes_ne
      (i := Fin.natAdd k i) (z := z) (by
        rw [hPl, hPh]
        simp [-Fin.natAdd_eq_addNat, helperTape, hz0, hlr]
        omega))
    obtain ⟨c, hc, hcD⟩ := hPpos D hD
    exact ⟨c, hc, by simpa [-Fin.natAdd_eq_addNat, hcD] using hDz⟩
  -- every head of every phase stays in `S' i`, at most two cells more than `tm` visits
  set S' : Fin k → Finset ℤ := fun i => insert (L i - 1) (insert (R i + 1) (p.visitedByTapeHead i))
  have hS : ∀ i, Finset.Icc (L i - 1) (R i + 1) ⊆ S' i := fun i z hz => by
    rw [Finset.mem_Icc] at hz
    rcases (by omega : z = L i - 1 ∨ z = R i + 1 ∨ (L i ≤ z ∧ z ≤ R i)) with rfl | rfl | hz'
    · simp [S']
    · simp [S']
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hIcc i (Finset.mem_Icc.mpr hz')))
  have hmem : ∀ i z, L i - 1 ≤ z → z ≤ R i + 1 → z ∈ S' i := fun i z h1 h2 =>
    hS i (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  have hb : ∀ i, L i ≤ 0 ∧ 0 ≤ R i ∧ L i ≤ x i ∧ x i ≤ R i := fun i => by
    have := hL i; have := hR i; have := hinv i; omega
  have hsi : ∀ i, (R i + 1 - L i).toNat ≤ s := fun i => by
    rw [← Int.card_Icc]
    exact (Finset.card_le_card (hIcc i)).trans
      ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hs)
  -- the seven phases
  have h₀ := mark_runsWithin (input := input) (ip := 1) (W := fun _ _ => none) (out := []) (S := S')
    (fun _ => some origin) (H' := fun _ => helperTape origin mark 0 0) (x := fun _ => 0)
    (fun _ => helperTape_zero) (fun i => hmem i 0 (by have := hb i; omega) (by have := hb i; omega))
  have h₁ : (track tm mark).RunsWithin _
      (pairCfg none p.last.inputPos p.last.workTapes (fun i => helperTape origin mark (l i) (r i))
        x p.last.output) t (Fin.append S' S') := ⟨P, hPh, by rw [hPl, show p.last.state = none
      from hp], hPlen.trans ht, fun D hD j => by
    obtain ⟨c, hc, hcD⟩ := hPpos D hD
    have hc' : ∀ i, c.workTapePos i ∈ S' i := fun i => Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (p.mem_visitedByTapeHead.mpr ⟨c, hc, rfl⟩))
    rw [hcD]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simpa [-Fin.natAdd_eq_addNat] using hc' i⟩
  have h₂ := mark_runsWithin (ip := p.last.inputPos) (W := p.last.workTapes)
    (out := p.last.output) (S := S') (fun h => some (h.getD mark))
    (H' := fun i => helperTape origin mark (L i) (R i)) (fun i => by
      rw [hL, hR]
      exact helperTape_update (hinv i).1 (hinv i).2.1 ⟨(hinv i).2.2.1, (hinv i).2.2.2.1⟩)
    (fun i => hmem i (x i) (by have := hb i; omega) (by have := hb i; omega))
  have h₃ := right_runsWithin (origin := origin) (mark := mark) (ip := p.last.inputPos)
    (W := p.last.workTapes) (out := p.last.output) (fun i => (hb i).1) (fun i => (hb i).2.1)
    (fun i => (hb i).2.2) hS
  have h₄ := erase_runsWithin hom (ip := p.last.inputPos) (W := p.last.workTapes)
    (out := p.last.output) (fun i => (hb i).1) (fun i => (hb i).2.1)
    (fun i z hz => by have := (hinv i).2.2.2.2 z hz; have := hL i; have := hR i; omega) hS
  have h₅ := home_runsWithin (origin := origin) (mark := mark) (ip := p.last.inputPos)
    (out := p.last.output) (fun i => (hb i).1) (fun i => (hb i).2.1) hS
  have h₆ := rewind_runsWithin (ip := p.last.inputPos) (W := fun _ _ => none)
    (out := p.last.output) (fun _ _ => none) (S := S')
    (fun i => hmem i 0 (by have := hb i; omega) (by have := hb i; omega))
  obtain ⟨Q, hQh, hQl, hQt, hQS⟩ :=
    (((((h₀.seq rfl h₁).seq rfl h₂).seq rfl h₃).seq rfl h₄).seq rfl h₅).seq rfl h₆
  -- the input head moved at most `t` cells
  have hip : (p.last.inputPos : ℕ) ≤ 1 + t := by
    have h := inputPos_runFrom_le tm p.head p.length
    rw [← Fin.val_last p.length, ← runPath_apply_eq_runFrom] at h
    simp [hp0] at h
    exact h.trans (by omega)
  refine computesTidily_iff.mpr ⟨Q, by rw [wordsCfg_eq_pairCfg]; exact hQh,
    by rw [wordsCfg_eq_pairCfg, ← hout]; exact hQl, ?_, ?_⟩
  · have hsup : ∀ m : Fin k → ℕ, (∀ i, m i ≤ s) → Finset.univ.sup m ≤ s := fun m hm =>
      Finset.sup_le fun i _ => hm i
    have := hsup _ fun i => (show (R i - x i + 1).toNat ≤ s by have := hsi i; have := hb i; omega)
    have := hsup _ fun i => (show (R i - L i + 1).toNat ≤ s by have := hsi i; omega)
    have := hsup _ fun i => (show (1 - L i).toNat ≤ s by have := hsi i; have := hb i; omega)
    change Q.length ≤ _
    omega
  · have hcard : ∀ i, (S' i).card ≤ p.spaceUsedByTape i + 2 := fun i =>
      (Finset.card_insert_le _ _).trans (Nat.succ_le_succ (Finset.card_insert_le _ _))
    calc Q.space ≤ ∑ j, (Fin.append S' S' j).card := Q.space_le_sum_card hQS
      _ = 2 * ∑ i, (S' i).card := by rw [Fin.sum_univ_add]; simp [-Fin.natAdd_eq_addNat, two_mul]
      _ ≤ 2 * ∑ i, (p.spaceUsedByTape i + 2) := by gcongr with i; exact hcard i
      _ = 2 * (p.space + 2 * k) := by simp [Finset.sum_add_distrib, MultiTapeNTM.RunPath.space,
        mul_comm]
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

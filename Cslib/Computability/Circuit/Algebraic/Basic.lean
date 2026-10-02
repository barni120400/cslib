/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/
module

public import Cslib.Computability.Circuit.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Algebraic circuits

The algebraic basis consists of constants from `R`, binary addition, and binary multiplication.
`AlgebraicCircuit R inputCount outputCount` specializes the generic `Circuit` to this basis,
retaining shared gates, arbitrary output wires, and the generic size and depth conventions.
In particular, constants cost one gate, while inputs and output selection cost nothing.

This is the bounded fan-in arithmetic circuit model of
[Shpilka and Yehudayoff, Section 1.1][ShpilkaYehudayoff2010], with a topological ordering included
in the representation. That reference counts edges; here size counts operation gates.
The syntax does not require algebraic laws; the usual interpretation only needs addition and
multiplication. Polynomial semantics over a commutative semiring are provided in
`Cslib.Computability.Circuit.Algebraic.Polynomial`.

## References

* [Amir Shpilka and Amir Yehudayoff, *Arithmetic Circuits: A Survey of Recent Results and
  Open Questions*][ShpilkaYehudayoff2010]
-/

@[expose] public section

namespace Cslib.Circuits
namespace Algebraic

/-- Algebraic operations with constants from `R`. -/
inductive Op (R : Type*) where
  /-- A constant from the coefficient type. -/
  | const (value : R)
  /-- Binary addition. -/
  | add
  /-- Binary multiplication. -/
  | mul
  deriving DecidableEq, Fintype

/-- The signature of constants, binary addition, and binary multiplication. -/
abbrev signature (R : Type*) : Signature where
  Op := Op R
  Arity
    | .const _ => 0
    | .add | .mul => 2

/-- Interpret constants and arithmetic operations in `R`. -/
def interpretation (R : Type*) [Add R] [Mul R] : Interpretation (signature R) R
  | .const value, _ => value
  | .add, x => x 0 + x 1
  | .mul, x => x 0 * x 1

/-- Every program over the algebraic basis has fan-in at most two. -/
theorem program_fanInAtMost_two {R : Type*} {inputCount gateCount : ℕ}
    (p : Program (signature R) inputCount gateCount) : p.FanInAtMost 2 := by
  induction p with
  | empty => trivial
  | gate p line ih => exact ⟨ih, by cases line.op <;> simp⟩

end Algebraic

/-- A circuit with constants from `R`, binary addition, and binary multiplication.
Taking `outputCount = 1` gives the usual single-output algebraic circuit. -/
abbrev AlgebraicCircuit (R : Type*) (inputCount outputCount : ℕ) :=
  Circuit (Algebraic.signature R) inputCount outputCount

/-- Every algebraic circuit has fan-in at most two. -/
theorem AlgebraicCircuit.fanInAtMost_two {R : Type*} {inputCount outputCount : ℕ}
    (c : AlgebraicCircuit R inputCount outputCount) : c.FanInAtMost 2 :=
  Algebraic.program_fanInAtMost_two c.program

end Cslib.Circuits

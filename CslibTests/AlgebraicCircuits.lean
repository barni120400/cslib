/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

import Cslib.Computability.Circuit.Algebraic.Polynomial
import Cslib.Computability.Circuit.Composition
import Mathlib.Data.Fin.VecNotation

/-! # Algebraic circuit tests

Exercise shared gates, constants, multiple outputs, polynomial semantics, and generic composition.
-/

namespace CslibTests.AlgebraicCircuits

open Cslib.Circuits

/-- Compute `(x₀ + x₁)²`, retaining the shared sum and the first input as additional outputs. -/
def squareSum (R : Type*) : AlgebraicCircuit R 2 3 where
  program := .gate (.gate .empty ⟨.add, ![.input 0, .input 1]⟩) ⟨.mul, ![.gate 0, .gate 0]⟩
  outputs := ![.gate 1, .gate 0, .input 0]

example : (squareSum ℕ).eval (Algebraic.interpretation ℕ) ![2, 3] = ![25, 5, 2] := by
  decide

example : (squareSum ℕ).size = 2 := rfl

example : (squareSum ℕ).depth = 2 := by decide

example : (squareSum ℕ).FanInAtMost 2 := AlgebraicCircuit.fanInAtMost_two _

example : ¬ (squareSum ℕ).FanInAtMost 1 := by decide

example {R : Type*} [CommSemiring R] (x : Fin 2 → R) :
    (squareSum R).eval (Algebraic.interpretation R) x 0 = (x 0 + x 1) ^ 2 := by
  rw [pow_two]
  rfl

example {R : Type*} [CommSemiring R] :
    (squareSum R).polynomials 0 =
      (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) R) ^ 2 := by
  rw [pow_two]
  rfl

/-- A constant is available even when there are no input wires. -/
def constant {R : Type*} (value : R) : AlgebraicCircuit R 0 1 where
  program := .gate .empty ⟨.const value, Fin.elim0⟩
  outputs := fun _ ↦ .gate 0

example : (constant (-3 : ℤ)).eval (Algebraic.interpretation ℤ) Fin.elim0 0 = -3 := rfl

example : (constant (7 : ℕ)).size = 1 := rfl

example : (constant (7 : ℕ)).depth = 1 := rfl

example {R : Type*} [CommSemiring R] (value : R) :
    (constant value).polynomials 0 = MvPolynomial.C value := rfl

/-- Zero-gate wiring duplicates an input, so the first output is the square of twice that input. -/
def squareDouble (R : Type*) : AlgebraicCircuit R 1 3 :=
  (squareSum R).comp (Circuit.wiring (Algebraic.signature R) fun _ ↦ 0)

example : (squareDouble ℕ).eval (Algebraic.interpretation ℕ) ![3] = ![36, 6, 3] := by decide

example : (squareDouble ℕ).size = 2 := rfl

example {R : Type*} [CommSemiring R] (x : Fin 1 → R) :
    MvPolynomial.eval x ((squareDouble R).polynomials 0) =
      (squareSum R).eval (Algebraic.interpretation R) (fun _ ↦ x 0) 0 := by
  rw [AlgebraicCircuit.eval_polynomials]
  simp [squareDouble, Function.comp_def]

example {R : Type*} [CommSemiring R] :
    (squareDouble R).Computes (Algebraic.interpretation R)
      (fun x output ↦ MvPolynomial.eval x ((squareDouble R).polynomials output)) :=
  AlgebraicCircuit.computes_polynomials _

-- A circuit can have no outputs even though it contains a gate.
example : (show AlgebraicCircuit ℕ 0 0 from
    ⟨(constant 7).program, Fin.elim0⟩).depth = 0 := rfl

end CslibTests.AlgebraicCircuits

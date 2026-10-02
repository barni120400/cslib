/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

import Cslib.Computability.Circuit.Algebraic.Synthesis
import Cslib.Computability.Circuit.Composition
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Algebraic circuit tests

Exercise shared gates, constants, multiple outputs, polynomial semantics, and generic composition.
-/

namespace CslibTests.AlgebraicCircuits

open Cslib.Circuits

/-- Compute `(x₀ + x₁)²`, retaining the shared sum and the first input as additional outputs. -/
def squareSum (K : Type*) [Field K] : AlgebraicCircuit K 2 3 where
  program := .gate (.gate .empty ⟨.add, ![.input 0, .input 1]⟩) ⟨.mul, ![.gate 0, .gate 0]⟩
  outputs := ![.gate 1, .gate 0, .input 0]

/-- Evaluation reads both the final product and its shared intermediate sum. -/
theorem squareSum_eval {K : Type*} [Field K] (x : Fin 2 → K) :
    (squareSum K).eval (Algebraic.interpretation K) x =
      ![(x 0 + x 1) * (x 0 + x 1), x 0 + x 1, x 0] := by
  funext output
  fin_cases output <;> rfl

example : (squareSum ℚ).eval (Algebraic.interpretation ℚ) ![2, 3] = ![25, 5, 2] := by
  norm_num [squareSum_eval]

example : (squareSum ℚ).eval (Algebraic.interpretation ℚ) ![1 / 2, 1 / 2] =
    ![1, 1, 1 / 2] := by
  norm_num [squareSum_eval]

example : (squareSum ℚ).size = 2 := rfl

example : (squareSum ℚ).depth = 2 := by decide

example : (squareSum ℚ).FanInAtMost 2 := AlgebraicCircuit.fanInAtMost_two _

example : ¬ (squareSum ℚ).FanInAtMost 1 := by decide

example {K : Type*} [Field K] (x : Fin 2 → K) :
    (squareSum K).eval (Algebraic.interpretation K) x 0 = (x 0 + x 1) ^ 2 := by
  rw [pow_two]
  rfl

example {K : Type*} [Field K] :
    (squareSum K).polynomials 0 =
      (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^ 2 := by
  rw [pow_two]
  rfl

/-- A constant is available even when there are no input wires. -/
def constant {K : Type*} [Field K] (value : K) : AlgebraicCircuit K 0 1 where
  program := .gate .empty ⟨.const value, Fin.elim0⟩
  outputs := fun _ ↦ .gate 0

example : (constant (-3 : ℚ)).eval (Algebraic.interpretation ℚ) Fin.elim0 0 = -3 := rfl

example : (constant (7 : ℚ)).size = 1 := rfl

example : (constant (7 : ℚ)).depth = 1 := rfl

example {K : Type*} [Field K] (value : K) :
    (constant value).polynomials 0 = MvPolynomial.C value := rfl

/-- Zero-gate wiring duplicates an input, so the first output is the square of twice that input. -/
def squareDouble (K : Type*) [Field K] : AlgebraicCircuit K 1 3 :=
  (squareSum K).comp (Circuit.wiring (Algebraic.signature K) fun _ ↦ 0)

example : (squareDouble ℚ).eval (Algebraic.interpretation ℚ) ![3] = ![36, 6, 3] := by
  norm_num [squareDouble, squareSum_eval, Function.comp_def]

example : (squareDouble ℚ).size = 2 := rfl

example {K : Type*} [Field K] (x : Fin 1 → K) :
    MvPolynomial.eval x ((squareDouble K).polynomials 0) =
      (squareSum K).eval (Algebraic.interpretation K) (fun _ ↦ x 0) 0 := by
  rw [AlgebraicCircuit.eval_polynomials]
  simp [squareDouble, Function.comp_def]

example {K : Type*} [Field K] :
    (squareDouble K).Computes (Algebraic.interpretation K)
      (fun x output ↦ MvPolynomial.eval x ((squareDouble K).polynomials output)) :=
  AlgebraicCircuit.computes_polynomials _

-- A circuit can have no outputs even though it contains a gate.
example : (show AlgebraicCircuit ℚ 0 0 from
    ⟨(constant 7).program, Fin.elim0⟩).depth = 0 := rfl

end CslibTests.AlgebraicCircuits

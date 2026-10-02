/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/
module

public import Cslib.Computability.Circuit.Algebraic.Basic
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Polynomial semantics of algebraic circuits

Evaluate an algebraic circuit on formal variables to obtain one multivariate polynomial per
output. Evaluating those polynomials at an input agrees with running the original circuit.
This follows from the generic `Circuit.map_eval` theorem, using polynomial evaluation as a
homomorphism of interpretations.

Equality of output polynomials implies equality of the functions computed by the circuits.
The converse need not hold over finite fields: polynomial semantics retain the formal polynomial,
not just its values on the coefficient ring.
-/

@[expose] public section

namespace Cslib.Circuits

variable {R : Type*} [CommSemiring R] {inputCount outputCount : ℕ}

namespace Algebraic

/-- Interpret algebraic gates as operations on multivariate polynomials with coefficients in `R`.
Constant gates are embedded using `MvPolynomial.C`. -/
noncomputable def polynomialInterpretation (R : Type*) [CommSemiring R] (inputCount : ℕ) :
    Interpretation (signature R) (MvPolynomial (Fin inputCount) R)
  | .const value, _ => MvPolynomial.C value
  | .add, x => x 0 + x 1
  | .mul, x => x 0 * x 1

/-- Polynomial evaluation preserves the interpretation of each algebraic gate. -/
noncomputable def evalHomomorphism (x : Fin inputCount → R) :
    Homomorphism (polynomialInterpretation R inputCount) (interpretation R) where
  map := MvPolynomial.eval x
  homomorphic := by
    intro op input
    cases op <;> simp [polynomialInterpretation, interpretation]

end Algebraic

namespace AlgebraicCircuit

/-- The formal polynomial at each output of an algebraic circuit. -/
noncomputable def polynomials (c : AlgebraicCircuit R inputCount outputCount) :
    Fin outputCount → MvPolynomial (Fin inputCount) R :=
  c.eval (Algebraic.polynomialInterpretation R inputCount) MvPolynomial.X

/-- A wiring circuit selects the corresponding formal variables. -/
@[simp] theorem polynomials_wiring (select : Fin outputCount → Fin inputCount) :
    polynomials (Circuit.wiring (Algebraic.signature R) select) = MvPolynomial.X ∘ select := rfl

/-- Evaluating an output polynomial agrees with evaluating the circuit at that output. -/
@[simp] theorem eval_polynomials (c : AlgebraicCircuit R inputCount outputCount)
    (x : Fin inputCount → R) (output : Fin outputCount) :
    MvPolynomial.eval x (c.polynomials output) = c.eval (Algebraic.interpretation R) x output := by
  simpa [polynomials, Algebraic.evalHomomorphism, Function.comp_def] using
    congrFun (c.map_eval (Algebraic.evalHomomorphism x) MvPolynomial.X) output

/-- An algebraic circuit computes the function obtained by evaluating its output polynomials. -/
theorem computes_polynomials (c : AlgebraicCircuit R inputCount outputCount) :
    c.Computes (Algebraic.interpretation R)
      (fun x output ↦ MvPolynomial.eval x (c.polynomials output)) :=
  fun x ↦ funext fun output ↦ (c.eval_polynomials x output).symm

end AlgebraicCircuit

end Cslib.Circuits

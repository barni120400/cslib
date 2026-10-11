/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/
module

public import Cslib.Computability.Circuit.Algebraic.Polynomial
public import Cslib.Computability.Circuit.Synthesis

/-!
# Synthesis of algebraic circuits

Every multivariate polynomial over a field is the formal output polynomial of an algebraic
circuit. The proof uses polynomial induction and the generic synthesis rules for constants,
input projections, addition, and multiplication. It synthesizes polynomial substitution first,
then evaluates the resulting circuit at the formal variables.

This is the polynomial analogue of constructing circuits for Boolean functions. The statement
concerns formal polynomial equality, so it also applies over finite fields without identifying
distinct polynomials that happen to define the same function.
-/

@[expose] public section

namespace Cslib.Circuits

variable {K : Type*} [Field K] {inputCount : ℕ}

namespace Algebraic

private theorem synthesis_substitution (p : MvPolynomial (Fin inputCount) K) :
    ∃ cost, Synthesis (polynomialInterpretation K inputCount) (inputs inputCount)
      {fun x ↦ MvPolynomial.eval₂ MvPolynomial.C x p} cost := by
  induction p using MvPolynomial.induction_on with
  | C value =>
    refine ⟨1, ?_⟩
    simpa [polynomialInterpretation] using
      (Synthesis.nullary (I := polynomialInterpretation K inputCount)
        (s := inputs inputCount) (.const value) rfl)
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact ⟨a + b + 1, by simpa [polynomialInterpretation] using ha.binary hb .add⟩
  | mul_X p i hp =>
    obtain ⟨a, ha⟩ := hp
    have hx : Synthesis (polynomialInterpretation K inputCount) (inputs inputCount)
        {fun x ↦ x i} 0 := Synthesis.of_mem ⟨i, rfl⟩
    exact ⟨a + 1, by simpa [polynomialInterpretation] using ha.binary hx .mul⟩

end Algebraic

namespace AlgebraicCircuit

/-- Every multivariate polynomial over a field is the formal output of an algebraic circuit. -/
theorem exists_polynomial (p : MvPolynomial (Fin inputCount) K) :
    ∃ c : AlgebraicCircuit K inputCount 1, c.polynomials 0 = p := by
  obtain ⟨cost, h⟩ := Algebraic.synthesis_substitution p
  obtain ⟨c, hc, _⟩ := h.exists_circuit
  exact ⟨c, by simpa [polynomials, single] using congrFun (hc MvPolynomial.X) 0⟩

/-- Every polynomial function over a field is computed by an algebraic circuit. -/
theorem exists_circuit (p : MvPolynomial (Fin inputCount) K) :
    ∃ c : AlgebraicCircuit K inputCount 1,
      c.Computes (Algebraic.interpretation K) (single fun x ↦ MvPolynomial.eval x p) := by
  obtain ⟨c, hc⟩ := exists_polynomial p
  refine ⟨c, fun x ↦ funext fun output ↦ ?_⟩
  have houtput : output = 0 := Subsingleton.elim _ _
  simpa [houtput, hc, single] using (c.eval_polynomials x output).symm

end AlgebraicCircuit
end Cslib.Circuits

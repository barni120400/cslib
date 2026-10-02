# Circuit API

The namespaces below are rooted at `Cslib.Circuits`. Circuits separate their syntax from the
operations used to evaluate them.

| Layer | Role | Main API |
| --- | --- | --- |
| `Signature` | Gate symbols and their finite arities; the set of symbols may be infinite. | `Op`, `Arity` |
| `Wire` | A reference to an input or an earlier gate. | `input`, `gate`, `elim`, `Renaming` |
| `Line` | One gate symbol with one wire per argument. | `op`, `wires`, `eval`, `mapWires` |
| `Program` | Gates in topological order. The gate-count index prevents forward references. | `empty`, `gate`, `eval`, `trace` |
| `Circuit` | A program together with designated output wires. | `program`, `outputs`, `eval`, `Computes`, `ComputesOn` |
| `Interpretation` | An operation on a carrier for each gate symbol. | `Interpretation signature Carrier` |
| `Homomorphism` | A carrier map preserving every interpreted operation. | `Circuit.map_eval` |

`Program.eval` returns all gate values. `Program.trace` additionally allows reading the original
inputs through `Wire`. `Circuit.eval` reads only the designated outputs from that trace. A gate
may be read repeatedly, shared by several later gates, and selected as an output even if later
gates also read it.

Size counts all operation gates, including constants, but excludes inputs and output selection.
Inputs have depth zero; a constant gate has depth one. Circuit depth is the maximum depth of its
selected outputs, so unused gates do not increase circuit depth.

## Building on the core

- `Composition`: `d.comp c` feeds the outputs of `c` to `d`; `c.append d` runs both on the same
  inputs and joins their outputs. Both add gate counts and have evaluation theorems.
- `Synthesis`: construct circuits from derivations showing which scalar functions can be obtained
  from available functions within a gate budget.
- `Complexity`: `ecomplexity` and `ecomplexityOn` give the least gate count, or infinity when no
  circuit exists. Natural-number `complexity` additionally requires a complete interpretation.
- `Normalization`: merge gates computing the same function without increasing size.
- `Finite`, `Counting`, and `Shannon`: enumerate finite gate bases, count computable functions,
  and derive lower bounds under the stated finiteness hypotheses.
- `Boolean`: instantiate the core with constants, NOT, AND, and OR, then develop Boolean synthesis
  and complexity results.

## Algebraic circuits

Import `Cslib.Computability.Circuit.Algebraic.Basic` for the definition:

```lean
AlgebraicCircuit K inputCount outputCount -- assumes [Field K]
-- abbreviates Circuit (Algebraic.signature K) inputCount outputCount
```

The basis has `Algebraic.Op.const k`, `.add`, and `.mul`. Constants have arity zero; addition and
multiplication have arity two. `Algebraic.interpretation K` supplies arithmetic in the field `K`.
The underlying `Op` and `signature` do not depend on the field laws. There are no primitive
subtraction or division gates; negation can be expressed using `-1` and multiplication.

The abbreviation uses the existing circuit representation, so wiring, composition, size, depth,
and the generic semantics apply directly. The operation type is finite when `K` is finite;
unrestricted constants over an infinite coefficient type do not form a finite gate basis.

Import `Cslib.Computability.Circuit.Algebraic.Polynomial` for formal polynomial semantics:

```lean
c.polynomials output : MvPolynomial (Fin inputCount) K
```

`c.polynomials` runs the same circuit with constant gates interpreted by `MvPolynomial.C` and
inputs by `MvPolynomial.X`. `Algebraic.evalHomomorphism` connects this interpretation to ordinary
arithmetic. The generic `Circuit.map_eval` then proves `AlgebraicCircuit.eval_polynomials`:
evaluating each output polynomial at `x` agrees with `c.eval (Algebraic.interpretation K) x`.

Formal polynomial equality is stronger than equality as functions over finite fields. Use
`polynomials` for the former and the generic `Computes` API for the latter. Examples exercising
constants, shared gates, multiple outputs, and composition are in
[`CslibTests/AlgebraicCircuits.lean`](../../../CslibTests/AlgebraicCircuits.lean).

## Fan-in terminology

The number of inputs to a gate is its **fan-in**. Bounded fan-in means a fixed constant bound;
the usual binary basis has bound two. Unbounded fan-in permits arbitrary finite arities.

| Model | Binary basis | Unbounded fan-in basis |
| --- | --- | --- |
| Arithmetic (algebraic) | Field constants, binary `+` and `×` | Field constants, sums and products of arbitrary finite arity |
| Boolean | Constants, unary NOT, binary AND and OR (De Morgan basis) | Constants, unary NOT, AND and OR of arbitrary finite arity |

For arithmetic circuits, see [Shpilka and Yehudayoff, Section 1.1][SY10]. For Boolean circuits,
compare [Oliveira's binary definition][BooleanBinary] with [Blais's unbounded definition][BooleanUnbounded].
Fan-out describes reuse of a result; restricting it to one yields the formula model.

The current Boolean and algebraic signatures are binary. An unbounded variant fits the existing
`Signature` API by indexing sum/product or AND/OR symbols by their arity. Such a basis is infinite
even over a finite field, so the existing finite-basis counting theorems would need further bounds.
Size conventions also matter: CSLib counts operation gates, whereas [SY10] counts edges.

## A first synthesis result

Import `Cslib.Computability.Circuit.Algebraic.Synthesis` for
`AlgebraicCircuit.exists_polynomial`: every `p : MvPolynomial (Fin n) K` has a circuit
`c : AlgebraicCircuit K n 1` with `c.polynomials 0 = p`.
`AlgebraicCircuit.exists_circuit` then states that `c` computes `fun x ↦ MvPolynomial.eval x p`.

This parallels the existence of circuits for Boolean functions in `Boolean.LupanovConstruction`
and `Boolean.Lupanov`, without their quantitative size bounds. The proof uses the same generic
`Synthesis` layer, applying polynomial induction to constants, sums, and products by variables.
Together with `computes_polynomials`, it characterizes the functions computed by algebraic
circuits as polynomial functions. It does not assert that every function on an arbitrary field
is polynomial.

[SY10]: https://www.cs.tau.ac.il/~shpilka/publications/SY10.pdf
[BooleanBinary]: https://cs.uwaterloo.ca/~r5olivei/courses/2024-fall-cs360/lecture-notes/lecture08/
[BooleanUnbounded]: https://cs.uwaterloo.ca/~eblais/cs365/w25/circuits

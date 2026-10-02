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
AlgebraicCircuit R inputCount outputCount
-- abbreviates Circuit (Algebraic.signature R) inputCount outputCount
```

The basis has `Algebraic.Op.const r`, `.add`, and `.mul`. Constants have arity zero; addition and
multiplication have arity two. `Algebraic.interpretation R` supplies the usual arithmetic
operations. The syntax works for any coefficient type, and evaluation requires `Add R` and
`Mul R`. The ordinary algebraic setting is a commutative semiring, including rings and fields.
There are no primitive subtraction or division gates; over a ring, negation can be expressed
using the constant `-1` and multiplication.

The abbreviation uses the existing circuit representation, so wiring, composition, size, depth,
and the generic semantics apply directly. The operation type is finite when `R` is finite;
unrestricted constants over an infinite coefficient type do not form a finite gate basis.

Import `Cslib.Computability.Circuit.Algebraic.Polynomial` for formal polynomial semantics:

```lean
c.polynomials output : MvPolynomial (Fin inputCount) R
```

`c.polynomials` runs the same circuit with constant gates interpreted by `MvPolynomial.C` and
inputs by `MvPolynomial.X`. `Algebraic.evalHomomorphism` connects this interpretation to ordinary
arithmetic. The generic `Circuit.map_eval` then proves `AlgebraicCircuit.eval_polynomials`:
evaluating each output polynomial at `x` agrees with `c.eval (Algebraic.interpretation R) x`.

Formal polynomial equality is stronger than equality as functions over finite fields. Use
`polynomials` for the former and the generic `Computes` API for the latter. Examples exercising
constants, shared gates, multiple outputs, and composition are in
[`CslibTests/AlgebraicCircuits.lean`](../../../CslibTests/AlgebraicCircuits.lean).

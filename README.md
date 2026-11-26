# Sumcheck in Agda

Executable sumcheck verifiers with constructive correctness proofs in Agda, covering symbolic circuits and evaluation-form messages of arbitrary degree.

The verifiers work over commutative rings with decidable equality, with certified node weights for general-degree evaluation form. The ring implementation supports naturals modulo every p ≥ 2; a separate F₅ version is kept as a small worked example.

## Example

Take `p(x,y) = 1 + x + 2y + xy` over F₅ and the claim that its sum over `{0,1}²` is 1.

| Round | Prover sends `g(0), g(1)` | Check | Challenge | Next claim `g(r)` |
| --- | --- | --- | --- | --- |
| 1 | 4, 2 | 4 + 2 = 1 | 2 | 0 |
| 2 | 3, 2 | 3 + 2 = 0 | 3 | 0 |

The final check is `p(2,3) = 0`. See [`Examples.agda`](src/Examples.agda) and [`Modular/Examples.agda`](src/Modular/Examples.agda), which also covers F₁₇.

## What is proved

- **Verifier and specification are equivalent.** `verify-sound` and `verify-complete` ([`Ring/Correctness.agda`](src/Ring/Correctness.agda)) show the Boolean checker accepts exactly the transcripts satisfying the inductive relation `Accepts`. They hold for any operations with a setoid equality, decidable equality and the interpolation identity. `verifyWith-cong` gives invariance under equivalent evaluators and oracles.
- **Interpolation in any commutative ring** ([`Ring/Interpolation.agda`](src/Ring/Interpolation.agda)). Two-point interpolation equals the Lagrange form; no multiplicative inverses or primality are needed. `coefficient-evaluation` is a stdlib `Inverse` between coefficients `(a, b)` of `a + bX` and values at 0 and 1, under pointwise setoid equality.
- **Derived dictionary** ([`Ring/FromRing.agda`](src/Ring/FromRing.agda)). A `CommutativeRing`, decidable equality and a normalization with `normalize x ≈ x` give the executable `Operations` and all hypotheses of the correctness theorem.
- **Arithmetic modulo p = k + 2** ([`Modular/Ring.agda`](src/Modular/Ring.agda), [`Modular/Correctness.agda`](src/Modular/Correctness.agda)). Naturals under stdlib's `_≡%[ p ]_` form a `CommutativeRing`; with reduction mod p as normalization, `Ring.FromRing` gives the theorem for every p ≥ 2. Primality is not assumed; composite moduli are accepted.

- **Arbitrary-degree sumcheck with an honest prover** ([`Circuit/Protocol.agda`](src/Circuit/Protocol.agda), [`Circuit/Completeness.agda`](src/Circuit/Completeness.agda)). Polynomials are arithmetic circuits and round messages are unexpanded sums of univariate circuits. `honest-complete` proves that for any circuit, any challenges and the true Boolean-cube sum, the honest transcript is accepted, provided the degree bound is at least the circuit's conservative `bound`. It needs only reflexivity of the executable equality. `Ring.FromRing` instantiates it for any ring with decidable equality, hence for every modulus ([`Modular/CircuitExamples.agda`](src/Modular/CircuitExamples.agda)). [`Circuit/Degree.agda`](src/Circuit/Degree.agda) proves that accepted messages have structural degree at most the bound.
- **Evaluation form equals circuit form** ([`Circuit/EvaluationForm.agda`](src/Circuit/EvaluationForm.agda)). For every transcript, including adversarial ones, the linear verifier `Ring.Verifier.verify` on value pairs accepts exactly when the circuit verifier accepts the decoded affine messages at degree bound 1 (`wire-verify-equivalent`). Decoding is `Ring.Interpolation`'s inverse of endpoint evaluation. Certified-linear circuit messages encode the other way (`verify-equivalent`). A degree-0 evaluation-form verifier also checks that both values agree, and matches the circuit verifier at bound 0 when all endpoint pairs agree (`constant-verify-equivalent`). Examples are in [`Modular/EvaluationFormExamples.agda`](src/Modular/EvaluationFormExamples.agda).
- **General-degree evaluation form** ([`Ring/Lagrange.agda`](src/Ring/Lagrange.agda), [`Circuit/Barycentric.agda`](src/Circuit/Barycentric.agda)). Lagrange interpolation on d + 1 nodes over a commutative ring, in the first barycentric form with certified weights: Kronecker node law, setoid congruence, and degree 0 and 1 as special cases (degree 1 is the existing two-point formula). The verifier evaluates received tuples in O(d+1) ring operations per point, proved equal to the direct formula, and never builds a polynomial. `verify-equivalent`: for a fixed node set shared by all rounds, its verdict equals `Circuit.Protocol.verify` on the decoded Lagrange circuits, for all received lists and challenges, malformed ones included. Examples (z-lean Examples 1 and 3 in F₁₇, mixed degrees, a composite modulus) are in [`Modular/BarycentricExamples.agda`](src/Modular/BarycentricExamples.agda).

The F₅ modules ([`Sumcheck.agda`](src/Sumcheck.agda), [`FieldLaws.agda`](src/FieldLaws.agda), [`Quest12Bridge.agda`](src/Quest12Bridge.agda)) prove interpolation correctness by exhaustive computation and verifier equivalence by induction on transcripts.

## Not proved

These results establish verifier/specification equivalence and honest-prover completeness, not cryptographic soundness. Cryptographic soundness would bound the probability, over random challenges, that a false claim is accepted (Schwartz–Zippel; Thaler §4.1). [`dishonest-fixed-challenge-accepted`](src/Examples.agda) shows a false claim passing with fixed challenges. Challenge generation, zero knowledge and extracted code are also not covered.

The circuit degree check counts variable occurrences in each univariate leaf, giving a conservative bound rather than the exact polynomial degree. A bridge to formal polynomial degree is not proved. The honest prover enumerates the Boolean cube, so both computation and round-message size grow exponentially with the number of remaining variables. Out-of-range variables evaluate to zero.

For the barycentric verifier, weights are supplied and checked, not computed. Uniqueness of degree-bounded interpolants (reconstructing an arbitrary bounded circuit from its node values) is not proved. Partial-run residual-sum semantics and non-Boolean summation domains are not formalized. The representation theorem currently requires a fixed node set shared by all rounds.

## Check

Requires Agda 2.9.0 and the standard library 2.4.

```sh
agda --build-library
```

## References

- Lund, Fortnow, Karloff, Nisan (1992). [Algebraic Methods for Interactive Proof Systems](https://doi.org/10.1145/146585.146605).
- Justin Thaler. [Proofs, Arguments, and Zero-Knowledge](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf), §2.4 (interpolation), §4.1 (sumcheck).
- Agda stdlib modular arithmetic: [#581](https://github.com/agda/agda-stdlib/issues/581); quotient-ring draft [#2729](https://github.com/agda/agda-stdlib/pull/2729).
- Barycentric Lagrange interpolation: [DLMF §3.3(i)](https://dlmf.nist.gov/3.3.i); Berrut and Trefethen, [SIAM Review 46 (2004)](https://doi.org/10.1137/S0036144502417715). Lean counterparts: mathlib [`Lagrange`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Lagrange.lean) (`eval_interpolate_at_node`, `eval_interpolate_not_at_node`).
- [z-lean](https://github.com/z-tech/z-lean) - Lean sumcheck formalization that motivated this experiment.

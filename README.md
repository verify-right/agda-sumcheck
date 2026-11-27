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
- **Coefficient–evaluation isomorphism** ([`Ring/LagrangeInverse.agda`](src/Ring/LagrangeInverse.agda)). Certified weights make all node differences units; polynomials with d + 1 coefficients that agree at the nodes have equal coefficients, by monic synthetic division (no field, no 0 ≠ 1). Packaged as a stdlib `Inverse` between coefficient and value setoids.
- **Reconstruction of circuits** ([`Circuit/Normalization.agda`](src/Circuit/Normalization.agda), [`Circuit/Reconstruction.agda`](src/Circuit/Reconstruction.agda)). Every message passing `degreeOK d` is reproduced at every point by barycentric evaluation of its values at any certified node set of size d + 1.
- **General verifiers** ([`Circuit/General.agda`](src/Circuit/General.agda), [`Circuit/GeneralCompleteness.agda`](src/Circuit/GeneralCompleteness.agda)). One public degree bound and node set per round, an arbitrary summation domain list, partial runs with a residual-sum terminal oracle. The evaluation-form and symbolic verdicts agree for all well-formed transcripts; all malformed ones are rejected; the honest prover is complete under per-variable bounds. Tests are in [`Modular/GeneralExamples.agda`](src/Modular/GeneralExamples.agda).

The F₅ modules ([`Sumcheck.agda`](src/Sumcheck.agda), [`FieldLaws.agda`](src/FieldLaws.agda), [`Quest12Bridge.agda`](src/Quest12Bridge.agda)) prove interpolation correctness by exhaustive computation and verifier equivalence by induction on transcripts.

## Not proved

These results establish verifier/specification equivalence and honest-prover completeness, not cryptographic soundness. Cryptographic soundness would bound the probability, over random challenges, that a false claim is accepted (Schwartz–Zippel; Thaler §4.1). [`dishonest-fixed-challenge-accepted`](src/Examples.agda) shows a false claim passing with fixed challenges. Challenge generation, zero knowledge and extracted code are also not covered.

The circuit degree check counts variable occurrences in each univariate leaf, giving a conservative bound rather than the exact polynomial degree. A bridge to formal polynomial degree is not proved. The honest prover enumerates the Boolean cube, so both computation and round-message size grow exponentially with the number of remaining variables. Out-of-range variables evaluate to zero.

Weights are computed by `setup` from a supplied inversion procedure and always validated by `certify?`; the modular examples invert by finite search, not by extended GCD. Polynomials are circuits with positional variables defaulting to zero out of range; they model z-lean's `Fin n` variables only at the intended arity. The degree bounds are occurrence counts, not z-lean's exact `degreeOf`.

## Theorem scope

| Theorem | Statement (abridged) | Meaning |
| --- | --- | --- |
| `unit-differences` | `Certified x w → UnitDifferences x` | certified weights make every `x i - x j`, `i ≢ j`, a unit |
| `synthetic-divide-correct` | `p ≋ addHead (eval p a) (linearTimes a (quotient p a))` | `p = (X - a)·q + p(a)` coefficientwise |
| `eval-injective` | `UnitDifferences x → (∀ i → eval p (x i) ≈ eval q (x i)) → p ≋ q` | d + 1 node values determine d + 1 coefficients |
| `coefficient-evaluation` | `Certified x w → Inverse (Coefficients d) (Values (suc d))` | evaluation at nodes and Lagrange interpolation are inverse |
| `reconstruction` | `degreeOK d m ≡ true → B.evaluate ns (encode ns m) r ≈ evaluateMessage op m r` | evaluation form represents every checked circuit message |
| `verify-representation` | `evVerify dom oracle cs claim (toLists ts) rs ≡ symVerify dom oracle (bounds cs) claim (decodeTuples ts) rs` | equal verdicts on every well-formed transcript, any domain, oracle, node sets |
| `malformed-rejected` | `parse cs ms ≡ nothing → evRun … cs ms rs ≡ false` | wrong tuple sizes or round counts are rejected |
| `encode-representation` | `Checked cs ms → evVerify … (toLists (encodeChecked hs)) rs ≡ symVerify … ms rs` | encoding preserves the verdict of checked circuit messages |
| `symVerify-legacy`, `evRun-legacy` | Boolean domain, full run, repeated bound | the general verifiers specialize to `Circuit.Protocol.verify` and `Circuit.Barycentric.verify` |
| `residual-sum` | `residual dom f m prefix ≈ ringSum (map (λ z → f (prefix ++ z)) (tuples dom m))` | the partial-run oracle is `Σ_{z ∈ domain^m} f(prefix ++ z)` |
| `honest-complete`, `evaluation-form-complete` | `Bounded p 0 bs → … ≡ true` | the honest prover is accepted after any number of rounds |
| `setup-complete` | `(∀ i → ℓᵢ(xᵢ) * inv ℓᵢ(xᵢ) ≈ 1#) → ∃[ ns ] setup inv xs ≡ just ns` | setup succeeds when the inversion procedure is correct |

Costs: one barycentric evaluation is O(d+1) ring operations once weights are known, and a round sums |domain| evaluations; certifying weights is O((d+1)²). These are operation counts, not bit complexity or measurements. List append, normalization and residual enumeration (|domain|^m terms) have separate costs.

## Provenance

`Ring/DensePolynomial.agda` and `Ring/DensePolynomialLaws.agda` are ported unchanged from `quest28-hqc` (identical to Quest 15.13). `Zero`, `head-eval` and `quotient-zero` in `Ring/LagrangeInverse.agda` are adapted from Quest 15.13 `PolynomialRoots.agda`; `Circuit/Normalization.agda` generalizes Quest 15.13 `CircuitNormalization.agda` from arithmetic modulo p to any certified ring. Uniqueness uses monic synthetic division because the dense library already provides `quotient`; a Newton-basis argument would add machinery without shortening the proof.

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
- CompPoly (pinned by z-lean) has a verified, computable second-form barycentric evaluator with computed weights over fields: [Barycentric.lean](https://github.com/Verified-zkEVM/CompPoly/blob/06686e4c70939af82203af21516f8ab8a21a8051/CompPoly/Univariate/Barycentric.lean). The Agda development here uses the first form without division at the query and unit-certified weights over commutative rings.
- [z-lean](https://github.com/z-tech/z-lean) - Lean sumcheck formalization that motivated this experiment.

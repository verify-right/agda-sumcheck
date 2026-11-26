# Sumcheck in Agda

An executable linear sumcheck verifier with Agda correctness proofs. It works over any commutative ring and is instantiated for naturals modulo every p ≥ 2; a separate F₅ version is kept as a small worked example.

## Example

Take `p(x,y) = 1 + x + 2y + xy` over F₅ and the claim that its sum over `{0,1}²` is 1.

| Round | Prover sends `g(0), g(1)` | Check | Challenge | Next claim `g(r)` |
| --- | --- | --- | --- | --- |
| 1 | 4, 2 | 4 + 2 = 1 | 2 | 0 |
| 2 | 3, 2 | 3 + 2 = 0 | 3 | 0 |

The final check is `p(2,3) = 0`. See [`Examples.agda`](src/Examples.agda) and [`Modular/Examples.agda`](src/Modular/Examples.agda), which also covers F₁₇.

## What is proved

- **Verifier and specification are equivalent.** `verify-sound` and `verify-complete` ([`Ring/Correctness.agda`](src/Ring/Correctness.agda)) show the Boolean checker accepts exactly the transcripts satisfying the inductive relation `Accepts`. They hold for any operations with a setoid equality, decidable equality and the interpolation identity. `verifyWith-cong` gives invariance under equivalent evaluators and oracles.
- **Interpolation in any commutative ring** ([`Ring/Interpolation.agda`](src/Ring/Interpolation.agda)). Two-point interpolation equals the Lagrange form; no inverses or primality are needed. `coefficient-evaluation` is a stdlib `Inverse` between coefficients `(a, b)` of `a + bX` and values at 0 and 1, under pointwise setoid equality.
- **Arithmetic modulo p = k + 2** ([`Modular/Ring.agda`](src/Modular/Ring.agda), [`Modular/Correctness.agda`](src/Modular/Correctness.agda)). Naturals under stdlib's `_≡%[ p ]_` form a `CommutativeRing`, so the theorem holds for every p ≥ 2. Primality is not assumed; composite moduli are accepted.

The F₅ modules ([`Sumcheck.agda`](src/Sumcheck.agda), [`FieldLaws.agda`](src/FieldLaws.agda), [`Quest12Bridge.agda`](src/Quest12Bridge.agda)) prove the same equivalence by exhaustive computation.

## Not proved

These results are verifier/specification equivalence, not cryptographic soundness. Cryptographic soundness would bound the probability, over random challenges, that a false claim is accepted (Schwartz–Zippel; Thaler §4.1). Also not covered: challenge generation, zero knowledge, higher-degree round polynomials and extracted code. [`dishonest-fixed-challenge-accepted`](src/Examples.agda) shows a false claim passing with fixed challenges.

## Check

Requires Agda 2.9.0 and the standard library 2.4.

```sh
agda --build-library
```

## References

- Lund, Fortnow, Karloff, Nisan (1992). [Algebraic Methods for Interactive Proof Systems](https://doi.org/10.1145/146585.146605).
- Justin Thaler. [Proofs, Arguments, and Zero-Knowledge](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf), §2.4 (interpolation), §4.1 (sumcheck).
- Agda stdlib modular arithmetic: [#581](https://github.com/agda/agda-stdlib/issues/581); quotient-ring draft [#2729](https://github.com/agda/agda-stdlib/pull/2729).
- [z-lean](https://github.com/z-tech/z-lean) - Lean sumcheck formalization that motivated this experiment.

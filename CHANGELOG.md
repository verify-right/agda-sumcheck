# Changelog

## Verified evaluation-form verifier: uniqueness, reconstruction, general protocol

- Dense polynomials ported from Quest 28; certified weights give unit node differences; synthetic division as a coefficient identity.
- Uniqueness of interpolants over commutative rings and the coefficient–evaluation `Inverse`.
- Coefficient normalization of circuits and reconstruction of every degree-checked message from its node values.
- General symbolic and evaluation-form verifiers: per-round bounds and node sets, arbitrary domain lists, partial runs with residual sums; verdict equality, malformed-input rejection, legacy specializations.
- Honest-prover completeness under per-variable bounds, transferred to evaluation form; certified weight setup.
- Tests in F₁₇ and ℤ/15, including z-lean Example 3 with bounds (2, 1, 1) and stops k = 0…3.

## General-degree evaluation-form sumcheck

- Lagrange interpolation on d + 1 nodes with certified weights: Kronecker node law, congruence, degree 0 and degree 1 special cases.
- O(m) prefix/suffix-product barycentric evaluator, proved equal to the direct formula.
- Evaluation-form verifier with per-round node sets and an exact-length boundary for received lists.
- Verdict equals the circuit verifier for all transcripts under a fixed node set.
- F₁₇ examples, including z-lean Examples 1 and 3, mixed degrees and a composite modulus.

## Evaluation-form bridge

- The linear verifier on value pairs agrees with the circuit verifier at degree bound 1, for arbitrary transcripts.
- Certified-linear circuit messages encode to value pairs with the same verdict.
- Degree-0 evaluation-form verifier with an equal-endpoints check; equivalent to the circuit verifier at bound 0 for transcripts with equal endpoint pairs.
- Acceptance counting is deferred.

## Arbitrary-degree sumcheck and honest-prover completeness

- Circuit polynomials, sum-tree round messages and an executable honest prover.
- Honest-prover completeness for any circuit and degree bound covering it.
- Accepted messages have structural degree at most the bound.
- Oracle agreement for pointwise-equivalent final oracles.
- Instantiated through `Ring.FromRing`; examples over F₅ and F₁₇.

## Commutative-ring verifier and arithmetic modulo p ≥ 2

- Verifier parameterised by ring operations, with separate challenge list.
- Verifier/specification equivalence over commutative rings with decidable setoid equality.
- Naturals modulo p = k + 2 as a stdlib `CommutativeRing`.
- Examples over F₂, F₅, F₁₇ and modulo 4.
- Depends on the Agda standard library 2.4.

## Verified linear sumcheck over F₅

- Field F₅ and it's arithmetic and linear interpolation.
- Interpolation correctness.
- Executable transcript verifier.
- Verifier equivalence with its acceptance specification.
- Examples of accepted and rejected transcripts.
- Use Quest 12: dot-product transport construction.

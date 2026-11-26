# Changelog

## Evaluation-form bridge

- The linear verifier on value pairs agrees with the circuit verifier at degree bound 1, for arbitrary transcripts.
- Certified-linear circuit messages encode to value pairs with the same verdict.
- Degree-0 evaluation-form verifier with an equal-endpoints check, equivalent to the circuit verifier at bound 0.
- Acceptance counting is deferred.

## Arbitrary-degree sumcheck and honest-prover completeness

- Circuit polynomials, sum-tree round messages and an executable honest prover.
- Honest-prover completeness for any circuit and degree bound covering it.
- Accepted messages have structural degree at most the bound.
- Oracle agreement for pointwise-equivalent final oracles.
- Instantiated through `Ring.FromRing`; examples over F₅ and F₁₇.

## Commutative-ring verifier and arithmetic modulo p ≥ 2

- Verifier parameterised by ring operations, with separate challenge list.
- Soundness and completeness over any commutative ring with setoid equality.
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

# Sumcheck in Agda

An executable linear sumcheck verifier, with correctness proofs checked by Agda. One version works over F₅ (integers modulo 5). The other works over any commutative ring and is instantiated for naturals modulo every p ≥ 2.

## How it works

Suppose we have a polynomial:

```
p(x,y) = 1 + x + 2y + xy
```

Someone claims its sum over all Boolean inputs is 1:

```
p(0,0) + p(0,1) + p(1,0) + p(1,1) = 1 (mod 5)
```

Instead of evaluating every input, the verifier checks a sequence of smaller claims.

**Round 1**

The prover supplies two evaluations of a linear polynomial:

```
g₁(0) = 4
g₁(1) = 2
```

The verifier checks `4 + 2 = 1 (mod 5)`.

It then chooses a challenge `r₁ = 2`. Linear interpolation gives `g₁(2) = 0`.

**Round 2**

The prover supplies another pair:

```
g₂(0) = 3
g₂(1) = 2
```

The verifier checks `3 + 2 = 0 (mod 5)`.

With the next challenge `r₂ = 3`, interpolation gives `g₂(3) = 0`.

Finally, the verifier evaluates `p(2,3) = 0`.

Example is in [`honest-accepted`](src/Examples.agda).

The sum-check protocol was introduced by Lund, Fortnow, Karloff and Nisan (1992). See [Thaler, 4.1](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf) for the protocol and its soundness analysis.

## Modules

- [`Sumcheck.agda`](src/Sumcheck.agda):
  - F5 arithmetic and linear interpolation.
  - Transcript verification, including round consistency and final oracle evaluation.
  - Proofs connecting the executable checker to its mathematical specification.
  - `interpolate-is-lagrange`: our interpolation function agrees with the standard Lagrange formula.
  - `verify-sound` and `verify-complete`: the checker accepts exactly the transcripts satisfying its acceptance specification.
- [`FieldLaws.agda`](src/FieldLaws.agda) - arithmetic modulo 5.
- [`Examples.agda`](src/Examples.agda) - accepted and rejected transcripts, including a false claim accepted with fixed challenges.
- [`Quest12Bridge.agda`](src/Quest12Bridge.agda) - dot-product transport reused from other experiment.

### Commutative-ring verifier

- [`Ring/Verifier.agda`](src/Ring/Verifier.agda) - verifier parameterised by ring operations. Prover messages and challenges are separate lists, and their lengths are checked.
- [`Ring/Interpolation.agda`](src/Ring/Interpolation.agda) - two-point interpolation identity and endpoint laws in any stdlib `CommutativeRing`. No inverses or primality are needed.
- [`Ring/Correctness.agda`](src/Ring/Correctness.agda) - `verify-sound` and `verify-complete` relative to a setoid equality, assuming decidable equality and the interpolation identity; `verify-oracle-cong` for pointwise-equivalent oracles.
- [`Modular/Ring.agda`](src/Modular/Ring.agda) - naturals with `x ≈ y` iff `x mod p ≡ y mod p` form a commutative ring, for `p = k + 2`, built from stdlib `Data.Nat.DivMod` remainder laws.
- [`Modular/Correctness.agda`](src/Modular/Correctness.agda) - the correctness theorem for every modulus `p ≥ 2`.
- [`Modular/Examples.agda`](src/Modular/Examples.agda), [`Modular/CertifiedExamples.agda`](src/Modular/CertifiedExamples.agda) - F₂, F₅, F₁₇ and modulo-4 transcripts, noncanonical representatives, length mismatches, and the general theorem applied to concrete transcripts.

For prime p this is arithmetic in Fₚ, but primality and field inverses are not proved: composite moduli are accepted on purpose.

* Check proofs

Requires Agda 2.9.0 and the standard library 2.4.

```sh
agda --build-library
```


* Limitations

Supports only linear round polynomials.  
Challenges are provided externally.  
No probabilistic soundness, zero knowledge, correctness of extracted code.

See [`dishonest-fixed-challenge-accepted`](src/Examples.agda) for why challenge selection matters.

* References

- Lund, Fortnow, Karloff, Nisan (1992). [Algebraic Methods for Interactive Proof Systems](https://doi.org/10.1145/146585.146605).
- Justin Thaler. [Proofs, Arguments, and Zero-Knowledge](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf), §2.4 (interpolation), §4.1 (sumcheck).
- Modular arithmetic in the Agda standard library: [#581](https://github.com/agda/agda-stdlib/issues/581), and the quotient-ring draft [#2729](https://github.com/agda/agda-stdlib/pull/2729).
- [z-lean](https://github.com/z-tech/z-lean) - Lean sumcheck formalization that motivated this experiment.
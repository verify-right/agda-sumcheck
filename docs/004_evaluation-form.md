# Evaluation-form sumcheck

Work in $\mathbb F_{17}$ with the polynomial

$$
p(x)=1+2x.
$$

The prover can represent the round polynomial by its coefficients $(1,2)$ or its endpoint values $(1,3)$.

The claimed sum is

$$
p(0)+p(1)=4.
$$

At challenge $r=2$, the verifier computes directly from the received values:

$$
1+(3-1)2=5.
$$

There is no need to construct a symbolic polynomial.

`wire-verify-equivalent` proves that both representations give the same verification result for arbitrary received messages, including dishonest ones.

For constant polynomials, the verifier additionally checks that both endpoint values agree.

Proofs: [Circuit/EvaluationForm.agda](../src/Circuit/EvaluationForm.agda).

Examples: [Modular/EvaluationFormExamples.agda](../src/Modular/EvaluationFormExamples.agda).

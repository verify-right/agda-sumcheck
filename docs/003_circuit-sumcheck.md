# Arbitrary-degree sumcheck

Work in $\mathbb F_{17}$ with

$$
p(x,y)=1+x^3+2y^2+xy.
$$

The sum over Boolean inputs is 11.

The first round polynomial is

$$
g(x)=p(x,0)+p(x,1)=4+2x^3+x.
$$

The verifier checks $g(0)+g(1)=11$ and chooses the challenge 2.

The next claim is

$$
g(2)=22=5\pmod{17}.
$$

The second round polynomial is

$$
h(y)=p(2,y)=9+2y^2+2y.
$$

The verifier checks $h(0)+h(1)=5\pmod{17}$. At challenge 3, the final evaluation is 16.

`message-correct` proves that each honest message represents the remaining Boolean-cube sum.

`honest-complete` proves acceptance for every challenge sequence when the claim is correct and the degree bound is sufficient.

Proofs: [Circuit/Completeness.agda](../src/Circuit/Completeness.agda).

Example: [Modular/CircuitExamples.agda](../src/Modular/CircuitExamples.agda).

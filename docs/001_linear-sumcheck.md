# Linear sumcheck

Work in $\mathbb F_5$ with the polynomial

$$
p(x,y)=1+x+2y+xy.
$$

Its sum over Boolean inputs is

$$
1+3+2+5=1\pmod 5.
$$

Instead of summing all four values, consider

$$
g(x)=p(x,0)+p(x,1)=4+3x.
$$

The prover sends $g(0)=4$ and $g(1)=2$.

The verifier checks that their sum matches the claim and chooses a challenge $r=2$.

Linear interpolation gives

$$
g(r)=4+(2-4)r=0\pmod 5.
$$

The remaining claim concerns only one variable:

$$
p(2,0)+p(2,1)=0\pmod 5.
$$

Repeating this procedure reduces the claim to a single polynomial evaluation.

`verify-sound` and `verify-complete` prove that the executable verifier accepts exactly the transcripts satisfying the acceptance relation.

Proofs [Sumcheck.agda](../src/Sumcheck.agda).

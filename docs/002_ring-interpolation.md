# Linear interpolation over rings

A linear polynomial $f(x)=a+bx$ is determined by its values at 0 and 1:

$$
f(0)=a,\qquad f(1)=a+b.
$$

Recovering its coefficients requires only subtraction:

$$
a=f(0),\qquad b=f(1)-f(0).
$$

Consequently,

$$
f(r)=f(0)+(f(1)-f(0))r.
$$

No division is needed. This works even modulo 4, where 2 has no multiplicative inverse.

For example, given $f(0)=1$ and $f(1)=3$,

$$
f(3)=1+(3-1)3=3\pmod 4.
$$

`linear-reconstruction` proves this identity over any commutative ring. `linear-interpolation` proves equivalence with the Lagrange formula.

Proofs [Ring/Interpolation.agda](../src/Ring/Interpolation.agda).

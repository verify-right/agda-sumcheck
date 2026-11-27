# Uniqueness and the general verifier

## Why node values determine a polynomial

Let $p$ have coefficients $p_0,\dots,p_d$ and vanish at nodes $x_0,\dots,x_d$ whose differences $x_i-x_j$ are units. Synthetic division by the monic $X-x_0$ gives

$$
p = (X-x_0)\,q + p(x_0) = (X-x_0)\,q
$$

with $q$ of $d$ coefficients. At every other node, $(x_j-x_0)\,q(x_j)=0$, and multiplying by the inverse of $x_j-x_0$ gives $q(x_j)=0$. By induction $q$ has zero coefficients, hence so has $p$. Applied to $p-q$, two polynomials with equal node values have equal coefficients (`eval-injective`).

No field is needed. In $\mathbb Z/15$ the nodes $0,1,2$ have unit differences, so the argument applies; the nodes $0,3$ do not, and `setup` rejects them. Certified weights supply the units: $w_i\prod_{j\ne i}(x_i-x_j)=1$, so each factor $x_i-x_j$ has inverse $w_i\prod_{k\ne i,j}(x_i-x_k)$ (`unit-differences`).

Together with the node law of [General-degree evaluation form](005_barycentric.md), evaluation and interpolation are inverse (`coefficient-evaluation`).

## Reconstructing circuits

A round circuit that passes the degree check at $d$ normalizes to $d+1$ coefficients. Its node values therefore determine it, and barycentric evaluation of those values reproduces it at every point (`reconstruction`). For $X^2-X^2+X$, represented as two leaves $X^2-X^2$ and $X$, the maximum leaf occurrence count is 4: the check rejects it at $d=1$, and accepts it at $d=4$, where reconstruction returns $r$.

## The general verifier

Each round has a public degree bound and node set. The prover sends values at the nodes; the verifier sums the interpolant over the domain list and continues with its value at the challenge. After $k$ rounds the terminal oracle is

$$
\sum_{z\in\mathrm{domain}^{\,n-k}} p(r_1,\dots,r_k,z).
$$

For z-lean's Example 3, $p=x^2y+z$ over $\{0,1\}$ with bounds $(2,1,1)$ and challenges $(2,3,5)$, the claims are $6,10,8,0$. Stopping after two rounds, the oracle is $p(2,3,0)+p(2,3,1)=12+13=25\equiv 8$.

`verify-representation` states that the evaluation-form verdict equals the symbolic one for every well-formed transcript; `malformed-rejected` covers all others. `honest-complete` shows the honest prover passes when each bound covers its variable's occurrences.

Proofs: [Ring/LagrangeInverse.agda](../src/Ring/LagrangeInverse.agda), [Circuit/Reconstruction.agda](../src/Circuit/Reconstruction.agda), [Circuit/General.agda](../src/Circuit/General.agda), [Circuit/GeneralCompleteness.agda](../src/Circuit/GeneralCompleteness.agda).

Examples: [Modular/GeneralExamples.agda](../src/Modular/GeneralExamples.agda).

Lean counterparts: mathlib's [`Lagrange`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Lagrange.lean) (`eq_interpolate`, over fields) and CompPoly's [Barycentric.lean](https://github.com/Verified-zkEVM/CompPoly/blob/06686e4c70939af82203af21516f8ab8a21a8051/CompPoly/Univariate/Barycentric.lean).

# General-degree evaluation form

A round polynomial $g$ of degree at most $d$ is determined by its values $y_i = g(x_i)$ at $d+1$ distinct nodes $x_0,\dots,x_d$. The verifier receives the values and must compute $g(0)+g(1)$ and $g(r)$.

## Lagrange basis in barycentric form

Let

$$
\ell_i(r)=\prod_{j\ne i}(r-x_j),\qquad w_i=\ell_i(x_i)^{-1},\qquad
g(r)=\sum_i y_i\,w_i\,\ell_i(r).
$$

The basis $w_i\ell_i$ is $1$ at $x_i$ and $0$ at every other node, since $\ell_i(x_k)$ contains the factor $x_k-x_k$. So the sum takes the value $y_k$ at $x_k$ (`lagrange-node`). This is the first barycentric form ([DLMF §3.3(i)](https://dlmf.nist.gov/3.3.i)).

Over a commutative ring the differences $x_i-x_j$ need not be invertible. The weights are therefore public data with a certificate $w_i\,\ell_i(x_i)=1$, checked by `certify?`. In $\mathbb F_{17}$ the nodes $0,1,2$ have $\ell_i(x_i)=2,-1,2$, hence weights $9,16,9$.

For $d=1$ with nodes $0,1$ and weights $-1,1$:

$$
g(r)=-y_0(r-1)+y_1 r=y_0+(y_1-y_0)r,
$$

which is the two-point formula of [Linear interpolation over rings](002_ring-interpolation.md) (`lagrange01`). For $d=0$ the interpolant is the constant $y_0$.

## Linear-time evaluation

Each $\ell_i(r)$ is a prefix product $\prod_{j<i}(r-x_j)$ times a suffix product $\prod_{j>i}(r-x_j)$. One pass carries the prefix forward and returns the suffix backward, so evaluation costs $O(d)$ ring operations once weights are known. There is no division by $r-x_i$, so a challenge equal to a node needs no special case. `evalAt-correct` proves equality with the direct formula. These are operation counts, not bit complexity or measurements.

## Verifier and circuit verifier

For Example 3 of z-lean, $p(x,y,z)=x^2y+z$ over $\{0,1\}^3$ sums to 6. The first round sends $g_1(0),g_1(1),g_1(2)=2,4,10$ for $g_1(X)=2X^2+2$. The verifier checks $2+4=6$, receives $r_1=2$, and continues with $g_1(2)=10$.

On the proof side, each tuple is decoded into a sum of basis-term circuits, one leaf per term, each of degree $d$. `verify-equivalent` states that, for a uniform degree bound, the evaluation-form verdict equals the circuit verifier's verdict for every received transcript, including malformed and adversarial ones.

Proofs: [Ring/Lagrange.agda](../src/Ring/Lagrange.agda), [Circuit/Barycentric.agda](../src/Circuit/Barycentric.agda).

Examples: [Modular/BarycentricExamples.agda](../src/Modular/BarycentricExamples.agda).

Lean counterpart: mathlib's [`Lagrange`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Lagrange.lean) proves the node law and the barycentric formulas for polynomials over fields.

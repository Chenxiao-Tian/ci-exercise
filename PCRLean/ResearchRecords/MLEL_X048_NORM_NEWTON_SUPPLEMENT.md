# MLEL-X048 Supplement

## Norm--Newton Ideals and Base-First Toroidal Preparation

**Parent:** MLEL-X048 / FDI-RRF-NNW-FINAL  
**Date:** 2026-08-05  
**Status:** exact diagonal monomial theorem; global wild effectivity open.

Let

```text
A=k[x_1,...,x_r],
B=k[u_1,...,u_r],
x_i=u_i^(e_i),
n=product_i e_i.
```

For a monomial ideal

```text
J=(u^(alpha_1),...,u^(alpha_m))
```

define the norm--Newton ideal on `A` by

```text
NN_f(J)=integralClosure((x^(beta_1),...,x^(beta_m))),
beta_(a,i)=n alpha_(a,i)/e_i.
```

The displayed monomials are the field norms of the upper generators up to units. Their pullbacks are the `n`-th powers of those generators. Consequently

```text
integralClosure(NN_f(J)B)=integralClosure(J^n).
```

Both ideals have Newton polyhedron `n NP(J)`. Their normalized blowups therefore have the same toric fan after base change. A regular refinement of that fan is obtained by a finite sequence of star and barycentric subdivisions, hence by ordinary blowups in regular toroidal strata of the base. After normalized pullback, the upper ideal is principal and monomial.

For a finite marked family, first form the exact joint marked sum of powers and apply `NN_f` to that one monomial ideal. This preserves simultaneous marked permissibility, while passive, source, boundary, contact, and wild-shadow data remain separate colours.

The theorem is base-first: it does not descend the upper regular centre word. Normalization is used only on the comparison space upstairs. The final modification of the original model is the ordinary base blowup word.

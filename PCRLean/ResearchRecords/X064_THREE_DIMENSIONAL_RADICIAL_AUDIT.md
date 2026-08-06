# X064 Three-Dimensional Radicial Audit

## Purpose

This note isolates the load-bearing local calculation from the unified manuscript. It is designed for review independently of the global categorical and compactness layers.

## Local setup

Let

```text
A = k[[x,y,w]],  char(k)=p>0,
X: z^q - f(x,y,w)=0,  q=p^e,
ord(f)>=q.
```

The complete local state contains every Hasse coefficient below the mark `q`, the logarithmic differential row, projectivized contact schemes, Fitting and Tor--Valabrega diagrams, the finite generic cleaning quotient, and labelled exceptional history.

For a point centre `P=(z,x,y,w)`, the base charts are

```text
x-chart: y=x y1, w=x w1, z=x z1,  f_x=x^{-q}f(x,xy1,xw1);
y-chart: x=y x1, w=y w1, z=y z1,  f_y=y^{-q}f(yx1,y,yw1);
w-chart: x=w x1, y=w y1, z=w z1,  f_w=w^{-q}f(wx1,wy1,w).
```

The `z`-chart is disjoint from the multiplicity-`q` strict transform. Every normal Hasse coefficient satisfies the controlled formula

```text
D^[alpha](f_new)=t^(|alpha|-q)(D^[alpha]f)^tot.
```

## Compensated alternatives

On every nonterminal base chart one of the following is strict:

1. bad-support dimension;
2. logarithmic differential corank;
3. projectivized contact height;
4. generic length of the cleaning quotient;
5. active Frobenius exponent;
6. ordered Fitting profile;
7. aged exceptional history.

A residual-order increase is permitted only in alternative 4: an old nonzero leading coefficient becomes a `q`th power after translation and maps to zero after cleaning. The comparison therefore has a nonzero kernel.

## Hauser--Perlega cycle family

For the characteristic-two order-eight family

```text
F0 = x^(8a+4)y^(8b+4)u^(8r)w^(8s-d)
     [ w^d(lambda+u^(2d+6)Q)+x^(d+1)u^(2d+6)A ],
```

with `d>0` even and `A` a unit, the cited point sequence has residual orders

```text
d, d+4, d+3, d+3, d+3, d+2, d+2, d+2,
```

and returns formally with `d` replaced by `d+2`. The first jump kills the degree-`d` class in the generic cleaning quotient. All subsequent chart copies retain the same primitive source identity. Hence the final same-form equation is not gauge-equivalent to the ancestor state.

## Review checklist

An external reviewer should verify, in order:

- the Hasse controlled-transform formula in each chart;
- invariance of the cleaning quotient under permitted cleaning translations;
- nonzero kernel at every residual-order increase;
- non-recreation of the killed class under later charts;
- compatibility with a larger positive-dimensional permissible centre;
- absence of any same-dimensional resolution theorem in the chart proof.

The public X064 theorem asserts that the same finite alternatives hold for the simultaneous multi-root envelope. This generalization remains a principal target for independent review.

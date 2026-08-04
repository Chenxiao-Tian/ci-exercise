# MLEL-X038 Supplement

## A sharp nonzero purification–grading defect and the two-stage RID

Let

```text
R = k[u,x],
N = R,
L = (u*x, x^2).
```

The module `N` has no `u`-power torsion, so purification before grading does
nothing:

```text
H^0_(u)(N)=0.
```

However the degree-zero part of `gr_L(N)` is

```text
A_0 = R/L.
```

The class of `x` is nonzero in `A_0`, while

```text
u*x = 0 in A_0.
```

Therefore

```text
H^0_(u)(gr_L(N)) != 0,
```

and the purification–grading defect is already nonzero in degree zero.  This is
the minimal algebraic model of a new exceptional torsion class created by
passing to the associated graded, despite the original module being
exceptional-torsion-free.

The example proves that the X038 packet cannot be omitted or replaced by the
old ambient torsion alone.

It also clarifies the two-stage total defect.  Even after the old
projective-normal packet has been transported to a blowup chart, there can be:

```text
B = kernel/cokernel of the twisted Rees base-change map,
E = new exceptional torsion created by associated grading.
```

The total RID should carry a finite filtration with `B` and `E` as
subquotients.  The first is a Rees-chart/base-change problem; the second is the
exact torsion quotient proved in the main X038 report.

Both are isomorphism defects which vanish off the exceptional divisor.  Once
coherence of the chart comparison is established, both are finite
exceptional-supported packets and therefore enter the same divisorial descent
compiler.

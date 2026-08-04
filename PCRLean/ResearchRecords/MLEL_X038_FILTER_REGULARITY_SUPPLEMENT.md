# MLEL-X038 Supplement

## Exceptional Filter-Regularity and the Local-Cohomology Form of the Defect

Let the X038 notation be

```text
T = H^0_(u)(N),
A = gr_L(N),
H = gr_L^ind(T),
U = H^0_(u)(A),
E = U/H.
```

The exact identity

```text
E = H^0_(u)(gr_L(N/T))
```

has three useful consequences.

## 1. Filter-regularity criterion

The purified module `N/T` is `u`-power-torsion-free.  Nevertheless its
associated graded can acquire new `u`-torsion.  The interchange defect vanishes
exactly when multiplication by `u` is injective on the complete associated
graded module:

```text
E=0
<-> H^0_(u)(gr_L(N/T))=0
<-> u is gr_L(N/T)-regular.
```

Thus X038 is an exceptional filter-regularity theorem.  The degree formula is a
saturation/filtration-strictness module of Valabrega–Valla type rather than an
unstructured transform discrepancy.

## 2. Local-cohomology derivation

From

```text
0 -> H -> A -> A/H -> 0
```

and the fact that `H` is killed by a power of `u`, one has

```text
H^0_(u)(H)=H,
H^1_(u)(H)=0.
```

The beginning of the local-cohomology sequence therefore gives

```text
0 -> H -> H^0_(u)(A) -> H^0_(u)(A/H) -> 0.
```

Hence

```text
H^0_(u)(A/H)=U/H.
```

This is the sheafification-friendly proof of the purification–grading identity.
For an effective Cartier divisor `E` on a scheme, replace the local equation
`u` by the coherent functor `H^0_E`.

## 3. Multi-exceptional extension

For an SNC exceptional boundary with local equations `u_1,...,u_r`, the
relevant torsion is supported on the union and is locally killed by a monomial

```text
u_1^e_1 * ... * u_r^e_r.
```

The exponent vector is a finite source-labelled debt/contact coordinate.  A
sequential filtration by component-supported local cohomology should reduce the
multi-exceptional packet to finitely many one-component X038 packets and their
overlap extensions.

## 4. Formalization target

The next atomic Lean theorem should not begin with Rees geometry.  It should
formalize the abstract nested-submodule sequence:

```text
H <= U <= A
-> 0 -> U/H -> A/H -> A/U -> 0,
```

followed by a finite-exponent torsion predicate proving

```text
torsion(A/H) = U/H
```

under `H <= torsion(A)` and a uniform exponent killing `H`.  Scheme-level
Artin–Rees and chart transport can then be attached to this certified algebraic
kernel.

The supplement changes no truth status.  The all-chart twisted Rees map,
exceptional-defect elimination, no-recharge, and general resolution remain
open.

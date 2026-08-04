# X038 Counterexample Ledger

## TVC-1 — Cartier identity with supported torsion

```text
A=k[z], J=(z), F=A/(z).
```

`Bl_J(Spec A)` is the identity morphism, but the strict transform of `F` is
zero.  Therefore a morphism-only carrier word loses transform data.

## TVC-2 — Cartier identity without torsion

If multiplication by `z` is injective on `F`, multiplying a centre by the
Cartier factor `z` does not change strict transform.  This is the exact boundary
for Cartier-stable source compression.

## TVC-3 — Transverse nested centres

```text
A=k[x,z], I=(x), K=(x,z), M=A.
```

On the `z`-chart, `x=zs`; after the Cartier twist the old and new conormal
degrees agree and both TVC kernels vanish.

## TVC-4 — Passive crossing-axes module

```text
A=k[x,z], I=(x), K=(x,z), M=A/(z).
```

Every old normal graded piece is `k[z]/(z)`.  The ambient trace blowup separates
the strict transforms of the module and carrier.  The example rejects any rule
that treats the carrier-Cartier identity as an irrelevant step.

## TVC-5 — Tangent curves

```text
(y), (y-x^m) in k[x,y].
```

The anchor contact ideal is `(x^m)`.  One ambient trace blowup changes contact
order from `m` to `m-1`.  Support dimension alone cannot see this progress.

## TVC-6 — Raw base-change kernel

A nonflat chart algebra can make

```text
(I^aM/I^(a+1)M) tensor B -> F_a/F_(a+1)
```

noninjective.  Any proposed common-core theorem must retain the right Tor
kernel rather than assume image filtration commutes with tensor product.

## TVC-7 — Pure saturation failure

Even if the raw base-change map is injective, `F_(a+1)` need not be
`q`-saturated in `F_a`.  Quotient by exceptional power torsion can therefore
create a nonzero left Valabrega kernel.

## TVC-8 — Flat projective tail with bad low degree

Sheafification on the projectivized normal bundle can be flat while a finite
low associated-graded piece is nonflat.  The low transition window cannot be
deleted from the finite packet.

## TVC-9 — Symmetry tie

Two source-labelled flatifier or contact ideals may be exchanged by an
automorphism.  Choosing one anchor or flatifier first breaks functoriality; the
complete finite orbit/groupoid must be retained.

## TVC-10 — Source erasure under cleaning

A normalization or cleaning step can make two presentations look equal while
one still carries nonzero Cartier torsion.  Source compression before the
Cartier-torsion certificate vanishes is forbidden.

## TVC-11 — Missing component

If the chosen good open omits the generic point of a carrier component, a
flatified generically-zero packet need not vanish on that component.  The
flat-kill lemma requires a good open meeting every irreducible component.

## TVC-12 — Singular flatifier centre

Flatification may produce an admissible blowup with singular centre.  Such a
centre cannot enter the final ordinary sequence directly.  Its source ideal
must be principalized and every regular trace subcentre recursively legalized
in smaller carrier dimension.

## Posterior effect

The ledger rejects:

```text
morphism-only domination;
one untyped RID map;
projective-tail-only flatness;
same-dimensional unranked legalization;
Cartier source compression before torsion vanishing.
```

It supports the two-kernel common-core and carrier-dimension induction
architecture, but does not prove its global bridge theorems.

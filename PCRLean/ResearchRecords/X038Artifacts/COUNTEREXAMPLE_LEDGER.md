# X038 Counterexample Ledger

## TVF-1 — Cartier identity with supported torsion

```text
A=k[z], J=(z), F=A/(z).
```

`Bl_J(Spec A)` is the identity morphism, but the strict transform of `F` is
zero. Therefore a morphism-only carrier word loses transform data.

## TVF-2 — Cartier identity without torsion

If multiplication by `z` is injective on `F`, multiplying a centre by the
Cartier factor `z` does not change strict transform. This is the exact boundary
for Cartier-stable source compression.

## TVF-3 — Transverse regular flag

```text
A=k[x,z], I=(x), K=(x,z), M=A.
```

On the `z`-chart, `x=zs`; after the Cartier twist the controlled and strict
carrier ideals agree, and all Tor-Valabrega defects vanish.

## TVF-4 — Passive crossing-axes module

```text
A=k[x,z], I=(x), K=(x,z), M=A/(z).
```

Every old normal graded piece is `k[z]/(z)`. The ambient trace blowup separates
the strict transforms of the module and carrier. The example rejects any rule
that treats the carrier-Cartier identity as an irrelevant step.

## TVF-5 — Tangent curves

```text
(y), (y-x^m) in k[x,y].
```

The anchor contact ideal is `(x^m)`. One ambient trace blowup changes contact
order from `m` to `m-1`. Support dimension alone cannot see this progress.

## TVF-6 — Raw base-change kernel

A nonflat chart algebra can make

```text
(I^aM/I^(a+1)M) tensor B -> gr_J(N)_a
```

noninjective. Any transform theorem must retain `ker(alpha)` rather than assume
image filtration commutes with tensor product.

## TVF-7 — False two-epimorphism cospan

Take

```text
B=k[q,y],
J=(q*y),
L=Sat_q(J)=(y),
N=B.
```

The natural map

```text
J/J^2 -> L/L^2
```

has image `q(L/L^2)` and is not surjective. Hence the initial X038 claim that
the new normal piece and the old chart-pulled piece both epimorphically map to
one common quotient is false. The corrected primitive is

```text
Old --alpha>> gr_J --beta-> gr_L,
```

and must retain both `ker(beta)` and `coker(beta)`.

## TVF-8 — Valabrega intersection defect

Even when `alpha` is injective, one can have

```text
J^a N intersect L^(a+1)N
  strictly larger than J^(a+1)N.
```

Then `ker(beta)` is nonzero. Regularity of the underlying carrier alone does
not remove this module-theoretic defect; the complete owner portfolio must be
Tor-safe and normally flat along the preparatory centre.

## TVF-9 — Saturation-generation defect

The same example `J=(q*y)`, `L=(y)` gives

```text
L^aN / (J^aN + L^(a+1)N) != 0.
```

Thus kernel-only defect tracking is incomplete. The cokernel of `beta` is a
separate finite packet.

## TVF-10 — Projective tail is not necessary for flatifier existence

The complete associated graded module is finite over `gr_I(A)`, and the mixed
packet is finite over the two-ideal mixed-Rees algebra. A construction that
requires a projective tail merely to obtain a flatifier carries avoidable
machinery. Projectivization may still be useful for geometry, but is not a
load-bearing existence device.

## TVF-11 — Flat tail with bad low degree

Although the projective tail is unnecessary for existence, a theorem that
checks only sheafification and ignores the complete affine graded module can
miss a nonflat low degree. The affine normal-cone packet avoids this loss by
retaining all degrees in one finite module.

## TVF-12 — Symmetry tie

Two source-labelled flatifier or contact ideals may be exchanged by an
automorphism. Choosing one anchor or flatifier first breaks functoriality; the
complete finite orbit/groupoid must be retained.

## TVF-13 — Source erasure under cleaning

A normalization or cleaning step can make two presentations look equal while
one still carries nonzero Cartier torsion. Source compression before the
Cartier-torsion certificate vanishes is forbidden.

## TVF-14 — Missing component

If the chosen good open omits the generic point of a carrier component, a
flatified generically-zero packet need not vanish on that component. The
flat-kill lemma requires a good open meeting every irreducible component.

## TVF-15 — Singular flatifier centre

Flatification may produce an admissible blowup with singular centre. Such a
centre cannot enter the final ordinary sequence directly. Its source ideal
must be principalized and every regular trace subcentre recursively legalized
in smaller carrier dimension.

## TVF-16 — Same-dimensional refitting loop

The procedure

```text
flatify packet
-> compute new transform defects
-> enlarge packet
-> flatify again on the same carrier
```

has no established termination rank. The candidate algorithm instead chooses
one centre-enriched flatifier and legalizes each centre recursively in strictly
smaller carrier dimension. The Regular-Flag Legal-Lift Theorem must then kill
the transform defects edge by edge.

## Posterior effect

The ledger rejects:

```text
morphism-only domination;
one untyped direct RID map;
two unconditional epimorphisms to a common quotient;
kernel-only Valabrega tracking;
projective-tail dependence for affine flatifier existence;
same-dimensional unranked legalization;
Cartier source compression before torsion vanishing.
```

It supports the controlled-core factorization, affine normal-cone flatification,
regular-flag legal lift, and carrier-dimension induction architecture. It does
not prove their scheme-level bridge theorems.

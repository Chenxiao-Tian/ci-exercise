# X039 Counterexample Ledger

## NTR-1 — Flatness is essential

Let `A` be a domain and let `M=A/(u)` with `u` nonzero.  The module vanishes at
the generic point but is nonzero and entirely `u`-torsion.  Generic vanishing
alone cannot kill an exceptional defect; carrier flatness is essential.

## NTR-2 — Cartier identity carries transform data

For `A=k[z]`, centre `(z)`, and `F=A/(z)`, the carrier blowup is the identity
morphism while the strict transform is zero.  A morphism-only realization word
loses the pure-transform source and is forbidden.

## NTR-3 — No transitivity without the Hironaka hypotheses

For a nested pair whose relative ideal is not a complete intersection, the
relative normal algebra need not be symmetric or flat.  Normal flatness along
the larger carrier does not by itself imply normal flatness along the smaller
closed subscheme.  X039 transitivity is restricted to regular flags.

## NTR-4 — Regularity of carriers does not replace owner flatness

Even for the coordinate flag `(x) ⊂ (x,z)` in `k[x,z]`, the owner `k[x,z]/(z)`
has nonflat normal pieces along `(x)`.  The regular geometry alone does not
supply passive legality.

## NTR-5 — Preferred-chart reasoning is incomplete

In a regular flag blowup, relative `y`-pivot charts meet the transformed
carrier, while ambient-normal `x`-pivot charts do not.  The proof must establish
this coverage and compare every overlap; checking one preferred chart does not
prove the Regular-Flag Flat-Lift theorem.

## NTR-6 — Same-dimensional refitting loop

The unranked procedure

```text
flatify C
-> compute new transform defects on C
-> enlarge the packet
-> flatify C again
```

may repeat without a strict coordinate.  X039 chooses one immutable
centre-enriched flatifier and legalizes its word centres recursively in
strictly smaller carrier dimension.

## NTR-7 — Singular flatifier centre

General flatification may use a singular centre.  Such a centre cannot enter
the final ordinary sequence.  Its source ideal must be principalized by a
regular word, and every trace subcentre must be jointly legalized before its
ambient blowup.

## NTR-8 — Source compression before torsion vanishing

Two centre words that differ by a Cartier factor can induce different strict
transforms when the owner has Cartier-supported torsion.  Source-labelled
Cartier factors may be compressed only after the zero-torsion certificate.

## NTR-9 — Missing component in flat-kill

A dense open that misses an irreducible component cannot certify vanishing of a
flatified defect there.  The admissible good open must contain every minimal
point, and every component of the transformed regular carrier must meet it.

## NTR-10 — Tangent contact is not passive transitivity

For `(y)` and `(y-x^m)`, the reduced support is a regular point but contact
falls only by `m -> m-1`.  Hironaka normal-flatness transitivity does not replace
the anchor-contact principalization and Cartier cleaning branch.

## NTR-11 — Flatness of the projective tail alone is insufficient

A projective-normal sheaf can be flat while a finite low associated-graded
piece is not.  The carrier flatifier must retain the complete finite Rees
comparison packet, not only its eventual projective tail.

## NTR-12 — Boundary monomial without regularity

If the alleged exceptional equation is a zero divisor on the carrier, a flat
owner need not obtain the required no-recharge conclusion from that equation.
The certificate must state that every boundary factor is Cartier and that the
local exceptional monomial is a base nonzerodivisor.

## Posterior effect

The ledger supports:

```text
one centre-enriched flatifier per raw carrier;
regular-flag Hironaka transitivity after flatness;
flatness as the purification-torsion endpoint;
strict carrier-dimension recursion;
explicit all-chart Regular-Flag Flat-Lift;
source compression only after zero torsion.
```

It rejects morphism-only domination, regularity-only passive safety,
preferred-chart proofs, same-dimensional refitting, and unqualified
normal-flatness transitivity.

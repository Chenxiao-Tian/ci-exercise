# X041 Counterexample Ledger

## HNC-1 — A projective tail can miss a bad low degree

A graded module may have a flat eventual tail while `G_0` or another finite low
piece is nonflat.  Flatification of the tail sheaf alone does not prove normal
flatness.  The homogenized packet avoids this loss because the affine chart
`D_+(z)` recovers the complete module `G`, including every low degree.

## HNC-2 — An arbitrary cutoff is not canonical

A Serre comparison bound chosen from one finite presentation need not be
invariant under a new presentation or under base change.  The total-degree
homogenization `G[z]` uses no cutoff and is defined directly from the canonical
graded module.

## HNC-3 — Strict transform depends on the centre

```text
A=k[t], J=(t), F=A/(t).
```

The blowup in the Cartier ideal is the identity morphism, but the strict
transform of `F` is zero.  Hence strict transform cannot be reconstructed from
the bare modification morphism.

## HNC-4 — Distinguished word ideal versus arbitrary equivalent ideal

A finite centre word may be represented by a distinguished composite blowup
ideal with the correct union-of-centres certificate.  Stacks Project, Divisors,
Lemma 31.34.6 identifies its strict transform with the iterated one.  Replacing
this ideal by an arbitrary ideal defining an isomorphic blowup is forbidden
unless the Cartier-torsion boundary of Lemma 31.34.5 is certified.

## HNC-5 — Flatness is the exact tail-persistence boundary

Once a source strict transform is flat over the base, every further strict
transform along a blowup is its pullback.  Without flatness, new exceptional
power torsion can appear and a common refinement need not preserve the source
transform.

## HNC-6 — Positive-characteristic functorial flatifier centres may be singular

Rydh's theorem gives a functorial blowup sequence for proper coherent sheaves
under flat base change in arbitrary characteristic, but smooth centres are
asserted only in characteristic zero.  The source word therefore cannot enter
the final resolution sequence directly; lower-dimensional regular realization
is still required.

## HNC-7 — Regular flag without Tor safety

Normal flatness of `gr_C(M)` alone does not automatically make every filtration
sequence exact after the ambient blowup chart base change.  The Regular-Flag
Flat-Lift theorem must retain the separate Tor-safety hypotheses for the Rees
filtration.

## HNC-8 — Relevant and irrelevant blowup charts

For

```text
I_C=(x_1,...,x_r),
I_D=(x_1,...,x_r,y_1,...,y_s),
```

the `x_i`-pivot charts do not meet the strict transform of `C`.  A proof that
checks only one preferred `y_j` chart or incorrectly includes `x_i` charts in
the carrier atlas has incomplete coverage.

## HNC-9 — Missing component destroys support descent

If the maximal flat open does not contain the generic point of one component of
`C`, an admissible source ideal can vanish generically on that component and
its support need not have smaller dimension.  Componentwise generic flatness is
part of the source certificate.

## HNC-10 — Flatifier principalization without the normal portfolio

Principalizing the common source ideal on `C` while omitting the affine normal
module may select regular centres that destroy the filtration exactness needed
for ambient transport.  The entire normal/log/source/debt portfolio must be
enrolled in the lower-dimensional state.

## HNC-11 — Same-dimensional re-flatification loop

```text
flatify -> compute new transform defect -> enlarge packet -> flatify again
```

has no established strict rank.  X041 chooses the canonical flatifier once and
resolves its support in lower dimension; every nested carrier call has smaller
dimension.

## HNC-12 — Source relabelling after common refinement

Even when final modules are isomorphic, cloning or renaming one source can
recharge passive or debt budgets.  Centre-exact word IDs and lineage maps must
survive all charts and common refinements.

## Posterior effect

The ledger rejects projective-tail-only flatness, arbitrary cutoff packets,
bare modification semantics, singular flatifier centres as final centres,
Regular-Flag transport without Tor safety, missing-component admissibility,
and same-dimensional re-flatification.  It supports canonical homogenized
projective completion, Rydh functorial source words, centre-exact strict-
transform transitivity, product-ideal cofinality, lower-dimensional full-
portfolio realization, and all-chart Regular-Flag Flat-Lift.  The scheme-level
bridges remain unproved in this program.

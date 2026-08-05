# X040 Counterexample Ledger

## CFT-0 — Hidden flatifier choice

An existence theorem can produce two different admissible flatifier words for
the same carrier packet.  They may have different source ideals and ambient
trace supports.  Taking a symmetry product after selecting one word does not
make the selection functorial.  The source word must be produced by a
functorial flatification theorem from a canonical finite packet.

## CFT-0B — Projective tail alone misses low degrees

A coherent projective-normal tail sheaf can be flat while a finite low
associated-graded piece is nonflat.  The functorial packet must include bounded
irrelevant torsion, a finite low/transition window, and the proper tail with
comparison maps.  Conversely, the affine normal-cone packet is sufficient for
existence but does not by itself choose a functorial flatifier.

## CFT-1 — Crossing preparatory source

```text
X=Spec k[x,y,z], C1=V(x), C2=V(y), D=V(x,z) subset C1.
```

`D intersect C2` is the origin, while neither `D subset C2` nor `C2 subset D`.
Independent maximal-carrier preparation is not closed under ambient
interaction.

## CFT-2 — Minimal finite crossing model

```text
D={0,1}, C={1,2}, E=D intersect C={1}.
```

The sources are non-disjoint and non-nested.  Enrolling `E` creates a deeper
stratum contained in both.  This is formalized in
`CrossCarrierCompletionModel.lean`.

## CFT-3 — Singular common product centre

Even when every source support is regular, the union cut out by their product
can be singular along intersections.  The product ideal is a common
modification target, not a permissible centre.  It must be realized by
lower-dimensional relative principalization.

## CFT-4 — Missing generic component

If a flatifier ideal is not the unit at the generic point of one carrier
component, its support need not have smaller dimension.  Componentwise
admissibility is required for the dimension-strict recursion.

## CFT-5 — Morphism-only common refinement

A common refinement morphism does not determine source-pure transforms when a
source has Cartier-supported torsion.  Every factor retains its centre label and
zero-torsion certificate.

## CFT-6 — Product ideal without full portfolio

Principalizing the common product while forgetting passive owners or boundary
strata can use a regular centre that is active-permissible but passive-unsafe or
non-SNC.  The lower-dimensional recursive input must carry the complete
portfolio.

## CFT-7 — Flatness without Cartier regularity

Pullback of a flat source transform is safe under further Cartier exceptional
factors.  If the alleged factor is a zero divisor on the transformed base, the
no-recharge argument fails.

## CFT-8 — Arrangement completion without deepest-first order

A clean crossing pair need not be disjoint or nested before its intersection is
processed.  Serializing a raw source before the deeper intersection reintroduces
a clean-square transport problem.

## CFT-9 — New passive charge from relabelling

Intersection completion, chart restriction, or source relabelling cannot create
a new maximal-carrier passive obligation.  Any such charge is a hidden reset
unless accompanied by a genuine outer birth witness.

## CFT-10 — Arbitrary source ordering

A finite symmetry orbit of carrier flatifiers may have no invariant first
source.  The product ideal is invariant; arbitrary concatenation is not.

## Posterior effect

The ledger rejects hidden nonfunctorial flatifier selection, projective-tail-only
flatness, independent flatifier concatenation, direct singular product centres,
morphism-only domination, noncomponentwise admissibility, and uncompleted
crossing serialization.  It supports a canonical finite proper Rees-Serre
packet, functorial component flatifiers, one source-labelled common trace
product, lower-support-dimensional relative principalization, finite source
arrangement completion, and nested-only wonderful persistence.  It does not
prove their scheme-level bridge theorems.

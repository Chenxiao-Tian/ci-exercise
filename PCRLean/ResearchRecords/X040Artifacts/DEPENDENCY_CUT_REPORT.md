# X040 Dependency-Cut Report

## Root-facing position

X040 refines the critical path

```text
CTR-13 -> HER-03/HER-05 -> HER-15 -> TRM-12 -> GLB-07/08 -> FIN-01.
```

The parent X039 cut contained independent maximal-carrier flatifier realization,
Regular-Flag Flat-Lift, and no-reset.  Two failures are now explicit:

1. preparatory centres attached to different maximal carriers can cross;
2. an arbitrary choice of one admissible flatifier per carrier is not made
   functorial merely by multiplying the chosen source orbit afterwards.

## Deleted edges

```text
prepare every maximal carrier independently
-> concatenate the finite words
-> all maximal carriers remain legal;

choose one flatifier per carrier
-> symmetrize the chosen ideals
-> obtain a functorial source product.
```

The first edge fails by the crossing-centre example.  The second retains a
hidden nonfunctorial choice.

## Replacement cut

```text
CFT-0  FUNCTORIAL_REES_SERRE_PACKET
       encode the complete affine associated-graded portfolio by a finite
       low/transition packet and proper projective-normal tail, with exact
       comparison and base-change certificates;

CFT-1  FUNCTORIAL_CARRIER_FLATIFIER_SOURCE
       apply functorial proper flatification to the intrinsic maximal-carrier
       groupoid and obtain equivariant component source words;

CFT-2  COMMON_SOURCE_PRODUCT
       compress each functorial word to one immutable source ideal, lift
       ambiently, and form the finite invariant product;

CFT-3  LOWER_SUPPORT_REGULAR_REALIZATION
       use the full lower-dimensional relative principalization theorem to
       realize the common product by regular jointly legal centres;

CFT-4  SOURCE_PURE_TRANSFORM_COMMON_REFINEMENT
       prove that flat source strict transforms pull back through the common
       refinement without additional Cartier torsion;

CFT-5  SOURCE_ARRANGEMENT_COMPLETION
       include every trace support and intersection, route bad strata to
       support-thickness recursion, and serialize clean strata deepest first;

CFT-6  REGULAR_FLAG_FLAT_LIFT
       transport the complete portfolio in the remaining nested case;

CFT-7  SOURCE_CONSERVATIVE_NO_RESET
       prevent flatification, intersection completion, and wonderful
       serialization from creating new passive sources or changing identities.
```

## Standard versus project-specific burden

Standard inputs:

```text
functorial flatification of proper morphisms by admissible blowups;
composition of finite blowups is a blowup;
product ideals give finite common refinements;
strict transform of a carrier is its induced blowup;
flat strict transform is pullback;
Hironaka normal-flatness transitivity;
minimal intersection-closed stratum is disjoint or nested.
```

Open project edges:

```text
finite functorial Rees-Serre comparison for the full graded portfolio;
semantic passage from proper functorial flatification to immutable source ideals;
full-portfolio lower-dimensional principalization of the common product;
source-labelled strict-transform comparison through the common refinement;
Regular-Flag Flat-Lift on every chart and overlap;
source/owner/boundary/debt no-reset;
outer birth accounting and global serialization.
```

## Information gain

The corrected architecture removes:

```text
hidden flatifier selection;
arbitrary ordering of maximal-carrier flatifiers;
independent cross-carrier interaction checks;
one passive budget per intersection stratum;
a general clean-square transport theorem during wonderful serialization.
```

The highest-information next task is now

```text
CFT-0/CFT-1
  finite functorial Rees-Serre packet and canonical source word,

CFT-4
  exact source-pure transform through the product refinement,

CFT-6
  nested all-chart Regular-Flag Flat-Lift,

CFT-7
  source-conservative no-reset.
```

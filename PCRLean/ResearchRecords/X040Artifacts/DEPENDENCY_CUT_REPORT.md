# X040 Dependency-Cut Report

## Root-facing position

X040 refines the critical path

```text
CTR-13 -> HER-03/HER-05 -> HER-15 -> TRM-12 -> GLB-07/08 -> FIN-01.
```

The parent X039 cut contained independent maximal-carrier flatifier realization,
Regular-Flag Flat-Lift, and no-reset.  The crossing-centre counterexample shows
that independent realization is not closed under ambient interaction.

## Deleted edge

```text
prepare every maximal carrier independently
-> concatenate the finite words
-> all maximal carriers remain legal.
```

This edge is false without completing intersections between preparatory source
centres and the other carriers.

## Replacement cut

```text
CFT-A  COMMON_SOURCE_PRODUCT
       compress each flatifier to one source ideal, lift ambiently, and form
       the finite symmetry-invariant product;

CFT-B  LOWER_SUPPORT_REGULAR_REALIZATION
       use the full lower-dimensional relative principalization theorem to
       realize the common product by regular jointly legal centres;

CFT-C  SOURCE_PURE_TRANSFORM_COMMON_REFINEMENT
       prove that flat source strict transforms pull back through the common
       refinement without additional Cartier torsion;

CFT-D  SOURCE_ARRANGEMENT_COMPLETION
       include every trace support and intersection, route bad strata to
       support-thickness recursion, and serialize clean strata deepest first;

CFT-E  REGULAR_FLAG_FLAT_LIFT
       transport the complete portfolio in the remaining nested case;

CFT-F  SOURCE_CONSERVATIVE_NO_RESET
       prevent intersection completion and wonderful serialization from
       creating new passive sources or changing identities.
```

## Standard versus project-specific burden

Standard inputs:

```text
composition of finite blowups is a blowup;
product ideals give finite common refinements;
strict transform of a carrier is its induced blowup;
flat strict transform is pullback;
Hironaka normal-flatness transitivity;
minimal intersection-closed stratum is disjoint or nested.
```

Open project edges:

```text
full-portfolio lower-dimensional principalization of the common product;
source-labelled strict-transform comparison through the common refinement;
Regular-Flag Flat-Lift on every chart and overlap;
source/owner/boundary/debt no-reset;
outer birth accounting and global serialization.
```

## Information gain

The common product removes:

```text
arbitrary ordering of maximal-carrier flatifiers;
independent cross-carrier interaction checks;
one passive budget per intersection stratum;
a general clean-square transport theorem during wonderful serialization.
```

The highest-information next task is `CFT-C + CFT-E`: exact source-pure
transform through the product refinement and the nested all-chart flat-lift.

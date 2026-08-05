# MLEL-X041 / SCD-DSW

## Saturated Cartier Décalage, Divisor-Word Compression, and Source-Word Realization

**Chinese title:** 饱和 Cartier 降阶、除子词压缩与来源词实现  
**Protocol:** `PCR-FRACTAL-PROOF-LEAN 1.0 / MLEL-A003-FPE-EDGE`  
**Seed architecture:** `MLEL-D001 / FCPP-ATLAS`  
**Accepted mathematical parent:** `MLEL-M004 / HMC-SCCD` (restricted)  
**Experimental parent:** `MLEL-X040 / CFT-ACN`  
**Primary refinement:** `X040-G7 -> X040-G13 -> X040-G16`, hence `HER-03/HER-15 -> TRM-12`  
**Class:** `EXPERIMENTAL_CANDIDATE_GRAPH_REFINEMENT / NO THEOREM PROMOTION`  
**Date:** 2026-08-04 ET / 2026-08-05 UTC  
**Global status:** `OPEN_GAP`

---

# 0. Executive verdict

X040 retained the complete centre-enriched source word because a strict
transform depends on its centres and not only on the final modification
morphism.  That correction is indispensable.  The present round identifies a
smaller invariant that can replace the word **after the exceptional divisor and
its torsion budget have been retained**.

For an effective Cartier equation `f`, the Berthelot--Ogus décalage satisfies

```text
eta_f eta_g = eta_(f*g),
H^i(Leta_f M) = f^i (H^i(M)/H^i(M)[f]).
```

Thus one décalage layer removes one Cartier-torsion layer; `N` iterations remove
`f^N`-torsion.  On a coherent packet, exceptional power torsion stabilizes at a
finite exponent.  Consequently a centre word has a finite downstream capsule

```text
(final modification,
 total exceptional Cartier divisor,
 saturation exponent,
 saturated Leta transform,
 source/owner/debt/boundary lineage).
```

At degree zero, successive saturation by a divisor word is exactly one
saturation by the product equation and is independent of the order of the
components.  This exact algebra is written in Lean in the present round.

The decisive proposed theorem is a **Décalage--Strict-Transform Word Theorem**:
actual iterated passive strict transform equals the degree-zero cohomology of a
finite saturated `Leta` transform along the total source exceptional divisor.
For active/contact data, the same operator is used with a prescribed finite
number of layers rather than full saturation; the remaining layer count is the
contact/debt coordinate.

The theorem would turn Source-Word Realization and exceptional no-reset into a
factorization-independent divisor statement.  It is not yet proved.

---

# 1. Why the final morphism is insufficient but the total divisor may suffice

X037 supplied the minimal no-go:

```text
A=k[z], J=(z), F=A/(z).
```

The blowup in the effective Cartier ideal `J` is the identity morphism, but the
strict transform of `F` is zero.  The same identity morphism presented with an
empty centre leaves `F` unchanged.  Hence a modification morphism alone loses
transform data.

The two presentations have different exceptional source divisors:

```text
Cartier-centre presentation: D=V(z),
empty-centre presentation:   D=empty.
```

The conjectural minimal downstream object is therefore not the bare morphism,
but the morphism together with the total source-labelled exceptional Cartier
divisor and the finite torsion exponent.

---

# 2. The décalage identities

Let `A` be a ring, let `f` be a nonzerodivisor, and let `M` be an object of
`D(A)` represented by a complex of `f`-torsion-free modules.  The
Berthelot--Ogus operator gives

```text
H^i(Leta_f M)
  ~= f^i (H^i(M)/H^i(M)[f]).
```

If `f` and `g` are nonzerodivisors on all terms, then

```text
eta_f eta_g M = eta_(f*g) M.
```

It also commutes with flat base change.  These are standard results in the
Berthelot--Ogus/Stacks décalage theory.

By induction one expects the normalized formula

```text
H^i((Leta_f)^N M)
  ~= f^(N*i) (H^i(M)/H^i(M)[f^N]).
```

For `i=0` this is simply

```text
H^0((Leta_f)^N M)=H^0(M)/H^0(M)[f^N].
```

If `N` is at least the exceptional-torsion exponent, this is the quotient by
all sections supported on `V(f)`.

For a finite divisor word with local equations `f_1,...,f_r`, repeated
application collapses to the product equation

```text
F=f_1*...*f_r.
```

At degree zero the same statement is the elementary saturation law

```text
Sat_(f*g)(P)=Sat_g(Sat_f(P)).
```

The exact module statement and finite-word permutation invariance are formalized
in `PowerSaturationProduct.lean` and `DivisorWordSaturation.lean`.

---

# 3. Strict transform as stabilized décalage

Let `pi:Y->X` be a centre-enriched finite word of blowups and let `E_pi` be the
sum of all source-labelled exceptional divisors on `Y`, with ideal
`I_pi=O_Y(-E_pi)`.  Let `F` be a finite owner module on `X`.

The candidate theorem is

```text
F^(strict,pi)
  ~= H^0((Leta_(I_pi))^N Lpi^*F)
```

for every `N` at least the power-torsion exponent of `H^0(Lpi^*F)` along
`E_pi`.

The statement is stronger than the observation that a final flat strict
transform pulls back through later blowups.  It compares different
factorizations of the same common refinement, provided they carry the same
source-divisor capsule.

The expected proof has four parts:

```text
SCD-1  one affine blowup chart:
       strict transform is tensor product modulo exceptional power torsion;

SCD-2  one Cartier divisor:
       stabilized degree-zero Leta equals quotient by exceptional power
       torsion;

SCD-3  composition:
       eta_f eta_g = eta_(f*g) identifies iterated words with the total
       divisor;

SCD-4  descent:
       the total divisor, saturation exponent, and derived comparison glue on
       overlaps and commute with smooth/etale base change.
```

`SCD-1` is standard strict-transform algebra.  `SCD-2/3` are standard plus the
finite Noetherian exponent.  `SCD-4`, especially arbitrary nonflat common
refinements and the source ledger, is the project-specific bridge.

---

# 4. Contact and passive transform are two budgets of one operator

The tangent-curve model becomes transparent.  Let

```text
M=A/(u^m).
```

One décalage layer gives the cohomological model `A/(u^(m-1))`; after `m`
layers the exceptional torsion vanishes.  Thus:

```text
passive strict transform:
  apply enough layers to reach saturation;

active/contact controlled transform:
  apply the prescribed number of layers determined by the mark;

remaining contact/debt:
  the unconsumed décalage height.
```

This does not identify active and passive semantics.  It gives a common
Cartier-layer calculus with two different stopping rules.  The distinction is
part of the certificate.

---

# 5. Canonical good-triple preparation

For a perfect complex `P` and an effective Cartier divisor `D`, the Stacks
blowing-up-complexes construction produces a unique admissible blowup such that
all intrinsic décalage ideals become invertible.  In the resulting good triple,
`Leta_D P` remains perfect and commutes with arbitrary pullback.  Locally the
blowup is in the finite product of intrinsic ideals attached to a finite free
representative; the construction has a universal property and glues without a
coordinate choice.

This suggests the following source realization strategy.

```text
1. Construct the functorial proper flatifier source word of X040.
2. On its final model retain the total source exceptional divisor E.
3. Package every finite passive/log/source comparison as one perfect complex P.
4. Apply the canonical good-triple blowup for (E,P), if nontrivial.
5. Replace the downstream source word by the saturated décalage capsule
   (Y,E,N,Q,lineage).
6. Pull capsules to a common refinement using good-triple base change.
```

If the final source modules are finitely presented and flat, they are locally
free, so their degree-zero capsules are already torsion free.  The good-triple
step is needed for the complete comparison complex and for nonflat common
refinements, not to re-flatify a flat module.

The canonical blowup may have singular centres in positive characteristic.  As
in X040, its modification ideal is passed to the lower-dimensional
full-portfolio regular realization compiler; its centre/divisor payload is not
discarded.

---

# 6. Revised source-word package

The X040 package

```text
(source word, final strict transforms, exceptional lineage,
 composite modification ideal)
```

is refined to

```text
SCD source capsule = (
  final source modification Y->C,
  complete centre word until the comparison theorem is proved,
  total source exceptional divisor E,
  finite saturation exponent N,
  perfect comparison complex P,
  Q=(Leta_E)^N Lpi^*P with degree twists,
  final flat H^0 owner transforms,
  source/owner/boundary/debt lineage,
  good-triple and base-change certificates,
  one separate ideal representing only the modification morphism
).
```

After the Décalage--Strict-Transform Word Theorem is established, the full word
can be removed from downstream interfaces and retained only in the audit
ledger.  Before that theorem is established, compression is forbidden.

---

# 7. Corrected common-refinement chain

```text
intrinsic maximal-carrier groupoid
-> finite functorial Rees-Serre flatifier words
-> SCD capsules on the final source models
-> composite modification ideals only for common-refinement geometry
-> canonical common trace product
-> lower-support-dimensional regular realization
-> pullback of good SCD capsules to the common model
-> Décalage--Strict-Transform Word comparison
-> simultaneous maximal-carrier passive flatness
-> source-arrangement completion
-> disjoint/nested wonderful word
-> Regular-Flag Flat-Lift as the one-layer local form of SCD transport
-> source-conservative all-chart reentry.
```

The new architecture keeps X040's common-product and symmetry advantages while
replacing a difficult word-by-word strict-transform comparison by one total-
divisor derived comparison.

---

# 8. Candidate factorization-independence theorem

> **Saturated Cartier Décalage Source-Word Theorem.**  Let `pi:Y->X` be a finite
> centre-enriched word of ordinary blowups, let `E_pi` be its total
> source-labelled exceptional Cartier divisor, and let `P` be a perfect source
> packet with coherent cohomology.  There exists a finite exponent `N` such
> that the normalized iterated décalage `(Leta_(E_pi))^N Lpi^*P` has cohomology
> obtained from `Lpi^*P` by quotienting every cohomology module by its full
> exceptional power torsion.  The construction is independent of the ordering
> and parenthesization of the divisor components, commutes with flat base
> change, and—after the canonical good-triple preparation—commutes with arbitrary
> pullback.
>
> For a module in degree zero, its `H^0` is the actual iterated strict transform
> along `pi`.  For a marked contact packet, one prescribed décalage layer is the
> controlled exceptional division and strictly lowers the remaining contact
> height.  The comparison is compatible with overlaps, source labels, owners,
> boundary, and debt.

The theorem is not proved.  The degree-zero saturation algebra and rank
arithmetic are written in Lean; the derived, scheme, word, and naturality edges
remain open.

---

# 9. Exact frontier after X041

```text
X041-G1   DERIVED_ITERATION_FORMULA_FOR_LETA_POWERS
X041-G2   UNIFORM_TORSION_EXPONENT_FOR_FINITE_COHOMOLOGY_PACKET
X041-G3   SATURATED_LETA_CAPSULE_AND_DEGREE_TWISTS
X041-G4   ONE_BLOWUP_STRICT_TRANSFORM_EQUALS_SATURATED_H0_LETA
X041-G5   TOTAL_EXCEPTIONAL_DIVISOR_OF_A_CENTRE_WORD
X041-G6   WORD_COMPOSITION_VIA_ETA_PRODUCT_IDENTITY
X041-G7   OVERLAP_AND_SMOOTH_BASE_CHANGE_OF_SCD_CAPSULES
X041-G8   GOOD_TRIPLE_PREPARATION_FOR_THE_COMPLETE_SOURCE_COMPLEX
X041-G9   ARBITRARY_PULLBACK_AFTER_GOOD_TRIPLE
X041-G10  SOURCE_WORD_REALIZATION_ON_A_COMMON_REFINEMENT
X041-G11  ACTIVE_CONTROLLED_LAYER_VERSUS_PASSIVE_SATURATION
X041-G12  CONTACT_HEIGHT_STRICT_DESCENT
X041-G13  REGULAR_FLAG_FLAT_LIFT_AS_ONE_LAYER_SCD_THEOREM
X041-G14  SOURCE_CONSERVATIVE_SCD_NO_RESET
X041-G15  COMMON_TRACE_PRODUCT_WITH_SCD_CAPSULES
X041-G16  GLOBAL_SCD_CAPSULE_DESCENT
X041-G17  DIMENSION_TORSION_SOURCE_DEBT_SCC_RANK
X041-G18  UNIVERSAL_ACTUAL_JOINTLY_LEGAL_CENTRE_WORD
```

The highest-information cut is

```text
X041-G1/G3/G4
  derived saturation and one-step strict-transform comparison,

X041-G8/G9/G10
  good-triple preparation and common-refinement source realization,

X041-G13/G14
  Regular-Flag Flat-Lift and all-chart no-reset.
```

---

# 10. Lean source written in this round

```text
PowerSaturationProduct.lean
DivisorWordSaturation.lean
SaturatedSourceCapsule.lean
DecalageSourceRank.lean
X041SaturatedDecalageIndex.lean
X041SaturatedDecalageIndexAudit.lean
```

The exact source proves only:

1. relative power saturation is extensive, monotone, and idempotent;
2. saturation by a product equals successive saturation;
3. finite divisor-word saturation equals saturation by the product and is
   invariant under permutation;
4. a finite exponent certificate computes the saturated submodule;
5. source-capsule quotients are invariant under divisor-word permutation;
6. the carrier-dimension/torsion-height/source-count/debt rank is well founded.

It does not formalize `Leta`, perfect complexes, blowups, strict transforms,
functorial flatification, good triples, common refinements, regular centres,
hereditary reentry, termination, or resolution.

---

# 11. Annals-series maximum-likelihood estimate

The total-divisor décalage formalism adds a derived transform chapter but is
expected to compress repeated Cartier-trace, contact, and source-word
comparisons.  The modal form remains six papers with a new central estimate of
**564 dense Annals/AMS-equivalent pages**.

| Paper | Maximum-likelihood title | Pages |
|---:|---|---:|
| I | Intrinsic Frobenius-Hasse States, Affine Conormal Packets, and Projectivity Discriminants | 90 |
| II | Common Trace Products, Anchor-Contact Ideals, and Wonderful Actual-Centre Synthesis | 120 |
| III | Functorial Flatification, Saturated Cartier Décalage, and Hereditary Reentry | 144 |
| IV | Décalage Height, Source-Debt Causality, and Dimension-Strict Termination | 84 |
| V | Global Descent, Symmetry-Compatible Serialization, and Principalization | 78 |
| VI | Functorial Resolution, Counterexample Closure, and Lean Reproducibility | 48 |
|  | **Total** | **564** |

A one-volume editorial edition with theorem-interface cards, divisor/source
capsules, complete chart algebra, proof DAG, counterexample atlas, and
paper-to-Lean map is estimated at `612--652` physical pages.

Subjective planning weights:

```text
six papers                                   0.62
seven papers, splitting derived transform    0.23
five papers after consolidation              0.09
other                                        0.06
```

These are research-planning weights, not calibrated probabilities.

---

# 12. Truth boundary

```text
ROUND_ID                                      = MLEL-X041 / SCD-DSW

ETA_PRODUCT_IDENTITY_IDENTIFIED               = standard math
COHOMOLOGY_TORSION_LAYER_FORMULA_IDENTIFIED   = standard math
GOOD_TRIPLE_UNIVERSAL_BLOWUP_IDENTIFIED       = standard math
POWER_SATURATION_PRODUCT_LEAN_WRITTEN         = true
DIVISOR_WORD_INVARIANCE_LEAN_WRITTEN          = true
FINITE_SOURCE_CAPSULE_LEAN_WRITTEN            = true
DECALAGE_RANK_LEAN_WRITTEN                    = true

DERIVED_SATURATION_THEOREM_PROVED             = false
STRICT_TRANSFORM_WORD_COMPARISON_PROVED       = false
GOOD_TRIPLE_SOURCE_PACKET_PROVED              = false
COMMON_REFINEMENT_SOURCE_REALIZATION_PROVED   = false
REGULAR_FLAG_FLAT_LIFT_PROVED                 = false
SOURCE_CONSERVATIVE_NO_RESET_PROVED           = false
UNIVERSAL_JOINTLY_LEGAL_CENTRE_WORD_PROVED    = false

X041_CLEANROOM_GREEN                          = false
NEW_DECLARATIONS_PROMOTED                     = false
CERTIFIED_GRAPH_CHANGED                       = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED            = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION    = false
FORMAL_GLOBAL_STATUS                          = OPEN_GAP
```

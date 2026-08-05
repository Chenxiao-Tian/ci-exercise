# MLEL-X040 / CFT-ACN

## Common Flatifier Traces, Admissible Common Refinement, and Nested-Only Persistence

**Chinese title:** 共同平坦化迹、许可共同细化与仅嵌套持久性  
**Protocol:** `PCR-FRACTAL-PROOF-LEAN 1.0 / MLEL-A003-FPE-EDGE`  
**Seed architecture:** `MLEL-D001 / FCPP-ATLAS`  
**Accepted mathematical parent:** `MLEL-M004 / HMC-SCCD` (restricted)  
**Experimental parent:** `MLEL-X039 / NTR-RFL`  
**Primary D001 refinement:** `CTR-07/12/13 -> HER-02/03/05 -> HER-15`, with direct return edges to `TRM-02/11/12` and `GLB-03/04`  
**Class:** `COUNTEREXAMPLE-DRIVEN CANDIDATE-GRAPH COMPRESSION / NO THEOREM PROMOTION`  
**Date:** 2026-08-04 ET  
**Global status:** `OPEN_GAP`

---

# 0. Executive verdict

X039 showed that normal flatness is transitive down regular flags and that a
prepared carrier does not acquire new exceptional power torsion.  It therefore
reduced passive preparation of a clean arrangement to its inclusion-maximal
carriers.

A hidden interaction remained.  The lower-dimensional flatifier centre chosen
inside one maximal carrier can meet another maximal carrier without being
disjoint from or contained in it.  Independent carrier-by-carrier preparation
therefore does not define a closed ambient algorithm.

The X040 correction is to aggregate all finite source-labelled ambient trace
ideals into one product ideal

```text
K_common = product_lambda K_lambda.
```

The blowup of the product is the standard common refinement of all source
blowups.  Since every flatifier is componentwise admissible, the support of the
common product has strictly smaller dimension than the maximal carriers.  The
strong relative principalization theorem in lower dimension can therefore
replace the singular common blowup by a finite word of ordinary blowups in
regular, recursively jointly legal centres.

The final word factors through every source flatifier simultaneously.  Flat
strict transforms pull back to flat strict transforms, so all maximal carriers
are prepared in one symmetry-invariant macro.  Intersections of the trace
supports are enrolled in one finite arrangement completion.  After deepest
strata are processed, every remaining interaction is disjoint or nested; the
only module-transport theorem still required is the nested Regular-Flag
Flat-Lift theorem.

The principal new chain is

```text
finite orbit of carrier flatifiers
-> ambient trace ideals
-> one symmetry-invariant product ideal
-> lower-support-dimensional relative principalization
-> regular jointly legal common-refinement word
-> factorization through every flatifier
-> simultaneous maximal-carrier flatness
-> Hironaka transitivity to every stratum
-> deepest-first disjoint-or-nested wonderful persistence.
```

General positive-characteristic resolution is not proved.

---

# 1. Exact X039 validation inherited by this round

The repaired X039 exact-snapshot clean room is green.

```text
PR                         = 58, draft, open, unmerged
base SHA                   = f2341ba202787f103c2d53a5fcf785f37fbe7122
head SHA                   = 9e928baea472515b9bcea2c43e707a759bf2aff0
workflow run               = 30965674511
job                        = 92178972043
conclusion                 = success
artifact                   = 8914697081
artifact digest            = sha256:1c740d3df364787ff7b66e3b6443a7222025940f35d0e348f59a2a71d3a9239a
```

The successful slice certifies only the abstract Hironaka tensor-flatness
compiler, finite-owner compilation, exceptional no-recharge leaf, and nested
rank arithmetic.  It does not prove the sheafified Hironaka comparison,
Regular-Flag Flat-Lift, common-flatifier realization, no-reset, termination, or
resolution.

---

# 2. Counterexample to independent maximal-carrier preparation

Let

```text
X = Spec k[x,y,z],
C_1 = V(x),
C_2 = V(y).
```

The two regular maximal carriers meet cleanly in the `z`-axis.  Suppose one
flatifier word for `C_1` begins with the regular centre

```text
D = V(x,z) subset C_1.
```

Then

```text
D intersection C_2 = V(x,y,z)
```

is nonempty, but

```text
D is not contained in C_2,
C_2 is not contained in D.
```

Blowing up `D` ambiently restricts on `C_2` to the blowup of `C_2` in the
origin.  Thus a preparatory step for `C_1` changes `C_2`; it is not covered by
either the disjoint case or the nested flag `D subset C_2`.

This rejects the naive compiler

```text
prepare each maximal carrier independently
-> concatenate the words.
```

The minimal finite-set model `{0,1}` and `{1,2}` with new intersection `{1}` is
formalized in `CrossCarrierCompletionModel.lean`.

The geometric repair is to enroll all preparatory source centres and their
intersections before serialization.  In the example, the origin is processed
before `D`; after that deepest blowup, the transforms of `D` and `C_2` are
disjoint.

---

# 3. Compressing one finite flatifier word to one source ideal

Let

```text
C_m -> C_(m-1) -> ... -> C_0=C
```

be a finite sequence of blowups in finitely presented centres.  Standard
composition of blowups gives a finitely presented ideal `J subset O_C` such
that the composite is isomorphic to `Bl_J(C) -> C`.

The ideal `J` must retain an immutable source label.  The equality of the
composite morphism with one blowup does not by itself identify strict
transforms; the centre-enriched Cartier-trace semantics of X037 is retained.
For flat final strict transforms, the flat Cartier-trace base-change theorem
recovers the source-pure transform after every later dominating modification.

Thus one maximal carrier contributes one source-labelled admissible ideal, not
an unstructured finite word, to the common-refinement stage.

---

# 4. Ambient traces and the finite common product

Let `{C_lambda}` be the finite set of inclusion-maximal regular carriers.  For
each `lambda`, let

```text
J_lambda subset O_(C_lambda)
```

be the componentwise-admissible flatifier ideal, and let

```text
K_lambda = inverseImage(J_lambda) subset O_X
```

be its canonical ambient trace ideal.  Scheme-theoretically,

```text
V(K_lambda) = V(J_lambda) subset C_lambda.
```

Define

```text
K_common = product_lambda K_lambda.
```

The product is independent of the enumeration of the finite source orbit.  Its
closed support is the finite union of the source supports.

The elementary binary containments

```text
I*J <= I,
I*J <= J
```

and commutativity/associativity are formalized in
`CommonTraceProduct.lean`.

## Standard common-refinement theorem

The blowup

```text
Bl_(K_common)(X) -> X
```

factors through every

```text
Bl_(K_lambda)(X) -> X.
```

More generally, a finite family of admissible blowups has an admissible common
refinement obtained from the product of its ideals.  This is a standard
universal-property theorem for blowups.

By the strict-transform theorem, the transform of `C_lambda` in
`Bl_(K_lambda)(X)` is

```text
Bl_(J_lambda)(C_lambda),
```

which is precisely the chosen carrier flatifier.

---

# 5. Strict support-dimension drop

The admissible good open of each flatifier contains every generic point of
`C_lambda`.  Hence

```text
V(J_lambda)
```

contains no irreducible component of the regular carrier.  Therefore

```text
dim V(J_lambda) < dim C_lambda
```

componentwise.  Since the common product support is a finite union,

```text
dim V(K_common)
  = max_lambda dim V(K_lambda)
  < max_lambda dim C_lambda.
```

This is the decisive well-foundedness fact.  The common product centre may be
singular and is not itself allowed in the final ordinary sequence, but its
entire support lies in a strictly lower-dimensional relative-resolution
problem.

A direct blowup in `K_common` is therefore only a canonical modification target,
not an actual final centre.

---

# 6. Lower-dimensional regular realization

Assume the strong relative principalization program for all carrier dimensions
strictly below

```text
d = max_lambda dim C_lambda.
```

Apply it to the source-labelled ideal `K_common`, with the restrictions of all
active owners, passive owners, boundary strata, contact packets, sources, and
debts.  It produces a finite ambient word

```text
X' -> ... -> X
```

of ordinary blowups in regular, nonidentity, jointly legal centres contained in
`V(K_common)`, such that

```text
K_common O_(X')
```

is invertible.

The universal property then gives

```text
X' -> Bl_(K_common)(X) -> Bl_(K_lambda)(X)
```

for every `lambda`.

Every recursive legalization call occurs on a carrier of dimension `<d`; no
same-dimensional re-flatification loop is introduced.

This step uses the full lower-dimensional theorem, not merely resolution of the
reduced support.  Nilpotent thickness, contact, passive safety, boundary SNC,
and source ledgers must be carried by the recursive call.

---

# 7. Simultaneous pullback of all flat strict transforms

Let `F_lambda^flat` be any passive/projective-normal strict transform produced
on the flatified carrier

```text
C_lambda^flat = Bl_(J_lambda)(C_lambda),
```

and assume it is flat over `C_lambda^flat`.

The common regular word factors through the source flatifier.  Flatness is
preserved under base change.  Moreover, every additional exceptional divisor
on the dominating word is Cartier on the transformed regular carrier.  A flat
module has no torsion with respect to a Cartier equation.  Therefore the strict
transform along the complete common word is exactly the pullback of
`F_lambda^flat`; no additional source-Cartier purification occurs.

Consequently every maximal carrier is passive legal after the same common
macro.

This argument uses:

```text
factorization through the source blowup,
composition of strict transforms,
flat strict transform equals pullback,
exceptional no-recharge.
```

The exact source-labelled all-chart sheaf interface remains an open project
edge, but no new existence theorem for simultaneous flatification is required.

---

# 8. Finite source-arrangement completion

The source supports and the old carrier arrangement form a finite family.  Take
all scheme-theoretic intersections.  Combinatorially, every intersection lies
inside the finite union of the original point labels, so the completion space
is finite.  The over-approximation by the powerset of that finite union is
formalized in `FiniteArrangementCompletion.lean`.

If an intersection stratum is nonregular, it enters the X035 support-thickness
branch in strictly lower support dimension.  If all strata are regular and
jointly legal, they form a clean source-enriched arrangement.

Let `D` be a minimal nonempty current stratum.  Intersection closure and
minimality imply that for every other stratum `C`,

```text
D is disjoint from C
or
D is contained in C.
```

The exact finite-set theorem is formalized in
`MinimalStratumNesting.lean`.

Hence after source arrangement completion the ambient transport problem has
only two cases:

```text
disjoint transport,
nested Regular-Flag Flat-Lift.
```

A general transverse or clean-square passive transform theorem is no longer
load bearing.

---

# 9. Wonderful persistence and maximal-carrier budget

After the common macro prepares all inclusion-maximal carriers, Hironaka
normal-flatness transitivity prepares every regular intersection stratum.
Deepest-first wonderful serialization then proceeds as follows.

* A disjoint carrier is unchanged locally.
* A containing carrier is transported by the Regular-Flag Flat-Lift theorem.
* Flatness kills all exceptional purification torsion.
* Hironaka transitivity prepares every new descendant stratum.
* No passive source is re-enrolled by intersection completion or serialization.

Thus the X039 multiset of independent maximal-carrier charges can be compressed
to one common source-product obligation.

The internal rank is

```text
(common support dimension,
 unresolved source count,
 remaining common-word height).
```

Its well-founded arithmetic is formalized in
`CommonFlatifierBudgetRank.lean`.

---

# 10. Maximum-likelihood common-flatifier theorem

> **Common-Flatifier Trace Realization Theorem.**  Let `X` be a regular
> Noetherian ambient scheme carrying a finite symmetry-stable clean arrangement
> of regular raw carriers and a finite active/passive/logarithmic/source
> portfolio.  For every inclusion-maximal carrier, let a componentwise
> admissible centre-enriched blowup flatify its complete passive and transform
> packet.  Let `K_common` be the product of the ambient trace ideals of these
> flatifiers.  Assume strong relative principalization and joint legalization
> in all carrier dimensions below the maximum carrier dimension.
>
> Then there is a finite symmetry-compatible word of ordinary ambient blowups
> in regular, nonidentity, jointly legal centres, all supported in
> `V(K_common)`, such that the word factors through the blowup of `K_common` and
> through every source flatifier.  The strict transform of every maximal
> carrier is normally flat and Tor-safe for every passive owner.  The full
> source-enriched intersection arrangement becomes regular and clean after
> lower-dimensional support-thickness recursion.  Every deepest-first
> interaction is disjoint or nested; nested interactions are transported by
> Regular-Flag Flat-Lift.  All source, owner, boundary, contact, and debt data
> reenter without reset, and no new passive charge is created inside the
> wonderful word.

This theorem is the current maximum-likelihood replacement for independent
maximal-carrier legalization.  It is not proved.

---

# 11. Corrected candidate graph

```text
finite intrinsic state
-> finite raw carrier arrangement
-> inclusion-maximal carriers

for every maximal carrier:
  one centre-enriched admissible flatifier ideal J_lambda
  -> ambient trace ideal K_lambda

finite source orbit
-> common product K_common
-> componentwise support-dimension drop
-> lower-dimensional relative principalization
-> regular jointly legal ambient word
-> factor through Bl_(K_common)
-> factor through every source flatifier
-> simultaneous maximal-carrier passive flatness

source-enriched intersection completion
-> bad strata: lower-dimensional support-thickness recursion
-> clean strata: deepest-first wonderful word
-> disjoint or nested coverage
-> nested Regular-Flag Flat-Lift
-> Hironaka transitivity to every descendant
-> exceptional no recharge
-> all-chart hereditary reentry
-> outer causal termination and globalization.
```

---

# 12. Exact frontier after X040

```text
X040-G1   FINITE_FLATIFIER_WORD_TO_ONE_SOURCE_IDEAL
X040-G2   AMBIENT_TRACE_IDEAL_AND_STRICT_CARRIER_BLOWUP
X040-G3   FINITE_PRODUCT_BLOWUP_COMMON_REFINEMENT
X040-G4   COMPONENTWISE_ADMISSIBLE_SUPPORT_DIMENSION_DROP
X040-G5   LOWER_DIMENSIONAL_RELATIVE_PRINCIPALIZATION_OF_COMMON_PRODUCT
X040-G6   REGULAR_JOINTLY_LEGAL_AMBIENT_REALIZATION
X040-G7   SOURCE_PURE_TRANSFORM_AFTER_COMMON_REFINEMENT
X040-G8   SIMULTANEOUS_MAXIMAL_CARRIER_FLATNESS
X040-G9   FINITE_SOURCE_ARRANGEMENT_COMPLETION
X040-G10  BAD_SOURCE_INTERSECTION_SUPPORT_THICKNESS_RECURSION
X040-G11  CLEAN_SOURCE_ARRANGEMENT_WONDERFUL_SERIALIZATION
X040-G12  MINIMAL_STRATUM_DISJOINT_OR_NESTED_SCHEME_THEOREM
X040-G13  REGULAR_FLAG_FLAT_LIFT
X040-G14  HIRONAKA_TRANSITIVITY_AND_WONDERFUL_PERSISTENCE
X040-G15  COMMON_PASSIVE_BUDGET_NO_RECHARGE
X040-G16  SOURCE_CONSERVATIVE_ALL_CHART_NO_RESET
X040-G17  OUTER_BIRTH_CLASSIFICATION_FOR_NEW_MAXIMAL_SOURCES
X040-G18  UNIVERSAL_ACTUAL_JOINTLY_LEGAL_CENTRE_WORD
```

The highest-information cut is

```text
X040-G5/G6
  lower-dimensional principalization with the complete portfolio,

X040-G7
  centre-enriched source-pure transform under the common refinement,

X040-G13
  Regular-Flag Flat-Lift,

X040-G16
  source-conservative all-chart no-reset.
```

The product and common-refinement existence are standard.  The genuinely
project-specific burden is their integration with legal centres and hereditary
state identity.

---

# 13. Exact Lean source written in this round

```text
MinimalStratumNesting.lean
CommonTraceProduct.lean
CommonFlatifierBudgetRank.lean
FiniteArrangementCompletion.lean
CrossCarrierCompletionModel.lean
X040CommonFlatifierTraceIndex.lean
X040CommonFlatifierTraceIndexAudit.lean
```

The slice proves only:

1. finite source/intersection completion has one finite over-approximation;
2. crossing source centres can be non-disjoint and non-nested;
3. a minimal nonempty stratum is disjoint from or contained in every stratum;
4. binary source products are contained in both factors and are symmetric and
   associative;
5. the support/source/word rank is well founded.

It does not prove a blowup factorization, support-dimension theorem, flatifier,
principalization, Regular-Flag Flat-Lift, no-reset, termination, or resolution.

---

# 14. Counterexample ledger additions

```text
CFT-1  independent maximal-carrier words cross;
CFT-2  direct blowup of the common product can have a singular centre;
CFT-3  product modification without source labels can change strict transform;
CFT-4  a good open missing one component does not give support-dimension drop;
CFT-5  flatifier word composition without finite presentation is invalid;
CFT-6  regularization of the product without the full owner portfolio can
       create passive or boundary illegality;
CFT-7  arrangement completion without deepest-first order leaves cross cases;
CFT-8  repeated source charge after common preparation is a forbidden reset;
CFT-9  flat pullback is insufficient without Cartier/no-torsion control;
CFT-10 arbitrary ordering of a symmetry orbit breaks functoriality.
```

---

# 15. Annals-series maximum-likelihood estimate

The common-product theorem adds a concise common-refinement section to Paper II
but removes independent flatifier-word reconciliation, general clean-square
transport, and one passive budget per intersection stratum from Papers III and
IV.  The new central estimate is **552 dense Annals/AMS-equivalent pages**.

| Paper | Maximum-likelihood title | Pages |
|---:|---|---:|
| I | Intrinsic Frobenius-Hasse States, Affine Conormal Packets, and Projectivity Discriminants | 90 |
| II | Common Trace Products, Anchor-Contact Ideals, and Wonderful Actual-Centre Synthesis | 120 |
| III | Common-Refinement Flatification, Regular-Flag Transport, and Hereditary Reentry | 132 |
| IV | Passive-Budget No-Recharge, Source-Debt Causality, and Dimension-Strict Termination | 84 |
| V | Global Descent, Symmetry-Compatible Serialization, and Principalization | 78 |
| VI | Functorial Resolution, Counterexample Closure, and Lean Reproducibility | 48 |
|  | **Total** | **552** |

A single-volume editorial edition with theorem-interface cards, common-trace and
source ledgers, regular-flag chart compendium, proof DAG, counterexample atlas,
and paper-to-Lean map is estimated at **598--632 physical pages**.

Subjective publication-form planning weights:

```text
six papers                                      0.67
seven papers, splitting common-refinement lift 0.15
five papers after consolidation                 0.12
other                                           0.06
```

These are research-planning weights, not calibrated probabilities.

---

# 16. Modal decisive theorem for the final series

> **Common-Trace Carrier Legalization and Nested Persistence Theorem.**  For a
> prepared marked state on a smooth `n`-dimensional scheme over a perfect field
> of characteristic `p>0`, the finite symmetry orbit of maximal raw carrier
> flatifiers admits one componentwise-admissible common ambient trace product.
> Its support has strictly smaller dimension than the maximal carriers.  The
> strong relative principalization theorem in lower dimension realizes the
> common modification by a finite ordinary word in regular, jointly legal trace
> centres.  The word factors through every source flatifier, so every maximal
> carrier becomes normally flat, Tor-safe, active-permissible, and
> SNC-compatible simultaneously.  The source-enriched intersection completion
> is finite; bad intersections enter lower-dimensional support-thickness
> recursion, while clean intersections admit a deepest-first wonderful word.
> Every remaining interaction is disjoint or nested.  The nested
> Regular-Flag Flat-Lift theorem, Hironaka transitivity, and exceptional
> no-recharge preserve passive legality through the complete word.  Every
> source, owner, boundary, contact, and debt identity reenters without reset,
> nested calls lower support dimension, and outer successors lower the global
> causal rank.

This is a maximum-likelihood theorem target, not an established theorem.

---

# 17. Truth boundary

```text
ROUND_ID                                            = MLEL-X040 / CFT-ACN

X039_EXPERIMENTAL_CLEANROOM_GREEN                   = true
X039_DECLARATIONS_PROMOTED                          = false

INDEPENDENT_MAXIMAL_CARRIER_COMPILER_REJECTED       = true
CROSS_CARRIER_COUNTERMODEL_RECORDED                 = true
COMMON_TRACE_PRODUCT_IDENTIFIED                     = true
FINITE_PRODUCT_COMMON_REFINEMENT_IDENTIFIED         = STANDARD_MATH
STRICT_SUPPORT_DIMENSION_ROUTE_IDENTIFIED           = true
FINITE_SOURCE_ARRANGEMENT_COMPLETION_IDENTIFIED     = true
MINIMAL_STRATUM_NESTING_LEAN_SOURCE_WRITTEN         = true
COMMON_TRACE_PRODUCT_LEAN_SOURCE_WRITTEN             = true
COMMON_BUDGET_RANK_LEAN_SOURCE_WRITTEN              = true

LOWER_DIMENSIONAL_FULL_PORTFOLIO_PRINCIPALIZATION_PROVED = false
SOURCE_PURE_TRANSFORM_COMMON_REFINEMENT_PROVED      = false
REGULAR_FLAG_FLAT_LIFT_PROVED                       = false
SOURCE_CONSERVATIVE_ALL_CHART_NO_RESET_PROVED       = false
UNIVERSAL_JOINTLY_LEGAL_CENTRE_WORD_PROVED          = false
GLOBAL_TERMINATION_PROVED                           = false

X040_CLEANROOM_GREEN                                = false
NEW_DECLARATIONS_PROMOTED                           = false
CERTIFIED_GRAPH_CHANGED                             = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED                  = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION          = false
FORMAL_GLOBAL_STATUS                                = OPEN_GAP
```

---

# 18. Principal standard inputs

1. Composition of finitely presented blowups is a blowup.
2. A finite product of admissible blowup ideals gives a common refinement.
3. The strict transform of a closed subscheme is the blowup in the induced
   centre.
4. Strict transform is compatible with composition and étale localization.
5. The strict transform of a sheaf flat over the base centre is its pullback.
6. Hironaka/Herrmann-Schmidt/Robbiano transitivity of normal flatness for
   regular flags.
7. Wonderful compactification/building-set serialization of clean
   arrangements.
8. The current MLE-Lean baseline through X039 and the restricted Hasse-Morita
   core descent theorem.

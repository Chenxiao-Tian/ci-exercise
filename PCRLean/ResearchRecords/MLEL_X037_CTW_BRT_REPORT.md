# MLEL-X037 / CTW-BRT

## Cartier-Trace Words, Bifiltered Rees Transport, and the Pure-Transform Interchange Defect

**Chinese title:** Cartier 迹词、双过滤 Rees 运输与纯变换交换缺陷  
**Protocol:** `PCR-FRACTAL-PROOF-LEAN 1.0 / MLEL-A003-FPE-EDGE`  
**Seed architecture:** `MLEL-D001 / FCPP-ATLAS`  
**Accepted mathematical parent:** `MLEL-M004 / HMC-SCCD` (restricted)  
**Experimental parent:** `MLEL-X036 / PNF-ACL`  
**Primary D001 refinement:** `G29 -> G31 -> G41`, with common return edges to `G18/G26/G46/G52/G53`  
**Class:** `EXPERIMENTAL_CANDIDATE_GRAPH_CORRECTION / NO_THEOREM_PROMOTION`  
**Date:** 2026-08-04  
**Global status:** `OPEN_GAP`

---

# 0. Executive verdict

X036 correctly moved passive normal flatness and regular-support contact from
one-shot centre-selection gates to lower-dimensional legalization problems.
Its phrase

```text
regular word dominating the flatifying modification
```

is nevertheless insufficient.  A strict or pure transform remembers the
**chosen blowup centre**, not merely the resulting morphism.  A blowup in an
effective Cartier divisor is the identity morphism, while its strict transform
can still quotient away every section supported on that divisor.

The corrected primitive is therefore not a bare dominating modification.  It
is a **centre-enriched Cartier-trace word** carrying:

```text
carrier C_i inside ambient X_i,
source-labelled carrier ideal J_i,
canonical ambient trace ideal K_i = inverse image of J_i,
carrier and ambient blowups,
pure-transform / controlled-transform payload,
owner, source, debt, and boundary identities.
```

The same correction applies to both X036 branches:

```text
projective-normal flatification
and
anchor-contact principalization.
```

After lower-dimensional principalization, the relevant carrier ideals become
Cartier or monomial.  Their carrier blowups may then be identities, but their
ambient trace blowups remain nonidentity and realize the required saturation,
pure transform, or contact division.

The new load-bearing theorem is a **bifiltered Rees interchange theorem**.  It
must compare

```text
ambient strict transform, then associated graded along the transformed carrier
```

with

```text
associated graded along the original carrier, then carrier pure transform.
```

Rather than assuming these operations always commute, X037 introduces their
finite kernel/cokernel as the **Rees interchange defect**.  Vanishing gives the
transport theorem; nonvanishing produces a new finite Fitting/projective-normal
recursive packet.

---

# 1. Exact validation state inherited from X036

The final X036 exact-snapshot clean room is green.

```text
PR                         = 46, draft, open, unmerged
base branch                = pcr-fractal-x036-pnf-acl-base-20260804
head branch                = pcr-fractal-x036-pnf-acl-head-20260804
head SHA                   = f91193c943adc8bdb2d1f3d5b2f0c6b61580be40
workflow run               = 30927499452
job                        = 92053484311
conclusion                 = success
artifact                   = 8900025922
artifact digest            = sha256:fb5f2a0bc06c83645d2c87b850dff8a996c259c390623975c2bc21f032dd647c
```

The run completed the placeholder/project-axiom scan, official default build,
all exact X036 module builds, unified axiom audit, source snapshot, and evidence
upload.  This certifies only the finite X036 Experimental slice.  It promotes no
declaration and does not prove a scheme-level flatification or resolution
theorem.

---

# 2. The morphism-only domination statement is false

## 2.1 Carrier model

Let

```text
A = k[z],
C = Spec(A),
J = (z),
F = A/(z).
```

Since `J` is an effective Cartier ideal, `Bl_J(C) -> C` is the identity
morphism.  Nevertheless its exceptional divisor is `V(z)`, and every section
of `F` is supported there.  By the definition of strict transform,

```text
F^str = F / H^0_{V(z)}(F) = 0.
```

If the same identity morphism is presented as the blowup in the empty centre,
the strict transform is `F`, not zero.  Thus the identity morphism does not
determine the transformed sheaf.

## 2.2 Ambient passive model

Embed the carrier in

```text
R = k[x,z],
X = Spec(R),
C = V(x),
M = R/(z).
```

Along `C`, every homogeneous piece of `gr_(x)(M)` is isomorphic to `k[z]/(z)`.
Hence the passive associated graded module is not flat over `C`.

The carrier ideal `J=(z)` has canonical ambient trace ideal

```text
K = (x,z).
```

Blowing up `X` in `K` is nonidentity.  The strict transforms of `V(x)` and
`V(z)` meet the exceptional divisor at different directions and are disjoint.
Consequently the transformed passive sheaf is zero along the transformed
carrier and its associated graded is flat.

This example proves that the missing data are not cosmetic.  A carrier-Cartier
identity step can be the decisive ambient passive-flatness step.

## 2.3 Contact model

For the tangent curves

```text
(y),
(y-x^m)
```

on `A^2`, the contact ideal on the anchor `V(y)` is `(x^m)`.  Principalization
on the anchor makes the contact Cartier, but blowing up that Cartier ideal on
the anchor is the identity.  Blowing up its ambient trace `(x,y)` is
nonidentity and changes the residual contact from `x^m` to `x^(m-1)`.

The passive and contact examples are therefore instances of the same
Cartier-on-carrier / non-Cartier-in-ambient mechanism.

---

# 3. Cartier trace and its finite torsion packet

Let `D` be an effective Cartier divisor on a Noetherian carrier `C`, with ideal
`L`, and let `F` be coherent.  Define the Cartier trace packet

```text
CT_D(F) = H^0_D(F)
        = union_n (0 :_F L^n).
```

Noetherianity makes this union stabilize.  The strict transform for the
identity blowup in `D` is

```text
PT_D(F) = F / CT_D(F).
```

This packet is the exact obstruction to forgetting the centre.  If
`CT_D(F)=0`, multiplying a blowup centre by `D` does not change the strict
transform.  If the packet is nonzero, the same underlying blowup morphism can
produce a different transformed sheaf.

For an ideal or contact equation, the analogous operation is Cartier
saturation / controlled division.  The payload therefore consists of both

```text
Cartier-supported module torsion
and
Cartier valuation/contact exponents.
```

---

# 4. Centre-enriched carrier words

Let `C_i -> X_i` be a regular carrier in a regular ambient scheme.  One
centre-enriched step is the tuple

```text
S_i = (
  C_i -> X_i,
  source label lambda_i,
  coherent carrier ideal J_i subset O_(C_i),
  ambient trace ideal K_i = preimage(J_i) subset O_(X_i),
  carrier payload Q_i,
  owner/boundary/source/debt ledger,
  transform certificate
).
```

The next ambient scheme is

```text
X_(i+1) = Bl_(K_i)(X_i),
```

and strict-transform geometry gives

```text
C_(i+1) = Bl_(J_i)(C_i).
```

If `J_i` is invertible, the second morphism is an identity but the step is not
deleted.  It is a **Cartier-trace step**.  Its ambient centre can have
codimension at least two and its pure-transform payload can be nontrivial.

A morphism-only word forgets `J_i`, `lambda_i`, and the payload.  The Lean file
`CentreEnrichedPureTransform.lean` proves the exact abstract no-go: on a
nontrivial module, forgetting the vertical submodule and retaining only the
carrier-morphism token is not injective.

---

# 5. Source-labelled pure transforms on a dominating regular word

Let `J` be an arbitrary coherent ideal on a regular carrier `C`, and let

```text
pi : C' -> C
```

be a lower-dimensional regular-centre word for which `J O_(C')` is invertible.
Do not replace the original centre by the bare morphism `pi`.  Retain the
immutable source label `[J]` and define the source-pure transform

```text
PT_(J,pi)(F)
  = pi^*F / H^0_(V(J O_(C')))(pi^*F).
```

The universal property factors `pi` through `Bl_J(C)`.  The required
Cartier-trace base-change theorem should state, under the precise Tor/flatness
hypotheses supplied by flatification, that `PT_(J,pi)(F)` is the pullback of the
strict transform on `Bl_J(C)`.

This is the correct replacement for the phrase “a regular word dominates the
flatifier”.  The word must dominate the **centre-enriched pure-transform
problem**.

---

# 6. Converting an arbitrary flatification word to regular ambient steps

Suppose a proper projective-normal sheaf on `P(E)->C` is flatified by a sequence
of possibly singular-centre blowups on `C`:

```text
C^flat -> ... -> C.
```

Process one source-labelled flatifier ideal `J` at a time.

1. Apply the lower-dimensional principalization/resolution program to `J` on
   the current regular carrier.
2. Lift every regular centre to its canonical ambient trace centre.
3. On the final carrier, `J` is invertible or monomial.
4. Execute the residual Cartier-trace steps instead of deleting them as carrier
   identities.
5. Use the Cartier-trace base-change theorem to identify the resulting
   source-pure transform with the pullback of the flatified strict transform.
6. Pull back the next source-labelled flatifier centre and repeat.

Flatness is stable under base change.  Thus this procedure can inherit the
flatness output of the original flatifier without ever using a singular ambient
centre, provided the transform comparisons and no-reset laws are proved.

The same compiler applies to anchor contact ideals.  The only difference is the
payload property: flatness in the passive branch and strict contact reduction
in the contact branch.

---

# 7. The bifiltered Rees object

Let `R` be a local or affine ambient ring, let

```text
I = ideal of the carrier C,
J = carrier legalization ideal in R/I,
K = inverse image of J in R,
M = one ambient owner module.
```

The pair `I subset K` supplies two filtrations:

```text
normal degree       from powers of I,
carrier-trace degree from powers of K or J.
```

A suitable extended/bigraded Rees module should encode the pieces

```text
I^a K^b M
```

and their saturations in both exceptional directions.  It must specialize to

```text
gr_I(M)
```

on the normal side and to the `K`-blowup strict transform on the ambient side.
The exact extended grading and saturation convention remains an X037 theorem
obligation; it may not be hidden in notation.

---

# 8. The pure-transform interchange morphism

On every standard `K`-blowup chart, the common bifiltered Rees module should
produce a canonical comparison

```text
Xi_(I,K,M):
  gr_(I')(PT_K(M))
  ->
  PT_J(gr_I(M)) tensor grading-twist,
```

where `I'` is the transformed carrier ideal.  The direction and twist must be
fixed by the explicit chart algebra and verified on overlaps.

Define the Rees interchange defect by

```text
RID_(I,K)(M)
  = ker(Xi_(I,K,M)) directSum coker(Xi_(I,K,M)).
```

For a finite owner portfolio, take the direct sum over owners and over the
finite low-degree/projective-tail packet.

This replaces an overstrong universal equality by an exact dichotomy:

```text
RID = 0
-> ambient transform and projective-normal pure transform agree;

RID != 0
-> its Fitting/support/projective-normal packet is a canonical recursive
   defect carrier.
```

The defect is expected to be supported on the non-Tor-independent locus of the
two filtrations.  Derived deformation-to-normal-bundle technology may help
construct `Xi`, but the final theorem must be stated and proved in ordinary
coherent scheme language.

---

# 9. Sharpening the finite Rees--Serre packet

Flatness of the projective sheaf alone is not yet the full finite certificate
for `gr_I(M)`.  The packet must include:

```text
1. a uniform comparison cutoff N;
2. the finite low pieces G_0,...,G_N;
3. bounded irrelevant torsion and the kernels/cokernels of
   G_n -> pi_* F(n) in the transition window;
4. vanishing or perfect base-change certificates for higher direct images in
   the stable tail;
5. flatness of the projective-normal sheaf F;
6. compatibility with the source-labelled pure transform;
7. the finite Rees interchange defect.
```

The Lean file `FinitePrefixTailCriterion.lean` proves only the final logical
compiler: once the finite window and eventual tail are certified, every degree
is covered.  Serre comparison, cohomology/base change, and flattening remain
geometric obligations.

---

# 10. Unified carrier-ideal realization compiler

The maximum-likelihood common theorem now has the following interface.

> **Carrier-Ideal Realization Compiler.**  Let `C->X` be a regular carrier in a
> regular ambient scheme, let `{J_lambda}` be a finite symmetry-stable family of
> coherent carrier ideals with immutable source labels, and let `Q` be a finite
> portfolio of projective-normal sheaves, contact ideals, boundary-conormal
> packets, owners, sources, and debts.  Assume the strong relative
> principalization program in dimensions below `dim X`.  Then there is a finite
> word of ordinary ambient blowups in regular trace centres such that every
> `J_lambda` becomes monomial on the carrier, every residual Cartier trace is
> executed rather than discarded, and the final source-pure transforms of `Q`
> agree with the transforms prescribed by the original centre-enriched
> flatification/principalization problem.  Every nonterminal branch either
> lowers the carrier dimension, kills a Rees interchange defect, improves the
> passive projective-normal packet, lowers contact, or cleans debt.

This theorem is not proved.  It is the proposed common parent of the passive,
contact, and logarithmic legalization macros.

---

# 11. Corrected candidate graph

```text
prepared intrinsic state
-> finite minimizer intersection arrangement
-> raw regular candidate carrier C

PASSIVE / LOG LEGALIZATION
-> finite projective-normal and log-conormal packets
-> source-labelled flatifier ideals J_lambda on C
-> lower-dimensional simultaneous principalization
-> centre-enriched regular carrier word
-> ambient trace lift
-> residual Cartier-trace steps
-> bifiltered Rees comparison Xi
-> RID vanishes or strict RID recursion
-> normally flat / Tor-safe / SNC carrier

REGULAR-SUPPORT CONTACT
-> full symmetry-stable anchor family
-> source-labelled contact ideals D_i
-> same carrier-ideal realization compiler
-> residual Cartier-trace cleaning
-> empty or clean transformed intersection

CLEAN ARRANGEMENT
-> maximal wonderful word
-> legalize every word centre by the same compiler
-> all-chart source-labelled hereditary reentry
-> dimension/RID/passive/contact/debt/SCC rank
-> finite global ordinary word.
```

---

# 12. Exact open frontier after X037

```text
X037-G1   CENTRE_ENRICHED_BLOWUP_WORD_SEMANTICS
X037-G2   CARTIER_TRACE_TORSION_PACKET_FINITE_STABILIZATION
X037-G3   CARRIER_IDEAL_TO_CANONICAL_AMBIENT_TRACE_IDEAL
X037-G4   STRICT_TRANSFORM_OF_CARRIER_EQUALS_CARRIER_BLOWUP
X037-G5   SOURCE_PURE_TRANSFORM_ON_A_DOMINATING_WORD
X037-G6   CARTIER_TRACE_BASE_CHANGE_WITH_TOR_CERTIFICATE
X037-G7   SIMULTANEOUS_LOWER_DIMENSIONAL_PRINCIPALIZATION_OF_SOURCE_IDEALS
X037-G8   REGULAR_AMBIENT_REALIZATION_OF_A_FLATIFIER_WORD
X037-G9   BIGRADED_OR_EXTENDED_BIFILTERED_REES_FINITE_PRESENTATION
X037-G10  ALL_CHART_PURE_TRANSFORM_INTERCHANGE_MORPHISM
X037-G11  FINITENESS_AND_BASE_CHANGE_OF_REES_INTERCHANGE_DEFECT
X037-G12  RID_VANISHING_OR_STRICT_FITTING_SUPPORT_DESCENT
X037-G13  PROJECTIVE_NORMAL_REGULARITY_PACKET
X037-G14  PASSIVE_NORMAL_FLATNESS_AFTER_CARTIER_TRACE_REALIZATION
X037-G15  ANCHOR_CONTACT_AS_THE_SAME_CARTIER_TRACE_COMPILER
X037-G16  LOG_CONORMAL_CARTIER_TRACE_LEGALIZATION
X037-G17  SYMMETRY_OVERLAP_AND_SOURCE_LABEL_TRANSPORT
X037-G18  CARTIER_TRACE_MACRO_NO_RESET
X037-G19  COMPOSITE_DIMENSION_RID_PASSIVE_CONTACT_DEBT_SCC_RANK
X037-G20  UNIVERSAL_ACTUAL_JOINTLY_LEGAL_CENTRE_WORD
```

The new highest-information cut is

```text
X037-G6 + X037-G10/X037-G12 + X037-G18.
```

The deepest project-specific issue is no longer whether a flatifier exists.
It is whether its centre-enriched pure-transform effect can be reproduced by a
regular ambient word and reconstructed on every chart without reset.

---

# 13. Lean source written in this round

```text
CentreEnrichedPureTransform.lean
BifilteredLegalizationRank.lean
FinitePrefixTailCriterion.lean
X037CartierTraceReesTransportIndex.lean
X037CartierTraceReesTransportIndexAudit.lean
```

The exact slice proves:

1. a carrier-morphism token does not determine a pure-transform payload;
2. finite-window plus eventual-tail certificates cover every degree;
3. Rees-commutator improvement dominates passive/contact/debt changes;
4. passive improvement dominates contact/debt;
5. contact improvement dominates debt;
6. the proposed four-coordinate rank is well founded.

It does not construct the scheme-level Cartier trace, bifiltered Rees object,
interchange map, defect packet, or ambient legalization word.

---

# 14. Counterexample and stress-test ledger

The X037 compiler must pass at least the following families.

```text
CT-1  identity Cartier blowup with fully supported torsion sheaf
CT-2  identity Cartier blowup with Cartier-torsion-free sheaf
CT-3  passive crossing axes in A^2
CT-4  tangent curves with contact m -> m-1
CT-5  nested regular centres with clean nonzero excess
CT-6  several flatifier ideals becoming different SNC monomials
CT-7  symmetry exchanging two anchors or flatifier sources
CT-8  a flat projective tail with nonflat low associated-graded pieces
CT-9  nonzero Rees interchange kernel with zero cokernel, and conversely
CT-10 normalization/cleaning attempts that erase a source label
```

The no-go boundary is sharp: if the Cartier trace packet vanishes, the centre
may often be changed by a Cartier factor without changing the strict transform;
if it does not vanish, morphism-only replacement is invalid.

---

# 15. Annals-series maximum-likelihood estimate

The modal form remains six papers.  Centre-enriched transform semantics and the
bifiltered Rees comparison add a substantial chapter to Paper III, while the
single carrier-ideal compiler slightly compresses the former separate passive
and contact preparations.  The new central estimate is **562 dense
Annals/AMS-equivalent pages**.

| Paper | Maximum-likelihood title | Pages |
|---:|---|---:|
| I | Intrinsic Frobenius-Hasse States, Affine Conormal Packets, and Projectivity Discriminants | 90 |
| II | Anchor-Contact Ideals, Cartier-Trace Words, and Wonderful Actual-Centre Synthesis | 118 |
| III | Carrier-Enriched Flatification, Bifiltered Rees Transport, and Hereditary Reentry | 140 |
| IV | Rees-Interchange Defects, Source-Debt Causality, and Termination | 88 |
| V | Global Descent, Symmetry-Compatible Serialization, and Principalization | 78 |
| VI | Functorial Resolution, Counterexample Closure, and Lean Reproducibility | 48 |
|  | **Total** | **562** |

A one-volume editorial edition with theorem-interface cards, the centre-source
ledger, chart compendium, proof DAG, counterexample atlas, and paper-to-Lean map
is estimated at **610--650 physical pages**.

Subjective publication-form planning weights:

```text
six papers                                      0.57
seven papers, splitting bifiltered transport    0.25
five papers after consolidation                 0.11
other                                           0.07
```

These are research-planning weights, not calibrated probabilities.

---

# 16. Modal decisive theorem

> **Cartier-Trace Ambient Realization and Bifiltered Rees Interchange
> Theorem.**  Let a prepared marked state on an `n`-dimensional smooth scheme
> over a perfect field of characteristic `p>0` produce a finite
> symmetry-stable family of regular raw carriers.  Assume the strong relative
> principalization program in dimensions `<n`.  Every finite source-labelled
> family of passive flatifier, anchor-contact, and logarithmic carrier ideals
> admits a finite centre-enriched word of ordinary ambient blowups in regular
> trace centres.  Carrier-Cartier identity steps are retained and realize the
> prescribed pure or controlled transforms.  For every owner there is a
> canonical all-chart bifiltered Rees comparison; its finite interchange defect
> either vanishes or produces a strict lower-support/Fitting recursive task.
> When the defects vanish, the transformed carrier is simultaneously
> permissible for all active owners, normally flat and Tor-safe for all passive
> owners, and SNC-compatible with the total boundary.  All source, owner, debt,
> boundary, flatifier, contact, and packet identities reenter on overlaps
> without reset.  Every nonterminal macro strictly lowers the composite
> dimension/RID/passive/contact/debt/SCC rank.

This is the current maximum-likelihood replacement for the X036
morphism-dominating lift theorem.  It is not yet proved.

---

# 17. Truth boundary

```text
ROUND_ID                                          = MLEL-X037 / CTW-BRT

X036_EXPERIMENTAL_CLEANROOM_GREEN                 = true
X036_DECLARATIONS_PROMOTED                        = false

MORPHISM_ONLY_DOMINATION_COUNTEREXAMPLE_IDENTIFIED = true
CENTRE_ENRICHED_WORD_IDENTIFIED                   = true
CARTIER_TRACE_PACKET_IDENTIFIED                   = true
PASSIVE_CONTACT_COMMON_COMPILER_IDENTIFIED        = true
REES_INTERCHANGE_DEFECT_IDENTIFIED                = true
CENTRE_PAYLOAD_NO_GO_LEAN_SOURCE_WRITTEN          = true
FINITE_PREFIX_TAIL_LEAN_SOURCE_WRITTEN            = true
BIFILTERED_RANK_LEAN_SOURCE_WRITTEN               = true

CARTIER_TRACE_SCHEME_THEOREM_PROVED               = false
SOURCE_PURE_TRANSFORM_BASE_CHANGE_PROVED          = false
BIGRADED_REES_INTERCHANGE_MAP_PROVED              = false
REES_INTERCHANGE_DEFECT_FINITE_PACKET_PROVED      = false
PASSIVE_NORMAL_FLAT_AMBIENT_REALIZATION_PROVED    = false
ANCHOR_CONTACT_COMMON_COMPILER_PROVED             = false
CARTIER_TRACE_MACRO_NO_RESET_PROVED               = false
UNIVERSAL_JOINTLY_LEGAL_CENTRE_WORD_PROVED        = false

X037_CLEANROOM_GREEN                              = false
NEW_DECLARATIONS_PROMOTED                         = false
CERTIFIED_GRAPH_CHANGED                           = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED                = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION        = false
FORMAL_GLOBAL_STATUS                              = OPEN_GAP
```

---

# 18. Principal standard inputs and literature

1. The definition of strict transform as pullback modulo
   exceptional-supported sections, including the explicit warning that the
   strict transform depends on the chosen centre and not only on the blowup
   morphism.
2. Invariance under multiplying a centre by an effective Cartier divisor only
   under the corresponding torsion-free hypothesis.
3. Universal flattening for proper finitely presented morphisms and coherent
   sheaves.
4. Relative Serre comparison for finite graded modules and coherence/vanishing
   of projective higher direct images.
5. Raynaud--Gruson flatification and D. Rydh, *Functorial flatification of
   proper morphisms*, arXiv:2501.08394.  Smooth flatifying centres are supplied
   there only in characteristic zero, so positive-characteristic regular
   ambient realization remains part of this program.
6. A. Khan and D. Rydh, *Virtual Cartier divisors and blow-ups*, Selecta Math.
   31 (2025), Art. 67, as a possible construction guide, not a substitute for
   the ordinary scheme-level bridge.
7. The MLE--Lean baseline through X036 and the restricted Hasse--Morita core
   descent theorem.

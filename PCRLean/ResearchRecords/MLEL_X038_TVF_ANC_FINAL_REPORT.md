# MLEL-X038 / TVF-ANC

## Tor-Valabrega Factorization, Affine Normal-Cone Flatification, and Dimension-Strict Carrier Legalization

**Chinese title:** Tor-Valabrega 变换分解、仿射法锥平坦化与维数严格载体合法化  
**Protocol:** `PCR-FRACTAL-PROOF-LEAN 1.0 / MLEL-A003-FPE-EDGE`  
**Seed architecture:** `MLEL-D001 / FCPP-ATLAS`  
**Accepted mathematical parent:** `MLEL-M004 / HMC-SCCD` (restricted)  
**Experimental parent:** `MLEL-X037 / CTW-BRT`  
**Primary D001 refinement:** `G28/G29 -> G31 -> G41`, with return edges to `G18/G46/G52/G53`  
**Class:** `EXPERIMENTAL_CANDIDATE_GRAPH_REWRITE / NO_THEOREM_PROMOTION`  
**Date:** 2026-08-04  
**Global status:** `OPEN_GAP`

---

# 0. Executive verdict

This round makes three successive reductions of the passive-transform bottleneck.

1. A strict transform remembers its blowup centre, so a bare modification
   morphism is insufficient.  Centre-enriched Cartier-trace words from X037 are
   retained.
2. A single direct bifiltered comparison map is too coarse, and the first X038
   replacement by two epimorphisms to one common quotient is false.  The exact
   comparison factors through the controlled-transform graded module and has
   three typed defects.
3. The projective Rees-Serre tail is unnecessary for flatifier existence.  The
   complete passive and transform-defect portfolios are finite coherent modules
   over affine normal-cone and two-ideal mixed-Rees algebras, so general affine
   flatification applies directly.

The final local architecture is

```text
old controlled normal piece
-- alpha: Tor/base-change epimorphism -->
controlled-transform core gr_J
-- beta: Valabrega saturation map -->
new strict-carrier normal piece gr_L.
```

The three exact transform defects are

```text
ker(alpha),
ker(beta),
coker(beta).
```

A lower-dimensional affine flatifier is realized by a centre-enriched regular
word.  Every preparatory centre is recursively legalized in strictly smaller
carrier dimension.  The missing load-bearing edge is the Regular-Flag
Legal-Lift Theorem, which must show that joint legality of a flag centre kills
all three transform defects on every chart and overlap.

No arbitrary-dimensional positive-characteristic resolution theorem is proved.

---

# 1. The failed direct-map and common-cospan candidates

## 1.1 X037 direct comparison

X037 proposed an extended bifiltered Rees comparison between

```text
gr of the ambient strict transform
and
strict transform of the old associated graded.
```

This was useful as a target but did not distinguish nonexact base change from
power saturation.

## 1.2 First X038 common-cospan candidate

The first X038 candidate attempted to map the old and new transformed graded
objects epimorphically to one common quotient.  This is false.

Take

```text
B=k[q,y],
J=(q y),
L=Sat_q(J)=(y),
N=B.
```

The natural degree-one map

```text
J/J^2 -> L/L^2
```

has image `q(L/L^2)`, so it is not surjective.  Saturation-generation is a
cokernel defect independent of the intersection kernel.  The candidate graph
must therefore retain a directional factorization and three defects.

---

# 2. Relative power saturation

For a commutative ring `R`, an `R`-module `M`, a scalar `q`, and a submodule
`P`, define

```text
Sat_q(P;M) = {x in M | q^n x belongs to P for some n>=0}.
```

It is an extensive, monotone, idempotent closure operation.  Put

```text
T_q(M)=Sat_q(0;M).
```

Then

```text
T_q(M/P)=Sat_q(P;M)/P,
```

and consequently

```text
Q_q(M/P):=(M/P)/T_q(M/P) ~= M/Sat_q(P;M).
```

If multiplication by `q` is regular on `M/P`, then

```text
Sat_q(P;M)=P.
```

If multiplication by `q` is regular on `M`, then `T_q(M)=0`.

These abstract module statements are written in
`PowerSaturation.lean` without project axioms or placeholders.

---

# 3. Correct affine chart factorization

Let `A` be Noetherian, let

```text
I subset K subset A,
q in K,
B=A[K/q],
M a finite A-module.
```

Put

```text
N=M tensor_A B,
Nbar=Q_q(N).
```

The exceptional parameter `q` is regular on `Nbar`.

Let `J` be the controlled transform of the carrier ideal `I`, generated on the
`q`-chart by the divided elements `i/q`.  Let

```text
L=Sat_q(J;B)
```

be the strict-transform carrier ideal.  For every degree `a`, define

```text
Core_a = J^a Nbar/J^(a+1)Nbar,
New_a  = L^a Nbar/L^(a+1)Nbar.
```

The Cartier-twisted strict transform of the old normal piece maps
surjectively to `Core_a`:

```text
alpha_a : Old_a -->> Core_a.
```

Its kernel is the filtration-base-change/Tor defect.

The inclusion `J subset L` gives

```text
beta_a : Core_a -> New_a.
```

The exact candidate formulas are

```text
ker(beta_a)
  = (J^a Nbar intersection L^(a+1)Nbar)
      / J^(a+1)Nbar,

coker(beta_a)
  = L^a Nbar
      / (J^a Nbar + L^(a+1)Nbar).
```

They are respectively the Valabrega intersection defect and the
saturation-generation defect.

If

```text
ker(alpha_a)=0,
ker(beta_a)=0,
coker(beta_a)=0,
```

then `Old_a` and `New_a` are canonically equivalent through `Core_a`.  The
abstract linear-algebra compiler is written in
`ControlledCoreInterchange.lean`.  The scheme-level maps and kernel formulas
remain open.

---

# 4. Affine normal-cone compression

Let `I` be a finitely generated ideal of a Noetherian ring `A`, and let `M` be
finite.  Then

```text
gr_I(A)=directSum_a I^a/I^(a+1)
```

is a finite-type Noetherian algebra over `A/I`, while `gr_I(M)` is finite over
`gr_I(A)`.  Hence the complete associated-graded passive owner is one coherent
module on the affine normal cone

```text
Spec_(A/I) gr_I(A).
```

As an `A/I`-module, `gr_I(M)` is the direct sum of its homogeneous pieces.
Flatness of the complete direct sum is equivalent to flatness of every piece.
The corresponding abstract direct-sum and finite-owner portfolio compilers are
written in `BigradedFlatnessCompiler.lean`.

No projective normal bundle, Hilbert polynomial, or Serre cutoff is required to
obtain a flatifier for the complete associated-graded portfolio.

---

# 5. Two-ideal mixed-Rees compression

For finitely generated ideals `I` and `K`, define

```text
R_(I,K)(A)=directSum_(a,b>=0) I^a K^b U^a V^b,
R_(I,K)(M)=directSum_(a,b>=0) I^a K^b M U^a V^b.
```

If `f_i` generate `I` and `g_j` generate `K`, the mixed-Rees algebra is
generated by the finitely many homogeneous elements `f_i U` and `g_j V`.
The mixed-Rees module is generated in bidegree `(0,0)` by any finite generating
set of `M`.  Thus both are Noetherian finite objects.

Kernels and cokernels of homogeneous maps between finite mixed-Rees modules
are finite.  Colon chains by a homogeneous exceptional element stabilize, so
power torsion and saturation are controlled by one finite exponent across all
bidegrees.  Once the chart maps `alpha` and `beta` are constructed
homogeneously, all three transform defects form one finite affine coherent
packet.

This standard finite-generation argument removes the former projective
Rees-Serre packet from the critical path.  Its exact graded/scheme Lean
interface remains open.

---

# 6. Affine flat-kill

Let `C` be a reduced Noetherian regular carrier.  Form the finite direct sum of

```text
all passive associated-graded owner modules,
all ker(alpha), ker(beta), coker(beta) modules,
log-conormal defects,
source-Cartier torsion,
anchor-contact transform defects.
```

This is one finite coherent module on an affine finite-type normal/mixed-Rees
scheme over `C`.

Let `U subset C` meet the generic point of every irreducible component and be
the locus where the desired legality already holds.  A `U`-admissible
flatifying blowup makes the strict transform of the packet finitely presented
and flat.  Every defect summand is zero over `U`; a finitely presented flat
module of rank zero on a componentwise dense open is zero.  Thus flatification
kills the three generically zero transform defects and makes the complete
passive portfolio flat.

The theorem providing an admissible possibly singular flatifier is a standard
input.  The project-specific task is to realize it by ordinary ambient blowups
in regular, recursively legal centres.

---

# 7. Regular-flag legal lift

Consider a flag of regular immersions

```text
D subset C subset X.
```

Etale-locally in a regular ambient ring one has a regular sequence presentation

```text
I_C=(x_1,...,x_r),
I_D=(x_1,...,x_r,y_1,...,y_s).
```

In the blowup of `D`, only the `y_j`-charts meet the strict transform of `C`.
On the `y_1`-chart,

```text
x_i=y_1 x_i',
y_j=y_1 y_j'  (j>1),
```

and the strict carrier ideal is `(x_1',...,x_r')`.  Thus the controlled carrier
ideal is already power-saturated in the regular-flag chamber, and the conormal
bundle differs from the pullback of the old conormal bundle only by the
canonical exceptional line twist.

The missing theorem is:

> If `D` is jointly legal for the complete affine normal-cone/Rees portfolio of
> `(C,M)`, then after blowing up `X` in `D`, the strict transform satisfies
>
> ```text
> gr_(C')(M')
>   ~= StrictTransform_D(gr_C(M)) tensor grading twist
> ```
>
> on every chart and overlap, and all three Tor-Valabrega defects vanish.

The local ideal normal form is standard.  The finite owner-module transform,
overlap, base-change, source, and boundary statements remain open.

---

# 8. Dimension-strict carrier legalization

Define `Legalize_n(d)` for regular carriers of dimension at most `d` in an
`n`-dimensional regular ambient scheme.

```text
Legalize_n(d):
  1. construct the finite affine legality packet on C;
  2. choose one centre-enriched admissible flatifier of C;
  3. factor it through a lower-dimensional regular word on C;
  4. for every word centre D with dim D<d, invoke Legalize_n(dim D);
  5. execute the resulting jointly legal ambient trace blowup;
  6. transport the carrier packet by the Regular-Flag Legal-Lift Theorem;
  7. continue the immutable source-labelled word;
  8. output the flat, Tor-safe, SNC-compatible strict transform of C.
```

No repeated same-dimensional re-flatification is allowed.  The carrier
flatifier is chosen once; all subsequent recursion occurs on strictly smaller
carriers.  The arithmetic backend for the order

```text
carrier dimension
> unresolved transform defects
> contact
> debt
```

is written in `FlatKillLegalizationRank.lean`.  The geometric strict-drop and
factorization theorems remain open.

---

# 9. Final candidate graph

```text
finite intrinsic Frobenius-Hasse/conormal state
-> finite minimizer intersection arrangement
-> raw regular carrier C

complete finite affine normal/mixed-Rees legality packet
-> one centre-enriched admissible flatifier on C
-> lower-dimensional regular word factoring through it
-> recursively legalize every regular trace subcentre D
-> ordinary ambient trace blowups

at each regular-flag edge:
  Old --alpha>> gr_J --beta-> gr_L
  joint legality kills ker alpha, ker beta, coker beta
  exact transform interchange

end of word:
  passive normal flatness
  Tor safety
  logarithmic/SNC legality
  active marked permissibility
  nonidentity

regular-support contact:
  anchor ideals
  same carrier compiler
  residual Cartier contact cleaning

clean arrangement:
  maximal wonderful word
  legalize every word centre
  all-chart Cartier-stable hereditary reentry
  dimension-strict plus global causal termination
  finite global ordinary word.
```

---

# 10. Exact frontier

```text
X038-G1   affine strict-transform power-torsion scheme API
X038-G3   controlled transform J and strict carrier ideal L=Sat_q(J)
X038-G4   homogeneous alpha and Tor-kernel presentation
X038-G5   homogeneous beta with intersection/cokernel formulas
X038-G7B  exact mixed-Rees graded/scheme interface
X038-G9   overlaps and smooth base change
X038-G10  generic vanishing of all three defects
X038-G12  flat generically-zero vanishing in the required scheme scope
X038-G13  centre-enriched regular word factoring through the flatifier
X038-G14  recursive joint legalization of every trace subcentre
X038-G15  ambient trace realization and transform transport
X038-G16  anchor contact through the same compiler
X038-G17  log conormal through the same compiler
X038-G18  Cartier-stable source compression and no reset
X038-G19  geometric dimension-strict termination
X038-G20  universal actual jointly legal centre word
RFL-A      regular-flag legal-lift theorem.
```

The highest-information cut is

```text
scheme-level alpha/beta and mixed-Rees overlap package
+
Regular-Flag Legal-Lift
+
centre-enriched regular factorization of the flatifier
+
Cartier-stable all-chart no-reset.
```

---

# 11. Exact Lean slice

```text
PowerSaturation.lean
ControlledCoreInterchange.lean
BigradedFlatnessCompiler.lean
FlatKillLegalizationRank.lean
X038TorValabregaCommonCoreIndex.lean
X038TorValabregaCommonCoreIndexAudit.lean
```

The slice proves only:

1. relative power saturation is an extensive, monotone, idempotent submodule
   closure;
2. quotient power torsion is exactly relative saturation modulo the original
   submodule;
3. regularity of the exceptional scalar on a quotient kills new saturation;
4. a regular exceptional scalar creates no power torsion;
5. an abstract Tor epimorphism followed by a zero-kernel/full-range
   controlled-to-new map yields a canonical equivalence;
6. total bigraded and finite-owner portfolio flatness compile from the
   homogeneous pieces;
7. the proposed dimension/defect/contact/debt order is well founded.

The files do not construct any scheme-level transform or flatifier.

---

# 12. Annals-series maximum-likelihood estimate

The projective-tail deletion saves ten to twelve pages; the exact
Tor-Valabrega factorization and regular-flag compiler reintroduce several pages
of chart algebra.  The central estimate is **552 dense
Annals/AMS-equivalent pages**.

| Paper | Maximum-likelihood title | Pages |
|---:|---|---:|
| I | Intrinsic Frobenius-Hasse States, Affine Conormal Packets, and Projectivity Discriminants | 90 |
| II | Anchor-Contact Ideals, Cartier-Trace Words, and Wonderful Actual-Centre Synthesis | 118 |
| III | Affine Normal-Cone Flatification, Tor-Valabrega Factorization, and Hereditary Reentry | 134 |
| IV | Source-Debt Causality, Recurrent Classes, and Dimension-Strict Termination | 84 |
| V | Global Descent, Symmetry-Compatible Serialization, and Principalization | 78 |
| VI | Functorial Resolution, Counterexample Closure, and Lean Reproducibility | 48 |
|  | **Total** | **552** |

A one-volume editorial edition with theorem-interface cards, the source and
Cartier ledger, affine normal/mixed-Rees chart compendium, proof DAG,
counterexample atlas, and paper-to-Lean map is estimated at **600--635 physical
pages**.

Subjective publication-form planning weights:

```text
six papers                                      0.64
seven papers, splitting transform factorization 0.18
five papers after consolidation                 0.11
other                                           0.07
```

These are planning weights, not calibrated probabilities.

---

# 13. Modal decisive theorem

> **Affine Normal-Cone Tor-Valabrega Factorization and Recursive Carrier
> Legalization Theorem.**  Let a prepared marked state on a smooth
> `n`-dimensional scheme over a perfect field of characteristic `p>0` produce a
> finite symmetry-stable family of regular raw carriers.  Assume strong
> relative principalization and the same carrier-legalization theorem in
> dimensions `<n`.  For every carrier, all passive associated-graded modules,
> logarithmic defects, source-Cartier modules, and Tor-Valabrega transform
> defects form one finite coherent graded module on an affine finite-type
> normal/mixed-Rees scheme over the carrier.  A componentwise admissible
> flatifying blowup makes this complete packet finitely presented and flat.
>
> The flatifier factors through a finite centre-enriched word of ordinary
> ambient blowups in regular trace centres, each recursively legalized on a
> strictly lower-dimensional carrier.  For every regular flag formed by a word
> centre inside the current carrier, joint legality gives an all-chart
> Cartier-twist-compatible factorization from the old controlled normal module
> through the controlled core to the new strict-carrier normal module.  The Tor
> kernel, Valabrega intersection kernel, and saturation-generation cokernel
> vanish.  Hence the transformed carrier is active-permissible, normally flat
> and Tor-safe for every passive owner, and SNC-compatible with the total
> boundary.  Certified Cartier factors may then be compressed without changing
> strict transforms.  All owner, source, debt, boundary, contact, flatifier,
> and controlled-core identities reenter without reset.  Every nested
> legalization call strictly lowers carrier dimension, and every outer macro
> lowers the global causal rank.

This theorem is a maximum-likelihood target.  It is not established.

---

# 14. Truth boundary

```text
ROUND_ID                                           = MLEL-X038 / TVF-ANC

STRICT_TRANSFORM_CENTRE_DEPENDENCE_RETAINED        = true
DIRECT_BIFILTERED_RID_REJECTED                     = true
TWO_EPIMORPHISM_COSPAN_REJECTED                    = true
FALSE_COSPAN_COUNTEREXAMPLE_RECORDED               = true
CONTROLLED_CORE_FACTORIZATION_IDENTIFIED           = true
THREE_TRANSFORM_DEFECTS_IDENTIFIED                 = true
AFFINE_NORMAL_CONE_COMPRESSION_IDENTIFIED          = true
PROJECTIVE_REES_SERRE_TAIL_REQUIRED                = false
REGULAR_FLAG_LEGAL_LIFT_IDENTIFIED                 = true
DIMENSION_STRICT_CARRIER_COMPILER_IDENTIFIED       = true

POWER_SATURATION_LEAN_SOURCE_WRITTEN               = true
CONTROLLED_CORE_COMPILER_LEAN_SOURCE_WRITTEN       = true
BIGRADED_FLATNESS_LEAN_SOURCE_WRITTEN              = true
DIMENSION_STRICT_RANK_LEAN_SOURCE_WRITTEN          = true

SCHEME_LEVEL_ALPHA_BETA_PROVED                     = false
MIXED_REES_OVERLAP_PACKET_PROVED                   = false
REGULAR_FLAG_LEGAL_LIFT_PROVED                     = false
REGULAR_AMBIENT_REALIZATION_OF_FLATIFIER_PROVED    = false
CARTIER_STABLE_ALL_CHART_NO_RESET_PROVED           = false
UNIVERSAL_JOINTLY_LEGAL_CENTRE_WORD_PROVED         = false

X038_CLEANROOM_GREEN                               = false
NEW_DECLARATIONS_PROMOTED                          = false
CERTIFIED_GRAPH_CHANGED                            = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED                 = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION         = false
FORMAL_GLOBAL_STATUS                               = OPEN_GAP
```

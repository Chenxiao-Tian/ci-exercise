# MLEL-X038 / TVC-FKL

## Tor-Valabrega Common Cores, Flat-Kill Legalization, and Cartier-Stable Reentry

**Chinese title:** Tor-Valabrega 共同核、平坦消灭合法化与 Cartier 稳定重入  
**Protocol:** `PCR-FRACTAL-PROOF-LEAN 1.0 / MLEL-A003-FPE-EDGE`  
**Seed architecture:** `MLEL-D001 / FCPP-ATLAS`  
**Accepted mathematical parent:** `MLEL-M004 / HMC-SCCD` (restricted)  
**Experimental parent:** `MLEL-X037 / CTW-BRT`  
**Primary D001 refinement:** `G28/G29 -> G31 -> G41`, with return edges to `G18/G46/G52/G53`  
**Class:** `EXPERIMENTAL_CANDIDATE_GRAPH_REFINEMENT / NO_THEOREM_PROMOTION`  
**Date:** 2026-08-04  
**Global status:** `OPEN_GAP`

---

# 0. Executive verdict

X037 corrected the morphism-only flatification proposal: strict and pure
transforms remember the chosen centre, even when a Cartier centre induces the
identity carrier morphism.  It then proposed a direct bifiltered comparison
map and an undifferentiated Rees interchange defect.

The present round makes a second correction.  A speculative direct map is not
the primitive object.  On every affine blowup chart the two transformed graded
objects admit canonical **surjections to a common image-filtration core**:

```text
new normal graded piece, with Cartier twist  -->>  common core
old graded piece after chart pullback        -->>  common core.
```

The two kernels have different meanings:

```text
left kernel   = exceptional power-saturation / Valabrega-type defect;
right kernel  = nonexact filtration base change / Tor defect.
```

Thus

```text
one mysterious RID
```

is replaced by

```text
Tor defect + Valabrega saturation defect + a canonical common core.
```

When both kernels vanish, no arbitrary inverse or comparison choice is needed:
the two surjections are equivalences and produce the desired interchange
isomorphism through the common core.

The second refinement is a **flat-kill principle**.  The finite coherent
Tor-Valabrega packet is enrolled in the passive portfolio.  A
lower-dimensional, centre-enriched flatification/principalization word makes
its strict transform flat.  Since the packet is generically zero, flatness over
a reduced carrier forces the transformed packet to be zero.  Every preparatory
centre is itself legalized recursively on a strictly lower-dimensional carrier.

This does not yet prove the scheme-level packet, the ambient trace comparison,
hereditary no-reset, or the general resolution theorem.  It gives a more exact
and substantially smaller load-bearing bridge.

---

# 1. Why the X037 direct comparison should be replaced

Let `A` be a Noetherian affine ambient ring, let

```text
I subset K subset A,
M a finite A-module,
q in K,
B = A[K/q]
```

be one standard chart of the blowup in `K`.  The ideal `I` defines a carrier
`C`, and `K/I` defines the induced centre on `C`.

Put

```text
N = M tensor_A B,
T_q(N) = {x in N | q^n x = 0 for some n},
N^str = N / T_q(N).
```

Strict transform on this chart is precisely quotient by `q`-power torsion.
For the old `I`-adic filtration define

```text
F_a = image(I^a M tensor_A B -> N),
barG_a = F_a/F_(a+1),
G_a = (I^a M/I^(a+1)M) tensor_A B.
```

There is a canonical surjection

```text
rho_a : G_a -->> barG_a.
```

It need not be an isomorphism because the chart algebra is not generally flat
over `A`.  Its kernel is the filtration-base-change defect and is controlled by
the Tor kernels of

```text
I^a M tensor_A B -> M tensor_A B.
```

The second obstruction is that quotienting by `q`-power torsion is not left
exact on arbitrary short exact sequences.  Therefore neither side should be
identified with the other before these two failures are separated.

---

# 2. Relative power saturation

For a submodule `P subset N`, define

```text
Sat_q(P;N) = {x in N | q^n x belongs to P for some n}.
```

Then

```text
T_q(N/P) = Sat_q(P;N)/P
```

and hence

```text
Q_q(N/P)
  := (N/P)/T_q(N/P)
  ~= N/Sat_q(P;N).
```

This is an elementary exact identity.  It is the local algebraic meaning of
strict transform on a chart.

The new Lean file `PowerSaturation.lean` proves the corresponding abstract
module statements:

```text
powerSaturation is extensive, monotone, and idempotent;
a quotient class is q-power torsion iff its representative lies in Sat_q;
Sat_q(P;N)=P iff every q-power-torsion quotient class is already zero.
```

Noetherianity implies that for finite `N/P` the ascending chain

```text
(0 : q) <= (0 : q^2) <= ...
```

stabilizes.  Thus each local saturation defect is killed by one bounded power
of `q` and is finite.

---

# 3. The right-hand Tor/base-change map

Apply `Q_q` to `rho_a`.  Since `rho_a` is surjective, so is

```text
R_a : Q_q(G_a) -->> Q_q(barG_a).
```

Define

```text
C_a = Q_q(barG_a).
```

The right defect is

```text
TVD^Tor_a = ker(R_a).
```

More explicitly,

```text
ker(R_a)
 = rho_a^(-1)(T_q(barG_a))
   /
   (ker(rho_a) + T_q(G_a)).
```

Thus it records both raw nonexact base change and the additional saturation
needed after the chart exceptional parameter is introduced.

The raw kernel `ker(rho_a)` has a finite Tor presentation.  One may obtain it
from the two exact sequences

```text
0 -> I^a M -> M -> M/I^a M -> 0
```

and the inclusions for consecutive filtration levels.  The exact preferred
presentation is part of the future scheme/Lean interface; the finite kernel
itself is canonical and presentation independent.

---

# 4. The left-hand Valabrega/saturation map

Let `L` be the transformed carrier ideal on the chart.  After removing
`q`-power torsion from the chart ring and module, one has the chart relation

```text
I B = q L.
```

Consequently

```text
F_a = q^a L^a N
```

before quotienting torsion.  The degree-`a` normal graded piece of the strict
transform, with its Cartier line twist, is locally represented by

```text
A_a = (L^a N^str/L^(a+1)N^str) tensor O(-aE).
```

Multiplication by `q^a` gives a canonical surjection

```text
L_a : A_a -->> C_a.
```

Well-definedness is exactly where saturation enters.  An element from
`L^(a+1)N^str` becomes, after multiplication by `q^a`, a class whose next
multiplication by `q` lies in `F_(a+1)`; it is therefore zero in
`Q_q(F_a/F_(a+1))`.

Define the left defect

```text
TVD^VV_a = ker(L_a).
```

It is a relative Valabrega-type module: it measures the failure of the next
filtration piece to be `q`-saturated inside the current piece.  In a torsionfree
chart model it has the form

```text
Sat_q(F_(a+1);F_a)
/
q^a L^(a+1)N^str,
```

with the exact denominator adjusted by the chart torsion and Cartier twist.

The terminology is structural rather than an assertion that this is literally
the original one-ideal Valabrega-Valla module.  The classical module

```text
directSum_n (I^(n+1) intersection J)/(J I^n)
```

is the model: vanishing expresses strict compatibility between a filtration
and a quotient/regular-sequence operation.  X038 uses the analogous
power-saturated mixed-filtration obstruction.

---

# 5. The Tor-Valabrega common-core theorem on one chart

The exact candidate statement is now:

> **Affine Common-Core Interchange.**  For every degree `a` on every standard
> trace-blowup chart there are canonical surjections
>
> ```text
> L_a : A_a -->> C_a,
> R_a : Q_q(G_a) -->> C_a,
> ```
>
> where `C_a=Q_q(F_a/F_(a+1))`.  Their kernels are respectively the
> Valabrega/saturation and Tor/base-change defects.  If both kernels vanish,
> there is a unique linear equivalence
>
> ```text
> A_a ~= Q_q(G_a)
> ```
>
> compatible with both maps to `C_a`.

The abstract final implication is already written in
`CommonCoreInterchange.lean`: two surjections with zero kernels induce a
canonical equivalence through their common codomain.

This theorem avoids the direction ambiguity in X037.  There is no need to
postulate a direct comparison and then take both its kernel and cokernel.  The
canonical data are two epimorphisms and two kernels.

---

# 6. Minimal models

## 6.1 Transverse flat model

Take

```text
A=k[x,z], I=(x), K=(x,z), M=A.
```

On the `z`-chart, write `x=zs`.  The strict transform carrier has ideal `(s)`.
The old degree-one conormal generator `x` and the new generator `s` differ by
the Cartier factor `z`.  After the line twist, both maps to the common core
`k[z]`.  Both Tor-Valabrega kernels vanish.

## 6.2 Passive torsion model

Take the same `A,I,K` and

```text
M=A/(z).
```

Every old normal graded piece is `k[z]/(z)` and is not flat over the carrier.
The ambient trace blowup separates the strict transform of `M` from the strict
transform of the carrier.  The bad packet is killed, but this occurs precisely
through exceptional torsion; a morphism-only carrier identity does not record
it.

## 6.3 Tangent-curve contact model

For

```text
(y), (y-x^m) in k[x,y]
```

the anchor contact ideal is `(x^m)`.  On the ambient point blowup one
exceptional factor is divided out, giving contact order `m-1`.  In common-core
language, the class killed by one exceptional multiplication is a nontrivial
saturation class before cleaning and disappears after the Cartier-trace step.

## 6.4 Flat tail but bad low piece

A projective-normal sheaf may have a flat eventual projective tail while a
finite low associated-graded piece remains nonflat.  Therefore the common-core
packet must retain both the finite transition window and the projective tail;
flatness of the sheafification alone is insufficient.

---

# 7. Global finite packet

For a finite passive portfolio and one source-labelled carrier ideal, define
formally

```text
TVC = direct sum over owners and degrees of
      (TVD^Tor_a directSum TVD^VV_a).
```

This infinite-looking object is expected to be finite for two reasons.

1. The mixed Rees module

   ```text
   directSum_(a,b) I^a K^b M
   ```

   is finite over the corresponding two-ideal Rees algebra in the Noetherian
   finite-module setting.
2. Relative Serre comparison splits the degrees into a finite low window and a
   coherent tail on the projectivized normal bundle.

The required scheme theorem must produce:

```text
uniform cutoff N,
finite low Tor/VV kernels,
bounded irrelevant and q-power torsion,
coherent projective Tor/VV tail,
overlap cocycles,
flat-base-change maps,
and source-labelled Cartier twists.
```

This is not yet proved.  It is a more precise replacement for the X037
undifferentiated RID packet.

---

# 8. The flat-kill lemma

The geometric principle is elementary once the defect packet exists.

> **Flat-Kill Lemma.**  Let `S` be reduced and Noetherian, let `U subset S`
> contain the generic point of every irreducible component, and let `F` be a
> finite-type coherent sheaf on a quasi-compact finitely presented `X->S` with
> `F|_U=0`.  Suppose a `U`-admissible blowup `S'->S` makes the strict transform
> `F^str` finitely presented and flat over `S'`.  If the inverse image of `U`
> is dense in every component of `S'`, then `F^str=0`.

Indeed a finitely presented flat module is locally free.  Its rank is locally
constant, and it has rank zero on a dense open meeting every component.
Therefore it has rank zero everywhere.

Apply this to the direct sum of the finite Tor-Valabrega defect packet and the
finite projective-normal legality packet.  A single simultaneous flatifier
makes the target pieces flat and kills every generically zero defect.

The existence of a flatifying blowup is standard under the usual
quasi-compactness, finite-presentation, and flat-on-`U` hypotheses.  The
positive-characteristic problem is not existence of a possibly singular
flatifier; it is its realization by a finite word of ordinary ambient blowups
in regular, already-legal centres.

---

# 9. Dimension-strict ambient realization

Let `C` be a regular raw carrier of dimension `d`.  A flatifier ideal is
supported in the closed bad locus, hence its support has dimension `<d` on
each relevant component.

Use lower-dimensional principalization/resolution to replace the flatifier by
a centre-enriched regular word on `C`.  Before lifting each regular subcentre
`D subset C` to the ambient scheme, legalize `D` recursively with the enlarged
portfolio containing:

```text
active owners,
passive owners,
projective-normal pieces,
Tor defects,
Valabrega defects,
log-conormal defects,
source and debt ledgers.
```

Since

```text
dim D < dim C < dim X,
```

this nested legalization is dimension-strict.  The internal recursion cannot
return to the same carrier dimension.  Once each subcentre is jointly legal,
its ambient trace blowup is allowed by the final theorem semantics.

The Lean file `FlatKillLegalizationRank.lean` proves only the arithmetic backend
for the proposed ordering

```text
carrier dimension
> unresolved TVC defects
> contact
> exceptional debt.
```

The geometric strict-drop theorem remains open.

---

# 10. Cartier-stable reentry after flat-kill

After the projective-normal and TVC packets are flat, every relevant module is
torsionfree with respect to a Cartier boundary equation on the reduced regular
carrier.  Consequently multiplication of a later centre ideal by an effective
Cartier boundary factor does not change its strict transform, provided the
precise torsion-free hypothesis is carried.

This suggests a substantial compression of the source ledger:

```text
before flat-kill:
  retain every centre source and Cartier-trace payload;

after flat-kill:
  identify source words differing only by certified Cartier factors.
```

The quotient is not a presentation normalization.  It is allowed only after a
proof that the relevant Cartier torsion packet is zero.  The future no-reset
theorem must preserve the certificate and forbid reintroduction of the erased
Cartier torsion.

---

# 11. Corrected candidate graph

```text
prepared intrinsic state
-> finite minimizer intersection arrangement
-> raw regular carrier C

PROJECTIVE-NORMAL / LOG PACKET
-> finite low pieces + coherent projective tail
-> source-labelled flatifier ideals on C

CENTRE-ENRICHED REALIZATION
-> lower-dimensional simultaneous principalization
-> recursively legalize every regular subcentre
-> lift canonical ambient trace centres
-> retain residual Cartier-trace steps

ON EVERY TRACE-BLOWUP CHART
-> image filtration F_a
-> common core C_a = Q_q(F_a/F_(a+1))
-> right Tor/base-change epimorphism
-> left Valabrega/saturation epimorphism
-> finite TVC packet

FLAT-KILL
-> simultaneous flatification of projective-normal + TVC packet
-> generically zero flat TVC packet vanishes
-> canonical ambient/normal interchange
-> passive normal flatness, Tor safety, and log legality

REGULAR-SUPPORT CONTACT
-> anchor-contact ideals
-> the same centre-enriched TVC compiler
-> residual monomial Cartier cleaning

CLEAN ARRANGEMENT
-> maximal wonderful word
-> legalize each word centre by the same dimension-strict compiler
-> Cartier-stable all-chart reentry without reset
-> finite global ordinary word.
```

---

# 12. Exact open frontier after X038

```text
X038-G1   AFFINE_STRICT_TRANSFORM_POWER_TORSION_API
X038-G2   RELATIVE_POWER_SATURATION_AND_QUOTIENT_IDENTITY
X038-G3   CHART_IMAGE_FILTRATION_AND_TRANSFORMED_CARRIER_IDEAL
X038-G4   TOR_BASE_CHANGE_EPIMORPHISM_AND_KERNEL_PRESENTATION
X038-G5   VALABREGA_SATURATION_EPIMORPHISM_AND_KERNEL_FORMULA
X038-G6   TOR_VALABREGA_COMMON_CORE_COSPAN
X038-G7   MIXED_REES_FINITE_PRESENTATION_AND_UNIFORM_CUTOFF
X038-G8   PROJECTIVE_TVC_TAIL_AND_SERRE_COMPARISON
X038-G9   OVERLAP_COCYCLES_AND_SMOOTH_BASE_CHANGE
X038-G10  GENERIC_VANISHING_OF_THE_TVC_PACKET
X038-G11  SIMULTANEOUS_PROJECTIVE_NORMAL_TVC_FLATIFICATION
X038-G12  FLAT_GENERICALLY_ZERO_IMPLIES_ZERO_ON_EVERY_COMPONENT
X038-G13  REGULAR_CENTRE_WORD_FACTORING_THROUGH_THE_FLATIFIER
X038-G14  RECURSIVE_JOINT_LEGALIZATION_OF_EVERY_TRACE_SUBCENTRE
X038-G15  AMBIENT_TRACE_REALIZATION_AND_COMMON_CORE_TRANSPORT
X038-G16  ANCHOR_CONTACT_AS_THE_SAME_TVC_COMPILER
X038-G17  LOG_CONORMAL_AS_THE_SAME_TVC_COMPILER
X038-G18  CARTIER_STABLE_SOURCE_COMPRESSION_AND_NO_RESET
X038-G19  DIMENSION_STRICT_LEGALIZATION_TERMINATION
X038-G20  UNIVERSAL_ACTUAL_JOINTLY_LEGAL_CENTRE_WORD
```

The highest-information cut is now

```text
X038-G6/G7
+ X038-G11/G14/G15
+ X038-G18/G19.
```

`G2` and the abstract vanishing-to-equivalence compiler are Lean-sized leaves.
The genuinely new project mathematics lies in globalizing the two kernels,
realizing the flatifier by recursively legal ambient trace centres, and proving
Cartier-stable hereditary reentry.

---

# 13. Lean source written in this round

```text
PowerSaturation.lean
CommonCoreInterchange.lean
FlatKillLegalizationRank.lean
X038TorValabregaCommonCoreIndex.lean
X038TorValabregaCommonCoreIndexAudit.lean
```

The exact slice proves only:

1. relative power saturation is a closure operation;
2. quotient `q`-power torsion is exactly relative saturation modulo the
   original submodule;
3. saturation is trivial exactly when every power-torsion quotient class is
   zero;
4. two surjections to a common core with vanishing kernels produce a canonical
   linear equivalence;
5. dimension, defect, contact, and debt drops are strict in the proposed
   well-founded rank.

No scheme-level Tor-Valabrega cospan is claimed by these declarations.

---

# 14. Counterexample and stress-test ledger

```text
TVC-1   Cartier identity blowup with fully supported torsion
TVC-2   Cartier identity blowup with Cartier-torsion-free module
TVC-3   transverse nested regular centres with zero TVC packet
TVC-4   passive crossing-axes module with nonflat normal pieces
TVC-5   tangent curves with contact m -> m-1
TVC-6   nonflat chart base change with nonzero right Tor kernel
TVC-7   q-saturation failure with zero raw base-change kernel
TVC-8   flat projective tail but nonflat low piece
TVC-9   two source ideals exchanged by symmetry
TVC-10  normalization or cleaning that erases a Cartier source certificate
TVC-11  defect supported on one component but not another
TVC-12  a flatifier whose centre is singular and must be dominated in lower
        dimension by regular centres.
```

Any proposed theorem that replaces the common cospan by a direct equality,
forgets the low window, or deletes carrier-Cartier identity steps fails one of
these tests.

---

# 15. Annals-series maximum-likelihood estimate

The common-core decomposition removes part of the speculative bifiltered-Rees
machinery, but adds a precise mixed-Rees/Tor-Valabrega chapter.  The current
central estimate is **560 dense Annals/AMS-equivalent pages**.

| Paper | Maximum-likelihood title | Pages |
|---:|---|---:|
| I | Intrinsic Frobenius-Hasse States, Affine Conormal Packets, and Projectivity Discriminants | 90 |
| II | Anchor-Contact Ideals, Cartier-Trace Words, and Wonderful Actual-Centre Synthesis | 118 |
| III | Tor-Valabrega Common Cores, Projective-Normal Flatification, and Hereditary Reentry | 142 |
| IV | Source-Debt Causality, Recurrent Classes, and Dimension-Strict Termination | 84 |
| V | Global Descent, Symmetry-Compatible Serialization, and Principalization | 78 |
| VI | Functorial Resolution, Counterexample Closure, and Lean Reproducibility | 48 |
|  | **Total** | **560** |

A one-volume editorial edition with theorem-interface cards, the source/Cartier
ledger, mixed-Rees chart compendium, proof DAG, counterexample atlas, and
paper-to-Lean map is estimated at **610--645 physical pages**.

Subjective publication-form planning weights:

```text
six papers                                    0.60
seven papers, splitting common-core theory    0.23
five papers after consolidation               0.10
other                                         0.07
```

These are research-planning weights, not calibrated probabilities.

---

# 16. Modal decisive theorem

> **Tor-Valabrega Common-Core Flat-Kill Theorem.**  Let a prepared marked
> state on an `n`-dimensional smooth scheme over a perfect field of
> characteristic `p>0` produce a finite symmetry-stable family of regular raw
> carriers.  Assume strong relative principalization and the same legalization
> theorem in dimensions `<n`.  For every finite source-labelled family of
> passive flatifier, anchor-contact, and logarithmic carrier ideals there is a
> centre-enriched word of ordinary ambient blowups in regular trace centres.
> On every standard chart and in every normal degree, the ambient strict
> transform and the carrier projective-normal pure transform admit canonical
> epimorphisms to one common image-filtration core.  The two kernels form a
> finite Tor-Valabrega packet, compatible with overlaps and smooth base change.
> A simultaneous lower-dimensional flatification of the projective-normal and
> Tor-Valabrega packets, realized recursively by jointly legal ambient trace
> centres, makes the former flat and kills the latter.  The resulting carrier
> is simultaneously active-permissible, normally flat and Tor-safe for all
> passive owners, and SNC-compatible with the total boundary.  Certified
> Cartier factors may then be compressed without changing strict transforms.
> Every owner, source, debt, boundary, contact, flatifier, and common-core
> identity reenters without reset.  Every nonterminal nested legalization
> strictly lowers carrier dimension, and every outer macro lowers the global
> dimension/phase/contact/Fitting/source-debt/SCC rank.

This is the current maximum-likelihood theorem target.  It is not an
established theorem.

---

# 17. Truth boundary

```text
ROUND_ID                                           = MLEL-X038 / TVC-FKL

X037_EXPERIMENTAL_CLEANROOM_GREEN                 = true
X037_DECLARATIONS_PROMOTED                        = false

DIRECT_RID_REPLACED_BY_COMMON_CORE                = true
TOR_AND_VALABREGA_KERNEL_TYPES_IDENTIFIED         = true
POWER_SATURATION_LEAN_SOURCE_WRITTEN               = true
COMMON_CORE_COMPILER_LEAN_SOURCE_WRITTEN           = true
DIMENSION_STRICT_RANK_LEAN_SOURCE_WRITTEN          = true

AFFINE_SCHEME_COMMON_CORE_THEOREM_PROVED           = false
MIXED_REES_FINITE_TVC_PACKET_PROVED                = false
PROJECTIVE_TVC_OVERLAP_BASE_CHANGE_PROVED          = false
REGULAR_AMBIENT_REALIZATION_OF_FLATIFIER_PROVED    = false
TVC_FLAT_KILL_AMBIENT_INTERCHANGE_PROVED           = false
CARTIER_STABLE_MACRO_NO_RESET_PROVED               = false
UNIVERSAL_JOINTLY_LEGAL_CENTRE_WORD_PROVED         = false

X038_CLEANROOM_GREEN                               = false
NEW_DECLARATIONS_PROMOTED                          = false
CERTIFIED_GRAPH_CHANGED                            = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED                 = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION         = false
FORMAL_GLOBAL_STATUS                               = OPEN_GAP
```

---

# 18. Principal standard inputs and literature

1. The Stacks Project, Section 31.34: strict transform is pullback modulo
   exceptional-supported sections; on affine blowup charts this is quotient by
   power torsion; strict transform depends on the chosen centre.
2. The Stacks Project, Lemma 31.34.7: universally exact short exact sequences
   remain exact after strict transform.
3. The Stacks Project, Theorem 38.30.7: flatification of finite-type
   quasi-coherent modules by an admissible blowup under finite-presentation and
   flat-on-an-open hypotheses.
4. P. Valabrega and G. Valla, *Form rings and regular sequences*, Nagoya Math.
   J. 72 (1978), 93--101, as the classical filtration-intersection model.
5. D. Rydh, *Functorial flatification of proper morphisms*, arXiv:2501.08394,
   for modern functorial proper flatification; regular/smooth flatifying centres
   in positive characteristic are not supplied by that theorem and remain part
   of the present ambient-realization program.
6. The MLE-Lean baseline through X037 and the restricted Hasse-Morita core
   descent theorem.

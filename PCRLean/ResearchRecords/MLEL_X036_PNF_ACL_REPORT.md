# MLEL-X036 / PNF-ACL

## Projective-Normal Flatification, Anchor-Contact Principalization, and Ambient Legalization

**Chinese title:** 射影法平坦化、锚–接触主理想化与环境合法化  
**Protocol:** `PCR-FRACTAL-PROOF-LEAN 1.0 / MLEL-A003-FPE-EDGE`  
**Seed architecture:** `MLEL-D001 / FCPP-ATLAS`  
**Accepted mathematical parent:** `MLEL-M004 / HMC-SCCD` (restricted)  
**Experimental parent:** `MLEL-X035 / STD-ALI`  
**Primary D001 refinement:** `G26 -> G28/G29/G30 -> G31 -> G41`, with a new lower-dimensional return edge to `G61` and `G53`  
**Class:** `EXPERIMENTAL_CANDIDATE_GRAPH_REFINEMENT / NO_THEOREM_PROMOTION`  
**Date:** 2026-08-04  
**Global status:** `OPEN_GAP`

---

# 0. Executive verdict

X035 isolated the load-bearing cut

```text
FINITE_REES_SERRE_PASSIVE_PACKET
PASSIVE_AND_LOG_SNC_AMBIENT_LIFT
NILPOTENT_CONTACT_STRICT_TRANSFORM_DESCENT
JOINT_DEFECT_MACRO_NO_RESET.
```

The present round changes the logical shape of this cut.  Passive normal
flatness and regular-support contact should not be treated as mysterious
properties that one lucky centre must satisfy at the moment it is selected.
They are lower-dimensional **legalization problems on the proposed centre and
on the regular anchors**.

The new macro is

```text
raw regular candidate C
-> finite projective-normal passive packet on C
-> flatifying modification of C
-> regular word dominating that modification
-> ambient lift of the word
-> strict transform C' jointly legal
-> blow up C'.
```

For a nonregular intersection with regular reduced support, the second macro is

```text
finite regular anchor family {Z_i}
-> contact ideals D_i on Z_i
-> lower-dimensional principalization of D_i
-> ambient lift
-> monomial contact cleaning
-> empty or clean transformed intersection.
```

Thus the genuinely new theorem is no longer a universal scalar thickness
invariant.  It is an **ambient dominating-modification lift theorem** coupling
projective-normal pure transforms, controlled contact transforms, boundary
conormal data, and hereditary ledgers.

---

# 1. A necessary correction to the X035 finite-joint-discriminant language

Finite obstruction modules can be fused by zeroth Fitting ideals.  Active,
cotangent, conormal-excess, projectivity, and action defects therefore admit one
finite coherent discriminant.

Passive normal flatness is different.  Let `C -> X` be a regular immersion,
put

```text
A = O_C,
E = I_C/I_C^2,
S = Sym_A(E),
G(M) = gr_{I_C}(M).
```

The requirement is that the infinite graded `A`-module

```text
G(M)=directSum_n G(M)_n
```

be flat.  There is a maximal open locus on which a finitely presented
projective-normal sheaf is flat, and there are finite flattening
stratifications or universal flattening monomorphisms in the relevant proper
setting.  There is not, in general, one canonical closed ideal whose complement
represents arbitrary-base-change flatness for every module.

The corrected output is therefore a **stratified finite packet**, not one
undifferentiated joint ideal.

---

# 2. The projective-normal finite packet

Let `C` be regular and let `P=P(E)` be the projectivized normal bundle, with
projection `pi:P->C`.  For one passive owner `M`, write

```text
G = gr_{I_C}(M),
F = tilde(G) on P.
```

## 2.1 Low pieces and the projective tail

For a finite graded `S`-module, Serre comparison gives a bound `N` such that

```text
G_n -> pi_* F(n)
```

is an isomorphism for all `n>N`; higher cohomology vanishes after a further
uniform increase of `N`.

Therefore the infinite flatness problem splits into:

```text
LOW PACKET
G_0,...,G_N

PROJECTIVE TAIL
F on P, equivalently pi_*F(n) for n>N.
```

The complete graded module is flat over `A` exactly when every homogeneous
piece is flat.  Once the low pieces are flat and every high piece is identified
with a flat tail module, the direct sum is flat.  This exact algebraic compiler
is formalized in `FiniteGradedFlatnessCompiler.lean`.

For finitely many passive owners, take the direct sum over owners.  The exact
simultaneous compiler is formalized in `FinitePassivePortfolio.lean`.

## 2.2 Hilbert-polynomial compression on a reduced centre

Because `C` is regular, it is reduced.  For the projective morphism `P->C`, a
coherent sheaf is flat over `C` precisely on the flattening strata; on a reduced
base, flatness is equivalent to local constancy of the fibre Hilbert polynomial.
Since the polynomial degree is bounded by `rank(E)-1`, finitely many sufficiently
large values determine it.

This supplies a finite numerical shadow of the projective tail, but the
scheme-level algorithm should retain the flattening monomorphism/stratification
rather than replace it by a bare numerical function.

## 2.3 Definition of the PNF packet

The **projective-normal flatness packet** of a passive portfolio is

```text
PNF_C(M_1,...,M_s)
  = (N,
     {G_j,n : 1<=j<=s, 0<=n<=N},
     {F_j on P(E)},
     flattening data,
     base-change and pure-transform certificates).
```

It is finite, presentation independent after the required comparison theorems,
and naturally adapted to proper flatification.

---

# 3. Flatification is a preparatory modification, not a centre-selection gate

Raynaud--Gruson flatification, and its functorial proper form, produce a
sequence of blowups

```text
C^flat -> C
```

supported away from the maximal flat locus, such that the pure transforms of
the finitely many projective-tail sheaves are flat.  The finitely many low
pieces can be flattened simultaneously by adding their Fitting/flatifier data.

The centres of the flatification word need not be regular in positive
characteristic.  This is not a fatal obstruction because `dim C < dim X`.
Under the outer induction hypothesis, principalize the flatification ideals and
resolve their centres on `C`.  The resulting regular-centre word

```text
C' -> C
```

dominates the original flatifying modification.  Flatness is preserved by base
change, so the pulled-back pure transforms remain flat on `C'`.

This converts the passive gate into a lower-dimensional recursive task.

---

# 4. Ambient dominating-modification lift

Let

```text
C_r -> ... -> C_0=C
```

be a finite word of blowups along regular centres `D_i subset C_i`.  Blow up the
successive ambient transforms `X_i` along the same `D_i`.

Standard strict-transform geometry gives

```text
C_{i+1} = Bl_{D_i}(C_i)
```

inside

```text
X_{i+1}=Bl_{D_i}(X_i).
```

Locally, if `u=0` is the exceptional divisor, the normal coordinates of `C`
are divided by `u`.  Consequently the normal bundle is the pullback of the old
normal bundle twisted by the exceptional line bundle.  Projectivization
forgets this common line twist, so the new projectivized normal bundle is the
base change of the old one.

The load-bearing transport theorem should identify

```text
tilde(gr_{C_{i+1}}(M_{i+1}))
```

with the pure transform of the old projective-normal sheaf, up to the finite
low-degree torsion packet and a grading twist.  This is the precise bridge by
which flatification on `C` becomes normal flatness of the ambiently lifted
strict transform.

Active marked legality survives every lift by ideal-power monotonicity, as in
X035.  The unresolved obligations are the projective-normal pure-transform
identity, low-degree torsion control, all-chart overlap compatibility, and
source/debt no reset.

---

# 5. Anchor-contact ideals replace the raw nilpotent thickness cone

Let `Z_0,...,Z_r` be regular candidate centres in a regular ambient `X`, let

```text
Z = intersection_i Z_i,
Y = Z_red,
```

and assume `Y` is regular while `Z` is not.  For every anchor `Z_i`, define the
coherent contact ideal

```text
D_i = sum_{j != i} I_{Z_j} O_{Z_i}.
```

Then

```text
V(D_i) in Z_i
```

is exactly the scheme-theoretic common intersection `Z`, and

```text
radical(D_i)=I_{Y/Z_i}.
```

Thus the regular-support thickness problem is a finite family of ordinary
coherent ideals on regular schemes of strictly smaller dimension.

No anchor is chosen arbitrarily.  Retain the complete finite anchor groupoid,
process all minimal intrinsic contact profiles, and serialize the resulting
ambient centres by the existing intersection-completion/wonderful machinery.

---

# 6. Controlled transform of contact

In a local anchor graph chart, a graph difference has the form

```text
f = u^e g,
```

where `u=0` is the exceptional divisor.  An ambient blowup along a centre in
the common intersection removes one exceptional factor from every graph
difference:

```text
f/u = u^(e-1) g.
```

The exact scalar identity and the strict drop `e-1<e` are formalized in
`AnchorContactCleaning.lean`.

The tangent-curve model becomes the universal one-variable shadow:

```text
(y) and (y-x^m)
-> contact ideal (x^m) on the anchor curve
-> ambient blowup at x=0
-> contact ideal (x^(m-1)).
```

Contact order must precede exceptional debt in the rank.  Then the contact
coordinate decreases even when a blowup creates or relabels exceptional debt.
The exact rank arithmetic is formalized in `AnchorContactCleaning.lean` and
`LegalizationPhaseRank.lean`.

---

# 7. Lower-dimensional principalization plus ambient cleaning

Apply the lower-dimensional principalization theorem to every anchor contact
ideal `D_i`.  After a finite regular word, each controlled transform is
monomial:

```text
D_i^c = product_alpha E_alpha^(a_i,alpha).
```

A divisor `E_alpha` is Cartier on the anchor, so blowing it up inside the anchor
would be the identity.  In the ambient scheme, however, it has codimension at
least two and its blowup is nonidentity.  Blowing up its ambient image removes
one contact factor.  Repeating this `a_i,alpha` times kills the monomial contact.

Hence the regular-support branch should terminate by

```text
lower-dimensional principalization
+ finite ambient monomial-contact cleaning.
```

This replaces the X035 conjecture of a universal same-dimensional strict
transformation law for the entire thickness cone.  The graded cone remains a
useful diagnostic packet, but the actual descent mechanism is the anchor
contact ideal and lower-dimensional principalization.

---

# 8. Logarithmic legalization

Boundary compatibility can be treated by the same philosophy.  On a proposed
regular centre `C`, collect:

```text
restrictions of boundary ideals to C,
log-conormal rank and splitting defects,
all finite boundary-stratum intersection defects.
```

If the generic logarithmic rank is wrong, reject the branch.  Otherwise the
closed degeneracy locus is a finite Fitting/contact packet on `C`.  Resolve and
principalize it in lower dimension, lift the regular word ambiently, and obtain
a strict transform of `C` having SNC with the transformed boundary.

Thus passive and logarithmic legality are parallel lower-dimensional
legalization macros.

---

# 9. Corrected candidate graph

```text
prepared intrinsic state
-> finite Frobenius-Hasse/conormal packet
-> finite minimizer intersection arrangement

RAW CANDIDATE CENTRE C
-> active certificate                    [automatic under subcentres]
-> projective-normal passive packet
-> log-conormal boundary packet
-> lower-dimensional flatification/log principalization
-> regular dominating word on C
-> ambient lift
-> jointly legal strict transform C'
-> ordinary blowup along C'

REGULAR-SUPPORT BAD INTERSECTION
-> full anchor groupoid {D_i on Z_i}
-> lower-dimensional principalization
-> ambient monomial-contact cleaning
-> clean/empty arrangement

CLEAN ARRANGEMENT
-> maximal wonderful word
-> the same legalization compiler for every word centre
-> all-chart hereditary reentry
-> composite dimension/contact/passive/debt/SCC rank
-> finite global ordinary word.
```

---

# 10. Lean source written in this round

```text
FiniteGradedFlatnessCompiler.lean
FinitePassivePortfolio.lean
AnchorContactCleaning.lean
LegalizationPhaseRank.lean
X036ProjectiveNormalLegalizationIndex.lean
X036ProjectiveNormalLegalizationIndexAudit.lean
```

The slice proves:

1. finite low-piece plus flat-tail certificates imply flatness of every graded
   piece and the complete direct sum;
2. the same compiler works simultaneously for a finite passive portfolio;
3. one positive exceptional contact exponent transforms from `e` to `e-1`;
4. contact improvement dominates arbitrary debt changes;
5. the contact/passive/debt rank is well founded.

It does not prove the geometric construction or transport of those
certificates.

---

# 11. Exact open frontier after X036

```text
X036-G1   REES_SERRE_UNIFORM_COMPARISON_BOUND
X036-G2   PROJECTIVE_NORMAL_PACKET_BASE_CHANGE
X036-G3   FINITE_LOW_PIECE_FLATIFIER
X036-G4   PROPER_PROJECTIVE_TAIL_FLATIFICATION
X036-G5   REGULAR_WORD_DOMINATING_FLATIFIER_IN_LOWER_DIMENSION
X036-G6   AMBIENT_LIFT_OF_DOMINATING_WORD
X036-G7   NORMAL_BUNDLE_TWIST_AND_PROJECTIVIZATION_BASE_CHANGE
X036-G8   ASSOCIATED_GRADED_PURE_TRANSFORM_THEOREM
X036-G9   PASSIVE_NORMAL_FLATNESS_AFTER_AMBIENT_LEGALIZATION
X036-G10  LOG_CONORMAL_LEGALIZATION
X036-G11  ANCHOR_CONTACT_IDEAL_CANONICITY
X036-G12  ANCHOR_CONTACT_CONTROLLED_TRANSFORM
X036-G13  SYMMETRY_SAFE_ANCHOR_GROUPOID_SERIALIZATION
X036-G14  CONTACT_PRINCIPALIZATION_AMBIENT_CLEANING
X036-G15  LEGALIZATION_MACRO_NO_RESET
X036-G16  WONDERFUL_WORD_LEGALIZATION
X036-G17  COMPOSITE_DIMENSION_CONTACT_PASSIVE_DEBT_SCC_RANK
X036-G18  UNIVERSAL_ACTUAL_JOINTLY_LEGAL_CENTRE_WORD
```

The new highest-information cut is

```text
X036-G8 + X036-G12 + X036-G15.
```

Flatification and lower-dimensional principalization supply powerful existence
inputs.  The genuinely project-specific mathematics is the exact ambient
transport of the projective-normal and contact packets and their hereditary
identity after the macro.

---

# 12. Annals-series maximum-likelihood estimate

The modal form remains six papers.  The independent projective-normal
flatification chapter increases Paper III, while anchor-contact
principalization compresses the old same-dimensional thickness chapter.  The
new central estimate is **556 dense Annals/AMS-equivalent pages**.

| Paper | Maximum-likelihood title | Pages |
|---:|---|---:|
| I | Intrinsic Frobenius-Hasse States, Affine Conormal Packets, and Projectivity Discriminants | 90 |
| II | Anchor-Contact Ideals, Wonderful Arrangements, and Actual-Centre Synthesis | 120 |
| III | Projective-Normal Flatification, Ambient Legalization, and Hereditary Reentry | 132 |
| IV | Source-Debt Causality, Recurrent Classes, and Termination | 88 |
| V | Global Descent, Symmetry-Compatible Serialization, and Principalization | 78 |
| VI | Functorial Resolution, Counterexample Closure, and Lean Reproducibility | 48 |
|  | **Total** | **556** |

A one-volume editorial edition with theorem-interface cards, the proof DAG,
counterexample atlas, chart compendium, and paper-to-Lean map is estimated at
**600--635 physical pages**.

Subjective publication-form planning weights are:

```text
six papers                         0.61
seven papers, splitting flatness  0.20
five papers after consolidation   0.12
other                              0.07
```

These are research-planning weights, not calibrated probabilities.

---

# 13. Modal decisive theorem

> **Projective-Normal Legalization and Anchor-Contact Separation Theorem.**
> Let a prepared marked state on an `n`-dimensional smooth scheme produce a
> finite symmetry-stable family of regular candidate centres.  Assume the
> strong principalization and relative resolution program in dimensions
> `< n`.  Then every raw candidate centre admits a finite lower-dimensional
> regular word, lifted to the ambient scheme, whose strict transform is
> simultaneously permissible for all active owners, normally flat and
> Tor-safe for every passive owner, and SNC-compatible with the total
> boundary.  For every nonregular intersection with regular reduced support,
> the complete anchor-contact family admits a lower-dimensional
> principalization word followed by finite ambient contact cleaning, after
> which that intersection is empty or clean.  The complete construction is
> symmetry compatible, commutes with smooth base change and overlaps, and
> reconstructs every owner, source, debt, boundary, and packet identity
> without reset.  Each nonterminal macro strictly lowers the
> dimension/contact/passive/debt/SCC rank.

This is the current maximum-likelihood replacement for the four independent
X035 bridges.  It is not yet proved.

---

# 14. Truth boundary

```text
ROUND_ID                                           = MLEL-X036 / PNF-ACL

PROJECTIVE_NORMAL_PACKET_IDENTIFIED               = true
PASSIVE_GATE_RECAST_AS_LEGALIZATION_MACRO          = true
ANCHOR_CONTACT_IDEALS_IDENTIFIED                  = true
CONTACT_PRINCIPALIZATION_CLEANING_ROUTE_IDENTIFIED = true
FINITE_GRADED_FLATNESS_LEAN_SOURCE_WRITTEN         = true
FINITE_PASSIVE_PORTFOLIO_LEAN_SOURCE_WRITTEN       = true
CONTACT_CLEANING_LEAN_SOURCE_WRITTEN               = true
LEGALIZATION_RANK_LEAN_SOURCE_WRITTEN              = true

REES_SERRE_SCHEME_THEOREM_PROVED                   = false
AMBIENT_PROJECTIVE_NORMAL_TRANSPORT_PROVED         = false
PASSIVE_NORMAL_FLAT_LEGALIZATION_PROVED            = false
LOG_SNC_LEGALIZATION_PROVED                        = false
ANCHOR_CONTACT_TRANSFORM_PROVED                    = false
LEGALIZATION_MACRO_NO_RESET_PROVED                 = false
UNIVERSAL_JOINTLY_LEGAL_CENTRE_WORD_PROVED         = false

X036_CLEANROOM_GREEN                               = false
NEW_DECLARATIONS_PROMOTED                          = false
CERTIFIED_GRAPH_CHANGED                            = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED                 = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION         = false
FORMAL_GLOBAL_STATUS                               = OPEN_GAP
```

---

# 15. Principal standard inputs and literature

1. Serre comparison and vanishing for coherent sheaves on relative Proj.
2. Grothendieck flattening stratification and Hilbert-polynomial flatness
   criteria for projective coherent sheaves.
3. Raynaud--Gruson flatification by blowups; D. Rydh, *Functorial
   flatification of proper morphisms*, arXiv:2501.08394.
4. V. Cossart, O. Piltant, B. Schober, *Constancy of the Hilbert--Samuel
   function*, Nagoya Math. J. 256 (2024), 938--952.
5. Standard strict-transform and blowup-chart algebra.
6. The current MLE--Lean baseline through X035 and the restricted Hasse--Morita
   core descent theorem.

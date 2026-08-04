# MLEL-X038 / PGI-ERD

## Purification–Grading Interchange, Exceptional Rees Defects, and Divisorial Descent

**Chinese title:** 纯化–分次交换、例外 Rees 缺陷与除子下降  
**Protocol:** `PCR-FRACTAL-PROOF-LEAN 1.0 / MLEL-A003-FPE-EDGE`  
**Seed architecture:** `MLEL-D001 / FCPP-ATLAS`  
**Accepted mathematical parent:** `MLEL-M004 / HMC-SCCD` (restricted)  
**Experimental parents:** `MLEL-X036 / PNF-ACL`, `MLEL-X037 / CTW-BRT`  
**Primary D001 refinement:** `G29 -> G31 -> G41 -> G46/G52/G53`  
**Class:** `LOCAL_ALGEBRA_CLOSURE + EXPERIMENTAL_CANDIDATE_GRAPH_REFINEMENT / NO_THEOREM_PROMOTION`  
**Date:** 2026-08-04  
**Global status:** `OPEN_GAP`

---

# 0. Executive verdict

X037 isolated the correct centre-enriched transform semantics and introduced an
all-chart Rees interchange defect.  The defect was provisionally described as
an arbitrary kernel plus cokernel of a comparison between

```text
associated graded of the ambient pure transform
and
pure transform of the projective-normal associated graded.
```

The present round identifies a large and unavoidable part of that defect
exactly.  On one exceptional chart, purification and associated grading fail to
commute by a **single exceptional graded-torsion kernel**, not by an arbitrary
kernel/cokernel pair.

Let

```text
R  = a Noetherian chart ring,
L  = transformed carrier ideal,
N  = ambient pullback module before exceptional purification,
u  = a local equation of the exceptional Cartier divisor,
T  = H^0_(u)(N),
A  = gr_L(N),
H  = gr_L^ind(T),
U  = H^0_(u)(A).
```

Then there is a canonical exact sequence

```text
0 -> U/H
  -> gr_L(N/T)
  -> A/U
  -> 0,
```

and

```text
U/H = H^0_(u)(gr_L(N/T)).
```

Thus:

```text
purification before grading
-> gr_L(N/T)

purification after grading
-> A/U

interchange defect
-> exceptional torsion of gr_L(N/T).
```

The defect is finite graded, is killed by a power of the exceptional equation,
and is compatible with flat base change.  Artin–Rees supplies an explicit
finite prefix and eventual tail for the inherited filtration, but Noetherianity
already gives finite generation once the two torsion layers are recognized as
submodules of the finite associated graded module.

A second defect can occur before purification: the twisted Rees base-change map
from the old projective-normal packet to the associated graded of the ambient
pullback need not be an isomorphism on the exceptional locus.  Its kernel and
cokernel are coherent and exceptional-supported once the all-chart comparison
is constructed.  Therefore the total X037 Rees interchange defect should have
a finite filtration with two exceptional-supported types of subquotient:

```text
Rees base-change/twist defect,
purification–grading torsion defect.
```

Off the exceptional divisor both vanish automatically.  This changes the
termination problem: the interchange defect is not a new full-dimensional
singularity.  It is a divisorial, source-labelled packet that must be eliminated
by lower-dimensional flatification/principalization and Cartier-trace cleaning.

---

# 1. Local purification–grading theorem

## 1.1 Setup

Let `R` be a Noetherian ring, `L` an ideal, `N` a finite `R`-module, and
`u in R`.  Define

```text
T = H^0_(u)(N)
  = {x in N | u^q x = 0 for some q}.
```

Because `N` is Noetherian, the ascending chain

```text
ker(u) <= ker(u^2) <= ...
```

stabilizes.  Hence there is one exponent `q_N` such that

```text
T = ker(u^q_N).
```

Filter `N` by `F^aN=L^aN`.  Give `T` the induced filtration

```text
F^aT = T intersection L^aN,
```

and give `N/T` the quotient filtration

```text
F^a(N/T) = (L^aN+T)/T.
```

Put

```text
A = gr_L(N),
H = gr_L^ind(T),
U = H^0_(u)(A).
```

## 1.2 Exactness of the induced filtration

In degree `a`, the inclusion `T -> N` and quotient `N -> N/T` give

```text
0
-> (T intersection L^aN)/(T intersection L^(a+1)N)
-> L^aN/L^(a+1)N
-> (L^aN+T)/(L^(a+1)N+T)
-> 0.
```

Taking the direct sum over `a` yields

```text
0 -> H -> A -> gr_L(N/T) -> 0.
```

Thus

```text
gr_L(N/T) ~= A/H.
```

## 1.3 Nested exceptional-torsion layers

The uniform exponent `q_N` kills `T`, hence it kills every homogeneous piece of
`H`.  Therefore

```text
H <= U.
```

The quotient map `A/H -> A/U` is surjective and has kernel `U/H`.  Combining it
with the preceding identification gives

```text
0 -> U/H
  -> gr_L(N/T)
  -> A/U
  -> 0.
```

The right-hand term is exactly the chartwise Cartier purification of `A`:

```text
A/U = A/H^0_(u)(A).
```

## 1.4 The kernel is all new exceptional torsion

Let `a+H` be an element of `A/H`.  If it is killed by `u^r`, then

```text
u^r a in H.
```

Since `H` is killed by `u^q_N`,

```text
u^(r+q_N) a = 0,
```

so `a in U`.  Conversely every class in `U/H` is exceptional-power torsion.
Therefore

```text
H^0_(u)(A/H) = U/H.
```

Equivalently,

```text
H^0_(u)(gr_L(N/T))
  = H^0_(u)(gr_L(N)) / gr_L^ind(H^0_(u)(N)).
```

This is the **purification–grading interchange defect**.

---

# 2. Explicit degree formula

In degree `a`, the full exceptional torsion of `A_a=L^aN/L^(a+1)N` is

```text
U_a
 = (((L^(a+1)N : u^infinity) intersection L^aN)
    / L^(a+1)N).
```

The inherited layer is

```text
H_a
 = ((T intersection L^aN)+L^(a+1)N) / L^(a+1)N.
```

Hence the defect degree is

```text
E_a
 = ((L^(a+1)N : u^infinity) intersection L^aN)
   /
   (L^(a+1)N + (T intersection L^aN)).
```

This formula isolates the exact failure of exceptional saturation to be strict
with respect to the `L`-adic filtration.

If `N` has no `u`-power torsion, then `T=0` and

```text
E = H^0_(u)(gr_L(N)).
```

In this chamber, vanishing of the interchange defect is equivalent to
exceptional regularity on the associated graded.  In degreewise form it is a
saturated filtration-strictness condition, closely related to the familiar
intersection criterion

```text
uN intersection L^aN = u L^aN.
```

The X038 theorem uses the full saturation formula rather than assuming a
one-step nonzerodivisor criterion.

---

# 3. Finiteness and the Artin–Rees window

## 3.1 Noetherian finite generation

The associated graded ring `gr_L(R)` is Noetherian.  The module

```text
A=gr_L(N)
```

is finite over it.  Both `H` and `U` are graded submodules of `A`; therefore
both are finite.  Consequently

```text
E=U/H
```

is a finite graded module.

This argument is simpler than invoking Artin–Rees merely for finite generation.

## 3.2 What Artin–Rees still supplies

Artin–Rees gives an integer `c` such that for every `a>=c`,

```text
T intersection L^aN
  = L^(a-c)(T intersection L^cN).
```

Thus the inherited layer has a finite transition window followed by an
explicitly generated tail.  Together with finite generation of `U`, this gives
a computable packet consisting of

```text
one stabilization exponent for T,
one Artin–Rees index c,
finitely many degrees below c,
a finite set of homogeneous tail generators,
a projective-tail/Fitting presentation.
```

The Lean file `ArtinReesTailCompiler.lean` formalizes only the final logical
step: a finite prefix, a cutoff seed, and one successor law certify every
degree.

---

# 4. Flat-base-change compatibility

Let `R->S` be flat.  Put

```text
N_S=N tensor_R S,
L_S=LS,
u_S=image(u).
```

## 4.1 Exceptional torsion

Choose `q` at which `ker(u^q)` stabilizes on `N`.  Flatness gives

```text
ker(u^q:N->N) tensor S
 ~= ker(u_S^q:N_S->N_S).
```

The equality `ker(u^q)=ker(u^(q+1))` also survives flat base change and forces
all higher kernels on `N_S` to stabilize at `q`.  Hence

```text
H^0_(u)(N) tensor S
 ~= H^0_(u_S)(N_S).
```

The same argument applies to the finite associated graded module `A`.

## 4.2 Filtrations and intersections

Flatness gives

```text
L^aN tensor S ~= L_S^a N_S.
```

Intersections commute because they are kernels of the map

```text
N -> N/T directSum N/L^aN.
```

Therefore

```text
(T intersection L^aN) tensor S
 ~= T_S intersection L_S^aN_S.
```

It follows degreewise that `A`, `H`, `U`, and `E=U/H` commute with flat base
change.  The purification–grading exact sequence is therefore flat-natural.

This closes the abstract flat-base-change theorem for the local packet.  The
scheme-level sheafification, grading twists, and overlap cocycles remain formal
interfaces to be written.

---

# 5. Exceptional support and divisorial descent

Because `E` is a finite exceptional-power-torsion module, some power of `u`
kills it.  Hence

```text
Supp(E) subset V(u).
```

When the transformed carrier is regular and `u=0` is a component of its SNC
exceptional boundary, `V(u)` has strictly smaller dimension than the carrier.
Thus a nonzero purification–grading defect is automatically a lower-dimensional
packet.

For several exceptional components with local equations `{u_alpha}`, the
finite packet is killed locally by one monomial

```text
product_alpha u_alpha^(e_alpha).
```

The exponent vector is a source-labelled exceptional-debt/contact profile.
Principalizing its Fitting support on the carrier and executing the residual
ambient Cartier-trace steps removes the old defect source.  The unresolved
geometric theorem must prove that every new defect receives a new causal source
and that an eliminated source never recharges.

---

# 6. The remaining Rees base-change/twist defect

The preceding exact sequence compares purification before and after grading of
one module already living on an ambient blowup chart.  To connect it with the
old projective-normal packet, one still needs a twisted comparison.

Let `I` be the old carrier ideal, `K` a trace ideal, `I'` the transformed carrier
ideal, and `N` the ambient pullback of an owner module.  On a chart meeting the
strict transform of the carrier, total and strict normal directions differ by
an exceptional line factor.  There should be a canonical map in every degree

```text
beta_a:
  pullback(I^aM/I^(a+1)M) tensor O(aE)
  -> L^aN/L^(a+1)N.
```

Off the exceptional divisor the blowup is an isomorphism and `beta_a` is an
isomorphism.  Once the all-chart construction is written, its kernel and
cokernel are coherent and exceptional-supported.  Define their finite
low-degree/projective-tail packet as the **Rees base-change defect** `B`.

The total X037 interchange defect should then admit a finite filtration whose
subquotients are:

```text
B,
E = purification–grading defect.
```

Both vanish off the exceptional divisor.  This is the new maximum-likelihood
shape of the all-chart theorem.  The construction of `beta`, its line twist,
and its overlap compatibility are not proved in this round.

---

# 7. Corrected defect-elimination macro

The proposed macro is now:

```text
1. Construct the Rees base-change defect B.
2. Construct the purification–grading defect E.
3. Fuse their finite Fitting/projective-tail packets.
4. If the fused packet is zero, accept the transform comparison.
5. If nonzero, its support lies in the exceptional boundary of the carrier.
6. Invoke lower-dimensional relative principalization/flatification on that
   support, preserving the immutable trace source.
7. Lift the resulting regular word to ambient trace centres.
8. Execute residual Cartier-trace steps instead of deleting carrier identities.
9. Recompute the comparison on every chart.
10. Prove that support dimension, exceptional exponent, or the projective-tail
    Fitting profile strictly drops.
11. Preserve zero comparison packets under all later source-labelled steps.
```

The leading rank coordinates are therefore

```text
(dim Supp(total interchange defect),
 exceptional torsion/Artin–Rees exponent,
 projective-tail/Fitting profile,
 passive complexity,
 contact,
 debt,
 SCC height).
```

The Lean file `ExceptionalInterchangeRank.lean` verifies the corresponding
well-founded arithmetic only.

---

# 8. Candidate graph update

The X037 edge

```text
arbitrary ker/coker RID
-> strict Fitting/support recursion
```

is replaced by the more structured chain

```text
ambient trace blowup chart
-> twisted Rees base-change comparison
-> exceptional base-change defect B

ambient exceptional purification
-> induced torsion H <= full graded torsion U
-> exact packet E=U/H

B directSum E
-> finite exceptional interchange packet
-> zero chamber: exact projective-normal transport
-> nonzero chamber: divisorial lower-dimensional legalization
-> ambient Cartier-trace lift
-> no-reset comparison reentry.
```

This refinement directly serves the D001 critical chain

```text
HER-03 normal flatness
-> HER-05 joint legality
-> HER-15 all-chart reentry
-> TRM-05 Fitting descent
-> TRM-11 composite rank
-> TRM-12 local termination.
```

---

# 9. Lean source written in this round

```text
ExceptionalTorsionLayers.lean
ArtinReesTailCompiler.lean
ExceptionalInterchangeRank.lean
X038PurificationGradingInterchangeIndex.lean
X038PurificationGradingInterchangeIndexAudit.lean
```

The exact slice proves:

1. nested inherited/full exceptional-torsion layers have exact choice-free
   clean/defect coverage;
2. distinct layers produce a concrete witness without selecting a preferred
   geometric stratum;
3. a finite prefix, cutoff seed, and tail law certify every degree;
4. support, exponent, tail, passive, contact, and debt drops are strict in one
   well-founded lexicographic rank.

It does not formalize the local exact sequence, Artin–Rees theorem, flat base
change, Rees chart comparison, exceptional support theorem, defect elimination,
or no-reset.

---

# 10. Exact open frontier after X038

```text
X038-G1   SHEAFIFIED_EXCEPTIONAL_TORSION_FUNCTOR
X038-G2   INDUCED_FILTRATION_ASSOCIATED_GRADED_EXACT_SEQUENCE
X038-G3   PURIFICATION_GRADING_TORSION_IDENTITY
X038-G4   FINITE_GRADED_PACKET_AND_ARTIN_REES_WINDOW
X038-G5   FLAT_BASE_CHANGE_OF_EXCEPTIONAL_TORSION_AND_INTERSECTIONS
X038-G6   MULTI_EXCEPTIONAL_MONOMIAL_TORSION_PACKET
X038-G7   ALL_CHART_TWISTED_REES_BASE_CHANGE_MAP
X038-G8   NORMAL_BUNDLE_LINE_TWIST_IDENTIFICATION
X038-G9   FINITE_REES_BASE_CHANGE_DEFECT
X038-G10  TOTAL_INTERCHANGE_DEFECT_FILTRATION
X038-G11  EXCEPTIONAL_SUPPORT_AND_LOWER_DIMENSIONAL_CARRIER
X038-G12  DEFECT_FLATIFICATION_AND_AMBIENT_CARTIER_TRACE_LIFT
X038-G13  STRICT_SUPPORT_EXPONENT_OR_TAIL_DROP
X038-G14  SOURCE_LABEL_AND_ZERO_DEFECT_NO_RECHARGE
X038-G15  OVERLAP_COCYCLE_FOR_THE_COMPARISON
X038-G16  PROJECTIVE_NORMAL_FLATNESS_AFTER_DEFECT_ELIMINATION
X038-G17  WONDERFUL_WORD_COMPATIBILITY
X038-G18  ALL_CHART_PACKET_RECONSTRUCTION_WITHOUT_RESET
X038-G19  COMPOSITE_DIMENSION_DEFECT_EXPONENT_TAIL_DEBT_SCC_RANK
X038-G20  UNIVERSAL_JOINTLY_LEGAL_ACTUAL_CENTRE_WORD
```

The highest-information cut is now

```text
X038-G7/G8/G9
+ X038-G12/G13
+ X038-G14/G18.
```

The local purification–grading algebra is essentially closed on paper.  The
remaining project-specific problem is the twisted Rees chart comparison and
its causal elimination under ordinary ambient trace blowups.

---

# 11. Annals-series maximum-likelihood estimate

The exact torsion sequence removes some arbitrary RID machinery, but the
Artin–Rees window, twisted Rees base-change packet, and exceptional-defect
elimination require a dedicated section.  The new central estimate is **564
dense Annals/AMS-equivalent pages**.

| Paper | Maximum-likelihood title | Pages |
|---:|---|---:|
| I | Intrinsic Frobenius-Hasse States, Affine Conormal Packets, and Projectivity Discriminants | 90 |
| II | Anchor-Contact Ideals, Cartier-Trace Words, and Wonderful Actual-Centre Synthesis | 118 |
| III | Purification–Grading Interchange, Carrier-Enriched Flatification, and Hereditary Reentry | 142 |
| IV | Exceptional Rees Defects, Source-Debt Causality, and Termination | 88 |
| V | Global Descent, Symmetry-Compatible Serialization, and Principalization | 78 |
| VI | Functorial Resolution, Counterexample Closure, and Lean Reproducibility | 48 |
|  | **Total** | **564** |

A single-volume editorial edition with theorem-interface cards, the
centre/source/defect ledger, complete chart compendium, proof DAG,
counterexample atlas, and paper-to-Lean map is estimated at **612--652 physical
pages**.

Subjective publication-form planning weights:

```text
six papers                                           0.58
seven papers, splitting Rees transport/defects       0.24
five papers after consolidation                      0.11
other                                                0.07
```

These are planning weights, not calibrated probabilities.

---

# 12. Modal decisive theorem

> **Purification–Grading Interchange and Exceptional Rees-Defect Descent
> Theorem.**  Let a centre-enriched legalizing word act on a prepared marked
> state over a perfect field of characteristic `p>0`.  On every standard chart
> and for every owner, there is a finite, flat-base-change-compatible
> exceptional interchange packet.  It has a finite filtration whose
> subquotients are the twisted Rees base-change defect and the exact
> purification–grading torsion
> `H^0_E(gr(N/H^0_E(N)))`.  The packet vanishes away from the exceptional
> boundary.  If it is zero, the associated graded of the ambient pure transform
> agrees, with the canonical line twist, with the source-labelled
> projective-normal pure transform.  If it is nonzero, its support is a strict
> lower-dimensional exceptional carrier and admits a finite relative
> flatification/principalization word whose ambient Cartier-trace lift strictly
> lowers support dimension, exceptional exponent, or projective-tail Fitting
> profile.  Vanished source-labelled packets never recharge.  Consequently the
> transformed carrier is simultaneously active-permissible, passive
> normal-flat and Tor-safe, and SNC-compatible, and all packet, owner, source,
> debt, contact, and boundary identities reenter on overlaps without reset.

This is the current maximum-likelihood replacement for the undifferentiated
X037 RID theorem.  It is not yet proved in its scheme-level form.

---

# 13. Truth boundary

```text
ROUND_ID                                             = MLEL-X038 / PGI-ERD

X037_EXPERIMENTAL_CLEANROOM_GREEN                    = true
X037_DECLARATIONS_PROMOTED                           = false

PURIFICATION_GRADING_EXACT_SEQUENCE_PROVED_ON_PAPER  = true
NEW_TORSION_IDENTITY_PROVED_ON_PAPER                 = true
FINITE_GRADED_DEFECT_PROVED_ON_PAPER                 = true
FLAT_BASE_CHANGE_PROVED_ON_PAPER                     = true
EXCEPTIONAL_SUPPORT_IDENTIFIED                       = true

NESTED_LAYER_LEAN_SOURCE_WRITTEN                     = true
ARTIN_REES_TAIL_COMPILER_LEAN_SOURCE_WRITTEN         = true
EXCEPTIONAL_RANK_LEAN_SOURCE_WRITTEN                 = true

ALL_CHART_TWISTED_REES_MAP_PROVED                    = false
TOTAL_DEFECT_FILTRATION_PROVED                       = false
DEFECT_ELIMINATION_STRICT_DROP_PROVED                = false
ZERO_DEFECT_NO_RECHARGE_PROVED                       = false
PASSIVE_NORMAL_FLAT_AMBIENT_REALIZATION_PROVED       = false
UNIVERSAL_JOINTLY_LEGAL_CENTRE_WORD_PROVED           = false

X038_CLEANROOM_GREEN                                 = false
NEW_DECLARATIONS_PROMOTED                            = false
CERTIFIED_GRAPH_CHANGED                              = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED                   = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION           = false
FORMAL_GLOBAL_STATUS                                 = OPEN_GAP
```

---

# 14. Principal standard inputs

1. Noetherian stabilization of exceptional-power torsion.
2. Exactness of associated graded for an induced submodule filtration and the
   quotient filtration.
3. Noetherianity of Rees and associated graded rings.
4. Artin–Rees for an explicit finite transition window.
5. Flat-base-change exactness for kernels, intersections, powers, and quotient
   filtrations.
6. Strict/pure transforms as exceptional-torsion quotients.
7. The X037 centre-enriched Cartier-trace semantics and flat Cartier-trace
   base-change proposition.
8. The restricted MLE–Lean Hasse–Morita core descent theorem.

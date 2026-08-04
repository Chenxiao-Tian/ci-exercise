# MLEL-X035 / STD-ALI

## Support-Thickness Dichotomy, Ambient-Lift Induction, and Nilpotent Contact Packets

**Chinese title:** 支撑-厚度二分、环境提升归纳与幂零接触包  
**Protocol:** `PCR-FRACTAL-PROOF-LEAN 1.0 / MLEL-A003-FPE-EDGE`  
**Seed architecture:** `MLEL-D001 / FCPP-ATLAS`  
**Accepted mathematical parent:** `MLEL-M004 / HMC-SCCD`  
**Experimental parents:** `MLEL-X032`, `MLEL-X033`, `MLEL-X034`  
**Class:** `EXPERIMENTAL_CANDIDATE_GRAPH_REFINEMENT / NO_THEOREM_PROMOTION`  
**Date:** 2026-08-04  
**Global status:** `OPEN_GAP`

## Central refinement

For a nonregular scheme-theoretic intersection `Z` in a regular ambient scheme,
write `Y=Z_red`.  The first-defect branch splits intrinsically into:

```text
support-singular branch:
  Y singular
  -> lower-dimensional relative resolution of Y
  -> ambient lift of the same ordinary centres;

regular-support thickness branch:
  Y regular but Z nonregular
  -> finite nilpotent contact/normal-cone packet on Y
  -> strict thickness/contact/Hasse/Fitting descent.
```

The tangent-curve scheme `Spec k[x]/(x^m)` proves that support dimension alone
is insufficient: its reduced support is already a regular point, while the
contact thickness must fall `m -> m-1`.

## Standard mathematical collapses

1. In a regular locally Noetherian ambient scheme, a regular
   scheme-theoretic intersection is a regular immersion.  The canonical
   conormal map from the direct sum of the component conormals onto the
   intersection conormal is a surjection of finite locally free modules; its
   kernel is the finite projective excess bundle.
2. For a finitely presented module,
   `Delta_r(M)=Fitt_r(M)*Ann(Fitt_{r-1}(M))` cuts out the rank-`r` free locus.
3. The strict transform of a stratum under an ambient blowup is its blowup in
   the induced centre.  Active marked permissibility lifts because centre
   ideals enlarge.

## Nilpotent contact packet

For `K=I_Z` and `J=I_Y=radical(K)`, define the positive thickness cone

```text
Theta(Z/Y)=directSum_{q>=1} (J^q+K)/(J^{q+1}+K).
```

It is the positive-degree part of the normal cone of `Y` in `Z`.  Its top
nonzero degree is the thickness coordinate.  Projectivity discriminants,
Fitting supports, Hasse/contact profiles and Schur residuals provide the
candidate strict recursion on a regular carrier.

## Candidate graph

```text
finite minimizer arrangement
-> full finite good/bad coverage

clean layer
-> regular-intersection collapse
-> projective excess bundles
-> wonderful ordinary serialization

bad layer
-> singular reduced carriers
     relative lower-dimensional resolution + ambient lift
-> regular reduced carriers
     nilpotent contact packet + strict thickness descent
-> clean arrangement
-> wonderful ordinary serialization.
```

## Lean slice

```text
FiniteBadStratumCoverage.lean
SupportThicknessAlternative.lean
StratumInductionActiveLift.lean
SupportThicknessRank.lean
NilpotentThickness.lean
X035SupportThicknessIndex.lean
X035SupportThicknessIndexAudit.lean
```

The source proves finite choice-free coverage, the support/thickness partition,
active legality under ambient lifting, well-founded support/thickness
arithmetic and elementary nilpotent-thickness certificates.  Passive/SNC
ambient lifting and strict thickness descent remain open.

## Exact frontier

```text
X035-G1   REGULAR_INTERSECTION_COLLAPSE_SCHEME_THEOREM
X035-G2   PROJECTIVITY_DISCRIMINANT_SCHEME_AND_LEAN_THEOREM
X035-G3   RELATIVE_LOWER_DIMENSIONAL_STATE_RESTRICTION
X035-G4   AMBIENT_LIFT_STRICT_TRANSFORM_WORD_THEOREM
X035-G5   AMBIENT_LIFT_PASSIVE_NORMAL_FLATNESS
X035-G6   AMBIENT_LIFT_LOG_SNC_AND_NONIDENTITY
X035-G7   NILPOTENT_CONTACT_PACKET_FINITE_PRESENTATION
X035-G8   THICKNESS_PACKET_BASE_CHANGE_AND_OVERLAP
X035-G9   MAXIMAL_THICKNESS_STRATIFICATION
X035-G10  NILPOTENT_CONTACT_STRICT_DESCENT
X035-G11  SUPPORT_THICKNESS_MACRO_NO_RESET
X035-G12  CLEAN_AFTER_FINITE_SUPPORT_THICKNESS_MACROS
X035-G13  WONDERFUL_WORD_JOINT_LEGALITY
X035-G14  COMPOSITE_DIMENSION_PHASE_THICKNESS_SCC_RANK
X035-G15  UNIVERSAL_ACTUAL_CENTRE_WORD_CERTIFICATE
```

The highest-information cut is `X035-G5 + X035-G10`.

## Annals maximum-likelihood plan

The mode remains six papers and 550 dense Annals/AMS-equivalent pages:

```text
I    Intrinsic Frobenius-Hasse States, Affine Conormal Packets,
     and Projectivity Discriminants                              90
II   Content Ideals, Support-Thickness Strata,
     and Wonderful Actual-Centre Synthesis                     122
III  Joint Legality, Ambient Lifting, All-Chart Transforms,
     and Hereditary Reentry without Reset                      118
IV   Nilpotent Contact Defects, Recurrent Classes,
     and Causal Termination                                     94
V    Global Descent, Symmetry-Compatible Wonderful
     Serialization, and Principalization                        78
VI   Functorial Resolution, Counterexample Closure,
     and Lean Reproducibility                                   48
                                                               ---
                                                               550
```

## Truth boundary

```text
SUPPORT_THICKNESS_DICHOTOMY_IDENTIFIED             = true
ACTIVE_AMBIENT_LIFT_LEAN_SOURCE_WRITTEN            = true
CHOICE_FREE_BAD_LAYER_LEAN_SOURCE_WRITTEN          = true
SUPPORT_THICKNESS_RANK_LEAN_SOURCE_WRITTEN         = true
PASSIVE_SNC_AMBIENT_LIFT_PROVED                    = false
NILPOTENT_CONTACT_STRICT_DESCENT_PROVED            = false
UNIVERSAL_ACTUAL_CENTRE_SYNTHESIS_PROVED           = false
X035_CLEANROOM_GREEN                               = false
NEW_DECLARATIONS_PROMOTED                          = false
CERTIFIED_GRAPH_CHANGED                            = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED                 = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION         = false
FORMAL_GLOBAL_STATUS                               = OPEN_GAP
```

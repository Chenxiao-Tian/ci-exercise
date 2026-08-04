# MLEL-X032 / FPP-CMS-FPA

## Finite-Projective Frames, Intrinsic Order Ideals, Canonical Minimizer Spaces, and the Symmetry-Safe Centre-Word Boundary

**Date:** 2026-08-03/04  
**Protocol:** `PCR-FRACTAL-PROOF-LEAN 1.0 / MLEL-A003-FPE-EDGE`  
**Seed architecture:** `MLEL-D001 / FCPP-ATLAS`  
**Accepted mathematical parent:** `MLEL-M004 / HMC-SCCD`  
**Experimental parent:** `MLEL-X031 / ACI-MMR-OIH`  
**Baseline class:** `COMPLETE_RESEARCH_ARCHIVE / NO_THEOREM_PROMOTION`  
**Global status:** `OPEN_GAP`

## 1. Selected load-bearing cut

The round refines D001 `G11 / FND-11` and the downstream canonicality edge
`G16 -> G20 -> G25 -> G26`.  G11 lies on the default critical path

```text
FND-11 -> CTR-13 -> HER-15 -> TRM-12 -> GLB-07/08 -> FIN-04.
```

The two tasks were:

1. remove the independently supplied dual frame from the intrinsic order-ideal
   compiler;
2. test whether cardinal-minimal marked closures really produce a canonical
   symmetry-compatible single centre.

## 2. Positive algebraic refinement

The following exact chain is now written as Experimental Lean source:

```text
finite module
-> finite spanning family
-> surjective finite-free linear-combination map

projective target
-> the surjection splits
-> split finite-free presentation
-> projected standard basis + pulled-back coordinates form a finite dual frame
-> intrinsic cokernel graph/proper-hybrid/unit status.
```

The intrinsic order ideal

```text
O_P(x) = span { f(x) | f : P ->ₗ[R] R }
```

is the least ideal absorbing all dual values.  This minimality and the
unit-obstruction no-go require no basis, finite-projectivity assumption, or
chosen frame.  A finite dual frame is needed only as a finite proof certificate
for zero detection and effective computation.

Consequently the abstract algebraic FND-11 input can be reduced from

```text
finite-projective cokernel + separately supplied finite dual frame
```

to

```text
finite-projective cokernel.
```

The remaining load-bearing edge is geometric and functorial: construct the
relevant finite-projective cokernel from every resolution state and transport
its obstruction/order-ideal package compatibly under localization,
smooth/etale maps, controlled transforms and overlaps.

## 3. Canonicality no-go and candidate-graph repair

X031 supplies a cardinal-minimal acceptable correction subfamily.  Existence of
such a minimizer does not imply a canonical single choice.

A two-component Boolean model has exactly two singleton minimizers exchanged by
an involution and no fixed minimizer.  Intersecting them destroys
acceptability; unioning them can destroy properness.  In the integer-ideal
model,

```text
(6) <= (2),  (6) <= (3),  but  (2) + (3) = (1).
```

Therefore the candidate edge

```text
cardinal-minimal acceptable family -> canonical single centre
```

is deleted and replaced by

```text
unique minimizer
-> canonical single marked closure

multiple minimizers
-> canonical finite minimizer space/groupoid
-> separately proved ordinary centre-word serialization
-> critical-pair compatibility or finite rewrite exit
-> joint legality + hereditary no-reset + strict macro rank.
```

No stacky quotient may replace the required ordinary coherent centres in the
final theorem.

## 4. Experimental PR and clean-room matrix

| PR | Node | Scope | Run at archival | Status |
|---:|---|---|---:|---|
| 35 | X032 / SFP-IOM | split presentation, intrinsic minimality, cokernel compiler | 30866047700 | queued |
| 36 | X032A / IOM-ATOMIC | frame-free intrinsic order-ideal atomic leaf | 30866602773 | queued |
| 37 | X032-B / CMS-NES | minimizer-space symmetry no-go and unique chamber | 30866735214 | queued |
| 38 | X032B / PROJECTIVE-SPLIT | projective surjections split | 30867241525 | queued |
| 39 | X032C / FPP-DF | split finite-free presentation to dual frame/compiler | 30867374999 | queued |
| 40 | X032C / FINITE-PROJECTIVE-SPLIT | finite spanning projective split presentation | 30867516545 | queued |
| 41 | X032D / FPA-IOM | finite projective module automatically yields X031 frame/status | 30867757723 | queued |

Queued workflows are not green evidence.  None of these declarations is
imported into `CertifiedIndex`.

## 5. Updated exact frontier

```text
X032-N1  UNIVERSAL_RESOLUTION_COKERNEL_CONSTRUCTION
X032-N2  FINITE_PROJECTIVITY_ON_A_FINITE_FITTING_ATLAS
X032-N3  COKERNEL_AND_OBSTRUCTION_PRESENTATION_INDEPENDENCE
X032-N4  ORDER_IDEAL_NO_RESET_BASE_CHANGE_AND_OVERLAP
X032-N5  UNIQUE_MINIMIZER_LOCUS_CONSTRUCTIBILITY
X032-N6  MINIMIZER_SPACE_BASE_CHANGE_EQUIVALENCE
X032-N7  MINIMIZER_CENTRE_CRITICAL_PAIR_CLASSIFICATION
X032-N8  SYMMETRY_SAFE_ORDINARY_CENTRE_WORD_SERIALIZATION
X032-N9  SERIALIZED_WORD_JOINT_LEGALITY
X032-N10 SERIALIZED_WORD_HEREDITARY_NO_RESET_AND_STRICT_RANK
```

The highest-posterior next geometric mission is the finite Fitting-atlas
construction of the intrinsic cokernel/order-ideal package, followed by the
critical-pair classification for nonunique minimizer centres.

## 6. Truth boundary

```text
FND11_ABSTRACT_FRAME_INPUT_REMOVED             = EXPERIMENTAL_SOURCE_WRITTEN
INTRINSIC_ORDER_IDEAL_MINIMALITY_WRITTEN       = true
MINIMIZER_SYMMETRY_NO_GO_WRITTEN               = true
CANDIDATE_GRAPH_CORRECTED                       = true
ALL_NEW_CLEANROOM_RUNS_GREEN                    = false
NEW_DECLARATIONS_PROMOTED                       = false
CERTIFIED_GRAPH_CHANGED                         = false
UNIVERSAL_RESOLUTION_COKERNEL_CONSTRUCTED       = false
UNIVERSAL_ACTUAL_CENTRE_SYNTHESIS_PROVED        = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED              = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION      = false
FORMAL_GLOBAL_STATUS                            = OPEN_GAP
```

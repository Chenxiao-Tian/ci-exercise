# MLEL-X033 / MWB-DFI — Baseline Research Record

## Maximal Wonderful Building-Set Completion, Defect-First Intersection Profiles, and Symmetry-Safe Ordinary-Centre Serialization

**Protocol:** `PCR-FRACTAL-PROOF-LEAN 1.0 / MLEL-A003-FPE-EDGE`  
**Accepted mathematical parent:** `MLEL-M004 / HMC-SCCD`  
**Experimental parent:** `MLEL-X032 / FPP-CMS-FPA`  
**Source branch:** `pcr-fractal-x033-mwb-dfi-base-20260804`  
**Clean-room PR:** `#43`  
**Clean-room head:** `ca18cb1adb7702f5930173c94249c1286832f35c`  
**Workflow run at archival:** `30873031266` (`queued`)  
**Epistemic class:** `EXPERIMENTAL_RESEARCH_HISTORY / NO_THEOREM_PROMOTION`  
**Formal global status:** `OPEN_GAP`

## Candidate-graph repair

The X032 minimizer-space no-go is resolved on the clean geometric chamber by retaining the whole finite minimizer arrangement rather than choosing one point:

```text
all minimal marked closures
-> all nonempty scheme-theoretic intersections
-> maximal building set
-> canonical product ideal
-> intrinsic rank layers
-> one disjoint-union ordinary centre per layer
-> finite wonderful blow-up word.
```

The product of the building-set ideals is independent of enumeration and symmetry invariant.  The rank-layer word is therefore an implementation of an intrinsic final model, not the source of its canonicity.

## Symmetric defect packet

On a common graph chart, a finite family of graph centres with sections `h_a` is encoded without a distinguished base point by

```text
D(h)_(a,b) = h_a - h_b.
```

The corresponding linear map has kernel equal to the diagonal submodule of constant families and is equivariant under every permutation of the centre family.  This converts multi-centre coincidence/contact into another finite packet to which the existing order-ideal, Hasse, Frobenius and Fitting machinery may be applied.

## Red-team corrections

The following implications are deleted from the Candidate Graph:

```text
I inf J = I*J -> clean geometric intersection;

finitely presented cokernel
-> projective on an open cover of the whole state;

iterated Fitting/Nash blow-up -> universal resolution.
```

The Tor equality is retained only as a passive/derived-intersection diagnostic.  The corrected module interface is projective Fitting locus plus a closed nonprojective residual packet.

## Exact remaining frontier

```text
X033-N1  graph-atlas configuration-difference effectivity and overlap descent
X033-N2  intersection-stratum regularity criterion
X033-N3  maximal-building-set marked legality
X033-N4  wonderful product-blowup to ordinary-centre word
X033-N5  layerwise passive and logarithmic SNC safety
X033-N6  strict intersection-defect descent
X033-N7  Fitting-discriminant strict residual recursion
X033-N8  wonderful-word hereditary no-reset
X033-N9  wonderful-word strict macro rank
X033-N10 universal actual-centre-word certificate
```

The next maximum-posterior mission is `X033-N1 + X033-N6`: construct the configuration-difference packet on compatible étale graph charts and prove a clean-or-strict-defect alternative for every zero scheme.

## Annals-series planning posterior

The D001 six-paper architecture remains the current maximum-likelihood publication plan:

```text
Paper I    82 pages   intrinsic states and finite packets
Paper II  108 pages   cokernel obstructions, wonderful arrangements and centre words
Paper III 116 pages   joint legality and hereditary transform
Paper IV   96 pages   defect carriers and causal termination
Paper V    74 pages   functorial globalization and principalization
Paper VI   44 pages   final resolution theorem and reproducibility
Total     520 Annals/AMS-equivalent pages
```

This planning estimate has no theorem effect.

## Truth boundary

```text
X033_SOURCE_WRITTEN                              = true
X033_CLEANROOM_GREEN                             = false
SCHEME_WONDERFUL_GEOMETRY_FORMALIZED             = false
PROJECT_SPECIFIC_LAYER_GATES_PROVED              = false
INTERSECTION_DEFECT_STRICT_DESCENT_PROVED        = false
UNIVERSAL_ACTUAL_CENTRE_SYNTHESIS_PROVED         = false
NEW_DECLARATIONS_PROMOTED                        = false
CERTIFIED_GRAPH_CHANGED                          = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED               = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION       = false
FORMAL_GLOBAL_STATUS                             = OPEN_GAP
```

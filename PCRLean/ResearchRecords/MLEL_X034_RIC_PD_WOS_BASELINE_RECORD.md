# MLEL-X034 / RIC-PD-WOS — Baseline Research Record

## Regular-Intersection Collapse, Projectivity Discriminants, and Wonderful Ordinary Serialization

**Date:** 2026-08-04  
**Protocol:** `PCR-FRACTAL-PROOF-LEAN 1.0 / MLEL-A003-FPE-EDGE`  
**Accepted theorem parent:** `MLEL-M004 / HMC-SCCD`  
**Experimental parents:** `MLEL-X031`, `MLEL-X032`, `MLEL-X033`  
**Draft validation PR:** `#44`  
**Base branch:** `pcr-fractal-x034-ric-pd-wos-base-20260804`  
**Base SHA:** `5ea6548833cdf3a63a43b6bec12e6a59aba0bd45`  
**Head SHA:** `97dbe06832c7da841a56038419f176dc28dcca92`  
**Clean-room run:** `30873201226` (`queued` at archival)  
**Promotion:** none  
**Global status:** `OPEN_GAP`

## Candidate-graph correction

The X033 implication

```text
Tor_1^R(R/I,R/J)=0 -> clean/legal critical pair
```

is rejected. Tor vanishing is only the zero-excess/transverse chamber. Nested
regular centres and smooth centres with common normal directions can have
nonzero Tor excess and still meet cleanly.

The corrected principal edge is

```text
all nonempty scheme-theoretic intersection strata regular immersions
-> conormal maps surjective between finite-projective modules
-> finite-projective excess kernels, possibly nonzero
-> clean arrangement
-> deepest-first wonderful ordinary-centre serialization.
```

The corrected defect edge is

```text
first nonregular/non-quasi-regular/jointly-illegal stratum
-> canonical conormal/normal-cone/Fitting/owner/boundary defect
-> strict Schur-Fitting / DFK-KR recursion.
```

## Exact Lean leaves written

- `PCRLean.Experimental.TorExcessIsZeroExcess`;
- `PCRLean.Experimental.SplitExcessKernel`;
- `PCRLean.Experimental.ProjectivityDiscriminantPrime`;
- `PCRLean.Experimental.X034RegularIntersectionIndex` and audit target.

The source proves nested Tor no-go, projectivity of a split excess kernel, and
the prime-product containment law used by the proposed projectivity
discriminant. It does not prove the scheme-level Regular-Intersection Collapse,
wonderful serialization, strict first-defect descent, hereditary no-reset, or
resolution.

## Projectivity discriminant target

For a finitely presented module `M` over a Noetherian ring,

```text
Delta_r(M) = Fitt_r(M) * Ann(Fitt_{r-1}(M)),
Delta_proj(M) = sum_r Delta_r(M).
```

The proposed point-locus identities are

```text
D(Delta_r(M)) = rank-r free locus,
D(Delta_proj(M)) = finite-projective locus.
```

The prime-product Boolean edge is written; the full Fitting-annihilator theorem
remains open.

## Maximum-likelihood Annals series

The current central estimate is **six papers / 550 dense-equivalent pages**:

```text
Paper I    88
Paper II  114
Paper III 120
Paper IV  102
Paper V    78
Paper VI   48
Total     550
```

## Truth boundary

```text
X034_SOURCE_WRITTEN                         = true
X034_MACHINE_CHECKS_PASSED                 = true
X034_CLEANROOM_GREEN                       = false
REGULAR_INTERSECTION_COLLAPSE_PROVED       = false
WONDERFUL_SERIALIZATION_PROVED             = false
FIRST_DEFECT_STRICT_DROP_PROVED            = false
NEW_DECLARATIONS_PROMOTED                  = false
CERTIFIED_GRAPH_CHANGED                    = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION = false
FORMAL_GLOBAL_STATUS                       = OPEN_GAP
```

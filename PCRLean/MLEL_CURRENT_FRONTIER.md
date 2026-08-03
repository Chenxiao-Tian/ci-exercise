# MLE–Lean Current Frontier

**Current accepted node:** `MLEL-M004 / HMC-SCCD`  
**Current archived experimental frontier:** `MLEL-X031 / ACI-MMR-OIH`  
**Current proof-architecture node:** `MLEL-D001 / FCPP-ATLAS`  
**Official baseline branch:** `pcr-lean-formalization-20260801`  
**Experimental source branch:** `pcr-jump-integral-heredity-20260803`  
**X031 frozen source head:** `1edbe17181b638c366bf650b578e4d5f40e89185`  
**X031 clean-room:** PR `#31`, run `30854334500` (`queued` at archival)  
**D001 architecture branch:** `pcr-blueprint-d001-20260803`  
**D001 clean-room:** PR `#32`, run `30858121934`, job `91833782154` (`queued` at revalidation)  
**D001 independent topology audit:** `MLEL-D001-A001`, all static checks passed  
**Global status:** `OPEN_GAP`  
**General resolution proved:** `false`

## Certified frontier

`MLEL-M004 / HMC-SCCD` remains the highest accepted kernel-verified node. It certifies realized finite Hasse-Morita active/passive core descent and a conditional source-causal termination backend in their exact restricted domains. No 2026-08-03 experimental or architecture declaration is imported into `CertifiedIndex`.

## Experimental mathematical frontier — X031

```text
finite affine conormal packet
-> zero-obstruction maximal-minor graph branch
   or nonzero intrinsic order-ideal hybrid branch
-> actual affine centre candidate
```

X031 is `EXACTLY_DEFINED / PROOF_TERMS_WRITTEN / CLEANROOM_PENDING`, not kernel-certified.

## Proof-architecture frontier — D001

The controlling plan is a six-paper, 520-page-equivalent proof series:

```text
Paper I   FND   82 pages   intrinsic states, equivalences, finite packets
Paper II  CTR  108 pages   actual-centre synthesis and regularization
Paper III HER  116 pages   joint legality and hereditary all-chart reentry
Paper IV  TRM   96 pages   birth, defect, recurrent classes, termination
Paper V   GLB   74 pages   global descent and functorial serialization
Paper VI  FIN   44 pages   final resolution theorem and reproducibility
```

The dictionary contains 65 load-bearing groups, 325 uniformly numbered `DEF/LEM/PROP/THM/COMP` entries and 1,340 explicit dependency edges.

Independent audit `MLEL-D001-A001` verifies:

```text
unique dictionary IDs                         = true
five entries per group                        = true
all dependency endpoints exist                = true
full 325-node DAG acyclic                     = true
stored topological order complete             = true
Lean group cases                              = 65
Lean dependency table equals JSON group graph = true
page budget equals FCPP-LEN                    = true
```

The architecture Lean file checks only that every dependency lowers a finite rank and that a `ProofPackage` for all groups yields final node G65. It proves no open mathematical obligation.

## Critical theorem spine

```text
G01-G13   semantic state and finite intrinsic packet
G14-G26   universal actual centre / centre-word synthesis
G27-G41   joint legality and hereditary no-reset transform
G42-G53   birth/defect/SCC elimination and local termination
G54-G61   ideal-sheaf descent and finite functorial globalization
G62-G65   embedded/nonembedded resolution and paper-Lean audit
```

## Exact open load-bearing groups

```text
G26       universal actual-centre synthesis
G31       universal joint active/passive/boundary legality
G41       hereditary all-chart reentry without reset
G43       complete geometric birth realization
G47       recurrent-SCC exit theorem
G49-G53   immediate-defect carrier and complete termination rank
G54-G60   non-affine descent, functorial serialization and global sequence
G62-G65   final theorem, consequences and semantic proof/code closure
```

## Canonical load set

```text
PCRLean/FORMAL_STATUS.md
PCRLean/FORMAL_FRONTIER.md
PCRLean/MLEL_CURRENT_FRONTIER.md
PCRLean/ResearchRecords/MLEL_X031_ACI_MMR_OIH_REPORT.md
PCRLean/ResearchRecords/MLEL_D001_FCPP_ATLAS_BASELINE.md
PCRLean/ResearchRecords/MLEL_D001_TOPOLOGY_AUDIT_2026-08-03.md
PCRLean/Blueprint/FinalProofBlueprint.lean
MLEL_M004_HMC_SCCD_REPORT.md
```

## Truth boundary

```text
MLEL_M004_ACCEPTED                         = true
MLEL_X031_ARCHIVED                         = true
MLEL_D001_ARCHITECTURE_FROZEN              = true
D001_INDEPENDENT_TOPOLOGY_AUDIT_PASSED     = true
D001_ARCHITECTURE_CLEANROOM_GREEN          = false
EXPERIMENTAL_RESULTS_PROMOTED              = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED         = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION = false
FORMAL_GLOBAL_STATUS                       = OPEN_GAP
```

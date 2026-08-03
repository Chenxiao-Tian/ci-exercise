# PCRLean formal status

This branch is the official persistent MLE-Lean research line of the positive-characteristic-resolution program.

- Research line: `PCR-MLE-LEAN`
- GitHub branch: `pcr-lean-formalization-20260801`
- Pull request: `#2` (draft, open, unmerged)
- Current accepted formal node: `MLEL-M004 / HMC-SCCD`
- Current archived experimental frontier: `MLEL-X031 / ACI-MMR-OIH`
- Current proof-architecture node: `MLEL-D001 / FCPP-ATLAS`
- Default jump-search protocol: `PCR-JUMP-LEAN 2.0 / MLEL-A002-JUMP2`
- Accepted page-planning parameter: `PCR-PARAM-001 / FCPP-LEN = 520`
- Audited certified-code head: `0f57fe5fa3a8541e0b95d717f94085b45b960d7c`
- Global status: `OPEN_GAP`
- Arbitrary-dimensional positive-characteristic resolution proved: `false`

Baseline inclusion preserves evidence labels. A declaration is certified only at an exact successful kernel build and axiom audit; an experimental or architecture archive entry does not enter the Certified Graph.

## Certified layer

The latest certified evidence remains:

```text
full PCRLean kernel run = 30769310996, job = 91553530229, success
HMC-SCCD run            = 30769310950, job = 91553529694, success
```

The accepted restricted exits are the finite Hasse-Morita active/passive descent layer and the conditional source-causal termination backend recorded in `MLEL_M004_HMC_SCCD_REPORT.md`.

No 2026-08-03 experimental or proof-architecture declaration is imported into `CertifiedIndex`.

## Archived experimental frontier — X031 / ACI-MMR-OIH

The frozen centre-synthesis architecture joins two affine branches:

```text
zero obstruction
-> maximal-minor cover + augmented-minor vanishing
-> unique global solution
-> full packet ideal = actual graph-centre ideal
```

and

```text
nonzero cokernel obstruction
-> intrinsic order ideal
-> zero / proper-hybrid / unit trichotomy
-> finite cardinal-minimal marked closure
-> graph-plus-defect centre
```

Source and clean-room record:

```text
branch = pcr-jump-integral-heredity-20260803
head   = 1edbe17181b638c366bf650b578e4d5f40e89185
PR     = #31
run    = 30854334500
status = queued at archival
```

Evidence label: `EXACTLY-DEFINED / PROOF-TERMS-WRITTEN / CLEANROOM-PENDING`.

## Accepted proof-architecture planning node — D001 / FCPP-ATLAS

The controlling architecture is a six-paper, 520-page-equivalent series:

```text
FND  82 pages   intrinsic states, equivalences and finite packets
CTR 108 pages   actual-centre synthesis and regularization
HER 116 pages   joint legality and hereditary all-chart reentry
TRM  96 pages   birth, defect, recurrent classes and termination
GLB  74 pages   global descent and functorial serialization
FIN  44 pages   final theorem, consequences and reproducibility
```

It contains:

```text
65 load-bearing groups
325 uniformly numbered DEF/LEM/PROP/THM/COMP entries
1,340 explicit dependency edges
an acyclic full dictionary DAG
```

The independent audit `MLEL-D001-A001` verified the JSON/CSV/PDF/Lean topology, including exact equality of the JSON 65-group dependency graph and the Lean dependency table.

Architecture-only Lean target:

```text
branch = pcr-blueprint-d001-20260803
PR     = #32
run    = 30858121934
job    = 91833782154
status = queued at revalidation
```

`PCRLean.Blueprint.FinalProofAtlas.blueprint_implies_final_claim` states only that a proof package for every declared group yields the final group. It assumes no open mathematical bridge and proves no general resolution theorem by itself.

## Exact unresolved load-bearing spine

```text
G26       universal actual-centre synthesis
G31       joint active/passive/boundary legality
G41       hereditary all-chart no-reset reentry
G43       complete geometric birth realization
G47       recurrent-SCC exit
G49-G53   immediate defect and complete termination rank
G54-G60   non-affine descent and finite functorial globalization
G62-G65   final resolution, consequences and paper-Lean closure
```

## Current truth statement

```text
MLEL_M004_ACCEPTED                          = true
MLEL_X031_ARCHIVED                          = true
MLEL_D001_ARCHITECTURE_FROZEN               = true
D001_INDEPENDENT_TOPOLOGY_AUDIT_PASSED      = true
D001_ARCHITECTURE_CLEANROOM_GREEN           = false
EXPERIMENTAL_THEOREMS_PROMOTED              = false
GENERAL_GEOMETRIC_REALIZATION               = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED          = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION  = false
FORMAL_GLOBAL_STATUS                        = OPEN_GAP
```

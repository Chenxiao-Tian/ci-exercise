# PCRLean formal status

This branch is the official persistent MLE–Lean research line of the positive-characteristic-resolution program.

- Research line: `PCR-MLE-LEAN`
- GitHub branch: `pcr-lean-formalization-20260801`
- Pull request: `#2` (draft, open, unmerged)
- Current accepted formal node: `MLEL-M004 / HMC-SCCD`
- Current experimental archive node: `MLEL-X20260803-GRAPH-MACRO-SNC`
- Default jump-search protocol: `PCR-JUMP-LEAN 2.0 / MLEL-A002-JUMP2`
- Audited certified-code head: `0f57fe5fa3a8541e0b95d717f94085b45b960d7c`
- Global status: `OPEN_GAP`
- Arbitrary-dimensional positive-characteristic resolution proved: `false`

Baseline inclusion preserves evidence labels. A declaration is certified only at an exact successful kernel build and axiom audit; an experimental archive entry does not enter the Certified Graph.

## Certified layer

The latest certified evidence remains:

```text
full PCRLean kernel run = 30769310996, job = 91553530229, success
HMC-SCCD run            = 30769310950, job = 91553529694, success
```

The accepted restricted exits are the finite Hasse–Morita active/passive descent layer and the conditional source-causal termination backend recorded in `MLEL_M004_HMC_SCCD_REPORT.md`.

No 2026-08-03 experimental theorem is imported into `CertifiedIndex`.

## Historical MLEL-002 repair frontier

The last dedicated certified-baseline repair run was:

```text
run = 30769310958
job = 91553529729
result = failure
```

At that checkpoint `CoordinateBoundarySNC` and `CoordinateRootPacket` still failed. Later experimental graph-centre work does not silently certify the old MLEL-002 chain.

## Archived experimental frontier — 2026-08-03

By explicit user instruction, every research output of the current PCR-JUMP-LEAN conversation is archived while theorem promotion remains separate.

Archival report:

```text
PCRLean/ResearchRecords/MLEL_JUMP_GRAPH_MACRO_FRONTIER_2026-08-03.md
```

Experimental source:

```text
branch = pcr-jump-integral-heredity-20260803
head   = 2fd1b04b47915745e189b92859688436968f9466
```

Exact clean-room target:

```text
PR     = #25
run    = 30839499119
status = queued at synchronization
```

The strongest local macro now combines, for one actual polynomial graph centre:

- proper nonwhole finite-type regular centre data;
- Frobenius-normal filtration and arbitrary-mark active permissibility;
- exact controlled transforms on every standard chart;
- terminality or residual ideal `(E_k)^(p^e-mark)`;
- induced-flat passive Tor safety along every centre power;
- flat passive restriction to the centre;
- exact regular intersection with every finite coefficient-boundary stratum;
- exact preservation and reflection of ordered boundary regular sequences;
- source-preserving classification of exceptional debt as cleanup rather than birth;
- strict concrete finite-source rank decrease.

Integrated module:

```text
PCRLean.Experimental.PolynomialGraphLocalResolutionMacro
```

Evidence label:

```text
EXPERIMENTAL-WRITTEN-CLEANROOM-PENDING
```

not kernel-certified and not promoted.

## Exact unresolved frontiers

1. universal finite intrinsic Frobenius–Hasse packet extraction and gluing;
2. universal actual-centre synthesis, including hybrid, nonlinear and rank-zero cases;
3. scheme-level étale graph-atlas formalization and exact ideal/chart descent;
4. arbitrary passive modules, full normal flatness and global SNC/divisor gluing;
5. hereditary reconstruction of every differential packet and ledger after all charts and normalization operations;
6. geometric finite-source supports for genuine births, with no split or clone;
7. projection-free immediate-defect escape;
8. finite functorial globalization and final principalization/resolution compilers.

No frontier may be crossed by `axiom`, `sorry`, `admit`, an unproved typeclass instance, stale CI evidence, semantic weakening or an Experimental-to-Certified import.

## Current truth statement

```text
MLEL_M004_ACCEPTED                          = true
HMC_SCCD_RESTRICTED_KERNEL_EXIT             = true
PCR_JUMP_LEAN_2_0_BASELINE_PROTOCOL         = true
ALL_CURRENT_CONVERSATION_OUTPUTS_ARCHIVED   = true
LATEST_EXPERIMENTAL_SNC_MACRO_WRITTEN       = true
LATEST_EXPERIMENTAL_CLEANROOM_GREEN         = false
EXPERIMENTAL_THEOREMS_PROMOTED              = false
GENERAL_GEOMETRIC_REALIZATION               = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION  = false
FORMAL_GLOBAL_STATUS                        = OPEN_GAP
```
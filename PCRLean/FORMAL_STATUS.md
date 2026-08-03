# PCRLean formal status

This branch is the official persistent MLE–Lean research line of the positive-characteristic-resolution program.

- Research line: `PCR-MLE-LEAN`
- GitHub branch: `pcr-lean-formalization-20260801`
- Pull request: `#2` (draft, open, unmerged)
- Current accepted formal node: `MLEL-M004 / HMC-SCCD`
- Current experimental archive node: `MLEL-X20260803-GRAPH-MACRO`
- Default jump-search protocol: `PCR-JUMP-LEAN 2.0 / MLEL-A002-JUMP2`
- Audited certified-code head: `0f57fe5fa3a8541e0b95d717f94085b45b960d7c`
- Global status: `OPEN_GAP`
- Arbitrary-dimensional positive-characteristic resolution proved: `false`

Baseline inclusion preserves evidence labels. A Lean declaration is certified only in the exact domain built and audited by the kernel; an MLE manuscript remains an estimate; a conditional compiler does not establish universal geometric hypotheses; an experimental archive entry does not enter the Certified Graph.

## Current green certified layer

At the audited certified-code head, the full PCRLean kernel workflow completed successfully:

```text
workflow = PCR Lean kernel verification
run      = 30769310996
job      = 91553530229
result   = success
```

The dedicated HMC-SCCD workflow also completed successfully:

```text
workflow = PCR HMC-SCCD verification
run      = 30769310950
job      = 91553529694
result   = success
```

The certified restricted exits include:

- finite multiplication/Hasse packet classification and matrix-unit generation;
- active Hasse-only saturation and exact Frobenius-core descent;
- passive block Morita descent to one common row core;
- simultaneous active Hasse core and passive Morita row-core construction;
- proper finitely generated active core over a Noetherian base, conditional on proper saturation;
- a well-founded lexicographic rank coupling fixed-ancestor Noetherian trace memory to the finite-source generational rank;
- conditional finite termination for source-causal programs and fully gated ordinary-centre systems.

Principal declarations remain the `PCRLean.HMCSCCD` theorem family recorded in `MLEL_M004_HMC_SCCD_REPORT.md`.

## Earlier MLEL-002 repair frontier

The last dedicated `MLEL-002 / FCR-GEO` repair run recorded in the certified baseline was:

```text
workflow = PCR MLEL-002 verification
run      = 30769310958
job      = 91553529729
result   = failure
placeholder rejection = success
axiom audit = skipped after build failure
```

At that checkpoint the failure set had been reduced to:

```text
PCRLean.CoordinateBoundarySNC
PCRLean.CoordinateRootPacket
```

This historical repair state remains recorded; later experimental graph-centre work does not silently certify the old MLEL-002 chain.

## Archived experimental frontier — 2026-08-03

By explicit user instruction, every research output of the current PCR-JUMP-LEAN conversation is archived in the MLE–Lean research baseline, while theorem promotion remains separate.

The exact archival record is:

```text
PCRLean/ResearchRecords/MLEL_JUMP_GRAPH_MACRO_FRONTIER_2026-08-03.md
```

Experimental source:

```text
branch = pcr-jump-integral-heredity-20260803
head   = 2da9394f1ce1c74e30382595ec8bc9e7b88a7e39
```

Exact clean-room target:

```text
PR     = #24
run    = 30837634276
status = queued at archival synchronization
```

The strongest local experimental macro combines, for one polynomial graph centre:

- actual proper finite-type regular centre data;
- Frobenius-normal ideal powers and arbitrary-mark active permissibility;
- exact controlled transforms on every standard chart;
- residual ideal `(E_k)^(p^e-mark)`;
- induced-flat passive Tor safety along every centre power;
- flat passive restriction to the centre;
- exact regular intersection with every finite coefficient-boundary stratum;
- source-preserving classification of exceptional debt as cleanup rather than birth;
- strict concrete finite-source rank decrease.

The integrated experimental module is:

```text
PCRLean.Experimental.PolynomialGraphLocalResolutionMacro
```

This is currently `EXPERIMENTAL-WRITTEN-CLEANROOM-PENDING`, not kernel-certified and not imported by `CertifiedIndex`.

## Exact unresolved frontiers

1. universal intrinsic finite Frobenius–Hasse packet extraction and presentation-independent gluing;
2. universal actual-centre synthesis, including hybrid, nonlinear and rank-zero cases;
3. scheme-level étale graph-atlas formalization and exact ideal/chart descent;
4. arbitrary passive modules, full normal flatness and genuine SNC/codimension legality beyond the induced-flat/regular-strata chamber;
5. hereditary reconstruction of every differential packet and ledger after all charts, cleaning, saturation, normalization and integral closure;
6. geometric finite-source support for genuine births, with no split and no clone;
7. projection-free immediate-defect escape;
8. finite functorial globalization and the principalization/resolution compilers.

No frontier may be crossed by `axiom`, `sorry`, `admit`, an unproved typeclass instance, stale CI evidence, or an imported experimental theorem.

## Baseline method protocol

`PCR-JUMP-LEAN 2.0` remains the default protocol. It preserves PCR-JUMP-LEAN 1.0 and adds evidence levels E0–E10, exact-commit clean-room CI, the Experimental-to-Certified import firewall, bridge queue B00–B21 and missions IFCCS, HKITF, CSCN, with RZRC as the rank-zero fallback.

Protocol adoption and research archival do not promote experimental declarations.

## Current truth statement

```text
MLEL_M004_ACCEPTED                          = true
HMC_SCCD_RESTRICTED_KERNEL_EXIT             = true
PCR_JUMP_LEAN_2_0_BASELINE_PROTOCOL         = true
ALL_CURRENT_CONVERSATION_OUTPUTS_ARCHIVED   = true
LATEST_EXPERIMENTAL_LOCAL_MACRO_WRITTEN     = true
LATEST_EXPERIMENTAL_CLEANROOM_GREEN         = false
EXPERIMENTAL_THEOREMS_PROMOTED              = false
GENERAL_GEOMETRIC_REALIZATION               = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION  = false
FORMAL_GLOBAL_STATUS                        = OPEN_GAP
```

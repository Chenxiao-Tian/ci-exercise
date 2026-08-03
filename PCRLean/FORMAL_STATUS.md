# PCRLean formal status

This branch is the official persistent MLE–Lean research line of the positive-characteristic-resolution program.

- Research line: `PCR-MLE-LEAN`
- GitHub branch: `pcr-lean-formalization-20260801`
- Pull request: `#2` (draft, open, unmerged)
- Current formal node: `MLEL-M004 / HMC-SCCD`
- Default jump-search protocol: `PCR-JUMP-LEAN 2.0 / MLEL-A002-JUMP2`
- Audited code head: `0f57fe5fa3a8541e0b95d717f94085b45b960d7c`
- Global status: `OPEN_GAP`
- Arbitrary-dimensional positive-characteristic resolution proved: `false`

Baseline inclusion preserves evidence labels. A Lean declaration is certified only in the exact domain built and audited by the kernel; an MLE manuscript remains an estimate; a conditional compiler does not establish universal geometric hypotheses; a failed dedicated workflow remains failed.

## Current green certified layer

At the audited code head, the full PCRLean kernel workflow completed successfully:

```text
workflow = PCR Lean kernel verification
run      = 30769310996
job      = 91553530229
result   = success
```

The workflow completed placeholder rejection, the full certified-index build, kernel axiom audit, exact source snapshot, and audit-artifact upload.

The dedicated HMC-SCCD workflow also completed successfully at the same code head:

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

Principal declarations:

```text
PCRLean.HMCSCCD.fullPacket_stable_of_split_stable
PCRLean.HMCSCCD.passive_eq_fromRowModule_of_split_stable
PCRLean.HMCSCCD.exists_active_passive_core
PCRLean.HMCSCCD.exists_proper_fg_active_passive_core
PCRLean.HMCSCCD.causalRankLt_wellFounded
PCRLean.HMCSCCD.causalRankStep_wellFounded
PCRLean.HMCSCCD.CausalProgram.terminal_reachable
PCRLean.HMCSCCD.CausalProgram.no_infinite_execution
PCRLean.HMCSCCD.GatedSystem.every_input_resolves
PCRLean.HMCSCCD.GatedSystem.every_step_all_gates
PCRLean.HMCSCCD.GatedSystem.no_infinite_branch
```

## Current MLEL-002 repair frontier

The dedicated `MLEL-002 / FCR-GEO` workflow was rerun after fifteen repair commits. Placeholder rejection succeeded, and the earlier failure set was substantially reduced:

```text
workflow = PCR MLEL-002 verification
run      = 30769310958
job      = 91553529729
result   = failure
axiom audit = skipped after build failure
```

Current failing modules and exact first errors:

```text
PCRLean.CoordinateBoundarySNC
  line 38: parser error around an invalid `rcases` pattern

PCRLean.CoordinateRootPacket
  line 75: invalid `⟨...⟩` notation because the expected type is not determined
```

The latest dedicated build now succeeds for several modules that failed in the preceding audit, including:

```text
PCRLean.CoordinateCentreKernelBridge
PCRLean.CoordinatePassiveSafety
PCRLean.MultiOwnerHasseCore
PCRLean.CoordinateCentreProper
```

Thus the repair is real but incomplete. `MLEL-002 / FCR-GEO` remains a candidate restricted geometric chamber rather than a certified complete chain. The success of `HMCSCCD.lean` does not silently certify the remaining boundary-SNC and root-packet obligations.

## Exact unresolved frontiers

1. close the two current reduced-chamber Lean failures and complete the dedicated axiom audit;
2. universal intrinsic finite Frobenius-frame construction and frame-independent gluing;
3. arbitrary proper Frobenius core to an actual regular finite-type owner-safe centre word;
4. universal joint active/passive/SNC legality, normal flatness, and passive Tor safety;
5. scheme-level blowup, strict transform, controlled transform, every standard chart and overlap, and hereditary no-reset after cleaning, saturation, normalization, and integral closure;
6. fully quasilinear rank-zero radicial-core descent;
7. geometric finite-source birth realization with no split and no clone;
8. projection-free immediate-defect escape and finite functorial globalization.

No frontier may be crossed by `axiom`, `sorry`, `admit`, an unproved typeclass instance, or an imported MLE assertion.

## Baseline method protocol

`PCR-JUMP-LEAN 2.0` is now the default protocol for future isolated jump-search missions. Its canonical baseline files are:

```text
PCRLean/ResearchProtocols/PCR_JUMP_LEAN_2_0_BASELINE.md
PCRLean/ResearchProtocols/PCR_JUMP_LEAN_2_0_BASELINE_RECORD.json
```

The protocol adds evidence levels E0–E10, exact-commit clean-room CI, an Experimental-to-Certified import firewall, the bridge queue B00–B21, and the priority missions IFCCS, HKITF, CSCN, with RZRC as the rank-zero fallback.

Protocol adoption is methodological only. It does not change any theorem evidence label, promote an experimental declaration, or alter `OPEN_GAP`.

## Current truth statement

```text
MLEL_M004_ACCEPTED                         = true
HMC_SCCD_RESTRICTED_KERNEL_EXIT            = true
MLEL_002_REPAIR_PROGRESS                   = true
MLEL_002_CURRENT_FAILED_MODULE_COUNT       = 2
MLEL_002_COMPLETE_CHAIN_CERTIFIED          = false
PCR_JUMP_LEAN_2_0_BASELINE_PROTOCOL        = true
EXPERIMENTAL_THEOREMS_PROMOTED_BY_PROTOCOL = false
GENERAL_GEOMETRIC_REALIZATION              = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION = false
FORMAL_GLOBAL_STATUS                       = OPEN_GAP
```

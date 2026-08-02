# PCRLean formal status

This branch is the official persistent MLE–Lean research line of the positive-characteristic-resolution program.

- Research line: `PCR-MLE-LEAN`
- GitHub branch: `pcr-lean-formalization-20260801`
- Pull request: `#2` (draft, open, unmerged)
- Current formal node: `MLEL-M004 / HMC-SCCD`
- Global status: `OPEN_GAP`
- Arbitrary-dimensional positive-characteristic resolution proved: `false`

Baseline inclusion preserves evidence labels. A Lean declaration is certified only in the exact domain built and audited by the kernel; an MLE manuscript remains an estimate; a conditional compiler does not establish universal geometric hypotheses; a failed dedicated workflow remains failed.

## Current green certified layer

At branch head `be31eeea5249e87f99a2d0e8390e69d4f7aeabd6`, the full PCRLean kernel workflow completed successfully:

```text
workflow = PCR Lean kernel verification
run      = 30768792809
job      = 91552178167
result   = success
```

The workflow completed placeholder rejection, the full certified build, kernel axiom audit, exact source snapshot, and audit-artifact upload.

The dedicated HMC-SCCD workflow also completed successfully:

```text
workflow = PCR HMC-SCCD verification
run      = 30768792795
job      = 91552174841
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

## Current failed candidate chain

The dedicated `MLEL-002 / FCR-GEO` end-to-end workflow is not green at the current branch head:

```text
workflow = PCR MLEL-002 verification
run      = 30768792785
job      = 91552174757
result   = failure
```

The current failing modules are:

```text
PCRLean.CoordinateBoundarySNC
PCRLean.CoordinateCentreKernelBridge
PCRLean.CoordinatePassiveSafety
PCRLean.CoordinateCentrePrincipalization
PCRLean.MultiOwnerHasseCore
```

Accordingly, `MLEL-002 / FCR-GEO` remains a candidate restricted geometric chamber. It is not a currently certified complete chain. The success of `HMCSCCD.lean` does not silently certify these separate coordinate, boundary, passive-safety, principalization, or multi-owner modules.

## Exact unresolved frontiers

1. universal intrinsic finite Frobenius-frame construction and frame-independent gluing;
2. arbitrary proper Frobenius core to an actual regular finite-type owner-safe centre word;
3. universal joint active/passive/SNC legality, normal flatness, and passive Tor safety;
4. scheme-level blowup, strict transform, controlled transform, every standard chart and overlap, and hereditary no-reset after cleaning, saturation, normalization, and integral closure;
5. fully quasilinear rank-zero radicial-core descent;
6. geometric finite-source birth realization with no split and no clone;
7. projection-free immediate-defect escape;
8. finite functorial globalization and derivation of principalization, embedded resolution, and nonembedded resolution.

No frontier may be crossed by `axiom`, `sorry`, `admit`, an unproved typeclass instance, or an imported MLE assertion.

## Current truth statement

```text
MLEL_M004_ACCEPTED                         = true
HMC_SCCD_RESTRICTED_KERNEL_EXIT            = true
MLEL_002_COMPLETE_CHAIN_CERTIFIED          = false
GENERAL_GEOMETRIC_REALIZATION              = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION = false
FORMAL_GLOBAL_STATUS                       = OPEN_GAP
```

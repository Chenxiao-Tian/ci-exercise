# PCRLean exact formal frontier

This branch contains genuine Lean kernel checks and a separately labelled archive of experimental research. It does not contain a proof of arbitrary-dimensional resolution in positive characteristic.

## Certified Hasse--Morita core layer

On a declared realized finite product Frobenius frame, the kernel-checked layer proves:

1. multiplication/Hasse packet classification and matrix-unit generation;
2. active Hasse-only saturation and exact core descent;
3. passive block Morita descent to one row core;
4. simultaneous active and passive core construction;
5. proper finitely generated active core over a Noetherian base, conditional on proper saturation.

Principal declarations:

```text
PCRLean.HMCSCCD.fullPacket_stable_of_split_stable
PCRLean.HMCSCCD.passive_eq_fromRowModule_of_split_stable
PCRLean.HMCSCCD.exists_active_passive_core
PCRLean.HMCSCCD.exists_proper_fg_active_passive_core
```

These theorems do not construct a universal Frobenius frame or a universal regular centre.

## Certified source-causal backend

A fixed-ancestor Noetherian trace module coupled to the finite-source generational rank gives a well-founded relation. For a supplied geometric program carrying all centre, owner, passive, boundary, chart, overlap, reentry and rank certificates, the existing compiler proves finite reachability and excludes infinite branches.

Principal declarations:

```text
PCRLean.HMCSCCD.causalRankLt_wellFounded
PCRLean.HMCSCCD.causalRankStep_wellFounded
PCRLean.HMCSCCD.CausalProgram.terminal_reachable
PCRLean.HMCSCCD.CausalProgram.no_infinite_execution
PCRLean.HMCSCCD.GatedSystem.every_input_resolves
PCRLean.HMCSCCD.GatedSystem.every_step_all_gates
PCRLean.HMCSCCD.GatedSystem.no_infinite_branch
```

This is a conditional backend, not universal geometry.

## Archived experimental graph-macro frontier

The archival record

```text
PCRLean/ResearchRecords/MLEL_JUMP_GRAPH_MACRO_FRONTIER_2026-08-03.md
```

summarizes the current strongest experimental chamber. Its source branch is

```text
pcr-jump-integral-heredity-20260803
```

at dependency-index head

```text
2da9394f1ce1c74e30382595ec8bc9e7b88a7e39.
```

The local macro assembles:

```text
actual polynomial graph centre
exact quotient and regular centre ring
Frobenius-normal filtration
arbitrary-mark active permissibility
induced-flat passive Tor safety and flat centre restriction
exact regular intersection with finite coefficient-boundary strata
all standard chart factorizations
terminality or pure exceptional debt
source-preserving cleanup and strict finite-source rank decrease
```

The exact clean-room target is PR #24, run `30837634276`; it was queued when archived. Hence this chamber remains experimental and is not imported by the Certified Graph.

## Mathematical bridge now localized

Over a perfect field, a regular finite-type centre is smooth, and a closed immersion between smooth schemes is étale-locally a coordinate subspace. Consequently, after an actual regular centre has been constructed, existence of local coordinate/graph models is standard geometry. The formal frontier is to implement that scheme-level atlas and descend the exact ideals, charts, passive data, boundary strata and history without reset.

## Exact unresolved goals

### U1. Universal packetization

Construct a finite, intrinsic, presentation-independent Frobenius--Hasse state from arbitrary marked/differential Rees data and prove compatibility with smooth/étale base change, cleaning and integral-closure equivalence.

### U2. Universal actual-centre synthesis

From arbitrary proper core/direction/Fitting data construct an actual finite-type ideal defining a regular, nonwhole, nonidentity centre in the marked singular locus. Cover hybrid and rank-zero nonlinear chambers or produce a finite certified centre word.

### U3. Scheme-level graph atlas and gluing

Formalize the étale coordinate/graph model of a regular immersion. Prove exact descent of centre ideals, chart maps, overlaps and local certificates.

### U4. Universal joint legality

Extend beyond induced-flat passive modules and regular coefficient-boundary strata. Prove arbitrary passive Tor/normal-flat safety, genuine SNC transversality and codimension compatibility for all owners, or produce an owner-safe centre word.

### U5. Hereditary transform and no reset

Define scheme-level blowup, strict/controlled transform and next-packet reconstruction on every chart and overlap. Prove cleaning, saturation, normalization and integral closure do not reset owner, source, debt or history identities.

### U6. Genuine-birth realization

Assign hereditary finite source supports to every genuinely new jump-capable identity. Prove no split and no clone. Local graph exceptional debt is already classified experimentally as cleanup, not birth.

### U7. Immediate defect

Produce a projection-free finite-type actual carrier and centre word changing the intrinsic defect/pro-isomorphism class.

### U8. Globalization

Glue and serialize local centres finitely, preserve smooth/étale functoriality, compile a global well-founded program, and derive principalization, embedded resolution and nonembedded resolution.

## Current highest-posterior architecture

```text
intrinsic finite Frobenius--Hasse packet
-> graded Frobenius normalization and ceiling marks
-> cotangent/conormal or canonical hybrid centre synthesis
-> actual regular centre or finite centre word
-> etale polynomial-graph atlas
-> joint local graph macro
-> hereditary no-reset packet reconstruction
-> source-causal birth and cleanup ledger
-> immediate-defect escape
-> Noetherian/multiset/degree/debt termination
-> finite global serialization
-> principalization and resolution
```

## Non-negotiable rule

No U1--U8 bridge may be crossed by `axiom`, `sorry`, `admit`, an unproved typeclass instance, stale CI evidence, semantic weakening, or an Experimental-to-Certified import. A complete proof exists only when the exact general main theorem and every dependency are kernel-checked and the paper/Lean semantics agree.

```text
CURRENT_CERTIFIED_NODE                     = MLEL-M004 / HMC-SCCD
LATEST_EXPERIMENTAL_LOCAL_MACRO_WRITTEN    = true
LATEST_EXPERIMENTAL_CLEANROOM_GREEN        = false
LATEST_EXPERIMENTAL_RESULTS_PROMOTED       = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED         = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION = false
FORMAL_GLOBAL_STATUS                       = OPEN_GAP
```

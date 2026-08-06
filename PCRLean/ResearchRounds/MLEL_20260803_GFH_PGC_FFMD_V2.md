# MLEL Experimental Research Record V2 — 2026-08-03

## Graded Frobenius Heredity, Polynomial-Graph Centres, Boundary Transversality, Passive Gates, and Finite Exceptional Debt

**Protocol:** PCR-JUMP-LEAN 2.0 / MLEL-A002-JUMP2  
**Official accepted Certified node:** MLEL-M004 / HMC-SCCD  
**Certified Graph changed:** no  
**Experimental results promoted:** no  
**General positive-characteristic resolution proved:** no  
**Global truth state:** `OPEN_GAP`

## Persistent full record

The complete round report, conversation-output audit, machine state, exact
clean-room logs, per-module matrix, source slice, API probes and hashes are
stored in the persistent MLE–Lean library:

```text
/正特征奇点消解/MLE-Lean线/ResearchRounds/
  2026-08-03_GFH_PGC_FFMD_V2/

/正特征奇点消解/MLE-Lean线/ResearchRounds/
  PCR_MLE_LEAN_BASELINE_SUPPLEMENT_2026-08-03_V2.zip
```

The machine-readable status and clean-room logs in that package are the
authoritative evidence for exact build and axiom-audit outcomes.  This summary
does not upgrade a proof-written declaration merely because its source exists.

## Mathematical advances in this record

### 1. Graded Frobenius heredity

Bare integral equivalence is too weak.  The correct presentation language must
retain marks.  The current experimental interface reflects

```text
x^(p^e) ∈ I^m
  ↔
x ∈ I^(ceil(m / p^e))
```

under a graded-power/normal-cone nonvanishing hypothesis.  Arbitrary mark
compression creates an explicitly bounded exceptional exponent.

### 2. Actual polynomial-graph centres

For a graph ideal

```text
I_h = (Z_i - h_i)
```

in a polynomial algebra over a Noetherian regular domain, the experimental
proof slice constructs:

- an actual finite-type ideal;
- non-top and non-bottom strictness;
- an exact quotient by the coefficient ring;
- regular quotient;
- Frobenius-normality;
- marked permissibility;
- every standard blowup chart.

At Frobenius block `q=p^e` and positive mark `m≤q`, every chart residual ideal
is exactly

```text
(exceptional pivot)^(q-m).
```

Thus the exact mark is terminal, while a strict submark leaves only pure
exceptional debt.

### 3. Faithfully flat marked-centre descent

The module

```text
PCRLean.Experimental.FaithfullyFlatMarkedCentreDescent
```

separates the local-to-global algebraic content of an adapted graph atlas.  It
attempts, with no project axiom, to descend:

- ideal containment and equality;
- centre uniqueness;
- marked permissibility;
- centre strictness;
- finite type over a Noetherian base;
- Frobenius-normality from an exact graph model.

### 4. Boundary strata and transversality

For a split retraction `A → B` with section and `J⊂B`, the proposed universal
formula is

```text
A / (ker(project) + section(J))  ≃  B / J.
```

It yields regular graph-boundary strata whenever `B/J` is regular.  Regularity
of the strata is kept distinct from SNC.

The first-order transversality gate is explicitly

```text
I ⊓ J = I * J.
```

A permanent no-go example records that the smooth divisor `(X)` is not
transverse to itself, even though the individual quotient and intersection
strata are regular.  This prevents regular quotient certificates from being
silently relabelled SNC.

For split retraction kernels, the experimental theorem proves transversality
with every boundary ideal pulled back from the retract.  A separate faithfully
flat descent module exposes ideal-intersection preservation as the precise
flatness/Tor interface.

### 5. Passive Tor gate

Passive safety is represented as injectivity after tensoring the centre-ideal
inclusion.  The source slice and API-probe records state exactly whether the
pinned mathlib flatness API discharged this condition in the current build.
The theorem is intentionally limited to flat passive modules and is not a
universal passive-owner result.

### 6. Exceptional-debt identity and termination

For a fixed finite ancestor-source type and Frobenius block `q`, a debt event is
identified by

```text
(source, positive mark in Fin q).
```

The event identity excludes chart and pivot labels.  Chart changes are local
occurrences of the same global debt and cannot be registered as fresh births.
There are at most

```text
card(Source) * q
```

possible debt identities in one block.  The proposed rank

```text
(q, card(Source)*q - registered.card)
```

decreases either when the block drops or when one genuinely fresh key is
registered.  This is the debt component of the causal termination compiler;
geometric classification of every transition remains open.

## Current exact frontier

1. construct a finite adapted étale/fpqc graph atlas for every actual regular
   candidate centre;
2. descend regular immersion, quotient regularity and conormal local freeness;
3. prove the full SNC gate: regular strata, conormal direct sum and codimension
   additivity;
4. extend passive safety beyond flat split modules;
5. descend actual blowup charts and controlled transforms through overlaps;
6. prove no-reset/no-clone for owners, source keys and exceptional debt;
7. reconstruct the next intrinsic differential packet on every chart;
8. handle nonlinear rank-zero/radicial and immediate-defect branches;
9. serialize local centre words into one finite functorial global sequence;
10. compile principalization, embedded resolution and nonembedded resolution.

## Permanent truth boundary

```text
EXPERIMENTAL_RESULTS_PROMOTED = false
CERTIFIED_GRAPH_CHANGED = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION = false
FORMAL_GLOBAL_STATUS = OPEN_GAP
```

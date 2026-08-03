# MLEL-M004 / HMC-SCCD

## Hasse--Morita Core Construction, Source-Conservative Centre Descent, and Noetherian Causal Resolution

**Date:** 2026-08-02  
**Line:** PCR-MLE-LEAN  
**Status:** `OPEN_GAP`  
**General positive-characteristic resolution proved:** `false`

## 1. Round result

This node upgrades the fourth maximum-likelihood architecture with two genuine kernel-certified restricted exits:

1. a simultaneous active/passive Hasse--Morita core theorem on realized finite product Frobenius frames;
2. a Noetherian source-causal termination compiler coupling fixed-ancestor trace memory to the finite-source generational rank.

The result does not construct the required geometric system for arbitrary singularities and therefore does not prove arbitrary-dimensional resolution in positive characteristic.

## 2. Certified Hasse--Morita core

Let `spec` be a finite product Frobenius-frame specification, let `F` be a realized frame, let `I` be an active ideal, and let `N` be a passive block submodule.

The finite packet is separated into multiplication and genuine Hasse indices. If `N` is stable under the lifted operators of both classes, Lean proves stability under the full packet and hence the Morita decomposition

```text
N = BlockMatrixStableSubmodule.fromRowModule
      (BlockMatrixStableSubmodule.rowModule N).
```

At the same time the active Hasse-only saturation descends to the base:

```text
F.hasseSaturation I = (F.core I).map (algebraMap R A).
```

The combined theorem is:

```text
exists_active_passive_core
```

which produces an active base ideal `C` and a passive row core `P` simultaneously. Over a Noetherian base, if the active saturation is proper, Lean also proves that `C` is proper and finitely generated:

```text
exists_proper_fg_active_passive_core.
```

This is an algebraic descent theorem. It does not prove that the core centre is regular or universally Tor-safe.

## 3. Certified source-causal backend

Define

```text
CausalRank = Submodule R M × GenRank.
```

The first coordinate is fixed-ancestor Noetherian trace memory. The second is the existing finite-source generational rank. The rank relation is lexicographic:

- a genuinely new independent trace strictly enlarges the trace submodule;
- with fixed trace memory, an accepted source-conservative `GenStep` strictly lowers `GenRank`.

Lean proves:

```text
causalRankLt_wellFounded
causalRankStep_wellFounded
CausalProgram.terminal_reachable
CausalProgram.no_infinite_execution.
```

For a supplied geometric system in which every step carries all mandatory ordinary-centre certificates, Lean further proves:

```text
GatedSystem.every_input_resolves
GatedSystem.every_step_all_gates
GatedSystem.no_infinite_branch.
```

The gate exposes actual finite-type ideal, regularity, marked permissibility, passive safety, SNC boundary, every standard chart, overlap gluing, hereditary reentry, nonidentity, and rank decrease. Universal existence of such a geometric system remains an open theorem.

## 4. Lean verification evidence

**Source branch commit:**

```text
5bda3cd095328e2f22ffc30187bdc0fd42719c1a
```

**GitHub Actions:**

```text
workflow = PCR HMC-SCCD verification
run      = 30768590222
job      = 91551628068
result   = success
```

The workflow established:

```text
placeholder rejection = success
lake build PCRLean.HMCSCCD = success
build jobs = 8495 / 8495
kernel #print axioms audit = success
```

Every audited theorem depends only on Lean foundational axioms:

```text
propext
Classical.choice
Quot.sound
```

No `sorryAx`, project-specific axiom, resolution axiom, or packetization axiom was detected.

**Audit artifact:**

```text
artifact id = 8839797138
artifact sha256 = d24809996dbd42d2e6f102bbe13b2b5dd340743450c02e9fe2e4a71165287243
```

## 5. Architecture update

The current highest-posterior chain is now:

```text
intrinsic finite Frobenius frame
-> finite multiplication/Hasse packet
-> all matrix units
-> simultaneous active Hasse core and passive Morita row core
-> actual regular owner-safe centre word
-> hereditary all-chart source-conservative reentry
-> Noetherian trace / finite-source causal descent
-> finite global serialization
-> principalization and resolution.
```

The first algebraic core and the final conditional termination compiler now have genuine restricted Lean certification. The unresolved burden is concentrated in the geometric middle.

## 6. Exact open frontier

1. universal intrinsic finite Frobenius-frame construction and overlap gluing;
2. arbitrary proper Frobenius core to actual regular owner-safe centre word;
3. arbitrary passive Tor safety and normal flatness beyond the split Morita chamber;
4. strict/controlled transform and hereditary no-reset on every chart and overlap;
5. universal actual finite-source birth-witness realization with no split and no clone;
6. fully quasilinear rank-zero radicial core;
7. projection-free immediate-defect escape;
8. finite functorial globalization and derivation of principalization, embedded resolution, and nonembedded resolution.

## 7. Final truth statement

```text
MLEL-M004_ACCEPTED = true
HMC_SCCD_RESTRICTED_KERNEL_EXIT = true
GENERAL_GEOMETRIC_REALIZATION = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION = false
FORMAL_GLOBAL_STATUS = OPEN_GAP
```

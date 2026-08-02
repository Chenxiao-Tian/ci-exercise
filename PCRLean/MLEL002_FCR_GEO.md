# MLEL-002 / FCR-GEO

## Frobenius-Core Regular Geometric Realization

This file records the intended scope and current evidence state of the first end-to-end split-coordinate geometric chamber of the MLE–Lean line.

## Candidate chamber target

The proposed chamber uses:

1. finitely many active owner ideals with one common positive Frobenius mark;
2. exact descent of each active owner from a base ideal;
3. a joint base core obtained from the finite supremum of owner cores;
4. a root equivalence identifying the root of the joint core with an actual coordinate-centre ideal;
5. explicit split or coordinate certificates for the passive module and the centre quotient.

The intended conclusions are:

- the joint active ideal is exactly the extension of the joint base core;
- the coordinate root centre is an actual proper finite-type ideal;
- the same centre is marked-permissible for every active owner and their finite aggregate;
- its quotient is explicitly a smaller polynomial ring, serving as an affine regular-coordinate certificate;
- on every standard coordinate blowup chart the pure Frobenius packet has unit controlled transform;
- overlap equality follows after all transformed packets become the unit ideal;
- the split passive module is preserved;
- a finite owner-support rank decreases to a terminal chamber.

## Current CI truth

At branch head `be31eeea5249e87f99a2d0e8390e69d4f7aeabd6`, the dedicated workflow did not certify this full chain:

```text
workflow = PCR MLEL-002 verification
run      = 30768792785
job      = 91552174757
result   = failure
```

Current failing modules:

```text
PCRLean.CoordinateBoundarySNC
PCRLean.CoordinateCentreKernelBridge
PCRLean.CoordinatePassiveSafety
PCRLean.CoordinateCentrePrincipalization
PCRLean.MultiOwnerHasseCore
```

The failure includes unresolved Lean goals, elaboration/typeclass errors, and—in the failed build output for `CoordinatePassiveSafety`—a declaration using `sorry`. The workflow stopped before its axiom audit. Therefore none of the complete-chain conclusions above may currently be cited as kernel-certified through `PCRLean.MLEL002Index`.

## Certified sublayer that remains valid

Separate from the failed coordinate-geometric chain, the branch has a green restricted algebraic/causal module:

```text
PCRLean.HMCSCCD
```

with successful dedicated and full-kernel workflows. It certifies simultaneous active Hasse-core/passive Morita-row-core descent on a realized finite product frame and a conditional source-causal termination backend. It does not prove the missing coordinate boundary, quotient, passive-safety, principalization, or multi-owner theorems listed above.

Thus:

```text
HMC_SCCD_RESTRICTED_KERNEL_EXIT       = true
MLEL_002_COMPLETE_CHAIN_CERTIFIED     = false
```

## Evidence boundary

Even after the dedicated MLEL-002 chain is repaired, this chamber would remain restricted. It would not prove that an arbitrary canonical Frobenius core:

- admits a root equivalence;
- is locally a coordinate ideal;
- has constant conormal rank;
- is regular and SNC-compatible without a coordinate certificate;
- is passive Tor-safe for arbitrary passive owners;
- survives strict transform, normalization, saturation, and integral closure on arbitrary overlaps;
- globalizes functorially over arbitrary schemes;
- resolves immediate defect;
- proves arbitrary-dimensional resolution in positive characteristic.

The global status remains `OPEN_GAP`.

## Research role

The chamber remains the most concrete proposed bridge

```text
finite Hasse stability
-> Frobenius descent
-> joint root centre
-> all-chart terminalization
```

but its current task is proof repair and semantic audit, not promotion to a theorem. The next universal burden remains removal of the split-coordinate hypotheses by a genuine Fitting/flattening, descent, and hereditary transform theorem.

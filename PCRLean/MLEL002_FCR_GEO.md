# MLEL-002 / FCR-GEO

## Frobenius-Core Regular Geometric Realization

This file records the intended scope and current evidence state of the first end-to-end split-coordinate geometric chamber of the MLE–Lean line.

## Candidate chamber target

The proposed chamber uses:

1. finitely many active owner ideals with one common positive Frobenius mark;
2. exact descent of each active owner from a base ideal;
3. a joint base core obtained from the finite supremum of owner cores;
4. a root or coordinate packet identifying an actual coordinate-centre ideal;
5. explicit split or coordinate certificates for the passive module, boundary packet, and centre quotient.

The intended conclusions are:

- every active owner is controlled by the extension of a joint base core;
- the coordinate root centre is an actual proper finite-type ideal;
- the same centre is marked-permissible for every active owner and their finite aggregate;
- its quotient is explicitly a smaller polynomial ring, serving as an affine regular-coordinate certificate;
- the boundary coordinate frame remains transverse/SNC-compatible;
- on every standard coordinate blowup chart the pure Frobenius packet has unit controlled transform;
- overlap equality follows after transformed root packets become the unit ideal;
- the split passive module is preserved;
- a finite owner-support rank decreases to a terminal chamber.

## Latest dedicated CI truth

At audited code head `0f57fe5fa3a8541e0b95d717f94085b45b960d7c`, the dedicated workflow completed placeholder rejection but did not certify the full chain:

```text
workflow = PCR MLEL-002 verification
run      = 30769310958
job      = 91553529729
result   = failure
axiom audit = skipped after build failure
```

The repair round reduced the failing set from five modules to two.

Current failures:

```text
PCRLean.CoordinateBoundarySNC
  line 38: parser error caused by an invalid `rcases` pattern

PCRLean.CoordinateRootPacket
  line 75: invalid `⟨...⟩` notation because the expected type is not determined
```

Current dedicated-build successes include formerly failing components:

```text
PCRLean.CoordinateCentreKernelBridge
PCRLean.CoordinatePassiveSafety
PCRLean.MultiOwnerHasseCore
PCRLean.CoordinateCentreProper
```

`CoordinateCentrePrincipalization` has been replaced in the reduced index by a smaller pair of obligations: properness of the coordinate centre and the explicit root-packet transform. The properness module builds; the root-packet module remains open.

Accordingly, the latest evidence is neither the old five-module failure nor a completed theorem. It is a materially improved two-module repair frontier.

## Certified sublayer that remains valid

Separate from the incomplete coordinate-geometric chain, the branch has a green restricted algebraic/causal module:

```text
PCRLean.HMCSCCD
```

At the same audited code head:

```text
HMC-SCCD run = 30769310950
HMC-SCCD job = 91553529694
result       = success

full kernel run = 30769310996
full kernel job = 91553530229
result          = success
```

`HMCSCCD` certifies simultaneous active Hasse-core/passive Morita-row-core descent on a realized finite product frame and a conditional source-causal termination backend. It does not prove the remaining boundary-SNC or root-packet theorems.

Thus:

```text
HMC_SCCD_RESTRICTED_KERNEL_EXIT       = true
MLEL_002_REPAIR_PROGRESS              = true
MLEL_002_CURRENT_FAILED_MODULE_COUNT  = 2
MLEL_002_COMPLETE_CHAIN_CERTIFIED     = false
```

## Evidence boundary

Even after the two Lean failures are closed and the dedicated axiom audit succeeds, this chamber will remain restricted. It will not by itself prove that an arbitrary canonical Frobenius core:

- admits a functorial root packet;
- is locally a coordinate ideal without an explicit frame;
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
-> proper coordinate root centre
-> boundary-compatible all-chart terminalization
```

Its immediate formal target is now sharply localized:

1. repair the `CoordinateBoundarySNC` parser/proof term;
2. supply the missing expected type in `CoordinateRootPacket`;
3. rerun the dedicated build and project-specific axiom audit.

Only after those three steps may the reduced chamber be promoted to a restricted kernel-certified theorem.

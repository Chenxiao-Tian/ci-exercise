# MLE–Lean current research frontier — 2026-08-03

This file is a baseline navigation entry.  It does not change the Certified
Graph and does not assert a proof of arbitrary-dimensional resolution in
positive characteristic.

## Load order

1. `PCRLean/FORMAL_STATUS.md`
2. `PCRLean/FORMAL_FRONTIER.md`
3. `PCRLean/ResearchProtocols/PCR_JUMP_LEAN_2_0_BASELINE.md`
4. `PCRLean/ResearchProtocols/MLEL_JUMP_REDUCED_NORMAL_CONE_ROUND_2026-08-03.md`
5. `PCRLean/ResearchProtocols/MLEL_JUMP_REDUCED_NORMAL_CONE_ROUND_2026-08-03.json`

## Current research-only frontier

The latest experimental Lean–MLE information is organized around the chain

```text
graded Frobenius normalization
-> reduced normal-cone power reflection
-> actual polynomial graph centres
-> exact quotient and finite free conormal candidates
-> faithfully flat descent of properness, finite generation,
   reduced quotient, Frobenius-normality, and conormal finiteness
-> finite etale/fpqc graph-atlas existence theorem
-> joint legality and hereditary controlled transforms.
```

The decisive local boundary is:

```text
coordinate or graph centre has Frobenius-normal I-adic filtration
iff the passive coefficient ring is reduced
```

in the stated affine models.  The decisive remaining geometric bridge is the
construction of a finite graph atlas for an arbitrary actual regular centre,
with effective overlap descent of the ideal, conormal frame, owner data,
boundary data, and controlled transforms.

## Evidence classification

```text
mathematical definitions and proof-term candidates = present
counterexample audit                            = present
exact-head clean-room build                     = pending
exact-head #print axioms audit                   = pending
promotion to official Certified Graph           = not performed
```

## Global truth

```text
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED         = false
FORMAL_GLOBAL_STATUS                       = OPEN_GAP
```

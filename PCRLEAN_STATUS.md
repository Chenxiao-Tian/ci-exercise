# PCR-Lean closed-loop experiment

Branch: `pcr-lean-closed-loop`

This branch is an isolated formal-verification experiment for the positive-characteristic resolution research program. It does not alter the formal research baseline and does not claim arbitrary-dimensional resolution.

## Kernel-checked scope

- exact odd-cusp `s`- and `y`-chart factorization identities;
- exact tame ramified-quadratic collision recurrence;
- exact Artin-Schreier two-parameter collision recurrence and arithmetic tail classification;
- well-founded finite-source generational rank and its four certified edge types.

## Required CI guarantees

- Lean 4.30.0 and mathlib v4.30.0 are pinned;
- `lake build` succeeds;
- no source-level `sorry`, `admit`, or custom `axiom` declarations;
- nanoda independently checks the compiled environment with `sorryAx` forbidden;
- `#print axioms` audits are emitted for the certified declarations.

## Not yet certified

The universal packet-entry, actual-centre algebraization, joint owner/passive legality, all-chart hereditary reentry, fully quasilinear core, immediate-defect escape, global serialization, and arbitrary-dimensional resolution statements remain outside `PCRLean/Certified` until they receive complete kernel-checked proofs.

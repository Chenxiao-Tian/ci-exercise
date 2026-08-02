# PCR-Lean closed-loop experiment

Branch: `pcr-lean-closed-loop`

This branch is an isolated formal-verification experiment for the positive-characteristic resolution research program. It does not alter the formal research baseline and does not claim arbitrary-dimensional resolution.

## Kernel-checked scope

- exact principal Frobenius-content active and sibling chart factorizations;
- exact odd-cusp `s`- and `y`-chart factorization identities;
- exact tame ramified-quadratic active and sibling chart recurrences and debt arithmetic;
- exact Artin-Schreier active and sibling chart recurrences and arithmetic tail classification;
- well-founded finite-source generational rank and its four certified edge types;
- abstract theorem that strict natural-valued rank, no certified dead ends, and terminal soundness imply finite reachability of a resolved state;
- persistent-obstruction no-go: a nonzero exactly preserved obstruction cannot vanish along a finite certified path.

## Required CI guarantees

- Lean 4.30.0 and mathlib v4.30.0 are pinned;
- `lake build` succeeds;
- no source-level `sorry`, `admit`, or custom `axiom` declarations;
- the certified index is audited by `#print axioms`;
- leanchecker independently checks the compiled environment;
- nanoda independently checks the environment with `sorryAx` forbidden.

## Posterior correction

The experimental MLE theorem claiming universal fully-quasilinear root-torsor elimination after resolving obstruction support is not certified and is invalidated as stated. The formal persistent-obstruction theorem records the missing requirement: the geometric centre word must be proved to change or annihilate the obstruction class; support reduction alone is not enough.

## Not yet certified

The universal packet-entry, actual-centre algebraization, joint owner/passive legality, all-chart hereditary reentry, fully quasilinear core, geometric birth realization, immediate-defect escape, global serialization, and arbitrary-dimensional resolution statements remain outside `PCRLean/Certified` until they receive complete kernel-checked proofs.

# MLEL-X032A / IOM-ATOMIC

## Intrinsic Order-Ideal Minimality Atomic Leaf

**Parent:** `MLEL-X032 / SFP-IOM`, D001 `G11 / FND-11`  
**Protocol:** `PCR-FRACTAL-PROOF-LEAN 1.0`  
**Class:** `EXPERIMENTAL_ATOMIC_LEAF / NO_THEOREM_PROMOTION`  
**Global status:** `OPEN_GAP`

The exact theorem slice proves over an arbitrary commutative ring and arbitrary
module that:

```text
all dual values f(x) lie in J  <->  orderIdeal(x) <= J;
orderIdeal(x) is the least such J;
orderIdeal(x)=top  <->  no proper such J exists.
```

It also proves the exact abstract boundary: if a nonzero section is annihilated
by every dual functional, then its order ideal is zero although the section is
not. Therefore zero detection requires a separate dual-separation certificate.

This file does not construct a finite dual frame, a split finite-free cokernel
presentation, a regular centre, a hereditary transform, or resolution. It is
isolated from `CertifiedIndex` pending exact clean-room evidence and explicit
promotion authorization.

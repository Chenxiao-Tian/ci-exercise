# X052 Addendum: Pointwise, Uniform, and Functorial DPE

**Parent:** `MLEL-X052 / PIF-MPD-DPE-FINAL`  
**Date:** 2026-08-05  
**Global status:** `OPEN_GAP`.

The final proof audit distinguishes three assertions.

1. **Pointwise DPE:** every valuation admits some separating projection whose selected henselian branch is defectless.
2. **Uniform DPE:** every quasi-compact valuation neighbourhood has a finite constructible cover by such projections, stable under common refinement.
3. **Functorial DPE:** the uniform family is compatible with open restriction, smooth/etale pullback, perfect-field extension, and the source/boundary labels of the finite state.

A regular local uniformization gives pointwise DPE by etale local coordinates. Conditional on the coherent centre and transform architecture, pointwise DPE gives pointwise local uniformization through defectless-projection multiplicity reduction. It does not automatically give a finite constructible family or a smooth-functorial choice.

Thus the public global theorem is conditional on the uniform/functorial form. The exact logical structure is

```text
pointwise DPE  <-> local uniformization
  (conditional on the coherent architecture),

uniform DPE    -> finite global resolution,
functorial DPE -> smooth-functorial resolution.
```

No implication from pointwise DPE to uniform or functorial DPE is claimed without proof. The current load-bearing frontier is therefore UDPE rather than merely pointwise DPE.

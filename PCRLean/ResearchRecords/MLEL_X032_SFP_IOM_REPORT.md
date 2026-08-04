# MLEL-X032 / SFP-IOM

## Split-Free Presentations and Intrinsic Order-Ideal Minimality

**Protocol:** `PCR-FRACTAL-PROOF-LEAN 1.0 / MLEL-A003-FPE-EDGE`  
**Parent:** `MLEL-D001 / FCPP-ATLAS`, `G11 / FND-11`  
**Predecessor:** `MLEL-X031 / ACI-MMR-OIH`  
**Class:** `EXPERIMENTAL_MATH_AND_LEAN / NO_THEOREM_PROMOTION`  
**Official accepted node:** `MLEL-M004 / HMC-SCCD`  
**Global status:** `OPEN_GAP`

## Exact refinement

The previous order-ideal compiler used a finite dual frame both to define the
coefficient defect and to separate the obstruction class. X032 separates these
roles.

1. The intrinsic order ideal
   `span {f(x) | f : P →ₗ[R] R}` is the least ideal absorbing all dual values.
   This minimality and the unit-obstruction no-go require no frame and no
   projectivity assumption.
2. Zero detection does require dual separation. A split finite-free
   presentation constructs a finite dual frame by projected standard vectors
   and section coordinates.
3. Conversely a finite dual frame constructs a split finite-free
   presentation.
4. Compatible split presentations give exact order-ideal base change and,
   under faithful flatness, reflect the zero, proper-nonzero, and unit regimes.
5. An explicit split presentation of a cokernel yields a frame-independent
   graph/hybrid/unit obstruction certificate.

## Counterexample boundary

For `P = Z/2Z` over `Z`, every linear map `P → Z` is zero, so the nonzero class
`1` has zero order ideal. Thus `orderIdeal x = ⊥ → x = 0` is false without a
separate dual-separation certificate.

## Exact remaining bridge

```text
finite packet map phi and section b
-> finite Fitting atlas with compatible split finite-free presentations of coker(phi)
-> [X032] intrinsic graph / proper-hybrid / unit trichotomy
-> proper regular jointly legal marked closure
-> hereditary all-chart no-reset reconstruction.
```

X032 does not construct the universal split atlas, a legal regular centre,
passive Tor safety, hereditary reentry, or global resolution. All declarations
remain outside `CertifiedIndex` until exact clean-room evidence, semantic audit,
and explicit promotion authorization are present.

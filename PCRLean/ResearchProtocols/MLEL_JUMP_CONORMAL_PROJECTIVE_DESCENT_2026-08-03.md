# MLE–Lean research supplement

## Faithfully flat descent of conormal finiteness and projectivity

**Date:** 2026-08-03  
**Status:** research-only, clean-room verification pending  
**Certified Graph changed:** no  
**Global status:** `OPEN_GAP`

The reduced graph-centre round produced explicit local free conormal modules

```text
I_h/I_h^2 ~= R^iota
```

for polynomial graph ideals.  The remaining module-theoretic descent has now
been split into precise Lean candidates.

## Candidate theorem 1: finite conormal descent

For a faithfully flat algebra `A -> B` and an ideal `I ⊂ A`,

```text
Module.Finite B (B tensor_A I.Cotangent)
  ->
Module.Finite A I.Cotangent.
```

An equivalent finite `B`-module may be supplied instead of a typeclass instance.
This uses the existing faithfully flat finiteness descent theorem in mathlib.

## Candidate theorem 2: flat conormal descent

```text
Module.Flat B (B tensor_A I.Cotangent)
  ->
Module.Flat A I.Cotangent.
```

## Candidate theorem 3: finite-presentation descent

```text
Module.FinitePresentation B (B tensor_A I.Cotangent)
  ->
Module.FinitePresentation A I.Cotangent.
```

## Candidate theorem 4: projective conormal descent

Combining the previous two candidate theorems with the standard implication
“finitely presented flat implies projective” gives

```text
Module.Projective A I.Cotangent.
```

This is the exact algebraic conclusion needed for a finite locally free
conormal sheaf after localization.

## Remaining nonformal bridge

The scheme-level graph atlas must still produce an actual equivalence

```text
B tensor_A (I/I^2)
  ~=
(I B)/(I B)^2
```

and identify the extended conormal with the explicit free graph conormal.  The
mathlib cotangent base-change API supplies this equivalence for tensor-product
base change under flatness, but the project's graph-atlas geometry and scalar
identifications still have to be constructed.

## Truth boundary

```text
CONORMAL_FINITE_DESCENT_CANDIDATE_WRITTEN      = true
CONORMAL_FLAT_DESCENT_CANDIDATE_WRITTEN        = true
CONORMAL_FINITE_PRESENTATION_CANDIDATE_WRITTEN = true
CONORMAL_PROJECTIVE_DESCENT_CANDIDATE_WRITTEN  = true

EXACT_HEAD_LEAN_BUILD_GREEN                    = false
AXIOM_AUDIT_GREEN                              = false
BASELINE_THEOREM_PROMOTION                     = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED             = false
FORMAL_GLOBAL_STATUS                           = OPEN_GAP
```

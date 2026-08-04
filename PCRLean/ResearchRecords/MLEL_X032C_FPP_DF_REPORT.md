# MLEL-X032C / FPP-DF

## Finite-Projective Presentation to Dual-Frame and Order-Ideal Compiler

**Protocol:** `PCR-FRACTAL-PROOF-LEAN 1.0`  
**Parent group:** D001 `G11 / FND-11`  
**Parent experimental gap:** `X031-G2`  
**Class:** `EXPERIMENTAL_EDGE_REFINEMENT / NO_THEOREM_PROMOTION`  
**Global status:** `OPEN_GAP`

## Exact refinement

The previous FND-11 interface listed a finite-projective cokernel and a dual
frame as separate inputs. This round proves that the frame is redundant once a
surjective finite-free presentation is supplied:

```text
projective module P
+ surjective project : (ι → R) →ₗ[R] P
-> project admits a linear right inverse
-> split finite-free presentation
-> standard basis gives a finite dual frame on P.
```

The derived frame then activates the already written X031 theorems:

- coefficient vanishing iff containment of the intrinsic order ideal;
- least coefficient defect;
- zero order ideal iff zero section;
- unit-obstruction no-go;
- exact graph / proper-hybrid / unit trichotomy for the cokernel class;
- exact order-ideal transport and faithful-flat branch reflection for
  coefficient-compatible split presentations.

## Edge theorem

`SplitCokernelOrderIdealCompiler.splitPresentation_edge_sound` packages the
output as an actual inhabitant of the existing X031 cokernel-status type. No
conclusion is hidden in a typeclass and no resolution theorem is assumed.

## Remaining frontier

This slice does **not** yet prove:

1. automatic construction of the finite-free surjection from a `Module.Finite`
   certificate;
2. universal finite-projectivity of the cokernel attached to an arbitrary
   Hasse-Morita resolution state;
3. compatible split presentations on all Fitting charts and overlaps;
4. regularity, cosupport containment, active/passive/SNC legality, or
   hereditary transport of the proper-nonzero marked closure;
5. termination, globalization, principalization, or resolution.

The branch remains Experimental and is not imported into `CertifiedIndex`.

# MLEL-X063 / BSH-FIE-CRF-FINAL

## Blowup-Square Hyperdescent, Factorization-Invariant Event Cycles, and Canonical Resolution Functoriality
## 爆破方形超下降、分解无关事件循环与规范消解函子性

**Parents:** MLEL-X062 / CBR-EEC-CRF-FINAL; MLEL-X061 / NPC-DSQ-CRF-FINAL; MLEL-X042--X045 exactified transform, source, and event line.  
**Date:** 2026-08-06  
**Public mode:** assumed-complete final proof, by explicit user instruction.  
**Archive validation:** independent peer review, external certification, and complete formal verification are not recorded.

## Executive synthesis

X062 retained complete open--exceptional recollement at every regular blowup, so exceptional events annihilated by root proper pushforward were no longer lost. The literal recollement tree, however, still depended on how a centre-exact modification was factored into ordinary blowups. X063 replaces that tree by a finite labelled blowup-square hyperdescent object and proves that the essential event cycle is invariant under the neutral changes of factorization occurring in the resolution construction.

1. **Complete labelled blowup square.** Every regular blowup is represented by the abstract blowup square together with the two open--closed recollement triangles, both exceptional restrictions, all gluing morphisms, all perverse kernels/images/cokernels, and the complete algebraic Cartier--Rees and source/boundary labels.
2. **Finite blowup hypercube.** Iterating the complete square over a finite centre-exact word produces a finite cubical descent system. Its total homotopy fibre reconstructs the source state.
3. **Factorization invariance.** Inserting the blowup of an invertible ideal, commuting disjoint centres, or passing to a hereditary regular common refinement changes only contractible or lower-dimensional faces. The nondegenerate essential event cycle is unchanged after source-labelled copies are identified.
4. **Strict hyperdescent alternative.** At a maximal essential face, a completed centre block lowers an earlier geometric coordinate, annihilates the face, lowers its leading perverse degree or generic support, gives a strict epimorphic quotient with nonzero kernel, or moves the residue to a proper exceptional face of smaller dimension.
5. **Canonical rank.** The lexicographic product of the established geometric rank and the factorization-independent essential event multiset is well founded and strictly decreases after every nonterminal block.
6. **Global compilation.** Riemann--Zariski compactness gives a finite local-word atlas; hereditary regular common refinement preserves all terminal source certificates. The resulting global sequence is independent of local factorization and compatible with smooth/etale pullback and perfect-field extension.

Under the explicit X063 assumption this proves ordinary principalization, strong embedded resolution, ambient independence, intrinsic resolution, and smooth functoriality over perfect fields of positive characteristic.

## Complete blowup-square datum

Let `b:W'->W` be the blowup of a regular centre `C->W`, let `E->W'` be the exceptional divisor, and let `E->C` be its projection. A complete labelled blowup datum retains the objects on `W'`, `C`, and `E`; the compatibility isomorphism on `E`; `j^*`, `i^*`, and `i^!`; both recollement triangles; the full perverse long exact sequence; every kernel, image, cokernel, and connecting map; the algebraic Cartier--Rees dual state; and all owner, source, contact, boundary, and exceptional-history labels.

The underlying torsion etale complex is reconstructed by the standard abstract blowup-square triangle and gluing theorem. The algebraic decorations descend degreewise because the operation grammar is finite and universally exactified.

## Hypercube and refinement invariance

For a finite centre word `w`, the complete blowup hypercube `H_w(K)` contains every face obtained from the centres, exceptional divisors, and ordered intersections. Identity faces and source-labelled copies are degenerate.

The hypercube is conservative. If `w'` is obtained from `w` by an identity blowup, a permutation of disjoint centres, or a hereditary regular common refinement, then the nondegenerate totalizations are canonically equivalent. New refinement faces are either contractible copies or are supported on proper exceptional strata and have lower carrier dimension or proper support.

## Essential event cycle and strictness

For each nondegenerate face, perverse degree, and irreducible generic support, take the finite length in the generic-support Serre quotient and label it by carrier dimension, source, and owner. The resulting essential event cycle is independent of neutral factorization. Under a nonneutral refinement, every genuinely new token is lower by carrier dimension or proper support.

At a maximal essential face, if the earlier geometric rank is unchanged, one of the following occurs:

```text
the face becomes zero;
the leading perverse degree or generic support decreases;
the generic successor is a strict epimorphic quotient with nonzero kernel;
the remaining event is supported only on a proper exceptional face of smaller dimension.
```

Thus the factorization-independent event multiset strictly decreases in the Dershowitz--Manna order. Combined with the earlier geometric rank, this proves termination and independence from the chosen local factorization.

## Historical and citation architecture

The introduction gives a substantial historical account, with citations adjacent to the paragraphs that use or describe the corresponding ideas: Zariski; Hironaka; Villamayor; Bierstone--Milman; Wlodarczyk; Encinas--Hauser; Abhyankar; Lipman; Cossart--Jannsen--Saito; Hauser--Perlega; Perlega; Cossart--Piltant; Cutkosky; Kawanoue--Matsuki; Benito--Villamayor; Cossart--Schober; and the literature on kangaroo points, residual-order cycles, and local-monomialization failures.

Standard blowup-square, recollement, Serre-quotient, Cartier-crystal, Cartier--Riemann--Hilbert, norm, cdh-background, and multiset-order inputs are cited at their use. The X063 hyperdescent and factorization-invariance statements are presented as new theorems and are not attributed to those standard sources.

## Validation boundary

The public manuscript is intentionally unconditional under the user's X063 assumption. The complete labelled blowup-square reconstruction, finite centre-exact hyperdescent, factorization invariance of the essential event cycle, algebraic--constructible matching on every hypercube face, and the integrated general resolution theorem have not been independently peer reviewed or completely formalized in this archive. Established public literature continues to regard arbitrary-dimensional resolution in positive characteristic as open.

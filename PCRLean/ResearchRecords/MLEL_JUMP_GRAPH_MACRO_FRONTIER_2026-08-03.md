# MLEL-X20260803 / Graded Frobenius Graph-Macro Frontier

**Date:** 2026-08-03  
**Protocol:** `PCR-JUMP-LEAN 2.0 / MLEL-A002-JUMP2`  
**Accepted certified parent:** `MLEL-M004 / HMC-SCCD`  
**Experimental branch:** `pcr-jump-integral-heredity-20260803`  
**Experimental dependency-index head:** `2da9394f1ce1c74e30382595ec8bc9e7b88a7e39`  
**Exact clean-room PR:** `#24`  
**Clean-room run:** `30837634276`  
**Status at archival time:** `queued`  
**Promoted to Certified Graph:** `false`  
**Global status:** `OPEN_GAP`

This record is an archival baseline entry, not a theorem promotion. It stores the full research output of the current PCR-JUMP-LEAN conversation while preserving the formal truth boundary.

## Structural corrections retained

The research line now permanently distinguishes:

- cotangent row-span ideals from tangent annihilators;
- actual ideal, properness, nonwhole-centre strictness, regular quotient, regular immersion, marked permissibility, singular-locus containment and nonidentity action;
- active containment, passive Tor/normal-flat safety and boundary SNC;
- presentation normalization from ordinary blowup;
- source-conservative cleanup from genuine birth.

Counterexamples retained in the archive include identity packets, principal Cartier identity actions, owner-union kernel collapse, nonreduced normal-cone failure, imperfect-field coefficient obstruction, and the hybrid cusp `y^p-x^(p+1)`.

## Current highest experimental local chamber

For a Noetherian regular coefficient domain `R` of characteristic `p`, a finite nonempty polynomial graph centre

```text
I_h = (Z_i - h_i) in R[Z_i]
```

and a prime-power root packet with `q=p^e` and `0 < mark <= q`, the experimental dependency graph assembles:

1. an actual proper nonzero finite-type centre;
2. exact quotient `R[Z_i]/I_h ≃ R` and regular centre ring;
3. a Frobenius-normal centre filtration;
4. active marked permissibility at every positive mark not exceeding q;
5. every standard chart and exact factorization;
6. residual ideal exactly `(E_k)^(q-mark)`;
7. terminality when `mark=q`;
8. induced-flat passive Tor safety along every centre power;
9. flat restriction of passive data to the centre;
10. for every coefficient boundary ideal J, exact intersection quotient
    `R[Z_i]/(I_h+J_P) ≃ R/J`;
11. regular intersection for every finite coefficient-boundary stratum whose quotient is regular;
12. source support and active identity count preserved by the residual transition;
13. cleanup height `q -> q-mark`, hence strict concrete `GenRank` decrease.

The integrated module is:

```text
PCRLean.Experimental.PolynomialGraphLocalResolutionMacro
```

with the unified index and audit:

```text
PCRLean.Experimental.GradedFrobeniusHeredityKernelIndex
PCRLean/Experimental/GradedFrobeniusHeredityKernelIndexAudit.lean
```

## Evidence boundary

The source contains exact definitions, proof-term candidates, counterexample audits, and `#print axioms` targets. The clean-room run had not executed at archival time. Therefore the correct evidence label is:

```text
EXPERIMENTAL-WRITTEN-CLEANROOM-PENDING
```

It is not `LEAN-KERNEL-VERIFIED`, is not imported by `CertifiedIndex`, and is not a proof of arbitrary-dimensional resolution.

## Known mathematical localization bridge

Over a perfect field, a regular finite-type scheme is smooth. A closed immersion between smooth schemes is étale-locally a coordinate subspace. Thus, after an algorithm constructs an actual regular centre, local coordinate/graph models are standard mathematics. The remaining burden is formal scheme-level atlas construction, exact descent of ideals/charts/history, and hereditary reconstruction of the resolution state.

## Updated highest-posterior architecture

```text
intrinsic finite Frobenius–Hasse packet
-> graded Frobenius normalization and ceiling marks
-> cotangent/conormal or canonical hybrid centre synthesis
-> actual regular centre or finite centre word
-> etale polynomial-graph atlas
-> local graph macro: active + induced-flat passive + regular boundary strata
   + every chart + source-conservative cleanup
-> hereditary next-packet reconstruction without reset
-> source realization for genuine births
-> projection-free immediate-defect escape
-> Noetherian/multiset/degree/debt causal termination
-> finite functorial globalization
-> principalization and resolution
```

## Exact remaining frontiers

1. universal finite intrinsic packet extraction and presentation independence;
2. universal actual-centre synthesis, including hybrid/rank-zero/nonlinear cases;
3. scheme-level étale graph atlas and exact ideal/chart gluing;
4. arbitrary passive modules, full normal flatness and genuine SNC/codimension legality;
5. hereditary next-packet reconstruction after every chart and normalization;
6. geometric source supports for genuine births, with no split or clone;
7. projection-free immediate-defect carrier;
8. finite global serialization and final principalization/resolution compilers.

```text
CURRENT_CERTIFIED_NODE                     = MLEL-M004 / HMC-SCCD
LATEST_EXPERIMENTAL_LOCAL_MACRO_WRITTEN    = true
LATEST_EXPERIMENTAL_CLEANROOM_GREEN        = false
LATEST_EXPERIMENTAL_RESULTS_PROMOTED       = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED         = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION = false
FORMAL_GLOBAL_STATUS                       = OPEN_GAP
```

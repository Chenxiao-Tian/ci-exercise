# MLEL-X033 / MAWS-TED

## Minimizer Arrangements, Wonderful Serialization, and Tor-Excess Defect

**Chinese title:** 极小中心排列、奇妙序列化与 Tor 过剩缺陷  
**Protocol:** `PCR-FRACTAL-PROOF-LEAN 1.0 / MLEL-A003-FPE-EDGE`  
**Seed architecture:** `MLEL-D001 / FCPP-ATLAS`  
**Accepted mathematical parent:** `MLEL-M004 / HMC-SCCD`  
**Experimental parents:** `MLEL-X031 / ACI-MMR-OIH`, `MLEL-X032 / FPP-CMS-FPA`  
**Primary refinement:** `G16 -> G20 -> G25 -> G26`  
**Secondary correction:** `G11 -> G18`  
**Class:** `EXPERIMENTAL_REFINEMENT / NO_THEOREM_PROMOTION`  
**Global status:** `OPEN_GAP`

## 1. Load-bearing cut

X032 proved that a cardinal-minimal marked correction family need not admit a symmetry-fixed single selector. X033 therefore attacks the next edge:

```text
finite minimizer space
-> symmetry-compatible finite word of ordinary legal blowups.
```

It also corrects the phrase "finite-projective cokernel on a finite Fitting atlas": projectivity is generally only an open locus, not an atlas covering every point of a finite module.

## 2. Intrinsic order ideal as content ideal

For a module section `x`,

```text
O_P(x) = span { f(x) | f : P ->ₗ[R] R }.
```

A finite dual frame proves

```text
O_P(x) = min { I : Ideal R | x ∈ I • P }.
```

Indeed the reconstruction formula puts `x` in `O_P(x)P`; conversely, if `x ∈ IP`, every functional value lies in `I`. Thus the order ideal is the intrinsic content ideal of the obstruction section, not a frame-dependent coefficient construction.

This gives the projected frame-free base-change theorem for every ring map `R -> S` and finite projective `P`:

```text
O_(P tensor S)(1 tensor x) = O_P(x) S.
```

Linear-equivalence invariance and the least-content theorem are written as Experimental Lean source. The tensor base-change theorem remains a Lean target.

## 3. Projectivity discriminant

The global-projectivity reading is false. For `R=k[t]`, `M=R/(t)` is zero on `D(t)` but nonfree at `(t)`.

For a finite module over a Noetherian ring, write `F_r=Fitt_r(M)` and `F_{-1}=0`, and define

```text
Delta_r(M) = F_r * Ann(F_{r-1}),
Delta_proj(M) = sum_r Delta_r(M).
```

Then the exact proposed theorem is

```text
D(Delta_r(M))
  = { p | M_p is free of rank r },
D(Delta_proj(M))
  = { p | M_p is finite projective }.
```

The proof combines the Fitting rank criterion with finite generation:
`I_p=0` iff `Ann(I)` contains an element outside `p`.

The corrected interface is

```text
finitely presented cokernel
-> projectivity discriminant
-> projective locus: intrinsic content/order ideal
-> defect locus: Schur-Fitting residual packet.
```

## 4. Schur-Fitting recursion

On a determinant chart,

```text
M = [A B; C D],   det(A) invertible,
S = D - C A^{-1} B,
b_res = b_2 - C A^{-1} b_1.
```

Invertible block row/column operations reduce the affine cokernel problem to `(S,b_res)`. If `S=0`, the residual cokernel is free. If `S != 0` and the pivot size `r>0`, the presentation shape drops from `(m,n)` to `(m-r,n-r)`. The strict decrease of `m+n` is written in Lean; the cokernel equivalence and overlap independence remain open. The `r=0` branch must enter Frobenius/radicial descent rather than claiming arithmetic progress.

## 5. Minimizer intersection arrangement

For a selected family `A`, put

```text
K_A = J + sum_{a in A} C_a.
```

Then

```text
K_(A union B) = K_A + K_B,
V(K_A) intersect V(K_B) = V(K_(A union B)).
```

Moreover active marked legality is monotone: `D_o <= K_A^(m_o)` implies `D_o <= K_(A union B)^(m_o)`. Thus all finite intersection strata remain inside the same finite grammar and remain active-owner acceptable.

The old example `(2)+(3)=(1)` still blocks replacing two minimizers by one proper centre, but now has a favourable interpretation: the two centres are disjoint, hence lie in the commuting critical-pair chamber.

## 6. Tor-excess and wonderful serialization

The first exact pair split is:

```text
same centre
or
comaximal/disjoint centres
or
proper canonical intersection.
```

For the last branch define the elementary Tor-independence condition

```text
I ∩ J = I*J
```

and the excess module `(I ∩ J)/(I*J)`. Tor independence alone is insufficient: the tangent curves `(y)` and `(y-x^2)` have zero elementary excess but nonreduced scheme-theoretic intersection `(y,x^2)`. Regularity and clean intersection remain independent gates.

The retained conditional theorem is:

```text
finite symmetry-stable arrangement
+ every nonempty intersection regular and clean
+ active legality
+ passive Tor safety/normal flatness
+ SNC boundary compatibility
+ nonidentity action
-> canonical deepest-first wonderful ordinary-centre word.
```

Using the maximal building set, blow the deepest strata first. Distinct strata in one deepest layer are disjoint; after their blowup the remaining strict transforms again form a clean arrangement. Layer depth is intrinsic, so the word is symmetry-equivariant and requires no arbitrary minimizer selector.

The decisive open dichotomy is:

```text
all intersection strata clean and jointly legal
-> wonderful serialization

or
first failed stratum
-> canonical finite Tor/Fitting/conormal defect carrier
-> strict lower support/Fitting complexity.
```

## 7. Lean and experiment evidence

New Experimental files include:

- `IntrinsicOrderIdealLinearEquiv.lean`;
- `ProjectiveOrderIdealContent.lean`;
- `MarkedClosureArrangement.lean`;
- `CriticalPairTorExcess.lean`;
- `SchurFittingComplexity.lean`;
- `X033MinimizerArrangementIndex.lean` and audit.

Draft PR: `#42`. Exact clean-room run: `30872321737`, job `91876672001`; status at archival: `queued`. A queued run is not green evidence.

The deterministic experiment suite checked 1,000 content-invariance trials, 1,500 marked-closure/intersection trials, and 500 finite-field Schur reductions, all with zero identity failures. These experiments do not prove the universal geometric edges.

## 8. Exact frontier

```text
X033-N1  PROJECTIVITY_DISCRIMINANT_SCHEME_THEOREM
X033-N2  FRAME_FREE_FINITE_PROJECTIVE_BASE_CHANGE
X033-N3  SCHUR_COKERNEL_AND_OBSTRUCTION_EQUIVALENCE
X033-N4  RESIDUAL_PACKET_PRESENTATION_INDEPENDENCE
X033-N5  DISJOINT_CENTRE_BLOWUP_COMMUTATION
X033-N6  MINIMIZER_INTERSECTION_LATTICE_SHEAFIFICATION
X033-N7  CLEAN_ARRANGEMENT_RECOGNITION
X033-N8  JOINT_LEGALITY_OF_ALL_INTERSECTION_STRATA
X033-N9  LAYERWISE_WONDERFUL_ORDINARY_BLOWUP_THEOREM
X033-N10 NONCLEAN_EXCESS_CARRIER_STRICT_DROP
X033-N11 WONDERFUL_WORD_HEREDITARY_NO_RESET
X033-N12 MACRO_RANK_DECREASE_AFTER_SERIALIZATION
```

## 9. Annals-series maximum-likelihood estimate

The updated central estimate is six papers and 564 dense Annals-equivalent pages:

```text
I   Intrinsic Frobenius-Hasse Packets,
    Projectivity Discriminants, and Content Ideals       92
II  Actual Centres, Minimizer Arrangements,
    and Wonderful Serialization                         124
III Joint Legality, All-Chart Transforms,
    and Hereditary Reentry                              118
IV  Fitting and Tor Defects, Birth, Recurrent Classes,
    and Causal Termination                              104
V   Global Descent, Functorial Centre Words,
    and Principalization                                 80
VI  Functorial Resolution in Positive Characteristic
    and Formal Reproducibility                           46
                                                        ---
                                                        564
```

This is a publication forecast conditional on the architecture, not a claim of completion or acceptance.

## 10. Truth boundary

```text
ORDER_IDEAL_CONTENT_THEOREM_WRITTEN          = true
MINIMIZER_INTERSECTION_ALGEBRA_WRITTEN       = true
TOR_EXCESS_CASE_SPLIT_WRITTEN                = true
SCHUR_SHAPE_STRICT_DESCENT_WRITTEN           = true
PROJECTIVITY_ATLAS_OVERCLAIM_CORRECTED       = true
WONDERFUL_SERIALIZATION_COMPLETE             = false
ALL_INTERSECTION_STRATA_JOINTLY_LEGAL         = false
NONCLEAN_DEFECT_STRICT_DROP                  = false
NEW_CLEANROOM_GREEN                          = false
NEW_DECLARATIONS_PROMOTED                    = false
CERTIFIED_GRAPH_CHANGED                      = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED           = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION   = false
FORMAL_GLOBAL_STATUS                         = OPEN_GAP
```

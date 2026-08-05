# X041 Semantic Alignment

## Scope rule

The X041 Lean declarations certify only elementary module saturation, finite
word invariance, finite exponent bookkeeping, quotient invariance, and rank
arithmetic.  They do not certify Berthelot--Ogus décalage, derived categories,
strict transforms, blowups, good triples, flatification, common refinements,
regular centres, hereditary reentry, termination, or resolution.

## Paper-to-Lean map

| Manuscript statement | Lean declaration | Exact certified content | Not certified |
|---|---|---|---|
| Product saturation | `PowerSaturationProduct.powerSaturation_mul` | Relative power saturation by `q*r` equals successive saturation by `q` and `r` | `eta_q eta_r`, Cartier divisors, or strict transforms |
| Word saturation | `DivisorWordSaturation.wordSaturation_eq_prod` | A finite scalar word equals saturation by its product | Total exceptional divisor of a scheme word |
| Permutation invariance | `DivisorWordSaturation.wordSaturation_eq_of_perm` | Reordering commuting scalar saturations changes no submodule | Invariance of intermediate blowup schemes or boundaries |
| Finite exponent certificate | `SaturatedSourceCapsule.ExponentCertificate.mono` | A larger exponent remains a complete saturation detector | Existence of a uniform exponent for coherent sheaves |
| Source capsule | `SaturatedSourceCapsule.Capsule.saturatedSubmodule_eq_of_perm` | Equal inherited submodules and permuted scalar words give equal saturated submodules | Actual source-word transform or derived good-triple capsule |
| Rank arithmetic | `DecalageSourceRank.rank_wellFounded` | The four-coordinate natural-number relation is well founded | Every geometric macro lowers a coordinate |

## Standard inputs not formalized here

```text
H^i(Leta_f M)=f^i(H^i(M)/H^i(M)[f]);
eta_f eta_g=eta_(f*g);
flat-base-change compatibility of eta;
Noetherian stabilization of power torsion;
one-chart strict transform is quotient by exceptional power torsion;
canonical good-triple blowup of a perfect complex;
Leta compatibility with arbitrary pullback after good-triple preparation.
```

Each needs the exact scheme, derived, owner, source, boundary, and chart
interfaces used by this project.

## Forbidden extrapolations

The X041 source does not license any claim that:

```text
one Leta layer is a passive strict transform;
full saturation is the active controlled transform;
an arbitrary source packet is perfect;
a source word is determined by its final morphism;
the total divisor capsule already equals the actual iterated transform;
good-triple blowups have regular centres in positive characteristic;
Regular-Flag Flat-Lift or all-chart no-reset is proved;
termination, globalization, or general resolution is proved.
```

## Truth boundary

```text
NEW_DECLARATIONS_PROMOTED                  = false
CERTIFIED_GRAPH_CHANGED                    = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED         = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION = false
FORMAL_GLOBAL_STATUS                       = OPEN_GAP
```

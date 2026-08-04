# MLEL-X037 / BRT-ESD — Two-Sided Lattice Correction

**Status:** candidate-graph correction inside the same round  
**Date:** 2026-08-04  
**Global status:** `OPEN_GAP`

## 1. Why quotienting exceptional torsion is not sufficient

The first X037 formulation compared the actual ambient packet `F_act` with the
flat strict target `F_str` by quotienting the exceptional-power torsion of
`F_act`.  That is necessary but not sufficient.

Two torsion-free coherent lattices can coincide away from an exceptional
Cartier divisor and still differ on the divisor.  The simplest model is

```text
O(-E) subset O
```

inside their common localization.  Both sheaves have zero exceptional torsion,
but they are not equal.  A uniform normal-line twist may explain part of this
difference, yet a finite module can exhibit nonuniform elementary divisors,
for example

```text
O directSum O
versus
O directSum O(-E).
```

Therefore the complete invariant is not a scalar nilpotence exponent and not
merely `H^0_E(F_act)`.

## 2. The common-localization packet

Let `j : U = C^+ minus E -> C^+`.  After first quotienting exceptional torsion,
embed the actual packet and the line-regraded strict target into their common
localized sheaf

```text
V = j_* j^* F.
```

Write the resulting coherent lattices as

```text
A subset V,    S subset V.
```

The canonical two-sided discrepancy packet is

```text
K = A intersection S,
L = A + S,
Q_A^- = A/K,
Q_S^- = S/K,
Q_A^+ = L/A,
Q_S^+ = L/S.
```

Noether's second isomorphism theorem gives

```text
A/(A intersection S) ~= (A+S)/S,
S/(A intersection S) ~= (A+S)/A.
```

Thus there are only two independent discrepancy modules.  They are coherent
and supported on `E`, hence killed by finite powers of `I_E` on a Noetherian
quasi-compact chart.

The exact submodule algebra is formalized in
`ExceptionalLatticePacket.lean`.

## 3. Filtered exceptional lattice debt

For either discrepancy module `Q`, retain the finite `I_E`-adic layer packet

```text
Layer_q(Q) = I_E^q Q / I_E^(q+1) Q.
```

Each layer is a coherent module on `E`.  Its projectivity, rank, content,
Fitting, Hasse, and kernel data form a finite recursive packet.  The debt is the
source-labelled multiset

```text
(number of nonzero layers,
 support dimensions,
 projective-rank profiles,
 Fitting/kernel profiles).
```

The scalar contact exponent from the tangent graph is the rank-one cyclic
shadow of this packet.

## 4. Elementary transforms, not only uniform multiplication

Multiplication by one exceptional equation moves every lattice summand by the
same amount.  It cannot align arbitrary lattices with different elementary
exponents.  The correct local operation is an **exceptional elementary
transform**:

```text
A -> ker(A -> Q_layer)
```

for a canonical projective/content or Schur-Fitting quotient layer on `E`.
In an adapted frame this multiplies selected normal directions by the
exceptional equation while leaving the complementary directions unchanged.

The affine conormal/order-ideal machinery from Papers I--II is therefore
reused on each exceptional layer.  Positive projective pivots yield graph or
hybrid elementary transforms; nonprojective loci return to Schur--Fitting and
DFK-KR recursion.  This is a genuine fractal reentry of the centre-synthesis
compiler on the exceptional divisor.

## 5. Weighted ambient realization in matrix form

The scalar weighted ideal

```text
I_C + K^N
```

is sufficient only for cyclic or uniform lattice debt.  In general the
weighted ambient flatifier must be a finite module-image or determinantal Rees
ideal whose local diagonal form has weights

```text
(a_1,...,a_r).
```

After lower-dimensional Fitting stratification and monomialization, the
weighted packet becomes toroidal and is dominated by a finite word of ordinary
regular coordinate centres.  Every preparatory subcentre must itself be
legalized recursively in smaller carrier dimension.

## 6. Corrected decisive theorem

> **Bi-Rees Commensurability and Exceptional Elementary-Transform Theorem.**
> After a carrier flatification word, the actual projective-normal packet and
> the line-regraded flat strict target determine two coherent lattices in one
> common localization.  Their intersection/sum discrepancy modules are
> exceptional-power torsion and admit a finite intrinsic Fitting/Hasse layer
> packet.  A finite sequence of source-labelled exceptional elementary
> transforms, realized by a recursively legalized ordinary ambient-centre
> word, identifies the actual lattice with an invertible twist of the flat
> target.  The complete layer multiset strictly decreases and does not recharge
> under hereditary successor reconstruction.

This theorem is stronger and more accurate than the scalar saturation statement
in the first X037 report.  It is not proved.

## 7. Revised highest-information cut

```text
X037-L1  COMMON_LOCALIZATION_AND_LINE_REGRADING
X037-L2  BIREES_COMMENSURABILITY_MAP
X037-L3  COHERENCE_AND_FINITE_E-POWER_BOUNDS
X037-L4  INTRINSIC_LAYER_FITTING_PACKET
X037-L5  EXCEPTIONAL_ELEMENTARY_TRANSFORM_ACTUALIZATION
X037-L6  MATRIX-WEIGHTED_AMBIENT_REES_REALIZATION
X037-L7  REGULAR_TOROIDAL_DOMINATION
X037-L8  LATTICE_LAYER_NO_RECHARGE
```

The new highest-information cut is

```text
X037-L2 + X037-L5 + X037-L8.
```

## 8. Truth boundary

```text
SCALAR_SATURATION_ONLY_MODEL_COMPLETE          = false
TWO_SIDED_LATTICE_PACKET_IDENTIFIED            = true
SECOND_ISOMORPHISM_LEAN_SOURCE_WRITTEN         = true
ELEMENTARY_TRANSFORM_COMPILER_IDENTIFIED       = CANDIDATE
BIREES_COMMENSURABILITY_PROVED                 = false
EXCEPTIONAL_ELEMENTARY_ACTUALIZATION_PROVED    = false
LATTICE_LAYER_NO_RECHARGE_PROVED               = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION     = false
FORMAL_GLOBAL_STATUS                           = OPEN_GAP
```

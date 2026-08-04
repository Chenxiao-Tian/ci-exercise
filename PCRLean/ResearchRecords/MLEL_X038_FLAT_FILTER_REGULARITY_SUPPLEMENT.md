# MLEL-X038 Supplement

## Flat Filter-Regularity and Simultaneous Exceptional-Torsion Elimination

**Parent:** `MLEL-X038 / PGI-ERD`  
**Class:** `STANDARD ALGEBRA ENDPOINT + CANDIDATE GEOMETRIC COMPILER`  
**Date:** 2026-08-04  
**Global status:** `OPEN_GAP`

---

# 1. Main compression

Let `C` be a regular carrier, let `u` be a local equation of one component of
the exceptional SNC divisor on `C`, and let

```text
G = gr_L(N / H^0_(u)(N)).
```

The X038 purification--grading defect is

```text
E_u(G)=H^0_(u)(G).
```

The decisive observation is elementary but load-bearing:

> If `G` is flat over `C`, then multiplication by every base
> nonzerodivisor is injective on `G`.  Since `u` is a Cartier equation,
> `E_u(G)=0`.

Thus the purification--grading defect does not require an independent
same-dimensional elimination algorithm once the **whole purified associated
graded module** has been flatified over the carrier.

The exact module endpoint is written in
`FlatExceptionalTorsionKill.lean`.

---

# 2. Proof

Let `A` be the local ring of `C`, let `G` be an `A`-flat module, and let `u` be
a nonzerodivisor in `A`.  The injection

```text
0 -> A --u--> A
```

remains injective after tensoring with `G`, so

```text
0 -> G --u--> G
```

is exact.  Repeating the argument shows that `u^n g=0` implies `g=0` for every
`n`.  Hence every submodule consisting of `u`-power torsion is zero.

No finite-rank hypothesis over `A` is used.

---

# 3. SNC monomials

Let the exceptional boundary on `C` have local equations

```text
u_1,...,u_r
```

forming part of a regular parameter system.  Every monomial

```text
u^alpha = product_i u_i^(alpha_i)
```

is a nonzerodivisor in the regular local ring.  Therefore a carrier-flat
module has no torsion killed by any exceptional monomial.  One simultaneous
flatification of the complete purified associated-graded portfolio kills all
purification--grading defects for all owners and all boundary strata.

The source-labelled exponent vector remains useful before flatification as a
diagnostic and rank coordinate, but it is not a separate terminal obstruction.

---

# 4. Corrected two-stage transform problem

The total ambient transform problem has two logically different stages.

```text
STAGE A: twisted Rees base-change / controlled-filtration comparison
  old projective-normal packet
  -> associated graded of the ambient pullback;

STAGE B: purification versus associated grading
  associated graded of the ambient pullback
  -> associated graded of the ambient strict transform.
```

X038 identifies Stage B exactly:

```text
0 -> E_u(G)
  -> gr_L(N/H^0_(u)(N))
  -> gr_L(N)/H^0_(u)(gr_L(N))
  -> 0.
```

Stage B vanishes after carrier flatification of `G`.  The genuinely
project-specific bridge is therefore Stage A: construct its all-chart map,
prove finite coherent exceptional kernel/cokernel, and show that recursively
legal regular trace centres make the comparison exact.

---

# 5. Revised flatification packet

For one raw regular carrier `C`, the flatifier should act on the finite
projective-normal/Rees packet representing the complete purified associated
graded modules

```text
G_j = gr_C(M_j / exceptional torsion)
```

for all passive owners, together with:

```text
finite low-degree comparison modules,
coherent projective tails,
twisted Rees base-change defects,
log-conormal defects,
source-Cartier and anchor-contact packets.
```

After the centre-enriched flatifier has been realized ambiently:

```text
G_j is flat over the transformed carrier
-> every exceptional equation is G_j-regular
-> every purification--grading defect is zero.
```

A generically zero Rees comparison defect, once made carrier-flat, is killed by
the reduced-base flat-kill lemma.  Therefore one flatification macro handles
both:

```text
positive-rank passive modules by producing flatness,
and
generically zero transform defects by producing actual vanishing.
```

---

# 6. Regular-flag edge theorem

Suppose

```text
D subset C subset X
```

is a flag of regular immersions and `D` is one centre in the regular word
realizing the carrier flatifier.  The recursive state on `D` must contain the
complete projective-normal/Rees portfolio of `C`.  The maximum-likelihood edge
theorem is:

> **Regular-Flag Flat-Lift Theorem.**  If `D` is jointly legal for the complete
> carrier portfolio, then on every relevant blowup chart the controlled carrier
> ideal is already saturated, the twisted Rees base-change comparison is an
> isomorphism, and the associated graded of the ambient strict transform is the
> centre-enriched strict transform of the old purified associated graded,
> including the canonical exceptional line twist.  Since the final carrier
> transform is flat, all purification--grading torsion vanishes.

This theorem is not proved.  Its local coordinate ideal statement is standard;
its complete owner-module, overlap, source, and boundary interfaces remain
open.

---

# 7. Revised critical cut

The former divisorial-elimination cut is compressed to:

```text
FR-1  ALL_CHART_TWISTED_REES_BASE_CHANGE_MAP
FR-2  FINITE_EXCEPTIONAL_KERNEL_COKERNEL_PACKET
FR-3  REGULAR_FLAG_FLAT_LIFT
FR-4  CENTRE_ENRICHED_REGULAR_REALIZATION_OF_THE_FLATIFIER
FR-5  CARTIER_STABLE_ALL_CHART_NO_RESET
FR-6  DIMENSION_STRICT_NESTED_LEGALIZATION
```

The purification--grading endpoint itself is no longer conceptually open:
once the geometric module is correctly identified and flat, its exceptional
power torsion is zero.

---

# 8. Truth boundary

```text
FLAT_MODULE_HAS_NO_EXCEPTIONAL_POWER_TORSION       = standard theorem
LEAN_MODULE_ENDPOINT_WRITTEN                       = true
PURIFICATION_GRADING_DEFECT_KILLED_BY_FLATNESS     = conditional on scheme identification
MULTI_EXCEPTIONAL_MONOMIAL_ENDPOINT_IDENTIFIED     = true

ALL_CHART_TWISTED_REES_MAP_PROVED                  = false
REGULAR_FLAG_FLAT_LIFT_PROVED                      = false
CENTRE_ENRICHED_FLATIFIER_REALIZATION_PROVED       = false
ALL_CHART_NO_RESET_PROVED                          = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION         = false
FORMAL_GLOBAL_STATUS                               = OPEN_GAP
```

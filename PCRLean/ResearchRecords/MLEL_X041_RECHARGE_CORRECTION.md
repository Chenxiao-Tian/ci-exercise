# MLEL-X041 Final Correction

## Saturated Source Capsules and the Exceptional-Recharge Defect

**Parent:** `MLEL-X041 / SCD-DSW`  
**Class:** `COUNTEREXAMPLE-BOUNDARY CORRECTION / CANDIDATE-GRAPH REWRITE`  
**Date:** 2026-08-05 UTC  
**Global status:** `OPEN_GAP`

---

# 1. Correction

The first X041 theorem stated too broadly that the actual iterated strict
transform of an arbitrary centre word is determined by the final model, the
total exceptional divisor, and a finite saturation exponent.

The total-divisor capsule canonically defines the **fully resaturated
transform**.  It agrees with the actual iterated strict transform only if later
pullbacks create no new power torsion along earlier exceptional components.
This is precisely the exceptional no-recharge condition.

Thus saturated Cartier décalage does not prove no-reset by itself.  It isolates
the exact no-recharge obstruction.

---

# 2. Algebraic mechanism

Consider composable ring maps

```text
A -> B -> C
```

with exceptional parameters `e in B` and `f in C`.  Let `Q_e(N)` denote
quotient by `e`-power torsion.  The iterated transform is

```text
Q_f(Q_e(M tensor_A B) tensor_B C).
```

The total-divisor saturated transform is

```text
Q_(e*f)(M tensor_A C).
```

The second tensor product can create new `e`-power torsion not descended from
the first-stage torsion.  The second ordinary strict-transform step removes
`f`-power torsion, but need not remove the newly created old-`e` torsion.  Total
saturation removes both.  Equality therefore requires a base-change/no-recharge
certificate.

In actual regular blowup flags, the intended Tor-safety and normal-flatness
hypotheses are designed to exclude this creation.  That exclusion is exactly
what Regular-Flag Flat-Lift and hereditary no-reset must prove.

---

# 3. Canonical recharge packet

Let `F^iter` be the actual iterated transform on the final model `Y`, and let
`I_E=O_Y(-E)` be the ideal of the total source exceptional divisor.  Define

```text
Recharge_E(F^iter)
  = H^0_E(F^iter)
  = union_n F^iter[I_E^n].
```

The factorization-independent fully saturated quotient is

```text
F^sat = F^iter / Recharge_E(F^iter).
```

A finite exponent computes this quotient on a coherent quasi-compact
Noetherian packet.  The recharge module is finite and supported on `E`.

The exact terminal comparison is now

```text
F^iter ~= F^sat
<-> Recharge_E(F^iter)=0.
```

At the module level this is the equality between an inherited submodule and its
full power saturation.  `SaturationRecharge.lean` records the exact
clean/defect coverage and divisor-word invariance.

---

# 4. Corrected décalage theorem

> **Saturated Cartier Décalage with Recharge Defect.**  Let `pi:Y->X` be a
> finite centre-enriched word and let `E_pi` be its total source-labelled
> exceptional Cartier divisor.  For a perfect finite source packet `P`, a
> finite iterated `Leta_(E_pi)` capsule computes the fully `E_pi`-saturated
> transform of `Lpi^*P`.  The capsule is independent of the ordering of the
> divisor components and, after good-triple preparation, commutes with
> arbitrary pullback.
>
> For a degree-zero owner module, there is a comparison from the actual
> iterated strict transform to the saturated capsule.  Its kernel is the finite
> exceptional-recharge module.  The comparison is an isomorphism exactly in the
> no-recharge chamber.  Stepwise Tor-safety/normal-flatness and Regular-Flag
> Flat-Lift imply this vanishing for legal centre words.

This corrected theorem is still open.  It separates a standard saturated
transform from the project-specific no-recharge theorem.

---

# 5. Consequence for the global rank

A recharge packet is not a new untyped debt.  Its finite support and exponent
are inserted before the old source/debt coordinates:

```text
carrier dimension,
recharge support dimension,
recharge/torsion height,
unresolved source count,
contact,
debt,
SCC height.
```

A legal nested step must make the recharge packet zero.  A nonzero packet is
routed to a finite exceptional Fitting/support recursion rather than silently
reset.

---

# 6. Revised critical path

```text
saturated total-divisor capsule
-> actual-to-saturated comparison
-> exceptional recharge packet

recharge = 0
  -> source-word realization
  -> Regular-Flag Flat-Lift
  -> no-reset

recharge != 0
  -> exceptional Fitting/support carrier
  -> strict recharge descent
  -> return to the comparison.
```

The highest-information cut becomes

```text
SCD-R1  ACTUAL_TO_SATURATED_COMPARISON
SCD-R2  FINITENESS_BASE_CHANGE_AND_OVERLAP_OF_RECHARGE
SCD-R3  LEGAL_REGULAR_FLAG_IMPLIES_RECHARGE_ZERO
SCD-R4  NONZERO_RECHARGE_STRICT_DESCENT
SCD-R5  SOURCE_CONSERVATIVE_NO_RESET.
```

---

# 7. Truth boundary

```text
TOTAL_DIVISOR_SATURATED_CAPSULE_IDENTIFIED       = true
ACTUAL_TRANSFORM_EQUALS_CAPSULE_UNCONDITIONALLY  = false
EXCEPTIONAL_RECHARGE_DEFECT_IDENTIFIED           = true
MODULE_RECHARGE_COVERAGE_LEAN_WRITTEN             = true

ACTUAL_TO_SATURATED_SCHEME_COMPARISON_PROVED     = false
LEGAL_FLAG_RECHARGE_VANISHING_PROVED             = false
NONZERO_RECHARGE_STRICT_DESCENT_PROVED           = false
SOURCE_WORD_REALIZATION_PROVED                   = false
ALL_CHART_NO_RESET_PROVED                        = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION       = false
FORMAL_GLOBAL_STATUS                             = OPEN_GAP
```

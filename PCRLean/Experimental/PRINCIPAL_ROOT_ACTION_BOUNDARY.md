# PRAB-001: Principal-Root Action Boundary

**Line:** PCR-JUMP-LEAN 2.0  
**Branch:** `pcr-jump-principal-root-boundary-20260803`  
**Class:** experimental no-go and compiler correction  
**Global status:** `OPEN_GAP`

## 1. Algebraic fact

For every commutative ring `R`, element `r`, and positive mark `m`, the pure
power packet

```text
((r^m), m)
```

is marked-permissible for the root ideal `(r)`. The ideal `(r)` is principal.
If `r` is a nonzero nonunit in a domain, then

```text
bottom < (r) < top.
```

These facts are formalized in `PrincipalRootActionBoundary.lean`.

## 2. Geometric no-go

A principal root ideal generated locally by a nonzerodivisor defines an
effective Cartier divisor. The blowup is characterized by the universal
property of making the inverse image of the centre an effective Cartier
divisor. Since the identity morphism already has this property, the blowup of
an effective Cartier divisor is canonically isomorphic to the original scheme.

Therefore the following implication is invalid:

```text
proper + nonbottom + regular + permissible
    -> useful nonidentity blowup centre.
```

An additional gate is required:

```text
NonidentityActionGate.
```

## 3. Compiler correction

Pure-root output must be classified as one of two distinct actions.

### Terminal/boundary enrollment

If the current marked object is already a pure power or SNC monomial supported
on the root divisor, record the divisor in the boundary/monomial ledger and
terminate that component. Do not perform an identity blowup.

### Hybrid enlargement

If an ordinary, Hasse, owner, or boundary defect remains, enlarge the root
component by the necessary non-Cartier components and test the hybrid ideal or
a finite centre word. The cusp `y^p-x^(p+1)` realizes this branch: `(y)` is a
principal root component, while `(x,y)` is the effective codimension-two hybrid
centre.

## 4. Revised action gates

A centre action must carry separate certificates:

```text
ActualCoherentIdealGate
ProperClosedCentreGate      -- ideal != top
NonwholeCentreGate          -- ideal != bottom
RegularImmersionGate
MarkedPermissibilityGate
SingularLocusGate
JointOwnerGate
PassiveTorGate
BoundarySNCGate
NonidentityActionGate       -- not an invertible Cartier blowup action
AllChartGate
OverlapGate
HereditaryReentryGate
RankDecreaseGate
```

No subset of these gates is silently inferred from regularity of the quotient.

## 5. Open Lean bridge

The scheme-level theorem still needed is:

```text
PRAB-L007

If an actual coherent ideal sheaf is invertible and defines an effective
Cartier divisor, then its ordinary blowup morphism is an isomorphism.
```

After scheme-level blowups exist in PCRLean, this theorem should become a
certified no-go imported by the action compiler.

No result in this note is promoted to the official baseline.

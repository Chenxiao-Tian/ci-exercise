# X041 Counterexample Ledger

## SCD-1 — Same morphism, different divisor payload

```text
A=k[z], F=A/(z).
```

The blowup in the Cartier ideal `(z)` and the empty identity modification have
the same underlying morphism.  The first strict transform is zero and the
second is `F`.  A divisor/source label is indispensable.

## SCD-2 — One décalage layer is not full saturation

For

```text
M=A/(u^m), m>1,
```

one Cartier-décalage layer removes only the first torsion layer and leaves the
model `A/(u^(m-1))`.  Passive strict transform requires enough layers to reach
the full power-torsion quotient.  An algorithm that identifies one `Leta`
application with strict transform is false.

## SCD-3 — Contact must not be fully saturated

The same module models contact order.  Full saturation would erase the entire
contact packet in one step and destroy the controlled-transform mark.  Active
contact consumes only the prescribed number of layers; passive sheaf transform
uses full saturation.

## SCD-4 — Non-Cartier equation

The product and base-change identities require exceptional equations that are
nonzerodivisors on the chosen complex terms.  A locally principal zero divisor
is not an effective Cartier divisor and cannot be enrolled in the SCD word.

## SCD-5 — Nonflat arbitrary base change

`Leta` commutes directly with flat base change.  Under an arbitrary nonflat
common refinement, new Tor can appear.  The candidate must first establish the
Stacks good-triple condition or carry an explicit derived defect packet.

## SCD-6 — Nonperfect source packet

The canonical good-triple blowup is formulated for a perfect object.  A finite
module over the affine normal cone need not be perfect as an `O_C`-module.  The
proper Rees-Serre packet on the regular projective normal bundle, together with
finite low-degree complexes, is retained to produce a perfect source packet.

## SCD-7 — Total divisor without multiplicity

The reduced union of exceptional components does not remember how many
Cartier layers must be removed.  The capsule must retain the saturation exponent
or multiplicity/debt ledger.

## SCD-8 — Word product without source lineage

Two words may have the same product equation after normalization while carrying
different owners or birth events.  Saturation invariance does not license
source-ledger compression before the owner/source comparison theorem.

## SCD-9 — `Leta` is not exact

The décalage functor does not preserve arbitrary distinguished triangles.
Kernel/cokernel arguments must be made through perfect representatives,
cohomology formulas, or explicit good-triple comparisons rather than formal
triangulated exactness.

## SCD-10 — Missing componentwise exponent

A local torsion exponent need not be uniform on a non-quasi-compact space.  The
finite capsule requires coherent cohomology on a quasi-compact Noetherian model
and one exponent dominating all finitely many cohomology degrees and affine
charts.

## SCD-11 — Flat module boundary

If the final source transform is finitely presented and flat over the regular
source base, exceptional Cartier equations act injectively and no new
power-torsion is created under flat pullback.  This is the exact chamber in
which additional common-refinement blowups are harmless.

## SCD-12 — Order-independent torsion does not imply order-independent geometry

The module saturation quotient is invariant under permutation of divisor
equations.  The ambient blowup centres and intermediate boundaries can still
change.  The SCD theorem compares final source transforms; it does not assert
that arbitrary centre words are isomorphic step by step.

## Posterior effect

The ledger rejects bare morphism semantics, one-layer passive transforms,
full-saturation contact transforms, arbitrary nonflat base change, nonperfect
good-triple inputs, multiplicity-free divisor capsules, and misuse of
triangulated exactness.  It supports a finite source divisor word, a uniform
saturation exponent, perfect good-triple preparation, and a separate
active/passive stopping rule.  It does not prove the scheme-level SCD theorem.

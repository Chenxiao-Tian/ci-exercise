# MLEL-X051 Supplement

## Rank-One Reduction and Henselian-Rational Reprojection

**Parent:** MLEL-X051 / FPR-R1C-HRR-FINAL  
**Date:** 2026-08-05  
**Status:** external valuation theorems plus a conditional finite-state descent theorem.

---

## 1. Rank-one reduction

Novacoski--Spivakovsky prove that local uniformization for valuations centred on a category of local domains follows from the rank-one case; their argument also treats embedded and related variants. A finite-rank valuation is decomposed into rank-one valuations through its chain of convex subgroups.

For the present programme, each stage carries the complete finite coloured state. Owner/passive/boundary legality and source ancestry are not discarded when passing to residue fields or coarsenings. The higher-rank reduction is therefore conditional only on the rank-one theorem being stable for this complete state.

---

## 2. Primitive rank-one independent defect

Kuhlmann proves that an independent Artin--Schreier defect extension has idempotent distance `delta=p delta`, and idempotent distances are convex-subgroup cuts. A rank-one ordered group has no nonzero proper convex subgroup. For an immediate defect extension the distance is a proper cut below zero, hence

```text
delta=0^-.
```

The best-generator ideal is the maximal ideal of the valuation ring. It is idempotent and non-finitely-generated because the value group has no least positive element.

This removes isolated-subgroup height from the rank-one rank. Coarsening is a classification operation, not geometric progress.

---

## 3. Valuation-algebraic transcendence degree one

Let `(F/K,v)` have transcendence degree one, with `vF/vK` torsion and `Fv/Kv` algebraic. Kuhlmann's henselian-rationality theorem gives a finite extension `L/K` for which

```text
(F.L)^h = L(x)^h
```

for a suitable `x`.

A finite event-visible state inside this henselization is defined on one finite etale neighbourhood of a local model of `L(x)`, since henselizations are filtered colimits of etale neighbourhoods and the state is finitely presented.

---

## 4. Finite-state descent theorem

Assume:

```text
lower-dimensional full-portfolio preparation on a model of L;
X042--X044 ordinary-centre preparation and hereditary transform;
X047 Cech--Rees descent for the finite extension L/K;
X049 Norm--Rees and balanced-gap descent.
```

Then the finite state on the henselian-rational chamber admits an upper ordinary regular jointly legal centre word. Nonzero finite-flat discrepancies are coherent colours on the base and are eliminated in finitely many X044 blocks; zero discrepancy descends the word. Divisorially unbalanced data use the downstairs norm shadow, while balanced gaps become flat and vanish. Hence the word descends to the original model.

---

## 5. Remaining uniformity theorem

The per-valuation henselian-rationality theorem does not by itself choose the codimension-one subfield, finite extension, common model, and source-labelled finite state uniformly on a quasi-compact neighbourhood. Nor does it prove the no-equal-or-higher-birth clause.

The remaining theorem URHR must produce a finite portfolio satisfying all of these requirements. Once URHR is available, the rank-one class-V token disappears by the preceding finite-state descent theorem and higher-rank valuations follow by composition.

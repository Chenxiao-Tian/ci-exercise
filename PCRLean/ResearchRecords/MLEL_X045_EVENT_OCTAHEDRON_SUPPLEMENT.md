# MLEL-X045 Supplement

## Octahedral Event Composition and Primitive Source Filtrations

**Parent:** MLEL-X045 / AEF-NUB-CRX-FINAL  
**Date:** 2026-08-05  
**Status:** standard triangulated-category theorem plus finite source-filtered construction.

---

## 1. Two-step composition

For completed centre-exact words

```text
Sigma_0 --u--> Sigma_1 --v--> Sigma_2
```

let

```text
h_u : Her_u P_0 -> P_1,
h_v : Her_v P_1 -> P_2.
```

The composite comparison is

```text
h_(vu)=h_v o Her_v(h_u).
```

The octahedral axiom gives a distinguished triangle

```text
Her_v Cone(h_u)
  -> Cone(h_(vu))
  -> Cone(h_v)
  -> Her_v Cone(h_u)[1].
```

Thus cumulative novelty is an extension of transported earlier novelty by the new one-step novelty.

---

## 2. Finite chains

For a chain `w_1,...,w_n`, induction gives a finite filtration of the cumulative event object in the extension closure

```text
< Her_(w_n...w_2) Ev_(w_1),
  Her_(w_n...w_3) Ev_(w_2),
  ...,
  Ev_(w_n) >.
```

This filtration is independent of inserting identity/gauge steps, because their event cone is zero. It is compatible with open restriction and every base change for which hereditary transport is exact.

---

## 3. Source semilattice

Let `S_0` be the finite set of immutable root source IDs. Let `L(S_0)` be its finite nonempty join semilattice. A source-filtered complex has subcomplexes `F_A P`, `A in L(S_0)`, with

```text
A<=B  =>  F_A P subset F_B P.
```

All portfolio constructors are source monotone. In particular, tensor and multiplication use joins, while kernels, images, cokernels, Hasse operators, Fitting layers, and strict-transform comparisons inherit the source label.

For a source-filtered event complex `E`, define

```text
Prim_A(E)=F_A E / sum_(B<A)F_B E.
```

This quotient is canonical even when several incomparable lower supports occur. Its coherent cohomology and Fitting layers define the primitive event packet.

---

## 4. No chart cloning

Suppose `E` is represented on an etale chart family. Descent identifies the chart restrictions as one global source-filtered complex. A decomposition of one cohomology sheaf into irreducible components is not a decomposition of source identity. The canonical identity is

```text
(A, colour, cohomological degree, Fitting layer).
```

Repeated chart manifestations are aliases. If the event genuinely decomposes into smaller source supports, those pieces occur in lower primitive quotients.

---

## 5. Counterexample boundary

Without the source filtration, the same event may be renamed after every chart change. Without the octahedral triangle, a cumulative event may be mistaken for a fresh independent source. Without the primitive quotient, a source join may be split into arbitrarily many component labels. These are semantic errors, not geometric births.

The construction does not prove that a fixed primitive token cannot recur. That requires the coherent profile and recurrent-class descent theorem of the main X045 report.

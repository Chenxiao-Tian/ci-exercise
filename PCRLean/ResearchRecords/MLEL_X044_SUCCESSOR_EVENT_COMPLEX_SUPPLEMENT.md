# MLEL-X044 Supplement

## Coherent Successor Event Complexes and Choice-Free Source Births

**Parent:** `MLEL-X044 / COP-PCH-UCS-FINAL`  
**Date:** 2026-08-05  
**Status:** finite birth realization closed; ancestral termination open.

## 1. Comparison object

Represent the complete finite obstruction portfolio of a state `Sigma` by a bounded coherent presentation complex `P(Sigma)`, graded by obstruction colour and source label. For a completed centre-exact word `w`, hereditary transport and intrinsic recomputation give a natural map

```text
h_w : Her_w P(Sigma) -> P(Sigma_w).
```

The map includes the Frobenius--Hasse core, conormal and normal-jet packets, exactified mixed-Rees data, support--thickness pieces, boundary, and source lineage.

## 2. Event cone

Define

```text
Ev_w(Sigma)=Cone(h_w).
```

Its cohomology is coherent and supported in the successor nonterminal locus. Kernel-type degrees record inherited data that disappear; cokernel-type degrees record genuinely new successor obstruction data.

## 3. Choice-free birth labels

A new source is labelled by

```text
(colour, event degree, Fitting layer)
```

of one coherent cohomology sheaf. Irreducible components are not chosen. The finite Fitting filtration is intrinsic and symmetry invariant. Hence each transition has finitely many birth packets and cannot manufacture sources by chart choice or component selection.

## 4. Naturality

Because the underlying state and hereditary maps commute with open restriction and smooth/etale base change, so do the event cone and its Fitting filtration. The cone vanishes precisely when the successor portfolio is entirely inherited.

## 5. Remaining issue

Coherence and finite branching do not imply well-foundedness. The same ancestor may contribute to infinitely many future event cones, especially in kangaroo, radicial, or immediate-defect chambers. The next theorem must attach a strict ancestral conductor or recurrent-class height to every nonzero event cone.

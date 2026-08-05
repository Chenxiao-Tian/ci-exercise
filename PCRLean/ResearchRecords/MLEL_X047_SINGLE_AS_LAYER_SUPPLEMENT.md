# MLEL-X047 Supplement

## The Independent Artin--Schreier One-Layer Descent Dichotomy

**Parent:** MLEL-X047 / FCD-RAE-ZSD-FINAL  
**Date:** 2026-08-05  
**Status:** zero-shadow branch closed after finite-flat preparation; compatible upper monomialization remains open.

---

## 1. Setup

Let `(L|K,v)` be an independent immediate Artin--Schreier defect extension of degree `p`. Fix:

```text
one quasi-compact valuation neighbourhood;
one finite common model X;
one finite event-visible shadow hull;
one finite normalization/alteration model Y->X;
immutable projection, layer and source ancestry.
```

The complete finite packet contains coefficient and Hasse data, the differential-ramification portfolio, traces, conductors, source labels, and every X044/X043 legality certificate.

Flatten the proper generically finite map by a good-open-admissible blowup so that its strict transform is finite locally free. Realize the flattening modification by the X044 regular-centre block when working in the candidate resolution category.

---

## 2. The two shadows

There are two logically different obstruction objects.

### 2.1 Ramification shadow

This is the X046 typed differential-ramification complex. It measures whether the independent wild layer is visible through differentials, traces, conductors, coefficient cuts, and the chosen finite projection.

### 2.2 Cech-Rees shadow

This lives on the finite-flat relation. It measures whether the prepared upper coloured packet and upper centre word descend as modules, ideals, Rees algebras, labelled filtrations, and stagewise blowups.

The second shadow cannot be omitted. A ramified upper ideal may be invariant under the Artin--Schreier automorphism and still fail fpqc descent on a non-torsor model.

---

## 3. One-layer dichotomy

### Theorem

Let `w_Y` be a finite ordinary upper word for the complete event-visible packet. After a finite constructible refinement, precisely one of the following occurs.

```text
EFFECTIVE-SHADOW BRANCH:
  the direct sum of the typed ramification shadow and the Cech-Rees shadow
  is nonzero;
  its first nonzero cohomology/Fitting layer is a coherent proper colour on X;

ZERO-SHADOW BRANCH:
  both shadows vanish;
  the upper packet and every stage of w_Y descend uniquely to X;
  the descended word is ordinary, regular and jointly legal;
  the terminal upper certificate descends.
```

### Proof

All shadow terms are coherent after finite-flat preparation, and the finite cover permits finite pushforward to the base. If the combined shadow is nonzero, take its first nonzero intrinsic layer. If it is zero, the ramification comparisons are quasi-isomorphisms and the complete Cech datum is effective. Apply fpqc descent to the modules, ideals and Rees algebras, then descend the blowup word stagewise.

---

## 4. What has actually been closed

The following sentence is now a theorem in the stated chamber:

```text
zero complete shadow -> exact descent.
```

The adjective “complete” includes the Cech comparison, cocycle, all Rees structure maps, all labelled filtrations, and terminal certificates.

The following sentence remains open:

```text
for every independent Artin--Schreier packet there exists a finite upper word
whose complete shadow is either zero or has a strictly lowerable first layer.
```

This is Cech-Compatible Wild Monomialization.

---

## 5. Minimal next experiment/theorem

Work with one affine finite-flat model `A->B` and one upper monomial ideal `J subset B` arising from a prepared independent Artin--Schreier layer. Form explicitly:

```text
p_0^*J, p_1^*J subset B tensor_A B;
the equalizer defect;
the multiplication and Rees defects;
the cocycle defect on B tensor_A B tensor_A B.
```

Prove one of:

1. the defect is nonzero and its Fitting ideal strictly changes after the descended X044 block; or
2. the defect vanishes and the ideal descends.

No new global invariant or manuscript architecture should be introduced before this one-layer calculation is settled.

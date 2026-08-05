# MLEL-X053 Supplement

## Terminal Basins and Riemann--Zariski Compactness

**Parent:** MLEL-X053 / RZC-FLA-HCR-FINAL  
**Date:** 2026-08-05  
**Status:** standard valuation-space topology; no resolution theorem is used.

---

## 1. Riemann--Zariski space

For an integral finite-type model `X` with function field `K`, let `RZ(K/X)` be the valuation rings of `K` having a centre on `X`. It is the projective limit, in locally ringed spaces, of the proper birational models of `X` and is quasi-compact. For reduced `X`, take the finite disjoint union over irreducible components.

Every proper model `Y->X` has a continuous centre map

```text
c_Y:RZ(K/X)->Y.
```

The maps are compatible with domination.

---

## 2. Basin attached to a finite word

Let `w:Y->X` be a finite centre-exact blowup word and let `T subset Y` be an open terminal locus. Define

```text
Omega(w,T)=c_Y^(-1)(T).
```

This set is open. It depends only on the final centre-exact word and terminal certificate, not on a chart representation.

If a valuation has centre in `T`, then the same word uniformizes it. Thus a local uniformization word automatically uniformizes an open valuation neighbourhood; no additional continuity theorem for the chosen projection is required.

---

## 3. Finite extraction

If every valuation admits some finite word and terminal open, the basins form an open cover. Quasi-compactness produces a finite subcover. The chosen finite family need not be unique or functorial.

The extraction uses only:

```text
pointwise finite words;
openness of terminality on the final model;
properness and uniqueness of valuation centres;
quasi-compactness of the valuation space.
```

It does not use constructibility of the set of defectless projections and does not choose one projection on an entire basin.

---

## 4. Detection of unresolved points

Let `Z->X` be a proper model. For every point `z in Z` and every irreducible component through `z`, there is a valuation ring of the component function field dominating the corresponding local domain. Its centre on `Z` is `z`.

Consequently, if a proper model factors through a finite local-word atlas and preserves all terminal certificates, then the absence of unresolved valuation centres implies the absence of unresolved scheme points.

---

## 5. Boundary of compactness

Compactness produces only a finite family of models. It neither makes their fibre product regular nor supplies a permissible sequence dominating them. The blowup of `A^2` in `(x^2,y^3)` is already a singular common modification. Regular hereditary common refinement is a separate geometric theorem.

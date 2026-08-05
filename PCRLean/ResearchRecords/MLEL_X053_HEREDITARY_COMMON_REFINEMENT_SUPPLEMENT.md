# MLEL-X053 Supplement

## Hereditary Regular Common Refinement of a Finite Local-Word Atlas

**Parent:** MLEL-X053 / RZC-FLA-HCR-FINAL  
**Date:** 2026-08-05  
**Status:** conditional geometric theorem using the X040--X044 full-portfolio architecture.

---

## 1. Input

Let `(W,E,X)` be an embedded pair with `W` regular and `E` SNC. Let

```text
w_i:(W_i,E_i,X_i)->(W,E,X), i=1,...,m,
```

be finite words of ordinary blowups in regular jointly legal centres. Retain the complete source-word data:

```text
ordered centre ideals;
centre-exact composite modification ideal;
strict-transform and passive owner modules;
source and exceptional lineage;
terminal open T_i;
regularity, normal-flatness, and SNC certificates on T_i.
```

Assume every word is an isomorphism over the initially terminal open and at the generic points of every component of `X`.

---

## 2. Common modification

The finite words are admissible blowups after centre-exact compression. Their product ideal defines a common admissible blowup, or equivalently a common proper modification is dominated by an admissible blowup. The support of the common modification ideal contains no generic point of a component of `X`; hence its carrier dimension is strictly smaller than `dim X`.

The common blowup may be singular. It is only a target to be dominated.

---

## 3. Full terminal portfolio

Enrol in one finite coloured portfolio:

```text
the common modification ideal;
all source composite ideals;
all active marked ideals and normal Hasse jets;
all exactified passive and Tor-Valabrega systems;
all ordered boundary ideals;
all terminal strict-transform owners;
all terminal conormal and SNC certificates;
all source, contact, and exceptional-history filtrations.
```

The bad support lies in the support of the common modification ideal or in a proper failure locus of one terminal certificate. Every such support has smaller carrier dimension.

---

## 4. Regular realization

Apply the lower-dimensional full-portfolio theorem to principalize the common modification ideal and prepare all terminal data simultaneously. The resulting word is a finite sequence of ordinary blowups in regular jointly legal centres. The universal property of blowup gives a factorization through every source word.

On a source terminal open, each later centre is either disjoint from the terminal strict transform or regular and transverse to it and the total boundary. The blowup of a regular ambient scheme in a regular centre is regular; the strict transform of a regular subscheme meeting the centre cleanly is regular; the ordered boundary remains SNC. X042 exactification and X043 regular-flag comparison transport the passive and normal data on every chart.

Thus every source terminal certificate survives on the common refinement.

---

## 5. Product-ideal technical lemma

On a reduced component, let `I_1,...,I_m` be finite-type ideals which contain a nonzerodivisor at the generic point. If their product is invertible after pullback, then every `I_i` is invertible as a fractional ideal: in the total quotient ring,

```text
I_i * ((product_(j not=i) I_j) * (product_j I_j)^(-1)) = O.
```

This gives the factorization through each source blowup. Components on which one source ideal is the unit ideal are harmless. The centre-exact source word is retained because an isomorphic final modification alone does not determine strict transform.

---

## 6. Terminality after refinement

Let `z` be a point of the final strict transform and choose a valuation dominating a component local domain at `z`. If the finite basins cover the valuation space, the valuation belongs to one source basin. The image of `z` on that source model is its valuation centre and lies in the source terminal open. Hereditary preservation therefore makes `z` regular and SNC. Hence the final pair is globally terminal.

---

## 7. Truth boundary

The standard inputs are finite common admissible domination and elementary preservation of regular/SNC pairs under clean regular blowups. The load-bearing input is the lower-dimensional full-portfolio principalization/actual-centre theorem. Without it, a common modification may be singular and the patching argument does not close.

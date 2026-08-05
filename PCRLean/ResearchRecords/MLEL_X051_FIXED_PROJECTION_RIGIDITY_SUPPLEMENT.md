# MLEL-X051 Supplement

## Fixed-Projection Rigidity and the Reprojection Firewall

**Parent:** MLEL-X051 / FPR-R1C-HRR-FINAL  
**Date:** 2026-08-05  
**Status:** exact valued-field no-go theorem.

---

## 1. Model changes versus valued-field changes

Let `L/K` be a fixed finite extension and `v` a fixed valuation of `L`. A blowup of a model of `K`, normalization in `L`, completion of a local model, or replacement by a dominating finite common model changes the centre of `v` but does not change the valued-field extension.

Consequently the following data are fixed:

```text
vK, vL, Kv, Lv;
e(L/K,v), f(L/K,v), d(L/K,v);
Artin-Schreier right-hand-side class;
best-generator ideal H_(L/K) in O_v;
distance/improvement cut;
dependent/independent type;
approximation pro-isomorphism class.
```

## 2. Rigidity theorem

> **Theorem.** No finite sequence of ordinary blowups of finite models of `K` can change any datum in the above list.

The proof is immediate from the definitions: birational modification does not change `K`, `L`, or `v`, while all listed objects are invariants of these valued fields.

## 3. Consequences

For a fixed independent Artin--Schreier defect layer, ordinary blowups alone cannot:

```text
create a best generator;
make the best-generator ideal finitely generated;
remove the defect;
change independent defect into dependent defect;
strictly improve the intrinsic cut.
```

A valid class-V escape must therefore do at least one of:

```text
change the projection/finite field tower;
lower a separate geometric or valuation coordinate;
produce a new coherent contraction visible to the finite state.
```

## 4. Counterexample to a model-stage distance rank

Take any cofinal sequence of Artin--Schreier representatives for a nonattained cut. Replacing the sequence by a cofinal tail leaves the cut and the pro-object unchanged. A stage index, number of used representatives, or position in a key-polynomial list is not intrinsic. The same remains true after arbitrary blowups of the chosen models.

## 5. Programme effect

X050's Uniform Nonattained-Cut Escape is corrected to Uniform Rank-One Henselian Reprojection. Reprojection is not optional terminology: the fixed-projection theorem proves that it is logically necessary in the primitive class-V chamber unless an earlier independent coordinate drops.

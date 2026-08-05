# MLEL-X047 Supplement

## Cech-Rees Descent for Ideals, Blowups, and Joint Legality

**Parent:** MLEL-X047 / FCD-RAE-ZSD-FINAL  
**Date:** 2026-08-05  
**Status:** standard fpqc descent theorem written in the exact form required by the resolution programme.

---

## 1. Ramified invariance is not descent

Let `A=k[t]`, `B=k[s]`, `t=s^2`, with characteristic not two. The ideal `(s)` is stable under the involution of `B`, but no ideal of `A` pulls back to `(s)`. Thus invariance under visible automorphisms is weaker than descent on `Spec(B tensor_A B)`.

The same warning applies to wild degree-p covers. A centre must carry a complete descent datum, not merely an orbit label.

---

## 2. Complete descent object

Let `f:Y->X` be finite faithfully flat. A complete centre object consists of

```text
J subset O_Y;
R(J)=directSum_(n>=0) J^n T^n;
a bounded owner/passive complex P;
source and boundary filtrations;
all structure maps and legality certificates.
```

A descent datum is an isomorphism between the two pullbacks to `Y x_X Y`, compatible with the embedding `J->O_Y`, the algebra structure on `R(J)`, every map in `P`, and every filtration, and satisfying the cocycle on the triple fibre product.

---

## 3. Ideal and Rees descent

### Theorem

A complete descent datum on the centre object is effective. There are unique downstairs data

```text
J_X subset O_X,
R_X=directSum J_X^n T^n,
P_X,
source/boundary filtrations
```

whose pullback is the upper object.

### Proof

Fpqc descent is effective and fully faithful for quasi-coherent modules. Descend the modules and every structure map. The descended map `J_X->O_X` is injective because its pullback is injective and the cover is faithfully flat. Multiplication, unit, grading and the identities defining powers of `J` descend by full faithfulness; hence the descended graded algebra is the Rees algebra of `J_X`.

---

## 4. Blowup descent

Since relative Proj commutes with flat base change,

```text
Bl_(J_X)(X) x_X Y = Bl_J(Y).
```

This isomorphism is centre exact. It does not replace `J_X` by an arbitrary ideal defining an isomorphic modification.

For a finite word, apply the argument stage by stage. The pulled-back cover remains finite faithfully flat after every downstairs blowup.

---

## 5. Descent of regularity and legality

The following properties descend when encoded by the complete finite certificates used in X042--X043:

- quasi-regular immersion of the centre: fpqc local on the base;
- regularity of a finite-presentation centre: reflected by faithfully flat base change;
- active marked containments: reflected by faithful flatness;
- flatness and universal exactness of the passive portfolio: fpqc local;
- normal Hasse-jet containments: finite module containments reflected by faithful flatness;
- logarithmic incidence: descend the ordered Cartier ideals, conormal maps and regular-intersection certificates;
- source and history labels: descend as filtrations and labelled maps.

Thus a zero-shadow upper jointly legal word descends to a jointly legal word.

---

## 6. Terminal descent

If the upper terminal packet is regular with SNC boundary and its full terminal certificate has descent datum, the downstairs packet has the same property. Regularity descends through the finite faithfully flat cover. The SNC statement is expressed by regularity of all ordered intersections and invertibility of the component ideals, which are fpqc local in this finite-presentation setting.

---

## 7. Boundary of the theorem

The theorem does not construct a compatible upper word. It says that once the full Cech-Rees shadow vanishes, descent is automatic and unique. The hard remaining theorem is to produce an upper word for which the Cech discrepancy is either zero or has an effective first nonzero layer that strictly decreases under a downstairs actual-centre block.

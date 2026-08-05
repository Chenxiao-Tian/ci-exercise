# MLEL-X049 Supplement

## Exactified Flatification of a Ramification-Balanced Descent Gap

**Parent:** MLEL-X049 / FNI-BGE-NRW-FINAL  
**Date:** 2026-08-05  
**Status:** conditional scheme-level closure using Raynaud--Gruson flatification, X042 exactification, and X044 regular-centre realization.

---

## 1. The two-sided gap

Let `f:Y->X` be finite locally free and let `J subset O_Y` be coherent. Define

```text
I_- = Ann_X(f_*O_Y/J),
I_+ = image((f_*O_Y)^vee tensor J -> O_X),
Q_- = J/I_-O_Y,
Q_+ = I_+O_Y/J.
```

The exact sequences

```text
0 -> I_-O_Y -> J -> Q_- -> 0,
0 -> J -> I_+O_Y -> Q_+ -> 0
```

measure failure of descent from below and from above. Both quotients are needed. A one-sided conductor or trace ideal does not determine descent.

---

## 2. Codimension-one balance

Assume `X` is normal. At a codimension-one generic point, write the ramification indices as `e_j` and the exponents of the invertible part of `J` as `d_j`. The residue vanishes exactly when `d_j=e_j a` for one integer `a`.

If the residue vanishes at every codimension-one generic point, then `Q_-` and `Q_+` vanish in codimension one. Their supports have codimension at least two.

This implication uses the normality of the base and the fact that the local descent interval over a DVR is exact.

---

## 3. Why strict transform of the quotient alone is unsafe

Blowing up a Cartier divisor can be the identity morphism while the strict transform of a module supported on the centre is zero. Therefore one may not flatten or saturate `Q_-` and `Q_+` in isolation and then identify the result with the new descent gap.

The following objects are retained simultaneously:

```text
I_-O_Y, J, I_+O_Y;
Q_-, Q_+;
the two injections and two quotient maps;
all Tor_1 base-change kernels;
all images and cokernels;
the evaluation map defining I_+;
Rees powers and multiplication maps;
source, owner, boundary and wild-layer labels.
```

This is the exactified descent-interval portfolio.

---

## 4. Simultaneous flatification

Apply Raynaud--Gruson flatification to the finite direct sum of the quotient and comparison modules, relative to the good open on which the diagram already descends. The output is a good-open-admissible blowup whose strict transforms of the defect modules are flat.

X042 universal exactification requires every source, target, kernel, image and cokernel in the defining diagram to be enrolled. Once these modules are flat, the transformed two-sided sequences are universally exact under every later centre-exact pullback.

The flatification centre may be singular. Its centre-exact modification ideal therefore enters the X044 full portfolio; strict lower-dimensional preparation realizes it by ordinary blowups in regular jointly legal centres.

---

## 5. Flat-kill and descent

Let `X'` be reduced and suppose every component meets the good open. A finite flat module on `X'` has support which is a union of irreducible components. Since the transformed `Q_-'` and `Q_+'` vanish on the good open, they vanish everywhere.

Universal exactness now gives

```text
J' = I_-' O_(Y') = I_+' O_(Y').
```

Thus the transformed upper ideal descends uniquely.

---

## 6. Strictness and rank

A nonzero balanced gap has a finite profile

```text
(dim Supp(Q_- directSum Q_+),
 Fitting profile,
 presentation shape,
 remaining flatification-word height).
```

The simultaneous preparation lowers support/Fitting/presentation data or advances a finite centre word. At the completed block the gap vanishes. The profile is inserted before the coherent source-event coordinates, so no later chart event can reset it.

---

## 7. Boundary

The theorem is not available when a nonzero ramification residue survives at a codimension-one generic point. The basic model `t=s^e`, `J=(s)` remains a permanent firewall. It also depends on the conditional X044 actual-centre theorem for the flatification modification. General positive-characteristic resolution is not proved.

# MLEL-X055 / FEU-RLT-CRF-FINAL

## Frobenius-Envelope Uniformization, Root-Lattice Terminalization, and Canonical Resolution Functoriality
## Frobenius 包络一致化、根格终端化与规范消解函子性

**Parent:** MLEL-X054 / FRU-DPP-CRF-FINAL  
**Date:** 2026-08-05  
**Public interpretation:** assumed-complete final-proof reconstruction  
**External validation:** independent peer review and complete formal certification not yet recorded in this archive.

---

## 0. Executive verdict

X054 closed the valuation frontier through degree-p radicial-root uniformization followed by Frobenius transfer. X055 strengthens the most vulnerable part of that argument: dependence on a chosen degree-p tower and the treatment of terminal unit coefficients.

The X055 replacement is simultaneous.

1. A finite purely inseparable extension is treated as one **Frobenius envelope**, not as an ordered tower of degree-p roots.
2. Its intrinsic state is defined from the logarithmic cotangent complex, finite normal Hasse coefficient modules, differential-rank profile, projectivized contact multiset, active Frobenius exponents, Fitting profile, and aged source history.
3. Different root presentations and different degree-p towers admit a common Frobenius frame and define the same saturated state.
4. On every nonterminal blowup chart, one fixed lexicographic-multiset rank strictly decreases.
5. At a terminal state, a unit coefficient with zero differential is a pth power because the base is smooth over a perfect field. It can therefore be absorbed into the root variable. A unit with nonzero differential gives regularity.
6. The remaining terminal equations define a saturated root lattice. Their normalization is toroidal, and a regular subdivision is realized by ordinary blowups in regular boundary strata.
7. This proves uniformization of an arbitrary finite purely inseparable envelope at once, independent of tower order.
8. Temkin's inseparable local uniformization then gives a regular centre on a full Frobenius-root field. Frobenius transfer of etale parameters produces a defectless separating projection.
9. Riemann-Zariski compactness, hereditary regular common refinement, and the canonical projection groupoid yield ordinary embedded resolution, principalization, ambient independence, intrinsic resolution, and smooth functoriality.

The public X055 article is written unconditionally under the user's assumption that this reconstructed proof is the correct final proof.

---

## 1. Smooth p-constants

Let `R` be regular and essentially of finite type over a perfect field `k` of characteristic `p`.

> **Smooth p-constant lemma.**
> `ker(d:R -> Omega^1_(R/k)) = R^p`.

Etale locally `R` is a localization of a polynomial ring. The assertion is immediate there and is preserved by localization and etale base change.

This closes the terminal unit issue. If a terminal unit `u` has `du=0`, then `u=v^p` and is absorbed into the root variable. If `du` has a unit coefficient, the logarithmic Jacobian criterion gives regularity.

---

## 2. The simultaneous Frobenius envelope

Let `K'/K` be finite purely inseparable. On a regular local model `A`, choose any finite radicial presentation and let `B` be the normalization in `K'`.

The intrinsic state is

```text
R(B/A) =
  (dimension of the differential-Hasse support,
   logarithmic differential corank,
   projective contact multiset,
   active p-exponent multiset,
   ordered Fitting profile,
   aged exceptional history).
```

The state is attached to the normalized finite morphism, not to the chosen equations. Cotangent/Fitting data are intrinsic. Hasse-Morita descent identifies the coefficient systems after passage to a common Frobenius frame. Any two root towers have a common refinement obtained by adjoining all root generators.

---

## 3. Strict chart descent

For a blowup chart with exceptional parameter `x`, an active relation

```text
z_i^(p^e_i) = a_i
```

is transformed by

```text
q_i = floor(ord_x(a_i^tot)/p^e_i),
z_i = x^(q_i) z_i',
a_i' = x^(-p^e_i q_i) a_i^tot,
```

followed by complete p-cleaning.

Every nonterminal chart strictly decreases one of:

```text
support dimension;
differential corank;
projective contact height;
active Frobenius exponent;
Fitting profile;
aged history multiset.
```

Universal exactification makes kernel/image/cokernel formation commute with the centre-exact pullback, so the alternatives agree on overlaps and for all owners simultaneously.

---

## 4. Terminal root lattice

After unit absorption, terminal equations are

```text
z_j^(p^e_j) = x_1^(b_j1) ... x_s^(b_js).
```

With boundary character lattice `M`, define

```text
M' = M + sum_j Z p^(-e_j) b_j  subset M tensor Q.
```

The normalization is the toroidal embedding for the saturated lattice `M'`. The labelled toroidal-centre theorem gives a regular subdivision realized by ordinary blowups in regular strata of a smooth ambient toroidal pair. The normalized strict transform is regular and the ordered boundary is SNC.

---

## 5. Arbitrary finite radicial envelopes

The support-singular branch is lower dimensional. On regular support the actual-centre theorem supplies a regular jointly legal centre for the full differential/contact/Fitting/history portfolio. The envelope rank strictly decreases. Therefore every branch reaches a terminal root-lattice state.

This yields:

> **Simultaneous radicial-envelope uniformization.**
> If a valuation has a regular centre on a model of `K`, then its unique extension to any finite purely inseparable `K'/K` has a regular centre after finitely many ordinary blowups in regular centres, jointly legal for every prescribed finite portfolio. The result is independent of the chosen radicial tower.

---

## 6. Defectless projections and final assembly

Temkin supplies a finite purely inseparable extension `L/F` with a regular centre. Choose `e` with `L subset F^(1/p^e)` and apply the simultaneous envelope theorem to `F^(1/p^e)/L`.

At the resulting regular centre choose etale parameters `u_i` and put `t_i=u_i^(p^e)`. The p-power isomorphism `F^(1/p^e) -> F` transports the finite etale henselian branch to a finite separable defectless branch of `F/k(t)`.

Pointwise local words are finite. Their terminal basins are open in the Riemann-Zariski space. Quasi-compactness yields a finite atlas. Hereditary regular common refinement compiles the atlas into one ordinary global sequence. The canonical projection groupoid removes the noncanonical choice of a finite subcover and gives smooth functoriality.

---

## 7. Dependency closure

The simultaneous induction uses

```text
(ambient dimension,
 carrier dimension,
 differential-Hasse support dimension,
 differential corank,
 projective contact multiset,
 p-exponent multiset,
 coherent recurrence multiset).
```

Every same-dimensional radicial step lowers an inner coordinate. Every support-singular, flatification, overlap, or common-refinement call is on a proper closed carrier. The terminal lattice step uses only the already established toroidal centre theorem. Hence no dimension-d theorem invokes general dimension-d resolution.

---

## 8. Final public theorem

Over a perfect field of characteristic `p>0`, every reduced finite-type scheme admits resolution by a finite sequence of ordinary blowups in closed regular centres. Embedded resolution preserves an ordered SNC boundary, is an isomorphism over the resolved open, and is compatible with open restrictions, smooth/etale morphisms, and perfect-field extensions. Principalization and ambient-independent intrinsic resolution follow.

---

## 9. Validation boundary

The X055 paper is the best current final-proof reconstruction under the user's assumption that X055 is mathematically correct. The archive does not contain independent peer review, external certification, or complete formal verification of the general theorem.

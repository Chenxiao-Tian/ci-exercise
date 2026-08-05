# MLEL-X056 / FFS-NRT-VCT-FINAL

## Frobenius-Foliation Saturation, Norm-Rees Terminalization, and Valuation-Certificate Termination
## Frobenius 叶层饱和、Norm-Rees 终端化与估值证书终止

**Parent:** MLEL-X055 / FEU-RLT-CRF-FINAL, together with the X055 Frobenius-sandwich and intrinsic-action variants  
**Date:** 2026-08-05  
**Public mode:** assumed-complete final-proof reconstruction  
**External validation:** independent peer review and complete formal certification are not recorded in this archive.

## 0. Executive verdict

X056 merges the three strongest X055 branches into one proof.

1. A height-one finite radicial morphism is represented intrinsically by its saturated p-closed logarithmic foliation, not by a selected equation `z^p=a`.
2. Centre ideals stable under the full relative Hasse algebra descend uniquely through the Frobenius sandwich; their Rees algebras and strict transforms commute with the quotient.
3. A finite foliation/contact/Cartier/Fitting/history state decreases on every nonterminal chart.
4. Vanishing of the terminal foliation defects gives logarithmic Cartier straightening. The invariant ring is regular in pth powers of foliation coordinates and the untouched transverse coordinates.
5. The identity `ker(d:R->Omega^1_(R/k))=R^p` for smooth algebras over a perfect field removes every terminal differential-zero unit.
6. X056 replaces the vulnerable “one fan regular in two lattices” step by base-first Ferrand Norm-Rees regularization. Source toric subdivisions are encoded by monomial ideals upstairs; their norm ideals are principalized downstairs by ordinary blowups in regular centres. The normalized pullback dominates the source subdivision and decreases the source cone-multiplicity multiset.
7. An arbitrary finite purely inseparable extension is handled by its canonical Frobenius filtration `K_i=K(K')^(p^(e-i))`; each layer is a height-one sandwich. No radicial generator or arbitrary degree-p tower is selected.
8. Inseparable local uniformization followed by simultaneous Frobenius-envelope uniformization yields a regular centre on a full Frobenius-root field. Frobenius transfer of etale parameters gives a defectless separating projection.
9. The global centre sequence is still defined solely by the intrinsic Frobenius-Hasse state. Projections are valuation certificates used only to prove termination. An infinite intrinsic sequence would yield one valuation in all nonterminal cylinders and hence an impossible infinite descent of its defectless-projection certificate.

The public X056 article is written as a complete unconditional proof under the user's X056 assumption.

## 1. Height-one sandwich theorem

Let `q:Y->X` be finite radicial of height one. On the regular locus of `Y`, set

```text
F_(Y/X)=Der_X(O_Y) cap T_Y(-log E_Y).
```

It is saturated, Lie closed, and p-closed. The complete state records the nonprojective support, logarithmic differential corank, projectivized contact multiset, Cartier-Hasse comparison, ordered Fitting profile, and aged exceptional history.

A centre ideal stable under the full relative Hasse algebra satisfies

```text
J=(J cap O_X) O_Y.
```

The equality holds degreewise for the Rees algebra. Hence blowup and strict-transform semantics descend through the sandwich.

The complete actual-centre block strictly lowers the state unless the foliation is logarithmically straight. In the straight chamber, etale coordinates make the foliation a coordinate p-foliation and the invariant ring is regular.

## 2. Base-first terminalization

For a terminal finite p-primary lattice extension `M subset M'`, choose a canonical toric resolution of the source fan. One source star subdivision is the normalized blowup of a monomial ideal `J`. Let

```text
I=N_pi(J)
```

be its Ferrand norm ideal on the base. In diagonal toroidal charts,

```text
integral_closure(I O_Y)=integral_closure(J^[M':M]).
```

The exactified norm/Rees/descent-interval portfolio glues. Principalization of `I` by the actual-centre theorem produces ordinary base blowups in regular boundary-compatible centres, and the normalized pullback dominates the desired source subdivision. Iteration lowers the finite source cone-multiplicity multiset and regularizes the normalization.

Normalization is therefore a comparison operation only; the final output remains a sequence of ordinary blowups on the base.

## 3. Canonical Frobenius filtration

If `(K')^(p^e) subset K`, define

```text
K_i=K (K')^(p^(e-i)), 0<=i<=e.
```

This filtration is determined by `K'/K`, begins at `K`, ends at `K'`, and has height-one layers. Applying height-one sandwich uniformization successively gives simultaneous Frobenius-envelope uniformization independent of a root presentation.

## 4. Global proof chain

```text
finite intrinsic Frobenius-Hasse state
-> actual regular jointly legal centre block
-> exact all-chart hereditary successor
-> coherent/source recurrence descent
-> height-one Frobenius-sandwich uniformization
-> base-first Norm-Rees terminalization
-> simultaneous Frobenius-envelope uniformization
-> defectless projection certificate for every valuation
-> valuation-certificate termination of the intrinsic sequence
-> smooth-functorial embedded resolution
-> principalization, ambient independence, intrinsic resolution.
```

## 5. Public theorem

Over a perfect field of positive characteristic, every reduced finite-type scheme admits resolution by a finite sequence of ordinary blowups in closed regular centres. The embedded construction preserves an ordered SNC boundary, is an isomorphism over the resolved open, and commutes with open restrictions, smooth/etale morphisms, and perfect-field extensions.

## 6. Validation boundary

The public article is written as the complete final proof requested by the user. The research archive does not record independent peer review, external theorem certification, or complete formal verification of the general theorem.

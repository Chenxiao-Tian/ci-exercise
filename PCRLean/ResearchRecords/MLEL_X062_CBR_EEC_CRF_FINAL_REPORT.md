# MLEL-X062 / CBR-EEC-CRF-FINAL

## Conservative Blowup Recollement, Exceptional Event Cycles, and Canonical Resolution Functoriality
## 保守爆破重黏合、例外事件循环与规范消解函子性

**Parents:** X061 Noetherian perverse cycles and dynamic Serre quotients; X060/X059 Postnikov and Cartier-dual lines; X057 transform-complete Cartier crystals; X042-X045 exactified transform, actual-centre, and event lines.  
**Date:** 2026-08-05  
**Public mode:** assumed-complete final proof, by explicit user instruction.  
**Archive validation:** independent peer review and complete formal verification are not recorded.

---

## 0. Executive verdict

X061 removed the finite-monodromy and finite-derived-envelope hypotheses by using the finite length of the current generic support quotients. It still transported the residual state to the initial model by proper direct image. Proper direct image is not conservative: a nonzero exceptional object may have zero derived pushforward. X062 removes this final categorical assumption.

For every regular blowup the proof retains the full open-exceptional recollement:

```text
open restriction;
closed *-restriction;
closed !-restriction;
both gluing morphisms;
all perverse kernels, images, cokernels, and connecting maps;
algebraic Cartier-Rees dual data.
```

Iterating over a finite centre-exact word gives a finite source-labelled recollement tree. Every nonzero event appears at some node. If its root proper transport vanishes, a maximal nonzero node is supported on an exceptional carrier of strictly smaller dimension.

At each node X061's dynamic generic-support cycle is used. Tokens are ordered by carrier dimension, perverse degree, proper closed support inclusion, and current generic length. A completed actual-centre block either lowers the earlier geometric rank, lowers the node cycle, or moves the event to a closed child of smaller dimension. The resulting recursive multiset rank is well founded.

Under the X062 assumption this closes termination without assuming conservativity of proper direct image. The remaining proof chain is the established actual-centre, Cartier-Spencer, Kummer/Norm-Rees, Riemann-Zariski, hereditary common-refinement, and canonical descent architecture.

---

## 1. The nonconservativity firewall

Let `pi:W~ -> W` be the blowup of a regular codimension-two centre and `i:E -> W~` its exceptional divisor. Since `E` is a projective-line bundle,

```text
R pi_* i_* O_E(-1) = 0,
```

although `i_* O_E(-1)` is nonzero. Thus root direct image cannot be the sole event detector. Orlov's blowup formula exhibits the same exceptional components in the coherent derived category, but X062 uses only open-closed recollement as the load-bearing mechanism.

---

## 2. One-step complete probe

For `j:U=W~\E -> W~` and `i:E -> W~`, retain the standard triangles

```text
j_! j^* K -> K -> i_* i^* K ->,
i_* i^! K -> K -> Rj_* j^* K ->.
```

Define

```text
B_pi(K) = (j^*K, i^*K, i^!K, alpha_K, beta_K).
```

This probe is conservative on objects and morphisms. It is compatible with the perverse Postnikov tower and smooth/etale base change.

---

## 3. Iterated source-labelled recollement tree

A finite centre-exact word produces a finite rooted tree. A closed child lies on the new exceptional divisor or one of its ordered intersections with inherited boundary. Its carrier dimension is smaller than the parent dimension. Immutable source joins identify strict-transform, chart, and common-refinement copies.

For an event `E`, the node system is

```text
Rec(E) = {(S_tau, K_tau, source_tau)}.
```

The system is conservative by induction on the word.

---

## 4. Recursive exceptional cycle

At a node `tau`, let `Q_(tau,Z)` be the generic perverse Serre quotient at an irreducible support `Z`. The event cycle is

```text
Theta(E) = multiset of
  (dim S_tau, perverse degree q, generic support Z, source/owner labels)
weighted by length in Q_(tau,Z).
```

The order is lexicographic in carrier dimension, perverse degree, and strict support inclusion. Unrelated source-labelled carriers are incomparable. The order and its finite multiset extension are well founded.

---

## 5. Algebraic realization

Cartier-Riemann-Hilbert duality identifies the leading constructible quotient on every node with a nonnilpotent coherent Cartier-Rees quotient. Its Fitting support is combined with normal Hasse jets, exactified Tor-Valabrega maps, Cartier-Spencer and Kummer defects, boundary, source, and owner data.

For an exceptional node, the lower-dimensional full-portfolio theorem prepares the support, and regular-flag ambient realization lifts its centre to the ambient model. Thus the constructible event consumed by the rank is exactly the algebraic quotient acted on by an ordinary ambient blowup.

---

## 6. Strict recursive alternative

If no earlier geometric coordinate falls, then at every maximal node:

```text
node vanishes;
leading perverse degree/support falls;
generic successor is a strict epimorphic quotient with nonzero kernel;
or the remaining event moves to an exceptional child of smaller dimension.
```

All new tokens are strictly smaller than a removed token. Hence

```text
R_62(Sigma) = (rho_geom(Sigma), Theta(Sigma))
```

strictly decreases at every nonterminal completed block.

---

## 7. Final proof chain

```text
finite intrinsic Frobenius-Hasse state
-> actual regular jointly legal centres
-> exactified hereditary transform
-> Cartier-Spencer radicial descent
-> Kummer saturation and Norm-Rees terminalization
-> dynamic generic-support descent at every recollement node
-> conservative exceptional event-cycle termination
-> Riemann-Zariski finite local-word atlas
-> hereditary regular common refinement
-> canonical projection-groupoid descent
-> principalization and smooth-functorial resolution.
```

---

## 8. Validation boundary

The public X062 article is intentionally unconditional under the user's assumption. The complete recursive blowup-recollement theorem, exceptional-node algebraic matching, and the use of the resulting rank for arbitrary-dimensional positive-characteristic resolution have not been independently peer reviewed or completely formalized in this archive. Established public literature continues to treat the general problem as open.

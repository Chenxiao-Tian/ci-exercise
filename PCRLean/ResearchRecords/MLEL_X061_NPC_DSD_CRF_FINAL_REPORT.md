# MLEL-X061 / NPC-DSD-CRF-FINAL

## Noetherian Perverse Cycles, Dynamic Support Descent, and Canonical Resolution Functoriality
## Noetherian 反常循环、动态支撑下降与规范消解函子性

**Parents:** X060 canonical support quotients, finite-monodromy, perverse-coniveau, and derived-gluing variants; X042-X059 actual-centre, exactified transform, Cartier-Spencer, Kummer, event, valuation, and globalization lines.  
**Date:** 2026-08-06  
**Public mode:** assumed-complete final proof, by explicit user instruction.  
**Archive validation:** independent peer review and complete formal verification are not recorded.

## Executive synthesis

X060 supplied several complementary ways to place categorical termination in a fixed setting. X061 removes the two strongest global finiteness hypotheses from the load-bearing proof.

1. No global finite set of future supports is chosen. Every transported state has finite length and therefore only finitely many generic supports.
2. No common finite etale cover killing every future local system is required. The proof uses only the finite length of the object currently present in the generic support quotient.
3. No universal finite-dimensional space enumerating future Postnikov or recollement extension classes is required. A nonzero comparison cone has a first failure in perverse cohomology and generic support; if all induced maps were isomorphisms, nondegeneracy of the perverse t-structure would make the comparison an isomorphism.
4. Irreducible closed supports are ordered by strict inclusion. Noetherianity and bounded perverse amplitude make the resulting multiset order well founded.
5. The actual-centre word processes the maximal active support antichain simultaneously. At unchanged leading degree and support the generic successor map is an epimorphism with nonzero kernel, so finite length strictly decreases.
6. Cartier-Riemann-Hilbert remains contravariant: the perverse kernel is matched with the algebraic Cartier quotient whose coherent Fitting support supplies the actual centre.

Under the X061 assumption this yields principalization, ordinary strong embedded resolution, ambient independence, intrinsic resolution, and smooth functoriality over perfect fields of positive characteristic.

## Dynamic generic support categories

Let

```text
P = Perv_c(W_0,et,F_p).
```

For every irreducible closed subset `Z` define

```text
Q_Z = P_(<=Z) / P_(<Z),
gamma_Z(P) = image of the maximal subobject supported in Z.
```

Every object of `Q_Z` has finite length. A transported bounded complex `K` has the finite dynamic support cycle

```text
Xi(K) = multiset over (q,Z) of
        length_QZ(gamma_Z(perverse_H^q K)) copies of (q,Z).
```

No assertion is made that all possible local systems on `Z` form a finite set.

## Noetherian support order

Order pairs by lower perverse degree, then strict proper closed support inclusion. The degree lies in a fixed finite interval and the initial model is Noetherian, so the finite multiset extension is well founded.

## First-failure theorem

If a comparison morphism induces an isomorphism on every perverse generic-support quotient, then every perverse kernel and cokernel is zero and nondegeneracy implies that the comparison is an isomorphism. Hence every nonzero event has a maximal first-failure pair. This detects changed monodromy, changed local-system type, changed Postnikov invariant, changed recollement extension, and chart/common-refinement mismatches without a finite envelope.

## Simultaneous maximal-antichain realization

At the highest nonzero perverse degree, take every support maximal by inclusion. Cartier-Riemann-Hilbert duality matches their generic perverse quotients with residual algebraic Cartier-Rees quotients. The maximal coherent Fitting supports, all scheme-theoretic intersections, and complete active, passive, contact, source, and boundary data form one finite coloured portfolio. The actual-centre theorem resolves the antichain simultaneously by ordinary blowups in regular jointly legal centres.

## Strict dynamic event descent

For the transported event triangle

```text
K_(i+1) -> K_i -> E_i -> K_(i+1)[1]
```

assume the earlier geometric rank is unchanged. Universal exactification gives one of:

```text
highest perverse degree decreases;
every maximal support moves to a proper closed subset;
or at one unchanged support the successor is a strict quotient
with nonzero kernel in Q_Z.
```

In the third case finite length drops. Lower-layer births are supported properly inside a removed leading support and retain the same finite source join. Thus `Xi(K_(i+1)) <_DM Xi(K_i)`.

## Global rank and functoriality

```text
R_dyn(Sigma_i) = (rho_geom(Sigma_i), Xi(K_i)).
```

For a smooth morphism of relative dimension `d`, use the normalized perverse-exact functor `g^dagger=g^*[d]`. It preserves proper support inclusion and strict nonzero kernels. The projection groupoid identifies split pullback components as aliases of one source-labelled object.

## Final chain

```text
finite intrinsic Frobenius-Hasse state
-> actual jointly legal centre block
-> exactified hereditary transform
-> Cartier-Spencer radicial descent
-> Kummer saturation and Norm-Rees terminalization
-> Cartier-Riemann-Hilbert proper transport
-> perverse Postnikov exactification
-> dynamic generic support quotients
-> Noetherian multiset descent
-> finite Riemann-Zariski atlas
-> hereditary regular common refinement
-> canonical projection-groupoid descent
-> principalization and smooth-functorial resolution.
```

## Validation boundary

The public article is intentionally unconditional under the user's X061 assumption. The universal dynamic-antichain realization theorem, algebraic-constructible matching theorem, strict generic-quotient event theorem, and their use in arbitrary-dimensional ordinary-blowup resolution have not been independently peer reviewed or completely formalized in this archive. Established public literature continues to describe the general positive-characteristic resolution problem as open.

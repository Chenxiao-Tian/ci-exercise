# X062 Supplement

## Minimal Cartier Carriers and Fitting-Exact Generic Descent

### 1. Why an arbitrary representative is insufficient

A Cartier crystal is a Cartier module modulo nilpotent submodules and quotients. Two representatives can be nil-isomorphic while having different presentation matrices and different Fitting ideals. Therefore `Fitt_r(M)` is not a canonical centre prescription until a canonical representative is chosen.

### 2. Minimalization

For a coherent Cartier crystal `C`, let `C_min` be its unique minimal representative. It has no nilpotent submodule or quotient. A nil-isomorphism between minimal representatives is an isomorphism. Localization preserves minimality.

Define

```text
f_r(C)=Fitt_r(C_min).
```

The Fitting tower is intrinsic and commutes with smooth/etale base change.

### 3. Exact direction of Cartier--Riemann--Hilbert

A short exact sequence on the perverse side

```text
0 -> L -> P -> P' -> 0
```

corresponds contravariantly to

```text
0 -> M' -> M -> Q -> 0
```

on the Cartier side. The event kernel `L` is therefore the solution of the quotient `Q`. X062 always forms the centre from `Q_min`, never from a directionally incorrect submodule.

### 4. Relative Fitting preparation

The centre portfolio includes all Fitting ideals, presentations, exact sequences, Rees powers, and legality data. Flattening is carried out relative to the initial generic support. Once the strict transform is flat and zero on the dense good open, it has no component dominating that support.

### 5. Minimality and flat-kill

Vanishing in the crystal category means only nilpotence for an arbitrary representative. For a minimal representative it means actual vanishing. Hence flat-kill removes the quotient scheme-theoretically, not merely up to nilpotence.

### 6. Support causality

The remaining event supports lie in proper Fitting strata, their intersections, or exceptional strict transforms. Their images on the initial model are proper closed subsets of the support eliminated at the leading layer. This is the exact replacement condition required by the dynamic multiset order.

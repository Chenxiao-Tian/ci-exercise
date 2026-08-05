# MLEL-X046 Supplement

## Uniformizing Alteration Portfolios and Exactified Downstairs Shadows

**Parent:** MLEL-X046 / PDS-AST-IDE-FINAL  
**Date:** 2026-08-05  
**Status:** finite comparison architecture; independent-defect descent open.

---

## 1. Uniformizing alteration charts

Let `V` be a quasi-compact valuation neighbourhood carrying a class-V token and let `P` be the complete finite event-visible packet. For each valuation choose a certified chart of one of the following types:

```text
defectless finite projection;
Abhyankar or quasi-monomial local uniformization;
local uniformization after a finite extension;
local uniformization after a purely inseparable alteration.
```

The chart is required to monomialize every function and finite module used by `P`, not merely to make the ambient local ring regular. The conditions are open in the constructible valuation topology once the finite functions and centres are fixed. Quasi-compactness gives a finite subcover.

---

## 2. Common models and prime towers

For the finite chart family choose common proper models of the original function field and common normal models of the finitely many extension fields. Replace each extension by a typed prime-layer tower. Source, projection and valuation ancestry are fixed before taking common refinements.

The resulting portfolio is finite:

```text
f_a : Y_a -> X_a,
prime tower T_a,
monomial coloured packet P_a^mon,
valuation neighbourhood V_a,
source/projection ancestry.
```

---

## 3. Exactified layer comparisons

For every prime layer retain the complete comparison diagram rather than only its support:

```text
source and target complexes;
kernels, images and cokernels;
trace, norm or Frobenius-contraction maps;
relative Kahler differential complexes;
ramification and conductor modules;
coefficient and Hasse shadow modules;
all multiplication-image sequences.
```

Simultaneous flatification of this exactified portfolio makes the defining short exact sequences universally exact. Hence layer-shadow formation commutes with all later centre-exact pullbacks.

---

## 4. Shadow composition

For a tower `K_0 subset ... subset K_m`, let `s_i` be the comparison morphism of layer `i`. The total comparison is the composite of the transported `s_i`. Repeated use of the octahedral axiom gives a finite filtration of its cone with graded factors equal to the transported layer cones.

Thus a total alteration shadow is zero if and only if every typed layer comparison is exact after the required descent certificates. A hidden independent layer cannot be cancelled by an unrelated defectless or radicial layer.

---

## 5. Downstairs coherent shadow

After proper pushforward to the finite base model, take the bounded derived image of the exactified total comparison. Its coherent cohomology and intrinsic Fitting layers form

```text
AltSh(f,P).
```

The support is the failure locus for descent of the monomialized alteration packet through the complete typed comparison. The source label is the join of the alteration and packet sources, never a new root.

A nonzero proper layer is enrolled in the X044 coloured portfolio. Its complete active, passive, logarithmic and source data are prepared before the same closed subscheme is blown up ambiently.

---

## 6. Generic zero and flat-kill

On a locus where the relevant layer is defectless, etale, radicially descended, or already monomial with exact trace/Frobenius comparison, the alteration shadow is zero. If the exactified shadow is made flat over a reduced carrier and the good locus meets every irreducible component, reduced-base flat-kill makes the shadow zero globally on that carrier.

This does not prove that an independent defect shadow is generically zero. The independent layer may remain nonzero at the valuation centre and is precisely the IDE branch.

---

## 7. Descent-effectivity boundary

The following implication remains open:

```text
stable nonterminal independent-defect packet
+ monomial uniformizing alteration
+ complete stable alteration shadow
=> nonzero effective coherent shadow on the original model
   or exact descent of the monomial packet.
```

The failure of this implication is the only place where the finite uniformizing alteration portfolio may remain merely diagnostic rather than yield an actual centre on the original model.

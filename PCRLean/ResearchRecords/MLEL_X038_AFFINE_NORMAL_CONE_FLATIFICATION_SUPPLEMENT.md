# MLEL-X038 Supplement

## Affine Normal-Cone Flatification and Noetherian Mixed-Rees Compression

**Parent:** `MLEL-X038 / TVC-FKL`  
**Status:** `STANDARD-MATHEMATICAL-COMPRESSION / EXACT AMBIENT TRANSPORT OPEN`  
**Date:** 2026-08-04

---

# 1. Executive correction

The X035-X038 line repeatedly treated passive normal flatness as an
infinite-degree problem requiring a finite low window plus a projective
Rees-Serre tail.  That projective detour is unnecessary.

For a Noetherian carrier `C`, the complete associated graded module is a single
finite module over the affine normal-cone algebra.  The general flatification
by blowup theorem applies directly to that coherent module on the affine normal
cone.  Because the blowup is performed on the degree-zero base `C`, strict
transform preserves the grading.  Flatness of the total direct sum is exactly
flatness of every homogeneous piece.

The same observation applies to the two-ideal mixed-Rees module that packages
the Tor-Valabrega common-core defects.  No numerical cutoff or projective tail
is needed for the existence of a flatifier.  The remaining nonstandard work is
not finite generation; it is the exact ambient trace realization and the
all-chart identification of the transformed finite modules with the desired
normal and contact packets.

---

# 2. One-ideal affine normal-cone module

Let `A` be Noetherian, let `I subset A` be finitely generated, and let `M` be a
finite `A`-module.  Put

```text
G_A(I) = gr_I(A) = directSum_(a>=0) I^a/I^(a+1),
G_M(I) = gr_I(M) = directSum_(a>=0) I^a M/I^(a+1)M.
```

## Proposition 2.1 — finite generation

`G_A(I)` is a finite-type Noetherian algebra over `A/I`, and `G_M(I)` is a
finite graded module over `G_A(I)`.

### Proof

Choose generators `f_1,...,f_r` of `I`.  Their initial forms generate
`G_A(I)` as an `A/I`-algebra, so it is a quotient of

```text
(A/I)[T_1,...,T_r].
```

It is therefore finite type and Noetherian.  If `m_1,...,m_s` generate `M` over
`A`, their degree-zero classes generate `G_M(I)` over `G_A(I)`: every class in
`I^aM/I^(a+1)M` is a sum of degree-`a` initial forms times the classes of the
`m_j`.  Hence `G_M(I)` is finite.  QED.

Geometrically, for a regular immersion `C -> X`, the relative affine scheme

```text
N_C(X) = Spec_C gr_(I_C)(O_X)
```

is the normal cone, and in the regular case the normal bundle.  The complete
passive associated-graded module is one coherent sheaf on this affine
finite-type `C`-scheme.

---

# 3. Flatness of the total graded module

As an `A/I`-module,

```text
G_M(I) = directSum_a G_M(I)_a.
```

Therefore

```text
G_M(I) is flat over A/I
iff
all homogeneous pieces G_M(I)_a are flat over A/I.
```

The forward implication holds because every homogeneous piece is an
`A/I`-linear direct summand of the graded direct sum.  The reverse implication
holds because arbitrary direct sums of flat modules are flat.

Thus the normal-flatness gate is exactly ordinary flatness of one coherent
module on the affine normal cone.  The X036 Lean theorem

```text
FiniteGradedFlatnessCompiler.directSumFlat_iff_pieceFlat
```

already formalizes the abstract direct-sum equivalence.  Its geometric
instantiation remains open.

---

# 4. Direct application of flatification by blowup

Let `U subset C` be a quasi-compact open on which the associated-graded
portfolio is flat.  Let

```text
Y = Spec_C G_A(I)
```

and let `F` be the coherent sheaf corresponding to the finite
`G_A(I)`-module obtained by taking the direct sum of all passive owners.

The morphism `Y -> C` is affine and of finite presentation; `Y` is
quasi-compact; `F` is finite type and, over a Noetherian base, finitely
presented.  The general flatification theorem therefore gives a
`U`-admissible blowup

```text
C^flat -> C
```

such that the strict transform `F^flat` is finitely presented and flat over
`C^flat`.

No properness and no passage to `Proj` is required.  A projective-normal sheaf,
Hilbert polynomial, Serre vanishing bound, or finite tail is not needed for
this existence statement.

---

# 5. Strict transform preserves grading

The flatifying blowup is performed on the base `C`.  On an affine chart its
exceptional parameter has degree zero in `G_A(I)`.  Pullback of a graded module
along a degree-zero ring map is graded, and the submodule of exceptional power
torsion is graded: if

```text
x = sum_d x_d
```

has finite homogeneous support and one exceptional power kills `x`, then it
kills every `x_d` separately.  Hence the strict-transform quotient decomposes
as the direct sum of the strict transforms of its homogeneous pieces.

Consequently, flatness of the total strict transform implies flatness of every
transformed homogeneous piece.

This statement concerns the strict transform of the old affine normal-cone
module.  Identifying it with the associated graded module of the ambient
strict transform is exactly the Tor-Valabrega common-core problem and is not
being assumed here.

---

# 6. Finite passive portfolios

For finitely many passive owners `M_1,...,M_s`, take

```text
F_pass = directSum_j gr_I(M_j).
```

It is finite over `gr_I(A)` because the sum is finite.  One admissible blowup
flatifies the entire portfolio simultaneously.  This replaces separate owner
flatifiers and removes any need to select a preferred passive owner.

The same finite direct sum may include finite cotangent, log-conormal, active
legality, source, and boundary obstruction modules whenever their desired gate
is flatness or vanishing after flatification.

---

# 7. Two-ideal mixed-Rees compression

Let `I subset K subset A` be finitely generated ideals.  Define

```text
R_(I,K)(A)
  = directSum_(a,b>=0) I^a K^b U^a V^b
  subset A[U,V],

R_(I,K)(M)
  = directSum_(a,b>=0) I^a K^b M U^a V^b.
```

## Proposition 7.1 — Noetherian finite mixed-Rees module

`R_(I,K)(A)` is a finite-type Noetherian `A`-algebra and `R_(I,K)(M)` is finite
as a module over it.

### Proof

If `f_i` generate `I` and `g_j` generate `K`, the algebra is generated by the
finitely many homogeneous elements

```text
f_i U,
g_j V.
```

If `m_l` generate `M`, the degree-`(0,0)` elements `m_l` generate the mixed-Rees
module.  QED.

Let `h=qV` be the homogeneous element corresponding to a chart pivot
`q in K`.  For a finite graded submodule `P subset N`, the colon chain

```text
(P : h) <= (P : h^2) <= ...
```

stabilizes by Noetherianity.  Hence

```text
(P : h^infinity) = (P : h^e)
```

for one finite exponent `e` valid simultaneously in every bidegree.  The
power-torsion submodule and every relative saturation quotient are therefore
finite graded modules.

Any kernel or cokernel of a homogeneous map between finite mixed-Rees modules
is finite.  Thus, once the chart common-core maps are constructed from
homogeneous mixed-Rees maps, the complete Tor and Valabrega defects are finite
without a degree-by-degree cutoff argument.

---

# 8. Revised finite-state packet

The finite packet should now be defined affine-algebraically as

```text
ANC-TVC_C = direct sum of
  gr_(I_C)(M_j) for all passive owners,
  homogeneous Tor kernels,
  homogeneous power-saturation/Valabrega quotients,
  finite log-conormal modules,
  finite source/Cartier torsion modules,
```

viewed as one coherent module on a finite affine normal/mixed-Rees scheme over
`C`.

The existence of a `U`-admissible flatifier follows from the general affine
flatification theorem.  The packet is not yet an actual resolution step because
three bridges remain:

```text
1. exact construction and overlap gluing of the homogeneous TVC maps;
2. replacement of a possibly singular flatifier by a dimension-strict regular
   centre-enriched word;
3. ambient trace transport and hereditary reentry without reset.
```

---

# 9. Candidate-graph consequences

Delete or demote:

```text
FINITE_REES_SERRE_PASSIVE_PACKET as an independent load-bearing theorem;
PROJECTIVE_NORMAL_TAIL as a necessary existence device;
HILBERT_POLYNOMIAL_COMPRESSION as a central gate.
```

Retain projectivization only as an optional geometric visualization or for
specific proper comparison arguments.

Replace the X038 frontier nodes by:

```text
X038-G7A  FINITE_ASSOCIATED_GRADED_MODULE_OVER_AFFINE_NORMAL_CONE
          standard proof closed; Lean scheme interface open

X038-G7B  FINITE_TWO_IDEAL_MIXED_REES_MODULE
          standard proof closed; Lean graded-algebra interface open

X038-G7C  UNIFORM_HOMOGENEOUS_POWER_SATURATION_BOUND
          standard Noetherian proof closed; Lean open

X038-G8A  AFFINE_FLATIFICATION_OF_THE_COMPLETE_ANC_TVC_PACKET
          standard flatification input identified

X038-G8B  GRADING_PRESERVED_BY_DEGREE_ZERO_STRICT_TRANSFORM
          elementary proof identified; scheme/Lean interface open.
```

The highest-information cut becomes smaller:

```text
AFFINE_CHART_COMMON_CORE_AND_KERNEL_FORMULAS
+
REGULAR_AMBIENT_REALIZATION_OF_THE_AFFINE_FLATIFIER
+
CARTIER_STABLE_ALL_CHART_NO_RESET.
```

---

# 10. Revised decisive theorem

> **Affine Normal-Cone Tor-Valabrega Flat-Kill Theorem.**  For every raw
> regular carrier `C`, the complete passive, logarithmic, source-Cartier, and
> Tor-Valabrega legality data form one finite coherent graded module on an
> affine finite-type normal/mixed-Rees scheme over `C`.  Its generic legal
> locus admits a `U`-admissible flatifying blowup of `C`.  A centre-enriched
> regular word in lower carrier dimension factors through this flatifier and is
> realized by ordinary ambient trace blowups.  On every chart the two
> Tor-Valabrega common-core kernels vanish after flat-kill, so the ambient
> associated graded module agrees with the flat strict transform of the affine
> normal-cone module.  The resulting carrier is jointly active, passive, and
> logarithmically legal, and all data reenter without reset.

This remains a candidate theorem.  The supplement closes only the finite
algebra/flatifier-existence compression, not its ambient realization.

---

# 11. Truth boundary

```text
AFFINE_NORMAL_CONE_FINITE_MODULE_PROOF             = closed standard math
MIXED_REES_FINITE_MODULE_PROOF                     = closed standard math
UNIFORM_NOETHERIAN_SATURATION_ARGUMENT             = closed standard math
GENERAL_AFFINE_FLATIFICATION_INPUT_IDENTIFIED      = true
PROJECTIVE_REES_SERRE_TAIL_REQUIRED                = false

SCHEME_LEVEL_TVC_COMMON_CORE_PROVED                = false
REGULAR_AMBIENT_REALIZATION_OF_FLATIFIER_PROVED    = false
CARTIER_STABLE_ALL_CHART_NO_RESET_PROVED           = false
UNIVERSAL_JOINTLY_LEGAL_CENTRE_WORD_PROVED         = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION         = false
FORMAL_GLOBAL_STATUS                               = OPEN_GAP
```

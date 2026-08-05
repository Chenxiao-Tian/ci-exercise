# MLEL-X040 Final Supplement

## Functorial Flatifier Sources and the Return of the Projective Rees-Serre Packet

**Parent:** `MLEL-X040 / CFT-ACN`  
**Class:** `NATURALITY-DRIVEN CANDIDATE-GRAPH CORRECTION`  
**Date:** 2026-08-04 ET  
**Global status:** `OPEN_GAP`

---

# 1. Hidden choice in the first X040 formulation

The first X040 formulation said:

```text
for every maximal carrier choose one componentwise-admissible flatifier;
compress its word to one source ideal;
multiply the ambient traces.
```

Existence of a flatifier is not enough for a functorial resolution algorithm.
Different flatifiers can have different source supports, words, and ambient
trace ideals.  Taking the product over a finite symmetry orbit removes an
ordering choice only after the flatifier itself has been selected.  It does not
remove arbitrary flatifier selection.

Thus the common product must be formed from a **functorial flatifier source**.

---

# 2. Why the affine normal-cone packet is not by itself a canonicality theorem

For a regular carrier `C` and one passive owner `M`, the complete associated
graded module

```text
G_C(M)=gr_(I_C)(M)
```

is finite over the affine normal-cone algebra

```text
Sym_(O_C)(I_C/I_C^2).
```

This proves that ordinary flatification can be applied to the complete graded
portfolio and is sufficient for existence.  General affine flatification,
however, does not by itself select a unique source ideal or a source word
functorial under every smooth/etale base change.

The X038 deletion of the projective tail was therefore correct only as an
**existence compression**.  It was too strong as a **naturality compression**.

---

# 3. Proper functorial flatification as the canonicality engine

Let

```text
E_C=I_C/I_C^2,
P_C=P(E_C),
pi_C:P_C->C.
```

For every passive owner, let `F_C(M)` be the coherent projective-normal sheaf
associated with `G_C(M)`.  Add the finite low-degree Rees pieces, bounded
irrelevant-torsion/comparison modules, logarithmic conormal modules, and
source-Cartier modules as coherent modules on `C` itself.  Regard the latter as
proper packets through the identity morphism `C->C`.

The complete **functorial Rees-Serre carrier packet** is

```text
FRS_C = (
  finite low-degree and transition modules on C,
  projective-normal sheaves on P_C,
  source and boundary labels,
  comparison morphisms
).
```

A functorial flatification theorem for proper morphisms produces a finite
admissible blowup word of `C`, functorial under flat base change, which makes the
strict transforms of the complete proper packet flat.  Smooth and etale maps
are flat, so the source word is compatible with the functoriality category
required by the resolution program.

In positive characteristic the flatifying centres are not known to be regular.
They remain source ideals to be realized by the lower-dimensional supported
principalization compiler.  The theorem supplies canonical source data, not
final permissible centres.

---

# 4. Finite low-degree / proper-tail comparison remains necessary

Flatness of the projective-normal sheaf alone does not imply flatness of every
homogeneous piece.  A finite Rees-Serre comparison packet must retain:

```text
1. a finite presentation of G_C(M);
2. bounded irrelevant torsion;
3. a finite transition window of low graded pieces;
4. the coherent tail sheaf on P_C;
5. the comparison maps G_n -> pi_*F(n);
6. the necessary higher-direct-image/base-change certificates.
```

Once this finite packet is flat, every low piece is flat directly and every
high piece is flat through the projective comparison.  The abstract finite
prefix/tail and direct-sum compilers written in X036/X037 remain useful exact
Lean leaves.

The cutoff must be defined by a base-change-compatible certificate rather than
an arbitrary presentation-dependent integer.  One acceptable interface is a
finite comparison certificate included as part of the functorial proper packet;
its invariance is an independent edge theorem.

---

# 5. Finite maximal-carrier groupoid

Let `Max(A)` be the intrinsic finite antichain of inclusion-maximal carriers and
form the disjoint union

```text
C^max = disjointUnion_(C in Max(A)) C.
```

The finite arrangement automorphism groupoid acts on `C^max` and on the direct
sum of the proper FRS packets.  Apply functorial proper flatification to this
single groupoid-equivariant packet.  Functoriality under isomorphisms and flat
base change makes the resulting component words equivariant; no arbitrary
choice of a preferred carrier or flatifier remains.

Compress the finite component words to immutable source ideals, lift them to
ambient trace ideals, and take their product.  The common trace product is now
canonical relative to the intrinsic state and packet, not merely symmetric
after a hidden choice.

---

# 6. Corrected common-trace chain

```text
finite intrinsic maximal-carrier groupoid
-> complete functorial Rees-Serre proper packet
-> functorial admissible flatification word on the disjoint carrier base
-> immutable component source ideals J_lambda
-> ambient traces K_lambda
-> canonical finite product K_common
-> lower-support-dimensional full-portfolio principalization
-> regular jointly legal common-refinement word
-> factor through every functorial source flatifier
-> simultaneous maximal-carrier normal flatness
-> Hironaka transitivity and nested wonderful persistence.
```

The affine normal-cone packet is retained as the exact all-degree semantic
object.  The projective Rees-Serre packet is retained as the proper
functoriality engine.  A bridge theorem proves that their flatness certificates
are equivalent in the required chamber.

---

# 7. New decisive edge

> **Functorial Carrier-Flatifier Source Theorem.**  For every regular raw
> carrier with finite passive/logarithmic/source portfolio, construct a finite
> proper Rees-Serre packet, canonically and compatibly with smooth/etale base
> change.  Functorial proper flatification produces a finite componentwise
> admissible source word whose strict transform makes the complete affine
> associated-graded portfolio flat.  The word, every source ideal obtained from
> its finite composition, and its ambient trace are invariant under the finite
> carrier groupoid.  The centres may be singular and are passed to the
> lower-dimensional regular realization compiler.

The theorem combines standard functorial flatification with project-specific
Rees-Serre comparison, source compression, and semantic alignment.  It is not
proved in this program.

---

# 8. Revised highest-information cut

```text
CFT-0  FUNCTORIAL_REES_SERRE_CARRIER_PACKET
CFT-1  FUNCTORIAL_PROPER_FLATIFIER_SOURCE
CFT-2  COMMON_TRACE_PRODUCT_AND_LOWER_SUPPORT_REALIZATION
CFT-3  SOURCE_PURE_TRANSFORM_COMMON_REFINEMENT
CFT-4  REGULAR_FLAG_FLAT_LIFT
CFT-5  SOURCE_CONSERVATIVE_ALL_CHART_NO_RESET.
```

The common product solves cross-carrier interaction only after `CFT-0/1`
remove the hidden flatifier choice.

---

# 9. Publication consequence

Paper III regains a self-contained projective Rees-Serre and functorial
flatification chapter.  The common-product compression still removes repeated
flatifier reconciliation and general clean-square transport.  The revised
central estimate is **558 dense Annals/AMS-equivalent pages**:

```text
I    90
II  120
III 138
IV   84
V    78
VI   48
    ---
    558
```

The single-volume editorial estimate becomes `604-640` physical pages.

---

# 10. Truth boundary

```text
HIDDEN_ARBITRARY_FLATIFIER_CHOICE_IDENTIFIED       = true
AFFINE_PACKET_SUFFICIENT_FOR_EXISTENCE             = true
AFFINE_PACKET_ALONE_SUFFICIENT_FOR_FUNCTORIALITY   = false
PROJECTIVE_REES_SERRE_PACKET_RESTORED              = true
FUNCTORIAL_PROPER_FLATIFICATION_INPUT_IDENTIFIED   = true
FINITE_MAXIMAL_CARRIER_GROUPOID_PACKET_IDENTIFIED  = true

FUNCTORIAL_REES_SERRE_COMPARISON_PROVED            = false
FUNCTORIAL_CARRIER_FLATIFIER_SOURCE_PROVED         = false
REGULAR_REALIZATION_OF_FUNCTORIAL_FLATIFIER_PROVED = false
COMMON_REFINEMENT_PURE_TRANSFORM_PROVED            = false
REGULAR_FLAG_FLAT_LIFT_PROVED                      = false
ALL_CHART_NO_RESET_PROVED                          = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION         = false
FORMAL_GLOBAL_STATUS                               = OPEN_GAP
```

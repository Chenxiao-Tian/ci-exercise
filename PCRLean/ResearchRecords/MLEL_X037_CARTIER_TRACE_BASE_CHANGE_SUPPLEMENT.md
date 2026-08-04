# MLEL-X037 Supplement

## Carrier-Side Cartier-Trace Base Change after Flatification

**Parent:** `MLEL-X037 / CTW-BRT`  
**Status:** `MATHEMATICAL_PROOF_SKETCH_CLOSED / LEAN_OPEN / AMBIENT_INTERCHANGE_OPEN`  
**Date:** 2026-08-04

---

# 1. Purpose

X037 introduced source-labelled Cartier-trace words because strict transforms
remember their centres.  This supplement closes one carrier-side subproblem:
once the strict transform produced by a flatifier is flat over the flatified
base, any further dominating regular modification recovers it by the
source-labelled Cartier pure transform.

This does not identify that carrier transform with the associated graded of the
ambient strict transform.  The bifiltered Rees interchange defect remains the
central open bridge.

---

# 2. Proposition

> **Proposition (flat Cartier-trace base change).**  Let `b:S'->S` be a blowup
> with exceptional effective Cartier divisor `E`.  Let `f:X->S` be a morphism,
> let `F` be a quasi-coherent sheaf on `X`, and let `F^str` be its strict
> transform on `X'=X times_S S'`.  Let `g:T->S'` be any morphism and put
> `D=g^{-1}E`.  Assume:
>
> 1. `D` is an effective Cartier divisor on `T`;
> 2. `F^str` is flat over `S'`.
>
> Then the pullback `g^*F^str` is canonically the quotient of the pullback of
> `F` to `X times_S T` by its maximal submodule of sections supported over
> `D`.  Equivalently, `g^*F^str` is the source-labelled Cartier pure transform
> on `T`.

The statement applies equally to a coherent sheaf on a projective-normal
bundle over `S`.

---

# 3. Proof

On `X'` there is an exact sequence

```text
0 -> T_E -> pr_X^*F -> F^str -> 0,
```

where `T_E` is the maximal submodule supported over the exceptional divisor
`E`.

Because `F^str` is flat over `S'`, base change along `g:T->S'` preserves
left exactness at the final quotient.  Hence on `X times_S T` we obtain

```text
0 -> g^*T_E -> F_T -> g^*F^str -> 0.
```

The submodule `g^*T_E` is supported over `D`.  Conversely, `g^*F^str` is flat
over `T`, since flatness is preserved by base change.  Multiplication by a local
equation of the effective Cartier divisor `D` is injective on every `T`-flat
module.  Therefore `g^*F^str` has no nonzero section supported over `D`.

Every `D`-supported submodule of `F_T` must consequently map to zero in
`g^*F^str`, hence is contained in `g^*T_E`.  Thus `g^*T_E` is exactly the
maximal `D`-supported submodule and

```text
F_T / H^0_D(F_T)  ~=  g^*F^str.
```

This proves the proposition.

---

# 4. Corollary for a regular word dominating a flatifier

Let

```text
S^flat -> S
```

be the final base of a finite flatification word and let `F^flat` be the final
strict transform, flat over `S^flat`.  Suppose a regular-centre word

```text
T -> S
```

factors through `S^flat` and the pullback of the total exceptional locus is an
SNC Cartier divisor on `T`.  Then the source-labelled pure transform of `F` on
`T` is canonically the pullback of `F^flat`, and is therefore flat over `T`.

Consequently the carrier-side phrase

```text
regular word dominating the centre-enriched flatifier
```

is sufficient once it includes:

```text
a factorization through the final flatified base,
the immutable total-exceptional source label,
and the Cartier pure-transform quotient.
```

A bare domination of morphisms without these data is insufficient.

---

# 5. Effect on the X037 frontier

The former node

```text
X037-G6 CARTIER_TRACE_BASE_CHANGE_WITH_TOR_CERTIFICATE
```

splits into:

```text
X037-G6A FLAT_CARTIER_TRACE_BASE_CHANGE
          mathematical proof above; Lean interface open

X037-G6B REGULAR_WORD_FACTORIZATION_THROUGH_FINAL_FLATIFIER
          open lower-dimensional geometric compiler

X037-G6C TOTAL_EXCEPTIONAL_SOURCE_LABEL_AND_SNC_PULLBACK
          open hereditary/logarithmic transport
```

The highest-information project-specific cut becomes

```text
X037-G10  ALL_CHART_PURE_TRANSFORM_INTERCHANGE_MORPHISM
X037-G11  FINITENESS_AND_BASE_CHANGE_OF_REES_INTERCHANGE_DEFECT
X037-G12  RID_VANISHING_OR_STRICT_FITTING_SUPPORT_DESCENT
X037-G18  CARTIER_TRACE_MACRO_NO_RESET.
```

Carrier flatness after factorization is no longer the conceptual mystery.  The
remaining mystery is the ambient comparison

```text
associated graded of ambient strict transform
versus
carrier projective-normal pure transform.
```

---

# 6. Truth boundary

```text
FLAT_CARTIER_TRACE_BASE_CHANGE_NATURAL_PROOF      = closed
LEAN_SCHEME_INTERFACE                             = open
REGULAR_FACTORING_WORD                            = open
TOTAL_EXCEPTIONAL_SNC_SOURCE_TRANSPORT            = open
AMBIENT_ASSOCIATED_GRADED_INTERCHANGE              = open
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION         = false
FORMAL_GLOBAL_STATUS                               = OPEN_GAP
```

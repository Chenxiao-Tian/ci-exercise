# MLEL-X040 Final Semantic Supplement

## The Common Product Uses Modification Ideals, Not a Lossy Compression of Transform Payloads

**Parent:** `MLEL-X040 / CFT-ACN`  
**Class:** `CENTRE-DEPENDENCE SEMANTIC CORRECTION`  
**Date:** 2026-08-04 ET  
**Global status:** `OPEN_GAP`

---

# 1. Correction

A finite blowup word can be represented, as a modification morphism, by one
blowup ideal.  It does not follow that the iterated strict transform of a sheaf
is the strict transform associated with that one composite ideal.  Strict
transform remembers the actual centres.

Therefore X040 may compress a functorial flatifier word to one ideal only for
the purpose of constructing a common-refinement modification.  It may not
compress the transform semantics.

---

# 2. Source-word package

For each maximal carrier `C_lambda`, the functorial flatifier output is retained
as the complete package

```text
S_lambda = (
  W_lambda,                 -- the ordered centre-enriched flatifier word
  pi_lambda:C_lambda^f->C_lambda,
  J_lambda^mod,             -- one ideal representing pi_lambda as a blowup
  F_lambda^f,               -- final strict transforms of the full packet
  exceptional/source lineage,
  overlap and base-change certificates
).
```

The ideal `J_lambda^mod` is only the **modification ideal**.  The transform
payload is `(W_lambda,F_lambda^f,lineage)`.

Lift `J_lambda^mod` to its ambient trace ideal `K_lambda^mod` and form

```text
K_common^mod = product_lambda K_lambda^mod.
```

A regular common word making `K_common^mod` invertible factors through every
modification `pi_lambda`.  On the final model, the desired source transform is
defined as the pullback of `F_lambda^f`, not by forgetting `W_lambda` and
recomputing strict transform from `J_lambda^mod` alone.

---

# 3. Required realization theorem

The remaining project edge is:

> **Source-Word Realization under a Common Refinement.**  Let a regular ordinary
> ambient word factor through the modification morphism underlying a
> centre-enriched flatifier word.  If the final source strict transform is flat
> and the complete exceptional/source lineage pulls back as an SNC Cartier
> divisor, then the actual iterated strict transform along the regular ambient
> word is canonically the pullback of the final source strict transform.  The
> comparison is compatible with all charts, overlaps, owners, controlled marks,
> and smooth base change.

This is stronger than the universal property of blowup and weaker than saying
that strict transform depends only on the composite morphism.  It retains
exactly the missing centre data identified in X037.

---

# 4. Corrected chain

```text
functorial carrier flatifier
-> complete source-word package S_lambda
-> modification ideal J_lambda^mod
-> common product modification K_common^mod
-> regular lower-dimensional common-refinement word
-> factorization through every pi_lambda
-> source-word realization theorem
-> pullback of every flat final strict transform
-> simultaneous maximal-carrier legality.
```

---

# 5. Truth boundary

```text
FINITE_WORD_AS_ONE_MODIFICATION_BLOWUP          = standard math
ITERATED_STRICT_TRANSFORM_DEPENDS_ONLY_ON_IDEAL = false
SOURCE_WORD_PAYLOAD_RETAINED                    = true
COMMON_PRODUCT_USED_ONLY_FOR_MODIFICATION       = true
SOURCE_WORD_REALIZATION_THEOREM_PROVED          = false
REGULAR_FLAG_FLAT_LIFT_PROVED                   = false
ALL_CHART_NO_RESET_PROVED                       = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION      = false
FORMAL_GLOBAL_STATUS                            = OPEN_GAP
```

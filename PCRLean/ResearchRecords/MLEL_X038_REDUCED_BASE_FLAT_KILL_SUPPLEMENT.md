# MLEL-X038 Supplement

## Reduced-Base Flat-Kill without a Finite-Rank Hypothesis

**Parent:** `MLEL-X038 / TVF-ANC`  
**Status:** `STANDARD ALGEBRA PROOF CLOSED / SCHEME-LEAN INTERFACE OPEN`  
**Date:** 2026-08-04

---

# 1. Correction

An earlier formulation justified flat-kill by saying that the transformed
defect was a finitely presented flat module over the carrier and hence locally
free of rank zero.  This is not the right argument: a coherent module on an
affine finite-type scheme over the carrier need not be finite as a module over
the carrier ring.

The correct proof uses reducedness of the carrier and flatness over the carrier.
No finite-rank hypothesis over the carrier is required.

---

# 2. Algebraic theorem

> **Reduced-Base Flat-Kill Lemma.**  Let `A` be a reduced Noetherian ring with
> minimal primes `p_1,...,p_s`.  Let `B` be an `A`-algebra and let `M` be a
> `B`-module which is flat as an `A`-module.  If
>
> ```text
> M tensor_A A_(p_i) = 0
> ```
>
> for every minimal prime `p_i`, then `M=0`.

## Proof

Because `A` is reduced, the diagonal map

```text
A -> product_i A_(p_i)
```

is injective.  Indeed its kernel consists of the elements annihilated after
localization at every minimal prime, hence is contained in the intersection of
the minimal primes, which is the nilradical and therefore zero.

The set of minimal primes is finite because `A` is Noetherian.  Thus the finite
product is also the finite direct sum as an `A`-module.  Tensoring the injection
with the flat `A`-module `M` preserves injectivity and gives

```text
M -> product_i (M tensor_A A_(p_i)).
```

Every target factor is zero by hypothesis, so `M=0`.  QED.

---

# 3. Geometric form

> Let `S` be a reduced locally Noetherian scheme with finitely many irreducible
> components locally, let `f:X->S` be a morphism, and let `F` be a
> quasi-coherent module flat over `S`.  If the restriction of `F` to the fibre
> over the generic point of every irreducible component of `S` is zero, then
> `F=0`.

The assertion is affine-local on `X` and `S`, where it is exactly the algebraic
lemma.

For the X038 flat-kill compiler, the good open `U subset S` must contain the
generic point of every component.  If a defect sheaf is zero over `U`, then its
strict transform under a `U`-admissible flatifier has zero generic fibres.  Once
the strict transform is flat over the reduced blown-up carrier and every
component still meets the inverse image of `U`, the lemma forces the defect to
vanish globally.

---

# 4. Why flatness is essential

Without flatness the conclusion fails.  For example, over a domain `A` any
nonzero torsion module `A/(a)` vanishes after localization at the generic point
but is not zero.  The flatifier is therefore used twice:

```text
for the passive associated-graded summands:
  it produces the desired flatness;

for the generically zero Tor-Valabrega defect summands:
  flatness plus reduced-base generic vanishing forces actual zero.
```

---

# 5. Component condition

It is not enough that `U` be dense in the total topological space if a component
is missed.  The flat-kill certificate must record:

```text
U contains every minimal point of the carrier;
the admissible flatifier is an isomorphism over U;
every component of the transformed carrier meets U;
the transformed carrier remains reduced.
```

For a regular carrier and a blowup in a centre disjoint from `U`, the transformed
carrier is regular once the realizing word uses regular centres, hence reduced.
The componentwise statement must nevertheless be present explicitly in the
edge certificate.

---

# 6. Effect on the frontier

The node

```text
X038-G12 FLAT_GENERICALLY_ZERO_IMPLIES_ZERO
```

is mathematically reduced to the injectivity

```text
A -> product of localizations at minimal primes
```

and preservation of that injection under tensoring with a flat module.  The
remaining work is the exact scheme-level and Lean interface, not new algebraic
geometry.

The decisive geometric gap remains regular ambient realization of the
flatifier and the Regular-Flag Legal-Lift Theorem.

---

# 7. Truth boundary

```text
REDUCED_BASE_FLAT_KILL_ALGEBRA_PROOF       = closed
FINITE_RANK_OVER_BASE_REQUIRED             = false
COMPONENTWISE_GENERIC_CONDITION_REQUIRED   = true
SCHEME_LEAN_INTERFACE                      = open
REGULAR_AMBIENT_REALIZATION                = open
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION = false
FORMAL_GLOBAL_STATUS                       = OPEN_GAP
```

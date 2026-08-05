# MLEL-X043 Supplement

## Finite Normal Hasse Jets and Canonical Ambient Trace Words

**Parent:** `MLEL-X043 / ATR-NJC`  
**Date:** 2026-08-05  
**Status:** local theorem closure; universal centre synthesis and global termination remain open.

---

## 1. Why restriction to the carrier is insufficient

Let `W=Spec k[x,y]`, `C=V(x)`, and `D=V(x,y)`. For mark `b=2`, the ideal
`a=(x)` restricts to zero on `C`, hence satisfies every condition visible from
`a O_C`. Nevertheless `x` is not in `(x,y)^2`, so `D` is not permissible for
`(a,2)`.

The missing datum is the first normal coefficient of `x` along `C`. Thus
ambient active legality cannot be recovered from the degree-zero restriction;
all normal Hasse coefficients below the mark are required.

---

## 2. Intrinsic truncated jet

For a regular immersion `C -> W` with ideal `I` and a coherent ideal `a`, set

```text
J_C^{<b}(a)=(a+I^b)/I^b subset O_W/I^b.
```

This is independent of a normal frame. Its finite `I`-adic filtration has
length `b`. In an etale normal frame `x_1,...,x_r`, the Hasse-Taylor map gives
an isomorphism of filtered `O_C`-modules

```text
O_W/I^b
  ~= directSum_(|alpha|<b) O_C x^alpha
```

on the chosen chart, and presents `J_C^{<b}(a)` by the coefficients
`partial_x^[alpha](f)|_C`.

Changing the normal frame changes the coefficient vector by an invertible
block-triangular matrix whose diagonal blocks are the symmetric powers of the
conormal transition matrix. Hence the generated finite idealistic filtration
is intrinsic.

---

## 3. Exact marked-divisibility theorem

Let `D subset C` be regular, let `L=I_(D/C)`, and let `J=I_(D/W)`.

### Theorem

For a local section `f` and an integer `b>=1`, the following are equivalent:

```text
f in J^b;

for every multi-index alpha with |alpha|<b,
partial_x^[alpha](f)|_C in L^(b-|alpha|).
```

### Proof

The forward implication follows by applying Hasse derivatives to products of
`b` generators of `J` and restricting to `C`.

For the converse, modulo `I^b` write

```text
f = sum_(|alpha|<b) c_alpha x^alpha.
```

Every coefficient satisfies `c_alpha in L^(b-|alpha|)`, so every summand is in
`J^b`. The omitted remainder is in `I^b subset J^b`.

No completion or infinite iteration is used. The criterion is finite because
normal degree `>=b` is automatically in `J^b`.

---

## 4. Rees-family form

If a marked Rees algebra has homogeneous generators

```text
f_lambda T^(b_lambda),
```

its normal-coefficient family on `C` consists of

```text
partial_x^[alpha](f_lambda)|_C T^(b_lambda-|alpha|)
for |alpha|<b_lambda.
```

A regular `D subset C` is ambiently permissible for the original generators if
and only if it is permissible for this finite family. Integral/Hasse saturation
may enlarge the family, but does not change the criterion when the saturation
is known to preserve permissible centres.

---

## 5. Canonical ambient word

Let

```text
C_m -> ... -> C_0=C
```

be a finite word of blowups in regular centres `D_i subset C_i`. Define
`W_(i+1)=Bl_(D_i)(W_i)` and let `C_(i+1)` be the strict transform of `C_i`.
Then canonically

```text
C_(i+1)=Bl_(D_i)(C_i).
```

If every `D_i` is permissible for the finite normal-coefficient family,
normal-flat for the exactified passive portfolio, and normal-crossing with the
induced boundary, the ambient word is jointly legal.

The centre on `W_i` is not a new lift or closure: it is the same closed
subscheme `D_i`, defined by the inverse image of its carrier ideal. Regularity
follows from composition of regular immersions.

---

## 6. Counterexample boundaries

### 6.1 Restriction-only failure

`a O_C` does not detect normal coefficients, as in `(a,b)=((x),2)` above.

### 6.2 Morphism-only failure

An effective Cartier centre can produce the identity blowup while changing the
strict transform. The centre-exact ideal or source open must remain part of the
word.

### 6.3 Singular carrier centre

If `D` is not regular in `C`, the same closed subscheme need not be an allowed
ambient centre. X043 does not regularize a singular flatifier directly; it
uses lower-dimensional full-portfolio principalization to replace it by a word
of regular centres.

### 6.4 Active-only legality

Normal-jet divisibility does not imply passive normal flatness or boundary
compatibility. Those are separate rows of the joint portfolio.

### 6.5 Fixed finite jets independent of the mark

There is no universal cutoff independent of `b`. The finite bound is the
actual mark: all orders `<b` and no higher orders are required.

---

## 7. Updated frontier

The local legality layer is now finite and intrinsic. The next nonstandard
problem is not ambientization but the existence, for every nonterminal
Frobenius--Hasse state, of an actual regular carrier arrangement whose complete
joint portfolio enters the lower-dimensional induction and whose associated
macro strictly lowers the global source-causal rank.

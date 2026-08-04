# MLEL-X038 Supplement

## Regular-Flag Legal Lifting and the Dimension-Strict Carrier Compiler

**Parent:** `MLEL-X038 / TVF-ANC`  
**Status:** `MAXIMUM-LIKELIHOOD EDGE THEOREM / LOCAL NORMAL FORM IDENTIFIED / FULL MODULE TRANSPORT OPEN`  
**Date:** 2026-08-04

---

# 1. Purpose

The final X038 correction separates three transform defects, but the global
compiler still needs a reason why recursively legalizing a preparatory centre
kills exactly those defects.  The missing edge is a regular-flag transform
theorem.

The relevant geometry is a flag

```text
D subset C subset X
```

of regular immersions, where `C` is a raw carrier and `D` is one regular centre
in a lower-dimensional word that principalizes or flatifies data on `C`.

The correct recursive policy is:

```text
before blowing up D in X,
legalize D for the complete affine normal-cone portfolio of C.
```

Under that certificate, the Tor--Valabrega factorization is predicted to be
exact, so the ambient transform of the portfolio on `C` equals its
centre-enriched carrier strict transform.

---

# 2. Local normal form for a regular flag

Let `R` be a regular local ring and let

```text
I subset K subset R
```

define regular immersions

```text
C=V(I) subset X=Spec(R),
D=V(K) subset C.
```

Because regular immersions compose, the conormal sequence

```text
0 -> (I/I^2) tensor O_D
  -> K/K^2
  -> (K/I)/(K/I)^2
  -> 0
```

is locally split exact.  After choosing local bases and lifting them, one may
write

```text
I = (x_1,...,x_r),
K = (x_1,...,x_r,y_1,...,y_s),
```

where the displayed sequence is regular.

In the blowup of `K`, the standard charts meeting the strict transform of `C`
are the `y_j`-charts.  On the `y_1`-chart,

```text
x_i = y_1 x_i',
y_j = y_1 y_j'  (j>1),
```

and the strict transform of `C` is defined by

```text
I'=(x_1',...,x_r').
```

The charts with pivot among the `x_i` do not meet the strict transform of `C`.
Thus, on every relevant chart, the controlled transform of the carrier ideal is
already its strict transform.  The purely ideal-theoretic saturation defect
vanishes in the regular-flag chamber.

Equivalently, the exceptional parameter is regular modulo the controlled
carrier ideal, and the X038 power-saturation lemma gives

```text
Sat_q(J)=J.
```

---

# 3. Conormal line twist

On the same chart, the old and new normal generators satisfy

```text
x_i = q x_i'.
```

Therefore the conormal bundles obey a canonical line-twist relation

```text
I'/I'^2
  ~= pullback(I/I^2) tensor O(E_C)
```

with the sign determined by the convention for `O(E_C)` and its canonical
section.  Dually, the normal bundle is the pullback of the old normal bundle
with the inverse exceptional twist.  Projectivization forgets the common line
twist, but the affine normal-cone theorem must retain it degree by degree.

The twist is not an ambiguity: it is fixed by the explicit equation
`x_i=q x_i'` on every standard chart and must be checked on overlaps.

---

# 4. The complete passive object to be enrolled at D

Let `M_1,...,M_t` be the ambient passive owners and put

```text
G_C(M_j)=gr_I(M_j).
```

Each `G_C(M_j)` is a finite module on the affine normal cone of `C` in `X`.
Before executing the centre `D`, the recursive state on `D` must include the
finite direct sum

```text
P_(C,D) = directSum_j G_C(M_j)
          + log-conormal modules
          + source-Cartier torsion modules
          + the finite Rees exact-sequence kernels needed for controlled
            division.
```

The legality certificate for `D` requires:

```text
1. Tor safety for the finite Rees filtration presentation;
2. normal flatness of P_(C,D) along D;
3. SNC compatibility of the regular flag with the boundary;
4. active marked-power containment;
5. nonidentity of the ambient trace action.
```

The first two clauses are exactly the hypotheses expected to kill the Tor
kernel and the two module-theoretic Valabrega defects.

---

# 5. Candidate regular-flag transform theorem

> **Regular-Flag Legal-Lift Theorem.**  Let `D subset C subset X` be a flag of
> regular immersions in a regular Noetherian ambient scheme.  Let `M` be a
> finite owner module and let `G_C(M)=gr_C(M)`.  Suppose `D` carries the full
> joint-legality certificate for the finite affine normal-cone/Rees portfolio
> attached to `(C,M)`: the relevant Rees filtration sequences are Tor-safe,
> the induced graded portfolio is normally flat along `D`, and the flag is
> logarithmically transverse to the total boundary.  Blow up `X` in `D`, let
> `C'` and `M'` be the strict transforms, and let `E_C` be the exceptional
> divisor on `C'=Bl_D(C)`.  Then there is a canonical all-chart isomorphism
>
> ```text
> gr_(C')(M')
>   ~= StrictTransform_D(gr_C(M)) tensor the canonical grading line twist.
> ```
>
> The isomorphism is compatible with overlaps, finite owner sums, smooth base
> change, source labels, and controlled marks.  In the X038 factorization,
> `ker(alpha)`, `ker(beta)`, and `coker(beta)` are zero.

This is the maximum-likelihood edge theorem connecting recursive centre
legality to ambient passive transport.  It is not yet proved.

---

# 6. Proof decomposition

The theorem should be decomposed as follows.

```text
RFL-1  regular-flag etale normal form;
RFL-2  relevant-chart coverage: only relative y-pivots meet C';
RFL-3  controlled carrier ideal equals strict carrier ideal;
RFL-4  conormal exceptional line twist;
RFL-5  finite Rees filtration presentation of every owner;
RFL-6  Tor safety implies exact strict transform of the filtration sequences;
RFL-7  normal flatness implies exceptional regularity on every quotient;
RFL-8  power saturation and Valabrega kernel/cokernel vanish;
RFL-9  degreewise transform isomorphism;
RFL-10 direct-sum reconstruction of the full affine normal-cone module;
RFL-11 double-localization overlap equality;
RFL-12 smooth-base-change and source-ledger naturality.
```

`RFL-3` is supported by the regular quotient saturation lemma already written
in Lean.  `RFL-9` is supported abstractly by
`ControlledCoreInterchange.lean`.  The scheme, Rees, overlap, and naturality
nodes remain open.

---

# 7. Dimension-strict carrier legalization compiler

Define `Legalize_n(d)` to mean:

> In an `n`-dimensional regular ambient scheme, every regular raw carrier of
> dimension at most `d`, equipped with a finite active/passive/log/source/debt
> portfolio, admits a finite preparatory ambient word after which its strict
> transform is jointly legal.

The recursion is:

```text
Legalize_n(d):
  1. flatify/principalize the finite affine packet on the d-dimensional carrier;
  2. choose a lower-dimensional regular word factoring through the flatifier;
  3. for every word centre D of dimension e<d, invoke Legalize_n(e);
  4. blow up the resulting legal ambient trace centre;
  5. use the Regular-Flag Legal-Lift Theorem to transport the carrier packet;
  6. continue the source-labelled lower-dimensional word;
  7. at the end, inherit flatness/log legality from the centre-enriched
     flatifier and output the legalized carrier.
```

The base case `d=0` is rigid: a regular zero-dimensional carrier has no proper
nonempty subcentre, finite modules over its residue fields are flat, and every
proper contact ideal is absent.  Terminal, empty, and forbidden identity actions
are separated by the action classifier.

Each recursive call satisfies

```text
e < d < n.
```

Thus the nested legalization recursion is well founded independently of the
outer singularity rank.  The finite length of the lower-dimensional
principalization word supplies the internal macro-height coordinate.

---

# 8. Removal of the same-level fixed-point problem

A misleading formulation would attempt to choose a flatifier for a carrier,
construct the transform defects caused by that flatifier, enlarge the packet,
and choose another flatifier on the same carrier.  This can create an
uncontrolled same-dimensional fixed-point loop.

The dimension-strict compiler avoids it:

```text
the carrier flatifier is chosen once;
its regular word centres are legalized recursively in smaller dimension;
the regular-flag theorem kills the transform defects at each lifted edge.
```

No repeated same-dimensional re-flatification is part of the algorithm.

---

# 9. Revised decisive cut

The geometric cut is now concentrated in three theorems:

```text
RFL-A  REGULAR_FLAG_LEGAL_LIFT
       exact all-chart transform interchange under joint legality;

RFL-B  CENTRE_ENRICHED_REGULAR_WORD_FACTORIZATION
       a lower-dimensional regular word factors through the affine flatifier
       while retaining every source ideal and Cartier trace;

RFL-C  CARRIER_LEGALIZATION_NO_RESET
       the recursive word transports all owners, sources, debts, boundary,
       packets, and rank coordinates without reset.
```

The ambient-dimension/carrier-dimension induction then compiles these edges into
jointly legal actual centres.

---

# 10. Truth boundary

```text
REGULAR_FLAG_LOCAL_NORMAL_FORM_IDENTIFIED          = standard math
RELEVANT_CHART_COVERAGE_IDENTIFIED                 = true
IDEAL_SATURATION_DEFECT_VANISHES_IN_REGULAR_FLAG   = candidate with Lean algebra leaf
CONORMAL_LINE_TWIST_IDENTIFIED                     = true
COMPLETE_OWNER_PORTFOLIO_ON_AFFINE_NORMAL_CONE     = finite standard math

REGULAR_FLAG_MODULE_TRANSFORM_THEOREM_PROVED       = false
ALL_CHART_OVERLAP_NATURALITY_PROVED                = false
CENTRE_ENRICHED_REGULAR_WORD_FACTORIZATION_PROVED  = false
CARRIER_LEGALIZATION_NO_RESET_PROVED               = false
UNIVERSAL_JOINTLY_LEGAL_CENTRE_WORD_PROVED         = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION         = false
FORMAL_GLOBAL_STATUS                               = OPEN_GAP
```

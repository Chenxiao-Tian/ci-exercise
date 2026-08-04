# MLEL-X038 Final Correction

## From a False Common-Quotient Cospan to the Tor--Valabrega Controlled-Core Factorization

**Final round label:** `MLEL-X038 / TVF-ANC`  
**Expanded title:** Tor--Valabrega Factorization, Affine Normal-Cone Flatification, and Dimension-Strict Legalization  
**Parent candidate:** `MLEL-X038 / TVC-FKL`  
**Status:** `COUNTEREXAMPLE-DRIVEN CANDIDATE-GRAPH REWRITE / OPEN_GAP`  
**Date:** 2026-08-04

---

# 1. Correction statement

The first X038 candidate asserted that the old chart-pulled normal graded piece
and the new normal graded piece both mapped epimorphically to a common
image-filtration quotient.  This is false before the controlled transform is
power-saturated.

The correct primitive is the canonical factorization

```text
old controlled graded object
        --alpha_a-->>
controlled-transform core gr_J
        --beta_a-->
new strict-carrier normal graded object gr_L.
```

Here:

```text
ker(alpha_a)       = Tor / filtration-base-change defect;
ker(beta_a)        = Valabrega intersection defect;
coker(beta_a)      = saturation-generation defect.
```

All three defects must vanish for transform interchange.

---

# 2. Minimal counterexample to the cospan

Let

```text
B = k[q,y],
J = (q y),
L = Sat_q(J) = (y),
N = B.
```

The degree-one controlled-to-strict map is

```text
J/J^2 -> L/L^2.
```

Its image is

```text
q (L/L^2),
```

so it is not surjective.  Therefore there is no canonical left epimorphism from
the new normal graded piece to the proposed common quotient in the general
unsaturated chamber.

The cokernel is

```text
(L/L^2) / q(L/L^2) ~= k[y]/(y)  after the evident identification,
```

and is precisely the missing saturation-generation defect.

The error is structural: saturation of a controlled-transform ideal, and
formation of its powers, need not commute before the exceptional parameter is
regular on all relevant quotients.

---

# 3. Correct affine setup

Let `A` be Noetherian, let

```text
I subset K subset A,
q in K,
B=A[K/q],
M a finite A-module.
```

Let

```text
N = M tensor_A B,
Nbar = N / q-power-torsion.
```

The scalar `q` is regular on `Nbar`.  Let `J` be the controlled transform of
`I`, generated locally by the divided elements `i/q`, and let

```text
L = Sat_q(J;B)
```

be the strict-transform carrier ideal.

For each normal degree `a`, define

```text
Core_a = J^a Nbar / J^(a+1) Nbar,
New_a  = L^a Nbar / L^(a+1) Nbar.
```

The Cartier-twisted strict transform of the old degree-`a` normal piece maps
surjectively to `Core_a`.  This map is induced by controlled division by
`q^a`; its kernel records failure of the old filtration to commute with chart
base change and strict-transform torsion removal.

The inclusion `J subset L` induces

```text
beta_a : Core_a -> New_a.
```

Its exact defects are

```text
ker(beta_a)
  = (J^a Nbar intersection L^(a+1) Nbar)
      / J^(a+1) Nbar,

coker(beta_a)
  = L^a Nbar
      / (J^a Nbar + L^(a+1) Nbar).
```

These are finite modules and are the appropriate relative
Valabrega-type defects.

---

# 4. Correct transform theorem

> **Affine Tor--Valabrega Factorization Theorem, candidate form.**  For every
> standard chart of a centre-enriched ambient trace blowup and every normal
> degree, there is a canonical factorization
>
> ```text
> Old_a --alpha_a-->> Core_a --beta_a--> New_a.
> ```
>
> The first map is an epimorphism.  Its kernel is the homogeneous
> filtration-base-change/Tor defect.  The kernel and cokernel of the second map
> are the homogeneous Valabrega intersection and saturation-generation
> defects.  If these three modules vanish, the composite gives the unique
> Cartier-twist-compatible isomorphism between the old controlled normal piece
> and the new strict-carrier normal piece.

The abstract final compiler is formalized in
`ControlledCoreInterchange.lean`.  The geometric construction and formulas are
not yet Lean-proved.

---

# 5. Affine normal-cone compression survives the correction

The cospan failure does not affect the second X038 simplification.

```text
gr_I(A)
```

is a finite-type Noetherian algebra over `A/I`, and `gr_I(M)` is finite over
it.  Likewise the two-ideal mixed-Rees module

```text
directSum_(a,b) I^a K^b M U^a V^b
```

is finite over a finite-type Noetherian algebra.  The homogeneous kernels and
cokernels of `alpha` and `beta`, together with their power-torsion and colon
modules, are therefore finite once the homogeneous maps are constructed.

Consequently the entire passive and Tor--Valabrega portfolio is one coherent
module on an affine finite-type normal/mixed-Rees scheme over the carrier.  A
general admissible flatification applies directly.  The projective
Rees--Serre tail remains deleted from the critical path.

---

# 6. Revised flat-kill packet

The finite packet now contains

```text
all passive associated-graded owner modules,
ker(alpha),
ker(beta),
coker(beta),
log-conormal defect modules,
source-Cartier torsion modules,
anchor-contact transform defects.
```

On the generic jointly legal locus:

```text
passive associated-graded modules are flat;
ker(alpha)=0;
ker(beta)=0;
coker(beta)=0;
log and source-Cartier defects vanish.
```

A simultaneous admissible flatifier makes the complete packet flat.  The three
generically zero defect modules then vanish on every component meeting the
good open.  This supplies the exact transform interchange needed for normal
flatness.

The remaining issue is to realize the possibly singular flatifier by a
centre-enriched word of ordinary ambient blowups in recursively legalized
regular trace centres.

---

# 7. Revised minimum open cut

```text
CUT-A
  scheme-level construction of alpha_a and beta_a;
  exact Tor, intersection, and cokernel formulas;
  homogeneous mixed-Rees packaging and overlap descent.

CUT-B
  factorization of an admissible affine flatifier through a
  lower-dimensional regular centre-enriched word;
  recursive joint legalization of every trace subcentre;
  ambient trace realization.

CUT-C
  Cartier-stable source compression;
  all-chart reconstruction without reset;
  geometric proof of carrier-dimension strictness.
```

The highest-information local theorem is now the simultaneous homogeneous
construction of `alpha` and `beta` from one finite two-ideal mixed-Rees module.

---

# 8. Final X038 candidate graph

```text
finite intrinsic state
-> actual raw regular carrier C
-> complete affine normal-cone passive packet
-> source-labelled carrier ideals

lower-dimensional principalization
-> recursively legal regular trace word
-> ambient trace blowups

on every chart:
  old controlled normal piece
  -- Tor epimorphism -->
  controlled core gr_J
  -- Valabrega map -->
  strict normal piece gr_L

finite affine packet:
  ker alpha + ker beta + coker beta

simultaneous affine flatification
-> flat-kill of generically zero defects
-> exact transform interchange
-> passive normal flatness and log legality
-> Cartier-stable hereditary reentry
-> dimension-strict termination
-> universal actual jointly legal centre word.
```

---

# 9. Publication consequence

The final X038 maximum-likelihood series remains six papers and **552 dense
Annals/AMS-equivalent pages**, but Paper III is retitled:

```text
Affine Normal-Cone Flatification,
Tor--Valabrega Factorization,
and Hereditary Reentry.
```

The cospan is recorded in the counterexample atlas rather than stated as a
lemma.

---

# 10. Truth boundary

```text
INITIAL_TWO_EPIMORPHISM_COSPAN                     = false
MINIMAL_COUNTEREXAMPLE_RECORDED                    = true
CONTROLLED_CORE_FACTORIZATION_IDENTIFIED           = true
TOR_KERNEL_IDENTIFIED                              = candidate
VALABREGA_KERNEL_AND_COKERNEL_IDENTIFIED           = candidate
AFFINE_NORMAL_CONE_COMPRESSION_RETAINED            = true
ABSTRACT_FACTORIZATION_LEAN_SOURCE_WRITTEN         = true

SCHEME_LEVEL_ALPHA_BETA_CONSTRUCTION_PROVED        = false
MIXED_REES_GLOBAL_PACKET_PROVED                    = false
REGULAR_AMBIENT_REALIZATION_OF_FLATIFIER_PROVED    = false
CARTIER_STABLE_ALL_CHART_NO_RESET_PROVED           = false
UNIVERSAL_JOINTLY_LEGAL_CENTRE_WORD_PROVED         = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION         = false
FORMAL_GLOBAL_STATUS                               = OPEN_GAP
```

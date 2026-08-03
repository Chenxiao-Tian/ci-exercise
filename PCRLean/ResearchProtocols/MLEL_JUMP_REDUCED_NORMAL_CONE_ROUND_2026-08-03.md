# MLE–Lean research baseline record

## Reduced normal cones, graph centres, and graded Frobenius heredity

**Record date:** 2026-08-03  
**Baseline line:** PCR-MLE-LEAN  
**Protocol:** PCR-JUMP-LEAN 2.0  
**Record type:** research-information baseline update  
**Certified Graph changed:** no  
**General positive-characteristic resolution proved:** no  
**Global truth status:** `OPEN_GAP`

## 1. Scope and evidence policy

This record preserves the mathematically effective information produced by the
recent Lean–MLE / PCR-JUMP-LEAN rounds.  It does not promote any Experimental
Lean declaration into the official Certified Graph.

The source work remains isolated in draft experimental branches and pull
requests, principally:

```text
pcr-jump-integral-heredity-20260803
pcr-jump-reduced-normal-cone-20260803
PR #19  graded Frobenius heredity and actual centre ideals
PR #21  reduced normal-cone heredity and graph-centre certificates
```

At the time of this record, the latest exact-head clean-room builds and axiom
audits were still queued.  Accordingly the new declarations are classified as
`EXACTLY_DEFINED / PROOF_TERM_CANDIDATE / CI_PENDING`, not as kernel-certified.

## 2. Permanent negative results and corrected boundaries

### 2.1 Bare integral equivalence is too weak

The replacement

```text
X^q  ->  X
```

changes the marked singular condition if the mark is not divided.  The correct
scaled normalization is

```text
(g^q, q*m)  ->  (g, m).
```

For an arbitrary mark `m`, the candidate exact law is

```text
(g^q, m)  ->  (g, ceil(m/q)),
```

with a bounded exceptional debt

```text
delta = q * ceil(m/q) - m,
0 <= delta < q.
```

Thus the state language must retain grading, marks, differential data, and
boundary debt.  Equality of ungraded integral closures is not by itself a
sufficient hereditary state relation.

### 2.2 Reducedness is an essential hypothesis

In a nonreduced ring, a nonzero nilpotent `x` can satisfy `x^q = 0`.  Hence the
zero ideal, and more generally a nonreduced normal cone, may fail prime-power
root reflection.  The dual-number example is the minimal permanent no-go.

### 2.3 Regular quotient, regular immersion, permissibility, and nonidentity are
independent gates

The following implications are permanently forbidden without separate proofs:

```text
regular quotient  -> regular immersion
regular centre    -> marked permissibility
permissibility    -> nonidentity blowup
active containment -> passive Tor safety
```

Principal Cartier root ideals may be permissible while their blowup is an
identity.  Hybrid higher-codimension centres or terminal boundary enrollment
must be used instead.

## 3. New unifying object: Frobenius-normal centre filtration

For a characteristic index `p` and an ideal `I`, define

```text
ReflectsFrobeniusPowers p I :=
  forall e m x,
    x^(p^e) in I^((p^e)*m) -> x in I^m.
```

The reverse implication is automatic for every ideal.  Hence this property is
exactly the missing root-reflection content of scaled Frobenius normalization.

The current candidate proof architecture derives it from the normal cone:

```text
nonzero initial class in I^r/I^(r+1)
  -> nonzero p^e-th power in I^(p^e*r)/I^(p^e*r+1)
  -> one-layer power reflection
  -> full I-adic Frobenius reflection.
```

An abstract `ReducedNormalConePowerModel` now externalizes the exact structure
required from a future associated-graded or quasi-regular theorem: injective
encodings of all normal-cone layers into a reduced graded carrier, compatible
with prime-power operations.

## 4. Sharp local coordinate and graph models

### 4.1 Coordinate centres

For a positive-dimensional coordinate centre

```text
I = (Z_i)
```

in a polynomial ring over a passive coefficient ring `R`, the normal variables
form the outer polynomial layer.  The exact ideal-power criterion identifies
membership in `I^m` with a lower bound on total normal degree.

The candidate theorem is sharp:

```text
I reflects prime-power roots
  iff
R is reduced.
```

### 4.2 Polynomial graph centres

For a tuple `h_i in R`, the actual graph ideal

```text
I_h = (Z_i - h_i)
```

is carried to `(Z_i)` by graph translation.  The candidate sharp theorem is
again

```text
I_h reflects prime-power roots
  iff
R is reduced.
```

This extends the local model from linear centres to nonlinear polynomial graph
centres.

### 4.3 Exact graph quotient and actual-centre data

Graph evaluation `Z_i |-> h_i` has kernel exactly `I_h`.  Consequently:

```text
R[Z_i] / I_h  ~=  R.
```

The local graph centre therefore has an explicit package consisting of:

```text
actual ideal
properness over a nontrivial base
finite generation for finite normal rank
exact quotient equivalence
reduced quotient when R is reduced
regular quotient when R is regular.
```

### 4.4 Explicit conormal bases

For finite normal rank, candidate Lean constructions identify

```text
(Z_i)/(Z_i)^2              ~= R^iota
(Z_i-h_i)/(Z_i-h_i)^2      ~= R^iota.
```

The second equivalence is transported through graph translation.  These are the
local free-conormal components required for a regular-immersion certificate.
They remain Experimental until clean-room verification.

## 5. Faithfully flat descent layer

The current algebraic descent layer separates several logically distinct
claims.

### 5.1 Already compiled as candidate theorems

Under a faithfully flat algebra `A -> B`:

```text
(I B) cap A = I;
properness of a graph-model ideal descends;
finite generation of I descends from finite generation of I B;
reducedness of B/(I B) descends to A/I;
Frobenius-normality of I B descends to I.
```

The natural quotient map

```text
A/I -> B/(I B)
```

is explicitly constructed and proved injective from faithful flatness.

### 5.2 Conormal finiteness descent

A new isolated candidate theorem records the exact module-theoretic statement:

```text
if B tensor_A (I/I^2) is finite over B,
then I/I^2 is finite over A.
```

More generally, any linear equivalence of the base-changed conormal with a
finite `B`-module gives finiteness of the original conormal.

This closes only finite generation.  Descent of finite projectivity or local
freeness, and the scheme-level identification of the tensor-base-changed
conormal with the conormal of the extended ideal, remain separate bridges.

## 6. Current highest-posterior local-to-global bridge

The most likely correct regular-centre heredity theorem has now been compressed
to the following form.

### Graph-atlas heredity conjecture

Let `W` be smooth over a perfect field and let `C -> W` be an actual regular
closed immersion compatible with the current boundary.  There should exist a
finite surjective etale/fpqc atlas on which the pair `(W,C)` is represented by a
polynomial graph ideal

```text
(Z_i - h_i)
```

over a reduced regular coefficient ring, with all overlap transitions carrying
explicit finite generator-change certificates.

From such an atlas, the current algebraic layer would give:

```text
actual coherent centre ideal
properness and finite type
regular reduced quotient
finite locally free conormal after completing descent
Frobenius-normal I-adic filtration
exact scaled and ceiling-mark compression
compatibility with active marked-power containment.
```

The atlas-existence and descent theorem is not yet proved in Lean and is not
silently assumed.

## 7. Current dependency architecture

The updated maximum-likelihood proof chain is:

```text
intrinsic finite Frobenius--Hasse packet
-> graded Frobenius normalization with mark scaling
-> bounded exceptional-debt enrollment
-> Fitting/conormal/hybrid centre synthesis
-> finite etale/fpqc polynomial-graph atlas
-> actual regular centre and free conormal descent
-> Frobenius-normal normal-cone filtration
-> joint active/passive/boundary legality
-> all-chart controlled-transform heredity with no reset
-> causal source/birth ledger
-> Noetherian + multiset + degree + debt termination
-> finite global serialization
-> principalization and resolution.
```

## 8. Exact remaining gaps after this round

1. Obtain clean-room Lean builds and `#print axioms` audits for the exact
   experimental heads.
2. Construct a finite etale/fpqc graph atlas for an arbitrary actual regular
   centre in the smooth ambient scheme.
3. Prove effective overlap descent of the actual graph ideals and their finite
   conormal frames.
4. Prove finite projective/local-free conormal descent, not merely finiteness.
5. Extend principal marked heredity to finite nonprincipal differential Rees
   presentations and Hasse saturation.
6. Prove joint active-owner permissibility and passive Tor/normal-flat safety.
7. Prove SNC boundary compatibility and preserve bounded exceptional debt on
   every chart and overlap.
8. Prove controlled-transform and packet reconstruction after cleaning,
   saturation, normalization, and integral closure without history reset.
9. Realize geometric birth supports, immediate-defect carriers, and the finite
   global serialization theorem.
10. Compile principalization, embedded resolution, and nonembedded resolution.

## 9. Baseline truth statement

```text
REDUCED_NORMAL_CONE_ARCHITECTURE_RECORDED      = true
GRAPH_CENTRE_LOCAL_CERTIFICATE_RECORDED        = true
FAITHFULLY_FLAT_DESCENT_FRONTIER_RECORDED      = true
CONORMAL_FINITE_DESCENT_CANDIDATE_RECORDED     = true

NEW_EXPERIMENTAL_THEOREMS_BASELINE_CERTIFIED   = false
CERTIFIED_GRAPH_CHANGED                        = false
GENERAL_GEOMETRIC_REALIZATION                  = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION     = false
FORMAL_GLOBAL_STATUS                           = OPEN_GAP
```

No result in this record may be cited as kernel-certified without an exact
commit-matched clean-room build, complete axiom audit, and an explicit theorem
promotion instruction.

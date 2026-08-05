# MLEL-X052 / PIF-MPD-DPE-FINAL

## Projection-Invariance Firewall, Minimal Projection Defect, and Defectless-Projection Equivalence
## 投影不变量防火墙、最小投影缺陷与无缺陷投影等价

**Parents:** MLEL-X051 / IDP-CFR-PZD-FINAL; MLEL-X050 / BGI-FSP-NCE-FINAL; MLEL-X045--X049 recurrence, descent, and wild-shadow lines.  
**Date:** 2026-08-05  
**Class:** fixed-valued-field invariance theorem + birational no-go + projection-minimal defect diagnostic + restricted positive chambers + exact final frontier.  
**Global status:** `OPEN_GAP`.

---

## 0. Executive verdict

X051 correctly identified the primitive zero-distance Artin--Schreier carrier and correctly rejected coarsening as birational progress. Its proposed primitive zero-distance geometric escape theorem, however, still asked ordinary blowups of fixed models to make a fixed valued-field extension defectless, dependent, or different in distance type. That is impossible: these are invariants of the valued-field extension, not of its models.

X052 therefore makes a final structural correction.

1. For a fixed finite valued-field extension `(F|E,v)`, every birational modification of models leaves the ramification index, residue degree, henselian local degree, defect, Artin--Schreier distance, best-generator ideal, and dependent/independent type unchanged.
2. Consequently, ordinary blowups cannot create a best generator for a fixed defective Artin--Schreier extension, cannot turn independent defect into dependent defect, and cannot change the primitive zero-distance cut. They can only change finite coherent contractions and model-theoretic presentation data.
3. Once the finite coherent state has stabilized, a fixed projection offers no further geometric escape. The X051 `PZGE` target is therefore superseded as an ordinary-blowup statement.
4. The only operation capable of changing the defect token is a change of projection, i.e. a change of the rational subfield over which the function field is finite.
5. For a valued function field `(F|k,v)` of dimension `d`, define the local projection-defect exponent of a separating transcendence basis `t=(t_1,...,t_d)` by

   ```text
   [F^h:k(t)^h] = e_t(v) f_t(v) p^(epsilon_t(v)).
   ```

   The minimal projection defect

   ```text
   epsilon_pr(F,v/k)=min_t epsilon_t(v)
   ```

   is a birational invariant of `(F,v)`.
6. Local uniformization implies `epsilon_pr=0`: at a regular centre one has etale local coordinates, hence a finite etale local projection and a defectless henselian branch.
7. The Abhyankar chamber has `epsilon_pr=0` by the Generalized Stability Theorem and elimination of ramification. An immediate transcendence-degree-one extension over a separably tame base has `epsilon_pr=0` by henselian rationality.
8. In the candidate resolution architecture, `epsilon_pr=0` is also sufficient: a defectless finite projection gives multiplicity reduction along the valuation, while X033--X050 supply the finite-state centre, transform, ancestry, and globalization interfaces conditionally required to iterate the reduction.
9. Hence the remaining theorem is not a small geometric escape lemma. It is the valuation-theoretic assertion

   ```text
   DEFECTLESS PROJECTION EXISTENCE (DPE):
   epsilon_pr(F,v/k)=0 for every valued function field over a perfect field.
   ```

   In the present architecture DPE is equivalent to local uniformization, up to the already isolated coherent and lower-dimensional interfaces.

General arbitrary-dimensional positive-characteristic resolution is not established.

---

## 1. Fixed-projection invariance

Let `E subset F` be a finite separable field extension. Fix a valuation `v` on `F` and let `w=v|E`. Let `R` and `S` be any models of `E` and `F` dominated by `w` and `v`, and let `R'`, `S'` be arbitrary birational models dominated by the same valuations.

### Theorem 1.1 -- fixed-projection invariance

The following data are unchanged by replacing `(R,S)` with `(R',S')`:

```text
the valued fields (E,w) and (F,v);
the henselizations E^h and F^h inside a fixed algebraic closure;
the local henselian degree [F^h:E^h];
the ramification index e(v/w);
the residue degree f(v/w);
the defect exponent epsilon(v/w);
the prime-degree tame/wild tower type;
for an Artin--Schreier layer, its distance cut;
its best-generator ideal in the valuation ring;
its dependent or independent defect class.
```

### Proof

A birational model changes neither function field nor valuation. Henselization is a functor of the valued field, and the local degree, ramification index, residue degree, and defect are defined from the valued-field extension. Artin--Schreier distance and the best-generator ideal are defined from all right-hand sides defining the same extension inside the fixed valued field. The dependent/independent classification is expressed by the idempotence type of this distance. None of these definitions mentions a model.

### Corollary 1.2 -- fixed-projection blowup firewall

No finite sequence of ordinary blowups of models can, for a fixed extension `(F|E,v)`, do any of the following:

```text
make a defective extension defectless;
produce a best Artin--Schreier generator;
turn independent defect into dependent defect;
change the Artin--Schreier distance cut;
change the associated convex subgroup or the primitive 0^- type.
```

A blowup may change contractions of valuation ideals, coefficient ideals, multiplicity, or the finite event-visible state. It cannot change the fixed valued-field defect token.

---

## 2. Refutation of the fixed-projection PZGE target

The X051 primitive zero-distance target allowed five exits. For a fixed projection, the exits “best generator”, “dependent defect”, and “change of cut/pro-isomorphism class” are excluded by Theorem 1.1. A model invariant such as multiplicity or support dimension may decrease, but after the X050 finite-state stabilization this does not remove the unchanged primitive defect token. A newly visible coherent contraction can occur only finitely many times by the ancestral Noetherian ACC.

### Theorem 2.1 -- stabilized fixed-projection no-go

Assume a primitive independent zero-distance Artin--Schreier token has stable finite coherent state in the sense of X050. Then no sequence of ordinary blowups which retains the same rational subfield `E` can eliminate the token.

### Proof

All coherent contractions and event-visible shadows stabilize by hypothesis and by the X045/X050 ancestral ACC. The only remaining data are the fixed valued-field extension and its primitive distance prime. By Theorem 1.1 these data are invariant under every further birational model. Thus the token persists.

### Consequence 2.2

`PZGE` is not a valid ordinary-blowup theorem for a fixed projection. Any valid escape theorem must contain an actual change of rational subfield or finite projection.

---

## 3. Admissible projections and minimal projection defect

Let `k` be perfect of characteristic `p>0`, let `F|k` be a finitely generated field extension of transcendence degree `d`, and let `v` be a valuation of `F` trivial on `k`.

### Definition 3.1 -- admissible projection

An admissible projection is a separating transcendence basis

```text
t=(t_1,...,t_d) subset F
```

such that `F|k(t)` is finite separable. Since `k` is perfect, admissible projections exist.

Fix the extension of `v` from `k(t)` to `F`. Define `epsilon_t(v)` by

```text
[F^h:k(t)^h] = e_t(v) f_t(v) p^(epsilon_t(v)).
```

### Definition 3.2 -- minimal projection defect

Set

```text
epsilon_pr(F,v/k)=min_t epsilon_t(v),
D_pr(F,v/k)=p^(epsilon_pr(F,v/k)),
```

where `t` runs through all admissible projections.

The minimum exists because the set is nonempty and consists of nonnegative integers.

### Proposition 3.3 -- birational invariance

`epsilon_pr(F,v/k)` depends only on the valued function field `(F|k,v)`. It is unchanged by every birational modification of every model.

### Proof

The collection of admissible rational subfields of `F` and each henselian defect exponent are field-theoretic. A model changes neither.

### Warning 3.4

The defect of the currently chosen projection may decrease after switching projections, but it can decrease only until `epsilon_pr` is reached. The number of attempted projections, the index of a projection in a finite list, and a switch from one minimizing projection to another are not strict ranks.

---

## 4. Chambers in which the minimum is zero

### Theorem 4.1 -- local uniformization implies defectless projection

If `v` admits local uniformization on a regular finite-type `k`-model, then

```text
epsilon_pr(F,v/k)=0.
```

### Proof

Let `x` be the regular centre of `v`. Since `k` is perfect, the model is smooth at `x`. Choose etale local coordinates `t_1,...,t_d` at `x`. After shrinking and applying Zariski's Main Theorem to the quasi-finite etale morphism, the component containing `x` is finite etale over an open of affine `d`-space. The corresponding extension of henselian local fields is unramified and hence defectless. Therefore `epsilon_t(v)=0`.

### Theorem 4.2 -- Abhyankar chamber

Assume `(F|k,v)` has no transcendence defect and the standard residue separability hypotheses. Then

```text
epsilon_pr(F,v/k)=0.
```

### Proof

Choose a standard valuation transcendence basis. The Generalized Stability Theorem makes the valued rational function field defectless, and elimination of ramification identifies the finite henselian extension with an unramified extension. Hence its defect exponent is zero.

### Theorem 4.3 -- immediate transcendence-degree-one chamber

Let `(K,v)` be separably tame and let `(F|K,v)` be an immediate separable function field of transcendence degree one. Then there exists `x in F` such that

```text
F^h=K(x)^h.
```

In particular the corresponding projection has local degree one and defect exponent zero.

### Proof

This is the henselian rationality theorem for immediate transcendence-degree-one function fields over a separably tame base.

---

## 5. Conditional converse through multiplicity reduction

Cutkosky--Mourtada prove that, for a hypersurface singularity along a valuation, a defectless finite linear projection permits reduction of multiplicity. The coherent part of the present programme supplies, conditionally, the simultaneous centre legality, all-chart transform, source conservation, and lower-dimensional preparation needed to iterate that reduction.

### Theorem 5.1 -- conditional projection criterion for local uniformization

Assume the X033--X050 finite-state and lower-dimensional theorems. If

```text
epsilon_pr(F,v/k)=0,
```

then `v` admits local uniformization by a finite sequence of ordinary blowups in regular centres.

### Proof

Choose an admissible projection of defect exponent zero. Present the local model as a hypersurface over the regular projection base. Apply defectless-projection multiplicity reduction. Every coherent auxiliary obstruction created by the reduction is prepared by the full coloured centre theorem; the regular-flag and hereditary transform theorems reconstruct the successor state. Multiplicity is a positive integer and strictly decreases until the hypersurface is regular. The boundary is then made SNC by the toroidal centre block.

### Corollary 5.2 -- exact frontier equivalence inside the programme

Under the same coherent hypotheses, local uniformization for all valuations is equivalent to

```text
DPE: epsilon_pr(F,v/k)=0 for every valued function field (F|k,v).
```

The forward implication is Theorem 4.1; the reverse implication is Theorem 5.1.

---

## 6. Projection-minimal defect core

### Definition 6.1

A projection-minimal defect core is a valued function field with

```text
epsilon_pr(F,v/k)>0,
```

together with an admissible projection attaining the minimum and a primitive independent degree-`p` layer in its tame--wild decomposition.

### Proposition 6.2

Neither birational modifications of models nor further changes among minimizing projections lower the projection defect. Every finite-state coherent shadow may still be prepared, but the projection-minimal token remains.

### Proof

Birational invariance is Proposition 3.3. Minimality excludes a projection of smaller exponent. Finite-state preparation does not change the valued field extension.

### Consequence 6.3

The remaining theorem is not an ordinal refinement of PZGE. It is the nonexistence of projection-minimal defect cores:

> **Defectless Projection Existence (DPE).** Every valued function field over a perfect field admits an admissible projection with defectless henselian branch.

This theorem is known in the Abhyankar and tame-base one-dimensional chambers above. In general it is open and, within the current architecture, equivalent to local uniformization.

---

## 7. Candidate-graph contraction

### Closed or reduced to standard inputs after X052

```text
fixed-projection invariance of e, f, defect, distance and defect type;
no-go for fixed-projection PZGE after finite-state stabilization;
existence and birational invariance of minimal projection defect;
local uniformization => defectless projection;
Abhyankar valuations => minimal projection defect zero;
immediate trdeg-one over separably tame base => henselian-rational projection;
defectless projection => multiplicity reduction;
conditional equivalence DPE <-> local uniformization in the programme.
```

### Superseded routes

```text
coarsening height as a blowup rank;
ordinary blowups making a fixed defect extension defectless;
ordinary blowups changing independent to dependent defect;
ordinary blowups changing a fixed Artin--Schreier distance cut;
finite reprojection count as a well-founded rank;
PZGE as a fixed-projection ordinary-centre theorem.
```

### Single remaining load-bearing theorem

```text
DEFECTLESS PROJECTION EXISTENCE (DPE)
-> defectless-projection multiplicity reduction
-> local uniformization
-> coherent/global source-causal termination
-> finite Zariski/etale serialization
-> principalization and functorial resolution.
```

---

## 8. Truth boundary

```text
FIXED_PROJECTION_INVARIANCE                    = closed
PZGE_FIXED_PROJECTION                          = refuted / ill-typed
MINIMAL_PROJECTION_DEFECT                       = closed definition and invariance
LOCAL_UNIFORMIZATION_IMPLIES_DPE                = closed
DPE_FOR_ABHYANKAR_CHAMBER                       = literature-established
DPE_FOR_TAME_BASE_IMMEDIATE_TRDEG_ONE            = literature-established
DPE_IMPLIES_LOCAL_UNIFORMIZATION_IN_PROGRAMME    = conditional on coherent architecture
DPE_IN_GENERAL                                  = open
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION       = not established
```

X052 removes the last false appearance that the remaining valuation obstruction could be discharged by one more model-theoretic blowup invariant. The exact unresolved theorem is the existence of a defectless projection; within the present proof architecture this is local uniformization itself.

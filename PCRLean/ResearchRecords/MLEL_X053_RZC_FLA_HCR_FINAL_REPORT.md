# MLEL-X053 / RZC-FLA-HCR-FINAL

## Riemann--Zariski Compactness, Finite Local-Word Atlases, and Hereditary Common Refinement
## Riemann--Zariski 紧致性、有限局部中心词图册与遗传共同细化

**Parents:** MLEL-X052 / PIF-MPD-DPE-FINAL; MLEL-X045 / AEF-NUB-CRX-FINAL; MLEL-X040--X044 common-trace, actual-centre, transform, and source-word line.  
**Date:** 2026-08-05  
**Class:** standard Riemann--Zariski compactness + finite admissible common refinement + conditional regular hereditary realization.  
**Global status:** `OPEN_GAP`.

---

## 0. Executive verdict

X052 separated pointwise, uniform, and functorial defectless-projection existence. X053 proves that the first two should not be treated as independent valuation-theoretic hypotheses.

A defectless projection at one valuation gives, through the X052 multiplicity-reduction and coherent-centre machinery, one finite local centre word. The locus of valuations uniformized by that same finite word is an open subset of the Riemann--Zariski space. Quasi-compactness therefore extracts finitely many local words from pointwise existence.

A finite family of source words has a common admissible blowup. That common blowup can be singular, so compactness alone does not prove resolution. The missing patching step is precisely the hereditary regular common-refinement theorem developed in X040--X044: the finite common modification ideal has support of smaller carrier dimension; principalization with the complete active, passive, logarithmic, source, and terminal portfolio realizes it by ordinary blowups in regular jointly legal centres and preserves every source terminal open.

Consequently, conditional on the coherent centre and hereditary common-refinement theorems already isolated in the programme,

```text
pointwise defectless projection existence
    -> pointwise local words
    -> finite Riemann--Zariski local-word atlas
    -> one finite hereditary regular common refinement
    -> global embedded resolution by ordinary blowups.
```

No separate finite-constructible `Uniform DPE` assumption is needed for existence. What remains separate is functorial canonicalization: an arbitrary finite subcover of the valuation space is not preserved by smooth pullback. Smooth-functorial resolution requires a canonical/functorial projection atlas or an equivalent intrinsic serialization theorem.

The exact valuation frontier after X053 is therefore **Pointwise Defectless Projection Existence (PDPE)**. Within the current architecture it is equivalent to pointwise local uniformization. General PDPE, functorial canonicalization, and arbitrary-dimensional positive-characteristic resolution remain open.

---

## 1. The valuation space of the current embedded pair

Let `X` be a reduced finite-type scheme with irreducible components `X_a` and function fields `K_a`. Define

```text
RZ(X)=disjointUnion_a RZ(K_a/X_a),
```

where `RZ(K_a/X_a)` is the set of valuation rings of `K_a` having a centre on `X_a`, with the Zariski topology. It is quasi-compact; a finite disjoint union is quasi-compact.

For every proper birational model `Y->X`, each valuation in `RZ(X)` has a unique centre on `Y`. Denote the centre map by

```text
c_Y:RZ(X)->Y.
```

For an open subset `V subset Y`, the set `c_Y^(-1)(V)` is open in `RZ(X)`.

---

## 2. Terminal basins of finite centre words

Let

```text
w:(W_w,E_w,X_w)->(W,E,X)
```

be a finite word of ordinary blowups in regular jointly legal centres. Let `T_w subset X_w` be the largest open on which `X_w` is regular and has SNC with the total boundary and on which every declared owner/passive certificate is terminal.

### Definition 2.1 -- terminal basin

Define

```text
Omega(w)=c_(X_w)^(-1)(T_w) subset RZ(X).
```

### Proposition 2.2 -- basin openness

`Omega(w)` is open. Every valuation in `Omega(w)` is uniformized by the same word `w`.

### Proof

The centre map is continuous, so the inverse image of the open terminal locus is open. A valuation in the inverse image has its final centre in the regular/SNC terminal locus; the word therefore uniformizes that valuation with all declared boundary and owner conditions.

### Corollary 2.3 -- pointwise words form an open cover

If every valuation in `RZ(X)` admits a finite legal local word, then the terminal basins of these words form an open cover of `RZ(X)`.

---

## 3. Finite local-word atlas

### Theorem 3.1 -- Riemann--Zariski finite-atlas theorem

Assume every valuation centred on `X` admits a finite ordinary jointly legal local word. Then there exist finitely many words

```text
w_1,...,w_m
```

such that

```text
RZ(X)=Omega(w_1) union ... union Omega(w_m).
```

### Proof

Apply quasi-compactness of `RZ(X)` to the open cover of Corollary 2.3.

### Application to pointwise DPE

Under the X052 defectless-projection multiplicity-reduction theorem and the lower-dimensional coherent-centre induction, pointwise DPE gives a finite local word for each valuation. Hence pointwise DPE gives a finite local-word atlas.

### Boundary

The finite subcover is not canonical. This theorem gives existence, not smooth-functorial selection.

---

## 4. Common admissible domination

Let `U subset W` be the largest open on which the initial pair is already terminal. Each finite local word is a `U`-admissible modification and, by centre-exact compression, a `U`-admissible blowup in one coherent ideal.

### Theorem 4.1 -- finite common admissible blowup

For finitely many source words `w_i`, there exists one `U`-admissible blowup

```text
B->W
```

which factors through the composite modification of every `w_i`. The morphisms from `B` to the source models are again `U`-admissible blowups.

### Proof

Use the common-refinement theorem for finitely many admissible blowups, equivalently the blowup of the product of their centre-exact modification ideals.

### Warning 4.2 -- common domination is not regularity

The common blowup need not be regular. For example, the blowup of `A^2` in `(x^2,y^3)` has a chart

```text
k[x,y,u]/(y^3-x^2u),
```

which is singular at the origin. Thus Riemann--Zariski compactness plus an arbitrary common blowup does not by itself prove resolution.

---

## 5. Hereditary regular common refinement

For each source word retain:

```text
its ordered centres;
its centre-exact composite modification ideal;
its final strict-transform portfolio;
its regular/SNC terminal open;
its owner, source, boundary, contact, and exceptional lineage.
```

The finite common modification is an isomorphism at every generic point of every component of `X`; its support therefore has carrier dimension strictly smaller than `dim X`.

### Theorem 5.1 -- hereditary regular common-refinement theorem

Assume the full-portfolio principalization theorem in smaller carrier dimension, the X042--X043 exactified transform and all-chart reentry theorem, and the X044 source-closed actual-centre theorem. For a finite local-word atlas there exists one finite word

```text
r:(W',E',X')->(W,E,X)
```

of ordinary blowups in regular jointly legal centres such that:

1. `r` factors through every source word `w_i`;
2. over the inverse image of each `T_(w_i)`, all further centres are disjoint from the terminal pair or meet it with the declared SNC/normal-flatness certificates;
3. the final strict transform over that inverse image remains regular and SNC;
4. source words, strict transforms, and terminal certificates agree on all charts and overlaps;
5. the construction is an isomorphism over the initially terminal open `U`.

### Proof

Take a common admissible modification and a coherent ideal representing it. Its support avoids the generic points of the current carriers, hence lies in smaller carrier dimension. Enrol the ideal together with all source terminal certificates in the complete coloured portfolio. Lower-dimensional full-portfolio principalization realizes the modification by ordinary blowups in regular jointly legal centres. The universal property gives factorization through every source modification. X042 exactification and X043 regular-flag comparison identify the actual successor normal systems; source-word realization identifies the final strict transforms. Since the terminal strict transform and total boundary are part of the passive/logarithmic portfolio, every later centre is either disjoint from them or has normal crossings with them. Blowup in such a centre preserves regularity and SNC. Induction over the finite common word proves the assertions.

### Truth boundary

The theorem is conditional on the X040--X044 regular common-refinement architecture. It is not a consequence of quasi-compactness alone and must not be cited as a standard theorem of valuation theory.

---

## 6. Pointwise DPE gives global existence

### Theorem 6.1 -- compactness compilation of pointwise DPE

Assume:

1. pointwise defectless projection existence for every valuation of every relevant valued function field;
2. defectless-projection multiplicity reduction and the lower-dimensional coherent-centre induction;
3. the hereditary regular common-refinement theorem.

Then every reduced finite-type embedded pair over a perfect field admits a finite embedded resolution by ordinary blowups in regular jointly legal centres.

### Proof

Pointwise DPE gives a finite local word at every valuation. Theorem 3.1 extracts a finite local-word atlas and Theorem 5.1 gives one regular hereditary common refinement `W'`.

Suppose a point `x' in X'` were nonregular or failed SNC with the total boundary. Choose an irreducible component through `x'` and a valuation of its function field dominating the corresponding local domain. This valuation has centre `x'` on `X'`. It belongs to some basin `Omega(w_i)`. Since `W'` factors through the final source model of `w_i`, the image of `x'` is the centre of the valuation on that source model and lies in `T_(w_i)`. By hereditary preservation of the terminal certificate, `x'` is regular and SNC, a contradiction. Hence the final pair is resolved everywhere.

### Corollary 6.2 -- no independent uniformity hypothesis for existence

Within the stated architecture, pointwise DPE already implies a finite global resolution. The finite-cover part of X052 `Uniform DPE` follows from Riemann--Zariski quasi-compactness and is not a separate valuation-theoretic conjecture.

---

## 7. Functoriality boundary

An arbitrary finite subcover of `RZ(X)` is not canonical and need not pull back to the chosen finite subcover of a smooth cover. Therefore Theorem 6.1 is an existence theorem.

### Hypothesis 7.1 -- functorial projection-atlas selection

There is an intrinsic finite local-word atlas, or an equivalent intrinsic common source portfolio, which:

```text
is stable under open restriction;
commutes with smooth and etale pullback;
commutes with extension of the perfect ground field;
retains source and boundary labels;
and yields the same hereditary common refinement after deletion of empty centres.
```

Under this additional hypothesis, the X042--X044 functorial common-refinement theorem gives smooth-functorial principalization and resolution.

### Correction to X052

The X052 hypothesis should be separated as follows:

```text
PDPE: pointwise defectless projection existence -- valuation frontier;
RZC-HCR: finite compilation -- supplied by X053 conditionally;
FPAS: functorial projection-atlas selection -- separate canonicalization frontier.
```

---

## 8. Candidate-graph contraction

### Closed or reduced to standard inputs

```text
terminal basin openness;
Riemann--Zariski finite subcover;
finite common admissible blowup;
every point on a final model is dominated by a centred valuation;
pointwise local words -> finite local-word atlas.
```

### Conditionally closed in the present architecture

```text
regular hereditary common refinement;
pointwise DPE -> finite global embedded resolution;
pointwise DPE -> principalization and intrinsic resolution existence.
```

### Remaining load-bearing chain

```text
Pointwise Defectless Projection Existence (PDPE)
-> local multiplicity reduction and local uniformization
-> X053 finite atlas and hereditary common refinement
-> finite global resolution existence.
```

For smooth-functorial resolution add:

```text
Functorial Projection-Atlas Selection (FPAS)
-> functorial common refinement
-> smooth-functorial principalization and resolution.
```

---

## 9. Truth boundary

```text
RZ_TERMINAL_BASIN_OPENNESS                         = standard closed
RZ_FINITE_LOCAL_WORD_ATLAS                         = standard closed
FINITE_COMMON_ADMISSIBLE_BLOWUP                    = standard closed
HEREDITARY_REGULAR_COMMON_REFINEMENT               = conditional on X040-X044
POINTWISE_DPE_IMPLIES_GLOBAL_EXISTENCE              = conditional theorem closed
SEPARATE_UNIFORM_DPE_FOR_EXISTENCE                  = superseded
POINTWISE_DPE_GENERAL                               = open
FUNCTORIAL_PROJECTION_ATLAS_SELECTION               = open
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION          = not established
```

X053 removes one unnecessary layer from the final hypothesis without pretending to solve the valuation problem. The exact existence frontier is pointwise DPE; the exact functoriality frontier is canonical projection-atlas selection.

# MLEL-X051 / FPR-R1C-HRR-FINAL

## Fixed-Projection Rigidity, the Rank-One Defect Core, and Henselian-Rational Reprojection
## 固定投影刚性、秩一缺陷核心与 Hensel 有理重投影

**Parents:** MLEL-X050 / BGI-FSP-NCE-FINAL; MLEL-X049 / FNI-BGE-NRW-FINAL; MLEL-X047 / WAD-GCD-UWP-FINAL; MLEL-X045 / AEF-NUB-CRX-FINAL; the local-uniformization and valuation-theory line.  
**Date:** 2026-08-05  
**Class:** exact no-go for fixed projections + external rank-one reduction + transcendence-defect firewall + finite-state descent in the henselian-rational chamber + one final uniform reprojection theorem.  
**Global status:** `OPEN_GAP`.

---

## 0. Executive verdict

X050 identified the genuine class-V carrier as the non-finitely-generated best-generator ideal, or equivalently the nonattained Artin--Schreier improvement cut, and froze the research to Uniform Nonattained-Cut Escape. X051 sharpens that frontier in four ways.

1. **Fixed-projection rigidity.** For a fixed valued-field extension `(L/K,v)`, ordinary blowups and all birational changes of finite models leave the extension, valuation, ramification index, residue degree, defect, best-generator ideal, Artin--Schreier distance, and dependent/independent type unchanged. Hence no sequence of ordinary blowups can make a best generator appear or convert an independent defect extension into a dependent one without changing the projection/field tower.

2. **Reduction to rank one.** Novacoski--Spivakovsky prove that local uniformization, including the relevant embedded variants, reduces to rank-one valuations. In the present programme the higher-rank class-V packet is therefore decomposed into its rank-one composition factors, with all finite coloured data and ancestry transported through the composition.

3. **The rank-one core is primitive.** Kuhlmann's classification says that an independent Artin--Schreier defect extension has idempotent distance. In rank one there is no nonzero proper convex subgroup, so the only proper idempotent distance of an immediate defect layer is `0^-`. Thus the remaining independent rank-one layer is already the primitive zero-distance case; isolated-subgroup height cannot serve as a decreasing model-stage rank.

4. **Henselian-rational reprojection.** If a rank-one valued function field `(F/K,v)` has transcendence degree one, `vF/vK` torsion and `Fv/Kv` algebraic, Kuhlmann proves that after a finite extension `L/K`, `(F.L/L,v)` is henselian rational. A finite event-visible state in a henselian-rational chamber descends to a finite etale neighbourhood of a rational one-variable model. Lower-dimensional preparation, followed by X047 Cech--Rees descent and X049 Norm--Rees/balanced-gap descent, gives an ordinary regular jointly legal word on the original model.

These results close the descent once a finite henselian-rational reprojection certificate is given. The final open theorem is now **Uniform Rank-One Henselian Reprojection (URHR)**: construct, on a quasi-compact neighbourhood of every primitive rank-one independent-defect token, a finite portfolio of codimension-one valued subfields and finite base extensions satisfying the valuation-algebraic hypotheses, compatible with the complete finite state, and producing no equal-or-higher class-V birth.

Under URHR, class V exits by a finite ordinary centre tree. Combined with X045 coherent recurrence descent, the global source-causal multiset is well founded and the remaining globalization is formal. URHR is not proved in the current baseline; general arbitrary-dimensional positive-characteristic resolution remains open.

---

## 1. Fixed-projection rigidity

Let `K` be the function field of a finite-type integral model `X`, let `L/K` be a finite extension, and let `v` be a valuation of `L` with restriction to `K`. A birational modification changes the centre of `v`, but not the valued-field extension.

### Theorem 1.1 -- fixed-projection rigidity

For every sequence of ordinary blowups of finite models of `K`, followed by normalization in `L`, the following objects are unchanged:

```text
(L/K,v);
ramification index e and residue degree f;
defect d=[L^h:K^h]/(ef);
the Artin--Schreier best-generator ideal H_(L/K) in O_v;
the distance/improvement cut;
dependent or independent defect type;
the pro-isomorphism class of the approximation end.
```

### Proof

The function fields, the valuation, and the valued-field inclusion are unchanged by birational modification. The numerical ramification invariants and defect are invariants of the henselian valued-field extension. The best-generator ideal and distance are defined inside the fixed valuation ring from all Artin--Schreier representatives of the same extension. The dependent/independent classification is defined through the valued-field distance and its relation to purely inseparable extensions. None of these definitions uses a finite model.

### Corollary 1.2 -- no fixed-projection escape by blowup

If `(L/K,v)` is an independent Artin--Schreier defect extension, no finite word of ordinary blowups of models of `K` can, by itself,

```text
produce a best generator;
make H_(L/K) finitely generated;
make the extension defectless;
make the extension dependent;
strictly improve the distance cut.
```

Any valid escape must change the finite projection/field tower, lower an independent geometric coordinate, or expose a new coherent shadow used by the finite state.

---

## 2. Rank-one reduction

Novacoski--Spivakovsky prove that local uniformization for valuations centred on a chosen category of local domains follows from the rank-one case; they also establish the corresponding reductions for embedded and related versions.

### External Theorem 2.1 -- rank-one reduction

To prove local uniformization for all valuations centred on the local objects under consideration, it is enough to prove it for rank-one valuations in the same class.

### Programme interface

A valuation of finite rank is a composition of rank-one valuations. The complete finite coloured state is transported successively through the corresponding residue-field and quotient-value-group stages. The X042--X045 exactification and ancestry rules ensure that:

```text
centres remain actual coherent ideals;
owner/passive/boundary legality is rechecked at every stage;
source identities do not split or reset;
finite rank-one action trees compose in the prescribed valuation order.
```

### Conditional Corollary 2.2 -- class-V reduction to rank one

Assume the rank-one escape theorem is uniform for the complete finite state and stable under composition of valuations. Then every finite-rank class-V token admits a finite escape tree. No independent ordinal for the number of valuation-composition stages is required: the composition length is finite and the rank-one token order is used at each stage.

The project-specific stability under all owners and source labels is part of URHR below.

---

## 3. The transcendence-defect firewall

Let `(F/k,v)` be a valued function field over the perfect trivially valued field `k`. The Generalized Stability Theorem says that if equality holds in the Abhyankar inequality over a defectless base, then every finite extension of `F` is defectless.

### External Theorem 3.1 -- generalized stability

If `(K,v)` is defectless and `(F/K,v)` is a valued function field without transcendence defect, then `(F,v)` is defectless.

### Corollary 3.2 -- location of the genuine class-V frontier

A genuine independent-defect token over a perfect ground field can occur only at a valuation with positive transcendence defect. Abhyankar and quasi-monomial valuations lie in the defectless/monomial branch and do not contribute class V.

Thus the remaining valuation induction is on positive transcendence defect, not on a finite approximation index and not on the defect of a fixed projection.

---

## 4. The rank-one primitive distance

Let `(L/K,v)` be an independent immediate Artin--Schreier defect extension. Kuhlmann's classification gives

```text
dist(theta,K)=delta,
delta=p delta,
```

and every idempotent distance is of the form `H^-` for a convex subgroup `H` of the divisible hull of `vK`.

### Theorem 4.1 -- rank-one primitive core

If `v` has rank one, then

```text
dist(theta,K)=0^-;
H_(L/K)=m_v=m_v^2;
```

and the best-generator ideal is not finitely generated.

### Proof

A rank-one ordered group has no nonzero proper convex subgroup. The distance of an immediate defect extension is a proper cut below zero, so the subgroup appearing in `H^-` cannot be the whole divisible hull. Hence it is zero and the distance is `0^-`. The best-generator prime is therefore the maximal ideal of the valuation ring. The value group has no least positive element in the independent immediate case; consequently the maximal ideal is idempotent and nonprincipal. Since every finitely generated ideal of a valuation ring is principal, it is not finitely generated.

### Corollary 4.2 -- no isolated-subgroup countdown in rank one

Coarsening and isolated-subgroup height do not furnish progress in the rank-one core. A valid escape must use a reprojection/finite extension, lower a separate geometric coordinate, or obtain an effective coherent contraction.

---

## 5. Henselian-rational reprojection

Let `(F/K,v)` be a valued function field of transcendence degree one such that `vF/vK` is torsion and `Fv/Kv` is algebraic.

### External Theorem 5.1 -- henselian rationality after finite base extension

There exists a finite extension `L/K` such that `(F.L/L,v)` is henselian rational. Equivalently, for some `x in F.L`,

```text
(F.L)^h = L(x)^h.
```

This is Kuhlmann's Theorem 1.6. In the immediate case over a tame or separably tame base, no arbitrary finite extension is needed beyond the theorem's stated finite immediate refinement.

### Lemma 5.2 -- finite-state etale realization

Let a finite event-visible state be defined in `(F.L)^h=L(x)^h`. Then all coefficients, modules, ideals, finite Hasse operators, comparison maps, and source/boundary labels of that state are defined on one finite etale neighbourhood of a local model of `L(x)`.

### Proof

A henselization is a filtered colimit of etale neighbourhoods. The state uses finitely many elements, finitely presented modules, and finitely many maps and relations. All of them, together with the finitely many equalities expressing the state, descend to one stage of the filtered system.

### Theorem 5.3 -- finite-state escape in the henselian-rational chamber

Assume lower-dimensional full-portfolio preparation over the model of `L`, and suppose the finite extension `L/K` is retained with its complete X047 Cech--Rees and X049 Norm--Rees/descent-gap data. Then the finite event-visible state on `(F.L/L,v)` admits a finite ordinary upper word which prepares all active, passive, logarithmic, source, and transform data. After finitely many discrepancy and balanced-gap preparations, this word descends to a finite ordinary regular jointly legal word on the original model.

### Proof

Choose the finite etale neighbourhood of Lemma 5.2. Its base is a smooth one-variable extension of a lower-dimensional model after the latter has been prepared by induction. The finite coloured state is coherent there. Apply the X044 joint marked and monomial-face construction together with X042--X043 exactified transform to obtain a finite regular upper word. Etale descent is immediate. For the finite extension `L/K`, apply X047: a nonzero Cech--Rees discrepancy gives a coherent downstairs colour and is consumed by the X044 block; Noetherian ACC makes the discrepancy-purification finite, while zero discrepancy gives fpqc descent of the complete word. Divisorially unbalanced data are handled by the X049 base norm shadow; balanced descent gaps are exactified, flattened and killed. The resulting word is defined on the original model and is legal for the complete portfolio.

### Corollary 5.4 -- disappearance of the certified rank-one token

In the henselian-rational reprojection chamber, the current rank-one immediate algebraic defect token disappears: the henselized function field is rational over the new base, and all remaining finite obstructions are coherent packets already controlled by X044--X049.

This corollary concerns the certified reprojection chamber. It does not assert that every primitive token admits such a reprojection uniformly.

---

## 6. Uniform Rank-One Henselian Reprojection

The final theorem required by the present architecture is:

> **URHR.** Let a primitive rank-one independent Artin--Schreier token be represented on a quasi-compact valuation neighbourhood by its immutable ancestry and complete stable finite state. There exists a finite constructible cover of the neighbourhood and, on each member, a codimension-one valued subfield `K_i` and a finite extension `L_i/K_i` such that:
>
> 1. `trdeg(F/K_i)=1`, `vF/vK_i` is torsion, and `Fv/K_i v` is algebraic;
> 2. `(F.L_i/L_i,v)` is henselian rational;
> 3. the finite state, its source labels, and all comparison maps are represented on a finite common model and satisfy the hypotheses of Theorem 5.3;
> 4. the descended ordinary word eliminates the acted primitive token or lowers an earlier geometric/transcendence-defect coordinate;
> 5. no leaf creates an equal-or-higher class-V token with fresh ancestry.

Kuhlmann's theorem supplies item 2 after an appropriate valuation-algebraic codimension-one subfield is chosen. The missing work is the uniform, finite, source-compatible selection and its no-upward-birth theorem.

### Conditional Theorem 6.1 -- class-V elimination from URHR

Assume URHR. Every class-V token admits a finite ordinary regular jointly legal escape tree. Together with the X045 coherent token order, the full recurrent multiset strictly decreases.

### Proof

Use Novacoski--Spivakovsky to decompose higher-rank valuations into rank-one stages. Generalized stability removes every no-transcendence-defect stage. Each remaining primitive rank-one stage enters URHR and then Theorem 5.3. The token disappears or an earlier coordinate decreases. Source-compatible no-upward birth gives the Dershowitz--Manna replacement condition. The finite composition of rank-one stages preserves strict multiset descent.

---

## 7. Candidate-graph contraction

### Closed or reduced to standard theorems

```text
fixed-projection rigidity;
no fixed-projection best-generator improvement by blowup;
rank-one reduction for local uniformization;
Abhyankar/no-transcendence-defect valuations are defectless;
rank-one independent defect has primitive distance 0^-;
finite-state etale realization in a henselization;
finite-state preparation and descent once a henselian-rational certificate is given;
X050 best-generator ideal and noncoherence theorem;
X049 Norm--Rees/balanced-gap preparation;
X047 finite-flat Cech--Rees descent;
X045 coherent recurrent-class termination.
```

### Remaining chain

```text
Uniform Rank-One Henselian Reprojection (URHR)
-> rank-one class-V escape
-> higher-rank composition
-> strict full recurrence multiset
-> global source-causal termination
-> finite Zariski/etale serialization
-> principalization and functorial resolution.
```

---

## 8. Truth boundary

```text
FIXED_PROJECTION_RIGIDITY                          = closed
RANK_ONE_LOCAL_UNIFORMIZATION_REDUCTION            = external theorem
GENERALIZED_STABILITY_FIREWALL                      = external theorem
RANK_ONE_PRIMITIVE_DISTANCE                         = closed from classification
HENSELIAN_RATIONALITY_AFTER_FINITE_BASE_EXTENSION   = external theorem
FINITE_STATE_ESCAPE_GIVEN_REPROJECTION_CERTIFICATE  = conditional on X044--X049 and lower dimension
UNIFORM_RANK_ONE_HENSELIAN_REPROJECTION             = open
STRICT_CLASS_V_ORDINAL                              = open pending URHR
GLOBAL_TERMINATION_AND_GLOBALIZATION                = open
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION          = not established
```

X051 rules out the last model-stage pseudo-ranks, proves the full descent in the certified henselian-rational chamber, and reduces the valuation frontier to one uniform reprojection theorem. Further research is frozen to URHR.

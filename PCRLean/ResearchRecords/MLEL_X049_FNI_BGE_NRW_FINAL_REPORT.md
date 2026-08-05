# MLEL-X049 / FNI-BGE-NRW-FINAL

## Ferrand Norm Ideals, Balanced Descent-Gap Elimination, and Global Norm--Rees Wild Preparation
## Ferrand 范数理想、平衡下降间隙消除与全局 Norm--Rees 野准备

**Parents:** MLEL-X048 / FDI-RRF-NNW-FINAL; MLEL-X047 / WAD-GCD-UWP-FINAL; MLEL-X045 / AEF-NUB-CRX-FINAL; MLEL-X044 / COP-PCH-UCS-FINAL.  
**Date:** 2026-08-05  
**Class:** global norm construction + exactified balanced-gap flatification + toroidal-chamber wild preparation.  
**Global status:** `OPEN_GAP`.

---

## 0. Executive verdict

X048 isolated two distinct wild branches. A divisorially unbalanced upper ideal cannot descend after any ordinary base blowup, while a ramification-balanced ideal has a descent gap supported in codimension at least two. It also gave a local diagonal Norm--Newton construction but left its globalization and the balanced-gap descent step open.

X049 closes these two interfaces in the form needed by the current proof architecture.

1. For a finite locally free morphism `f:Y->X` of rank `n` and a coherent ideal `J subset O_Y`, Ferrand's norm functor gives a canonical coherent ideal

   ```text
   N_f(J)=image(Norm_f(J) -> Norm_f(O_Y)=O_X).
   ```

   It is functorial and compatible with flat base change. The map and its image/kernel/cokernel are retained under nonflat centre words.

2. In a diagonal toroidal chart `x_i=u_i^(e_i)`, the integral closure of `N_f(J)` is exactly the X048 Norm--Newton ideal. Hence the normalized base blowup of the global norm ideal has the same Newton fan as the normalized upper blowup of `J^n`.

3. The normalized Rees algebra

   ```text
   overline(Rees_X(N_f(J)))
   ```

   is a global, presentation-independent Norm--Rees shadow. It is finite on the excellent finite-type bases used in the programme. Any ordinary regular base word dominating this normalized blowup is a valid base-first realization of the local Newton modification.

4. If every codimension-one ramification residue vanishes, the lower and upper descent quotients

   ```text
   Q_- = J / I_-(J)O_Y,
   Q_+ = I_+(J)O_Y / J
   ```

   are supported in codimension at least two. Enrol both exact sequences, their Tor kernels, images, cokernels, multiplication maps, and source labels in the X042 exactified portfolio. A simultaneous admissible flatification makes the strict transforms of `Q_-` and `Q_+` flat while preserving the transformed sequences. Since they are generically zero on every component, flat-kill gives `Q_-'=Q_+'=0`. The transformed upper ideal is therefore the extension of one downstairs ideal.

5. This proves the balanced descent-gap step conditionally on the existing X044 regular-centre realization of the flatifying modification. The codimension-one firewall remains intact: the theorem cannot apply when the ramification residue is nonzero.

6. Combining the global norm ideal with balanced-gap elimination closes Ramification-Balanced Base-First Wild Preparation in the finite toroidal event-visible chamber. Divisorially unbalanced colours are handled by the base norm shadow; balanced residual colours become genuinely descended after lower-dimensional preparation.

The remaining single target is **Event-Visible Wild Toroidalization (EVWT)**: on a quasi-compact independent Artin--Schreier neighbourhood, produce a finite regular upper/common model on which the finite wild map is toroidal in every direction read by the complete state and the complete coloured packet is monomial. No new invariant or centre grammar is needed before that theorem is resolved.

General arbitrary-dimensional positive-characteristic resolution is not established.

---

## 1. The Ferrand norm ideal

Let `f:Y->X` be finite locally free of constant rank `n`. Ferrand's norm functor over schemes gives

```text
Norm_f: QCoh(Y) -> QCoh(X)
```

and is compatible with arbitrary base change. It sends quasi-coherent algebras to quasi-coherent algebras and satisfies

```text
Norm_f(O_Y)=O_X.
```

For a coherent ideal `J subset O_Y`, apply the norm functor to the inclusion `J->O_Y`.

### Definition 1.1 -- Ferrand norm ideal

```text
N_f(J)=image(Norm_f(J) -> O_X).
```

The ideal is coherent because the norm of a finite module is finite in the Noetherian finite-rank setting. Its source, target, kernel and cokernel are retained as part of the exactified state.

### Theorem 1.2 -- flat naturality

For every flat base change `g:X'->X`, with `Y'=Y x_X X'`,

```text
N_(f')(J O_(Y')) = N_f(J) O_(X').
```

### Proof

Ferrand's norm functor and its universal normic polynomial law commute with arbitrary base change. Under flat base change, formation of the image of the induced map commutes with pullback. Smooth and etale naturality follow immediately.

### Multiplicativity

If `J,K subset O_Y`, multiplication of normic laws gives

```text
N_f(J) N_f(K) subset N_f(JK).
```

Consequently the norm ideals of the powers of one ideal form a graded multiplicative system. For the actual modification it is enough to use the Rees algebra of `N_f(J)` and then normalize.

---

## 2. Toroidal identification with the Norm--Newton ideal

Work in a split diagonal toroidal chart

```text
A=k[x_1,...,x_r],
B=k[u_1,...,u_r],
x_i=u_i^(e_i),
n=product_i e_i.
```

Let `J` be the monomial ideal generated by `u^(alpha^(a))`.

### Theorem 2.1 -- toroidal norm-polyhedron theorem

The Newton polyhedron of the Ferrand norm ideal is

```text
NP(N_f(J)) = conv{(n/e_i) alpha_i^(a)} + R_>=0^r.
```

Equivalently,

```text
overline(N_f(J)) = NN_f(J)
```

with `NN_f(J)` as in X048, and

```text
overline(N_f(J) O_Y)=overline(J^n).
```

### Proof

The norm of the monomial `u^alpha` is a unit times

```text
product_i x_i^((n/e_i)alpha_i).
```

Thus the norms of the monomial generators give all vertices of the displayed polyhedron. The norm of an arbitrary element of `J` is homogeneous of degree `n` in its coefficients and is a sum of monomials whose exponent vectors lie in the same scaled Newton polyhedron. Cancellation can remove terms but cannot create a term below that polyhedron. Hence the integral closure has exactly the stated Newton polyhedron. Pulling back multiplies the `i`-th exponent by `e_i`, yielding `n NP(J)`, which is the Newton polyhedron of `J^n`.

### Corollary 2.2 -- normalized blowup comparison

The normalized pullback of the blowup of `N_f(J)` and the normalized blowup of `J` have the same toric normal fan.

---

## 3. The global Norm--Rees shadow

Assume `X` is excellent and Noetherian, as in the finite-type situation of the programme.

### Definition 3.1

The global Norm--Rees shadow of `J` is

```text
NR_f(J)=normalization(Rees_X(N_f(J))).
```

The normalization is finite. Its relative Proj is the canonical normalized norm modification.

### Theorem 3.2 -- globalization of X048

On every toroidal chart of Section 2, `Proj(NR_f(J))` is the X048 Norm--Newton modification. The construction glues globally, commutes with smooth/etale base change, and is independent of a generating set of `J`.

### Proof

The norm ideal is globally defined and flat-natural. Normalization of a finite-type algebra is finite on excellent bases and commutes with restriction. The local polyhedron theorem identifies the chartwise normalized Rees algebras.

### Ordinary realization

The normalized modification is not used as the final resolution step. Its modification ideal and complete colour data enter the X044 portfolio. In the toroidal chamber a regular fan refinement is realized by a finite sequence of ordinary blowups in regular boundary strata. In a nonmonomial chamber, the support of the norm-Rees presentation defects is part of the lower-dimensional preparation.

---

## 4. Exactified balanced descent-gap elimination

Let `X` be reduced Noetherian and let `f:Y->X` be finite locally free. For a coherent ideal `J subset O_Y`, write

```text
I_- = Ann_X(f_*O_Y/J),
I_+ = image((f_*O_Y)^vee tensor J -> O_X),
Q_- = J/I_-O_Y,
Q_+ = I_+O_Y/J.
```

Assume the codimension-one ramification residue of `J` vanishes along every component of the branch divisor. Then the two quotients are zero at every codimension-one generic point; their supports have codimension at least two.

### Definition 4.1 -- complete descent-interval diagram

Retain the exact sequences

```text
0 -> I_-O_Y -> J -> Q_- -> 0,
0 -> J -> I_+O_Y -> Q_+ -> 0,
```

as well as:

```text
the evaluation map defining I_+;
all kernels, images and cokernels;
Tor_1 terms under the intended base changes;
multiplication maps and Rees powers;
source, owner, boundary and wild-layer labels.
```

### Theorem 4.2 -- balanced gap elimination

Suppose a good-open-admissible modification `pi:X'->X` has the following properties:

1. the strict transforms of `Q_-` and `Q_+` are flat over `X'`;
2. the complete descent-interval diagram is universally exact after the centre-exact transform;
3. every component of `X'` meets the good open on which `Q_-=Q_+=0`.

Then

```text
Q_-'=Q_+'=0
```

and the transformed ideal `J'` is extended from a unique downstairs ideal `I' subset O_(X')`.

### Proof

A finite flat module on a reduced Noetherian scheme has support equal to a union of irreducible components. Each transformed quotient is flat and vanishes on the good open meeting every component, hence is zero. Universal exactness then identifies `J'` both with the extension of the transformed lower ideal and with the extension of the transformed upper ideal. Faithful flatness of `Y'->X'` gives uniqueness.

### Corollary 4.3 -- existence in the candidate architecture

Raynaud--Gruson flatification applied simultaneously to the finite quotient portfolio gives a good-open-admissible blowup with property (1). X042 universal exactification supplies property (2), and X044 realizes the resulting modification by ordinary regular jointly legal centres using strict lower-dimensional full-portfolio preparation. Thus the balanced descent gap is eliminated in the candidate architecture.

### Firewall

If a divisorial ramification residue is nonzero, the hypotheses fail at a codimension-one generic point. No application of flat-kill is permitted. The X048 ramification-residue theorem remains the decisive no-go.

---

## 5. Ramification-balanced base-first preparation in the toroidal chamber

Let the event-visible finite wild map be toroidal on a finite regular upper/common model and let the complete upper coloured ideal family be monomial. Form the exact joint marked ideal `J_joint` upstairs and the global Ferrand norm ideal `N_f(J_joint)` downstairs.

### Theorem 5.1 -- toroidal RB-BFWP

Conditional on the X044 lower-dimensional full-portfolio theorem, there is a finite sequence of ordinary blowups on the original base in regular jointly legal centres such that on every normalized upper chart:

1. the joint upper marked family is monomial and principal;
2. every divisorially unbalanced colour is controlled by its base norm-Rees shadow rather than by descent of its upper centre;
3. every ramification-balanced colour has zero transformed descent gap and is the extension of a downstairs colour;
4. all passive, boundary, source and event data re-enter through X042--X045 without reset;
5. every nonterminal leaf lowers the norm-Newton face profile, a balanced-gap Fitting profile, or an earlier class-V coordinate.

### Proof

Principalize the global norm-Rees shadow by a regular toroidal base word. The toroidal norm-polyhedron theorem identifies its normalized pullback with the upper Newton modification. Apply the balanced gap theorem to the codimension-at-least-two residual diagrams. The unbalanced branch never requests descent of an impossible upper centre. Joint legality and hereditary comparison follow from X042--X044. The monomial fan word and the lower-dimensional gap word have finite heights, giving the stated strict alternatives.

---

## 6. What remains: Event-Visible Wild Toroidalization

The preceding theorem assumes a toroidal finite map and a monomial complete upper packet. Local uniformization after extension or alteration gives regular upper models, but it does not by itself produce a toroidal finite map compatible with every object in the complete state.

### Single target EVWT

> **Event-Visible Wild Toroidalization.** For one independent Artin--Schreier degree-`p` layer on a quasi-compact valuation neighbourhood, construct a finite common model and a finite regular upper preparation such that:
>
> 1. the finite wild map is toroidal, or diagonal after a finite toroidal chart cover, in every direction used by the event-visible state;
> 2. the complete active, passive, Hasse, differential, ramification, source and boundary portfolio is monomial;
> 3. the Ferrand norm ideals and descent-interval diagrams commute with the chart groupoid;
> 4. every nonterminal leaf enters the toroidal RB-BFWP theorem or lowers an earlier valuation/wild-layer coordinate;
> 5. no equal-or-higher class-V token with new ancestry is born.

Under EVWT, Theorem 5.1 gives UDE-EV, and X045 supplies the global recurrent multiset descent.

---

## 7. Candidate-graph contraction

### Closed or conditionally closed after X049

```text
global Ferrand norm ideal;
flat-base-change naturality of the norm ideal;
toroidal norm-polyhedron identity;
global normalized Norm--Rees shadow;
exactified balanced descent-gap elimination;
conditional ordinary regular realization of gap flatification;
toroidal ramification-balanced base-first wild preparation;
X047 clean zero-shadow descent;
X045 coherent recurrence termination.
```

### Remaining chain

```text
Event-Visible Wild Toroidalization (EVWT)
-> UDE-EV
-> no equal-or-higher class-V birth
-> strict class-V ordinal
-> full global source-causal termination
-> finite Zariski/etale serialization
-> principalization and functorial resolution.
```

---

## 8. Truth boundary

```text
FERRAND_NORM_IDEAL                              = closed construction
TOROIDAL_NORM_NEWTON_IDENTIFICATION             = closed local theorem
GLOBAL_NORMALIZED_NORM_REES_SHADOW              = closed construction
BALANCED_GAP_ELIMINATION                        = conditional on exactified flatification and X044 realization
TOROIDAL_RB_BFWP                                = conditional theorem closed
EVENT_VISIBLE_WILD_TOROIDALIZATION              = open
UDE_EV_AND_STRICT_CLASS_V_ORDINAL                = open pending EVWT
GLOBAL_TERMINATION_AND_GLOBALIZATION             = open
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION       = not established
```

X049 should remain focused on EVWT. No new global invariant, source ledger, centre grammar, recurrent taxonomy, or manuscript architecture is justified before the one-layer toroidalization theorem is proved, refuted, or split by a genuine counterexample.

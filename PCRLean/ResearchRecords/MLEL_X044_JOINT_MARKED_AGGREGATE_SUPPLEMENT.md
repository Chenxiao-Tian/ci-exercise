# MLEL-X044 Supplement

## Joint Marked Aggregation and Colour-Preserving Monomial Resolution

**Parent:** `MLEL-X044 / COP-PCH-UCS-FINAL`  
**Date:** 2026-08-05  
**Status:** exact regular-centre reduction; global block termination remains open.

---

## 1. The common-mark aggregate

Let

\[
  \{(\mathfrak a_\lambda,b_\lambda)\}_{\lambda\in\Lambda}
\]

be a finite family of marked ideals on a regular scheme. Choose a common multiple `B` of the positive marks and put

\[
 c_\lambda=B/b_\lambda,
 \qquad
 \mathfrak A=\sum_\lambda \mathfrak a_\lambda^{c_\lambda}.
\]

The colours and source labels are retained in the multi-Rees package, but the single pair `(A,B)` controls simultaneous centre permissibility.

## 2. Exact root lemma for a regular centre

Let `D` be a regular closed subscheme of a regular scheme, with ideal `J`. Since

\[
 \operatorname{gr}_J(\mathcal O_W)
 \simeq
 \operatorname{Sym}_{\mathcal O_D}(J/J^2)
\]

is locally a polynomial algebra over a reduced ring, it is reduced. Therefore

\[
 \operatorname{ord}_J(f^m)=m\operatorname{ord}_J(f)
\]

and

\[
 \mathfrak a^m\subset J^{bm}
 \Longleftrightarrow
 \mathfrak a\subset J^b.
\]

The reverse implication can fail for a nonregular centre because the associated graded ring may contain nilpotents.

## 3. Simultaneous permissibility

For a regular centre `D`,

\[
 \mathfrak A\subset J^B
 \Longleftrightarrow
 \mathfrak a_\lambda\subset J^{b_\lambda}
 \quad\text{for every }\lambda.
\]

One direction is immediate. In the other direction each summand lies in `J^B`, and the regular-centre root lemma applies.

## 4. Transform compatibility

If `D` is permissible and `H` is exceptional, then

\[
\begin{aligned}
 \mathfrak A'
 &=I_H^{-B}\mathfrak A\mathcal O_{W'}\\
 &=\sum_\lambda
   \left(I_H^{-b_\lambda}
          \mathfrak a_\lambda\mathcal O_{W'}\right)^{c_\lambda}\\
 &=\sum_\lambda (\mathfrak a_\lambda')^{c_\lambda}.
\end{aligned}
\]

Thus aggregation commutes with every controlled transform.

## 5. Why product aggregation is wrong

The product of the ideals controls only the sum of component orders. Excess order in one colour can mask failure in another. The common-power sum encodes ownerwise simultaneous permissibility exactly.

## 6. Monomial phase

After simultaneous preparation every colour is monomial in an SNC boundary. The aggregate is one monomial marked ideal whose cosupport is exactly the common coloured cosupport. A characteristic-free monomial principalization chooses only boundary strata contained in that cosupport and strictly lowers the standard monomial invariant. Each selected regular centre is permissible for every colour. Colours remain separate for owner, source, and successor transport.

## 7. Consequence

```text
finite coloured obstruction package
-> lower-dimensional simultaneous preparation
-> exact common-mark aggregate
-> ordinary monomial marked-ideal resolution
-> colourwise hereditary reconstruction.
```

This closes the centre-selection block conditionally on the lower-dimensional full-portfolio theorem. It does not prove that the sequence of successor blocks is finite.

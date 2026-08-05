# MLEL-X048 Supplement

## Content--Annihilator Descent Intervals for Finite Flat Ideals

**Parent:** MLEL-X048 / FDI-RRF-NNW-FINAL  
**Date:** 2026-08-05  
**Status:** exact finite-flat algebra.

Let `A->B` be finite faithfully flat and let `J subset B` be a finitely generated ideal.

Define

```text
Low(J)=Ann_A(B/J),
Up(J)=image(Hom_A(B,A) tensor_A J -> A).
```

Then

```text
Low(J)B subset J subset Up(J)B.
```

`Low(J)` is the largest ideal `I` of `A` for which `IB subset J`, and `Up(J)` is the smallest ideal `I` for which `J subset IB`. Consequently

```text
J descends <=> Low(J)=Up(J).
```

The finite descent defect is

```text
(J/Low(J)B) directSum (Up(J)B/J).
```

The construction is local on the base and compatible with flat base change after the complete kernel/image/evaluation diagram is exactified. This exactification is necessary under the nonflat base blowups used by the resolution algorithm.

For `A=k[t]`, `B=k[s]`, `t=s^e`, and `J=(s)`,

```text
Low(J)=(t),
Up(J)=A.
```

Thus the ideal is maximally non-descended at the ramification divisor. This example is the basic firewall against interpreting every regular upper centre as a potential downstairs centre.

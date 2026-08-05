# MLEL-X048 Supplement

## Ramification Residues and the Alteration-Only Centre Firewall

**Parent:** MLEL-X048 / FDI-RRF-NNW-FINAL  
**Date:** 2026-08-05  
**Status:** exact codimension-one theorem and no-go.

Let `A` be a DVR and let the normalization in a finite extension be the semilocal product of DVRs `B_j`, with

```text
t=unit_j u_j^(e_j).
```

An invertible upper ideal has exponents `d_j`. It descends from `A` exactly when one integer `a` satisfies

```text
d_j=e_j a
```

for all `j`. The class of `(d_j)` modulo this ramification lattice is its divisorial residue.

A sequence of ordinary blowups of a regular normal base is an isomorphism at the generic point of every old divisor; blowing the divisor itself is an identity. Hence a nonzero divisorial residue cannot be removed by further base blowups.

The upper centre `(u_j)` in a ramified chart may be regular while no corresponding base centre exists. Such a centre is **alteration-only**. It may be used to understand the upper monomial packet, but it cannot be counted as a step of the base resolution and it cannot be forced to descend by a Cech purification process.

If all divisorial residues vanish, the remaining content--annihilator descent gap is supported in codimension at least two. That balanced residual gap is a coherent colour and can be routed to the X044 lower-dimensional actual-centre block.

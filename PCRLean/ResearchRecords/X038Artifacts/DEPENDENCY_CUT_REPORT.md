# X038 Dependency-Cut Report

## Root-facing path

The D001 critical path remains

```text
FND-11
-> CTR-13
-> HER-15
-> TRM-12
-> GLB-07/08
-> FIN-04.
```

X038 refines the central `CTR-13 -> HER-15` edge through `HER-02/HER-03`:

```text
raw actual carrier
-> one finite affine normal-cone/mixed-Rees packet
-> centre-enriched lower-dimensional flatifier word
-> Tor-Valabrega common-core transport
-> joint legality
-> all-chart hereditary reentry.
```

## Compression achieved in this round

The following formerly load-bearing tasks are no longer required as
independent existence theorems:

```text
finite Rees-Serre tail;
Hilbert-polynomial compression;
projective-normal flatification as opposed to affine normal-cone flatification.
```

For Noetherian finite data, the complete associated-graded module and complete
two-ideal mixed-Rees module are finite over finite-type algebras.  General
affine flatification therefore applies to the whole graded packet at once.
The remaining problem is exact ambient transport, not finite generation.

## Minimum open cut after the current experimental leaves

```text
CUT-A  X038-G6/G9
       scheme-level common-core cospan, homogeneous kernel formulas,
       overlap cocycles, and smooth base change

CUT-B  X038-G13/G14/G15
       factor a flatifier through recursively legalized regular trace centres
       and prove exact ambient affine-normal transport

CUT-C  X038-G18/G19
       Cartier-stable no-reset and carrier-dimension termination.
```

The standard or Lean-sized layers below this cut are:

```text
relative power saturation and quotient power torsion;
two-surjection common-core equivalence;
finite associated-graded module over the affine normal cone;
finite two-ideal mixed-Rees module;
Noetherian stabilization of homogeneous saturation;
flatness of the total graded direct sum iff every piece is flat;
lexicographic rank arithmetic.
```

## Downstream release

Closing `CUT-A` releases:

```text
exact HER-02/HER-03 chart interface;
a canonical finite coherent passive defect packet;
all-chart transform statements with a common codomain.
```

Closing `CUT-B` releases:

```text
joint active/passive/log legality for preparatory and final centres;
regular ambient realization of arbitrary admissible flatifiers;
anchor-contact and log-conormal reuse of one compiler.
```

Closing `CUT-C` releases:

```text
HER-14/HER-15 no-reset handoff;
TRM-11 composite rank;
TRM-12 local termination compiler.
```

## Highest-information next theorem

The single most informative next local theorem is:

> For a Noetherian affine nested pair `I subset K`, a finite module `M`, and
> every standard `K`-blowup chart, construct the two canonical epimorphisms to
> `Q_q(F_a/F_(a+1))` simultaneously in all degrees as dehomogenizations of
> homogeneous maps between finite two-ideal mixed-Rees modules; identify their
> kernels with the Tor and power-saturation modules; and prove compatibility on
> double localizations.

A proof would close the direction ambiguity, finite-packet realization, and
first overlap edge at once.  A counterexample would sharply identify a missing
Tor-independence, regular-immersion, or saturation hypothesis.

## Circularity audit

The flatifier may have singular centre, but it is never inserted directly into
the final sequence.  Its source ideal is processed on the regular carrier, and
every regular trace subcentre has strictly smaller carrier dimension.  The
candidate recursion therefore uses

```text
carrier dimension
> unresolved affine ANC-TVC packet
> contact
> debt.
```

The arithmetic relation is Lean-written.  The geometric claim that every
recursive call satisfies the dimension inequality remains open.

## Formal status

```text
CERTIFIED_GRAPH_CHANGED                    = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED         = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION = false
FORMAL_GLOBAL_STATUS                       = OPEN_GAP
```

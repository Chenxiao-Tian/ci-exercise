# MLEL-002 / FCR-GEO

## Frobenius-Core Regular Geometric Realization

This file freezes the exact scope of the first machine-checked geometric chamber of the MLE-Lean line.

## Certified chamber target

The formal module `PCRLean.HMCSCCD` treats a restricted split-coordinate, finite multi-owner Frobenius chamber.  The input data include:

1. finitely many active owner ideals with one common positive Frobenius mark;
2. exact descent of each active owner from a base ideal;
3. a joint base core obtained from the finite supremum of owner cores;
4. a root equivalence identifying the root of the joint core with an actual coordinate-centre ideal;
5. explicit split or coordinate certificates for the passive module and the centre quotient.

Within this chamber the intended conclusions are:

- the joint active ideal is exactly the extension of the joint base core;
- the coordinate root centre is an actual proper finite-type ideal;
- the same centre is marked-permissible for every active owner and for their finite aggregate;
- its quotient is explicitly a smaller polynomial ring, which is the affine regular-coordinate certificate used here;
- on every standard coordinate blowup chart the pure Frobenius packet has unit controlled transform;
- overlap equality is immediate after all transformed packets become the unit ideal;
- the split passive module is preserved through the Morita block description;
- the chamber rank drops from one unresolved split-Frobenius step to the terminal rank zero.

## Evidence boundary

This chamber is a genuine restricted theorem only after `lake build`, placeholder rejection, and `#print axioms` all succeed on the exact commit.

It is not the universal geometric realization theorem.  In particular it does not prove that an arbitrary canonical Frobenius core:

- admits a root equivalence;
- is locally a coordinate ideal;
- has constant conormal rank;
- is regular and SNC-compatible without the coordinate certificate;
- is passive Tor-safe for arbitrary passive owners;
- survives strict transform, normalization, saturation, and integral closure on arbitrary overlaps;
- globalizes functorially over arbitrary schemes;
- resolves immediate defect;
- proves arbitrary-dimensional resolution in positive characteristic.

The global status therefore remains `OPEN_GAP`.

## Research role

`MLEL-002` establishes the first nontrivial end-to-end chamber in which the chain

`finite Hasse stability -> Frobenius descent -> joint root centre -> all-chart terminalization`

is represented by actual ideals and ordinary affine blowup charts.  The next universal burden is to remove the split-coordinate hypotheses by a Fitting/flattening and descent theorem, not to strengthen the conclusion by assumption.

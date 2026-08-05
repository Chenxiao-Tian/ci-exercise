# MLEL-X041 Final Semantic Correction

## Composite Blowup Ideals Exist, but Functorial Centre-Exact Compression Is an Additional Theorem

**Parent:** `MLEL-X041 / HNC-STC-RFL`  
**Class:** `HIDDEN-CHOICE / NATURALITY CORRECTION`  
**Date:** 2026-08-04 ET / 2026-08-05 UTC  
**Global status:** `OPEN_GAP`

---

# 1. Correction

For a finite sequence of blowups of finite-presentation centres, the
composition is a blowup of one finite-presentation centre.  The standard proof,
however, chooses a sufficiently large degree and a finite submodule of a power
of the preceding centre ideal.  It proves existence; it does not by itself
produce a presentation-independent ideal functorial under every flat base
change.

Therefore the phrase

```text
canonical or distinguished composite word ideal
```

is too strong unless a separate construction and naturality certificate are
provided.

The valid standard statement is:

```text
a centre-exact composite ideal exists,
its centre has the union-of-word-centres support,
and strict transform for that certified ideal equals the iterated strict
transform.
```

The choice and transport of such an ideal remain project data.

---

# 2. Correct source-word object

A functorial flatifier source is retained as the complete package

```text
SW = (
  the ordered centre-enriched blowup word W,
  the final modification pi_W,
  the final strict transforms F_W,
  the total exceptional/source lineage,
  a polarized composite-blowup presentation when chosen,
  the support-union and strict-transform certificates,
  flat-base-change comparison maps
).
```

The word and final strict transforms are primary.  A single ideal
`J_W^comp` is optional certificate data used to invoke blowup universal
properties or form a product common refinement.  It is never allowed to replace
`W` or its transform payload.

---

# 3. Two valid common-refinement routes

## Route A — functorial polarized compression

Construct `J_W^comp` from the source word together with a relatively ample
exceptional polarization and prove:

```text
Bl_(J_W^comp)(C) ~= terminal source modification;
support(J_W^comp) is the transported union of word centres;
J_W^comp commutes with flat base change up to the certified Cartier
 equivalence that preserves strict transforms.
```

The finite product of the ambient traces of these polarized ideals then gives
the common-refinement modification.

## Route B — word-level common cofinality

Retain the finite source words and build a functorial common modification of
their terminal models, for example from the closure of the common flat open in
their fibre product, followed by a functorial blowup sequence dominating this
modification.  One must then prove that the resulting regular realization is
centre-exact for every original source word.

Neither route is completed in the current program.  Route A is shorter for the
Annals manuscript; Route B is a valuable fallback if functorial ideal
compression fails.

---

# 4. Exact use of standard strict-transform theorems

The standard theorems close the following implications only after the
centre-exact presentation is supplied:

```text
certified composite centre with union support
-> iterated strict transform equals one-step strict transform;

flat terminal source transform
-> every later blowup strict transform is its pullback;

finite family of certified one-step source ideals
-> product blowup is a common refinement.
```

They do not prove functorial choice of the composite centre for an arbitrary
word.

The local-to-global flatification product argument applies directly to a finite
family of already specified admissible blowups.  It does not remove the hidden
choice in first turning a functorial sequence into one ideal.

---

# 5. Revised X041 cut

Add the node

```text
X041-G4F  FUNCTORIAL_POLARIZED_WORD_COMPRESSION
```

with obligations:

```text
finite-type composite ideal;
terminal-modification isomorphism;
union-of-centres support;
strict-transform equality;
flat-base-change naturality;
Cartier-factor/torsion boundary;
source and exceptional lineage preservation.
```

The highest-information cut becomes

```text
X041-G1/G2  homogenized normal packet and flatness;
X041-G4F     functorial polarized word compression, or word-level fallback;
X041-G6/G7  lower-dimensional full-portfolio regular realization;
X041-G9/G10 Regular-Flag Flat-Lift and overlap naturality;
X041-G12     source-conservative all-chart no reset.
```

The dominant geometric theorem remains Regular-Flag Flat-Lift.  The
canonicity correction prevents a false shortcut in the globalization edge.

---

# 6. Publication consequence

Paper III needs a short independent section on polarized source-word
compression and its fallback common-modification construction.  The revised
central estimate is **552 dense Annals/AMS-equivalent pages**:

```text
I    90
II  120
III 132
IV   84
V    78
VI   48
    ---
    552
```

---

# 7. Truth boundary

```text
COMPOSITION_OF_FINITE_BLOWUP_WORD_IS_A_BLOWUP       = standard existence
COMPOSITE_CENTRE_SUPPORT_UNION_CERTIFICATE           = standard existence
STRICT_TRANSFORM_TRANSITIVITY_AFTER_CERTIFICATION    = standard theorem
FUNCTORIAL_CANONICAL_COMPOSITE_IDEAL                 = not supplied by those theorems
SOURCE_WORD_REMAINS_PRIMARY                          = true
POLARIZED_WORD_COMPRESSION_ROUTE_IDENTIFIED          = true
WORD_LEVEL_COMMON_MODIFICATION_FALLBACK_IDENTIFIED   = true

FUNCTORIAL_POLARIZED_WORD_COMPRESSION_PROVED         = false
WORD_LEVEL_CENTRE_EXACT_COFINALITY_PROVED            = false
REGULAR_FLAG_FLAT_LIFT_PROVED                        = false
ALL_CHART_NO_RESET_PROVED                            = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION           = false
FORMAL_GLOBAL_STATUS                                 = OPEN_GAP
```

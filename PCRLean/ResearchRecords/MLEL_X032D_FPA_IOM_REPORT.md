# MLEL-X032D / FPA-IOM

## Finite-Projective Automatic Dual Frames and Intrinsic Order-Ideal Compiler

**Protocol:** `PCR-FRACTAL-PROOF-LEAN 1.0`  
**Parent group:** D001 `G11 / FND-11`  
**Parents:** `MLEL-X032B`, `MLEL-X032C`  
**Class:** `EXPERIMENTAL_ALGEBRAIC_EDGE_CLOSURE / NO_THEOREM_PROMOTION`  
**Global status:** `OPEN_GAP`

## Mathematical result

For every finite projective module `P` over a commutative ring `R`:

```text
Module.Finite R P
+ Module.Projective R P
-> exists n and a surjection (Fin n -> R) ->ₗ[R] P
-> the surjection splits
-> P has an explicit finite dual frame indexed by Fin n.
```

The first arrow uses `Module.Finite.exists_fin` and
`Fintype.linearCombination`; surjectivity is exactly the theorem that the
chosen finite family spans the top submodule. The second arrow is the
projective lifting property. The third arrow projects the standard free basis
and pulls back coordinate functionals.

Applied to the cokernel `Q = E / range(phi)`, this constructs the finite frame
required by the existing X031 order-ideal compiler and produces a first-class
finite-index package carrying the graph / proper-hybrid / unit-obstruction
status.

## Candidate-graph consequence

The algebraic input to FND-11 is reduced from

```text
finite projective cokernel + independently supplied finite dual frame
```

to

```text
finite projective cokernel.
```

The finite dual frame is theorem-generated rather than assumed.

## Exact remaining frontier

This closes only the abstract module-theoretic edge. It does not prove:

1. that the cokernel extracted from every positive-characteristic resolution
   state is finite projective;
2. that this cokernel and obstruction section are presentation independent;
3. compatibility of the automatically generated packages under localization,
   smooth/etale maps, controlled transforms, and overlap transport;
4. construction of a proper regular marked closure in the nonzero branch;
5. active/passive/SNC legality, hereditary reentry, termination,
   globalization, principalization, or resolution.

No declaration is imported into `CertifiedIndex`; exact clean-room evidence is
required before even restricted promotion can be considered.

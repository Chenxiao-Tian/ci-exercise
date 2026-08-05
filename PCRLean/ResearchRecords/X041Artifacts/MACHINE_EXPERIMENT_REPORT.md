# X041 Bounded Machine Experiment Report

The experiments are falsification tools only; they do not prove the universal
module or scheme statements.

## Experiment 1 — binary product saturation

For every cyclic module `Z/nZ` with

```text
2 <= n <= 40,
q,r,d in Z/nZ,
N=(d) subset Z/nZ,
```

the program compared

```text
Sat_(q*r)(N)
```

with

```text
Sat_r(Sat_q(N)).
```

```text
cases checked = 672399
failures      = 0
```

## Experiment 2 — permutation invariance of length-three words

For every cyclic module `Z/nZ` with

```text
2 <= n <= 15,
word=(q1,q2,q3),
N=(d),
```

the program compared saturation for every distinct permutation of the word.

```text
comparisons checked = 945231
failures             = 0
```

## Interpretation

The experiments support the exact Lean target

```text
Sat_(product word)(N)=iterated saturation along the word
```

and its permutation invariance in commutative modules.  They do not test
perfect complexes, `Leta`, scheme blowups, good-triple base change, source
lineage, or actual strict transforms.

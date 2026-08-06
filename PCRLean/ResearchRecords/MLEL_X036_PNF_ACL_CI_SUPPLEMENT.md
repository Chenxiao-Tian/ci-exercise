# MLEL-X036 / PNF-ACL — Exact Clean-Room Supplement

**Date:** 2026-08-04  
**Class:** `EXPERIMENTAL_GREEN_SLICE / NO_THEOREM_PROMOTION`  
**Formal status:** `OPEN_GAP`

## Exact evidence

```text
PR                                  = #46
base branch                         = pcr-fractal-x036-pnf-acl-base-20260804
base SHA                            = 1569bfb84696ab9a47beeeffcc9d8aaf34e3be30
head branch                         = pcr-fractal-x036-pnf-acl-head-20260804
head SHA                            = f91193c943adc8bdb2d1f3d5b2f0c6b61580be40
workflow run                        = 30927499452
job                                 = 92053484311
conclusion                          = success
Lean                                = 4.30.0
artifact                            = 8900025922
artifact SHA-256                    = fb5f2a0bc06c83645d2c87b850dff8a996c259c390623975c2bc21f032dd647c
```

The run rejected `axiom`, `sorry`, and `admit` in the X036 slice, bootstrapped
and hashed the pinned environment, completed the official 8539-job build,
built every exact X036 module target, ran the unified `#print axioms` audit
with no `sorryAx`, and uploaded the exact source/evidence archive.

## Certified scope of this evidence

The green slice proves only:

1. finite low-degree plus flat-tail certificates compile to flatness of the
   complete graded direct sum;
2. the same compiler works for a finite passive portfolio;
3. one scalar exceptional contact factor can be removed and the numerical
   contact order drops;
4. contact/passive/debt lexicographic ranks are well founded.

It does not prove the scheme-level Rees–Serre comparison, projective-normal
transport under ambient blowups, passive/logarithmic ambient legalization,
anchor-contact transform compatibility, hereditary no-reset, termination,
globalization, or arbitrary-dimensional resolution.

```text
X036_EXPERIMENTAL_CLEANROOM_GREEN          = true
X036_AXIOM_AUDIT_NO_SORRYAX                = true
X036_DECLARATIONS_PROMOTED                  = false
CERTIFIED_GRAPH_CHANGED                     = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED          = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION = false
FORMAL_GLOBAL_STATUS                        = OPEN_GAP
```

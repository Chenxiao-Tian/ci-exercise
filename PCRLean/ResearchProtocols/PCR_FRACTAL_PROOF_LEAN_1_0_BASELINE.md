# PCR-FRACTAL-PROOF-LEAN 1.0

## Fractal Proof Engineering, Edge Certification, Mathematical Invention, and Lean Closure Protocol

**Chinese title:** 分形证明工程、依赖边认证、新数学创造与 Lean 闭环协议 1.0  
**Baseline node:** `MLEL-A003 / FPE-EDGE`  
**Date:** 2026-08-03  
**Epistemic class:** `RESEARCH_META_PROTOCOL / PROOF_ENGINEERING`  
**Baseline status:** `ACCEPTED_RESEARCH_PROTOCOL`  
**Seed architecture:** `MLEL-D001 / FCPP-ATLAS`  
**Accepted mathematical node:** `MLEL-M004 / HMC-SCCD`  
**Global truth:** `OPEN_GAP`  
**General resolution proved:** `false`

## Purpose

The protocol treats the final positive-characteristic-resolution theorem as the root of a typed proof hypergraph. Every unresolved claim is recursively refined into smaller claim nodes. Every dependency arrow is itself a theorem obligation carrying soundness, case coverage, witness synthesis, interface compatibility, naturality and well-foundedness data. Refinement continues until the leaves can be proved directly from mathlib and the Certified Graph and pass the Lean kernel.

The current D001 architecture supplies the seed graph:

```text
6 papers
65 load-bearing theorem groups
325 DEF/LEM/PROP/THM/COMP dictionary entries
1,340 explicit dependency edges
520 dense-paper-equivalent pages
```

These nodes are not assumed to be final atomic leaves. They must be recursively refined, corrected by counterexamples and connected by independently proved semantic edge certificates.

## Core closure principle

```text
root theorem
-> recursively refined claim nodes
-> first-class edge theorems
-> atomic Lean proofs
-> certified cut covering the root
-> final theorem
```

A complete proof requires both:

1. every claim node on a root-covering certified cut is kernel proved; and
2. every hyperedge used on that cut has a kernel-proved semantic certificate.

Acyclicity alone is insufficient. The edge must prove that its children really imply the parent, that all case branches are exhaustive, that witnesses are actual finite data, that interfaces match, and that recursive calls decrease a well-founded rank.

## Research generation policy

Examples, counterexamples, symbolic experiments, local theorems, historical jumps and newly invented mathematical tools may generate candidate refinements. Candidate tools can include new modules, complexes, obstruction classes, categories, dualities, persistence objects, causal ledgers, finite carriers or rewriting systems. None enters the Certified Graph until the precise bridge theorem and all required edge certificates pass Lean.

## Candidate and Certified graphs

- `CandidateGraph` is mutable and may contain conjectures, alternatives and failed branches.
- `CertifiedGraph` is monotone and contains only exact Lean-kernel-checked nodes and edges.
- Candidate manuscripts may change; the final paper must be reconstructed from the Certified Graph.

## Atomicity rule

A node is not atomic while it hides a witness, a chart, an overlap, a base-change law, an owner/passive/boundary condition, a history reset, a termination argument or an unproved geometric interface. Phrases such as “standard,” “similarly,” “after preparation,” or “choose a canonical centre” force further refinement.

## Completion condition

```text
FINAL_MAIN_THEOREM_KERNEL_VERIFIED = true
ALL_CLAIM_NODES_ON_CERTIFIED_CUT   = proved
ALL_EDGE_CERTIFICATES_ON_CUT       = proved
PAPER_LEAN_SEMANTIC_MISMATCH       = 0
```

## Persistent artifacts

The full 32-page PDF protocol, Markdown source, JSON protocol, claim/edge templates, Lean architecture file, baseline record, checksums and complete package are stored in the persistent MLE–Lean Library under:

```text
/正特征奇点消解/MLE-Lean线/ResearchProtocols/
PCR-FRACTAL-PROOF-LEAN-1.0/
```

Baseline inclusion records the protocol and changes no mathematical truth. This file is not imported into `CertifiedIndex`.
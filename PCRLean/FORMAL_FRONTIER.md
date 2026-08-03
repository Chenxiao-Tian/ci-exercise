# PCRLean exact formal frontier

This branch separates kernel-certified mathematics, experimental mathematics, and architecture-only proof planning. It does not contain a proof of arbitrary-dimensional resolution in positive characteristic.

## Certified layer

`MLEL-M004 / HMC-SCCD` remains the highest accepted node. It certifies finite realized Hasse-Morita active/passive core descent and a conditional source-causal termination backend in their exact stated domains. It does not construct the universal geometry.

## Experimental mathematical frontier

`MLEL-X031 / ACI-MMR-OIH` is the current archived centre-synthesis frontier. It joins:

```text
zero obstruction -> maximal/augmented minors -> unique graph centre
nonzero obstruction -> intrinsic order ideal -> finite marked hybrid closure
```

Frozen source head: `1edbe17181b638c366bf650b578e4d5f40e89185`. Clean-room PR #31/run `30854334500` was queued at archival. X031 is not imported into `CertifiedIndex`.

## Controlling proof architecture

`MLEL-D001 / FCPP-ATLAS` freezes the complete proof topology as six papers and 520 dense mathematical pages:

```text
G01-G13   FND: state semantics, finite packets and affine obstruction
G14-G26   CTR: actual centre or finite centre word
G27-G41   HER: joint legality and hereditary all-chart reentry
G42-G53   TRM: birth, defect, SCC exit and local termination
G54-G61   GLB: sheaf descent, functorial finite globalization, principalization
G62-G65   FIN: embedded/nonembedded resolution and proof-code reproducibility
```

Each of 65 groups has five entries: `DEF`, `LEM`, `PROP`, `THM`, and `COMP`. The full dictionary has 325 named obligations and 1,340 explicit dependency edges.

Independent audit `MLEL-D001-A001` verified unique IDs, five entries per group, valid edge endpoints, an acyclic 325-node DAG, a complete topological order, 65 Lean group cases, exact equality of the JSON and Lean group graphs, and the page total `520`.

`PCRLean.Blueprint.FinalProofAtlas.blueprint_implies_final_claim` is architecture-only: a `ProofPackage` proving every group from its declared predecessors yields the final group. It assumes and proves none of the open mathematical bridges by itself.

D001 clean-room target: PR #32, run `30858121934`, job `91833782154`; queued at revalidation.

## Open load-bearing groups

```text
G26       universal actual-centre synthesis
G31       universal joint legality
G41       hereditary all-chart no-reset reentry
G43       complete geometric birth realization
G47       recurrent-SCC exit
G49-G53   immediate defect and complete termination rank
G54-G60   non-affine descent and finite functorial globalization
G62-G65   final resolution, consequences and paper-Lean closure
```

No open group may be crossed by `axiom`, `sorry`, `admit`, an unproved instance, stale CI evidence, semantic weakening, or an Experimental-to-Certified import.

```text
CURRENT_CERTIFIED_NODE                     = MLEL-M004 / HMC-SCCD
CURRENT_EXPERIMENTAL_NODE                  = MLEL-X031 / ACI-MMR-OIH
CURRENT_ARCHITECTURE_NODE                  = MLEL-D001 / FCPP-ATLAS
D001_STATIC_TOPOLOGY_AUDIT_PASSED          = true
D001_CLEANROOM_GREEN                       = false
FINAL_MAIN_THEOREM_KERNEL_VERIFIED         = false
GENERAL_POSITIVE_CHARACTERISTIC_RESOLUTION = false
FORMAL_GLOBAL_STATUS                       = OPEN_GAP
```

# Formal verification

The 23 November 2026 correspondence review checked the revised manuscript against the same 152-module Lean candidate that passed the independent Linux replay. The original manuscript review and the clean replay retain their own source hashes. This edition corrects the range of one intermediate estimate and clarifies several proof steps. The exponent, counting population and formal statements are unchanged. [Preprint](subquarter-preprint.pdf) · [Proof notes](PROOF_NOTES.md) · [Detailed proof map](source/PROOF_MAP.md)

| Dimension | Result |
| --- | --- |
| Run completion | **COMPLETE**. Clean Linux x86-64 reproduction and confirmed VM termination. |
| Verification verdict | **PASS**. Six individual checks of the candidate export, both inventory reconciliations, strict axiom audits and protected comparison. |
| Paper coverage | **152 candidate and 44 independent reference modules**, 14 protected theorem interfaces, four protected definition bodies and zero holes. The counting conclusions take Stewart’s quantitative Thue bound as a premise. |
| Qualification | The 35 A07 controls passed at their recorded scopes. A separate operator performed A11. |
| Specialist review | Pending. The human mathematical review is separate from the mechanical results. |

Assurance gates A01–A11 and A13 passed for the 22 November manuscript and its frozen formal inputs. The machine-readable
record preserves the control statuses and exact evidence identities.
[Verification data](verification.json)

## Manuscript-to-Lean review

Three independent AI-assisted mathematical reviews covered the determinant argument, the arithmetic reduction and the counting interfaces. The integrated review found a missing hypothesis in §11. The revised text now matches the box theorem. The source map tracks 25 proof steps, 141 theorems and 31 definitions. All 313 implementing and named-target source spans matched the acquired candidate. The 78 earlier obligations, 12 joins and three final rows each retain their disposition. [Steps and dependencies](source/PROOF_MAP.md#forward-map-and-dependencies) · [Lean declaration index](source/PROOF_MAP.md#reverse-declaration-index) · [Historical contracts](source/PROOF_MAP.md#historical-bindings-and-joins)

| Article | What the review checked | Formal source |
| --- | --- | --- |
| §§2–4 | The count retains positive starts, endpoints and Pell returns. In Proposition 4.2 a single rectangle works across the box. Vanishing of determinants using all its columns gives the required rank bound even for populations with fewer rows than columns. | [Population](lean/PaperTargets/CanonicalSource.lean) · [Uniform minor](lean/PaperTargets/UniformRectangles.lean#L26) |
| §§5–7 | The source chooses its prime. The real bound and divisibility by the 28th power of that prime concern the same integer determinant. Once the class population is fixed, a single relation holds for every member. | [Actual interval nodes](lean/PaperProofs/DividedMinors.lean#L374) · [Entire class relation](lean/PaperTargets/ClassRelations.lean#L75) |
| §§8–9 | Graphs, coordinate rulings and singular fibres are accounted for. The common homogeneous degree retains the point at infinity in the resultant calculation. Content is removed before Stewart is applied at a signed nonzero level. | [Graph and ruling decomposition](lean/PaperProofs/GraphRulings.lean#L305) · [Resultant level](lean/PaperProofs/SourceRecovery.lean#L236) · [Class count](lean/PaperProofs/ClassCounts.lean#L88) |
| §§10–12 | Section 11 needs $0<\delta\le1$. For box loss $e>0$ it chooses $\delta=\min(1,e/3)$. Section 12 takes $e=\varepsilon/4$, pays both dyadic losses, covers the finite head and reuses one constant for every real cutoff through flooring. | [Box specification](lean/PaperTargets/BoxCounts.lean#L16) · [Natural count](lean/PaperProofs/GlobalCounts.lean#L118) · [Shared witness](lean/PaperAudit/ReviewHandover20261119.lean#L19) |
| §13 | The two jet determinants are 2240 and 393660. The linear coefficient has order 21 for distinct smooth nodes. Repeating a smooth node in the perturbed row realizes this order for the full determinant in the enlarged real model. For the selected arithmetic classes the full determinant already vanishes. | [Coefficient expansion](lean/PaperProofs/AngularWitness.lean#L497) · [Realized witness](lean/PaperProofs/AngularWitness.lean#L522) |

The published candidate comprises the 151 maintained Lean modules and the November audit overlay. All 155 project files matched the acquired candidate archive, including the three package files. All 43 target modules shared with the 44-module independent reference were byte-identical. The 14 selected theorem interfaces and four definition bodies below are the scope of the protected comparison. The original article review, this edition’s AI-assisted correspondence review, and the A11 kernel replay have distinct evidentiary scopes. [File hashes](sources.json) · [A11 identities](verification.json)

## Counting theorems

[`PaperTargets/GlobalCounts.lean`](lean/PaperTargets/GlobalCounts.lean) states the
three final specifications. [The corresponding proofs](lean/PaperProofs/GlobalCounts.lean)
cover all positive starts, with the real cutoff obtained by flooring. The
[supplementary joint-constant result](lean/PaperAudit/ReviewHandover20261119.lean#L19)
states both estimates with the same witness. The supplementary theorem and
the scalar-balance audit are covered by the full candidate replay and
transitive axiom checks. The 14 rows below give the separate selection for
protected comparison.

| Protected theorem interface |
| --- |
| `P0365Subquarter.original_shell_source_count` |
| `P0365Subquarter.natural_pair_count` |
| `P0365Subquarter.real_pair_count` |
| `P0365Subquarter.actual_graph_ruling_decomposition` |
| `P0365Subquarter.actual_source_resultant_level` |
| `P0365Subquarter.rounded_class_source_subpower` |
| `P0365Subquarter.irreducible_interval_source_count` |
| `P0365Subquarter.coarse_interval_source_count` |
| `P0365Subquarter.compact_box_source_count` |
| `P0365Subquarter.actual_box_source_count` |
| `P0365Subquarter.fixed_kernel_product_count` |
| `P0365Subquarter.fixed_kernel_ratio_count` |
| `P0365Subquarter.fixed_multiplier_ratio_count` |
| `P0365Subquarter.rounded_shell_source_assignment` |

| Protected definition body |
| --- |
| `P0365Subquarter.CF18NaturalPairCount` |
| `P0365Subquarter.CF18OriginalShellSourceCount` |
| `P0365Subquarter.CF18RealPairCount` |
| `P0365Subquarter.StewartPrimitiveThue` |

## Checker results

| Checker | Exit | Verdict | Stage cleanup |
| --- | --- | --- | --- |
| Lean native checker | 0 | PASS | Confirmed |
| Lean paranoid checker | 0 | PASS | Confirmed |
| Lean4Lean | 0 | PASS | Confirmed |
| Nanoda | 0 | PASS | Confirmed |
| Con-Leche | 0 | PASS | Confirmed |
| Con-Ron | 0 | PASS | Confirmed |

The strict audit covered every axiom declaration in the candidate export.
The actual target-transitive sets were retrieved for all 14 selected
interfaces and both supplementary audit declarations. The observed axiom
names were `Classical.choice`, `Quot.sound`, `propext`.
[Per-declaration sets](verification.json)

### Qualification controls

The 35 qualifying observations comprise 28 previously qualified cases, three installed coverage decisions (E01–E03), two installed receipt-collection checks (E05–E06), and two hosted controls. E04 rejected a changed revision against the environment lock. T06 observed network denial at the build, export and paranoid-checker stages, and exercised the offline Lake resolver separately in the same hosted run. The clean A11 replay followed qualification. [Control dispositions](verification.json)

## Stewart’s theorem

The Lean [definition of the premise](lean/PaperTargets/ThueLevels.lean#L16)
covers content-one integer polynomials of full degree 3 through 11 with
separable rational affine section, primitive signed integer pairs and
nonzero signed levels of their homogenizations. Section 9.3 explains how
the full-divisor specialization of Stewart’s Theorem 1 gives the bound
$2800d^{1+\omega(|h|)}$ used in the applications. Full degree rules out a
root at infinity. Separability provides the nonzero discriminant. The
specialization also applies to the separable reducible cubic used for
fixed multiplier ratios. Stewart’s proof itself lies outside the Lean
project. [Stewart, Theorem 1 and its specialization, pp. 795–796](https://uwaterloo.ca/pure-mathematics/sites/default/files/uploads/documents/s0894-0347-1991-1119199-x_0.pdf#page=3) · [Formal use in LP00](PROOF_NOTES.md#lp00)

## Formal variants

The paper uses the interval-node bound $1\le w\le 1+1/M$. The Lean
[interface](lean/PaperTargets/DividedMinors.lean) exposes $1\le w\le2$ and
$w\le1+3/M$, which suffice for the downstream determinant estimate. The
[proof of the interval nodes](lean/PaperProofs/DividedMinors.lean) establishes
the sharper inequality before relaxing it. The final natural and real
bounds use the same constant through exact flooring.

## Reproduction

The [Lean directory](lean) contains all 155 files from the checked
candidate, including 152 Lean modules and three package files. It uses
Lean/Lake 4.35.0, the pinned Mathlib revision and eight additional locked
dependencies. [Source hashes and tool pins](sources.json)

With Elan and the pinned Lake dependencies available, build the candidate
from the repository root.

```sh
cd lean
lake build PaperTargets PaperProofs PaperAudit +PaperAudit.ReviewSupplement +PaperAudit.ReviewHandover20261119
```

This command builds the public candidate with Lean. The protected A11 report
also used a separate frozen reference, mandatory controls and six checkers.
The independent reference, raw execution records and private reviews remain
in private custody. The public evidence gives their receipt and content
identities. [Verification data](verification.json)

Generate fresh reading files using Pandoc 3.9.0.2, Tectonic 0.16.9, the
prepared Tectonic v33 bundle cache and Poppler’s `pdftotext`. The renderer
reads the cited page numbers from the PDF it just built and checks the Lean spans before writing the proof map. The authoring repository exports the public data with `python3 -B research/papers/p0365-subquarter-v1/manuscript/render_proof_map.py --public-data`. The article and companion snapshots, the public data export and the source commit are recorded in [sources.json](sources.json).

```sh
python3 -B render.py --out-dir /tmp/subquarter-reading
cmp subquarter-preprint.pdf /tmp/subquarter-reading/subquarter-preprint.pdf
cmp PROOF_NOTES.md /tmp/subquarter-reading/PROOF_NOTES.md
cmp source/PROOF_MAP.md /tmp/subquarter-reading/source/PROOF_MAP.md
```

## Evidence identities

| Item | SHA-256 |
| --- | --- |
| Published Markdown source | `3586129a069973b7a2170c40a10022880b0759ddea6d881620efc15589060ae9` |
| Independently reviewed 22 November Markdown source | `d1f57b29e526ddd3ee1af30cfe41a668bd9861e35ec274f9047cec1152ddb35c` |
| A11 candidate source archive | `0595c5c731ff97f8d0ec38676252825fb77071e3dabe9d28dffa1cc72fe104f4` |
| A11 protected reference archive | `8e23acf0528ef4599b6bcfcc9bccaf8972d31af1340d7856586face71c20e671` |
| A11 candidate export | `bb197c76c2d8ee61479b8d1a0c287e187d1cd5b056a34c1233783e5452a79790` |
| A11 reference export | `97bc9d600ecfefa56656f72a3fb3e94fef90aae6731f95e20722766152b3d2e1` |
| A11 receipt | `c8ca1f69315cd18276ee0148fb4dfb3049b65930598b7dced2f1811c5d1d360b` |
| Independently held acquisition | `51ace3c930cc3fec3e2d5076f672176c101cd2f5b7186ce8f57e0f954615045f` |

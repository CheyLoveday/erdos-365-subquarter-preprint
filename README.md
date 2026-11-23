# A Subquarter Exponent for Consecutive Powerful Numbers

**Chey Loveday · 23 November 2026 · GitHub preprint**

Let $S(X)$ count positive integers $n\le X$ for which both $n$ and $n+1$
are powerful. The paper proves, for every $\varepsilon>0$,

```math
S(X)\ll_{\varepsilon} X^{333/1400+\varepsilon}.
```

The base exponent is below $1/4$. The paper uses Stewart’s published
quantitative Thue theorem. Erdős’s fixed-polylogarithmic question remains open.

## Start here

- [Read the preprint (PDF)](subquarter-preprint.pdf)
- [Follow the proof in the Lamport notes](PROOF_NOTES.md), starting with the [dependency map](PROOF_NOTES.md#dependency-map)
- [See exactly what Lean and odProof verified](FORMAL_VERIFICATION.md)
- [Browse the checked Lean candidate](lean)

The independent Linux replay finished `COMPLETE / PASS` after all 35
controls qualified. Six checker executions covered the candidate export.
A separate protected comparison matched 14 theorem interfaces and four
definition bodies. Lean takes `StewartPrimitiveThue` as an explicit premise.
Independent specialist mathematical review remains pending. [Verification scope](FORMAL_VERIFICATION.md)

## Sources and reproduction

[`source/MANUSCRIPT.md`](source/MANUSCRIPT.md) is the frozen Pandoc Markdown
publication source. The PDF and proof notes are generated reading copies.
[`sources.json`](sources.json) binds the authoring revision and file hashes.
[`verification.json`](verification.json) records the compiler and dependency
pins, the six checker outcomes, control dispositions, axiom sets and receipt
hashes. [Reproduction instructions](FORMAL_VERIFICATION.md#reproduction)

## Citation and rights

Chey Loveday. *A Subquarter Exponent for Consecutive Powerful Numbers*.
GitHub preprint, 23 November 2026. Cite the exact repository commit for this
edition. [Release v1.0.1-preprint](https://github.com/CheyLoveday/erdos-365-subquarter-preprint/releases/tag/v1.0.1-preprint)

Copyright © 2026 Chey Loveday. The paper, proof notes and verification data
are available under **CC BY 4.0**. The original Lean and Python code is
available under **Apache 2.0**. [Licences and file coverage](LICENSE.md)

The paper and Lean formalization involved AI assistance, as described in
the preprint. The author is responsible for the mathematical claims.

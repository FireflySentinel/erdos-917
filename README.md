# Erdős Problem #917: twelve-critical graphs with $(2/5+o(1))n^2$ edges

Preprint disproving the general asymptotic conjecture in
[Erdős Problem #917](https://www.erdosproblems.com/917) at $k=12$, the first case in the
residue class $3\mid k$, which earlier counterexamples did not reach.

[Preprint PDF](paper/PROOF.pdf) · [LaTeX source](paper/PROOF.tex) ·
[Formalization notes](FORMALIZATION.md)

## Build and check

With [Elan](https://github.com/leanprover/elan) installed, run from the repository root:

```sh
lake exe cache get
lake build
lake env lean checks/Check.lean
LEAN_NUM_THREADS=2 lake env leanchecker Erdos917
```

## Exact statement

[`Erdos917.conversion_twelve_critical`](Erdos917/Main.lean) proves that the five-module
construction is twelve-critical: chromatic number 12, and every proper subgraph, including
those missing vertices, is 11-colorable. [`Erdos917.AEHK.counterexample_density`](Erdos917/Counterexample.lean)
gives the limit $e/N^2\to2/5$ and rules out $f_{12}(n)\sim 3n^2/8$.

The existence of the AEHK family of $K_5$-saturated graphs is the external mathematical
input and is not formalized.

## Use of generative AI

GPT-6 Astra was used to generate the mathematical proofs and draft the manuscript.
GPT-5.6 Sol and Claude Opus 5 were used only for editorial review of the exposition.
GPT-6 Astra was run in a research environment containing earlier results produced by
GPT-5.6 Sol and Claude Opus 5, but those earlier results did not contribute to the final
mathematical arguments. The author reviewed the final manuscript and takes full
responsibility for its content.

The Lean formalization was developed with OpenAI Codex (GPT-6).

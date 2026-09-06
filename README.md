# Erdős Problem #917: twelve-critical graphs with $(2/5+o(1))n^2$ edges

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22348353.svg)](https://doi.org/10.5281/zenodo.22348353)
[![Lean](https://github.com/FireflySentinel/erdos-917/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/FireflySentinel/erdos-917/actions/workflows/lean.yml)

Preprint disproving the general asymptotic conjecture in
[Erdős Problem #917](https://www.erdosproblems.com/917) at $k=12$, the first case in the
residue class $3\mid k$, which earlier counterexamples did not reach.

**Qiyuan Gu**, University of Chicago

[Preprint PDF](PROOF.pdf) · [LaTeX source](PROOF.tex) ·
[Lean formalization](Erdos917/Counterexample.lean) · [Build instructions](FORMALIZATION.md)

## What this settles

Erdős Problem #917 asks three separate things about $f_k(n)$, the largest number of edges
in a $k$-critical graph on $n$ vertices:

| | question | status |
|---|---|---|
| (i) | $f_k(n)\gg_k n^2$ for $k\ge 4$? | yes, Toft (1970) |
| (ii) | $f_6(n)\sim n^2/4$? | open; not addressed here |
| (iii) | $f_k(n)\sim\frac12\left(1-\frac{1}{\lfloor k/3\rfloor}\right)n^2$ for $k\ge 6$? | already known to fail for $3\nmid k$; refuted here for $k=12$ |

This paper addresses (iii), at $k=12$:

$$\text{conjectured coefficient } \tfrac12\left(1-\tfrac14\right)=\tfrac38,
\qquad\text{construction}\longrightarrow\tfrac25>\tfrac38 .$$

The case $3\mid k$, where joining $k/3$ equal odd cycles attains the conjectured
coefficient exactly, was the one still standing, and $k=12$ falls in it.

Question (ii) is the $k=6$ instance of (iii), since $\frac12(1-\frac12)=\frac14$. A
counterexample at $k=12$ refutes (iii) as a general formula but leaves that instance
untouched, so whether $f_6(n)\sim n^2/4$ is neither proved nor disproved here.

The coefficient $2/5$ sits below the known upper bounds for $k=12$, which stand above
$0.449$ (Luo, Ma and Yang, [arXiv:2301.01656](https://arxiv.org/abs/2301.01656)).

## Main theorem

**Theorem 1.** There is a sequence of twelve-critical graphs $G_s$ such that

$$|V(G_s)|\to\infty,\qquad e(G_s)=\left(\frac25+o(1)\right)|V(G_s)|^2 .$$

In particular $f_{12}(n)\not\sim 3n^2/8$.

The manuscript defines *twelve-critical* by chromatic number $12$ and
$11$-colorability after deleting any edge. The constructed graphs satisfy the stronger
condition that every proper subgraph is $11$-colorable, also proved in Lean.
The proof exhibits an explicit $11$-coloring after the deletion of each type of edge,
so no critical subgraph has to be extracted.

The construction combines $K_5$-saturated graphs of sublinear maximum degree, the explicit
family of Alon, Erdős, Holzman and Krivelevich with $v=13Q^2+12Q$ and $\Delta=22Q-3$, with
a coloring module of Pegden. Given a $K_5$-saturated $H$ with $\Delta(H)<|H|-1$ and an odd
$h\ge 11$ with $|H|>40h\Delta(H)$, the assembly yields a twelve-critical graph on
$N=5(a+h+2v)$ vertices with $a=2hv$ and $e\ge 10a^2(1-\Delta/v)$. Taking $Q=h^2$ with
$h=3^s$ drives $e/N^2\to 2/5$.

## Lean formalization

Lean 4 formalizes Lemma 2 and the full conversion in Proposition 3: twelve-criticality,
the vertex count, the exact edge count, and its lower bound. It also verifies the
parameter inequalities and the limit $e(G_s)/|V(G_s)|^2\to2/5$ in Theorem 1.
Lean defines $f_{12}$ as the finite extremal maximum under the manuscript's edge-deletion
convention and proves that $f_{12}(n)/n^2$ cannot converge to any $c<2/5$, including $3/8$.
The existence of the AEHK saturated graph family is the external mathematical input,
stated explicitly as [`AEHK.Family`](Erdos917/Counterexample.lean).

[FORMALIZATION.md](FORMALIZATION.md) gives the theorem statements, proof correspondence,
and build commands.

## Use of generative AI

GPT-6 Astra was used to generate the mathematical proofs and draft the manuscript.
GPT-5.6 Sol and Claude Opus 5 were used only for editorial review of the exposition.
GPT-6 Astra was run in a research environment containing earlier results produced by
GPT-5.6 Sol and Claude Opus 5, but those earlier results did not contribute to the final
mathematical arguments. The author reviewed the final manuscript and takes full
responsibility for its content.

The Lean formalization was developed with OpenAI Codex (GPT-6).

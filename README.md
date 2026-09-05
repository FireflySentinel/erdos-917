# Erdős Problem #917 — twelve-critical graphs with $(2/5+o(1))n^2$ edges

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22348353.svg)](https://doi.org/10.5281/zenodo.22348353)

Preprint disproving the **general asymptotic conjecture** in
[Erdős Problem #917](https://www.erdosproblems.com/917) at $k=12$ — the first case in
the residue class $3\mid k$, which earlier counterexamples did not reach.

**Qiyuan Gu**, University of Chicago — <phoenix1203@uchicago.edu>

## Status

| | |
|---|---|
| Manuscript | v2, 6 pages, 5 September 2026 — [`PROOF.pdf`](PROOF.pdf), [`PROOF.tex`](PROOF.tex) |
| DOI | [10.5281/zenodo.22348353](https://doi.org/10.5281/zenodo.22348353) (always the latest version; v2 is [10.5281/zenodo.22349927](https://doi.org/10.5281/zenodo.22349927)) |
| erdosproblems.com | listed **open** as of 5 September 2026, no proof claims submitted |
| Refereeing | not yet refereed |

## What this does and does not settle

Erdős Problem #917 asks three separate things about $f_k(n)$, the largest number of edges
in a $k$-critical graph on $n$ vertices:

| | question | status |
|---|---|---|
| (i) | $f_k(n)\gg_k n^2$ for $k\ge 4$? | **yes** — Toft (1970) |
| (ii) | $f_6(n)\sim n^2/4$? | **open — this paper says nothing about it** |
| (iii) | $f_k(n)\sim\frac12\left(1-\frac{1}{\lfloor k/3\rfloor}\right)n^2$ for $k\ge 6$? | refuted for $3\nmid k$ by Stiebitz (1987); **refuted here for $k=12$** |

This paper addresses **(iii) only**, at $k=12$:

$$\text{conjectured coefficient } \tfrac12\left(1-\tfrac14\right)=\tfrac38,
\qquad\text{construction}\longrightarrow\tfrac25>\tfrac38 .$$

Stiebitz's constructions had already refuted (iii) for $k\not\equiv 0\pmod 3$; the case
$3\mid k$ — where the join of $k/3$ equal odd cycles exactly attains the conjectured
coefficient — was the one still standing. $k=12$ falls in that case.

Note that (ii) is the $k=6$ *instance* of (iii), since $\frac12(1-\frac12)=\frac14$. A
counterexample at $k=12$ refutes (iii) as a general formula but leaves that instance
untouched.

> **The middle question, $f_6(n)\sim n^2/4$, is neither proved nor disproved here.**

The coefficient $2/5$ sits below the known upper bounds: Stiebitz's
$f_k(n)<\mathrm{ex}(n;K_{k-1})$ and the improvement of Luo, Ma and Yang
([arXiv:2301.01656](https://arxiv.org/abs/2301.01656)) both exceed $0.449$ at $k=12$.

## Main theorem

**Theorem 1.** There is a sequence of twelve-critical graphs $G_s$ such that

$$|V(G_s)|\to\infty,\qquad e(G_s)=\left(\frac25+o(1)\right)|V(G_s)|^2 .$$

In particular $f_{12}(n)\not\sim 3n^2/8$.

Here *twelve-critical* means chromatic number $12$ with every proper subgraph
$11$-colorable. The proof exhibits an explicit $11$-coloring after the deletion of each
type of edge, so no critical subgraph has to be extracted.

## Method

The construction combines $K_5$-**saturated** graphs of sublinear maximum degree — the
explicit family of Alon, Erdős, Holzman and Krivelevich, with
$v=13Q^2+12Q$, $\Delta=22Q-3$ — with a **coloring module of Pegden**. Given a
$K_5$-saturated $H$ with $\Delta(H)<|H|-1$ and an odd $h\ge 11$ with $|H|>40h\Delta(H)$,
the assembly yields a twelve-critical graph on $N=5(a+h+2v)$ vertices with $a=2hv$ and
$e\ge 10a^2(1-\Delta/v)$. Taking $Q=h^2$ with $h=3^s$ drives $e/N^2\to 2/5$.

## Use of generative AI

GPT-6 Astra was used to generate the mathematical proofs and draft the manuscript.
GPT-5.6 Sol and Claude Opus 5 were used only for editorial review of the exposition.
GPT-6 Astra was run in a research environment containing earlier results produced by
GPT-5.6 Sol and Claude Opus 5, but those earlier results did not contribute to the final
mathematical arguments. The author reviewed the final manuscript and takes full
responsibility for its content.

## Citation

```bibtex
@misc{gu2026erdos917,
  author       = {Qiyuan Gu},
  title        = {Twelve-critical graphs with $(2/5+o(1))n^2$ edges},
  year         = {2026},
  doi          = {10.5281/zenodo.22348353},
  howpublished = {Preprint, Zenodo},
  note         = {Erd\H{o}s Problem 917}
}
```

Problem statement quoted from T. F. Bloom, *Erdős Problem #917*,
<https://www.erdosproblems.com/917>.

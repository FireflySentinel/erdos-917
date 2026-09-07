# feat(ErdosProblems): formalize problem 917

Fixes #1018.

Add the statements of Erdős Problem 917 and closely related variants.
The external proof refutes the general asymptotic formula at k = 12. The k = 6 question remains open. Toft's quadratic lower bound is recorded as a known result, without a formal-proof attribute pointing to this repository.

Formalization choices:

- Criticality means that deleting any edge lowers the chromatic number, as on the problem page. It does not require the absence of isolated vertices.
- `extremalEdges` is the natural-number supremum over finite graphs; its value is zero for an empty class. The class is finite, so this is the maximum whenever nonempty.
- The bridge proves equivalence with the repository's 11-colorability formulation at k = 12, identifies the two extremal functions, and refutes the proposed limit 3/8.

The external proof attributes link to each declaration in the [proof bridge](https://github.com/FireflySentinel/erdos-917/blob/3a1409ca0f415b4c51287e46f0c8a5406fca0425/checks/FormalConjecturesBridge.lean#L64).
The theorem types use the proposed definitions; the axiom guards allow only
`propext`, `Classical.choice`, and `Quot.sound`.

Validation: `lake --wfail build 'FormalConjectures.ErdosProblems.«917»'`
on Lean 4.33.1; the proof bridge compiles on the proof repository's Lean 4.33.0.
A source comparison checks that the definitions and linked statement types agree.

AI assistance: OpenAI Codex (GPT-6) was used to prepare the statements, proof
bridges, and this draft.

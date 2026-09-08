# The Minimum Q-Order of BFGS with Exact Line Search Is One

Lean 4 formalization of the paper-facing results in *The Minimum Q-Order of
BFGS with Exact Line Search Is One* by Benqi Liu, Chenyi Li, and Zaiwen Wen.
The paper is available as arXiv:2609.00596 (2026).

Contributor: Chenyi Li ([@chenyili0818](https://github.com/chenyili0818)).
Source: <https://github.com/chenyili0818/bfgs-minimum-q-order>.
Paper: <https://arxiv.org/abs/2609.00596>.

## Toolchain

This contribution targets the active ReasBook branch `v4.32.2`:

- Lean: `leanprover/lean4:v4.32.2`
- mathlib: `v4.32.2`
- branch: `v4.32.2`

The supplied source snapshot declared `v4.32.0`; its dependency pins and
toolchain were aligned to the active `v4.32.2` ReasBook branch for this
contribution.

## Scope

The public paper surface is imported by `BFGSMinimumQOrder` and documented by
`Paper.lean`. It covers the exact-line-search quasi-Newton algorithm, the
planar alternating-scale BFGS construction, the smooth localized strongly
convex objective, the universal Q-order lower bound, and the convex Broyden
extension. The reusable analysis and optimization infrastructure is retained
under `ReasLib/`; the imported DFP Wolfe development remains available under
`DFPWolfe/` but is not part of the paper root.

The source repository does not identify intentionally uncovered manuscript
material beyond the modules present in its public `Book` aggregate.

## Formalization snapshot

| Measure | Value |
| --- | ---: |
| Imported Lean source files (excluding dated compatibility roots) | 868 |
| Physical Lean source lines (same scope) | 163,306 |
| Declarations | 4,914 |
| Theorem/lemma/example declarations | 4,108 |
| Other declarations | 806 |
| Proof completion | 4,914 / 4,914 = 100% |
| `sorry` placeholders | 0 |
| `admit` placeholders | 0 |

Declaration counts are measured from the imported source closure by declaration
keyword. The two dated compatibility roots are excluded; ReasBook wrapper
modules are also excluded from these source statistics. Comment text containing
the word `admit` is not a placeholder.

## Validation

From the `ReasBook/` directory on branch `v4.32.2`:

```sh
lake env lean Papers/BFGSMinimumQOrder_Liu_2026/Paper.lean
lake env lean Papers/BFGSMinimumQOrder_Liu_2026/BFGSMinimumQOrder.lean
```

Both commands pass locally; the full project build also passes with
`lake build BFGSMinimumQOrder_Liu_2026` (4,110 jobs).

## Layout

```text
ReasBook/Papers/BFGSMinimumQOrder_Liu_2026/
|-- Paper.lean                 # ReasBook documentation root
|-- BFGSMinimumQOrder.lean     # Stable public aggregate
|-- Book/                      # Paper-facing statements and checks
|-- ReasLib/                   # Reusable analysis and optimization proofs
|-- DFPWolfe/                  # Imported supporting formalization
`-- docs/FORMALIZATION_MAP.md  # Manuscript-to-Lean map
```

The imported DFP Wolfe files retain their Apache License 2.0 notice in
`LICENSES/DFP_wolfe_local-APACHE-2.0.txt`; see `THIRD_PARTY_NOTICES.md` for
attribution details.

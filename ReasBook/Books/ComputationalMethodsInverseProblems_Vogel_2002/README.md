# Computational Methods for Inverse Problems

**Publication:** Source only; not included in the [published catalog](https://optpku.github.io/ReasBook/).

Curtis R. Vogel, first edition (2002), SIAM.

Lean 4 formalization covering the inverse-problem framework, regularization,
Tikhonov methods, iterative methods, spectral filter methods, parameter choice,
variational methods, and iterative solution methods across Chapters 1–9.
The project uses Lean/mathlib `v4.32.0` and keeps the chapter structure of the
book in the `Chap01/` through `Chap09/` directories.

## Contributors

- Yifan Bai (@TTony2019)
- Wanli Ma
- Zichen Wang

Project-level formalization credit is recorded in the [catalog](https://github.com/optpku/ReasBook/blob/90ac3dd3a968313d0da7a3137680aa895af6a69a/README.md#books) and [`book.yml`](book.yml); it is separate from the original reference authors and per-file Lean authorship.

## Statistics

- **Lean files:** 722 `.lean` files, 121,494 lines
- **Theorem/lemma/example declarations:** 3,580
- **Remaining placeholders:** 0 `sorry` or `admit` occurrences
- **Lean toolchain:** `leanprover/lean4:v4.32.0`

## Build

From the repository root, build the complete book:

```bash
lake build ComputationalMethodsInverseProblems_Vogel_2002
```

The book is also included in the default `lake build` targets.
[`Book.lean`](Book.lean) imports all 721 chapter and supporting modules.
All 722 Lean files, the chapter aggregates, and the full-book aggregate compile
successfully with Lean/mathlib `v4.32.0`. An axiom-dependency audit of all
7,234 imported book declarations found no `sorryAx` or additional axioms beyond
Lean’s standard propositional extensionality, classical choice, and quotient soundness.

## Project files

- [`lakefile.lean`](../../lakefile.lean) — repository Lake project configuration
- [`book.yml`](book.yml) — book metadata and statistics
- [`Book.lean`](Book.lean) — aggregate entry point for all formalized chapters
- `Chap01/`–`Chap09/` — chapter-by-chapter formalization

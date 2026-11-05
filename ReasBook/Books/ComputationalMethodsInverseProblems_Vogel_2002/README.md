# Computational Methods for Inverse Problems

**Publication:** Source only; not included in the [published catalog](https://optpku.github.io/ReasBook/).

Curtis R. Vogel, first edition (2002), SIAM.

Lean 4 formalization covering the inverse-problem framework, regularization,
Tikhonov methods, iterative methods, spectral filter methods, parameter choice,
variational methods, and iterative solution methods across Chapters 1–9.
The project uses Lean/mathlib `v4.32.0` and keeps the chapter structure of the
book in the `Chap01/`–`Chap09/` directories.

## Contributors

- Yifan Bai (@TTony2019)
- Wanli Ma
- Zichen Wang

Project-level formalization credit is recorded in the [catalog](https://github.com/optpku/ReasBook/blob/90ac3dd3a968313d0da7a3137680aa895af6a69a/README.md#books) and [`book.yml`](book.yml); it is separate from the original reference authors and per-file Lean authorship.

## Recorded source statistics

These retained source statistics are historical counts, not a new build report.

- **Lean files:** 683 `.lean` files, 114,644 lines
- **Theorem/lemma/example declarations:** 3,109
- **Remaining placeholders:** 105 `sorry` occurrences
- **Lean toolchain:** `leanprover/lean4:v4.32.0`

## Build

The book library is currently disabled in the branch’s [Lake configuration](../../lakefile.lean) because of unresolved mathlib API incompatibilities. It has no enabled aggregate build target in this configuration.

[`Book.lean`](Book.lean) imports all chapter modules. Some source files in the
current snapshot still contain Lean errors and duplicate declarations, so a
full build is not yet clean; the diagnostics identify the affected chapter
files.

## Project files

- [`lakefile.lean`](../../lakefile.lean) — branch Lake configuration and disabled book target
- [`book.yml`](book.yml) — book metadata and statistics
- [`Book.lean`](Book.lean) — aggregate entry point for all formalized chapters
- `Chap01/`–`Chap09/` — chapter-by-chapter formalization

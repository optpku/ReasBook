# Lectures on Convex Optimization

**Published reading (v4.30.0):** [Verso](https://optpku.github.io/ReasBook/versions/v4.30.0/books/introductorylecturesonconvexoptimization_nesterov_2004/) · [Documentation](https://optpku.github.io/ReasBook/versions/v4.30.0/docs/ReasBook/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/Book.html) · [Theorem map](https://optpku.github.io/ReasBook/versions/v4.30.0/theorem-maps/books/introductorylecturesonconvexoptimization_nesterov_2004/)

[Lean source root](Book.lean)

Yurii Nesterov, second edition (2018), Springer.

The seven-chapter layout follows the [2018 second edition](https://link.springer.com/book/10.1007/978-3-319-91578-4),
not the four-chapter 2004 first edition. The historical directory and module ID
`IntroductoryLecturesOnConvexOptimization_Nesterov_2004` is retained for link and
import compatibility; it is not the bibliographic title or publication year.

Lean 4 formalization of the definitions, algorithms, lemmas, and main complexity
results across Chapters 1–7. The imported source is adapted to the stable Lean and
mathlib `v4.30.0` API by the local compatibility layer.

## Contributors

- Chenyi Li (@chenyili0818)
- Siyuan Shao
- Yijie Wang
- Feiming Wang
- Weiran Shi
- Yuhao Jiang
- Zebo Liu
- Wentao Long

Project-level formalization credit is recorded in the [catalog](https://github.com/optpku/ReasBook/blob/90ac3dd3a968313d0da7a3137680aa895af6a69a/README.md#books) and [`book.yml`](book.yml); it is separate from the original reference authors and per-file Lean authorship.

## Recorded source statistics

These retained source statistics are historical counts, not a new build report.

- **Declarations:** 14,663 (theorem/lemma/example: 11,863; other: 2,800)
- **Lean code:** 1,645 `.lean` files, 494,658 lines
- **Proof completion:** 14,587 / 14,663 = 99.48%
- **Remaining placeholders:** `sorry`: 76; `admit`: 0
- **Lean toolchain:** `leanprover/lean4:v4.30.0`

## Metadata

See [`book.yml`](book.yml).

## Published contents

- [Chapter 01 — Nonlinear Optimization](https://optpku.github.io/ReasBook/versions/v4.30.0/books/introductorylecturesonconvexoptimization_nesterov_2004/chapters/chap01/)
- [Chapter 02 — Smooth Convex Optimization](https://optpku.github.io/ReasBook/versions/v4.30.0/books/introductorylecturesonconvexoptimization_nesterov_2004/chapters/chap02/)
- [Chapter 03 — Nonsmooth Convex Optimization](https://optpku.github.io/ReasBook/versions/v4.30.0/books/introductorylecturesonconvexoptimization_nesterov_2004/chapters/chap03/)
- [Chapter 04 — Second-Order Methods](https://optpku.github.io/ReasBook/versions/v4.30.0/books/introductorylecturesonconvexoptimization_nesterov_2004/chapters/chap04/)
- [Chapter 05 — Polynomial-Time Interior-Point Methods](https://optpku.github.io/ReasBook/versions/v4.30.0/books/introductorylecturesonconvexoptimization_nesterov_2004/chapters/chap05/)
- [Chapter 06 — The Primal-Dual Model of an Objective Function](https://optpku.github.io/ReasBook/versions/v4.30.0/books/introductorylecturesonconvexoptimization_nesterov_2004/chapters/chap06/)
- [Chapter 07 — Optimization in Relative Scale](https://optpku.github.io/ReasBook/versions/v4.30.0/books/introductorylecturesonconvexoptimization_nesterov_2004/chapters/chap07/)

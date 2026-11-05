# Smooth Minimization of Non-Smooth Functions

**Published reading (v4.30.0):** [Verso](https://optpku.github.io/ReasBook/versions/v4.30.0/papers/smoothminimization_nesterov_2004/) · [Documentation](https://optpku.github.io/ReasBook/versions/v4.30.0/docs/ReasBook/SmoothMinimization_Nesterov_2004/Paper.html) · [Theorem map](https://optpku.github.io/ReasBook/versions/v4.30.0/theorem-maps/papers/smoothminimization_nesterov_2004/)

**Project-level formalization contributors:** Wanli Ma, Zichen Wang, Zaiwen Wen.

Project-level formalization credit is recorded in the [catalog](https://github.com/optpku/ReasBook/blob/90ac3dd3a968313d0da7a3137680aa895af6a69a/README.md#papers); it is separate from the original reference authors and per-file Lean authorship.

- **Author:** Yurii Nesterov
- **Venue:** Mathematical Programming, Ser. A 103, 127–152 (2005), DOI: 10.1007/s10107-004-0552-5
- **Paper ID:** `SmoothMinimization_Nesterov_2004`
- **Branch/toolchain:** `v4.30.0` / `leanprover/lean4:v4.30.0`

## Contributors

- Wanli Ma (@wl-ma)
- Zichen Wang

## Coverage

Formalization of the paper's results on smooth minimization of non-smooth functions:
smoothing techniques and complexity guarantees for first-order methods.

## Statistics

- **Declarations:** 353 (theorem/lemma/example: 303; other: 50)
- **Lean code:** 27 `.lean` files, 15255 lines
- **Proof completion:** 353/353 (approx)
- **Remaining placeholders:** `sorry`: 0; `admit`: 0

## Build

```bash
cd ReasBook
lake build Papers.SmoothMinimization_Nesterov_2004.Paper
```

## Published contents

- [1. Introduction](https://optpku.github.io/ReasBook/versions/v4.30.0/smoothminimization_nesterov_2004/section01/)
- [2. Smooth Approximations of Non-differentiable Functions](https://optpku.github.io/ReasBook/versions/v4.30.0/smoothminimization_nesterov_2004/section02/)
- [3. Fast Gradient Methods](https://optpku.github.io/ReasBook/versions/v4.30.0/smoothminimization_nesterov_2004/section03/)
- [4. Applications](https://optpku.github.io/ReasBook/versions/v4.30.0/smoothminimization_nesterov_2004/section04/)
- [5. Implementation Issues and Modifications](https://optpku.github.io/ReasBook/versions/v4.30.0/smoothminimization_nesterov_2004/section05/)

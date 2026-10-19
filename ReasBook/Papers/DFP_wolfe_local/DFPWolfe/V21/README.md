# v21 polar proof: verified foundations

This directory indexes the new polar construction in the October 9, 2026
submission (`DFP_MP_20261009_v21_submission.zip`). It is an independent proof
route. The earlier center-manifold formalization remains in the same project.

- **Authors:** Benqi Liu, Zichen Wang, Zaiwen Wen, Liwei Zhang, and Yaxiang Yuan
- **Formalization:** Zichen Wang ([@imathwy](https://github.com/imathwy))
- **Toolchain:** `leanprover/lean4:v4.32.0`, mathlib `v4.32.0`
- **Source snapshot:** [`c788aa3`](https://github.com/imathwy/DFP_wolfe_local/commit/c788aa3dabd6cac78f4ec8b2c9c1e897cbc1188f)
- **Manuscript SHA-256:** `6e6e05b0fae7896b5c944344e28652260d4be010b19616d9058eea5584830188`
- **Entry point:** [`DFPWolfe.V21`](../V21.lean)
- **License:** Apache License, Version 2.0

| Source location | Navigation | Proof modules | Verified content |
| --- | --- | --- | --- |
| Section 3.1 | [PolarData](PolarData.lean) | `DFP.Polar.Parameters` in `Polar.Recurrence` and `Polar.Realization` | Angles, cubic feedback, prescribed matrix recurrence, tail-product radius definitions, points and gradient data. Tail-product convergence is not claimed. |
| Section 3.2 | [NormalizedMap](NormalizedMap.lean) | `Polar.Normalized.Regularization`, `Dynamics`, `Recurrence`, `Regularity` | Canceled factors, exact normalized coordinate transport and recurrence, local analyticity, fixed-compact denominator bounds and uniform Taylor jets. |
| `eq:polar-two-cycle` and its surrounding derivation | [LimitingTwoCycle](LimitingTwoCycle.lean) | `Polar.CycleFamily` and `Polar.TwoCycle` | Rational cycle branch, local inverse, positivity, alternating limiting stages, determinants and reference states. |

All proof modules have prefix `ReasLib.Optimization.DFP.`. The independent
[dependency graph](../../theorem-map/v21/index.html) includes every public
source-declared theorem and lemma in these nine polar proof modules, with
statement and proof edges extracted from the compiled environment. Its scope
is these verified foundations, not the entire v21 manuscript.

This snapshot contains 13 Lean files and 4,127 lines: nine proof modules,
three source-facing navigation files and the independent import root.
There are 301 declaration heads (152 theorems, 68 lemmas, 80 definitions and
one structure), including private declarations. Source scans find zero `sorry`,
`admit`, `sorryAx` or custom `axiom` tokens outside comments and strings.
The declared foundations are proved; this is not a whole-paper completion ratio.

The restoring slow drift, contraction estimates and forward-invariant tube,
infinite-product estimates, near/far separation, explicit cutoff interpolation,
Wolfe ratios and final v21 counterexample theorem remain outside this snapshot.
The existing center-manifold counterexample theorem does not discharge these
v21 proof obligations. No new theorem numbered 1–8 is asserted here.

The original eight Verso routes are retained. Three additional routes display
the polar recurrence, normalized-map regularity and limiting two-cycle source.
The complete project `Paper.lean` imports both proof routes for API generation;
Docs and Verso sites must be rebuilt together after this source PR is merged.

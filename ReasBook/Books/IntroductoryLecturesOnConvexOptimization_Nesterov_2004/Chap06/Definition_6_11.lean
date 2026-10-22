/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Definition 6.11 lies in the finite convex/simplex domain.

Sampled owner declarations:
* mathlib `stdSimplex`, the canonical owner of the standard simplex;
* mathlib `stdSimplex_eq_inter`, the canonical decomposition into nonnegativity and mass-one
  constraints;
* mathlib `mem_Icc_of_mem_stdSimplex`, a standard derived bound for simplex coordinates;
* project `Definition_5_4_7_16`, which already recalls the same owner in finite-dimensional
  coordinates and exports the shared notation `Δ[n]`.

Best owner abstraction:
* source-facing: the textbook simplex `Δ_n`;
* core/canonical: `stdSimplex 𝕜 ι`;
* bridge/view: the real-coordinate notation `Δ[n] = stdSimplex ℝ (Fin n)`, already owned by
  `Definition_5_4_7_16`.

Primitive data:
* the coefficient type `𝕜`;
* the finite index type `ι`.

Derived API:
* the set-builder characterization of simplex membership;
* the shared source-facing notation `Δ[n]` for the real `Fin n` specialization.

Source/core/bridge triage:
* this file remains a core/canonical recall of `stdSimplex`;
* the notation `Δ[n]` is the shared source-facing bridge reused by Chapter 6 statements, not a
  second owner layer.
-/

open scoped StandardSimplex

/- The source-facing simplex notation is the canonical real `Fin n` specialization. -/
example (n : ℕ) : Set (Fin n → ℝ) := Δ[n]

/- Definition 6.11: the standard simplex `Δ_n` is the canonical mathlib set
`Δ[n] = stdSimplex ℝ (Fin n)`, and in general `stdSimplex 𝕜 ι` is the set of functions with
nonnegative coordinates and total sum equal to `1`. -/
recall stdSimplex (𝕜 : Type v) (ι : Type u) [Semiring 𝕜] [PartialOrder 𝕜] [Fintype ι] : Set (ι → 𝕜)

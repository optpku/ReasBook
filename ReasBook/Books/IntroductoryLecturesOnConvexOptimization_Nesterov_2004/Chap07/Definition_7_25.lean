/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_11

open scoped StandardSimplex

section

variable (n : ℕ)

/- Definition 7.25 lies in the finite-dimensional simplex domain.

Sampled owner declarations:
* mathlib `stdSimplex`, the canonical owner of the standard simplex;
* mathlib `stdSimplex_eq_inter`, the canonical set-level decomposition of the same owner;
* project `Definition_6_11`, which already fixes the chapter-level notation `Δ[n]`;
* project `Definition_5_4_7_16`, which already recalls the same owner without a parallel local
  theorem.

Best owner abstraction:
* source-facing: the textbook simplex `Δ_n` in `ℝⁿ`;
* core/canonical: `stdSimplex ℝ (Fin n)`;
* bridge/view: the Chapter 6 notation `Δ[n]` and the definitional set-builder expansion of the
  simplex owner.

Primitive data:
* the dimension `n`.

Derived API:
* the notation `Δ[n] : Set (Fin n → ℝ)`;
* the definitional characterization of `Δ[n]` by coordinatewise nonnegativity and total mass `1`.

Source/core/bridge triage:
* this file is a `bridge/view` recall only;
* it reuses the earlier project simplex surface instead of restating the same theorem under a new
  Chapter 7 wrapper.
-/

/- Definition 7.25 uses the chapter-level notation `Δ[n]` for the canonical simplex owner. -/
#check (Δ[n] : Set (Fin n → ℝ))

/- The source-facing set-builder description is the definitional expansion of the canonical
simplex owner. -/
#check
  (show Δ[n] = {x : Fin n → ℝ | (∀ i : Fin n, 0 ≤ x i) ∧ ∑ i : Fin n, x i = 1} from rfl)

end

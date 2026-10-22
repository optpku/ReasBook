/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DikinEllipsoidNotation Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Proposition 5.0.31 lies in the Chapter 5 self-concordance / Dikin-ellipsoid domain.

Sampled owner declarations:
* `openDikinEllipsoid` and the notation `W⁰[f; x](r)` in `Definition_5_0_13`, the chapter owner
  and textbook surface for the local quadratic neighborhood;
* `mem_openDikinEllipsoid_inv_constant_iff_hessian_quadratic_lt_inv_sq` in
  `Definition_5_0_14`, the source-facing inverse-parameter quadratic bridge;
* `IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset` in `Theorem_5_1_5`, the
  canonical owner-level domain-inclusion theorem;
* `IsSelfConcordantOnWith.hessian_posSemidef` in `Definition_5_1_1`, which supplies the
  nonnegativity needed by the quadratic bridge.

Source/core/bridge triage:
* source-facing: the textbook inverse-Hessian quadratic neighborhood centered at `sBar`,
  together with the degenerate-point corollary at `0`;
* core/canonical: `W⁰[f; sBar](1 / (Mf : ℝ))` and
  `IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset`;
* bridge/view: the quadratic membership reformulation from `Definition_5_0_14`.

Primitive data:
* a domain `dom`, a self-concordance constant `Mf`, a function `f`, and a center `sBar`;
* the bundled owner hypothesis `IsSelfConcordantOnWith dom Mf f`;
* the displayed inverse-square Hessian quadratic inequality.

Derived API:
* the canonical Dikin neighborhood `W⁰[f; sBar](1 / (Mf : ℝ))`;
* the inverse-square quadratic reformulation of that neighborhood;
* the domain-membership conclusion.

This file therefore recalls the canonical Dikin-owner inclusion theorem directly and keeps only
the genuine quadratic-inequality bridge as new source-facing API. -/

/- Proposition 5.0.31 uses the canonical Dikin-owner inclusion theorem
`IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset` for the neighborhood
`W⁰[f; sBar](1 / (Mf : ℝ))`. -/
recall IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset

-- Proof sketch: rewrite the displayed quadratic bound as membership of `s` in the canonical
-- Dikin ellipsoid `W⁰[f; s̄](1 / M_f)` via the inverse-parameter quadratic bridge from
-- `Definition_5_0_14`, then apply the owner-level inclusion theorem
-- `IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset`. When `Mf = 0`, the bridge
-- identifies the displayed neighborhood with the empty Dikin ellipsoid, so the inclusion remains
-- vacuous without an extra positivity binder.
/-- Proposition 5.0.31: for a self-concordant function on an open convex domain `dom`, the
quadratic neighborhood `{s | ⟪s - s̄, ∇²f(s̄) (s - s̄)⟫ < 1 / M_f^2}` centered at `s̄ ∈ dom` is
contained in `dom`. Via Definition 5.0.14, this is the source-facing quadratic reformulation of
the canonical Dikin neighborhood `W⁰[f; sBar](1 / (Mf : ℝ))`. -/
theorem selfConcordant_quadratic_neighborhood_subset_domain
    (dom : Set E) {Mf : NNReal} {f : E → ℝ}
    [IsSelfConcordantOnWith dom Mf f]
    {sBar : E} (hsBar : sBar ∈ dom) :
    {s : E |
        inner ℝ (s - sBar) (hessian f sBar (s - sBar)) <
          1 / (Mf : ℝ) ^ (2 : ℕ)} ⊆
      dom := by
  intro s hs
  have hself : IsSelfConcordantOnWith dom Mf f := inferInstance
  have hsW : s ∈ W⁰[f; sBar](1 / (Mf : ℝ)) := by
    refine
      (mem_openDikinEllipsoid_inv_constant_iff_hessian_quadratic_lt_inv_sq
        f sBar s Mf (hself.hessian_posSemidef hsBar (s - sBar))).2 hs
  exact hself.openDikinEllipsoid_inv_constant_subset hsBar hsW

-- Proof sketch: apply `selfConcordant_quadratic_neighborhood_subset_domain` to the point `0`.
-- The displayed hypothesis is exactly the same quadratic inequality after simplifying
-- `0 - s̄ = -s̄` and the Hessian quadratic form in the displacement vector.
/-- If the Hessian quadratic form of the displacement from `s̄` to the origin is less than
`1 / M_f^2`, then the origin belongs to the domain. -/
theorem zero_mem_domain_of_selfConcordant_quadratic_neighborhood
    (dom : Set E) {Mf : NNReal} {f : E → ℝ}
    [IsSelfConcordantOnWith dom Mf f]
    {sBar : E} (hsBar : sBar ∈ dom)
    (hquad :
      inner ℝ sBar (hessian f sBar sBar) <
        1 / (Mf : ℝ) ^ (2 : ℕ)) :
    (0 : E) ∈ dom := by
  have hsubset :
      {s : E |
          inner ℝ (s - sBar) (hessian f sBar (s - sBar)) <
            1 / (Mf : ℝ) ^ (2 : ℕ)} ⊆ dom :=
    selfConcordant_quadratic_neighborhood_subset_domain dom hsBar
  exact hsubset (by simpa using hquad)

end

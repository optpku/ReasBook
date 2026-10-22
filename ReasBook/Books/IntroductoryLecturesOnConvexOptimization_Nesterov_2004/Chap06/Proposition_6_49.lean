/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_30

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 6.49 lies in the strong-convexity / affine-perturbation minimization domain on
real inner-product spaces.

Mandatory domain-style sampling:
- project `StrongConvexOn.quadratic_growth_of_isMinOn_of_mem` in `Chap02/Theorem_2_30`, the
  canonical quadratic-growth owner at a feasible minimizer;
- project `StrongConvexOn.add_convexOn` in `Chap02/Proposition_2_3`, the canonical bridge adding
  a convex perturbation to a strongly convex objective;
- mathlib `LinearMap.convexOn`, the owner convexity API for linear functionals;
- mathlib `innerSL`, the canonical linear functional `x ↦ ⟪g, x⟫`.

Best owner abstraction:
- source-facing: Proposition 6.49's strengthened variational inequality for an affine perturbation
  of a strongly convex objective;
- core/canonical: `StrongConvexOn Q σΨ Ψ` together with `IsMinOn`;
- bridge/view: the affine perturbation `x ↦ Ψ x + inner ℝ g x`.

Primitive data:
- the feasible set `Q`, strong-convexity owner `hΨ_strong`, perturbation vector `g`, minimizer
  candidate `v_t`, and comparison point `x`.

Derived API:
- convexity of `x ↦ inner ℝ g x`;
- strong convexity of the affine perturbation via `StrongConvexOn.add_convexOn`;
- quadratic growth of the perturbed objective at the feasible minimizer `v_t`.

The previous version duplicated the owner proof locally, repeated redundant convexity/positivity
binders already subsumed by the owner abstraction, and fixed the statement to `EuclideanSpace`
coordinates although only the real inner-product-space owner layer is used. This refinement keeps
the source-facing proposition, makes feasibility of `v_t` explicit because `IsMinOn` does not
include membership, and derives the inequality directly from the Chapter 2 owner theorem.
-/

-- Proof sketch: set `Φ x = Ψ x + inner ℝ g x`. The linear term is affine, so `Φ` remains
-- `σΨ`-strongly convex on `Q`. Apply strong convexity to the segment from `v_t` to any feasible
-- `x`, use the minimizing property of `v_t` to compare `Φ v_t` with the segment value, rearrange,
-- divide by the segment parameter, and let the parameter tend to `0`.
/-- Proposition 6.49: if `Ψ` is `σΨ`-strongly convex on the feasible set `Q` and the feasible
point `v_t ∈ Q` minimizes the affine perturbation `x ↦ Ψ x + ⟪g, x⟫` over `Q`, then every
feasible point satisfies the strengthened variational inequality
`Ψ x + ⟪g, x - v_t⟫ ≥ Ψ v_t + (σΨ / 2) * ‖x - v_t‖²`. -/
theorem strongConvexOn_variational_inequality_of_affine_isMinOn
    {Q : Set E} {Ψ : E → ℝ} {σΨ : ℝ} {g v_t x : E}
    (hΨ_strong : StrongConvexOn Q σΨ Ψ)
    (hv_t_mem : v_t ∈ Q)
    (hv_t : IsMinOn (fun y ↦ Ψ y + inner ℝ g y) Q v_t)
    (hx : x ∈ Q) :
    Ψ x + inner ℝ g (x - v_t) ≥
      Ψ v_t + (σΨ / 2) * ‖x - v_t‖ ^ (2 : ℕ) := by
  have hinner_convex : ConvexOn ℝ Q (fun y : E ↦ inner ℝ g y) := by
    simpa using (innerSL ℝ g).convexOn hΨ_strong.1
  have hperturbed_strong : StrongConvexOn Q σΨ (fun y : E ↦ inner ℝ g y + Ψ y) := by
    simpa [Pi.add_apply, add_comm] using hΨ_strong.add_convexOn hinner_convex
  have hv_t' : IsMinOn (fun y : E ↦ inner ℝ g y + Ψ y) Q v_t := by
    simpa [add_comm] using hv_t
  have hquad :
      inner ℝ g x + Ψ x ≥
        inner ℝ g v_t + Ψ v_t + (σΨ / 2) * ‖x - v_t‖ ^ (2 : ℕ) :=
    hperturbed_strong.quadratic_growth_of_isMinOn_of_mem hv_t_mem hv_t' x hx
  have hinner_sub : inner ℝ g (x - v_t) = inner ℝ g x - inner ℝ g v_t := by
    rw [inner_sub_right]
  nlinarith [hquad, hinner_sub]

end

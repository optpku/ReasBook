/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open Set Topology
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace IsSelfConcordantBarrierOnWith

-- Proof sketch: the standard self-concordance component is the owner theorem
-- `IsStandardSelfConcordantOn.add`. For the barrier parameter, expand the gradient and Hessian of
-- the sum at `x ∈ dom₁ ∩ dom₂`; the displayed expression splits into the two summand barrier
-- expressions, which are bounded by `ν₁` and `ν₂`.
/-- Theorem 5.3.2: the pointwise sum of a `ν₁`-self-concordant barrier `F₁` on `dom₁` and a
`ν₂`-self-concordant barrier `F₂` on `dom₂` is a `(\nu₁ + \nu₂)`-self-concordant barrier on the
intersection domain `dom₁ ∩ dom₂`. -/
theorem add
    {dom₁ dom₂ : Set E} {ν₁ ν₂ : NNReal} {F₁ F₂ : E → ℝ}
    (h₁ : IsSelfConcordantBarrierOnWith dom₁ ν₁ F₁)
    (h₂ : IsSelfConcordantBarrierOnWith dom₂ ν₂ F₂) :
    IsSelfConcordantBarrierOnWith (dom₁ ∩ dom₂) (ν₁ + ν₂) (F₁ + F₂) := by
  let hself₁ : IsStandardSelfConcordantOn dom₁ F₁ := h₁.toIsStandardSelfConcordantOn
  let hself₂ : IsStandardSelfConcordantOn dom₂ F₂ := h₂.toIsStandardSelfConcordantOn
  refine
    { toIsStandardSelfConcordantOn := by simpa using hself₁.add hself₂
      barrier_parameter_bound := ?_ }
  intro x hx u
  rcases hx with ⟨hx₁, hx₂⟩
  have hbound₁ := h₁.barrier_parameter_bound hx₁ u
  have hbound₂ := h₂.barrier_parameter_bound hx₂ u
  have hF₁ : DifferentiableAt ℝ F₁ x := by
    exact
      (hself₁.contDiffOn.contDiffAt (hself₁.isOpen_domain.mem_nhds hx₁)).differentiableAt
        (by norm_num)
  have hF₂ : DifferentiableAt ℝ F₂ x := by
    exact
      (hself₂.contDiffOn.contDiffAt (hself₂.isOpen_domain.mem_nhds hx₂)).differentiableAt
        (by norm_num)
  have hgrad : ∇ (F₁ + F₂) x = ∇ F₁ x + ∇ F₂ x := by
    rw [gradient, fderiv_add hF₁ hF₂]
    simp [gradient]
  have hF₁_c2 : ContDiffOn ℝ 2 F₁ dom₁ := hself₁.contDiffOn.of_le (by norm_num)
  have hF₂_c2 : ContDiffOn ℝ 2 F₂ dom₂ := hself₂.contDiffOn.of_le (by norm_num)
  have hfderiv₁ : DifferentiableAt ℝ (fderiv ℝ F₁) x := by
    exact
      ((hF₁_c2.fderiv_of_isOpen hself₁.isOpen_domain
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableOn
        (by simp) x hx₁).differentiableAt (hself₁.isOpen_domain.mem_nhds hx₁)
  have hfderiv₂ : DifferentiableAt ℝ (fderiv ℝ F₂) x := by
    exact
      ((hF₂_c2.fderiv_of_isOpen hself₂.isOpen_domain
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableOn
        (by simp) x hx₂).differentiableAt (hself₂.isOpen_domain.mem_nhds hx₂)
  have hgradF₁ : DifferentiableAt ℝ (∇ F₁) x := by
    unfold gradient
    simpa using ((InnerProductSpace.toDual ℝ E).symm.differentiableAt.comp x hfderiv₁)
  have hgradF₂ : DifferentiableAt ℝ (∇ F₂) x := by
    unfold gradient
    simpa using ((InnerProductSpace.toDual ℝ E).symm.differentiableAt.comp x hfderiv₂)
  have hgrad_nhds : (fun y ↦ ∇ (F₁ + F₂) y) =ᶠ[𝓝 x] fun y ↦ ∇ F₁ y + ∇ F₂ y := by
    filter_upwards [hself₁.isOpen_domain.mem_nhds hx₁, hself₂.isOpen_domain.mem_nhds hx₂] with
      y hy₁ hy₂
    have hFy₁ : DifferentiableAt ℝ F₁ y := by
      exact
        (hself₁.contDiffOn.contDiffAt (hself₁.isOpen_domain.mem_nhds hy₁)).differentiableAt
          (by norm_num)
    have hFy₂ : DifferentiableAt ℝ F₂ y := by
      exact
        (hself₂.contDiffOn.contDiffAt (hself₂.isOpen_domain.mem_nhds hy₂)).differentiableAt
          (by norm_num)
    rw [gradient, fderiv_add hFy₁ hFy₂]
    simp [gradient]
  have hhess : hessian (F₁ + F₂) x = hessian F₁ x + hessian F₂ x := by
    rw [hessian, hgrad_nhds.fderiv_eq, fderiv_fun_add hgradF₁ hgradF₂]
  calc
    2 * inner ℝ (∇ (F₁ + F₂) x) u - inner ℝ u (hessian (F₁ + F₂) x u)
        = (2 * inner ℝ (∇ F₁ x) u - inner ℝ u (hessian F₁ x u)) +
            (2 * inner ℝ (∇ F₂ x) u - inner ℝ u (hessian F₂ x u)) := by
          rw [hgrad, hhess]
          simp [inner_add_left, inner_add_right, ContinuousLinearMap.add_apply, two_mul,
            sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ ≤ (ν₁ : ℝ) + (ν₂ : ℝ) := add_le_add hbound₁ hbound₂
    _ = ((ν₁ + ν₂ : NNReal) : ℝ) := by exact_mod_cast rfl

end IsSelfConcordantBarrierOnWith

end

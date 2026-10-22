/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Fact_2_35
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Text_2_0_10

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped InnerProductSpace Topology

universe u v

variable {A : Type v} [Preorder A] [IsDirectedOrder A]
variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

omit [IsDirectedOrder A] in
private theorem weakConvergence_iff_forall_tendsto_inner_right_aux
    [CompleteSpace 𝓗] (ξ : A → 𝓗) (x : 𝓗) :
    Tendsto (fun a ↦ toWeakSpace ℝ 𝓗 (ξ a)) atTop (𝓝 (toWeakSpace ℝ 𝓗 x)) ↔
      ∀ u : 𝓗, Tendsto (fun a ↦ ⟪ξ a, u⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ) := by
  have hinj : Function.Injective ((topDualPairing ℝ 𝓗).flip) := by
    intro y z hyz
    exact (SeparatingDual.eq_iff_forall_dual_eq).2 fun l ↦ DFunLike.congr_fun hyz l
  constructor
  · intro hξ u
    exact ((weakSpace_continuous_inner_right u).tendsto (toWeakSpace ℝ 𝓗 x)).comp hξ
  · intro hξ
    refine (WeakBilin.tendsto_iff_forall_eval_tendsto ((topDualPairing ℝ 𝓗).flip) hinj).2 ?_
    intro l
    let u : 𝓗 := (InnerProductSpace.toDual ℝ 𝓗).symm (WeakDual.toStrongDual l)
    have hu : Tendsto (fun a ↦ ⟪ξ a, u⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ) := hξ u
    have hξeq : ∀ a, l (toWeakSpace ℝ 𝓗 (ξ a)) = ⟪ξ a, u⟫_ℝ := by
      intro a
      change WeakDual.toStrongDual l (ξ a) = _
      rw [← InnerProductSpace.toDual_symm_apply, real_inner_comm]
    have hxeq : l (toWeakSpace ℝ 𝓗 x) = ⟪x, u⟫_ℝ := by
      change WeakDual.toStrongDual l x = _
      rw [← InnerProductSpace.toDual_symm_apply, real_inner_comm]
    change Tendsto (fun a ↦ l (toWeakSpace ℝ 𝓗 (ξ a))) atTop (𝓝 (l (toWeakSpace ℝ 𝓗 x)))
    rw [show (fun a ↦ l (toWeakSpace ℝ 𝓗 (ξ a))) = fun a ↦ ⟪ξ a, u⟫_ℝ by
      funext a
      exact hξeq a]
    rw [hxeq]
    exact hu

omit [IsDirectedOrder A] in
private theorem tendsto_infDist_hyperplane_iff_tendsto_inner_right
    (ξ : A → 𝓗) (x u : 𝓗) (hu : u ≠ 0) :
    Tendsto (fun a ↦ Metric.infDist (ξ a) (innerProductLevelSet u ⟪x, u⟫_ℝ)) atTop (𝓝 0) ↔
      Tendsto (fun a ↦ ⟪ξ a, u⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ) := by
  constructor
  · intro hdist
    have hdist' : Tendsto
        (fun a ↦ |⟪ξ a, u⟫_ℝ - ⟪x, u⟫_ℝ| / ‖u‖) atTop (𝓝 0) := by
      simpa [infDist_hyperplane_eq_abs_inner_sub_div_norm, hu] using hdist
    have hnorm : Tendsto (fun a ↦ ‖⟪ξ a, u⟫_ℝ - ⟪x, u⟫_ℝ‖) atTop (𝓝 0) := by
      have hmul :=
        hdist'.mul (tendsto_const_nhds : Tendsto (fun _ : A ↦ ‖u‖) atTop (𝓝 ‖u‖))
      simpa [Real.norm_eq_abs, div_mul_cancel₀ _ (show ‖u‖ ≠ 0 by simpa using hu)] using hmul
    have hsub : Tendsto (fun a ↦ ⟪ξ a, u⟫_ℝ - ⟪x, u⟫_ℝ) atTop (𝓝 0) :=
      (tendsto_zero_iff_norm_tendsto_zero).2 hnorm
    simpa using
      hsub.add (tendsto_const_nhds : Tendsto (fun _ : A ↦ ⟪x, u⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ))
  · intro hξ
    have hsub : Tendsto (fun a ↦ ⟪ξ a, u⟫_ℝ - ⟪x, u⟫_ℝ) atTop (𝓝 0) := by
      simpa [sub_eq_add_neg] using
        hξ.add (tendsto_const_nhds : Tendsto (fun _ : A ↦ -⟪x, u⟫_ℝ) atTop (𝓝 (-⟪x, u⟫_ℝ)))
    have hnorm : Tendsto (fun a ↦ ‖⟪ξ a, u⟫_ℝ - ⟪x, u⟫_ℝ‖) atTop (𝓝 0) := by
      simpa using hsub.norm
    have hdist' : Tendsto
        (fun a ↦ ‖u‖⁻¹ * ‖⟪ξ a, u⟫_ℝ - ⟪x, u⟫_ℝ‖) atTop (𝓝 0) := by
      simpa using
        (tendsto_const_nhds : Tendsto (fun _ : A ↦ ‖u‖⁻¹) atTop (𝓝 ‖u‖⁻¹)).mul hnorm
    simpa [infDist_hyperplane_eq_abs_inner_sub_div_norm, hu, Real.norm_eq_abs,
      div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdist'

omit [IsDirectedOrder A] [InnerProductSpace ℝ 𝓗] in
/-- Remark 2.31 (1): strong convergence of a net to `x` is equivalent to the distance
`dist (ξ a) x` tending to `0`. -/
theorem strongConvergence_iff_tendsto_dist (ξ : A → 𝓗) (x : 𝓗) :
    Tendsto ξ atTop (𝓝 x) ↔ Tendsto (fun a ↦ dist (ξ a) x) atTop (𝓝 0) := by
  simpa using (tendsto_iff_dist_tendsto_zero : Tendsto ξ atTop (𝓝 x) ↔ _)

omit [IsDirectedOrder A] [InnerProductSpace ℝ 𝓗] in
/-- Remark 2.31 (1): strong convergence of a net to `x` is equivalent to convergence to `0` of the
distance from the net to the singleton `{x}`. -/
theorem strongConvergence_iff_tendsto_infDist_singleton (ξ : A → 𝓗) (x : 𝓗) :
    Tendsto ξ atTop (𝓝 x) ↔
      Tendsto (fun a ↦ Metric.infDist (ξ a) ({x} : Set 𝓗)) atTop (𝓝 0) := by
  simpa [Metric.infDist_singleton] using strongConvergence_iff_tendsto_dist ξ x

omit [IsDirectedOrder A] in
/-- A net converges weakly to `x` exactly when all scalar inner-product coordinates against fixed
vectors converge to the corresponding coordinate of `x`. -/
theorem weakConvergence_iff_forall_tendsto_inner_right
    [CompleteSpace 𝓗] (ξ : A → 𝓗) (x : 𝓗) :
    Tendsto (fun a ↦ toWeakSpace ℝ 𝓗 (ξ a)) atTop (𝓝 (toWeakSpace ℝ 𝓗 x)) ↔
      ∀ u : 𝓗, Tendsto (fun a ↦ ⟪ξ a, u⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ) :=
  weakConvergence_iff_forall_tendsto_inner_right_aux ξ x

omit [IsDirectedOrder A] in
/-- Remark 2.31 (2): weak convergence of a net to `x` is equivalent to convergence to `0` of the
distance to every closed hyperplane through `x`, encoded as
`innerProductLevelSet u ⟪x, u⟫_ℝ` with `u ≠ 0`. -/
theorem weakConvergence_iff_forall_tendsto_infDist_hyperplane
    [CompleteSpace 𝓗] (ξ : A → 𝓗) (x : 𝓗) :
    Tendsto (fun a ↦ toWeakSpace ℝ 𝓗 (ξ a)) atTop (𝓝 (toWeakSpace ℝ 𝓗 x)) ↔
      ∀ u : 𝓗, u ≠ 0 →
        Tendsto (fun a ↦ Metric.infDist (ξ a) (innerProductLevelSet u ⟪x, u⟫_ℝ)) atTop (𝓝 0) := by
  rw [weakConvergence_iff_forall_tendsto_inner_right]
  constructor
  · intro hξ u hu
    exact (tendsto_infDist_hyperplane_iff_tendsto_inner_right ξ x u hu).2 (hξ u)
  · intro hξ u
    by_cases hu : u = 0
    · simpa [hu] using (tendsto_const_nhds : Tendsto (fun _ : A ↦ (0 : ℝ)) atTop (𝓝 0))
    · exact (tendsto_infDist_hyperplane_iff_tendsto_inner_right ξ x u hu).1 (hξ u hu)

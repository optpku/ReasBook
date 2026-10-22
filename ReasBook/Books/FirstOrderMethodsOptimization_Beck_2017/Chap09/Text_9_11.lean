/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_1
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_53
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_39
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open InnerProductSpace (toDualMap)

universe u

section IndicatorScalar

variable {α : Type u}

/-- For a positive stepsize `t`, scaling the indicator `δ_ C` by `t` leaves it unchanged. -/
theorem smul_extendedIndicator_eq_of_pos (C : Set α) {t : ℝ} (ht : 0 < t) :
    (((t : EReal) • δ_ C) : α → EReal) = δ_ C := by
  let tPos : PosReal := ⟨t, ht⟩
  simpa [tPos] using smul_extendedIndicator_eq C tPos

end IndicatorScalar

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "ω₂" => (fun z : E ↦ (((‖z‖ ^ (2 : ℕ) / 2 : ℝ) : EReal)))

/- Text 9.11 is a `bridge/view` item in the Chapter 9 Mirror-C / Chapter 6 proximal-projection
domain. The source-facing owner for the one-step Mirror-C argmin is already
`mirror_c_update_objective` from Definition 9.6, while the Chapter 6 canonical owners on the
proximal side are `prox[...]`, `smul_extendedIndicator_eq`, and
`prox_scaledExtendedIndicator_eq_singleton_metricProjection`. The primitive data in this file are
therefore only the Euclidean specialization `ω(x) = ‖x‖² / 2` and the Riesz identification of the
chosen subgradient with `toDualMap ℝ E gradf`; the explicit Euclidean formula is derived API
rather than a second owner definition. -/

-- Proof sketch: expand `mirror_c_update_objective` at `ω₂`, use the Riesz identification
-- `((toDualMap ℝ E gradf) x : ℝ) = ⟪gradf, x⟫`, and complete the square around the forward point
-- `xk - t • gradf`.
/-- Helper for Text 9.11: in the Euclidean specialization `ω₂(x) = ‖x‖² / 2`, the Mirror-C
problem functional with chosen strong-dual subgradient `toDualMap ℝ E gradf` evaluates to the
inner-product linear form against `t • gradf - xk`. -/
theorem mirror_c_problem_functional_half_squared_norm_apply
    (xk gradf x : E) (t : ℝ) :
    mirror_c_problem_functional ω₂ xk (toDualMap ℝ E gradf) t x =
      inner ℝ (t • gradf - xk) x := by
  -- Evaluate the owner and identify the quadratic derivative with the Riesz map at `xk`.
  rw [mirror_c_problem_functional_apply]
  have hderiv :
      fderiv ℝ (fun y : E ↦ (ω₂ y).toReal) xk = toDualMap ℝ E xk := by
    change fderiv ℝ (fun y : E ↦ ‖y‖ ^ (2 : ℕ) / 2) xk = toDualMap ℝ E xk
    have hfd : HasFDerivAt (fun y : E ↦ ‖y‖ ^ (2 : ℕ) / 2) (toDualMap ℝ E xk) xk := by
      convert (((hasStrictFDerivAt_norm_sq xk).hasFDerivAt).const_smul (1 / 2 : ℝ)) using 1
      · funext y
        rw [Pi.smul_apply, smul_eq_mul]
        ring
      · ext y
        simp [ContinuousLinearMap.smul_apply, InnerProductSpace.toDualMap_apply_apply]
    exact hfd.fderiv
  rw [hderiv, InnerProductSpace.toDualMap_apply_apply, InnerProductSpace.toDualMap_apply_apply,
    inner_sub_left, real_inner_smul_left]

/-- Evaluating the canonical Mirror-C owner at the Euclidean specialization `ω₂(x) = ‖x‖² / 2`
gives the Chapter 6 proximal objective for `((t : EReal) • g)` at the forward-subgradient point
`xk - t • gradf`, up to the additive constant `-‖xk - t • gradf‖² / 2`. -/
theorem mirror_c_update_objective_half_squared_norm_apply
    (g : E → EReal) (xk gradf x : E) (t : ℝ) :
    mirror_c_update_objective g ω₂ xk (toDualMap ℝ E gradf) t x =
      proximal_objective ((t : EReal) • g) (xk - t • gradf) x -
        (((‖xk - t • gradf‖ ^ (2 : ℕ) / 2 : ℝ) : EReal)) := by
  let u : E := xk - t • gradf
  have hu : t • gradf - xk = -u := by
    dsimp [u]
    abel
  have hquad := quadratic_translate_identity (0 : E) u x
  rw [sub_zero, sub_zero] at hquad
  rw [inner_sub_right, real_inner_self_eq_norm_sq] at hquad
  -- Complete the square around the forward point `u = xk - t • gradf`.
  have hreal :
      inner ℝ (t • gradf - xk) x + ‖x‖ ^ (2 : ℕ) / 2 =
        ‖x - u‖ ^ (2 : ℕ) / 2 - ‖u‖ ^ (2 : ℕ) / 2 := by
    rw [hu, inner_neg_left]
    nlinarith [hquad]
  have hcombine :
      (((inner ℝ (t • gradf - xk) x : ℝ) : EReal) + ω₂ x) =
        (((inner ℝ (t • gradf - xk) x + ‖x‖ ^ (2 : ℕ) / 2 : ℝ) : EReal)) := by
    rw [show ω₂ x = (((‖x‖ ^ (2 : ℕ) / 2 : ℝ) : EReal)) by rfl, ← EReal.coe_add]
  have hrealEReal :
      (((inner ℝ (t • gradf - xk) x + ‖x‖ ^ (2 : ℕ) / 2 : ℝ) : EReal)) =
        ((((‖x - u‖ ^ (2 : ℕ) / 2 : ℝ) : EReal)) -
          (((‖u‖ ^ (2 : ℕ) / 2 : ℝ) : EReal))) := by
    rw [← EReal.coe_sub]
    exact congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) hreal
  have hhalfDistance :
      ((((1 / 2 : ℝ) * ‖x - u‖ ^ (2 : ℕ) : ℝ) : EReal)) =
        (((‖x - u‖ ^ (2 : ℕ) / 2 : ℝ) : EReal)) := by
    congr 1
    ring
  -- Rewrite the owner into the proximal objective and isolate the additive constant.
  calc
    mirror_c_update_objective g ω₂ xk (toDualMap ℝ E gradf) t x
        = (t : EReal) * g x + (((inner ℝ (t • gradf - xk) x : ℝ) : EReal) + ω₂ x) := by
            rw [
              mirror_c_update_objective_apply,
              mirror_c_problem_functional_half_squared_norm_apply,
              add_assoc,
              add_left_comm (((inner ℝ (t • gradf - xk) x : ℝ) : EReal)) ((t : EReal) * g x),
              ← add_assoc]
    _ = (t : EReal) * g x +
          ((((‖x - u‖ ^ (2 : ℕ) / 2 : ℝ) : EReal)) -
            (((‖u‖ ^ (2 : ℕ) / 2 : ℝ) : EReal))) := by
              rw [hcombine, hrealEReal]
    _ = proximal_objective ((t : EReal) • g) u x -
          (((‖u‖ ^ (2 : ℕ) / 2 : ℝ) : EReal)) := by
            rw [proximal_objective_apply, Pi.smul_apply, smul_eq_mul, hhalfDistance]
            simp [sub_eq_add_neg, add_left_comm, add_comm]
    _ = proximal_objective ((t : EReal) • g) (xk - t • gradf) x -
          (((‖xk - t • gradf‖ ^ (2 : ℕ) / 2 : ℝ) : EReal)) := by
            simp [u]

-- Proof sketch: rewrite the canonical owner using
-- `mirror_c_update_objective_half_squared_norm_apply`; the additive constant does not change the
-- minimizer set, and `mem_proximal_mapping_iff` identifies minimizers of the proximal objective
-- with proximal-set membership.
/-- Text 9.11 (1): in a Euclidean space with distance-generating function
`ω(x) = ‖x‖² / 2`, the one-step Mirror-C update is exactly the proximal subgradient update.
Equivalently, the next iterate minimizes the Mirror-C objective if and only if it belongs to the
proximal set of the scaled nonsmooth term `(t : EReal) • g` at the forward-subgradient point
`xk - t • f'(xk)`. -/
theorem isMinOn_mirror_c_half_squared_norm_update_iff_mem_scaled_prox
    (g : E → EReal) (xk gradf xNext : E) (t : ℝ) :
    IsMinOn (mirror_c_update_objective g ω₂ xk (toDualMap ℝ E gradf) t) Set.univ xNext ↔
      xNext ∈ prox[((t : EReal) • g)] (xk - t • gradf) := by
  let u : E := xk - t • gradf
  rw [mem_proximal_mapping_iff]
  constructor
  · intro hmin
    have hconst : IsMinOn (fun _ : E ↦ ω₂ u) Set.univ xNext := isMinOn_const
    -- Add back the constant identified by the Euclidean normalization.
    convert hmin.add hconst using 1
    ext x
    rw [mirror_c_update_objective_half_squared_norm_apply]
    simpa [u] using
      (EReal.sub_add_cancel :
        (proximal_objective ((t : EReal) • g) (xk - t • gradf) x -
            (((‖xk - t • gradf‖ ^ (2 : ℕ) / 2 : ℝ) : EReal))) +
              (((‖xk - t • gradf‖ ^ (2 : ℕ) / 2 : ℝ) : EReal)) =
          proximal_objective ((t : EReal) • g) (xk - t • gradf) x).symm
  · intro hmin
    have hconst : IsMinOn (fun _ : E ↦ -(ω₂ u)) Set.univ xNext := isMinOn_const
    -- Remove the same constant to recover the original Mirror-C owner.
    convert hmin.add hconst using 1
    ext x
    rw [mirror_c_update_objective_half_squared_norm_apply]
    simp [u, sub_eq_add_neg, add_assoc]

section Indicator

variable [CompleteSpace E]

/- The source-facing Chapter 9 statement uses a real stepsize `t` with `0 < t`, whereas the
canonical Chapter 6 scaled-proximal API is parametrized by `PosReal`. This is a genuine
`bridge/view` conversion, not a second owner. -/
/-- For a positive stepsize `t`, the proximal map of `(t : EReal) • δ_ C` is the singleton
containing the metric projection `P_C(x)`. -/
theorem prox_scaledExtendedIndicator_eq_singleton_metricProjection_of_pos
    (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {t : ℝ} (ht : 0 < t) (x : E) :
    prox[((t : EReal) • δ_ C)] x = {Pp[C, hC_nonempty, hC_closed, hC_convex] x} := by
  let tPos : PosReal := ⟨t, ht⟩
  simpa [tPos] using
    prox_scaledExtendedIndicator_eq_singleton_metricProjection
      C hC_nonempty hC_closed hC_convex tPos x

-- Proof sketch: apply the proximal-set reformulation from part (1) with `g = δ_ C`.
-- Use `smul_extendedIndicator_eq_of_pos` and
-- `prox_scaledExtendedIndicator_eq_singleton_metricProjection_of_pos` to identify the Chapter 6
-- proximal set with the singleton containing the canonical metric projection.
/-- Text 9.11 (2): if the composite term is the indicator `δ_ C` of a nonempty closed convex set
`C`, then in the same Euclidean specialization the Mirror-C update is exactly the standard mirror
descent, i.e. the projected subgradient step onto `C`. -/
theorem isMinOn_mirror_c_half_squared_norm_indicator_update_iff_eq_projection
    (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (xk gradf xNext : E) {t : ℝ} (ht : 0 < t) :
    IsMinOn
        (mirror_c_update_objective (δ_ C) ω₂ xk (toDualMap ℝ E gradf) t)
        Set.univ xNext ↔
      xNext = Pp[C, hC_nonempty, hC_closed, hC_convex] (xk - t • gradf) := by
  -- Specialize the proximal characterization to the indicator and collapse the prox set to a
  -- singleton metric projection.
  rw [isMinOn_mirror_c_half_squared_norm_update_iff_mem_scaled_prox]
  rw [prox_scaledExtendedIndicator_eq_singleton_metricProjection_of_pos
    C hC_nonempty hC_closed hC_convex ht]
  simp [Set.mem_singleton_iff]

end Indicator

end

/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_12
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Proposition_5_4
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_39
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "ω₂" => (fun z : E ↦ ‖z‖ ^ (2 : ℕ) / 2)

/- Text 9.5 is a `bridge/view` item. Chapter 9 already owns the one-step mirror-descent
objective as `mirror_descent_update_objective`, so the public surface here should be its
Euclidean specialization `ω(y) = ‖y‖² / 2`, not a parallel raw lambda. The complete-the-square
algebra is already owned by Chapter 6's `quadratic_translate_identity`, and Chapter 5 already
records the gradient identity `∇ (fun y ↦ ‖y‖² / 2) x = x` needed to evaluate the owner at this
quadratic mirror map. The source-facing mathematical content is then the equivalence between the
canonical mirror-descent step and the projected-subgradient minimization on the feasible set `C`.
-/

/- Chapter 5 already owns the gradient identity `∇ (fun y ↦ ‖y‖² / 2) x = x`. -/
recall gradient_half_squared_norm_div_two

-- Proof sketch: rewrite the linearized Euclidean objective
-- `mirror_descent_update_objective ω₂ x g t` by evaluating the owner with
-- `gradient_half_squared_norm_div_two`.
/-- Evaluating the canonical Chapter 9 owner at the Euclidean mirror map
`ω₂(y) = ‖y‖² / 2` gives the expanded textbook objective
`y ↦ ⟪t • g - x, y⟫ + ω₂ y`. -/
@[simp] theorem mirror_descent_update_objective_half_squared_norm_apply
    (x g y : E) (t : ℝ) :
    mirror_descent_update_objective ω₂ x g t y =
      inner ℝ (t • g - x) y + ω₂ y := by
  rw [mirror_descent_update_objective_apply, gradient_half_squared_norm_div_two]

-- Proof sketch: specialize `quadratic_translate_identity` to the center `x - t • g`,
-- then rewrite the left-hand side with
-- `mirror_descent_update_objective_half_squared_norm_apply`.
/-- Completing the square rewrites the canonical Euclidean mirror-descent objective
`mirror_descent_update_objective ω₂ x g t` as the half squared distance to
`x - t • g`, up to an additive constant independent of `y`. -/
theorem euclidean_mirror_descent_objective_eq_half_squared_distance
    (x g y : E) (t : ℝ) :
    mirror_descent_update_objective ω₂ x g t y =
      ‖y - (x - t • g)‖ ^ (2 : ℕ) / 2 - ‖x - t • g‖ ^ (2 : ℕ) / 2 := by
  let u : E := x - t • g
  have hquad := quadratic_translate_identity (0 : E) u y
  rw [mirror_descent_update_objective_half_squared_norm_apply]
  have hu : t • g - x = -u := by
    dsimp [u]
    abel
  rw [hu, inner_neg_left]
  change -inner ℝ u y + ‖y‖ ^ (2 : ℕ) / 2 =
      ‖y - u‖ ^ (2 : ℕ) / 2 - ‖u‖ ^ (2 : ℕ) / 2
  rw [sub_zero, sub_zero] at hquad
  rw [inner_sub_right, real_inner_self_eq_norm_sq] at hquad
  nlinarith [hquad]

/-- Pointwise additive-constant companion for the Euclidean specialization of
`mirror_descent_update_objective`. -/
@[simp] theorem mirror_descent_update_objective_half_squared_norm_add_const_apply
    (x g y : E) (t : ℝ) :
    mirror_descent_update_objective ω₂ x g t y + ω₂ (x - t • g) =
      ‖y - (x - t • g)‖ ^ (2 : ℕ) / 2 := by
  rw [euclidean_mirror_descent_objective_eq_half_squared_distance]
  change
    ‖y - (x - t • g)‖ ^ (2 : ℕ) / 2 - ‖x - t • g‖ ^ (2 : ℕ) / 2 +
        ‖x - t • g‖ ^ (2 : ℕ) / 2 =
      ‖y - (x - t • g)‖ ^ (2 : ℕ) / 2
  ring

/-- Adding the constant `ω₂ (x - t • g)` turns the Euclidean specialization of the canonical
mirror-descent one-step owner into the half squared-distance objective centered at `x - t • g`. -/
theorem mirror_descent_update_objective_half_squared_norm_add_const_eq_half_squared_distance
    (x g : E) (t : ℝ) :
    (fun y : E ↦ mirror_descent_update_objective ω₂ x g t y + ω₂ (x - t • g)) =
      fun y : E ↦ ‖y - (x - t • g)‖ ^ (2 : ℕ) / 2 := by
  funext y
  simpa using
    mirror_descent_update_objective_half_squared_norm_add_const_apply x g y t

/-- Pointwise reverse additive-constant companion for the Euclidean specialization of
`mirror_descent_update_objective`. -/
@[simp] theorem half_squared_distance_add_neg_const_eq_mirror_descent_update_objective_apply
    (x g y : E) (t : ℝ) :
    ‖y - (x - t • g)‖ ^ (2 : ℕ) / 2 + -(ω₂ (x - t • g)) =
      mirror_descent_update_objective ω₂ x g t y := by
  change
    ‖y - (x - t • g)‖ ^ (2 : ℕ) / 2 - ‖x - t • g‖ ^ (2 : ℕ) / 2 =
      mirror_descent_update_objective ω₂ x g t y
  simpa using
    (euclidean_mirror_descent_objective_eq_half_squared_distance x g y t).symm

-- Mathlib recall: `isMinOn_const` and `IsMinOn.add` are the canonical minimizer tools for
-- additive constants.
-- Proof sketch: rewrite the mirror-descent objective with
-- `euclidean_mirror_descent_objective_eq_half_squared_distance`; the additive constant does not
-- affect minimizers, so the specialized mirror-descent step and the projected-subgradient step
-- define the same `IsMinOn` condition on the feasible set `C`.
/-- Text 9.5: in a real inner-product space, hence in particular in Euclidean space, choosing the
mirror map `ω(x) = ‖x‖² / 2`, for which `∇ω(x) = x`, turns the mirror-descent
one-step minimization into the
projected subgradient one-step minimization of the half squared distance to `x - t • g`.
Equivalently, the two objectives have the same minimizers on the feasible set `C`.
-/
theorem mirror_descent_half_squared_norm_step_iff_projected_subgradient_step
    (C : Set E) (x g xNext : E) (t : ℝ) :
    IsMinOn (mirror_descent_update_objective ω₂ x g t) C xNext ↔
      IsMinOn (fun y : E ↦ ‖y - (x - t • g)‖ ^ (2 : ℕ) / 2) C xNext := by
  constructor
  · intro hmin
    have hconst : IsMinOn (fun _ : E ↦ ω₂ (x - t • g)) C xNext := isMinOn_const
    convert hmin.add hconst using 1
    ext y
    exact
      (mirror_descent_update_objective_half_squared_norm_add_const_apply x g y t).symm
  · intro hmin
    have hconst : IsMinOn (fun _ : E ↦ -(ω₂ (x - t • g))) C xNext := isMinOn_const
    convert hmin.add hconst using 1
    ext y
    exact
      (half_squared_distance_add_neg_const_eq_mirror_descent_update_objective_apply x g y t).symm

-- Proof sketch: combine the minimizer equivalence above with the Chapter 3 owner theorems
-- `projectionPoint_isMinOn` and `eq_projectionPoint_of_mem_isMinOn`.
/-- On a nonempty closed convex feasible set in a complete real inner-product space, the Euclidean
mirror-descent one-step minimizer is exactly the metric projection of `x - t • g` onto `C`. This
is the projection-valued companion to
`mirror_descent_half_squared_norm_step_iff_projected_subgradient_step`. -/
theorem mirror_descent_half_squared_norm_step_iff_eq_projection
    (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (x g xNext : E) (t : ℝ) (hxNext : xNext ∈ C) :
    IsMinOn (mirror_descent_update_objective ω₂ x g t) C xNext ↔
      xNext = Pp[C, hC_nonempty, hC_closed, hC_convex] (x - t • g) := by
  constructor
  · intro hmin
    have hproj :
        IsMinOn (fun y : E ↦ ‖y - (x - t • g)‖ ^ (2 : ℕ) / 2) C xNext :=
      (mirror_descent_half_squared_norm_step_iff_projected_subgradient_step C x g xNext t).mp hmin
    exact eq_projectionPoint_of_mem_isMinOn C hC_nonempty hC_closed hC_convex (x - t • g) hxNext
      hproj
  · intro hxNext
    subst hxNext
    exact
      (mirror_descent_half_squared_norm_step_iff_projected_subgradient_step C x g
          (Pp[C, hC_nonempty, hC_closed, hC_convex] (x - t • g)) t).mpr
        (projectionPoint_isMinOn C hC_nonempty hC_closed hC_convex (x - t • g))

end

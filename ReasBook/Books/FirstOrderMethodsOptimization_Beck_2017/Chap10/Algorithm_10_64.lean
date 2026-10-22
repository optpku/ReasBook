/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Algorithm 10.64 is `source-facing`: the textbook writes the affine iteration on `ℝ^n`, but the
primitive data are only a real linear self-map `A`, a translation vector `b`, a positive scalar
`L_f^{(2)}`, and an initial point. Domain sampling in mathlib/project shows that affine updates on
real modules are already organized around the owner declarations `LinearMap.toAffineMap`,
`AffineMap.id`, and `AffineMap.const`, while autonomous one-step recursions are most canonically
viewed through `Nat.iterate`. The faithful public API here is therefore the affine one-step
self-map together with the source-facing iterate sequence and its canonical autonomous-iterate
view. The normed/continuous layer is only a later bridge for analytic results and is not primitive
for this algorithmic definition. -/

/-- The affine one-step update `x ↦ x - (1 / L_f^{(2)}) (A x + b)` used by Algorithm G2, viewed
as an affine self-map of a real module. -/
def affine_gradient_step
    (A : E →ₗ[ℝ] E) (b : E) (Lf2 : PosReal) : E →ᵃ[ℝ] E :=
  AffineMap.id ℝ E - (Lf2⁻¹ : ℝ) • A.toAffineMap +
    AffineMap.const ℝ E (-((Lf2⁻¹ : ℝ) • b))

-- Proof sketch: unfold `affine_gradient_step`; evaluation at `x` is definitionally the displayed
-- affine update formula.
/-- Evaluating `affine_gradient_step` at `x` gives the formula
`x - (1 / L_f^{(2)}) (A x + b)`. -/
@[simp] theorem affine_gradient_step_apply
    (A : E →ₗ[ℝ] E) (b : E) (Lf2 : PosReal) (x : E) :
    affine_gradient_step A b Lf2 x =
      x - (Lf2⁻¹ : ℝ) • (A x + b) := by
  simp [affine_gradient_step, sub_eq_add_neg, smul_add, add_assoc, add_left_comm, add_comm]

/-- Algorithm 10.64: given an initialization `x^0 = x0`, a linear map `A`, an offset `b`, and a
positive parameter `L_f^{(2)}`, Algorithm G2 generates iterates by the recursion
`x^(k+1) = x^k - (1 / L_f^{(2)}) (A x^k + b)` in the ambient real module. -/
def affine_gradient_method
    (A : E →ₗ[ℝ] E) (b : E) (Lf2 : PosReal) (x0 : E) : ℕ → E
  | 0 => x0
  | k + 1 => affine_gradient_step A b Lf2 (affine_gradient_method A b Lf2 x0 k)

/-- The affine-gradient sequence agrees with the autonomous iterate view
`x^k = (affine_gradient_step A b L_f^{(2)})^[k] (x^0)`. -/
theorem affine_gradient_method_def
    (A : E →ₗ[ℝ] E) (b : E) (Lf2 : PosReal) (x0 : E) :
    affine_gradient_method A b Lf2 x0 =
      fun k ↦ Nat.iterate (affine_gradient_step A b Lf2) k x0 := by
  funext k
  induction k with
  | zero => rfl
  | succ k hk =>
      simp [affine_gradient_method, hk, Function.iterate_succ_apply']

/-- The affine-gradient method starts at the prescribed initialization `x^0 = x0`. -/
@[simp] theorem affine_gradient_method_zero
    (A : E →ₗ[ℝ] E) (b : E) (Lf2 : PosReal) (x0 : E) :
    affine_gradient_method A b Lf2 x0 0 = x0 :=
  rfl

/-- Each successor iterate of the affine-gradient method is obtained by applying the one-step
affine update to the current iterate. -/
@[simp] theorem affine_gradient_method_succ
    (A : E →ₗ[ℝ] E) (b : E) (Lf2 : PosReal) (x0 : E) (k : ℕ) :
    affine_gradient_method A b Lf2 x0 (k + 1) =
      affine_gradient_step A b Lf2 (affine_gradient_method A b Lf2 x0 k) :=
  rfl

-- Proof sketch: unfold one autonomous step using `affine_gradient_method_succ`, then rewrite the
-- resulting one-step map with `affine_gradient_step_apply`.
/-- The affine-gradient iterates satisfy the textbook general step
`x^(k+1) = x^k - (1 / L_f^{(2)}) (A x^k + b)`. -/
theorem affine_gradient_method_update
    (A : E →ₗ[ℝ] E) (b : E) (Lf2 : PosReal) (x0 : E) (k : ℕ) :
    affine_gradient_method A b Lf2 x0 (k + 1) =
      affine_gradient_method A b Lf2 x0 k -
        (Lf2⁻¹ : ℝ) • (A (affine_gradient_method A b Lf2 x0 k) + b) := by
  rw [affine_gradient_method_succ, affine_gradient_step_apply]

end

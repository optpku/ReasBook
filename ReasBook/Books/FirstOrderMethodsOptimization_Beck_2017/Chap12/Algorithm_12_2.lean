/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {E : Type u} {V : Type v}
variable [AddCommMonoid E] [Module ℝ E]
variable [NormedAddCommGroup V] [Module ℝ V]

/- Algorithm 12.2 is `source-facing` in the Chapter 12 dual proximal-gradient API.

Domain sampling against the surrounding project and mathlib points to:
- `prox[...]` from Chapter 6 as the canonical owner for the set-valued proximal update in step
  (b);
- `IsMaxOn` as the canonical owner for the step-(a) argmax condition;
- `DualBasedProximalGradientDualStepsizeParameter` from Algorithm 12.1, applied to
  `A.toContinuousLinearMap`, as the canonical owner for the admissible bound `‖A‖² / σ ≤ L`;
- `LinearMap.adjoint` together with `LinearMap.toContinuousLinearMap` as the natural Hilbert-space
  realization of `Aᵀ` and `‖A‖`.

Because both the primal argmax in step (a) and the proximal point in step (b) are naturally
set-valued at statement stage, the faithful public API is a trajectory predicate on a pair of
sequences `(x^k, y^k)` rather than a recursive chosen-update function. -/

/-- The admissible dual updates in step (b) of the dual proximal-gradient method--primal
representation. A next dual iterate `y⁺` is obtained from a proximal point
`p ∈ prox_{L g}(A x - L y)` by the affine correction
`y⁺ = y - (1 / L) A x + (1 / L) p`. -/
def dual_proximal_gradient_primal_y_step
    (g : V → EReal) (A : E →ₗ[ℝ] V) (x : E) (y : V) (L : PosReal) : Set V :=
  (fun p : V ↦ y - (1 / L : ℝ) • A x + (1 / L : ℝ) • p) ''
    prox[((L : EReal) • g)] (A x - (L : ℝ) • y)

-- Proof sketch: unfold `dual_proximal_gradient_primal_y_step`; membership in the image set is
-- exactly the existence of a proximal point `p` with the displayed affine update formula.
/-- Membership in `dual_proximal_gradient_primal_y_step g A x y L` is equivalent to the existence
of a proximal point `p ∈ prox_{L g}(A x - L y)` producing the updated dual iterate
`y - (1 / L) A x + (1 / L) p`. -/
theorem mem_dual_proximal_gradient_primal_y_step_iff
    {g : V → EReal} {A : E →ₗ[ℝ] V} {x : E} {y yNext : V} {L : PosReal} :
    yNext ∈ dual_proximal_gradient_primal_y_step g A x y L ↔
      ∃ p ∈ prox[((L : EReal) • g)] (A x - (L : ℝ) • y),
        yNext = y - (1 / L : ℝ) • A x + (1 / L : ℝ) • p := by
  constructor
  · intro hyNext
    rcases hyNext with ⟨p, hp, rfl⟩
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, hpNext⟩
    exact ⟨p, hp, hpNext.symm⟩

end

section

variable {E : Type u} {V : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The admissible primal points in step (a) of the dual proximal-gradient method: `x` belongs to
this set exactly when it maximizes the affine-minus-`f` objective
`x' ↦ ⟪x', Aᵀ y⟫ - f(x')` over the whole primal space. -/
def dual_proximal_gradient_primal_x_argmax
    (f : E → EReal) (A : E →ₗ[ℝ] V) (y : V) : Set E :=
  {x | IsMaxOn (fun x' : E ↦ (((inner ℝ x' (A.adjoint y) : ℝ) : EReal) - f x')) Set.univ x}

-- Proof sketch: unfold `dual_proximal_gradient_primal_x_argmax`; membership is definitionally the
-- `IsMaxOn` argmax condition for the affine-minus-`f` objective on `Set.univ`.
/-- Membership in `dual_proximal_gradient_primal_x_argmax f A y` means that `x` is an argmax of
`x' ↦ ⟪x', Aᵀ y⟫ - f(x')`. -/
@[simp] theorem mem_dual_proximal_gradient_primal_x_argmax_iff
    {f : E → EReal} {A : E →ₗ[ℝ] V} {y : V} {x : E} :
    x ∈ dual_proximal_gradient_primal_x_argmax f A y ↔
      IsMaxOn (fun x' : E ↦ (((inner ℝ x' (A.adjoint y) : ℝ) : EReal) - f x')) Set.univ x :=
  Iff.rfl

/-- Algorithm 12.2: given an initialization `y⁰ = y0` and an admissible constant stepsize
parameter `L`, a pair of sequences `(x^k, y^k)` follows the dual proximal-gradient method in
primal representation when every iterate satisfies step (a)
`x^k ∈ argmax_x {⟪x, Aᵀ y^k⟫ - f(x)}` and step (b)
`y^(k+1) = y^k - (1 / L) A x^k + (1 / L) prox_{L g}(A x^k - L y^k)`, recorded here through the
canonical set-valued owners for the argmax and proximal update. -/
class is_dual_proximal_gradient_primal_trajectory
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V)
    {σ : PosReal}
    (L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ)
    (y0 : V) (x : ℕ → E) (y : ℕ → V) : Prop where
  /-- The dual sequence starts from the prescribed initialization `y⁰ = y0`. -/
  zero :
    y 0 = y0
  /-- At each iteration `k`, the primal point lies in the argmax set. -/
  primal_step (k : ℕ) :
    x k ∈ dual_proximal_gradient_primal_x_argmax f A (y k)
  /-- At each iteration `k`, the next dual point lies in the corresponding Chapter 12 proximal
  update set. -/
  dual_step (k : ℕ) :
    y (k + 1) ∈ dual_proximal_gradient_primal_y_step g A (x k) (y k) L

end

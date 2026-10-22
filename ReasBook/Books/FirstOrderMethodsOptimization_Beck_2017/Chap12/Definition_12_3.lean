/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

section

variable {E : Type u} {Y : Type v}
variable [AddCommMonoid E] [Module ℝ E]
variable [AddCommGroup Y] [Module ℝ Y]

/- Definition 12.3 is `source-facing`: it introduces the equality-constrained Lagrangian for the
split model from Definition 12.2.

Domain sampling in the surrounding chapter/project identifies the relevant owners:
- `composite_model_objective` from Definition 10.2 as the canonical pointwise-sum owner, used here
  as the product objective `(x, z) ↦ f x + g z`;
- `fenchel_split_lagrangian` from Definition 4.8 as the nearby same-shape split-Lagrangian owner,
  confirming that the Chapter 12 Lagrangian itself should remain the source-facing primitive while
  its transpose/separation formulas stay derived bridge API;
- `dual_based_proximal_gradient_primal_optimal_value_eq_split_infimum` from Definition 12.2 as
  the source-facing bridge that identifies the same split reformulation at the primal-value level;
- `LinearMap.dualMap` together with the canonical dual evaluation pairing for the transpose term
  `Aᵀ y`.

Primitive data are therefore only the product objective and the constraint residual pairing. The
Lagrangian should therefore reuse the canonical product objective
`composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd)` rather than rebuilding `f x + g z`
locally, while the transpose presentation remains a derived `bridge/view` theorem. -/

/-- Definition 12.3: the Lagrangian for the split model `min_{x,z} f x + g z` with constraint
`A x - z = 0` and dual variable `y ∈ Y*` is
`L(x, z; y) = f x + g z - ⟪y, A x - z⟫`, expressed using the canonical dual evaluation pairing. -/
def dual_based_proximal_gradient_lagrangian
    (f : E → EReal) (g : Y → EReal) (A : E →ₗ[ℝ] Y)
    (x : E) (z : Y) (y : Module.Dual ℝ Y) : EReal :=
  composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd) (x, z) - (y (A x - z) : EReal)

-- Proof sketch: unfold `dual_based_proximal_gradient_lagrangian`; the displayed formula is exactly
-- the defining split objective minus the equality-constraint pairing.
/-- Evaluating the Chapter 12 Lagrangian gives the split objective value minus the dual pairing of
the residual `A x - z`. -/
@[simp] theorem dual_based_proximal_gradient_lagrangian_apply
    (f : E → EReal) (g : Y → EReal) (A : E →ₗ[ℝ] Y)
    (x : E) (z : Y) (y : Module.Dual ℝ Y) :
    dual_based_proximal_gradient_lagrangian f g A x z y =
      composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd) (x, z) -
        (y (A x - z) : EReal) := rfl

-- Proof sketch: expand the residual pairing by linearity and identify `y (A x)` with
-- `(A.dualMap y) x`; the result separates into the `x`-affine perturbation of `f` and the
-- `z`-affine perturbation of `g`.
/-- The split Lagrangian separates into the two affine perturbations that later produce the dual
objective `-f*(Aᵀ y) - g*(-y)`. -/
theorem dual_based_proximal_gradient_lagrangian_eq_affine_split
    (f : E → EReal) (g : Y → EReal) (A : E →ₗ[ℝ] Y)
    (x : E) (z : Y) (y : Module.Dual ℝ Y) :
    dual_based_proximal_gradient_lagrangian f g A x z y =
      (f x - ((A.dualMap y) x : EReal)) + (g z + (y z : EReal)) := by
  rw [dual_based_proximal_gradient_lagrangian_apply, composite_model_objective_apply]
  have hy : (y (A x - z) : EReal) = (((A.dualMap y) x - y z : ℝ) : EReal) := by
    simp [LinearMap.dualMap_apply, map_sub]
  rw [hy]
  have hs : -((((A.dualMap y) x - y z : ℝ) : EReal)) =
      -(((A.dualMap y) x : EReal)) + (y z : EReal) := by
    change (((-(((A.dualMap y) x - y z)) : ℝ)) : EReal) =
        (((-((A.dualMap y) x) + y z : ℝ)) : EReal)
    norm_num [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  rw [sub_eq_add_neg, hs]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

-- Proof sketch: expand `y (A x - z)` by linearity as `y (A x) - y z`, identify `y (A x)` with
-- `(A.dualMap y) x` via `LinearMap.dualMap_apply`, and then regroup the extended-real terms.
/-- The Lagrangian admits the textbook transpose rewrite
`L(x, z; y) = f x + g z - (Aᵀ y)(x) + y(z)`. -/
theorem dual_based_proximal_gradient_lagrangian_eq_dualMap_form
    (f : E → EReal) (g : Y → EReal) (A : E →ₗ[ℝ] Y)
    (x : E) (z : Y) (y : Module.Dual ℝ Y) :
    dual_based_proximal_gradient_lagrangian f g A x z y =
      f x + g z - ((A.dualMap y) x : EReal) + (y z : EReal) := by
  rw [dual_based_proximal_gradient_lagrangian_eq_affine_split]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

end

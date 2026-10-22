/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

section

variable {E : Type u} {Y : Type v}
variable [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup Y] [Module ℝ Y]

/- Definition 12.5 has two layers:
- `source-facing`: the textbook dual terms `F(y) = f*(Aᵀ y)` and `G(y) = g*(-y)`;
- `core/canonical`: Chapter 10's `composite_model_objective` for the split sum `F + G`;
- `bridge/view`: the identification of that split sum with the negated Chapter 12.4 dual
  maximization objective `-q`.

Domain sampling in the surrounding chapter/project identifies:
- `conjugate_function` as the owner of Fenchel conjugates;
- `LinearMap.dualMap` as the owner of the transpose pullback `Aᵀ y`;
- `composite_model_objective` as the chapter owner for pointwise sums;
- `dual_based_proximal_gradient_lagrange_dual_objective` as the maximization-side Chapter 12
  owner.

Primitive data are therefore only the two dual terms `F` and `G`; the combined minimization
objective is derived API from the existing owner `composite_model_objective`. -/

/-- The textbook term `F(y) = f*(Aᵀ y)` in the dual-based proximal gradient dual model, expressed
through the canonical pullback `A.dualMap` on the algebraic dual. -/
def dual_based_proximal_gradient_dual_F_term
    (f : E → EReal) (A : E →ₗ[ℝ] Y) : Module.Dual ℝ Y → EReal :=
  conjugate_function f ∘ A.dualMap

-- Proof sketch: unfold `dual_based_proximal_gradient_dual_F_term`; its value at `y` is exactly the
-- Chapter 4 conjugate `f*` evaluated at the dual pullback `A.dualMap y`.
/-- Evaluating the textbook `F`-term gives `f*(Aᵀ y)` via `conjugate_function`. -/
@[simp] theorem dual_based_proximal_gradient_dual_F_term_apply
    (f : E → EReal) (A : E →ₗ[ℝ] Y) (y : Module.Dual ℝ Y) :
    dual_based_proximal_gradient_dual_F_term f A y =
      conjugate_function f (A.dualMap y) :=
  rfl

/-- The textbook term `G(y) = g*(-y)` in the dual-based proximal gradient dual model. -/
def dual_based_proximal_gradient_dual_G_term
    (g : Y → EReal) : Module.Dual ℝ Y → EReal :=
  conjugate_function g ∘ Neg.neg

-- Proof sketch: unfold `dual_based_proximal_gradient_dual_G_term`; this is exactly the Chapter 4
-- conjugate of `g` evaluated at the negated dual variable.
/-- Evaluating the textbook `G`-term gives `g*(-y)` via `conjugate_function`. -/
@[simp] theorem dual_based_proximal_gradient_dual_G_term_apply
    (g : Y → EReal) (y : Module.Dual ℝ Y) :
    dual_based_proximal_gradient_dual_G_term g y =
      conjugate_function g (-y) :=
  rfl

/- Definition 12.5: the dual minimization objective in textbook split form is the Chapter 10
owner `composite_model_objective` applied to the Chapter 12 dual terms `F` and `G`. -/
recall composite_model_objective
recall composite_model_objective_apply

-- Proof sketch: unfold the split terms `F` and `G` and the Chapter 12.4 owner `q`, then apply
-- `EReal.neg_sub` under the local non-`⊥` hypotheses that rule out the mixed infinite case.
/-- When the two split summands avoid `⊥`, their canonical Chapter 10 sum agrees pointwise with
the bridge/view `-q(y)`. -/
theorem dual_based_proximal_gradient_dual_terms_sum_eq_neg_lagrange_dual_objective
    (f : E → EReal) (g : Y → EReal) (A : E →ₗ[ℝ] Y) (y : Module.Dual ℝ Y)
    (hF : dual_based_proximal_gradient_dual_F_term f A y ≠ ⊥)
    (hG : dual_based_proximal_gradient_dual_G_term g y ≠ ⊥) :
    composite_model_objective
        (dual_based_proximal_gradient_dual_F_term f A)
        (dual_based_proximal_gradient_dual_G_term g) y =
      -dual_based_proximal_gradient_lagrange_dual_objective f g A y := by
  rw [composite_model_objective_apply, dual_based_proximal_gradient_dual_F_term_apply,
    dual_based_proximal_gradient_dual_G_term_apply,
    dual_based_proximal_gradient_lagrange_dual_objective_apply]
  have hF_top : -conjugate_function f (A.dualMap y) ≠ ⊤ := by
    intro h
    have h' : conjugate_function f (A.dualMap y) = ⊥ := by
      simpa using congrArg Neg.neg h
    exact hF h'
  have hneg :
      -(-conjugate_function f (A.dualMap y) - conjugate_function g (-y)) =
        - -conjugate_function f (A.dualMap y) + conjugate_function g (-y) :=
    EReal.neg_sub (Or.inr (by simpa using hG)) (Or.inl hF_top)
  simpa using hneg.symm

-- Proof sketch: use the bridge theorem to identify the source-facing split objective with the
-- negated Chapter 12.4 owner pointwise, rewrite its range as the negated range of `q`, and then
-- apply the order-duality identity `sInf (-s) = -sSup s`.
/-- If the split summands are never `⊥`, the infimum of the dual minimization objective is the
negation of the canonical dual maximization value from Definition 12.4. -/
theorem dual_based_proximal_gradient_dual_terms_infimum_eq_neg_lagrange_dual_problem_value
    (f : E → EReal) (g : Y → EReal) (A : E →ₗ[ℝ] Y)
    (hF : ∀ y, dual_based_proximal_gradient_dual_F_term f A y ≠ ⊥)
    (hG : ∀ y, dual_based_proximal_gradient_dual_G_term g y ≠ ⊥) :
    sInf
        (Set.range
          (composite_model_objective
            (dual_based_proximal_gradient_dual_F_term f A)
            (dual_based_proximal_gradient_dual_G_term g))) =
      -dual_based_proximal_gradient_lagrange_dual_problem_value f g A := by
  rw [dual_based_proximal_gradient_lagrange_dual_problem_value]
  have hrange :
      Set.range
          (composite_model_objective
            (dual_based_proximal_gradient_dual_F_term f A)
            (dual_based_proximal_gradient_dual_G_term g)) =
        -Set.range (dual_based_proximal_gradient_lagrange_dual_objective f g A) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      rw [dual_based_proximal_gradient_dual_terms_sum_eq_neg_lagrange_dual_objective
        f g A y (hF y) (hG y)]
      simp [Set.mem_neg]
    · intro hz
      have hz' : -z ∈ Set.range (dual_based_proximal_gradient_lagrange_dual_objective f g A) := by
        simpa [Set.mem_neg] using hz
      rcases hz' with ⟨y, hy⟩
      refine ⟨y, ?_⟩
      rw [dual_based_proximal_gradient_dual_terms_sum_eq_neg_lagrange_dual_objective
        f g A y (hF y) (hG y)]
      simpa using congrArg Neg.neg hy
  rw [hrange]
  exact ereal_sInf_neg
    (Set.range (dual_based_proximal_gradient_lagrange_dual_objective f g A))

end

/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- This support owner extracts the reusable source-facing residual from Remark 10.17 so nearby
Chapter 10 items can depend on `ℓ[f, x, y]` without creating an import cycle with the downstream
gap theorem owner `fundamental_prox_grad_inequality`. -/

/-- The first-order linearization defect
`ℓ_f(x, y) = f(x) - f(y) - ⟪∇ f(y), x - y⟫` of the smooth term `f` at the base point `y`,
viewed as a totalized `EReal` expression on `E × interior (effective_domain f)`. -/
def prox_gradient_linearization_defect (f : E → EReal) (x : E)
    (y : interior (effective_domain f)) : EReal :=
  f x - f (y : E) -
    (inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - (y : E)) : EReal)

/- Textbook bracket notation for the first-order residual `ℓ_f(x, y)`. -/
notation "ℓ[" f ", " x ", " y "]" => prox_gradient_linearization_defect f x y

/-- Evaluating `ℓ[f, x, y]` expands to `f(x) - f(y) - ⟪∇ f(y), x - y⟫`. -/
@[simp] theorem prox_gradient_linearization_defect_eq
    (f : E → EReal) (x : E) (y : interior (effective_domain f)) :
    ℓ[f, x, y] =
      f x - f (y : E) -
        (inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - (y : E)) : EReal) :=
  rfl

end

end

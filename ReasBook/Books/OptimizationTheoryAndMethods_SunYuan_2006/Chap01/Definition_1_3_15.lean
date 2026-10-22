/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped RealInnerProductSpace

-- Semantic recall: mathlib exposes order-theoretic owners such as `MonotoneOn` and convex-analytic
-- owners such as `StrongConvexOn`, but no canonical owner for the source's inner-product
-- monotone-operator notion on subset domains was found. The source-facing API below therefore
-- keeps local `Prop`-valued owners for maps `F : D → E` on subtype domains `D` of a real inner
-- product space `E`.

section Definition1315

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {D : Set E} {D₀ : Set D}

/-- Chapter01 Definition 1.3.15 (1). A mapping `F : D → E` is monotone on `D₀ : Set D` when
`⟪F x - F y, (x : E) - y⟫ ≥ 0` for every `x, y ∈ D₀`. -/
def monotoneOperatorOn (F : D → E) (D₀ : Set D) : Prop :=
  ∀ ⦃x y : D⦄, x ∈ D₀ → y ∈ D₀ → ⟪F x - F y, (x : E) - y⟫ ≥ 0

/-- Unfolding formula for `monotoneOperatorOn`. -/
@[simp] theorem monotoneOperatorOn_iff (F : D → E) (D₀ : Set D) :
    monotoneOperatorOn F D₀ ↔
      ∀ ⦃x y : D⦄, x ∈ D₀ → y ∈ D₀ → ⟪F x - F y, (x : E) - y⟫ ≥ 0 :=
  Iff.rfl

/-- Chapter01 Definition 1.3.15 (2). A mapping `F : D → E` is strictly monotone on
`D₀ : Set D` when `⟪F x - F y, (x : E) - y⟫ > 0` for every distinct
`x, y ∈ D₀`. -/
def strictlyMonotoneOperatorOn (F : D → E) (D₀ : Set D) : Prop :=
  ∀ ⦃x y : D⦄, x ∈ D₀ → y ∈ D₀ → x ≠ y → ⟪F x - F y, (x : E) - y⟫ > 0

/-- Unfolding formula for `strictlyMonotoneOperatorOn`. -/
@[simp] theorem strictlyMonotoneOperatorOn_iff (F : D → E) (D₀ : Set D) :
    strictlyMonotoneOperatorOn F D₀ ↔
      ∀ ⦃x y : D⦄, x ∈ D₀ → y ∈ D₀ → x ≠ y →
        ⟪F x - F y, (x : E) - y⟫ > 0 :=
  Iff.rfl

/-- Chapter01 Definition 1.3.15 (3). A mapping `F : D → E` is uniformly, equivalently strongly,
monotone on `D₀ : Set D` when there exists `c > 0` such that
`⟪F x - F y, (x : E) - y⟫ ≥ c * ‖(x : E) - y‖ ^ 2` for every
`x, y ∈ D₀`. -/
def stronglyMonotoneOperatorOn (F : D → E) (D₀ : Set D) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ ⦃x y : D⦄, x ∈ D₀ → y ∈ D₀ →
      ⟪F x - F y, (x : E) - y⟫ ≥ c * ‖(x : E) - y‖ ^ (2 : ℕ)

/-- Strong monotonicity on `D₀` implies monotonicity on `D₀`. -/
theorem monotoneOperatorOn_of_stronglyMonotoneOperatorOn
    (hF : stronglyMonotoneOperatorOn F D₀) :
    monotoneOperatorOn F D₀ := by
  rcases hF with ⟨c, hc, hF⟩
  intro x y hx hy
  exact le_trans (by positivity : 0 ≤ c * ‖(x : E) - y‖ ^ (2 : ℕ)) (hF hx hy)

/-- Unfolding formula for `stronglyMonotoneOperatorOn`. -/
@[simp] theorem stronglyMonotoneOperatorOn_iff (F : D → E) (D₀ : Set D) :
    stronglyMonotoneOperatorOn F D₀ ↔
      ∃ c : ℝ, 0 < c ∧
        ∀ ⦃x y : D⦄, x ∈ D₀ → y ∈ D₀ →
          ⟪F x - F y, (x : E) - y⟫ ≥ c * ‖(x : E) - y‖ ^ (2 : ℕ) :=
  Iff.rfl

end Definition1315

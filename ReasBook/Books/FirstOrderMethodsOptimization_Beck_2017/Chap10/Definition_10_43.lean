/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

open PosReal

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 10.43 is `source-facing`: the textbook introduces smooth approximations and
smoothability for convex real-valued functions. Domain sampling in this workspace shows that the
analytic owner clauses are `ConvexOn ℝ Set.univ` and Chapter 5's `is_l_smooth_on`, while Chapter 6
already owns the positive-parameter type `PosReal`. For downstream Chapter 10 reuse, the primitive
approximation owner is the nonnegative-parameter predicate; the textbook strictly positive
parameter convention is then a thin bridge obtained by coercing `PosReal` to `NNReal`. -/

/-- A function `hμ` is a `1 / μ`-smooth approximation of `h` with nonnegative parameters
`(α, β)` when it is convex, lies between `h` and `h + β μ`, and is globally `(α / μ)`-smooth. -/
structure IsSmoothApproximationNonneg (h hμ : E → ℝ) (α β : NNReal) (μ : PosReal) : Prop where
  convex : ConvexOn ℝ Set.univ hμ
  lower_le (x : E) : hμ x ≤ h x
  upper_le (x : E) : h x ≤ hμ x + (β : ℝ) * (μ : ℝ)
  smooth : is_l_smooth_on hμ Set.univ (α / toNNReal μ)

/-- A function `hμ` is a `1 / μ`-smooth approximation of `h` with positive parameters `(α, β)`.
This is the textbook source-facing view of `IsSmoothApproximationNonneg`, obtained by coercing the
parameters to `NNReal`. -/
abbrev IsSmoothApproximation (h hμ : E → ℝ) (α β μ : PosReal) : Prop :=
  IsSmoothApproximationNonneg h hμ (toNNReal α) (toNNReal β) μ

namespace IsSmoothApproximation

-- Proof sketch: copy the four fields of `hh`; the lower and upper comparison inequalities are
-- unchanged, and the positive parameters are viewed as nonnegative via `PosReal.toNNReal`.
/-- A positive-parameter smooth approximation is also a nonnegative-parameter smooth approximation
after coercing the parameters to `NNReal`. -/
theorem toNonneg
    {h hμ : E → ℝ} {α β μ : PosReal} (hh : IsSmoothApproximation h hμ α β μ) :
    IsSmoothApproximationNonneg h hμ (toNNReal α) (toNNReal β) μ :=
  hh

end IsSmoothApproximation

/-- A function `h : E → ℝ` is nonnegatively `(α, β)`-smoothable if for every `μ > 0` there exists
a `1 / μ`-smooth approximation of `h` with nonnegative parameters `(α, β)`. -/
def is_smoothable_nonneg (h : E → ℝ) (α β : NNReal) : Prop :=
  ∀ μ : PosReal, ∃ hμ : E → ℝ, IsSmoothApproximationNonneg h hμ α β μ

/-- Definition 10.43: a function `h : E → ℝ` is `(α, β)`-smoothable if for every `μ > 0` there
exists a `1 / μ`-smooth approximation of `h` with parameters `(α, β)`. This is the textbook
positive-parameter view of `is_smoothable_nonneg`. -/
abbrev is_smoothable (h : E → ℝ) (α β : PosReal) : Prop :=
  is_smoothable_nonneg h (toNNReal α) (toNNReal β)

-- Proof sketch: for each `ε > 0`, choose the smoothing parameter `μ = ε / (β + 1)`. The
-- approximation inequalities and convexity of `hμ` yield the Jensen inequality for `h` up to the
-- additive error `β μ < ε`; then remove `ε` via `le_of_forall_pos_le_add`.
/-- A nonnegatively smoothable function is convex on the whole ambient space. -/
theorem is_smoothable_nonneg_convex
    {h : E → ℝ} {α β : NNReal} (hh : is_smoothable_nonneg h α β) :
    ConvexOn ℝ Set.univ h := by
  rw [ConvexOn]
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  apply le_of_forall_pos_le_add
  intro ε hε
  let μ : PosReal := ⟨ε / ((β : ℝ) + 1), by
    refine div_pos hε ?_
    have hβ_nonneg : 0 ≤ (β : ℝ) := β.2
    linarith⟩
  rcases hh μ with ⟨hμ, hhμ⟩
  have hconv :
      hμ (a • x + b • y) ≤ a * hμ x + b * hμ y := by
    simpa [smul_eq_mul] using hhμ.convex.2 (by simp) (by simp) ha hb hab
  have hβμ_lt_ε : (β : ℝ) * (μ : ℝ) < ε := by
    have hβ_nonneg : 0 ≤ (β : ℝ) := β.2
    have hμ_pos : 0 < (μ : ℝ) := PosReal.coe_pos μ
    have hden_pos : 0 < (β : ℝ) + 1 := by
      linarith
    have hsum : ((β : ℝ) + 1) * (μ : ℝ) = ε := by
      change ((β : ℝ) + 1) * (ε / ((β : ℝ) + 1)) = ε
      field_simp [hden_pos.ne']
    nlinarith
  calc
    h (a • x + b • y) ≤ hμ (a • x + b • y) + (β : ℝ) * (μ : ℝ) := hhμ.upper_le _
    _ ≤ (a * hμ x + b * hμ y) + (β : ℝ) * (μ : ℝ) := by linarith
    _ ≤ (a * h x + b * h y) + (β : ℝ) * (μ : ℝ) := by
      gcongr
      · exact hhμ.lower_le x
      · exact hhμ.lower_le y
    _ ≤ (a * h x + b * h y) + ε := by linarith
    _ = a • h x + b • h y + ε := by simp [smul_eq_mul]

/-- A smoothable function is convex on the whole ambient space. -/
theorem is_smoothable_convex
    {h : E → ℝ} {α β : PosReal} (hh : is_smoothable h α β) :
    ConvexOn ℝ Set.univ h :=
  is_smoothable_nonneg_convex hh

-- Proof sketch: unfold `is_smoothable`; its defining clause already gives the required
-- approximation for the chosen positive parameter `μ`.
/-- For every positive parameter `μ`, a nonnegatively smoothable function admits a
`1 / μ`-smooth approximation with the same parameters `(α, β)`. -/
theorem is_smoothable_nonneg_exists_smooth_approximation
    {h : E → ℝ} {α β : NNReal} (hh : is_smoothable_nonneg h α β) (μ : PosReal) :
    ∃ hμ : E → ℝ, IsSmoothApproximationNonneg h hμ α β μ :=
  hh μ

/-- For every positive parameter `μ`, a smoothable function admits a `1 / μ`-smooth approximation
with the same parameters `(α, β)`. -/
theorem is_smoothable_exists_smooth_approximation
    {h : E → ℝ} {α β : PosReal} (hh : is_smoothable h α β) (μ : PosReal) :
    ∃ hμ : E → ℝ, IsSmoothApproximation h hμ α β μ :=
  hh μ

/-- A positively parametrized smoothable function is also nonnegatively smoothable after coercing
its parameters to `NNReal`. -/
theorem is_smoothable_to_nonneg
    {h : E → ℝ} {α β : PosReal} (hh : is_smoothable h α β) :
    is_smoothable_nonneg h (toNNReal α) (toNNReal β) :=
  hh

end

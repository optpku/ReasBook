/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable {n : ℕ} {p : ENNReal} [Fact (1 ≤ p)]

local notation "E" => WithLp p (Fin n → ℝ)

/-
Theorem 5.12 is a `bridge/view` item. Its owner abstractions are the chapter predicate
`is_l_smooth_on`, specialized to `Set.univ`, and mathlib's Lipschitz/Fréchet-derivative API. The
only primitive mathematical data is the `C²` function `f`; the Hessian bound is the derived
pointwise estimate on
`fderiv ℝ (fderiv ℝ f)`.
-/

-- Proof sketch: for `(ii) → (i)`, integrate the derivative of `fderiv ℝ f` along each line
-- segment and bound the resulting Bochner integral by the uniform operator-norm estimate on the
-- Hessian. For `(i) → (ii)`, evaluate the `L`-Lipschitz estimate for `fderiv ℝ f` on small
-- increments `x + t • d`, divide by `t`, and pass to the limit using the `C²` hypothesis.
/-- Helper for Theorem 5.12: a `C²` function has a globally differentiable derivative field. -/
lemma differentiableFderivOfContDiffTwo {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (fderiv ℝ f) := by
  -- Differentiate once less to make the derivative field itself `C¹`.
  have hfderiv : ContDiff ℝ 1 (fderiv ℝ f) := by
    simpa using hf.fderiv_right (m := 1) (by norm_num)
  -- A `C¹` map is differentiable everywhere.
  exact hfderiv.differentiable_one

/-- Helper for Theorem 5.12: a uniform Hessian operator-norm bound makes the derivative map
globally `L`-Lipschitz on `Set.univ`. -/
lemma lipschitzOnWithFderivOfHessianBound {f : E → ℝ} {L : NNReal} (hf : ContDiff ℝ 2 f)
    (hH : ∀ x : E, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (L : ℝ)) :
    LipschitzOnWith L (fderiv ℝ f) Set.univ := by
  -- Apply the mean value theorem to the derivative field itself.
  refine
    convex_univ.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) (f := fderiv ℝ f) ?_ ?_
  · intro x hx
    exact differentiableFderivOfContDiffTwo hf x
  · intro x hx
    -- Convert the real operator-norm bound into the `NNReal`-valued bound expected by mathlib.
    exact NNReal.coe_le_coe.mp (by simpa using hH x)

/-- Helper for Theorem 5.12: global `L`-smoothness bounds the Hessian operator norm pointwise. -/
lemma hessianOperatorNormLeOfIsLSmooth {f : E → ℝ} {L : NNReal}
    (hs : is_l_smooth_on f Set.univ L) :
    ∀ x : E, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (L : ℝ) := by
  -- Unpack smoothness to expose the global Lipschitz control of the derivative field.
  rw [is_l_smooth_on] at hs
  intro x
  -- The converse mean value inequality turns the Lipschitz estimate back into a derivative bound.
  simpa using
    norm_fderiv_le_of_lipschitzOn (𝕜 := ℝ) (f := fderiv ℝ f) (x₀ := x) (s := Set.univ)
      (by simp) hs.2

-- Route correction: instead of reproducing the textbook line-integral calculation, use mathlib's
-- mean-value/Lipschitz API for the derivative field `fderiv ℝ f`, which packages the same
-- argument with less transport overhead.
/-- Theorem 5.12: on the canonical `WithLp p (Fin n → ℝ)` model of `ℝ^n`, a twice continuously
differentiable function is globally `L`-smooth for the `l_p` norm if and only if its Fréchet
Hessian, viewed as the derivative of `fderiv ℝ f`, has nonnegative operator norm at most `L` at
every point. This is the canonical operator-norm rendering of the textbook bound
`‖∇² f(x)‖_{p,q} ≤ L`. -/
theorem is_l_smooth_iff_hessian_operator_norm_le
    {f : E → ℝ} {L : NNReal} (hf : ContDiff ℝ 2 f) :
    is_l_smooth_on f Set.univ L ↔
      ∀ x : E, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (L : ℝ) := by
  constructor
  · intro hs
    -- The reverse mean value inequality extracts the Hessian bound from derivative Lipschitzness.
    exact hessianOperatorNormLeOfIsLSmooth hs
  · intro hH
    rw [is_l_smooth_on]
    refine ⟨?_, lipschitzOnWithFderivOfHessianBound hf hH⟩
    -- A `C²` function is differentiable everywhere, which supplies the first field.
    have hcont : ContDiff ℝ 1 f := by
      simpa using hf.of_le (show (1 : WithTop ℕ∞) ≤ 2 by decide)
    have hdiff : Differentiable ℝ f := hcont.differentiable_one
    intro x hx
    exact hdiff x

-- Proof sketch: this is the `NNReal`-valued reformulation of the main theorem, obtained by
-- coercing the real operator-norm bound through `NNReal.coe_le_coe` and `coe_nnnorm`.
/-- Companion `NNReal`-valued operator-norm formulation of Theorem 5.12. -/
theorem is_l_smooth_iff_hessian_operator_nnnorm_le
    {f : E → ℝ} {L : NNReal} (hf : ContDiff ℝ 2 f) :
    is_l_smooth_on f Set.univ L ↔
      ∀ x : E, ‖fderiv ℝ (fderiv ℝ f) x‖₊ ≤ L := by
  rw [is_l_smooth_iff_hessian_operator_norm_le hf]
  constructor
  · intro h x
    exact NNReal.coe_le_coe.mp (by simpa using h x)
  · intro h x
    simpa using NNReal.coe_le_coe.mpr (h x)

end

/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_21
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Proposition_5_7
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_43

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E]

/-
Example 10.44 is `source-facing` in the Chapter 10 smoothing API: the new mathematical object is
the radial norm smoothing `x ↦ √(‖x‖² + μ²) - μ`.

Domain sampling in this neighborhood identifies:
- `sqrt_alpha_sq_add_norm_sq_function` from Proposition 4.21 as the upstream owner for the
  square-root radial expression before subtracting `μ`;
- `IsSmoothApproximation` and `is_smoothable` from Definition 10.43 as the Chapter 10 owner
  abstractions for the two public theorem statements;
- `sqrt_one_add_sq_norm_is_l_smooth` from Proposition 5.7 as the Chapter 5 radial smoothness owner
  that supplies the canonical smoothness input.

The primitive local datum is only the smoothing family `norm_smooth_approximation`. The
smooth-approximation and smoothability theorems below are derived API and should therefore live at
the chapter’s canonical ambient owner level rather than hard-coding a coordinate or proof-route
presentation.
-/
/-- The radial smoothing of the ambient norm with parameter `μ` is
`x ↦ √(‖x‖² + μ²) - μ`. On `EuclideanSpace ℝ (Fin n)` this is the textbook formula on `ℝ^n`. -/
def norm_smooth_approximation (μ : PosReal) : E → ℝ :=
  fun x ↦ (sqrt_alpha_sq_add_norm_sq_function μ x).toReal - μ

/-- Evaluating `norm_smooth_approximation μ` at `x` gives the radial smoothing formula
`√(‖x‖² + μ²) - μ`. -/
@[simp] theorem norm_smooth_approximation_apply (μ : PosReal) (x : E) :
    norm_smooth_approximation μ x =
      Real.sqrt (‖x‖ ^ (2 : ℕ) + (μ : ℝ) ^ (2 : ℕ)) - μ := by
  simp [norm_smooth_approximation, sqrt_alpha_sq_add_norm_sq_function, add_comm]

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

open scoped BigOperators

open WithLp

/- The proof follows the textbook route faithfully:
1. control the approximation error directly with elementary square-root inequalities;
2. prove convexity by combining convexity of the norm with convexity of the scalar radial profile
   `r ↦ √(r² + μ²)`;
3. rewrite the smoothing as a rescaled copy of Proposition 5.7 and transport smoothness through
   precomposition and scalar multiplication. -/

namespace Example_10_44

variable (μ : PosReal)

-- Proof sketch: rewrite the `WithLp 2` norm of a scalar pair using the standard
-- two-dimensional Euclidean norm formula.
/-- Helper for Example 10.44: the `L²` norm of the scalar pair `(r, t)` is `√(r² + t²)`. -/
lemma euclidean_two_norm_eq_sqrt_add_sq
    (r t : ℝ) :
    ‖toLp 2 (r, t)‖ = Real.sqrt (r ^ (2 : ℕ) + t ^ (2 : ℕ)) := by
  -- The canonical `WithLp 2` pair norm is already the textbook square-root expression.
  simpa [Real.norm_eq_abs, sq_abs] using (WithLp.prod_norm_eq_of_L2 (toLp 2 (r, t)))

-- Proof sketch: rewrite the convex combination of the two lifted vectors `![r, μ]` and `![s, μ]`
-- as `![a r + b s, μ]`, then apply the triangle inequality in `ℝ²`.
/-- Helper for Example 10.44: the scalar radial profile `r ↦ √(r² + μ²)` is convex on
`[0, ∞)`. -/
lemma sqrt_sq_add_parameter_convex
    {r s a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    Real.sqrt ((a * r + b * s) ^ (2 : ℕ) + (μ : ℝ) ^ (2 : ℕ)) ≤
      a * Real.sqrt (r ^ (2 : ℕ) + (μ : ℝ) ^ (2 : ℕ)) +
        b * Real.sqrt (s ^ (2 : ℕ) + (μ : ℝ) ^ (2 : ℕ)) := by
  have hμ_nonneg : 0 ≤ (μ : ℝ) := le_of_lt (PosReal.coe_pos μ)
  let u := toLp 2 (r, (μ : ℝ))
  let v := toLp 2 (s, (μ : ℝ))
  have hu :
      ‖u‖ = Real.sqrt (r ^ (2 : ℕ) + (μ : ℝ) ^ (2 : ℕ)) := by
    -- The first lifted pair has the expected Euclidean norm.
    simpa [u] using euclidean_two_norm_eq_sqrt_add_sq r (μ : ℝ)
  have hv :
      ‖v‖ = Real.sqrt (s ^ (2 : ℕ) + (μ : ℝ) ^ (2 : ℕ)) := by
    -- The same identification holds at the second endpoint.
    simpa [v] using euclidean_two_norm_eq_sqrt_add_sq s (μ : ℝ)
  have hcomb :
      a • u + b • v = toLp 2 (a * r + b * s, (μ : ℝ)) := by
    -- The second coordinate collapses because `a + b = 1`.
    have hμcoord : a * (μ : ℝ) + b * (μ : ℝ) = (μ : ℝ) := by
      nlinarith
    calc
      a • u + b • v = a • toLp 2 (r, (μ : ℝ)) + b • toLp 2 (s, (μ : ℝ)) := by
        rfl
      _ = toLp 2 (a • (r, (μ : ℝ))) + toLp 2 (b • (s, (μ : ℝ))) := by
        rw [WithLp.toLp_smul, WithLp.toLp_smul]
      _ = toLp 2 (a • (r, (μ : ℝ)) + b • (s, (μ : ℝ))) := by
        rw [← WithLp.toLp_add]
      _ = toLp 2 (a * r + b * s, a * (μ : ℝ) + b * (μ : ℝ)) := by
        simp [Prod.smul_mk]
      _ = toLp 2 (a * r + b * s, (μ : ℝ)) := by
        rw [hμcoord]
  calc
    Real.sqrt ((a * r + b * s) ^ (2 : ℕ) + (μ : ℝ) ^ (2 : ℕ))
        = ‖toLp 2 (a * r + b * s, (μ : ℝ))‖ := by
            symm
            simpa using euclidean_two_norm_eq_sqrt_add_sq (a * r + b * s) (μ : ℝ)
    _ = ‖a • u + b • v‖ := by rw [hcomb]
    _ ≤ ‖a • u‖ + ‖b • v‖ := norm_add_le _ _
    _ = a * ‖u‖ + b * ‖v‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg ha, abs_of_nonneg hb]
    _ = a * Real.sqrt (r ^ (2 : ℕ) + (μ : ℝ) ^ (2 : ℕ)) +
          b * Real.sqrt (s ^ (2 : ℕ) + (μ : ℝ) ^ (2 : ℕ)) := by
          rw [hu, hv]

-- Proof sketch: `x / μ = (1 / μ) • x`, so the inside of the square root is
-- `μ² * (1 + ‖x / μ‖²) = ‖x‖² + μ²`; positivity of `μ` lets us pull `μ` out of the square root.
/-- Helper for Example 10.44: the smoothing can be rewritten as a rescaled copy of the Chapter 5
profile `x ↦ √(1 + ‖x‖²)`. -/
lemma norm_smooth_approximation_eq_rescaled_sqrt_one_add_sq_norm
    (x : E) :
    norm_smooth_approximation μ x =
      (μ : ℝ) * Real.sqrt (1 + ‖((1 / (μ : ℝ)) • x)‖ ^ (2 : ℕ)) - μ := by
  have hμ_pos : 0 < (μ : ℝ) := PosReal.coe_pos μ
  have hμ_nonneg : 0 ≤ (μ : ℝ) := le_of_lt hμ_pos
  have hμ_ne : (μ : ℝ) ≠ 0 := ne_of_gt hμ_pos
  have hnorm_div : ‖((1 / (μ : ℝ)) • x)‖ = ‖x‖ / (μ : ℝ) := by
    rw [norm_smul, Real.norm_of_nonneg (le_of_lt (one_div_pos.mpr hμ_pos))]
    field_simp [hμ_ne]
  have hmul :
      ((μ : ℝ) ^ (2 : ℕ)) * (1 + ‖((1 / (μ : ℝ)) • x)‖ ^ (2 : ℕ)) =
        ‖x‖ ^ (2 : ℕ) + (μ : ℝ) ^ (2 : ℕ) := by
    rw [hnorm_div]
    field_simp [hμ_ne]
    ring
  calc
    norm_smooth_approximation μ x
        = Real.sqrt (‖x‖ ^ (2 : ℕ) + (μ : ℝ) ^ (2 : ℕ)) - μ := by
            rw [norm_smooth_approximation_apply]
    _ = Real.sqrt (((μ : ℝ) ^ (2 : ℕ)) * (1 + ‖((1 / (μ : ℝ)) • x)‖ ^ (2 : ℕ))) - μ := by
          rw [hmul]
    _ = Real.sqrt ((μ : ℝ) ^ (2 : ℕ)) *
          Real.sqrt (1 + ‖((1 / (μ : ℝ)) • x)‖ ^ (2 : ℕ)) - μ := by
          rw [Real.sqrt_mul (by positivity)]
    _ = (μ : ℝ) * Real.sqrt (1 + ‖((1 / (μ : ℝ)) • x)‖ ^ (2 : ℕ)) - μ := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hμ_nonneg]

-- Proof sketch: the lower inequality is `√(‖x‖² + μ²) ≤ ‖x‖ + μ`, and the upper inequality is
-- `‖x‖ ≤ √(‖x‖² + μ²)`; both are proved by squaring the nonnegative sides.
/-- Helper for Example 10.44: the square-root smoothing lies between the norm and the norm shifted
up by `μ`. -/
lemma norm_smooth_approximation_bounds
    (x : E) :
    norm_smooth_approximation μ x ≤ ‖x‖ ∧
      ‖x‖ ≤ norm_smooth_approximation μ x + μ := by
  have hμ_pos : 0 < (μ : ℝ) := PosReal.coe_pos μ
  have hμ_nonneg : 0 ≤ (μ : ℝ) := le_of_lt hμ_pos
  have hnorm_nonneg : 0 ≤ ‖x‖ := norm_nonneg x
  constructor
  · -- The approximation is never above the original norm.
    rw [norm_smooth_approximation_apply]
    have hsqrt_le : Real.sqrt (‖x‖ ^ (2 : ℕ) + (μ : ℝ) ^ (2 : ℕ)) ≤ ‖x‖ + μ := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith
    linarith
  · -- Adding back the shift `μ` recovers an upper bound for the norm.
    rw [norm_smooth_approximation_apply]
    have hnorm_le :
        ‖x‖ ≤ Real.sqrt (‖x‖ ^ (2 : ℕ) + (μ : ℝ) ^ (2 : ℕ)) := by
      exact (Real.le_sqrt hnorm_nonneg (by positivity)).2 (by nlinarith)
    simpa using hnorm_le

-- Proof sketch: first use `is_l_smooth_on_iff`, then apply the chain rule and the operator norm
-- bound `‖A (x - y)‖ ≤ ‖A‖ ‖x - y‖`.
/-- Helper for Example 10.44: precomposing an `L`-smooth function with a continuous linear map
multiplies the smoothness constant by the square of the operator norm. -/
lemma is_l_smooth_on_precompose_continuousLinearMap
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (A : Y →L[ℝ] E) (h : E → ℝ) {L : NNReal}
    (hh : is_l_smooth_on h Set.univ L) :
    is_l_smooth_on
      (fun y : Y ↦ h (A y))
      Set.univ
      (L * ‖A‖₊ ^ (2 : ℕ)) := by
  rw [is_l_smooth_on_iff] at hh ⊢
  refine ⟨?_, ?_⟩
  · intro y hy
    -- Differentiability is stable under composition with the linear map `A`.
    exact (hh.1 (A y) (by simp)).comp y A.differentiableAt
  · intro x hx y hy
    -- The chain rule turns the derivative difference into a composition with `A`.
    have hxderiv :
        fderiv ℝ (fun z : Y ↦ h (A z)) x =
          (fderiv ℝ h (A x)).comp A := by
      simpa [Function.comp, ContinuousLinearMap.comp_apply] using
        (fderiv_comp x (hh.1 (A x) (by simp)) A.differentiableAt)
    have hyderiv :
        fderiv ℝ (fun z : Y ↦ h (A z)) y =
          (fderiv ℝ h (A y)).comp A := by
      simpa [Function.comp, ContinuousLinearMap.comp_apply] using
        (fderiv_comp y (hh.1 (A y) (by simp)) A.differentiableAt)
    have hmap :
        ‖A x - A y‖ ≤ ‖A‖ * ‖x - y‖ := by
      simpa [map_sub] using A.le_opNorm (x - y)
    have hsub :
        (fderiv ℝ h (A x)).comp A - (fderiv ℝ h (A y)).comp A =
          (fderiv ℝ h (A x) - fderiv ℝ h (A y)).comp A := by
      ext z
      simp
    calc
      ‖fderiv ℝ (fun z : Y ↦ h (A z)) x - fderiv ℝ (fun z : Y ↦ h (A z)) y‖
          = ‖(fderiv ℝ h (A x) - fderiv ℝ h (A y)).comp A‖ := by
              rw [hxderiv, hyderiv, hsub]
      _ ≤ ‖fderiv ℝ h (A x) - fderiv ℝ h (A y)‖ * ‖A‖ := by
            exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (L : ℝ) * ‖A x - A y‖ * ‖A‖ := by
            gcongr
            exact hh.2 (A x) (by simp) (A y) (by simp)
      _ ≤ (L : ℝ) * (‖A‖ * ‖x - y‖) * ‖A‖ := by
            gcongr
      _ = ((L * ‖A‖₊ ^ (2 : ℕ)) : ℝ) * ‖x - y‖ := by
            simp [pow_two, mul_assoc, mul_left_comm, mul_comm]

-- Proof sketch: differentiability is preserved by scalar multiplication and constant shifts, and
-- the derivative differences scale by the absolute value of the scalar factor.
/-- Helper for Example 10.44: multiplying a smooth function by a nonnegative scalar scales the
smoothness constant by that scalar, and subtracting a constant does not change it. -/
lemma is_l_smooth_on_const_mul_sub_const
    (c d : ℝ) (hc : 0 ≤ c) {h : E → ℝ} {L : NNReal}
    (hh : is_l_smooth_on h Set.univ L) :
    is_l_smooth_on
      (fun x : E ↦ c * h x - d)
      Set.univ
      (Real.toNNReal c * L) := by
  rw [is_l_smooth_on_iff] at hh ⊢
  refine ⟨?_, ?_⟩
  · intro x hx
    -- Constant shifts do not affect differentiability, and scalar multiplication preserves it.
    exact ((hh.1 x hx).const_mul c).sub_const d
  · intro x hx y hy
    -- The derivative of `x ↦ c * h x - d` is just `c` times the derivative of `h`.
    have hxmul : DifferentiableAt ℝ (fun z : E ↦ c • h z) x := (hh.1 x hx).const_smul c
    have hymul : DifferentiableAt ℝ (fun z : E ↦ c • h z) y := (hh.1 y hy).const_smul c
    have hfun : (fun z : E ↦ c * h z - d) = (fun z : E ↦ c • h z) - fun _ : E ↦ d := by
      ext z
      simp [smul_eq_mul]
    have hxderiv :
        fderiv ℝ (fun z : E ↦ c * h z - d) x = c • fderiv ℝ h x := by
      calc
        fderiv ℝ (fun z : E ↦ c * h z - d) x
            = fderiv ℝ ((fun z : E ↦ c • h z) - fun _ : E ↦ d) x := by
                rw [hfun]
        _ = fderiv ℝ (fun z : E ↦ c • h z) x - fderiv ℝ (fun _ : E ↦ d) x := by
              rw [fderiv_sub hxmul (differentiableAt_const d)]
        _ = c • fderiv ℝ h x := by
              simpa using congrFun (fderiv_const_smul_field (𝕜 := ℝ) (R := ℝ) (f := h) c) x
    have hyderiv :
        fderiv ℝ (fun z : E ↦ c * h z - d) y = c • fderiv ℝ h y := by
      calc
        fderiv ℝ (fun z : E ↦ c * h z - d) y
            = fderiv ℝ ((fun z : E ↦ c • h z) - fun _ : E ↦ d) y := by
                rw [hfun]
        _ = fderiv ℝ (fun z : E ↦ c • h z) y - fderiv ℝ (fun _ : E ↦ d) y := by
              rw [fderiv_sub hymul (differentiableAt_const d)]
        _ = c • fderiv ℝ h y := by
              simpa using congrFun (fderiv_const_smul_field (𝕜 := ℝ) (R := ℝ) (f := h) c) y
    calc
      ‖fderiv ℝ (fun z : E ↦ c * h z - d) x - fderiv ℝ (fun z : E ↦ c * h z - d) y‖
          = ‖c • (fderiv ℝ h x - fderiv ℝ h y)‖ := by
              rw [hxderiv, hyderiv, smul_sub]
      _ = |c| * ‖fderiv ℝ h x - fderiv ℝ h y‖ := norm_smul _ _
      _ = c * ‖fderiv ℝ h x - fderiv ℝ h y‖ := by
            rw [abs_of_nonneg hc]
      _ ≤ c * ((L : ℝ) * ‖x - y‖) := by
            gcongr
            exact hh.2 x hx y hy
      _ = (((Real.toNNReal c) * L : NNReal) : ℝ) * ‖x - y‖ := by
            have hcoeff : c * (L : ℝ) = (((Real.toNNReal c) * L : NNReal) : ℝ) := by
              simpa [Real.toNNReal_of_nonneg hc]
            calc
              c * ((L : ℝ) * ‖x - y‖) = (c * (L : ℝ)) * ‖x - y‖ := by ring
              _ = (((Real.toNNReal c) * L : NNReal) : ℝ) * ‖x - y‖ := by rw [hcoeff]

-- Proof sketch: combine convexity of the norm with convexity of the scalar profile
-- `r ↦ √(r² + μ²)`, then subtract the constant `μ`.
/-- Helper for Example 10.44: the square-root smoothing is convex on the whole space. -/
lemma norm_smooth_approximation_convexOn :
    ConvexOn ℝ Set.univ (norm_smooth_approximation (E := E) μ) := by
  rw [ConvexOn]
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hnorm :
      ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
    -- The ambient norm is convex on the vector space.
    calc
      ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg ha, abs_of_nonneg hb]
  have hmono :
      Real.sqrt (‖a • x + b • y‖ ^ (2 : ℕ) + (μ : ℝ) ^ (2 : ℕ)) ≤
        Real.sqrt ((a * ‖x‖ + b * ‖y‖) ^ (2 : ℕ) + (μ : ℝ) ^ (2 : ℕ)) := by
    -- Monotonicity of the square root reduces the claim to the norm convexity bound.
    apply Real.sqrt_le_sqrt
    nlinarith [hnorm, norm_nonneg (a • x + b • y)]
  have hscalar :
      Real.sqrt ((a * ‖x‖ + b * ‖y‖) ^ (2 : ℕ) + (μ : ℝ) ^ (2 : ℕ)) ≤
        a * Real.sqrt (‖x‖ ^ (2 : ℕ) + (μ : ℝ) ^ (2 : ℕ)) +
          b * Real.sqrt (‖y‖ ^ (2 : ℕ) + (μ : ℝ) ^ (2 : ℕ)) := by
    -- The remaining step is the scalar convexity of the radial profile.
    exact sqrt_sq_add_parameter_convex (μ := μ) ha hb hab
  calc
    norm_smooth_approximation μ (a • x + b • y)
        = Real.sqrt (‖a • x + b • y‖ ^ (2 : ℕ) + (μ : ℝ) ^ (2 : ℕ)) - μ := by
            rw [norm_smooth_approximation_apply]
    _ ≤
        (a * Real.sqrt (‖x‖ ^ (2 : ℕ) + (μ : ℝ) ^ (2 : ℕ)) +
          b * Real.sqrt (‖y‖ ^ (2 : ℕ) + (μ : ℝ) ^ (2 : ℕ))) - μ := by
          gcongr
          exact le_trans hmono hscalar
    _ = a * norm_smooth_approximation μ x + b * norm_smooth_approximation μ y := by
          set sx : ℝ := Real.sqrt (‖x‖ ^ (2 : ℕ) + (μ : ℝ) ^ (2 : ℕ))
          set sy : ℝ := Real.sqrt (‖y‖ ^ (2 : ℕ) + (μ : ℝ) ^ (2 : ℕ))
          rw [norm_smooth_approximation_apply, norm_smooth_approximation_apply]
          have habμ : a * (μ : ℝ) + b * (μ : ℝ) = (μ : ℝ) := by
            calc
              a * (μ : ℝ) + b * (μ : ℝ) = (a + b) * (μ : ℝ) := by ring
              _ = (μ : ℝ) := by rw [hab, one_mul]
          calc
            (a * sx + b * sy) - μ = (a * sx + b * sy) - (a * (μ : ℝ) + b * (μ : ℝ)) := by
              rw [habμ]
            _ = a * (sx - μ) + b * (sy - μ) := by
              ring

-- Proof sketch: enlarging the smoothness constant preserves the derivative Lipschitz bound.
/-- Helper for Example 10.44: a function that is globally `L₁`-smooth is also globally
`L₂`-smooth whenever `L₁ ≤ L₂`. -/
lemma is_l_smooth_on_mono
    {h : E → ℝ} {L₁ L₂ : NNReal}
    (hh : is_l_smooth_on h Set.univ L₁) (hL : L₁ ≤ L₂) :
    is_l_smooth_on h Set.univ L₂ := by
  rw [is_l_smooth_on_iff] at hh ⊢
  refine ⟨hh.1, ?_⟩
  intro x hx y hy
  exact le_trans (hh.2 x hx y hy) (by gcongr)

-- Proof sketch: transport Proposition 5.7 through the dilation `x ↦ x / μ`, then multiply by
-- `μ` and subtract the constant `μ`.
/-- Helper for Example 10.44: the square-root smoothing is globally `1 / μ`-smooth. -/
lemma norm_smooth_approximation_is_l_smooth_on :
    is_l_smooth_on
      (norm_smooth_approximation (E := E) μ)
      Set.univ
      ((1 : NNReal) / PosReal.toNNReal μ) := by
  let Aμ : E →L[ℝ] E := ((1 / (μ : ℝ)) : ℝ) • ContinuousLinearMap.id ℝ E
  have hpre :
      is_l_smooth_on
        (fun x : E ↦ Real.sqrt (1 + ‖((1 / (μ : ℝ)) • x)‖ ^ (2 : ℕ)))
        Set.univ
        (1 * ‖Aμ‖₊ ^ (2 : ℕ)) := by
    -- Proposition 5.7 supplies the base profile, and the dilation contributes `‖Aμ‖²`.
    simpa [Aμ, ContinuousLinearMap.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      is_l_smooth_on_precompose_continuousLinearMap
        (A := Aμ)
        (fun z : E ↦ Real.sqrt (1 + ‖z‖ ^ (2 : ℕ)))
        sqrt_one_add_sq_norm_is_l_smooth_innerProductSpace
  have hscaled :
      is_l_smooth_on
        (fun x : E ↦ (μ : ℝ) * Real.sqrt (1 + ‖((1 / (μ : ℝ)) • x)‖ ^ (2 : ℕ)) - μ)
        Set.univ
        (Real.toNNReal (μ : ℝ) * (1 * ‖Aμ‖₊ ^ (2 : ℕ))) := by
    -- Outer multiplication by `μ` scales the Lipschitz constant once, and the shift `-μ`
    -- leaves it unchanged.
    exact is_l_smooth_on_const_mul_sub_const
      (μ : ℝ) (μ : ℝ) (le_of_lt (PosReal.coe_pos μ)) hpre
  have hAμ_norm_le : ‖Aμ‖ ≤ (μ : ℝ)⁻¹ := by
    -- The dilation `x ↦ x / μ` has operator norm at most `1 / μ`, with equality in the
    -- nontrivial case and a smaller norm in the trivial case.
    calc
      ‖Aμ‖ = ‖(1 / (μ : ℝ))‖ * ‖ContinuousLinearMap.id ℝ E‖ := by
            change ‖((1 / (μ : ℝ)) • ContinuousLinearMap.id ℝ E)‖ =
              ‖(1 / (μ : ℝ))‖ * ‖ContinuousLinearMap.id ℝ E‖
            rw [norm_smul]
      _ ≤ (μ : ℝ)⁻¹ * 1 := by
            rw [Real.norm_of_nonneg (le_of_lt (one_div_pos.mpr (PosReal.coe_pos μ)))]
            have hid_le : ‖ContinuousLinearMap.id ℝ E‖ ≤ 1 :=
              ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)
            simpa [one_div] using
              mul_le_mul_of_nonneg_left hid_le (le_of_lt (one_div_pos.mpr (PosReal.coe_pos μ)))
      _ = (μ : ℝ)⁻¹ := by ring
  have hconst_le :
      Real.toNNReal (μ : ℝ) * ‖Aμ‖₊ ^ (2 : ℕ) ≤
        (1 : NNReal) / PosReal.toNNReal μ := by
    -- The transported constant is bounded above by `1 / μ`.
    have hbound_real :
        (((Real.toNNReal (μ : ℝ) * ‖Aμ‖₊ ^ (2 : ℕ) : NNReal) : ℝ)) ≤
          ((((1 : NNReal) / PosReal.toNNReal μ : NNReal) : ℝ)) := by
      have hμ_nonneg : 0 ≤ (μ : ℝ) := le_of_lt (PosReal.coe_pos μ)
      have hAμ_sq_le : ‖Aμ‖ ^ (2 : ℕ) ≤ ((μ : ℝ)⁻¹) ^ (2 : ℕ) := by
        nlinarith [hAμ_norm_le, norm_nonneg Aμ]
      have hμ_ne : (μ : ℝ) ≠ 0 := ne_of_gt (PosReal.coe_pos μ)
      calc
        (((Real.toNNReal (μ : ℝ) * ‖Aμ‖₊ ^ (2 : ℕ) : NNReal) : ℝ))
            = (μ : ℝ) * ‖Aμ‖ ^ (2 : ℕ) := by
                simp [Real.toNNReal_of_nonneg hμ_nonneg]
        _ ≤ (μ : ℝ) * ((μ : ℝ)⁻¹) ^ (2 : ℕ) := by
              gcongr
        _ = (μ : ℝ)⁻¹ := by
              field_simp [hμ_ne]
        _ = ((((1 : NNReal) / PosReal.toNNReal μ : NNReal) : ℝ)) := by
              simp [PosReal.coe_toNNReal, div_eq_mul_inv]
    exact_mod_cast hbound_real
  -- Route correction: finish by rewriting the target function to the transported Chapter 5 profile.
  have hsmooth :
      is_l_smooth_on
        (fun x : E ↦ (μ : ℝ) * Real.sqrt (1 + ‖((1 / (μ : ℝ)) • x)‖ ^ (2 : ℕ)) - μ)
        Set.univ
        ((1 : NNReal) / PosReal.toNNReal μ) :=
    is_l_smooth_on_mono hscaled (by simpa [one_mul] using hconst_le)
  have hfun :
      norm_smooth_approximation (E := E) μ =
        (fun x : E ↦ (μ : ℝ) * Real.sqrt (1 + ‖((1 / (μ : ℝ)) • x)‖ ^ (2 : ℕ)) - μ) := by
    funext x
    exact norm_smooth_approximation_eq_rescaled_sqrt_one_add_sq_norm (μ := μ) x
  simpa [hfun] using hsmooth

end Example_10_44

-- Proof sketch: verify the lower and upper approximation bounds directly from
-- `√(‖x‖² + μ²) ≤ ‖x‖ + μ` and `‖x‖ ≤ √(‖x‖² + μ²)`, then rewrite
-- `norm_smooth_approximation μ` as
-- `μ * (fun z ↦ √(1 + ‖z‖²)) (x / μ) - μ` and combine Proposition 5.7 with the
-- standard smoothness scaling rule.
/-- The canonical radial smoothing `x ↦ √(‖x‖² + μ²) - μ` is a `1 / μ`-smooth approximation of
the ambient norm with parameters `(1, 1)`. -/
theorem norm_smooth_approximation_is_smooth_approximation
    (μ : PosReal) :
    IsSmoothApproximation
      (fun x : E ↦ ‖x‖)
      (norm_smooth_approximation μ) 1 1 μ := by
  refine
    { convex := Example_10_44.norm_smooth_approximation_convexOn (μ := μ)
      lower_le := ?_
      upper_le := ?_
      smooth := Example_10_44.norm_smooth_approximation_is_l_smooth_on (μ := μ) }
  · intro x
    -- The lower comparison is the first half of the pointwise square-root bounds.
    exact (Example_10_44.norm_smooth_approximation_bounds (μ := μ) x).1
  · intro x
    -- The upper comparison is the second half of the same bound pair.
    simpa using (Example_10_44.norm_smooth_approximation_bounds (μ := μ) x).2

-- Proof sketch: combine the companion approximation theorem for
-- `norm_smooth_approximation μ` with the convexity of the ambient norm,
-- then use that same companion theorem for each positive parameter `μ` in the existential clause
-- of `is_smoothable`.
/-- Example 10.44: on any proper real inner-product space, hence in particular on every
finite-dimensional Euclidean space `ℝ^n`, the norm is `(1, 1)`-smoothable, and for each `μ > 0`
the function `x ↦ √(‖x‖² + μ²) - μ` gives a `1 / μ`-smooth approximation. -/
theorem norm_is_one_one_smoothable :
    is_smoothable (fun x : E ↦ ‖x‖) 1 1 := by
  intro μ
  -- The smoothing family from the previous theorem witnesses the existential clause directly.
  refine ⟨norm_smooth_approximation μ, ?_⟩
  exact norm_smooth_approximation_is_smooth_approximation μ

end

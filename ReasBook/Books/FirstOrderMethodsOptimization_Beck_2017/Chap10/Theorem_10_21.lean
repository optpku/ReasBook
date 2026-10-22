/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_10
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Remark_10_19
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Remark_10_20
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable {f g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
variable [hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf]
variable {α : ℝ} {x : ℕ → E} {L : ℕ → PosReal} {xStar : E}

local notation "F" => composite_model_objective f g

namespace IsConvexCompositeSmoothMinimizationProblem

/-- Source-faithful stepsize owner for Theorem 10.21: either the exact constant stepsize rule
`L_k = L_f` with `α = 1`, or the genuine backtracking procedure B2 from Algorithm 10.3 with
`α = max {η, s / L_f}`. The B2 branch records the actual accepted-trial owner, not only the
trajectory-level upper-model shadow, because the source proof uses the resulting bound
`L_k ≤ α L_f`. -/
abbrev SourceSublinearRateStepsizeRule
    {XStar : Set E} {FOpt : ℝ}
    (hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    (x : ℕ → E) (L : ℕ → PosReal)
    (htraj : is_proximal_gradient_trajectory f g x L)
    (α : ℝ) : Prop :=
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  (α = 1 ∧ uses_proximal_gradient_Lf_stepsize_rule Lf L) ∨
    ∃ _ : 0 < (Lf : ℝ), ∃ s : PosReal, ∃ η : ProximalGradientBacktrackingGrowthFactor,
      α = max (η : ℝ) ((s : ℝ) / (Lf : ℝ)) ∧
        uses_proximal_gradient_backtracking_B2_rule f g x L htraj s η

end IsConvexCompositeSmoothMinimizationProblem

include hproblem

/-- Helper for Theorem 10.21: smoothness on `interior (effective_domain f)` implies the Chapter 3
differentiability predicate at every interior-domain point. -/
-- TODO: Rebuild Corollary 10.8's local bridge without importing the broken upstream file, by
-- converting `is_l_smooth_on` on `interior (effective_domain f)` into `is_differentiable_at`.
lemma differentiableAt_of_memInteriorEffectiveDomain
    {xPoint : E} (hxPoint : xPoint ∈ interior (effective_domain f)) :
    is_differentiable_at f xPoint := by
  -- Smoothness on the interior domain is exactly the differentiability predicate after
  -- rewriting `finite_domain f` to `effective_domain f`.
  simpa [is_differentiable_at, finite_domain_eq_effective_domain hproblem.f_ne_bot] using
    ⟨hxPoint, hproblem.f_toReal_smooth_on_interior_effective_domain.1 xPoint hxPoint⟩

/-- Helper for Theorem 10.21: on `effective_domain g`, the composite objective is the coercion of
the finite real sum `(f x).toReal + (g x).toReal`. -/
-- TODO: Port the finite-objective normalization proof from Theorem 10.15 locally, using
-- `effective_domain g ⊆ interior (effective_domain f)` to show both summands are finite.
lemma objectiveEqReal_of_memEffectiveDomainG
    {xPoint : E} (hxPoint : xPoint ∈ effective_domain g) :
    F xPoint = ((((f xPoint).toReal + (g xPoint).toReal : ℝ)) : EReal) := by
  have hfxPoint : xPoint ∈ effective_domain f := by
    exact
      interior_subset
        (hproblem.g_effective_domain_subset_interior_f_effective_domain hxPoint)
  have hfx_val :
      f xPoint = ((((f xPoint).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hfxPoint).ne (hproblem.f_ne_bot xPoint)).symm
  have hgx_val :
      g xPoint = ((((g xPoint).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hxPoint).ne
        (hproblem.g_proper.ne_bot xPoint)).symm
  -- Once both summands are finite, the composite objective is the cast of the real sum.
  rw [composite_model_objective_apply, hfx_val, hgx_val]
  simp [EReal.coe_add]

/-- Helper for Theorem 10.21: a finite objective gap to the optimal value is the cast of the
corresponding real difference. -/
-- TODO: After the finite-objective normalization lemma is restored, rewrite `F xPoint` through its
-- real representative and simplify the resulting `EReal` subtraction.
lemma objectiveMinusFOpt_eq_coe_sub_toReal_of_memEffectiveDomainG
    {xPoint : E} (hxPoint : xPoint ∈ effective_domain g) :
    ((((F xPoint).toReal - FOpt : ℝ) : EReal)) =
      F xPoint - (FOpt : EReal) := by
  have hxPoint_val :
      F xPoint = ((((f xPoint).toReal + (g xPoint).toReal : ℝ)) : EReal) :=
    objectiveEqReal_of_memEffectiveDomainG
      (hproblem := hproblem)
      hxPoint
  have hxPoint_toReal :
      (F xPoint).toReal = (f xPoint).toReal + (g xPoint).toReal := by
    rw [hxPoint_val]
    simpa using EReal.toReal_coe ((f xPoint).toReal + (g xPoint).toReal)
  -- Rewrite the finite objective value through its real representative before subtracting `FOpt`.
  rw [hxPoint_toReal, hxPoint_val]
  simp [EReal.coe_sub]

/-- Helper for Theorem 10.21: every feasible point has objective value at least the optimal lower
bound `FOpt`. -/
-- TODO: Combine `hproblem.optimal_value_isGLB` with the finite-objective normalization lemma to
-- transport the lower-bound statement from `EReal` to `ℝ`.
lemma toReal_ge_FOpt_of_memEffectiveDomainG
    {xPoint : E} (hxPoint : xPoint ∈ effective_domain g) :
    FOpt ≤ (F xPoint).toReal := by
  have hxPoint_val :
      F xPoint = ((((f xPoint).toReal + (g xPoint).toReal : ℝ)) : EReal) :=
    objectiveEqReal_of_memEffectiveDomainG
      (hproblem := hproblem)
      hxPoint
  have hxPoint_toReal :
      (F xPoint).toReal = (f xPoint).toReal + (g xPoint).toReal := by
    rw [hxPoint_val]
    simpa using EReal.toReal_coe ((f xPoint).toReal + (g xPoint).toReal)
  have hxPoint_finite :
      (((F xPoint).toReal : ℝ) : EReal) = F xPoint := by
    rw [hxPoint_toReal, hxPoint_val]
  have hlower : (FOpt : EReal) ≤ F xPoint := hproblem.optimal_value_isGLB.1 ⟨xPoint, rfl⟩
  -- Once the feasible objective value is known to be finite, the `EReal` lower bound reads as a
  -- plain real inequality.
  rw [← hxPoint_finite] at hlower
  exact EReal.coe_le_coe_iff.mp hlower

/-- Helper for Theorem 10.21: every positive-index proximal-gradient iterate lies in
`effective_domain g` because it is realized by the prox-gradient operator. -/
lemma proximalGradientPositiveIterate_memEffectiveDomainG
    (htraj : is_proximal_gradient_trajectory f g x L)
    (k : ℕ) :
    x (k + 1) ∈ effective_domain g := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  let xk := proximal_gradient_trajectory_iterate htraj k
  rw [proximal_gradient_trajectory_succ_eq_operator htraj k]
  exact prox_grad_operator_mem_effective_domain_g (f := f) (g := g) (L := L k) (x := xk)

/-- Helper for Theorem 10.21: summing real successive differences over a prefix telescopes to the
initial-minus-terminal value. -/
lemma realPrefixTelescope
    (φ : ℕ → ℝ) (K : ℕ) :
    Finset.sum (Finset.range (K + 1)) (fun i ↦ φ i - φ (i + 1)) =
      φ 0 - φ (K + 1) := by
  have htel := Finset.sum_range_sub φ (K + 1)
  calc
    Finset.sum (Finset.range (K + 1)) (fun i ↦ φ i - φ (i + 1)) =
      Finset.sum (Finset.range (K + 1)) (fun i ↦ -(φ (i + 1) - φ i)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        ring
    _ = -Finset.sum (Finset.range (K + 1)) (fun i ↦ φ (i + 1) - φ i) := by
      rw [Finset.sum_neg_distrib]
    _ = -(φ (K + 1) - φ 0) := by
      rw [htel]
    _ = φ 0 - φ (K + 1) := by
      ring

/-- Helper for Theorem 10.21: the source-faithful stepsize owner refines directly to Remark
10.19's canonical sublinear-rate owner. -/
lemma sourceSublinearRateRule_sublinearRateStepsizeRule
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SourceSublinearRateStepsizeRule x L htraj α) :
    hproblem.SublinearRateStepsizeRule x L htraj α := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  rcases hrule with ⟨hα, hLf_rule⟩ | ⟨hLf, s, η, hα, hB2⟩
  · exact Or.inl ⟨hα, hLf_rule⟩
  · refine Or.inr ?_
    refine ⟨hLf, s, η, hα, ?_⟩
    exact
      uses_proximal_gradient_backtracking_B2_rule_upperModel
        (f := f)
        (g := g)
        hproblem.f_ne_bot
        hB2

/-- Helper for Theorem 10.21: forgetting the source-faithful constant/B2 stepsize owner keeps the
same constant-rule/B2-procedure dichotomy needed for the accepted upper-model inequality. -/
lemma sourceSublinearRateRule_constantOrBacktrackingB2
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SourceSublinearRateStepsizeRule x L htraj α) :
    hproblem.ConstantOrBacktrackingB2StepsizeRule x L htraj := by
  -- Pass through Remark 10.19's canonical sublinear-rate owner, then forget `α`.
  exact
    hproblem.sublinearRateStepsizeRule_constantOrBacktrackingB2
      (sourceSublinearRateRule_sublinearRateStepsizeRule htraj hrule)

/-- Helper for Theorem 10.21: every source-faithful stepsize sequence satisfies the uniform bound
`L_n ≤ α L_f` from the textbook constant-rule/B2 dichotomy. -/
-- TODO: In the constant branch, rewrite `L_n = L_f`; in the B2 branch, combine Remark 10.19's
-- global bound `L_n ≤ max {η L_f, s}` with `α = max {η, s / L_f}`.
lemma sourceSublinearRateRule_stepsizeBound
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SourceSublinearRateStepsizeRule x L htraj α) :
    ∀ n, (L n : ℝ) ≤ α * (Lf : ℝ) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  intro n
  rcases hrule with ⟨hα, hLf_rule⟩ | ⟨hLf_pos, s, η, hα, hB2⟩
  · -- In the constant branch, the stepsize rule is exactly `L_n = L_f`.
    rw [hα, hLf_rule n]
    simpa using (le_rfl : (Lf : ℝ) ≤ (Lf : ℝ))
  · -- In the B2 branch, combine Remark 10.19's global bound with `α = max {η, s / L_f}`.
    rcases
        proximal_gradient_backtracking_B2_stepsize_bounds
          (Lf := Lf)
          (f := f)
          (g := g)
          hproblem.f_ne_bot
          hproblem.f_effective_domain_convex
          hproblem.g_effective_domain_subset_interior_f_effective_domain
          hproblem.f_toReal_smooth_on_interior_effective_domain
          htraj
          s
          η
          hB2
          n with
      ⟨_, hL_upper⟩
    have hη_upper : (η : ℝ) * (Lf : ℝ) ≤ α * (Lf : ℝ) := by
      rw [hα]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt hLf_pos)
    have hs_upper : (s : ℝ) ≤ α * (Lf : ℝ) := by
      rw [hα]
      exact (div_le_iff₀ hLf_pos).1 (le_max_right _ _)
    have hmax_upper : max ((η : ℝ) * (Lf : ℝ)) (s : ℝ) ≤ α * (Lf : ℝ) := by
      exact max_le hη_upper hs_upper
    exact le_trans hL_upper hmax_upper

/-- Helper for Theorem 10.21: convexity of `f` makes the prox-gradient linearization defect
nonnegative at every base point in `interior (effective_domain f)`. -/
-- TODO: Port the supporting-hyperplane argument used in Theorem 10.72's convex support lemma to
-- the Chapter 10 defect notation `ℓ[f, xPoint, y]`.
lemma convexLinearizationDefect_nonneg
    {xPoint : E} (hxPoint : xPoint ∈ effective_domain f)
    (y : interior (effective_domain f)) :
    (0 : EReal) ≤ ℓ[f, xPoint, y] := by
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap (y : E) xPoint
  let φ : ℝ → ℝ := fun t ↦ (f (line t)).toReal
  have hconv :
      ConvexOn ℝ (effective_domain f) (fun z ↦ (f z).toReal) :=
    convexOn_toReal_of_is_convex_function hproblem.f_convex
      (fun z _ ↦ hproblem.f_ne_bot z)
  have hφ_convex :
      ConvexOn ℝ (line ⁻¹' effective_domain f) φ := by
    -- Restrict the convex real-valued model of `f` to the segment from `y` to `xPoint`.
    simpa [φ, line] using hconv.comp_affineMap line
  have hφ_zero :
      (0 : ℝ) ∈ line ⁻¹' effective_domain f := by
    simpa [line] using interior_subset y.2
  have hφ_one :
      (1 : ℝ) ∈ line ⁻¹' effective_domain f := by
    simpa [line] using hxPoint
  have hyDiff :
      DifferentiableAt ℝ (fun z ↦ (f z).toReal) (y : E) := by
    exact (differentiableAt_of_memInteriorEffectiveDomain (hproblem := hproblem) y.2).2
  have hφ_deriv :
      HasDerivAt φ
        (inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (xPoint - (y : E))) 0 := by
    -- Differentiate the segment restriction and identify the derivative with the gradient pairing.
    have hcomp :
        HasDerivAt φ
          (fderiv ℝ (fun z ↦ (f z).toReal) (y : E) (xPoint - (y : E))) 0 := by
      have hbase :
          HasFDerivAt (fun z ↦ (f z).toReal)
            (fderiv ℝ (fun z ↦ (f z).toReal) (y : E)) (line 0) := by
        simpa [line] using hyDiff.hasFDerivAt
      have hline : HasDerivAt line (xPoint - (y : E)) 0 := by
        simpa [line] using
          (show HasDerivAt (AffineMap.lineMap (y : E) xPoint) (xPoint - (y : E)) (0 : ℝ) from
            AffineMap.hasDerivAt_lineMap)
      simpa [φ, line] using HasFDerivAt.comp_hasDerivAt 0 hbase hline
    have hgrad :
        fderiv ℝ (fun z ↦ (f z).toReal) (y : E) (xPoint - (y : E)) =
          inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (xPoint - (y : E)) := by
      simpa using
        (show
            fderiv ℝ (fun z ↦ (f z).toReal) (y : E) (xPoint - (y : E)) =
              inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (xPoint - (y : E)) from
          HasGradientAt.fderiv_apply hyDiff.hasGradientAt)
    simpa [hgrad] using hcomp
  have hsupport :
      inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (xPoint - (y : E)) ≤
        (f xPoint).toReal - (f (y : E)).toReal := by
    have hsecant :
        inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (xPoint - (y : E)) ≤
          slope φ 0 1 := by
      -- Convexity bounds the derivative at the left endpoint by the secant slope.
      exact hφ_convex.le_slope_of_hasDerivAt hφ_zero hφ_one zero_lt_one hφ_deriv
    simpa [φ, line, slope] using hsecant
  have hreal :
      0 ≤
        (f xPoint).toReal - (f (y : E)).toReal -
          inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (xPoint - (y : E)) := by
    linarith
  have hfx_val :
      f xPoint = ((((f xPoint).toReal : ℝ)) : EReal) := by
    exact (EReal.coe_toReal (mem_effective_domain.mp hxPoint).ne (hproblem.f_ne_bot xPoint)).symm
  have hfy_val :
      f (y : E) = ((((f (y : E)).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp (interior_subset y.2)).ne
        (hproblem.f_ne_bot (y : E))).symm
  -- Rewrite the defect once and then read the supporting-hyperplane inequality on the real layer.
  rw [prox_gradient_linearization_defect_eq, hfx_val, hfy_val]
  simpa [EReal.coe_sub] using (EReal.coe_le_coe_iff.mpr hreal)

/-- Helper for Theorem 10.21: one proximal-gradient step bounds the normalized objective gap by
the drop in squared distance to an optimizer. -/
-- TODO: Specialize Theorem 10.16 at `(xStar, x^n, L_n)`, drop the nonnegative defect term using
-- convexity, then convert the finite objective gap to the normalized real inequality.
lemma proximalGradientOneStepGapDivLeDistSqDrop
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SourceSublinearRateStepsizeRule x L htraj α)
    (hxStar : xStar ∈ XStar)
    (n : ℕ) :
    ((F (x (n + 1))).toReal - FOpt) / (α * (Lf : ℝ)) ≤
      (‖xStar - x n‖ ^ (2 : ℕ) - ‖xStar - x (n + 1)‖ ^ (2 : ℕ)) / 2 := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  let xn := proximal_gradient_trajectory_iterate htraj n
  have hcanon :
      hproblem.SublinearRateStepsizeRule x L htraj α :=
    sourceSublinearRateRule_sublinearRateStepsizeRule htraj hrule
  have hα_pos : 0 < α :=
    hproblem.sublinearRateStepsizeRule_alpha_pos hcanon
  have hLf_pos : 0 < (Lf : ℝ) :=
    hproblem.sublinearRateStepsizeRule_lf_pos hcanon
  have hαLf_pos : 0 < α * (Lf : ℝ) := mul_pos hα_pos hLf_pos
  have haccepts :
      proximal_gradient_backtracking_B2_accepts f g (L n) xn := by
    -- The source-faithful rule still gives the accepted upper-model inequality at iteration `n`.
    exact
      proximal_gradient_constant_or_backtracking_B2_stepsize_accepts
        hproblem.f_ne_bot
        hproblem.f_effective_domain_convex
        hproblem.g_effective_domain_subset_interior_f_effective_domain
        hproblem.f_toReal_smooth_on_interior_effective_domain
        htraj
        (sourceSublinearRateRule_constantOrBacktrackingB2 htraj hrule)
        n
  have hFxStar :
      F xStar = (FOpt : EReal) :=
    hproblem.objective_eq_optimalValue_of_mem_optimalSet hxStar
  have hxStar_eff_g :
      xStar ∈ effective_domain g := by
    have hg_ne_top : g xStar ≠ ⊤ := by
      intro hg_top
      have htop : F xStar = ⊤ := by
        calc
          F xStar = f xStar + g xStar := by rfl
          _ = f xStar + ⊤ := by rw [hg_top]
          _ = ⊤ := EReal.add_top_of_ne_bot (hproblem.f_ne_bot xStar)
      rw [htop] at hFxStar
      exact EReal.coe_ne_top FOpt hFxStar.symm
    exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hg_ne_top)
  have hxStar_eff_f :
      xStar ∈ effective_domain f := by
    exact
      interior_subset
        (hproblem.g_effective_domain_subset_interior_f_effective_domain hxStar_eff_g)
  have hxsucc_g :
      x (n + 1) ∈ effective_domain g := by
    exact proximalGradientPositiveIterate_memEffectiveDomainG (hproblem := hproblem) htraj n
  have hfund :
      F xStar - F (x (n + 1)) ≥
        (((((L n : ℝ) / 2) * ‖xStar - x (n + 1)‖ ^ (2 : ℕ) -
            ((L n : ℝ) / 2) * ‖xStar - x n‖ ^ (2 : ℕ) : ℝ)) : EReal) +
          ℓ[f, xStar, xn] := by
    -- Specialize Theorem 10.16 at the optimizer `xStar` and the current iterate `x^n`.
    simpa [xn, proximal_gradient_trajectory_succ_eq_operator htraj n] using
      (fundamental_prox_grad_inequality
        (f := f)
        (g := g)
        xStar
        xn
        (L n)
        haccepts)
  have hdefect_nonneg :
      (0 : EReal) ≤ ℓ[f, xStar, xn] := by
    -- Convexity lets us drop the linearization defect from the one-step inequality.
    simpa [xn] using
      convexLinearizationDefect_nonneg
        (hproblem := hproblem)
        hxStar_eff_f
        xn
  have hstepE :
      (((((L n : ℝ) / 2) * ‖xStar - x (n + 1)‖ ^ (2 : ℕ) -
          ((L n : ℝ) / 2) * ‖xStar - x n‖ ^ (2 : ℕ) : ℝ)) : EReal) ≤
        F xStar - F (x (n + 1)) := by
    have hbase :
        (((((L n : ℝ) / 2) * ‖xStar - x (n + 1)‖ ^ (2 : ℕ) -
            ((L n : ℝ) / 2) * ‖xStar - x n‖ ^ (2 : ℕ) : ℝ)) : EReal) ≤
          (((((L n : ℝ) / 2) * ‖xStar - x (n + 1)‖ ^ (2 : ℕ) -
              ((L n : ℝ) / 2) * ‖xStar - x n‖ ^ (2 : ℕ) : ℝ)) : EReal) +
            ℓ[f, xStar, xn] := by
      exact le_add_of_nonneg_right hdefect_nonneg
    exact le_trans hbase hfund
  have hxsucc_value :
      F (x (n + 1)) = ((((F (x (n + 1))).toReal : ℝ)) : EReal) := by
    rw [objectiveEqReal_of_memEffectiveDomainG (hproblem := hproblem) hxsucc_g, EReal.toReal_coe]
  have hstep_real :
      ((L n : ℝ) / 2) * ‖xStar - x (n + 1)‖ ^ (2 : ℕ) -
          ((L n : ℝ) / 2) * ‖xStar - x n‖ ^ (2 : ℕ) ≤
        FOpt - (F (x (n + 1))).toReal := by
    rw [hFxStar, hxsucc_value] at hstepE
    exact EReal.coe_le_coe_iff.mp (by simpa [EReal.coe_sub] using hstepE)
  have hgap_nonneg :
      0 ≤ (F (x (n + 1))).toReal - FOpt := by
    exact sub_nonneg.mpr (toReal_ge_FOpt_of_memEffectiveDomainG (hproblem := hproblem) hxsucc_g)
  have hgap_drop :
      (F (x (n + 1))).toReal - FOpt ≤
        ((L n : ℝ) / 2) *
          (‖xStar - x n‖ ^ (2 : ℕ) - ‖xStar - x (n + 1)‖ ^ (2 : ℕ)) := by
    nlinarith
  have hdrop_nonneg :
      0 ≤ ‖xStar - x n‖ ^ (2 : ℕ) - ‖xStar - x (n + 1)‖ ^ (2 : ℕ) := by
    have hprod_nonneg :
        0 ≤
          ((L n : ℝ) / 2) *
            (‖xStar - x n‖ ^ (2 : ℕ) - ‖xStar - x (n + 1)‖ ^ (2 : ℕ)) := by
      linarith
    have hhalf_pos : 0 < (L n : ℝ) / 2 := by
      exact div_pos (L n).2 (by norm_num)
    by_contra hdrop_neg
    have hprod_neg :
        ((L n : ℝ) / 2) *
            (‖xStar - x n‖ ^ (2 : ℕ) - ‖xStar - x (n + 1)‖ ^ (2 : ℕ)) < 0 := by
      exact mul_neg_of_pos_of_neg hhalf_pos (lt_of_not_ge hdrop_neg)
    linarith
  have hcoeff_le :
      ((L n : ℝ) / 2) ≤ (α * (Lf : ℝ)) / 2 := by
    nlinarith [sourceSublinearRateRule_stepsizeBound htraj hrule n]
  have huniform_gap :
      (F (x (n + 1))).toReal - FOpt ≤
        ((α * (Lf : ℝ)) / 2) *
          (‖xStar - x n‖ ^ (2 : ℕ) - ‖xStar - x (n + 1)‖ ^ (2 : ℕ)) := by
    have hscaled :
        ((L n : ℝ) / 2) *
            (‖xStar - x n‖ ^ (2 : ℕ) - ‖xStar - x (n + 1)‖ ^ (2 : ℕ)) ≤
          ((α * (Lf : ℝ)) / 2) *
            (‖xStar - x n‖ ^ (2 : ℕ) - ‖xStar - x (n + 1)‖ ^ (2 : ℕ)) := by
      exact mul_le_mul_of_nonneg_right hcoeff_le hdrop_nonneg
    exact le_trans hgap_drop hscaled
  -- Clear the positive factor `α L_f` to reach the normalized real form of the source estimate.
  exact (div_le_iff₀ hαLf_pos).2 (by
    nlinarith [huniform_gap])

/-- Helper for Theorem 10.21: summing the normalized one-step bounds over a prefix telescopes to
the initial squared distance to the optimizer. -/
-- TODO: Sum the one-step gap inequality over `i = 0, ..., K`, telescope the squared-distance
-- differences with `realPrefixTelescope`, and drop the terminal nonnegative distance term.
lemma proximalGradientRealPrefixTelescope
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SourceSublinearRateStepsizeRule x L htraj α)
    (hxStar : xStar ∈ XStar)
    (K : ℕ) :
    Finset.sum (Finset.range (K + 1))
      (fun i ↦ ((F (x (i + 1))).toReal - FOpt) / (α * (Lf : ℝ))) ≤
      ‖x 0 - xStar‖ ^ (2 : ℕ) / 2 := by
  let φ : ℕ → ℝ := fun i ↦ ‖xStar - x i‖ ^ (2 : ℕ)
  have hsum :
      Finset.sum (Finset.range (K + 1))
          (fun i ↦ ((F (x (i + 1))).toReal - FOpt) / (α * (Lf : ℝ))) ≤
        Finset.sum (Finset.range (K + 1)) (fun i ↦ (φ i - φ (i + 1)) / 2) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    simpa [φ] using proximalGradientOneStepGapDivLeDistSqDrop htraj hrule hxStar i
  have htel :
      Finset.sum (Finset.range (K + 1)) (fun i ↦ (φ i - φ (i + 1)) / 2) =
        (φ 0 - φ (K + 1)) / 2 := by
    calc
      Finset.sum (Finset.range (K + 1)) (fun i ↦ (φ i - φ (i + 1)) / 2) =
          (Finset.sum (Finset.range (K + 1)) (fun i ↦ φ i - φ (i + 1))) / 2 := by
            calc
              Finset.sum (Finset.range (K + 1)) (fun i ↦ (φ i - φ (i + 1)) / 2) =
                  Finset.sum (Finset.range (K + 1))
                    (fun i ↦ (φ i - φ (i + 1)) * (1 / 2 : ℝ)) := by
                      simp [div_eq_mul_inv]
              _ = (Finset.sum (Finset.range (K + 1)) (fun i ↦ φ i - φ (i + 1))) *
                    (1 / 2 : ℝ) := by
                      rw [Finset.sum_mul]
              _ = (Finset.sum (Finset.range (K + 1)) (fun i ↦ φ i - φ (i + 1))) / 2 := by
                    simp [div_eq_mul_inv]
      _ = (φ 0 - φ (K + 1)) / 2 := by
        rw [realPrefixTelescope (hproblem := hproblem) φ K]
  have hterminal_nonneg : 0 ≤ φ (K + 1) := by
    positivity
  have hdrop_terminal :
      (φ 0 - φ (K + 1)) / 2 ≤ φ 0 / 2 := by
    nlinarith
  exact le_trans hsum <| by
    rw [htel]
    simpa [φ, norm_sub_rev] using hdrop_terminal

/- Theorem 10.21 is `source-facing` in the convex proximal-gradient API.

Domain sampling in the existing chapter identifies:
- `IsConvexCompositeSmoothMinimizationProblem` as the owner of Assumption 10.1 plus convexity of
  `f`;
- `is_proximal_gradient_trajectory` as the owner of the iterate sequence `x^k`;
- `hproblem.SourceSublinearRateStepsizeRule` below as the source-faithful owner of the admissible
  constant/B2 stepsize regimes together with the auxiliary constant `α`;
- `hproblem.SublinearRateStepsizeRule` from Remark 10.19 only as a weaker bridge/view surface
  that remembers the B2 upper-model inequality but not the full accepted-trial rule.

The source proof of Theorem 10.21 uses the global B2 stepsize bound `L_k ≤ α L_f`, so the public
theorem must quantify over the exact constant-rule/B2-procedure dichotomy rather than the weaker
upper-model owner from Remark 10.19. The objective-gap estimate remains derived API over that
source-faithful stepsize owner and does not introduce unrelated optimizer data. -/

-- Proof sketch: apply the fundamental prox-gradient inequality from Theorem 10.16 with
-- `x = xStar`, `y = x^n`, and `L = L_n`, then use the convexity of `f` to make the
-- linearization error nonnegative. Sum the resulting inequalities from `n = 0` to `k - 1`,
-- use Remark 10.19 to bound every `L_n` by `α L_f`, and finally use the monotonicity from
-- Remark 10.20 to pass from the averaged bound to the pointwise estimate at the positive index
-- `k`.
/-- Theorem 10.21: under Assumption 10.1, if `f` is convex and `x^k` is generated by the
proximal gradient method with either the constant stepsize rule `L_k = L_f` or backtracking
procedure B2, then every positive
iterate satisfies the sublinear objective-gap estimate
`F(x^k) - F_opt ≤ α L_f ‖x^0 - x*‖² / (2 k)`. -/
-- TODO: Reindex `k = K + 1`, combine the prefix telescope with Remark 10.20 monotonicity to
-- pass from the averaged prefix bound to the pointwise objective-gap estimate, then coerce back
-- to the displayed `EReal` statement.
theorem proximal_gradient_convex_objective_gap_le
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SourceSublinearRateStepsizeRule x L htraj α)
    (hxStar : xStar ∈ XStar)
    (k : ℕ) (hk : 1 ≤ k) :
    F (x k) - (FOpt : EReal) ≤
      ((α * (Lf : ℝ) * ‖x 0 - xStar‖ ^ (2 : ℕ) / (2 * (k : ℝ)) : ℝ) : EReal) := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le hk
  suffices
      F (x (K + 1)) - (FOpt : EReal) ≤
        ((α * (Lf : ℝ) * ‖x 0 - xStar‖ ^ (2 : ℕ) / (2 * ((K + 1 : ℕ) : ℝ)) : ℝ) : EReal) by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  have hcanon :
      hproblem.SublinearRateStepsizeRule x L htraj α :=
    sourceSublinearRateRule_sublinearRateStepsizeRule htraj hrule
  have hα_pos : 0 < α :=
    hproblem.sublinearRateStepsizeRule_alpha_pos hcanon
  have hLf_pos : 0 < (Lf : ℝ) :=
    hproblem.sublinearRateStepsizeRule_lf_pos hcanon
  have hαLf_pos : 0 < α * (Lf : ℝ) := mul_pos hα_pos hLf_pos
  have hbase_rule :
      hproblem.ConstantOrBacktrackingB2StepsizeRule x L htraj :=
    sourceSublinearRateRule_constantOrBacktrackingB2 htraj hrule
  have hanti : Antitone (fun n ↦ F (x n)) := by
    refine antitone_nat_of_succ_le ?_
    intro n
    have hdiff : is_differentiable_at f (x n) := by
      exact
        differentiableAt_of_memInteriorEffectiveDomain
          (hproblem := hproblem)
          (xPoint := x n)
          (proximal_gradient_trajectory_mem_interior_effective_domain htraj n)
    have hmodel :
        f (x (n + 1)) ≤
          (((f (x n)).toReal +
              inner ℝ (∇ (fun y ↦ (f y).toReal) (x n)) (x (n + 1) - x n) +
              ((L n : ℝ) / 2) * ‖x (n + 1) - x n‖ ^ (2 : ℕ) : ℝ) : EReal) := by
      exact hproblem.upper_model_of_constantOrBacktrackingB2Rule htraj hbase_rule n
    exact composite_model_objective_monotone_of_upper_model htraj n hdiff hmodel
  have hprefix :=
    proximalGradientRealPrefixTelescope htraj hrule hxStar K
  have objectiveEqCoeToReal :
      ∀ {z : E}, z ∈ effective_domain g →
        F z = ((((F z).toReal : ℝ)) : EReal) := by
    intro z hz
    rw [objectiveEqReal_of_memEffectiveDomainG (hproblem := hproblem) hz, EReal.toReal_coe]
  have hK_eff :
      x (K + 1) ∈ effective_domain g :=
    proximalGradientPositiveIterate_memEffectiveDomainG (hproblem := hproblem) htraj K
  have hsum_lower :
      Finset.sum (Finset.range (K + 1))
          (fun _ ↦ ((F (x (K + 1))).toReal - FOpt) / (α * (Lf : ℝ))) ≤
        Finset.sum (Finset.range (K + 1))
          (fun i ↦ ((F (x (i + 1))).toReal - FOpt) / (α * (Lf : ℝ))) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi_le : i + 1 ≤ K + 1 := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    have hi_eff :
        x (i + 1) ∈ effective_domain g :=
      proximalGradientPositiveIterate_memEffectiveDomainG (hproblem := hproblem) htraj i
    have hmonoE : F (x (K + 1)) ≤ F (x (i + 1)) := hanti hi_le
    have hmono_real :
        (F (x (K + 1))).toReal ≤ (F (x (i + 1))).toReal := by
      rw [objectiveEqCoeToReal hK_eff, objectiveEqCoeToReal hi_eff] at hmonoE
      exact EReal.coe_le_coe_iff.mp hmonoE
    have hgap_real :
        (F (x (K + 1))).toReal - FOpt ≤ (F (x (i + 1))).toReal - FOpt := by
      exact sub_le_sub_right hmono_real FOpt
    exact (div_le_div_iff_of_pos_right hαLf_pos).2 hgap_real
  have hsum_const :
      Finset.sum (Finset.range (K + 1))
          (fun _ ↦ ((F (x (K + 1))).toReal - FOpt) / (α * (Lf : ℝ))) =
        (K + 1 : ℝ) * (((F (x (K + 1))).toReal - FOpt) / (α * (Lf : ℝ))) := by
    simp [nsmul_eq_mul]
  have havg_bound :
      (K + 1 : ℝ) * (((F (x (K + 1))).toReal - FOpt) / (α * (Lf : ℝ))) ≤
        ‖x 0 - xStar‖ ^ (2 : ℕ) / 2 := by
    calc
      (K + 1 : ℝ) * (((F (x (K + 1))).toReal - FOpt) / (α * (Lf : ℝ))) =
          Finset.sum (Finset.range (K + 1))
            (fun _ ↦ ((F (x (K + 1))).toReal - FOpt) / (α * (Lf : ℝ))) := by
              symm
              exact hsum_const
      _ ≤ Finset.sum (Finset.range (K + 1))
            (fun i ↦ ((F (x (i + 1))).toReal - FOpt) / (α * (Lf : ℝ))) := hsum_lower
      _ ≤ ‖x 0 - xStar‖ ^ (2 : ℕ) / 2 := hprefix
  have hK1_pos : 0 < (K + 1 : ℝ) := by
    positivity
  have hnormalized :
      ((F (x (K + 1))).toReal - FOpt) / (α * (Lf : ℝ)) ≤
        ‖x 0 - xStar‖ ^ (2 : ℕ) / (2 * (K + 1 : ℝ)) := by
    have htmp :
        ((F (x (K + 1))).toReal - FOpt) / (α * (Lf : ℝ)) ≤
          (‖x 0 - xStar‖ ^ (2 : ℕ) / 2) / (K + 1 : ℝ) := by
      exact (le_div_iff₀ hK1_pos).2 <| by
        simpa [mul_assoc, mul_left_comm, mul_comm] using havg_bound
    have hrewrite :
        (‖x 0 - xStar‖ ^ (2 : ℕ) / 2) / (K + 1 : ℝ) =
          ‖x 0 - xStar‖ ^ (2 : ℕ) / (2 * (K + 1 : ℝ)) := by
      field_simp [hK1_pos.ne']
    rw [hrewrite] at htmp
    exact htmp
  have hreal :
      (F (x (K + 1))).toReal - FOpt ≤
        α * (Lf : ℝ) * ‖x 0 - xStar‖ ^ (2 : ℕ) / (2 * (K + 1 : ℝ)) := by
    have hscaled :
        (F (x (K + 1))).toReal - FOpt ≤
          (‖x 0 - xStar‖ ^ (2 : ℕ) / (2 * (K + 1 : ℝ))) * (α * (Lf : ℝ)) :=
      (div_le_iff₀ hαLf_pos).1 hnormalized
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
  -- Convert the final real estimate back to the public `EReal` objective-gap statement.
  rw [← objectiveMinusFOpt_eq_coe_sub_toReal_of_memEffectiveDomainG
    (hproblem := hproblem) hK_eff]
  simpa [Nat.cast_add, Nat.cast_one, mul_assoc, mul_left_comm, mul_comm] using
    (EReal.coe_le_coe_iff.mpr hreal)

/-- Bridge/view layer: reindexing Theorem 10.21 from `k : ℕ` with
`1 ≤ k` to `k : ℕ+` gives the
same sublinear objective-gap estimate at the positive iterate `x^k`. -/
lemma proximal_gradient_convex_objective_gap_le_at_pnat
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SourceSublinearRateStepsizeRule x L htraj α)
    (hxStar : xStar ∈ XStar)
    (k : ℕ+) :
    F (x k) - (FOpt : EReal) ≤
      ((α * (Lf : ℝ) * ‖x 0 - xStar‖ ^ (2 : ℕ) / (2 * (k : ℝ)) : ℝ) : EReal) := by
  simpa using
    proximal_gradient_convex_objective_gap_le htraj hrule hxStar k k.property

end

end

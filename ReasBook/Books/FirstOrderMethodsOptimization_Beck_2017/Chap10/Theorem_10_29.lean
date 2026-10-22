/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_21
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Remark_10_19
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_15
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [ProperSpace E]

/- Theorem 10.29 is `source-facing` in the strongly-convex proximal-gradient API.

Domain sampling in the existing Chapter 10 development identifies:
- `IsCompositeSmoothMinimizationProblem` as the owner of Assumption 10.1;
- `is_proximal_gradient_trajectory` as the owner of the iterate sequence `x^k`;
- `hproblem.SublinearRateStepsizeRule x L htraj α` from Remark 10.19 as the chapter owner of the
  admissible constant/B2 stepsize regime together with its rate factor `α`;
- `condition_number` from Definition 10.21, with notation `κ(L_f, σ)`, as the chapter owner of
  the ratio `L_f / σ`.

Primitive data are the problem instance, trajectory, stepsize rule, strong-convexity modulus, and
optimal point. Definition 10.3 already canonically supplies the properness, lower-semicontinuity,
and convexity data for `g`, so those assumptions should not be duplicated on the theorem surface.
The stepsize hypothesis should therefore use the existing owner-level bridge from Remark 10.19,
rather than repeating its internal disjunction and local instance plumbing. The geometric
contraction factor is derived API, so the statements below reuse `κ(Lf, σ)` instead of restating
`L_f / σ` through parallel local arithmetic. -/

section

variable {f g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
variable [hproblem : IsCompositeSmoothMinimizationProblem f g XStar FOpt Lf]
variable {σ : PosReal} {α : ℝ} {x : ℕ → E} {L : ℕ → PosReal} {xStar : E}

local notation "F" => composite_model_objective f g
local notation "κ" => κ(Lf, σ)

/-- Helper for Theorem 10.29: any optimizer `xStar ∈ XStar` attains the optimal composite value
`FOpt`. -/
lemma objective_eq_optimal_value_of_mem_optimal_set
    (h : IsCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    {x : E} (hx : x ∈ XStar) :
    F x = (FOpt : EReal) := by
  -- The optimizer-set field identifies `x` as a global minimizer of the composite objective.
  apply le_antisymm
  · exact h.optimal_value_isGLB.2 <| by
      rintro _ ⟨y, rfl⟩
      have hx_opt : x ∈ unconstrained_problem_solutions F := by
        change x ∈ unconstrained_problem_solutions (composite_model_objective f g)
        simpa [h.optimal_set_eq] using hx
      exact (mem_unconstrained_problem_solutions_iff_forall_le.mp hx_opt) y
  · exact h.optimal_value_isGLB.1 ⟨x, rfl⟩

/-- Helper for Theorem 10.29: strong convexity of `f` lowers the first-order linearization defect
by the quadratic term `σ ‖x - y‖² / 2` at an interior base point `y`. -/
lemma proximal_gradient_strong_convexity_linearization_defect_lower_bound_real
    (hstrong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun z ↦ (f z).toReal))
    (hsmooth :
      is_l_smooth_on (fun z ↦ (f z).toReal) (interior (effective_domain f)) Lf)
    {x : E} (hx : x ∈ effective_domain f)
    (y : interior (effective_domain f)) :
    ((σ : ℝ) / 2) * ‖x - (y : E)‖ ^ (2 : ℕ) ≤
      (f x).toReal - (f (y : E)).toReal -
        inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - (y : E)) := by
  let ψ : E → ℝ := fun z ↦ (f z).toReal - ((σ : ℝ) / 2) * ‖z‖ ^ (2 : ℕ)
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap (y : E) x
  let φ : ℝ → ℝ := fun s ↦ ψ (line s)
  have hψ_convex : ConvexOn ℝ (effective_domain f) ψ := by
    -- Shift the strongly convex function by the quadratic term from
    -- `strongConvexOn_iff_convex`; this is the source proof's governing object.
    simpa [ψ] using (strongConvexOn_iff_convex.mp hstrong)
  have hφ_convex : ConvexOn ℝ (line ⁻¹' effective_domain f) φ := by
    -- Restrict the shifted convex function to the segment from `y` to `x`.
    simpa [φ, line] using hψ_convex.comp_affineMap line
  have hφ_zero : (0 : ℝ) ∈ line ⁻¹' effective_domain f := by
    simpa [line] using interior_subset y.2
  have hφ_one : (1 : ℝ) ∈ line ⁻¹' effective_domain f := by
    simpa [line] using hx
  have hy_diff :
      DifferentiableAt ℝ (fun z ↦ (f z).toReal) (y : E) := by
    exact (is_l_smooth_on_iff.mp hsmooth).1 _ y.2
  have hline : HasDerivAt line (x - (y : E)) 0 := by
    simpa [line] using
      (show HasDerivAt (AffineMap.lineMap (y : E) x) (x - (y : E)) (0 : ℝ) from
        AffineMap.hasDerivAt_lineMap)
  have hφf_deriv :
      HasDerivAt
        (fun s ↦ (f (line s)).toReal)
        (inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - (y : E)))
        0 := by
    -- Differentiate the smooth term along the segment at the base point `y`.
    have hcomp :
        HasDerivAt
          (fun s ↦ (f (line s)).toReal)
          (fderiv ℝ (fun z ↦ (f z).toReal) (y : E) (x - (y : E)))
          0 := by
      have hbase :
          HasFDerivAt (fun z ↦ (f z).toReal) (fderiv ℝ (fun z ↦ (f z).toReal) (y : E))
            (line 0) := by
        simpa [line] using hy_diff.hasFDerivAt
      simpa [line] using HasFDerivAt.comp_hasDerivAt 0 hbase hline
    have hgrad :
        fderiv ℝ (fun z ↦ (f z).toReal) (y : E) (x - (y : E)) =
          inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - (y : E)) := by
      simpa using
        (show
            fderiv ℝ (fun z ↦ (f z).toReal) (y : E) (x - (y : E)) =
              inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - (y : E)) from
          HasGradientAt.fderiv_apply hy_diff.hasGradientAt)
    simpa [hgrad] using hcomp
  have hφq_deriv :
      HasDerivAt
        (fun s ↦ ((σ : ℝ) / 2) * ‖line s‖ ^ (2 : ℕ))
        ((σ : ℝ) * inner ℝ (y : E) (x - (y : E)))
        0 := by
    -- Differentiate the quadratic correction along the same segment.
    have hnorm_sq : HasDerivAt (fun s ↦ ‖line s‖ ^ (2 : ℕ)) (2 * inner ℝ (y : E) (x - (y : E))) 0 := by
      simpa [line] using hline.norm_sq
    have hscaled := hnorm_sq.const_mul ((σ : ℝ) / 2)
    convert hscaled using 1
    ring
  have hφ_deriv :
      HasDerivAt
        φ
        (inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - (y : E)) -
          (σ : ℝ) * inner ℝ (y : E) (x - (y : E)))
        0 := by
    -- The shifted derivative is the smooth derivative minus the quadratic correction.
    simpa [φ, ψ] using hφf_deriv.sub hφq_deriv
  have hsecant :
      inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - (y : E)) -
          (σ : ℝ) * inner ℝ (y : E) (x - (y : E)) ≤
        slope φ 0 1 := by
    -- Convexity bounds the derivative at the left endpoint by the secant slope.
    exact hφ_convex.le_slope_of_hasDerivAt hφ_zero hφ_one zero_lt_one hφ_deriv
  have hsecant' :
      inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - (y : E)) -
          (σ : ℝ) * inner ℝ (y : E) (x - (y : E)) ≤
        ψ x - ψ (y : E) := by
    simpa [φ, line, slope] using hsecant
  have hsecant'' :
      inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - (y : E)) -
          (σ : ℝ) * inner ℝ (y : E) (x - (y : E)) ≤
        (f x).toReal - ((σ : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) -
          ((f (y : E)).toReal - ((σ : ℝ) / 2) * ‖(y : E)‖ ^ (2 : ℕ)) := by
    simpa [ψ] using hsecant'
  have hsecant_expanded :
      inner ℝ x (∇ (fun z ↦ (f z).toReal) (y : E)) -
          inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (y : E) -
          (σ : ℝ) * (inner ℝ (y : E) x - ‖(y : E)‖ ^ (2 : ℕ)) ≤
        (f x).toReal - ((σ : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) -
          ((f (y : E)).toReal - ((σ : ℝ) / 2) * ‖(y : E)‖ ^ (2 : ℕ)) := by
    simpa [inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm] using hsecant''
  have hinner :
      inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - (y : E)) =
        inner ℝ x (∇ (fun z ↦ (f z).toReal) (y : E)) -
          inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (y : E) := by
    rw [inner_sub_right, real_inner_comm]
  have hnorm :
      ‖x - (y : E)‖ ^ (2 : ℕ) =
        ‖x‖ ^ (2 : ℕ) - 2 * inner ℝ (y : E) x + ‖(y : E)‖ ^ (2 : ℕ) := by
    simpa [real_inner_comm] using (norm_sub_sq_real x (y : E))
  -- Rearrange the shifted support inequality back into the textbook defect lower bound.
  rw [hinner, hnorm]
  linarith

/-- Helper for Theorem 10.29: the Chapter 10 linearization defect `ℓ_f(x, y)` dominates
`σ ‖x - y‖² / 2` at interior base points `y`. -/
lemma proximal_gradient_strong_convexity_linearization_defect_lower_bound
    (hstrong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun z ↦ (f z).toReal))
    (hf_ne_bot : ∀ z, f z ≠ ⊥)
    (hsmooth :
      is_l_smooth_on (fun z ↦ (f z).toReal) (interior (effective_domain f)) Lf)
    {x : E} (hx : x ∈ effective_domain f)
    (y : interior (effective_domain f)) :
    ((((σ : ℝ) / 2) * ‖x - (y : E)‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
      ℓ[f, x, y] := by
  have hreal :
      ((σ : ℝ) / 2) * ‖x - (y : E)‖ ^ (2 : ℕ) ≤
        (f x).toReal - (f (y : E)).toReal -
          inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - (y : E)) :=
    proximal_gradient_strong_convexity_linearization_defect_lower_bound_real
      hstrong hsmooth hx y
  have hfx_val :
      f x = ((((f x).toReal : ℝ)) : EReal) := by
    exact (EReal.coe_toReal (mem_effective_domain.mp hx).ne (hf_ne_bot x)).symm
  have hfy_val :
      f (y : E) = ((((f (y : E)).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp (interior_subset y.2)).ne
        (hf_ne_bot (y : E))).symm
  -- Rewrite the Chapter 10 defect once, then coerce the real inequality into `EReal`.
  rw [prox_gradient_linearization_defect_eq, hfx_val, hfy_val]
  simpa [EReal.coe_sub] using (EReal.coe_le_coe_iff.mpr hreal)

/-- Helper for Theorem 10.29: combining the accepted upper model with the strong-convex
linearization bound yields the source one-step prox-gap inequality `(10.37)`. -/
lemma proximal_gradient_strongly_convex_step_gap
    (hstrong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun z ↦ (f z).toReal))
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SublinearRateStepsizeRule x L htraj α)
    (hxStar : xStar ∈ XStar)
    (k : ℕ) :
    F xStar - F (x (k + 1)) ≥
      (((((L k : ℝ) / 2) * ‖xStar - x (k + 1)‖ ^ (2 : ℕ) -
          (((L k : ℝ) - (σ : ℝ)) / 2) * ‖xStar - x k‖ ^ (2 : ℕ) : ℝ)) : EReal) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  let xk := proximal_gradient_trajectory_iterate htraj k
  have hrule_base :
      hproblem.ConstantOrBacktrackingB2StepsizeRule x L htraj :=
    hproblem.sublinearRateStepsizeRule_constantOrBacktrackingB2 hrule
  have haccepts :
      proximal_gradient_backtracking_B2_accepts f g (L k) xk := by
    -- Remark 10.19 upgrades the admissible stepsize owner to the accepted B2 upper model.
    exact
      proximal_gradient_constant_or_backtracking_B2_stepsize_accepts
        hproblem.f_ne_bot
        hproblem.f_effective_domain_convex
        hproblem.g_effective_domain_subset_interior_f_effective_domain
        hproblem.f_toReal_smooth_on_interior_effective_domain
        htraj
        hrule_base
        k
  have hFxStar :
      F xStar = (FOpt : EReal) :=
    objective_eq_optimal_value_of_mem_optimal_set hproblem hxStar
  have hFxStar_ne_top : F xStar ≠ ⊤ := by
    rw [hFxStar]
    simp
  have hfxStar_ne_top : f xStar ≠ ⊤ := by
    intro hfxStar_top
    have htop : F xStar = ⊤ := by
      rw [composite_model_objective_apply, hfxStar_top]
      exact EReal.top_add_of_ne_bot (hproblem.g_proper.ne_bot xStar)
    exact hFxStar_ne_top htop
  have hxStar_eff : xStar ∈ effective_domain f := by
    exact lt_of_le_of_ne le_top hfxStar_ne_top
  have hfund :
      F xStar - F (x (k + 1)) ≥
        (((((L k : ℝ) / 2) * ‖xStar - x (k + 1)‖ ^ (2 : ℕ) -
            ((L k : ℝ) / 2) * ‖xStar - x k‖ ^ (2 : ℕ) : ℝ)) : EReal) +
          ℓ[f, xStar, xk] := by
    -- Specialize Theorem 10.16 at the optimizer `xStar` and the current iterate `x^k`.
    simpa [xk, proximal_gradient_trajectory_succ_eq_operator htraj k] using
      (fundamental_prox_grad_inequality
        (f := f)
        (g := g)
        xStar
        xk
        (L k)
        haccepts)
  have hlin :
      ((((σ : ℝ) / 2) * ‖xStar - x k‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        ℓ[f, xStar, xk] := by
    -- Insert the strong-convexity lower bound for the linearization defect.
    simpa [xk] using
      (proximal_gradient_strong_convexity_linearization_defect_lower_bound
        (hstrong := hstrong)
        (hf_ne_bot := hproblem.f_ne_bot)
        (hsmooth := hproblem.f_toReal_smooth_on_interior_effective_domain)
        hxStar_eff
        xk)
  let q0 : ℝ :=
    ((L k : ℝ) / 2) * ‖xStar - x (k + 1)‖ ^ (2 : ℕ) -
      ((L k : ℝ) / 2) * ‖xStar - x k‖ ^ (2 : ℕ)
  have hinsert :
      (((((L k : ℝ) / 2) * ‖xStar - x (k + 1)‖ ^ (2 : ℕ) -
          (((L k : ℝ) - (σ : ℝ)) / 2) * ‖xStar - x k‖ ^ (2 : ℕ) : ℝ)) : EReal) ≤
        (((q0 : ℝ)) : EReal) + ℓ[f, xStar, xk] := by
    have hadd :
        ((((σ : ℝ) / 2) * ‖xStar - x k‖ ^ (2 : ℕ) : ℝ) : EReal) + (((q0 : ℝ)) : EReal) ≤
          ℓ[f, xStar, xk] + (((q0 : ℝ)) : EReal) := by
      simpa [add_comm] using add_le_add_right hlin ((((q0 : ℝ)) : EReal))
    have hadd' :
        (((q0 : ℝ)) : EReal) +
            ((((σ : ℝ) / 2) * ‖xStar - x k‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
          (((q0 : ℝ)) : EReal) + ℓ[f, xStar, xk] := by
      simpa [add_comm, add_left_comm, add_assoc] using hadd
    have hq :
        (((((L k : ℝ) / 2) * ‖xStar - x (k + 1)‖ ^ (2 : ℕ) -
            (((L k : ℝ) - (σ : ℝ)) / 2) * ‖xStar - x k‖ ^ (2 : ℕ) : ℝ)) : EReal) =
          (((q0 : ℝ)) : EReal) +
            ((((σ : ℝ) / 2) * ‖xStar - x k‖ ^ (2 : ℕ) : ℝ) : EReal) := by
      rw [← EReal.coe_add]
      congr 1
      dsimp [q0]
      ring_nf
    simpa [hq] using hadd'
  exact le_trans hinsert hfund

/-- Helper for Theorem 10.29: every positive-index proximal-gradient objective value is finite, so
it coincides with the cast of its `toReal` value. -/
lemma proximal_gradient_next_objective_eq_coe_toReal
    (hproblem : IsCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    (htraj : is_proximal_gradient_trajectory f g x L)
    (k : ℕ) :
    F (x (k + 1)) = ((((F (x (k + 1))).toReal : ℝ)) : EReal) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  have hxsucc :
      x (k + 1) ∈ effective_domain g :=
    proximal_gradient_positive_iterate_mem_effective_domain_g
      (f := f)
      (g := g)
      (hf_ne_bot := hproblem.f_ne_bot)
      (hf_effective_domain_convex := hproblem.f_effective_domain_convex)
      (hg_effective_domain_subset_interior_f_effective_domain :=
        hproblem.g_effective_domain_subset_interior_f_effective_domain)
      (hf_toReal_smooth_on_interior_effective_domain :=
        hproblem.f_toReal_smooth_on_interior_effective_domain)
      (htraj := htraj)
      k
  have hobj :
      F (x (k + 1)) =
        ((((f (x (k + 1))).toReal + (g (x (k + 1))).toReal : ℝ)) : EReal) :=
    proximal_gradient_objective_eq_real_of_mem_effective_domain_g
      (f := f)
      (g := g)
      (hf_ne_bot := hproblem.f_ne_bot)
      (hg_effective_domain_subset_interior_f_effective_domain :=
        hproblem.g_effective_domain_subset_interior_f_effective_domain)
      hxsucc
  -- Rewrite the finite composite objective once and then fold it back through `toReal`.
  rw [hobj, EReal.toReal_coe]

/-- Helper for Theorem 10.29: any finite proximal-gradient objective gap `F z - F_opt` is the cast
of the real difference of the corresponding `toReal` values. -/
lemma proximal_gradient_objective_gap_eq_coe_sub_optimal_value_of_mem_effective_domain_g
    (hproblem : IsCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    {z : E} (hz : z ∈ effective_domain g) :
    ((((F z).toReal - FOpt : ℝ)) : EReal) = F z - (FOpt : EReal) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  have hz_obj :
      F z = ((((f z).toReal + (g z).toReal : ℝ)) : EReal) :=
    proximal_gradient_objective_eq_real_of_mem_effective_domain_g
      (f := f)
      (g := g)
      (hf_ne_bot := hproblem.f_ne_bot)
      (hg_effective_domain_subset_interior_f_effective_domain :=
        hproblem.g_effective_domain_subset_interior_f_effective_domain)
      hz
  -- Once the iterate is finite, the gap is the canonical cast of the real subtraction.
  rw [hz_obj, EReal.toReal_coe]
  simp [EReal.coe_sub]

/-- Helper for Theorem 10.29: the objective gap at every positive iterate is the cast of its real
counterpart. -/
lemma proximal_gradient_positive_iterate_gap_coe
    (hproblem : IsCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    (htraj : is_proximal_gradient_trajectory f g x L)
    (k : ℕ) :
    ((((F (x (k + 1))).toReal - FOpt : ℝ)) : EReal) =
      F (x (k + 1)) - (FOpt : EReal) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  have hxsucc :
      x (k + 1) ∈ effective_domain g :=
    proximal_gradient_positive_iterate_mem_effective_domain_g
      (f := f)
      (g := g)
      (hf_ne_bot := hproblem.f_ne_bot)
      (hf_effective_domain_convex := hproblem.f_effective_domain_convex)
      (hg_effective_domain_subset_interior_f_effective_domain :=
        hproblem.g_effective_domain_subset_interior_f_effective_domain)
      (hf_toReal_smooth_on_interior_effective_domain :=
        hproblem.f_toReal_smooth_on_interior_effective_domain)
      (htraj := htraj)
      k
  -- Reuse the finite-gap bridge at the realized positive iterate.
  exact
    proximal_gradient_objective_gap_eq_coe_sub_optimal_value_of_mem_effective_domain_g
      hproblem
      hxsucc

/-- Helper for Theorem 10.29: every positive-index proximal-gradient objective gap is nonnegative
as a real number. -/
lemma proximal_gradient_positive_iterate_gap_nonneg
    (hproblem : IsCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    (htraj : is_proximal_gradient_trajectory f g x L)
    (k : ℕ) :
    0 ≤ (F (x (k + 1))).toReal - FOpt := by
  have hgapE :
      ((0 : ℝ) : EReal) ≤ ((((F (x (k + 1))).toReal - FOpt : ℝ)) : EReal) := by
    rw [proximal_gradient_positive_iterate_gap_coe hproblem htraj k]
    have hgap_nonneg : (0 : EReal) ≤ F (x (k + 1)) - (FOpt : EReal) := by
      exact
        (EReal.sub_nonneg (Or.inr (by simp)) (Or.inr (by simp))).2
          (hproblem.optimal_value_isGLB.1 ⟨x (k + 1), rfl⟩)
    simpa using hgap_nonneg
  exact EReal.coe_nonneg.mp hgapE

/-- Helper for Theorem 10.29: equation `(10.37)` becomes an ordinary real inequality once the
finite objective value at `x^(k+1)` is isolated. -/
lemma proximal_gradient_strongly_convex_step_gap_real
    (hstrong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun z ↦ (f z).toReal))
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SublinearRateStepsizeRule x L htraj α)
    (hxStar : xStar ∈ XStar)
    (k : ℕ) :
    (F (x (k + 1))).toReal - FOpt ≤
      (((L k : ℝ) - (σ : ℝ)) / 2) * ‖xStar - x k‖ ^ (2 : ℕ) -
        ((L k : ℝ) / 2) * ‖xStar - x (k + 1)‖ ^ (2 : ℕ) := by
  have hgapE :
      (((((L k : ℝ) / 2) * ‖xStar - x (k + 1)‖ ^ (2 : ℕ) -
          (((L k : ℝ) - (σ : ℝ)) / 2) * ‖xStar - x k‖ ^ (2 : ℕ) : ℝ)) : EReal) ≤
        F xStar - F (x (k + 1)) := by
    exact proximal_gradient_strongly_convex_step_gap hstrong htraj hrule hxStar k
  have hxStar_value :
      F xStar = (FOpt : EReal) :=
    objective_eq_optimal_value_of_mem_optimal_set hproblem hxStar
  have hxsucc_value :
      F (x (k + 1)) = ((((F (x (k + 1))).toReal : ℝ)) : EReal) :=
    proximal_gradient_next_objective_eq_coe_toReal hproblem htraj k
  have hgap_real :
      (((L k : ℝ) / 2) * ‖xStar - x (k + 1)‖ ^ (2 : ℕ) -
          (((L k : ℝ) - (σ : ℝ)) / 2) * ‖xStar - x k‖ ^ (2 : ℕ)) ≤
        FOpt - (F (x (k + 1))).toReal := by
    rw [hxStar_value, hxsucc_value] at hgapE
    exact EReal.coe_le_coe_iff.mp (by simpa [EReal.coe_sub] using hgapE)
  -- Move the real objective gap to the left to match the source inequality `(10.37)`.
  nlinarith

/-- Helper for Theorem 10.29: the real-form step-gap inequality rewritten in the exact norm order
used by clauses (a) and (c). -/
lemma proximal_gradient_strongly_convex_objective_gap_real_step
    (hstrong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun z ↦ (f z).toReal))
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SublinearRateStepsizeRule x L htraj α)
    (hxStar : xStar ∈ XStar)
    (k : ℕ) :
    (F (x (k + 1))).toReal - FOpt ≤
      (((L k : ℝ) - (σ : ℝ)) / 2) * ‖x k - xStar‖ ^ (2 : ℕ) -
        ((L k : ℝ) / 2) * ‖x (k + 1) - xStar‖ ^ (2 : ℕ) := by
  -- Normalize both norms with `norm_sub_rev` so the theorem bodies match the textbook display.
  simpa [norm_sub_rev] using
    proximal_gradient_strongly_convex_step_gap_real
      (hproblem := hproblem)
      hstrong
      htraj
      hrule
      hxStar
      k

/-- Helper for Theorem 10.29: the contraction factor written with the condition number
`κ(L_f, σ)` is exactly `1 - σ / (α L_f)`. -/
lemma proximal_gradient_contraction_factor_eq_one_sub_sigma_div_alpha_mul_Lf
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SublinearRateStepsizeRule x L htraj α) :
    1 - 1 / (α * κ) = 1 - (σ : ℝ) / (α * (Lf : ℝ)) := by
  have hα_pos : 0 < α :=
    hproblem.sublinearRateStepsizeRule_alpha_pos hrule
  have hLf_pos : 0 < (Lf : ℝ) :=
    hproblem.sublinearRateStepsizeRule_lf_pos hrule
  have hσ_pos : 0 < (σ : ℝ) := σ.2
  -- Normalize `κ(L_f, σ)` to the ratio `L_f / σ` and clear denominators using positivity.
  rw [condition_number_eq]
  field_simp [hα_pos.ne', hLf_pos.ne', hσ_pos.ne']

-- Proof sketch: apply the fundamental prox-grad inequality with `x = xStar`, `y = x^k`, and
-- `L = L_k`; use strong convexity of `f` to bound the linearization error from below by
-- `(σ / 2) ‖x^k - xStar‖²`, use that `xStar` is optimal to make the objective gap nonpositive,
-- and then use the constant/B2 stepsize rule to replace `L_k` by the uniform factor `α L_f`.
/-- Theorem 10.29 (1): clause (a). Under Assumption 10.1, if `f` is `σ`-strongly convex and the
proximal-gradient trajectory uses either the constant rule `L_k = L_f` or backtracking procedure
B2 with the corresponding value of `α`, then with `κ = L_f / σ`,
`‖x^(k+1) - x*‖² ≤ (1 - 1 / (α κ)) ‖x^k - x*‖²`. -/
theorem proximal_gradient_strongly_convex_step_distance_sq_le
    (hstrong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun y ↦ (f y).toReal))
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SublinearRateStepsizeRule x L htraj α)
    (hL_bound : ∀ k, (L k : ℝ) ≤ α * (Lf : ℝ))
    (hxStar : xStar ∈ XStar)
    (k : ℕ) :
    ‖x (k + 1) - xStar‖ ^ (2 : ℕ) ≤
      (1 - 1 / (α * κ)) * ‖x k - xStar‖ ^ (2 : ℕ) := by
  have hgap_real :
      (F (x (k + 1))).toReal - FOpt ≤
        (((L k : ℝ) - (σ : ℝ)) / 2) * ‖x k - xStar‖ ^ (2 : ℕ) -
          ((L k : ℝ) / 2) * ‖x (k + 1) - xStar‖ ^ (2 : ℕ) :=
    proximal_gradient_strongly_convex_objective_gap_real_step
      (hproblem := hproblem)
      hstrong
      htraj
      hrule
      hxStar
      k
  have hgap_nonneg :
      0 ≤ (F (x (k + 1))).toReal - FOpt :=
    proximal_gradient_positive_iterate_gap_nonneg hproblem htraj k
  have hcore :
      ((L k : ℝ) / 2) * ‖x (k + 1) - xStar‖ ^ (2 : ℕ) ≤
        (((L k : ℝ) - (σ : ℝ)) / 2) * ‖x k - xStar‖ ^ (2 : ℕ) := by
    -- Drop the nonnegative objective gap from the left side of the real-form source inequality.
    nlinarith
  have hLk_pos : 0 < (L k : ℝ) := (L k).2
  have hscaled :
      (L k : ℝ) * ‖x (k + 1) - xStar‖ ^ (2 : ℕ) ≤
        (((L k : ℝ) - (σ : ℝ)) * ‖x k - xStar‖ ^ (2 : ℕ)) := by
    nlinarith [hcore]
  have hstep_coeff :
      (1 - (σ : ℝ) / (L k : ℝ)) * ‖x k - xStar‖ ^ (2 : ℕ) =
        ((((L k : ℝ) - (σ : ℝ)) * ‖x k - xStar‖ ^ (2 : ℕ)) / (L k : ℝ)) := by
    field_simp [hLk_pos.ne']
  have hstep_real :
      ‖x (k + 1) - xStar‖ ^ (2 : ℕ) ≤
        (1 - (σ : ℝ) / (L k : ℝ)) * ‖x k - xStar‖ ^ (2 : ℕ) := by
    -- Clear the positive factor `L_k` with a one-sided division step.
    rw [hstep_coeff]
    exact (le_div_iff₀ hLk_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)
  have hα_pos : 0 < α :=
    hproblem.sublinearRateStepsizeRule_alpha_pos hrule
  have hLf_pos : 0 < (Lf : ℝ) :=
    hproblem.sublinearRateStepsizeRule_lf_pos hrule
  have hcoeff :
      1 - (σ : ℝ) / (L k : ℝ) ≤ 1 - (σ : ℝ) / (α * (Lf : ℝ)) := by
    have hαLf_pos : 0 < α * (Lf : ℝ) := mul_pos hα_pos hLf_pos
    have hrecip :
        (α * (Lf : ℝ))⁻¹ ≤ ((L k : ℝ))⁻¹ := by
      exact (inv_le_inv₀ hαLf_pos hLk_pos).2 (hL_bound k)
    have hfrac :
        (σ : ℝ) / (α * (Lf : ℝ)) ≤ (σ : ℝ) / (L k : ℝ) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hrecip σ.2.le
    -- Replace the step-dependent denominator by the uniform upper bound `α L_f`.
    nlinarith
  have hdist_nonneg : 0 ≤ ‖x k - xStar‖ ^ (2 : ℕ) := by
    positivity
  have hstep_uniform :
      ‖x (k + 1) - xStar‖ ^ (2 : ℕ) ≤
        (1 - (σ : ℝ) / (α * (Lf : ℝ))) * ‖x k - xStar‖ ^ (2 : ℕ) := by
    exact le_trans hstep_real (mul_le_mul_of_nonneg_right hcoeff hdist_nonneg)
  -- Rewrite the coefficient back to the public condition-number notation.
  rw [proximal_gradient_contraction_factor_eq_one_sub_sigma_div_alpha_mul_Lf
    (hproblem := hproblem) htraj hrule]
  exact hstep_uniform

-- Proof sketch: iterate clause (a) from `0` through `k - 1`; each step multiplies the squared
-- distance by the same factor `1 - 1 / (α * κ(Lf, σ))`, so induction yields the
-- geometric estimate.
/-- Theorem 10.29 (2): clause (b). Under the same hypotheses as clause (a), the iterates satisfy
the geometric distance estimate
`‖x^k - x*‖² ≤ (1 - 1 / (α κ))^k ‖x^0 - x*‖²`, where `κ = L_f / σ`. -/
theorem proximal_gradient_strongly_convex_distance_sq_le_geometric
    (hstrong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun y ↦ (f y).toReal))
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SublinearRateStepsizeRule x L htraj α)
    (hL_bound : ∀ k, (L k : ℝ) ≤ α * (Lf : ℝ))
    (hxStar : xStar ∈ XStar)
    (k : ℕ) :
    ‖x k - xStar‖ ^ (2 : ℕ) ≤
      (1 - 1 / (α * κ)) ^ k * ‖x 0 - xStar‖ ^ (2 : ℕ) := by
  by_cases hinit_zero : ‖x 0 - xStar‖ ^ (2 : ℕ) = 0
  · have hzero_all : ∀ n, ‖x n - xStar‖ ^ (2 : ℕ) = 0 := by
      intro n
      induction n with
      | zero =>
          exact hinit_zero
      | succ n ih =>
          have hstep :
              ‖x (n + 1) - xStar‖ ^ (2 : ℕ) ≤
                (1 - 1 / (α * κ)) * ‖x n - xStar‖ ^ (2 : ℕ) :=
            proximal_gradient_strongly_convex_step_distance_sq_le
              (hproblem := hproblem)
              hstrong
              htraj
              hrule
              hL_bound
              hxStar
              n
          rw [ih] at hstep
          have hdist_nonneg : 0 ≤ ‖x (n + 1) - xStar‖ ^ (2 : ℕ) := by
            positivity
          linarith
    -- Once the initial distance vanishes, every later iterate must stay at the optimizer.
    rw [hzero_all k, hinit_zero]
    simp
  · have hinit_nonneg : 0 ≤ ‖x 0 - xStar‖ ^ (2 : ℕ) := by
      positivity
    have hinit_pos : 0 < ‖x 0 - xStar‖ ^ (2 : ℕ) :=
      lt_of_le_of_ne hinit_nonneg (Ne.symm hinit_zero)
    have hq_nonneg : 0 ≤ 1 - 1 / (α * κ) :=
      by
        have hstep0 :
            ‖x (0 + 1) - xStar‖ ^ (2 : ℕ) ≤
              (1 - 1 / (α * κ)) * ‖x 0 - xStar‖ ^ (2 : ℕ) :=
          proximal_gradient_strongly_convex_step_distance_sq_le
            (hproblem := hproblem)
            hstrong
            htraj
            hrule
            hL_bound
            hxStar
            0
        have hdist_nonneg : 0 ≤ ‖x (0 + 1) - xStar‖ ^ (2 : ℕ) := by
          positivity
        -- A negative contraction factor would force the right-hand side below zero.
        by_contra hq_nonneg
        have hq_neg : 1 - 1 / (α * κ) < 0 := lt_of_not_ge hq_nonneg
        have hright_neg :
            (1 - 1 / (α * κ)) * ‖x 0 - xStar‖ ^ (2 : ℕ) < 0 := by
          exact mul_neg_of_neg_of_pos hq_neg hinit_pos
        linarith
    induction k with
    | zero =>
        simp
    | succ n ih =>
        have hstep :
            ‖x (n + 1) - xStar‖ ^ (2 : ℕ) ≤
              (1 - 1 / (α * κ)) * ‖x n - xStar‖ ^ (2 : ℕ) :=
          proximal_gradient_strongly_convex_step_distance_sq_le
            (hproblem := hproblem)
            hstrong
            htraj
            hrule
            hL_bound
            hxStar
            n
        have hmul :
            (1 - 1 / (α * κ)) * ‖x n - xStar‖ ^ (2 : ℕ) ≤
              (1 - 1 / (α * κ)) * ((1 - 1 / (α * κ)) ^ n * ‖x 0 - xStar‖ ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left ih hq_nonneg
        -- Iterate the one-step contraction by multiplying the induction hypothesis by the
        -- nonnegative common factor.
        exact le_trans hstep (by
          simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hmul)

-- Proof sketch: start from the one-step inequality underlying clause (a), rearrange it into an
-- objective-gap estimate, bound `L_k` above by `α L_f`, and then substitute the geometric
-- distance estimate from clause (b).
/-- Theorem 10.29 (3): clause (c). Under the same hypotheses as clause (a), the composite
objective gap satisfies
`F(x^(k+1)) - F_opt ≤ (α L_f / 2) (1 - 1 / (α κ))^(k+1) ‖x^0 - x*‖²`, where
`κ = L_f / σ`. -/
theorem proximal_gradient_strongly_convex_objective_gap_le
    (hstrong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun y ↦ (f y).toReal))
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SublinearRateStepsizeRule x L htraj α)
    (hL_bound : ∀ k, (L k : ℝ) ≤ α * (Lf : ℝ))
    (hxStar : xStar ∈ XStar)
    (k : ℕ) :
    F (x (k + 1)) - (FOpt : EReal) ≤
      ((((α * (Lf : ℝ)) / 2) *
          (1 - 1 / (α * κ)) ^ (k + 1) *
          ‖x 0 - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  have hgap_real :
      (F (x (k + 1))).toReal - FOpt ≤
        (((L k : ℝ) - (σ : ℝ)) / 2) * ‖x k - xStar‖ ^ (2 : ℕ) -
          ((L k : ℝ) / 2) * ‖x (k + 1) - xStar‖ ^ (2 : ℕ) :=
    proximal_gradient_strongly_convex_objective_gap_real_step
      (hproblem := hproblem)
      hstrong
      htraj
      hrule
      hxStar
      k
  have hdrop :
      (F (x (k + 1))).toReal - FOpt ≤
        (((L k : ℝ) - (σ : ℝ)) / 2) * ‖x k - xStar‖ ^ (2 : ℕ) := by
    have hcoeff_nonneg : 0 ≤ (L k : ℝ) / 2 := by
      exact div_nonneg (le_of_lt (L k).2) (by positivity)
    have hterm_nonneg : 0 ≤ ((L k : ℝ) / 2) * ‖x (k + 1) - xStar‖ ^ (2 : ℕ) := by
      exact mul_nonneg hcoeff_nonneg (by positivity)
    -- Drop the nonpositive distance term from the real-form source inequality.
    nlinarith
  have hα_pos : 0 < α :=
    hproblem.sublinearRateStepsizeRule_alpha_pos hrule
  have hLf_pos : 0 < (Lf : ℝ) :=
    hproblem.sublinearRateStepsizeRule_lf_pos hrule
  have hαLf_pos : 0 < α * (Lf : ℝ) := mul_pos hα_pos hLf_pos
  have hcoeff_le :
      (((L k : ℝ) - (σ : ℝ)) / 2) ≤ (((α * (Lf : ℝ)) - (σ : ℝ)) / 2) := by
    nlinarith [hL_bound k]
  have hdist_geom_public :
      ‖x k - xStar‖ ^ (2 : ℕ) ≤
        (1 - 1 / (α * κ)) ^ k * ‖x 0 - xStar‖ ^ (2 : ℕ) :=
      proximal_gradient_strongly_convex_distance_sq_le_geometric
        (hproblem := hproblem)
        hstrong
        htraj
        hrule
        hL_bound
        hxStar
        k
  have hbase_explicit :
      1 - (σ : ℝ) / (Lf : ℝ) * α⁻¹ = 1 - (σ : ℝ) / (α * (Lf : ℝ)) := by
    field_simp [hα_pos.ne', hLf_pos.ne']
  have hdist_geom :
      ‖x k - xStar‖ ^ (2 : ℕ) ≤
        (1 - (σ : ℝ) / (α * (Lf : ℝ))) ^ k * ‖x 0 - xStar‖ ^ (2 : ℕ) := by
    rw [proximal_gradient_contraction_factor_eq_one_sub_sigma_div_alpha_mul_Lf
      (hproblem := hproblem) htraj hrule] at hdist_geom_public
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hbase_explicit] using
      hdist_geom_public
  by_cases hinit_zero : ‖x 0 - xStar‖ ^ (2 : ℕ) = 0
  · have hzero_all : ∀ n, ‖x n - xStar‖ ^ (2 : ℕ) = 0 := by
      intro n
      induction n with
      | zero =>
          exact hinit_zero
      | succ n ih =>
          have hstep :
              ‖x (n + 1) - xStar‖ ^ (2 : ℕ) ≤
                (1 - 1 / (α * κ)) * ‖x n - xStar‖ ^ (2 : ℕ) :=
            proximal_gradient_strongly_convex_step_distance_sq_le
              (hproblem := hproblem)
              hstrong
              htraj
              hrule
              hL_bound
              hxStar
              n
          rw [ih] at hstep
          have hdist_nonneg : 0 ≤ ‖x (n + 1) - xStar‖ ^ (2 : ℕ) := by
            positivity
          linarith
    have hgap_nonneg :
        0 ≤ (F (x (k + 1))).toReal - FOpt :=
      proximal_gradient_positive_iterate_gap_nonneg hproblem htraj k
    have hvalue :
        (F (x (k + 1))).toReal - FOpt = 0 := by
      rw [hzero_all k] at hdrop
      linarith
    -- In the zero-distance branch, the positive-iterate gap collapses to zero as well.
    rw [← proximal_gradient_positive_iterate_gap_coe hproblem htraj k]
    rw [hvalue, hinit_zero]
    simp
  · have hinit_nonneg : 0 ≤ ‖x 0 - xStar‖ ^ (2 : ℕ) := by
      positivity
    have hinit_pos : 0 < ‖x 0 - xStar‖ ^ (2 : ℕ) :=
      lt_of_le_of_ne hinit_nonneg (Ne.symm hinit_zero)
    have hq_nonneg :
        0 ≤ 1 - (σ : ℝ) / (α * (Lf : ℝ)) := by
      have hstep0 :
          ‖x (0 + 1) - xStar‖ ^ (2 : ℕ) ≤
            (1 - (σ : ℝ) / (α * (Lf : ℝ))) * ‖x 0 - xStar‖ ^ (2 : ℕ) := by
        simpa [proximal_gradient_contraction_factor_eq_one_sub_sigma_div_alpha_mul_Lf
          (hproblem := hproblem) htraj hrule, hbase_explicit] using
          proximal_gradient_strongly_convex_step_distance_sq_le
            (hproblem := hproblem)
            hstrong
            htraj
            hrule
            hL_bound
            hxStar
            0
      have hdist_nonneg : 0 ≤ ‖x (0 + 1) - xStar‖ ^ (2 : ℕ) := by
        positivity
      -- A negative coefficient would force the right-hand side below zero.
      by_contra hq_nonneg
      have hq_neg : 1 - (σ : ℝ) / (α * (Lf : ℝ)) < 0 := lt_of_not_ge hq_nonneg
      have hright_neg :
          (1 - (σ : ℝ) / (α * (Lf : ℝ))) * ‖x 0 - xStar‖ ^ (2 : ℕ) < 0 := by
        exact mul_neg_of_neg_of_pos hq_neg hinit_pos
      linarith
    have hcoeff_eq :
        (((α * (Lf : ℝ)) - (σ : ℝ)) / 2) =
          ((α * (Lf : ℝ)) / 2) * (1 - (σ : ℝ) / (α * (Lf : ℝ))) := by
      field_simp [hαLf_pos.ne']
    have hcoeff_nonneg : 0 ≤ (((α * (Lf : ℝ)) - (σ : ℝ)) / 2) := by
      rw [hcoeff_eq]
      exact mul_nonneg (by positivity) hq_nonneg
    have hbound1 :
        (F (x (k + 1))).toReal - FOpt ≤
          (((α * (Lf : ℝ)) - (σ : ℝ)) / 2) * ‖x k - xStar‖ ^ (2 : ℕ) := by
      exact le_trans hdrop (mul_le_mul_of_nonneg_right hcoeff_le (by positivity))
    have hbound2 :
        (F (x (k + 1))).toReal - FOpt ≤
          (((α * (Lf : ℝ)) - (σ : ℝ)) / 2) *
            ((1 - (σ : ℝ) / (α * (Lf : ℝ))) ^ k * ‖x 0 - xStar‖ ^ (2 : ℕ)) := by
      exact le_trans hbound1 (mul_le_mul_of_nonneg_left hdist_geom hcoeff_nonneg)
    rw [← proximal_gradient_positive_iterate_gap_coe hproblem htraj k]
    exact EReal.coe_le_coe_iff.mpr <| by
      calc
        (F (x (k + 1))).toReal - FOpt ≤
            (((α * (Lf : ℝ)) - (σ : ℝ)) / 2) *
              ((1 - (σ : ℝ) / (α * (Lf : ℝ))) ^ k * ‖x 0 - xStar‖ ^ (2 : ℕ)) := hbound2
        _ = ((α * (Lf : ℝ)) / 2) *
              (1 - (σ : ℝ) / (α * (Lf : ℝ))) *
              ((1 - (σ : ℝ) / (α * (Lf : ℝ))) ^ k * ‖x 0 - xStar‖ ^ (2 : ℕ)) := by
              rw [hcoeff_eq]
        _ = ((α * (Lf : ℝ)) / 2) *
              (1 - (σ : ℝ) / (α * (Lf : ℝ))) ^ (k + 1) *
              ‖x 0 - xStar‖ ^ (2 : ℕ) := by
              simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]
        _ = ((α * (Lf : ℝ)) / 2) *
              (1 - 1 / (α * κ)) ^ (k + 1) *
              ‖x 0 - xStar‖ ^ (2 : ℕ) := by
              rw [proximal_gradient_contraction_factor_eq_one_sub_sigma_div_alpha_mul_Lf
                (hproblem := hproblem) htraj hrule]

end

end

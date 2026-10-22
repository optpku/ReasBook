/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Lemma_9_3
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Lemma_9_4
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Theorem_9_12
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_67
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_68
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_69
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_67
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_69
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_72.StepsizeRules

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open Filter
open scoped Topology Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {f g ω : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
variable [hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf]
variable {x : ℕ → E} {L : ℕ → PosReal} {α : ℝ} {xStar : E}

local notation "F" => composite_model_objective f g

/- Theorem 10.72 is `source-facing` in the non-Euclidean proximal-gradient analysis.

Domain sampling against the existing Chapter 9 and Chapter 10 API points to:
- `is_non_euclidean_proximal_gradient_trajectory` from Algorithm 10.68 as the owner of the
  iterate sequence `x^k`;
- `non_euclidean_proximal_gradient_constant_or_backtracking_B5_stepsize_rule` and
  `non_euclidean_proximal_gradient_sublinear_rate_stepsize_rule` from this item as the source
  stepsize owners for the constant/B5 regimes;
- `hproblem.upper_model_of_constantOrBacktrackingB5Rule` from Definition 10.69 as the accepted
  upper-model inequality at the realized step;
- `non_euclidean_proximal_gradient_step_iff_isMinOn_non_euclidean_proximal_gradient_model` from
  Algorithm 10.67 as the canonical bridge from the step predicate to the textbook model;
- Chapter 9's Bregman owner `B[ω]` and its lower quadratic bound from Lemma 9.4.

The source proof route is therefore:
1. establish clause (a) by comparing the accepted upper model at `x^(k+1)` with the same model
   evaluated at the comparator `x^k`;
2. retain clause (b) on the source-faithful Chapter 9 route through the non-Euclidean second prox
   theorem, the three-point identity, and a Bregman telescope. -/

-- Proof sketch: Definition 10.69 gives the accepted upper-model inequality at the realized next
-- iterate `x^(k+1)`. Lemma 9.4 upgrades the quadratic term `(L_k / 2) ‖x^(k+1) - x^k‖²` to the
-- Bregman term `L_k B_ω(x^(k+1), x^k)`, so `F(x^(k+1))` is bounded by the textbook local model at
-- `x^(k+1)`. The Algorithm 10.67 step predicate says that this local model is minimized at
-- `x^(k+1)`, and evaluating the same model at `x^k` collapses it to `F(x^k)`.
/-- Theorem 10.72 (1): clause (a). Under the displayed `g`-regularity, smoothness, domain, and
Bregman-potential hypotheses, if the non-Euclidean proximal-gradient trajectory uses either the
constant stepsize rule `L_k = L_f` or backtracking procedure B5, then the objective sequence
`F(x^k)` is nonincreasing. -/
theorem non_euclidean_proximal_gradient_objective_values_antitone
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (hrule : hproblem.ConstantOrBacktrackingB5StepsizeRule hω x L) :
    Antitone (fun k ↦ F (x k)) := by
  -- It is enough to prove the one-step descent inequality.
  refine antitone_nat_of_succ_le ?_
  intro n
  have hxng := (is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj n).1
  have hxn1g :=
    (is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj (n + 1)).1
  have hxns :=
    (is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj n).2
  have hdiff := is_non_euclidean_proximal_gradient_trajectory_differentiable_at htraj n
  have hupper := hproblem.upper_model_of_constantOrBacktrackingB5Rule hω htraj hrule n
  have hquad :
      (((((L n : ℝ) / 2) * ‖x (n + 1) - x n‖ ^ (2 : ℕ) : ℝ)) : EReal) ≤
        ((((L n : ℝ) * B[ω] (x (n + 1)) (x n) : ℝ)) : EReal) := by
    -- Lemma 9.4 upgrades the quadratic term to the Bregman penalty term.
    have hbreg :
        ((1 : ℝ) / 2) * ‖x (n + 1) - x n‖ ^ (2 : ℕ) ≤
          B[ω] (x (n + 1)) (x n) := by
      simpa using
        bregmanDistance_lower_quadratic_bound
          hω (x (n + 1)) (x n) hxn1g hxng hxns (hω_diff (x n) hxns)
    have hLn_nonneg : 0 ≤ (L n : ℝ) := le_of_lt (PosReal.coe_pos (L n))
    have hscaled :
        (L n : ℝ) * (((1 : ℝ) / 2) * ‖x (n + 1) - x n‖ ^ (2 : ℕ)) ≤
          (L n : ℝ) * B[ω] (x (n + 1)) (x n) :=
      mul_le_mul_of_nonneg_left hbreg hLn_nonneg
    have hscaled' :
        (((L n : ℝ) / 2) * ‖x (n + 1) - x n‖ ^ (2 : ℕ)) ≤
          (L n : ℝ) * B[ω] (x (n + 1)) (x n) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
    exact_mod_cast hscaled'
  have hmodel_step :
      x (n + 1) ∈ effective_domain g ∧
        IsMinOn (non_euclidean_textbook_model f g ω (x n) (L n)) Set.univ (x (n + 1)) := by
    exact
      (non_euclidean_proximal_gradient_step_iff_mem_effective_domain_and_isMinOn_textbook_model_univ
        hω hdiff (is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj n)).1
        (is_non_euclidean_proximal_gradient_trajectory_mem_step htraj n)
  have hmodel_min :
      IsMinOn (non_euclidean_textbook_model f g ω (x n) (L n)) Set.univ (x (n + 1)) := by
    -- The next iterate minimizes the textbook Bregman-regularized local model.
    exact hmodel_step.2
  have hmodel_succ :
      F (x (n + 1)) ≤
        non_euclidean_textbook_model f g ω (x n) (L n) (x (n + 1)) := by
    -- The accepted upper model controls the successor objective by the local model value.
    calc
      F (x (n + 1))
          = f (x (n + 1)) + g (x (n + 1)) := by
              rfl
      _ ≤
          (f (x n) +
              ((inner ℝ (∇ (fun y ↦ (f y).toReal) (x n)) (x (n + 1) - x n) +
                ((L n : ℝ) / 2) * ‖x (n + 1) - x n‖ ^ (2 : ℕ) : ℝ) : EReal)) +
            g (x (n + 1)) := by
              simpa [add_assoc, add_left_comm, add_comm] using
                add_le_add_right hupper (g (x (n + 1)))
      _ ≤
          (f (x n) +
              ((inner ℝ (∇ (fun y ↦ (f y).toReal) (x n)) (x (n + 1) - x n) : ℝ) : EReal)) +
            g (x (n + 1)) +
            ((((L n : ℝ) * B[ω] (x (n + 1)) (x n) : ℝ)) : EReal) := by
              simpa [add_assoc, add_left_comm, add_comm] using
                add_le_add_left hquad
                  ((f (x n) +
                    ((inner ℝ (∇ (fun y ↦ (f y).toReal) (x n)) (x (n + 1) - x n) : ℝ) :
                      EReal)) +
                    g (x (n + 1)))
      _ = non_euclidean_textbook_model f g ω (x n) (L n) (x (n + 1)) := by
            simp [non_euclidean_textbook_model, add_assoc, add_left_comm, add_comm]
  -- Evaluating the same model at the current iterate collapses exactly to `F(x^n)`.
  calc
    F (x (n + 1)) ≤ non_euclidean_textbook_model f g ω (x n) (L n) (x (n + 1)) := hmodel_succ
    _ ≤ non_euclidean_textbook_model f g ω (x n) (L n) (x n) :=
      (isMinOn_univ_iff.mp hmodel_min) (x n)
    _ = F (x n) := by
      simp [non_euclidean_textbook_model]

/-- Helper for Theorem 10.72: a finite linear term is convex as an extended-real-valued function. -/
lemma finite_linear_term_is_convex_function
    (ell : E →L[ℝ] ℝ) (c : ℝ) :
    is_convex_function (fun u ↦ (((c * ell u : ℝ)) : EReal)) := by
  have hlinear_convex : ConvexOn ℝ Set.univ (fun u ↦ c * ell u) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ hab
    refine le_of_eq ?_
    simp [map_add, map_smul, hab]
    ring
  exact Function.toEReal_isConvexFunction hlinear_convex

/-- Helper for Theorem 10.72: the source linearized objective
`u ↦ (⟨∇f(x^n), u⟩ + g(u)) / L_n` appearing in `(10.u400)`, before the Bregman term is added
back. -/
abbrev non_euclidean_scaled_linearized_objective
    (f g : E → EReal) (x : ℕ → E) (L : ℕ → PosReal) (n : ℕ) : E → EReal :=
  fun u ↦
    ((((L n : ℝ)⁻¹ * fderiv ℝ (fun y ↦ (f y).toReal) (x n) u : ℝ) : EReal) +
      (((L n : ℝ)⁻¹ : EReal) * g u))

/-- Helper for Theorem 10.72: adding the finite linearization term
`u ↦ ⟪∇f(x^n), u⟫ / L_n` does not change the effective domain of the scaled penalty, so the source
linearized objective has the same effective domain as `g`. -/
lemma non_euclidean_scaled_linearized_objective_effective_domain_eq
    (hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    (n : ℕ) :
    effective_domain (non_euclidean_scaled_linearized_objective f g x L n) =
      effective_domain g := by
  ext u
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  let scaledG : E → EReal := (((1 / L n : PosReal) : EReal) • g)
  have hscaled_dom :
      effective_domain scaledG = effective_domain g :=
    scaled_backtracking_penalty_effective_domain_eq g (L n)
  constructor
  · intro hu
    have hu_ne_top :
        non_euclidean_scaled_linearized_objective f g x L n u ≠ ⊤ :=
      (lt_top_iff_ne_top.mp (mem_effective_domain.mp hu))
    have hscaled_ne_top : scaledG u ≠ ⊤ := by
      -- A finite linear term cannot hide `g(u) = ⊤` inside the scaled objective.
      intro htop
      have hscaled_value :
          (((L n : ℝ)⁻¹ : EReal) * g u) = ⊤ := by
        simpa [scaledG, Pi.smul_apply, smul_eq_mul, PosReal.coe_inv] using htop
      apply hu_ne_top
      rw [non_euclidean_scaled_linearized_objective, hscaled_value]
      exact EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)
    have hu_scaled : u ∈ effective_domain scaledG :=
      mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hscaled_ne_top)
    rwa [hscaled_dom] at hu_scaled
  · intro hu
    have hu_scaled : u ∈ effective_domain scaledG := by
      rwa [hscaled_dom]
    -- Once the scaled penalty is finite, adding the finite linearization keeps the value finite.
    exact mem_effective_domain.mpr <| by
      simpa [non_euclidean_scaled_linearized_objective, scaledG, Pi.smul_apply, smul_eq_mul,
        PosReal.coe_inv] using
        EReal.add_lt_top (EReal.coe_ne_top _)
          (mem_effective_domain.mp hu_scaled).ne

/-- Helper for Theorem 10.72: the source linearized objective is proper and convex, so it can be
used as the `ψ_n` input of Theorem 9.12 on the exact textbook route. -/
lemma non_euclidean_scaled_linearized_objective_proper_convex
    (hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    (n : ℕ) :
    IsProperExtendedRealFunction (non_euclidean_scaled_linearized_objective f g x L n) ∧
      is_convex_function (non_euclidean_scaled_linearized_objective f g x L n) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  let scaledG : E → EReal := (((1 / L n : PosReal) : EReal) • g)
  rcases scaled_backtracking_penalty_proper_closed_convex g (L n) with
    ⟨hscaled_proper, _, hscaled_convex⟩
  constructor
  · refine ⟨?_, ?_⟩
    · intro u
      -- The finite linear term and the scaled penalty are both never `⊥`.
      have hlinear_ne_bot :
          ((((L n : ℝ)⁻¹ * fderiv ℝ (fun y ↦ (f y).toReal) (x n) u : ℝ)) : EReal) ≠ ⊥ :=
        EReal.coe_ne_bot _
      have hscaled_ne_bot : scaledG u ≠ ⊥ :=
        hscaled_proper.ne_bot u
      simpa [non_euclidean_scaled_linearized_objective, scaledG, Pi.smul_apply, smul_eq_mul,
        PosReal.coe_inv, EReal.add_ne_bot_iff] using And.intro hlinear_ne_bot hscaled_ne_bot
    · -- The effective domain agreement with `g` transfers nonemptiness directly.
      simpa [non_euclidean_scaled_linearized_objective_effective_domain_eq hproblem n] using
        hproblem.g_proper.effective_domain_nonempty
  · have hlinear_convex :
        is_convex_function
          (fun u ↦
            ((((L n : ℝ)⁻¹ * fderiv ℝ (fun y ↦ (f y).toReal) (x n) u : ℝ)) : EReal)) :=
      finite_linear_term_is_convex_function
        (fderiv ℝ (fun y ↦ (f y).toReal) (x n))
        ((L n : ℝ)⁻¹)
    have hsum_convex :
        is_convex_function
            ((fun u ↦
                ((((L n : ℝ)⁻¹ * fderiv ℝ (fun y ↦ (f y).toReal) (x n) u : ℝ)) : EReal)) +
              scaledG) :=
      is_convex_function_pointwise_add hlinear_convex hscaled_convex
        (fun _ ↦ EReal.coe_ne_bot _)
        hscaled_proper.ne_bot
    -- Normalize the scaled penalty back to the textbook `ψ_n` notation.
    simpa [non_euclidean_scaled_linearized_objective, scaledG, Pi.smul_apply, smul_eq_mul,
      PosReal.coe_inv] using hsum_convex

/-- Helper for Theorem 10.72: convexity of the smooth term gives the supporting-hyperplane
inequality for the finite-valued restriction `x ↦ (f x).toReal` at a differentiability point. -/
lemma non_euclidean_convex_support_toReal_at_basepoint
    (hf_convex : is_convex_function f)
    (hf_ne_bot : ∀ z, f z ≠ ⊥)
    {xBase y : E}
    (hxBase : xBase ∈ effective_domain f)
    (hxDiff : DifferentiableAt ℝ (fun z ↦ (f z).toReal) xBase)
    (hy : y ∈ effective_domain f) :
    (f y).toReal ≥ (f xBase).toReal +
      inner ℝ (∇ (fun z ↦ (f z).toReal) xBase) (y - xBase) := by
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap xBase y
  let φ : ℝ → ℝ := fun t ↦ (f (line t)).toReal
  have hconv :
      ConvexOn ℝ (effective_domain f) (fun z ↦ (f z).toReal) :=
    convexOn_toReal_of_is_convex_function hf_convex
      (fun z _ ↦ hf_ne_bot z)
  have hφ_convex :
      ConvexOn ℝ (line ⁻¹' effective_domain f) φ := by
    -- Restrict the convex real-valued model to the segment joining the base point to `y`.
    simpa [φ, line] using hconv.comp_affineMap line
  have hφ_zero :
      (0 : ℝ) ∈ line ⁻¹' effective_domain f := by
    simpa [line] using hxBase
  have hφ_one :
      (1 : ℝ) ∈ line ⁻¹' effective_domain f := by
    simpa [line] using hy
  have hφ_deriv :
      HasDerivAt φ
        (inner ℝ (∇ (fun z ↦ (f z).toReal) xBase) (y - xBase)) 0 := by
    -- Differentiate the segment restriction and identify the derivative with the gradient pairing.
    have hcomp :
        HasDerivAt φ
          (fderiv ℝ (fun z ↦ (f z).toReal) xBase (y - xBase)) 0 := by
      have hbase :
          HasFDerivAt (fun z ↦ (f z).toReal)
            (fderiv ℝ (fun z ↦ (f z).toReal) xBase) (line 0) := by
        simpa [line] using hxDiff.hasFDerivAt
      have hline : HasDerivAt line (y - xBase) 0 := by
        simpa [line] using
          (show HasDerivAt (AffineMap.lineMap xBase y) (y - xBase) (0 : ℝ) from
            AffineMap.hasDerivAt_lineMap)
      simpa [φ, line] using HasFDerivAt.comp_hasDerivAt 0 hbase hline
    have hgrad :
        fderiv ℝ (fun z ↦ (f z).toReal) xBase (y - xBase) =
          inner ℝ (∇ (fun z ↦ (f z).toReal) xBase) (y - xBase) := by
      simpa using
        (show
            fderiv ℝ (fun z ↦ (f z).toReal) xBase (y - xBase) =
              inner ℝ (∇ (fun z ↦ (f z).toReal) xBase) (y - xBase) from
          HasGradientAt.fderiv_apply hxDiff.hasGradientAt)
    simpa [hgrad] using hcomp
  have hsecant :
      inner ℝ (∇ (fun z ↦ (f z).toReal) xBase) (y - xBase) ≤ slope φ 0 1 := by
    -- Convexity bounds the derivative at the left endpoint by the segment secant slope.
    exact hφ_convex.le_slope_of_hasDerivAt hφ_zero hφ_one zero_lt_one hφ_deriv
  have hsecant' :
      inner ℝ (∇ (fun z ↦ (f z).toReal) xBase) (y - xBase) ≤
        (f y).toReal - (f xBase).toReal := by
    simpa [φ, line, slope] using hsecant
  linarith

/-- Helper for Theorem 10.72: the accepted upper-model inequality together with the minimizing
property of the realized step bounds the successor objective by the textbook model at any
comparator `u`. This is the source `(10.94)` and `(10.u399)` package. -/
lemma non_euclidean_successor_le_textbook_model
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (hrule : hproblem.ConstantOrBacktrackingB5StepsizeRule hω x L)
    (n : ℕ) (u : E) :
    F (x (n + 1)) ≤ non_euclidean_textbook_model f g ω (x n) (L n) u := by
  have hxng := (is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj n).1
  have hxn1g :=
    (is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj (n + 1)).1
  have hxns :=
    (is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj n).2
  have hdiff := is_non_euclidean_proximal_gradient_trajectory_differentiable_at htraj n
  have hupper := hproblem.upper_model_of_constantOrBacktrackingB5Rule hω htraj hrule n
  have hquad :
      (((((L n : ℝ) / 2) * ‖x (n + 1) - x n‖ ^ (2 : ℕ) : ℝ)) : EReal) ≤
        ((((L n : ℝ) * B[ω] (x (n + 1)) (x n) : ℝ)) : EReal) := by
    -- Lemma 9.4 upgrades the quadratic remainder in the accepted upper model to the Bregman term.
    have hbreg :
        ((1 : ℝ) / 2) * ‖x (n + 1) - x n‖ ^ (2 : ℕ) ≤
          B[ω] (x (n + 1)) (x n) := by
      simpa using
        bregmanDistance_lower_quadratic_bound
          hω (x (n + 1)) (x n) hxn1g hxng hxns (hω_diff (x n) hxns)
    have hLn_nonneg : 0 ≤ (L n : ℝ) := le_of_lt (PosReal.coe_pos (L n))
    have hscaled :
        (L n : ℝ) * (((1 : ℝ) / 2) * ‖x (n + 1) - x n‖ ^ (2 : ℕ)) ≤
          (L n : ℝ) * B[ω] (x (n + 1)) (x n) :=
      mul_le_mul_of_nonneg_left hbreg hLn_nonneg
    have hscaled' :
        (((L n : ℝ) / 2) * ‖x (n + 1) - x n‖ ^ (2 : ℕ)) ≤
          (L n : ℝ) * B[ω] (x (n + 1)) (x n) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
    exact_mod_cast hscaled'
  have hmodel_step :
      x (n + 1) ∈ effective_domain g ∧
        IsMinOn (non_euclidean_textbook_model f g ω (x n) (L n)) Set.univ (x (n + 1)) := by
    exact
      (non_euclidean_proximal_gradient_step_iff_mem_effective_domain_and_isMinOn_textbook_model_univ
        hω hdiff (is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj n)).1
        (is_non_euclidean_proximal_gradient_trajectory_mem_step htraj n)
  have hmodel_min :
      IsMinOn (non_euclidean_textbook_model f g ω (x n) (L n)) Set.univ (x (n + 1)) := by
    -- The realized next iterate minimizes the textbook local model from Algorithm 10.67.
    exact hmodel_step.2
  have hmodel_succ :
      F (x (n + 1)) ≤
        non_euclidean_textbook_model f g ω (x n) (L n) (x (n + 1)) := by
    -- The accepted upper model bounds the true successor objective by the textbook model value.
    calc
      F (x (n + 1))
          = f (x (n + 1)) + g (x (n + 1)) := by
              rfl
      _ ≤
          (f (x n) +
              ((inner ℝ (∇ (fun y ↦ (f y).toReal) (x n)) (x (n + 1) - x n) +
                ((L n : ℝ) / 2) * ‖x (n + 1) - x n‖ ^ (2 : ℕ) : ℝ) : EReal)) +
            g (x (n + 1)) := by
              simpa [add_assoc, add_left_comm, add_comm] using
                add_le_add_right hupper (g (x (n + 1)))
      _ ≤
          (f (x n) +
              ((inner ℝ (∇ (fun y ↦ (f y).toReal) (x n)) (x (n + 1) - x n) : ℝ) : EReal)) +
            g (x (n + 1)) +
            ((((L n : ℝ) * B[ω] (x (n + 1)) (x n) : ℝ)) : EReal) := by
              simpa [add_assoc, add_left_comm, add_comm] using
                add_le_add_left hquad
                  ((f (x n) +
                    ((inner ℝ (∇ (fun y ↦ (f y).toReal) (x n)) (x (n + 1) - x n) : ℝ) :
                      EReal)) +
                    g (x (n + 1)))
      _ = non_euclidean_textbook_model f g ω (x n) (L n) (x (n + 1)) := by
            simp [non_euclidean_textbook_model, add_assoc, add_left_comm, add_comm]
  -- The same minimizing property lets us compare the successor with any source comparator `u`.
  calc
    F (x (n + 1)) ≤ non_euclidean_textbook_model f g ω (x n) (L n) (x (n + 1)) := hmodel_succ
    _ ≤ non_euclidean_textbook_model f g ω (x n) (L n) u :=
      (isMinOn_univ_iff.mp hmodel_min) u

/-- Helper for Theorem 10.72: convexity of `f` replaces the local linear model at a comparator by
the true objective value, leaving only the Bregman penalty. This is the source passage from
`m(u, x^n)` to `f(u)`. -/
lemma non_euclidean_textbook_model_le_objective_add_bregman
    (hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    {n : ℕ} {u : E} (hu : u ∈ effective_domain g) :
    non_euclidean_textbook_model f g ω (x n) (L n) u ≤
      F u + ((((L n : ℝ) * B[ω] u (x n) : ℝ) : EReal)) := by
  have hxng := (is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj n).1
  have hdiff := is_non_euclidean_proximal_gradient_trajectory_differentiable_at htraj n
  have hxBase_finite : x n ∈ finite_domain f := interior_subset hdiff.1
  have hxBase_eff : x n ∈ effective_domain f := by
    exact hxBase_finite.1
  have hxBase_val :
      f (x n) = (((f (x n)).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hxBase_eff).ne
        (show f (x n) ≠ ⊥ from hxBase_finite.2)).symm
  have hu_eff : u ∈ effective_domain f := by
    exact interior_subset
      (hproblem.g_effective_domain_subset_interior_f_effective_domain hu)
  have hu_val :
      f u = (((f u).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hu_eff).ne
        (hproblem.f_ne_bot u)).symm
  have hsupport :
      (f (x n)).toReal +
          inner ℝ (∇ (fun z ↦ (f z).toReal) (x n)) (u - x n) ≤
        (f u).toReal := by
    exact non_euclidean_convex_support_toReal_at_basepoint
      hproblem.f_convex
      hproblem.f_ne_bot
      hxBase_eff hdiff.2 hu_eff
  have hlinearized_le :
      f (x n) + ((inner ℝ (∇ (fun z ↦ (f z).toReal) (x n)) (u - x n) : ℝ) : EReal) ≤
        f u := by
    -- Rewrite the finite smooth values as real coercions and transport the real support bound.
    rw [hxBase_val, hu_val]
    simpa [EReal.coe_add] using (EReal.coe_le_coe hsupport)
  calc
    non_euclidean_textbook_model f g ω (x n) (L n) u
        =
          (f (x n) +
              ((inner ℝ (∇ (fun z ↦ (f z).toReal) (x n)) (u - x n) : ℝ) : EReal)) +
            (g u + ((((L n : ℝ) * B[ω] u (x n) : ℝ) : EReal))) := by
              simp [non_euclidean_textbook_model, add_assoc]
    _ ≤
          f u + (g u + ((((L n : ℝ) * B[ω] u (x n) : ℝ) : EReal))) := by
              exact add_le_add_left hlinearized_le _
    _ = F u + ((((L n : ℝ) * B[ω] u (x n) : ℝ) : EReal)) := by
          simp [composite_model_objective, add_assoc]

/-- Helper for Theorem 10.72: the optimal value is a lower bound for every objective value along
the non-Euclidean proximal-gradient trajectory. -/
lemma non_euclidean_objective_gap_nonneg
    (hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    (n : ℕ) :
    (FOpt : EReal) ≤ F (x n) := by
  -- The optimal value is the greatest lower bound of the objective range.
  exact hproblem.optimal_value_isGLB.1 ⟨x n, rfl⟩

/-- Helper for Theorem 10.72: every optimizer has finite nonsmooth value, so it belongs to
`effective_domain g`. -/
lemma non_euclidean_optimizer_mem_effective_domain_g
    (hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    (hxStar : xStar ∈ XStar) :
    xStar ∈ effective_domain g := by
  have hopt :
      F xStar = (FOpt : EReal) :=
    IsConvexCompositeSmoothMinimizationProblem.objective_eq_optimalValue_of_mem_optimalSet
      hproblem hxStar
  have hf_ne_bot : ∀ z, f z ≠ ⊥ :=
    hproblem.f_ne_bot
  have hg_ne_top : g xStar ≠ ⊤ := by
    intro hg_top
    have htop : F xStar = ⊤ := by
      calc
        F xStar = f xStar + g xStar := by rfl
        _ = f xStar + ⊤ := by rw [hg_top]
        _ = ⊤ := EReal.add_top_of_ne_bot (hf_ne_bot xStar)
    rw [htop] at hopt
    exact EReal.coe_ne_top FOpt hopt.symm
  exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hg_ne_top)

/-- Helper for Theorem 10.72: the realized next iterate minimizes exactly the Chapter 9 objective
`ψ_n(·) + B_ω(·, x^n)` used in the source proof of clause (b). -/
lemma non_euclidean_successor_minimizes_scaled_bregman_objective
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (n : ℕ) :
    IsMinOn
      (secondProxObjective (non_euclidean_scaled_linearized_objective f g x L n) ω (x n))
      Set.univ (x (n + 1)) := by
  have hdiff := is_non_euclidean_proximal_gradient_trajectory_differentiable_at htraj n
  have hstep := is_non_euclidean_proximal_gradient_trajectory_mem_step htraj n
  have hscaled_step :
      x (n + 1) ∈ effective_domain g ∧
        IsMinOn (scaled_bregman_objective f g ω (x n) (L n)) Set.univ (x (n + 1)) := by
    exact
      (non_euclidean_proximal_gradient_step_iff_mem_effective_domain_and_isMinOn_scaled_objective_univ
        hω hdiff (is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj n)).1 hstep
  have hscaled_min :
      IsMinOn (scaled_bregman_objective f g ω (x n) (L n)) Set.univ (x (n + 1)) := by
    -- The trajectory step is the unconstrained argmin of the Chapter 9 Bregman-form objective.
    exact hscaled_step.2
  simpa [scaled_bregman_objective, SecondProxObjective.apply,
    non_euclidean_scaled_linearized_objective] using hscaled_min

/-- Helper for Theorem 10.72: the source three-point identity for the Chapter 10 iterates can be
rewritten directly in add form, so the Chapter 9 optimality inequality can be normalized without
passing through an `EReal` subtraction chain. -/
lemma non_euclidean_three_point_add_form
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (n : ℕ) (u : E) :
    inner ℝ
        ((∇ (fun z ↦ (ω z).toReal) (x n)) - (∇ (fun z ↦ (ω z).toReal) (x (n + 1))))
        (u - x (n + 1)) +
      B[ω] u (x n) =
    B[ω] u (x (n + 1)) + B[ω] (x (n + 1)) (x n) := by
  -- Expanding the three Bregman distances shows that the `ω`-values cancel and the gradient
  -- terms collect to the displayed inner-product expression.
  rw [bregmanDistance_def, bregmanDistance_def, bregmanDistance_def]
  have hsplit : u - x n = (u - x (n + 1)) + (x (n + 1) - x n) := by
    abel
  rw [hsplit, inner_add_right, inner_sub_left]
  ring

/-- Helper for Theorem 10.72: comparing a second-prox minimizer with points on the segment from
the minimizer to a feasible comparator gives the normalized secant estimate needed for the
first-order inequality.  This argument uses only convexity of the penalty, not an exact
subdifferential sum rule. -/
private lemma non_euclidean_second_prox_segment_secant
    {psi omega : E → EReal} (hpsi_proper : IsProperExtendedRealFunction psi)
    (hpsi_convex : is_convex_function psi)
    {a b u : E} (ha_eff : a ∈ effective_domain psi)
    (ha : IsMinOn (fun z ↦ psi z + B[omega] z b) Set.univ a)
    (hu : u ∈ effective_domain psi) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (psi a).toReal - (psi u).toReal ≤
      (B[omega] (AffineMap.lineMap a u t) b - B[omega] a b) / t := by
  let z : E := AffineMap.lineMap a u t
  have hline_rewrite : z = t • u + (1 - t) • a := by
    calc
      z = t • (u - a) + a := by
        simp [z, AffineMap.lineMap_apply_module']
      _ = t • u + (1 - t) • a := by
        rw [smul_sub, sub_eq_add_neg]
        have hcoeff : -(t • a) + a = (1 - t) • a := by
          calc
            -(t • a) + a = (-t) • a + (1 : ℝ) • a := by simp
            _ = ((-t) + 1) • a := by rw [← add_smul]
            _ = (1 - t) • a := by ring_nf
        simpa [add_assoc] using congrArg (fun x ↦ t • u + x) hcoeff
  have hz_eff_combo :
      t • u + (1 - t) • a ∈ effective_domain psi :=
    combo_mem_effective_domain_of_is_convex_function hpsi_convex hu ha_eff ⟨ht0.le, ht1⟩
  have hz_eff : z ∈ effective_domain psi := by
    rw [hline_rewrite]
    exact hz_eff_combo
  have hmin :
      psi a + B[omega] a b ≤ psi z + B[omega] z b :=
    (isMinOn_iff.mp ha) z (by simp)
  have hpsia_top : psi a ≠ ⊤ := (mem_effective_domain.mp ha_eff).ne
  have hpsiz_top : psi z ≠ ⊤ := (mem_effective_domain.mp hz_eff).ne
  have hpsia_bot : psi a ≠ ⊥ := hpsi_proper.ne_bot a
  have hpsiz_bot : psi z ≠ ⊥ := hpsi_proper.ne_bot z
  have hpsia_coe : (((psi a).toReal : ℝ) : EReal) = psi a :=
    EReal.coe_toReal hpsia_top hpsia_bot
  have hpsiz_coe : (((psi z).toReal : ℝ) : EReal) = psi z :=
    EReal.coe_toReal hpsiz_top hpsiz_bot
  have hseg_real :
      (psi z).toReal ≤ t * (psi u).toReal + (1 - t) * (psi a).toReal := by
    let hpsi_toReal : ConvexOn ℝ (effective_domain psi) (fun x ↦ (psi x).toReal) :=
      convexOn_toReal_of_is_convex_function_of_proper psi hpsi_convex
    have hseg_toReal :
        (psi (t • u + (1 - t) • a)).toReal ≤
          t * (psi u).toReal + (1 - t) * (psi a).toReal :=
      hpsi_toReal.2 hu ha_eff ht0.le (sub_nonneg.mpr ht1) (by linarith)
    simpa [hline_rewrite] using hseg_toReal
  have hmin_real :
      (psi a).toReal + B[omega] a b ≤ (psi z).toReal + B[omega] z b := by
    have hmin_ereal :
        ((((psi a).toReal + B[omega] a b : ℝ)) : EReal) ≤
          ((((psi z).toReal + B[omega] z b : ℝ)) : EReal) := by
      simpa [EReal.coe_add, hpsia_coe, hpsiz_coe] using hmin
    exact EReal.coe_le_coe_iff.mp hmin_ereal
  have hgap_support :
      (psi a).toReal - (psi z).toReal ≤ B[omega] z b - B[omega] a b := by
    linarith
  have hgap_convex :
      t * ((psi a).toReal - (psi u).toReal) ≤ (psi a).toReal - (psi z).toReal := by
    linarith
  have hgap :
      t * ((psi a).toReal - (psi u).toReal) ≤ B[omega] z b - B[omega] a b :=
    le_trans hgap_convex hgap_support
  have hgap' :
      ((psi a).toReal - (psi u).toReal) * t ≤ B[omega] z b - B[omega] a b := by
    simpa [mul_comm] using hgap
  exact (le_div_iff₀ ht0).2 hgap'

/-- Helper for Theorem 10.72: the Bregman term along the same segment has the expected derivative
at the minimizing endpoint whenever the potential is ambiently differentiable there. -/
private lemma non_euclidean_hasDerivAt_bregmanAlongSegmentAtZero
    {omega : E → EReal} {a b u : E}
    (ha_diff : DifferentiableAt ℝ (fun z ↦ (omega z).toReal) a) :
    HasDerivAt
      (fun t : ℝ ↦ B[omega] (AffineMap.lineMap a u t) b)
      (inner ℝ
        ((∇ (fun z ↦ (omega z).toReal) a) - (∇ (fun z ↦ (omega z).toReal) b))
        (u - a))
      0 := by
  have homega_path :
      HasDerivAt
        (fun t : ℝ ↦ (omega (AffineMap.lineMap a u t)).toReal)
        (inner ℝ (∇ (fun z ↦ (omega z).toReal) a) (u - a))
        0 := by
    simpa using
      lineMapDerivAtZero_eq_innerGradient
        (fun z ↦ (omega z).toReal) (x := u) (y := a) ha_diff
  have hlinear_rewrite :
      (fun t : ℝ ↦
        inner ℝ (∇ (fun z ↦ (omega z).toReal) b) (AffineMap.lineMap a u t - b)) =
        fun t : ℝ ↦
          t * inner ℝ (∇ (fun z ↦ (omega z).toReal) b) (u - a) +
            inner ℝ (∇ (fun z ↦ (omega z).toReal) b) (a - b) := by
    funext t
    calc
      inner ℝ (∇ (fun z ↦ (omega z).toReal) b) (AffineMap.lineMap a u t - b)
          = inner ℝ (∇ (fun z ↦ (omega z).toReal) b) (t • (u - a) + (a - b)) := by
              rw [AffineMap.lineMap_apply_module']
              abel
      _ = t * inner ℝ (∇ (fun z ↦ (omega z).toReal) b) (u - a) +
            inner ℝ (∇ (fun z ↦ (omega z).toReal) b) (a - b) := by
              rw [inner_add_right]
              simpa using inner_smul_right (∇ (fun z ↦ (omega z).toReal) b) (u - a) t
  have hlinear :
      HasDerivAt
        (fun t : ℝ ↦
          inner ℝ (∇ (fun z ↦ (omega z).toReal) b) (AffineMap.lineMap a u t - b))
        (inner ℝ (∇ (fun z ↦ (omega z).toReal) b) (u - a))
        0 := by
    rw [hlinear_rewrite]
    simpa using
      ((hasDerivAt_id (0 : ℝ)).mul_const
        (inner ℝ (∇ (fun z ↦ (omega z).toReal) b) (u - a))).add_const
          (inner ℝ (∇ (fun z ↦ (omega z).toReal) b) (a - b))
  have hpath_minus_const :
      HasDerivAt
        (fun t : ℝ ↦ (omega (AffineMap.lineMap a u t)).toReal - (omega b).toReal)
        (inner ℝ (∇ (fun z ↦ (omega z).toReal) a) (u - a))
        0 := by
    simpa using homega_path.sub_const ((omega b).toReal)
  simpa [bregmanDistance_def, inner_sub_left] using hpath_minus_const.sub hlinear

/-- Specialized second-prox optimality bridge for Theorem 10.72.  Because the trajectory already
records that the minimizing successor lies in `dom(∂omega)`, a direct segment argument proves the
source inequality without the relative-interior qualification needed by the generic exact-sum-rule
version of Theorem 9.12. -/
private lemma non_euclidean_second_prox_optimality_ineq_of_mem_domains
    {psi omega : E → EReal} (hpsi_proper : IsProperExtendedRealFunction psi)
    (hpsi_convex : is_convex_function psi)
    {a b : E} (ha_eff : a ∈ effective_domain psi)
    (ha_sub : a ∈ subdifferential_domain omega)
    (homega_diff : ∀ z ∈ subdifferential_domain omega,
      DifferentiableAt ℝ (fun w ↦ (omega w).toReal) z)
    (ha : IsMinOn (fun z ↦ psi z + B[omega] z b) Set.univ a) :
    ∀ u ∈ effective_domain psi,
      (inner ℝ
          ((∇ (fun z ↦ (omega z).toReal) b) - (∇ (fun z ↦ (omega z).toReal) a))
          (u - a) : EReal) ≤
        psi u - psi a := by
  intro u hu
  let phi : ℝ → ℝ := fun t ↦ B[omega] (AffineMap.lineMap a u t) b
  let ell : ℝ :=
    inner ℝ
      ((∇ (fun z ↦ (omega z).toReal) a) - (∇ (fun z ↦ (omega z).toReal) b))
      (u - a)
  have hphi_deriv : HasDerivAt phi ell 0 := by
    simpa [phi, ell] using
      non_euclidean_hasDerivAt_bregmanAlongSegmentAtZero
        (omega := omega) (a := a) (b := b) (u := u) (homega_diff a ha_sub)
  have hquot_tendsto :
      Tendsto (fun t : ℝ ↦ t⁻¹ * (phi t - phi 0)) (𝓝[>] (0 : ℝ)) (𝓝 ell) := by
    simpa using hphi_deriv.tendsto_slope_zero_right
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := by
    simpa [Set.mem_Ioi] using
      (eventually_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t ∈ Set.Ioi (0 : ℝ))
  have hlt1 : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < 1 := by
    simpa [Set.mem_Iio] using
      (show Set.Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) from
        nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
  have hevent :
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        -(t⁻¹ * (phi t - phi 0)) ≤ (psi u).toReal - (psi a).toReal := by
    filter_upwards [hpos, hlt1] with t ht0 ht1
    have hsecant :
        (psi a).toReal - (psi u).toReal ≤ t⁻¹ * (phi t - phi 0) := by
      simpa [phi, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, ht0.ne'] using
        non_euclidean_second_prox_segment_secant
          (psi := psi) (omega := omega) hpsi_proper hpsi_convex ha_eff ha hu ht0 ht1.le
    simpa [sub_eq_add_neg] using (neg_le_neg hsecant)
  have hlimit :
      -ell ≤ (psi u).toReal - (psi a).toReal :=
    le_of_tendsto_of_tendsto hquot_tendsto.neg tendsto_const_nhds hevent
  have hpsiu_top : psi u ≠ ⊤ := (mem_effective_domain.mp hu).ne
  have hpsia_top : psi a ≠ ⊤ := (mem_effective_domain.mp ha_eff).ne
  have hpsiu_bot : psi u ≠ ⊥ := hpsi_proper.ne_bot u
  have hpsia_bot : psi a ≠ ⊥ := hpsi_proper.ne_bot a
  have hpsiu_coe : (((psi u).toReal : ℝ) : EReal) = psi u :=
    EReal.coe_toReal hpsiu_top hpsiu_bot
  have hpsia_coe : (((psi a).toReal : ℝ) : EReal) = psi a :=
    EReal.coe_toReal hpsia_top hpsia_bot
  have hflip :
      -ell =
        inner ℝ
          ((∇ (fun z ↦ (omega z).toReal) b) - (∇ (fun z ↦ (omega z).toReal) a))
          (u - a) := by
    dsimp [ell]
    rw [inner_sub_left, inner_sub_left]
    ring
  have hpsi_sub_coe :
      ((((psi u).toReal - (psi a).toReal : ℝ)) : EReal) = psi u - psi a := by
    calc
      ((((psi u).toReal - (psi a).toReal : ℝ)) : EReal)
          = (((psi u).toReal : ℝ) : EReal) - (((psi a).toReal : ℝ) : EReal) := by
              rw [EReal.coe_sub]
      _ = psi u - psi a := by rw [hpsiu_coe, hpsia_coe]
  calc
    (inner ℝ
        ((∇ (fun z ↦ (omega z).toReal) b) - (∇ (fun z ↦ (omega z).toReal) a))
        (u - a) : EReal)
        = (((-ell : ℝ)) : EReal) := by rw [hflip]
    _ ≤ ((((psi u).toReal - (psi a).toReal : ℝ)) : EReal) := EReal.coe_le_coe hlimit
    _ = psi u - psi a := hpsi_sub_coe

/-- Helper for Theorem 10.72: apply the source second-prox segment argument to the linearized
objective `(m(·, x^n) + g) / L_n`.  The trajectory already provides successor membership in
`dom(∂ω)`, so no generic exact-sum-rule qualification is needed, and the result has the plus form
of equation `(10.96)` in `scaled_bregman_objective` language. -/
lemma psi_n_second_prox_three_point_bridge
    (hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (n : ℕ) {u : E} (hu : u ∈ effective_domain g) :
    non_euclidean_scaled_linearized_objective f g x L n (x (n + 1)) +
      (((B[ω] u (x (n + 1)) + B[ω] (x (n + 1)) (x n) : ℝ)) : EReal) ≤
    non_euclidean_scaled_linearized_objective f g x L n u +
      (((B[ω] u (x n) : ℝ)) : EReal) := by
  let ψ : E → EReal := non_euclidean_scaled_linearized_objective f g x L n
  rcases non_euclidean_scaled_linearized_objective_proper_convex
      hproblem n with
    ⟨hψ_proper, hψ_convex⟩
  have huψ : u ∈ effective_domain ψ := by
    simpa [ψ, non_euclidean_scaled_linearized_objective_effective_domain_eq hproblem n] using hu
  have hmin :
      IsMinOn (secondProxObjective ψ ω (x n)) Set.univ (x (n + 1)) := by
    simpa [ψ] using
      non_euclidean_successor_minimizes_scaled_bregman_objective hω htraj n
  have hsucc_eff :
      x (n + 1) ∈ effective_domain ψ := by
    -- The finite Bregman term does not change the effective domain of the proper penalty.
    exact SecondProxObjective.minimizer_mem_effective_domain hψ_proper hmin
  have hmin_apply :
      IsMinOn (fun z ↦ ψ z + B[ω] z (x n)) Set.univ (x (n + 1)) := by
    simpa [SecondProxObjective.apply] using hmin
  have hopt :
      (inner ℝ
          ((∇ (fun z ↦ (ω z).toReal) (x n)) - (∇ (fun z ↦ (ω z).toReal) (x (n + 1))))
          (u - x (n + 1)) : ℝ) ≤
        ψ u - ψ (x (n + 1)) := by
    -- The trajectory already supplies successor membership in `dom(∂ω)`, so the direct segment
    -- bridge avoids the generic exact-sum-rule qualification from Theorem 9.12.
    simpa [ψ] using
      non_euclidean_second_prox_optimality_ineq_of_mem_domains
        hψ_proper hψ_convex hsucc_eff
        (is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj (n + 1)).2
        hω_diff hmin_apply u huψ
  have hopt_add :
      (((inner ℝ
          ((∇ (fun z ↦ (ω z).toReal) (x n)) - (∇ (fun z ↦ (ω z).toReal) (x (n + 1))))
          (u - x (n + 1)) : ℝ)) : EReal) +
        ψ (x (n + 1)) ≤
      ψ u := by
    -- Rewrite the Chapter 9 subtraction form once into add form before touching Bregman terms.
    exact
      (EReal.le_sub_iff_add_le
        (.inl (hψ_proper.ne_bot (x (n + 1))))
        (.inl (mem_effective_domain.mp hsucc_eff).ne)).1 hopt
  have hthree :
      ((((inner ℝ
          ((∇ (fun z ↦ (ω z).toReal) (x n)) - (∇ (fun z ↦ (ω z).toReal) (x (n + 1))))
          (u - x (n + 1)) +
          B[ω] u (x n) : ℝ)) : EReal)) =
        (((B[ω] u (x (n + 1)) + B[ω] (x (n + 1)) (x n) : ℝ)) : EReal) := by
    -- The real three-point identity is now packaged in the exact add form needed downstream.
    simpa [EReal.coe_add] using
      congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal))
        (non_euclidean_three_point_add_form htraj n u)
  have hshift :
      (((inner ℝ
          ((∇ (fun z ↦ (ω z).toReal) (x n)) - (∇ (fun z ↦ (ω z).toReal) (x (n + 1))))
          (u - x (n + 1)) : ℝ)) : EReal) +
        ψ (x (n + 1)) +
        (((B[ω] u (x n) : ℝ)) : EReal) ≤
      ψ u + (((B[ω] u (x n) : ℝ)) : EReal) := by
    -- Add the same Bregman term to both sides so the left side matches the add-form identity.
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_right hopt_add ((((B[ω] u (x n) : ℝ)) : EReal))
  -- Normalize the left side with the add-form three-point identity to obtain the source plus form.
  calc
    ψ (x (n + 1)) +
        (((B[ω] u (x (n + 1)) + B[ω] (x (n + 1)) (x n) : ℝ)) : EReal)
        = ψ (x (n + 1)) +
            ((((inner ℝ
                ((∇ (fun z ↦ (ω z).toReal) (x n)) - (∇ (fun z ↦ (ω z).toReal) (x (n + 1))))
                (u - x (n + 1)) +
                B[ω] u (x n) : ℝ)) : EReal)) := by
              rw [hthree]
    _ = (((inner ℝ
            ((∇ (fun z ↦ (ω z).toReal) (x n)) - (∇ (fun z ↦ (ω z).toReal) (x (n + 1))))
            (u - x (n + 1)) : ℝ)) : EReal) +
          ψ (x (n + 1)) +
          (((B[ω] u (x n) : ℝ)) : EReal) := by
            simp [EReal.coe_add, add_assoc, add_left_comm, add_comm]
    _ ≤ ψ u + (((B[ω] u (x n) : ℝ)) : EReal) := hshift

/-- Helper for Theorem 10.72: expose the source second-prox segment comparison for
`(m(·, x^n) + g) / L_n` in the chapter's `scaled_bregman_objective` notation. -/
lemma non_euclidean_scaled_objective_successor_add_bregman_le_comparator
    (hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (n : ℕ) {u : E} (hu : u ∈ effective_domain g) :
    scaled_bregman_objective f g ω (x n) (L n) (x (n + 1)) +
      (((B[ω] u (x (n + 1)) : ℝ)) : EReal) ≤
    scaled_bregman_objective f g ω (x n) (L n) u := by
  -- The public comparator theorem is just the source plus-form bridge rewritten in the chapter's
  -- `scaled_bregman_objective` notation.
  simpa [scaled_bregman_objective, non_euclidean_scaled_linearized_objective,
    add_assoc, add_left_comm, add_comm] using
    psi_n_second_prox_three_point_bridge hproblem hω hω_diff htraj n hu

/-- Helper for Theorem 10.72: any trial curvature `Lbar ≥ L_f` is accepted by the B5 upper-model
test at the current non-Euclidean proximal-gradient iterate. -/
lemma non_euclidean_B5_accepts_of_stepsize_ge_Lf
    (hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)]
    [Fact (is_convex_function g)]
    [hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ)]
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (n : ℕ) (Lbar : PosReal) (hLbar : (Lf : ℝ) ≤ (Lbar : ℝ)) :
    non_euclidean_proximal_gradient_backtracking_B5_accepts f g ω Lbar (x n) := by
  have hxn := is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj n
  have hxng := hxn.1
  have hdiff := is_non_euclidean_proximal_gradient_trajectory_differentiable_at htraj n
  rcases existsUnique_non_euclidean_proximal_gradient_step_mem_effectiveDomain
      f g ω (x n) Lbar hxn hdiff with
    ⟨xNext, hxNext, _⟩
  have hstep : non_euclidean_proximal_gradient_step f g ω (x n) Lbar xNext := hxNext.1
  have hxNextg :
      xNext ∈ effective_domain g := by
    exact hxNext.2
  have hxn_int :
      x n ∈ interior (effective_domain f) :=
    hproblem.g_effective_domain_subset_interior_f_effective_domain hxng
  have hxNext_int :
      xNext ∈ interior (effective_domain f) :=
    hproblem.g_effective_domain_subset_interior_f_effective_domain hxNextg
  have hdescentLf :
      (f xNext).toReal ≤
        (f (x n)).toReal +
          inner ℝ (∇ (fun y ↦ (f y).toReal) (x n)) (xNext - x n) +
          ((Lf : ℝ) / 2) * ‖xNext - x n‖ ^ (2 : ℕ) := by
    -- Lemma 5.7 gives the textbook descent model at the current iterate and trial point.
    simpa [norm_sub_rev] using
      (is_l_smooth_on_descent_lemma
        hproblem.f_effective_domain_convex.interior
        hproblem.f_toReal_smooth_on_interior_effective_domain
        hxn_int
        hxNext_int)
  have hdescentLbar :
      (f xNext).toReal ≤
        (f (x n)).toReal +
          inner ℝ (∇ (fun y ↦ (f y).toReal) (x n)) (xNext - x n) +
          ((Lbar : ℝ) / 2) * ‖xNext - x n‖ ^ (2 : ℕ) := by
    -- Increasing the curvature coefficient from `L_f` to `Lbar` preserves the upper model.
    have hnorm_nonneg : 0 ≤ ‖xNext - x n‖ ^ (2 : ℕ) := by
      positivity
    nlinarith
  have hupper :
      f xNext ≤
        f (x n) +
          ((inner ℝ (∇ (fun y ↦ (f y).toReal) (x n)) (xNext - x n) +
            ((Lbar : ℝ) / 2) * ‖xNext - x n‖ ^ (2 : ℕ) : ℝ) : EReal) :=
    non_euclidean_upper_model_of_toReal_le hdiff hxNext_int hdescentLbar
  -- Repackage the descent inequality into the owner-level B5 acceptance predicate.
  refine (non_euclidean_proximal_gradient_backtracking_B5_accepts_iff f g ω Lbar (x n)).2 ?_
  exact ⟨xNext, hstep, hupper⟩

/-- Helper for Theorem 10.72: under B5, the chosen curvature sits between the previous trial
curvature and `max {η L_f, L_prev}`. -/
lemma non_euclidean_B5_local_stepsize_bounds
    (hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)]
    [Fact (is_convex_function g)]
    [hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ)]
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    {s : PosReal} {η : ProximalGradientBacktrackingGrowthFactor}
    (hB5 : UsesNonEuclideanProximalGradientBacktrackingB5Rule f g ω x L s η)
    (n : ℕ) :
    let LPrev := proximal_gradient_backtracking_B2_previous_stepsize s L n
    (LPrev : ℝ) ≤ (L n : ℝ) ∧
      (L n : ℝ) ≤ max ((η : ℝ) * (Lf : ℝ)) (LPrev : ℝ) := by
  rcases hB5.existsIndex n with ⟨i, hi⟩
  rcases hi with ⟨hi, hLk⟩
  dsimp
  constructor
  · -- Every accepted B5 trial has the form `L_prev * η^i`, so it is at least `L_prev`.
    rw [hLk, proximal_gradient_backtracking_trial_stepsize_coe]
    have hηge1 : (1 : ℝ) ≤ (η : ℝ) := le_of_lt η.2
    have hLPrev_nonneg :
        0 ≤ (proximal_gradient_backtracking_B2_previous_stepsize s L n : ℝ) := by
      exact le_of_lt (proximal_gradient_backtracking_B2_previous_stepsize s L n).2
    exact le_mul_of_one_le_right hLPrev_nonneg (one_le_pow₀ hηge1)
  · cases i with
    | zero =>
        -- Accepting the first trial means the chosen curvature is exactly the previous one.
        rw [hLk, proximal_gradient_backtracking_trial_stepsize_coe]
        simp
    | succ m =>
        let LPrev : PosReal := proximal_gradient_backtracking_B2_previous_stepsize s L n
        let Ltrial : PosReal := proximal_gradient_backtracking_trial_stepsize LPrev η m
        have hreject :
            ¬ non_euclidean_proximal_gradient_backtracking_B5_accepts
                f g ω Ltrial (x n) := by
          exact
            IsBacktrackingProcedureB5Index.not_accepts_of_lt
              f g ω hi (Nat.lt_succ_self m)
        have htrial_lt_lf : (Ltrial : ℝ) < (Lf : ℝ) := by
          refine lt_of_not_ge fun hnot ↦ ?_
          exact hreject <|
            non_euclidean_B5_accepts_of_stepsize_ge_Lf
              hproblem htraj n Ltrial hnot
        have haccepted_eq :
            (L n : ℝ) = (Ltrial : ℝ) * (η : ℝ) := by
          simp [hLk, Ltrial, LPrev, proximal_gradient_backtracking_trial_stepsize_coe,
            pow_succ, mul_assoc]
        have haccepted_lt :
            (L n : ℝ) < (η : ℝ) * (Lf : ℝ) := by
          have hη_pos : 0 < (η : ℝ) := lt_trans zero_lt_one η.2
          rw [haccepted_eq]
          nlinarith
        exact le_trans (le_of_lt haccepted_lt) (le_max_left _ _)

/-- Helper for Theorem 10.72: if `α = max {η, s / L_f}` with `L_f > 0`, then
`α L_f = max {η L_f, s}`. -/
lemma non_euclidean_alpha_mul_lf_eq_max_stepsize
    {s : PosReal} {η : ProximalGradientBacktrackingGrowthFactor}
    (hLf : 0 < (Lf : ℝ))
    (hα : α = max (η : ℝ) ((s : ℝ) / (Lf : ℝ))) :
    max ((η : ℝ) * (Lf : ℝ)) (s : ℝ) = α * (Lf : ℝ) := by
  -- Split on which branch of the textbook `max` defines `α`.
  rw [hα]
  by_cases hη : (η : ℝ) ≤ (s : ℝ) / (Lf : ℝ)
  · have hs : (s : ℝ) = ((s : ℝ) / (Lf : ℝ)) * (Lf : ℝ) := by
      field_simp [hLf.ne']
    have hηLf : (η : ℝ) * (Lf : ℝ) ≤ (s : ℝ) := by
      nlinarith
    rw [max_eq_right hηLf, max_eq_right hη]
    exact hs
  · have hηlt : (s : ℝ) / (Lf : ℝ) < (η : ℝ) := lt_of_not_ge hη
    have hsLf : (s : ℝ) < (η : ℝ) * (Lf : ℝ) := by
      have hmul :
          ((s : ℝ) / (Lf : ℝ)) * (Lf : ℝ) < (η : ℝ) * (Lf : ℝ) := by
        exact mul_lt_mul_of_pos_right hηlt hLf
      have hs :
          ((s : ℝ) / (Lf : ℝ)) * (Lf : ℝ) = (s : ℝ) := by
        field_simp [hLf.ne']
      rw [hs] at hmul
      exact hmul
    rw [max_eq_left (le_of_lt hsLf), max_eq_left (le_of_lt hηlt)]

/-- Helper for Theorem 10.72: the non-Euclidean sublinear-rate owner forces the rate constant
`α` to be positive. -/
lemma non_euclidean_sublinear_rate_alpha_pos
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (hrule : hproblem.NonEuclideanSublinearRateStepsizeRule hω x L α) :
    0 < α := by
  rcases hrule with ⟨hα, _⟩ | ⟨hLf, s, η, hα, _⟩
  · simpa [hα]
  · rw [hα]
    have hη_pos : 0 < (η : ℝ) := lt_trans zero_lt_one η.2
    have hs_div_pos : 0 < (s : ℝ) / (Lf : ℝ) := by
      exact div_pos s.2 hLf
    exact lt_of_lt_of_le hη_pos (le_max_left _ _)

/-- Helper for Theorem 10.72: every admissible constant/B5 stepsize satisfies the uniform bound
`L_n ≤ α L_f`. -/
lemma non_euclidean_stepsize_control
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (hrule : hproblem.NonEuclideanSublinearRateStepsizeRule hω x L α)
    (n : ℕ) :
    (L n : ℝ) ≤ α * (Lf : ℝ) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  letI : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ) := hω
  rcases hrule with ⟨hα, hLconst⟩ | ⟨hLf, s, η, hα, hB5⟩
  · -- In the constant branch, every curvature estimate equals `L_f`.
    simpa [hα, hLconst n]
  · have hglobal :
        (L n : ℝ) ≤ max ((η : ℝ) * (Lf : ℝ)) (s : ℝ) := by
      induction n with
      | zero =>
          -- The initial comparison uses the seed curvature `s` as the previous trial.
          have hlocal :=
            non_euclidean_B5_local_stepsize_bounds
              hproblem htraj hB5 0
          simpa [proximal_gradient_backtracking_B2_previous_stepsize_zero] using hlocal.2
      | succ n ih =>
          have hlocal :=
            non_euclidean_B5_local_stepsize_bounds
              hproblem htraj hB5 (n + 1)
          have hstep :
              (L (n + 1) : ℝ) ≤ max ((η : ℝ) * (Lf : ℝ)) (L n : ℝ) := by
            simpa [proximal_gradient_backtracking_B2_previous_stepsize_succ] using hlocal.2
          have hmax_le :
              max ((η : ℝ) * (Lf : ℝ)) (L n : ℝ) ≤
                max ((η : ℝ) * (Lf : ℝ)) (s : ℝ) := by
            exact max_le (le_max_left _ _) ih
          exact le_trans hstep hmax_le
    have hαlf :
        max ((η : ℝ) * (Lf : ℝ)) (s : ℝ) = α * (Lf : ℝ) :=
      non_euclidean_alpha_mul_lf_eq_max_stepsize hLf hα
    -- The B5 recurrence therefore matches the textbook rate constant `α`.
    simpa [hαlf] using hglobal

/-- Helper for Theorem 10.72: on `effective_domain g`, the composite objective is a finite real
sum of the finite `f`- and `g`-values. -/
lemma non_euclidean_objective_eq_real_of_mem_effective_domain
    (hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    {z : E} (hz : z ∈ effective_domain g) :
    F z = ((((f z).toReal + (g z).toReal : ℝ)) : EReal) := by
  have hfz : z ∈ effective_domain f := by
    exact interior_subset (hproblem.g_effective_domain_subset_interior_f_effective_domain hz)
  have hfz_val :
      f z = ((((f z).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hfz).ne
        (hproblem.f_ne_bot z)).symm
  have hgz_val :
      g z = ((((g z).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hz).ne
        (hproblem.g_proper.ne_bot z)).symm
  -- Once both summands are finite, the composite objective is the cast of the real sum.
  rw [composite_model_objective_apply, hfz_val, hgz_val]
  simp [EReal.coe_add]

/-- Helper for Theorem 10.72: on `effective_domain g`, the objective value itself is the cast of
its `toReal` value. -/
lemma non_euclidean_objective_eq_coe_toReal_of_mem_effective_domain
    (hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    {z : E} (hz : z ∈ effective_domain g) :
    F z = ((((F z).toReal : ℝ)) : EReal) := by
  rw [non_euclidean_objective_eq_real_of_mem_effective_domain
    hproblem hz]
  rw [EReal.toReal_coe]

/-- Helper for Theorem 10.72: every positive non-Euclidean proximal-gradient iterate lies in
`effective_domain g`. -/
lemma non_euclidean_iterate_mem_effective_domain
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    {n : ℕ} (hn : 1 ≤ n) :
    x n ∈ effective_domain g := by
  rcases Nat.exists_eq_add_of_le hn with ⟨m, rfl⟩
  simpa [Nat.add_comm] using
    (is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj (m + 1)).1

/-- Helper for Theorem 10.72: every positive-index objective gap is finite, so its real value
casts back to the displayed `EReal` gap `F(x^n) - F_opt`. -/
lemma non_euclidean_positive_iterate_gap_coe
    (hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    {n : ℕ} (hn : 1 ≤ n) :
    ((((F (x n)).toReal - FOpt : ℝ)) : EReal) = F (x n) - (FOpt : EReal) := by
  have hx :
      x n ∈ effective_domain g :=
    non_euclidean_iterate_mem_effective_domain htraj hn
  have hx_obj :
      F (x n) = ((((f (x n)).toReal + (g (x n)).toReal : ℝ)) : EReal) :=
    non_euclidean_objective_eq_real_of_mem_effective_domain hproblem hx
  -- Rewrite the finite iterate objective before simplifying the `EReal` subtraction.
  rw [hx_obj, EReal.toReal_coe]
  simp [EReal.coe_sub]

/-- Helper for Theorem 10.72: every positive-index objective gap is nonnegative as a real
number. -/
lemma non_euclidean_positive_iterate_gap_nonneg
    (hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ (F (x n)).toReal - FOpt := by
  have hgapE :
      ((0 : ℝ) : EReal) ≤ ((((F (x n)).toReal - FOpt : ℝ)) : EReal) := by
    rw [non_euclidean_positive_iterate_gap_coe
      hproblem htraj hn]
    have hnonneg_gap : (0 : EReal) ≤ F (x n) - (FOpt : EReal) := by
      exact
        (EReal.sub_nonneg
          (.inr (EReal.coe_ne_top FOpt))
          (.inr (EReal.coe_ne_bot FOpt))).2 <|
          non_euclidean_objective_gap_nonneg hproblem n
    simpa using hnonneg_gap
  exact EReal.coe_nonneg.mp hgapE

/-- Helper for Theorem 10.72: rewrite the stabilized Chapter 9 comparator directly into the
textbook finite-`EReal` one-step inequality
`F(x^(n+1)) + L_n B_ω(x*, x^(n+1)) ≤ F(x*) + L_n B_ω(x*, x^n)`. -/
lemma non_euclidean_textbook_successor_add_scaled_bregman_le_optimizer
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (hrule : hproblem.NonEuclideanSublinearRateStepsizeRule hω x L α)
    (hxStar : xStar ∈ XStar)
    (n : ℕ) :
    F (x (n + 1)) + ((((L n : ℝ) * B[ω] xStar (x (n + 1)) : ℝ)) : EReal) ≤
      F xStar + ((((L n : ℝ) * B[ω] xStar (x n) : ℝ)) : EReal) := by
  let c : EReal :=
    (((f (x n)).toReal - inner ℝ (∇ (fun y ↦ (f y).toReal) (x n)) (x n) : ℝ) : EReal)
  have hdiff := is_non_euclidean_proximal_gradient_trajectory_differentiable_at htraj n
  have hxStar_eff :
      xStar ∈ effective_domain g :=
    non_euclidean_optimizer_mem_effective_domain_g hproblem hxStar
  have hrule_cb5 :
      hproblem.ConstantOrBacktrackingB5StepsizeRule hω x L :=
    hproblem.sublinearRateStepsizeRule_constantOrBacktrackingB5 hrule
  have hsucc_le_model :
      F (x (n + 1)) ≤ non_euclidean_textbook_model f g ω (x n) (L n) (x (n + 1)) :=
    non_euclidean_successor_le_textbook_model
      hω hω_diff htraj hrule_cb5 n (x (n + 1))
  have hcompare_model :
      non_euclidean_textbook_model f g ω (x n) (L n) (x (n + 1)) +
          ((((L n : ℝ) * B[ω] xStar (x (n + 1)) : ℝ)) : EReal) ≤
        non_euclidean_textbook_model f g ω (x n) (L n) xStar := by
    have hLn_nonneg : (0 : EReal) ≤ ((L n : ℝ) : EReal) := by
      exact_mod_cast le_of_lt (PosReal.coe_pos (L n))
    have hscaled :
        ((L n : ℝ) : EReal) *
            (scaled_bregman_objective f g ω (x n) (L n) (x (n + 1)) +
              (((B[ω] xStar (x (n + 1)) : ℝ)) : EReal)) ≤
          ((L n : ℝ) : EReal) * scaled_bregman_objective f g ω (x n) (L n) xStar := by
      -- Scale the Chapter 9 plus-form comparator by the positive curvature `L_n`.
      exact mul_le_mul_of_nonneg_left
        (non_euclidean_scaled_objective_successor_add_bregman_le_comparator
          hproblem hω hω_diff htraj n hxStar_eff)
        hLn_nonneg
    have hshift :
        c +
            ((L n : ℝ) : EReal) *
              (scaled_bregman_objective f g ω (x n) (L n) (x (n + 1)) +
                (((B[ω] xStar (x (n + 1)) : ℝ)) : EReal)) ≤
          c + ((L n : ℝ) : EReal) * scaled_bregman_objective f g ω (x n) (L n) xStar := by
      -- Add back the finite constant from the textbook-model normalization.
      simpa [add_assoc, add_left_comm, add_comm] using add_le_add_right hscaled c
    have hlhs :
        non_euclidean_textbook_model f g ω (x n) (L n) (x (n + 1)) +
            ((((L n : ℝ) * B[ω] xStar (x (n + 1)) : ℝ)) : EReal) =
          c +
            ((L n : ℝ) : EReal) *
              (scaled_bregman_objective f g ω (x n) (L n) (x (n + 1)) +
                (((B[ω] xStar (x (n + 1)) : ℝ)) : EReal)) := by
      have hdistrib :
          ((L n : ℝ) : EReal) *
              scaled_bregman_objective f g ω (x n) (L n) (x (n + 1)) +
            ((L n : ℝ) : EReal) * (((B[ω] xStar (x (n + 1)) : ℝ)) : EReal) =
          ((L n : ℝ) : EReal) *
            (scaled_bregman_objective f g ω (x n) (L n) (x (n + 1)) +
              (((B[ω] xStar (x (n + 1)) : ℝ)) : EReal)) := by
        rw [← EReal.left_distrib_of_nonneg_of_ne_top
          hLn_nonneg (EReal.coe_ne_top _)]
      -- Route correction: normalize the successor side to `c + L_n (scaledObjective + Bregman)`.
      calc
        non_euclidean_textbook_model f g ω (x n) (L n) (x (n + 1)) +
            ((((L n : ℝ) * B[ω] xStar (x (n + 1)) : ℝ)) : EReal)
            =
          c +
              ((L n : ℝ) : EReal) * scaled_bregman_objective f g ω (x n) (L n) (x (n + 1)) +
                ((((L n : ℝ) * B[ω] xStar (x (n + 1)) : ℝ)) : EReal) := by
                  rw [non_euclidean_model_eq_constant_add_scaled_bregman_objective
                    f g ω (x n) (x (n + 1)) (L n) hdiff]
        _ = c +
                ((L n : ℝ) : EReal) * scaled_bregman_objective f g ω (x n) (L n) (x (n + 1)) +
                  ((L n : ℝ) : EReal) * (((B[ω] xStar (x (n + 1)) : ℝ)) : EReal) := by
                rw [EReal.coe_mul]
        _ = c +
                ((L n : ℝ) : EReal) *
                  (scaled_bregman_objective f g ω (x n) (L n) (x (n + 1)) +
                    (((B[ω] xStar (x (n + 1)) : ℝ)) : EReal)) := by
                simpa [add_assoc, add_left_comm, add_comm] using
                  congrArg (fun t : EReal ↦ c + t) hdistrib
    have hrhs :
        c + ((L n : ℝ) : EReal) * scaled_bregman_objective f g ω (x n) (L n) xStar =
          non_euclidean_textbook_model f g ω (x n) (L n) xStar := by
      rw [non_euclidean_model_eq_constant_add_scaled_bregman_objective
        f g ω (x n) xStar (L n) hdiff]
    -- Route correction: rewrite the scaled Chapter 9 inequality into textbook-model form first,
    -- then use it as the stable finite `EReal` bridge for clause (b).
    calc
      non_euclidean_textbook_model f g ω (x n) (L n) (x (n + 1)) +
          ((((L n : ℝ) * B[ω] xStar (x (n + 1)) : ℝ)) : EReal)
          = c +
              ((L n : ℝ) : EReal) *
                (scaled_bregman_objective f g ω (x n) (L n) (x (n + 1)) +
                  (((B[ω] xStar (x (n + 1)) : ℝ)) : EReal)) := hlhs
      _ ≤ c + ((L n : ℝ) : EReal) * scaled_bregman_objective f g ω (x n) (L n) xStar := hshift
      _ = non_euclidean_textbook_model f g ω (x n) (L n) xStar := hrhs
  have hmodel_le_objective :
      non_euclidean_textbook_model f g ω (x n) (L n) xStar ≤
        F xStar + ((((L n : ℝ) * B[ω] xStar (x n) : ℝ)) : EReal) :=
    non_euclidean_textbook_model_le_objective_add_bregman
      hproblem htraj hxStar_eff
  -- Sandwich the middle textbook model between the true successor objective and the optimizer
  -- comparison bound from the source route.
  calc
    F (x (n + 1)) + ((((L n : ℝ) * B[ω] xStar (x (n + 1)) : ℝ)) : EReal)
        ≤ non_euclidean_textbook_model f g ω (x n) (L n) (x (n + 1)) +
            ((((L n : ℝ) * B[ω] xStar (x (n + 1)) : ℝ)) : EReal) := by
              simpa [add_comm] using
                add_le_add_right hsucc_le_model
                  ((((L n : ℝ) * B[ω] xStar (x (n + 1)) : ℝ)) : EReal)
    _ ≤ non_euclidean_textbook_model f g ω (x n) (L n) xStar := hcompare_model
    _ ≤ F xStar + ((((L n : ℝ) * B[ω] xStar (x n) : ℝ)) : EReal) := hmodel_le_objective

/-- Helper for Theorem 10.72: route correction for clause (b). After the Chapter 9 comparator has
been stabilized, convert it to the textbook one-step gap drop
`F(x^(n+1)) - F_opt ≤ L_n (B_ω(x*, x^n) - B_ω(x*, x^(n+1)))`. -/
lemma non_euclidean_one_step_gap_le_scaled_bregman_drop
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (hrule : hproblem.NonEuclideanSublinearRateStepsizeRule hω x L α)
    (hxStar : xStar ∈ XStar)
    (n : ℕ) :
    (F (x (n + 1))).toReal - FOpt ≤
      (L n : ℝ) * (B[ω] xStar (x n) - B[ω] xStar (x (n + 1))) := by
  have hxsucc_eff :
      x (n + 1) ∈ effective_domain g :=
    non_euclidean_iterate_mem_effective_domain
      htraj (Nat.succ_le_succ (Nat.zero_le n))
  have hbridge :=
    non_euclidean_textbook_successor_add_scaled_bregman_le_optimizer
      hω hω_diff htraj hrule hxStar n
  have hsucc_obj :
      F (x (n + 1)) = ((((F (x (n + 1))).toReal : ℝ)) : EReal) :=
    non_euclidean_objective_eq_coe_toReal_of_mem_effective_domain
      hproblem hxsucc_eff
  have hopt_obj :
      F xStar = (FOpt : EReal) :=
    IsConvexCompositeSmoothMinimizationProblem.objective_eq_optimalValue_of_mem_optimalSet
      hproblem hxStar
  have hbridge_realE :
      ((((F (x (n + 1))).toReal + (L n : ℝ) * B[ω] xStar (x (n + 1)) : ℝ)) : EReal) ≤
        ((((FOpt + (L n : ℝ) * B[ω] xStar (x n) : ℝ)) : EReal)) := by
    -- Rewrite both objective values to finite real coercions before moving to `ℝ`.
    rw [hsucc_obj, hopt_obj] at hbridge
    simpa [EReal.coe_add, EReal.coe_mul, add_assoc, add_left_comm, add_comm] using hbridge
  have hbridge_real :
      (F (x (n + 1))).toReal + (L n : ℝ) * B[ω] xStar (x (n + 1)) ≤
        FOpt + (L n : ℝ) * B[ω] xStar (x n) :=
    EReal.coe_le_coe_iff.mp hbridge_realE
  -- Rearranging the finite real inequality gives the source gap-drop estimate `(10.99)`.
  linarith

/-- Helper for Theorem 10.72: dividing the one-step drop by the source denominator `α L_f`
produces the textbook normalized gap inequality `(10.100)`. -/
lemma non_euclidean_one_step_gap_div_le_bregman_drop
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (hrule : hproblem.NonEuclideanSublinearRateStepsizeRule hω x L α)
    (hxStar : xStar ∈ XStar)
    (n : ℕ) :
    ((F (x (n + 1))).toReal - FOpt) / (α * (Lf : ℝ)) ≤
      B[ω] xStar (x n) - B[ω] xStar (x (n + 1)) := by
  have hstep :=
    non_euclidean_one_step_gap_le_scaled_bregman_drop
      hω hω_diff htraj hrule hxStar n
  have hgap_nonneg :
      0 ≤ (F (x (n + 1))).toReal - FOpt :=
    non_euclidean_positive_iterate_gap_nonneg
      hproblem htraj (Nat.succ_le_succ (Nat.zero_le n))
  have hdrop_nonneg :
      0 ≤ B[ω] xStar (x n) - B[ω] xStar (x (n + 1)) := by
    -- The one-step drop must be nonnegative because it dominates the nonnegative objective gap.
    have hLn_pos : 0 < (L n : ℝ) := PosReal.coe_pos (L n)
    nlinarith
  have hscale_le :
      (L n : ℝ) * (B[ω] xStar (x n) - B[ω] xStar (x (n + 1))) ≤
        (α * (Lf : ℝ)) * (B[ω] xStar (x n) - B[ω] xStar (x (n + 1))) := by
    -- The source stepsize owner bounds `L_n` by the uniform rate constant `α L_f`.
    exact
      mul_le_mul_of_nonneg_right
        (non_euclidean_stepsize_control
          hω htraj hrule n)
        hdrop_nonneg
  have hαLf_pos : 0 < α * (Lf : ℝ) := by
    exact
      mul_pos
        (non_euclidean_sublinear_rate_alpha_pos
          hω hrule)
        (hproblem.sublinearRateStepsizeRule_lf_pos_of_nonEuclidean hrule)
  have hscaled :
      (F (x (n + 1))).toReal - FOpt ≤
        (α * (Lf : ℝ)) * (B[ω] xStar (x n) - B[ω] xStar (x (n + 1))) := by
    -- Replace the local factor `L_n` in `(10.99)` by the global bound `α L_f`.
    exact le_trans hstep hscale_le
  -- Divide through by the positive scalar `α L_f` to obtain `(10.100)`.
  exact (div_le_iff₀ hαLf_pos).2 <| by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- Helper for Theorem 10.72: summing the normalized one-step inequalities telescopes the Bregman
terms exactly as in `(10.102)`. -/
lemma non_euclidean_real_prefix_telescope
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (hrule : hproblem.NonEuclideanSublinearRateStepsizeRule hω x L α)
    (hxStar : xStar ∈ XStar)
    (K : ℕ) :
    Finset.sum (Finset.range (K + 1))
        (fun i ↦ ((F (x (i + 1))).toReal - FOpt) / (α * (Lf : ℝ))) +
      B[ω] xStar (x (K + 1)) ≤
    B[ω] xStar (x 0) := by
  let gap : ℕ → ℝ :=
    fun i ↦ ((F (x (i + 1))).toReal - FOpt) / (α * (Lf : ℝ))
  induction K with
  | zero =>
      have hstep :=
        non_euclidean_one_step_gap_div_le_bregman_drop
          hω hω_diff htraj hrule hxStar 0
      have hbase :
          gap 0 + B[ω] xStar (x (0 + 1)) ≤ B[ω] xStar (x 0) := by
        -- The first normalized one-step drop is already the `K = 0` telescope.
        have hstep' :
            gap 0 ≤ B[ω] xStar (x 0) - B[ω] xStar (x (0 + 1)) := by
          simpa [gap] using hstep
        exact (le_sub_iff_add_le).1 hstep'
      simpa [gap, Finset.sum_range_one] using hbase
  | succ K ih =>
      have hstep :=
        non_euclidean_one_step_gap_div_le_bregman_drop
          hω hω_diff htraj hrule hxStar (K + 1)
      have hstep' :
          gap (K + 1) + B[ω] xStar (x (K + 2)) ≤ B[ω] xStar (x (K + 1)) := by
        -- Append the next normalized drop to extend the telescope by one step.
        have hstep'' :
            gap (K + 1) ≤
              B[ω] xStar (x (K + 1)) - B[ω] xStar (x (K + 2)) := by
          simpa [gap] using hstep
        exact (le_sub_iff_add_le).1 hstep''
      calc
        Finset.sum (Finset.range (K + 2)) gap + B[ω] xStar (x (K + 2))
            =
          Finset.sum (Finset.range (K + 1)) gap +
            (gap (K + 1) + B[ω] xStar (x (K + 2))) := by
              rw [Finset.sum_range_succ]
              ring
        _ ≤
          Finset.sum (Finset.range (K + 1)) gap +
            B[ω] xStar (x (K + 1)) := by
              have hprefix_add :=
                add_le_add_left hstep' (Finset.sum (Finset.range (K + 1)) gap)
              simpa [add_assoc, add_left_comm, add_comm] using hprefix_add
        _ ≤ B[ω] xStar (x 0) := ih

-- Proof sketch: keep the source-faithful Chapter 9 route. The key bridge is the one-step
-- inequality obtained by the second-prox segment argument for the scaled linearized objective,
-- rewriting with the three-point identity, and telescoping the resulting Bregman differences.
/-- Theorem 10.72 (2): clause (b). Under the same assumptions as clause (1), every positive
iterate satisfies the non-Euclidean sublinear objective-gap estimate
`F(x^k) - F_opt ≤ α L_f B[ω] x* x^0 / k` for every optimizer `x* ∈ X^*`. -/
theorem non_euclidean_proximal_gradient_objective_gap_le
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (hrule : hproblem.NonEuclideanSublinearRateStepsizeRule hω x L α)
    (hxStar : xStar ∈ XStar) (k : ℕ) (hk : 1 ≤ k) :
    F (x k) - (FOpt : EReal) ≤
      (((α * (Lf : ℝ) * B[ω] xStar (x 0) / (k : ℝ) : ℝ)) : EReal) := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le hk
  let gap : ℕ → ℝ :=
    fun i ↦ ((F (x (i + 1))).toReal - FOpt) / (α * (Lf : ℝ))
  have hprefix :=
    non_euclidean_real_prefix_telescope
      hω hω_diff htraj hrule hxStar K
  have hrule_cb5 :
      hproblem.ConstantOrBacktrackingB5StepsizeRule hω x L :=
    hproblem.sublinearRateStepsizeRule_constantOrBacktrackingB5 hrule
  have hanti_obj :=
    non_euclidean_proximal_gradient_objective_values_antitone
      hω hω_diff htraj hrule_cb5
  have hαLf_pos : 0 < α * (Lf : ℝ) := by
    exact
      mul_pos
        (non_euclidean_sublinear_rate_alpha_pos
          hω hrule)
        (hproblem.sublinearRateStepsizeRule_lf_pos_of_nonEuclidean hrule)
  have hxStar_eff :
      xStar ∈ effective_domain g :=
    non_euclidean_optimizer_mem_effective_domain_g hproblem hxStar
  have hsum_lower :
      ((K + 1 : ℝ) * gap K) ≤
        Finset.sum (Finset.range (K + 1)) gap := by
    calc
      ((K + 1 : ℝ) * gap K) =
          Finset.sum (Finset.range (K + 1)) (fun _ ↦ gap K) := by
            simp
      _ ≤ Finset.sum (Finset.range (K + 1)) gap := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have hi_le : i ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            have hobj :
                F (x (K + 1)) ≤ F (x (i + 1)) :=
              hanti_obj (Nat.succ_le_succ hi_le)
            have hK_eff :
                x (K + 1) ∈ effective_domain g :=
              non_euclidean_iterate_mem_effective_domain
                htraj (Nat.succ_le_succ (Nat.zero_le K))
            have hi_eff :
                x (i + 1) ∈ effective_domain g :=
              non_euclidean_iterate_mem_effective_domain
                htraj (Nat.succ_le_succ (Nat.zero_le i))
            have hK_obj :
                F (x (K + 1)) = ((((F (x (K + 1))).toReal : ℝ)) : EReal) :=
              non_euclidean_objective_eq_coe_toReal_of_mem_effective_domain
                hproblem hK_eff
            have hi_obj :
                F (x (i + 1)) = ((((F (x (i + 1))).toReal : ℝ)) : EReal) :=
              non_euclidean_objective_eq_coe_toReal_of_mem_effective_domain
                hproblem hi_eff
            have htoReal :
                (F (x (K + 1))).toReal ≤ (F (x (i + 1))).toReal := by
              -- Clause (a) compares finite objective values, so it descends to `toReal`.
              exact
                EReal.toReal_le_toReal hobj
                  (by
                    rw [hK_obj]
                    exact EReal.coe_ne_bot _)
                  (by
                    rw [hi_obj]
                    exact EReal.coe_ne_top _)
            have hi_gap :
                (F (x (K + 1))).toReal - FOpt ≤
                  (F (x (i + 1))).toReal - FOpt :=
              sub_le_sub_right htoReal FOpt
            exact div_le_div_of_nonneg_right hi_gap (le_of_lt hαLf_pos)
  have hK_eff :
      x (K + 1) ∈ effective_domain g :=
    non_euclidean_iterate_mem_effective_domain
      htraj (Nat.succ_le_succ (Nat.zero_le K))
  have hK_subgrad :
      x (K + 1) ∈ subdifferential_domain ω :=
    (is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj (K + 1)).2
  have hbreg_nonneg :
      0 ≤ B[ω] xStar (x (K + 1)) := by
    -- The terminal Bregman term is nonnegative, so dropping it preserves the prefix bound.
    exact
      bregmanDistance_nonneg_of_mem_subdifferential_domain
        hω xStar (x (K + 1)) hxStar_eff hK_eff hK_subgrad
          (hω_diff (x (K + 1)) hK_subgrad)
  have hsum_upper :
      Finset.sum (Finset.range (K + 1)) gap ≤ B[ω] xStar (x 0) := by
    nlinarith [hprefix, hbreg_nonneg]
  have hgap_real :
      gap K ≤ B[ω] xStar (x 0) / (K + 1 : ℝ) := by
    have hmul :
        ((K + 1 : ℝ) * gap K) ≤ B[ω] xStar (x 0) :=
      le_trans hsum_lower hsum_upper
    exact (le_div_iff₀ (by exact_mod_cast Nat.succ_pos K)).2 <| by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hreal :
      (F (x (K + 1))).toReal - FOpt ≤
        α * (Lf : ℝ) * B[ω] xStar (x 0) / (K + 1 : ℝ) := by
    have hscaled :
        (F (x (K + 1))).toReal - FOpt ≤
          (B[ω] xStar (x 0) / (K + 1 : ℝ)) * (α * (Lf : ℝ)) := by
      -- Multiply the averaged normalized bound back by the positive denominator `α L_f`.
      exact (div_le_iff₀ hαLf_pos).1 hgap_real
    simpa [gap, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hgapE :
      ((((F (x (K + 1))).toReal - FOpt : ℝ)) : EReal) ≤
        (((α * (Lf : ℝ) * B[ω] xStar (x 0) / (K + 1 : ℝ) : ℝ)) : EReal) :=
    EReal.coe_le_coe_iff.mpr hreal
  have hgap_coe :
      ((((F (x (K + 1))).toReal - FOpt : ℝ)) : EReal) =
        F (x (K + 1)) - (FOpt : EReal) :=
    non_euclidean_positive_iterate_gap_coe
      hproblem htraj (Nat.succ_le_succ (Nat.zero_le K))
  have hfinal :
      F (x (K + 1)) - (FOpt : EReal) ≤
        (((α * (Lf : ℝ) * B[ω] xStar (x 0) / (K + 1 : ℝ) : ℝ)) : EReal) := by
    rw [← hgap_coe]
    exact hgapE
  -- Convert `K + 1` back to the original positive index `k = 1 + K`.
  simpa [Nat.add_comm] using hfinal

end

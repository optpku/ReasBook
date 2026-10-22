/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_2_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_5_extra_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.InitialSublevelSet
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic

open Filter
open scoped Gradient

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Domain sampling:
-- * source-facing: the sequential Wolfe-Powell line-search convergence statement for the iterates
--   `x`, directions `s`, and steplengths `α`;
-- * core/canonical: the chapter owners `lineSearchObjective`, `WolfePowellParameters`,
--   `WolfePowellCondition`, and the mathlib gradient owner `∇`;
-- * bridge/view: the derivative bridge `deriv (lineSearchObjective f (x k) (s k))`, identified
--   by `deriv_lineSearchObjective_apply`, the cosine-to-ratio bridge
--   `gradientNorm_mul_cos_angle_searchDirection_negGradient_eq_neg_gradientInner_div_norm`,
--   and the update relation `x (k + 1) = x k + α k • s k`.
-- Primitive data are therefore the iterate/update sequences, the parameter owner carried by each
-- `WolfePowellCondition`, the per-step Wolfe owner on the canonical search-ray profile, the
-- local gradient witnesses `HasGradientAt f (∇ f y) y` on `initialSublevelSet f (x 0)`, the
-- descent hypothesis, and the uniform continuity of `∇ f` on that same initial-sublevel-set
-- owner. The cosine formulation is the source-facing theorem surface; the ratio limit is a
-- bridge/view consequence.

/-- Helper for Chapter02 Theorem 2.5.5: every Wolfe-Powell step decreases the objective value,
so the iterate values form a descent sequence. -/
lemma wolfePowell_step_value_nonincrease
    (f : E → ℝ) (x s : ℕ → E) (α : ℕ → ℝ) (ρ σ : ℝ)
    (h_hasGradient : ∀ y ∈ initialSublevelSet f (x 0), HasGradientAt f (∇ f y) y)
    (h_update : ∀ k, x (k + 1) = x k + α k • s k)
    (h_descent : ∀ k, inner ℝ (∇ f (x k)) (s k) < 0)
    (h_wolfeStep :
      ∀ k,
        WolfePowellCondition
          (lineSearchObjective f (x k) (s k))
          (deriv (lineSearchObjective f (x k) (s k)))
          ρ σ (α k)) :
    ∀ k, x k ∈ initialSublevelSet f (x 0) → f (x (k + 1)) ≤ f (x k) := by
  intro k hxk
  rcases wolfePowellCondition_iff.mp (h_wolfeStep k) with ⟨h_params, hα, h_dec, _⟩
  rcases wolfePowellParameters_iff.mp h_params with ⟨hρ_pos, _, _⟩
  -- The Wolfe sufficient-decrease clause becomes an explicit bound on `f (x (k + 1))`.
  have h_deriv_zero :
      deriv (lineSearchObjective f (x k) (s k)) 0 = inner ℝ (∇ f (x k)) (s k) := by
    have h_grad_zero : HasGradientAt f (∇ f (x k)) (x k + (0 : ℝ) • s k) := by
      simpa [zero_smul] using h_hasGradient (x k) hxk
    simpa using h_grad_zero.deriv_lineSearchObjective_apply (x := x k) (d := s k) (t := 0)
  have h_upper :
      f (x (k + 1)) ≤ f (x k) + ρ * α k * inner ℝ (∇ f (x k)) (s k) := by
    simpa [lineSearchObjective_apply, lineSearchObjective_zero, h_update k, h_deriv_zero] using h_dec
  have hρα_pos : 0 < ρ * α k := mul_pos hρ_pos hα
  have h_prod_neg : ρ * α k * inner ℝ (∇ f (x k)) (s k) < 0 :=
    mul_neg_of_pos_of_neg hρα_pos (h_descent k)
  -- Since the directional derivative is negative, the Wolfe upper bound is strictly below
  -- `f (x k)`.
  have h_rhs_lt : f (x k) + ρ * α k * inner ℝ (∇ f (x k)) (s k) < f (x k) := by
    simpa using add_lt_add_left h_prod_neg (f (x k))
  exact le_of_lt (lt_of_le_of_lt h_upper h_rhs_lt)

/-- Helper for Chapter02 Theorem 2.5.5: the Wolfe-Powell descent inequality keeps every iterate
inside the initial sublevel set. -/
lemma wolfePowell_iterates_mem_initialSublevelSet
    (f : E → ℝ) (x s : ℕ → E) (α : ℕ → ℝ) (ρ σ : ℝ)
    (h_hasGradient : ∀ y ∈ initialSublevelSet f (x 0), HasGradientAt f (∇ f y) y)
    (h_update : ∀ k, x (k + 1) = x k + α k • s k)
    (h_descent : ∀ k, inner ℝ (∇ f (x k)) (s k) < 0)
    (h_wolfeStep :
      ∀ k,
        WolfePowellCondition
          (lineSearchObjective f (x k) (s k))
          (deriv (lineSearchObjective f (x k) (s k)))
          ρ σ (α k)) :
    ∀ k : ℕ, x k ∈ initialSublevelSet f (x 0) := by
  intro k
  induction k with
  | zero =>
      -- The starting point belongs to its own initial sublevel set.
      exact mem_initialSublevelSet.mpr le_rfl
  | succ k hk =>
      -- One step of Wolfe-Powell descent preserves the initial-sublevel-set invariant.
      refine mem_initialSublevelSet.mpr ?_
      exact le_trans
        (wolfePowell_step_value_nonincrease
          f x s α ρ σ h_hasGradient h_update h_descent h_wolfeStep k hk)
        (mem_initialSublevelSet.mp hk)

/-- Helper for Chapter02 Theorem 2.5.5: the monotone descent sequence `f (x k)` converges
because it is bounded below. -/
lemma wolfePowell_function_values_tendsto
    (f : E → ℝ) (x s : ℕ → E) (α : ℕ → ℝ) (ρ σ : ℝ)
    (h_bddBelow : BddBelow (Set.range f))
    (h_hasGradient : ∀ y ∈ initialSublevelSet f (x 0), HasGradientAt f (∇ f y) y)
    (h_update : ∀ k, x (k + 1) = x k + α k • s k)
    (h_descent : ∀ k, inner ℝ (∇ f (x k)) (s k) < 0)
    (h_wolfeStep :
      ∀ k,
        WolfePowellCondition
          (lineSearchObjective f (x k) (s k))
          (deriv (lineSearchObjective f (x k) (s k)))
          ρ σ (α k)) :
    ∃ l : ℝ, Tendsto (fun k : ℕ ↦ f (x k)) atTop (nhds l) := by
  have h_antitone : Antitone (fun k : ℕ ↦ f (x k)) :=
    antitone_nat_of_succ_le fun k =>
      wolfePowell_step_value_nonincrease
        f x s α ρ σ h_hasGradient h_update h_descent h_wolfeStep k
        (wolfePowell_iterates_mem_initialSublevelSet
          f x s α ρ σ h_hasGradient h_update h_descent h_wolfeStep k)
  have h_range_bddBelow : BddBelow (Set.range (fun k : ℕ ↦ f (x k))) := by
    rcases h_bddBelow with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact hm ⟨x k, rfl⟩
  -- A bounded antitone real sequence converges.
  exact Real.tendsto_of_bddBelow_antitone h_range_bddBelow h_antitone

/-- Helper for Chapter02 Theorem 2.5.5: the consecutive objective drops tend to zero because
the objective values themselves converge. -/
lemma wolfePowell_function_drop_tendsto_zero
    (f : E → ℝ) (x s : ℕ → E) (α : ℕ → ℝ) (ρ σ : ℝ)
    (h_bddBelow : BddBelow (Set.range f))
    (h_hasGradient : ∀ y ∈ initialSublevelSet f (x 0), HasGradientAt f (∇ f y) y)
    (h_update : ∀ k, x (k + 1) = x k + α k • s k)
    (h_descent : ∀ k, inner ℝ (∇ f (x k)) (s k) < 0)
    (h_wolfeStep :
      ∀ k,
        WolfePowellCondition
          (lineSearchObjective f (x k) (s k))
          (deriv (lineSearchObjective f (x k) (s k)))
          ρ σ (α k)) :
    Tendsto (fun k : ℕ ↦ f (x k) - f (x (k + 1))) atTop (nhds 0) := by
  rcases wolfePowell_function_values_tendsto
      f x s α ρ σ h_bddBelow h_hasGradient h_update h_descent h_wolfeStep
      with ⟨l, hl⟩
  have hl_succ : Tendsto (fun k : ℕ ↦ f (x (k + 1))) atTop (nhds l) := by
    exact (Filter.tendsto_add_atTop_iff_nat 1).2 hl
  -- Subtract the shifted convergent sequence from the original one.
  simpa using hl.sub hl_succ

/-- Helper for Chapter02 Theorem 2.5.5: the Wolfe curvature clause yields the executable form of
textbook inequality `(2.5.21)`, bounding the normalized directional derivative by the gradient
difference between consecutive iterates. -/
lemma wolfePowell_curvature_difference_norm_lower_bound
    (f : E → ℝ) (x s : ℕ → E) (α : ℕ → ℝ) (ρ σ : ℝ)
    (h_hasGradient : ∀ y ∈ initialSublevelSet f (x 0), HasGradientAt f (∇ f y) y)
    (h_update : ∀ k, x (k + 1) = x k + α k • s k)
    (h_descent : ∀ k, inner ℝ (∇ f (x k)) (s k) < 0)
    (h_wolfeStep :
      ∀ k,
        WolfePowellCondition
          (lineSearchObjective f (x k) (s k))
          (deriv (lineSearchObjective f (x k) (s k)))
          ρ σ (α k)) :
    ∀ k : ℕ,
      (1 - σ) * (-(inner ℝ (∇ f (x k)) (s k) / ‖s k‖)) ≤
        ‖∇ f (x (k + 1)) - ∇ f (x k)‖ := by
  intro k
  rcases wolfePowellCondition_iff.mp (h_wolfeStep k) with ⟨_, _, _, h_curv⟩
  have hxk :
      x k ∈ initialSublevelSet f (x 0) :=
    wolfePowell_iterates_mem_initialSublevelSet
      f x s α ρ σ h_hasGradient h_update h_descent h_wolfeStep k
  have hxk_succ :
      x (k + 1) ∈ initialSublevelSet f (x 0) :=
    wolfePowell_iterates_mem_initialSublevelSet
      f x s α ρ σ h_hasGradient h_update h_descent h_wolfeStep (k + 1)
  have hs_pos : 0 < ‖s k‖ := by
    refine norm_pos_iff.2 ?_
    intro hs_zero
    exact (lt_irrefl (0 : ℝ)) <| by simpa [hs_zero] using h_descent k
  have h_deriv_zero :
      deriv (lineSearchObjective f (x k) (s k)) 0 = inner ℝ (∇ f (x k)) (s k) := by
    have h_grad_zero : HasGradientAt f (∇ f (x k)) (x k + (0 : ℝ) • s k) := by
      simpa [zero_smul] using h_hasGradient (x k) hxk
    simpa using h_grad_zero.deriv_lineSearchObjective_apply (x := x k) (d := s k) (t := 0)
  have h_deriv_alpha :
      deriv (lineSearchObjective f (x k) (s k)) (α k) =
        inner ℝ (∇ f (x (k + 1))) (s k) := by
    have h_grad_alpha : HasGradientAt f (∇ f (x (k + 1))) (x k + α k • s k) := by
      simpa [h_update k] using h_hasGradient (x (k + 1)) hxk_succ
    simpa using
      h_grad_alpha.deriv_lineSearchObjective_apply
        (x := x k) (d := s k) (t := α k)
  let a : ℝ := inner ℝ (∇ f (x k)) (s k)
  let b : ℝ := inner ℝ (∇ f (x (k + 1))) (s k)
  let diff : E := ∇ f (x (k + 1)) - ∇ f (x k)
  have h_curv_explicit : σ * a ≤ b := by
    simpa [a, b, h_deriv_zero, h_deriv_alpha] using h_curv
  -- Subtract the initial slope from the curvature inequality to expose the gradient difference.
  have h_gap' :
      (1 - σ) * (-a) ≤ b - a := by
    refine (le_sub_iff_add_le).2 ?_
    calc
      (1 - σ) * (-a) + a = σ * a := by
        dsimp [a]
        ring
      _ ≤ b := h_curv_explicit
  have h_gap :
      (1 - σ) * (-a) ≤ inner ℝ diff (s k) := by
    simpa [diff, a, b, inner_sub_left] using h_gap'
  have h_norm_bound :
      (1 - σ) * (-a) ≤ ‖diff‖ * ‖s k‖ :=
    le_trans h_gap (real_inner_le_norm diff (s k))
  -- Divide by the positive search-direction norm and apply Cauchy-Schwarz.
  calc
    (1 - σ) * (-(inner ℝ (∇ f (x k)) (s k) / ‖s k‖))
        = (1 - σ) * ((-a) / ‖s k‖) := by
            rw [show inner ℝ (∇ f (x k)) (s k) = a by rfl, neg_div]
    _ = ((1 - σ) * (-a)) / ‖s k‖ := by rw [mul_div_assoc]
    _ ≤ (‖diff‖ * ‖s k‖) / ‖s k‖ := by
          exact div_le_div_of_nonneg_right h_norm_bound (le_of_lt hs_pos)
    _ = ‖diff‖ := by rw [mul_div_assoc, div_self hs_pos.ne', mul_one]
    _ = ‖∇ f (x (k + 1)) - ∇ f (x k)‖ := rfl

/-- Helper for Chapter02 Theorem 2.5.5: the normalized directional derivative tends to zero,
which is the textbook limit `(2.5.19)`. -/
lemma wolfePowellLineSearch_normalized_directionalDerivative_tendsto_zero
    (f : E → ℝ) (x s : ℕ → E) (α : ℕ → ℝ) (ρ σ : ℝ)
    (h_bddBelow : BddBelow (Set.range f))
    (h_hasGradient : ∀ y ∈ initialSublevelSet f (x 0), HasGradientAt f (∇ f y) y)
    (h_gradUniform : UniformContinuousOn (∇ f) (initialSublevelSet f (x 0)))
    (h_update : ∀ k, x (k + 1) = x k + α k • s k)
    (h_descent : ∀ k, inner ℝ (∇ f (x k)) (s k) < 0)
    (h_wolfeStep :
      ∀ k,
        WolfePowellCondition
          (lineSearchObjective f (x k) (s k))
          (deriv (lineSearchObjective f (x k) (s k)))
          ρ σ (α k)) :
    Tendsto (fun k : ℕ ↦ inner ℝ (∇ f (x k)) (s k) / ‖s k‖) atTop (nhds 0) := by
  have h_mem : ∀ k : ℕ, x k ∈ initialSublevelSet f (x 0) :=
    wolfePowell_iterates_mem_initialSublevelSet
      f x s α ρ σ h_hasGradient h_update h_descent h_wolfeStep
  have h_params : WolfePowellParameters ρ σ :=
    (wolfePowellCondition_iff.mp (h_wolfeStep 0)).1
  rcases wolfePowellParameters_iff.mp h_params with ⟨hρ_pos, _, hσ_lt_one⟩
  have h_drop_zero :
      Tendsto (fun k : ℕ ↦ f (x k) - f (x (k + 1))) atTop (nhds 0) :=
    wolfePowell_function_drop_tendsto_zero
      f x s α ρ σ h_bddBelow h_hasGradient h_update h_descent h_wolfeStep
  have h_negRatio :
      Tendsto (fun k : ℕ ↦ -(inner ℝ (∇ f (x k)) (s k) / ‖s k‖)) atTop (nhds 0) := by
    refine Metric.tendsto_atTop.2 ?_
    intro ε hε
    by_contra h_eventual
    have h_bad :
        ∀ N : ℕ,
          ∃ n, N ≤ n ∧
            ε ≤ dist (-(inner ℝ (∇ f (x n)) (s n) / ‖s n‖)) 0 := by
      intro N
      by_contra hN
      refine h_eventual ?_
      refine ⟨N, ?_⟩
      intro n hn
      by_contra hdist
      exact hN ⟨n, hn, le_of_not_gt hdist⟩
    have h_freq :
        ∃ᶠ n in atTop,
          ε ≤ dist (-(inner ℝ (∇ f (x n)) (s n) / ‖s n‖)) 0 :=
      (Filter.frequently_atTop).2 h_bad
    obtain ⟨φ, hφmono, hφbad⟩ := Filter.extraction_of_frequently_atTop h_freq
    have hφ_tendsto : Tendsto φ atTop atTop := hφmono.tendsto_atTop
    have h_bad_ratio :
        ∀ n : ℕ,
          ε ≤ -(inner ℝ (∇ f (x (φ n))) (s (φ n)) / ‖s (φ n)‖) := by
      intro n
      have hs_pos : 0 < ‖s (φ n)‖ := by
        refine norm_pos_iff.2 ?_
        intro hs_zero
        exact (lt_irrefl (0 : ℝ)) <| by simpa [hs_zero] using h_descent (φ n)
      have hbad_abs :
          ε ≤ |inner ℝ (∇ f (x (φ n))) (s (φ n))| / ‖s (φ n)‖ := by
        simpa [dist_eq_norm, Real.norm_eq_abs, abs_div] using hφbad n
      have hbad_rewrite :
          |inner ℝ (∇ f (x (φ n))) (s (φ n))| / ‖s (φ n)‖ =
            -(inner ℝ (∇ f (x (φ n))) (s (φ n)) / ‖s (φ n)‖) := by
        rw [abs_of_neg (h_descent (φ n)), neg_div]
      exact hbad_rewrite ▸ hbad_abs
    have h_drop_subseq :
        Tendsto (fun n : ℕ ↦ f (x (φ n)) - f (x (φ n + 1))) atTop (nhds 0) := by
      change Tendsto ((fun k : ℕ ↦ f (x k) - f (x (k + 1))) ∘ φ) atTop (nhds 0)
      exact h_drop_zero.comp hφ_tendsto
    have h_dist_subseq :
        Tendsto (fun n : ℕ ↦ dist (x (φ n)) (x (φ n + 1))) atTop (nhds 0) := by
      refine Metric.tendsto_atTop.2 ?_
      intro δ hδ
      have hρεδ_pos : 0 < (ρ * ε) * δ := mul_pos (mul_pos hρ_pos hε) hδ
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h_drop_subseq ((ρ * ε) * δ) hρεδ_pos
      refine ⟨N, ?_⟩
      intro n hn
      rcases wolfePowellCondition_iff.mp (h_wolfeStep (φ n)) with ⟨_, hα_pos, h_dec, _⟩
      have hs_pos : 0 < ‖s (φ n)‖ := by
        refine norm_pos_iff.2 ?_
        intro hs_zero
        exact (lt_irrefl (0 : ℝ)) <| by simpa [hs_zero] using h_descent (φ n)
      have h_drop_nonneg :
          0 ≤ f (x (φ n)) - f (x (φ n + 1)) := by
        exact sub_nonneg.mpr
          (wolfePowell_step_value_nonincrease
            f x s α ρ σ h_hasGradient h_update h_descent h_wolfeStep (φ n)
            (h_mem (φ n)))
      have h_small_drop :
          f (x (φ n)) - f (x (φ n + 1)) < (ρ * ε) * δ := by
        simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg h_drop_nonneg] using hN n hn
      have h_eps_inner :
          ε * ‖s (φ n)‖ ≤ -(inner ℝ (∇ f (x (φ n))) (s (φ n))) := by
        exact (le_div_iff₀ hs_pos).mp <| by simpa [neg_div] using h_bad_ratio n
      have h_step_gap :
          ρ * α (φ n) * (-(inner ℝ (∇ f (x (φ n))) (s (φ n)))) ≤
            f (x (φ n)) - f (x (φ n + 1)) := by
        have h_dec_explicit :
            f (x (φ n + 1)) ≤
              f (x (φ n)) + ρ * α (φ n) * inner ℝ (∇ f (x (φ n))) (s (φ n)) := by
          have h_deriv_zero :
              deriv (lineSearchObjective f (x (φ n)) (s (φ n))) 0 =
                inner ℝ (∇ f (x (φ n))) (s (φ n)) := by
            have h_grad_zero :
                HasGradientAt f (∇ f (x (φ n))) (x (φ n) + (0 : ℝ) • s (φ n)) := by
              simpa [zero_smul] using h_hasGradient (x (φ n)) (h_mem (φ n))
            simpa using
              h_grad_zero.deriv_lineSearchObjective_apply
                (x := x (φ n)) (d := s (φ n)) (t := 0)
          simpa [lineSearchObjective_apply, lineSearchObjective_zero, h_update (φ n), h_deriv_zero]
            using h_dec
        have h_aux :
            f (x (φ n + 1)) + ρ * α (φ n) * (-(inner ℝ (∇ f (x (φ n))) (s (φ n)))) ≤
              f (x (φ n)) := by
          calc
            f (x (φ n + 1)) + ρ * α (φ n) * (-(inner ℝ (∇ f (x (φ n))) (s (φ n)))) ≤
                f (x (φ n)) +
                  (ρ * α (φ n) * inner ℝ (∇ f (x (φ n))) (s (φ n)) +
                    ρ * α (φ n) * (-(inner ℝ (∇ f (x (φ n))) (s (φ n))))) := by
                  simpa [add_assoc, add_left_comm, add_comm] using
                    add_le_add_right h_dec_explicit
                      (ρ * α (φ n) * (-(inner ℝ (∇ f (x (φ n))) (s (φ n)))))
            _ = f (x (φ n)) := by ring
        exact (le_sub_iff_add_le).2 <| by simpa [add_comm, add_left_comm, add_assoc] using h_aux
      have h_scaled_gap :
          (ρ * ε) * (α (φ n) * ‖s (φ n)‖) ≤
            f (x (φ n)) - f (x (φ n + 1)) := by
        have h_scale_nonneg : 0 ≤ ρ * α (φ n) := le_of_lt (mul_pos hρ_pos hα_pos)
        have h_scaled :=
          mul_le_mul_of_nonneg_left h_eps_inner h_scale_nonneg
        have h_scaled' :
            (ρ * ε) * (α (φ n) * ‖s (φ n)‖) ≤
              ρ * α (φ n) * (-(inner ℝ (∇ f (x (φ n))) (s (φ n)))) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using h_scaled
        exact le_trans h_scaled' h_step_gap
      have h_step_size_small :
          α (φ n) * ‖s (φ n)‖ < δ := by
        have h_scaled_small :
            (ρ * ε) * (α (φ n) * ‖s (φ n)‖) < (ρ * ε) * δ :=
          lt_of_le_of_lt h_scaled_gap h_small_drop
        exact lt_of_mul_lt_mul_left h_scaled_small (le_of_lt (mul_pos hρ_pos hε))
      have hdist_eq :
          dist (x (φ n)) (x (φ n + 1)) = |α (φ n)| * ‖s (φ n)‖ := by
        rw [dist_comm, dist_eq_norm, h_update (φ n), add_sub_cancel_left, norm_smul,
          Real.norm_eq_abs]
      have hdist_eq' :
          dist (x (φ n)) (x (φ n + 1)) = α (φ n) * ‖s (φ n)‖ := by
        calc
          dist (x (φ n)) (x (φ n + 1)) = |α (φ n)| * ‖s (φ n)‖ := hdist_eq
          _ = α (φ n) * ‖s (φ n)‖ := by rw [abs_of_pos hα_pos]
      have h_step_size_small_abs : |α (φ n)| * ‖s (φ n)‖ < δ := by
        simpa [abs_of_pos hα_pos] using h_step_size_small
      simpa [hdist_eq] using h_step_size_small_abs
    have h_grad_diff_subseq :
        Tendsto
          (fun n : ℕ ↦ ∇ f (x (φ n + 1)) - ∇ f (x (φ n)))
          atTop
          (nhds 0) := by
      refine Metric.tendsto_atTop.2 ?_
      intro ε' hε'
      rcases (Metric.uniformContinuousOn_iff.mp h_gradUniform) ε' hε' with ⟨δ, hδ, hδ_spec⟩
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h_dist_subseq δ hδ
      refine ⟨N, ?_⟩
      intro n hn
      have hxφ :
          x (φ n) ∈ initialSublevelSet f (x 0) :=
        h_mem (φ n)
      have hxφ_succ :
          x (φ n + 1) ∈ initialSublevelSet f (x 0) :=
        h_mem (φ n + 1)
      have hdist_small : dist (x (φ n)) (x (φ n + 1)) < δ := by
        simpa [Real.dist_eq, abs_of_nonneg dist_nonneg] using hN n hn
      have h_grad_close :
          dist (∇ f (x (φ n + 1))) (∇ f (x (φ n))) < ε' :=
        hδ_spec (x (φ n + 1)) hxφ_succ (x (φ n)) hxφ (by simpa [dist_comm] using hdist_small)
      simpa [dist_eq_norm] using h_grad_close
    have h_norm_grad_diff_subseq :
        Tendsto
          (fun n : ℕ ↦ ‖∇ f (x (φ n + 1)) - ∇ f (x (φ n))‖)
          atTop
          (nhds 0) := by
      simpa using h_grad_diff_subseq.norm
    have h_one_minus_sigma_eps_pos : 0 < (1 - σ) * ε :=
      mul_pos (sub_pos.mpr hσ_lt_one) hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h_norm_grad_diff_subseq
      ((1 - σ) * ε) h_one_minus_sigma_eps_pos
    have h_lower_at_N :
        (1 - σ) * ε ≤ ‖∇ f (x (φ N + 1)) - ∇ f (x (φ N))‖ := by
      have h_curv_lower :=
        wolfePowell_curvature_difference_norm_lower_bound
          f x s α ρ σ h_hasGradient h_update h_descent h_wolfeStep (φ N)
      have h_scale_nonneg : 0 ≤ 1 - σ := le_of_lt (sub_pos.mpr hσ_lt_one)
      have h_bad_scaled := mul_le_mul_of_nonneg_left (h_bad_ratio N) h_scale_nonneg
      exact le_trans (by simpa [mul_assoc] using h_bad_scaled) h_curv_lower
    have h_upper_at_N :
        ‖∇ f (x (φ N + 1)) - ∇ f (x (φ N))‖ < (1 - σ) * ε := by
      simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hN N le_rfl
    exact (not_lt_of_ge h_lower_at_N) h_upper_at_N
  -- Route correction: prove the nonnegative contradiction form first, then negate it to recover
  -- the source-facing ratio `(2.5.19)`.
  simpa using h_negRatio.neg

/-- Chapter02 Theorem 2.5.5: let `f : E → ℝ` on a real Hilbert space `E` be bounded below, and
assume `∇ f y` is the genuine gradient of `f` at each `y` in the initial sublevel set
`initialSublevelSet f (x 0) = {y | f y ≤ f (x 0)}` and that `∇ f` is uniformly continuous there.
If the iterate sequence `x`, search directions `s`, and steplengths `α` satisfy the
Wolfe-Powell rule from Chapter02 Algorithm 2.5.3, then the source-facing cosine formulation
`‖∇ f (x k)‖ * cos θ k ⟶ 0`, written with
`θ k = InnerProductGeometry.angle (s k) (-∇ f (x k))`, holds. -/
theorem wolfePowellLineSearch_gradientNorm_mul_cos_angle_tendsto_zero
    (f : E → ℝ) (x s : ℕ → E) (α : ℕ → ℝ) (ρ σ : ℝ)
    (h_bddBelow : BddBelow (Set.range f))
    (h_hasGradient : ∀ y ∈ initialSublevelSet f (x 0), HasGradientAt f (∇ f y) y)
    (h_gradUniform : UniformContinuousOn (∇ f) (initialSublevelSet f (x 0)))
    (h_update : ∀ k, x (k + 1) = x k + α k • s k)
    (h_descent : ∀ k, inner ℝ (∇ f (x k)) (s k) < 0)
    (h_wolfeStep :
      ∀ k,
        WolfePowellCondition
          (lineSearchObjective f (x k) (s k))
          (deriv (lineSearchObjective f (x k) (s k)))
          ρ σ (α k)) :
    Tendsto
      (fun k : ℕ ↦
        ‖∇ f (x k)‖ * Real.cos (InnerProductGeometry.angle (s k) (-∇ f (x k))))
      atTop
      (nhds 0) := by
  have h_ratio :
      Tendsto (fun k : ℕ ↦ inner ℝ (∇ f (x k)) (s k) / ‖s k‖) atTop (nhds 0) :=
    wolfePowellLineSearch_normalized_directionalDerivative_tendsto_zero
      f x s α ρ σ h_bddBelow h_hasGradient h_gradUniform h_update h_descent h_wolfeStep
  -- Route correction: once the ratio form `(2.5.19)` is established, the cosine form `(2.5.20)`
  -- is just the chapter's inner-product/angle rewrite.
  simpa [gradientNorm_mul_cos_angle_searchDirection_negGradient_eq_neg_gradientInner_div_norm]
    using h_ratio.neg

/-- Derived reformulation of
`wolfePowellLineSearch_gradientNorm_mul_cos_angle_tendsto_zero`: under the same hypotheses,
the equivalent ratio view
`(inner ℝ (∇ f (x k)) (s k)) / ‖s k‖ ⟶ 0`
also holds. -/
theorem wolfePowellLineSearch_gradientInner_div_searchDirectionNorm_tendsto_zero
    (f : E → ℝ) (x s : ℕ → E) (α : ℕ → ℝ) (ρ σ : ℝ)
    (h_bddBelow : BddBelow (Set.range f))
    (h_hasGradient : ∀ y ∈ initialSublevelSet f (x 0), HasGradientAt f (∇ f y) y)
    (h_gradUniform : UniformContinuousOn (∇ f) (initialSublevelSet f (x 0)))
    (h_update : ∀ k, x (k + 1) = x k + α k • s k)
    (h_descent : ∀ k, inner ℝ (∇ f (x k)) (s k) < 0)
    (h_wolfeStep :
      ∀ k,
        WolfePowellCondition
          (lineSearchObjective f (x k) (s k))
          (deriv (lineSearchObjective f (x k) (s k)))
          ρ σ (α k)) :
    Tendsto (fun k : ℕ ↦ inner ℝ (∇ f (x k)) (s k) / ‖s k‖) atTop (nhds 0) := by
  have h_cos :
      Tendsto
        (fun k : ℕ ↦
          ‖∇ f (x k)‖ * Real.cos (InnerProductGeometry.angle (s k) (-∇ f (x k))))
        atTop
        (nhds 0) :=
    wolfePowellLineSearch_gradientNorm_mul_cos_angle_tendsto_zero
      f x s α ρ σ h_bddBelow h_hasGradient h_gradUniform h_update h_descent h_wolfeStep
  simpa [gradientNorm_mul_cos_angle_searchDirection_negGradient_eq_neg_gradientInner_div_norm]
    using h_cos.neg

end

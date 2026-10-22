/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap05.Lemma_5_7
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_68
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_69
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_72.StepsizeRules

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {f g ω : E → EReal} {Lf : NNReal}
variable [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
  [Fact (is_convex_function g)]

local notation "constantOrBacktrackingB5StepsizeRule[" hω "; " x "; " L "]" =>
  non_euclidean_proximal_gradient_constant_or_backtracking_B5_stepsize_rule
    (f := f) (g := g) (ω := ω) (Lf := Lf) hω x L

/- `lean_leansearch` was unavailable in this run, so the local Chapter 5 and Chapter 10 files
were used directly for API recall.

Definition 10.69 is a `source-facing` bridge in the non-Euclidean proximal-gradient section. The
source item does not introduce a new owner abstraction; it restates the shared quadratic
upper-model inequality at one iterate under the admissible constant-or-B5 stepsize regime. The
relevant domain owners already present in the project are:
- `uses_proximal_gradient_Lf_stepsize_rule` from Remark 10.19 for the constant branch;
- `UsesNonEuclideanProximalGradientBacktrackingB5Rule` from Algorithm 10.69 for the B5
  branch;
- `non_euclidean_proximal_gradient_constant_or_backtracking_B5_stepsize_rule` from Theorem 10.72
  as the source-facing Chapter 10 owner of that exact disjunction;
- `is_l_smooth_on_descent_lemma` from Lemma 5.7 for the smoothness-based derivation of the
  constant branch on the segment joining consecutive iterates.

Primitive data are the smoothness/domain hypotheses, the Bregman potential hypothesis, the
non-Euclidean trajectory, and the canonical Chapter 10 stepsize owner. The displayed quadratic
upper-model inequality is derived API, so this file should first bridge to the canonical owner
`non_euclidean_proximal_gradient_backtracking_B5_accepts` from Algorithm 10.69 instead of
keeping the expanded inequality as the primary owner-facing output. -/

omit [FiniteDimensional ℝ E] [IsProperExtendedRealFunction g]
  [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)] in
/-- Helper for Definition 10.69: every iterate of a non-Euclidean proximal-gradient trajectory
lies in `interior (effective_domain f)` once `effective_domain g` is contained there. -/
lemma non_euclidean_proximal_gradient_trajectory_mem_interior_effective_domain
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (k : ℕ) :
    x k ∈ interior (effective_domain f) := by
  exact
    hg_effective_domain_subset_interior_f_effective_domain
      (is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj k).1

/-- Helper for Definition 10.69: a real-valued descent estimate upgrades to the `EReal`
upper-model inequality once the current iterate lies in the finite domain and the next iterate
stays in `interior (effective_domain f)`. -/
lemma non_euclidean_upper_model_of_toReal_le
    {xk xNext : E} {Lk : PosReal}
    (hfxk : is_differentiable_at f xk)
    (hxNext : xNext ∈ interior (effective_domain f))
    (hdescent :
      (f xNext).toReal ≤
        (f xk).toReal +
          inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (xNext - xk) +
          ((Lk : ℝ) / 2) * ‖xNext - xk‖ ^ (2 : ℕ)) :
    f xNext ≤
      f xk +
        ((inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (xNext - xk) +
          ((Lk : ℝ) / 2) * ‖xNext - xk‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  -- Split on whether `f xNext` is `⊥`; only the finite-value branch needs the real lift.
  by_cases hxNext_bot : f xNext = ⊥
  · simp [hxNext_bot]
  · -- Both endpoint values are finite, so the real descent estimate can be cast back to `EReal`.
    have hxNext_eff : xNext ∈ effective_domain f := interior_subset hxNext
    have hxNext_val : f xNext = (((f xNext).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal (mem_effective_domain.mp hxNext_eff).ne hxNext_bot).symm
    have hdescent' :
        (f xNext).toReal ≤
          (f xk).toReal +
            (inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (xNext - xk) +
              ((Lk : ℝ) / 2) * ‖xNext - xk‖ ^ (2 : ℕ)) := by
      -- Normalize the real inequality into the parenthesized form expected by the `EReal` cast.
      simpa [add_assoc] using hdescent
    rw [hxNext_val, differentiable_at_value_eq_coe_toReal hfxk]
    exact_mod_cast hdescent'

/-- Bridge/view layer: under the standing smoothness and domain hypotheses, the canonical
constant-or-B5 stepsize owner implies that the chosen curvature estimate `L_k` satisfies the
canonical B5 acceptance predicate at iteration `k`. -/
theorem non_euclidean_proximal_gradient_constant_or_backtracking_B5_stepsize_accepts
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    [hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ)]
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (hrule : constantOrBacktrackingB5StepsizeRule[hω; x; L])
    (k : ℕ) :
    non_euclidean_proximal_gradient_backtracking_B5_accepts f g ω (L k) (x k) := by
  rcases hrule with hLf_rule | ⟨s, η, hB5⟩
  · -- In the constant-rule branch, the realized successor already satisfies the smooth upper model.
    have hdiff : is_differentiable_at f (x k) :=
      is_non_euclidean_proximal_gradient_trajectory_differentiable_at htraj k
    have hxk_int :
        x k ∈ interior (effective_domain f) :=
      non_euclidean_proximal_gradient_trajectory_mem_interior_effective_domain
        hg_effective_domain_subset_interior_f_effective_domain htraj k
    have hxk1_int :
        x (k + 1) ∈ interior (effective_domain f) :=
      non_euclidean_proximal_gradient_trajectory_mem_interior_effective_domain
        hg_effective_domain_subset_interior_f_effective_domain htraj (k + 1)
    have hdescent :
        (f (x (k + 1))).toReal ≤
          (f (x k)).toReal +
            inner ℝ (∇ (fun y ↦ (f y).toReal) (x k)) (x (k + 1) - x k) +
            ((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) := by
      -- Lemma 5.7 supplies the real-valued quadratic model on consecutive iterates.
      simpa [hLf_rule k, norm_sub_rev] using
        (is_l_smooth_on_descent_lemma
          hf_effective_domain_convex.interior
          hf_toReal_smooth_on_interior_effective_domain
          hxk_int
          hxk1_int)
    have hupper :
        f (x (k + 1)) ≤
          f (x k) +
            ((inner ℝ (∇ (fun y ↦ (f y).toReal) (x k)) (x (k + 1) - x k) +
              ((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) : ℝ) : EReal) :=
      non_euclidean_upper_model_of_toReal_le hdiff hxk1_int hdescent
    -- Repackage the realized successor into the canonical B5 acceptance predicate.
    refine (non_euclidean_proximal_gradient_backtracking_B5_accepts_iff f g ω (L k) (x k)).2 ?_
    exact ⟨x (k + 1), is_non_euclidean_proximal_gradient_trajectory_mem_step htraj k, hupper⟩
  · -- In the B5 branch, the owner already records acceptance at the chosen iterate and stepsize.
    simpa using UsesNonEuclideanProximalGradientBacktrackingB5Rule.accepts f g ω hB5 k

/-- Qualified domain companion for Definition 10.69: every admissible non-Euclidean
proximal-gradient step at `(xk, Lk)` stays in
`effective_domain g ∩ subdifferential_domain ω` once the current iterate does. -/
lemma non_euclidean_proximal_gradient_step_mem_domains
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (hqual : (intrinsicInterior ℝ (effective_domain g) ∩
      intrinsicInterior ℝ (effective_domain ω)).Nonempty)
    {xk xNext : E} {Lk : PosReal}
    (hxk : xk ∈ effective_domain g ∩ subdifferential_domain ω)
    (hstep : non_euclidean_proximal_gradient_step f g ω xk Lk xNext) :
    xNext ∈ effective_domain g ∩ subdifferential_domain ω := by
  have hxNext_scaled :
      xNext ∈ effective_domain g ∧
        IsMinOn (scaled_bregman_objective f g ω xk Lk) Set.univ xNext := by
    -- Convert the step owner into the canonical scaled-objective minimizer form.
    exact
      (non_euclidean_proximal_gradient_step_iff_mem_effective_domain_and_isMinOn_scaled_objective_univ
        (f := f) (g := g) (ω := ω) (xk := xk) (xNext := xNext) (Lk := Lk)
        hω hstep.differentiable_at hxk).mp hstep
  have hxNext_sub : xNext ∈ subdifferential_domain ω :=
    scaledBacktrackingAuxiliaryMinimizer_mem_subdifferentialDomain
      f g ω xk Lk hxk hqual hxNext_scaled.2
  exact ⟨hxNext_scaled.1, hxNext_sub⟩

/-- Definition 10.69: if `effective_domain f` is convex,
`effective_domain g ⊆ interior (effective_domain f)`, `(fun y ↦ (f y).toReal)` is `L_f`-smooth
on `interior (effective_domain f)`, and the
non-Euclidean proximal-gradient trajectory satisfies the canonical constant-or-B5 stepsize owner,
then at every iteration `k` the quadratic upper-model inequality
`f(x^(k+1)) ≤ f(x^k) + ⟪∇ f(x^k), x^(k+1) - x^k⟫ + (L_k / 2) ‖x^(k+1) - x^k‖²` holds. -/
theorem non_euclidean_proximal_gradient_upper_model_of_constant_or_backtracking_B5_rule
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (hrule : constantOrBacktrackingB5StepsizeRule[hω; x; L])
    (k : ℕ) :
    f (x (k + 1)) ≤
      f (x k) +
        ((inner ℝ (∇ (fun y ↦ (f y).toReal) (x k)) (x (k + 1) - x k) +
          ((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  rcases hrule with hLf_rule | ⟨s, η, hB5⟩
  · -- The constant-rule branch is the direct smoothness argument on consecutive iterates.
    have hdiff : is_differentiable_at f (x k) :=
      is_non_euclidean_proximal_gradient_trajectory_differentiable_at htraj k
    have hxk_int :
        x k ∈ interior (effective_domain f) :=
      non_euclidean_proximal_gradient_trajectory_mem_interior_effective_domain
        hg_effective_domain_subset_interior_f_effective_domain htraj k
    have hxk1_int :
        x (k + 1) ∈ interior (effective_domain f) :=
      non_euclidean_proximal_gradient_trajectory_mem_interior_effective_domain
        hg_effective_domain_subset_interior_f_effective_domain htraj (k + 1)
    have hdescent :
        (f (x (k + 1))).toReal ≤
          (f (x k)).toReal +
            inner ℝ (∇ (fun y ↦ (f y).toReal) (x k)) (x (k + 1) - x k) +
            ((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) := by
      -- Lemma 5.7 gives the real quadratic upper model on the segment between the iterates.
      simpa [hLf_rule k, norm_sub_rev] using
        (is_l_smooth_on_descent_lemma
          hf_effective_domain_convex.interior
          hf_toReal_smooth_on_interior_effective_domain
          hxk_int
          hxk1_int)
    exact non_euclidean_upper_model_of_toReal_le hdiff hxk1_int hdescent
  · -- Route correction: transport the accepted B5 witness to the realized successor by uniqueness.
    have hxk :
        x k ∈ effective_domain g ∩ subdifferential_domain ω :=
      is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj k
    have hdiff : is_differentiable_at f (x k) :=
      is_non_euclidean_proximal_gradient_trajectory_differentiable_at htraj k
    have hstepSucc :
        non_euclidean_proximal_gradient_step f g ω (x k) (L k) (x (k + 1)) :=
      is_non_euclidean_proximal_gradient_trajectory_mem_step htraj k
    have hxSucc :
        x (k + 1) ∈ effective_domain g ∩ subdifferential_domain ω :=
      is_non_euclidean_proximal_gradient_trajectory_mem_domains htraj (k + 1)
    have haccepts :
        non_euclidean_proximal_gradient_backtracking_B5_accepts f g ω (L k) (x k) :=
      UsesNonEuclideanProximalGradientBacktrackingB5Rule.accepts f g ω hB5 k
    rcases
        (non_euclidean_proximal_gradient_backtracking_B5_accepts_iff f g ω (L k) (x k)).1
          haccepts with
      ⟨xNext, hstepNext, hupperNext⟩
    have hxNext_eff : xNext ∈ effective_domain g :=
      hstepNext.mem_effective_domain hω hxk
    rcases
        existsUnique_non_euclidean_proximal_gradient_step_mem_effectiveDomain
          (f := f) (g := g) (ω := ω) (xk := x k) (Lk := L k) hxk hdiff with
      ⟨xStar, hxStar, huniqStar⟩
    have hxNext_eq : xNext = xStar := huniqStar xNext ⟨hstepNext, hxNext_eff⟩
    have hxSucc_eq : x (k + 1) = xStar := huniqStar (x (k + 1)) ⟨hstepSucc, hxSucc.1⟩
    have hupperStar :
        f xStar ≤
          f (x k) +
            ((inner ℝ (∇ (fun y ↦ (f y).toReal) (x k)) (xStar - x k) +
              ((L k : ℝ) / 2) * ‖xStar - x k‖ ^ (2 : ℕ) : ℝ) : EReal) := by
      -- First transport the accepted witness to the unique admissible step.
      simpa [hxNext_eq] using hupperNext
    -- Then rewrite the unique admissible step back to the realized successor.
    simpa [hxSucc_eq] using hupperStar

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {f g ω : E → EReal} {Lf : NNReal}
variable {XStar : Set E} {FOpt : ℝ}

namespace IsConvexCompositeSmoothMinimizationProblem

/-- Bridge/view layer: Assumption 10.77 specializes the primitive Definition 10.69 upper-model
theorem to the source-facing constant-or-B5 stepsize rule from Theorem 10.72. -/
theorem upper_model_of_constantOrBacktrackingB5Rule
    [hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf]
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_non_euclidean_proximal_gradient_trajectory f g ω x L)
    (hrule : hproblem.ConstantOrBacktrackingB5StepsizeRule hω x L)
    (k : ℕ) :
    f (x (k + 1)) ≤
      f (x k) +
        ((inner ℝ (∇ (fun y ↦ (f y).toReal) (x k)) (x (k + 1) - x k) +
          ((L k : ℝ) / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  -- The problem-class owner only repackages the primitive theorem with the canonical `g` data.
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  simpa [ConstantOrBacktrackingB5StepsizeRule] using
    non_euclidean_proximal_gradient_upper_model_of_constant_or_backtracking_B5_rule
      (f := f) (g := g) (ω := ω) (Lf := Lf)
      hproblem.f_effective_domain_convex
      hproblem.g_effective_domain_subset_interior_f_effective_domain
      hproblem.f_toReal_smooth_on_interior_effective_domain
      hω
      htraj
      hrule
      k

end IsConvexCompositeSmoothMinimizationProblem

end

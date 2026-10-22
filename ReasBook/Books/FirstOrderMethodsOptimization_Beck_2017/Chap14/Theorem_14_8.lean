/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_2
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_65
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_2
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_9
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_30
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_12
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Lemma_11_7
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_4
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Algorithm_14_8
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Algorithm_14_8.PairBridge
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Theorem_14_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Gradient Topology

section

variable {E1 : Type u} {E2 : Type u}
variable [NormedAddCommGroup E1] [NormedSpace ℝ E1]
variable [NormedAddCommGroup E2] [NormedSpace ℝ E2]

/- `prompt_add/` is absent in this workspace, so the owner review is done against the nearby
Chapter 11 recurrence lemmas, Algorithm 14.8, Lemma 14.4, and the Chapter 14 convex-rate owners.

Theorem 14.8 is `source-facing`: it gives the two-block `O(1 / k)` estimate for the objective gap
along the explicit block sequences `x₁^k` and `x₂^k` for the pair objective from
Algorithm 14.8. Domain sampling against the nearby Chapter 14 files identifies the relevant
owners:
- `two_block_alternating_minimization_objective` and
  `two_block_alternating_minimization_objective_blocks` from Algorithm 14.8 for the source-level
  objective `F(x₁, x₂) = f(x₁, x₂) + g₁(x₁) + g₂(x₂)`;
- `ConvexOn ℝ Set.univ f` from the nearby Chapter 14 rate files for the real-valued smooth term,
  together with the frozen-slice `is_l_smooth_on` assumptions from Lemma 14.4;
- `is_convex_function` only for the extended-real penalty terms `g₁` and `g₂`;
- `is_two_block_alternating_minimization_trajectory` from Algorithm 14.8 as the source-facing
  owner for the generated pair iterates, with
  `is_two_block_alternating_minimization_trajectory_toTrajectory` retained as the canonical bridge
  to `is_alternating_minimization_trajectory` on
  `two_block_alternating_minimization_block_iterate`, and with the reusable `Fin 2` bridge data
  imported from `Algorithm_14_8.PairBridge` for the companion API below to the canonical Chapter
  14 owner
  `IsAlternatingMinimizationConvexRateProblem`; and
- `nonnegative_sequence_le_max_geometric_or_sublinear_of_quadratic_step_recurrence` from
  Lemma 11.7 only as the proof-level scalar recurrence bridge.

Layer triage:
- `source-facing`: the theorem below, stated directly for the two-block objective and the
  Algorithm 14.8 trajectory including the textbook initialization clause for `x₂⁰`;
- `core/canonical`: the Algorithm 14.8 objective owner together with the Chapter 14
  block-vector trajectory owner and the canonical convexity owner `ConvexOn ℝ Set.univ f` for the
  smooth term;
- `bridge/view`: the explicit initial-domain witness together with
  `is_two_block_alternating_minimization_trajectory_toTrajectory`, and the scalar recurrence on the
  objective-gap sequence, both used internally rather than as public theorem inputs. -/

variable {f : E1 × E2 → ℝ} {g1 : E1 → EReal} {g2 : E2 → EReal}
variable {x1 : ℕ → E1} {x2 : ℕ → E2} {XStar : Set (E1 × E2)} {xStar : E1 × E2} {FOpt : ℝ}
variable {L1 L2 R : PosReal}

local notation "F" => two_block_alternating_minimization_objective f.toEReal g1 g2
local notation "x[" k "]" => (x1 k, x2 k)
local notation "φ₁" => twoBlockX1PartialInfimum f g1 g2
local notation "φ₂" => twoBlockX2PartialInfimum f g1 g2
local notation "η₁" => twoBlockX1InactiveMarginal f g2
local notation "η₂" => twoBlockX2InactiveMarginal f g1

/-- Source-facing two-block convex-rate owner: Assumption 14.12 together with the canonical
optimal-set and optimal-value data used by the Chapter 14 `O(1 / k)` rate theorem. -/
class IsTwoBlockAlternatingMinimizationConvexRateProblem
    (f : E1 × E2 → ℝ) (g1 : E1 → EReal) (g2 : E2 → EReal)
    (XStar : outParam (Set (E1 × E2))) (FOpt : outParam ℝ)
    (L1 : outParam PosReal) (L2 : outParam PosReal) : Prop where
  g1_proper : IsProperExtendedRealFunction g1
  g1_closed : LowerSemicontinuous g1
  g1_convex : is_convex_function g1
  g2_proper : IsProperExtendedRealFunction g2
  g2_closed : LowerSemicontinuous g2
  g2_convex : is_convex_function g2
  f_convex : ConvexOn ℝ Set.univ f
  f_x1_smooth :
    ∀ z2 : E2, is_l_smooth_on (fun y1 ↦ f (y1, z2)) Set.univ (PosReal.toNNReal L1)
  f_x2_smooth :
    ∀ z1 : E1, is_l_smooth_on (fun y2 ↦ f (z1, y2)) Set.univ (PosReal.toNNReal L2)
  optimal_set_eq :
    XStar = unconstrained_problem_solutions
      (two_block_alternating_minimization_objective f.toEReal g1 g2)
  optimal_set_nonempty : XStar.Nonempty
  optimal_value_isGLB :
    IsGLB (Set.range (two_block_alternating_minimization_objective f.toEReal g1 g2))
      (FOpt : EReal)
  bounded_sublevel_distance_to_each_optimal_point (α : PosReal) :
    ∃ Rα : PosReal, ∀ {y xStar : E1 × E2},
      two_block_alternating_minimization_objective f.toEReal g1 g2 y ≤ ((α : ℝ) : EReal) →
      xStar ∈ XStar →
      ‖y - xStar‖ ≤ (Rα : ℝ)

namespace TwoBlockConvexRate

open Metric

variable {f : E1 × E2 → ℝ} {g1 : E1 → EReal} {g2 : E2 → EReal}
variable {XStar : Set (E1 × E2)} {FOpt : ℝ} {L1 L2 : PosReal}

/-- Assumption 14.12 exports the canonical Chapter 14 convex-rate owner on the `Fin 2`
block-vector view from Algorithm 14.8. This is a companion bridge, not a replacement for the
source-facing pair owner. -/
theorem toIsAlternatingMinimizationConvexRateProblem
    (h : IsTwoBlockAlternatingMinimizationConvexRateProblem f g1 g2 XStar FOpt L1 L2)
    (hfull_smooth :
      is_l_smooth_on
        (twoBlockAlternatingMinimizationSmoothTerm f)
        Set.univ
        (twoBlockAlternatingMinimizationGlobalSmoothness L1 L2)) :
    IsAlternatingMinimizationConvexRateProblem
      (twoBlockAlternatingMinimizationSmoothTerm f)
      (twoBlockAlternatingMinimizationPenalties g1 g2)
      (twoBlockAlternatingMinimizationOptimalSet XStar)
      FOpt
      (twoBlockAlternatingMinimizationGlobalSmoothness L1 L2) := by
  let pairLinear :
      ((i : Fin 2) → two_block_alternating_minimization_space E1 E2 i) →ₗ[ℝ] E1 × E2 :=
    { toFun := fun x ↦ (x 0, x 1)
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro a x
        rfl }
  have hobjective_eq :
      ∀ z : ((i : Fin 2) → two_block_alternating_minimization_space E1 E2 i),
        composite_model_objective
            (twoBlockAlternatingMinimizationSmoothTerm f).toEReal
            (separableSum (twoBlockAlternatingMinimizationPenalties g1 g2))
            z =
          two_block_alternating_minimization_objective f.toEReal g1 g2 (z 0, z 1) := by
    intro z
    -- Normalize the canonical `Fin 2` composite objective back to the source-facing pair objective.
    simp [composite_model_objective, twoBlockAlternatingMinimizationSmoothTerm,
      twoBlockAlternatingMinimizationPenalties, separableSum]
    have hcase :
        Fin.cases g1 (fun _ ↦ g2) (1 : Fin 2) (z 1) = g2 (z 1) := by
      change g2 (z 1) = g2 (z 1)
      rfl
    rw [hcase]
    ac_rfl
  have hnorm_eq :
      ∀ x y : ((i : Fin 2) → two_block_alternating_minimization_space E1 E2 i),
        ‖x - y‖ = ‖((x 0, x 1) : E1 × E2) - ((y 0, y 1) : E1 × E2)‖ := by
    intro x y
    -- On two coordinates, the `Fin 2` sup norm is exactly the product max norm.
    rw [Pi.norm_def, Prod.norm_def]
    simp only [Pi.sub_apply, Prod.mk_sub_mk]
    have hsup :
        Finset.univ.sup (fun b : Fin 2 ↦ ‖x b - y b‖₊) =
          max ‖x 0 - y 0‖₊ ‖x 1 - y 1‖₊ := by
      refine le_antisymm (Finset.sup_le ?_) ?_
      · intro b hb
        fin_cases b
        · exact le_max_left _ _
        · exact le_max_right _ _
      · refine max_le ?_ ?_
        · exact
            Finset.le_sup
              (s := Finset.univ)
              (f := fun b : Fin 2 ↦ ‖x b - y b‖₊)
              (by simp)
        · exact
            Finset.le_sup
              (s := Finset.univ)
              (f := fun b : Fin 2 ↦ ‖x b - y b‖₊)
              (by simp)
    calc
      ↑(Finset.univ.sup (fun b : Fin 2 ↦ ‖x b - y b‖₊)) =
          ↑(max ‖x 0 - y 0‖₊ ‖x 1 - y 1‖₊) := by
            exact congrArg (fun t : NNReal ↦ (t : ℝ)) hsup
      _ = max ‖x 0 - y 0‖ ‖x 1 - y 1‖ := rfl
  refine
    { g_proper := by
        -- Build the aggregate `Fin 2` penalty owner from the two source-facing block penalties.
        refine separableSum_proper (twoBlockAlternatingMinimizationPenalties g1 g2) ?_
        intro i
        fin_cases i
        · simpa [twoBlockAlternatingMinimizationPenalties] using h.g1_proper
        · simpa [twoBlockAlternatingMinimizationPenalties] using h.g2_proper
      g_closed := by
        -- The same blockwise packaging yields lower semicontinuity of the separable sum.
        refine separableSum_closed (twoBlockAlternatingMinimizationPenalties g1 g2) ?_
        intro i
        fin_cases i
        · simpa [twoBlockAlternatingMinimizationPenalties] using h.g1_closed
        · simpa [twoBlockAlternatingMinimizationPenalties] using h.g2_closed
      g_convex := by
        -- Convexity of the aggregate penalty is inherited coordinatewise from `g₁` and `g₂`.
        refine
          separableSum_convex
            (twoBlockAlternatingMinimizationPenalties g1 g2)
            (fun i ↦ ?_)
            (fun i ↦ ?_)
        · fin_cases i
          · simpa [twoBlockAlternatingMinimizationPenalties] using h.g1_proper
          · simpa [twoBlockAlternatingMinimizationPenalties] using h.g2_proper
        · fin_cases i
          · simpa [twoBlockAlternatingMinimizationPenalties] using h.g1_convex
          · simpa [twoBlockAlternatingMinimizationPenalties] using h.g2_convex
      f_convex := by
        -- Transport convexity of the pair smooth term along the coordinate projection map.
        simpa [twoBlockAlternatingMinimizationSmoothTerm, Function.comp, pairLinear] using
          h.f_convex.comp_linearMap pairLinear
      f_smooth := hfull_smooth
      optimal_set_eq := by
        ext z
        change
          (z 0, z 1) ∈ XStar ↔
            z ∈
              unconstrained_problem_solutions
                (composite_model_objective
                  (twoBlockAlternatingMinimizationSmoothTerm f).toEReal
                  (separableSum (twoBlockAlternatingMinimizationPenalties g1 g2)))
        constructor
        · intro hz
          have hz_pair :
              (z 0, z 1) ∈
                unconstrained_problem_solutions
                  (two_block_alternating_minimization_objective f.toEReal g1 g2) := by
            simpa [h.optimal_set_eq] using hz
          refine (mem_unconstrained_problem_solutions_iff_forall_le).2 ?_
          intro w
          -- Compare every block vector by translating both objectives back to the pair view.
          simpa [hobjective_eq] using
            (mem_unconstrained_problem_solutions_iff_forall_le.mp hz_pair) (w 0, w 1)
        · intro hz
          have hz_pair :
              (z 0, z 1) ∈
                unconstrained_problem_solutions
                  (two_block_alternating_minimization_objective f.toEReal g1 g2) := by
            refine (mem_unconstrained_problem_solutions_iff_forall_le).2 ?_
            intro y
            -- Repackage every pair candidate as the canonical `Fin 2` state.
            simpa [hobjective_eq] using
              (mem_unconstrained_problem_solutions_iff_forall_le.mp hz)
                (two_block_alternating_minimization_state y.1 y.2)
          simpa [h.optimal_set_eq] using hz_pair
      optimal_set_nonempty := by
        rcases h.optimal_set_nonempty with ⟨xStar, hxStar⟩
        -- Lift any optimal pair to its canonical block-vector state.
        refine ⟨two_block_alternating_minimization_state xStar.1 xStar.2, ?_⟩
        simpa [twoBlockAlternatingMinimizationOptimalSet] using hxStar
      optimal_value_isGLB := by
        constructor
        · rintro _ ⟨z, rfl⟩
          -- Lower bounds transfer immediately through the objective normalization lemma.
          calc
            (FOpt : EReal)
                ≤ two_block_alternating_minimization_objective f.toEReal g1 g2 (z 0, z 1) :=
                  h.optimal_value_isGLB.1 ⟨(z 0, z 1), rfl⟩
            _ =
                composite_model_objective
                  (twoBlockAlternatingMinimizationSmoothTerm f).toEReal
                  (separableSum (twoBlockAlternatingMinimizationPenalties g1 g2))
                  z :=
              (hobjective_eq z).symm
        · intro b hb
          -- Every pair value is realized by its canonical `Fin 2` state, so any lower bound on the
          -- block-vector range is also a lower bound on the pair range.
          exact h.optimal_value_isGLB.2 <| by
            rintro _ ⟨y, rfl⟩
            simpa [hobjective_eq] using
              hb ⟨two_block_alternating_minimization_state y.1 y.2, rfl⟩
      bounded_sublevel_distance_to_each_optimal_point := by
        intro α
        rcases h.bounded_sublevel_distance_to_each_optimal_point α with ⟨Rα, hRα⟩
        refine ⟨Rα, ?_⟩
        intro x xStar hx hxStar
        have hx_pair :
            two_block_alternating_minimization_objective f.toEReal g1 g2 (x 0, x 1) ≤
              ((α : ℝ) : EReal) := by
          simpa [hobjective_eq] using hx
        have hxStar_pair : (xStar 0, xStar 1) ∈ XStar := by
          simpa [twoBlockAlternatingMinimizationOptimalSet] using hxStar
        -- Reuse the source-facing pair radius and then identify the two equivalent norms.
        calc
          ‖x - xStar‖ = ‖((x 0, x 1) : E1 × E2) - ((xStar 0, xStar 1) : E1 × E2)‖ :=
            hnorm_eq x xStar
          _ ≤ (Rα : ℝ) := hRα hx_pair hxStar_pair }

/-- Assumption 14.12 makes the canonical `Fin 2` Chapter 14 convex-rate owner available through
typeclass search. -/
instance
    instIsAlternatingMinimizationConvexRateProblemOfIsTwoBlockProblem
    [h : IsTwoBlockAlternatingMinimizationConvexRateProblem f g1 g2 XStar FOpt L1 L2]
    [hfull_smooth : Fact
      (is_l_smooth_on
        (twoBlockAlternatingMinimizationSmoothTerm f)
        Set.univ
        (twoBlockAlternatingMinimizationGlobalSmoothness L1 L2))] :
    IsAlternatingMinimizationConvexRateProblem
      (twoBlockAlternatingMinimizationSmoothTerm f)
      (twoBlockAlternatingMinimizationPenalties g1 g2)
      (twoBlockAlternatingMinimizationOptimalSet XStar)
      FOpt
      (twoBlockAlternatingMinimizationGlobalSmoothness L1 L2) :=
  TwoBlockConvexRate.toIsAlternatingMinimizationConvexRateProblem h hfull_smooth.1

attribute [instance] IsTwoBlockAlternatingMinimizationConvexRateProblem.g1_proper

attribute [instance] IsTwoBlockAlternatingMinimizationConvexRateProblem.g2_proper

/-- The source-facing pairwise sublevel-radius clause in Assumption 14.12 implies the weaker
distance-to-optimal-set estimate used elsewhere in the Chapter 14 rate analysis. -/
theorem bounded_sublevel_distance_to_optimal_set
    (h : IsTwoBlockAlternatingMinimizationConvexRateProblem f g1 g2 XStar FOpt L1 L2)
    (α : PosReal) :
    ∃ Rα : PosReal,
      ∀ ⦃y : E1 × E2⦄,
        two_block_alternating_minimization_objective f.toEReal g1 g2 y ≤ ((α : ℝ) : EReal) →
        infDist y XStar ≤ Rα := by
  rcases h.bounded_sublevel_distance_to_each_optimal_point α with ⟨Rα, hRα⟩
  refine ⟨Rα, ?_⟩
  intro y hy
  rcases h.optimal_set_nonempty with ⟨xStar, hxStar⟩
  refine (infDist_le_dist_of_mem hxStar).trans ?_
  simpa [dist_eq_norm] using hRα hy hxStar

/-- The source-facing pairwise sublevel-radius clause in Assumption 14.12 yields a radius that
controls the whole initial sublevel set `{y | F y ≤ F x0}`. -/
theorem bounded_initial_sublevel_distance_to_each_optimal_point
    (h : IsTwoBlockAlternatingMinimizationConvexRateProblem f g1 g2 XStar FOpt L1 L2)
    {x0 : E1 × E2} {α : PosReal}
    (hx0 :
      two_block_alternating_minimization_objective f.toEReal g1 g2 x0 ≤ ((α : ℝ) : EReal)) :
    ∃ Rα : PosReal,
      ∀ {y xStar : E1 × E2},
        two_block_alternating_minimization_objective f.toEReal g1 g2 y ≤
          two_block_alternating_minimization_objective f.toEReal g1 g2 x0 →
        xStar ∈ XStar →
        ‖y - xStar‖ ≤ (Rα : ℝ) := by
  -- Any point below `F x0` is also below the positive level `α`.
  rcases h.bounded_sublevel_distance_to_each_optimal_point α with ⟨Rα, hRα⟩
  refine ⟨Rα, ?_⟩
  intro y xStar hy hxStar
  exact hRα (hy.trans hx0) hxStar

/-- If the initial objective value is bounded by a positive level `α`, then the same Assumption
14.12 radius controls the whole initial sublevel set in the weaker distance-to-optimal-set form
used by later convergence arguments. -/
theorem bounded_initial_sublevel_distance_to_optimal_set
    (h : IsTwoBlockAlternatingMinimizationConvexRateProblem f g1 g2 XStar FOpt L1 L2)
    {x0 : E1 × E2} {α : PosReal}
    (hx0 :
      two_block_alternating_minimization_objective f.toEReal g1 g2 x0 ≤ ((α : ℝ) : EReal)) :
    ∃ Rα : PosReal,
      ∀ ⦃y : E1 × E2⦄,
        two_block_alternating_minimization_objective f.toEReal g1 g2 y ≤
          two_block_alternating_minimization_objective f.toEReal g1 g2 x0 →
        infDist y XStar ≤ Rα := by
  rcases TwoBlockConvexRate.bounded_sublevel_distance_to_optimal_set h α with ⟨Rα, hRα⟩
  refine ⟨Rα, ?_⟩
  intro y hy
  exact hRα (hy.trans hx0)

end TwoBlockConvexRate

-- Proof sketch: set
-- `a k = (F x[k]).toReal - FOpt` and use the source-facing Algorithm 14.8 trajectory
-- hypothesis together with the extra initial-domain bridge `hx0 : x[0] ∈ effective_domain F` to
-- obtain the canonical block-vector trajectory via
-- `is_two_block_alternating_minimization_trajectory_toTrajectory`. Then derive the needed slice
-- convexity and full-objective convexity data from the canonical convexity owner
-- `ConvexOn ℝ Set.univ f`, the penalty regularity, the frozen-slice smoothness assumptions, and
-- the initial-sublevel-radius hypothesis to prove the Chapter 14 quadratic recurrence
-- `a k - a (k + 1) ≥ (1 / γ) * a (k + 1)^2`
-- `γ = 2 * min (L₁, L₂) * R^2`. The stated quadratic recurrence is then
-- `nonnegative_sequence_le_max_geometric_or_sublinear_of_quadratic_step_recurrence`
-- yields
-- `a k ≤ max {((1 / 2)^((k - 1) / 2)) * a 0, 4γ / (k - 1)}` for every `k ≥ 2`. Since
-- `4γ = 8 * min (L₁, L₂) * R^2`, this is exactly the displayed estimate.
/-- Helper for Theorem 14.8: a convex differentiable real-valued function on the whole Banach
space satisfies the first-order support inequality in `fderiv` form. -/
lemma convex_real_support_univ_fderiv
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℝ} {x y : E}
    (hφ_convex : ConvexOn ℝ Set.univ φ)
    (hφ_diff : DifferentiableAt ℝ φ x) :
    φ y ≥ φ x + fderiv ℝ φ x (y - x) := by
  let line : ℝ → E := AffineMap.lineMap x y
  let ψ : ℝ → ℝ := fun t ↦ φ (line t)
  have hψ_convex : ConvexOn ℝ Set.univ ψ := by
    -- Restrict the ambient convex function to the affine line from `x` to `y`.
    simpa [ψ, line] using
      hφ_convex.comp_affineMap (AffineMap.lineMap x y)
  have hψ_deriv : HasDerivAt ψ (fderiv ℝ φ x (y - x)) 0 := by
    -- Differentiate the line restriction at the base point and identify the direction `y - x`.
    have hbase : HasFDerivAt φ (fderiv ℝ φ x) (line 0) := by
      simpa [line] using hφ_diff.hasFDerivAt
    have hline : HasDerivAt line (y - x) 0 := by
      simpa [line] using
        (show HasDerivAt (AffineMap.lineMap x y) (y - x) (0 : ℝ) from
          AffineMap.hasDerivAt_lineMap)
    simpa [ψ, line] using HasFDerivAt.comp_hasDerivAt 0 hbase hline
  have hsecant :
      fderiv ℝ φ x (y - x) ≤ slope ψ 0 1 := by
    -- Convexity bounds the derivative at the left endpoint by the secant slope.
    exact hψ_convex.le_slope_of_hasDerivAt (by simp) (by simp) zero_lt_one hψ_deriv
  have hsecant' :
      fderiv ℝ φ x (y - x) ≤ φ y - φ x := by
    simpa [ψ, line, slope] using hsecant
  linarith

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: the current second block is always an exact minimizer of the current
`x₂`-subproblem, with the `k = 0` case coming from the initialization clause. -/
lemma two_block_current_x2_objective_is_min_on
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (n : ℕ) :
    IsMinOn
      (two_block_alternating_minimization_x2_objective f.toEReal g1 g2 (x1 n))
      Set.univ
      (x2 n) := by
  -- Split off the initialization case from the recursive update case.
  cases n with
  | zero =>
      simpa using htraj.initial
  | succ n =>
      simpa [Nat.succ_eq_add_one] using htraj.step_x2 n

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: every outer iterate stays in the effective domain of `F`, and the
objective never exceeds its initial value. -/
lemma two_block_iterates_mem_effective_domain_and_initial_sublevel
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F) :
    ∀ n : ℕ, x[n] ∈ effective_domain F ∧ F x[n] ≤ F x[0] := by
  intro n
  induction n with
  | zero =>
      -- The initial pair is finite by hypothesis, and its value equals itself.
      exact ⟨hx0, le_rfl⟩
  | succ n ihn =>
      let xHalf := two_block_alternating_minimization_half_step x1 x2 n
      have hhalf_le : F xHalf ≤ F x[n] := by
        -- Compare the exact `x₁`-update against the old first block on the frozen `x₂^n` slice.
        have hmin := (isMinOn_iff.mp (htraj.step_x1 n)) (x1 n) (by simp)
        simpa [xHalf, two_block_alternating_minimization_half_step] using hmin
      have hhalf_mem : xHalf ∈ effective_domain F := by
        -- Finite descent from the current iterate keeps the half-step finite.
        refine mem_effective_domain.mpr ?_
        exact lt_of_le_of_lt hhalf_le (mem_effective_domain.mp ihn.1)
      have hnext_le_half : F x[n + 1] ≤ F xHalf := by
        -- Compare the exact `x₂`-update against the old second block on the frozen `x₁^{n+1}`
        -- slice.
        have hmin := (isMinOn_iff.mp (htraj.step_x2 n)) (x2 n) (by simp)
        simpa [xHalf, two_block_alternating_minimization_half_step] using hmin
      have hnext_mem : x[n + 1] ∈ effective_domain F := by
        -- The next iterate inherits finiteness from the half-step it improves.
        refine mem_effective_domain.mpr ?_
        exact lt_of_le_of_lt hnext_le_half (mem_effective_domain.mp hhalf_mem)
      have hnext_le_zero : F x[n + 1] ≤ F x[0] := by
        exact le_trans hnext_le_half (le_trans hhalf_le ihn.2)
      exact ⟨hnext_mem, hnext_le_zero⟩

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: each half-step also stays in the effective domain and in the initial
sublevel set. -/
lemma two_block_half_step_mem_effective_domain_and_initial_sublevel
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F)
    (n : ℕ) :
    two_block_alternating_minimization_half_step x1 x2 n ∈ effective_domain F ∧
      F (two_block_alternating_minimization_half_step x1 x2 n) ≤ F x[0] := by
  let xHalf := two_block_alternating_minimization_half_step x1 x2 n
  have hiter :=
    two_block_iterates_mem_effective_domain_and_initial_sublevel
      htraj hx0 n
  have hhalf_le : F xHalf ≤ F x[n] := by
    -- The exact first-block minimizer cannot exceed the old first block value on the same slice.
    have hmin := (isMinOn_iff.mp (htraj.step_x1 n)) (x1 n) (by simp)
    simpa [xHalf, two_block_alternating_minimization_half_step] using hmin
  have hhalf_mem : xHalf ∈ effective_domain F := by
    -- Finite descent from the current iterate keeps the half-step finite.
    refine mem_effective_domain.mpr ?_
    exact lt_of_le_of_lt hhalf_le (mem_effective_domain.mp hiter.1)
  have hhalf_le_zero : F xHalf ≤ F x[0] := by
    exact le_trans hhalf_le hiter.2
  exact ⟨hhalf_mem, hhalf_le_zero⟩

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: every iterate objective gap is nonnegative because each iterate is
finite and `xStar` globally minimizes `F`. -/
lemma two_block_objective_gap_nonneg
    [hg1_proper : IsProperExtendedRealFunction g1]
    [hg2_proper : IsProperExtendedRealFunction g2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hxStar : IsMinOn F Set.univ xStar)
    (hFOpt : F xStar = (FOpt : EReal))
    (hx0 : x[0] ∈ effective_domain F)
    (n : ℕ) :
    0 ≤ (F x[n]).toReal - FOpt := by
  have hiter :=
    two_block_iterates_mem_effective_domain_and_initial_sublevel
      htraj hx0 n
  have hFx_bot : F x[n] ≠ ⊥ := by
    -- The smooth term is real-valued, and the proper penalties never take the value `-∞`.
    rw [two_block_alternating_minimization_objective_apply, EReal.add_ne_bot_iff,
      EReal.add_ne_bot_iff]
    exact ⟨⟨by simp [Function.toEReal], hg1_proper.ne_bot (x1 n)⟩, hg2_proper.ne_bot (x2 n)⟩
  have hFx_coe :
      (((F x[n]).toReal : ℝ) : EReal) = F x[n] := by
    exact EReal.coe_toReal (mem_effective_domain.mp hiter.1).ne hFx_bot
  have hlowerE : (FOpt : EReal) ≤ F x[n] := by
    -- Compare the global minimizer `xStar` against the current iterate.
    have hmin := (isMinOn_iff.mp hxStar) x[n] (by simp)
    simpa [hFOpt] using hmin
  have hlowerE' : (FOpt : EReal) ≤ (((F x[n]).toReal : ℝ) : EReal) := by
    rwa [← hFx_coe] at hlowerE
  have hlower : FOpt ≤ (F x[n]).toReal := by
    exact_mod_cast hlowerE'
  linarith

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: the source proof reduces the theorem to a Chapter 14 quadratic
recurrence and then to the Chapter 11 scalar recurrence estimate. -/
lemma two_block_objective_gap_le_of_quadratic_recurrence
    (γ : PosReal)
    (hγ :
      4 * (γ : ℝ) ≤ 8 * min (L1 : ℝ) (L2 : ℝ) * ((R : ℝ) ^ (2 : ℕ)))
    (ha_nonneg : ∀ n : ℕ, 0 ≤ (F x[n]).toReal - FOpt)
    (hstep :
      ∀ n : ℕ,
        ((F x[n]).toReal - FOpt) - ((F x[n + 1]).toReal - FOpt) ≥
          (1 / (γ : ℝ)) * (((F x[n + 1]).toReal - FOpt) ^ (2 : ℕ)))
    (k : ℕ) (hk : 2 ≤ k) :
    (F x[k]).toReal - FOpt ≤
      max
        (((1 / 2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) *
          ((F x[0]).toReal - FOpt))
        ((8 * min (L1 : ℝ) (L2 : ℝ) * ((R : ℝ) ^ (2 : ℕ))) / ((k - 1 : ℕ) : ℝ)) := by
  -- Apply Lemma 11.7 directly to the two-block objective-gap sequence.
  have hmain :=
    _root_.nonnegative_sequence_le_max_geometric_or_sublinear_of_quadratic_step_recurrence
      ha_nonneg
      hstep
      hk
  -- Then enlarge the sublinear branch using the coefficient comparison `hγ`.
  have hsub :
      4 * (γ : ℝ) / ((k - 1 : ℕ) : ℝ) ≤
        (8 * min (L1 : ℝ) (L2 : ℝ) * ((R : ℝ) ^ (2 : ℕ))) / ((k - 1 : ℕ) : ℝ) := by
    exact div_le_div_of_nonneg_right hγ (by positivity)
  exact hmain.trans (max_le_max le_rfl hsub)

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: properness of the penalty terms rules out the value `-∞` for the
two-block objective at every point. -/
lemma two_block_objective_ne_bot
    [hg1_proper : IsProperExtendedRealFunction g1]
    [hg2_proper : IsProperExtendedRealFunction g2]
    (y : E1 × E2) :
    F y ≠ ⊥ := by
  rcases y with ⟨y1, y2⟩
  -- The smooth term is real-valued, and proper penalties never attain `-∞`.
  rw [two_block_alternating_minimization_objective_apply, EReal.add_ne_bot_iff,
    EReal.add_ne_bot_iff]
  exact ⟨⟨by simp [Function.toEReal], hg1_proper.ne_bot y1⟩, hg2_proper.ne_bot y2⟩

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: on the effective domain, the objective is exactly the coercion of its
real value. -/
lemma two_block_objective_eq_coe_toReal_of_mem_effective_domain
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    {y : E1 × E2} (hy : y ∈ effective_domain F) :
    (((F y).toReal : ℝ) : EReal) = F y := by
  -- Combine effective-domain finiteness with the global non-`⊥` fact.
  exact
    EReal.coe_toReal
      (mem_effective_domain.mp hy).ne
      (two_block_objective_ne_bot y)

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: the optimal pair attains the finite value `FOpt`, so it lies in the
effective domain of `F`. -/
lemma two_block_optimal_point_mem_effective_domain
    (hFOpt : F xStar = (FOpt : EReal)) :
    xStar ∈ effective_domain F := by
  -- Rewrite the optimal value through the finite real coercion `FOpt`.
  refine mem_effective_domain.mpr ?_
  simp [hFOpt]

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: the exact second-block update makes the next objective gap no larger
than the half-step objective gap. -/
lemma two_block_next_iterate_objective_gap_le_half_step_gap
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F)
    (n : ℕ) :
    (F x[n + 1]).toReal - FOpt ≤
      (F (two_block_alternating_minimization_half_step x1 x2 n)).toReal - FOpt := by
  let xHalf := two_block_alternating_minimization_half_step x1 x2 n
  have hhalf :=
    two_block_half_step_mem_effective_domain_and_initial_sublevel
      htraj hx0 n
  have hnext_le_half : F x[n + 1] ≤ F xHalf := by
    -- Compare the exact `x₂`-update against the previous second block on the frozen half-step
    -- slice.
    have hmin := (isMinOn_iff.mp (htraj.step_x2 n)) (x2 n) (by simp)
    simpa [xHalf, two_block_alternating_minimization_half_step] using hmin
  have hnext_real_le_half_real :
      (F x[n + 1]).toReal ≤ (F xHalf).toReal := by
    -- Convert the EReal descent inequality to a real inequality using finiteness of the
    -- half-step objective and global non-`⊥` for the current iterate.
    exact
      EReal.toReal_le_toReal
        hnext_le_half
        (two_block_objective_ne_bot x[n + 1])
        (mem_effective_domain.mp hhalf.1).ne
  linarith

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: exact minimization of the current second-block slice identifies the
first-block partial infimum at `x₁^n` with the current objective value. -/
lemma two_block_x1_partial_infimum_eq_current_value
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (n : ℕ) :
    φ₁ (x1 n) = F x[n] := by
  change sInf (Set.range (fun z2 : E2 ↦ F (x1 n, z2))) = F x[n]
  have hmin :
      IsMinOn
        (two_block_alternating_minimization_x2_objective f.toEReal g1 g2 (x1 n))
        Set.univ
        (x2 n) :=
    two_block_current_x2_objective_is_min_on
      htraj n
  apply le_antisymm
  · -- The current second block supplies one witness in the fiber defining `phi1`.
    exact sInf_le ⟨x2 n, by simp⟩
  · -- Exact `x₂`-minimality shows that every other fiber value lies above `F x[n]`.
    refine le_sInf ?_
    rintro _ ⟨z2, rfl⟩
    simpa using (isMinOn_iff.mp hmin) z2 (by simp)

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: the same first-block partial infimum equals the optimal value at
`xStar.1`. -/
lemma two_block_x1_partial_infimum_eq_optimal_value
    (hxStar : IsMinOn F Set.univ xStar)
    (hFOpt : F xStar = (FOpt : EReal)) :
    φ₁ xStar.1 = (FOpt : EReal) := by
  change sInf (Set.range (fun z2 : E2 ↦ F (xStar.1, z2))) = (FOpt : EReal)
  apply le_antisymm
  · -- The optimal pair contributes the witness `xStar.2` in the fiber over `xStar.1`.
    calc
      sInf (Set.range (fun z2 : E2 ↦ F (xStar.1, z2))) ≤ F (xStar.1, xStar.2) := by
        exact sInf_le ⟨xStar.2, by simp⟩
      _ = (FOpt : EReal) := hFOpt
  · -- Global minimality bounds every point in that fiber below by `FOpt`, hence also its infimum.
    refine le_sInf ?_
    rintro _ ⟨z2, rfl⟩
    have hmin := (isMinOn_iff.mp hxStar) (xStar.1, z2) (by simp)
    simpa [hFOpt] using hmin

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: exact minimization of the current first-block slice identifies the
second-block partial infimum at `x₂^n` with the half-step objective value. -/
lemma two_block_x2_partial_infimum_eq_current_value
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (n : ℕ) :
    φ₂ (x2 n) = F (two_block_alternating_minimization_half_step x1 x2 n) := by
  change sInf (Set.range (fun z1 : E1 ↦ F (z1, x2 n))) =
    F (two_block_alternating_minimization_half_step x1 x2 n)
  have hmin :
      IsMinOn
        (two_block_alternating_minimization_x1_objective f.toEReal g1 g2 (x2 n))
        Set.univ
        (x1 (n + 1)) := by
    simpa [Nat.succ_eq_add_one] using htraj.step_x1 n
  apply le_antisymm
  · -- The updated first block supplies one witness in the fiber defining `phi2`.
    exact sInf_le ⟨x1 (n + 1), by simp [two_block_alternating_minimization_half_step]⟩
  · -- Exact `x₁`-minimality keeps all other fiber values above the half-step objective.
    refine le_sInf ?_
    rintro _ ⟨z1, rfl⟩
    simpa [two_block_alternating_minimization_half_step] using
      (isMinOn_iff.mp hmin) z1 (by simp)

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: the second-block partial infimum equals the optimal value at
`xStar.2`. -/
lemma two_block_x2_partial_infimum_eq_optimal_value
    (hxStar : IsMinOn F Set.univ xStar)
    (hFOpt : F xStar = (FOpt : EReal)) :
    φ₂ xStar.2 = (FOpt : EReal) := by
  change sInf (Set.range (fun z1 : E1 ↦ F (z1, xStar.2))) = (FOpt : EReal)
  apply le_antisymm
  · -- The optimal pair contributes the witness `xStar.1` in the fiber over `xStar.2`.
    calc
      sInf (Set.range (fun z1 : E1 ↦ F (z1, xStar.2))) ≤ F (xStar.1, xStar.2) := by
        exact sInf_le ⟨xStar.1, by simp⟩
      _ = (FOpt : EReal) := hFOpt
  · -- Global minimality bounds the entire fiber below by `FOpt`, hence also its infimum.
    refine le_sInf ?_
    rintro _ ⟨z1, rfl⟩
    have hmin := (isMinOn_iff.mp hxStar) (z1, xStar.2) (by simp)
    simpa [hFOpt] using hmin

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: if the full objective is finite at `y`, then the first penalty term
is also finite there. -/
lemma two_block_first_penalty_eq_coe_toReal_of_mem_effective_domain
    [hg1_proper : IsProperExtendedRealFunction g1]
    [hg2_proper : IsProperExtendedRealFunction g2]
    {y : E1 × E2} (hy : y ∈ effective_domain F) :
    (((g1 y.1).toReal : ℝ) : EReal) = g1 y.1 := by
  rcases y with ⟨y1, y2⟩
  have hg1_ne_top : g1 y1 ≠ ⊤ := by
    -- A top-valued active penalty would force the whole objective to be `⊤`, contradicting
    -- effective-domain membership.
    intro hg1_top
    have hFy_top : F (y1, y2) = ⊤ := by
      calc
        F (y1, y2) = (((f (y1, y2) : ℝ) : EReal) + ⊤) + g2 y2 := by
          simp [two_block_alternating_minimization_objective_apply, hg1_top]
        _ = ⊤ + g2 y2 := by
          rw [EReal.add_top_of_ne_bot (by simp)]
        _ = ⊤ := by
          rw [EReal.top_add_of_ne_bot (hg2_proper.ne_bot y2)]
    exact (mem_effective_domain.mp hy).ne hFy_top
  exact EReal.coe_toReal hg1_ne_top (hg1_proper.ne_bot y1)

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: if the full objective is finite at `y`, then the second penalty term
is also finite there. -/
lemma two_block_second_penalty_eq_coe_toReal_of_mem_effective_domain
    [hg1_proper : IsProperExtendedRealFunction g1]
    [hg2_proper : IsProperExtendedRealFunction g2]
    {y : E1 × E2} (hy : y ∈ effective_domain F) :
    (((g2 y.2).toReal : ℝ) : EReal) = g2 y.2 := by
  rcases y with ⟨y1, y2⟩
  have hg2_ne_top : g2 y2 ≠ ⊤ := by
    -- A top-valued inactive penalty would also force the whole objective to be `⊤`.
    intro hg2_top
    have hFy_top : F (y1, y2) = ⊤ := by
      calc
        F (y1, y2) = (((f (y1, y2) : ℝ) : EReal) + g1 y1) + ⊤ := by
          simp [two_block_alternating_minimization_objective_apply, hg2_top, add_assoc]
        _ = ⊤ := by
          have hleft_ne_bot :
              (((f (y1, y2) : ℝ) : EReal) + g1 y1) ≠ ⊥ := by
            exact (EReal.add_ne_bot_iff).2 ⟨by simp, hg1_proper.ne_bot y1⟩
          rw [EReal.add_top_of_ne_bot hleft_ne_bot]
    exact (mem_effective_domain.mp hy).ne hFy_top
  exact EReal.coe_toReal hg2_ne_top (hg2_proper.ne_bot y2)

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: finiteness of the full objective forces finiteness of the first
penalty term at the same point. -/
lemma two_block_first_penalty_mem_effective_domain_of_objective_mem
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    {y : E1 × E2} (hy : y ∈ effective_domain F) :
    y.1 ∈ effective_domain g1 := by
  -- Rewrite `g₁(y₁)` as a real coercion using the full-objective finiteness witness.
  refine mem_effective_domain.mpr <| lt_top_iff_ne_top.mpr ?_
  rw [← two_block_first_penalty_eq_coe_toReal_of_mem_effective_domain hy]
  simp

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: finiteness of the full objective also forces finiteness of the
second penalty term. -/
lemma two_block_second_penalty_mem_effective_domain_of_objective_mem
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    {y : E1 × E2} (hy : y ∈ effective_domain F) :
    y.2 ∈ effective_domain g2 := by
  -- Rewrite `g₂(y₂)` as a real coercion using the same effective-domain witness.
  refine mem_effective_domain.mpr <| lt_top_iff_ne_top.mpr ?_
  rw [← two_block_second_penalty_eq_coe_toReal_of_mem_effective_domain hy]
  simp

/-- Helper for Theorem 14.8: the full two-block objective
`F(y₁, y₂) = f(y₁, y₂) + g₁(y₁) + g₂(y₂)` is convex once the smooth term and both penalties are
convex. -/
lemma two_block_objective_is_convex_function
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hg1_convex : is_convex_function g1)
    (hg2_convex : is_convex_function g2) :
    is_convex_function F := by
  let H : E1 × E2 → EReal := fun p ↦ (((f p : ℝ) : EReal)) + g2 p.2
  have hH_convex : is_convex_function H := by
    -- First package the smooth term with the second penalty into the canonical split owner.
    simpa [H] using
      (joint_convex_split_objective_is_convex_function
        hf_convex
        (fun z2 ↦ (‹IsProperExtendedRealFunction g2›.ne_bot z2))
        hg2_convex :
        is_convex_function (fun p : E1 × E2 ↦ (((f p : ℝ) : EReal)) + g2 p.2))
  have hg1_pair_convex : is_convex_function (fun p : E1 × E2 ↦ g1 p.1) := by
    -- Then pull the first penalty back along the product projection.
    simpa using
      is_convex_function_precompose_linearMap_add
        hg1_convex
        (LinearMap.fst ℝ E1 E2)
        (0 : E1)
  have hH_ne_bot : ∀ p : E1 × E2, H p ≠ ⊥ := by
    intro p
    exact (EReal.add_ne_bot_iff).2 ⟨by simp, ‹IsProperExtendedRealFunction g2›.ne_bot p.2⟩
  have hg1_pair_ne_bot : ∀ p : E1 × E2, g1 p.1 ≠ ⊥ :=
    fun p ↦ ‹IsProperExtendedRealFunction g1›.ne_bot p.1
  have hsum_convex : is_convex_function (fun p : E1 × E2 ↦ H p + g1 p.1) := by
    exact
      is_convex_function_pointwise_add
        hH_convex hg1_pair_convex hH_ne_bot hg1_pair_ne_bot
  -- Reattach the first penalty to recover the full two-block objective.
  change
    is_convex_function
      (fun p : E1 × E2 ↦ (((f p : ℝ) : EReal)) + g1 p.1 + g2 p.2)
  simpa [H, add_assoc, add_left_comm, add_comm] using hsum_convex

/-- Helper for Theorem 14.8: the first full partial infimum
`φ₁(y₁) = inf_z₂ F(y₁, z₂)` is convex. -/
lemma two_block_x1_partial_infimum_is_convex
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hg1_convex : is_convex_function g1)
    (hg2_convex : is_convex_function g2) :
    is_convex_function φ₁ := by
  have hF_convex :=
    two_block_objective_is_convex_function
      hf_convex hg1_convex hg2_convex
  -- Apply Chapter 2 partial-infimum convexity directly to the full two-block objective.
  simpa [twoBlockX1PartialInfimum] using partial_infimum_is_convex_function hF_convex

/-- Helper for Theorem 14.8: the second full partial infimum
`φ₂(y₂) = inf_z₁ F(z₁, y₂)` is convex. -/
lemma two_block_x2_partial_infimum_is_convex
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hg1_convex : is_convex_function g1)
    (hg2_convex : is_convex_function g2) :
    is_convex_function φ₂ := by
  let H : E2 × E1 → EReal := fun yz ↦ F (yz.2, yz.1)
  have hH_convex : is_convex_function H := by
    have hF_convex :=
      two_block_objective_is_convex_function
        hf_convex hg1_convex hg2_convex
    -- Transport convexity of `F` through the coordinate swap `(y₂, z₁) ↦ (z₁, y₂)`.
    simpa [H, LinearEquiv.prodComm_apply] using
      is_convex_function_precompose_linearMap_add
        hF_convex
        (LinearEquiv.prodComm ℝ E2 E1).toLinearMap
        (0 : E1 × E2)
  -- Apply partial-infimum convexity on the swapped fibers defining `φ₂`.
  simpa [H, twoBlockX2PartialInfimum] using partial_infimum_is_convex_function hH_convex

/-- Helper for Theorem 14.8: the first inactive marginal
`η₁(y₁) = inf_z₂ (f(y₁, z₂) + g₂(z₂))` is convex. -/
lemma two_block_x1_inactive_marginal_is_convex
    [IsProperExtendedRealFunction g2]
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hg2_convex : is_convex_function g2) :
    is_convex_function η₁ := by
  let H : E1 × E2 → EReal := fun p ↦ (((f p : ℝ) : EReal)) + g2 p.2
  have hH_convex : is_convex_function H := by
    -- Package the smooth term and inactive penalty before taking the partial infimum.
    simpa [H] using
      (joint_convex_split_objective_is_convex_function
        hf_convex
        (fun z2 ↦ (‹IsProperExtendedRealFunction g2›.ne_bot z2))
        hg2_convex :
        is_convex_function (fun p : E1 × E2 ↦ (((f p : ℝ) : EReal)) + g2 p.2))
  -- The inactive marginal is the partial infimum of that split objective.
  simpa [H, twoBlockX1InactiveMarginal] using partial_infimum_is_convex_function hH_convex

/-- Helper for Theorem 14.8: the second inactive marginal
`η₂(y₂) = inf_z₁ (f(z₁, y₂) + g₁(z₁))` is convex. -/
lemma two_block_x2_inactive_marginal_is_convex
    [IsProperExtendedRealFunction g1]
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hg1_convex : is_convex_function g1) :
    is_convex_function η₂ := by
  let hswap : E2 × E1 → ℝ := fun p ↦ f (p.2, p.1)
  have hswap_convex : ConvexOn ℝ Set.univ hswap := by
    let phi : E2 × E1 →ᵃ[ℝ] E1 × E2 :=
      (LinearEquiv.prodComm ℝ E2 E1).toLinearMap.toAffineMap
    -- Swap the coordinates so the active penalty again sits on the inactive factor.
    simpa [hswap, Function.comp, phi] using hf_convex.comp_affineMap phi
  let H : E2 × E1 → EReal := fun p ↦ (((hswap p : ℝ) : EReal)) + g1 p.2
  have hH_convex : is_convex_function H := by
    -- Apply the same split-objective packaging after swapping the two coordinates.
    simpa [H] using
      (joint_convex_split_objective_is_convex_function
        hswap_convex
        (fun z1 ↦ (‹IsProperExtendedRealFunction g1›.ne_bot z1))
        hg1_convex :
        is_convex_function (fun p : E2 × E1 ↦ (((hswap p : ℝ) : EReal)) + g1 p.2))
  -- The second inactive marginal is the corresponding swapped partial infimum.
  simpa [H, hswap, twoBlockX2InactiveMarginal] using
    partial_infimum_is_convex_function hH_convex

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: once the current outer iterate is finite, the inactive marginal
`η₁(y₁) = inf_z₂ (f(y₁, z₂) + g₂(z₂))` is attained at the current second block. -/
lemma two_block_x1_inactive_marginal_eq_current_value
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F)
    (n : ℕ) :
    η₁ (x1 n) = (((f (x1 n, x2 n) : ℝ) : EReal)) + g2 (x2 n) := by
  change sInf (Set.range (fun z2 : E2 ↦ (((f (x1 n, z2) : ℝ) : EReal)) + g2 z2)) =
    (((f (x1 n, x2 n) : ℝ) : EReal)) + g2 (x2 n)
  have hiter :=
    two_block_iterates_mem_effective_domain_and_initial_sublevel
      htraj hx0 n
  have hg1_coe :
      (((g1 (x1 n)).toReal : ℝ) : EReal) = g1 (x1 n) :=
    two_block_first_penalty_eq_coe_toReal_of_mem_effective_domain
      hiter.1
  have hmin :
      IsMinOn
        (two_block_alternating_minimization_x2_objective f.toEReal g1 g2 (x1 n))
        Set.univ
        (x2 n) :=
    two_block_current_x2_objective_is_min_on
      htraj n
  apply le_antisymm
  · -- The current inactive block provides a witness in the marginal fiber.
    exact sInf_le ⟨x2 n, by simp⟩
  · -- Exact `x₂`-minimality lets us cancel the finite active penalty from both slice values.
    refine le_sInf ?_
    rintro _ ⟨z2, rfl⟩
    have hslice : F x[n] ≤ F (x1 n, z2) := by
      simpa using (isMinOn_iff.mp hmin) z2 (by simp)
    have hcancel :
        ((((f (x1 n, x2 n) : ℝ) : EReal) + g2 (x2 n)) +
            (((g1 (x1 n)).toReal : ℝ) : EReal)) ≤
          ((((f (x1 n, z2) : ℝ) : EReal) + g2 z2) +
            (((g1 (x1 n)).toReal : ℝ) : EReal)) := by
      simpa [two_block_alternating_minimization_objective_apply, hg1_coe,
        add_left_comm, add_comm] using hslice
    exact
      (EReal.addLECancellable_coe ((g1 (x1 n)).toReal)).add_le_add_iff_right.mp hcancel

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: the optimal second block gives an upper witness for the inactive
first-block marginal `η₁`. -/
lemma two_block_x1_inactive_marginal_le_optimal_witness :
    η₁ xStar.1 ≤ (((f xStar : ℝ) : EReal)) + g2 xStar.2 := by
  -- Insert the optimal inactive block as one witness in the marginal fiber.
  exact sInf_le ⟨xStar.2, by simp⟩

/-- Helper for Theorem 14.8: if `xStar` globally minimizes the full objective, then the optimal
second block actually attains the inactive marginal `η₁(xStar.1)`. -/
lemma two_block_x1_inactive_marginal_eq_optimal_witness_value
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    (hxStar : IsMinOn F Set.univ xStar)
    (hFOpt : F xStar = (FOpt : EReal)) :
    η₁ xStar.1 = (((f xStar : ℝ) : EReal)) + g2 xStar.2 := by
  have hxStar_mem : xStar ∈ effective_domain F :=
    two_block_optimal_point_mem_effective_domain
      hFOpt
  have hg1_star_val :
      (((g1 xStar.1).toReal : ℝ) : EReal) = g1 xStar.1 :=
    two_block_first_penalty_eq_coe_toReal_of_mem_effective_domain
      hxStar_mem
  apply le_antisymm
  · -- The optimal second block gives one witness in the defining fiber of `η₁(xStar.1)`.
    simpa using
      two_block_x1_inactive_marginal_le_optimal_witness
  · -- Global minimality on the full objective lets us cancel the finite active penalty term.
    refine le_sInf ?_
    rintro _ ⟨z2, rfl⟩
    have hmin := (isMinOn_iff.mp hxStar) (xStar.1, z2) (by simp)
    have hcancel :
        ((((f xStar : ℝ) : EReal) + g2 xStar.2) +
            (((g1 xStar.1).toReal : ℝ) : EReal)) ≤
          ((((f (xStar.1, z2) : ℝ) : EReal) + g2 z2) +
            (((g1 xStar.1).toReal : ℝ) : EReal)) := by
      have hxStar_eta : xStar = (xStar.1, xStar.2) := by
        cases xStar
        rfl
      have hmin' := hmin
      rw [hxStar_eta, two_block_alternating_minimization_objective_apply,
        two_block_alternating_minimization_objective_apply] at hmin'
      calc
        ((((f xStar : ℝ) : EReal) + g2 xStar.2) +
              (((g1 xStar.1).toReal : ℝ) : EReal))
            = ((((f xStar : ℝ) : EReal) + g2 xStar.2) + g1 xStar.1) := by
                rw [hg1_star_val]
        _ ≤ ((((f (xStar.1, z2) : ℝ) : EReal) + g2 z2) + g1 xStar.1) := by
              simpa [Function.toEReal, add_assoc, add_left_comm, add_comm] using hmin'
        _ = ((((f (xStar.1, z2) : ℝ) : EReal) + g2 z2) +
              (((g1 xStar.1).toReal : ℝ) : EReal)) := by
                rw [hg1_star_val]
    exact
      (EReal.addLECancellable_coe ((g1 xStar.1).toReal)).add_le_add_iff_right.mp hcancel

/-
These two marginal reattachment lemmas only use the product-space geometry and the properness
instances appearing explicitly in their headers; the ambient normed-space instances are unused.
-/
omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: reattaching the active penalty to `η₁(x₁^n)` recovers the full
current objective value. -/
lemma two_block_x1_inactive_marginal_add_active_penalty_eq_current_objective
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F)
    (n : ℕ) :
    η₁ (x1 n) + g1 (x1 n) = F x[n] := by
  have heta :
      η₁ (x1 n) = (((f (x1 n, x2 n) : ℝ) : EReal)) + g2 (x2 n) := by
    simpa using
      two_block_x1_inactive_marginal_eq_current_value
        htraj hx0 n
  -- Add back the active penalty after the exact inactive minimization identity.
  calc
    η₁ (x1 n) + g1 (x1 n)
        = ((((f (x1 n, x2 n) : ℝ) : EReal)) + g2 (x2 n)) + g1 (x1 n) := by
            rw [heta]
    _ = F x[n] := by
      simp [two_block_alternating_minimization_objective_apply, add_left_comm, add_comm]

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: reattaching the active penalty to the optimal witness for `η₁`
compares the marginal value against `F_opt`. -/
lemma two_block_x1_inactive_marginal_add_active_penalty_le_optimal_value
    (hFOpt : F xStar = (FOpt : EReal)) :
    η₁ xStar.1 + g1 xStar.1 ≤ (FOpt : EReal) := by
  have heta :
      η₁ xStar.1 ≤ (((f xStar : ℝ) : EReal)) + g2 xStar.2 := by
    simpa using
      two_block_x1_inactive_marginal_le_optimal_witness
  -- Add back the active penalty and rewrite to the full objective at `xStar`.
  calc
    η₁ xStar.1 + g1 xStar.1
        ≤ ((((f xStar : ℝ) : EReal)) + g2 xStar.2) + g1 xStar.1 := by
            simpa [add_assoc, add_left_comm, add_comm] using
              add_le_add_right heta (g1 xStar.1)
    _ = F xStar := by
      have hxStar_eta : xStar = (xStar.1, xStar.2) := by
        cases xStar
        rfl
      rw [show ((((f xStar : ℝ) : EReal)) + g2 xStar.2) + g1 xStar.1 =
          (((f xStar : ℝ) : EReal)) + (g1 xStar.1 + g2 xStar.2) by
            rw [add_assoc, add_comm (g2 xStar.2) (g1 xStar.1)]]
      rw [hxStar_eta, two_block_alternating_minimization_objective_apply]
      simp [Function.toEReal, add_assoc]
    _ = (FOpt : EReal) := hFOpt

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: once the half-step is finite, the inactive marginal
`η₂(y₂) = inf_z₁ (f(z₁, y₂) + g₁(z₁))` is attained at the updated first block. -/
lemma two_block_x2_inactive_marginal_eq_current_value
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F)
    (n : ℕ) :
    η₂ (x2 n) = (((f (x1 (n + 1), x2 n) : ℝ) : EReal)) + g1 (x1 (n + 1)) := by
  change sInf (Set.range (fun z1 : E1 ↦ (((f (z1, x2 n) : ℝ) : EReal)) + g1 z1)) =
    (((f (x1 (n + 1), x2 n) : ℝ) : EReal)) + g1 (x1 (n + 1))
  have hhalf :=
    two_block_half_step_mem_effective_domain_and_initial_sublevel
      htraj hx0 n
  have hg2_coe :
      (((g2 (x2 n)).toReal : ℝ) : EReal) = g2 (x2 n) := by
    simpa [two_block_alternating_minimization_half_step] using
      two_block_second_penalty_eq_coe_toReal_of_mem_effective_domain
        hhalf.1
  have hmin :
      IsMinOn
        (two_block_alternating_minimization_x1_objective f.toEReal g1 g2 (x2 n))
        Set.univ
        (x1 (n + 1)) := by
    simpa [Nat.succ_eq_add_one] using htraj.step_x1 n
  apply le_antisymm
  · -- The updated first block is a witness in the second marginal fiber.
    exact sInf_le ⟨x1 (n + 1), by simp⟩
  · -- Exact `x₁`-minimality lets us cancel the finite inactive penalty `g₂(x₂^n)`.
    refine le_sInf ?_
    rintro _ ⟨z1, rfl⟩
    have hslice :
        F (x1 (n + 1), x2 n) ≤ F (z1, x2 n) := by
      simpa [Nat.succ_eq_add_one, two_block_alternating_minimization_half_step] using
        (isMinOn_iff.mp hmin) z1 (by simp)
    have hcancel :
        ((((f (x1 (n + 1), x2 n) : ℝ) : EReal) + g1 (x1 (n + 1))) +
            (((g2 (x2 n)).toReal : ℝ) : EReal)) ≤
          ((((f (z1, x2 n) : ℝ) : EReal) + g1 z1) +
            (((g2 (x2 n)).toReal : ℝ) : EReal)) := by
      simpa [two_block_alternating_minimization_objective_apply, hg2_coe,
        add_left_comm, add_comm] using hslice
    exact
      (EReal.addLECancellable_coe ((g2 (x2 n)).toReal)).add_le_add_iff_right.mp hcancel

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: the optimal first block gives an upper witness for the inactive
second-block marginal `η₂`. -/
lemma two_block_x2_inactive_marginal_le_optimal_witness :
    η₂ xStar.2 ≤ (((f xStar : ℝ) : EReal)) + g1 xStar.1 := by
  -- Insert the optimal active block as one witness in the marginal fiber.
  exact sInf_le ⟨xStar.1, by simp⟩

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: if `xStar` globally minimizes the full objective, then the optimal
first block actually attains the inactive marginal `η₂(xStar.2)`. -/
lemma two_block_x2_inactive_marginal_eq_optimal_witness_value
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    (hxStar : IsMinOn F Set.univ xStar)
    (hFOpt : F xStar = (FOpt : EReal)) :
    η₂ xStar.2 = (((f xStar : ℝ) : EReal)) + g1 xStar.1 := by
  have hxStar_mem : xStar ∈ effective_domain F :=
    two_block_optimal_point_mem_effective_domain
      hFOpt
  have hg2_star_val :
      (((g2 xStar.2).toReal : ℝ) : EReal) = g2 xStar.2 :=
    two_block_second_penalty_eq_coe_toReal_of_mem_effective_domain
      hxStar_mem
  apply le_antisymm
  · -- The optimal first block gives one witness in the defining fiber of `η₂(xStar.2)`.
    simpa using
      two_block_x2_inactive_marginal_le_optimal_witness
  · -- Global minimality on the full objective lets us cancel the finite inactive penalty term.
    refine le_sInf ?_
    rintro _ ⟨z1, rfl⟩
    have hmin := (isMinOn_iff.mp hxStar) (z1, xStar.2) (by simp)
    have hcancel :
        ((((f xStar : ℝ) : EReal) + g1 xStar.1) +
            (((g2 xStar.2).toReal : ℝ) : EReal)) ≤
          ((((f (z1, xStar.2) : ℝ) : EReal) + g1 z1) +
            (((g2 xStar.2).toReal : ℝ) : EReal)) := by
      have hxStar_eta : xStar = (xStar.1, xStar.2) := by
        cases xStar
        rfl
      have hmin' := hmin
      rw [hxStar_eta, two_block_alternating_minimization_objective_apply,
        two_block_alternating_minimization_objective_apply] at hmin'
      calc
        ((((f xStar : ℝ) : EReal) + g1 xStar.1) +
              (((g2 xStar.2).toReal : ℝ) : EReal))
            = ((((f xStar : ℝ) : EReal) + g1 xStar.1) + g2 xStar.2) := by
                rw [hg2_star_val]
        _ ≤ ((((f (z1, xStar.2) : ℝ) : EReal) + g1 z1) + g2 xStar.2) := by
              simpa [Function.toEReal, add_assoc] using hmin'
        _ = ((((f (z1, xStar.2) : ℝ) : EReal) + g1 z1) +
              (((g2 xStar.2).toReal : ℝ) : EReal)) := by
                rw [hg2_star_val]
    exact
      (EReal.addLECancellable_coe ((g2 xStar.2).toReal)).add_le_add_iff_right.mp hcancel

/-
This half-step reattachment lemma likewise uses only the explicit properness assumptions and the
pair-space objective. -/
omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: reattaching the inactive penalty to `η₂(x₂^n)` recovers the
half-step objective value. -/
lemma x2_marginal_add_penalty_eq_half_step_objective
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F)
    (n : ℕ) :
    η₂ (x2 n) + g2 (x2 n) = F (two_block_alternating_minimization_half_step x1 x2 n) := by
  have heta :
      η₂ (x2 n) = (((f (x1 (n + 1), x2 n) : ℝ) : EReal)) + g1 (x1 (n + 1)) := by
    simpa using
      two_block_x2_inactive_marginal_eq_current_value
        htraj hx0 n
  -- Add back the frozen second-block penalty after the exact inactive minimization identity.
  calc
    η₂ (x2 n) + g2 (x2 n)
        = ((((f (x1 (n + 1), x2 n) : ℝ) : EReal)) + g1 (x1 (n + 1))) + g2 (x2 n) := by
            rw [heta]
    _ = F (two_block_alternating_minimization_half_step x1 x2 n) := by
      simp [two_block_alternating_minimization_objective_apply,
        two_block_alternating_minimization_half_step, add_comm]

omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: reattaching the inactive penalty to the optimal witness for `η₂`
compares that marginal value against `F_opt`. -/
lemma two_block_x2_inactive_marginal_add_inactive_penalty_le_optimal_value
    (hFOpt : F xStar = (FOpt : EReal)) :
    η₂ xStar.2 + g2 xStar.2 ≤ (FOpt : EReal) := by
  have heta :
      η₂ xStar.2 ≤ (((f xStar : ℝ) : EReal)) + g1 xStar.1 := by
    simpa using
      two_block_x2_inactive_marginal_le_optimal_witness
  -- Add back the inactive penalty and rewrite to the full objective at `xStar`.
  calc
    η₂ xStar.2 + g2 xStar.2
        ≤ ((((f xStar : ℝ) : EReal)) + g1 xStar.1) + g2 xStar.2 := by
            simpa [add_assoc, add_left_comm, add_comm] using
              add_le_add_right heta (g2 xStar.2)
    _ = F xStar := by
      have hxStar_eta : xStar = (xStar.1, xStar.2) := by
        cases xStar
        rfl
      rw [show ((((f xStar : ℝ) : EReal)) + g1 xStar.1) + g2 xStar.2 =
          (((f xStar : ℝ) : EReal)) + (g1 xStar.1 + g2 xStar.2) by
            rw [add_assoc]]
      rw [hxStar_eta, two_block_alternating_minimization_objective_apply]
      simp [Function.toEReal, add_assoc]
    _ = (FOpt : EReal) := hFOpt

/-- Helper for Theorem 14.8: once a pair objective has a supporting affine lower bound at an
attained fiber minimizer, the same support inequality descends to the partial infimum. -/
lemma partial_infimum_support_of_attained_pair_support
    {E : Type u} {V : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (H : E × V → EReal) (x0 : E) (v0 : V) (g : Module.Dual ℝ E)
    (hattained :
      sInf (Set.range (fun v : V ↦ H (x0, v))) = H (x0, v0))
    (hsupport :
      ∀ y : E, ∀ v : V, H (y, v) ≥ H (x0, v0) + (g (y - x0) : EReal)) :
    ∀ y : E,
      sInf (Set.range (fun v : V ↦ H (y, v))) ≥
        sInf (Set.range (fun v : V ↦ H (x0, v))) + (g (y - x0) : EReal) := by
  intro y
  -- Rewrite the base fiber infimum through the attained minimizer before descending the support
  -- inequality to the entire target fiber.
  rw [hattained]
  refine le_sInf ?_
  rintro _ ⟨v, rfl⟩
  -- Every point in the `y`-fiber lies above the same supporting affine lower bound.
  exact hsupport y v

/-- Helper for Theorem 14.8: the source proof sometimes only needs to descend mixed pair support
at one fixed active competitor, not uniformly over all active competitors. -/
lemma partial_infimum_support_at_fixed_point_of_attained_pair_support
    {E : Type u} {V : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (H : E × V → EReal) (x0 : E) (v0 : V) (y : E) (g : Module.Dual ℝ E)
    (hattained :
      sInf (Set.range (fun v : V ↦ H (x0, v))) = H (x0, v0))
    (hsupport :
      ∀ v : V, H (y, v) ≥ H (x0, v0) + (g (y - x0) : EReal)) :
    sInf (Set.range (fun v : V ↦ H (y, v))) ≥
      sInf (Set.range (fun v : V ↦ H (x0, v))) + (g (y - x0) : EReal) := by
  -- Rewrite the base fiber through its attained minimizer and then check every point of the fixed
  -- target fiber against the same affine lower bound.
  rw [hattained]
  refine le_sInf ?_
  rintro _ ⟨v, rfl⟩
  exact hsupport v

/-- Helper for Theorem 14.8: for a jointly convex two-variable extended-real objective, affine
support on an attained minimizing fiber descends to the partial infimum once the pair-support
inequality is already available on the whole target fiber. -/
lemma convex_partial_infimum_support_of_exact_fiber_minimizer
    {E : Type u} {V : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {H : E × V → EReal} {x0 : E} {v0 : V} {g : Module.Dual ℝ E}
    (hattained :
      sInf (Set.range (fun v : V ↦ H (x0, v))) = H (x0, v0))
    (hpair_support :
      ∀ y : E, ∀ v : V, H (y, v) ≥ H (x0, v0) + (g (y - x0) : EReal)) :
    ∀ y : E,
      sInf (Set.range (fun v : V ↦ H (y, v))) ≥
        sInf (Set.range (fun v : V ↦ H (x0, v))) + (g (y - x0) : EReal) := by
  intro y
  -- Route correction: the old theorem tried to manufacture whole-fiber pair support from a single
  -- frozen-slice support inequality. That implication is false in general, so this helper now only
  -- performs the true descent step once the whole-fiber support input has been provided.
  simpa using
    partial_infimum_support_of_attained_pair_support
      H x0 v0 g
      hattained
      hpair_support
      y

/-- Helper for Theorem 14.8: for the split objective `H(y, v) = h(y, v) + q(v)`, the true
fixed-competitor bridge only descends support once the whole target fiber already satisfies the
same affine lower bound. -/
-- Route correction: the old split-objective bridge tried to infer whole-fiber support from the
-- single active slice `v = v0`, but the counterexample below shows that implication is false.
-- The repaired helper only performs the honest descent step from a supplied fixed-`y` pair-support
-- hypothesis to the corresponding partial-infimum inequality.
lemma partial_infimum_support_of_exact_fiber_minimizer
    {E : Type u} {V : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {h : E × V → ℝ} {q : V → EReal} {x0 : E} {v0 : V} {y : E} {g : Module.Dual ℝ E}
    (hattained :
      sInf (Set.range (fun v : V ↦ (((h (x0, v) : ℝ) : EReal)) + q v)) =
        (((h (x0, v0) : ℝ) : EReal)) + q v0)
    (hsupport :
      ∀ v : V,
        (((h (y, v) : ℝ) : EReal)) + q v ≥
          ((((h (x0, v0) : ℝ) : EReal)) + q v0) + (g (y - x0) : EReal)) :
    sInf (Set.range (fun v : V ↦ (((h (y, v) : ℝ) : EReal)) + q v)) ≥
      sInf (Set.range (fun v : V ↦ (((h (x0, v) : ℝ) : EReal)) + q v)) +
        (g (y - x0) : EReal) := by
  -- Descend the supplied fixed-competitor pair support to the fiber infimum by rewriting the base
  -- fiber through its attained minimizer.
  simpa using
    partial_infimum_support_at_fixed_point_of_attained_pair_support
      (fun yz : E × V ↦ (((h yz : ℝ) : EReal)) + q yz.2)
      x0 v0 y g
      hattained
      hsupport

/-- Helper for Theorem 14.8: once a uniform mixed pair-support inequality is available for the
inactive `x₂` fibers, it descends directly to the first-block marginal `η₁`. -/
lemma two_block_x1_inactive_marginal_support_of_pair_support
    (n : ℕ)
    (hattained :
      sInf (Set.range (fun z2 : E2 ↦ (((f (x1 n, z2) : ℝ) : EReal)) + g2 z2)) =
        (((f (x1 n, x2 n) : ℝ) : EReal)) + g2 (x2 n))
    (hpair_support :
      ∀ y1 : E1, ∀ z2 : E2,
        (((f (y1, z2) : ℝ) : EReal)) + g2 z2 ≥
          ((((f (x1 n, x2 n) : ℝ) : EReal)) + g2 (x2 n)) +
            (fderiv ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n) (y1 - x1 n) : EReal)) :
    ∀ y1 : E1,
      sInf (Set.range (fun z2 : E2 ↦ (((f (y1, z2) : ℝ) : EReal)) + g2 z2)) ≥
        sInf (Set.range (fun z2 : E2 ↦ (((f (x1 n, z2) : ℝ) : EReal)) + g2 z2)) +
          (fderiv ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n) (y1 - x1 n) : EReal) := by
  intro y1
  -- Descend the pair-support inequality to the partial infimum by rewriting the attained base
  -- fiber through the current second-block minimizer.
  simpa using
    partial_infimum_support_of_attained_pair_support
      (fun yz : E1 × E2 ↦ (((f yz : ℝ) : EReal)) + g2 yz.2)
      (x1 n) (x2 n)
      (fderiv ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n))
      hattained
      (by
        intro y1 z2
        simpa using hpair_support y1 z2)
      y1

/-- Helper for Theorem 14.8: the symmetric mixed pair-support inequality descends to the
second-block marginal `η₂`. -/
lemma two_block_x2_inactive_marginal_support_of_pair_support
    (n : ℕ)
    (hattained :
      sInf (Set.range (fun z1 : E1 ↦ (((f (z1, x2 n) : ℝ) : EReal)) + g1 z1)) =
        (((f (x1 (n + 1), x2 n) : ℝ) : EReal)) + g1 (x1 (n + 1)))
    (hpair_support :
      ∀ y2 : E2, ∀ z1 : E1,
        (((f (z1, y2) : ℝ) : EReal)) + g1 z1 ≥
          ((((f (x1 (n + 1), x2 n) : ℝ) : EReal)) + g1 (x1 (n + 1))) +
            (fderiv ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n) (y2 - x2 n) : EReal)) :
    ∀ y2 : E2,
      sInf (Set.range (fun z1 : E1 ↦ (((f (z1, y2) : ℝ) : EReal)) + g1 z1)) ≥
        sInf (Set.range (fun z1 : E1 ↦ (((f (z1, x2 n) : ℝ) : EReal)) + g1 z1)) +
          (fderiv ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n) (y2 - x2 n) : EReal) := by
  intro y2
  -- Descend the symmetric pair-support inequality to the partial infimum by rewriting the
  -- attained base fiber through the half-step first-block minimizer.
  simpa using
    partial_infimum_support_of_attained_pair_support
      (fun yz : E2 × E1 ↦ (((f (yz.2, yz.1) : ℝ) : EReal)) + g1 yz.2)
      (x2 n) (x1 (n + 1))
      (fderiv ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n))
      hattained
      (by
        intro y2 z1
        simpa [add_comm] using hpair_support y2 z1)
      y2

/-- Helper for Theorem 14.8: convexity of the smooth term gives the first-order support inequality
on the frozen current second-block slice `y₁ ↦ f(y₁, x₂^n)`. -/
lemma two_block_x1_frozen_slice_support_at_current_second_block
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_x1_smooth :
      ∀ z2 : E2, is_l_smooth_on (fun y1 ↦ f (y1, z2)) Set.univ (PosReal.toNNReal L1))
    (n : ℕ) (y1 : E1) :
    f (y1, x2 n) ≥
      f (x1 n, x2 n) +
        fderiv ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n) (y1 - x1 n) := by
  have hslice_convex : ConvexOn ℝ Set.univ (fun z1 ↦ f (z1, x2 n)) := by
    let phi : E1 →ᵃ[ℝ] E1 × E2 :=
      (LinearMap.inl ℝ E1 E2).toAffineMap + AffineMap.const ℝ E1 (0, x2 n)
    have hphi : (fun z1 ↦ phi z1) = fun z1 ↦ (z1, x2 n) := by
      funext z1
      simp [phi]
    -- Restrict joint convexity to the frozen second-block affine slice.
    simpa [Function.comp, hphi] using hf_convex.comp_affineMap phi
  have hdiff : DifferentiableAt ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n) := by
    -- Global `L₁`-smoothness makes the frozen slice differentiable at the current iterate.
    exact
      (is_l_smooth_on_iff.mp (hf_x1_smooth (x2 n))).1 (x1 n) (by simp)
  -- Apply the generic real-valued first-order support inequality to the frozen slice.
  simpa using convex_real_support_univ_fderiv hslice_convex hdiff

/-
These support lemmas cancel a finite penalty term from objective comparisons; they do not use the
ambient normed-space instances beyond the explicit properness assumptions on `g₁` and `g₂`.
-/
omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: exact minimization of the current second-block slice implies the
inactive-slice support inequality at the current first block. -/
lemma two_block_x1_inactive_slice_support_at_current_first_block
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F)
    (n : ℕ) :
    ∀ z2 : E2,
      (((f (x1 n, z2) : ℝ) : EReal) + g2 z2) ≥
        (((f (x1 n, x2 n) : ℝ) : EReal) + g2 (x2 n)) := by
  have hiter :=
    two_block_iterates_mem_effective_domain_and_initial_sublevel
      htraj hx0 n
  have hg1_coe :
      (((g1 (x1 n)).toReal : ℝ) : EReal) = g1 (x1 n) :=
    two_block_first_penalty_eq_coe_toReal_of_mem_effective_domain
      hiter.1
  have hmin :
      IsMinOn
        (two_block_alternating_minimization_x2_objective f.toEReal g1 g2 (x1 n))
        Set.univ
        (x2 n) :=
    two_block_current_x2_objective_is_min_on
      htraj n
  intro z2
  have hslice : F x[n] ≤ F (x1 n, z2) := by
    -- The current second block minimizes the frozen `x₁^n` objective.
    simpa using (isMinOn_iff.mp hmin) z2 (by simp)
  have hcancel :
      ((((f (x1 n, x2 n) : ℝ) : EReal) + g2 (x2 n)) +
          (((g1 (x1 n)).toReal : ℝ) : EReal)) ≤
        ((((f (x1 n, z2) : ℝ) : EReal) + g2 z2) +
          (((g1 (x1 n)).toReal : ℝ) : EReal)) := by
    -- Rewrite both full objective values so that the common finite active penalty can be canceled.
    simpa [two_block_alternating_minimization_objective_apply, hg1_coe,
      add_assoc, add_left_comm, add_comm] using hslice
  exact
    (EReal.addLECancellable_coe ((g1 (x1 n)).toReal)).add_le_add_iff_right.mp hcancel

/-- Helper for Theorem 14.8: convexity of the smooth term gives the first-order support inequality
on the frozen half-step first-block slice `y₂ ↦ f(x₁^{n+1}, y₂)`. -/
lemma two_block_x2_frozen_slice_support_at_half_step_first_block
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_x2_smooth :
      ∀ z1 : E1, is_l_smooth_on (fun y2 ↦ f (z1, y2)) Set.univ (PosReal.toNNReal L2))
    (n : ℕ) (y2 : E2) :
    f (x1 (n + 1), y2) ≥
      f (x1 (n + 1), x2 n) +
        fderiv ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n) (y2 - x2 n) := by
  have hslice_convex : ConvexOn ℝ Set.univ (fun z2 ↦ f (x1 (n + 1), z2)) := by
    let phi : E2 →ᵃ[ℝ] E1 × E2 :=
      (LinearMap.inr ℝ E1 E2).toAffineMap + AffineMap.const ℝ E2 (x1 (n + 1), 0)
    have hphi : (fun z2 ↦ phi z2) = fun z2 ↦ (x1 (n + 1), z2) := by
      funext z2
      simp [phi]
    -- Restrict joint convexity to the frozen first-block affine slice.
    simpa [Function.comp, hphi] using hf_convex.comp_affineMap phi
  have hdiff : DifferentiableAt ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n) := by
    -- Global `L₂`-smoothness makes the frozen slice differentiable at the current iterate.
    exact
      (is_l_smooth_on_iff.mp (hf_x2_smooth (x1 (n + 1)))).1 (x2 n) (by simp)
  -- Apply the generic real-valued first-order support inequality to the frozen slice.
  simpa using convex_real_support_univ_fderiv hslice_convex hdiff

/-
The symmetric inactive-slice support lemma has the same product-space-only dependency profile.
-/
omit [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: exact minimization of the half-step first-block slice implies the
inactive-slice support inequality at the current second block. -/
lemma two_block_x2_inactive_slice_support_at_current_second_block
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F)
    (n : ℕ) :
    ∀ z1 : E1,
      (((f (z1, x2 n) : ℝ) : EReal) + g1 z1) ≥
        (((f (x1 (n + 1), x2 n) : ℝ) : EReal) + g1 (x1 (n + 1))) := by
  have hhalf :=
    two_block_half_step_mem_effective_domain_and_initial_sublevel
      htraj hx0 n
  have hg2_coe :
      (((g2 (x2 n)).toReal : ℝ) : EReal) = g2 (x2 n) := by
    simpa [two_block_alternating_minimization_half_step] using
      two_block_second_penalty_eq_coe_toReal_of_mem_effective_domain
        hhalf.1
  have hmin :
      IsMinOn
        (two_block_alternating_minimization_x1_objective f.toEReal g1 g2 (x2 n))
        Set.univ
        (x1 (n + 1)) := by
    simpa [Nat.succ_eq_add_one] using htraj.step_x1 n
  intro z1
  have hslice : F (x1 (n + 1), x2 n) ≤ F (z1, x2 n) := by
    -- The half-step first block minimizes the frozen `x₂^n` objective.
    simpa [Nat.succ_eq_add_one, two_block_alternating_minimization_half_step] using
      (isMinOn_iff.mp hmin) z1 (by simp)
  have hcancel :
      ((((f (x1 (n + 1), x2 n) : ℝ) : EReal) + g1 (x1 (n + 1))) +
          (((g2 (x2 n)).toReal : ℝ) : EReal)) ≤
        ((((f (z1, x2 n) : ℝ) : EReal) + g1 z1) +
          (((g2 (x2 n)).toReal : ℝ) : EReal)) := by
    -- Rewrite both full objective values so that the common finite inactive penalty can be
    -- canceled.
    simpa [two_block_alternating_minimization_objective_apply, hg2_coe,
      add_assoc, add_left_comm, add_comm] using hslice
  exact
    (EReal.addLECancellable_coe ((g2 (x2 n)).toReal)).add_le_add_iff_right.mp hcancel

/-- Helper for Theorem 14.8: once the full source-faithful support inequality is known against the
fixed competitor `xStar`, it descends to the first inactive marginal `η₁`. -/
lemma two_block_x1_inactive_marginal_support_at_xStar_of_pair_support
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F)
    (n : ℕ)
    (hpair_support :
      ∀ z2 : E2,
        (((f (xStar.1, z2) : ℝ) : EReal)) + g2 z2 ≥
          ((((f (x1 n, x2 n) : ℝ) : EReal)) + g2 (x2 n)) +
            (fderiv ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n) (xStar.1 - x1 n) : EReal)) :
    η₁ xStar.1 ≥
      η₁ (x1 n) +
        (fderiv ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n) (xStar.1 - x1 n) : EReal) := by
  have hattained :
      sInf (Set.range (fun z2 : E2 ↦ (((f (x1 n, z2) : ℝ) : EReal)) + g2 z2)) =
        (((f (x1 n, x2 n) : ℝ) : EReal)) + g2 (x2 n) := by
    -- Rewrite the current marginal through the exact current second-block minimizer.
    simpa using
      two_block_x1_inactive_marginal_eq_current_value
        htraj hx0 n
  -- Descend the fixed-competitor pair support to the marginal by rewriting the attained base
  -- fiber through `x₂ⁿ`.
  simpa [twoBlockX1InactiveMarginal] using
    partial_infimum_support_at_fixed_point_of_attained_pair_support
      (fun yz : E1 × E2 ↦ (((f yz : ℝ) : EReal)) + g2 yz.2)
      (x1 n) (x2 n) xStar.1
      (fderiv ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n))
      hattained
      hpair_support

/-- Helper for Theorem 14.8: once the full source-faithful support inequality is known against the
fixed competitor `xStar`, it descends to the second inactive marginal `η₂`. -/
lemma two_block_x2_inactive_marginal_support_at_xStar_of_pair_support
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F)
    (n : ℕ)
    (hpair_support :
      ∀ z1 : E1,
        (((f (z1, xStar.2) : ℝ) : EReal)) + g1 z1 ≥
          ((((f (x1 (n + 1), x2 n) : ℝ) : EReal)) + g1 (x1 (n + 1))) +
            (fderiv ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n) (xStar.2 - x2 n) : EReal)) :
    η₂ xStar.2 ≥
      η₂ (x2 n) +
        (fderiv ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n) (xStar.2 - x2 n) : EReal) := by
  have hattained :
      sInf (Set.range (fun z1 : E1 ↦ (((f (z1, x2 n) : ℝ) : EReal)) + g1 z1)) =
        (((f (x1 (n + 1), x2 n) : ℝ) : EReal)) + g1 (x1 (n + 1)) := by
    -- Rewrite the current marginal through the exact half-step first-block minimizer.
    simpa using
      two_block_x2_inactive_marginal_eq_current_value
        htraj hx0 n
  -- Descend the fixed-competitor pair support to the marginal by rewriting the attained half-step
  -- fiber through `x₁^{n+1}`.
  simpa [twoBlockX2InactiveMarginal] using
    partial_infimum_support_at_fixed_point_of_attained_pair_support
      (fun yz : E2 × E1 ↦ (((f (yz.2, yz.1) : ℝ) : EReal)) + g1 yz.2)
      (x2 n) (x1 (n + 1)) xStar.2
      (fderiv ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n))
      hattained
      hpair_support

/-- Helper for Theorem 14.8: adding back the frozen inactive penalty turns the current first-block
slice support inequality into support for the split objective on the active slice
`y₁ ↦ f(y₁, x₂^n) + g₂(x₂^n)`. -/
lemma two_block_x1_split_objective_support_on_active_slice
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_x1_smooth :
      ∀ z2 : E2, is_l_smooth_on (fun y1 ↦ f (y1, z2)) Set.univ (PosReal.toNNReal L1))
    (n : ℕ) (y1 : E1) :
    (((f (y1, x2 n) : ℝ) : EReal)) + g2 (x2 n) ≥
      ((((f (x1 n, x2 n) : ℝ) : EReal)) + g2 (x2 n)) +
        (fderiv ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n) (y1 - x1 n) : EReal) := by
  have hslice_support :
      f (y1, x2 n) ≥
        f (x1 n, x2 n) +
          fderiv ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n) (y1 - x1 n) := by
    -- Reuse the real-valued frozen-slice first-order support inequality before reattaching the
    -- constant inactive penalty term.
    simpa using
      two_block_x1_frozen_slice_support_at_current_second_block
        hf_convex hf_x1_smooth n y1
  have hslice_support_le :
      f (x1 n, x2 n) +
          fderiv ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n) (y1 - x1 n) ≤
        f (y1, x2 n) := by
    linarith
  have hslice_support_ereal :
      ((((f (x1 n, x2 n) : ℝ) : EReal)) +
          (fderiv ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n) (y1 - x1 n) : EReal)) ≤
        (((f (y1, x2 n) : ℝ) : EReal)) := by
    exact_mod_cast hslice_support_le
  -- Add the same inactive penalty to both sides and normalize the affine term.
  simpa [add_assoc, add_left_comm, add_comm] using
    add_le_add_right hslice_support_ereal (g2 (x2 n))

/-- Helper for Theorem 14.8: adding back the frozen active penalty turns the current second-block
slice support inequality into support for the split objective on the active slice
`y₂ ↦ f(x₁^{n+1}, y₂) + g₁(x₁^{n+1})`. -/
lemma two_block_x2_split_objective_support_on_active_slice
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_x2_smooth :
      ∀ z1 : E1, is_l_smooth_on (fun y2 ↦ f (z1, y2)) Set.univ (PosReal.toNNReal L2))
    (n : ℕ) (y2 : E2) :
    (((f (x1 (n + 1), y2) : ℝ) : EReal)) + g1 (x1 (n + 1)) ≥
      ((((f (x1 (n + 1), x2 n) : ℝ) : EReal)) + g1 (x1 (n + 1))) +
        (fderiv ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n) (y2 - x2 n) : EReal) := by
  have hslice_support :
      f (x1 (n + 1), y2) ≥
        f (x1 (n + 1), x2 n) +
          fderiv ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n) (y2 - x2 n) := by
    -- Reuse the real-valued half-step slice support inequality before reattaching the constant
    -- active penalty term.
    simpa using
      two_block_x2_frozen_slice_support_at_half_step_first_block
        hf_convex hf_x2_smooth n y2
  have hslice_support_le :
      f (x1 (n + 1), x2 n) +
          fderiv ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n) (y2 - x2 n) ≤
        f (x1 (n + 1), y2) := by
    linarith
  have hslice_support_ereal :
      ((((f (x1 (n + 1), x2 n) : ℝ) : EReal)) +
          (fderiv ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n) (y2 - x2 n) : EReal)) ≤
        (((f (x1 (n + 1), y2) : ℝ) : EReal)) := by
    exact_mod_cast hslice_support_le
  -- Add the same active penalty to both sides and normalize the affine term.
  simpa [add_assoc, add_left_comm, add_comm] using
    add_le_add_right hslice_support_ereal (g1 (x1 (n + 1)))

/-- Helper for Theorem 14.8: convexity and differentiability of the active slice make its Fréchet
derivative a genuine Chapter 3 subgradient of the active-slice extended-real function. -/
lemma active_slice_fderiv_is_subgradient
    {E : Type u} {V : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {h : E × V → ℝ} {x0 : E} {v0 : V}
    (hh_convex : ConvexOn ℝ Set.univ h)
    (hslice_diff : DifferentiableAt ℝ (fun z : E ↦ h (z, v0)) x0) :
    is_subgradient_at
      (fun x : E ↦ (((h (x, v0) : ℝ) : EReal)))
      x0
      (fderiv ℝ (fun z : E ↦ h (z, v0)) x0) := by
  have hslice_convex : ConvexOn ℝ Set.univ (fun z : E ↦ h (z, v0)) := by
    let phi : E →ᵃ[ℝ] E × V :=
      (LinearMap.inl ℝ E V).toAffineMap + AffineMap.const ℝ E (0, v0)
    have hphi : (fun z ↦ phi z) = fun z ↦ (z, v0) := by
      funext z
      simp [phi]
    -- Restrict joint convexity to the active affine slice through `v0`.
    simpa [Function.comp, hphi] using hh_convex.comp_affineMap phi
  rw [is_subgradient_at_coe_iff]
  intro y
  -- The derivative of a convex real-valued slice supplies the supporting affine lower bound.
  simpa using convex_real_support_univ_fderiv hslice_convex hslice_diff

/-- Helper for Theorem 14.8: exact minimization of the inactive split slice makes the zero
functional a Chapter 3 subgradient of that one-variable slice objective. -/
lemma zero_mem_subdifferential_of_exact_inactive_split_minimizer
    {E : Type u} {V : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {h : E × V → ℝ} {q : V → EReal} {x0 : E} {v0 : V}
    (hv0_mem :
      v0 ∈ effective_domain (fun v : V ↦ (((h (x0, v) : ℝ) : EReal)) + q v))
    (hmin :
      ∀ v : V,
        (((h (x0, v) : ℝ) : EReal)) + q v ≥
          (((h (x0, v0) : ℝ) : EReal)) + q v0) :
    (0 : Module.Dual ℝ V) ∈
      subdifferential (fun v : V ↦ (((h (x0, v) : ℝ) : EReal)) + q v) v0 := by
  have hdom :
      (effective_domain (fun v : V ↦ (((h (x0, v) : ℝ) : EReal)) + q v)).Nonempty :=
    ⟨v0, hv0_mem⟩
  -- Convert the pointwise exact-minimizer inequality to the Chapter 3 Fermat criterion.
  refine (isMinOn_univ_iff_zero_mem_subdifferential hdom).mp ?_
  rw [isMinOn_univ_iff]
  intro v
  simpa using hmin v

/-- Helper for Theorem 14.8: the inactive marginal
`η(x) = inf_v (h(x, v) + q(v))` is convex whenever the split objective is jointly convex. -/
private lemma inactive_split_marginal_is_convex_function
    {E : Type u} {V : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {h : E × V → ℝ} {q : V → EReal}
    (hh_convex : ConvexOn ℝ Set.univ h)
    (hq_ne_bot : ∀ v : V, q v ≠ ⊥)
    (hq_convex : is_convex_function q) :
    is_convex_function
      (fun x : E ↦ sInf (Set.range (fun v : V ↦ (((h (x, v) : ℝ) : EReal)) + q v))) := by
  let H : E × V → EReal := fun p ↦ (((h p : ℝ) : EReal)) + q p.2
  have hH : is_convex_function H :=
    joint_convex_split_objective_is_convex_function
      hh_convex hq_ne_bot hq_convex
  -- Apply the chapter partial-infimum convexity owner to the split objective `H`.
  simpa [H] using partial_infimum_is_convex_function hH

/-- Helper for Theorem 14.8: every frozen inactive point `v0` gives an upper bound on the inactive
marginal `η(x) = inf_v (h(x, v) + q(v))`. -/
private lemma inactive_split_marginal_le_frozen_slice_value
    {E : Type u} {V : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {h : E × V → ℝ} {q : V → EReal} {x : E} {v0 : V} :
    sInf (Set.range (fun v : V ↦ (((h (x, v) : ℝ) : EReal)) + q v)) ≤
      (((h (x, v0) : ℝ) : EReal)) + q v0 := by
  -- The frozen value at `v0` is one witness in the defining fiber of the infimum.
  exact sInf_le ⟨v0, by simp⟩

/-- Helper for Theorem 14.8: if a convex extended-real marginal touches a differentiable real
majorant at `x0`, then the derivative of that majorant supports the marginal at any fixed
competitor whose marginal value is not `-∞`. -/
private lemma convex_contact_ne_bot
    {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {eta : E → EReal} {chi : E → ℝ} {x0 : E}
    (heta_convex : is_convex_function eta)
    (heta_le_chi : ∀ x : E, eta x ≤ (chi x : EReal))
    (heta_x0_eq : eta x0 = (chi x0 : EReal)) :
    ∀ z : E, eta z ≠ ⊥ := by
  intro z
  by_contra hz
  let w : E := (2 : ℝ) • x0 - z
  let rz : ℝ := 2 * chi x0 - chi w - 1
  have hz_epi : ((z, rz) : E × ℝ) ∈ {p : E × ℝ | eta p.1 ≤ (p.2 : EReal)} := by
    simp [hz]
  have hw_epi : ((w, chi w) : E × ℝ) ∈ {p : E × ℝ | eta p.1 ≤ (p.2 : EReal)} := by
    exact heta_le_chi w
  have hmid_raw :
      (((1 / 2 : ℝ) • z + (1 - 1 / 2 : ℝ) • w,
          (1 / 2 : ℝ) * rz + (1 - 1 / 2 : ℝ) * chi w) : E × ℝ) ∈
        {p : E × ℝ | eta p.1 ≤ (p.2 : EReal)} := by
    exact
      heta_convex hz_epi hw_epi (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
        (by norm_num : (0 : ℝ) ≤ (1 - 1 / 2 : ℝ))
        (by ring : (1 / 2 : ℝ) + (1 - 1 / 2 : ℝ) = 1)
  have hmid_coord :
      (1 / 2 : ℝ) • z + (1 - 1 / 2 : ℝ) • w = x0 := by
    dsimp [w]
    module
  have hmid_value :
      (1 / 2 : ℝ) * rz + (1 - 1 / 2 : ℝ) * chi w = chi x0 - 1 / 2 := by
    dsimp [rz]
    ring
  have hmid_le : eta x0 ≤ ((chi x0 - 1 / 2 : ℝ) : EReal) := by
    have hmid_raw' :
        eta ((1 / 2 : ℝ) • z + (1 - 1 / 2 : ℝ) • w) ≤
          (((1 / 2 : ℝ) * rz + (1 - 1 / 2 : ℝ) * chi w : ℝ) : EReal) := by
      exact hmid_raw
    rw [hmid_coord, hmid_value] at hmid_raw'
    exact hmid_raw'
  have hmid_lt : ((chi x0 - 1 / 2 : ℝ) : EReal) < (chi x0 : EReal) := by
    exact_mod_cast (sub_lt_self (chi x0) (by norm_num : (0 : ℝ) < 1 / 2))
  have hx0_gt : ((chi x0 - 1 / 2 : ℝ) : EReal) < eta x0 := by
    simpa [heta_x0_eq] using hmid_lt
  exact not_lt_of_ge hmid_le hx0_gt

/-- Helper for Theorem 14.8: on a finite-dimensional normed space, any subgradient of a convex
real-valued majorant at a differentiable point equals the Fréchet derivative pairing there. -/
private lemma subgradient_pairing_eq_fderiv_of_convex_differentiable
    {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {chi : E → ℝ} {x0 d : E} {p : Module.Dual ℝ E}
    (hchi_convex : ConvexOn ℝ Set.univ chi)
    (hchi_diff : DifferentiableAt ℝ chi x0)
    (hp : p ∈ ∂(fun x : E ↦ (chi x : EReal))(x0)) :
    (p d : EReal) = (fderiv ℝ chi x0 d : EReal) := by
  let chiE : E → EReal := fun x ↦ (chi x : EReal)
  haveI : IsProperExtendedRealFunction chiE :=
    { ne_bot := by
        intro x
        simp [chiE]
      effective_domain_nonempty := ⟨x0, by simp [chiE, effective_domain]⟩ }
  have hchi_convexE : is_convex_function chiE := by
    simpa [chiE] using Function.toEReal_isConvexFunction hchi_convex
  have hx0_eff : x0 ∈ interior (effective_domain chiE) := by
    simp [chiE, effective_domain]
  have hchiE_ne_bot : ∀ x : E, chiE x ≠ ⊥ := by
    intro x
    simp [chiE]
  have hx0_fin : x0 ∈ interior (finite_domain chiE) := by
    simpa [finite_domain_eq_effective_domain hchiE_ne_bot] using hx0_eff
  have hderiv :
      HasFDerivAt (fun y ↦ (chiE y).toReal) (fderiv ℝ chi x0) x0 := by
    -- The `EReal` coercion is finite everywhere, so the Fréchet derivative is unchanged.
    simpa [chiE] using hchi_diff.hasFDerivAt
  have hp_le :
      (p d : EReal) ≤ directional_derivative chiE x0 d := by
    exact
      subgradient_pairing_le_directional_derivative_at_interior_point
        hchi_convexE hx0_eff hp
  have hdir :
      directional_derivative chiE x0 d = (fderiv ℝ chi x0 d : EReal) := by
    simpa [chiE] using
      directional_derivative_eq_of_mem_interior_of_hasFDerivAt
        hx0_fin hderiv d
  have hleft : p d ≤ fderiv ℝ chi x0 d := by
    rw [hdir] at hp_le
    exact EReal.coe_le_coe_iff.mp hp_le
  have hp_neg_le :
      (p (-d) : EReal) ≤ directional_derivative chiE x0 (-d) := by
    exact
      subgradient_pairing_le_directional_derivative_at_interior_point
        hchi_convexE hx0_eff hp
  have hdir_neg :
      directional_derivative chiE x0 (-d) = (fderiv ℝ chi x0 (-d) : EReal) := by
    simpa [chiE] using
      directional_derivative_eq_of_mem_interior_of_hasFDerivAt
        hx0_fin hderiv (-d)
  have hright : fderiv ℝ chi x0 d ≤ p d := by
    rw [hdir_neg] at hp_neg_le
    have hneg :
        -(p d) ≤ -(fderiv ℝ chi x0 d) := by
      simpa using (EReal.coe_le_coe_iff.mp hp_neg_le)
    linarith
  exact congrArg (fun t : ℝ ↦ (t : EReal)) (le_antisymm hleft hright)

/-- Helper for Theorem 14.8: at a touching point, the derivative of the real majorant is
dominated by the directional derivative of the convex marginal in every direction. -/
private lemma majorantFDerivDominatedByMarginalDirectionalDerivative
    {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {eta : E → EReal} {chi : E → ℝ} {x0 : E}
    (heta_convex : is_convex_function eta)
    (hchi_convex : ConvexOn ℝ Set.univ chi)
    (heta_le_chi : ∀ x : E, eta x ≤ (chi x : EReal))
    (heta_x0_eq : eta x0 = (chi x0 : EReal))
    (hchi_diff : DifferentiableAt ℝ chi x0) :
    ∀ d : E, fderiv ℝ chi x0 d ≤ (directional_derivative eta x0 d).toReal := by
  intro d
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x0 (x0 + d)
  let etaLine : ℝ → EReal := fun t ↦ eta (line t)
  let chiLine : ℝ → ℝ := fun t ↦ chi (line t)
  have hetaLine_le_chiLine : ∀ t : ℝ, etaLine t ≤ (chiLine t : EReal) := by
    intro t
    exact heta_le_chi (line t)
  have hcontact_line : etaLine 0 = (chiLine 0 : EReal) := by
    simpa [etaLine, chiLine, line] using heta_x0_eq
  have hne_bot_line : ∀ t : ℝ, etaLine t ≠ ⊥ :=
    fun t ↦ convex_contact_ne_bot heta_convex heta_le_chi heta_x0_eq (line t)
  have heff_univ : effective_domain etaLine = Set.univ := by
    ext t
    constructor
    · intro _
      simp
    · intro _
      exact mem_effective_domain.mpr (lt_of_le_of_lt (hetaLine_le_chiLine t) (by simp))
  have hzero_int :
      (0 : ℝ) ∈ interior (effective_domain etaLine) := by
    -- The touching real majorant forces the line restriction to stay finite from above as well.
    simpa [heff_univ] using (show (0 : ℝ) ∈ interior (Set.univ : Set ℝ) by simp)
  have hzero_fin :
      (0 : ℝ) ∈ interior (finite_domain etaLine) := by
    simpa [finite_domain_eq_effective_domain hne_bot_line] using hzero_int
  letI : IsProperExtendedRealFunction etaLine :=
    { ne_bot := hne_bot_line
      effective_domain_nonempty := ⟨0, by simpa [heff_univ]⟩ }
  have hetaLine_convex : is_convex_function etaLine := by
    have heta_eff_univ : effective_domain eta = Set.univ := by
      ext z
      constructor
      · intro _
        simp
      · intro _
        exact mem_effective_domain.mpr (lt_of_le_of_lt (heta_le_chi z) (by simp))
    have heta_toReal_convex : ConvexOn ℝ Set.univ (fun z : E ↦ (eta z).toReal) := by
      -- The touched majorant makes `eta` finite-valued everywhere, so its `toReal` restriction is
      -- globally convex.
      simpa [heta_eff_univ] using
        convexOn_toReal_of_is_convex_function heta_convex
          (fun z _ ↦ convex_contact_ne_bot heta_convex heta_le_chi heta_x0_eq z)
    have hetaLine_toReal_convex :
        ConvexOn ℝ Set.univ (fun t : ℝ ↦ (etaLine t).toReal) := by
      -- Restrict the finite-valued convex representative to the same affine line.
      simpa [etaLine] using heta_toReal_convex.comp_affineMap line
    -- Convert the convexity of the finite-valued line restriction back to the chapter owner.
    exact (is_convex_function_iff_convexOn_toReal_of_proper etaLine).2 <| by
      simpa [heff_univ] using hetaLine_toReal_convex
  have hchiLine_convex : ConvexOn ℝ Set.univ chiLine := by
    -- Restrict the real majorant to the same line.
    simpa [chiLine, line] using hchi_convex.comp_affineMap line
  obtain ⟨p, hp_eta⟩ :=
    subdifferential_nonempty_at_interior_point etaLine 0 hetaLine_convex hzero_int
  have hp_chi : p ∈ ∂(fun t : ℝ ↦ (chiLine t : EReal))(0) := by
    -- The same affine support that holds for the marginal also supports the touching majorant.
    rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain] at hp_eta ⊢
    constructor
    · simp [chiLine, effective_domain]
    · intro t ht
      have ht_eta : t ∈ effective_domain etaLine := by
        simpa [heff_univ]
      calc
        (chiLine t : EReal) ≥ etaLine t := hetaLine_le_chiLine t
        _ ≥ etaLine 0 + (p (t - 0) : EReal) := hp_eta.2 t ht_eta
        _ = (chiLine 0 : EReal) + (p (t - 0) : EReal) := by
              rw [hcontact_line]
  have hp_le_dir :
      (p 1 : EReal) ≤ directional_derivative etaLine 0 1 := by
    -- A subgradient pairing is always bounded by the directional derivative at an interior point.
    exact
      subgradient_pairing_le_directional_derivative_at_interior_point
        hetaLine_convex hzero_int hp_eta
  have hchiLine_deriv :
      HasDerivAt chiLine (fderiv ℝ chi x0 d) 0 := by
    have hbase : HasFDerivAt chi (fderiv ℝ chi x0) (line 0) := by
      simpa [line] using hchi_diff.hasFDerivAt
    have hline_deriv : HasDerivAt line d 0 := by
      simpa [line] using
        (show HasDerivAt (AffineMap.lineMap x0 (x0 + d)) ((x0 + d) - x0) (0 : ℝ) from
          AffineMap.hasDerivAt_lineMap)
    -- Differentiate the majorant once along the chosen affine line.
    simpa [chiLine, line] using HasFDerivAt.comp_hasDerivAt 0 hbase hline_deriv
  have hchiLine_diff : DifferentiableAt ℝ chiLine 0 :=
    hchiLine_deriv.differentiableAt
  have hp_eq_fderiv :
      (p 1 : EReal) = (fderiv ℝ chiLine 0 1 : EReal) := by
    -- On the real line, the touching majorant has singleton subdifferential at the base point.
    exact
      subgradient_pairing_eq_fderiv_of_convex_differentiable
        hchiLine_convex hchiLine_diff hp_chi
  have hdir_line_real :
      directional_derivative etaLine 0 1 =
        (((directional_derivative etaLine 0 1).toReal : ℝ) : EReal) := by
    rcases
        exists_real_has_directional_derivative_at_of_convex_interior_point
          (f := etaLine) (x := (0 : ℝ)) (d := (1 : ℝ)) hetaLine_convex hzero_fin with
      ⟨ℓ, hℓ⟩
    rw [directional_derivative_eq_of_has_directional_derivative_at hℓ]
    simp
  have hline_fderiv :
      fderiv ℝ chiLine 0 1 = fderiv ℝ chi x0 d := by
    -- Evaluate the one-dimensional Fréchet derivative on the unit direction.
    simpa using hchiLine_deriv.deriv
  have hline_directional :
      directional_derivative etaLine 0 1 = directional_derivative eta x0 d := by
    -- Normalizing the line restriction recovers the original directional derivative.
    simp [directional_derivative, etaLine, line, AffineMap.lineMap_apply_module', add_comm]
  have hbound_line :
      (fderiv ℝ chiLine 0 1 : EReal) ≤
        (((directional_derivative etaLine 0 1).toReal : ℝ) : EReal) := by
    calc
      (fderiv ℝ chiLine 0 1 : EReal) = (p 1 : EReal) := by rw [hp_eq_fderiv]
      _ ≤ directional_derivative etaLine 0 1 := hp_le_dir
      _ = (((directional_derivative etaLine 0 1).toReal : ℝ) : EReal) := hdir_line_real
  have hbound_real :
      fderiv ℝ chiLine 0 1 ≤ (directional_derivative etaLine 0 1).toReal := by
    exact EReal.coe_le_coe_iff.mp hbound_line
  -- Translate the scalar line estimate back to the ambient direction `d`.
  simpa [hline_fderiv, hline_directional] using hbound_real

/-- Helper for Theorem 14.8: if a convex extended-real marginal touches a convex differentiable
real majorant at `x0`, then the derivative of that majorant supports the marginal at any fixed
competitor whose marginal value is not `-∞`. -/
private lemma convex_contact_support_at_fixed_point_of_differentiable_majorant
    {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {eta : E → EReal} {chi : E → ℝ} {x0 y : E}
    (heta_convex : is_convex_function eta)
    (hchi_convex : ConvexOn ℝ Set.univ chi)
    (heta_le_chi : ∀ x : E, eta x ≤ (chi x : EReal))
    (heta_x0_eq : eta x0 = (chi x0 : EReal))
    (hy_ne_bot : eta y ≠ ⊥)
    (hchi_diff : DifferentiableAt ℝ chi x0) :
    eta y ≥ eta x0 + (fderiv ℝ chi x0 (y - x0) : EReal) := by
  have hne_bot : ∀ z : E, eta z ≠ ⊥ :=
    convex_contact_ne_bot heta_convex heta_le_chi heta_x0_eq
  have hx0_int : x0 ∈ interior (effective_domain eta) := by
    -- The touching majorant makes the whole effective domain equal to `Set.univ`.
    have heff_univ : effective_domain eta = Set.univ := by
      ext z
      constructor
      · intro _
        simp
      · intro _
        exact mem_effective_domain.mpr (lt_of_le_of_lt (heta_le_chi z) (by simp))
    simpa [heff_univ] using (show x0 ∈ interior (Set.univ : Set E) by simp)
  have hx0_fin : x0 ∈ interior (finite_domain eta) := by
    simpa [finite_domain_eq_effective_domain hne_bot] using hx0_int
  have hy_eff : y ∈ effective_domain eta := by
    have hy_ne_top : eta y ≠ ⊤ := by
      exact ne_of_lt (lt_of_le_of_lt (heta_le_chi y) (by simp))
    exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hy_ne_top)
  have hsecant :
      eta y ≥ eta x0 + directional_derivative eta x0 (y - x0) := by
    -- Apply the Chapter 3 convex secant inequality at the touched point.
    exact
      value_ge_value_add_directional_derivative_of_mem_effective_domain
        eta x0 y heta_convex hne_bot hx0_int hy_eff
  have hdir_real :
      directional_derivative eta x0 (y - x0) =
        (((directional_derivative eta x0 (y - x0)).toReal : ℝ) : EReal) := by
    rcases
        exists_real_has_directional_derivative_at_of_convex_interior_point
          (f := eta) (x := x0) (d := y - x0) heta_convex hx0_fin with
      ⟨ℓ, hℓ⟩
    rw [directional_derivative_eq_of_has_directional_derivative_at hℓ]
    simp
  have hdir_bound_real :
      fderiv ℝ chi x0 (y - x0) ≤ (directional_derivative eta x0 (y - x0)).toReal :=
    majorantFDerivDominatedByMarginalDirectionalDerivative
      heta_convex hchi_convex heta_le_chi heta_x0_eq hchi_diff (y - x0)
  have hdir_bound :
      (fderiv ℝ chi x0 (y - x0) : EReal) ≤
        directional_derivative eta x0 (y - x0) := by
    rw [hdir_real]
    exact_mod_cast hdir_bound_real
  have hadd :
      eta x0 + (fderiv ℝ chi x0 (y - x0) : EReal) ≤
        eta x0 + directional_derivative eta x0 (y - x0) := by
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_left hdir_bound (eta x0)
  -- Replace the directional derivative in the secant inequality by the derivative of the
  -- touching majorant.
  exact le_trans hadd hsecant

/-- Helper for Theorem 14.8: the generic product-space bridge from an active-slice subgradient
and a zero inactive-slice subgradient to full pair support is false without extra structure. The
convex split objective `H(x, v) = |x - v|` at `(0, 0)` has active-slice subgradient `id`,
inactive-slice subgradient `0`, but the claimed pair-support inequality fails at `(1, 1)`. -/
private lemma pair_support_of_active_and_zero_inactive_subgradients_counterexample :
    let h : ℝ × ℝ → ℝ := fun p ↦ |p.1 - p.2|
    let q : ℝ → EReal := fun _ ↦ 0
    ConvexOn ℝ Set.univ h ∧
      is_subgradient_at
        (fun x : ℝ ↦ (((h (x, 0) : ℝ) : EReal)))
        0
        (LinearMap.id : Module.Dual ℝ ℝ) ∧
      (0 : Module.Dual ℝ ℝ) ∈
        subdifferential (fun v : ℝ ↦ (((h (0, v) : ℝ) : EReal)) + q v) 0 ∧
      ¬
        (∀ y v : ℝ,
          (((h (y, v) : ℝ) : EReal)) + q v ≥
            ((((h (0, 0) : ℝ) : EReal)) + q 0) +
              (((LinearMap.id : Module.Dual ℝ ℝ) (y - 0) : ℝ) : EReal)) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · let phi : ℝ × ℝ →ᵃ[ℝ] ℝ :=
        (LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ).toAffineMap +
          AffineMap.const ℝ (ℝ × ℝ) 0
    have hphi : (fun p : ℝ × ℝ ↦ phi p) = fun p ↦ p.1 - p.2 := by
      funext p
      simp [phi]
    simpa [hphi, Real.norm_eq_abs] using
      (convexOn_univ_norm : ConvexOn ℝ Set.univ (norm : ℝ → ℝ)).comp_affineMap phi
  · rw [is_subgradient_at_coe_iff]
    intro y
    simpa [Real.norm_eq_abs] using (le_abs_self y)
  · rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain]
    constructor
    · simp [effective_domain]
    · intro v hv
      simpa [Real.norm_eq_abs] using (show (0 : ℝ) ≤ ‖v‖ by exact norm_nonneg v)
  · intro hforall
    have hbad := hforall 1 1
    norm_num at hbad
    exact (by norm_num : ¬ ((1 : EReal) ≤ 0)) hbad

/-- Helper for Theorem 14.8: the current blocker is the fixed-competitor marginal-support step.
For a jointly convex split objective with an attained inactive minimizer at `(x0, v0)`, the
active-slice derivative through `v0` should support the inactive marginal at the fixed competitor
`y`. -/
-- Route correction: the generic product-space bridge from separate slice subgradients to full
-- pair support is false in general, as the counterexample above shows. The remaining blocker is a
-- theorem-specific strengthened bridge for the split objective used in Theorem 14.8.
private lemma fixed_competitor_support_of_joint_split_objective
    {E : Type u} {V : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {h : E × V → ℝ} {q : V → EReal} {x0 y : E} {v0 : V}
    (hh_convex : ConvexOn ℝ Set.univ h)
    (hq_ne_bot : ∀ v : V, q v ≠ ⊥)
    (hq_convex : is_convex_function q)
    (hslice_diff : DifferentiableAt ℝ (fun z : E ↦ h (z, v0)) x0)
    (hv0_mem :
      v0 ∈ effective_domain (fun v : V ↦ (((h (x0, v) : ℝ) : EReal)) + q v))
    (hattained :
      sInf (Set.range (fun v : V ↦ (((h (x0, v) : ℝ) : EReal)) + q v)) =
        (((h (x0, v0) : ℝ) : EReal)) + q v0)
    (hmin :
      ∀ v : V,
        (((h (x0, v) : ℝ) : EReal)) + q v ≥
          (((h (x0, v0) : ℝ) : EReal)) + q v0)
    (hy_ne_bot :
      let eta : E → EReal :=
        fun x ↦ sInf (Set.range (fun v : V ↦ (((h (x, v) : ℝ) : EReal)) + q v))
      eta y ≠ ⊥) :
    let eta : E → EReal :=
      fun x ↦ sInf (Set.range (fun v : V ↦ (((h (x, v) : ℝ) : EReal)) + q v))
    eta y ≥
      eta x0 + (fderiv ℝ (fun z : E ↦ h (z, v0)) x0 (y - x0) : EReal) := by
  let eta : E → EReal :=
    fun x ↦ sInf (Set.range (fun v : V ↦ (((h (x, v) : ℝ) : EReal)) + q v))
  let chi : E → ℝ := fun z ↦ h (z, v0) + (q v0).toReal
  have hqv0_ne_top : q v0 ≠ ⊤ := by
    intro htop
    have hsum_top :
        (((h (x0, v0) : ℝ) : EReal)) + q v0 = ⊤ := by
      rw [htop, add_comm, EReal.top_add_of_ne_bot (by simp)]
    exact (mem_effective_domain.mp hv0_mem).ne hsum_top
  have hqv0_coe : (((q v0).toReal : ℝ) : EReal) = q v0 := by
    exact EReal.coe_toReal hqv0_ne_top (hq_ne_bot v0)
  have heta_convex : is_convex_function eta := by
    -- The inactive marginal is convex because the split objective is jointly convex.
    exact inactive_split_marginal_is_convex_function hh_convex hq_ne_bot hq_convex
  have hchi_convex : ConvexOn ℝ Set.univ chi := by
    let phi : E →ᵃ[ℝ] E × V :=
      (LinearMap.inl ℝ E V).toAffineMap + AffineMap.const ℝ E (0, v0)
    have hphi : (fun z ↦ phi z) = fun z : E ↦ (z, v0) := by
      funext z
      simp [phi]
    have hslice_convex : ConvexOn ℝ Set.univ (fun z : E ↦ h (z, v0)) := by
      -- Restrict the joint smooth term to the active slice through `v0`.
      simpa [Function.comp, hphi] using hh_convex.comp_affineMap phi
    -- Adding the frozen inactive constant preserves convexity of the touching majorant.
    simpa [chi] using hslice_convex.add_const (q v0).toReal
  have heta_le_chi : ∀ x : E, eta x ≤ (chi x : EReal) := by
    intro x
    calc
      eta x ≤ (((h (x, v0) : ℝ) : EReal)) + q v0 :=
        inactive_split_marginal_le_frozen_slice_value
      _ = (chi x : EReal) := by
            simp [chi, hqv0_coe, add_assoc, add_left_comm, add_comm]
  have hcontact : eta x0 = (chi x0 : EReal) := by
    -- At `x0`, the chosen inactive witness `v0` attains the marginal infimum.
    simpa [eta, chi, hqv0_coe, add_assoc, add_left_comm, add_comm] using hattained
  have hy_ne_bot' : eta y ≠ ⊥ := by
    simpa [eta] using hy_ne_bot
  have hsupport :
      eta y ≥ eta x0 + (fderiv ℝ chi x0 (y - x0) : EReal) := by
    exact
      convex_contact_support_at_fixed_point_of_differentiable_majorant
        heta_convex
        hchi_convex
        heta_le_chi
        hcontact
        hy_ne_bot'
        (by simpa [chi] using hslice_diff)
  have hchi_fderiv :
      fderiv ℝ chi x0 (y - x0) =
        fderiv ℝ (fun z : E ↦ h (z, v0)) x0 (y - x0) := by
    simp [chi]
  -- Apply the generic touched-majorant support theorem to the inactive marginal and the frozen
  -- active slice through `v0`.
  simpa [eta, hchi_fderiv] using hsupport

/-- Helper for Theorem 14.8: the genuine source-faithful missing bridge is a marginal-subgradient
statement. When a jointly convex split objective attains the inactive minimizer at `(x0, v0)`, the
derivative on the active slice through `v0` should support the inactive marginal at `x0`. -/
private lemma attained_inactive_marginal_support_of_joint_convex_split_objective
    {E : Type u} {V : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {h : E × V → ℝ} {q : V → EReal} {x0 y : E} {v0 : V}
    (hh_convex : ConvexOn ℝ Set.univ h)
    (hq_ne_bot : ∀ v : V, q v ≠ ⊥)
    (hq_convex : is_convex_function q)
    (hslice_diff : DifferentiableAt ℝ (fun z : E ↦ h (z, v0)) x0)
    (hv0_mem :
      v0 ∈ effective_domain (fun v : V ↦ (((h (x0, v) : ℝ) : EReal)) + q v))
    (hattained :
      sInf (Set.range (fun v : V ↦ (((h (x0, v) : ℝ) : EReal)) + q v)) =
        (((h (x0, v0) : ℝ) : EReal)) + q v0)
    (hmin :
      ∀ v : V,
        (((h (x0, v) : ℝ) : EReal)) + q v ≥
          (((h (x0, v0) : ℝ) : EReal)) + q v0)
    (hy_ne_bot :
      let eta : E → EReal :=
        fun x ↦ sInf (Set.range (fun v : V ↦ (((h (x, v) : ℝ) : EReal)) + q v))
      eta y ≠ ⊥) :
    let eta : E → EReal :=
      fun x ↦ sInf (Set.range (fun v : V ↦ (((h (x, v) : ℝ) : EReal)) + q v))
    eta y ≥
      eta x0 + (fderiv ℝ (fun z : E ↦ h (z, v0)) x0 (y - x0) : EReal) := by
  -- This is exactly the fixed-competitor bridge specialized to the attained inactive marginal.
  simpa using
    fixed_competitor_support_of_joint_split_objective
      hh_convex hq_ne_bot hq_convex hslice_diff hv0_mem hattained hmin hy_ne_bot

section PropernessInstances

private lemma two_block_x1_inactive_marginal_eq_current_value_of_problem
    [hproblem : IsTwoBlockAlternatingMinimizationConvexRateProblem f g1 g2 XStar FOpt L1 L2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F)
    (n : ℕ) :
    sInf (Set.range (fun z2 : E2 ↦ (((f (x1 n, z2) : ℝ) : EReal)) + g2 z2)) =
      (((f (x1 n, x2 n) : ℝ) : EReal)) + g2 (x2 n) := by
  simpa using two_block_x1_inactive_marginal_eq_current_value htraj hx0 n

private lemma two_block_x2_inactive_marginal_eq_current_value_of_problem
    [hproblem : IsTwoBlockAlternatingMinimizationConvexRateProblem f g1 g2 XStar FOpt L1 L2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F)
    (n : ℕ) :
    sInf (Set.range (fun z1 : E1 ↦ (((f (z1, x2 n) : ℝ) : EReal)) + g1 z1)) =
      (((f (x1 (n + 1), x2 n) : ℝ) : EReal)) + g1 (x1 (n + 1)) := by
  simpa using two_block_x2_inactive_marginal_eq_current_value htraj hx0 n

private lemma two_block_objective_gap_nonneg_of_problem
    [hproblem : IsTwoBlockAlternatingMinimizationConvexRateProblem f g1 g2 XStar FOpt L1 L2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hxStar : IsMinOn F Set.univ xStar)
    (hFOpt : F xStar = (FOpt : EReal))
    (hx0 : x[0] ∈ effective_domain F)
    (n : ℕ) :
    0 ≤ (F x[n]).toReal - FOpt := by
  exact two_block_objective_gap_nonneg htraj hxStar hFOpt hx0 n

/-- Helper for Theorem 14.8: the attained current second-block minimizer should let the
frozen-slice support descend directly to the first inactive marginal at `xStar.1`. -/
private lemma two_block_x1_partial_infimum_support_at_current_iterate
    [hproblem : IsTwoBlockAlternatingMinimizationConvexRateProblem f g1 g2 XStar FOpt L1 L2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F)
    (hxStar_eta1_ne_bot : η₁ xStar.1 ≠ ⊥)
    (n : ℕ) :
    η₁ xStar.1 ≥
      η₁ (x1 n) +
        (fderiv ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n) (xStar.1 - x1 n) : EReal) := by
  have hiter :=
    two_block_iterates_mem_effective_domain_and_initial_sublevel
      htraj hx0 n
  have hslice_diff :
      DifferentiableAt ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n) := by
    -- The frozen first-block slice is differentiable at the current iterate by the `L₁`-smooth
    -- source assumption.
    exact
      (is_l_smooth_on_iff.mp (hproblem.f_x1_smooth (x2 n))).1
        (x1 n) (by simp)
  have hv0_mem :
      x2 n ∈ effective_domain (fun z2 : E2 ↦ (((f (x1 n, z2) : ℝ) : EReal)) + g2 z2) := by
    -- The current pair is finite, so the attained inactive witness value at `x₂ⁿ` is finite too.
    refine mem_effective_domain.mpr <| lt_top_iff_ne_top.mpr ?_
    intro htop
    have hF_top : F x[n] = ⊤ := by
      calc
        F x[n]
            = ((((f (x1 n, x2 n) : ℝ) : EReal)) + g2 (x2 n)) + g1 (x1 n) := by
                simp [two_block_alternating_minimization_objective_apply, add_assoc, add_left_comm,
                  add_comm]
        _ = ⊤ + g1 (x1 n) := by rw [htop]
        _ = ⊤ := by
              rw [EReal.top_add_of_ne_bot (hproblem.g1_proper.ne_bot (x1 n))]
    exact (mem_effective_domain.mp hiter.1).ne hF_top
  -- Specialize the generic touched-majorant bridge to the attained inactive marginal at
  -- `(x₁ⁿ, x₂ⁿ)` and the fixed competitor `xStar.1`.
  simpa [twoBlockX1InactiveMarginal] using
    fixed_competitor_support_of_joint_split_objective
      (h := f)
      (q := g2)
      (x0 := x1 n)
      (y := xStar.1)
      (v0 := x2 n)
      hproblem.f_convex
      (fun z2 ↦ hproblem.g2_proper.ne_bot z2)
      hproblem.g2_convex
      hslice_diff
      hv0_mem
      (two_block_x1_inactive_marginal_eq_current_value_of_problem htraj hx0 n)
      (two_block_x1_inactive_slice_support_at_current_first_block htraj hx0 n)
      (by simpa [twoBlockX1InactiveMarginal] using hxStar_eta1_ne_bot)

/-- Helper for Theorem 14.8: symmetrically, the attained half-step first-block minimizer should
let the frozen-slice support descend directly to the second inactive marginal at `xStar.2`. -/
private lemma two_block_x2_partial_infimum_support_at_half_step
    [hproblem : IsTwoBlockAlternatingMinimizationConvexRateProblem f g1 g2 XStar FOpt L1 L2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F)
    (hxStar_eta2_ne_bot : η₂ xStar.2 ≠ ⊥)
    (n : ℕ) :
    η₂ xStar.2 ≥
      η₂ (x2 n) +
        (fderiv ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n) (xStar.2 - x2 n) : EReal) := by
  have hhalf :=
    two_block_half_step_mem_effective_domain_and_initial_sublevel
      htraj hx0 n
  have hslice_diff :
      DifferentiableAt ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n) := by
    -- The frozen second-block slice is differentiable at the half-step base point by `L₂`-smoothness.
    exact
      (is_l_smooth_on_iff.mp (hproblem.f_x2_smooth (x1 (n + 1)))).1
        (x2 n) (by simp)
  have hv0_mem :
      x1 (n + 1) ∈
        effective_domain (fun z1 : E1 ↦ (((f (z1, x2 n) : ℝ) : EReal)) + g1 z1) := by
    -- The half-step pair is finite, so the attained inactive witness value at `x₁ⁿ⁺¹` is finite.
    refine mem_effective_domain.mpr <| lt_top_iff_ne_top.mpr ?_
    intro htop
    have hF_top : F (two_block_alternating_minimization_half_step x1 x2 n) = ⊤ := by
      calc
        F (two_block_alternating_minimization_half_step x1 x2 n)
            = ((((f (x1 (n + 1), x2 n) : ℝ) : EReal)) + g1 (x1 (n + 1))) + g2 (x2 n) := by
                simp [two_block_alternating_minimization_objective_apply,
                  two_block_alternating_minimization_half_step, add_assoc, add_left_comm, add_comm]
        _ = ⊤ + g2 (x2 n) := by rw [htop]
        _ = ⊤ := by
              rw [EReal.top_add_of_ne_bot (hproblem.g2_proper.ne_bot (x2 n))]
    exact (mem_effective_domain.mp hhalf.1).ne hF_top
  -- Specialize the generic touched-majorant bridge to the attained inactive marginal at the
  -- half-step pair `(x₁ⁿ⁺¹, x₂ⁿ)` and the fixed competitor `xStar.2`.
  simpa [twoBlockX2InactiveMarginal] using
    fixed_competitor_support_of_joint_split_objective
      (h := fun p : E2 × E1 ↦ f (p.2, p.1))
      (q := g1)
      (x0 := x2 n)
      (y := xStar.2)
      (v0 := x1 (n + 1))
      (by
        let phi : E2 × E1 →ᵃ[ℝ] E1 × E2 :=
          (LinearEquiv.prodComm ℝ E2 E1).toLinearMap.toAffineMap
        -- Swap the product coordinates so the generic split-objective bridge sees the active
        -- variable in first position.
        simpa [Function.comp, phi] using hproblem.f_convex.comp_affineMap phi)
      (fun z1 ↦ hproblem.g1_proper.ne_bot z1)
      hproblem.g1_convex
      hslice_diff
      hv0_mem
      (two_block_x2_inactive_marginal_eq_current_value_of_problem htraj hx0 n)
      (two_block_x2_inactive_slice_support_at_current_second_block htraj hx0 n)
      (by simpa [twoBlockX2InactiveMarginal] using hxStar_eta2_ne_bot)

/-- Helper for Theorem 14.8: once the direct marginal support at `xStar.1` is known, any point on
the fixed `xStar.1` fiber inherits the same lower bound because the marginal is an infimum. -/
private lemma two_block_x1_support_on_xStar_fiber_of_partial_infimum_support
    [hproblem : IsTwoBlockAlternatingMinimizationConvexRateProblem f g1 g2 XStar FOpt L1 L2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F)
    (hxStar_eta1_ne_bot : η₁ xStar.1 ≠ ⊥)
    (n : ℕ) :
    ∀ z2 : E2,
      (((f (xStar.1, z2) : ℝ) : EReal)) + g2 z2 ≥
        ((((f (x1 n, x2 n) : ℝ) : EReal)) + g2 (x2 n)) +
          (fderiv ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n) (xStar.1 - x1 n) : EReal) := by
  intro z2
  have hmarg :
      η₁ xStar.1 ≥
        η₁ (x1 n) +
          (fderiv ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n) (xStar.1 - x1 n) : EReal) := by
    -- Invoke the direct marginal-support bridge once it is available.
    simpa using
      two_block_x1_partial_infimum_support_at_current_iterate
        htraj hx0 hxStar_eta1_ne_bot n
  have hcurrent_value :
      η₁ (x1 n) = (((f (x1 n, x2 n) : ℝ) : EReal)) + g2 (x2 n) := by
    -- Rewrite the current marginal through its attained current-fiber minimizer.
    simpa using
      two_block_x1_inactive_marginal_eq_current_value_of_problem htraj hx0 n
  have hfiber :
      η₁ xStar.1 ≤ (((f (xStar.1, z2) : ℝ) : EReal)) + g2 z2 := by
    -- Every point on the fixed `xStar.1` fiber dominates the infimum defining `η₁(xStar.1)`.
    exact sInf_le ⟨z2, by simp⟩
  calc
    ((((f (x1 n, x2 n) : ℝ) : EReal)) + g2 (x2 n)) +
        (fderiv ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n) (xStar.1 - x1 n) : EReal)
        = η₁ (x1 n) +
            (fderiv ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n) (xStar.1 - x1 n) : EReal) := by
              rw [hcurrent_value]
    _ ≤ η₁ xStar.1 := hmarg
    _ ≤ (((f (xStar.1, z2) : ℝ) : EReal)) + g2 z2 := hfiber

/-- Helper for Theorem 14.8: once the direct marginal support at `xStar.2` is known, any point on
the fixed `xStar.2` fiber inherits the same lower bound because the marginal is an infimum. -/
private lemma two_block_x2_support_on_xStar_fiber_of_partial_infimum_support
    [hproblem : IsTwoBlockAlternatingMinimizationConvexRateProblem f g1 g2 XStar FOpt L1 L2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F)
    (hxStar_eta2_ne_bot : η₂ xStar.2 ≠ ⊥)
    (n : ℕ) :
    ∀ z1 : E1,
      (((f (z1, xStar.2) : ℝ) : EReal)) + g1 z1 ≥
        ((((f (x1 (n + 1), x2 n) : ℝ) : EReal)) + g1 (x1 (n + 1))) +
          (fderiv ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n) (xStar.2 - x2 n) : EReal) := by
  intro z1
  have hmarg :
      η₂ xStar.2 ≥
        η₂ (x2 n) +
          (fderiv ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n) (xStar.2 - x2 n) : EReal) := by
    -- Invoke the symmetric direct marginal-support bridge once it is available.
    simpa using
      two_block_x2_partial_infimum_support_at_half_step
        htraj hx0 hxStar_eta2_ne_bot n
  have hcurrent_value :
      η₂ (x2 n) = (((f (x1 (n + 1), x2 n) : ℝ) : EReal)) + g1 (x1 (n + 1)) := by
    -- Rewrite the half-step marginal through its attained first-block minimizer.
    simpa using
      two_block_x2_inactive_marginal_eq_current_value_of_problem htraj hx0 n
  have hfiber :
      η₂ xStar.2 ≤ (((f (z1, xStar.2) : ℝ) : EReal)) + g1 z1 := by
    -- Every point on the fixed `xStar.2` fiber dominates the infimum defining `η₂(xStar.2)`.
    exact sInf_le ⟨z1, by simp⟩
  calc
    ((((f (x1 (n + 1), x2 n) : ℝ) : EReal)) + g1 (x1 (n + 1))) +
        (fderiv ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n) (xStar.2 - x2 n) : EReal)
        = η₂ (x2 n) +
            (fderiv ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n) (xStar.2 - x2 n) : EReal) := by
              rw [hcurrent_value]
    _ ≤ η₂ xStar.2 := hmarg
    _ ≤ (((f (z1, xStar.2) : ℝ) : EReal)) + g1 z1 := hfiber

/-- Helper for Theorem 14.8: moving only the first block along the segment from `x₁^n` to
`xStar.1` can only shrink the distance to the optimizer pair. -/
lemma two_block_x1_trial_point_distance_le_current_distance
    (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖((((1 - t) • x1 n + t • xStar.1), x2 n) : E1 × E2) - xStar‖ ≤ ‖x[n] - xStar‖ := by
  rcases ht with ⟨ht_nonneg, ht_le_one⟩
  have hcoeff_nonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht_le_one
  have hfst :
      ‖((1 - t) • x1 n + t • xStar.1) - xStar.1‖ ≤ ‖x1 n - xStar.1‖ := by
    have hdisp :
        ((1 - t) • x1 n + t • xStar.1) - xStar.1 =
          (1 - t) • (x1 n - xStar.1) := by
      module
    calc
      ‖((1 - t) • x1 n + t • xStar.1) - xStar.1‖
          = ‖(1 - t) • (x1 n - xStar.1)‖ := by rw [hdisp]
      _ = |1 - t| * ‖x1 n - xStar.1‖ := norm_smul _ _
      _ = (1 - t) * ‖x1 n - xStar.1‖ := by
            rw [abs_of_nonneg hcoeff_nonneg]
      _ ≤ ‖x1 n - xStar.1‖ := by
            nlinarith [norm_nonneg (x1 n - xStar.1)]
  -- The second coordinate is unchanged, so the product max norm can only decrease.
  simpa [Prod.norm_def] using
    max_le_max hfst le_rfl

/-- Helper for Theorem 14.8: the first-block segment trial point inherits the same radius bound as
the current iterate. -/
lemma two_block_x1_trial_point_distance_le_radius
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F)
    (hR :
      ∀ ⦃y : E1 × E2⦄,
        F y ≤ F x[0] →
        ‖y - xStar‖ ≤ (R : ℝ))
    (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖((((1 - t) • x1 n + t • xStar.1), x2 n) : E1 × E2) - xStar‖ ≤ (R : ℝ) := by
  have hiter :=
    two_block_iterates_mem_effective_domain_and_initial_sublevel
      htraj hx0 n
  -- First compare to the current iterate, then invoke the given sublevel-radius bound.
  exact
    le_trans
      (two_block_x1_trial_point_distance_le_current_distance
        n ht)
      (hR hiter.2)

/-- Helper for Theorem 14.8: moving only the second block along the segment from `x₂^n` to
`xStar.2` can only shrink the distance to the half-step pair. -/
lemma two_block_x2_trial_point_distance_le_half_step_distance
    (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖((x1 (n + 1), (1 - t) • x2 n + t • xStar.2) : E1 × E2) - xStar‖ ≤
      ‖two_block_alternating_minimization_half_step x1 x2 n - xStar‖ := by
  rcases ht with ⟨ht_nonneg, ht_le_one⟩
  have hcoeff_nonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht_le_one
  have hsnd :
      ‖((1 - t) • x2 n + t • xStar.2) - xStar.2‖ ≤ ‖x2 n - xStar.2‖ := by
    have hdisp :
        ((1 - t) • x2 n + t • xStar.2) - xStar.2 =
          (1 - t) • (x2 n - xStar.2) := by
      module
    calc
      ‖((1 - t) • x2 n + t • xStar.2) - xStar.2‖
          = ‖(1 - t) • (x2 n - xStar.2)‖ := by rw [hdisp]
      _ = |1 - t| * ‖x2 n - xStar.2‖ := norm_smul _ _
      _ = (1 - t) * ‖x2 n - xStar.2‖ := by
            rw [abs_of_nonneg hcoeff_nonneg]
      _ ≤ ‖x2 n - xStar.2‖ := by
            nlinarith [norm_nonneg (x2 n - xStar.2)]
  -- The first coordinate is unchanged across the half-step comparison.
  simpa [two_block_alternating_minimization_half_step, Prod.norm_def] using
    max_le_max le_rfl hsnd

/-- Helper for Theorem 14.8: the second-block segment trial point inherits the same radius bound as
the half-step pair. -/
lemma two_block_x2_trial_point_distance_le_radius
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F)
    (hR :
      ∀ ⦃y : E1 × E2⦄,
        F y ≤ F x[0] →
        ‖y - xStar‖ ≤ (R : ℝ))
    (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖((x1 (n + 1), (1 - t) • x2 n + t • xStar.2) : E1 × E2) - xStar‖ ≤ (R : ℝ) := by
  have hhalf :=
    two_block_half_step_mem_effective_domain_and_initial_sublevel
      htraj hx0 n
  -- First compare to the half-step pair, then invoke the sublevel-radius bound there.
  exact
    le_trans
      (two_block_x2_trial_point_distance_le_half_step_distance
        n ht)
      (hR hhalf.2)

omit [NormedSpace ℝ E1] [NormedSpace ℝ E2] in
/-- Helper for Theorem 14.8: the current first-block distance to the optimizer is bounded by the
same initial-sublevel radius as the full pair iterate. -/
lemma two_block_x1_current_first_block_distance_le_radius
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F)
    (hR :
      ∀ ⦃y : E1 × E2⦄,
        F y ≤ F x[0] →
        ‖y - xStar‖ ≤ (R : ℝ))
    (n : ℕ) :
    ‖xStar.1 - x1 n‖ ≤ (R : ℝ) := by
  have hiter :=
    two_block_iterates_mem_effective_domain_and_initial_sublevel
      htraj hx0 n
  have hcoord :
      ‖x1 n - xStar.1‖ ≤ ‖x[n] - xStar‖ := by
    calc
      ‖x1 n - xStar.1‖
          ≤ max ‖x1 n - xStar.1‖ ‖x2 n - xStar.2‖ := le_max_left _ _
      _ = ‖x[n] - xStar‖ := by
            simp [Prod.norm_def]
  calc
    ‖xStar.1 - x1 n‖ = ‖x1 n - xStar.1‖ := norm_sub_rev _ _
    _ ≤ ‖x[n] - xStar‖ := hcoord
    _ ≤ (R : ℝ) := hR hiter.2

/-- Helper for Theorem 14.8: the source `x₁`-branch first compares the exact half-step against
the segment trial point toward `xStar.1`, yielding the affine-quadratic estimate in the trial
parameter `t`. -/
lemma two_block_x1_half_step_gap_le_affine_quadratic
    [hproblem : IsTwoBlockAlternatingMinimizationConvexRateProblem f g1 g2 XStar FOpt L1 L2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hxStar : IsMinOn F Set.univ xStar)
    (hFOpt : F xStar = (FOpt : EReal))
    (hx0 : x[0] ∈ effective_domain F)
    (hR :
      ∀ ⦃y : E1 × E2⦄,
        F y ≤ F x[0] →
        ‖y - xStar‖ ≤ (R : ℝ))
    (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    let xHalf := two_block_alternating_minimization_half_step x1 x2 n
    ((F xHalf).toReal - FOpt) ≤
      (1 - t) * ((F x[n]).toReal - FOpt) +
        (((L1 : ℝ) / 2) * t ^ (2 : ℕ) * ((R : ℝ) ^ (2 : ℕ))) := by
  let xHalf := two_block_alternating_minimization_half_step x1 x2 n
  let y1 : E1 := (1 - t) • x1 n + t • xStar.1
  have hiter :=
    two_block_iterates_mem_effective_domain_and_initial_sublevel
      htraj hx0 n
  have hhalf :=
    two_block_half_step_mem_effective_domain_and_initial_sublevel
      htraj hx0 n
  have hFx_val :
      (((F x[n]).toReal : ℝ) : EReal) = F x[n] := by
    -- The current iterate is finite, so its objective is the coercion of its real value.
    exact
      EReal.coe_toReal
        (mem_effective_domain.mp hiter.1).ne
        (two_block_objective_ne_bot x[n])
  have hFHalf_val :
      (((F xHalf).toReal : ℝ) : EReal) = F xHalf := by
    -- The same finite-value rewrite holds at the half-step iterate.
    exact
      EReal.coe_toReal
        (mem_effective_domain.mp hhalf.1).ne
        (two_block_objective_ne_bot xHalf)
  have hxStar_mem : xStar ∈ effective_domain F :=
    two_block_optimal_point_mem_effective_domain hFOpt
  have hg1_cur_eff :
      x1 n ∈ effective_domain g1 :=
    two_block_first_penalty_mem_effective_domain_of_objective_mem hiter.1
  have hg1_star_eff :
      xStar.1 ∈ effective_domain g1 :=
    two_block_first_penalty_mem_effective_domain_of_objective_mem hxStar_mem
  have hg2_cur_eff :
      x2 n ∈ effective_domain g2 :=
    two_block_second_penalty_mem_effective_domain_of_objective_mem hiter.1
  have hg1_cur_val :
      (((g1 (x1 n)).toReal : ℝ) : EReal) = g1 (x1 n) :=
    two_block_first_penalty_eq_coe_toReal_of_mem_effective_domain hiter.1
  have hg1_star_val :
      (((g1 xStar.1).toReal : ℝ) : EReal) = g1 xStar.1 :=
    two_block_first_penalty_eq_coe_toReal_of_mem_effective_domain hxStar_mem
  have hg2_cur_val :
      (((g2 (x2 n)).toReal : ℝ) : EReal) = g2 (x2 n) :=
    two_block_second_penalty_eq_coe_toReal_of_mem_effective_domain hiter.1
  have hηstar_ne_bot : η₁ xStar.1 ≠ ⊥ := by
    -- The optimal witness formula makes the marginal finite from below.
    rw [two_block_x1_inactive_marginal_eq_optimal_witness_value hxStar hFOpt]
    exact (EReal.add_ne_bot_iff).2 ⟨by simp, hproblem.g2_proper.ne_bot xStar.2⟩
  have hηcur_eq :
      η₁ (x1 n) = (((f (x1 n, x2 n) : ℝ) : EReal)) + g2 (x2 n) := by
    -- Rewrite the current marginal through the attained current second-block minimizer.
    simpa using two_block_x1_inactive_marginal_eq_current_value htraj hx0 n
  have hηstar_eq :
      η₁ xStar.1 = (((f xStar : ℝ) : EReal)) + g2 xStar.2 := by
    -- Rewrite the optimal marginal through the optimal second-block witness.
    simpa using two_block_x1_inactive_marginal_eq_optimal_witness_value hxStar hFOpt
  have hηcur_ne_top : η₁ (x1 n) ≠ ⊤ := by
    -- The current marginal is the sum of two finite terms.
    rw [hηcur_eq]
    exact
      (EReal.add_ne_top_iff_ne_top_right
        (x := (((f (x1 n, x2 n) : ℝ) : EReal)))
        (y := g2 (x2 n))
        (by simp)
        (by simp)).2
        (mem_effective_domain.mp hg2_cur_eff).ne
  have hηcur_ne_bot : η₁ (x1 n) ≠ ⊥ := by
    rw [hηcur_eq]
    exact (EReal.add_ne_bot_iff).2 ⟨by simp, hproblem.g2_proper.ne_bot (x2 n)⟩
  have hηstar_ne_top : η₁ xStar.1 ≠ ⊤ := by
    -- The optimal marginal is also represented by a finite witness value.
    have hg2_star_eff :
        xStar.2 ∈ effective_domain g2 :=
      two_block_second_penalty_mem_effective_domain_of_objective_mem hxStar_mem
    rw [hηstar_eq]
    exact
      (EReal.add_ne_top_iff_ne_top_right
        (x := (((f xStar : ℝ) : EReal)))
        (y := g2 xStar.2)
        (by simp)
        (by simp)).2
        (mem_effective_domain.mp hg2_star_eff).ne
  have hηcur_val :
      (((η₁ (x1 n)).toReal : ℝ) : EReal) = η₁ (x1 n) := by
    exact EReal.coe_toReal hηcur_ne_top hηcur_ne_bot
  have hηstar_val :
      (((η₁ xStar.1).toReal : ℝ) : EReal) = η₁ xStar.1 := by
    exact EReal.coe_toReal hηstar_ne_top hηstar_ne_bot
  have hηcur_real :
      (η₁ (x1 n)).toReal = f (x1 n, x2 n) + (g2 (x2 n)).toReal := by
    -- Convert the attained current marginal identity to a real equality.
    have htmp := congrArg EReal.toReal hηcur_eq
    rw [EReal.toReal_add (EReal.coe_ne_top _) (EReal.coe_ne_bot _)
      (mem_effective_domain.mp hg2_cur_eff).ne (hproblem.g2_proper.ne_bot (x2 n))] at htmp
    simpa using htmp
  have hcurrent_real :
      (η₁ (x1 n)).toReal + (g1 (x1 n)).toReal = (F x[n]).toReal := by
    -- Reattaching the current active penalty recovers the current full objective.
    have hcurrE :=
      two_block_x1_inactive_marginal_add_active_penalty_eq_current_objective
        htraj hx0 n
    have htmp :
        (((η₁ (x1 n)).toReal + (g1 (x1 n)).toReal : ℝ) : EReal) =
          (((F x[n]).toReal : ℝ) : EReal) := by
      rw [EReal.coe_add, hηcur_val, hg1_cur_val, hFx_val]
      simpa using hcurrE
    exact_mod_cast htmp
  have hopt_real :
      (η₁ xStar.1).toReal + (g1 xStar.1).toReal ≤ FOpt := by
    -- Reattaching the optimal active penalty compares the marginal value with `FOpt`.
    have hoptE :=
      two_block_x1_inactive_marginal_add_active_penalty_le_optimal_value
        (xStar := xStar) (FOpt := FOpt) hFOpt
    have htmp :
        (((η₁ xStar.1).toReal + (g1 xStar.1).toReal : ℝ) : EReal) ≤ (FOpt : EReal) := by
      rw [EReal.coe_add, hηstar_val, hg1_star_val]
      simpa using hoptE
    exact_mod_cast htmp
  have hmarg :
      η₁ xStar.1 ≥
        η₁ (x1 n) +
          (fderiv ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n) (xStar.1 - x1 n) : EReal) := by
    -- The repaired marginal-support bridge supplies the source support step.
    simpa using
      two_block_x1_partial_infimum_support_at_current_iterate
        htraj hx0 hηstar_ne_bot n
  have hderiv_bound :
      fderiv ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n) (xStar.1 - x1 n) ≤
        (η₁ xStar.1).toReal - (η₁ (x1 n)).toReal := by
    -- Rewrite the EReal support inequality into a real derivative bound.
    have hmarg' :
        (((η₁ (x1 n)).toReal +
              fderiv ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n) (xStar.1 - x1 n) : ℝ) : EReal) ≤
          (((η₁ xStar.1).toReal : ℝ) : EReal) := by
      calc
        (((η₁ (x1 n)).toReal +
              fderiv ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n) (xStar.1 - x1 n) : ℝ) : EReal)
            = η₁ (x1 n) +
                (fderiv ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n) (xStar.1 - x1 n) : EReal) := by
                  rw [EReal.coe_add, hηcur_val]
        _ ≤ η₁ xStar.1 := hmarg
        _ = (((η₁ xStar.1).toReal : ℝ) : EReal) := by rw [hηstar_val]
    have hderiv_bound' :
        (η₁ (x1 n)).toReal +
            fderiv ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n) (xStar.1 - x1 n) ≤
          (η₁ xStar.1).toReal := by
      exact_mod_cast hmarg'
    linarith
  have hslice_diff :
      DifferentiableAt ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n) := by
    -- `L₁`-smoothness makes the frozen first-block slice differentiable at the current iterate.
    exact
      (is_l_smooth_on_iff.mp (hproblem.f_x1_smooth (x2 n))).1
        (x1 n) (by simp)
  have htrial_sub :
      y1 - x1 n = t • (xStar.1 - x1 n) := by
    -- The first-block segment trial point moves from `x₁ⁿ` toward `xStar.1` with weight `t`.
    dsimp [y1]
    module
  have hsmooth_raw :
      f (y1, x2 n) ≤
        f (x1 n, x2 n) +
          fderiv ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n) (y1 - x1 n) +
          ((L1 : ℝ) / 2) * ‖x1 n - y1‖ ^ (2 : ℕ) := by
    -- Apply the smooth upper model on the frozen first-block slice.
    simpa [norm_sub_rev] using
      is_l_smooth_on_univ_fderiv_descent
        (hproblem.f_x1_smooth (x2 n)) (x1 n) y1
  have hsmooth :
      f (y1, x2 n) ≤
        f (x1 n, x2 n) +
          t * fderiv ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n) (xStar.1 - x1 n) +
          ((L1 : ℝ) / 2) * ‖x1 n - y1‖ ^ (2 : ℕ) := by
    -- Normalize the trial displacement to the scalar step `t`.
    rw [htrial_sub, map_smul] at hsmooth_raw
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hsmooth_raw
  have hdist_trial :
      ‖x1 n - y1‖ = t * ‖xStar.1 - x1 n‖ := by
    -- The trial displacement is exactly `t` times the current first-block error.
    rw [norm_sub_rev, htrial_sub, norm_smul, Real.norm_of_nonneg ht.1]
  have hfirst_radius :
      ‖xStar.1 - x1 n‖ ≤ (R : ℝ) :=
    two_block_x1_current_first_block_distance_le_radius htraj hx0 hR n
  have hnorm_sq :
      ‖x1 n - y1‖ ^ (2 : ℕ) ≤ t ^ (2 : ℕ) * ((R : ℝ) ^ (2 : ℕ)) := by
    -- The scalar step and the radius bound control the quadratic smoothness term.
    rw [hdist_trial]
    have hmul : t * ‖xStar.1 - x1 n‖ ≤ t * (R : ℝ) :=
      mul_le_mul_of_nonneg_left hfirst_radius ht.1
    have hmul_nonneg : 0 ≤ t * ‖xStar.1 - x1 n‖ := by
      exact mul_nonneg ht.1 (norm_nonneg _)
    have hmulR_nonneg : 0 ≤ t * (R : ℝ) := by
      exact mul_nonneg ht.1 (le_of_lt R.2)
    have hsq : (t * ‖xStar.1 - x1 n‖) ^ (2 : ℕ) ≤ (t * (R : ℝ)) ^ (2 : ℕ) := by
      nlinarith [hmul, hmul_nonneg, hmulR_nonneg]
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq
  have hquad_bound :
      ((L1 : ℝ) / 2) * ‖x1 n - y1‖ ^ (2 : ℕ) ≤
        ((L1 : ℝ) / 2) * t ^ (2 : ℕ) * ((R : ℝ) ^ (2 : ℕ)) := by
    -- Multiply the squared-distance bound by the nonnegative smoothness coefficient.
    have hcoef_nonneg : 0 ≤ (L1 : ℝ) / 2 := by
      have hL1_nonneg : 0 ≤ (L1 : ℝ) := le_of_lt L1.2
      nlinarith
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hnorm_sq hcoef_nonneg
  have hscaled_deriv :
      t * fderiv ℝ (fun z1 ↦ f (z1, x2 n)) (x1 n) (xStar.1 - x1 n) ≤
        t * ((η₁ xStar.1).toReal - (η₁ (x1 n)).toReal) := by
    -- Scale the derivative bound by the nonnegative segment parameter.
    exact mul_le_mul_of_nonneg_left hderiv_bound ht.1
  have hslice_real :
      f (y1, x2 n) + (g2 (x2 n)).toReal ≤
        (1 - t) * (η₁ (x1 n)).toReal + t * (η₁ xStar.1).toReal +
          ((L1 : ℝ) / 2) * t ^ (2 : ℕ) * ((R : ℝ) ^ (2 : ℕ)) := by
    -- Reexpress the smooth upper model through the current and optimal marginal values.
    linarith [hsmooth, hscaled_deriv, hηcur_real, hquad_bound]
  have hconv_raw :
      g1 y1 ≤ ((1 - t : ℝ) : EReal) * g1 (x1 n) + (t : EReal) * g1 xStar.1 := by
    -- Convexity of `g₁` controls the trial penalty by the endpoint penalties.
    have hseg :=
      (is_convex_function_iff_segment_ineq.mp hproblem.g1_convex)
        xStar.1 hg1_star_eff (x1 n) hg1_cur_eff ht
    simpa [y1, add_assoc, add_left_comm, add_comm] using hseg
  have hconv_rhs_val :
      ((1 - t : ℝ) : EReal) * g1 (x1 n) + (t : EReal) * g1 xStar.1 =
        ((((1 - t) * (g1 (x1 n)).toReal + t * (g1 xStar.1).toReal : ℝ)) : EReal) := by
    -- The convex combination of the two finite endpoint penalties is again finite.
    rw [← hg1_cur_val, ← hg1_star_val, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    simp [mul_comm]
  have hconv_rhs_ne_top :
      ((1 - t : ℝ) : EReal) * g1 (x1 n) + (t : EReal) * g1 xStar.1 ≠ ⊤ := by
    rw [hconv_rhs_val]
    exact EReal.coe_ne_top _
  have hg1_trial_ne_top : g1 y1 ≠ ⊤ := by
    -- The trial penalty lies below a finite convex combination, so it is finite as well.
    intro htop
    have htop_rhs :
        ((1 - t : ℝ) : EReal) * g1 (x1 n) + (t : EReal) * g1 xStar.1 = ⊤ := by
      have : (⊤ : EReal) ≤ ((1 - t : ℝ) : EReal) * g1 (x1 n) + (t : EReal) * g1 xStar.1 := by
        simpa [htop] using hconv_raw
      exact top_unique this
    exact hconv_rhs_ne_top htop_rhs
  have hg1_trial_val :
      (((g1 y1).toReal : ℝ) : EReal) = g1 y1 := by
    exact EReal.coe_toReal hg1_trial_ne_top (hproblem.g1_proper.ne_bot y1)
  have hg1_convex_real :
      (g1 y1).toReal ≤
        (1 - t) * (g1 (x1 n)).toReal + t * (g1 xStar.1).toReal := by
    -- Convert the convex EReal penalty bound into a real inequality.
    have hconv_toReal :
        (g1 y1).toReal ≤
          (((1 - t : ℝ) : EReal) * g1 (x1 n) + (t : EReal) * g1 xStar.1).toReal :=
      EReal.toReal_le_toReal
        hconv_raw
        (hproblem.g1_proper.ne_bot y1)
        hconv_rhs_ne_top
    rw [hconv_rhs_val] at hconv_toReal
    simpa using hconv_toReal
  have htrial_real :
      f (y1, x2 n) + (g2 (x2 n)).toReal + (g1 y1).toReal ≤
        (1 - t) * (F x[n]).toReal + t * FOpt +
          ((L1 : ℝ) / 2) * t ^ (2 : ℕ) * ((R : ℝ) ^ (2 : ℕ)) := by
    -- Combine the smooth-slice estimate, the convex penalty bound, and the current/optimal
    -- reattachment formulas.
    have hsum :
        f (y1, x2 n) + (g2 (x2 n)).toReal + (g1 y1).toReal ≤
          (1 - t) * ((η₁ (x1 n)).toReal + (g1 (x1 n)).toReal) +
            t * ((η₁ xStar.1).toReal + (g1 xStar.1).toReal) +
              ((L1 : ℝ) / 2) * t ^ (2 : ℕ) * ((R : ℝ) ^ (2 : ℕ)) := by
      linarith [hslice_real, hg1_convex_real]
    have hcurrent_scaled :
        (1 - t) * ((η₁ (x1 n)).toReal + (g1 (x1 n)).toReal) =
          (1 - t) * (F x[n]).toReal := by
      rw [hcurrent_real]
    have hopt_scaled :
        t * ((η₁ xStar.1).toReal + (g1 xStar.1).toReal) ≤ t * FOpt := by
      exact mul_le_mul_of_nonneg_left hopt_real ht.1
    calc
      f (y1, x2 n) + (g2 (x2 n)).toReal + (g1 y1).toReal
          ≤ (1 - t) * ((η₁ (x1 n)).toReal + (g1 (x1 n)).toReal) +
              t * ((η₁ xStar.1).toReal + (g1 xStar.1).toReal) +
                ((L1 : ℝ) / 2) * t ^ (2 : ℕ) * ((R : ℝ) ^ (2 : ℕ)) := hsum
      _ = (1 - t) * (F x[n]).toReal +
            t * ((η₁ xStar.1).toReal + (g1 xStar.1).toReal) +
              ((L1 : ℝ) / 2) * t ^ (2 : ℕ) * ((R : ℝ) ^ (2 : ℕ)) := by
            rw [hcurrent_scaled]
      _ ≤ (1 - t) * (F x[n]).toReal + t * FOpt +
            ((L1 : ℝ) / 2) * t ^ (2 : ℕ) * ((R : ℝ) ^ (2 : ℕ)) := by
            linarith
  have htrial_val :
      F (y1, x2 n) =
        (((f (y1, x2 n) + (g2 (x2 n)).toReal + (g1 y1).toReal : ℝ)) : EReal) := by
    -- The trial objective is finite, so rewrite it as a real-valued sum.
    rw [two_block_alternating_minimization_objective_apply, ← hg1_trial_val, ← hg2_cur_val]
    simp [add_left_comm, add_comm]
  have hmin :
      F xHalf ≤ F (y1, x2 n) := by
    -- Exact minimization of the first-block subproblem compares the half-step against the trial
    -- segment point.
    have hstep :
        IsMinOn
          (two_block_alternating_minimization_x1_objective f.toEReal g1 g2 (x2 n))
          Set.univ
          (x1 (n + 1)) := by
      simpa [Nat.succ_eq_add_one] using htraj.step_x1 n
    simpa [xHalf, two_block_alternating_minimization_half_step] using
      (isMinOn_iff.mp hstep) y1 (by simp)
  have hboundE :
      (((F xHalf).toReal : ℝ) : EReal) ≤
        (((1 - t) * (F x[n]).toReal + t * FOpt +
            ((L1 : ℝ) / 2) * t ^ (2 : ℕ) * ((R : ℝ) ^ (2 : ℕ)) : ℝ) : EReal) := by
    -- Transport the exact-minimization comparison through the finite real trial bound.
    rw [hFHalf_val]
    exact le_trans hmin <| by
      rw [htrial_val]
      exact EReal.coe_le_coe htrial_real
  have hbound :
      (F xHalf).toReal ≤
        (1 - t) * (F x[n]).toReal + t * FOpt +
          ((L1 : ℝ) / 2) * t ^ (2 : ℕ) * ((R : ℝ) ^ (2 : ℕ)) := by
    exact_mod_cast hboundE
  -- Rearranging the affine upper bound gives the displayed half-step gap estimate.
  linarith

/-- Helper for Theorem 14.8: the source `x₂`-branch compares the exact next iterate against the
segment trial point toward `xStar.2`, giving the affine-quadratic estimate in the trial
parameter `t`. -/
lemma two_block_x2_next_gap_le_affine_quadratic
    [hproblem : IsTwoBlockAlternatingMinimizationConvexRateProblem f g1 g2 XStar FOpt L1 L2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hxStar : IsMinOn F Set.univ xStar)
    (hFOpt : F xStar = (FOpt : EReal))
    (hx0 : x[0] ∈ effective_domain F)
    (hR :
      ∀ ⦃y : E1 × E2⦄,
        F y ≤ F x[0] →
        ‖y - xStar‖ ≤ (R : ℝ))
    (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    let xHalf := two_block_alternating_minimization_half_step x1 x2 n
    ((F x[n + 1]).toReal - FOpt) ≤
      (1 - t) * ((F xHalf).toReal - FOpt) +
        (((L2 : ℝ) / 2) * t ^ (2 : ℕ) * ((R : ℝ) ^ (2 : ℕ))) := by
  let xHalf := two_block_alternating_minimization_half_step x1 x2 n
  let y2 : E2 := (1 - t) • x2 n + t • xStar.2
  have hhalf :=
    two_block_half_step_mem_effective_domain_and_initial_sublevel
      htraj hx0 n
  have hnext :=
    two_block_iterates_mem_effective_domain_and_initial_sublevel
      htraj hx0 (n + 1)
  have hFHalf_val :
      (((F xHalf).toReal : ℝ) : EReal) = F xHalf := by
    -- The half-step objective is finite.
    exact
      EReal.coe_toReal
        (mem_effective_domain.mp hhalf.1).ne
        (two_block_objective_ne_bot xHalf)
  have hFNext_val :
      (((F x[n + 1]).toReal : ℝ) : EReal) = F x[n + 1] := by
    -- The next iterate objective is finite as well.
    exact
      EReal.coe_toReal
        (mem_effective_domain.mp hnext.1).ne
        (two_block_objective_ne_bot x[n + 1])
  have hxStar_mem : xStar ∈ effective_domain F :=
    two_block_optimal_point_mem_effective_domain hFOpt
  have hg2_cur_eff :
      x2 n ∈ effective_domain g2 :=
    two_block_second_penalty_mem_effective_domain_of_objective_mem hhalf.1
  have hg2_star_eff :
      xStar.2 ∈ effective_domain g2 :=
    two_block_second_penalty_mem_effective_domain_of_objective_mem hxStar_mem
  have hg1_half_eff :
      x1 (n + 1) ∈ effective_domain g1 :=
    two_block_first_penalty_mem_effective_domain_of_objective_mem hhalf.1
  have hg2_cur_val :
      (((g2 (x2 n)).toReal : ℝ) : EReal) = g2 (x2 n) := by
    simpa [xHalf, two_block_alternating_minimization_half_step] using
      two_block_second_penalty_eq_coe_toReal_of_mem_effective_domain hhalf.1
  have hg2_star_val :
      (((g2 xStar.2).toReal : ℝ) : EReal) = g2 xStar.2 :=
    two_block_second_penalty_eq_coe_toReal_of_mem_effective_domain hxStar_mem
  have hg1_half_val :
      (((g1 (x1 (n + 1))).toReal : ℝ) : EReal) = g1 (x1 (n + 1)) := by
    simpa [xHalf, two_block_alternating_minimization_half_step] using
      two_block_first_penalty_eq_coe_toReal_of_mem_effective_domain hhalf.1
  have hηstar_ne_bot : η₂ xStar.2 ≠ ⊥ := by
    -- The optimal witness representation also makes the second inactive marginal finite below.
    rw [two_block_x2_inactive_marginal_eq_optimal_witness_value hxStar hFOpt]
    exact (EReal.add_ne_bot_iff).2 ⟨by simp, hproblem.g1_proper.ne_bot xStar.1⟩
  have hηcur_eq :
      η₂ (x2 n) = (((f (x1 (n + 1), x2 n) : ℝ) : EReal)) + g1 (x1 (n + 1)) := by
    -- Rewrite the half-step inactive marginal through the attained first-block witness.
    simpa using two_block_x2_inactive_marginal_eq_current_value htraj hx0 n
  have hηstar_eq :
      η₂ xStar.2 = (((f xStar : ℝ) : EReal)) + g1 xStar.1 := by
    -- Rewrite the optimal second inactive marginal through the optimal first-block witness.
    simpa using two_block_x2_inactive_marginal_eq_optimal_witness_value hxStar hFOpt
  have hηcur_ne_top : η₂ (x2 n) ≠ ⊤ := by
    -- The half-step inactive marginal is represented by finite data.
    rw [hηcur_eq]
    exact
      (EReal.add_ne_top_iff_ne_top_right
        (x := (((f (x1 (n + 1), x2 n) : ℝ) : EReal)))
        (y := g1 (x1 (n + 1)))
        (by simp)
        (by simp)).2
        (mem_effective_domain.mp hg1_half_eff).ne
  have hηcur_ne_bot : η₂ (x2 n) ≠ ⊥ := by
    rw [hηcur_eq]
    exact (EReal.add_ne_bot_iff).2 ⟨by simp, hproblem.g1_proper.ne_bot (x1 (n + 1))⟩
  have hηstar_ne_top : η₂ xStar.2 ≠ ⊤ := by
    have hg1_star_eff :
        xStar.1 ∈ effective_domain g1 :=
      two_block_first_penalty_mem_effective_domain_of_objective_mem hxStar_mem
    rw [hηstar_eq]
    exact
      (EReal.add_ne_top_iff_ne_top_right
        (x := (((f xStar : ℝ) : EReal)))
        (y := g1 xStar.1)
        (by simp)
        (by simp)).2
        (mem_effective_domain.mp hg1_star_eff).ne
  have hηcur_val :
      (((η₂ (x2 n)).toReal : ℝ) : EReal) = η₂ (x2 n) := by
    exact EReal.coe_toReal hηcur_ne_top hηcur_ne_bot
  have hηstar_val :
      (((η₂ xStar.2).toReal : ℝ) : EReal) = η₂ xStar.2 := by
    exact EReal.coe_toReal hηstar_ne_top hηstar_ne_bot
  have hηcur_real :
      (η₂ (x2 n)).toReal = f (x1 (n + 1), x2 n) + (g1 (x1 (n + 1))).toReal := by
    -- Convert the attained half-step marginal identity to a real equality.
    have htmp := congrArg EReal.toReal hηcur_eq
    rw [EReal.toReal_add (EReal.coe_ne_top _) (EReal.coe_ne_bot _)
      (mem_effective_domain.mp hg1_half_eff).ne
      (hproblem.g1_proper.ne_bot (x1 (n + 1)))] at htmp
    simpa using htmp
  have hhalf_real :
      (η₂ (x2 n)).toReal + (g2 (x2 n)).toReal = (F xHalf).toReal := by
    -- Reattaching the inactive penalty recovers the half-step objective.
    have hcurrE :=
      x2_marginal_add_penalty_eq_half_step_objective
        htraj hx0 n
    have htmp :
        (((η₂ (x2 n)).toReal + (g2 (x2 n)).toReal : ℝ) : EReal) =
          (((F xHalf).toReal : ℝ) : EReal) := by
      rw [EReal.coe_add, hηcur_val, hg2_cur_val, hFHalf_val]
      simpa [xHalf] using hcurrE
    exact_mod_cast htmp
  have hopt_real :
      (η₂ xStar.2).toReal + (g2 xStar.2).toReal ≤ FOpt := by
    -- The optimal reattachment bounds the second inactive marginal by `FOpt`.
    have hoptE :=
      two_block_x2_inactive_marginal_add_inactive_penalty_le_optimal_value
        (xStar := xStar) (FOpt := FOpt) hFOpt
    have htmp :
        (((η₂ xStar.2).toReal + (g2 xStar.2).toReal : ℝ) : EReal) ≤ (FOpt : EReal) := by
      rw [EReal.coe_add, hηstar_val, hg2_star_val]
      simpa using hoptE
    exact_mod_cast htmp
  have hmarg :
      η₂ xStar.2 ≥
        η₂ (x2 n) +
          (fderiv ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n) (xStar.2 - x2 n) : EReal) := by
    -- Use the symmetric repaired marginal-support bridge at the half-step base point.
    simpa using
      two_block_x2_partial_infimum_support_at_half_step
        htraj hx0 hηstar_ne_bot n
  have hderiv_bound :
      fderiv ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n) (xStar.2 - x2 n) ≤
        (η₂ xStar.2).toReal - (η₂ (x2 n)).toReal := by
    -- Convert the EReal support inequality into a real derivative bound.
    have hmarg' :
        (((η₂ (x2 n)).toReal +
              fderiv ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n) (xStar.2 - x2 n) : ℝ) : EReal) ≤
          (((η₂ xStar.2).toReal : ℝ) : EReal) := by
      calc
        (((η₂ (x2 n)).toReal +
              fderiv ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n) (xStar.2 - x2 n) : ℝ) : EReal)
            = η₂ (x2 n) +
                (fderiv ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n) (xStar.2 - x2 n) : EReal) := by
                  rw [EReal.coe_add, hηcur_val]
        _ ≤ η₂ xStar.2 := hmarg
        _ = (((η₂ xStar.2).toReal : ℝ) : EReal) := by rw [hηstar_val]
    have hderiv_bound' :
        (η₂ (x2 n)).toReal +
            fderiv ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n) (xStar.2 - x2 n) ≤
          (η₂ xStar.2).toReal := by
      exact_mod_cast hmarg'
    linarith
  have hslice_diff :
      DifferentiableAt ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n) := by
    -- `L₂`-smoothness makes the frozen second-block slice differentiable at the half-step base.
    exact
      (is_l_smooth_on_iff.mp (hproblem.f_x2_smooth (x1 (n + 1)))).1
        (x2 n) (by simp)
  have htrial_sub :
      y2 - x2 n = t • (xStar.2 - x2 n) := by
    -- The second-block segment trial point moves from `x₂ⁿ` toward `xStar.2` with weight `t`.
    dsimp [y2]
    module
  have hsmooth_raw :
      f (x1 (n + 1), y2) ≤
        f (x1 (n + 1), x2 n) +
          fderiv ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n) (y2 - x2 n) +
          ((L2 : ℝ) / 2) * ‖x2 n - y2‖ ^ (2 : ℕ) := by
    -- Apply the smooth upper model on the frozen second-block slice.
    simpa [norm_sub_rev] using
      is_l_smooth_on_univ_fderiv_descent
        (hproblem.f_x2_smooth (x1 (n + 1))) (x2 n) y2
  have hsmooth :
      f (x1 (n + 1), y2) ≤
        f (x1 (n + 1), x2 n) +
          t * fderiv ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n) (xStar.2 - x2 n) +
          ((L2 : ℝ) / 2) * ‖x2 n - y2‖ ^ (2 : ℕ) := by
    -- Normalize the trial displacement to the scalar step `t`.
    rw [htrial_sub, map_smul] at hsmooth_raw
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hsmooth_raw
  have hdist_trial :
      ‖x2 n - y2‖ = t * ‖xStar.2 - x2 n‖ := by
    -- The second-block trial displacement is again exactly scaled by `t`.
    rw [norm_sub_rev, htrial_sub, norm_smul, Real.norm_of_nonneg ht.1]
  have hsecond_radius :
      ‖xStar.2 - x2 n‖ ≤ (R : ℝ) := by
    -- The half-step pair already lies in the initial sublevel, so the second coordinate is within
    -- the same radius.
    have hcoord :
        ‖x2 n - xStar.2‖ ≤ ‖xHalf - xStar‖ := by
      calc
        ‖x2 n - xStar.2‖
            ≤ max ‖x1 (n + 1) - xStar.1‖ ‖x2 n - xStar.2‖ := le_max_right _ _
        _ = ‖xHalf - xStar‖ := by
              simp [xHalf, two_block_alternating_minimization_half_step, Prod.norm_def]
    calc
      ‖xStar.2 - x2 n‖ = ‖x2 n - xStar.2‖ := norm_sub_rev _ _
      _ ≤ ‖xHalf - xStar‖ := hcoord
      _ ≤ (R : ℝ) := hR hhalf.2
  have hnorm_sq :
      ‖x2 n - y2‖ ^ (2 : ℕ) ≤ t ^ (2 : ℕ) * ((R : ℝ) ^ (2 : ℕ)) := by
    -- The same scalar-step and radius control bounds the quadratic term on the second block.
    rw [hdist_trial]
    have hmul : t * ‖xStar.2 - x2 n‖ ≤ t * (R : ℝ) :=
      mul_le_mul_of_nonneg_left hsecond_radius ht.1
    have hmul_nonneg : 0 ≤ t * ‖xStar.2 - x2 n‖ := by
      exact mul_nonneg ht.1 (norm_nonneg _)
    have hmulR_nonneg : 0 ≤ t * (R : ℝ) := by
      exact mul_nonneg ht.1 (le_of_lt R.2)
    have hsq : (t * ‖xStar.2 - x2 n‖) ^ (2 : ℕ) ≤ (t * (R : ℝ)) ^ (2 : ℕ) := by
      nlinarith [hmul, hmul_nonneg, hmulR_nonneg]
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq
  have hquad_bound :
      ((L2 : ℝ) / 2) * ‖x2 n - y2‖ ^ (2 : ℕ) ≤
        ((L2 : ℝ) / 2) * t ^ (2 : ℕ) * ((R : ℝ) ^ (2 : ℕ)) := by
    -- Multiply the squared-distance bound by the nonnegative `L₂ / 2` coefficient.
    have hcoef_nonneg : 0 ≤ (L2 : ℝ) / 2 := by
      have hL2_nonneg : 0 ≤ (L2 : ℝ) := le_of_lt L2.2
      nlinarith
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hnorm_sq hcoef_nonneg
  have hscaled_deriv :
      t * fderiv ℝ (fun z2 ↦ f (x1 (n + 1), z2)) (x2 n) (xStar.2 - x2 n) ≤
        t * ((η₂ xStar.2).toReal - (η₂ (x2 n)).toReal) := by
    -- Scale the derivative bound by the nonnegative segment parameter.
    exact mul_le_mul_of_nonneg_left hderiv_bound ht.1
  have hslice_real :
      f (x1 (n + 1), y2) + (g1 (x1 (n + 1))).toReal ≤
        (1 - t) * (η₂ (x2 n)).toReal + t * (η₂ xStar.2).toReal +
          ((L2 : ℝ) / 2) * t ^ (2 : ℕ) * ((R : ℝ) ^ (2 : ℕ)) := by
    -- Reexpress the smooth upper model through the current and optimal second inactive marginals.
    linarith [hsmooth, hscaled_deriv, hηcur_real, hquad_bound]
  have hconv_raw :
      g2 y2 ≤ ((1 - t : ℝ) : EReal) * g2 (x2 n) + (t : EReal) * g2 xStar.2 := by
    -- Convexity of `g₂` controls the second-block trial penalty.
    have hseg :=
      (is_convex_function_iff_segment_ineq.mp hproblem.g2_convex)
        xStar.2 hg2_star_eff (x2 n) hg2_cur_eff ht
    simpa [y2, add_assoc, add_left_comm, add_comm] using hseg
  have hconv_rhs_val :
      ((1 - t : ℝ) : EReal) * g2 (x2 n) + (t : EReal) * g2 xStar.2 =
        ((((1 - t) * (g2 (x2 n)).toReal + t * (g2 xStar.2).toReal : ℝ)) : EReal) := by
    -- The convex combination of the finite endpoint penalties is finite.
    rw [← hg2_cur_val, ← hg2_star_val, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    simp [mul_comm]
  have hconv_rhs_ne_top :
      ((1 - t : ℝ) : EReal) * g2 (x2 n) + (t : EReal) * g2 xStar.2 ≠ ⊤ := by
    rw [hconv_rhs_val]
    exact EReal.coe_ne_top _
  have hg2_trial_ne_top : g2 y2 ≠ ⊤ := by
    -- The trial inactive penalty lies below a finite convex combination.
    intro htop
    have htop_rhs :
        ((1 - t : ℝ) : EReal) * g2 (x2 n) + (t : EReal) * g2 xStar.2 = ⊤ := by
      have : (⊤ : EReal) ≤ ((1 - t : ℝ) : EReal) * g2 (x2 n) + (t : EReal) * g2 xStar.2 := by
        simpa [htop] using hconv_raw
      exact top_unique this
    exact hconv_rhs_ne_top htop_rhs
  have hg2_trial_val :
      (((g2 y2).toReal : ℝ) : EReal) = g2 y2 := by
    exact EReal.coe_toReal hg2_trial_ne_top (hproblem.g2_proper.ne_bot y2)
  have hg2_convex_real :
      (g2 y2).toReal ≤
        (1 - t) * (g2 (x2 n)).toReal + t * (g2 xStar.2).toReal := by
    -- Convert the convex EReal penalty bound into a real inequality.
    have hconv_toReal :
        (g2 y2).toReal ≤
          (((1 - t : ℝ) : EReal) * g2 (x2 n) + (t : EReal) * g2 xStar.2).toReal :=
      EReal.toReal_le_toReal
        hconv_raw
        (hproblem.g2_proper.ne_bot y2)
        hconv_rhs_ne_top
    rw [hconv_rhs_val] at hconv_toReal
    simpa using hconv_toReal
  have htrial_real :
      f (x1 (n + 1), y2) + (g1 (x1 (n + 1))).toReal + (g2 y2).toReal ≤
        (1 - t) * (F xHalf).toReal + t * FOpt +
          ((L2 : ℝ) / 2) * t ^ (2 : ℕ) * ((R : ℝ) ^ (2 : ℕ)) := by
    -- Combine the smooth-slice estimate, the convex penalty bound, and the half-step/optimal
    -- reattachment formulas.
    have hsum :
        f (x1 (n + 1), y2) + (g1 (x1 (n + 1))).toReal + (g2 y2).toReal ≤
          (1 - t) * ((η₂ (x2 n)).toReal + (g2 (x2 n)).toReal) +
            t * ((η₂ xStar.2).toReal + (g2 xStar.2).toReal) +
              ((L2 : ℝ) / 2) * t ^ (2 : ℕ) * ((R : ℝ) ^ (2 : ℕ)) := by
      linarith [hslice_real, hg2_convex_real]
    have hhalf_scaled :
        (1 - t) * ((η₂ (x2 n)).toReal + (g2 (x2 n)).toReal) =
          (1 - t) * (F xHalf).toReal := by
      rw [hhalf_real]
    have hopt_scaled :
        t * ((η₂ xStar.2).toReal + (g2 xStar.2).toReal) ≤ t * FOpt := by
      exact mul_le_mul_of_nonneg_left hopt_real ht.1
    calc
      f (x1 (n + 1), y2) + (g1 (x1 (n + 1))).toReal + (g2 y2).toReal
          ≤ (1 - t) * ((η₂ (x2 n)).toReal + (g2 (x2 n)).toReal) +
              t * ((η₂ xStar.2).toReal + (g2 xStar.2).toReal) +
                ((L2 : ℝ) / 2) * t ^ (2 : ℕ) * ((R : ℝ) ^ (2 : ℕ)) := hsum
      _ = (1 - t) * (F xHalf).toReal +
            t * ((η₂ xStar.2).toReal + (g2 xStar.2).toReal) +
              ((L2 : ℝ) / 2) * t ^ (2 : ℕ) * ((R : ℝ) ^ (2 : ℕ)) := by
            rw [hhalf_scaled]
      _ ≤ (1 - t) * (F xHalf).toReal + t * FOpt +
            ((L2 : ℝ) / 2) * t ^ (2 : ℕ) * ((R : ℝ) ^ (2 : ℕ)) := by
            linarith
  have htrial_val :
      F (x1 (n + 1), y2) =
        (((f (x1 (n + 1), y2) + (g1 (x1 (n + 1))).toReal + (g2 y2).toReal : ℝ)) : EReal) := by
    -- The trial objective is finite, so rewrite it as a real-valued sum.
    rw [two_block_alternating_minimization_objective_apply, ← hg1_half_val, ← hg2_trial_val]
    simp [add_left_comm, add_comm]
  have hmin :
      F x[n + 1] ≤ F (x1 (n + 1), y2) := by
    -- Exact minimization of the second-block subproblem compares the next iterate against the
    -- second-block segment trial point.
    have hstep :
        IsMinOn
          (two_block_alternating_minimization_x2_objective f.toEReal g1 g2 (x1 (n + 1)))
          Set.univ
          (x2 (n + 1)) := by
      simpa [Nat.succ_eq_add_one] using htraj.step_x2 n
    simpa [two_block_alternating_minimization_objective_apply, add_assoc, add_left_comm, add_comm]
      using (isMinOn_iff.mp hstep) y2 (by simp)
  have hboundE :
      (((F x[n + 1]).toReal : ℝ) : EReal) ≤
        (((1 - t) * (F xHalf).toReal + t * FOpt +
            ((L2 : ℝ) / 2) * t ^ (2 : ℕ) * ((R : ℝ) ^ (2 : ℕ)) : ℝ) : EReal) := by
    -- Transport the exact-minimization comparison through the finite real trial bound.
    rw [hFNext_val]
    exact le_trans hmin <| by
      rw [htrial_val]
      exact EReal.coe_le_coe htrial_real
  have hbound :
      (F x[n + 1]).toReal ≤
        (1 - t) * (F xHalf).toReal + t * FOpt +
          ((L2 : ℝ) / 2) * t ^ (2 : ℕ) * ((R : ℝ) ^ (2 : ℕ)) := by
    exact_mod_cast hboundE
  -- Rearranging the affine upper bound gives the displayed next-iterate gap estimate.
  linarith

/-- Helper for Theorem 14.8: optimizing an affine-quadratic upper bound
`a ≤ (1 - t) b + c t^2` over `t ∈ [0, 1]` yields the quadratic-gap lower bound
`b - a ≥ a^2 / (4 c)` when `c > 0` and `a ≥ 0`. -/
private lemma twoBlockAffineQuadraticGap_of_segmentUpperBound
    {a b c : ℝ}
    (hc : 0 < c)
    (ha_nonneg : 0 ≤ a)
    (hbound :
      ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 →
        a ≤ (1 - t) * b + c * t ^ (2 : ℕ)) :
    b - a ≥ a ^ (2 : ℕ) / (4 * c) := by
  have hba : a ≤ b := by
    simpa using hbound (by simp : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
  have hac : a ≤ c := by
    simpa using hbound (by simp : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
  let t : ℝ := a / (2 * c)
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    positivity
  have ht_le_one : t ≤ 1 := by
    have htwo : a ≤ 2 * c := by
      nlinarith [hac, hc]
    have hden_pos : 0 < 2 * c := by positivity
    exact (div_le_iff₀ hden_pos).2 <| by
      simpa [t] using htwo
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht_nonneg, ht_le_one⟩
  have hstep : a ≤ (1 - t) * b + c * t ^ (2 : ℕ) := hbound ht
  have htb : -t * b ≤ -t * a := by
    have hmul := mul_le_mul_of_nonneg_left hba ht_nonneg
    linarith
  have hstep' : a ≤ b - t * a + c * t ^ (2 : ℕ) := by
    linarith
  have hrewrite :
      b - t * a + c * t ^ (2 : ℕ) = b - a ^ (2 : ℕ) / (4 * c) := by
    have hc_ne : c ≠ 0 := hc.ne'
    dsimp [t]
    field_simp [hc_ne]
    ring
  rw [hrewrite] at hstep'
  linarith

/-- Helper for Theorem 14.8: the source equation `(14.35)` is the `x₁`-half-step quadratic gap
estimate. -/
lemma two_block_x1_half_step_quadratic_gap
    [hproblem : IsTwoBlockAlternatingMinimizationConvexRateProblem f g1 g2 XStar FOpt L1 L2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hxStar : IsMinOn F Set.univ xStar)
    (hFOpt : F xStar = (FOpt : EReal))
    (hx0 : x[0] ∈ effective_domain F)
    (hR :
      ∀ ⦃y : E1 × E2⦄,
        F y ≤ F x[0] →
        ‖y - xStar‖ ≤ (R : ℝ))
    (n : ℕ) :
    let xHalf := two_block_alternating_minimization_half_step x1 x2 n
    ((F x[n]).toReal - FOpt) - ((F xHalf).toReal - FOpt) ≥
      (1 / (2 * (L1 : ℝ) * ((R : ℝ) ^ (2 : ℕ)))) *
        (((F xHalf).toReal - FOpt) ^ (2 : ℕ)) := by
  let xHalf := two_block_alternating_minimization_half_step x1 x2 n
  let a : ℝ := (F xHalf).toReal - FOpt
  let b : ℝ := (F x[n]).toReal - FOpt
  let c : ℝ := ((L1 : ℝ) / 2) * ((R : ℝ) ^ (2 : ℕ))
  have ha_nonneg : 0 ≤ a := by
    -- The half-step objective still lies above the optimal value.
    have hhalf :=
      two_block_half_step_mem_effective_domain_and_initial_sublevel
        htraj hx0 n
    have hFHalf_val :
        (((F xHalf).toReal : ℝ) : EReal) = F xHalf := by
      exact
        EReal.coe_toReal
          (mem_effective_domain.mp hhalf.1).ne
          (two_block_objective_ne_bot xHalf)
    have hFOpt_le :
        (FOpt : EReal) ≤ (((F xHalf).toReal : ℝ) : EReal) := by
      calc
        (FOpt : EReal) = F xStar := by simpa using hFOpt.symm
        _ ≤ F xHalf := (isMinOn_iff.mp hxStar) xHalf (by simp)
        _ = (((F xHalf).toReal : ℝ) : EReal) := hFHalf_val.symm
    have hFOpt_le_real : FOpt ≤ (F xHalf).toReal := by
      exact_mod_cast hFOpt_le
    simpa [a] using sub_nonneg.mpr hFOpt_le_real
  have hc : 0 < c := by
    -- The affine-quadratic coefficient is strictly positive.
    have hL1_pos : 0 < (L1 : ℝ) := L1.2
    have hR_sq_pos : 0 < ((R : ℝ) ^ (2 : ℕ)) := by
      simpa [pow_two] using sq_pos_of_pos (show 0 < (R : ℝ) from R.2)
    dsimp [c]
    nlinarith
  have hbound :
      ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 →
        a ≤ (1 - t) * b + c * t ^ (2 : ℕ) := by
    intro t ht
    -- The affine-quadratic half-step estimate provides the hypothesis for the scalar optimizer.
    simpa [a, b, c, xHalf, mul_assoc, mul_left_comm, mul_comm] using
      two_block_x1_half_step_gap_le_affine_quadratic
        htraj hxStar hFOpt hx0 hR n t ht
  have hgap :
      b - a ≥ a ^ (2 : ℕ) / (4 * c) :=
    twoBlockAffineQuadraticGap_of_segmentUpperBound hc ha_nonneg hbound
  have hcoeff :
      a ^ (2 : ℕ) / (4 * c) =
        (1 / (2 * (L1 : ℝ) * ((R : ℝ) ^ (2 : ℕ)))) * (a ^ (2 : ℕ)) := by
    have hc_ne : c ≠ 0 := hc.ne'
    dsimp [c]
    field_simp [hc_ne]
    ring
  rw [hcoeff] at hgap
  -- Re-expand the scalar variables to recover the source quadratic-gap statement.
  simpa [a, b, xHalf]
    using hgap

/-- Helper for Theorem 14.8: the source equation `(14.36)` contributes the `x₂`-next-step
quadratic gap estimate. -/
lemma two_block_x2_next_step_quadratic_gap
    [hproblem : IsTwoBlockAlternatingMinimizationConvexRateProblem f g1 g2 XStar FOpt L1 L2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hxStar : IsMinOn F Set.univ xStar)
    (hFOpt : F xStar = (FOpt : EReal))
    (hx0 : x[0] ∈ effective_domain F)
    (hR :
      ∀ ⦃y : E1 × E2⦄,
        F y ≤ F x[0] →
        ‖y - xStar‖ ≤ (R : ℝ))
    (n : ℕ) :
    let xHalf := two_block_alternating_minimization_half_step x1 x2 n
    ((F xHalf).toReal - FOpt) - ((F x[n + 1]).toReal - FOpt) ≥
      (1 / (2 * (L2 : ℝ) * ((R : ℝ) ^ (2 : ℕ)))) *
        (((F x[n + 1]).toReal - FOpt) ^ (2 : ℕ)) := by
  let xHalf := two_block_alternating_minimization_half_step x1 x2 n
  let a : ℝ := (F x[n + 1]).toReal - FOpt
  let b : ℝ := (F xHalf).toReal - FOpt
  let c : ℝ := ((L2 : ℝ) / 2) * ((R : ℝ) ^ (2 : ℕ))
  have ha_nonneg : 0 ≤ a := by
    -- The next iterate objective also lies above the optimal value.
    exact two_block_objective_gap_nonneg_of_problem htraj hxStar hFOpt hx0 (n + 1)
  have hc : 0 < c := by
    -- The second affine-quadratic coefficient is strictly positive.
    have hL2_pos : 0 < (L2 : ℝ) := L2.2
    have hR_sq_pos : 0 < ((R : ℝ) ^ (2 : ℕ)) := by
      simpa [pow_two] using sq_pos_of_pos (show 0 < (R : ℝ) from R.2)
    dsimp [c]
    nlinarith
  have hbound :
      ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 →
        a ≤ (1 - t) * b + c * t ^ (2 : ℕ) := by
    intro t ht
    -- The symmetric affine-quadratic next-iterate estimate feeds the same scalar optimizer.
    simpa [a, b, c, xHalf, mul_assoc, mul_left_comm, mul_comm] using
      two_block_x2_next_gap_le_affine_quadratic
        htraj hxStar hFOpt hx0 hR n t ht
  have hgap :
      b - a ≥ a ^ (2 : ℕ) / (4 * c) :=
    twoBlockAffineQuadraticGap_of_segmentUpperBound hc ha_nonneg hbound
  have hcoeff :
      a ^ (2 : ℕ) / (4 * c) =
        (1 / (2 * (L2 : ℝ) * ((R : ℝ) ^ (2 : ℕ)))) * (a ^ (2 : ℕ)) := by
    have hc_ne : c ≠ 0 := hc.ne'
    dsimp [c]
    field_simp [hc_ne]
    ring
  rw [hcoeff] at hgap
  -- Re-expand the scalar variables to recover the symmetric quadratic-gap statement.
  simpa [a, b, xHalf]
    using hgap

/-- Helper for Theorem 14.8: the source proof's real work is the quadratic one-step recurrence
for the two-block objective-gap sequence. -/
lemma two_block_objective_gap_quadratic_recurrence
    [hproblem : IsTwoBlockAlternatingMinimizationConvexRateProblem f g1 g2 XStar FOpt L1 L2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hxStar : IsMinOn F Set.univ xStar)
    (hFOpt : F xStar = (FOpt : EReal))
    (hx0 : x[0] ∈ effective_domain F)
    (hR :
      ∀ ⦃y : E1 × E2⦄,
        F y ≤ F x[0] →
        ‖y - xStar‖ ≤ (R : ℝ))
    (n : ℕ) :
    ((F x[n]).toReal - FOpt) - ((F x[n + 1]).toReal - FOpt) ≥
      (1 / (2 * min (L1 : ℝ) (L2 : ℝ) * ((R : ℝ) ^ (2 : ℕ)))) *
        (((F x[n + 1]).toReal - FOpt) ^ (2 : ℕ)) := by
  let xHalf := two_block_alternating_minimization_half_step x1 x2 n
  let gapCurrent : ℝ := (F x[n]).toReal - FOpt
  let gapHalf : ℝ := (F xHalf).toReal - FOpt
  let gapNext : ℝ := (F x[n + 1]).toReal - FOpt
  let c1 : ℝ := 1 / (2 * (L1 : ℝ) * ((R : ℝ) ^ (2 : ℕ)))
  let c2 : ℝ := 1 / (2 * (L2 : ℝ) * ((R : ℝ) ^ (2 : ℕ)))
  have h1 :
      gapCurrent - gapHalf ≥ c1 * gapHalf ^ (2 : ℕ) := by
    -- This is the first-block quadratic-gap estimate.
    simpa [gapCurrent, gapHalf, c1, xHalf] using
      two_block_x1_half_step_quadratic_gap htraj hxStar hFOpt hx0 hR n
  have h2 :
      gapHalf - gapNext ≥ c2 * gapNext ^ (2 : ℕ) := by
    -- This is the second-block quadratic-gap estimate.
    simpa [gapHalf, gapNext, c2, xHalf] using
      two_block_x2_next_step_quadratic_gap htraj hxStar hFOpt hx0 hR n
  have hmono :
      gapNext ≤ gapHalf := by
    -- The second block update cannot increase the objective gap relative to the half-step.
    simpa [gapHalf, gapNext, xHalf] using
      two_block_next_iterate_objective_gap_le_half_step_gap
        (FOpt := FOpt) htraj hx0 n
  have hgapNext_nonneg : 0 ≤ gapNext := by
    -- The next-iterate objective gap is nonnegative.
    simpa [gapNext] using
      two_block_objective_gap_nonneg_of_problem htraj hxStar hFOpt hx0 (n + 1)
  have hsquare :
      gapNext ^ (2 : ℕ) ≤ gapHalf ^ (2 : ℕ) := by
    -- Monotonicity of the nonnegative gaps upgrades to their squares.
    nlinarith [hmono, hgapNext_nonneg]
  have hc1_nonneg : 0 ≤ c1 := by
    have hL1_pos : 0 < (L1 : ℝ) := L1.2
    have hR_pos : 0 < (R : ℝ) := R.2
    dsimp [c1]
    positivity
  have hc2_nonneg : 0 ≤ c2 := by
    have hL2_pos : 0 < (L2 : ℝ) := L2.2
    have hR_pos : 0 < (R : ℝ) := R.2
    dsimp [c2]
    positivity
  have h1next :
      gapCurrent - gapHalf ≥ c1 * gapNext ^ (2 : ℕ) := by
    -- The first-block quadratic gap also controls the smaller next-iterate square.
    have hscale := mul_le_mul_of_nonneg_left hsquare hc1_nonneg
    linarith [h1, hscale]
  have hhalf_nonneg : 0 ≤ gapCurrent - gapHalf := by
    -- The first-block quadratic estimate already implies the half-step objective decreases.
    have hsq_nonneg : 0 ≤ gapHalf ^ (2 : ℕ) := sq_nonneg gapHalf
    nlinarith [h1, hc1_nonneg, hsq_nonneg]
  have hnext_nonneg : 0 ≤ gapHalf - gapNext := by
    -- The half-step objective dominates the next-iterate objective.
    linarith [hmono]
  by_cases hL : (L1 : ℝ) ≤ (L2 : ℝ)
  · have hmain :
        gapCurrent - gapNext ≥ c1 * gapNext ^ (2 : ℕ) := by
      -- When `L₁ ≤ L₂`, the desired coefficient is the first-block one.
      linarith [h1next, hnext_nonneg]
    simpa [gapCurrent, gapNext, c1, min_eq_left hL]
      using hmain
  · have hL' : (L2 : ℝ) ≤ (L1 : ℝ) := le_of_not_ge hL
    have hmain :
        gapCurrent - gapNext ≥ c2 * gapNext ^ (2 : ℕ) := by
      -- Otherwise the desired coefficient is the second-block one.
      linarith [h2, hhalf_nonneg]
    simpa [gapCurrent, gapNext, c2, min_eq_right hL']
      using hmain

/-- Helper for Theorem 14.8: the source proof reduces the theorem to a Chapter 14 quadratic
recurrence and then to the Chapter 11 scalar recurrence estimate. -/
lemma two_block_objective_gap_le_max_geometric_or_sublinear_core
    [hproblem : IsTwoBlockAlternatingMinimizationConvexRateProblem f g1 g2 XStar FOpt L1 L2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hxStar : IsMinOn F Set.univ xStar)
    (hFOpt : F xStar = (FOpt : EReal))
    (hx0 : x[0] ∈ effective_domain F)
    (hR :
      ∀ ⦃y : E1 × E2⦄,
        F y ≤ F x[0] →
        ‖y - xStar‖ ≤ (R : ℝ))
    (k : ℕ) (hk : 2 ≤ k) :
    (F x[k]).toReal - FOpt ≤
      max
        (((1 / 2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) *
          ((F x[0]).toReal - FOpt))
        ((8 * min (L1 : ℝ) (L2 : ℝ) * ((R : ℝ) ^ (2 : ℕ))) / ((k - 1 : ℕ) : ℝ)) := by
  let γ : PosReal := ⟨2 * min (L1 : ℝ) (L2 : ℝ) * ((R : ℝ) ^ (2 : ℕ)), by
    have hmin_pos : 0 < min (L1 : ℝ) (L2 : ℝ) := by
      exact lt_min (PosReal.coe_pos L1) (PosReal.coe_pos L2)
    have hR_pos : 0 < (R : ℝ) ^ (2 : ℕ) := by
      nlinarith [PosReal.coe_pos R]
    exact mul_pos (mul_pos (by norm_num) hmin_pos) hR_pos⟩
  have hγ :
      4 * (γ : ℝ) ≤ 8 * min (L1 : ℝ) (L2 : ℝ) * ((R : ℝ) ^ (2 : ℕ)) := by
    have hγ_eq :
        4 * (γ : ℝ) = 8 * min (L1 : ℝ) (L2 : ℝ) * ((R : ℝ) ^ (2 : ℕ)) := by
      dsimp [γ]
      ring
    exact hγ_eq.le
  have hgap_nonneg :
      ∀ n : ℕ, 0 ≤ (F x[n]).toReal - FOpt := by
    -- Each iterate is finite and lies above the optimal value.
    intro n
    exact two_block_objective_gap_nonneg_of_problem htraj hxStar hFOpt hx0 n
  have hstep :
      ∀ n : ℕ,
        ((F x[n]).toReal - FOpt) - ((F x[n + 1]).toReal - FOpt) ≥
          (1 / (γ : ℝ)) * (((F x[n + 1]).toReal - FOpt) ^ (2 : ℕ)) := by
    -- This is the remaining source-faithful Chapter 14 recurrence step.
    intro n
    simpa [γ] using
      two_block_objective_gap_quadratic_recurrence
        htraj hxStar hFOpt hx0 hR n
  exact
    two_block_objective_gap_le_of_quadratic_recurrence
      γ hγ hgap_nonneg hstep k hk

/-- Helper for Theorem 14.8: if the initial pair `x^0 = (x₁^0, x₂^0)` lies in `dom(F)`, then under
an explicit initial-sublevel radius witness `R`, every `k ≥ 2` objective gap is
bounded by the maximum of the geometric term
`(1 / 2)^((k - 1) / 2) (F(x^0) - F_opt)` and the sublinear term
`8 min {L₁, L₂} R^2 / (k - 1)`. -/
theorem
    two_block_alternating_minimization_objective_gap_le_max_geometric_or_sublinear_of_initial_radius
    [hproblem : IsTwoBlockAlternatingMinimizationConvexRateProblem f g1 g2 XStar FOpt L1 L2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F)
    (R : PosReal)
    (hR :
      ∀ ⦃y xStar : E1 × E2⦄,
        F y ≤ F x[0] →
        xStar ∈ XStar →
        ‖y - xStar‖ ≤ (R : ℝ))
    (k : ℕ) (hk : 2 ≤ k) :
    (F x[k]).toReal - FOpt ≤
      max
        (((1 / 2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) *
          ((F x[0]).toReal - FOpt))
        ((8 * min (L1 : ℝ) (L2 : ℝ) * ((R : ℝ) ^ (2 : ℕ))) / ((k - 1 : ℕ) : ℝ)) := by
  rcases hproblem.optimal_set_nonempty with ⟨xStar, hxStar_mem⟩
  have hxStar : IsMinOn F Set.univ xStar := by
    -- Rewrite optimal-set membership through the canonical unconstrained-solution owner.
    simpa [hproblem.optimal_set_eq, mem_unconstrained_problem_solutions_iff] using hxStar_mem
  have hFOpt_lower : (FOpt : EReal) ≤ F xStar :=
    hproblem.optimal_value_isGLB.1 ⟨xStar, rfl⟩
  have hFOpt_upper : F xStar ≤ (FOpt : EReal) := by
    -- The chosen optimizer is a lower bound for the whole objective range,
    -- so the glb lies above it.
    refine hproblem.optimal_value_isGLB.2 ?_
    rintro _ ⟨y, rfl⟩
    exact (isMinOn_iff.mp hxStar) y (by simp)
  have hFOpt : F xStar = (FOpt : EReal) := le_antisymm hFOpt_upper hFOpt_lower
  have hR' :
      ∀ ⦃y : E1 × E2⦄,
        F y ≤ F x[0] →
        ‖y - xStar‖ ≤ (R : ℝ) :=
    fun {_} hy ↦ hR hy hxStar_mem
  -- Reduce to the core theorem after fixing one optimal point and one compatible radius witness.
  exact
    two_block_objective_gap_le_max_geometric_or_sublinear_core
      htraj hxStar hFOpt hx0 hR' k hk

/-- Theorem 14.8: if Assumption 14.12 holds and `(x₁^k, x₂^k)` is generated by the exact
two-block alternating-minimization method from Algorithm 14.8, then there exists a radius
`R = R_{F(x^0)}` controlling the initial sublevel set `{y | F y ≤ F x[0]}` such that, for every
`k ≥ 2`, provided the initial pair `x^0 = (x₁^0, x₂^0)` lies in `dom(F)`, the objective gap is
bounded by the maximum of the geometric term
`(1 / 2)^((k - 1) / 2) (F(x^0) - F_opt)` and the sublinear term
`8 min {L₁, L₂} R^2 / (k - 1)`. -/
theorem two_block_objective_gap_le_max_geometric_or_sublinear
    [hproblem : IsTwoBlockAlternatingMinimizationConvexRateProblem f g1 g2 XStar FOpt L1 L2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F) :
    ∃ R : PosReal,
      (∀ ⦃y xStar : E1 × E2⦄,
        F y ≤ F x[0] →
        xStar ∈ XStar →
        ‖y - xStar‖ ≤ (R : ℝ)) ∧
      ∀ k : ℕ,
        2 ≤ k →
          (F x[k]).toReal - FOpt ≤
            max
              (((1 / 2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) *
                ((F x[0]).toReal - FOpt))
              ((8 * min (L1 : ℝ) (L2 : ℝ) * ((R : ℝ) ^ (2 : ℕ))) /
                ((k - 1 : ℕ) : ℝ)) := by
  let α : PosReal := ⟨max (F x[0]).toReal 1, by
    change 0 < max (F x[0]).toReal 1
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)⟩
  have hx0_top : F x[0] ≠ ⊤ := (mem_effective_domain.mp hx0).ne
  have hx0_le_α : F x[0] ≤ ((α : ℝ) : EReal) := by
    calc
      F x[0] ≤ (((F x[0]).toReal : ℝ) : EReal) := EReal.le_coe_toReal hx0_top
      _ ≤ ((α : ℝ) : EReal) := by
            exact_mod_cast (le_max_left (F x[0]).toReal (1 : ℝ))
  rcases
      TwoBlockConvexRate.bounded_initial_sublevel_distance_to_each_optimal_point
        hproblem hx0_le_α with
    ⟨R, hR⟩
  have hR' :
      ∀ ⦃y xStar : E1 × E2⦄,
        F y ≤ F x[0] →
        xStar ∈ XStar →
        ‖y - xStar‖ ≤ (R : ℝ) :=
    fun {_ _} hy hxStar ↦ hR hy hxStar
  refine ⟨R, hR', ?_⟩
  intro k hk
  -- Once the source-facing initial-sublevel radius is extracted, the explicit-radius theorem
  -- applies verbatim.
  exact
    two_block_alternating_minimization_objective_gap_le_max_geometric_or_sublinear_of_initial_radius
      htraj hx0 R hR' k hk

end PropernessInstances

end

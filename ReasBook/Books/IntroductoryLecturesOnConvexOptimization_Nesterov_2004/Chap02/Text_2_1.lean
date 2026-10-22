/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_22

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient ProjectedGradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: stagewise lower bounds for the simple-set estimating-sequence owner objects from
Proposition 2.22.

Owner declarations sampled for this refinement:
* `simpleSetEstimatingValue_succ` and `simpleSetEstimatingCenter_succ` in `Proposition_2_22`,
  which own the recursive stage update and center sequence;
* `gradientMapping` and `reducedGradient` in `Definition_2_35_1`, which own the projected point
  `x_Q(y_k; L)` and reduced gradient `g_Q(y_k; L)`;
* `gradientMapping_objective_lower_bound` in `Theorem_2_36`, which owns the lower bound
  `(2.2.57)` inserted in the second displayed inequality.

Best owner abstraction:
* source-facing owner stage of `simpleSetEstimatingValue` and `simpleSetEstimatingCenter`, with
  projected-gradient data used only as derived stage views; the stronger μ-retaining inequalities
  below are bridge companions, not the main public statements.

Source/core/bridge triage:
* source-facing: the two μ-free displayed bounds from Text 2.1, stated directly for
  `simpleSetEstimatingValue ... (k + 1)`;
* core/canonical: `simpleSetEstimatingValue`, `simpleSetEstimatingCenter`, `gradientMapping`, and
  `reducedGradient`;
* bridge/view: the stronger companions retaining the nonnegative strong-convexity terms dropped in
  the source display.

Primitive data:
* the feasible set `Q`, the objective `f`, the initial point `x0`, the stage index `k`, the
  simple-set recursion inputs `(μ, L, gamma0, y, α)`, and the comparison point `x_k`.

Derived API:
* the stage data `γ_k`, `γ_{k+1}`, `φ_k^*`, `φ_{k+1}^*`, and `v_k` from Proposition 2.22;
* the projected-gradient point `x_Q(y_k; L)` and reduced gradient `g_Q(y_k; L)`;
* the μ-free and μ-retaining right-hand sides factored below as internal notation only.

This file therefore keeps Text 2.1 at the source-facing owner stage and removes the parallel
free-floating scalar API from the earlier version. -/

section

variable
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (f : E → ℝ) (x0 : E)
    (μ : ℝ) (L : NNRealˣ) (gamma0 : ℝ)
    (y : ℕ → E) (α : ℕ → ℝ)
    {k : ℕ} {xk : E}

local notation "gammaK" => estimatingSequenceCurvature μ gamma0 α k
local notation "gammaKp1" => estimatingSequenceCurvature μ gamma0 α (k + 1)

local notation "phi" =>
  simpleSetEstimatingValue Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α

local notation "v" =>
  simpleSetEstimatingCenter Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k

local notation "yK" => y k

local notation "xQ" =>
  x_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; L](yK)

local notation "gQ" =>
  g_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; L](yK)

local notation "gQNormSq" => ‖gQ‖ ^ (2 : ℕ)

local notation "curvatureCoeff" =>
  α k / (2 * L) - α k ^ (2 : ℕ) / (2 * gammaKp1)

local notation "transportCoeff" =>
  α k * (1 - α k) * gammaK / gammaKp1

local notation "transportStrongConvexityTerm" =>
  transportCoeff * (μ / 2) * ‖yK - v‖ ^ (2 : ℕ)

local notation "objectiveStrongConvexityTerm" =>
  (μ / 2) * ‖xk - yK‖ ^ (2 : ℕ)

local notation "intermediateRhs" =>
  (1 - α k) * f xk +
    α k * f xQ +
    curvatureCoeff * gQNormSq +
    transportCoeff * inner ℝ gQ (v - yK)

local notation "intermediateStrongRhs" =>
  intermediateRhs + transportStrongConvexityTerm

local notation "objectiveLowerRhs" =>
  f xQ +
    inner ℝ gQ (xk - yK) +
    (1 / (2 * L)) * gQNormSq

local notation "objectiveLowerStrongRhs" =>
  objectiveLowerRhs + objectiveStrongConvexityTerm

local notation "combinedShift" =>
  ((α k * gammaK) / gammaKp1) • (v - yK) + (xk - yK)

local notation "finalRhs" =>
  f xQ +
    (1 / (2 * L) - α k ^ (2 : ℕ) / (2 * gammaKp1)) * gQNormSq +
    (1 - α k) * inner ℝ gQ combinedShift

local notation "finalStrongRhs" =>
  finalRhs +
    (1 - α k) * objectiveStrongConvexityTerm +
    transportStrongConvexityTerm

/-- The first displayed lower bound in Text 2.1, stated directly for the owner stage
`simpleSetEstimatingValue ... (k + 1)`: after replacing `φ_k^*` by `f(x_k)` in the Proposition
2.22 recursion and discarding the nonnegative transport strong-convexity term, one gets the
μ-free lower bound `intermediateRhs`. -/
-- Proof sketch: rewrite `phi (k + 1)` with `simpleSetEstimatingValue_succ`, use `α k ≤ 1` to
-- replace `(1 - α k) * phi k` by `(1 - α k) * f xk`, and use the sign assumptions to drop
-- `transportStrongConvexityTerm`.
theorem simple_set_phi_star_lower_bound_intermediate
    (halpha_k : α k ≤ 1)
    (htransportCoeff : 0 ≤ transportCoeff)
    (hμ : 0 ≤ μ)
    (hphi_k : f xk ≤ phi k) :
    phi (k + 1) ≥ intermediateRhs := by
  -- Scale the lower bound `f xk ≤ φ_k^*` by the nonnegative factor `1 - α k`.
  have hcoeff_nonneg : 0 ≤ 1 - α k := by
    exact sub_nonneg.mpr halpha_k
  have hscaled : (1 - α k) * f xk ≤ (1 - α k) * phi k := by
    exact mul_le_mul_of_nonneg_left hphi_k hcoeff_nonneg
  -- Rewrite the successor value and isolate the transport strong-convexity term.
  have hsucc :
      phi (k + 1) =
        (1 - α k) * phi k +
          α k * f xQ +
          curvatureCoeff * gQNormSq +
          transportStrongConvexityTerm +
          transportCoeff * inner ℝ gQ (v - yK) := by
    calc
      phi (k + 1) =
          (1 - α k) * phi k +
            α k * f xQ +
            curvatureCoeff * gQNormSq +
            transportCoeff *
              ((μ / 2) * ‖yK - v‖ ^ (2 : ℕ) + inner ℝ gQ (v - yK)) := by
              simpa using
                simpleSetEstimatingValue_succ
                  Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k
      _ =
          (1 - α k) * phi k +
            α k * f xQ +
            curvatureCoeff * gQNormSq +
            transportStrongConvexityTerm +
            transportCoeff * inner ℝ gQ (v - yK) := by
              ring
  -- Then show the dropped transport strong-convexity contribution is nonnegative.
  have hμ_half : 0 ≤ μ / 2 := by
    nlinarith
  have hsq : 0 ≤ ‖yK - v‖ ^ (2 : ℕ) := by
    positivity
  have htransport_strong_nonneg : 0 ≤ transportStrongConvexityTerm := by
    exact mul_nonneg (mul_nonneg htransportCoeff hμ_half) hsq
  nlinarith

/-- The stronger bridge form of `simple_set_phi_star_lower_bound_intermediate` that keeps the
transport strong-convexity term coming from the owner Proposition 2.22 recursion. -/
-- Proof sketch: rewrite `phi (k + 1)` with `simpleSetEstimatingValue_succ` and use `α k ≤ 1` to
-- replace `(1 - α k) * phi k` by `(1 - α k) * f xk`, keeping the remaining terms unchanged.
theorem simple_set_phi_star_lower_bound_intermediate_with_strong_convexity
    (halpha_k : α k ≤ 1)
    (hphi_k : f xk ≤ phi k) :
    phi (k + 1) ≥ intermediateStrongRhs := by
  -- Scale the lower bound `f xk ≤ φ_k^*` by the nonnegative factor `1 - α k`.
  have hcoeff_nonneg : 0 ≤ 1 - α k := by
    exact sub_nonneg.mpr halpha_k
  have hscaled : (1 - α k) * f xk ≤ (1 - α k) * phi k := by
    exact mul_le_mul_of_nonneg_left hphi_k hcoeff_nonneg
  -- Rewrite the successor value so the only comparison point is the first term.
  have hsucc :
      phi (k + 1) =
        (1 - α k) * phi k +
          α k * f xQ +
          curvatureCoeff * gQNormSq +
          transportStrongConvexityTerm +
          transportCoeff * inner ℝ gQ (v - yK) := by
    calc
      phi (k + 1) =
          (1 - α k) * phi k +
            α k * f xQ +
            curvatureCoeff * gQNormSq +
            transportCoeff *
              ((μ / 2) * ‖yK - v‖ ^ (2 : ℕ) + inner ℝ gQ (v - yK)) := by
              simpa using
                simpleSetEstimatingValue_succ
                  Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α k
      _ =
          (1 - α k) * phi k +
            α k * f xQ +
            curvatureCoeff * gQNormSq +
            transportStrongConvexityTerm +
            transportCoeff * inner ℝ gQ (v - yK) := by
              ring
  -- Insert the scaled comparison into the recursion and keep the common terms unchanged.
  nlinarith

/-- Text 2.1: if `α_k ≤ 1`, the transport coefficient is nonnegative, `μ ≥ 0`,
`φ_k^* ≥ f(x_k)`, and the μ-free lower bound `(2.2.57)` holds at stage `k`, then the owner
Proposition 2.22 update yields the displayed μ-free lower bound `finalRhs` for
`simpleSetEstimatingValue ... (k + 1)`. -/
-- Proof sketch: apply `simple_set_phi_star_lower_bound_intermediate`, substitute the μ-free
-- lower bound `objectiveLowerRhs` for `f xk`, and collect the norm and inner-product terms.
theorem simple_set_phi_star_lower_bound_of_objective_lower_bound
    (halpha_k : α k ≤ 1)
    (htransportCoeff : 0 ≤ transportCoeff)
    (hμ : 0 ≤ μ)
    (hphi_k : f xk ≤ phi k)
    (hobjective_lower : f xk ≥ objectiveLowerRhs) :
    phi (k + 1) ≥ finalRhs := by
  -- Start from the source-faithful intermediate lower bound from Proposition 2.22.
  have hintermediate :=
    simple_set_phi_star_lower_bound_intermediate
      Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α
      halpha_k htransportCoeff hμ hphi_k
  have hcoeff_nonneg : 0 ≤ 1 - α k := by
    exact sub_nonneg.mpr halpha_k
  -- Scale the objective lower bound `(2.2.57)` by `1 - α k`.
  have hscaled : (1 - α k) * objectiveLowerRhs ≤ (1 - α k) * f xk := by
    exact mul_le_mul_of_nonneg_left hobjective_lower hcoeff_nonneg
  -- Regroup the final displayed expression so the scaled objective bound can be inserted directly.
  have hfinal_repr :
      finalRhs =
        (1 - α k) * objectiveLowerRhs +
          α k * f xQ +
          curvatureCoeff * gQNormSq +
          transportCoeff * inner ℝ gQ (v - yK) := by
    rw [show inner ℝ gQ combinedShift =
        inner ℝ gQ (((α k * gammaK) / gammaKp1) • (v - yK)) +
          inner ℝ gQ (xk - yK) by
          rw [inner_add_right]]
    rw [inner_smul_right]
    ring
  nlinarith

/-- The stronger bridge form of Text 2.1 obtained by retaining the objective and transport
strong-convexity contributions instead of discarding them from the displayed μ-free formula. -/
-- Proof sketch: apply `simple_set_phi_star_lower_bound_intermediate_with_strong_convexity`,
-- substitute the stronger lower bound `objectiveLowerStrongRhs` for `f xk`, and collect the norm,
-- inner-product, and strong-convexity terms.
theorem simple_set_phi_star_lower_bound_of_objective_lower_bound_with_strong_convexity
    (halpha_k : α k ≤ 1)
    (hphi_k : f xk ≤ phi k)
    (hobjective_lower : f xk ≥ objectiveLowerStrongRhs) :
    phi (k + 1) ≥ finalStrongRhs := by
  -- Start from the version that retains both strong-convexity contributions.
  have hintermediate :=
    simple_set_phi_star_lower_bound_intermediate_with_strong_convexity
      Q hQ_nonempty hQ_closed hQ_convex f x0 μ L gamma0 y α
      halpha_k hphi_k
  have hcoeff_nonneg : 0 ≤ 1 - α k := by
    exact sub_nonneg.mpr halpha_k
  -- Scale the stronger objective lower bound before inserting it into the intermediate estimate.
  have hscaled : (1 - α k) * objectiveLowerStrongRhs ≤ (1 - α k) * f xk := by
    exact mul_le_mul_of_nonneg_left hobjective_lower hcoeff_nonneg
  -- Rewrite the final strong right-hand side in the same grouped form as the intermediate bound.
  have hfinal_repr :
      finalStrongRhs =
        (1 - α k) * objectiveLowerStrongRhs +
          α k * f xQ +
          curvatureCoeff * gQNormSq +
          transportCoeff * inner ℝ gQ (v - yK) +
          transportStrongConvexityTerm := by
    rw [show inner ℝ gQ combinedShift =
        inner ℝ gQ (((α k * gammaK) / gammaKp1) • (v - yK)) +
          inner ℝ gQ (xk - yK) by
          rw [inner_add_right]]
    rw [inner_smul_right]
    ring
  nlinarith

end

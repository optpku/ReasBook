/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_18
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_23

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped BigOperators PositiveDefMatrixNorm

variable {m : ℕ+} {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "PosMat" => { G : Matrix (Fin n) (Fin n) ℝ // Matrix.PosDef G }
local notation "ConstraintVec" => { d : E // d ≠ 0 }

/- Algorithm 7.9 lies in the recursive outer-iterate / first-stopping-index /
positive-definite-normalization domain.

Sampled owner-style declarations:
- `maxTypeObjective` in `Lemma_2_18.lean`, the project owner for finite maxima of nonempty
  families;
- `absLinearLogSumExp` in `Proposition_7_14.lean`, the Chapter 7 owner for the symmetric
  log-sum-exp smoothing with a positive parameter;
- `relativeScaleSubgradientApproximationIterate` and
  `relativeScaleSubgradientApproximationStoppingIndex` in `Algorithm_7_2.lean`, where the
  autonomous orbit and first accepted stage are derived from the explicit step map;
- `schemeSNRestartingIterate` and `schemeSNRestartingStoppingIndex` in `Algorithm_7_4.lean`, the
  nearby Chapter 7 owner pattern for autonomous restart trajectories and first-hit stopping
  indices;
- `positiveDefMatrixNorm_def` in `Definition_7_23.lean`, the chapter owner relating a
  positive-definite matrix to the quadratic normalization scalar used below.

Best owner abstraction:
- source-facing: the recursive outer iterates `\hat x_t` and the first accepted stage/time of
  Algorithm 7.9;
- core/canonical: `maxTypeObjective (fun i x ↦ |⟪aᵢ, x⟫|)`, the positive-parameter smoothing owner
  `absLinearLogSumExp μ a`, the explicit step map `iterativeSmoothingStep`, and the least
  stopping index obtained by `Nat.find`;
- bridge/view: the stopping time `T = s + 1` and the accepted output point.

Primitive data:
- the explicit smoothing, localization, and step-map formulas;
- the nonzero constraint vector `d : ConstraintVec`, needed for the textbook normalization
  `G⁻¹ d / ⟪d, G⁻¹ d⟫`;
- an actual outer trajectory `xHat : ℕ → E` together with explicit auxiliary hypotheses for the
  initial point, the stagewise positivity of `μ_t`, and the recursive update equation;
- existence of an outer stage satisfying the stopping criterion.

Derived API:
- the recursive iterate equations for `\hat x_t`;
- the stopping predicate and termination statement;
- the canonical first stopping index `s`;
- the stopping time `T = s + 1`;
- the accepted output point `\hat x_T`.

Algorithms 7.2 and 7.4 admit autonomous `Function.iterate` owners because their step maps are
defined on all states. Algorithm 7.9 does not: its smoothing owner is only available when the
stagewise parameter `μ_t` is positive, and `iterativeSmoothingParameter a δ 0 = 0`. The previous
whole-space autonomous-map API was therefore vacuous. This refinement keeps the source-facing
outer iterate itself as the public owner, while the stagewise positivity data and recursive update
equations remain explicit auxiliary hypotheses on that iterate rather than instance-level wrapper
data. The first accepted stage is still derived canonically by `Nat.find`. It also no longer
threads a separate proof binder `hd : d ≠ 0` through the algorithmic API: the nondegeneracy is
part of the owner data via `ConstraintVec`, so the initial point is stated only on the intended
nondegenerate domain. The old public duplicates `iterativeSmoothingObjective` and
`iterativeSmoothingSmoothedObjective` remain deleted in favor of the chapter owners
`maxTypeObjective` and `absLinearLogSumExp`.
-/

/-- The localized feasible set
`Q(r) = {x ∈ ℝⁿ : ⟪d, x⟫ = 1, ‖x‖_G ≤ r}`
used in Algorithm 7.9. -/
def iterativeSmoothingFeasibleSet
    (d : ConstraintVec) (G : PosMat) (r : ℝ) : Set E :=
  {x | inner ℝ (d : E) x = 1 ∧ ‖x‖[G] ≤ r}

/-- Membership in `iterativeSmoothingFeasibleSet d G r` is exactly the conjunction
`⟪d, x⟫ = 1` and `‖x‖_G ≤ r`. -/
theorem mem_iterativeSmoothingFeasibleSet_iff
    {d : ConstraintVec} {x : E} {G : PosMat} {r : ℝ} :
    x ∈ iterativeSmoothingFeasibleSet d G r ↔
      inner ℝ (d : E) x = 1 ∧ ‖x‖[G] ≤ r :=
  Iff.rfl

/-- The normalization scalar `⟪d, G⁻¹ d⟫` appearing in the textbook initial point of
Algorithm 7.9. -/
def iterativeSmoothingInitialDenominator
    (d : ConstraintVec) (G : PosMat) : ℝ :=
  inner ℝ (d : E) (Matrix.toEuclideanLin G.1⁻¹ d)

/-- Expanding `iterativeSmoothingInitialDenominator d G` recovers the scalar `⟪d, G⁻¹ d⟫`. -/
theorem iterativeSmoothingInitialDenominator_eq
    (d : ConstraintVec) (G : PosMat) :
    iterativeSmoothingInitialDenominator d G =
      inner ℝ (d : E) (Matrix.toEuclideanLin G.1⁻¹ d) :=
  rfl

/-- For a constraint vector `d : ConstraintVec`, the textbook normalization scalar
`⟪d, G⁻¹ d⟫` is strictly positive. -/
theorem iterativeSmoothingInitialDenominator_pos
    (d : ConstraintVec) (G : PosMat) :
    0 < iterativeSmoothingInitialDenominator d G := by
  let GInv : PosMat := ⟨G.1⁻¹, G.2.inv⟩
  have hnorm : 0 < ‖d‖[GInv] :=
    Seminorm.map_pos_of_ne_zero _ d.2
  rw [positiveDefMatrixNorm_def] at hnorm
  have hsqrt : 0 < Real.sqrt (iterativeSmoothingInitialDenominator d G) := by
    simpa [iterativeSmoothingInitialDenominator, GInv, real_inner_comm] using hnorm
  exact (Real.sqrt_pos).1 hsqrt

/-- For a constraint vector `d : ConstraintVec`, the textbook normalization scalar `⟪d, G⁻¹ d⟫`
is nonzero. -/
theorem iterativeSmoothingInitialDenominator_ne_zero
    (d : ConstraintVec) (G : PosMat) :
    iterativeSmoothingInitialDenominator d G ≠ 0 :=
  ne_of_gt (iterativeSmoothingInitialDenominator_pos d G)

/-- The initial point
`x₀ = G⁻¹ d / ⟪d, G⁻¹ d⟫`
from Algorithm 7.9, defined on the intended nondegenerate domain of nonzero constraint vectors. -/
def iterativeSmoothingInitialPoint
    (d : ConstraintVec) (G : PosMat) : E :=
  (iterativeSmoothingInitialDenominator d G)⁻¹ • Matrix.toEuclideanLin G.1⁻¹ d

/-- Expanding `iterativeSmoothingInitialPoint d G` gives the normalized vector
`G⁻¹ d / ⟪d, G⁻¹ d⟫`. -/
theorem iterativeSmoothingInitialPoint_eq
    (d : ConstraintVec) (G : PosMat) :
    iterativeSmoothingInitialPoint d G =
      (iterativeSmoothingInitialDenominator d G)⁻¹ • Matrix.toEuclideanLin G.1⁻¹ d :=
  rfl

/-- The block length
`\tilde N = ⌊2 e γ √(2 n \ln(2m)) (1 + 1 / δ)⌋`
used in Algorithm 7.9. -/
def iterativeSmoothingBlockLength
    (m n : ℕ) (δ γ : ℝ) : ℕ :=
  Nat.floor (2 * Real.exp 1 * γ * Real.sqrt (2 * n * Real.log (2 * m)) * (1 + 1 / δ))

/-- Expanding `iterativeSmoothingBlockLength m n δ γ` recovers the textbook expression for
`\tilde N`. -/
theorem iterativeSmoothingBlockLength_def
    (m n : ℕ) (δ γ : ℝ) :
    iterativeSmoothingBlockLength m n δ γ =
      Nat.floor (2 * Real.exp 1 * γ * Real.sqrt (2 * n * Real.log (2 * m)) * (1 + 1 / δ)) :=
  rfl

/-- The smoothing parameter
`μ_t = δ f(\hat x_{t-1}) / (2 e (1 + δ) \ln(2m))`
chosen at each outer iteration of Algorithm 7.9. -/
def iterativeSmoothingParameter
    (a : Fin (m : ℕ) → E) (δ : ℝ) (x : E) : ℝ :=
  (δ * maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) /
    (2 * Real.exp 1 * (1 + δ) * Real.log (2 * m))

/-- Evaluating `iterativeSmoothingParameter a δ x` gives the textbook formula for `μ_t` with
`x = \hat x_{t-1}`. -/
theorem iterativeSmoothingParameter_eq
    (a : Fin (m : ℕ) → E) (δ : ℝ) (x : E) :
    iterativeSmoothingParameter a δ x =
      (δ * maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) /
        (2 * Real.exp 1 * (1 + δ) * Real.log (2 * m)) :=
  rfl

/-- The textbook smoothing parameter vanishes at the origin because the underlying max objective
vanishes there. -/
@[simp] theorem iterativeSmoothingParameter_zero
    (a : Fin (m : ℕ) → E) (δ : ℝ) :
    iterativeSmoothingParameter a δ 0 = 0 := by
  simp [iterativeSmoothingParameter, maxTypeObjective_apply]

/-- Under the natural positive-parameter regime `δ > 0` and `f(x) > 0`, the textbook smoothing
parameter `μ_t` is positive. This is the bridge from the scalar parameter formula to the canonical
positive-parameter smoothing owner `absLinearLogSumExp`. -/
theorem iterativeSmoothingParameter_pos
    (a : Fin (m : ℕ) → E) (δ : ℝ) (x : E)
    (hδ : 0 < δ)
    (hx : 0 < maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) :
    0 < iterativeSmoothingParameter a δ x := by
  -- Rewrite the parameter to the explicit quotient from the textbook formula.
  rw [iterativeSmoothingParameter_eq]
  -- The logarithmic factor is positive because the positive natural `m` satisfies `1 ≤ m`.
  have hm_one_le : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt m.pos)
  have hlog_pos : 0 < Real.log (2 * (m : ℝ)) := by
    refine Real.log_pos ?_
    nlinarith
  -- The remaining denominator factors are also positive under `δ > 0`.
  have hone_add_δ_pos : 0 < 1 + δ := by
    linarith
  have htwo_pos : (0 : ℝ) < 2 := by
    norm_num
  have hdenom_pos : 0 < 2 * Real.exp 1 * (1 + δ) * Real.log (2 * (m : ℝ)) := by
    refine mul_pos ?_ hlog_pos
    refine mul_pos ?_ hone_add_δ_pos
    exact mul_pos htwo_pos (Real.exp_pos 1)
  -- Positive numerator over positive denominator gives the desired positivity.
  exact div_pos (mul_pos hδ hx) hdenom_pos

/-- The smoothness constant
`L_μ = γ² n / μ`
attached to the smoothed objective in Algorithm 7.9. -/
def iterativeSmoothingSmoothness
    (n : ℕ) (γ μ : ℝ) : ℝ :=
  (γ ^ (2 : ℕ) * n) / μ

/-- Expanding `iterativeSmoothingSmoothness n γ μ` recovers the displayed formula
`L_μ = γ² n / μ`. -/
theorem iterativeSmoothingSmoothness_eq
    (n : ℕ) (γ μ : ℝ) :
    iterativeSmoothingSmoothness n γ μ =
      (γ ^ (2 : ℕ) * n) / μ :=
  rfl

/-- The stopping factor `1 / e` from the acceptance test in Algorithm 7.9. -/
def iterativeSmoothingStoppingFactor : ℝ :=
  1 / Real.exp 1

/-- Expanding `iterativeSmoothingStoppingFactor` recovers the threshold `1 / e`. -/
theorem iterativeSmoothingStoppingFactor_def :
    iterativeSmoothingStoppingFactor = 1 / Real.exp 1 :=
  rfl

/-- The textbook smoothed objective
`f_μ(x) = μ log (∑ᵢ [exp (⟪aᵢ, x⟫ / μ) + exp (-⟪aᵢ, x⟫ / μ)])`
used in the step subroutine of Algorithm 7.9. -/
def iterativeSmoothingSmoothedObjective
    (a : Fin (m : ℕ) → E) (μ : {μ : ℝ // 0 < μ}) : E → ℝ :=
  fun x ↦
    (μ : ℝ) * Real.log
      (Finset.univ.sum fun i : Fin (m : ℕ) ↦
        Real.exp (inner ℝ (a i) x / (μ : ℝ)) +
          Real.exp (-(inner ℝ (a i) x / (μ : ℝ))))

/-- Evaluating `iterativeSmoothingSmoothedObjective a μ` recovers the textbook smoothing
formula for Algorithm 7.9. -/
theorem iterativeSmoothingSmoothedObjective_apply
    (a : Fin (m : ℕ) → E) (μ : {μ : ℝ // 0 < μ}) (x : E) :
    iterativeSmoothingSmoothedObjective a μ x =
      (μ : ℝ) * Real.log
        (Finset.univ.sum fun i : Fin (m : ℕ) ↦
          Real.exp (inner ℝ (a i) x / (μ : ℝ)) +
            Real.exp (-(inner ℝ (a i) x / (μ : ℝ)))) :=
  rfl

/-- The single outer update
`\hat x_t = S(f_{μ_t}, L_{μ_t}, Q(f(\hat x_{t-1})), G, x₀, \tilde N)`
from Algorithm 7.9, defined on stages where the textbook smoothing parameter `μ_t` is positive.
The smoothing owner is the textbook function `iterativeSmoothingSmoothedObjective a ⟨μ_t, hμ⟩`. -/
def iterativeSmoothingStep
    (S : (E → ℝ) → ℝ → Set E → PosMat → E → ℕ → E)
    (a : Fin (m : ℕ) → E) (d : ConstraintVec) (G : PosMat)
    (δ γ : ℝ) (xPrev : E)
    (hμ : 0 < iterativeSmoothingParameter a δ xPrev) : E :=
  let μ : {μ : ℝ // 0 < μ} := ⟨iterativeSmoothingParameter a δ xPrev, hμ⟩
  S (iterativeSmoothingSmoothedObjective a μ)
    (iterativeSmoothingSmoothness n γ (μ : ℝ))
    (iterativeSmoothingFeasibleSet d G
      (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) xPrev))
    G
    (iterativeSmoothingInitialPoint d G)
    (iterativeSmoothingBlockLength m n δ γ)

/-- Evaluating `iterativeSmoothingStep S a d G δ γ xPrev hμ` applies the subroutine `S` to the
textbook smoothing owner `iterativeSmoothingSmoothedObjective a μ` attached to the positive
parameter `μ = iterativeSmoothingParameter a δ xPrev`, the constant `L_μ`, the set `Q(f(xPrev))`,
the matrix `G`, the initial point `x₀`, and the block length `\tilde N`. -/
theorem iterativeSmoothingStep_eq
    (S : (E → ℝ) → ℝ → Set E → PosMat → E → ℕ → E)
    (a : Fin (m : ℕ) → E) (d : ConstraintVec) (G : PosMat)
    (δ γ : ℝ) (xPrev : E) (hμ : 0 < iterativeSmoothingParameter a δ xPrev) :
    iterativeSmoothingStep S a d G δ γ xPrev hμ =
      let μ : {μ : ℝ // 0 < μ} := ⟨iterativeSmoothingParameter a δ xPrev, hμ⟩
      S (iterativeSmoothingSmoothedObjective a μ)
        (iterativeSmoothingSmoothness n γ (μ : ℝ))
        (iterativeSmoothingFeasibleSet d G
          (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) xPrev))
        G
        (iterativeSmoothingInitialPoint d G)
        (iterativeSmoothingBlockLength m n δ γ) :=
  rfl

section Trajectory

/-- An Algorithm 7.9 outer iterate starts at the textbook initial point `x₀`. The iterate
itself is the source-facing object; the initialization proof is kept as an explicit auxiliary
hypothesis rather than instance data. -/
@[simp] theorem iterativeSmoothingIterate_zero
    {n : ℕ}
    {d : { d : EuclideanSpace ℝ (Fin n) // d ≠ 0 }}
    {G : { G : Matrix (Fin n) (Fin n) ℝ // Matrix.PosDef G }}
    {xHat : ℕ → EuclideanSpace ℝ (Fin n)}
    (hZero : xHat 0 = iterativeSmoothingInitialPoint d G) :
    xHat 0 = iterativeSmoothingInitialPoint d G :=
  hZero

/-- Along an Algorithm 7.9 outer iterate, the stagewise positivity of the smoothing parameter is
kept as explicit auxiliary data attached to the iterate `\hat x_t`. -/
theorem iterativeSmoothingIterate_parameter_pos
    {m : ℕ+} {n : ℕ}
    (a : Fin (m : ℕ) → EuclideanSpace ℝ (Fin n)) {δ : ℝ}
    {xHat : ℕ → EuclideanSpace ℝ (Fin n)}
    (hParameterPos : ∀ t : ℕ, 0 < iterativeSmoothingParameter a δ (xHat t))
    (t : ℕ) :
    0 < iterativeSmoothingParameter a δ (xHat t) :=
  hParameterPos t

/-- The recursive update equation for Algorithm 7.9 is stated directly on the explicit outer
iterate `\hat x_t`, with the stagewise positivity proof supplied explicitly. -/
theorem iterativeSmoothingIterate_succ
    {m : ℕ+} {n : ℕ}
    (S :
      (EuclideanSpace ℝ (Fin n) → ℝ) → ℝ → Set (EuclideanSpace ℝ (Fin n)) →
        { G : Matrix (Fin n) (Fin n) ℝ // Matrix.PosDef G } →
          EuclideanSpace ℝ (Fin n) → ℕ → EuclideanSpace ℝ (Fin n))
    (a : Fin (m : ℕ) → EuclideanSpace ℝ (Fin n))
    {d : { d : EuclideanSpace ℝ (Fin n) // d ≠ 0 }}
    {G : { G : Matrix (Fin n) (Fin n) ℝ // Matrix.PosDef G }}
    {δ γ : ℝ} {xHat : ℕ → EuclideanSpace ℝ (Fin n)}
    (hParameterPos : ∀ t : ℕ, 0 < iterativeSmoothingParameter a δ (xHat t))
    (hSucc :
      ∀ t : ℕ,
        xHat (t + 1) =
          iterativeSmoothingStep S a d G δ γ (xHat t) (hParameterPos t))
    (t : ℕ) :
    xHat (t + 1) =
      iterativeSmoothingStep S a d G δ γ (xHat t) (hParameterPos t) :=
  hSucc t

end Trajectory

/-- The stopping predicate from Algorithm 7.9, evaluated at outer stage `t`. -/
def iterativeSmoothingStoppingCriterion
    (a : Fin (m : ℕ) → E) (xHat : ℕ → E)
    (t : ℕ) : Prop :=
  maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) (xHat (t + 1)) ≥
    iterativeSmoothingStoppingFactor *
      maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) (xHat t)

/-- Algorithm 7.9: termination means that some outer stage satisfies the acceptance test
`f(\hat x_{t+1}) ≥ (1 / e) f(\hat x_t)`. -/
def iterativeSmoothingTerminates
    (a : Fin (m : ℕ) → E) (xHat : ℕ → E) : Prop :=
  ∃ t : ℕ, iterativeSmoothingStoppingCriterion a xHat t

/-- The textbook first stopping index `s`, derived canonically from the least outer stage
satisfying the Algorithm 7.9 stopping predicate. -/
noncomputable def iterativeSmoothingStoppingIndex
    {a : Fin (m : ℕ) → E} {xHat : ℕ → E}
    (hTerminate : iterativeSmoothingTerminates a xHat) : ℕ := by
  classical
  exact Nat.find hTerminate

/-- The first stopping index is least with respect to the Algorithm 7.9 stopping predicate. -/
theorem iterativeSmoothingStoppingIndex_isLeast
    {a : Fin (m : ℕ) → E} {xHat : ℕ → E}
    (hTerminate : iterativeSmoothingTerminates a xHat) :
    IsLeast {t : ℕ | iterativeSmoothingStoppingCriterion a xHat t}
      (iterativeSmoothingStoppingIndex hTerminate) := by
  classical
  simpa [iterativeSmoothingStoppingIndex] using Nat.isLeast_find hTerminate

/-- The stopping test succeeds at the first accepted outer step. -/
theorem iterativeSmoothingStoppingIndex_spec
    {a : Fin (m : ℕ) → E} {xHat : ℕ → E}
    (hTerminate : iterativeSmoothingTerminates a xHat) :
    maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|)
      (xHat (iterativeSmoothingStoppingIndex hTerminate + 1)) ≥
      iterativeSmoothingStoppingFactor *
        maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|)
          (xHat (iterativeSmoothingStoppingIndex hTerminate)) := by
  simpa [iterativeSmoothingStoppingCriterion] using
    (iterativeSmoothingStoppingIndex_isLeast hTerminate).1

/-- The stopping test fails at every earlier outer step. -/
theorem iterativeSmoothingStoppingIndex_min
    {a : Fin (m : ℕ) → E} {xHat : ℕ → E}
    (hTerminate : iterativeSmoothingTerminates a xHat)
    {t : ℕ} (ht : t < iterativeSmoothingStoppingIndex hTerminate) :
    maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) (xHat (t + 1)) <
      iterativeSmoothingStoppingFactor *
        maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) (xHat t) := by
  exact lt_of_not_ge fun hStop ↦
    (not_le_of_gt ht)
      ((iterativeSmoothingStoppingIndex_isLeast hTerminate).2
        (by simpa [iterativeSmoothingStoppingCriterion] using hStop))

/-- The textbook stopping time `T`, defined from the first stopping index `s` by `T = s + 1`. -/
def iterativeSmoothingStoppingTime
    {a : Fin (m : ℕ) → E} {xHat : ℕ → E}
    (hTerminate : iterativeSmoothingTerminates a xHat) : ℕ :=
  iterativeSmoothingStoppingIndex hTerminate + 1

/-- At the textbook stopping time `T`, the acceptance inequality
`f(\hat x_T) ≥ (1 / e) f(\hat x_{T-1})` holds. -/
theorem iterativeSmoothingStoppingTime_spec
    {a : Fin (m : ℕ) → E} {xHat : ℕ → E}
    (hTerminate : iterativeSmoothingTerminates a xHat) :
    maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|)
      (xHat (iterativeSmoothingStoppingTime hTerminate)) ≥
      iterativeSmoothingStoppingFactor *
        maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|)
          (xHat (iterativeSmoothingStoppingIndex hTerminate)) := by
  simpa [iterativeSmoothingStoppingTime] using
    iterativeSmoothingStoppingIndex_spec hTerminate

/-- The output point of Algorithm 7.9 is the accepted iterate `\hat x_T`. -/
def iterativeSmoothingOutputPoint
    {a : Fin (m : ℕ) → E} {xHat : ℕ → E}
    (hTerminate : iterativeSmoothingTerminates a xHat) : E :=
  xHat (iterativeSmoothingStoppingTime hTerminate)

/-- The output point is exactly the iterate indexed by the textbook stopping time `T`. -/
theorem iterativeSmoothingOutputPoint_eq
    {a : Fin (m : ℕ) → E} {xHat : ℕ → E}
    (hTerminate : iterativeSmoothingTerminates a xHat) :
    iterativeSmoothingOutputPoint hTerminate =
      xHat (iterativeSmoothingStoppingTime hTerminate) :=
  rfl

end

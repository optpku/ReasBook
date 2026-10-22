/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Algorithm_7_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped MatrixGameRelativeScaleNotation StandardSimplex

variable {m n : ℕ+}

local notation "Δₙ" => Δ[(n : ℕ)]
local notation "PosMat" => { G : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ // Matrix.PosDef G }
local notation "DiagPosMat" =>
  { G : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ // Matrix.IsDiag G ∧ Matrix.PosDef G }
local notation "Solver" =>
  (Δₙ → ℝ) → ℝ → Set Δₙ → PosMat → Δₙ → ℕ → Δₙ

/- Theorem 7.12 lies in Chapter 7's nonnegative matrix-game / relative-scale outer-iteration
domain.

Sampled owner-style declarations:
- `Δ[n]` in `Chap06/Definition_6_11.lean`, the chapter simplex owner for finite matrix-game
  iterates;
- `matrixGameRelativeScaleIterate`, `matrixGameRelativeScaleTerminates`,
  `matrixGameRelativeScaleStoppingTime`, and `matrixGameRelativeScaleStoppingTime_min` in
  `Algorithm_7_10.lean`, the canonical owner API for the outer orbit and first accepted stage;
- `matrixGameRelativeScaleBlockLength` in `Algorithm_7_10.lean`, the canonical per-stage
  lower-level budget;
- `iterativeSmoothingTotalLowerLevelSteps` and the split statement surface in
  `Theorem_7_11.lean`, the nearby Chapter 7 pattern for stopping-time and total-work bounds;
- `IsRelativeAccuracy` in `Definition_7_1.lean`, the chapter owner for terminal relative-value
  accuracy.

Best owner abstraction:
- source-facing: Theorem 7.12's stopping-time, terminal-value, and total-work bounds for the
  nonnegative matrix-game relative-scale method;
- core/canonical: the Algorithm 7.10 owners
  `matrixGameRelativeScaleIterate m S f fμ D δ`,
  `matrixGameRelativeScaleStoppingTime hTerminate`,
  `matrixGameRelativeScaleOutputPoint hTerminate`, and
  `matrixGameRelativeScaleBlockLength m n δ`;
- bridge/view: the derived total lower-level work
  `matrixGameRelativeScaleTotalLowerLevelSteps hTerminate`.

Primitive data:
- the objective `f`, smoothing family `fμ`, diagonal positive-definite matrix data `D`,
  parameter `δ`, lower-level solver `S`, and canonical termination witness `hTerminate`;
- feasibility of the generated orbit, the feasible-set lower bound for `fStar`, the positivity
  regimes `0 < fStar` and `0 < δ`, the initial-value bound, and the terminal relative-gap
  estimate.

Derived API:
- the generated points `\hat x_t`;
- the stopping time `T`;
- the accepted output point `\hat x_T`;
- the total lower-level work up to `T`;
- the optional `IsRelativeAccuracy` packaging of the terminal-value conclusion.

Source/core/bridge triage:
- source-facing: the three atomic theorem clauses below;
- core/canonical: the Algorithm 7.10 orbit, stopping-time, and block-length owners;
- bridge/view: `matrixGameRelativeScaleTotalLowerLevelSteps`.
-/

/-- The total number of lower-level steps used by Algorithm 7.10 up to its canonical stopping
time, assuming that each outer stage uses the canonical block length
`matrixGameRelativeScaleBlockLength m n δ`. -/
def matrixGameRelativeScaleTotalLowerLevelSteps
    {S : Solver} {f : Δₙ → ℝ} {fμ : ℝ → Δₙ → ℝ} {D : DiagPosMat} {δ : ℝ}
    (hTerminate : matrixGameRelativeScaleTerminates m S f fμ D δ) : ℕ :=
  matrixGameRelativeScaleStoppingTime hTerminate *
    matrixGameRelativeScaleBlockLength m n δ

-- Proof sketch: unfold `matrixGameRelativeScaleTotalLowerLevelSteps`.
/-- Expanding `matrixGameRelativeScaleTotalLowerLevelSteps hTerminate` gives the product of the
canonical stopping time and the canonical per-stage lower-level work budget. -/
theorem matrixGameRelativeScaleTotalLowerLevelSteps_def
    {S : Solver} {f : Δₙ → ℝ} {fμ : ℝ → Δₙ → ℝ} {D : DiagPosMat} {δ : ℝ}
    (hTerminate : matrixGameRelativeScaleTerminates m S f fμ D δ) :
    matrixGameRelativeScaleTotalLowerLevelSteps hTerminate =
      matrixGameRelativeScaleStoppingTime hTerminate *
        matrixGameRelativeScaleBlockLength m n δ :=
  rfl

section Complexity

variable
  {S : Solver} {f : Δₙ → ℝ} {fμ : ℝ → Δₙ → ℝ} {D : DiagPosMat}
  {δ fStar : ℝ} {feasibleSet : Set Δₙ}

local notation "x̂" => x̂[m; S; f; fμ; D | δ]

/-- Helper for Theorem 7.12: before the first accepted stage, each failed acceptance test shrinks
the objective by the factor `e⁻¹`, so the value at stage `t` is bounded by
`exp (-t) * f (\hat x_0)`. -/
lemma matrixGameRelativeScale_value_le_exp_neg_until_stoppingIndex
    (hTerminate : matrixGameRelativeScaleTerminates m S f fμ D δ) :
    ∀ ⦃t : ℕ⦄, t ≤ matrixGameRelativeScaleStoppingIndex hTerminate →
      f (x̂ t) ≤ Real.exp (-(t : ℝ)) * f (x̂ 0) := by
  intro t ht
  induction' t with t ih
  · -- The geometric bound is exact at the initial iterate.
    simp
  · -- Each preterminal stage fails the stopping test, so one more factor `e⁻¹` is gained.
    have ht_lt : t < matrixGameRelativeScaleStoppingIndex hTerminate := Nat.lt_of_succ_le ht
    have hfail :
        f (x̂ (t + 1)) <
          matrixGameRelativeScaleStoppingFactor * f (x̂ t) :=
      matrixGameRelativeScaleStoppingIndex_min hTerminate ht_lt
    have hprev :
        f (x̂ t) ≤ Real.exp (-(t : ℝ)) * f (x̂ 0) :=
      ih (Nat.le_of_lt ht_lt)
    have hfactor_nonneg : 0 ≤ matrixGameRelativeScaleStoppingFactor := by
      rw [matrixGameRelativeScaleStoppingFactor_def]
      positivity
    have hstep :
        f (x̂ (t + 1)) ≤
          matrixGameRelativeScaleStoppingFactor * (Real.exp (-(t : ℝ)) * f (x̂ 0)) := by
      exact (le_of_lt hfail).trans (mul_le_mul_of_nonneg_left hprev hfactor_nonneg)
    calc
      f (x̂ (t + 1))
          ≤ matrixGameRelativeScaleStoppingFactor * (Real.exp (-(t : ℝ)) * f (x̂ 0)) := hstep
      _ = Real.exp (-((t + 1 : ℕ) : ℝ)) * f (x̂ 0) := by
            calc
              matrixGameRelativeScaleStoppingFactor * (Real.exp (-(t : ℝ)) * f (x̂ 0))
                  = ((1 / Real.exp 1) * Real.exp (-(t : ℝ))) * f (x̂ 0) := by
                      rw [matrixGameRelativeScaleStoppingFactor_def]
                      ring
              _ = (Real.exp (-1) * Real.exp (-(t : ℝ))) * f (x̂ 0) := by
                    simp [Real.exp_neg, one_div]
              _ = Real.exp ((-1) + -(t : ℝ)) * f (x̂ 0) := by
                    rw [← Real.exp_add]
              _ = Real.exp (-((t + 1 : ℕ) : ℝ)) * f (x̂ 0) := by
                    congr 2
                    norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm]

-- Proof sketch: use `matrixGameRelativeScaleStoppingTime_min hTerminate` to get geometric decay
-- before the accepted stage, evaluate feasibility at the generated points via
-- `hGenerated_feasible`, compare `f*` with the preterminal objective value, and combine this
-- with the initial estimate `f (x̂ 0) ≤ 2 √n fStar`.
/-- Theorem 7.12 (1): if every generated point `\hat x_t` is feasible, feasible points have
objective value at least `f*`, and the initial value satisfies `f(\hat x_0) ≤ 2 √n f*`, then
the stopping time satisfies `T ≤ 1 + log (2 √n)`. -/
theorem matrixGameRelativeScale_stoppingTime_le
    (hTerminate : matrixGameRelativeScaleTerminates m S f fμ D δ)
    (hGenerated_feasible : ∀ t : ℕ, x̂ t ∈ feasibleSet)
    (hOptimal_value_le_of_feasible :
      ∀ (x : Δₙ) (_hx : x ∈ feasibleSet), fStar ≤ f x)
    (hfStar_pos : 0 < fStar)
    (hInitial_value_le :
      f (x̂ 0) ≤ 2 * Real.sqrt (n : ℝ) * fStar) :
    (matrixGameRelativeScaleStoppingTime hTerminate : ℝ) ≤
      1 + Real.log (2 * Real.sqrt (n : ℝ)) := by
  -- Compare the feasible preterminal value both with `fStar` and with the geometric-decay bound.
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast n.2
  have hTwo_sqrt_pos : 0 < 2 * Real.sqrt (n : ℝ) := by
    have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn_pos
    positivity
  have hs_feasible :
      x̂ (matrixGameRelativeScaleStoppingIndex hTerminate) ∈ feasibleSet :=
    hGenerated_feasible _
  have hs_lower :
      fStar ≤ f (x̂ (matrixGameRelativeScaleStoppingIndex hTerminate)) :=
    hOptimal_value_le_of_feasible _ hs_feasible
  have hs_decay :
      f (x̂ (matrixGameRelativeScaleStoppingIndex hTerminate)) ≤
        Real.exp (-(matrixGameRelativeScaleStoppingIndex hTerminate : ℝ)) * f (x̂ 0) :=
    matrixGameRelativeScale_value_le_exp_neg_until_stoppingIndex
      (hTerminate := hTerminate) le_rfl
  have hs_initial :
      Real.exp (-(matrixGameRelativeScaleStoppingIndex hTerminate : ℝ)) * f (x̂ 0) ≤
        Real.exp (-(matrixGameRelativeScaleStoppingIndex hTerminate : ℝ)) *
          (2 * Real.sqrt (n : ℝ) * fStar) := by
    exact mul_le_mul_of_nonneg_left hInitial_value_le (by positivity)
  have hpreterminal_bound :
      fStar ≤
        Real.exp (-(matrixGameRelativeScaleStoppingIndex hTerminate : ℝ)) *
          (2 * Real.sqrt (n : ℝ) * fStar) := by
    exact hs_lower.trans (hs_decay.trans hs_initial)
  have hnormalized :
      1 ≤
        Real.exp (-(matrixGameRelativeScaleStoppingIndex hTerminate : ℝ)) *
          (2 * Real.sqrt (n : ℝ)) := by
    have hscaled :
        fStar ≤
          (Real.exp (-(matrixGameRelativeScaleStoppingIndex hTerminate : ℝ)) *
              (2 * Real.sqrt (n : ℝ))) * fStar := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hpreterminal_bound
    nlinarith
  -- Multiplying by `exp s` isolates the stopping index and allows a logarithmic conclusion.
  have hExp_bound :
      Real.exp (matrixGameRelativeScaleStoppingIndex hTerminate : ℝ) ≤
        2 * Real.sqrt (n : ℝ) := by
    have hMul :=
      mul_le_mul_of_nonneg_left hnormalized (le_of_lt (Real.exp_pos _))
    calc
      Real.exp (matrixGameRelativeScaleStoppingIndex hTerminate : ℝ)
          = Real.exp (matrixGameRelativeScaleStoppingIndex hTerminate : ℝ) * 1 := by ring
      _ ≤ Real.exp (matrixGameRelativeScaleStoppingIndex hTerminate : ℝ) *
            (Real.exp (-(matrixGameRelativeScaleStoppingIndex hTerminate : ℝ)) *
              (2 * Real.sqrt (n : ℝ))) := hMul
      _ = 2 * Real.sqrt (n : ℝ) := by
            calc
              Real.exp (matrixGameRelativeScaleStoppingIndex hTerminate : ℝ) *
                  (Real.exp (-(matrixGameRelativeScaleStoppingIndex hTerminate : ℝ)) *
                    (2 * Real.sqrt (n : ℝ)))
                  = (Real.exp (matrixGameRelativeScaleStoppingIndex hTerminate : ℝ) *
                      Real.exp (-(matrixGameRelativeScaleStoppingIndex hTerminate : ℝ))) *
                      (2 * Real.sqrt (n : ℝ)) := by ring
              _ = Real.exp
                    ((matrixGameRelativeScaleStoppingIndex hTerminate : ℝ) +
                      -(matrixGameRelativeScaleStoppingIndex hTerminate : ℝ)) *
                    (2 * Real.sqrt (n : ℝ)) := by
                      rw [← Real.exp_add]
              _ = 2 * Real.sqrt (n : ℝ) := by simp
  have hs_le_log :
      (matrixGameRelativeScaleStoppingIndex hTerminate : ℝ) ≤
        Real.log (2 * Real.sqrt (n : ℝ)) :=
    (Real.le_log_iff_exp_le hTwo_sqrt_pos).2 hExp_bound
  -- Converting `T = s + 1` finishes the stopping-time bound.
  simpa [matrixGameRelativeScaleStoppingTime, Nat.cast_add, add_assoc, add_left_comm, add_comm]
    using add_le_add_left hs_le_log 1

-- Proof sketch: multiply the terminal relative-gap estimate by `1 + δ`, use `0 < 1 + δ`, and
-- rearrange the resulting inequality to isolate `f x̂T`.
/-- Theorem 7.12 (2): the accepted output point satisfies
`f(\hat x_T) ≤ (1 + δ) f*` once `δ > 0` and the terminal relative-gap estimate from the
relative-scale analysis is available. -/
theorem matrixGameRelativeScale_outputPoint_value_le
    (hTerminate : matrixGameRelativeScaleTerminates m S f fμ D δ)
    (hδ : 0 < δ)
    (hTerminal_relative_gap :
      f (matrixGameRelativeScaleOutputPoint hTerminate) - fStar ≤
        (δ / (1 + δ)) * f (matrixGameRelativeScaleOutputPoint hTerminate)) :
    f (matrixGameRelativeScaleOutputPoint hTerminate) ≤ (1 + δ) * fStar := by
  have hOne_add_δ : 0 < 1 + δ := by
    linarith
  -- Scale the terminal gap inequality by the positive factor `1 + δ`.
  have hScaled :
      (f (matrixGameRelativeScaleOutputPoint hTerminate) - fStar) * (1 + δ) ≤
        δ * f (matrixGameRelativeScaleOutputPoint hTerminate) := by
    have hMul :=
      mul_le_mul_of_nonneg_right hTerminal_relative_gap hOne_add_δ.le
    have hOne_add_δ_ne : (1 + δ) ≠ 0 := ne_of_gt hOne_add_δ
    simpa [div_eq_mul_inv, hOne_add_δ_ne, mul_assoc, mul_left_comm, mul_comm] using hMul
  -- Rearranging isolates the output value on the left.
  nlinarith [hScaled]

-- Proof sketch: combine Theorem 7.12 (1) with the definition of
-- `matrixGameRelativeScaleTotalLowerLevelSteps` as the product of the canonical stopping time and
-- the canonical block length, then expand the block-length formula.
/-- Theorem 7.12 (3): the total number of lower-level steps does not exceed
`4 e (1 + log (2 √n)) √(2 n log m) (1 + 1 / δ)` under the same feasibility and initial-value
hypotheses together with `δ > 0`. -/
theorem matrixGameRelativeScale_totalLowerLevelSteps_le
    (hTerminate : matrixGameRelativeScaleTerminates m S f fμ D δ)
    (hδ : 0 < δ)
    (hGenerated_feasible : ∀ t : ℕ, x̂ t ∈ feasibleSet)
    (hOptimal_value_le_of_feasible :
      ∀ (x : Δₙ) (_hx : x ∈ feasibleSet), fStar ≤ f x)
    (hfStar_pos : 0 < fStar)
    (hInitial_value_le :
      f (x̂ 0) ≤ 2 * Real.sqrt (n : ℝ) * fStar) :
    (matrixGameRelativeScaleTotalLowerLevelSteps hTerminate : ℝ) ≤
      4 * Real.exp 1 * (1 + Real.log (2 * Real.sqrt (n : ℝ))) *
        Real.sqrt (2 * (n : ℝ) * Real.log (m : ℝ)) * (1 + 1 / δ) := by
  -- Rewrite the total work as stopping time times the canonical block length.
  have hTime_bound :
      (matrixGameRelativeScaleStoppingTime hTerminate : ℝ) ≤
        1 + Real.log (2 * Real.sqrt (n : ℝ)) :=
    matrixGameRelativeScale_stoppingTime_le
      (hTerminate := hTerminate)
      hGenerated_feasible hOptimal_value_le_of_feasible hfStar_pos hInitial_value_le
  have hTime_bound_nonneg : 0 ≤ 1 + Real.log (2 * Real.sqrt (n : ℝ)) := by
    positivity
  have hBlock_expr_nonneg :
      0 ≤ 4 * Real.exp 1 * Real.sqrt (2 * (n : ℝ) * Real.log (m : ℝ)) * (1 + 1 / δ) := by
    positivity
  have hBlock_bound :
      (matrixGameRelativeScaleBlockLength m n δ : ℝ) ≤
        4 * Real.exp 1 * Real.sqrt (2 * (n : ℝ) * Real.log (m : ℝ)) * (1 + 1 / δ) := by
    rw [matrixGameRelativeScaleBlockLength_def]
    exact Nat.floor_le hBlock_expr_nonneg
  have hMul_time :
      (matrixGameRelativeScaleStoppingTime hTerminate : ℝ) *
          (matrixGameRelativeScaleBlockLength m n δ : ℝ) ≤
        (1 + Real.log (2 * Real.sqrt (n : ℝ))) *
          (matrixGameRelativeScaleBlockLength m n δ : ℝ) := by
    exact mul_le_mul_of_nonneg_right hTime_bound (by positivity)
  have hMul_block :
      (1 + Real.log (2 * Real.sqrt (n : ℝ))) *
          (matrixGameRelativeScaleBlockLength m n δ : ℝ) ≤
        (1 + Real.log (2 * Real.sqrt (n : ℝ))) *
          (4 * Real.exp 1 * Real.sqrt (2 * (n : ℝ) * Real.log (m : ℝ)) * (1 + 1 / δ)) := by
    exact mul_le_mul_of_nonneg_left hBlock_bound hTime_bound_nonneg
  calc
    (matrixGameRelativeScaleTotalLowerLevelSteps hTerminate : ℝ)
        = (matrixGameRelativeScaleStoppingTime hTerminate : ℝ) *
            (matrixGameRelativeScaleBlockLength m n δ : ℝ) := by
              rw [matrixGameRelativeScaleTotalLowerLevelSteps_def, Nat.cast_mul]
    _ ≤ (1 + Real.log (2 * Real.sqrt (n : ℝ))) *
          (matrixGameRelativeScaleBlockLength m n δ : ℝ) := hMul_time
    _ ≤ (1 + Real.log (2 * Real.sqrt (n : ℝ))) *
          (4 * Real.exp 1 * Real.sqrt (2 * (n : ℝ) * Real.log (m : ℝ)) * (1 + 1 / δ)) :=
          hMul_block
    _ = 4 * Real.exp 1 * (1 + Real.log (2 * Real.sqrt (n : ℝ))) *
          Real.sqrt (2 * (n : ℝ) * Real.log (m : ℝ)) * (1 + 1 / δ) := by
          ring_nf

-- Proof sketch: package the lower and upper bounds on `f x̂T` together with `0 < fStar` into the
-- three conjuncts defining `IsRelativeAccuracy`.
/-- If the optimal value `f*` is positive and the accepted output value is already known to lie
between `f*` and `(1 + δ) f*`, then the output value in Theorem 7.12 has relative accuracy `δ`
in the sense of Definition 7.1. -/
theorem matrixGameRelativeScale_outputPoint_isRelativeAccuracy
    (hTerminate : matrixGameRelativeScaleTerminates m S f fμ D δ)
    (hfStar_pos : 0 < fStar)
    (hOutput_value_ge : fStar ≤ f (matrixGameRelativeScaleOutputPoint hTerminate))
    (hOutput_value_le :
      f (matrixGameRelativeScaleOutputPoint hTerminate) ≤ (1 + δ) * fStar) :
    IsRelativeAccuracy fStar δ (f (matrixGameRelativeScaleOutputPoint hTerminate)) := by
  -- The relative-accuracy predicate is exactly the conjunction of these three bounds.
  exact ⟨hfStar_pos, hOutput_value_ge, hOutput_value_le⟩

end Complexity

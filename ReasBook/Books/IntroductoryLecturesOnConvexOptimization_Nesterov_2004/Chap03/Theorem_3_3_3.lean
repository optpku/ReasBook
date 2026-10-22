/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Algorithm_3_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_71
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_3_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [PseudoMetricSpace E]

open ConstrainedLevelMethod
open scoped BigOperators

local instance
    (method : ConstrainedLevelMethodInput E)
    (hrelative : method.RelativeStoppingExists)
    (hfinite : method.SelectedThresholdFinite hrelative) :
    DecidablePred (globallyStopsAt method hrelative hfinite) := by
  classical
  exact Classical.decPred _

/- Theorem 3.3.3 lies in the constrained level-method total internal-complexity domain.

Relevant owner declarations sampled before refining:
- `HasGeometricRateOfConvergence.iterationThreshold` in `Chap01/Definition_1_2_6`, the canonical
  owner of the logarithmic outer-iteration threshold;
- `selected_exactValue_le_epsilon_at_natCeil_masterIterationCountBound` in `Theorem_3_3_2`, the
  chapter source-facing threshold theorem for the displayed logarithmic bound;
- `levelMethodIterationCap` in `Theorem_3_3_1`, the canonical floor-plus-one cap for one inner
  level-method run at tolerance `χ ε`;
- `ConstrainedLevelMethod.stoppingIndex` in `Algorithm_3_11`, the canonical full-step internal
  iteration count at one master step;
- `ConstrainedLevelMethod.globalStopIndex` in `Algorithm_3_11`, the canonical terminal-step
  internal iteration count at the first globally stopping master step;
- `levelParameterObjective` in `Definition_3_71`, the owner of the `α`-dependent scalar factor
  `α * (1 - α)^2 * (2 - α)`;

Best owner abstraction:
- source-facing: the total internal iteration count of a constrained level method up to the first
  globally stopping master step;
- core/canonical: the geometric-rate threshold owner for `N(ε)` together with the method-owned
  full-step and terminal-step internal counters;
- bridge/view: the arithmetic comparison that combines the outer-step bound with the summed
  full-step and terminal-step contributions.

Primitive data:
- the natural-ceiling outer-step cap from Theorem `3.3.2`,
  `⌈Real.log ((t0 - tStar) / ((1 - χ) * ε)) / Real.log (2 * (1 - χ))⌉₊`;
- the canonical one-run full-step cap
  `levelMethodIterationCap M_f D (χ * ε) α = ⌊K⌋ + 1`;
- the actual full-step iteration counts `stoppingIndex method hrelative hfinite i`;
- the first globally stopping master step `k`, recorded by
  `IsLeast {i : ℕ | globallyStopsAt method hrelative hfinite i} k`,
  together with its actual terminal-step iteration count
  `globalStopIndex method hrelative hfinite k hfirst.1`;
- the per-step cost owner `constrainedLevelMethodInternalIterationBound M_f D χ ε α`.

Derived API:
- the expanded rational form of the per-step factor;
- the bridge from the raw real-valued bound `K` to the owner cap `⌊K⌋ + 1`;
- the arithmetic helper that compares the summed full-step and terminal-step contributions with the
  natural-ceiling bound `(N(ε) + 1) levelMethodIterationCap ...`.

Source/core/bridge triage:
- source-facing: the constrained level method and its actual internal iteration counts;
- core/canonical: `levelMethodIterationCap`, `ConstrainedLevelMethod.stoppingIndex`,
  `ConstrainedLevelMethod.globalStopIndex`,
  `HasGeometricRateOfConvergence.iterationThreshold`, and `levelParameterObjective`;
- bridge/view: the scalar arithmetic comparison used internally once the actual iteration counts
  have already been assembled.
-/

/-- The uniform bound on the number of internal iterations contributed by one master step of the
constrained level method. -/
abbrev constrainedLevelMethodInternalIterationBound (M_f D χ ε α : ℝ) : ℝ :=
  M_f ^ (2 : ℕ) * D ^ (2 : ℕ) /
    (χ ^ (2 : ℕ) * ε ^ (2 : ℕ) * levelParameterObjective α)

/-- Unfolding `constrainedLevelMethodInternalIterationBound` recovers the displayed rational
expression for the per-step complexity bound. -/
-- Proof sketch: unfold `constrainedLevelMethodInternalIterationBound`.
theorem constrainedLevelMethodInternalIterationBound_eq
    (M_f D χ ε α : ℝ) :
    constrainedLevelMethodInternalIterationBound M_f D χ ε α =
      M_f ^ (2 : ℕ) * D ^ (2 : ℕ) /
        (χ ^ (2 : ℕ) * ε ^ (2 : ℕ) * α * (1 - α) ^ (2 : ℕ) * (2 - α)) := by
  simp [constrainedLevelMethodInternalIterationBound, levelParameterObjective, mul_assoc,
    mul_left_comm, mul_comm]

/-- The per-step constrained level-method internal-iteration bound is nonnegative for admissible
level parameters `α ∈ [0, 1]`. -/
theorem constrainedLevelMethodInternalIterationBound_nonneg
    (M_f D χ ε α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ constrainedLevelMethodInternalIterationBound M_f D χ ε α := by
  rw [constrainedLevelMethodInternalIterationBound_eq]
  have htwo_sub_nonneg : 0 ≤ 2 - α := by
    linarith [hα.2]
  have hden_nonneg :
      0 ≤ χ ^ (2 : ℕ) * ε ^ (2 : ℕ) * α * (1 - α) ^ (2 : ℕ) * (2 - α) := by
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (sq_nonneg χ) (sq_nonneg ε))
            hα.1)
          (sq_nonneg (1 - α)))
        htwo_sub_nonneg
  exact div_nonneg (mul_nonneg (sq_nonneg M_f) (sq_nonneg D)) hden_nonneg

/-- The displayed real-valued internal-iteration bound is dominated by the canonical floor-plus-one
one-run cap from Theorem `3.3.1` at tolerance `χ ε`. -/
theorem constrainedLevelMethodInternalIterationBound_le_levelMethodIterationCap
    (M_f D χ ε α : ℝ) :
    constrainedLevelMethodInternalIterationBound M_f D χ ε α ≤
      (levelMethodIterationCap M_f D (χ * ε) α : ℝ) := by
  simpa [constrainedLevelMethodInternalIterationBound, levelMethodIterationCap, mul_assoc,
      mul_left_comm, mul_comm, mul_pow] using
    (Nat.lt_floor_add_one
      (M_f ^ (2 : ℕ) * D ^ (2 : ℕ) /
        ((χ * ε) ^ (2 : ℕ) * levelParameterObjective α))).le

-- Arithmetic helper used by the source-facing total-complexity theorem below.
private theorem totalComplexity_le_of_natOuterCap_and_internalCostBound
    {fullMasterSteps outerCap stepCap : ℕ} {fullStepComplexity finalStepComplexity : ℝ}
    (houter : fullMasterSteps ≤ outerCap)
    (hfull : fullStepComplexity ≤ (fullMasterSteps : ℝ) * stepCap)
    (hfinal : finalStepComplexity ≤ stepCap) :
    fullStepComplexity + finalStepComplexity ≤ ((outerCap : ℝ) + 1) * stepCap := by
  have hfull' : fullStepComplexity ≤ (outerCap : ℝ) * stepCap := by
    exact hfull.trans <|
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr houter) (show 0 ≤ (stepCap : ℝ) by positivity)
  nlinarith

/-- Theorem 3.3.3: if a constrained level method has a globally stopping master step, if each
preceding full master step before the first globally stopping one is bounded by the canonical
one-run cap `levelMethodIterationCap M_f D (χ ε) α`, if the terminal globally stopping master
step satisfies the raw bound `constrainedLevelMethodInternalIterationBound M_f D χ ε α`, and if
the number of preceding full master steps is bounded by the natural ceiling of the logarithmic
threshold from Theorem `3.3.2`, then the total number of internal iterations executed up to that
first globally stopping step is bounded by `(N(ε) + 1)` copies of the canonical cap
`levelMethodIterationCap M_f D (χ ε) α`. -/
theorem constrained_level_total_internal_iterations_le
    (method : ConstrainedLevelMethodInput E)
    (hrelative : method.RelativeStoppingExists)
    (hfinite : method.SelectedThresholdFinite hrelative)
    {k : ℕ}
    (hfirst : IsLeast {i : ℕ | globallyStopsAt method hrelative hfinite i} k)
    {M_f D tStar : ℝ}
    (houter :
      k ≤
        ⌈Real.log
            ((method.initialParameter - tStar) /
              ((1 - method.chi) * method.epsilon)) /
          Real.log (2 * (1 - method.chi))⌉₊)
    (hfull_internal :
      ∀ i < k,
        stoppingIndex method hrelative hfinite i ≤
          levelMethodIterationCap
            M_f D (method.chi * method.epsilon) method.levelCoefficient)
    (hterminal_internal :
      (globalStopIndex method hrelative hfinite k hfirst.1 : ℝ) ≤
        constrainedLevelMethodInternalIterationBound
          M_f D method.chi method.epsilon method.levelCoefficient) :
    (∑ i ∈ Finset.range k, (stoppingIndex method hrelative hfinite i : ℝ)) +
        (globalStopIndex method hrelative hfinite k hfirst.1 : ℝ) ≤
      (((⌈Real.log
              ((method.initialParameter - tStar) /
                ((1 - method.chi) * method.epsilon)) /
            Real.log (2 * (1 - method.chi))⌉₊ : ℕ) : ℝ) + 1) *
        levelMethodIterationCap
          M_f D (method.chi * method.epsilon) method.levelCoefficient := by
  let N :=
    ⌈Real.log
        ((method.initialParameter - tStar) /
          ((1 - method.chi) * method.epsilon)) /
      Real.log (2 * (1 - method.chi))⌉₊
  let J :=
    levelMethodIterationCap
      M_f D (method.chi * method.epsilon) method.levelCoefficient
  have hfull_sum :
      (∑ i ∈ Finset.range k, (stoppingIndex method hrelative hfinite i : ℝ)) ≤ (k : ℝ) * J := by
    calc
      ∑ i ∈ Finset.range k, (stoppingIndex method hrelative hfinite i : ℝ)
        ≤ ∑ _i ∈ Finset.range k, (J : ℝ) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            exact_mod_cast hfull_internal i (Finset.mem_range.mp hi)
      _ = (k : ℝ) * J := by
            simp [J]
  have hterminal_internal' :
      (globalStopIndex method hrelative hfinite k hfirst.1 : ℝ) ≤ J := by
    exact hterminal_internal.trans <| by
      simpa [J] using
        constrainedLevelMethodInternalIterationBound_le_levelMethodIterationCap
          M_f D method.chi method.epsilon method.levelCoefficient
  exact
    totalComplexity_le_of_natOuterCap_and_internalCostBound
      (by simpa [N] using houter)
      hfull_sum
      (by simpa [J] using hterminal_internal')

end

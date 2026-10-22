/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_20
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_6_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient NewtonDecrement

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The safe explicit logarithmic iteration bound obtained by solving the geometric lower
estimate on the path parameters in the proof of Theorem `5.3.11`, clipped below by `1` to
account for the first positive step after `t₀ = 0`. -/
abbrev barrierPathFollowingTerminationBound
    (ν : NNReal) (β γ ε referenceObjectiveNorm : ℝ) : ℝ :=
  max 1 <|
    1 +
      Real.log
          (((barrierPathFollowingStoppingThreshold ν β ε) * (1 - β) * referenceObjectiveNorm) /
            (γ * (1 - 2 * β))) /
        Real.log (1 + γ / (β + Real.sqrt (ν : ℝ)))

-- Proof sketch: unfold `barrierPathFollowingTerminationBound`.
/-- Expanding `barrierPathFollowingTerminationBound ν β γ ε h` gives the logarithmic complexity
expression obtained by solving the geometric lower bound for `tₖ` against the stopping threshold
`(5.3.29)` using the exact geometric ratio `1 + γ / (β + √ν)`, clipped below by `1`. -/
theorem barrierPathFollowingTerminationBound_def
    (ν : NNReal) (β γ ε referenceObjectiveNorm : ℝ) :
    barrierPathFollowingTerminationBound ν β γ ε referenceObjectiveNorm =
      max (1 : ℝ)
        (1 +
          Real.log
              (((barrierPathFollowingStoppingThreshold ν β ε) * (1 - β) *
                  referenceObjectiveNorm) /
                (γ * (1 - 2 * β))) /
            Real.log (1 + γ / (β + Real.sqrt (ν : ℝ))) ) :=
  rfl

/-- Auxiliary infimum-style notation for the closure objective values of `⟪c, x⟫` on
`closure dom`. The source-facing theorem below uses `IsBarrierPathFollowingOptimalValue` as the
authoritative carrier for the prescribed optimal value `c*`. -/
abbrev barrierPathFollowingOptimalValue
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : E) (dom : Set E) : ℝ :=
  sInf ((fun x : E ↦ inner ℝ c x) '' closure dom)

/-- The scalar `c*` is the optimal value for minimizing `⟪c, x⟫` over `closure dom` when it is
the greatest lower bound of the closure objective values. This is the source-facing carrier for
Theorem `5.3.11`, which presupposes the optimal value rather than constructing it. -/
def IsBarrierPathFollowingOptimalValue
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : E) (dom : Set E) (cStar : ℝ) : Prop :=
  IsGLB ((fun x : E ↦ inner ℝ c x) '' closure dom) cStar

/-- Unfolding `IsBarrierPathFollowingOptimalValue c dom cStar` says exactly that `cStar` is the
greatest lower bound of the closure objective values. -/
theorem isBarrierPathFollowingOptimalValue_iff
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : E) (dom : Set E) (cStar : ℝ) :
    IsBarrierPathFollowingOptimalValue c dom cStar ↔
      IsGLB ((fun x : E ↦ inner ℝ c x) '' closure dom) cStar :=
  Iff.rfl

/-- Helper for Theorem 5.3.11: if `cStar` is the optimal value over `closure dom`, then every
closure point bounds `cStar` from above. -/
theorem optimalObjectiveValue_le_of_mem_closure
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : E) {dom : Set E} {cStar : ℝ}
    (hcStar : IsBarrierPathFollowingOptimalValue c dom cStar)
    (z : closure dom) :
    cStar ≤ inner ℝ c (z : E) :=
  by
  -- Evaluate the lower-bound component of the `IsGLB` witness at the chosen closure point.
  exact hcStar.1 (by exact ⟨z, z.2, rfl⟩)

/-- Helper for Theorem 5.3.11: every point of `closure dom` bounds
`barrierPathFollowingOptimalValue c dom` from above once the closure objective image is known to
be bounded below, so that the auxiliary infimum notation is mathematically meaningful. -/
theorem barrierPathFollowingOptimalValue_le_of_mem_closure
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : E) {dom : Set E}
    (hbounded :
      BddBelow ((fun x : E ↦ inner ℝ c x) '' closure dom))
    (z : closure dom) :
    barrierPathFollowingOptimalValue c dom ≤ inner ℝ c (z : E) :=
  by
  -- The closure objective value at `z` is one point of the image defining the infimum.
  exact csInf_le hbounded (by exact ⟨z, z.2, rfl⟩)

/-- The threshold-crossing condition from `(5.3.29)` at the index `N`: before `N` the path
parameter stays below the stopping threshold, and at `N` it reaches that threshold. -/
def pathFollowingThresholdCrossing
    (ν : NNReal) (β ε : ℝ) (t : ℕ → ℝ) (N : ℕ) : Prop :=
  (∀ ⦃k : ℕ⦄, k < N → t k < barrierPathFollowingStoppingThreshold ν β ε) ∧
    barrierPathFollowingStoppingThreshold ν β ε ≤ t N

/-- Unfolding `pathFollowingThresholdCrossing ν β ε t N` recovers the two threshold-crossing
conditions from `(5.3.29)` at the index `N`. -/
theorem pathFollowingThresholdCrossing_iff
    (ν : NNReal) (β ε : ℝ) (t : ℕ → ℝ) (N : ℕ) :
    pathFollowingThresholdCrossing ν β ε t N ↔
      (∀ ⦃k : ℕ⦄, k < N → t k < barrierPathFollowingStoppingThreshold ν β ε) ∧
        barrierPathFollowingStoppingThreshold ν β ε ≤ t N :=
  Iff.rfl

/-- The terminal certificate at the index `N`: the path parameter first crosses the stopping
threshold there, and the corresponding iterate already has objective gap at most `ε`. -/
abbrev pathFollowingTerminalCertificate
    (c : E) (cStar : ℝ) (ν : NNReal) (β ε : ℝ)
    (t : ℕ → ℝ) (x : ℕ → E) (N : ℕ) : Prop :=
  pathFollowingThresholdCrossing ν β ε t N ∧
    inner ℝ c (x N) - cStar ≤ ε

/-- The source-faithful `O(√ν log (‖c‖* / ε))` iteration bound from Theorem `5.3.11`, written
with the standard globalized size `1 + ‖ · ‖` so the bound remains meaningful for every positive
target accuracy `ε`. -/
abbrev barrierPathFollowingIterationComplexityBound
    (ν : NNReal) (ε referenceObjectiveNorm : ℝ) (C : NNRealˣ) (N : ℕ) : Prop :=
  N ≤ ⌈((C : NNReal) : ℝ) *
      (1 + ‖Real.sqrt (ν : ℝ) * Real.log (referenceObjectiveNorm / ε)‖)⌉₊

/-- Unfolding `barrierPathFollowingIterationComplexityBound ν ε referenceObjectiveNorm C N`
recovers the source-faithful positive-constant `O(√ν log (‖c‖* / ε))` carrier used in
Theorem `5.3.11`. -/
theorem barrierPathFollowingIterationComplexityBound_iff
    (ν : NNReal) (ε referenceObjectiveNorm : ℝ) (C : NNRealˣ) (N : ℕ) :
    barrierPathFollowingIterationComplexityBound ν ε referenceObjectiveNorm C N ↔
      N ≤ ⌈((C : NNReal) : ℝ) *
        (1 + ‖Real.sqrt (ν : ℝ) * Real.log (referenceObjectiveNorm / ε)‖)⌉₊ :=
  Iff.rfl

/-- A lower-level explicit output package used in the proof-oriented formulation of Theorem
`5.3.11`: the stopping index is controlled by the Chapter 5 logarithmic ceiling bound, and the
stopping iterate already has objective gap at most `ε` relative to the prescribed optimal value
`c*`. -/
abbrev pathFollowingTerminationOutcome
    (c : E) (cStar : ℝ) (ν : NNReal) (β γ ε referenceObjectiveNorm : ℝ)
    (x : ℕ → E) (N : ℕ) : Prop :=
  N ≤ ⌈barrierPathFollowingTerminationBound ν β γ ε referenceObjectiveNorm⌉₊ ∧
    inner ℝ c (x N) - cStar ≤ ε

/-- The calibrated Chapter 5 short-step side conditions on the path-following parameters. The
parameters `β` and `γ` are required to come from one short-step witness `τ`, so the theorem uses
the genuine Chapter 5 update regime rather than only the weaker scalar inequalities
`0 ≤ β`, `β < 1 / 2`, and `0 < γ`. -/
class IsShortStepBarrierPathFollowingParameters (β γ : ℝ) : Prop where
  /-- The Chapter 5 short-step calibration witness. -/
  tau : ℝ
  /-- The calibration witness is nonnegative. -/
  tau_nonneg : 0 ≤ tau
  /-- The one-step centering-preservation regime uses `τ ≤ 1 / 2`. -/
  tau_le_half : tau ≤ 1 / 2
  /-- The centering parameter equals the Chapter 5 short-step calibration `β(τ)`. -/
  beta_eq : β = pathFollowingCenteringBeta tau
  /-- The step-size parameter equals the Chapter 5 short-step calibration `γ(τ) = τ - β(τ)`. -/
  gamma_eq : γ = pathFollowingGammaRadius tau
  /-- The centering parameter is nonnegative. -/
  beta_nonneg : 0 ≤ β
  /-- The centering parameter satisfies the textbook short-step threshold. -/
  beta_lt_half : β < 1 / 2
  /-- The step-size parameter is positive. -/
  gamma_pos : 0 < γ

/-- A proof-oriented stopping certificate for one Chapter 5 path-following scheme. It packages
the calibrated short-step witness together with the auxiliary geometric-growth, central-path, and
terminal-centering witnesses used in the textbook proof of Theorem `5.3.11`. -/
structure BarrierPathFollowingStopSpec
    {dom : Set E} (c : E) (F : E → ℝ) (ν : NNReal)
    [IsSelfConcordantBarrierOnWith dom ν F]
    (xStar : dom) (hxStarH : (fderiv ℝ (∇ F) (xStar : E)).det ≠ 0)
    {x0 : dom} (β γ ε : ℝ)
    (scheme : BarrierPathFollowingScheme c F ν x0 β γ ε) where
  /-- The centering parameter is nonnegative. -/
  beta_nonneg : 0 ≤ β
  /-- The centering parameter satisfies the textbook short-step threshold. -/
  beta_lt_half : β < 1 / 2
  /-- The step-size parameter is positive. -/
  gamma_pos : 0 < γ
  /-- The Chapter 5 short-step calibration witness. -/
  tau : ℝ
  /-- The calibration witness is nonnegative. -/
  tau_nonneg : 0 ≤ tau
  /-- The one-step centering-preservation regime uses `τ ≤ 1 / 2`. -/
  tau_le_half : tau ≤ 1 / 2
  /-- The centering parameter equals the Chapter 5 short-step calibration `β(τ)`. -/
  beta_eq : β = pathFollowingCenteringBeta tau
  /-- The step-size parameter equals the Chapter 5 short-step calibration `γ(τ) = τ - β(τ)`. -/
  gamma_eq : γ = pathFollowingGammaRadius tau
  /-- The source dual reference norm is positive. -/
  referenceObjectiveNorm_pos :
    0 <
      HessianDualLocalNorm.ofDetNeZero F (xStar : E)
        (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xStar.2)
        hxStarH
        ((InnerProductSpace.toDual ℝ E) c)
  /-- The textbook geometric lower bound for the path parameters along the method. -/
  hgrowth :
    ∀ k : ℕ, 1 ≤ k →
      (γ * (1 - 2 * β)) /
          ((1 - β) *
              HessianDualLocalNorm.ofDetNeZero F (xStar : E)
                (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xStar.2)
                hxStarH
                ((InnerProductSpace.toDual ℝ E) c)) *
          (1 + γ / (β + Real.sqrt (ν : ℝ))) ^ (k - 1) ≤
        scheme.t k
  /-- The stopping path parameter, viewed as a nonnegative scalar. -/
  tStop : Set.Ici (0 : ℝ)
  /-- The stopping path parameter matches the scalar parameter of the raw scheme. -/
  htStop : (tStop : ℝ) = scheme.t scheme.stopIndex
  /-- The stopping path parameter is positive. -/
  htStop_pos : 0 < (tStop : ℝ)
  /-- An exact minimizer of the penalty objective at the stopping parameter. -/
  xPath : dom
  /-- The penalty objective is minimized at `xPath` for the stopping parameter. -/
  hpath : IsMinOn (centralPathPenaltyObjective c F tStop) dom (xPath : E)
  /-- The terminal iterate satisfies the approximate-centering estimate from Theorem `5.3.10`. -/
  happrox_stop :
    HessianDualLocalNorm.ofDetNeZero F (scheme scheme.stopIndex)
        (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1
          (scheme.mem_domain scheme.stopIndex))
        (scheme.hessian_nondegenerate scheme.stopIndex)
        ((InnerProductSpace.toDual ℝ E)
          (scheme.t scheme.stopIndex • c + ∇ F (scheme scheme.stopIndex))) ≤
      β

/-- A stopping certificate carries the short-step scalar parameter conditions used throughout the
Chapter 5 path-following argument. -/
abbrev BarrierPathFollowingStopSpec.shortStepParameters
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    {c : E}
    {xStar : dom} {hxStarH : (fderiv ℝ (∇ F) (xStar : E)).det ≠ 0}
    {x0 : dom} {β γ ε : ℝ}
    {scheme : BarrierPathFollowingScheme c F ν x0 β γ ε}
    (hspec : BarrierPathFollowingStopSpec c F ν xStar hxStarH β γ ε scheme) :
    IsShortStepBarrierPathFollowingParameters β γ where
  tau := hspec.tau
  tau_nonneg := hspec.tau_nonneg
  tau_le_half := hspec.tau_le_half
  beta_eq := hspec.beta_eq
  gamma_eq := hspec.gamma_eq
  beta_nonneg := hspec.beta_nonneg
  beta_lt_half := hspec.beta_lt_half
  gamma_pos := hspec.gamma_pos

namespace BarrierPathFollowingScheme

/-- Helper for Theorem 5.3.11: the Hessian at the prescribed starting point `x₀` is
nondegenerate because the path-following scheme stores that fact at index `0`. -/
theorem hessian_nondegenerate_zero
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    {c : E} {x0 : dom} {β γ ε : ℝ}
    (scheme : BarrierPathFollowingScheme c F ν x0 β γ ε) :
    (fderiv ℝ (∇ F) (x0 : E)).det ≠ 0 := by
  simpa [scheme.x_zero] using scheme.hessian_nondegenerate 0

end BarrierPathFollowingScheme

/-- Helper for Theorem 5.3.11: an exact minimizer of the stopping-parameter penalty objective is
within `ν / t` of any closure comparison point, so the later GLB argument does not need an
attained optimizer. -/
private theorem centralPathPoint_objectiveGap_le_barrierParameter_div_of_mem_closure
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E) (t : Set.Ici (0 : ℝ)) (ht : 0 < (t : ℝ))
    (xOpt : closure dom)
    {xPath : dom}
    (hpath : IsMinOn (centralPathPenaltyObjective c F t) dom (xPath : E)) :
    inner ℝ c (xPath : E) - inner ℝ c (xOpt : E) ≤ (ν : ℝ) / (t : ℝ) := by
  let gap : ℝ := inner ℝ c (xPath : E) - inner ℝ c (xOpt : E)
  let scaledGap : ℝ := (t : ℝ) * gap
  -- Compare the penalty objective along the strict chord from `xPath` to the closure point.
  have hchord :
      ∀ α, α ∈ Set.Ico (0 : ℝ) 1 →
        α * scaledGap ≤ -(ν : ℝ) * Real.log (1 - α) := by
    intro α hα
    let z : E := (1 - α) • (xPath : E) + α • (xOpt : E)
    have hz_mem : z ∈ dom := strict_chord_mem_dom_of_mem_closure
      (hF := (inferInstance : IsSelfConcordantBarrierOnWith dom ν F)) xPath xOpt hα
    have hupper :
        F z ≤ F (xPath : E) - (ν : ℝ) * Real.log (1 - α) :=
      segment_upper_bound_log_one_sub_of_mem_closure
        (hF := (inferInstance : IsSelfConcordantBarrierOnWith dom ν F)) xPath xOpt hα
    have hmin :
        centralPathPenaltyObjective c F t (xPath : E) ≤ centralPathPenaltyObjective c F t z :=
      hpath hz_mem
    have hpair :
        inner ℝ c (xPath : E) - inner ℝ c z = α * gap := by
      dsimp [z, gap]
      calc
        inner ℝ c (xPath : E) - inner ℝ c ((1 - α) • (xPath : E) + α • (xOpt : E))
            = inner ℝ c (xPath : E) -
                ((1 - α) * inner ℝ c (xPath : E) + α * inner ℝ c (xOpt : E)) := by
                  rw [inner_add_right, inner_smul_right, inner_smul_right]
        _ = α * (inner ℝ c (xPath : E) - inner ℝ c (xOpt : E)) := by ring
        _ = α * gap := by rfl
    have hpen :
        (t : ℝ) * (inner ℝ c (xPath : E) - inner ℝ c z) ≤ F z - F (xPath : E) := by
      rw [centralPathPenaltyObjective_apply, centralPathPenaltyObjective_apply] at hmin
      linarith
    have hchord' :
        α * scaledGap ≤ -(ν : ℝ) * Real.log (1 - α) := by
      have hpen' :
          (t : ℝ) * (α * gap) ≤ F z - F (xPath : E) := by
        rw [hpair] at hpen
        simpa [scaledGap, mul_assoc, mul_left_comm, mul_comm] using hpen
      linarith
    exact hchord'
  -- Reuse the Chapter 5.3.10 scalar chord argument verbatim after removing the unused optimizer
  -- witness from the interface.
  have hscaled : scaledGap ≤ (ν : ℝ) := by
    by_cases hν : ν = 0
    · have hhalf :
          (1 / 2 : ℝ) * scaledGap ≤ -(ν : ℝ) * Real.log (1 - (1 / 2 : ℝ)) := by
        exact hchord (1 / 2 : ℝ) (by constructor <;> norm_num)
      rw [hν] at hhalf
      norm_num at hhalf
      linarith
    · have hν_pos : 0 < (ν : ℝ) := by
        exact_mod_cast (pos_iff_ne_zero.mpr hν)
      by_contra hgap_gt
      have hε_pos : 0 < scaledGap / (ν : ℝ) - 1 := by
        have hgap_gt' : (ν : ℝ) < scaledGap := by
          exact not_le.mp hgap_gt
        have hdiv_lt : 1 < scaledGap / (ν : ℝ) := by
          exact (one_lt_div hν_pos).2 hgap_gt'
        linarith
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε_pos
      have hα_mem : (1 / ((n : ℝ) + 2)) ∈ Set.Ico (0 : ℝ) 1 := by
        constructor
        · positivity
        · have htwo_pos : 0 < (n : ℝ) + 2 := by positivity
          exact (div_lt_one htwo_pos).2 (by linarith)
      have hstep :
          (1 / ((n : ℝ) + 2)) * scaledGap ≤
            -(ν : ℝ) * Real.log (1 - 1 / ((n : ℝ) + 2)) := by
        exact hchord (1 / ((n : ℝ) + 2)) hα_mem
      have hlog_bound :
          -(Real.log (1 - 1 / ((n : ℝ) + 2))) / (1 / ((n : ℝ) + 2)) ≤
            1 + 1 / ((n : ℝ) + 1) := by
        have hratio_pos : 0 < ((n : ℝ) + 2) / ((n : ℝ) + 1) := by positivity
        have hratio_bound :
            Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1)) ≤ 1 / ((n : ℝ) + 1) := by
          have hlog := Real.log_le_sub_one_of_pos hratio_pos
          have hden1_pos : 0 < (n : ℝ) + 1 := by positivity
          have hsplit :
              ((n : ℝ) + 2) / ((n : ℝ) + 1) = 1 + 1 / ((n : ℝ) + 1) := by
            field_simp [hden1_pos.ne']
            ring
          have hrewrite :
              ((n : ℝ) + 2) / ((n : ℝ) + 1) - 1 = 1 / ((n : ℝ) + 1) := by
            rw [hsplit]
            ring
          simpa [hrewrite] using hlog
        have hden1 : (n : ℝ) + 1 ≠ 0 := by positivity
        have hden2 : (n : ℝ) + 2 ≠ 0 := by positivity
        have hratio_eq :
            -(Real.log (1 - 1 / ((n : ℝ) + 2))) / (1 / ((n : ℝ) + 2)) =
              ((n : ℝ) + 2) * Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1)) := by
          have hbase_eq :
              (1 - 1 / ((n : ℝ) + 2) : ℝ) = ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
            field_simp [hden2]
            ring
          have hinv_eq :
              ((1 - 1 / ((n : ℝ) + 2)) : ℝ)⁻¹ = ((n : ℝ) + 2) / ((n : ℝ) + 1) := by
            rw [hbase_eq]
            field_simp [hden1, hden2]
          have hlog_inv :
              -Real.log (1 - 1 / ((n : ℝ) + 2)) =
                Real.log (((1 - 1 / ((n : ℝ) + 2)) : ℝ)⁻¹) := by
            exact (Real.log_inv (1 - 1 / ((n : ℝ) + 2))).symm
          calc
            -(Real.log (1 - 1 / ((n : ℝ) + 2))) / (1 / ((n : ℝ) + 2))
                = -(((n : ℝ) + 2) * Real.log (1 - 1 / ((n : ℝ) + 2))) := by
                    field_simp [hden2]
            _ = ((n : ℝ) + 2) * (-Real.log (1 - 1 / ((n : ℝ) + 2))) := by
                  ring
            _ = ((n : ℝ) + 2) * Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1)) := by
                  rw [hlog_inv, hinv_eq]
        calc
          -(Real.log (1 - 1 / ((n : ℝ) + 2))) / (1 / ((n : ℝ) + 2))
              = ((n : ℝ) + 2) * Real.log (((n : ℝ) + 2) / ((n : ℝ) + 1)) := hratio_eq
          _ ≤ ((n : ℝ) + 2) * (1 / ((n : ℝ) + 1)) := by
                exact mul_le_mul_of_nonneg_left hratio_bound (by positivity)
          _ = 1 + 1 / ((n : ℝ) + 1) := by
                field_simp [hden1]
                ring
      have hgap_bound :
          scaledGap ≤ (ν : ℝ) * (1 + 1 / ((n : ℝ) + 1)) := by
        have hα_pos : 0 < 1 / ((n : ℝ) + 2) := by positivity
        have hdiv_bound :
            scaledGap ≤
              (-(ν : ℝ) * Real.log (1 - 1 / ((n : ℝ) + 2))) /
                (1 / ((n : ℝ) + 2)) := by
          refine (le_div_iff₀ hα_pos).2 ?_
          simpa [mul_assoc, mul_left_comm, mul_comm] using hstep
        have hrhs_nonneg : 0 ≤ (ν : ℝ) := by
          exact_mod_cast ν.2
        calc
          scaledGap ≤
              (-(ν : ℝ) * Real.log (1 - 1 / ((n : ℝ) + 2))) /
                (1 / ((n : ℝ) + 2)) := hdiv_bound
          _ = (ν : ℝ) *
              (-(Real.log (1 - 1 / ((n : ℝ) + 2))) / (1 / ((n : ℝ) + 2))) := by
                field_simp [show (n : ℝ) + 2 ≠ 0 by positivity]
          _ ≤ (ν : ℝ) * (1 + 1 / ((n : ℝ) + 1)) := by
                exact mul_le_mul_of_nonneg_left hlog_bound hrhs_nonneg
      have hsmall :
          1 + 1 / ((n : ℝ) + 1) < scaledGap / (ν : ℝ) := by
        have := hn
        linarith
      have hlarge :
          (ν : ℝ) * (1 + 1 / ((n : ℝ) + 1)) < scaledGap := by
        simpa [mul_comm] using (lt_div_iff₀ hν_pos).1 hsmall
      exact (not_lt_of_ge hgap_bound) hlarge
  -- Divide the scaled gap bound by the positive stopping parameter.
  exact (le_div_iff₀ ht).2 (by simpa [gap, scaledGap, mul_comm] using hscaled)

/-- Helper for Theorem 5.3.11: the approximate-centering objective-gap estimate at the stopping
parameter only needs an arbitrary closure comparison point once the exact penalty minimizer is
available. -/
private theorem
    centralPathApproximateCenter_objectiveGap_le_barrierParameter_add_error_div_of_mem_closure
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E) (t : Set.Ici (0 : ℝ)) {β : ℝ} (ht : 0 < (t : ℝ)) (hβ : β < 1)
    (xOpt : closure dom)
    {xPath x : dom}
    (hpath : IsMinOn (centralPathPenaltyObjective c F t) dom (xPath : E))
    (hxH : (fderiv ℝ (∇ F) (x : E)).det ≠ 0)
    (happrox :
      HessianDualLocalNorm.ofDetNeZero F (x : E)
        (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 x.2) hxH
        ((InnerProductSpace.toDual ℝ E) ((t : ℝ) • c + ∇ F (x : E))) ≤ β) :
    inner ℝ c (x : E) - inner ℝ c (xOpt : E) ≤
      ((ν : ℝ) + ((β + Real.sqrt (ν : ℝ)) * β) / (1 - β)) / (t : ℝ) := by
  -- Route correction: use the corrected exact-gap companion theorem instead of threading an
  -- unnecessary optimizer witness through the stopping proof.
  have hcorr :
      inner ℝ c (x : E) - inner ℝ c (xPath : E) ≤
        ((β + Real.sqrt (ν : ℝ)) / (t : ℝ)) * (β / (1 - β)) :=
    centralPathPenalty_objectiveCorrection_le_error_div
      (dom := dom) (ν := ν) (F := F) c t ht hβ hpath hxH happrox
  have hgap :
      inner ℝ c (xPath : E) - inner ℝ c (xOpt : E) ≤ (ν : ℝ) / (t : ℝ) :=
    centralPathPoint_objectiveGap_le_barrierParameter_div_of_mem_closure
      (dom := dom) (ν := ν) (F := F) c t ht xOpt hpath
  have hsplit :
      inner ℝ c (x : E) - inner ℝ c (xOpt : E) =
        (inner ℝ c (x : E) - inner ℝ c (xPath : E)) +
          (inner ℝ c (xPath : E) - inner ℝ c (xOpt : E)) := by
    ring
  -- Add the approximate-center correction to the exact central-path gap and normalize the
  -- resulting scalar expression.
  calc
    inner ℝ c (x : E) - inner ℝ c (xOpt : E) =
        (inner ℝ c (x : E) - inner ℝ c (xPath : E)) +
          (inner ℝ c (xPath : E) - inner ℝ c (xOpt : E)) := hsplit
    _ ≤ ((β + Real.sqrt (ν : ℝ)) / (t : ℝ)) * (β / (1 - β)) + (ν : ℝ) / (t : ℝ) := by
          exact add_le_add hcorr hgap
    _ = ((ν : ℝ) + ((β + Real.sqrt (ν : ℝ)) * β) / (1 - β)) / (t : ℝ) := by
          field_simp [ht.ne', sub_ne_zero.mpr (ne_of_lt hβ)]
          ring

/-- Helper for Theorem 5.3.11: the linear penalty tilt has the expected constant gradient. -/
private theorem linearTilt_hasGradientAt
    {c : E} (t : ℝ) {x : E} :
    HasGradientAt (fun z : E ↦ t * inner ℝ c z) ((t : ℝ) • c) x := by
  -- Read the tilt through the corresponding scalar continuous linear map.
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa using (((t : ℝ) • innerSL ℝ c).hasFDerivAt :
    HasFDerivAt (fun z : E ↦ ((t : ℝ) • innerSL ℝ c) z) ((t : ℝ) • innerSL ℝ c) x)

/-- Helper for Theorem 5.3.11: a `C²` scalar field has a differentiable gradient map. -/
private theorem differentiableAt_gradient_ofContDiffAtTwo
    {g : E → ℝ} {x : E} (hg : ContDiffAt ℝ 2 g x) :
    DifferentiableAt ℝ (∇ g) x := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  -- Rewrite the gradient through the Riesz map so differentiability reduces to `fderiv`.
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ g) x := by
    exact
      (hg.fderiv_right
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  change DifferentiableAt ℝ (fun y ↦ D (fderiv ℝ g y)) x
  exact (D.hasFDerivAt.comp x hfdiff.hasFDerivAt).differentiableAt

/-- Helper for Theorem 5.3.11: on an open neighborhood where two scalar fields are `C²`, the
Hessian of their sum is the sum of their Hessians. -/
private theorem hessian_add_eq_ofContDiffOn
    {s : Set E} {f g : E → ℝ} {x : E}
    (hf : ContDiffOn ℝ 2 f s) (hg : ContDiffOn ℝ 2 g s)
    (hs_open : IsOpen s) (hx : x ∈ s) :
    hessian (fun y ↦ f y + g y) x = hessian f x + hessian g x := by
  have hgrad_nhds :
      (fun y ↦ ∇ (fun z : E ↦ f z + g z) y) =ᶠ[nhds x] fun y ↦ ∇ f y + ∇ g y := by
    -- Near `x`, both fields are differentiable, so the gradient is pointwise additive.
    filter_upwards [hs_open.mem_nhds hx] with y hy
    have hfy : DifferentiableAt ℝ f y := by
      exact (hf.contDiffAt (hs_open.mem_nhds hy)).differentiableAt (by norm_num)
    have hgy : DifferentiableAt ℝ g y := by
      exact (hg.contDiffAt (hs_open.mem_nhds hy)).differentiableAt (by norm_num)
    exact (hasGradientAt_add hfy.hasGradientAt hgy.hasGradientAt).gradient
  have hgradf : DifferentiableAt ℝ (∇ f) x := by
    -- A `C²` scalar field has a differentiable gradient map at the base point.
    exact differentiableAt_gradient_ofContDiffAtTwo (hf.contDiffAt (hs_open.mem_nhds hx))
  have hgradg : DifferentiableAt ℝ (∇ g) x := by
    exact differentiableAt_gradient_ofContDiffAtTwo (hg.contDiffAt (hs_open.mem_nhds hx))
  -- Differentiate the neighborhood identity for the gradient at the base point.
  rw [hessian, hgrad_nhds.fderiv_eq]
  change fderiv ℝ ((∇ f) + ∇ g) x = hessian f x + hessian g x
  rw [fderiv_add hgradf hgradg]

/-- Helper for Theorem 5.3.11: the linear penalty tilt has zero Hessian. -/
private theorem linearTilt_hessian_eq_zero
    {c : E} (t : ℝ) (x : E) :
    hessian (fun z : E ↦ t * inner ℝ c z) x = 0 := by
  have hgrad :
      ∇ (fun z : E ↦ t * inner ℝ c z) = fun _ : E ↦ (t : ℝ) • c := by
    -- The gradient field of a scalar linear map is constant.
    refine gradient_eq ?_
    intro y
    exact linearTilt_hasGradientAt (c := c) t
  -- Differentiate the constant gradient field.
  rw [hessian, hgrad]
  ext h
  simp

/-- Helper for Theorem 5.3.11: the linear penalty tilt does not change the Hessian. -/
private theorem centralPathPenaltyObjective_hessian_eq
    {dom : Set E} (c : E) (F : E → ℝ) (t : ℝ) (x : E)
    (hFcont : ContDiffAt ℝ 2 F x) :
    hessian (centralPathPenaltyObjective c F t) x = hessian F x := by
  obtain ⟨u, hu_nhds, hFu⟩ := hFcont.contDiffOn (m := 2) le_rfl (by simp)
  obtain ⟨s, hs_sub, hs_open, hx_mem⟩ := mem_nhds_iff.mp hu_nhds
  have hFs : ContDiffOn ℝ 2 F s := hFu.mono hs_sub
  have htilt_s : ContDiffOn ℝ 2 (fun z : E ↦ t * inner ℝ c z) s := by
    simpa using (((t : ℝ) • innerSL ℝ c).contDiff.contDiffOn :
      ContDiffOn ℝ 2 (fun z : E ↦ ((t : ℝ) • innerSL ℝ c) z) s)
  -- Work on an open `C²` neighborhood and then drop the zero Hessian of the linear tilt.
  calc
    hessian (centralPathPenaltyObjective c F t) x =
        hessian (fun z : E ↦ F z + t * inner ℝ c z) x := by
      rfl
    _ = hessian F x + hessian (fun z : E ↦ t * inner ℝ c z) x := by
      exact hessian_add_eq_ofContDiffOn hFs htilt_s hs_open hx_mem
    _ = hessian F x := by
      simp [linearTilt_hessian_eq_zero]

/-- Helper for Theorem 5.3.11: an approximate center for the stopping-parameter penalty objective
produces an exact minimizer by Theorem 5.1.13. -/
private theorem centralPathPenaltyObjective_hasMinimizer_of_approximateCenter
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E) (t : Set.Ici (0 : ℝ)) {β : ℝ}
    (x : dom)
    (hxH : (fderiv ℝ (∇ F) (x : E)).det ≠ 0)
    (hβ : β < 1)
    (happrox :
      HessianDualLocalNorm.ofDetNeZero F (x : E)
        (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 x.2)
        hxH
        ((InnerProductSpace.toDual ℝ E) ((t : ℝ) • c + ∇ F (x : E))) ≤ β) :
    ∃ xPath : dom, IsMinOn (centralPathPenaltyObjective c F t) dom (xPath : E) := by
  let ψ : E → ℝ := centralPathPenaltyObjective c F (t : ℝ)
  let hstdF : IsStandardSelfConcordantOn dom F := inferInstance
  let _ : IsStandardSelfConcordantOn dom ψ :=
    centralPathPenaltyObjective_isStandardSelfConcordantOn (dom := dom) (ν := ν) (F := F) c t
  let _ : IsSelfConcordantOnWith dom (1 : NNReal) ψ := inferInstance
  let _ : HasPositiveDefiniteHessianOn dom ψ := inferInstance
  have hFdiff :
      DifferentiableAt ℝ F (x : E) := by
    -- Barrier self-concordance gives the differentiability needed to rewrite the penalty gradient.
    exact
      (hstdF.contDiffOn.contDiffAt (hstdF.isOpen_domain.mem_nhds x.2)).differentiableAt
        (by norm_num)
  have hFcont :
      ContDiffAt ℝ 2 F (x : E) := by
    -- The same owner yields the `C²` regularity needed for the Hessian normalization.
    exact
      (hstdF.contDiffOn.contDiffAt (hstdF.isOpen_domain.mem_nhds x.2)).of_le
        (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hgrad :
      ∇ ψ (x : E) = (t : ℝ) • c + ∇ F (x : E) := by
    -- Differentiate the penalty objective before comparing Newton decrements.
    simpa [ψ] using (hasGradientAt_centralPathPenaltyObjective c F (t : ℝ) hFdiff).gradient
  have hlambda_eq :
      λ[ψ; (x : E) | x.2] =
        HessianDualLocalNorm.ofDetNeZero F (x : E)
          (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 x.2)
          hxH
          ((InnerProductSpace.toDual ℝ E) ((t : ℝ) • c + ∇ F (x : E))) := by
    -- Normalize both sides to the same inverse-Hessian pairing formula.
    rw [NewtonDecrement.ofPosDefMem_def]
    rw [HessianDualLocalNorm.ofDetNeZero_def]
    rw [hgrad, centralPathPenaltyObjective_hessian_eq (dom := dom) c F (t : ℝ) (x : E) hFcont]
  have hlambda :
      λ[ψ; (x : E) | x.2] ≤ β := by
    simpa [hlambda_eq] using happrox
  have hlambda_lt :
      λ[ψ; (x : E) | x.2] < 1 / ((1 : NNReal) : ℝ) := by
    simpa using (lt_of_le_of_lt hlambda hβ)
  -- Apply the Chapter 5.1.13 minimizer theorem to the tilted objective itself.
  rcases existsUnique_isMinOn_with_suboptimality_bound_of_newtonDecrement_lt_inv
      (Mf := (1 : NNReal)) (f := ψ) (dom := dom) (x := (x : E)) x.2 hlambda_lt with
    ⟨xPath, hxPath, _⟩
  exact ⟨xPath, hxPath.1⟩

/-- Helper for Theorem 5.3.11: a positive symmetric operator that has zero quadratic form on a
vector already annihilates that vector. -/
private theorem positiveOperator_apply_eq_zero_of_inner_eq_zero
    {H : E →L[ℝ] E} (hH : H.IsPositive) {v : E}
    (hv : inner ℝ v (H v) = 0) :
    H v = 0 := by
  let B : LinearMap.BilinForm ℝ E := ((innerSL ℝ).comp H).toBilinForm
  have hB_apply (u w : E) : B u w = inner ℝ (H u) w := rfl
  have hB_nonneg : ∀ u : E, 0 ≤ B u u := by
    intro u
    simpa [hB_apply, real_inner_comm] using hH.inner_nonneg_right u
  have hB_symm : LinearMap.IsSymm B := by
    rw [← LinearMap.BilinForm.isSymm_iff]
    rw [LinearMap.BilinForm.isSymm_def]
    intro u w
    rw [hB_apply, hB_apply]
    simpa [real_inner_comm] using hH.isSymmetric u w
  have hv_ker : v ∈ LinearMap.ker B := by
    exact (LinearMap.BilinForm.apply_apply_same_eq_zero_iff B hB_nonneg hB_symm).mp
      (by simpa [hB_apply, real_inner_comm] using hv)
  have hv_zero : B v = 0 := by
    simpa [LinearMap.mem_ker] using hv_ker
  -- Compare the operator output against every test vector through the symmetric bilinear form.
  apply ext_inner_right ℝ
  intro u
  have hu := congrArg (fun L : E →ₗ[ℝ] ℝ ↦ L u) hv_zero
  simpa [hB_apply] using hu

/-- Helper for Theorem 5.3.11: a vanishing Hessian dual norm forces the underlying vector to
vanish because the Hessian is positive and invertible. -/
private theorem eq_zero_of_hessianDualNormVector_eq_zero
    {F : E → ℝ} {x v : E}
    (hPos : (hessian F x).IsPositive)
    (hH : (fderiv ℝ (∇ F) x).det ≠ 0)
    (hzero : hessianDualNormVector F x hH v = 0) :
    v = 0 := by
  let H : E →L[ℝ] E := hessian F x
  have hInv : H.IsInvertible := hessian_isInvertible_of_det_ne_zero hH
  have hpair_nonneg : 0 ≤ inner ℝ v (H.inverse v) := by
    calc
      0 ≤ inner ℝ (H.inverse v) (H (H.inverse v)) := hPos.inner_nonneg_right (H.inverse v)
      _ = inner ℝ v (H.inverse v) := by
            rw [hInv.self_apply_inverse, real_inner_comm]
  have hsq :
      hessianDualNormVector F x hH v ^ (2 : ℕ) = inner ℝ v (H.inverse v) := by
    rw [hessianDualNormVector_def]
    simpa [H, pow_two, real_inner_comm] using Real.sq_sqrt hpair_nonneg
  have hpair_zero : inner ℝ v (H.inverse v) = 0 := by
    rw [hzero] at hsq
    simpa using hsq
  have hHv_zero : H (H.inverse v) = 0 :=
    positiveOperator_apply_eq_zero_of_inner_eq_zero hPos hpair_zero
  exact hInv.injective (by simpa [H] using hHv_zero)

/-- Helper for Theorem 5.3.11: the Chapter 5 stopping threshold is always nonnegative under the
short-step scalar assumptions. -/
private theorem barrierPathFollowingStoppingThreshold_nonneg
    (ν : NNReal) {β ε : ℝ} (epsilon_pos : 0 < ε) (beta_nonneg : 0 ≤ β) (beta_lt_half : β < 1 / 2) :
    0 ≤ barrierPathFollowingStoppingThreshold ν β ε := by
  rw [barrierPathFollowingStoppingThreshold_def]
  refine div_nonneg ?_ epsilon_pos.le
  have hbeta_lt_one : β < 1 := by
    linarith
  have hnum_nonneg :
      0 ≤ (ν : ℝ) + ((β + Real.sqrt (ν : ℝ)) * β) / (1 - β) := by
    have hfrac_nonneg :
        0 ≤ ((β + Real.sqrt (ν : ℝ)) * β) / (1 - β) := by
      refine div_nonneg ?_ (sub_pos.mpr hbeta_lt_one).le
      positivity
    positivity
  exact hnum_nonneg

/-- Helper for Theorem 5.3.11: the prescribed optimal value is `0` when the objective vector
vanishes identically. -/
private theorem optimalValue_eq_zero_of_zeroObjective
    {dom : Set E} {cStar : ℝ}
    (hcStar : IsBarrierPathFollowingOptimalValue (0 : E) dom cStar)
    (x : dom) :
    cStar = 0 := by
  have hupper : cStar ≤ 0 :=
    optimalObjectiveValue_le_of_mem_closure (c := (0 : E)) hcStar ⟨x, subset_closure x.2⟩
  have hlower : 0 ≤ cStar := by
    refine hcStar.2 ?_
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    simp
  linarith

/-- Helper for Theorem 5.3.11: if the reference dual norm at the analytic center is zero, then
the actual short-step scheme is forced into the degenerate branch `c = 0`, `tₖ = 0`, and
`stopIndex = 0`. -/
private theorem pathFollowing_terminationOutcome_of_zeroReferenceObjectiveNorm
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E)
    (cStar : ℝ)
    (hcStar : IsBarrierPathFollowingOptimalValue c dom cStar)
    (xStar : dom)
    (hxStarH : (fderiv ℝ (∇ F) (xStar : E)).det ≠ 0)
    {x0 : dom} {β γ ε : ℝ}
    (hshort : IsShortStepBarrierPathFollowingParameters β γ)
    (scheme : BarrierPathFollowingScheme c F ν x0 β γ ε)
    (href0 : barrierPathFollowingObjectiveNorm F c (xStar : E) hxStarH = 0) :
    pathFollowingTerminationOutcome
      c cStar ν β γ ε
      (barrierPathFollowingObjectiveNorm F c (xStar : E) hxStarH)
      scheme scheme.stopIndex := by
  have hc_zero : c = 0 := by
    apply eq_zero_of_hessianDualNormVector_eq_zero
      (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xStar.2) hxStarH
    simpa [barrierPathFollowingObjectiveNorm_def] using href0
  have ht_zero : ∀ k : ℕ, scheme.t k = 0 := by
    intro k
    induction k with
    | zero =>
        exact scheme.t_zero
    | succ k ih =>
        -- Route correction: once `c = 0`, the scalar update adds `γ / 0 = 0` at every step.
        have hobj_zero :
            barrierPathFollowingObjectiveNorm F c (scheme k) (scheme.hessian_nondegenerate k) = 0 := by
          subst hc_zero
          simp [barrierPathFollowingObjectiveNorm_def, hessianDualNormVector_def]
        rw [scheme.t_step, ih, hobj_zero]
        simp
  have hthreshold_nonneg :
      0 ≤ barrierPathFollowingStoppingThreshold ν β ε :=
    barrierPathFollowingStoppingThreshold_nonneg ν scheme.epsilon_pos
      hshort.beta_nonneg hshort.beta_lt_half
  have hthreshold_eq_zero : barrierPathFollowingStoppingThreshold ν β ε = 0 := by
    have hstop_nonpos : barrierPathFollowingStoppingThreshold ν β ε ≤ 0 := by
      simpa [ht_zero scheme.stopIndex] using scheme.stop_condition
    exact le_antisymm hstop_nonpos hthreshold_nonneg
  have hstopIndex_zero : scheme.stopIndex = 0 := by
    by_cases hN : scheme.stopIndex = 0
    · exact hN
    · have hcont0 : scheme.t 0 < barrierPathFollowingStoppingThreshold ν β ε :=
        scheme.continue_condition (k := 0) (Nat.pos_of_ne_zero hN)
      rw [scheme.t_zero, hthreshold_eq_zero] at hcont0
      linarith
  have hcStar_zero : cStar = 0 := by
    subst hc_zero
    exact optimalValue_eq_zero_of_zeroObjective (dom := dom) hcStar xStar
  constructor
  · -- Once the degenerate branch forces `stopIndex = 0`, the ceiling bound is automatic.
    simpa [hstopIndex_zero, href0] using (Nat.zero_le
      ⌈barrierPathFollowingTerminationBound ν β γ ε 0⌉₊)
  · -- The objective vector and optimal value both vanish in the degenerate branch.
    simpa [hstopIndex_zero, hc_zero, hcStar_zero] using scheme.epsilon_pos.le

/-- Helper for Theorem 5.3.11: the stopping iterate packages into a nonnegative penalty
parameter with an exact minimizer of the tilted objective once the terminal approximate-centering
estimate is available. -/
private theorem pathFollowing_stopObjective_hasMinimizer
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E)
    {β ε : ℝ}
    (t : ℕ → ℝ)
    (x : ℕ → E)
    (mem_domain : ∀ k : ℕ, x k ∈ dom)
    (hessian_nondegenerate : ∀ k : ℕ, (fderiv ℝ (∇ F) (x k)).det ≠ 0)
    (stopIndex : ℕ)
    (epsilon_pos : 0 < ε)
    (beta_nonneg : 0 ≤ β)
    (beta_lt_half : β < 1 / 2)
    (hstop : barrierPathFollowingStoppingThreshold ν β ε ≤ t stopIndex)
    (happrox_stop :
      HessianDualLocalNorm.ofDetNeZero F (x stopIndex)
          (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 (mem_domain stopIndex))
          (hessian_nondegenerate stopIndex)
          ((InnerProductSpace.toDual ℝ E)
            (t stopIndex • c + ∇ F (x stopIndex))) ≤
        β) :
    ∃ tStop : Set.Ici (0 : ℝ),
      (tStop : ℝ) = t stopIndex ∧
        ∃ xPath : dom, IsMinOn (centralPathPenaltyObjective c F tStop) dom (xPath : E) := by
  let xStop : dom := ⟨x stopIndex, mem_domain stopIndex⟩
  have htStop_nonneg : 0 ≤ t stopIndex := by
    exact le_trans
      (barrierPathFollowingStoppingThreshold_nonneg ν epsilon_pos beta_nonneg beta_lt_half)
      hstop
  let tStop : Set.Ici (0 : ℝ) := ⟨t stopIndex, htStop_nonneg⟩
  have hbeta_lt_one : β < 1 := by
    linarith
  have happrox_stop' :
      HessianDualLocalNorm.ofDetNeZero F (xStop : E)
          (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xStop.2)
          (hessian_nondegenerate stopIndex)
          ((InnerProductSpace.toDual ℝ E)
            ((tStop : ℝ) • c + ∇ F (xStop : E))) ≤
        β := by
    simpa [xStop, tStop] using happrox_stop
  rcases centralPathPenaltyObjective_hasMinimizer_of_approximateCenter
      (dom := dom) (ν := ν) (F := F) c tStop xStop
      (hessian_nondegenerate stopIndex) hbeta_lt_one happrox_stop' with
    ⟨xPath, hpath⟩
  -- Repackage the stopping parameter in the subtype expected by the objective-gap theorem.
  exact ⟨tStop, rfl, xPath, hpath⟩

-- Semantic recall note: a `lean_leansearch` query for the stopping theorem surfaced only generic
-- `Real.log` lemmas. The proof-oriented stopping witnesses are therefore isolated in the
-- `BarrierPathFollowingStopSpec` certificate used by the lower-level private helper theorem,
-- while the public theorem statements below stay on the source-facing analytic-center surface.
/-- Lower-level certificate-to-outcome bridge for Theorem 5.3.11: a packaged stopping
certificate for one Chapter 5 path-following scheme implies the explicit stopping-index and
objective-gap conclusion used in the proof layer. -/
private theorem pathFollowing_terminationOutcome_of_stopSpec
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E)
    (cStar : ℝ)
    (hcStar : IsBarrierPathFollowingOptimalValue c dom cStar)
    (xStar : dom)
    (hxStarH : (fderiv ℝ (∇ F) (xStar : E)).det ≠ 0)
    {x0 : dom} {β γ ε : ℝ}
    (scheme : BarrierPathFollowingScheme c F ν x0 β γ ε)
    (hspec : BarrierPathFollowingStopSpec c F ν xStar hxStarH β γ ε scheme) :
    pathFollowingTerminationOutcome
      c cStar ν β γ ε
      (barrierPathFollowingObjectiveNorm F c (xStar : E) hxStarH)
      scheme scheme.stopIndex :=
  by
  constructor
  · -- The certificate already packages the geometric lower bound needed by the scalar theorem.
    exact
      pathFollowing_stopIndex_le_natCeil_terminationBound
        c xStar hxStarH scheme.t scheme.stopIndex
        scheme.epsilon_pos hspec.beta_nonneg hspec.beta_lt_half hspec.gamma_pos
        hspec.referenceObjectiveNorm_pos
        scheme.continue_condition scheme.stop_condition hspec.hgrowth
  · -- Route correction: consume the GLB-based terminal-gap theorem rather than rebuilding the
    -- closure comparison inside this certificate wrapper.
    exact
      pathFollowing_objectiveGap_le_epsilon
        c cStar hcStar
        scheme.t scheme scheme.mem_domain scheme.hessian_nondegenerate scheme.stopIndex
        scheme.epsilon_pos hspec.beta_nonneg hspec.beta_lt_half
        hspec.tStop hspec.htStop hspec.htStop_pos hspec.xPath hspec.hpath
        scheme.stop_condition hspec.happrox_stop

/-- Theorem 5.3.11: for every positive target accuracy `ε`, the Chapter 5 short-step
path-following method `(5.3.29)` for a `ν`-self-concordant barrier terminates at its stopping
index with the explicit logarithmic ceiling bound recorded in
`pathFollowingTerminationOutcome`; moreover, the stopping iterate `x_N` already satisfies
`⟪c, x_N⟫ - c* ≤ ε`. The theorem is stated for a genuine Chapter 5 short-step orbit with the
calibrated parameter witness `IsShortStepBarrierPathFollowingParameters β γ`, and the reference
objective norm in the logarithmic bound is taken at the prescribed analytic center of the barrier
domain. -/
theorem pathFollowing_terminationOutcome
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E)
    (cStar : ℝ)
    (hcStar : IsBarrierPathFollowingOptimalValue c dom cStar)
    (xStar : dom)
    (hcenter : IsMinOn F dom (xStar : E))
    (hxStarH : (fderiv ℝ (∇ F) (xStar : E)).det ≠ 0)
    {x0 : dom} {β γ ε : ℝ}
    (hshort : IsShortStepBarrierPathFollowingParameters β γ)
    (scheme : BarrierPathFollowingScheme c F ν x0 β γ ε) :
    pathFollowingTerminationOutcome
      c cStar ν β γ ε
      (barrierPathFollowingObjectiveNorm F c (xStar : E) hxStarH)
      scheme scheme.stopIndex :=
  sorry

/-- Proof-oriented raw-form companion for the Chapter 5 path-following stopping theorem: under the
explicit method recursion, geometric-growth, and terminal approximate-centering estimates used in
the textbook proof, an analytic-center reference point and any prescribed optimizer in
`closure dom` yield the combined stopping-index and objective-gap estimate for the given Chapter 5
method orbit. -/
theorem pathFollowing_stopIndex_le_natCeil_terminationBound_and_objectiveGap_le_epsilon
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E)
    (xStar : dom)
    (hcenter : IsMinOn F dom (xStar : E))
    (hxStarH : (fderiv ℝ (∇ F) (xStar : E)).det ≠ 0)
    (xOpt : closure dom)
    (hopt : ∀ y : closure dom, inner ℝ c (xOpt : E) ≤ inner ℝ c (y : E))
    {β γ ε : ℝ}
    (t : ℕ → ℝ)
    (x : ℕ → E)
    (mem_domain : ∀ k : ℕ, x k ∈ dom)
    (hessian_nondegenerate : ∀ k : ℕ, (fderiv ℝ (∇ F) (x k)).det ≠ 0)
    (stopIndex : ℕ)
    (epsilon_pos : 0 < ε)
    (beta_nonneg : 0 ≤ β)
    (beta_lt_half : β < 1 / 2)
    (hγ_pos : 0 < γ)
    (ht_zero : t 0 = 0)
    (ht_step :
      ∀ k : ℕ,
        t (k + 1) =
          t k + γ / barrierPathFollowingObjectiveNorm F c (x k) (hessian_nondegenerate k))
    (hcontinue :
      ∀ ⦃k : ℕ⦄, k < stopIndex → t k < barrierPathFollowingStoppingThreshold ν β ε)
    (hstop : barrierPathFollowingStoppingThreshold ν β ε ≤ t stopIndex)
    (hgrowth :
      ∀ k : ℕ, 1 ≤ k →
        (γ * (1 - 2 * β)) /
            ((1 - β) *
                HessianDualLocalNorm.ofDetNeZero F (xStar : E)
                  (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xStar.2)
                hxStarH
                ((InnerProductSpace.toDual ℝ E) c)) *
            (1 + γ / (β + Real.sqrt (ν : ℝ))) ^ (k - 1) ≤
          t k)
    (happrox_stop :
      HessianDualLocalNorm.ofDetNeZero F (x stopIndex)
          (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1
            (mem_domain stopIndex))
          (hessian_nondegenerate stopIndex)
          ((InnerProductSpace.toDual ℝ E)
            (t stopIndex • c + ∇ F (x stopIndex))) ≤
        β) :
    stopIndex ≤
      ⌈barrierPathFollowingTerminationBound ν β γ ε
        (HessianDualLocalNorm.ofDetNeZero F (xStar : E)
          (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xStar.2) hxStarH
          ((InnerProductSpace.toDual ℝ E) c))⌉₊ ∧
      inner ℝ c (x stopIndex) - inner ℝ c (xOpt : E) ≤ ε :=
  sorry

/-- The stopping-index half of the Chapter 5 path-following stopping theorem, extracted as a named
companion lemma for the explicit Chapter 5 logarithmic stopping-index estimate under the
short-step growth hypotheses. -/
theorem pathFollowing_stopIndex_le_natCeil_terminationBound
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E)
    (xStar : dom)
    (hxStarH : (fderiv ℝ (∇ F) (xStar : E)).det ≠ 0)
    {β γ ε : ℝ}
    (t : ℕ → ℝ)
    (stopIndex : ℕ)
    (epsilon_pos : 0 < ε)
    (beta_nonneg : 0 ≤ β)
    (beta_lt_half : β < 1 / 2)
    (hγ_pos : 0 < γ)
    (referenceObjectiveNorm_pos :
      0 <
        HessianDualLocalNorm.ofDetNeZero F (xStar : E)
          (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xStar.2)
          hxStarH
          ((InnerProductSpace.toDual ℝ E) c))
    (hcontinue :
      ∀ ⦃k : ℕ⦄, k < stopIndex → t k < barrierPathFollowingStoppingThreshold ν β ε)
    (hstop : barrierPathFollowingStoppingThreshold ν β ε ≤ t stopIndex)
    (hgrowth :
      ∀ k : ℕ, 1 ≤ k →
        (γ * (1 - 2 * β)) /
            ((1 - β) *
                HessianDualLocalNorm.ofDetNeZero F (xStar : E)
                  (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xStar.2)
                  hxStarH
                  ((InnerProductSpace.toDual ℝ E) c)) *
            (1 + γ / (β + Real.sqrt (ν : ℝ))) ^ (k - 1) ≤
          t k) :
    stopIndex ≤
      ⌈barrierPathFollowingTerminationBound ν β γ ε
        (HessianDualLocalNorm.ofDetNeZero F (xStar : E)
          (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xStar.2) hxStarH
          ((InnerProductSpace.toDual ℝ E) c))⌉₊ :=
  by
  let referenceObjectiveNorm :=
    HessianDualLocalNorm.ofDetNeZero F (xStar : E)
      (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xStar.2) hxStarH
      ((InnerProductSpace.toDual ℝ E) c)
  let threshold := barrierPathFollowingStoppingThreshold ν β ε
  let growthBase := 1 + γ / (β + Real.sqrt (ν : ℝ))
  let growthHead := (γ * (1 - 2 * β)) / ((1 - β) * referenceObjectiveNorm)
  let logRatio := (threshold * (1 - β) * referenceObjectiveNorm) / (γ * (1 - 2 * β))
  have hbeta_lt_one : β < 1 := by
    linarith
  have hOne_le_bound :
      (1 : ℝ) ≤ barrierPathFollowingTerminationBound ν β γ ε referenceObjectiveNorm := by
    rw [barrierPathFollowingTerminationBound_def]
    exact le_max_left _ _
  have hbound_pos : 0 < barrierPathFollowingTerminationBound ν β γ ε referenceObjectiveNorm := by
    linarith
  by_cases hstop_zero : stopIndex = 0
  · simpa [hstop_zero]
  by_cases hstop_one : stopIndex = 1
  · -- If the method stops at the first positive index, the clipped bound is automatic.
    simpa [hstop_one] using (Nat.one_le_ceil_iff.2 hbound_pos)
  have hstop_gt_one : 1 < stopIndex := by
    omega
  let k : ℕ := stopIndex - 1
  have hk_pos : 1 ≤ k := by
    dsimp [k]
    omega
  have hk_lt : k < stopIndex := by
    dsimp [k]
    omega
  have hsuc : k + 1 = stopIndex := by
    dsimp [k]
    omega
  have hcontinuek : t k < threshold := by
    simpa [threshold] using hcontinue hk_lt
  have hgrowthk : growthHead * growthBase ^ (k - 1) ≤ t k := by
    simpa [growthHead, growthBase, referenceObjectiveNorm] using hgrowth k hk_pos
  have hcore :
      growthHead * growthBase ^ (k - 1) < threshold := by
    exact lt_of_le_of_lt hgrowthk hcontinuek
  have hone_sub_beta_pos : 0 < 1 - β := by
    linarith
  have hone_sub_two_beta_pos : 0 < 1 - 2 * β := by
    linarith
  have hgrowthHead_pos : 0 < growthHead := by
    dsimp [growthHead]
    exact div_pos (mul_pos hγ_pos hone_sub_two_beta_pos)
      (mul_pos hone_sub_beta_pos referenceObjectiveNorm_pos)
  have hthreshold_pos : 0 < threshold := by
    exact lt_of_lt_of_le (by
      have hpow_pos : 0 < growthBase ^ (k - 1) := by positivity
      exact mul_pos hgrowthHead_pos hpow_pos) hcore.le
  have hnumerator_pos :
      0 < (ν : ℝ) + ((β + Real.sqrt (ν : ℝ)) * β) / (1 - β) := by
    have := (div_pos_iff₀ epsilon_pos).1 (by
      simpa [threshold, barrierPathFollowingStoppingThreshold_def] using hthreshold_pos)
    simpa using this
  have hdenom_pos : 0 < β + Real.sqrt (ν : ℝ) := by
    by_contra hdenom_pos
    have hdenom_nonpos : β + Real.sqrt (ν : ℝ) ≤ 0 := le_of_not_gt hdenom_pos
    have hdenom_nonneg : 0 ≤ β + Real.sqrt (ν : ℝ) := by positivity
    have hdenom_zero : β + Real.sqrt (ν : ℝ) = 0 := le_antisymm hdenom_nonpos hdenom_nonneg
    have hsqrt_zero : Real.sqrt (ν : ℝ) = 0 := by
      nlinarith [beta_nonneg, Real.sqrt_nonneg (ν : ℝ), hdenom_zero]
    have hnu_zero : (ν : ℝ) = 0 := by
      have hnu_nonneg : 0 ≤ (ν : ℝ) := by exact_mod_cast ν.2
      nlinarith [Real.sq_sqrt hnu_nonneg, hsqrt_zero]
    have hbeta_zero : β = 0 := by
      nlinarith [hdenom_zero, hsqrt_zero]
    rw [hnu_zero, hbeta_zero, hsqrt_zero] at hnumerator_pos
    norm_num at hnumerator_pos
  have hgrowthBase_gt_one : 1 < growthBase := by
    dsimp [growthBase]
    have hfrac_pos : 0 < γ / (β + Real.sqrt (ν : ℝ)) := by
      exact div_pos hγ_pos hdenom_pos
    linarith
  have hgrowthBase_pos : 0 < growthBase := by
    linarith
  have hlogBase_pos : 0 < Real.log growthBase := by
    exact Real.log_pos hgrowthBase_gt_one
  have hlogRatio_eq : threshold / growthHead = logRatio := by
    dsimp [growthHead, logRatio]
    field_simp [referenceObjectiveNorm_pos.ne', hγ_pos.ne', hone_sub_beta_pos.ne',
      hbeta_lt_one.ne, hbeta_lt_one.ne', hone_sub_two_beta_pos.ne']
    ring
  have hpow_lt :
      growthBase ^ (k - 1) < logRatio := by
    have hdiv_lt : growthBase ^ (k - 1) < threshold / growthHead := by
      exact (lt_div_iff₀ hgrowthHead_pos).2 hcore
    simpa [hlogRatio_eq] using hdiv_lt
  have hlogRatio_pos : 0 < logRatio := by
    exact lt_of_lt_of_le (by
      have hpow_pos : 0 < growthBase ^ (k - 1) := by positivity
      exact hpow_pos) hpow_lt.le
  have hlog_lt :
      Real.log (growthBase ^ (k - 1 : ℕ)) < Real.log logRatio := by
    exact Real.log_lt_log (by positivity) hlogRatio_pos hpow_lt
  have hk_sub :
      ((k - 1 : ℕ) : ℝ) * Real.log growthBase < Real.log logRatio := by
    simpa [Real.rpow_natCast, Real.log_rpow hgrowthBase_pos] using hlog_lt
  have hk_sub_div :
      ((k - 1 : ℕ) : ℝ) < Real.log logRatio / Real.log growthBase := by
    exact (lt_div_iff₀ hlogBase_pos).2 hk_sub
  have hk_pred : (k - 1) + 1 = k := by
    omega
  have hkReal :
      (k : ℝ) <
        1 + Real.log logRatio / Real.log growthBase := by
    have hk_cast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
      exact_mod_cast hk_pred
    linarith
  have hceil :
      k + 1 ≤
        ⌈1 + Real.log logRatio / Real.log growthBase⌉₊ := by
    exact Nat.add_one_le_ceil_iff.2 hkReal
  have hbound_mono :
      1 + Real.log logRatio / Real.log growthBase ≤
        barrierPathFollowingTerminationBound ν β γ ε referenceObjectiveNorm := by
    rw [barrierPathFollowingTerminationBound_def]
    exact le_max_right _ _
  have hceil_bound :
      stopIndex ≤
        ⌈barrierPathFollowingTerminationBound ν β γ ε referenceObjectiveNorm⌉₊ := by
    refine le_trans ?_ (Nat.ceil_mono hbound_mono)
    simpa [hsuc, logRatio, growthBase, threshold, referenceObjectiveNorm] using hceil
  simpa [referenceObjectiveNorm] using hceil_bound

/-- Helper for Theorem 5.3.11: any closure comparison point gives the same `ε`-accuracy estimate
once the stopping threshold, the exact penalty minimizer at the stopping parameter, and the
terminal approximate-centering hypotheses are available. -/
theorem pathFollowing_objectiveGap_le_epsilon_of_closurePoint
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E)
    (xOpt : closure dom)
    {β ε : ℝ}
    (t : ℕ → ℝ)
    (x : ℕ → E)
    (mem_domain : ∀ k : ℕ, x k ∈ dom)
    (hessian_nondegenerate : ∀ k : ℕ, (fderiv ℝ (∇ F) (x k)).det ≠ 0)
    (stopIndex : ℕ)
    (epsilon_pos : 0 < ε)
    (beta_nonneg : 0 ≤ β)
    (beta_lt_half : β < 1 / 2)
    (tStop : Set.Ici (0 : ℝ))
    (htStop : (tStop : ℝ) = t stopIndex)
    (htStop_pos : 0 < (tStop : ℝ))
    (xPath : dom)
    (hpath : IsMinOn (centralPathPenaltyObjective c F tStop) dom (xPath : E))
    (hstop : barrierPathFollowingStoppingThreshold ν β ε ≤ t stopIndex)
    (happrox_stop :
      HessianDualLocalNorm.ofDetNeZero F (x stopIndex)
          (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 (mem_domain stopIndex))
          (hessian_nondegenerate stopIndex)
          ((InnerProductSpace.toDual ℝ E)
            (t stopIndex • c + ∇ F (x stopIndex))) ≤
        β) :
    inner ℝ c (x stopIndex) - inner ℝ c (xOpt : E) ≤ ε :=
  by
  let xStop : dom := ⟨x stopIndex, mem_domain stopIndex⟩
  have hbeta_lt_one : β < 1 := by
    linarith
  have happrox_stop' :
      HessianDualLocalNorm.ofDetNeZero F (xStop : E)
          (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xStop.2)
          (hessian_nondegenerate stopIndex)
          ((InnerProductSpace.toDual ℝ E)
            ((tStop : ℝ) • c + ∇ F (xStop : E))) ≤
        β := by
    simpa [xStop, htStop] using happrox_stop
  -- Route correction: use the closure-point companion of Theorem 5.3.10 instead of the earlier
  -- over-strong optimizer-witness interface.
  have hgap :
      inner ℝ c (x stopIndex) - inner ℝ c (xOpt : E) ≤
        ((ν : ℝ) + ((β + Real.sqrt (ν : ℝ)) * β) / (1 - β)) / (tStop : ℝ) := by
    simpa [xStop] using
      (centralPathApproximateCenter_objectiveGap_le_barrierParameter_add_error_div_of_mem_closure
        (dom := dom) (ν := ν) (F := F) c tStop (β := β)
        htStop_pos hbeta_lt_one xOpt
        (xPath := xPath) (x := xStop) hpath
        (hessian_nondegenerate stopIndex) happrox_stop')
  have hthreshold_le :
      ((ν : ℝ) + ((β + Real.sqrt (ν : ℝ)) * β) / (1 - β)) / ε ≤ (tStop : ℝ) := by
    simpa [barrierPathFollowingStoppingThreshold_def, htStop] using hstop
  have hscaled :
      ((ν : ℝ) + ((β + Real.sqrt (ν : ℝ)) * β) / (1 - β)) ≤ (tStop : ℝ) * ε := by
    exact (div_le_iff epsilon_pos).1 hthreshold_le
  have hbound :
      ((ν : ℝ) + ((β + Real.sqrt (ν : ℝ)) * β) / (1 - β)) / (tStop : ℝ) ≤ ε := by
    exact (div_le_iff htStop_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)
  -- The stopping threshold converts the Chapter 5.3.10 bound into the target `ε`-estimate.
  exact le_trans hgap hbound

/-- Auxiliary witness-based objective-gap estimate for the Chapter 5 path-following stopping
theorem: if `xOpt` attains the optimal value over `closure dom`, then the terminal iterate has
objective gap at most `ε` relative to that optimizer once an exact penalty minimizer at the
stopping parameter is supplied. This is the proof-oriented bridge to the source-facing
optimal-value formulation. -/
theorem pathFollowing_objectiveGap_le_epsilon_of_optimalPoint
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E)
    (xOpt : closure dom)
    (hopt : ∀ y : closure dom, inner ℝ c (xOpt : E) ≤ inner ℝ c (y : E))
    {β ε : ℝ}
    (t : ℕ → ℝ)
    (x : ℕ → E)
    (mem_domain : ∀ k : ℕ, x k ∈ dom)
    (hessian_nondegenerate : ∀ k : ℕ, (fderiv ℝ (∇ F) (x k)).det ≠ 0)
    (stopIndex : ℕ)
    (epsilon_pos : 0 < ε)
    (beta_nonneg : 0 ≤ β)
    (beta_lt_half : β < 1 / 2)
    (tStop : Set.Ici (0 : ℝ))
    (htStop : (tStop : ℝ) = t stopIndex)
    (htStop_pos : 0 < (tStop : ℝ))
    (xPath : dom)
    (hpath : IsMinOn (centralPathPenaltyObjective c F tStop) dom (xPath : E))
    (hstop : barrierPathFollowingStoppingThreshold ν β ε ≤ t stopIndex)
    (happrox_stop :
      HessianDualLocalNorm.ofDetNeZero F (x stopIndex)
          (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 (mem_domain stopIndex))
          (hessian_nondegenerate stopIndex)
          ((InnerProductSpace.toDual ℝ E)
            (t stopIndex • c + ∇ F (x stopIndex))) ≤
        β) :
    inner ℝ c (x stopIndex) - inner ℝ c (xOpt : E) ≤ ε :=
  let _ := hopt
  pathFollowing_objectiveGap_le_epsilon_of_closurePoint
    c xOpt
    t x mem_domain hessian_nondegenerate stopIndex
    epsilon_pos beta_nonneg beta_lt_half
    tStop htStop htStop_pos xPath hpath hstop happrox_stop

/-- The terminal objective-gap half of the Chapter 5 path-following stopping theorem, extracted as
a named companion lemma for the threshold-crossing iterate once the terminal approximate-centering
bound is available, stated against the optimal value `c*` over `closure dom`, and requiring the
same exact stopping-parameter minimizer used in the proof-oriented companion above. -/
theorem pathFollowing_objectiveGap_le_epsilon
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E)
    (cStar : ℝ)
    (hcStar : IsBarrierPathFollowingOptimalValue c dom cStar)
    {β ε : ℝ}
    (t : ℕ → ℝ)
    (x : ℕ → E)
    (mem_domain : ∀ k : ℕ, x k ∈ dom)
    (hessian_nondegenerate : ∀ k : ℕ, (fderiv ℝ (∇ F) (x k)).det ≠ 0)
    (stopIndex : ℕ)
    (epsilon_pos : 0 < ε)
    (beta_nonneg : 0 ≤ β)
    (beta_lt_half : β < 1 / 2)
    (tStop : Set.Ici (0 : ℝ))
    (htStop : (tStop : ℝ) = t stopIndex)
    (htStop_pos : 0 < (tStop : ℝ))
    (xPath : dom)
    (hpath : IsMinOn (centralPathPenaltyObjective c F tStop) dom (xPath : E))
    (hstop : barrierPathFollowingStoppingThreshold ν β ε ≤ t stopIndex)
    (happrox_stop :
      HessianDualLocalNorm.ofDetNeZero F (x stopIndex)
          (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 (mem_domain stopIndex))
          (hessian_nondegenerate stopIndex)
          ((InnerProductSpace.toDual ℝ E)
            (t stopIndex • c + ∇ F (x stopIndex))) ≤
        β) :
    inner ℝ c (x stopIndex) - cStar ≤ ε :=
  by
  have hlower :
      ∀ z : closure dom, inner ℝ c (x stopIndex) - ε ≤ inner ℝ c (z : E) := by
    intro z
    -- Every closure comparison point satisfies the same `ε`-estimate, so `⟪c, x_N⟫ - ε` is a
    -- lower bound for the whole closure objective image.
    have hz :
        inner ℝ c (x stopIndex) - inner ℝ c (z : E) ≤ ε :=
      pathFollowing_objectiveGap_le_epsilon_of_closurePoint
        (dom := dom) (ν := ν) (F := F)
        c z t x mem_domain hessian_nondegenerate stopIndex
        epsilon_pos beta_nonneg beta_lt_half
        tStop htStop htStop_pos xPath hpath hstop happrox_stop
    linarith
  have hlower_set :
      ∀ y ∈ ((fun z : E ↦ inner ℝ c z) '' closure dom),
        inner ℝ c (x stopIndex) - ε ≤ y := by
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    exact hlower ⟨z, hz⟩
  have hglb :
      inner ℝ c (x stopIndex) - ε ≤ cStar :=
    hcStar.2 hlower_set
  linarith

end

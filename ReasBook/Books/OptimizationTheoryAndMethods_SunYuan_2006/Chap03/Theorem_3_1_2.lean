/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.DerivativeTest
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_7
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_2_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Definition_3_1_extra_1

open Filter

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Domain sampling pass:
-- Primary domain: smooth unconstrained optimization with exact line search on the
-- steepest-descent ray.
-- Sampled owner declarations:
-- * `IsStationaryPoint` in Chapter01 Definition 1.4.7;
-- * `IsExactLineSearchStepOnNonnegativeRay` in Chapter02 Definition 2.2-extra-1;
-- * `steepestDescentDirection`, `steepestDescentObjective`, and `steepestDescentStep` in
--   Chapter03 Definition 3.1-extra-1.
-- Owner abstraction:
-- * source-facing: a steepest-descent iterate sequence together with an accumulation point of a
--   subsequence;
-- * core/canonical: `IsSteepestDescentSequence`, `steepestDescentObjective`, and
--   `IsStationaryPoint`;
-- * bridge/view: `IsSteepestDescentSequence.exactLineSearch` and
--   `IsSteepestDescentSequence.update` recover the Chapter 2 line-search owner and the Chapter 3
--   update equation on the canonical steepest-descent ray, while the raw formulas
--   `x - α • gradient f x` and `gradient f xStar = 0` remain derived API.
-- Primitive data are therefore the Chapter 3 sequence owner plus the convergent subsequence; the
-- old separate exact-line-search and update hypotheses were duplicate views of that owner.

/-- Helper for Chapter03 Theorem 3.1.2: every exact-line-search steepest-descent step does not
increase the objective value. -/
lemma steepestDescent_value_nonincreasing
    (f : E → ℝ)
    (x : ℕ → E)
    (α : ℕ → ℝ)
    (hSeq : IsSteepestDescentSequence f x α)
    (k : ℕ) :
    f (x (k + 1)) ≤ f (x k) := by
  -- Exact line search compares the chosen step with the zero step on the same search ray.
  have hMin :=
    lineSearchObjective_le_zero_of_isExactLineSearchStepOnNonnegativeRay (hSeq.exactLineSearch k)
  rw [lineSearchObjective_zero] at hMin
  rw [lineSearchObjective_apply] at hMin
  have hStep : f (steepestDescentStep f (x k) (α k)) ≤ f (x k) := by
    simpa [steepestDescentStep] using hMin
  simpa [hSeq.update k] using hStep

/-- Helper for Chapter03 Theorem 3.1.2: the objective values along a steepest-descent sequence
form an antitone sequence. -/
lemma steepestDescent_value_antitone
    (f : E → ℝ)
    (x : ℕ → E)
    (α : ℕ → ℝ)
    (hSeq : IsSteepestDescentSequence f x α) :
    Antitone (fun k : ℕ ↦ f (x k)) := by
  -- Iterating the one-step decrease gives monotonicity along the whole run.
  exact antitone_nat_of_succ_le
    (fun k ↦ steepestDescent_value_nonincreasing f x α hSeq k)

/-- Helper for Chapter03 Theorem 3.1.2: for a fixed trial step `τ`, the corresponding steepest
descent objective gap depends continuously on the base point. -/
lemma continuous_steepestDescent_trial_gap
    (f : E → ℝ)
    (hC1 : ContDiff ℝ 1 f)
    (τ : ℝ) :
    Continuous (fun y : E ↦ f (steepestDescentStep f y τ) - f y) := by
  -- Route correction: the key interface bridge is continuity of `gradient`, obtained from the
  -- continuous Fréchet derivative field and the Riesz isomorphism.
  have hGradAux : Continuous (fun y : E ↦ (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f y)) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hC1.continuous_fderiv one_ne_zero)
  have hGrad : Continuous (gradient f) := by
    change Continuous (fun y : E ↦ (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f y))
    exact hGradAux
  have hStep : Continuous (fun y : E ↦ steepestDescentStep f y τ) := by
    -- Rewriting the step as `y + τ • (-∇f y)` exposes only continuous operations.
    have hStepAux : Continuous (fun y : E ↦ y + τ • (-gradient f y)) :=
      continuous_id.add ((hGrad.neg).const_smul τ)
    simpa [steepestDescentStep, steepestDescentDirection] using hStepAux
  -- The trial-step gap is the difference between two continuous objective evaluations.
  exact (hC1.continuous.comp hStep).sub hC1.continuous

/-- Helper for Chapter03 Theorem 3.1.2: if the gradient at `xStar` is nonzero, then one fixed
positive steepest-descent trial step yields a uniform objective decrease near `xStar`. -/
lemma eventually_trial_step_decrease_of_gradient_ne_zero
    (f : E → ℝ)
    (hC1 : ContDiff ℝ 1 f)
    {xStar : E}
    (hGradNe : gradient f xStar ≠ 0) :
    ∃ τ > 0, ∃ η > 0, ∀ᶠ y in nhds xStar, f (steepestDescentStep f y τ) ≤ f y - η := by
  -- A nonzero gradient makes the steepest-descent direction a genuine descent direction.
  have hDescent :
      IsDescentDirectionAt f xStar (steepestDescentDirection f xStar) :=
    steepestDescentDirection_isDescentDirection f xStar hGradNe
  obtain ⟨δ, hδpos, hLocalDecrease⟩ := hDescent.exists_localDecrease_lineSearchObjective
  let τ : ℝ := δ / 2
  have hτpos : 0 < τ := by
    dsimp [τ]
    linarith
  have hτlt : τ < δ := by
    dsimp [τ]
    linarith
  have hDecreaseAt :
      f (steepestDescentStep f xStar τ) < f xStar := by
    -- Choosing a small positive step on the steepest-descent ray strictly lowers `f` at `xStar`.
    simpa [lineSearchObjective_apply, lineSearchObjective_zero, steepestDescentStep] using
      hLocalDecrease τ hτpos hτlt
  let g : E → ℝ := fun y ↦ f (steepestDescentStep f y τ) - f y
  have hgCont : Continuous g := by
    simpa [g] using continuous_steepestDescent_trial_gap f hC1 τ
  have hgNeg : g xStar < 0 := by
    -- The chosen trial step has strictly negative objective gap at the limit point.
    dsimp [g]
    linarith
  let η : ℝ := -g xStar / 2
  have hηpos : 0 < η := by
    dsimp [η]
    linarith
  have hGapEventually : ∀ᶠ y in nhds xStar, g y < -η := by
    -- Continuity preserves a strict negative margin on a neighborhood of `xStar`.
    have hConst : ContinuousAt (fun _ : E ↦ (-η : ℝ)) xStar := continuous_const.continuousAt
    have hPoint : g xStar < (-η : ℝ) := by
      dsimp [η]
      linarith
    exact hgCont.continuousAt.eventually_lt hConst hPoint
  refine ⟨τ, hτpos, η, hηpos, ?_⟩
  refine hGapEventually.mono ?_
  intro y hy
  -- Re-expressing the strict gap gives the claimed uniform decrease inequality.
  dsimp [g] at hy ⊢
  linarith

/-- Chapter03 Theorem 3.1.2 (Global convergence theorem of the steepest descent method): if
`f : E → ℝ` on a real Hilbert space `E` is `C¹`, the iterates form a Chapter 3
`IsSteepestDescentSequence`, and a subsequence `x ∘ φ` converges to `xStar`, then `xStar` is a
stationary point of `f`. -/
theorem exactLineSearchSteepestDescent_accumulationPoint_stationary
    (f : E → ℝ)
    (x : ℕ → E)
    (α : ℕ → ℝ)
    (hC1 : ContDiff ℝ 1 f)
    (hSeq : IsSteepestDescentSequence f x α)
    {xStar : E}
    {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hTendsto : Tendsto (x ∘ φ) atTop (nhds xStar)) :
    IsStationaryPoint f xStar := by
  rw [isStationaryPoint_iff]
  refine ⟨?_, ?_⟩
  · -- A nonstationary accumulation point would force a fixed objective decrease along the
    -- convergent subsequence, contradicting convergence of the objective values.
    by_contra hGradNe
    obtain ⟨τ, hτpos, η, hηpos, hTrialDecrease⟩ :=
      eventually_trial_step_decrease_of_gradient_ne_zero f hC1 hGradNe
    have hAntitone : Antitone (fun k : ℕ ↦ f (x k)) :=
      steepestDescent_value_antitone f x α hSeq
    have hAlongSubseq :
        ∀ᶠ k in atTop, f (steepestDescentStep f (x (φ k)) τ) ≤ f (x (φ k)) - η := by
      -- The neighborhood decrease transfers to the convergent subsequence.
      simpa [Function.comp_def] using hTendsto.eventually hTrialDecrease
    have hSubseqDecrease :
        ∀ᶠ k in atTop, f (x (φ (k + 1))) ≤ f (x (φ k)) - η := by
      refine hAlongSubseq.mono ?_
      intro k hk
      have hExactChoice :
          f (x (φ k + 1)) ≤ f (steepestDescentStep f (x (φ k)) τ) := by
        -- Exact line search does no worse than the fixed admissible trial step `τ`.
        have hOpt := (hSeq.exactLineSearch (φ k)).optimal (α := τ) (le_of_lt hτpos)
        rw [lineSearchObjective_apply, lineSearchObjective_apply] at hOpt
        have hStepChoice :
            f (steepestDescentStep f (x (φ k)) (α (φ k))) ≤
              f (steepestDescentStep f (x (φ k)) τ) := by
          simpa [steepestDescentStep] using hOpt
        simpa [hSeq.update (φ k)] using hStepChoice
      have hFuture :
          f (x (φ (k + 1))) ≤ f (x (φ k + 1)) := by
        -- The whole objective sequence is nonincreasing, so later subsequence terms are no larger.
        exact hAntitone (Nat.succ_le_of_lt (hφ (Nat.lt_succ_self k)))
      exact hFuture.trans (hExactChoice.trans hk)
    have hValueTendsto :
        Tendsto (fun k ↦ f (x (φ k))) atTop (nhds (f xStar)) := by
      -- Continuity of `f` sends the convergent subsequence to convergent objective values.
      exact hC1.continuous.continuousAt.tendsto.comp hTendsto
    have hValueTendstoTail :
        Tendsto (fun k ↦ f (x (φ (k + 1)))) atTop (nhds (f xStar)) := by
      -- Shifting the subsequence by one index preserves the same limit.
      exact (tendsto_add_atTop_iff_nat 1).2 hValueTendsto
    have hRightTendsto :
        Tendsto (fun k ↦ f (x (φ k)) - η) atTop (nhds (f xStar - η)) := by
      -- Subtracting the fixed positive margin shifts the limiting objective value by `η`.
      exact hValueTendsto.sub tendsto_const_nhds
    have hStrictEventually :
        ∀ᶠ k in atTop, f (x (φ k)) - η < f (x (φ (k + 1))) := by
      -- The shifted right-hand side converges strictly below the unshifted left-hand side.
      have hSep : f xStar - η < f xStar := by
        linarith
      exact hRightTendsto.eventually_lt hValueTendstoTail hSep
    have hContradiction : ∀ᶠ k in (atTop : Filter ℕ), False := by
      filter_upwards [hStrictEventually, hSubseqDecrease] with k hkStrict hkLe
      exact not_lt_of_ge hkLe hkStrict
    rcases hContradiction.exists_forall_of_atTop with ⟨k0, hk0⟩
    exact hk0 k0 le_rfl
  · -- `C¹` regularity gives differentiability at the accumulation point.
    exact hC1.contDiffAt.differentiableAt_one

end

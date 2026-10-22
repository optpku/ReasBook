/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_66
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_67
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_68
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_75

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

local notation "TimeFiltration" => Filtration NNReal mΩ

variable {ℱ : TimeFiltration}

namespace IsContinuousLocalMartingaleUpTo

/-- Helper for Corollary 21.74: every term of an almost surely increasing stopping-time
approximation stays below the limiting stop almost surely. -/
private lemma aeLe_ofStoppingTimeApproximationUpTo
    {τSeq : ℕ → Ω → ENNReal} {τ : Ω → ENNReal}
    (hApprox : IsStoppingTimeApproximationUpTo ℱ μ τSeq τ) :
    ∀ n : ℕ, ∀ᵐ ω ∂μ, τSeq n ω ≤ τ ω := by
  intro n
  rcases hApprox with ⟨_, _, hlim⟩
  filter_upwards [hlim] with ω hω
  -- Proof comment: a monotone ENNReal sequence cannot converge to a limit below one of its
  -- earlier terms.
  exact Monotone.ge_of_tendsto hω.1 hω.2 n

/-- Helper for Corollary 21.74: the release-after-`τ` localizer at deterministic horizon `T`
is still a stopping time. -/
private lemma releaseAfterConst_isStoppingTime
    {τ : Ω → ENNReal} {T : NNReal}
    (hτ : IsStoppingTime ℱ τ) :
    IsStoppingTime ℱ (fun ω ↦ if τ ω ≤ (T : ENNReal) then ∞ else (T : ENNReal)) := by
  intro t
  by_cases hTt : T ≤ t
  · have hEvent : MeasurableSet[ℱ t] {ω | τ ω ≤ (T : ENNReal)} :=
      ℱ.mono hTt _ (hτ.measurableSet_le T)
    have hEq :
        {ω | (if τ ω ≤ (T : ENNReal) then ∞ else (T : ENNReal)) ≤ (t : ENNReal)} =
          {ω | τ ω ≤ (T : ENNReal)}ᶜ := by
      ext ω
      by_cases hω : τ ω ≤ (T : ENNReal)
      · simp [hω]
      · simp [hω, hTt]
    -- Proof comment: once `t` dominates `T`, the localizer is at most `t` exactly when the
    -- release branch did not fire.
    exact hEq.symm ▸ hEvent.compl
  · have hEq :
      {ω | (if τ ω ≤ (T : ENNReal) then ∞ else (T : ENNReal)) ≤ (t : ENNReal)} = ∅ := by
      ext ω
      by_cases hω : τ ω ≤ (T : ENNReal)
      · simp [hω]
      · simp [hω, hTt]
    -- Proof comment: before time `T`, neither branch can fall below `t`.
    exact hEq.symm ▸ MeasurableSet.empty

/-- Helper for Corollary 21.74: the deterministic release-after-`τ` sequence is pointwise
monotone and tends to `∞`. -/
private lemma releaseAfterConst_monotone_tendsto_top
    {τ : Ω → ENNReal} :
    ∀ᵐ ω ∂μ,
      Monotone (fun n : ℕ ↦ if τ ω ≤ (n : ENNReal) then (∞ : ENNReal) else (n : ENNReal)) ∧
        Tendsto
          (fun n : ℕ ↦ if τ ω ≤ (n : ENNReal) then (∞ : ENNReal) else (n : ENNReal))
          atTop
          (𝓝 (∞ : ENNReal)) := by
  refine Filter.Eventually.of_forall ?_
  intro ω
  constructor
  · intro a b hab
    by_cases ha : τ ω ≤ (a : ENNReal)
    · have hb : τ ω ≤ (b : ENNReal) := le_trans ha (by exact_mod_cast hab)
      simp [ha, hb]
    · by_cases hb : τ ω ≤ (b : ENNReal)
      · simp [ha, hb]
      · simp [ha, hb]
        exact_mod_cast hab
  · by_cases hfin : τ ω < ∞
    · let t : NNReal := (τ ω).toNNReal
      have hτ_eq : τ ω = (t : ENNReal) := by
        simp [t, ENNReal.coe_toNNReal, hfin.ne]
      have hEventually :
          ∀ᶠ n : ℕ in atTop,
            (if τ ω ≤ (n : ENNReal) then (∞ : ENNReal) else (n : ENNReal)) = ∞ := by
        refine Filter.eventually_atTop.2 ?_
        refine ⟨Nat.ceil (t : ℝ), ?_⟩
        intro n hn
        have htn_real : (t : ℝ) ≤ n := le_trans (Nat.le_ceil (t : ℝ)) (by exact_mod_cast hn)
        have htn : (t : ENNReal) ≤ (n : ENNReal) := by
          exact_mod_cast htn_real
        have hτn : τ ω ≤ (n : ENNReal) := by
          simpa [hτ_eq] using htn
        simp [hτn]
      -- Proof comment: once the deterministic horizon exceeds the finite stop `τ(ω)`, the
      -- release branch stays at `∞` forever.
      exact Tendsto.congr' (hEventually.mono fun _ hn ↦ hn.symm) tendsto_const_nhds
    · have hτ_eq : τ ω = ∞ := by
        simpa [lt_top_iff_ne_top] using hfin
      -- Proof comment: if `τ(ω) = ∞`, the release branch never fires and we are left with the
      -- deterministic sequence `n`.
      simpa [hτ_eq] using ENNReal.tendsto_nat_nhds_top

/-- Helper for Corollary 21.74: releasing the deterministic horizon after the terminal stop `τ`
turns the doubly stopped process back into the bounded-horizon stop `τ ∧ T`. -/
private lemma stoppedProcess_stoppedProcess_releaseAfterConst
    {X : NNReal → Ω → ℝ} {τ : Ω → ENNReal} (T : NNReal) :
    stoppedProcess (stoppedProcess X τ)
        (fun ω ↦ if τ ω ≤ (T : ENNReal) then ∞ else (T : ENNReal)) =
      stoppedProcess X (fun ω ↦ min (τ ω) (T : ENNReal)) := by
  have hStop :
      stoppedProcess (stoppedProcess X τ)
          (fun ω ↦ if τ ω ≤ (T : ENNReal) then ∞ else (T : ENNReal)) =
        stoppedProcess X
          (fun ω ↦ min (if τ ω ≤ (T : ENNReal) then ∞ else (T : ENNReal)) (τ ω)) :=
    stoppedProcess_stoppedProcess'
  refine hStop.trans ?_
  congr 1
  funext ω
  by_cases hω : τ ω ≤ (T : ENNReal)
  · -- Proof comment: after the stop has already occurred by time `T`, the release branch is
    -- `∞`, so only `τ` remains.
    calc
      min (if τ ω ≤ (T : ENNReal) then ∞ else (T : ENNReal)) (τ ω) = τ ω := by
        simp [hω]
      _ = min (τ ω) (T : ENNReal) := by rw [min_eq_left hω]
  · -- Proof comment: before `τ` is reached, the release-after clock is just the deterministic
    -- horizon `T`.
    simpa [hω, min_comm]

/-- Helper for Corollary 21.74: the missing bounded-horizon owner is the uniformly integrable
martingale package for `M ^ {(τ ∧ T)}`. -/
private lemma boundedHorizonMartingaleUi
    {τ : Ω → ENNReal} {M : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingaleUpTo ℱ μ τ M) (T : NNReal) :
    Martingale (stoppedProcess M (fun ω ↦ min (τ ω) (T : ENNReal))) ℱ μ ∧
      UniformIntegrable
        (stoppedProcess M (fun ω ↦ min (τ ω) (T : ENNReal))) 1 μ := by
  -- Route correction: the released-clock proof is now isolated from the old circular terminal
  -- slice route. The only remaining gap is to reconstruct the bounded-horizon owner `M ^ {(τ ∧ T)}`
  -- directly.
  have hMart :
      Martingale (stoppedProcess M (fun ω ↦ min (τ ω) (T : ENNReal))) ℱ μ := by
    -- Proof comment: the canonical Chapter 21 owner already gives the martingale statement for
    -- the bounded stop `τ ∧ T`, so no approximation machinery is needed here.
    simpa using
      IsContinuousLocalMartingaleUpTo.martingale_stoppedProcess_minConst_of_upTo
        (ℱ := ℱ)
        (μ := μ)
        (τ := τ)
        (M := M)
        hM
        T
  have hUI :
      UniformIntegrable
        (stoppedProcess M (fun ω ↦ min (τ ω) (T : ENNReal))) 1 μ := by
    -- Proof comment: stopping the already bounded-horizon martingale once more at the same
    -- deterministic time `T` leaves the process unchanged, so the standard deterministic-stop UI
    -- theorem closes the uniform-integrability clause.
    simpa [stoppedProcessConstTime_eq_min, min_assoc, min_left_comm, min_comm] using
      (martingaleUniformIntegrable_stoppedProcessConstTime
        (μ := μ)
        (ℱ := ℱ)
        hMart
        T).2
  exact ⟨hMart, hUI⟩

/-- Helper for Corollary 21.74: if the bounded-horizon owner `M ^ {(τ ∧ T)}` is a uniformly
integrable martingale for every deterministic horizon `T`, then the released clocks localize the
fully stopped process `M^τ`. -/
private lemma stoppedProcess_localizingSequence
    {τ : Ω → ENNReal} {M : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingaleUpTo ℱ μ τ M)
    (hτ : IsStoppingTime ℱ τ) :
    ∃ ν : ℕ → Ω → ENNReal, IsLocalizingSequence ℱ μ (stoppedProcess M τ) ν := by
  let ν : ℕ → Ω → ENNReal :=
    fun n ω ↦ if τ ω ≤ (n : ENNReal) then ∞ else (n : ENNReal)
  refine ⟨ν, (isLocalizingSequence_iff ℱ μ (stoppedProcess M τ) ν).2 ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro n
    -- Proof comment: each released deterministic horizon is a stopping time by the explicit
    -- branchwise description above.
    simpa [ν] using
      (releaseAfterConst_isStoppingTime (ℱ := ℱ) (τ := τ) (T := (n : NNReal)) hτ)
  · -- Proof comment: pathwise, the released clocks are monotone and eventually jump to `∞`.
    simpa [ν] using (releaseAfterConst_monotone_tendsto_top (μ := μ) (τ := τ))
  · intro n
    have hClock :
        stoppedProcess (stoppedProcess M τ) (ν n) =
          stoppedProcess M (fun ω ↦ min (τ ω) (n : ENNReal)) := by
      -- Proof comment: after releasing the deterministic horizon beyond `τ`, the visible process
      -- is exactly the bounded-horizon stop `M ^ {(τ ∧ n)}`.
      simpa [ν] using
        (stoppedProcess_stoppedProcess_releaseAfterConst
          (X := M) (τ := τ) (T := (n : NNReal)))
    exact hClock ▸ boundedHorizonMartingaleUi (ℱ := ℱ) (μ := μ) hM (n : NNReal)

/-- Corollary 21.74: if `M` is a continuous local martingale up to the stopping time `τ`, then
the stopped process `M^τ` is a continuous local martingale. -/
theorem isContinuousLocalMartingale_stoppedProcess
    {τ : Ω → ENNReal} {M : NNReal → Ω → ℝ}
    (hM : IsContinuousLocalMartingaleUpTo ℱ μ τ M)
    (hτ : IsStoppingTime ℱ τ) :
    IsContinuousLocalMartingale ℱ μ (stoppedProcess M τ) := by
  let Y : NNReal → Ω → ℝ := stoppedProcess M τ
  have hY_adapted : Adapted ℱ Y := by
    -- Proof comment: stopping preserves adaptedness for continuous sample paths.
    exact (hM.adapted.stronglyAdapted.stoppedProcess hM.continuous hτ).adapted
  have hY_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ Y t ω := by
    -- Proof comment: continuity survives time clipping at the stopping clock.
    simpa [Y] using continuous_stoppedProcess_of_continuous hM.continuous
  rcases stoppedProcess_localizingSequence (ℱ := ℱ) (μ := μ) (hM := hM) hτ with ⟨ν, hν⟩
  -- Proof comment: once the released clocks localize `M^τ`, the final theorem is the standard
  -- `IsLocalMartingale` packaging plus the preserved continuity.
  refine ⟨?_, hY_cont⟩
  exact (isLocalMartingale_iff ℱ μ Y).2 ⟨hY_adapted, ν, hν⟩

end IsContinuousLocalMartingaleUpTo

end ProbabilityTheory

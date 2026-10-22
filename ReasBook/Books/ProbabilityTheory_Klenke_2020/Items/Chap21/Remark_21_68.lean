/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_66

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

local notation "TimeFiltration" => Filtration NNReal mΩ

/-- Helper for Remark 21.68: `BoundedInTimeAe μ M` means that one deterministic constant bounds
the whole path `t ↦ M t ω` for every `t ≥ 0` outside a single `μ`-null set. -/
def BoundedInTimeAe (μ : Measure Ω) (M : NNReal → Ω → ℝ) : Prop :=
  ∃ C : ℝ, ∀ᵐ ω ∂μ, ∀ t : NNReal, |M t ω| ≤ C

/-- Helper for Remark 21.68: a pathwise deterministic bound can be replaced by a nonnegative one
without changing the exceptional null set. -/
lemma boundedInTimeAe_exists_nonneg_bound
    {μ : Measure Ω} {M : NNReal → Ω → ℝ} (hbounded : BoundedInTimeAe μ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ ω ∂μ, ∀ t : NNReal, |M t ω| ≤ C := by
  rcases hbounded with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  filter_upwards [hC] with ω hω t
  exact le_trans (hω t) (le_max_left _ _)

/-- Helper for Remark 21.68: a deterministic almost-sure bound makes each time slice integrable on
any finite measure. -/
lemma integrable_at_time_of_boundedInTimeAe
    {μ : Measure Ω} [IsFiniteMeasure μ] {M : NNReal → Ω → ℝ} (u : NNReal)
    (hbounded : BoundedInTimeAe μ M) (hMeas : AEStronglyMeasurable (M u) μ) :
    Integrable (M u) μ := by
  rcases boundedInTimeAe_exists_nonneg_bound hbounded with ⟨C, _, hC⟩
  -- Compare the time slice to the constant dominating function.
  refine Integrable.mono' (integrable_const C) hMeas ?_
  filter_upwards [hC] with ω hω
  simpa [Real.norm_eq_abs] using hω u

/-- Helper for Remark 21.68: along a localizing sequence, each fixed-time stopped value eventually
agrees with the original process, so the stopped values converge almost surely. -/
lemma ae_tendsto_stoppedProcess_at_time_of_localizingSequence
    {μ : Measure Ω} {ℱ : TimeFiltration} {M : NNReal → Ω → ℝ}
    {τSeq : ℕ → Ω → ENNReal} (hτSeq : IsLocalizingSequence ℱ μ M τSeq) (u : NNReal) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ stoppedProcess M (τSeq n) u ω) atTop (𝓝 (M u ω)) := by
  rcases (isLocalizingSequence_iff ℱ μ M τSeq).1 hτSeq with ⟨_, hlim, _⟩
  filter_upwards [hlim] with ω hω
  rcases hω with ⟨_, hωtendsto⟩
  -- Convergence of `τₙ ω` to `∞` forces eventual release of the stopping at every fixed time `u`.
  have hu_eventually : ∀ᶠ n in atTop, (u : ENNReal) ≤ τSeq n ω :=
    (ENNReal.tendsto_nhds_top_iff_nnreal.1 hωtendsto u).mono fun _ hn ↦ le_of_lt hn
  have hEventuallyEq :
      (fun n ↦ stoppedProcess M (τSeq n) u ω) =ᶠ[atTop] fun _ ↦ M u ω :=
    hu_eventually.mono fun _ hn ↦ stoppedProcess_eq_of_le hn
  exact Tendsto.congr' hEventuallyEq.symm tendsto_const_nhds

/-- Helper for Remark 21.68: dominated convergence upgrades the almost-sure convergence of the
stopped process at time `u` to convergence of its set integrals on any measurable set. -/
lemma tendsto_setIntegral_stoppedProcess_at_time
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : TimeFiltration} {M : NNReal → Ω → ℝ}
    {s u : NNReal} {A : Set Ω} (_ : MeasurableSet[ℱ s] A) (hbounded : BoundedInTimeAe μ M)
    {τSeq : ℕ → Ω → ENNReal} (hτSeq : IsLocalizingSequence ℱ μ M τSeq) :
    Tendsto (fun n ↦ ∫ ω in A, stoppedProcess M (τSeq n) u ω ∂μ) atTop
      (𝓝 (∫ ω in A, M u ω ∂μ)) := by
  rcases boundedInTimeAe_exists_nonneg_bound hbounded with ⟨C, _, hC⟩
  rcases (isLocalizingSequence_iff ℱ μ M τSeq).1 hτSeq with ⟨_, _, hMart⟩
  let ν : Measure Ω := μ.restrict A
  letI : IsFiniteMeasure ν := by
    infer_instance
  have hBoundInt : Integrable (fun _ : Ω ↦ C) ν := integrable_const C
  have hMeas :
      ∀ n, AEStronglyMeasurable (fun ω ↦ stoppedProcess M (τSeq n) u ω) ν := by
    intro n
    exact (((hMart n).1.integrable u).mono_measure (Measure.restrict_le_self)).aestronglyMeasurable
  have hBound :
      ∀ n, ∀ᵐ ω ∂ν, ‖stoppedProcess M (τSeq n) u ω‖ ≤ C := by
    intro n
    filter_upwards [ae_restrict_of_ae hC] with ω hω
    simpa [Real.norm_eq_abs, stoppedProcess] using hω ((min (u : ENNReal) (τSeq n ω)).untopA)
  have hLim :
      ∀ᵐ ω ∂ν, Tendsto (fun n ↦ stoppedProcess M (τSeq n) u ω) atTop (𝓝 (M u ω)) :=
    ae_restrict_of_ae (ae_tendsto_stoppedProcess_at_time_of_localizingSequence hτSeq u)
  -- Work on the restricted measure so the set integral becomes an ordinary integral.
  simpa [ν] using
    (tendsto_integral_of_dominated_convergence (fun _ : Ω ↦ C)
      hMeas hBoundInt hBound hLim)

/-- Helper for Remark 21.68: the stopped martingale identities pass to the limit and give the set
integral characterization of the original process. -/
lemma setIntegral_eq_of_bounded_localizingSequence
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : TimeFiltration} {M : NNReal → Ω → ℝ}
    {s t : NNReal} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[ℱ s] A)
    (hbounded : BoundedInTimeAe μ M) {τSeq : ℕ → Ω → ENNReal}
    (hτSeq : IsLocalizingSequence ℱ μ M τSeq) :
    ∫ ω in A, M t ω ∂μ = ∫ ω in A, M s ω ∂μ := by
  rcases (isLocalizingSequence_iff ℱ μ M τSeq).1 hτSeq with ⟨_, _, hMart⟩
  have hEqStopped :
      ∀ n,
        ∫ ω in A, stoppedProcess M (τSeq n) t ω ∂μ =
          ∫ ω in A, stoppedProcess M (τSeq n) s ω ∂μ := by
    intro n
    -- Each stopped process is a martingale, so its set integrals already agree.
    simpa using ((hMart n).1.setIntegral_eq hst hA).symm
  have htendsto :
      Tendsto (fun n ↦ ∫ ω in A, stoppedProcess M (τSeq n) t ω ∂μ) atTop
        (𝓝 (∫ ω in A, M t ω ∂μ)) :=
    tendsto_setIntegral_stoppedProcess_at_time hA hbounded hτSeq
  have hstendsto :
      Tendsto (fun n ↦ ∫ ω in A, stoppedProcess M (τSeq n) s ω ∂μ) atTop
        (𝓝 (∫ ω in A, M s ω ∂μ)) :=
    tendsto_setIntegral_stoppedProcess_at_time hA hbounded hτSeq
  have hstendsto' :
      Tendsto (fun n ↦ ∫ ω in A, stoppedProcess M (τSeq n) t ω ∂μ) atTop
        (𝓝 (∫ ω in A, M s ω ∂μ)) := by
    refine Tendsto.congr' (Filter.Eventually.of_forall fun n ↦ (hEqStopped n).symm) hstendsto
  exact tendsto_nhds_unique htendsto hstendsto'

-- Proof sketch: choose a localizing sequence for `M`; each stopped process is a martingale, so
-- for `A ∈ ℱ s` one has equality of expectations on `A ∩ {τₙ ≤ s}`. A single almost-sure bound
-- uniform in time dominates the stopped values `M (τₙ ∧ t)`, and dominated convergence lets
-- `n → ∞` pass through the stopped identities to recover the martingale
-- conditional-expectation relation for `M` itself.
/-- Remark 21.68: on a probability space, a bounded local martingale is a martingale. Here
boundedness is recorded by `BoundedInTimeAe μ M`, meaning that one deterministic constant bounds
`|M t ω|` for every `t ≥ 0` outside a single `μ`-null set of sample points. -/
theorem martingale_of_bounded_local_martingale
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : TimeFiltration} {M : NNReal → Ω → ℝ}
    (hlocal : IsLocalMartingale ℱ μ M)
    (hbounded : BoundedInTimeAe μ M) :
    Martingale M ℱ μ := by
  rcases (isLocalMartingale_iff ℱ μ M).1 hlocal with ⟨hadapted, τSeq, hτSeq⟩
  have hstrong : StronglyAdapted ℱ M := hadapted.stronglyAdapted
  have hInt : ∀ u : NNReal, Integrable (M u) μ := by
    intro u
    -- The deterministic pathwise bound gives integrability of every time slice.
    refine integrable_at_time_of_boundedInTimeAe u hbounded ?_
    exact ((hstrong u).mono (ℱ.le u)).aestronglyMeasurable
  have hSub : Submartingale M ℱ μ := by
    refine submartingale_of_setIntegral_le hstrong hInt ?_
    intro s t hst A hA
    -- Pass the stopped martingale identities to the limit on each `A ∈ ℱ s`.
    exact le_of_eq <|
      (setIntegral_eq_of_bounded_localizingSequence hst hA hbounded hτSeq).symm
  have hSubNeg : Submartingale (-M) ℱ μ := by
    refine submartingale_of_setIntegral_le hstrong.neg (fun u ↦ (hInt u).neg) ?_
    intro s t hst A hA
    have hEq :
        ∫ ω in A, M t ω ∂μ = ∫ ω in A, M s ω ∂μ :=
      setIntegral_eq_of_bounded_localizingSequence hst hA hbounded hτSeq
    -- Apply the same set-integral identity to the negated process to get a supermartingale.
    apply le_of_eq
    simpa only [Pi.neg_apply, integral_neg] using congrArg Neg.neg hEq.symm
  have hSuper : Supermartingale M ℱ μ := by
    simpa using hSubNeg.neg
  exact (martingale_iff).2 ⟨hSuper, hSub⟩

end ProbabilityTheory

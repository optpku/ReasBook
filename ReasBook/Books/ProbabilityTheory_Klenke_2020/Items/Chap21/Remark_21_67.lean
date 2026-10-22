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

variable {Ω : Type u}

/-- A real-valued continuous-time process is bounded if a single deterministic constant bounds all
sample paths at all times. This stronger auxiliary notion is useful downstream, but the
source-faithful boundedness notion for Remark 21.67 is the pathwise version below. -/
def IsBoundedProcess (X : NNReal → Ω → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t : NNReal, ∀ ω : Ω, |X t ω| ≤ C

/-- A real-valued continuous-time process is pathwise bounded if each sample path is bounded by
some sample-dependent constant. This is the source-faithful boundedness notion used in
Remark 21.67. -/
def IsPathwiseBoundedProcess (X : NNReal → Ω → ℝ) : Prop :=
  ∀ ω : Ω, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : NNReal, |X t ω| ≤ C

/-- A bounded process is, in particular, pathwise bounded. -/
theorem IsBoundedProcess.isPathwiseBounded {X : NNReal → Ω → ℝ}
    (hX : IsBoundedProcess X) :
    IsPathwiseBoundedProcess X := by
  rcases hX with ⟨C, hC_nonneg, hC⟩
  intro ω
  exact ⟨C, hC_nonneg, fun t ↦ hC t ω⟩

variable [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω}
variable {M : NNReal → Ω → ℝ} {τ : Ω → ENNReal}

local notation "TimeFiltration" => Filtration NNReal mΩ

variable {ℱ : Filtration NNReal mΩ}

/-- A sequence of stopping times approximates `τ` if it is almost surely increasing and converges
almost surely to `τ`. -/
def IsStoppingTimeApproximationUpTo
    (ℱ : TimeFiltration) (μ : Measure Ω)
    (τSeq : ℕ → Ω → ENNReal) (τ : Ω → ENNReal) : Prop :=
  IsStoppingTime ℱ τ ∧
    (∀ n : ℕ, IsStoppingTime ℱ (τSeq n)) ∧
    ∀ᵐ ω ∂μ,
      Monotone (fun n ↦ τSeq n ω) ∧
        Tendsto (fun n ↦ τSeq n ω) atTop (𝓝 (τ ω))

-- Semantic recall: `lean_leansearch` only surfaced the generic stopped-process API, so the
-- source-facing clause owners below are introduced locally on top of the chapter owner from
-- `Definition 21.66`.
/-- Source clause `(ii)`: `M` admits an almost surely increasing stopping-time approximation to
`τ` whose stopped processes are martingales. -/
def HasStoppedMartingaleApproximationUpTo
    (ℱ : TimeFiltration) (μ : Measure Ω)
    (τ : Ω → ENNReal) (M : NNReal → Ω → ℝ) : Prop :=
  ∃ τSeq : ℕ → Ω → ENNReal,
    IsStoppingTimeApproximationUpTo ℱ μ τSeq τ ∧
      ∀ n : ℕ, Martingale (stoppedProcess M (τSeq n)) ℱ μ

/-- Unfolding `HasStoppedMartingaleApproximationUpTo` gives the approximation and martingale
clauses from source clause `(ii)`. -/
theorem hasStoppedMartingaleApproximationUpTo_iff
    (ℱ : TimeFiltration) (μ : Measure Ω)
    (τ : Ω → ENNReal) (M : NNReal → Ω → ℝ) :
    HasStoppedMartingaleApproximationUpTo ℱ μ τ M ↔
      ∃ τSeq : ℕ → Ω → ENNReal,
        IsStoppingTimeApproximationUpTo ℱ μ τSeq τ ∧
          ∀ n : ℕ, Martingale (stoppedProcess M (τSeq n)) ℱ μ :=
  Iff.rfl

/-- Source clause `(iii)`: `M` admits an almost surely increasing stopping-time approximation to
`τ` whose stopped processes are bounded martingales in the source-faithful sample-path-wise
sense. -/
def HasPathwiseBoundedStoppedMartingaleApproximationUpTo
    (ℱ : TimeFiltration) (μ : Measure Ω)
    (τ : Ω → ENNReal) (M : NNReal → Ω → ℝ) : Prop :=
  ∃ τSeq : ℕ → Ω → ENNReal,
    IsStoppingTimeApproximationUpTo ℱ μ τSeq τ ∧
      ∀ n : ℕ,
        Martingale (stoppedProcess M (τSeq n)) ℱ μ ∧
          IsPathwiseBoundedProcess (stoppedProcess M (τSeq n))

/-- Unfolding `HasPathwiseBoundedStoppedMartingaleApproximationUpTo` gives the approximation,
martingale, and sample-path boundedness clauses of source clause `(iii)`. -/
theorem hasPathwiseBoundedStoppedMartingaleApproximationUpTo_iff
    (ℱ : TimeFiltration) (μ : Measure Ω)
    (τ : Ω → ENNReal) (M : NNReal → Ω → ℝ) :
    HasPathwiseBoundedStoppedMartingaleApproximationUpTo ℱ μ τ M ↔
      ∃ τSeq : ℕ → Ω → ENNReal,
        IsStoppingTimeApproximationUpTo ℱ μ τSeq τ ∧
          ∀ n : ℕ,
            Martingale (stoppedProcess M (τSeq n)) ℱ μ ∧
              IsPathwiseBoundedProcess (stoppedProcess M (τSeq n)) :=
  Iff.rfl

/-- Auxiliary stronger bounded clause: `M` admits an almost surely increasing stopping-time
approximation to `τ` whose stopped processes are martingales and are each bounded by a single
deterministic constant. -/
def HasBoundedStoppedMartingaleApproximationUpTo
    (ℱ : TimeFiltration) (μ : Measure Ω)
    (τ : Ω → ENNReal) (M : NNReal → Ω → ℝ) : Prop :=
  ∃ τSeq : ℕ → Ω → ENNReal,
    IsStoppingTimeApproximationUpTo ℱ μ τSeq τ ∧
      ∀ n : ℕ,
        Martingale (stoppedProcess M (τSeq n)) ℱ μ ∧
          IsBoundedProcess (stoppedProcess M (τSeq n))

/-- Unfolding `HasBoundedStoppedMartingaleApproximationUpTo` gives the approximation, martingale,
and deterministic boundedness clauses of the stronger auxiliary owner. -/
theorem hasBoundedStoppedMartingaleApproximationUpTo_iff
    (ℱ : TimeFiltration) (μ : Measure Ω)
    (τ : Ω → ENNReal) (M : NNReal → Ω → ℝ) :
    HasBoundedStoppedMartingaleApproximationUpTo ℱ μ τ M ↔
      ∃ τSeq : ℕ → Ω → ENNReal,
        IsStoppingTimeApproximationUpTo ℱ μ τSeq τ ∧
          ∀ n : ℕ,
            Martingale (stoppedProcess M (τSeq n)) ℱ μ ∧
              IsBoundedProcess (stoppedProcess M (τSeq n)) :=
  Iff.rfl

/-- The stronger deterministic-bounded approximation owner implies the source-faithful
pathwise-bounded owner. -/
theorem HasBoundedStoppedMartingaleApproximationUpTo.toPathwise
    (h : HasBoundedStoppedMartingaleApproximationUpTo ℱ μ τ M) :
    HasPathwiseBoundedStoppedMartingaleApproximationUpTo ℱ μ τ M := by
  rcases h with ⟨τSeq, hApprox, hBounded⟩
  refine ⟨τSeq, hApprox, ?_⟩
  intro n
  exact ⟨(hBounded n).1, ((hBounded n).2).isPathwiseBounded⟩

namespace IsLocalizingSequenceUpTo

/-- Every localizing sequence up to `τ` yields the underlying stopping-time approximation to `τ`.
-/
theorem stoppingTimeApproximationUpTo
    {τ : Ω → ENNReal} {M : NNReal → Ω → ℝ} {τSeq : ℕ → Ω → ENNReal} :
    IsLocalizingSequenceUpTo ℱ μ τ M τSeq →
      IsStoppingTimeApproximationUpTo ℱ μ τSeq τ := by
  rintro ⟨hτ, hτSeq, hlim, _⟩
  exact ⟨hτ, hτSeq, hlim⟩

end IsLocalizingSequenceUpTo

/-- Helper for Remark 21.67: timewise almost-everywhere equality preserves the martingale
property once the target process is already known to be strongly adapted. -/
lemma martingale_congr_ae
    {M N : NNReal → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hN_stronglyAdapted : StronglyAdapted ℱ N) (hMN : ∀ t : NNReal, M t =ᵐ[μ] N t) :
    Martingale N ℱ μ := by
  -- Proof comment: transport the conditional-expectation identity from `M` to `N` at times
  -- `t` and `s`.
  refine ⟨hN_stronglyAdapted, ?_⟩
  intro s t hst
  exact (condExp_congr_ae (hMN t)).symm.trans ((hM.condExp_ae_eq hst).trans (hMN s))

omit mΩ in
/-- Helper for Remark 21.67: deterministic stopping at time `T` is just time clipping by
`min t T`. -/
lemma stoppedProcessConstTime_eq_min
    {X : NNReal → Ω → ℝ} (T t : NNReal) :
    stoppedProcess X (fun _ ↦ (T : ENNReal)) t = X (min t T) := by
  ext ω
  -- Proof comment: unfold deterministic stopping and split on whether `t` is before or after
  -- the fixed horizon `T`.
  rw [stoppedProcess]
  change X ((min (t : ENNReal) T).untopA) ω = X (min t T) ω
  by_cases ht : t ≤ T
  · have hmin : min (t : ENNReal) T = t := by
      exact min_eq_left (by exact_mod_cast ht)
    have htop : (t : ENNReal) ≠ ⊤ := by
      simp
    rw [hmin]
    have hUntop : WithTop.untop (t : ENNReal) htop = t := by
      exact WithTop.coe_inj.mp (WithTop.coe_untop (t : ENNReal) htop)
    rw [WithTop.untopA_eq_untop htop, hUntop]
    simp [min_eq_left ht]
  · have hTt : T ≤ t := le_of_not_ge ht
    have hmin : min (t : ENNReal) T = T := by
      exact min_eq_right (by exact_mod_cast hTt)
    have htop : (T : ENNReal) ≠ ⊤ := by
      simp
    rw [hmin]
    have hUntop : WithTop.untop (T : ENNReal) htop = T := by
      exact WithTop.coe_inj.mp (WithTop.coe_untop (T : ENNReal) htop)
    rw [WithTop.untopA_eq_untop htop, hUntop]
    simp [min_eq_right hTt]

/-- Helper for Remark 21.67: conditioning the fixed terminal value `X T` along the clipped
filtration `ℱ (min t T)` gives a martingale in the original filtration. -/
lemma martingaleCondExpConstTime
    [IsFiniteMeasure μ] {X : NNReal → Ω → ℝ}
    (hX : Martingale X ℱ μ) (T : NNReal) :
    Martingale (fun t ω ↦ μ[X T | ℱ (min t T)] ω) ℱ μ := by
  -- Proof comment: before time `T` this is the tower property, and after time `T` the
  -- conditional expectation has stabilized at the terminal slice `X T`.
  refine ⟨?_, ?_⟩
  · intro t
    exact stronglyMeasurable_condExp.mono (ℱ.mono (min_le_left t T))
  · intro s t hst
    by_cases hs : s ≤ T
    · have hsle : s ≤ min t T := le_min hst hs
      simpa [min_eq_left hs] using
        (condExp_condExp_of_le (ℱ.mono hsle) (ℱ.le (min t T)) :
          μ[μ[X T | ℱ (min t T)] | ℱ s] =ᵐ[μ] μ[X T | ℱ s])
    · have hTs : T ≤ s := le_of_not_ge hs
      have hTt : T ≤ t := hTs.trans hst
      have hTT : μ[X T | ℱ T] = X T :=
        condExp_of_stronglyMeasurable (ℱ.le T) (hX.stronglyMeasurable T) (hX.integrable T)
      have hEqt : (fun ω ↦ μ[X T | ℱ (min t T)] ω) =ᵐ[μ] X T := by
        exact Filter.EventuallyEq.of_eq (by simpa [min_eq_right hTt] using hTT)
      have hEqs : (fun ω ↦ μ[X T | ℱ (min s T)] ω) =ᵐ[μ] X T := by
        exact Filter.EventuallyEq.of_eq (by simpa [min_eq_right hTs] using hTT)
      have hcond : μ[X T | ℱ s] = X T :=
        condExp_of_stronglyMeasurable (ℱ.le s)
          ((hX.stronglyMeasurable T).mono (ℱ.mono hTs)) (hX.integrable T)
      have hleft :
          μ[(fun ω ↦ μ[X T | ℱ (min t T)] ω) | ℱ s] =ᵐ[μ] μ[X T | ℱ s] :=
        condExp_congr_ae hEqt
      have hright :
          μ[X T | ℱ s] =ᵐ[μ] fun ω ↦ μ[X T | ℱ (min s T)] ω := by
        exact (Filter.EventuallyEq.of_eq hcond).trans hEqs.symm
      exact hleft.trans hright

/-- Helper for Remark 21.67: the process stopped at the deterministic time `T` agrees almost
everywhere with the corresponding conditional-expectation martingale. -/
lemma stoppedProcessConstTime_ae_eq_condExp
    [IsFiniteMeasure μ] {X : NNReal → Ω → ℝ}
    (hX : Martingale X ℱ μ) (T t : NNReal) :
    stoppedProcess X (fun _ ↦ (T : ENNReal)) t =ᵐ[μ] fun ω ↦ μ[X T | ℱ (min t T)] ω := by
  -- Proof comment: before `T` this is the martingale identity, and after `T` both sides equal
  -- the terminal slice `X T`.
  by_cases ht : t ≤ T
  · simpa [stoppedProcessConstTime_eq_min, min_eq_left ht] using (hX.condExp_ae_eq ht).symm
  · have hTt : T ≤ t := le_of_not_ge ht
    have hTT : μ[X T | ℱ T] = X T :=
      condExp_of_stronglyMeasurable (ℱ.le T) (hX.stronglyMeasurable T) (hX.integrable T)
    exact Filter.EventuallyEq.of_eq (by
      simpa [stoppedProcessConstTime_eq_min, min_eq_right hTt] using hTT.symm)

/-- Helper for Remark 21.67: on a finite measure space, stopping a martingale at a deterministic
time gives a uniformly integrable martingale. -/
lemma martingaleUniformIntegrable_stoppedProcessConstTime
    [IsFiniteMeasure μ] {X : NNReal → Ω → ℝ}
    (hX : Martingale X ℱ μ) (T : NNReal) :
    Martingale (stoppedProcess X (fun _ ↦ (T : ENNReal))) ℱ μ ∧
      UniformIntegrable (stoppedProcess X (fun _ ↦ (T : ENNReal))) 1 μ := by
  let N : NNReal → Ω → ℝ := fun t ω ↦ μ[X T | ℱ (min t T)] ω
  have hN_mart : Martingale N ℱ μ := martingaleCondExpConstTime hX T
  have hStopped_strong : StronglyAdapted ℱ (stoppedProcess X (fun _ ↦ (T : ENNReal))) := by
    intro t
    -- Proof comment: the deterministic stop at `T` is just evaluation at `min t T`.
    simpa [N, stoppedProcessConstTime_eq_min] using
      ((hX.stronglyMeasurable (min t T)).mono (ℱ.mono (min_le_left t T)))
  have hStopped_eq :
      ∀ t : NNReal,
        N t =ᵐ[μ] stoppedProcess X (fun _ ↦ (T : ENNReal)) t := by
    intro t
    exact (stoppedProcessConstTime_ae_eq_condExp hX T t).symm
  have hStopped_mart :
      Martingale (stoppedProcess X (fun _ ↦ (T : ENNReal))) ℱ μ :=
    martingale_congr_ae hN_mart hStopped_strong hStopped_eq
  letI : SigmaFinite μ := by
    infer_instance
  have hUI_N : UniformIntegrable N 1 μ := by
    -- Proof comment: conditional expectations of the integrable terminal slice `X T` are
    -- uniformly integrable as a family.
    simpa [N] using
      (hX.integrable T).uniformIntegrable_condExp fun t : NNReal ↦ ℱ.le (min t T)
  exact ⟨hStopped_mart, hUI_N.ae_eq hStopped_eq⟩

/-- Helper for Remark 21.67: clipping a stopping-time approximation by the deterministic horizon
`n` termwise still yields an almost surely increasing approximation to the same terminal stopping
time `τ`. -/
lemma stoppingTimeApproximationUpTo_minConst
    {τSeq : ℕ → Ω → ENNReal}
    (hApprox : IsStoppingTimeApproximationUpTo ℱ μ τSeq τ) :
    IsStoppingTimeApproximationUpTo ℱ μ
      (fun n ω ↦ min (τSeq n ω) (n : ENNReal)) τ := by
  rcases hApprox with ⟨hτ, hτSeq, hlim⟩
  refine ⟨hτ, ?_, ?_⟩
  · intro n
    exact (hτSeq n).min_const n
  · filter_upwards [hlim] with ω hω
    rcases hω with ⟨hmono, htendsto⟩
    refine ⟨?_, ?_⟩
    · intro a b hab
      exact min_le_min (hmono hab) (by exact_mod_cast hab)
    · -- Proof comment: `τₙ ω → τ ω` and the deterministic horizons `n` tend to `∞`, so their
      -- pointwise minima still converge to `τ ω`.
      have hpair :
          Tendsto (fun n : ℕ ↦ (τSeq n ω, (n : ENNReal))) atTop (𝓝 (τ ω, (∞ : ENNReal))) :=
        Filter.Tendsto.prodMk_nhds htendsto ENNReal.tendsto_nat_nhds_top
      have hmin : Continuous fun p : ENNReal × ENNReal ↦ min p.1 p.2 :=
        continuous_fst.inf continuous_snd
      have hmin_tendsto :
          Tendsto (fun p : ENNReal × ENNReal ↦ min p.1 p.2)
            (𝓝 (τ ω, (∞ : ENNReal))) (𝓝 (min (τ ω) (∞ : ENNReal))) :=
        hmin.continuousAt.tendsto
      simpa using hmin_tendsto.comp hpair

omit mΩ in
/-- Helper for Remark 21.67: if `σ` is bounded above by the deterministic horizon `T`, then
stopping a continuous process at `σ` produces pathwise bounded sample paths. -/
lemma isPathwiseBoundedProcess_stoppedProcess_of_le_const
    {X : NNReal → Ω → ℝ} (hX_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ X t ω)
    {σ : Ω → ENNReal} (T : NNReal) (hσ_le : ∀ ω, σ ω ≤ (T : ENNReal)) :
    IsPathwiseBoundedProcess (stoppedProcess X σ) := by
  intro ω
  obtain ⟨C, hC⟩ :
      ∃ C : ℝ, ∀ s ∈ Set.Icc (0 : NNReal) T, ‖X s ω‖ ≤ C :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : NNReal) T)).exists_bound_of_continuousOn
      (hX_cont ω).continuousOn
  have hC_nonneg : 0 ≤ C := by
    have hzero_mem : (0 : NNReal) ∈ Set.Icc (0 : NNReal) T := by
      constructor
      · rfl
      · exact bot_le
    exact le_trans (norm_nonneg _) (hC 0 hzero_mem)
  refine ⟨C, hC_nonneg, ?_⟩
  intro t
  have hmem :
      ((min (t : ENNReal) (σ ω)).untopA : NNReal) ∈ Set.Icc (0 : NNReal) T := by
    constructor
    · exact bot_le
    · have hleENN : min (t : ENNReal) (σ ω) ≤ (T : ENNReal) :=
        le_trans (min_le_right _ _) (hσ_le ω)
      have hfinite : min (t : ENNReal) (σ ω) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
      have hEq :
          (((min (t : ENNReal) (σ ω)).untopA : NNReal) : ENNReal) =
            min (t : ENNReal) (σ ω) := by
        rw [WithTop.untopA_eq_untop hfinite]
        exact WithTop.coe_untop (min (t : ENNReal) (σ ω)) hfinite
      have hleUntop :
          (((min (t : ENNReal) (σ ω)).untopA : NNReal) : ENNReal) ≤ (T : ENNReal) := by
        exact le_of_eq_of_le hEq hleENN
      exact_mod_cast hleUntop
  -- Proof comment: every stopped value is the original path evaluated at a time in `[0,T]`.
  simpa [Real.norm_eq_abs, stoppedProcess] using
    hC ((min (t : ENNReal) (σ ω)).untopA) hmem

-- Source-faithful route: clipping the approximating stopping times by deterministic horizons
-- already gives the pathwise-bounded stopped martingale approximation used in Remark 21.67.
/-- On a probability space, continuity plus adaptedness refines a stopped-martingale
approximation to the chapter's pathwise-bounded stopped-martingale helper by deterministic time
clipping. -/
lemma pathwiseBoundedMartingaleApproximationFromStoppedApproximation
    [IsProbabilityMeasure μ]
    (hM_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω)
    (hApproxMart : HasStoppedMartingaleApproximationUpTo ℱ μ τ M) :
    HasPathwiseBoundedStoppedMartingaleApproximationUpTo ℱ μ τ M := by
  -- Route correction: on the current general owner surface, the level-hit-time construction
  -- is unnecessary; clipping the stopping-time approximation by deterministic horizons already
  -- yields the source-faithful pathwise-bounded clause recorded here.
  rcases hApproxMart with ⟨τSeq, hApprox, hMart⟩
  let σ : ℕ → Ω → ENNReal := fun n ω ↦ min (τSeq n ω) (n : ENNReal)
  have hApproxσ : IsStoppingTimeApproximationUpTo ℱ μ σ τ :=
    stoppingTimeApproximationUpTo_minConst hApprox
  refine ⟨σ, hApproxσ, ?_⟩
  intro n
  have hDoubleStop :
      stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (n : ENNReal)) =
        stoppedProcess M (σ n) := by
    -- Proof comment: stopping `M ^ {τₙ}` once more at the deterministic time `n` is the same as
    -- stopping `M` at the clipped time `τₙ ∧ n`.
    have hStop :
        stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (n : ENNReal)) =
          stoppedProcess M (fun ω ↦ min ((fun _ ↦ (n : ENNReal)) ω) (τSeq n ω)) :=
      stoppedProcess_stoppedProcess'
    simpa [σ, min_comm] using hStop
  have hStoppedMart :
      Martingale (stoppedProcess M (σ n)) ℱ μ := by
    have hDetStop :
        Martingale (stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (n : ENNReal))) ℱ μ ∧
          UniformIntegrable
            (stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (n : ENNReal))) 1 μ :=
      martingaleUniformIntegrable_stoppedProcessConstTime (hMart n) n
    exact hDoubleStop ▸ hDetStop.1
  have hStoppedBounded :
      IsPathwiseBoundedProcess (stoppedProcess M (σ n)) := by
    -- Proof comment: `σₙ ≤ n` pointwise, so the stopped path only explores the compact interval
    -- `[0, n]`, where continuity makes each sample path bounded.
    refine isPathwiseBoundedProcess_stoppedProcess_of_le_const hM_cont n ?_
    intro ω
    exact min_le_right _ _
  exact ⟨hStoppedMart, hStoppedBounded⟩

/-- Source clause `(i) ↔ (ii)` from Remark 21.67: on a probability space, for a continuous
adapted process `M` and a stopping time `τ`, being a local martingale up to `τ` is equivalent to
admitting an almost surely increasing sequence of stopping times converging to `τ` whose stopped
processes are martingales. -/
theorem isLocalMartingaleUpTo_iff_exists_stopped_martingale_approximation_continuousAdapted
    [IsProbabilityMeasure μ]
    (hM_adapted : Adapted ℱ M)
    (hM_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω) :
    IsLocalMartingaleUpTo ℱ μ τ M ↔ HasStoppedMartingaleApproximationUpTo ℱ μ τ M := by
  let hM_cont_source_context := hM_cont
  clear hM_cont_source_context
  constructor
  · intro hLocal
    rcases (isLocalMartingaleUpTo_iff ℱ μ τ M).1 hLocal with ⟨_, τSeq, hSeq⟩
    have hApprox : IsStoppingTimeApproximationUpTo ℱ μ τSeq τ :=
      IsLocalizingSequenceUpTo.stoppingTimeApproximationUpTo hSeq
    rcases hSeq with ⟨_, _, _, hMartUI⟩
    -- Proof comment: a localizing sequence up to `τ` already supplies the approximation from
    -- clause `(ii)` after forgetting uniform integrability.
    exact ⟨τSeq, hApprox, fun n ↦ (hMartUI n).1⟩
  · rintro ⟨τSeq, hApprox, hMart⟩
    let τSeqT : ℕ → Ω → ENNReal := fun n ω ↦ min (τSeq n ω) (n : ENNReal)
    have hApproxT : IsStoppingTimeApproximationUpTo ℱ μ τSeqT τ :=
      stoppingTimeApproximationUpTo_minConst hApprox
    have hMartUIT : ∀ n : ℕ,
        Martingale (stoppedProcess M (τSeqT n)) ℱ μ ∧
          UniformIntegrable (stoppedProcess M (τSeqT n)) 1 μ := by
      intro n
      have hDoubleStop :
          stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (n : ENNReal)) =
            stoppedProcess M (τSeqT n) := by
        -- Proof comment: stopping `M^τₙ` again at time `n` is the same as stopping `M` once at
        -- the clipped time `τₙ ∧ n`.
        have hStop :
            stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (n : ENNReal)) =
              stoppedProcess M (fun ω ↦ min ((fun _ ↦ (n : ENNReal)) ω) (τSeq n ω)) :=
          stoppedProcess_stoppedProcess'
        simpa [τSeqT, min_comm] using hStop
      have hDetStop :
          Martingale (stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (n : ENNReal))) ℱ μ ∧
            UniformIntegrable
              (stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (n : ENNReal))) 1 μ :=
        martingaleUniformIntegrable_stoppedProcessConstTime (hMart n) n
      exact hDoubleStop ▸ hDetStop
    -- Proof comment: the clipped approximation `τₙ ∧ n` keeps the same limit `τ` and turns
    -- each stopped martingale into a uniformly integrable one.
    exact (isLocalMartingaleUpTo_iff ℱ μ τ M).2
      ⟨hM_adapted, τSeqT, ⟨hApproxT.1, hApproxT.2.1, hApproxT.2.2, hMartUIT⟩⟩

-- Owner-level bridge kept for downstream files: `Definition 21.66` packages clause `(ii)` with
-- uniform integrability.
/-- Helper bridge to the chapter owner `IsLocalMartingaleUpTo`: under adaptedness, being a local
martingale up to `τ` is equivalent to admitting an almost surely increasing sequence of stopping
times converging to `τ` whose stopped processes are uniformly integrable martingales. -/
theorem isLocalMartingaleUpTo_iff_exists_stopped_martingale_sequence
    (hM_adapted : Adapted ℱ M) :
    IsLocalMartingaleUpTo ℱ μ τ M ↔
      ∃ τSeq : ℕ → Ω → ENNReal,
        IsStoppingTimeApproximationUpTo ℱ μ τSeq τ ∧
          ∀ n : ℕ,
            Martingale (stoppedProcess M (τSeq n)) ℱ μ ∧
              UniformIntegrable (stoppedProcess M (τSeq n)) 1 μ := by
  constructor
  · intro hLocal
    rcases (isLocalMartingaleUpTo_iff ℱ μ τ M).1 hLocal with ⟨_, τSeq, hSeq⟩
    have hApprox : IsStoppingTimeApproximationUpTo ℱ μ τSeq τ :=
      IsLocalizingSequenceUpTo.stoppingTimeApproximationUpTo hSeq
    rcases hSeq with ⟨_, _, _, hMartUI⟩
    -- Proof comment: unfold the localizing-sequence owner and keep all fields explicitly.
    exact ⟨τSeq, hApprox, hMartUI⟩
  · rintro ⟨τSeq, hApprox, hMartUI⟩
    -- Proof comment: the right-hand side is exactly the chapter owner after repackaging the
    -- stopping-time approximation and uniform-integrability data.
    exact (isLocalMartingaleUpTo_iff ℱ μ τ M).2
      ⟨hM_adapted, τSeq, ⟨hApprox.1, hApprox.2.1, hApprox.2.2, hMartUI⟩⟩

/-- Auxiliary stronger bounded consequence: if a continuous adapted process admits an almost
surely increasing stopping-time approximation to `τ` whose stopped processes are deterministically
bounded martingales, then it is a local martingale up to `τ`. -/
theorem isLocalMartingaleUpTo_of_exists_bounded_stopped_martingale_sequence
    (hM_adapted : Adapted ℱ M)
    (hM_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω)
    [IsProbabilityMeasure μ] :
    HasBoundedStoppedMartingaleApproximationUpTo ℱ μ τ M →
      IsLocalMartingaleUpTo ℱ μ τ M := by
  rintro ⟨τSeq, hApprox, hMartBounded⟩
  have hStopped :
      HasStoppedMartingaleApproximationUpTo ℱ μ τ M :=
    ⟨τSeq, hApprox, fun n ↦ (hMartBounded n).1⟩
  exact
    (isLocalMartingaleUpTo_iff_exists_stopped_martingale_approximation_continuousAdapted
      hM_adapted hM_cont).2 hStopped

/-- Auxiliary stronger bounded consequence: on a probability space, if `M` has continuous sample
paths, then a deterministic bounded stopped-martingale approximation still implies that `M` is a
local martingale up to `τ`. -/
theorem isLocalMartingaleUpTo_iff_exists_bounded_stopped_martingale_sequence
    (hM_adapted : Adapted ℱ M)
    (hM_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω)
    [IsProbabilityMeasure μ] :
    HasBoundedStoppedMartingaleApproximationUpTo ℱ μ τ M →
      IsLocalMartingaleUpTo ℱ μ τ M := by
  -- Route correction: the former converse statement was false for deterministic boundedness, so
  -- this legacy auxiliary owner is kept only as the truthful forward implication.
  exact isLocalMartingaleUpTo_of_exists_bounded_stopped_martingale_sequence hM_adapted hM_cont

/-- Source clause `(i) ↔ (iii)` from Remark 21.67: on a probability space, if `M` has
continuous sample paths, then being a local martingale up to the stopping time `τ` is equivalent
to admitting a sequence of stopping times increasing almost surely to `τ` such that every stopped
process `M^{τ_n}` is a bounded martingale in the source-faithful pathwise sense of
`HasPathwiseBoundedStoppedMartingaleApproximationUpTo`. -/
theorem isLocalMartingaleUpTo_iff_exists_pathwiseBounded_stopped_martingale_sequence
    (hM_adapted : Adapted ℱ M)
    (hM_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω)
    [IsProbabilityMeasure μ] :
    IsLocalMartingaleUpTo ℱ μ τ M ↔
      HasPathwiseBoundedStoppedMartingaleApproximationUpTo ℱ μ τ M := by
  constructor
  · intro hLocal
    have hApprox :
        HasStoppedMartingaleApproximationUpTo ℱ μ τ M :=
      (isLocalMartingaleUpTo_iff_exists_stopped_martingale_approximation_continuousAdapted
        hM_adapted hM_cont).1 hLocal
    exact pathwiseBoundedMartingaleApproximationFromStoppedApproximation
      hM_cont hApprox
  · rintro ⟨τSeq, hApprox, hMartBounded⟩
    have hStopped :
        HasStoppedMartingaleApproximationUpTo ℱ μ τ M :=
      ⟨τSeq, hApprox, fun n ↦ (hMartBounded n).1⟩
    exact (isLocalMartingaleUpTo_iff_exists_stopped_martingale_approximation_continuousAdapted
      hM_adapted hM_cont).2 hStopped

/-- Remark 21.67: on a probability space, for a continuous adapted process `M` and a stopping
time `τ`, the following are equivalent: `M` is a local martingale up to `τ`; `M` admits an almost
surely increasing sequence of stopping times converging to `τ` whose stopped processes are
martingales; and `M` admits such a sequence whose stopped processes are bounded martingales in the
source-faithful pathwise sense. -/
theorem isLocalMartingaleUpTo_remark_21_67_continuousAdapted
    [IsProbabilityMeasure μ]
    (hM_adapted : Adapted ℱ M)
    (hM_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω) :
    (IsLocalMartingaleUpTo ℱ μ τ M ↔ HasStoppedMartingaleApproximationUpTo ℱ μ τ M) ∧
      (IsLocalMartingaleUpTo ℱ μ τ M ↔
        HasPathwiseBoundedStoppedMartingaleApproximationUpTo ℱ μ τ M) := by
  -- Proof comment: Remark 21.67 is exactly the conjunction of the already separated clause
  -- `(i) ↔ (ii)` and clause `(i) ↔ (iii)` equivalences.
  refine ⟨?_, ?_⟩
  · exact isLocalMartingaleUpTo_iff_exists_stopped_martingale_approximation_continuousAdapted
      hM_adapted hM_cont
  · exact isLocalMartingaleUpTo_iff_exists_pathwiseBounded_stopped_martingale_sequence
      hM_adapted hM_cont

end ProbabilityTheory

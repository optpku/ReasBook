/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Martingale.Centering
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_1_3.StoppingApprox
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_1_3.StoppedProcess
import Books.ProbabilityTheory_Klenke_2020.Items.Chap04.Exercise_4_2_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Theorem_10_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Theorem_10_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Theorem_12_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_22

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u}
variable {E : Type v} [TopologicalSpace E]

variable [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω}
variable {ℱ : Filtration NNReal mΩ} [SigmaFiniteFiltration μ ℱ]
variable {X Y : NNReal → Ω → ℝ}

/-- Helper for this exercise: the `n`-th upper step index for the time `t`. -/
private def upperStepIndex (n : ℕ) (t : NNReal) : ℕ :=
  ⌈t * (n + 1 : NNReal)⌉₊

/-- Helper for this exercise: the `n`-th upper step time approximation of `t`. -/
private def upperStepTime (n : ℕ) (t : NNReal) : NNReal :=
  ((upperStepIndex n t : ℕ) : NNReal) / (n + 1)

/-- Helper for this exercise: the upper step approximation truncated at the horizon `T`. -/
private def upperStepTimeOn (T : NNReal) (n : ℕ) (t : NNReal) : NNReal :=
  min (upperStepTime n t) T

/-- Helper for this exercise: the upper step approximation stays to the right of `t`. -/
private lemma self_le_upperStepTime (n : ℕ) (t : NNReal) :
    t ≤ upperStepTime n t := by
  have hceil : t * (n + 1 : NNReal) ≤ (upperStepIndex n t : ℕ) := by
    simpa [upperStepIndex] using Nat.le_ceil (t * (n + 1 : NNReal))
  -- Proof comment: divide the ceiling inequality by the positive denominator `n + 1`.
  rw [upperStepTime]
  rw [le_div_iff₀]
  · simpa [mul_assoc] using hceil
  · exact Nat.cast_add_one_pos n

/-- Helper for this exercise: the upper step approximation overshoots by at most
`1 / (n + 1)`. -/
private lemma upperStepTime_le_add_inv (n : ℕ) (t : NNReal) :
    upperStepTime n t ≤ t + 1 / (n + 1 : NNReal) := by
  have hceil : (upperStepIndex n t : ℕ) ≤ t * (n + 1 : NNReal) + 1 := by
    simpa [upperStepIndex] using
      (Nat.ceil_lt_add_one (show 0 ≤ t * (n + 1 : NNReal) by positivity)).le
  -- Proof comment: divide the one-step ceiling bound by `n + 1`.
  rw [upperStepTime]
  rw [div_le_iff₀]
  · refine hceil.trans ?_
    rw [add_mul, div_eq_mul_inv, one_mul, inv_mul_cancel₀]
    exact Nat.cast_add_one_ne_zero n
  · exact Nat.cast_add_one_pos n

/-- Helper for this exercise: the upper step times converge down to `t`. -/
private lemma tendsto_upperStepTime (t : NNReal) :
    Tendsto (fun n ↦ upperStepTime n t) atTop (𝓝 t) := by
  have hupper : Tendsto (fun n : ℕ ↦ t + 1 / (n + 1 : NNReal)) atTop (𝓝 t) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ t) atTop (𝓝 t)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ ↦ (1 : NNReal) / (n + 1 : NNReal)) atTop (𝓝 0))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ t) atTop (𝓝 t)) hupper ?_ ?_
  · exact Filter.Eventually.of_forall fun n ↦ self_le_upperStepTime n t
  · exact Filter.Eventually.of_forall fun n ↦ upperStepTime_le_add_inv n t

/-- Helper for this exercise: on a fixed horizon strip, each upper-step approximation is jointly
measurable with respect to `ℱ T`. -/
private lemma upperStep_measurableOnStrip
    {X : NNReal → Ω → ℝ}
    (hX_adapted : Adapted ℱ X) (T : NNReal) (n : ℕ) :
    Measurable[Subtype.instMeasurableSpace.prod (ℱ T)] fun p : Set.Iic T × Ω ↦
      X (upperStepTimeOn T n p.1) p.2 := by
  letI : MeasurableSpace Ω := ℱ T
  let g : ℕ × Ω → ℝ := fun q ↦ X (min (((q.1 : ℕ) : NNReal) / (n + 1)) T) q.2
  have hg : Measurable g := by
    -- Proof comment: every slice only samples `X` at a deterministic time below `T`.
    refine measurable_from_prod_countable_right fun k ↦ ?_
    simpa [g] using
      hX_adapted.measurable_le (min_le_right (((k : ℕ) : NNReal) / (n + 1)) T)
  have hidx : Measurable fun p : Set.Iic T × Ω ↦ upperStepIndex n p.1 := by
    simpa [upperStepIndex] using
      ((measurable_fst.subtype_val.mul_const (n + 1 : NNReal)).nat_ceil :
        Measurable fun p : Set.Iic T × Ω ↦ ⌈((p.1 : NNReal) * (n + 1 : NNReal))⌉₊)
  have hmap : Measurable fun p : Set.Iic T × Ω ↦ (upperStepIndex n p.1, p.2) :=
    hidx.prodMk measurable_snd
  have hcomp :
      (fun p : Set.Iic T × Ω ↦ X (upperStepTimeOn T n p.1) p.2) =
        g ∘ fun p : Set.Iic T × Ω ↦ (upperStepIndex n p.1, p.2) := by
    rfl
  rw [hcomp]
  exact hg.comp hmap

/-- Helper for this exercise: on a fixed horizon strip, the upper-step approximations converge
pointwise to the original process. -/
private lemma upperStep_tendstoOnStrip
    {X : NNReal → Ω → ℝ}
    (hX_right_cont : ∀ (ω : Ω) (t : NNReal),
      ContinuousWithinAt (fun s : NNReal ↦ X s ω) (Set.Ici t) t)
    (T : NNReal) (p : Set.Iic T × Ω) :
    Tendsto (fun n ↦ X (upperStepTimeOn T n p.1) p.2) atTop (𝓝 (X p.1 p.2)) := by
  have htime_tendsto :
      Tendsto (fun n ↦ upperStepTimeOn T n p.1) atTop (𝓝 (p.1 : NNReal)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (p.1 : NNReal)) atTop (𝓝 (p.1 : NNReal)))
      (tendsto_upperStepTime p.1) ?_ ?_
    · exact Filter.Eventually.of_forall fun n ↦
        le_min (self_le_upperStepTime n p.1) p.1.2
    · exact Filter.Eventually.of_forall fun n ↦ min_le_left _ _
  have htime_within :
      Tendsto (fun n ↦ upperStepTimeOn T n p.1) atTop (𝓝[Set.Ici (p.1 : NNReal)] p.1) := by
    refine tendsto_inf.2 ⟨htime_tendsto, ?_⟩
    exact tendsto_principal.2 <| Filter.Eventually.of_forall fun n ↦
      le_min (self_le_upperStepTime n p.1) p.1.2
  -- Proof comment: compose right continuity of the sample path with the time approximation.
  exact (hX_right_cont p.2 p.1).tendsto.comp htime_within

/-- Helper for this exercise: an adapted right-continuous process is measurable on every finite
strip `Set.Iic T × Ω` with respect to the product `σ`-algebra
`Subtype.instMeasurableSpace.prod (ℱ T)`. -/
private lemma measurable_strip_of_adapted_rightContinuous
    {X : NNReal → Ω → ℝ}
    (hX_adapted : Adapted ℱ X)
    (hX_right_cont : ∀ (ω : Ω) (t : NNReal),
      ContinuousWithinAt (fun s : NNReal ↦ X s ω) (Set.Ici t) t)
    (T : NNReal) :
    Measurable[Subtype.instMeasurableSpace.prod (ℱ T)] fun p : Set.Iic T × Ω ↦ X p.1 p.2 := by
  letI : MeasurableSpace (Set.Iic T × Ω) := Subtype.instMeasurableSpace.prod (ℱ T)
  let approx : ℕ → Set.Iic T × Ω → ℝ := fun n p ↦ X (upperStepTimeOn T n p.1) p.2
  -- Proof comment: the strip map is the pointwise limit of the measurable upper-step
  -- approximations built above.
  refine measurable_of_tendsto_metrizable
    (fun n ↦ by
      simpa using
        (upperStep_measurableOnStrip hX_adapted T n :
          Measurable[Subtype.instMeasurableSpace.prod (ℱ T)] (approx n)))
    ?_
  rw [tendsto_pi_nhds]
  intro p
  simpa using upperStep_tendstoOnStrip hX_right_cont T p

/-- Helper for this exercise: an adapted right-continuous process is progressively measurable. -/
private theorem progMeasurable_of_adaptedRightContinuous
    {X : NNReal → Ω → ℝ}
    (hX_adapted : Adapted ℱ X)
    (hX_right_cont : ∀ (ω : Ω) (t : NNReal),
      ContinuousWithinAt (fun s : NNReal ↦ X s ω) (Set.Ici t) t) :
    ProgMeasurable ℱ X := by
  intro T
  -- Proof comment: progressive measurability is exactly strip measurability on every finite
  -- horizon.
  exact Measurable.stronglyMeasurable <|
    measurable_strip_of_adapted_rightContinuous hX_adapted hX_right_cont T

/-- Helper for this exercise: evaluating an adapted right-continuous process at a finite stopping
time is measurable with respect to the stopping-time `σ`-algebra. -/
private theorem measurableStoppedValue_of_adaptedRightContinuous
    {X : NNReal → Ω → ℝ} {τ : Ω → NNReal}
    (hX_adapted : Adapted ℱ X)
    (hX_right_cont : ∀ (ω : Ω) (t : NNReal),
      ContinuousWithinAt (fun s : NNReal ↦ X s ω) (Set.Ici t) t)
    (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal)) :
    Measurable[hτ.measurableSpace] (fun ω ↦ X (τ ω) ω) := by
  -- Proof comment: rewrite the evaluation at `τ` as a stopped value and invoke the canonical
  -- stopped-value measurability theorem for progressively measurable processes.
  simpa [stoppedValue] using
    measurable_stoppedValue (progMeasurable_of_adaptedRightContinuous hX_adapted hX_right_cont) hτ


-- Reuse the item-local dyadic stopping-time approximation API from `StoppingApprox`.

/-- Helper for this exercise: right continuity transports right-sided time approximations to the
corresponding stopped values. -/
private lemma stoppedValue_tendsto_of_rightTimeApprox
    {X : NNReal → Ω → ℝ} (hX_right_cont : HasRightContinuousPaths X)
    {ρn : ℕ → Ω → NNReal} {ρ : Ω → NNReal}
    (hρ_le : ∀ n ω, ρ ω ≤ ρn n ω)
    (hρ_tendsto : ∀ ω, Tendsto (fun n ↦ ρn n ω) atTop (𝓝 (ρ ω))) :
    ∀ ω,
      Tendsto
        (fun n ↦ stoppedValue X (fun ω' ↦ (ρn n ω' : ENNReal)) ω)
        atTop
        (𝓝 (stoppedValue X (fun ω' ↦ (ρ ω' : ENNReal)) ω)) := by
  intro ω
  have hWithin :
      Tendsto (fun n ↦ ρn n ω) atTop (𝓝[Set.Ici (ρ ω)] (ρ ω)) := by
    refine tendsto_inf.2 ⟨hρ_tendsto ω, ?_⟩
    exact tendsto_principal.2 <| Filter.Eventually.of_forall fun n ↦ hρ_le n ω
  -- Proof comment: right continuity is exactly continuity within `Set.Ici (ρ ω)`, so composing
  -- with the approximating times gives the stopped-value limit.
  simpa [stoppedValue] using (hX_right_cont ω (ρ ω)).tendsto.comp hWithin

/-- Helper for Exercise 21.1.3: a deterministic bound for the larger stopping time `τ` also bounds
the smaller stopping time `σ` whenever `σ ≤ τ`. -/
private lemma exists_bound_of_le_of_exists_bound
    {σ τ : Ω → NNReal} (hστ : σ ≤ τ)
    (hτ_bdd : ∃ T : NNReal, ∀ ω, τ ω ≤ T) :
    ∃ T : NNReal, ∀ ω, σ ω ≤ T := by
  rcases hτ_bdd with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  intro ω
  exact (hστ ω).trans (hT ω)

/-- Helper for Exercise 21.1.3: one bounded horizon controls every dyadic ceiling approximation
of a stopping time after enlarging the horizon by `1`. -/
private lemma exists_uniform_bound_dyadicCeilApprox
    {τ : Ω → NNReal} (hτ_bdd : ∃ T : NNReal, ∀ ω, τ ω ≤ T) :
    ∃ T : NNReal, ∀ n ω, dyadicCeilApprox n τ ω ≤ T := by
  rcases hτ_bdd with ⟨T, hT⟩
  refine ⟨T + 1, ?_⟩
  intro n ω
  have hmesh_le_one : ((2 : NNReal) ^ n)⁻¹ ≤ 1 := by
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (show (1 : NNReal) ≤ 2 by norm_num))
  -- Proof comment: each dyadic ceiling overshoots the original bound by at most one mesh size,
  -- and every dyadic mesh is at most `1`.
  calc
    dyadicCeilApprox n τ ω ≤ T + ((2 : NNReal) ^ n)⁻¹ :=
      dyadicCeilApprox_le_add_mesh n hT ω
    _ ≤ T + 1 := by gcongr

/-- Helper for this exercise: truncating a finite stopping time by deterministic constants is
eventually constant pointwise, hence the corresponding stopped values converge. -/
private lemma stoppedValue_min_const_tendsto_of_finiteStoppingTime
    {X : NNReal → Ω → ℝ} {ρ : Ω → NNReal} :
    ∀ ω,
      Tendsto
        (fun n : ℕ ↦ stoppedValue X (fun ω' ↦ min (ρ ω' : ENNReal) (n : ENNReal)) ω)
        atTop
        (𝓝 (stoppedValue X (fun ω' ↦ (ρ ω' : ENNReal)) ω)) := by
  intro ω
  have hEventually :
      ∀ᶠ n : ℕ in atTop,
        stoppedValue X (fun ω' ↦ min (ρ ω' : ENNReal) (n : ENNReal)) ω =
          stoppedValue X (fun ω' ↦ (ρ ω' : ENNReal)) ω := by
    filter_upwards [show ∀ᶠ n : ℕ in atTop, Nat.ceil (ρ ω : ℝ) ≤ n from
      Filter.eventually_ge_atTop (Nat.ceil (ρ ω : ℝ))] with n hn
    have hρ_le_n_real : (ρ ω : ℝ) ≤ n := by
      exact le_trans (Nat.le_ceil (ρ ω : ℝ)) (by exact_mod_cast hn)
    have hρ_le_n : (ρ ω : ENNReal) ≤ (n : ENNReal) := by
      exact_mod_cast hρ_le_n_real
    -- Proof comment: once `n` dominates the finite time `ρ(ω)`, the truncation `ρ ∧ n` equals
    -- `ρ` at that sample point.
    have hmin : min (ρ ω : ENNReal) (n : ENNReal) = (ρ ω : ENNReal) := min_eq_left hρ_le_n
    calc
      stoppedValue X (fun ω' ↦ min (ρ ω' : ENNReal) (n : ENNReal)) ω
          = X (min (ρ ω : ENNReal) (n : ENNReal)).untopA ω := by
              rfl
      _ = X ((ρ ω : ENNReal).untopA) ω := by rw [hmin]
      _ = stoppedValue X (fun ω' ↦ (ρ ω' : ENNReal)) ω := by
            rfl
  have hEq :
      (fun n : ℕ ↦ stoppedValue X (fun ω' ↦ min (ρ ω' : ENNReal) (n : ENNReal)) ω) =ᶠ[atTop]
        (fun _ : ℕ ↦ stoppedValue X (fun ω' ↦ (ρ ω' : ENNReal)) ω) := hEventually
  exact Tendsto.congr' hEq.symm tendsto_const_nhds

/-- Helper for Exercise 21.1.3: a dyadic ceiling approximation of a bounded stopping time takes
only finitely many deterministic values, so the corresponding stopped value is integrable. -/
private lemma integrable_stoppedValue_dyadicCeilApprox
    {X : NNReal → Ω → ℝ} (hX : Supermartingale X ℱ μ)
    {τ : Ω → NNReal} (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal))
    (m : ℕ) (hτ_bdd : ∃ T : NNReal, ∀ ω, τ ω ≤ T) :
    Integrable (stoppedValue X (fun ω ↦ (dyadicCeilApprox m τ ω : ENNReal))) μ := by
  obtain ⟨T, hT⟩ := hτ_bdd
  let c : NNReal := (2 : NNReal) ^ m
  let K : ℕ := Nat.ceil (((c * T : NNReal) : ℝ)) + 1
  let s : Finset NNReal := (Finset.range K).image fun k : ℕ ↦ ((k : NNReal) / c)
  have hs :
      ∀ ω,
        (fun ω' ↦ (dyadicCeilApprox m τ ω' : ENNReal)) ω ∈
          (WithTop.some '' (s : Set NNReal)) := by
    intro ω
    have hcτ_le :
        (((c * τ ω : NNReal) : ℝ)) ≤ (((c * T : NNReal) : ℝ)) := by
      exact_mod_cast (mul_le_mul_left' (hT ω) c)
    have hceil_le :
        Nat.ceil (((c * τ ω : NNReal) : ℝ)) ≤ Nat.ceil (((c * T : NNReal) : ℝ)) := by
      exact Nat.ceil_le.2 (hcτ_le.trans (Nat.le_ceil _))
    have hmem_range : Nat.ceil (((c * τ ω : NNReal) : ℝ)) ∈ Finset.range K := by
      refine Finset.mem_range.2 ?_
      exact lt_of_le_of_lt hceil_le (Nat.lt_succ_self _)
    refine ⟨((Nat.ceil (((c * τ ω : NNReal) : ℝ)) : ℕ) : NNReal) / c, ?_⟩
    refine ⟨Finset.mem_image.2 ⟨_, hmem_range, rfl⟩, ?_⟩
    simp [c, dyadicCeilApprox]
  -- Proof comment: the dyadic ceiling stop only visits a finite deterministic grid below the
  -- bounded horizon, so `integrable_stoppedValue_of_mem_finset` applies directly.
  exact
    integrable_stoppedValue_of_mem_finset
      (dyadicCeilApprox_isStoppingTime hτ m) hX.integrable hs

/-- Helper for Exercise 21.1.3: sampling the continuous-time filtration along a monotone
deterministic time grid produces a discrete filtration. -/
private def sampledFiltration (τ : ℕ → NNReal) (hτ : Monotone τ) :
    Filtration ℕ mΩ :=
  Filtration.mk (fun n ↦ ℱ (τ n))
    (fun _ _ hij ↦ ℱ.mono (hτ hij))
    (fun n ↦ ℱ.le (τ n))

/-- Helper for Exercise 21.1.3: the sampled filtration inherits sigma-finiteness from the ambient
filtration. -/
private instance sampledFiltration_sigmaFinite
    (τ : ℕ → NNReal) (hτ : Monotone τ) :
    SigmaFiniteFiltration μ (sampledFiltration (ℱ := ℱ) τ hτ) where
  SigmaFinite n := by
    -- Proof comment: the sampled stage at `n` is literally the ambient stage `ℱ (τ n)`.
    simpa [sampledFiltration] using
      (inferInstance : SigmaFinite (μ.trim (ℱ.le (τ n))))

/-- Helper for Exercise 21.1.3: a supermartingale stays a supermartingale after monotone
deterministic sampling. -/
private theorem sampledSupermartingaleOfMonotone
    {X : NNReal → Ω → ℝ} (hX : Supermartingale X ℱ μ)
    {τ : ℕ → NNReal} (hτ : Monotone τ) :
    Supermartingale (fun n ω ↦ X (τ n) ω) (sampledFiltration (ℱ := ℱ) τ hτ) μ := by
  refine ⟨?_, ?_, ?_⟩
  · -- Proof comment: each sampled time uses the same measurable slice as the ambient process.
    intro n
    simpa [sampledFiltration] using hX.1 (τ n)
  · -- Proof comment: the supermartingale conditional-expectation inequality is stable under the
    -- monotone deterministic reindexing.
    intro i j hij
    simpa [sampledFiltration] using hX.2.1 (τ i) (τ j) (hτ hij)
  · -- Proof comment: integrability is inherited termwise from the ambient supermartingale.
    intro n
    exact hX.2.2 (τ n)

/-- Helper for Exercise 21.1.3: the `n`-th dyadic time grid has mesh `2^{-n}`. -/
private noncomputable def dyadicTime (n k : ℕ) : NNReal :=
  (k : NNReal) / (2 : NNReal) ^ n

/-- Helper for Exercise 21.1.3: each dyadic row is monotone in the discrete index. -/
private theorem monotone_dyadicTime (n : ℕ) :
    Monotone (dyadicTime n) := by
  intro i j hij
  have hcast : (i : NNReal) ≤ j := by
    exact_mod_cast hij
  have hnonneg : 0 ≤ ((2 : NNReal) ^ n)⁻¹ := by
    exact inv_nonneg.mpr (pow_nonneg (show (0 : NNReal) ≤ 2 by positivity) _)
  -- Proof comment: divide the monotone numerator by the fixed positive dyadic denominator.
  simpa [dyadicTime, div_eq_mul_inv] using mul_le_mul_of_nonneg_right hcast hnonneg

/-- Helper for Exercise 21.1.3: the `n`-th dyadic sampled process. -/
private noncomputable def dyadicRowProcess
    (X : NNReal → Ω → ℝ) (n : ℕ) : ℕ → Ω → ℝ :=
  fun k ω ↦ X (dyadicTime n k) ω

/-- Helper for Exercise 21.1.3: the discrete filtration attached to the `n`-th dyadic row. -/
private noncomputable def dyadicRowFiltration
    (ℱ : Filtration NNReal mΩ) (n : ℕ) : Filtration ℕ mΩ :=
  sampledFiltration (ℱ := ℱ) (dyadicTime n) (monotone_dyadicTime n)

/-- Helper for Exercise 21.1.3: each dyadic sampled row of a supermartingale is a discrete
supermartingale. -/
private theorem dyadicRow_supermartingale
    {X : NNReal → Ω → ℝ} (hX : Supermartingale X ℱ μ) (n : ℕ) :
    Supermartingale (dyadicRowProcess X n) (dyadicRowFiltration (ℱ := ℱ) n) μ := by
  -- Proof comment: this is the monotone-sampling theorem specialized to the dyadic grid.
  simpa [dyadicRowProcess, dyadicRowFiltration] using
    sampledSupermartingaleOfMonotone (ℱ := ℱ) (μ := μ) (X := X) hX
      (τ := dyadicTime n) (hτ := monotone_dyadicTime n)

/-- Helper for Exercise 21.1.3: the discrete dyadic stop is the ceiling index on the dyadic row.
-/
private noncomputable def dyadicCeilIndex (n : ℕ) (σ : Ω → NNReal) : Ω → ℕ∞ :=
  fun ω ↦ (Nat.ceil (((((2 : NNReal) ^ n) * σ ω : NNReal) : ℝ)) : ℕ∞)

/-- Helper for Exercise 21.1.3: the dyadic ceiling index stops exactly when the original stopping
time is below the corresponding dyadic mesh point. -/
private lemma dyadicCeilIndex_event_le
    {σ : Ω → NNReal} (n k : ℕ) :
    {ω | dyadicCeilIndex n σ ω ≤ k} = {ω | (σ ω : ENNReal) ≤ dyadicTime n k} := by
  ext ω
  have hpow_pos : 0 < (2 : NNReal) ^ n := by
    positivity
  constructor
  · intro hω
    have hceil_nat :
        Nat.ceil (((((2 : NNReal) ^ n) * σ ω : NNReal) : ℝ)) ≤ k := by
      simpa [dyadicCeilIndex] using hω
    have hreal :
        ((((2 : NNReal) ^ n) * σ ω : NNReal) : ℝ) ≤ k := by
      exact Nat.ceil_le.mp hceil_nat
    have hnn :
        (2 : NNReal) ^ n * σ ω ≤ k := by
      exact_mod_cast hreal
    have hdiv : σ ω ≤ dyadicTime n k := by
      rw [dyadicTime]
      exact (le_div_iff₀ hpow_pos).2 (by simpa [mul_comm] using hnn)
    exact_mod_cast hdiv
  · intro hω
    have hdiv : σ ω ≤ dyadicTime n k := by
      exact ENNReal.coe_le_coe.mp hω
    have hnn :
        (2 : NNReal) ^ n * σ ω ≤ k := by
      rw [dyadicTime] at hdiv
      simpa [mul_comm] using (le_div_iff₀ hpow_pos).1 (by simpa using hdiv)
    have hreal :
        ((((2 : NNReal) ^ n) * σ ω : NNReal) : ℝ) ≤ k := by
      exact_mod_cast hnn
    have hceil_nat :
        Nat.ceil (((((2 : NNReal) ^ n) * σ ω : NNReal) : ℝ)) ≤ k :=
      Nat.ceil_le.mpr hreal
    simpa [dyadicCeilIndex] using hceil_nat

/-- Helper for Exercise 21.1.3: the dyadic ceiling index is a stopping time for the sampled
dyadic-row filtration. -/
private lemma dyadicCeilIndex_isStoppingTime
    {σ : Ω → NNReal}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal)) (n : ℕ) :
    IsStoppingTime (dyadicRowFiltration (ℱ := ℱ) n) (dyadicCeilIndex n σ) := by
  intro k
  -- Proof comment: the discrete stopping event is exactly the ambient stopping event
  -- `{σ ≤ k / 2^n}` viewed at the sampled filtration time `dyadicTime n k`.
  convert hσ.measurableSet_le (dyadicTime n k) using 1
  exact dyadicCeilIndex_event_le (σ := σ) n k

/-- Helper for Exercise 21.1.3: the stopping-time `σ`-algebra of the dyadic ceiling index on the
sampled dyadic row agrees with the stopping-time `σ`-algebra of the ambient dyadic ceiling
approximation. -/
private lemma dyadicCeilIndex_measurableSpace_eq
    {σ : Ω → NNReal}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal)) (n : ℕ) :
    (dyadicCeilIndex_isStoppingTime (ℱ := ℱ) hσ n).measurableSpace =
      (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace := by
  ext s
  rw [IsStoppingTime.measurableSet, IsStoppingTime.measurableSet]
  constructor
  · intro hs
    refine ⟨hs.1, ?_⟩
    intro t
    let k : ℕ := Nat.floor ((((2 : NNReal) ^ n) * t : NNReal) : ℝ)
    have hs_stage :
        MeasurableSet[ℱ (dyadicTime n k)] (s ∩ {ω | dyadicCeilIndex n σ ω ≤ k}) := by
      simpa [dyadicRowFiltration, sampledFiltration] using hs.2 k
    have hEvent :
        {ω | (dyadicCeilApprox n σ ω : ENNReal) ≤ t} =
          {ω | dyadicCeilIndex n σ ω ≤ k} := by
      calc
        {ω | (dyadicCeilApprox n σ ω : ENNReal) ≤ t}
            = {ω | (σ ω : ENNReal) ≤ dyadicTime n k} := by
                simpa [k, dyadicTime] using dyadicCeilApprox_event_le_eq n σ t
        _ = {ω | dyadicCeilIndex n σ ω ≤ k} := (dyadicCeilIndex_event_le (σ := σ) n k).symm
    have hk_le_t : dyadicTime n k ≤ t := by
      have hpow_pos : 0 < (2 : NNReal) ^ n := by
        positivity
      rw [dyadicTime]
      refine (div_le_iff₀ hpow_pos).2 ?_
      have hfloor :
          ((Nat.floor ((((2 : NNReal) ^ n) * t : NNReal) : ℝ) : ℕ) : ℝ) ≤
            ((((2 : NNReal) ^ n) * t : NNReal) : ℝ) := by
        exact Nat.floor_le (show 0 ≤ ((((2 : NNReal) ^ n) * t : NNReal) : ℝ) by positivity)
      have hfloor_nnreal :
          (((Nat.floor ((((2 : NNReal) ^ n) * t : NNReal) : ℝ) : ℕ) : NNReal) ≤
            (2 : NNReal) ^ n * t) := by
        exact_mod_cast hfloor
      simpa [k, mul_comm] using hfloor_nnreal
    have hs_event :
        MeasurableSet[ℱ (dyadicTime n k)] (s ∩ {ω | (dyadicCeilApprox n σ ω : ENNReal) ≤ t}) := by
      convert hs_stage using 1
      ext ω
      simpa [Set.mem_inter_iff] using
        congrArg (fun u : Set Ω ↦ ω ∈ s ∩ u) hEvent
    exact ℱ.mono hk_le_t _ hs_event
  · intro hs
    refine ⟨hs.1, ?_⟩
    intro k
    have hs_stage :
        MeasurableSet[ℱ (dyadicTime n k)]
          (s ∩ {ω | (dyadicCeilApprox n σ ω : ENNReal) ≤ dyadicTime n k}) := by
      exact hs.2 (dyadicTime n k)
    have hmul :
        ((2 : NNReal) ^ n) * dyadicTime n k = k := by
      have hpow_ne : ((2 : NNReal) ^ n) ≠ 0 := by
        positivity
      rw [dyadicTime, div_eq_mul_inv]
      calc
        ((2 : NNReal) ^ n) * ((k : NNReal) * ((2 : NNReal) ^ n)⁻¹)
            = (k : NNReal) * (((2 : NNReal) ^ n) * ((2 : NNReal) ^ n)⁻¹) := by
                ac_rfl
        _ = (k : NNReal) * 1 := by rw [mul_inv_cancel₀ hpow_ne]
        _ = k := by simp
    have hfloor :
        Nat.floor ((((2 : NNReal) ^ n) * dyadicTime n k : NNReal) : ℝ) = k := by
      rw [hmul]
      simpa using Nat.floor_natCast k
    have hEvent :
        {ω | (dyadicCeilApprox n σ ω : ENNReal) ≤ dyadicTime n k} =
          {ω | dyadicCeilIndex n σ ω ≤ k} := by
      ext ω
      change ((dyadicCeilApprox n σ ω : ENNReal) ≤ dyadicTime n k ↔ dyadicCeilIndex n σ ω ≤ k)
      have hApprox :
          ((dyadicCeilApprox n σ ω : ENNReal) ≤ dyadicTime n k) ↔
            (σ ω : ENNReal) ≤
              (((Nat.floor ((((2 : NNReal) ^ n) * dyadicTime n k : NNReal) : ℝ) : ℕ) : NNReal) /
                (2 : NNReal) ^ n) := by
        simpa [Set.mem_setOf_eq] using
          congrFun (dyadicCeilApprox_event_le_eq n σ (dyadicTime n k)) ω
      have hIndex :
          (dyadicCeilIndex n σ ω ≤ k) ↔ (σ ω : ENNReal) ≤ dyadicTime n k := by
        simpa [Set.mem_setOf_eq] using
          congrFun (dyadicCeilIndex_event_le (σ := σ) n k) ω
      calc
        ((dyadicCeilApprox n σ ω : ENNReal) ≤ dyadicTime n k)
            ↔
              (σ ω : ENNReal) ≤
                (((Nat.floor ((((2 : NNReal) ^ n) * dyadicTime n k : NNReal) : ℝ) : ℕ) : NNReal) /
                  (2 : NNReal) ^ n) := hApprox
        _ ↔ (σ ω : ENNReal) ≤ dyadicTime n k := by
              rw [hfloor]
              simp [dyadicTime]
        _ ↔ dyadicCeilIndex n σ ω ≤ k := hIndex.symm
    have hs_index :
        MeasurableSet[ℱ (dyadicTime n k)] (s ∩ {ω | dyadicCeilIndex n σ ω ≤ k}) := by
      convert hs_stage using 1
      ext ω
      simpa [Set.mem_inter_iff] using
        (congrArg (fun u : Set Ω ↦ ω ∈ s ∩ u) hEvent).symm
    simpa [dyadicRowFiltration, sampledFiltration] using hs_index

/-- Helper for Exercise 21.1.3: a deterministic natural horizon for `σ` induces a deterministic
natural horizon for the dyadic ceiling index. -/
private lemma dyadicCeilIndex_le_of_natBound
    {σ : Ω → NNReal} (n N : ℕ)
    (hσ_le : ∀ ω, σ ω ≤ (N : NNReal)) :
    ∀ ω, dyadicCeilIndex n σ ω ≤ 2 ^ n * N := by
  intro ω
  have hmul :
      (2 : NNReal) ^ n * σ ω ≤ 2 ^ n * N := by
    gcongr
    exact hσ_le ω
  have hreal :
      ((((2 : NNReal) ^ n) * σ ω : NNReal) : ℝ) ≤ (2 ^ n * N : ℕ) := by
    exact_mod_cast hmul
  have hceil_nat :
      Nat.ceil (((((2 : NNReal) ^ n) * σ ω : NNReal) : ℝ)) ≤ 2 ^ n * N :=
    Nat.ceil_le.mpr hreal
  change (Nat.ceil (((((2 : NNReal) ^ n) * σ ω : NNReal) : ℝ)) : ℕ∞) ≤ 2 ^ n * N
  exact_mod_cast hceil_nat

/-- Helper for Exercise 21.1.3: stopping the dyadic sampled row at the dyadic ceiling index
rewrites to the ambient stopped value at `dyadicCeilApprox`. -/
private lemma dyadicRow_stoppedValue_eq_dyadicCeilApprox
    {X : NNReal → Ω → ℝ} (n : ℕ) (σ : Ω → NNReal) :
    stoppedValue (dyadicRowProcess X n) (dyadicCeilIndex n σ) =
      stoppedValue X (fun ω ↦ (dyadicCeilApprox n σ ω : ENNReal)) := by
  ext ω
  have htime :
      ((((dyadicCeilApprox n σ ω : NNReal) : ENNReal)).untopA : NNReal) =
        dyadicCeilApprox n σ ω := by
    have hne : ((dyadicCeilApprox n σ ω : NNReal) : ENNReal) ≠ ∞ := by simp
    rw [WithTop.untopA_eq_untop hne]
    exact ENNReal.coe_inj.mp (WithTop.coe_untop _ hne)
  -- Proof comment: both stopped values evaluate `X` at the same dyadic ceiling time
  -- `ceil(2^n σ(ω)) / 2^n`; only the discrete versus continuous packaging differs.
  rw [stoppedValue, stoppedValue, htime]
  simp [dyadicRowProcess, dyadicCeilIndex, dyadicTime, dyadicCeilApprox]

/-- Helper for this exercise: bounded stopping-time expectation identities imply the
deterministic-time set-integral equalities needed to reconstruct a martingale. -/
private lemma setIntegralEq_ofExpectedStoppedValueEqInitial_piecewise
    {Z : NNReal → Ω → ℝ}
    (hZ_int : ∀ t : NNReal, Integrable (Z t) μ)
    (hstop : ∀ τ : Ω → NNReal, IsStoppingTime ℱ (fun ω ↦ (τ ω : ENNReal)) →
      (∃ T : NNReal, ∀ ω, τ ω ≤ T) →
        μ[stoppedValue Z (fun ω ↦ (τ ω : ENNReal))] = μ[Z 0])
    {s t : NNReal} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    ∫ ω in A, Z s ω ∂μ = ∫ ω in A, Z t ω ∂μ := by
  classical
  let τA : Ω → NNReal := A.piecewise (fun _ ↦ s) (fun _ ↦ t)
  have hτA_coe :
      (fun ω ↦ (τA ω : ENNReal)) =
        A.piecewise (fun _ ↦ (s : ENNReal)) (fun _ ↦ (t : ENNReal)) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [τA, hω]
  have hτA : IsStoppingTime ℱ fun ω ↦ (τA ω : ENNReal) := by
    rw [hτA_coe]
    exact isStoppingTime_piecewise_const hst hA
  have hτA_bdd : ∃ T : NNReal, ∀ ω, τA ω ≤ T := by
    refine ⟨t, ?_⟩
    intro ω
    by_cases hω : ω ∈ A
    · simpa [τA, hω] using hst
    · simp [τA, hω]
  have hτA_eq : μ[stoppedValue Z (fun ω ↦ (τA ω : ENNReal))] = μ[Z 0] :=
    hstop τA hτA hτA_bdd
  have ht_eq : μ[Z t] = μ[Z 0] := by
    -- Proof comment: the constant stopping time at `t` is the deterministic-time instance of the
    -- same bounded stopping identity.
    simpa [stoppedValue_const] using
      hstop (fun _ ↦ t) (isStoppingTime_const ℱ t) ⟨t, fun _ ↦ le_rfl⟩
  have hA_mΩ : MeasurableSet A := (ℱ.le s) _ hA
  have hStoppedPiecewise :
      stoppedValue Z (A.piecewise (fun _ ↦ (s : ENNReal)) fun _ ↦ (t : ENNReal)) =
        A.piecewise (Z s) (Z t) :=
    stoppedValue_piecewise_const
  have hPiecewise :
      μ[stoppedValue Z (fun ω ↦ (τA ω : ENNReal))] =
        ∫ ω in A, Z s ω ∂μ + ∫ ω in Aᶜ, Z t ω ∂μ := by
    -- Proof comment: the piecewise stopping time samples `Z` at `s` on `A` and at `t` on `Aᶜ`.
    have hτA_fun :
        stoppedValue Z (fun ω ↦ (τA ω : ENNReal)) =
          stoppedValue Z (A.piecewise (fun _ ↦ (s : ENNReal)) fun _ ↦ (t : ENNReal)) :=
      congrArg (fun τ : Ω → ENNReal ↦ stoppedValue Z τ) hτA_coe
    have hτA_int :
        μ[stoppedValue Z (fun ω ↦ (τA ω : ENNReal))] =
          ∫ x, stoppedValue Z
            (A.piecewise (fun _ ↦ (s : ENNReal)) fun _ ↦ (t : ENNReal)) x ∂μ := by
      simpa using congrArg (fun f : Ω → ℝ ↦ ∫ x, f x ∂μ) hτA_fun
    have hStopped_int :
        ∫ x,
            stoppedValue Z
              (A.piecewise (fun _ ↦ (s : ENNReal)) fun _ ↦ (t : ENNReal)) x ∂μ =
          ∫ x, A.piecewise (Z s) (Z t) x ∂μ := by
      simpa using congrArg (fun f : Ω → ℝ ↦ ∫ x, f x ∂μ) hStoppedPiecewise
    calc
      μ[stoppedValue Z (fun ω ↦ (τA ω : ENNReal))]
          = ∫ x,
              stoppedValue Z
                (A.piecewise (fun _ ↦ (s : ENNReal)) fun _ ↦ (t : ENNReal)) x ∂μ :=
            hτA_int
      _ = ∫ x, A.piecewise (Z s) (Z t) x ∂μ := hStopped_int
      _ = ∫ ω in A, Z s ω ∂μ + ∫ ω in Aᶜ, Z t ω ∂μ := by
            simpa using
              (integral_piecewise hA_mΩ (hZ_int s).integrableOn (hZ_int t).integrableOn :
                ∫ x, A.piecewise (Z s) (Z t) x ∂μ =
                  ∫ ω in A, Z s ω ∂μ + ∫ ω in Aᶜ, Z t ω ∂μ)
  have ht_split :
      μ[Z t] = ∫ ω in A, Z t ω ∂μ + ∫ ω in Aᶜ, Z t ω ∂μ := by
    simpa [setIntegral_univ] using (integral_add_compl hA_mΩ (hZ_int t)).symm
  -- Proof comment: compare the piecewise stopping identity with the deterministic-time identity
  -- at `t` and cancel the common complement term.
  linarith

/-- Helper for this exercise: bounded stopping-time expectation identities characterize
martingales via the deterministic-time set-integral criterion. -/
private lemma martingale_of_expectedStoppedValueEqInitial_piecewise
    {Z : NNReal → Ω → ℝ}
    (hZ_adapted : Adapted ℱ Z)
    (hZ_int : ∀ t : NNReal, Integrable (Z t) μ)
    (hstop : ∀ τ : Ω → NNReal, IsStoppingTime ℱ (fun ω ↦ (τ ω : ENNReal)) →
      (∃ T : NNReal, ∀ ω, τ ω ≤ T) →
        μ[stoppedValue Z (fun ω ↦ (τ ω : ENNReal))] = μ[Z 0]) :
    Martingale Z ℱ μ := by
  refine ⟨hZ_adapted.stronglyAdapted, ?_⟩
  intro s t hst
  -- Proof comment: identify `Z s` as the conditional expectation of `Z t` by checking equality
  -- of restricted integrals on every `ℱ s`-measurable event.
  exact
    (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) (hZ_int t)
      (fun u _ _ ↦ (hZ_int s).integrableOn)
      (fun u hu _ ↦
        setIntegralEq_ofExpectedStoppedValueEqInitial_piecewise hZ_int hstop hst hu)
      ((hZ_adapted.stronglyAdapted s).aestronglyMeasurable)).symm

/-- Helper for this exercise: for bounded stopping times `σ ≤ τ`, the dyadic conditional
expectations of `X_{τ^m}` converge almost surely to the conditional expectation with respect to
`𝓕_σ` under a right-continuous filtration. -/
private theorem dyadic_condexp_tendsto_ae [Filtration.IsRightContinuous ℱ] :
    ∀ {X : NNReal → Ω → ℝ}
      (_ : Supermartingale X ℱ μ) (_ : HasRightContinuousPaths X)
      {σ τ : Ω → NNReal}
      (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
      (_ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal))
      (_ : σ ≤ τ)
      (_ : ∃ T : NNReal, ∀ ω, σ ω ≤ T)
      (_ : ∃ T : NNReal, ∀ ω, τ ω ≤ T),
      ∀ m : ℕ,
        ∀ᵐ ω ∂μ,
          Tendsto
            (fun n ↦
              μ[stoppedValue X (fun ω' ↦ (dyadicCeilApprox m τ ω' : ENNReal)) |
                (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace] ω)
            atTop
            (𝓝
              (μ[stoppedValue X (fun ω' ↦ (dyadicCeilApprox m τ ω' : ENNReal)) |
                hσ.measurableSpace] ω)) := by
  intro X hX _hXrc σ τ hσ hτ _hστ _hσ_bdd hτ_bdd m
  have hInt :
      Integrable (stoppedValue X (fun ω' ↦ (dyadicCeilApprox m τ ω' : ENNReal))) μ :=
    integrable_stoppedValue_dyadicCeilApprox hX hτ m hτ_bdd
  let g : Ω → ℝ :=
    stoppedValue X (fun ω' ↦ (dyadicCeilApprox m τ ω' : ENNReal))
  let mn : ℕ → MeasurableSpace Ω :=
    fun n ↦ (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace
  have hmn_le : ∀ n, mn n ≤ mΩ := by
    intro n
    exact (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace_le
  have hmn_anti : Antitone mn := by
    simpa [mn] using
      (dyadicCeilApprox_measurableSpace_antitone hσ)
  have hiInf : (⨅ n : ℕ, mn n) = hσ.measurableSpace := by
    simpa [mn] using
      (dyadicCeilApprox_measurableSpace_iInf_eq hσ)
  let S :
      (μ.trim hσ.measurableSpace_le).FiniteSpanningSetsIn
        {s | MeasurableSet[hσ.measurableSpace] s} :=
    (μ.trim hσ.measurableSpace_le).toFiniteSpanningSetsIn
  have hPiece :
      ∀ k : ℕ,
        ∀ᵐ ω ∂μ.restrict (S.set k),
          Tendsto
            (fun n ↦ μ[g | mn n] ω)
            atTop
            (𝓝 (μ[g | hσ.measurableSpace] ω)) := by
    intro k
    let s : Set Ω := S.set k
    have hs_hσ : MeasurableSet[hσ.measurableSpace] s := S.set_mem k
    have hs : MeasurableSet s := hσ.measurableSpace_le _ hs_hσ
    have hs_fin : μ s < ∞ := by
      simpa [s, trim_measurableSet_eq hσ.measurableSpace_le hs_hσ] using S.finite k
    haveI : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs_fin.ne
    have hs_mn : ∀ n, MeasurableSet[mn n] s := by
      intro n
      have hσ_le_mn : hσ.measurableSpace ≤ mn n := by
        rw [← hiInf]
        exact iInf_le mn n
      exact hσ_le_mn _ hs_hσ
    have hInt_restrict : Integrable g (μ.restrict s) := hInt.restrict
    have hRestrictStage :
        ∀ n, (μ.restrict s)[g | mn n] =ᵐ[μ.restrict s] μ[g | mn n] := by
      intro n
      exact condExp_restrict_ae_eq_restrict (hmn_le n) (hs_mn n) hInt
    have hRestrictLimit :
        (μ.restrict s)[g | hσ.measurableSpace] =ᵐ[μ.restrict s] μ[g | hσ.measurableSpace] :=
      condExp_restrict_ae_eq_restrict hσ.measurableSpace_le hs_hσ hInt
    have hRestrictAe :
        ∀ᵐ ω ∂μ.restrict s,
          Tendsto (fun n ↦ (μ.restrict s)[g | mn n] ω) atTop
            (𝓝 ((μ.restrict s)[g | hσ.measurableSpace] ω)) := by
      -- Proof comment: on each finite-measure `𝓕_σ`-measurable slice, the finite-measure reverse
      -- Lévy theorem applies to the antitone dyadic stopping-time `σ`-algebras.
      simpa [hiInf] using
        (tendsto_ae_condExp_iInf_of_antitone hmn_le hmn_anti hInt_restrict)
    have hAllRestrict :
        ∀ᵐ ω ∂μ.restrict s, ∀ n, (μ.restrict s)[g | mn n] ω = μ[g | mn n] ω := by
      exact ae_all_iff.2 hRestrictStage
    filter_upwards [hRestrictAe, hAllRestrict, hRestrictLimit] with ω hω hωeq hωlim
    have hFn :
        (fun n ↦ (μ.restrict s)[g | mn n] ω) =ᶠ[atTop]
          (fun n ↦ μ[g | mn n] ω) :=
      Filter.Eventually.of_forall fun n ↦ hωeq n
    have hω' :
        Tendsto (fun n ↦ μ[g | mn n] ω) atTop
          (𝓝 ((μ.restrict s)[g | hσ.measurableSpace] ω)) :=
      hω.congr' hFn
    simpa [hωlim] using hω'
  have hAe :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n ↦ μ[g | mn n] ω)
          atTop
          (𝓝 (μ[g | hσ.measurableSpace] ω)) := by
    -- Proof comment: the stopping-time `σ`-algebra is sigma-finite, so the finite-measure slice
    -- convergence statements glue back together across a countable `𝓕_σ`-measurable spanning
    -- family.
    have hGlobal :
        ∀ᵐ ω ∂μ.restrict (⋃ k : ℕ, S.set k),
          Tendsto
            (fun n ↦ μ[g | mn n] ω)
            atTop
            (𝓝 (μ[g | hσ.measurableSpace] ω)) :=
      (ae_restrict_iUnion_iff (fun k : ℕ ↦ S.set k)
        (fun ω ↦
          Tendsto
            (fun n ↦ μ[g | mn n] ω)
            atTop
            (𝓝 (μ[g | hσ.measurableSpace] ω)))).2 hPiece
    simpa [S.spanning] using hGlobal
  simpa [g, mn] using hAe

/-- Helper for Exercise 21.1.3: on a finite measurable slice, the restricted conditional
expectations of an integrable function along an antitone family of `σ`-algebras converge in `L¹`
to the restricted conditional expectation on the limiting `σ`-algebra. -/
private theorem restrict_condExp_tendstoL1_of_antitone
    {g : Ω → ℝ} (hInt : Integrable g μ)
    {m : ℕ → MeasurableSpace Ω}
    (hm_le : ∀ n, m n ≤ mΩ) (hm_anti : Antitone m)
    {s : Set Ω} (hμs : μ s < ∞) :
    Tendsto
      (fun n ↦
        eLpNorm (((μ.restrict s)[g | m n]) - ((μ.restrict s)[g | ⨅ k : ℕ, m k])) 1
          (μ.restrict s))
      atTop (𝓝 0) := by
  have hInt_restrict : Integrable g (μ.restrict s) := hInt.restrict
  haveI : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hμs.ne
  have hAe :
      ∀ᵐ ω ∂μ.restrict s,
        Tendsto
          (fun n ↦ (μ.restrict s)[g | m n] ω)
          atTop
          (𝓝 ((μ.restrict s)[g | ⨅ k : ℕ, m k] ω)) := by
    -- Proof comment: on the finite restricted measure, reverse Lévy gives almost-sure
    -- convergence along the antitone family.
    exact
      (tendsto_ae_condExp_iInf_of_antitone hm_le hm_anti hInt_restrict)
  have hIntLimit :
      Integrable ((μ.restrict s)[g | ⨅ k : ℕ, m k]) (μ.restrict s) := by
    exact integrable_condExp
  have hMemLp :
      MemLp ((μ.restrict s)[g | ⨅ k : ℕ, m k]) 1 (μ.restrict s) :=
    memLp_one_iff_integrable.2 hIntLimit
  -- Proof comment: finite-measure Vitali upgrades the restricted almost-sure convergence to
  -- `L¹` convergence.
  exact
    tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
      (fun n ↦ (stronglyMeasurable_condExp.mono (hm_le n)).aestronglyMeasurable)
      hMemLp
      (hInt_restrict.uniformIntegrable_condExp fun n ↦ hm_le n).unifIntegrable
      hAe

/-- Helper for Exercise 21.1.3: finite spanning slices of the limiting `σ`-algebra inherit the
restricted reverse-Lévy `L¹` convergence. -/
private lemma finiteSpanningSlice_measure_lt_top
    {mInf : MeasurableSpace Ω} (hmInf : mInf ≤ mΩ)
    (S : (μ.trim hmInf).FiniteSpanningSetsIn {s | MeasurableSet[mInf] s}) (k : ℕ) :
    μ (S.set k) < ∞ := by
  -- Proof comment: each spanning slice is finite for the trimmed measure, and on
  -- `mInf`-measurable sets the trimmed and ambient measures coincide.
  have hs_mInf : MeasurableSet[mInf] (S.set k) := S.set_mem k
  simpa [trim_measurableSet_eq hmInf hs_mInf] using S.finite k

/-- Helper for Exercise 21.1.3: finite spanning slices of the limiting `σ`-algebra inherit the
restricted reverse-Lévy `L¹` convergence. -/
private theorem finiteSpanningSlice_condExp_tendstoL1
    {g : Ω → ℝ} (hInt : Integrable g μ)
    {mInf : MeasurableSpace Ω} (hmInf : mInf ≤ mΩ)
    {m : ℕ → MeasurableSpace Ω}
    (hm_le : ∀ n, m n ≤ mΩ) (hm_anti : Antitone m)
    (hiInf : (⨅ n : ℕ, m n) = mInf)
    (S : (μ.trim hmInf).FiniteSpanningSetsIn {s | MeasurableSet[mInf] s}) :
    ∀ k : ℕ,
      Tendsto
        (fun n ↦
          eLpNorm
            (((μ.restrict (S.set k))[g | m n]) -
              ((μ.restrict (S.set k))[g | mInf]))
            1 (μ.restrict (S.set k)))
        atTop (𝓝 0) := by
  have hiInf' : mInf = ⨅ n : ℕ, m n := hiInf.symm
  subst mInf
  intro k
  have hs_fin : μ (S.set k) < ∞ :=
    finiteSpanningSlice_measure_lt_top hmInf S k
  -- Proof comment: each spanning slice is a finite measure space, so the restricted reverse-Lévy
  -- `L¹` theorem applies directly on that slice.
  simpa using
    (restrict_condExp_tendstoL1_of_antitone
      hInt hm_le hm_anti hs_fin)

/-- Helper for Exercise 21.1.3: finite partial unions of a trimmed finite spanning family are
ambient measurable. -/
private lemma finiteSpanningPartialUnion_measurable
    {mTrim : MeasurableSpace Ω} (hm : mTrim ≤ mΩ)
    (S : (μ.trim hm).FiniteSpanningSetsIn {s | MeasurableSet[mTrim] s}) :
    ∀ N : ℕ, MeasurableSet[mΩ] (⋃ k ∈ Finset.range (N + 1), S.set k) := by
  intro N
  -- Proof comment: every partial union uses only finitely many `mTrim`-measurable sets, and
  -- `hm` transports that measurability to the ambient space.
  exact Finset.measurableSet_biUnion _ fun k _ ↦ hm _ (S.set_mem k)

/-- Helper for Exercise 21.1.3: every sample point eventually lies in the finite partial unions of
a spanning family. -/
private lemma eventually_mem_finiteSpanningPartialUnion
    {mTrim : MeasurableSpace Ω} (hm : mTrim ≤ mΩ)
    (S : (μ.trim hm).FiniteSpanningSetsIn {s | MeasurableSet[mTrim] s}) (ω : Ω) :
    ∀ᶠ N : ℕ in atTop, ω ∈ ⋃ k ∈ Finset.range (N + 1), S.set k := by
  have hω_cover : ω ∈ ⋃ i : ℕ, S.set i := by
    simpa [S.spanning] using (show ω ∈ (Set.univ : Set Ω) from trivial)
  rcases mem_iUnion.mp hω_cover with ⟨k, hk⟩
  refine (Filter.eventually_ge_atTop k).mono fun N hN ↦ ?_
  -- Proof comment: once the union index passes one spanning witness `k`, that witness stays in
  -- every later finite partial union.
  simpa [Finset.mem_range, Nat.lt_succ_iff] using
    (show ∃ i, i ≤ N ∧ ω ∈ S.set i from ⟨k, hN, hk⟩)

/-- Helper for Exercise 21.1.3: the complement indicators of the finite partial unions converge
pointwise almost everywhere to `0`. -/
private lemma tendsto_indicator_compl_finiteSpanningPartialUnion
    {mTrim : MeasurableSpace Ω} (hm : mTrim ≤ mΩ)
    (S : (μ.trim hm).FiniteSpanningSetsIn {s | MeasurableSet[mTrim] s})
    {g : Ω → ℝ} :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun N : ℕ ↦
          ((⋃ k ∈ Finset.range (N + 1), S.set k)ᶜ).indicator (fun ω' ↦ |g ω'|) ω)
        atTop (𝓝 0) := by
  -- Route correction: first prove the ambient indicator family is eventually zero pointwise,
  -- then let dominated convergence consume that normal form.
  refine Filter.Eventually.of_forall fun ω ↦ ?_
  let U : ℕ → Set Ω := fun N ↦ ⋃ k ∈ Finset.range (N + 1), S.set k
  have hω_cover : ω ∈ ⋃ i : ℕ, S.set i := by
    simpa [S.spanning] using (show ω ∈ (Set.univ : Set Ω) from trivial)
  rcases mem_iUnion.mp hω_cover with ⟨k, hk⟩
  have hmem : ∀ᶠ N : ℕ in atTop, ω ∈ U N := by
    refine (Filter.eventually_ge_atTop k).mono fun N hN ↦ ?_
    -- Proof comment: once the partial union index reaches one spanning witness `k`, that witness
    -- remains present in every later union.
    refine mem_iUnion.2 ⟨k, ?_⟩
    refine mem_iUnion.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hN), hk⟩
  have hzero :
      (fun N : ℕ ↦
        ((⋃ k ∈ Finset.range (N + 1), S.set k)ᶜ).indicator (fun ω' ↦ |g ω'|) ω) =ᶠ[atTop]
        fun _ ↦ 0 := by
    -- Proof comment: once `ω` lies in the finite partial union, the complement indicator vanishes.
    filter_upwards [hmem] with N hN
    rw [Set.indicator_of_notMem]
    exact fun hωc ↦ hωc hN
  exact Tendsto.congr' hzero.symm tendsto_const_nhds

/-- Helper for Exercise 21.1.3: the complements of the finite partial unions of a finite spanning
family carry asymptotically no `|g|`-mass. -/
private lemma tendsto_setIntegral_abs_compl_finiteSpanning
    {mTrim : MeasurableSpace Ω} (hm : mTrim ≤ mΩ)
    (S : (μ.trim hm).FiniteSpanningSetsIn {s | MeasurableSet[mTrim] s})
    {g : Ω → ℝ} (hg : Integrable g μ) :
    Tendsto
      (fun N : ℕ ↦ ∫ ω in (⋃ k ∈ Finset.range (N + 1), S.set k)ᶜ, |g ω| ∂μ)
      atTop (𝓝 0) := by
  let U : ℕ → Set Ω := fun N ↦ ⋃ k ∈ Finset.range (N + 1), S.set k
  have hU_meas : ∀ N : ℕ, MeasurableSet[mΩ] (U N) := by
    intro N
    exact Finset.measurableSet_biUnion _ fun k _ ↦ hm _ (S.set_mem k)
  have h_meas :
      ∀ N : ℕ, AEStronglyMeasurable[mΩ] ((U N)ᶜ.indicator fun ω ↦ |g ω|) μ := by
    intro N
    exact hg.norm.aestronglyMeasurable.indicator (hU_meas N).compl
  have h_bound :
      ∀ N : ℕ, ∀ᵐ ω ∂μ, ‖((U N)ᶜ.indicator fun ω' ↦ |g ω'|) ω‖ ≤ |g ω| := by
    intro N
    -- Proof comment: the complement indicator either keeps `|g|` or replaces it by `0`.
    exact Filter.Eventually.of_forall fun ω ↦ by
      by_cases hω : ω ∈ (U N)ᶜ <;> simp [hω, abs_nonneg]
  have h_lim :
      ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ ↦ ((U N)ᶜ.indicator fun ω' ↦ |g ω'|) ω) atTop (𝓝 0) := by
    refine Filter.Eventually.of_forall fun ω ↦ ?_
    have hω_cover : ω ∈ ⋃ i : ℕ, S.set i := by
      simpa [S.spanning] using (show ω ∈ (Set.univ : Set Ω) from trivial)
    rcases mem_iUnion.mp hω_cover with ⟨k, hk⟩
    have hmem : ∀ᶠ N : ℕ in atTop, ω ∈ U N := by
      refine (Filter.eventually_ge_atTop k).mono fun N hN ↦ ?_
      refine mem_iUnion.2 ⟨k, ?_⟩
      refine mem_iUnion.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hN), hk⟩
    have hzero :
        (fun N : ℕ ↦ ((U N)ᶜ.indicator fun ω' ↦ |g ω'|) ω) =ᶠ[atTop] fun _ ↦ 0 := by
      filter_upwards [hmem] with N hN
      rw [Set.indicator_of_notMem]
      exact fun hωc ↦ hωc hN
    exact Tendsto.congr' hzero.symm tendsto_const_nhds
  have h_indicator :
      Tendsto
        (fun N : ℕ ↦ ∫ ω, ((U N)ᶜ.indicator fun ω' ↦ |g ω'|) ω ∂μ)
        atTop (𝓝 0) := by
    -- Proof comment: dominated convergence now runs on the ambient indicator family without any
    -- restricted-measure transport.
    simpa using
      (MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun ω ↦ |g ω|) h_meas hg.norm h_bound h_lim)
  -- Proof comment: rewrite the ambient indicator integrals back to the desired set integrals.
  have hrewrite :
      (fun N : ℕ ↦ ∫ ω, ((U N)ᶜ.indicator fun ω' ↦ |g ω'|) ω ∂μ) =
        fun N : ℕ ↦ ∫ ω in (U N)ᶜ, |g ω| ∂μ := by
    funext N
    rw [MeasureTheory.integral_indicator (hU_meas N).compl]
  rw [hrewrite] at h_indicator
  simpa [U] using h_indicator

/-- Helper for Exercise 21.1.3: a finite partial union of the spanning slices still has finite
ambient measure. -/
private lemma finiteSpanningPartialUnion_measure_lt_top
    {mTrim : MeasurableSpace Ω} (hm : mTrim ≤ mΩ)
    (S : (μ.trim hm).FiniteSpanningSetsIn {s | MeasurableSet[mTrim] s}) (N : ℕ) :
    μ (⋃ k ∈ Finset.range (N + 1), S.set k) < ∞ := by
  -- Proof comment: a finite partial union is dominated by the finite sum of the slice measures,
  -- and each slice measure is already finite.
  refine lt_of_le_of_lt (MeasureTheory.measure_biUnion_finset_le (μ := μ) (Finset.range (N + 1))
    S.set) ?_
  refine ENNReal.sum_lt_top.mpr ?_
  intro k hk
  rw [← MeasureTheory.trim_measurableSet_eq hm (S.set_mem k)]
  exact S.finite k

/-- Helper for Exercise 21.1.3: on exponent `1`, the `L¹` seminorm of an indicator is the
corresponding set integral of the absolute value. -/
private lemma eLpNorm_indicator_eq_ofReal_setIntegral_abs
    {s : Set Ω} (hs : MeasurableSet s) {f : Ω → ℝ} (hf : Integrable f μ) :
    eLpNorm (s.indicator f) 1 μ = ENNReal.ofReal (∫ ω in s, |f ω| ∂μ) := by
  -- Proof comment: move the indicator into the restricted measure and then use the `p = 1`
  -- seminorm formula there.
  rw [MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hs,
    MeasureTheory.eLpNorm_one_eq_lintegral_enorm,
    ← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm hf.restrict]
  simp [Real.norm_eq_abs]

/-- Helper for Exercise 21.1.3: the `L¹` mass of `g` on the complements of the finite partial
unions tends to zero. -/
private lemma tendsto_eLpNorm_indicator_compl_finiteSpanning
    {mTrim : MeasurableSpace Ω} (hm : mTrim ≤ mΩ)
    (S : (μ.trim hm).FiniteSpanningSetsIn {s | MeasurableSet[mTrim] s})
    {g : Ω → ℝ} (hg : Integrable g μ) :
    Tendsto
      (fun N : ℕ ↦
        eLpNorm (((⋃ k ∈ Finset.range (N + 1), S.set k)ᶜ).indicator g) 1 μ)
      atTop (𝓝 0) := by
  have hRewrite :
      ∀ N : ℕ,
        eLpNorm (((⋃ k ∈ Finset.range (N + 1), S.set k)ᶜ).indicator g) 1 μ =
          ENNReal.ofReal
            (∫ ω in (⋃ k ∈ Finset.range (N + 1), S.set k)ᶜ, |g ω| ∂μ) := by
    intro N
    -- Proof comment: rewrite the `L¹` norm of the complement indicator back to the
    -- corresponding set integral of `|g|`.
    simpa using
      (eLpNorm_indicator_eq_ofReal_setIntegral_abs (mΩ := mΩ) (μ := μ)
        (s := (⋃ k ∈ Finset.range (N + 1), S.set k)ᶜ) (f := g)
        ((finiteSpanningPartialUnion_measurable
          (mΩ := mΩ) (μ := μ) (mTrim := mTrim) hm S N).compl) hg)
  -- Proof comment: the set-integral tail already tends to `0`, and `ENNReal.ofReal` is
  -- continuous at the origin.
  refine Tendsto.congr' (Filter.Eventually.of_forall fun N ↦ (hRewrite N).symm) ?_
  simpa using
    (ENNReal.continuous_ofReal.tendsto 0).comp
      (tendsto_setIntegral_abs_compl_finiteSpanning
        (mΩ := mΩ) (μ := μ) (mTrim := mTrim) hm S hg)

/-- Helper for Exercise 21.1.3: on each finite spanning slice, the ambient indicator form of the
conditional-expectation difference inherits the restricted reverse-Lévy `L¹` convergence. -/
private lemma finiteSpanningSlice_indicator_condExp_tendstoL1
    {g : Ω → ℝ} (hInt : Integrable g μ)
    {mInf : MeasurableSpace Ω} (hmInf : mInf ≤ mΩ)
    {m : ℕ → MeasurableSpace Ω}
    (hm_le : ∀ n, m n ≤ mΩ) (hm_anti : Antitone m)
    (hiInf : (⨅ n : ℕ, m n) = mInf)
    (S : (μ.trim hmInf).FiniteSpanningSetsIn {s | MeasurableSet[mInf] s}) :
    ∀ k : ℕ,
      Tendsto
        (fun n ↦
          eLpNorm ((S.set k).indicator (μ[g | m n] - μ[g | mInf])) 1 μ)
        atTop (𝓝 0) := by
  intro k
  let s : Set Ω := S.set k
  have hs_mInf : MeasurableSet[mInf] s := S.set_mem k
  have hs : MeasurableSet[mΩ] s := hmInf _ hs_mInf
  letI : SigmaFinite (μ.trim hmInf) := S.sigmaFinite
  change Tendsto (fun n ↦ eLpNorm (s.indicator (μ[g | m n] - μ[g | mInf])) 1 μ) atTop (𝓝 0)
  have hmInf_le : ∀ n, mInf ≤ m n := by
    intro n
    rw [← hiInf]
    exact iInf_le m n
  have hs_m : ∀ n, MeasurableSet[m n] s := by
    intro n
    exact hmInf_le n _ hs_mInf
  have hRewrite :
      ∀ n : ℕ,
        eLpNorm (s.indicator (μ[g | m n] - μ[g | mInf])) 1 μ =
          eLpNorm (((μ.restrict s)[g | m n]) - ((μ.restrict s)[g | mInf])) 1
            (μ.restrict s) := by
    intro n
    letI : SigmaFinite (μ.trim (show mInf ≤ mΩ from (hmInf_le n).trans (hm_le n))) := by
      simpa using (S.sigmaFinite : SigmaFinite (μ.trim hmInf))
    letI : SigmaFinite (μ.trim (hm_le n)) :=
      sigmaFiniteTrim_mono (μ := μ) (hm := hm_le n) (hm₂ := hmInf_le n)
    -- Proof comment: rewrite the ambient indicator norm to the restricted slice norm and then
    -- transport both conditional expectations across restriction.
    calc
      eLpNorm (s.indicator (μ[g | m n] - μ[g | mInf])) 1 μ
          = eLpNorm (μ[g | m n] - μ[g | mInf]) 1 (μ.restrict s) := by
              simpa using
                (MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict (μ := μ) (p := (1 : ℝ≥0∞))
                  (f := μ[g | m n] - μ[g | mInf]) hs)
      _ = eLpNorm (((μ.restrict s)[g | m n]) - ((μ.restrict s)[g | mInf])) 1 (μ.restrict s) := by
            refine eLpNorm_congr_ae ?_
            exact
              ((MeasureTheory.condExp_restrict_ae_eq_restrict (hm_le n) (hs_m n) hInt).symm.sub
                (MeasureTheory.condExp_restrict_ae_eq_restrict hmInf hs_mInf hInt).symm)
  refine Tendsto.congr' (Filter.Eventually.of_forall fun n ↦ (hRewrite n).symm) ?_
  -- Proof comment: the restricted slice theorem now applies directly.
  simpa [s] using
    (finiteSpanningSlice_condExp_tendstoL1
      (mΩ := mΩ) (μ := μ) (mInf := mInf) hInt hmInf hm_le hm_anti hiInf S k)

/-- Helper for Exercise 21.1.3: the `L¹` mass on a finite partial union is bounded by the sum of
the `L¹` masses on its spanning slices. -/
private lemma finiteSpanningPartialUnion_indicator_le_sum
    {mTrim : MeasurableSpace Ω} (hm : mTrim ≤ mΩ)
    (S : (μ.trim hm).FiniteSpanningSetsIn {s | MeasurableSet[mTrim] s})
    (N : ℕ) {f : Ω → ℝ} (hf : Integrable f μ) :
    eLpNorm ((⋃ k ∈ Finset.range (N + 1), S.set k).indicator f) 1 μ ≤
      Finset.sum (Finset.range (N + 1)) (fun k ↦ eLpNorm ((S.set k).indicator f) 1 μ) := by
  induction N with
  | zero =>
      -- Proof comment: the first partial union consists of the single slice `S.set 0`.
      simp
  | succ N hN =>
      let U : Set Ω := ⋃ k ∈ Finset.range (N + 1), S.set k
      let A : Set Ω := S.set (N + 1)
      have hU : MeasurableSet[mΩ] U :=
        finiteSpanningPartialUnion_measurable (mΩ := mΩ) (μ := μ) (mTrim := mTrim) hm S N
      have hA : MeasurableSet[mΩ] A := hm _ (S.set_mem (N + 1))
      have hUnion :
          (⋃ k ∈ Finset.range (N + 2), S.set k) = U ∪ (A \ U) := by
        -- Proof comment: the next partial union is the old union plus the new slice, with the
        -- overlap removed to make the triangle-inequality step disjoint.
        have hRange :
            Finset.range (N + 2) = insert (N + 1) (Finset.range (N + 1)) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (Finset.range_add_one (n := N + 1))
        calc
          (⋃ k ∈ Finset.range (N + 2), S.set k) = A ∪ U := by
            rw [hRange]
            simp [U, A, Finset.notMem_range_self, union_comm, union_left_comm, union_assoc]
          _ = U ∪ (A \ U) := by
            ext ω
            by_cases hωU : ω ∈ U <;> by_cases hωA : ω ∈ A <;> simp [hωU, hωA]
      calc
        eLpNorm ((⋃ k ∈ Finset.range (N + 2), S.set k).indicator f) 1 μ
            = eLpNorm (U.indicator f + (A \ U).indicator f) 1 μ := by
                rw [hUnion, Set.indicator_union_of_disjoint Set.disjoint_sdiff_right]
                rfl
        _ ≤ eLpNorm (U.indicator f) 1 μ + eLpNorm ((A \ U).indicator f) 1 μ := by
              exact eLpNorm_add_le
                (hf.aestronglyMeasurable.indicator hU)
                (hf.aestronglyMeasurable.indicator (hA.diff hU))
                (by norm_num)
        _ ≤ eLpNorm (U.indicator f) 1 μ + eLpNorm (A.indicator f) 1 μ := by
              refine add_le_add le_rfl ?_
              exact eLpNorm_mono fun ω ↦ norm_indicator_le_of_subset Set.diff_subset f ω
        _ ≤
            Finset.sum (Finset.range (N + 1)) (fun k ↦ eLpNorm ((S.set k).indicator f) 1 μ) +
              eLpNorm (A.indicator f) 1 μ := by
                exact add_le_add hN le_rfl
        _ =
            Finset.sum (Finset.range (N + 2)) (fun k ↦ eLpNorm ((S.set k).indicator f) 1 μ) := by
                simp [A, Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]

/-- Helper for Exercise 21.1.3: finite partial unions of the limiting `σ`-algebra inherit the
restricted reverse-Lévy `L¹` convergence. -/
private lemma finiteSpanningPartialUnion_condExp_tendstoL1
    {g : Ω → ℝ} (hInt : Integrable g μ)
    {mInf : MeasurableSpace Ω} (hmInf : mInf ≤ mΩ)
    {m : ℕ → MeasurableSpace Ω}
    (hm_le : ∀ n, m n ≤ mΩ) (hm_anti : Antitone m)
    (hiInf : (⨅ n : ℕ, m n) = mInf)
    (S : (μ.trim hmInf).FiniteSpanningSetsIn {s | MeasurableSet[mInf] s}) :
    ∀ N : ℕ,
      Tendsto
        (fun n ↦
          eLpNorm
            ((⋃ k ∈ Finset.range (N + 1), S.set k).indicator
              (μ[g | m n] - μ[g | mInf]))
            1 μ)
        atTop (𝓝 0) := by
  intro N
  let bound : ℕ → ℝ≥0∞ := fun n ↦
    Finset.sum (Finset.range (N + 1)) fun k ↦
      eLpNorm ((S.set k).indicator (μ[g | m n] - μ[g | mInf])) 1 μ
  have hBound :
      ∀ n,
        eLpNorm
            ((⋃ k ∈ Finset.range (N + 1), S.set k).indicator
              (μ[g | m n] - μ[g | mInf]))
            1 μ ≤ bound n := by
    intro n
    have hDiffInt : Integrable (μ[g | m n] - μ[g | mInf]) μ :=
      integrable_condExp.sub integrable_condExp
    -- Proof comment: the finite-union term is controlled by the sum of the slice terms by the
    -- preceding partial-union domination lemma.
    simpa [bound] using
      (finiteSpanningPartialUnion_indicator_le_sum
        (mΩ := mΩ) (μ := μ) (mTrim := mInf) hmInf S N hDiffInt)
  have hBoundTendsto : Tendsto bound atTop (𝓝 0) := by
    -- Proof comment: each slice term tends to `0`, and finite sums preserve that convergence.
    simpa [bound] using
      (tendsto_finset_sum (Finset.range (N + 1)) fun k hk ↦
        finiteSpanningSlice_indicator_condExp_tendstoL1
          (mΩ := mΩ) (μ := μ) hInt hmInf hm_le hm_anti hiInf S k)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ≥0∞)) atTop (𝓝 0)) hBoundTendsto
    ?_ ?_
  · intro n
    exact bot_le
  · exact hBound

/-- Helper for Exercise 21.1.3: conditioning cannot increase the `L¹` mass on an
ambient-measurable indicator slice. -/
private lemma eLpNorm_indicator_condExp_le
    {g : Ω → ℝ} (hInt : Integrable g μ)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {s : Set Ω} (hs : MeasurableSet[m] s) :
    eLpNorm (s.indicator (μ[g | m])) 1 μ ≤ eLpNorm (s.indicator g) 1 μ := by
  have hsΩ : MeasurableSet[mΩ] s := hm _ hs
  have hIntCond : Integrable (μ[g | m]) μ := by
    simpa using (integrable_condExp : Integrable (μ[g | m]) μ)
  -- Proof comment: rewrite both sides as set integrals of absolute values and apply the
  -- conditional-expectation set-integral contraction.
  calc
    eLpNorm (s.indicator (μ[g | m])) 1 μ
        = ENNReal.ofReal (∫ ω in s, |μ[g | m] ω| ∂μ) := by
            simpa using
              (eLpNorm_indicator_eq_ofReal_setIntegral_abs (mΩ := mΩ) (μ := μ)
                (s := s) (f := μ[g | m]) hsΩ hIntCond)
    _ ≤ ENNReal.ofReal (∫ ω in s, |g ω| ∂μ) := by
          exact ENNReal.ofReal_le_ofReal (MeasureTheory.setIntegral_abs_condExp_le hs g)
    _ = eLpNorm (s.indicator g) 1 μ := by
          simpa using
            (eLpNorm_indicator_eq_ofReal_setIntegral_abs (mΩ := mΩ) (μ := μ)
              (s := s) (f := g) hsΩ hInt).symm

/-- Helper for Exercise 21.1.3: finite-union convergence plus tail control reassembles the global
sigma-finite `L¹` limit for reverse conditional expectations. -/
private lemma dyadicCondexpSigmaFiniteReassembly
    {g : Ω → ℝ} (hInt : Integrable g μ)
    {mInf : MeasurableSpace Ω} (hmInf : mInf ≤ mΩ)
    {m : ℕ → MeasurableSpace Ω}
    (hm_le : ∀ n, m n ≤ mΩ) (hm_anti : Antitone m)
    (hiInf : (⨅ n : ℕ, m n) = mInf)
    (S : (μ.trim hmInf).FiniteSpanningSetsIn {s | MeasurableSet[mInf] s}) :
    Tendsto (fun n ↦ eLpNorm (μ[g | m n] - μ[g | mInf]) 1 μ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  have hε_third : 0 < ε / 3 := by
    exact ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨N, hN⟩ :=
    (ENNReal.tendsto_atTop_zero.mp
      (tendsto_eLpNorm_indicator_compl_finiteSpanning
        (mΩ := mΩ) (μ := μ) (mTrim := mInf) hmInf S hInt)) (ε / 3) hε_third
  obtain ⟨M, hM⟩ :=
    (ENNReal.tendsto_atTop_zero.mp
      (finiteSpanningPartialUnion_condExp_tendstoL1
        (mΩ := mΩ) (μ := μ) (mInf := mInf) hInt hmInf hm_le hm_anti hiInf S N))
      (ε / 3) hε_third
  refine ⟨M, fun n hn ↦ ?_⟩
  let U : Set Ω := ⋃ k ∈ Finset.range (N + 1), S.set k
  have hU_mInf : MeasurableSet[mInf] U := by
    -- Proof comment: the fixed main part is a finite union of `mInf`-measurable spanning slices.
    exact Finset.measurableSet_biUnion _ fun k hk ↦ S.set_mem k
  have hU : MeasurableSet[mΩ] U := hmInf _ hU_mInf
  have hmInf_le : ∀ n, mInf ≤ m n := by
    intro n
    rw [← hiInf]
    exact iInf_le m n
  have hDiffInt :
      ∀ n, Integrable (μ[g | m n] - μ[g | mInf]) μ := by
    intro n
    exact integrable_condExp.sub integrable_condExp
  have hMainSmall :
      eLpNorm (U.indicator (μ[g | m n] - μ[g | mInf])) 1 μ ≤ ε / 3 :=
    hM n hn
  have hTailSmall : eLpNorm (Uᶜ.indicator g) 1 μ ≤ ε / 3 := by
    exact hN N le_rfl
  have hCond_n_small :
      eLpNorm (Uᶜ.indicator (μ[g | m n])) 1 μ ≤ ε / 3 := by
    exact
      (eLpNorm_indicator_condExp_le (mΩ := mΩ) (μ := μ) hInt
        (hm_le n) (hmInf_le n _ hU_mInf.compl)).trans
        hTailSmall
  have hCond_inf_small :
      eLpNorm (Uᶜ.indicator (μ[g | mInf])) 1 μ ≤ ε / 3 := by
    exact
      (eLpNorm_indicator_condExp_le (mΩ := mΩ) (μ := μ) hInt hmInf hU_mInf.compl).trans
        hTailSmall
  have hTailDiff :
      eLpNorm (Uᶜ.indicator (μ[g | m n] - μ[g | mInf])) 1 μ ≤ ε / 3 + ε / 3 := by
    have hIntCond_n : Integrable (μ[g | m n]) μ := by
      simpa using (integrable_condExp : Integrable (μ[g | m n]) μ)
    have hIntCond_inf : Integrable (μ[g | mInf]) μ := by
      simpa using (integrable_condExp : Integrable (μ[g | mInf]) μ)
    have hAsm_n :
        AEStronglyMeasurable[mΩ] (Uᶜ.indicator (μ[g | m n])) μ :=
      hIntCond_n.aestronglyMeasurable.indicator hU.compl
    have hAsm_inf :
        AEStronglyMeasurable[mΩ] (Uᶜ.indicator (μ[g | mInf])) μ :=
      hIntCond_inf.aestronglyMeasurable.indicator hU.compl
    -- Proof comment: on the complement, the conditional-expectation difference is controlled by
    -- the sum of the two conditional-expectation tails.
    rw [Uᶜ.indicator_sub' (μ[g | m n]) (μ[g | mInf])]
    exact (eLpNorm_sub_le hAsm_n hAsm_inf le_rfl).trans
      (add_le_add hCond_n_small hCond_inf_small)
  have hAsm_tail :
      AEStronglyMeasurable[mΩ] (Uᶜ.indicator (μ[g | m n] - μ[g | mInf])) μ :=
    (hDiffInt n).aestronglyMeasurable.indicator hU.compl
  have hAsm_main :
      AEStronglyMeasurable[mΩ] (U.indicator (μ[g | m n] - μ[g | mInf])) μ :=
    (hDiffInt n).aestronglyMeasurable.indicator hU
  -- Proof comment: split the global difference into the fixed finite main part and the small
  -- complement tail, then combine the two estimates.
  calc
    eLpNorm (μ[g | m n] - μ[g | mInf]) 1 μ
        =
          eLpNorm
            (Uᶜ.indicator (μ[g | m n] - μ[g | mInf]) +
              U.indicator (μ[g | m n] - μ[g | mInf])) 1 μ := by
      congr
      exact (U.indicator_compl_add_self (μ[g | m n] - μ[g | mInf])).symm
    _ ≤
        eLpNorm (Uᶜ.indicator (μ[g | m n] - μ[g | mInf])) 1 μ +
          eLpNorm (U.indicator (μ[g | m n] - μ[g | mInf])) 1 μ := by
      exact eLpNorm_add_le hAsm_tail hAsm_main le_rfl
    _ ≤ (ε / 3 + ε / 3) + ε / 3 := add_le_add hTailDiff hMainSmall
    _ = ε := by simp only [ENNReal.add_thirds]

/-- Helper for Exercise 21.1.3: `L¹` convergence on `μ` transfers directly to restricted set
integrals. -/
private lemma tendstoRestrictedIntegralOfTendstoL1
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {s : Set Ω}
    (hg : Integrable g μ) (hfi : ∀ n, Integrable (f n) μ)
    (hL1 : Tendsto (fun n ↦ eLpNorm (fun ω ↦ f n ω - g ω) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ ω in s, f n ω ∂μ) atTop (𝓝 (∫ ω in s, g ω ∂μ)) := by
  have hL1_restrict :
      Tendsto (fun n ↦ eLpNorm (fun ω ↦ f n ω - g ω) 1 (μ.restrict s)) atTop (𝓝 0) := by
    -- Proof comment: restricting the measure can only decrease the `L¹` seminorm, so the same
    -- convergence holds on every measurable slice.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL1 ?_ ?_
    · intro n
      exact bot_le
    · intro n
      exact eLpNorm_mono_measure (fun ω ↦ f n ω - g ω) Measure.restrict_le_self
  -- Proof comment: after moving to the restricted measure, continuity of the Bochner integral on
  -- `L¹` gives the restricted-integral limit.
  exact tendsto_integral_of_L1' g hg.restrict
    (Filter.Eventually.of_forall fun n ↦ (hfi n).restrict) hL1_restrict

private theorem dyadic_condexp_tendsto_L1 [Filtration.IsRightContinuous ℱ] :
    ∀ {X : NNReal → Ω → ℝ}
      (_ : Supermartingale X ℱ μ) (_ : HasRightContinuousPaths X)
      {σ τ : Ω → NNReal}
      (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
      (_ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal))
      (_ : σ ≤ τ)
      (_ : ∃ T : NNReal, ∀ ω, σ ω ≤ T)
      (_ : ∃ T : NNReal, ∀ ω, τ ω ≤ T),
      ∀ m : ℕ,
        Tendsto
          (fun n ↦
            eLpNorm
              (μ[stoppedValue X (fun ω' ↦ (dyadicCeilApprox m τ ω' : ENNReal)) |
                  (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace] -
                μ[stoppedValue X (fun ω' ↦ (dyadicCeilApprox m τ ω' : ENNReal)) |
                  hσ.measurableSpace])
              1 μ)
          atTop (𝓝 0) := by
  intro X hX _hXrc σ τ hσ hτ _hστ _hσ_bdd hτ_bdd m
  have hInt :
    Integrable (stoppedValue X (fun ω' ↦ (dyadicCeilApprox m τ ω' : ENNReal))) μ :=
    integrable_stoppedValue_dyadicCeilApprox hX hτ m hτ_bdd
  let g : Ω → ℝ :=
    stoppedValue X (fun ω' ↦ (dyadicCeilApprox m τ ω' : ENNReal))
  let mn : ℕ → MeasurableSpace Ω :=
    fun n ↦ (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace
  have hmn_le : ∀ n, mn n ≤ mΩ := by
    intro n
    exact (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace_le
  have hmn_anti : Antitone mn := by
    simpa [mn] using (dyadicCeilApprox_measurableSpace_antitone hσ)
  have hiInf : (⨅ n : ℕ, mn n) = hσ.measurableSpace := by
    simpa [mn] using (dyadicCeilApprox_measurableSpace_iInf_eq hσ)
  let S :
      (μ.trim hσ.measurableSpace_le).FiniteSpanningSetsIn
        {s | MeasurableSet[hσ.measurableSpace] s} :=
    (μ.trim hσ.measurableSpace_le).toFiniteSpanningSetsIn
  -- Proof comment: invoke the sigma-finite reassembly lemma for the dyadic stopping-time
  -- filtration approximation.
  simpa [g, mn] using
    (dyadicCondexpSigmaFiniteReassembly hInt hσ.measurableSpace_le hmn_le hmn_anti hiInf S)

/-- Helper for this exercise: for a bounded stopping time `σ`, the dyadic stopped values `X_{σ^n}`
converge almost surely to `X_σ`. -/
private theorem dyadic_stoppedValue_tendsto_ae :
    ∀ {X : NNReal → Ω → ℝ} (_ : Supermartingale X ℱ μ) (_ : HasRightContinuousPaths X)
      {σ : Ω → NNReal}
      (_ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
      (_ : ∃ T : NNReal, ∀ ω, σ ω ≤ T),
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n ↦ stoppedValue X (fun ω' ↦ (dyadicCeilApprox n σ ω' : ENNReal)) ω)
          atTop
          (𝓝 (stoppedValue X (fun ω' ↦ (σ ω' : ENNReal)) ω)) := by
  intro X _hX hXrc σ _hσ _hσ_bdd
  -- Proof comment: the dyadic ceilings decrease to the original finite time from the right, so
  -- right continuity of the sample paths gives pointwise convergence of the stopped values.
  exact Filter.Eventually.of_forall fun ω ↦
    stoppedValue_tendsto_of_rightTimeApprox hXrc
      (fun n ω' ↦ self_le_dyadicCeilApprox n σ ω')
      (dyadicCeilApprox_tendsto σ) ω

/-- Helper for Exercise 21.1.3: a bounded stopping time is controlled by an integer horizon. -/
private lemma exists_nat_bound_of_exists_bound
    {σ : Ω → NNReal} (hσ_bdd : ∃ T : NNReal, ∀ ω, σ ω ≤ T) :
    ∃ N : ℕ, ∀ ω, σ ω ≤ (N : NNReal) := by
  rcases hσ_bdd with ⟨T, hT⟩
  refine ⟨Nat.ceil T, ?_⟩
  intro ω
  exact (hT ω).trans (by exact_mod_cast Nat.le_ceil T)

/-- Helper for Exercise 21.1.3: each dyadic mesh already satisfies the discrete bounded
optional-stopping inequality on the sampled row. -/
private lemma dyadicExpectedStoppedValue_mono
    {X : NNReal → Ω → ℝ} (hX : Supermartingale X ℱ μ)
    {σ τ : Ω → NNReal}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
    (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal))
    (hστ : σ ≤ τ) (hτ_bdd : ∃ T : NNReal, ∀ ω, τ ω ≤ T) :
    ∀ m : ℕ,
      μ[stoppedValue X (fun ω ↦ (dyadicCeilApprox m τ ω : ENNReal))] ≤
        μ[stoppedValue X (fun ω ↦ (dyadicCeilApprox m σ ω : ENNReal))] := by
  intro m
  rcases exists_nat_bound_of_exists_bound hτ_bdd with ⟨N, hτ_le_N⟩
  letI : SigmaFiniteFiltration μ (dyadicRowFiltration (ℱ := ℱ) m) := by
    refine ⟨fun k => ?_⟩
    simpa [dyadicRowFiltration] using
      (inferInstance : SigmaFinite (μ.trim (ℱ.le (dyadicTime m k))))
  have hσ_idx :
      IsStoppingTime (dyadicRowFiltration (ℱ := ℱ) m) (dyadicCeilIndex m σ) :=
    dyadicCeilIndex_isStoppingTime (ℱ := ℱ) hσ m
  have hτ_idx :
      IsStoppingTime (dyadicRowFiltration (ℱ := ℱ) m) (dyadicCeilIndex m τ) :=
    dyadicCeilIndex_isStoppingTime (ℱ := ℱ) hτ m
  have hidx_le : dyadicCeilIndex m σ ≤ dyadicCeilIndex m τ := by
    intro ω
    change
      (Nat.ceil (((((2 : NNReal) ^ m) * σ ω : NNReal) : ℝ)) : ℕ∞) ≤
        (Nat.ceil (((((2 : NNReal) ^ m) * τ ω : NNReal) : ℝ)) : ℕ∞)
    have hreal :
        ((((2 : NNReal) ^ m) * σ ω : NNReal) : ℝ) ≤
          ((((2 : NNReal) ^ m) * τ ω : NNReal) : ℝ) := by
      exact_mod_cast (mul_le_mul_left' (hστ ω) ((2 : NNReal) ^ m))
    exact_mod_cast Nat.ceil_le_ceil hreal
  have hτ_idx_bdd : ∀ ω, dyadicCeilIndex m τ ω ≤ 2 ^ m * N :=
    dyadicCeilIndex_le_of_natBound (n := m) (N := N) hτ_le_N
  -- Proof comment: Theorem 10.11 applies directly to the sampled dyadic supermartingale once the
  -- sampled stops are packaged as bounded discrete stopping times.
  have hdisc :=
    supermartingale_expected_stoppedValue_mono_of_le_of_bounded
      (X := dyadicRowProcess X m) (ℱ := dyadicRowFiltration (ℱ := ℱ) m) (μ := μ)
      (dyadicRow_supermartingale (ℱ := ℱ) (μ := μ) hX m)
      hσ_idx hτ_idx hidx_le hτ_idx_bdd
  rw [dyadicRow_stoppedValue_eq_dyadicCeilApprox (X := X) (n := m) (σ := τ),
    dyadicRow_stoppedValue_eq_dyadicCeilApprox (X := X) (n := m) (σ := σ)] at hdisc
  exact hdisc

/-- Helper for Exercise 21.1.3: dyadic ceiling indices are monotone in the stopped time. -/
private lemma dyadicCeilIndex_mono
    {σ τ : Ω → NNReal} (hστ : σ ≤ τ) (n : ℕ) :
    dyadicCeilIndex n σ ≤ dyadicCeilIndex n τ := by
  intro ω
  change
    (Nat.ceil (((((2 : NNReal) ^ n) * σ ω : NNReal) : ℝ)) : ℕ∞) ≤
      (Nat.ceil (((((2 : NNReal) ^ n) * τ ω : NNReal) : ℝ)) : ℕ∞)
  have hreal :
      ((((2 : NNReal) ^ n) * σ ω : NNReal) : ℝ) ≤
        ((((2 : NNReal) ^ n) * τ ω : NNReal) : ℝ) := by
    exact_mod_cast mul_le_mul_left' (hστ ω) ((2 : NNReal) ^ n)
  exact_mod_cast Nat.ceil_le_ceil hreal

/-- Helper for Exercise 21.1.3: dyadic ceiling approximation fixes deterministic integer horizons.
-/
private lemma dyadicCeilApprox_constNatCast
    (n N : ℕ) :
    dyadicCeilApprox n (fun _ : Ω ↦ (N : NNReal)) = fun _ ↦ (N : NNReal) := by
  -- Proof comment: on a deterministic integer horizon, the dyadic ceiling lands exactly on the
  -- same dyadic mesh point, so the ceiling is exact and the remaining division cancels.
  funext ω
  have hpow : ((2 : NNReal) ^ n) = ((2 ^ n : ℕ) : NNReal) := by
    exact_mod_cast (show (2 : ℕ) ^ n = 2 ^ n by rfl)
  have hprod_real :
      (((((2 : NNReal) ^ n) * (N : NNReal) : NNReal) : ℝ)) = ((2 ^ n * N : ℕ) : ℝ) := by
    rw [hpow]
    norm_num [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc]
  have hceil :
      Nat.ceil (((((2 : NNReal) ^ n) * (N : NNReal) : NNReal) : ℝ)) = 2 ^ n * N := by
    rw [hprod_real]
    simpa using (Nat.ceil_natCast (2 ^ n * N))
  rw [dyadicCeilApprox, hceil, hpow]
  have hpow_pos : (0 : NNReal) < ((2 ^ n : ℕ) : NNReal) := by
    positivity
  rw [div_eq_iff hpow_pos.ne']
  norm_num [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Exercise 21.1.3: once a stopping time has been rounded to the dyadic mesh
`2^{-m}`, any finer dyadic ceiling leaves it unchanged. -/
private lemma dyadicCeilApprox_dyadicCeilApprox
    (m n : ℕ) (hmn : m ≤ n) (σ : Ω → NNReal) :
    dyadicCeilApprox n (dyadicCeilApprox m σ) = dyadicCeilApprox m σ := by
  funext ω
  set a : ℕ := Nat.ceil (((((2 : NNReal) ^ m) * σ ω : NNReal) : ℝ))
  have ha :
      dyadicCeilApprox m σ ω = (a : NNReal) / (2 : NNReal) ^ m := by
    simp [dyadicCeilApprox, a]
  have hpow : (2 : NNReal) ^ n = (2 : NNReal) ^ m * (2 : NNReal) ^ (n - m) := by
    rw [← pow_add, Nat.add_sub_of_le hmn]
  have hpow_nat_nm : (2 : NNReal) ^ (n - m) = ((2 ^ (n - m) : ℕ) : NNReal) := by
    exact_mod_cast (show (2 : ℕ) ^ (n - m) = 2 ^ (n - m) by rfl)
  have hmul :
      (2 : NNReal) ^ n * dyadicCeilApprox m σ ω =
        ((a * 2 ^ (n - m) : ℕ) : NNReal) := by
    rw [ha, hpow, div_eq_mul_inv]
    calc
      ((2 : NNReal) ^ m * (2 : NNReal) ^ (n - m)) * ((a : NNReal) * ((2 : NNReal) ^ m)⁻¹)
          = (((2 : NNReal) ^ (n - m)) * (a : NNReal)) *
              (((2 : NNReal) ^ m) * ((2 : NNReal) ^ m)⁻¹) := by
                ac_rfl
      _ = (((2 : NNReal) ^ (n - m)) * (a : NNReal)) * 1 := by
            rw [mul_inv_cancel₀]
            positivity
      _ = ((2 : NNReal) ^ (n - m)) * (a : NNReal) := by simp
      _ = ((a * 2 ^ (n - m) : ℕ) : NNReal) := by
            rw [hpow_nat_nm, Nat.cast_mul]
            ac_rfl
  have hceil :
      Nat.ceil (((((2 : NNReal) ^ n) * dyadicCeilApprox m σ ω : NNReal) : ℝ)) =
        a * 2 ^ (n - m) := by
    rw [hmul]
    simpa using Nat.ceil_natCast (a * 2 ^ (n - m))
  rw [dyadicCeilApprox, hceil, ha, hpow, hpow_nat_nm, Nat.cast_mul]
  have hpow_nm_ne : (((2 ^ (n - m) : ℕ) : NNReal)) ≠ 0 := by
    positivity
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (mul_div_mul_right (a : NNReal) ((2 : NNReal) ^ m) hpow_nm_ne)

/-- Helper for Exercise 21.1.3: the dyadic conditional expectations of the fixed terminal value
`X N` converge almost surely to the conditional expectation with respect to `𝓕_σ`. -/
private theorem dyadicConstHorizon_condExp_tendsto_ae
    [Filtration.IsRightContinuous ℱ] :
    ∀ {X : NNReal → Ω → ℝ}
      (_ : Supermartingale X ℱ μ) (_ : HasRightContinuousPaths X)
      {σ : Ω → NNReal}
      (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
      (_ : ∃ T : NNReal, ∀ ω, σ ω ≤ T)
      (N : ℕ) (_ : ∀ ω, σ ω ≤ (N : NNReal)),
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n ↦ μ[X N | (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace] ω)
          atTop
          (𝓝 (μ[X N | hσ.measurableSpace] ω)) := by
  intro X hX hXrc σ hσ hσ_bdd N hσ_le_N
  let τ : Ω → NNReal := fun _ ↦ (N : NNReal)
  have hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal) :=
    isStoppingTime_const ℱ (N : NNReal)
  have hστ : σ ≤ τ := hσ_le_N
  have hτ_bdd : ∃ T : NNReal, ∀ ω, τ ω ≤ T := ⟨N, fun _ ↦ le_rfl⟩
  -- Proof comment: specialize the dyadic conditional-expectation convergence theorem to the
  -- constant terminal stop and then normalize the stopped value back to `X N`.
  simpa [τ, dyadicCeilApprox_constNatCast, stoppedValue_const] using
    (dyadic_condexp_tendsto_ae hX hXrc hσ hτ hστ hσ_bdd hτ_bdd 0)

/-- Helper for Exercise 21.1.3: the dyadic conditional expectations of the fixed terminal value
`X N` converge in `L¹(μ)` to the conditional expectation with respect to `𝓕_σ`. -/
private theorem dyadicConstHorizon_condExp_tendsto_L1
    [Filtration.IsRightContinuous ℱ] :
    ∀ {X : NNReal → Ω → ℝ}
      (_ : Supermartingale X ℱ μ) (_ : HasRightContinuousPaths X)
      {σ : Ω → NNReal}
      (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
      (_ : ∃ T : NNReal, ∀ ω, σ ω ≤ T)
      (N : ℕ) (_ : ∀ ω, σ ω ≤ (N : NNReal)),
      Tendsto
        (fun n ↦
          eLpNorm
            (μ[X N | (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace] -
              μ[X N | hσ.measurableSpace])
            1 μ)
        atTop (𝓝 0) := by
  intro X hX hXrc σ hσ hσ_bdd N hσ_le_N
  let τ : Ω → NNReal := fun _ ↦ (N : NNReal)
  have hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal) :=
    isStoppingTime_const ℱ (N : NNReal)
  have hστ : σ ≤ τ := hσ_le_N
  have hτ_bdd : ∃ T : NNReal, ∀ ω, τ ω ≤ T := ⟨N, fun _ ↦ le_rfl⟩
  -- Proof comment: this is the same constant-horizon specialization as above, but at the `L¹`
  -- level.
  simpa [τ, dyadicCeilApprox_constNatCast, stoppedValue_const] using
    (dyadic_condexp_tendsto_L1 hX hXrc hσ hτ hστ hσ_bdd hτ_bdd 0)

/-- Helper for Exercise 21.1.3: along the dyadic stopping-time sigma algebras of `σ`, reverse
Lévy converges back to the stopping-time sigma algebra `𝓕_σ` both almost surely and in `L¹`. -/
private theorem dyadicCondexp_tendsto_toStoppingTime
    [Filtration.IsRightContinuous ℱ]
    {g : Ω → ℝ} (hInt : Integrable g μ)
    {σ : Ω → NNReal}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal)) :
    (∀ᵐ ω ∂μ,
      Tendsto
        (fun n ↦ μ[g | (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace] ω)
        atTop
        (𝓝 (μ[g | hσ.measurableSpace] ω))) ∧
      Tendsto
        (fun n ↦
          eLpNorm
            (μ[g | (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace] -
              μ[g | hσ.measurableSpace])
            1 μ)
        atTop (𝓝 0) := by
  let mn : ℕ → MeasurableSpace Ω :=
    fun n ↦ (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace
  have hmn_le : ∀ n, mn n ≤ mΩ := by
    intro n
    exact (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace_le
  have hmn_anti : Antitone mn := by
    simpa [mn] using (dyadicCeilApprox_measurableSpace_antitone hσ)
  have hiInf : (⨅ n : ℕ, mn n) = hσ.measurableSpace := by
    simpa [mn] using (dyadicCeilApprox_measurableSpace_iInf_eq hσ)
  let S :
      (μ.trim hσ.measurableSpace_le).FiniteSpanningSetsIn
        {s | MeasurableSet[hσ.measurableSpace] s} :=
    (μ.trim hσ.measurableSpace_le).toFiniteSpanningSetsIn
  have hAe :
      ∀ᵐ ω ∂μ,
        Tendsto (fun n ↦ μ[g | mn n] ω) atTop (𝓝 (μ[g | hσ.measurableSpace] ω)) := by
    have hPiece :
        ∀ k : ℕ,
          ∀ᵐ ω ∂μ.restrict (S.set k),
            Tendsto (fun n ↦ μ[g | mn n] ω) atTop
              (𝓝 (μ[g | hσ.measurableSpace] ω)) := by
      intro k
      let s : Set Ω := S.set k
      have hs_hσ : MeasurableSet[hσ.measurableSpace] s := S.set_mem k
      have hs_fin : μ s < ∞ := by
        simpa [s, trim_measurableSet_eq hσ.measurableSpace_le hs_hσ] using S.finite k
      haveI : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs_fin.ne
      have hs_mn : ∀ n, MeasurableSet[mn n] s := by
        intro n
        have hσ_le_mn : hσ.measurableSpace ≤ mn n := by
          rw [← hiInf]
          exact iInf_le mn n
        exact hσ_le_mn _ hs_hσ
      have hInt_restrict : Integrable g (μ.restrict s) := hInt.restrict
      have hRestrictStage :
          ∀ n, (μ.restrict s)[g | mn n] =ᵐ[μ.restrict s] μ[g | mn n] := by
        intro n
        exact condExp_restrict_ae_eq_restrict (hmn_le n) (hs_mn n) hInt
      have hRestrictLimit :
          (μ.restrict s)[g | hσ.measurableSpace] =ᵐ[μ.restrict s] μ[g | hσ.measurableSpace] :=
        condExp_restrict_ae_eq_restrict hσ.measurableSpace_le hs_hσ hInt
      have hRestrictAe :
          ∀ᵐ ω ∂μ.restrict s,
            Tendsto (fun n ↦ (μ.restrict s)[g | mn n] ω) atTop
              (𝓝 ((μ.restrict s)[g | hσ.measurableSpace] ω)) := by
        -- Proof comment: on each finite `𝓕_σ`-measurable slice, the finite-measure reverse Lévy
        -- theorem applies directly to the antitone dyadic stopping-time sigma algebras.
        simpa [hiInf] using
          (tendsto_ae_condExp_iInf_of_antitone hmn_le hmn_anti hInt_restrict)
      have hAllRestrict :
          ∀ᵐ ω ∂μ.restrict s, ∀ n, (μ.restrict s)[g | mn n] ω = μ[g | mn n] ω := by
        exact ae_all_iff.2 hRestrictStage
      filter_upwards [hRestrictAe, hAllRestrict, hRestrictLimit] with ω hω hωeq hωlim
      have hFn :
          (fun n ↦ (μ.restrict s)[g | mn n] ω) =ᶠ[atTop] fun n ↦ μ[g | mn n] ω :=
        Filter.Eventually.of_forall fun n ↦ hωeq n
      have hω' :
          Tendsto (fun n ↦ μ[g | mn n] ω) atTop
            (𝓝 ((μ.restrict s)[g | hσ.measurableSpace] ω)) :=
        hω.congr' hFn
      simpa [hωlim] using hω'
    have hGlobal :
        ∀ᵐ ω ∂μ.restrict (⋃ k : ℕ, S.set k),
          Tendsto (fun n ↦ μ[g | mn n] ω) atTop (𝓝 (μ[g | hσ.measurableSpace] ω)) :=
      (ae_restrict_iUnion_iff (fun k : ℕ ↦ S.set k)
        (fun ω ↦
          Tendsto (fun n ↦ μ[g | mn n] ω) atTop
            (𝓝 (μ[g | hσ.measurableSpace] ω)))).2 hPiece
    -- Proof comment: the finite-slice reverse-Lévy statements glue back together across the
    -- countable `𝓕_σ`-measurable spanning family of the trimmed measure.
    simpa [S.spanning] using hGlobal
  have hL1 :
      Tendsto
        (fun n ↦ eLpNorm (μ[g | mn n] - μ[g | hσ.measurableSpace]) 1 μ)
        atTop (𝓝 0) := by
    -- Proof comment: the sigma-finite reassembly theorem upgrades the slice-by-slice reverse
    -- Lévy convergence to a global `L¹` limit.
    simpa [mn] using
      (dyadicCondexpSigmaFiniteReassembly hInt hσ.measurableSpace_le hmn_le hmn_anti hiInf S)
  exact ⟨by simpa [mn] using hAe, by simpa [mn] using hL1⟩

/-- Helper for Exercise 21.1.3: a right-continuous martingale preserves its initial expectation at
every bounded stopping time. -/
private lemma expectedStoppedValue_eq_initial_of_martingale_of_boundedStoppingTime
    [Filtration.IsRightContinuous ℱ]
    {X : NNReal → Ω → ℝ} (hX : Martingale X ℱ μ) (hXrc : HasRightContinuousPaths X)
    {σ : Ω → NNReal}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
    (hσ_bdd : ∃ T : NNReal, ∀ ω, σ ω ≤ T) :
    μ[stoppedValue X (fun ω ↦ (σ ω : ENNReal))] = μ[X 0] := by
  obtain ⟨T, hT⟩ := exists_uniform_bound_dyadicCeilApprox hσ_bdd
  let N : ℕ := Nat.ceil T
  let τm : ℕ → Ω → ENNReal := fun m ω ↦ (dyadicCeilApprox m σ ω : ENNReal)
  have hτm_stop : ∀ m, IsStoppingTime ℱ (τm m) := by
    intro m
    exact dyadicCeilApprox_isStoppingTime hσ m
  have hτm_count : ∀ m, (Set.range (τm m)).Countable := by
    intro m
    simpa [τm] using dyadicCeilApprox_countableRange m σ
  have hσ_le_N : ∀ ω, σ ω ≤ (N : NNReal) := by
    intro ω
    exact (self_le_dyadicCeilApprox 0 σ ω).trans <|
      (hT 0 ω).trans (by exact_mod_cast Nat.le_ceil T)
  have hτm_le_N : ∀ m ω, τm m ω ≤ (N : ENNReal) := by
    intro m ω
    have hle : dyadicCeilApprox m σ ω ≤ (N : NNReal) :=
      (hT m ω).trans (by exact_mod_cast Nat.le_ceil T)
    simpa [τm] using hle
  have hCondNat :
      ∀ m, stoppedValue X (τm m) =ᵐ[μ] μ[X N | (hτm_stop m).measurableSpace] := by
    intro m
    -- Proof comment: the same countable-range optional-sampling identity also holds at the
    -- integer terminal horizon `N`, which bounds every dyadic ceiling approximation uniformly.
    exact hX.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
      (hτm_stop m) (hτm_le_N m) (hτm_count m)
  have hAeTendsto :
      ∀ᵐ ω ∂μ,
        Tendsto (fun m ↦ stoppedValue X (τm m) ω) atTop
          (𝓝 (stoppedValue X (fun ω ↦ (σ ω : ENNReal)) ω)) := by
    -- Proof comment: the dyadic ceilings converge to `σ` from the right, so right continuity of
    -- the sample paths gives pointwise convergence of the stopped values.
    simpa [τm] using
      (dyadic_stoppedValue_tendsto_ae hX.supermartingale hXrc hσ hσ_bdd)
  have hCondTendsto :
      ∀ᵐ ω ∂μ,
        Tendsto (fun m ↦ μ[X N | (hτm_stop m).measurableSpace] ω) atTop
          (𝓝 (μ[X N | hσ.measurableSpace] ω)) := by
    -- Proof comment: reverse Lévy convergence applies to the fixed terminal slice `X N` along
    -- the dyadic stopping-time sigma algebras.
    simpa [τm] using
      (dyadicConstHorizon_condExp_tendsto_ae (X := X) hX.supermartingale hXrc hσ
        ⟨N, hσ_le_N⟩ N hσ_le_N)
  have hAllCond :
      ∀ᵐ ω ∂μ, ∀ m, stoppedValue X (τm m) ω = μ[X N | (hτm_stop m).measurableSpace] ω := by
    rw [ae_all_iff]
    intro m
    exact hCondNat m
  have hStoppedEqCond :
      stoppedValue X (fun ω ↦ (σ ω : ENNReal)) =ᵐ[μ] μ[X N | hσ.measurableSpace] := by
    filter_upwards [hAeTendsto, hCondTendsto, hAllCond] with ω hStop hCondLim hAllCondω
    have hStopToCond :
        Tendsto (fun m ↦ stoppedValue X (τm m) ω) atTop
          (𝓝 (μ[X N | hσ.measurableSpace] ω)) := by
      exact hCondLim.congr' (Filter.Eventually.of_forall fun m ↦ (hAllCondω m).symm)
    -- Proof comment: the dyadic stopped values and the dyadic terminal conditional expectations
    -- are termwise equal almost surely, so their pointwise limits must coincide.
    exact tendsto_nhds_unique hStop hStopToCond
  -- Proof comment: the exact stopped value is the terminal conditional expectation at the integer
  -- horizon `N`, so integrating it recovers the constant martingale expectation.
  calc
    μ[stoppedValue X (fun ω ↦ (σ ω : ENNReal))]
        = ∫ ω, μ[X N | hσ.measurableSpace] ω ∂μ := by
            exact integral_congr_ae hStoppedEqCond
    _ = μ[X N] := by
          simpa using
            (integral_condExp (μ := μ) (m := hσ.measurableSpace)
              (f := X N) hσ.measurableSpace_le)
    _ = μ[X 0] := by
          simpa [setIntegral_univ] using
            (hX.setIntegral_eq (show (0 : NNReal) ≤ (N : NNReal) by exact zero_le _)
              (s := Set.univ) MeasurableSet.univ).symm

/-- Helper for Exercise 21.1.3: if a measurable event belongs to the stopping-time sigma algebra
of `σ`, then choosing between `σ` and a later stopping time `τ` on that event still gives a
stopping time. -/
private lemma isStoppingTime_piecewise_of_mem_measurableSpace
    {σ τ : Ω → ENNReal}
    (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hστ : σ ≤ τ) {A : Set Ω} [DecidablePred (· ∈ A)]
    (hA : MeasurableSet[hσ.measurableSpace] A) :
    IsStoppingTime ℱ (A.piecewise τ σ) := by
  intro t
  change MeasurableSet[ℱ t] {ω | A.piecewise τ σ ω ≤ t}
  have hAσ : MeasurableSet[ℱ t] (A ∩ {ω | σ ω ≤ t}) := hA.2 t
  have hAτ :
      MeasurableSet[ℱ t] (A ∩ {ω | τ ω ≤ t}) := by
    -- Proof comment: on `{τ ≤ t}`, the smaller stop `σ` is automatically below `t`, so the
    -- `A`-part can be rewritten through the measurable slice `A ∩ {σ ≤ t}`.
    have hEq :
        A ∩ {ω | τ ω ≤ t} = (A ∩ {ω | σ ω ≤ t}) ∩ {ω | τ ω ≤ t} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · intro hω
        exact ⟨⟨hω.1, (hστ ω).trans hω.2⟩, hω.2⟩
      · intro hω
        exact ⟨hω.1.1, hω.2⟩
    rw [hEq]
    exact hAσ.inter (hτ t)
  have hAcσ :
      MeasurableSet[ℱ t] (Aᶜ ∩ {ω | σ ω ≤ t}) := by
    -- Proof comment: the complement slice is the measurable difference between `{σ ≤ t}` and its
    -- `A`-part.
    have hEq :
        Aᶜ ∩ {ω | σ ω ≤ t} = {ω | σ ω ≤ t} \ (A ∩ {ω | σ ω ≤ t}) := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_diff]
      constructor
      · intro hω
        exact ⟨hω.2, fun hAω ↦ hω.1 hAω.1⟩
      · intro hω
        exact ⟨fun hAω ↦ hω.2 ⟨hAω, hω.1⟩, hω.1⟩
    rw [hEq]
    exact (hσ t).diff hAσ
  -- Proof comment: the event `{A.piecewise τ σ ≤ t}` splits into the `A`-branch and the
  -- complement branch, and each branch is measurable at time `t`.
  have hEvent :
      {ω | A.piecewise τ σ ω ≤ t} =
        (A ∩ {ω | τ ω ≤ t}) ∪ (Aᶜ ∩ {ω | σ ω ≤ t}) := by
    ext ω
    by_cases hω : ω ∈ A <;> simp [Set.piecewise, hω]
  simpa [hEvent] using hAτ.union hAcσ

/-- Helper for Exercise 21.1.3: stopping along a piecewise-chosen finite time evaluates
piecewise. -/
private lemma stoppedValue_piecewise
    {X : NNReal → Ω → ℝ} {A : Set Ω} [DecidablePred (· ∈ A)]
    {σ τ : Ω → ENNReal} :
    stoppedValue X (A.piecewise τ σ) =
      A.piecewise (stoppedValue X τ) (stoppedValue X σ) := by
  -- Proof comment: `stoppedValue` is just evaluation at the chosen stopping time, so the
  -- piecewise split is pointwise tautological.
  ext ω
  by_cases hω : ω ∈ A <;> simp [Set.piecewise, stoppedValue, hω]

/-- Helper for Exercise 21.1.3: if two bounded stopping times already lie on the same dyadic
mesh, then the bounded optional-sampling inequality holds exactly between them. -/
private theorem dyadicAligned_optionalSampling
    {X : NNReal → Ω → ℝ} (hX : Supermartingale X ℱ μ) (hXrc : HasRightContinuousPaths X)
    {σ τ : Ω → NNReal}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
    (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal))
    (hστ : σ ≤ τ) (hτ_bdd : ∃ T : NNReal, ∀ ω, τ ω ≤ T)
    (n : ℕ)
    (hσ_fixed : dyadicCeilApprox n σ = σ)
    (hτ_fixed : dyadicCeilApprox n τ = τ) :
    μ[stoppedValue X (fun ω ↦ (τ ω : ENNReal)) | hσ.measurableSpace] ≤ᵐ[μ]
      stoppedValue X (fun ω ↦ (σ ω : ENNReal)) := by
  classical
  let sigmaInf : Ω → ENNReal := fun ω ↦ (σ ω : ENNReal)
  let tauInf : Ω → ENNReal := fun ω ↦ (τ ω : ENNReal)
  have hσ_bdd : ∃ T : NNReal, ∀ ω, σ ω ≤ T :=
    exists_bound_of_le_of_exists_bound hστ hτ_bdd
  have hσ_int : Integrable (stoppedValue X sigmaInf) μ := by
    simpa [sigmaInf, hσ_fixed] using
      integrable_stoppedValue_dyadicCeilApprox (X := X) hX hσ n hσ_bdd
  have hτ_int : Integrable (stoppedValue X tauInf) μ := by
    simpa [tauInf, hτ_fixed] using
      integrable_stoppedValue_dyadicCeilApprox (X := X) hX hτ n hτ_bdd
  have hSigmaMeas :
      StronglyMeasurable[hσ.measurableSpace] (stoppedValue X sigmaInf) := by
    -- Proof comment: right continuity upgrades adaptedness to the exact stopped-value
    -- measurability needed on the stopping-time sigma algebra.
    exact
      (measurableStoppedValue_of_adaptedRightContinuous
        (X := X) hX.1.adapted hXrc hσ).stronglyMeasurable
  have hCondMeas :
      StronglyMeasurable[hσ.measurableSpace]
        (μ[stoppedValue X tauInf | hσ.measurableSpace]) :=
    stronglyMeasurable_condExp
  have hLeTrim :
      μ[stoppedValue X tauInf | hσ.measurableSpace] ≤ᵐ[μ.trim hσ.measurableSpace_le]
        stoppedValue X sigmaInf := by
    refine MeasureTheory.ae_le_of_forall_setIntegral_le
      (integrable_condExp.trim hσ.measurableSpace_le hCondMeas)
      (hσ_int.trim hσ.measurableSpace_le hSigmaMeas) ?_
    intro A hA _hA_fin
    let ρ : Ω → NNReal := Set.piecewise A τ σ
    let rhoInf : Ω → ENNReal := fun ω ↦ (ρ ω : ENNReal)
    have hστInf : sigmaInf ≤ tauInf := by
      intro ω
      simpa [sigmaInf, tauInf] using hστ ω
    have hρ_stop : IsStoppingTime ℱ rhoInf := by
      -- Proof comment: gluing the later stop `τ` on an `𝓕_σ`-measurable set preserves the
      -- stopping-time property.
      have hRhoEq : rhoInf = Set.piecewise A tauInf sigmaInf := by
        funext ω
        by_cases hω : ω ∈ A
        · simp [rhoInf, ρ, sigmaInf, tauInf, Set.piecewise, hω]
        · simp [rhoInf, ρ, sigmaInf, tauInf, Set.piecewise, hω]
      rw [hRhoEq]
      exact isStoppingTime_piecewise_of_mem_measurableSpace hσ hτ hστInf hA
    have hσ_le_ρ : σ ≤ ρ := by
      intro ω
      by_cases hω : ω ∈ A
      · simpa [ρ, Set.piecewise, hω] using hστ ω
      · simp [ρ, Set.piecewise, hω]
    have hρ_bdd : ∃ T : NNReal, ∀ ω, ρ ω ≤ T := by
      rcases hτ_bdd with ⟨T, hT⟩
      refine ⟨T, ?_⟩
      intro ω
      by_cases hω : ω ∈ A
      · simpa [ρ, Set.piecewise, hω] using hT ω
      · simpa [ρ, Set.piecewise, hω] using (hστ ω).trans (hT ω)
    have hρ_fixed : dyadicCeilApprox n ρ = ρ := by
      funext ω
      by_cases hω : ω ∈ A
      · simpa [ρ, dyadicCeilApprox, hω] using congrFun hτ_fixed ω
      · simpa [ρ, dyadicCeilApprox, hω] using congrFun hσ_fixed ω
    have hρ_exp_le :
        μ[stoppedValue X rhoInf] ≤ μ[stoppedValue X sigmaInf] := by
      -- Proof comment: on a common dyadic mesh, the dyadic expected-value theorem is already the
      -- exact expected-value theorem.
      simpa [rhoInf, sigmaInf, hρ_fixed, hσ_fixed] using
        dyadicExpectedStoppedValue_mono (X := X) hX hσ hρ_stop hσ_le_ρ hρ_bdd n
    have hρ_piecewise :
        stoppedValue X rhoInf =
          Set.piecewise A (stoppedValue X tauInf) (stoppedValue X sigmaInf) := by
      -- Proof comment: the glued stop evaluates to `τ` on `A` and to `σ` on `Aᶜ`.
      ext ω
      by_cases hω : ω ∈ A
      · simp [rhoInf, ρ, sigmaInf, tauInf, Set.piecewise, stoppedValue, hω]
      · simp [rhoInf, ρ, sigmaInf, tauInf, Set.piecewise, stoppedValue, hω]
    have hρ_split :
        μ[stoppedValue X rhoInf] =
          ∫ ω in A, stoppedValue X tauInf ω ∂μ +
            ∫ ω in Aᶜ, stoppedValue X sigmaInf ω ∂μ := by
      -- Proof comment: split the glued stopped value over the measurable partition `A ∪ Aᶜ`.
      calc
        μ[stoppedValue X rhoInf]
            = ∫ ω, stoppedValue X rhoInf ω ∂μ := rfl
        _ = ∫ ω, Set.piecewise A (stoppedValue X tauInf) (stoppedValue X sigmaInf) ω ∂μ := by
              simpa using congrArg (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) hρ_piecewise
        _ =
            ∫ ω in A, stoppedValue X tauInf ω ∂μ +
              ∫ ω in Aᶜ, stoppedValue X sigmaInf ω ∂μ := by
                simpa using
                  (integral_piecewise (hσ.measurableSpace_le _ hA)
                    hτ_int.integrableOn hσ_int.integrableOn)
    have hσ_split :
        μ[stoppedValue X sigmaInf] =
          ∫ ω in A, stoppedValue X sigmaInf ω ∂μ +
            ∫ ω in Aᶜ, stoppedValue X sigmaInf ω ∂μ := by
      -- Proof comment: split the reference stopped value of `σ` over the same partition.
      simpa [setIntegral_univ] using
        (integral_add_compl (hσ.measurableSpace_le _ hA) hσ_int).symm
    have hSetLeStopped :
        ∫ ω in A, stoppedValue X tauInf ω ∂μ ≤
          ∫ ω in A, stoppedValue X sigmaInf ω ∂μ := by
      -- Proof comment: compare the glued-stop expectation with the exact `σ`-stop expectation and
      -- cancel the common complement contribution.
      linarith [hρ_exp_le, hρ_split, hσ_split]
    have hLeftTrim :
        ∫ ω in A, μ[stoppedValue X tauInf | hσ.measurableSpace] ω ∂μ.trim hσ.measurableSpace_le =
          ∫ ω in A, stoppedValue X tauInf ω ∂μ := by
      calc
        ∫ ω in A, μ[stoppedValue X tauInf | hσ.measurableSpace] ω ∂μ.trim hσ.measurableSpace_le
            = ∫ ω in A, μ[stoppedValue X tauInf | hσ.measurableSpace] ω ∂μ := by
                symm
                exact MeasureTheory.setIntegral_trim hσ.measurableSpace_le hCondMeas hA
        _ = ∫ ω in A, stoppedValue X tauInf ω ∂μ := by
              simpa [tauInf] using
                (MeasureTheory.setIntegral_condExp hσ.measurableSpace_le hτ_int hA)
    have hRightTrim :
        ∫ ω in A, stoppedValue X sigmaInf ω ∂μ =
          ∫ ω in A, stoppedValue X sigmaInf ω ∂μ.trim hσ.measurableSpace_le := by
      exact MeasureTheory.setIntegral_trim hσ.measurableSpace_le hSigmaMeas hA
    calc
      ∫ ω in A, μ[stoppedValue X tauInf | hσ.measurableSpace] ω ∂μ.trim hσ.measurableSpace_le
          = ∫ ω in A, stoppedValue X tauInf ω ∂μ := hLeftTrim
      _ ≤ ∫ ω in A, stoppedValue X sigmaInf ω ∂μ := hSetLeStopped
      _ = ∫ ω in A, stoppedValue X sigmaInf ω ∂μ.trim hσ.measurableSpace_le := hRightTrim
  exact
    (MeasureTheory.StronglyMeasurable.ae_le_trim_iff
      hσ.measurableSpace_le hCondMeas hSigmaMeas).mp hLeTrim

/-- Helper for Exercise 21.1.3: for a fixed dyadic terminal approximation `τ^m`, letting the
conditioning stop `σ^n` converge down to `σ` yields the exact conditional inequality. -/
private theorem dyadicStoppedValue_condExp_ae_le
    [Filtration.IsRightContinuous ℱ] :
    ∀ {X : NNReal → Ω → ℝ} (_ : Supermartingale X ℱ μ) (_ : HasRightContinuousPaths X)
      {σ τ : Ω → NNReal}
      (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
      (_ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal))
      (_ : σ ≤ τ)
      (_ : ∃ T : NNReal, ∀ ω, σ ω ≤ T)
      (_ : ∃ T : NNReal, ∀ ω, τ ω ≤ T)
      (m : ℕ),
      μ[stoppedValue X (fun ω ↦ (dyadicCeilApprox m τ ω : ENNReal)) | hσ.measurableSpace] ≤ᵐ[μ]
        stoppedValue X (fun ω ↦ (σ ω : ENNReal)) := by
  intro X hX hXrc σ τ hσ hτ hστ hσ_bdd hτ_bdd m
  let tauM : Ω → NNReal := dyadicCeilApprox m τ
  let tauMInf : Ω → ENNReal := fun ω ↦ (tauM ω : ENNReal)
  have hτm : IsStoppingTime ℱ tauMInf := dyadicCeilApprox_isStoppingTime hτ m
  have hτm_bdd : ∃ T : NNReal, ∀ ω, tauM ω ≤ T :=
    by
      rcases exists_uniform_bound_dyadicCeilApprox hτ_bdd with ⟨T, hT⟩
      exact ⟨T, hT m⟩
  have hStage :
      ∀ n, m ≤ n →
        μ[stoppedValue X tauMInf | (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace] ≤ᵐ[μ]
          stoppedValue X (fun ω ↦ (dyadicCeilApprox n σ ω : ENNReal)) := by
    intro n hmn
    let sigmaN : Ω → NNReal := dyadicCeilApprox n σ
    letI : SigmaFiniteFiltration μ (dyadicRowFiltration (ℱ := ℱ) n) := by
      refine ⟨fun k => ?_⟩
      simpa [dyadicRowFiltration] using
        (inferInstance : SigmaFinite (μ.trim (ℱ.le (dyadicTime n k))))
    have hσ_idx :
        IsStoppingTime (dyadicRowFiltration (ℱ := ℱ) n) (dyadicCeilIndex n σ) :=
      dyadicCeilIndex_isStoppingTime (ℱ := ℱ) hσ n
    have hτ_idx :
        IsStoppingTime (dyadicRowFiltration (ℱ := ℱ) n) (dyadicCeilIndex n tauM) :=
      dyadicCeilIndex_isStoppingTime (ℱ := ℱ) hτm n
    have hσn_le_tauM : sigmaN ≤ tauM := by
      intro ω
      calc
        dyadicCeilApprox n σ ω ≤ dyadicCeilApprox n τ ω :=
          dyadicCeilApprox_mono n hστ ω
        _ ≤ dyadicCeilApprox m τ ω :=
          dyadicCeilApprox_antitone τ hmn ω
    have hσ_le_tauM : σ ≤ tauM := by
      intro ω
      exact (self_le_dyadicCeilApprox n σ ω).trans (hσn_le_tauM ω)
    have hidx_le : dyadicCeilIndex n σ ≤ dyadicCeilIndex n tauM :=
      dyadicCeilIndex_mono hσ_le_tauM n
    obtain ⟨N, hτm_le_N⟩ := exists_nat_bound_of_exists_bound hτm_bdd
    have hdisc :=
      supermartingale_condExp_stoppedValue_le_of_le_of_bounded
        (X := dyadicRowProcess X n) (ℱ := dyadicRowFiltration (ℱ := ℱ) n) (μ := μ)
        (dyadicRow_supermartingale (ℱ := ℱ) (μ := μ) hX n)
        hσ_idx hτ_idx hidx_le
        (dyadicCeilIndex_le_of_natBound (n := n) (N := N) hτm_le_N)
    have hSigmaSpace :
        hσ_idx.measurableSpace =
          (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace :=
      dyadicCeilIndex_measurableSpace_eq (ℱ := ℱ) hσ n
    -- Proof comment: for `n ≥ m`, the discrete bounded optional-sampling theorem applies on the
    -- sampled dyadic row, and the two stopped values rewrite back to the ambient dyadic stops.
    rw [dyadicRow_stoppedValue_eq_dyadicCeilApprox (X := X) (n := n) (σ := tauM),
      dyadicRow_stoppedValue_eq_dyadicCeilApprox (X := X) (n := n) (σ := σ)] at hdisc
    simpa [hSigmaSpace, tauMInf, tauM, sigmaN, dyadicCeilApprox_dyadicCeilApprox m n hmn τ]
      using hdisc
  have hCondTendsto :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n ↦
            μ[stoppedValue X (fun ω' ↦ (dyadicCeilApprox m τ ω' : ENNReal)) |
              (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace] ω)
          atTop
          (𝓝 (μ[stoppedValue X tauMInf | hσ.measurableSpace] ω)) := by
    simpa [tauMInf, tauM] using
      dyadic_condexp_tendsto_ae hX hXrc hσ hτ hστ hσ_bdd hτ_bdd m
  have hStopTendsto :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n ↦ stoppedValue X (fun ω' ↦ (dyadicCeilApprox n σ ω' : ENNReal)) ω)
          atTop
          (𝓝 (stoppedValue X (fun ω' ↦ (σ ω' : ENNReal)) ω)) :=
    dyadic_stoppedValue_tendsto_ae hX hXrc hσ hσ_bdd
  have hAllStage :
      ∀ᵐ ω ∂μ,
        ∀ n, m ≤ n →
          μ[stoppedValue X tauMInf | (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace] ω ≤
            stoppedValue X (fun ω' ↦ (dyadicCeilApprox n σ ω' : ENNReal)) ω := by
    rw [ae_all_iff]
    intro n
    by_cases hmn : m ≤ n
    · filter_upwards [hStage n hmn] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun ω hle ↦
        False.elim ((not_le_of_gt <| lt_of_not_ge hmn) hle)
  filter_upwards [hCondTendsto, hStopTendsto, hAllStage] with ω hCond hStop hAll
  let pairSeq : ℕ → ℝ × ℝ := fun n ↦
    (μ[stoppedValue X tauMInf | (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace] ω,
      stoppedValue X (fun ω' ↦ (dyadicCeilApprox n σ ω' : ENNReal)) ω)
  have hPair :
      Tendsto pairSeq atTop
        (𝓝
          (μ[stoppedValue X tauMInf | hσ.measurableSpace] ω,
            stoppedValue X (fun ω' ↦ (σ ω' : ENNReal)) ω)) := by
    simpa [pairSeq, nhds_prod_eq] using hCond.prodMk hStop
  have hEventuallyLe :
      ∀ᶠ n in atTop, pairSeq n ∈ {p : ℝ × ℝ | p.1 ≤ p.2} := by
    filter_upwards [Filter.eventually_ge_atTop m] with n hn
    exact hAll n hn
  have hClosed : IsClosed {p : ℝ × ℝ | p.1 ≤ p.2} :=
    isClosed_le continuous_fst continuous_snd
  exact hClosed.mem_of_tendsto hPair hEventuallyLe

/-- Helper for Exercise 21.1.3: conditioning the fixed-horizon dyadic defect
`X_{σⁿ} - μ[X N | 𝓕_{σⁿ}]` back to `𝓕_σ` is bounded by the exact defect
`X_σ - μ[X N | 𝓕_σ]`. -/
private lemma dyadicStoppedValueDefect_condExp_ae_le
    [Filtration.IsRightContinuous ℱ] :
    ∀ {X : NNReal → Ω → ℝ} (_ : Supermartingale X ℱ μ) (_ : HasRightContinuousPaths X)
      {σ : Ω → NNReal}
      (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
      (_ : ∃ T : NNReal, ∀ ω, σ ω ≤ T)
      (N : ℕ) (_ : ∀ ω, σ ω ≤ (N : NNReal)),
      ∀ n,
        μ[(fun ω ↦
          stoppedValue X (fun ω' ↦ (dyadicCeilApprox n σ ω' : ENNReal)) ω -
            μ[X N | (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace] ω)
          | hσ.measurableSpace] ≤ᵐ[μ]
          fun ω ↦
            stoppedValue X (fun ω' ↦ (σ ω' : ENNReal)) ω - μ[X N | hσ.measurableSpace] ω := by
  intro X hX hXrc σ hσ hσ_bdd N hσ_le_N n
  let sigmaN : Ω → ENNReal := fun ω ↦ (dyadicCeilApprox n σ ω : ENNReal)
  let sigma : Ω → ENNReal := fun ω ↦ (σ ω : ENNReal)
  have hσn : IsStoppingTime ℱ sigmaN := dyadicCeilApprox_isStoppingTime hσ n
  have hSigmaNInt : Integrable (stoppedValue X sigmaN) μ := by
    -- Proof comment: bounded dyadic stopped values are already integrable.
    simpa [sigmaN] using
      integrable_stoppedValue_dyadicCeilApprox (X := X) hX hσ n hσ_bdd
  have hCondInt :
      Integrable (μ[X N | hσn.measurableSpace]) μ := integrable_condExp
  have hσ_le_sigmaN : sigma ≤ sigmaN := by
    intro ω
    change (σ ω : ENNReal) ≤ (dyadicCeilApprox n σ ω : ENNReal)
    exact_mod_cast self_le_dyadicCeilApprox n σ ω
  have hMeas_le : hσ.measurableSpace ≤ hσn.measurableSpace :=
    hσ.measurableSpace_mono hσn hσ_le_sigmaN
  have hStoppedLe :
      μ[stoppedValue X sigmaN | hσ.measurableSpace] ≤ᵐ[μ] stoppedValue X sigma := by
    -- Proof comment: this is the exact bounded optional-sampling inequality with terminal stop
    -- `σⁿ` and conditioning stop `σ`.
    simpa [sigmaN, sigma] using
      (dyadicStoppedValue_condExp_ae_le (X := X) hX hXrc hσ hσ (σ := σ) (τ := σ)
        (show σ ≤ σ by intro ω; exact le_rfl) hσ_bdd hσ_bdd n)
  have hTower :
      μ[μ[X N | hσn.measurableSpace] | hσ.measurableSpace] =ᵐ[μ]
        μ[X N | hσ.measurableSpace] := by
    -- Proof comment: conditioning first on `𝓕_{σⁿ}` and then on the smaller `𝓕_σ`
    -- collapses by the tower property.
    exact condExp_condExp_of_le hMeas_le hσn.measurableSpace_le
  -- Proof comment: linearity of conditional expectation rewrites the defect, after which the
  -- stopped-value inequality and the tower identity compare the two sides termwise.
  refine (condExp_sub hSigmaNInt hCondInt hσ.measurableSpace).trans_le ?_
  filter_upwards [hStoppedLe, hTower] with ω hω_stop hω_tower
  simpa [hω_tower] using sub_le_sub_right hω_stop (μ[X N | hσ.measurableSpace] ω)

/-- Helper for Exercise 21.1.3: along the dyadic tower, conditioning an earlier dyadic stopped
value back to a finer dyadic stopping-time sigma algebra is dominated by the finer stopped value.
-/
private lemma dyadicStoppedValue_condExp_ae_le_toFiner
    {X : NNReal → Ω → ℝ} (hX : Supermartingale X ℱ μ)
    {σ : Ω → NNReal}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
    (hσ_bdd : ∃ T : NNReal, ∀ ω, σ ω ≤ T)
    (n m : ℕ) (hnm : n ≤ m) :
    μ[stoppedValue X (fun ω ↦ (dyadicCeilApprox n σ ω : ENNReal)) |
        (dyadicCeilApprox_isStoppingTime hσ m).measurableSpace] ≤ᵐ[μ]
      stoppedValue X (fun ω ↦ (dyadicCeilApprox m σ ω : ENNReal)) := by
  let sigmaN : Ω → NNReal := dyadicCeilApprox n σ
  let sigmaNInf : Ω → ENNReal := fun ω ↦ (sigmaN ω : ENNReal)
  let sigmaM : Ω → NNReal := dyadicCeilApprox m σ
  have hσn : IsStoppingTime ℱ sigmaNInf := dyadicCeilApprox_isStoppingTime hσ n
  have hσn_bdd : ∃ T : NNReal, ∀ ω, sigmaN ω ≤ T := by
    rcases exists_uniform_bound_dyadicCeilApprox hσ_bdd with ⟨T, hT⟩
    exact ⟨T, hT n⟩
  letI : SigmaFiniteFiltration μ (dyadicRowFiltration (ℱ := ℱ) m) := by
    refine ⟨fun k => ?_⟩
    simpa [dyadicRowFiltration] using
      (inferInstance : SigmaFinite (μ.trim (ℱ.le (dyadicTime m k))))
  have hσm_idx :
      IsStoppingTime (dyadicRowFiltration (ℱ := ℱ) m) (dyadicCeilIndex m σ) :=
    dyadicCeilIndex_isStoppingTime (ℱ := ℱ) hσ m
  have hσn_idx :
      IsStoppingTime (dyadicRowFiltration (ℱ := ℱ) m) (dyadicCeilIndex m sigmaN) :=
    dyadicCeilIndex_isStoppingTime (ℱ := ℱ) hσn m
  have hσ_le_sigmaN : σ ≤ sigmaN := by
    intro ω
    exact self_le_dyadicCeilApprox n σ ω
  have hidx_le : dyadicCeilIndex m σ ≤ dyadicCeilIndex m sigmaN :=
    dyadicCeilIndex_mono hσ_le_sigmaN m
  obtain ⟨N, hσn_le_N⟩ := exists_nat_bound_of_exists_bound hσn_bdd
  have hdisc :=
    supermartingale_condExp_stoppedValue_le_of_le_of_bounded
      (X := dyadicRowProcess X m) (ℱ := dyadicRowFiltration (ℱ := ℱ) m) (μ := μ)
      (dyadicRow_supermartingale (ℱ := ℱ) (μ := μ) hX m)
      hσm_idx hσn_idx hidx_le
      (dyadicCeilIndex_le_of_natBound (n := m) (N := N) hσn_le_N)
  have hSigmaSpace :
      hσm_idx.measurableSpace =
        (dyadicCeilApprox_isStoppingTime hσ m).measurableSpace :=
    dyadicCeilIndex_measurableSpace_eq (ℱ := ℱ) hσ m
  -- Proof comment: both stops already live on the same dyadic row `m`, so the discrete bounded
  -- optional-sampling theorem applies before rewriting back to the ambient stopped values.
  rw [dyadicRow_stoppedValue_eq_dyadicCeilApprox (X := X) (n := m) (σ := sigmaN),
    dyadicRow_stoppedValue_eq_dyadicCeilApprox (X := X) (n := m) (σ := σ)] at hdisc
  simpa [hSigmaSpace, sigmaNInf, sigmaN, sigmaM, dyadicCeilApprox_dyadicCeilApprox n m hnm σ]
    using hdisc

/-- Helper for Exercise 21.1.3: the fixed-horizon dyadic defect sequence is integrable,
nonnegative, and uniformly bounded in expectation. -/
private lemma dyadicStoppedValueDefect_expectationBound_noRightContinuousFiltration :
    ∀ {X : NNReal → Ω → ℝ} (_ : Supermartingale X ℱ μ)
      {σ : Ω → NNReal}
      (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
      (_ : ∃ T : NNReal, ∀ ω, σ ω ≤ T)
      (N : ℕ) (_ : ∀ ω, σ ω ≤ (N : NNReal)),
      ∀ n,
        Integrable
            (fun ω ↦
              stoppedValue X (fun ω' ↦ (dyadicCeilApprox n σ ω' : ENNReal)) ω -
                μ[X N | (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace] ω) μ ∧
          (0 ≤ᵐ[μ]
            fun ω ↦
              stoppedValue X (fun ω' ↦ (dyadicCeilApprox n σ ω' : ENNReal)) ω -
                μ[X N | (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace] ω) ∧
            μ[fun ω ↦
              stoppedValue X (fun ω' ↦ (dyadicCeilApprox n σ ω' : ENNReal)) ω -
                μ[X N | (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace] ω] ≤
              μ[X 0] - μ[X N] := by
  intro X hX σ hσ hσ_bdd N hσ_le_N n
  let sigmaN : Ω → NNReal := dyadicCeilApprox n σ
  let sigmaNInf : Ω → ENNReal := fun ω ↦ (sigmaN ω : ENNReal)
  let defect : Ω → ℝ := fun ω ↦
    stoppedValue X sigmaNInf ω - μ[X N | (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace] ω
  have hσn : IsStoppingTime ℱ sigmaNInf := dyadicCeilApprox_isStoppingTime hσ n
  have hSigmaNInt : Integrable (stoppedValue X sigmaNInf) μ := by
    -- Proof comment: bounded dyadic stopped values are already integrable.
    simpa [sigmaN, sigmaNInf] using
      integrable_stoppedValue_dyadicCeilApprox (X := X) hX hσ n hσ_bdd
  have hCondInt :
      Integrable (μ[X N | hσn.measurableSpace]) μ := integrable_condExp
  have hDefectInt : Integrable defect μ := hSigmaNInt.sub hCondInt
  have hσn_le_N : sigmaN ≤ fun _ ↦ (N : NNReal) := by
    intro ω
    calc
      sigmaN ω = dyadicCeilApprox n σ ω := rfl
      _ ≤ dyadicCeilApprox n (fun _ : Ω ↦ (N : NNReal)) ω :=
        dyadicCeilApprox_mono n hσ_le_N ω
      _ = N := by simpa [dyadicCeilApprox_constNatCast]
  have hσn_bdd : ∃ T : NNReal, ∀ ω, sigmaN ω ≤ T := ⟨N, hσn_le_N⟩
  have hCondLeStopped :
      μ[X N | hσn.measurableSpace] ≤ᵐ[μ] stoppedValue X sigmaNInf := by
    letI : SigmaFiniteFiltration μ (dyadicRowFiltration (ℱ := ℱ) n) := by
      refine ⟨fun k => ?_⟩
      simpa [dyadicRowFiltration] using
        (inferInstance : SigmaFinite (μ.trim (ℱ.le (dyadicTime n k))))
    let τ : Ω → NNReal := fun _ ↦ (N : NNReal)
    have hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal) :=
      isStoppingTime_const ℱ (N : NNReal)
    have hσ_idx :
        IsStoppingTime (dyadicRowFiltration (ℱ := ℱ) n) (dyadicCeilIndex n σ) :=
      dyadicCeilIndex_isStoppingTime (ℱ := ℱ) hσ n
    have hτ_idx :
        IsStoppingTime (dyadicRowFiltration (ℱ := ℱ) n) (dyadicCeilIndex n τ) :=
      dyadicCeilIndex_isStoppingTime (ℱ := ℱ) hτ n
    have hidx_le : dyadicCeilIndex n σ ≤ dyadicCeilIndex n τ :=
      dyadicCeilIndex_mono hσ_le_N n
    have hdisc :=
      supermartingale_condExp_stoppedValue_le_of_le_of_bounded
        (X := dyadicRowProcess X n) (ℱ := dyadicRowFiltration (ℱ := ℱ) n) (μ := μ)
        (dyadicRow_supermartingale (ℱ := ℱ) (μ := μ) hX n)
        hσ_idx hτ_idx hidx_le
        (dyadicCeilIndex_le_of_natBound (n := n) (N := N) fun _ ↦ le_rfl)
    have hSigmaSpace :
        hσ_idx.measurableSpace =
          (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace :=
      dyadicCeilIndex_measurableSpace_eq (ℱ := ℱ) hσ n
    -- Proof comment: the bounded discrete optional-sampling inequality on the `n`-th dyadic row
    -- already gives the nonnegativity of the defect without any filtration right continuity.
    rw [dyadicRow_stoppedValue_eq_dyadicCeilApprox (X := X) (n := n) (σ := τ),
      dyadicRow_stoppedValue_eq_dyadicCeilApprox (X := X) (n := n) (σ := σ)] at hdisc
    simpa [sigmaN, sigmaNInf, τ, hSigmaSpace, dyadicCeilApprox_constNatCast, stoppedValue_const]
      using hdisc
  have hDefectNonneg : 0 ≤ᵐ[μ] defect := by
    filter_upwards [hCondLeStopped] with ω hω
    exact sub_nonneg.mpr hω
  have hStoppedExpLe : μ[stoppedValue X sigmaNInf] ≤ μ[X 0] := by
    let zeroStop : Ω → NNReal := fun _ ↦ 0
    have hZero : IsStoppingTime ℱ fun ω ↦ (zeroStop ω : ENNReal) :=
      isStoppingTime_const ℱ (0 : NNReal)
    have hzero_le_sigma : zeroStop ≤ σ := by
      intro ω
      exact zero_le _
    have hZeroFixed : dyadicCeilApprox n zeroStop = zeroStop := by
      simpa [zeroStop] using (dyadicCeilApprox_constNatCast (Ω := Ω) n 0)
    -- Proof comment: compare the dyadic stop `σⁿ` with the constant initial stop `0`.
    simpa [sigmaN, sigmaNInf, zeroStop, hZeroFixed, stoppedValue_const] using
      (dyadicExpectedStoppedValue_mono (X := X) hX hZero hσ hzero_le_sigma hσ_bdd n)
  have hDefectIntegral :
      μ[defect] = μ[stoppedValue X sigmaNInf] - μ[X N] := by
    -- Proof comment: integrate the defect and collapse the conditional-expectation term.
    calc
      μ[defect]
          = μ[stoppedValue X sigmaNInf] -
              ∫ ω, μ[X N | hσn.measurableSpace] ω ∂μ := by
                simp [defect, integral_sub hSigmaNInt hCondInt]
      _ = μ[stoppedValue X sigmaNInf] - μ[X N] := by
            rw [integral_condExp (μ := μ) (m := hσn.measurableSpace) (f := X N)
              hσn.measurableSpace_le]
  have hBound : μ[defect] ≤ μ[X 0] - μ[X N] := by
    linarith [hDefectIntegral, hStoppedExpLe]
  exact ⟨hDefectInt, hDefectNonneg, by simpa [defect] using hBound⟩

/-- Helper for Exercise 21.1.3: the fixed-horizon dyadic defect sequence is integrable,
nonnegative, and uniformly bounded in expectation. -/
private lemma dyadicStoppedValueDefect_expectation_bound
    [Filtration.IsRightContinuous ℱ] :
    ∀ {X : NNReal → Ω → ℝ} (_ : Supermartingale X ℱ μ) (_ : HasRightContinuousPaths X)
      {σ : Ω → NNReal}
      (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
      (_ : ∃ T : NNReal, ∀ ω, σ ω ≤ T)
      (N : ℕ) (_ : ∀ ω, σ ω ≤ (N : NNReal)),
      ∀ n,
        Integrable
            (fun ω ↦
              stoppedValue X (fun ω' ↦ (dyadicCeilApprox n σ ω' : ENNReal)) ω -
                μ[X N | (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace] ω) μ ∧
          (0 ≤ᵐ[μ]
            fun ω ↦
              stoppedValue X (fun ω' ↦ (dyadicCeilApprox n σ ω' : ENNReal)) ω -
                μ[X N | (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace] ω) ∧
            μ[fun ω ↦
              stoppedValue X (fun ω' ↦ (dyadicCeilApprox n σ ω' : ENNReal)) ω -
                μ[X N | (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace] ω] ≤
              μ[X 0] - μ[X N] := by
  intro X hX _hXrc σ hσ hσ_bdd N hσ_le_N n
  -- Route correction: the nonnegative defect estimate is dyadic-row/discrete and does not need
  -- filtration right continuity; keep the old wrapper only for downstream callers.
  simpa using
    (dyadicStoppedValueDefect_expectationBound_noRightContinuousFiltration
      (X := X) hX hσ hσ_bdd N hσ_le_N n)

/-- Helper for Exercise 21.1.3: for a bounded stopping time `σ`, the exact stopped value `X_σ` is
integrable and the expectations of the dyadic stopped values `X_{σⁿ}` converge to `E[X_σ]`. -/
private lemma dyadicStoppedValue_expectation_tendsto
    [Filtration.IsRightContinuous ℱ] :
    ∀ {X : NNReal → Ω → ℝ} (_ : Supermartingale X ℱ μ) (_ : HasRightContinuousPaths X)
      {σ : Ω → NNReal}
      (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
      (_ : ∃ T : NNReal, ∀ ω, σ ω ≤ T),
      Integrable (stoppedValue X (fun ω ↦ (σ ω : ENNReal))) μ ∧
        Tendsto
          (fun n ↦ μ[stoppedValue X (fun ω ↦ (dyadicCeilApprox n σ ω : ENNReal))])
          atTop
          (𝓝 μ[stoppedValue X (fun ω ↦ (σ ω : ENNReal))]) := by
  intro X hX hXrc σ hσ hσ_bdd
  obtain ⟨N, hσ_le_N⟩ := exists_nat_bound_of_exists_bound hσ_bdd
  let A : Ω → ℝ := stoppedValue X (fun ω ↦ (σ ω : ENNReal))
  let B : Ω → ℝ := μ[X N | hσ.measurableSpace]
  let D : Ω → ℝ := fun ω ↦ A ω - B ω
  let Aₙ : ℕ → Ω → ℝ :=
    fun n ↦ stoppedValue X (fun ω ↦ (dyadicCeilApprox n σ ω : ENNReal))
  let Bₙ : ℕ → Ω → ℝ :=
    fun n ↦ μ[X N | (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace]
  let Dₙ : ℕ → Ω → ℝ := fun n ω ↦ Aₙ n ω - Bₙ n ω
  have hDefect :
      ∀ n,
        Integrable (Dₙ n) μ ∧
          (0 ≤ᵐ[μ] Dₙ n) ∧ μ[Dₙ n] ≤ μ[X 0] - μ[X N] := by
    intro n
    -- Proof comment: the dyadic defect helper already packages integrability, nonnegativity,
    -- and the uniform expectation bound at the fixed horizon `N`.
    simpa [Aₙ, Bₙ, Dₙ] using
      (dyadicStoppedValueDefect_expectation_bound (X := X) hX hXrc hσ hσ_bdd N hσ_le_N n)
  have hA_tendsto :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Aₙ n ω) atTop (𝓝 (A ω)) := by
    -- Proof comment: right continuity transports the dyadic stopping-time approximation to the
    -- exact stopped value.
    simpa [Aₙ, A] using
      (dyadic_stoppedValue_tendsto_ae (X := X) hX hXrc hσ hσ_bdd)
  have hB_tendsto :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Bₙ n ω) atTop (𝓝 (B ω)) := by
    -- Proof comment: reverse-Lévy convergence along the dyadic stopping-time sigma algebras
    -- handles the fixed terminal value `X N`.
    simpa [Bₙ, B] using
      (dyadicConstHorizon_condExp_tendsto_ae (X := X) hX hXrc hσ hσ_bdd N hσ_le_N)
  have hD_tendsto :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Dₙ n ω) atTop (𝓝 (D ω)) := by
    -- Proof comment: subtract the two pointwise convergent pieces in the fixed-horizon defect
    -- normal form.
    filter_upwards [hA_tendsto, hB_tendsto] with ω hAω hBω
    simpa [Dₙ, D] using hAω.sub hBω
  have hD_nonneg : 0 ≤ᵐ[μ] D := ae_nonneg_limit (fun n ↦ (hDefect n).2.1) hD_tendsto
  have hD_aestrong : AEStronglyMeasurable D μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n ↦ (hDefect n).1.aestronglyMeasurable) hD_tendsto
  have hFatou :
      ∫⁻ ω, ENNReal.ofReal (D ω) ∂μ ≤
        liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal (Dₙ n ω) ∂μ) atTop := by
    -- Proof comment: Fatou upgrades the nonnegative dyadic defect bounds to the exact defect.
    calc
      ∫⁻ ω, ENNReal.ofReal (D ω) ∂μ
          = ∫⁻ ω, liminf (fun n ↦ ENNReal.ofReal (Dₙ n ω)) atTop ∂μ := by
              refine lintegral_congr_ae ?_
              filter_upwards [hD_tendsto] with ω hω
              exact ((ENNReal.continuous_ofReal.tendsto (D ω)).comp hω).liminf_eq.symm
      _ ≤ liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal (Dₙ n ω) ∂μ) atTop := by
            refine MeasureTheory.lintegral_liminf_le' ?_
            intro n
            exact ((hDefect n).1.aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have hEventuallyBound :
      ∀ᶠ n in atTop,
        ∫⁻ ω, ENNReal.ofReal (Dₙ n ω) ∂μ ≤ ENNReal.ofReal (μ[X 0] - μ[X N]) := by
    filter_upwards with n
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hDefect n).1 (hDefect n).2.1]
    exact ENNReal.ofReal_le_ofReal (hDefect n).2.2
  have hLiminf_ne_top :
      liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal (Dₙ n ω) ∂μ) atTop ≠ ⊤ := by
    have hLiminf_le :
        liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal (Dₙ n ω) ∂μ) atTop ≤
          ENNReal.ofReal (μ[X 0] - μ[X N]) :=
      Filter.liminf_le_of_frequently_le' hEventuallyBound.frequently
    exact ne_top_of_le_ne_top (b := ENNReal.ofReal (μ[X 0] - μ[X N]))
      ENNReal.ofReal_ne_top hLiminf_le
  have hD_lintegral_ne_top :
      ∫⁻ ω, ENNReal.ofReal (D ω) ∂μ ≠ ⊤ := by
    exact ne_top_of_le_ne_top hLiminf_ne_top hFatou
  have hD_int : Integrable D μ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hD_aestrong hD_nonneg).1
      hD_lintegral_ne_top
  have hB_int : Integrable B μ := integrable_condExp
  have hD_int_nonneg : 0 ≤ μ[D] := integral_nonneg_of_ae hD_nonneg
  have hIntegralLe :
      ∀ n, μ[Dₙ n] ≤ μ[D] := by
    intro n
    have hCondLe :
        μ[Dₙ n | hσ.measurableSpace] ≤ᵐ[μ] D := by
      -- Proof comment: condition the dyadic defect back to `𝓕_σ`, then compare it to the exact
      -- defect using the fixed-horizon defect inequality.
      simpa [B, D, Dₙ, A, Aₙ, Bₙ] using
        (dyadicStoppedValueDefect_condExp_ae_le (X := X) hX hXrc hσ hσ_bdd N hσ_le_N n)
    calc
      μ[Dₙ n]
          = ∫ ω, μ[Dₙ n | hσ.measurableSpace] ω ∂μ := by
              symm
              exact integral_condExp (μ := μ) (m := hσ.measurableSpace) (f := Dₙ n)
                hσ.measurableSpace_le
      _ ≤ μ[D] := by
            exact integral_mono_ae integrable_condExp hD_int hCondLe
  have hBoundedBelow :
      Filter.IsBoundedUnder (· ≥ ·) atTop (fun n ↦ μ[Dₙ n]) := by
    exact isBoundedUnder_of_eventually_ge <|
      Filter.Eventually.of_forall fun n ↦ integral_nonneg_of_ae (hDefect n).2.1
  have hCoboundedBelow :
      Filter.IsCoboundedUnder (· ≥ ·) atTop (fun n ↦ μ[Dₙ n]) := by
    refine IsCoboundedUnder.of_frequently_le (a := μ[D]) ?_
    exact (Filter.Eventually.of_forall fun n ↦ hIntegralLe n).frequently
  have hBoundedAbove :
      Filter.IsBoundedUnder (· ≤ ·) atTop (fun n ↦ μ[Dₙ n]) := by
    exact isBoundedUnder_of_eventually_le <|
      Filter.Eventually.of_forall fun n ↦ hIntegralLe n
  have hCoboundedAbove :
      Filter.IsCoboundedUnder (· ≤ ·) atTop (fun n ↦ μ[Dₙ n]) := by
    refine IsCoboundedUnder.of_frequently_ge (a := 0) ?_
    exact Filter.Frequently.of_forall fun n ↦ integral_nonneg_of_ae (hDefect n).2.1
  have hFatouReal :
      μ[D] ≤ liminf (fun n ↦ μ[Dₙ n]) atTop := by
    have hMap :
        ENNReal.ofReal (liminf (fun n ↦ μ[Dₙ n]) atTop) =
          liminf (fun n ↦ ENNReal.ofReal (μ[Dₙ n])) atTop :=
      Monotone.map_liminf_of_continuousAt (F := atTop) ENNReal.ofReal_mono
        (fun n ↦ μ[Dₙ n]) ENNReal.continuous_ofReal.continuousAt
        hCoboundedBelow hBoundedBelow
    have hEq :
        (fun n ↦ ∫⁻ ω, ENNReal.ofReal (Dₙ n ω) ∂μ) =
          fun n ↦ ENNReal.ofReal (μ[Dₙ n]) := by
      funext n
      symm
      exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hDefect n).1 (hDefect n).2.1
    have hFatouENN :
        ENNReal.ofReal (μ[D]) ≤ ENNReal.ofReal (liminf (fun n ↦ μ[Dₙ n]) atTop) := by
      calc
        ENNReal.ofReal (μ[D]) = ∫⁻ ω, ENNReal.ofReal (D ω) ∂μ := by
          rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hD_int hD_nonneg]
        _ ≤ liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal (Dₙ n ω) ∂μ) atTop := hFatou
        _ = liminf (fun n ↦ ENNReal.ofReal (μ[Dₙ n])) atTop := by rw [hEq]
        _ = ENNReal.ofReal (liminf (fun n ↦ μ[Dₙ n]) atTop) := hMap.symm
    have hLiminfNonneg : 0 ≤ liminf (fun n ↦ μ[Dₙ n]) atTop := by
      refine (Filter.le_liminf_iff' hCoboundedBelow hBoundedBelow).2 ?_
      intro y hy
      exact Filter.Eventually.of_forall fun n ↦
        (le_of_lt hy).trans (integral_nonneg_of_ae (hDefect n).2.1)
    exact (ENNReal.ofReal_le_ofReal_iff hLiminfNonneg).1 hFatouENN
  have hLimsupLe :
      limsup (fun n ↦ μ[Dₙ n]) atTop ≤ μ[D] := by
    refine (Filter.limsup_le_iff' hCoboundedAbove hBoundedAbove).2 ?_
    intro y hy
    exact Filter.Eventually.of_forall fun n ↦ (hIntegralLe n).trans hy.le
  have hDefectIntegral_tendsto :
      Tendsto (fun n ↦ μ[Dₙ n]) atTop (𝓝 (μ[D])) := by
    -- Proof comment: the dyadic defect expectations are squeezed between Fatou's lower bound and
    -- the integrated conditional-expectation upper bound.
    exact tendsto_of_le_liminf_of_limsup_le hFatouReal hLimsupLe hBoundedAbove hBoundedBelow
  have hA_eq : A = fun ω ↦ D ω + B ω := by
    funext ω
    simp [D]
  have hA_int : Integrable A μ := by
    -- Proof comment: recover the exact stopped value as the sum of the exact defect and the
    -- integrable terminal conditional expectation.
    rw [hA_eq]
    exact hD_int.add hB_int
  have hAIntegral :
      μ[A] = μ[D] + μ[X N] := by
    calc
      μ[A] = μ[D] + ∫ ω, B ω ∂μ := by
        rw [← integral_add hD_int hB_int]
        simpa [hA_eq]
      _ = μ[D] + μ[X N] := by
        rw [integral_condExp (μ := μ) (m := hσ.measurableSpace) (f := X N)
          hσ.measurableSpace_le]
  have hAIntegral_n :
      ∀ n, μ[Aₙ n] = μ[Dₙ n] + μ[X N] := by
    intro n
    have hBn_int : Integrable (Bₙ n) μ := integrable_condExp
    calc
      μ[Aₙ n] = μ[Dₙ n] + ∫ ω, Bₙ n ω ∂μ := by
        rw [← integral_add (hDefect n).1 hBn_int]
        congr 1
        funext ω
        simp [Dₙ]
      _ = μ[Dₙ n] + μ[X N] := by
        rw [integral_condExp (μ := μ)
          (m := (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace) (f := X N)
          (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace_le]
  have hStopped_tendsto :
      Tendsto (fun n ↦ μ[Aₙ n]) atTop (𝓝 (μ[A])) := by
    have hAddConst :
        Tendsto (fun n ↦ μ[Dₙ n] + μ[X N]) atTop (𝓝 (μ[D] + μ[X N])) :=
      hDefectIntegral_tendsto.add tendsto_const_nhds
    have hEqSeq : (fun n ↦ μ[Aₙ n]) = fun n ↦ μ[Dₙ n] + μ[X N] := by
      funext n
      exact hAIntegral_n n
    rw [hEqSeq, hAIntegral]
    exact hAddConst
  exact ⟨by simpa [A] using hA_int, by simpa [Aₙ, A] using hStopped_tendsto⟩

/-- Helper for Exercise 21.1.3: the fixed-horizon dyadic defect sequence converges in `L¹`. -/
private lemma dyadicStoppedValueDefect_tendsto_L1 :
    [Filtration.IsRightContinuous ℱ] →
    ∀ {X : NNReal → Ω → ℝ} (_ : Supermartingale X ℱ μ) (_ : HasRightContinuousPaths X)
      {σ : Ω → NNReal}
      (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
      (_ : ∃ T : NNReal, ∀ ω, σ ω ≤ T)
      (N : ℕ) (_ : ∀ ω, σ ω ≤ (N : NNReal)),
      Tendsto
        (fun n ↦
          eLpNorm
            (fun ω ↦
              (stoppedValue X (fun ω' ↦ (dyadicCeilApprox n σ ω' : ENNReal)) ω -
                  μ[X N | (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace] ω) -
                (stoppedValue X (fun ω' ↦ (σ ω' : ENNReal)) ω -
                  μ[X N | hσ.measurableSpace] ω))
            1 μ)
        atTop (𝓝 0) := by
  intro _ X hX hXrc σ hσ hσ_bdd N hσ_le_N
  let A : Ω → ℝ := stoppedValue X (fun ω ↦ (σ ω : ENNReal))
  let B : Ω → ℝ := μ[X N | hσ.measurableSpace]
  let D : Ω → ℝ := fun ω ↦ A ω - B ω
  let Aₙ : ℕ → Ω → ℝ :=
    fun n ↦ stoppedValue X (fun ω ↦ (dyadicCeilApprox n σ ω : ENNReal))
  let Bₙ : ℕ → Ω → ℝ :=
    fun n ↦ μ[X N | (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace]
  let Dₙ : ℕ → Ω → ℝ := fun n ω ↦ Aₙ n ω - Bₙ n ω
  have hDefect :
      ∀ n,
        Integrable (Dₙ n) μ ∧
          (0 ≤ᵐ[μ] Dₙ n) ∧ μ[Dₙ n] ≤ μ[X 0] - μ[X N] := by
    intro n
    -- Proof comment: the defect expectation bound already packages integrability,
    -- nonnegativity, and the uniform expectation control at the fixed horizon `N`.
    simpa [Aₙ, Bₙ, Dₙ] using
      (dyadicStoppedValueDefect_expectation_bound (X := X) hX hXrc hσ hσ_bdd N hσ_le_N n)
  have hA_tendsto :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Aₙ n ω) atTop (𝓝 (A ω)) := by
    -- Proof comment: right continuity transports the dyadic ceiling approximation to the exact
    -- stopped value.
    simpa [Aₙ, A] using
      (dyadic_stoppedValue_tendsto_ae (X := X) hX hXrc hσ hσ_bdd)
  have hB_tendsto :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Bₙ n ω) atTop (𝓝 (B ω)) := by
    -- Proof comment: reverse Lévy along the dyadic stopping-time sigma algebras handles the
    -- fixed terminal value `X N`.
    simpa [Bₙ, B] using
      (dyadicConstHorizon_condExp_tendsto_ae (X := X) hX hXrc hσ hσ_bdd N hσ_le_N)
  have hD_tendsto :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Dₙ n ω) atTop (𝓝 (D ω)) := by
    -- Proof comment: subtract the two convergent pieces in the fixed-horizon defect normal form.
    filter_upwards [hA_tendsto, hB_tendsto] with ω hAω hBω
    simpa [Dₙ, D] using hAω.sub hBω
  have hD_nonneg : 0 ≤ᵐ[μ] D := ae_nonneg_limit (fun n ↦ (hDefect n).2.1) hD_tendsto
  have hD_aestrong : AEStronglyMeasurable D μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n ↦ (hDefect n).1.aestronglyMeasurable) hD_tendsto
  have hFatou :
      ∫⁻ ω, ENNReal.ofReal (D ω) ∂μ ≤
        liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal (Dₙ n ω) ∂μ) atTop := by
    -- Proof comment: Fatou upgrades the nonnegative dyadic defect bounds to the exact defect.
    calc
      ∫⁻ ω, ENNReal.ofReal (D ω) ∂μ
          = ∫⁻ ω, liminf (fun n ↦ ENNReal.ofReal (Dₙ n ω)) atTop ∂μ := by
              refine lintegral_congr_ae ?_
              filter_upwards [hD_tendsto] with ω hω
              exact ((ENNReal.continuous_ofReal.tendsto (D ω)).comp hω).liminf_eq.symm
      _ ≤ liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal (Dₙ n ω) ∂μ) atTop := by
            refine MeasureTheory.lintegral_liminf_le' ?_
            intro n
            exact ((hDefect n).1.aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have hEventuallyBound :
      ∀ᶠ n in atTop,
        ∫⁻ ω, ENNReal.ofReal (Dₙ n ω) ∂μ ≤ ENNReal.ofReal (μ[X 0] - μ[X N]) := by
    filter_upwards with n
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hDefect n).1 (hDefect n).2.1]
    exact ENNReal.ofReal_le_ofReal (hDefect n).2.2
  have hLiminf_ne_top :
      liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal (Dₙ n ω) ∂μ) atTop ≠ ⊤ := by
    have hLiminf_le :
        liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal (Dₙ n ω) ∂μ) atTop ≤
          ENNReal.ofReal (μ[X 0] - μ[X N]) :=
      Filter.liminf_le_of_frequently_le' hEventuallyBound.frequently
    exact ne_top_of_le_ne_top (b := ENNReal.ofReal (μ[X 0] - μ[X N]))
      ENNReal.ofReal_ne_top hLiminf_le
  have hD_lintegral_ne_top :
      ∫⁻ ω, ENNReal.ofReal (D ω) ∂μ ≠ ⊤ := by
    exact ne_top_of_le_ne_top hLiminf_ne_top hFatou
  have hD_int : Integrable D μ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hD_aestrong hD_nonneg).1
      hD_lintegral_ne_top
  have hIntegralLe :
      ∀ n, μ[Dₙ n] ≤ μ[D] := by
    intro n
    have hCondLe :
        μ[Dₙ n | hσ.measurableSpace] ≤ᵐ[μ] D := by
      -- Proof comment: condition the dyadic defect back to `𝓕_σ`, then compare it to the exact
      -- defect using the fixed-horizon defect inequality.
      simpa [B, D, Dₙ, A, Aₙ, Bₙ] using
        (dyadicStoppedValueDefect_condExp_ae_le (X := X) hX hXrc hσ hσ_bdd N hσ_le_N n)
    calc
      μ[Dₙ n]
          = ∫ ω, μ[Dₙ n | hσ.measurableSpace] ω ∂μ := by
              symm
              exact integral_condExp (μ := μ) (m := hσ.measurableSpace) (f := Dₙ n)
                hσ.measurableSpace_le
      _ ≤ μ[D] := by
            exact integral_mono_ae integrable_condExp hD_int hCondLe
  have hBoundedBelow :
      Filter.IsBoundedUnder (· ≥ ·) atTop (fun n ↦ μ[Dₙ n]) := by
    exact isBoundedUnder_of_eventually_ge <|
      Filter.Eventually.of_forall fun n ↦ integral_nonneg_of_ae (hDefect n).2.1
  have hCoboundedBelow :
      Filter.IsCoboundedUnder (· ≥ ·) atTop (fun n ↦ μ[Dₙ n]) := by
    refine IsCoboundedUnder.of_frequently_le (a := μ[D]) ?_
    exact (Filter.Eventually.of_forall fun n ↦ hIntegralLe n).frequently
  have hBoundedAbove :
      Filter.IsBoundedUnder (· ≤ ·) atTop (fun n ↦ μ[Dₙ n]) := by
    exact isBoundedUnder_of_eventually_le <|
      Filter.Eventually.of_forall fun n ↦ hIntegralLe n
  have hCoboundedAbove :
      Filter.IsCoboundedUnder (· ≤ ·) atTop (fun n ↦ μ[Dₙ n]) := by
    refine IsCoboundedUnder.of_frequently_ge (a := 0) ?_
    exact Filter.Frequently.of_forall fun n ↦ integral_nonneg_of_ae (hDefect n).2.1
  have hFatouReal :
      μ[D] ≤ liminf (fun n ↦ μ[Dₙ n]) atTop := by
    have hMap :
        ENNReal.ofReal (liminf (fun n ↦ μ[Dₙ n]) atTop) =
          liminf (fun n ↦ ENNReal.ofReal (μ[Dₙ n])) atTop :=
      Monotone.map_liminf_of_continuousAt (F := atTop) ENNReal.ofReal_mono
        (fun n ↦ μ[Dₙ n]) ENNReal.continuous_ofReal.continuousAt
        hCoboundedBelow hBoundedBelow
    have hEq :
        (fun n ↦ ∫⁻ ω, ENNReal.ofReal (Dₙ n ω) ∂μ) =
          fun n ↦ ENNReal.ofReal (μ[Dₙ n]) := by
      funext n
      symm
      exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hDefect n).1 (hDefect n).2.1
    have hFatouENN :
        ENNReal.ofReal (μ[D]) ≤ ENNReal.ofReal (liminf (fun n ↦ μ[Dₙ n]) atTop) := by
      calc
        ENNReal.ofReal (μ[D]) = ∫⁻ ω, ENNReal.ofReal (D ω) ∂μ := by
          rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hD_int hD_nonneg]
        _ ≤ liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal (Dₙ n ω) ∂μ) atTop := hFatou
        _ = liminf (fun n ↦ ENNReal.ofReal (μ[Dₙ n])) atTop := by rw [hEq]
        _ = ENNReal.ofReal (liminf (fun n ↦ μ[Dₙ n]) atTop) := hMap.symm
    have hLiminfNonneg : 0 ≤ liminf (fun n ↦ μ[Dₙ n]) atTop := by
      refine (Filter.le_liminf_iff' hCoboundedBelow hBoundedBelow).2 ?_
      intro y hy
      exact Filter.Eventually.of_forall fun n ↦
        (le_of_lt hy).trans (integral_nonneg_of_ae (hDefect n).2.1)
    exact (ENNReal.ofReal_le_ofReal_iff hLiminfNonneg).1 hFatouENN
  have hLimsupLe :
      limsup (fun n ↦ μ[Dₙ n]) atTop ≤ μ[D] := by
    refine (Filter.limsup_le_iff' hCoboundedAbove hBoundedAbove).2 ?_
    intro y hy
    exact Filter.Eventually.of_forall fun n ↦ (hIntegralLe n).trans hy.le
  have hDefectIntegral_tendsto :
      Tendsto (fun n ↦ μ[Dₙ n]) atTop (𝓝 (μ[D])) := by
    -- Proof comment: the dyadic defect expectations are squeezed between Fatou's lower bound and
    -- the integrated conditional-expectation upper bound.
    exact tendsto_of_le_liminf_of_limsup_le hFatouReal hLimsupLe hBoundedAbove hBoundedBelow
  have hScheffe :
      Integrable D μ ∧
        Tendsto (fun n ↦ ∫ ω, ‖Dₙ n ω - D ω‖ ∂μ) atTop (𝓝 0) := by
    -- Proof comment: Scheffé upgrades convergence of the nonnegative defects plus convergence of
    -- their expectations to `L¹` convergence.
    simpa using
      (scheffe_of_nonnegative_ae_tendsto (μ := μ) (fSeq := Dₙ) (f := D) (I := μ[D])
        (fun n ↦ (hDefect n).1) (fun n ↦ (hDefect n).2.1) hD_tendsto hDefectIntegral_tendsto)
  have hDiffInt : ∀ n, Integrable (fun ω ↦ Dₙ n ω - D ω) μ := by
    intro n
    exact (hDefect n).1.sub hD_int
  have hNorm :
      Tendsto
        (fun n ↦ ENNReal.ofReal (∫ ω, ‖Dₙ n ω - D ω‖ ∂μ))
        atTop
        (𝓝 0) := by
    have hNorm' :
        Tendsto
          (fun n ↦ ENNReal.ofReal (∫ ω, ‖Dₙ n ω - D ω‖ ∂μ))
          atTop
          (𝓝 (ENNReal.ofReal (0 : ℝ))) :=
      (ENNReal.continuous_ofReal.tendsto 0).comp hScheffe.2
    simpa using hNorm'
  have hRewrite :
      (fun n ↦ eLpNorm (fun ω ↦ Dₙ n ω - D ω) 1 μ) =
        fun n ↦ ENNReal.ofReal (∫ ω, ‖Dₙ n ω - D ω‖ ∂μ) := by
    funext n
    rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm,
      ← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm (hDiffInt n)]
  rw [hRewrite]
  exact hNorm

/-- Helper for Exercise 21.1.3: under a right-continuous filtration, the dyadic stopped values
converge in `L¹` to the exact stopped value. -/
private theorem dyadic_stoppedValue_tendsto_L1_of_rightContinuous
    [Filtration.IsRightContinuous ℱ] :
    ∀ {X : NNReal → Ω → ℝ} (_ : Supermartingale X ℱ μ) (_ : HasRightContinuousPaths X)
      {σ : Ω → NNReal}
      (_ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
      (_ : ∃ T : NNReal, ∀ ω, σ ω ≤ T),
      Tendsto
        (fun n ↦
          eLpNorm
            (fun ω ↦
              stoppedValue X (fun ω' ↦ (dyadicCeilApprox n σ ω' : ENNReal)) ω -
                stoppedValue X (fun ω' ↦ (σ ω' : ENNReal)) ω)
            1 μ)
        atTop (𝓝 0) := by
  intro X hX hXrc σ hσ hσ_bdd
  obtain ⟨N, hσ_le_N⟩ := exists_nat_bound_of_exists_bound hσ_bdd
  let A : Ω → ℝ := stoppedValue X (fun ω ↦ (σ ω : ENNReal))
  let B : Ω → ℝ := μ[X N | hσ.measurableSpace]
  let Aₙ : ℕ → Ω → ℝ :=
    fun n ↦ stoppedValue X (fun ω ↦ (dyadicCeilApprox n σ ω : ENNReal))
  let Bₙ : ℕ → Ω → ℝ :=
    fun n ↦ μ[X N | (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace]
  have hA_int : Integrable A μ := by
    -- Proof comment: the expectation-limit theorem already packages integrability of the exact
    -- stopped value `X_σ`.
    simpa [A] using (dyadicStoppedValue_expectation_tendsto (X := X) hX hXrc hσ hσ_bdd).1
  have hAₙ_int :
      ∀ n, Integrable (Aₙ n) μ := by
    intro n
    -- Proof comment: every dyadic ceiling stop is bounded, so its stopped value is integrable.
    simpa [Aₙ] using integrable_stoppedValue_dyadicCeilApprox (X := X) hX hσ n hσ_bdd
  have hB_int : Integrable B μ := by
    -- Proof comment: conditional expectations are always integrable.
    exact integrable_condExp
  have hBₙ_int :
      ∀ n, Integrable (Bₙ n) μ := by
    intro n
    -- Proof comment: the dyadic conditional expectations are integrable for the same reason.
    exact integrable_condExp
  have hDefect :
      Tendsto
        (fun n ↦
          eLpNorm
            (fun ω ↦ ((Aₙ n ω - Bₙ n ω) - (A ω - B ω)))
            1 μ)
        atTop (𝓝 0) := by
    -- Proof comment: the fixed-horizon defect theorem controls the stopped-value error after
    -- subtracting the matching conditional expectations of `X N`.
    simpa [Aₙ, Bₙ, A, B] using
      (dyadicStoppedValueDefect_tendsto_L1 (X := X) hX hXrc hσ hσ_bdd N hσ_le_N)
  have hCond :
      Tendsto
        (fun n ↦ eLpNorm (fun ω ↦ Bₙ n ω - B ω) 1 μ)
        atTop (𝓝 0) := by
    -- Proof comment: reverse Lévy on the dyadic stopping-time sigma algebras handles the
    -- fixed terminal conditional-expectation term.
    simpa [Bₙ, B] using
      (dyadicConstHorizon_condExp_tendsto_L1 (X := X) hX hXrc hσ hσ_bdd N hσ_le_N)
  have hBound :
      ∀ n,
        eLpNorm (fun ω ↦ Aₙ n ω - A ω) 1 μ ≤
          eLpNorm (fun ω ↦ ((Aₙ n ω - Bₙ n ω) - (A ω - B ω))) 1 μ +
            eLpNorm (fun ω ↦ Bₙ n ω - B ω) 1 μ := by
    intro n
    have hEq :
        (fun ω ↦ Aₙ n ω - A ω) =
          (fun ω ↦ ((Aₙ n ω - Bₙ n ω) - (A ω - B ω)) + (Bₙ n ω - B ω)) := by
      funext ω
      ring
    rw [hEq]
    exact
      eLpNorm_add_le
        ((((hAₙ_int n).sub (hBₙ_int n)).sub (hA_int.sub hB_int)).aestronglyMeasurable)
        (((hBₙ_int n).sub hB_int).aestronglyMeasurable)
        le_rfl
  have hUpper :
      Tendsto
        (fun n ↦
          eLpNorm
            (fun ω ↦ ((Aₙ n ω - Bₙ n ω) - (A ω - B ω)))
            1 μ +
              eLpNorm (fun ω ↦ Bₙ n ω - B ω) 1 μ)
        atTop (𝓝 0) := by
    simpa using hDefect.add hCond
  -- Proof comment: the target difference is squeezed between `0` and the sum of the two
  -- convergent error terms.
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hUpper
      (fun n ↦ zero_le _)
      hBound

/-- Helper for this exercise: the same dyadic stopped values converge in `L¹` to `X_σ`. -/
private theorem dyadic_stoppedValue_tendsto_L1 :
    [Filtration.IsRightContinuous ℱ] →
    ∀ {X : NNReal → Ω → ℝ} (_ : Supermartingale X ℱ μ) (_ : HasRightContinuousPaths X)
      {σ : Ω → NNReal}
      (_ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
      (_ : ∃ T : NNReal, ∀ ω, σ ω ≤ T),
      Tendsto
        (fun n ↦
          eLpNorm
            (fun ω ↦
              stoppedValue X (fun ω' ↦ (dyadicCeilApprox n σ ω' : ENNReal)) ω -
                stoppedValue X (fun ω' ↦ (σ ω' : ENNReal)) ω)
            1 μ)
        atTop (𝓝 0) := by
  intro _ X hX hXrc σ hσ hσ_bdd
  obtain ⟨N, hσ_le_N⟩ := exists_nat_bound_of_exists_bound hσ_bdd
  let A : Ω → ℝ := stoppedValue X (fun ω ↦ (σ ω : ENNReal))
  let B : Ω → ℝ := μ[X N | hσ.measurableSpace]
  let Aₙ : ℕ → Ω → ℝ :=
    fun n ↦ stoppedValue X (fun ω ↦ (dyadicCeilApprox n σ ω : ENNReal))
  let Bₙ : ℕ → Ω → ℝ :=
    fun n ↦ μ[X N | (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace]
  have hA_int : Integrable A μ := by
    -- Proof comment: the expectation-limit theorem already packages integrability of the exact
    -- stopped value `X_σ`.
    simpa [A] using (dyadicStoppedValue_expectation_tendsto (X := X) hX hXrc hσ hσ_bdd).1
  have hAₙ_int :
      ∀ n, Integrable (Aₙ n) μ := by
    intro n
    -- Proof comment: every dyadic ceiling stop is bounded, so its stopped value is integrable.
    simpa [Aₙ] using integrable_stoppedValue_dyadicCeilApprox (X := X) hX hσ n hσ_bdd
  have hB_int : Integrable B μ := by
    -- Proof comment: conditional expectations are always integrable.
    exact integrable_condExp
  have hBₙ_int :
      ∀ n, Integrable (Bₙ n) μ := by
    intro n
    -- Proof comment: the dyadic conditional expectations are integrable for the same reason.
    exact integrable_condExp
  have hDefect :
      Tendsto
        (fun n ↦
          eLpNorm
            (fun ω ↦ ((Aₙ n ω - Bₙ n ω) - (A ω - B ω)))
            1 μ)
        atTop (𝓝 0) := by
    -- Proof comment: the fixed-horizon defect theorem controls the stopped-value error after
    -- subtracting the matching conditional expectations of `X N`.
    simpa [Aₙ, Bₙ, A, B] using
      (dyadicStoppedValueDefect_tendsto_L1 (X := X) hX hXrc hσ hσ_bdd N hσ_le_N)
  have hCond :
      Tendsto
        (fun n ↦ eLpNorm (fun ω ↦ Bₙ n ω - B ω) 1 μ)
        atTop (𝓝 0) := by
    -- Proof comment: reverse Lévy on the dyadic stopping-time sigma algebras handles the
    -- fixed terminal conditional-expectation term.
    simpa [Bₙ, B] using
      (dyadicConstHorizon_condExp_tendsto_L1 (X := X) hX hXrc hσ hσ_bdd N hσ_le_N)
  have hBound :
      ∀ n,
        eLpNorm (fun ω ↦ Aₙ n ω - A ω) 1 μ ≤
          eLpNorm (fun ω ↦ ((Aₙ n ω - Bₙ n ω) - (A ω - B ω))) 1 μ +
            eLpNorm (fun ω ↦ Bₙ n ω - B ω) 1 μ := by
    intro n
    have hEq :
        (fun ω ↦ Aₙ n ω - A ω) =
          (fun ω ↦ ((Aₙ n ω - Bₙ n ω) - (A ω - B ω)) + (Bₙ n ω - B ω)) := by
      funext ω
      ring
    rw [hEq]
    exact
      eLpNorm_add_le
        ((((hAₙ_int n).sub (hBₙ_int n)).sub (hA_int.sub hB_int)).aestronglyMeasurable)
        (((hBₙ_int n).sub hB_int).aestronglyMeasurable)
        le_rfl
  have hUpper :
      Tendsto
        (fun n ↦
          eLpNorm
            (fun ω ↦ ((Aₙ n ω - Bₙ n ω) - (A ω - B ω)))
            1 μ +
              eLpNorm (fun ω ↦ Bₙ n ω - B ω) 1 μ)
        atTop (𝓝 0) := by
    simpa using hDefect.add hCond
  -- Proof comment: the target difference is squeezed between `0` and the sum of the two
  -- convergent error terms.
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hUpper
      (fun n ↦ zero_le _)
      hBound

/-- Helper for Exercise 21.1.3: the bounded clipped stop `τ ∧ t` is exactly the time-`t` slice
of the stopped process. -/
private lemma stoppedValue_min_const_eq_stoppedProcess
    {X : NNReal → Ω → ℝ} {τ : Ω → ENNReal} {t : NNReal} :
    stoppedValue X (fun ω ↦ min (τ ω) (t : ENNReal)) =
      stoppedProcess X τ t := by
  -- Proof comment: both sides evaluate `X` at the same clipped time; only the order of the
  -- `min` arguments differs.
  ext ω
  change X (min (τ ω) (t : ENNReal)).untopA ω =
    X (min (t : ENNReal) (τ ω)).untopA ω
  rw [min_comm]

/-- Helper for Exercise 21.1.3: the bounded clip `τ ∧ t` of an `ENNReal`-valued stopping time as
an `NNReal`-valued stopping time. -/
private def clippedStoppingTimeNNReal (τ : Ω → ENNReal) (t : NNReal) : Ω → NNReal :=
  fun ω ↦ ENNReal.toNNReal (min (τ ω) (t : ENNReal))

/-- Helper for Exercise 21.1.3: coercing the bounded `NNReal` clip back to `ENNReal` recovers the
original clipped stopping time `τ ∧ t`. -/
private lemma clippedStoppingTimeNNReal_coe
    {τ : Ω → ENNReal} {t : NNReal} :
    (fun ω ↦ ((clippedStoppingTimeNNReal τ t ω : NNReal) : ENNReal)) =
      fun ω ↦ min (τ ω) (t : ENNReal) := by
  -- Proof comment: the deterministic clip `τ ∧ t` is finite, so `toNNReal` followed by coercion
  -- back to `ENNReal` leaves it unchanged.
  funext ω
  simp [clippedStoppingTimeNNReal, ENNReal.coe_toNNReal]

/-- Helper for Exercise 21.1.3: the bounded `NNReal` clip of a stopping time is again a stopping
time. -/
private lemma clippedStoppingTimeNNReal_isStoppingTime
    {τ : Ω → ENNReal} (hτ : IsStoppingTime ℱ τ) (t : NNReal) :
    IsStoppingTime ℱ fun ω ↦ (clippedStoppingTimeNNReal τ t ω : ENNReal) := by
  -- Proof comment: after rewriting the coerced `NNReal` clip back to `τ ∧ t`, this is exactly
  -- the standard `min_const` stopping-time construction.
  rw [clippedStoppingTimeNNReal_coe]
  exact hτ.min_const t

/-- Helper for Exercise 21.1.3: the bounded `NNReal` clip never exceeds the clipping constant. -/
private lemma clippedStoppingTimeNNReal_le_const
    {τ : Ω → ENNReal} {t : NNReal} :
    ∀ ω, clippedStoppingTimeNNReal τ t ω ≤ t := by
  intro ω
  -- Proof comment: after coercing back to `ENNReal`, the bound is the obvious estimate
  -- `min (τ ω) t ≤ t`.
  exact ENNReal.coe_le_coe.mp <| by
    simp [clippedStoppingTimeNNReal, ENNReal.coe_toNNReal, min_le_right]

/-- Helper for Exercise 21.1.3: evaluating `stoppedValue` at the bounded `NNReal` clip recovers
the stopped-process slice. -/
private lemma stoppedValue_clippedStoppingTimeNNReal_eq_stoppedProcess
    {X : NNReal → Ω → ℝ} {τ : Ω → ENNReal} {t : NNReal} :
    stoppedValue X (fun ω ↦ (clippedStoppingTimeNNReal τ t ω : ENNReal)) =
      stoppedProcess X τ t := by
  -- Proof comment: rewrite the coerced bounded clip back to `τ ∧ t`, then use the canonical
  -- stopped-process identification.
  rw [clippedStoppingTimeNNReal_coe]
  exact stoppedValue_min_const_eq_stoppedProcess


/-- Helper for Exercise 21.1.3: a bounded right-continuous supermartingale has decreasing
expected stopped values at bounded stopping times `σ ≤ τ`. -/
private theorem expectedStoppedValue_mono_of_le_of_bounded_rightContinuous
    [Filtration.IsRightContinuous ℱ] :
    ∀ {X : NNReal → Ω → ℝ} (_ : Supermartingale X ℱ μ) (_ : HasRightContinuousPaths X)
      {σ τ : Ω → NNReal}
      (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
      (_ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal))
      (_ : σ ≤ τ) (_ : ∃ T : NNReal, ∀ ω, τ ω ≤ T),
      Integrable (stoppedValue X (fun ω ↦ (σ ω : ENNReal))) μ ∧
        Integrable (stoppedValue X (fun ω ↦ (τ ω : ENNReal))) μ ∧
          μ[stoppedValue X (fun ω ↦ (τ ω : ENNReal))] ≤
            μ[stoppedValue X (fun ω ↦ (σ ω : ENNReal))] := by
  intro X hX hXrc σ τ hσ hτ hστ hτ_bdd
  have hσ_bdd : ∃ T : NNReal, ∀ ω, σ ω ≤ T :=
    exists_bound_of_le_of_exists_bound hστ hτ_bdd
  obtain ⟨hσ_int, hσ_tendsto⟩ :=
    dyadicStoppedValue_expectation_tendsto (X := X) hX hXrc hσ hσ_bdd
  obtain ⟨hτ_int, hτ_tendsto⟩ :=
    dyadicStoppedValue_expectation_tendsto (X := X) hX hXrc hτ hτ_bdd
  let sigmaInf : Ω → ENNReal := fun ω ↦ (σ ω : ENNReal)
  let tauInf : Ω → ENNReal := fun ω ↦ (τ ω : ENNReal)
  have hDyadicLe :
      ∀ n,
        μ[stoppedValue X (fun ω ↦ (dyadicCeilApprox n τ ω : ENNReal))] ≤
          μ[stoppedValue X (fun ω ↦ (dyadicCeilApprox n σ ω : ENNReal))] :=
    dyadicExpectedStoppedValue_mono (X := X) hX hσ hτ hστ hτ_bdd
  let pairSeq : ℕ → ℝ × ℝ := fun n ↦
    (μ[stoppedValue X (fun ω ↦ (dyadicCeilApprox n τ ω : ENNReal))],
      μ[stoppedValue X (fun ω ↦ (dyadicCeilApprox n σ ω : ENNReal))])
  have hPair :
      Tendsto pairSeq atTop
        (𝓝 (μ[stoppedValue X tauInf], μ[stoppedValue X sigmaInf])) := by
    simpa [pairSeq, tauInf, sigmaInf, nhds_prod_eq] using hτ_tendsto.prodMk hσ_tendsto
  have hEventuallyLe :
      ∀ᶠ n in atTop, pairSeq n ∈ {p : ℝ × ℝ | p.1 ≤ p.2} := by
    exact Filter.Eventually.of_forall fun n ↦ hDyadicLe n
  have hClosed : IsClosed {p : ℝ × ℝ | p.1 ≤ p.2} :=
    isClosed_le continuous_fst continuous_snd
  have hLimitLe :
      μ[stoppedValue X tauInf] ≤ μ[stoppedValue X sigmaInf] :=
    hClosed.mem_of_tendsto hPair hEventuallyLe
  -- Proof comment: the dyadic expectation inequalities survive after passing both sides to their
  -- exact bounded stopping-time limits.
  exact ⟨hσ_int, hτ_int, hLimitLe⟩

/-- Helper for this exercise: a right-continuous supermartingale satisfies the optional sampling
inequality for bounded stopping times `σ ≤ τ`. -/
private theorem optionalSampling_bounded :
    [Filtration.IsRightContinuous ℱ] →
    ∀ {X : NNReal → Ω → ℝ} (_ : Supermartingale X ℱ μ) (_ : HasRightContinuousPaths X)
      {σ τ : Ω → NNReal}
      (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
      (_ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal))
      (_ : σ ≤ τ) (_ : ∃ T : NNReal, ∀ ω, τ ω ≤ T),
      μ[stoppedValue X (fun ω ↦ (τ ω : ENNReal)) | hσ.measurableSpace] ≤ᵐ[μ]
        stoppedValue X (fun ω ↦ (σ ω : ENNReal)) := by
  intro _ X hX hXrc σ τ hσ hτ hστ hτ_bdd
  classical
  let sigmaInf : Ω → ENNReal := fun ω ↦ (σ ω : ENNReal)
  let tauInf : Ω → ENNReal := fun ω ↦ (τ ω : ENNReal)
  obtain ⟨hσ_int, hτ_int, hExpLe⟩ :=
    expectedStoppedValue_mono_of_le_of_bounded_rightContinuous
      hX hXrc hσ hτ hστ hτ_bdd
  have hSigmaMeas :
      StronglyMeasurable[hσ.measurableSpace] (stoppedValue X sigmaInf) := by
    -- Proof comment: the exact `σ`-stopped value is measurable with respect to the stopping-time
    -- `σ`-algebra.
    exact
      (measurableStoppedValue_of_adaptedRightContinuous
        (X := X) hX.1.adapted hXrc hσ).stronglyMeasurable
  have hCondMeas :
      StronglyMeasurable[hσ.measurableSpace]
        (μ[stoppedValue X tauInf | hσ.measurableSpace]) :=
    stronglyMeasurable_condExp
  have hLeTrim :
      μ[stoppedValue X tauInf | hσ.measurableSpace] ≤ᵐ[μ.trim hσ.measurableSpace_le]
        stoppedValue X sigmaInf := by
    refine MeasureTheory.ae_le_of_forall_setIntegral_le
      (integrable_condExp.trim hσ.measurableSpace_le hCondMeas)
      (hσ_int.trim hσ.measurableSpace_le hSigmaMeas) ?_
    intro A hA _hA_fin
    let ρ : Ω → NNReal := Set.piecewise A τ σ
    let rhoInf : Ω → ENNReal := fun ω ↦ (ρ ω : ENNReal)
    have hστInf : sigmaInf ≤ tauInf := by
      intro ω
      simpa [sigmaInf, tauInf] using hστ ω
    have hρ_stop : IsStoppingTime ℱ rhoInf := by
      -- Proof comment: `A` is measurable at the stopping time `σ`, so the glued stop is still a
      -- stopping time.
      have hRhoEq : rhoInf = Set.piecewise A tauInf sigmaInf := by
        funext ω
        by_cases hω : ω ∈ A
        · simp [rhoInf, ρ, sigmaInf, tauInf, Set.piecewise, hω]
        · simp [rhoInf, ρ, sigmaInf, tauInf, Set.piecewise, hω]
      rw [hRhoEq]
      exact isStoppingTime_piecewise_of_mem_measurableSpace hσ hτ hστInf hA
    have hσ_le_ρ : σ ≤ ρ := by
      intro ω
      by_cases hω : ω ∈ A
      · simpa [ρ, Set.piecewise, hω] using hστ ω
      · simp [ρ, Set.piecewise, hω]
    have hρ_bdd : ∃ T : NNReal, ∀ ω, ρ ω ≤ T := by
      rcases hτ_bdd with ⟨T, hT⟩
      refine ⟨T, ?_⟩
      intro ω
      by_cases hω : ω ∈ A
      · simpa [ρ, Set.piecewise, hω] using hT ω
      · simpa [ρ, Set.piecewise, hω] using (hστ ω).trans (hT ω)
    obtain ⟨_hσ_int', hρ_int, hρ_le⟩ :=
      expectedStoppedValue_mono_of_le_of_bounded_rightContinuous
        hX hXrc hσ hρ_stop hσ_le_ρ hρ_bdd
    have hρ_piecewise :
        stoppedValue X rhoInf =
          Set.piecewise A (stoppedValue X tauInf) (stoppedValue X sigmaInf) := by
      -- Proof comment: on `A` the glued stop is `τ`, and off `A` it is `σ`.
      ext ω
      by_cases hω : ω ∈ A
      · simp [rhoInf, ρ, sigmaInf, tauInf, Set.piecewise, stoppedValue, hω]
      · simp [rhoInf, ρ, sigmaInf, tauInf, Set.piecewise, stoppedValue, hω]
    have hρ_split :
        μ[stoppedValue X rhoInf] =
          ∫ ω in A, stoppedValue X tauInf ω ∂μ +
            ∫ ω in Aᶜ, stoppedValue X sigmaInf ω ∂μ := by
      -- Proof comment: rewrite the glued stopped value as a piecewise function and integrate each
      -- branch separately.
      calc
        μ[stoppedValue X rhoInf]
            = ∫ ω, stoppedValue X rhoInf ω ∂μ := rfl
        _ = ∫ ω, Set.piecewise A (stoppedValue X tauInf) (stoppedValue X sigmaInf) ω ∂μ := by
              simpa using congrArg (fun f : Ω → ℝ ↦ ∫ ω, f ω ∂μ) hρ_piecewise
        _ =
            ∫ ω in A, stoppedValue X tauInf ω ∂μ +
              ∫ ω in Aᶜ, stoppedValue X sigmaInf ω ∂μ := by
                simpa using
                  (integral_piecewise (hσ.measurableSpace_le _ hA)
                    hτ_int.integrableOn hσ_int.integrableOn)
    have hσ_split :
        μ[stoppedValue X sigmaInf] =
          ∫ ω in A, stoppedValue X sigmaInf ω ∂μ +
            ∫ ω in Aᶜ, stoppedValue X sigmaInf ω ∂μ := by
      -- Proof comment: split the exact stopped value of `σ` over `A` and its complement.
      simpa [setIntegral_univ] using
        (integral_add_compl (hσ.measurableSpace_le _ hA) hσ_int).symm
    have hSetLeStopped :
        ∫ ω in A, stoppedValue X tauInf ω ∂μ ≤
          ∫ ω in A, stoppedValue X sigmaInf ω ∂μ := by
      -- Proof comment: compare the glued-stop expectation with the exact `σ`-stop expectation and
      -- cancel the common complement contribution.
      linarith [hρ_le, hρ_split, hσ_split]
    have hLeftTrim :
        ∫ ω in A, μ[stoppedValue X tauInf | hσ.measurableSpace] ω ∂μ.trim hσ.measurableSpace_le =
          ∫ ω in A, stoppedValue X tauInf ω ∂μ := by
      calc
        ∫ ω in A, μ[stoppedValue X tauInf | hσ.measurableSpace] ω ∂μ.trim hσ.measurableSpace_le
            =
              ∫ ω in A, μ[stoppedValue X tauInf | hσ.measurableSpace] ω ∂μ := by
                symm
                exact MeasureTheory.setIntegral_trim hσ.measurableSpace_le hCondMeas hA
        _ = ∫ ω in A, stoppedValue X tauInf ω ∂μ := by
              simpa [tauInf] using
                (MeasureTheory.setIntegral_condExp hσ.measurableSpace_le hτ_int hA)
    have hRightTrim :
        ∫ ω in A, stoppedValue X sigmaInf ω ∂μ =
          ∫ ω in A, stoppedValue X sigmaInf ω ∂μ.trim hσ.measurableSpace_le := by
      exact MeasureTheory.setIntegral_trim hσ.measurableSpace_le hSigmaMeas hA
    calc
      ∫ ω in A, μ[stoppedValue X tauInf | hσ.measurableSpace] ω ∂μ.trim hσ.measurableSpace_le
          = ∫ ω in A, stoppedValue X tauInf ω ∂μ := hLeftTrim
      _ ≤ ∫ ω in A, stoppedValue X sigmaInf ω ∂μ := hSetLeStopped
      _ = ∫ ω in A, stoppedValue X sigmaInf ω ∂μ.trim hσ.measurableSpace_le := hRightTrim
  exact
    (MeasureTheory.StronglyMeasurable.ae_le_trim_iff
      hσ.measurableSpace_le hCondMeas hSigmaMeas).mp hLeTrim

/-- Helper for Exercise 21.1.3: bounded optional sampling on the clipped stopping times yields the
finite-test-set inequality needed for the finite-stop argument. -/
private lemma setIntegralClippedStopsLeOfFiniteTestSet
    [Filtration.IsRightContinuous ℱ]
    {X : NNReal → Ω → ℝ} (hX : Supermartingale X ℱ μ) (hXrc : HasRightContinuousPaths X)
    {σ τ : Ω → NNReal}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
    (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal))
    (hστ : σ ≤ τ) {s : Set Ω}
    (hs : MeasurableSet[hσ.measurableSpace] s) (n : ℕ) :
    ∫ ω in s ∩ {ω | (σ ω : ENNReal) ≤ (n : ENNReal)},
        stoppedProcess X (fun ω ↦ (τ ω : ENNReal)) n ω ∂μ
      ≤
        ∫ ω in s ∩ {ω | (σ ω : ENNReal) ≤ (n : ENNReal)},
          stoppedValue X (fun ω ↦ (σ ω : ENNReal)) ω ∂μ := by
  let tNN : NNReal := n
  let sigmaClip : Ω → NNReal :=
    clippedStoppingTimeNNReal (fun ω ↦ (σ ω : ENNReal)) tNN
  let tauClip : Ω → NNReal :=
    clippedStoppingTimeNNReal (fun ω ↦ (τ ω : ENNReal)) tNN
  have hσclip_raw : IsStoppingTime ℱ fun ω ↦ min (σ ω : ENNReal) (tNN : ENNReal) :=
    hσ.min_const tNN
  have hτclip_raw : IsStoppingTime ℱ fun ω ↦ min (τ ω : ENNReal) (tNN : ENNReal) :=
    hτ.min_const tNN
  have hσclip : IsStoppingTime ℱ fun ω ↦ (sigmaClip ω : ENNReal) := by
    simpa [sigmaClip] using hσclip_raw
  have hτclip : IsStoppingTime ℱ fun ω ↦ (tauClip ω : ENNReal) := by
    simpa [tauClip] using hτclip_raw
  have hσclip_le_tauClip : sigmaClip ≤ tauClip := by
    intro ω
    have hSigmaCoe :
        ((sigmaClip ω : NNReal) : ENNReal) = min (σ ω : ENNReal) (tNN : ENNReal) := by
      simpa [sigmaClip] using
        congrFun
          (clippedStoppingTimeNNReal_coe
            (τ := fun ω ↦ (σ ω : ENNReal)) (t := tNN))
          ω
    have hTauCoe :
        ((tauClip ω : NNReal) : ENNReal) = min (τ ω : ENNReal) (tNN : ENNReal) := by
      simpa [tauClip] using
        congrFun
          (clippedStoppingTimeNNReal_coe
            (τ := fun ω ↦ (τ ω : ENNReal)) (t := tNN))
          ω
    apply ENNReal.coe_le_coe.mp
    rw [hSigmaCoe, hTauCoe]
    exact min_le_min (show (σ ω : ENNReal) ≤ (τ ω : ENNReal) by exact_mod_cast hστ ω) le_rfl
  have hTauClip_bdd : ∃ T : NNReal, ∀ ω, tauClip ω ≤ T :=
    ⟨tNN, clippedStoppingTimeNNReal_le_const (τ := fun ω ↦ (τ ω : ENNReal)) (t := tNN)⟩
  obtain ⟨hSigmaClip_int, hTauClip_int, _⟩ :=
    expectedStoppedValue_mono_of_le_of_bounded_rightContinuous
      (X := X) hX hXrc hσclip hτclip hσclip_le_tauClip hTauClip_bdd
  have hClipLe :
      μ[stoppedValue X (fun ω ↦ (tauClip ω : ENNReal)) | hσclip.measurableSpace] ≤ᵐ[μ]
        stoppedValue X (fun ω ↦ (sigmaClip ω : ENNReal)) := by
    -- Proof comment: this is exactly the bounded optional-sampling inequality for the clipped
    -- stopping times `σ ∧ n` and `τ ∧ n`.
    exact optionalSampling_bounded
      (X := X) hX hXrc hσclip hτclip hσclip_le_tauClip hTauClip_bdd
  let u : Set Ω := s ∩ {ω | σ ω ≤ tNN}
  have hu_hσ_raw :
      MeasurableSet[hσ.measurableSpace] (s ∩ {ω | (σ ω : ENNReal) ≤ (tNN : ENNReal)}) := by
    exact hs.inter (hσ.measurableSet_le' tNN)
  have hu_hσ : MeasurableSet[hσ.measurableSpace] u := by
    simpa [u] using hu_hσ_raw
  have hu_hσclip : MeasurableSet[hσclip.measurableSpace] u := by
    -- Proof comment: on the test set `{σ ≤ n}`, the clipped stopping time `σ ∧ n` carries the
    -- same information as `σ`.
    have hu_hσclip_raw :
        MeasurableSet[(hσ.min_const tNN).measurableSpace]
          (s ∩ {ω | (σ ω : ENNReal) ≤ (tNN : ENNReal)}) :=
      (hσ.measurableSet_inter_le_const_iff s tNN).mp hu_hσ_raw
    simpa [u, sigmaClip] using hu_hσclip_raw
  have hu : MeasurableSet u := hσ.measurableSpace_le _ hu_hσ
  have hLeftEq :
      ∫ ω in u, μ[stoppedValue X (fun ω ↦ (tauClip ω : ENNReal)) | hσclip.measurableSpace] ω ∂μ
        =
      ∫ ω in u, stoppedProcess X (fun ω ↦ (τ ω : ENNReal)) tNN ω ∂μ := by
    calc
      ∫ ω in u, μ[stoppedValue X (fun ω ↦ (tauClip ω : ENNReal)) | hσclip.measurableSpace] ω ∂μ
          =
        ∫ ω in u, stoppedValue X (fun ω ↦ (tauClip ω : ENNReal)) ω ∂μ := by
              simpa using
                (MeasureTheory.setIntegral_condExp hσclip.measurableSpace_le hTauClip_int
                  hu_hσclip)
      _ =
        ∫ ω in u, stoppedProcess X (fun ω ↦ (τ ω : ENNReal)) tNN ω ∂μ := by
              congr 1 with ω
              exact congrFun
                (stoppedValue_clippedStoppingTimeNNReal_eq_stoppedProcess
                  (X := X) (τ := fun ω ↦ (τ ω : ENNReal)) (t := tNN))
                ω
  have hRightEq :
      ∫ ω in u, stoppedValue X (fun ω ↦ (sigmaClip ω : ENNReal)) ω ∂μ
        =
      ∫ ω in u, stoppedValue X (fun ω ↦ (σ ω : ENNReal)) ω ∂μ := by
    -- Proof comment: on `{σ ≤ n}`, clipping `σ` at `n` does not change the sampled time.
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem hu] with ω hω
    have hσ_le_n : (σ ω : ENNReal) ≤ (tNN : ENNReal) := by exact_mod_cast hω.2
    simp [u, sigmaClip, clippedStoppingTimeNNReal, stoppedValue, ENNReal.coe_toNNReal,
      hσ_le_n, min_eq_left hσ_le_n]
  have hSetLe :
      ∫ ω in u, μ[stoppedValue X (fun ω ↦ (tauClip ω : ENNReal)) | hσclip.measurableSpace] ω ∂μ
        ≤
      ∫ ω in u, stoppedValue X (fun ω ↦ (sigmaClip ω : ENNReal)) ω ∂μ := by
    have hLeftInt :
        Integrable
          (μ[stoppedValue X (fun ω ↦ (tauClip ω : ENNReal)) | hσclip.measurableSpace])
          (μ.restrict u) :=
      (integrable_condExp : Integrable
        (μ[stoppedValue X (fun ω ↦ (tauClip ω : ENNReal)) | hσclip.measurableSpace]) μ).restrict
    have hRightInt :
        Integrable (stoppedValue X (fun ω ↦ (sigmaClip ω : ENNReal))) (μ.restrict u) :=
      hSigmaClip_int.restrict
    -- Proof comment: integrate the bounded optional-sampling inequality over the fixed test set.
    exact integral_mono_ae hLeftInt hRightInt (ae_restrict_of_ae hClipLe)
  -- Proof comment: convert the bounded clipped inequality back to the stopped-process and exact
  -- stopped-value spellings used in the finite-stop limit argument.
  calc
    ∫ ω in s ∩ {ω | (σ ω : ENNReal) ≤ (n : ENNReal)},
        stoppedProcess X (fun ω ↦ (τ ω : ENNReal)) n ω ∂μ
        =
      ∫ ω in u, stoppedProcess X (fun ω ↦ (τ ω : ENNReal)) tNN ω ∂μ := by
          simp [u, tNN]
    _ =
      ∫ ω in u, μ[stoppedValue X (fun ω ↦ (tauClip ω : ENNReal)) | hσclip.measurableSpace] ω ∂μ :=
        hLeftEq.symm
    _ ≤ ∫ ω in u, stoppedValue X (fun ω ↦ (sigmaClip ω : ENNReal)) ω ∂μ := hSetLe
    _ =
      ∫ ω in s ∩ {ω | (σ ω : ENNReal) ≤ (n : ENNReal)},
        stoppedValue X (fun ω ↦ (σ ω : ENNReal)) ω ∂μ := by
          simpa [u, tNN] using hRightEq

/-- Helper for this exercise: an adapted integrable right-continuous process is a martingale iff
every bounded stopping time preserves its initial expectation. -/
private theorem expectedStoppedValue_iff_martingale :
    [Filtration.IsRightContinuous ℱ] →
    ∀ {Y : NNReal → Ω → ℝ} (_ : Adapted ℱ Y)
      (_ : ∀ t : NNReal, Integrable (Y t) μ)
      (_ : HasRightContinuousPaths Y),
      Martingale Y ℱ μ ↔
        ∀ τ : Ω → NNReal, IsStoppingTime ℱ (fun ω ↦ (τ ω : ENNReal)) →
          (∃ T : NNReal, ∀ ω, τ ω ≤ T) →
            μ[stoppedValue Y (fun ω ↦ (τ ω : ENNReal))] = μ[Y 0] := by
  intro _ Y hY_adapted hY_int hYrc
  constructor
  · intro hY τ hτ hτ_bdd
    let tauInf : Ω → ENNReal := fun ω ↦ (τ ω : ENNReal)
    -- Proof comment: the bounded stopping-time expectation identity is already packaged in the
    -- theorem-local martingale owner above.
    simpa [tauInf] using
      expectedStoppedValue_eq_initial_of_martingale_of_boundedStoppingTime
        (X := Y) hY hYrc hτ hτ_bdd
  · intro hstop
    -- Proof comment: the converse direction is already packaged in the piecewise stopping-time
    -- reconstruction lemma proved above.
    exact martingale_of_expectedStoppedValueEqInitial_piecewise hY_adapted hY_int hstop

/-- Helper for Exercise 21.1.3: on a finite test set, the exact stopped value restricted to the
event `{ρ ≤ n}` converges in integral to the unrestricted exact stopped value. -/
private lemma restrictedIntegralStoppedValue_tendstoOnFiniteTestSet
    {X : NNReal → Ω → ℝ} {ρ : Ω → NNReal}
    (hρ : IsStoppingTime ℱ fun ω ↦ (ρ ω : ENNReal))
    (hρ_int : Integrable (stoppedValue X (fun ω ↦ (ρ ω : ENNReal))) μ)
    {s : Set Ω} (hs : MeasurableSet s) (hμs : μ s < ⊤) :
    Tendsto
      (fun n : ℕ ↦
        ∫ ω in s ∩ {ω | (ρ ω : ENNReal) ≤ (n : ENNReal)},
          stoppedValue X (fun ω ↦ (ρ ω : ENNReal)) ω ∂μ)
      atTop
      (𝓝 (∫ ω in s, stoppedValue X (fun ω ↦ (ρ ω : ENNReal)) ω ∂μ)) := by
  let rhoInf : Ω → ENNReal := fun ω ↦ (ρ ω : ENNReal)
  let F : ℕ → Ω → ℝ :=
    fun n ↦ {ω | rhoInf ω ≤ (n : ENNReal)}.indicator (stoppedValue X rhoInf)
  have hEventMeas : ∀ n : ℕ, MeasurableSet {ω | rhoInf ω ≤ (n : ENNReal)} := by
    intro n
    exact hρ.measurableSpace_le _ (hρ.measurableSet_le' n)
  have hConst_UI : UniformIntegrable (fun _ : ℕ ↦ stoppedValue X rhoInf) 1 μ :=
    uniformIntegrable_const le_rfl (by simp) (memLp_one_iff_integrable.2 hρ_int)
  have hF_UI : UniformIntegrable F 1 μ :=
    uniformIntegrableIndicatorFamily hConst_UI hEventMeas
  have hF_int : ∀ n : ℕ, Integrable (F n) μ := by
    intro n
    exact hρ_int.indicator (hEventMeas n)
  have hF_tendsto :
      ∀ᵐ ω ∂(μ.restrict s), Tendsto (fun n ↦ F n ω) atTop (𝓝 (stoppedValue X rhoInf ω)) := by
    refine ae_restrict_of_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hEq : (fun n ↦ F n ω) =ᶠ[atTop] fun _ ↦ stoppedValue X rhoInf ω := by
      filter_upwards
        [show ∀ᶠ n : ℕ in atTop, Nat.ceil (ρ ω : ℝ) ≤ n from
          Filter.eventually_ge_atTop (Nat.ceil (ρ ω : ℝ))] with n hn
      have hρ_le_n_real : (ρ ω : ℝ) ≤ n := by
        exact le_trans (Nat.le_ceil (ρ ω : ℝ)) (by exact_mod_cast hn)
      have hρ_le_n_nn : ρ ω ≤ n := by
        exact_mod_cast hρ_le_n_real
      have hρ_le_n : rhoInf ω ≤ (n : ENNReal) := by
        change (ρ ω : ENNReal) ≤ (n : ENNReal)
        exact_mod_cast hρ_le_n_nn
      have hmem : ω ∈ {ω | rhoInf ω ≤ (n : ENNReal)} := hρ_le_n
      simp [F, hmem]
    exact Tendsto.congr' hEq.symm tendsto_const_nhds
  have hLimit :
      Tendsto (fun n ↦ ∫ ω, F n ω ∂(μ.restrict s)) atTop
        (𝓝 (∫ ω, stoppedValue X rhoInf ω ∂(μ.restrict s))) :=
    restrictedIntegralConvergenceOfUi hμs hF_UI hF_int hρ_int hF_tendsto
  have hSeqEq :
      (fun n : ℕ ↦ ∫ ω, F n ω ∂(μ.restrict s)) =
        fun n : ℕ ↦
          ∫ ω in s ∩ {ω | (ρ ω : ENNReal) ≤ (n : ENNReal)},
            stoppedValue X rhoInf ω ∂μ := by
    funext n
    change
      ∫ ω, {ω | rhoInf ω ≤ (n : ENNReal)}.indicator (stoppedValue X rhoInf) ω ∂(μ.restrict s)
        =
      ∫ ω in s ∩ {ω | rhoInf ω ≤ (n : ENNReal)}, stoppedValue X rhoInf ω ∂μ
    rw [MeasureTheory.integral_indicator (μ := μ.restrict s) (f := stoppedValue X rhoInf)
      (s := {ω | rhoInf ω ≤ (n : ENNReal)}) (hEventMeas n)]
    change
      ∫ ω, stoppedValue X rhoInf ω ∂((μ.restrict s).restrict {ω | rhoInf ω ≤ (n : ENNReal)})
        =
      ∫ ω in s ∩ {ω | rhoInf ω ≤ (n : ENNReal)}, stoppedValue X rhoInf ω ∂μ
    rw [Measure.restrict_restrict (hEventMeas n), Set.inter_comm]
  -- Proof comment: pass to the restricted measure on `s`, where the indicator family converges
  -- almost surely to the exact stopped value and remains uniformly integrable.
  simpa [rhoInf, hSeqEq] using hLimit

/-- Helper for Exercise 21.1.3: on a finite test set, the clipped stopped-process integrals
converge to the exact stopped-value integral. -/
private lemma restrictedIntegralClippedStop_tendstoOnFiniteTestSet
    {X : NNReal → Ω → ℝ} {ρ : Ω → NNReal}
    (hρ : IsStoppingTime ℱ fun ω ↦ (ρ ω : ENNReal))
    (hρ_int : Integrable (stoppedValue X (fun ω ↦ (ρ ω : ENNReal))) μ)
    {s : Set Ω} (hs : MeasurableSet s) (hμs : μ s < ⊤) :
    Tendsto
      (fun n : ℕ ↦
        ∫ ω in s ∩ {ω | (ρ ω : ENNReal) ≤ (n : ENNReal)},
          stoppedProcess X (fun ω ↦ (ρ ω : ENNReal)) n ω ∂μ)
      atTop
      (𝓝 (∫ ω in s, stoppedValue X (fun ω ↦ (ρ ω : ENNReal)) ω ∂μ)) := by
  let rhoInf : Ω → ENNReal := fun ω ↦ (ρ ω : ENNReal)
  have hBase :=
    restrictedIntegralStoppedValue_tendstoOnFiniteTestSet
      (X := X) hρ hρ_int hs hμs
  have hSeqEq :
      (fun n : ℕ ↦
        ∫ ω in s ∩ {ω | rhoInf ω ≤ (n : ENNReal)}, stoppedProcess X rhoInf n ω ∂μ) =
        fun n : ℕ ↦
          ∫ ω in s ∩ {ω | rhoInf ω ≤ (n : ENNReal)}, stoppedValue X rhoInf ω ∂μ := by
    funext n
    refine integral_congr_ae ?_
    have hSetMeas : MeasurableSet (s ∩ {ω | rhoInf ω ≤ (n : ENNReal)}) :=
      hs.inter (hρ.measurableSpace_le _ (hρ.measurableSet_le' n))
    filter_upwards [ae_restrict_mem hSetMeas] with ω hω
    simpa [rhoInf, stoppedValue] using
      (stoppedProcess_eq_of_ge (u := X) (τ := rhoInf) (i := (n : NNReal)) (ω := ω) hω.2)
  -- Proof comment: on `{ρ ≤ n}`, the stopped process has already frozen at the exact stopped
  -- value, so the clipped integral is the same sequence as in the exact-stop helper above.
  exact Tendsto.congr'
    (Filter.Eventually.of_forall fun n ↦ (congrFun hSeqEq n).symm) hBase

/-- Helper for Exercise 21.1.3: once the exact finite stopped values are known to be integrable,
the finite optional-sampling inequality follows from the bounded clipped inequalities by passing to
the limit on finite `𝓕_σ`-test sets. -/
private theorem optionalSampling_finite_of_integrableStoppedValues
    [Filtration.IsRightContinuous ℱ] :
    ∀ {X : NNReal → Ω → ℝ} (_ : Supermartingale X ℱ μ)
      (_ : HasRightContinuousPaths X)
      (_ : UniformIntegrable X 1 μ)
      {σ τ : Ω → NNReal}
      (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
      (_ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal))
      (_ : σ ≤ τ)
      (_ : Integrable (stoppedValue X (fun ω ↦ (σ ω : ENNReal))) μ)
      (_ : Integrable (stoppedValue X (fun ω ↦ (τ ω : ENNReal))) μ),
      μ[stoppedValue X (fun ω ↦ (τ ω : ENNReal)) | hσ.measurableSpace] ≤ᵐ[μ]
        stoppedValue X (fun ω ↦ (σ ω : ENNReal)) := by
  intro X hX hXrc hX_UI σ τ hσ hτ hστ hσ_int hτ_int
  let sigmaInf : Ω → ENNReal := fun ω ↦ (σ ω : ENNReal)
  let tauInf : Ω → ENNReal := fun ω ↦ (τ ω : ENNReal)
  have hSigmaMeas :
      StronglyMeasurable[hσ.measurableSpace] (stoppedValue X sigmaInf) := by
    exact
      (measurableStoppedValue_of_adaptedRightContinuous
        (X := X) hX.1.adapted hXrc hσ).stronglyMeasurable
  have hCondMeas :
      StronglyMeasurable[hσ.measurableSpace]
        (μ[stoppedValue X tauInf | hσ.measurableSpace]) :=
    stronglyMeasurable_condExp
  have hXNatUI : UniformIntegrable (fun n : ℕ ↦ X n) 1 μ := by
    refine ⟨fun n ↦ hX_UI.aestronglyMeasurable n, ?_, ?_⟩
    · intro ε hε
      rcases hX_UI.unifIntegrable hε with ⟨δ, hδ, hδ_bound⟩
      exact ⟨δ, hδ, fun n s hs hμs ↦ hδ_bound n s hs hμs⟩
    · rcases hX_UI.2.2 with ⟨C, hC⟩
      exact ⟨C, fun n ↦ hC n⟩
  have hLeTrim :
      μ[stoppedValue X tauInf | hσ.measurableSpace] ≤ᵐ[μ.trim hσ.measurableSpace_le]
        stoppedValue X sigmaInf := by
    refine MeasureTheory.ae_le_of_forall_setIntegral_le
      (integrable_condExp.trim hσ.measurableSpace_le hCondMeas)
      (hσ_int.trim hσ.measurableSpace_le hSigmaMeas) ?_
    intro s hs hμs
    have hsμ : μ s < ⊤ := by
      rw [trim_measurableSet_eq hσ.measurableSpace_le hs] at hμs
      exact hμs
    have hs_ambient : MeasurableSet s := hσ.measurableSpace_le _ hs
    let B : ℕ → Ω → ℝ := fun n ↦
      {ω | (σ ω : ENNReal) ≤ (n : ENNReal) ∧ (n : ENNReal) < (τ ω : ENNReal)}.indicator (X n)
    have hBandMeas :
        ∀ n : ℕ,
          MeasurableSet {ω | (σ ω : ENNReal) ≤ (n : ENNReal) ∧ (n : ENNReal) < (τ ω : ENNReal)} := by
      intro n
      have hTauGt : MeasurableSet {ω | (n : ENNReal) < (τ ω : ENNReal)} := by
        simpa [Set.compl_setOf, not_le] using
          ((hτ.measurableSpace_le _ (hτ.measurableSet_le' n)).compl : MeasurableSet {ω |
            ¬ (τ ω : ENNReal) ≤ (n : ENNReal)})
      exact
        (hσ.measurableSpace_le _ (hσ.measurableSet_le' n)).inter hTauGt
    have hB_UI : UniformIntegrable B 1 μ :=
      uniformIntegrableIndicatorFamily hXNatUI hBandMeas
    have hB_int : ∀ n : ℕ, Integrable (B n) μ := by
      intro n
      exact (hX.integrable n).indicator (hBandMeas n)
    have hB_tendsto :
        ∀ᵐ ω ∂(μ.restrict s), Tendsto (fun n ↦ B n ω) atTop (𝓝 0) := by
      refine ae_restrict_of_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
      have hEq :
          (fun n ↦ B n ω) =ᶠ[atTop] fun _ ↦ 0 := by
        filter_upwards
          [show ∀ᶠ n : ℕ in atTop, Nat.ceil (τ ω : ℝ) ≤ n from
            Filter.eventually_ge_atTop (Nat.ceil (τ ω : ℝ))] with n hn
        have hτ_le_n_real : (τ ω : ℝ) ≤ n := by
          exact le_trans (Nat.le_ceil (τ ω : ℝ)) (by exact_mod_cast hn)
        have hτ_le_n_nn : τ ω ≤ n := by
          exact_mod_cast hτ_le_n_real
        have hnot : ¬ (n : ENNReal) < (τ ω : ENNReal) := by
          exact not_lt_of_ge (by exact_mod_cast hτ_le_n_nn)
        simp [B, hnot]
      exact Tendsto.congr' hEq.symm tendsto_const_nhds
    have hBandLimit :
        Tendsto
          (fun n : ℕ ↦
            ∫ ω in s, B n ω ∂μ)
          atTop (𝓝 0) := by
      have hZeroInt : Integrable (0 : Ω → ℝ) μ :=
        integrable_zero (μ := μ) (ε' := ℝ)
      have hBand :=
        restrictedIntegralConvergenceOfUi
          (μ := μ) (f := B) (g := fun _ : Ω ↦ (0 : ℝ)) (s := s)
          hsμ hB_UI hB_int hZeroInt hB_tendsto
      simpa using hBand
    have hTauLimit :
        Tendsto
          (fun n : ℕ ↦
            ∫ ω in s ∩ {ω | (τ ω : ENNReal) ≤ (n : ENNReal)},
              stoppedValue X tauInf ω ∂μ)
          atTop
          (𝓝 (∫ ω in s, stoppedValue X tauInf ω ∂μ)) :=
      restrictedIntegralStoppedValue_tendstoOnFiniteTestSet
        (X := X) hτ hτ_int hs_ambient hsμ
    have hSigmaLimit :
        Tendsto
          (fun n : ℕ ↦
            ∫ ω in s ∩ {ω | (σ ω : ENNReal) ≤ (n : ENNReal)},
              stoppedValue X sigmaInf ω ∂μ)
          atTop
          (𝓝 (∫ ω in s, stoppedValue X sigmaInf ω ∂μ)) :=
      restrictedIntegralStoppedValue_tendstoOnFiniteTestSet
        (X := X) hσ hσ_int hs_ambient hsμ
    have hClipLimit :
        Tendsto
          (fun n : ℕ ↦
            ∫ ω in s ∩ {ω | (σ ω : ENNReal) ≤ (n : ENNReal)},
              stoppedProcess X tauInf n ω ∂μ)
          atTop
          (𝓝 (∫ ω in s, stoppedValue X tauInf ω ∂μ)) := by
      have hFirst :
          Tendsto
            (fun n : ℕ ↦
              ∫ ω in s ∩ {ω | (τ ω : ENNReal) ≤ (n : ENNReal)},
                stoppedValue X tauInf ω ∂μ)
            atTop
            (𝓝 (∫ ω in s, stoppedValue X tauInf ω ∂μ)) :=
        hTauLimit
      have hSecond :
          Tendsto
            (fun n : ℕ ↦
              ∫ ω in s, B n ω ∂μ)
            atTop
            (𝓝 0) :=
        hBandLimit
      have hSeqEq :
          (fun n : ℕ ↦
            ∫ ω in s ∩ {ω | (σ ω : ENNReal) ≤ (n : ENNReal)},
              stoppedProcess X tauInf n ω ∂μ) =
            fun n : ℕ ↦
              ∫ ω in s ∩ {ω | (τ ω : ENNReal) ≤ (n : ENNReal)},
                stoppedValue X tauInf ω ∂μ +
                  ∫ ω in s, B n ω ∂μ := by
        funext n
        let u : Set Ω := s ∩ {ω | (τ ω : ENNReal) ≤ (n : ENNReal)}
        let v : Set Ω := s ∩ {ω | (σ ω : ENNReal) ≤ (n : ENNReal) ∧ (n : ENNReal) < (τ ω : ENNReal)}
        have hu_meas : MeasurableSet u := by
          dsimp [u]
          exact hs_ambient.inter (hτ.measurableSpace_le _ (hτ.measurableSet_le' n))
        have hv_meas : MeasurableSet v := by
          dsimp [v]
          exact hs_ambient.inter (hBandMeas n)
        have hDisj : Disjoint u v := by
          refine Set.disjoint_left.2 fun ω hωu hωv ↦ ?_
          exact not_lt_of_ge hωu.2 (hωv.2.2)
        have hUnion :
            s ∩ {ω | (σ ω : ENNReal) ≤ (n : ENNReal)} = u ∪ v := by
          ext ω
          constructor
          · intro hω
            by_cases hωτ : (τ ω : ENNReal) ≤ (n : ENNReal)
            · exact Or.inl ⟨hω.1, hωτ⟩
            · exact Or.inr ⟨hω.1, ⟨hω.2, lt_of_not_ge hωτ⟩⟩
          · intro hω
            rcases hω with hω | hω
            · exact ⟨hω.1, (show (σ ω : ENNReal) ≤ τ ω by exact_mod_cast hστ ω).trans hω.2⟩
            · exact ⟨hω.1, hω.2.1⟩
        have hLeft :
            ∫ ω in u, stoppedProcess X tauInf n ω ∂μ =
              ∫ ω in u, stoppedValue X tauInf ω ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [ae_restrict_mem hu_meas] with ω hω
          simpa [tauInf, stoppedValue] using
            (stoppedProcess_eq_of_ge (u := X) (τ := tauInf) (i := (n : NNReal)) (ω := ω) hω.2)
        have hRight :
            ∫ ω in v, stoppedProcess X tauInf n ω ∂μ =
              ∫ ω in s, B n ω ∂μ := by
          calc
            ∫ ω in v, stoppedProcess X tauInf n ω ∂μ
                = ∫ ω in v, X n ω ∂μ := by
                    refine integral_congr_ae ?_
                    filter_upwards [ae_restrict_mem hv_meas] with ω hω
                    have hω_le : (n : ENNReal) ≤ tauInf ω := le_of_lt hω.2.2
                    simpa using
                      (stoppedProcess_eq_of_le
                        (u := X) (τ := tauInf) (i := (n : NNReal)) (ω := ω) hω_le)
            _ = ∫ ω in s, B n ω ∂μ := by
                  symm
                  dsimp [B, v]
                  rw [MeasureTheory.integral_indicator (μ := μ.restrict s) (f := X n)
                    (s := {ω | (σ ω : ENNReal) ≤ (n : ENNReal) ∧ (n : ENNReal) < (τ ω : ENNReal)})
                    (hBandMeas n)]
                  rw [Measure.restrict_restrict (hBandMeas n)]
                  simp [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
        calc
          ∫ ω in s ∩ {ω | (σ ω : ENNReal) ≤ (n : ENNReal)},
              stoppedProcess X tauInf n ω ∂μ
              =
            ∫ ω in u ∪ v, stoppedProcess X tauInf n ω ∂μ := by
                rw [hUnion]
          _ =
            ∫ ω in u, stoppedProcess X tauInf n ω ∂μ +
              ∫ ω in v, stoppedProcess X tauInf n ω ∂μ := by
                have hIntU : IntegrableOn (stoppedProcess X tauInf n) u μ := by
                  refine hτ_int.integrableOn.congr_fun ?_ hu_meas
                  intro ω hω
                  simpa [tauInf, stoppedValue] using
                    (stoppedProcess_eq_of_ge
                      (u := X) (τ := tauInf) (i := (n : NNReal)) (ω := ω) hω.2).symm
                have hIntV : IntegrableOn (stoppedProcess X tauInf n) v μ := by
                  refine (hX.integrable n).integrableOn.congr_fun ?_ hv_meas
                  intro ω hω
                  have hω_le : (n : ENNReal) ≤ tauInf ω := le_of_lt hω.2.2
                  simpa using
                    (stoppedProcess_eq_of_le
                      (u := X) (τ := tauInf) (i := (n : NNReal)) (ω := ω) hω_le).symm
                rw [setIntegral_union hDisj hv_meas hIntU hIntV]
          _ =
            ∫ ω in u, stoppedValue X tauInf ω ∂μ +
              ∫ ω in v, stoppedProcess X tauInf n ω ∂μ := by
                rw [hLeft]
          _ =
            ∫ ω in u, stoppedValue X tauInf ω ∂μ +
              ∫ ω in s, B n ω ∂μ := by
                rw [hRight]
      have hAdd :
          Tendsto
            (fun n : ℕ ↦
              ∫ ω in s ∩ {ω | (τ ω : ENNReal) ≤ (n : ENNReal)},
                stoppedValue X tauInf ω ∂μ +
                  ∫ ω in s, B n ω ∂μ)
            atTop
            (𝓝 (∫ ω in s, stoppedValue X tauInf ω ∂μ + 0)) :=
        hFirst.add hSecond
      rw [hSeqEq]
      simpa using hAdd
    have hSetLe :
        ∫ ω in s, stoppedValue X tauInf ω ∂μ ≤
          ∫ ω in s, stoppedValue X sigmaInf ω ∂μ := by
      let leftSeq : ℕ → ℝ := fun n ↦
        ∫ ω in s ∩ {ω | (σ ω : ENNReal) ≤ (n : ENNReal)},
          stoppedProcess X tauInf n ω ∂μ
      let rightSeq : ℕ → ℝ := fun n ↦
        ∫ ω in s ∩ {ω | (σ ω : ENNReal) ≤ (n : ENNReal)},
          stoppedValue X sigmaInf ω ∂μ
      have hBounded :
          ∀ n : ℕ,
            leftSeq n ≤ rightSeq n :=
        fun n ↦ setIntegralClippedStopsLeOfFiniteTestSet
          (X := X) hX hXrc hσ hτ hστ hs n
      have hPair :
          Tendsto (fun n ↦ (leftSeq n, rightSeq n)) atTop
            (𝓝
              (∫ ω in s, stoppedValue X tauInf ω ∂μ,
                ∫ ω in s, stoppedValue X sigmaInf ω ∂μ)) := by
        simpa [leftSeq, rightSeq, nhds_prod_eq] using hClipLimit.prodMk hSigmaLimit
      have hEventuallyLe :
          ∀ᶠ n in atTop, (leftSeq n, rightSeq n) ∈ {p : ℝ × ℝ | p.1 ≤ p.2} :=
        Filter.Eventually.of_forall fun n ↦ hBounded n
      have hClosed : IsClosed {p : ℝ × ℝ | p.1 ≤ p.2} :=
        isClosed_le continuous_fst continuous_snd
      exact hClosed.mem_of_tendsto hPair hEventuallyLe
    have hLeftTrim :
        ∫ ω in s, μ[stoppedValue X tauInf | hσ.measurableSpace] ω ∂μ.trim hσ.measurableSpace_le =
          ∫ ω in s, stoppedValue X tauInf ω ∂μ := by
      calc
        ∫ ω in s, μ[stoppedValue X tauInf | hσ.measurableSpace] ω ∂μ.trim hσ.measurableSpace_le
            =
          ∫ ω in s, μ[stoppedValue X tauInf | hσ.measurableSpace] ω ∂μ := by
              symm
              exact MeasureTheory.setIntegral_trim hσ.measurableSpace_le hCondMeas hs
        _ = ∫ ω in s, stoppedValue X tauInf ω ∂μ := by
              simpa [tauInf] using
                (MeasureTheory.setIntegral_condExp hσ.measurableSpace_le hτ_int hs)
    have hRightTrim :
        ∫ ω in s, stoppedValue X sigmaInf ω ∂μ =
          ∫ ω in s, stoppedValue X sigmaInf ω ∂μ.trim hσ.measurableSpace_le := by
      exact MeasureTheory.setIntegral_trim hσ.measurableSpace_le hSigmaMeas hs
    calc
      ∫ ω in s, μ[stoppedValue X tauInf | hσ.measurableSpace] ω ∂μ.trim hσ.measurableSpace_le
          = ∫ ω in s, stoppedValue X tauInf ω ∂μ := hLeftTrim
      _ ≤ ∫ ω in s, stoppedValue X sigmaInf ω ∂μ := hSetLe
      _ = ∫ ω in s, stoppedValue X sigmaInf ω ∂μ.trim hσ.measurableSpace_le := hRightTrim
  exact
    (MeasureTheory.StronglyMeasurable.ae_le_trim_iff
      hσ.measurableSpace_le hCondMeas hSigmaMeas).mp hLeTrim

/-- Helper for Exercise 21.1.3: a uniformly integrable right-continuous supermartingale has
integrable finite stopped values. -/
private lemma integrableStoppedValue_of_ui_finiteStoppingTime
    [Filtration.IsRightContinuous ℱ]
    {X : NNReal → Ω → ℝ} (_ : Supermartingale X ℱ μ)
    (_ : HasRightContinuousPaths X) (_ : UniformIntegrable X 1 μ)
    {ρ : Ω → NNReal} (_ : IsStoppingTime ℱ fun ω ↦ (ρ ω : ENNReal)) :
    Integrable (stoppedValue X (fun ω ↦ (ρ ω : ENNReal))) μ := by
  rename_i hX hXrc hX_UI hρ
  let rhoInf : Ω → ENNReal := fun ω ↦ (ρ ω : ENNReal)
  let Y : ℕ → Ω → ℝ := fun n ↦ stoppedProcess X rhoInf n
  have hXNatBound : ∃ C : NNReal, ∀ n : ℕ, ∫ ω, |X n ω| ∂μ ≤ C := by
    rcases hX_UI.2.2 with ⟨C, hC⟩
    refine ⟨C, fun n ↦ ?_⟩
    have hCn := hC n
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (hX.integrable n)] at hCn
    exact (ENNReal.ofReal_le_coe).1 hCn
  have hY_int : ∀ n : ℕ, Integrable (Y n) μ := by
    intro n
    let rhoClip : Ω → NNReal := fun ω ↦ min (ρ ω) n
    have hY_eq :
        stoppedValue X (fun ω ↦ (rhoClip ω : ENNReal)) = Y n := by
      simpa [Y, rhoInf, rhoClip, min_comm] using
        (stoppedValue_min_const_eq_stoppedProcess
          (X := X) (τ := rhoInf) (t := (n : NNReal)))
    have hRhoClip : IsStoppingTime ℱ fun ω ↦ (rhoClip ω : ENNReal) := by
      simpa [rhoClip] using hρ.min_const (n : NNReal)
    have hRhoClip_bdd : ∃ T : NNReal, ∀ ω, rhoClip ω ≤ T := by
      refine ⟨n, ?_⟩
      intro ω
      exact min_le_right _ _
    obtain ⟨hInt, -, -⟩ :=
      expectedStoppedValue_mono_of_le_of_bounded_rightContinuous
        (X := X) hX hXrc hRhoClip hRhoClip (fun _ ↦ le_rfl) hRhoClip_bdd
    simpa [hY_eq] using hInt
  have hYexp_le : ∀ n : ℕ, μ[Y n] ≤ μ[X 0] := by
    intro n
    let zeroStop : Ω → NNReal := fun _ ↦ 0
    let rhoClip : Ω → NNReal := fun ω ↦ min (ρ ω) n
    have hY_eq :
        stoppedValue X (fun ω ↦ (rhoClip ω : ENNReal)) = Y n := by
      simpa [Y, rhoInf, rhoClip, min_comm] using
        (stoppedValue_min_const_eq_stoppedProcess
          (X := X) (τ := rhoInf) (t := (n : NNReal)))
    have hZero : IsStoppingTime ℱ fun ω ↦ (zeroStop ω : ENNReal) :=
      isStoppingTime_const ℱ 0
    have hRhoClip : IsStoppingTime ℱ fun ω ↦ (rhoClip ω : ENNReal) := by
      simpa [rhoClip] using hρ.min_const (n : NNReal)
    have hZeroLe : zeroStop ≤ rhoClip := by
      intro ω
      simp [zeroStop, rhoClip]
    have hRhoClip_bdd : ∃ T : NNReal, ∀ ω, rhoClip ω ≤ T := by
      refine ⟨n, ?_⟩
      intro ω
      exact min_le_right _ _
    obtain ⟨-, -, hle⟩ :=
      expectedStoppedValue_mono_of_le_of_bounded_rightContinuous
        (X := X) hX hXrc hZero hRhoClip hZeroLe hRhoClip_bdd
    simpa [hY_eq, zeroStop, stoppedValue_const] using hle
  have hYnegBound : ∃ C : ℝ, ∀ n : ℕ, ∫ ω, (-Y n ω)⁺ ∂μ ≤ C := by
    rcases hXNatBound with ⟨C, hC⟩
    refine ⟨(C : ℝ), fun n ↦ ?_⟩
    let rhoClip : Ω → NNReal := fun ω ↦ min (ρ ω) n
    have hY_eq :
        stoppedValue X (fun ω ↦ (rhoClip ω : ENNReal)) = Y n := by
      simpa [Y, rhoInf, rhoClip, min_comm] using
        (stoppedValue_min_const_eq_stoppedProcess
          (X := X) (τ := rhoInf) (t := (n : NNReal)))
    have hRhoClip : IsStoppingTime ℱ fun ω ↦ (rhoClip ω : ENNReal) := by
      simpa [rhoClip] using hρ.min_const (n : NNReal)
    have hRhoClip_le_const : rhoClip ≤ fun _ ↦ (n : NNReal) := by
      intro ω
      exact min_le_right _ _
    have hRhoClip_bdd : ∃ T : NNReal, ∀ ω, rhoClip ω ≤ T := by
      refine ⟨n, ?_⟩
      intro ω
      exact min_le_right _ _
    have hStopLe :
        μ[X n | hRhoClip.measurableSpace] ≤ᵐ[μ] Y n := by
      have hRaw :=
        optionalSampling_bounded
          (X := X) hX hXrc hRhoClip (isStoppingTime_const ℱ n) hRhoClip_le_const
          ⟨n, fun _ ↦ le_rfl⟩
      simpa [hY_eq, stoppedValue_const] using hRaw
    have hNegLe :
        (fun ω ↦ (-Y n ω)⁺) ≤ᵐ[μ] μ[(fun ω ↦ |X n ω|) | hRhoClip.measurableSpace] := by
      have hStopNeg :
          (fun ω ↦ -Y n ω) ≤ᵐ[μ] μ[(fun ω ↦ -X n ω) | hRhoClip.measurableSpace] := by
        filter_upwards [hStopLe, condExp_neg (μ := μ) (f := X n) (m := hRhoClip.measurableSpace)]
          with ω hω hωneg
        have hω' : -Y n ω ≤ -μ[X n | hRhoClip.measurableSpace] ω := by
          exact neg_le_neg hω
        calc
          -Y n ω ≤ -μ[X n | hRhoClip.measurableSpace] ω := hω'
          _ = μ[(fun ω ↦ -X n ω) | hRhoClip.measurableSpace] ω := by
                simpa using hωneg.symm
      have hCondMono :
          μ[(fun ω ↦ -X n ω) | hRhoClip.measurableSpace] ≤ᵐ[μ]
            μ[(fun ω ↦ |X n ω|) | hRhoClip.measurableSpace] := by
        refine condExp_mono
          (m := hRhoClip.measurableSpace)
          ((hX.integrable n).neg)
          ((hX.integrable n).norm) ?_
        exact Filter.Eventually.of_forall fun ω ↦
          by simpa [Real.norm_eq_abs] using neg_le_abs (X n ω)
      have hCondNonneg :
          0 ≤ᵐ[μ] μ[(fun ω ↦ |X n ω|) | hRhoClip.measurableSpace] := by
        exact condExp_nonneg <| Filter.Eventually.of_forall fun ω ↦ abs_nonneg (X n ω)
      filter_upwards [hStopNeg, hCondMono, hCondNonneg] with ω hω₁ hω₂ hω₃
      exact max_le_iff.mpr ⟨le_trans hω₁ hω₂, hω₃⟩
    calc
      ∫ ω, (-Y n ω)⁺ ∂μ
          ≤ ∫ ω, μ[(fun ω ↦ |X n ω|) | hRhoClip.measurableSpace] ω ∂μ := by
              exact integral_mono_ae ((hY_int n).neg_part) integrable_condExp hNegLe
      _ = ∫ ω, |X n ω| ∂μ := by
            rw [integral_condExp (μ := μ) (m := hRhoClip.measurableSpace)
              (f := fun ω ↦ |X n ω|) hRhoClip.measurableSpace_le]
      _ ≤ C := hC n
  have hYNormBound : ∃ C : ℝ, ∀ n : ℕ, ∫ ω, ‖Y n ω‖ ∂μ ≤ C := by
    rcases hYnegBound with ⟨Cneg, hCneg⟩
    refine ⟨|μ[X 0]| + 2 * (Cneg : ℝ), fun n ↦ ?_⟩
    have hdecomp :
        μ[Y n] = ∫ ω, (Y n ω)⁺ ∂μ - ∫ ω, (-Y n ω)⁺ ∂μ := by
      simpa using integral_eq_integral_pos_part_sub_integral_neg_part (hY_int n)
    have hpos :
        ∫ ω, (Y n ω)⁺ ∂μ ≤ |μ[X 0]| + Cneg := by
      have haux : ∫ ω, (Y n ω)⁺ ∂μ ≤ μ[X 0] + ∫ ω, (-Y n ω)⁺ ∂μ := by
        linarith [hYexp_le n, hdecomp]
      calc
        ∫ ω, (Y n ω)⁺ ∂μ ≤ μ[X 0] + ∫ ω, (-Y n ω)⁺ ∂μ := haux
        _ ≤ |μ[X 0]| + ∫ ω, (-Y n ω)⁺ ∂μ := by
              gcongr
              exact le_abs_self _
        _ ≤ |μ[X 0]| + Cneg := by
              gcongr
              exact hCneg n
    have hnormEq : ∀ ω, ‖Y n ω‖ = (Y n ω)⁺ + (Y n ω)⁻ := by
      intro ω
      by_cases hω : 0 ≤ Y n ω
      · rw [Real.norm_eq_abs, abs_of_nonneg hω, posPart_eq_self.2 hω,
          negPart_eq_zero.2 hω, add_zero]
      · have hω' : Y n ω ≤ 0 := le_of_not_ge hω
        rw [Real.norm_eq_abs, abs_of_nonpos hω', posPart_eq_zero.2 hω',
          negPart_eq_neg.2 hω', zero_add]
    calc
      ∫ ω, ‖Y n ω‖ ∂μ = ∫ ω, ((Y n ω)⁺ + (-Y n ω)⁺) ∂μ := by
        refine integral_congr_ae ?_
        exact ae_of_all μ (hnormEq)
      _ = ∫ ω, (Y n ω)⁺ ∂μ + ∫ ω, (Y n ω)⁻ ∂μ := by
            simpa [posPart, negPart] using integral_add (hY_int n).pos_part (hY_int n).neg_part
      _ ≤ (|μ[X 0]| + Cneg) + Cneg := by
            gcongr
            exact hCneg n
      _ = |μ[X 0]| + 2 * Cneg := by ring
  have hY_tendsto :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Y n ω) atTop (𝓝 (stoppedValue X rhoInf ω)) := by
    refine Filter.Eventually.of_forall fun ω ↦ ?_
    have hEq :
        (fun n ↦ Y n ω) =ᶠ[atTop] fun _ ↦ stoppedValue X rhoInf ω := by
      filter_upwards
        [show ∀ᶠ n : ℕ in atTop, Nat.ceil (ρ ω : ℝ) ≤ n from
          Filter.eventually_ge_atTop (Nat.ceil (ρ ω : ℝ))] with n hn
      have hρ_le_n_real : (ρ ω : ℝ) ≤ n := by
        exact le_trans (Nat.le_ceil (ρ ω : ℝ)) (by exact_mod_cast hn)
      have hρ_le_n_nn : ρ ω ≤ n := by
        exact_mod_cast hρ_le_n_real
      have hρ_le_n : rhoInf ω ≤ (n : ENNReal) := by
        change (ρ ω : ENNReal) ≤ (n : ENNReal)
        exact_mod_cast hρ_le_n_nn
      simpa [Y, rhoInf, stoppedValue] using
        (stoppedProcess_eq_of_ge (u := X) (τ := rhoInf) (i := (n : NNReal)) (ω := ω) hρ_le_n)
    exact Tendsto.congr' hEq.symm tendsto_const_nhds
  have hStoppedMeas :
      AEStronglyMeasurable (stoppedValue X rhoInf) μ := by
    exact aestronglyMeasurable_of_tendsto_ae atTop
      (fun n ↦ (hY_int n).aestronglyMeasurable) hY_tendsto
  rcases hYNormBound with ⟨C, hC⟩
  have hFatou :
      ∫⁻ ω, ENNReal.ofReal (‖stoppedValue X rhoInf ω‖) ∂μ ≤
        Filter.liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal (‖Y n ω‖) ∂μ) atTop := by
    calc
      ∫⁻ ω, ENNReal.ofReal (‖stoppedValue X rhoInf ω‖) ∂μ
          = ∫⁻ ω, Filter.liminf (fun n ↦ ENNReal.ofReal (‖Y n ω‖)) atTop ∂μ := by
              refine lintegral_congr_ae ?_
              filter_upwards [hY_tendsto] with ω hω
              exact ((ENNReal.continuous_ofReal.tendsto ‖stoppedValue X rhoInf ω‖).comp
                (hω.norm)).liminf_eq.symm
      _ ≤ Filter.liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal (‖Y n ω‖) ∂μ) atTop := by
            refine MeasureTheory.lintegral_liminf_le' ?_
            intro n
            exact ((hY_int n).norm.aestronglyMeasurable.aemeasurable).ennreal_ofReal
  have hLiminfBound :
      Filter.liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal (‖Y n ω‖) ∂μ) atTop ≤ ENNReal.ofReal C := by
    refine Filter.liminf_le_of_frequently_le ?_
    refine (Filter.Eventually.of_forall fun n ↦ ?_).frequently
    calc
      ∫⁻ ω, ENNReal.ofReal (‖Y n ω‖) ∂μ = ENNReal.ofReal (∫ ω, ‖Y n ω‖ ∂μ) := by
        simpa [Real.norm_eq_abs] using
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hY_int n).norm)
            (Filter.Eventually.of_forall fun ω ↦ abs_nonneg (Y n ω))).symm
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (hC n)
  have hNormFinite :
      ∫⁻ ω, ENNReal.ofReal (‖stoppedValue X rhoInf ω‖) ∂μ ≠ ⊤ := by
    exact (lt_of_le_of_lt (hFatou.trans hLiminfBound) ENNReal.ofReal_lt_top).ne
  exact
    (integrable_norm_iff hStoppedMeas).mp <|
      (lintegral_ofReal_ne_top_iff_integrable hStoppedMeas.norm
        (Filter.Eventually.of_forall fun ω ↦ norm_nonneg _)).1 <| by
          simpa using hNormFinite

/-- Helper for this exercise: a uniformly integrable right-continuous supermartingale satisfies
the optional sampling inequality for finite stopping times `σ ≤ τ`. -/
private theorem optionalSampling_finite :
    [Filtration.IsRightContinuous ℱ] →
    ∀ {X : NNReal → Ω → ℝ} (_ : Supermartingale X ℱ μ)
      (_ : HasRightContinuousPaths X)
      (_ : UniformIntegrable X 1 μ)
      {σ τ : Ω → NNReal}
      (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
      (_ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal))
      (_ : σ ≤ τ),
      μ[stoppedValue X (fun ω ↦ (τ ω : ENNReal)) | hσ.measurableSpace] ≤ᵐ[μ]
        stoppedValue X (fun ω ↦ (σ ω : ENNReal)) := by
  intro _ X hX hXrc hX_UI σ τ hσ hτ hστ
  have hσ_int :
      Integrable (stoppedValue X (fun ω ↦ (σ ω : ENNReal))) μ :=
    integrableStoppedValue_of_ui_finiteStoppingTime hX hXrc hX_UI hσ
  have hτ_int :
      Integrable (stoppedValue X (fun ω ↦ (τ ω : ENNReal))) μ :=
    integrableStoppedValue_of_ui_finiteStoppingTime hX hXrc hX_UI hτ
  -- Proof comment: once the exact finite stopped values are known to be integrable, the theorem
  -- is the clipped bounded inequality plus the finite-test-set limit package assembled above.
  exact
    optionalSampling_finite_of_integrableStoppedValues
      (X := X) hX hXrc hX_UI hσ hτ hστ hσ_int hτ_int

/-- Helper for this exercise: stopping a right-continuous supermartingale at a stopping time again
produces a right-continuous supermartingale. -/
private theorem stoppedProcess_supermartingale_and_rightContinuous :
    [Filtration.IsRightContinuous ℱ] →
    ∀ {X : NNReal → Ω → ℝ} (_ : Supermartingale X ℱ μ)
      (_ : HasRightContinuousPaths X)
      {τ : Ω → ENNReal} (_ : IsStoppingTime ℱ τ),
      Supermartingale (stoppedProcess X τ) ℱ μ ∧
        HasRightContinuousPaths (stoppedProcess X τ) := by
  intro _ X hX hXrc τ hτ
  classical
  have hrc : HasRightContinuousPaths (stoppedProcess X τ) :=
    stoppedProcess_hasRightContinuousPaths hXrc
  have hAdapted : StronglyAdapted ℱ (stoppedProcess X τ) :=
    (progMeasurable_of_adaptedRightContinuous hX.1.adapted hXrc).stronglyAdapted_stoppedProcess hτ
  have hInt : ∀ t : NNReal, Integrable (stoppedProcess X τ t) μ := by
    intro t
    have hσt : IsStoppingTime ℱ fun ω ↦ (clippedStoppingTimeNNReal τ t ω : ENNReal) :=
      clippedStoppingTimeNNReal_isStoppingTime hτ t
    have hσt_bdd : ∃ T : NNReal, ∀ ω, clippedStoppingTimeNNReal τ t ω ≤ T :=
      ⟨t, clippedStoppingTimeNNReal_le_const (τ := τ) (t := t)⟩
    obtain ⟨hσt_int, -, -⟩ :=
      expectedStoppedValue_mono_of_le_of_bounded_rightContinuous
        hX hXrc hσt hσt (fun _ ↦ le_rfl) hσt_bdd
    simpa using
      (hσt_int.congr
        (Filter.EventuallyEq.of_eq
          (stoppedValue_clippedStoppingTimeNNReal_eq_stoppedProcess
            (X := X) (τ := τ) (t := t))))
  have hSetLe :
      ∀ s t : NNReal, s ≤ t → ∀ A : Set Ω, MeasurableSet[ℱ s] A →
        ∫ ω in A, stoppedProcess X τ t ω ∂μ ≤
          ∫ ω in A, stoppedProcess X τ s ω ∂μ := by
    intro s t hst A hA
    let B₁ : Set Ω := A ∩ {ω | τ ω ≤ (s : ENNReal)}
    let B₂ : Set Ω := A ∩ {ω | (s : ENNReal) < τ ω}
    have hA_meas : MeasurableSet A := (ℱ.le s) _ hA
    have hTauGt_fs : MeasurableSet[ℱ s] {ω | (s : ENNReal) < τ ω} := by
      simpa [Set.compl_setOf, not_le] using (hτ s).compl
    have hTauGt : MeasurableSet {ω | (s : ENNReal) < τ ω} := (ℱ.le s) _ hTauGt_fs
    have hB₁_meas : MeasurableSet B₁ := hA_meas.inter ((ℱ.le s) _ (hτ s))
    have hB₂_meas : MeasurableSet B₂ := hA_meas.inter hTauGt
    have hB₂_meas_fs : MeasurableSet[ℱ s] B₂ := hA.inter hTauGt_fs
    have hDisj : Disjoint B₁ B₂ := by
      refine Set.disjoint_left.2 fun ω hω₁ hω₂ ↦ ?_
      exact not_lt_of_ge (by simpa using hω₁.2) (by simpa using hω₂.2)
    have hUnion : A = B₁ ∪ B₂ := by
      ext ω
      constructor
      · intro hωA
        by_cases hωs : τ ω ≤ (s : ENNReal)
        · exact Or.inl ⟨hωA, hωs⟩
        · exact Or.inr ⟨hωA, lt_of_not_ge hωs⟩
      · intro hω
        exact hω.elim (fun h ↦ h.1) fun h ↦ h.1
    have hEqOn₁ : EqOn (stoppedProcess X τ t) (stoppedProcess X τ s) B₁ := by
      intro ω hω
      have hωs : τ ω ≤ (s : ENNReal) := hω.2
      rw [stoppedProcess_eq_of_ge (u := X) (τ := τ) (i := t) (ω := ω)
          (hωs.trans (show (t : ENNReal) ≥ (s : ENNReal) from by exact_mod_cast hst))]
      rw [stoppedProcess_eq_of_ge (u := X) (τ := τ) (i := s) (ω := ω) hωs]
    let σs : Ω → NNReal := fun _ ↦ s
    let τt : Ω → NNReal := fun ω ↦ max (clippedStoppingTimeNNReal τ t ω) s
    let ρ : Ω → NNReal := Set.piecewise B₂ τt σs
    have hσs : IsStoppingTime ℱ fun ω ↦ (σs ω : ENNReal) :=
      isStoppingTime_const ℱ s
    have hτt : IsStoppingTime ℱ fun ω ↦ (τt ω : ENNReal) := by
      have hτt_eq :
          (fun ω ↦ (τt ω : ENNReal)) =
            fun ω ↦ max ((clippedStoppingTimeNNReal τ t ω : NNReal) : ENNReal) (s : ENNReal) := by
        funext ω
        simp [τt]
      rw [hτt_eq]
      exact (clippedStoppingTimeNNReal_isStoppingTime hτ t).max_const s
    have hσs_le_τt : σs ≤ τt := by
      intro ω
      exact le_max_right _ _
    have hσs_le_τt_inf :
        (fun ω ↦ (σs ω : ENNReal)) ≤ fun ω ↦ (τt ω : ENNReal) := by
      intro ω
      exact ENNReal.coe_le_coe.mpr (hσs_le_τt ω)
    have hρ : IsStoppingTime ℱ fun ω ↦ (ρ ω : ENNReal) := by
      have hσs_ms : hσs.measurableSpace = ℱ s := by
        simpa [σs] using IsStoppingTime.measurableSpace_const ℱ s
      have hB₂_meas_hσ : MeasurableSet[hσs.measurableSpace] B₂ := by
        rw [hσs_ms]
        exact hB₂_meas_fs
      have hρ_eq :
          (fun ω ↦ (ρ ω : ENNReal)) =
            Set.piecewise B₂ (fun ω ↦ (τt ω : ENNReal)) (fun ω ↦ (σs ω : ENNReal)) := by
        funext ω
        by_cases hω : ω ∈ B₂ <;> simp [ρ, hω]
      rw [hρ_eq]
      exact
        isStoppingTime_piecewise_of_mem_measurableSpace
          hσs hτt hσs_le_τt_inf hB₂_meas_hσ
    have hρ_bdd : ∃ T : NNReal, ∀ ω, ρ ω ≤ T := by
      refine ⟨t, ?_⟩
      intro ω
      by_cases hω : ω ∈ B₂
      · have hτt_le : τt ω ≤ t := by
          exact max_le (clippedStoppingTimeNNReal_le_const (τ := τ) (t := t) ω) hst
        simpa [ρ, hω] using hτt_le
      · simpa [ρ, hω] using hst
    have hσs_le_ρ : σs ≤ ρ := by
      intro ω
      by_cases hω : ω ∈ B₂
      · simpa [ρ, hω] using hσs_le_τt ω
      · simp [ρ, hω]
    have hStopLe :
        μ[stoppedValue X (fun ω ↦ (ρ ω : ENNReal)) | ℱ s] ≤ᵐ[μ] X s := by
      have hσs_ms : hσs.measurableSpace = ℱ s := by
        simpa [σs] using IsStoppingTime.measurableSpace_const ℱ s
      have hRaw :=
        optionalSampling_bounded hX hXrc hσs hρ hσs_le_ρ hρ_bdd
      rw [hσs_ms] at hRaw
      simpa [σs, stoppedValue_const] using hRaw
    have hρ_int : Integrable (stoppedValue X (fun ω ↦ (ρ ω : ENNReal))) μ := by
      obtain ⟨hρ_int, -, -⟩ :=
        expectedStoppedValue_mono_of_le_of_bounded_rightContinuous
          hX hXrc hρ hρ (fun _ ↦ le_rfl) hρ_bdd
      exact hρ_int
    have hSetLe₂ :
        ∫ ω in B₂, stoppedProcess X τ t ω ∂μ ≤ ∫ ω in B₂, stoppedProcess X τ s ω ∂μ := by
      have hStoppedρ :
          EqOn (stoppedValue X (fun ω ↦ (ρ ω : ENNReal))) (stoppedProcess X τ t) B₂ := by
        intro ω hω
        have hωτ : (s : ENNReal) < τ ω := hω.2
        have hs_le_clip : s ≤ clippedStoppingTimeNNReal τ t ω := by
          refine ENNReal.coe_le_coe.mp ?_
          have hmin_eq :
              (clippedStoppingTimeNNReal τ t ω : ENNReal) = min (τ ω) (t : ENNReal) := by
            simpa [clippedStoppingTimeNNReal, ENNReal.coe_toNNReal]
          rw [hmin_eq]
          exact le_min hωτ.le (show (s : ENNReal) ≤ (t : ENNReal) from by exact_mod_cast hst)
        have hclip : clippedStoppingTimeNNReal τ t ω = max (clippedStoppingTimeNNReal τ t ω) s := by
          symm
          exact max_eq_left hs_le_clip
        have hρ_eq : ρ ω = clippedStoppingTimeNNReal τ t ω := by
          calc
            ρ ω = τt ω := by simp [ρ, hω]
            _ = max (clippedStoppingTimeNNReal τ t ω) s := rfl
            _ = clippedStoppingTimeNNReal τ t ω := max_eq_left hs_le_clip
        simpa [stoppedValue, hρ_eq] using
          congrFun
            (stoppedValue_clippedStoppingTimeNNReal_eq_stoppedProcess
              (X := X) (τ := τ) (t := t))
            ω
      have hStoppedS :
          EqOn (X s) (stoppedProcess X τ s) B₂ := by
        intro ω hω
        exact (stoppedProcess_eq_of_le (u := X) (τ := τ) (i := s) (ω := ω) hω.2.le).symm
      have hLeft :
          ∫ ω in B₂, stoppedValue X (fun ω ↦ (ρ ω : ENNReal)) ω ∂μ ≤ ∫ ω in B₂, X s ω ∂μ := by
        calc
          ∫ ω in B₂, stoppedValue X (fun ω ↦ (ρ ω : ENNReal)) ω ∂μ
              = ∫ ω in B₂, μ[stoppedValue X (fun ω ↦ (ρ ω : ENNReal)) | ℱ s] ω ∂μ := by
                  symm
                  exact setIntegral_condExp (ℱ.le s) hρ_int hB₂_meas_fs
          _ ≤ ∫ ω in B₂, X s ω ∂μ := by
                exact MeasureTheory.setIntegral_mono_ae
                  integrable_condExp.integrableOn (hX.integrable s).integrableOn hStopLe
      calc
        ∫ ω in B₂, stoppedProcess X τ t ω ∂μ
            = ∫ ω in B₂, stoppedValue X (fun ω ↦ (ρ ω : ENNReal)) ω ∂μ := by
                symm
                exact setIntegral_congr_fun hB₂_meas hStoppedρ
        _ ≤ ∫ ω in B₂, X s ω ∂μ := hLeft
        _ = ∫ ω in B₂, stoppedProcess X τ s ω ∂μ := by
              exact setIntegral_congr_fun hB₂_meas hStoppedS
    have hSplit_t :
        ∫ ω in A, stoppedProcess X τ t ω ∂μ =
          ∫ ω in B₁, stoppedProcess X τ t ω ∂μ +
            ∫ ω in B₂, stoppedProcess X τ t ω ∂μ := by
      rw [hUnion]
      exact setIntegral_union hDisj hB₂_meas (hInt t).integrableOn (hInt t).integrableOn
    have hSplit_s :
        ∫ ω in A, stoppedProcess X τ s ω ∂μ =
          ∫ ω in B₁, stoppedProcess X τ s ω ∂μ +
            ∫ ω in B₂, stoppedProcess X τ s ω ∂μ := by
      rw [hUnion]
      exact setIntegral_union hDisj hB₂_meas (hInt s).integrableOn (hInt s).integrableOn
    have hSetEq₁ :
        ∫ ω in B₁, stoppedProcess X τ t ω ∂μ =
          ∫ ω in B₁, stoppedProcess X τ s ω ∂μ :=
      setIntegral_congr_fun hB₁_meas hEqOn₁
    linarith
  -- Route correction: prove the stopped process by the set-integral characterization, using the
  -- bounded optional-sampling theorem only on the measurable piece where the stopping time has
  -- not yet occurred.
  have hSubNeg : Submartingale (-(stoppedProcess X τ)) ℱ μ := by
    refine submartingale_of_setIntegral_le hAdapted.neg (fun t ↦ (hInt t).neg) ?_
    intro s t hst A hA
    have hSet := hSetLe s t hst A hA
    simpa [Pi.neg_apply, integral_neg, neg_le_neg_iff] using hSet
  have hSuper : Supermartingale (stoppedProcess X τ) ℱ μ := by
    simpa using hSubNeg.neg
  exact ⟨hSuper, hrc⟩

/-- Exercise 21.1.3 (1): item (i.a). The dyadic conditional expectations of `X_{τ^m}` converge
almost surely and in `L¹` to the conditional expectation with respect to `𝓕_σ`. -/
theorem exercise_21_1_3_i_a :
    ∀ {X : NNReal → Ω → ℝ}
      (_ : Supermartingale X ℱ μ) (_ : HasRightContinuousPaths X)
      {σ τ : Ω → NNReal}
      (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
      (_ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal))
      (_ : σ ≤ τ)
      (_ : ∃ T : NNReal, ∀ ω, σ ω ≤ T)
      (_ : ∃ T : NNReal, ∀ ω, τ ω ≤ T)
      [Filtration.IsRightContinuous ℱ],
      ∀ m : ℕ,
        (∀ᵐ ω ∂μ,
          Tendsto
            (fun n ↦
              μ[stoppedValue X (fun ω' ↦ (dyadicCeilApprox m τ ω' : ENNReal)) |
                (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace] ω)
            atTop
            (𝓝
              (μ[stoppedValue X (fun ω' ↦ (dyadicCeilApprox m τ ω' : ENNReal)) |
                hσ.measurableSpace] ω))) ∧
        Tendsto
          (fun n ↦
            eLpNorm
              (μ[stoppedValue X (fun ω' ↦ (dyadicCeilApprox m τ ω' : ENNReal)) |
                  (dyadicCeilApprox_isStoppingTime hσ n).measurableSpace] -
                μ[stoppedValue X (fun ω' ↦ (dyadicCeilApprox m τ ω' : ENNReal)) |
                  hσ.measurableSpace])
              1 μ)
          atTop (𝓝 0) := by
  intro X hX hXrc σ τ hσ hτ hστ hσ_bdd hτ_bdd _ m
  constructor
  · -- Proof comment: the almost-sure dyadic conditional-expectation convergence is exactly the
    -- theorem-local reverse-Lévy statement for the stopping-time sigma-algebras.
    exact dyadic_condexp_tendsto_ae hX hXrc hσ hτ hστ hσ_bdd hτ_bdd m
  · -- Proof comment: the matching `L¹` convergence is now a direct application of the imported
    -- sigma-finite reverse-Lévy theorem specialized to the dyadic stopping-time family.
    exact dyadic_condexp_tendsto_L1 hX hXrc hσ hτ hστ hσ_bdd hτ_bdd m

/-- Exercise 21.1.3 (2): item (i.b). The dyadic stopped values `X_{σ^n}` converge almost surely
and in `L¹` to `X_σ`. -/
theorem exercise_21_1_3_i_b :
    ∀ {X : NNReal → Ω → ℝ} (_ : Supermartingale X ℱ μ) (_ : HasRightContinuousPaths X)
      {σ : Ω → NNReal}
      (_ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
      (_ : ∃ T : NNReal, ∀ ω, σ ω ≤ T)
      [Filtration.IsRightContinuous ℱ],
      (∀ᵐ ω ∂μ,
        Tendsto
          (fun n ↦ stoppedValue X (fun ω' ↦ (dyadicCeilApprox n σ ω' : ENNReal)) ω)
          atTop
          (𝓝 (stoppedValue X (fun ω' ↦ (σ ω' : ENNReal)) ω))) ∧
      Tendsto
        (fun n ↦
          eLpNorm
            (fun ω ↦
              stoppedValue X (fun ω' ↦ (dyadicCeilApprox n σ ω' : ENNReal)) ω -
                stoppedValue X (fun ω' ↦ (σ ω' : ENNReal)) ω)
            1 μ)
        atTop (𝓝 0) := by
  intro X hX hXrc σ hσ hσ_bdd _
  constructor
  · -- Proof comment: this is the almost-sure right-continuity convergence proved above.
    exact dyadic_stoppedValue_tendsto_ae hX hXrc hσ hσ_bdd
  · -- Proof comment: the `L¹` convergence is delegated to the theorem-local dyadic helper so the
    -- remaining blocker stays isolated in one place.
    exact dyadic_stoppedValue_tendsto_L1 hX hXrc hσ hσ_bdd

/-- Exercise 21.1.3 (3): item (ii). A right-continuous supermartingale satisfies the optional
sampling inequality for bounded stopping times `σ ≤ τ`. -/
theorem exercise_21_1_3_ii :
    ∀ {X : NNReal → Ω → ℝ} (_ : Supermartingale X ℱ μ) (_ : HasRightContinuousPaths X)
      {σ τ : Ω → NNReal}
      (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
      (_ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal))
      (_ : σ ≤ τ) (_ : ∃ T : NNReal, ∀ ω, τ ω ≤ T)
      [Filtration.IsRightContinuous ℱ],
      μ[stoppedValue X (fun ω ↦ (τ ω : ENNReal)) | hσ.measurableSpace] ≤ᵐ[μ]
        stoppedValue X (fun ω ↦ (σ ω : ENNReal)) := by
  intro X hX hXrc σ τ hσ hτ hστ hτ_bdd _
  -- Proof comment: the public bounded optional-sampling statement is exactly the theorem-local
  -- helper proved above.
  exact optionalSampling_bounded hX hXrc hσ hτ hστ hτ_bdd

/-- Exercise 21.1.3 (4): item (iii). An adapted integrable right-continuous process is a
martingale iff every bounded stopping time preserves its initial expectation. -/
theorem exercise_21_1_3_iii :
    ∀ {Y : NNReal → Ω → ℝ} (_ : Adapted ℱ Y)
      (_ : ∀ t : NNReal, Integrable (Y t) μ)
      (_ : HasRightContinuousPaths Y)
      [Filtration.IsRightContinuous ℱ],
      Martingale Y ℱ μ ↔
        ∀ τ : Ω → NNReal, IsStoppingTime ℱ (fun ω ↦ (τ ω : ENNReal)) →
          (∃ T : NNReal, ∀ ω, τ ω ≤ T) →
            μ[stoppedValue Y (fun ω ↦ (τ ω : ENNReal))] = μ[Y 0] := by
  intro Y hY_adapted hY_int hYrc _
  -- Proof comment: this is the public wrapper around the theorem-local characterization proved
  -- from bounded optional sampling.
  exact expectedStoppedValue_iff_martingale hY_adapted hY_int hYrc

/-- Exercise 21.1.3 (5): item (iv). A uniformly integrable right-continuous supermartingale
satisfies the optional sampling inequality for finite stopping times `σ ≤ τ`. -/
theorem exercise_21_1_3_iv :
    ∀ {X : NNReal → Ω → ℝ} (_ : Supermartingale X ℱ μ)
      (_ : HasRightContinuousPaths X)
      (_ : UniformIntegrable X 1 μ)
      {σ τ : Ω → NNReal}
      (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : ENNReal))
      (_ : IsStoppingTime ℱ fun ω ↦ (τ ω : ENNReal))
      (_ : σ ≤ τ)
      [Filtration.IsRightContinuous ℱ],
      μ[stoppedValue X (fun ω ↦ (τ ω : ENNReal)) | hσ.measurableSpace] ≤ᵐ[μ]
        stoppedValue X (fun ω ↦ (σ ω : ENNReal)) := by
  intro X hX hXrc hX_UI σ τ hσ hτ hστ _
  -- Proof comment: the public finite-stop statement is the theorem-local uniformly integrable
  -- optional-sampling result.
  exact optionalSampling_finite hX hXrc hX_UI hσ hτ hστ

/-- Exercise 21.1.3 (6): item (v). Stopping a right-continuous supermartingale at a stopping time
again produces a right-continuous supermartingale. -/
theorem exercise_21_1_3_v :
    ∀ {X : NNReal → Ω → ℝ} (_ : Supermartingale X ℱ μ)
      (_ : HasRightContinuousPaths X)
      {τ : Ω → ENNReal} (_ : IsStoppingTime ℱ τ)
      [Filtration.IsRightContinuous ℱ],
      Supermartingale (stoppedProcess X τ) ℱ μ ∧
        HasRightContinuousPaths (stoppedProcess X τ) := by
  intro X hX hXrc τ hτ _
  -- Proof comment: the public stopped-process theorem is the theorem-local structural result.
  exact stoppedProcess_supermartingale_and_rightContinuous hX hXrc hτ

end ProbabilityTheory

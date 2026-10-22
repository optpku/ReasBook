/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_22
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Theorem_7_21

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped MeasureTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

namespace MeasureTheory
namespace Filtration

private abbrev ambientCompletedMeasurableSpace
    (μ : Measure Ω) : MeasurableSpace (NullMeasurableSpace Ω μ) :=
  inferInstance

private noncomputable abbrev completedRightLimitMeasurableSpace
    (μ : Measure Ω) (ℱ : Filtration NNReal mΩ) (t : NNReal) :
    MeasurableSpace (NullMeasurableSpace Ω μ) :=
  @eventuallyMeasurableSpace Ω (ℱ₊ t) (ae μ) inferInstance

-- The usual augmentation completes each right-limit `σ`-algebra with respect to the ambient
-- measure `μ`, so monotonicity only needs the monotonicity of `ℱ₊`.
private theorem completed_right_continuous_filtration_mono
    (μ : Measure Ω) (ℱ : Filtration NNReal mΩ) :
    Monotone (completedRightLimitMeasurableSpace μ ℱ) := by
  -- Each stage is obtained by adjoining `μ`-null sets to `ℱ₊ t`, so monotonicity is inherited
  -- from the right-limit filtration.
  intro s t hst
  intro A hA
  rcases hA with ⟨U, hU, hAU⟩
  exact ⟨U, (ℱ₊.mono hst) _ hU, hAU⟩

-- Each completed stage still sits inside the ambient `μ`-completion of `mΩ`.
private theorem completed_right_continuous_filtration_le
    (μ : Measure Ω) (ℱ : Filtration NNReal mΩ) (t : NNReal) :
    completedRightLimitMeasurableSpace μ ℱ t ≤
      ambientCompletedMeasurableSpace μ := by
  -- The witness set is already measurable for `mΩ`, hence also for the ambient completion.
  intro s hs
  rcases hs with ⟨U, hU, hsU⟩
  exact ⟨U, (ℱ₊.le t) _ hU, hsU⟩

/-- The textbook filtration `ℱ^{+,*}` obtained by completing each right-limit σ-algebra
`ℱ_t^+` with respect to the ambient measure `μ`. -/
noncomputable def completed_right_continuous_filtration
    (μ : Measure Ω) (ℱ : Filtration NNReal mΩ) :
    Filtration NNReal (ambientCompletedMeasurableSpace μ) where
  seq t := completedRightLimitMeasurableSpace μ ℱ t
  mono' := completed_right_continuous_filtration_mono μ ℱ
  le' := completed_right_continuous_filtration_le μ ℱ

/-- Lean notation `ℱ^+*[μ]`, formalizing the textbook completed augmentation `ℱ^{+,*}`. -/
scoped[MeasureTheory] notation:arg ℱ "^+*[" μ "]" =>
  Filtration.completed_right_continuous_filtration μ ℱ

/- The source notation `ℱ^{+,*}` is formalized by `ℱ^+*[μ]`, the filtration
`completed_right_continuous_filtration μ ℱ`
on the completed measurable space `NullMeasurableSpace Ω μ`. -/

/- At time `t`, the filtration `ℱ^+*[μ]` is the null-measurable completion of the right-limit
`σ`-algebra `ℱ_t^+` with respect to the ambient measure `μ`. -/
theorem completed_right_continuous_filtration_apply
    (μ : Measure Ω) (ℱ : Filtration NNReal mΩ) (t : NNReal) :
    (ℱ^+*[μ]) t =
      @eventuallyMeasurableSpace Ω (ℱ₊ t) (ae μ) inferInstance := rfl

/- A set is measurable for `(ℱ^+*[μ]) t` exactly when it is null-measurable for the ambient
measure `μ` on the right-limit `σ`-algebra `ℱ₊ t`. -/
theorem measurableSet_completed_right_continuous_filtration_iff
    (μ : Measure Ω) (ℱ : Filtration NNReal mΩ) (t : NNReal) {s : Set Ω} :
    MeasurableSet[(ℱ^+*[μ]) t] s ↔
      ∃ U : Set Ω, MeasurableSet[ℱ₊ t] U ∧ s =ᵐ[μ] U := Iff.rfl

/-- Helper for Exercise 21.4.5: trimming `μ` to a smaller σ-algebra preserves the value on sets
already measurable for that smaller σ-algebra. -/
private theorem trim_apply_eq_of_measurable
    (μ : Measure Ω) {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {s : Set Ω}
    (hs : MeasurableSet[m] s) :
    μ.trim hm s = μ s := by
  -- Route correction: `trim` agrees with the ambient measure on the smaller measurable sets, but
  -- not on arbitrary sets.
  exact trim_measurableSet_eq hm hs

/-- Helper for Exercise 21.4.5: measurability in the right limit of `ℱ^+*[μ]` is exactly the
family of later-time null-measurability statements. -/
private theorem completedRightContinuous_rightCont_measurableSet_iff
    (μ : Measure Ω) (ℱ : Filtration NNReal mΩ) {t : NNReal} {s : Set Ω} :
    MeasurableSet[((ℱ^+*[μ])₊) t] s ↔
      ∀ u > t, ∃ U : Set Ω, MeasurableSet[ℱ₊ u] U ∧ s =ᵐ[μ] U := by
  -- Unfold the right limit as an infimum over future stages, then unpack each completed stage.
  rw [Filtration.rightCont_eq (𝓕 := (ℱ^+*[μ])) t]
  simp [measurableSet_completed_right_continuous_filtration_iff, MeasurableSpace.measurableSet_iInf]

/-- Helper for Exercise 21.4.5: if a set is null-measurable for every later completed right-limit
stage, then it is already null-measurable at the current right-limit stage. -/
private theorem completedRightContinuous_nullMeasurableSet_of_forall_gt
    (μ : Measure Ω) (ℱ : Filtration NNReal mΩ) {t : NNReal} {s : Set Ω}
    (hs : ∀ u > t, ∃ U : Set Ω, MeasurableSet[ℱ₊ u] U ∧ s =ᵐ[μ] U) :
    ∃ U : Set Ω, MeasurableSet[ℱ₊ t] U ∧ s =ᵐ[μ] U := by
  let u : ℕ → NNReal := fun n ↦ t + 1 / (n + 1 : NNReal)
  have hu_gt : ∀ n, t < u n := by
    intro n
    simp [u]
  have hu_antitone : Antitone u := by
    intro n m hnm
    rcases lt_or_eq_of_le hnm with hnm' | rfl
    · simpa [u, add_comm, add_left_comm, add_assoc] using
        add_le_add_left (Nat.one_div_lt_one_div hnm').le t
    · rfl
  have hu_cofinal : ∀ {v : NNReal}, t < v → ∃ n, u n ≤ v := by
    intro v hv
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (tsub_pos_of_lt hv)
    refine ⟨n, ?_⟩
    simpa [u, add_comm, add_left_comm, add_assoc, add_tsub_cancel_of_le hv.le] using
      (add_lt_add_left hn t).le
  choose V hV_meas hV_ae using fun n ↦ hs (u n) (hu_gt n)
  let S : ℕ → Set Ω := fun n ↦ ⋂ k : ℕ, V (n + k)
  have hS_mono : Monotone S := by
    intro n m hnm
    rcases Nat.exists_eq_add_of_le hnm with ⟨d, rfl⟩
    refine Set.iInter_mono' ?_
    intro k
    refine ⟨d + k, ?_⟩
    simp [Nat.add_left_comm, Nat.add_comm]
  have hS_meas : ∀ n, MeasurableSet[ℱ₊ (u n)] (S n) := by
    intro n
    -- Each tail intersection is measurable at time `u n` because every later witness lives in a
    -- smaller `σ`-algebra and hence is measurable for the larger stage `u n`.
    refine MeasurableSet.iInter fun k ↦ ?_
    exact (ℱ₊.mono (hu_antitone (Nat.le_add_right n k))) _ (hV_meas (n + k))
  have hS_ae : ∀ n, S n =ᵐ[μ] s := by
    intro n
    -- Countable intersections preserve a.e. equality, so each tail intersection still agrees with
    -- `s` almost surely.
    simpa [S, Set.iInter_const] using
      (Filter.EventuallyEq.countable_iInter fun k ↦ hV_ae (n + k)).symm
  let U : Set Ω := ⋃ n, S n
  have hU_ae : U =ᵐ[μ] s := by
    -- Countable unions preserve a.e. equality, and the constant union of `s` is `s`.
    simpa [U, Set.iUnion_const] using Filter.EventuallyEq.countable_iUnion hS_ae
  have hU_future : ∀ n, MeasurableSet[ℱ₊ (u n)] U := by
    intro n
    -- Rewrite the global union as the tail union starting at `n`; monotonicity of the tail
    -- intersections lets us discard the finitely many earlier terms.
    have htail : U = ⋃ k, S (k + n) := by
      simpa [U, Nat.add_comm] using (hS_mono.iUnion_nat_add n).symm
    rw [htail]
    refine MeasurableSet.iUnion fun k ↦ ?_
    simpa [Nat.add_comm] using
      (ℱ₊.mono (hu_antitone (Nat.le_add_left n k))) _ (hS_meas (k + n))
  have hU_meas : MeasurableSet[ℱ₊ t] U := by
    have hU_plus : MeasurableSet[((ℱ₊)₊) t] U := by
      -- It is enough to check measurability on a cofinal future sequence above `t`.
      rw [Filtration.rightCont_eq (𝓕 := ℱ₊) t]
      exact MeasurableSpace.measurableSet_iInf.2 fun v ↦
        MeasurableSpace.measurableSet_iInf.2 fun hv ↦ by
          rcases hu_cofinal hv with ⟨n, hn⟩
          exact (ℱ₊.mono hn) _ (hU_future n)
    have hrc : (ℱ₊₊ : Filtration NNReal mΩ) = ℱ₊ := by
      simpa using (Filtration.rightCont_self (𝓕 := ℱ))
    have hspace : ((ℱ₊₊ : Filtration NNReal mΩ) t) = ℱ₊ t := by
      simpa using congrArg (fun 𝓖 : Filtration NNReal mΩ ↦ 𝓖 t) hrc
    exact hspace ▸ hU_plus
  exact ⟨U, hU_meas, hU_ae.symm⟩

/- The completed right-continuous filtration `ℱ^+*[μ]` satisfies the chapter owner property
`UsualConditions` for the completed measure `μ.completion`. -/
-- Proof sketch: right continuity comes from the defining use of `ℱ.rightCont`, and completeness at
-- time `0` is built into the passage from `μ` to `μ.completion`.
theorem completed_right_continuous_filtration_usual_conditions
    (μ : Measure Ω) (ℱ : Filtration NNReal mΩ) :
    UsualConditions (ℱ^+*[μ]) μ.completion := by
  refine
    { toIsRightContinuous := ?_
      complete_timeZero := ?_ }
  · refine Filtration.IsRightContinuous.mk ?_
    -- Right continuity reduces to collapsing future null-measurable representatives to time `t`.
    intro t s hs
    exact (measurableSet_completed_right_continuous_filtration_iff μ ℱ t (s := s)).2 <|
      completedRightContinuous_nullMeasurableSet_of_forall_gt μ ℱ <|
        (completedRightContinuous_rightCont_measurableSet_iff μ ℱ).1 hs
  · intro s hs
    -- Time-zero completeness is immediate because `μ.completion` and `μ` have the same values on
    -- all sets, so the null witness `∅` already shows measurability in the completed stage.
    rw [Measure.completion_apply] at hs
    change ∃ U : Set Ω, MeasurableSet[ℱ₊ 0] U ∧ s =ᵐ[μ] U
    exact ⟨∅,
      (show @MeasurableSet Ω (ℱ₊ 0) (∅ : Set Ω) from @MeasurableSet.empty Ω (ℱ₊ 0)),
      ae_eq_empty.2 hs⟩

end Filtration

open ProbabilityTheory

/-- Helper for Exercise 21.4.5: a set measurable for the right-limit stage `ℱ₊ s` is measurable
for every strictly later stage `ℱ u`. -/
private theorem measurableSet_rightCont_of_lt
    {ℱ : Filtration NNReal mΩ} {s u : NNReal} {A : Set Ω}
    (hA : MeasurableSet[(Filtration.rightCont ℱ) s] A) (hsu : s < u) :
    MeasurableSet[ℱ u] A := by
  -- Unpack `ℱ₊ s` as the infimum of all future stages and read off the `u`-component.
  rw [Filtration.rightCont_eq (𝓕 := ℱ) s] at hA
  exact MeasurableSpace.measurableSet_iInf.1 (MeasurableSpace.measurableSet_iInf.1 hA u) hsu

/-- Helper for Exercise 21.4.5: for real-valued `L²` functions, the `eLpNorm` at exponent `2`
is the square root of the second moment. -/
private theorem eLpNormTwo_eq_ofReal_sqrt_integral_sq
    {μ : Measure Ω} {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (∫ ω, f ω ^ 2 ∂μ)) := by
  -- Pass from `eLpNorm` to `lpNorm`, then invoke the Chapter 7 `p = 2` identity.
  calc
    eLpNorm f 2 μ = ENNReal.ofReal (lpNorm f 2 μ) := by
      rw [← ENNReal.ofReal_toReal hf.eLpNorm_ne_top, toReal_eLpNorm hf.aestronglyMeasurable]
    _ = ENNReal.ofReal (Real.sqrt (∫ ω, f ω ^ 2 ∂μ)) := by
      rw [lpNorm_two_eq_sqrt_integral_sq hf]

/-- Helper for Exercise 21.4.5: a Brownian increment has `L¹` norm at most the square root of
its time lag. -/
private theorem brownianIncrement_integral_abs_le_sqrt_timeLag
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) {s t : NNReal}
    (hst : s ≤ t) :
    ∫ ω, |B t ω - B s ω| ∂μ ≤ Real.sqrt (((t - s : NNReal) : ℝ)) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  have hInc_mem : MemLp (fun ω ↦ B t ω - B s ω) 2 μ :=
    ProbabilityTheory.brownianIncrement_memLp_two hB hst
  have hInc_int : Integrable (fun ω ↦ B t ω - B s ω) μ :=
    hInc_mem.integrable (by norm_num)
  have hLpOne :
      ENNReal.ofReal (∫ ω, |B t ω - B s ω| ∂μ) =
        eLpNorm (fun ω ↦ B t ω - B s ω) 1 μ := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hInc_int]
    simp [Real.norm_eq_abs]
  have hLpCompare :
      eLpNorm (fun ω ↦ B t ω - B s ω) 1 μ ≤
        eLpNorm (fun ω ↦ B t ω - B s ω) 2 μ :=
    eLpNorm_le_eLpNorm_of_exponent_le (show (1 : ENNReal) ≤ 2 by norm_num)
      hInc_int.aestronglyMeasurable
  have hLpTwo :
      eLpNorm (fun ω ↦ B t ω - B s ω) 2 μ =
        ENNReal.ofReal (Real.sqrt (((t - s : NNReal) : ℝ))) := by
    calc
      eLpNorm (fun ω ↦ B t ω - B s ω) 2 μ
          = ENNReal.ofReal (Real.sqrt (∫ ω, (B t ω - B s ω) ^ 2 ∂μ)) := by
              rw [eLpNormTwo_eq_ofReal_sqrt_integral_sq hInc_mem]
      _ = ENNReal.ofReal (Real.sqrt (((t - s : NNReal) : ℝ))) := by
            rw [ProbabilityTheory.brownianIncrement_sq_integral_eq_timeLag hB hst]
  have hBoundENN :
      ENNReal.ofReal (∫ ω, |B t ω - B s ω| ∂μ) ≤
        ENNReal.ofReal (Real.sqrt (((t - s : NNReal) : ℝ))) := by
    rw [hLpOne]
    exact hLpCompare.trans_eq hLpTwo
  exact (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).mp hBoundENN

/-- Helper for Exercise 21.4.5: the right-limit approximation
`u n = s + (t - s) / (n + 1)` stays inside `(s, t]`, and its gap from `s` is explicit. -/
private theorem rightLimitApproxSpec
    {s t : NNReal} (hst : s < t) :
    let u : ℕ → NNReal := fun n ↦ s + (t - s) / (n + 1)
    (∀ n, s < u n) ∧
      (∀ n, u n ≤ t) ∧
      (∀ n, ((u n - s : NNReal) : ℝ) = ((t - s : NNReal) : ℝ) / (n + 1)) := by
  let u : ℕ → NNReal := fun n ↦ s + (t - s) / (n + 1)
  refine ⟨?_, ?_, ?_⟩
  · intro n
    -- The correction term is positive because `t - s > 0`.
    have hpos : 0 < (t - s : NNReal) / (n + 1) := by
      exact div_pos (tsub_pos_of_lt hst) (by positivity)
    simpa [u] using lt_add_of_pos_right s hpos
  · intro n
    -- Dividing the gap `t - s` by `n + 1 ≥ 1` keeps the approximation below `t`.
    have hdiv :
        (t - s : NNReal) / (n + 1) ≤ t - s := by
      exact div_le_self (show 0 ≤ (t - s : NNReal) by positivity) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
    calc
      u n = s + (t - s) / (n + 1) := rfl
      _ ≤ s + (t - s) := by
            simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hdiv s
      _ = t := by rw [add_tsub_cancel_of_le hst.le]
  · intro n
    -- The subtraction cancels the added offset, leaving the explicit right-gap.
    simpa [u, add_tsub_cancel_left]

/-- Helper for Exercise 21.4.5: the square-root time gap of the standard right-limit
approximation tends to `0`. -/
private theorem rightLimitApproxSqrtGap_tendsto_zero
    {s t : NNReal} (hst : s < t) :
    let u : ℕ → NNReal := fun n ↦ s + (t - s) / (n + 1)
    Filter.Tendsto (fun n ↦ Real.sqrt (((u n - s : NNReal) : ℝ))) Filter.atTop (nhds 0) := by
  let u : ℕ → NNReal := fun n ↦ s + (t - s) / (n + 1)
  rcases rightLimitApproxSpec (s := s) (t := t) hst with ⟨_, _, hgap⟩
  have hdiv :
      Filter.Tendsto (fun n : ℕ ↦ ((t - s : NNReal) : ℝ) / (n + 1)) Filter.atTop (nhds 0) := by
    -- Proof comment: the explicit right-gap is a constant multiple of the standard
    -- `1 / (n + 1) → 0` sequence.
    simpa [div_eq_mul_inv, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat : Filter.Tendsto
        (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) Filter.atTop (nhds 0)).const_mul
        (((t - s : NNReal) : ℝ))
  -- Proof comment: rewrite the gap by the explicit formula and use continuity of `Real.sqrt`.
  simpa [u, hgap, Real.sqrt_zero] using Filter.Tendsto.sqrt hdiv

/-- Helper for Exercise 21.4.5: every set measurable for the original measurable space remains
measurable in the ambient `μ`-completion. -/
private theorem measurableSpace_le_ambientCompleted
    (μ : Measure Ω) :
    mΩ ≤ Filtration.ambientCompletedMeasurableSpace μ := by
  intro s hs
  exact ⟨s, hs, Filter.EventuallyEq.rfl⟩

/-- Helper for Exercise 21.4.5: trimming `μ.completion` back to the original measurable space
recovers the original measure `μ`. -/
private theorem completion_trim_eq
    (μ : Measure Ω) :
    μ.completion.trim (measurableSpace_le_ambientCompleted (Ω := Ω) (mΩ := mΩ) μ) = μ := by
  refine @Measure.ext Ω mΩ _ _ (fun s hs ↦ ?_)
  -- Proof comment: both measures agree on every ambient measurable set, which determines the
  -- trimmed measure uniquely.
  calc
    (μ.completion.trim (measurableSpace_le_ambientCompleted (Ω := Ω) (mΩ := mΩ) μ)) s
        = μ.completion s := by
            exact @trim_measurableSet_eq Ω mΩ (Filtration.ambientCompletedMeasurableSpace μ)
              (μ.completion) _
              (measurableSpace_le_ambientCompleted (Ω := Ω) (mΩ := mΩ) μ) hs
    _ = μ s := by rw [Measure.completion_apply]

/-- Helper for Exercise 21.4.5: strong adaptedness along `ℱ` lifts to the completed
right-continuous filtration because each `ℱ t` sits inside `(ℱ^+*[μ]) t`. -/
private theorem stronglyAdapted_completed_right_continuous_filtration
    {β : Type*} [TopologicalSpace β]
    {μ : Measure Ω} {ℱ : Filtration NNReal mΩ} {X : NNReal → Ω → β}
    (hX : StronglyAdapted ℱ X) :
    StronglyAdapted (ℱ^+*[μ]) X := by
  intro t
  -- First pass from `ℱ t` to the right-limit stage `ℱ₊ t`, then complete with respect to `μ`.
  refine (hX t).mono <| (Filtration.le_rightCont ℱ t).trans ?_
  intro s hs
  exact ⟨s, hs, Filter.EventuallyEq.rfl⟩

/-- Helper for Exercise 21.4.5: integrability on `μ` transports to `μ.completion` because the
completion trim is exactly `μ`. -/
private theorem integrable_completion_of_stronglyMeasurable
    {μ : Measure Ω} {f : Ω → ℝ} (hf_int : Integrable f μ) :
    Integrable f μ.completion := by
  have htrim :
      Integrable f
        (μ.completion.trim (measurableSpace_le_ambientCompleted (Ω := Ω) (mΩ := mΩ) μ)) := by
    -- Proof comment: first rewrite the trimmed completion measure back to the original measure.
    simpa [completion_trim_eq (Ω := Ω) (mΩ := mΩ) μ] using hf_int
  -- Proof comment: integrability on the trimmed completion upgrades to the full completion.
  exact integrable_of_integrable_trim
    (measurableSpace_le_ambientCompleted (Ω := Ω) (mΩ := mΩ) μ) htrim

/-- Helper for Exercise 21.4.5: on ambient measurable sets, set integrals against `μ.completion`
and `μ` agree. -/
private theorem setIntegral_completion_eq_setIntegral_of_measurable
    {μ : Measure Ω} {f : Ω → ℝ} (hf_meas : StronglyMeasurable f) {U : Set Ω}
    (hU : MeasurableSet U) :
    (∫ ω : Ω in U, f ω ∂μ.completion) = ∫ ω in U, f ω ∂μ := by
  -- Proof comment: `setIntegral_trim` is the canonical completion bridge once the measurable set
  -- is expressed in the ambient measurable space.
  calc
    ∫ ω : Ω in U, f ω ∂μ.completion
        = ∫ ω : Ω in U, f ω
            ∂μ.completion.trim (measurableSpace_le_ambientCompleted (Ω := Ω) (mΩ := mΩ) μ) := by
            exact setIntegral_trim
              (measurableSpace_le_ambientCompleted (Ω := Ω) (mΩ := mΩ) μ) hf_meas hU
    _ = ∫ ω in U, f ω ∂μ := by
          rw [completion_trim_eq (Ω := Ω) (mΩ := mΩ) μ]
          rfl

/-- Helper for Exercise 21.4.5: a Brownian martingale remains a martingale for the right-limit
filtration `ℱ₊`. -/
private theorem martingale_rightLimit_of_continuous_paths
    {μ : Measure Ω} {ℱ : Filtration NNReal mΩ} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) (hBm : Martingale B ℱ μ) :
    Martingale B (Filtration.rightCont ℱ) μ := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  refine ⟨?_, ?_⟩
  · intro t
    -- Proof comment: adaptedness only enlarges when we pass from `ℱ t` to the right-limit stage.
    exact (hBm.stronglyAdapted t).mono (Filtration.le_rightCont ℱ t)
  · intro s t hst
    refine
      (ae_eq_condExp_of_forall_setIntegral_eq ((Filtration.rightCont ℱ).le s) (hBm.integrable t)
        (fun A hA _ ↦ (hBm.integrable s).integrableOn)
        (fun A hA _ ↦ ?_) ((hBm.stronglyAdapted s).mono (Filtration.le_rightCont ℱ s)).aestronglyMeasurable
      ).symm
    by_cases hst_eq : s = t
    · subst hst_eq
      simp
    · have hst_lt : s < t := lt_of_le_of_ne hst hst_eq
      let u : ℕ → NNReal := fun n ↦ s + (t - s) / (n + 1)
      rcases rightLimitApproxSpec (s := s) (t := t) hst_lt with ⟨hu_gt, hu_le, _⟩
      have hu_tendsto :
          Filter.Tendsto
            (fun n ↦ Real.sqrt (((u n - s : NNReal) : ℝ))) Filter.atTop (nhds 0) := by
        simpa [u] using rightLimitApproxSqrtGap_tendsto_zero (s := s) (t := t) hst_lt
      have hset_eq :
          ∀ n, ∫ ω in A, B t ω ∂μ = ∫ ω in A, B (u n) ω ∂μ := by
        intro n
        symm
        exact hBm.setIntegral_eq (hu_le n) (measurableSet_rightCont_of_lt hA (hu_gt n))
      have hsub_eq :
          ∀ n,
            (∫ ω in A, B (u n) ω ∂μ) - ∫ ω in A, B s ω ∂μ =
              ∫ ω in A, (B (u n) ω - B s ω) ∂μ := by
        intro n
        exact
          (integral_sub' ((hBm.integrable (u n)).integrableOn) ((hBm.integrable s).integrableOn)).symm
      have habs_bound :
          ∀ n,
            |(∫ ω in A, B (u n) ω ∂μ) - ∫ ω in A, B s ω ∂μ| ≤
              Real.sqrt (((u n - s : NNReal) : ℝ)) := by
        intro n
        have hinc_int : Integrable (fun ω ↦ B (u n) ω - B s ω) μ :=
          (hBm.integrable (u n)).sub (hBm.integrable s)
        have hset_abs_le :
            ∫ ω in A, |B (u n) ω - B s ω| ∂μ ≤
              ∫ ω, |B (u n) ω - B s ω| ∂μ := by
          exact integral_mono_measure Measure.restrict_le_self
            (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _) hinc_int.norm
        calc
          |(∫ ω in A, B (u n) ω ∂μ) - ∫ ω in A, B s ω ∂μ|
              = |∫ ω in A, (B (u n) ω - B s ω) ∂μ| := by rw [hsub_eq n]
          _ ≤ ∫ ω in A, |B (u n) ω - B s ω| ∂μ := by
                simpa [Real.norm_eq_abs] using
                  (norm_integral_le_integral_norm
                    (μ := μ.restrict A) (f := fun ω ↦ B (u n) ω - B s ω))
          _ ≤ ∫ ω, |B (u n) ω - B s ω| ∂μ := hset_abs_le
          _ ≤ Real.sqrt (((u n - s : NNReal) : ℝ)) := by
                exact brownianIncrement_integral_abs_le_sqrt_timeLag hB (show s ≤ u n from (hu_gt n).le)
      have habs_tendsto :
          Filter.Tendsto
            (fun n ↦ |(∫ ω in A, B (u n) ω ∂μ) - ∫ ω in A, B s ω ∂μ|)
            Filter.atTop (nhds 0) := by
        refine squeeze_zero (fun n ↦ abs_nonneg _) habs_bound hu_tendsto
      have hdiff_tendsto :
          Filter.Tendsto
            (fun n ↦ (∫ ω in A, B (u n) ω ∂μ) - ∫ ω in A, B s ω ∂μ)
            Filter.atTop (nhds 0) := by
        rw [tendsto_zero_iff_abs_tendsto_zero]
        exact habs_tendsto
      have hu_integral_tendsto :
          Filter.Tendsto (fun n ↦ ∫ ω in A, B (u n) ω ∂μ) Filter.atTop
            (nhds (∫ ω in A, B s ω ∂μ)) := by
        -- Proof comment: the increment estimates show the future-time integrals converge back to
        -- the time-`s` integral.
        have h := hdiff_tendsto.const_add (∫ ω in A, B s ω ∂μ)
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
      have ht_integral_tendsto :
          Filter.Tendsto (fun _ : ℕ ↦ ∫ ω in A, B t ω ∂μ) Filter.atTop
            (nhds (∫ ω in A, B s ω ∂μ)) := by
        have hconst :
            (fun n ↦ ∫ ω in A, B (u n) ω ∂μ) = fun _ : ℕ ↦ ∫ ω in A, B t ω ∂μ := by
          funext n
          exact (hset_eq n).symm
        rw [hconst] at hu_integral_tendsto
        exact hu_integral_tendsto
      simpa using tendsto_nhds_unique ht_integral_tendsto tendsto_const_nhds

-- Proof sketch: for `s ≤ t`, the martingale identity `E[B_t | ℱ_u] = B_u` holds for every
-- `u ∈ Ioi s`. Passing to the right-limit `ℱ_s⁺ = ⋂ u > s, ℱ_u` identifies the conditional
-- expectation of `B_t` with the almost sure limit of `B_u` as `u ↓ s`, and almost sure continuity
-- of Brownian paths turns that limit into `B_s`. Completing `ℱ_s⁺` with respect to `μ` does not
-- change conditional expectations after passing to `μ.completion`.
/-- Exercise 21.4.5: if a Brownian motion is a martingale for `ℱ`, then it is also a martingale
for the completed right-continuous filtration `ℱ^+*[μ]`, formalizing the textbook augmentation
`ℱ^{+,*}`. The filtration-side owner theorem is
`Filtration.completed_right_continuous_filtration_usual_conditions`; this is the Brownian-motion
corollary justified by the exercise. -/
theorem brownian_martingale_completed_right_continuous_filtration
    {μ : Measure Ω} {ℱ : Filtration NNReal mΩ} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) (hBm : Martingale B ℱ μ) :
    Martingale B (ℱ^+*[μ]) μ.completion := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  letI : IsProbabilityMeasure μ.completion := by
    refine ⟨?_⟩
    change μ Set.univ = 1
    exact measure_univ
  have hRight : Martingale B (Filtration.rightCont ℱ) μ :=
    martingale_rightLimit_of_continuous_paths hB hBm
  refine ⟨stronglyAdapted_completed_right_continuous_filtration hBm.stronglyAdapted, ?_⟩
  intro s t hst
  refine
    (ae_eq_condExp_of_forall_setIntegral_eq ((ℱ^+*[μ]).le s)
      (by
        simpa using
          (integrable_completion_of_stronglyMeasurable (μ := μ) (f := B t) (hBm.integrable t) :
            Integrable (B t) μ.completion))
      (fun A hA _ ↦ by
        simpa using
          (((integrable_completion_of_stronglyMeasurable (μ := μ) (f := B s) (hBm.integrable s)) :
            Integrable (B s) μ.completion).integrableOn : IntegrableOn (B s) A μ.completion))
      (fun A hA _ ↦ ?_)
      ((stronglyAdapted_completed_right_continuous_filtration hBm.stronglyAdapted s).aestronglyMeasurable)
    ).symm
  rcases (Filtration.measurableSet_completed_right_continuous_filtration_iff μ ℱ s (s := A)).1 hA with
    ⟨U, hU, hAU⟩
  have hU_ambient : MeasurableSet U := (Filtration.rightCont ℱ).le s U hU
  have hAU_completion : A =ᵐ[μ.completion] U := by
    simpa [Measure.ae_completion μ] using hAU
  have hBs_meas : StronglyMeasurable (B s) := by
    exact (hBm.stronglyAdapted s).mono (ℱ.le s)
  have hBt_meas : StronglyMeasurable (B t) := by
    exact (hBm.stronglyAdapted t).mono (ℱ.le t)
  calc
    ∫ ω in A, B s ω ∂μ.completion = ∫ ω in U, B s ω ∂μ.completion := by
      exact setIntegral_congr_set hAU_completion
    _ = ∫ ω in U, B s ω ∂μ := by
      exact setIntegral_completion_eq_setIntegral_of_measurable hBs_meas hU_ambient
    _ = ∫ ω in U, B t ω ∂μ := by
      exact hRight.setIntegral_eq hst hU
    _ = ∫ ω in U, B t ω ∂μ.completion := by
      symm
      exact setIntegral_completion_eq_setIntegral_of_measurable hBt_meas hU_ambient
    _ = ∫ ω in A, B t ω ∂μ.completion := by
      exact setIntegral_congr_set hAU_completion.symm

end MeasureTheory

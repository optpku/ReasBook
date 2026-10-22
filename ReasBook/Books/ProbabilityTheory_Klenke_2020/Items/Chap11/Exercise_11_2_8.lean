/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Filtration
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/- This item is `source-facing`: it describes a `{0,1}`-valued real process together with its
one-step conditional law. The public owner abstraction is therefore the transition-law
predicate `exercise1128Transition`, which packages both the binary state-space restriction and the
displayed conditional law along the natural filtration. The ambient-`ℝ` two-point row kernel below
is auxiliary support code for that statement, so it stays private. -/

private theorem exercise1128RowKernel_measurable (p : ℝ) :
    Measurable
      (fun x : ℝ ↦
        (ENNReal.ofReal x • Measure.dirac (1 - p + p * x) +
          ENNReal.ofReal (1 - x) • Measure.dirac (p * x) : Measure ℝ)) := by
  have h_left : Measurable (fun x : ℝ ↦ 1 - p + p * x) := by
    fun_prop
  have h_right : Measurable (fun x : ℝ ↦ p * x) := by
    fun_prop
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  simp only [Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ hs]
  refine Measurable.add ?_ ?_
  · refine measurable_id.ennreal_ofReal.mul ?_
    exact (measurable_const.indicator hs).comp h_left
  · refine (measurable_const.sub measurable_id).ennreal_ofReal.mul ?_
    exact (measurable_const.indicator hs).comp h_right

private def exercise1128RowKernel (p : ℝ) : Kernel ℝ ℝ where
  toFun x :=
    ENNReal.ofReal x • Measure.dirac (1 - p + p * x) +
      ENNReal.ofReal (1 - x) • Measure.dirac (p * x)
  measurable' := exercise1128RowKernel_measurable p

/-- The source-facing transition law for this item: with respect to the natural filtration of `X`,
the process is `{0,1}`-valued and the conditional law of `X_{n+1}` is the canonical
two-point law determined by `X_n` and `p`. -/
def exercise1128Transition (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ) (X : ℕ → Ω → ℝ) (hX_meas : ∀ n, Measurable (X n)) : Prop :=
  let ℱ := Filtration.natural X fun n ↦ (hX_meas n).stronglyMeasurable
  (∀ n ω, X n ω ∈ ({0, 1} : Set ℝ)) ∧
    ∀ n ⦃s : Set ℝ⦄, MeasurableSet s →
      μ⟦X (n + 1) ⁻¹' s | ℱ n⟧ =ᵐ[μ] fun ω ↦ (exercise1128RowKernel p (X n ω)).real s

/-- A process satisfying `exercise1128Transition` is `{0,1}`-valued at every time. -/
theorem exercise1128Transition_binary {p : ℝ} {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ n, Measurable (X n))
    (hX_transition : exercise1128Transition μ p X hX_meas) :
    ∀ n ω, X n ω ∈ ({0, 1} : Set ℝ) :=
  hX_transition.1

private theorem exercise1128Transition_conditionalLaw {p : ℝ} {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ n, Measurable (X n))
    (hX_transition : exercise1128Transition μ p X hX_meas) :
    let ℱ := Filtration.natural X fun n ↦ (hX_meas n).stronglyMeasurable
    ∀ n ⦃s : Set ℝ⦄, MeasurableSet s →
      μ⟦X (n + 1) ⁻¹' s | ℱ n⟧ =ᵐ[μ] fun ω ↦ (exercise1128RowKernel p (X n ω)).real s :=
  hX_transition.2

-- Proof sketch: if `x ∈ {0, 1}`, exactly one of the two weights in `exercise1128RowKernel p x`
-- is `1` and the other is `0`, so the two-point law reduces to the Dirac mass at `x`.
private theorem exercise1128RowKernel_eq_dirac_of_mem_zero_one {p x : ℝ}
    (hx : x ∈ ({0, 1} : Set ℝ)) :
    exercise1128RowKernel p x = Measure.dirac x := by
  -- Split the binary state into the two allowed values and simplify the kernel weights.
  rcases by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hx with rfl | rfl
  · ext s hs
    simp [exercise1128RowKernel, hs]
  · ext s hs
    simp [exercise1128RowKernel, hs]

/-- Helper for this item: a real number in `{0, 1}` has absolute value at most `1`. -/
private theorem abs_le_one_of_mem_zero_one {x : ℝ} (hx : x ∈ ({0, 1} : Set ℝ)) :
    |x| ≤ 1 := by
  -- The binary state space leaves only the two trivial absolute values.
  rcases by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hx with rfl | rfl <;> norm_num

-- Proof sketch: under the conditional-law hypothesis, the one-step conditional law of
-- `X_{n + 1}` is `exercise1128RowKernel p (X n ω)` along the natural filtration. The binary part
-- of `exercise1128Transition` identifies this with `Measure.dirac (X n ω)` via
-- `exercise1128RowKernel_eq_dirac_of_mem_zero_one`,
-- `Measure.dirac (X n ω)`, so `X_{n + 1}` and `X_n` agree almost surely.
/-- For a process satisfying the source-facing transition law of this item, consecutive time slices
coincide almost everywhere. -/
theorem exercise1128_succ_ae_eq_self {p : ℝ} {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ n, Measurable (X n))
    (hX_transition : exercise1128Transition μ p X hX_meas) (n : ℕ) :
    X (n + 1) =ᵐ[μ] X n := by
  let ℱ : Filtration ℕ ‹MeasurableSpace Ω› :=
    Filtration.natural X fun k ↦ (hX_meas k).stronglyMeasurable
  let A0 : Set Ω := (X n) ⁻¹' ({0} : Set ℝ)
  let A1 : Set Ω := (X n) ⁻¹' ({1} : Set ℝ)
  let B0 : Set Ω := (X (n + 1)) ⁻¹' ({0} : Set ℝ)
  let B1 : Set Ω := (X (n + 1)) ⁻¹' ({1} : Set ℝ)
  let M01 : Set Ω := A0 ∩ B1
  let M10 : Set Ω := A1 ∩ B0
  let hℱ_strong :
      StronglyAdapted ℱ X := Filtration.stronglyAdapted_natural
        (fun k ↦ (hX_meas k).stronglyMeasurable)
  let hℱ_adapted : Adapted ℱ X := hℱ_strong.adapted
  have hA0_meas : MeasurableSet A0 := by
    simpa [A0] using (hX_meas n) (measurableSet_singleton (0 : ℝ))
  have hA1_meas : MeasurableSet A1 := by
    simpa [A1] using (hX_meas n) (measurableSet_singleton (1 : ℝ))
  have hB0_meas : MeasurableSet B0 := by
    simpa [B0] using (hX_meas (n + 1)) (measurableSet_singleton (0 : ℝ))
  have hB1_meas : MeasurableSet B1 := by
    simpa [B1] using (hX_meas (n + 1)) (measurableSet_singleton (1 : ℝ))
  have hA0_meas_ℱ : MeasurableSet[ℱ n] A0 := by
    simpa [A0] using (hℱ_adapted n) (measurableSet_singleton (0 : ℝ))
  have hA1_meas_ℱ : MeasurableSet[ℱ n] A1 := by
    simpa [A1] using (hℱ_adapted n) (measurableSet_singleton (1 : ℝ))
  have hB1_ind_integrable : Integrable (Set.indicator B1 fun _ ↦ (1 : ℝ)) μ := by
    exact (integrable_const (1 : ℝ)).indicator hB1_meas
  have hB0_ind_integrable : Integrable (Set.indicator B0 fun _ ↦ (1 : ℝ)) μ := by
    exact (integrable_const (1 : ℝ)).indicator hB0_meas
  have hcondLaw := exercise1128Transition_conditionalLaw hX_meas hX_transition
  have hM01_real_zero : μ.real M01 = 0 := by
    -- On `{X n = 0}`, the next-step kernel assigns zero mass to `{1}`.
    calc
      μ.real M01 = ∫ ω in A0, (μ⟦B1 | ℱ n⟧) ω ∂μ := by
        rw [setIntegral_condExp (ℱ.le n) hB1_ind_integrable hA0_meas_ℱ]
        rw [← integral_indicator hA0_meas]
        symm
        simpa [M01, A0, B1, Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm,
          Set.inter_comm, smul_eq_mul] using
          integral_indicator_const (1 : ℝ) (hA0_meas.inter hB1_meas)
      _ =
          ∫ ω in A0, (exercise1128RowKernel p (X n ω)).real ({1} : Set ℝ) ∂μ := by
            exact integral_congr_ae
              ((hcondLaw n (s := ({1} : Set ℝ)) (measurableSet_singleton (1 : ℝ))).restrict)
      _ = ∫ ω in A0, (0 : ℝ) ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [self_mem_ae_restrict (μ := μ) (s := A0) hA0_meas] with ω hω
            have hXn0 : X n ω = 0 := by
              simpa [A0] using hω
            rw [hXn0, exercise1128RowKernel_eq_dirac_of_mem_zero_one (by simp)]
            simp [MeasureTheory.measureReal_def]
      _ = 0 := by simp
  have hM10_real_zero : μ.real M10 = 0 := by
    -- On `{X n = 1}`, the next-step kernel assigns zero mass to `{0}`.
    calc
      μ.real M10 = ∫ ω in A1, (μ⟦B0 | ℱ n⟧) ω ∂μ := by
        rw [setIntegral_condExp (ℱ.le n) hB0_ind_integrable hA1_meas_ℱ]
        rw [← integral_indicator hA1_meas]
        symm
        simpa [M10, A1, B0, Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm,
          Set.inter_comm, smul_eq_mul] using
          integral_indicator_const (1 : ℝ) (hA1_meas.inter hB0_meas)
      _ =
          ∫ ω in A1, (exercise1128RowKernel p (X n ω)).real ({0} : Set ℝ) ∂μ := by
            exact integral_congr_ae
              ((hcondLaw n (s := ({0} : Set ℝ)) (measurableSet_singleton (0 : ℝ))).restrict)
      _ = ∫ ω in A1, (0 : ℝ) ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [self_mem_ae_restrict (μ := μ) (s := A1) hA1_meas] with ω hω
            have hXn1 : X n ω = 1 := by
              simpa [A1] using hω
            rw [hXn1, exercise1128RowKernel_eq_dirac_of_mem_zero_one (by simp)]
            simp [MeasureTheory.measureReal_def]
      _ = 0 := by simp
  have hM01_zero : μ M01 = 0 := (measureReal_eq_zero_iff (μ := μ)).1 hM01_real_zero
  have hM10_zero : μ M10 = 0 := (measureReal_eq_zero_iff (μ := μ)).1 hM10_real_zero
  have hMismatch_meas : MeasurableSet (M01 ∪ M10) :=
    (hA0_meas.inter hB1_meas).union (hA1_meas.inter hB0_meas)
  have hMismatch_ae : ∀ᵐ ω ∂μ, ω ∉ M01 ∪ M10 := by
    rw [ae_iff]
    have hMismatch_badSet : {a | ¬ a ∉ M01 ∪ M10} = M01 ∪ M10 := by
      ext a
      by_cases hM01 : a ∈ M01
      · simp [hM01]
      · simp [hM01]
    rw [hMismatch_badSet]
    exact measure_union_null hM01_zero hM10_zero
  -- Outside the two mismatch events, the binary values can only agree.
  filter_upwards [hMismatch_ae] with ω hω
  have hXn : X n ω ∈ ({0, 1} : Set ℝ) := exercise1128Transition_binary hX_meas hX_transition n ω
  have hXsucc : X (n + 1) ω ∈ ({0, 1} : Set ℝ) :=
    exercise1128Transition_binary hX_meas hX_transition (n + 1) ω
  rcases by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hXn with hXn0 | hXn1
  · rcases by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hXsucc with hXsucc0 | hXsucc1
    · simpa [hXn0] using hXsucc0
    · exfalso
      exact hω (Or.inl (by simp [M01, A0, B1, hXn0, hXsucc1]))
  · rcases by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hXsucc with hXsucc0 | hXsucc1
    · exfalso
      exact hω (Or.inr (by simp [M10, A1, B0, hXn1, hXsucc0]))
    · simpa [hXn1] using hXsucc1

-- Proof sketch: iterate the one-step almost-everywhere identity from the previous lemma and use
-- transitivity of `=ᵐ[μ]` to show inductively that every time slice agrees almost everywhere with
-- the initial value.
/-- A process satisfying this item's transition law is constant in time up to almost-everywhere
equality, with time slices equal almost everywhere to the initial state. -/
theorem exercise1128_ae_eq_initial {p : ℝ} {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ n, Measurable (X n))
    (hX_transition : exercise1128Transition μ p X hX_meas) (n : ℕ) :
    X n =ᵐ[μ] X 0 := by
  -- Propagate the one-step almost-sure constancy from time `0` to time `n`.
  induction n with
  | zero =>
      exact Filter.EventuallyEq.rfl
  | succ k hk =>
      exact (exercise1128_succ_ae_eq_self hX_meas hX_transition k).trans hk

-- Proof sketch: `exercise1128_succ_ae_eq_self` gives the one-step almost-everywhere identity
-- needed by `MeasureTheory.martingale_nat` for the natural filtration; strong measurability comes
-- from `hX_meas`, and integrability follows from boundedness of the binary-valued process supplied
-- by `exercise1128Transition`.
/-- Part (1) of this item: a real-valued process satisfying the displayed binary transition law is
a martingale with respect to its natural filtration. -/
theorem binary_transition_process_martingale {p : ℝ}
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ n, Measurable (X n))
    (hX_transition : exercise1128Transition μ p X hX_meas) :
    Martingale X (Filtration.natural X fun n ↦ (hX_meas n).stronglyMeasurable) μ := by
  let ℱ : Filtration ℕ ‹MeasurableSpace Ω› :=
    Filtration.natural X fun n ↦ (hX_meas n).stronglyMeasurable
  have hbound : ∀ n, ∀ᵐ ω ∂μ, ‖X n ω‖ ≤ 1 := by
    intro n
    filter_upwards [Filter.Eventually.of_forall fun ω ↦
      exercise1128Transition_binary hX_meas hX_transition n ω] with ω hω
    simpa [Real.norm_eq_abs] using abs_le_one_of_mem_zero_one hω
  have hintegrable : ∀ n, Integrable (X n) μ := by
    intro n
    -- The binary state space gives a uniform `L¹` bound by the constant function `1`.
    refine Integrable.mono' (integrable_const (1 : ℝ)) (hX_meas n).aestronglyMeasurable (hbound n)
  have hstep :
      ∀ n, X n =ᵐ[μ] μ[X (n + 1) | ℱ n] := by
    intro n
    -- Replace `X (n + 1)` by `X n` almost surely, then collapse the conditional expectation.
    exact (Filter.EventuallyEq.of_eq
        (condExp_of_stronglyMeasurable (ℱ.le n) ((Filtration.stronglyAdapted_natural
          (fun k ↦ (hX_meas k).stronglyMeasurable)) n) (hintegrable n)).symm).trans
      ((condExp_congr_ae (exercise1128_succ_ae_eq_self hX_meas hX_transition n)).symm)
  exact martingale_nat
    (Filtration.stronglyAdapted_natural (fun n ↦ (hX_meas n).stronglyMeasurable))
    hintegrable hstep

-- Proof sketch: `exercise1128_ae_eq_initial` yields a countable family of almost-everywhere
-- equalities. Intersecting the corresponding full-measure sets gives a full-measure set on which
-- every time slice equals `X 0`, so the sample paths converge there to `X 0`.
/-- Part (2) of this item: under the same binary transition hypotheses, the process converges
almost surely, and its almost sure limit is the initial random variable `X 0`. -/
theorem binary_transition_process_ae_tendsto_initial {p : ℝ} {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ n, Measurable (X n))
    (hX_transition : exercise1128Transition μ p X hX_meas) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (X 0 ω)) := by
  have hconst : ∀ᵐ ω ∂μ, ∀ n, X n ω = X 0 ω := by
    rw [ae_all_iff]
    intro n
    exact exercise1128_ae_eq_initial hX_meas hX_transition n
  -- On the full-measure set where every time slice equals `X 0`, the path is constant.
  filter_upwards [hconst] with ω hω
  have hpath :
      (fun n ↦ X n ω) = fun _ : ℕ ↦ X 0 ω := by
    funext n
    exact hω n
  exact Filter.Tendsto.congr' (Filter.EventuallyEq.of_eq hpath.symm) tendsto_const_nhds

-- Proof sketch: combine `binary_transition_process_martingale` with the previous almost-sure
-- convergence statement to identify the natural-filtration limit process with `X 0` almost
-- everywhere, then use `HasLaw.congr`.
/-- Exercise 11.2.8: the canonical almost sure limit of the process has the same distribution as
the initial state `X 0`. -/
theorem binary_transition_process_limitProcess_hasLaw_initial {p : ℝ}
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ n, Measurable (X n))
    (hX_transition : exercise1128Transition μ p X hX_meas) :
    HasLaw
      ((Filtration.natural X fun n ↦ (hX_meas n).stronglyMeasurable).limitProcess X μ)
      (μ.map (X 0)) μ := by
  let ℱ : Filtration ℕ ‹MeasurableSpace Ω› :=
    Filtration.natural X fun n ↦ (hX_meas n).stronglyMeasurable
  have hlimitInitial :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (X 0 ω)) :=
    binary_transition_process_ae_tendsto_initial hX_meas hX_transition
  have hX0_strong :
      StronglyMeasurable[⨆ n, ℱ n] (X 0) := by
    exact
      ((Filtration.stronglyAdapted_natural
        (fun n ↦ (hX_meas n).stronglyMeasurable)) 0).mono
        (le_iSup ℱ 0)
  have hlimit_exists :
      ∃ g : Ω → ℝ,
        StronglyMeasurable[⨆ n, ℱ n] g ∧
          ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (g ω)) := by
    exact ⟨X 0, hX0_strong, hlimitInitial⟩
  have hlimit_eq : ℱ.limitProcess X μ =ᵐ[μ] X 0 := by
    -- `limitProcess` chooses an almost-sure limit when one exists,
    -- so compare that choice with `X 0`.
    rw [Filtration.limitProcess, dif_pos hlimit_exists]
    have hchoice_limit :
        ∀ᵐ ω ∂μ,
          Tendsto (fun n ↦ X n ω) atTop (𝓝 ((Classical.choose hlimit_exists) ω)) :=
      (Classical.choose_spec hlimit_exists).2
    filter_upwards [hchoice_limit, hlimitInitial] with ω hω_limit hω_initial
    exact tendsto_nhds_unique hω_limit hω_initial
  have hX0_law : HasLaw (X 0) (μ.map (X 0)) μ := by
    exact ⟨(hX_meas 0).aemeasurable, rfl⟩
  exact hX0_law.congr hlimit_eq

end ProbabilityTheory

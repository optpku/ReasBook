/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Theorem_20_14

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {τ : Ω → Ω}

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 20.23: if an event is fixed by the preimage under `τ`, then it is fixed by
every iterate of `τ`. -/
lemma preimageIterate_eq_self_of_preimage_eq_self {A : Set Ω} (hA : τ ⁻¹' A = A) :
    ∀ k : ℕ, (τ^[k]) ⁻¹' A = A := by
  intro k
  -- Proof comment: iterate the one-step fixed-point identity by the standard function-iterate API.
  exact Function.IsFixedPt.preimage_iterate hA k

/-- Helper for Theorem 20.23: the real Cesàro average of the correlations
`P (A ∩ (τ^[k]) ⁻¹' B)` is the integral of `1_A` against the Birkhoff average of `1_B`. -/
lemma correlationCesaroReal_eq_integral_indicatorMul_birkhoffAverage
    (hτ : MeasurePreserving τ P P) {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), P.real (A ∩ (τ^[k]) ⁻¹' B)) / (n + 1 : ℝ)) =
      ∫ ω, A.indicator (fun _ ↦ (1 : ℝ)) ω *
        birkhoffAverage ℝ τ (B.indicator (fun _ ↦ (1 : ℝ))) (n + 1) ω ∂P := by
  let g : Ω → ℝ := B.indicator (fun _ ↦ (1 : ℝ))
  have hProdEq :
      (fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω * birkhoffAverage ℝ τ g (n + 1) ω) =
        A.indicator (fun ω ↦ birkhoffAverage ℝ τ g (n + 1) ω) := by
    -- Proof comment: multiplying by `1_A` is the same as restricting the observable to `A`.
    funext ω
    simpa [g] using
      (Set.indicator_mul_left A (fun _ ↦ (1 : ℝ))
        (fun ω ↦ birkhoffAverage ℝ τ g (n + 1) ω) (i := ω)).symm
  have hTermIntegrable :
      ∀ k ∈ Finset.range (n + 1),
        Integrable (fun ω ↦ g ((τ^[k]) ω)) (P.restrict A) := by
    intro k hk
    -- Proof comment: each orbit term is again an indicator bounded by `1`, hence integrable on
    -- the restricted probability measure.
    simpa [g, Set.indicator_comp_right] using
      ((integrable_const (1 : ℝ)).indicator
        (((hτ.iterate k).measurable) hB) : Integrable (((τ^[k]) ⁻¹' B).indicator fun _ ↦ (1 : ℝ))
          (P.restrict A))
  have hTermIntegral :
      ∀ k ∈ Finset.range (n + 1),
        ∫ ω in A, g ((τ^[k]) ω) ∂P = P.real (A ∩ (τ^[k]) ⁻¹' B) := by
    intro k hk
    -- Proof comment: rewrite the restricted integral as the indicator of the intersection event
    -- and evaluate it with `integral_indicator_one`.
    calc
      ∫ ω in A, g ((τ^[k]) ω) ∂P
          = ∫ ω, A.indicator (fun ω ↦ g ((τ^[k]) ω)) ω ∂P := by
              rw [integral_indicator hA]
      _ = ∫ ω, (A ∩ (τ^[k]) ⁻¹' B).indicator (fun _ ↦ (1 : ℝ)) ω ∂P := by
            refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
            by_cases hωA : ω ∈ A
            · by_cases hωB : (τ^[k]) ω ∈ B
              · simp [g, hωA, hωB]
              · simp [g, hωA, hωB]
            · simp [g, hωA]
      _ = P.real (A ∩ (τ^[k]) ⁻¹' B) := by
            simpa using
              (integral_indicator_one (μ := P) (s := A ∩ (τ^[k]) ⁻¹' B)
                (hA.inter (((hτ.iterate k).measurable) hB)))
  have hIntegralEq :
      ∫ ω, A.indicator (fun _ ↦ (1 : ℝ)) ω * birkhoffAverage ℝ τ g (n + 1) ω ∂P
        = ((∑ k ∈ Finset.range (n + 1), P.real (A ∩ (τ^[k]) ⁻¹' B)) / (n + 1 : ℝ)) := by
    calc
    ∫ ω, A.indicator (fun _ ↦ (1 : ℝ)) ω * birkhoffAverage ℝ τ g (n + 1) ω ∂P
        = ∫ ω in A, birkhoffAverage ℝ τ g (n + 1) ω ∂P := by
            rw [hProdEq, integral_indicator hA]
    _ = ∫ ω in A, ((n + 1 : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1), g ((τ^[k]) ω)) ∂P := by
          simp [birkhoffAverage, birkhoffSum, g, smul_eq_mul]
    _ = (n + 1 : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1), ∫ ω in A, g ((τ^[k]) ω) ∂P := by
          rw [integral_const_mul, integral_finset_sum]
          intro k hk
          exact hTermIntegrable k hk
    _ = (n + 1 : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1), P.real (A ∩ (τ^[k]) ⁻¹' B) := by
          refine congrArg (fun t : ℝ ↦ (n + 1 : ℝ)⁻¹ * t) ?_
          exact Finset.sum_congr rfl fun k hk ↦ hTermIntegral k hk
    _ = ((∑ k ∈ Finset.range (n + 1), P.real (A ∩ (τ^[k]) ⁻¹' B)) / (n + 1 : ℝ)) := by
          rw [div_eq_inv_mul]
  exact hIntegralEq.symm

/-- Helper for Theorem 20.23: under ergodicity, the shifted Birkhoff averages of `1_B` converge
almost surely to `P.real B`. -/
lemma aeTendstoBirkhoffAverageIndicatorOfErgodic
    (hErg : Ergodic τ P) {B : Set Ω} (hB : MeasurableSet B) :
    ∀ᵐ ω ∂P,
      Tendsto
        (fun n : ℕ ↦ birkhoffAverage ℝ τ (B.indicator (fun _ ↦ (1 : ℝ))) (n + 1) ω)
        atTop
        (𝓝 (P.real B)) := by
  let g : Ω → ℝ := B.indicator (fun _ ↦ (1 : ℝ))
  have hgInt : Integrable g P := by
    -- Proof comment: the indicator of a measurable event is bounded by the integrable constant `1`.
    simpa [g] using ((integrable_const (1 : ℝ)).indicator hB : Integrable g P)
  have hAe :
      ∀ᵐ ω ∂P, Tendsto (birkhoffAverage ℝ τ g · ω) atTop (𝓝 (P[g])) :=
    birkhoffAverage_tendsto_ae_expectation_of_ergodic
      (P := P) (τ := τ) (f := g) hErg hgInt
  have hExp : P[g] = P.real B := by
    -- Proof comment: the expectation of the indicator is the real-valued measure of `B`.
    simpa [g] using (integral_indicator_one (μ := P) (s := B) hB)
  filter_upwards [hAe] with ω hω
  -- Proof comment: shift the Birkhoff averages from `n` to `n + 1`, then rewrite the limit.
  have hShift :
      Tendsto (fun n : ℕ ↦ birkhoffAverage ℝ τ g (n + 1) ω) atTop (𝓝 (P[g])) :=
    (tendsto_add_atTop_iff_nat 1).2 hω
  simpa [g, hExp] using hShift

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 20.23: every shifted Birkhoff average of the indicator `1_B` has norm at
most `1`. -/
lemma norm_birkhoffAverage_indicator_le_one {B : Set Ω} (n : ℕ) (ω : Ω) :
    ‖birkhoffAverage ℝ τ (B.indicator (fun _ ↦ (1 : ℝ))) (n + 1) ω‖ ≤ 1 := by
  let g : Ω → ℝ := B.indicator (fun _ ↦ (1 : ℝ))
  have hTerm_nonneg :
      ∀ k ∈ Finset.range (n + 1), 0 ≤ g ((τ^[k]) ω) := by
    intro k hk
    -- Proof comment: each orbit term of the indicator takes only the values `0` and `1`.
    by_cases hmem : (τ^[k]) ω ∈ B
    · simp [g, hmem]
    · simp [g, hmem]
  have hTerm_le_one :
      ∀ k ∈ Finset.range (n + 1), g ((τ^[k]) ω) ≤ 1 := by
    intro k hk
    -- Proof comment: the same dichotomy bounds every orbit term from above by `1`.
    by_cases hmem : (τ^[k]) ω ∈ B
    · simp [g, hmem]
    · simp [g, hmem]
  have hsum_nonneg :
      0 ≤ ∑ k ∈ Finset.range (n + 1), g ((τ^[k]) ω) := by
    exact Finset.sum_nonneg fun k hk ↦ hTerm_nonneg k hk
  have hsum_le :
      ∑ k ∈ Finset.range (n + 1), g ((τ^[k]) ω) ≤
        ∑ k ∈ Finset.range (n + 1), (1 : ℝ) := by
    exact Finset.sum_le_sum fun k hk ↦ hTerm_le_one k hk
  have hAvg_nonneg :
      0 ≤ (n + 1 : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1), g ((τ^[k]) ω) := by
    exact mul_nonneg (inv_nonneg.mpr <| by positivity) hsum_nonneg
  have hAvg_le_one :
      (n + 1 : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1), g ((τ^[k]) ω) ≤ 1 := by
    calc
      (n + 1 : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1), g ((τ^[k]) ω)
          ≤ (n + 1 : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1), (1 : ℝ) := by
              exact mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr <| by positivity)
      _ = (n + 1 : ℝ)⁻¹ * (n + 1) := by simp
      _ = 1 := by
            have hn_ne : ((n : ℝ) + 1) ≠ 0 := by positivity
            rw [inv_mul_cancel₀ hn_ne]
  -- Proof comment: the Birkhoff average is a nonnegative real, so its norm is just itself.
  calc
    ‖birkhoffAverage ℝ τ g (n + 1) ω‖
        = |(n + 1 : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1), g ((τ^[k]) ω)| := by
            simp [birkhoffAverage, birkhoffSum, g, Real.norm_eq_abs]
    _ = (n + 1 : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1), g ((τ^[k]) ω) := by
          exact abs_of_nonneg hAvg_nonneg
    _ ≤ 1 := hAvg_le_one

lemma tendsto_correlationCesaroReal_of_ergodic
    (hτ : MeasurePreserving τ P P) (hErg : Ergodic τ P) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto
      (fun n : ℕ ↦ ((∑ k ∈ Finset.range (n + 1), P.real (A ∩ (τ^[k]) ⁻¹' B)) / (n + 1 : ℝ)))
      atTop
      (𝓝 (P.real A * P.real B)) := by
  -- Route correction: replace the timeout-prone `L²` orthogonal-projection argument by the
  -- source proof using almost-sure Birkhoff convergence for the indicator of `B`.
  let g : Ω → ℝ := B.indicator (fun _ ↦ (1 : ℝ))
  let F : ℕ → Ω → ℝ := fun n ω ↦
    A.indicator (fun _ ↦ (1 : ℝ)) ω * birkhoffAverage ℝ τ g (n + 1) ω
  have hgMeas : Measurable g := by
    -- Proof comment: the indicator of a measurable event is measurable.
    simpa [g] using (measurable_const.indicator hB : Measurable g)
  have hIndicatorMeas : Measurable (A.indicator (fun _ ↦ (1 : ℝ))) := by
    -- Proof comment: the indicator `1_A` is measurable for the same reason.
    simpa using (measurable_const.indicator hA : Measurable (A.indicator fun _ ↦ (1 : ℝ)))
  have hAvgMeas :
      ∀ n : ℕ, Measurable (fun ω ↦ birkhoffAverage ℝ τ g (n + 1) ω) := by
    intro n
    -- Proof comment: Birkhoff averages are measurable because the orbit sums are measurable.
    simpa [birkhoffAverage, birkhoffSum, smul_eq_mul] using
      (measurable_birkhoffSum (τ := τ) hτ.measurable hgMeas (n + 1)).const_mul ((n + 1 : ℝ)⁻¹)
  have hF_meas : ∀ᶠ n in atTop, AEStronglyMeasurable (F n) P := by
    refine Filter.Eventually.of_forall fun n ↦ ?_
    -- Proof comment: products of measurable real-valued observables are a.e. strongly measurable.
    exact (hIndicatorMeas.mul (hAvgMeas n)).aestronglyMeasurable
  have hF_bound : ∃ C, ∀ᶠ n in atTop, ∀ᵐ ω ∂P, ‖F n ω‖ ≤ C := by
    refine ⟨1, Filter.Eventually.of_forall fun n ↦ ?_⟩
    refine Filter.Eventually.of_forall fun ω ↦ ?_
    -- Proof comment: on `A` the integrand is the Birkhoff average, off `A` it is zero.
    by_cases hωA : ω ∈ A
    · simpa [F, g, hωA] using
        (norm_birkhoffAverage_indicator_le_one (τ := τ) (B := B) n ω)
    · simp [F, g, hωA]
  have hF_lim :
      ∀ᵐ ω ∂P, Tendsto (fun n ↦ F n ω) atTop (𝓝 (A.indicator (fun _ ↦ P.real B) ω)) := by
    filter_upwards
      [aeTendstoBirkhoffAverageIndicatorOfErgodic (P := P) (τ := τ) hErg hB] with ω hω
    -- Proof comment: multiply the almost-sure Birkhoff limit by the fixed scalar `1_A(ω)`.
    by_cases hωA : ω ∈ A
    · simpa [F, g, hωA] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 (1 : ℝ))).mul hω)
    · simp [F, g, hωA]
  have hIntegralTendsto :
      Tendsto (fun n : ℕ ↦ ∫ ω, F n ω ∂P) atTop (𝓝 (∫ ω, A.indicator (fun _ ↦ P.real B) ω ∂P)) :=
    tendsto_integral_filter_of_norm_le_const (μ := P) hF_meas hF_bound hF_lim
  have hIntegralConst :
      ∫ ω, A.indicator (fun _ ↦ P.real B) ω ∂P = P.real A * P.real B := by
    -- Proof comment: integrate the constant `P.real B` over the event `A`.
    rw [integral_indicator_const (μ := P) (e := (P.real B : ℝ)) hA, smul_eq_mul]
  have hIntegralEq :
      ∀ n : ℕ,
        ∫ ω, F n ω ∂P =
          ((∑ k ∈ Finset.range (n + 1), P.real (A ∩ (τ^[k]) ⁻¹' B)) / (n + 1 : ℝ)) := by
    intro n
    -- Proof comment: this is exactly the correlation-to-integral normalization lemma.
    simpa [F, g] using
      (correlationCesaroReal_eq_integral_indicatorMul_birkhoffAverage
        (P := P) (τ := τ) hτ hA hB n).symm
  have hRealIntegral :
      Tendsto
        (fun n : ℕ ↦ ∫ ω, F n ω ∂P)
        atTop
        (𝓝 (P.real A * P.real B)) := by
    simpa [hIntegralConst] using hIntegralTendsto
  exact hRealIntegral.congr' <| Filter.Eventually.of_forall hIntegralEq

-- Proof sketch: for the forward implication, apply Birkhoff's ergodic theorem to the indicator
-- of `B` and integrate against the indicator of `A`, using dominated convergence to identify the
-- Cesàro averages of the correlation terms. For the converse, test the limit formula on an
-- invariant event `A` with `B = A`; then every summand is `P A`, so the limit forces
-- `P A = (P A)^2`, hence invariant events have probability `0` or `1`.
/-- Theorem 20.23: for a probability-preserving transformation `τ`, ergodicity is equivalent to
the convergence of the Cesàro averages of the correlation probabilities
`P (A ∩ (τ^[k])⁻¹(B))` to `P A * P B` for all measurable events `A` and `B`. -/
theorem ergodic_iff_tendsto_cesaro_preimage_intersection
    (hτ : MeasurePreserving τ P P) :
    Ergodic τ P ↔
      ∀ ⦃A B : Set Ω⦄, MeasurableSet A → MeasurableSet B →
        Tendsto
          (fun n : ℕ ↦
            (∑ k ∈ Finset.range (n + 1), P (A ∩ (τ^[k]) ⁻¹' B)) / (n + 1 : ℝ≥0∞))
          atTop
          (𝓝 (P A * P B)) := by
  constructor
  · intro hErg A B hA hB
    -- Proof comment: first prove the real-valued limit, then transport it to `ℝ≥0∞` with
    -- `ENNReal.ofReal`.
    have hReal :=
      tendsto_correlationCesaroReal_of_ergodic (P := P) (τ := τ) hτ hErg hA hB
    have hOfReal :
        Tendsto
          (fun n : ℕ ↦
            ENNReal.ofReal
              (((∑ k ∈ Finset.range (n + 1), P.real (A ∩ (τ^[k]) ⁻¹' B)) / (n + 1 : ℝ))))
          atTop
          (𝓝 (ENNReal.ofReal (P.real A * P.real B))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp hReal
    have hCesaroEq :
        (fun n : ℕ ↦
          ENNReal.ofReal
            (((∑ k ∈ Finset.range (n + 1), P.real (A ∩ (τ^[k]) ⁻¹' B)) / (n + 1 : ℝ)))) =
          fun n : ℕ ↦
            (∑ k ∈ Finset.range (n + 1), P (A ∩ (τ^[k]) ⁻¹' B)) / (n + 1 : ℝ≥0∞) := by
      funext n
      rw [ENNReal.ofReal_div_of_pos <| by positivity]
      rw [show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by norm_num]
      rw [ENNReal.ofReal_natCast]
      rw [ENNReal.ofReal_sum_of_nonneg]
      · simp [Measure.real]
      · intro k hk
        exact ENNReal.toReal_nonneg
    rw [hCesaroEq] at hOfReal
    simpa [Measure.real, ENNReal.ofReal_mul] using hOfReal
  · intro hCesaro
    refine ⟨hτ, ?_⟩
    refine ⟨?_⟩
    intro A hA hAinv
    -- Proof comment: an invariant event makes every correlation term constant, so the Cesàro
    -- limit forces `P[A] = P[A]^2`.
    have hIterA : ∀ k : ℕ, (τ^[k]) ⁻¹' A = A :=
      preimageIterate_eq_self_of_preimage_eq_self (τ := τ) hAinv
    have hConst :
        ∀ n : ℕ,
        (∑ k ∈ Finset.range (n + 1), P (A ∩ (τ^[k]) ⁻¹' A)) / (n + 1 : ℝ≥0∞) = P A := by
      intro n
      calc
        (∑ k ∈ Finset.range (n + 1), P (A ∩ (τ^[k]) ⁻¹' A)) / (n + 1 : ℝ≥0∞)
            = (∑ k ∈ Finset.range (n + 1), P A) / (n + 1 : ℝ≥0∞) := by
                congr 1
                exact Finset.sum_congr rfl fun k hk ↦ by rw [hIterA k, Set.inter_self]
        _ = ((n + 1 : ℝ≥0∞) * P A) / (n + 1 : ℝ≥0∞) := by
              simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ = P A := by
              simpa [mul_comm, Nat.cast_add, Nat.cast_one] using
                (ENNReal.mul_div_cancel_right (a := P A) (b := (n + 1 : ℝ≥0∞)) (by simp)
                  (by simp))
    have hConstTendsto :
        Tendsto
          (fun n : ℕ ↦ (∑ k ∈ Finset.range (n + 1), P (A ∩ (τ^[k]) ⁻¹' A)) / (n + 1 : ℝ≥0∞))
          atTop
          (𝓝 (P A)) := by
      refine tendsto_const_nhds.congr' ?_
      exact Filter.Eventually.of_forall fun n ↦ (hConst n).symm
    have hEq : P A = P A * P A :=
      tendsto_nhds_unique hConstTendsto (hCesaro hA hA)
    have hRealZeroOrOne : P.real A = 0 ∨ P.real A = 1 := by
      have hrealEq : P.real A = P.real A * P.real A := by
        simpa [Measure.real] using congrArg ENNReal.toReal hEq
      have hmul : P.real A * (1 - P.real A) = 0 := by
        nlinarith
      rcases eq_zero_or_eq_zero_of_mul_eq_zero hmul with hzero | hone
      · exact Or.inl hzero
      · exact Or.inr <| by linarith
    rcases hRealZeroOrOne with hzero | hone
    · exact Filter.eventuallyConst_set'.2 <| Or.inl <|
        ae_eq_empty.2 <| (measureReal_eq_zero_iff (μ := P) (s := A)).mp hzero
    · have hAcompl : P Aᶜ = 0 := by
        rw [measure_compl hA (measure_ne_top P A), IsProbabilityMeasure.measure_univ,
          (ENNReal.toReal_eq_one_iff (P A)).mp (by simpa [Measure.real] using hone), tsub_self]
      exact Filter.eventuallyConst_set'.2 <| Or.inr <| ae_eq_univ.2 hAcompl

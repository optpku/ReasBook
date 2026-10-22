/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Definition_15_40

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ProbabilityTheory

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

namespace RealRandomVariableArray

namespace SatisfiesLyapunovCondition

/-- Helper for Lemma 15.41: if the row-sum variance vanishes, then the normalized Lindeberg
quantity is zero because the definition uses `Var[A.rowSum n; μ]⁻¹`. -/
lemma lindebergFunction_eq_zero_of_rowSum_variance_eq_zero
    {A : RealRandomVariableArray Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ε : ℝ} {n : ℕ} (hVar : Var[A.rowSum n; μ] = 0) :
    A.lindebergFunction μ ε n = 0 := by
  -- Proof comment: unfold the normalization and use `0⁻¹ = 0`.
  simp [RealRandomVariableArray.lindebergFunction_def, hVar]

/-- Helper for Lemma 15.41: on the truncation set `ε ^ 2 * v < x ^ 2`, the square is bounded by
the scaled absolute `(2 + δ)`-moment integrand. -/
lemma truncatedSquare_le_scaledAbsMoment
    {x ε δ v : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hv : 0 < v)
    (hx : ε ^ 2 * v < x ^ 2) :
    x ^ 2 ≤ ε ^ (-δ) * (Real.rpow v (δ / 2))⁻¹ * Real.rpow |x| (2 + δ) := by
  -- Proof comment: raise the truncation inequality to the exponent `δ / 2`.
  have hpow : ε ^ δ * Real.rpow v (δ / 2) ≤ Real.rpow |x| δ := by
    have hpow' :=
      Real.rpow_le_rpow (by positivity : 0 ≤ ε ^ 2 * v) hx.le (by positivity : 0 ≤ δ / 2)
    have hεrewrite : (ε ^ 2 : ℝ) ^ (δ / 2) = ε ^ δ := by
      calc
        (ε ^ 2 : ℝ) ^ (δ / 2) = ε ^ ((2 : ℝ) * (δ / 2)) := by
          simpa using (Real.rpow_natCast_mul hε.le 2 (δ / 2)).symm
        _ = ε ^ δ := by
          congr 1
          ring
    have hxrewrite : (x ^ 2 : ℝ) ^ (δ / 2) = Real.rpow |x| δ := by
      calc
        (x ^ 2 : ℝ) ^ (δ / 2) = (|x| ^ 2 : ℝ) ^ (δ / 2) := by rw [sq_abs]
        _ = |x| ^ ((2 : ℝ) * (δ / 2)) := by
          simpa using (Real.rpow_natCast_mul (abs_nonneg x) 2 (δ / 2)).symm
        _ = Real.rpow |x| δ := by
          congr 1
          ring
    calc
      ε ^ δ * Real.rpow v (δ / 2) = ε ^ δ * (v ^ (δ / 2) : ℝ) := by
        rfl
      _ = (ε ^ 2 * v) ^ (δ / 2) := by
        rw [Real.mul_rpow (by positivity) hv.le, hεrewrite]
      _ ≤ (x ^ 2) ^ (δ / 2) := hpow'
      _ = Real.rpow |x| δ := hxrewrite
  -- Proof comment: multiply by `|x| ^ 2` and fold the powers into `|x| ^ (2 + δ)`.
  have hmul : |x| ^ 2 * (ε ^ δ * Real.rpow v (δ / 2)) ≤ Real.rpow |x| (2 + δ) := by
    have habs_add : |x| ^ 2 * Real.rpow |x| δ = Real.rpow |x| (2 + δ) := by
      symm
      simpa [Real.rpow_natCast] using
        (Real.rpow_add_of_nonneg (abs_nonneg x) (by positivity : 0 ≤ (2 : ℝ)) hδ.le)
    calc
      |x| ^ 2 * (ε ^ δ * Real.rpow v (δ / 2)) ≤ |x| ^ 2 * Real.rpow |x| δ := by
        gcongr
      _ = Real.rpow |x| (2 + δ) := habs_add
  have hconst_pos : 0 < ε ^ δ * Real.rpow v (δ / 2) := by
    exact mul_pos (Real.rpow_pos_of_pos hε _) (Real.rpow_pos_of_pos hv _)
  have hmain : |x| ^ 2 ≤ (ε ^ δ * Real.rpow v (δ / 2))⁻¹ * Real.rpow |x| (2 + δ) := by
    rw [le_inv_mul_iff₀ hconst_pos]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  -- Proof comment: rewrite the reciprocal constant as `ε ^ (-δ) * v ^ (-δ / 2)`.
  calc
    x ^ 2 = |x| ^ 2 := by rw [sq_abs]
    _ ≤ (ε ^ δ * Real.rpow v (δ / 2))⁻¹ * Real.rpow |x| (2 + δ) := hmain
    _ = ε ^ (-δ) * (Real.rpow v (δ / 2))⁻¹ * Real.rpow |x| (2 + δ) := by
      rw [mul_inv_rev, Real.rpow_neg hε.le]
      simp [mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Lemma 15.41: each rowwise Lindeberg quantity is bounded by the corresponding
scaled Lyapunov quantity in `ENNReal`. -/
lemma ofReal_lindebergFunction_le_scaledLyapunovFunction
    {A : RealRandomVariableArray Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hSq : ∀ n i, MemLp (A n i) 2 μ) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (n : ℕ) :
    ENNReal.ofReal (A.lindebergFunction μ ε n) ≤
      ENNReal.ofReal (ε ^ (-δ)) * A.lyapunovFunction μ δ n := by
  by_cases hVar : Var[A.rowSum n; μ] = 0
  · -- Proof comment: the degenerate row is zero on the left, so the comparison is immediate.
    rw [lindebergFunction_eq_zero_of_rowSum_variance_eq_zero hVar]
    simp
  have hv : 0 < Var[A.rowSum n; μ] := by
    refine lt_of_le_of_ne (ProbabilityTheory.variance_nonneg _ _) ?_
    simpa [eq_comm] using hVar
  let s : Fin (A.rowLength n) → Set Ω :=
    fun i ↦ {ω | ε ^ 2 * Var[A.rowSum n; μ] < (A n i ω) ^ 2}
  let c : ℝ := ε ^ (-δ) * (Real.rpow (Var[A.rowSum n; μ]) (δ / 2))⁻¹
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hs : ∀ i : Fin (A.rowLength n), MeasurableSet (s i) := by
    intro i
    -- Proof comment: the truncation event is measurable because each row entry is measurable.
    dsimp [s]
    exact measurableSet_lt measurable_const ((A.measurable_entry n i).pow_const 2)
  have hterm_nonneg :
      ∀ i : Fin (A.rowLength n),
        0 ≤ μ[Set.indicator (s i) (fun ω ↦ (A n i ω) ^ 2)] := by
    intro i
    -- Proof comment: every truncated square integrand is pointwise nonnegative.
    refine integral_nonneg ?_
    intro ω
    by_cases hω : ω ∈ s i
    · simpa [Set.mem_setOf_eq, hω] using sq_nonneg (A n i ω)
    · simp [Set.mem_setOf_eq, hω]
  have hterm_le :
      ∀ i : Fin (A.rowLength n),
        ENNReal.ofReal (μ[Set.indicator (s i) (fun ω ↦ (A n i ω) ^ 2)]) ≤
          ENNReal.ofReal c *
            ∫⁻ ω, ENNReal.ofReal (Real.rpow |A n i ω| (2 + δ)) ∂μ := by
    intro i
    have hInt : Integrable (Set.indicator (s i) (fun ω ↦ (A n i ω) ^ 2)) μ := by
      exact ((hSq n i).integrable_sq).indicator (hs i)
    have hNonneg : 0 ≤ᵐ[μ] Set.indicator (s i) (fun ω ↦ (A n i ω) ^ 2) := by
      exact Filter.Eventually.of_forall fun ω ↦ by
        by_cases hω : ω ∈ s i
        · simp [s, hω, sq_nonneg]
        · simp [s, hω]
    calc
      ENNReal.ofReal (μ[Set.indicator (s i) (fun ω ↦ (A n i ω) ^ 2)]) =
          ∫⁻ ω, ENNReal.ofReal (Set.indicator (s i) (fun ω ↦ (A n i ω) ^ 2) ω) ∂μ := by
        rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hNonneg]
      _ ≤ ∫⁻ ω, ENNReal.ofReal (c * Real.rpow |A n i ω| (2 + δ)) ∂μ := by
        -- Proof comment: compare the integrands pointwise using the scalar truncation estimate.
        refine lintegral_mono_ae ?_
        filter_upwards with ω
        by_cases hω : ω ∈ s i
        · have hω' : ε ^ 2 * Var[A.rowSum n; μ] < (A n i ω) ^ 2 := by
            simpa [s] using hω
          simp [hω, c]
          exact ENNReal.ofReal_le_ofReal
            (truncatedSquare_le_scaledAbsMoment hε hδ hv hω')
        · simp [hω, c]
      _ = ENNReal.ofReal c *
          ∫⁻ ω, ENNReal.ofReal (Real.rpow |A n i ω| (2 + δ)) ∂μ := by
        simp_rw [ENNReal.ofReal_mul hc_nonneg]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hsum_nonneg :
      0 ≤ ∑ i : Fin (A.rowLength n), μ[Set.indicator (s i) (fun ω ↦ (A n i ω) ^ 2)] := by
    refine Finset.sum_nonneg fun i _ ↦ hterm_nonneg i
  have hsum_le :
      ∑ i : Fin (A.rowLength n),
          ENNReal.ofReal (μ[Set.indicator (s i) (fun ω ↦ (A n i ω) ^ 2)]) ≤
        ENNReal.ofReal c *
          ∑ i : Fin (A.rowLength n),
            ∫⁻ ω, ENNReal.ofReal (Real.rpow |A n i ω| (2 + δ)) ∂μ := by
    calc
      ∑ i : Fin (A.rowLength n),
          ENNReal.ofReal (μ[Set.indicator (s i) (fun ω ↦ (A n i ω) ^ 2)]) ≤
          ∑ i : Fin (A.rowLength n),
            ENNReal.ofReal c *
              ∫⁻ ω, ENNReal.ofReal (Real.rpow |A n i ω| (2 + δ)) ∂μ := by
        refine Finset.sum_le_sum fun i _ ↦ hterm_le i
      _ = ENNReal.ofReal c *
          ∑ i : Fin (A.rowLength n),
            ∫⁻ ω, ENNReal.ofReal (Real.rpow |A n i ω| (2 + δ)) ∂μ := by
        rw [Finset.mul_sum]
  have hconst :
      ENNReal.ofReal ((Var[A.rowSum n; μ])⁻¹) * ENNReal.ofReal c =
        ENNReal.ofReal (ε ^ (-δ)) *
          (ENNReal.ofReal (Real.rpow (Var[A.rowSum n; μ]) (1 + δ / 2)))⁻¹ := by
    have hconstReal :
        (Var[A.rowSum n; μ])⁻¹ * c =
          ε ^ (-δ) * (Real.rpow (Var[A.rowSum n; μ]) (1 + δ / 2))⁻¹ := by
      have hvpow :
          (Real.rpow (Var[A.rowSum n; μ]) (1 + δ / 2))⁻¹ =
            (Var[A.rowSum n; μ])⁻¹ * (Real.rpow (Var[A.rowSum n; μ]) (δ / 2))⁻¹ := by
        have hpowfactor :
            Real.rpow (Var[A.rowSum n; μ]) (1 + δ / 2) =
              Var[A.rowSum n; μ] * Real.rpow (Var[A.rowSum n; μ]) (δ / 2) := by
          simpa [Real.rpow_one] using
            (Real.rpow_add hv (1 : ℝ) (δ / 2))
        rw [hpowfactor, mul_inv_rev]
        simp [mul_comm]
      calc
        (Var[A.rowSum n; μ])⁻¹ * c =
            ε ^ (-δ) *
              ((Var[A.rowSum n; μ])⁻¹ *
                (Real.rpow (Var[A.rowSum n; μ]) (δ / 2))⁻¹) := by
          simp [c, mul_assoc, mul_left_comm, mul_comm]
        _ = ε ^ (-δ) * (Real.rpow (Var[A.rowSum n; μ]) (1 + δ / 2))⁻¹ := by
          rw [hvpow]
    calc
      ENNReal.ofReal ((Var[A.rowSum n; μ])⁻¹) * ENNReal.ofReal c =
          ENNReal.ofReal ((Var[A.rowSum n; μ])⁻¹ * c) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hv.le)]
      _ = ENNReal.ofReal (ε ^ (-δ) * (Real.rpow (Var[A.rowSum n; μ]) (1 + δ / 2))⁻¹) := by
        rw [hconstReal]
      _ = ENNReal.ofReal (ε ^ (-δ)) *
          (ENNReal.ofReal (Real.rpow (Var[A.rowSum n; μ]) (1 + δ / 2)))⁻¹ := by
        have hεneg_nonneg : 0 ≤ ε ^ (-δ) := by positivity
        have hrpow_pos : 0 < Real.rpow (Var[A.rowSum n; μ]) (1 + δ / 2) := by
          exact Real.rpow_pos_of_pos hv _
        rw [ENNReal.ofReal_mul hεneg_nonneg, ENNReal.ofReal_inv_of_pos hrpow_pos]
  calc
    ENNReal.ofReal (A.lindebergFunction μ ε n) =
        ENNReal.ofReal ((Var[A.rowSum n; μ])⁻¹) *
          ∑ i : Fin (A.rowLength n),
            ENNReal.ofReal (μ[Set.indicator (s i) (fun ω ↦ (A n i ω) ^ 2)]) := by
      rw [RealRandomVariableArray.lindebergFunction_def, ENNReal.ofReal_mul (inv_nonneg.2 hv.le)]
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i hi
      exact hterm_nonneg i
    _ ≤ ENNReal.ofReal ((Var[A.rowSum n; μ])⁻¹) *
        (ENNReal.ofReal c *
          ∑ i : Fin (A.rowLength n),
            ∫⁻ ω, ENNReal.ofReal (Real.rpow |A n i ω| (2 + δ)) ∂μ) := by
      exact mul_le_mul_left' hsum_le _
    _ = (ENNReal.ofReal ((Var[A.rowSum n; μ])⁻¹) * ENNReal.ofReal c) *
        ∑ i : Fin (A.rowLength n),
          ∫⁻ ω, ENNReal.ofReal (Real.rpow |A n i ω| (2 + δ)) ∂μ := by
      rw [mul_assoc]
    _ = ENNReal.ofReal (ε ^ (-δ)) *
        ((ENNReal.ofReal (Real.rpow (Var[A.rowSum n; μ]) (1 + δ / 2)))⁻¹ *
          ∑ i : Fin (A.rowLength n),
            ∫⁻ ω, ENNReal.ofReal (Real.rpow |A n i ω| (2 + δ)) ∂μ) := by
      rw [hconst, mul_assoc]
    _ = ENNReal.ofReal (ε ^ (-δ)) * A.lyapunovFunction μ δ n := by
      rw [RealRandomVariableArray.lyapunovFunction_def]

-- Proof sketch: fix `ε > 0` and use the pointwise inequality
-- `x^2 1_{|x| > ε √Var[Sₙ]} ≤ ε^{-δ} Var[Sₙ]^{-δ / 2} |x|^(2 + δ)` termwise inside the row sum.
-- After dividing by `Var[Sₙ]`, the Lindeberg quantity is bounded by `ε^{-δ}` times the
-- Lyapunov quantity of order `2 + δ`, so the assumed convergence to `0` implies the
-- Lindeberg convergence.
/-- Lemma 15.41: every centered square-integrable array satisfying the Lyapunov condition also
satisfies the Lindeberg condition. -/
theorem satisfiesLindebergCondition
    {A : RealRandomVariableArray Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hA : A.SatisfiesLyapunovCondition μ) :
    A.SatisfiesLindebergCondition μ := by
  rcases hA.exists_delta with ⟨δ, hδ, hMoment, hLyap⟩
  refine
    { toIsCentered := hA.toIsCentered
      memLp_two := hA.memLp_two
      lindeberg_tendsto := ?_ }
  intro ε hε
  let u : ℕ → ENNReal := fun n ↦ ENNReal.ofReal (A.lindebergFunction μ ε n)
  have hLindeberg_nonneg : ∀ n : ℕ, 0 ≤ A.lindebergFunction μ ε n := by
    intro n
    -- Proof comment: the Lindeberg quantity is a nonnegative normalization of nonnegative terms.
    rw [RealRandomVariableArray.lindebergFunction_def]
    refine mul_nonneg (inv_nonneg.2 (ProbabilityTheory.variance_nonneg _ _)) ?_
    refine Finset.sum_nonneg fun i _ ↦ ?_
    refine integral_nonneg ?_
    intro ω
    by_cases hω : ω ∈ {ω | ε ^ 2 * Var[A.rowSum n; μ] < (A n i ω) ^ 2}
    · simpa [Set.mem_setOf_eq, hω] using sq_nonneg (A n i ω)
    · simp [Set.mem_setOf_eq, hω]
  have hu_le :
      ∀ n : ℕ, u n ≤ ENNReal.ofReal (ε ^ (-δ)) * A.lyapunovFunction μ δ n := by
    intro n
    -- Proof comment: this is the rowwise comparison proved above.
    simpa [u] using
      ofReal_lindebergFunction_le_scaledLyapunovFunction hA.memLp_two hε hδ n
  have hscaled :
      Tendsto (fun n ↦ ENNReal.ofReal (ε ^ (-δ)) * A.lyapunovFunction μ δ n) atTop (nhds 0) := by
    -- Proof comment: multiply the Lyapunov convergence by the fixed scalar `ε ^ (-δ)`.
    simpa using
      (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (ε ^ (-δ))) hLyap
        (Or.inr ENNReal.ofReal_ne_top))
  have hu_tendsto : Tendsto u atTop (nhds 0) := by
    -- Proof comment: squeeze `u` between `0` and the scaled Lyapunov sequence.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hscaled ?_ ?_
    · intro n
      simp [u]
    · intro n
      exact hu_le n
  have hu_finite : ∀ n : ℕ, u n ≠ ⊤ := by
    intro n
    simp [u]
  -- Proof comment: `u n = ofReal (Lₙ(ε))`, so converting back to `ℝ` recovers the desired limit.
  simpa [u, hLindeberg_nonneg] using
    (ENNReal.tendsto_toReal_zero_iff hu_finite).2 hu_tendsto

end SatisfiesLyapunovCondition

end RealRandomVariableArray

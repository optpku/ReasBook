/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Remark_9_38

open MeasureTheory
open scoped BigOperators

universe u

namespace ProbabilityTheory

variable {Ω : Type u}

/-- Helper for Theorem 9.39: the discrete stochastic integral changes by exactly the new stake
times the new increment of the integrator. -/
lemma stochasticIntegral_succ_sub (H X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    stochasticIntegral H X (n + 1) ω - stochasticIntegral H X n ω =
      H (n + 1) ω * (X (n + 1) ω - X n ω) := by
  -- Expand the final partial sum and cancel the previously accumulated terms.
  simp [stochasticIntegral_apply, Finset.sum_range_succ]

/-- Helper for Theorem 9.39: integrating against the constant process `1` telescopes to the
difference between the current value and the initial value. -/
lemma stochasticIntegral_one_eq_sub_initial (X : ℕ → Ω → ℝ) :
    stochasticIntegral (fun _ _ ↦ (1 : ℝ)) X = fun n ω ↦ X n ω - X 0 ω := by
  ext n ω
  induction n with
  | zero =>
      -- At time `0` the stochastic integral is the empty sum.
      simp [stochasticIntegral_apply]
  | succ n ih =>
      -- The new summand adds the next increment, so the partial sums telescope.
      calc
        stochasticIntegral (fun _ _ ↦ (1 : ℝ)) X (n + 1) ω
            = stochasticIntegral (fun _ _ ↦ (1 : ℝ)) X n ω
                + (stochasticIntegral (fun _ _ ↦ (1 : ℝ)) X (n + 1) ω
                    - stochasticIntegral (fun _ _ ↦ (1 : ℝ)) X n ω) := by
              ring
        _ = stochasticIntegral (fun _ _ ↦ (1 : ℝ)) X n ω + (X (n + 1) ω - X n ω) := by
              rw [stochasticIntegral_succ_sub]
              simp
        _ = X n ω - X 0 ω + (X (n + 1) ω - X n ω) := by
              rw [ih]
        _ = X (n + 1) ω - X 0 ω := by
              ring

/-- Helper for Theorem 9.39: negating the integrator negates the discrete stochastic integral. -/
lemma stochasticIntegral_neg_right (H X : ℕ → Ω → ℝ) :
    stochasticIntegral H (-X) = -stochasticIntegral H X := by
  ext n ω
  induction n with
  | zero =>
      -- Both stochastic integrals vanish at time `0`.
      simp [stochasticIntegral_apply]
  | succ n ih =>
      -- Each new summand acquires a minus sign when the integrator is negated.
      calc
        stochasticIntegral H (-X) (n + 1) ω
            = stochasticIntegral H (-X) n ω
                + H (n + 1) ω * ((-X) (n + 1) ω - (-X) n ω) := by
                  simp [stochasticIntegral_apply, Finset.sum_range_succ]
        _ = (-stochasticIntegral H X) n ω
              + H (n + 1) ω * ((-X) (n + 1) ω - (-X) n ω) := by
                  rw [ih]
        _ = (-stochasticIntegral H X) (n + 1) ω := by
              simp [stochasticIntegral_apply, Finset.sum_range_succ]
              ring

/-- Helper for Theorem 9.39: the stochastic integral agrees with the function-valued sum form used
by `Submartingale.sum_mul_sub'`. -/
lemma stochasticIntegral_eq_sum_mul_sub (H X : ℕ → Ω → ℝ) :
    stochasticIntegral H X =
      fun n ↦ ∑ k ∈ Finset.range n, H (k + 1) * (X (k + 1) - X k) := by
  funext n ω
  simp [stochasticIntegral_apply]

variable [mΩ : MeasurableSpace Ω]
variable {ℱ : Filtration ℕ mΩ} {μ : Measure Ω}

/-- Helper for Theorem 9.39: a locally bounded predictable integrand produces integrable
stochastic-integral values against an integrable process. -/
lemma stochasticIntegral_integrable [IsFiniteMeasure μ] {H X : ℕ → Ω → ℝ}
    (hH : IsPredictable ℱ H) (hH_bdd : IsLocallyBoundedProcess H)
    (hX_int : ∀ n, Integrable (X n) μ) :
    ∀ n, Integrable (stochasticIntegral H X n) μ := by
  intro n
  -- Control each summand by the local bound at the corresponding time.
  simpa [stochasticIntegral_apply] using
    (integrable_finset_sum (Finset.range n) fun k hk ↦ by
      obtain ⟨C, hC_nonneg, hC⟩ := hH_bdd (k + 1)
      have hH_meas : Measurable (H (k + 1)) :=
        (hH.measurable_add_one k).mono (ℱ.le k) (by rfl)
      have hdiff_int : Integrable (fun ω ↦ X (k + 1) ω - X k ω) μ :=
        (hX_int (k + 1)).sub (hX_int k)
      exact hdiff_int.bdd_mul (c := C)
        (hH_meas.stronglyMeasurable.aestronglyMeasurable)
        (ae_of_all _ fun ω ↦ by simpa [Real.norm_eq_abs] using hC ω))

/-- Helper for Theorem 9.39: nonnegative locally bounded predictable integrands preserve the
submartingale property under the discrete stochastic integral. -/
lemma submartingale_stochasticIntegral [IsFiniteMeasure μ] {X H : ℕ → Ω → ℝ}
    (hX : Submartingale X ℱ μ) (hH : IsPredictable ℱ H)
    (hH_bdd : IsLocallyBoundedProcess H) (hH_nonneg : ∀ n ω, 0 ≤ H n ω) :
    Submartingale (stochasticIntegral H X) ℱ μ := by
  have hSI_adapted : StronglyAdapted ℱ (stochasticIntegral H X) :=
    (stochasticIntegral_adapted hH hX.stronglyAdapted.adapted).stronglyAdapted
  have hSI_int : ∀ n, Integrable (stochasticIntegral H X n) μ :=
    stochasticIntegral_integrable hH hH_bdd hX.integrable
  refine submartingale_of_condExp_sub_nonneg_nat hSI_adapted hSI_int fun n ↦ ?_
  choose C hC_nonneg hC using hH_bdd
  let ξ : ℕ → Ω → ℝ := fun m ω ↦ if m ≤ n + 1 then H m ω else 0
  let R : ℝ := Finset.sum (Finset.range (n + 2)) C
  have hR_nonneg : 0 ≤ R := by
    exact Finset.sum_nonneg fun k hk ↦ hC_nonneg k
  have hξ_adapted : StronglyAdapted ℱ fun m ↦ ξ (m + 1) := by
    intro m
    by_cases hm : m + 1 ≤ n + 1
    · simpa [ξ, hm] using (hH.measurable_add_one m).stronglyMeasurable
    · simpa [ξ, hm] using
        (stronglyMeasurable_const : StronglyMeasurable[ℱ m] (fun _ : Ω ↦ (0 : ℝ)))
  have hξ_bdd : ∀ m ω, ξ m ω ≤ R := by
    intro m ω
    by_cases hm : m ≤ n + 1
    · have hm_mem : m ∈ Finset.range (n + 2) := by
        simp [Finset.mem_range, Nat.lt_succ_iff.mpr hm]
      have hCm_le_R : C m ≤ R := by
        simpa [R] using Finset.single_le_sum (fun k hk ↦ hC_nonneg k) hm_mem
      have hHm_le_Cm : H m ω ≤ C m := by
        simpa [abs_of_nonneg (hH_nonneg m ω)] using hC m ω
      simpa [ξ, hm] using hHm_le_Cm.trans hCm_le_R
    · simpa [ξ, hm] using hR_nonneg
  have hξ_nonneg : ∀ m ω, 0 ≤ ξ m ω := by
    intro m ω
    by_cases hm : m ≤ n + 1
    · simpa [ξ, hm] using hH_nonneg m ω
    · simp [ξ, hm]
  have hTrunc :
      Submartingale (stochasticIntegral ξ X) ℱ μ := by
    -- On a finite horizon, the locally bounded predictable process becomes globally bounded.
    simpa [stochasticIntegral_eq_sum_mul_sub] using
      hX.sum_mul_sub' hξ_adapted hξ_bdd hξ_nonneg
  have hCondEq :
      μ[stochasticIntegral ξ X (n + 1) - stochasticIntegral ξ X n | ℱ n] =ᵐ[μ]
        μ[stochasticIntegral H X (n + 1) - stochasticIntegral H X n | ℱ n] := by
    -- The truncation agrees with `H` at the single increment used between times `n` and `n + 1`.
    refine condExp_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
    simp [stochasticIntegral_succ_sub, ξ]
  exact (hTrunc.condExp_sub_nonneg n.le_succ).trans hCondEq.le

/-- Helper for Theorem 9.39: a martingale integrator and a locally bounded predictable integrand
produce a submartingale after splitting the stake process into positive and negative parts. -/
lemma martingale_stochasticIntegral_submartingale [IsFiniteMeasure μ] {X H : ℕ → Ω → ℝ}
    (hX : Martingale X ℱ μ) (hH : IsPredictable ℱ H) (hH_bdd : IsLocallyBoundedProcess H) :
    Submartingale (stochasticIntegral H X) ℱ μ := by
  let Hpos : ℕ → Ω → ℝ := fun n ω ↦ max (H n ω) 0
  let Hneg : ℕ → Ω → ℝ := fun n ω ↦ max (-H n ω) 0
  have hHpos : IsPredictable ℱ Hpos := by
    refine isPredictable_of_measurable_add_one ?_ ?_
    · simpa [Hpos] using (hH.adapted 0).measurable.max measurable_const
    · intro n
      simpa [Hpos] using (hH.measurable_add_one n).max measurable_const
  have hHneg : IsPredictable ℱ Hneg := by
    refine isPredictable_of_measurable_add_one ?_ ?_
    · simpa [Hneg] using (hH.adapted 0).measurable.neg.max measurable_const
    · intro n
      simpa [Hneg] using (hH.measurable_add_one n).neg.max measurable_const
  have hHpos_bdd : IsLocallyBoundedProcess Hpos := by
    intro n
    obtain ⟨C, hC_nonneg, hC⟩ := hH_bdd n
    refine ⟨C, hC_nonneg, fun ω ↦ ?_⟩
    have hmax_le : max (H n ω) 0 ≤ |H n ω| := by
      exact max_le (le_abs_self _) (abs_nonneg _)
    have hHpos_nonneg : 0 ≤ Hpos n ω := le_max_right _ _
    rw [abs_of_nonneg hHpos_nonneg]
    exact hmax_le.trans (hC ω)
  have hHneg_bdd : IsLocallyBoundedProcess Hneg := by
    intro n
    obtain ⟨C, hC_nonneg, hC⟩ := hH_bdd n
    refine ⟨C, hC_nonneg, fun ω ↦ ?_⟩
    have hmax_le : max (-H n ω) 0 ≤ |-H n ω| := by
      exact max_le (le_abs_self _) (abs_nonneg _)
    have hHneg_nonneg : 0 ≤ Hneg n ω := le_max_right _ _
    rw [abs_of_nonneg hHneg_nonneg]
    exact hmax_le.trans (by simpa [abs_neg] using hC ω)
  have hHpos_nonneg : ∀ n ω, 0 ≤ Hpos n ω := by
    intro n ω
    exact le_max_right _ _
  have hHneg_nonneg : ∀ n ω, 0 ≤ Hneg n ω := by
    intro n ω
    exact le_max_right _ _
  have hPos :
      Submartingale (stochasticIntegral Hpos X) ℱ μ :=
    submartingale_stochasticIntegral hX.submartingale hHpos hHpos_bdd hHpos_nonneg
  have hNeg :
      Submartingale (stochasticIntegral Hneg (-X)) ℱ μ :=
    submartingale_stochasticIntegral hX.neg.submartingale hHneg hHneg_bdd hHneg_nonneg
  have hDecomp :
      stochasticIntegral H X = stochasticIntegral Hpos X + stochasticIntegral Hneg (-X) := by
    ext n ω
    induction n with
    | zero =>
        simp [stochasticIntegral_apply]
    | succ n ih =>
        have hStep :
            H (n + 1) ω * (X (n + 1) ω - X n ω) =
              Hpos (n + 1) ω * (X (n + 1) ω - X n ω) +
                Hneg (n + 1) ω * ((-X) (n + 1) ω - (-X) n ω) := by
          by_cases hω : 0 ≤ H (n + 1) ω
          · have hnegω : -H (n + 1) ω ≤ 0 := by
              linarith
            simp [Hpos, Hneg, hω, hnegω]
          · have hω' : H (n + 1) ω ≤ 0 := le_of_not_ge hω
            have hnegω : 0 ≤ -H (n + 1) ω := by
              linarith
            simp [Hpos, Hneg, hω', hnegω]
            ring
        calc
          stochasticIntegral H X (n + 1) ω
              = stochasticIntegral H X n ω + H (n + 1) ω * (X (n + 1) ω - X n ω) := by
                  linarith [stochasticIntegral_succ_sub H X n ω]
          _ = stochasticIntegral Hpos X n ω + stochasticIntegral Hneg (-X) n ω +
                (Hpos (n + 1) ω * (X (n + 1) ω - X n ω) +
                  Hneg (n + 1) ω * ((-X) (n + 1) ω - (-X) n ω)) := by
                rw [ih, hStep]
                simp [Pi.add_apply, add_assoc, add_comm]
          _ = stochasticIntegral Hpos X (n + 1) ω + stochasticIntegral Hneg (-X) (n + 1) ω := by
                linarith [stochasticIntegral_succ_sub Hpos X n ω,
                  stochasticIntegral_succ_sub Hneg (-X) n ω]
  -- The positive and negative parts produce submartingales whose sum is the original transform.
  simpa [hDecomp] using hPos.add hNeg

/-- Helper for Theorem 9.39: locally bounded predictable integrands preserve the martingale
property under the discrete stochastic integral. -/
lemma martingale_stochasticIntegral [IsFiniteMeasure μ] {X H : ℕ → Ω → ℝ}
    (hX : Martingale X ℱ μ) (hH : IsPredictable ℱ H) (hH_bdd : IsLocallyBoundedProcess H) :
    Martingale (stochasticIntegral H X) ℱ μ := by
  have hSub :
      Submartingale (stochasticIntegral H X) ℱ μ :=
    martingale_stochasticIntegral_submartingale hX hH hH_bdd
  have hNegSub :
      Submartingale (-stochasticIntegral H X) ℱ μ := by
    simpa [stochasticIntegral_neg_right H X] using
      martingale_stochasticIntegral_submartingale hX.neg hH hH_bdd
  -- A process is a martingale once both it and its negative are submartingales.
  exact (martingale_iff).2 ⟨by simpa using hNegSub.neg, hSub⟩

end ProbabilityTheory

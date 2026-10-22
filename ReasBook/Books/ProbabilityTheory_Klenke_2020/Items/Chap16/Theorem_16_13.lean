/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Definition_15_39
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Theorem_16_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Corollary_16_9

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

universe u v

noncomputable section

open RealRandomVariableArray

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {Ω' : Type v} [MeasurableSpace Ω']
variable (A : RealRandomVariableArray Ω) (P : Measure Ω) [IsProbabilityMeasure P]
variable [A.IsIndependent P] [A.IsNull P]

/-- Helper for Theorem 16.13: identical distribution transfers infinite divisibility of random
variables. -/
lemma isInfinitelyDivisibleRandomVariable_of_identDistrib
    (Q : Measure Ω') [IsProbabilityMeasure Q] {X Y : Ω' → ℝ}
    (hXY : IdentDistrib X Y Q Q) :
    IsInfinitelyDivisibleRandomVariable Q Y → IsInfinitelyDivisibleRandomVariable Q X := by
  intro hY n
  -- Reuse the same i.i.d. decomposition and replace only the final distributional identification.
  rcases hY n with ⟨Ω'', hΩ'', P', ν, Z, hZ_meas, hZ_law, hZ_indep, hZ_sum⟩
  exact ⟨Ω'', hΩ'', P', ν, Z, hZ_meas, hZ_law, hZ_indep, hXY.trans hZ_sum⟩

/-- Helper for Theorem 16.13: replacing the limit variable by its measurable representative does
not change the pushed-forward law. -/
lemma measurableRepresentativeLaw_eq
    (Q : Measure Ω') [IsProbabilityMeasure Q] (S : Ω' → ℝ)
    (hS : TendstoInDistribution A.rowSum atTop S (fun _ ↦ P) Q) :
    ProbabilityMeasure.map ⟨Q, inferInstance⟩ hS.aemeasurable_limit =
      ProbabilityMeasure.map ⟨Q, inferInstance⟩
        hS.aemeasurable_limit.measurable_mk.aemeasurable := by
  -- Proof comment: the measurable representative `mk S` agrees with `S` almost everywhere, so
  -- the two pushforward laws coincide.
  apply ProbabilityMeasure.toMeasure_injective
  simpa using Measure.map_congr hS.aemeasurable_limit.ae_eq_mk

/-- Helper for Theorem 16.13: law-side infinite divisibility for the measurable representative
immediately gives infinite divisibility of that representative as a random variable. -/
lemma measurableRepresentative_isInfinitelyDivisible
    (Q : Measure Ω') [IsProbabilityMeasure Q] (S : Ω' → ℝ)
    (hS : TendstoInDistribution A.rowSum atTop S (fun _ ↦ P) Q)
    (hLaw :
      ProbabilityMeasure.IsInfinitelyDivisible
        (ProbabilityMeasure.map ⟨Q, inferInstance⟩
          hS.aemeasurable_limit.measurable_mk.aemeasurable)) :
    IsInfinitelyDivisibleRandomVariable Q (hS.aemeasurable_limit.mk S) := by
  -- Proof comment: the owner-level law criterion from Definition 16.1 applies directly to the
  -- measurable representative.
  exact
    (isInfinitelyDivisibleRandomVariable_iff_law_isInfinitelyDivisible
      (P := Q) (X := hS.aemeasurable_limit.mk S) hS.aemeasurable_limit.measurable_mk).2 hLaw

/-- Helper for Theorem 16.13: the characteristic function of a row-sum law factors into the
product of the characteristic functions of the row entries. -/
lemma rowSumLaw_charFun_eq_prod_entryCharFun
    (n : ℕ) (t : ℝ) :
    charFun (Measure.map (A.rowSum n) P) t =
      ∏ l : Fin (A.rowLength n), charFun (P.map (A n l)) t := by
  -- Factor the characteristic function of the finite sum using rowwise independence.
  have hrow :
      A.rowSum n = fun ω ↦ ∑ i : Fin (A.rowLength n), A n i ω := by
    funext ω
    simp [RealRandomVariableArray.rowSum, Finset.sum_apply]
  have hlaw :
      charFun (A.rowSumLaw P n : Measure ℝ) t =
        ∏ l : Fin (A.rowLength n), charFun (P.map (A n l)) t := by
    rw [A.rowSumLaw_toMeasure P n, hrow]
    simpa using congrFun
      ((RealRandomVariableArray.IsIndependent.rowwise (A := A) (μ := P) n).charFun_map_fun_sum_eq_prod
        (fun i ↦ (A.measurable_entry n i).aemeasurable)) t
  simpa [A.rowSumLaw_toMeasure P n] using hlaw

/-- Helper for Theorem 16.13: convergence in distribution of the row sums gives pointwise
convergence of the row-entry characteristic-function products to the limiting law. -/
lemma rowSumEntryCharFunProduct_tendsto_limit
    (Q : Measure Ω') [IsProbabilityMeasure Q] (S : Ω' → ℝ)
    (hS : TendstoInDistribution A.rowSum atTop S (fun _ ↦ P) Q)
    (μS : ProbabilityMeasure ℝ)
    (hμS : μS = ProbabilityMeasure.map ⟨Q, inferInstance⟩ hS.aemeasurable_limit) :
    ∀ t : ℝ,
      Tendsto
        (fun n ↦ ∏ l : Fin (A.rowLength n), charFun (P.map (A n l)) t)
        atTop
        (𝓝 (charFun (μS : Measure ℝ) t)) := by
  intro t
  -- Translate weak convergence of laws into pointwise convergence of characteristic functions.
  have hchar := ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hS.tendsto t
  -- Normalize the row-sum characteristic function into the product form required by Theorem 16.12.
  convert hchar using 1
  · ext n
    simpa using (rowSumLaw_charFun_eq_prod_entryCharFun (A := A) (P := P) n t).symm
  · simpa [hμS] using Measure.map_congr hS.aemeasurable_limit.ae_eq_mk

omit [A.IsIndependent P] in
/-- Helper for Theorem 16.13: the entry characteristic functions are uniformly close to `1` on
compact intervals once the null-array tails are small enough. -/
lemma eventually_entryCharFun_closeTo_one_on_compacts
    (L : ℝ) (hL : 0 < L) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      ∀ t ∈ Set.Icc (-L) L, ∀ l : Fin (A.rowLength n),
        ‖charFun (P.map (A n l)) t - 1‖ ≤ ε := by
  let η : ℝ := ε / (4 * (L + 1))
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have htail :
      ∀ᶠ n in atTop,
        ⨆ i : Fin (A.rowLength n), P {ω | η < |A n i ω|} < ENNReal.ofReal (ε / 4) :=
    (tendsto_order.1
      (RealRandomVariableArray.IsNull.asymptotically_negligible
        (A := A) (μ := P) (ε := η) hη)).2 _ <| by
          positivity
  filter_upwards [htail] with n hn t ht l
  let s : Set Ω := {ω | η < |A n l ω|}
  let f : Ω → ℂ := fun ω ↦ Complex.exp (t * A n l ω * Complex.I) - 1
  have hs : MeasurableSet s := by
    -- Proof comment: the tail event is measurable because each array entry is measurable.
    exact measurableSet_lt measurable_const (A.measurable_entry n l).norm
  have ht_abs : |t| ≤ L := by
    exact abs_le.2 ht
  have hη_eq : (L + 1) * η = ε / 4 := by
    dsimp [η]
    field_simp
  have hgood_const : |t| * η ≤ ε / 4 := by
    have ht_abs' : |t| ≤ L + 1 := by
      linarith
    calc
      |t| * η ≤ (L + 1) * η := by
        gcongr
      _ = ε / 4 := hη_eq
  have htail_real : P.real s ≤ ε / 4 := by
    have htail_lt : P s < ENNReal.ofReal (ε / 4) := by
      simpa [s] using
        (le_iSup (fun i : Fin (A.rowLength n) ↦ P {ω | η < |A n i ω|}) l).trans_lt hn
    exact (ENNReal.toReal_lt_of_lt_ofReal htail_lt).le
  have hpoint_two : ∀ ω, ‖f ω‖ ≤ 2 := by
    intro ω
    -- Proof comment: every oscillatory factor has modulus `1`,
    -- so subtracting `1` costs at most `2`.
    have hnorm_exp : ‖Complex.exp (t * A n l ω * Complex.I)‖ = 1 := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Complex.norm_exp_ofReal_mul_I (t * A n l ω))
    calc
      ‖f ω‖ = ‖Complex.exp (t * A n l ω * Complex.I) - 1‖ := by
        rfl
      _ ≤ ‖Complex.exp (t * A n l ω * Complex.I)‖ + ‖(1 : ℂ)‖ := by
        simpa using norm_sub_le (Complex.exp (t * A n l ω * Complex.I)) (1 : ℂ)
      _ = 2 := by
        rw [hnorm_exp]
        norm_num
  have hgood_point : ∀ ω ∈ sᶜ, ‖f ω‖ ≤ |t| * η := by
    intro ω hω
    -- Proof comment: on the complement of the tail event, `|A n l ω| ≤ η`, so the exponential
    -- defect is controlled by the Lipschitz estimate for `exp (i x)` near the origin.
    have hω_le : |A n l ω| ≤ η := by
      exact le_of_not_gt <| by simpa [s] using hω
    calc
      ‖f ω‖ = ‖Complex.exp (t * A n l ω * Complex.I) - 1‖ := by
        rfl
      _ ≤ |t * A n l ω| := by
        simpa [mul_assoc, mul_left_comm, mul_comm, Real.norm_eq_abs] using
          (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * A n l ω))
      _ = |t| * |A n l ω| := by
        rw [abs_mul]
      _ ≤ |t| * η := by
        gcongr
  have htail_int : ‖∫ ω in s, f ω ∂P‖ ≤ ε / 2 := by
    calc
      ‖∫ ω in s, f ω ∂P‖ ≤ 2 * P.real s := by
        exact
          norm_setIntegral_le_of_norm_le_const
            (μ := P) (s := s) (f := f) (by simp) fun ω _ ↦ hpoint_two ω
      _ ≤ 2 * (ε / 4) := by
        gcongr
      _ = ε / 2 := by
        ring
  have hgood_int : ‖∫ ω in sᶜ, f ω ∂P‖ ≤ ε / 4 := by
    calc
      ‖∫ ω in sᶜ, f ω ∂P‖ ≤ (|t| * η) * P.real sᶜ := by
        exact
          norm_setIntegral_le_of_norm_le_const
            (μ := P) (s := sᶜ) (f := f) (by simp) hgood_point
      _ ≤ (|t| * η) * 1 := by
        gcongr
        exact measureReal_le_one
      _ = |t| * η := by
        ring
      _ ≤ ε / 4 := hgood_const
  have hexp_int : Integrable (fun ω ↦ Complex.exp (t * A n l ω * Complex.I)) P := by
    -- Proof comment: the oscillatory integrand has unit modulus, hence it is integrable.
    have hmeas :
        Measurable (fun ω ↦ Complex.exp (t * A n l ω * Complex.I)) := by
      refine Complex.measurable_exp.comp ?_
      simpa using
        (Complex.measurable_ofReal.comp ((A.measurable_entry n l).const_mul t)).mul_const
          Complex.I
    refine Integrable.of_bound hmeas.aestronglyMeasurable 1 ?_
    exact ae_of_all _ fun ω ↦ by
      have hnorm_exp : ‖Complex.exp (t * A n l ω * Complex.I)‖ = 1 := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (Complex.norm_exp_ofReal_mul_I (t * A n l ω))
      simp [hnorm_exp]
  have hf_int : Integrable f P := by
    exact hexp_int.sub (integrable_const 1)
  have hchar_split :
      charFun (P.map (A n l)) t - 1 = ∫ ω in s, f ω ∂P + ∫ ω in sᶜ, f ω ∂P := by
    -- Proof comment: rewrite the pushforward characteristic function as an integral over `P`,
    -- then split it across the tail event and its complement.
    have hconst : (∫ ω, (1 : ℂ) ∂P) = 1 := by
      simp
    have hkernel_meas :
        AEStronglyMeasurable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I))
          (Measure.map (A n l) P) := by
      refine (Complex.measurable_exp.comp ?_).aestronglyMeasurable
      simpa using (Complex.measurable_ofReal.comp (measurable_const.mul measurable_id)).mul_const
        Complex.I
    rw [MeasureTheory.charFun_apply_real]
    rw [integral_map (A.measurable_entry n l).aemeasurable hkernel_meas]
    rw [← hconst, ← integral_sub hexp_int (integrable_const 1)]
    simpa [f] using (integral_add_compl hs hf_int).symm
  calc
    ‖charFun (P.map (A n l)) t - 1‖
      = ‖∫ ω in s, f ω ∂P + ∫ ω in sᶜ, f ω ∂P‖ := by
          rw [hchar_split]
    _ ≤ ‖∫ ω in s, f ω ∂P‖ + ‖∫ ω in sᶜ, f ω ∂P‖ := by
      exact norm_add_le _ _
    _ ≤ ε / 2 + ε / 4 := by
      gcongr
    _ ≤ ε := by
      linarith

omit [A.IsIndependent P] [A.IsNull P] in
/-- Helper for Theorem 16.13: each row-entry characteristic function is a canonical CFP. -/
lemma rowEntryCharFun_isCFP
    (n : ℕ) (l : Fin (A.rowLength n)) :
    IsCFP (fun t : ℝ ↦ charFun (P.map (A n l)) t) := by
  -- Proof comment: each mapped row-entry law is already a probability measure, so its
  -- characteristic function is a CFP by the owner API.
  simpa using ProbabilityMeasure.isCFP_charFun (ProbabilityMeasure.map ⟨P, inferInstance⟩
    (A.measurable_entry n l).aemeasurable)

/-- Helper for Theorem 16.13: the centered Fourier kernel is integrable against every finite
measure on `ℝ`. -/
lemma integrable_complexExpSubOne (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    Integrable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I) - 1) μ := by
  have hmeas : Measurable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I) - 1) := by
    refine (Complex.measurable_exp.comp ?_).sub measurable_const
    simpa using
      (Complex.measurable_ofReal.comp (measurable_const.mul measurable_id)).mul_const Complex.I
  -- Proof comment: the centered kernel stays uniformly bounded by `2`, so every finite measure
  -- integrates it.
  refine Integrable.of_bound hmeas.aestronglyMeasurable 2 ?_
  exact ae_of_all _ fun x ↦ by
    have hnorm_exp : ‖Complex.exp (t * x * Complex.I)‖ = 1 := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Complex.norm_exp_ofReal_mul_I (t * x))
    calc
      ‖Complex.exp (t * x * Complex.I) - 1‖
          ≤ ‖Complex.exp (t * x * Complex.I)‖ + ‖(1 : ℂ)‖ := by
            simpa using norm_sub_le (Complex.exp (t * x * Complex.I)) (1 : ℂ)
      _ = 2 := by
            rw [hnorm_exp]
            norm_num

/-- Helper for Theorem 16.13: the rowwise compound-Poisson intensity is the finite sum of the
entry laws in the `n`th row. -/
noncomputable def rowIntensity (n : ℕ) : FiniteMeasure ℝ :=
  ∑ l : Fin (A.rowLength n),
    (ProbabilityMeasure.map ⟨P, inferInstance⟩ (A.measurable_entry n l).aemeasurable).toFiniteMeasure

/-- Helper for Theorem 16.13: the rowwise compound-Poisson approximant has the expected
exponential characteristic function. -/
lemma rowCompoundPoisson_charFun_eq_exp_sumEntryCharFunSubOne
    (n : ℕ) (t : ℝ) :
    charFun (compoundPoissonMeasure (rowIntensity (A := A) (P := P) n) : Measure ℝ) t =
      Complex.exp
        (∑ l : Fin (A.rowLength n), (charFun (P.map (A n l)) t - 1)) := by
  -- Proof comment: rewrite the compound-Poisson exponent as the integral of the centered Fourier
  -- kernel against the finite sum of row-entry laws.
  rw [charFun_compoundPoissonMeasure]
  have hsplit :
      ∫ x, (Complex.exp (t * x * Complex.I) - 1) ∂
          ((rowIntensity (A := A) (P := P) n : FiniteMeasure ℝ) : Measure ℝ) =
        ∑ l : Fin (A.rowLength n),
          ∫ x, (Complex.exp (t * x * Complex.I) - 1) ∂
            ((((ProbabilityMeasure.map ⟨P, inferInstance⟩
                (A.measurable_entry n l).aemeasurable).toFiniteMeasure :
                  FiniteMeasure ℝ) : Measure ℝ)) := by
    simpa [rowIntensity] using
      (integral_finset_sum_measure
        (s := Finset.univ)
        (f := fun x : ℝ ↦ Complex.exp (t * x * Complex.I) - 1)
        (μ := fun l : Fin (A.rowLength n) ↦
          ((((ProbabilityMeasure.map ⟨P, inferInstance⟩
              (A.measurable_entry n l).aemeasurable).toFiniteMeasure :
                FiniteMeasure ℝ) : Measure ℝ)))
        (hf := by
          intro l hl
          simpa using
            integrable_complexExpSubOne
              (μ := ((((ProbabilityMeasure.map ⟨P, inferInstance⟩
                  (A.measurable_entry n l).aemeasurable).toFiniteMeasure :
                    FiniteMeasure ℝ) : Measure ℝ)))
              t))
  rw [hsplit]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro l hl
  let νl : ProbabilityMeasure ℝ :=
    ProbabilityMeasure.map ⟨P, inferInstance⟩ (A.measurable_entry n l).aemeasurable
  let μl : Measure ℝ := (νl : Measure ℝ)
  have hkernel : Integrable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I)) μl := by
    -- Proof comment: add back the constant `1` to the centered kernel to recover the usual
    -- Fourier kernel.
    convert (integrable_complexExpSubOne (μ := μl) t).add (integrable_const 1) using 1
    ext x
    simp [μl]
  have hentry :
      ∫ x, (Complex.exp (t * x * Complex.I) - 1) ∂μl = charFun (P.map (A n l)) t - 1 := by
    have hchar :
        ∫ x, Complex.exp (t * x * Complex.I) ∂μl = charFun (P.map (A n l)) t := by
      change ∫ x, Complex.exp (t * x * Complex.I) ∂(νl : Measure ℝ) = charFun (P.map (A n l)) t
      simpa [νl] using (MeasureTheory.charFun_apply_real (μ := (νl : Measure ℝ)) (t := t)).symm
    have hmass : (Measure.map (A n l) P).real Set.univ = 1 := by
      have hprob : IsProbabilityMeasure (Measure.map (A n l) P) :=
        Measure.isProbabilityMeasure_map (A.measurable_entry n l).aemeasurable
      rw [MeasureTheory.isProbabilityMeasure_iff_real] at hprob
      exact hprob
    have hconst : ∫ x, (1 : ℂ) ∂μl = 1 := by
      rw [integral_const]
      change (Measure.map (A n l) P).real Set.univ • (1 : ℂ) = 1
      rw [hmass]
      norm_num
    calc
      ∫ x, (Complex.exp (t * x * Complex.I) - 1) ∂μl
          = ∫ x, Complex.exp (t * x * Complex.I) ∂μl - ∫ x, (1 : ℂ) ∂μl := by
              rw [integral_sub hkernel (integrable_const 1)]
      _ = charFun (P.map (A n l)) t - 1 := by
            rw [hchar, hconst]
  simpa [μl, νl] using hentry

/-- Helper for Theorem 16.13: on the half-ball around `1`, the exact row product rewrites as the
exponential of the sum of the principal logarithms. -/
lemma rowProduct_eq_exp_sumEntryLogs_ofNearOne
    (n : ℕ) (t : ℝ)
    (hnear : ∀ l : Fin (A.rowLength n), ‖charFun (P.map (A n l)) t - 1‖ ≤ 1 / 2) :
    ∏ l : Fin (A.rowLength n), charFun (P.map (A n l)) t =
      Complex.exp (∑ l : Fin (A.rowLength n), Complex.log (charFun (P.map (A n l)) t)) := by
  have hnonzero : ∀ l : Fin (A.rowLength n), charFun (P.map (A n l)) t ≠ 0 := by
    intro l hzero
    have hbad : (1 : ℝ) ≤ 1 / 2 := by
      simpa [hzero] using hnear l
    norm_num at hbad
  -- Proof comment: the half-ball control excludes the origin, so each factor is exactly the
  -- exponential of its principal logarithm.
  rw [Complex.exp_sum]
  refine Finset.prod_congr rfl ?_
  intro l hl
  exact (Complex.exp_log (hnonzero l)).symm

/-- Helper for Theorem 16.13: the same principal-log normalization works for every finite
subproduct of one row once all row entries stay in the half-ball around `1`. -/
lemma rowSubproduct_eq_exp_sumEntryLogs_ofNearOne
    {n : ℕ} (s : Finset (Fin (A.rowLength n))) (t : ℝ)
    (hnear : ∀ l : Fin (A.rowLength n), ‖charFun (P.map (A n l)) t - 1‖ ≤ 1 / 2) :
    Finset.prod s (fun l ↦ charFun (P.map (A n l)) t) =
      Complex.exp (Finset.sum s (fun l ↦ Complex.log (charFun (P.map (A n l)) t))) := by
  have hnonzero : ∀ l : Fin (A.rowLength n), charFun (P.map (A n l)) t ≠ 0 := by
    intro l hzero
    have hbad : (1 : ℝ) ≤ 1 / 2 := by
      simpa [hzero] using hnear l
    norm_num at hbad
  -- Proof comment: the half-ball control excludes the origin for every row factor, so the
  -- principal logarithm exponentiates back termwise on any chosen finite subproduct.
  rw [Complex.exp_sum]
  refine Finset.prod_congr rfl ?_
  intro l hl
  exact (Complex.exp_log (hnonzero l)).symm

omit [A.IsIndependent P] in
/-- Helper for Theorem 16.13: for a fixed frequency, the rowwise supremum of the entry
characteristic-function defects tends to `0`. -/
lemma entryCharFunSubOneSup_tendstoZero
    (t : ℝ) :
    Tendsto
      (fun n ↦ ⨆ l : Fin (A.rowLength n), ‖charFun (P.map (A n l)) t - 1‖)
      atTop
      (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards with n
    have hnonneg :
        0 ≤ ⨆ l : Fin (A.rowLength n), ‖charFun (P.map (A n l)) t - 1‖ := by
      by_cases hempty : IsEmpty (Fin (A.rowLength n))
      · letI := hempty
        simp
      · letI : Nonempty (Fin (A.rowLength n)) := not_isEmpty_iff.mp hempty
        let l0 : Fin (A.rowLength n) := Classical.choice ‹Nonempty (Fin (A.rowLength n))›
        rw [← Finset.sup'_univ_eq_ciSup]
        have hle :
            ‖charFun (P.map (A n l0)) t - 1‖ ≤
              Finset.univ.sup' Finset.univ_nonempty
                (fun l : Fin (A.rowLength n) ↦ ‖charFun (P.map (A n l)) t - 1‖) := by
          exact
            Finset.le_sup' (f := fun l : Fin (A.rowLength n) ↦
              ‖charFun (P.map (A n l)) t - 1‖) (Finset.mem_univ l0)
        exact le_trans (norm_nonneg _) hle
    linarith
  · intro ε hε
    let L : ℝ := |t| + 1
    have hL : 0 < L := by
      dsimp [L]
      positivity
    have ht : t ∈ Set.Icc (-L) L := by
      dsimp [L]
      constructor
      · linarith [neg_le_abs t]
      · linarith [le_abs_self t]
    filter_upwards
      [eventually_entryCharFun_closeTo_one_on_compacts (A := A) (P := P) L hL (ε / 2)
        (by linarith)] with n hn
    have hiSup_le :
        ⨆ l : Fin (A.rowLength n), ‖charFun (P.map (A n l)) t - 1‖ ≤ ε / 2 := by
      by_cases hempty : IsEmpty (Fin (A.rowLength n))
      · letI := hempty
        simp
        positivity
      · letI : Nonempty (Fin (A.rowLength n)) := not_isEmpty_iff.mp hempty
        rw [← Finset.sup'_univ_eq_ciSup]
        exact Finset.sup'_le Finset.univ_nonempty _ fun l _ ↦ hn t ht l
    linarith

/-- Helper for Theorem 16.13: the full row product is always a characteristic-function value of
norm at most `1`. -/
lemma rowProduct_norm_le_one
    (n : ℕ) (t : ℝ) :
    ‖∏ l : Fin (A.rowLength n), charFun (P.map (A n l)) t‖ ≤ 1 := by
  -- Proof comment: the full row product is the characteristic function of the `n`th row sum law.
  simpa [A.rowSumLaw_toMeasure P n,
    rowSumLaw_charFun_eq_prod_entryCharFun (A := A) (P := P) n t] using
    (MeasureTheory.norm_charFun_le_one (μ := (A.rowSumLaw P n : Measure ℝ)) t)

/-- Helper for Theorem 16.13: the principal-log sum of one row lies in the closed left half-plane
whenever every entry characteristic function stays in the half-ball around `1`. -/
lemma rowLogSum_re_nonpos_ofNearOne
    (n : ℕ) (t : ℝ)
    (hnear : ∀ l : Fin (A.rowLength n), ‖charFun (P.map (A n l)) t - 1‖ ≤ 1 / 2) :
    (∑ l : Fin (A.rowLength n), Complex.log (charFun (P.map (A n l)) t)).re ≤ 0 := by
  have hnorm :
      ‖Complex.exp (∑ l : Fin (A.rowLength n), Complex.log (charFun (P.map (A n l)) t))‖ ≤ 1 := by
    simpa [rowProduct_eq_exp_sumEntryLogs_ofNearOne (A := A) (P := P) n t hnear] using
      rowProduct_norm_le_one (A := A) (P := P) n t
  have hExp : Real.exp
      ((∑ l : Fin (A.rowLength n), Complex.log (charFun (P.map (A n l)) t)).re) ≤ 1 := by
    simpa [Complex.norm_exp] using hnorm
  exact (Real.exp_le_one_iff).1 hExp

section PointwiseColoring

variable {E : Type*} [NormedAddCommGroup E]

/-- Helper for Theorem 16.13: the `j`th block of a fixed row coloring is the corresponding color
class in that row. -/
def colorClassBlock {n : ℕ} (m : ℕ+) (c : Fin (A.rowLength n) → Fin m) (j : Fin m) :
    Finset (Fin (A.rowLength n)) :=
  Finset.univ.filter fun l ↦ c l = j

/-- Helper for Theorem 16.13: distinct color classes of one coloring are pairwise disjoint. -/
lemma pairwiseDisjoint_colorClassBlock {n : ℕ} (m : ℕ+) (c : Fin (A.rowLength n) → Fin m) :
    Pairwise
      (fun i j ↦
        Disjoint (colorClassBlock (A := A) m c i) (colorClassBlock (A := A) m c j)) := by
  intro i j hij
  -- Proof comment: one row index cannot simultaneously carry two different colors.
  refine Finset.disjoint_left.2 ?_
  intro l hli hlj
  have hi : c l = i := (Finset.mem_filter.1 hli).2
  have hj : c l = j := (Finset.mem_filter.1 hlj).2
  exact hij (hi.symm.trans hj)

/-- Helper for Theorem 16.13: the color classes of one coloring cover the full row index set. -/
lemma biUnion_colorClassBlock_eq_univ {n : ℕ} (m : ℕ+) (c : Fin (A.rowLength n) → Fin m) :
    Finset.biUnion Finset.univ (colorClassBlock (A := A) m c) =
      (Finset.univ : Finset (Fin (A.rowLength n))) := by
  classical
  ext l
  -- Proof comment: every row index belongs to the unique block labelled by its assigned color.
  simp [colorClassBlock]

/-- Helper for Theorem 16.13: summing over the color classes of one coloring recovers the full
row sum. -/
lemma colorClassBlock_sum_eq_rowSum
    {n : ℕ} (m : ℕ+) (v : Fin (A.rowLength n) → E) (c : Fin (A.rowLength n) → Fin m) :
    Finset.sum Finset.univ (fun j : Fin m ↦
      Finset.sum (colorClassBlock (A := A) m c j) v) =
      Finset.sum Finset.univ v := by
  have hdisj' :
      Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin m)))
        (colorClassBlock (A := A) m c) := by
    intro i hi j hj hij
    exact pairwiseDisjoint_colorClassBlock (A := A) m c hij
  -- Proof comment: `Finset.sum_biUnion` collapses the blockwise partition back to the full row.
  calc
    Finset.sum Finset.univ (fun j : Fin m ↦ Finset.sum (colorClassBlock (A := A) m c j) v)
        = Finset.sum (Finset.biUnion Finset.univ (colorClassBlock (A := A) m c)) v := by
          symm
          exact Finset.sum_biUnion hdisj'
    _ = Finset.sum Finset.univ v := by
          simp [biUnion_colorClassBlock_eq_univ (A := A) m c]

/-- Helper for Theorem 16.13: multiplying over the color classes of one coloring recovers the full
row product. -/
lemma colorClassBlock_prod_eq_rowProduct
    {n : ℕ} (m : ℕ+) {β : Type*} [CommMonoid β]
    (z : Fin (A.rowLength n) → β) (c : Fin (A.rowLength n) → Fin m) :
    Finset.prod Finset.univ (fun j : Fin m ↦
      Finset.prod (colorClassBlock (A := A) m c j) z) =
      Finset.prod Finset.univ z := by
  have hdisj' :
      Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin m)))
        (colorClassBlock (A := A) m c) := by
    intro i hi j hj hij
    exact pairwiseDisjoint_colorClassBlock (A := A) m c hij
  -- Proof comment: `Finset.prod_biUnion` gives the multiplicative factorization over the
  -- partition blocks, and the cover lemma identifies the union with the whole row.
  calc
    Finset.prod Finset.univ (fun j : Fin m ↦ Finset.prod (colorClassBlock (A := A) m c j) z)
        = Finset.prod (Finset.biUnion Finset.univ (colorClassBlock (A := A) m c)) z := by
          symm
          exact Finset.prod_biUnion hdisj'
    _ = Finset.prod Finset.univ z := by
          simp [biUnion_colorClassBlock_eq_univ (A := A) m c]

/-- Helper for Theorem 16.13: the fixed-frequency discrepancy of a coloring is the largest
pairwise block-sum gap in one row. -/
noncomputable def pointwiseColoringDiscrepancy {n : ℕ} (m : ℕ+)
    (v : Fin (A.rowLength n) → E) (c : Fin (A.rowLength n) → Fin m) : ℝ :=
  ↑(Finset.univ.sup fun j : Fin m ↦
    Finset.univ.sup fun j' : Fin m ↦
      ‖Finset.sum (colorClassBlock (A := A) m c j) v -
          Finset.sum (colorClassBlock (A := A) m c j') v‖₊)

/-- Helper for Theorem 16.13: finite search over all colorings produces one minimizing the
pointwise discrepancy. -/
lemma existsMinimizingPointwiseColoring {n : ℕ} (m : ℕ+) (v : Fin (A.rowLength n) → E) :
    ∃ c : Fin (A.rowLength n) → Fin m,
      ∀ c' : Fin (A.rowLength n) → Fin m,
        pointwiseColoringDiscrepancy (A := A) m v c ≤
          pointwiseColoringDiscrepancy (A := A) m v c' := by
  classical
  obtain ⟨c, _hcMem, hcMin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin (A.rowLength n) → Fin m))
      (pointwiseColoringDiscrepancy (A := A) m v) ⟨fun _ ↦ 0, by simp⟩
  refine ⟨c, ?_⟩
  intro c'
  -- Proof comment: the finite function space of row colorings is the search space for the
  -- minimizer, so every recoloring candidate is dominated by the chosen one.
  exact hcMin c' (by simp)

/-- Helper for Theorem 16.13: a pointwise discrepancy minimizer is no worse than any one-point
recoloring. -/
lemma minimizingPointwiseColoring_recolorControl
    {n : ℕ} {m : ℕ+} {v : Fin (A.rowLength n) → E} {c : Fin (A.rowLength n) → Fin m}
    (hmin :
      ∀ c' : Fin (A.rowLength n) → Fin m,
        pointwiseColoringDiscrepancy (A := A) m v c ≤
          pointwiseColoringDiscrepancy (A := A) m v c')
    (a : Fin (A.rowLength n)) (j' : Fin m) :
    pointwiseColoringDiscrepancy (A := A) m v c ≤
      pointwiseColoringDiscrepancy (A := A) m v (Function.update c a j') := by
  -- Proof comment: a one-point recoloring is just another point in the finite coloring space.
  exact hmin (Function.update c a j')

/-- Helper for Theorem 16.13: recoloring one row index only erases that index from every old
color class and reinserts it into the new one. -/
lemma colorClassBlock_update_eq
    {n : ℕ} (m : ℕ+) (c : Fin (A.rowLength n) → Fin m) (a : Fin (A.rowLength n))
    (j j' : Fin m) :
    colorClassBlock (A := A) m (Function.update c a j') j =
      if j = j' then insert a ((colorClassBlock (A := A) m c j).erase a)
      else (colorClassBlock (A := A) m c j).erase a := by
  classical
  ext l
  by_cases hla : l = a
  · subst hla
    by_cases hj : j = j'
    · simp [colorClassBlock, Function.update, hj]
    · simp [colorClassBlock, Function.update, hj, eq_comm]
  · by_cases hj : j = j'
    · simp [colorClassBlock, Function.update, hla, hj]
    · simp [colorClassBlock, Function.update, hla, hj]

/-- Helper for Theorem 16.13: after recoloring one row index, the `j`th block sum changes only by
the loss or gain of the recolored vector. -/
lemma colorClassBlockSum_update
    {n : ℕ} (m : ℕ+) (v : Fin (A.rowLength n) → E) (c : Fin (A.rowLength n) → Fin m)
    (a : Fin (A.rowLength n)) (j j' : Fin m) :
    Finset.sum (colorClassBlock (A := A) m (Function.update c a j') j) v =
      Finset.sum (colorClassBlock (A := A) m c j) v +
        (if j = j' then v a else 0) -
        (if c a = j then v a else 0) := by
  classical
  let B : Finset (Fin (A.rowLength n)) := colorClassBlock (A := A) m c j
  let f : Fin (A.rowLength n) → E := v
  by_cases hj : j = j'
  · subst hj
    by_cases hca : c a = j
    · have haB : a ∈ B := by
        simpa [B, colorClassBlock] using hca
      have hnew :
          Finset.sum (colorClassBlock (A := A) m (Function.update c a j) j) f =
            f a + Finset.sum (B.erase a) f := by
        rw [colorClassBlock_update_eq, if_pos rfl]
        simpa [B] using
          (Finset.sum_insert (s := B.erase a) (a := a) (f := f) (Finset.notMem_erase a B))
      -- Proof comment: if the recolored index already belonged to the target block, the new and
      -- old sums share the same `erase/insert` decomposition.
      calc
        Finset.sum (colorClassBlock (A := A) m (Function.update c a j) j) f
            = f a + Finset.sum (B.erase a) f := hnew
        _ = Finset.sum B f := by
              simpa [B, f, add_comm] using (B.sum_erase_add f haB)
        _ = Finset.sum B f + (if j = j then v a else 0) - (if c a = j then v a else 0) := by
              simp [f, hca]
    · have haB : a ∉ B := by
        simpa [B, colorClassBlock] using hca
      have hnew :
          Finset.sum (colorClassBlock (A := A) m (Function.update c a j) j) f =
            f a + Finset.sum B f := by
        rw [colorClassBlock_update_eq, if_pos rfl, Finset.erase_eq_of_notMem haB]
        simpa using (Finset.sum_insert (s := B) (a := a) (f := f) haB)
      -- Proof comment: if the old block did not contain the recolored index, the new block sum
      -- is exactly the old sum plus the inserted term.
      calc
        Finset.sum (colorClassBlock (A := A) m (Function.update c a j) j) f
            = f a + Finset.sum B f := hnew
        _ = Finset.sum B f + (if j = j then v a else 0) - (if c a = j then v a else 0) := by
              simp [f, hca, add_comm]
  · by_cases hca : c a = j
    · have haB : a ∈ B := by
        simpa [B, colorClassBlock] using hca
      have hsumB : Finset.sum B f = Finset.sum (B.erase a) f + f a := by
        simpa [B, f, add_comm] using (B.sum_erase_add f haB).symm
      -- Proof comment: if the recolored index leaves the `j`th block, the new block sum is the
      -- erased old sum, so the correction subtracts exactly `v a`.
      calc
        Finset.sum (colorClassBlock (A := A) m (Function.update c a j') j) f
            = Finset.sum (B.erase a) f := by
                rw [colorClassBlock_update_eq, if_neg hj]
        _ = Finset.sum B f + (if j = j' then v a else 0) - (if c a = j then v a else 0) := by
              rw [hsumB]
              simp [f, hj, hca]
    · have haB : a ∉ B := by
        simpa [B, colorClassBlock] using hca
      -- Proof comment: if the recolored index belonged to neither relevant block, nothing
      -- changes in the `j`th block sum.
      calc
        Finset.sum (colorClassBlock (A := A) m (Function.update c a j') j) f
            = Finset.sum (B.erase a) f := by
                rw [colorClassBlock_update_eq, if_neg hj]
        _ = Finset.sum B f := by
              simpa [Finset.erase_eq_of_notMem haB]
        _ = Finset.sum B f + (if j = j' then v a else 0) - (if c a = j then v a else 0) := by
              simp [f, hj, hca]

/-- Helper for Theorem 16.13: the correction term from a one-point recoloring has norm bounded by
the norm of the recolored vector. -/
lemma colorClassBlockSum_updateCorrection_norm_le
    {n : ℕ} (m : ℕ+) (v : Fin (A.rowLength n) → E) (c : Fin (A.rowLength n) → Fin m)
    (a : Fin (A.rowLength n)) (j j' : Fin m) {ρ : ℝ}
    (ha : ‖v a‖ ≤ ρ) :
    ‖(if j = j' then v a else 0) - (if c a = j then v a else 0)‖ ≤ ρ := by
  have hρ : 0 ≤ ρ := le_trans (norm_nonneg _) ha
  -- Proof comment: the correction term is always one of `0`, `v a`, or `-v a`.
  by_cases hj' : j = j'
  · subst hj'
    by_cases hj : c a = j
    · simp [hj, hρ]
    · simpa [hj] using ha
  · by_cases hj : c a = j
    · simpa [hj', hj, norm_neg] using ha
    · simp [hj', hj, hρ]

/-- Helper for Theorem 16.13: recoloring one row index changes any fixed pairwise block-sum gap
by at most `2 * ρ`. -/
lemma pointwiseColoringDiscrepancyUpdateBound
    {n : ℕ} (m : ℕ+) (v : Fin (A.rowLength n) → E) (c : Fin (A.rowLength n) → Fin m)
    (a : Fin (A.rowLength n)) (j j' jnew : Fin m) {ρ : ℝ}
    (ha : ‖v a‖ ≤ ρ) :
    ‖Finset.sum (colorClassBlock (A := A) m (Function.update c a jnew) j) v -
        Finset.sum (colorClassBlock (A := A) m (Function.update c a jnew) j') v‖ ≤
      ‖Finset.sum (colorClassBlock (A := A) m c j) v -
          Finset.sum (colorClassBlock (A := A) m c j') v‖ +
        2 * ρ := by
  let oldj := Finset.sum (colorClassBlock (A := A) m c j) v
  let oldj' := Finset.sum (colorClassBlock (A := A) m c j') v
  let δj : E := (if j = jnew then v a else 0) - (if c a = j then v a else 0)
  let δj' : E := (if j' = jnew then v a else 0) - (if c a = j' then v a else 0)
  have hnewj :
      Finset.sum (colorClassBlock (A := A) m (Function.update c a jnew) j) v = oldj + δj := by
    -- Proof comment: normalize the updated `j`th block sum into its old value plus one local
    -- correction term.
    calc
      Finset.sum (colorClassBlock (A := A) m (Function.update c a jnew) j) v
          = oldj + (if j = jnew then v a else 0) - (if c a = j then v a else 0) := by
              simpa [oldj] using colorClassBlockSum_update (A := A) m v c a j jnew
      _ = oldj + δj := by
            simp [δj, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hnewj' :
      Finset.sum (colorClassBlock (A := A) m (Function.update c a jnew) j') v = oldj' + δj' := by
    -- Proof comment: the second updated block sum has the same one-correction normal form.
    calc
      Finset.sum (colorClassBlock (A := A) m (Function.update c a jnew) j') v
          = oldj' + (if j' = jnew then v a else 0) - (if c a = j' then v a else 0) := by
              simpa [oldj'] using colorClassBlockSum_update (A := A) m v c a j' jnew
      _ = oldj' + δj' := by
            simp [δj', sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hδj : ‖δj‖ ≤ ρ := by
    -- Proof comment: each individual correction is bounded by the same `ρ` budget.
    simpa [δj] using colorClassBlockSum_updateCorrection_norm_le (A := A) m v c a j jnew ha
  have hδj' : ‖δj'‖ ≤ ρ := by
    -- Proof comment: the same one-point bound applies to the second correction.
    simpa [δj'] using colorClassBlockSum_updateCorrection_norm_le (A := A) m v c a j' jnew ha
  have hδpair : ‖δj - δj'‖ ≤ 2 * ρ := by
    -- Proof comment: the difference of two `ρ`-bounded corrections is bounded by `2 * ρ`.
    have htri : ‖δj - δj'‖ ≤ ‖δj‖ + ‖δj'‖ := norm_sub_le _ _
    linarith
  have hrewrite : (oldj + δj) - (oldj' + δj') = (oldj - oldj') + (δj - δj') := by
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  -- Proof comment: rewrite the new gap as the old gap plus the pair of correction terms, then
  -- absorb those corrections into the universal `2 * ρ` budget.
  calc
    ‖Finset.sum (colorClassBlock (A := A) m (Function.update c a jnew) j) v -
        Finset.sum (colorClassBlock (A := A) m (Function.update c a jnew) j') v‖
        = ‖(oldj - oldj') + (δj - δj')‖ := by
            rw [hnewj, hnewj', hrewrite]
    _ ≤ ‖oldj - oldj'‖ + ‖δj - δj'‖ := norm_add_le _ _
    _ ≤ ‖oldj - oldj'‖ + 2 * ρ := by linarith

/-- Helper for Theorem 16.13: on one fixed row, the pointwise discrepancy supremum is attained by
some pair of color classes. -/
lemma existsPointwiseColoringDiscrepancyWitness
    {n : ℕ} (m : ℕ+) (v : Fin (A.rowLength n) → E) (c : Fin (A.rowLength n) → Fin m) :
    ∃ j j' : Fin m,
      pointwiseColoringDiscrepancy (A := A) m v c =
        ‖Finset.sum (colorClassBlock (A := A) m c j) v -
            Finset.sum (colorClassBlock (A := A) m c j') v‖ := by
  have hm : (Finset.univ : Finset (Fin m)).Nonempty := Finset.univ_nonempty
  obtain ⟨j, _hjmem, hj⟩ :=
    Finset.exists_mem_eq_sup (s := Finset.univ) hm
      (fun j : Fin m ↦
        Finset.univ.sup fun j' : Fin m ↦
          ‖Finset.sum (colorClassBlock (A := A) m c j) v -
              Finset.sum (colorClassBlock (A := A) m c j') v‖₊)
  obtain ⟨j', _hj'mem, hj'⟩ :=
    Finset.exists_mem_eq_sup (s := Finset.univ) hm
      (fun j' : Fin m ↦
        ‖Finset.sum (colorClassBlock (A := A) m c j) v -
            Finset.sum (colorClassBlock (A := A) m c j') v‖₊)
  -- Proof comment: the discrepancy is a nested finite supremum over the color pairs, so some
  -- pair attains it exactly.
  exact ⟨j, j', by simpa [pointwiseColoringDiscrepancy, hj, hj']⟩

/-- Helper for Theorem 16.13: every concrete pairwise block-sum gap is bounded by the full
pointwise discrepancy of the underlying coloring. -/
lemma blockSumGap_le_pointwiseColoringDiscrepancy
    {n : ℕ} (m : ℕ+) (v : Fin (A.rowLength n) → E)
    (c : Fin (A.rowLength n) → Fin m) (j j' : Fin m) :
    ‖Finset.sum (colorClassBlock (A := A) m c j) v -
        Finset.sum (colorClassBlock (A := A) m c j') v‖ ≤
      pointwiseColoringDiscrepancy (A := A) m v c := by
  let D : NNReal :=
    Finset.univ.sup fun i : Fin m ↦
      Finset.univ.sup fun i' : Fin m ↦
        ‖Finset.sum (colorClassBlock (A := A) m c i) v -
            Finset.sum (colorClassBlock (A := A) m c i') v‖₊
  have hj'Sup :
      ‖Finset.sum (colorClassBlock (A := A) m c j) v -
          Finset.sum (colorClassBlock (A := A) m c j') v‖₊ ≤
        Finset.univ.sup fun i' : Fin m ↦
          ‖Finset.sum (colorClassBlock (A := A) m c j) v -
              Finset.sum (colorClassBlock (A := A) m c i') v‖₊ := by
    exact Finset.le_sup (s := (Finset.univ : Finset (Fin m)))
      (f := fun i' : Fin m ↦
        ‖Finset.sum (colorClassBlock (A := A) m c j) v -
            Finset.sum (colorClassBlock (A := A) m c i') v‖₊) (by
      show j' ∈ (Finset.univ : Finset (Fin m))
      simp)
  have hjSup :
      Finset.univ.sup (fun i' : Fin m ↦
        ‖Finset.sum (colorClassBlock (A := A) m c j) v -
            Finset.sum (colorClassBlock (A := A) m c i') v‖₊) ≤
        D := by
    exact Finset.le_sup (s := (Finset.univ : Finset (Fin m)))
      (f := fun i : Fin m ↦
        Finset.univ.sup fun i' : Fin m ↦
          ‖Finset.sum (colorClassBlock (A := A) m c i) v -
              Finset.sum (colorClassBlock (A := A) m c i') v‖₊) (by
      show j ∈ (Finset.univ : Finset (Fin m))
      simp)
  have hleNN :
      ‖Finset.sum (colorClassBlock (A := A) m c j) v -
          Finset.sum (colorClassBlock (A := A) m c j') v‖₊ ≤
        D := by
    exact le_trans hj'Sup hjSup
  -- Proof comment: the concrete block pair is one entry in the nested finite supremum defining
  -- the discrepancy.
  simpa [pointwiseColoringDiscrepancy, D] using
    (show (‖Finset.sum (colorClassBlock (A := A) m c j) v -
        Finset.sum (colorClassBlock (A := A) m c j') v‖₊ : ℝ) ≤
        (D : ℝ) from by
          exact_mod_cast hleNN)

/-- Helper for Theorem 16.13: recoloring one row index increases the pointwise discrepancy by at
most `2 * ρ`. -/
lemma pointwiseColoringDiscrepancy_update_le
    {n : ℕ} (m : ℕ+) (v : Fin (A.rowLength n) → E) (c : Fin (A.rowLength n) → Fin m)
    (a : Fin (A.rowLength n)) (jnew : Fin m) {ρ : ℝ}
    (ha : ‖v a‖ ≤ ρ) :
    pointwiseColoringDiscrepancy (A := A) m v (Function.update c a jnew) ≤
      pointwiseColoringDiscrepancy (A := A) m v c + 2 * ρ := by
  rcases
      existsPointwiseColoringDiscrepancyWitness
        (A := A) (m := m) (v := v) (c := Function.update c a jnew) with
    ⟨j, j', hwit⟩
  rw [hwit]
  -- Proof comment: witness the updated discrepancy by one concrete extremal block pair, control
  -- that pair by the one-point update estimate, and then absorb the old pair into the original
  -- discrepancy supremum.
  have hupdate :
      ‖Finset.sum (colorClassBlock (A := A) m (Function.update c a jnew) j) v -
          Finset.sum (colorClassBlock (A := A) m (Function.update c a jnew) j') v‖ ≤
        ‖Finset.sum (colorClassBlock (A := A) m c j) v -
            Finset.sum (colorClassBlock (A := A) m c j') v‖ +
          2 * ρ := by
    exact pointwiseColoringDiscrepancyUpdateBound (A := A) m v c a j j' jnew ha
  have hold :
      ‖Finset.sum (colorClassBlock (A := A) m c j) v -
          Finset.sum (colorClassBlock (A := A) m c j') v‖ +
        2 * ρ ≤
      pointwiseColoringDiscrepancy (A := A) m v c + 2 * ρ := by
    gcongr
    exact blockSumGap_le_pointwiseColoringDiscrepancy (A := A) m v c j j'
  exact le_trans hupdate hold

/-- Helper for Theorem 16.13: updating a finite family of row indices to prescribed target colors
increases the pointwise discrepancy by at most `2 * s.card * ρ`. -/
lemma pointwiseColoringDiscrepancy_updateOn_le
    {n : ℕ} (m : ℕ+) (v : Fin (A.rowLength n) → E)
    (c c' : Fin (A.rowLength n) → Fin m) {ρ : ℝ}
    (hbound : ∀ a : Fin (A.rowLength n), ‖v a‖ ≤ ρ)
    (s : Finset (Fin (A.rowLength n))) :
    pointwiseColoringDiscrepancy (A := A) m v (fun a ↦ if a ∈ s then c' a else c a) ≤
      pointwiseColoringDiscrepancy (A := A) m v c + 2 * (s.card : ℝ) * ρ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- Proof comment: with no prescribed recolorings, the coloring is unchanged and the budget
      -- is zero.
      simp
  | @insert a s ha ih =>
      let cs : Fin (A.rowLength n) → Fin m := fun b ↦ if b ∈ s then c' b else c b
      have hstep :
          pointwiseColoringDiscrepancy (A := A) m v
              (fun b ↦ if b ∈ insert a s then c' b else c b) ≤
            pointwiseColoringDiscrepancy (A := A) m v cs + 2 * ρ := by
        have hEq :
            (fun b ↦ if b ∈ insert a s then c' b else c b) =
              Function.update cs a (c' a) := by
          funext b
          by_cases hb : b = a
          · subst hb
            simp [cs, ha]
          · simp [cs, ha, hb]
        -- Proof comment: peel off the fresh recoloring at `a` and apply the one-point estimate to
        -- the coloring already updated on `s`.
        rw [hEq]
        exact pointwiseColoringDiscrepancy_update_le (A := A) m v cs a (c' a) (hbound a)
      have htail :
          pointwiseColoringDiscrepancy (A := A) m v cs ≤
            pointwiseColoringDiscrepancy (A := A) m v c + 2 * (s.card : ℝ) * ρ := by
        simpa [cs] using ih
      have hcard : ((insert a s).card : ℝ) = (s.card : ℝ) + 1 := by
        simp [ha]
      -- Proof comment: add the fresh `2 * ρ` recoloring cost to the induction hypothesis and
      -- rewrite the total budget using the enlarged finite update set.
      calc
        pointwiseColoringDiscrepancy (A := A) m v (fun b ↦ if b ∈ insert a s then c' b else c b) ≤
            pointwiseColoringDiscrepancy (A := A) m v cs + 2 * ρ := hstep
        _ ≤ pointwiseColoringDiscrepancy (A := A) m v c + 2 * (s.card : ℝ) * ρ + 2 * ρ := by
            linarith
        _ = pointwiseColoringDiscrepancy (A := A) m v c +
              2 * ((insert a s).card : ℝ) * ρ := by
            rw [hcard]
            ring

/-- Helper for Theorem 16.13: any comparison coloring differs from the current coloring only on
its finite disagreement set, so the discrepancy cost is controlled by the size of that set. -/
lemma pointwiseColoringDiscrepancy_compare_le_of_disagreementCard
    {n : ℕ} (m : ℕ+) (v : Fin (A.rowLength n) → E)
    (c c' : Fin (A.rowLength n) → Fin m) {ρ : ℝ}
    (hbound : ∀ a : Fin (A.rowLength n), ‖v a‖ ≤ ρ) :
    pointwiseColoringDiscrepancy (A := A) m v c' ≤
      pointwiseColoringDiscrepancy (A := A) m v c +
        2 * ((((Finset.univ : Finset (Fin (A.rowLength n))).filter fun a ↦ c a ≠ c' a).card : ℝ)) *
          ρ := by
  classical
  let s : Finset (Fin (A.rowLength n)) :=
    (Finset.univ : Finset (Fin (A.rowLength n))).filter fun a ↦ c a ≠ c' a
  have hs :
      (fun a ↦ if a ∈ s then c' a else c a) = c' := by
    funext a
    by_cases ha : a ∈ s
    · simp [ha]
    · have hEq : c a = c' a := by
        by_contra hneq
        exact ha (by simp [s, hneq])
      simp [ha, hEq]
  have hupdate :
      pointwiseColoringDiscrepancy (A := A) m v (fun a ↦ if a ∈ s then c' a else c a) ≤
        pointwiseColoringDiscrepancy (A := A) m v c + 2 * (s.card : ℝ) * ρ := by
    exact pointwiseColoringDiscrepancy_updateOn_le (A := A) m v c c' hbound s
  have hsDisc :
      pointwiseColoringDiscrepancy (A := A) m v c' =
        pointwiseColoringDiscrepancy (A := A) m v (fun a ↦ if a ∈ s then c' a else c a) := by
    simpa [hs]
  -- Proof comment: update exactly the disagreement set; away from that finite set the two
  -- colorings already agree, so the multi-point recoloring bound applies verbatim.
  calc
    pointwiseColoringDiscrepancy (A := A) m v c' =
        pointwiseColoringDiscrepancy (A := A) m v (fun a ↦ if a ∈ s then c' a else c a) := by
          exact hsDisc
    _ ≤ pointwiseColoringDiscrepancy (A := A) m v c + 2 * (s.card : ℝ) * ρ := hupdate
    _ =
        pointwiseColoringDiscrepancy (A := A) m v c +
          2 *
              ((((Finset.univ : Finset (Fin (A.rowLength n))).filter fun a ↦ c a ≠ c' a).card :
                ℝ)) *
            ρ := by
          rfl

end PointwiseColoring

/-- Helper for Theorem 16.13: the projected block sum along a fixed scalar direction is the real
part of the corresponding complex block sum. -/
lemma projectedColorClassBlockSum_eq
    {n : ℕ} (m : ℕ+) (v : Fin (A.rowLength n) → ℂ)
    (c : Fin (A.rowLength n) → Fin m) (j : Fin m) (ω : ℂ) :
    Complex.re (ω * Finset.sum (colorClassBlock (A := A) m c j) v) =
      Finset.sum (colorClassBlock (A := A) m c j) (fun l ↦ Complex.re (ω * v l)) := by
  -- Proof comment: distribute the fixed scalar through the finite sum and then pass `Complex.re`
  -- termwise through that sum.
  rw [Finset.mul_sum, Complex.re_sum]

/-- Helper for Theorem 16.13: once a pointwise discrepancy witness is normalized by a unit
complex scalar, every projected block sum lies between the witness endpoints. -/
lemma witnessProjectedColorClassBlockSums_between
    {n : ℕ} (m : ℕ+) (v : Fin (A.rowLength n) → ℂ)
    (c : Fin (A.rowLength n) → Fin m) {jMax jMin i : Fin m} {ω : ℂ}
    (hω : ‖ω‖ = 1)
    (_hgap :
      pointwiseColoringDiscrepancy (A := A) m v c =
        ‖Finset.sum (colorClassBlock (A := A) m c jMax) v -
            Finset.sum (colorClassBlock (A := A) m c jMin) v‖)
    (hωgap :
      Complex.re
          (ω *
            (Finset.sum (colorClassBlock (A := A) m c jMax) v -
              Finset.sum (colorClassBlock (A := A) m c jMin) v)) =
        pointwiseColoringDiscrepancy (A := A) m v c) :
    Complex.re (ω * Finset.sum (colorClassBlock (A := A) m c jMin) v) ≤
      Complex.re (ω * Finset.sum (colorClassBlock (A := A) m c i) v) ∧
    Complex.re (ω * Finset.sum (colorClassBlock (A := A) m c i) v) ≤
      Complex.re (ω * Finset.sum (colorClassBlock (A := A) m c jMax) v) := by
  let s : Fin m → ℂ := fun j ↦ Finset.sum (colorClassBlock (A := A) m c j) v
  have hiMin :
      ‖s i - s jMin‖ ≤ pointwiseColoringDiscrepancy (A := A) m v c := by
    -- Proof comment: every concrete block pair is bounded by the full pointwise discrepancy.
    simpa [s] using
      blockSumGap_le_pointwiseColoringDiscrepancy (A := A) m v c i jMin
  have hiMax :
      ‖s jMax - s i‖ ≤ pointwiseColoringDiscrepancy (A := A) m v c := by
    -- Proof comment: the same pointwise discrepancy bound applies to the witness upper block.
    simpa [s] using
      blockSumGap_le_pointwiseColoringDiscrepancy (A := A) m v c jMax i
  have hReMin :
      Complex.re (ω * (s i - s jMin)) ≤ pointwiseColoringDiscrepancy (A := A) m v c := by
    have habs :
        |Complex.re (ω * (s i - s jMin))| ≤
          ‖ω * (s i - s jMin)‖ := Complex.abs_re_le_norm (ω * (s i - s jMin))
    have hnormω :
        ‖ω * (s i - s jMin)‖ = ‖s i - s jMin‖ := by
      calc
        ‖ω * (s i - s jMin)‖ = ‖ω‖ * ‖s i - s jMin‖ := norm_mul _ _
        _ = ‖s i - s jMin‖ := by simp [hω]
    have hleAbs :
        Complex.re (ω * (s i - s jMin)) ≤ |Complex.re (ω * (s i - s jMin))| := by
      exact le_abs_self _
    exact le_trans (le_trans hleAbs habs) (by
      rw [hnormω]
      exact hiMin)
  have hReMax :
      Complex.re (ω * (s jMax - s i)) ≤ pointwiseColoringDiscrepancy (A := A) m v c := by
    have habs :
        |Complex.re (ω * (s jMax - s i))| ≤
          ‖ω * (s jMax - s i)‖ := Complex.abs_re_le_norm (ω * (s jMax - s i))
    have hnormω :
        ‖ω * (s jMax - s i)‖ = ‖s jMax - s i‖ := by
      calc
        ‖ω * (s jMax - s i)‖ = ‖ω‖ * ‖s jMax - s i‖ := norm_mul _ _
        _ = ‖s jMax - s i‖ := by simp [hω]
    have hleAbs :
        Complex.re (ω * (s jMax - s i)) ≤ |Complex.re (ω * (s jMax - s i))| := by
      exact le_abs_self _
    exact le_trans (le_trans hleAbs habs) (by
      rw [hnormω]
      exact hiMax)
  have hupper :
      Complex.re (ω * s i) ≤ Complex.re (ω * s jMax) := by
    have hlinWitness :
        Complex.re (ω * (s jMax - s jMin)) =
          Complex.re (ω * s jMax) - Complex.re (ω * s jMin) := by
      simp [sub_eq_add_neg, mul_add]
    have hlinMid :
        Complex.re (ω * (s i - s jMin)) =
          Complex.re (ω * s i) - Complex.re (ω * s jMin) := by
      simp [sub_eq_add_neg, mul_add]
    have hωgap' := hωgap
    rw [hlinWitness] at hωgap'
    rw [hlinMid] at hReMin
    -- Proof comment: the witness gap is exactly the endpoint difference, and every intermediate
    -- block differs from the lower endpoint by at most that same gap.
    linarith
  have hlower :
      Complex.re (ω * s jMin) ≤ Complex.re (ω * s i) := by
    have hlin :
        Complex.re (ω * (s jMax - s i)) =
          Complex.re (ω * s jMax) - Complex.re (ω * s i) := by
      simp [sub_eq_add_neg, mul_add]
    rw [hlin] at hReMax
    have hlinWitness :
        Complex.re (ω * (s jMax - s jMin)) =
          Complex.re (ω * s jMax) - Complex.re (ω * s jMin) := by
      simp [sub_eq_add_neg, mul_add]
    have hgap' :
        Complex.re (ω * (s jMax - s jMin)) =
          pointwiseColoringDiscrepancy (A := A) m v c := by
      simpa [s] using hωgap
    rw [hlinWitness] at hgap'
    linarith
  simpa [s] using And.intro hlower hupper

/-- Helper for Theorem 16.13: a finite product of unit-disk factors that are all `δ`-close to one
reference value stays within `card * δ` of the corresponding pure power. -/
lemma normProdSubPowLeCardMulLocal {ι : Type*}
    (s : Finset ι) (z : ι → ℂ) (w : ℂ) {δ : ℝ}
    (hz : ∀ i ∈ s, ‖z i‖ ≤ 1)
    (hw : ‖w‖ ≤ 1)
    (hclose : ∀ i ∈ s, ‖z i - w‖ ≤ δ) :
    ‖(∏ i ∈ s, z i) - w ^ s.card‖ ≤ s.card * δ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- Proof comment: the empty product is exactly the zeroth power.
      simp
  | @insert a s ha ih =>
      have hclosea : ‖z a - w‖ ≤ δ := hclose a (by simp [ha])
      have hδ : 0 ≤ δ := le_trans (norm_nonneg _) hclosea
      have hzs : ∀ i ∈ s, ‖z i‖ ≤ 1 := fun i hi ↦ hz i (by simp [hi])
      have hcloses : ∀ i ∈ s, ‖z i - w‖ ≤ δ := fun i hi ↦ hclose i (by simp [hi])
      have hprod :
          ‖∏ x ∈ s, z x‖ ≤ 1 := by
        rw [norm_prod]
        exact Finset.prod_le_one (fun i hi ↦ norm_nonneg _) fun i hi ↦ hzs i hi
      have htail : ‖(∏ x ∈ s, z x) - w ^ s.card‖ ≤ s.card * δ := ih hzs hcloses
      have hfirst : ‖z a - w‖ * ‖∏ x ∈ s, z x‖ ≤ δ := by
        calc
          ‖z a - w‖ * ‖∏ x ∈ s, z x‖ ≤ δ * 1 := by
            gcongr
          _ = δ := by ring
      have hsecond : ‖w‖ * ‖(∏ x ∈ s, z x) - w ^ s.card‖ ≤ s.card * δ := by
        calc
          ‖w‖ * ‖(∏ x ∈ s, z x) - w ^ s.card‖ ≤ 1 * ((s.card : ℝ) * δ) := by
            gcongr
          _ = (s.card : ℝ) * δ := by ring
      -- Proof comment: split off the new factor and bound the two resulting terms separately by
      -- the one-step perturbation budget and the induction hypothesis.
      calc
        ‖(∏ x ∈ insert a s, z x) - w ^ (insert a s).card‖
            = ‖z a * (∏ x ∈ s, z x) - w * w ^ s.card‖ := by
                simp [ha, pow_succ, mul_comm]
        _ = ‖(z a - w) * (∏ x ∈ s, z x) + w * ((∏ x ∈ s, z x) - w ^ s.card)‖ := by
              congr 1
              ring
        _ ≤ ‖(z a - w) * (∏ x ∈ s, z x)‖ + ‖w * ((∏ x ∈ s, z x) - w ^ s.card)‖ := by
              exact norm_add_le _ _
        _ = ‖z a - w‖ * ‖∏ x ∈ s, z x‖ + ‖w‖ * ‖(∏ x ∈ s, z x) - w ^ s.card‖ := by
              rw [norm_mul, norm_mul]
        _ ≤ δ + (s.card : ℝ) * δ := by linarith
        _ = ((s.card : ℝ) + 1) * δ := by ring
        _ = (insert a s).card * δ := by
              simp [ha]

/-- Helper for Theorem 16.13: the row-entry characteristic functions already satisfy the three
local hypotheses needed for the triangular-array CFP criterion. -/
lemma rowEntryCharFun_triangularCriterionData
    (Q : Measure Ω') [IsProbabilityMeasure Q] (S : Ω' → ℝ)
    (hS : TendstoInDistribution A.rowSum atTop S (fun _ ↦ P) Q)
    (μS : ProbabilityMeasure ℝ)
    (hμS : μS = ProbabilityMeasure.map ⟨Q, inferInstance⟩ hS.aemeasurable_limit) :
    (∀ n : ℕ, ∀ l : Fin (A.rowLength n),
        IsCFP (fun t : ℝ ↦ charFun (P.map (A n l)) t)) ∧
      (∀ L > 0, ∀ ε > 0, ∀ᶠ n in atTop,
        ∀ t ∈ Set.Icc (-L) L, ∀ l : Fin (A.rowLength n),
          ‖charFun (P.map (A n l)) t - 1‖ ≤ ε) ∧
      (∀ t : ℝ,
        Tendsto
          (fun n ↦ ∏ l : Fin (A.rowLength n), charFun (P.map (A n l)) t)
          atTop
          (𝓝 (charFun (μS : Measure ℝ) t))) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Each row entry law has a characteristic function of CFP type.
    intro n l
    exact rowEntryCharFun_isCFP (A := A) (P := P) n l
  · -- The null-array hypothesis gives the compact near-one control required by the criterion.
    intro L hL ε hε
    exact eventually_entryCharFun_closeTo_one_on_compacts (A := A) (P := P) L hL ε hε
  · -- Convergence in distribution of the row sums identifies the rowwise product limit law.
    intro t
    exact rowSumEntryCharFunProduct_tendsto_limit (A := A) (P := P) Q S hS μS hμS t

/-- Helper for Theorem 16.13: the limiting law of the row sums is infinitely divisible once the
rowwise product hypotheses are packaged for Theorem 16.12. -/
lemma rowSumLimitLaw_isInfinitelyDivisible
    (Q : Measure Ω') [IsProbabilityMeasure Q] (S : Ω' → ℝ)
    (hS : TendstoInDistribution A.rowSum atTop S (fun _ ↦ P) Q)
    (μS : ProbabilityMeasure ℝ)
    (hμS : μS = ProbabilityMeasure.map ⟨Q, inferInstance⟩ hS.aemeasurable_limit) :
    ProbabilityMeasure.IsInfinitelyDivisible μS := by
  rcases rowEntryCharFun_triangularCriterionData (A := A) (P := P) Q S hS μS hμS with
    ⟨hcfp, hsmall, hprod⟩
  -- Proof comment: Theorem 16.12 exactly matches the packaged rowwise CFP, near-one, and
  -- product-limit data, so it closes the owner-side law statement directly.
  exact cfp_array_product_limit_charFun_isInfinitelyDivisible
    (k := A.rowLength)
    (φs := fun n l t ↦ charFun (P.map (A n l)) t)
    (μ := μS) hcfp hsmall hprod

-- Proof sketch: apply the earlier triangular-array CFP theorem to the limiting law of the row
-- sums, then transport that owner-side infinite divisibility statement back to the random
-- variable via the measurable-representative bridge.
/-- Theorem 16.13: if the row sums of an independent null array of real random variables converge
in distribution to a real random variable `S`, then `S` is infinitely divisible. -/
theorem null_array_limit_isInfinitelyDivisible
    (Q : Measure Ω') [IsProbabilityMeasure Q] (S : Ω' → ℝ)
    (hS : TendstoInDistribution A.rowSum atTop S (fun _ ↦ P) Q) :
    IsInfinitelyDivisibleRandomVariable Q S := by
  let Sm : Ω' → ℝ := hS.aemeasurable_limit.mk S
  let μS : ProbabilityMeasure ℝ := ProbabilityMeasure.map ⟨Q, inferInstance⟩ hS.aemeasurable_limit
  have hSm_meas : Measurable Sm := hS.aemeasurable_limit.measurable_mk
  have hSm_ident : IdentDistrib S Sm Q Q := by
    simpa [Sm] using hS.aemeasurable_limit.identDistrib_mk
  have hμS_infdiv : ProbabilityMeasure.IsInfinitelyDivisible μS := by
    -- Proof comment: the law-side statement is now a direct application of Theorem 16.12 to the
    -- packaged rowwise characteristic-function data.
    exact rowSumLimitLaw_isInfinitelyDivisible (A := A) (P := P) Q S hS μS rfl
  have hμS_map_eq :
      μS =
        ProbabilityMeasure.map ⟨Q, inferInstance⟩ hSm_meas.aemeasurable := by
    -- Proof comment: the limit law built from `hS.aemeasurable_limit` equals the law of the
    -- measurable representative `Sm`.
    simpa [μS, Sm] using measurableRepresentativeLaw_eq (A := A) (P := P) Q S hS
  have hSm_map_infdiv :
      ProbabilityMeasure.IsInfinitelyDivisible
        (ProbabilityMeasure.map ⟨Q, inferInstance⟩ hSm_meas.aemeasurable) := by
    -- Proof comment: transport infinite divisibility across the equality of the two map laws.
    exact hμS_map_eq ▸ hμS_infdiv
  have hSm_infdiv : IsInfinitelyDivisibleRandomVariable Q Sm := by
    -- Convert the law-side infinite divisibility back to the measurable representative.
    simpa [Sm] using
      measurableRepresentative_isInfinitelyDivisible (A := A) (P := P) Q S hS hSm_map_infdiv
  -- Transfer the measurable representative result back to the original limit variable.
  exact
    isInfinitelyDivisibleRandomVariable_of_identDistrib (Q := Q) hSm_ident hSm_infdiv

end

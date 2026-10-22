/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_10

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Example 24.19: transporting the bounded-cell Poisson law from `ℝ≥0∞` to `ℝ`
gives the real-valued count law needed for scalar moment computations. -/
private theorem poissonCountToReal_hasLaw_onBoundedSet
    (P : ProbabilityMeasure Ω) (ν : Measure NNReal) (X : Ω → Measure NNReal)
    (hX : ProbabilityTheory.IsPoissonPointProcess ν P X)
    {A : Set NNReal} (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A)
    (hA_finite : ν A ≠ ⊤) :
    HasLaw (fun ω ↦ (X ω A).toReal)
      (Measure.map (fun n : ℕ ↦ (n : ℝ)) (poissonMeasure (ν A).toNNReal))
      (P : Measure Ω) := by
  have hCountLaw :
      HasLaw (fun ω ↦ X ω A)
        (Measure.map (fun n : ℕ ↦ (n : ℝ≥0∞)) (poissonMeasure (ν A).toNNReal))
        (P : Measure Ω) :=
    hX.2.2.2 hA hA_bdd hA_finite
  have hToRealLaw :
      HasLaw ENNReal.toReal
        (Measure.map (fun n : ℕ ↦ (n : ℝ)) (poissonMeasure (ν A).toNNReal))
        (Measure.map (fun n : ℕ ↦ (n : ℝ≥0∞)) (poissonMeasure (ν A).toNNReal)) := by
    refine ⟨ENNReal.measurable_toReal.aemeasurable, ?_⟩
    -- Proof comment: on natural numbers, `ENNReal.toReal` recovers the ordinary cast to `ℝ`.
    rw [AEMeasurable.map_map_of_aemeasurable ENNReal.measurable_toReal.aemeasurable
      (measurable_of_countable (fun n : ℕ ↦ (n : ℝ≥0∞))).aemeasurable]
    rfl
  -- Proof comment: compose the bounded-cell count law with `ENNReal.toReal` once and reuse the
  -- resulting real-valued law everywhere downstream.
  simpa [Function.comp] using hToRealLaw.comp hCountLaw

/-- Helper for Example 24.19: the singleton masses of `poissonMeasure r` are the explicit Poisson
probabilities. -/
private theorem poissonMeasure_apply_singleton_eq (r : NNReal) (n : ℕ) :
    poissonMeasure r ({n} : Set ℕ) = ENNReal.ofReal (poissonPMFReal r n) := by
  -- Proof comment: rewrite the Poisson measure back to its defining `PMF`.
  simpa [poissonMeasure, poissonPMFReal_ofReal_eq_poissonPMF] using
    (PMF.toMeasure_apply_singleton (poissonPMF r) n (measurableSet_singleton n))

/-- Helper for Example 24.19: a summable singleton-mass weighted norm series on `ℕ` yields an
integrable function for the corresponding finite measure. -/
private theorem integrable_natMeasure_of_summableNorm (μ : Measure ℕ) [IsFiniteMeasure μ]
    (f : ℕ → ℝ) (hf : Summable (fun n : ℕ ↦ (μ {n}).toReal * ‖f n‖)) :
    Integrable f μ := by
  -- Proof comment: expand the finite measure into singleton atoms and collapse the norm integral
  -- to the assumed summable series.
  refine ⟨(measurable_of_countable f).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm, ← Measure.sum_smul_dirac μ, lintegral_sum_measure]
  have hterm :
      (fun n : ℕ ↦ ∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ {n} • Measure.dirac n) =
        fun n : ℕ ↦ ENNReal.ofReal ((μ {n}).toReal * ‖f n‖) := by
    funext n
    rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    have hmass : μ {n} = ENNReal.ofReal (μ {n}).toReal :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    calc
      μ {n} * ENNReal.ofReal ‖f n‖ = ENNReal.ofReal (μ {n}).toReal * ENNReal.ofReal ‖f n‖ := by
        simpa using congrArg (fun t : ℝ≥0∞ ↦ t * ENNReal.ofReal ‖f n‖) hmass
      _ = ENNReal.ofReal ((μ {n}).toReal * ‖f n‖) := by
        simpa using (ENNReal.ofReal_mul (norm_nonneg (f n))).symm
  rw [hterm, ← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity) hf]
  simp

/-- Helper for Example 24.19: the real-valued Poisson law has the exact exponential moment
`exp (λ (exp u - 1))`. -/
private theorem poissonMeasure_realCast_mgf (lam : NNReal) (u : ℝ) :
    mgf (fun n : ℕ ↦ (n : ℝ)) (poissonMeasure lam) u =
      Real.exp ((lam : ℝ) * (Real.exp u - 1)) := by
  have hseries :
      HasSum
        (fun n : ℕ ↦
          Real.exp (-((lam : ℝ))) * (((lam : ℝ) * Real.exp u) ^ n / ↑n.factorial))
        (Real.exp (-((lam : ℝ))) * Real.exp ((lam : ℝ) * Real.exp u)) := by
    simpa [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp ((lam : ℝ) * Real.exp u)).mul_left
        (Real.exp (-((lam : ℝ))))
  have hsummable :
      Summable
        (fun n : ℕ ↦
          (poissonMeasure lam {n}).toReal * ‖Real.exp (u * (n : ℝ))‖) := by
    refine hseries.summable.congr ?_
    intro n
    rw [poissonMeasure_apply_singleton_eq]
    rw [ENNReal.toReal_ofReal poissonPMFReal_nonneg, poissonPMFReal]
    have hfac : (↑n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    rw [Real.norm_of_nonneg (Real.exp_nonneg _), mul_comm u (n : ℝ), Real.exp_nat_mul, mul_pow]
    field_simp [hfac]
  have hint :
      Integrable (fun n : ℕ ↦ Real.exp (u * (n : ℝ))) (poissonMeasure lam) := by
    exact integrable_natMeasure_of_summableNorm (poissonMeasure lam) _ hsummable
  -- Proof comment: rewrite the expectation as a singleton series and collapse it with the
  -- exponential power series.
  calc
    mgf (fun n : ℕ ↦ (n : ℝ)) (poissonMeasure lam) u
      = ∫ n, Real.exp (u * (n : ℝ)) ∂poissonMeasure lam := by
          rfl
    _ = ∑' n : ℕ, ((poissonMeasure lam) {n}).toReal * Real.exp (u * (n : ℝ)) := by
          simpa [Measure.real, smul_eq_mul] using integral_countable hint
    _ =
        ∑' n : ℕ,
          Real.exp (-((lam : ℝ))) * (((lam : ℝ) * Real.exp u) ^ n / ↑n.factorial) := by
          refine tsum_congr fun n ↦ ?_
          rw [poissonMeasure_apply_singleton_eq]
          rw [ENNReal.toReal_ofReal poissonPMFReal_nonneg, poissonPMFReal]
          have hfac : (↑n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
          rw [mul_comm u (n : ℝ), Real.exp_nat_mul, mul_pow]
          field_simp [hfac]
    _ = Real.exp (-((lam : ℝ))) * Real.exp ((lam : ℝ) * Real.exp u) := hseries.tsum_eq
    _ = Real.exp ((lam : ℝ) * (Real.exp u - 1)) := by
          rw [← Real.exp_add]
          congr 1
          ring

/-- Helper for Example 24.19: on one bounded measurable cell, the transported Poisson count law
gives the exact exponential moment of the real-valued count variable. -/
private theorem poissonCountToReal_expMul_expectation_onBoundedSet
    (P : ProbabilityMeasure Ω) (ν : Measure NNReal) (X : Ω → Measure NNReal)
    (hX : ProbabilityTheory.IsPoissonPointProcess ν P X)
    {A : Set NNReal} (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A)
    (hA_finite : ν A ≠ ⊤) (u : ℝ) :
    ∫ ω, Real.exp (u * (X ω A).toReal) ∂(P : Measure Ω) =
      Real.exp ((ν A).toReal * (Real.exp u - 1)) := by
  have hLaw := poissonCountToReal_hasLaw_onBoundedSet P ν X hX hA hA_bdd hA_finite
  have hExpMeas :
      AEStronglyMeasurable (fun x : ℝ ↦ Real.exp (u * x))
        (Measure.map (fun n : ℕ ↦ (n : ℝ)) (poissonMeasure (ν A).toNNReal)) := by
    -- Proof comment: the scalar exponential kernel is continuous, hence strongly measurable.
    exact
      ((measurable_const.mul measurable_id).exp.aestronglyMeasurable :
        AEStronglyMeasurable (fun x : ℝ ↦ Real.exp (u * x))
          (Measure.map (fun n : ℕ ↦ (n : ℝ)) (poissonMeasure (ν A).toNNReal)))
  have hMap :
      mgf id (Measure.map (fun n : ℕ ↦ (n : ℝ)) (poissonMeasure (ν A).toNNReal)) u =
        mgf (fun n : ℕ ↦ (n : ℝ)) (poissonMeasure (ν A).toNNReal) u := by
    simpa using
      congrFun
        (ProbabilityTheory.mgf_id_map
          ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).aemeasurable))
        u
  -- Proof comment: evaluate the expectation under the transported count law, then collapse the
  -- Poisson mgf explicitly.
  calc
    ∫ ω, Real.exp (u * (X ω A).toReal) ∂(P : Measure Ω)
      = ∫ x, Real.exp (u * x) ∂(Measure.map (fun n : ℕ ↦ (n : ℝ)) (poissonMeasure (ν A).toNNReal)) := by
          simpa using hLaw.integral_comp hExpMeas
    _ = mgf id (Measure.map (fun n : ℕ ↦ (n : ℝ)) (poissonMeasure (ν A).toNNReal)) u := by
          rfl
    _ = mgf (fun n : ℕ ↦ (n : ℝ)) (poissonMeasure (ν A).toNNReal) u := hMap
    _ = Real.exp ((((ν A).toNNReal : NNReal) : ℝ) * (Real.exp u - 1)) := by
          simpa using poissonMeasure_realCast_mgf (ν A).toNNReal u
    _ = Real.exp ((ν A).toReal * (Real.exp u - 1)) := by
          simp [ENNReal.coe_toNNReal_eq_toReal]

/-- Helper for Example 24.19: the finite-cell Laplace identity on `Fin n` is the product of the
one-cell Poisson factors. -/
private theorem disjointBoundedStepLaplaceTransformFinNNReal
    (P : ProbabilityMeasure Ω) (ν : Measure NNReal) (X : Ω → Measure NNReal)
    (hX : ProbabilityTheory.IsPoissonPointProcess ν P X)
    {n : ℕ} (A : Fin n → Set NNReal) (a : Fin n → NNReal)
    (hA : ∀ i, MeasurableSet (A i)) (hA_bdd : ∀ i, Bornology.IsBounded (A i))
    (hdisj : Pairwise (fun i j ↦ Disjoint (A i) (A j))) :
    ∫ ω, Real.exp (-∑ i, (a i : ℝ) * (X ω (A i)).toReal) ∂(P : Measure Ω) =
      Real.exp (∑ i, (ν (A i)).toReal * (Real.exp (-(a i : ℝ)) - 1)) := by
  letI : IsLocallyFiniteMeasure ν := hX.2.2.1
  have hA_finite : ∀ i, ν (A i) ≠ ⊤ := fun i ↦ (hA_bdd i).measure_lt_top.ne
  have hCountIndep :
      iIndepFun (fun i ω ↦ X ω (A i)) (P : Measure Ω) :=
    hX.2.1 _ A hA hdisj
  have hToRealIndep :
      iIndepFun (fun i ω ↦ (X ω (A i)).toReal) (P : Measure Ω) := by
    -- Proof comment: move the independent bounded-cell count family through `ENNReal.toReal`
    -- once so the scalar exponential-moment route applies coordinatewise.
    exact hCountIndep.comp (fun _ ↦ ENNReal.toReal) (fun _ ↦ ENNReal.measurable_toReal)
  let Y : Fin n → Ω → ℝ := fun i ω ↦ Real.exp ((-(a i : ℝ)) * (X ω (A i)).toReal)
  have hYIndep : iIndepFun Y (P : Measure Ω) := by
    -- Proof comment: independence is preserved under the coordinatewise exponential kernels.
    refine hToRealIndep.comp (fun i x ↦ Real.exp ((-(a i : ℝ)) * x)) ?_
    intro i
    exact (measurable_const.mul measurable_id).exp
  have hY_meas : ∀ i, Measurable (Y i) := by
    intro i
    -- Proof comment: random-measure evaluation is measurable on measurable cells, and the
    -- exponential kernel is continuous.
    have hCellMeas : Measurable (fun ω ↦ (X ω (A i)).toReal) :=
      ENNReal.measurable_toReal.comp ((Measure.measurable_coe (hA i)).comp hX.1.measurable)
    exact (measurable_const.mul hCellMeas).exp
  have hY_aestronglyMeasurable :
      ∀ i, AEStronglyMeasurable (Y i) (P : Measure Ω) := fun i ↦
        (hY_meas i).aestronglyMeasurable
  -- Route correction: factor the finite exponential of the sum into a product of one-cell
  -- terms, and apply independent increments only once at that product layer.
  calc
    ∫ ω, Real.exp (-∑ i, (a i : ℝ) * (X ω (A i)).toReal) ∂(P : Measure Ω)
      = ∫ ω, ∏ i, Y i ω ∂(P : Measure Ω) := by
          congr with ω
          calc
            Real.exp (-∑ i, (a i : ℝ) * (X ω (A i)).toReal)
                = Real.exp (∑ i, (-(a i : ℝ) * (X ω (A i)).toReal)) := by
                    congr 1
                    simp
            _ = ∏ i, Y i ω := by
                  rw [Real.exp_sum]
    _ = ∏ i, ∫ ω, Y i ω ∂(P : Measure Ω) := by
          simpa using hYIndep.integral_prod_eq_prod_integral hY_aestronglyMeasurable
    _ = ∏ i, Real.exp ((ν (A i)).toReal * (Real.exp (-(a i : ℝ)) - 1)) := by
          refine Finset.prod_congr rfl fun i _ ↦ ?_
          simpa [Y, mul_comm, mul_left_comm, mul_assoc] using
            poissonCountToReal_expMul_expectation_onBoundedSet
              P ν X hX (hA i) (hA_bdd i) (hA_finite i) (-(a i : ℝ))
    _ = Real.exp (∑ i, (ν (A i)).toReal * (Real.exp (-(a i : ℝ)) - 1)) := by
          rw [← Real.exp_sum]

/-- Helper for Example 24.19: the finite-dimensional Laplace transform of a Poisson point process
over pairwise disjoint bounded measurable cells has the textbook product-exponential form. -/
theorem disjointBoundedStepLaplaceTransformNNReal
    (P : ProbabilityMeasure Ω) (ν : Measure NNReal) (X : Ω → Measure NNReal)
    (hX : ProbabilityTheory.IsPoissonPointProcess ν P X)
    {ι : Type*} [Fintype ι] (A : ι → Set NNReal) (a : ι → NNReal)
    (hA : ∀ i, MeasurableSet (A i)) (hA_bdd : ∀ i, Bornology.IsBounded (A i))
    (hdisj : Pairwise (fun i j ↦ Disjoint (A i) (A j))) :
    ∫ ω, Real.exp (-∑ i, (a i : ℝ) * (X ω (A i)).toReal) ∂(P : Measure Ω) =
      Real.exp (∑ i, (ν (A i)).toReal * (Real.exp (-(a i : ℝ)) - 1)) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hmain :=
    disjointBoundedStepLaplaceTransformFinNNReal P ν X hX
      (A := fun i ↦ A (e i)) (a := fun i ↦ a (e i))
      (hA := fun i ↦ hA (e i))
      (hA_bdd := fun i ↦ hA_bdd (e i))
      (hdisj := by
        intro i j hij
        exact hdisj (by
          intro hEq
          exact hij (e.injective hEq)))
  have hSampleSum :
      ∀ ω,
        (∑ i : ι, (a i : ℝ) * (X ω (A i)).toReal) =
          ∑ i : Fin (Fintype.card ι), (a (e i) : ℝ) * (X ω (A (e i))).toReal := by
    intro ω
    symm
    exact Fintype.sum_equiv e
      (fun i : Fin (Fintype.card ι) ↦ (a (e i) : ℝ) * (X ω (A (e i))).toReal)
      (fun i : ι ↦ (a i : ℝ) * (X ω (A i)).toReal)
      (fun _ ↦ rfl)
  have hIntensitySum :
      (∑ i : ι, (ν (A i)).toReal * (Real.exp (-(a i : ℝ)) - 1)) =
        ∑ i : Fin (Fintype.card ι),
          (ν (A (e i))).toReal * (Real.exp (-(a (e i) : ℝ)) - 1) := by
    symm
    exact Fintype.sum_equiv e
      (fun i : Fin (Fintype.card ι) ↦
        (ν (A (e i))).toReal * (Real.exp (-(a (e i) : ℝ)) - 1))
      (fun i : ι ↦ (ν (A i)).toReal * (Real.exp (-(a i : ℝ)) - 1))
      (fun _ ↦ rfl)
  -- Proof comment: reindex the already proved `Fin`-indexed identity once through
  -- `Fintype.equivFin`, then keep later simple-function fibers in their native finite index type.
  calc
    ∫ ω, Real.exp (-∑ i, (a i : ℝ) * (X ω (A i)).toReal) ∂(P : Measure Ω)
      = ∫ ω,
          Real.exp (-∑ i : Fin (Fintype.card ι), (a (e i) : ℝ) * (X ω (A (e i))).toReal)
            ∂(P : Measure Ω) := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
              simpa [hSampleSum ω]
    _ = Real.exp
          (∑ i : Fin (Fintype.card ι),
            (ν (A (e i))).toReal * (Real.exp (-(a (e i) : ℝ)) - 1)) := hmain
    _ = Real.exp (∑ i, (ν (A i)).toReal * (Real.exp (-(a i : ℝ)) - 1)) := by
          rw [← hIntensitySum]

end ProbabilityTheory

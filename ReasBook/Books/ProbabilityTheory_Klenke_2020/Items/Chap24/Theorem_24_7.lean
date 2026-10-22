/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Theorem_24_5
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Exercise_15_1_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory
open scoped BigOperators CompactlySupported NNReal

universe u

variable {E : Type u} [PseudoMetricSpace E] [MeasurableSpace E]

-- Semantic recall: `MeasureTheory.Measure.ext_of_charFun` is the mathlib uniqueness tool for the
-- characteristic-function side, while Chapter 24 packages the random-measure ambient law on
-- `ProbabilityMeasure (BoundedlyFiniteMeasure E)` rather than on arbitrary `Measure E`.

/-- The Laplace transform of a probability law on boundedly finite measures, evaluated at a
nonnegative compactly supported continuous test function. -/
def random_measure_laplace_transform
    (P : ProbabilityMeasure (BoundedlyFiniteMeasure E))
    (f : C_c(E, ℝ≥0)) : ℝ :=
  ∫ μ, Real.exp (-BoundedlyFiniteMeasure.nonnegativeVagueIntegral f μ)
    ∂(P : Measure (BoundedlyFiniteMeasure E))

-- Proof sketch: unfold `random_measure_laplace_transform`; this is exactly the expectation of the
-- textbook test functional `μ ↦ exp (-∫ f dμ)` under the law `P`.
/-- Expanding `random_measure_laplace_transform P f` gives the textbook Laplace-transform formula
for the law `P` of a random measure. -/
theorem random_measure_laplace_transform_def
    (P : ProbabilityMeasure (BoundedlyFiniteMeasure E))
    (f : C_c(E, ℝ≥0)) :
    random_measure_laplace_transform P f =
      ∫ μ, Real.exp (-BoundedlyFiniteMeasure.nonnegativeVagueIntegral f μ)
        ∂(P : Measure (BoundedlyFiniteMeasure E)) :=
by
  -- Proof comment: this is exactly the defining formula of `random_measure_laplace_transform`.
  rfl

/-- The characteristic function of a probability law on boundedly finite measures, evaluated at a
real-valued compactly supported continuous test function. -/
def random_measure_characteristic_function
    (P : ProbabilityMeasure (BoundedlyFiniteMeasure E))
    (f : C_c(E, ℝ)) : ℂ :=
  ∫ μ, Complex.exp ((BoundedlyFiniteMeasure.vagueIntegral f μ : ℂ) * Complex.I)
    ∂(P : Measure (BoundedlyFiniteMeasure E))

-- Proof sketch: unfold `random_measure_characteristic_function`; this is exactly the expectation
-- of the Fourier kernel `μ ↦ exp (i ∫ f dμ)` under the law `P`.
/-- Expanding `random_measure_characteristic_function P f` gives the textbook characteristic-
function formula for the law `P` of a random measure. -/
theorem random_measure_characteristic_function_def
    (P : ProbabilityMeasure (BoundedlyFiniteMeasure E))
    (f : C_c(E, ℝ)) :
    random_measure_characteristic_function P f =
      ∫ μ, Complex.exp ((BoundedlyFiniteMeasure.vagueIntegral f μ : ℂ) * Complex.I)
        ∂(P : Measure (BoundedlyFiniteMeasure E)) :=
by
  -- Proof comment: this is exactly the defining formula of
  -- `random_measure_characteristic_function`.
  rfl

-- Proof sketch: for each nonnegative test function `f`, apply the one-dimensional uniqueness
-- theorem for Laplace transforms to the pushforward laws of `μ ↦ ∫ f dμ`; then invoke
-- `random_measure_law_eq_of_integral_or_disjoint_set_finite_dimensional_distributions`.
section ChapterAmbient

variable [BorelSpace E] [LocallyCompactSpace E] [PolishSpace E] [T2Space E]

/-- Helper for Theorem 24.7: finite tuples of random-measure test integrals are measurable. -/
private theorem measurable_random_measure_test_integral_tuple
    {n : ℕ} (fs : Fin n → C_c(E, ℝ≥0)) :
    Measurable (random_measure_test_integral_tuple fs) := by
  -- Proof comment: each coordinate is one measurable nonnegative vague integral.
  exact measurable_pi_lambda _ fun i ↦ measurable_nonnegativeVagueIntegral (fs i)

/-- Helper for Theorem 24.7: a nonnegative weighted sum of test integrals is the single
nonnegative vague integral of the weighted sum test function. -/
private theorem nonnegativeVagueIntegralWeightedSum
    {n : ℕ} (fs : Fin n → C_c(E, ℝ≥0)) (a : Fin n → ℝ≥0) (μ : BoundedlyFiniteMeasure E) :
    BoundedlyFiniteMeasure.nonnegativeVagueIntegral (∑ i, a i • fs i) μ =
      ∑ i, (a i : ℝ) * BoundedlyFiniteMeasure.nonnegativeVagueIntegral (fs i) μ := by
  -- Proof comment: rewrite the nonnegative integral as an ordinary real-valued vague integral,
  -- then use finite linearity of the Bochner integral.
  rw [nonnegativeVagueIntegral_eq_vagueIntegral_toReal, BoundedlyFiniteMeasure.vagueIntegral_apply]
  calc
    ∫ x, (∑ i, a i • fs i).toReal x ∂(μ : Measure E)
        = ∫ x, ∑ i, (a i : ℝ) * (fs i).toReal x ∂(μ : Measure E) := by
            congr with x
            simp [mul_comm, mul_left_comm, mul_assoc]
    _ = ∑ i, ∫ x, (a i : ℝ) * (fs i).toReal x ∂(μ : Measure E) := by
          rw [integral_finset_sum]
          intro i hi
          exact Integrable.const_mul (integrable_vagueTest μ (fs i).toReal) (a i : ℝ)
    _ = ∑ i, (a i : ℝ) * BoundedlyFiniteMeasure.nonnegativeVagueIntegral (fs i) μ := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [integral_const_mul, ← BoundedlyFiniteMeasure.vagueIntegral_apply,
            ← nonnegativeVagueIntegral_eq_vagueIntegral_toReal]

/-- Helper for Theorem 24.7: a real weighted sum of nonnegative test integrals is the vague
integral of the corresponding real-valued weighted sum test function. -/
private theorem vagueIntegralWeightedToRealSum
    {n : ℕ} (fs : Fin n → C_c(E, ℝ≥0)) (t : Fin n → ℝ) (μ : BoundedlyFiniteMeasure E) :
    BoundedlyFiniteMeasure.vagueIntegral (∑ i, t i • (fs i).toReal) μ =
      ∑ i, t i * BoundedlyFiniteMeasure.nonnegativeVagueIntegral (fs i) μ := by
  -- Proof comment: expand the vague integral of the finite sum and pull each scalar outside.
  rw [BoundedlyFiniteMeasure.vagueIntegral_apply]
  calc
    ∫ x, (∑ i, t i • (fs i).toReal) x ∂(μ : Measure E)
        = ∫ x, ∑ i, t i * (fs i).toReal x ∂(μ : Measure E) := by
            congr with x
            simp [mul_comm, mul_left_comm, mul_assoc]
    _ = ∑ i, ∫ x, t i * (fs i).toReal x ∂(μ : Measure E) := by
          rw [integral_finset_sum]
          intro i hi
          exact Integrable.const_mul (integrable_vagueTest μ (fs i).toReal) (t i)
    _ = ∑ i, t i * BoundedlyFiniteMeasure.nonnegativeVagueIntegral (fs i) μ := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [integral_const_mul, ← BoundedlyFiniteMeasure.vagueIntegral_apply,
            ← nonnegativeVagueIntegral_eq_vagueIntegral_toReal]

/-- Helper for Theorem 24.7: the characteristic function of a finite tuple law is the
characteristic function of the corresponding weighted test integral. -/
private theorem tupleLawCharFunDualEqCharacteristicProbe
    {n : ℕ} (fs : Fin n → C_c(E, ℝ≥0))
    (P : ProbabilityMeasure (BoundedlyFiniteMeasure E))
    (L : StrongDual ℝ (Fin n → ℝ)) :
    MeasureTheory.charFunDual
        (Measure.map (random_measure_test_integral_tuple fs)
          (P : Measure (BoundedlyFiniteMeasure E)))
        L =
      random_measure_characteristic_function P
        (∑ i, (L (Pi.single i (1 : ℝ))) • (fs i).toReal) := by
  have hProbeMeas :
      AEStronglyMeasurable
        (fun v : Fin n → ℝ ↦ Complex.exp ((L v : ℂ) * Complex.I))
        (Measure.map (random_measure_test_integral_tuple fs)
          (P : Measure (BoundedlyFiniteMeasure E))) := by
    have hMeas :
        Measurable (fun v : Fin n → ℝ ↦ Complex.exp ((L v : ℂ) * Complex.I)) := by
      fun_prop
    exact hMeas.aestronglyMeasurable
  -- Proof comment: push the tuple-law characteristic function back to the original law `P`.
  rw [MeasureTheory.charFunDual_apply,
    integral_map (measurable_random_measure_test_integral_tuple (E := E) fs).aemeasurable
      hProbeMeas]
  -- Proof comment: the dual probe decomposes into the finite weighted sum of tuple coordinates.
  congr with μ
  have hsum :
      L (random_measure_test_integral_tuple fs μ) =
        ∑ i, L (Pi.single i
          (BoundedlyFiniteMeasure.nonnegativeVagueIntegral (fs i) μ)) := by
    have hdecomp :
        ∑ i, (Pi.single i
          (BoundedlyFiniteMeasure.nonnegativeVagueIntegral (fs i) μ) : Fin n → ℝ) =
          random_measure_test_integral_tuple fs μ := by
      ext j
      simp [random_measure_test_integral_tuple]
    calc
      L (random_measure_test_integral_tuple fs μ) = L
          (∑ i, (Pi.single i
            (BoundedlyFiniteMeasure.nonnegativeVagueIntegral (fs i) μ) : Fin n → ℝ)) := by
            rw [← hdecomp]
      _ = ∑ i, L (Pi.single i
            (BoundedlyFiniteMeasure.nonnegativeVagueIntegral (fs i) μ)) := by
            rw [map_sum]
  have hsingle :
      ∀ i : Fin n,
        L (Pi.single i (BoundedlyFiniteMeasure.nonnegativeVagueIntegral (fs i) μ)) =
          L (Pi.single i (1 : ℝ)) *
            BoundedlyFiniteMeasure.nonnegativeVagueIntegral (fs i) μ := by
    intro i
    calc
      L (Pi.single i (BoundedlyFiniteMeasure.nonnegativeVagueIntegral (fs i) μ))
          = L
              ((BoundedlyFiniteMeasure.nonnegativeVagueIntegral (fs i) μ) •
                (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
                  congr
                  ext j
                  by_cases hij : j = i
                  · subst hij
                    simp
                  · simp [Pi.single_apply, hij]
      _ = (BoundedlyFiniteMeasure.nonnegativeVagueIntegral (fs i) μ) • L (Pi.single i (1 : ℝ)) := by
            rw [map_smul]
      _ = L (Pi.single i (1 : ℝ)) *
            BoundedlyFiniteMeasure.nonnegativeVagueIntegral (fs i) μ := by
            rw [smul_eq_mul, mul_comm]
  -- Proof comment: identify the resulting real exponent with the weighted vague integral.
  rw [hsum]
  rw [vagueIntegralWeightedToRealSum (E := E) fs (fun i ↦ L (Pi.single i (1 : ℝ))) μ]
  have hsumEq :
      ∑ i, L (Pi.single i (BoundedlyFiniteMeasure.nonnegativeVagueIntegral (fs i) μ)) =
        ∑ i, L (Pi.single i (1 : ℝ)) *
          BoundedlyFiniteMeasure.nonnegativeVagueIntegral (fs i) μ :=
    Finset.sum_congr rfl fun i _ ↦ hsingle i
  congr 1
  congr 1
  exact congrArg (fun r : ℝ ↦ (r : ℂ)) hsumEq

/-- Helper for Theorem 24.7: mapping the tuple law through `MeasurableEquiv.toLp` is the same as
mapping directly by the `WithLp.toLp`-transported tuple map. -/
private theorem tupleLawMapToLpEq
    {n : ℕ} (fs : Fin n → C_c(E, ℝ≥0))
    (P : ProbabilityMeasure (BoundedlyFiniteMeasure E)) :
    Measure.map (fun ν ↦ WithLp.toLp 2 (random_measure_test_integral_tuple fs ν))
      (P : Measure (BoundedlyFiniteMeasure E)) =
      Measure.map (MeasurableEquiv.toLp 2 (Fin n → ℝ))
        (Measure.map (random_measure_test_integral_tuple fs)
          (P : Measure (BoundedlyFiniteMeasure E))) := by
  -- Proof comment: collapse the two successive pushforwards to one pushforward by the composed
  -- tuple map.
  symm
  rw [AEMeasurable.map_map_of_aemeasurable
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable.aemeasurable
    (measurable_random_measure_test_integral_tuple (E := E) fs).aemeasurable]
  rfl

/-- Helper for Theorem 24.7: the Euclidean inner product against a transported tuple is the
weighted sum of its coordinates. -/
private theorem innerToLpTestIntegralTupleEqWeightedProbe
    {n : ℕ} (fs : Fin n → C_c(E, ℝ≥0)) (t : EuclideanSpace ℝ (Fin n))
    (ν : BoundedlyFiniteMeasure E) :
    inner ℝ t (WithLp.toLp 2 (random_measure_test_integral_tuple fs ν)) =
      ∑ i, t i * BoundedlyFiniteMeasure.nonnegativeVagueIntegral (fs i) ν := by
  -- Proof comment: `PiLp.inner_apply` reduces the Euclidean inner product to a coordinate sum.
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [PiLp.toLp_apply]
  simpa using (RCLike.inner_apply' (t i) (BoundedlyFiniteMeasure.nonnegativeVagueIntegral (fs i) ν))

/-- Helper for Theorem 24.7: agreement of all law-level characteristic-function values implies
agreement of every finite-dimensional law of test-integral tuples. -/
private theorem testIntegralTupleLawEqOfCharacteristicAgreement
    (P Q : ProbabilityMeasure (BoundedlyFiniteMeasure E))
    (hChar :
      ∀ f : C_c(E, ℝ),
        random_measure_characteristic_function P f =
          random_measure_characteristic_function Q f) :
    ∀ n : ℕ, ∀ fs : Fin n → C_c(E, ℝ≥0),
      Measure.map (random_measure_test_integral_tuple fs) (P : Measure (BoundedlyFiniteMeasure E)) =
        Measure.map (random_measure_test_integral_tuple fs) (Q : Measure (BoundedlyFiniteMeasure E)) :=
by
  intro n fs
  -- Route correction: the characteristic-function half stays on the raw tuple space `Fin n → ℝ`;
  -- no `toLp` transport is needed here.
  refine Measure.ext_of_charFunDual <| funext fun L ↦ ?_
  -- Proof comment: rewrite both tuple-law probes as characteristic functions of weighted test
  -- integrals and then apply the hypothesis `hChar`.
  rw [tupleLawCharFunDualEqCharacteristicProbe (E := E) fs P L,
    tupleLawCharFunDualEqCharacteristicProbe (E := E) fs Q L]
  exact hChar _

/-- Helper for Theorem 24.7: agreement of all law-level Laplace-transform values implies agreement
of every finite-dimensional law of test-integral tuples. -/
private theorem testIntegralTupleLawEqOfLaplaceAgreement
    (P Q : ProbabilityMeasure (BoundedlyFiniteMeasure E))
    (hLaplace :
      ∀ f : C_c(E, ℝ≥0),
        random_measure_laplace_transform P f =
          random_measure_laplace_transform Q f) :
    ∀ n : ℕ, ∀ fs : Fin n → C_c(E, ℝ≥0),
      Measure.map (random_measure_test_integral_tuple fs) (P : Measure (BoundedlyFiniteMeasure E)) =
        Measure.map (random_measure_test_integral_tuple fs) (Q : Measure (BoundedlyFiniteMeasure E)) :=
by
  intro n fs
  let Y : BoundedlyFiniteMeasure E → EuclideanSpace ℝ (Fin n) :=
    fun ν ↦ WithLp.toLp 2 (random_measure_test_integral_tuple fs ν)
  have hYmeas : Measurable Y := by
    simpa [Y, MeasurableEquiv.toLp_apply] using
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable.comp
        (measurable_random_measure_test_integral_tuple (E := E) fs)
  let μP : Measure (EuclideanSpace ℝ (Fin n)) :=
    Measure.map Y (P : Measure (BoundedlyFiniteMeasure E))
  let μQ : Measure (EuclideanSpace ℝ (Fin n)) :=
    Measure.map Y (Q : Measure (BoundedlyFiniteMeasure E))
  have hμP_def : μP = Measure.map Y (P : Measure (BoundedlyFiniteMeasure E)) := rfl
  have hμQ_def : μQ = Measure.map Y (Q : Measure (BoundedlyFiniteMeasure E)) := rfl
  have hOrthantMeas : MeasurableSet {x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i} :=
    by
      have hInter :
          {x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i} =
            ⋂ i, {x : EuclideanSpace ℝ (Fin n) | 0 ≤ x i} := by
              ext x
              simp
      rw [hInter]
      exact MeasurableSet.iInter fun i ↦
        measurableSet_le measurable_const
          (PiLp.continuous_apply (p := 2) (β := fun _ : Fin n ↦ ℝ) i).measurable
  have hμP_nonneg : ∀ᵐ x ∂μP, ∀ i, 0 ≤ x i := by
    -- Proof comment: every coordinate of the transported tuple is a nonnegative vague integral.
    rw [hμP_def, ae_map_iff hYmeas.aemeasurable hOrthantMeas]
    · exact Filter.Eventually.of_forall fun ν i ↦ by
        simp [Y, random_measure_test_integral_tuple]
        exact integral_nonneg fun x ↦ NNReal.coe_nonneg ((fs i) x)
  have hμQ_nonneg : ∀ᵐ x ∂μQ, ∀ i, 0 ≤ x i := by
    -- Proof comment: the same pointwise nonnegativity holds for the `Q`-law tuple map.
    rw [hμQ_def, ae_map_iff hYmeas.aemeasurable hOrthantMeas]
    · exact Filter.Eventually.of_forall fun ν i ↦ by
        simp [Y, random_measure_test_integral_tuple]
        exact integral_nonneg fun x ↦ NNReal.coe_nonneg ((fs i) x)
  have hmgf :
      ∀ t : EuclideanSpace ℝ (Fin n),
        (∀ i, 0 ≤ t i) →
          ProbabilityTheory.mgf (fun x ↦ -inner ℝ t x) μP 1 =
            ProbabilityTheory.mgf (fun x ↦ -inner ℝ t x) μQ 1 := by
    intro t ht
    have hInnerMeas : Measurable (fun x : EuclideanSpace ℝ (Fin n) ↦ -inner ℝ t x) := by
      fun_prop
    have hExpMeasP :
        AEStronglyMeasurable
          (fun x : EuclideanSpace ℝ (Fin n) ↦ Real.exp (1 * -inner ℝ t x))
          (Measure.map Y (P : Measure (BoundedlyFiniteMeasure E))) := by
      exact ((measurable_const.mul hInnerMeas).exp).aestronglyMeasurable
    have hExpMeasQ :
        AEStronglyMeasurable
          (fun x : EuclideanSpace ℝ (Fin n) ↦ Real.exp (1 * -inner ℝ t x))
          (Measure.map Y (Q : Measure (BoundedlyFiniteMeasure E))) := by
      exact ((measurable_const.mul hInnerMeas).exp).aestronglyMeasurable
    let a : Fin n → ℝ≥0 := fun i ↦ ⟨t i, ht i⟩
    -- Proof comment: rewrite both mgfs back to the law-level Laplace transform at the weighted
    -- test function `∑ i, a i • fs i`.
    calc
      ProbabilityTheory.mgf (fun x ↦ -inner ℝ t x) μP 1
          = random_measure_laplace_transform P (∑ i, a i • fs i) := by
              rw [hμP_def]
              calc
                ProbabilityTheory.mgf (fun x ↦ -inner ℝ t x)
                    (Measure.map Y (P : Measure (BoundedlyFiniteMeasure E))) 1
                    =
                    ProbabilityTheory.mgf
                      (fun ν ↦ -inner ℝ t (Y ν))
                      (P : Measure (BoundedlyFiniteMeasure E)) 1 := by
                        simpa [Function.comp] using
                          (ProbabilityTheory.mgf_map
                            (μ := (P : Measure (BoundedlyFiniteMeasure E)))
                            (Y := Y)
                            (X := fun x : EuclideanSpace ℝ (Fin n) ↦ -inner ℝ t x)
                            hYmeas.aemeasurable
                            hExpMeasP)
                _ = random_measure_laplace_transform P (∑ i, a i • fs i) := by
                      rw [ProbabilityTheory.mgf, random_measure_laplace_transform]
                      refine integral_congr_ae <| Filter.Eventually.of_forall fun ν ↦ ?_
                      dsimp [Y]
                      rw [innerToLpTestIntegralTupleEqWeightedProbe (E := E) fs t ν,
                        ← BoundedlyFiniteMeasure.nonnegativeVagueIntegral_apply,
                        nonnegativeVagueIntegralWeightedSum (E := E) fs a ν]
                      simp [a]
      _ = random_measure_laplace_transform Q (∑ i, a i • fs i) := hLaplace _
      _ = ProbabilityTheory.mgf (fun x ↦ -inner ℝ t x) μQ 1 := by
            rw [hμQ_def]
            calc
              random_measure_laplace_transform Q (∑ i, a i • fs i)
                  = ProbabilityTheory.mgf
                      (fun ν ↦ -inner ℝ t (Y ν))
                      (Q : Measure (BoundedlyFiniteMeasure E)) 1 := by
                        rw [ProbabilityTheory.mgf, random_measure_laplace_transform]
                        refine integral_congr_ae <| Filter.Eventually.of_forall fun ν ↦ ?_
                        dsimp [Y]
                        rw [innerToLpTestIntegralTupleEqWeightedProbe (E := E) fs t ν,
                          ← BoundedlyFiniteMeasure.nonnegativeVagueIntegral_apply,
                          nonnegativeVagueIntegralWeightedSum (E := E) fs a ν]
                        simp [a]
              _ = ProbabilityTheory.mgf (fun x ↦ -inner ℝ t x)
                    (Measure.map Y (Q : Measure (BoundedlyFiniteMeasure E))) 1 := by
                        simpa [Function.comp] using
                          (ProbabilityTheory.mgf_map
                            (μ := (Q : Measure (BoundedlyFiniteMeasure E)))
                            (Y := Y)
                            (X := fun x : EuclideanSpace ℝ (Fin n) ↦ -inner ℝ t x)
                            hYmeas.aemeasurable
                            hExpMeasQ).symm
  have hμeq : μP = μQ :=
    eq_of_laplaceTransform_eq_on_nonnegativeOrthant
      (d := n) (μ := μP) (ν := μQ) hμP_nonneg hμQ_nonneg hmgf
  -- Proof comment: pull the transported-law equality back through the measurable equivalence.
  refine (MeasurableEquiv.toLp 2 (Fin n → ℝ)).map_measurableEquiv_injective ?_
  calc
    Measure.map (MeasurableEquiv.toLp 2 (Fin n → ℝ))
        (Measure.map (random_measure_test_integral_tuple fs)
          (P : Measure (BoundedlyFiniteMeasure E)))
        = μP := (tupleLawMapToLpEq (E := E) fs P).symm
    _ = μQ := hμeq
    _ =
        Measure.map (MeasurableEquiv.toLp 2 (Fin n → ℝ))
          (Measure.map (random_measure_test_integral_tuple fs)
            (Q : Measure (BoundedlyFiniteMeasure E))) := tupleLawMapToLpEq (E := E) fs Q

/-- Theorem 24.7 (1): the distribution of a random measure is determined by its Laplace transform
`f ↦ random_measure_laplace_transform P f` on `C_c^+(E)`. -/
theorem random_measure_distribution_ext_iff_laplace_transform_eq
    (P Q : ProbabilityMeasure (BoundedlyFiniteMeasure E)) :
    P = Q ↔
      ∀ f : C_c(E, ℝ≥0),
        random_measure_laplace_transform P f = random_measure_laplace_transform Q f :=
by
  constructor
  · intro hPQ f
    -- Proof comment: identical laws have identical expectations of every Laplace kernel.
    simpa [hPQ]
  · intro hLaplace
    -- Proof comment: first upgrade the one-function Laplace agreement to equality of every finite
    -- tuple law, then invoke Theorem 24.5.
    refine
      random_measure_law_eq_of_integral_or_disjoint_set_finite_dimensional_distributions
        (E := E) (P := P) (Q := Q) ?_
    left
    exact testIntegralTupleLawEqOfLaplaceAgreement (E := E) P Q hLaplace

-- Proof sketch: for each real-valued test function `f`, apply
-- `MeasureTheory.Measure.ext_of_charFun` to the pushforward laws of `μ ↦ ∫ f dμ`; then use
-- `random_measure_law_eq_of_integral_or_disjoint_set_finite_dimensional_distributions`.
/-- Theorem 24.7 (2): the distribution of a random measure is determined by its characteristic
function `f ↦ random_measure_characteristic_function P f` on `C_c(E)`. -/
theorem random_measure_distribution_ext_iff_characteristic_function_eq
    (P Q : ProbabilityMeasure (BoundedlyFiniteMeasure E)) :
    P = Q ↔
      ∀ f : C_c(E, ℝ),
        random_measure_characteristic_function P f =
          random_measure_characteristic_function Q f :=
by
  constructor
  · intro hPQ f
    -- Proof comment: identical laws have identical expectations of every Fourier kernel.
    simpa [hPQ]
  · intro hChar
    -- Proof comment: equality of all one-function characteristic values determines every finite
    -- tuple law, and Theorem 24.5 promotes that to equality of the full random-measure laws.
    refine
      random_measure_law_eq_of_integral_or_disjoint_set_finite_dimensional_distributions
        (E := E) (P := P) (Q := Q) ?_
    left
    exact testIntegralTupleLawEqOfCharacteristicAgreement (E := E) P Q hChar

end ChapterAmbient

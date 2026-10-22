/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Exercise_15_1_3Basic

open MeasureTheory
open BoundedContinuousFunction

open scoped BigOperators
open scoped Pointwise
open scoped RealInnerProductSpace

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Helper for Exercise 15.1.3: the torus pullback of `charFun (μ.map latticeEmbedding)` is in
`L²(UnitAddTorus (Fin d))`. -/
lemma latticeTorusChar_memLp {d : ℕ} (μ : Measure (Fin d → ℤ)) [IsFiniteMeasure μ] :
    MemLp (latticeTorusChar (d := d) μ) 2 volume :=
by
  have hchart : Measurable (latticeTorusChartRescaled d) :=
    latticeTorusChartRescaled_measurable
  have haestrongly :
      AEStronglyMeasurable (latticeTorusChar (d := d) μ) volume := by
    -- Proof comment: once the torus chart is packaged as a measurable map, `latticeTorusChar`
    -- inherits strong measurability from the owner characteristic function.
    have hstrong : StronglyMeasurable (charFun (μ.map latticeEmbedding)) :=
      MeasureTheory.stronglyMeasurable_charFun (μ := μ.map latticeEmbedding)
    exact (hstrong.comp_measurable hchart).aestronglyMeasurable
  -- Proof comment: the characteristic function is uniformly bounded by the total mass, so the
  -- finite-measure `MemLp.of_bound` criterion applies.
  refine MemLp.of_bound haestrongly ((μ.map latticeEmbedding).real Set.univ) ?_
  filter_upwards with u
  simpa [latticeTorusChar] using
    (MeasureTheory.norm_charFun_le (μ := μ.map latticeEmbedding) (latticeTorusChartRescaled d u))

/-- Helper for Exercise 15.1.3: the torus pullback of the characteristic function packaged as an
`L²` function. -/
noncomputable abbrev latticeTorusLp {d : ℕ} (μ : Measure (Fin d → ℤ)) [IsFiniteMeasure μ] :
    Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d))) :=
  (latticeTorusChar_memLp (d := d) μ).toLp (latticeTorusChar (d := d) μ)

/-- Helper for Exercise 15.1.3: the singleton masses of a finite lattice measure form a summable
family. -/
lemma summable_latticeSingletonMass {d : ℕ} (μ : Measure (Fin d → ℤ)) [IsFiniteMeasure μ] :
    Summable (fun x : Fin d → ℤ => μ.real ({x} : Set (Fin d → ℤ))) := by
  have htsum_eq :
      (∑' x : Fin d → ℤ, μ ({x} : Set (Fin d → ℤ))) = μ Set.univ := by
    simpa using
      ((μ : Measure (Fin d → ℤ)).tsum_indicator_apply_singleton Set.univ MeasurableSet.univ)
  have htsum : (∑' x : Fin d → ℤ, μ ({x} : Set (Fin d → ℤ))) ≠ ⊤ := by
    rw [htsum_eq]
    exact measure_ne_top μ Set.univ
  -- Proof comment: the singleton masses are summable because their `ENNReal` sum is the finite
  -- total mass of `μ`, and `measureReal` is just `toReal`.
  simpa [MeasureTheory.measureReal_def] using
    (ENNReal.summable_toReal htsum :
      Summable (fun x : Fin d → ℤ => (μ ({x} : Set (Fin d → ℤ))).toReal))

/-- Helper for Exercise 15.1.3: the squared singleton masses of a finite lattice measure form a
summable family. -/
lemma summable_latticeSingletonMassSq {d : ℕ} (μ : Measure (Fin d → ℤ)) [IsFiniteMeasure μ] :
    Summable (fun x : Fin d → ℤ => μ.real ({x} : Set (Fin d → ℤ)) ^ 2) := by
  let totalMass : ℝ := μ.real Set.univ
  have hmass : Summable (fun x : Fin d → ℤ => μ.real ({x} : Set (Fin d → ℤ))) :=
    summable_latticeSingletonMass (d := d) μ
  refine (hmass.mul_left totalMass).of_nonneg_of_le ?_ ?_
  · intro x
    positivity
  · intro x
    have hnonneg : 0 ≤ μ.real ({x} : Set (Fin d → ℤ)) := MeasureTheory.measureReal_nonneg
    have hle :
        μ.real ({x} : Set (Fin d → ℤ)) ≤ totalMass := by
      simpa [totalMass] using
        (MeasureTheory.measureReal_mono (show ({x} : Set (Fin d → ℤ)) ⊆ Set.univ by simp))
    -- Proof comment: each singleton mass is bounded by the total mass, so `a^2 ≤ totalMass * a`.
    rw [pow_two]
    nlinarith

/-- Helper for Exercise 15.1.3: the singleton masses define an `ℓ²` coefficient family on
`ℤ^d`. -/
lemma latticeSingletonMass_memℓ2 {d : ℕ} (μ : Measure (Fin d → ℤ)) [IsFiniteMeasure μ] :
    Memℓp (fun x : Fin d → ℤ => (μ.real ({x} : Set (Fin d → ℤ)) : ℂ)) 2 := by
  refine memℓp_gen ?_
  -- Proof comment: the `ℓ²` norm is exactly the summable family of squared singleton masses.
  simpa [Complex.norm_real, MeasureTheory.measureReal_nonneg] using
    summable_latticeSingletonMassSq (d := d) μ

/-- Helper for Exercise 15.1.3: the singleton masses packaged as an `ℓ²(ℤ^d, ℂ)` vector. -/
noncomputable def latticeSingletonMassℓ2 {d : ℕ} (μ : Measure (Fin d → ℤ)) [IsFiniteMeasure μ] :
    ℓ²(Fin d → ℤ, ℂ) :=
  ⟨fun x ↦ (μ.real ({x} : Set (Fin d → ℤ)) : ℂ), latticeSingletonMass_memℓ2 (d := d) μ⟩

/-- Helper for Exercise 15.1.3: the coordinate half cube `(-1 / 2, 1 / 2]^d` is measurable. -/
lemma measurableSet_coordinateHalfCube (d : ℕ) : MeasurableSet (coordinateHalfCube d) := by
  unfold coordinateHalfCube
  rw [Set.setOf_forall]
  exact MeasurableSet.iInter fun i : Fin d ↦
    (continuous_apply i).measurable measurableSet_Ioc

/-- Helper for Exercise 15.1.3: the lattice singleton masses define a summable Fourier series on
`UnitAddTorus (Fin d)`. -/
lemma summable_latticeTorusFourierTerms {d : ℕ} (μ : Measure (Fin d → ℤ)) [IsFiniteMeasure μ] :
    Summable
      (fun x : Fin d → ℤ => (μ.real ({x} : Set (Fin d → ℤ)) : ℂ) • UnitAddTorus.mFourier x) := by
  -- Proof comment: `mFourier x` has unit norm, so summability reduces to the summable singleton
  -- masses.
  refine Summable.of_norm_bounded (summable_latticeSingletonMass (d := d) μ) ?_
  intro x
  have hnonneg : 0 ≤ μ.real ({x} : Set (Fin d → ℤ)) := MeasureTheory.measureReal_nonneg
  rw [norm_smul, UnitAddTorus.mFourier_norm, mul_one, Complex.norm_real]
  simp [abs_of_nonneg hnonneg]

/-- Helper for Exercise 15.1.3: the torus Fourier series with singleton-mass coefficients. -/
noncomputable def latticeTorusFourierSeries {d : ℕ} (μ : Measure (Fin d → ℤ)) [IsFiniteMeasure μ] :
    C(UnitAddTorus (Fin d), ℂ) :=
  ∑' x : Fin d → ℤ, (μ.real ({x} : Set (Fin d → ℤ)) : ℂ) • UnitAddTorus.mFourier x

/-- Helper for Exercise 15.1.3: the torus chart turns the owner kernel `innerProbChar` into the
standard torus monomial. -/
lemma innerProbChar_latticeTorusChartRescaled_eq_mFourier {d : ℕ} (u : UnitAddTorus (Fin d))
    (x : Fin d → ℤ) :
    innerProbChar (latticeTorusChartRescaled d u) (latticeEmbedding x) =
      UnitAddTorus.mFourier x u := by
  let ySub := UnitAddTorus.measurableEquivPiIoc (latticeTorusChartBase d) u
  let y : Fin d → ℝ := ySub.1
  have hy : y ∈ coordinateHalfCube d := by
    intro i
    exact ySub.2 i
  have hu :
      u = fun i ↦ (y i : UnitAddCircle) := by
    have hsymm :
        (UnitAddTorus.measurableEquivPiIoc (latticeTorusChartBase d)).symm ySub = u :=
      (UnitAddTorus.measurableEquivPiIoc (latticeTorusChartBase d)).symm_apply_apply u
    have hcoe :
        (UnitAddTorus.measurableEquivPiIoc (latticeTorusChartBase d)).symm ySub =
          fun i ↦ (y i : UnitAddCircle) := by
      dsimp [y]
    exact hsymm.symm.trans hcoe
  -- Proof comment: evaluate the chart on its preferred representative and reuse the already
  -- normalized lattice-kernel computation on the half cube.
  have hkernel := mFourierNegEvalEqLatticeKernel (d := d) (-x) y
  have hphase :
      Complex.exp (((⟪latticeEmbedding x, (2 * Real.pi) • WithLp.toLp 2 y⟫ : ℝ) * Complex.I)) =
        Complex.exp (-((⟪(2 * Real.pi) • WithLp.toLp 2 y, latticeEmbedding (-x)⟫ : ℝ) *
          Complex.I)) := by
    congr 1
    have hneg : latticeEmbedding (-x) = -(latticeEmbedding x) := by
      ext i
      simp [latticeEmbedding]
    rw [hneg, inner_neg_right, real_inner_comm]
    simp [mul_comm]
  have hkernel' :
      Complex.exp (-((⟪(2 * Real.pi) • WithLp.toLp 2 y, latticeEmbedding (-x)⟫ : ℝ) *
        Complex.I)) =
        UnitAddTorus.mFourier x (fun i ↦ (y i : UnitAddCircle)) := by
    simpa using hkernel.symm
  -- Proof comment: after commuting the real inner product and rewriting `-x`, the owner kernel
  -- has exactly the phase from the `mFourierNegEvalEqLatticeKernel` lemma.
  rw [hu, innerProbChar_apply, latticeTorusChartRescaled_apply_halfCube (d := d) hy]
  exact hphase.trans hkernel'

/-- Helper for Exercise 15.1.3: the singleton-mass Fourier series agrees pointwise with the torus
pullback `latticeTorusChar`. -/
lemma latticeTorusFourierSeries_apply_eq_latticeTorusChar {d : ℕ}
    (μ : Measure (Fin d → ℤ)) [IsFiniteMeasure μ] (u : UnitAddTorus (Fin d)) :
    latticeTorusFourierSeries (d := d) μ u = latticeTorusChar (d := d) μ u := by
  rw [latticeTorusFourierSeries]
  have htsum :
      (∑' x : Fin d → ℤ, (μ.real ({x} : Set (Fin d → ℤ)) : ℂ) • UnitAddTorus.mFourier x) u =
        ∑' x : Fin d → ℤ, ((μ.real ({x} : Set (Fin d → ℤ)) : ℂ) • UnitAddTorus.mFourier x) u := by
    simpa using (ContinuousMap.tsum_apply (summable_latticeTorusFourierTerms (d := d) μ) u).symm
  rw [htsum]
  simp only [ContinuousMap.smul_apply, smul_eq_mul]
  have hInt :
      Integrable (fun x : Fin d → ℤ =>
        innerProbChar (latticeTorusChartRescaled d u) (latticeEmbedding x)) μ := by
    refine Integrable.of_bound ((measurable_of_countable _).aestronglyMeasurable) 1 ?_
    filter_upwards with x
    rw [innerProbChar_apply]
    exact
      (show
        ‖Complex.exp (((⟪latticeEmbedding x, latticeTorusChartRescaled d u⟫ : ℝ) * Complex.I))‖ ≤ 1
        from le_of_eq (Complex.norm_exp_ofReal_mul_I _))
  have hchar :
      latticeTorusChar (d := d) μ u =
        ∑' x : Fin d → ℤ,
          μ.real ({x} : Set (Fin d → ℤ)) *
            innerProbChar (latticeTorusChartRescaled d u) (latticeEmbedding x) := by
    -- Proof comment: expand `charFun` as the countable integral of the lattice Fourier kernel.
    rw [latticeTorusChar, charFun_eq_integral_innerProbChar]
    rw [integral_map (measurable_of_countable latticeEmbedding).aemeasurable (by fun_prop)]
    simpa [smul_eq_mul] using (MeasureTheory.integral_countable (μ := μ) hInt)
  calc
    ∑' x : Fin d → ℤ, (μ.real ({x} : Set (Fin d → ℤ)) : ℂ) * UnitAddTorus.mFourier x u
        = ∑' x : Fin d → ℤ,
            μ.real ({x} : Set (Fin d → ℤ)) *
              innerProbChar (latticeTorusChartRescaled d u) (latticeEmbedding x) := by
            refine tsum_congr ?_
            intro x
            rw [innerProbChar_latticeTorusChartRescaled_eq_mFourier (d := d) u x]
    _ = latticeTorusChar (d := d) μ u := hchar.symm

/-- Helper for Exercise 15.1.3: the `L²` class of the singleton-mass Fourier series is exactly
`latticeTorusLp`. -/
lemma latticeTorusFourierSeries_toLp_eq_latticeTorusLp {d : ℕ}
    (μ : Measure (Fin d → ℤ)) [IsFiniteMeasure μ] :
    ContinuousMap.toLp (E := ℂ) 2 volume ℂ (latticeTorusFourierSeries (d := d) μ) =
      latticeTorusLp (d := d) μ := by
  apply Lp.ext
  have hleft :
      ContinuousMap.toLp (E := ℂ) 2 volume ℂ (latticeTorusFourierSeries (d := d) μ)
        =ᵐ[volume] latticeTorusChar (d := d) μ := by
    refine (ContinuousMap.coeFn_toLp volume (latticeTorusFourierSeries (d := d) μ)).trans ?_
    exact Filter.Eventually.of_forall
      (latticeTorusFourierSeries_apply_eq_latticeTorusChar (d := d) μ)
  -- Proof comment: both `Lp` representatives agree almost everywhere with `latticeTorusChar`.
  exact hleft.trans (MeasureTheory.MemLp.coeFn_toLp (latticeTorusChar_memLp (d := d) μ)).symm

/-- Helper for Exercise 15.1.3: the torus Fourier coefficient integral becomes the half-cube
integral of the rescaled characteristic function. -/
lemma mFourierCoeff_latticeTorusLp_eq_halfCubeIntegral {d : ℕ}
    (μ : Measure (Fin d → ℤ)) [IsFiniteMeasure μ] (x : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (latticeTorusLp (d := d) μ) x =
      ∫ y in coordinateHalfCube d,
        Complex.exp (-((⟪(2 * Real.pi) • WithLp.toLp 2 y, latticeEmbedding x⟫ : ℝ) *
          Complex.I)) *
          charFun (μ.map latticeEmbedding) ((2 * Real.pi) • WithLp.toLp 2 y) ∂volume := by
  rw [UnitAddTorus.mFourierCoeff]
  have hLp :
      (fun u : UnitAddTorus (Fin d) ↦
        UnitAddTorus.mFourier (-x) u • latticeTorusLp (d := d) μ u) =ᵐ[volume]
      fun u ↦ UnitAddTorus.mFourier (-x) u • latticeTorusChar (d := d) μ u := by
    filter_upwards [MeasureTheory.MemLp.coeFn_toLp (latticeTorusChar_memLp (d := d) μ)] with u hu
    simp [hu]
  rw [integral_congr_ae hLp]
  rw [UnitAddTorus.integral_preimage
    (f := fun u : UnitAddTorus (Fin d) ↦
      UnitAddTorus.mFourier (-x) u • latticeTorusChar (d := d) μ u)
    (a := latticeTorusChartBase d)]
  refine integral_congr_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_coordinateHalfCube d)]
    with y hyCube
  rw [smul_eq_mul, mFourierNegEvalEqLatticeKernel, latticeTorusChar_apply_halfCube (μ := μ) hyCube]

/-- Helper for Exercise 15.1.3: the `L²` norm of the torus pullback is the half-open cube
integral of the rescaled lattice characteristic function. -/
lemma integral_sqNorm_latticeTorusLp_eq_halfCubeIntegral {d : ℕ}
    (μ : Measure (Fin d → ℤ)) [IsFiniteMeasure μ] :
    ∫ u, ‖latticeTorusLp (d := d) μ u‖ ^ 2 =
      ∫ y in coordinateHalfCube d,
        ‖charFun (μ.map latticeEmbedding) ((2 * Real.pi) • WithLp.toLp 2 y)‖ ^ 2 ∂volume := by
  have hLp :
      ∫ u, ‖latticeTorusLp (d := d) μ u‖ ^ 2 =
        ∫ u, ‖latticeTorusChar (d := d) μ u‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [MeasureTheory.MemLp.coeFn_toLp (latticeTorusChar_memLp (d := d) μ)] with u hu
    simp [hu]
  calc
    ∫ u, ‖latticeTorusLp (d := d) μ u‖ ^ 2 = ∫ u, ‖latticeTorusChar (d := d) μ u‖ ^ 2 := hLp
    _ = ∫ y in coordinateHalfCube d,
          ‖latticeTorusChar (d := d) μ (fun i ↦ (y i : UnitAddCircle))‖ ^ 2 ∂volume := by
            simpa [coordinateHalfCube, latticeTorusChartBase] using
              (UnitAddTorus.integral_preimage
                (f := fun u : UnitAddTorus (Fin d) ↦ ‖latticeTorusChar (d := d) μ u‖ ^ 2)
                (a := latticeTorusChartBase d))
    _ = ∫ y in coordinateHalfCube d,
          ‖charFun (μ.map latticeEmbedding) ((2 * Real.pi) • WithLp.toLp 2 y)‖ ^ 2 ∂volume := by
            refine integral_congr_ae ?_
            filter_upwards [ae_restrict_mem (measurableSet_coordinateHalfCube d)] with y hyCube
            simp [latticeTorusChar_apply_halfCube (μ := μ) hyCube]

/-- Helper for Exercise 15.1.3: the torus Fourier coefficients of the pulled-back characteristic
function are the singleton masses of `μ`. -/
lemma mFourierCoeff_latticeTorusLp_eq_singletonMass {d : ℕ}
    (μ : Measure (Fin d → ℤ)) [IsFiniteMeasure μ] (x : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (latticeTorusLp (d := d) μ) x =
      (μ.real ({x} : Set (Fin d → ℤ)) : ℂ) := by
  have hsumSeries :
      HasSum
        (fun y : Fin d → ℤ =>
          (μ.real ({y} : Set (Fin d → ℤ)) : ℂ) • UnitAddTorus.mFourierLp 2 y)
        (ContinuousMap.toLp (E := ℂ) 2 volume ℂ (latticeTorusFourierSeries (d := d) μ)) := by
    -- Proof comment: push the pointwise Fourier series into `L²` through the continuous-to-`Lp`
    -- map, so Parseval's orthonormal-basis API applies directly.
    simpa [latticeTorusFourierSeries] using
      (ContinuousMap.toLp (E := ℂ) 2 volume ℂ :
        C(UnitAddTorus (Fin d), ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d)))).hasSum
        ((summable_latticeTorusFourierTerms (d := d) μ).hasSum)
  have hreprSeries :
      HasSum
        (fun y : Fin d → ℤ =>
          (latticeSingletonMassℓ2 (d := d) μ y) • UnitAddTorus.mFourierLp 2 y)
        ((UnitAddTorus.mFourierBasis (d := Fin d)).repr.symm
          (latticeSingletonMassℓ2 (d := d) μ)) := by
    -- Proof comment: the torus Fourier basis reconstructs an `ℓ²` vector from its coordinates.
    simpa [UnitAddTorus.coe_mFourierBasis, latticeSingletonMassℓ2] using
      (UnitAddTorus.mFourierBasis (d := Fin d)).hasSum_repr_symm
        (latticeSingletonMassℓ2 (d := d) μ)
  have hseriesEq :
      ContinuousMap.toLp (E := ℂ) 2 volume ℂ (latticeTorusFourierSeries (d := d) μ) =
        (UnitAddTorus.mFourierBasis (d := Fin d)).repr.symm (latticeSingletonMassℓ2 (d := d) μ) :=
    hsumSeries.unique hreprSeries
  -- Route correction: replace the brittle half-cube transport proof by the canonical Fourier-basis
  -- route, where the coefficient is read off from the `ℓ²` coordinate vector.
  calc
    UnitAddTorus.mFourierCoeff (latticeTorusLp (d := d) μ) x
        = UnitAddTorus.mFourierCoeff
            (ContinuousMap.toLp (E := ℂ) 2 volume ℂ (latticeTorusFourierSeries (d := d) μ)) x := by
              rw [latticeTorusFourierSeries_toLp_eq_latticeTorusLp (d := d) μ]
    _ = (UnitAddTorus.mFourierBasis (d := Fin d)).repr
          ((UnitAddTorus.mFourierBasis (d := Fin d)).repr.symm
            (latticeSingletonMassℓ2 (d := d) μ)) x := by
              rw [hseriesEq, ← UnitAddTorus.mFourierBasis_repr]
    _ = latticeSingletonMassℓ2 (d := d) μ x := by
          simp
    _ = (μ.real ({x} : Set (Fin d → ℤ)) : ℂ) := rfl

/-- Helper for Exercise 15.1.3: the `L²`-norm of the torus pullback equals the normalized cube
integral of `‖charFun (μ.map latticeEmbedding)‖²`. -/
lemma integral_sqNorm_latticeTorusLp_eq_cubeIntegral {d : ℕ}
    (μ : Measure (Fin d → ℤ)) [IsFiniteMeasure μ] :
    ∫ u, ‖latticeTorusLp (d := d) μ u‖ ^ 2 =
      (((2 * Real.pi) ^ d : ℝ)⁻¹ *
        ∫ t in latticeFrequencyCube d, ‖charFun (μ.map latticeEmbedding) t‖ ^ 2 ∂volume) := by
  let iocCube : Set (Fin d → ℝ) :=
    {y : Fin d → ℝ | ∀ i, y i ∈ Set.Ioc (-Real.pi) Real.pi}
  let icoCube : Set (Fin d → ℝ) :=
    {y : Fin d → ℝ | ∀ i, y i ∈ Set.Ico (-Real.pi) Real.pi}
  let sqNormChar : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun t ↦ ‖charFun (μ.map latticeEmbedding) t‖ ^ 2
  have hrescale :
      ∫ y in coordinateHalfCube d,
          ‖charFun (μ.map latticeEmbedding) ((2 * Real.pi) • WithLp.toLp 2 y)‖ ^ 2 ∂volume =
        (((2 * Real.pi : ℝ) ^ d)⁻¹) •
          ∫ y in iocCube, sqNormChar (WithLp.toLp 2 y) ∂volume := by
    -- Proof comment: rescaling `(-1/2, 1/2]^d` by `2π` produces the Jacobian factor `((2π)^d)⁻¹`
    -- and the coordinate cube `(-π, π]^d`.
    simpa [iocCube, sqNormChar] using
      (coordinateHalfOpenCubeRescaleIntegral (d := d)
        (G := fun y : Fin d → ℝ => sqNormChar (WithLp.toLp 2 y)))
  have hiocIco :
      ∫ y in iocCube, sqNormChar (WithLp.toLp 2 y) ∂volume =
        ∫ y in icoCube, sqNormChar (WithLp.toLp 2 y) ∂volume := by
    change ∫ y, sqNormChar (WithLp.toLp 2 y) ∂(volume.restrict iocCube) =
      ∫ y, sqNormChar (WithLp.toLp 2 y) ∂(volume.restrict icoCube)
    rw [Measure.restrict_congr_set (coordinatePiIocAeEqPiIco d)]
  have hcoord :
      ∫ y in icoCube, sqNormChar (WithLp.toLp 2 y) ∂volume =
        ∫ t in latticeFrequencyCube d, sqNormChar t ∂volume := by
    -- Proof comment: the half-open coordinate cube and `latticeFrequencyCube d` are the same
    -- integral domain after the standard coordinate identification.
    simpa [icoCube, sqNormChar] using
      (coordinateIcoIntegralEqLatticeFrequencyCubeIntegral (d := d) (G := sqNormChar))
  calc
    ∫ u, ‖latticeTorusLp (d := d) μ u‖ ^ 2 =
        ∫ y in coordinateHalfCube d,
          ‖charFun (μ.map latticeEmbedding) ((2 * Real.pi) • WithLp.toLp 2 y)‖ ^ 2 ∂volume := by
            exact integral_sqNorm_latticeTorusLp_eq_halfCubeIntegral (d := d) μ
    _ = (((2 * Real.pi : ℝ) ^ d)⁻¹) • ∫ y in iocCube, sqNormChar (WithLp.toLp 2 y) ∂volume :=
          hrescale
    _ = (((2 * Real.pi : ℝ) ^ d)⁻¹) • ∫ y in icoCube, sqNormChar (WithLp.toLp 2 y) ∂volume := by
          rw [hiocIco]
    _ = (((2 * Real.pi : ℝ) ^ d)⁻¹ * ∫ t in latticeFrequencyCube d, sqNormChar t ∂volume) := by
          rw [hcoord, smul_eq_mul]
    _ = (((2 * Real.pi) ^ d : ℝ)⁻¹ *
          ∫ t in latticeFrequencyCube d, ‖charFun (μ.map latticeEmbedding) t‖ ^ 2 ∂volume) := by
          rfl

/-- Exercise 15.1.3: under the hypotheses of Theorem 15.10 for a finite measure `μ` on `ℤ^d`,
the sum of the squared singleton masses equals the normalized `L²`-norm of its characteristic
function on the fundamental domain `[-π, π)^d`. -/
theorem lattice_measure_plancherel_formula (d : ℕ) (μ : Measure (Fin d → ℤ)) [IsFiniteMeasure μ] :
    (∑' x : Fin d → ℤ, μ.real ({x} : Set (Fin d → ℤ)) ^ 2) =
      (((2 * Real.pi) ^ d : ℝ)⁻¹ *
        ∫ t in latticeFrequencyCube d, ‖charFun (μ.map latticeEmbedding) t‖ ^ 2 ∂volume) := by
  have hs :
      HasSum (fun x : Fin d → ℤ => μ.real ({x} : Set (Fin d → ℤ)) ^ 2)
        (((2 * Real.pi) ^ d : ℝ)⁻¹ *
          ∫ t in latticeFrequencyCube d, ‖charFun (μ.map latticeEmbedding) t‖ ^ 2 ∂volume) := by
    -- Route correction: the blocked support-import route is unavailable in the current build
    -- graph, so the proof uses the same Fourier-basis and norm-transport lemmas directly here.
    -- Proof comment: Parseval on `UnitAddTorus (Fin d)` gives the sum of squared Fourier
    -- coefficients, then the coefficient and norm bridge lemmas rewrite that identity into the
    -- lattice-measure statement.
    convert (UnitAddTorus.hasSum_sq_mFourierCoeff (d := Fin d) (latticeTorusLp (d := d) μ))
      using 1
    · ext x
      rw [mFourierCoeff_latticeTorusLp_eq_singletonMass]
      simp [Complex.norm_real]
    · rw [integral_sqNorm_latticeTorusLp_eq_cubeIntegral]
  -- Proof comment: `HasSum.tsum_eq` converts Parseval's series identity into the stated
  -- Plancherel formula.
  simpa using hs.tsum_eq

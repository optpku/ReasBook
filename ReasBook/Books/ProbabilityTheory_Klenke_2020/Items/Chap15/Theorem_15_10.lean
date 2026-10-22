/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped BigOperators
open scoped RealInnerProductSpace

noncomputable section

/-- The canonical embedding of the lattice `ℤ^d` into the Euclidean space `ℝ^d`. -/
abbrev latticeEmbedding {d : ℕ} (x : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i ↦ (x i : ℝ))

/-- The half-open cube `[-π, π)^d` in the coordinate model of `ℝ^d`. -/
abbrev latticeFrequencyCube (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {t | ∀ i, t i ∈ Set.Ico (-Real.pi) Real.pi}

-- Proof sketch: unfold `latticeFrequencyCube`.
/-- Membership in `latticeFrequencyCube d` means that every coordinate lies in `[-π, π)`. -/
theorem mem_latticeFrequencyCube_iff {d : ℕ} {t : EuclideanSpace ℝ (Fin d)} :
    t ∈ latticeFrequencyCube d ↔
      ∀ i, t i ∈ Set.Ico (-Real.pi) Real.pi := Iff.rfl

/-- Helper for Theorem 15.10: the lattice character on `ℝ^d` factors coordinatewise after
transporting the embedded lattice point to the `Fin d → ℝ` model. -/
lemma latticeCharacter_eq_coordProd {d : ℕ} (t : EuclideanSpace ℝ (Fin d)) (z : Fin d → ℤ) :
    Complex.exp (((⟪t, latticeEmbedding z⟫ : ℝ) * Complex.I)) =
      ∏ i, Complex.exp ((((z i : ℝ) * t i) * Complex.I)) := by
  -- Route correction: use the existing `PiLp` coordinate inner-product API directly instead of
  -- adding a custom real-inner normalization lemma.
  -- Proof comment: rewrite the Euclidean inner product as a finite coordinate sum and then turn
  -- the exponential of that sum into the product of the coordinate exponentials.
  have hphase :
      (((⟪t, latticeEmbedding z⟫ : ℝ) : ℂ) * Complex.I) =
        ∑ i : Fin d, ((((z i : ℝ) * t i) : ℂ) * Complex.I) := by
    rw [latticeEmbedding, PiLp.inner_apply, Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hcoord : ((⟪t i, (z i : ℝ)⟫ : ℝ)) = (z i : ℝ) * t i := by
      -- Proof comment: for real scalars, the coordinate inner product is ordinary multiplication.
      rw [real_inner_eq_re_inner]
      simp [RCLike.inner_apply]
    simpa using congrArg (fun r : ℝ ↦ (r : ℂ) * Complex.I) hcoord
  rw [hphase, Complex.exp_sum]

/-- Helper for Theorem 15.10: multiplying the inverse phase at `x` with the characteristic-function
phase at `y` collapses to the single lattice frequency `y - x`. -/
lemma latticeKernel_mul_charFunPhase {d : ℕ} (t : EuclideanSpace ℝ (Fin d))
    (x y : Fin d → ℤ) :
    Complex.exp (-((⟪t, latticeEmbedding x⟫ : ℝ) * Complex.I)) *
        Complex.exp (((⟪latticeEmbedding y, t⟫ : ℝ) * Complex.I)) =
      Complex.exp (((⟪t, latticeEmbedding (y - x)⟫ : ℝ) * Complex.I)) := by
  -- Proof comment: rewrite the product of phases as one exponential of a sum, then identify that
  -- sum with the inner product against the lattice difference `y - x`.
  have hsub : latticeEmbedding (y - x) = latticeEmbedding y - latticeEmbedding x := by
    ext i
    simp [latticeEmbedding, sub_eq_add_neg]
  have hinner :
      ((⟪t, latticeEmbedding (y - x)⟫ : ℝ)) =
        ((⟪t, latticeEmbedding y⟫ : ℝ)) - ((⟪t, latticeEmbedding x⟫ : ℝ)) := by
    rw [hsub, inner_sub_right]
  have hcomm : ((⟪latticeEmbedding y, t⟫ : ℝ)) = ((⟪t, latticeEmbedding y⟫ : ℝ)) := by
    simpa using real_inner_comm t (latticeEmbedding y)
  rw [hcomm, ← Complex.exp_add]
  have hphase :
      -((⟪t, latticeEmbedding x⟫ : ℝ) * Complex.I) +
          ((⟪t, latticeEmbedding y⟫ : ℝ) * Complex.I) =
        ((((⟪t, latticeEmbedding y⟫ : ℝ)) - ((⟪t, latticeEmbedding x⟫ : ℝ))) : ℂ) *
          Complex.I := by
    ring
  rw [hphase]
  congr 1
  simpa using congrArg (fun r : ℝ ↦ (r : ℂ) * Complex.I) hinner.symm

/-- Helper for Theorem 15.10: the one-dimensional lattice character integrates to `2π` at
frequency `0` and to `0` at every nonzero integer frequency. -/
lemma integral_interval_integerFrequency (n : ℤ) :
    ∫ s in Set.Ico (-Real.pi) Real.pi,
      Complex.exp ((((n : ℝ) * s) * Complex.I)) ∂volume =
        if n = 0 then (2 * Real.pi : ℂ) else 0 := by
  -- Route correction: keep the proof in interval-integral and `smul` form until
  -- `Real.sin_int_mul_pi` kills the nonzero branch.
  -- Proof comment: first convert the half-open set integral to an interval integral on `[-π, π]`.
  rw [MeasureTheory.integral_Ico_eq_integral_Ioc]
  have hpi : -Real.pi ≤ Real.pi := by
    nlinarith [Real.pi_pos]
  rw [← intervalIntegral.integral_of_le hpi]
  by_cases hn : n = 0
  · -- Proof comment: at frequency `0`, the integrand is constantly `1`.
    subst hn
    rw [if_pos rfl]
    have hzero : ((Real.pi + Real.pi : ℝ) • (1 : ℂ)) = (2 * Real.pi : ℂ) := by
      rw [Algebra.smul_def, map_add, add_mul]
      calc
        (algebraMap ℝ ℂ) Real.pi * 1 + (algebraMap ℝ ℂ) Real.pi * 1
            = (Real.pi : ℂ) + (Real.pi : ℂ) := by simp
        _ = (2 * Real.pi : ℂ) := by ring
    simpa only [Int.cast_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      intervalIntegral.integral_const, sub_neg_eq_add] using hzero
  · -- Proof comment: for nonzero frequency, rescale to the standard `exp (u I)` integral and then
    -- use the sine evaluation at an integer multiple of `π`.
    have hnr : (n : ℝ) ≠ 0 := by
      exact_mod_cast hn
    have hrescale :
        (∫ s in -Real.pi..Real.pi, Complex.exp ((((n : ℝ) * s) * Complex.I))) =
          (n : ℝ)⁻¹ •
            ∫ u in -(Real.pi * (n : ℝ))..(Real.pi * (n : ℝ)), Complex.exp (u * Complex.I) := by
      calc
        (∫ s in -Real.pi..Real.pi, Complex.exp ((((n : ℝ) * s) * Complex.I))) =
            ∫ s in -Real.pi..Real.pi, Complex.exp (Complex.I * ↑(s * (n : ℝ))) := by
              refine intervalIntegral.integral_congr_ae ?_
              filter_upwards [] with s hs
              simp [mul_comm]
        _ = (n : ℝ)⁻¹ •
              ∫ u in (-Real.pi) * (n : ℝ)..Real.pi * (n : ℝ), Complex.exp (Complex.I * ↑u) := by
              exact
                (intervalIntegral.integral_comp_mul_right
                  (f := fun u : ℝ ↦ Complex.exp (Complex.I * ↑u))
                  (a := -Real.pi) (b := Real.pi) (c := (n : ℝ)) hnr)
        _ = (n : ℝ)⁻¹ •
              ∫ u in -(Real.pi * (n : ℝ))..(Real.pi * (n : ℝ)), Complex.exp (u * Complex.I) := by
              simp [mul_comm]
    have hsin : Real.sin (Real.pi * (n : ℝ)) = 0 := by
      simpa [mul_comm] using Real.sin_int_mul_pi n
    rw [hrescale, if_neg hn, integral_exp_mul_I_eq_sin]
    simp [hsin]

/-- Helper for Theorem 15.10: the lattice frequency cube `[-π, π)^d` is measurable. -/
lemma measurableSet_latticeFrequencyCube (d : ℕ) :
    MeasurableSet (latticeFrequencyCube d) := by
  -- Proof comment: the cube is the intersection of the coordinate strips `t i ∈ [-π, π)`.
  unfold latticeFrequencyCube
  rw [Set.setOf_forall]
  exact MeasurableSet.iInter fun i : Fin d ↦
    (PiLp.continuous_apply 2 _ i).measurable measurableSet_Ico

/-- Helper for Theorem 15.10: the fundamental cube `[-π, π)^d` has volume `(2π)^d`. -/
lemma volume_latticeFrequencyCube (d : ℕ) :
    volume (latticeFrequencyCube d) = ENNReal.ofReal ((2 * Real.pi : ℝ) ^ d) := by
  let e : (Fin d → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin d) := MeasurableEquiv.toLp 2 (Fin d → ℝ)
  let box : Set (Fin d → ℝ) := {u | ∀ i, u i ∈ Set.Ico (-Real.pi) Real.pi}
  have hmap : Measure.map e (volume : Measure (Fin d → ℝ)) = volume := by
    simpa [e] using (PiLp.volume_preserving_toLp (ι := Fin d)).map_eq
  have hcube : MeasurableSet (latticeFrequencyCube d) := measurableSet_latticeFrequencyCube d
  have hbox :
      e ⁻¹' latticeFrequencyCube d = box := by
    ext u
    simp [e, box, latticeFrequencyCube, MeasurableEquiv.coe_toLp]
  have hbox_pi :
      box = Set.univ.pi fun i : Fin d ↦ Set.Ico (-Real.pi) Real.pi := by
    ext u
    simp [box]
  -- Proof comment: transport the Euclidean cube back to the coordinate function model and use the
  -- product formula for volume on rectangles.
  calc
    volume (latticeFrequencyCube d)
        = Measure.map e (volume : Measure (Fin d → ℝ)) (latticeFrequencyCube d) := by
            rw [hmap]
    _ = (volume : Measure (Fin d → ℝ)) box := by
          rw [Measure.map_apply e.measurable hcube, hbox]
    _ = (Measure.pi fun _ : Fin d ↦ (volume : Measure ℝ)) box := by
          rw [MeasureTheory.volume_pi]
    _ = ∏ i : Fin d, (volume : Measure ℝ) (Set.Ico (-Real.pi) Real.pi) := by
          rw [hbox_pi, Measure.pi_pi]
    _ = ENNReal.ofReal ((2 * Real.pi : ℝ) ^ d) := by
          calc
            ∏ i : Fin d, (volume : Measure ℝ) (Set.Ico (-Real.pi) Real.pi)
                = (ENNReal.ofReal (Real.pi + Real.pi)) ^ d := by
                    simp [Real.volume_Ico, Finset.prod_const]
            _ = (ENNReal.ofReal (2 * Real.pi)) ^ d := by
                  congr 1
                  ring
            _ = ENNReal.ofReal ((2 * Real.pi : ℝ) ^ d) := by
                  rw [ENNReal.ofReal_pow (by positivity)]

/-- Helper for Theorem 15.10: `WithLp.toLp` transports the coordinate cube `[-π, π)^d` to
`latticeFrequencyCube d` without changing the set integral. -/
lemma coordinateIcoIntegralEqLatticeFrequencyCubeIntegral {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (G : EuclideanSpace ℝ (Fin d) → E) :
    ∫ x in ({x : Fin d → ℝ | ∀ i, x i ∈ Set.Ico (-Real.pi) Real.pi} : Set (Fin d → ℝ)),
      G (WithLp.toLp 2 x) ∂volume =
        ∫ t in latticeFrequencyCube d, G t ∂volume := by
  let piCube : Set (Fin d → ℝ) :=
    {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ico (-Real.pi) Real.pi}
  have himage : (WithLp.toLp 2) '' piCube = latticeFrequencyCube d := by
    -- Proof comment: in coordinates, `WithLp.toLp` acts as the identity map.
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [piCube, latticeFrequencyCube] using hx
    · intro ht
      refine ⟨fun i ↦ t i, ?_, ?_⟩
      · simpa [piCube, latticeFrequencyCube] using ht
      · ext i
        rfl
  -- Proof comment: move the integral through the measure-preserving coordinate/euclidean
  -- equivalence and then rewrite the image cube.
  calc
    ∫ x in piCube, G (WithLp.toLp 2 x) ∂volume =
        ∫ t in (WithLp.toLp 2) '' piCube, G t ∂volume := by
          symm
          simpa [piCube] using
            (MeasurePreserving.setIntegral_image_emb
              (h₁ := PiLp.volume_preserving_toLp (ι := Fin d))
              (h₂ := (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding)
              (g := G) (s := piCube))
    _ = ∫ t in latticeFrequencyCube d, G t ∂volume := by
          rw [himage]

/-- Helper for Theorem 15.10: restricting coordinate volume to the half-open cube gives the
product of the one-dimensional restricted interval volumes. -/
lemma coordinateIcoRestrict_eq_pi {d : ℕ} :
    ((volume : Measure (Fin d → ℝ)).restrict
      ({u : Fin d → ℝ | ∀ i, u i ∈ Set.Ico (-Real.pi) Real.pi} : Set (Fin d → ℝ))) =
      Measure.pi (fun _ : Fin d ↦ (volume : Measure ℝ).restrict (Set.Ico (-Real.pi) Real.pi)) := by
  -- Proof comment: rewrite coordinate volume as a product measure and then restrict the box in one
  -- owner-level step via `restrict_pi_pi`.
  rw [MeasureTheory.volume_pi]
  simpa [Set.pi, Set.setOf_forall] using
    (Measure.restrict_pi_pi
      (μ := fun _ : Fin d ↦ (volume : Measure ℝ))
      (s := fun _ : Fin d ↦ Set.Ico (-Real.pi) Real.pi))

/-- Helper for Theorem 15.10: the lattice character of frequency `z` is orthogonal on
`[-π, π)^d`, so only the zero frequency survives the cube integral. -/
lemma integral_latticeFrequencyCube_character {d : ℕ} (z : Fin d → ℤ) :
    ∫ t in latticeFrequencyCube d,
      Complex.exp (((⟪t, latticeEmbedding z⟫ : ℝ) * Complex.I)) ∂volume =
        if z = 0 then (((2 * Real.pi : ℝ) ^ d : ℝ) : ℂ) else 0 := by
  -- Route correction: keep the proof in the coordinate product-measure model once the cube has
  -- been transported there, and factor the character with the closed 1D orthogonality lemma.
  rw [← coordinateIcoIntegralEqLatticeFrequencyCubeIntegral
    (d := d)
    (G := fun t : EuclideanSpace ℝ (Fin d) ↦
      Complex.exp (((⟪t, latticeEmbedding z⟫ : ℝ) * Complex.I)))]
  -- Proof comment: rewrite the set integral as an integral against the restricted product measure.
  simp_rw [latticeCharacter_eq_coordProd]
  change
    ∫ u, ∏ i, Complex.exp ((((z i : ℝ) * u i) * Complex.I)) ∂
        ((volume : Measure (Fin d → ℝ)).restrict
          ({u : Fin d → ℝ | ∀ i, u i ∈ Set.Ico (-Real.pi) Real.pi} : Set (Fin d → ℝ))) =
      if z = 0 then (((2 * Real.pi : ℝ) ^ d : ℝ) : ℂ) else 0
  rw [coordinateIcoRestrict_eq_pi]
  have hprod :
      (∫ u : Fin d → ℝ,
          ∏ i, Complex.exp ((((z i : ℝ) * u i) * Complex.I)) ∂
            Measure.pi
              (fun _ : Fin d ↦ (volume : Measure ℝ).restrict (Set.Ico (-Real.pi) Real.pi))) =
        ∏ i : Fin d,
          ∫ s, Complex.exp ((((z i : ℝ) * s) * Complex.I))
            ∂((volume : Measure ℝ).restrict (Set.Ico (-Real.pi) Real.pi)) := by
    simpa using
      (MeasureTheory.integral_fintype_prod_eq_prod
        (f := fun i ↦ fun s : ℝ ↦ Complex.exp ((((z i : ℝ) * s) * Complex.I)))
        (μ := fun _ : Fin d ↦ (volume : Measure ℝ).restrict (Set.Ico (-Real.pi) Real.pi)))
  rw [hprod]
  have hcoord :
      ∀ i : Fin d,
        ∫ s, Complex.exp ((((z i : ℝ) * s) * Complex.I))
            ∂((volume : Measure ℝ).restrict (Set.Ico (-Real.pi) Real.pi)) =
          if z i = 0 then (2 * Real.pi : ℂ) else 0 := by
    intro i
    simpa using integral_interval_integerFrequency (z i)
  simp_rw [hcoord]
  by_cases hz : z = 0
  · -- Proof comment: at zero frequency every coordinate contributes the same `2π` factor.
    subst hz
    simp [Finset.prod_const]
  · -- Proof comment: a nonzero lattice vector has a nonzero coordinate, and that factor vanishes.
    rw [if_neg hz]
    have hzcoord : ∃ i, z i ≠ 0 := by
      by_contra h
      push Not at h
      apply hz
      ext i
      exact h i
    obtain ⟨i, hi⟩ := hzcoord
    exact Finset.prod_eq_zero_iff.mpr ⟨i, Finset.mem_univ i, by simp [hi]⟩

/-- Helper for Theorem 15.10: after expanding the characteristic function and swapping the order of
integration, the cube integral becomes a `μ`-integral of lattice characters. -/
lemma cubeIntegral_mul_charFun_eq_measureIntegral {d : ℕ}
    {μ : Measure (Fin d → ℤ)} [IsFiniteMeasure μ] (x : Fin d → ℤ) :
    ∫ t in latticeFrequencyCube d,
      Complex.exp (-((⟪t, latticeEmbedding x⟫ : ℝ) * Complex.I)) *
        charFun (μ.map latticeEmbedding) t ∂volume
      =
        ∫ y,
          ∫ t in latticeFrequencyCube d,
            Complex.exp (((⟪t, latticeEmbedding (y - x)⟫ : ℝ) * Complex.I)) ∂volume ∂μ := by
  let ν : Measure (EuclideanSpace ℝ (Fin d)) := volume.restrict (latticeFrequencyCube d)
  let kernel : EuclideanSpace ℝ (Fin d) → (Fin d → ℤ) → ℂ :=
    fun t y ↦
      Complex.exp (-((⟪t, latticeEmbedding x⟫ : ℝ) * Complex.I)) *
        Complex.exp (((⟪latticeEmbedding y, t⟫ : ℝ) * Complex.I))
  haveI : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [show ν Set.univ = volume (latticeFrequencyCube d) by
      simp [ν]]
    rw [volume_latticeFrequencyCube]
    simp
  have hchar (t : EuclideanSpace ℝ (Fin d)) :
      charFun (μ.map latticeEmbedding) t =
        ∫ y, Complex.exp (((⟪latticeEmbedding y, t⟫ : ℝ) * Complex.I)) ∂μ := by
    rw [MeasureTheory.charFun_apply]
    simpa using
      (MeasureTheory.integral_map
        (μ := μ) (φ := latticeEmbedding)
        (f := fun y : EuclideanSpace ℝ (Fin d) ↦
          Complex.exp (((⟪y, t⟫ : ℝ) * Complex.I)))
        (measurable_of_countable latticeEmbedding).aemeasurable
        ((show Measurable fun y : EuclideanSpace ℝ (Fin d) ↦
            Complex.exp (((⟪y, t⟫ : ℝ) * Complex.I)) by
          fun_prop).aestronglyMeasurable))
  have hmeasKernel : Measurable (Function.uncurry kernel) := by
    have hmeasEmbedding :
        Measurable (latticeEmbedding : (Fin d → ℤ) → EuclideanSpace ℝ (Fin d)) :=
      measurable_of_countable latticeEmbedding
    dsimp [Function.uncurry, kernel]
    fun_prop
  have hkernel :
      Integrable (Function.uncurry kernel) (ν.prod μ) := by
    refine Integrable.of_bound hmeasKernel.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun p ↦ by
      rcases p with ⟨t, y⟩
      have hnormLeft :
          ‖Complex.exp (-((⟪t, latticeEmbedding x⟫ : ℝ) * Complex.I))‖ = 1 := by
        simpa [neg_mul] using Complex.norm_exp_ofReal_mul_I (-((⟪t, latticeEmbedding x⟫ : ℝ)))
      have hnormRight :
          ‖Complex.exp (((⟪latticeEmbedding y, t⟫ : ℝ) * Complex.I))‖ = 1 := by
        exact Complex.norm_exp_ofReal_mul_I ((⟪latticeEmbedding y, t⟫ : ℝ))
      change
        ‖Complex.exp (-((⟪t, latticeEmbedding x⟫ : ℝ) * Complex.I)) *
            Complex.exp (((⟪latticeEmbedding y, t⟫ : ℝ) * Complex.I))‖ ≤ 1
      rw [norm_mul, hnormLeft, hnormRight]
      norm_num
  -- Proof comment: first expand the characteristic function into a `μ`-integral of phases.
  change
    ∫ t,
      Complex.exp (-((⟪t, latticeEmbedding x⟫ : ℝ) * Complex.I)) *
        charFun (μ.map latticeEmbedding) t ∂ν
      =
        ∫ y,
          ∫ t, Complex.exp (((⟪t, latticeEmbedding (y - x)⟫ : ℝ) * Complex.I)) ∂ν ∂μ
  have hlhs :
      ∫ t,
        Complex.exp (-((⟪t, latticeEmbedding x⟫ : ℝ) * Complex.I)) *
          charFun (μ.map latticeEmbedding) t ∂ν
        =
          ∫ t, ∫ y, kernel t y ∂μ ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [] with t
    calc
      Complex.exp (-((⟪t, latticeEmbedding x⟫ : ℝ) * Complex.I)) *
          charFun (μ.map latticeEmbedding) t
          =
            Complex.exp (-((⟪t, latticeEmbedding x⟫ : ℝ) * Complex.I)) *
              ∫ y, Complex.exp (((⟪latticeEmbedding y, t⟫ : ℝ) * Complex.I)) ∂μ := by
                rw [hchar t]
      _ = ∫ y, kernel t y ∂μ := by
            simpa [kernel] using
              (MeasureTheory.integral_const_mul
                (μ := μ)
                (r := Complex.exp (-((⟪t, latticeEmbedding x⟫ : ℝ) * Complex.I)))
                (f := fun y : Fin d → ℤ ↦
                  Complex.exp (((⟪latticeEmbedding y, t⟫ : ℝ) * Complex.I)))).symm
  have hrhs :
      ∫ y, ∫ t, kernel t y ∂ν ∂μ
        =
          ∫ y,
            ∫ t, Complex.exp (((⟪t, latticeEmbedding (y - x)⟫ : ℝ) * Complex.I)) ∂ν ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [] with y
    refine integral_congr_ae ?_
    filter_upwards [] with t
    simpa [kernel] using latticeKernel_mul_charFunPhase t x y
  exact hlhs.trans <| (MeasureTheory.integral_integral_swap (μ := ν) (ν := μ) hkernel).trans hrhs

-- Proof sketch: view `μ` as a finite measure on `EuclideanSpace ℝ (Fin d)` via
-- `latticeEmbedding`, expand the characteristic function there, and integrate the exponential
-- kernel over the half-open fundamental domain `[-π, π)^d`; the orthogonality of the exponentials
-- kills every lattice point except `x`.
/-- Theorem 15.10: the point mass of a finite measure on `ℤ^d` at `x` is recovered from its
characteristic function by integrating `exp (-i⟪t, x⟫) φ_μ(t)` over `[-π, π)^d`. -/
theorem discreteFourierInversionFormula {d : ℕ} {μ : Measure (Fin d → ℤ)} [IsFiniteMeasure μ]
    (x : Fin d → ℤ) :
    (μ.real ({x} : Set (Fin d → ℤ)) : ℂ) =
      (((2 * Real.pi : ℝ) ^ d)⁻¹ : ℂ) *
        ∫ t in latticeFrequencyCube d,
          Complex.exp (-((⟪t, latticeEmbedding x⟫ : ℝ) * Complex.I)) *
            charFun (μ.map latticeEmbedding) t ∂volume := by
  let c : ℂ := (((2 * Real.pi : ℝ) ^ d : ℝ) : ℂ)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast pow_ne_zero d (show (2 * Real.pi : ℝ) ≠ 0 by positivity)
  -- Proof comment: expand the characteristic function integral, collapse the inner cube integral
  -- by orthogonality, and identify the surviving term with the singleton indicator of `{x}`.
  rw [cubeIntegral_mul_charFun_eq_measureIntegral]
  simp_rw [integral_latticeFrequencyCube_character]
  have hindicator :
      (fun y : Fin d → ℤ ↦ if y - x = 0 then c else 0) =
        Set.indicator ({x} : Set (Fin d → ℤ)) (fun _ ↦ c) := by
    funext y
    by_cases hy : y = x
    · subst hy
      simp
    · simp [hy, sub_eq_zero]
  rw [hindicator, MeasureTheory.integral_indicator_const c (measurableSet_singleton x)]
  calc
    (μ.real ({x} : Set (Fin d → ℤ)) : ℂ)
        = (c⁻¹ * c) * (μ.real ({x} : Set (Fin d → ℤ)) : ℂ) := by
            simp [hc]
    _ = c⁻¹ * ((μ.real ({x} : Set (Fin d → ℤ)) : ℂ) * c) := by
          ring
    _ = (((2 * Real.pi : ℝ) ^ d)⁻¹ : ℂ) * (μ.real ({x} : Set (Fin d → ℤ))) • c := by
          simp [c, Algebra.smul_def, mul_comm]

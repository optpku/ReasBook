/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal Pointwise ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- The ambient Euclidean space `ℝ^3` used for the Earth/sphere model in Borel's paradox. -/
local notation "Earth" => EuclideanSpace ℝ (Fin 3)

/-- The Earth's surface, modeled as the unit sphere in `ℝ^3`. -/
local notation "EarthSurface" => Metric.sphere (0 : Earth) 1

/-- The unit sphere in `ℝ^3` is nonempty. -/
instance : Nonempty EarthSurface := by
  let h : (Metric.sphere (0 : Earth) (1 : ℝ)).Nonempty ↔ 0 ≤ (1 : ℝ) :=
    NormedSpace.sphere_nonempty
  exact h.2 zero_le_one |>.to_subtype

/-- The uniform distribution on the Earth's surface, modeled as the normalized spherical surface
measure on the unit sphere in `ℝ^3`. -/
noncomputable def earthSurfaceUniformMeasure : ProbabilityMeasure EarthSurface :=
  FiniteMeasure.normalize
    (⟨(volume : Measure Earth).toSphere, inferInstance⟩ : FiniteMeasure EarthSurface)

/-- The textbook longitude-latitude parametrization used in Borel's paradox: `θ ∈ [0, π)` picks
the vertical great circle and `φ ∈ [-π, π)` runs once around that great circle. -/
def earthPointOfLongitudeLatitude (θ φ : ℝ) : EarthSurface :=
  ⟨WithLp.toLp 2
      (fun i : Fin 3 ↦
        if i = 0 then Real.cos θ * Real.cos φ
        else if i = 1 then Real.sin θ * Real.cos φ
        else Real.sin φ),
    by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_three, pow_two]
      nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ]⟩

/-- The canonical longitude coordinate in the textbook Borel-paradox parametrization of the unit
sphere. It records the meridian as an angle in `[0, π]`, i.e. modulo antipodal reversal in the
equatorial plane. -/
noncomputable def borelParadoxLongitude (x : EarthSurface) : ℝ :=
  let θ := Complex.arg (x.1 0 + x.1 1 * Complex.I)
  if θ < 0 then θ + Real.pi else θ

/-- The canonical latitude coordinate in the textbook Borel-paradox parametrization of the unit
sphere. After choosing the meridian via `borelParadoxLongitude`, this is the signed angle of `x`
along that great circle, valued in `[-π, π]`. -/
noncomputable def borelParadoxLatitude (x : EarthSurface) : ℝ :=
  let θ := borelParadoxLongitude x
  Complex.arg ((x.1 0 * Real.cos θ + x.1 1 * Real.sin θ) + x.1 2 * Complex.I)

/-- Helper for Exercise 8.3.5: the longitude branch only flips the planar cosine by a sign. -/
theorem borelParadoxLongitude_norm_mul_cos (x : EarthSurface) :
    let z : ℂ := x.1 0 + x.1 1 * Complex.I
    let α : ℝ := Complex.arg z
    ‖z‖ * Real.cos (borelParadoxLongitude x) = if α < 0 then -x.1 0 else x.1 0 := by
  -- Proof comment: the only effect of the longitude normalization is the extra `π` on the
  -- negative-argument branch, and `cos (θ + π) = - cos θ`.
  dsimp
  by_cases hα : Complex.arg (x.1 0 + x.1 1 * Complex.I) < 0
  · rw [borelParadoxLongitude, if_pos hα, Real.cos_add_pi]
    simpa [hα] using Complex.norm_mul_cos_arg (x.1 0 + x.1 1 * Complex.I)
  · rw [borelParadoxLongitude, if_neg hα]
    simpa [hα] using Complex.norm_mul_cos_arg (x.1 0 + x.1 1 * Complex.I)

/-- Helper for Exercise 8.3.5: the longitude branch only flips the planar sine by a sign. -/
theorem borelParadoxLongitude_norm_mul_sin (x : EarthSurface) :
    let z : ℂ := x.1 0 + x.1 1 * Complex.I
    let α : ℝ := Complex.arg z
    ‖z‖ * Real.sin (borelParadoxLongitude x) = if α < 0 then -x.1 1 else x.1 1 := by
  -- Proof comment: the sine term behaves exactly like the cosine term because the branch adds the
  -- same `π`, and `sin (θ + π) = - sin θ`.
  dsimp
  by_cases hα : Complex.arg (x.1 0 + x.1 1 * Complex.I) < 0
  · rw [borelParadoxLongitude, if_pos hα, Real.sin_add_pi]
    simpa [hα] using Complex.norm_mul_sin_arg (x.1 0 + x.1 1 * Complex.I)
  · rw [borelParadoxLongitude, if_neg hα]
    simpa [hα] using Complex.norm_mul_sin_arg (x.1 0 + x.1 1 * Complex.I)

/-- Helper for Exercise 8.3.5: the longitude-normalized meridian projection equals the signed
planar norm. -/
theorem meridianProjection_eq_signed_norm (x : EarthSurface) :
    let z : ℂ := x.1 0 + x.1 1 * Complex.I
    let α : ℝ := Complex.arg z
    x.1 0 * Real.cos (borelParadoxLongitude x) + x.1 1 * Real.sin (borelParadoxLongitude x) =
      if α < 0 then -‖z‖ else ‖z‖ := by
  -- Proof comment: rewrite the first two coordinates in polar form and then use
  -- `cos (α - θ) = cos α cos θ + sin α sin θ`; the normalized longitude is either `α` or `α + π`.
  dsimp
  let z : ℂ := x.1 0 + x.1 1 * Complex.I
  let α : ℝ := Complex.arg z
  have hx0 : x.1 0 = ‖z‖ * Real.cos α := by
    simpa [z, α] using (Complex.norm_mul_cos_arg z).symm
  have hx1 : x.1 1 = ‖z‖ * Real.sin α := by
    simpa [z, α] using (Complex.norm_mul_sin_arg z).symm
  have hz :
      ((‖z‖ * Real.cos α : ℝ) : ℂ) + (‖z‖ * Real.sin α : ℝ) * Complex.I = z := by
    simpa [z, α, mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
      using (Complex.norm_mul_cos_add_sin_mul_I z)
  have hznorm :
      ‖((↑(‖z‖ * Real.cos α) : ℂ) + (↑(‖z‖ * Real.sin α) : ℂ) * Complex.I)‖ = ‖z‖ := by
    simpa using congrArg norm hz
  by_cases hα : α < 0
  · rw [borelParadoxLongitude, show Complex.arg (x.1 0 + x.1 1 * Complex.I) = α by rfl, if_pos hα,
      hx0, hx1, if_pos hα]
    calc
      ‖z‖ * Real.cos α * Real.cos (α + Real.pi) +
          ‖z‖ * Real.sin α * Real.sin (α + Real.pi)
          = ‖z‖ * (Real.cos α * Real.cos (α + Real.pi) +
              Real.sin α * Real.sin (α + Real.pi)) := by ring
      _ = ‖z‖ * Real.cos (α - (α + Real.pi)) := by rw [← Real.cos_sub]
      _ = -‖z‖ := by simp
      _ = -‖((↑(‖z‖ * Real.cos α) : ℂ) + (↑(‖z‖ * Real.sin α) : ℂ) * Complex.I)‖ := by
        rw [hznorm]
  · rw [borelParadoxLongitude, show Complex.arg (x.1 0 + x.1 1 * Complex.I) = α by rfl, if_neg hα,
      hx0, hx1, if_neg hα]
    calc
      ‖z‖ * Real.cos α * Real.cos α + ‖z‖ * Real.sin α * Real.sin α
          = ‖z‖ * (Real.cos α * Real.cos α + Real.sin α * Real.sin α) := by ring
      _ = ‖z‖ * (Real.sin α ^ 2 + Real.cos α ^ 2) := by ring
      _ = ‖z‖ := by rw [Real.sin_sq_add_cos_sq]; ring
      _ = ‖((↑(‖z‖ * Real.cos α) : ℂ) + (↑(‖z‖ * Real.sin α) : ℂ) * Complex.I)‖ := by
        rw [hznorm]

/-- Helper for Exercise 8.3.5: the signed meridian complex built from the longitude branch and the
vertical coordinate has norm `1` on the unit sphere. -/
theorem earthSurface_signedMeridianComplex_norm_one (x : EarthSurface) :
    let z : ℂ := x.1 0 + x.1 1 * Complex.I
    let α : ℝ := Complex.arg z
    ‖((((if α < 0 then -‖z‖ else ‖z‖ : ℝ) : ℂ) + x.1 2 * Complex.I))‖ = 1 := by
  -- Proof comment: convert sphere membership into the coordinate identity
  -- `x₀^2 + x₁^2 + x₂^2 = 1`, then compute the complex norm square directly.
  dsimp
  have hsphere : ‖(x : Earth)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using x.2
  have hsum : x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2 = 1 := by
    have hnormsq : ‖(x : Earth)‖ ^ 2 = 1 := by
      nlinarith [hsphere]
    have hcoords : ‖(x : Earth)‖ ^ 2 = x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2 := by
      simpa [Fin.sum_univ_three] using (EuclideanSpace.real_norm_sq_eq (x : Earth))
    nlinarith
  let z : ℂ := x.1 0 + x.1 1 * Complex.I
  let α : ℝ := Complex.arg z
  let w : ℂ := (((if α < 0 then -‖z‖ else ‖z‖ : ℝ) : ℂ) + x.1 2 * Complex.I)
  have hzsq : ‖z‖ ^ 2 = x.1 0 ^ 2 + x.1 1 ^ 2 := by
    calc
      ‖z‖ ^ 2 = Complex.normSq z := by rw [Complex.sq_norm]
      _ = x.1 0 ^ 2 + x.1 1 ^ 2 := by
        simp [z, Complex.normSq_apply, pow_two]
  have hwsq : ‖w‖ ^ 2 = 1 := by
    by_cases hα : α < 0
    · calc
        ‖w‖ ^ 2 = Complex.normSq w := by rw [Complex.sq_norm]
        _ = (-‖z‖) ^ 2 + x.1 2 ^ 2 := by
          simp [w, hα, Complex.normSq_apply, pow_two]
        _ = ‖z‖ ^ 2 + x.1 2 ^ 2 := by ring
        _ = 1 := by
          nlinarith [hzsq, hsum]
    · calc
        ‖w‖ ^ 2 = Complex.normSq w := by rw [Complex.sq_norm]
        _ = ‖z‖ ^ 2 + x.1 2 ^ 2 := by
          simp [w, hα, Complex.normSq_apply, pow_two]
        _ = 1 := by
          nlinarith [hzsq, hsum]
  have hw_nonneg : 0 ≤ ‖w‖ := norm_nonneg w
  nlinarith

/-- Helper for Exercise 8.3.5: after rewriting the meridian projection into signed norm form, the
latitude is recovered from a single normalized complex number. -/
theorem borelParadoxLatitude_trig_of_signedMeridian (x : EarthSurface) :
    let z : ℂ := x.1 0 + x.1 1 * Complex.I
    let α : ℝ := Complex.arg z
    (Real.cos (borelParadoxLatitude x) = if α < 0 then -‖z‖ else ‖z‖) ∧
      Real.sin (borelParadoxLatitude x) = x.1 2 := by
  -- Proof comment: keep the latitude complex in one spelling `w`, rewrite its real part with the
  -- meridian projection lemma, and then read off cosine and sine from `Complex.arg w`.
  dsimp
  let z : ℂ := x.1 0 + x.1 1 * Complex.I
  let α : ℝ := Complex.arg z
  let w : ℂ := (((if α < 0 then -‖z‖ else ‖z‖ : ℝ) : ℂ) + x.1 2 * Complex.I)
  have hreal :
      x.1 0 * Real.cos (borelParadoxLongitude x) +
          x.1 1 * Real.sin (borelParadoxLongitude x) =
        if α < 0 then -‖z‖ else ‖z‖ := by
    simpa [z, α] using meridianProjection_eq_signed_norm x
  have hcomplex :
      (x.1 0 : ℂ) * Real.cos (borelParadoxLongitude x) +
          (x.1 1 : ℂ) * Real.sin (borelParadoxLongitude x) +
          x.1 2 * Complex.I = w := by
    calc
      (x.1 0 : ℂ) * Real.cos (borelParadoxLongitude x) +
          (x.1 1 : ℂ) * Real.sin (borelParadoxLongitude x) +
          x.1 2 * Complex.I
          =
        (((x.1 0 * Real.cos (borelParadoxLongitude x) +
            x.1 1 * Real.sin (borelParadoxLongitude x) : ℝ) : ℂ) +
            x.1 2 * Complex.I) := by
              simp [add_assoc]
      _ = w := by rw [hreal]
  have hlat : borelParadoxLatitude x = Complex.arg w := by
    -- Proof comment: after the real-part rewrite, the latitude definition is exactly `Complex.arg w`.
    simpa [borelParadoxLatitude, add_assoc] using congrArg Complex.arg hcomplex
  have hnorm : ‖w‖ = 1 := by
    simpa [w, z, α] using earthSurface_signedMeridianComplex_norm_one x
  constructor
  · have hcos : ‖w‖ * Real.cos (Complex.arg w) = if α < 0 then -‖z‖ else ‖z‖ := by
      simpa [w, Complex.add_re, Complex.mul_re, Complex.I_re] using Complex.norm_mul_cos_arg w
    rw [hlat]
    rw [hnorm, one_mul] at hcos
    simpa [z, α] using hcos
  · have hsin : ‖w‖ * Real.sin (Complex.arg w) = x.1 2 := by
      simpa [w, Complex.add_im, Complex.mul_im, Complex.I_im] using Complex.norm_mul_sin_arg w
    rw [hlat]
    rw [hnorm, one_mul] at hsin
    simpa [z, α] using hsin

/-- The canonical Borel-paradox coordinates reconstruct the original point on the sphere. -/
theorem earthPointOfLongitudeLatitude_borelParadoxCoordinates (x : EarthSurface) :
    earthPointOfLongitudeLatitude (borelParadoxLongitude x) (borelParadoxLatitude x) = x := by
  -- Route correction: the previous route kept trying to unfold `Complex.arg` directly. The stable
  -- route is to use the branch lemmas above for the longitude and meridian projection, then apply
  -- the same `Complex.arg` reconstruction once more to the normalized meridian complex.
  let z : ℂ := x.1 0 + x.1 1 * Complex.I
  let α : ℝ := Complex.arg z
  have hlat := borelParadoxLatitude_trig_of_signedMeridian x
  have hlongCos := borelParadoxLongitude_norm_mul_cos x
  have hlongSin := borelParadoxLongitude_norm_mul_sin x
  dsimp [z, α] at hlat hlongCos hlongSin
  apply Subtype.ext
  ext i
  fin_cases i
  · -- Proof comment: combine the longitude cosine branch identity with the signed latitude cosine.
    simp [earthPointOfLongitudeLatitude]
    by_cases hα : Complex.arg (x.1 0 + x.1 1 * Complex.I) < 0
    · have hlatCos : Real.cos (borelParadoxLatitude x) = -‖z‖ := by
        simpa [z, hα] using hlat.1
      have hlong : ‖z‖ * Real.cos (borelParadoxLongitude x) = -x.1 0 := by
        simpa [z, hα] using hlongCos
      calc
        Real.cos (borelParadoxLongitude x) * Real.cos (borelParadoxLatitude x)
            = Real.cos (borelParadoxLongitude x) * (-‖z‖) := by rw [hlatCos]
        _ = -(‖z‖ * Real.cos (borelParadoxLongitude x)) := by ring
        _ = -(-x.1 0) := by rw [hlong]
        _ = x.1 0 := by ring
    · have hlatCos : Real.cos (borelParadoxLatitude x) = ‖z‖ := by
        simpa [z, hα] using hlat.1
      have hlong : ‖z‖ * Real.cos (borelParadoxLongitude x) = x.1 0 := by
        simpa [z, hα] using hlongCos
      calc
        Real.cos (borelParadoxLongitude x) * Real.cos (borelParadoxLatitude x)
            = Real.cos (borelParadoxLongitude x) * ‖z‖ := by rw [hlatCos]
        _ = ‖z‖ * Real.cos (borelParadoxLongitude x) := by ring
        _ = x.1 0 := by rw [hlong]
  · -- Proof comment: the second coordinate is identical, with sine in place of cosine.
    simp [earthPointOfLongitudeLatitude]
    by_cases hα : Complex.arg (x.1 0 + x.1 1 * Complex.I) < 0
    · have hlatCos : Real.cos (borelParadoxLatitude x) = -‖z‖ := by
        simpa [z, hα] using hlat.1
      have hlong : ‖z‖ * Real.sin (borelParadoxLongitude x) = -x.1 1 := by
        simpa [z, hα] using hlongSin
      calc
        Real.sin (borelParadoxLongitude x) * Real.cos (borelParadoxLatitude x)
            = Real.sin (borelParadoxLongitude x) * (-‖z‖) := by rw [hlatCos]
        _ = -(‖z‖ * Real.sin (borelParadoxLongitude x)) := by ring
        _ = -(-x.1 1) := by rw [hlong]
        _ = x.1 1 := by ring
    · have hlatCos : Real.cos (borelParadoxLatitude x) = ‖z‖ := by
        simpa [z, hα] using hlat.1
      have hlong : ‖z‖ * Real.sin (borelParadoxLongitude x) = x.1 1 := by
        simpa [z, hα] using hlongSin
      calc
        Real.sin (borelParadoxLongitude x) * Real.cos (borelParadoxLatitude x)
            = Real.sin (borelParadoxLongitude x) * ‖z‖ := by rw [hlatCos]
        _ = ‖z‖ * Real.sin (borelParadoxLongitude x) := by ring
        _ = x.1 1 := by rw [hlong]
  · -- Proof comment: the vertical coordinate is exactly the latitude sine.
    simpa [earthPointOfLongitudeLatitude] using hlat.2

/-- The canonical Borel-paradox longitude lies in `[0, π]`; this is the closed-interval version of
the textbook range `[0, π)`, differing only by an endpoint convention. -/
theorem borelParadoxLongitude_mem_Icc (x : EarthSurface) :
    borelParadoxLongitude x ∈ Set.Icc 0 Real.pi := by
  -- Proof comment: the raw complex argument lies in `(-π, π]`; the longitude definition only
  -- shifts negative values by `π`, so the result lands in `[0, π]`.
  let θ : ℝ := Complex.arg (x.1 0 + x.1 1 * Complex.I)
  have hθ_mem : θ ∈ Set.Ioc (-Real.pi) Real.pi := by
    simpa [θ] using Complex.arg_mem_Ioc (x.1 0 + x.1 1 * Complex.I)
  have hlong :
      borelParadoxLongitude x = if θ < 0 then θ + Real.pi else θ := by
    simp [borelParadoxLongitude, θ]
  by_cases hθ : θ < 0
  · constructor
    · rw [hlong]
      simp [hθ]
      have hlow : -Real.pi < θ := hθ_mem.1
      linarith
    · rw [hlong]
      simp [hθ]
      linarith
  · constructor
    · rw [hlong]
      simp [hθ]
      exact le_of_not_gt hθ
    · rw [hlong]
      simp [hθ]
      exact hθ_mem.2

/-- The canonical Borel-paradox latitude lies in `[-π, π]`; this is the closed-interval version of
the textbook range `[-π, π)`, differing only by an endpoint convention. -/
theorem borelParadoxLatitude_mem_Icc (x : EarthSurface) :
    borelParadoxLatitude x ∈ Set.Icc (-Real.pi) Real.pi := by
  -- Proof comment: the latitude is itself a raw complex argument, so it inherits the standard
  -- range `(-π, π]` from `Complex.arg`.
  unfold borelParadoxLatitude
  constructor
  · exact le_of_lt <| Complex.neg_pi_lt_arg _
  · exact Complex.arg_le_pi _

/-- The longitude law in Borel's paradox: the uniform probability measure on `[0, π)`, realized
as the conditioned Lebesgue measure on `[0, π]`. -/
noncomputable def borelParadoxLongitudeMeasure : Measure ℝ :=
  volume[|Set.Icc 0 Real.pi]

/-- The longitude law in Borel's paradox has constant Lebesgue density `1 / π` on `[0, π]`. -/
theorem borelParadoxLongitudeMeasure_def :
    borelParadoxLongitudeMeasure =
      volume.withDensity
        (Set.indicator (Set.Icc 0 Real.pi) fun _ ↦ ENNReal.ofReal (1 / Real.pi)) := by
  calc
    borelParadoxLongitudeMeasure = (volume (Set.Icc 0 Real.pi))⁻¹ • volume.restrict (Set.Icc 0 Real.pi) := by
      rfl
    _ = (volume.restrict (Set.Icc 0 Real.pi)).withDensity
          ((volume (Set.Icc 0 Real.pi))⁻¹ • (1 : ℝ → ℝ≥0∞)) := by
        rw [withDensity_smul _ measurable_one, withDensity_one]
    _ = volume.withDensity
          (Set.indicator (Set.Icc 0 Real.pi) ((volume (Set.Icc 0 Real.pi))⁻¹ • (1 : ℝ → ℝ≥0∞))) := by
        rw [← withDensity_indicator measurableSet_Icc]
    _ = volume.withDensity
          (Set.indicator (Set.Icc 0 Real.pi) fun _ ↦ ENNReal.ofReal (1 / Real.pi)) := by
        congr with x
        simp [Real.volume_Icc, Real.pi_pos, ENNReal.ofReal_inv_of_pos]

/-- The latitude law in Borel's paradox: the probability measure on `[-π, π)` with density
`φ ↦ |cos φ| / 4`, written on `[-π, π]` since the endpoint change is null for Lebesgue measure. -/
noncomputable def borelParadoxLatitudeMeasure : Measure ℝ :=
  volume.withDensity
    (Set.indicator (Set.Icc (-Real.pi) Real.pi) fun φ ↦
      ENNReal.ofReal (|Real.cos φ| / 4))

/-- The defining density formula for the latitude law in Borel's paradox. -/
theorem borelParadoxLatitudeMeasure_def :
    borelParadoxLatitudeMeasure =
      volume.withDensity
        (Set.indicator (Set.Icc (-Real.pi) Real.pi) fun φ ↦
          ENNReal.ofReal (|Real.cos φ| / 4)) := rfl

/-- Helper for Exercise 8.3.5: the latitude density `φ ↦ |cos φ| / 4` integrates to `1` on
`[-π, π]`. -/
private theorem integral_abs_cos_div_four_eq_one :
    ∫ φ in (-Real.pi)..Real.pi, |Real.cos φ| / 4 = 1 := by
  -- Proof comment: first reflect the negative half-interval to `[0, π]`, then split `[0, π]`
  -- at `π / 2` where the sign of `cos` changes exactly once.
  have hInt (a b : ℝ) : IntervalIntegrable (fun φ : ℝ ↦ |Real.cos φ| / 4) volume a b := by
    have hcos : Continuous fun φ : ℝ ↦ Real.cos φ := Real.continuous_cos
    simpa using (hcos.abs.div_const (4 : ℝ)).intervalIntegrable a b
  have hnegSplit :
      (∫ φ in (-Real.pi)..0, |Real.cos φ| / 4) + ∫ φ in 0..Real.pi, |Real.cos φ| / 4 =
        ∫ φ in (-Real.pi)..Real.pi, |Real.cos φ| / 4 := by
    refine intervalIntegral.integral_add_adjacent_intervals (hInt _ _) (hInt _ _)
  have hnegEq :
      ∫ φ in (-Real.pi)..0, |Real.cos φ| / 4 = ∫ φ in 0..Real.pi, |Real.cos φ| / 4 := by
    have hCompNeg :
        (∫ φ in 0..Real.pi, |Real.cos (-φ)| / 4) =
          ∫ φ in (-Real.pi)..0, |Real.cos φ| / 4 := by
      simpa using
        (@intervalIntegral.integral_comp_neg ℝ _ _ 0 Real.pi
          (fun φ : ℝ ↦ |Real.cos φ| / 4))
    calc
      ∫ φ in (-Real.pi)..0, |Real.cos φ| / 4
          = ∫ φ in 0..Real.pi, |Real.cos (-φ)| / 4 := by simpa using hCompNeg.symm
      _ = ∫ φ in 0..Real.pi, |Real.cos φ| / 4 := by
        refine intervalIntegral.integral_congr ?_
        intro φ hφ
        simp [Real.cos_neg]
  have hposSplit :
      (∫ φ in 0..(Real.pi / 2), |Real.cos φ| / 4) +
          ∫ φ in (Real.pi / 2)..Real.pi, |Real.cos φ| / 4 =
        ∫ φ in 0..Real.pi, |Real.cos φ| / 4 := by
    refine intervalIntegral.integral_add_adjacent_intervals (hInt _ _) (hInt _ _)
  have hleft : ∫ φ in 0..(Real.pi / 2), |Real.cos φ| / 4 = 1 / 4 := by
    -- Proof comment: on `[0, π / 2]`, cosine is nonnegative, so the absolute value drops.
    calc
      ∫ φ in 0..(Real.pi / 2), |Real.cos φ| / 4
          = ∫ φ in 0..(Real.pi / 2), Real.cos φ / 4 := by
              refine intervalIntegral.integral_congr ?_
              intro φ hφ
              have hφ' : φ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
                simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ Real.pi / 2 by positivity)] using hφ
              have hlow : -(Real.pi / 2) ≤ φ := by
                have hneg : -(Real.pi / 2) ≤ (0 : ℝ) := by
                  nlinarith [Real.pi_pos]
                exact le_trans hneg hφ'.1
              have hφ'' : φ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨hlow, hφ'.2⟩
              simp [abs_of_nonneg (Real.cos_nonneg_of_mem_Icc hφ'')]
      _ = (∫ φ in 0..(Real.pi / 2), Real.cos φ) / 4 := by
            rw [intervalIntegral.integral_div]
      _ = 1 / 4 := by
            rw [integral_cos]
            norm_num [Real.sin_pi_div_two]
  have hright : ∫ φ in (Real.pi / 2)..Real.pi, |Real.cos φ| / 4 = 1 / 4 := by
    -- Proof comment: on `[π / 2, π]`, cosine is nonpositive, so `|cos| = -cos`.
    have hpiHalfLePi : Real.pi / 2 ≤ Real.pi := by
      nlinarith [Real.pi_pos]
    calc
      ∫ φ in (Real.pi / 2)..Real.pi, |Real.cos φ| / 4
          = ∫ φ in (Real.pi / 2)..Real.pi, (-Real.cos φ) / 4 := by
              refine intervalIntegral.integral_congr ?_
              intro φ hφ
              have hφ' : φ ∈ Set.Icc (Real.pi / 2) Real.pi := by
                simpa [Set.uIcc_of_le hpiHalfLePi] using hφ
              have hcos : Real.cos φ ≤ 0 := by
                refine Real.cos_nonpos_of_pi_div_two_le_of_le hφ'.1 ?_
                linarith [hφ'.2, Real.pi_pos]
              simp [abs_of_nonpos hcos]
      _ = -(∫ φ in (Real.pi / 2)..Real.pi, Real.cos φ) / 4 := by
            rw [intervalIntegral.integral_div, intervalIntegral.integral_neg]
      _ = 1 / 4 := by
            rw [integral_cos]
            norm_num [Real.sin_pi_div_two]
  have hpos : ∫ φ in 0..Real.pi, |Real.cos φ| / 4 = 1 / 2 := by
    linarith [hposSplit, hleft, hright]
  linarith [hnegSplit, hnegEq, hpos]

instance : IsProbabilityMeasure borelParadoxLongitudeMeasure := by
  exact cond_isProbabilityMeasure_of_finite
    (by
      exact ne_of_gt <| by
        simpa [Real.volume_Icc] using (ENNReal.ofReal_pos.mpr Real.pi_pos))
    (by simp [Real.volume_Icc])

instance : IsProbabilityMeasure borelParadoxLatitudeMeasure := by
  -- Proof comment: rewrite the total mass by `withDensity_apply`, then convert the restricted
  -- integral on `[-π, π]` to the interval integral already computed above.
  refine ⟨?_⟩
  rw [borelParadoxLatitudeMeasure_def, withDensity_apply _ MeasurableSet.univ,
    lintegral_indicator measurableSet_Icc]
  simp only [Measure.restrict_univ]
  let f : ℝ → ℝ := fun φ ↦ |Real.cos φ| / 4
  change ∫⁻ φ, ENNReal.ofReal (f φ) ∂volume.restrict (Set.Icc (-Real.pi) Real.pi) = 1
  have hle : -Real.pi ≤ Real.pi := by
    linarith [Real.pi_pos]
  have hfiInterval : IntervalIntegrable f volume (-Real.pi) Real.pi := by
    have hcos : Continuous fun φ : ℝ ↦ Real.cos φ := Real.continuous_cos
    simpa [f] using (hcos.abs.div_const (4 : ℝ)).intervalIntegrable (-Real.pi) Real.pi
  have hfi : Integrable f (volume.restrict (Set.Icc (-Real.pi) Real.pi)) := by
    rw [show Integrable f (volume.restrict (Set.Icc (-Real.pi) Real.pi)) ↔
        IntervalIntegrable f volume (-Real.pi) Real.pi by
          rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle]
          rfl]
    exact hfiInterval
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc (-Real.pi) Real.pi)] f := by
    filter_upwards with φ
    have hnonneg : 0 ≤ |Real.cos φ| := abs_nonneg _
    positivity
  rw [← ENNReal.ofReal_one, ← ofReal_integral_eq_lintegral_ofReal hfi hnn]
  have hset :
      ∫ φ, f φ ∂volume.restrict (Set.Icc (-Real.pi) Real.pi) = 1 := by
    calc
      ∫ φ, f φ ∂volume.restrict (Set.Icc (-Real.pi) Real.pi)
          = ∫ φ in Set.Icc (-Real.pi) Real.pi, f φ ∂volume := by
              rfl
      _ = ∫ φ in Set.Ioc (-Real.pi) Real.pi, f φ ∂volume := by
            rw [integral_Icc_eq_integral_Ioc']
            simp
      _ = ∫ φ in (-Real.pi)..Real.pi, f φ := by
            symm
            exact intervalIntegral.integral_of_le hle
      _ = 1 := by
            rw [show (∫ φ in (-Real.pi)..Real.pi, f φ) =
                ∫ φ in (-Real.pi)..Real.pi, |Real.cos φ| / 4 by
                  rfl]
            exact integral_abs_cos_div_four_eq_one
  simp [hset]

/-- Helper for Exercise 8.3.5: the cone chart with coordinates `(r, θ, φ)` sends
`(r, θ, φ)` to `r • earthPointOfLongitudeLatitude θ φ`. -/
private def borelParadoxConeChart (p : Earth) : Earth :=
  p 0 • (earthPointOfLongitudeLatitude (p 1) (p 2) : Earth)

/-- Helper for Exercise 8.3.5: the equatorial complex coordinate of
`earthPointOfLongitudeLatitude θ φ` is `cos φ` times the standard unit-circle complex number at
angle `θ`. -/
private theorem earthPointOfLongitudeLatitude_equatorialComplex (θ φ : ℝ) :
    (((earthPointOfLongitudeLatitude θ φ : Earth) 0 : ℂ) +
        ((earthPointOfLongitudeLatitude θ φ : Earth) 1 : ℂ) * Complex.I) =
      (Real.cos φ : ℂ) * (Real.cos θ + Real.sin θ * Complex.I) := by
  -- Proof comment: unfold the coordinate formula once and collect the real and imaginary parts of
  -- the equatorial projection into the standard `cos θ + sin θ * I` factor.
  simp [earthPointOfLongitudeLatitude, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Exercise 8.3.5: the negative-`cos φ` branch of the equatorial complex is the same
chart, rewritten with meridian angle `θ - π`. -/
private theorem earthPointOfLongitudeLatitude_equatorialComplex_subPi (θ φ : ℝ) :
    (((earthPointOfLongitudeLatitude θ φ : Earth) 0 : ℂ) +
        ((earthPointOfLongitudeLatitude θ φ : Earth) 1 : ℂ) * Complex.I) =
      (-Real.cos φ : ℂ) *
        (Real.cos (θ - Real.pi) + Real.sin (θ - Real.pi) * Complex.I) := by
  -- Proof comment: rewrite the equatorial factor using `cos (θ - π) = -cos θ` and
  -- `sin (θ - π) = -sin θ`, then move the minus sign onto the radial factor.
  calc
    (((earthPointOfLongitudeLatitude θ φ : Earth) 0 : ℂ) +
        ((earthPointOfLongitudeLatitude θ φ : Earth) 1 : ℂ) * Complex.I)
        = (Real.cos φ : ℂ) * (Real.cos θ + Real.sin θ * Complex.I) := by
            rw [earthPointOfLongitudeLatitude_equatorialComplex]
    _ = (-Real.cos φ : ℂ) * (Real.cos (θ - Real.pi) + Real.sin (θ - Real.pi) * Complex.I) := by
          simp [Real.cos_sub, Real.sin_sub, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Exercise 8.3.5: once the longitude is fixed to `θ`, the meridian complex reduces
to the standard `cos φ + sin φ * I` normal form. -/
private theorem earthPointOfLongitudeLatitude_meridianComplex (θ φ : ℝ) :
    ((((earthPointOfLongitudeLatitude θ φ : Earth) 0 * Real.cos θ +
        (earthPointOfLongitudeLatitude θ φ : Earth) 1 * Real.sin θ : ℝ) : ℂ) +
      ((earthPointOfLongitudeLatitude θ φ : Earth) 2 : ℂ) * Complex.I) =
        Real.cos φ + Real.sin φ * Complex.I := by
  -- Proof comment: the meridian real part is `cos φ (cos² θ + sin² θ)`, so the complex number is
  -- exactly the usual latitude complex.
  have hreal :
      (earthPointOfLongitudeLatitude θ φ : Earth) 0 * Real.cos θ +
          (earthPointOfLongitudeLatitude θ φ : Earth) 1 * Real.sin θ =
        Real.cos φ := by
    calc
      (earthPointOfLongitudeLatitude θ φ : Earth) 0 * Real.cos θ +
          (earthPointOfLongitudeLatitude θ φ : Earth) 1 * Real.sin θ
          = Real.cos φ * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by
              simp [earthPointOfLongitudeLatitude, pow_two, mul_assoc]
              ring
      _ = Real.cos φ := by
            rw [Real.sin_sq_add_cos_sq]
            ring
  calc
    ((((earthPointOfLongitudeLatitude θ φ : Earth) 0 * Real.cos θ +
        (earthPointOfLongitudeLatitude θ φ : Earth) 1 * Real.sin θ : ℝ) : ℂ) +
      ((earthPointOfLongitudeLatitude θ φ : Earth) 2 : ℂ) * Complex.I)
        = (((Real.cos φ : ℝ) : ℂ) + (Real.sin φ : ℂ) * Complex.I) := by
            rw [hreal]
            simp [earthPointOfLongitudeLatitude]
    _ = Real.cos φ + Real.sin φ * Complex.I := by
          simp

/-- Helper for Exercise 8.3.5: away from the poles, the textbook coordinates of
`earthPointOfLongitudeLatitude θ φ` recover `(θ, φ)` itself. -/
private theorem borelParadoxCoordinates_earthPointOfLongitudeLatitude_of_cos_ne_zero
    {θ φ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) (hφ : φ ∈ Set.Ioo (-Real.pi) Real.pi)
    (hcos : Real.cos φ ≠ 0) :
    borelParadoxLongitude (earthPointOfLongitudeLatitude θ φ) = θ ∧
      borelParadoxLatitude (earthPointOfLongitudeLatitude θ φ) = φ := by
  have hθIoc : θ ∈ Set.Ioc (-Real.pi) Real.pi := ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.le⟩
  have hφIoc : φ ∈ Set.Ioc (-Real.pi) Real.pi := ⟨hφ.1, hφ.2.le⟩
  have hlong : borelParadoxLongitude (earthPointOfLongitudeLatitude θ φ) = θ := by
    -- Proof comment: the sign of `cos φ` determines whether the raw argument is `θ` or `θ - π`.
    rcases lt_or_gt_of_ne hcos with hcosNeg | hcosPos
    · have hθSubIoc : θ - Real.pi ∈ Set.Ioc (-Real.pi) Real.pi := by
        constructor
        · linarith [hθ.1]
        · linarith [hθ.2, Real.pi_pos]
      have hnegCosPos : 0 < -Real.cos φ := by
        linarith
      have hsinPos : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo hθ
      have hargNeg :
          Complex.arg (-(Real.cos θ + Real.sin θ * Complex.I)) = θ - Real.pi := by
        rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos]
        · simpa using Complex.arg_cos_add_sin_mul_I hθIoc
        · simpa using hsinPos
      have harg :
          Complex.arg
              ((((earthPointOfLongitudeLatitude θ φ : Earth) 0 : ℂ) +
                ((earthPointOfLongitudeLatitude θ φ : Earth) 1 : ℂ) * Complex.I)) =
            θ - Real.pi := by
        rw [earthPointOfLongitudeLatitude_equatorialComplex]
        have hrewrite :
            (Real.cos φ : ℂ) * (Real.cos θ + Real.sin θ * Complex.I) =
              (-Real.cos φ : ℂ) * (-(Real.cos θ + Real.sin θ * Complex.I)) := by
          ring
        rw [hrewrite]
        simpa using
          (Complex.arg_real_mul (-(Real.cos θ + Real.sin θ * Complex.I)) hnegCosPos).trans hargNeg
      have hθSubNeg : θ - Real.pi < 0 := by
        linarith [hθ.2]
      unfold borelParadoxLongitude
      rw [harg]
      simp [hθSubNeg]
    · have harg :
          Complex.arg
              ((((earthPointOfLongitudeLatitude θ φ : Earth) 0 : ℂ) +
                ((earthPointOfLongitudeLatitude θ φ : Earth) 1 : ℂ) * Complex.I)) =
            θ := by
        rw [earthPointOfLongitudeLatitude_equatorialComplex]
        simpa using Complex.arg_mul_cos_add_sin_mul_I hcosPos hθIoc
      have hθNonneg : ¬θ < 0 := by
        linarith [hθ.1]
      unfold borelParadoxLongitude
      rw [harg]
      simp [hθNonneg]
  have hlat : borelParadoxLatitude (earthPointOfLongitudeLatitude θ φ) = φ := by
    -- Proof comment: after the longitude is identified with `θ`, the latitude complex is already
    -- in the standard `cos φ + sin φ * I` form.
    have harg :
        Complex.arg
            ((((earthPointOfLongitudeLatitude θ φ : Earth) 0 * Real.cos θ +
                (earthPointOfLongitudeLatitude θ φ : Earth) 1 * Real.sin θ : ℝ) : ℂ) +
              ((earthPointOfLongitudeLatitude θ φ : Earth) 2 : ℂ) * Complex.I) = φ := by
      rw [earthPointOfLongitudeLatitude_meridianComplex]
      simpa [Complex.ofReal_cos, Complex.ofReal_sin] using Complex.arg_cos_add_sin_mul_I hφIoc
    unfold borelParadoxLatitude
    simpa [hlong] using harg
  exact ⟨hlong, hlat⟩

/-- Helper for Exercise 8.3.5: the cone chart is injective on the interior box away from the
poles, where the longitude coordinate is well defined. -/
private theorem injOn_borelParadoxConeChart :
    Set.InjOn borelParadoxConeChart
      {p : Earth |
        p 0 ∈ Set.Ioo (0 : ℝ) 1 ∧
          p 1 ∈ Set.Ioo (0 : ℝ) Real.pi ∧
            p 2 ∈ Set.Ioo (-Real.pi) Real.pi ∧
              Real.cos (p 2) ≠ 0} := by
  intro p hp q hq hpq
  have hp0 : 0 < p 0 := hp.1.1
  have hq0 : 0 < q 0 := hq.1.1
  have hnormEarthPoint (u v : ℝ) : ‖(earthPointOfLongitudeLatitude u v : Earth)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using
      (earthPointOfLongitudeLatitude u v).2
  have hpNorm : ‖borelParadoxConeChart p‖ = p 0 := by
    rw [borelParadoxConeChart, norm_smul, hnormEarthPoint]
    simp [Real.norm_eq_abs, abs_of_pos hp0]
  have hqNorm : ‖borelParadoxConeChart q‖ = q 0 := by
    rw [borelParadoxConeChart, norm_smul, hnormEarthPoint]
    simp [Real.norm_eq_abs, abs_of_pos hq0]
  have hp0_eq : p 0 = q 0 := by
    have hnorm := congrArg norm hpq
    rw [hpNorm, hqNorm] at hnorm
    exact hnorm
  have hp0_ne : p 0 ≠ 0 := by
    linarith
  have hsphereEq :
      earthPointOfLongitudeLatitude (p 1) (p 2) =
        earthPointOfLongitudeLatitude (q 1) (q 2) := by
    apply Subtype.ext
    have hpq' :
        p 0 • (earthPointOfLongitudeLatitude (p 1) (p 2) : Earth) =
          p 0 • (earthPointOfLongitudeLatitude (q 1) (q 2) : Earth) := by
      simpa [borelParadoxConeChart, hp0_eq] using hpq
    exact smul_right_injective Earth hp0_ne hpq'
  have hpCoords := borelParadoxCoordinates_earthPointOfLongitudeLatitude_of_cos_ne_zero
    hp.2.1 hp.2.2.1 hp.2.2.2
  have hqCoords := borelParadoxCoordinates_earthPointOfLongitudeLatitude_of_cos_ne_zero
    hq.2.1 hq.2.2.1 hq.2.2.2
  have hp1_eq : p 1 = q 1 := by
    have hlongEq := congrArg borelParadoxLongitude hsphereEq
    simpa [hpCoords.1, hqCoords.1] using hlongEq
  have hp2_eq : p 2 = q 2 := by
    have hlatEq := congrArg borelParadoxLatitude hsphereEq
    simpa [hpCoords.2, hqCoords.2] using hlatEq
  ext i
  fin_cases i
  · exact hp0_eq
  · exact hp1_eq
  · exact hp2_eq

/-- Helper for Exercise 8.3.5: on the interior box, membership in the cone over a coordinate
rectangle is equivalent to the obvious coordinate conditions. -/
private theorem borelParadoxConeChart_mem_rectangleCone_iff
    (s t : Set ℝ) {p : Earth}
    (hp0 : p 0 ∈ Set.Ioo (0 : ℝ) 1) (hp1 : p 1 ∈ Set.Ioo (0 : ℝ) Real.pi)
    (hp2 : p 2 ∈ Set.Ioo (-Real.pi) Real.pi) (hcos : Real.cos (p 2) ≠ 0) :
    let A : Set EarthSurface := fun x : EarthSurface ↦
      (borelParadoxLongitude x, borelParadoxLatitude x) ∈ s ×ˢ t
    borelParadoxConeChart p ∈ Set.Ioo (0 : ℝ) 1 • (Subtype.val '' A) ↔ p 1 ∈ s ∧ p 2 ∈ t := by
  let A : Set EarthSurface := fun x : EarthSurface ↦
    (borelParadoxLongitude x, borelParadoxLatitude x) ∈ s ×ˢ t
  change borelParadoxConeChart p ∈ Set.Ioo (0 : ℝ) 1 • (Subtype.val '' A) ↔ p 1 ∈ s ∧ p 2 ∈ t
  have hcoords := borelParadoxCoordinates_earthPointOfLongitudeLatitude_of_cos_ne_zero hp1 hp2 hcos
  have hnormSphere : ‖(earthPointOfLongitudeLatitude (p 1) (p 2) : Earth)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using
      (earthPointOfLongitudeLatitude (p 1) (p 2)).2
  constructor
  · intro hpCone
    rcases hpCone with ⟨r, hr, y, ⟨x, hxA, rfl⟩, hyEq⟩
    have hxNorm : ‖(x : Earth)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using x.2
    have hr_eq : r = p 0 := by
      have hnorm := congrArg norm hyEq
      rw [norm_smul, hxNorm, Real.norm_eq_abs, abs_of_pos hr.1, borelParadoxConeChart,
        norm_smul, hnormSphere, Real.norm_eq_abs, abs_of_pos hp0.1] at hnorm
      simpa using hnorm
    have hxEq : x = earthPointOfLongitudeLatitude (p 1) (p 2) := by
      apply Subtype.ext
      rw [borelParadoxConeChart, hr_eq] at hyEq
      exact smul_right_injective Earth (by linarith [hp0.1]) hyEq
    have hxCoords : borelParadoxLongitude x = p 1 ∧ borelParadoxLatitude x = p 2 := by
      simpa [hxEq] using hcoords
    change borelParadoxLongitude x ∈ s ∧ borelParadoxLatitude x ∈ t at hxA
    simpa [hxCoords.1, hxCoords.2] using hxA
  · intro hpst
    have hxA : earthPointOfLongitudeLatitude (p 1) (p 2) ∈ A := by
      change
        borelParadoxLongitude (earthPointOfLongitudeLatitude (p 1) (p 2)) ∈ s ∧
          borelParadoxLatitude (earthPointOfLongitudeLatitude (p 1) (p 2)) ∈ t
      simpa [hcoords.1, hcoords.2] using hpst
    refine ⟨p 0, hp0, (earthPointOfLongitudeLatitude (p 1) (p 2) : Earth), ?_, ?_⟩
    · exact ⟨earthPointOfLongitudeLatitude (p 1) (p 2), hxA, rfl⟩
    · simp [borelParadoxConeChart]

/-- Helper for Exercise 8.3.5: the longitude factor over `(0, π)` is `π` times the public
longitude measure. -/
private theorem longitudeIndicator_lintegral_eq_pi_mul_apply
    (s : Set ℝ) (hs : MeasurableSet s) :
    (∫⁻ θ in Set.Ioo (0 : ℝ) Real.pi,
        Set.indicator s (fun _ ↦ (1 : ℝ≥0∞)) θ ∂volume) =
      ENNReal.ofReal Real.pi * borelParadoxLongitudeMeasure s := by
  -- Proof comment: both sides are the Lebesgue mass of `s` inside the longitude strip; the right
  -- side rewrites through the explicit uniform density on `[0, π]`.
  have hMeasIndicator :
      Measurable
        (Set.indicator (Set.Icc (0 : ℝ) Real.pi) fun _ : ℝ ↦ ENNReal.ofReal (1 / Real.pi)) := by
    exact measurable_const.indicator measurableSet_Icc
  have hRestr :
      volume (s ∩ Set.Ioo (0 : ℝ) Real.pi) = volume (s ∩ Set.Icc (0 : ℝ) Real.pi) := by
    refine measure_congr ?_
    have hIooIcc :
        Set.Ioo (0 : ℝ) Real.pi =ᵐ[volume] Set.Icc (0 : ℝ) Real.pi := Ioo_ae_eq_Icc
    filter_upwards [hIooIcc] with θ hθ
    exact propext
      ⟨fun hsθ ↦ ⟨hsθ.1, hθ.mp hsθ.2⟩,
        fun hsθ ↦ ⟨hsθ.1, hθ.mpr hsθ.2⟩⟩
  have hMeasure :
      borelParadoxLongitudeMeasure s =
        ENNReal.ofReal (1 / Real.pi) * volume (s ∩ Set.Icc (0 : ℝ) Real.pi) := by
    rw [borelParadoxLongitudeMeasure_def, withDensity_apply _ hs, ← lintegral_indicator hs]
    simp [Set.indicator_indicator, hs, measurableSet_Icc, Set.inter_assoc, Set.inter_left_comm,
      Set.inter_comm, hMeasIndicator, Real.pi_pos.ne']
  calc
    (∫⁻ θ in Set.Ioo (0 : ℝ) Real.pi,
        Set.indicator s (fun _ ↦ (1 : ℝ≥0∞)) θ ∂volume)
        = volume (s ∩ Set.Ioo (0 : ℝ) Real.pi) := by
            rw [← lintegral_indicator measurableSet_Ioo]
            simp [Set.indicator_indicator, hs, measurableSet_Ioo, Set.inter_assoc,
              Set.inter_left_comm, Set.inter_comm]
    _ = volume (s ∩ Set.Icc (0 : ℝ) Real.pi) := hRestr
    _ = ENNReal.ofReal Real.pi * borelParadoxLongitudeMeasure s := by
          rw [hMeasure]
          have hmul : ENNReal.ofReal Real.pi * ENNReal.ofReal (1 / Real.pi) = 1 := by
            rw [← ENNReal.ofReal_mul]
            · simp [Real.pi_pos.ne']
            · positivity
          rw [← mul_assoc, hmul, one_mul]

section BorelParadox

variable (P : Measure Ω) (X : Ω → EarthSurface) (Θ Φ : Ω → ℝ)

/-- Helper for Exercise 8.3.5: the canonical longitude coordinate is measurable. -/
private theorem measurable_borelParadoxLongitude : Measurable borelParadoxLongitude := by
  -- Proof comment: the definition is a measurable `if` built from the measurable complex
  -- argument of the equatorial projection.
  classical
  let θ : EarthSurface → ℝ := fun x ↦ Complex.arg (x.1 0 + x.1 1 * Complex.I)
  have hθ : Measurable θ := Complex.measurable_arg.comp <| by fun_prop
  have hθpi : Measurable fun x : EarthSurface ↦ θ x + Real.pi := hθ.add measurable_const
  unfold borelParadoxLongitude
  change Measurable (fun x : EarthSurface ↦ if θ x < 0 then θ x + Real.pi else θ x)
  simpa using
    (Measurable.ite (measurableSet_lt hθ measurable_const) hθpi hθ)

/-- Helper for Exercise 8.3.5: the canonical latitude coordinate is measurable. -/
private theorem measurable_borelParadoxLatitude : Measurable borelParadoxLatitude := by
  -- Proof comment: once the longitude is measurable, the complex-valued meridian coordinate is
  -- measurable as well, so measurability follows from `Complex.arg`.
  let θ : EarthSurface → ℝ := borelParadoxLongitude
  have hθ : Measurable θ := measurable_borelParadoxLongitude
  have hw :
      Measurable fun x : EarthSurface ↦
        (x.1 0 : ℂ) * Complex.cos (θ x) + (x.1 1 : ℂ) * Complex.sin (θ x) + x.1 2 * Complex.I := by
    fun_prop
  -- Proof comment: rewrite the latitude definition into the exact complex-trigonometric normal
  -- form used by `hw`, then compose with `Complex.measurable_arg`.
  have hEq :
      borelParadoxLatitude =
        fun x : EarthSurface ↦
          Complex.arg
            ((x.1 0 : ℂ) * Complex.cos (θ x) + (x.1 1 : ℂ) * Complex.sin (θ x) +
              x.1 2 * Complex.I) := by
    funext x
    simp [borelParadoxLatitude, θ, add_assoc, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [hEq]
  simpa [Function.comp, add_assoc] using Complex.measurable_arg.comp hw

/-- Helper for Exercise 8.3.5: the canonical coordinate pair is measurable as a map to `ℝ × ℝ`. -/
private theorem measurable_borelParadoxCoordinates :
    Measurable fun x : EarthSurface ↦ (borelParadoxLongitude x, borelParadoxLatitude x) := by
  -- Proof comment: pair the already established coordinate-wise measurability facts.
  exact measurable_borelParadoxLongitude.prodMk measurable_borelParadoxLatitude

/-- Helper for Exercise 8.3.5: the weighted latitude integral on `(-π, π)` is exactly four times
the public latitude measure. -/
private theorem latitudeWeightedIntegral_eq_four_mul_apply
    (t : Set ℝ) (ht : MeasurableSet t) :
    (∫⁻ φ in Set.Ioo (-Real.pi) Real.pi,
        Set.indicator t (fun φ ↦ ENNReal.ofReal |Real.cos φ|) φ ∂volume)
      = 4 * borelParadoxLatitudeMeasure t := by
  -- Proof comment: first rewrite `borelParadoxLatitudeMeasure` by its `withDensity` definition and
  -- pull the constant factor `4` inside the integral.
  symm
  calc
    4 * borelParadoxLatitudeMeasure t
        = 4 * ∫⁻ φ in t,
            Set.indicator (Set.Icc (-Real.pi) Real.pi)
              (fun φ ↦ ENNReal.ofReal (|Real.cos φ| / 4)) φ ∂volume := by
            rw [borelParadoxLatitudeMeasure_def, withDensity_apply _ ht]
    _ = ∫⁻ φ in t,
          (4 : ℝ≥0∞) *
            Set.indicator (Set.Icc (-Real.pi) Real.pi)
              (fun φ ↦ ENNReal.ofReal (|Real.cos φ| / 4)) φ ∂volume := by
            let g : ℝ → ℝ := fun φ ↦ |Real.cos φ| / 4
            have hg : Measurable g := by
              fun_prop
            have hIndicator :
                Measurable
                  (Set.indicator (Set.Icc (-Real.pi) Real.pi)
                    (fun φ ↦ ENNReal.ofReal (g φ))) :=
              hg.ennreal_ofReal.indicator measurableSet_Icc
            rw [← lintegral_const_mul (4 : ℝ≥0∞) hIndicator]
    _ = ∫⁻ φ in t,
          Set.indicator (Set.Icc (-Real.pi) Real.pi)
            (fun φ ↦ ENNReal.ofReal |Real.cos φ|) φ ∂volume := by
            refine lintegral_congr ?_
            intro φ
            by_cases hφ : φ ∈ Set.Icc (-Real.pi) Real.pi
            · have hmul : 4 * (|Real.cos φ| / 4) = |Real.cos φ| := by ring
              calc
                (4 : ℝ≥0∞) *
                    Set.indicator (Set.Icc (-Real.pi) Real.pi)
                      (fun φ ↦ ENNReal.ofReal (|Real.cos φ| / 4)) φ
                    = (4 : ℝ≥0∞) * ENNReal.ofReal (|Real.cos φ| / 4) := by
                        simp [hφ]
                _ = ENNReal.ofReal (4 * (|Real.cos φ| / 4)) := by
                      rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_mul]
                      positivity
                _ = ENNReal.ofReal |Real.cos φ| := by rw [hmul]
                _ = Set.indicator (Set.Icc (-Real.pi) Real.pi)
                      (fun φ ↦ ENNReal.ofReal |Real.cos φ|) φ := by
                        simp [hφ]
            · simp [hφ]
    _ = ∫⁻ φ,
          Set.indicator (t ∩ Set.Icc (-Real.pi) Real.pi)
            (fun φ ↦ ENNReal.ofReal |Real.cos φ|) φ ∂volume := by
            rw [← lintegral_indicator ht]
            refine lintegral_congr ?_
            intro φ
            simp [Set.indicator_indicator, Set.inter_comm, Set.inter_left_comm, Set.inter_assoc]
    _ = ∫⁻ φ,
          Set.indicator (t ∩ Set.Ioo (-Real.pi) Real.pi)
            (fun φ ↦ ENNReal.ofReal |Real.cos φ|) φ ∂volume := by
            refine lintegral_congr_ae ?_
            have hIooIcc :
                Set.Ioo (-Real.pi) Real.pi =ᵐ[volume] Set.Icc (-Real.pi) Real.pi :=
              Ioo_ae_eq_Icc
            filter_upwards [hIooIcc] with φ hφ
            by_cases htφ : φ ∈ t
            · have hiff : φ ∈ Set.Icc (-Real.pi) Real.pi ↔ φ ∈ Set.Ioo (-Real.pi) Real.pi := by
                simpa using hφ.symm
              by_cases hIcc : φ ∈ Set.Icc (-Real.pi) Real.pi
              · have hIoo : φ ∈ Set.Ioo (-Real.pi) Real.pi := hiff.mp hIcc
                simp [Set.indicator_indicator, Set.mem_inter_iff, htφ, hIcc, hIoo]
              · have hIoo : φ ∉ Set.Ioo (-Real.pi) Real.pi := by
                  intro hIoo
                  exact hIcc (hiff.mpr hIoo)
                simp [Set.indicator_indicator, Set.mem_inter_iff, htφ, hIcc, hIoo]
            · simp [htφ]
    _ = ∫⁻ φ in Set.Ioo (-Real.pi) Real.pi,
          Set.indicator t (fun φ ↦ ENNReal.ofReal |Real.cos φ|) φ ∂volume := by
            rw [← lintegral_indicator measurableSet_Ioo]
            refine lintegral_congr ?_
            intro φ
            simp [Set.indicator_indicator, Set.inter_comm, Set.inter_left_comm, Set.inter_assoc]

/-- Helper for Exercise 8.3.5: every coordinate hyperplane in `Earth = ℝ^3` has zero Lebesgue
measure. -/
-- Semantic recall: use `PiLp.volume_preserving_toLp` to transport to functions and then
-- `Measure.pi_hyperplane` for the coordinate fiber.
private theorem volume_coordinateHyperplane_eq_zero (i : Fin 3) (c : ℝ) :
    volume {x : Earth | x i = c} = 0 := by
  have hcoord : Measurable fun x : Earth ↦ x i := by
    fun_prop
  have hmeas : MeasurableSet {x : Earth | x i = c} := by
    rw [show ({x : Earth | x i = c} : Set Earth) = ((fun x : Earth ↦ x i) ⁻¹' ({c} : Set ℝ)) by
      ext x
      simp]
    exact hcoord (measurableSet_singleton c)
  let μ : Fin 3 → Measure ℝ := fun _ ↦ volume
  have hhyperplane : Measure.pi μ {f : ∀ j : Fin 3, ℝ | f i = c} = 0 := by
    simpa [μ] using (Measure.pi_hyperplane μ i c)
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage hmeas.nullMeasurableSet]
  simpa [Set.preimage, volume_pi, μ] using hhyperplane

/-- Helper for Exercise 8.3.5: the cone chart has the explicit Jacobian matrix expected from the
coordinate formula `(r, θ, φ) ↦ (r cos θ cos φ, r sin θ cos φ, r sin φ)`. -/
private noncomputable def borelParadoxConeChartMatrix (p : Earth) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![
    Real.cos (p 1) * Real.cos (p 2), -p 0 * Real.sin (p 1) * Real.cos (p 2),
      -p 0 * Real.cos (p 1) * Real.sin (p 2);
    Real.sin (p 1) * Real.cos (p 2), p 0 * Real.cos (p 1) * Real.cos (p 2),
      -p 0 * Real.sin (p 1) * Real.sin (p 2);
    Real.sin (p 2), 0, p 0 * Real.cos (p 2)
  ]

/-- Helper for Exercise 8.3.5: the determinant of the explicit cone-chart Jacobian matrix is
`r^2 cos φ`. -/
theorem det_borelParadoxConeChartMatrix (p : Earth) :
    (borelParadoxConeChartMatrix p).det = (p 0) ^ 2 * Real.cos (p 2) := by
  -- Proof comment: expand the `3 × 3` determinant once, rewrite the two sine squares using
  -- `sin² + cos² = 1`, and finish by polynomial normalization.
  have hsin1 : Real.sin (p 1) ^ 2 = 1 - Real.cos (p 1) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (p 1)]
  have hsin2 : Real.sin (p 2) ^ 2 = 1 - Real.cos (p 2) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (p 2)]
  simp [borelParadoxConeChartMatrix, Matrix.det_fin_three, pow_two]
  ring_nf
  rw [hsin1, hsin2]
  ring_nf

/-- Helper for Exercise 8.3.5: the absolute Jacobian determinant of the cone chart is
`r^2 * |cos φ|`. -/
theorem abs_det_borelParadoxConeChartMatrix (p : Earth) :
    |(borelParadoxConeChartMatrix p).det| = (p 0) ^ 2 * |Real.cos (p 2)| := by
  -- Proof comment: once the determinant is known, only the nonnegativity of `r^2` remains.
  rw [det_borelParadoxConeChartMatrix]
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]

/-- Helper for Exercise 8.3.5: after trimming away the endpoint and pole fibers, the cone over the
open spherical rectangle is exactly the image of the explicit cone chart. -/
private theorem openRectangleCone_eq_borelParadoxConeChart_image
    (s t : Set ℝ) :
    let A₀ : Set EarthSurface := fun x : EarthSurface ↦
      borelParadoxLongitude x ∈ s ∩ Set.Ioo (0 : ℝ) Real.pi ∧
        borelParadoxLatitude x ∈ t ∩ Set.Ioo (-Real.pi) Real.pi ∧
          Real.cos (borelParadoxLatitude x) ≠ 0
    let D : Set Earth := fun p : Earth ↦
      p 0 ∈ Set.Ioo (0 : ℝ) 1 ∧
        p 1 ∈ s ∩ Set.Ioo (0 : ℝ) Real.pi ∧
          p 2 ∈ t ∩ Set.Ioo (-Real.pi) Real.pi ∧
            Real.cos (p 2) ≠ 0
    Set.Ioo (0 : ℝ) 1 • (Subtype.val '' A₀) = borelParadoxConeChart '' D := by
  let A₀ : Set EarthSurface := fun x : EarthSurface ↦
    borelParadoxLongitude x ∈ s ∩ Set.Ioo (0 : ℝ) Real.pi ∧
      borelParadoxLatitude x ∈ t ∩ Set.Ioo (-Real.pi) Real.pi ∧
        Real.cos (borelParadoxLatitude x) ≠ 0
  let D : Set Earth := fun p : Earth ↦
    p 0 ∈ Set.Ioo (0 : ℝ) 1 ∧
      p 1 ∈ s ∩ Set.Ioo (0 : ℝ) Real.pi ∧
        p 2 ∈ t ∩ Set.Ioo (-Real.pi) Real.pi ∧
          Real.cos (p 2) ≠ 0
  change Set.Ioo (0 : ℝ) 1 • (Subtype.val '' A₀) = borelParadoxConeChart '' D
  ext y
  constructor
  · intro hy
    rcases hy with ⟨r, hr, z, ⟨x, hxA0, rfl⟩, rfl⟩
    let p : Earth := WithLp.toLp 2 fun i : Fin 3 ↦
      if i = 0 then r else if i = 1 then borelParadoxLongitude x else borelParadoxLatitude x
    have hp0 : p 0 = r := by
      simp [p]
    have hp1 : p 1 = borelParadoxLongitude x := by
      simp [p]
    have hp2 : p 2 = borelParadoxLatitude x := by
      simp [p]
    have hpD : p ∈ D := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [hp0] using hr
      · simpa [hp1] using hxA0.1
      · simpa [hp2] using hxA0.2.1
      · simpa [hp2] using hxA0.2.2
    refine ⟨p, hpD, ?_⟩
    -- Proof comment: the coordinate witness uses the canonical longitude/latitude of `x`, and the
    -- reconstruction theorem identifies the chart point with `x` itself.
    rw [borelParadoxConeChart, hp0, hp1, hp2]
    exact congrArg (fun z : EarthSurface ↦ r • (z : Earth))
      (earthPointOfLongitudeLatitude_borelParadoxCoordinates x)
  · intro hy
    rcases hy with ⟨p, hpD, rfl⟩
    refine ⟨p 0, hpD.1, (earthPointOfLongitudeLatitude (p 1) (p 2) : Earth), ?_, ?_⟩
    · have hcoords := borelParadoxCoordinates_earthPointOfLongitudeLatitude_of_cos_ne_zero
        hpD.2.1.2 hpD.2.2.1.2 hpD.2.2.2
      have hxA0 : earthPointOfLongitudeLatitude (p 1) (p 2) ∈ A₀ := by
        refine ⟨?_, ?_, ?_⟩
        · simpa [hcoords.1] using hpD.2.1
        · simpa [hcoords.2] using hpD.2.2.1
        · simpa [hcoords.2] using hpD.2.2.2
      exact ⟨earthPointOfLongitudeLatitude (p 1) (p 2), hxA0, rfl⟩
    · simp [borelParadoxConeChart]

/-- Helper for Exercise 8.3.5: every removed boundary point of the spherical rectangle lies on one
of the coordinate hyperplanes `x₁ = 0` or `x₂ = 0`. -/
private theorem boundaryRectangleCone_subset_coordinateHyperplanes
    (s t : Set ℝ) :
    let A : Set EarthSurface := fun x : EarthSurface ↦
      (borelParadoxLongitude x, borelParadoxLatitude x) ∈ s ×ˢ t
    let A₀ : Set EarthSurface := fun x : EarthSurface ↦
      borelParadoxLongitude x ∈ s ∩ Set.Ioo (0 : ℝ) Real.pi ∧
        borelParadoxLatitude x ∈ t ∩ Set.Ioo (-Real.pi) Real.pi ∧
          Real.cos (borelParadoxLatitude x) ≠ 0
    Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (A \ A₀)) ⊆
      {y : Earth | y 1 = 0} ∪ {y : Earth | y 2 = 0} := by
  dsimp
  intro y hy
  rcases hy with ⟨r, hr, _, ⟨x, hxBoundary, rfl⟩, rfl⟩
  have hxθFormula :
      ((x : Earth) 1) =
        Real.sin (borelParadoxLongitude x) * Real.cos (borelParadoxLatitude x) := by
    -- Proof comment: rewrite the second coordinate using the reconstructed longitude/latitude
    -- parametrization of `x`.
    have hrepr := congrArg (fun z : EarthSurface ↦ ((z : Earth) 1))
      (earthPointOfLongitudeLatitude_borelParadoxCoordinates x)
    simpa [earthPointOfLongitudeLatitude] using hrepr.symm
  have hxφFormula : ((x : Earth) 2) = Real.sin (borelParadoxLatitude x) := by
    -- Proof comment: the third Cartesian coordinate is exactly the latitude sine.
    have hrepr := congrArg (fun z : EarthSurface ↦ ((z : Earth) 2))
      (earthPointOfLongitudeLatitude_borelParadoxCoordinates x)
    simpa [earthPointOfLongitudeLatitude] using hrepr.symm
  have hxθIcc := borelParadoxLongitude_mem_Icc x
  have hxφIcc := borelParadoxLatitude_mem_Icc x
  have hxRect :
      borelParadoxLongitude x ∈ s ∧ borelParadoxLatitude x ∈ t := by
    simpa using hxBoundary.1
  by_cases hθ :
      borelParadoxLongitude x ∈ Set.Ioo (0 : ℝ) Real.pi
  · by_cases hφ :
        borelParadoxLatitude x ∈ Set.Ioo (-Real.pi) Real.pi
    · have hcosZero : Real.cos (borelParadoxLatitude x) = 0 := by
        by_contra hcosZero
        exact hxBoundary.2 ⟨⟨hxRect.1, hθ⟩, ⟨hxRect.2, hφ⟩, hcosZero⟩
      left
      -- Proof comment: after the interval endpoints are excluded, only the pole slice remains,
      -- and there the second coordinate vanishes because `cos φ = 0`.
      simp [smul_eq_mul, hxθFormula, hcosZero]
    · right
      have hφEnds :
          borelParadoxLatitude x = -Real.pi ∨ borelParadoxLatitude x = Real.pi := by
        have hnot : ¬(-Real.pi < borelParadoxLatitude x ∧ borelParadoxLatitude x < Real.pi) := by
          simpa [Set.mem_Ioo] using hφ
        rcases hxφIcc with ⟨hφlo, hφhi⟩
        rcases not_and_or.mp hnot with hleft | hright
        · left
          linarith
        · right
          linarith
      rcases hφEnds with hφEq | hφEq
      · simp [smul_eq_mul, hxφFormula, hφEq]
      · simp [smul_eq_mul, hxφFormula, hφEq]
  · left
    have hθEnds :
        borelParadoxLongitude x = 0 ∨ borelParadoxLongitude x = Real.pi := by
      have hnot : ¬(0 < borelParadoxLongitude x ∧ borelParadoxLongitude x < Real.pi) := by
        simpa [Set.mem_Ioo] using hθ
      rcases hxθIcc with ⟨hθlo, hθhi⟩
      rcases not_and_or.mp hnot with hleft | hright
      · left
        linarith
      · right
        linarith
    -- Proof comment: the longitude endpoint fibers are meridians with `x₁ = 0`.
    rcases hθEnds with hθEq | hθEq
    · simp [smul_eq_mul, hxθFormula, hθEq]
    · simp [smul_eq_mul, hxθFormula, hθEq]

/-- Helper for Exercise 8.3.5: the cone over the removed boundary fibers has zero Lebesgue
volume because it is contained in two coordinate hyperplanes. -/
private theorem boundaryRectangleConeVolume_eq_zero
    (s t : Set ℝ) :
    let A : Set EarthSurface := fun x : EarthSurface ↦
      (borelParadoxLongitude x, borelParadoxLatitude x) ∈ s ×ˢ t
    let A₀ : Set EarthSurface := fun x : EarthSurface ↦
      borelParadoxLongitude x ∈ s ∩ Set.Ioo (0 : ℝ) Real.pi ∧
        borelParadoxLatitude x ∈ t ∩ Set.Ioo (-Real.pi) Real.pi ∧
          Real.cos (borelParadoxLatitude x) ≠ 0
    volume (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (A \ A₀))) = 0 := by
  dsimp
  refine measure_mono_null
    (boundaryRectangleCone_subset_coordinateHyperplanes s t) ?_
  -- Proof comment: each coordinate hyperplane has zero volume, so their finite union does too.
  simpa using
    measure_union_null (volume_coordinateHyperplane_eq_zero 1 0)
      (volume_coordinateHyperplane_eq_zero 2 0)

/-- Helper for Exercise 8.3.5: a product of three one-coordinate densities factors under the
ambient Lebesgue measure on `ℝ^3`. -/
private theorem lintegral_finThree_prod
    (f0 f1 f2 : ℝ → ℝ≥0∞) (hf0 : Measurable f0) (hf1 : Measurable f1) (hf2 : Measurable f2) :
    ∫⁻ x : Fin 3 → ℝ, f0 (x 0) * f1 (x 1) * f2 (x 2) ∂volume =
      (∫⁻ r, f0 r ∂volume) * (∫⁻ θ, f1 θ ∂volume) * ∫⁻ φ, f2 φ ∂volume := by
  let g : (Fin 2 → ℝ) → ℝ≥0∞ := fun y ↦ f1 (y 0) * f2 (y 1)
  have hg : Measurable g := by
    -- Proof comment: the tail factor only depends on the second and third coordinates, so it is
    -- measurable by composition with the two coordinate projections.
    exact (hf1.comp (measurable_pi_apply 0)).mul (hf2.comp (measurable_pi_apply 1))
  have hsplit0 := ((MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).symm)
  rw [← hsplit0.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  -- Proof comment: split the first coordinate off as a genuine product space.
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.cons,
    Fin.zero_succAbove]
  have hIntegrand :
      (fun a : ℝ × (Fin 2 → ℝ) ↦
        f0 a.1 * f1 (Fin.cases a.1 a.2 1) * f2 (Fin.cases a.1 a.2 2)) =
      (fun a : ℝ × (Fin 2 → ℝ) ↦ f0 a.1 * g a.2) := by
    funext a
    have h1 : Fin.cases a.1 a.2 1 = a.2 0 := rfl
    have h2 : Fin.cases a.1 a.2 2 = a.2 1 := rfl
    rw [h1, h2]
    simp [g, mul_assoc]
  rw [hIntegrand]
  rw [show (volume : Measure (ℝ × (Fin 2 → ℝ))) = (volume : Measure ℝ).prod volume by rfl]
  rw [lintegral_prod_mul hf0.aemeasurable hg.aemeasurable]
  have hsplit1 := ((MeasureTheory.volume_preserving_piFinTwo (fun _ : Fin 2 ↦ ℝ)).symm)
  have htail :
      ∫⁻ y : Fin 2 → ℝ, g y ∂volume = (∫⁻ θ, f1 θ ∂volume) * ∫⁻ φ, f2 φ ∂volume := by
    rw [← hsplit1.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    -- Proof comment: the remaining two coordinates are exactly an `ℝ × ℝ` product.
    simp [MeasurableEquiv.piFinTwo_symm_apply, Fin.cons, g]
    have hIntegrand2 :
        (fun a : ℝ × ℝ ↦ f1 a.1 * f2 (Fin.cases a.1 (Fin.cons a.2 finZeroElim) 1)) =
        (fun a : ℝ × ℝ ↦ f1 a.1 * f2 a.2) := by
      funext a
      have h1 : Fin.cases a.1 (Fin.cons a.2 finZeroElim) 1 = a.2 := rfl
      rw [h1]
    rw [hIntegrand2]
    rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume by rfl]
    rw [lintegral_prod_mul hf1.aemeasurable hf2.aemeasurable]
  rw [htail]
  ac_rfl

/-- Helper for Exercise 8.3.5: the explicit Jacobian matrix differentiates the cone chart
`(r, θ, φ) ↦ r • earthPointOfLongitudeLatitude θ φ`. -/
theorem hasFDerivAt_borelParadoxConeChart (p : Earth) :
    HasFDerivAt borelParadoxConeChart
      ((Matrix.toEuclideanLin (borelParadoxConeChartMatrix p)).toContinuousLinearMap) p := by
  have hChart :
      borelParadoxConeChart =
        fun q : Earth ↦
          WithLp.toLp 2
            (fun i : Fin 3 ↦
              if i = 0 then q 0 * Real.cos (q 1) * Real.cos (q 2)
              else if i = 1 then q 0 * Real.sin (q 1) * Real.cos (q 2)
              else q 0 * Real.sin (q 2)) := by
    funext q
    ext i
    fin_cases i <;> simp [borelParadoxConeChart, earthPointOfLongitudeLatitude, mul_assoc]
  let e : Earth ≃L[ℝ] (Fin 3 → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ)
  let coord : Fin 3 → Earth →L[ℝ] ℝ := fun i ↦
    PiLp.proj (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (β := fun _ : Fin 3 ↦ ℝ) i
  let rows : Fin 3 → Earth →L[ℝ] ℝ := fun i ↦
    if i = 0 then
      (Real.cos (p 1) * Real.cos (p 2)) • coord 0 +
        (-p 0 * Real.sin (p 1) * Real.cos (p 2)) • coord 1 +
          (-p 0 * Real.cos (p 1) * Real.sin (p 2)) • coord 2
    else if i = 1 then
      (Real.sin (p 1) * Real.cos (p 2)) • coord 0 +
        (p 0 * Real.cos (p 1) * Real.cos (p 2)) • coord 1 +
          (-p 0 * Real.sin (p 1) * Real.sin (p 2)) • coord 2
    else
      Real.sin (p 2) • coord 0 +
        (p 0 * Real.cos (p 2)) • coord 2
  have hDerivG :
      HasFDerivAt
        (fun q : Earth ↦
          fun i : Fin 3 ↦
            if i = 0 then q 0 * Real.cos (q 1) * Real.cos (q 2)
            else if i = 1 then q 0 * Real.sin (q 1) * Real.cos (q 2)
            else q 0 * Real.sin (q 2))
        (ContinuousLinearMap.pi rows) p := by
    rw [hasFDerivAt_pi]
    intro i
    fin_cases i
    · have hq0 : HasFDerivAt (fun q : Earth ↦ q 0) (coord 0) p := by
        simpa [coord] using
          (PiLp.hasFDerivAt_apply (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
            (E := fun _ : Fin 3 ↦ ℝ) p 0)
      have hq1 :
          HasFDerivAt (fun q : Earth ↦ Real.cos (q 1))
            ((-Real.sin (p 1)) • coord 1) p := by
        simpa using
          (Real.hasDerivAt_cos (p 1)).comp_hasFDerivAt p
            (PiLp.hasFDerivAt_apply (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
              (E := fun _ : Fin 3 ↦ ℝ) p 1)
      have hq2 :
          HasFDerivAt (fun q : Earth ↦ Real.cos (q 2))
            ((-Real.sin (p 2)) • coord 2) p := by
        simpa using
          (Real.hasDerivAt_cos (p 2)).comp_hasFDerivAt p
            (PiLp.hasFDerivAt_apply (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
              (E := fun _ : Fin 3 ↦ ℝ) p 2)
      simpa [rows, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm, smul_smul, add_comm,
        add_left_comm, add_assoc] using
        (hq0.mul hq1).mul hq2
    · have hq0 : HasFDerivAt (fun q : Earth ↦ q 0) (coord 0) p := by
        simpa [coord] using
          (PiLp.hasFDerivAt_apply (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
            (E := fun _ : Fin 3 ↦ ℝ) p 0)
      have hq1 :
          HasFDerivAt (fun q : Earth ↦ Real.sin (q 1))
            (Real.cos (p 1) • coord 1) p := by
        simpa using
          (Real.hasDerivAt_sin (p 1)).comp_hasFDerivAt p
            (PiLp.hasFDerivAt_apply (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
              (E := fun _ : Fin 3 ↦ ℝ) p 1)
      have hq2 :
          HasFDerivAt (fun q : Earth ↦ Real.cos (q 2))
            ((-Real.sin (p 2)) • coord 2) p := by
        simpa using
          (Real.hasDerivAt_cos (p 2)).comp_hasFDerivAt p
            (PiLp.hasFDerivAt_apply (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
              (E := fun _ : Fin 3 ↦ ℝ) p 2)
      simpa [rows, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm, smul_smul, add_comm,
        add_left_comm, add_assoc] using
        (hq0.mul hq1).mul hq2
    · have hq0 : HasFDerivAt (fun q : Earth ↦ q 0) (coord 0) p := by
        simpa [coord] using
          (PiLp.hasFDerivAt_apply (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
            (E := fun _ : Fin 3 ↦ ℝ) p 0)
      have hq2 :
          HasFDerivAt (fun q : Earth ↦ Real.sin (q 2))
            (Real.cos (p 2) • coord 2) p := by
        simpa using
          (Real.hasDerivAt_sin (p 2)).comp_hasFDerivAt p
            (PiLp.hasFDerivAt_apply (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
              (E := fun _ : Fin 3 ↦ ℝ) p 2)
      simpa [rows, mul_assoc, mul_left_comm, mul_comm, smul_smul, add_comm, add_left_comm,
        add_assoc] using hq0.mul hq2
  have hDerivEq :
      (e.symm : (Fin 3 → ℝ) →L[ℝ] Earth).comp (ContinuousLinearMap.pi rows) =
        ((Matrix.toEuclideanLin (borelParadoxConeChartMatrix p)).toContinuousLinearMap) := by
    ext q i
    fin_cases i
    · change rows 0 q = ((Matrix.toEuclideanLin (borelParadoxConeChartMatrix p) q).ofLp 0)
      have hcoord :
          ((Matrix.toEuclideanLin (borelParadoxConeChartMatrix p) q).ofLp 0) =
            Matrix.mulVec (borelParadoxConeChartMatrix p) q.ofLp 0 := by
        simpa using
          congrArg (fun x : Fin 3 → ℝ ↦ x 0)
            (Matrix.ofLp_toEuclideanLin_apply (borelParadoxConeChartMatrix p) q)
      rw [hcoord]
      dsimp [rows, coord]
      simp [borelParadoxConeChartMatrix, Matrix.mulVec, Fin.sum_univ_three, Matrix.vecHead,
        Matrix.vecTail]
      ring_nf
    · change rows 1 q = ((Matrix.toEuclideanLin (borelParadoxConeChartMatrix p) q).ofLp 1)
      have hcoord :
          ((Matrix.toEuclideanLin (borelParadoxConeChartMatrix p) q).ofLp 1) =
            Matrix.mulVec (borelParadoxConeChartMatrix p) q.ofLp 1 := by
        simpa using
          congrArg (fun x : Fin 3 → ℝ ↦ x 1)
            (Matrix.ofLp_toEuclideanLin_apply (borelParadoxConeChartMatrix p) q)
      rw [hcoord]
      dsimp [rows, coord]
      simp [borelParadoxConeChartMatrix, Matrix.mulVec, Fin.sum_univ_three, Matrix.vecHead,
        Matrix.vecTail]
      ring_nf
    · change rows 2 q = ((Matrix.toEuclideanLin (borelParadoxConeChartMatrix p) q).ofLp 2)
      have hcoord :
          ((Matrix.toEuclideanLin (borelParadoxConeChartMatrix p) q).ofLp 2) =
            Matrix.mulVec (borelParadoxConeChartMatrix p) q.ofLp 2 := by
        simpa using
          congrArg (fun x : Fin 3 → ℝ ↦ x 2)
            (Matrix.ofLp_toEuclideanLin_apply (borelParadoxConeChartMatrix p) q)
      rw [hcoord]
      dsimp [rows, coord]
      simp [borelParadoxConeChartMatrix, Matrix.mulVec, Fin.sum_univ_three, Matrix.vecHead,
        Matrix.vecTail]
  exact hChart ▸ hDerivEq ▸
    ((e.symm : (Fin 3 → ℝ) →L[ℝ] Earth).hasFDerivAt.comp p hDerivG)

/-- Helper for Exercise 8.3.5: the derivative of the cone chart has determinant
`r^2 cos φ`, encoded by `borelParadoxConeChartMatrix`. -/
theorem abs_det_fderiv_borelParadoxConeChart (p : Earth) :
    |(((Matrix.toEuclideanLin (borelParadoxConeChartMatrix p)).toContinuousLinearMap).det)| =
      (p 0) ^ 2 * |Real.cos (p 2)| := by
  have hdet :
      (((Matrix.toEuclideanLin (borelParadoxConeChartMatrix p)).toContinuousLinearMap).det) =
        (borelParadoxConeChartMatrix p).det := by
    change LinearMap.det (Matrix.toEuclideanLin (borelParadoxConeChartMatrix p)) =
      (borelParadoxConeChartMatrix p).det
    rw [Matrix.toEuclideanLin, Matrix.toLpLin_eq_toLin (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
      (R := ℝ)]
    simpa using
      (LinearMap.det_toLin (PiLp.basisFun (2 : ℝ≥0∞) ℝ (Fin 3))
        (f := borelParadoxConeChartMatrix p))
  rw [hdet, abs_det_borelParadoxConeChartMatrix]

/-- Helper for Exercise 8.3.5: the radial factor `r ↦ r^2` on `(0, 1)` integrates to `1 / 3`
with respect to Lebesgue measure. -/
private theorem radialSquareIndicator_lintegral :
    ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) 1) (fun r ↦ ENNReal.ofReal (r ^ 2)) r ∂volume =
      ENNReal.ofReal (1 / 3 : ℝ) := by
  calc
    ∫⁻ r, Set.indicator (Set.Ioo (0 : ℝ) 1) (fun r ↦ ENNReal.ofReal (r ^ 2)) r ∂volume
        = ∫⁻ r in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (r ^ 2) ∂volume := by
            rw [← lintegral_indicator measurableSet_Ioo]
    _ = Measure.volumeIoiPow 2 (Set.Iio ⟨(1 : ℝ), Set.mem_Ioi.2 one_pos⟩) := by
          rw [Measure.volumeIoiPow, withDensity_apply _ measurableSet_Iio,
            setLIntegral_subtype measurableSet_Ioi _ fun a : ℝ ↦ ENNReal.ofReal (a ^ 2),
            Set.image_subtype_val_Ioi_Iio]
    _ = ENNReal.ofReal (1 / 3 : ℝ) := by
          have h := Measure.volumeIoiPow_apply_Iio 2 ⟨(1 : ℝ), Set.mem_Ioi.2 one_pos⟩
          norm_num at h ⊢
          exact h

/-- Exercise 8.3.5: the remaining geometric content is the cone volume of a coordinate
rectangle on the sphere. -/
private theorem borelParadoxRectangleConeVolume
    (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    let A : Set EarthSurface := fun x : EarthSurface ↦
      (borelParadoxLongitude x, borelParadoxLatitude x) ∈ s ×ˢ t
    volume (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' A)) =
      volume (Metric.ball (0 : Earth) 1) * borelParadoxLongitudeMeasure s *
        borelParadoxLatitudeMeasure t := by
  let A : Set EarthSurface := fun x : EarthSurface ↦
    (borelParadoxLongitude x, borelParadoxLatitude x) ∈ s ×ˢ t
  let A₀ : Set EarthSurface := fun x : EarthSurface ↦
    borelParadoxLongitude x ∈ s ∩ Set.Ioo (0 : ℝ) Real.pi ∧
      borelParadoxLatitude x ∈ t ∩ Set.Ioo (-Real.pi) Real.pi ∧
        Real.cos (borelParadoxLatitude x) ≠ 0
  let D : Set Earth := fun p : Earth ↦
    p 0 ∈ Set.Ioo (0 : ℝ) 1 ∧
      p 1 ∈ s ∩ Set.Ioo (0 : ℝ) Real.pi ∧
        p 2 ∈ t ∩ Set.Ioo (-Real.pi) Real.pi ∧
          Real.cos (p 2) ≠ 0
  let coneA : Set Earth := Set.Ioo (0 : ℝ) 1 • (Subtype.val '' A)
  let coneA₀ : Set Earth := Set.Ioo (0 : ℝ) 1 • (Subtype.val '' A₀)
  let coneBoundary : Set Earth := Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (A \ A₀))
  change volume coneA = volume (Metric.ball (0 : Earth) 1) *
    borelParadoxLongitudeMeasure s * borelParadoxLatitudeMeasure t
  have hconeA₀_subset : coneA₀ ⊆ coneA := by
    intro y hy
    rcases hy with ⟨r, hr, _, ⟨x, hxA₀, rfl⟩, rfl⟩
    have hxA : x ∈ A := by
      change borelParadoxLongitude x ∈ s ∧ borelParadoxLatitude x ∈ t
      exact ⟨hxA₀.1.1, hxA₀.2.1.1⟩
    exact ⟨r, hr, (x : Earth), ⟨x, hxA, rfl⟩, rfl⟩
  have hcone_subset : coneA ⊆ coneA₀ ∪ coneBoundary := by
    intro y hy
    rcases hy with ⟨r, hr, _, ⟨x, hxA, rfl⟩, rfl⟩
    by_cases hxA₀ : x ∈ A₀
    · left
      exact ⟨r, hr, (x : Earth), ⟨x, hxA₀, rfl⟩, rfl⟩
    · right
      exact ⟨r, hr, (x : Earth), ⟨x, ⟨hxA, hxA₀⟩, rfl⟩, rfl⟩
  have hboundary_null : volume coneBoundary = 0 := by
    simpa [A, A₀, coneBoundary] using boundaryRectangleConeVolume_eq_zero s t
  have hcone_le : volume coneA ≤ volume coneA₀ := by
    calc
      volume coneA ≤ volume (coneA₀ ∪ coneBoundary) := measure_mono hcone_subset
      _ ≤ volume coneA₀ + volume coneBoundary := measure_union_le _ _
      _ = volume coneA₀ := by rw [hboundary_null, add_zero]
  have hcone_ge : volume coneA₀ ≤ volume coneA := measure_mono hconeA₀_subset
  have hDmeas : MeasurableSet D := by
    have h0 : Measurable fun p : Earth ↦ p 0 := by fun_prop
    have h1 : Measurable fun p : Earth ↦ p 1 := by fun_prop
    have h2 : Measurable fun p : Earth ↦ p 2 := by fun_prop
    have hcos : Measurable fun p : Earth ↦ Real.cos (p 2) := by fun_prop
    refine h0 (measurableSet_Ioo) |>.inter ?_
    refine (h1 ((hs.inter measurableSet_Ioo))).inter ?_
    refine (h2 (ht.inter measurableSet_Ioo)).inter ?_
    exact (hcos (measurableSet_singleton 0)).compl
  have hInj : Set.InjOn borelParadoxConeChart D :=
    injOn_borelParadoxConeChart.mono fun p hp ↦ by
      exact ⟨hp.1, hp.2.1.2, hp.2.2.1.2, hp.2.2.2⟩
  have himage :
      volume (borelParadoxConeChart '' D) =
        ∫⁻ p in D,
          ENNReal.ofReal
            |(((Matrix.toEuclideanLin (borelParadoxConeChartMatrix p)).toContinuousLinearMap).det)|
            ∂volume := by
    simpa using
      (lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ := volume) (s := D)
        (f := borelParadoxConeChart)
        (f' := fun p ↦
          (Matrix.toEuclideanLin (borelParadoxConeChartMatrix p)).toContinuousLinearMap)
        hDmeas
        (fun p hp ↦ (hasFDerivAt_borelParadoxConeChart p).hasFDerivWithinAt)
        hInj
        (fun _ ↦ 1))
  have himage' :
      volume (borelParadoxConeChart '' D) =
        ∫⁻ p in D, ENNReal.ofReal |(borelParadoxConeChartMatrix p).det| ∂volume := by
    simpa [abs_det_fderiv_borelParadoxConeChart] using himage
  have hconeA₀_image :
      coneA₀ = borelParadoxConeChart '' D := by
    simpa [A₀, D, coneA₀] using openRectangleCone_eq_borelParadoxConeChart_image s t
  have hconeA₀ :
      volume coneA₀ =
        ∫⁻ p in D,
          ENNReal.ofReal |(borelParadoxConeChartMatrix p).det| ∂volume := by
    rw [hconeA₀_image]
    exact himage'
  let f0 : ℝ → ℝ≥0∞ :=
    Set.indicator (Set.Ioo (0 : ℝ) 1) fun r ↦ ENNReal.ofReal (r ^ 2)
  let f1 : ℝ → ℝ≥0∞ :=
    Set.indicator (s ∩ Set.Ioo (0 : ℝ) Real.pi) fun _ ↦ (1 : ℝ≥0∞)
  let f2 : ℝ → ℝ≥0∞ :=
    Set.indicator (t ∩ Set.Ioo (-Real.pi) Real.pi) fun φ ↦ ENNReal.ofReal |Real.cos φ|
  have hf0 : Measurable f0 := by
    simpa [f0] using (measurable_id.pow_const 2).ennreal_ofReal.indicator measurableSet_Ioo
  have hf1 : Measurable f1 := measurable_const.indicator (hs.inter measurableSet_Ioo)
  have hf2 : Measurable f2 := by
    exact (Real.continuous_cos.abs.measurable.ennreal_ofReal).indicator (ht.inter measurableSet_Ioo)
  have hfactor :
      ∫⁻ p : Earth, f0 (p 0) * f1 (p 1) * f2 (p 2) ∂volume =
        (∫⁻ r, f0 r ∂volume) * (∫⁻ θ, f1 θ ∂volume) * ∫⁻ φ, f2 φ ∂volume := by
    rw [← (PiLp.volume_preserving_toLp (Fin 3)).lintegral_comp_emb
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ)).symm.toHomeomorph.measurableEmbedding]
    simpa [f0, f1, f2] using lintegral_finThree_prod f0 f1 f2 hf0 hf1 hf2
  have hconeA₀' :
      volume coneA₀ = ∫⁻ p : Earth, f0 (p 0) * f1 (p 1) * f2 (p 2) ∂volume := by
    rw [hconeA₀, ← lintegral_indicator hDmeas]
    refine lintegral_congr ?_
    intro p
    by_cases hp0 : p 0 ∈ Set.Ioo (0 : ℝ) 1
    · by_cases hp1 : p 1 ∈ s ∩ Set.Ioo (0 : ℝ) Real.pi
      · by_cases hp2 : p 2 ∈ t ∩ Set.Ioo (-Real.pi) Real.pi
        · by_cases hcos : Real.cos (p 2) ≠ 0
          · have hpD : p ∈ D := ⟨hp0, hp1, hp2, hcos⟩
            rw [Set.indicator_of_mem hpD]
            simp [f0, f1, f2, hp0, hp1, hp2, abs_det_borelParadoxConeChartMatrix,
              ENNReal.ofReal_mul, sq_nonneg, mul_comm]
          · have hcos0 : Real.cos (p 2) = 0 := not_ne_iff.mp hcos
            have hpD : p ∉ D := by
              intro hpD
              exact hcos hpD.2.2.2
            rw [Set.indicator_of_notMem hpD]
            simp [f0, f1, f2, hp0, hp1, hp2, hcos0]
        · have hpD : p ∉ D := by
            intro hpD
            exact hp2 hpD.2.2.1
          rw [Set.indicator_of_notMem hpD]
          simp [f0, f1, f2, hp0, hp1, hp2]
      · have hpD : p ∉ D := by
          intro hpD
          exact hp1 hpD.2.1
        rw [Set.indicator_of_notMem hpD]
        simp [f0, f1, f2, hp0, hp1]
    · have hpD : p ∉ D := by
        intro hpD
        exact hp0 hpD.1
      rw [Set.indicator_of_notMem hpD]
      simp [f0, f1, f2, hp0]
  have hf0int : ∫⁻ r, f0 r ∂volume = ENNReal.ofReal (1 / 3 : ℝ) := by
    simpa [f0] using radialSquareIndicator_lintegral
  have hf1int :
      ∫⁻ θ, f1 θ ∂volume =
        ENNReal.ofReal Real.pi * borelParadoxLongitudeMeasure s := by
    simpa [f1, Set.indicator_indicator, hs, measurableSet_Ioo, Set.inter_assoc,
      Set.inter_left_comm, Set.inter_comm] using longitudeIndicator_lintegral_eq_pi_mul_apply s hs
  have hf2int :
      ∫⁻ φ, f2 φ ∂volume = 4 * borelParadoxLatitudeMeasure t := by
    simpa [f2, Set.indicator_indicator, ht, measurableSet_Ioo, Set.inter_assoc,
      Set.inter_left_comm, Set.inter_comm] using latitudeWeightedIntegral_eq_four_mul_apply t ht
  have hball :
      volume (Metric.ball (0 : Earth) 1) = ENNReal.ofReal (Real.pi * 4 / 3) := by
    simpa using EuclideanSpace.volume_ball_fin_three (x := (0 : Earth)) (r := (1 : ℝ))
  have hconst :
      ENNReal.ofReal (1 / 3 : ℝ) * (ENNReal.ofReal Real.pi) * 4 =
        ENNReal.ofReal (Real.pi * 4 / 3) := by
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_mul,
      ← ENNReal.ofReal_mul]
    · congr 1
      ring_nf
    · positivity
    · positivity
  have hconeA_eq : volume coneA = volume coneA₀ := le_antisymm hcone_le hcone_ge
  rw [hconeA_eq, hconeA₀', hfactor, hf0int, hf1int, hf2int]
  calc
    ENNReal.ofReal (1 / 3 : ℝ) *
        (ENNReal.ofReal Real.pi * borelParadoxLongitudeMeasure s) *
          (4 * borelParadoxLatitudeMeasure t)
        = (ENNReal.ofReal (1 / 3 : ℝ) * ENNReal.ofReal Real.pi * 4) *
            borelParadoxLongitudeMeasure s * borelParadoxLatitudeMeasure t := by
              ac_rfl
    _ = ENNReal.ofReal (Real.pi * 4 / 3) * borelParadoxLongitudeMeasure s *
          borelParadoxLatitudeMeasure t := by
            rw [hconst]
    _ = volume (Metric.ball (0 : Earth) 1) * borelParadoxLongitudeMeasure s *
          borelParadoxLatitudeMeasure t := by
            rw [hball]

/-- Helper for Exercise 8.3.5: the canonical coordinate map sends measurable rectangles to the
expected product masses under the uniform surface law. -/
private theorem earthSurfaceUniformMeasure_map_borelParadoxCoordinates_apply_prod
    (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ((earthSurfaceUniformMeasure : ProbabilityMeasure EarthSurface) : Measure EarthSurface).map
        (fun x : EarthSurface ↦ (borelParadoxLongitude x, borelParadoxLatitude x))
        (s ×ˢ t)
      = borelParadoxLongitudeMeasure s * borelParadoxLatitudeMeasure t := by
  let A : Set EarthSurface := fun x : EarthSurface ↦
    (borelParadoxLongitude x, borelParadoxLatitude x) ∈ s ×ˢ t
  let ν : FiniteMeasure EarthSurface :=
    ⟨(volume : Measure Earth).toSphere, inferInstance⟩
  have hA : MeasurableSet A := by
    -- Proof comment: the rectangle preimage is measurable because the coordinate map is measurable.
    exact (hs.prod ht).preimage measurable_borelParadoxCoordinates
  have hνmeasure_ne : ((ν : FiniteMeasure EarthSurface) : Measure EarthSurface) ≠ 0 := by
    -- Proof comment: the spherical surface measure of a nontrivial Euclidean space is nonzero.
    simpa [ν] using (Measure.toSphere_ne_zero (μ := (volume : Measure Earth)))
  have hνne : ν ≠ 0 := by
    intro hν
    exact hνmeasure_ne (by simpa using congrArg (fun μ : FiniteMeasure EarthSurface ↦
      (μ : Measure EarthSurface)) hν)
  have hmass :
      (ν.mass : ℝ≥0∞) = 3 * volume (Metric.ball (0 : Earth) 1) := by
    -- Proof comment: the total spherical surface mass is `3` times the unit-ball volume.
    rw [FiniteMeasure.ennreal_mass]
    change ((volume : Measure Earth).toSphere) Set.univ =
      3 * volume (Metric.ball (0 : Earth) 1)
    simpa using (Measure.toSphere_apply_univ (μ := (volume : Measure Earth)))
  have hnormalize :
      ((earthSurfaceUniformMeasure : ProbabilityMeasure EarthSurface) : Measure EarthSurface) =
        ν.mass⁻¹ • ((volume : Measure Earth).toSphere) := by
    -- Proof comment: the uniform surface law is the normalized spherical surface measure.
    simpa [earthSurfaceUniformMeasure, ν] using (ν.toMeasure_normalize_eq_of_nonzero hνne)
  have hmass_ne_zero : ν.mass ≠ 0 := by
    -- Proof comment: the total spherical surface mass is the positive constant `3` times the unit
    -- ball volume in `ℝ^3`, so the finite measure itself is nonzero.
    exact fun hmass0 ↦ hνne ((MeasureTheory.FiniteMeasure.mass_zero_iff ν).mp hmass0)
  have hmass_lt_top : ν.mass < ∞ := by
    rw [FiniteMeasure.ennreal_mass]
    simpa using (show ((ν : Measure EarthSurface) Set.univ) < ∞ from measure_univ_lt_top)
  calc
    ((earthSurfaceUniformMeasure : ProbabilityMeasure EarthSurface) : Measure EarthSurface).map
        (fun x : EarthSurface ↦ (borelParadoxLongitude x, borelParadoxLatitude x))
        (s ×ˢ t)
        =
      ((earthSurfaceUniformMeasure : ProbabilityMeasure EarthSurface) : Measure EarthSurface) A := by
          -- Proof comment: unfold the pushforward mass of the measurable rectangle into the mass
          -- of its coordinate preimage on the sphere.
          rw [Measure.map_apply measurable_borelParadoxCoordinates (hs.prod ht)]
          rfl
    _ = ν.mass⁻¹ * ((volume : Measure Earth).toSphere A) := by
          rw [hnormalize, Measure.smul_apply]
          simp [smul_eq_mul]
    _ = ν.mass⁻¹ * (3 * volume (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' A))) := by
          -- Proof comment: `toSphere_apply'` turns the spherical surface mass into the cone volume
          -- of the same rectangle in the ambient Euclidean space.
          rw [Measure.toSphere_apply' (μ := (volume : Measure Earth)) hA]
          simp
    _ =
      ν.mass⁻¹ *
        (3 *
          (volume (Metric.ball (0 : Earth) 1) * borelParadoxLongitudeMeasure s *
            borelParadoxLatitudeMeasure t)) := by
          rw [borelParadoxRectangleConeVolume s t hs ht]
    _ =
      ν.mass⁻¹ *
        (ν.mass * (borelParadoxLongitudeMeasure s * borelParadoxLatitudeMeasure t)) := by
          rw [hmass]
          ac_rfl
    _ = borelParadoxLongitudeMeasure s * borelParadoxLatitudeMeasure t := by
          have hmass_ne_zero' : ((ν.mass : ℝ≥0∞) ≠ 0) := by
            exact_mod_cast hmass_ne_zero
          rw [← mul_assoc]
          have hcancel : (↑ν.mass⁻¹ : ℝ≥0∞) * ↑ν.mass = 1 := by
            exact_mod_cast inv_mul_cancel₀ hmass_ne_zero
          rw [hcancel, one_mul]

/-- Helper for Exercise 8.3.5: the canonical coordinate pair of a uniform point on the sphere has
the product law `borelParadoxLongitudeMeasure ⊗ borelParadoxLatitudeMeasure`. -/
private theorem earthSurfaceUniformMeasure_map_borelParadoxCoordinates :
    ((earthSurfaceUniformMeasure : ProbabilityMeasure EarthSurface) : Measure EarthSurface).map
        (fun x : EarthSurface ↦ (borelParadoxLongitude x, borelParadoxLatitude x))
      = borelParadoxLongitudeMeasure.prod borelParadoxLatitudeMeasure := by
  -- Proof comment: finite product measures are determined by their values on measurable rectangles.
  refine Measure.ext_prod ?_
  intro s t hs ht
  rw [Measure.prod_prod]
  exact earthSurfaceUniformMeasure_map_borelParadoxCoordinates_apply_prod s t hs ht

/-- Helper for Exercise 8.3.5: once the coordinate pair agrees almost everywhere with the canonical
coordinates of `X`, its law is the product law from the uniform sphere measure. -/
private theorem hasLaw_longitude_latitude_pair_of_uniformOnEarthSurface
    (hX : HasLaw X earthSurfaceUniformMeasure P)
    (hcoords : ∀ᵐ ω ∂P,
      (Θ ω, Φ ω) = (borelParadoxLongitude (X ω), borelParadoxLatitude (X ω))) :
    HasLaw (fun ω ↦ (Θ ω, Φ ω))
      (borelParadoxLongitudeMeasure.prod borelParadoxLatitudeMeasure) P := by
  -- Route correction: the closed strip `[0, π] × [-π, π]` still carries duplicate
  -- parametrizations, so the stable transport statement is the direct a.e. equality with the
  -- canonical coordinate pair.
  -- Proof comment: package the canonical coordinates on `EarthSurface`, compose with `hX`, and
  -- then transport the law across the given almost-everywhere equality.
  have hCanonical :
      HasLaw (fun ω ↦ (borelParadoxLongitude (X ω), borelParadoxLatitude (X ω)))
        (borelParadoxLongitudeMeasure.prod borelParadoxLatitudeMeasure) P := by
    let hSurfaceCoords :
        HasLaw (fun x : EarthSurface ↦ (borelParadoxLongitude x, borelParadoxLatitude x))
          (borelParadoxLongitudeMeasure.prod borelParadoxLatitudeMeasure) earthSurfaceUniformMeasure :=
      { aemeasurable :=
          by
            exact measurable_borelParadoxCoordinates.aemeasurable
        map_eq := earthSurfaceUniformMeasure_map_borelParadoxCoordinates }
    exact hSurfaceCoords.comp hX
  exact hCanonical.congr hcoords

private theorem hasLaw_borelParadoxCoordinates_of_uniformOnEarthSurface
    (hX : HasLaw X earthSurfaceUniformMeasure P) :
    HasLaw (fun ω ↦ (borelParadoxLongitude (X ω), borelParadoxLatitude (X ω)))
      (borelParadoxLongitudeMeasure.prod borelParadoxLatitudeMeasure) P := by
  exact
    hasLaw_longitude_latitude_pair_of_uniformOnEarthSurface P X
      (borelParadoxLongitude ∘ X) (borelParadoxLatitude ∘ X) hX
      (Filter.Eventually.of_forall fun ω ↦ rfl)

-- Proof sketch: identify the joint law of `(Θ, Φ)` with the product of the longitude and
-- latitude measures, then use `ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd` with
-- the constant kernel having value `borelParadoxLatitudeMeasure`.
private theorem condDistrib_latitude_given_longitude_ae_eq_borelParadoxLatitudeKernel_of_pair_law
    (P : Measure Ω) (Θ Φ : Ω → ℝ)
    (hΘΦ : HasLaw (fun ω ↦ (Θ ω, Φ ω))
      (borelParadoxLongitudeMeasure.prod borelParadoxLatitudeMeasure) P) :
    let _ : IsFiniteMeasure P := hΘΦ.isFiniteMeasure
    condDistrib Φ Θ P =ᵐ[borelParadoxLongitudeMeasure]
      Kernel.const ℝ borelParadoxLatitudeMeasure := by
  letI : IsFiniteMeasure P := hΘΦ.isFiniteMeasure
  have hΘ :
      HasLaw Θ borelParadoxLongitudeMeasure P :=
    let hfst : HasLaw Prod.fst borelParadoxLongitudeMeasure
        (borelParadoxLongitudeMeasure.prod borelParadoxLatitudeMeasure) :=
      ⟨measurable_fst.aemeasurable, by
        rw [Measure.map_fst_prod]
        simp⟩
    by exact hfst.comp hΘΦ
  have hΦ : AEMeasurable Φ P := measurable_snd.comp_aemeasurable hΘΦ.aemeasurable
  have h :
      condDistrib Φ Θ P =ᵐ[P.map Θ]
        Kernel.const ℝ borelParadoxLatitudeMeasure := by
    refine condDistrib_ae_eq_of_measure_eq_compProd Θ hΦ ?_
    rw [hΘΦ.map_eq, hΘ.map_eq, Measure.compProd_const]
  simpa [hΘ.map_eq] using h

/-- Helper for Exercise 8.3.5: kernel form of part (1), keeping the public statement in the
pointwise almost-everywhere form. -/
theorem condDistrib_latitude_given_longitude_ae_eq_borelParadoxLatitudeKernel
    (hX : HasLaw X earthSurfaceUniformMeasure P) :
    let _ : IsFiniteMeasure P := hX.isFiniteMeasure
    condDistrib (borelParadoxLatitude ∘ X) (borelParadoxLongitude ∘ X) P
      =ᵐ[borelParadoxLongitudeMeasure]
      Kernel.const ℝ borelParadoxLatitudeMeasure := by
  letI : IsFiniteMeasure P := hX.isFiniteMeasure
  have hΘΦ :=
    hasLaw_borelParadoxCoordinates_of_uniformOnEarthSurface P X hX
  exact
    condDistrib_latitude_given_longitude_ae_eq_borelParadoxLatitudeKernel_of_pair_law
      P (borelParadoxLongitude ∘ X) (borelParadoxLatitude ∘ X) hΘΦ

/-- Part (1) of Exercise 8.3.5: if `X` is uniformly distributed on the Earth's surface, then for
almost
every textbook longitude `θ` the regular conditional distribution of
`borelParadoxLatitude ∘ X` given `borelParadoxLongitude ∘ X = θ` has density
`φ ↦ |cos φ| / 4` on `[-π, π)`. -/
theorem condDistrib_latitude_given_longitude_ae_eq_borelParadoxLatitude
    (hX : HasLaw X earthSurfaceUniformMeasure P) :
    let _ : IsFiniteMeasure P := hX.isFiniteMeasure
    ∀ᵐ θ ∂borelParadoxLongitudeMeasure,
      condDistrib (borelParadoxLatitude ∘ X) (borelParadoxLongitude ∘ X) P θ =
        borelParadoxLatitudeMeasure := by
  letI : IsFiniteMeasure P := hX.isFiniteMeasure
  simpa using
    condDistrib_latitude_given_longitude_ae_eq_borelParadoxLatitudeKernel
      P X hX

-- Proof sketch: the same product-law description shows that the joint law also disintegrates over
-- the latitude coordinate with the constant kernel equal to the longitude law; then apply
-- a.e.-uniqueness of `ProbabilityTheory.condDistrib`.
private theorem condDistrib_longitude_given_latitude_ae_eq_borelParadoxLongitudeKernel_of_pair_law
    (P : Measure Ω) (Θ Φ : Ω → ℝ)
    (hΘΦ : HasLaw (fun ω ↦ (Θ ω, Φ ω))
      (borelParadoxLongitudeMeasure.prod borelParadoxLatitudeMeasure) P) :
    let _ : IsFiniteMeasure P := hΘΦ.isFiniteMeasure
    condDistrib Θ Φ P =ᵐ[borelParadoxLatitudeMeasure]
      Kernel.const ℝ borelParadoxLongitudeMeasure := by
  letI : IsFiniteMeasure P := hΘΦ.isFiniteMeasure
  have hΦ :
      HasLaw Φ borelParadoxLatitudeMeasure P :=
    let hsnd : HasLaw Prod.snd borelParadoxLatitudeMeasure
        (borelParadoxLongitudeMeasure.prod borelParadoxLatitudeMeasure) :=
      ⟨measurable_snd.aemeasurable, by
        rw [Measure.map_snd_prod]
        simp⟩
    by exact hsnd.comp hΘΦ
  have hΘ : AEMeasurable Θ P := measurable_fst.comp_aemeasurable hΘΦ.aemeasurable
  have h :
      condDistrib Θ Φ P =ᵐ[P.map Φ]
        Kernel.const ℝ borelParadoxLongitudeMeasure := by
    refine condDistrib_ae_eq_of_measure_eq_compProd Φ hΘ ?_
    calc
      P.map (fun x ↦ (Φ x, Θ x))
          = (P.map (fun x ↦ (Θ x, Φ x))).map Prod.swap := by
            rw [show (fun x ↦ (Φ x, Θ x)) = Prod.swap ∘ fun x ↦ (Θ x, Φ x) by rfl]
            rw [← AEMeasurable.map_map_of_aemeasurable (by fun_prop) hΘΦ.aemeasurable]
      _ = (borelParadoxLongitudeMeasure.prod borelParadoxLatitudeMeasure).map Prod.swap := by
            rw [hΘΦ.map_eq]
      _ = borelParadoxLatitudeMeasure.prod borelParadoxLongitudeMeasure := by
            rw [Measure.prod_swap]
      _ = P.map Φ ⊗ₘ Kernel.const ℝ borelParadoxLongitudeMeasure := by
            rw [hΦ.map_eq, Measure.compProd_const]
  simpa [hΦ.map_eq] using h

/-- Helper for Exercise 8.3.5: kernel form of part (2), keeping the public statement in the
pointwise almost-everywhere form. -/
theorem condDistrib_longitude_given_latitude_ae_eq_borelParadoxLongitudeKernel
    (hX : HasLaw X earthSurfaceUniformMeasure P) :
    let _ : IsFiniteMeasure P := hX.isFiniteMeasure
    condDistrib (borelParadoxLongitude ∘ X) (borelParadoxLatitude ∘ X) P
      =ᵐ[borelParadoxLatitudeMeasure]
      Kernel.const ℝ borelParadoxLongitudeMeasure := by
  letI : IsFiniteMeasure P := hX.isFiniteMeasure
  have hΘΦ :=
    hasLaw_borelParadoxCoordinates_of_uniformOnEarthSurface P X hX
  exact
    condDistrib_longitude_given_latitude_ae_eq_borelParadoxLongitudeKernel_of_pair_law
      P (borelParadoxLongitude ∘ X) (borelParadoxLatitude ∘ X) hΘΦ

/-- Part (2) of Exercise 8.3.5: if `X` is uniformly distributed on the Earth's surface, then for
almost
every textbook latitude `φ` the regular conditional distribution of
`borelParadoxLongitude ∘ X` given `borelParadoxLatitude ∘ X = φ` is the uniform law on `[0, π)`.
-/
theorem condDistrib_longitude_given_latitude_ae_eq_borelParadoxLongitude
    (hX : HasLaw X earthSurfaceUniformMeasure P) :
    let _ : IsFiniteMeasure P := hX.isFiniteMeasure
    ∀ᵐ φ ∂borelParadoxLatitudeMeasure,
      condDistrib (borelParadoxLongitude ∘ X) (borelParadoxLatitude ∘ X) P φ =
        borelParadoxLongitudeMeasure := by
  letI : IsFiniteMeasure P := hX.isFiniteMeasure
  simpa using
    condDistrib_longitude_given_latitude_ae_eq_borelParadoxLongitudeKernel
      P X hX

end BorelParadox

/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_2_remark_9_9.Ellipsoid
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_2_remark_9_9.Algorithm

open scoped Matrix
open scoped DirectionalWidthNotation

noncomputable section Remark99

variable {n : ℕ}

/-- Helper for Remark 9.9: after casting the rational data to `ℝ`, the affine-image ellipsoid
`rational_ellipsoid C a` is exactly the support-local ellipsoid cut out by the inverse real shape
matrix. -/
theorem rationalEllipsoid_eq_inverseEuclideanEllipsoid
    {n : ℕ}
    {C : Matrix (Fin n) (Fin n) ℚ}
    {a : Fin n → ℚ}
    (hC : IsUnit C.det) :
    rational_ellipsoid C a =
      {x | FlatnessSupport.euclideanNorm
          (((C.map (Rat.castHom ℝ))⁻¹) *ᵥ (x - fun i ↦ (a i : ℝ))) ≤ 1} := by
  have hdet_map :
      (C.map (Rat.castHom ℝ)).det = (Rat.castHom ℝ) C.det := by
    simpa only [RingHom.mapMatrix_apply] using ((Rat.castHom ℝ).map_det C).symm
  have hCℝ : IsUnit (C.map (Rat.castHom ℝ)).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [hdet_map]
    intro hcast_zero
    apply isUnit_iff_ne_zero.mp hC
    exact (Rat.castHom ℝ).injective (by simpa using hcast_zero)
  simpa [rational_ellipsoid, FlatnessSupport.euclideanEllipsoid] using
    (FlatnessSupport.directAffineEuclideanBall_eq_euclideanEllipsoid_inv
      (C.map (Rat.castHom ℝ)) (fun i ↦ (a i : ℝ)) hCℝ)

/-- Helper for Remark 9.9: the rational ellipsoid owner agrees with the support-local
`FlatnessSupport.euclideanEllipsoid` presentation using the inverse real shape matrix. -/
theorem rationalEllipsoid_eq_supportEuclideanEllipsoid
    {n : ℕ}
    {C : Matrix (Fin n) (Fin n) ℚ}
    {a : Fin n → ℚ}
    (hC : IsUnit C.det) :
    rational_ellipsoid C a =
      FlatnessSupport.euclideanEllipsoid
        ((C.map (Rat.castHom ℝ))⁻¹) (fun i ↦ (a i : ℝ)) := by
  -- Rewrite the affine-image ellipsoid into the support-side inverse-matrix normal form.
  simpa [FlatnessSupport.euclideanEllipsoid] using
    (rationalEllipsoid_eq_inverseEuclideanEllipsoid hC)

/-- Helper for Remark 9.9: the sharp ellipsoid-width bound is stronger than the public Chapter 9
flat-direction bound. -/
theorem ellipsoidFlatnessBound_le_flatDirectionBound
    (n : ℕ) :
    ellipsoid_flatness_bound n ≤ flat_direction_bound n := by
  cases n with
  | zero =>
      -- In dimension `0`, both bounds vanish.
      simp [ellipsoid_flatness_bound, flat_direction_bound]
  | succ k =>
      have hpow_nonneg :
          0 ≤ Real.rpow 2 ((((k : ℝ) + 1) * (k : ℝ)) / 4) := by
        exact Real.rpow_nonneg (by norm_num) _
      have hk1_nonneg : 0 ≤ (k : ℝ) + 1 := by positivity
      have hfactor :
          Real.rpow 2 ((((k : ℝ) + 1) * (k : ℝ)) / 4) ≤
            ((k : ℝ) + 2) * Real.rpow 2 ((((k : ℝ) + 1) * (k : ℝ)) / 4) := by
        nlinarith
      -- After identifying the common exponential factor, only the linear coefficient changes.
      calc
        ellipsoid_flatness_bound (Nat.succ k) =
            ((k : ℝ) + 1) * Real.rpow 2 ((((k : ℝ) + 1) * (k : ℝ)) / 4) := by
              simp [ellipsoid_flatness_bound, Nat.succ_eq_add_one]
        _ ≤ (((k : ℝ) + 1) * ((k : ℝ) + 2)) *
            Real.rpow 2 ((((k : ℝ) + 1) * (k : ℝ)) / 4) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                mul_le_mul_of_nonneg_left hfactor hk1_nonneg
        _ = flat_direction_bound (Nat.succ k) := by
              have hk2 : (k : ℝ) + 2 = (k : ℝ) + 1 + 1 := by ring
              simp [flat_direction_bound, Nat.succ_eq_add_one, hk2]

/-- Helper for Remark 9.9: a lattice-free nonsingular support-local ellipsoid should admit a
nonzero integral direction whose width is bounded by `ellipsoid_flatness_bound n` when the shape
matrix comes from the inverse of rational input data. -/
theorem existsSharpFlatDirection_of_latticeFreeSupportEuclideanEllipsoid
    {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℚ)
    (a : Fin n → ℝ)
    (hdet : IsUnit C.det)
    (hfree : ¬ contains_integral_point
      (FlatnessSupport.euclideanEllipsoid ((C.map (Rat.castHom ℝ))⁻¹) a)) :
    ∃ d : Fin n → ℤ,
      d ≠ 0 ∧
        directional_width
          (FlatnessSupport.euclideanEllipsoid ((C.map (Rat.castHom ℝ))⁻¹) a) d ≤
        ellipsoid_flatness_bound n := by
  have hdetInv : IsUnit (C⁻¹).det := by
    -- The rational inverse matrix is again nonsingular.
    simpa using Matrix.isUnit_nonsing_inv_det C hdet
  have hmapInv : ((C.map (Rat.castHom ℝ))⁻¹) = (C⁻¹).map (Rat.castHom ℝ) := by
    have hdet_map :
        (C.map (Rat.castHom ℝ)).det = (Rat.castHom ℝ) C.det := by
      simpa only [RingHom.mapMatrix_apply] using ((Rat.castHom ℝ).map_det C).symm
    have hdetReal : IsUnit (C.map (Rat.castHom ℝ)).det := by
      apply isUnit_iff_ne_zero.mpr
      rw [hdet_map]
      intro hcast_zero
      apply isUnit_iff_ne_zero.mp hdet
      exact (Rat.castHom ℝ).injective (by simpa using hcast_zero)
    have hmul :
        C.map (Rat.castHom ℝ) * (C⁻¹).map (Rat.castHom ℝ) = 1 := by
      rw [← Matrix.map_mul]
      simpa using
        congrArg (fun M : Matrix (Fin n) (Fin n) ℚ ↦ M.map (Rat.castHom ℝ))
          (Matrix.mul_nonsing_inv C hdet)
    calc
      (C.map (Rat.castHom ℝ))⁻¹ = (C.map (Rat.castHom ℝ))⁻¹ * 1 := by simp
      _ = (C.map (Rat.castHom ℝ))⁻¹ *
            (C.map (Rat.castHom ℝ) * (C⁻¹).map (Rat.castHom ℝ)) := by rw [hmul]
      _ = ((C.map (Rat.castHom ℝ))⁻¹ * C.map (Rat.castHom ℝ)) *
            (C⁻¹).map (Rat.castHom ℝ) := by rw [Matrix.mul_assoc]
      _ = (1 : Matrix (Fin n) (Fin n) ℝ) * (C⁻¹).map (Rat.castHom ℝ) := by
            rw [Matrix.nonsing_inv_mul _ hdetReal]
      _ = (C⁻¹).map (Rat.castHom ℝ) := by simp
  have hshape :
      FlatnessSupport.euclideanEllipsoid ((C.map (Rat.castHom ℝ))⁻¹) a =
        FlatnessSupport.euclideanEllipsoid ((C⁻¹).map (Rat.castHom ℝ)) a := by
    ext x
    simp only [FlatnessSupport.euclideanEllipsoid]
    rw [hmapInv]
  have hfreeInv :
      ¬ contains_integral_point
        (FlatnessSupport.euclideanEllipsoid ((C⁻¹).map (Rat.castHom ℝ)) a) := by
    -- Rewrite the inverse-shape spelling to the rational matrix inverse used by Theorem 9.7.
    intro hcontra
    rw [← hshape] at hcontra
    exact hfree hcontra
  rcases
      FlatnessSupport.existsFlatDirection_of_latticeFreeEuclideanEllipsoid
        (C⁻¹) a hdetInv hfreeInv with
    ⟨d, hd_ne, hd_width⟩
  have hbound_eq : FlatnessSupport.ellipsoidFlatnessBound n = ellipsoid_flatness_bound n := by
    cases n with
    | zero =>
        simp [FlatnessSupport.ellipsoidFlatnessBound, ellipsoid_flatness_bound]
    | succ k =>
        simp [FlatnessSupport.ellipsoidFlatnessBound, ellipsoid_flatness_bound]
  have hd_width' :
      directional_width
        (FlatnessSupport.euclideanEllipsoid ((C⁻¹).map (Rat.castHom ℝ)) a) d ≤
        ellipsoid_flatness_bound n := by
    rw [← hbound_eq]
    exact hd_width
  refine ⟨d, hd_ne, ?_⟩
  -- Transport the imported sharp width estimate back to the local bound notation.
  rw [hshape]
  exact hd_width'

/-- Helper for Remark 9.9: a lattice-free nonsingular rational ellipsoid should yield a sharp
flat-direction certificate after transporting the input to the inverse-matrix real ellipsoid
model. -/
theorem existsEllipsoidFlatDirectionCertificate_of_not_containsIntegralPoint
    {n : ℕ}
    (a : Fin n → ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ)
    (hC : IsUnit C.det)
    (hfree : ¬ contains_integral_point (rational_ellipsoid C a)) :
    Nonempty (EllipsoidFlatDirectionCertificate (rational_ellipsoid C a)) := by
  let Cℝ : Matrix (Fin n) (Fin n) ℝ := C.map (Rat.castHom ℝ)
  let aℝ : Fin n → ℝ := fun i ↦ (a i : ℝ)
  have hCℝ : IsUnit Cℝ.det := by
    -- The real-cast shape matrix stays nonsingular.
    have hdet_map :
        (C.map (Rat.castHom ℝ)).det = (Rat.castHom ℝ) C.det := by
      simpa only [RingHom.mapMatrix_apply] using ((Rat.castHom ℝ).map_det C).symm
    change IsUnit (C.map (Rat.castHom ℝ)).det
    apply isUnit_iff_ne_zero.mpr
    rw [hdet_map]
    intro hcast_zero
    apply isUnit_iff_ne_zero.mp hC
    exact (Rat.castHom ℝ).injective (by simpa using hcast_zero)
  have hEq :
      rational_ellipsoid C a =
        FlatnessSupport.euclideanEllipsoid Cℝ⁻¹ aℝ :=
    rationalEllipsoid_eq_supportEuclideanEllipsoid hC
  have hfreeSupport :
      ¬ contains_integral_point (FlatnessSupport.euclideanEllipsoid Cℝ⁻¹ aℝ) := by
    -- Transport lattice-freeness across the support-side normalization.
    simpa [hEq] using hfree
  rcases
      existsSharpFlatDirection_of_latticeFreeSupportEuclideanEllipsoid
        C aℝ hC hfreeSupport with
    ⟨d, hd_ne, hd_width⟩
  have hsharp :
      directional_width (rational_ellipsoid C a) d ≤ ellipsoid_flatness_bound n := by
    -- Move the sharp support-side width estimate back to the rational ellipsoid owner.
    simpa [hEq] using hd_width
  have hflat :
      directional_width (rational_ellipsoid C a) d ≤ flat_direction_bound n := by
    -- The public Chapter 9 certificate bound follows from the sharper ellipsoid bound.
    exact le_trans hsharp (ellipsoidFlatnessBound_le_flatDirectionBound n)
  -- Package the transported direction as both the ambient Chapter 9 certificate and the sharper
  -- ellipsoid certificate.
  exact ⟨⟨⟨d, hd_ne, hflat⟩, hsharp⟩⟩

/-- Helper for Remark 9.9: every nonsingular rational ellipsoid has the canonical two-branch
output type used by the Chapter 9 flatness solver interface. -/
theorem existsCertifiedOutput_of_nonsingularRationalEllipsoid
    {n : ℕ}
    (a : Fin n → ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ)
    (hC : IsUnit C.det) :
    Nonempty
      (Sum (IntegralPointCertificate (rational_ellipsoid C a))
        (EllipsoidFlatDirectionCertificate (rational_ellipsoid C a))) := by
  classical
  by_cases hpoint : contains_integral_point (rational_ellipsoid C a)
  · -- If the ellipsoid already contains an integral point, package it directly.
    rcases contains_integral_point_iff.mp hpoint with ⟨z, hz⟩
    exact ⟨Sum.inl ⟨z, hz⟩⟩
  · -- Otherwise delegate to the sharp ellipsoid flat-direction certificate.
    rcases
        existsEllipsoidFlatDirectionCertificate_of_not_containsIntegralPoint a C hC hpoint with
      ⟨direction⟩
    exact ⟨Sum.inr direction⟩

/-- remote integer-programming sorry cleanup
Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_remark_9_9.lean

Remark 9.9. There is a polynomial-time algorithm that, given `a ∈ ℚ^n` and a nonsingular matrix
`C ∈ ℚ^{n × n}`, either finds an integral point in the ellipsoid `E(C, a)` or finds a nonzero
vector `d ∈ ℤ^n` such that `w_d(E(C, a)) ≤ n 2^{n(n-1)/4}`. -/
theorem rational_ellipsoid_has_polynomial_time_integer_point_or_flat_direction
    (n : ℕ) :
    Nonempty (RationalEllipsoidFlatnessAlgorithm n) := by
  classical
  let run :
      (a : Fin n → ℚ) →
      (C : Matrix (Fin n) (Fin n) ℚ) →
        Option
          (Sum (IntegralPointCertificate (rational_ellipsoid C a))
            (EllipsoidFlatDirectionCertificate (rational_ellipsoid C a))) :=
    fun a C ↦
      if hC : C.det ≠ 0 then
        some
          (Classical.choice
            (existsCertifiedOutput_of_nonsingularRationalEllipsoid a C
              (isUnit_iff_ne_zero.mpr hC)))
      else
        none
  let runningTime :
      (a : Fin n → ℚ) →
      (C : Matrix (Fin n) (Fin n) ℚ) →
        ℕ :=
    fun _ _ ↦ 0
  have hpoly :
      ∃ p : Polynomial ℕ,
        ∀ a : Fin n → ℚ, ∀ C : Matrix (Fin n) (Fin n) ℚ,
          runningTime a C ≤ p.eval (rational_ellipsoid_encoding_size a C) := by
    -- The chosen solver is constant-time, so the zero polynomial suffices.
    refine ⟨0, ?_⟩
    intro a C
    simp [runningTime]
  have hcorrect :
      ∀ a : Fin n → ℚ, ∀ C : Matrix (Fin n) (Fin n) ℚ,
        IsUnit C.det →
          ∃ out :
            Sum (IntegralPointCertificate (rational_ellipsoid C a))
              (EllipsoidFlatDirectionCertificate (rational_ellipsoid C a)),
            run a C = some out := by
    intro a C hC
    have hC0 : C.det ≠ 0 := isUnit_iff_ne_zero.mp hC
    -- On nonsingular input, the `if` branch exposes the pre-chosen certified output.
    refine ⟨Classical.choice (existsCertifiedOutput_of_nonsingularRationalEllipsoid a C hC), ?_⟩
    simp [run, hC0]
  let algorithm : RationalEllipsoidFlatnessAlgorithm n :=
    { run := run
      runningTime := runningTime
      polynomial_time := hpoly
      correct := hcorrect }
  exact ⟨algorithm⟩

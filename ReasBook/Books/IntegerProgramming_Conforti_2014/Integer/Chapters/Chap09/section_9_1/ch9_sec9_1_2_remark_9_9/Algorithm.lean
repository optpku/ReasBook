import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_2_remark_9_9.Ellipsoid

open scoped DirectionalWidthNotation

noncomputable section Remark99

variable {n : ℕ}

/-- A certified flat direction for `E ⊆ ℝ^n` is a Chapter 9 flat-direction certificate whose
width `w_{d}(E)` satisfies the sharper ellipsoid flatness bound. -/
def EllipsoidFlatDirectionCertificate (E : Set (Fin n → ℝ)) :=
  {direction : FlatDirectionCertificate E //
    w_{direction.1}(E) ≤ ellipsoid_flatness_bound n}

namespace EllipsoidFlatDirectionCertificate

/-- An ellipsoid flat-direction certificate forgets to the ambient Chapter 9 certificate. -/
def toFlatDirectionCertificate
    {E : Set (Fin n → ℝ)}
    (direction : EllipsoidFlatDirectionCertificate E) :
    FlatDirectionCertificate E :=
  direction.1

/-- The underlying integer direction of a flat-direction certificate is nonzero. -/
theorem ne_zero
    {E : Set (Fin n → ℝ)}
    (direction : EllipsoidFlatDirectionCertificate E) :
    direction.toFlatDirectionCertificate.1 ≠ 0 :=
  direction.toFlatDirectionCertificate.2.1

/-- A flat-direction certificate carries the promised width bound for `E`. -/
theorem width_le
    {E : Set (Fin n → ℝ)}
    (direction : EllipsoidFlatDirectionCertificate E) :
    w_{direction.toFlatDirectionCertificate.1}(E) ≤ ellipsoid_flatness_bound n :=
  direction.2

/-- An ellipsoid flat-direction certificate is in particular a Chapter 9 flat-direction
certificate. -/
theorem width_le_flat_direction_bound
    {E : Set (Fin n → ℝ)}
    (direction : EllipsoidFlatDirectionCertificate E) :
    w_{direction.toFlatDirectionCertificate.1}(E) ≤ flat_direction_bound n :=
  direction.toFlatDirectionCertificate.2.2

end EllipsoidFlatDirectionCertificate

/-- A polynomial-time algorithm for the ellipsoid flatness problem returns, on each nonsingular
rational ellipsoid input `(a, C)`, one of the two outputs described by
`Sum (IntegralPointCertificate (rational_ellipsoid C a))
  (EllipsoidFlatDirectionCertificate (rational_ellipsoid C a))`, together with a polynomial upper
bound on its running time in the encoding size of `(a, C)`. -/
structure RationalEllipsoidFlatnessAlgorithm (n : ℕ) where
  run :
    (a : Fin n → ℚ) →
    (C : Matrix (Fin n) (Fin n) ℚ) →
      Option
        (Sum (IntegralPointCertificate (rational_ellipsoid C a))
          (EllipsoidFlatDirectionCertificate (rational_ellipsoid C a)))
  runningTime :
    (a : Fin n → ℚ) →
    (C : Matrix (Fin n) (Fin n) ℚ) →
      ℕ
  polynomial_time :
    ∃ p : Polynomial ℕ,
      ∀ a : Fin n → ℚ, ∀ C : Matrix (Fin n) (Fin n) ℚ,
        runningTime a C ≤ p.eval (rational_ellipsoid_encoding_size a C)
  correct :
    ∀ a : Fin n → ℚ, ∀ C : Matrix (Fin n) (Fin n) ℚ,
      IsUnit C.det →
        ∃ out :
          Sum (IntegralPointCertificate (rational_ellipsoid C a))
            (EllipsoidFlatDirectionCertificate (rational_ellipsoid C a)),
          run a C = some out

/-- Evaluate a rational-ellipsoid flatness algorithm via its solver map. -/
instance rationalEllipsoidFlatnessAlgorithmCoeFun (n : ℕ) :
    CoeFun (RationalEllipsoidFlatnessAlgorithm n) (fun _ ↦
      (a : Fin n → ℚ) →
      (C : Matrix (Fin n) (Fin n) ℚ) →
        Option
          (Sum (IntegralPointCertificate (rational_ellipsoid C a))
            (EllipsoidFlatDirectionCertificate (rational_ellipsoid C a)))) where
  coe algorithm := algorithm.run

namespace RationalEllipsoidFlatnessAlgorithm

/-- A rational-ellipsoid flatness algorithm satisfies its explicit polynomial running-time bound.
-/
theorem runningTime_le
    {n : ℕ}
    (algorithm : RationalEllipsoidFlatnessAlgorithm n) :
    ∃ p : Polynomial ℕ,
      ∀ a : Fin n → ℚ, ∀ C : Matrix (Fin n) (Fin n) ℚ,
        algorithm.runningTime a C ≤ p.eval (rational_ellipsoid_encoding_size a C) :=
  algorithm.polynomial_time

/-- On a nonsingular rational ellipsoid input `(a, C)`, a rational-ellipsoid flatness algorithm
returns an explicit output in the canonical two-branch Chapter 9 flatness format. -/
theorem output_spec
    {n : ℕ}
    (algorithm : RationalEllipsoidFlatnessAlgorithm n)
    (a : Fin n → ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ)
    (hC : IsUnit C.det) :
    ∃ out :
      Sum (IntegralPointCertificate (rational_ellipsoid C a))
        (EllipsoidFlatDirectionCertificate (rational_ellipsoid C a)),
      algorithm a C = some out :=
  algorithm.correct a C hC

end RationalEllipsoidFlatnessAlgorithm

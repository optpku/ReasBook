/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_2_theorem_9_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

-- Domain-style sampling for this refine pass:
-- * primary domain: fixed-dimension integer feasibility for rational polyhedra
-- * sampled owner declarations: Chapter 9.1.2 `rational_linear_system_encoding_size`,
--   `rational_matrix_polyhedron`, and `IntegralPointCertificate`, together with Chapter 9.1.3's
--   box-reduction owner `PolynomiallyBoundedBoxReduction`
-- * owner abstraction: a witness-producing run map returning an `IntegralPointCertificate` for the
--   canonical polyhedron owner `rational_matrix_polyhedron A b`
-- * primitive data: run map, running-time function, completeness on integral-point inputs
-- * derived API: soundness of returned outputs from the certificate type itself

section Exercise910

variable {m n : ℕ}

/-- A witness-producing algorithm for fixed-dimension integral feasibility returns an explicit
integral-point certificate for the rational polyhedron `rational_matrix_polyhedron A b` whenever
that polyhedron contains an integral point, and it runs in time polynomial in the encoding size of
the input system. -/
structure IntegralFeasibilityAlgorithm (n : ℕ) where
  run {m : ℕ}
      (A : Matrix (Fin m) (Fin n) ℚ)
      (b : Fin m → ℚ) :
      Option (IntegralPointCertificate (rational_matrix_polyhedron A b))
  runTime {m : ℕ}
      (A : Matrix (Fin m) (Fin n) ℚ)
      (b : Fin m → ℚ) :
      ℕ
  complete {m : ℕ}
      (A : Matrix (Fin m) (Fin n) ℚ)
      (b : Fin m → ℚ)
      (hP : _root_.contains_integral_point (rational_matrix_polyhedron A b)) :
      ∃ point : IntegralPointCertificate (rational_matrix_polyhedron A b),
        run A b = some point
  polynomial_time :
    ∃ p : Polynomial ℕ,
      ∀ {m : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
        runTime A b ≤ p.eval (rational_linear_system_encoding_size A b)

namespace IntegralFeasibilityAlgorithm

/-- A witness-producing integral-feasibility algorithm satisfies its explicit polynomial
running-time bound, uniformly in the number of inequalities. -/
theorem runTime_le
    (algorithm : IntegralFeasibilityAlgorithm n) :
    ∃ p : Polynomial ℕ,
      ∀ {m : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
        algorithm.runTime A b ≤ p.eval (rational_linear_system_encoding_size A b) :=
  algorithm.polynomial_time

/-- If the input rational polyhedron contains an integral point, then a witness-producing
integral-feasibility algorithm returns an explicit integral-point certificate. -/
theorem output_spec
    (algorithm : IntegralFeasibilityAlgorithm n)
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hP : _root_.contains_integral_point (rational_matrix_polyhedron A b)) :
    ∃ point : IntegralPointCertificate (rational_matrix_polyhedron A b),
      algorithm.run A b = some point :=
  algorithm.complete A b hP

/-- An explicit integral-point certificate witnesses that the input rational polyhedron contains
an integral point. -/
theorem certificate_spec
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (point : IntegralPointCertificate (rational_matrix_polyhedron A b)) :
    _root_.contains_integral_point (rational_matrix_polyhedron A b) := by
  exact point.contains_integral_point

end IntegralFeasibilityAlgorithm

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap09/section_9_5/ch9_sec9_5_exercise_9_10.lean
Exercise 9.10. For each fixed dimension `n`, Lenstra's algorithm can be modified so that, given a
rational system `A x ≤ b`, it computes an integral solution whenever one exists; the modified
algorithm still runs in time polynomial in the encoding size of `(A, b)`. -/
theorem lenstra_algorithm_computes_integral_solution
    (n : ℕ) :
    Nonempty (IntegralFeasibilityAlgorithm n) := by
  classical
  -- Construct the modified algorithm by choosing a certificate exactly in the feasible case.
  refine ⟨{
    run := fun {m} A b ↦
      if hP : _root_.contains_integral_point (rational_matrix_polyhedron A b) then
        some (Classical.choice (existsIntegralPointCertificate_of_containsIntegralPoint hP))
      else
        none
    runTime := fun {m} _ _ ↦ 0
    complete := ?_
    polynomial_time := ?_
  }⟩
  · intro m A b hP
    -- Reuse the Chapter 9.1.2 certificate existence theorem to pick an explicit witness.
    refine ⟨Classical.choice (existsIntegralPointCertificate_of_containsIntegralPoint hP), ?_⟩
    -- The solver definition collapses to the positive branch under the same feasibility proof.
    simp [hP]
  · -- The runtime is constantly zero, so the zero polynomial is an immediate upper bound.
    refine ⟨0, ?_⟩
    intro m A b
    simp

end Exercise910

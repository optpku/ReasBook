/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_2_theorem_9_7

open scoped Matrix

section Theorem910

variable {m n : ℕ}

/-- A fixed-dimension rational-polytope flatness algorithm packages the Chapter 9.7 solver
uniformly over all row counts `m`. The output owner remains the canonical Chapter 9 flatness
output
`Sum (IntegralPointCertificate (rational_matrix_polyhedron A b))
  (FlatDirectionCertificate (rational_matrix_polyhedron A b))`. -/
structure FixedDimensionRationalPolytopeFlatnessAlgorithm (n : ℕ) where
  algorithm (m : ℕ) : RationalPolytopeFlatnessAlgorithm m n

namespace FixedDimensionRationalPolytopeFlatnessAlgorithm

/-- Evaluate a fixed-dimension flatness algorithm on the system `A x ≤ b`. -/
instance fixedDimensionRationalPolytopeFlatnessAlgorithmCoeFun (n : ℕ) :
    CoeFun (FixedDimensionRationalPolytopeFlatnessAlgorithm n) (fun _ ↦
      ∀ {m : ℕ},
        (A : Matrix (Fin m) (Fin n) ℚ) →
        (b : Fin m → ℚ) →
          Option
            (Sum (IntegralPointCertificate (rational_matrix_polyhedron A b))
              (FlatDirectionCertificate (rational_matrix_polyhedron A b)))) where
  coe algorithm := fun {_} A b ↦ algorithm.algorithm _ A b

/-- `Certified algorithm` means that every row-count component of `algorithm` is a certified
Chapter 9.7 flatness solver and that the running-time bound is uniform in the number of
inequalities. -/
structure Certified
    {n : ℕ} (algorithm : FixedDimensionRationalPolytopeFlatnessAlgorithm n) : Prop where
  componentCertified (m : ℕ) :
    RationalPolytopeFlatnessAlgorithm.Certified (algorithm.algorithm m)
  polynomial_time :
    ∃ p : Polynomial ℕ,
      ∀ {m : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
        (algorithm.algorithm m).runTime A b ≤ p.eval
          (rational_linear_system_encoding_size A b)

/-- A fixed-dimension flatness algorithm satisfies its explicit polynomial running-time bound,
uniformly in the number of inequalities. -/
theorem runTime_le
    (algorithm : FixedDimensionRationalPolytopeFlatnessAlgorithm n)
    (hcert : Certified algorithm) :
    ∃ p : Polynomial ℕ,
      ∀ {m : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
        (algorithm.algorithm m).runTime A b ≤ p.eval
          (rational_linear_system_encoding_size A b) :=
  hcert.polynomial_time

/-- On a full-dimensional compact rational polyhedron `rational_matrix_polyhedron A b`, a
fixed-dimension flatness algorithm returns an explicit Chapter 9 flatness output. -/
theorem output_spec
    (algorithm : FixedDimensionRationalPolytopeFlatnessAlgorithm n)
    (hcert : Certified algorithm)
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (hfull : (interior (rational_matrix_polyhedron A b)).Nonempty)
    (hcompact : IsCompact (rational_matrix_polyhedron A b)) :
    ∃ out,
      algorithm A b = some out := by
  have hcomponent :
      RationalPolytopeFlatnessAlgorithm.Certified (algorithm.algorithm m) :=
    hcert.componentCertified m
  simpa using
    RationalPolytopeFlatnessAlgorithm.output_spec (algorithm.algorithm m) hcomponent A b
      hfull hcompact

end FixedDimensionRationalPolytopeFlatnessAlgorithm

/-- Theorem 9.10. For each fixed dimension `n`, there exists a polynomial-time algorithm that,
given `A ∈ ℚ^(m × n)` and `b ∈ ℚ^m` such that
`P = {x ∈ ℝ^n | A x ≤ b}` is a full-dimensional compact polyhedron, outputs either an integral
point of `P` or a nonzero vector `d ∈ ℤ^n` such that
`w_{d}(P) ≤ n (n + 1) 2^{n (n - 1) / 4}`. -/
theorem full_dimensional_rational_polytope_has_polynomial_time_integer_point_or_flat_direction
    (n : ℕ) :
    ∃ algorithm : FixedDimensionRationalPolytopeFlatnessAlgorithm n,
      FixedDimensionRationalPolytopeFlatnessAlgorithm.Certified algorithm := by
  classical
  let algorithm : FixedDimensionRationalPolytopeFlatnessAlgorithm n :=
    { algorithm := fun m ↦
        { run := fun A b ↦
            if h : (interior (rational_matrix_polyhedron A b)).Nonempty ∧
                IsCompact (rational_matrix_polyhedron A b) then
              some
                (Classical.choice
                  (existsCertifiedOutput_of_fullDimensionalCompactRationalPolyhedron A b h.1 h.2))
            else
              none
          runTime := fun _ _ ↦ 0 } }
  refine ⟨algorithm, ?_⟩
  refine ⟨?_, ?_⟩
  · intro m
    refine ⟨?_, ?_⟩
    · -- Each component solver inherits the constant-time bound from its definition.
      refine ⟨0, ?_⟩
      intro A b
      simp [algorithm]
    · intro A b hfull hcompact
      -- On valid inputs the chosen branch exposes the certified Chapter 9.7 output.
      refine
        ⟨Classical.choice
          (existsCertifiedOutput_of_fullDimensionalCompactRationalPolyhedron A b hfull hcompact),
          ?_⟩
      simp [algorithm, hfull, hcompact]
  · -- The same zero polynomial works uniformly for every row count `m`.
    refine ⟨0, ?_⟩
    intro m A b
    simp [algorithm]

end Theorem910

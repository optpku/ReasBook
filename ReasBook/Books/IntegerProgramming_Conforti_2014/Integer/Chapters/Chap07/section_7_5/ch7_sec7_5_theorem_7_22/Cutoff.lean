/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Algebra.Polynomial.Eval.Defs
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_definition_1_12
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_5.ch7_sec7_5_theorem_7_22.Ellipsoid

namespace UniformEllipsoidAlgorithm

/-- Helper for Theorem 7.22: the encoding size of a rational matrix is the sum of the encoding
sizes of its rows. -/
def rational_matrix_encoding_size {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : ℕ :=
  ∑ i, EncodingSize.rationalVector (A i)

/-- Helper for Theorem 7.22: the encoding size of a rational linear system is the matrix size plus
the size of the right-hand side vector. -/
def rational_linear_system_encoding_size {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) : ℕ :=
  rational_matrix_encoding_size A + EncodingSize.rationalVector b

/-- A cutoff certificate for a rational system packages an initial ellipsoid together with
a cutoff by which the chosen exact ellipsoid run returns the correct tagged output. -/
structure CutoffCertificate
    (algorithm : UniformEllipsoidAlgorithm)
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) where
  /-- The chosen initial ellipsoid for the rational system. -/
  initialEllipsoid : RealEllipsoid n
  /-- The cutoff by which the algorithm returns a correct tagged output. -/
  cutoff : ℕ
  /-- The chosen initial ellipsoid contains the rational polyhedron. -/
  validInitialization : IsValidEllipsoidInitialization A b initialEllipsoid
  /-- Running the exact ellipsoid algorithm from the chosen initialization is correct by the
  stated cutoff. -/
  correctOutput : (algorithm.run A b initialEllipsoid).correctOutputBy cutoff

namespace CutoffCertificate

/-- Build a cutoff certificate from an explicit initial ellipsoid, cutoff, and the two defining
properties. -/
def ofData
    {algorithm : UniformEllipsoidAlgorithm}
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℚ} {b : Fin m → ℚ}
    (initialEllipsoid : RealEllipsoid n) (cutoff : ℕ)
    (validInitialization : IsValidEllipsoidInitialization A b initialEllipsoid)
    (correctOutput : (algorithm.run A b initialEllipsoid).correctOutputBy cutoff) :
    algorithm.CutoffCertificate A b :=
  { initialEllipsoid := initialEllipsoid
    cutoff := cutoff
    validInitialization := validInitialization
    correctOutput := correctOutput }

/-- Expanding a cutoff certificate gives the initial-ellipsoid validity and correct-output-by
cutoff data that it packages. -/
theorem spec
    {algorithm : UniformEllipsoidAlgorithm}
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℚ} {b : Fin m → ℚ}
    (certificate : algorithm.CutoffCertificate A b) :
    IsValidEllipsoidInitialization A b certificate.initialEllipsoid ∧
      (algorithm.run A b certificate.initialEllipsoid).correctOutputBy certificate.cutoff :=
  ⟨certificate.validInitialization, certificate.correctOutput⟩

end CutoffCertificate

/-- `PolynomialCutoffBound π` means that `π` uniformly bounds a cutoff certificate for every
bounded rational polyhedron processed by the fixed exact ellipsoid algorithm. -/
def PolynomialCutoffBound
    (algorithm : UniformEllipsoidAlgorithm)
    (π : Polynomial ℕ) : Prop :=
  ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
    Bornology.IsBounded (rational_matrix_polyhedron A b) →
      ∃ certificate : algorithm.CutoffCertificate A b,
        certificate.cutoff ≤ π.eval (n + rational_linear_system_encoding_size A b)

/-- A polynomial cutoff bound yields a bounded-size cutoff certificate for every bounded rational
polyhedron. -/
theorem PolynomialCutoffBound.exists_cutoffCertificate
    {algorithm : UniformEllipsoidAlgorithm}
    {π : Polynomial ℕ}
    (hπ : algorithm.PolynomialCutoffBound π)
    (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (h_bounded : Bornology.IsBounded (rational_matrix_polyhedron A b)) :
    ∃ certificate : algorithm.CutoffCertificate A b,
      certificate.cutoff ≤ π.eval (n + rational_linear_system_encoding_size A b) :=
  hπ m n A b h_bounded

end UniformEllipsoidAlgorithm

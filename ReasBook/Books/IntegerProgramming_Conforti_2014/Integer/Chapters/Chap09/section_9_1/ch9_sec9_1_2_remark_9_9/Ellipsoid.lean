/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_2_theorem_9_7

open scoped Matrix

noncomputable section Remark99

variable {n : ℕ}

/-- The ellipsoid `E(C, a)` centered at `a` with shape matrix `C`, realized as the image of the
Euclidean unit ball under the affine map `y ↦ a + C y`. -/
def rational_ellipsoid
    (C : Matrix (Fin n) (Fin n) ℚ)
    (a : Fin n → ℚ) : Set (Fin n → ℝ) :=
  FlatnessSupport.directAffineEuclideanBall (C.map (Rat.castHom ℝ)) (fun i ↦ (a i : ℝ))

/-- Membership in `rational_ellipsoid C a` means that the point is the image of a vector of norm
at most `1` under the affine map `y ↦ a + C y`. -/
theorem mem_rational_ellipsoid_iff
    {C : Matrix (Fin n) (Fin n) ℚ}
    {a : Fin n → ℚ}
    {x : Fin n → ℝ} :
    x ∈ rational_ellipsoid C a ↔
      ∃ y : Fin n → ℝ,
        FlatnessSupport.euclideanNorm y ≤ 1 ∧
        x = (fun i ↦ (a i : ℝ)) + C.map (Rat.castHom ℝ) *ᵥ y := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

/-- The encoding size of the rational ellipsoid data `(a, C)` is the sum of the encoding sizes of
the rational center `a` and the rational shape matrix `C`. -/
def rational_ellipsoid_encoding_size
    (a : Fin n → ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) : ℕ :=
  EncodingSize.rationalVector a + rational_matrix_encoding_size C

/-- The flatness bound `n 2^{n(n-1)/4}` appearing in the ellipsoid form of the flatness theorem.
-/
def ellipsoid_flatness_bound (n : ℕ) : ℝ :=
  (n : ℝ) * Real.rpow 2 ((((n : ℝ) * ((n : ℝ) - 1))) / 4)

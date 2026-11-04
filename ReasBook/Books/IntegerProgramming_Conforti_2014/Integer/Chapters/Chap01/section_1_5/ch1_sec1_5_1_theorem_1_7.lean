/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Int.Basic

public section

open scoped Matrix

namespace Int

/-- Theorem 1.7 (1). For integers `a`, `b`, `c` with `a` and `b` not both zero, the linear
Diophantine equation `a * x + b * y = c` has an integer solution exactly when
`(Int.gcd a b : ℤ)` divides `c`. -/
theorem existsMulAddMulEq_iff_gcdDvd
    (a b c : ℤ)
    (hnot : a ≠ 0 ∨ b ≠ 0) :
    (∃ x y : ℤ, a * x + b * y = c) ↔ ((Int.gcd a b : ℤ) ∣ c) := by
  -- Solvability only uses the common-divisor property; the nonzero assumption belongs to the
  -- textbook formulation but is not otherwise needed for this equivalence.
  rcases hnot with ha | hb
  all_goals
    constructor
    · rintro ⟨x, y, hxy⟩
      rw [← hxy]
      exact Int.dvd_add
        (dvd_mul_of_dvd_left (Int.gcd_dvd_left a b))
        (dvd_mul_of_dvd_left (Int.gcd_dvd_right a b))
    · rintro ⟨k, rfl⟩
      -- Multiplying the canonical Bézout coefficients by `k` gives the requested solution.
      refine ⟨Int.gcdA a b * k, Int.gcdB a b * k, ?_⟩
      calc
        a * (Int.gcdA a b * k) + b * (Int.gcdB a b * k) =
            (a * Int.gcdA a b + b * Int.gcdB a b) * k := by ring
        _ = (Int.gcd a b : ℤ) * k := by rw [Int.gcd_eq_gcd_ab]

/-- Helper for Theorem 1.7: a nontrivial pair of integers has nonzero integer-cast gcd. -/
lemma gcdIntCast_ne_zero_of_not_both_zero
    (a b : ℤ) (hnot : a ≠ 0 ∨ b ≠ 0) : (Int.gcd a b : ℤ) ≠ 0 := by
  -- A zero cast forces the natural gcd, and hence both inputs, to vanish.
  intro hg
  have hgNat : Int.gcd a b = 0 := by
    exact_mod_cast hg
  obtain ⟨ha, hb⟩ := Int.gcd_eq_zero_iff.mp hgNat
  exact hnot.elim (fun hne ↦ hne ha) (fun hne ↦ hne hb)

/-- Helper for Theorem 1.7: the Bézout completion sends the input row to its gcd row. -/
lemma bezoutCompletionVecMul (a b : ℤ) :
    let g : ℤ := Int.gcd a b
    (![a, b] : Fin 2 → ℤ) ᵥ*
        !![Int.gcdA a b, -(b / g); Int.gcdB a b, a / g] = ![g, 0] := by
  -- The divisibility identities normalize the second coordinate to a cancelling cross term.
  dsimp only
  have ha : (Int.gcd a b : ℤ) * (a / (Int.gcd a b : ℤ)) = a := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel (Int.gcd_dvd_left a b)
  have hb : (Int.gcd a b : ℤ) * (b / (Int.gcd a b : ℤ)) = b := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel (Int.gcd_dvd_right a b)
  have hfirst : a * Int.gcdA a b + b * Int.gcdB a b = (Int.gcd a b : ℤ) :=
    (Int.gcd_eq_gcd_ab a b).symm
  have hsecond :
      a * -(b / (Int.gcd a b : ℤ)) + b * (a / (Int.gcd a b : ℤ)) = 0 := by
    calc
      a * -(b / (Int.gcd a b : ℤ)) + b * (a / (Int.gcd a b : ℤ)) =
          -((Int.gcd a b : ℤ) * (a / (Int.gcd a b : ℤ))) *
              (b / (Int.gcd a b : ℤ)) +
            ((Int.gcd a b : ℤ) * (b / (Int.gcd a b : ℤ))) *
              (a / (Int.gcd a b : ℤ)) := by
                rw [ha, hb]
                ring
      _ = 0 := by ring
  -- Extensionality reduces the row equality to the two scalar identities above.
  ext i
  fin_cases i
  · simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using hfirst
  · simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using hsecond

/-- Helper for Theorem 1.7: the Bézout completion matrix has determinant one. -/
lemma bezoutCompletionDet
    (a b : ℤ) (hnot : a ≠ 0 ∨ b ≠ 0) :
    let g : ℤ := Int.gcd a b
    Matrix.det !![Int.gcdA a b, -(b / g); Int.gcdB a b, a / g] = 1 := by
  -- Dividing both inputs by their nonzero gcd turns Bézout's identity into determinant one.
  dsimp only
  have hg : (Int.gcd a b : ℤ) ≠ 0 :=
    gcdIntCast_ne_zero_of_not_both_zero a b hnot
  have ha : (Int.gcd a b : ℤ) * (a / (Int.gcd a b : ℤ)) = a := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel (Int.gcd_dvd_left a b)
  have hb : (Int.gcd a b : ℤ) * (b / (Int.gcd a b : ℤ)) = b := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel (Int.gcd_dvd_right a b)
  have hnormalized :
      Int.gcdA a b * (a / (Int.gcd a b : ℤ)) +
          (b / (Int.gcd a b : ℤ)) * Int.gcdB a b = 1 := by
    apply mul_left_cancel₀ hg
    calc
      (Int.gcd a b : ℤ) *
          (Int.gcdA a b * (a / (Int.gcd a b : ℤ)) +
            (b / (Int.gcd a b : ℤ)) * Int.gcdB a b) =
          ((Int.gcd a b : ℤ) * (a / (Int.gcd a b : ℤ))) * Int.gcdA a b +
            ((Int.gcd a b : ℤ) * (b / (Int.gcd a b : ℤ))) * Int.gcdB a b := by ring
      _ = a * Int.gcdA a b + b * Int.gcdB a b := by rw [ha, hb]
      _ = (Int.gcd a b : ℤ) := (Int.gcd_eq_gcd_ab a b).symm
      _ = (Int.gcd a b : ℤ) * 1 := by ring
  calc
    Matrix.det !![Int.gcdA a b, -(b / (Int.gcd a b : ℤ));
        Int.gcdB a b, a / (Int.gcd a b : ℤ)] =
        Int.gcdA a b * (a / (Int.gcd a b : ℤ)) +
          (b / (Int.gcd a b : ℤ)) * Int.gcdB a b := by
            rw [Matrix.det_fin_two_of]
            ring
    _ = 1 := hnormalized

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_theorem_1_7.lean.
Theorem 1.7 (2). For integers `a` and `b` with `a` and `b` not both zero, there exists
`T : GL (Fin 2) ℤ` such that right multiplication sends the row `![a, b]` to
`![(Int.gcd a b : ℤ), 0]`. -/
theorem existsGLTwoVecMul_eq_gcd_zero
    (a b : ℤ)
    (hnot : a ≠ 0 ∨ b ≠ 0) :
    ∃ T : GL (Fin 2) ℤ,
      (![a, b] : Fin 2 → ℤ) ᵥ* (T : Matrix (Fin 2) (Fin 2) ℤ) = ![(Int.gcd a b : ℤ), 0] := by
  -- The determinant interface packages the explicit completion as an invertible matrix.
  let M : Matrix (Fin 2) (Fin 2) ℤ :=
    !![Int.gcdA a b, -(b / (Int.gcd a b : ℤ));
       Int.gcdB a b, a / (Int.gcd a b : ℤ)]
  have hdet : Matrix.det M = 1 := by
    exact bezoutCompletionDet a b hnot
  have hunit : IsUnit (Matrix.det M) := by
    rw [hdet]
    exact isUnit_one
  refine ⟨Matrix.GeneralLinearGroup.mk'' M hunit, ?_⟩
  -- Its underlying matrix is `M`, whose row action was computed independently.
  exact bezoutCompletionVecMul a b

end Int

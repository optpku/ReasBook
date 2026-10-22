/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_1_1
public import Mathlib.Analysis.Fourier.ZMod

public section

open scoped BigOperators

namespace Matrix

/-- Exercise 5.4. For `ω = Matrix.fourierRoot n = Complex.exp (-Complex.I * 2 * Real.pi / n)`,
the finite geometric sum `∑ j : Fin n, ω ^ ((j : ℕ) * (k : ℕ))` is `n` at the zero frequency
and `0` at every nonzero frequency. See `Matrix.fourierRoot_eq_exp` for the source formula for
`ω`. -/
theorem fourierRoot_orthogonality (n : ℕ) [NeZero n] (k : Fin n) :
    ∑ j : Fin n, Matrix.fourierRoot n ^ ((j : ℕ) * (k : ℕ)) =
      if k = 0 then (n : ℂ) else 0 := by
  classical
  cases n with
  | zero => cases NeZero.ne 0 rfl
  | succ n =>
      convert
        (AddChar.sum_mulShift (-(k : ZMod (n + 1)))
          (ZMod.isPrimitive_stdAddChar (n + 1))) using 1
      · refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Matrix.fourierRoot_eq_stdAddChar, ← AddChar.map_nsmul_eq_pow]
        congr 1
        rw [nsmul_eq_mul]
        change (((j : ZMod (n + 1)) * (k : ZMod (n + 1))) * (-1)) =
          (j : ZMod (n + 1)) * (-(k : ZMod (n + 1)))
        rw [← mul_neg_one (k : ZMod (n + 1)), ← mul_assoc]
      · by_cases hk : k = 0
        · subst hk
          rw [if_pos rfl]
          simp
        · have hkz : (-(k : ZMod (n + 1))) ≠ 0 := by
            intro hk0
            have : (k : ZMod (n + 1)) = 0 := by
              simpa using (neg_eq_zero.mp hk0)
            exact hk (by exact_mod_cast this)
          rw [if_neg hk]
          simp [hkz]

/-- The zero-frequency case of `Matrix.fourierRoot_orthogonality`. -/
theorem fourierRoot_orthogonality_zero (n : ℕ) [NeZero n] :
    ∑ j : Fin n, Matrix.fourierRoot n ^ ((j : ℕ) * 0) = (n : ℂ) := by
  have h := fourierRoot_orthogonality n (0 : Fin n)
  rwa [if_pos rfl] at h

/-- The nonzero-frequency case of `Matrix.fourierRoot_orthogonality`. -/
theorem fourierRoot_orthogonality_ne_zero (n : ℕ) [NeZero n] (k : Fin n) (hk : k ≠ 0) :
    ∑ j : Fin n, Matrix.fourierRoot n ^ ((j : ℕ) * (k : ℕ)) = 0 := by
  simpa [hk] using fourierRoot_orthogonality n k

end Matrix

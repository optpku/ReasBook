module

public import Mathlib.Analysis.Matrix.Order

public section

noncomputable section

universe u

open scoped MatrixOrder

namespace Matrix

/-- A strict scalar Loewner lower bound makes a real finite matrix positive definite. -/
theorem posDef_of_loewner_lowerBound
    {n : Type u} [Finite n] [DecidableEq n]
    {A : Matrix n n ℝ} {m : ℝ} (hm : 0 < m)
    (h : m • (1 : Matrix n n ℝ) ≤ A) : A.PosDef := by
  -- Local instance justification (finite matrix sums): the public theorem only needs `Finite n`,
  -- while the quadratic-form API requires a concrete enumeration of the finite index type.
  letI := Fintype.ofFinite n
  have hdiff : (A - m • (1 : Matrix n n ℝ)).PosSemidef :=
    (le_iff.mp h)
  have hscalar : (m • (1 : Matrix n n ℝ)).PosSemidef :=
    PosSemidef.smul PosSemidef.one hm.le
  have hsemidef : A.PosSemidef := by
    have hadd := hscalar.add hdiff
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hadd
  apply PosDef.of_dotProduct_mulVec_pos hsemidef.isHermitian
  intro x hx
  have hdiffq := hdiff.dotProduct_mulVec_nonneg x
  have hstrict : 0 < star x ⬝ᵥ ((m • (1 : Matrix n n ℝ)) *ᵥ x) := by
    have hxx : 0 < star x ⬝ᵥ x := dotProduct_star_self_pos_iff.mpr hx
    simpa [smul_mulVec, one_mulVec, dotProduct_smul] using mul_pos hm hxx
  have hdecomp :
      m • (1 : Matrix n n ℝ) + (A - m • (1 : Matrix n n ℝ)) = A := by
    abel
  rw [← hdecomp, add_mulVec, dotProduct_add]
  exact add_pos_of_pos_of_nonneg hstrict hdiffq

/-- A Hermitian real matrix with a strictly positive quadratic-form lower bound is positive
definite. -/
theorem posDef_of_quadraticForm_lowerBound
    {n : Type u} [Fintype n]
    {A : Matrix n n ℝ} {m : ℝ} (hA : A.IsHermitian) (hm : 0 < m)
    (hquad : ∀ x : n → ℝ,
      m * (star x ⬝ᵥ x) ≤ star x ⬝ᵥ (A *ᵥ x)) : A.PosDef := by
  apply PosDef.of_dotProduct_mulVec_pos hA
  intro x hx
  exact (mul_pos hm (dotProduct_star_self_pos_iff.mpr hx)).trans_le (hquad x)

end Matrix

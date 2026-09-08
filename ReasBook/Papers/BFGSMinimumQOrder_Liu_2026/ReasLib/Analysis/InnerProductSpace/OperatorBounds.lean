module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

public section

universe u

namespace ContinuousLinearMap

/-- A continuous linear endomorphism bounded in operator norm by `η` has quadratic form
between `-η * ‖v‖ ^ 2` and `η * ‖v‖ ^ 2`. -/
theorem inner_apply_bounds_of_norm_le {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (B : E →L[ℝ] E) (η : ℝ)
    (h_norm : ‖B‖ ≤ η) (v : E) :
    -η * ‖v‖ ^ 2 ≤ inner ℝ (B v) v ∧ inner ℝ (B v) v ≤ η * ‖v‖ ^ 2 := by
  -- First transfer the operator-norm hypothesis to the chosen vector.
  have applyNormBound : ‖B v‖ ≤ η * ‖v‖ := B.le_of_opNorm_le h_norm v
  -- Normalize the repeated norm product to the square used in the conclusion.
  have normProductNormalization : (η * ‖v‖) * ‖v‖ = η * ‖v‖ ^ 2 := by
    rw [pow_two, mul_assoc]
  -- Cauchy--Schwarz and the pointwise bound control the absolute quadratic form.
  have quadraticFormAbsBound : |inner ℝ (B v) v| ≤ η * ‖v‖ ^ 2 := by
    calc
      |inner ℝ (B v) v| ≤ ‖B v‖ * ‖v‖ := abs_real_inner_le_norm (B v) v
      _ ≤ (η * ‖v‖) * ‖v‖ := mul_le_mul_of_nonneg_right applyNormBound (norm_nonneg v)
      _ = η * ‖v‖ ^ 2 := normProductNormalization
  -- The absolute-value estimate supplies both requested signed inequalities.
  constructor
  · simpa only [neg_mul] using neg_le_of_abs_le quadraticFormAbsBound
  · exact le_of_abs_le quadraticFormAbsBound

end ContinuousLinearMap

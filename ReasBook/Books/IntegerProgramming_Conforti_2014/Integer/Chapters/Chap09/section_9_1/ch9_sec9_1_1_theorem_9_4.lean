import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: the policy-requested semantic Lean search tool `lean_leansearch` was
-- unavailable in this environment (`tool_search` returned no such tool). Local Chapter 9
-- precedent uses `Basis` together with `gramSchmidtBasis`, so this file follows that API.

open InnerProductSpace Module

universe u

noncomputable section Theorem94

variable {n : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Gram-Schmidt coefficient `mu_{j,k}` of `B j` along the `k`th Gram-Schmidt vector of `B`. -/
def gram_schmidt_coefficient (B : Basis (Fin n) ℝ E) (j k : Fin n) : ℝ :=
  ⟪B j, gramSchmidtBasis B k⟫_ℝ / ‖gramSchmidtBasis B k‖ ^ 2

/-- Condition `(9.4)(i)`: every coefficient below the diagonal in the Gram-Schmidt expansion of
`B` has absolute value at most `1 / 2`. -/
def basis_reduction_condition_i (B : Basis (Fin n) ℝ E) : Prop :=
  ∀ ⦃j k : Fin n⦄, k < j → |gram_schmidt_coefficient B j k| ≤ (1 : ℝ) / 2

/-- Condition `(9.4)(ii)`: every adjacent pair of Gram-Schmidt vectors satisfies the Step 2
comparison that prevents another swap. -/
def basis_reduction_condition_ii (B : Basis (Fin n) ℝ E) : Prop :=
  ∀ j : Fin (n - 1),
    let jCurrent : Fin n := ⟨j.1, Nat.lt_of_lt_pred j.2⟩
    let jNext : Fin n := ⟨j.1 + 1, Nat.succ_lt_of_lt_pred j.2⟩
    ‖gramSchmidtBasis B jCurrent‖ ≤
      ‖gramSchmidtBasis B jNext +
        (gram_schmidt_coefficient B jNext jCurrent) • gramSchmidtBasis B jCurrent‖

/-- A basis is reduced when it satisfies Conditions `(9.4)(i)` and `(9.4)(ii)`. -/
def IsReducedBasis (B : Basis (Fin n) ℝ E) : Prop :=
  basis_reduction_condition_i B ∧ basis_reduction_condition_ii B

namespace IsReducedBasis

/-- A reduced basis satisfies the size-reduction inequalities from Theorem 9.4(i). -/
theorem condition_i
    {B : Basis (Fin n) ℝ E}
    (hB : IsReducedBasis B) :
    basis_reduction_condition_i B :=
  hB.1

/-- A reduced basis satisfies the Step 2 stopping criterion from Theorem 9.4(ii). -/
theorem condition_ii
    {B : Basis (Fin n) ℝ E}
    (hB : IsReducedBasis B) :
    basis_reduction_condition_ii B :=
  hB.2

end IsReducedBasis

/-- A basis is reduced exactly when it satisfies Conditions `(9.4)(i)` and `(9.4)(ii)`. -/
theorem isReducedBasis_iff
    {B : Basis (Fin n) ℝ E} :
    IsReducedBasis B ↔ basis_reduction_condition_i B ∧ basis_reduction_condition_ii B :=
  Iff.rfl

/-- Theorem 9.4. When the basis reduction algorithm terminates, the basis `b^1, ..., b^n` is
reduced. In the formalization, this is the source-facing basis returned at termination, together
with the Step 1 size-reduction condition and the Step 2 stopping inequality established for that
output basis. -/
theorem basis_reduction_algorithm_terminates_with_reduced_basis
    {B : Basis (Fin n) ℝ E}
    (hB_i : basis_reduction_condition_i B)
    (hB_ii : basis_reduction_condition_ii B) :
    IsReducedBasis B :=
  ⟨hB_i, hB_ii⟩

end Theorem94

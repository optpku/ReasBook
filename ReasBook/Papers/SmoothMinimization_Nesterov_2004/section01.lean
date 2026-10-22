/-
Authors: Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Papers/SmoothMinimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib

open scoped BigOperators

/-- Definition 1.1.1 (Classical complexity benchmark for subgradient schemes).
A classical worst-case iteration-complexity estimate for subgradient-type schemes for non-smooth
convex minimization in the black-box oracle model is of order O(1/eps^2) (equation (1.1)), where
eps > 0 is the desired absolute accuracy in objective value. -/
def ClassicalSubgradientComplexityBenchmark (iter : ℝ → ℝ) : Prop :=
  ∃ C > 0, ∀ eps > 0, iter eps ≤ C / (eps ^ 2)

/-- Definition 1.1.2 (Constructive lower-bound illustration in the black-box model).
In the black-box oracle model for non-smooth convex minimization, a cited hard instance is the
problem of minimizing `x ↦ max_{1 ≤ i ≤ n} x i` subject to `∑ i, (x i)^2 ≤ 1`
(equation (1.1) and (eq:intro:hard_instance)). -/
noncomputable def HardInstanceProblem (n : ℕ) :
    Set (Fin n → ℝ) × ((Fin n → ℝ) → ℝ) :=
  ({x | ∑ i, (x i)^2 ≤ (1 : ℝ)}, fun x => sSup (Set.range x))

/-- Definition 1.1.3 (Complexity benchmark for smooth convex minimization).
For minimizing a convex function with L-Lipschitz continuous gradient by an optimal first-order
method, the cited iteration complexity estimate is O(√(L/eps)) (equation
(eq:intro:smooth_complexity)) for reaching absolute accuracy eps > 0 in objective value. -/
def SmoothConvexComplexityBenchmark (L : ℝ) (iter : ℝ → ℝ) : Prop :=
  ∃ C > 0, ∀ eps > 0, iter eps ≤ C * Real.sqrt (L / eps)

/-- Definition 1.1.4 (Spaces, duals, and pairing).
Let `E` be a finite-dimensional real normed vector space and let `E*` be the dual space of linear
functionals on `E` (mathlib `Module.Dual`). For `s ∈ E*` and `x ∈ E`, the pairing `⟪s, x⟫` is the
value `s x`. When an inner product is used, the same bracket notation is employed, with an index
when needed. -/
def DualPairing {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (s : Module.Dual ℝ E) (x : E) : ℝ :=
  s x

/-- Definition 1.1.5 (Dual norm).
Given a norm `‖·‖` on `E`, the dual norm `‖·‖_*` on `E*` is defined by
`‖s‖_* = max { ⟪s, x⟫ : x ∈ E, ‖x‖ = 1 }` (equation (eq:dual_norm_def)). -/
noncomputable def DualNormDef {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (s : Module.Dual ℝ E) : ℝ :=
  sSup { r : ℝ | ∃ x : E, ‖x‖ = 1 ∧ r = DualPairing s x }

/-- Definition 1.1.6 (Adjoint operator).
Let `A : E1 → E2*` be a linear operator. The adjoint `A* : E2 → E1*` is defined by
`⟪A x, u⟫_2 = ⟪A* u, x⟫_1` for all `x ∈ E1` and `u ∈ E2` (equation (eq:adjoint_def)). -/
def AdjointOperator {E1 E2 : Type*} [SeminormedAddCommGroup E1] [NormedSpace ℝ E1]
    [FiniteDimensional ℝ E1] [SeminormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2] (A : E1 →ₗ[ℝ] Module.Dual ℝ E2) :
    E2 →ₗ[ℝ] Module.Dual ℝ E1 :=
  LinearMap.flip A

/-- Definition 1.1.7 (Operator norm ‖A‖_{1,2}).
For a linear operator `A : E1 → E2*`, define
`‖A‖_{1,2} = max { ⟪A x, u⟫_2 : ‖x‖_1 = 1, ‖u‖_2 = 1 }`
(equation (eq:operator_norm_def)). -/
noncomputable def OperatorNormDef {E1 E2 : Type*} [SeminormedAddCommGroup E1]
    [NormedSpace ℝ E1] [FiniteDimensional ℝ E1] [SeminormedAddCommGroup E2]
    [NormedSpace ℝ E2] [FiniteDimensional ℝ E2]
    (A : E1 →ₗ[ℝ] Module.Dual ℝ E2) : ℝ :=
  sSup { r : ℝ |
    ∃ x : E1, ∃ u : E2, ‖x‖ = 1 ∧ ‖u‖ = 1 ∧ r = DualPairing (A x) u }

/-- Adjoint pairing matches evaluation of the original map. -/
lemma dualPairing_adjointOperator {E1 E2 : Type*} [SeminormedAddCommGroup E1] [NormedSpace ℝ E1]
    [FiniteDimensional ℝ E1] [SeminormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2] (A : E1 →ₗ[ℝ] Module.Dual ℝ E2) (u : E2) (x : E1) :
    DualPairing (AdjointOperator A u) x = DualPairing (A x) u := by
  rfl

/-- Normalizing a nonzero vector by its norm gives unit norm. -/
lemma norm_inv_smul_eq_one_of_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E} (hu : u ≠ 0) : ‖(‖u‖)⁻¹ • u‖ = 1 := by
  simpa using (norm_smul_inv_norm (x := u) hu)

/-- The operator-norm defining set is bounded above. -/
lemma bddAbove_operatorNormDefSet {E1 E2 : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1]
    [FiniteDimensional ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2] (A : E1 →ₗ[ℝ] Module.Dual ℝ E2) :
    BddAbove { r : ℝ | ∃ x : E1, ∃ v : E2, ‖x‖ = 1 ∧ ‖v‖ = 1 ∧ r = DualPairing (A x) v } := by
  classical
  let Acont : E1 →ₗ[ℝ] (E2 →L[ℝ] ℝ) :=
    (LinearMap.toContinuousLinearMap).toLinearMap.comp A
  have hcont : Continuous Acont := Acont.continuous_of_finiteDimensional
  rcases SemilinearMapClass.bound_of_continuous Acont hcont with ⟨C, _, hC⟩
  refine ⟨C, ?_⟩
  rintro r ⟨x, v, hx, hv, rfl⟩
  have hle_abs : DualPairing (A x) v ≤ |DualPairing (A x) v| := le_abs_self _
  have hle_op : |DualPairing (A x) v| ≤ ‖Acont x‖ * ‖v‖ := by
    simpa [DualPairing, Acont, Real.norm_eq_abs] using (Acont x).le_opNorm v
  have hleC : |DualPairing (A x) v| ≤ C * ‖x‖ * ‖v‖ := by
    calc
      |DualPairing (A x) v| ≤ ‖Acont x‖ * ‖v‖ := hle_op
      _ ≤ (C * ‖x‖) * ‖v‖ := by
        exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg v)
      _ = C * ‖x‖ * ‖v‖ := by
        ring
  have hleC' : |DualPairing (A x) v| ≤ C := by
    simpa [hx, hv, mul_assoc] using hleC
  exact hle_abs.trans hleC'

/-- Unit-sphere pairing is bounded by the operator norm definition. -/
lemma dualPairing_le_operatorNormDef {E1 E2 : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1]
    [FiniteDimensional ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2] (A : E1 →ₗ[ℝ] Module.Dual ℝ E2)
    {x : E1} {v : E2} (hx : ‖x‖ = 1) (hv : ‖v‖ = 1) :
    DualPairing (A x) v ≤ OperatorNormDef A := by
  classical
  set S : Set ℝ :=
      { r : ℝ | ∃ x : E1, ∃ v : E2, ‖x‖ = 1 ∧ ‖v‖ = 1 ∧ r = DualPairing (A x) v }
  have hSbdd : BddAbove S := bddAbove_operatorNormDefSet (A := A)
  have hmem : DualPairing (A x) v ∈ S := ⟨x, v, hx, hv, rfl⟩
  simpa [OperatorNormDef, S] using (le_csSup hSbdd hmem)

/-- Pointwise adjoint bound on the unit sphere. -/
lemma adjointOperator_dualNorm_le_pointwise {E1 E2 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [FiniteDimensional ℝ E1] [NormedAddCommGroup E2]
    [NormedSpace ℝ E2] [FiniteDimensional ℝ E2] (A : E1 →ₗ[ℝ] Module.Dual ℝ E2) (u : E2)
    {x : E1} (hx : ‖x‖ = 1) :
    DualPairing (AdjointOperator A u) x ≤ OperatorNormDef A * ‖u‖ := by
  classical
  have hpair : DualPairing (AdjointOperator A u) x = DualPairing (A x) u := by
    simp [dualPairing_adjointOperator]
  by_cases hu : u = 0
  · simp [hu, AdjointOperator, DualPairing]
  · let v : E2 := (‖u‖)⁻¹ • u
    have hv : ‖v‖ = 1 := by
      simpa [v] using (norm_inv_smul_eq_one_of_ne_zero (u := u) hu)
    have hle_v : DualPairing (A x) v ≤ OperatorNormDef A :=
      dualPairing_le_operatorNormDef (A := A) (x := x) (v := v) hx hv
    have hmul :
        ‖u‖ * DualPairing (A x) v ≤ ‖u‖ * OperatorNormDef A := by
      exact mul_le_mul_of_nonneg_left hle_v (norm_nonneg _)
    have hnorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    have hscale : ‖u‖ • v = u := by
      simp [v, smul_smul, hnorm]
    have hlin : DualPairing (A x) u = ‖u‖ * DualPairing (A x) v := by
      calc
        DualPairing (A x) u = DualPairing (A x) (‖u‖ • v) := by simp [hscale]
        _ = ‖u‖ * DualPairing (A x) v := by
          simp [DualPairing, map_smul, smul_eq_mul]
    have hmul' : ‖u‖ * DualPairing (A x) v ≤ OperatorNormDef A * ‖u‖ := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    have hle : DualPairing (A x) u ≤ OperatorNormDef A * ‖u‖ := by
      calc
        DualPairing (A x) u = ‖u‖ * DualPairing (A x) v := hlin
        _ ≤ OperatorNormDef A * ‖u‖ := hmul'
    simpa [hpair] using hle

/-- Proposition 1.1.1.
For any `u ∈ E2`, the adjoint operator satisfies the bound
`‖A* u‖_{1,*} ≤ ‖A‖_{1,2} ‖u‖_2` (equation (eq:1.2)). -/
theorem adjointOperator_dualNorm_le {E1 E2 : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1]
    [FiniteDimensional ℝ E1] [NormedAddCommGroup E2] [NormedSpace ℝ E2]
    [FiniteDimensional ℝ E2]
    (A : E1 →ₗ[ℝ] Module.Dual ℝ E2) (u : E2) :
    DualNormDef (AdjointOperator A u) ≤ OperatorNormDef A * ‖u‖ := by
  classical
  set S : Set ℝ :=
      { r : ℝ | ∃ x : E1, ‖x‖ = 1 ∧ r = DualPairing (AdjointOperator A u) x }
  have hDual : DualNormDef (AdjointOperator A u) = sSup S := by
    simp [DualNormDef, S]
  by_cases hS : ∃ x : E1, ‖x‖ = 1
  · have hSne : S.Nonempty := by
      rcases hS with ⟨x, hx⟩
      exact ⟨DualPairing (AdjointOperator A u) x, ⟨x, hx, rfl⟩⟩
    have hle : ∀ r ∈ S, r ≤ OperatorNormDef A * ‖u‖ := by
      intro r hr
      rcases hr with ⟨x, hx, rfl⟩
      exact adjointOperator_dualNorm_le_pointwise (A := A) (u := u) (x := x) hx
    have : sSup S ≤ OperatorNormDef A * ‖u‖ := csSup_le hSne hle
    simpa [hDual] using this
  · have hSempty : S = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro r hr
      rcases hr with ⟨x, hx, rfl⟩
      exact (hS ⟨x, hx⟩).elim
    set Sop : Set ℝ :=
        { r : ℝ | ∃ x : E1, ∃ v : E2, ‖x‖ = 1 ∧ ‖v‖ = 1 ∧ r = DualPairing (A x) v }
    have hOp_empty : Sop = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro r hr
      rcases hr with ⟨x, v, hx, hv, rfl⟩
      exact (hS ⟨x, hx⟩).elim
    have hDual0 : DualNormDef (AdjointOperator A u) = 0 := by
      simp [hDual, hSempty, Real.sSup_empty]
    have hOp : OperatorNormDef A = sSup Sop := by
      simp [OperatorNormDef, Sop]
    have hOp0 : OperatorNormDef A = 0 := by
      simp [hOp, hOp_empty, Real.sSup_empty]
    simp [hDual0, hOp0]

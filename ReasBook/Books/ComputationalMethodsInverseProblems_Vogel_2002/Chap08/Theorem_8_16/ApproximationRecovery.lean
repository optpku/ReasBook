/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_16.ApproximationBridge
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Prop_8_13
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_15

public section

noncomputable section

namespace VariationalRegularization

variable {d : ℕ}

open scoped ContDiff

namespace BVCompactness

/-- Helper for Theorem 8.16: the remaining analytic owner is a reciprocal-budget smooth recovery
family for each `u : BV Ω`. -/
theorem existsSmoothCompactSupportRecoverySeq_of_bv
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (u : BV Ω) :
    ∃ φ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ,
      ∀ n : ℕ,
        ContDiff ℝ ∞ (φ n) ∧
        HasCompactSupport (φ n) ∧
        tsupport (φ n) ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) ∧
        MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - φ n x) 1 (domainMeasure Ω) ≤
          ENNReal.ofReal (1 / (n + 1 : ℝ)) ∧
        ∫ x, ‖fderiv ℝ (φ n) x‖ ∂domainMeasure Ω ≤
          (totalVariation u.toL1).toReal + 1 / (n + 1 : ℝ) := by
  classical
  -- Route correction: the public recovery sequence is obtained by choosing the already-proved
  -- one-shot strict-BV approximant at the reciprocal budget `1 / (n + 1)`.
  have happrox :
      ∀ n : ℕ,
        ∃ φ : EuclideanSpace ℝ (Fin d) → ℝ,
          ContDiff ℝ ∞ φ ∧
          HasCompactSupport φ ∧
          tsupport φ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) ∧
          MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - φ x) 1 (domainMeasure Ω) ≤
            ENNReal.ofReal (1 / (n + 1 : ℝ)) ∧
          ∫ x, ‖fderiv ℝ φ x‖ ∂domainMeasure Ω ≤
            (totalVariation u.toL1).toReal + 1 / (n + 1 : ℝ) := by
    intro n
    -- The bridge owner already gives the required witness at any positive budget.
    simpa using
      (existsSmoothCompactSupportApprox_of_bv
        (d := d) (Ω := Ω) (u := u) (ε := 1 / (n + 1 : ℝ)) (by positivity))
  choose φ hφ using happrox
  -- Package the pointwise chosen witnesses into the requested sequence.
  exact ⟨φ, hφ⟩

/-- Helper for Theorem 8.16: a strict `BV` recovery theorem should provide one smooth compactly
supported approximant with independently chosen `L¹` and derivative budgets. -/
theorem existsSmoothCompactSupportApprox_of_bv_twoBudgets
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (u : BV Ω)
    {δ η : ℝ}
    (hδ : 0 < δ)
    (hη : 0 < η) :
    ∃ φ : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ ∞ φ ∧
      HasCompactSupport φ ∧
      tsupport φ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) ∧
      MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - φ x) 1 (domainMeasure Ω) ≤
        ENNReal.ofReal δ ∧
      ∫ x, ‖fderiv ℝ φ x‖ ∂domainMeasure Ω ≤
        (totalVariation u.toL1).toReal + η := by
  obtain ⟨φ, hφ⟩ := existsSmoothCompactSupportRecoverySeq_of_bv (d := d) (Ω := Ω) u
  have hmin_pos : 0 < min δ η := lt_min hδ hη
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hmin_pos
  have hδ_budget : 1 / (n + 1 : ℝ) < δ := (lt_min_iff.mp hn).1
  have hη_budget : 1 / (n + 1 : ℝ) < η := (lt_min_iff.mp hn).2
  rcases hφ n with ⟨hφ_smooth, hφ_compact, hφ_subset, hφ_err, hφ_deriv⟩
  refine ⟨φ n, hφ_smooth, hφ_compact, hφ_subset, ?_, ?_⟩
  · -- The reciprocal-budget witness already has smaller `L¹` error than the requested budget.
    exact hφ_err.trans <| ENNReal.ofReal_le_ofReal (le_of_lt hδ_budget)
  · -- The derivative budget is handled by the same chosen index.
    have hη_le : 1 / (n + 1 : ℝ) ≤ η := le_of_lt hη_budget
    linarith

end BVCompactness

end VariationalRegularization

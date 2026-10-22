/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Example_19_28

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace ERealFunction

section

variable (φ : ℝ → Set.Ioi (⊥ : EReal))

-- Proof sketch: Example 19.28 (9) characterizes existence of a saddle point by the equality
-- `phiRangeInfimum φ = (φ 0 : EReal)`. A strict inequality between these two values therefore
-- excludes saddle points.
/-- Remark 19.29: in the setting of Example 19.28, if `γ < φ(0)` then the Lagrangian of the
Lorentz-constraint perturbation has no saddle point. -/
lemma not_exists_saddlePoint_lorentzConstraintPerturbation_of_phiRangeInfimum_lt
    (hφ : φ ∈ Γ₀(ℝ)) (hφ0 : 0 ∈ effectiveDomain φ)
    (hγ : phiRangeInfimum φ < (φ 0 : EReal)) :
    ¬ ∃ ξ : ℝ × ℝ, ∃ v : ℝ,
      IsSaddlePointOn (Set.univ : Set (ℝ × ℝ)) (Set.univ : Set ℝ)
        (ℒ[lorentzConstraintPerturbation φ]) ξ v := by
  rintro ⟨ξ, v, hsaddle⟩
  have hEq :=
    (exists_saddlePoint_lorentzConstraintPerturbation_iff φ hφ hφ0).1 ⟨ξ, v, hsaddle⟩
  exact hγ.ne hEq.symm

-- Proof sketch: Example 19.28 (4) identifies the primal solution set with
-- `Set.Ici (0 : ℝ) ×ˢ ({0} : Set ℝ)`, which is nonempty.
/-- The Lorentz-constraint perturbation of Example 19.28 has a primal minimizer. -/
lemma argmin_perturbationPrimalObjective_lorentzConstraintPerturbation_nonempty :
    (Argmin
      (perturbationPrimalObjective (lorentzConstraintPerturbation φ))).Nonempty := by
  rw [argmin_perturbationPrimalObjective_lorentzConstraintPerturbation φ]
  exact ⟨(0, 0), by simp⟩

-- Proof sketch: Example 19.28 (7) identifies the dual solution set with `Set.Ici (0 : ℝ)`,
-- which is nonempty.
/-- The Lorentz-constraint perturbation of Example 19.28 has a dual minimizer. -/
lemma argmin_perturbationDualObjective_lorentzConstraintPerturbation_nonempty :
    (Argmin
      (perturbationDualObjective (lorentzConstraintPerturbation φ))).Nonempty := by
  rw [argmin_perturbationDualObjective_lorentzConstraintPerturbation φ]
  exact ⟨0, by simp⟩

-- Proof sketch: Example 19.28 (3) and (6) identify the primal and dual optimal values with
-- `(φ 0 : EReal)` and `-phiRangeInfimum φ`, so equality of the optimal values up to sign would
-- force `(φ 0 : EReal)` to equal that infimum, contradicting the strict inequality.
/-- A strict inequality `γ < φ(0)` forces the optimal primal value to differ from the negative of
the optimal dual value, so the Lorentz-constraint perturbation has a nonzero duality gap. -/
lemma nonzero_duality_gap_lorentzConstraintPerturbation_of_phiRangeInfimum_lt
    (hγ : phiRangeInfimum φ < (φ 0 : EReal)) :
    sInf
        (Set.range (perturbationPrimalObjective (lorentzConstraintPerturbation φ))) ≠
      -sInf
        (Set.range (perturbationDualObjective (lorentzConstraintPerturbation φ))) := by
  intro hgap
  rw [sInf_perturbationPrimalObjective_lorentzConstraintPerturbation φ,
    sInf_perturbationDualObjective_lorentzConstraintPerturbation φ, neg_neg] at hgap
  exact hγ.ne hgap.symm

end

end ERealFunction

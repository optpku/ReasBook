/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_25.DiscrepancyChoice
public import Mathlib.Analysis.Asymptotics.Theta

public section
noncomputable section
open scoped Asymptotics
namespace TsvdDiscrepancy
universe u v
variable {H : Type u} {F : Type v}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Theorem 7.25. Under the explicit power-law residual model, an admissible
integer discrepancy family is asymptotically equivalent to `(7.89)`.

The model is an additional substantive hypothesis: noise moment conditions
alone do not control one fixed sample. The scalar theorem
`isEquivalent_of_powerResidualModel` also applies directly to expected residuals.
The proof bounds the index within one of the benchmark using integral tail
bounds; it assumes neither the desired asymptotic rate nor an inconsistent
infinite Hilbert-space white-noise vector. -/
theorem isEquivalent_indexBenchmark
    (K : ℕ → H →L[ℝ] F) (d : ℕ → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (b c p q σ : ℝ) (m : ℕ → ℕ)
    (hb : 0 < b) (hc : 0 < c) (hp : 1 < p) (hq : 1 < q) (hσ : 0 < σ)
    (hmodel : HasPowerResidualModel
      (fun n m ↦ ‖K n (Rtsvd n m (d n)) - d n‖ ^ 2) b c p q σ)
    (hchoice : IsDiscrepancyChoiceFamily K d Rtsvd σ m) :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n ↦ (m n : ℝ)) (indexBenchmark b c p q σ) := by
  exact isEquivalent_of_powerResidualModel hb hc (by linarith) hσ hmodel hchoice

/-- The `=Θ` consequence of the TSVD discrepancy asymptotic equivalence. -/
theorem isTheta_indexBenchmark
    (K : ℕ → H →L[ℝ] F) (d : ℕ → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (b c p q σ : ℝ) (m : ℕ → ℕ)
    (hb : 0 < b) (hc : 0 < c) (hp : 1 < p) (hq : 1 < q) (hσ : 0 < σ)
    (hmodel : HasPowerResidualModel
      (fun n m ↦ ‖K n (Rtsvd n m (d n)) - d n‖ ^ 2) b c p q σ)
    (hchoice : IsDiscrepancyChoiceFamily K d Rtsvd σ m) :
    (fun n ↦ (m n : ℝ)) =Θ[Filter.atTop] indexBenchmark b c p q σ :=
  (isEquivalent_indexBenchmark K d Rtsvd b c p q σ m
    hb hc hp hq hσ hmodel hchoice).isTheta
end TsvdDiscrepancy

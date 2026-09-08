module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.CenterOrbitRecurrenceCertificate
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.ResidualBranchAdapter

public section

open scoped BigOperators

universe u v w

namespace LocalCutoff.GraphTransform

/-- Helper for Infrastructure I.16a: source-facing data combining a contracted
center-orbit error with the finite non-distinguished composition branches. -/
structure CenterOrbitResidualCertificate
    (ι : Type u) (Θ : Type v) (E : Type w)
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set Θ) where
  orbit : CenterOrbitRecurrenceCertificate Θ E K
  distinguished : ι
  branches : ι → Θ → E
  branchBound : ℝ
  residualBound : ℝ
  orbitBudget_le : orbit.budget ≤ residualBound / 2
  branch_norm_le : ∀ i, i ≠ distinguished → ∀ u ∈ K,
    ‖branches i u‖ ≤ branchBound
  branchBudget_le : ((Fintype.card ι : ℝ) - 1) * branchBound ≤ residualBound / 2

/-- Helper for Infrastructure I.16a: a center-orbit recurrence bound supplies
the principal half of a finite composition residual estimate. -/
theorem residual_norm_le_of_centerOrbit_and_nonDistinguished
    {ι : Type u} {Θ : Type v} {E : Type w}
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set Θ}
    (orbit : CenterOrbitRecurrenceCertificate Θ E K)
    (hK : K.Nonempty)
    (distinguished : ι) (branches : ι → Θ → E)
    (branchBound residualBound : ℝ)
    (horbitBudget : orbit.budget ≤ residualBound / 2)
    (hbranch : ∀ i, i ≠ distinguished → ∀ u ∈ K,
      ‖branches i u‖ ≤ branchBound)
    (hbranchBudget : ((Fintype.card ι : ℝ) - 1) * branchBound ≤ residualBound / 2) :
    ∀ u ∈ K,
      ‖orbit.defect u - orbit.filtered u +
          ∑ i, if i = distinguished then 0 else branches i u‖ ≤ residualBound := by
  intro u hu
  have horbit : ‖orbit.defect u - orbit.filtered u‖ ≤ residualBound / 2 :=
    (orbit.error_norm_le hK u hu).trans horbitBudget
  exact residual_norm_le_of_principal_and_nonDistinguished distinguished
    (orbit.defect u - orbit.filtered u) (fun i ↦ branches i u)
    branchBound residualBound horbit
    (fun i hi ↦ hbranch i hi u hu) hbranchBudget

/-- Infrastructure I.16a: a combined center-orbit and finite-branch certificate
bounds the full residual by its declared error budget. -/
theorem CenterOrbitResidualCertificate.norm_residual_le
    {ι : Type u} {Θ : Type v} {E : Type w}
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set Θ}
    (certificate : CenterOrbitResidualCertificate ι Θ E K)
    (hK : K.Nonempty) :
    ∀ u ∈ K,
      ‖certificate.orbit.defect u - certificate.orbit.filtered u +
          ∑ i, if i = certificate.distinguished then 0 else
            certificate.branches i u‖ ≤ certificate.residualBound := by
  exact residual_norm_le_of_centerOrbit_and_nonDistinguished
    certificate.orbit hK certificate.distinguished certificate.branches
    certificate.branchBound certificate.residualBound certificate.orbitBudget_le
    certificate.branch_norm_le certificate.branchBudget_le

/-- Helper for Infrastructure I.16a: a finite transported-increment recurrence
is combined with the non-distinguished composition branches without requiring a
global bound along an infinite center orbit. -/
structure FiniteCenterOrbitResidualCertificate
    (ι : Type u) (Θ : Type v) (E : Type w)
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E]
    (K : Set Θ) where
  orbit : FiniteCenterOrbitRecurrenceCertificate Θ E K
  distinguished : ι
  branches : ι → Θ → E
  branchBound : ℝ
  residualBound : ℝ
  orbitBudget_le : orbit.budget ≤ residualBound / 2
  branch_norm_le : ∀ i, i ≠ distinguished → ∀ u ∈ K,
    ‖branches i u‖ ≤ branchBound
  branchBudget_le :
    ((Fintype.card ι : ℝ) - 1) * branchBound ≤ residualBound / 2

/-- Infrastructure I.16a: a finite center-orbit recurrence and the finite
non-distinguished branch budget bound the full residual at its initial state. -/
theorem FiniteCenterOrbitResidualCertificate.norm_residual_le
    {ι : Type u} {Θ : Type v} {E : Type w}
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E]
    {K : Set Θ}
    (certificate : FiniteCenterOrbitResidualCertificate ι Θ E K) :
    ∀ u ∈ K,
      ‖certificate.orbit.error u +
          ∑ i, if i = certificate.distinguished then 0 else
            certificate.branches i u‖ ≤ certificate.residualBound := by
  intro u hu
  have horbit : ‖certificate.orbit.error u‖ ≤ certificate.residualBound / 2 :=
    (certificate.orbit.error_norm_le hu).trans certificate.orbitBudget_le
  exact residual_norm_le_of_principal_and_nonDistinguished
    certificate.distinguished (certificate.orbit.error u)
    (fun i ↦ certificate.branches i u) certificate.branchBound
    certificate.residualBound horbit
    (fun i hi ↦ certificate.branch_norm_le i hi u hu)
    certificate.branchBudget_le

/-
The finite recurrence stores its principal term as `error`, whereas the graph
transform residual is normally written as a live term minus a filtered term.
This adapter keeps that notational transport separate from the budget argument.
-/

/-- Helper for Infrastructure I.16a: an explicit identification of a finite-orbit
error with a live-minus-filtered term transports the residual bound to the graph
transform normal form. -/
theorem finiteCenterOrbitResidual_norm_le_of_difference
    {ι : Type u} {Θ : Type v} {E : Type w}
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E]
    {K : Set Θ}
    (certificate : FiniteCenterOrbitResidualCertificate ι Θ E K)
    (defect filtered : Θ → E)
    (herror : ∀ u ∈ K, certificate.orbit.error u = defect u - filtered u) :
    ∀ u ∈ K,
      ‖defect u - filtered u +
          ∑ i, if i = certificate.distinguished then 0 else
            certificate.branches i u‖ ≤ certificate.residualBound := by
  intro u hu
  rw [← herror u hu]
  exact certificate.norm_residual_le u hu

end LocalCutoff.GraphTransform

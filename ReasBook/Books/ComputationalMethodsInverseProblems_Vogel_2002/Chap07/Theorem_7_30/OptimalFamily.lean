/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Notation_7_7.OptimalFamily
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_30.ExpectedObjective
public import Mathlib.Order.Filter.Extr

public section

namespace TsvdGcv

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {H : Type v} {F : Type w}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A TSVD truncation-index family `mV` is eventually GCV-optimal when, for all
sufficiently large `n`, the selected index `mV n` lies in the denominator-valid
admissible set and minimizes the concrete TSVD expected GCV objective there. -/
def IsOptimalFamilyEventually
    (μ : MeasureTheory.Measure Ω)
    (K : ℕ → H →L[ℝ] F)
    (R : ℕ → ℕ → F →L[ℝ] H)
    (fTrue : H) (η : ℕ → Ω → F)
    (mV : ℕ → ℕ) : Prop :=
  ∀ᶠ n in Filter.atTop,
    mV n ∈ gcvAdmissibleIndexSet n ∧
      IsMinOn (expectedObjective μ K R fTrue η n) (gcvAdmissibleIndexSet n) (mV n)

/-- The defining eventual-membership and minimality characterization of
`IsOptimalFamilyEventually`. -/
@[simp] theorem isOptimalFamilyEventually_iff
    (μ : MeasureTheory.Measure Ω)
    (K : ℕ → H →L[ℝ] F)
    (R : ℕ → ℕ → F →L[ℝ] H)
    (fTrue : H) (η : ℕ → Ω → F)
    (mV : ℕ → ℕ) :
    IsOptimalFamilyEventually μ K R fTrue η mV ↔
      ∀ᶠ n in Filter.atTop,
        mV n ∈ gcvAdmissibleIndexSet n ∧
          IsMinOn (expectedObjective μ K R fTrue η n) (gcvAdmissibleIndexSet n) (mV n) :=
  Iff.rfl

/-- An eventually GCV-optimal family is eventually denominator-valid. -/
theorem IsOptimalFamilyEventually.eventually_mem
    {μ : MeasureTheory.Measure Ω}
    {K : ℕ → H →L[ℝ] F}
    {R : ℕ → ℕ → F →L[ℝ] H}
    {fTrue : H} {η : ℕ → Ω → F}
    {mV : ℕ → ℕ}
    (h : IsOptimalFamilyEventually μ K R fTrue η mV) :
    ∀ᶠ n in Filter.atTop, mV n ∈ gcvAdmissibleIndexSet n :=
  h.mono fun _ hn ↦ hn.1

/-- An eventually GCV-optimal family eventually minimizes the concrete TSVD
expected GCV objective on the denominator-valid admissible set. -/
theorem IsOptimalFamilyEventually.eventually_isMinOn
    {μ : MeasureTheory.Measure Ω}
    {K : ℕ → H →L[ℝ] F}
    {R : ℕ → ℕ → F →L[ℝ] H}
    {fTrue : H} {η : ℕ → Ω → F}
    {mV : ℕ → ℕ}
    (h : IsOptimalFamilyEventually μ K R fTrue η mV) :
    ∀ᶠ n in Filter.atTop,
      IsMinOn (expectedObjective μ K R fTrue η n) (gcvAdmissibleIndexSet n) (mV n) :=
  h.mono fun _ hn ↦ hn.2

/-- A pointwise GCV-optimal family on `gcvAdmissibleIndexSet` is eventually
GCV-optimal once the source admissibility is supplied explicitly. -/
theorem IsOptimalFamilyEventually.of_forall
    {μ : MeasureTheory.Measure Ω}
    {K : ℕ → H →L[ℝ] F}
    {R : ℕ → ℕ → F →L[ℝ] H}
    {fTrue : H} {η : ℕ → Ω → F}
    {mV : ℕ → ℕ}
    (h_mem : ∀ n, mV n ∈ gcvAdmissibleIndexSet n)
    (h_opt :
      ParameterChoice.IsOptimalParameterFamily
        (expectedObjective μ K R fTrue η)
        gcvAdmissibleIndexSet
        mV) :
    IsOptimalFamilyEventually μ K R fTrue η mV := by
  have h_opt' :
      ∀ n,
        IsMinOn
          (expectedObjective μ K R fTrue η n)
          (gcvAdmissibleIndexSet n)
          (mV n) :=
    (ParameterChoice.isOptimalParameterFamily_iff
      (expectedObjective μ K R fTrue η)
      gcvAdmissibleIndexSet
      mV).1 h_opt
  exact Filter.Eventually.of_forall fun n ↦ ⟨h_mem n, h_opt' n⟩

end

end TsvdGcv

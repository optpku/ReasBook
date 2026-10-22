/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_6.EstimationError
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_12.Nullspace
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_12.SingularSystem

public section

noncomputable section

/-!
Remark 7.12 (summary of standing Chapter 7 assumptions).

This source item is a prose recap of five recurring assumptions in the Chapter 7
analysis:

* the semidiscrete semistochastic data model `(7.34)`,
* singular-system data for `K n` together with the algebraic square decay
  `(7.49)`,
* algebraic square decay of the generalized Fourier coefficients of `fTrue`
  from `(7.53)`,
* vanishing nullspace component as `n → ∞`,
* and the linear filtering representation `(7.36)` for the Tikhonov solution.

The reusable nullspace and singular-system APIs are split into the item-local
foundation modules `Book.Ch7.Remark_7_12.Nullspace` and
`Book.Ch7.Remark_7_12.SingularSystem`, with the singular-system extension
built on the Remark 7.9 scaling foundation `Book.Ch7.Remark_7_9.Scaling`.
This file keeps the remaining source-facing Chapter 7 assumptions together
with the bundled standing-assumption owner built on top of that
infrastructure.
-/

namespace FilterRegularization

universe u v

section DataModel

variable {H : Type u} {F : Type v}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The semidiscrete semistochastic data model `(7.34)` is the noisy data
equation `d = K fTrue + η`. -/
abbrev HasSemistochasticDataModel (K : H →L[ℝ] F) (fTrue : H) (d η : F) : Prop :=
  d = K fTrue + η

@[simp] theorem hasSemistochasticDataModel_iff
    (K : H →L[ℝ] F) (fTrue : H) (d η : F) :
    HasSemistochasticDataModel K fTrue d η ↔ d = K fTrue + η :=
  Iff.rfl

end DataModel

end FilterRegularization

namespace FilterRegularization

universe u v

section StandingAssumptionsSection

variable {H : Type u} {F : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Remark 7.12. Bundle of the five recurring Chapter 7 standing assumptions:
the semistochastic data model, algebraic square decay of the singular values,
algebraic square decay of the generalized Fourier coefficients of `fTrue`, the
vanishing nullspace component, and the singular-system Tikhonov
filter-series representation `(7.36)` of the reconstruction operators. -/
structure StandingAssumptions
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤) (fTrue : H)
    (c p b q : ℝ) (d η : ℕ → F)
    (R : ℕ → F →L[ℝ] H) (α : ℕ → ℝ) : Prop where
  /-- Each datum satisfies the semistochastic model `(7.34)`. -/
  semistochasticDataModel (n : ℕ) :
    HasSemistochasticDataModel (K n) fTrue (d n) (η n)
  /-- The singular values satisfy the algebraic square-decay law `(7.49)`. -/
  singularValueSquareDecay (n : ℕ) :
    (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p
  /-- The generalized Fourier coefficients of `fTrue` satisfy `(7.53)`. -/
  fourierCoefficientSquareDecay (n : ℕ) :
    (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q
  /-- The nullspace component of `fTrue` vanishes asymptotically. -/
  vanishingNullspaceComponent :
    HasVanishingNullspaceComponent K fTrue
  /-- The reconstruction operator has the Tikhonov filter representation
  `(7.36)` relative to the singular system `S n`. -/
  filterRepresentation (n : ℕ) :
    (S n).HasTikhonovFilterRepresentation (α n) (R n)

namespace StandingAssumptions

set_option linter.defProp false in
/-- Build `StandingAssumptions` from its five defining assumption families. -/
def ofAssumptions
    {K : ℕ → H →L[ℝ] F}
    {S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n)}
    {h_length : ∀ n, (S n).length = ⊤} {fTrue : H}
    {c p b q : ℝ} {d η : ℕ → F}
    {R : ℕ → F →L[ℝ] H} {α : ℕ → ℝ}
    (h_dataModel : ∀ n, HasSemistochasticDataModel (K n) fTrue (d n) (η n))
    (h_singularValueSquareDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierCoefficientSquareDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_vanishingNullspaceComponent : HasVanishingNullspaceComponent K fTrue)
    (h_filterRepresentation :
      ∀ n, (S n).HasTikhonovFilterRepresentation (α n) (R n)) :
    StandingAssumptions K S h_length fTrue c p b q d η R α :=
  { semistochasticDataModel := h_dataModel
    singularValueSquareDecay := h_singularValueSquareDecay
    fourierCoefficientSquareDecay := h_fourierCoefficientSquareDecay
    vanishingNullspaceComponent := h_vanishingNullspaceComponent
    filterRepresentation := h_filterRepresentation }

/-- Under `StandingAssumptions`, the datum `d n` is reconstructed by the
Tikhonov filter series attached to `S n` and `α n`. -/
theorem hasSum_apply_data
    {K : ℕ → H →L[ℝ] F}
    {S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n)}
    {h_length : ∀ n, (S n).length = ⊤} {fTrue : H}
    {c p b q : ℝ} {d η : ℕ → F}
    {R : ℕ → F →L[ℝ] H} {α : ℕ → ℝ}
    (h : StandingAssumptions K S h_length fTrue c p b q d η R α)
    (n : ℕ) :
    HasSum
      ((S n).filterSeries (SpectralFilter.tikhonov (α n)) (d n))
      (R n (d n)) :=
  (h.filterRepresentation n).hasSum (d n)

end StandingAssumptions

namespace StandingAssumptions

/-- Specification lemma for `StandingAssumptions`. -/
theorem iff
    {K : ℕ → H →L[ℝ] F}
    {S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n)}
    {h_length : ∀ n, (S n).length = ⊤} {fTrue : H}
    {c p b q : ℝ} {d η : ℕ → F}
    {R : ℕ → F →L[ℝ] H} {α : ℕ → ℝ} :
    StandingAssumptions K S h_length fTrue c p b q d η R α ↔
      (∀ n, HasSemistochasticDataModel (K n) fTrue (d n) (η n)) ∧
      (∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p) ∧
      (∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q) ∧
      HasVanishingNullspaceComponent K fTrue ∧
      ∀ n, (S n).HasTikhonovFilterRepresentation (α n) (R n) := by
  constructor
  · intro h
    exact ⟨h.semistochasticDataModel, h.singularValueSquareDecay,
      h.fourierCoefficientSquareDecay, h.vanishingNullspaceComponent,
      h.filterRepresentation⟩
  · rintro ⟨h_dataModel, h_singularValueSquareDecay, h_fourierCoefficientSquareDecay,
      h_vanishingNullspaceComponent, h_filterRepresentation⟩
    exact StandingAssumptions.ofAssumptions
      h_dataModel h_singularValueSquareDecay
      h_fourierCoefficientSquareDecay h_vanishingNullspaceComponent h_filterRepresentation

end StandingAssumptions

end StandingAssumptionsSection

end FilterRegularization

/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_17.Pseudoinverse
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_1

public section

noncomputable section

universe u

section MinimumBoundValue

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The fixed-residual minimum-bound value built from the quadratic pseudoinverse term
and the penalty `γ * σ ^ 2 / α`. -/
def minimumBoundValue (K : Matrix n n ℝ) (r : EuclideanSpace ℝ n) (γ σ α : ℝ) : ℝ :=
  dotProduct r
      (ContinuousLinearMap.pseudoInverse
          (LinearMap.toContinuousLinearMap
            (((Fintype.card n : ℝ) • (K.transpose * K)).toEuclideanLin)) r) /
      (Fintype.card n : ℝ) +
    γ * σ ^ 2 / α

/-- The defining formula for `minimumBoundValue`. -/
@[simp] theorem minimumBoundValue_def
    (K : Matrix n n ℝ) (r : EuclideanSpace ℝ n) (γ σ α : ℝ) :
    minimumBoundValue K r γ σ α =
      dotProduct r
          (ContinuousLinearMap.pseudoInverse
            (LinearMap.toContinuousLinearMap
              (((Fintype.card n : ℝ) • (K.transpose * K)).toEuclideanLin)) r) /
          (Fintype.card n : ℝ) +
        γ * σ ^ 2 / α := by
  simp [minimumBoundValue]

end MinimumBoundValue

section MinimumBound

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Definition 7.5-extra-1. The minimum-bound objective associated to a family of
regularized residuals. -/
def minimumBound (K : Matrix n n ℝ) (rfamily : ℝ → EuclideanSpace ℝ n) (γ σ : ℝ)
    : ℝ → ℝ :=
  fun α ↦ minimumBoundValue K (rfamily α) γ σ α

/-- The defining formula for `minimumBound` in terms of `minimumBoundValue`. -/
@[simp] theorem minimumBound_eq_minimumBoundValue (K : Matrix n n ℝ)
    (rfamily : ℝ → EuclideanSpace ℝ n) (γ σ α : ℝ) :
    minimumBound K rfamily γ σ α = minimumBoundValue K (rfamily α) γ σ α := by
  simp [minimumBound]

/-- Evaluating `minimumBound` gives the explicit quadratic pseudoinverse formula
for the residual at the chosen regularization parameter. -/
theorem minimumBound_eq_dotProduct_pseudoInverse_add_penalty
    (K : Matrix n n ℝ) (rfamily : ℝ → EuclideanSpace ℝ n) (γ σ α : ℝ) :
    minimumBound K rfamily γ σ α =
      dotProduct (rfamily α)
          (ContinuousLinearMap.pseudoInverse
            (LinearMap.toContinuousLinearMap
              (((Fintype.card n : ℝ) • (K.transpose * K)).toEuclideanLin))
            (rfamily α)) /
          (Fintype.card n : ℝ) +
        γ * σ ^ 2 / α := by
  simp [minimumBound, minimumBoundValue]

/-- A parameter is a minimum-bound parameter when it minimizes `minimumBound`
over the admissible positive regularization parameters. -/
def IsMinimumBoundParameter (K : Matrix n n ℝ) (rfamily : ℝ → EuclideanSpace ℝ n)
    (γ σ : ℝ) (α : ℝ) : Prop :=
  α ∈ Set.Ioi (0 : ℝ) ∧ IsMinOn (minimumBound K rfamily γ σ) (Set.Ioi (0 : ℝ)) α

/-- The defining characterization of `IsMinimumBoundParameter`. -/
@[simp] theorem IsMinimumBoundParameter_iff (K : Matrix n n ℝ)
    (rfamily : ℝ → EuclideanSpace ℝ n) (γ σ α : ℝ) :
    IsMinimumBoundParameter K rfamily γ σ α ↔
      α ∈ Set.Ioi (0 : ℝ) ∧
        IsMinOn (minimumBound K rfamily γ σ) (Set.Ioi (0 : ℝ)) α := Iff.rfl

/-- A minimum-bound parameter is an admissible positive regularization parameter. -/
theorem IsMinimumBoundParameter.pos (K : Matrix n n ℝ)
    (rfamily : ℝ → EuclideanSpace ℝ n) (γ σ α : ℝ)
    (hα : IsMinimumBoundParameter K rfamily γ σ α) : 0 < α :=
  hα.1

/-- A minimum-bound parameter minimizes `minimumBound` on the admissible positive
regularization parameters. -/
theorem IsMinimumBoundParameter.isMinOn (K : Matrix n n ℝ)
    (rfamily : ℝ → EuclideanSpace ℝ n) (γ σ α : ℝ)
    (hα : IsMinimumBoundParameter K rfamily γ σ α) :
    IsMinOn (minimumBound K rfamily γ σ) (Set.Ioi (0 : ℝ)) α :=
  hα.2

/-- A minimum-bound parameter minimizes the explicit `minimumBoundValue`
backend over the positive regularization parameters. -/
theorem IsMinimumBoundParameter_iff_isMinOn_minimumBoundValue
    (K : Matrix n n ℝ) (rfamily : ℝ → EuclideanSpace ℝ n) (γ σ α : ℝ) :
    IsMinimumBoundParameter K rfamily γ σ α ↔
      α ∈ Set.Ioi (0 : ℝ) ∧
        IsMinOn (fun a ↦ minimumBoundValue K (rfamily a) γ σ a) (Set.Ioi (0 : ℝ)) α := by
  constructor
  · intro hα
    rcases (IsMinimumBoundParameter_iff K rfamily γ σ α).mp hα with ⟨hpos, hmin⟩
    refine ⟨hpos, ?_⟩
    rw [isMinOn_iff] at hmin ⊢
    intro b hb
    simpa [minimumBound] using hmin b hb
  · intro hα
    rcases hα with ⟨hpos, hmin⟩
    refine (IsMinimumBoundParameter_iff K rfamily γ σ α).2 ?_
    refine ⟨hpos, ?_⟩
    rw [isMinOn_iff] at hmin ⊢
    intro b hb
    simpa [minimumBound] using hmin b hb

end MinimumBound

section MinimumBoundBridges

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Rewriting `minimumBound` through the explicit residual coming from an influence
matrix family. -/
theorem minimumBound_influenceMatrix_eq (K : Matrix n n ℝ) (Rfamily : ℝ → Matrix n n ℝ)
    (γ σ : ℝ) (d : EuclideanSpace ℝ n) (α : ℝ) :
    minimumBound K (fun a ↦ regularizedResidual (influenceMatrix K (Rfamily a)) d) γ σ α =
      minimumBoundValue K (K.toEuclideanLin (regularizedSolution (Rfamily α) d) - d) γ σ α := by
  rw [minimumBound_eq_minimumBoundValue, regularizedResidual_influenceMatrix]

end MinimumBoundBridges

end

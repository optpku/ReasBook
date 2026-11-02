import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.subgradient
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_1.ch8_sec8_1_proposition_8_1

open scoped BigOperators Matrix

section Proposition810

variable {m₁ n : ℕ}
variable (A₁ : Matrix (Fin m₁) (Fin n) ℝ) (b₁ : Fin m₁ → ℝ) (c : Fin n → ℝ)
variable (Q : Set (Fin n → ℝ))

/-- The penalized objective of the Lagrangian relaxation `LR(λ)` evaluated at `x`. -/
def lagrangian_relaxation_objective
    (lam : Fin m₁ → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  c ⬝ᵥ x + lam ⬝ᵥ (b₁ - A₁ *ᵥ x)

/-- `IsOptimalLagrangianRelaxationSolution A₁ b₁ c Q λ x_star` means that `x_star ∈ Q` and
maximizes the Lagrangian-relaxation objective of `LR(λ)` over `Q`. -/
def IsOptimalLagrangianRelaxationSolution
    (lam : Fin m₁ → ℝ)
    (x_star : Fin n → ℝ) : Prop :=
  x_star ∈ Q ∧
    ∀ x ∈ Q,
      lagrangian_relaxation_objective A₁ b₁ c lam x ≤
        lagrangian_relaxation_objective A₁ b₁ c lam x_star

theorem isOptimalLagrangianRelaxationSolution_iff
    (lam : Fin m₁ → ℝ)
    (x_star : Fin n → ℝ) :
    IsOptimalLagrangianRelaxationSolution A₁ b₁ c Q lam x_star ↔
      x_star ∈ Q ∧
        ∀ x ∈ Q,
          lagrangian_relaxation_objective A₁ b₁ c lam x ≤
            lagrangian_relaxation_objective A₁ b₁ c lam x_star :=
  Iff.rfl

theorem IsOptimalLagrangianRelaxationSolution.mem
    {lam : Fin m₁ → ℝ}
    {x_star : Fin n → ℝ}
    (hx_star_opt : IsOptimalLagrangianRelaxationSolution A₁ b₁ c Q lam x_star) :
    x_star ∈ Q :=
  hx_star_opt.1

theorem IsOptimalLagrangianRelaxationSolution.objective_le
    {lam : Fin m₁ → ℝ}
    {x_star x : Fin n → ℝ}
    (hx_star_opt : IsOptimalLagrangianRelaxationSolution A₁ b₁ c Q lam x_star)
    (hx : x ∈ Q) :
    lagrangian_relaxation_objective A₁ b₁ c lam x ≤
      lagrangian_relaxation_objective A₁ b₁ c lam x_star :=
  hx_star_opt.2 x hx

/-- Helper for Proposition 8.10: the penalized objective is affine in the multiplier vector, and
the linear term is the slack vector `b₁ - A₁ *ᵥ x`. -/
lemma lagrangianRelaxationObjective_eq_baseObjective_add_slackGap
    (lam lam_star : Fin m₁ → ℝ)
    (x : Fin n → ℝ) :
    lagrangian_relaxation_objective A₁ b₁ c lam x =
      lagrangian_relaxation_objective A₁ b₁ c lam_star x +
        ∑ i, (b₁ - A₁ *ᵥ x) i * (lam i - lam_star i) := by
  have hlam : lam = lam_star + (lam - lam_star) := by
    ext i
    simp
  have hsplit :
      lam ⬝ᵥ (b₁ - A₁ *ᵥ x) =
        lam_star ⬝ᵥ (b₁ - A₁ *ᵥ x) +
          ∑ i, (b₁ - A₁ *ᵥ x) i * (lam i - lam_star i) := by
    -- Commute the dot product once so `dotProduct_add` applies directly to the multiplier split.
    calc
      lam ⬝ᵥ (b₁ - A₁ *ᵥ x)
          = (b₁ - A₁ *ᵥ x) ⬝ᵥ lam := by
              rw [dotProduct_comm]
      _ = (b₁ - A₁ *ᵥ x) ⬝ᵥ (lam_star + (lam - lam_star)) := by
            exact congrArg (fun t : Fin m₁ → ℝ ↦ (b₁ - A₁ *ᵥ x) ⬝ᵥ t) hlam
      _ = (b₁ - A₁ *ᵥ x) ⬝ᵥ lam_star + (b₁ - A₁ *ᵥ x) ⬝ᵥ (lam - lam_star) := by
            rw [dotProduct_add]
      _ = lam_star ⬝ᵥ (b₁ - A₁ *ᵥ x) + (b₁ - A₁ *ᵥ x) ⬝ᵥ (lam - lam_star) := by
            rw [dotProduct_comm (b₁ - A₁ *ᵥ x) lam_star]
      _ = lam_star ⬝ᵥ (b₁ - A₁ *ᵥ x) +
            ∑ i, (b₁ - A₁ *ᵥ x) i * (lam i - lam_star i) := by
            rfl
  -- Expand `λ` around `λ_star` and isolate the slack-dependent increment.
  calc
    lagrangian_relaxation_objective A₁ b₁ c lam x
        = c ⬝ᵥ x +
            (lam_star ⬝ᵥ (b₁ - A₁ *ᵥ x) +
              ∑ i, (b₁ - A₁ *ᵥ x) i * (lam i - lam_star i)) := by
            rw [lagrangian_relaxation_objective, hsplit]
    _ = lagrangian_relaxation_objective A₁ b₁ c lam_star x +
          ∑ i, (b₁ - A₁ *ᵥ x) i * (lam i - lam_star i) := by
          simp [lagrangian_relaxation_objective, add_assoc]

/-- Proposition 8.10. If `x_star` is an optimal solution of `LR(λ_star)` as defined in (8.2),
then the slack vector `b¹ - A₁ x_star` is a subgradient of the Lagrangian-relaxation value
function `z_LR` at `λ_star` on the nonnegative orthant. -/
theorem lagrangian_relaxation_slack_is_subgradient_of_optimal_solution
    (lam_star : Fin m₁ → ℝ)
    (x_star : Fin n → ℝ)
    (hx_star_opt :
      IsOptimalLagrangianRelaxationSolution A₁ b₁ c Q lam_star x_star) :
    IsSubgradientAtOn
      (lagrangian_relaxation_value A₁ b₁ c Q)
      (Set.Ici (0 : Fin m₁ → ℝ))
      lam_star
      (b₁ - A₁ *ᵥ x_star) := by
  intro lam hlam
  have hxQ : x_star ∈ Q := hx_star_opt.mem
  have hvalueUpper :
      lagrangian_relaxation_value A₁ b₁ c Q lam_star ≤
        ((lagrangian_relaxation_objective A₁ b₁ c lam_star x_star : ℝ) : EReal) := by
    -- Bound every point of the defining supremum by optimality of `x_star` at `lam_star`.
    rw [lagrangian_relaxation_value_eq_sSup]
    refine sSup_le ?_
    rintro _ ⟨x, hxQ', rfl⟩
    have hobjective :
        lagrangian_relaxation_objective A₁ b₁ c lam_star x ≤
          lagrangian_relaxation_objective A₁ b₁ c lam_star x_star :=
      hx_star_opt.2 x hxQ'
    have hobjectiveEReal :
        (((lagrangian_relaxation_objective A₁ b₁ c lam_star x : ℝ) : EReal) ≤
          ((lagrangian_relaxation_objective A₁ b₁ c lam_star x_star : ℝ) : EReal)) :=
      EReal.coe_le_coe hobjective
    simpa [lagrangian_relaxation_objective] using hobjectiveEReal
  have hvalueEq :
      lagrangian_relaxation_value A₁ b₁ c Q lam_star =
        ((lagrangian_relaxation_objective A₁ b₁ c lam_star x_star : ℝ) : EReal) := by
    -- The optimizer both attains the supremum and is itself one candidate in the supremum set.
    apply le_antisymm
    · exact hvalueUpper
    · simpa [lagrangian_relaxation_objective] using
        lagrangian_objective_le_lagrangian_relaxation_value A₁ b₁ c Q lam_star hxQ
  have hobjectiveLower :
      ((lagrangian_relaxation_objective A₁ b₁ c lam x_star : ℝ) : EReal) ≤
        lagrangian_relaxation_value A₁ b₁ c Q lam := by
    -- Evaluate the relaxation at the fixed optimizer `x_star` to obtain the comparison lower bound.
    simpa [lagrangian_relaxation_objective] using
      lagrangian_objective_le_lagrangian_relaxation_value A₁ b₁ c Q lam hxQ
  have hobjectiveAffine :
      ((lagrangian_relaxation_objective A₁ b₁ c lam x_star : ℝ) : EReal) =
        lagrangian_relaxation_value A₁ b₁ c Q lam_star +
          ((∑ i, (b₁ - A₁ *ᵥ x_star) i * (lam i - lam_star i) : ℝ) : EReal) := by
    -- Rewrite the objective at `lam` as the base objective at `lam_star` plus the slack-gap term.
    calc
      ((lagrangian_relaxation_objective A₁ b₁ c lam x_star : ℝ) : EReal)
          = ((lagrangian_relaxation_objective A₁ b₁ c lam_star x_star +
                ∑ i, (b₁ - A₁ *ᵥ x_star) i * (lam i - lam_star i) : ℝ) : EReal) := by
              exact congrArg (fun t : ℝ ↦ (t : EReal))
                (lagrangianRelaxationObjective_eq_baseObjective_add_slackGap
                  A₁ b₁ c lam lam_star x_star)
      _ = ((lagrangian_relaxation_objective A₁ b₁ c lam_star x_star : ℝ) : EReal) +
            ((∑ i, (b₁ - A₁ *ᵥ x_star) i * (lam i - lam_star i) : ℝ) : EReal) := by
            rw [EReal.coe_add]
      _ = lagrangian_relaxation_value A₁ b₁ c Q lam_star +
            ((∑ i, (b₁ - A₁ *ᵥ x_star) i * (lam i - lam_star i) : ℝ) : EReal) := by
            rw [← hvalueEq]
  -- The subgradient inequality is now the comparison lower bound followed by the affine rewrite.
  calc
    lagrangian_relaxation_value A₁ b₁ c Q lam
        ≥ ((lagrangian_relaxation_objective A₁ b₁ c lam x_star : ℝ) : EReal) :=
      hobjectiveLower
    _ = lagrangian_relaxation_value A₁ b₁ c Q lam_star +
          ((∑ i, (b₁ - A₁ *ᵥ x_star) i * (lam i - lam_star i) : ℝ) : EReal) :=
      hobjectiveAffine

end Proposition810

/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_1.ch8_sec8_1_theorem_8_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

-- The Section 8.1 integer-program and Lagrangian-dual owners already exist upstream.
-- This file keeps only the source-facing Exercise 8.7 surrogate-dual layer and its
-- bridges to those canonical owners.

section Exercise87

variable {m₁ n : ℕ}

/-- The surrogate-feasible set `{x ∈ Q | λ A₁ x ≤ λ b¹}` attached to the multiplier vector `λ`. -/
def surrogate_feasible_set
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (Q : Set (Fin n → ℝ))
    (lam : Fin m₁ → ℝ) : Set (Fin n → ℝ) :=
  {x | x ∈ Q ∧ lam ⬝ᵥ (A₁ *ᵥ x) ≤ lam ⬝ᵥ b₁}

/-- Membership in `surrogate_feasible_set A₁ b₁ Q λ` means exactly that `x ∈ Q` and the
scalarized inequality `λ A₁ x ≤ λ b¹` holds. -/
theorem mem_surrogate_feasible_set_iff
    {A₁ : Matrix (Fin m₁) (Fin n) ℝ}
    {b₁ : Fin m₁ → ℝ}
    {Q : Set (Fin n → ℝ)}
    {lam : Fin m₁ → ℝ}
    {x : Fin n → ℝ} :
    x ∈ surrogate_feasible_set A₁ b₁ Q lam ↔
      x ∈ Q ∧ lam ⬝ᵥ (A₁ *ᵥ x) ≤ lam ⬝ᵥ b₁ :=
  Iff.rfl

/-- Every feasible point of Proposition 8.1's integer program is feasible for the surrogate
relaxation with any nonnegative multiplier vector `λ`. -/
theorem lagrangian_integer_feasible_set_subset_surrogate_feasible_set
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (Q : Set (Fin n → ℝ))
    (lam : Fin m₁ → ℝ)
    (hlam : 0 ≤ lam) :
    lagrangian_integer_feasible_set A₁ b₁ Q ⊆ surrogate_feasible_set A₁ b₁ Q lam := by
  intro x hx
  rw [mem_lagrangian_integer_feasible_set_iff] at hx
  refine ⟨hx.1, ?_⟩
  have hslack : 0 ≤ b₁ - A₁ *ᵥ x := fun i ↦ sub_nonneg.mpr (hx.2 i)
  have hdot : 0 ≤ lam ⬝ᵥ (b₁ - A₁ *ᵥ x) := dotProduct_nonneg_of_nonneg hlam hslack
  rw [dotProduct_sub] at hdot
  exact le_of_sub_nonneg hdot

/-- The surrogate-relaxation value `z_SD(λ) = max {c x | λ A₁ x ≤ λ b¹, x ∈ Q}`, recorded in
`EReal` to match the canonical Section 8.1 value layer. -/
noncomputable def surrogate_relaxation_value
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ))
    (lam : Fin m₁ → ℝ) : EReal :=
  sSup ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) '' surrogate_feasible_set A₁ b₁ Q lam)

/-- `surrogate_relaxation_value A₁ b₁ c Q λ` unfolds to the supremum of `c x` over
`surrogate_feasible_set A₁ b₁ Q λ`. -/
theorem surrogate_relaxation_value_eq_sSup
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ))
    (lam : Fin m₁ → ℝ) :
    surrogate_relaxation_value A₁ b₁ c Q lam =
      sSup
        ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
          surrogate_feasible_set A₁ b₁ Q lam) :=
  rfl

/-- A surrogate-feasible point has nonnegative Lagrangian penalty `λ (b¹ - A₁ x)`. Equivalently,
its original objective value is bounded above by the penalized Lagrangian objective. -/
theorem objective_le_lagrangian_objective_of_mem_surrogate_feasible
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ))
    (lam : Fin m₁ → ℝ)
    {x : Fin n → ℝ}
    (hx : x ∈ surrogate_feasible_set A₁ b₁ Q lam) :
    c ⬝ᵥ x ≤ c ⬝ᵥ x + lam ⬝ᵥ (b₁ - A₁ *ᵥ x) := by
  have hpenalty : 0 ≤ lam ⬝ᵥ (b₁ - A₁ *ᵥ x) := by
    rw [dotProduct_sub]
    exact sub_nonneg.mpr hx.2
  exact le_add_of_nonneg_right hpenalty

/-- For each multiplier vector `λ`, the surrogate-relaxation bound is dominated by the
canonical Section 8.1 Lagrangian-relaxation bound over `convexHull ℝ Q`. -/
theorem surrogate_relaxation_value_le_lagrangian_relaxation_value
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ))
    (lam : Fin m₁ → ℝ) :
    surrogate_relaxation_value A₁ b₁ c Q lam ≤
      lagrangian_relaxation_value A₁ b₁ c (convexHull ℝ Q) lam := by
  -- Rewrite the surrogate owner as a supremum over surrogate-feasible witnesses.
  rw [surrogate_relaxation_value_eq_sSup]
  refine sSup_le ?_
  rintro _ ⟨x, hx, rfl⟩
  have hobjective :
      ((c ⬝ᵥ x : ℝ) : EReal) ≤
        ((c ⬝ᵥ x + lam ⬝ᵥ (b₁ - A₁ *ᵥ x) : ℝ) : EReal) := by
    -- A surrogate-feasible point has nonnegative penalty, so the penalized objective dominates.
    exact_mod_cast
      (objective_le_lagrangian_objective_of_mem_surrogate_feasible A₁ b₁ c Q lam hx)
  -- Insert the same point into the Lagrangian supremum over the convex hull of `Q`.
  exact hobjective.trans <|
    lagrangian_objective_le_lagrangian_relaxation_value A₁ b₁ c (convexHull ℝ Q) lam
      (subset_convexHull ℝ Q hx.1)

/-- The surrogate dual value `z_SD := inf_{λ ≥ 0} z_SD(λ)`. -/
noncomputable def surrogate_dual_value
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ)) : EReal :=
  sInf
    ((fun lam : Fin m₁ → ℝ ↦ surrogate_relaxation_value A₁ b₁ c Q lam) ''
      Set.Ici (0 : Fin m₁ → ℝ))

/-- `surrogate_dual_value A₁ b₁ c Q` unfolds to the infimum of `z_SD(λ)` over the nonnegative
multiplier vectors. -/
theorem surrogate_dual_value_eq_sInf
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ)) :
    surrogate_dual_value A₁ b₁ c Q =
      sInf
        ((fun lam : Fin m₁ → ℝ ↦ surrogate_relaxation_value A₁ b₁ c Q lam) ''
          Set.Ici (0 : Fin m₁ → ℝ)) :=
  rfl

/-- Helper for Exercise 8.7: every nonnegative multiplier vector yields a surrogate-relaxation
upper bound on the integer-program value. -/
theorem integer_program_value_le_surrogate_relaxation_value
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ))
    (lam : Fin m₁ → ℝ)
    (hlam : 0 ≤ lam) :
    integer_program_value A₁ b₁ c Q ≤ surrogate_relaxation_value A₁ b₁ c Q lam := by
  -- Rewrite both owners as suprema of objective values over their feasible sets.
  rw [integer_program_value_eq_sSup, surrogate_relaxation_value_eq_sSup]
  refine sSup_le ?_
  rintro _ ⟨x, hx, rfl⟩
  -- A feasible integer-program point is surrogate-feasible for every `λ ≥ 0`.
  exact le_sSup ⟨x,
    lagrangian_integer_feasible_set_subset_surrogate_feasible_set A₁ b₁ Q lam hlam hx, rfl⟩

/-- Exercise 8.7 (1). For the surrogate dual value
`z_SD := inf_{λ ≥ 0} z_SD(λ)` associated to the relaxations
`z_SD(λ) = max {c x | λ A₁ x ≤ λ b¹, x ∈ Q}`, one has `z_I ≤ z_SD`. -/
theorem integer_program_value_le_surrogate_dual_value
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ)) :
    integer_program_value A₁ b₁ c Q ≤ surrogate_dual_value A₁ b₁ c Q := by
  -- Bound `z_I` by every fixed-`λ` surrogate relaxation and then infimize over `λ ≥ 0`.
  rw [surrogate_dual_value_eq_sInf]
  refine le_sInf ?_
  rintro _ ⟨lam, hlam, rfl⟩
  exact integer_program_value_le_surrogate_relaxation_value A₁ b₁ c Q lam hlam

/-- Exercise 8.7 (2). The surrogate dual bound is no stronger than the canonical Section 8.1
Lagrangian dual bound: `z_SD ≤ z_LD`. -/
theorem surrogate_dual_value_le_lagrangian_dual_value
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ)) :
    surrogate_dual_value A₁ b₁ c Q ≤ lagrangian_dual_value A₁ b₁ c Q := by
  -- Compare the two dual infima pointwise at each nonnegative multiplier vector.
  rw [surrogate_dual_value_eq_sInf, lagrangian_dual_value_eq_sInf]
  refine le_sInf ?_
  rintro _ ⟨lam, hlam, rfl⟩
  -- The surrogate dual infimum is below the chosen surrogate value, which is below the
  -- corresponding Lagrangian relaxation value on `Q`.
  have hsurrogate :
      sInf
          ((fun lam : Fin m₁ → ℝ ↦ surrogate_relaxation_value A₁ b₁ c Q lam) ''
            Set.Ici (0 : Fin m₁ → ℝ)) ≤
        surrogate_relaxation_value A₁ b₁ c Q lam := by
    exact sInf_le ⟨lam, hlam, rfl⟩
  exact hsurrogate.trans <|
    (surrogate_relaxation_value_le_lagrangian_relaxation_value A₁ b₁ c Q lam).trans <|
      by
        rw [← lagrangianRelaxationValue_eq_convexHull A₁ b₁ c Q lam]

end Exercise87

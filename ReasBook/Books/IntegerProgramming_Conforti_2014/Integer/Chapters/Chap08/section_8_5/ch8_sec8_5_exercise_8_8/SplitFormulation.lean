/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Analysis.Convex.Jensen
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_5.ch8_sec8_5_exercise_8_2

open scoped Matrix

noncomputable section

section Exercise88

variable {m₁ m₂ n p : ℕ}

/-- `HasSection81RationalPresentation A b` records the Section 8.1 standing assumption that the
easy-block inequalities defining
`{x ∈ ℤ_+^p × ℝ_+^(n-p) | A *ᵥ x ≤ b}` come from rational coefficient data. -/
def HasSection81RationalPresentation
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : Prop :=
  ∃ Aq : Matrix (Fin m) (Fin n) ℚ, ∃ bq : Fin m → ℚ,
    A = Aq.map (Rat.castHom ℝ) ∧
      b = fun i ↦ (bq i : ℝ)

/-- `HasSection81RationalPresentation A b` expands to explicit rational witnesses for the
defining matrix and right-hand side. -/
theorem hasSection81RationalPresentation_iff
    {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    {b : Fin m → ℝ} :
    HasSection81RationalPresentation A b ↔
      ∃ Aq : Matrix (Fin m) (Fin n) ℚ, ∃ bq : Fin m → ℚ,
        A = Aq.map (Rat.castHom ℝ) ∧
          b = fun i ↦ (bq i : ℝ) :=
  Iff.rfl

/-- The split product base set `Q₁ ×ˢ Q₂` used in Exercise 8.8. -/
abbrev split_mixed_integer_base_set
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  Set.prod
    (mixed_integer_equality_lagrangian_base_set hp A₁ b₁)
    (mixed_integer_equality_lagrangian_base_set hp A₂ b₂)

/-- Membership in `split_mixed_integer_base_set hp A₁ b₁ A₂ b₂` means that the first component
lies in the first mixed-integer base set and the second component lies in the second one. -/
theorem mem_split_mixed_integer_base_set_iff
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    {x y : Fin n → ℝ} :
    (x, y) ∈ split_mixed_integer_base_set hp A₁ b₁ A₂ b₂ ↔
      x ∈ mixed_integer_equality_lagrangian_base_set hp A₁ b₁ ∧
        y ∈ mixed_integer_equality_lagrangian_base_set hp A₂ b₂ :=
  Iff.rfl

/-- The Lagrangian relaxation value obtained from the split formulation of Exercise 8.8 by
dualizing the coupling equations `x - y = 0` with unrestricted multiplier vector `λ`. -/
def split_mixed_integer_lagrangian_relaxation_value
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ)
    (lam : Fin n → ℝ) : EReal :=
  sSup
    ((fun xy : (Fin n → ℝ) × (Fin n → ℝ) ↦
        ((c ⬝ᵥ xy.1 + lam ⬝ᵥ (xy.2 - xy.1) : ℝ) : EReal)) ''
      split_mixed_integer_base_set hp A₁ b₁ A₂ b₂)

/-- `split_mixed_integer_lagrangian_relaxation_value hp A₁ b₁ A₂ b₂ c λ` unfolds to the supremum
of the split Lagrangian objective over `split_mixed_integer_base_set hp A₁ b₁ A₂ b₂`. -/
theorem split_mixed_integer_lagrangian_relaxation_value_eq_sSup
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ)
    (lam : Fin n → ℝ) :
    split_mixed_integer_lagrangian_relaxation_value hp A₁ b₁ A₂ b₂ c lam =
      sSup
        ((fun xy : (Fin n → ℝ) × (Fin n → ℝ) ↦
            ((c ⬝ᵥ xy.1 + lam ⬝ᵥ (xy.2 - xy.1) : ℝ) : EReal)) ''
          split_mixed_integer_base_set hp A₁ b₁ A₂ b₂) :=
  rfl

/-- The Lagrangian dual value `z̄` from Exercise 8.8, obtained by minimizing the split
Lagrangian-relaxation value over all multiplier vectors `λ ∈ ℝ^n`. -/
def split_mixed_integer_lagrangian_dual_value
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ) : EReal :=
  sInf
    (Set.range fun lam : Fin n → ℝ ↦
      split_mixed_integer_lagrangian_relaxation_value hp A₁ b₁ A₂ b₂ c lam)

/-- `split_mixed_integer_lagrangian_dual_value hp A₁ b₁ A₂ b₂ c` unfolds to the infimum of the
split Lagrangian-relaxation values over all multiplier vectors `λ ∈ ℝ^n`. -/
theorem split_mixed_integer_lagrangian_dual_value_eq_sInf
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ) :
    split_mixed_integer_lagrangian_dual_value hp A₁ b₁ A₂ b₂ c =
      sInf
        (Set.range fun lam : Fin n → ℝ ↦
          split_mixed_integer_lagrangian_relaxation_value hp A₁ b₁ A₂ b₂ c lam) :=
  rfl

/-- The feasible region `conv(Q₁) ∩ conv(Q₂)` that appears in the convex-hull description of the
split Lagrangian dual from Exercise 8.8. -/
abbrev split_mixed_integer_convex_hull_intersection
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ) : Set (Fin n → ℝ) :=
  convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₁ b₁) ∩
    convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₂ b₂)

/-- Membership in `split_mixed_integer_convex_hull_intersection hp A₁ b₁ A₂ b₂` means belonging
to both convex hulls `conv(Q₁)` and `conv(Q₂)`. -/
theorem mem_split_mixed_integer_convex_hull_intersection_iff
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    {x : Fin n → ℝ} :
    x ∈ split_mixed_integer_convex_hull_intersection hp A₁ b₁ A₂ b₂ ↔
      x ∈ convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₁ b₁) ∧
      x ∈ convexHull ℝ (mixed_integer_equality_lagrangian_base_set hp A₂ b₂) :=
  Iff.rfl

/-- The canonical Chapter 8 value of maximizing `c x` over `conv(Q₁) ∩ conv(Q₂)`, recorded on the
`EReal` value layer so the statement remains meaningful without separate attainment or boundedness
hypotheses. -/
noncomputable abbrev split_mixed_integer_convex_hull_intersection_value
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ) : EReal :=
  integer_program_value (0 : Matrix (Fin 0) (Fin n) ℝ) (0 : Fin 0 → ℝ) c
    (split_mixed_integer_convex_hull_intersection hp A₁ b₁ A₂ b₂)

/-- `split_mixed_integer_convex_hull_intersection_value hp A₁ b₁ A₂ b₂ c` unfolds to the
supremum of the objective over `conv(Q₁) ∩ conv(Q₂)`. -/
theorem split_mixed_integer_convex_hull_intersection_value_eq_sSup
    (hp : p ≤ n)
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (c : Fin n → ℝ) :
    split_mixed_integer_convex_hull_intersection_value hp A₁ b₁ A₂ b₂ c =
      sSup
        ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
          split_mixed_integer_convex_hull_intersection hp A₁ b₁ A₂ b₂) := by
  simp [split_mixed_integer_convex_hull_intersection_value, integer_program_value,
    lagrangian_integer_feasible_set]

end Exercise88

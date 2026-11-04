/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_5.ch8_sec8_5_exercise_8_18.FeasibilityCone

set_option trace.profiler true

-- This source-facing exercise reuses the Chapter 8 Benders owners
-- `benders_residual`/`benders_subproblem_feasible_set`/`benders_original_feasible_set`/
-- `benders_original_value`, together with the project finite-family extreme-ray owner
-- `IsExtremeRayRepresentativeFamily` built on `IsExtremeRayOfCone`. The source-facing cone name
-- `benders_feasibility_cone` lives in the item-owned foundation module.

open scoped Matrix

section Exercise818

variable {m n p : ℕ}

/-- The feasible `x`-region of the Benders reformulation cut out by the extreme-ray inequalities
`r^j (b - A x) ≥ 0`. -/
def benders_extreme_ray_reformulation_feasible_set
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ))
    {q : ℕ}
    (rays : Fin q → Fin m → ℝ) : Set (Fin n → ℝ) :=
  X ∩ benders_feasibility_cut_set A b rays

/-- Membership in the extreme-ray reformulation feasible set means `x ∈ X` together with every
feasibility cut `r^j (b - A x) ≥ 0`. -/
theorem mem_benders_extreme_ray_reformulation_feasible_set_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ))
    {q : ℕ}
    (rays : Fin q → Fin m → ℝ)
    (x : Fin n → ℝ) :
    x ∈ benders_extreme_ray_reformulation_feasible_set A b X rays ↔
      x ∈ X ∧ ∀ j : Fin q, 0 ≤ rays j ⬝ᵥ benders_residual A b x := by
  simp [benders_extreme_ray_reformulation_feasible_set, mem_benders_feasibility_cut_set_iff]

/-- The value of the Benders reformulation obtained by maximizing `c x` over the extreme-ray
feasibility-cut region, recorded in `EReal` so infeasible instances have value `⊥` and
unbounded-above instances have value `⊤`. -/
noncomputable def benders_extreme_ray_reformulation_value
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    {q : ℕ}
    (rays : Fin q → Fin m → ℝ) : EReal :=
  sSup
    ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
      benders_extreme_ray_reformulation_feasible_set A b X rays)

namespace Benders

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_18.lean: when the slave objective is zero,
`originalValue` is the supremum of the master objective over the projection set. -/
lemma originalValue_zero_eq_projectionSupremum
    {α : Type*}
    (residual : α → Fin m → ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (X : Set α)
    (f : α → ℝ) :
    originalValue residual G X f (0 : Fin p → ℝ) =
      sSup ((fun x : α ↦ ((f x : ℝ) : EReal)) '' (X ∩ projectionSet residual G)) := by
  -- It suffices to identify the two objective-image sets before taking their supremum.
  unfold originalValue
  apply congrArg sSup
  ext value
  constructor
  · rintro ⟨⟨x, y⟩, hxy, rfl⟩
    rcases (mem_originalFeasibleSet_iff residual G X (x, y)).1 hxy with ⟨hxX, hy⟩
    refine ⟨x, ⟨hxX, (mem_projectionSet_iff residual G x).2 ⟨y, hy⟩⟩, ?_⟩
    -- The zero slave objective leaves precisely the master objective value.
    simp only [zero_dotProduct, add_zero]
  · rintro ⟨x, ⟨hxX, hxProjection⟩, rfl⟩
    rcases (mem_projectionSet_iff residual G x).1 hxProjection with ⟨y, hy⟩
    refine ⟨(x, y), (mem_originalFeasibleSet_iff residual G X (x, y)).2 ⟨hxX, hy⟩, ?_⟩
    -- Any projection witness realizes the same value because its coefficient is zero.
    simp only [zero_dotProduct, add_zero]

end Benders

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_18.lean: intersecting the original Benders
projection with `X` gives the extreme-ray reformulation feasible set. -/
lemma bendersOriginalProjection_eq_extremeRayReformulationFeasibleSet
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ))
    {q : ℕ}
    (rays : Fin q → Fin m → ℝ)
    (hrays : IsExtremeRayRepresentativeFamily (benders_feasibility_cone G) rays) :
    X ∩ benders_projection_set A G b =
      benders_extreme_ray_reformulation_feasible_set A b X rays := by
  -- Normalize the source-facing representative-family predicate to the imported local owner.
  have hraysLocal :
      IsExtremeRayRepresentativeFamilyLocal (benders_dual_cone G) rays := by
    simpa only [IsExtremeRayRepresentativeFamily, IsExtremeRayRepresentativeFamilyLocal,
      benders_feasibility_cone] using hrays
  -- Transport the established projection/cut equality through intersection with `X`.
  calc
    X ∩ benders_projection_set A G b = X ∩ benders_feasibility_cut_set A b rays :=
      congrArg (fun S ↦ X ∩ S)
        (bendersProjectionSet_eq_feasibilityCutSet_ofExtremeRays A G b rays hraysLocal)
    _ = benders_extreme_ray_reformulation_feasible_set A b X rays := rfl

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_18.lean. Exercise 8.18.
For the mixed problem `z_I := max c x` subject to `A *ᵥ x + G *ᵥ y ≤ b`, `x ∈ X`, and
`y ∈ ℝ^p_+`, if `rays` is a finite representative family of the extreme rays of the cone
`C := {u ∈ ℝ^m_+ | u ᵥ* G ≥ 0}`, then its Benders reformulation is the problem
`max c x` over `x ∈ X` subject to the feasibility cuts `r^j (b - A x) ≥ 0`. -/
theorem benders_original_value_eq_extreme_ray_reformulation_value
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    {q : ℕ}
    (rays : Fin q → Fin m → ℝ)
    (hrays : IsExtremeRayRepresentativeFamily (benders_feasibility_cone G) rays) :
    benders_original_value A G b X c 0 =
      benders_extreme_ray_reformulation_value A b X c rays := by
  unfold benders_original_value benders_extreme_ray_reformulation_value
  rw [Benders.originalValue_zero_eq_projectionSupremum]
  rw [bendersOriginalProjection_eq_extremeRayReformulationFeasibleSet A G b X rays hrays]

end Exercise818

#print axioms benders_original_value_eq_extreme_ray_reformulation_value

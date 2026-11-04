/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_3.ch8_sec8_3_theorem_8_18

open scoped Matrix

section Exercise816Equality

variable {α : Type*}
variable {m p : ℕ}
variable {K J : Type*}

namespace Benders
namespace Equality

/-- The equality-constrained Benders subproblem feasible set
`{y | G y = rhs, y ≥ 0}` for a fixed right-hand side `rhs`. -/
def subproblemFeasibleSet
    (G : Matrix (Fin m) (Fin p) ℝ)
    (rhs : Fin m → ℝ) : Set (Fin p → ℝ) :=
  {y | G *ᵥ y = rhs ∧ ∀ i, 0 ≤ y i}

/-- Membership in `subproblemFeasibleSet G rhs` is exactly the conjunction `G y = rhs` and
coordinatewise nonnegativity of `y`. -/
theorem mem_subproblemFeasibleSet_iff
    (G : Matrix (Fin m) (Fin p) ℝ)
    (rhs : Fin m → ℝ)
    (y : Fin p → ℝ) :
    y ∈ subproblemFeasibleSet G rhs ↔
      G *ᵥ y = rhs ∧ ∀ i, 0 ≤ y i :=
  Iff.rfl

/-- Equality-constrained subproblem feasibility is equivalent to ordinary Benders subproblem
feasibility together with the reverse inequality `rhs ≤ G y`. -/
theorem mem_subproblemFeasibleSet_iff_mem_benders_subproblem_feasible_set
    (G : Matrix (Fin m) (Fin p) ℝ)
    (rhs : Fin m → ℝ)
    (y : Fin p → ℝ) :
    y ∈ subproblemFeasibleSet G rhs ↔
      y ∈ benders_subproblem_feasible_set G rhs ∧ rhs ≤ G *ᵥ y := by
  rw [mem_subproblemFeasibleSet_iff, mem_benders_subproblem_feasible_set_iff]
  constructor
  · rintro ⟨hEq, hy⟩
    exact ⟨⟨hEq.le, hy⟩, hEq.ge⟩
  · rintro ⟨⟨hLe, hy⟩, hGe⟩
    exact ⟨le_antisymm hLe hGe, hy⟩

/-- The `x`-projection of a mixed system whose fixed-`x` right-hand side is `residual x`,
encoded as existence of an equality-constrained subproblem solution. -/
def projectionSet
    (residual : α → Fin m → ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ) : Set α :=
  {x | ∃ y, y ∈ subproblemFeasibleSet G (residual x)}

/-- Membership in `projectionSet residual G` means that there exists a nonnegative vector `y`
satisfying `G y = residual x`. -/
theorem mem_projectionSet_iff
    (residual : α → Fin m → ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (x : α) :
    x ∈ projectionSet residual G ↔
      ∃ y : Fin p → ℝ, y ∈ subproblemFeasibleSet G (residual x) :=
  Iff.rfl

/-- Every equality-constrained Benders projection point is feasible for the ordinary
inequality-constrained projection. -/
theorem projectionSet_subset
    (residual : α → Fin m → ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ) :
    projectionSet residual G ⊆ Benders.projectionSet residual G := by
  intro x hx
  rcases (mem_projectionSet_iff residual G x).1 hx with ⟨y, hy⟩
  refine (Benders.mem_projectionSet_iff residual G x).2 ?_
  refine ⟨y, ?_⟩
  exact
    (mem_subproblemFeasibleSet_iff_mem_benders_subproblem_feasible_set
      G
      (residual x)
      y).1 hy |>.1

/-- The optimal value of the equality-constrained Benders subproblem with right-hand side
`rhs`, recorded in `EReal` so unbounded-above subproblems have value `⊤ = +∞`. -/
noncomputable def subproblemValue
    (G : Matrix (Fin m) (Fin p) ℝ)
    (h : Fin p → ℝ)
    (rhs : Fin m → ℝ) : EReal :=
  sSup
    ((fun y : Fin p → ℝ ↦ ((h ⬝ᵥ y : ℝ) : EReal)) ''
      subproblemFeasibleSet G rhs)

/-- The feasible set of a mixed problem with master variable restricted to `X` and
equality-constrained subproblem right-hand side `residual x`. -/
def originalFeasibleSet
    (residual : α → Fin m → ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (X : Set α) : Set (α × (Fin p → ℝ)) :=
  {xy | xy.1 ∈ X ∧ xy.2 ∈ subproblemFeasibleSet G (residual xy.1)}

/-- Membership in the residual-based equality-constrained mixed feasible set means `x ∈ X` and
`y` solves the equality-constrained subproblem with right-hand side `residual x`. -/
theorem mem_originalFeasibleSet_iff
    (residual : α → Fin m → ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (X : Set α)
    (xy : α × (Fin p → ℝ)) :
    xy ∈ originalFeasibleSet residual G X ↔
      xy.1 ∈ X ∧ xy.2 ∈ subproblemFeasibleSet G (residual xy.1) :=
  Iff.rfl

/-- Every equality-constrained mixed feasible pair is feasible for the ordinary
inequality-constrained mixed problem. -/
theorem originalFeasibleSet_subset
    (residual : α → Fin m → ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (X : Set α) :
    originalFeasibleSet residual G X ⊆ Benders.originalFeasibleSet residual G X := by
  intro xy hxy
  rcases (mem_originalFeasibleSet_iff residual G X xy).1 hxy with ⟨hxX, hy⟩
  refine (Benders.mem_originalFeasibleSet_iff residual G X xy).2 ?_
  exact ⟨hxX,
    (mem_subproblemFeasibleSet_iff_mem_benders_subproblem_feasible_set
      G
      (residual xy.1)
      xy.2).1 hy |>.1⟩

/-- The source value of the residual-based equality-constrained mixed problem, namely the maximum
of `f(x) + h y` over the feasible pairs `(x, y)`, recorded in `EReal` so infeasible instances
have value `⊥` and unbounded-above instances have value `⊤`. -/
noncomputable def originalValue
    (residual : α → Fin m → ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (X : Set α)
    (f : α → ℝ)
    (h : Fin p → ℝ) : EReal :=
  sSup
    ((fun xy : α × (Fin p → ℝ) ↦ ((f xy.1 + h ⬝ᵥ xy.2 : ℝ) : EReal)) ''
      originalFeasibleSet residual G X)

/-- Residual-based equality-constrained Benders reformulation principle: if the feasible master
projection is exactly the feasibility-cut region and the equality-constrained subproblem value is
exactly the supremum described by the optimality cuts, then the original mixed problem value
equals the ordinary Benders master value. -/
theorem originalValue_eq_masterValue
    (residual : α → Fin m → ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (X : Set α)
    (f : α → ℝ)
    (h : Fin p → ℝ)
    (u : K → Fin m → ℝ)
    (r : J → Fin m → ℝ)
    (hproj : projectionSet residual G = Benders.feasibilityCutSet residual r)
    (hsubproblem :
      ∀ x : α,
        x ∈ projectionSet residual G →
          subproblemValue G h (residual x) =
            Benders.optimalityCutValue residual u x) :
    originalValue residual G X f h = Benders.masterValue residual X u r f := by
  apply le_antisymm
  · refine sSup_le ?_
    rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
    rcases (mem_originalFeasibleSet_iff residual G X (x, y)).1 hxy with ⟨hxX, hyfeas⟩
    have hxproj : x ∈ projectionSet residual G := by
      exact (mem_projectionSet_iff residual G x).2 ⟨y, hyfeas⟩
    have hy_le_subproblem :
        ((h ⬝ᵥ y : ℝ) : EReal) ≤ subproblemValue G h (residual x) := by
      exact le_sSup (Set.mem_image_of_mem (fun y' : Fin p → ℝ ↦ ((h ⬝ᵥ y' : ℝ) : EReal)) hyfeas)
    have hy_le_optimality :
        ((h ⬝ᵥ y : ℝ) : EReal) ≤ Benders.optimalityCutValue residual u x := by
      simpa [hsubproblem x hxproj] using hy_le_subproblem
    have hcuts : ∀ k, h ⬝ᵥ y ≤ u k ⬝ᵥ residual x := by
      intro k
      have hk_upper :
          Benders.optimalityCutValue residual u x ≤ ((u k ⬝ᵥ residual x : ℝ) : EReal) := by
        refine sSup_le ?_
        rintro _ ⟨η, hη, rfl⟩
        simpa using hη k
      exact_mod_cast hy_le_optimality.trans hk_upper
    have hxfeas : x ∈ Benders.feasibilityCutSet residual r := by
      rw [← hproj]
      exact hxproj
    have hmaster : (x, h ⬝ᵥ y) ∈ Benders.masterFeasibleSet residual X u r := by
      exact (Benders.mem_masterFeasibleSet_iff residual X u r (x, h ⬝ᵥ y)).2
        ⟨hxX, hcuts, (Benders.mem_feasibilityCutSet_iff residual r x).1 hxfeas⟩
    exact le_sSup
      (Set.mem_image_of_mem
        (fun xη : α × ℝ ↦ ((f xη.1 + xη.2 : ℝ) : EReal))
        hmaster)
  · refine sSup_le ?_
    rintro _ ⟨⟨x, η⟩, hxη, rfl⟩
    rcases (Benders.mem_masterFeasibleSet_iff residual X u r (x, η)).1 hxη with
      ⟨hxX, hηcuts, hxfeas⟩
    have hxfeas_mem : x ∈ Benders.feasibilityCutSet residual r := by
      exact (Benders.mem_feasibilityCutSet_iff residual r x).2 hxfeas
    have hxproj : x ∈ projectionSet residual G := by
      rw [hproj]
      exact hxfeas_mem
    rcases (mem_projectionSet_iff residual G x).1 hxproj with ⟨y, hyfeas⟩
    have hη_le_optimality :
        ((η : ℝ) : EReal) ≤ Benders.optimalityCutValue residual u x := by
      exact le_sSup
        (Set.mem_image_of_mem (fun η' : ℝ ↦ (η' : EReal))
          ((Benders.mem_optimalityCutSet_iff residual u x η).2 hηcuts))
    have hη_le_subproblem :
        ((η : ℝ) : EReal) ≤ subproblemValue G h (residual x) := by
      simpa [hsubproblem x hxproj] using hη_le_optimality
    have horiginal_feasible : (x, y) ∈ originalFeasibleSet residual G X := by
      exact (mem_originalFeasibleSet_iff residual G X (x, y)).2 ⟨hxX, hyfeas⟩
    have hy_le_original :
        ((f x + h ⬝ᵥ y : ℝ) : EReal) ≤ originalValue residual G X f h := by
      exact le_sSup
        (Set.mem_image_of_mem
          (fun xy : α × (Fin p → ℝ) ↦ ((f xy.1 + h ⬝ᵥ xy.2 : ℝ) : EReal))
          horiginal_feasible)
    have horiginal_ne_bot : originalValue residual G X f h ≠ ⊥ := by
      exact ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe (f x + h ⬝ᵥ y)) hy_le_original)
    by_cases horiginal_top : originalValue residual G X f h = ⊤
    · simp [horiginal_top]
    · have hsubproblem_le_real :
          subproblemValue G h (residual x) ≤
            (((originalValue residual G X f h).toReal - f x : ℝ) : EReal) := by
        refine sSup_le ?_
        rintro _ ⟨y', hy'feas, rfl⟩
        have hy'_original_feasible : (x, y') ∈ originalFeasibleSet residual G X := by
          exact (mem_originalFeasibleSet_iff residual G X (x, y')).2 ⟨hxX, hy'feas⟩
        have hy'_le_original :
            ((f x + h ⬝ᵥ y' : ℝ) : EReal) ≤ originalValue residual G X f h := by
          exact le_sSup
            (Set.mem_image_of_mem
              (fun xy : α × (Fin p → ℝ) ↦ ((f xy.1 + h ⬝ᵥ xy.2 : ℝ) : EReal))
              hy'_original_feasible)
        have hy'_le_real :
            ((f x + h ⬝ᵥ y' : ℝ) : EReal) ≤
              (((originalValue residual G X f h).toReal : ℝ) : EReal) := by
          exact hy'_le_original.trans (EReal.le_coe_toReal horiginal_top)
        have hy'_le_real' : f x + h ⬝ᵥ y' ≤ (originalValue residual G X f h).toReal := by
          exact_mod_cast hy'_le_real
        have hy'_translated : h ⬝ᵥ y' ≤ (originalValue residual G X f h).toReal - f x := by
          linarith
        change ((h ⬝ᵥ y' : ℝ) : EReal) ≤
          (((originalValue residual G X f h).toReal - f x : ℝ) : EReal)
        exact_mod_cast hy'_translated
      have hη_le_real : η ≤ (originalValue residual G X f h).toReal - f x := by
        exact_mod_cast hη_le_subproblem.trans hsubproblem_le_real
      have hobjective_le_real : f x + η ≤ (originalValue residual G X f h).toReal := by
        linarith
      calc
        ((f x + η : ℝ) : EReal)
            ≤ (((originalValue residual G X f h).toReal : ℝ) : EReal) := by
              exact_mod_cast hobjective_le_real
        _ = originalValue residual G X f h :=
              EReal.coe_toReal horiginal_top horiginal_ne_bot

end Equality
end Benders

end Exercise816Equality

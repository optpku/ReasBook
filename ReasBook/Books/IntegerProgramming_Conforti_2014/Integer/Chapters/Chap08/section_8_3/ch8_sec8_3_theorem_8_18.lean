/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Data.EReal.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Analysis.Convex.Extreme
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_3.ch3_sec3_3_proposition_3_9
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_3.ch3_sec3_3_remark_3_10
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_3.ch3_sec3_3_theorem_3_7
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_proposition_3_15
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_definition_3_10_extra_3
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_theorem_3_13
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_14.ch3_sec3_14_corollary_3_42
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_15.ch3_sec3_15_corollary_3_47
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_definition_3_11_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_8.ch4_sec4_8_remark_4_32
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Notation

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

-- Semantic recall note: `lean_leansearch` surfaced `instSupSetEReal` and
-- `Real.sSup_of_not_bddAbove`, matching the Chapter 8 precedent that value owners should use
-- `EReal` when unbounded-above behavior matters.
-- Local analogue note: the projection-style API follows Chapter 4 Theorem 4.39, and the
-- optimization-value surface follows the Chapter 8 relaxation-value files.

section Theorem818

variable {m n p : ℕ}
universe u v w

variable {K : Type u} {J : Type v}

/-- The right-hand side `b - A x` that appears after fixing the master variable `x` in the
Benders subproblem. -/
def benders_residual
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i ↦ b i - (A *ᵥ x) i

/-- The coordinate formula for the Benders residual `b - A x`. -/
theorem benders_residual_apply
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (x : Fin n → ℝ)
    (i : Fin m) :
    benders_residual A b x i = b i - (A *ᵥ x) i := rfl

/-- The linear-programming Benders subproblem feasible set
`{y | G y ≤ rhs, y ≥ 0}` for a fixed right-hand side `rhs`. -/
def benders_subproblem_feasible_set
    (G : Matrix (Fin m) (Fin p) ℝ)
    (rhs : Fin m → ℝ) : Set (Fin p → ℝ) :=
  {y | G *ᵥ y ≤ rhs ∧ ∀ i, 0 ≤ y i}

/-- Membership in the Benders subproblem feasible set is exactly the system
`G y ≤ rhs` together with nonnegativity of `y`. -/
theorem mem_benders_subproblem_feasible_set_iff
    (G : Matrix (Fin m) (Fin p) ℝ)
    (rhs : Fin m → ℝ)
    (y : Fin p → ℝ) :
    y ∈ benders_subproblem_feasible_set G rhs ↔
      G *ᵥ y ≤ rhs ∧ ∀ i, 0 ≤ y i := Iff.rfl

/-- The optimal value `z_LP(x)` of the Benders subproblem with right-hand side `rhs`, recorded in
`EReal` so unbounded-above subproblems have value `⊤ = +∞`. -/
noncomputable def benders_subproblem_value
    (G : Matrix (Fin m) (Fin p) ℝ)
    (h : Fin p → ℝ)
    (rhs : Fin m → ℝ) : EReal :=
  sSup
    ((fun y : Fin p → ℝ ↦ ((h ⬝ᵥ y : ℝ) : EReal)) ''
      benders_subproblem_feasible_set G rhs)

/-- The dual polyhedron `Q = {v ∈ ℝ^m_+ | v G ≥ h}` of the Benders subproblem. -/
def benders_dual_polyhedron
    (G : Matrix (Fin m) (Fin p) ℝ)
    (h : Fin p → ℝ) : Set (Fin m → ℝ) :=
  {v | 0 ≤ v ∧ h ≤ v ᵥ* G}

/-- Membership in `benders_dual_polyhedron G h` is exactly the conjunction `v ≥ 0` and
`v ᵥ* G ≥ h`. -/
theorem mem_benders_dual_polyhedron_iff
    (G : Matrix (Fin m) (Fin p) ℝ)
    (h : Fin p → ℝ)
    (v : Fin m → ℝ) :
    v ∈ benders_dual_polyhedron G h ↔ 0 ≤ v ∧ h ≤ v ᵥ* G :=
  Iff.rfl

/-- The cone `C = {v ∈ ℝ^m_+ | v G ≥ 0}` whose extreme rays define the Benders feasibility cuts. -/
def benders_dual_cone
    (G : Matrix (Fin m) (Fin p) ℝ) : Set (Fin m → ℝ) :=
  {v | 0 ≤ v ∧ 0 ≤ v ᵥ* G}

/-- Membership in `benders_dual_cone G` is exactly the conjunction `v ≥ 0` and `v ᵥ* G ≥ 0`. -/
theorem mem_benders_dual_cone_iff
    (G : Matrix (Fin m) (Fin p) ℝ)
    (v : Fin m → ℝ) :
    v ∈ benders_dual_cone G ↔ 0 ≤ v ∧ 0 ≤ v ᵥ* G :=
  Iff.rfl

/-- A finite family `points` represents the extreme points of `P` when each listed point is an
extreme point of `P`, different indices represent different points, and every extreme point of
`P` appears in the family. -/
def IsExtremePointRepresentativeFamily
    (P : Set (Fin m → ℝ))
    {q : ℕ}
    (points : Fin q → Fin m → ℝ) : Prop :=
  (∀ k : Fin q, points k ∈ P.extremePoints ℝ) ∧
    Pairwise (fun k l ↦ points k ≠ points l) ∧
      ∀ x : Fin m → ℝ, x ∈ P.extremePoints ℝ → ∃ k : Fin q, x = points k

/-- Unfolding `IsExtremePointRepresentativeFamily P points` gives the source-facing extreme-point,
pairwise-distinct-point, and spanning conditions. -/
theorem isExtremePointRepresentativeFamily_iff
    (P : Set (Fin m → ℝ))
    {q : ℕ}
    (points : Fin q → Fin m → ℝ) :
    IsExtremePointRepresentativeFamily P points ↔
      (∀ k : Fin q, points k ∈ P.extremePoints ℝ) ∧
        Pairwise (fun k l ↦ points k ≠ points l) ∧
          ∀ x : Fin m → ℝ, x ∈ P.extremePoints ℝ → ∃ k : Fin q, x = points k :=
  Iff.rfl

/-- A finite family `rays` represents the extreme rays of `C` when each listed vector generates
an extreme ray of `C`, different indices represent different rays, and every extreme ray of `C`
is same-ray equivalent to one of the listed vectors. -/
def IsExtremeRayRepresentativeFamilyLocal
    (C : Set (Fin m → ℝ))
    {q : ℕ}
    (rays : Fin q → Fin m → ℝ) : Prop :=
  (∀ t : Fin q, IsExtremeRayOfCone C (rays t)) ∧
    Pairwise (fun s t ↦ ¬ SameRay ℝ (rays s) (rays t)) ∧
      ∀ r : Fin m → ℝ, IsExtremeRayOfCone C r → ∃ t : Fin q, SameRay ℝ r (rays t)

/-- Unfolding `IsExtremeRayRepresentativeFamilyLocal C rays` gives the source-facing extreme-ray,
pairwise-distinct-ray, and spanning conditions. -/
theorem isExtremeRayRepresentativeFamilyLocal_iff
    (C : Set (Fin m → ℝ))
    {q : ℕ}
    (rays : Fin q → Fin m → ℝ) :
    IsExtremeRayRepresentativeFamilyLocal C rays ↔
      (∀ t : Fin q, IsExtremeRayOfCone C (rays t)) ∧
        Pairwise (fun s t ↦ ¬ SameRay ℝ (rays s) (rays t)) ∧
          ∀ r : Fin m → ℝ, IsExtremeRayOfCone C r → ∃ t : Fin q, SameRay ℝ r (rays t) :=
  Iff.rfl

/- Core residual-parametrized Benders owners used by the linear theorem and its later variants. -/
namespace Benders

variable {α : Type w}

/-- The `x`-projection of a mixed system whose fixed-`x` right-hand side is `residual x`,
encoded as existence of a feasible subproblem solution. -/
def projectionSet
    (residual : α → Fin m → ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ) : Set α :=
  {x | ∃ y, y ∈ benders_subproblem_feasible_set G (residual x)}

/-- Membership in `projectionSet residual G` means that there exists a nonnegative vector `y`
satisfying `G y ≤ residual x`. -/
theorem mem_projectionSet_iff
    (residual : α → Fin m → ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (x : α) :
    x ∈ projectionSet residual G ↔
      ∃ y : Fin p → ℝ, y ∈ benders_subproblem_feasible_set G (residual x) :=
  Iff.rfl

/-- The optimality cuts generated by `u` at a fixed master point `x`, expressed through the
residual map. -/
def optimalityCutSet
    (residual : α → Fin m → ℝ)
    (u : K → Fin m → ℝ)
    (x : α) : Set ℝ :=
  {η | ∀ k, η ≤ u k ⬝ᵥ residual x}

/-- Membership in the residual-based Benders optimality-cut set means satisfying every inequality
`η ≤ u^k residual x`. -/
theorem mem_optimalityCutSet_iff
    (residual : α → Fin m → ℝ)
    (u : K → Fin m → ℝ)
    (x : α)
    (η : ℝ) :
    η ∈ optimalityCutSet residual u x ↔
      ∀ k, η ≤ u k ⬝ᵥ residual x :=
  Iff.rfl

/-- The supremal `η` allowed by all residual-based Benders optimality cuts at `x`, recorded in
`EReal` so the unconstrained case has value `⊤ = +∞`. -/
noncomputable def optimalityCutValue
    (residual : α → Fin m → ℝ)
    (u : K → Fin m → ℝ)
    (x : α) : EReal :=
  sSup ((fun η : ℝ ↦ (η : EReal)) '' optimalityCutSet residual u x)

/-- The feasibility cuts generated by `r` on the master variable through the residual map. -/
def feasibilityCutSet
    (residual : α → Fin m → ℝ)
    (r : J → Fin m → ℝ) : Set α :=
  {x | ∀ j, 0 ≤ r j ⬝ᵥ residual x}

/-- Membership in the residual-based Benders feasibility-cut set means satisfying every inequality
`r^j residual x ≥ 0`. -/
theorem mem_feasibilityCutSet_iff
    (residual : α → Fin m → ℝ)
    (r : J → Fin m → ℝ)
    (x : α) :
    x ∈ feasibilityCutSet residual r ↔
      ∀ j, 0 ≤ r j ⬝ᵥ residual x :=
  Iff.rfl

/-- The feasible set of a mixed problem with master variable restricted to `X` and subproblem
right-hand side `residual x`. -/
def originalFeasibleSet
    (residual : α → Fin m → ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (X : Set α) : Set (α × (Fin p → ℝ)) :=
  {xy | xy.1 ∈ X ∧ xy.2 ∈ benders_subproblem_feasible_set G (residual xy.1)}

/-- Membership in the residual-based mixed feasible set means `x ∈ X` and `y` solves the
subproblem with right-hand side `residual x`. -/
theorem mem_originalFeasibleSet_iff
    (residual : α → Fin m → ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (X : Set α)
    (xy : α × (Fin p → ℝ)) :
    xy ∈ originalFeasibleSet residual G X ↔
      xy.1 ∈ X ∧ xy.2 ∈ benders_subproblem_feasible_set G (residual xy.1) :=
  Iff.rfl

/-- The source value of the residual-based mixed problem, namely the maximum of `f(x) + h y` over
the feasible pairs `(x, y)`, recorded in `EReal` so infeasible instances have value `⊥` and
unbounded-above instances have value `⊤`. -/
noncomputable def originalValue
    (residual : α → Fin m → ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (X : Set α)
    (f : α → ℝ)
    (h : Fin p → ℝ) : EReal :=
  sSup
    ((fun xy : α × (Fin p → ℝ) ↦ ((f xy.1 + h ⬝ᵥ xy.2 : ℝ) : EReal)) ''
      originalFeasibleSet residual G X)

/-- The feasible set of the residual-based Benders master reformulation, with optimality cuts
indexed by `K` and feasibility cuts indexed by `J`. -/
def masterFeasibleSet
    (residual : α → Fin m → ℝ)
    (X : Set α)
    (u : K → Fin m → ℝ)
    (r : J → Fin m → ℝ) : Set (α × ℝ) :=
  {xη |
    xη.1 ∈ X ∧
      xη.2 ∈ optimalityCutSet residual u xη.1 ∧
      xη.1 ∈ feasibilityCutSet residual r}

/-- Membership in the residual-based Benders master feasible set is exactly the conjunction of the
master restriction `x ∈ X`, all optimality cuts, and all feasibility cuts. -/
theorem mem_masterFeasibleSet_iff
    (residual : α → Fin m → ℝ)
    (X : Set α)
    (u : K → Fin m → ℝ)
    (r : J → Fin m → ℝ)
    (xη : α × ℝ) :
    xη ∈ masterFeasibleSet residual X u r ↔
      xη.1 ∈ X ∧
        (∀ k, xη.2 ≤ u k ⬝ᵥ residual xη.1) ∧
        ∀ j, 0 ≤ r j ⬝ᵥ residual xη.1 := by
  rfl

/-- The optimal value of the residual-based Benders master reformulation, namely the maximum of
`f(x) + η` over the master feasible pairs `(x, η)`, recorded in `EReal` so infeasible instances
have value `⊥` and unbounded-above instances have value `⊤`. -/
noncomputable def masterValue
    (residual : α → Fin m → ℝ)
    (X : Set α)
    (u : K → Fin m → ℝ)
    (r : J → Fin m → ℝ)
    (f : α → ℝ) : EReal :=
  sSup
    ((fun xη : α × ℝ ↦ ((f xη.1 + xη.2 : ℝ) : EReal)) ''
      masterFeasibleSet residual X u r)

/-- Residual-based Benders reformulation principle: if the feasible master projection is exactly
the feasibility-cut region and the subproblem value is exactly the supremum described by the
optimality cuts, then the original mixed problem value equals the Benders master value. -/
theorem originalValue_eq_masterValue
    (residual : α → Fin m → ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (X : Set α)
    (f : α → ℝ)
    (h : Fin p → ℝ)
    (u : K → Fin m → ℝ)
    (r : J → Fin m → ℝ)
    (hproj : projectionSet residual G = feasibilityCutSet residual r)
    (hsubproblem :
      ∀ x : α,
        x ∈ projectionSet residual G →
          benders_subproblem_value G h (residual x) =
            optimalityCutValue residual u x) :
    originalValue residual G X f h = masterValue residual X u r f := by
  apply le_antisymm
  · refine sSup_le ?_
    rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
    rcases (mem_originalFeasibleSet_iff residual G X (x, y)).1 hxy with ⟨hxX, hyfeas⟩
    have hxproj : x ∈ projectionSet residual G := by
      -- The original feasible pair gives the fixed-`x` subproblem witness.
      exact (mem_projectionSet_iff residual G x).2 ⟨y, hyfeas⟩
    have hy_le_subproblem :
        ((h ⬝ᵥ y : ℝ) : EReal) ≤ benders_subproblem_value G h (residual x) := by
      -- Any feasible `y` contributes one candidate value to the subproblem supremum.
      exact le_sSup (Set.mem_image_of_mem (fun y' : Fin p → ℝ ↦ ((h ⬝ᵥ y' : ℝ) : EReal)) hyfeas)
    have hy_le_optimality :
        ((h ⬝ᵥ y : ℝ) : EReal) ≤ optimalityCutValue residual u x := by
      -- Replace the subproblem value by the assumed optimality-cut supremum.
      simpa [hsubproblem x hxproj] using hy_le_subproblem
    have hcuts : ∀ k, h ⬝ᵥ y ≤ u k ⬝ᵥ residual x := by
      intro k
      have hk_upper :
          optimalityCutValue residual u x ≤ ((u k ⬝ᵥ residual x : ℝ) : EReal) := by
        -- Every listed cut bounds the entire optimality-cut owner from above.
        refine sSup_le ?_
        rintro _ ⟨η, hη, rfl⟩
        simpa using hη k
      exact_mod_cast hy_le_optimality.trans hk_upper
    have hxfeas : x ∈ feasibilityCutSet residual r := by
      -- The projection hypothesis identifies subproblem feasibility with feasibility cuts.
      rw [← hproj]
      exact hxproj
    have hmaster : (x, h ⬝ᵥ y) ∈ masterFeasibleSet residual X u r := by
      -- The original feasible pair induces a master feasible pair with `η = h y`.
      exact (mem_masterFeasibleSet_iff residual X u r (x, h ⬝ᵥ y)).2
        ⟨hxX, hcuts, (mem_feasibilityCutSet_iff residual r x).1 hxfeas⟩
    -- This master feasible pair realizes the same objective value.
    exact le_sSup
      (Set.mem_image_of_mem
        (fun xη : α × ℝ ↦ ((f xη.1 + xη.2 : ℝ) : EReal))
        hmaster)
  · refine sSup_le ?_
    rintro _ ⟨⟨x, η⟩, hxη, rfl⟩
    rcases (mem_masterFeasibleSet_iff residual X u r (x, η)).1 hxη with ⟨hxX, hηcuts, hxfeas⟩
    have hxfeas_mem : x ∈ feasibilityCutSet residual r := by
      -- Repackage the master-side inequalities as feasibility-cut membership.
      exact (mem_feasibilityCutSet_iff residual r x).2 hxfeas
    have hxproj : x ∈ projectionSet residual G := by
      -- The projection hypothesis turns feasibility cuts back into subproblem feasibility.
      rw [hproj]
      exact hxfeas_mem
    rcases (mem_projectionSet_iff residual G x).1 hxproj with ⟨y, hyfeas⟩
    have hη_le_optimality :
        ((η : ℝ) : EReal) ≤ optimalityCutValue residual u x := by
      -- The chosen `η` is one admissible point of the optimality-cut owner.
      exact le_sSup
        (Set.mem_image_of_mem (fun η' : ℝ ↦ (η' : EReal))
          ((mem_optimalityCutSet_iff residual u x η).2 hηcuts))
    have hη_le_subproblem :
        ((η : ℝ) : EReal) ≤ benders_subproblem_value G h (residual x) := by
      -- Replace the optimality-cut owner by the subproblem value.
      simpa [hsubproblem x hxproj] using hη_le_optimality
    have horiginal_feasible : (x, y) ∈ originalFeasibleSet residual G X := by
      -- The recovered subproblem witness yields an original feasible pair.
      exact (mem_originalFeasibleSet_iff residual G X (x, y)).2 ⟨hxX, hyfeas⟩
    have hy_le_original :
        ((f x + h ⬝ᵥ y : ℝ) : EReal) ≤ originalValue residual G X f h := by
      -- Any recovered feasible pair contributes to the original-value supremum.
      exact le_sSup
        (Set.mem_image_of_mem
          (fun xy : α × (Fin p → ℝ) ↦ ((f xy.1 + h ⬝ᵥ xy.2 : ℝ) : EReal))
          horiginal_feasible)
    have horiginal_ne_bot : originalValue residual G X f h ≠ ⊥ := by
      -- The existence of one feasible original pair rules out value `⊥`.
      exact ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe (f x + h ⬝ᵥ y)) hy_le_original)
    by_cases horiginal_top : originalValue residual G X f h = ⊤
    · -- If the original value is already `⊤`, every master objective is below it.
      simp [horiginal_top]
    · have hsubproblem_le_real :
          benders_subproblem_value G h (residual x) ≤
            (((originalValue residual G X f h).toReal - f x : ℝ) : EReal) := by
        -- Every subproblem objective is bounded above by the translated original value.
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
      -- Translate the real upper bound back to the original `EReal` owner.
      calc
        ((f x + η : ℝ) : EReal)
            ≤ (((originalValue residual G X f h).toReal : ℝ) : EReal) := by
              exact_mod_cast hobjective_le_real
        _ = originalValue residual G X f h :=
              EReal.coe_toReal horiginal_top horiginal_ne_bot

end Benders

/-- The `x`-projection of the mixed system `A x + G y ≤ b`, `y ≥ 0`, encoded as existence of a
subproblem solution after fixing `x`. -/
abbrev benders_projection_set
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  Benders.projectionSet (benders_residual A b) G

/-- Membership in the `x`-projection means that there exists a nonnegative vector `y` satisfying
`G y ≤ b - A x`. -/
theorem mem_benders_projection_set_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (x : Fin n → ℝ) :
    x ∈ benders_projection_set A G b ↔
      ∃ y : Fin p → ℝ, y ∈ benders_subproblem_feasible_set G (benders_residual A b x) :=
  Benders.mem_projectionSet_iff (benders_residual A b) G x

/-- The optimality cuts generated by `u` at a fixed master vector `x`. -/
abbrev benders_optimality_cut_set
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (u : K → Fin m → ℝ)
    (x : Fin n → ℝ) : Set ℝ :=
  Benders.optimalityCutSet (benders_residual A b) u x

/-- Membership in the Benders optimality-cut set means satisfying every inequality
`η ≤ u^k (b - A x)`. -/
theorem mem_benders_optimality_cut_set_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (u : K → Fin m → ℝ)
    (x : Fin n → ℝ)
    (η : ℝ) :
    η ∈ benders_optimality_cut_set A b u x ↔
      ∀ k, η ≤ u k ⬝ᵥ benders_residual A b x :=
  Benders.mem_optimalityCutSet_iff (benders_residual A b) u x η

/-- The supremal `η` allowed by all Benders optimality cuts at `x`. -/
noncomputable abbrev benders_optimality_cut_value
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (u : K → Fin m → ℝ)
    (x : Fin n → ℝ) : EReal :=
  Benders.optimalityCutValue (benders_residual A b) u x

/-- The feasibility cuts generated by `r` on the master variable `x`. -/
abbrev benders_feasibility_cut_set
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (r : J → Fin m → ℝ) : Set (Fin n → ℝ) :=
  Benders.feasibilityCutSet (benders_residual A b) r

/-- Membership in the Benders feasibility-cut set means satisfying every inequality
`r^j (b - A x) ≥ 0`. -/
theorem mem_benders_feasibility_cut_set_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (r : J → Fin m → ℝ)
    (x : Fin n → ℝ) :
    x ∈ benders_feasibility_cut_set A b r ↔
      ∀ j, 0 ≤ r j ⬝ᵥ benders_residual A b x :=
  Benders.mem_feasibilityCutSet_iff (benders_residual A b) r x

/-- The feasible set of the original mixed problem (8.26), with master variable restricted to the
set `X`. -/
abbrev benders_original_feasible_set
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ)) : Set ((Fin n → ℝ) × (Fin p → ℝ)) :=
  Benders.originalFeasibleSet (benders_residual A b) G X

/-- Membership in the original mixed feasible set means `x ∈ X` and `y` solves the Benders
subproblem with right-hand side `b - A x`. -/
theorem mem_benders_original_feasible_set_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ))
    (xy : (Fin n → ℝ) × (Fin p → ℝ)) :
    xy ∈ benders_original_feasible_set A G b X ↔
      xy.1 ∈ X ∧
        xy.2 ∈ benders_subproblem_feasible_set G (benders_residual A b xy.1) :=
  Benders.mem_originalFeasibleSet_iff (benders_residual A b) G X xy

/-- The source value `z_I` of the original mixed problem (8.26), namely the maximum of
`c x + h y` over the feasible pairs `(x, y)`. -/
noncomputable abbrev benders_original_value
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    (h : Fin p → ℝ) : EReal :=
  Benders.originalValue (benders_residual A b) G X (fun x ↦ c ⬝ᵥ x) h

/-- The feasible set of the Benders master reformulation (8.27), with optimality cuts indexed by
`K` and feasibility cuts indexed by `J`. -/
abbrev benders_master_feasible_set
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ))
    (u : K → Fin m → ℝ)
    (r : J → Fin m → ℝ) : Set ((Fin n → ℝ) × ℝ) :=
  Benders.masterFeasibleSet (benders_residual A b) X u r

/-- Membership in the Benders master feasible set is exactly the conjunction of the master
restriction `x ∈ X`, all optimality cuts, and all feasibility cuts. -/
theorem mem_benders_master_feasible_set_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ))
    (u : K → Fin m → ℝ)
    (r : J → Fin m → ℝ)
    (xη : (Fin n → ℝ) × ℝ) :
    xη ∈ benders_master_feasible_set A b X u r ↔
      xη.1 ∈ X ∧
        (∀ k, xη.2 ≤ u k ⬝ᵥ benders_residual A b xη.1) ∧
        ∀ j, 0 ≤ r j ⬝ᵥ benders_residual A b xη.1 :=
  Benders.mem_masterFeasibleSet_iff (benders_residual A b) X u r xη

/-- The optimal value of the Benders master reformulation (8.27), namely the maximum of
`η + c x` over the master feasible pairs `(x, η)`. -/
noncomputable abbrev benders_master_value
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ))
    (u : K → Fin m → ℝ)
    (r : J → Fin m → ℝ)
    (c : Fin n → ℝ) : EReal :=
  Benders.masterValue (benders_residual A b) X u r (fun x ↦ c ⬝ᵥ x)

/-- Helper for Theorem 8.18: the integer-block coordinates of
`u ᵥ* mixedConstraintMatrix A_I A_C` are exactly `u ᵥ* A_I`. -/
lemma vecMul_mixedConstraintMatrix_castAdd
    (A_I : Matrix (Fin m) (Fin p) ℝ)
    (A_C : Matrix (Fin m) (Fin m) ℝ)
    (u : Fin m → ℝ)
    (j : Fin p) :
    (u ᵥ* mixedConstraintMatrix A_I A_C) (Fin.castAdd m j) = (u ᵥ* A_I) j := by
  -- Expand the block matrix by coordinates and read off the left block directly.
  simp [mixedConstraintMatrix, Matrix.vecMul, dotProduct]

/-- Helper for Theorem 8.18: the slack-block coordinates of
`u ᵥ* mixedConstraintMatrix A_I A_C` are exactly `u ᵥ* A_C`. -/
lemma vecMul_mixedConstraintMatrix_natAdd
    (A_I : Matrix (Fin m) (Fin p) ℝ)
    (A_C : Matrix (Fin m) (Fin m) ℝ)
    (u : Fin m → ℝ)
    (j : Fin m) :
    (u ᵥ* mixedConstraintMatrix A_I A_C) (Fin.natAdd p j) = (u ᵥ* A_C) j := by
  -- Expand the block matrix by coordinates and read off the right block directly.
  simp [mixedConstraintMatrix, Matrix.vecMul, dotProduct]

/-- Helper for Theorem 8.18: an extreme ray generator belongs to the cone whose edge it spans. -/
lemma extremeRay_mem_of_isExtremeRayOfCone
    {C : Set (Fin m → ℝ)}
    {r : Fin m → ℝ}
    (hr : IsExtremeRayOfCone C r) :
    r ∈ C := by
  -- Unpack the edge witness and evaluate the resulting extreme subset at the generator itself.
  have hr_edge :
      IsEdgeOf C (PointedCone.hull ℝ ({r} : Set (Fin m → ℝ)) : Set (Fin m → ℝ)) :=
    (isExtremeRayOfCone_iff).1 hr
  exact hr_edge.isExtreme.1 (PointedCone.subset_hull (by simp))

/-- Helper for Theorem 8.18: a nonzero vector on the same ray as a listed cone generator remains
inside the finitely generated cone spanned by that family. -/
lemma sameRay_mem_finitelyGeneratedCone_ofMemOfNonzero
    {q : ℕ}
    {rays : Fin q → Fin m → ℝ}
    {x y : Fin m → ℝ}
    (hy_nonzero : y ≠ 0)
    (hxy : SameRay ℝ x y)
    (hy : y ∈ finitely_generated_cone rays) :
    x ∈ finitely_generated_cone rays := by
  -- Same-ray equivalence rewrites `x` as a nonnegative multiple of the nonzero cone point `y`.
  rcases hxy.exists_nonneg_right hy_nonzero with ⟨a, ha, rfl⟩
  exact cone_smul_mem hy ha

/-- Helper for Theorem 8.18: raywise bounds propagate to every multiplier in the finitely
generated cone spanned by the listed rays. -/
lemma finitelyGeneratedCone_evaluation_le_ofRaywiseLe
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    {q : ℕ}
    (rays : Fin q → Fin m → ℝ)
    {x : Fin n → ℝ}
    {u : Fin m → ℝ}
    (hRaywise : ∀ t : Fin q, rays t ⬝ᵥ (A *ᵥ x) ≤ rays t ⬝ᵥ b)
    (hu : u ∈ finitely_generated_cone rays) :
    u ⬝ᵥ (A *ᵥ x) ≤ u ⬝ᵥ b := by
  rcases (mem_finitely_generated_cone_iff.mp hu) with ⟨μ, hμ_nonneg, rfl⟩
  -- Expanding the conic combination reduces the claim to summing the listed raywise inequalities.
  calc
    (∑ t : Fin q, μ t • rays t) ⬝ᵥ (A *ᵥ x)
        = ∑ t : Fin q, (μ t • rays t) ⬝ᵥ (A *ᵥ x) := by
            simpa using (sum_dotProduct Finset.univ (fun t : Fin q ↦ μ t • rays t) (A *ᵥ x))
    _ = ∑ t : Fin q, μ t * (rays t ⬝ᵥ (A *ᵥ x)) := by
          simp [smul_eq_mul]
    _ ≤ ∑ t : Fin q, μ t * (rays t ⬝ᵥ b) := by
          refine Finset.sum_le_sum ?_
          intro t ht
          exact mul_le_mul_of_nonneg_left (hRaywise t) (hμ_nonneg t)
    _ = ∑ t : Fin q, (μ t • rays t) ⬝ᵥ b := by
          simp [smul_eq_mul]
    _ = (∑ t : Fin q, μ t • rays t) ⬝ᵥ b := by
          symm
          simpa using (sum_dotProduct Finset.univ (fun t : Fin q ↦ μ t • rays t) b)

/-- Helper for Theorem 8.18: the feasible `x`-projection is exactly the family of residual points
that satisfy every inequality coming from the full dual cone `C = {v ≥ 0 | v ᵥ* G ≥ 0}`. -/
lemma bendersProjectionSet_eq_allDualConeCuts
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ) :
    benders_projection_set A G b =
      {x : Fin n → ℝ |
        ∀ v : Fin m → ℝ, v ∈ benders_dual_cone G → 0 ≤ v ⬝ᵥ benders_residual A b x} := by
  ext x
  constructor
  · intro hx
    rcases (mem_benders_projection_set_iff A G b x).1 hx with ⟨y, hy⟩
    let s : Fin m → ℝ := fun i ↦ benders_residual A b x i - (G *ᵥ y) i
    have hs_nonneg : 0 ≤ s := by
      -- The slack variables record the residual inequality gap coordinatewise.
      intro i
      exact sub_nonneg.mpr (hy.1 i)
    have hslack :
        G *ᵥ y + (1 : Matrix (Fin m) (Fin m) ℝ) *ᵥ s = benders_residual A b x := by
      -- The chosen slack exactly completes the inequality `G y ≤ b - A x` to equality.
      ext i
      simp [s, benders_residual_apply]
    have hx_image :
        x ∈ Prod.fst '' {xz : (Fin n → ℝ) × (Fin (p + m) → ℝ) |
          A *ᵥ xz.1 +
              mixedConstraintMatrix G (1 : Matrix (Fin m) (Fin m) ℝ) *ᵥ xz.2 = b ∧
            0 ≤ xz.2} := by
      -- The original witness `y` together with its slack witness `s` fits Corollary 3.47.
      refine ⟨(x, Fin.append y s), ?_, rfl⟩
      constructor
      · calc
          A *ᵥ x +
              mixedConstraintMatrix G (1 : Matrix (Fin m) (Fin m) ℝ) *ᵥ Fin.append y s
              = A *ᵥ x + (G *ᵥ y + (1 : Matrix (Fin m) (Fin m) ℝ) *ᵥ s) := by
                  simp [mixedConstraintMatrix_mulVec_append]
          _ = A *ᵥ x + benders_residual A b x := by rw [hslack]
          _ = b := by
                ext i
                simp [benders_residual_apply]
      · -- Nonnegativity of the appended vector is exactly nonnegativity of `y` and `s`.
        intro j
        refine Fin.addCases ?_ ?_ j
        · intro j'
          simpa using hy.2 j'
        · intro i
          simpa [s] using hs_nonneg i
    rw [polyhedron_x_projection_image_eq_forall_nonneg_multipliers
      A
      (mixedConstraintMatrix G (1 : Matrix (Fin m) (Fin m) ℝ))
      b] at hx_image
    intro v hv
    rcases (mem_benders_dual_cone_iff G v).1 hv with ⟨hv_nonneg, hvG_nonneg⟩
    have hv_block :
        0 ≤ v ᵥ* mixedConstraintMatrix G (1 : Matrix (Fin m) (Fin m) ℝ) := by
      -- The block matrix inequality repackages `v ≥ 0` and `v ᵥ* G ≥ 0`.
      intro j
      refine Fin.addCases ?_ ?_ j
      · intro j'
        simpa [vecMul_mixedConstraintMatrix_castAdd] using hvG_nonneg j'
      · intro i
        simpa [vecMul_mixedConstraintMatrix_natAdd] using hv_nonneg i
    have hmult : v ⬝ᵥ (A *ᵥ x) ≤ v ⬝ᵥ b := hx_image v hv_block
    -- The multiplier inequality is exactly the nonnegativity of `v (b - A x)`.
    have hnonneg : 0 ≤ v ⬝ᵥ b - v ⬝ᵥ (A *ᵥ x) := sub_nonneg.mpr hmult
    have hresidual :
        v ⬝ᵥ benders_residual A b x = v ⬝ᵥ b - v ⬝ᵥ (A *ᵥ x) := by
      calc
        v ⬝ᵥ benders_residual A b x = v ⬝ᵥ (fun i ↦ b i - (A *ᵥ x) i) := rfl
        _ = v ⬝ᵥ b - v ⬝ᵥ (A *ᵥ x) := dotProduct_sub v b (A *ᵥ x)
    rw [hresidual]
    exact hnonneg
  · intro hx
    have hx_multipliers :
        x ∈ {x : Fin n → ℝ |
          ∀ u : Fin m → ℝ,
            0 ≤ u ᵥ* mixedConstraintMatrix G (1 : Matrix (Fin m) (Fin m) ℝ) →
              u ⬝ᵥ (A *ᵥ x) ≤ u ⬝ᵥ b} := by
      intro u hu
      have hu_cone : u ∈ benders_dual_cone G := by
        -- Reading the block inequalities back off the slack matrix recovers dual-cone membership.
        refine (mem_benders_dual_cone_iff G u).2 ⟨?_, ?_⟩
        · intro i
          have hui :
              0 ≤ (u ᵥ* mixedConstraintMatrix G (1 : Matrix (Fin m) (Fin m) ℝ))
                (Fin.natAdd p i) := hu (Fin.natAdd p i)
          simpa [vecMul_mixedConstraintMatrix_natAdd] using hui
        · intro j
          have huj :
              0 ≤ (u ᵥ* mixedConstraintMatrix G (1 : Matrix (Fin m) (Fin m) ℝ))
                (Fin.castAdd m j) := hu (Fin.castAdd m j)
          simpa [vecMul_mixedConstraintMatrix_castAdd] using huj
      have hu_residual : 0 ≤ u ⬝ᵥ benders_residual A b x := hx u hu_cone
      -- Rewrite the residual inequality into the multiplier inequality of Corollary 3.47.
      have hresidual :
          u ⬝ᵥ benders_residual A b x = u ⬝ᵥ b - u ⬝ᵥ (A *ᵥ x) := by
        calc
          u ⬝ᵥ benders_residual A b x = u ⬝ᵥ (fun i ↦ b i - (A *ᵥ x) i) := rfl
          _ = u ⬝ᵥ b - u ⬝ᵥ (A *ᵥ x) := dotProduct_sub u b (A *ᵥ x)
      rw [← sub_nonneg, ← hresidual]
      exact hu_residual
    have hx_image :
        x ∈ Prod.fst '' {xz : (Fin n → ℝ) × (Fin (p + m) → ℝ) |
          A *ᵥ xz.1 +
              mixedConstraintMatrix G (1 : Matrix (Fin m) (Fin m) ℝ) *ᵥ xz.2 = b ∧
            0 ≤ xz.2} := by
      -- Corollary 3.47 turns the universal multiplier inequalities back into a slack witness.
      rw [polyhedron_x_projection_image_eq_forall_nonneg_multipliers
        A
        (mixedConstraintMatrix G (1 : Matrix (Fin m) (Fin m) ℝ))
        b]
      exact hx_multipliers
    rcases (mem_image_fst_iff).1 hx_image with ⟨z, hz⟩
    let y : Fin p → ℝ := fun j ↦ z (Fin.castAdd m j)
    let s : Fin m → ℝ := fun i ↦ z (Fin.natAdd p i)
    have hz_append : z = Fin.append y s := by
      -- Split the flat slack witness into its `y` and slack blocks.
      ext j
      refine Fin.addCases ?_ ?_ j
      · intro j'
        simp [y]
      · intro i
        simp [s]
    have hz_eq :
        A *ᵥ x +
            mixedConstraintMatrix G (1 : Matrix (Fin m) (Fin m) ℝ) *ᵥ Fin.append y s = b := by
      -- Normalize the flat witness to the canonical appended form.
      simpa [hz_append] using hz.1
    have hs_nonneg : 0 ≤ s := by
      -- The slack block inherits nonnegativity from the appended witness.
      intro i
      simpa [s] using hz.2 (Fin.natAdd p i)
    have hy_nonneg : 0 ≤ y := by
      -- The `y` block inherits nonnegativity from the appended witness.
      intro j
      simpa [y] using hz.2 (Fin.castAdd m j)
    have hslack :
        G *ᵥ y + (1 : Matrix (Fin m) (Fin m) ℝ) *ᵥ s = benders_residual A b x := by
      -- Rearranging the slack-system equality recovers the residual equality `G y + s = b - A x`.
      ext i
      have hi := congrFun hz_eq i
      simp [mixedConstraintMatrix_mulVec_append, benders_residual_apply] at hi ⊢
      linarith
    refine (mem_benders_projection_set_iff A G b x).2 ?_
    refine ⟨y, (mem_benders_subproblem_feasible_set_iff G (benders_residual A b x) y).2 ?_⟩
    refine ⟨?_, ?_⟩
    · intro i
      have hi : (G *ᵥ y) i + s i = benders_residual A b x i := by
        simpa using congrFun hslack i
      have hs0 : 0 ≤ s i := hs_nonneg i
      linarith
    · intro j
      exact hy_nonneg j

/-- Helper for Theorem 8.18: every feasible `x` satisfies the listed feasibility cuts coming from
any representative family of extreme rays of the Benders dual cone. -/
lemma bendersProjectionSet_subset_feasibilityCutSet_ofExtremeRays
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    {qJ : ℕ}
    (r : Fin qJ → Fin m → ℝ)
    (hrays : IsExtremeRayRepresentativeFamilyLocal (benders_dual_cone G) r) :
    benders_projection_set A G b ⊆ benders_feasibility_cut_set A b r := by
  intro x hx
  rw [mem_benders_feasibility_cut_set_iff]
  have hx_all := (bendersProjectionSet_eq_allDualConeCuts A G b ▸ hx)
  -- Each listed ray lies in the dual cone, so the universal dual-cone inequalities apply to it.
  intro j
  exact hx_all (r j) (extremeRay_mem_of_isExtremeRayOfCone (hrays.1 j))

/-- Helper for Theorem 8.18: the row `-e_i` evaluates a vector `u` to `-u_i`. -/
lemma negSingleDotProduct_eq_neg
    (u : Fin m → ℝ)
    (i : Fin m) :
    (fun j ↦ -Pi.single i (1 : ℝ) j) ⬝ᵥ u = -u i := by
  -- Only the `i`th coordinate survives in the dot product against the negated singleton row.
  rw [dotProduct, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

/-- Helper for Theorem 8.18: the Benders dual cone is closed under nonnegative scaling. -/
lemma smul_mem_bendersDualCone
    (G : Matrix (Fin m) (Fin p) ℝ)
    {u : Fin m → ℝ}
    (hu : u ∈ benders_dual_cone G)
    {a : ℝ}
    (ha : 0 ≤ a) :
    a • u ∈ benders_dual_cone G := by
  rcases (mem_benders_dual_cone_iff G u).1 hu with ⟨hu_nonneg, hu_dual⟩
  refine (mem_benders_dual_cone_iff G (a • u)).2 ⟨?_, ?_⟩
  · intro i
    simpa [Pi.smul_apply, smul_eq_mul] using mul_nonneg ha (hu_nonneg i)
  · intro j
    have hj : 0 ≤ a * (u ᵥ* G) j := mul_nonneg ha (hu_dual j)
    simpa [Pi.smul_apply, smul_eq_mul, Matrix.smul_vecMul] using hj

/-- Helper for Theorem 8.18: the Benders dual cone is closed under addition. -/
lemma add_mem_bendersDualCone
    (G : Matrix (Fin m) (Fin p) ℝ)
    {u v : Fin m → ℝ}
    (hu : u ∈ benders_dual_cone G)
    (hv : v ∈ benders_dual_cone G) :
    u + v ∈ benders_dual_cone G := by
  rcases (mem_benders_dual_cone_iff G u).1 hu with ⟨hu_nonneg, hu_dual⟩
  rcases (mem_benders_dual_cone_iff G v).1 hv with ⟨hv_nonneg, hv_dual⟩
  refine (mem_benders_dual_cone_iff G (u + v)).2 ⟨?_, ?_⟩
  · intro i
    exact add_nonneg (hu_nonneg i) (hv_nonneg i)
  · intro j
    have hj : 0 ≤ (u ᵥ* G) j + (v ᵥ* G) j := add_nonneg (hu_dual j) (hv_dual j)
    simpa [Matrix.add_vecMul] using hj

/-- Helper for Theorem 8.18: the Benders dual cone is polyhedral because it is defined by the
homogeneous inequalities `u ≥ 0` and `u G ≥ 0`. -/
lemma bendersDualCone_isPolyhedralCone
    (G : Matrix (Fin m) (Fin p) ℝ) :
    is_polyhedral_cone (benders_dual_cone G) := by
  let M : Matrix (Fin (p + m)) (Fin m) ℝ :=
    Fin.addCases (-Gᵀ) fun i : Fin m ↦ -Pi.single i (1 : ℝ)
  refine (is_polyhedral_cone_iff).2 ?_
  refine ⟨p + m, M, ?_⟩
  ext u
  constructor
  · intro hu
    rcases (mem_benders_dual_cone_iff G u).1 hu with ⟨hu_nonneg, hu_dual⟩
    intro s
    refine Fin.addCases ?_ ?_ s
    · intro j
      have hj : 0 ≤ (u ᵥ* G) j := hu_dual j
      have hrow :
          (M *ᵥ u) (Fin.castAdd m j) = -((u ᵥ* G) j) := by
        calc
          (M *ᵥ u) (Fin.castAdd m j) = ((-Gᵀ) *ᵥ u) j := by
            simp [M, Matrix.mulVec, Fin.addCases_left]
          _ = -((u ᵥ* G) j) := by
            simpa [Matrix.neg_mulVec, Matrix.mulVec_transpose]
      rw [hrow]
      exact neg_nonpos.mpr hj
    · intro i
      have hrow :
          (M *ᵥ u) (Fin.natAdd p i) = -u i := by
        calc
          (M *ᵥ u) (Fin.natAdd p i)
              = (fun j ↦ -Pi.single i (1 : ℝ) j) ⬝ᵥ u := by
                  simp [M, Matrix.mulVec, Fin.addCases_right]
          _ = -u i := negSingleDotProduct_eq_neg u i
      rw [hrow]
      exact neg_nonpos.mpr (hu_nonneg i)
  · intro hu
    refine (mem_benders_dual_cone_iff G u).2 ⟨?_, ?_⟩
    · intro i
      have hi : (M *ᵥ u) (Fin.natAdd p i) ≤ 0 := hu (Fin.natAdd p i)
      have hrow :
          (M *ᵥ u) (Fin.natAdd p i) = -u i := by
        calc
          (M *ᵥ u) (Fin.natAdd p i)
              = (fun j ↦ -Pi.single i (1 : ℝ) j) ⬝ᵥ u := by
                  simp [M, Matrix.mulVec, Fin.addCases_right]
          _ = -u i := negSingleDotProduct_eq_neg u i
      rw [hrow] at hi
      exact neg_nonpos.mp hi
    · intro j
      have hj : (M *ᵥ u) (Fin.castAdd m j) ≤ 0 := hu (Fin.castAdd m j)
      have hrow :
          (M *ᵥ u) (Fin.castAdd m j) = -((u ᵥ* G) j) := by
        calc
          (M *ᵥ u) (Fin.castAdd m j) = ((-Gᵀ) *ᵥ u) j := by
            simp [M, Matrix.mulVec, Fin.addCases_left]
          _ = -((u ᵥ* G) j) := by
            simpa [Matrix.neg_mulVec, Matrix.mulVec_transpose]
      rw [hrow] at hj
      exact neg_nonpos.mp hj

/-- Helper for Theorem 8.18: the Benders dual cone inherits a polyhedron presentation from its
homogeneous matrix description. -/
lemma bendersDualCone_isPolyhedron
    (G : Matrix (Fin m) (Fin p) ℝ) :
    is_polyhedron (benders_dual_cone G) := by
  rcases (is_polyhedral_cone_iff.mp (bendersDualCone_isPolyhedralCone G)) with ⟨k, A, hA⟩
  exact ⟨k, A, 0, hA⟩

/-- Helper for Theorem 8.18: the Benders dual cone is pointed because no nonzero vector can be
both coordinatewise nonnegative and coordinatewise nonpositive. -/
lemma bendersDualCone_isPointed
    (G : Matrix (Fin m) (Fin p) ℝ) :
    is_pointed (benders_dual_cone G) := by
  rw [is_pointed_iff_eq_zero_of_mem_linealitySpace]
  intro u hu
  have hzero_mem : (0 : Fin m → ℝ) ∈ benders_dual_cone G := by
    exact (mem_benders_dual_cone_iff G 0).2 (by simp)
  have hu_mem : u ∈ benders_dual_cone G := by
    simpa using (mem_linealitySpace_iff.mp hu) hzero_mem (1 : ℝ)
  have hneg_mem : -u ∈ benders_dual_cone G := by
    simpa using (mem_linealitySpace_iff.mp hu) hzero_mem (-1 : ℝ)
  rcases (mem_benders_dual_cone_iff G u).1 hu_mem with ⟨hu_nonneg, _⟩
  rcases (mem_benders_dual_cone_iff G (-u)).1 hneg_mem with ⟨hneg_nonneg, _⟩
  ext i
  exact le_antisymm (by simpa using hneg_nonneg i) (hu_nonneg i)

/-- Helper for Theorem 8.18: the Benders dual cone is its own recession cone because it is a
cone closed under nonnegative scaling and addition. -/
lemma recessionCone_bendersDualCone_eq
    (G : Matrix (Fin m) (Fin p) ℝ) :
    recessionCone (benders_dual_cone G) = benders_dual_cone G := by
  ext u
  constructor
  · intro hu
    have hzero_mem : (0 : Fin m → ℝ) ∈ benders_dual_cone G := by
      exact (mem_benders_dual_cone_iff G 0).2 (by simp)
    simpa using (mem_recessionCone_iff.mp hu) hzero_mem 1 zero_le_one
  · intro hu
    rw [mem_recessionCone_iff]
    intro x hx a ha
    exact add_mem_bendersDualCone G hx (smul_mem_bendersDualCone G hu ha)

/-- Helper for Theorem 8.18: the origin is an extreme point of the Benders dual cone. -/
lemma zero_mem_extremePoints_bendersDualCone
    (G : Matrix (Fin m) (Fin p) ℝ) :
    (0 : Fin m → ℝ) ∈ (benders_dual_cone G).extremePoints ℝ := by
  refine (mem_extremePoints_iff_left).2 ?_
  refine ⟨(mem_benders_dual_cone_iff G 0).2 (by simp), ?_⟩
  intro y hy z hz hseg
  rcases mem_openSegment_iff_div.mp hseg with ⟨a, c, ha, hc, hcomb⟩
  let α' : ℝ := a / (a + c)
  let β' : ℝ := c / (a + c)
  have hα_pos : 0 < α' := by
    dsimp [α']
    positivity
  have hβ_pos : 0 < β' := by
    dsimp [β']
    positivity
  have hy_nonneg := (mem_benders_dual_cone_iff G y).1 hy |>.1
  have hz_nonneg := (mem_benders_dual_cone_iff G z).1 hz |>.1
  have hy_zero : y = 0 := by
    ext i
    have hcoord : α' * y i + β' * z i = 0 := by
      have hcoord' := congrArg (fun p : Fin m → ℝ ↦ p i) hcomb
      simpa [α', β', Pi.smul_apply] using hcoord'
    have hαy_nonpos : α' * y i ≤ 0 := by
      nlinarith [hcoord, mul_nonneg hβ_pos.le (hz_nonneg i)]
    have hαy_zero : α' * y i = 0 := by
      exact le_antisymm hαy_nonpos (mul_nonneg hα_pos.le (hy_nonneg i))
    have hyi_zero : y i = 0 := by
      exact (mul_eq_zero.mp hαy_zero).resolve_left hα_pos.ne'
    exact hyi_zero
  have hz_zero : z = 0 := by
    ext i
    have hcoord : α' * y i + β' * z i = 0 := by
      have hcoord' := congrArg (fun p : Fin m → ℝ ↦ p i) hcomb
      simpa [α', β', Pi.smul_apply] using hcoord'
    rw [hy_zero] at hcoord
    have hβz_zero : β' * z i = 0 := by
      simpa using hcoord
    exact (mul_eq_zero.mp hβz_zero).resolve_left hβ_pos.ne'
  simpa [hy_zero, hz_zero]

/-- Helper for Theorem 8.18: every extreme point of the Benders dual cone is the origin. -/
lemma extremePoint_eq_zero_of_mem_bendersDualCone
    (G : Matrix (Fin m) (Fin p) ℝ)
    {u : Fin m → ℝ}
    (hu : u ∈ (benders_dual_cone G).extremePoints ℝ) :
    u = 0 := by
  let C := benders_dual_cone G
  have hu_ext := mem_extremePoints_iff_left.mp hu
  have hu_mem : u ∈ C := hu_ext.1
  by_cases huzero : u = 0
  · exact huzero
  have hhalf_mem : ((1 / 2 : ℝ) • u) ∈ C :=
    smul_mem_bendersDualCone G hu_mem (by positivity)
  have hthreeHalf_mem : ((3 / 2 : ℝ) • u) ∈ C :=
    smul_mem_bendersDualCone G hu_mem (by positivity)
  have hu_open : u ∈ openSegment ℝ ((1 / 2 : ℝ) • u) ((3 / 2 : ℝ) • u) := by
    rw [mem_openSegment_iff_div]
    refine ⟨(1 : ℝ), (1 : ℝ), by positivity, by positivity, ?_⟩
    ext i
    simp [Pi.smul_apply]
    ring
  have hleft : ((1 / 2 : ℝ) • u) = u :=
    hu_ext.2 ((1 / 2 : ℝ) • u) hhalf_mem ((3 / 2 : ℝ) • u) hthreeHalf_mem hu_open
  have hsmul_zero : (((1 / 2 : ℝ) - 1) • u) = 0 := by
    simpa [sub_smul] using sub_eq_zero.mpr hleft
  rcases smul_eq_zero.mp hsmul_zero with hcoeff | huzero'
  · norm_num at hcoeff
  · exact huzero'

/-- Helper for Theorem 8.18: any extreme ray of the Benders dual cone belongs to the finitely
generated cone of the listed extreme-ray representatives. -/
lemma bendersDualConeExtremeRay_mem_listedCone
    (G : Matrix (Fin m) (Fin p) ℝ)
    {qJ : ℕ}
    (r : Fin qJ → Fin m → ℝ)
    (hrays : IsExtremeRayRepresentativeFamilyLocal (benders_dual_cone G) r)
    {g : Fin m → ℝ}
    (hg : IsExtremeRayOfPolyhedron (benders_dual_cone G) g) :
    g ∈ finitely_generated_cone r := by
  have hg_cone : IsExtremeRayOfCone (benders_dual_cone G) g := by
    rw [← recessionCone_bendersDualCone_eq G]
    exact (isExtremeRayOfPolyhedron_iff).1 hg
  rcases hrays.2.2 g hg_cone with ⟨t, hsame⟩
  have hlisted_mem : r t ∈ finitely_generated_cone r := by
    exact subset_cone (Set.range r) (Set.mem_range_self t)
  have hlisted_ne : r t ≠ 0 := extremeRay_ne_zero (hrays.1 t)
  exact sameRay_mem_finitelyGeneratedCone_ofMemOfNonzero hlisted_ne hsame hlisted_mem

/-- Helper for Theorem 8.18: any nonnegative combination of extreme rays of the Benders dual cone
lies in the finitely generated cone of the listed representatives. -/
lemma bendersDualConeExtremeRayCombination_mem_listedCone
    (G : Matrix (Fin m) (Fin p) ℝ)
    {qJ q' : ℕ}
    (r : Fin qJ → Fin m → ℝ)
    (hrays : IsExtremeRayRepresentativeFamilyLocal (benders_dual_cone G) r)
    (s : Fin q' → Fin m → ℝ)
    (hs : ∀ j : Fin q', IsExtremeRayOfPolyhedron (benders_dual_cone G) (s j))
    (coeff : Fin q' → ℝ)
    (hcoeff_nonneg : ∀ j : Fin q', 0 ≤ coeff j) :
    ∑ j, coeff j • s j ∈ finitely_generated_cone r := by
  induction q' with
  | zero =>
      refine mem_finitely_generated_cone_iff.mpr ?_
      refine ⟨0, ?_, ?_⟩
      · intro i
        simp
      · simp
  | succ q' ih =>
      let stail : Fin q' → Fin m → ℝ := fun j ↦ s j.succ
      let coeffTail : Fin q' → ℝ := fun j ↦ coeff j.succ
      have htail_extreme : ∀ j : Fin q', IsExtremeRayOfPolyhedron (benders_dual_cone G) (stail j) := by
        intro j
        exact hs j.succ
      have htail_nonneg : ∀ j : Fin q', 0 ≤ coeffTail j := by
        intro j
        exact hcoeff_nonneg j.succ
      have htail_mem :
          ∑ j, coeffTail j • stail j ∈ finitely_generated_cone r := by
        exact ih stail htail_extreme coeffTail htail_nonneg
      have hhead_mem : s 0 ∈ finitely_generated_cone r :=
        bendersDualConeExtremeRay_mem_listedCone G r hrays (hs 0)
      simpa [Fin.sum_univ_succ, stail, coeffTail, add_comm, add_left_comm, add_assoc] using
        finitely_generated_cone_add_smul_mem r htail_mem hhead_mem (hcoeff_nonneg 0)

/-- Helper for Theorem 8.18: every multiplier in the Benders dual cone lies in the finitely
generated cone of the listed extreme rays. -/
lemma bendersDualCone_mem_listedCone_ofExtremeRays
    (G : Matrix (Fin m) (Fin p) ℝ)
    {qJ : ℕ}
    (r : Fin qJ → Fin m → ℝ)
    (hrays : IsExtremeRayRepresentativeFamilyLocal (benders_dual_cone G) r) :
    ∀ v : Fin m → ℝ, v ∈ benders_dual_cone G → v ∈ finitely_generated_cone r := by
  intro v hv
  have hpolyhedron : is_polyhedron (benders_dual_cone G) := bendersDualCone_isPolyhedron G
  have hpointed : is_pointed (benders_dual_cone G) := bendersDualCone_isPointed G
  have hExtremePoints :
      (benders_dual_cone G).extremePoints ℝ = ({0} : Set (Fin m → ℝ)) := by
    ext u
    constructor
    · intro hu
      simp [extremePoint_eq_zero_of_mem_bendersDualCone G hu]
    · intro hu
      rcases Set.mem_singleton_iff.mp hu with rfl
      exact zero_mem_extremePoints_bendersDualCone G
  rcases exists_vertex_part_add_extreme_ray_part_of_mem_polyhedron
      hpolyhedron hpointed hv with
    ⟨vertexPart, rayPart, hvertexPart, hrayPart, hv_split⟩
  have hvertex_zero : vertexPart = 0 := by
    have hvertex_zero_hull :
        vertexPart ∈ convexHull ℝ ({0} : Set (Fin m → ℝ)) := by
      simpa [hExtremePoints] using hvertexPart
    simpa using hvertex_zero_hull
  have hray_cone :
      rayPart ∈ cone {g : Fin m → ℝ | IsExtremeRayOfPolyhedron (benders_dual_cone G) g} := by
    simpa [pointedCone_hull_eq_cone] using hrayPart
  rcases mem_cone_iff.mp hray_cone with ⟨q', s, hs_source, hs_comb⟩
  rcases isConicCombination_iff.mp hs_comb with ⟨coeff, hcoeff_nonneg, hs_repr⟩
  have hray_listed : rayPart ∈ finitely_generated_cone r := by
    simpa [hs_repr] using
      bendersDualConeExtremeRayCombination_mem_listedCone G r hrays s hs_source coeff
        hcoeff_nonneg
  have hv_eq : v = rayPart := by
    simpa [hvertex_zero] using hv_split
  simpa [hv_eq] using hray_listed

/-- Helper for Theorem 8.18: the Benders projection set is exactly the feasibility-cut set cut
out by any representative family of extreme rays of the dual cone. -/
lemma bendersProjectionSet_eq_feasibilityCutSet_ofExtremeRays
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    {qJ : ℕ}
    (r : Fin qJ → Fin m → ℝ)
    (hrays : IsExtremeRayRepresentativeFamilyLocal (benders_dual_cone G) r) :
    benders_projection_set A G b = benders_feasibility_cut_set A b r := by
  refine Set.Subset.antisymm
    (bendersProjectionSet_subset_feasibilityCutSet_ofExtremeRays A G b r hrays) ?_
  intro x hx
  rw [bendersProjectionSet_eq_allDualConeCuts A G b]
  intro v hv
  have hv_listed :
      v ∈ finitely_generated_cone r :=
    bendersDualCone_mem_listedCone_ofExtremeRays G r hrays v hv
  have hraywise :
      ∀ j : Fin qJ, r j ⬝ᵥ (A *ᵥ x) ≤ r j ⬝ᵥ b := by
    intro j
    have hj : 0 ≤ r j ⬝ᵥ benders_residual A b x :=
      (mem_benders_feasibility_cut_set_iff A b r x).1 hx j
    have hresidual :
        r j ⬝ᵥ benders_residual A b x = r j ⬝ᵥ b - r j ⬝ᵥ (A *ᵥ x) := by
      calc
        r j ⬝ᵥ benders_residual A b x = r j ⬝ᵥ (fun i ↦ b i - (A *ᵥ x) i) := rfl
        _ = r j ⬝ᵥ b - r j ⬝ᵥ (A *ᵥ x) := dotProduct_sub (r j) b (A *ᵥ x)
    rw [hresidual] at hj
    linarith
  have hmult :
      v ⬝ᵥ (A *ᵥ x) ≤ v ⬝ᵥ b :=
    finitelyGeneratedCone_evaluation_le_ofRaywiseLe A b r hraywise hv_listed
  have hresidual :
      v ⬝ᵥ benders_residual A b x = v ⬝ᵥ b - v ⬝ᵥ (A *ᵥ x) := by
    calc
      v ⬝ᵥ benders_residual A b x = v ⬝ᵥ (fun i ↦ b i - (A *ᵥ x) i) := rfl
      _ = v ⬝ᵥ b - v ⬝ᵥ (A *ᵥ x) := dotProduct_sub v b (A *ᵥ x)
  rw [hresidual]
  exact sub_nonneg.mpr hmult

/-- Helper for Theorem 8.18: the stacked matrix `[G ; -I]` is the canonical Chapter 3 owner for
the fixed-`x` Benders subproblem. -/
private abbrev bendersSubproblemMatrix
    (G : Matrix (Fin m) (Fin p) ℝ) :
    Matrix (Fin (m + p)) (Fin p) ℝ :=
  (Matrix.fromRows G (-(1 : Matrix (Fin p) (Fin p) ℝ))).submatrix
    finSumFinEquiv.symm (Equiv.refl _)

/-- Helper for Theorem 8.18: the stacked right-hand side `(rhs, 0)` of the fixed-`x` Benders
subproblem. -/
private abbrev bendersSubproblemRhs
    (rhs : Fin m → ℝ) :
    Fin (m + p) → ℝ :=
  Sum.elim rhs (fun _ ↦ 0) ∘ finSumFinEquiv.symm

/-- Helper for Theorem 8.18: the stacked matrix `[-I ; -Gᵀ]` presents the Benders dual
polyhedron as a standard polyhedron. -/
private abbrev bendersDualPolyhedronMatrix
    (G : Matrix (Fin m) (Fin p) ℝ) :
    Matrix (Fin (m + p)) (Fin m) ℝ :=
  (Matrix.fromRows (-(1 : Matrix (Fin m) (Fin m) ℝ)) (-Gᵀ)).submatrix
    finSumFinEquiv.symm (Equiv.refl _)

/-- Helper for Theorem 8.18: the stacked right-hand side `(0, -h)` of the Benders dual
polyhedron presentation. -/
private abbrev bendersDualPolyhedronRhs
    (h : Fin p → ℝ) :
    Fin (m + p) → ℝ :=
  Sum.elim (fun _ ↦ 0) (fun j ↦ -h j) ∘ finSumFinEquiv.symm

/-- Helper for Theorem 8.18: the stacked primal region `[G ; -I] y ≤ (rhs, 0)` is exactly the
subproblem feasible set `{y | G y ≤ rhs, y ≥ 0}`. -/
lemma mem_bendersSubproblemPrimalRegion_iff
    (G : Matrix (Fin m) (Fin p) ℝ)
    (rhs : Fin m → ℝ)
    (y : Fin p → ℝ) :
    y ∈ primal_feasible_region (bendersSubproblemMatrix G) (bendersSubproblemRhs (p := p) rhs) ↔
      y ∈ benders_subproblem_feasible_set G rhs := by
  let Araw : Matrix (Fin m ⊕ Fin p) (Fin p) ℝ :=
    Matrix.fromRows G (-(1 : Matrix (Fin p) (Fin p) ℝ))
  have hmul :=
    Matrix.submatrix_mulVec_equiv Araw y finSumFinEquiv.symm (Equiv.refl _)
  rw [mem_primal_feasible_region_iff, mem_benders_subproblem_feasible_set_iff]
  constructor
  · intro hy
    refine ⟨?_, ?_⟩
    · intro i
      -- Read the original `G y ≤ rhs` rows off the stacked system.
      have hrow := hy (finSumFinEquiv (Sum.inl i))
      have hEq :
          (bendersSubproblemMatrix G *ᵥ y) (finSumFinEquiv (Sum.inl i)) =
            (Araw *ᵥ y) (Sum.inl i) := by
        simpa [bendersSubproblemMatrix, Araw] using
          congrFun hmul (finSumFinEquiv (Sum.inl i))
      have hRhs :
          bendersSubproblemRhs (p := p) rhs (finSumFinEquiv (Sum.inl i)) = rhs i := by
        simp [bendersSubproblemRhs]
      rw [hEq, hRhs] at hrow
      simpa [Araw, Matrix.fromRows_mulVec] using hrow
    · intro j
      -- Read the nonnegativity rows `-y ≤ 0` off the stacked system.
      have hrow := hy (finSumFinEquiv (Sum.inr j))
      have hEq :
          (bendersSubproblemMatrix G *ᵥ y) (finSumFinEquiv (Sum.inr j)) =
            (Araw *ᵥ y) (Sum.inr j) := by
        simpa [bendersSubproblemMatrix, Araw] using
          congrFun hmul (finSumFinEquiv (Sum.inr j))
      have hRhs :
          bendersSubproblemRhs (p := p) rhs (finSumFinEquiv (Sum.inr j)) = 0 := by
        simp [bendersSubproblemRhs]
      rw [hEq, hRhs] at hrow
      have hneg : -y j ≤ 0 := by
        simpa [Araw, Matrix.fromRows_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec] using hrow
      exact neg_nonpos.mp hneg
  · rintro ⟨hyG, hyNonneg⟩
    intro row
    -- Evaluate the stacked row through `finSumFinEquiv`, then use the corresponding source row.
    rcases hsplit : finSumFinEquiv.symm row with i | j
    · have hr : row = finSumFinEquiv (Sum.inl i) := by
        simpa [hsplit] using (finSumFinEquiv.apply_symm_apply row).symm
      rw [hr]
      have hEq :
          (bendersSubproblemMatrix G *ᵥ y) (finSumFinEquiv (Sum.inl i)) =
            (Araw *ᵥ y) (Sum.inl i) := by
        simpa [bendersSubproblemMatrix, Araw] using
          congrFun hmul (finSumFinEquiv (Sum.inl i))
      have hRhs :
          bendersSubproblemRhs (p := p) rhs (finSumFinEquiv (Sum.inl i)) = rhs i := by
        simp [bendersSubproblemRhs]
      rw [hEq, hRhs]
      simpa [Araw, Matrix.fromRows_mulVec] using hyG i
    · have hr : row = finSumFinEquiv (Sum.inr j) := by
        simpa [hsplit] using (finSumFinEquiv.apply_symm_apply row).symm
      rw [hr]
      have hEq :
          (bendersSubproblemMatrix G *ᵥ y) (finSumFinEquiv (Sum.inr j)) =
            (Araw *ᵥ y) (Sum.inr j) := by
        simpa [bendersSubproblemMatrix, Araw] using
          congrFun hmul (finSumFinEquiv (Sum.inr j))
      have hRhs :
          bendersSubproblemRhs (p := p) rhs (finSumFinEquiv (Sum.inr j)) = 0 := by
        simp [bendersSubproblemRhs]
      rw [hEq, hRhs]
      have hneg : -y j ≤ 0 := neg_nonpos.mpr (hyNonneg j)
      simpa [Araw, Matrix.fromRows_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec] using hneg

/-- Helper for Theorem 8.18: the stacked system `[-I ; -Gᵀ] v ≤ (0, -h)` is exactly the Benders
dual polyhedron `Q = {v ≥ 0 | h ≤ v G}`. -/
lemma mem_bendersDualPolyhedron_iff_polyhedron
    (G : Matrix (Fin m) (Fin p) ℝ)
    (h : Fin p → ℝ)
    (v : Fin m → ℝ) :
    v ∈ polyhedron_le_set (bendersDualPolyhedronMatrix G) (bendersDualPolyhedronRhs (m := m) h) ↔
      v ∈ benders_dual_polyhedron G h := by
  let Araw : Matrix (Fin m ⊕ Fin p) (Fin m) ℝ :=
    Matrix.fromRows (-(1 : Matrix (Fin m) (Fin m) ℝ)) (-Gᵀ)
  have hmul :=
    Matrix.submatrix_mulVec_equiv Araw v finSumFinEquiv.symm (Equiv.refl _)
  rw [mem_polyhedron_le_set_iff, mem_benders_dual_polyhedron_iff]
  constructor
  · intro hv
    refine ⟨?_, ?_⟩
    · intro i
      -- The first block `-I v ≤ 0` is equivalent to coordinatewise nonnegativity of `v`.
      have hrow := hv (finSumFinEquiv (Sum.inl i))
      have hEq :
          (bendersDualPolyhedronMatrix G *ᵥ v) (finSumFinEquiv (Sum.inl i)) =
            (Araw *ᵥ v) (Sum.inl i) := by
        simpa [bendersDualPolyhedronMatrix, Araw] using
          congrFun hmul (finSumFinEquiv (Sum.inl i))
      have hRhs :
          bendersDualPolyhedronRhs (m := m) h (finSumFinEquiv (Sum.inl i)) = 0 := by
        simp [bendersDualPolyhedronRhs]
      rw [hEq, hRhs] at hrow
      have hneg : -v i ≤ 0 := by
        simpa [Araw, Matrix.fromRows_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec] using hrow
      exact neg_nonpos.mp hneg
    · intro j
      -- The second block `-Gᵀ v ≤ -h` is equivalent to `h ≤ v G`.
      have hrow := hv (finSumFinEquiv (Sum.inr j))
      have hEq :
          (bendersDualPolyhedronMatrix G *ᵥ v) (finSumFinEquiv (Sum.inr j)) =
            (Araw *ᵥ v) (Sum.inr j) := by
        simpa [bendersDualPolyhedronMatrix, Araw] using
          congrFun hmul (finSumFinEquiv (Sum.inr j))
      have hRhs :
          bendersDualPolyhedronRhs (m := m) h (finSumFinEquiv (Sum.inr j)) = -h j := by
        simp [bendersDualPolyhedronRhs]
      rw [hEq, hRhs] at hrow
      have hneg : -((v ᵥ* G) j) ≤ -h j := by
        simpa [Araw, Matrix.fromRows_mulVec, Matrix.neg_mulVec, Matrix.mulVec_transpose] using hrow
      linarith
  · rintro ⟨hvNonneg, hvDual⟩ row
    -- Evaluate the stacked row through `finSumFinEquiv`, then use the matching dual condition.
    rcases hsplit : finSumFinEquiv.symm row with i | j
    · have hr : row = finSumFinEquiv (Sum.inl i) := by
        simpa [hsplit] using (finSumFinEquiv.apply_symm_apply row).symm
      rw [hr]
      have hEq :
          (bendersDualPolyhedronMatrix G *ᵥ v) (finSumFinEquiv (Sum.inl i)) =
            (Araw *ᵥ v) (Sum.inl i) := by
        simpa [bendersDualPolyhedronMatrix, Araw] using
          congrFun hmul (finSumFinEquiv (Sum.inl i))
      have hRhs :
          bendersDualPolyhedronRhs (m := m) h (finSumFinEquiv (Sum.inl i)) = 0 := by
        simp [bendersDualPolyhedronRhs]
      rw [hEq, hRhs]
      have hneg : -v i ≤ 0 := neg_nonpos.mpr (hvNonneg i)
      simpa [Araw, Matrix.fromRows_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec] using hneg
    · have hr : row = finSumFinEquiv (Sum.inr j) := by
        simpa [hsplit] using (finSumFinEquiv.apply_symm_apply row).symm
      rw [hr]
      have hEq :
          (bendersDualPolyhedronMatrix G *ᵥ v) (finSumFinEquiv (Sum.inr j)) =
            (Araw *ᵥ v) (Sum.inr j) := by
        simpa [bendersDualPolyhedronMatrix, Araw] using
          congrFun hmul (finSumFinEquiv (Sum.inr j))
      have hRhs :
          bendersDualPolyhedronRhs (m := m) h (finSumFinEquiv (Sum.inr j)) = -h j := by
        simp [bendersDualPolyhedronRhs]
      rw [hEq, hRhs]
      have hneg : -((v ᵥ* G) j) ≤ -h j := by
        linarith [hvDual j]
      simpa [Araw, Matrix.fromRows_mulVec, Matrix.neg_mulVec, Matrix.mulVec_transpose] using hneg

/-- Helper for Theorem 8.18: the Benders dual polyhedron is exactly the stacked polyhedron
`[-I ; -Gᵀ] v ≤ (0, -h)`. -/
lemma bendersDualPolyhedron_eq_polyhedron_le_set
    (G : Matrix (Fin m) (Fin p) ℝ)
    (h : Fin p → ℝ) :
    benders_dual_polyhedron G h =
      polyhedron_le_set (bendersDualPolyhedronMatrix G) (bendersDualPolyhedronRhs (m := m) h) := by
  ext v
  simpa using (mem_bendersDualPolyhedron_iff_polyhedron G h v).symm

/-- Helper for Theorem 8.18: the Benders dual polyhedron is polyhedral through its stacked
matrix description. -/
lemma bendersDualPolyhedron_isPolyhedron
    (G : Matrix (Fin m) (Fin p) ℝ)
    (h : Fin p → ℝ) :
    is_polyhedron (benders_dual_polyhedron G h) := by
  refine ⟨m + p, bendersDualPolyhedronMatrix G, bendersDualPolyhedronRhs (m := m) h, ?_⟩
  exact bendersDualPolyhedron_eq_polyhedron_le_set G h

/-- Helper for Theorem 8.18: once the Benders dual polyhedron is nonempty, the `-I` block forces
its lineality space to be trivial, so the polyhedron is pointed. -/
lemma bendersDualPolyhedron_isPointed
    (G : Matrix (Fin m) (Fin p) ℝ)
    (h : Fin p → ℝ)
    (hQ : Set.Nonempty (benders_dual_polyhedron G h)) :
    is_pointed (benders_dual_polyhedron G h) := by
  have hlineality :
      linealitySpace
          (polyhedron_le_set (bendersDualPolyhedronMatrix G) (bendersDualPolyhedronRhs (m := m) h)) =
        {r : Fin m → ℝ | bendersDualPolyhedronMatrix G *ᵥ r = 0} :=
    polyhedron_linealitySpace_eq_kernel_set
      (bendersDualPolyhedronMatrix G)
      (bendersDualPolyhedronRhs (m := m) h)
      (by simpa [bendersDualPolyhedron_eq_polyhedron_le_set G h] using hQ)
  rw [is_pointed_iff_eq_zero_of_mem_linealitySpace]
  intro r hr
  have hrKernel : bendersDualPolyhedronMatrix G *ᵥ r = 0 := by
    simpa [bendersDualPolyhedron_eq_polyhedron_le_set G h, hlineality] using hr
  let Araw : Matrix (Fin m ⊕ Fin p) (Fin m) ℝ :=
    Matrix.fromRows (-(1 : Matrix (Fin m) (Fin m) ℝ)) (-Gᵀ)
  have hmul :=
    Matrix.submatrix_mulVec_equiv Araw r finSumFinEquiv.symm (Equiv.refl _)
  ext i
  -- The `-I` rows of the kernel equation force each coordinate to vanish.
  have hi :
      -r i = 0 := by
    have hcoord := congrFun hrKernel (finSumFinEquiv (Sum.inl i))
    have hEq :
        (bendersDualPolyhedronMatrix G *ᵥ r) (finSumFinEquiv (Sum.inl i)) =
          (Araw *ᵥ r) (Sum.inl i) := by
      simpa [bendersDualPolyhedronMatrix, Araw] using congrFun hmul (finSumFinEquiv (Sum.inl i))
    rw [hEq] at hcoord
    simpa [Araw, Matrix.fromRows_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec] using hcoord
  have hi' : r i = 0 := by linarith
  simpa using hi'

/-- Helper for Theorem 8.18: every extreme ray of the Benders dual polyhedron is a recession
direction of the stacked system, hence lies in the homogeneous cone `C = {v ≥ 0 | v G ≥ 0}`. -/
lemma mem_bendersDualCone_of_isExtremeRay_bendersDualPolyhedron
    (G : Matrix (Fin m) (Fin p) ℝ)
    (h : Fin p → ℝ)
    (hQ : Set.Nonempty (benders_dual_polyhedron G h))
    {g : Fin m → ℝ}
    (hg : IsExtremeRayOfPolyhedron (benders_dual_polyhedron G h) g) :
    g ∈ benders_dual_cone G := by
  have hrec :
      recessionCone (benders_dual_polyhedron G h) =
        {r : Fin m → ℝ | bendersDualPolyhedronMatrix G *ᵥ r ≤ 0} := by
    rw [bendersDualPolyhedron_eq_polyhedron_le_set G h]
    exact polyhedron_recessionCone_eq_homogeneous_solution_set
      (bendersDualPolyhedronMatrix G)
      (bendersDualPolyhedronRhs (m := m) h)
      (by simpa [bendersDualPolyhedron_eq_polyhedron_le_set G h] using hQ)
  have hgRows : bendersDualPolyhedronMatrix G *ᵥ g ≤ 0 := by
    simpa [hrec] using (isExtremeRayOfPolyhedron_mem_recessionCone hg)
  let Araw : Matrix (Fin m ⊕ Fin p) (Fin m) ℝ :=
    Matrix.fromRows (-(1 : Matrix (Fin m) (Fin m) ℝ)) (-Gᵀ)
  have hmul :=
    Matrix.submatrix_mulVec_equiv Araw g finSumFinEquiv.symm (Equiv.refl _)
  refine (mem_benders_dual_cone_iff G g).2 ⟨?_, ?_⟩
  · intro i
    -- The homogeneous `-I` rows show that every extreme recession ray is coordinatewise
    -- nonnegative.
    have hrow := hgRows (finSumFinEquiv (Sum.inl i))
    have hneg : -g i ≤ 0 := by
      have hEq :
          (bendersDualPolyhedronMatrix G *ᵥ g) (finSumFinEquiv (Sum.inl i)) =
            (Araw *ᵥ g) (Sum.inl i) := by
        simpa [bendersDualPolyhedronMatrix, Araw] using
          congrFun hmul (finSumFinEquiv (Sum.inl i))
      rw [hEq] at hrow
      simpa [Araw, Matrix.fromRows_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec] using hrow
    exact neg_nonpos.mp hneg
  · intro j
    -- The homogeneous `-Gᵀ` rows show that every extreme recession ray satisfies `g G ≥ 0`.
    have hrow := hgRows (finSumFinEquiv (Sum.inr j))
    have hneg : -((g ᵥ* G) j) ≤ 0 := by
      have hEq :
          (bendersDualPolyhedronMatrix G *ᵥ g) (finSumFinEquiv (Sum.inr j)) =
            (Araw *ᵥ g) (Sum.inr j) := by
        simpa [bendersDualPolyhedronMatrix, Araw] using
          congrFun hmul (finSumFinEquiv (Sum.inr j))
      rw [hEq] at hrow
      simpa [Araw, Matrix.fromRows_mulVec, Matrix.neg_mulVec, Matrix.mulVec_transpose] using hrow
    exact neg_nonpos.mp hneg

/-- Helper for Theorem 8.18: the Chapter 3 dual-objective owner for the stacked subproblem is
exactly the image of the Benders dual polyhedron under `v ↦ v (b - A x)`. -/
lemma bendersDualObjectiveValues_eq_dualPolyhedronImage
    (G : Matrix (Fin m) (Fin p) ℝ)
    (h : Fin p → ℝ)
    (rhs : Fin m → ℝ) :
    dual_objective_values (bendersSubproblemMatrix G) (bendersSubproblemRhs (p := p) rhs) h =
      (fun v : Fin m → ℝ ↦ v ⬝ᵥ rhs) '' benders_dual_polyhedron G h := by
  let stackedA := bendersSubproblemMatrix G
  let stackedb : Fin (m + p) → ℝ := bendersSubproblemRhs (p := p) rhs
  ext β
  constructor
  · rintro ⟨w, hw, rfl⟩
    let v : Fin m → ℝ := fun i ↦ w (Fin.castAdd p i)
    let μ : Fin p → ℝ := fun j ↦ w (Fin.natAdd m j)
    have hwData := (mem_dual_feasible_region_iff stackedA h w).mp hw
    have hvec :=
      Matrix.submatrix_vecMul_equiv
        (Matrix.fromRows G (-(1 : Matrix (Fin p) (Fin p) ℝ)))
        w
        finSumFinEquiv.symm
        (Equiv.refl _)
    have hwSplit :
        (w ∘ finSumFinEquiv) ᵥ* Matrix.fromRows G (-(1 : Matrix (Fin p) (Fin p) ℝ)) = h := by
      -- Undo the row reindexing once so the stacked dual equation can be read blockwise.
      ext j
      calc
        ((w ∘ finSumFinEquiv) ᵥ* Matrix.fromRows G (-(1 : Matrix (Fin p) (Fin p) ℝ))) j =
            (w ᵥ* stackedA) j := by
              symm
              simpa [stackedA] using congrFun hvec j
        _ = h j := congrFun hwData.1 j
    have hvμ : v ᵥ* G - μ = h := by
      -- Splitting the row equation isolates the slack block `μ = v G - h`.
      ext j
      have hvEq : ((w ∘ finSumFinEquiv) ∘ Sum.inl) = v := by
        funext i
        rfl
      have hμEq : ((w ∘ finSumFinEquiv) ∘ Sum.inr) = μ := by
        funext i
        rfl
      simpa [Matrix.vecMul_fromRows, hvEq, hμEq, Matrix.vecMul_neg, Matrix.vecMul_one,
        Pi.sub_apply] using congrFun hwSplit j
    have hv_mem : v ∈ benders_dual_polyhedron G h := by
      refine (mem_benders_dual_polyhedron_iff G h v).2 ⟨?_, ?_⟩
      · intro i
        exact hwData.2 (Fin.castAdd p i)
      · intro j
        have hμ_nonneg : 0 ≤ μ j := hwData.2 (Fin.natAdd m j)
        have hμ_eq : (v ᵥ* G) j - h j = μ j := by
          have hj : (v ᵥ* G) j - μ j = h j := by
            simpa [Pi.sub_apply] using congrFun hvμ j
          linarith
        have : 0 ≤ (v ᵥ* G) j - h j := by
          rw [hμ_eq]
          exact hμ_nonneg
        exact sub_nonneg.mp this
    let wRaw : Fin m ⊕ Fin p → ℝ := w ∘ finSumFinEquiv
    have hwRaw_split : Sum.elim v μ = wRaw := by
      funext i
      cases i <;> rfl
    have hwComp : w ∘ finSumFinEquiv = wRaw := by
      funext i
      cases i <;> rfl
    have hobj : w ⬝ᵥ stackedb = v ⬝ᵥ rhs := by
      -- The lower block of the right-hand side is zero, so only the `v` block contributes.
      calc
        w ⬝ᵥ stackedb = (w ∘ finSumFinEquiv) ⬝ᵥ Sum.elim rhs (fun _ ↦ 0) := by
          simpa [wRaw, stackedb, Function.comp] using
            (comp_equiv_symm_dotProduct w (Sum.elim rhs (fun _ ↦ 0)) finSumFinEquiv.symm).symm
        _ = wRaw ⬝ᵥ Sum.elim rhs (fun _ ↦ 0) := by rw [hwComp]
        _ = (Sum.elim v μ) ⬝ᵥ Sum.elim rhs (fun _ ↦ 0) := by rw [hwRaw_split.symm]
        _ = v ⬝ᵥ rhs + μ ⬝ᵥ (fun _ ↦ 0) := by rw [sumElim_dotProduct_sumElim]
        _ = v ⬝ᵥ rhs := by simp
    exact ⟨v, hv_mem, hobj.symm⟩
  · rintro ⟨v, hv, rfl⟩
    let μ : Fin p → ℝ := v ᵥ* G - h
    let wRaw : Fin m ⊕ Fin p → ℝ := Sum.elim v μ
    let w : Fin (m + p) → ℝ := wRaw ∘ finSumFinEquiv.symm
    have hvData := (mem_benders_dual_polyhedron_iff G h v).mp hv
    have hwSplit :
        wRaw ᵥ* Matrix.fromRows G (-(1 : Matrix (Fin p) (Fin p) ℝ)) = h := by
      -- The chosen slack block `μ = v G - h` makes the stacked dual equation hold exactly.
      ext j
      calc
        (wRaw ᵥ* Matrix.fromRows G (-(1 : Matrix (Fin p) (Fin p) ℝ))) j
            = (v ᵥ* G) j + (μ ᵥ* (-(1 : Matrix (Fin p) (Fin p) ℝ))) j := by
                simp [wRaw, Matrix.vecMul_fromRows]
        _ = (v ᵥ* G) j - μ j := by
              simp [Matrix.vecMul_neg, Matrix.vecMul_one, sub_eq_add_neg]
        _ = h j := by
              simp [μ, Pi.sub_apply]
    have hw_mem : w ∈ dual_feasible_region stackedA h := by
      rw [mem_dual_feasible_region_iff]
      refine ⟨?_, ?_⟩
      · -- Reindex the exact split equation back to the stacked row type.
        have hw_vec :=
          Matrix.submatrix_vecMul_equiv
            (Matrix.fromRows G (-(1 : Matrix (Fin p) (Fin p) ℝ)))
            w
            finSumFinEquiv.symm
            (Equiv.refl _)
        have hwComp : w ∘ finSumFinEquiv = wRaw := by
          funext i
          simp [w, wRaw]
        ext j
        have hEq :
            ((w ∘ finSumFinEquiv) ᵥ* Matrix.fromRows G (-(1 : Matrix (Fin p) (Fin p) ℝ))) j =
              (w ᵥ* stackedA) j := by
          symm
          simpa [stackedA] using congrFun hw_vec j
        calc
          (w ᵥ* stackedA) j
              = ((w ∘ finSumFinEquiv) ᵥ* Matrix.fromRows G (-(1 : Matrix (Fin p) (Fin p) ℝ))) j := by
                  symm
                  exact hEq
          _ = (wRaw ᵥ* Matrix.fromRows G (-(1 : Matrix (Fin p) (Fin p) ℝ))) j := by rw [hwComp]
          _ = h j := congrFun hwSplit j
      · intro row
        rcases hsplit : finSumFinEquiv.symm row with i | j
        · have hr : row = finSumFinEquiv (Sum.inl i) := by
            simpa [hsplit] using (finSumFinEquiv.apply_symm_apply row).symm
          rw [hr]
          simpa [w, wRaw] using hvData.1 i
        · have hr : row = finSumFinEquiv (Sum.inr j) := by
            simpa [hsplit] using (finSumFinEquiv.apply_symm_apply row).symm
          rw [hr]
          have hj : 0 ≤ μ j := by
            have hdual : h j ≤ (v ᵥ* G) j := hvData.2 j
            simpa [μ, Pi.sub_apply] using sub_nonneg.mpr hdual
          simpa [w, wRaw] using hj
    have hobj : w ⬝ᵥ stackedb = v ⬝ᵥ rhs := by
      -- The constructed slack block again disappears against the zero lower block of `stackedb`.
      have hwComp : w ∘ finSumFinEquiv = wRaw := by
        funext i
        simp [w, wRaw]
      calc
        w ⬝ᵥ stackedb = (w ∘ finSumFinEquiv) ⬝ᵥ Sum.elim rhs (fun _ ↦ 0) := by
          simpa [w, wRaw, stackedb, Function.comp] using
            (comp_equiv_symm_dotProduct w (Sum.elim rhs (fun _ ↦ 0)) finSumFinEquiv.symm).symm
        _ = wRaw ⬝ᵥ Sum.elim rhs (fun _ ↦ 0) := by rw [hwComp]
        _ = (Sum.elim v μ) ⬝ᵥ Sum.elim rhs (fun _ ↦ 0) := rfl
        _ = v ⬝ᵥ rhs + μ ⬝ᵥ (fun _ ↦ 0) := by rw [sumElim_dotProduct_sumElim]
        _ = v ⬝ᵥ rhs := by simp
    exact ⟨w, hw_mem, hobj⟩

/-- Helper for Theorem 8.18: for a feasible master point `x`, the fixed-`x` Benders subproblem
value is the minimum listed extreme-point cut value, hence equals the optimality-cut value. -/
lemma bendersSubproblemValue_eq_optimalityCutValue_ofExtremePoints
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (h : Fin p → ℝ)
    {qK : ℕ}
    (u : Fin qK → Fin m → ℝ)
    (hpoints : IsExtremePointRepresentativeFamily (benders_dual_polyhedron G h) u) :
    ∀ x : Fin n → ℝ,
      x ∈ benders_projection_set A G b →
        benders_subproblem_value G h (benders_residual A b x) =
          benders_optimality_cut_value A b u x := by
  classical
  intro x hx
  let rhs := benders_residual A b x
  let stackedA := bendersSubproblemMatrix G
  let stackedb : Fin (m + p) → ℝ := bendersSubproblemRhs (p := p) rhs
  have hP : Set.Nonempty (primal_feasible_region stackedA stackedb) := by
    rcases (mem_benders_projection_set_iff A G b x).mp hx with ⟨y, hy⟩
    exact ⟨y, (mem_bendersSubproblemPrimalRegion_iff G rhs y).2 hy⟩
  have hPrimalImage :
      ((fun y : Fin p → ℝ ↦ ((h ⬝ᵥ y : ℝ) : EReal)) '' benders_subproblem_feasible_set G rhs) =
        ((fun y : Fin p → ℝ ↦ ((h ⬝ᵥ y : ℝ) : EReal)) '' primal_feasible_region stackedA stackedb) := by
    -- The fixed-`x` Benders objective owner uses exactly the same real objective on the same
    -- feasible set once the stacked primal adapter is applied.
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, (mem_bendersSubproblemPrimalRegion_iff G rhs y).2 hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, (mem_bendersSubproblemPrimalRegion_iff G rhs y).1 hy, rfl⟩
  have hDualImage :
      ((fun w : Fin (m + p) → ℝ ↦ ((w ⬝ᵥ stackedb : ℝ) : EReal)) '' dual_feasible_region stackedA h) =
        ((fun v : Fin m → ℝ ↦ ((v ⬝ᵥ rhs : ℝ) : EReal)) '' benders_dual_polyhedron G h) := by
    -- Coercing the real dual-objective image to `EReal` preserves the exact image description.
    simpa [dual_objective_values, Set.image_image, stackedA, stackedb] using
      congrArg (Set.image (fun t : ℝ ↦ (t : EReal)))
        (bendersDualObjectiveValues_eq_dualPolyhedronImage G h rhs)
  have hdualEq :
      benders_subproblem_value G h rhs =
        sInf ((fun v : Fin m → ℝ ↦ ((v ⬝ᵥ rhs : ℝ) : EReal)) '' benders_dual_polyhedron G h) := by
    -- Remark 3.10 identifies the primal `EReal` supremum with the dual `EReal` infimum as soon
    -- as the primal region is nonempty, and the adapters rewrite both owners back to the
    -- Benders-side objects.
    calc
      benders_subproblem_value G h rhs
          = sSup ((fun y : Fin p → ℝ ↦ ((h ⬝ᵥ y : ℝ) : EReal)) '' primal_feasible_region stackedA stackedb) := by
              rw [benders_subproblem_value, hPrimalImage]
      _ = sInf
            ((fun w : Fin (m + p) → ℝ ↦ ((w ⬝ᵥ stackedb : ℝ) : EReal)) '' dual_feasible_region stackedA h) := by
              exact linear_program_duality_eq_except_both_empty stackedA stackedb h (Or.inl hP)
      _ = sInf ((fun v : Fin m → ℝ ↦ ((v ⬝ᵥ rhs : ℝ) : EReal)) '' benders_dual_polyhedron G h) := by
              rw [hDualImage]
  by_cases hQ : Set.Nonempty (benders_dual_polyhedron G h)
  · have hQ_polyhedron : is_polyhedron (benders_dual_polyhedron G h) :=
      bendersDualPolyhedron_isPolyhedron G h
    have hQ_pointed : is_pointed (benders_dual_polyhedron G h) :=
      bendersDualPolyhedron_isPointed G h hQ
    have hExtremeNonempty :
        ((benders_dual_polyhedron G h).extremePoints ℝ).Nonempty :=
      (polyhedron_extremePoints_nonempty_iff_is_pointed hQ_polyhedron hQ).2 hQ_pointed
    have hqK_nonzero : qK ≠ 0 := by
      -- A nonempty pointed polyhedron has an extreme point, so a representative family cannot be
      -- indexed by `Fin 0`.
      intro hqK_zero
      subst hqK_zero
      rcases hExtremeNonempty with ⟨vExt, hvExt⟩
      rcases hpoints.2.2 vExt hvExt with ⟨k, _⟩
      exact Fin.elim0 k
    have hExtremeRange :
        Set.range u = (benders_dual_polyhedron G h).extremePoints ℝ := by
      ext v
      constructor
      · rintro ⟨k, rfl⟩
        exact hpoints.1 k
      · intro hv
        rcases hpoints.2.2 v hv with ⟨k, rfl⟩
        exact Set.mem_range_self k
    let k0 : Fin qK := ⟨0, Nat.pos_of_ne_zero hqK_nonzero⟩
    obtain ⟨kMin, hkMin_mem, hkMin⟩ :=
      Finset.exists_min_image (Finset.univ : Finset (Fin qK)) (fun k : Fin qK ↦ u k ⬝ᵥ rhs)
        (by exact ⟨k0, by simp [k0]⟩)
    have hkMin_le : ∀ k : Fin qK, u kMin ⬝ᵥ rhs ≤ u k ⬝ᵥ rhs := by
      intro k
      exact hkMin k (by simp)
    have hkMin_extreme : u kMin ∈ (benders_dual_polyhedron G h).extremePoints ℝ := hpoints.1 kMin
    have hkMin_memQ : u kMin ∈ benders_dual_polyhedron G h :=
      (mem_extremePoints_iff_left.mp hkMin_extreme).1
    have hkMin_isLeast :
        IsLeast ((fun v : Fin m → ℝ ↦ v ⬝ᵥ rhs) '' benders_dual_polyhedron G h) (u kMin ⬝ᵥ rhs) := by
      refine ⟨?_, ?_⟩
      · -- The minimizing listed extreme point is itself a feasible dual point.
        exact Set.mem_image_of_mem (fun v : Fin m → ℝ ↦ v ⬝ᵥ rhs) hkMin_memQ
      · rintro _ ⟨v, hv, rfl⟩
        rcases exists_vertex_part_add_extreme_ray_part_of_mem_polyhedron
            hQ_polyhedron hQ_pointed hv with
          ⟨vertexPart, rayPart, hVertexHull, hRayHull, hv_split⟩
        have hRayNonneg : 0 ≤ rayPart ⬝ᵥ rhs := by
          -- Decompose the recession part into extreme rays and use `x ∈ benders_projection_set`
          -- to show every such ray has nonnegative value on the residual `rhs`.
          have hRayCone :
              rayPart ∈ cone {g : Fin m → ℝ |
                IsExtremeRayOfPolyhedron (benders_dual_polyhedron G h) g} := by
            simpa [pointedCone_hull_eq_cone] using hRayHull
          rcases mem_cone_iff.mp hRayCone with ⟨q, s, hs_source, hs_comb⟩
          rcases isConicCombination_iff.mp hs_comb with ⟨coeff, hcoeff_nonneg, hrepr⟩
          have hcutAll :
              ∀ g : Fin m → ℝ, g ∈ benders_dual_cone G → 0 ≤ g ⬝ᵥ rhs := by
            have hxCuts :
                x ∈ {x : Fin n → ℝ |
                  ∀ v : Fin m → ℝ, v ∈ benders_dual_cone G → 0 ≤ v ⬝ᵥ benders_residual A b x} := by
              simpa [bendersProjectionSet_eq_allDualConeCuts A G b] using hx
            simpa [rhs] using hxCuts
          calc
            0 ≤ ∑ j : Fin q, coeff j * (s j ⬝ᵥ rhs) := by
                  refine Finset.sum_nonneg ?_
                  intro j hj
                  exact mul_nonneg (hcoeff_nonneg j)
                    (hcutAll (s j)
                      (mem_bendersDualCone_of_isExtremeRay_bendersDualPolyhedron G h hQ
                        (hs_source j)))
            _ = (∑ j : Fin q, coeff j • s j) ⬝ᵥ rhs := by
                  calc
                    ∑ j : Fin q, coeff j * (s j ⬝ᵥ rhs)
                        = ∑ j : Fin q, (coeff j • s j) ⬝ᵥ rhs := by
                            simp [smul_eq_mul]
                    _ = (∑ j : Fin q, coeff j • s j) ⬝ᵥ rhs := by
                          symm
                          simpa using
                            (sum_dotProduct Finset.univ (fun j : Fin q ↦ coeff j • s j) rhs)
            _ = rayPart ⬝ᵥ rhs := by rw [hrepr]
        have hVertexListed : vertexPart ∈ convexHull ℝ (Set.range u) := by
          -- Replace the ambient extreme-point set by the listed representative family.
          rw [hExtremeRange]
          exact hVertexHull
        rcases mem_convexHull_range_iff_exists_barycentric_weights.mp hVertexListed with
          ⟨lam, hlam_nonneg, hlam_sum, hVertexRepr⟩
        have hkMin_le_vertex :
            u kMin ⬝ᵥ rhs ≤ vertexPart ⬝ᵥ rhs := by
          -- The minimum listed value is bounded above by any barycentric average of listed values.
          calc
            u kMin ⬝ᵥ rhs
                = (∑ k : Fin qK, lam k) * (u kMin ⬝ᵥ rhs) := by rw [hlam_sum, one_mul]
            _ = ∑ k : Fin qK, lam k * (u kMin ⬝ᵥ rhs) := by
                  simpa using
                    (Finset.sum_mul Finset.univ (fun k : Fin qK ↦ lam k) (u kMin ⬝ᵥ rhs))
            _ ≤ ∑ k : Fin qK, lam k * (u k ⬝ᵥ rhs) := by
                  refine Finset.sum_le_sum ?_
                  intro k hk
                  exact mul_le_mul_of_nonneg_left (hkMin_le k) (hlam_nonneg k)
            _ = (∑ k : Fin qK, lam k • u k) ⬝ᵥ rhs := by
                  calc
                    ∑ k : Fin qK, lam k * (u k ⬝ᵥ rhs)
                        = ∑ k : Fin qK, (lam k • u k) ⬝ᵥ rhs := by
                            simp [smul_eq_mul]
                    _ = (∑ k : Fin qK, lam k • u k) ⬝ᵥ rhs := by
                          symm
                          simpa using
                            (sum_dotProduct Finset.univ (fun k : Fin qK ↦ lam k • u k) rhs)
            _ = vertexPart ⬝ᵥ rhs := by rw [hVertexRepr]
        calc
          u kMin ⬝ᵥ rhs ≤ vertexPart ⬝ᵥ rhs := hkMin_le_vertex
          _ ≤ vertexPart ⬝ᵥ rhs + rayPart ⬝ᵥ rhs := by linarith
          _ = v ⬝ᵥ rhs := by
                calc
                  vertexPart ⬝ᵥ rhs + rayPart ⬝ᵥ rhs = (vertexPart + rayPart) ⬝ᵥ rhs := by
                    symm
                    exact add_dotProduct vertexPart rayPart rhs
                  _ = v ⬝ᵥ rhs := by rw [hv_split]
    have hkMin_isGreatest :
        IsGreatest (benders_optimality_cut_set A b u x) (u kMin ⬝ᵥ rhs) := by
      refine ⟨?_, ?_⟩
      · -- The minimum listed value satisfies every optimality cut.
        rw [mem_benders_optimality_cut_set_iff]
        intro k
        exact hkMin_le k
      · intro η hη
        -- Any feasible cut value is below each listed point, hence below the minimum one.
        exact (mem_benders_optimality_cut_set_iff A b u x η).mp hη kMin
    have hOptEq :
        benders_optimality_cut_value A b u x = ((u kMin ⬝ᵥ rhs : ℝ) : EReal) := by
      -- The optimality-cut owner is the `EReal` image of a real set with greatest element
      -- `u kMin ⋅ rhs`.
      exact (isGreatest_ereal_image_of_isGreatest hkMin_isGreatest).csSup_eq
    have hDualEqMin :
        sInf ((fun v : Fin m → ℝ ↦ ((v ⬝ᵥ rhs : ℝ) : EReal)) '' benders_dual_polyhedron G h) =
          ((u kMin ⬝ᵥ rhs : ℝ) : EReal) := by
      -- The minimum listed extreme point is also the least value on the whole dual polyhedron.
      simpa [Set.image_image] using (isLeast_ereal_image_of_isLeast hkMin_isLeast).csInf_eq
    calc
      benders_subproblem_value G h rhs =
          sInf ((fun v : Fin m → ℝ ↦ ((v ⬝ᵥ rhs : ℝ) : EReal)) '' benders_dual_polyhedron G h) :=
            hdualEq
      _ = ((u kMin ⬝ᵥ rhs : ℝ) : EReal) := hDualEqMin
      _ = benders_optimality_cut_value A b u x := hOptEq.symm
  · have hQempty : benders_dual_polyhedron G h = (∅ : Set (Fin m → ℝ)) := by
      rwa [Set.not_nonempty_iff_eq_empty] at hQ
    have hSubTop : benders_subproblem_value G h rhs = ⊤ := by
      -- When the dual polyhedron is empty, the dual `EReal` infimum is `⊤`, so the primal value
      -- is unbounded above by Remark 3.10.
      rw [hdualEq, hQempty]
      simp
    have hqK_zero : qK = 0 := by
      -- Otherwise some listed point would belong to the empty dual polyhedron.
      by_contra hqK_nonzero
      let k : Fin qK := ⟨0, Nat.pos_of_ne_zero hqK_nonzero⟩
      have hk_mem :
          u k ∈ benders_dual_polyhedron G h :=
        (mem_extremePoints_iff_left.mp (hpoints.1 k)).1
      simpa [hQempty] using hk_mem
    have hOptTop : benders_optimality_cut_value A b u x = ⊤ := by
      subst hqK_zero
      have hCuts :
          benders_optimality_cut_set A b u x = (Set.univ : Set ℝ) := by
        ext η
        rw [mem_benders_optimality_cut_set_iff]
        simp
      rw [benders_optimality_cut_value, Benders.optimalityCutValue]
      change sSup ((fun η : ℝ ↦ (η : EReal)) '' benders_optimality_cut_set A b u x) = ⊤
      rw [hCuts]
      exact ereal_sSup_eq_top_of_not_bddAbove (s := (Set.univ : Set ℝ)) (by
        intro hBdd
        rcases hBdd with ⟨M, hM⟩
        have hUpper := hM (by simp : M + 1 ∈ (Set.univ : Set ℝ))
        linarith)
    exact hSubTop.trans hOptTop.symm

/-- Theorem 8.18 (Benders). If the family `u` is a representative family of the extreme points
of the dual polyhedron `Q = {v ∈ ℝ^m_+ | v G ≥ h}` and the family `r` is a representative
family of the extreme rays of the cone `C = {v ∈ ℝ^m_+ | v G ≥ 0}`, then the mixed
problem (8.26) has the same value as the Benders master reformulation (8.27) with
optimality cuts
`η ≤ u^k (b - A x)` and feasibility cuts `r^j (b - A x) ≥ 0`. -/
theorem benders_original_value_eq_master_value
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (X : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    (h : Fin p → ℝ)
    {qK qJ : ℕ}
    (u : Fin qK → Fin m → ℝ)
    (r : Fin qJ → Fin m → ℝ)
    (hpoints :
      IsExtremePointRepresentativeFamily (benders_dual_polyhedron G h) u)
    (hrays : IsExtremeRayRepresentativeFamilyLocal (benders_dual_cone G) r) :
    benders_original_value A G b X c h = benders_master_value A b X u r c := by
  -- Route correction: the generic Benders bridge is now proved without the spurious finiteness
  -- hypothesis, so the remaining work is exactly to derive the feasibility-cut and optimality-cut
  -- equalities from `hrays` and `hpoints`.
  have hproj_subset :
      benders_projection_set A G b ⊆ benders_feasibility_cut_set A b r :=
    bendersProjectionSet_subset_feasibilityCutSet_ofExtremeRays A G b r hrays
  have hproj :
      benders_projection_set A G b = benders_feasibility_cut_set A b r := by
    -- The listed extreme rays generate the full dual cone, so the raywise cuts already imply all
    -- dual-cone inequalities.
    exact bendersProjectionSet_eq_feasibilityCutSet_ofExtremeRays A G b r hrays
  have hsubproblem :
      ∀ x : Fin n → ℝ,
        x ∈ benders_projection_set A G b →
          benders_subproblem_value G h (benders_residual A b x) =
            benders_optimality_cut_value A b u x := by
    -- Route correction: normalize the fixed-`x` subproblem to the stacked LP once, then identify
    -- the dual infimum with the minimum listed extreme-point cut value.
    exact bendersSubproblemValue_eq_optimalityCutValue_ofExtremePoints A G b h u hpoints
  -- Once the chapter-specific projection and subproblem identities are available, the generic
  -- Benders bridge finishes the value equality immediately.
  exact Benders.originalValue_eq_masterValue
    (benders_residual A b)
    G
    X
    (fun x ↦ c ⬝ᵥ x)
    h
    u
    r
    hproj
    hsubproblem

end Theorem818

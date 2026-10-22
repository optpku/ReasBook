/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_49
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Definition_7_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

/-- The support function of `C` evaluated at `u`, viewed as an `EReal` supremum of the inner
product functional on `C`. -/
noncomputable abbrev supportFunctionEReal (C : Set 𝓗) (u : 𝓗) : EReal :=
  sSup ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' C)

-- Proof sketch: unfold `supportFunctionEReal`.
/-- The support function `σ[C]` is the supremum of the image of `C` under the functional
`x ↦ ⟪x, u⟫`. -/
theorem supportFunctionEReal_eq_sSup_image (C : Set 𝓗) (u : 𝓗) :
    σ[C] u = sSup ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' C) := by
  -- This is exactly the defining expression of `supportFunctionEReal`.
  rfl

/-- The support halfspace of `C` in the direction `u` is the closed halfspace cut out by the
support-function bound `⟪x, u⟫ ≤ σ[C] u`. -/
def supportFunctionHalfspace (C : Set 𝓗) (u : 𝓗) : Set 𝓗 :=
  {x : 𝓗 | (⟪x, u⟫_ℝ : EReal) ≤ σ[C] u}

-- Proof sketch: unfold `supportFunctionHalfspace`.
/-- A point belongs to the support halfspace of `C` in the direction `u` exactly when its inner
product with `u` is bounded above by the support value `σ[C] u`. -/
theorem mem_supportFunctionHalfspace_iff (C : Set 𝓗) (u x : 𝓗) :
    x ∈ supportFunctionHalfspace C u ↔ (⟪x, u⟫_ℝ : EReal) ≤ σ[C] u := by
  -- Membership is the defining inequality of `supportFunctionHalfspace`.
  rfl

/-- Helper for Proposition 7.11: the textbook support function agrees with Chapter 3's
`innerSupremumOn`. -/
private theorem supportFunctionEReal_eq_innerSupremumOn (C : Set 𝓗) (u : 𝓗) :
    σ[C] u = innerSupremumOn C u := by
  rfl

/-- Helper for Proposition 7.11: every point of `C` lies in each support halfspace of `C`. -/
private theorem supportFunctionHalfspace_contains_set (C : Set 𝓗) (u : 𝓗) :
    C ⊆ supportFunctionHalfspace C u := by
  intro x hx
  -- The support value is the supremum of the image, so every image point lies below it.
  rw [mem_supportFunctionHalfspace_iff, supportFunctionEReal_eq_sSup_image]
  exact (isLUB_sSup _).1 ⟨x, hx, rfl⟩

/-- Helper for Proposition 7.11: nonempty sets have support values strictly above `⊥`. -/
private theorem supportFunctionEReal_ne_bot_of_nonempty {C : Set 𝓗} (hC_nonempty : C.Nonempty)
    (u : 𝓗) :
    σ[C] u ≠ ⊥ := by
  rcases hC_nonempty with ⟨x, hx⟩
  intro hσ_bot
  have hx_le : (⟪x, u⟫_ℝ : EReal) ≤ σ[C] u := by
    -- Realizing one point of the image gives a lower bound for the supremum.
    rw [supportFunctionEReal_eq_sSup_image]
    exact (isLUB_sSup _).1 ⟨x, hx, rfl⟩
  exact not_le_of_gt (EReal.bot_lt_coe _) (hσ_bot ▸ hx_le)

/-- Helper for Proposition 7.11: when the support value is finite, the support halfspace is the
usual real halfspace cut out by `x ↦ ⟪x, u⟫`. -/
private theorem supportFunctionHalfspace_eq_real_halfspace_of_nonempty_of_ne_top {C : Set 𝓗}
    (hC_nonempty : C.Nonempty) {u : 𝓗} (hσ_top : σ[C] u ≠ ⊤) :
    supportFunctionHalfspace C u = {x : 𝓗 | ⟪x, u⟫_ℝ ≤ (σ[C] u).toReal} := by
  have hσ_bot : σ[C] u ≠ ⊥ :=
    supportFunctionEReal_ne_bot_of_nonempty hC_nonempty u
  ext x
  constructor
  · intro hx
    -- Replace the finite `EReal` threshold by its real representative.
    rw [mem_supportFunctionHalfspace_iff] at hx
    have hx' : (⟪x, u⟫_ℝ : EReal) ≤ ((σ[C] u).toReal : EReal) := by
      simpa [EReal.coe_toReal hσ_top hσ_bot] using hx
    exact_mod_cast hx'
  · intro hx
    -- Cast the real inequality back to `EReal` and recover the original threshold.
    have hx' : (⟪x, u⟫_ℝ : EReal) ≤ ((σ[C] u).toReal : EReal) := by
      exact_mod_cast hx
    rw [mem_supportFunctionHalfspace_iff]
    simpa [EReal.coe_toReal hσ_top hσ_bot] using hx'

/-- Helper for Proposition 7.11: for nonempty `C`, each support halfspace is closed. -/
private theorem supportFunctionHalfspace_isClosed_of_nonempty {C : Set 𝓗} (hC_nonempty : C.Nonempty)
    (u : 𝓗) :
    IsClosed (supportFunctionHalfspace C u) := by
  by_cases hσ_top : σ[C] u = ⊤
  · -- If the support value is `⊤`, the defining inequality is automatic.
    have hset : supportFunctionHalfspace C u = Set.univ := by
      ext x
      simp [supportFunctionHalfspace, hσ_top]
    rw [hset]
    exact isClosed_univ
  · -- Otherwise rewrite to an ordinary closed halfspace for the continuous functional.
    rw [supportFunctionHalfspace_eq_real_halfspace_of_nonempty_of_ne_top hC_nonempty hσ_top]
    have hcont : Continuous (fun x : 𝓗 ↦ ⟪x, u⟫_ℝ) :=
      continuous_id.inner continuous_const
    simpa using isClosed_le hcont continuous_const

/-- Helper for Proposition 7.11: for nonempty `C`, each support halfspace is convex. -/
private theorem supportFunctionHalfspace_isConvex_of_nonempty {C : Set 𝓗} (hC_nonempty : C.Nonempty)
    (u : 𝓗) :
    Convex ℝ (supportFunctionHalfspace C u) := by
  by_cases hσ_top : σ[C] u = ⊤
  · -- If the support value is `⊤`, the support halfspace is all of `𝓗`.
    have hset : supportFunctionHalfspace C u = Set.univ := by
      ext x
      simp [supportFunctionHalfspace, hσ_top]
    rw [hset]
    exact convex_univ
  · -- Otherwise rewrite to the standard convex linear halfspace.
    rw [supportFunctionHalfspace_eq_real_halfspace_of_nonempty_of_ne_top hC_nonempty hσ_top]
    have hlinear : IsLinearMap ℝ (fun x : 𝓗 ↦ ⟪x, u⟫_ℝ) := by
      refine ⟨?_, ?_⟩
      · intro x y
        rw [inner_add_left]
      · intro a x
        simpa using inner_smul_real_left x u a
    simpa using convex_halfSpace_le hlinear (σ[C] u).toReal

/-- Helper for Proposition 7.11: the support function is monotone under set inclusion. -/
private theorem supportFunctionEReal_mono {C D : Set 𝓗} (hCD : C ⊆ D) (u : 𝓗) :
    σ[C] u ≤ σ[D] u := by
  -- Every value attained on `C` also appears in the image of `D`.
  rw [supportFunctionEReal_eq_sSup_image, supportFunctionEReal_eq_sSup_image]
  refine (isLUB_sSup _).2 ?_
  rintro _ ⟨x, hx, rfl⟩
  exact (isLUB_sSup _).1 ⟨x, hCD hx, rfl⟩

section ProjectionSeparation

variable {S : Set 𝓗}
variable (hS_nonempty : S.Nonempty) (hS_closed : IsClosed S) (hS_convex : Convex ℝ S)

local notation "P" =>
  projectionPoint S (isChebyshev_of_nonempty_isClosed_convex hS_nonempty hS_closed hS_convex)

/-- Helper for Proposition 7.11: the projection variational inequality bounds every support value
of a closed convex set by the value at the projection point. -/
private lemma projectionPoint_support_upper_bound {x y : 𝓗} (hy : y ∈ S) :
    ⟪y, x - P x⟫_ℝ ≤ ⟪P x, x - P x⟫_ℝ := by
  -- Read the pointwise projection inequality off the characterization of `projectionPoint`.
  have hprojection :
      P x ∈ S ∧ ∀ z ∈ S, ⟪z - P x, x - P x⟫_ℝ ≤ 0 := by
    exact
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        hS_nonempty hS_closed hS_convex).mp rfl
  have hy_nonpos : ⟪y - P x, x - P x⟫_ℝ ≤ 0 := hprojection.2 y hy
  have hrewrite :
      ⟪y - P x, x - P x⟫_ℝ = ⟪y, x - P x⟫_ℝ - ⟪P x, x - P x⟫_ℝ := by
    rw [inner_sub_left]
  rw [hrewrite] at hy_nonpos
  linarith

/-- Helper for Proposition 7.11: a pointwise upper bound on `⟪y, u⟫` over `S` bounds
`innerSupremumOn S u`. -/
private lemma innerSupremumOn_le_of_forall_inner_le {u : 𝓗} {a : ℝ}
    (hbound : ∀ y ∈ S, ⟪y, u⟫_ℝ ≤ a) :
    innerSupremumOn S u ≤ (a : EReal) := by
  -- Rewrite the support value as a supremum and show that `a` is an upper bound.
  rw [innerSupremumOn_eq_sSup_image]
  refine (isLUB_sSup _).2 ?_
  rintro _ ⟨y, hy, rfl⟩
  exact show ((⟪y, u⟫_ℝ : EReal) ≤ (a : EReal)) by
    exact_mod_cast hbound y hy

/-- Helper for Proposition 7.11: a point outside a closed convex set differs from its projection. -/
private lemma projectionPoint_residual_ne_zero {x : 𝓗} (hx : x ∉ S) :
    x - P x ≠ 0 := by
  -- If the residual vanished, `x` would equal its projection, hence lie in `S`.
  intro hu_zero
  have hPx_mem : P x ∈ S := by
    exact
      projectionPoint_mem S
        (isChebyshev_of_nonempty_isClosed_convex hS_nonempty hS_closed hS_convex) x
  have hx_eq : x = P x := sub_eq_zero.mp hu_zero
  exact hx (hx_eq.symm ▸ hPx_mem)

/-- Helper for Proposition 7.11: the projection residual contributes a strictly positive inner
product gap between the projection point and the original point. -/
private lemma projectionPoint_support_strict_gap {x : 𝓗} (hx : x ∉ S) :
    ⟪P x, x - P x⟫_ℝ < ⟪x, x - P x⟫_ℝ := by
  -- The extra term is `‖x - P x‖^2`, which is positive away from the set.
  have hu_ne : x - P x ≠ 0 :=
    projectionPoint_residual_ne_zero hS_nonempty hS_closed hS_convex hx
  have hnorm_sq_pos : 0 < ‖x - P x‖ ^ 2 := by
    exact pow_pos (norm_pos_iff.mpr hu_ne) 2
  have hlt :
      ⟪P x, x - P x⟫_ℝ < ⟪P x, x - P x⟫_ℝ + ‖x - P x‖ ^ 2 := by
    linarith
  calc
    ⟪P x, x - P x⟫_ℝ < ⟪P x, x - P x⟫_ℝ + ‖x - P x‖ ^ 2 := hlt
    _ = ⟪x, x - P x⟫_ℝ := by
        calc
          ⟪P x, x - P x⟫_ℝ + ‖x - P x‖ ^ 2
              = ⟪P x, x - P x⟫_ℝ + ⟪x - P x, x - P x⟫_ℝ := by
                  rw [real_inner_self_eq_norm_sq]
          _ = ⟪P x + (x - P x), x - P x⟫_ℝ := by
                rw [inner_add_left]
          _ = ⟪x, x - P x⟫_ℝ := by
                congr 1
                abel_nf

/-- Helper for Proposition 7.11: a point outside a nonempty closed convex set admits a direction
whose support value on the set is strictly below its inner product at that point. -/
private theorem exists_nonzero_innerSupremumOn_lt_inner_of_nonempty_isClosed_convex_of_not_mem
    (hS_nonempty : S.Nonempty) (hS_closed : IsClosed S) (hS_convex : Convex ℝ S)
    {x : 𝓗} (hx : x ∉ S) :
    ∃ u : 𝓗,
      u ≠ 0 ∧ innerSupremumOn S u < (⟪x, u⟫_ℝ : EReal) := by
  -- Use the projection residual `u := x - P x` as the separating direction.
  let p :=
    projectionPoint S (isChebyshev_of_nonempty_isClosed_convex hS_nonempty hS_closed hS_convex) x
  let u := x - p
  have hu_ne : u ≠ 0 := by
    simpa [u, p] using
      projectionPoint_residual_ne_zero hS_nonempty hS_closed hS_convex hx
  refine ⟨u, hu_ne, ?_⟩
  have hsup_le :
      innerSupremumOn S u ≤ (⟪p, u⟫_ℝ : EReal) := by
    -- The projection inequality bounds every support value by the projection value.
    refine innerSupremumOn_le_of_forall_inner_le (S := S) fun y hy ↦ ?_
    simpa [u, p] using
      projectionPoint_support_upper_bound hS_nonempty hS_closed hS_convex hy
  have hgap : ⟪p, u⟫_ℝ < ⟪x, u⟫_ℝ := by
    -- The residual contributes the strictly positive term `‖x - P x‖^2`.
    simpa [u, p] using
      projectionPoint_support_strict_gap hS_nonempty hS_closed hS_convex hx
  exact lt_of_le_of_lt hsup_le (by exact_mod_cast hgap)

end ProjectionSeparation

-- Proof sketch: each `supportFunctionHalfspace C u` is a closed convex halfspace containing `C`,
-- so `closure (convexHull ℝ C)` is contained in their intersection by minimality of the closed
-- convex hull. For the reverse inclusion, project a point in the intersection onto
-- `closure (convexHull ℝ C)` and use the support-function inequality for the residual vector to
-- force equality with its projection.
/-- Proposition 7.11: the closed convex hull of `C` is the intersection of the support halfspaces
cut out by the support function `σ[C]`. -/
theorem closure_convexHull_eq_iInter_supportFunctionHalfspace (C : Set 𝓗) :
    closure (convexHull ℝ C) = ⋂ u : 𝓗, supportFunctionHalfspace C u := by
  by_cases hC_empty : C = ∅
  · -- In the empty case, the support value is `⊥`, so every support halfspace is empty.
    subst hC_empty
    ext x
    simp [supportFunctionHalfspace, supportFunctionEReal_eq_sSup_image]
  · let S : Set 𝓗 := closedConvexHull ℝ C
    have hC_nonempty : C.Nonempty := Set.nonempty_iff_ne_empty.mpr hC_empty
    have hS_nonempty : S.Nonempty :=
      hC_nonempty.mono (by
        intro x hx
        exact subset_closedConvexHull hx)
    have hS_closed : IsClosed S := by
      -- `closedConvexHull` is closed by construction.
      simpa [S] using isClosed_closedConvexHull (𝕜 := ℝ) (s := C)
    have hS_convex : Convex ℝ S := by
      -- `closedConvexHull` is convex by construction.
      simpa [S] using convex_closedConvexHull (𝕜 := ℝ) (s := C)
    rw [← closedConvexHull_eq_closure_convexHull]
    apply Set.Subset.antisymm
    · intro x hxS
      rw [Set.mem_iInter]
      intro u
      -- Minimality of the closed convex hull gives the easy inclusion into each halfspace.
      have hSu : S ⊆ supportFunctionHalfspace C u := by
        refine closedConvexHull_min ?_ ?_ ?_
        · exact supportFunctionHalfspace_contains_set C u
        · exact supportFunctionHalfspace_isConvex_of_nonempty hC_nonempty u
        · exact supportFunctionHalfspace_isClosed_of_nonempty hC_nonempty u
      exact hSu hxS
    · intro x hxInter
      by_contra hxS
      -- Strong separation of `x` from the closed convex hull yields a violating direction.
      rcases exists_nonzero_innerSupremumOn_lt_inner_of_nonempty_isClosed_convex_of_not_mem
          (S := S) hS_nonempty hS_closed hS_convex hxS with ⟨u, _, hsep⟩
      have hx_half : x ∈ supportFunctionHalfspace C u := by
        exact Set.mem_iInter.mp hxInter u
      have hx_le : (⟪x, u⟫_ℝ : EReal) ≤ σ[C] u := by
        exact (mem_supportFunctionHalfspace_iff C u x).mp hx_half
      have hmono : σ[C] u ≤ σ[S] u :=
        supportFunctionEReal_mono (C := C) (D := S)
          (by
            intro y hy
            exact subset_closedConvexHull hy) u
      have hsep' : σ[S] u < (⟪x, u⟫_ℝ : EReal) := by
        -- Translate the Chapter 3 separation inequality to the local support notation.
        rw [supportFunctionEReal_eq_innerSupremumOn]
        exact hsep
      exact (not_lt_of_ge (le_trans hx_le hmono)) hsep'

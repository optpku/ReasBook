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

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

section

variable {C : Set 𝓗}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "P" =>
  projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)

/-- Helper for Theorem 3.50: the projection variational inequality rewrites to a support bound at
the projection point. -/
private lemma projectionPoint_support_upper_bound {x y : 𝓗} (hy : y ∈ C) :
    ⟪y, x - P x⟫_ℝ ≤ ⟪P x, x - P x⟫_ℝ := by
  -- Read off the projection inequality at `P x`.
  have hprojection :
      P x ∈ C ∧ ∀ z ∈ C, ⟪z - P x, x - P x⟫_ℝ ≤ 0 := by
    exact
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex).mp rfl
  have hy_nonpos : ⟪y - P x, x - P x⟫_ℝ ≤ 0 := hprojection.2 y hy
  have hrewrite :
      ⟪y - P x, x - P x⟫_ℝ = ⟪y, x - P x⟫_ℝ - ⟪P x, x - P x⟫_ℝ := by
    rw [inner_sub_left]
  rw [hrewrite] at hy_nonpos
  linarith

omit [CompleteSpace 𝓗] in
/-- Helper for Theorem 3.50: a pointwise upper bound on `⟪y, u⟫` over `C` bounds
`innerSupremumOn C u`. -/
private lemma innerSupremumOn_le_of_forall_inner_le {u : 𝓗} {a : ℝ}
    (hbound : ∀ y ∈ C, ⟪y, u⟫_ℝ ≤ a) :
    innerSupremumOn C u ≤ (a : EReal) := by
  -- Rewrite the support functional as the supremum of the image and show `a` is an upper bound.
  rw [innerSupremumOn_eq_sSup_image]
  refine (isLUB_sSup _).2 ?_
  rintro _ ⟨y, hy, rfl⟩
  exact show ((⟪y, u⟫_ℝ : EReal) ≤ (a : EReal)) by
    exact_mod_cast hbound y hy

/-- Helper for Theorem 3.50: if `x ∉ C`, then the residual from `x` to its projection on `C` is
nonzero. -/
private lemma projectionPoint_residual_ne_zero {x : 𝓗} (hx : x ∉ C) :
    x - P x ≠ 0 := by
  -- Otherwise `x` would coincide with its projection, which lies in `C`.
  intro hu_zero
  have hPx_mem : P x ∈ C := by
    exact
      projectionPoint_mem C
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x
  have hx_eq : x = P x := sub_eq_zero.mp hu_zero
  exact hx (hx_eq.symm ▸ hPx_mem)

/-- Helper for Theorem 3.50: the projection residual creates a strict gap between evaluation at
the projection point and evaluation at `x`. -/
private lemma projectionPoint_support_strict_gap {x : 𝓗} (hx : x ∉ C) :
    ⟪P x, x - P x⟫_ℝ < ⟪x, x - P x⟫_ℝ := by
  -- The point `x` decomposes as its projection plus the residual, and the extra term is `‖u‖^2`.
  have hu_ne : x - P x ≠ 0 :=
    projectionPoint_residual_ne_zero hC_nonempty hC_closed hC_convex hx
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

-- Proof sketch: let `p := projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty
-- hC_closed hC_convex) x` and set `u := x - p`. Since `x ∉ C`, one has `u ≠ 0`. The variational
-- characterization of projections gives `⟪y - p, x - p⟫_ℝ ≤ 0` for every `y ∈ C`, which rewrites
-- to `⟪y, u⟫_ℝ ≤ ⟪p, u⟫_ℝ < ⟪x, u⟫_ℝ`; this yields strict separation of `C` and `{x}`.
/-- Theorem 3.50: a point outside a nonempty closed convex set is strongly separated from that set
in the orientation used by `AreStronglySeparated C ({x} : Set 𝓗)`. -/
theorem areStronglySeparated_singleton_of_nonempty_isClosed_convex_of_not_mem {C : Set 𝓗}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) {x : 𝓗}
    (hx : x ∉ C) :
    AreStronglySeparated C ({x} : Set 𝓗) := by
  -- Use the projection residual as the separating normal vector.
  let p :=
    projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x
  let u := x - p
  have hu_ne : u ≠ 0 := by
    simpa [u, p] using
      projectionPoint_residual_ne_zero hC_nonempty hC_closed hC_convex hx
  refine ⟨u, hu_ne, ?_⟩
  have hsup_le :
      innerSupremumOn C u ≤ (⟪p, u⟫_ℝ : EReal) := by
    -- The variational inequality bounds every support value by the value at the projection point.
    refine innerSupremumOn_le_of_forall_inner_le fun y hy ↦ ?_
    simpa [u, p] using
      projectionPoint_support_upper_bound hC_nonempty hC_closed hC_convex hy
  have hgap : ⟪p, u⟫_ℝ < ⟪x, u⟫_ℝ := by
    -- The residual contributes the strictly positive term `‖x - P x‖^2`.
    simpa [u, p] using
      projectionPoint_support_strict_gap hC_nonempty hC_closed hC_convex hx
  rw [innerInfimumOn_singleton x u]
  exact lt_of_le_of_lt hsup_le (by exact_mod_cast hgap)

-- Proof sketch: let `p := projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty
-- hC_closed hC_convex) x` and `u := x - p`. Since `x ∉ C`, one has `u ≠ 0`. For every `y ∈ C`,
-- the projection inequality `⟪y - p, x - p⟫_ℝ ≤ 0` implies
-- `⟪y - x, u⟫_ℝ = ⟪y - p, u⟫_ℝ - ‖u‖ ^ 2 ≤ -‖u‖ ^ 2 < 0`; equivalently
-- `innerSupremumOn C u < ⟪x, u⟫_ℝ`.
/-- Theorem 3.50: if `C` is a nonempty closed convex subset of a real Hilbert space and `x ∉ C`,
then there is a nonzero vector `u` with `sup_{y ∈ C} ⟪y, u⟫_ℝ < ⟪x, u⟫_ℝ`, equivalently
`sup_{y ∈ C} ⟪y - x, u⟫_ℝ < 0`. -/
theorem exists_nonzero_innerSupremumOn_lt_inner_of_nonempty_isClosed_convex_of_not_mem
    {C : Set 𝓗} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {x : 𝓗} (hx : x ∉ C) :
    ∃ u : 𝓗,
      u ≠ 0 ∧ innerSupremumOn C u < (⟪x, u⟫_ℝ : EReal) := by
  rcases areStronglySeparated_singleton_of_nonempty_isClosed_convex_of_not_mem
      hC_nonempty hC_closed hC_convex hx with ⟨u, hu, hsep⟩
  exact ⟨u, hu, by simpa using hsep⟩

end

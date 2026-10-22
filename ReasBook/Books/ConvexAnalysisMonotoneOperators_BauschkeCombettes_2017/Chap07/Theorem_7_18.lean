/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Definition_7_14
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Proposition_7_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

namespace Set

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

section ProjectionSeparation

variable {S : Set 𝓗}
variable (hS_nonempty : S.Nonempty) (hS_closed : IsClosed S) (hS_convex : Convex ℝ S)

local notation "P" =>
  projectionPoint S (isChebyshev_of_nonempty_isClosed_convex hS_nonempty hS_closed hS_convex)

/-- Helper for Theorem 7.18: the projection variational inequality gives a support bound at the
projection point. -/
private lemma projection_support_upper_bound {x y : 𝓗} (hy : y ∈ S) :
    ⟪y, x - P x⟫_ℝ ≤ ⟪P x, x - P x⟫_ℝ := by
  -- Read off the pointwise projection inequality at the Chebyshev projection.
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

/-- Helper for Theorem 7.18: a point outside a closed convex set differs from its projection by a
nonzero residual. -/
private lemma projection_residual_ne_zero {x : 𝓗} (hx : x ∉ S) :
    x - P x ≠ 0 := by
  -- Otherwise `x` would equal its projection, but the projection lies in `S`.
  intro hu_zero
  have hPx_mem : P x ∈ S := by
    exact
      projectionPoint_mem S
        (isChebyshev_of_nonempty_isClosed_convex hS_nonempty hS_closed hS_convex) x
  have hx_eq : x = P x := sub_eq_zero.mp hu_zero
  exact hx (hx_eq.symm ▸ hPx_mem)

/-- Helper for Theorem 7.18: the projection residual creates a strict gap between evaluation at
the projection point and at the external point. -/
private lemma projection_support_strict_gap {x : 𝓗} (hx : x ∉ S) :
    ⟪P x, x - P x⟫_ℝ < ⟪x, x - P x⟫_ℝ := by
  -- The extra term is `‖x - P x‖ ^ 2`, which is strictly positive off the set.
  have hu_ne : x - P x ≠ 0 :=
    projection_residual_ne_zero hS_nonempty hS_closed hS_convex hx
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

/-- Helper for Theorem 7.18: a point outside a nonempty closed convex set admits a separating
direction whose support value is strictly smaller than its evaluation at that point. -/
private theorem exists_nonzero_innerSupremumOn_lt_inner_of_nonempty_isClosed_convex_of_not_mem
    (hS_nonempty : S.Nonempty) (hS_closed : IsClosed S) (hS_convex : Convex ℝ S)
    {x : 𝓗} (hx : x ∉ S) :
    ∃ u : 𝓗,
      u ≠ 0 ∧ innerSupremumOn S u < (⟪x, u⟫_ℝ : EReal) := by
  -- Use the projection residual as the separating direction.
  let p :=
    projectionPoint S (isChebyshev_of_nonempty_isClosed_convex hS_nonempty hS_closed hS_convex) x
  let u := x - p
  have hu_ne : u ≠ 0 := by
    simpa [u, p] using
      projection_residual_ne_zero hS_nonempty hS_closed hS_convex hx
  refine ⟨u, hu_ne, ?_⟩
  have hsup_le :
      innerSupremumOn S u ≤ (⟪p, u⟫_ℝ : EReal) := by
    -- The projection inequality bounds every support value by the value at the projection point.
    rw [innerSupremumOn_eq_sSup_image]
    refine sSup_le ?_
    rintro _ ⟨y, hy, rfl⟩
    exact show ((⟪y, u⟫_ℝ : EReal) ≤ (⟪p, u⟫_ℝ : EReal)) by
      exact_mod_cast (projection_support_upper_bound hS_nonempty hS_closed hS_convex hy)
  have hgap : ⟪p, u⟫_ℝ < ⟪x, u⟫_ℝ := by
    -- The residual contributes the strictly positive term `‖x - P x‖^2`.
    simpa [u, p] using
      projection_support_strict_gap hS_nonempty hS_closed hS_convex hx
  exact lt_of_le_of_lt hsup_le (by exact_mod_cast hgap)

end ProjectionSeparation

/-- Helper for Theorem 7.18: the origin belongs to every polar set. -/
private lemma zero_mem_polarSet (C : Set 𝓗) :
    (0 : 𝓗) ∈ Cᵒ⊙ := by
  -- The inner product with the origin vanishes, so the defining inequalities are automatic.
  rw [mem_polarSet_iff_forall_inner_le_one]
  intro x hx
  simp

/-- Helper for Theorem 7.18: the polar set is closed. -/
private lemma polarSet_isClosed (C : Set 𝓗) :
    IsClosed (Cᵒ⊙) := by
  have hrepr :
      Cᵒ⊙ = ⋂ x : C, {u : 𝓗 | ⟪(x : 𝓗), u⟫_ℝ ≤ 1} := by
    -- Rewrite polar membership as the family of halfspace inequalities indexed by `C`.
    ext u
    simp [mem_polarSet_iff_forall_inner_le_one]
  rw [hrepr]
  -- Each defining halfspace is closed because `u ↦ ⟪x, u⟫` is continuous.
  refine isClosed_iInter fun x ↦ ?_
  simpa using isClosed_le (continuous_const.inner continuous_id) continuous_const

/-- Helper for Theorem 7.18: the polar set is convex. -/
private lemma polarSet_convex (C : Set 𝓗) :
    Convex ℝ (Cᵒ⊙) := by
  have hrepr :
      Cᵒ⊙ = ⋂ x : C, {u : 𝓗 | ⟪(x : 𝓗), u⟫_ℝ ≤ 1} := by
    -- The same halfspace representation reduces convexity to convexity of each halfspace.
    ext u
    simp [mem_polarSet_iff_forall_inner_le_one]
  rw [hrepr]
  refine convex_iInter fun x ↦ ?_
  intro u hu v hv a b ha hb hab
  -- Affine combinations preserve the linear upper bound on each halfspace.
  dsimp at hu hv ⊢
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  nlinarith

/-- Helper for Theorem 7.18: every point of `C`, and also the origin, lies in the bipolar. -/
private lemma union_singleton_zero_subset_polarSet_polarSet (C : Set 𝓗) :
    C ∪ ({0} : Set 𝓗) ⊆ Cᵒ⊙ᵒ⊙ := by
  intro x hx
  rcases hx with hxC | hx0
  · rw [mem_polarSet_iff_forall_inner_le_one]
    -- If `x ∈ C`, then every element of `Cᵒ⊙` already bounds its inner product by `1`.
    intro u hu
    rw [mem_polarSet_iff_forall_inner_le_one] at hu
    simpa [real_inner_comm] using hu x hxC
  · -- The origin case is the previous lemma applied to `Cᵒ⊙`.
    rcases Set.mem_singleton_iff.mp hx0 with rfl
    exact zero_mem_polarSet (C := Cᵒ⊙)

/-- Helper for Theorem 7.18: the closed convex hull of `C ∪ {0}` is contained in the bipolar of
`C`. -/
private lemma closure_convexHull_union_singleton_zero_subset_polarSet_polarSet (C : Set 𝓗) :
    closure (convexHull ℝ (C ∪ ({0} : Set 𝓗))) ⊆ Cᵒ⊙ᵒ⊙ := by
  -- Proposition 7.16 already places `C ∪ {0}` in the bipolar, and the bipolar is closed convex.
  refine closure_minimal ?_ (polarSet_isClosed (C := Cᵒ⊙))
  refine convexHull_min ?_ (polarSet_convex (C := Cᵒ⊙))
  exact union_singleton_zero_subset_polarSet_polarSet (C := C)

/-- Helper for Theorem 7.18: every point of a set lies below the support supremum of that set. -/
private lemma inner_le_innerSupremumOn_of_mem {S : Set 𝓗} {u y : 𝓗} (hy : y ∈ S) :
    (⟪y, u⟫_ℝ : EReal) ≤ innerSupremumOn S u := by
  -- Realizing one point of the image gives a lower bound on the defining supremum.
  rw [innerSupremumOn_eq_sSup_image]
  exact (isLUB_sSup _).1 (Set.mem_image_of_mem _ hy)

/-- Helper for Theorem 7.18: a strict separator of a closed convex hull can be rescaled into an
element of `Cᵒ⊙` that violates the bipolar inequality at `x`. -/
private lemma scaled_separator_mem_polarSet_and_violates_x {C S : Set 𝓗} {x u : 𝓗}
    (hCS : C ⊆ S) (h0S : (0 : 𝓗) ∈ S)
    (hsep : innerSupremumOn S u < (⟪x, u⟫_ℝ : EReal)) :
    ∃ v : 𝓗, v ∈ Cᵒ⊙ ∧ 1 < ⟪x, v⟫_ℝ := by
  have hσ_nonneg : (0 : EReal) ≤ innerSupremumOn S u := by
    simpa using (inner_le_innerSupremumOn_of_mem (u := u) h0S)
  have hσ_top : innerSupremumOn S u ≠ ⊤ := ne_top_of_lt hsep
  have hσ_bot : innerSupremumOn S u ≠ ⊥ := by
    have hbot_lt : (⊥ : EReal) < innerSupremumOn S u :=
      lt_of_lt_of_le (EReal.bot_lt_coe 0) hσ_nonneg
    exact ne_of_gt hbot_lt
  have hσ_real :
      (((innerSupremumOn S u).toReal : ℝ) : EReal) = innerSupremumOn S u :=
    EReal.coe_toReal hσ_top hσ_bot
  have hσ_toReal_lt : (innerSupremumOn S u).toReal < ⟪x, u⟫_ℝ := by
    -- Replace the finite support value by its real representative before casting back.
    have hsep' :
        (((innerSupremumOn S u).toReal : ℝ) : EReal) < (⟪x, u⟫_ℝ : EReal) := by
      simpa [hσ_real] using hsep
    exact_mod_cast hsep'
  have hσ_toReal_nonneg : 0 ≤ (innerSupremumOn S u).toReal := by
    -- The point `0 ∈ S` forces the support value to be nonnegative.
    have hnonneg' :
        ((0 : ℝ) : EReal) ≤ (((innerSupremumOn S u).toReal : ℝ) : EReal) := by
      simpa [hσ_real] using hσ_nonneg
    exact_mod_cast hnonneg'
  let a : ℝ := ((innerSupremumOn S u).toReal + ⟪x, u⟫_ℝ) / 2
  have ha_left : (innerSupremumOn S u).toReal < a := by
    dsimp [a]
    linarith
  have ha_right : a < ⟪x, u⟫_ℝ := by
    dsimp [a]
    linarith
  have ha_pos : 0 < a := by
    dsimp [a]
    linarith
  refine ⟨a⁻¹ • u, ?_, ?_⟩
  · -- The rescaled separator puts all of `C` below the level `1`.
    rw [mem_polarSet_iff_forall_inner_le_one]
    intro y hy
    have hy_le : (⟪y, u⟫_ℝ : EReal) ≤ innerSupremumOn S u :=
      inner_le_innerSupremumOn_of_mem (u := u) (hCS hy)
    have hy_le_real : ⟪y, u⟫_ℝ ≤ (innerSupremumOn S u).toReal := by
      have hy' :
          (⟪y, u⟫_ℝ : EReal) ≤ (((innerSupremumOn S u).toReal : ℝ) : EReal) := by
        simpa [hσ_real] using hy_le
      exact_mod_cast hy'
    have hy_lt_a : ⟪y, u⟫_ℝ < a :=
      lt_of_le_of_lt hy_le_real ha_left
    have hmul :
        a⁻¹ * ⟪y, u⟫_ℝ < a⁻¹ * a := by
      exact mul_lt_mul_of_pos_left hy_lt_a (inv_pos.mpr ha_pos)
    have ha_inv_mul : a⁻¹ * a = (1 : ℝ) := by
      exact inv_mul_cancel₀ ha_pos.ne'
    have hscaled : a⁻¹ * ⟪y, u⟫_ℝ < 1 := by
      simpa [ha_inv_mul] using hmul
    simpa [real_inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using hscaled.le
  · -- The same scaling keeps the value at `x` strictly above `1`.
    have hmul :
        a⁻¹ * a < a⁻¹ * ⟪x, u⟫_ℝ := by
      exact mul_lt_mul_of_pos_left ha_right (inv_pos.mpr ha_pos)
    have ha_inv_mul : a⁻¹ * a = (1 : ℝ) := by
      exact inv_mul_cancel₀ ha_pos.ne'
    have hscaled : (1 : ℝ) < a⁻¹ * ⟪x, u⟫_ℝ := by
      simpa [ha_inv_mul] using hmul
    simpa [real_inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using hscaled

/-- Helper for Theorem 7.18: every point of the bipolar lies in the closed convex hull of
`C ∪ {0}`. -/
private lemma polarSet_polarSet_subset_closure_convexHull_union_singleton_zero (C : Set 𝓗) :
    Cᵒ⊙ᵒ⊙ ⊆ closure (convexHull ℝ (C ∪ ({0} : Set 𝓗))) := by
  intro x hx
  by_contra hxS
  let S : Set 𝓗 := closure (convexHull ℝ (C ∪ ({0} : Set 𝓗)))
  have h0S : (0 : 𝓗) ∈ S := by
    -- The origin belongs to the generating set, hence also to its closed convex hull.
    exact subset_closure (subset_convexHull ℝ (C ∪ ({0} : Set 𝓗)) (Or.inr (by simp)))
  have hS_nonempty : S.Nonempty := ⟨0, h0S⟩
  have hS_closed : IsClosed S := isClosed_closure
  have hS_convex : Convex ℝ S := by
    -- Convexity survives passage from the convex hull to its closure.
    simpa [S] using (convex_convexHull ℝ (C ∪ ({0} : Set 𝓗))).closure
  have hx_not_mem : x ∉ S := by
    simpa [S] using hxS
  rcases exists_nonzero_innerSupremumOn_lt_inner_of_nonempty_isClosed_convex_of_not_mem
      (S := S) hS_nonempty hS_closed hS_convex hx_not_mem with ⟨u, hu_ne, hsep⟩
  have hCS : C ⊆ S := by
    intro y hy
    exact subset_closure (subset_convexHull ℝ (C ∪ ({0} : Set 𝓗)) (Or.inl hy))
  rcases scaled_separator_mem_polarSet_and_violates_x hCS h0S hsep with ⟨v, hvC, hvx⟩
  have hxv_le : ⟪v, x⟫_ℝ ≤ 1 := by
    -- Bipolar membership says every element of `Cᵒ⊙` evaluates against `x` by at most `1`.
    rw [mem_polarSet_iff_forall_inner_le_one] at hx
    exact hx v hvC
  have hxv_le' : ⟪x, v⟫_ℝ ≤ 1 := by
    simpa [real_inner_comm] using hxv_le
  exact not_le_of_gt hvx hxv_le'

-- Proof sketch: Proposition 7.16 gives `C ∪ {0} ⊆ Cᵒ⊙ᵒ⊙`, and the bipolar is closed and convex, so
-- it contains `closure (convexHull ℝ (C ∪ {0}))`. For the reverse inclusion, separate any point
-- outside `closure (convexHull ℝ (C ∪ {0}))` from that closed convex set by a nonzero functional,
-- rescale to place the support bound at `1`, and use the polar inequalities to contradict
-- membership in `Cᵒ⊙ᵒ⊙`.
/-- Theorem 7.18: the bipolar polar set of `C` is exactly the closed convex hull of `C ∪ {0}`. -/
theorem polarSet_polarSet_eq_closure_convexHull_union_singleton_zero (C : Set 𝓗) :
    Cᵒ⊙ᵒ⊙ = closure (convexHull ℝ (C ∪ ({0} : Set 𝓗))) := by
  -- Prove the two inclusions separately: minimality gives the forward direction, and separation
  -- plus rescaling gives the reverse direction.
  apply Subset.antisymm
  · exact polarSet_polarSet_subset_closure_convexHull_union_singleton_zero (C := C)
  · exact closure_convexHull_union_singleton_zero_subset_polarSet_polarSet (C := C)

end

end Set

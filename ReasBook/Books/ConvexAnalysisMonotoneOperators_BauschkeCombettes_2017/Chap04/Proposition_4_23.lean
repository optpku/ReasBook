/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_22

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {D : Set H} {T : H → H}

/- The residual half-space inequality is equivalent to the squared norm comparison that appears
in quasinonexpansiveness. -/
private lemma inner_sub_image_le_half_residual_sq_iff_norm_image_sub_sq_le (x y z : H) :
    ⟪z - y, x - y⟫_ℝ ≤ (1 / 2 : ℝ) * ‖y - x‖ ^ 2 ↔ ‖y - z‖ ^ 2 ≤ ‖x - z‖ ^ 2 := by
  let a : H := y - z
  let b : H := x - z
  have hxy : x - y = b - a := by
    simp [a, b, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hyx : y - x = a - b := by
    simp [a, b, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  -- Rewrite the displayed inequality in terms of the canonical residual vectors `a` and `b`.
  have hinner :
      ⟪z - y, x - y⟫_ℝ = ‖a‖ ^ 2 - ⟪a, b⟫_ℝ := by
    rw [show z - y = -a by simp [a], hxy, inner_neg_left, inner_sub_right,
      real_inner_self_eq_norm_sq]
    ring
  have hnorm :
      ‖y - x‖ ^ 2 = ‖a‖ ^ 2 - 2 * ⟪a, b⟫_ℝ + ‖b‖ ^ 2 := by
    rw [hyx]
    simpa using norm_sub_sq_real a b
  have hyz : ‖y - z‖ ^ 2 = ‖a‖ ^ 2 := by
    simp [a]
  have hxz : ‖x - z‖ ^ 2 = ‖b‖ ^ 2 := by
    simp [b]
  constructor <;> intro h
  · -- After the quadratic expansions, the half-space inequality rearranges to the norm bound.
    nlinarith [h, hinner, hnorm, hyz, hxz]
  · -- The converse direction is the same real-algebra calculation in reverse.
    nlinarith [h, hinner, hnorm, hyz, hxz]

/- Each residual half-space section is closed when `D` is closed. -/
private lemma halfspace_section_isClosed (hD_closed : IsClosed D) (x : H) :
    IsClosed
      {y : H | y ∈ D ∧ ⟪y - T x, x - T x⟫_ℝ ≤ (1 / 2 : ℝ) * ‖T x - x‖ ^ 2} := by
  -- The defining scalar functional is continuous, so its sublevel set is closed.
  have hcont : Continuous fun y : H ↦ ⟪y - T x, x - T x⟫_ℝ := by
    fun_prop
  simpa [Set.setOf_and] using
    hD_closed.inter (isClosed_le hcont continuous_const)

-- Proof sketch: for `y ∈ D ∩ Function.fixedPoints T`, use quasinonexpansiveness and expand
-- `‖x - y‖^2 - ‖T x - y‖^2` to obtain the half-space inequality for every `x ∈ D`; conversely,
-- if `y` lies in every such half-space, substitute `x = y` and use `y ∈ D` to force `T y = y`.
/-- Proposition 4.23 (1): if `D` is nonempty and `T` is quasinonexpansive on `D`, then the fixed
point set of `T` in `D` is the intersection, over `x ∈ D`, of the half-spaces
`{y ∈ D | ⟪y - T x, x - T x⟫_ℝ ≤ (1 / 2) ‖T x - x‖^2}`. -/
theorem fixedPointSetOn_eq_iInter_halfspaces_of_quasinonexpansive
    (hD : D.Nonempty) (hT : QuasinonexpansiveOn D T) :
    fixedPointSetOn D T =
      ⋂ x ∈ D, {y : H | y ∈ D ∧ ⟪y - T x, x - T x⟫_ℝ ≤ (1 / 2 : ℝ) * ‖T x - x‖ ^ 2} := by
  rw [quasinonexpansiveOn_iff] at hT
  ext y
  constructor
  · intro hy
    rcases mem_fixedPointSetOn_iff.mp hy with ⟨hyD, _⟩
    refine Set.mem_iInter.2 fun x ↦ Set.mem_iInter.2 fun hx ↦ ?_
    refine ⟨hyD, ?_⟩
    -- Square the quasinonexpansive estimate and rewrite it via the quadratic helper.
    have hsq : ‖T x - y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
      have hle : ‖T x - y‖ ≤ ‖x - y‖ := hT x hx y hy
      exact sq_le_sq.mpr <| by
        simpa [abs_of_nonneg (norm_nonneg (T x - y)), abs_of_nonneg (norm_nonneg (x - y))] using
          hle
    exact
      (inner_sub_image_le_half_residual_sq_iff_norm_image_sub_sq_le x (T x) y).2 hsq
  · intro hy
    rcases hD with ⟨x0, hx0⟩
    have hyD : y ∈ D := by
      exact (Set.mem_iInter.1 (Set.mem_iInter.1 hy x0) hx0).1
    have hySection :
        ⟪y - T y, y - T y⟫_ℝ ≤ (1 / 2 : ℝ) * ‖T y - y‖ ^ 2 := by
      exact (Set.mem_iInter.1 (Set.mem_iInter.1 hy y) hyD).2
    -- Evaluating the section condition at `x = y` forces the residual norm to vanish.
    have hsq : ‖T y - y‖ ^ 2 ≤ ‖y - y‖ ^ 2 := by
      exact
        (inner_sub_image_le_half_residual_sq_iff_norm_image_sub_sq_le y (T y) y).1 hySection
    have hsq' : ‖T y - y‖ ^ 2 ≤ 0 := by
      simpa using hsq
    have hzero : ‖T y - y‖ = 0 := by
      nlinarith [sq_nonneg ‖T y - y‖, hsq']
    have hfix : T y = y := by
      exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
    exact mem_fixedPointSetOn_iff.mpr ⟨hyD, hfix⟩

-- Proof sketch: rewrite `fixedPointSetOn D T` using the characterization in
-- `fixedPointSetOn_eq_iInter_halfspaces_of_quasinonexpansive`; each half-space cut out by a
-- continuous affine functional is closed, and intersections of closed sets remain closed.
/-- Proposition 4.23 (2): if `T` is quasinonexpansive on a closed convex set `D`, then its fixed
point set in `D` is closed and convex. -/
theorem isClosed_and_convex_fixedPointSetOn_of_quasinonexpansive
    (hT : QuasinonexpansiveOn D T)
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) :
    IsClosed (fixedPointSetOn D T) ∧ Convex ℝ (fixedPointSetOn D T) := by
  constructor
  · by_cases hDn : D.Nonempty
    · rw [fixedPointSetOn_eq_iInter_halfspaces_of_quasinonexpansive hDn hT]
      exact isClosed_iInter fun x ↦
        isClosed_iInter fun hx ↦ halfspace_section_isClosed hD_closed x
    · have hD_empty : D = ∅ := Set.not_nonempty_iff_eq_empty.mp hDn
      simp [hD_empty, fixedPointSetOn]
  · by_cases hDn : D.Nonempty
    · exact convex_fixedPointSetOn_of_quasinonexpansiveOn hDn hD_convex hT
    · have hD_empty : D = ∅ := Set.not_nonempty_iff_eq_empty.mp hDn
      simpa [hD_empty, fixedPointSetOn] using (convex_empty : Convex ℝ (∅ : Set H))

end

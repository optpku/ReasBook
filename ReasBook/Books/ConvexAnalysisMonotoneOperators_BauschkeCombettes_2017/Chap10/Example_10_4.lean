/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Definition_10_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Proposition_10_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open ERealFunction

section Seminormed

variable {H : Type u} [SeminormedAddCommGroup H] [NormedSpace ℝ H]

-- Proof sketch: the norm is positively homogeneous for positive real scalars, and
-- `sublinear_iff_isConvex_of_positivelyHomogeneous` upgrades the canonical convexity theorem
-- `convexOn_univ_norm` to sublinearity.
/-- Example 10.4 (i): the norm function is sublinear. -/
theorem norm_sublinear :
    Sublinear (fun x : H ↦ (‖x‖ : EReal)) := by
  have hnorm : PositivelyHomogeneous (fun x : H ↦ (‖x‖ : EReal)) := by
    intro a ha x
    change ((‖a • x‖ : ℝ) : EReal) = (a : EReal) * (‖x‖ : EReal)
    rw [norm_smul, Real.norm_of_nonneg ha.le, EReal.coe_mul]
  let f : H → Set.Ioi (⊥ : EReal) := fun x ↦ ⟨(‖x‖ : EReal), by simp⟩
  have hnorm' : PositivelyHomogeneous fun x : H ↦ (f x : EReal) := hnorm
  have hsub : Sublinear fun x : H ↦ (f x : EReal) := by
    refine (sublinear_iff_isConvex_of_positivelyHomogeneous f hnorm').2 ?_
    intro x y a ha hb
    have hreal : ‖a • x + (1 - a) • y‖ ≤ a * ‖x‖ + (1 - a) * ‖y‖ := by
      simpa [smul_eq_mul] using
        (convexOn_univ_norm.2 (by simp) (by simp) ha (sub_nonneg.mpr hb) (by ring) :
          ‖a • x + (1 - a) • y‖ ≤ a • ‖x‖ + (1 - a) • ‖y‖)
    change ((‖a • x + (1 - a) • y‖ : ℝ) : EReal) ≤
      (((a * ‖x‖ + (1 - a) * ‖y‖ : ℝ)) : EReal)
    rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul]
    exact_mod_cast hreal
  simpa [f] using hsub

end Seminormed

section NontrivialNormed

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [Nontrivial H]

-- Proof sketch: linearity would force `‖(-1) • x‖ = (-1) • ‖x‖` for every `x`. Since the left-hand
-- side equals `‖x‖`, any nonzero vector would then satisfy `‖x‖ = -‖x‖`, hence `‖x‖ = 0`,
-- contradiction.
/-- Example 10.4 (i): on a nontrivial real normed space, the norm function is not linear. -/
theorem norm_not_linear :
    ¬ IsLinearMap ℝ (norm : H → ℝ) := by
  intro hlinear
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  have hmap : ‖x‖ = (-1 : ℝ) * ‖x‖ := by
    simpa [smul_eq_mul] using hlinear.map_smul (-1 : ℝ) x
  have hnorm : ‖x‖ = 0 := by
    linarith [hmap]
  exact hx (norm_eq_zero.mp hnorm)

-- Proof sketch: positive homogeneity at the scalar `2` would give `‖2 • x‖^2 = 2 ‖x‖^2`, but the
-- norm scales quadratically, so the left-hand side is `4 ‖x‖^2`. A nonzero vector yields a
-- contradiction.
/-- On a nontrivial real normed space, the squared norm is not positively homogeneous. -/
theorem norm_sq_not_positivelyHomogeneous :
    ¬ PositivelyHomogeneous (fun x : H ↦ (‖x‖ ^ 2 : EReal)) := by
  intro hsq
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  have hscaleE :
      ((‖(2 : ℝ) • x‖ ^ 2 : ℝ) : EReal) = (((2 : ℝ) * ‖x‖ ^ 2 : ℝ) : EReal) := by
    simpa [EReal.coe_mul] using hsq.map_smul_of_pos (show 0 < (2 : ℝ) by norm_num) x
  have hscale : ‖(2 : ℝ) • x‖ ^ 2 = (2 : ℝ) * ‖x‖ ^ 2 :=
    EReal.coe_injective hscaleE
  have hquad : ‖(2 : ℝ) • x‖ ^ 2 = (4 : ℝ) * ‖x‖ ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num), pow_two, pow_two]
    ring
  have hnorm : ‖x‖ = 0 := by
    nlinarith [hscale, hquad]
  exact hx (norm_eq_zero.mp hnorm)

-- Proof sketch: a sublinear function is positively homogeneous by Definition 10.1, while
-- `x ↦ ‖x‖^2` fails positive homogeneity on every nontrivial real normed space.
/-- Example 10.4 (ii): on a nontrivial real normed space, the squared norm is not sublinear. -/
theorem norm_sq_not_sublinear :
    ¬ Sublinear (fun x : H ↦ (‖x‖ ^ 2 : EReal)) := by
  intro hsub
  exact norm_sq_not_positivelyHomogeneous (hsub.positivelyHomogeneous)

end NontrivialNormed

section SeminormedConvex

variable {H : Type u} [SeminormedAddCommGroup H] [NormedSpace ℝ H]

-- Proof sketch: the norm is convex on the whole space in any real seminormed space, and squaring
-- preserves convexity on the nonnegative range `Ici 0`.
/-- Example 10.4 (ii): on a real seminormed space, the squared norm is convex. -/
theorem norm_sq_convexOn_univ :
    ConvexOn ℝ (Set.univ : Set H) (fun x ↦ ‖x‖ ^ 2) :=
  (convexOn_univ_norm : ConvexOn ℝ (Set.univ : Set H) (fun x ↦ ‖x‖)).pow
    (fun x _ ↦ norm_nonneg x) 2

end SeminormedConvex

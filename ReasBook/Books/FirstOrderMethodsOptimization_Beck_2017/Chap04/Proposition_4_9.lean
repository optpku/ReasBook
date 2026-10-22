/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace (toDualMap)

noncomputable section

/- Proposition 4.9 is `source-facing`: it computes the conjugate of the hinge loss on `ℝ`.
The `core/canonical` owner abstractions already live upstream as the indicator `δ_ C` from
Chapter 2 and the primal-space conjugate `f∗` from Definition 4.1. This file therefore keeps
only the hinge-loss integrand as primitive data, states the conjugacy formula in the chapter's
canonical primal-space notation, and provides the dual-space `toDualMap ℝ ℝ` specialization as a
thin bridge companion. -/

recall conjugate_function_primal_apply

/-- The hinge-loss example `x ↦ max (1 - x, 0)`, viewed as an `EReal`-valued function. -/
def hinge_loss : ℝ → EReal :=
  fun x ↦ (max (1 - x) 0 : EReal)

/-- Evaluating `hinge_loss` at `x` returns `max (1 - x, 0)` as an extended real number. -/
@[simp] theorem hinge_loss_apply (x : ℝ) :
    hinge_loss x = (max (1 - x) 0 : EReal) :=
  rfl

/-- Helper for Proposition 4.9: on the region `x ≤ 1`, the Fenchel integrand for `hinge_loss`
reduces to the affine function `((1 + y) * x - 1)`. -/
lemma hingeLossFenchelIntegrand_eq_of_le_one {x y : ℝ} (hx : x ≤ 1) :
    ((toDualMap ℝ ℝ y x : EReal) - hinge_loss x) = ((((1 + y) * x - 1 : ℝ)) : EReal) := by
  have hx' : 0 ≤ 1 - x := by
    linarith
  -- Normalize the scalar pairing and the hinge branch to a real affine expression.
  change (((x * y - max (1 - x) 0 : ℝ)) : EReal) = ((((1 + y) * x - 1 : ℝ)) : EReal)
  rw [max_eq_left hx']
  congr 1
  ring_nf

/-- Helper for Proposition 4.9: on the region `1 ≤ x`, the Fenchel integrand for `hinge_loss`
reduces to the affine function `x * y`. -/
lemma hingeLossFenchelIntegrand_eq_of_one_le {x y : ℝ} (hx : 1 ≤ x) :
    ((toDualMap ℝ ℝ y x : EReal) - hinge_loss x) = (((x * y : ℝ)) : EReal) := by
  have hx' : 1 - x ≤ 0 := by
    linarith
  -- On the right branch, the hinge term vanishes and only the linear pairing remains.
  change (((x * y - max (1 - x) 0 : ℝ)) : EReal) = (((x * y : ℝ)) : EReal)
  rw [max_eq_right hx']
  ring_nf

/-- Helper for Proposition 4.9: if `y ∈ [-1, 0]`, then the conjugate of `hinge_loss` is finite
and equals `y`. -/
lemma hingeLossConjugate_eq_of_mem_Icc {y : ℝ} (hy : y ∈ Set.Icc (-1 : ℝ) 0) :
    (hinge_loss∗) y = (y : EReal) := by
  have hyNonneg : 0 ≤ 1 + y := by
    linarith [hy.1]
  have hyNonpos : y ≤ 0 := hy.2
  rw [conjugate_function_primal_apply, conjugate_function_apply]
  apply le_antisymm
  · -- Bound every branch of the objective above by the candidate value `y`.
    refine sSup_le ?_
    rintro z ⟨x, rfl⟩
    rcases le_or_gt x 1 with hx | hx
    · change ((toDualMap ℝ ℝ y x : EReal) - hinge_loss x) ≤ (y : EReal)
      rw [hingeLossFenchelIntegrand_eq_of_le_one hx]
      refine EReal.coe_le_coe_iff.mpr ?_
      have hmul : (1 + y) * x ≤ 1 + y := by
        simpa using (mul_le_mul_of_nonneg_left hx hyNonneg)
      linarith
    · change ((toDualMap ℝ ℝ y x : EReal) - hinge_loss x) ≤ (y : EReal)
      rw [hingeLossFenchelIntegrand_eq_of_one_le (le_of_lt hx)]
      refine EReal.coe_le_coe_iff.mpr ?_
      simpa using (mul_le_mul_of_nonpos_right (le_of_lt hx) hyNonpos)
  · -- The value `y` is attained at the breakpoint `x = 1`.
    refine le_sSup ?_
    refine ⟨1, ?_⟩
    simpa using (hingeLossFenchelIntegrand_eq_of_one_le (x := 1) (y := y) le_rfl)

/-- Helper for Proposition 4.9: if `0 < y`, then the conjugate of `hinge_loss` is `⊤`. -/
lemma hingeLossConjugate_eq_top_of_pos {y : ℝ} (hy : 0 < y) :
    (hinge_loss∗) y = ⊤ := by
  rw [conjugate_function_primal_apply, conjugate_function_apply, EReal.eq_top_iff_forall_lt]
  intro r
  let x : ℝ := max 1 ((r + 1) / y)
  have hx : 1 ≤ x := by
    simp [x]
  have hxDiv : (r + 1) / y ≤ x := by
    simp [x]
  have hxy : r + 1 ≤ x * y := by
    have hmul : ((r + 1) / y) * y ≤ x * y := by
      exact mul_le_mul_of_nonneg_right hxDiv (le_of_lt hy)
    simpa [div_eq_mul_inv, hy.ne', mul_assoc] using hmul
  have hlt : (r : EReal) < ((x * y : ℝ) : EReal) := by
    refine EReal.coe_lt_coe_iff.mpr ?_
    linarith
  -- Choose a large point on the right affine branch where the objective exceeds `r`.
  calc
    (r : EReal) < ((x * y : ℝ) : EReal) := hlt
    _ = ((toDualMap ℝ ℝ y x : EReal) - hinge_loss x) := by
      symm
      exact hingeLossFenchelIntegrand_eq_of_one_le hx
    _ ≤ sSup (Set.range fun z : ℝ ↦ (toDualMap ℝ ℝ y z : EReal) - hinge_loss z) := by
      exact le_sSup ⟨x, rfl⟩

/-- Helper for Proposition 4.9: if `y < -1`, then the conjugate of `hinge_loss` is `⊤`. -/
lemma hingeLossConjugate_eq_top_of_lt_negOne {y : ℝ} (hy : y < -1) :
    (hinge_loss∗) y = ⊤ := by
  let s : ℝ := -(1 + y)
  have hs : 0 < s := by
    dsimp [s]
    linarith
  rw [conjugate_function_primal_apply, conjugate_function_apply, EReal.eq_top_iff_forall_lt]
  intro r
  let x : ℝ := min 1 (-((r + 2) / s))
  have hx : x ≤ 1 := by
    simp [x]
  have hxAux : x ≤ -((r + 2) / s) := by
    simp [x]
  have hmul : (-s) * (-((r + 2) / s)) ≤ (-s) * x := by
    exact mul_le_mul_of_nonpos_left hxAux (le_of_lt (neg_neg_iff_pos.mpr hs))
  have hrewrite : (-s) * (-((r + 2) / s)) = r + 2 := by
    field_simp [hs.ne']
  have hxy : r + 2 ≤ (-s) * x := by
    simpa [hrewrite] using hmul
  have hlt : (r : EReal) < ((((1 + y) * x - 1 : ℝ)) : EReal) := by
    refine EReal.coe_lt_coe_iff.mpr ?_
    dsimp [s] at hxy
    linarith
  -- Choose a far-left point on the left affine branch where the objective exceeds `r`.
  calc
    (r : EReal) < ((((1 + y) * x - 1 : ℝ)) : EReal) := hlt
    _ = ((toDualMap ℝ ℝ y x : EReal) - hinge_loss x) := by
      symm
      exact hingeLossFenchelIntegrand_eq_of_le_one hx
    _ ≤ sSup (Set.range fun z : ℝ ↦ (toDualMap ℝ ℝ y z : EReal) - hinge_loss z) := by
      exact le_sSup ⟨x, rfl⟩

-- Proof sketch: analyze the supremum in `(hinge_loss∗) y` piecewise in `x`.
-- The affine branch on `(-∞, 1]` has slope `1 + y`, the branch on `[1, ∞)` has slope `y`, so a
-- finite maximizer exists exactly for `y ∈ [-1, 0]`, where the value at `x = 1` is `y`.
/-- Proposition 4.9: the convex conjugate `hinge_loss∗` of the hinge loss
`x ↦ max (1 - x, 0)` is the affine function `y` plus the indicator
`δ_ (Set.Icc (-1) 0)`. -/
theorem hinge_loss_conjugate_eq (y : ℝ) :
    (hinge_loss∗) y = (y : EReal) + (δ_ (Set.Icc (-1 : ℝ) 0)) y := by
  -- Split `y` into the two unbounded regimes and the finite interval `[-1, 0]`.
  by_cases hyLeft : y < -1
  · have hyNotMem : y ∉ Set.Icc (-1 : ℝ) 0 := by
      intro hyMem
      exact not_le_of_gt hyLeft hyMem.1
    simpa [extendedIndicator_of_not_mem hyNotMem] using
      hingeLossConjugate_eq_top_of_lt_negOne hyLeft
  · have hyGeNegOne : -1 ≤ y := by
      linarith
    by_cases hyPos : 0 < y
    · have hyNotMem : y ∉ Set.Icc (-1 : ℝ) 0 := by
        intro hyMem
        exact not_le_of_gt hyPos hyMem.2
      simpa [extendedIndicator_of_not_mem hyNotMem] using hingeLossConjugate_eq_top_of_pos hyPos
    · have hyMem : y ∈ Set.Icc (-1 : ℝ) 0 := by
        refine ⟨hyGeNegOne, ?_⟩
        linarith
      simpa [extendedIndicator_of_mem hyMem] using hingeLossConjugate_eq_of_mem_Icc hyMem

/-- Companion bridge: the dual-space Chapter 4 owner `conjugate_function hinge_loss`,
specialized along `toDualMap ℝ ℝ`, agrees with the primal-space formula from
`hinge_loss_conjugate_eq`. -/
theorem hinge_loss_conjugate_eq_dual (y : ℝ) :
    conjugate_function hinge_loss (toDualMap ℝ ℝ y) =
      (y : EReal) + (δ_ (Set.Icc (-1 : ℝ) 0)) y := by
  simpa [conjugate_function_primal_apply] using hinge_loss_conjugate_eq y

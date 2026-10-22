/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Definition_11_1_extra_1
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function

noncomputable section

section Chapter11Lemma1114

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Layer triage:
-- * source-facing: existence of a feasible descent direction versus failure of `IsMinOn`
-- * core/canonical reused from earlier Chapter 11 owner: `IsFeasibleDescentDirection`
-- * bridge/view: the companion theorem phrased via `feasibleDescentDirections`

/-- Helper for Chapter11 Lemma 11.1.4: in a convex feasible set, the difference `y - x` points
along a feasible segment starting from `x` whenever `y ≠ x`. -/
lemma sub_isFeasibleDirectionAt_of_convex
    {x y : E} {X : Set E} (hx : x ∈ X) (hy : y ∈ X) (hyx : y ≠ x) (hX : Convex ℝ X) :
    IsFeasibleDirectionAt X x (y - x) := by
  -- Use the full segment from `x` to `y` as the Chapter 8 feasible-ray witness.
  refine ⟨sub_ne_zero.mpr hyx, ⟨1, zero_lt_one, ?_⟩⟩
  intro t ht
  simpa using hX.add_smul_sub_mem hx hy ht

/-- Helper for Chapter11 Lemma 11.1.4: a strictly better feasible point yields a negative
gradient pairing with the chord direction from `x` to that point. -/
lemma inner_sub_gradient_lt_zero_of_convexOn_of_lt
    (f : E → ℝ) {x y : E} {X : Set E}
    (hx : x ∈ X) (hy : y ∈ X) (hf : ConvexOn ℝ X f)
    (hfdiff : DifferentiableAt ℝ f x) (hfyx : f y < f x) :
    inner ℝ (y - x) (gradient f x) < 0 := by
  let g : ℝ → ℝ := f ∘ AffineMap.lineMap x y
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) g := by
    -- Restrict the convex objective to the segment joining `x` and `y`.
    refine (hf.comp_affineMap (AffineMap.lineMap x y)).subset ?_ (convex_Icc 0 1)
    exact hf.1.mapsTo_lineMap hx hy
  have hcomp : HasDerivAt g ((fderiv ℝ f x) y - (fderiv ℝ f x) x) 0 := by
    -- Compose `f` with the segment map and identify the left endpoint with `x`.
    simpa [g] using
      (HasFDerivAt.comp_hasDerivAt_of_eq
        (x := (0 : ℝ)) (y := x) (l := f) (f := AffineMap.lineMap x y)
        hfdiff.hasFDerivAt
        (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := (0 : ℝ)))
        (AffineMap.lineMap_apply_zero x y).symm)
  have hgdiff : DifferentiableAt ℝ g 0 :=
    hcomp.differentiableAt
  have hderiv : deriv g 0 = inner ℝ (y - x) (gradient f x) := by
    -- Compute the derivative of the segment objective at `0`.
    calc
      deriv g 0 = (fderiv ℝ f x) y - (fderiv ℝ f x) x := hcomp.deriv
      _ = (fderiv ℝ f x) (y - x) := by simp
      _ = inner ℝ (gradient f x) (y - x) := by
        simpa using (inner_gradient_left (𝕜 := ℝ) (f := f) (x := x) (y := y - x))
      _ = inner ℝ (y - x) (gradient f x) := by rw [real_inner_comm]
  have hderiv_le : deriv g 0 ≤ slope g 0 1 :=
    hconv.deriv_le_slope (by simp) (by simp) zero_lt_one hgdiff
  have hslope_lt : slope g 0 1 < 0 := by
    -- The secant slope is negative because the endpoint value is strictly smaller.
    simpa [g, slope_def_field] using sub_lt_zero.mpr hfyx
  have hderiv_lt : deriv g 0 < 0 :=
    lt_of_le_of_lt hderiv_le hslope_lt
  simpa [hderiv] using hderiv_lt

/-- Chapter11 Lemma 11.1.4: if `x ∈ X`, `X` is convex, `f` is convex on `X`, and `f` is
differentiable at `x`, then there exists a feasible descent direction at `x` if and only if `x`
is not a minimizer of `f` on `X`. -/
theorem exists_feasibleDescentDirection_iff_not_isMinOn_of_convexOn
    (f : E → ℝ) {x : E} {X : Set E}
    (hx : x ∈ X) (hX : Convex ℝ X) (hf : ConvexOn ℝ X f)
    (hfdiff : DifferentiableAt ℝ f x) :
    (∃ d, IsFeasibleDescentDirection f x X d) ↔ ¬ IsMinOn f X x := by
  constructor
  · rintro ⟨d, hd⟩ hmin
    -- A feasible descent direction gives a feasible step with smaller objective value.
    rcases hd.exists_feasible_improving_step with ⟨α, hα, hxα, hlt⟩
    exact not_lt_of_ge ((isMinOn_iff.mp hmin) _ hxα) hlt
  · intro hnotmin
    rw [isMinOn_iff] at hnotmin
    push Not at hnotmin
    rcases hnotmin with ⟨y, hy, hfyx⟩
    have hyx : y ≠ x := by
      intro hyx
      subst hyx
      exact lt_irrefl _ hfyx
    -- Follow the source proof and choose the chord from `x` to a strictly better feasible point.
    refine ⟨y - x, ?_⟩
    rw [isFeasibleDescentDirection_iff_feasible_and_descent]
    refine ⟨sub_isFeasibleDirectionAt_of_convex hx hy hyx hX, ?_⟩
    -- Convexity of the objective forces this chord to have negative gradient pairing at `x`.
    simpa [isDescentDirectionAt_iff, real_inner_comm] using
      inner_sub_gradient_lt_zero_of_convexOn_of_lt f hx hy hf hfdiff hfyx

/-- The set-valued view `feasibleDescentDirections f x X` has a point exactly when the source
feasible-descent predicate holds for some direction. -/
theorem exists_mem_feasibleDescentDirections_iff_not_isMinOn_of_convexOn
    (f : E → ℝ) {x : E} {X : Set E}
    (hx : x ∈ X) (hX : Convex ℝ X) (hf : ConvexOn ℝ X f)
    (hfdiff : DifferentiableAt ℝ f x) :
    (∃ d, d ∈ feasibleDescentDirections f x X) ↔ ¬ IsMinOn f X x := by
  simpa [mem_feasibleDescentDirections_iff] using
    exists_feasibleDescentDirection_iff_not_isMinOn_of_convexOn f hx hX hf hfdiff

#print axioms exists_feasibleDescentDirection_iff_not_isMinOn_of_convexOn

end Chapter11Lemma1114

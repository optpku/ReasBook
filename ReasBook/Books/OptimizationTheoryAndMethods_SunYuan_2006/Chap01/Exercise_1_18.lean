/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp

-- Semantic recall hits verified for this item: `ConvexOn` and
-- `convexOn_iff_forall_pos`; local precedent in Chapter 1 uses `ConvexOn ℝ Set.univ f`
-- for global convexity statements on concrete Euclidean spaces.

section Exercise118

local notation "Point2" => EuclideanSpace ℝ (Fin 2)

local notation "Point3" => EuclideanSpace ℝ (Fin 3)

/-- The function `(x₁, x₂) ↦ x₁ * exp (-(x₁ + x₂))` from Exercise 1.18 (1). -/
noncomputable def exercise118Fun1 (x : Point2) : ℝ :=
  x 0 * Real.exp (-(x 0 + x 1))

/-- The quadratic function from Exercise 1.18 (2). -/
noncomputable def exercise118Fun2 (x : Point3) : ℝ :=
  x 0 ^ 2 + 3 * x 1 ^ 2 + 9 * x 2 ^ 2 - 2 * x 0 * x 1 + 6 * x 1 * x 2 + 2 * x 2 * x 0

/-- Helper for Chapter01 Exercise 1.18: the chosen midpoint violates Jensen's inequality for
`exercise118Fun1`. -/
lemma exercise118Fun1_midpoint_counterexample :
    exercise118Fun1 (((1 / 2 : ℝ) • !₂[(1 : ℝ), 0]) + ((1 / 2 : ℝ) • !₂[(0 : ℝ), 0])) >
      (1 / 2 : ℝ) * exercise118Fun1 !₂[(1 : ℝ), 0] +
        (1 / 2 : ℝ) * exercise118Fun1 !₂[(0 : ℝ), 0] := by
  -- The midpoint of `(1, 0)` and `(0, 0)` is `(1 / 2, 0)`.
  have hmid :
      (((1 / 2 : ℝ) • !₂[(1 : ℝ), 0]) + ((1 / 2 : ℝ) • !₂[(0 : ℝ), 0])) =
        !₂[(1 / 2 : ℝ), 0] := by
    ext i
    fin_cases i <;> norm_num
  -- The exponential factor is larger at `-1 / 2` than at `-1`, so the midpoint value is larger
  -- than the midpoint of the endpoint values.
  have hexp : Real.exp (-1 : ℝ) < Real.exp (-(1 / 2 : ℝ)) := by
    exact Real.exp_lt_exp.mpr (by norm_num)
  have hmul :
      (1 / 2 : ℝ) * Real.exp (-1 : ℝ) < (1 / 2 : ℝ) * Real.exp (-(1 / 2 : ℝ)) := by
    exact mul_lt_mul_of_pos_left hexp (by norm_num)
  calc
    exercise118Fun1 (((1 / 2 : ℝ) • !₂[(1 : ℝ), 0]) + ((1 / 2 : ℝ) • !₂[(0 : ℝ), 0]))
        = (1 / 2 : ℝ) * Real.exp (-(1 / 2 : ℝ)) := by
            rw [hmid]
            norm_num [exercise118Fun1]
    _ > (1 / 2 : ℝ) * Real.exp (-1 : ℝ) := by exact hmul
    _ = (1 / 2 : ℝ) * exercise118Fun1 !₂[(1 : ℝ), 0] +
          (1 / 2 : ℝ) * exercise118Fun1 !₂[(0 : ℝ), 0] := by
            norm_num [exercise118Fun1]

/-- Helper for Chapter01 Exercise 1.18: the quadratic in part (2) is a sum of squares of two
linear forms. -/
lemma exercise118Fun2_eq_sum_squares (x : Point3) :
    exercise118Fun2 x = (x 0 - x 1 + x 2) ^ (2 : ℕ) + 2 * (x 1 + 2 * x 2) ^ (2 : ℕ) := by
  -- Expanding the two squares reproduces the original quadratic exactly.
  unfold exercise118Fun2
  ring

/-- Helper for Chapter01 Exercise 1.18: the same sum-of-squares identity, written in the
`WithLp` coordinate model used by `EuclideanSpace.projₗ`. -/
lemma exercise118Fun2_eq_sum_squares_ofLp (x : Point3) :
    exercise118Fun2 x =
      (x.ofLp 0 - x.ofLp 1 + x.ofLp 2) ^ (2 : ℕ) + 2 * (x.ofLp 1 + 2 * x.ofLp 2) ^ (2 : ℕ) := by
  -- The `EuclideanSpace` coordinates and `ofLp` coordinates are definitionally the same.
  simpa using exercise118Fun2_eq_sum_squares x

/-- Helper for Chapter01 Exercise 1.18: the quadratic from part (2) is pointwise equal to the
sum-of-squares expression used in the convexity proof. -/
lemma exercise118Fun2_as_sum_squares_ofLp :
    exercise118Fun2 =
      fun x : Point3 ↦ (x.ofLp 0 - x.ofLp 1 + x.ofLp 2) ^ (2 : ℕ) +
        2 * (x.ofLp 1 + 2 * x.ofLp 2) ^ (2 : ℕ) := by
  -- Packaging the pointwise identity as a function equality lets the final `simpa` rewrite the
  -- target `ConvexOn` statement directly.
  funext x
  exact exercise118Fun2_eq_sum_squares_ofLp x

/-- Helper for Chapter01 Exercise 1.18: composing the convex square function with a real linear
form stays convex on the whole space. -/
lemma convexOn_sq_comp_linear {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (L : E →ₗ[ℝ] ℝ) : ConvexOn ℝ Set.univ (fun x ↦ (L x) ^ (2 : ℕ)) := by
  -- The scalar square is convex on `ℝ`; evaluating it on `L x` and `L y` gives the desired
  -- Jensen inequality on the domain of `L`.
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simpa [L.map_add, L.map_smul, smul_eq_mul] using
    (Even.convexOn_pow (𝕜 := ℝ) (n := 2) even_two).2
      (x := L x) (by simp) (y := L y) (by simp) ha hb hab

/-- Chapter01 Exercise 1.18 (1): the function `exercise118Fun1` on `ℝ²` is not convex. -/
theorem exercise118Fun1_not_convex :
    ¬ ConvexOn ℝ Set.univ exercise118Fun1 := by
  intro hconv
  let x : Point2 := !₂[(1 : ℝ), 0]
  let y : Point2 := !₂[(0 : ℝ), 0]
  -- Convexity would force Jensen's midpoint inequality at the chosen endpoints.
  have hJensen := hconv.2
  have hmidpoint :
      exercise118Fun1 (((1 / 2 : ℝ) • x) + ((1 / 2 : ℝ) • y)) ≤
        (1 / 2 : ℝ) * exercise118Fun1 x + (1 / 2 : ℝ) * exercise118Fun1 y := by
    simpa [x, y, smul_eq_mul] using
      hJensen (x := x) (by simp) (y := y) (by simp)
        (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  -- The explicit midpoint computation contradicts that inequality.
  have hstrict :
      exercise118Fun1 (((1 / 2 : ℝ) • x) + ((1 / 2 : ℝ) • y)) >
        (1 / 2 : ℝ) * exercise118Fun1 x + (1 / 2 : ℝ) * exercise118Fun1 y := by
    simpa [x, y] using exercise118Fun1_midpoint_counterexample
  exact (not_lt_of_ge hmidpoint) hstrict

/-- Chapter01 Exercise 1.18 (2): the quadratic function `exercise118Fun2` on `ℝ³` is convex. -/
theorem exercise118Fun2_convex :
    ConvexOn ℝ Set.univ exercise118Fun2 := by
  let L₁ : Point3 →ₗ[ℝ] ℝ :=
    EuclideanSpace.projₗ 0 - EuclideanSpace.projₗ 1 + EuclideanSpace.projₗ 2
  let L₂ : Point3 →ₗ[ℝ] ℝ :=
    EuclideanSpace.projₗ 1 + (2 : ℝ) • EuclideanSpace.projₗ 2
  have hsq₁ : ConvexOn ℝ Set.univ (fun x : Point3 ↦ (L₁ x) ^ (2 : ℕ)) :=
    convexOn_sq_comp_linear L₁
  have hsq₂ : ConvexOn ℝ Set.univ (fun x : Point3 ↦ (L₂ x) ^ (2 : ℕ)) :=
    convexOn_sq_comp_linear L₂
  have hscaled : ConvexOn ℝ Set.univ (fun x : Point3 ↦ 2 * (L₂ x) ^ (2 : ℕ)) := by
    -- Scaling a convex function by a nonnegative constant preserves convexity.
    simpa [smul_eq_mul] using (ConvexOn.smul (c := (2 : ℝ)) (by norm_num) hsq₂)
  have hsum :
      ConvexOn ℝ Set.univ (fun x : Point3 ↦ (L₁ x) ^ (2 : ℕ) + 2 * (L₂ x) ^ (2 : ℕ)) :=
    hsq₁.add hscaled
  -- Rewriting the quadratic as that sum of squares completes the proof.
  simpa [L₁, L₂, EuclideanSpace.projₗ, exercise118Fun2_as_sum_squares_ofLp] using hsum

end Exercise118

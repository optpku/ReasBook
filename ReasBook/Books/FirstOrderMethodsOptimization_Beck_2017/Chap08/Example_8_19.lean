/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_27
import FirstOrderMethodsOptimization_Beck_2017.Chap02.FunctionToEReal
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_19
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_4
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_7
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_12
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_10

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open WithLp (toLp)
open scoped Matrix

noncomputable section

section

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The matrix `A = ((1, 2), (3, 4))` from Example 8.19. -/
def example_8_19_matrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 : ℝ), 2; 3, 4]

/-- The Example 8.19 objective on `ℝ²` is
`f(x₁, x₂) = |x₁ + 2 x₂| + |3 x₁ + 4 x₂|`. -/
def example_8_19_objective (x : E) : ℝ :=
  |x 0 + 2 * x 1| + |3 * x 0 + 4 * x 1|

local notation "fE" => fun x : E ↦ (example_8_19_objective x : EReal)

-- Proof sketch: compute `example_8_19_matrix.toEuclideanLin x`, identify its two coordinates with
-- `x₁ + 2x₂` and `3x₁ + 4x₂`, and rewrite the `ℓ¹` norm on `ℝ²` as the sum of the absolute values
-- of those coordinates.
/-- The Example 8.19 objective is the `ℓ¹` norm of `A x`. -/
theorem example_8_19_objective_eq_l1_matrix_norm (x : E) :
    example_8_19_objective x =
      ‖toLp 1 (fun i : Fin 2 ↦ (example_8_19_matrix.toEuclideanLin x) i)‖ := by
  -- Rewrite the Euclidean `ℓ¹` norm of `A x` into the sum of its two coordinate absolute values.
  simpa [EuclideanSpace.l1Norm, example_8_19_objective, example_8_19_matrix,
    Matrix.toLpLin_apply, Fin.sum_univ_two] using
    (EuclideanSpace.l1Norm_eq_sum_abs (example_8_19_matrix.toEuclideanLin x)).symm

-- Proof sketch: evaluate the objective at the origin and simplify the two absolute values.
/-- For Example 8.19, the objective value at the origin is `0`. -/
theorem example_8_19_objective_zero :
    example_8_19_objective (0 : E) = 0 := by
  simp [example_8_19_objective]

/-- Helper for Example 8.19: the objective is nonnegative everywhere on `ℝ²`. -/
theorem example_8_19_objective_nonneg (x : E) :
    0 ≤ example_8_19_objective x := by
  -- Both absolute-value terms are nonnegative, so their sum is nonnegative as well.
  dsimp [example_8_19_objective]
  positivity

/-- Helper for Example 8.19: the objective vanishes exactly at the origin. -/
theorem example_8_19_objective_eq_zero_iff_origin (x : E) :
    example_8_19_objective x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    -- The two nonnegative absolute-value terms must each vanish.
    have hfirst_nonneg : 0 ≤ |x 0 + 2 * x 1| := abs_nonneg _
    have hsecond_nonneg : 0 ≤ |3 * x 0 + 4 * x 1| := abs_nonneg _
    have hfirst_zero : |x 0 + 2 * x 1| = 0 := by
      apply le_antisymm
      · calc
          |x 0 + 2 * x 1| ≤ |x 0 + 2 * x 1| + |3 * x 0 + 4 * x 1| := by
            nlinarith [hsecond_nonneg]
          _ = 0 := hx
      · exact hfirst_nonneg
    have hsecond_zero : |3 * x 0 + 4 * x 1| = 0 := by
      apply le_antisymm
      · calc
          |3 * x 0 + 4 * x 1| ≤ |x 0 + 2 * x 1| + |3 * x 0 + 4 * x 1| := by
            nlinarith [hfirst_nonneg]
          _ = 0 := hx
      · exact hsecond_nonneg
    have hEq1 : x 0 + 2 * x 1 = 0 := abs_eq_zero.mp hfirst_zero
    have hEq2 : 3 * x 0 + 4 * x 1 = 0 := abs_eq_zero.mp hsecond_zero
    have hx1 : x 1 = 0 := by
      linarith
    have hx0 : x 0 = 0 := by
      linarith
    ext i
    fin_cases i <;> simp [hx0, hx1]
  · intro hx
    -- Substituting the origin into the explicit formula gives `0`.
    simpa [hx] using example_8_19_objective_zero

-- Proof sketch: `example_8_19_objective` is a norm of the linear image `A x`, hence is
-- nonnegative everywhere. Evaluating at the origin gives `0`, so `0` is a global minimizer on
-- `ℝ²`.
/-- In Example 8.19, the origin is an optimal solution of the unconstrained problem. -/
theorem example_8_19_isMinOn_origin :
    IsMinOn example_8_19_objective Set.univ (0 : E) := by
  -- The explicit objective is nonnegative everywhere and takes the value `0` at the origin.
  rw [isMinOn_iff]
  intro x hx
  simpa [example_8_19_objective_zero] using example_8_19_objective_nonneg x

-- Proof sketch: view the real-valued objective as the everywhere-finite extended-real-valued
-- function `x ↦ (example_8_19_objective x : EReal)`. Use convexity of the `ℓ¹` norm composed with
-- the linear map `example_8_19_matrix.toEuclideanLin`, the fact that the feasible set is
-- `Set.univ`, and `example_8_19_isMinOn_origin` together with `example_8_19_objective_zero` to
-- identify the optimal set and optimal value.
/-- Example 8.19 (4): the example objective satisfies Assumption 8.7 on `ℝ²`, with feasible set
`Set.univ`, optimal set `{0}`, and optimal value `0`. -/
instance example_8_19_isConstrainedConvexProblem :
    IsConstrainedConvexProblem fE Set.univ ({(0 : E)}) 0 := by
  let l1Linear : E →ₗ[ℝ] WithLp 1 (Fin 2 → ℝ) :=
    { toFun := fun x ↦ toLp 1 (fun i : Fin 2 ↦ (example_8_19_matrix.toEuclideanLin x) i)
      map_add' := by
        intro x y
        ext i
        simp [LinearMap.map_add]
      map_smul' := by
        intro a x
        ext i
        simp }
  have hl1Linear_eq :
      (fun x : E ↦ ‖l1Linear x‖) = example_8_19_objective := by
    funext x
    simpa [l1Linear] using (example_8_19_objective_eq_l1_matrix_norm x).symm
  have hcont : Continuous example_8_19_objective := by
    -- A linear map on a finite-dimensional domain is continuous, and norms preserve continuity.
    simpa [hl1Linear_eq] using l1Linear.continuous_of_finiteDimensional.norm
  have hconvex_real :
      ConvexOn ℝ Set.univ example_8_19_objective := by
    have hconv :
        ConvexOn ℝ Set.univ (fun x : E ↦ ‖l1Linear x‖) := by
      -- The norm of a linear image is convex on the whole space.
      simpa [l1Linear, LinearMap.comp_apply] using convexOn_univ_norm.comp_linearMap l1Linear
    -- Rewrite the norm expression to the source-facing objective.
    simpa [hl1Linear_eq] using hconv
  have hminEReal : IsMinOn fE Set.univ (0 : E) := by
    -- The real-valued minimizer statement transports directly to the everywhere-finite `EReal`
    -- lift.
    have hminReal :
        ∀ x ∈ Set.univ, example_8_19_objective (0 : E) ≤ example_8_19_objective x := by
      simpa [isMinOn_iff] using example_8_19_isMinOn_origin
    rw [isMinOn_iff]
    intro x hx
    exact_mod_cast hminReal x hx
  refine
    { toIsProperExtendedRealFunction := Function.toEReal_isProper example_8_19_objective
      closed := Function.toEReal_lowerSemicontinuous_of_continuous hcont
      convex := Function.toEReal_isConvexFunction hconvex_real
      feasible_nonempty := by simp
      feasible_closed := isClosed_univ
      feasible_convex := convex_univ
      feasible_subset_interior_effective_domain := by
        simp [effective_domain]
      optimal_set_eq := ?_
      optimal_set_nonempty := by simp
      optimal_value_isGLB := ?_ }
  · -- The unique minimizer description is exactly the singleton `{0}`.
    ext x
    constructor
    · intro hx
      rcases hx with rfl
      rw [mem_constrained_problem_solutions_iff]
      exact ⟨by simp, hminEReal⟩
    · intro hx
      rw [mem_constrained_problem_solutions_iff, isMinOn_iff] at hx
      rw [Set.mem_singleton_iff]
      have hle : (example_8_19_objective x : EReal) ≤ 0 := by
        simpa [example_8_19_objective_zero] using hx.2 0 (by simp)
      have hge : (0 : EReal) ≤ example_8_19_objective x := by
        change (0 : EReal) ≤ (example_8_19_objective x : EReal)
        exact_mod_cast example_8_19_objective_nonneg x
      have hzeroE : (example_8_19_objective x : EReal) = 0 := le_antisymm hle hge
      have hzero : example_8_19_objective x = 0 := by
        exact_mod_cast hzeroE
      exact (example_8_19_objective_eq_zero_iff_origin x).mp hzero
  · refine ⟨?_, ?_⟩
    · intro y hy
      rcases hy with ⟨x, -, rfl⟩
      change (0 : EReal) ≤ (example_8_19_objective x : EReal)
      exact_mod_cast example_8_19_objective_nonneg x
    · intro y hy
      exact hy ⟨0, by simp, by simp [example_8_19_objective_zero]⟩

-- Proof sketch: the corrected decimal constant `7.2112` is strictly positive.
/-- The corrected Lipschitz constant `7.2112` is positive. -/
theorem example_8_19_lipschitz_constant_pos :
    0 < (7.2112 : ℝ) := by
  -- The displayed decimal constant is strictly positive by direct arithmetic.
  norm_num

/-- Helper for Example 8.19: every vector in the sign box `[-1, 1]^2` is sent by `Aᵀ` to a vector
with Euclidean norm at most `7.2112`. -/
theorem example_8_19_transpose_box_norm_le
    (w : Fin 2 → ℝ) (hw : ∀ i, |w i| ≤ 1) :
    ‖example_8_19_matrix.transpose.toEuclideanLin (toLp 2 w)‖ ≤ (7.2112 : ℝ) := by
  have hcoord0 :
      |(example_8_19_matrix.transpose.toEuclideanLin (toLp 2 w)) 0| ≤ 4 := by
    -- The first coordinate is `w₀ + 3 w₁`, so the triangle inequality bounds it by `4`.
    have hmul0 :
        (example_8_19_matrix.transpose.toEuclideanLin (toLp 2 w)) 0 = w 0 + 3 * w 1 := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, example_8_19_matrix]
    have habs3 : |3 * w 1| = 3 * |w 1| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (3 : ℝ))]
    calc
      |(example_8_19_matrix.transpose.toEuclideanLin (toLp 2 w)) 0|
          = |w 0 + 3 * w 1| := by rw [hmul0]
      _ ≤ |w 0| + |3 * w 1| := abs_add_le _ _
      _ = |w 0| + 3 * |w 1| := by rw [habs3]
      _ ≤ 1 + 3 * 1 := by
            gcongr
            · exact hw 0
            · exact hw 1
      _ = 4 := by norm_num
  have hcoord1 :
      |(example_8_19_matrix.transpose.toEuclideanLin (toLp 2 w)) 1| ≤ 6 := by
    -- The second coordinate is `2 w₀ + 4 w₁`, so the same argument bounds it by `6`.
    have hmul1 :
        (example_8_19_matrix.transpose.toEuclideanLin (toLp 2 w)) 1 = 2 * w 0 + 4 * w 1 := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, example_8_19_matrix]
    have habs2 : |2 * w 0| = 2 * |w 0| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
    have habs4 : |4 * w 1| = 4 * |w 1| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (4 : ℝ))]
    calc
      |(example_8_19_matrix.transpose.toEuclideanLin (toLp 2 w)) 1|
          = |2 * w 0 + 4 * w 1| := by rw [hmul1]
      _ ≤ |2 * w 0| + |4 * w 1| := abs_add_le _ _
      _ = 2 * |w 0| + 4 * |w 1| := by rw [habs2, habs4]
      _ ≤ 2 * 1 + 4 * 1 := by
            gcongr
            · exact hw 0
            · exact hw 1
      _ = 6 := by norm_num
  have hnorm_sq :
      ‖example_8_19_matrix.transpose.toEuclideanLin (toLp 2 w)‖ ^ (2 : ℕ) =
        |(example_8_19_matrix.transpose.toEuclideanLin (toLp 2 w)) 0| ^ (2 : ℕ) +
          |(example_8_19_matrix.transpose.toEuclideanLin (toLp 2 w)) 1| ^ (2 : ℕ) := by
    -- On `ℝ²`, the squared Euclidean norm is the sum of the squared coordinate magnitudes.
    calc
      ‖example_8_19_matrix.transpose.toEuclideanLin (toLp 2 w)‖ ^ (2 : ℕ)
          =
            (example_8_19_matrix.transpose.toEuclideanLin (toLp 2 w) 0) ^ (2 : ℕ) +
              (example_8_19_matrix.transpose.toEuclideanLin (toLp 2 w) 1) ^ (2 : ℕ) := by
                simpa [Fin.sum_univ_two] using
                  EuclideanSpace.real_norm_sq_eq
                    (example_8_19_matrix.transpose.toEuclideanLin (toLp 2 w))
      _ =
            |(example_8_19_matrix.transpose.toEuclideanLin (toLp 2 w)) 0| ^ (2 : ℕ) +
              |(example_8_19_matrix.transpose.toEuclideanLin (toLp 2 w)) 1| ^ (2 : ℕ) := by
                rw [sq_abs, sq_abs]
  have hcoord0_sq :
      |(example_8_19_matrix.transpose.toEuclideanLin (toLp 2 w)) 0| ^ (2 : ℕ) ≤ 16 := by
    nlinarith [abs_nonneg ((example_8_19_matrix.transpose.toEuclideanLin (toLp 2 w)) 0), hcoord0]
  have hcoord1_sq :
      |(example_8_19_matrix.transpose.toEuclideanLin (toLp 2 w)) 1| ^ (2 : ℕ) ≤ 36 := by
    nlinarith [abs_nonneg ((example_8_19_matrix.transpose.toEuclideanLin (toLp 2 w)) 1), hcoord1]
  have hnorm_sq_le :
      ‖example_8_19_matrix.transpose.toEuclideanLin (toLp 2 w)‖ ^ (2 : ℕ) ≤
        (7.2112 : ℝ) ^ (2 : ℕ) := by
    nlinarith [hnorm_sq, hcoord0_sq, hcoord1_sq]
  -- Take square roots via nonnegativity of the norm and the constant.
  exact
    (sq_le_sq₀ (norm_nonneg _) (show 0 ≤ (7.2112 : ℝ) by positivity)).mp
      hnorm_sq_le

-- Proof sketch: use the affine-`ℓ¹` subdifferential description from Proposition 3.19 together
-- with the four possible sign choices of the two residual coordinates to reduce every strong-dual
-- subgradient to one of four explicit vectors. Then bound each of their Euclidean norms by
-- `7.2112`.
/-- Every strong-dual subgradient of the Example 8.19 objective on `ℝ²` has norm at most
`7.2112`. -/
theorem example_8_19_subgradient_norm_le
    {x : E} {g : StrongDual ℝ E}
    (hg : g ∈ strongDualSubdifferential fE x) :
    ‖g‖ ≤ (7.2112 : ℝ) := by
  rcases (InnerProductSpace.toDual ℝ E).surjective g with ⟨z, rfl⟩
  have hz :
      z ∈ euclideanSubdifferentialAt example_8_19_objective x := by
    -- Transport the strong-dual witness back to the Euclidean-side subdifferential.
    rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt]
    simpa using hg
  have hz_affine :
      z ∈ euclideanSubdifferentialAt
        (fun y : E ↦ ∑ i : Fin 2, |(example_8_19_matrix.toEuclideanLin y + 0) i|) x := by
    -- Rewrite the objective into the affine `ℓ¹` normal form with zero offset.
    simpa [example_8_19_objective, example_8_19_matrix, Matrix.toLpLin_apply,
      Fin.sum_univ_two] using hz
  rcases
      (mem_euclidean_subdifferentialAt_affine_l1_iff example_8_19_matrix (0 : E) x z).mp
        hz_affine with
    ⟨w, rfl, hw_sign, hw_zero⟩
  have hw_box : ∀ i, |w i| ≤ 1 := by
    intro i
    by_cases hres : (example_8_19_matrix.toEuclideanLin x + 0) i = 0
    · exact hw_zero i hres
    · rw [hw_sign i hres]
      by_cases hnonneg : 0 ≤ (example_8_19_matrix.toEuclideanLin x + 0) i
      · have hpos : 0 < (example_8_19_matrix.toEuclideanLin x + 0) i := by
          have hne : (0 : ℝ) ≠ (example_8_19_matrix.toEuclideanLin x + 0) i := by
            simpa [eq_comm] using hres
          exact lt_of_le_of_ne hnonneg hne
        have hsign :
            Real.sign ((example_8_19_matrix.toEuclideanLin x + 0) i) = 1 := Real.sign_of_pos hpos
        rw [hsign]
        norm_num
      · have hneg : (example_8_19_matrix.toEuclideanLin x + 0) i < 0 := lt_of_not_ge hnonneg
        have hsign :
            Real.sign ((example_8_19_matrix.toEuclideanLin x + 0) i) = -1 := Real.sign_of_neg hneg
        rw [hsign]
        norm_num
  simpa using example_8_19_transpose_box_norm_le w hw_box

/-- For Example 8.19, the example admits the explicit subgradient norm bound package with
Lipschitz constant `L_f = 7.2112`. -/
def example_8_19_subgradient_norm_bound :
    SubgradientNormBoundOn fE Set.univ where
  L_f := 7.2112
  L_f_pos := example_8_19_lipschitz_constant_pos
  norm_le := fun _ hg ↦ example_8_19_subgradient_norm_le hg

-- Proof sketch: unfold `example_8_19_subgradient_norm_bound` and read off its stored constant.
/-- The bound package for Example 8.19 stores the constant `L_f = 7.2112`. -/
@[simp] theorem example_8_19_subgradient_norm_bound_L_f :
    example_8_19_subgradient_norm_bound.L_f = 7.2112 := by
  rfl

/-- The bound package for Example 8.19 coerces to the stored constant `7.2112`. -/
theorem example_8_19_subgradient_norm_bound_coe :
    (example_8_19_subgradient_norm_bound : ℝ) = 7.2112 := by
  rfl

/-- In Example 8.19, the chosen subgradient direction is the transpose-sign vector
`Aᵀ sgn(Ax)`, using the book convention `sgn 0 = 1`. -/
def example_8_19_subgradient_direction (x : E) : E :=
  example_8_19_matrix.transpose.toEuclideanLin
    (toLp 2 (sgn (fun i ↦ (example_8_19_matrix.toEuclideanLin x) i)))

/-- Helper for Example 8.19: the chosen direction has the displayed two-coordinate sign formula.
-/
theorem example_8_19_subgradient_direction_eq_sign_combination (x : E) :
    example_8_19_subgradient_direction x =
      !₂[
        (if 0 ≤ x 0 + 2 * x 1 then 1 else -1) +
          3 * (if 0 ≤ 3 * x 0 + 4 * x 1 then 1 else -1),
        2 * (if 0 ≤ x 0 + 2 * x 1 then 1 else -1) +
          4 * (if 0 ≤ 3 * x 0 + 4 * x 1 then 1 else -1)
      ] := by
  -- Expand `Aᵀ sgn(Ax)` coordinatewise and rewrite the two sign coordinates explicitly.
  ext i
  fin_cases i
  · simp [example_8_19_subgradient_direction, example_8_19_matrix, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, sgn_apply]
  · simp [example_8_19_subgradient_direction, example_8_19_matrix, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, sgn_apply]

-- Proof sketch: apply Proposition 3.19 (2) to the affine `ℓ¹` objective with matrix
-- `example_8_19_matrix` and zero offset, then rewrite the objective through
-- `example_8_19_objective_eq_l1_matrix_norm`.
/-- For Example 8.19, the chosen vector `v(x)` belongs to the Euclidean subdifferential
`∂ f(x)`. -/
theorem example_8_19_subgradient_direction_mem (x : E) :
    example_8_19_subgradient_direction x ∈
      euclideanSubdifferentialAt example_8_19_objective x := by
  -- Proposition 3.19 provides the sign-vector subgradient for the affine `ℓ¹` representation.
  simpa [example_8_19_subgradient_direction, example_8_19_objective, example_8_19_matrix,
    Matrix.toLpLin_apply, Fin.sum_univ_two] using
    transpose_sgn_mem_subdifferentialAt_affine_l1 example_8_19_matrix (0 : E) x

-- Proof sketch: the two sign coordinates in `sgn (A x)` each take only the values `±1`, so the
-- vector `Aᵀ sgn(Ax)` can only be one of the four explicit combinations obtained from those sign
-- pairs.
/-- In Example 8.19, the chosen subgradient direction takes only the four values
`(-4, -6)`, `(2, 2)`, `(-2, -2)`, and `(4, 6)`. -/
theorem example_8_19_subgradient_direction_mem_four_values (x : E) :
    example_8_19_subgradient_direction x ∈
      {v | v = (!₂[(-4 : ℝ), -6] : E) ∨ v = !₂[(2 : ℝ), 2] ∨
        v = !₂[(-2 : ℝ), -2] ∨ v = !₂[(4 : ℝ), 6]} := by
  -- Only the two residual signs matter, so there are four possible combinations.
  rw [example_8_19_subgradient_direction_eq_sign_combination]
  by_cases h1 : 0 ≤ x 0 + 2 * x 1
  · by_cases h2 : 0 ≤ 3 * x 0 + 4 * x 1
    · right
      right
      right
      norm_num [h1, h2]
    · right
      right
      left
      norm_num [h1, h2]
  · by_cases h2 : 0 ≤ 3 * x 0 + 4 * x 1
    · right
      left
      norm_num [h1, h2]
    · left
      norm_num [h1, h2]

-- Proof sketch: combine `example_8_19_subgradient_direction_mem_four_values` with the fact that
-- each of the four explicit vectors is nonzero.
/-- The chosen subgradient direction in Example 8.19 is never the zero vector. -/
theorem example_8_19_subgradient_direction_ne_zero (x : E) :
    example_8_19_subgradient_direction x ≠ 0 := by
  -- None of the four explicit candidate directions is the zero vector.
  intro hx
  have hmem := example_8_19_subgradient_direction_mem_four_values x
  rcases hmem with h | h | h | h
  · have h0 := congrArg (fun v : E ↦ v 0) h
    simp [hx] at h0
  · have h0 := congrArg (fun v : E ↦ v 0) h
    simp [hx] at h0
  · have h0 := congrArg (fun v : E ↦ v 0) h
    simp [hx] at h0
  · have h0 := congrArg (fun v : E ↦ v 0) h
    simp [hx] at h0

-- Proof sketch: `example_8_19_subgradient_direction_ne_zero` lets us expand `polyak_stepsize`
-- through its nonzero branch, and `(example_8_19_objective x : EReal).toReal =
-- example_8_19_objective x` because the objective is real-valued.
/-- Polyak's stepsize rule for the chosen Example 8.19 subgradient reduces to the displayed
quotient formula. -/
theorem example_8_19_polyak_stepsize_eq_quotient (x : E) :
    polyak_stepsize fE 0 x (example_8_19_subgradient_direction x) =
      example_8_19_objective x /
        ‖example_8_19_subgradient_direction x‖ ^ (2 : ℕ) := by
  simpa using
    polyak_stepsize_of_ne_zero fE 0 x (example_8_19_subgradient_direction x)
      (example_8_19_subgradient_direction_ne_zero x)

/-- For Example 8.19, the subgradient-method update is the Polyak quotient step taken in the
chosen direction `v(x)`. -/
def example_8_19_polyak_update (x : E) : E :=
  x -
    (example_8_19_objective x /
      ‖example_8_19_subgradient_direction x‖ ^ (2 : ℕ)) •
      example_8_19_subgradient_direction x

-- Proof sketch: unfold `example_8_19_polyak_update` and replace the scalar quotient by
-- `polyak_stepsize` using `example_8_19_polyak_stepsize_eq_quotient`.
/-- The Example 8.19 update map is exactly one Polyak step written with the chapter owner
`polyak_stepsize`. -/
theorem example_8_19_polyak_update_eq_polyak_step (x : E) :
    example_8_19_polyak_update x =
      x - polyak_stepsize fE 0 x (example_8_19_subgradient_direction x) •
        example_8_19_subgradient_direction x := by
  simpa [example_8_19_polyak_update] using
    congrArg
      (fun t : ℝ ↦ x - t • example_8_19_subgradient_direction x)
      (example_8_19_polyak_stepsize_eq_quotient x).symm

end

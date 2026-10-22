/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_44
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_23

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin
open scoped RealSymmetricMatrixSpace
open scoped PositiveDefMatrixNorm

variable {m n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

section Proposition725

/-!
# Proposition 7.25

The repository has no local `source/` directory, so statement repair is governed by the item
payload excerpt together with its stored proof text. In that available authority, the displayed
clauses `(7.u556)` and `(7.u557)` are source-faithful, while the quoted clause `(7.u558)` is false
without an additional geometric side condition and no local source text supplies such a repair.
Accordingly, the main labeled entry below is a blocked `#check` surface for the full quoted
proposition shape, while the source-faithful valid clauses and the convex repair are provided
separately as auxiliary API.
-/

/- This item lies in Chapter 7's weighted-matrix-norm / matrix-smoothing domain. The main
source-facing surfaces are the blocked Proposition 7.25 check-only owner and the clause theorems
`(7.u556)` and `(7.u557)`, stated using the chapter owners `squaredLpMatrixNormSmoothing`, `ρ(·)`
on `𝕊^n`, and the weighted norm notation `‖·‖[G]`. The convex distance-bound theorem
`distance_bound_to_weighted_norm_minimizer_of_convex` is retained only as an explicit repair of
the false quoted clause `(7.u558)`, not as an authorized restatement of Proposition 7.25 itself. -/

variable (r p : ℕ+)
variable (G : {G : Matrix (Fin m) (Fin m) ℝ // G.PosDef})
variable (X : E → 𝕊^n) (f : E → ℝ)

variable
  (h_rank_norm_comparison : ∀ M : 𝕊^n,
      Matrix.rank (M : Matrix (Fin n) (Fin n) ℝ) ≤ (r : ℕ) →
        (1 / (r : ℝ)) * ⟪M, M⟫_F ≤ ρ(M) ^ (2 : ℕ) ∧
          ρ(M) ^ (2 : ℕ) ≤ 2 * squaredLpMatrixNormSmoothing p M)
  (hXrank : ∀ y : E, Matrix.rank (X y : Matrix (Fin n) (Fin n) ℝ) ≤ (r : ℕ))
  (hf : ∀ y : E, f y = squaredLpMatrixNormSmoothing p (X y))
  (hGnorm : ∀ y : E, ‖y‖[G] = ρ(X y))

/-- Helper: the weighted norm squared is the quadratic form induced by the
positive-definite matrix. -/
private lemma positiveDefMatrixNorm_sq_eq_matrix_quadratic
    (z : E) :
    ‖z‖[G] ^ (2 : ℕ) = inner ℝ ((Matrix.toEuclideanLin G.1) z) z := by
  -- Rewrite the weighted norm through its matrix quadratic form and discharge the square-root
  -- side condition from positive semidefiniteness.
  have hPosLin : (Matrix.toEuclideanLin G.1).IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr G.2.posSemidef
  have hnonneg : 0 ≤ inner ℝ ((Matrix.toEuclideanLin G.1) z) z := by
    simpa [real_inner_comm] using hPosLin.inner_nonneg_right z
  rw [positiveDefMatrixNorm_def, Real.sq_sqrt hnonneg]

/-- Helper: the matrix quadratic form attached to the weighted norm is
symmetric in its vector arguments. -/
private lemma positiveDefMatrixNorm_matrix_quadratic_symm
    (x y : E) :
    inner ℝ ((Matrix.toEuclideanLin G.1) x) y =
      inner ℝ ((Matrix.toEuclideanLin G.1) y) x := by
  -- Positive operators are symmetric, so the cross term may be swapped before scalar algebra.
  have hPosLin : (Matrix.toEuclideanLin G.1).IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr G.2.posSemidef
  simpa [real_inner_comm] using hPosLin.isSymmetric x y

/-- Helper: the half squared weighted norm satisfies the exact affine
combination identity behind strong convexity. -/
private lemma half_weighted_norm_sq_affine_combo_exact
    (x y : E) (a b : ℝ) (hab : a + b = 1) :
    (1 / 2 : ℝ) * ‖a • x + b • y‖[G] ^ (2 : ℕ) =
      a * ((1 / 2 : ℝ) * ‖x‖[G] ^ (2 : ℕ)) +
        b * ((1 / 2 : ℝ) * ‖y‖[G] ^ (2 : ℕ)) -
          a * b * ((1 / 2 : ℝ) * ‖x - y‖[G] ^ (2 : ℕ)) := by
  let T : E →ₗ[ℝ] E := Matrix.toEuclideanLin G.1
  have hsq_x : ‖x‖[G] ^ (2 : ℕ) = inner ℝ (T x) x := by
    simpa [T] using positiveDefMatrixNorm_sq_eq_matrix_quadratic G x
  have hsq_y : ‖y‖[G] ^ (2 : ℕ) = inner ℝ (T y) y := by
    simpa [T] using positiveDefMatrixNorm_sq_eq_matrix_quadratic G y
  have hsq_diff : ‖x - y‖[G] ^ (2 : ℕ) = inner ℝ (T (x - y)) (x - y) := by
    simpa [T] using positiveDefMatrixNorm_sq_eq_matrix_quadratic G (x - y)
  have hcross :
      inner ℝ (T y) x = inner ℝ (T x) y := by
    simpa [T] using positiveDefMatrixNorm_matrix_quadratic_symm G y x
  have hcombo_expand :
      inner ℝ (T (a • x + b • y)) (a • x + b • y) =
        a ^ (2 : ℕ) * inner ℝ (T x) x +
          (a * b) * inner ℝ (T x) y +
            (a * b) * inner ℝ (T y) x +
              b ^ (2 : ℕ) * inner ℝ (T y) y := by
    -- Expand the quadratic form of the affine combination into diagonal and cross terms.
    simp [T, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, pow_two]
    ring
  have hdiff_expand :
      inner ℝ (T (x - y)) (x - y) =
        inner ℝ (T x) x - 2 * inner ℝ (T x) y + inner ℝ (T y) y := by
    -- Expand the squared difference and use symmetry to merge the two cross terms.
    calc
      inner ℝ (T (x - y)) (x - y)
          = inner ℝ (T x) x - inner ℝ (T x) y - inner ℝ (T y) x +
              inner ℝ (T y) y := by
                simp [sub_eq_add_neg, T, inner_add_left, inner_add_right, inner_neg_left,
                  inner_neg_right]
                ring_nf
      _ = inner ℝ (T x) x - 2 * inner ℝ (T x) y + inner ℝ (T y) y := by
            rw [hcross]
            ring
  calc
    (1 / 2 : ℝ) * ‖a • x + b • y‖[G] ^ (2 : ℕ)
        = (1 / 2 : ℝ) * inner ℝ (T (a • x + b • y)) (a • x + b • y) := by
            rw [positiveDefMatrixNorm_sq_eq_matrix_quadratic G (a • x + b • y)]
    _ =
        (1 / 2 : ℝ) *
          (a ^ (2 : ℕ) * inner ℝ (T x) x +
            (a * b) * inner ℝ (T x) y +
              (a * b) * inner ℝ (T y) x +
                b ^ (2 : ℕ) * inner ℝ (T y) y) := by
                  rw [hcombo_expand]
    _ =
        a * ((1 / 2 : ℝ) * inner ℝ (T x) x) +
          b * ((1 / 2 : ℝ) * inner ℝ (T y) y) -
            a * b *
              ((1 / 2 : ℝ) *
                (inner ℝ (T x) x - 2 * inner ℝ (T x) y + inner ℝ (T y) y)) := by
                  rw [hcross]
                  have hb' : b = 1 - a := by linarith
                  rw [hb']
                  ring
    _ =
        a * ((1 / 2 : ℝ) * ‖x‖[G] ^ (2 : ℕ)) +
          b * ((1 / 2 : ℝ) * ‖y‖[G] ^ (2 : ℕ)) -
            a * b * ((1 / 2 : ℝ) * inner ℝ (T (x - y)) (x - y)) := by
              rw [← hdiff_expand, ← hsq_x, ← hsq_y]
    _ =
        a * ((1 / 2 : ℝ) * ‖x‖[G] ^ (2 : ℕ)) +
          b * ((1 / 2 : ℝ) * ‖y‖[G] ^ (2 : ℕ)) -
            a * b * ((1 / 2 : ℝ) * ‖x - y‖[G] ^ (2 : ℕ)) := by
              rw [← hsq_diff]

/-- Helper: the half squared weighted norm is `1`-strongly convex on every
convex feasible set with respect to the weighted norm. -/
private lemma half_weighted_norm_sq_strongConvexOnWith
    {Q : Set E} (hQ_convex : Convex ℝ Q) :
    StrongConvexOnWith
      (positiveDefMatrixNorm G.1 G.2)
      1
      Q
      (fun y : E ↦ (1 / 2 : ℝ) * ‖y‖[G] ^ (2 : ℕ)) := by
  refine ⟨hQ_convex, by norm_num, ?_⟩
  intro x hx y hy a b ha hb hab
  -- The quadratic identity is exact, so the strong-convexity inequality follows by equality.
  exact le_of_eq <|
    half_weighted_norm_sq_affine_combo_exact G x y a b hab

/-- Helper: a minimizer of the weighted norm also minimizes its half squared
version on the same feasible set. -/
private lemma isMinOn_half_weighted_norm_sq_of_isMinOn_norm
    {Q : Set E} {x0 : E}
    (hx0 : IsMinOn (fun y : E ↦ ‖y‖[G]) Q x0) :
    IsMinOn (fun y : E ↦ (1 / 2 : ℝ) * ‖y‖[G] ^ (2 : ℕ)) Q x0 := by
  rw [isMinOn_iff] at hx0 ⊢
  intro y hy
  -- Squaring preserves the ordering because both weighted norms are nonnegative.
  have hnorm : ‖x0‖[G] ≤ ‖y‖[G] := hx0 y hy
  have hx0_nonneg : 0 ≤ ‖x0‖[G] := by
    exact apply_nonneg (positiveDefMatrixNorm G.1 G.2) x0
  have hy_nonneg : 0 ≤ ‖y‖[G] := by
    exact apply_nonneg (positiveDefMatrixNorm G.1 G.2) y
  nlinarith

include p X h_rank_norm_comparison hXrank hf hGnorm

/-- Helper: an attained constrained minimizer realizes the owner optimal
value after applying `EReal.toReal`. -/
private lemma optimalValueToReal_eq_of_mem_argmin
    {Q : Set E} {y : E} (hy : y ∈ argmin[Q] f) :
    ((.mk Q f : SetConstrainedMinimizationProblem E).optimalValue).toReal = f y := by
  -- Rewrite the owner optimal value by the attained minimizer and then remove `toReal`.
  have hopt :
      (.mk Q f : SetConstrainedMinimizationProblem E).optimalValue = (f y : EReal) := by
    simpa using
      SetConstrainedMinimizationProblem.optimalValue_eq_of_mem_argmin
        (.mk Q f : SetConstrainedMinimizationProblem E) hy
  simpa using congrArg EReal.toReal hopt

-- Proof sketch: apply the rank-bounded source comparison `(7.u555)` in chapter notation to `X y`,
-- use its right-hand inequality together with `r ≥ 1`, rewrite `f y` via `hf`, and substitute
-- `‖y‖[G] = ρ(X y)` via `hGnorm`.
/-- Helper for source line `(7.u556)` on the chapter owners
`squaredLpMatrixNormSmoothing` and `‖·‖[G]`. -/
theorem quadratic_lower_bound_of_rank_bounded_schatten_model
    (y : E) :
    (1 / (2 * (r : ℝ))) * ‖y‖[G] ^ (2 : ℕ) ≤ f y := by
  -- Apply the rank-bounded source comparison to the matrix model `X y`.
  have hGnorm_y : ‖y‖[G] = ρ(X y) := hGnorm y
  have hf_y : f y = squaredLpMatrixNormSmoothing p (X y) := hf y
  have hcomparison :
      ρ(X y) ^ (2 : ℕ) ≤ 2 * squaredLpMatrixNormSmoothing p (X y) :=
    (h_rank_norm_comparison (X y) (hXrank y)).2
  have hhalf :
      (1 / 2 : ℝ) * ρ(X y) ^ (2 : ℕ) ≤ squaredLpMatrixNormSmoothing p (X y) := by
    linarith
  have hr_ge_one : (1 : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast r.property
  have hρ_nonneg : 0 ≤ ρ(X y) ^ (2 : ℕ) := by
    positivity
  have hcoeff :
      (1 / (2 * (r : ℝ)) : ℝ) ≤ (1 / 2 : ℝ) := by
    have hr_pos : (0 : ℝ) < (r : ℝ) := by positivity
    have hmul : (2 : ℝ) ≤ 2 * (r : ℝ) := by nlinarith
    exact one_div_le_one_div_of_le (by positivity) hmul
  have hbase :
      (1 / (2 * (r : ℝ))) * ρ(X y) ^ (2 : ℕ) ≤ squaredLpMatrixNormSmoothing p (X y) :=
    (mul_le_mul_of_nonneg_right hcoeff hρ_nonneg).trans hhalf
  -- Then rewrite the model norm and objective back to the source-facing quantities.
  calc
    (1 / (2 * (r : ℝ))) * ‖y‖[G] ^ (2 : ℕ)
        = (1 / (2 * (r : ℝ))) * ρ(X y) ^ (2 : ℕ) := by rw [hGnorm_y]
    _ ≤ squaredLpMatrixNormSmoothing p (X y) := hbase
    _ = f y := by rw [← hf_y]

/-- Auxiliary clause `(7.u556)` from the Proposition 7.25 source payload: for every `y`,
`(1 / (2r)) ‖y‖_G^2 ≤ f_p(y)` under the displayed rank-bounded Schatten-smoothing model. -/
theorem proposition_7_25_clause_7u556
    (y : E) :
    (1 / (2 * (r : ℝ))) * ‖y‖[G] ^ (2 : ℕ) ≤ f y :=
  quadratic_lower_bound_of_rank_bounded_schatten_model
    r p G X f h_rank_norm_comparison hXrank hf hGnorm y

-- Proof sketch: the source line specializes the pointwise lower bound to an objective minimizer
-- `yStar ∈ argmin[Q] f`, derives `Q.Nonempty` from `mem_constrainedArgmin_iff` when needed, and
-- identifies the constrained optimal value with `f yStar` through the Chapter 1 owner bridge
-- `optimalValue_eq_of_mem_argmin`.
/-- Helper for source line `(7.u557)` at an attained constrained minimizer. -/
theorem quadratic_lower_bound_at_feasible_weighted_norm_infimum
    {Q : Set E} {yStar : E} (hyStar : yStar ∈ argmin[Q] f) :
    (1 / (2 * (r : ℝ))) * ‖yStar‖[G] ^ (2 : ℕ) ≤
      ((.mk Q f : SetConstrainedMinimizationProblem E).optimalValue).toReal := by
  -- First apply the pointwise quadratic lower bound at the constrained minimizer `yStar`.
  have hpoint :
      (1 / (2 * (r : ℝ))) * ‖yStar‖[G] ^ (2 : ℕ) ≤ f yStar :=
    quadratic_lower_bound_of_rank_bounded_schatten_model
      r p G X f h_rank_norm_comparison hXrank hf hGnorm yStar
  have hopt :
      ((.mk Q f : SetConstrainedMinimizationProblem E).optimalValue).toReal = f yStar := by
    exact optimalValueToReal_eq_of_mem_argmin p X f h_rank_norm_comparison hXrank hf hGnorm hyStar
  -- Then identify the attained objective value with the owner optimal value.
  calc
    (1 / (2 * (r : ℝ))) * ‖yStar‖[G] ^ (2 : ℕ) ≤ f yStar := hpoint
    _ = ((.mk Q f : SetConstrainedMinimizationProblem E).optimalValue).toReal := by
      symm
      exact hopt

/-- Auxiliary clause `(7.u557)` from the Proposition 7.25 source payload: if
`y_p^* ∈ argmin[Q] f_p`, then `(1 / (2r)) ‖y_p^*‖_G^2 ≤ f_p^*`. -/
theorem proposition_7_25_clause_7u557
    {Q : Set E} {yStar : E} (hyStar : yStar ∈ argmin[Q] f) :
    (1 / (2 * (r : ℝ))) * ‖yStar‖[G] ^ (2 : ℕ) ≤
      ((.mk Q f : SetConstrainedMinimizationProblem E).optimalValue).toReal :=
  quadratic_lower_bound_at_feasible_weighted_norm_infimum
    r p G X f h_rank_norm_comparison hXrank hf hGnorm hyStar

/-! Proposition 7.25 [Quadratic lower bound and distance bound].

The payload authority for this repo snapshot quotes all three displayed consequences `(7.u556)`,
`(7.u557)`, and `(7.u558)`. The third clause `(7.u558)` is false without an additional geometric
side condition, and there is no local `source/` file authorizing which missing hypothesis should
be added here. The source-facing owner therefore stays as a blocked check-only surface for the
full quoted proposition, while the valid clauses and the convex repair remain auxiliary API below.
-/
#check
  (∀ y : E, (1 / (2 * (r : ℝ))) * ‖y‖[G] ^ (2 : ℕ) ≤ f y) ∧
    (∀ {Q : Set E} {yStar : E},
      yStar ∈ argmin[Q] f →
        (1 / (2 * (r : ℝ))) * ‖yStar‖[G] ^ (2 : ℕ) ≤
          ((.mk Q f : SetConstrainedMinimizationProblem E).optimalValue).toReal) ∧
    (∀ {Q : Set E} {yStar x0 : E},
      yStar ∈ argmin[Q] f →
        x0 ∈ argmin[Q] (fun y : E ↦ ‖y‖[G]) →
          (1 / 2 : ℝ) * ‖yStar - x0‖[G] ^ (2 : ℕ) ≤
            (r : ℝ) * ((.mk Q f : SetConstrainedMinimizationProblem E).optimalValue).toReal)

/-
The theorem below implements an explicit convex repair of the false quoted source line `(7.u558)`.
-/

/-- Auxiliary convex repair of source line `(7.u558)`: if `Q` is convex,
`y_p^* ∈ argmin[Q] f_p`, and `x_0 ∈ argmin[Q] ‖·‖_G`, then
`(1 / 2) ‖y_p^* - x_0‖_G^2 ≤ r f_p^*`, with
`f_p^* = ((.mk Q f : SetConstrainedMinimizationProblem E).optimalValue).toReal`.

This is the source-proof-supported convex form of clause `(7.u558)`, separated
out as same-file auxiliary API. -/
theorem distance_bound_to_weighted_norm_minimizer_of_convex
    {Q : Set E} (hQ_convex : Convex ℝ Q) {yStar x0 : E} (hyStar : yStar ∈ argmin[Q] f)
    (hx0 : x0 ∈ argmin[Q] (fun y : E ↦ ‖y‖[G])) :
    (1 / 2 : ℝ) * ‖yStar - x0‖[G] ^ (2 : ℕ) ≤
      (r : ℝ) *
        ((.mk Q f : SetConstrainedMinimizationProblem E).optimalValue).toReal := by
  rcases mem_constrainedArgmin_iff.mp hyStar with ⟨hyStar_mem, _⟩
  rcases mem_constrainedArgmin_iff.mp hx0 with ⟨hx0_mem, hx0_min⟩
  have hx0_sq_min :
      IsMinOn (fun y : E ↦ (1 / 2 : ℝ) * ‖y‖[G] ^ (2 : ℕ)) Q x0 :=
    isMinOn_half_weighted_norm_sq_of_isMinOn_norm G hx0_min
  have hstrong :
      StrongConvexOnWith
        (positiveDefMatrixNorm G.1 G.2)
        1
        Q
        (fun y : E ↦ (1 / 2 : ℝ) * ‖y‖[G] ^ (2 : ℕ)) :=
    half_weighted_norm_sq_strongConvexOnWith G hQ_convex
  have hdistance_to_norm_sq :
      (1 / 2 : ℝ) * ‖yStar - x0‖[G] ^ (2 : ℕ) ≤
        (1 / 2 : ℝ) * ‖yStar‖[G] ^ (2 : ℕ) := by
    have hquad :
        (1 / 2 : ℝ) * ‖yStar‖[G] ^ (2 : ℕ) ≥
          (1 / 2 : ℝ) * ‖x0‖[G] ^ (2 : ℕ) +
            (1 / 2 : ℝ) * ‖yStar - x0‖[G] ^ (2 : ℕ) := by
      simpa using
        hstrong.quadratic_growth_of_isMinOn_of_mem hx0_mem hx0_sq_min yStar hyStar_mem
    have hx0_sq_nonneg : 0 ≤ (1 / 2 : ℝ) * ‖x0‖[G] ^ (2 : ℕ) := by
      positivity
    linarith
  have hnorm_sq_to_opt :
      (1 / 2 : ℝ) * ‖yStar‖[G] ^ (2 : ℕ) ≤
        (r : ℝ) * ((.mk Q f : SetConstrainedMinimizationProblem E).optimalValue).toReal := by
    have hlower :
        (1 / (2 * (r : ℝ))) * ‖yStar‖[G] ^ (2 : ℕ) ≤
          ((.mk Q f : SetConstrainedMinimizationProblem E).optimalValue).toReal :=
      quadratic_lower_bound_at_feasible_weighted_norm_infimum
        r p G X f h_rank_norm_comparison hXrank hf hGnorm hyStar
    have hr_pos : (0 : ℝ) < (r : ℝ) := by
      positivity
    nlinarith
  exact hdistance_to_norm_sq.trans hnorm_sq_to_opt

omit p X h_rank_norm_comparison hXrank hf hGnorm

end Proposition725

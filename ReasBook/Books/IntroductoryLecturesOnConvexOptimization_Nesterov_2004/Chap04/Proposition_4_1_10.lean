/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Proposition_4_1_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section
open scoped CubicRegularizedDiagonalInvariants

variable {n : ℕ} [NeZero n]

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 4.1.10 belongs to the diagonal quadratic-minimization interface.

Sampled owner declarations:
* `quadraticObjective` for the shifted quadratic `q_λ`;
* `UnconstrainedQuadraticMinimizationProblem.minimizer` and
  `UnconstrainedQuadraticMinimizationProblem.minimizer_unique` for the canonical quadratic
  minimizer / uniqueness owner;
* `cubicRegularizedDiagonalMinimum`, `cubicRegularizedMinimalDiagonalIndices`, and
  `cubicRegularizedMinimalDiagonalGradientSquare` for `H_min`, `I*`, and `G²`;
* `cubicRegularizedDiagonalResolvent_isMinOn` in `Proposition_4_1_9`, the upstream owner-level
  minimizer theorem for the diagonal resolvent point.

Source/core/bridge triage:
* source-facing: the coordinate description of the minimizer of `q_λ` in the degenerate case
  `G² = 0`;
* core/canonical: the shifted diagonal quadratic together with its resolvent point
  `-(diag(Hdiag + λ))⁻¹ g`;
* bridge/view: the coordinate formula for that resolvent and the equivalence between being a
  minimizer and satisfying the textbook coordinate formula.

Primitive data:
* the diagonal data `Hdiag`, gradient `g`, and shift `λ`;
* the strict interior inequality `λ > -H_min`.

Derived API:
* the coordinate formula for the diagonal resolvent point;
* the upstream owner-level minimizer theorem for that resolvent;
* the source-facing `iff` statement in the degenerate case `G² = 0`.

This file therefore keeps Proposition 4.1.10 as a source-facing bridge theorem, but exposes the
canonical diagonal resolvent minimizer through the upstream owner theorem in
`Proposition_4_1_9` instead of owning a second copy here. -/

section

variable (g : E) (Hdiag : Fin n → ℝ) (lam : ℝ)

local notation "A" => Matrix.diagonal fun i ↦ Hdiag i + lam

/-- Evaluating the diagonal resolvent point `-(diag(Hdiag + λ))⁻¹ g` gives the coordinate formula
`-g i / (H_i + λ)`. -/
theorem cubicRegularizedDiagonalResolvent_apply
    (hlam : -H_min[Hdiag] < lam) (i : Fin n) :
    (-((A)⁻¹).mulVec g) i = -g i / (Hdiag i + lam) := by
  -- The interior condition makes each shifted diagonal entry positive, hence invertible.
  have hpos : 0 < Hdiag i + lam := by
    have hmin_le : H_min[Hdiag] ≤ Hdiag i :=
      diagonalMinimum_le_entry (Hdiag := Hdiag) i
    linarith
  have hne : Hdiag i + lam ≠ 0 := ne_of_gt hpos
  -- Expand the diagonal inverse and then evaluate the diagonal matrix-vector product.
  rw [show A = Matrix.diagonal (fun j ↦ Hdiag j + lam) by rfl, Matrix.inv_diagonal]
  rw [Matrix.mulVec_diagonal]
  -- Over `ℝ`, the ring inverse agrees with the usual inverse on nonzero scalars.
  simp [Ring.inverse_eq_inv, div_eq_mul_inv, hne, mul_comm]

/-- Helper for Proposition 4.1.10: if the active squared gradient mass vanishes, then each active
coordinate of `g` vanishes. -/
lemma active_coordinates_vanish_of_zeroMinimalGradientSquare
    (hG : G²[g;Hdiag] = 0)
    {i : Fin n} (hi : i ∈ I*[Hdiag]) :
    g i = 0 := by
  -- The active squared mass is a sum of nonnegative squares, so every active summand is zero.
  have hsum_zero :
      ∀ j ∈ I*[Hdiag], (g j) ^ (2 : ℕ) = 0 := by
    have hzero :
        Finset.sum (I*[Hdiag]) (fun j ↦ (g j) ^ (2 : ℕ)) = 0 := by
      simpa [cubicRegularizedMinimalDiagonalGradientSquare] using hG
    exact (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _).mp hzero
  have hi_sq : (g i) ^ (2 : ℕ) = 0 :=
    hsum_zero i hi
  -- Over `ℝ`, a square is zero exactly when the original coordinate is zero.
  exact sq_eq_zero_iff.mp <| by simpa [pow_two] using hi_sq

/-- Helper for Proposition 4.1.10: the displayed source formula is equivalent to equality with
the canonical diagonal resolvent point. -/
lemma displayed_coordinate_formula_iff_eq_resolvent
    (hG : G²[g;Hdiag] = 0)
    (hlam : -H_min[Hdiag] < lam)
    (h : E) :
    (∀ i : Fin n,
        h i =
          if i ∈ I*[Hdiag] then
            0
          else
            -g i / (Hdiag i + lam)) ↔
      h = (-((A)⁻¹).mulVec g) := by
  constructor
  · intro hh
    -- Compare coordinates and split according to whether the index is active.
    ext i
    by_cases hi : i ∈ I*[Hdiag]
    · have hg_zero : g i = 0 :=
        active_coordinates_vanish_of_zeroMinimalGradientSquare
          (g := g) (Hdiag := Hdiag) hG hi
      rw [hh i, if_pos hi]
      rw [cubicRegularizedDiagonalResolvent_apply
        (g := g) (Hdiag := Hdiag) (lam := lam) hlam i]
      simp [hg_zero]
    · rw [hh i, if_neg hi]
      rw [cubicRegularizedDiagonalResolvent_apply
        (g := g) (Hdiag := Hdiag) (lam := lam) hlam i]
  · intro hh
    intro i
    by_cases hi : i ∈ I*[Hdiag]
    · have hg_zero : g i = 0 :=
        active_coordinates_vanish_of_zeroMinimalGradientSquare
          (g := g) (Hdiag := Hdiag) hG hi
      rw [hh, if_pos hi]
      rw [cubicRegularizedDiagonalResolvent_apply
        (g := g) (Hdiag := Hdiag) (lam := lam) hlam i]
      simp [hg_zero]
    · rw [hh, if_neg hi]
      rw [cubicRegularizedDiagonalResolvent_apply
        (g := g) (Hdiag := Hdiag) (lam := lam) hlam i]

/- The owner-level minimizer statement for the diagonal resolvent point is already the upstream
theorem `cubicRegularizedDiagonalResolvent_isMinOn`. -/
recall cubicRegularizedDiagonalResolvent_isMinOn

-- Proof sketch: `λ > -H_min` makes the shifted diagonal Hessian strictly positive, so the
-- shifted quadratic has the canonical resolvent minimizer above. The hypothesis `G² = 0`
-- forces `g i = 0` on `I*`, and the resolvent coordinate formula then reduces exactly to the
-- textbook description `h i = 0` on `I*` and `h i = -g i / (H_i + λ)` off `I*`. Uniqueness of
-- the quadratic minimizer supplies the converse direction.
/-- Proposition 4.1.10: if `G² = 0` and `λ > -H_min`, then a vector `h` minimizes the shifted
diagonal quadratic `q_λ` on `ℝⁿ` exactly when its coordinates satisfy
`h i = 0` on `I*` and `h i = -g i / (H_i + λ)` off `I*`. -/
theorem cubicRegularizedDiagonal_isMinOn_iff
    (hG : G²[g;Hdiag] = 0)
    (hlam : -H_min[Hdiag] < lam)
    (h : E) :
    IsMinOn (quadraticObjective 0 g A) Set.univ h ↔
      ∀ i : Fin n,
        h i =
          if i ∈ I*[Hdiag] then
            0
          else
            -g i / (Hdiag i + lam) := by
  constructor
  · intro hh
    -- The upstream uniqueness theorem identifies every minimizer with the canonical resolvent.
    have hres : h = (-((A)⁻¹).mulVec g) := by
      simpa [shiftedQuadraticObjective, shiftedDiagonalMatrix, diagonalResolventPoint,
        diagonal_shift_eq_diagonal_add_scalar (Hdiag := Hdiag) lam,
        Matrix.toEuclideanLin_apply] using
        (cubicRegularizedDiagonalResolvent_unique
          (g := g) (Hdiag := Hdiag) (lam := lam) hlam h hh)
    -- Translate resolvent equality into the displayed coordinate formula.
    exact (displayed_coordinate_formula_iff_eq_resolvent
      (g := g) (Hdiag := Hdiag) (lam := lam) hG hlam h).mpr hres
  · intro hh
    have hres : h = (-((A)⁻¹).mulVec g) :=
      (displayed_coordinate_formula_iff_eq_resolvent
        (g := g) (Hdiag := Hdiag) (lam := lam) hG hlam h).mp hh
    -- Once `h` is the canonical resolvent, the upstream minimizer theorem applies directly.
    simpa [hres, shiftedQuadraticObjective, shiftedDiagonalMatrix, diagonalResolventPoint,
      diagonal_shift_eq_diagonal_add_scalar (Hdiag := Hdiag) lam,
      Matrix.toEuclideanLin_apply] using
      (cubicRegularizedDiagonalResolvent_isMinOn
        (g := g) (Hdiag := Hdiag) (lam := lam) lam hlam)

end

/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_27

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient

/- Text 6.1.5.2 lies in Chapter 6's finite-dimensional log-sum-exp stabilization domain.

Sampled owner-style declarations:
- `coordinateMaximum` in `Chap06/Proposition_6_23`, the chapter owner for the maximal coordinate;
- `centeredByCoordinateMaximum` in `Chap06/Proposition_6_23`, the canonical max-centered vector;
- `η` in `Chap06/Definition_6_27`, the recalled log-sum-exp potential;
- `eta_eq_coordinateMaximum_add_eta_centered` and
  `gradient_eta_eq_gradient_eta_centered` in `Chap06/Proposition_6_23`, the canonical stable
  shift identities.

Best owner abstraction:
- source-facing: the stable max-shift identity for the scaled log-sum-exp potential;
- core/canonical: `coordinateMaximum`, `centeredByCoordinateMaximum`, `η`, and the two stable
  shift theorems from `Proposition_6_23`;
- bridge/view: the coordinate observations that the centered vector is nonpositive and has a zero
  coordinate.

This item reuses the chapter owners directly for the stable shift formulas and keeps only the
centered-coordinate consequences as local statement skeletons.
-/

section

variable {m : ℕ} [NeZero m]

local notation "U" => EuclideanSpace ℝ (Fin m)

/- Text 6.1.5.2-Stable Log-Sum-Exp Shift Trick: if `v` is obtained by subtracting the maximal
coordinate `coordinateMaximum u` from every component of `u`, then the scaled log-sum-exp
potential satisfies the stable identity
`η μ u = coordinateMaximum u + η μ (centeredByCoordinateMaximum u)`. -/
recall eta_eq_coordinateMaximum_add_eta_centered

-- Proof sketch: this item's main statement is exactly the Chapter 6 owner theorem already
-- recalled above, so the proof is the recalled stable max-shift identity itself.
/-- Text 6 1 5 2 Stable Log Sum Exp Shift Trick: subtracting the maximal coordinate from every
component of `u` produces the numerically stable centered vector, and the scaled log-sum-exp
potential splits as the maximal coordinate plus the centered log-sum-exp. -/
theorem stable_log_sum_exp_shift_trick
    (μ : {μ : ℝ // 0 < μ}) (u : U) :
    η μ u = coordinateMaximum u + η μ (centeredByCoordinateMaximum u) := by
  simpa using eta_eq_coordinateMaximum_add_eta_centered μ u

/-- Helper for Text 6 1 5 2 Stable Log Sum Exp Shift Trick: each coordinate of `u` is bounded
above by its maximal coordinate. -/
lemma coordinate_le_coordinateMaximum (u : U) (j : Fin m) :
    u j ≤ coordinateMaximum u := by
  -- Expanding the maximum reduces the claim to the standard finite-sup bound.
  simpa [coordinateMaximum_def] using
    (Finset.le_sup' (s := Finset.univ) (f := fun k : Fin m ↦ u k) (h := Finset.mem_univ j))

/-- Helper for Text 6 1 5 2 Stable Log Sum Exp Shift Trick: the finite maximum of the coordinates
is attained at some index. -/
lemma coordinateMaximum_eq_coordinate_of_argmax (u : U) :
    ∃ j : Fin m, coordinateMaximum u = u j := by
  -- The finite supremum over `Fin m` is attained by one coordinate.
  rcases
      Finset.exists_mem_eq_sup'
        (s := Finset.univ)
        (H := Finset.univ_nonempty)
        (f := fun j : Fin m ↦ u j) with
    ⟨j, _, hj⟩
  exact ⟨j, by simpa [coordinateMaximum_def] using hj⟩

-- Proof sketch: `coordinateMaximum u` is the maximum of the finite coordinate family, so each
-- coordinate `u j` is bounded above by it. Rewriting
-- `centeredByCoordinateMaximum u j = u j - coordinateMaximum u` gives the claim.
/-- Every coordinate of the vector centered by its maximal coordinate is nonpositive. -/
theorem centeredByCoordinateMaximum_nonpos
    (u : U) (j : Fin m) :
    centeredByCoordinateMaximum u j ≤ 0 := by
  -- Rewriting the centered coordinate reduces the claim to subtracting an upper bound.
  rw [centeredByCoordinateMaximum_apply]
  exact sub_nonpos.mpr (coordinate_le_coordinateMaximum u j)

-- Proof sketch: on the finite index type `Fin m`, the maximum defining `coordinateMaximum u` is
-- attained. At a maximizing coordinate, subtracting `coordinateMaximum u` leaves `0`.
/-- The vector centered by its maximal coordinate has at least one zero coordinate. -/
theorem centeredByCoordinateMaximum_exists_eq_zero
    (u : U) :
    ∃ j : Fin m, centeredByCoordinateMaximum u j = 0 := by
  rcases coordinateMaximum_eq_coordinate_of_argmax u with ⟨j, hj⟩
  use j
  -- At a maximizing coordinate, centering subtracts the coordinate from itself.
  rw [centeredByCoordinateMaximum_apply, hj]
  simp

/- Subtracting the maximal coordinate from every component preserves the gradient of the scaled
log-sum-exp potential, so the same stable shift trick applies to gradient computation. -/
recall gradient_eta_eq_gradient_eta_centered

end

/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_32
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open InnerProductSpace
open scoped BigOperators SeminormDualNorm SeminormOperatorNorm

/- Proposition 6.15 lies in the finite-dimensional `ℓ₁`/`ℓ∞` matrix-game norm domain.

Sampled owner declarations:
* `Seminorm.primalDualOperatorNorm`, the chapter owner for induced norms between separated source
  and target seminorm geometries;
* `EuclideanSpace.l1Seminorm`, the project owner for the coordinate `ℓ₁` seminorm on `ℝⁿ`;
* `Matrix.toEuclideanLin`, the canonical Euclidean realization of a matrix action;
* `dotProduct`, the source-facing row-pairing expression for matrix rows.

Best owner abstraction:
* source-facing: the supremum of the maximal absolute row pairing over the `ℓ₁` unit ball;
* core/canonical: `Seminorm.primalDualOperatorNorm` applied to
  `((InnerProductSpace.toDual ℝ _).toLinearMap.comp A.toEuclideanLin)`;
* bridge/view: the passage from the canonical operator norm to the entrywise maximum
  `max_{i,j} |A^{(i,j)}|`.

Primitive data:
* the real matrix `A`.

Derived API:
* the row-pairing supremum formula;
* the evaluation of the canonical `ℓ₁ → ℓ∞` operator norm by the maximal absolute entry;
* the entropy-distance rewrite of the primal-dual gap estimate from the norm form to the
  max-entry form.
-/

universe u v

variable {m n : ℕ+}

local notation "EN" => EuclideanSpace ℝ (Fin (n : ℕ))
local notation "EM" => EuclideanSpace ℝ (Fin (m : ℕ))

/-- Helper for Proposition 6.15: the sign choice attached to a real scalar has unit absolute value
and turns the scalar into its absolute value after multiplication. -/
private theorem sign_choice_abs_and_mul_eq_abs (a : ℝ) :
    let s : ℝ := if 0 ≤ a then 1 else -1
    |s| = 1 ∧ a * s = |a| := by
  by_cases ha : 0 ≤ a
  · simp [ha, abs_of_nonneg ha]
  · have hneg : a < 0 := lt_of_not_ge ha
    simp [ha, abs_of_neg hneg]

/-- Helper for Proposition 6.15: the `ℓ₁` seminorm of a signed standard basis vector is the
absolute value of its scalar coefficient. -/
-- Proof sketch: the coordinate `ℓ₁` seminorm is the sum of the absolute coordinate values, and a
-- scalar multiple of `Pi.single i 1` has exactly one nonzero coordinate.
private theorem l1Seminorm_smul_single_one_eq_abs {k : ℕ+}
    (i : Fin (k : ℕ)) (s : ℝ) :
    EuclideanSpace.l1Seminorm (k : ℕ)
        (s • (EuclideanSpace.single i 1 : EuclideanSpace ℝ (Fin (k : ℕ)))) = |s| := by
  -- Rewrite the `ℓ₁` seminorm as a coordinate sum and collapse the unique nonzero term.
  rw [EuclideanSpace.l1Seminorm_apply]
  rw [Finset.sum_eq_single i]
  · simp [smul_eq_mul]
  · intro j _ hji
    simp [smul_eq_mul, hji]
  · simp

/-- Helper for Proposition 6.15: pairing with a signed standard basis vector extracts the chosen
coordinate times the scalar. -/
-- Proof sketch: rewrite the vector as `Pi.single i s`, then use the standard `dotProduct_single`
-- computation.
private theorem dotProduct_smul_single_one {k : ℕ+}
    (v : EuclideanSpace ℝ (Fin (k : ℕ))) (i : Fin (k : ℕ)) (s : ℝ) :
    dotProduct v (s • (EuclideanSpace.single i 1 : EuclideanSpace ℝ (Fin (k : ℕ)))) = v i * s := by
  -- Expand the coordinate sum and collapse the unique nonzero coordinate.
  rw [dotProduct, Finset.sum_eq_single i]
  · simp [smul_eq_mul]
  · intro j _ hji
    simp [smul_eq_mul, hji]
  · simp

/-- Helper for Proposition 6.15: pairing with the signed standard basis vector at a coordinate
recovers the absolute value of that coordinate. -/
-- Proof sketch: evaluate the dot product against the signed basis vector by
-- `dotProduct_smul_single_one`, then use the sign-choice identity turning `v i * s` into
-- `|v i|`.
private theorem dotProduct_sign_single_eq_abs_coord {k : ℕ+}
    (v : EuclideanSpace ℝ (Fin (k : ℕ))) (i : Fin (k : ℕ)) :
    let s : ℝ := if 0 ≤ v i then 1 else -1
    dotProduct v (s • (EuclideanSpace.single i 1 : EuclideanSpace ℝ (Fin (k : ℕ)))) = |v i| := by
  -- Evaluate the pairing on the one-coordinate witness and collapse the chosen sign.
  let s : ℝ := if 0 ≤ v i then 1 else -1
  have hdot :
      dotProduct v (s • (EuclideanSpace.single i 1 : EuclideanSpace ℝ (Fin (k : ℕ)))) =
        v i * s := by
    simpa [s] using (dotProduct_smul_single_one v i s)
  have habs : v i * s = |v i| := by
    simpa [s] using (sign_choice_abs_and_mul_eq_abs (v i)).2
  exact hdot.trans habs

/-- Helper for Proposition 6.15: every pairing of `y` with an `ℓ₁`-unit vector has absolute value
bounded by the largest absolute coordinate of `y`. -/
-- Proof sketch: expand the Euclidean pairing as a coordinate sum, bound the absolute value of the
-- sum by the sum of absolute values, dominate each coefficient by the coordinatewise maximum, and
-- finish with the `ℓ₁` unit-ball hypothesis on `x`.
private theorem l1_pairing_le_sup_nnabs (y : EM) {x : EM}
    (hx : EuclideanSpace.l1Seminorm (m : ℕ) x ≤ 1) :
    |inner ℝ y x| ≤ ↑((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦ Real.nnabs (y j)) := by
  let C : ℝ := ↑((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦ Real.nnabs (y j))
  have hcoord :
      ∀ i : Fin (m : ℕ), |y i| ≤ C := by
    intro i
    have hi :
        (Real.nnabs (y i) : ℝ) ≤
          ↑((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦ Real.nnabs (y j)) := by
      exact_mod_cast
        (Finset.le_sup (s := (Finset.univ : Finset (Fin (m : ℕ))))
          (f := fun j ↦ Real.nnabs (y j)) (Finset.mem_univ i))
    simpa [C, Real.coe_nnabs] using hi
  have hsum_abs :
      |inner ℝ y x| ≤ ∑ i : Fin (m : ℕ), |y i| * |x i| := by
    -- Rewrite the inner product as a coordinate sum and bound it by the sum of absolute values.
    calc
      |inner ℝ y x| = |∑ i : Fin (m : ℕ), x i * y i| := by
        simpa [dotProduct] using congrArg abs (EuclideanSpace.inner_eq_star_dotProduct y x)
      _ ≤ ∑ i : Fin (m : ℕ), |y i * x i| := by
        simpa [mul_comm, dotProduct] using
          (Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset (Fin (m : ℕ))))
            (f := fun i : Fin (m : ℕ) ↦ x i * y i))
      _ = ∑ i : Fin (m : ℕ), |y i| * |x i| := by
        simp [abs_mul]
  have hdom :
      ∑ i : Fin (m : ℕ), |y i| * |x i| ≤ ∑ i : Fin (m : ℕ), C * |x i| := by
    -- Bound each coefficient `|y i|` by the coordinatewise maximum `C`.
    refine Finset.sum_le_sum ?_
    intro i _
    exact mul_le_mul_of_nonneg_right (hcoord i) (abs_nonneg _)
  have hunit :
      ∑ i : Fin (m : ℕ), C * |x i| ≤ C := by
    have hC_nonneg : 0 ≤ C := by
      exact_mod_cast (bot_le : (⊥ : NNReal) ≤ (Finset.univ : Finset (Fin (m : ℕ))).sup
        fun j ↦ Real.nnabs (y j))
    calc
      ∑ i : Fin (m : ℕ), C * |x i| = C * ∑ i : Fin (m : ℕ), |x i| := by
        rw [Finset.mul_sum]
      _ = C * EuclideanSpace.l1Seminorm (m : ℕ) x := by
        rw [EuclideanSpace.l1Seminorm_apply]
        simp [Real.norm_eq_abs]
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left hx hC_nonneg
      _ = C := by ring
  exact hsum_abs.trans (hdom.trans hunit)

/-- Helper for Proposition 6.15: on the `ℓ₁` unit ball, the row-pairing supremum is bounded by
the largest absolute matrix entry. -/
-- Proof sketch: bound each row pairing by the largest matrix entry using the same coordinatewise
-- `ℓ₁` estimate, then take the finite supremum over rows.
private theorem matrix_row_sup_le_max_abs_entry
    (A : Matrix (Fin (m : ℕ)) (Fin (n : ℕ)) ℝ) {x : EN}
    (hx : EuclideanSpace.l1Seminorm (n : ℕ) x ≤ 1) :
    ↑((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
      Real.nnabs (dotProduct (A j) x)) ≤
      ↑((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
        (Finset.univ : Finset (Fin (n : ℕ))).sup fun i ↦ Real.nnabs (A j i)) := by
  -- Bound each row pairing by the largest absolute coordinate in that row.
  have hrows :
      ∀ j : Fin (m : ℕ),
        (Real.nnabs (dotProduct (A j) x) :
            ℝ) ≤
          ↑((Finset.univ : Finset (Fin (n : ℕ))).sup fun i ↦ Real.nnabs (A j i)) := by
    intro j
    simpa [Real.coe_nnabs, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
      (l1_pairing_le_sup_nnabs (y := (WithLp.toLp 2 (A j) : EN)) (x := x) hx)
  -- Then take the finite supremum over rows and compare each row maximum with the global maximum.
  exact_mod_cast
    (Finset.sup_le_iff.2 fun j _ ↦
      (show Real.nnabs (dotProduct (A j) x) ≤
          (Finset.univ : Finset (Fin (m : ℕ))).sup fun j' ↦
            (Finset.univ : Finset (Fin (n : ℕ))).sup fun i ↦ Real.nnabs (A j' i) from
        (show Real.nnabs (dotProduct (A j) x) ≤
            (Finset.univ : Finset (Fin (n : ℕ))).sup fun i ↦ Real.nnabs (A j i) from
          by
            exact_mod_cast (hrows j)).trans
          (Finset.le_sup (s := (Finset.univ : Finset (Fin (m : ℕ))))
            (f := fun j' ↦ (Finset.univ : Finset (Fin (n : ℕ))).sup fun i ↦ Real.nnabs (A j' i))
            (Finset.mem_univ j))))

/-- Helper for Proposition 6.15: evaluating the Euclidean matrix action at a row index gives the
corresponding row pairing. -/
-- Proof sketch: unfold the matrix action to `mulVec` and then simplify the resulting coordinate
-- sum to the row `dotProduct`.
private theorem matrix_toEuclideanLin_apply_eq_dotProduct
    (A : Matrix (Fin (m : ℕ)) (Fin (n : ℕ)) ℝ) (x : EN) (j : Fin (m : ℕ)) :
    (A.toEuclideanLin x) j = dotProduct (A j) x := by
  rw [Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  simp [Matrix.mulVec, dotProduct]

/-- Helper for Proposition 6.15: transporting the canonical matrix output back from the dual
identifies each coordinate with the corresponding row pairing. -/
-- Proof sketch: evaluate the `toDual`/`symm` cancellation on the standard basis vector at the
-- chosen coordinate, then simplify that basis-vector pairing to the matrix row `dotProduct`.
private theorem matrix_toDual_comp_coord_eq_dotProduct
    (A : Matrix (Fin (m : ℕ)) (Fin (n : ℕ)) ℝ) (x : EN) (j : Fin (m : ℕ)) :
    ((toDual ℝ EM).symm (((toDual ℝ EM).toLinearMap.comp A.toEuclideanLin) x)) j =
      dotProduct (A j) x := by
  -- Evaluate the transported dual slice on the `j`-th standard basis vector.
  have hcoord := (InnerProductSpace.toDual_symm_apply
    (x := (EuclideanSpace.single j 1 : EM))
    (y := (((toDual ℝ EM).toLinearMap.comp A.toEuclideanLin) x)))
  -- Simplify the basis-vector pairing to the `j`-th output coordinate and then to the row pairing.
  simpa [LinearMap.comp_apply, matrix_toEuclideanLin_apply_eq_dotProduct, dotProduct] using hcoord

/-- Helper for Proposition 6.15: the dual norm of the coordinate `ℓ₁` seminorm is the coordinate
`ℓ∞` norm, i.e. the largest absolute coordinate. -/
-- Proof sketch: bound every pairing on the `ℓ₁` unit ball by the largest absolute coordinate
-- using `abs_sum_le_sum_abs`, then attain that bound with the signed standard basis vector
-- supported at a maximizing coordinate.
private theorem l1_dualNorm_eq_finset_sup_nnabs (y : EM) :
    ‖y‖[EuclideanSpace.l1Seminorm (m : ℕ),*] =
      ↑((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦ Real.nnabs (y j)) := by
  classical
  let S : Set ℝ := (fun x : EM ↦ inner ℝ y x) '' {x | EuclideanSpace.l1Seminorm (m : ℕ) x ≤ 1}
  let C : ℝ := ↑((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦ Real.nnabs (y j))
  -- Route correction: evaluate the extremal witness through `dotProduct`, not by unfolding scalar
  -- coordinate inner products.
  rw [Seminorm.dualNorm_apply]
  change sSup S = C
  have hS_nonempty : S.Nonempty := by
    -- The `ℓ₁` unit ball contains `0`, so the support-function image is nonempty.
    refine ⟨0, ⟨0, by simp, by simp⟩⟩
  have hS_bdd : BddAbove S := by
    -- The previously established pairing bound supplies a uniform upper bound on the image set.
    refine ⟨C, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    exact (le_abs_self _).trans (l1_pairing_le_sup_nnabs (y := y) (x := x) hx)
  refine le_antisymm ?_ ?_
  · -- Every value in the support image is bounded above by the coordinatewise maximum.
    refine csSup_le hS_nonempty ?_
    rintro z ⟨x, hx, rfl⟩
    exact (le_abs_self _).trans (l1_pairing_le_sup_nnabs (y := y) (x := x) hx)
  · obtain ⟨j0, -, hj0⟩ := Finset.exists_mem_eq_sup
        (s := (Finset.univ : Finset (Fin (m : ℕ)))) Finset.univ_nonempty
        (fun j : Fin (m : ℕ) ↦ Real.nnabs (y j))
    let s : ℝ := if 0 ≤ y j0 then 1 else -1
    let x0 : EM := s • (EuclideanSpace.single j0 1 : EM)
    have hs_abs : |s| = 1 := by
      -- The chosen sign has unit absolute value.
      simpa [s] using (sign_choice_abs_and_mul_eq_abs (y j0)).1
    have hx0_norm : EuclideanSpace.l1Seminorm (m : ℕ) x0 = 1 := by
      -- The signed standard basis vector lies on the boundary of the `ℓ₁` unit ball.
      calc
        EuclideanSpace.l1Seminorm (m : ℕ) x0 = |s| := by
          simpa [x0] using
            (l1Seminorm_smul_single_one_eq_abs (k := m) (i := j0) (s := s))
        _ = 1 := hs_abs
    have hx0 : EuclideanSpace.l1Seminorm (m : ℕ) x0 ≤ 1 := by
      simpa [hx0_norm] using le_rfl
    have hyx0 : inner ℝ y x0 = |y j0| := by
      -- Rewrite the pairing as a dot product and evaluate it on the signed basis witness.
      calc
        inner ℝ y x0 = dotProduct y x0 := by
          simpa [dotProduct_comm] using (EuclideanSpace.inner_eq_star_dotProduct y x0)
        _ = y j0 * s := by
          simpa [x0, PiLp.ofLp_single] using
            (dotProduct_smul_single_one (v := y) (i := j0) (s := s))
        _ = |y j0| := by
          simpa [s] using (sign_choice_abs_and_mul_eq_abs (y j0)).2
    have hCeq : C = |y j0| := by
      -- The chosen coordinate attains the finite maximum defining `C`.
      dsimp [C]
      rw [hj0]
      exact Real.coe_nnabs _
    have hx0_mem : inner ℝ y x0 ∈ S := by
      exact ⟨x0, hx0, rfl⟩
    -- Insert the maximizing witness into the support image to obtain the reverse inequality.
    exact le_csSup_of_le hS_bdd hx0_mem (by rw [hCeq, hyx0])

/-- Helper for Proposition 6.15: the dual norm of the canonical matrix output equals the maximal
absolute row pairing at the same vector. -/
-- Proof sketch: rewrite the dual norm as the largest absolute coordinate of the matrix output,
-- then replace each coordinate by the corresponding matrix-row `dotProduct`.
private theorem matrix_comp_output_l1_dualNorm_eq_row_sup
    (A : Matrix (Fin (m : ℕ)) (Fin (n : ℕ)) ℝ) (x : EN) :
    ‖A.toEuclideanLin x‖[EuclideanSpace.l1Seminorm (m : ℕ),*] =
      ↑((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
        Real.nnabs (dotProduct (A j) x)) := by
  -- Rewrite the matrix output norm as the supremum of its absolute coordinates.
  rw [l1_dualNorm_eq_finset_sup_nnabs]
  -- Then identify each coordinate with the corresponding row pairing of `A`.
  simp [matrix_toEuclideanLin_apply_eq_dotProduct]

/-- Helper for Proposition 6.15: the transported canonical matrix slice has dual norm equal to the
maximal absolute row pairing at the same vector. -/
-- Proof sketch: simplify the `toDual` transport in the canonical operator-norm slice to the
-- ordinary matrix output, then reuse `matrix_comp_output_l1_dualNorm_eq_row_sup`.
private theorem transported_matrix_output_l1_dualNorm_eq_row_sup
    (A : Matrix (Fin (m : ℕ)) (Fin (n : ℕ)) ℝ) (x : EN) :
    ‖(toDual ℝ EM).symm ((((toDual ℝ EM).toLinearMap.comp A.toEuclideanLin) x))‖[EuclideanSpace.l1Seminorm (m : ℕ),*] =
      ↑((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
        Real.nnabs (dotProduct (A j) x)) := by
  -- Collapse the `toDual` transport in the canonical slice to the matrix output itself.
  calc
    ‖(toDual ℝ EM).symm ((((toDual ℝ EM).toLinearMap.comp A.toEuclideanLin) x))‖[EuclideanSpace.l1Seminorm (m : ℕ),*] =
        ‖A.toEuclideanLin x‖[EuclideanSpace.l1Seminorm (m : ℕ),*] := by
          simp [LinearMap.comp_apply]
    _ = ↑((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
          Real.nnabs (dotProduct (A j) x)) :=
      matrix_comp_output_l1_dualNorm_eq_row_sup (A := A) (x := x)

/-- The supremum of the maximal absolute row pairing over the `ℓ₁` unit ball equals the largest
absolute entry of the matrix. -/
-- Proof sketch: for any `x` in the `ℓ₁` unit ball, each row pairing `dotProduct (A j) x` is
-- bounded by the maximal absolute entry of `A`. For the reverse inequality, use a signed
-- standard basis vector supported at a column where `A` attains that maximal absolute entry.
theorem matrix_l1_rowPairing_sSup_eq_max_abs_entry
    (A : Matrix (Fin (m : ℕ)) (Fin (n : ℕ)) ℝ) :
    sSup ((fun x : EN ↦
      ↑((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
        Real.nnabs (dotProduct (A j) x))) ''
      {x | EuclideanSpace.l1Seminorm (n : ℕ) x ≤ 1}) =
      ↑((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
        (Finset.univ : Finset (Fin (n : ℕ))).sup fun i ↦ Real.nnabs (A j i)) := by
  classical
  let C :=
    (Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
      (Finset.univ : Finset (Fin (n : ℕ))).sup fun i ↦ Real.nnabs (A j i)
  have hS_nonempty :
      ((fun x : EN ↦
        (Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
          Real.nnabs (dotProduct (A j) x)) '' {x | EuclideanSpace.l1Seminorm (n : ℕ) x ≤ 1}).Nonempty := by
    -- The zero vector belongs to the `ℓ₁` unit ball, so the row-pairing image is nonempty.
    refine ⟨0, ⟨0, by simp, by simp⟩⟩
  have hS_bdd :
      BddAbove ((fun x : EN ↦
        (Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
          Real.nnabs (dotProduct (A j) x)) '' {x | EuclideanSpace.l1Seminorm (n : ℕ) x ≤ 1}) := by
    -- Every row-pairing value on the `ℓ₁` unit ball is bounded by the largest matrix entry.
    refine ⟨C, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    exact_mod_cast (matrix_row_sup_le_max_abs_entry (A := A) hx)
  refine le_antisymm ?_ ?_
  · -- The forward inequality is the uniform row-wise estimate from `matrix_row_sup_le_max_abs_entry`.
    refine csSup_le hS_nonempty ?_
    rintro z ⟨x, hx, rfl⟩
    exact matrix_row_sup_le_max_abs_entry (A := A) hx
  · obtain ⟨j0, -, hj0⟩ := Finset.exists_mem_eq_sup
        (s := (Finset.univ : Finset (Fin (m : ℕ)))) Finset.univ_nonempty
        (fun j : Fin (m : ℕ) ↦ (Finset.univ : Finset (Fin (n : ℕ))).sup
          fun i ↦ Real.nnabs (A j i))
    obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_sup
        (s := (Finset.univ : Finset (Fin (n : ℕ)))) Finset.univ_nonempty
        (fun i : Fin (n : ℕ) ↦ Real.nnabs (A j0 i))
    let s : ℝ := if 0 ≤ A j0 i0 then 1 else -1
    let x0 : EN := s • (EuclideanSpace.single i0 1 : EN)
    have hs_abs : |s| = 1 := by
      -- The chosen sign has unit absolute value.
      simpa [s] using (sign_choice_abs_and_mul_eq_abs (A j0 i0)).1
    have hx0_norm : EuclideanSpace.l1Seminorm (n : ℕ) x0 = 1 := by
      -- The column witness is again a signed standard basis vector of `ℓ₁` norm one.
      calc
        EuclideanSpace.l1Seminorm (n : ℕ) x0 = |s| := by
          simpa [x0] using
            (l1Seminorm_smul_single_one_eq_abs (k := n) (i := i0) (s := s))
        _ = 1 := hs_abs
    have hx0 : EuclideanSpace.l1Seminorm (n : ℕ) x0 ≤ 1 := by
      simpa [hx0_norm] using le_rfl
    have hrow_eval : dotProduct (WithLp.toLp 2 (A j0) : EN) x0 = |A j0 i0| := by
      -- Evaluate the maximizing row on the signed basis witness by the same signed-coordinate
      -- extraction lemma used in the dual-norm proof.
      calc
        dotProduct (WithLp.toLp 2 (A j0) : EN) x0 = A j0 i0 * s := by
          simpa [x0, PiLp.ofLp_single] using
            (dotProduct_smul_single_one (v := (WithLp.toLp 2 (A j0) : EN)) (i := i0) (s := s))
        _ = |A j0 i0| := by
          simpa [s] using (sign_choice_abs_and_mul_eq_abs (A j0 i0)).2
    have hrow_abs :
        Real.nnabs (dotProduct (A j0) x0) = Real.nnabs (A j0 i0) := by
      -- Pass to `NNReal` after evaluating the witness row pairing explicitly.
      apply NNReal.eq
      rw [Real.coe_nnabs, hrow_eval]
      simp
    have hC_le_fx0 :
        C ≤
          ((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
            Real.nnabs (dotProduct (A j) x0)) := by
      -- The outer row supremum dominates the maximizing row `j0`, which in turn realizes `C`.
      calc
        C = Real.nnabs (A j0 i0) := by
          dsimp [C]
          simpa [hj0] using hi0
        _ = Real.nnabs (dotProduct (A j0) x0) := hrow_abs.symm
        _ ≤
            ((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
              Real.nnabs (dotProduct (A j) x0)) := by
            exact
              Finset.le_sup (s := (Finset.univ : Finset (Fin (m : ℕ))))
                (f := fun j ↦ Real.nnabs (dotProduct (A j) x0)) (Finset.mem_univ j0)
    have hx0_mem :
        ((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
            Real.nnabs (dotProduct (A j) x0)) ∈
          ((fun x : EN ↦
            ((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
              Real.nnabs (dotProduct (A j) x))) ''
            {x | EuclideanSpace.l1Seminorm (n : ℕ) x ≤ 1}) := by
      exact ⟨x0, hx0, rfl⟩
    -- Insert the maximizing column witness into the support image to recover the reverse bound.
    exact le_csSup_of_le hS_bdd hx0_mem hC_le_fx0

/-- The canonical `ℓ₁ → ℓ∞` operator norm of a real matrix is the largest absolute value of its
entries. -/
-- Proof sketch: rewrite the canonical operator norm as the source-facing supremum of the maximal
-- absolute row pairing over the `ℓ₁` unit ball, then apply
-- `matrix_l1_rowPairing_sSup_eq_max_abs_entry`.
theorem matrix_l1_to_linfty_operatorNorm_eq_max_abs_entry
    (A : Matrix (Fin (m : ℕ)) (Fin (n : ℕ)) ℝ) :
    ‖(toDual ℝ EM).toLinearMap.comp A.toEuclideanLin‖[EuclideanSpace.l1Seminorm (n : ℕ) ⇀
        EuclideanSpace.l1Seminorm (m : ℕ),*] =
      ↑((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
        (Finset.univ : Finset (Fin (n : ℕ))).sup fun i ↦ Real.nnabs (A j i)) := by
  -- Rewrite the bundled operator norm to the source-facing support function of row pairings.
  rw [Seminorm.primalDualOperatorNorm_def]
  -- Route correction: compare the two image sets directly, since the rewrite happens under
  -- `Set.image`.
  calc
    sSup
        ((fun x : EN ↦
            ‖(toDual ℝ EM).symm ((((toDual ℝ EM).toLinearMap.comp A.toEuclideanLin) x))‖[EuclideanSpace.l1Seminorm (m : ℕ),*]) ''
          {x | EuclideanSpace.l1Seminorm (n : ℕ) x ≤ 1}) =
      sSup
        ((fun x : EN ↦
            ↑((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
              Real.nnabs (dotProduct (A j) x))) ''
          {x | EuclideanSpace.l1Seminorm (n : ℕ) x ≤ 1}) := by
      apply congrArg sSup
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        -- Replace the transported slice value by the row-pairing formula at the same witness.
        exact ⟨x, hx, by
          simpa using
            (transported_matrix_output_l1_dualNorm_eq_row_sup (A := A) (x := x)).symm⟩
      · rintro ⟨x, hx, rfl⟩
        -- The same pointwise identity also provides the reverse inclusion.
        exact ⟨x, hx, by
          simpa using
            transported_matrix_output_l1_dualNorm_eq_row_sup (A := A) (x := x)⟩
    _ = ↑((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
          (Finset.univ : Finset (Fin (n : ℕ))).sup fun i ↦ Real.nnabs (A j i)) :=
      by
        let S : Set NNReal :=
          ((fun x : EN ↦
              (Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
                Real.nnabs (dotProduct (A j) x)) ''
            {x | EuclideanSpace.l1Seminorm (n : ℕ) x ≤ 1})
        have hrow :
            sSup S =
              (Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
                (Finset.univ : Finset (Fin (n : ℕ))).sup fun i ↦ Real.nnabs (A j i) := by
          simpa [S] using matrix_l1_rowPairing_sSup_eq_max_abs_entry (A := A)
        -- Coerce the native `NNReal` support-function identity to the real-valued operator norm.
        have hcoe :
            sSup
                (((fun x : EN ↦
                    ↑((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
                      Real.nnabs (dotProduct (A j) x))) ''
                  {x | EuclideanSpace.l1Seminorm (n : ℕ) x ≤ 1}) : Set ℝ) =
              (↑(sSup S) : ℝ) := by
          simpa [S, Set.image_image, Function.comp] using (NNReal.coe_sSup S).symm
        have hrow_real :
            (↑(sSup S) : ℝ) =
              ↑((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
                (Finset.univ : Finset (Fin (n : ℕ))).sup fun i ↦ Real.nnabs (A j i)) := by
          exact congrArg (fun t : NNReal ↦ (t : ℝ)) hrow
        exact hcoe.trans hrow_real

/-- Proposition 6.15 [Chapter6_1.json:39]: if the entropy-distance matrix-game gap estimate is
written with the canonical `ℓ₁ → ℓ∞` operator norm of `A`, then the same estimate can be written
with the largest absolute matrix entry `max_{i,j} |A^{(i,j)}|`. -/
-- Proof sketch: keep the lower endpoint `0` unchanged and rewrite only the operator-norm factor
-- in the assumed upper bound using `matrix_l1_to_linfty_operatorNorm_eq_max_abs_entry`.
theorem matrix_game_entropy_gap_mem_Icc_max_abs_entry_bound
    {X : Type u} {U : Type v}
    (A : Matrix (Fin (m : ℕ)) (Fin (n : ℕ)) ℝ)
    (f : X → ℝ) (φ : U → ℝ) (xHat : X) (uHat : U) (N : ℕ+)
    (hnonneg : 0 ≤ f xHat - φ uHat)
    (hgap_le :
      f xHat - φ uHat ≤
        ((4 * Real.sqrt (Real.log (n : ℝ) * Real.log (m : ℝ))) /
            Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) *
          ‖(toDual ℝ EM).toLinearMap.comp A.toEuclideanLin‖[EuclideanSpace.l1Seminorm (n : ℕ) ⇀
            EuclideanSpace.l1Seminorm (m : ℕ),*]) :
    f xHat - φ uHat ∈
      Set.Icc 0
        (((4 * Real.sqrt (Real.log (n : ℝ) * Real.log (m : ℝ))) /
            Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) *
          ↑((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
            (Finset.univ : Finset (Fin (n : ℕ))).sup fun i ↦ Real.nnabs (A j i))) := by
  -- Keep the nonnegative lower endpoint and rewrite only the upper endpoint via the norm formula.
  have hgap_le' :
      f xHat - φ uHat ≤
        ((4 * Real.sqrt (Real.log (n : ℝ) * Real.log (m : ℝ))) /
            Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) *
          ↑((Finset.univ : Finset (Fin (m : ℕ))).sup fun j ↦
            (Finset.univ : Finset (Fin (n : ℕ))).sup fun i ↦ Real.nnabs (A j i)) := by
    simpa [matrix_l1_to_linfty_operatorNorm_eq_max_abs_entry (A := A)] using hgap_le
  exact ⟨hnonneg, hgap_le'⟩

end

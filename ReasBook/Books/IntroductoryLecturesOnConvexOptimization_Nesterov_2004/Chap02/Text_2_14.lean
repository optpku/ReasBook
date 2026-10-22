/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Text_2_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Text_2_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_20
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_29

-- Declarations for this item will be appended below by the statement pipeline.

open scoped SmoothConvex

noncomputable section

variable {n : ℕ}

/- Text 2.14 is organized around the owner objective `quadraticHardInstanceFamily L k` and its
canonical stationary point `quadraticHardInstanceStationaryPoint k` from Text 2.13.

Sampled owner-style declarations in this domain:
- `quadraticHardInstanceFamily_mem_smooth_convex_objective` in `Text_2_11`
- `ConvexOn.isMinOn_iff_variational_inequality_of_hasGradientAt` in `Theorem_2_29`
- `SetConstrainedMinimizationProblem.optimalValue` and
  `SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn` in `Definition_2_20`

Primitive data:
- the hard-instance objective `quadraticHardInstanceFamily (L : ℝ) k`.

Derived API:
- the canonical stationary point is a global minimizer;
- the canonical whole-space owner problem on `Set.univ`;
- evaluating the objective at that minimizer gives the closed-form optimal value.

This file therefore keeps the source-facing minimizer and optimal-value statements, but derives
them through the existing smooth-convex owner abstraction and the Chapter 1/2 optimal-value owner
API rather than a parallel local `sInf`-based value wrapper. The raw infimum-of-range identity is
kept only as a companion bridge.
-/

/-- The canonical stationary point of the quadratic hard instance is a global minimizer of the
owner objective `quadraticHardInstanceFamily (L : ℝ) k`. -/
-- Proof sketch: combine
-- `quadraticHardInstanceFamily_mem_smooth_convex_objective` with
-- `quadraticHardInstanceStationaryPoint_hasGradientAt_zero`; convex differentiable functions on
-- `Set.univ` are globally minimized by specializing the constrained first-order owner theorem to
-- the zero-gradient case.
theorem quadraticHardInstanceStationaryPoint_isMinOn
    (L : NNReal) (k : Fin n) :
    IsMinOn (quadraticHardInstanceFamily (L : ℝ) k) Set.univ
      (quadraticHardInstanceStationaryPoint k) := by
  have hf := quadraticHardInstanceFamily_mem_smooth_convex_objective L k
  have hstat :
      HasGradientAt (quadraticHardInstanceFamily (L : ℝ) k) 0
        (quadraticHardInstanceStationaryPoint k) :=
    quadraticHardInstanceStationaryPoint_hasGradientAt_zero (L : ℝ) k
  refine (hf.convexOn.isMinOn_iff_variational_inequality_of_hasGradientAt (by simp) hstat).2 ?_
  intro x hx
  simp

private theorem quadraticHardInstanceFamily_stationaryPoint_eq_smoothLowerBoundFunction
    (L : NNReal) (k : Fin n) :
    quadraticHardInstanceFamily (L : ℝ) k (quadraticHardInstanceStationaryPoint k) =
      smoothLowerBoundFunction (L : ℝ) (Nat.succPNat k.1)
        (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k.1)) := by
  simp [quadraticHardInstanceFamily, quadraticHardInstanceStationaryPoint]
  congr
  ext i
  change (quadraticHardInstanceStationaryPoint k) (Fin.castLE (Nat.succ_le_of_lt k.2) i) = _
  have hi : Fin.castLE (Nat.succ_le_of_lt k.2) i ≤ k :=
    Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ i.2)
  simp [quadraticHardInstanceStationaryPoint_apply, hi]
  ring

/-- Helper for Text 2.14: splitting a path-tridiagonal matrix entry into diagonal, forward, and
backward neighbor contributions gives the scalar identity used to read off each row. -/
private theorem pathTridiagonal_entry_mul_eq_diag_sub_neighbors
    {m : ℕ} (y : EuclideanSpace ℝ (Fin (m + 1))) (i j : Fin (m + 1)) :
    pathTridiagonalMatrix (Nat.succPNat m) i j * y j =
      (if i = j then 2 * y j else 0) -
      (if (i : ℕ) + 1 = (j : ℕ) then y j else 0) -
      (if (j : ℕ) + 1 = (i : ℕ) then y j else 0) := by
  -- Split the matrix entry into the three source-proof cases: diagonal, forward edge, and
  -- backward edge.
  by_cases hij : i = j
  · subst hij
    simp [pathTridiagonalMatrix_apply]
  · by_cases hnext : (i : ℕ) + 1 = (j : ℕ)
    · have hprev : ¬ (j : ℕ) + 1 = (i : ℕ) := by
        omega
      simp [pathTridiagonalMatrix_apply, hij, hnext, hprev]
    · by_cases hprev : (j : ℕ) + 1 = (i : ℕ)
      · simp [pathTridiagonalMatrix_apply, hij, hnext, hprev]
      · simp [pathTridiagonalMatrix_apply, hij, hnext, hprev]

/-- Helper for Text 2.14: the first row of the path tridiagonal system is `2 y₀ - y₁`. -/
private theorem pathTridiagonal_mulVec_apply_head
    (k : ℕ) (y : EuclideanSpace ℝ (Fin (k + 2))) :
    (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (k + 1))) y) 0 =
      2 * y 0 - y ⟨1, by omega⟩ := by
  -- Expand the first row and isolate the only two nonzero contributions.
  change ∑ j : Fin (k + 2), pathTridiagonalMatrix (Nat.succPNat (k + 1)) 0 j * y j = _
  rw [show (∑ j : Fin (k + 2), pathTridiagonalMatrix (Nat.succPNat (k + 1)) 0 j * y j) =
      (∑ j : Fin (k + 2), ((if (0 : Fin (k + 2)) = j then 2 * y j else 0) -
        (if (1 : ℕ) = (j : ℕ) then y j else 0) -
        (if (j : ℕ) + 1 = (0 : ℕ) then y j else 0))) by
      refine Finset.sum_congr rfl ?_
      intro j hj
      simpa using pathTridiagonal_entry_mul_eq_diag_sub_neighbors y 0 j]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hdiag : (∑ j : Fin (k + 2), if (0 : Fin (k + 2)) = j then 2 * y j else 0) = 2 * y 0 := by
    rw [Fintype.sum_eq_single 0]
    · simp
    · intro j hj
      have hneq : ¬ (0 : Fin (k + 2)) = j := by
        simpa using hj.symm
      simp [hneq]
  have hnext : (∑ j : Fin (k + 2), if (1 : ℕ) = (j : ℕ) then y j else 0) = y ⟨1, by omega⟩ := by
    rw [Fintype.sum_eq_single ⟨1, by omega⟩]
    · simp
    · intro j hj
      have hne : (j : ℕ) ≠ 1 := by
        intro hEq
        apply hj
        ext
        simpa using hEq
      have hneq : ¬ (1 : ℕ) = (j : ℕ) := by
        simpa [eq_comm] using hne
      simp [hneq]
  have hprev : (∑ j : Fin (k + 2), if (j : ℕ) + 1 = (0 : ℕ) then y j else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    simp
  -- The remaining scalar expression is exactly the head equation.
  rw [hdiag, hnext, hprev]
  ring_nf

/-- Helper for Text 2.14: every interior row of the path tridiagonal system is
`2 yᵢ - yᵢ₋₁ - yᵢ₊₁`. -/
private theorem pathTridiagonal_mulVec_apply_middle
    (k : ℕ) (y : EuclideanSpace ℝ (Fin (k + 2))) (t : ℕ)
    (ht0 : t < k + 2) (ht1 : t + 1 < k + 2) (ht2 : t + 2 < k + 2) :
    (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (k + 1))) y) ⟨t + 1, ht1⟩ =
      2 * y ⟨t + 1, ht1⟩ - y ⟨t, ht0⟩ - y ⟨t + 2, ht2⟩ := by
  -- Expand an interior row and keep only the diagonal and two adjacent entries.
  change ∑ j : Fin (k + 2), pathTridiagonalMatrix (Nat.succPNat (k + 1)) ⟨t + 1, ht1⟩ j * y j = _
  rw [show (∑ j : Fin (k + 2), pathTridiagonalMatrix (Nat.succPNat (k + 1)) ⟨t + 1, ht1⟩ j * y j) =
      (∑ j : Fin (k + 2), ((if (⟨t + 1, ht1⟩ : Fin (k + 2)) = j then 2 * y j else 0) -
        (if t + 2 = (j : ℕ) then y j else 0) -
        (if (j : ℕ) + 1 = t + 1 then y j else 0))) by
      refine Finset.sum_congr rfl ?_
      intro j hj
      simpa using pathTridiagonal_entry_mul_eq_diag_sub_neighbors y ⟨t + 1, ht1⟩ j]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hdiag :
      (∑ j : Fin (k + 2), if (⟨t + 1, ht1⟩ : Fin (k + 2)) = j then 2 * y j else 0) =
        2 * y ⟨t + 1, ht1⟩ := by
    rw [Fintype.sum_eq_single ⟨t + 1, ht1⟩]
    · simp
    · intro j hj
      have hneq : ¬ (⟨t + 1, ht1⟩ : Fin (k + 2)) = j := by
        simpa using hj.symm
      simp [hneq]
  have hnext : (∑ j : Fin (k + 2), if t + 2 = (j : ℕ) then y j else 0) = y ⟨t + 2, ht2⟩ := by
    rw [Fintype.sum_eq_single ⟨t + 2, ht2⟩]
    · simp
    · intro j hj
      have hne : (j : ℕ) ≠ t + 2 := by
        intro hEq
        apply hj
        ext
        simpa using hEq
      have hneq : ¬ t + 2 = (j : ℕ) := by
        simpa [eq_comm] using hne
      simp [hneq]
  have hprev : (∑ j : Fin (k + 2), if (j : ℕ) + 1 = t + 1 then y j else 0) = y ⟨t, ht0⟩ := by
    rw [Fintype.sum_eq_single ⟨t, ht0⟩]
    · simp
    · intro j hj
      have hne : (j : ℕ) ≠ t := by
        intro hEq
        apply hj
        ext
        simpa using hEq
      have hneq' : ¬ (j : ℕ) = t := hne
      simp [hneq']
  -- The three surviving terms reconstruct the middle-row recurrence.
  rw [hdiag, hnext, hprev]
  ring_nf

/-- Helper for Text 2.14: the last row of the path tridiagonal system is `2 y_k - y_{k-1}`. -/
private theorem pathTridiagonal_mulVec_apply_tail
    (k : ℕ) (y : EuclideanSpace ℝ (Fin (k + 2))) :
    (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (k + 1))) y) (Fin.last (k + 1)) =
      2 * y (Fin.last (k + 1)) - y ⟨k, by omega⟩ := by
  -- Expand the last row and isolate the diagonal and predecessor terms.
  change ∑ j : Fin (k + 2), pathTridiagonalMatrix (Nat.succPNat (k + 1)) (Fin.last (k + 1)) j * y j = _
  rw [show (∑ j : Fin (k + 2), pathTridiagonalMatrix (Nat.succPNat (k + 1)) (Fin.last (k + 1)) j * y j) =
      (∑ j : Fin (k + 2), ((if Fin.last (k + 1) = j then 2 * y j else 0) -
        (if k + 2 = (j : ℕ) then y j else 0) -
        (if (j : ℕ) + 1 = k + 1 then y j else 0))) by
      refine Finset.sum_congr rfl ?_
      intro j hj
      simpa [Fin.val_last] using
        pathTridiagonal_entry_mul_eq_diag_sub_neighbors y (Fin.last (k + 1)) j]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hdiag :
      (∑ j : Fin (k + 2), if Fin.last (k + 1) = j then 2 * y j else 0) =
        2 * y (Fin.last (k + 1)) := by
    rw [Fintype.sum_eq_single (Fin.last (k + 1))]
    · simp
    · intro j hj
      have hneq : ¬ Fin.last (k + 1) = j := by
        simpa using hj.symm
      simp [hneq]
  have hnext : (∑ j : Fin (k + 2), if k + 2 = (j : ℕ) then y j else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hne : ¬ k + 2 = (j : ℕ) := by
      exact Ne.symm (Nat.ne_of_lt j.2)
    simp [hne]
  have hprev : (∑ j : Fin (k + 2), if (j : ℕ) + 1 = k + 1 then y j else 0) = y ⟨k, by omega⟩ := by
    rw [Fintype.sum_eq_single ⟨k, by omega⟩]
    · simp
    · intro j hj
      have hne : (j : ℕ) ≠ k := by
        intro hEq
        apply hj
        ext
        simpa using hEq
      have hneq' : ¬ (j : ℕ) = k := hne
      simp [hneq']
  -- This is exactly the tail boundary equation from the source tridiagonal system.
  rw [hdiag, hnext, hprev]
  ring_nf

/-- Helper for Text 2.14: the affine-profile stationary point solves the tridiagonal system
`A_k y = e₁`. -/
private theorem pathTridiagonal_mulVec_stationaryPoint
    (k : ℕ) :
    Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k))
      (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k)) =
        (EuclideanSpace.single (0 : Fin (k + 1)) (1 : ℝ)).ofLp := by
  cases' k with k
  · ext i
    fin_cases i
    -- In dimension one, the matrix equation is a direct scalar calculation.
    simp [Matrix.mulVec, dotProduct, pathTridiagonalMatrix_apply,
      smoothLowerBoundFunctionStationaryPoint_apply, EuclideanSpace.single]
    norm_num
  · ext i
    by_cases hi0 : i = 0
    · subst hi0
      -- The head row realizes the `2 y₀ - y₁ = 1` equation.
      rw [pathTridiagonal_mulVec_apply_head]
      simp [smoothLowerBoundFunctionStationaryPoint_apply, EuclideanSpace.single]
      field_simp
      simp
      ring_nf
      split_ifs with hzero
      · simp
      · exfalso
        exact hzero rfl
    · by_cases hilast : i = Fin.last (k + 1)
      · subst hilast
        -- The tail row realizes the boundary equation `2 y_k - y_{k-1} = 0`.
        rw [pathTridiagonal_mulVec_apply_tail]
        simp [smoothLowerBoundFunctionStationaryPoint_apply, EuclideanSpace.single]
        field_simp
        ring_nf
      · let t := i.1 - 1
        have hi_pos' : 1 ≤ i.1 := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (by
          intro hzero
          apply hi0
          ext
          simpa using hzero))
        have hi_le_last : i.1 ≤ k + 1 := Nat.le_of_lt_succ i.2
        have hi_ne_last_val : i.1 ≠ k + 1 := by
          intro hi_last
          apply hilast
          ext
          simpa [Fin.val_last] using hi_last
        have hi_lt_last : i.1 < k + 1 := lt_of_le_of_ne hi_le_last hi_ne_last_val
        have ht0 : t < k + 2 := by
          dsimp [t]
          omega
        have ht1 : t + 1 < k + 2 := by
          dsimp [t]
          omega
        have ht2 : t + 2 < k + 2 := by
          dsimp [t]
          omega
        have hi_eq : i = ⟨t + 1, ht1⟩ := by
          ext
          dsimp [t]
          rw [Nat.sub_add_cancel hi_pos']
        -- Every interior row realizes the affine-profile recurrence.
        rw [hi_eq, pathTridiagonal_mulVec_apply_middle k _ t ht0 ht1 ht2]
        have hne0 : (⟨t + 1, ht1⟩ : Fin (k + 2)) ≠ 0 := by
          intro hzero
          apply hi0
          calc
            i = ⟨t + 1, ht1⟩ := hi_eq
            _ = 0 := hzero
        simp [smoothLowerBoundFunctionStationaryPoint_apply, EuclideanSpace.single, hne0]
        field_simp
        ring_nf

/-- Helper for Text 2.14: after substituting `A_k x̄ = e₁`, the quadratic term collapses to the
head coordinate of the affine profile. -/
private theorem smoothLowerBoundFunctionStationaryPoint_dotProduct_mulVec_eq_head
    (k : Fin n) :
    dotProduct
        (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k.1))
        (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k.1))
          (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k.1))) =
      (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k.1)) 0 := by
  -- Replace the residual by `e₁`; then only the head coordinate survives in the dot product.
  rw [pathTridiagonal_mulVec_stationaryPoint k.1]
  change
    ∑ x : Fin (Nat.succPNat k.1),
        smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k.1) x *
          (EuclideanSpace.single (0 : Fin (Nat.succPNat k.1)) (1 : ℝ)).ofLp x =
      (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k.1)) 0
  rw [Fintype.sum_eq_single 0]
  · have hsingle0 :
        (EuclideanSpace.single (0 : Fin (Nat.succPNat k.1)) (1 : ℝ)).ofLp 0 = 1 := by
        simp [EuclideanSpace.single]
    rw [hsingle0]
    ring
  · intro j hj
    have hj0 : j ≠ (0 : Fin (Nat.succPNat k.1)) := by
      simpa [eq_comm] using hj
    have hsinglej :
        (EuclideanSpace.single (0 : Fin (Nat.succPNat k.1)) (1 : ℝ)).ofLp j = 0 := by
      change Function.update (fun _ : Fin (Nat.succPNat k.1) ↦ (0 : ℝ))
          (0 : Fin (Nat.succPNat k.1)) 1 j = 0
      rw [Function.update_of_ne hj0]
    rw [hsinglej]
    ring

/-- Evaluating the quadratic hard instance at its canonical stationary point gives the closed-form
value from Text 2.14. -/
-- Proof sketch: first pass from the ambient hard-instance owner to the core prefix owner
-- `smoothLowerBoundFunction` using
-- `quadraticHardInstanceFamily_stationaryPoint_eq_smoothLowerBoundFunction`; then evaluate the
-- prefix quadratic at `smoothLowerBoundFunctionStationaryPoint` using
-- `smoothLowerBoundFunction_apply` and the explicit affine-profile coordinates.
theorem quadraticHardInstanceFamily_stationaryPoint_value
    (L : NNReal) (k : Fin n) :
    quadraticHardInstanceFamily (L : ℝ) k (quadraticHardInstanceStationaryPoint k) =
      ((L : ℝ) / 8) * (-1 + 1 / (((k.1 + 2 : ℕ) : ℝ))) := by
  -- Rewrite the ambient hard-instance value as the prefix quadratic at the affine-profile point.
  rw [quadraticHardInstanceFamily_stationaryPoint_eq_smoothLowerBoundFunction]
  rw [smoothLowerBoundFunction_apply]
  -- Collapse the quadratic term using the source linear system `A_k x̄ = e₁`.
  rw [smoothLowerBoundFunctionStationaryPoint_dotProduct_mulVec_eq_head]
  have hhead :
      (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k.1)) 0 =
        1 - 1 / (((k.1 + 2 : ℕ) : ℝ)) := by
    -- The head coordinate is the first term of the explicit affine profile.
    simp [smoothLowerBoundFunctionStationaryPoint_apply]
    ring
  -- Substitute the explicit head coordinate and simplify the scalar expression.
  rw [hhead]
  ring

/-- Text 2.14: for the canonical smoothness parameter `L : NNReal`, the optimal value of the
quadratic hard-instance objective `f_k` is `((L : ℝ) / 8) * (-1 + 1 / (k + 1))`; in the file's
zero-based `Fin` indexing, `k : Fin n` represents the textbook index `k + 1`, so the denominator
becomes `k.1 + 2`. -/
-- Proof sketch: package `quadraticHardInstanceFamily (L : ℝ) k` as the canonical unconstrained
-- owner problem on `Set.univ`, apply
-- `SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn` at the minimizing stationary
-- point, and then rewrite the attained value with
-- `quadraticHardInstanceFamily_stationaryPoint_value`.
theorem quadraticHardInstanceFamily_optimal_value
    (L : NNReal) (k : Fin n) :
    (SetConstrainedMinimizationProblem.mk Set.univ
      (quadraticHardInstanceFamily (L : ℝ) k)).optimalValue =
      ((((L : ℝ) / 8) * (-1 + 1 / (((k.1 + 2 : ℕ) : ℝ))) : ℝ) : EReal) := by
  calc
    (SetConstrainedMinimizationProblem.mk Set.univ
      (quadraticHardInstanceFamily (L : ℝ) k)).optimalValue =
        (quadraticHardInstanceFamily (L : ℝ) k
          (quadraticHardInstanceStationaryPoint k) : EReal) := by
            exact
              (SetConstrainedMinimizationProblem.mk Set.univ
                (quadraticHardInstanceFamily (L : ℝ) k)).optimalValue_eq_of_isMinOn
                  (by simp) (quadraticHardInstanceStationaryPoint_isMinOn L k)
    _ =
        ((((L : ℝ) / 8) * (-1 + 1 / (((k.1 + 2 : ℕ) : ℝ))) : ℝ) : EReal) := by
          rw [quadraticHardInstanceFamily_stationaryPoint_value L k]

/-- Companion bridge: the raw infimum of the range of the quadratic hard-instance objective is
the same closed-form value as the owner-level optimal value. -/
-- Proof sketch: use the source-facing minimizer theorem to obtain an attained infimum of the raw
-- range via `IsMinOn.isGLB`, then evaluate the objective at the stationary point.
theorem quadraticHardInstanceFamily_csInf_range
    (L : NNReal) (k : Fin n) :
    sInf (Set.range (quadraticHardInstanceFamily (L : ℝ) k)) =
      ((L : ℝ) / 8) * (-1 + 1 / (((k.1 + 2 : ℕ) : ℝ))) := by
  have hmin := quadraticHardInstanceStationaryPoint_isMinOn L k
  have hglb :
      IsGLB (Set.range (quadraticHardInstanceFamily (L : ℝ) k))
        (quadraticHardInstanceFamily (L : ℝ) k (quadraticHardInstanceStationaryPoint k)) := by
    simpa [Set.range] using hmin.isGLB (by simp)
  calc
    sInf (Set.range (quadraticHardInstanceFamily (L : ℝ) k)) =
        quadraticHardInstanceFamily (L : ℝ) k (quadraticHardInstanceStationaryPoint k) := by
          exact hglb.csInf_eq ⟨_, ⟨quadraticHardInstanceStationaryPoint k, rfl⟩⟩
    _ = ((L : ℝ) / 8) * (-1 + 1 / (((k.1 + 2 : ℕ) : ℝ))) :=
      quadraticHardInstanceFamily_stationaryPoint_value L k

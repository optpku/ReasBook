/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_15

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

open scoped Gradient

/- Text 2.13 lies in the Euclidean quadratic hard-instance domain.

Sampled owner-style declarations in this domain:
* `quadraticHardInstanceFamily` in `Definition_2_10`
* `smoothLowerBoundFunctionStationaryPoint` in `Definition_2_11`
* `UnconstrainedQuadraticMinimizationProblem.eq_minimizer_of_gradient_eq_zero` in
  `Chap01/Proposition_1_9_11`
* `Submodule.comap` / `Submodule.pi`, the canonical submodule owners for coordinatewise vanishing

Best owner abstractions:
* source-facing: `coordinateSubspace k n` and `quadraticHardInstanceStationaryPoint k`
* core/canonical: the prefix owner point `smoothLowerBoundFunctionStationaryPoint`
* bridge/view: the zero-tail linear embedding from the active prefix into `ℝⁿ`

Primitive data:
* the cut index `k`
* the owner prefix stationary point on `Fin (k.1 + 1)`

Derived API:
* the ambient stationary point `quadraticHardInstanceStationaryPoint k`
* its coordinate formula and coordinate-subspace membership
* the stationary-point characterization on `ℝ^{k.1 + 1,n}`
-/

/-- The leading-coordinate subspace `ℝ^{k,n}` of `ℝⁿ`, consisting of vectors whose coordinates
from `k + 1` through `n` vanish in one-based indexing. -/
def coordinateSubspace (k n : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.comap (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv.toLinearMap
    (Submodule.pi Set.univ (fun i : Fin n ↦ if i.1 < k then ⊤ else ⊥))

scoped[CoordinateSubspace] notation "ℝ^{" k "," n "}" => coordinateSubspace k n
open scoped CoordinateSubspace

/-- Membership in `ℝ^{k,n}` is equivalent to vanishing of all coordinates with
index at least `k` in zero-based indexing. -/
-- Proof sketch: unfold `coordinateSubspace` and `Submodule.mem_pi`; for each coordinate,
-- membership in `⊤` is automatic and membership in `⊥` is equivalent to the coordinate being
-- zero.
theorem mem_coordinateSubspace_iff {k n : ℕ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ ℝ^{k,n} ↔ ∀ i : Fin n, k ≤ i.1 → x i = 0 := by
  constructor
  · intro hx i hi
    -- Coordinates landing in the `⊥`-fiber of the defining `Submodule.pi` must vanish.
    simpa [hi, not_lt.mpr hi] using hx i
  · intro hx i
    by_cases hi : i.1 < k
    · -- Coordinates in the active prefix lie in the `⊤`-fiber automatically.
      simp [hi]
    · -- Coordinates in the zero tail are exactly the coordinates constrained to lie in `⊥`.
      have hki : k ≤ i.1 := Nat.le_of_not_lt hi
      simp [hi, hx i hki]

-- Embed the active prefix space into `ℝⁿ` by filling the tail coordinates with `0`.
private def zeroTailEmbedding (k : Fin n) :
    EuclideanSpace ℝ (Fin (k.1 + 1)) →ₗ[ℝ] E where
  toFun x :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm
      (fun i ↦ if h : i ≤ k then x ⟨i.1, Nat.lt_succ_of_le h⟩ else 0)
  map_add' x y := by
    ext i
    by_cases hi : i ≤ k
    · simp [hi]
    · simp [hi]
  map_smul' c x := by
    ext i
    by_cases hi : i ≤ k
    · simp [hi]
    · simp [hi]

@[simp] private theorem zeroTailEmbedding_apply
    (k : Fin n) (x : EuclideanSpace ℝ (Fin (k.1 + 1))) (i : Fin n) :
    zeroTailEmbedding k x i = if h : i ≤ k then x ⟨i.1, Nat.lt_succ_of_le h⟩ else 0 :=
  rfl

/-- The stationary point of the quadratic hard instance `quadraticHardInstanceFamily L k`,
obtained by extending the owner stationary point of `smoothLowerBoundFunction` on the active
prefix and setting the tail coordinates to `0`. -/
def quadraticHardInstanceStationaryPoint (k : Fin n) : E :=
  zeroTailEmbedding k (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k.1))

/-- Evaluating the hard-instance stationary point returns the displayed affine profile on the
active prefix and `0` on the tail. -/
-- Proof sketch: unfold `quadraticHardInstanceStationaryPoint`; on the active prefix use
-- `smoothLowerBoundFunctionStationaryPoint_apply`, and outside it the tail is definitionally `0`.
theorem quadraticHardInstanceStationaryPoint_apply (k : Fin n) (i : Fin n) :
    quadraticHardInstanceStationaryPoint k i =
      if i ≤ k then
        1 - (((i.1 + 1 : ℕ) : ℝ) / ((k.1 + 2 : ℕ) : ℝ))
      else
        0 := by
  -- Unfold the zero-tail extension and evaluate separately on the active prefix and the tail.
  unfold quadraticHardInstanceStationaryPoint
  by_cases hi : i ≤ k
  · simp [zeroTailEmbedding_apply, hi, smoothLowerBoundFunctionStationaryPoint_apply]
    ring_nf
  · simp [zeroTailEmbedding_apply, hi]

/-- The hard-instance stationary point lies in the leading-coordinate subspace corresponding to
its active prefix. -/
-- Proof sketch: apply `mem_coordinateSubspace_iff` and read off from
-- `quadraticHardInstanceStationaryPoint_apply` that every coordinate with index at least
-- `k.1 + 1` is zero.
theorem quadraticHardInstanceStationaryPoint_mem_coordinateSubspace (k : Fin n) :
    quadraticHardInstanceStationaryPoint k ∈ ℝ^{k.1 + 1,n} := by
  rw [mem_coordinateSubspace_iff]
  intro i hi
  have hnot : ¬ i ≤ k := by
    intro hik
    exact Nat.not_succ_le_self k.1 (le_trans hi (Fin.le_iff_val_le_val.mp hik))
  -- Every coordinate beyond the active prefix is in the zero tail of the stationary point.
  simp [quadraticHardInstanceStationaryPoint_apply, hnot]

/-- Helper for Text 2.13: project `ℝⁿ` onto its first `k.1 + 1` coordinates. -/
private def prefixProjection (k : Fin n) : E →ₗ[ℝ] EuclideanSpace ℝ (Fin (k.1 + 1)) :=
  (EuclideanSpace.equiv (Fin (k.1 + 1)) ℝ).symm.toLinearMap.comp
    ((LinearMap.pi fun i : Fin (k.1 + 1) ↦
        LinearMap.proj (Fin.castLEEmb (Nat.succ_le_of_lt k.2) i)).comp
      (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv.toLinearMap)

/-- Helper for Text 2.13: the prefix projection reads off the first `k.1 + 1` coordinates. -/
private theorem prefixProjection_apply
    (k : Fin n) (x : E) (i : Fin (k.1 + 1)) :
    prefixProjection k x i = x (Fin.castLE (Nat.succ_le_of_lt k.2) i) := by
  -- The composed coordinate projection is definitionally the requested leading-coordinate readout.
  simp [prefixProjection]

/-- Helper for Text 2.13: the zero-tail embedding is a left inverse to the prefix projection. -/
private theorem prefixProjection_zeroTailEmbedding
    (k : Fin n) (x : EuclideanSpace ℝ (Fin (k.1 + 1))) :
    prefixProjection k (zeroTailEmbedding k x) = x := by
  ext i
  -- Restricting back to the active prefix forgets the zero tail and recovers the original point.
  have hi : Fin.castLE (Nat.succ_le_of_lt k.2) i ≤ k :=
    Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ i.2)
  simp [prefixProjection_apply, zeroTailEmbedding_apply, hi]

/-- Helper for Text 2.13: restricting the ambient hard instance to the leading-coordinate
subspace recovers the prefix lower-bound quadratic. -/
private theorem quadraticHardInstanceFamily_comp_zeroTailEmbedding
    (L : ℝ) (k : Fin n) (y : EuclideanSpace ℝ (Fin (k.1 + 1))) :
    quadraticHardInstanceFamily L k (zeroTailEmbedding k y) =
      smoothLowerBoundFunction L (Nat.succPNat k.1) y := by
  -- After extending by zero, the hard instance sees exactly the original active coordinates.
  simpa [quadraticHardInstanceFamily, prefixProjection] using
    congrArg (smoothLowerBoundFunction L (Nat.succPNat k.1))
      (prefixProjection_zeroTailEmbedding k y)

/-- Helper for Text 2.13: points in the leading-coordinate subspace are recovered from their
active prefix coordinates by zero-tail extension. -/
private theorem eq_zeroTailEmbedding_of_mem_coordinateSubspace
    (k : Fin n) {x : E} (hx : x ∈ ℝ^{k.1 + 1,n}) :
    x = zeroTailEmbedding k (prefixProjection k x) := by
  ext i
  by_cases hi : i ≤ k
  · -- On the active prefix, the zero-tail reconstruction simply reads back the original coordinate.
    simp [prefixProjection_apply, zeroTailEmbedding_apply, hi]
  · -- In the tail, membership in `ℝ^{k.1 + 1,n}` already forces the coordinate to vanish.
    have htail : x i = 0 := (mem_coordinateSubspace_iff.mp hx) i (Nat.succ_le_of_lt (lt_of_not_ge hi))
    simp [zeroTailEmbedding_apply, hi, htail]

/-- Helper for Text 2.13: the prefix gradient is `(L / 4)` times the residual
`A_k y - e₁`. -/
private theorem smoothLowerBoundFunction_gradient_eq_scaled_residual
    (L : ℝ) (k : ℕ) (y : EuclideanSpace ℝ (Fin (Nat.succPNat k))) :
    ∇ (smoothLowerBoundFunction L (Nat.succPNat k)) y =
      (L / 4) •
        (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k)) y -
          EuclideanSpace.single (0 : Fin (Nat.succPNat k)) (1 : ℝ)) := by
  -- Normalize the owner gradient formula to the linear-system residual `A_k y - e₁`.
  have hgrad :
      ∇ (smoothLowerBoundFunction L (Nat.succPNat k)) y =
        -(L / 4) • EuclideanSpace.single (0 : Fin (Nat.succPNat k)) (1 : ℝ) +
          (((L / 4) • pathTridiagonalMatrix (Nat.succPNat k)).toEuclideanLin y) := by
    simpa using congrFun (smoothLowerBoundFunction_gradient_eq L (Nat.succPNat k)) y
  rw [hgrad]
  funext i
  change (-(L / 4) * (EuclideanSpace.single (0 : Fin (Nat.succPNat k)) (1 : ℝ)).ofLp i) +
      ((((L / 4) • pathTridiagonalMatrix (Nat.succPNat k)).toEuclideanLin y).ofLp i) =
    (L / 4) * ((Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k)) y.ofLp) i -
      (EuclideanSpace.single (0 : Fin (Nat.succPNat k)) (1 : ℝ)).ofLp i)
  rw [show ((((L / 4) • pathTridiagonalMatrix (Nat.succPNat k)).toEuclideanLin y).ofLp) =
      Matrix.mulVec (((L / 4) • pathTridiagonalMatrix (Nat.succPNat k))) y.ofLp by
        simpa [Matrix.toLin'_apply] using
          (Matrix.ofLp_toLpLin (p := (2 : ENNReal)) (q := (2 : ENNReal))
            (((L / 4) • pathTridiagonalMatrix (Nat.succPNat k))) y)]
  rw [Matrix.smul_mulVec, Pi.smul_apply]
  simp [EuclideanSpace.single]
  ring

/-- Helper for Text 2.13: `smoothLowerBoundFunction` is differentiable at every prefix point. -/
private theorem smoothLowerBoundFunction_differentiableAt
    (L : ℝ) (k : ℕ) (y : EuclideanSpace ℝ (Fin (k + 1))) :
    DifferentiableAt ℝ (smoothLowerBoundFunction L (Nat.succPNat k)) y := by
  -- Reuse the symmetric-quadratic `C¹` owner theorem for the prefix quadratic model.
  have hcont : ContDiff ℝ 1 (smoothLowerBoundFunction L (Nat.succPNat k)) := by
    simpa [smoothLowerBoundFunction] using
      (symmetric_quadratic_contDiff_and_gradient_lipschitz 0
        (-(L / 4) • EuclideanSpace.single (0 : Fin (Nat.succPNat k)) (1 : ℝ))
        ((L / 4) • pathTridiagonalMatrix (Nat.succPNat k))
        ((pathTridiagonalMatrix_isSymm (Nat.succPNat k)).smul (L / 4))).1
  exact hcont.differentiable_one y

/-- Helper for Text 2.13: precomposing a differentiable scalar field with a continuous linear map
pulls back its gradient by the adjoint. -/
private theorem hasGradientAt_comp_continuousLinearMap
    {m : Type*} [NormedAddCommGroup m] [InnerProductSpace ℝ m] [CompleteSpace m]
    {f : m → ℝ} (A : E →L[ℝ] m) {x : E}
    (hf : DifferentiableAt ℝ f (A x)) :
    HasGradientAt (f ∘ A) (A.adjoint (∇ f (A x))) x := by
  -- Rewrite the gradient statement as a Fréchet-derivative statement and apply the chain rule.
  rw [hasGradientAt_iff_hasFDerivAt]
  have hcomp := (hf.hasGradientAt.hasFDerivAt).comp x A.hasFDerivAt
  convert hcomp using 1
  ext y
  calc
    inner ℝ (A.adjoint (∇ f (A x))) y = inner ℝ y (A.adjoint (∇ f (A x))) := by
      rw [real_inner_comm]
    _ = inner ℝ (A y) (∇ f (A x)) := A.adjoint_inner_right y (∇ f (A x))
    _ = inner ℝ (∇ f (A x)) (A y) := by
      rw [real_inner_comm]

/-- Helper for Text 2.13: the first row of the path tridiagonal matrix reads
`2 y₀ - y₁`. -/
private theorem pathTridiagonal_entry_mul_eq_diag_sub_neighbors
    {m : ℕ} (y : EuclideanSpace ℝ (Fin (m + 1))) (i j : Fin (m + 1)) :
    pathTridiagonalMatrix (Nat.succPNat m) i j * y j =
      (if i = j then 2 * y j else 0) -
      (if (i : ℕ) + 1 = (j : ℕ) then y j else 0) -
      (if (j : ℕ) + 1 = (i : ℕ) then y j else 0) := by
  -- Split the matrix entry into the diagonal, forward-edge, and backward-edge cases.
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

/-- Helper for Text 2.13: the first row of the path tridiagonal matrix reads
`2 y₀ - y₁`. -/
private theorem pathTridiagonal_mulVec_apply_head
    (k : ℕ) (y : EuclideanSpace ℝ (Fin (k + 2))) :
    (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (k + 1))) y) 0 =
      2 * y 0 - y ⟨1, by omega⟩ := by
  -- Expand the row into diagonal/neighbor contributions and evaluate the resulting finite sums.
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
    have hne : ¬ (j : ℕ) + 1 = (0 : ℕ) := by
      omega
    simp [hne]
  rw [hdiag, hnext, hprev]
  ring_nf

/-- Helper for Text 2.13: every interior row of the path tridiagonal matrix reads
`2 yᵢ - yᵢ₋₁ - yᵢ₊₁`. -/
private theorem pathTridiagonal_mulVec_apply_middle
    (k : ℕ) (y : EuclideanSpace ℝ (Fin (k + 2))) (t : ℕ) (ht : t < k)
    (ht0 : t < k + 2) (ht1 : t + 1 < k + 2) (ht2 : t + 2 < k + 2) :
    (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (k + 1))) y) ⟨t + 1, ht1⟩ =
      2 * y ⟨t + 1, ht1⟩ - y ⟨t, ht0⟩ - y ⟨t + 2, ht2⟩ := by
  -- Expand the row into diagonal/neighbor contributions and isolate the three surviving terms.
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
  rw [hdiag, hnext, hprev]
  ring_nf

/-- Helper for Text 2.13: the last row of the path tridiagonal matrix reads
`2 y_k - y_{k-1}`. -/
private theorem pathTridiagonal_mulVec_apply_tail
    (k : ℕ) (y : EuclideanSpace ℝ (Fin (k + 2))) :
    (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (k + 1))) y) (Fin.last (k + 1)) =
      2 * y (Fin.last (k + 1)) - y ⟨k, by omega⟩ := by
  -- Expand the row into diagonal/neighbor contributions and evaluate the resulting finite sums.
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
  rw [hdiag, hnext, hprev]
  ring_nf

/-- Helper for Text 2.13: evaluating the prefix gradient at a coordinate exposes the scalar
residual `(A_k y - e₁)_i`. -/
private theorem smoothLowerBoundFunction_gradient_eq_scaled_residual_apply
    (L : ℝ) (k : ℕ) (y : EuclideanSpace ℝ (Fin (k + 1))) (i : Fin (k + 1)) :
    (∇ (smoothLowerBoundFunction L (Nat.succPNat k)) y) i =
      (L / 4) *
        ((Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k)) y) i -
          if i = 0 then 1 else 0) := by
  -- Read the vector residual identity coordinatewise to remove the coercion noise.
  have h := congrFun (smoothLowerBoundFunction_gradient_eq_scaled_residual L k y) i
  rw [Pi.smul_apply] at h
  change (∇ (smoothLowerBoundFunction L (Nat.succPNat k)) y) i =
      (L / 4) * (((Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k)) y) i) -
        (EuclideanSpace.single (0 : Fin (k + 1)) (1 : ℝ)) i) at h
  simpa [EuclideanSpace.single] using h

/-- Helper for Text 2.13: the continuous-linear version of the prefix projection reads off the
first `k.1 + 1` coordinates. -/
private def prefixProjectionContinuous (k : Fin n) :
    E →L[ℝ] EuclideanSpace ℝ (Fin (k.1 + 1)) :=
  (prefixProjection k).toContinuousLinearMap

/-- Helper for Text 2.13: the continuous prefix projection agrees pointwise with the raw prefix
coordinate restriction. -/
@[simp] private theorem prefixProjectionContinuous_apply
    (k : Fin n) (x : E) (i : Fin (k.1 + 1)) :
    prefixProjectionContinuous k x i = x (Fin.castLE (Nat.succ_le_of_lt k.2) i) := by
  -- The continuous-linear wrapper preserves the explicit coordinate formula.
  simp [prefixProjectionContinuous, prefixProjection_apply]

/-- Helper for Text 2.13: the adjoint of the prefix projection is the zero-tail extension. -/
@[simp] private theorem prefixProjectionContinuous_adjoint_apply
    (k : Fin n) (x : EuclideanSpace ℝ (Fin (k.1 + 1))) (i : Fin n) :
    (prefixProjectionContinuous k).adjoint x i =
      if h : i ≤ k then x ⟨i.1, Nat.lt_succ_of_le h⟩ else 0 := by
  by_cases hi : i ≤ k
  · -- On the active prefix, the adjoint recovers the matching coordinate.
    have hinner :
        inner ℝ ((prefixProjectionContinuous k).adjoint x)
            (EuclideanSpace.single i (1 : ℝ)) =
          inner ℝ x
            (prefixProjectionContinuous k (EuclideanSpace.single i (1 : ℝ))) := by
      simpa using
        (prefixProjectionContinuous k).adjoint_inner_left
          (EuclideanSpace.single i (1 : ℝ)) x
    have hsingle :
        prefixProjectionContinuous k (EuclideanSpace.single i (1 : ℝ)) =
          EuclideanSpace.single ⟨i.1, Nat.lt_succ_of_le hi⟩ (1 : ℝ) := by
      ext j
      by_cases hij : j = ⟨i.1, Nat.lt_succ_of_le hi⟩
      · subst hij
        simp [prefixProjectionContinuous_apply]
      · have hne : Fin.castLE (Nat.succ_le_of_lt k.2) j ≠ i := by
          intro hji
          have hcast : j = ⟨i.1, Nat.lt_succ_of_le hi⟩ := by
            ext
            simpa using congrArg Fin.val hji
          exact hij hcast
        have hneq : ¬ j = ⟨i.1, Nat.lt_succ_of_le hi⟩ := hij
        simp [prefixProjectionContinuous_apply, hne, hneq, EuclideanSpace.single]
    have hcoord :
        ((prefixProjectionContinuous k).adjoint x) i = x ⟨i.1, Nat.lt_succ_of_le hi⟩ := by
      rw [hsingle] at hinner
      calc
        ((prefixProjectionContinuous k).adjoint x) i =
            inner ℝ ((prefixProjectionContinuous k).adjoint x)
              (EuclideanSpace.single i (1 : ℝ)) := by
                symm
                simpa using
                  (EuclideanSpace.inner_single_right i (1 : ℝ)
                    ((prefixProjectionContinuous k).adjoint x))
        _ = inner ℝ x (EuclideanSpace.single ⟨i.1, Nat.lt_succ_of_le hi⟩ (1 : ℝ)) := by
              simpa [hsingle] using hinner
        _ = x ⟨i.1, Nat.lt_succ_of_le hi⟩ := by
              simpa using
                (EuclideanSpace.inner_single_right ⟨i.1, Nat.lt_succ_of_le hi⟩
                  (1 : ℝ) x)
    simpa [hi] using hcoord
  · -- Outside the active prefix, the adjoint lands in the zero tail.
    have hinner :
        inner ℝ ((prefixProjectionContinuous k).adjoint x)
            (EuclideanSpace.single i (1 : ℝ)) =
          inner ℝ x
            (prefixProjectionContinuous k (EuclideanSpace.single i (1 : ℝ))) := by
      simpa using
        (prefixProjectionContinuous k).adjoint_inner_left
          (EuclideanSpace.single i (1 : ℝ)) x
    have hzero :
        prefixProjectionContinuous k (EuclideanSpace.single i (1 : ℝ)) = 0 := by
      ext j
      have hne : Fin.castLE (Nat.succ_le_of_lt k.2) j ≠ i := by
        intro hji
        have hle : i ≤ k := by
          refine Fin.le_iff_val_le_val.mpr ?_
          have hcast : i.1 = j.1 := by
            simpa using congrArg Fin.val hji.symm
          simpa [hcast] using Nat.le_of_lt_succ j.2
        exact hi hle
      simp [prefixProjectionContinuous_apply, hne]
    have hcoord : ((prefixProjectionContinuous k).adjoint x) i = 0 := by
      rw [hzero] at hinner
      calc
        ((prefixProjectionContinuous k).adjoint x) i =
            inner ℝ ((prefixProjectionContinuous k).adjoint x)
              (EuclideanSpace.single i (1 : ℝ)) := by
                symm
                simpa using
                  (EuclideanSpace.inner_single_right i (1 : ℝ)
                    ((prefixProjectionContinuous k).adjoint x))
        _ = inner ℝ x 0 := by
              simpa [hzero] using hinner
        _ = 0 := by simp
    simpa [hi] using hcoord

/-- Helper for Text 2.13: the ambient hard instance is the prefix lower-bound quadratic pulled
back along the continuous prefix projection. -/
private theorem quadraticHardInstanceFamily_eq_comp_prefixProjection
    (L : ℝ) (k : Fin n) :
    quadraticHardInstanceFamily L k =
      fun x ↦ smoothLowerBoundFunction L (Nat.succPNat k.1) (prefixProjection k x) := by
  -- Both sides first keep the active prefix coordinates and then apply the same quadratic model.
  funext x
  have hprefix :
      prefixProjection k x =
        (EuclideanSpace.equiv (Fin (k.1 + 1)) ℝ).symm
          (fun i ↦ x (Fin.castLE (Nat.succ_le_of_lt k.2) i)) := by
    ext i
    simp [prefixProjection_apply]
  simpa [quadraticHardInstanceFamily] using
    congrArg (smoothLowerBoundFunction L (Nat.succPNat k.1)) hprefix

/-- Helper for Text 2.13: the ambient hard-instance gradient is the zero-tail extension of the
prefix gradient. -/
private theorem quadraticHardInstanceFamily_gradient_eq_zeroTail_prefixGradient
    (L : ℝ) (k : Fin n) (x : E) :
    ∇ (quadraticHardInstanceFamily L k) x =
      zeroTailEmbedding k
        (∇ (smoothLowerBoundFunction L (Nat.succPNat k.1)) (prefixProjection k x)) := by
  -- Differentiate the prefix factorization and identify the adjoint with zero-tail extension.
  have hdiff :
      DifferentiableAt ℝ (smoothLowerBoundFunction L (Nat.succPNat k.1))
        (prefixProjection k x) := by
    exact smoothLowerBoundFunction_differentiableAt L k.1 (prefixProjection k x)
  have hgrad :=
    hasGradientAt_comp_continuousLinearMap
      (m := EuclideanSpace ℝ (Fin (k.1 + 1)))
      (A := prefixProjectionContinuous k) hdiff
  have hgrad' :
      HasGradientAt (quadraticHardInstanceFamily L k)
        ((prefixProjectionContinuous k).adjoint
          (∇ (smoothLowerBoundFunction L (Nat.succPNat k.1)) (prefixProjection k x))) x := by
    simpa [quadraticHardInstanceFamily_eq_comp_prefixProjection, prefixProjectionContinuous_apply]
      using hgrad
  ext i
  simpa [zeroTailEmbedding_apply, prefixProjectionContinuous_adjoint_apply] using
    congrArg (fun z : E ↦ z i) hgrad'.gradient

/-- Helper for Text 2.13: view a prefix vector as a nat-indexed coordinate sequence on its
support. -/
private def coordinateSequence
    (k : ℕ) (y : EuclideanSpace ℝ (Fin (k + 2))) : ℕ → ℝ :=
  fun t ↦ if ht : t ≤ k + 1 then y ⟨t, Nat.lt_succ_of_le ht⟩ else 0

/-- Helper for Text 2.13: on the supported range, `coordinateSequence` agrees with the original
prefix coordinates. -/
@[simp] private theorem coordinateSequence_apply
    (k : ℕ) (y : EuclideanSpace ℝ (Fin (k + 2))) {t : ℕ} (ht : t ≤ k + 1) :
    coordinateSequence k y t = y ⟨t, Nat.lt_succ_of_le ht⟩ := by
  -- On the active prefix, the sequence is defined by the corresponding coordinate of `y`.
  simp [coordinateSequence, ht]

/-- Helper for Text 2.13: outside the supported range, `coordinateSequence` vanishes. -/
@[simp] private theorem coordinateSequence_apply_of_lt
    (k : ℕ) (y : EuclideanSpace ℝ (Fin (k + 2))) {t : ℕ} (ht : k + 1 < t) :
    coordinateSequence k y t = 0 := by
  -- The sequence only records the coordinates that exist in the `(k + 2)`-dimensional prefix.
  simp [coordinateSequence, Nat.not_le_of_gt ht]

/-- Helper for Text 2.13: a solution of `A_k y = e₁` yields the expected head, interior, and tail
scalar recurrence for its coordinate sequence. -/
private theorem pathTridiagonal_solution_coordinate_recurrence
    (k : ℕ) {y : EuclideanSpace ℝ (Fin (k + 2))}
    (hy : Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (k + 1))) y =
      EuclideanSpace.single (0 : Fin (k + 2)) (1 : ℝ)) :
    coordinateSequence k y 1 = 2 * coordinateSequence k y 0 - 1 ∧
      (∀ t < k,
        coordinateSequence k y (t + 2) =
          2 * coordinateSequence k y (t + 1) - coordinateSequence k y t) ∧
      2 * coordinateSequence k y (k + 1) - coordinateSequence k y k = 0 := by
  constructor
  · -- The first row of `A_k y = e₁` is exactly the head equation.
    have hhead := congrFun hy 0
    rw [pathTridiagonal_mulVec_apply_head] at hhead
    have hhead' : 2 * y 0 - y 1 = 1 := by
      simpa [EuclideanSpace.single] using hhead
    have hzero : coordinateSequence k y 0 = y 0 := by
      simp [coordinateSequence]
    have hone : coordinateSequence k y 1 = y 1 := by
      simp [coordinateSequence]
    rw [hzero, hone]
    linarith
  · constructor
    · intro t ht
      -- Every interior row translates directly into the second-order affine recurrence.
      have ht0 : t < k + 2 := by omega
      have ht1 : t + 1 < k + 2 := by omega
      have ht2 : t + 2 < k + 2 := by omega
      have hmid := congrFun hy ⟨t + 1, ht1⟩
      rw [pathTridiagonal_mulVec_apply_middle k y t ht ht0 ht1 ht2] at hmid
      have hne0 : (⟨t + 1, ht1⟩ : Fin (k + 2)) ≠ 0 := by
        intro hzero
        have : t + 1 = 0 := by simpa using congrArg Fin.val hzero
        omega
      have hs0 : coordinateSequence k y t = y ⟨t, ht0⟩ := by
        simp [coordinateSequence, show t ≤ k + 1 by omega]
      have hs1 : coordinateSequence k y (t + 1) = y ⟨t + 1, ht1⟩ := by
        simp [coordinateSequence, show t + 1 ≤ k + 1 by omega]
      have hs2 : coordinateSequence k y (t + 2) = y ⟨t + 2, ht2⟩ := by
        simp [coordinateSequence, show t + 2 ≤ k + 1 by omega]
      rw [hs0, hs1, hs2]
      have hmid' :
          2 * y ⟨t + 1, ht1⟩ - y ⟨t, ht0⟩ - y ⟨t + 2, ht2⟩ = 0 := by
        simpa [EuclideanSpace.single, hne0] using hmid
      linarith
    · -- The last row gives the boundary condition at the tail.
      have htail := congrFun hy (Fin.last (k + 1))
      rw [pathTridiagonal_mulVec_apply_tail] at htail
      have hne0 : (Fin.last (k + 1) : Fin (k + 2)) ≠ 0 := by
        intro hzero
        have : k + 1 = 0 := by
          simpa [Fin.val_last] using congrArg Fin.val hzero
        omega
      have hlast_eq : (⟨k + 1, by omega⟩ : Fin (k + 2)) = Fin.last (k + 1) := by
        ext
        simp [Fin.val_last]
      have hslast : coordinateSequence k y (k + 1) = y (Fin.last (k + 1)) := by
        rw [coordinateSequence_apply k y (t := k + 1) (Nat.le_refl _)]
        simpa [hlast_eq]
      have hsk : coordinateSequence k y k = y ⟨k, by omega⟩ := by
        simp [coordinateSequence]
      rw [hslast, hsk]
      simpa [EuclideanSpace.single, hne0] using htail

/-- Helper for Text 2.13: the second-order tridiagonal recurrence makes the first differences
constant. -/
private theorem first_difference_constant_of_tridiagonal_recurrence
    (k : ℕ) {s : ℕ → ℝ}
    (hrec : ∀ t < k, s (t + 2) = 2 * s (t + 1) - s t) :
    ∀ t < k, s (t + 2) - s (t + 1) = s (t + 1) - s t := by
  intro t ht
  -- Rewriting the recurrence isolates the common first difference.
  linarith [hrec t ht]

/-- Helper for Text 2.13: a sequence with constant first difference is affine on the supported
range. -/
private theorem sequence_eq_initial_add_mul_constant_difference
    (k : ℕ) {s : ℕ → ℝ} {d : ℝ}
    (hd : ∀ t < k + 1, s (t + 1) - s t = d) :
    ∀ t ≤ k + 1, s t = s 0 + (t : ℝ) * d := by
  intro t
  induction' t with t iht
  · intro _
    ring
  · intro ht
    -- Move one step along the sequence using the constant-difference hypothesis.
    have hprev : s t = s 0 + (t : ℝ) * d := iht (Nat.le_of_succ_le ht)
    have hstep : s (t + 1) - s t = d := hd t (lt_of_lt_of_le (Nat.lt_succ_self t) ht)
    calc
      s (t + 1) = s t + d := by linarith
      _ = s 0 + (t : ℝ) * d + d := by rw [hprev]
      _ = s 0 + ((t + 1 : ℕ) : ℝ) * d := by
            norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm, mul_add, add_mul]

/-- Helper for Text 2.13: the tridiagonal recurrence forces the affine profile
`1 - (t + 1) / (k + 3)`. -/
private theorem affine_profile_of_tridiagonal_recurrence
    (k : ℕ) {s : ℕ → ℝ}
    (hhead : s 1 = 2 * s 0 - 1)
    (hrec : ∀ t < k, s (t + 2) = 2 * s (t + 1) - s t)
    (htail : 2 * s (k + 1) - s k = 0) :
    ∀ t ≤ k + 1,
      s t = 1 - (((t + 1 : ℕ) : ℝ) / ((k + 3 : ℕ) : ℝ)) := by
  let d : ℝ := s 1 - s 0
  have hconst :
      ∀ t < k + 1, s (t + 1) - s t = d := by
    intro t ht
    induction' t with t iht
    · simp [d]
    · -- The recurrence shows consecutive first differences are equal everywhere in the interior.
      have hprev : s (t + 1) - s t = d := iht (by omega)
      have hdiff :
          s (t + 2) - s (t + 1) = s (t + 1) - s t :=
        first_difference_constant_of_tridiagonal_recurrence k hrec t (by omega)
      linarith
  have haff :
      ∀ t ≤ k + 1, s t = s 0 + (t : ℝ) * d :=
    sequence_eq_initial_add_mul_constant_difference k hconst
  have hone : s 1 = s 0 + d := by
    simpa [d] using haff 1 (by omega)
  have hd_eq : d = s 0 - 1 := by
    -- The head equation identifies the common first difference.
    linarith [hhead, hone]
  have hk : s k = s 0 + (k : ℝ) * d := haff k (by omega)
  have hksucc : s (k + 1) = s 0 + ((k + 1 : ℕ) : ℝ) * d := haff (k + 1) (by omega)
  have hk1_cast : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by
    norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm]
  have hk2_cast : (((k + 2 : ℕ) : ℝ)) = (k : ℝ) + 2 := by
    norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm]
  have hk3_cast : (((k + 3 : ℕ) : ℝ)) = (k : ℝ) + 3 := by
    norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm]
  have htail_aff : s 0 + ((k + 2 : ℕ) : ℝ) * d = 0 := by
    -- The tail equation fixes the remaining affine parameter.
    rw [hk, hksucc] at htail
    have htail' : s 0 + ((k : ℝ) + 2) * d = 0 := by
      rw [hk1_cast] at htail
      ring_nf at htail ⊢
      exact htail
    simpa [hk2_cast] using htail'
  have hk3_ne : (((k + 3 : ℕ) : ℝ)) ≠ 0 := by
    positivity
  have hs0_mul : (((k + 3 : ℕ) : ℝ)) * s 0 = ((k + 2 : ℕ) : ℝ) := by
    have htail_aff' : s 0 + ((k + 2 : ℕ) : ℝ) * (s 0 - 1) = 0 := by
      simpa [hd_eq] using htail_aff
    nlinarith [htail_aff', hk2_cast, hk3_cast]
  have hd_mul : (((k + 3 : ℕ) : ℝ)) * d = -1 := by
    have hd_mul' : (((k + 3 : ℕ) : ℝ)) * (s 0 - 1) = -1 := by
      nlinarith [hs0_mul, hk2_cast, hk3_cast]
    simpa [hd_eq] using hd_mul'
  have hs0_formula : s 0 = 1 - (1 : ℝ) / ((k + 3 : ℕ) : ℝ) := by
    have hs0_div : s 0 = ((k + 2 : ℕ) : ℝ) / ((k + 3 : ℕ) : ℝ) := by
      apply (eq_div_iff hk3_ne).2
      simpa [mul_comm] using hs0_mul
    rw [hs0_div]
    have hk2_eq : ((k + 2 : ℕ) : ℝ) = ((k + 3 : ℕ) : ℝ) - 1 := by
      rw [hk2_cast, hk3_cast]
      ring
    rw [hk2_eq]
    field_simp [hk3_ne]
  have hd_formula : d = -(1 : ℝ) / ((k + 3 : ℕ) : ℝ) := by
    apply (eq_div_iff hk3_ne).2
    simpa [mul_comm] using hd_mul
  intro t ht
  -- Substitute the affine description and the solved affine parameters.
  rw [haff t ht, hs0_formula, hd_formula]
  rw [hk3_cast]
  field_simp [hk3_ne]
  have ht_cast : (((t + 1 : ℕ) : ℝ)) = (t : ℝ) + 1 := by
    norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm]
  rw [ht_cast]
  nlinarith

/-- Helper for Text 2.13: any prefix vector solving `A_k y = e₁` is the affine-profile point. -/
private theorem pathTridiagonal_solution_eq_stationaryPoint
    (k : ℕ) {y : EuclideanSpace ℝ (Fin (k + 1))}
    (hy : Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k)) y =
      EuclideanSpace.single (0 : Fin (k + 1)) (1 : ℝ)) :
    y = smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k) := by
  cases' k with k
  · ext i
    fin_cases i
    -- In dimension one, the single linear equation is `2 y₀ = 1`.
    have h0 := congrFun hy 0
    simp [Matrix.mulVec, dotProduct, pathTridiagonalMatrix_apply, EuclideanSpace.single] at h0
    have hy0_ofLp : y.ofLp 0 = 1 / 2 := by
      have htwo : (2 : ℝ) ≠ 0 := by norm_num
      have h0' : y.ofLp 0 * 2 = 1 := by
        simpa [mul_comm] using h0
      apply (eq_div_iff htwo).2
      exact h0'
    have hy0 : y 0 = 1 / 2 := by
      simpa using hy0_ofLp
    calc
      y 0 = (1 : ℝ) / 2 := hy0
      _ = smoothLowerBoundFunctionStationaryPoint (Nat.succPNat 0) 0 := by
            norm_num [smoothLowerBoundFunctionStationaryPoint_apply]
  · rcases pathTridiagonal_solution_coordinate_recurrence k hy with ⟨hhead, hrec, htail⟩
    have hprofile := affine_profile_of_tridiagonal_recurrence k hhead hrec htail
    ext i
    have hi : i.1 ≤ k + 1 := Nat.le_of_lt_succ i.2
    -- Each coordinate is determined by the solved affine profile of the recurrence.
    calc
      y i = coordinateSequence k y i.1 := by
        simpa using (coordinateSequence_apply k y (t := i.1) hi).symm
      _ = 1 - (((i.1 + 1 : ℕ) : ℝ) / ((k + 3 : ℕ) : ℝ)) := hprofile i.1 hi
      _ = smoothLowerBoundFunctionStationaryPoint (Nat.succPNat (k + 1)) i := by
        rw [smoothLowerBoundFunctionStationaryPoint_apply]
        have hden : (((Nat.succPNat (k + 1) : ℕ) : ℝ) + 1) = ((k + 3 : ℕ) : ℝ) := by
          norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm]
        rw [hden]
        norm_num

/-- Helper for Text 2.13: the affine-profile point solves `A_k y = e₁`. -/
private theorem pathTridiagonal_mulVec_stationaryPoint
    (k : ℕ) :
    Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k))
      (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k)) =
        (EuclideanSpace.single (0 : Fin (k + 1)) (1 : ℝ)).ofLp := by
  cases' k with k
  · ext i
    fin_cases i
    -- In dimension one, the matrix equation is a direct scalar computation.
    simp [Matrix.mulVec, dotProduct, pathTridiagonalMatrix_apply,
      smoothLowerBoundFunctionStationaryPoint_apply, EuclideanSpace.single]
    norm_num
  · ext i
    by_cases hi0 : i = 0
    · subst hi0
      -- The first row checks the head equation of the affine profile.
      rw [pathTridiagonal_mulVec_apply_head]
      simp [smoothLowerBoundFunctionStationaryPoint_apply, EuclideanSpace.single]
      field_simp
      simp [EuclideanSpace.single]
      ring_nf
      split_ifs with hzero
      · simp
      · exfalso
        exact hzero rfl
    · by_cases hilast : i = Fin.last (k + 1)
      · subst hilast
        -- The last row checks the tail boundary condition of the affine profile.
        rw [pathTridiagonal_mulVec_apply_tail]
        simp [smoothLowerBoundFunctionStationaryPoint_apply, EuclideanSpace.single]
        field_simp
        ring_nf
      · let t := i.1 - 1
        have ht : t < k := by
          have hi_pos : 0 < i.1 := Nat.pos_of_ne_zero (by
            intro hzero
            apply hi0
            ext
            simpa using hzero)
          have hi_le_last : i.1 ≤ k + 1 := Nat.le_of_lt_succ i.2
          have hi_ne_last_val : i.1 ≠ k + 1 := by
            intro hi_last
            apply hilast
            ext
            simpa [Fin.val_last] using hi_last
          have hi_lt_last : i.1 < k + 1 := lt_of_le_of_ne hi_le_last hi_ne_last_val
          dsimp [t]
          omega
        have hi_pos' : 1 ≤ i.1 := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (by
          intro hzero
          apply hi0
          ext
          simpa using hzero))
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
        -- Every interior row matches the constant-second-difference affine profile.
        rw [hi_eq, pathTridiagonal_mulVec_apply_middle k _ t ht ht0 ht1 ht2]
        have hne0 : (⟨t + 1, ht1⟩ : Fin (k + 2)) ≠ 0 := by
          intro hzero
          apply hi0
          calc
            i = ⟨t + 1, ht1⟩ := hi_eq
            _ = 0 := hzero
        simp [smoothLowerBoundFunctionStationaryPoint_apply, EuclideanSpace.single, hne0]
        field_simp
        ring_nf

/-- Helper for Text 2.13: the affine-profile point is stationary for the prefix quadratic. -/
private theorem smoothLowerBoundFunctionStationaryPoint_hasGradientAt_zero
    (L : ℝ) (k : ℕ) :
    HasGradientAt (smoothLowerBoundFunction L (Nat.succPNat k)) 0
      (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k)) := by
  have hdiff := smoothLowerBoundFunction_differentiableAt L k
    (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k))
  refine (hasGradientAt_zero_iff_gradient_eq_zero hdiff).2 ?_
  ext i
  -- The direct residual formula vanishes because the affine profile solves `A_k y = e₁`.
  have hgrad := smoothLowerBoundFunction_gradient_eq_scaled_residual_apply
    L k (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k)) i
  have hres := congrFun (pathTridiagonal_mulVec_stationaryPoint k) i
  rw [hres] at hgrad
  simpa using hgrad

/-- Helper for Text 2.13: zero gradient on the prefix quadratic forces the affine profile. -/
private theorem gradient_eq_zero_iff_eq_smoothLowerBoundFunctionStationaryPoint
    {L : ℝ} (hL : L ≠ 0) (k : ℕ) {y : EuclideanSpace ℝ (Fin (k + 1))} :
    ∇ (smoothLowerBoundFunction L (Nat.succPNat k)) y = 0 ↔
      y = smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k) := by
  constructor
  · intro hgrad0
    -- Cancel the nonzero scalar `(L / 4)` in the coordinatewise residual formula.
    have hL4 : L / 4 ≠ 0 := by
      intro hzero
      apply hL
      nlinarith
    have hres :
        Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k)) y =
          EuclideanSpace.single (0 : Fin (k + 1)) (1 : ℝ) := by
      ext i
      have hi := congrArg (fun z : EuclideanSpace ℝ (Fin (k + 1)) ↦ z i) hgrad0
      have hi0 : (∇ (smoothLowerBoundFunction L (Nat.succPNat k)) y) i = 0 := by
        simpa using hi
      rw [smoothLowerBoundFunction_gradient_eq_scaled_residual_apply] at hi0
      have hi' :
          (L / 4) *
              ((Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k)) y) i -
                if i = 0 then 1 else 0) =
            (L / 4) * 0 := by
        simpa using hi0
      have hcoord0 :
          ((Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k)) y) i -
              if i = 0 then 1 else 0) = 0 :=
        mul_left_cancel₀ hL4 hi'
      have hcoord :
          (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k)) y) i =
            if i = 0 then 1 else 0 := by
        linarith
      simpa [EuclideanSpace.single] using hcoord
    exact pathTridiagonal_solution_eq_stationaryPoint k hres
  · intro hy
    -- Substituting the solved point recovers the already proved stationarity statement.
    simpa [hy] using
      (smoothLowerBoundFunctionStationaryPoint_hasGradientAt_zero L k).gradient

/-- Helper for Text 2.13: any solution of `A_k y = e₁` is the affine-profile point. -/
private theorem eq_smoothLowerBoundFunctionStationaryPoint_of_pathTridiagonal_mulVec_eq_single
    (k : ℕ) {y : EuclideanSpace ℝ (Fin (k + 1))}
    (hy : Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k)) y =
      EuclideanSpace.single (0 : Fin (k + 1)) (1 : ℝ)) :
    y = smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k) := by
  -- This is exactly the uniqueness theorem for the tridiagonal linear system.
  exact pathTridiagonal_solution_eq_stationaryPoint k hy

/-- The canonical hard-instance stationary point is stationary for the owner objective
`quadraticHardInstanceFamily L k`. -/
-- Proof sketch: rewrite `quadraticHardInstanceFamily L k` as the lower-bound quadratic on the
-- first `k.1 + 1` coordinates, compute the gradient there, and use the explicit coordinate formula
-- of `quadraticHardInstanceStationaryPoint k`.
theorem quadraticHardInstanceStationaryPoint_hasGradientAt_zero
    (L : ℝ) (k : Fin n) :
    HasGradientAt (quadraticHardInstanceFamily L k) 0
      (quadraticHardInstanceStationaryPoint k) := by
  have hdiff :
      DifferentiableAt ℝ (quadraticHardInstanceFamily L k)
        (quadraticHardInstanceStationaryPoint k) := by
    -- Differentiate the ambient hard instance through its prefix factorization.
    rw [quadraticHardInstanceFamily_eq_comp_prefixProjection]
    simpa [prefixProjectionContinuous] using
      (smoothLowerBoundFunction_differentiableAt L k.1
        (prefixProjection k (quadraticHardInstanceStationaryPoint k))).comp
          (quadraticHardInstanceStationaryPoint k)
          (prefixProjectionContinuous k).differentiableAt
  refine (hasGradientAt_zero_iff_gradient_eq_zero hdiff).2 ?_
  -- Rewrite the ambient gradient through the prefix model and use prefix stationarity.
  rw [quadraticHardInstanceFamily_gradient_eq_zeroTail_prefixGradient]
  have hprefix_grad0 :
      ∇ (smoothLowerBoundFunction L (Nat.succPNat k.1))
        (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k.1)) = 0 :=
    (smoothLowerBoundFunctionStationaryPoint_hasGradientAt_zero L k.1).gradient
  have hzeroTail :
      zeroTailEmbedding k
        (∇ (smoothLowerBoundFunction L (Nat.succPNat k.1))
          (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k.1))) =
        zeroTailEmbedding k 0 :=
    congrArg (zeroTailEmbedding k) hprefix_grad0
  simpa [quadraticHardInstanceStationaryPoint, prefixProjection_zeroTailEmbedding] using hzeroTail

/-- Text 2.13: on the leading-coordinate subspace `ℝ^{k.1 + 1,n}`, a point is stationary for
`quadraticHardInstanceFamily L k` if and only if it is the canonical affine-profile point whose
coordinates are given by `quadraticHardInstanceStationaryPoint_apply`; equivalently, the equation
`∇ f_k(x) = A_k x - e₁ = 0` has the unique solution described in the text. -/
-- Proof sketch: the stationary equation of `quadraticHardInstanceFamily L k` on the active
-- coordinates is the tridiagonal system `A_{k.1 + 1} x = e₁`; on `ℝ^{k.1 + 1,n}`
-- the tail is already fixed to zero, and solving the tridiagonal recurrence determines the active
-- coordinates uniquely as `quadraticHardInstanceStationaryPoint k`.
theorem hasGradientAt_zero_iff_eq_quadraticHardInstanceStationaryPoint_of_mem_coordinateSubspace
    {L : ℝ} (hL : L ≠ 0) (k : Fin n) {x : E} (hx_mem : x ∈ ℝ^{k.1 + 1,n}) :
    HasGradientAt (quadraticHardInstanceFamily L k) 0 x ↔
      x = quadraticHardInstanceStationaryPoint k := by
  constructor
  · intro hx
    -- Route correction: use the already-stable ambient gradient pullback, then recover the
    -- prefix point from the coordinate-subspace reconstruction.
    have hgrad0 : ∇ (quadraticHardInstanceFamily L k) x = 0 := hx.gradient
    rw [quadraticHardInstanceFamily_gradient_eq_zeroTail_prefixGradient] at hgrad0
    have hprefix0 :
        ∇ (smoothLowerBoundFunction L (Nat.succPNat k.1)) (prefixProjection k x) = 0 := by
      -- Applying the left inverse `prefixProjection` removes the zero-tail embedding.
      have hproj := congrArg (prefixProjection k) hgrad0
      simpa [prefixProjection_zeroTailEmbedding] using hproj
    have hprefix_eq :
        prefixProjection k x =
          smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k.1) :=
      (gradient_eq_zero_iff_eq_smoothLowerBoundFunctionStationaryPoint hL k.1).1 hprefix0
    calc
      x = zeroTailEmbedding k (prefixProjection k x) := by
        exact eq_zeroTailEmbedding_of_mem_coordinateSubspace k hx_mem
      _ = zeroTailEmbedding k (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k.1)) := by
            rw [hprefix_eq]
      _ = quadraticHardInstanceStationaryPoint k := rfl
  · intro hx
    subst hx
    exact quadraticHardInstanceStationaryPoint_hasGradientAt_zero L k

end

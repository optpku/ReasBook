/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_29
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Text_2_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Text_2_16

-- Declarations for this item will be appended below by the statement pipeline.

open Finset
open scoped Gradient SmoothConvex

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "p" => normSeminorm ℝ E

/-- Helper for Theorem 2.8: the leading-coordinate subspace `ℝ^{k,n}` consists of vectors in
`ℝⁿ` whose coordinates with zero-based index at least `k` vanish. -/
private def coordinateSubspace (k n : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.comap (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv.toLinearMap
    (Submodule.pi Set.univ (fun i : Fin n ↦ if i.1 < k then ⊤ else ⊥))

scoped[CoordinateSubspace] notation "ℝ^{" k "," n "}" => coordinateSubspace k n
open scoped CoordinateSubspace

/-- Helper for Theorem 2.8: membership in `ℝ^{k,n}` is equivalent to vanishing of all coordinates
with zero-based index at least `k`. -/
private theorem mem_coordinateSubspace_iff {k n : ℕ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ ℝ^{k,n} ↔ ∀ i : Fin n, k ≤ i.1 → x i = 0 := by
  constructor
  · intro hx i hi
    simpa [hi, not_lt.mpr hi] using hx i
  · intro hx i
    by_cases hi : i.1 < k
    · simp [hi]
    · have hki : k ≤ i.1 := Nat.le_of_not_lt hi
      simp [hi, hx i hki]

/- Theorem 2.8 lies in the finite-dimensional smooth convex lower-bound domain.

Sampled owner-style declarations for this refinement:
* `SatisfiesSpanCondition method` from `Definition_2_9`, the owner predicate for first-order
  span-condition iterate families;
* `quadraticHardInstanceFamily_mem_smooth_convex_objective` from `Text_2_11`, the owner
  smoothness-membership theorem for the chapter hard instance;
* `quadraticHardInstanceStationaryPoint_isMinOn` from `Text_2_14`, the owner minimizer theorem
  for the canonical hard-instance stationary point;
* `quadraticHardInstanceFamily L k` and `quadraticHardInstanceStationaryPoint k` from
  `Definition_2_10` / `Text_2_13`, the chapter-owner hard instance and its canonical minimizer.

Best owner abstraction:
* core/canonical: the translated owner hard instance
  `fun x ↦ quadraticHardInstanceFamily (L : ℝ) hardIndex (x - x0)` together with its translated
  canonical minimizer `x0 + quadraticHardInstanceStationaryPoint hardIndex`;
* source-facing: the existential packaging `∃ f, ∃ xStar, ...`;
* bridge/view: the existential witness obtained from the explicit owner hard instance.

Primitive data:
* the hard-instance index `hardIndex`;
* the translated hard-instance objective;
* the translated canonical minimizer.

Derived API:
* membership of the translated hard instance in `𝓕_L^{1,1}(ℝⁿ)`;
* the global minimizer predicate for the translated canonical stationary point, derived from the
  owner theorem `quadraticHardInstanceStationaryPoint_isMinOn`;
* the iteratewise lower bounds for every span-condition method.

Accordingly, the file first states the core lower bound for the explicit translated owner hard
instance and then derives the textbook existential theorem as a thin bridge.
-/

private theorem two_mul_lt_of_one_le_of_le_half_sub
    {n k : ℕ} (hk₁ : 1 ≤ k) (hk₂ : k ≤ (n - 1) / 2) :
    2 * k < n := by
  omega

/-- Helper for Theorem 2.8: if each prefix gradient already lies in its natural coordinate
subspace `ℝ^{j+1,n}`, then the span of the first `k` such vectors lies in `ℝ^{k,n}`. -/
-- Proof sketch: use `Submodule.span_le` and rewrite coordinate-subspace membership
-- coordinatewise. A vector supported on the first `j + 1` coordinates is automatically supported
-- on the first `k` coordinates whenever `j < k`.
private theorem prefix_span_le_coordinateSubspace {k : ℕ}
    (g : ℕ → E)
    (hg : ∀ j : Fin k, g j ∈ ℝ^{j.1 + 1,n}) :
    Submodule.span ℝ (Set.range fun j : Fin k ↦ g j) ≤ ℝ^{k,n} := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨j, rfl⟩
  have hj : g j ∈ ℝ^{j.1 + 1,n} := hg j
  change g j ∈ ℝ^{k,n}
  rw [mem_coordinateSubspace_iff] at hj ⊢
  intro i hik
  exact hj i (le_trans (Nat.succ_le_of_lt j.is_lt) hik)

/-- Helper for Theorem 2.8: translating the quadratic hard instance by `x₀` only shifts the
gradient evaluation point from `x` to `x - x₀`. -/
-- Proof sketch: differentiate the untranslated hard instance at `x - x₀`, compose with the
-- translation map `y ↦ y - x₀`, and read off the resulting gradient by uniqueness.
private theorem quadraticHardInstanceFamily_translate_gradient_eq
    (L : NNReal) (hardIndex : Fin n) (x0 x : E) :
    ∇ (fun y ↦ quadraticHardInstanceFamily (L : ℝ) hardIndex (y - x0)) x =
      ∇ (quadraticHardInstanceFamily (L : ℝ) hardIndex) (x - x0) := by
  let g : E → ℝ := quadraticHardInstanceFamily (L : ℝ) hardIndex
  have hg : g ∈ (𝓕[L, p]¹¹ : Set (E → ℝ)) :=
    quadraticHardInstanceFamily_mem_smooth_convex_objective L hardIndex
  rw [mem_F11_iff] at hg
  -- Differentiate the owner hard instance at the translated point.
  have hx : HasGradientAt g (∇ g (x - x0)) (x - x0) :=
    hg.hasGradientAt (x - x0)
  have hsub : HasFDerivAt (fun y : E ↦ y - x0) (ContinuousLinearMap.id ℝ E) x := by
    simpa using (hasFDerivAt_id x).sub_const x0
  have htranslate :
      HasGradientAt (fun y : E ↦ g (y - x0)) (∇ g (x - x0)) x := by
    simpa [g, Function.comp_def] using (hx.hasFDerivAt.comp x hsub).hasGradientAt
  simpa [g] using htranslate.gradient

/-- Helper for Theorem 2.8: translating the quadratic hard instance by the prescribed initial point
preserves membership in the smooth-convex owner class `𝓕[L, p]¹¹`. -/
-- Proof sketch: rewrite owner membership as `ConvexC1SeminormSmooth`, then transport the three
-- ingredients separately along the affine translation `x ↦ x - x₀`: `C¹` regularity by
-- composition, convexity by `ConvexOn.translate_right`, and the gradient-Lipschitz estimate by
-- the explicit translated gradient formula.
private theorem quadraticHardInstanceFamily_translate_mem_smooth_convex_objective
    (L : NNReal) (hardIndex : Fin n) (x0 : E) :
    (fun x ↦ quadraticHardInstanceFamily (L : ℝ) hardIndex (x - x0)) ∈
      (𝓕[L, p]¹¹ : Set (E → ℝ)) := by
  let g : E → ℝ := quadraticHardInstanceFamily (L : ℝ) hardIndex
  have hg : g ∈ (𝓕[L, p]¹¹ : Set (E → ℝ)) :=
    quadraticHardInstanceFamily_mem_smooth_convex_objective L hardIndex
  rw [mem_F11_iff] at hg ⊢
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · -- Compose the `C¹` hard instance with the ambient translation map.
      rw [contDiffOn_univ]
      have htranslate : ContDiff ℝ 1 (fun x : E ↦ x - x0) := by
        simpa [sub_eq_add_neg] using
          contDiff_id.add (contDiff_const : ContDiff ℝ 1 fun _ : E ↦ -x0)
      simpa [g, Function.comp_def] using hg.contDiff.comp htranslate
    · -- Whole-space convexity is preserved by translating the argument.
      simpa [g, Set.preimage_univ, sub_eq_add_neg, Function.comp_def, add_comm] using
        (hg.convexOn.translate_right (-x0))
  · intro x _
    -- Differentiate the translated objective by the chain rule through `x ↦ x - x₀`.
    have hx : HasGradientAt g (∇ g (x - x0)) (x - x0) :=
      hg.hasGradientAt (x - x0)
    have hsub : HasFDerivAt (fun y : E ↦ y - x0) (ContinuousLinearMap.id ℝ E) x := by
      simpa using (hasFDerivAt_id x).sub_const x0
    have htranslate :
        HasGradientAt (fun y : E ↦ g (y - x0)) (∇ g (x - x0)) x := by
      simpa [g, Function.comp_def] using (hx.hasFDerivAt.comp x hsub).hasGradientAt
    simpa [g, quadraticHardInstanceFamily_translate_gradient_eq L hardIndex x0 x] using htranslate
  · intro x _ y _
    -- The translated gradient differences are exactly the untranslated ones at shifted points.
    have hx : ∇ (fun z : E ↦ g (z - x0)) x = ∇ g (x - x0) :=
      quadraticHardInstanceFamily_translate_gradient_eq L hardIndex x0 x
    have hy : ∇ (fun z : E ↦ g (z - x0)) y = ∇ g (y - x0) :=
      quadraticHardInstanceFamily_translate_gradient_eq L hardIndex x0 y
    rw [hx, hy]
    simpa [g, sub_eq_add_neg, sub_add_eq_sub_sub] using
      hg.dualNorm_gradient_sub_le (x - x0) (y - x0)

/-- Helper for Theorem 2.8: the hard instance is the lower-bound quadratic composed with the
explicit linear projection onto its active prefix coordinates. -/
private def hardInstancePrefixLinear (hardIndex : Fin n) :
    E →L[ℝ] EuclideanSpace ℝ (Fin (hardIndex.1 + 1)) :=
  ((EuclideanSpace.equiv (Fin (hardIndex.1 + 1)) ℝ).symm.toContinuousLinearEquiv :
      (Fin (hardIndex.1 + 1) → ℝ) ≃L[ℝ]
        EuclideanSpace ℝ (Fin (hardIndex.1 + 1))).toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun i : Fin (hardIndex.1 + 1) =>
        (ContinuousLinearMap.proj (R := ℝ)
          (i := Fin.castLE (Nat.succ_le_of_lt hardIndex.2) i) :
            (Fin n → ℝ) →L[ℝ] ℝ)).comp
      ((EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearEquiv.toContinuousLinearMap))

/-- Helper for Theorem 2.8: the explicit prefix projection reads off the corresponding active
coordinate. -/
private theorem hardInstancePrefix_eq_linear
    (hardIndex : Fin n) :
    hardInstancePrefixLinear hardIndex =
      fun x : E ↦
      (EuclideanSpace.equiv (Fin (hardIndex.1 + 1)) ℝ).symm
        (fun i ↦ x (Fin.castLE (Nat.succ_le_of_lt hardIndex.2) i)) := by
  ext x i
  -- Expand the linear projection and evaluate the selected coordinate.
  simp [hardInstancePrefixLinear]

/-- Helper for Theorem 2.8: the explicit prefix projection reads off the corresponding active
coordinate. -/
@[simp] private theorem hardInstancePrefixLinear_apply
    (hardIndex : Fin n) (x : E) (i : Fin (hardIndex.1 + 1)) :
    hardInstancePrefixLinear hardIndex x i =
      x (Fin.castLE (Nat.succ_le_of_lt hardIndex.2) i) := by
  simp [hardInstancePrefix_eq_linear]

/-- Helper for Theorem 2.8: extend a prefix vector back to `ℝⁿ` by keeping the active
coordinates and filling the tail with `0`. -/
private def hardInstanceZeroTailLinear (hardIndex : Fin n) :
    EuclideanSpace ℝ (Fin (hardIndex.1 + 1)) →L[ℝ] E :=
  (hardInstancePrefixLinear hardIndex).adjoint

/-- Helper for Theorem 2.8: evaluating the zero-tail extension keeps active coordinates and kills
the ambient tail. -/
@[simp] private theorem hardInstanceZeroTailLinear_apply
    (hardIndex : Fin n) (x : EuclideanSpace ℝ (Fin (hardIndex.1 + 1))) (i : Fin n) :
    hardInstanceZeroTailLinear hardIndex x i =
      if h : i ≤ hardIndex then x ⟨i.1, Nat.lt_succ_of_le h⟩ else 0 := by
  by_cases hi : i ≤ hardIndex
  · have hinner :
        inner ℝ ((hardInstanceZeroTailLinear hardIndex) x)
            (EuclideanSpace.single i (1 : ℝ)) =
          inner ℝ x
            (hardInstancePrefixLinear hardIndex (EuclideanSpace.single i (1 : ℝ))) := by
      simpa [hardInstanceZeroTailLinear] using
        (hardInstancePrefixLinear hardIndex).adjoint_inner_left
          (EuclideanSpace.single i (1 : ℝ)) x
    have hsingle :
        hardInstancePrefixLinear hardIndex (EuclideanSpace.single i (1 : ℝ)) =
          EuclideanSpace.single ⟨i.1, Nat.lt_succ_of_le hi⟩ (1 : ℝ) := by
      ext j
      by_cases hij : j = ⟨i.1, Nat.lt_succ_of_le hi⟩
      · subst hij
        simp [hardInstancePrefixLinear_apply]
      · have hne : Fin.castLE (Nat.succ_le_of_lt hardIndex.2) j ≠ i := by
          intro hji
          have hcast : j = ⟨i.1, Nat.lt_succ_of_le hi⟩ := by
            ext
            simpa using congrArg Fin.val hji
          exact hij hcast
        simp [hardInstancePrefixLinear_apply, hne, EuclideanSpace.single, hij]
    have hcoord :
        ((hardInstanceZeroTailLinear hardIndex) x) i =
          x ⟨i.1, Nat.lt_succ_of_le hi⟩ := by
      rw [hsingle] at hinner
      calc
        ((hardInstanceZeroTailLinear hardIndex) x) i =
            inner ℝ ((hardInstanceZeroTailLinear hardIndex) x)
              (EuclideanSpace.single i (1 : ℝ)) := by
                symm
                simpa using
                  (EuclideanSpace.inner_single_right i (1 : ℝ)
                    ((hardInstanceZeroTailLinear hardIndex) x))
        _ = inner ℝ x (EuclideanSpace.single ⟨i.1, Nat.lt_succ_of_le hi⟩ (1 : ℝ)) := by
              simpa [hsingle] using hinner
        _ = x ⟨i.1, Nat.lt_succ_of_le hi⟩ := by
              simpa using
                (EuclideanSpace.inner_single_right ⟨i.1, Nat.lt_succ_of_le hi⟩
                  (1 : ℝ) x)
    simpa [hi] using hcoord
  · have hinner :
        inner ℝ ((hardInstanceZeroTailLinear hardIndex) x)
            (EuclideanSpace.single i (1 : ℝ)) =
          inner ℝ x
            (hardInstancePrefixLinear hardIndex (EuclideanSpace.single i (1 : ℝ))) := by
      simpa [hardInstanceZeroTailLinear] using
        (hardInstancePrefixLinear hardIndex).adjoint_inner_left
          (EuclideanSpace.single i (1 : ℝ)) x
    have hzero :
        hardInstancePrefixLinear hardIndex (EuclideanSpace.single i (1 : ℝ)) = 0 := by
      ext j
      have hne : Fin.castLE (Nat.succ_le_of_lt hardIndex.2) j ≠ i := by
        intro hji
        have hle : i ≤ hardIndex := by
          refine Fin.le_iff_val_le_val.mpr ?_
          have hcast : i.1 = j.1 := by
            simpa using congrArg Fin.val hji.symm
          simpa [hcast] using Nat.le_of_lt_succ j.2
        exact hi hle
      simp [hardInstancePrefixLinear_apply, hne]
    have hcoord : ((hardInstanceZeroTailLinear hardIndex) x) i = 0 := by
      rw [hzero] at hinner
      calc
        ((hardInstanceZeroTailLinear hardIndex) x) i =
            inner ℝ ((hardInstanceZeroTailLinear hardIndex) x)
              (EuclideanSpace.single i (1 : ℝ)) := by
                symm
                simpa using
                  (EuclideanSpace.inner_single_right i (1 : ℝ)
                    ((hardInstanceZeroTailLinear hardIndex) x))
        _ = inner ℝ x 0 := by
              simpa [hzero] using hinner
        _ = 0 := by simp
    simpa [hi] using hcoord

/-- Helper for Theorem 2.8: the canonical hard-instance stationary point is obtained by extending
the affine-profile stationary point of the prefix lower-bound quadratic by a zero tail. -/
private def quadraticHardInstanceStationaryPoint (hardIndex : Fin n) : E :=
  hardInstanceZeroTailLinear hardIndex
    (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat hardIndex.1))

/-- Helper for Theorem 2.8: evaluating the hard-instance stationary point returns the affine
profile on the active prefix and `0` on the ambient tail. -/
@[simp] private theorem quadraticHardInstanceStationaryPoint_apply
    (hardIndex : Fin n) (i : Fin n) :
    quadraticHardInstanceStationaryPoint hardIndex i =
      if i ≤ hardIndex then
        1 - (((i.1 + 1 : ℕ) : ℝ) / ((hardIndex.1 + 2 : ℕ) : ℝ))
      else
        0 := by
  by_cases hi : i ≤ hardIndex
  · simp [quadraticHardInstanceStationaryPoint, hardInstanceZeroTailLinear_apply, hi]
    ring
  · simp [quadraticHardInstanceStationaryPoint, hardInstanceZeroTailLinear_apply, hi]

/-- Helper for Theorem 2.8: restricting the hard-instance stationary point back to the active
prefix recovers the prefix stationary point exactly. -/
private theorem hardInstancePrefixLinear_stationaryPoint
    (hardIndex : Fin n) :
    hardInstancePrefixLinear hardIndex (quadraticHardInstanceStationaryPoint hardIndex) =
      smoothLowerBoundFunctionStationaryPoint (Nat.succPNat hardIndex.1) := by
  ext i
  rw [hardInstancePrefixLinear_apply]
  have hi : Fin.castLE (Nat.succ_le_of_lt hardIndex.2) i ≤ hardIndex :=
    Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ i.2)
  simp [
    quadraticHardInstanceStationaryPoint_apply,
    hi,
    smoothLowerBoundFunctionStationaryPoint_apply
  ]
  ring

/-- Helper for Theorem 2.8: evaluating the hard instance at its stationary point reduces to the
prefix lower-bound quadratic at the affine-profile stationary point. -/
private theorem quadraticHardInstanceFamily_stationaryPoint_eq_smoothLowerBoundFunction
    (L : NNReal) (hardIndex : Fin n) :
    quadraticHardInstanceFamily (L : ℝ) hardIndex
        (quadraticHardInstanceStationaryPoint hardIndex) =
      smoothLowerBoundFunction (L : ℝ) (Nat.succPNat hardIndex.1)
        (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat hardIndex.1)) := by
  rw [quadraticHardInstanceFamily, quadraticHardInstanceStationaryPoint]
  congr
  ext i
  change quadraticHardInstanceStationaryPoint hardIndex
      (Fin.castLE (Nat.succ_le_of_lt hardIndex.2) i) = _
  have hi : Fin.castLE (Nat.succ_le_of_lt hardIndex.2) i ≤ hardIndex :=
    Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ i.2)
  simp [quadraticHardInstanceStationaryPoint_apply, hi]
  ring

/-- Helper for Theorem 2.8: each tridiagonal entry contributes its diagonal term and subtracts its
two neighboring terms. -/
private theorem pathTridiagonal_entry_mul_eq_diag_sub_neighbors
    {m : ℕ} (y : EuclideanSpace ℝ (Fin (m + 1))) (i j : Fin (m + 1)) :
    pathTridiagonalMatrix (Nat.succPNat m) i j * y j =
      (if i = j then 2 * y j else 0) -
      (if (i : ℕ) + 1 = (j : ℕ) then y j else 0) -
      (if (j : ℕ) + 1 = (i : ℕ) then y j else 0) := by
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

/-- Helper for Theorem 2.8: the first row of the path tridiagonal matrix reads `2 y₀ - y₁`. -/
private theorem pathTridiagonal_mulVec_apply_head
    (k : ℕ) (y : EuclideanSpace ℝ (Fin (k + 2))) :
    (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (k + 1))) y) 0 =
      2 * y 0 - y ⟨1, by omega⟩ := by
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
    simp
  rw [hdiag, hnext, hprev]
  ring_nf

/-- Helper for Theorem 2.8: every interior row of the path tridiagonal matrix reads
`2 yᵢ - yᵢ₋₁ - yᵢ₊₁`. -/
private theorem pathTridiagonal_mulVec_apply_middle
    (k : ℕ) (y : EuclideanSpace ℝ (Fin (k + 2))) (t : ℕ) (_ht : t < k)
    (ht0 : t < k + 2) (ht1 : t + 1 < k + 2) (ht2 : t + 2 < k + 2) :
    (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (k + 1))) y) ⟨t + 1, ht1⟩ =
      2 * y ⟨t + 1, ht1⟩ - y ⟨t, ht0⟩ - y ⟨t + 2, ht2⟩ := by
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

/-- Helper for Theorem 2.8: the last row of the path tridiagonal matrix reads `2 y_k - y_{k-1}`. -/
private theorem pathTridiagonal_mulVec_apply_tail
    (k : ℕ) (y : EuclideanSpace ℝ (Fin (k + 2))) :
    (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (k + 1))) y) (Fin.last (k + 1)) =
      2 * y (Fin.last (k + 1)) - y ⟨k, by omega⟩ := by
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

/-- Helper for Theorem 2.8: once a prefix vector vanishes from coordinate `j` onward, every
tridiagonal row from `j + 1` onward already evaluates to `0`. -/
private theorem pathTridiagonal_mulVec_eq_zero_of_vanishing_from
    (m j : ℕ) (y : EuclideanSpace ℝ (Fin (m + 1)))
    {i : Fin (m + 1)} (hy : ∀ t : Fin (m + 1), j ≤ t.1 → y t = 0)
    (hi : j + 1 ≤ i.1) :
    ((pathTridiagonalMatrix (Nat.succPNat m)).mulVec y) i = 0 := by
  cases' m with m
  · exfalso
    omega
  · by_cases hilast : i = Fin.last (m + 1)
    · subst hilast
      -- The tail row only sees the last two coordinates, and both vanish.
      rw [pathTridiagonal_mulVec_apply_tail]
      have hjlast : j ≤ (Fin.last (m + 1)).1 := by
        exact le_trans (Nat.le_succ j) (by simpa [Fin.val_last] using hi)
      have hjm : j ≤ (⟨m, by omega⟩ : Fin (m + 2)).1 := by
        have hjm1 : j + 1 ≤ m + 1 := by
          simpa [Fin.val_last] using hi
        exact Nat.succ_le_succ_iff.mp hjm1
      have hlast : y (Fin.last (m + 1)) = 0 := by
        exact hy _ hjlast
      have hprev : y ⟨m, by omega⟩ = 0 := by
        exact hy _ hjm
      rw [hlast, hprev]
      ring
    · let t := i.1 - 1
      have hi_pos : 0 < i.1 := by
        omega
      have ht : t < m := by
        have hi_le_last : i.1 ≤ m + 1 := Nat.le_of_lt_succ i.2
        have hi_ne_last_val : i.1 ≠ m + 1 := by
          intro hi_last
          apply hilast
          ext
          simpa [Fin.val_last] using hi_last
        have hi_lt_last : i.1 < m + 1 := lt_of_le_of_ne hi_le_last hi_ne_last_val
        dsimp [t]
        omega
      have hi_pos' : 1 ≤ i.1 := Nat.succ_le_of_lt hi_pos
      have ht0 : t < m + 2 := by
        dsimp [t]
        omega
      have ht1 : t + 1 < m + 2 := by
        dsimp [t]
        omega
      have ht2 : t + 2 < m + 2 := by
        dsimp [t]
        omega
      have hi_eq : i = ⟨t + 1, ht1⟩ := by
        ext
        dsimp [t]
        rw [Nat.sub_add_cancel hi_pos']
      -- Every interior row only sees three consecutive zero coordinates.
      rw [hi_eq]
      change ((pathTridiagonalMatrix (Nat.succPNat (m + 1))).mulVec y) ⟨t + 1, ht1⟩ = 0
      rw [pathTridiagonal_mulVec_apply_middle m _ t ht ht0 ht1 ht2]
      have hmid : y ⟨t + 1, ht1⟩ = 0 := by
        exact hy _ (by
          dsimp [t]
          omega)
      have hprev : y ⟨t, ht0⟩ = 0 := by
        exact hy _ (by
          dsimp [t]
          omega)
      have hnext : y ⟨t + 2, ht2⟩ = 0 := by
        exact hy _ (by
          dsimp [t]
          omega)
      rw [hmid, hprev, hnext]
      ring

/-- Helper for Theorem 2.8: the prefix gradient is `(L / 4)` times the residual `A_k y - e₁`. -/
private theorem smoothLowerBoundFunction_gradient_eq_scaled_residual
    (L : ℝ) (k : ℕ) (y : EuclideanSpace ℝ (Fin (Nat.succPNat k))) :
    ∇ (smoothLowerBoundFunction L (Nat.succPNat k)) y =
      (L / 4) •
        (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k)) y -
          EuclideanSpace.single (0 : Fin (Nat.succPNat k)) (1 : ℝ)) := by
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
  have htoLp :
      ((((L / 4) • pathTridiagonalMatrix (Nat.succPNat k)).toEuclideanLin y).ofLp) =
        Matrix.mulVec (((L / 4) • pathTridiagonalMatrix (Nat.succPNat k))) y.ofLp := by
    simpa [Matrix.toLin'_apply] using
      (Matrix.ofLp_toLpLin (2 : ENNReal) (2 : ENNReal)
        (((L / 4) • pathTridiagonalMatrix (Nat.succPNat k))) y)
  rw [htoLp]
  rw [Matrix.smul_mulVec, Pi.smul_apply]
  simp [EuclideanSpace.single]
  ring_nf

/-- Helper for Theorem 2.8: the coordinate form of the prefix gradient residual formula is the
expected scalar identity. -/
private theorem smoothLowerBoundFunction_gradient_eq_scaled_residual_apply
    (L : ℝ) (k : ℕ) (y : EuclideanSpace ℝ (Fin (Nat.succPNat k)))
    (i : Fin (Nat.succPNat k)) :
    (∇ (smoothLowerBoundFunction L (Nat.succPNat k)) y).ofLp i =
      (L / 4) * (((pathTridiagonalMatrix (Nat.succPNat k)).mulVec y.ofLp) i -
        (EuclideanSpace.single 0 (1 : ℝ)).ofLp i) := by
  -- Read the vector-valued residual identity at the coordinate `i`.
  simpa [Pi.smul_apply, EuclideanSpace.single] using
    congrFun (smoothLowerBoundFunction_gradient_eq_scaled_residual L k y) i

/-- Helper for Theorem 2.8: `smoothLowerBoundFunction` is differentiable at every prefix point. -/
private theorem smoothLowerBoundFunction_differentiableAt
    (L : ℝ) (k : ℕ) (y : EuclideanSpace ℝ (Fin (k + 1))) :
    DifferentiableAt ℝ (smoothLowerBoundFunction L (Nat.succPNat k)) y := by
  have hcont : ContDiff ℝ 1 (smoothLowerBoundFunction L (Nat.succPNat k)) := by
    simpa [smoothLowerBoundFunction] using
      (symmetric_quadratic_contDiff_and_gradient_lipschitz 0
        (-(L / 4) • EuclideanSpace.single (0 : Fin (Nat.succPNat k)) (1 : ℝ))
        ((L / 4) • pathTridiagonalMatrix (Nat.succPNat k))
        ((pathTridiagonalMatrix_isSymm (Nat.succPNat k)).smul (L / 4))).1
  exact hcont.differentiable_one y

/-- Helper for Theorem 2.8: the head row of the affine-profile stationary point already satisfies
the scalar identity `2 y₀ - y₁ = 1`. -/
private theorem pathTridiagonal_mulVec_stationaryPoint_head
    (k : ℕ) :
    (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (k + 1)))
      (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat (k + 1)))) 0 = 1 := by
  -- Read the first row explicitly and substitute the affine profile coordinates.
  rw [pathTridiagonal_mulVec_apply_head]
  simp [smoothLowerBoundFunctionStationaryPoint_apply]
  field_simp
  ring_nf

/-- Helper for Theorem 2.8: the affine-profile stationary point solves the tridiagonal system
`A_k y = e₁`. -/
private theorem pathTridiagonal_mulVec_stationaryPoint
    (k : ℕ) :
    Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k))
      (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k)) =
        (EuclideanSpace.single (0 : Fin (k + 1)) (1 : ℝ)).ofLp := by
  cases' k with k
  · ext i
    fin_cases i
    simp [Matrix.mulVec, dotProduct, pathTridiagonalMatrix_apply,
      smoothLowerBoundFunctionStationaryPoint_apply, EuclideanSpace.single]
    norm_num
  · ext i
    by_cases hi0 : i = 0
    · subst hi0
      -- The head row is the isolated scalar identity proved above.
      simpa [EuclideanSpace.single] using pathTridiagonal_mulVec_stationaryPoint_head k
    · by_cases hilast : i = Fin.last (k + 1)
      · subst hilast
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
        have hi_ne_last : i.1 ≠ k + 1 := by
            intro hi_last
            apply hilast
            ext
            simpa [Fin.val_last] using hi_last
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
        rw [hi_eq, pathTridiagonal_mulVec_apply_middle k _ t ht ht0 ht1 ht2]
        have hne0 : (⟨t + 1, ht1⟩ : Fin (k + 2)) ≠ 0 := by
          intro hzero
          have : t + 1 = 0 := by simpa using congrArg Fin.val hzero
          omega
        simp [smoothLowerBoundFunctionStationaryPoint_apply, EuclideanSpace.single, hne0]
        field_simp
        ring_nf

/-- Helper for Theorem 2.8: the affine-profile point is stationary for the prefix quadratic. -/
private theorem smoothLowerBoundFunctionStationaryPoint_hasGradientAt_zero
    (L : ℝ) (k : ℕ) :
    HasGradientAt (smoothLowerBoundFunction L (Nat.succPNat k)) 0
      (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k)) := by
  have hdiff := smoothLowerBoundFunction_differentiableAt L k
    (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k))
  refine (hasGradientAt_zero_iff_gradient_eq_zero hdiff).2 ?_
  ext i
  -- Read the prefix gradient formula coordinatewise at the stationary point.
  have hgrad :=
    smoothLowerBoundFunction_gradient_eq_scaled_residual_apply L k
      (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k)) i
  have hres := congrFun (pathTridiagonal_mulVec_stationaryPoint k) i
  have hdiff :
      (((pathTridiagonalMatrix (Nat.succPNat k)).mulVec
          (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k)).ofLp) i -
        (EuclideanSpace.single 0 (1 : ℝ)).ofLp i) = 0 := by
    exact sub_eq_zero.mpr hres
  change
    (∇ (smoothLowerBoundFunction L (Nat.succPNat k))
      (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k))).ofLp i = 0
  calc
    (∇ (smoothLowerBoundFunction L (Nat.succPNat k))
        (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k))).ofLp i
      = (L / 4) *
          (((pathTridiagonalMatrix (Nat.succPNat k)).mulVec
              (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat k)).ofLp) i -
            (EuclideanSpace.single 0 (1 : ℝ)).ofLp i) := by
          simpa using hgrad
    _ = (L / 4) * 0 := by rw [hdiff]
    _ = 0 := by ring

/-- Helper for Theorem 2.8: evaluating the hard-instance objective at its canonical stationary
point gives the closed-form value `((L / 8) * (-1 + 1 / (k + 2)))`. -/
private theorem quadraticHardInstanceFamily_stationaryPoint_value
    (L : NNReal) (hardIndex : Fin n) :
    quadraticHardInstanceFamily (L : ℝ) hardIndex (quadraticHardInstanceStationaryPoint hardIndex) =
      ((L : ℝ) / 8) * (-1 + 1 / (((hardIndex.1 + 2 : ℕ) : ℝ))) := by
  rw [quadraticHardInstanceFamily_stationaryPoint_eq_smoothLowerBoundFunction]
  rw [smoothLowerBoundFunction_apply]
  have hdot :
      dotProduct
          (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat hardIndex.1))
          (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat hardIndex.1))
            (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat hardIndex.1))) =
        (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat hardIndex.1)) 0 := by
    rw [pathTridiagonal_mulVec_stationaryPoint]
    simp [dotProduct, EuclideanSpace.single]
  have hhead :
      (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat hardIndex.1)) 0 =
        1 - 1 / (((hardIndex.1 + 2 : ℕ) : ℝ)) := by
    simp [smoothLowerBoundFunctionStationaryPoint_apply]
    ring
  rw [hdot, hhead]
  ring

/-- Helper for Theorem 2.8: the squared Euclidean norm of the hard-instance stationary point is
the normalized sum of the first `k.1 + 1` squares. -/
private theorem quadraticHardInstanceStationaryPoint_sqNorm_eq (hardIndex : Fin n) :
    ‖quadraticHardInstanceStationaryPoint hardIndex‖ ^ 2 =
      (∑ i ∈ Icc 1 (hardIndex.1 + 1), (i : ℝ) ^ 2) / (((hardIndex.1 + 2 : ℕ) : ℝ) ^ 2) := by
  let f : ℕ → ℝ := fun i ↦
    if hi : i < n then (quadraticHardInstanceStationaryPoint hardIndex) ⟨i, hi⟩ ^ 2 else 0
  have hnorm : ‖quadraticHardInstanceStationaryPoint hardIndex‖ ^ 2 = ∑ i ∈ range n, f i := by
    calc
      ‖quadraticHardInstanceStationaryPoint hardIndex‖ ^ 2
          = ∑ i : Fin n, (quadraticHardInstanceStationaryPoint hardIndex) i ^ 2 := by
              simpa using
                (EuclideanSpace.real_norm_sq_eq (quadraticHardInstanceStationaryPoint hardIndex))
      _ = ∑ i : Fin n, f i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [f]
      _ = ∑ i ∈ range n, f i := Fin.sum_univ_eq_sum_range f n
  rw [hnorm]
  have hk1 : hardIndex.1 + 1 ≤ n := Nat.succ_le_of_lt hardIndex.2
  rw [← Finset.sum_range_add_sum_Ico f hk1]
  have htail : (∑ i ∈ Ico (hardIndex.1 + 1) n, f i) = 0 := by
    refine sum_eq_zero ?_
    intro i hi
    have hk_le_i : hardIndex.1 + 1 ≤ i := (mem_Ico.mp hi).1
    have hi_lt_n : i < n := (mem_Ico.mp hi).2
    have hk_lt_i : hardIndex.1 < i := lt_of_lt_of_le (Nat.lt_succ_self _) hk_le_i
    have hnot : ¬ (⟨i, hi_lt_n⟩ : Fin n) ≤ hardIndex := by
      exact fun h ↦ not_le_of_gt hk_lt_i (Fin.le_iff_val_le_val.mp h)
    simp [f, hi_lt_n, quadraticHardInstanceStationaryPoint_apply, hnot]
  rw [htail, add_zero]
  calc
    ∑ i ∈ range (hardIndex.1 + 1), f i
        = ∑ i ∈ range (hardIndex.1 + 1),
            ((((hardIndex.1 + 1 - i : ℕ) : ℝ) / ((hardIndex.1 + 2 : ℕ) : ℝ)) ^ 2) := by
          refine sum_congr rfl ?_
          intro i hi
          have hi_lt_n : i < n := lt_of_lt_of_le (mem_range.mp hi) hk1
          have hi_le_k : i ≤ hardIndex.1 := Nat.lt_succ_iff.mp (mem_range.mp hi)
          have hik : (⟨i, hi_lt_n⟩ : Fin n) ≤ hardIndex :=
            Fin.le_iff_val_le_val.mpr hi_le_k
          simp [f, hi_lt_n, quadraticHardInstanceStationaryPoint_apply, hik]
          field_simp
          have hreal :
              (((hardIndex.1 : ℕ) : ℝ) + 2 - ((i : ℝ) + 1)) =
                (((hardIndex.1 + 1 - i : ℕ) : ℝ)) := by
            have hi2 : i + 1 ≤ hardIndex.1 + 2 := by omega
            have hcast : (((hardIndex.1 + 2 : ℕ) : ℝ) - ((i + 1 : ℕ) : ℝ)) =
                (((hardIndex.1 + 1 - i : ℕ) : ℝ)) := by
              rw [← Nat.cast_sub hi2]
              norm_num
              omega
            simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using hcast
          rw [hreal]
    _ = ∑ i ∈ range (hardIndex.1 + 1),
          ((((i + 1 : ℕ) : ℝ) / ((hardIndex.1 + 2 : ℕ) : ℝ)) ^ 2) := by
          have hrewrite :
              ∑ i ∈ range (hardIndex.1 + 1),
                  ((((hardIndex.1 + 1 - i : ℕ) : ℝ) / ((hardIndex.1 + 2 : ℕ) : ℝ)) ^ 2) =
                ∑ i ∈ range (hardIndex.1 + 1),
                  ((((hardIndex.1 - i + 1 : ℕ) : ℝ) / ((hardIndex.1 + 2 : ℕ) : ℝ)) ^ 2) := by
                  refine sum_congr rfl ?_
                  intro i hi
                  have hi_le_k : i ≤ hardIndex.1 := Nat.lt_succ_iff.mp (mem_range.mp hi)
                  have hnat : hardIndex.1 + 1 - i = hardIndex.1 - i + 1 := by omega
                  simp [hnat]
          have hreflect :
              ∑ i ∈ range (hardIndex.1 + 1),
                  ((((hardIndex.1 - i + 1 : ℕ) : ℝ) / ((hardIndex.1 + 2 : ℕ) : ℝ)) ^ 2) =
                ∑ i ∈ range (hardIndex.1 + 1),
                  ((((i + 1 : ℕ) : ℝ) / ((hardIndex.1 + 2 : ℕ) : ℝ)) ^ 2) := by
                  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                    (Finset.sum_range_reflect
                      (fun i ↦ ((((i + 1 : ℕ) : ℝ) / ((hardIndex.1 + 2 : ℕ) : ℝ)) ^ 2))
                      (hardIndex.1 + 1))
          exact hrewrite.trans hreflect
    _ = ∑ i ∈ range (hardIndex.1 + 1),
          (((i + 1 : ℕ) : ℝ) ^ 2) / (((hardIndex.1 + 2 : ℕ) : ℝ) ^ 2) := by
          refine sum_congr rfl ?_
          intro i hi
          rw [div_pow]
    _ = (∑ i ∈ range (hardIndex.1 + 1), (((i + 1 : ℕ) : ℝ) ^ 2)) /
          (((hardIndex.1 + 2 : ℕ) : ℝ) ^ 2) := by
          rw [Finset.sum_div]
    _ = (∑ i ∈ Icc 1 (hardIndex.1 + 1), (i : ℝ) ^ 2) /
          (((hardIndex.1 + 2 : ℕ) : ℝ) ^ 2) := by
          congr 1
          rw [show Icc 1 (hardIndex.1 + 1) = Ico 1 (hardIndex.1 + 2) by
            simpa using (Finset.Ico_succ_right_eq_Icc 1 (hardIndex.1 + 1))]
          rw [Finset.sum_Ico_eq_sum_range]
          refine sum_congr rfl ?_
          intro i hi
          ring_nf

/-- Helper for Theorem 2.8: the squared norm of the hard-instance stationary point is bounded by
`(1 / 3) * (k.1 + 2)`. -/
private theorem quadraticHardInstanceStationaryPoint_sqNorm_le (hardIndex : Fin n) :
    ‖quadraticHardInstanceStationaryPoint hardIndex‖ ^ 2 ≤
      (1 / 3 : ℝ) * (hardIndex.1 + 2) := by
  rw [quadraticHardInstanceStationaryPoint_sqNorm_eq]
  have hsqQ := sum_Icc_sq_le_cubic_third (hardIndex.1 + 1)
  have hsq :
      (∑ i ∈ Icc 1 (hardIndex.1 + 1), (i : ℝ) ^ 2) ≤
        (((hardIndex.1 + 2 : ℕ) : ℝ) ^ 3) / 3 := by
    have hq :
        ((∑ i ∈ Icc 1 (hardIndex.1 + 1), (i : ℚ) ^ 2 : ℚ) : ℝ) ≤
          ((((hardIndex.1 + 2 : ℕ) : ℚ) ^ 3) / 3 : ℚ) := by
      exact_mod_cast hsqQ
    simpa using hq
  have hdiv :
      (∑ i ∈ Icc 1 (hardIndex.1 + 1), (i : ℝ) ^ 2) / (((hardIndex.1 + 2 : ℕ) : ℝ) ^ 2) ≤
        ((((hardIndex.1 + 2 : ℕ) : ℝ) ^ 3) / 3) / (((hardIndex.1 + 2 : ℕ) : ℝ) ^ 2) := by
    exact div_le_div_of_nonneg_right hsq (by positivity)
  refine hdiv.trans_eq ?_
  have hk2 : (((hardIndex.1 + 2 : ℕ) : ℝ) ^ 2) ≠ 0 := by positivity
  field_simp [hk2]
  norm_num


/-- Helper for Theorem 2.8: precomposing a differentiable scalar field with a continuous linear
map pulls back its gradient by the adjoint. -/
private theorem hasGradientAt_comp_continuousLinearMap
    {m : Type*} [NormedAddCommGroup m] [InnerProductSpace ℝ m] [CompleteSpace m]
    {f : m → ℝ} (A : E →L[ℝ] m) {x : E}
    (hf : DifferentiableAt ℝ f (A x)) :
    HasGradientAt (f ∘ A) (A.adjoint (∇ f (A x))) x := by
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

/-- Helper for Theorem 2.8: rewriting `quadraticHardInstanceFamily` through the explicit active
prefix projection exposes the source-faithful lower-bound quadratic route. -/
private theorem quadraticHardInstanceFamily_eq_prefix_smoothLowerBoundFunction
    (L : NNReal) (hardIndex : Fin n) (x : E) :
    quadraticHardInstanceFamily (L : ℝ) hardIndex x =
      smoothLowerBoundFunction (L : ℝ) (Nat.succPNat hardIndex.1)
        (hardInstancePrefixLinear hardIndex x) := by
  -- Both sides restrict `x` to the first `hardIndex.1 + 1` coordinates before applying the same
  -- prefix quadratic.
  have hprefix :
      hardInstancePrefixLinear hardIndex x =
        (EuclideanSpace.equiv (Fin (hardIndex.1 + 1)) ℝ).symm
          (fun i ↦ x (Fin.castLE (Nat.succ_le_of_lt hardIndex.2) i)) := by
    ext i
    simp [hardInstancePrefixLinear]
  simpa [quadraticHardInstanceFamily] using
    congrArg (smoothLowerBoundFunction (L : ℝ) (Nat.succPNat hardIndex.1)) hprefix

/-- Helper for Theorem 2.8: differentiating the explicit prefix-factorization of the hard
instance yields a zero-tail extension of the prefix gradient. -/
private theorem quadraticHardInstanceFamily_gradient_eq_zeroTail_prefixGradient
    (L : NNReal) (hardIndex : Fin n) (y : E) :
    ∇ (quadraticHardInstanceFamily (L : ℝ) hardIndex) y =
      hardInstanceZeroTailLinear hardIndex
        (∇ (smoothLowerBoundFunction (L : ℝ) (Nat.succPNat hardIndex.1))
          (hardInstancePrefixLinear hardIndex y)) := by
  -- Differentiate the owner lower-bound quadratic on the active prefix, then pull it back through
  -- the explicit projection.
  have hdiff :
      DifferentiableAt ℝ (smoothLowerBoundFunction (L : ℝ) (Nat.succPNat hardIndex.1))
        (hardInstancePrefixLinear hardIndex y) := by
    have hcont : ContDiff ℝ 1
        (smoothLowerBoundFunction (L : ℝ) (Nat.succPNat hardIndex.1)) := by
      simpa [smoothLowerBoundFunction] using
        (symmetric_quadratic_contDiff_and_gradient_lipschitz 0
          ((-((L : ℝ) / 4)) •
            EuclideanSpace.single (0 : Fin (Nat.succPNat hardIndex.1)) (1 : ℝ))
          (((L : ℝ) / 4) • pathTridiagonalMatrix (Nat.succPNat hardIndex.1))
          ((pathTridiagonalMatrix_isSymm (Nat.succPNat hardIndex.1)).smul ((L : ℝ) / 4))).1
    exact hcont.differentiable_one _
  have hgrad :=
    hasGradientAt_comp_continuousLinearMap
      (m := EuclideanSpace ℝ (Fin (hardIndex.1 + 1)))
      (A := hardInstancePrefixLinear hardIndex) hdiff
  have hgrad' :
      HasGradientAt (quadraticHardInstanceFamily (L : ℝ) hardIndex)
        (hardInstanceZeroTailLinear hardIndex
          (∇ (smoothLowerBoundFunction (L : ℝ) (Nat.succPNat hardIndex.1))
            (hardInstancePrefixLinear hardIndex y))) y := by
    simpa [quadraticHardInstanceFamily, hardInstanceZeroTailLinear,
      hardInstancePrefix_eq_linear hardIndex] using hgrad
  exact hgrad'.gradient

/-- Helper for Theorem 2.8: every active-prefix coordinate with zero-based index at least `j`
already vanishes for a point in `ℝ^{j,n}`. -/
private theorem hardInstancePrefixLinear_eq_zero_of_mem_coordinateSubspace
    (hardIndex : Fin n) {j : ℕ} {y : E} (hy : y ∈ ℝ^{j,n})
    {i : Fin (hardIndex.1 + 1)} (hi : j ≤ i.1) :
    hardInstancePrefixLinear hardIndex y i = 0 := by
  -- Prefix coordinates are ambient coordinates, so the ambient zero-tail condition applies
  -- directly.
  rw [hardInstancePrefixLinear_apply]
  exact (mem_coordinateSubspace_iff.mp hy) _ hi

/-- Helper for Theorem 2.8: for the hard instance with active prefix `2 * k + 1`, every gradient
coordinate from `j + 1` onward vanishes at points in `ℝ^{j,n}`. -/
private theorem quadraticHardInstanceFamily_gradient_coordinate_eq_zero_of_mem_coordinateSubspace
    (L : NNReal) {k j : ℕ} (hk₁ : 1 ≤ k) (hk₂ : k ≤ (n - 1) / 2) (_hj : j ≤ k)
    {y : E} (hy : y ∈ ℝ^{j,n}) {i : Fin n} (hi : j + 1 ≤ i.1) :
    (∇ (quadraticHardInstanceFamily (L : ℝ)
      ⟨2 * k, two_mul_lt_of_one_le_of_le_half_sub hk₁ hk₂⟩) y) i = 0 := by
  let hardIndex : Fin n := ⟨2 * k, two_mul_lt_of_one_le_of_le_half_sub hk₁ hk₂⟩
  let prefixPoint := hardInstancePrefixLinear hardIndex y
  rw [quadraticHardInstanceFamily_gradient_eq_zeroTail_prefixGradient L hardIndex y]
  by_cases htail : i ≤ hardIndex
  · let prefixIndex : Fin (hardIndex.1 + 1) :=
      ⟨i.1, Nat.lt_succ_of_le (Fin.le_iff_val_le_val.mp htail)⟩
    -- Inside the active prefix, the explicit tridiagonal gradient formula only touches
    -- coordinates that already vanish by the prefix support hypothesis.
    have hprefix_zero :
        (∇ (smoothLowerBoundFunction (L : ℝ) (Nat.succPNat hardIndex.1))
            prefixPoint) prefixIndex = 0 := by
      change
        (∇ (smoothLowerBoundFunction (L : ℝ) (Nat.succPNat hardIndex.1))
          prefixPoint).ofLp prefixIndex = 0
      have hprefix_ne_zero : prefixIndex ≠ 0 := by
        intro hzero
        have : prefixIndex.1 = 0 := by
          simpa using congrArg Fin.val hzero
        exact Nat.not_succ_le_zero j (this ▸ hi)
      -- Read the prefix gradient formula at the active coordinate `prefixIndex`.
      have hgrad :=
        smoothLowerBoundFunction_gradient_eq_scaled_residual_apply
          (L : ℝ) hardIndex.1 prefixPoint prefixIndex
      have hvanish :
          ∀ t : Fin (hardIndex.1 + 1), j ≤ t.1 → prefixPoint t = 0 := by
        intro t ht
        simpa [prefixPoint] using
          hardInstancePrefixLinear_eq_zero_of_mem_coordinateSubspace hardIndex hy ht
      have hsum :
          ((pathTridiagonalMatrix (Nat.succPNat hardIndex.1)).mulVec prefixPoint) prefixIndex = 0 := by
        -- The tridiagonal stencil only touches coordinates that are already zero.
        exact pathTridiagonal_mulVec_eq_zero_of_vanishing_from
          hardIndex.1 j prefixPoint hvanish hi
      have hsingle : EuclideanSpace.single 0 (1 : ℝ) prefixIndex = 0 := by
        simp [EuclideanSpace.single, hprefix_ne_zero]
      calc
        (∇ (smoothLowerBoundFunction (L : ℝ) (Nat.succPNat hardIndex.1))
            prefixPoint).ofLp prefixIndex
          = ((L : ℝ) / 4) *
              (((pathTridiagonalMatrix (Nat.succPNat hardIndex.1)).mulVec prefixPoint.ofLp)
                prefixIndex -
                (EuclideanSpace.single 0 (1 : ℝ)).ofLp prefixIndex) := by
                  simpa using hgrad
        _ = (L / 4) * (0 - 0) := by rw [hsum, hsingle]
        _ = 0 := by ring
    have hprefix_zero' :
        (∇ (smoothLowerBoundFunction (L : ℝ) (Nat.succPNat hardIndex.1))
            (hardInstancePrefixLinear hardIndex y)) ⟨i.1,
              Nat.lt_succ_of_le (Fin.le_iff_val_le_val.mp htail)⟩ = 0 := by
      simpa [prefixPoint, prefixIndex] using hprefix_zero
    simpa [hardInstanceZeroTailLinear_apply, htail] using hprefix_zero'
  · -- Outside the active prefix, the pulled-back gradient is zero by construction.
    simp [hardInstanceZeroTailLinear_apply, htail]

/-- Helper for Theorem 2.8: the canonical hard-instance stationary point is stationary for the
ambient hard-instance objective. -/
private theorem quadraticHardInstanceStationaryPoint_hasGradientAt_zero
    (L : NNReal) (hardIndex : Fin n) :
    HasGradientAt (quadraticHardInstanceFamily (L : ℝ) hardIndex) 0
      (quadraticHardInstanceStationaryPoint hardIndex) := by
  have hf : quadraticHardInstanceFamily (L : ℝ) hardIndex ∈ (𝓕[L, p]¹¹ : Set (E → ℝ)) :=
    quadraticHardInstanceFamily_mem_smooth_convex_objective L hardIndex
  rw [mem_F11_iff] at hf
  refine (hasGradientAt_zero_iff_gradient_eq_zero
    (hf.contDiff.differentiable_one _)).2 ?_
  have hprefix_zero :
      ∇ (smoothLowerBoundFunction (L : ℝ) (Nat.succPNat hardIndex.1))
        (smoothLowerBoundFunctionStationaryPoint (Nat.succPNat hardIndex.1)) = 0 :=
    (smoothLowerBoundFunctionStationaryPoint_hasGradientAt_zero (L : ℝ) hardIndex.1).gradient
  rw [quadraticHardInstanceFamily_gradient_eq_zeroTail_prefixGradient L hardIndex]
  rw [hardInstancePrefixLinear_stationaryPoint hardIndex]
  have hzero := congrArg (hardInstanceZeroTailLinear hardIndex) hprefix_zero
  simpa using hzero.trans (LinearMap.map_zero _)

/-- Helper for Theorem 2.8: the canonical hard-instance stationary point globally minimizes the
ambient hard-instance objective. -/
private theorem quadraticHardInstanceStationaryPoint_isMinOn
    (L : NNReal) (hardIndex : Fin n) :
    IsMinOn (quadraticHardInstanceFamily (L : ℝ) hardIndex) Set.univ
      (quadraticHardInstanceStationaryPoint hardIndex) := by
  have hf := quadraticHardInstanceFamily_mem_smooth_convex_objective L hardIndex
  have hstat :
      HasGradientAt (quadraticHardInstanceFamily (L : ℝ) hardIndex) 0
        (quadraticHardInstanceStationaryPoint hardIndex) :=
    quadraticHardInstanceStationaryPoint_hasGradientAt_zero L hardIndex
  refine (hf.convexOn.isMinOn_iff_variational_inequality_of_hasGradientAt (by simp) hstat).2 ?_
  intro x hx
  simp

/-- Helper for Theorem 2.8: translating the hard-instance stationary point by `x₀` yields a
global minimizer of the translated quadratic hard instance. -/
private theorem quadraticHardInstanceFamily_translate_isMinOn
    (L : NNReal) (hardIndex : Fin n) (x0 : E) :
    IsMinOn (fun x ↦ quadraticHardInstanceFamily (L : ℝ) hardIndex (x - x0)) Set.univ
      (x0 + quadraticHardInstanceStationaryPoint hardIndex) := by
  rw [isMinOn_univ_iff]
  intro x
  have hmin : IsMinOn (quadraticHardInstanceFamily (L : ℝ) hardIndex) Set.univ
      (quadraticHardInstanceStationaryPoint hardIndex) :=
    quadraticHardInstanceStationaryPoint_isMinOn L hardIndex
  rw [isMinOn_univ_iff] at hmin
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmin (x - x0)

/-- Helper for Theorem 2.8: the large active prefix `2 * k + 1` restricts to the smaller
stage-`k` prefix by filling coordinates `k, ..., 2 * k` with `0`. -/
private def stageZeroTailEmbedding {k : ℕ} :
    EuclideanSpace ℝ (Fin ((k - 1) + 1)) →
      EuclideanSpace ℝ (Fin (2 * k + 1)) :=
  fun x ↦
    (EuclideanSpace.equiv (Fin (2 * k + 1)) ℝ).symm
      (fun i ↦ if h : i.1 < (k - 1) + 1 then x ⟨i.1, h⟩ else 0)

/-- Helper for Theorem 2.8: at stage `k + 1`, the zero-tail embedding keeps the first `k + 1`
coordinates and sets all later coordinates to `0`. -/
@[simp] private theorem stageZeroTailEmbedding_apply
    (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 1))) (i : Fin (2 * (k + 1) + 1)) :
    stageZeroTailEmbedding (k := k + 1) x i =
      if h : i.1 < k + 1 then x ⟨i.1, h⟩ else 0 := by
  simp [stageZeroTailEmbedding]

/-- Helper for Theorem 2.8: on `ℝ^{k,n}`, the large hard-instance prefix is exactly the zero-tail
extension of the stage-`k` prefix. -/
private theorem hardInstancePrefixLinear_eq_stageZeroTailEmbedding
    {k : ℕ} (hk₁ : 1 ≤ k) (hk₂ : k ≤ (n - 1) / 2)
    {y : E} (hy : y ∈ ℝ^{k,n}) :
    let bigIndex : Fin n := ⟨2 * k, two_mul_lt_of_one_le_of_le_half_sub hk₁ hk₂⟩
    let smallIndex : Fin n := ⟨k - 1, by omega⟩
    hardInstancePrefixLinear bigIndex y =
      stageZeroTailEmbedding (hardInstancePrefixLinear smallIndex y) := by
  dsimp [stageZeroTailEmbedding]
  ext i
  by_cases hi : i.1 < (k - 1) + 1
  · -- On the first `k` coordinates, both prefixes read the same ambient coordinate.
    have hi_lt_n : i.1 < n := by
      have htwok : 2 * k < n := two_mul_lt_of_one_le_of_le_half_sub hk₁ hk₂
      omega
    have hcast :
        (Fin.castLE
            (by
              have htwok : 2 * k < n := two_mul_lt_of_one_le_of_le_half_sub hk₁ hk₂
              exact htwok)
            i : Fin n) =
          ⟨i.1, hi_lt_n⟩ := by
      ext
      rfl
    simp [hardInstancePrefixLinear_apply, hi, hcast]
  · -- From coordinate `k` onward, membership in `ℝ^{k,n}` forces the large prefix to vanish.
    have hki : k ≤ i.1 := by omega
    have hi_lt_n : i.1 < n := by
      have htwok : 2 * k < n := two_mul_lt_of_one_le_of_le_half_sub hk₁ hk₂
      omega
    have hyi : y ⟨i.1, hi_lt_n⟩ = 0 :=
      (mem_coordinateSubspace_iff.mp hy) _ hki
    have hcast :
        (Fin.castLE
            (by
              have htwok : 2 * k < n := two_mul_lt_of_one_le_of_le_half_sub hk₁ hk₂
              exact htwok)
            i : Fin n) =
          ⟨i.1, hi_lt_n⟩ := by
      ext
      rfl
    simp [hardInstancePrefixLinear_apply, hi, hyi, hcast]

/-- Helper for Theorem 2.8: the preserved stage prefix embeds into the larger long-stage index
set. -/
private theorem stageZeroTailEmbedding_prefix_le (k : ℕ) :
    k + 1 ≤ Nat.succPNat (2 * (k + 1)) := by
  calc
    k + 1 ≤ (k + 1) + (k + 1) := Nat.le_add_right (k + 1) (k + 1)
    _ ≤ (k + 1) + (k + 1) + 1 := Nat.le_succ _
    _ = Nat.succPNat (2 * (k + 1)) := by
          simp [two_mul, Nat.add_left_comm, Nat.add_comm]

/-- Helper for Theorem 2.8: each preserved prefix index is a valid index in the larger stage. -/
private theorem stageZeroTailEmbedding_prefix_lt
    (k : ℕ) (i : Fin (k + 1)) :
    i.1 < Nat.succPNat (2 * (k + 1)) := by
  exact lt_of_lt_of_le i.2 (stageZeroTailEmbedding_prefix_le k)

/-- Helper for Theorem 2.8: the zero-tail embedding preserves every coordinate in the active
prefix. -/
private theorem stageZeroTailEmbedding_apply_prefix
    (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 1))) (i : Fin (k + 1)) :
    stageZeroTailEmbedding (k := k + 1) x ⟨i.1, stageZeroTailEmbedding_prefix_lt k i⟩ = x i := by
  rw [stageZeroTailEmbedding_apply]
  simp [i.2]

/-- Helper for Theorem 2.8: every coordinate in the tail block of the zero-tail embedding
vanishes. -/
private theorem stageZeroTailEmbedding_apply_zero_tail
    (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 1)))
    (i : Fin (2 * (k + 1) + 1)) (hi : k + 1 ≤ i.1) :
    stageZeroTailEmbedding (k := k + 1) x i = 0 := by
  rw [stageZeroTailEmbedding_apply]
  have hnot : ¬ i.1 < k + 1 := Nat.not_lt.mpr hi
  simp [hnot]

/-- Helper for Theorem 2.8: at stage `k + 2`, the head tridiagonal row is unchanged by the
zero-tail embedding. -/
private theorem stageZeroTailEmbedding_mulVec_head_succ
    (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 2))) :
    (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (2 * (k + 2))))
      (stageZeroTailEmbedding (k := k + 2) x)) 0 =
        (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (k + 1))) x) 0 := by
  have h1 : 1 < k + 2 := by omega
  let oneIdx : Fin (k + 2) := ⟨1, h1⟩
  have hzero :
      stageZeroTailEmbedding (k := k + 2) x 0 = x 0 := by
    simpa using stageZeroTailEmbedding_apply_prefix (k := k + 1) x 0
  have hone :
      stageZeroTailEmbedding (k := k + 2) x ⟨oneIdx.1, stageZeroTailEmbedding_prefix_lt (k + 1) oneIdx⟩ =
        x oneIdx := by
    simpa [oneIdx] using stageZeroTailEmbedding_apply_prefix (k := k + 1) x oneIdx
  -- Expand the two head rows and read off the first two preserved coordinates.
  calc
    (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (2 * (k + 2))))
        (stageZeroTailEmbedding (k := k + 2) x)) 0
      = 2 * stageZeroTailEmbedding (k := k + 2) x 0 -
          stageZeroTailEmbedding (k := k + 2) x ⟨1, by omega⟩ := by
            simpa [two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              (pathTridiagonal_mulVec_apply_head (2 * k + 3)
                (stageZeroTailEmbedding (k := k + 2) x))
    _ = 2 * x 0 - x oneIdx := by
          rw [hzero, hone]
    _ = (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (k + 1))) x) 0 := by
          symm
          simpa [oneIdx] using pathTridiagonal_mulVec_apply_head k x

/-- Helper for Theorem 2.8: at stage `k + 2`, every preserved interior tridiagonal row is
unchanged by the zero-tail embedding. -/
private theorem stageZeroTailEmbedding_mulVec_middle_succ
    (k t : ℕ) (ht : t < k) (x : EuclideanSpace ℝ (Fin (k + 2)))
    (ht1 : t + 1 < k + 2) (ht1Long : t + 1 < Nat.succPNat (2 * (k + 2))) :
    (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (2 * (k + 2))))
      (stageZeroTailEmbedding (k := k + 2) x)) ⟨t + 1, ht1Long⟩ =
        (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (k + 1))) x) ⟨t + 1, ht1⟩ := by
  have ht0 : t < k + 2 := by omega
  have ht2 : t + 2 < k + 2 := by omega
  let iPrev : Fin (k + 2) := ⟨t, ht0⟩
  let iMid : Fin (k + 2) := ⟨t + 1, ht1⟩
  let iNext : Fin (k + 2) := ⟨t + 2, ht2⟩
  let jPrev : Fin (2 * (k + 2) + 1) := ⟨iPrev.1, stageZeroTailEmbedding_prefix_lt (k + 1) iPrev⟩
  let jMid : Fin (2 * (k + 2) + 1) := ⟨iMid.1, stageZeroTailEmbedding_prefix_lt (k + 1) iMid⟩
  let jNext : Fin (2 * (k + 2) + 1) := ⟨iNext.1, stageZeroTailEmbedding_prefix_lt (k + 1) iNext⟩
  -- Expand the matching interior rows; all three neighboring coordinates stay inside the prefix.
  have hlong :=
    pathTridiagonal_mulVec_apply_middle
      (k := 2 * k + 3) (y := stageZeroTailEmbedding (k := k + 2) x)
      (t := t) (by omega) (by omega) (by omega) (by omega)
  have hshort :=
    pathTridiagonal_mulVec_apply_middle
      (k := k) (y := x) (t := t) ht (by omega) (by omega) (by omega)
  calc
    (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (2 * (k + 2))))
        (stageZeroTailEmbedding (k := k + 2) x)) ⟨t + 1, ht1Long⟩
      = 2 * stageZeroTailEmbedding (k := k + 2) x jMid -
          stageZeroTailEmbedding (k := k + 2) x jPrev -
          stageZeroTailEmbedding (k := k + 2) x jNext := by
            simpa [jPrev, jMid, jNext, iPrev, iMid, iNext, two_mul,
              Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlong
    _ = 2 * x iMid - x iPrev - x iNext := by
          have hprev :
              stageZeroTailEmbedding (k := k + 2) x jPrev =
                x iPrev := by
            simpa [jPrev, iPrev] using stageZeroTailEmbedding_apply_prefix (k := k + 1) x iPrev
          have hmid :
              stageZeroTailEmbedding (k := k + 2) x jMid =
                x iMid := by
            simpa [jMid, iMid] using stageZeroTailEmbedding_apply_prefix (k := k + 1) x iMid
          have hnext :
              stageZeroTailEmbedding (k := k + 2) x jNext =
                x iNext := by
            simpa [jNext, iNext] using stageZeroTailEmbedding_apply_prefix (k := k + 1) x iNext
          rw [hmid, hprev, hnext]
    _ = (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (k + 1))) x) ⟨t + 1, ht1⟩ := by
          symm
          simpa [two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hshort

/-- Helper for Theorem 2.8: at stage `k + 2`, the short last tridiagonal row matches the
corresponding long interior row because the forward long neighbor lies in the zero tail. -/
private theorem stageZeroTailEmbedding_mulVec_last_succ
    (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 2)))
    (hk1Long : k + 1 < Nat.succPNat (2 * (k + 2))) :
    (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (2 * (k + 2))))
      (stageZeroTailEmbedding (k := k + 2) x)) ⟨k + 1, hk1Long⟩ =
        (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (k + 1))) x) (Fin.last (k + 1)) := by
  have hk0 : k < k + 2 := by omega
  let iPrev : Fin (k + 2) := ⟨k, hk0⟩
  let iLast : Fin (k + 2) := Fin.last (k + 1)
  let jPrev : Fin (2 * (k + 2) + 1) := ⟨iPrev.1, stageZeroTailEmbedding_prefix_lt (k + 1) iPrev⟩
  let jLast : Fin (2 * (k + 2) + 1) := ⟨iLast.1, stageZeroTailEmbedding_prefix_lt (k + 1) iLast⟩
  have hjTail : k + 2 < 2 * (k + 2) + 1 := by omega
  let jTail : Fin (2 * (k + 2) + 1) := ⟨k + 2, hjTail⟩
  -- Compare the short tail row with the long interior row and kill the forward tail coordinate.
  have hlong :=
    pathTridiagonal_mulVec_apply_middle
      (k := 2 * k + 3) (y := stageZeroTailEmbedding (k := k + 2) x)
      (t := k) (by omega) (by omega) (by omega) (by omega)
  have hshort := pathTridiagonal_mulVec_apply_tail k x
  calc
    (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (2 * (k + 2))))
        (stageZeroTailEmbedding (k := k + 2) x)) ⟨k + 1, hk1Long⟩
      = 2 * stageZeroTailEmbedding (k := k + 2) x jLast -
          stageZeroTailEmbedding (k := k + 2) x jPrev -
          stageZeroTailEmbedding (k := k + 2) x jTail := by
            simpa [jPrev, jLast, jTail, iPrev, iLast, two_mul,
              Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlong
    _ = 2 * x (Fin.last (k + 1)) - x iPrev := by
          have hlast :
              stageZeroTailEmbedding (k := k + 2) x jLast =
                x iLast := by
            simpa [jLast, iLast, Fin.val_last] using
              stageZeroTailEmbedding_apply_prefix (k := k + 1) x iLast
          have hprev :
              stageZeroTailEmbedding (k := k + 2) x jPrev =
                x iPrev := by
            simpa [jPrev, iPrev] using stageZeroTailEmbedding_apply_prefix (k := k + 1) x iPrev
          have htail :
              stageZeroTailEmbedding (k := k + 2) x jTail = 0 := by
            simpa [jTail] using stageZeroTailEmbedding_apply_zero_tail (k := k + 1) x jTail (by omega)
          rw [hlast, hprev, htail]
          simp [iLast]
    _ = (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (k + 1))) x) (Fin.last (k + 1)) := by
          symm
          simpa [iPrev] using hshort

/-- Helper for Theorem 2.8: on the preserved prefix rows, the long tridiagonal operator acting on
the zero-tail embedding agrees with the short tridiagonal operator. -/
private theorem stageZeroTailEmbedding_mulVec_prefix_eq
    (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 1))) (i : Fin (k + 1)) :
    (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (2 * (k + 1))))
      (stageZeroTailEmbedding (k := k + 1) x)) ⟨i.1, stageZeroTailEmbedding_prefix_lt k i⟩ =
        (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k)) x) i := by
  -- Route correction: prove the preserved-prefix comparison row-by-row instead of forcing one
  -- cast-heavy `mulVec` identity.
  cases k with
  | zero =>
    fin_cases i
    -- In the one-dimensional short stage, both sides are the scalar `2 * x 0`.
    simp [Matrix.mulVec, dotProduct, pathTridiagonalMatrix_apply, stageZeroTailEmbedding_apply]
  | succ k =>
    by_cases hi0 : i = 0
    · subst hi0
      -- The head row is exactly the scalar comparison from the dedicated head lemma.
      simpa using stageZeroTailEmbedding_mulVec_head_succ k x
    · by_cases hilast : i = Fin.last (k + 1)
      · subst hilast
        -- The short last row matches the long interior row at value `k + 1`.
        have hk1Long : k + 1 < Nat.succPNat (2 * (k + 2)) :=
          stageZeroTailEmbedding_prefix_lt (k + 1) (Fin.last (k + 1))
        simpa [Fin.val_last] using stageZeroTailEmbedding_mulVec_last_succ k x hk1Long
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
        have ht1 : t + 1 < k + 2 := by
          dsimp [t]
          omega
        have hi_eq : i = ⟨t + 1, ht1⟩ := by
          ext
          dsimp [t]
          rw [Nat.sub_add_cancel hi_pos']
        -- Every remaining preserved row is an interior row.
        rw [hi_eq]
        let iMid : Fin (k + 2) := ⟨t + 1, ht1⟩
        have ht1Long : t + 1 < Nat.succPNat (2 * (k + 2)) :=
          stageZeroTailEmbedding_prefix_lt (k + 1) iMid
        simpa [iMid] using stageZeroTailEmbedding_mulVec_middle_succ k t ht x ht1 ht1Long

/-- Helper for Theorem 2.8: the long tridiagonal quadratic form collapses to the short one on a
zero-tail stage embedding. -/
private theorem stageZeroTailEmbedding_quadratic_form_collapse
    (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 1))) :
    dotProduct (stageZeroTailEmbedding (k := k + 1) x)
      (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (2 * (k + 1))))
        (stageZeroTailEmbedding (k := k + 1) x)) =
      dotProduct x (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k)) x) := by
  let y := stageZeroTailEmbedding (k := k + 1) x
  let z := Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (2 * (k + 1)))) y
  let g : ℕ → ℝ := fun i ↦ if hi : i < 2 * (k + 1) + 1 then y ⟨i, hi⟩ * z ⟨i, hi⟩ else 0
  let h : ℕ → ℝ := fun i ↦
    if hi : i < k + 1 then
      x ⟨i, hi⟩ * ((Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k)) x) ⟨i, hi⟩)
    else
      0
  have hlong :
      dotProduct y z = ∑ i ∈ range (2 * (k + 1) + 1), g i := by
    calc
      dotProduct y z = ∑ i : Fin (2 * (k + 1) + 1), g i.1 := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hi_le : i.1 ≤ 2 * (k + 1) := Nat.le_of_lt_succ i.2
        simpa [g, hi_le]
      _ = ∑ i ∈ range (2 * (k + 1) + 1), g i := Fin.sum_univ_eq_sum_range g _
  have hshort :
      dotProduct x (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k)) x) =
        ∑ i ∈ range (k + 1), h i := by
    calc
      dotProduct x (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k)) x) =
          ∑ i : Fin (k + 1), h i.1 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi_le : i.1 ≤ k := Nat.le_of_lt_succ i.2
            simpa [h, hi_le]
      _ = ∑ i ∈ range (k + 1), h i := Fin.sum_univ_eq_sum_range h _
  have hprefix :
      ∑ i ∈ range (k + 1), g i = ∑ i ∈ range (k + 1), h i := by
    refine sum_congr rfl ?_
    intro i hi
    have hi_lt : i < k + 1 := mem_range.mp hi
    have hi_le : i ≤ k := Nat.le_of_lt_succ hi_lt
    have hiLong : i < 2 * (k + 1) + 1 := by omega
    have hiLong_le : i ≤ 2 * (k + 1) := Nat.le_of_lt_succ hiLong
    let iShort : Fin (k + 1) := ⟨i, hi_lt⟩
    let iLong : Fin (2 * (k + 1) + 1) := ⟨i, hiLong⟩
    have hyi : y iLong = x iShort := by
      simpa [y, iLong, iShort] using stageZeroTailEmbedding_apply_prefix (k := k) x iShort
    have hzi :
        z iLong =
          (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k)) x) iShort := by
      simpa [y, z, iLong, iShort] using stageZeroTailEmbedding_mulVec_prefix_eq k x iShort
    simpa [g, h, hiLong_le, hi_le, iLong, iShort, hyi, hzi]
  have htail :
      ∑ i ∈ Ico (k + 1) (2 * (k + 1) + 1), g i = 0 := by
    refine sum_eq_zero ?_
    intro i hi
    have hi_ge : k + 1 ≤ i := (mem_Ico.mp hi).1
    have hi_lt : i < 2 * (k + 1) + 1 := (mem_Ico.mp hi).2
    have hi_le : i ≤ 2 * (k + 1) := Nat.le_of_lt_succ hi_lt
    let iLong : Fin (2 * (k + 1) + 1) := ⟨i, hi_lt⟩
    have hyzero : y iLong = 0 := by
      simpa [y, iLong] using stageZeroTailEmbedding_apply_zero_tail (k := k) x iLong hi_ge
    simpa [g, hi_le, iLong, hyzero]
  -- Split the long dot product into the preserved prefix and the zero tail block.
  calc
    dotProduct y z = ∑ i ∈ range (2 * (k + 1) + 1), g i := hlong
    _ = ∑ i ∈ range (k + 1), g i + ∑ i ∈ Ico (k + 1) (2 * (k + 1) + 1), g i := by
          symm
          exact Finset.sum_range_add_sum_Ico g (by omega)
    _ = ∑ i ∈ range (k + 1), h i := by rw [hprefix, htail, add_zero]
    _ = dotProduct x (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k)) x) := by
          exact hshort.symm

/-- Helper for Theorem 2.8: the lower-bound quadratic on the long prefix agrees with the
stage-`k` quadratic on vectors whose tail coordinates `k, ..., 2 * k` are zero. -/
private theorem smoothLowerBoundFunction_eq_stage_of_zeroTail
    (L : NNReal) {k : ℕ} (hk₁ : 1 ≤ k)
    (x : EuclideanSpace ℝ (Fin ((k - 1) + 1))) :
    smoothLowerBoundFunction (L : ℝ) (Nat.succPNat (2 * k)) (stageZeroTailEmbedding x) =
      smoothLowerBoundFunction (L : ℝ) (Nat.succPNat (k - 1)) x := by
  cases k with
  | zero =>
    omega
  | succ k =>
  -- Rewrite both objectives into their quadratic-plus-linear normal forms.
    rw [smoothLowerBoundFunction_apply, smoothLowerBoundFunction_apply]
    have hhead : stageZeroTailEmbedding (k := k + 1) x 0 = x 0 := by
      simpa using (stageZeroTailEmbedding_apply k x 0)
    have hquad :
        dotProduct (stageZeroTailEmbedding (k := k + 1) x)
          (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (2 * (k + 1))))
            (stageZeroTailEmbedding (k := k + 1) x)) =
          dotProduct x (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat k)) x) := by
      simpa using stageZeroTailEmbedding_quadratic_form_collapse k x
    have hkpred : k + 1 - 1 = k := Nat.succ_sub_one k
    have hquad' :
        dotProduct (stageZeroTailEmbedding (k := k + 1) x)
          (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (2 * (k + 1))))
            (stageZeroTailEmbedding (k := k + 1) x)) =
          dotProduct x (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (k + 1 - 1))) x) := by
      simpa [hkpred] using hquad
    have hhead' :
        (L : ℝ) / 4 * stageZeroTailEmbedding (k := k + 1) x 0 =
          (L : ℝ) / 4 * x 0 := by
      exact congrArg (fun t ↦ (L : ℝ) / 4 * t) hhead
  -- Substitute the preserved head coordinate and the collapsed quadratic form.
    calc
      (L : ℝ) / 8 *
            dotProduct (stageZeroTailEmbedding (k := k + 1) x)
              (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (2 * (k + 1))))
                (stageZeroTailEmbedding (k := k + 1) x)) -
          (L : ℝ) / 4 * stageZeroTailEmbedding (k := k + 1) x 0
        = (L : ℝ) / 8 *
            dotProduct (stageZeroTailEmbedding (k := k + 1) x)
              (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (2 * (k + 1))))
                (stageZeroTailEmbedding (k := k + 1) x)) -
          (L : ℝ) / 4 * x 0 := by
              rw [hhead']
      _ = (L : ℝ) / 8 *
            dotProduct x (Matrix.mulVec (pathTridiagonalMatrix (Nat.succPNat (k + 1 - 1))) x) -
          (L : ℝ) / 4 * x 0 := by
              exact congrArg (fun t ↦ (L : ℝ) / 8 * t - (L : ℝ) / 4 * x 0) hquad'

/-- Helper for Theorem 2.8: on the coordinate subspace `ℝ^{k,n}`, the terminal hard instance with
index `2 * k` agrees exactly with the smaller stage hard instance of index `k - 1`. -/
private theorem quadraticHardInstanceFamily_eq_stage_on_coordinateSubspace
    (L : NNReal) {k : ℕ} (hk₁ : 1 ≤ k) (hk₂ : k ≤ (n - 1) / 2)
    {y : E} (hy : y ∈ ℝ^{k,n}) :
    let bigIndex : Fin n := ⟨2 * k, two_mul_lt_of_one_le_of_le_half_sub hk₁ hk₂⟩
    let smallIndex : Fin n := ⟨k - 1, by omega⟩
    quadraticHardInstanceFamily (L : ℝ) bigIndex y =
      quadraticHardInstanceFamily (L : ℝ) smallIndex y := by
  dsimp
  let bigIndex : Fin n := ⟨2 * k, two_mul_lt_of_one_le_of_le_half_sub hk₁ hk₂⟩
  let smallIndex : Fin n := ⟨k - 1, by omega⟩
  -- Route correction: compare the two objectives only after rewriting both through explicit
  -- prefix maps; the long-prefix vector is the zero-tail extension of the short-prefix one.
  rw [quadraticHardInstanceFamily_eq_prefix_smoothLowerBoundFunction,
    quadraticHardInstanceFamily_eq_prefix_smoothLowerBoundFunction]
  rw [hardInstancePrefixLinear_eq_stageZeroTailEmbedding hk₁ hk₂ hy]
  exact smoothLowerBoundFunction_eq_stage_of_zeroTail L hk₁ _

/-- Helper for Theorem 2.8: for the hard instance with active prefix `2 * k + 1`, the gradient at
a point supported on the first `j` coordinates is supported on the first `j + 1` coordinates. -/
-- Proof sketch: rewrite membership in `ℝ^{j+1,n}` coordinatewise. For coordinates past the active
-- prefix the gradient vanishes because the hard instance ignores that tail, while inside the
-- active prefix the tridiagonal gradient formula only uses neighboring coordinates, all of which
-- are already zero once the index is at least `j + 1`.
private theorem quadraticHardInstanceFamily_gradient_mem_succ_coordinateSubspace
    (L : NNReal) {k j : ℕ} (hk₁ : 1 ≤ k) (hk₂ : k ≤ (n - 1) / 2) (hj : j ≤ k)
    {y : E} (hy : y ∈ ℝ^{j,n}) :
    ∇ (quadraticHardInstanceFamily (L : ℝ)
      ⟨2 * k, two_mul_lt_of_one_le_of_le_half_sub hk₁ hk₂⟩) y ∈ ℝ^{j + 1,n} := by
  -- Rewrite the target support condition coordinatewise and apply the explicit vanishing lemma to
  -- each tail coordinate.
  rw [mem_coordinateSubspace_iff]
  intro i hi
  exact quadraticHardInstanceFamily_gradient_coordinate_eq_zero_of_mem_coordinateSubspace
    L hk₁ hk₂ hj hy hi

/-- Helper for Theorem 2.8: the translated hard-instance gradient has the same coordinate support
propagation as the untranslated hard instance after shifting by `x₀`. -/
-- Proof sketch: first rewrite the translated gradient as the untranslated gradient at `x - x₀`,
-- then apply the support-propagation lemma for the owner hard instance.
private theorem translated_quadraticHardInstanceFamily_gradient_mem_succ_coordinateSubspace
    (L : NNReal) {k j : ℕ} (hk₁ : 1 ≤ k) (hk₂ : k ≤ (n - 1) / 2) (x0 : E) (hj : j ≤ k)
    {x : E} (hx : x - x0 ∈ ℝ^{j,n}) :
    ∇ (fun y ↦ quadraticHardInstanceFamily (L : ℝ)
      ⟨2 * k, two_mul_lt_of_one_le_of_le_half_sub hk₁ hk₂⟩
        (y - x0)) x ∈ ℝ^{j + 1,n} := by
  rw [quadraticHardInstanceFamily_translate_gradient_eq
    L ⟨2 * k, two_mul_lt_of_one_le_of_le_half_sub hk₁ hk₂⟩ x0 x]
  exact quadraticHardInstanceFamily_gradient_mem_succ_coordinateSubspace L hk₁ hk₂ hj hx

/-- Helper for Theorem 2.8: every iterate difference of a span-condition method applied to the
translated hard instance stays inside the corresponding prefix coordinate subspace. -/
-- Proof sketch: prove by induction on the iterate index. The span condition writes the next
-- iterate difference as a linear combination of earlier gradients, and the translated
-- gradient-support lemma ensures each of those gradients lies in the next prefix subspace.
private theorem span_condition_iterate_sub_mem_coordinateSubspace
    (L : NNReal) {k : ℕ} (hk₁ : 1 ≤ k) (hk₂ : k ≤ (n - 1) / 2) (x0 : E)
    (method : (E → ℝ) → E → ℕ → E) (hmethod : SatisfiesSpanCondition method) :
    ∀ {j : ℕ},
      j ≤ k →
        method
            (fun x ↦ quadraticHardInstanceFamily (L : ℝ)
              ⟨2 * k, two_mul_lt_of_one_le_of_le_half_sub hk₁ hk₂⟩ (x - x0))
            x0 j -
          x0 ∈ ℝ^{j,n} := by
  let hardIndex : Fin n := ⟨2 * k, two_mul_lt_of_one_le_of_le_half_sub hk₁ hk₂⟩
  let f : E → ℝ := fun x ↦ quadraticHardInstanceFamily (L : ℝ) hardIndex (x - x0)
  have hf_mem : f ∈ (𝓕[L, p]¹¹ : Set (E → ℝ)) :=
    quadraticHardInstanceFamily_translate_mem_smooth_convex_objective L hardIndex x0
  rw [mem_F11_iff] at hf_mem
  -- Build the source-faithful prefix-support invariant by strong induction on the iterate index.
  intro j hjk
  induction j using Nat.strong_induction_on with
  | h j ih =>
      cases j with
      | zero =>
          -- The zeroth iterate is exactly `x₀`, so the iterate difference is the zero vector.
          have hzero : method f x0 0 = x0 :=
            SatisfiesSpanCondition.zero_eq hmethod f hf_mem.contDiff x0
          rw [hzero, sub_self]
          exact Submodule.zero_mem _
      | succ j =>
          -- The span condition writes the next iterate difference in the span of earlier
          -- gradients.
          have hspan :
              method f x0 (j + 1) - x0 ∈
                Submodule.span ℝ (Set.range fun i : Fin (j + 1) ↦ ∇ f (method f x0 i)) :=
            SatisfiesSpanCondition.sub_mem_span hmethod f hf_mem.contDiff x0 (j + 1)
          have hspan_le :
              Submodule.span ℝ (Set.range fun i : Fin (j + 1) ↦ ∇ f (method f x0 i)) ≤
                ℝ^{j + 1,n} := by
            refine prefix_span_le_coordinateSubspace (k := j + 1)
              (g := fun i ↦ ∇ f (method f x0 i)) ?_
            intro i
            -- Each earlier iterate is already supported on its own prefix, so its gradient only
            -- opens one new coordinate.
            have hik : i.1 ≤ k := le_trans (Nat.le_of_lt i.2) hjk
            have hiter :
                method f x0 i.1 - x0 ∈ ℝ^{i.1,n} :=
              ih i.1 i.2 hik
            simpa [f] using
              translated_quadraticHardInstanceFamily_gradient_mem_succ_coordinateSubspace
                L hk₁ hk₂ x0 hik hiter
          exact hspan_le hspan

/-- Helper for Theorem 2.8: on the prefix coordinate subspace `ℝ^{k,n}`, the terminal hard
instance with index `2 * k` stays at least `L / (16 (k + 1))` above its global minimum. -/
-- Proof sketch: on `ℝ^{k,n}` the big hard instance agrees with the stage-`k` hard instance
-- because all coordinates from `k` onward vanish. The stage stationary point minimizes that
-- smaller objective, and the two stationary values differ by the explicit gap `L / (16 (k + 1))`.
private theorem quadraticHardInstanceFamily_gap_ge_of_mem_coordinateSubspace
    (L : NNReal) {k : ℕ} (hk₁ : 1 ≤ k) (hk₂ : k ≤ (n - 1) / 2)
    {y : E} (hy : y ∈ ℝ^{k,n}) :
    let hardIndex : Fin n := ⟨2 * k, two_mul_lt_of_one_le_of_le_half_sub hk₁ hk₂⟩
    let zStar : E := quadraticHardInstanceStationaryPoint hardIndex
    quadraticHardInstanceFamily (L : ℝ) hardIndex y -
      quadraticHardInstanceFamily (L : ℝ) hardIndex zStar ≥
        (L : ℝ) / (16 * (k + 1 : ℝ)) := by
  dsimp
  let hardIndex : Fin n := ⟨2 * k, two_mul_lt_of_one_le_of_le_half_sub hk₁ hk₂⟩
  let smallIndex : Fin n := ⟨k - 1, by omega⟩
  let zStar : E := quadraticHardInstanceStationaryPoint hardIndex
  let ySmall : ℝ := quadraticHardInstanceFamily (L : ℝ) smallIndex y
  have hstage :
      quadraticHardInstanceFamily (L : ℝ) hardIndex y = ySmall := by
    simpa [ySmall] using
      quadraticHardInstanceFamily_eq_stage_on_coordinateSubspace L hk₁ hk₂ hy
  have hmin :
      IsMinOn (quadraticHardInstanceFamily (L : ℝ) smallIndex) Set.univ
        (quadraticHardInstanceStationaryPoint smallIndex) :=
    quadraticHardInstanceStationaryPoint_isMinOn L smallIndex
  rw [isMinOn_univ_iff] at hmin
  -- The smaller stage stationary point minimizes the smaller stage objective on all of `ℝⁿ`.
  have hsmall_min :
      quadraticHardInstanceFamily (L : ℝ) smallIndex
          (quadraticHardInstanceStationaryPoint smallIndex) ≤
        quadraticHardInstanceFamily (L : ℝ) smallIndex y := by
    simpa [ySmall] using hmin y
  have hvalue_big := quadraticHardInstanceFamily_stationaryPoint_value L hardIndex
  have hvalue_small := quadraticHardInstanceFamily_stationaryPoint_value L smallIndex
  rw [hstage]
  -- The explicit stationary-value formulas differ by exactly `L / (16 * (k + 1))`.
  have hcompare :
      quadraticHardInstanceFamily (L : ℝ) hardIndex zStar ≤
        quadraticHardInstanceFamily (L : ℝ) smallIndex
            (quadraticHardInstanceStationaryPoint smallIndex) -
          (L : ℝ) / (16 * (k + 1 : ℝ)) := by
    rw [hvalue_big, hvalue_small]
    have htwo : (((2 * k + 2 : ℕ) : ℝ)) = 2 * (k + 1 : ℝ) := by
      norm_num [Nat.cast_mul, Nat.cast_add]
      ring
    rw [htwo]
    have hkpos : (0 : ℝ) < k + 1 := by positivity
    have hsmall :
        (((smallIndex.1 + 2 : ℕ) : ℝ)) = (k + 1 : ℝ) := by
      have hsmall_nat : smallIndex.1 + 2 = k + 1 := by
        dsimp [smallIndex]
        omega
      exact_mod_cast hsmall_nat
    have hvalue_eq :
        (↑L / 8) * (-1 + 1 / (2 * (k + 1 : ℝ))) =
          (↑L / 8) * (-1 + 1 / (k + 1 : ℝ)) -
            (L : ℝ) / (16 * (k + 1 : ℝ)) := by
      field_simp [hkpos.ne']
      ring_nf
    rw [hsmall]
    simpa using (le_of_eq hvalue_eq)
  nlinarith

/-- Helper for Theorem 2.8: the tail block `k, ..., 2 * k` of the canonical stationary point of
the hard instance with index `2 * k` has exactly the normalized square mass
`(1^2 + ... + (k + 1)^2) / (2 * k + 2)^2`. -/
-- Proof sketch: rewrite the tail interval as a range sum over `k + i`, evaluate the stationary
-- point coordinates there using `quadraticHardInstanceStationaryPoint_apply`, and then reflect the
-- resulting descending square sum into the ascending sum `1^2 + ... + (k + 1)^2`.
private theorem quadraticHardInstanceStationaryPoint_tail_sqNorm_eq
    {k : ℕ} (hk₁ : 1 ≤ k) (hk₂ : k ≤ (n - 1) / 2) :
    let hardIndex : Fin n := ⟨2 * k, two_mul_lt_of_one_le_of_le_half_sub hk₁ hk₂⟩
    let zStar : E := quadraticHardInstanceStationaryPoint hardIndex
    ∑ i ∈ Icc k (2 * k), (if hi : i < n then zStar ⟨i, hi⟩ ^ 2 else 0) =
      (∑ i ∈ Icc 1 (k + 1), (i : ℝ) ^ 2) / (((2 * k + 2 : ℕ) : ℝ) ^ 2) := by
  dsimp
  let hardIndex : Fin n := ⟨2 * k, two_mul_lt_of_one_le_of_le_half_sub hk₁ hk₂⟩
  let zStar : E := quadraticHardInstanceStationaryPoint hardIndex
  let f : ℕ → ℝ := fun i ↦ if hi : i < n then zStar ⟨i, hi⟩ ^ 2 else 0
  have htwok : 2 * k < n := two_mul_lt_of_one_le_of_le_half_sub hk₁ hk₂
  let denom : ℝ := ((2 * k + 2 : ℕ) : ℝ)
  rw [show Icc k (2 * k) = Ico k (2 * k + 1) by
    simpa using (Finset.Ico_succ_right_eq_Icc k (2 * k))]
  rw [Finset.sum_Ico_eq_sum_range]
  have hspan : 2 * k + 1 - k = k + 1 := by
    omega
  rw [hspan]
  calc
    ∑ i ∈ range (k + 1), f (k + i)
        = ∑ i ∈ range (k + 1),
            ((((k + 1 - i : ℕ) : ℝ) / denom) ^ 2) := by
          refine sum_congr rfl ?_
          intro i hi
          have hi_le : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
          have hiki : k + i ≤ 2 * k := by
            omega
          have hi_lt_n : k + i < n := lt_of_le_of_lt hiki htwok
          have hiki_fin : (⟨k + i, hi_lt_n⟩ : Fin n) ≤ hardIndex :=
            Fin.le_iff_val_le_val.mpr hiki
          have hdenom : denom = 2 * (k + 1 : ℝ) := by
            simp [denom, Nat.cast_mul, Nat.cast_add]
            ring
          simp [f, hi_lt_n, zStar, hardIndex, quadraticHardInstanceStationaryPoint_apply, hiki,
            hdenom]
          have hreal :
              (((2 * k : ℕ) : ℝ) + 2 - (((k + i : ℕ) : ℝ) + 1)) =
                (((k + 1 - i : ℕ) : ℝ)) := by
            have hi2 : k + i + 1 ≤ 2 * k + 2 := by
              omega
            have hnat : 2 * k + 2 - (k + i + 1) = k + 1 - i := by
              omega
            have hcast :
                (((2 * k + 2 : ℕ) : ℝ) - ((k + i + 1 : ℕ) : ℝ)) =
                  (((k + 1 - i : ℕ) : ℝ)) := by
              rw [← Nat.cast_sub hi2, hnat]
            simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_one, add_assoc, add_left_comm, add_comm]
              using hcast
          have hfrac :
              1 - (↑k + ↑i + 1) / (2 * ↑k + 2) =
                (((k + 1 - i : ℕ) : ℝ) / (2 * (↑k + 1))) := by
            have hnum :
                (2 * ↑k + 2 : ℝ) - (↑k + ↑i + 1) =
                  (((k + 1 - i : ℕ) : ℝ)) := by
              calc
                (2 * ↑k + 2 : ℝ) - (↑k + ↑i + 1)
                    = (((2 * k : ℕ) : ℝ) + 2 - (((k + i : ℕ) : ℝ) + 1)) := by
                        norm_num [Nat.cast_add, Nat.cast_mul]
                _ = (((k + 1 - i : ℕ) : ℝ)) := hreal
            calc
              1 - (↑k + ↑i + 1) / (2 * ↑k + 2) =
                  ((2 * ↑k + 2 : ℝ) - (↑k + ↑i + 1)) / (2 * ↑k + 2) := by
                    have hden : (2 * ↑k + 2 : ℝ) ≠ 0 := by positivity
                    field_simp [hden]
              _ = (((k + 1 - i : ℕ) : ℝ) / (2 * (↑k + 1))) := by
                    rw [hnum]
                    ring
          rw [hfrac]
    _ = ∑ i ∈ range (k + 1),
          ((((i + 1 : ℕ) : ℝ) / denom) ^ 2) := by
          have hrewrite :
              ∑ i ∈ range (k + 1), ((((k + 1 - i : ℕ) : ℝ) / denom) ^ 2) =
                ∑ i ∈ range (k + 1), ((((k - i + 1 : ℕ) : ℝ) / denom) ^ 2) := by
                  refine sum_congr rfl ?_
                  intro i hi
                  have hi_le : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
                  have hnat : k + 1 - i = k - i + 1 := by
                    omega
                  simp [hnat]
          have hreflect :
              ∑ i ∈ range (k + 1), ((((k - i + 1 : ℕ) : ℝ) / denom) ^ 2) =
                ∑ i ∈ range (k + 1), ((((i + 1 : ℕ) : ℝ) / denom) ^ 2) := by
                  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                    (Finset.sum_range_reflect
                      (fun i ↦ ((((i + 1 : ℕ) : ℝ) / denom) ^ 2))
                      (k + 1))
          exact hrewrite.trans hreflect
    _ = ∑ i ∈ range (k + 1), (((i + 1 : ℕ) : ℝ) ^ 2) / (denom ^ 2) := by
          refine sum_congr rfl ?_
          intro i hi
          rw [div_pow]
    _ = (∑ i ∈ range (k + 1), (((i + 1 : ℕ) : ℝ) ^ 2)) / (denom ^ 2) := by
          rw [Finset.sum_div]
    _ = (∑ i ∈ Icc 1 (k + 1), (i : ℝ) ^ 2) / (denom ^ 2) := by
          congr 1
          rw [show Icc 1 (k + 1) = Ico 1 (k + 2) by
            simpa using (Finset.Ico_succ_right_eq_Icc 1 (k + 1))]
          rw [Finset.sum_Ico_eq_sum_range]
          refine sum_congr rfl ?_
          intro i hi
          ring_nf

/-- Helper for Theorem 2.8: the square sum on `1, ..., k + 1` controls at least one eighth of the
square sum on `1, ..., 2 * k + 1`. -/
-- Proof sketch: expand both interval sums with `sum_Ico_pow` over `ℚ`, normalize the resulting
-- cubic polynomials, and then cast the arithmetic inequality to `ℝ`.
private theorem one_eighth_mul_sum_Icc_sq_le_sum_Icc_sq_tail (k : ℕ) :
    (1 / 8 : ℝ) * (∑ i ∈ Icc 1 (2 * k + 1), (i : ℝ) ^ 2) ≤
      ∑ i ∈ Icc 1 (k + 1), (i : ℝ) ^ 2 := by
  have hq :
      ((1 / 8 : ℚ) * (∑ i ∈ Icc 1 (2 * k + 1), (i : ℚ) ^ 2) ≤
        ∑ i ∈ Icc 1 (k + 1), (i : ℚ) ^ 2) := by
    rw [show Icc 1 (2 * k + 1) = Ico 1 ((2 * k + 1) + 1) by
      simpa using (Finset.Ico_succ_right_eq_Icc 1 (2 * k + 1))]
    rw [show Icc 1 (k + 1) = Ico 1 ((k + 1) + 1) by
      simpa using (Finset.Ico_succ_right_eq_Icc 1 (k + 1))]
    rw [sum_Ico_pow, sum_Ico_pow]
    repeat rw [sum_range_succ]
    repeat rw [sum_range_zero]
    norm_num [bernoulli'_zero, bernoulli'_one, bernoulli'_two]
    ring_nf
    nlinarith
  have hr :
      (((1 / 8 : ℚ) * (∑ i ∈ Icc 1 (2 * k + 1), (i : ℚ) ^ 2) : ℚ) : ℝ) ≤
        (∑ i ∈ Icc 1 (k + 1), (i : ℚ) ^ 2 : ℚ) := by
    exact_mod_cast hq
  simpa using hr

/-- Helper for Theorem 2.8: any point supported on the first `k` coordinates stays at squared
distance at least `‖z_*‖² / 8` from the stationary point of the hard instance with index
`2 * k`. -/
-- Proof sketch: the tail coordinates of `y - z_*` agree with `-z_*` because `y` vanishes from
-- coordinate `k` onward. The Euclidean norm therefore dominates the tail square-sum of `z_*`,
-- and explicit finite-sum estimates show that tail square-sum is at least one eighth of the full
-- norm square of `z_*`.
private theorem quadraticHardInstanceStationaryPoint_tail_distance_lower_bound
    {k : ℕ} (hk₁ : 1 ≤ k) (hk₂ : k ≤ (n - 1) / 2) {y : E} (hy : y ∈ ℝ^{k,n}) :
    let hardIndex : Fin n := ⟨2 * k, two_mul_lt_of_one_le_of_le_half_sub hk₁ hk₂⟩
    let zStar : E := quadraticHardInstanceStationaryPoint hardIndex
    ‖y - zStar‖ ^ 2 ≥ (1 / 8 : ℝ) * ‖zStar‖ ^ 2 := by
  dsimp
  let hardIndex : Fin n := ⟨2 * k, two_mul_lt_of_one_le_of_le_half_sub hk₁ hk₂⟩
  let zStar : E := quadraticHardInstanceStationaryPoint hardIndex
  let g : ℕ → ℝ := fun i ↦ if hi : i < n then ((y - zStar) ⟨i, hi⟩) ^ 2 else 0
  have htwok : 2 * k < n := two_mul_lt_of_one_le_of_le_half_sub hk₁ hk₂
  have hnorm :
      ‖y - zStar‖ ^ 2 = ∑ i ∈ range n, g i := by
    calc
      ‖y - zStar‖ ^ 2 = ∑ i : Fin n, ((y - zStar) i) ^ 2 := by
        simpa using (EuclideanSpace.real_norm_sq_eq (y - zStar))
      _ = ∑ i : Fin n, g i.1 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [g]
      _ = ∑ i ∈ range n, g i := Fin.sum_univ_eq_sum_range g n
  have hsubset : Icc k (2 * k) ⊆ range n := by
    intro i hi
    exact mem_range.mpr (lt_of_le_of_lt (Finset.mem_Icc.mp hi).2 htwok)
  have htail_le :
      ∑ i ∈ Icc k (2 * k), g i ≤ ∑ i ∈ range n, g i := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro i hi_range hi_not_mem
      by_cases hi : i < n
      · have hsquare : 0 ≤ ((y - zStar) ⟨i, hi⟩) ^ 2 := sq_nonneg _
        simpa [g, hi] using hsquare
      · simp [g, hi])
  have htail_eq :
      ∑ i ∈ Icc k (2 * k), g i =
        ∑ i ∈ Icc k (2 * k), (if hi : i < n then zStar ⟨i, hi⟩ ^ 2 else 0) := by
    refine sum_congr rfl ?_
    intro i hi
    have hiki : i ≤ 2 * k := (Finset.mem_Icc.mp hi).2
    have hi_lt_n : i < n := lt_of_le_of_lt hiki htwok
    have hyi : y ⟨i, hi_lt_n⟩ = 0 := (mem_coordinateSubspace_iff.mp hy) ⟨i, hi_lt_n⟩
      (Finset.mem_Icc.mp hi).1
    have hsq :
        ((y - zStar) ⟨i, hi_lt_n⟩) ^ 2 = zStar ⟨i, hi_lt_n⟩ ^ 2 := by
      simp [hyi]
    simpa [g, hi_lt_n] using hsq
  have htail_mass :
      (1 / 8 : ℝ) * ‖zStar‖ ^ 2 ≤
        ∑ i ∈ Icc k (2 * k), (if hi : i < n then zStar ⟨i, hi⟩ ^ 2 else 0) := by
    rw [quadraticHardInstanceStationaryPoint_sqNorm_eq hardIndex]
    rw [quadraticHardInstanceStationaryPoint_tail_sqNorm_eq hk₁ hk₂]
    have hsum := one_eighth_mul_sum_Icc_sq_le_sum_Icc_sq_tail k
    have hden : (0 : ℝ) < (((2 * k + 2 : ℕ) : ℝ) ^ 2) := by
      positivity
    have hdiv :
        (1 / 8 : ℝ) *
            ((∑ i ∈ Icc 1 (2 * k + 1), (i : ℝ) ^ 2) / (((2 * k + 2 : ℕ) : ℝ) ^ 2)) ≤
          (∑ i ∈ Icc 1 (k + 1), (i : ℝ) ^ 2) / (((2 * k + 2 : ℕ) : ℝ) ^ 2) := by
      have hdiv' :
          ((1 / 8 : ℝ) * (∑ i ∈ Icc 1 (2 * k + 1), (i : ℝ) ^ 2)) /
              (((2 * k + 2 : ℕ) : ℝ) ^ 2) ≤
            (∑ i ∈ Icc 1 (k + 1), (i : ℝ) ^ 2) /
              (((2 * k + 2 : ℕ) : ℝ) ^ 2) := by
        exact div_le_div_of_nonneg_right hsum (le_of_lt hden)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv'
    nlinarith
  have htail_to_norm :
      ∑ i ∈ Icc k (2 * k), (if hi : i < n then zStar ⟨i, hi⟩ ^ 2 else 0) ≤
        ‖y - zStar‖ ^ 2 := by
    calc
      ∑ i ∈ Icc k (2 * k), (if hi : i < n then zStar ⟨i, hi⟩ ^ 2 else 0)
          = ∑ i ∈ Icc k (2 * k), g i := by
              symm
              exact htail_eq
      _ ≤ ∑ i ∈ range n, g i := htail_le
      _ = ‖y - zStar‖ ^ 2 := by
            symm
            exact hnorm
  exact le_trans htail_mass htail_to_norm

/-- Core/canonical form of Theorem 2.8: the translated owner hard instance
`quadraticHardInstanceFamily (L : ℝ) ⟨2 * k, _⟩` lies in `𝓕_L^{1,1}(ℝⁿ)`, its
translated canonical stationary point globally minimizes it via
`quadraticHardInstanceStationaryPoint_isMinOn`, and together they realize the smooth first-order
lower bound at step `k`. -/
-- Proof sketch: take the chapter hard instance with active prefix length `2 * k + 1`, translate
-- it so that the prescribed initial point is `x₀`, and use the span condition to keep the first
-- `k` iterates inside the corresponding prefix-coordinate subspace. The translated canonical
-- stationary point still minimizes the translated objective, and its nontrivial tail yields the
-- objective-gap and distance lower bounds.
theorem quadraticHardInstanceFamily_translate_with_firstOrder_lower_bound
    (L : NNReal) {k : ℕ} (hk₁ : 1 ≤ k) (hk₂ : k ≤ (n - 1) / 2) (x0 : E) :
    let hardIndex : Fin n := ⟨2 * k, two_mul_lt_of_one_le_of_le_half_sub hk₁ hk₂⟩
    let f : E → ℝ := fun x ↦ quadraticHardInstanceFamily (L : ℝ) hardIndex (x - x0)
    let xStar : E := x0 + quadraticHardInstanceStationaryPoint hardIndex
    f ∈ (𝓕[L, p]¹¹ : Set (E → ℝ)) ∧
      IsMinOn f Set.univ xStar ∧
      ∀ method : (E → ℝ) → E → ℕ → E,
        SatisfiesSpanCondition method →
          let xk := method f x0 k
          f xk - f xStar ≥
              (3 * (L : ℝ) * ‖x0 - xStar‖ ^ 2) /
                (32 * ((k + 1 : ℝ) ^ 2)) ∧
            ‖xk - xStar‖ ^ 2 ≥
              (1 / 8 : ℝ) * ‖x0 - xStar‖ ^ 2 := by
  dsimp
  let hardIndex : Fin n := ⟨2 * k, two_mul_lt_of_one_le_of_le_half_sub hk₁ hk₂⟩
  let f : E → ℝ := fun x ↦ quadraticHardInstanceFamily (L : ℝ) hardIndex (x - x0)
  let zStar : E := quadraticHardInstanceStationaryPoint hardIndex
  let xStar : E := x0 + zStar
  refine ⟨?_, ?_, ?_⟩
  · -- The translated hard instance stays in the chapter smooth-convex owner class.
    simpa [f] using
      quadraticHardInstanceFamily_translate_mem_smooth_convex_objective L hardIndex x0
  · -- Translating the canonical stationary point preserves global minimality.
    simpa [f, xStar, zStar] using
      quadraticHardInstanceFamily_translate_isMinOn L hardIndex x0
  · intro method hmethod
    let xk : E := method f x0 k
    -- The span condition keeps the `k`-th iterate difference in the `k`-prefix coordinate subspace.
    have hxk_mem : xk - x0 ∈ ℝ^{k,n} := by
      simpa [f, xk] using
        span_condition_iterate_sub_mem_coordinateSubspace L hk₁ hk₂ x0 method hmethod
          (j := k) le_rfl
    have hgap :
        quadraticHardInstanceFamily (L : ℝ) hardIndex (xk - x0) -
            quadraticHardInstanceFamily (L : ℝ) hardIndex zStar ≥
          (L : ℝ) / (16 * (k + 1 : ℝ)) :=
      quadraticHardInstanceFamily_gap_ge_of_mem_coordinateSubspace L hk₁ hk₂ hxk_mem
    have hdist :
        ‖(xk - x0) - zStar‖ ^ 2 ≥ (1 / 8 : ℝ) * ‖zStar‖ ^ 2 :=
      quadraticHardInstanceStationaryPoint_tail_distance_lower_bound hk₁ hk₂ hxk_mem
    have hsq :
        ‖zStar‖ ^ 2 ≤ (2 : ℝ) * (k + 1 : ℝ) / 3 := by
      have hsq' : ‖zStar‖ ^ 2 ≤ (1 / 3 : ℝ) * ((2 * k : ℕ) + 2 : ℕ) := by
        simpa [hardIndex, zStar, Nat.cast_mul, Nat.cast_add] using
          (quadraticHardInstanceStationaryPoint_sqNorm_le hardIndex)
      have htwo : (((2 * k : ℕ) + 2 : ℕ) : ℝ) = 2 * (k + 1 : ℝ) := by
        norm_num [Nat.cast_mul, Nat.cast_add]
        ring
      rw [htwo] at hsq'
      nlinarith
    constructor
    · -- Route correction: the final objective-gap estimate is now reduced to the stage-gap lemma
      -- plus the norm upper bound for the canonical stationary point.
      have hx0dist : ‖x0 - xStar‖ ^ 2 = ‖zStar‖ ^ 2 := by
        simp [xStar, zStar, sub_eq_add_neg, add_comm]
      have hgap' :
          f xk - f xStar ≥ (L : ℝ) / (16 * (k + 1 : ℝ)) := by
        simpa [f, xk, xStar, zStar, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hgap
      rw [hx0dist]
      have hL : (0 : ℝ) ≤ L := by exact_mod_cast L.2
      have hkpos : (0 : ℝ) < k + 1 := by positivity
      have hrhs_le :
          (3 * (L : ℝ) * ‖zStar‖ ^ 2) / (32 * (k + 1 : ℝ) ^ 2) ≤
            (L : ℝ) / (16 * (k + 1 : ℝ)) := by
        have hmul : (L : ℝ) * ‖zStar‖ ^ 2 ≤ (L : ℝ) * (2 * (k + 1 : ℝ) / 3) :=
          mul_le_mul_of_nonneg_left hsq hL
        have hnum :
            3 * (L : ℝ) * ‖zStar‖ ^ 2 ≤ 2 * (L : ℝ) * (k + 1 : ℝ) := by
          nlinarith
        have hdiv :
            (3 * (L : ℝ) * ‖zStar‖ ^ 2) / (32 * (k + 1 : ℝ) ^ 2) ≤
              (2 * (L : ℝ) * (k + 1 : ℝ)) / (32 * (k + 1 : ℝ) ^ 2) := by
          exact div_le_div_of_nonneg_right hnum (by positivity)
        refine hdiv.trans_eq ?_
        field_simp [hkpos.ne']
        ring
      exact le_trans hrhs_le hgap'
    · -- Rewrite both distances through the translated stationary point and reuse the tail bound.
      simpa [xk, xStar, zStar, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hdist

/-- Theorem 2.8: for every iteration index `k` with `1 ≤ k ≤ (n - 1) / 2` and every
initial point `x₀ ∈ ℝⁿ`, there exists an objective
`f ∈ 𝓕_L^{1,1}(ℝⁿ)` together with a global minimizer `x*`, such that every first-order
iterative method satisfying the span condition has its `k`-th iterate satisfy the lower
bounds on objective error and squared distance to `x*`. -/
-- Proof sketch: package the translated owner hard instance from
-- `quadraticHardInstanceFamily_translate_with_firstOrder_lower_bound` as the existential witness
-- `f`, and take its translated canonical stationary point as `x*`.
theorem exists_smoothConvexObjective_with_firstOrder_lower_bound
    (L : NNReal) {k : ℕ} (hk₁ : 1 ≤ k) (hk₂ : k ≤ (n - 1) / 2) (x0 : E) :
    ∃ f : E → ℝ,
      ∃ xStar : E,
        f ∈ (𝓕[L, p]¹¹ : Set (E → ℝ)) ∧
          IsMinOn f Set.univ xStar ∧
          ∀ method : (E → ℝ) → E → ℕ → E,
            SatisfiesSpanCondition method →
              let xk := method f x0 k
              f xk - f xStar ≥
                  (3 * (L : ℝ) * ‖x0 - xStar‖ ^ 2) /
                    (32 * ((k + 1 : ℝ) ^ 2)) ∧
                ‖xk - xStar‖ ^ 2 ≥
                  (1 / 8 : ℝ) * ‖x0 - xStar‖ ^ 2 := by
  dsimp
  rcases
      quadraticHardInstanceFamily_translate_with_firstOrder_lower_bound
        L hk₁ hk₂ x0 with
    ⟨hf, hxStar, hlower⟩
  exact ⟨_, _, hf, hxStar, hlower⟩

end

/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Text_4_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_2_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient
open scoped BigOperators

variable {n k : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Helper for Proposition 4.3.2: a `C²` scalar field on Euclidean space has a differentiable
gradient. -/
private theorem differentiableAt_gradient_of_contDiffAt_two
    {m : Type*} [NormedAddCommGroup m] [InnerProductSpace ℝ m] [CompleteSpace m]
    {f : m → ℝ} {x : m} (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (∇ f) x := by
  let D : StrongDual ℝ m →L[ℝ] m :=
    (InnerProductSpace.toDual ℝ m).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    -- A `C²` scalar field has a differentiable first derivative.
    exact
      (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  -- Rewrite the gradient through the Riesz map so the chain rule applies directly.
  change DifferentiableAt ℝ (fun y ↦ D (fderiv ℝ f y)) x
  exact (D.hasFDerivAt.comp x hfdiff.hasFDerivAt).differentiableAt

/-- Helper for Proposition 4.3.2: precomposing a differentiable scalar field with a continuous
linear map pulls back its gradient by the adjoint. -/
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

/-- Helper for Proposition 4.3.2: precomposing by a continuous linear map transports the Hessian
quadratic form to the image direction. -/
private theorem hessian_quadratic_form_comp_continuousLinearMap
    {m : Type*} [NormedAddCommGroup m] [InnerProductSpace ℝ m] [CompleteSpace m]
    {f : m → ℝ} (A : E →L[ℝ] m) (hf : ContDiff ℝ 2 f) (x h : E) :
    inner ℝ (hessian (f ∘ A) x h) h =
      inner ℝ (hessian f (A x) (A h)) (A h) := by
  have hgradEq :
      ∇ (f ∘ A) = fun y : E ↦ A.adjoint (∇ f (A y)) := by
    -- Identify the pulled-back gradient pointwise by differentiating through the linear map.
    refine gradient_eq ?_
    intro y
    exact hasGradientAt_comp_continuousLinearMap A
      (hf.contDiffAt.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0))
  have hgradDiff : DifferentiableAt ℝ (∇ f) (A x) :=
    differentiableAt_gradient_of_contDiffAt_two hf.contDiffAt
  have hinner :
      HasFDerivAt (fun y : E ↦ ∇ f (A y)) ((hessian f (A x)).comp A) x := by
    -- Differentiate the gradient after the linear prefix map.
    change HasFDerivAt (∇ f ∘ A) ((hessian f (A x)).comp A) x
    exact hgradDiff.hasFDerivAt.comp x A.hasFDerivAt
  have houter :
      HasFDerivAt (fun y : E ↦ A.adjoint (∇ f (A y)))
        ((A.adjoint).comp ((hessian f (A x)).comp A)) x := by
    -- The adjoint is linear, so its derivative is constant.
    exact A.adjoint.hasFDerivAt.comp x hinner
  have hderivEq :
      fderiv ℝ (fun y : E ↦ A.adjoint (∇ f (A y))) x =
        (A.adjoint).comp ((hessian f (A x)).comp A) := houter.fderiv
  -- Replace the pulled-back gradient by its derivative formula.
  suffices hmain :
      inner ℝ ((A.adjoint) ((hessian f (A x)).comp A h)) h =
        inner ℝ (hessian f (A x) (A h)) (A h) by
    simpa [hessian, hgradEq, hderivEq] using hmain
  calc
    inner ℝ ((A.adjoint) ((hessian f (A x)).comp A h)) h =
        inner ℝ h ((A.adjoint) ((hessian f (A x)).comp A h)) := by
          rw [real_inner_comm]
    _ = inner ℝ (A h) ((hessian f (A x)).comp A h) :=
        A.adjoint_inner_right h ((hessian f (A x)).comp A h)
    _ = inner ℝ (hessian f (A x) (A h)) (A h) := by
          rw [ContinuousLinearMap.comp_apply, real_inner_comm]

/-- Helper for Proposition 4.3.2: on Euclidean space, the second Fréchet derivative is the dual
view of the Hessian operator. -/
private theorem sndFDeriv_eq_toDual_comp_hessian
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    fderiv ℝ (fderiv ℝ f) x =
      (InnerProductSpace.toDual ℝ E).toContinuousLinearMap.comp (hessian f x) := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    have hfderiv : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
      hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    exact hfderiv.differentiableAt one_ne_zero
  have hhess :
      hessian f x = D.comp (fderiv ℝ (fderiv ℝ f) x) := by
    -- This is the same Riesz-identification used in the forward `C22 ⇒ hessian` bridge.
    simpa [D, gradient, hessian] using fderiv_comp x D.differentiableAt hfdiff
  have hcancel :
      (InnerProductSpace.toDual ℝ E).toContinuousLinearMap.comp D =
        ContinuousLinearMap.id ℝ (StrongDual ℝ E) := by
    -- `toDual` and its inverse cancel after bundling as continuous linear maps.
    ext φ y
    change
      ((InnerProductSpace.toDual ℝ E)
        ((InnerProductSpace.toDual ℝ E).symm φ)) y = φ y
    simp
  calc
    fderiv ℝ (fderiv ℝ f) x =
        (ContinuousLinearMap.id ℝ (StrongDual ℝ E)).comp (fderiv ℝ (fderiv ℝ f) x) := by
          simp
    _ =
        ((InnerProductSpace.toDual ℝ E).toContinuousLinearMap.comp D).comp
          (fderiv ℝ (fderiv ℝ f) x) := by
          rw [hcancel]
    _ =
        (InnerProductSpace.toDual ℝ E).toContinuousLinearMap.comp
          (hessian f x) := by
          rw [ContinuousLinearMap.comp_assoc, hhess]

/-- Helper for Proposition 4.3.2: composing an operator with the Riesz map preserves its norm. -/
private theorem toDual_comp_norm (T : E →L[ℝ] E) :
    ‖(InnerProductSpace.toDual ℝ E).toContinuousLinearMap.comp T‖ = ‖T‖ := by
  -- Use the forward Riesz isometry directly, so the composition norm is preserved on the nose.
  exact (InnerProductSpace.toDual ℝ E).toLinearIsometry.norm_toContinuousLinearMap_comp (g := T)

/-- Helper for Proposition 4.3.2: a global Hessian operator bound upgrades directly to the
chapter's `C22[...]` owner. -/
private theorem mem_C22_of_contDiff_two_and_hessian_norm_sub_le
    {f : E → ℝ} {L3 : NNReal} (hf : ContDiff ℝ 2 f)
    (hhess : ∀ x y, ‖hessian f x - hessian f y‖ ≤ (L3 : ℝ) * ‖x - y‖) :
    f ∈ C22[L3] := by
  refine
    { contDiff := hf
      sndFDeriv_lipschitz := ?_ }
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  -- Rewrite the second Fréchet derivative through the intrinsic Hessian operator.
  rw [sndFDeriv_eq_toDual_comp_hessian (hf.contDiffAt (x := x)),
    sndFDeriv_eq_toDual_comp_hessian (hf.contDiffAt (x := y))]
  calc
    ‖(InnerProductSpace.toDual ℝ E).toContinuousLinearMap.comp (hessian f x) -
        (InnerProductSpace.toDual ℝ E).toContinuousLinearMap.comp (hessian f y)‖
        =
          ‖(InnerProductSpace.toDual ℝ E).toContinuousLinearMap.comp
            (hessian f x - hessian f y)‖ := by
            rw [ContinuousLinearMap.comp_sub]
    _ = ‖hessian f x - hessian f y‖ := by
          exact toDual_comp_norm (hessian f x - hessian f y)
    _ ≤ (L3 : ℝ) * ‖x - y‖ := hhess x y

/-- Helper for Proposition 4.3.2: an `L²` operator-norm bound on Hessian matrices gives the same
bound for the intrinsic Hessian operators. -/
private theorem hessian_norm_sub_le_of_hessianMatrix_norm_sub_le
    {f : E → ℝ} {L : ℝ}
    (hhess : ∀ x y, ‖hessian f x - hessian f y‖ ≤ L * ‖x - y‖) :
    ∀ x y, ‖hessian f x - hessian f y‖ ≤ L * ‖x - y‖ := by
  intro x y
  exact hhess x y

/-- Helper for Proposition 4.3.2: once the hard-instance objective is known to be `C²` and its
Hessian matrices satisfy the uniform `(8 * √2)` operator-norm estimate, the owner claim follows
immediately. -/
private theorem fk_mem_C22_of_matrix_bound
    (hkn : k ≤ n) (hcont : ContDiff ℝ 2 (fk hkn))
    (hhess : ∀ x y : E,
      ‖hessian (fk hkn) x - hessian (fk hkn) y‖ ≤ (8 * Real.sqrt 2) * ‖x - y‖) :
    fk hkn ∈ C22[⟨8 * Real.sqrt 2, by positivity⟩] := by
  -- First package the intrinsic Hessian estimate into the owner surface.
  exact
    mem_C22_of_contDiff_two_and_hessian_norm_sub_le hcont
      (hessian_norm_sub_le_of_hessianMatrix_norm_sub_le hhess)

/-- Helper for Proposition 4.3.2: each Euclidean coordinate is bounded by the ambient
Euclidean norm. -/
private theorem abs_apply_le_norm (x : E) (i : Fin n) :
    |x i| ≤ ‖x‖ := by
  -- Realize the coordinate as an inner product against the `i`th standard basis vector.
  calc
    |x i| = |inner ℝ (EuclideanSpace.single i (1 : ℝ)) x| := by
      simpa using (congrArg abs (EuclideanSpace.inner_single_left i (1 : ℝ) x)).symm
    _ ≤ ‖EuclideanSpace.single i (1 : ℝ)‖ * ‖x‖ := abs_real_inner_le_norm _ _
    _ = ‖x‖ := by
      simp

/-- Helper for Proposition 4.3.2: the difference of two coordinates is controlled by
`√2` times the Euclidean norm. -/
private theorem euclidean_single_sub_single_norm_le_sqrt_two
    (i j : Fin n) :
    ‖EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j (1 : ℝ)‖ ≤ Real.sqrt 2 := by
  by_cases hij : i = j
  · subst hij
    simp
  · have horth :
        inner ℝ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) = 0 := by
      simpa using (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin n)).inner_eq_zero hij
    have hsq :
        ‖EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j (1 : ℝ)‖ ^ (2 : ℕ) = 2 := by
      calc
        ‖EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j (1 : ℝ)‖ ^ (2 : ℕ)
            =
              ‖EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j (1 : ℝ)‖ *
                ‖EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j (1 : ℝ)‖ := by
                  rw [pow_two]
        _ =
              ‖EuclideanSpace.single i (1 : ℝ)‖ ^ (2 : ℕ) +
                ‖EuclideanSpace.single j (1 : ℝ)‖ ^ (2 : ℕ) := by
                  simpa using norm_sub_sq_eq_norm_sq_add_norm_sq_real horth
        _ = 2 := by norm_num
    have hsqrt := congrArg Real.sqrt hsq
    have hEq :
        ‖EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j (1 : ℝ)‖ = Real.sqrt 2 := by
      simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hsqrt
    exact hEq.le

/-- Helper for Proposition 4.3.2: the difference of two coordinates is controlled by
`√2` times the Euclidean norm. -/
private theorem abs_sub_apply_le_sqrt_two_mul_norm
    (x : E) (i j : Fin n) :
    |x i - x j| ≤ Real.sqrt 2 * ‖x‖ := by
  -- Realize the coordinate difference as pairing with `e_i - e_j`.
  calc
    |x i - x j| =
        |inner ℝ (EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j (1 : ℝ)) x| := by
          congr 1
          have hi : inner ℝ (EuclideanSpace.single i (1 : ℝ)) x = x i := by
            simpa using EuclideanSpace.inner_single_left i (1 : ℝ) x
          have hj : inner ℝ (EuclideanSpace.single j (1 : ℝ)) x = x j := by
            simpa using EuclideanSpace.inner_single_left j (1 : ℝ) x
          calc
            x i - x j
                = inner ℝ (EuclideanSpace.single i (1 : ℝ)) x -
                    inner ℝ (EuclideanSpace.single j (1 : ℝ)) x := by
                      rw [hi, hj]
            _ = inner ℝ
                  (EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j (1 : ℝ)) x := by
                    rw [inner_sub_left]
    _ ≤ ‖EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single j (1 : ℝ)‖ * ‖x‖ := by
          exact abs_real_inner_le_norm _ _
    _ ≤ Real.sqrt 2 * ‖x‖ := by
          exact mul_le_mul_of_nonneg_right
            (euclidean_single_sub_single_norm_le_sqrt_two i j) (norm_nonneg _)

/-- Helper for Proposition 4.3.2: the change of absolute values of two coordinates is also
controlled by `√2` times the Euclidean norm. -/
private theorem abs_abs_sub_abs_apply_le_sqrt_two_mul_norm
    (x : E) (i j : Fin n) :
    abs (|x i| - |x j|) ≤ Real.sqrt 2 * ‖x‖ := by
  -- First use the scalar reverse triangle inequality, then apply the coordinate-difference bound.
  exact
    (abs_abs_sub_abs_le_abs_sub (x i) (x j)).trans
      (abs_sub_apply_le_sqrt_two_mul_norm x i j)

/-- Helper for Proposition 4.3.2: the scalar cubic `t ↦ (1 / 3) |t|^3` is reused via the
Chapter 4 power-distance owner on `ℝ`. -/
private abbrev scalarCubic : ℝ → ℝ :=
  powerDistance (3 : ℝ) (0 : ℝ)

/-- Helper for Proposition 4.3.2: the scalar cubic has the expected explicit formula. -/
private theorem scalarCubic_apply (t : ℝ) :
    scalarCubic t = (1 / 3 : ℝ) * |t| ^ (3 : ℕ) := by
  -- On `ℝ`, the centered power-distance is exactly `(1 / 3) * |t|^3`.
  simp [scalarCubic, powerDistance]

/-- Helper for Proposition 4.3.2: the scalar cubic is `C²`. -/
private theorem scalarCubic_contDiff_two :
    ContDiff ℝ 2 scalarCubic := by
  -- Reuse the earlier owner theorem `powerDistance (3) 0 ∈ C22[2]` specialized to `ℝ`.
  simpa [scalarCubic] using
    ((powerDistance_three_zero_mem_C22 :
        powerDistance (3 : ℝ) (0 : ℝ) ∈ C22[(2 : NNReal)]).contDiff)

/-- Helper for Proposition 4.3.2: the active prefix length `((k - 1) + 1)` embeds into the ambient
dimension when `0 < k ≤ n`. -/
private theorem positive_branch_prefix_len_le (hk : 0 < k) (hkn : k ≤ n) :
    (k - 1) + 1 ≤ n := by
  omega

/-- Helper for Proposition 4.3.2: the positive branch keeps the first `k` coordinates as a prefix
vector. -/
private def positiveBranchPrefix (hk : 0 < k) (hkn : k ≤ n) (x : E) :
    EuclideanSpace ℝ (Fin ((k - 1) + 1)) :=
  (EuclideanSpace.equiv (Fin ((k - 1) + 1)) ℝ).symm
    fun i ↦ x (Fin.castLE (positive_branch_prefix_len_le hk hkn) i)

/-- Helper for Proposition 4.3.2: the prefix vector reads off the corresponding ambient
coordinate. -/
private theorem positiveBranchPrefix_apply (hk : 0 < k) (hkn : k ≤ n) (x : E)
    (i : Fin ((k - 1) + 1)) :
    positiveBranchPrefix hk hkn x i =
      x (Fin.castLE (positive_branch_prefix_len_le hk hkn) i) := by
  -- The prefix vector was defined by transporting exactly these first coordinates.
  simp [positiveBranchPrefix]

/-- Helper for Proposition 4.3.2: the initial linear feature is the first active coordinate. -/
private def initialFeature (hk : 0 < k) (hkn : k ≤ n) : E →L[ℝ] ℝ :=
  EuclideanSpace.proj (Fin.castLE (positive_branch_prefix_len_le hk hkn) (0 : Fin ((k - 1) + 1)))

/-- Helper for Proposition 4.3.2: each edge feature is the adjacent coordinate difference in the
active prefix chain. -/
private def edgeFeature (hk : 0 < k) (hkn : k ≤ n) (i : Fin (k - 1)) : E →L[ℝ] ℝ :=
  (EuclideanSpace.proj
      (Fin.castLE (positive_branch_prefix_len_le hk hkn) (Fin.castSucc i)) : E →L[ℝ] ℝ) -
    (EuclideanSpace.proj
      (Fin.castLE (positive_branch_prefix_len_le hk hkn) i.succ) : E →L[ℝ] ℝ)

/-- Helper for Proposition 4.3.2: the terminal feature is the last active prefix coordinate. -/
private def terminalFeature (hk : 0 < k) (hkn : k ≤ n) : E →L[ℝ] ℝ :=
  EuclideanSpace.proj
    (Fin.castLE (positive_branch_prefix_len_le hk hkn) (Fin.last (k - 1)))

/-- Helper for Proposition 4.3.2: each tail feature is one coordinate beyond the active prefix. -/
private def tailFeature (_hkn : k ≤ n) (i : Fin (n - k)) : E →L[ℝ] ℝ :=
  EuclideanSpace.proj (Fin.natAdd_castLEEmb (Nat.sub_le n k) i)

/-- Helper for Proposition 4.3.2: in the positive branch, `fk` is the source sum of adjacent
scalar-cubic features, the terminal cubic, the linear term, and the tail cubics. -/
private theorem fk_eq_scalarCubic_features_of_pos (hk : 0 < k) (hkn : k ≤ n) :
    fk hkn =
      fun x : E ↦
        (∑ i : Fin (k - 1), scalarCubic (edgeFeature hk hkn i x)) +
          scalarCubic (terminalFeature hk hkn x) -
          initialFeature hk hkn x +
          ∑ i : Fin (n - k), scalarCubic (tailFeature hkn i x) := by
  ext x
  -- Expand `fk` in the positive branch, then rewrite each source cubic as `scalarCubic`.
  simp only [fk_apply, hk, scalarCubic_apply, edgeFeature, terminalFeature, initialFeature,
    tailFeature, ContinuousLinearMap.sub_apply, EuclideanSpace.coe_proj, Fin.castLE_castSucc]
  simp only [↓reduceDIte, one_div]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]

/-- Helper for Proposition 4.3.2: the ambient norm splits exactly into the active prefix and the
tail coordinates. -/
private theorem positive_k_prefix_tail_norm_sq_split (hk : 0 < k) (hkn : k ≤ n) (h : E) :
    ‖h‖ ^ (2 : ℕ) =
      ‖positiveBranchPrefix hk hkn h‖ ^ (2 : ℕ) +
        ∑ i : Fin (n - k), ‖tailFeature hkn i h‖ ^ (2 : ℕ) := by
  let sq : ℕ → ℝ := fun i ↦ if hi : i < n then h ⟨i, hi⟩ ^ (2 : ℕ) else 0
  have hpred : (k - 1) + 1 = k := by
    omega
  have hprefix :
      ‖positiveBranchPrefix hk hkn h‖ ^ (2 : ℕ) = ∑ i ∈ Finset.range k, sq i := by
    calc
      ‖positiveBranchPrefix hk hkn h‖ ^ (2 : ℕ) =
          ∑ i : Fin ((k - 1) + 1), (positiveBranchPrefix hk hkn h i) ^ (2 : ℕ) := by
            simpa using EuclideanSpace.real_norm_sq_eq (positiveBranchPrefix hk hkn h)
      _ = ∑ i : Fin ((k - 1) + 1), sq i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi_lt_n : (i : ℕ) < n := lt_of_lt_of_le i.2 (positive_branch_prefix_len_le hk hkn)
            have hcast :
                (Fin.castLE (positive_branch_prefix_len_le hk hkn) i : Fin n) =
                  ⟨(i : ℕ), hi_lt_n⟩ := by
              ext
              rfl
            rw [positiveBranchPrefix_apply]
            simp [sq, hi_lt_n, hcast]
      _ = ∑ i ∈ Finset.range ((k - 1) + 1), sq i := by
            simpa using (Fin.sum_univ_eq_sum_range sq ((k - 1) + 1))
      _ = ∑ i ∈ Finset.range k, sq i := by
            simp [hpred]
  have htail :
      (∑ i : Fin (n - k), ‖tailFeature hkn i h‖ ^ (2 : ℕ)) = ∑ i ∈ Finset.Ico k n, sq i := by
    calc
      (∑ i : Fin (n - k), ‖tailFeature hkn i h‖ ^ (2 : ℕ)) = ∑ i : Fin (n - k), sq (k + i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hi_lt_n : k + (i : ℕ) < n := by
          omega
        have hcast :
            (Fin.natAdd_castLEEmb (Nat.sub_le n k) i : Fin n) = ⟨k + i, hi_lt_n⟩ := by
          ext
          simp [Fin.natAdd_castLEEmb]
          omega
        simp [tailFeature, sq, hi_lt_n, hcast, Real.norm_eq_abs]
      _ = ∑ j ∈ Finset.range (n - k), sq (k + j) := by
            simpa using (Fin.sum_univ_eq_sum_range (fun j ↦ sq (k + j)) (n - k))
      _ = ∑ i ∈ Finset.Ico k n, sq i := by
            rw [Finset.sum_Ico_eq_sum_range]
  have hnorm :
      ‖h‖ ^ (2 : ℕ) = ∑ i ∈ Finset.range n, sq i := by
    calc
      ‖h‖ ^ (2 : ℕ) = ∑ i : Fin n, (h i) ^ (2 : ℕ) := by
            simpa using EuclideanSpace.real_norm_sq_eq h
      _ = ∑ i : Fin n, sq i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [sq, i.2]
      _ = ∑ i ∈ Finset.range n, sq i := by
            simpa using (Fin.sum_univ_eq_sum_range sq n)
  -- Partition the ambient coordinate square sum into the prefix range and the tail interval.
  have hsplit_range :
      ∑ i ∈ Finset.range n, sq i = ∑ i ∈ Finset.range k, sq i + ∑ i ∈ Finset.Ico k n, sq i := by
    simpa [hpred] using
      (Finset.sum_range_add_sum_Ico sq (positive_branch_prefix_len_le hk hkn)).symm
  rw [hnorm, hsplit_range, hprefix, htail]

/-- Helper for Proposition 4.3.2: the initial-square, edge-square, and terminal-square block is
exactly the Chapter 2 chain quadratic form on the active prefix vector. -/
private theorem positive_k_initial_edge_terminal_sq_eq_chain
    (hk : 0 < k) (hkn : k ≤ n) (h : E) :
    ‖initialFeature hk hkn h‖ ^ (2 : ℕ) +
      (∑ i : Fin (k - 1), ‖edgeFeature hk hkn i h‖ ^ (2 : ℕ)) +
      ‖terminalFeature hk hkn h‖ ^ (2 : ℕ) =
        (positiveBranchPrefix hk hkn h 0) ^ (2 : ℕ) +
          (∑ i : Fin (k - 1),
            (positiveBranchPrefix hk hkn h (Fin.castLE (Nat.le_succ (k - 1)) i) -
                positiveBranchPrefix hk hkn h i.succ) ^ (2 : ℕ)) +
          (positiveBranchPrefix hk hkn h (Fin.last (k - 1))) ^ (2 : ℕ) := by
  -- Route correction: unfold the Chapter 2 chain form on the full active prefix, so the goal
  -- becomes a literal coordinate rewrite on the same prefix vector.
  simp [initialFeature, edgeFeature, terminalFeature, positiveBranchPrefix, Real.norm_eq_abs]

/-- Helper for Proposition 4.3.2: the explicit prefix-chain quadratic form is bounded by
`4 * ‖positiveBranchPrefix hk hkn h‖²`. -/
private theorem positive_k_chain_le_four_mul_prefix_norm_sq
    (hk : 0 < k) (hkn : k ≤ n) (h : E) :
    (positiveBranchPrefix hk hkn h 0) ^ (2 : ℕ) +
        (∑ i : Fin (k - 1),
          (positiveBranchPrefix hk hkn h (Fin.castLE (Nat.le_succ (k - 1)) i) -
              positiveBranchPrefix hk hkn h i.succ) ^ (2 : ℕ)) +
      (positiveBranchPrefix hk hkn h (Fin.last (k - 1))) ^ (2 : ℕ) ≤
        4 * ‖positiveBranchPrefix hk hkn h‖ ^ (2 : ℕ) := by
  let h' : EuclideanSpace ℝ (Fin ((k - 1) + 1)) := positiveBranchPrefix hk hkn h
  -- Each chain edge satisfies the textbook estimate `(a - b)^2 ≤ 2 a^2 + 2 b^2`.
  have hedge :
      ∀ i : Fin (k - 1),
        (h' (Fin.castLE (Nat.le_succ (k - 1)) i) - h' i.succ) ^ (2 : ℕ) ≤
          2 * (h' (Fin.castLE (Nat.le_succ (k - 1)) i)) ^ (2 : ℕ) + 2 * (h' i.succ) ^ (2 : ℕ) := by
    intro i
    nlinarith [sq_nonneg (h' (Fin.castLE (Nat.le_succ (k - 1)) i) + h' i.succ)]
  have hsum_edges :
      (∑ i : Fin (k - 1),
          (h' (Fin.castLE (Nat.le_succ (k - 1)) i) - h' i.succ) ^ (2 : ℕ)) ≤
        ∑ i : Fin (k - 1),
          (2 * (h' (Fin.castLE (Nat.le_succ (k - 1)) i)) ^ (2 : ℕ) +
            2 * (h' i.succ) ^ (2 : ℕ)) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact hedge i
  have hsum_expand :
      (∑ i : Fin (k - 1),
          (2 * (h' (Fin.castLE (Nat.le_succ (k - 1)) i)) ^ (2 : ℕ) + 2 * (h' i.succ) ^ (2 : ℕ))) =
        2 * (∑ i : Fin (k - 1), (h' (Fin.castLE (Nat.le_succ (k - 1)) i)) ^ (2 : ℕ)) +
          2 * (∑ i : Fin (k - 1), (h' i.succ) ^ (2 : ℕ)) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hcast_le :
      (∑ i : Fin (k - 1), (h' (Fin.castLE (Nat.le_succ (k - 1)) i)) ^ (2 : ℕ)) ≤
        ∑ i : Fin ((k - 1) + 1), (h' i) ^ (2 : ℕ) := by
    rw [Fin.sum_univ_castSucc]
    exact le_add_of_nonneg_right (sq_nonneg (h' (Fin.last (k - 1))))
  have hsucc_le :
      (∑ i : Fin (k - 1), (h' i.succ) ^ (2 : ℕ)) ≤
        ∑ i : Fin ((k - 1) + 1), (h' i) ^ (2 : ℕ) := by
    rw [Fin.sum_univ_succ]
    exact le_add_of_nonneg_left (sq_nonneg (h' 0))
  have hcast_eq :
      (∑ i : Fin ((k - 1) + 1), (h' i) ^ (2 : ℕ)) =
        (∑ i : Fin (k - 1), (h' (Fin.castLE (Nat.le_succ (k - 1)) i)) ^ (2 : ℕ)) +
          (h' (Fin.last (k - 1))) ^ (2 : ℕ) := by
    calc
      (∑ i : Fin ((k - 1) + 1), (h' i) ^ (2 : ℕ)) =
          (∑ i : Fin (k - 1), (h' i.castSucc) ^ (2 : ℕ)) + (h' (Fin.last (k - 1))) ^ (2 : ℕ) := by
            rw [Fin.sum_univ_castSucc]
      _ =
          (∑ i : Fin (k - 1), (h' (Fin.castLE (Nat.le_succ (k - 1)) i)) ^ (2 : ℕ)) +
            (h' (Fin.last (k - 1))) ^ (2 : ℕ) := by
            congr 1
  have hsucc_eq :
      (∑ i : Fin ((k - 1) + 1), (h' i) ^ (2 : ℕ)) =
        (h' 0) ^ (2 : ℕ) + (∑ i : Fin (k - 1), (h' i.succ) ^ (2 : ℕ)) := by
    rw [Fin.sum_univ_succ]
  calc
    (positiveBranchPrefix hk hkn h 0) ^ (2 : ℕ) +
        (∑ i : Fin (k - 1),
          (positiveBranchPrefix hk hkn h (Fin.castLE (Nat.le_succ (k - 1)) i) -
              positiveBranchPrefix hk hkn h i.succ) ^ (2 : ℕ)) +
      (positiveBranchPrefix hk hkn h (Fin.last (k - 1))) ^ (2 : ℕ)
        =
          h' 0 ^ (2 : ℕ) +
            (∑ i : Fin (k - 1),
              (h' (Fin.castLE (Nat.le_succ (k - 1)) i) - h' i.succ) ^ (2 : ℕ)) +
            h' (Fin.last (k - 1)) ^ (2 : ℕ) := by
            simp [h']
    _ ≤ 4 * ∑ i : Fin ((k - 1) + 1), (h' i) ^ (2 : ℕ) := by
      nlinarith [hsum_edges, hsum_expand, hcast_eq, hsucc_eq, hcast_le, hsucc_le]
    _ = 4 * ‖positiveBranchPrefix hk hkn h‖ ^ (2 : ℕ) := by
      simp [h', EuclideanSpace.real_norm_sq_eq]

/-- Helper for Proposition 4.3.2: the positive-branch edge, terminal, and tail feature squares
obey the sharp `4 * ‖h‖²` bound from the source chain argument. -/
private theorem positive_k_feature_square_le_four_mul_norm_sq
    (hk : 0 < k) (hkn : k ≤ n) (h : E) :
    (∑ i : Fin (k - 1), ‖edgeFeature hk hkn i h‖ ^ (2 : ℕ)) +
      ‖terminalFeature hk hkn h‖ ^ (2 : ℕ) +
      ∑ i : Fin (n - k), ‖tailFeature hkn i h‖ ^ (2 : ℕ) ≤
        4 * ‖h‖ ^ (2 : ℕ) := by
  have hchain :
      ‖initialFeature hk hkn h‖ ^ (2 : ℕ) +
          (∑ i : Fin (k - 1), ‖edgeFeature hk hkn i h‖ ^ (2 : ℕ)) +
        ‖terminalFeature hk hkn h‖ ^ (2 : ℕ) ≤
        4 * ‖positiveBranchPrefix hk hkn h‖ ^ (2 : ℕ) := by
    -- Rewrite the source block to the Chapter 2 chain form and apply its sharp norm bound.
    rw [positive_k_initial_edge_terminal_sq_eq_chain hk hkn h]
    exact positive_k_chain_le_four_mul_prefix_norm_sq hk hkn h
  have hdrop_initial :
      (∑ i : Fin (k - 1), ‖edgeFeature hk hkn i h‖ ^ (2 : ℕ)) +
          ‖terminalFeature hk hkn h‖ ^ (2 : ℕ) ≤
        4 * ‖positiveBranchPrefix hk hkn h‖ ^ (2 : ℕ) := by
    -- Drop the nonnegative initial square from the left-hand side.
    have hinitial_nonneg : 0 ≤ ‖initialFeature hk hkn h‖ ^ (2 : ℕ) := by positivity
    nlinarith
  have htail_nonneg :
      0 ≤ ∑ i : Fin (n - k), ‖tailFeature hkn i h‖ ^ (2 : ℕ) := by
    -- The tail contribution is again a sum of squares.
    refine Finset.sum_nonneg fun i hi ↦ ?_
    positivity
  -- Add the tail block and use the exact prefix-tail norm decomposition.
  calc
    (∑ i : Fin (k - 1), ‖edgeFeature hk hkn i h‖ ^ (2 : ℕ)) +
        ‖terminalFeature hk hkn h‖ ^ (2 : ℕ) +
        ∑ i : Fin (n - k), ‖tailFeature hkn i h‖ ^ (2 : ℕ)
        ≤ 4 * ‖positiveBranchPrefix hk hkn h‖ ^ (2 : ℕ) +
            ∑ i : Fin (n - k), ‖tailFeature hkn i h‖ ^ (2 : ℕ) := by
          gcongr
    _ ≤ 4 * ‖positiveBranchPrefix hk hkn h‖ ^ (2 : ℕ) +
          4 * ∑ i : Fin (n - k), ‖tailFeature hkn i h‖ ^ (2 : ℕ) := by
          nlinarith
    _ = 4 *
          (‖positiveBranchPrefix hk hkn h‖ ^ (2 : ℕ) +
            ∑ i : Fin (n - k), ‖tailFeature hkn i h‖ ^ (2 : ℕ)) := by
          ring
    _ = 4 * ‖h‖ ^ (2 : ℕ) := by
          rw [← positive_k_prefix_tail_norm_sq_split hk hkn h]

/-- Helper for Proposition 4.3.2: finite sums of gradients add in the expected Euclidean form. -/
private theorem hasGradientAt_finset_sum
    {ι : Type*} (s : Finset ι) {f : ι → E → ℝ} {g : ι → E → E} {x : E}
    (hf : ∀ i ∈ s, HasGradientAt (f i) (g i x) x) :
    HasGradientAt (fun y ↦ Finset.sum s fun i => f i y)
      (Finset.sum s fun i => g i x) x := by
  have hsum :
      HasFDerivAt (fun y ↦ Finset.sum s fun i => f i y)
        (∑ i ∈ s, (InnerProductSpace.toDual ℝ E) (g i x)) x := by
    exact HasFDerivAt.fun_sum fun i hi => (hf i hi).hasFDerivAt
  have hgrad :
      HasGradientAt (fun y ↦ Finset.sum s fun i => f i y)
        ((InnerProductSpace.toDual ℝ E).symm
          (∑ i ∈ s, (InnerProductSpace.toDual ℝ E) (g i x))) x := hsum.hasGradientAt
  convert hgrad using 1
  simp [map_sum]

/-- Helper for Proposition 4.3.2: the Hessian of a sum is the sum of the Hessians once every
summand is `C²`. -/
private theorem hessian_finset_sum
    {ι : Type*} (s : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i ∈ s, ContDiff ℝ 2 (f i)) (x : E) :
    hessian (fun y ↦ Finset.sum s fun i => f i y) x =
      Finset.sum s fun i => hessian (f i) x := by
  have hgrad :
      ∇ (fun y ↦ Finset.sum s fun i => f i y) =
        fun y : E ↦ Finset.sum s fun i => ∇ (f i) y := by
    -- Identify the gradient of the finite sum first so the Hessian becomes a derivative of a sum.
    refine gradient_eq ?_
    intro y
    exact
      hasGradientAt_finset_sum s fun i hi =>
        ((hf i hi).contDiffAt.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).hasGradientAt
  rw [hessian, hgrad]
  calc
    fderiv ℝ (fun y : E ↦ ∑ i ∈ s, ∇ (f i) y) x
        = ∑ i ∈ s, fderiv ℝ (fun y : E ↦ ∇ (f i) y) x := by
            exact fderiv_fun_sum fun i hi =>
              differentiableAt_gradient_of_contDiffAt_two (hf i hi).contDiffAt
    _ = ∑ i ∈ s, hessian (f i) x := by
          simp [hessian]

/-- Helper for Proposition 4.3.2: the quadratic form of the Hessian difference of a finite sum is
the sum of the quadratic forms of the Hessian differences. -/
private theorem inner_hessian_finset_sum_sub_eq
    {ι : Type*} (s : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i ∈ s, ContDiff ℝ 2 (f i)) (x y h : E) :
    inner ℝ ((hessian (fun z ↦ ∑ i ∈ s, f i z) x - hessian (fun z ↦ ∑ i ∈ s, f i z) y) h) h =
      ∑ i ∈ s, inner ℝ ((hessian (f i) x - hessian (f i) y) h) h := by
  rw [hessian_finset_sum s f hf x, hessian_finset_sum s f hf y]
  calc
    inner ℝ (((∑ i ∈ s, hessian (f i) x) - ∑ i ∈ s, hessian (f i) y) h) h
        = inner ℝ ((∑ i ∈ s, (hessian (f i) x) h) - ∑ i ∈ s, (hessian (f i) y) h) h := by
            simp [ContinuousLinearMap.sub_apply]
    _ = inner ℝ (∑ i ∈ s, ((hessian (f i) x) h - (hessian (f i) y) h)) h := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ i ∈ s, inner ℝ ((hessian (f i) x) h - (hessian (f i) y) h) h := by
          rw [sum_inner]
    _ = ∑ i ∈ s, inner ℝ ((hessian (f i) x - hessian (f i) y) h) h := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [ContinuousLinearMap.sub_apply]

/-- Helper for Proposition 4.3.2: the Hessian is linear under addition for globally `C²` scalar
fields. -/
private theorem hessian_add_of_contDiff_two
    {f g : E → ℝ} {x : E} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    hessian (fun y ↦ f y + g y) x = hessian f x + hessian g x := by
  have hgrad :
      ∇ (fun y ↦ f y + g y) = fun y : E ↦ ∇ f y + ∇ g y := by
    -- Identify the gradient of the sum first so Hessian linearity becomes `fderiv_add`.
    refine gradient_eq ?_
    intro y
    have hfgrad : HasGradientAt f (∇ f y) y :=
      (hf.contDiffAt.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).hasGradientAt
    have hggrad : HasGradientAt g (∇ g y) y :=
      (hg.contDiffAt.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).hasGradientAt
    rw [hasGradientAt_iff_hasFDerivAt]
    simpa using hfgrad.hasFDerivAt.add hggrad.hasFDerivAt
  rw [hessian, hgrad]
  change fderiv ℝ ((∇ f) + (∇ g)) x = hessian f x + hessian g x
  rw [fderiv_add
    (differentiableAt_gradient_of_contDiffAt_two (hf.contDiffAt (x := x)))
    (differentiableAt_gradient_of_contDiffAt_two (hg.contDiffAt (x := x)))]

/-- Helper for Proposition 4.3.2: the Hessian is linear under subtraction for globally `C²`
scalar fields. -/
private theorem hessian_sub_of_contDiff_two
    {f g : E → ℝ} {x : E} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    hessian (fun y ↦ f y - g y) x = hessian f x - hessian g x := by
  have hgrad :
      ∇ (fun y ↦ f y - g y) = fun y : E ↦ ∇ f y - ∇ g y := by
    -- The gradient of the difference is the difference of the gradients.
    refine gradient_eq ?_
    intro y
    have hfgrad : HasGradientAt f (∇ f y) y :=
      (hf.contDiffAt.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).hasGradientAt
    have hggrad : HasGradientAt g (∇ g y) y :=
      (hg.contDiffAt.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).hasGradientAt
    rw [hasGradientAt_iff_hasFDerivAt]
    simpa using hfgrad.hasFDerivAt.sub hggrad.hasFDerivAt
  rw [hessian, hgrad]
  change fderiv ℝ ((∇ f) - (∇ g)) x = hessian f x - hessian g x
  rw [fderiv_sub
    (differentiableAt_gradient_of_contDiffAt_two (hf.contDiffAt (x := x)))
    (differentiableAt_gradient_of_contDiffAt_two (hg.contDiffAt (x := x)))]

/-- Helper for Proposition 4.3.2: a scalar continuous linear map has zero Hessian. -/
private theorem hessian_continuousLinearMap_eq_zero
    (A : E →L[ℝ] ℝ) (x : E) :
    hessian (fun y : E ↦ A y) x = 0 := by
  have hgrad :
      ∇ (fun y : E ↦ A y) = fun _ : E ↦ (InnerProductSpace.toDual ℝ E).symm A := by
    -- The gradient of a scalar continuous linear map is the constant Riesz representative.
    refine gradient_eq ?_
    intro y
    rw [hasGradientAt_iff_hasFDerivAt]
    convert A.hasFDerivAt using 1
    ext z
    simp
  -- Differentiate the constant gradient map.
  rw [hessian, hgrad]
  ext h
  simp

/-- Helper for Proposition 4.3.2: every coordinate projection has operator norm at most `1`. -/
private theorem proj_norm_le_one (i : Fin n) :
    ‖(EuclideanSpace.proj i : E →L[ℝ] ℝ)‖ ≤ 1 := by
  -- The coordinate functional is bounded by the ambient Euclidean norm.
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro x
  simpa using abs_apply_le_norm x i

/-- Helper for Proposition 4.3.2: a coordinate-difference functional has operator norm at most
`√2`. -/
private theorem proj_sub_proj_norm_le_sqrt_two (i j : Fin n) :
    ‖(EuclideanSpace.proj i : E →L[ℝ] ℝ) - (EuclideanSpace.proj j : E →L[ℝ] ℝ)‖ ≤ Real.sqrt 2 := by
  -- The sharp coordinate-difference estimate from the source proof is exactly the operator bound.
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro x
  simpa using abs_sub_apply_le_sqrt_two_mul_norm x i j

/-- Helper for Proposition 4.3.2: transporting the scalar cubic through a continuous linear
feature map gives a quadratic-form Hessian-difference bound controlled by the feature norm. -/
private theorem scalarCubic_comp_hessian_sub_quadratic_le
    (A : E →L[ℝ] ℝ) (x y h : E) :
    |inner ℝ
        ((hessian (scalarCubic ∘ A) x - hessian (scalarCubic ∘ A) y) h) h|
      ≤ (2 * ‖A‖ * ‖x - y‖) * ‖A h‖ ^ (2 : ℕ) := by
  have hx :
      inner ℝ (hessian (scalarCubic ∘ A) x h) h =
        inner ℝ (hessian scalarCubic (A x) (A h)) (A h) :=
    hessian_quadratic_form_comp_continuousLinearMap A scalarCubic_contDiff_two x h
  have hy :
      inner ℝ (hessian (scalarCubic ∘ A) y h) h =
        inner ℝ (hessian scalarCubic (A y) (A h)) (A h) :=
    hessian_quadratic_form_comp_continuousLinearMap A scalarCubic_contDiff_two y h
  -- Rewrite the pulled-back Hessian quadratic form on the scalar feature and use the scalar owner.
  have hrewrite :
      inner ℝ ((hessian (scalarCubic ∘ A) x - hessian (scalarCubic ∘ A) y) h) h =
        inner ℝ ((hessian scalarCubic (A x) - hessian scalarCubic (A y)) (A h)) (A h) := by
    rw [ContinuousLinearMap.sub_apply, inner_sub_left, hx, hy, ContinuousLinearMap.sub_apply,
      inner_sub_left]
  rw [hrewrite]
  calc
    |inner ℝ ((hessian scalarCubic (A x) - hessian scalarCubic (A y)) (A h)) (A h)|
        ≤ ‖(hessian scalarCubic (A x) - hessian scalarCubic (A y)) (A h)‖ * ‖A h‖ := by
            exact abs_real_inner_le_norm _ _
    _ ≤ (‖hessian scalarCubic (A x) - hessian scalarCubic (A y)‖ * ‖A h‖) * ‖A h‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm
            (hessian scalarCubic (A x) - hessian scalarCubic (A y)) (A h)
    _ = ‖hessian scalarCubic (A x) - hessian scalarCubic (A y)‖ * ‖A h‖ ^ (2 : ℕ) := by
          ring_nf
    _ ≤ (2 * ‖A x - A y‖) * ‖A h‖ ^ (2 : ℕ) := by
          gcongr
          simpa [scalarCubic] using powerDistance_three_zero_hessian_norm_sub_le (A x) (A y)
    _ ≤ (2 * (‖A‖ * ‖x - y‖)) * ‖A h‖ ^ (2 : ℕ) := by
          gcongr
          simpa [map_sub] using ContinuousLinearMap.le_opNorm A (x - y)
    _ = (2 * ‖A‖ * ‖x - y‖) * ‖A h‖ ^ (2 : ℕ) := by ring

/-- Helper for Proposition 4.3.2: `1 ≤ √2`, used to compare projection norms with the sharp edge
norm bound. -/
private theorem one_le_sqrt_two : (1 : ℝ) ≤ Real.sqrt 2 := by
  have hsq :
      (1 : ℝ) ^ (2 : ℕ) ≤ (Real.sqrt 2) ^ (2 : ℕ) := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ (2 : ℝ))]
    norm_num
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith

/-- Helper for Proposition 4.3.2: the absolute value of a sum of three real numbers is bounded by
the sum of their absolute values. -/
private theorem abs_add_add_le (a b c : ℝ) :
    |a + b + c| ≤ |a| + |b| + |c| := by
  nlinarith [abs_add_le (a + b) c, abs_add_le a b]

/-- Helper for Proposition 4.3.2: on the positive branch, `hessian (fk hkn)` splits into the edge,
terminal, and tail scalar-cubic feature Hessians. -/
private theorem fk_positive_hessian_eq_of_pos
    (hk : 0 < k) (hkn : k ≤ n) (z : E) :
    hessian (fk hkn) z =
      (∑ i : Fin (k - 1),
          hessian (fun w : E ↦ scalarCubic (edgeFeature hk hkn i w)) z) +
        hessian (fun w : E ↦ scalarCubic (terminalFeature hk hkn w)) z +
        ∑ i : Fin (n - k), hessian (fun w : E ↦ scalarCubic (tailFeature hkn i w)) z := by
  let edgeTerm : Fin (k - 1) → E → ℝ := fun i w ↦ scalarCubic (edgeFeature hk hkn i w)
  let terminalTerm : E → ℝ := fun w ↦ scalarCubic (terminalFeature hk hkn w)
  let initialTerm : E → ℝ := fun w ↦ initialFeature hk hkn w
  let tailTerm : Fin (n - k) → E → ℝ := fun i w ↦ scalarCubic (tailFeature hkn i w)
  let edgeSum : E → ℝ := fun w ↦ ∑ i : Fin (k - 1), edgeTerm i w
  let tailSum : E → ℝ := fun w ↦ ∑ i : Fin (n - k), tailTerm i w
  have hedgeCont : ∀ i : Fin (k - 1), ContDiff ℝ 2 (edgeTerm i) := by
    intro i
    -- Each edge term is the scalar cubic transported through one adjacent-difference feature.
    simpa [edgeTerm] using scalarCubic_contDiff_two.comp (edgeFeature hk hkn i).contDiff
  have hterminalCont : ContDiff ℝ 2 terminalTerm := by
    -- The terminal term is the scalar cubic on the last active coordinate.
    simpa [terminalTerm] using scalarCubic_contDiff_two.comp (terminalFeature hk hkn).contDiff
  have hinitialCont : ContDiff ℝ 2 initialTerm := by
    -- The initial feature is linear, hence automatically `C²`.
    simpa [initialTerm] using (initialFeature hk hkn).contDiff
  have htailCont : ∀ i : Fin (n - k), ContDiff ℝ 2 (tailTerm i) := by
    intro i
    -- Each tail term is another scalar cubic feature.
    simpa [tailTerm] using scalarCubic_contDiff_two.comp (tailFeature hkn i).contDiff
  have hedgeSumCont : ContDiff ℝ 2 edgeSum := by
    -- Package the finite edge block into one `C²` function.
    simpa [edgeSum] using ContDiff.sum (s := Finset.univ) fun i hi ↦ hedgeCont i
  have htailSumCont : ContDiff ℝ 2 tailSum := by
    -- Package the finite tail block into one `C²` function.
    simpa [tailSum] using ContDiff.sum (s := Finset.univ) fun i hi ↦ htailCont i
  have hedgeSumHess :
      hessian edgeSum z = ∑ i : Fin (k - 1), hessian (edgeTerm i) z := by
    -- Normalize the edge Hessian block once so later rewrites stay flat.
    simpa [edgeSum] using
      hessian_finset_sum (s := Finset.univ) (f := edgeTerm) (x := z)
        (fun i hi ↦ hedgeCont i)
  have htailSumHess :
      hessian tailSum z = ∑ i : Fin (n - k), hessian (tailTerm i) z := by
    -- The same finite-sum Hessian formula handles the tail block.
    simpa [tailSum] using
      hessian_finset_sum (s := Finset.univ) (f := tailTerm) (x := z)
        (fun i hi ↦ htailCont i)
  let prefixTerm : E → ℝ := fun w ↦ edgeSum w + terminalTerm w
  let nonlinearBody : E → ℝ := fun w ↦ prefixTerm w - initialTerm w
  have hprefixCont : ContDiff ℝ 2 prefixTerm := by
    -- The prefix block is the sum of the edge and terminal nonlinear terms.
    simpa [prefixTerm] using hedgeSumCont.add hterminalCont
  have hbodyCont : ContDiff ℝ 2 nonlinearBody := by
    -- Subtracting the linear initial term preserves `C²`.
    simpa [nonlinearBody] using hprefixCont.sub hinitialCont
  have hsplitTail :
      hessian
          (fun w : E ↦
            (∑ i : Fin (k - 1), edgeTerm i w) + terminalTerm w - initialTerm w +
              ∑ i : Fin (n - k), tailTerm i w) z =
        hessian nonlinearBody z + hessian tailSum z := by
    change hessian (fun w : E ↦ nonlinearBody w + tailSum w) z =
      hessian nonlinearBody z + hessian tailSum z
    simpa using
      hessian_add_of_contDiff_two (f := nonlinearBody) (g := tailSum)
        (hf := hbodyCont) (hg := htailSumCont) (x := z)
  have hsplitInitial :
      hessian nonlinearBody z = hessian prefixTerm z - hessian initialTerm z := by
    change hessian (fun w : E ↦ prefixTerm w - initialTerm w) z =
      hessian prefixTerm z - hessian initialTerm z
    simpa using
      hessian_sub_of_contDiff_two (f := prefixTerm) (g := initialTerm)
        (hf := hprefixCont) (hg := hinitialCont) (x := z)
  have hsplitPrefix :
      hessian prefixTerm z = hessian edgeSum z + hessian terminalTerm z := by
    change hessian (fun w : E ↦ edgeSum w + terminalTerm w) z =
      hessian edgeSum z + hessian terminalTerm z
    simpa using
      hessian_add_of_contDiff_two (f := edgeSum) (g := terminalTerm)
        (hf := hedgeSumCont) (hg := hterminalCont) (x := z)
  rw [fk_eq_scalarCubic_features_of_pos hk hkn]
  calc
    hessian
        (fun w : E ↦
          (∑ i : Fin (k - 1), edgeTerm i w) + terminalTerm w - initialTerm w +
            ∑ i : Fin (n - k), tailTerm i w) z
        =
          hessian nonlinearBody z + hessian tailSum z := hsplitTail
    _ =
          (hessian prefixTerm z - hessian initialTerm z) + hessian tailSum z := by
            rw [hsplitInitial]
    _ =
          ((hessian edgeSum z + hessian terminalTerm z) - hessian initialTerm z) +
            hessian tailSum z := by
            rw [hsplitPrefix]
    _ =
          (∑ i : Fin (k - 1), hessian (edgeTerm i) z) +
            hessian terminalTerm z +
            ∑ i : Fin (n - k), hessian (tailTerm i) z := by
            rw [hedgeSumHess, htailSumHess, hessian_continuousLinearMap_eq_zero
              (initialFeature hk hkn) z]
            simp [sub_eq_add_neg]

/-- Helper for Proposition 4.3.2: on the positive branch, the Hessian quadratic-form difference
splits into the edge, terminal, and tail scalar-cubic feature contributions. -/
private theorem fk_positive_hessian_quadratic_sum_eq
    (hk : 0 < k) (hkn : k ≤ n) (x y h : E) :
    inner ℝ ((hessian (fk hkn) x - hessian (fk hkn) y) h) h =
      (∑ i : Fin (k - 1),
          inner ℝ
            ((hessian (fun z : E ↦ scalarCubic (edgeFeature hk hkn i z)) x -
                hessian (fun z : E ↦ scalarCubic (edgeFeature hk hkn i z)) y) h) h) +
        inner ℝ
          ((hessian (fun z : E ↦ scalarCubic (terminalFeature hk hkn z)) x -
              hessian (fun z : E ↦ scalarCubic (terminalFeature hk hkn z)) y) h) h +
        ∑ i : Fin (n - k),
          inner ℝ
            ((hessian (fun z : E ↦ scalarCubic (tailFeature hkn i z)) x -
                hessian (fun z : E ↦ scalarCubic (tailFeature hkn i z)) y) h) h := by
  let edgeTerm : Fin (k - 1) → E → ℝ := fun i z ↦ scalarCubic (edgeFeature hk hkn i z)
  let terminalTerm : E → ℝ := fun z ↦ scalarCubic (terminalFeature hk hkn z)
  let tailTerm : Fin (n - k) → E → ℝ := fun i z ↦ scalarCubic (tailFeature hkn i z)
  let edgeSum : E → ℝ := fun z ↦ ∑ i : Fin (k - 1), edgeTerm i z
  let tailSum : E → ℝ := fun z ↦ ∑ i : Fin (n - k), tailTerm i z
  have hedgeCont : ∀ i : Fin (k - 1), ContDiff ℝ 2 (edgeTerm i) := by
    intro i
    simpa [edgeTerm] using scalarCubic_contDiff_two.comp (edgeFeature hk hkn i).contDiff
  have hterminalCont : ContDiff ℝ 2 terminalTerm := by
    simpa [terminalTerm] using scalarCubic_contDiff_two.comp (terminalFeature hk hkn).contDiff
  have htailCont : ∀ i : Fin (n - k), ContDiff ℝ 2 (tailTerm i) := by
    intro i
    simpa [tailTerm] using scalarCubic_contDiff_two.comp (tailFeature hkn i).contDiff
  have hedgeSumHess (z : E) :
      hessian edgeSum z = ∑ i : Fin (k - 1), hessian (edgeTerm i) z := by
    simpa [edgeSum] using
      hessian_finset_sum (s := Finset.univ) (f := edgeTerm) (x := z)
        (fun i hi ↦ hedgeCont i)
  have htailSumHess (z : E) :
      hessian tailSum z = ∑ i : Fin (n - k), hessian (tailTerm i) z := by
    simpa [tailSum] using
      hessian_finset_sum (s := Finset.univ) (f := tailTerm) (x := z)
        (fun i hi ↦ htailCont i)
  have hedgeQuadEq :
      inner ℝ
          (((∑ i : Fin (k - 1), hessian (edgeTerm i) x) -
              ∑ i : Fin (k - 1), hessian (edgeTerm i) y) h) h =
        ∑ i : Fin (k - 1), inner ℝ ((hessian (edgeTerm i) x - hessian (edgeTerm i) y) h) h := by
    rw [← hedgeSumHess x, ← hedgeSumHess y]
    simpa [edgeSum] using
      inner_hessian_finset_sum_sub_eq (s := Finset.univ) (f := edgeTerm)
        (hf := fun i hi ↦ hedgeCont i) x y h
  have htailQuadEq :
      inner ℝ
          (((∑ i : Fin (n - k), hessian (tailTerm i) x) -
              ∑ i : Fin (n - k), hessian (tailTerm i) y) h) h =
        ∑ i : Fin (n - k), inner ℝ ((hessian (tailTerm i) x - hessian (tailTerm i) y) h) h := by
    rw [← htailSumHess x, ← htailSumHess y]
    simpa [tailSum] using
      inner_hessian_finset_sum_sub_eq (s := Finset.univ) (f := tailTerm)
        (hf := fun i hi ↦ htailCont i) x y h
  let edgeHx : E →L[ℝ] E := ∑ i : Fin (k - 1), hessian (edgeTerm i) x
  let edgeHy : E →L[ℝ] E := ∑ i : Fin (k - 1), hessian (edgeTerm i) y
  let tailHx : E →L[ℝ] E := ∑ i : Fin (n - k), hessian (tailTerm i) x
  let tailHy : E →L[ℝ] E := ∑ i : Fin (n - k), hessian (tailTerm i) y
  let edgeQuad : Fin (k - 1) → ℝ :=
    fun i ↦ inner ℝ ((hessian (edgeTerm i) x - hessian (edgeTerm i) y) h) h
  let tailQuad : Fin (n - k) → ℝ :=
    fun i ↦ inner ℝ ((hessian (tailTerm i) x - hessian (tailTerm i) y) h) h
  have hdecomp :
      edgeHx + hessian terminalTerm x + tailHx - (edgeHy + hessian terminalTerm y + tailHy) =
        (edgeHx - edgeHy) + (hessian terminalTerm x - hessian terminalTerm y) +
          (tailHx - tailHy) := by
    ext u
    abel_nf
  rw [fk_positive_hessian_eq_of_pos hk hkn x, fk_positive_hessian_eq_of_pos hk hkn y]
  change
    inner ℝ
        ((edgeHx + hessian terminalTerm x + tailHx -
            (edgeHy + hessian terminalTerm y + tailHy)) h)
        h =
      (∑ i : Fin (k - 1), edgeQuad i) +
        inner ℝ ((hessian terminalTerm x - hessian terminalTerm y) h) h +
        ∑ i : Fin (n - k), tailQuad i
  rw [hdecomp]
  calc
    inner ℝ
        (((edgeHx - edgeHy) + (hessian terminalTerm x - hessian terminalTerm y) +
              (tailHx - tailHy)) h) h
        =
          inner ℝ
            ((edgeHx - edgeHy) h) h +
            inner ℝ ((hessian terminalTerm x - hessian terminalTerm y) h) h +
            inner ℝ ((tailHx - tailHy) h) h := by
            rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, inner_add_left,
              inner_add_left]
    _ =
          (∑ i : Fin (k - 1), edgeQuad i) +
            inner ℝ ((hessian terminalTerm x - hessian terminalTerm y) h) h +
            ∑ i : Fin (n - k), tailQuad i := by
            rw [hedgeQuadEq, htailQuadEq]

/-- Helper for Proposition 4.3.2: the pointwise positive-branch Hessian quadratic-form difference
is controlled by the source feature-square estimate. -/
private theorem fk_positive_hessian_quadratic_sub_le_at
    (hk : 0 < k) (hkn : k ≤ n) (x y h : E) :
    |inner ℝ ((hessian (fk hkn) x - hessian (fk hkn) y) h) h|
      ≤ (8 * Real.sqrt 2) * ‖x - y‖ * ‖h‖ ^ (2 : ℕ) := by
  let edgeQuad : Fin (k - 1) → ℝ :=
    fun i ↦
      inner ℝ
        ((hessian (fun z : E ↦ scalarCubic (edgeFeature hk hkn i z)) x -
            hessian (fun z : E ↦ scalarCubic (edgeFeature hk hkn i z)) y) h) h
  let tailQuad : Fin (n - k) → ℝ :=
    fun i ↦
      inner ℝ
        ((hessian (fun z : E ↦ scalarCubic (tailFeature hkn i z)) x -
            hessian (fun z : E ↦ scalarCubic (tailFeature hkn i z)) y) h) h
  have hsumEq := fk_positive_hessian_quadratic_sum_eq hk hkn x y h
  let C : ℝ := 2 * Real.sqrt 2 * ‖x - y‖
  have hC_nonneg : 0 ≤ C := by
    -- All factors in the common coefficient are nonnegative.
    positivity
  have hedgeBound :
      ∀ i : Fin (k - 1),
        |edgeQuad i|
          ≤ C * ‖edgeFeature hk hkn i h‖ ^ (2 : ℕ) := by
    intro i
    have hfeatureNorm :
        ‖edgeFeature hk hkn i‖ ≤ Real.sqrt 2 := by
      -- The adjacent-difference feature is a difference of two coordinate projections.
      simpa [edgeFeature] using
        proj_sub_proj_norm_le_sqrt_two
          (Fin.castLE (positive_branch_prefix_len_le hk hkn) (Fin.castSucc i))
          (Fin.castLE (positive_branch_prefix_len_le hk hkn) i.succ)
    calc
      |edgeQuad i|
          ≤ (2 * ‖edgeFeature hk hkn i‖ * ‖x - y‖) * ‖edgeFeature hk hkn i h‖ ^ (2 : ℕ) := by
            simpa [edgeQuad] using
              scalarCubic_comp_hessian_sub_quadratic_le (edgeFeature hk hkn i) x y h
      _ ≤ (2 * Real.sqrt 2 * ‖x - y‖) * ‖edgeFeature hk hkn i h‖ ^ (2 : ℕ) := by
            gcongr
      _ = C * ‖edgeFeature hk hkn i h‖ ^ (2 : ℕ) := by
            rfl
  have hterminalBound :
      |inner ℝ
          ((hessian (fun z : E ↦ scalarCubic (terminalFeature hk hkn z)) x -
              hessian (fun z : E ↦ scalarCubic (terminalFeature hk hkn z)) y) h) h|
        ≤ C * ‖terminalFeature hk hkn h‖ ^ (2 : ℕ) := by
    have hfeatureNormOne :
        ‖terminalFeature hk hkn‖ ≤ 1 := by
      -- The terminal feature is a single coordinate projection.
      simpa [terminalFeature] using
        proj_norm_le_one
          (Fin.castLE (positive_branch_prefix_len_le hk hkn) (Fin.last (k - 1)))
    have hfeatureNorm :
        ‖terminalFeature hk hkn‖ ≤ Real.sqrt 2 := hfeatureNormOne.trans one_le_sqrt_two
    calc
      |inner ℝ
          ((hessian (fun z : E ↦ scalarCubic (terminalFeature hk hkn z)) x -
              hessian (fun z : E ↦ scalarCubic (terminalFeature hk hkn z)) y) h) h|
          ≤ (2 * ‖terminalFeature hk hkn‖ * ‖x - y‖) *
              ‖terminalFeature hk hkn h‖ ^ (2 : ℕ) := by
            simpa using
              scalarCubic_comp_hessian_sub_quadratic_le (terminalFeature hk hkn) x y h
      _ ≤ (2 * Real.sqrt 2 * ‖x - y‖) * ‖terminalFeature hk hkn h‖ ^ (2 : ℕ) := by
            gcongr
      _ = C * ‖terminalFeature hk hkn h‖ ^ (2 : ℕ) := by
            rfl
  have htailBound :
      ∀ i : Fin (n - k),
        |tailQuad i|
          ≤ C * ‖tailFeature hkn i h‖ ^ (2 : ℕ) := by
    intro i
    have hfeatureNormOne :
        ‖tailFeature hkn i‖ ≤ 1 := by
      -- Every tail feature is again a coordinate projection.
      simpa [tailFeature] using
        proj_norm_le_one (Fin.natAdd_castLEEmb (Nat.sub_le n k) i)
    have hfeatureNorm :
        ‖tailFeature hkn i‖ ≤ Real.sqrt 2 := hfeatureNormOne.trans one_le_sqrt_two
    calc
      |tailQuad i|
          ≤ (2 * ‖tailFeature hkn i‖ * ‖x - y‖) * ‖tailFeature hkn i h‖ ^ (2 : ℕ) := by
            simpa [tailQuad] using
              scalarCubic_comp_hessian_sub_quadratic_le (tailFeature hkn i) x y h
      _ ≤ (2 * Real.sqrt 2 * ‖x - y‖) * ‖tailFeature hkn i h‖ ^ (2 : ℕ) := by
            gcongr
      _ = C * ‖tailFeature hkn i h‖ ^ (2 : ℕ) := by
            rfl
  have htriangle :
      |(∑ i : Fin (k - 1), edgeQuad i) +
            inner ℝ
              ((hessian (fun z : E ↦ scalarCubic (terminalFeature hk hkn z)) x -
                  hessian (fun z : E ↦ scalarCubic (terminalFeature hk hkn z)) y) h) h +
            ∑ i : Fin (n - k), tailQuad i|
        ≤
          (∑ i : Fin (k - 1), |edgeQuad i|) +
            |inner ℝ
                ((hessian (fun z : E ↦ scalarCubic (terminalFeature hk hkn z)) x -
                    hessian (fun z : E ↦ scalarCubic (terminalFeature hk hkn z)) y) h) h| +
            ∑ i : Fin (n - k), |tailQuad i| := by
    have hbase :
        |(∑ i : Fin (k - 1), edgeQuad i) +
              inner ℝ
                ((hessian (fun z : E ↦ scalarCubic (terminalFeature hk hkn z)) x -
                    hessian (fun z : E ↦ scalarCubic (terminalFeature hk hkn z)) y) h) h +
              ∑ i : Fin (n - k), tailQuad i|
          ≤
            |∑ i : Fin (k - 1), edgeQuad i| +
              |inner ℝ
                  ((hessian (fun z : E ↦ scalarCubic (terminalFeature hk hkn z)) x -
                      hessian (fun z : E ↦ scalarCubic (terminalFeature hk hkn z)) y) h) h| +
              |∑ i : Fin (n - k), tailQuad i| := by
      simpa [add_assoc] using
        abs_add_add_le
          (∑ i : Fin (k - 1), edgeQuad i)
          (inner ℝ
            ((hessian (fun z : E ↦ scalarCubic (terminalFeature hk hkn z)) x -
                hessian (fun z : E ↦ scalarCubic (terminalFeature hk hkn z)) y) h) h)
          (∑ i : Fin (n - k), tailQuad i)
    have hedgeAbs :
        |∑ i : Fin (k - 1), edgeQuad i| ≤ ∑ i : Fin (k - 1), |edgeQuad i| := by
      exact Finset.abs_sum_le_sum_abs _ _
    have htailAbs :
        |∑ i : Fin (n - k), tailQuad i| ≤ ∑ i : Fin (n - k), |tailQuad i| := by
      exact Finset.abs_sum_le_sum_abs _ _
    nlinarith
  have htermwise :
      (∑ i : Fin (k - 1), |edgeQuad i|) +
          |inner ℝ
              ((hessian (fun z : E ↦ scalarCubic (terminalFeature hk hkn z)) x -
                  hessian (fun z : E ↦ scalarCubic (terminalFeature hk hkn z)) y) h) h| +
          ∑ i : Fin (n - k), |tailQuad i|
        ≤
          C *
            ((∑ i : Fin (k - 1), ‖edgeFeature hk hkn i h‖ ^ (2 : ℕ)) +
              ‖terminalFeature hk hkn h‖ ^ (2 : ℕ) +
              ∑ i : Fin (n - k), ‖tailFeature hkn i h‖ ^ (2 : ℕ)) := by
    have hedgeSumBound :
        (∑ i : Fin (k - 1), |edgeQuad i|) ≤
          ∑ i : Fin (k - 1), C * ‖edgeFeature hk hkn i h‖ ^ (2 : ℕ) := by
      exact Finset.sum_le_sum fun i hi ↦ hedgeBound i
    have htailSumBound :
        (∑ i : Fin (n - k), |tailQuad i|) ≤
          ∑ i : Fin (n - k), C * ‖tailFeature hkn i h‖ ^ (2 : ℕ) := by
      exact Finset.sum_le_sum fun i hi ↦ htailBound i
    -- Insert the common coefficient `C` into each feature contribution and factor it back out.
    calc
      (∑ i : Fin (k - 1), |edgeQuad i|) +
          |inner ℝ
              ((hessian (fun z : E ↦ scalarCubic (terminalFeature hk hkn z)) x -
                  hessian (fun z : E ↦ scalarCubic (terminalFeature hk hkn z)) y) h) h| +
          ∑ i : Fin (n - k), |tailQuad i|
          ≤
            (∑ i : Fin (k - 1), C * ‖edgeFeature hk hkn i h‖ ^ (2 : ℕ)) +
              C * ‖terminalFeature hk hkn h‖ ^ (2 : ℕ) +
              ∑ i : Fin (n - k), C * ‖tailFeature hkn i h‖ ^ (2 : ℕ) := by
              exact add_le_add (add_le_add hedgeSumBound hterminalBound) htailSumBound
      _ =
            C *
              ((∑ i : Fin (k - 1), ‖edgeFeature hk hkn i h‖ ^ (2 : ℕ)) +
                ‖terminalFeature hk hkn h‖ ^ (2 : ℕ) +
                ∑ i : Fin (n - k), ‖tailFeature hkn i h‖ ^ (2 : ℕ)) := by
              rw [← Finset.mul_sum, ← Finset.mul_sum]
              ring
  -- Combine the decomposition, the termwise feature bounds, and the source chain-energy estimate.
  calc
    |inner ℝ ((hessian (fk hkn) x - hessian (fk hkn) y) h) h|
        =
          |(∑ i : Fin (k - 1), edgeQuad i) +
              inner ℝ
                ((hessian (fun z : E ↦ scalarCubic (terminalFeature hk hkn z)) x -
                    hessian (fun z : E ↦ scalarCubic (terminalFeature hk hkn z)) y) h) h +
              ∑ i : Fin (n - k), tailQuad i| := by
            rw [hsumEq]
    _ ≤
          (∑ i : Fin (k - 1), |edgeQuad i|) +
            |inner ℝ
                ((hessian (fun z : E ↦ scalarCubic (terminalFeature hk hkn z)) x -
                    hessian (fun z : E ↦ scalarCubic (terminalFeature hk hkn z)) y) h) h| +
            ∑ i : Fin (n - k), |tailQuad i| := by
          exact htriangle
    _ ≤
          C *
            ((∑ i : Fin (k - 1), ‖edgeFeature hk hkn i h‖ ^ (2 : ℕ)) +
              ‖terminalFeature hk hkn h‖ ^ (2 : ℕ) +
              ∑ i : Fin (n - k), ‖tailFeature hkn i h‖ ^ (2 : ℕ)) := htermwise
    _ ≤ C * (4 * ‖h‖ ^ (2 : ℕ)) := by
          exact mul_le_mul_of_nonneg_left
            (positive_k_feature_square_le_four_mul_norm_sq hk hkn h) hC_nonneg
    _ = (8 * Real.sqrt 2) * ‖x - y‖ * ‖h‖ ^ (2 : ℕ) := by
          unfold C
          ring

/-- Helper for Proposition 4.3.2: in the positive branch, the Hessian quadratic-form difference is
controlled by the source feature-square estimate. -/
private theorem fk_positive_hessian_quadratic_sub_le
    (hk : 0 < k) (hkn : k ≤ n) :
    ∀ x y h : E,
      |inner ℝ ((hessian (fk hkn) x - hessian (fk hkn) y) h) h|
        ≤ (8 * Real.sqrt 2) * ‖x - y‖ * ‖h‖ ^ (2 : ℕ) := by
  intro x y h
  exact fk_positive_hessian_quadratic_sub_le_at hk hkn x y h

/-- Helper for Proposition 4.3.2: self-adjoint quadratic-form control implies an operator-norm
bound via the Rayleigh quotient. -/
private theorem selfAdjoint_norm_le_of_quadratic_bound
    {T : E →L[ℝ] E} {s : ℝ}
    (hT : (T : E →ₗ[ℝ] E).IsSymmetric)
    (hs : 0 ≤ s)
    (hquad : ∀ u : E, |inner ℝ (T u) u| ≤ s * ‖u‖ ^ (2 : ℕ)) :
    ‖T‖ ≤ s := by
  have hbound : ∀ u : E, |T.rayleighQuotient u| ≤ s := by
    intro u
    by_cases hu : u = 0
    · simpa [hu] using hs
    · have hu_pos : 0 < ‖u‖ ^ (2 : ℕ) := by
        positivity
      rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply, abs_div,
        abs_of_nonneg (by positivity : 0 ≤ ‖u‖ ^ (2 : ℕ))]
      exact (div_le_iff₀ hu_pos).2 (by simpa using hquad u)
  -- The Rayleigh-quotient characterization turns the diagonal bound into an operator bound.
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T hT]
  exact ciSup_le hbound

/-- Helper for Proposition 4.3.2: a `C²` scalar field with a pointwise quadratic-form bound on
Hessian differences is automatically in `C22[...]`. -/
private theorem mem_C22_of_contDiff_two_and_hessian_quadratic_sub_le
    {f : E → ℝ} {L3 : NNReal} (hf : ContDiff ℝ 2 f)
    (hhess : ∀ x y h,
      |inner ℝ ((hessian f x - hessian f y) h) h|
        ≤ (L3 : ℝ) * ‖x - y‖ * ‖h‖ ^ (2 : ℕ)) :
    f ∈ C22[L3] := by
  refine mem_C22_of_contDiff_two_and_hessian_norm_sub_le hf ?_
  intro x y
  have hsymm :
      ((hessian f x - hessian f y : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric := by
    exact
      (hessian_isSelfAdjoint_of_contDiffAt f x (hf.contDiffAt (x := x))).isSymmetric.sub
        (hessian_isSelfAdjoint_of_contDiffAt f y (hf.contDiffAt (x := y))).isSymmetric
  -- Apply the self-adjoint bridge to the Hessian difference operator at `(x,y)`.
  refine selfAdjoint_norm_le_of_quadratic_bound hsymm (by positivity) ?_
  intro h
  simpa using hhess x y h

/-- Proposition 4.3.2: for `k ≤ n`, the hard-instance objective `fk hkn` has globally
`(8 * √2)`-Lipschitz Hessian, recorded on the chapter's canonical `C22[...]` surface. The
degenerate cases `k = 0, 1` are included because the same owner bound still applies there. -/
theorem fk_mem_C22
    (hkn : k ≤ n) :
    fk hkn ∈ C22[⟨8 * Real.sqrt 2, by positivity⟩] := by
  by_cases hk : 0 < k
  · let edgeTerm : Fin (k - 1) → E → ℝ :=
      fun i z ↦ scalarCubic (edgeFeature hk hkn i z)
    let terminalTerm : E → ℝ :=
      fun z ↦ scalarCubic (terminalFeature hk hkn z)
    let tailTerm : Fin (n - k) → E → ℝ :=
      fun i z ↦ scalarCubic (tailFeature hkn i z)
    have hedgeCont : ∀ i : Fin (k - 1), ContDiff ℝ 2 (edgeTerm i) := by
      intro i
      -- Each edge feature is a scalar cubic composed with the adjacent-difference map.
      simpa [edgeTerm] using scalarCubic_contDiff_two.comp (edgeFeature hk hkn i).contDiff
    have hterminalCont : ContDiff ℝ 2 terminalTerm := by
      -- The terminal feature is a scalar cubic composed with the last active prefix projection.
      simpa [terminalTerm] using scalarCubic_contDiff_two.comp (terminalFeature hk hkn).contDiff
    have htailCont : ∀ i : Fin (n - k), ContDiff ℝ 2 (tailTerm i) := by
      intro i
      -- Each tail feature is a scalar cubic composed with the corresponding tail projection.
      simpa [tailTerm] using scalarCubic_contDiff_two.comp (tailFeature hkn i).contDiff
    have hcont : ContDiff ℝ 2 (fk hkn) := by
      -- Route correction: regroup the source edge, terminal, and tail scalar-cubic features into
      -- one nonlinear block and subtract the linear initial feature at the end.
      rw [fk_eq_scalarCubic_features_of_pos hk hkn]
      have hedgeSumCont :
          ContDiff ℝ 2 (fun z : E ↦ ∑ i : Fin (k - 1), edgeTerm i z) := by
        simpa using ContDiff.sum (s := Finset.univ) fun i hi ↦ hedgeCont i
      have htailSumCont :
          ContDiff ℝ 2 (fun z : E ↦ ∑ i : Fin (n - k), tailTerm i z) := by
        simpa using ContDiff.sum (s := Finset.univ) fun i hi ↦ htailCont i
      have hinitialCont : ContDiff ℝ 2 (fun z : E ↦ initialFeature hk hkn z) := by
        simpa using (initialFeature hk hkn).contDiff
      simpa [edgeTerm, terminalTerm, tailTerm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        using ((hedgeSumCont.add hterminalCont).sub hinitialCont).add htailSumCont
    have hhess :
        ∀ x y h : E,
          |inner ℝ ((hessian (fk hkn) x - hessian (fk hkn) y) h) h|
            ≤ (⟨8 * Real.sqrt 2, by positivity⟩ : NNReal) * ‖x - y‖ * ‖h‖ ^ (2 : ℕ) := by
      intro x y h
      simpa using fk_positive_hessian_quadratic_sub_le hk hkn x y h
    -- Package the positive branch into the chapter's `C22[...]` owner.
    exact mem_C22_of_contDiff_two_and_hessian_quadratic_sub_le hcont hhess
  · have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    subst hk0
    let coordTerm : Fin n → E → ℝ :=
      fun i x ↦ scalarCubic ((EuclideanSpace.proj i : E →L[ℝ] ℝ) x)
    have hcoordCont : ∀ i : Fin n, ContDiff ℝ 2 (coordTerm i) := by
      intro i
      -- Each coordinate feature is the scalar cubic precomposed with a continuous linear map.
      simpa [coordTerm] using
        scalarCubic_contDiff_two.comp (EuclideanSpace.proj i).contDiff
    have hfk_eq :
        fk hkn = fun x : E ↦ ∑ i : Fin n, coordTerm i x := by
      -- In the degenerate branch `k = 0`, `fk` is exactly the sum of coordinate cubics.
      ext x
      rw [fk_apply]
      simp [coordTerm, scalarCubic_apply, Finset.mul_sum]
    have hcont : ContDiff ℝ 2 (fk hkn) := by
      -- The degenerate branch is a finite sum of `C²` coordinate features.
      rw [hfk_eq]
      exact ContDiff.sum (s := Finset.univ) fun i hi ↦ hcoordCont i
    have hhess :
        ∀ x y h : E,
          |inner ℝ ((hessian (fk hkn) x - hessian (fk hkn) y) h) h|
            ≤ (⟨8 * Real.sqrt 2, by positivity⟩ : NNReal) * ‖x - y‖ * ‖h‖ ^ (2 : ℕ) := by
      intro x y h
      have hsumEq :
          inner ℝ ((hessian (fk hkn) x - hessian (fk hkn) y) h) h =
            ∑ i : Fin n,
              inner ℝ ((hessian (coordTerm i) x - hessian (coordTerm i) y) h) h := by
        -- Rewrite the degenerate branch Hessian as the finite sum of coordinate Hessians.
        rw [hfk_eq, hessian_finset_sum Finset.univ coordTerm (by intro i hi; exact hcoordCont i) x,
          hessian_finset_sum Finset.univ coordTerm (by intro i hi; exact hcoordCont i) y]
        calc
          inner ℝ
              (((∑ i : Fin n, hessian (coordTerm i) x) -
                  ∑ i : Fin n, hessian (coordTerm i) y) h) h
              = inner ℝ
                  ((∑ i : Fin n, (hessian (coordTerm i) x) h) -
                    ∑ i : Fin n, (hessian (coordTerm i) y) h) h := by
                      simp [ContinuousLinearMap.sub_apply]
          _ = inner ℝ
                (∑ i : Fin n, ((hessian (coordTerm i) x) h - (hessian (coordTerm i) y) h)) h := by
                  rw [Finset.sum_sub_distrib]
          _ =
                ∑ i : Fin n,
                  inner ℝ ((hessian (coordTerm i) x) h - (hessian (coordTerm i) y) h) h := by
                rw [sum_inner]
          _ = ∑ i : Fin n, inner ℝ ((hessian (coordTerm i) x - hessian (coordTerm i) y) h) h := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [ContinuousLinearMap.sub_apply]
      have hterm :
          ∀ i : Fin n,
            |inner ℝ ((hessian (coordTerm i) x - hessian (coordTerm i) y) h) h|
              ≤ (2 : ℝ) * ‖x - y‖ * ‖(EuclideanSpace.proj i : E →L[ℝ] ℝ) h‖ ^ (2 : ℕ) := by
        intro i
        have hA :=
          scalarCubic_comp_hessian_sub_quadratic_le (EuclideanSpace.proj i : E →L[ℝ] ℝ) x y h
        have hproj :
            (2 * ‖(EuclideanSpace.proj i : E →L[ℝ] ℝ)‖ * ‖x - y‖) *
                ‖(EuclideanSpace.proj i : E →L[ℝ] ℝ) h‖ ^ (2 : ℕ)
              ≤ (2 : ℝ) * ‖x - y‖ * ‖(EuclideanSpace.proj i : E →L[ℝ] ℝ) h‖ ^ (2 : ℕ) := by
          have hprojNorm : ‖(EuclideanSpace.proj i : E →L[ℝ] ℝ)‖ ≤ 1 := proj_norm_le_one i
          calc
            (2 * ‖(EuclideanSpace.proj i : E →L[ℝ] ℝ)‖ * ‖x - y‖) *
                ‖(EuclideanSpace.proj i : E →L[ℝ] ℝ) h‖ ^ (2 : ℕ)
                ≤ (2 * 1 * ‖x - y‖) * ‖(EuclideanSpace.proj i : E →L[ℝ] ℝ) h‖ ^ (2 : ℕ) := by
                    gcongr
            _ = (2 : ℝ) * ‖x - y‖ * ‖(EuclideanSpace.proj i : E →L[ℝ] ℝ) h‖ ^ (2 : ℕ) := by
                  ring
        exact hA.trans hproj
      have hproj_sq :
          (∑ i : Fin n, ‖(EuclideanSpace.proj i : E →L[ℝ] ℝ) h‖ ^ (2 : ℕ)) = ‖h‖ ^ (2 : ℕ) := by
        simpa using (EuclideanSpace.real_norm_sq_eq h).symm
      have hmain :
          |inner ℝ ((hessian (fk hkn) x - hessian (fk hkn) y) h) h|
            ≤ (2 : ℝ) * ‖x - y‖ * ‖h‖ ^ (2 : ℕ) := by
        calc
          |inner ℝ ((hessian (fk hkn) x - hessian (fk hkn) y) h) h|
              = |∑ i : Fin n,
                  inner ℝ ((hessian (coordTerm i) x - hessian (coordTerm i) y) h) h| := by
                    rw [hsumEq]
          _ ≤ ∑ i : Fin n,
                |inner ℝ ((hessian (coordTerm i) x - hessian (coordTerm i) y) h) h| := by
                  exact Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i : Fin n,
                (2 : ℝ) * ‖x - y‖ * ‖(EuclideanSpace.proj i : E →L[ℝ] ℝ) h‖ ^ (2 : ℕ) := by
                  exact Finset.sum_le_sum fun i hi => hterm i
          _ = (2 : ℝ) * ‖x - y‖ * ‖h‖ ^ (2 : ℕ) := by
                calc
                  ∑ i : Fin n, (2 : ℝ) * ‖x - y‖ * ‖(EuclideanSpace.proj i : E →L[ℝ] ℝ) h‖ ^ (2 : ℕ)
                      = (2 : ℝ) * ‖x - y‖ *
                          ∑ i : Fin n, ‖(EuclideanSpace.proj i : E →L[ℝ] ℝ) h‖ ^ (2 : ℕ) := by
                            rw [← Finset.mul_sum]
                  _ = (2 : ℝ) * ‖x - y‖ * ‖h‖ ^ (2 : ℕ) := by rw [hproj_sq]
      have hconst :
          (2 : ℝ) * ‖x - y‖ * ‖h‖ ^ (2 : ℕ)
            ≤ ((⟨8 * Real.sqrt 2, by positivity⟩ : NNReal) : ℝ) * ‖x - y‖ * ‖h‖ ^ (2 : ℕ) := by
        have hsqrt :
            (2 : ℝ) ≤ ((⟨8 * Real.sqrt 2, by positivity⟩ : NNReal) : ℝ) := by
          change (2 : ℝ) ≤ 8 * Real.sqrt 2
          have hsqrt_one : (1 : ℝ) ≤ Real.sqrt 2 := by
            have hsq :
                (1 : ℝ) ^ (2 : ℕ) ≤ (Real.sqrt 2) ^ (2 : ℕ) := by
              rw [Real.sq_sqrt (by positivity : 0 ≤ (2 : ℝ))]
              norm_num
            have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
            nlinarith
          nlinarith
        have hfactor_nonneg : 0 ≤ ‖x - y‖ * ‖h‖ ^ (2 : ℕ) := by positivity
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_right hsqrt hfactor_nonneg
      exact hmain.trans hconst
    -- Package the degenerate branch into the chapter's `C22[...]` owner.
    exact mem_C22_of_contDiff_two_and_hessian_quadratic_sub_le hcont hhess

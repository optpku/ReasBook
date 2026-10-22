/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type v} [Fintype ι]

local notation "E₂" => EuclideanSpace ℝ ι

/- Proposition 6.22 lies in the finite-index operator-norm / weighted-Euclidean domain.

Sampled owner declarations:
* `Seminorm.comp`, the canonical owner for transporting a seminorm along a linear map;
* `normSeminorm`, the ambient seminorm owner whose pullback gives the weighted geometry;
* `ContinuousLinearMap.opNorm`, the canonical ambient operator norm on continuous linear maps;
* `ContinuousLinearMap.pi`, the canonical owner for assembling a finite row family into a map to
  `EuclideanSpace ℝ ι`;
* `EuclideanSpace.equiv`, the canonical equivalence between `EuclideanSpace ℝ ι` and coordinate
  functions on `ι`;
* `EuclideanSpace.proj`, the canonical coordinate projections used to build the weighted scaling
  map;
* `operatorNorm_eq_sSup_dualPairing_unitSpheres` in `Chap06/Definition_6_3`, the chapter bridge
  from the canonical operator norm to a source-facing dual-pairing supremum.

Best owner abstraction:
* source-facing: the textbook supremum of `∑ⱼ u_j a_j(x)` over the ambient unit ball in `E` and
  the unit ball of the weighted Euclidean seminorm on `EuclideanSpace ℝ ι`;
* core/canonical: `‖normalizedRowMap a‖`;
* bridge/view: the weighted scaling map `weightedRowScale a`, which transports the weighted
  Euclidean seminorm to the ambient Euclidean norm.

Primitive data:
* the finite row family `a : ι → StrongDual ℝ E`.

Derived API:
* the weighted scaling map on `EuclideanSpace ℝ ι`;
* the normalized row map into `EuclideanSpace ℝ ι`;
* the source-facing weighted Euclidean seminorm, recovered as the pullback of the ambient
  seminorm after weighting;
* the source-facing bridge from the textbook supremum to the canonical operator norm.

Source/core/bridge triage:
* source-facing: `weightedRowEuclideanSeminorm` and Proposition 6.22's weighted-pairing
  supremum;
* core/canonical: `‖normalizedRowMap a‖`;
* bridge/view: `weightedRowScale`, which rewrites the weighted unit ball as an ordinary Euclidean
  unit ball.

The previous `weightedRowOperatorNorm` was a duplicate owner of this bound: it only repackaged the
same supremum into a local `def`. This refinement deletes that duplicate owner, keeps the weighted
seminorm as the source-facing bridge object, routes the inequality through the canonical operator
norm of the normalized row map, and promotes the public finite-family surface from the coordinate
owner `Fin m` to the chapter's canonical owner `[Fintype ι]`.
-/

/-- The diagonal scaling `u_j ↦ √‖a_j‖ u_j` transporting the weighted finite-family geometry to
the ambient Euclidean norm. -/
def weightedRowScale
    (a : ι → StrongDual ℝ E) : E₂ →L[ℝ] E₂ :=
  ((EuclideanSpace.equiv ι ℝ).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi fun j ↦
      Real.sqrt ‖a j‖ • EuclideanSpace.proj j)

omit [Fintype ι] in
/-- The `j`-th coordinate of `weightedRowScale a u` is `√‖a_j‖ u_j`. -/
theorem weightedRowScale_apply
    (a : ι → StrongDual ℝ E) (u : E₂) (j : ι) :
    weightedRowScale a u j = Real.sqrt ‖a j‖ * u j := by
  -- Expand the coordinate map once so later proofs can rewrite coordinates by this theorem.
  simp [weightedRowScale]

/-- The normalized row operator with coordinates
`x ↦ a_j(x) / √‖a_j‖`, interpreted as `0` on zero rows. -/
def normalizedRowMap
    (a : ι → StrongDual ℝ E) : E →L[ℝ] E₂ :=
  ((EuclideanSpace.equiv ι ℝ).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi fun j ↦
      (if ‖a j‖ = 0 then 0 else (Real.sqrt ‖a j‖)⁻¹) • a j)

omit [Fintype ι] in
/-- The `j`-th coordinate of `normalizedRowMap a x` is the normalized row value. -/
theorem normalizedRowMap_apply
    (a : ι → StrongDual ℝ E) (x : E) (j : ι) :
    normalizedRowMap a x j =
      (if ‖a j‖ = 0 then 0 else (Real.sqrt ‖a j‖)⁻¹) * a j x := by
  -- Expand the assembled `pi` map once so later proofs can work coordinatewise.
  by_cases h0 : ‖a j‖ = 0
  · simp [normalizedRowMap, h0]
  · simp [normalizedRowMap, h0]

/-- The weighted Euclidean seminorm on `EuclideanSpace ℝ ι` whose weights are the dual norms of
the rows `a_j`, expressed canonically as the pullback of the ambient seminorm along
`weightedRowScale a`. Zero rows produce zero weights, so the source-facing geometry is generally a
seminorm rather than a norm. -/
def weightedRowEuclideanSeminorm
    (a : ι → StrongDual ℝ E) : Seminorm ℝ E₂ :=
  Seminorm.comp (normSeminorm ℝ E₂) (weightedRowScale a).toLinearMap

/-- Evaluating `weightedRowEuclideanSeminorm a` gives the ambient norm of `weightedRowScale a u`.
-/
theorem weightedRowEuclideanSeminorm_eq_norm_weightedRowScale
    (a : ι → StrongDual ℝ E) (u : E₂) :
    weightedRowEuclideanSeminorm a u = ‖weightedRowScale a u‖ :=
  rfl

-- Proof sketch: expand `weightedRowEuclideanSeminorm` via `weightedRowScale_apply` and then use
-- `EuclideanSpace.norm_eq`.
/-- Applying `weightedRowEuclideanSeminorm a` gives the square root of the weighted quadratic form
`∑ⱼ ‖a_j‖ (u_j)^2`. -/
theorem weightedRowEuclideanSeminorm_apply
    (a : ι → StrongDual ℝ E) (u : E₂) :
    weightedRowEuclideanSeminorm a u =
      Real.sqrt (∑ j : ι, ‖a j‖ * (u j) ^ (2 : ℕ)) := by
  -- Rewrite the pullback seminorm as the ambient Euclidean norm and expand coordinates.
  rw [weightedRowEuclideanSeminorm_eq_norm_weightedRowScale, EuclideanSpace.norm_eq]
  -- Each coordinate contributes `‖a_j‖ * (u_j)^2` after simplifying the square-root weight.
  congr 1
  refine Finset.sum_congr rfl ?_
  intro j hj
  calc
    ‖weightedRowScale a u j‖ ^ 2 = ‖Real.sqrt ‖a j‖ * u j‖ ^ 2 := by
      rw [weightedRowScale_apply]
    _ = (Real.sqrt ‖a j‖) ^ 2 * (u j) ^ (2 : ℕ) := by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, sq_abs, sq_abs]
    _ = ‖a j‖ * (u j) ^ (2 : ℕ) := by
      rw [Real.sq_sqrt (norm_nonneg (a j))]

omit [Fintype ι] in
/-- Helper for Proposition 6.22: zero rows give zero coordinates in `normalizedRowMap a x`. -/
lemma normalizedRowMap_apply_eq_zero_of_rowNorm_eq_zero
    (a : ι → StrongDual ℝ E) (x : E) (j : ι) (h : ‖a j‖ = 0) :
    normalizedRowMap a x j = 0 := by
  -- The zero-weight branch of the normalized map vanishes by definition.
  simp [normalizedRowMap_apply, h]

/-- Helper for Proposition 6.22: on `ℝ`, the inner product is ordinary multiplication. -/
@[simp] private theorem real_inner_eq_mul (s t : ℝ) :
    inner ℝ s t = s * t := by
  -- Rewrite the scalar inner product through the canonical basis vector `1 : ℝ`.
  calc
    inner ℝ s t = inner ℝ (s • (1 : ℝ)) t := by simp
    _ = s * inner ℝ (1 : ℝ) t := by rw [real_inner_smul_left]
    _ = s * t := by
      congr 1
      calc
        inner ℝ (1 : ℝ) t = inner ℝ (1 : ℝ) (t • (1 : ℝ)) := by simp
        _ = t * inner ℝ (1 : ℝ) (1 : ℝ) := by rw [inner_smul_right]
        _ = t := by simp

/-- Helper for Proposition 6.22: the weighted source pairing is the Euclidean inner product between
`weightedRowScale a u` and `normalizedRowMap a x`. -/
lemma weightedRowPairing_eq_inner
    (a : ι → StrongDual ℝ E) (x : E) (u : E₂) :
    ∑ j : ι, u j * a j x =
      inner (𝕜 := ℝ) (weightedRowScale a u) (normalizedRowMap a x) := by
  -- Route correction: rewrite scalar coordinate inner products to multiplication before
  -- cancelling the square-root row factors.
  rw [PiLp.inner_apply]
  -- Each coordinate is handled independently, with a separate zero-row branch.
  refine Finset.sum_congr rfl ?_
  intro j hj
  by_cases h0 : ‖a j‖ = 0
  · -- A zero row contributes `0` on both sides.
    have haj : a j = 0 := norm_eq_zero.mp h0
    simp [weightedRowScale_apply, normalizedRowMap_apply_eq_zero_of_rowNorm_eq_zero a x j h0, haj]
  · -- On a nonzero row, the square-root factor cancels against its inverse.
    have hsqrt_ne : Real.sqrt ‖a j‖ ≠ 0 := (Real.sqrt_ne_zero (norm_nonneg (a j))).2 h0
    rw [weightedRowScale_apply, normalizedRowMap_apply, if_neg h0, real_inner_eq_mul]
    calc
      u j * a j x = (1 : ℝ) * (u j * a j x) := by ring
      _ = (Real.sqrt ‖a j‖ * (Real.sqrt ‖a j‖)⁻¹) * (u j * a j x) := by
        rw [mul_inv_cancel₀ hsqrt_ne]
      _ = (Real.sqrt ‖a j‖ * u j) * ((Real.sqrt ‖a j‖)⁻¹ * a j x) := by ring

/-- Helper for Proposition 6.22: each `‖normalizedRowMap a x‖` is attained by a pairing against a
weighted unit vector. -/
private lemma exists_weightedRowUnit_pairing_eq_norm
    (a : ι → StrongDual ℝ E) (x : E) :
    ∃ u : E₂,
      weightedRowEuclideanSeminorm a u ≤ 1 ∧
        ∑ j : ι, u j * a j x = ‖normalizedRowMap a x‖ := by
  let z : E₂ := normalizedRowMap a x
  let y : E₂ := ‖z‖⁻¹ • z
  let uFun : ι → ℝ := fun j ↦ if ‖a j‖ = 0 then 0 else y j / Real.sqrt ‖a j‖
  let u : E₂ := (EuclideanSpace.equiv ι ℝ).symm uFun
  have hu_scale : weightedRowScale a u = y := by
    -- The coordinatewise witness inverts the row scaling on the support of the nonzero rows.
    ext j
    by_cases h0 : ‖a j‖ = 0
    · have hzj : z j = 0 := by
        simpa [z] using normalizedRowMap_apply_eq_zero_of_rowNorm_eq_zero a x j h0
      simp [weightedRowScale_apply, u, uFun, y, h0, hzj]
    · have hsqrt_ne : Real.sqrt ‖a j‖ ≠ 0 := (Real.sqrt_ne_zero (norm_nonneg (a j))).2 h0
      calc
        weightedRowScale a u j = Real.sqrt ‖a j‖ * (y j / Real.sqrt ‖a j‖) := by
          simp [weightedRowScale_apply, u, uFun, h0]
        _ = y j := by
          rw [div_eq_mul_inv]
          calc
            Real.sqrt ‖a j‖ * (y j * (Real.sqrt ‖a j‖)⁻¹) =
                y j * (Real.sqrt ‖a j‖ * (Real.sqrt ‖a j‖)⁻¹) := by ring
            _ = y j := by rw [mul_inv_cancel₀ hsqrt_ne, mul_one]
  have hy_norm : ‖y‖ ≤ 1 := by
    -- Normalizing `z` yields a vector of norm `1`, except in the degenerate `z = 0` case.
    by_cases hz0 : ‖z‖ = 0
    · simp [y, hz0]
    · calc
        ‖y‖ = ‖z‖⁻¹ * ‖z‖ := by
          simp [y, norm_smul]
        _ = 1 := inv_mul_cancel₀ hz0
        _ ≤ 1 := le_rfl
  have hy_pair : inner (𝕜 := ℝ) y z = ‖z‖ := by
    -- The normalized direction pairs with `z` to recover its norm.
    by_cases hz0 : ‖z‖ = 0
    · have hz : z = 0 := norm_eq_zero.mp hz0
      simp [y, hz]
    · calc
        inner (𝕜 := ℝ) y z = inner (𝕜 := ℝ) (‖z‖⁻¹ • z) z := by rfl
        _ = ‖z‖⁻¹ * inner (𝕜 := ℝ) z z := by rw [real_inner_smul_left]
        _ = ‖z‖⁻¹ * ‖z‖ ^ (2 : ℕ) := by rw [real_inner_self_eq_norm_sq]
        _ = ‖z‖⁻¹ * (‖z‖ * ‖z‖) := by rw [pow_two]
        _ = ‖z‖ := by rw [← mul_assoc, inv_mul_cancel₀ hz0, one_mul]
  refine ⟨u, ?_, ?_⟩
  · -- Transport the weighted seminorm through `weightedRowScale a`.
    calc
      weightedRowEuclideanSeminorm a u = ‖weightedRowScale a u‖ := by
        rw [weightedRowEuclideanSeminorm_eq_norm_weightedRowScale]
      _ = ‖y‖ := by rw [hu_scale]
      _ ≤ 1 := hy_norm
  · -- The pairing bridge converts the source sum into the Euclidean pairing against `y`.
    calc
      ∑ j : ι, u j * a j x = inner (𝕜 := ℝ) (weightedRowScale a u) z := by
        simpa [z] using weightedRowPairing_eq_inner a x u
      _ = inner (𝕜 := ℝ) y z := by rw [hu_scale]
      _ = ‖z‖ := hy_pair
      _ = ‖normalizedRowMap a x‖ := by rfl

omit [Fintype ι] in
/-- Helper for Proposition 6.22: each coordinate of `normalizedRowMap a x` satisfies the
rowwise square estimate `‖normalizedRowMap a x j‖^2 ≤ ‖a j‖ * ‖x‖^2`. -/
private lemma sq_norm_normalizedRowMap_apply_le
    (a : ι → StrongDual ℝ E) (x : E) (j : ι) :
    ‖normalizedRowMap a x j‖ ^ (2 : ℕ) ≤ ‖a j‖ * ‖x‖ ^ (2 : ℕ) := by
  by_cases h0 : ‖a j‖ = 0
  · -- A zero row gives a zero coordinate, so the squared bound is immediate.
    simp [normalizedRowMap_apply_eq_zero_of_rowNorm_eq_zero a x j h0, h0]
  · -- On a nonzero row, divide the operator-norm estimate by the square-root row weight.
    have hsqrt_ne : Real.sqrt ‖a j‖ ≠ 0 := (Real.sqrt_ne_zero (norm_nonneg (a j))).2 h0
    have hcoord :
        ‖normalizedRowMap a x j‖ ≤ Real.sqrt ‖a j‖ * ‖x‖ := by
      calc
        ‖normalizedRowMap a x j‖ = ‖(Real.sqrt ‖a j‖)⁻¹ * a j x‖ := by
          rw [normalizedRowMap_apply, if_neg h0]
        _ = ‖(Real.sqrt ‖a j‖)⁻¹‖ * ‖a j x‖ := by rw [norm_mul]
        _ = (Real.sqrt ‖a j‖)⁻¹ * ‖a j x‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
        _ ≤ (Real.sqrt ‖a j‖)⁻¹ * (‖a j‖ * ‖x‖) := by
          gcongr
          exact (a j).le_opNorm x
        _ = Real.sqrt ‖a j‖ * ‖x‖ := by
          have hrow : ‖a j‖ = Real.sqrt ‖a j‖ * Real.sqrt ‖a j‖ := by
            symm
            exact Real.mul_self_sqrt (norm_nonneg (a j))
          nth_rewrite 2 [hrow]
          calc
            (Real.sqrt ‖a j‖)⁻¹ * ((Real.sqrt ‖a j‖ * Real.sqrt ‖a j‖) * ‖x‖) =
                ((Real.sqrt ‖a j‖)⁻¹ * Real.sqrt ‖a j‖) * (Real.sqrt ‖a j‖ * ‖x‖) := by
              ring
            _ = Real.sqrt ‖a j‖ * ‖x‖ := by rw [inv_mul_cancel₀ hsqrt_ne, one_mul]
    have hsq :
        ‖normalizedRowMap a x j‖ ^ (2 : ℕ) ≤ (Real.sqrt ‖a j‖ * ‖x‖) ^ (2 : ℕ) := by
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).2 hcoord
    simpa [pow_two, Real.sq_sqrt (norm_nonneg (a j)), mul_assoc, mul_left_comm, mul_comm] using
      hsq

-- Proof sketch: write the source supremum as the Euclidean dual pairing between
-- `normalizedRowMap a x` and `weightedRowScale a u`, then identify the supremum over the weighted
-- unit ball with the ordinary operator norm of `normalizedRowMap a`; this is the source-facing
-- specialization of the chapter bridge `operatorNorm_eq_sSup_dualPairing_unitSpheres`.
/-- The textbook weighted-pairing supremum equals the ordinary operator norm of
`normalizedRowMap a`. -/
theorem normalizedRowMap_opNorm_eq_weightedRowPairing_sSup
    (a : ι → StrongDual ℝ E) :
    ‖normalizedRowMap a‖ =
      sSup ((fun xu : E × E₂ ↦ ∑ j : ι, xu.2 j * a j xu.1) ''
        Set.prod {x : E | ‖x‖ ≤ 1}
          {u : E₂ | weightedRowEuclideanSeminorm a u ≤ 1}) := by
  let S : Set ℝ :=
    (fun xu : E × E₂ ↦ ∑ j : ι, xu.2 j * a j xu.1) ''
      Set.prod {x : E | ‖x‖ ≤ 1}
        {u : E₂ | weightedRowEuclideanSeminorm a u ≤ 1}
  let Tset : Set ℝ := (fun x : E ↦ ‖normalizedRowMap a x‖) '' Metric.closedBall (0 : E) 1
  have hS_nonempty : S.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨(0, 0), ?_, by simp⟩
    constructor
    · simp
    · simp [weightedRowEuclideanSeminorm_eq_norm_weightedRowScale]
  have hS_bound : ∀ r ∈ S, r ≤ ‖normalizedRowMap a‖ := by
    intro r hr
    rcases hr with ⟨⟨x, u⟩, hxu, rfl⟩
    rcases hxu with ⟨hx, hu⟩
    have hx' : ‖x‖ ≤ 1 := by simpa using hx
    have hu' : ‖weightedRowScale a u‖ ≤ 1 := by
      simpa [weightedRowEuclideanSeminorm_eq_norm_weightedRowScale] using hu
    -- First bound each source pairing value by the canonical operator norm.
    calc
      ∑ j : ι, u j * a j x =
          inner (𝕜 := ℝ) (weightedRowScale a u) (normalizedRowMap a x) := by
        rw [weightedRowPairing_eq_inner]
      _ ≤ ‖weightedRowScale a u‖ * ‖normalizedRowMap a x‖ := real_inner_le_norm _ _
      _ ≤ 1 * ‖normalizedRowMap a x‖ := by
        gcongr
      _ = ‖normalizedRowMap a x‖ := by ring
      _ ≤ ‖normalizedRowMap a‖ * ‖x‖ := (normalizedRowMap a).le_opNorm x
      _ ≤ ‖normalizedRowMap a‖ * 1 := by
        gcongr
      _ = ‖normalizedRowMap a‖ := by ring
  have hS_bdd : BddAbove S := ⟨‖normalizedRowMap a‖, hS_bound⟩
  have hT_nonempty : Tset.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨0, by simp, by simp⟩
  have hT_le : ∀ r ∈ Tset, r ≤ sSup S := by
    intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    have hx' : ‖x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    obtain ⟨u, hu, hpair⟩ := exists_weightedRowUnit_pairing_eq_norm a x
    have hmem : ∑ j : ι, u j * a j x ∈ S := by
      refine ⟨(x, u), ?_, rfl⟩
      exact ⟨hx', hu⟩
    -- Every norm value on the unit ball is realized by a source pairing witness.
    calc
      ‖normalizedRowMap a x‖ = ∑ j : ι, u j * a j x := by symm; exact hpair
      _ ≤ sSup S := le_csSup hS_bdd hmem
  have hsSup_T_le : sSup Tset ≤ sSup S := csSup_le hT_nonempty hT_le
  have hT_eq : sSup Tset = ‖normalizedRowMap a‖ := by
    simpa [Tset] using ContinuousLinearMap.sSup_unitClosedBall_eq_norm (normalizedRowMap a)
  have hsSup_S_le : sSup S ≤ ‖normalizedRowMap a‖ := csSup_le hS_nonempty hS_bound
  refine le_antisymm ?_ hsSup_S_le
  rw [← hT_eq]
  exact hsSup_T_le

-- Proof sketch: for `‖x‖ ≤ 1`, estimate each coordinate of `normalizedRowMap a x` using
-- `|a_j x| ≤ ‖a_j‖ ‖x‖`; after squaring and summing, the Euclidean norm is bounded by
-- `(∑ⱼ ‖a_j‖)^(1/2)`, and `opNorm_le_bound` finishes.
/-- The canonical operator norm of the normalized row map is bounded by
`(∑ⱼ ‖a_j‖)^(1/2)`. -/
theorem normalizedRowMap_opNorm_le_sqrt_sum_rowNorms
    (a : ι → StrongDual ℝ E) :
    ‖normalizedRowMap a‖ ≤ Real.sqrt (∑ j : ι, ‖a j‖) := by
  have hsum_nonneg : 0 ≤ ∑ j : ι, ‖a j‖ := by
    exact Finset.sum_nonneg fun j _ ↦ norm_nonneg (a j)
  -- Bound the Euclidean norm pointwise by the square root of the total row-norm mass.
  refine ContinuousLinearMap.opNorm_le_bound (normalizedRowMap a) (Real.sqrt_nonneg _) ?_
  intro x
  rw [EuclideanSpace.norm_eq]
  calc
    Real.sqrt (∑ j : ι, ‖normalizedRowMap a x j‖ ^ (2 : ℕ)) ≤
        Real.sqrt (∑ j : ι, ‖a j‖ * ‖x‖ ^ (2 : ℕ)) := by
      apply Real.sqrt_le_sqrt
      gcongr with j
      exact sq_norm_normalizedRowMap_apply_le a x j
    _ = Real.sqrt ((∑ j : ι, ‖a j‖) * ‖x‖ ^ (2 : ℕ)) := by
      rw [Finset.sum_mul]
    _ = Real.sqrt (∑ j : ι, ‖a j‖) * ‖x‖ := by
      rw [Real.sqrt_mul hsum_nonneg, Real.sqrt_sq (norm_nonneg x)]

/-- Proposition 6.22: for the row map with coordinates `x ↦ a_j(x)`, the supremum of
`∑ⱼ u_j a_j(x)` over the ambient unit ball of `E` and the weighted unit ball
of `weightedRowEuclideanSeminorm a` in `EuclideanSpace ℝ ι` is bounded above by
`(∑ⱼ ‖a_j‖)^(1/2)`. -/
theorem weightedRowPairing_sSup_le_sqrt_sum_rowNorms
    (a : ι → StrongDual ℝ E) :
    sSup ((fun xu : E × E₂ ↦ ∑ j : ι, xu.2 j * a j xu.1) ''
      Set.prod {x : E | ‖x‖ ≤ 1}
        {u : E₂ | weightedRowEuclideanSeminorm a u ≤ 1}) ≤
      Real.sqrt (∑ j : ι, ‖a j‖) := by
  let s : Set ℝ :=
    (fun xu : E × E₂ ↦ ∑ j : ι, xu.2 j * a j xu.1) ''
      Set.prod {x : E | ‖x‖ ≤ 1}
        {u : E₂ | weightedRowEuclideanSeminorm a u ≤ 1}
  -- Bound each element of the source-facing supremum set by the operator-norm estimate.
  refine csSup_le ?_ ?_
  · refine ⟨0, ?_⟩
    refine ⟨(0, 0), ?_, by simp⟩
    constructor
    · simp
    · simp [weightedRowEuclideanSeminorm_eq_norm_weightedRowScale]
  · intro r hr
    rcases hr with ⟨⟨x, u⟩, hxu, rfl⟩
    rcases hxu with ⟨hx, hu⟩
    have hx' : ‖x‖ ≤ 1 := by
      simpa using hx
    have hu' : ‖weightedRowScale a u‖ ≤ 1 := by
      simpa [weightedRowEuclideanSeminorm_eq_norm_weightedRowScale] using hu
    calc
      ∑ j : ι, u j * a j x =
          inner (𝕜 := ℝ) (weightedRowScale a u) (normalizedRowMap a x) := by
        rw [weightedRowPairing_eq_inner]
      _ ≤ ‖weightedRowScale a u‖ * ‖normalizedRowMap a x‖ := real_inner_le_norm _ _
      _ ≤ 1 * ‖normalizedRowMap a x‖ := by
        gcongr
      _ = ‖normalizedRowMap a x‖ := by ring
      _ ≤ ‖normalizedRowMap a‖ * ‖x‖ := (normalizedRowMap a).le_opNorm x
      _ ≤ ‖normalizedRowMap a‖ * 1 := by
        gcongr
      _ = ‖normalizedRowMap a‖ := by ring
      _ ≤ Real.sqrt (∑ j : ι, ‖a j‖) := normalizedRowMap_opNorm_le_sqrt_sum_rowNorms a

end

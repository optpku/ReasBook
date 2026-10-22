/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Data.List.TFAE
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Fact_2_26
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_28
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Proposition_3_27
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open ContinuousLinearMap
open scoped InnerProductSpace

variable {𝓗 : Type u} {𝓚 : Type v}
variable [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
variable [NormedAddCommGroup 𝓚] [InnerProductSpace ℝ 𝓚] [CompleteSpace 𝓚]

-- Proof sketch: apply the closed-range theorem to transfer the closedness of `range T` to
-- `range T*`.
/-- If `T` has closed range, then its adjoint also has closed range. -/
theorem adjoint_range_isClosed_of_isClosed_range (T : 𝓗 →L[ℝ] 𝓚)
    (hT_closed : IsClosed (T.range : Set 𝓚)) :
    IsClosed ((adjoint T).range : Set 𝓗) := by
  exact (ContinuousLinearMap.isClosed_range_iff_isClosed_range_adjoint T).mp hT_closed

/-- Helper for Proposition 3.30: when `range T` is closed, the orthogonal complement of `ker T`
is exactly the range of `T*`. -/
lemma orthogonal_ker_eq_adjoint_range (T : 𝓗 →L[ℝ] 𝓚)
    (hT_closed : IsClosed (T.range : Set 𝓚)) :
    T.kerᗮ = (adjoint T).range := by
  -- The abstract orthogonal-kernel identity gives the closure of `range T*`.
  calc
    T.kerᗮ = (adjoint T).range.topologicalClosure := ContinuousLinearMap.orthogonal_ker T
    _ = (adjoint T).range := by
      exact
        (adjoint_range_isClosed_of_isClosed_range T hT_closed).submodule_topologicalClosure_eq

/-- Helper for Proposition 3.30: closed range gives a uniform lower bound for `‖T x‖` on
`(ker T)ᗮ`. -/
private lemma closed_range_lower_bound_on_orthogonal_ker (T : 𝓗 →L[ℝ] 𝓚)
    (hT_closed : IsClosed (T.range : Set 𝓚)) :
    ∃ α > 0, ∀ x ∈ T.kerᗮ, α * ‖x‖ ≤ ‖T x‖ := by
  exact
    (ContinuousLinearMap.isClosed_range_iff_exists_pos_le_norm_of_mem_orthogonal_ker T).mp
      hT_closed

/-- Helper for Proposition 3.30: translating the normal-equation solution set by a chosen
solution identifies it with the kernel of `T`. -/
private lemma mem_moorePenroseSolutionSet_iff_sub_mem_ker (T : 𝓗 →L[ℝ] 𝓚) (y : 𝓚) {z x : 𝓗}
    (hz : z ∈ moorePenroseSolutionSet T y) :
    x ∈ moorePenroseSolutionSet T y ↔ x - z ∈ T.ker := by
  have hz' : adjoint T (T z) = adjoint T y := (mem_moorePenroseSolutionSet_iff T y z).mp hz
  constructor
  · intro hx
    have hsub : adjoint T (T x) - adjoint T (T z) = 0 := by
      rw [((mem_moorePenroseSolutionSet_iff T y x).mp hx), hz', sub_self]
    have hzero : adjoint T (T (x - z)) = 0 := by
      simpa [ContinuousLinearMap.map_sub] using hsub
    have hxker' : x - z ∈ ((adjoint T).comp T).ker := by
      change ((adjoint T).comp T) (x - z) = 0
      simpa using hzero
    have hxker : x - z ∈ T.ker := by
      rw [← ker_adjoint_comp_self]
      exact hxker'
    exact hxker
  · intro hx
    have hxker' : x - z ∈ ((adjoint T).comp T).ker := by
      have hxker : x - z ∈ T.ker := hx
      rw [ker_adjoint_comp_self]
      exact hxker
    have hzero : adjoint T (T (x - z)) = 0 := by
      change ((adjoint T).comp T) (x - z) = 0
      simpa using hxker'
    have hsub : adjoint T (T x) - adjoint T (T z) = 0 := by
      simpa [ContinuousLinearMap.map_sub] using hzero
    have hEq : adjoint T (T x) = adjoint T (T z) := sub_eq_zero.mp hsub
    exact (mem_moorePenroseSolutionSet_iff T y x).mpr (hEq.trans hz')

/-- Helper for Proposition 3.30: every Moore-Penrose inverse value lies in `(ker T)ᗮ`. -/
lemma moorePenroseInverse_mem_orthogonalKer (T : 𝓗 →L[ℝ] 𝓚)
    (hT_closed : IsClosed (T.range : Set 𝓚)) (y : 𝓚) :
    moorePenroseInverse T hT_closed y ∈ T.kerᗮ := by
  let m := moorePenroseInverse T hT_closed y
  have hm_mem : m ∈ moorePenroseSolutionSet T y :=
    moorePenroseInverse_mem_moorePenroseSolutionSet T hT_closed y
  have hm_proj : m = projectionPoint (moorePenroseSolutionSet T y)
      (isChebyshev_moorePenroseSolutionSet T hT_closed y) 0 := by
    rfl
  -- Route correction: use the projection inequality at both `m + k` and `m - k` to force
  -- orthogonality to every kernel vector.
  refine (Submodule.mem_orthogonal' T.ker m).2 ?_
  intro k hk
  have hproj :
      m ∈ moorePenroseSolutionSet T y ∧
        ∀ w ∈ moorePenroseSolutionSet T y, ⟪w - m, 0 - m⟫_ℝ ≤ 0 := by
    exact
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos
        (isChebyshev_moorePenroseSolutionSet T hT_closed y)
        (by
          -- The normal-equation set is affine because the defining equation is linear in `x`.
          intro x hx z hz a b ha hb hab
          rw [mem_moorePenroseSolutionSet_iff] at hx hz ⊢
          calc
            adjoint T (T (a • x + b • z))
                = a • adjoint T (T x) + b • adjoint T (T z) := by simp
            _ = a • adjoint T y + b • adjoint T y := by rw [hx, hz]
            _ = adjoint T y := by rw [← add_smul, hab, one_smul])
        ).mp hm_proj
  have hm_plus : m + k ∈ moorePenroseSolutionSet T y := by
    have hiff : m + k ∈ moorePenroseSolutionSet T y ↔ (m + k) - m ∈ T.ker :=
      mem_moorePenroseSolutionSet_iff_sub_mem_ker T y hm_mem
    exact
      hiff.mpr (by simpa)
  have hm_minus : m - k ∈ moorePenroseSolutionSet T y := by
    have hiff : m - k ∈ moorePenroseSolutionSet T y ↔ (m - k) - m ∈ T.ker :=
      mem_moorePenroseSolutionSet_iff_sub_mem_ker T y hm_mem
    exact
      hiff.mpr (by simpa)
  have hplus : ⟪(m + k) - m, 0 - m⟫_ℝ ≤ 0 := hproj.2 (m + k) hm_plus
  have hminus : ⟪(m - k) - m, 0 - m⟫_ℝ ≤ 0 := hproj.2 (m - k) hm_minus
  have hge : 0 ≤ ⟪k, m⟫_ℝ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, zero_sub, inner_neg_right] using
      hplus
  have hle : ⟪k, m⟫_ℝ ≤ 0 := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, zero_sub, inner_neg_right] using
      hminus
  have hEq : ⟪m, k⟫_ℝ = 0 := by
    have hEq' : ⟪k, m⟫_ℝ = 0 := le_antisymm hle hge
    simpa [real_inner_comm] using hEq'
  exact hEq

-- Proof sketch: identify the normal-equation solution set with an affine translate of `ker T`,
-- then use the projection characterization of the minimal-norm point to show that the unique point
-- lying in `(ker T)ᗮ` is `moorePenroseInverse T hT_closed y`.
/-- Proposition 3.30 (1): among the solutions of the normal equation `T* (T x) = T* y`, the unique
one orthogonal to `ker T` is `moorePenroseInverse T hT_closed y`. -/
theorem moorePenroseSolutionSet_inter_orthogonalKer_eq_singleton (T : 𝓗 →L[ℝ] 𝓚)
    (hT_closed : IsClosed (T.range : Set 𝓚)) (y : 𝓚) :
    moorePenroseSolutionSet T y ∩ (T.kerᗮ : Set 𝓗) = {moorePenroseInverse T hT_closed y} := by
  let m := moorePenroseInverse T hT_closed y
  have hm_mem : m ∈ moorePenroseSolutionSet T y :=
    moorePenroseInverse_mem_moorePenroseSolutionSet T hT_closed y
  have hm_orth : m ∈ T.kerᗮ := moorePenroseInverse_mem_orthogonalKer T hT_closed y
  ext x
  constructor
  · rintro ⟨hx_mem, hx_orth⟩
    -- The translate description turns both solution-set points into a kernel difference.
    have hsub_ker : x - m ∈ T.ker :=
      (show x ∈ moorePenroseSolutionSet T y ↔ x - m ∈ T.ker from
        mem_moorePenroseSolutionSet_iff_sub_mem_ker T y hm_mem).mp hx_mem
    have hsub_orth : x - m ∈ T.kerᗮ := Submodule.sub_mem T.kerᗮ hx_orth hm_orth
    have hzero : x - m = 0 := by
      have hinner : ⟪x - m, x - m⟫_ℝ = 0 :=
        (Submodule.mem_orthogonal' T.ker (x - m)).mp hsub_orth (x - m) hsub_ker
      exact inner_self_eq_zero.mp hinner
    exact Set.mem_singleton_iff.mpr (sub_eq_zero.mp hzero)
  · intro hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact ⟨hm_mem, hm_orth⟩

-- Proof sketch: apply the least-squares characterization of `moorePenroseInverse T hT_closed y`
-- and the projection theorem for the closed subspace `range T`.
/-- Proposition 3.30 (2): applying `T` to the Moore-Penrose inverse of `y` gives the metric
projection of `y` onto `range T`. -/
theorem apply_moorePenroseInverse_eq_rangeProjection (T : 𝓗 →L[ℝ] 𝓚)
    (hT_closed : IsClosed (T.range : Set 𝓚)) (y : 𝓚) :
    T (moorePenroseInverse T hT_closed y) = closedRangeProjection T hT_closed y := by
  -- Proposition 3.27 identifies the normal equation with the orthogonal projection equation.
  have htfae :=
    (leastSquares_tfae_and_exists_of_closed_range T hT_closed y).2
      (moorePenroseInverse T hT_closed y)
  exact
    (List.TFAE.out htfae 2 1).mp (moorePenroseInverse_normalEquation T hT_closed y)

-- Proof sketch: combine the orthogonal decomposition `𝓗 = ker T ⊕ (ker T)ᗮ` with the projection
-- identity for the orthogonal complement, and rewrite `(ker T)ᗮ` as `range T*` using the
-- closed-range theorem for adjoints.
/-- Proposition 3.30 (3): the orthogonal projection onto `ker T` is the map
`x ↦ x - T* ((T*)^† x)`. -/
theorem kerProjection_eq_sub_adjoint_adjointMoorePenroseInverse (T : 𝓗 →L[ℝ] 𝓚)
    (hT_closed : IsClosed (T.range : Set 𝓚)) (x : 𝓗) :
    T.ker.starProjection x =
      x - (adjoint T)
        (moorePenroseInverse (adjoint T)
          (adjoint_range_isClosed_of_isClosed_range T hT_closed) x) := by
  have hstar :
      T.ker.starProjection x = x - T.kerᗮ.starProjection x := by
    -- The orthogonal decomposition of `x` splits off the kernel component.
    have horth : T.kerᗮ.starProjection x = x - T.ker.starProjection x :=
      T.ker.starProjection_orthogonal_val x
    simpa [sub_eq_add_neg, add_comm] using
      congrArg (fun z ↦ x - z) horth
  have hadj :
      T.kerᗮ.starProjection x =
        (adjoint T)
          (moorePenroseInverse (adjoint T)
            (adjoint_range_isClosed_of_isClosed_range T hT_closed) x) := by
    -- Route correction: identify the orthogonal-complement projection with the adjoint-side
    -- range projector before inserting the Moore-Penrose formula.
    calc
      T.kerᗮ.starProjection x = closedRangeProjection (adjoint T)
          (adjoint_range_isClosed_of_isClosed_range T hT_closed) x := by
            have hAdj_closed : IsClosed (((adjoint T).range : Set 𝓗)) :=
              adjoint_range_isClosed_of_isClosed_range T hT_closed
            letI : CompleteSpace (adjoint T).range := hAdj_closed.completeSpace_coe
            simp [closedRangeProjection, orthogonal_ker_eq_adjoint_range T hT_closed]
      _ = (adjoint T)
            (moorePenroseInverse (adjoint T)
              (adjoint_range_isClosed_of_isClosed_range T hT_closed) x) := by
            symm
            exact
              apply_moorePenroseInverse_eq_rangeProjection (adjoint T)
                (adjoint_range_isClosed_of_isClosed_range T hT_closed) x
  -- Rewrite the orthogonal complement projector via the adjoint Moore-Penrose formula.
  calc
    T.ker.starProjection x = x - T.kerᗮ.starProjection x := hstar
    _ = x - (adjoint T)
          (moorePenroseInverse (adjoint T)
            (adjoint_range_isClosed_of_isClosed_range T hT_closed) x) := by rw [hadj]

-- Proof sketch: use part (1) to prove additivity and homogeneity, then use the closed-range lower
-- bound on `(ker T)ᗮ` together with part (2) to obtain the norm estimate.
/-- Proposition 3.30 (4): the Moore-Penrose inverse of a closed-range operator is a bounded linear
map. -/
theorem isBoundedLinearMap_moorePenroseInverse (T : 𝓗 →L[ℝ] 𝓚)
    (hT_closed : IsClosed (T.range : Set 𝓚)) :
    IsBoundedLinearMap ℝ (moorePenroseInverse T hT_closed) := by
  have hadd :
      ∀ y₁ y₂ : 𝓚,
        moorePenroseInverse T hT_closed (y₁ + y₂) =
          moorePenroseInverse T hT_closed y₁ + moorePenroseInverse T hT_closed y₂ := by
    intro y₁ y₂
    have hsol :
        moorePenroseInverse T hT_closed y₁ + moorePenroseInverse T hT_closed y₂ ∈
          moorePenroseSolutionSet T (y₁ + y₂) := by
      -- The normal equation is linear in the right-hand side.
      rw [mem_moorePenroseSolutionSet_iff]
      calc
        adjoint T
            (T (moorePenroseInverse T hT_closed y₁ + moorePenroseInverse T hT_closed y₂)) =
            adjoint T (T (moorePenroseInverse T hT_closed y₁)) +
              adjoint T (T (moorePenroseInverse T hT_closed y₂)) := by
              simp
        _ = adjoint T y₁ + adjoint T y₂ := by
              rw [moorePenroseInverse_normalEquation T hT_closed y₁,
                moorePenroseInverse_normalEquation T hT_closed y₂]
        _ = adjoint T (y₁ + y₂) := by simp
    have horth :
        moorePenroseInverse T hT_closed y₁ + moorePenroseInverse T hT_closed y₂ ∈ T.kerᗮ := by
      -- The orthogonal complement of the kernel is a linear subspace.
      exact Submodule.add_mem T.kerᗮ
        (moorePenroseInverse_mem_orthogonalKer T hT_closed y₁)
        (moorePenroseInverse_mem_orthogonalKer T hT_closed y₂)
    have hmem :
        moorePenroseInverse T hT_closed y₁ + moorePenroseInverse T hT_closed y₂ ∈
          ({moorePenroseInverse T hT_closed (y₁ + y₂)} : Set 𝓗) := by
      rw [← moorePenroseSolutionSet_inter_orthogonalKer_eq_singleton T hT_closed (y₁ + y₂)]
      exact ⟨hsol, horth⟩
    exact (Set.mem_singleton_iff.mp hmem).symm
  have hsmul :
      ∀ (a : ℝ) (y : 𝓚),
        moorePenroseInverse T hT_closed (a • y) = a • moorePenroseInverse T hT_closed y := by
    intro a y
    have hsol :
        a • moorePenroseInverse T hT_closed y ∈ moorePenroseSolutionSet T (a • y) := by
      -- Scalar multiplication respects the normal equation as well.
      rw [mem_moorePenroseSolutionSet_iff]
      calc
        adjoint T (T (a • moorePenroseInverse T hT_closed y)) =
            a • adjoint T (T (moorePenroseInverse T hT_closed y)) := by
              simp
        _ = a • adjoint T y := by
              rw [moorePenroseInverse_normalEquation T hT_closed y]
        _ = adjoint T (a • y) := by simp
    have horth : a • moorePenroseInverse T hT_closed y ∈ T.kerᗮ := by
      -- The orthogonal complement is closed under scalar multiplication.
      exact Submodule.smul_mem T.kerᗮ a
        (moorePenroseInverse_mem_orthogonalKer T hT_closed y)
    have hmem :
        a • moorePenroseInverse T hT_closed y ∈
          ({moorePenroseInverse T hT_closed (a • y)} : Set 𝓗) := by
      rw [← moorePenroseSolutionSet_inter_orthogonalKer_eq_singleton T hT_closed (a • y)]
      exact ⟨hsol, horth⟩
    exact (Set.mem_singleton_iff.mp hmem).symm
  have hlinear : IsLinearMap ℝ (moorePenroseInverse T hT_closed) := by
    -- Clause (i) turns the Moore-Penrose selection into a linear map.
    exact ⟨hadd, hsmul⟩
  rcases closed_range_lower_bound_on_orthogonal_ker T hT_closed with ⟨α, hαpos, hα⟩
  refine IsLinearMap.with_bound hlinear α⁻¹ ?_
  intro y
  have hlower :
      α * ‖moorePenroseInverse T hT_closed y‖ ≤
        ‖T (moorePenroseInverse T hT_closed y)‖ := by
    -- The lower bound applies because each Moore-Penrose inverse value lies in `(ker T)ᗮ`.
    exact hα (moorePenroseInverse T hT_closed y)
      (moorePenroseInverse_mem_orthogonalKer T hT_closed y)
  have hproj_norm :
      ‖T (moorePenroseInverse T hT_closed y)‖ ≤ ‖y‖ := by
    -- Part (ii) identifies `T (T† y)` with the range projection, and that projector is a
    -- contraction.
    calc
      ‖T (moorePenroseInverse T hT_closed y)‖ = ‖closedRangeProjection T hT_closed y‖ := by
        rw [apply_moorePenroseInverse_eq_rangeProjection T hT_closed y]
      _ ≤ ‖closedRangeProjection T hT_closed‖ * ‖y‖ := by
        exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖y‖ := by
        gcongr
        letI : CompleteSpace T.range := hT_closed.completeSpace_coe
        simpa [closedRangeProjection] using T.range.starProjection_norm_le
      _ = ‖y‖ := by simp
  have hbound0 : α * ‖moorePenroseInverse T hT_closed y‖ ≤ ‖y‖ := hlower.trans hproj_norm
  have hbound1 : ‖moorePenroseInverse T hT_closed y‖ ≤ ‖y‖ / α := by
    rw [le_div_iff₀ hαpos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbound0
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hbound1

/-- The Moore-Penrose inverse of a closed-range operator, bundled as a bounded linear operator. -/
noncomputable abbrev moorePenroseInverseOperator (T : 𝓗 →L[ℝ] 𝓚)
    (hT_closed : IsClosed (T.range : Set 𝓚)) : 𝓚 →L[ℝ] 𝓗 :=
  IsBoundedLinearMap.toContinuousLinearMap (moorePenroseInverse T hT_closed)
    (isBoundedLinearMap_moorePenroseInverse T hT_closed)

/- The textbook Moore-Penrose inverse notation `T⁺` keeps the closed-range witness explicit in
Lean as `T⁺[hT_closed]`. -/
scoped[ContinuousLinearMap] notation:max T:max "⁺[" hT_closed:max "]" =>
  moorePenroseInverseOperator T hT_closed

@[simp] theorem moorePenroseInverseOperator_apply (T : 𝓗 →L[ℝ] 𝓚)
    (hT_closed : IsClosed (T.range : Set 𝓚)) (y : 𝓚) :
    moorePenroseInverseOperator T hT_closed y = moorePenroseInverse T hT_closed y :=
  rfl

-- Proof sketch: part (1) places every value of `moorePenroseInverse T hT_closed` in
-- `(ker T)ᗮ`, and the closed-range theorem identifies `(ker T)ᗮ` with `range T*`; conversely, a
-- vector in `range T*` solves the normal equation for a suitable right-hand side.
/-- Proposition 3.30 (5): the range of the Moore-Penrose inverse of `T` is the range of the
adjoint operator `T*`. -/
theorem range_moorePenroseInverse_eq_adjoint_range (T : 𝓗 →L[ℝ] 𝓚)
    (hT_closed : IsClosed (T.range : Set 𝓚)) :
    Set.range (moorePenroseInverse T hT_closed) = ((adjoint T).range : Set 𝓗) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    -- Every Moore-Penrose inverse value lies in `(ker T)ᗮ = range T*`.
    simpa [orthogonal_ker_eq_adjoint_range T hT_closed] using
      (moorePenroseInverse_mem_orthogonalKer T hT_closed y)
  · intro hx
    -- Conversely, a point in `range T*` is the unique orthogonal solution for `y = T x`.
    refine ⟨T x, ?_⟩
    have hxorth : x ∈ T.kerᗮ := by
      simpa [orthogonal_ker_eq_adjoint_range T hT_closed] using hx
    have hxsol : x ∈ moorePenroseSolutionSet T (T x) := by
      rw [mem_moorePenroseSolutionSet_iff]
    have hmem : x ∈ ({moorePenroseInverse T hT_closed (T x)} : Set 𝓗) := by
      rw [← moorePenroseSolutionSet_inter_orthogonalKer_eq_singleton T hT_closed (T x)]
      exact ⟨hxsol, hxorth⟩
    exact (Set.mem_singleton_iff.mp hmem).symm

-- Proof sketch: combine part (2) with the closed-range orthogonal decomposition and part (5) to
-- show that `x ↦ moorePenroseInverse T hT_closed (T x)` is the metric projection onto
-- `range T* = range (moorePenroseInverse T hT_closed)`.
/-- Proposition 3.30 (6): composing `moorePenroseInverse T hT_closed` with `T` gives the metric
projection onto `range T*`, equivalently onto the range of `moorePenroseInverse T hT_closed`. -/
theorem apply_moorePenroseInverse_comp_eq_adjointRangeProjection (T : 𝓗 →L[ℝ] 𝓚)
    (hT_closed : IsClosed (T.range : Set 𝓚)) (x : 𝓗) :
    moorePenroseInverse T hT_closed (T x) =
      closedRangeProjection (adjoint T)
        (adjoint_range_isClosed_of_isClosed_range T hT_closed) x := by
  have hproj_mem :
      closedRangeProjection (adjoint T)
          (adjoint_range_isClosed_of_isClosed_range T hT_closed) x ∈
        ((adjoint T).range : Set 𝓗) := by
    -- The adjoint-range projection lands in the adjoint range by construction.
    exact
      closedRangeProjection_mem_range (adjoint T)
        (adjoint_range_isClosed_of_isClosed_range T hT_closed) x
  have horth :
      closedRangeProjection (adjoint T)
          (adjoint_range_isClosed_of_isClosed_range T hT_closed) x ∈ T.kerᗮ := by
    -- Rewrite `range T*` as `(ker T)ᗮ`.
    simpa [orthogonal_ker_eq_adjoint_range T hT_closed] using hproj_mem
  have hker_mem : T.ker.starProjection x ∈ T.ker := by
    exact Submodule.starProjection_apply_mem T.ker x
  have hres :
      x - closedRangeProjection (adjoint T)
          (adjoint_range_isClosed_of_isClosed_range T hT_closed) x ∈ T.ker := by
    -- Route correction: use clause (iii) to identify the residual with the kernel projection.
    have hker_eq :
        T.ker.starProjection x =
          x - closedRangeProjection (adjoint T)
            (adjoint_range_isClosed_of_isClosed_range T hT_closed) x := by
      calc
        T.ker.starProjection x = x - (adjoint T)
            (moorePenroseInverse (adjoint T)
              (adjoint_range_isClosed_of_isClosed_range T hT_closed) x) := by
                exact
                  kerProjection_eq_sub_adjoint_adjointMoorePenroseInverse T hT_closed x
        _ = x - closedRangeProjection (adjoint T)
              (adjoint_range_isClosed_of_isClosed_range T hT_closed) x := by
                rw [apply_moorePenroseInverse_eq_rangeProjection (adjoint T)
                  (adjoint_range_isClosed_of_isClosed_range T hT_closed) x]
    simpa [hker_eq] using hker_mem
  have hproj_eq :
      T
          (closedRangeProjection (adjoint T)
            (adjoint_range_isClosed_of_isClosed_range T hT_closed) x) = T x := by
    -- A residual in the kernel means the projection has the same image under `T`.
    have hzero :
        T
            (x - closedRangeProjection (adjoint T)
              (adjoint_range_isClosed_of_isClosed_range T hT_closed) x) = 0 := hres
    have hsub :
        T x -
            T
              (closedRangeProjection (adjoint T)
                (adjoint_range_isClosed_of_isClosed_range T hT_closed) x) = 0 := by
      simpa [ContinuousLinearMap.map_sub] using hzero
    exact (sub_eq_zero.mp hsub).symm
  have hsol :
      closedRangeProjection (adjoint T)
          (adjoint_range_isClosed_of_isClosed_range T hT_closed) x ∈
        moorePenroseSolutionSet T (T x) := by
    -- Matching `T`-images gives the normal equation for `y = T x`.
    rw [mem_moorePenroseSolutionSet_iff]
    rw [hproj_eq]
  have hmem :
      closedRangeProjection (adjoint T)
          (adjoint_range_isClosed_of_isClosed_range T hT_closed) x ∈
        ({moorePenroseInverse T hT_closed (T x)} : Set 𝓗) := by
    rw [← moorePenroseSolutionSet_inter_orthogonalKer_eq_singleton T hT_closed (T x)]
    exact ⟨hsol, horth⟩
  exact (Set.mem_singleton_iff.mp hmem).symm

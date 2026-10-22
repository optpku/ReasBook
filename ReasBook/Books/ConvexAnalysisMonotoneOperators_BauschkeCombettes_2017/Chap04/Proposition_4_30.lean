/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_45
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_51
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Corollary_4_28
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_4

open SubtypeFirmness

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Function Set
open scoped InnerProductSpace Topology

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The open unit interval `]0,1[` indexing the approximating curve. -/
private abbrev OpenUnitInterval : Type :=
  Set.Ioo (0 : ℝ) 1

/-- The filter corresponding to the limit `ε ↓ 0` along `]0,1[`. -/
private def openUnitIntervalZeroRightFilter : Filter OpenUnitInterval :=
  Filter.comap (fun ε : OpenUnitInterval ↦ (ε : ℝ)) (𝓝[>] (0 : ℝ))

-- Proof sketch: use convexity of `D` with coefficients `ε` and `1 - ε`, noting that both are
-- nonnegative and sum to `1`, while `x` and `T z` both belong to `D`.
/-- The affine combination `εx + (1 - ε)Tz` stays in `D`. -/
private theorem approximatingAffineMap_mem {D : Set H} (hD_convex : Convex ℝ D) (T : D → D)
    (ε : OpenUnitInterval) (x z : D) :
    (ε : ℝ) • (x : H) + (1 - (ε : ℝ)) • (T z : H) ∈ D := by
  -- Route correction: realize the affine combination as a line-map point of the segment
  -- joining `T z` and `x`, then invoke convexity of `D`.
  have hline : (AffineMap.lineMap (T z : H) (x : H)) (ε : ℝ) ∈ D :=
    hD_convex.lineMap_mem (T z).2 x.2 ⟨le_of_lt ε.2.1, le_of_lt ε.2.2⟩
  simpa [AffineMap.lineMap_apply, sub_eq_add_neg, smul_sub, add_smul, one_smul, add_assoc,
    add_left_comm, add_comm] using hline

/-- The affine contraction `z ↦ εx + (1 - ε)Tz` used to define the approximating curve. -/
private def approximatingAffineMap {D : Set H} (hD_convex : Convex ℝ D) (T : D → D)
    (ε : OpenUnitInterval) (x : D) : D → D :=
  fun z ↦
    ⟨(ε : ℝ) • (x : H) + (1 - (ε : ℝ)) • (T z : H),
      approximatingAffineMap_mem hD_convex T ε x z⟩

-- Proof sketch: the constant part contributes no Lipschitz growth, while the `T` part contributes
-- the factor `1 - ε`; combine this with `T` being nonexpansive and `0 < 1 - ε < 1`.
/-- The affine map defining the approximating curve is a contraction on `D`. -/
private theorem approximatingAffineMap_contracting {D : Set H} (hD_convex : Convex ℝ D) (T : D → D)
    (hT : LipschitzWith 1 T) (ε : OpenUnitInterval) (x : D) :
    ContractingWith (Real.toNNReal (1 - (ε : ℝ))) (approximatingAffineMap hD_convex T ε x) :=
  by
  have hε_nonneg : 0 ≤ 1 - (ε : ℝ) := sub_nonneg.mpr (le_of_lt ε.2.2)
  refine ⟨?_, ?_⟩
  · -- The contraction factor is strictly below `1` because `ε > 0`.
    rw [← NNReal.coe_lt_coe, NNReal.coe_one, Real.coe_toNNReal', max_eq_left hε_nonneg]
    simpa using sub_lt_self (1 : ℝ) ε.2.1
  · refine LipschitzWith.of_dist_le_mul ?_
    intro z w
    have hzw : ‖(T z : H) - (T w : H)‖ ≤ dist z w := by
      simpa [Subtype.dist_eq, dist_eq_norm] using hT.dist_le_mul z w
    -- The common affine term cancels, leaving the scaled nonexpansive difference.
    calc
      dist (approximatingAffineMap hD_convex T ε x z) (approximatingAffineMap hD_convex T ε x w) =
          ‖(1 - (ε : ℝ)) • ((T z : H) - (T w : H))‖ := by
            simp [approximatingAffineMap, Subtype.dist_eq, dist_eq_norm, sub_eq_add_neg, smul_sub,
              add_assoc, add_left_comm, add_comm]
      _ = (1 - (ε : ℝ)) * ‖(T z : H) - (T w : H)‖ := by
        rw [norm_smul, Real.norm_of_nonneg hε_nonneg]
      _ ≤ (1 - (ε : ℝ)) * dist z w := by
        exact mul_le_mul_of_nonneg_left hzw hε_nonneg
      _ = (Real.toNNReal (1 - (ε : ℝ))) * dist z w := by
        rw [Real.coe_toNNReal', max_eq_left hε_nonneg]

/-- The point `x_ε` on the approximating curve, defined as the unique fixed point of the affine
contraction `z ↦ εx + (1 - ε)Tz`. -/
noncomputable def approximatingCurvePoint {D : Set H} (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (T : D → D) (hT : LipschitzWith 1 T)
    (ε : Set.Ioo (0 : ℝ) 1) (x : D) : D :=
  letI : Nonempty D := ⟨x⟩
  letI : CompleteSpace D := hD_closed.completeSpace_coe
  ContractingWith.fixedPoint (approximatingAffineMap hD_convex T ε x)
    (approximatingAffineMap_contracting hD_convex T hT ε x)

/-- The resolvent regularization operator `T_ε`, sending `x` to the point `x_ε` on the
approximating curve. -/
noncomputable def approximatingCurveOperator {D : Set H} (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (T : D → D) (hT : LipschitzWith 1 T)
    (ε : Set.Ioo (0 : ℝ) 1) :
    D → D :=
  fun x ↦ approximatingCurvePoint hD_closed hD_convex T hT ε x

/-- The fixed-point set of `T`, viewed as a subset of the ambient Hilbert space. -/
private def ambientFixedPointSet {D : Set H} (T : D → D) : Set H :=
  Subtype.val '' Function.fixedPoints T

/-- Helper for Proposition 4.30: extend a self-map on `D` to an ambient map by keeping the same
formula on `D` and freezing it at `x₀` outside `D`. -/
private noncomputable def ambientExtension {D : Set H} (T : D → D) (x₀ : H) : H → H :=
  Function.extend Subtype.val (fun z : D ↦ (T z : H)) (fun _ ↦ x₀)

/-- Helper for Proposition 4.30: the ambient extension is nonexpansive on `D` because it agrees
with `T` there. -/
private theorem ambientExtension_lipschitzOnWith {D : Set H} {T : D → D} (hT : LipschitzWith 1 T)
    (x₀ : H) :
    LipschitzOnWith 1 (ambientExtension T x₀) D := by
  intro x hx y hy
  have hx_ext : ambientExtension T x₀ x = (T ⟨x, hx⟩ : H) := by
    simpa [ambientExtension] using
      (Subtype.val_injective.extend_apply (fun z : D ↦ (T z : H)) (fun _ ↦ x₀) ⟨x, hx⟩)
  have hy_ext : ambientExtension T x₀ y = (T ⟨y, hy⟩ : H) := by
    simpa [ambientExtension] using
      (Subtype.val_injective.extend_apply (fun z : D ↦ (T z : H)) (fun _ ↦ x₀) ⟨y, hy⟩)
  -- On points of `D`, the ambient extension reduces to `T`.
  rw [hx_ext, hy_ext]
  simpa [Subtype.edist_eq] using hT.edist_le_mul ⟨x, hx⟩ ⟨y, hy⟩

/-- Helper for Proposition 4.30: the ambient fixed-point set is the intersection of `D` with the
fixed-point set of any ambient extension of `T`. -/
private theorem ambientFixedPointSet_eq_inter_fixedPoints_ambientExtension {D : Set H} (T : D → D)
    (x₀ : H) :
    ambientFixedPointSet T = D ∩ Function.fixedPoints (ambientExtension T x₀) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    constructor
    · exact z.2
    · -- A subtype fixed point stays fixed after forgetting to the ambient space.
      rw [Function.mem_fixedPoints_iff]
      have hz_fixed : T z = z := Function.mem_fixedPoints_iff.mp hz
      simpa [ambientExtension] using congrArg Subtype.val hz_fixed
  · rintro ⟨hxD, hx⟩
    -- A fixed point of the ambient extension inside `D` gives a fixed point of `T`.
    have hx_ext : ambientExtension T x₀ x = (T ⟨x, hxD⟩ : H) := by
      simpa [ambientExtension] using
        (Subtype.val_injective.extend_apply (fun z : D ↦ (T z : H)) (fun _ ↦ x₀) ⟨x, hxD⟩)
    refine ⟨⟨x, hxD⟩, ?_, rfl⟩
    rw [Function.mem_fixedPoints_iff]
    apply Subtype.ext
    rw [Function.mem_fixedPoints_iff] at hx
    simpa [hx_ext] using hx

/-- Helper for Proposition 4.30: when `Fix T` is nonempty, its ambient realization is nonempty,
closed, and convex. -/
private theorem ambientFixedPointSet_nonempty_isClosed_convex {D : Set H} (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) {T : D → D} (hT : LipschitzWith 1 T)
    (hfix : (Function.fixedPoints T).Nonempty) :
    (ambientFixedPointSet T).Nonempty ∧ IsClosed (ambientFixedPointSet T) ∧
      Convex ℝ (ambientFixedPointSet T) := by
  rcases hfix with ⟨p, hp⟩
  let S : H → H := ambientExtension T (p : H)
  have hS_lipschitz : LipschitzOnWith 1 S D :=
    ambientExtension_lipschitzOnWith hT (p : H)
  have hclosed_convex :
      IsClosed (D ∩ Function.fixedPoints S) ∧ Convex ℝ (D ∩ Function.fixedPoints S) := by
    constructor
    · -- On `D`, fixed points are the zeros of the residual map `S - id`.
      rw [show D ∩ Function.fixedPoints S = D ∩ (fun x : H ↦ S x - x) ⁻¹' ({0} : Set H) by
          ext x
          constructor
          · rintro ⟨hxD, hxfix⟩
            constructor
            · exact hxD
            · simpa [Function.mem_fixedPoints_iff, sub_eq_zero] using hxfix
          · rintro ⟨hxD, hxzero⟩
            constructor
            · exact hxD
            · simpa [Function.mem_fixedPoints_iff, sub_eq_zero] using hxzero]
      exact ContinuousOn.preimage_isClosed_of_isClosed
        (hS_lipschitz.continuousOn.sub continuous_id.continuousOn) hD_closed isClosed_singleton
    · -- The standard segment argument for nonexpansive maps keeps fixed points convex.
      rw [convex_iff_segment_subset]
      intro x hx y hy z hz
      rw [segment_eq_image_lineMap] at hz
      rcases hz with ⟨r, hr, rfl⟩
      have hzD : AffineMap.lineMap x y r ∈ D := hD_convex.lineMap_mem hx.1 hy.1 hr
      have hxfix : S x = x := Function.mem_fixedPoints_iff.mp hx.2
      have hyfix : S y = y := Function.mem_fixedPoints_iff.mp hy.2
      have hdist :
          dist x (S (AffineMap.lineMap x y r)) ≤ r * dist x y ∧
            dist (S (AffineMap.lineMap x y r)) y ≤ (1 - r) * dist x y := by
        constructor
        · calc
            dist x (S (AffineMap.lineMap x y r)) =
                dist (S x) (S (AffineMap.lineMap x y r)) := by rw [hxfix]
            _ ≤ (1 : ℝ) * dist x (AffineMap.lineMap x y r) := by
              simpa only [NNReal.coe_one] using hS_lipschitz.dist_le_mul x hx.1
                (AffineMap.lineMap x y r) hzD
            _ = r * dist x y := by
              rw [dist_left_lineMap]
              simp [Real.norm_of_nonneg hr.1]
        · calc
            dist (S (AffineMap.lineMap x y r)) y =
                dist (S (AffineMap.lineMap x y r)) (S y) := by rw [hyfix]
            _ ≤ (1 : ℝ) * dist (AffineMap.lineMap x y r) y := by
              simpa only [NNReal.coe_one] using hS_lipschitz.dist_le_mul
                (AffineMap.lineMap x y r) hzD y hy.1
            _ = (1 - r) * dist x y := by
              rw [dist_lineMap_right]
              simp [Real.norm_of_nonneg (sub_nonneg.mpr hr.2)]
      have htriangle : dist x y ≤ dist x (S (AffineMap.lineMap x y r)) +
          dist (S (AffineMap.lineMap x y r)) y := by
        simpa [dist_comm] using dist_triangle_right x y (S (AffineMap.lineMap x y r))
      have hsum_le :
          dist x (S (AffineMap.lineMap x y r)) + dist (S (AffineMap.lineMap x y r)) y ≤
            dist x y := by
        calc
          dist x (S (AffineMap.lineMap x y r)) + dist (S (AffineMap.lineMap x y r)) y ≤
              r * dist x y + (1 - r) * dist x y := by
                exact add_le_add hdist.1 hdist.2
          _ = dist x y := by ring
      have hsum_eq :
          dist x (S (AffineMap.lineMap x y r)) + dist (S (AffineMap.lineMap x y r)) y =
            dist x y :=
        le_antisymm hsum_le htriangle
      have hdist_left_eq : dist x (S (AffineMap.lineMap x y r)) = r * dist x y := by
        linarith [hdist.1, hdist.2, hsum_eq]
      have hdist_right_eq :
          dist (S (AffineMap.lineMap x y r)) y = (1 - r) * dist x y := by
        linarith [hdist.1, hdist.2, hsum_eq]
      have hfixed_line :
          S (AffineMap.lineMap x y r) = AffineMap.lineMap x y r := by
        simpa using eq_lineMap_of_dist_eq_mul_of_dist_eq_mul hdist_left_eq hdist_right_eq
      exact ⟨hzD, Function.mem_fixedPoints_iff.mpr hfixed_line⟩
  have hset :
      ambientFixedPointSet T = D ∩ Function.fixedPoints S :=
    by simpa [S] using ambientFixedPointSet_eq_inter_fixedPoints_ambientExtension T (p : H)
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨(p : H), ⟨p, hp, rfl⟩⟩
  · simpa [hset] using hclosed_convex.1
  · simpa [hset] using hclosed_convex.2

-- Proof sketch: Proposition 4.30(iii) identifies `Fix T` with the fixed-point set of the firmly
-- nonexpansive map `T_ε`; the standard closed-convex fixed-point theory in Hilbert spaces then
-- yields that the ambient fixed-point set is Chebyshev.
/-- The ambient fixed-point set of a nonexpansive self-map on a closed convex set is Chebyshev as
soon as it is nonempty. -/
private theorem ambientFixedPointSet_isChebyshev {D : Set H} (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) {T : D → D} (hT : LipschitzWith 1 T)
    (hfix : (Function.fixedPoints T).Nonempty) :
    IsChebyshev (ambientFixedPointSet T) := by
  rcases ambientFixedPointSet_nonempty_isClosed_convex hD_closed hD_convex hT hfix with
    ⟨hnonempty, hclosed, hconvex⟩
  -- The ambient fixed-point set is a nonempty closed convex subset of the Hilbert space.
  exact isChebyshev_of_nonempty_isClosed_convex hnonempty hclosed hconvex

/-- The metric projection of `x` onto the fixed-point set of `T` in the ambient Hilbert space. -/
noncomputable def approximatingCurveLimitPoint {D : Set H} (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (T : D → D) (hT : LipschitzWith 1 T)
    (hfix : (Function.fixedPoints T).Nonempty) (x : D) : H :=
  projectionPoint (ambientFixedPointSet T)
    (ambientFixedPointSet_isChebyshev hD_closed hD_convex hT hfix) (x : H)

/-- Helper for Proposition 4.30: any best approximation from the ambient fixed-point set agrees
with the projection point used to define the approximating-curve limit. -/
private theorem eq_approximatingCurveLimitPoint_of_isBestApproximation {D : Set H}
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (T : D → D) (hT : LipschitzWith 1 T)
    (hfix : (Function.fixedPoints T).Nonempty) (x : D) {z : H}
    (hz : IsBestApproximation (x : H) (ambientFixedPointSet T) z) :
    z = approximatingCurveLimitPoint hD_closed hD_convex T hT hfix x := by
  -- Uniqueness of best approximations identifies any competing minimizer with the projection point.
  exact eq_projectionPoint_of_isBestApproximation _ _ hz

/-- The approximating curve `ε ↦ x_ε` through the point `x`. -/
noncomputable def approximatingCurvePath {D : Set H} (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (T : D → D) (hT : LipschitzWith 1 T) (x : D) :
    Set.Ioo (0 : ℝ) 1 → H :=
  fun ε ↦ approximatingCurvePoint hD_closed hD_convex T hT ε x

/-- The distance from `x` to the approximating curve. -/
noncomputable def approximatingCurveDistance {D : Set H} (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (T : D → D) (hT : LipschitzWith 1 T) (x : D) :
    Set.Ioo (0 : ℝ) 1 → ℝ :=
  fun ε ↦ ‖(x : H) - approximatingCurvePoint hD_closed hD_convex T hT ε x‖

-- Proof sketch: the defining affine map is contracting on the complete metric space `D`, so
-- Banach's fixed-point theorem gives existence and uniqueness of its fixed point.
/-- Proposition 4.30 (1): for every `ε ∈ ]0,1[` and every `x ∈ D`, there is a unique point
`x_ε ∈ D` satisfying `x_ε = εx + (1 - ε)T x_ε`. -/
theorem approximatingCurvePoint_existsUnique {D : Set H} (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (T : D → D) (hT : LipschitzWith 1 T)
    (ε : Set.Ioo (0 : ℝ) 1) (x : D) :
    ∃! z : D, (z : H) = (ε : ℝ) • (x : H) + (1 - (ε : ℝ)) • (T z : H) := by
  letI : Nonempty D := ⟨x⟩
  letI : CompleteSpace D := hD_closed.completeSpace_coe
  let F := approximatingAffineMap hD_convex T ε x
  let hF := approximatingAffineMap_contracting hD_convex T hT ε x
  refine ⟨ContractingWith.fixedPoint F hF, ?_, ?_⟩
  · -- The Banach fixed point satisfies the defining affine equation.
    simpa [F, approximatingAffineMap] using congrArg Subtype.val hF.fixedPoint_isFixedPt.eq.symm
  · intro y hy
    -- Any other affine fixed point is equal to the Banach fixed point by uniqueness.
    have hy_fixed : IsFixedPt F y := by
      refine Subtype.ext ?_
      simpa [F, approximatingAffineMap] using hy.symm
    exact hF.fixedPoint_unique hy_fixed

-- Proof sketch: unfold `approximatingCurvePoint` and use that `ContractingWith.fixedPoint` is a
-- fixed point of `approximatingAffineMap`.
/-- Proposition 4.30 (2): the regularized point `x_ε` satisfies the affine fixed-point equation
`x_ε = εx + (1 - ε)T x_ε`. -/
theorem approximatingCurvePoint_eq_affine_combination {D : Set H} (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (T : D → D) (hT : LipschitzWith 1 T)
    (ε : Set.Ioo (0 : ℝ) 1) (x : D) :
    (approximatingCurvePoint hD_closed hD_convex T hT ε x : H) =
      (ε : ℝ) • (x : H) + (1 - (ε : ℝ)) •
        (T (approximatingCurvePoint hD_closed hD_convex T hT ε x) : H) := by
  letI : Nonempty D := ⟨x⟩
  letI : CompleteSpace D := hD_closed.completeSpace_coe
  let F := approximatingAffineMap hD_convex T ε x
  let hF := approximatingAffineMap_contracting hD_convex T hT ε x
  -- Unfold the Banach fixed point defining `x_ε`.
  simpa [approximatingCurvePoint, F, hF, approximatingAffineMap] using
    congrArg Subtype.val hF.fixedPoint_isFixedPt.eq.symm

-- Proof sketch: rearrange the fixed-point equation from the previous clause.
/-- Proposition 4.30 (3): equivalently, `x_ε` solves the resolvent equation
`x_ε - (1 - ε)T x_ε = εx`. -/
theorem approximatingCurvePoint_eq_resolvent {D : Set H} (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (T : D → D) (hT : LipschitzWith 1 T)
    (ε : Set.Ioo (0 : ℝ) 1) (x : D) :
    (approximatingCurvePoint hD_closed hD_convex T hT ε x : H) -
        (1 - (ε : ℝ)) • (T (approximatingCurvePoint hD_closed hD_convex T hT ε x) : H) =
      (ε : ℝ) • (x : H) := by
  -- Rearrange the affine fixed-point equation into resolvent form.
  calc
    (approximatingCurvePoint hD_closed hD_convex T hT ε x : H) -
        (1 - (ε : ℝ)) • (T (approximatingCurvePoint hD_closed hD_convex T hT ε x) : H) =
        ((ε : ℝ) • (x : H) +
          (1 - (ε : ℝ)) • (T (approximatingCurvePoint hD_closed hD_convex T hT ε x) : H)) -
            (1 - (ε : ℝ)) •
              (T (approximatingCurvePoint hD_closed hD_convex T hT ε x) : H) := by
          rw [approximatingCurvePoint_eq_affine_combination hD_closed hD_convex T hT ε x]
    _ = (ε : ℝ) • (x : H) := by
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Proposition 4.30: subtracting the resolvent equations for two approximating-curve
points yields a stable ambient identity. -/
private theorem approximatingCurvePoint_resolvent_sub_eq {D : Set H} (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (T : D → D) (hT : LipschitzWith 1 T)
    (ε : OpenUnitInterval) (x y : D) :
    ((approximatingCurvePoint hD_closed hD_convex T hT ε x : H) -
        (approximatingCurvePoint hD_closed hD_convex T hT ε y : H)) -
      (1 - (ε : ℝ)) •
        ((T (approximatingCurvePoint hD_closed hD_convex T hT ε x) : H) -
          (T (approximatingCurvePoint hD_closed hD_convex T hT ε y) : H)) =
    (ε : ℝ) • ((x : H) - (y : H)) := by
  -- Compare the two resolvent identities in the ambient Hilbert space and subtract them.
  calc
    ((approximatingCurvePoint hD_closed hD_convex T hT ε x : H) -
        (approximatingCurvePoint hD_closed hD_convex T hT ε y : H)) -
      (1 - (ε : ℝ)) •
        ((T (approximatingCurvePoint hD_closed hD_convex T hT ε x) : H) -
          (T (approximatingCurvePoint hD_closed hD_convex T hT ε y) : H)) =
        ((approximatingCurvePoint hD_closed hD_convex T hT ε x : H) -
            (1 - (ε : ℝ)) •
              (T (approximatingCurvePoint hD_closed hD_convex T hT ε x) : H)) -
          ((approximatingCurvePoint hD_closed hD_convex T hT ε y : H) -
            (1 - (ε : ℝ)) •
              (T (approximatingCurvePoint hD_closed hD_convex T hT ε y) : H)) := by
          simp [sub_eq_add_neg, smul_sub, add_assoc, add_left_comm, add_comm]
    _ = (ε : ℝ) • (x : H) - (ε : ℝ) • (y : H) := by
      rw [approximatingCurvePoint_eq_resolvent hD_closed hD_convex T hT ε x,
        approximatingCurvePoint_eq_resolvent hD_closed hD_convex T hT ε y]
    _ = (ε : ℝ) • ((x : H) - (y : H)) := by
      rw [smul_sub]

/-- Helper for Proposition 4.30: a self-resolvent identity forces the point to be fixed by `T`.
-/
private theorem fixed_of_resolvent_self_eq {D : Set H} {T : D → D} (ε : OpenUnitInterval) (z : D)
    (hz :
      (z : H) - (1 - (ε : ℝ)) • (T z : H) =
        (ε : ℝ) • (z : H)) :
    z ∈ Function.fixedPoints T := by
  have hscale :
      (1 - (ε : ℝ)) • ((z : H) - (T z : H)) = 0 := by
    -- Rearranging isolates the common scalar factor `1 - ε`.
    calc
      (1 - (ε : ℝ)) • ((z : H) - (T z : H)) =
          ((1 - (ε : ℝ)) • (z : H)) - (1 - (ε : ℝ)) • (T z : H) := by
            rw [smul_sub]
      _ = ((z : H) - (ε : ℝ) • (z : H)) - (1 - (ε : ℝ)) • (T z : H) := by
            rw [sub_smul, one_smul]
      _ = ((z : H) - (1 - (ε : ℝ)) • (T z : H)) - (ε : ℝ) • (z : H) := by
            abel_nf
      _ = 0 := by
            rw [hz]
            abel_nf
  have hsub_zero : (z : H) - (T z : H) = 0 := by
    rcases smul_eq_zero.mp hscale with hε | hsub
    · exact False.elim ((sub_ne_zero.mpr (ne_of_gt ε.2.2)) hε)
    · exact hsub
  -- A vanishing residual is exactly the fixed-point condition.
  rw [Function.mem_fixedPoints_iff]
  exact Subtype.ext (sub_eq_zero.mp hsub_zero).symm

-- Proof sketch: compare the fixed-point equations for `x_ε` and `y_ε`, rewrite the residual
-- pairing exactly as in the textbook argument, and invoke Proposition 4.4.
/-- Proposition 4.30 (4): for each `ε ∈ ]0,1[`, the operator `T_ε` is firmly nonexpansive on
`D`. -/
theorem approximatingCurveOperator_firmlyNonexpansiveOn {D : Set H} (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (T : D → D) (hT : LipschitzWith 1 T)
    (ε : Set.Ioo (0 : ℝ) 1) :
    FirmlyNonexpansiveOn D
      (fun x : D ↦ (approximatingCurveOperator hD_closed hD_convex T hT ε x : H)) := by
  intro x y
  -- Route correction: package the resolvent subtraction in ambient `H` before pairing with
  -- `x_ε - y_ε`, so the coercions stay fixed throughout the proof.
  let xe := approximatingCurvePoint hD_closed hD_convex T hT ε x
  let ye := approximatingCurvePoint hD_closed hD_convex T hT ε y
  let d : H := (xe : H) - (ye : H)
  let e : H := (T xe : H) - (T ye : H)
  have hres : d - (1 - (ε : ℝ)) • e = (ε : ℝ) • ((x : H) - (y : H)) := by
    simpa [xe, ye, d, e] using
      approximatingCurvePoint_resolvent_sub_eq hD_closed hD_convex T hT ε x y
  have he_norm : ‖e‖ ≤ ‖d‖ := by
    -- Nonexpansiveness of `T` transfers directly to the ambient differences.
    simpa [xe, ye, d, e, Subtype.dist_eq, dist_eq_norm] using hT.dist_le_mul xe ye
  have hinner_le : inner ℝ e d ≤ ‖d‖ ^ 2 := by
    calc
      inner ℝ e d ≤ ‖e‖ * ‖d‖ := real_inner_le_norm _ _
      _ ≤ ‖d‖ * ‖d‖ := by
        exact mul_le_mul_of_nonneg_right he_norm (norm_nonneg d)
      _ = ‖d‖ ^ 2 := by ring
  have hscaled :
      (ε : ℝ) * ‖d‖ ^ 2 ≤ (ε : ℝ) * inner ℝ ((x : H) - (y : H)) d := by
    have hone_sub_nonneg : 0 ≤ 1 - (ε : ℝ) := sub_nonneg.mpr (le_of_lt ε.2.2)
    have hmul :
        (1 - (ε : ℝ)) * inner ℝ e d ≤ (1 - (ε : ℝ)) * ‖d‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_left hinner_le hone_sub_nonneg
    have hpair :
        inner ℝ (d - (1 - (ε : ℝ)) • e) d =
          (ε : ℝ) * inner ℝ ((x : H) - (y : H)) d := by
      rw [hres, real_inner_smul_left]
    have hpair' :
        inner ℝ (d - (1 - (ε : ℝ)) • e) d =
          ‖d‖ ^ 2 - (1 - (ε : ℝ)) * inner ℝ e d := by
      rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    rw [← hpair, hpair']
    nlinarith
  have hfinal : ‖d‖ ^ 2 ≤ inner ℝ ((x : H) - (y : H)) d := by
    nlinarith [hscaled, ε.2.1]
  -- Reinsert the local abbreviations to match the definition of firm nonexpansiveness.
  simpa [approximatingCurveOperator, xe, ye, d] using hfinal

-- Proof sketch: if `x` is fixed by `T`, then the defining equation forces `x_ε = x`; conversely,
-- if `x = T_ε x`, substitute into the same equation and solve for `T x = x`.
/-- Proposition 4.30 (5): the fixed-point sets of `T_ε` and `T` coincide. -/
theorem fixedPoints_approximatingCurveOperator_eq {D : Set H} (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (T : D → D) (hT : LipschitzWith 1 T)
    (ε : Set.Ioo (0 : ℝ) 1) :
    Function.fixedPoints (approximatingCurveOperator hD_closed hD_convex T hT ε) =
      Function.fixedPoints T := by
  ext z
  constructor
  · intro hz
    -- Convert a fixed point of `T_ε` into the self-resolvent identity and cancel `1 - ε`.
    rw [Function.mem_fixedPoints_iff] at hz ⊢
    exact Function.mem_fixedPoints_iff.mp <|
      fixed_of_resolvent_self_eq ε z <| by
        have hz_curve : approximatingCurvePoint hD_closed hD_convex T hT ε z = z := by
          simpa [approximatingCurveOperator] using hz
        simpa [hz_curve] using
          approximatingCurvePoint_eq_resolvent hD_closed hD_convex T hT ε z
  · intro hz
    -- A fixed point of `T` itself satisfies the affine equation, so uniqueness gives `T_ε z = z`.
    rw [Function.mem_fixedPoints_iff] at hz ⊢
    have hz_affine :
        (z : H) = (ε : ℝ) • (z : H) + (1 - (ε : ℝ)) • (T z : H) := by
      have hz_val : (T z : H) = (z : H) := congrArg Subtype.val hz
      have hrewrite :
          (ε : ℝ) • (z : H) + (1 - (ε : ℝ)) • (z : H) =
            (ε : ℝ) • (z : H) + (1 - (ε : ℝ)) • (T z : H) := by
        exact congrArg (fun v : H ↦ (ε : ℝ) • (z : H) + (1 - (ε : ℝ)) • v) hz_val.symm
      have hsum : (ε : ℝ) + (1 - (ε : ℝ)) = 1 := by ring
      calc
        (z : H) = (1 : ℝ) • (z : H) := by rw [one_smul]
        _ = ((ε : ℝ) + (1 - (ε : ℝ))) • (z : H) := by rw [hsum]
        _ = (ε : ℝ) • (z : H) + (1 - (ε : ℝ)) • (z : H) := by rw [add_smul]
        _ = (ε : ℝ) • (z : H) + (1 - (ε : ℝ)) • (T z : H) := hrewrite
    simpa [approximatingCurveOperator] using
      (approximatingCurvePoint_existsUnique hD_closed hD_convex T hT ε z).unique
        (approximatingCurvePoint_eq_affine_combination hD_closed hD_convex T hT ε z)
        hz_affine

-- Proof sketch: start from the defining equation of `x_ε` and isolate the common residual term.
/-- Proposition 4.30 (6): the residual of `x_ε` satisfies
`ε (x - T x_ε) = x_ε - T x_ε`. -/
theorem approximatingCurvePoint_residual_eq_left {D : Set H} (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (T : D → D) (hT : LipschitzWith 1 T)
    (ε : Set.Ioo (0 : ℝ) 1) (x : D) :
    (ε : ℝ) • ((x : H) - (T (approximatingCurvePoint hD_closed hD_convex T hT ε x) : H)) =
      (approximatingCurvePoint hD_closed hD_convex T hT ε x : H) -
        (T (approximatingCurvePoint hD_closed hD_convex T hT ε x) : H) := by
  let xe := approximatingCurvePoint hD_closed hD_convex T hT ε x
  -- Subtract `T x_ε` from the resolvent identity and combine the two scalar coefficients.
  calc
    (ε : ℝ) • ((x : H) - (T xe : H)) =
        (ε : ℝ) • (x : H) - (ε : ℝ) • (T xe : H) := by
            rw [smul_sub]
    _ = ((xe : H) - (1 - (ε : ℝ)) • (T xe : H)) - (ε : ℝ) • (T xe : H) := by
            rw [← approximatingCurvePoint_eq_resolvent hD_closed hD_convex T hT ε x]
    _ = (xe : H) - ((1 - (ε : ℝ)) • (T xe : H) + (ε : ℝ) • (T xe : H)) := by
            abel_nf
    _ = (xe : H) - (T xe : H) := by
            rw [← add_smul]
            have hsum : (1 - (ε : ℝ)) + (ε : ℝ) = 1 := by ring
            rw [hsum, one_smul]

-- Proof sketch: combine the defining equation with the previous residual identity and solve for
-- `x_ε - T x_ε` in terms of `x - x_ε`.
/-- Proposition 4.30 (7): the same residual can be written as
`(ε / (1 - ε)) (x - x_ε)`. -/
theorem approximatingCurvePoint_residual_eq_right {D : Set H} (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (T : D → D) (hT : LipschitzWith 1 T)
    (ε : Set.Ioo (0 : ℝ) 1) (x : D) :
    (approximatingCurvePoint hD_closed hD_convex T hT ε x : H) -
        (T (approximatingCurvePoint hD_closed hD_convex T hT ε x) : H) =
      ((ε : ℝ) / (1 - (ε : ℝ))) •
        ((x : H) - (approximatingCurvePoint hD_closed hD_convex T hT ε x : H)) := by
  let xe := approximatingCurvePoint hD_closed hD_convex T hT ε x
  have hx_sub :
      ((x : H) - (xe : H)) =
        (1 - (ε : ℝ)) • ((x : H) - (T xe : H)) := by
    -- Rearranging the affine equation isolates `x - x_ε`.
    calc
      ((x : H) - (xe : H)) =
          (x : H) -
            ((ε : ℝ) • (x : H) + (1 - (ε : ℝ)) • (T xe : H)) := by
              rw [show (xe : H) =
                  (ε : ℝ) • (x : H) + (1 - (ε : ℝ)) • (T xe : H) by
                    simpa [xe] using
                      approximatingCurvePoint_eq_affine_combination hD_closed hD_convex T hT ε x]
      _ = ((x : H) - (ε : ℝ) • (x : H)) - (1 - (ε : ℝ)) • (T xe : H) := by
            abel_nf
      _ = ((1 - (ε : ℝ)) : ℝ) • (x : H) - (1 - (ε : ℝ)) • (T xe : H) := by
            rw [show (x : H) - (ε : ℝ) • (x : H) =
                ((1 - (ε : ℝ)) : ℝ) • (x : H) by
                  simpa using (sub_smul (1 : ℝ) (ε : ℝ) (x : H)).symm]
      _ = (1 - (ε : ℝ)) • ((x : H) - (T xe : H)) := by
            rw [smul_sub]
  have hone_sub_ne : (1 - (ε : ℝ)) ≠ 0 := sub_ne_zero.mpr (ne_of_gt ε.2.2)
  have hx_sub' :
      ((x : H) - (T xe : H)) =
        ((1 - (ε : ℝ))⁻¹) • ((x : H) - (xe : H)) := by
    -- Multiply the previous identity by the inverse scalar to cancel `1 - ε`.
    calc
      ((x : H) - (T xe : H)) = (1 : ℝ) • ((x : H) - (T xe : H)) := by
        rw [one_smul]
      _ = (((1 - (ε : ℝ))⁻¹) * (1 - (ε : ℝ))) • ((x : H) - (T xe : H)) := by
        rw [inv_mul_cancel₀ hone_sub_ne]
      _ = ((1 - (ε : ℝ))⁻¹) • ((1 - (ε : ℝ)) • ((x : H) - (T xe : H))) := by
        rw [smul_smul]
      _ = ((1 - (ε : ℝ))⁻¹) • ((x : H) - (xe : H)) := by
        rw [hx_sub]
  -- Combine the left residual identity with the inverse rewrite of `x - x_ε`.
  calc
    (xe : H) - (T xe : H) = (ε : ℝ) • ((x : H) - (T xe : H)) := by
      rw [approximatingCurvePoint_residual_eq_left hD_closed hD_convex T hT ε x]
    _ = (ε : ℝ) • (((1 - (ε : ℝ))⁻¹) • ((x : H) - (xe : H))) := by
      rw [hx_sub']
    _ = (((ε : ℝ) / (1 - (ε : ℝ))) : ℝ) • ((x : H) - (xe : H)) := by
      rw [smul_smul, div_eq_mul_inv]

/-- Helper for Proposition 4.30: along a parameter sequence `εₙ → 0+`, bounded approximating-curve
values have vanishing residuals `x_{εₙ} - T x_{εₙ}`. -/
private theorem approximatingCurvePoint_residual_tendsto_zero_of_bounded_seq {D : Set H}
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (T : D → D)
    (hT : LipschitzWith 1 T) {εs : ℕ → OpenUnitInterval} (x : D)
    (hεs : Tendsto εs atTop openUnitIntervalZeroRightFilter)
    (hbounded :
      Bornology.IsBounded
        (Set.range fun n ↦ (approximatingCurvePoint hD_closed hD_convex T hT (εs n) x : H))) :
    Tendsto
      (fun n ↦
        (approximatingCurvePoint hD_closed hD_convex T hT (εs n) x : H) -
          (T (approximatingCurvePoint hD_closed hD_convex T hT (εs n) x) : H))
      atTop (𝓝 (0 : H)) := by
  let u : ℕ → H := fun n ↦ approximatingCurvePoint hD_closed hD_convex T hT (εs n) x
  have hεs_right : Tendsto (fun n ↦ (εs n : ℝ)) atTop (𝓝[>] (0 : ℝ)) := by
    simpa [openUnitIntervalZeroRightFilter] using hεs
  have hεs_zero : Tendsto (fun n ↦ (εs n : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    hεs_right.trans nhdsWithin_le_nhds
  have hcoeff :
      Tendsto (fun n ↦ ((εs n : ℝ) / (1 - (εs n : ℝ)))) atTop (𝓝 (0 : ℝ)) := by
    have hden :
        Tendsto (fun n ↦ 1 - (εs n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
      simpa using tendsto_const_nhds.sub hεs_zero
    simpa using hεs_zero.div hden one_ne_zero
  rcases isBounded_iff_forall_norm_le.mp hbounded with ⟨R, hR⟩
  let C : ℝ := max R 0 + ‖(x : H)‖
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hC :
      ∀ n, ‖(x : H) - u n‖ ≤ C := by
    intro n
    calc
      ‖(x : H) - u n‖ ≤ ‖(x : H)‖ + ‖u n‖ := norm_sub_le _ _
      _ ≤ ‖(x : H)‖ + max R 0 := by
        gcongr
        exact le_trans (hR _ (Set.mem_range_self n)) (le_max_left _ _)
      _ = C := by
        dsimp [C]
        ring
  have hcoeff_norm :
      Tendsto (fun n ↦ C * ‖((εs n : ℝ) / (1 - (εs n : ℝ)))‖) atTop (𝓝 (0 : ℝ)) := by
    simpa [C] using hcoeff.norm.const_mul C
  have hbound :
      ∀ n,
        ‖u n -
            (T (approximatingCurvePoint hD_closed hD_convex T hT (εs n) x) : H)‖ ≤
          C * ‖((εs n : ℝ) / (1 - (εs n : ℝ)))‖ := by
    intro n
    calc
      ‖u n - (T (approximatingCurvePoint hD_closed hD_convex T hT (εs n) x) : H)‖ =
          ‖(((εs n : ℝ) / (1 - (εs n : ℝ))) : ℝ) • ((x : H) - u n)‖ := by
            rw [show u n -
                (T (approximatingCurvePoint hD_closed hD_convex T hT (εs n) x) : H) =
                  (((εs n : ℝ) / (1 - (εs n : ℝ))) : ℝ) • ((x : H) - u n) by
                  simpa [u] using
                    approximatingCurvePoint_residual_eq_right hD_closed hD_convex T hT
                      (εs n) x]
      _ = ‖((εs n : ℝ) / (1 - (εs n : ℝ)))‖ * ‖(x : H) - u n‖ := by
            rw [norm_smul]
      _ ≤ ‖((εs n : ℝ) / (1 - (εs n : ℝ)))‖ * C := by
            exact mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _)
      _ = C * ‖((εs n : ℝ) / (1 - (εs n : ℝ)))‖ := by
            ring
  -- The residual identity isolates a scalar factor tending to `0`, while the displacement remains
  -- uniformly bounded.
  exact squeeze_zero_norm' (Eventually.of_forall hbound) hcoeff_norm

/-- Helper for Proposition 4.30: the canonical parameter `1 / (n + 2)` lies in `]0,1[`. -/
private theorem canonicalOpenUnitIntervalPoint_mem (n : ℕ) :
    0 < (1 : ℝ) / (n + 2 : ℝ) ∧ (1 : ℝ) / (n + 2 : ℝ) < 1 := by
  -- The reciprocal is positive because the denominator `n + 2` is positive.
  constructor
  · have hden_pos : 0 < (n + 2 : ℝ) := by
      positivity
    exact one_div_pos.mpr hden_pos
  · -- Since `n + 2 > 1`, its reciprocal is strictly smaller than `1`.
    have hden_pos : 0 < (n + 2 : ℝ) := by
      positivity
    have hnat : 1 < n + 2 := by
      omega
    have hden_gt_one : (1 : ℝ) < (n + 2 : ℝ) := by
      exact_mod_cast hnat
    exact (div_lt_one hden_pos).2 hden_gt_one

/-- Helper for Proposition 4.30: the canonical zero-right probe sequence in `]0,1[`. -/
private noncomputable def canonicalOpenUnitIntervalPoint (n : ℕ) : OpenUnitInterval :=
  ⟨(1 : ℝ) / (n + 2 : ℝ), canonicalOpenUnitIntervalPoint_mem n⟩

/-- Helper for Proposition 4.30: the canonical probe sequence tends to `0` from the right. -/
private theorem canonicalOpenUnitIntervalPoint_tendsto :
    Tendsto canonicalOpenUnitIntervalPoint atTop openUnitIntervalZeroRightFilter := by
  have htoTopNat : Tendsto (fun n : ℕ ↦ n + 2) atTop atTop :=
    Filter.tendsto_add_atTop_nat 2
  have htoTop' : Tendsto (fun n : ℕ ↦ ((n + 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp htoTopNat
  have htoTop : Tendsto (fun n : ℕ ↦ (n + 2 : ℝ)) atTop atTop := by
    simpa [Nat.cast_add] using htoTop'
  have htoZero : Tendsto (fun n : ℕ ↦ (((n + 2 : ℝ))⁻¹)) atTop (𝓝 (0 : ℝ)) := by
    simpa [one_div] using htoTop.inv_tendsto_atTop
  have htoRight :
      Tendsto (fun n : ℕ ↦ ((canonicalOpenUnitIntervalPoint n : OpenUnitInterval) : ℝ))
        atTop (𝓝[>] (0 : ℝ)) := by
    -- The canonical reciprocal sequence converges to `0`, and every term stays in `(0, 1)`.
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (fun n : ℕ ↦ ((canonicalOpenUnitIntervalPoint n : OpenUnitInterval) : ℝ)) ?_ ?_
    · simpa [canonicalOpenUnitIntervalPoint, one_div] using htoZero
    · exact Eventually.of_forall fun n ↦ (canonicalOpenUnitIntervalPoint n).2.1
  simpa [openUnitIntervalZeroRightFilter] using htoRight

/-- Helper for Proposition 4.30: the canonical probe sequence is strictly decreasing. -/
private theorem canonicalOpenUnitIntervalPoint_strictAnti :
    StrictAnti fun n : ℕ ↦ ((canonicalOpenUnitIntervalPoint n : OpenUnitInterval) : ℝ) := by
  intro m n hmn
  -- Increasing the denominator makes the reciprocal strictly smaller.
  have hm_pos : 0 < (m : ℝ) + 2 := by
    positivity
  have hmn' : (m : ℝ) + 2 < (n : ℝ) + 2 := by
    exact_mod_cast Nat.add_lt_add_right hmn 2
  simpa [canonicalOpenUnitIntervalPoint, one_div] using one_div_lt_one_div_of_lt hm_pos hmn'

/-- Helper for Proposition 4.30: a predicate holding frequently near `0+` holds along a strictly
decreasing zero-right sequence of witness parameters. -/
private theorem zeroRight_subsequence_of_frequently (P : OpenUnitInterval → Prop)
    (hP : ∃ᶠ ε in openUnitIntervalZeroRightFilter, P ε) :
    ∃ εs : ℕ → OpenUnitInterval,
      StrictAnti (fun n ↦ (εs n : ℝ)) ∧
      Tendsto εs atTop openUnitIntervalZeroRightFilter ∧
      ∀ n, P (εs n) := by
  haveI : openUnitIntervalZeroRightFilter.IsCountablyGenerated := by
    dsimp [openUnitIntervalZeroRightFilter]
    infer_instance
  obtain ⟨η, hη, hηP⟩ := Filter.exists_seq_forall_of_frequently hP
  have hη_right : Tendsto (fun n ↦ (η n : ℝ)) atTop (𝓝[>] (0 : ℝ)) := by
    simpa [openUnitIntervalZeroRightFilter] using hη
  have hη_inv :
      Tendsto (fun n ↦ ((η n : ℝ))⁻¹) atTop atTop := by
    simpa [one_div] using hη_right.inv_tendsto_nhdsGT_zero
  obtain ⟨φ, hφ, hφ_inv⟩ := Filter.strictMono_subseq_of_tendsto_atTop hη_inv
  refine ⟨η ∘ φ, ?_, hη.comp hφ.tendsto_atTop, ?_⟩
  · -- A strictly increasing inverse sequence yields a strictly decreasing parameter sequence.
    intro m n hmn
    have hm_pos : 0 < ((η (φ m) : OpenUnitInterval) : ℝ) := (η (φ m)).2.1
    exact
      lt_of_one_div_lt_one_div hm_pos <|
        by simpa [Function.comp, one_div] using hφ_inv hmn
  · intro n
    exact hηP (φ n)

/-- Helper for Proposition 4.30: a bounded approximating-curve sequence with parameters tending to
`0+` forces `T` to have a fixed point. -/
private theorem fixedPoints_nonempty_of_bounded_approximatingCurve_seq {D : Set H}
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (T : D → D)
    (hT : LipschitzWith 1 T) {εs : ℕ → OpenUnitInterval} (x : D)
    (hεs : Tendsto εs atTop openUnitIntervalZeroRightFilter)
    (hbounded :
      Bornology.IsBounded
        (Set.range fun n ↦ (approximatingCurvePoint hD_closed hD_convex T hT (εs n) x : H))) :
    (Function.fixedPoints T).Nonempty := by
  let u : ℕ → D := fun n ↦ approximatingCurvePoint hD_closed hD_convex T hT (εs n) x
  rcases bounded_sequence_has_weakly_convergent_subsequence (fun n ↦ (u n : H)) hbounded with
    ⟨y, φ, hφ, hweak⟩
  have hyD : y ∈ D := by
    -- Closed convexity makes the weak image closed, so the weak limit still lies in `D`.
    have hD_weakClosed : IsClosed ((toWeakSpace ℝ H) '' D) := by
      rw [← closure_eq_iff_isClosed]
      calc
        closure ((toWeakSpace ℝ H) '' D) = (toWeakSpace ℝ H) '' closure D := by
          simpa using (hD_convex.toWeakSpace_closure ℝ).symm
        _ = (toWeakSpace ℝ H) '' D := by
          rw [hD_closed.closure_eq]
    have hyWeak :
        toWeakSpace ℝ H y ∈ closure ((toWeakSpace ℝ H) '' D) := by
      exact mem_closure_of_tendsto hweak <|
        Eventually.of_forall fun n ↦ ⟨u (φ n), (u (φ n)).property, rfl⟩
    rw [hD_weakClosed.closure_eq] at hyWeak
    rcases hyWeak with ⟨z, hzD, hzy⟩
    exact (toWeakSpace ℝ H).injective hzy ▸ hzD
  let yD : D := ⟨y, hyD⟩
  have hres :
      Tendsto
        (fun n ↦
          (u (φ n) : H) - (T (u (φ n)) : H))
        atTop (𝓝 (0 : H)) := by
    -- The bounded full sequence has vanishing residuals, hence so does every subsequence.
    exact
      (approximatingCurvePoint_residual_tendsto_zero_of_bounded_seq
        hD_closed hD_convex T hT x hεs hbounded).comp hφ.tendsto_atTop
  have hy_fixed :
      T yD = y := by
    -- Apply demiclosedness to the weakly convergent approximate fixed-point subsequence.
    simpa [u, yD] using
      map_eq_of_tendsto_weakly_of_residual_tendsto_zero_of_nonexpansive
        hD_closed hD_convex hT hweak hres
  refine ⟨yD, ?_⟩
  rw [Function.mem_fixedPoints_iff]
  exact Subtype.ext hy_fixed

/-- Helper for Proposition 4.30: along an antitone zero-right parameter sequence, the
approximating-curve points converge strongly to the projection point onto `Fix T`. -/
private theorem approximatingCurvePoint_tendsto_limitPoint_of_antitone_zeroRight_seq {D : Set H}
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (T : D → D)
    (hT : LipschitzWith 1 T) (hfix : (Function.fixedPoints T).Nonempty)
    {εs : ℕ → OpenUnitInterval} (hεs_anti : Antitone fun n ↦ (εs n : ℝ))
    (hεs : Tendsto εs atTop openUnitIntervalZeroRightFilter) (x : D) :
    Tendsto (fun n ↦ (approximatingCurvePoint hD_closed hD_convex T hT (εs n) x : H))
      atTop (𝓝 (approximatingCurveLimitPoint hD_closed hD_convex T hT hfix x)) := by
  let p := approximatingCurveLimitPoint hD_closed hD_convex T hT hfix x
  let u : ℕ → D := fun n ↦ approximatingCurvePoint hD_closed hD_convex T hT (εs n) x
  have hp_best : IsBestApproximation (x : H) (ambientFixedPointSet T) p := by
    -- The chosen projection point is the unique best approximation from `Fix T`.
    simpa [p, approximatingCurveLimitPoint] using
      projectionPoint_isBestApproximation (ambientFixedPointSet T)
        (ambientFixedPointSet_isChebyshev hD_closed hD_convex hT hfix) (x : H)
  rcases hp_best.1 with ⟨y, hyfix, hy_eq⟩
  have hfejer_p :
      ∀ n,
        ‖(x : H) - (u n : H)‖ ^ 2 + ‖(u n : H) - p‖ ^ 2 ≤ ‖(x : H) - p‖ ^ 2 := by
    intro n
    let xe := u n
    have hy_curve :
        y ∈ Function.fixedPoints (approximatingCurveOperator hD_closed hD_convex T hT (εs n)) := by
      rw [fixedPoints_approximatingCurveOperator_eq hD_closed hD_convex T hT (εs n)]
      exact hyfix
    have hy_eq_point : approximatingCurvePoint hD_closed hD_convex T hT (εs n) y = y := by
      simpa [approximatingCurveOperator] using Function.mem_fixedPoints_iff.mp hy_curve
    have hfirm :
        ‖(xe : H) - (y : H)‖ ^ 2 ≤ inner ℝ ((x : H) - (y : H)) ((xe : H) - (y : H)) := by
      -- Firm nonexpansiveness of `T_ε` gives the one-step Fejér estimate.
      simpa [approximatingCurveOperator, u, xe, hy_eq_point] using
        approximatingCurveOperator_firmlyNonexpansiveOn hD_closed hD_convex T hT (εs n) x y
    let a : H := (x : H) - (xe : H)
    let b : H := (xe : H) - (y : H)
    have hcross_nonneg : 0 ≤ inner ℝ a b := by
      have hrewrite :
          inner ℝ ((x : H) - (y : H)) ((xe : H) - (y : H)) =
            inner ℝ a b + ‖b‖ ^ 2 := by
        rw [show ((x : H) - (y : H)) = a + b by
            simp [a, b, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]]
        rw [inner_add_left, real_inner_self_eq_norm_sq]
      rw [hrewrite] at hfirm
      linarith
    have hnorm :
        ‖(x : H) - (y : H)‖ ^ 2 = ‖a‖ ^ 2 + 2 * inner ℝ a b + ‖b‖ ^ 2 := by
      rw [show ((x : H) - (y : H)) = a + b by
          simp [a, b, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]]
      simpa [a, b] using norm_add_sq_real a b
    have hsum : ‖a‖ ^ 2 + ‖b‖ ^ 2 ≤ ‖(x : H) - (y : H)‖ ^ 2 := by
      rw [hnorm]
      nlinarith
    simpa [u, p, xe, a, b, hy_eq] using hsum
  have hbounded :
      Bornology.IsBounded (Set.range fun n ↦ (u n : H)) := by
    refine isBounded_iff_forall_norm_le.mpr ?_
    refine ⟨‖(x : H) - p‖ + ‖p‖, ?_⟩
    intro z hz
    rcases hz with ⟨n, rfl⟩
    have hdist_sq : ‖(u n : H) - p‖ ^ 2 ≤ ‖(x : H) - p‖ ^ 2 := by
      nlinarith [hfejer_p n]
    have hdist_le : ‖(u n : H) - p‖ ≤ ‖(x : H) - p‖ := by
      nlinarith [hdist_sq, norm_nonneg ((u n : H) - p), norm_nonneg ((x : H) - p)]
    -- Bounding `u n - p` bounds `u n` itself by the triangle inequality.
    calc
      ‖(u n : H)‖ = ‖((u n : H) - p) + p‖ := by
        congr 1
        abel_nf
      _ ≤ ‖(u n : H) - p‖ + ‖p‖ := norm_add_le _ _
      _ ≤ ‖(x : H) - p‖ + ‖p‖ := by
        simpa [add_comm] using add_le_add_right hdist_le ‖p‖
  -- Route correction: every subsequence has a further subsequence converging to the projection
  -- point, so the whole sequence converges by the subsequence criterion.
  refine Filter.tendsto_of_subseq_tendsto ?_
  intro ns hns
  have hbounded_ns :
      Bornology.IsBounded (Set.range fun n ↦ (u (ns n) : H)) := by
    exact hbounded.subset <| by
      rintro _ ⟨n, rfl⟩
      exact Set.mem_range_self (ns n)
  rcases bounded_sequence_has_weakly_convergent_subsequence (fun n ↦ (u (ns n) : H)) hbounded_ns with
    ⟨z, ψ, hψ, hweak⟩
  have hzD : z ∈ D := by
    -- Closed convexity makes the weak image of `D` closed, so the weak limit stays in `D`.
    have hD_weakClosed : IsClosed ((toWeakSpace ℝ H) '' D) := by
      rw [← closure_eq_iff_isClosed]
      calc
        closure ((toWeakSpace ℝ H) '' D) = (toWeakSpace ℝ H) '' closure D := by
          simpa using (hD_convex.toWeakSpace_closure ℝ).symm
        _ = (toWeakSpace ℝ H) '' D := by
          rw [hD_closed.closure_eq]
    have hzWeak :
        toWeakSpace ℝ H z ∈ closure ((toWeakSpace ℝ H) '' D) := by
      exact mem_closure_of_tendsto hweak <|
        Eventually.of_forall fun n ↦ ⟨u (ns (ψ n)), (u (ns (ψ n))).property, rfl⟩
    rw [hD_weakClosed.closure_eq] at hzWeak
    rcases hzWeak with ⟨w, hwD, hwz⟩
    exact (toWeakSpace ℝ H).injective hwz ▸ hwD
  let zD : D := ⟨z, hzD⟩
  have hres_full :
      Tendsto (fun n ↦ (u n : H) - (T (u n) : H)) atTop (𝓝 (0 : H)) :=
    approximatingCurvePoint_residual_tendsto_zero_of_bounded_seq
      hD_closed hD_convex T hT x hεs hbounded
  have hres :
      Tendsto (fun n ↦ (u (ns (ψ n)) : H) - (T (u (ns (ψ n))) : H)) atTop (𝓝 (0 : H)) := by
    -- Residual decay persists after passing to the chosen subsubsequence.
    exact hres_full.comp (hns.comp hψ.tendsto_atTop)
  have hz_fixed : T zD = z := by
    -- Demiclosedness turns the weak limit of approximate fixed points into an actual fixed point.
    simpa [u, zD, Function.comp] using
      map_eq_of_tendsto_weakly_of_residual_tendsto_zero_of_nonexpansive
        hD_closed hD_convex hT hweak hres
  have hz_memAmbient : z ∈ ambientFixedPointSet T := by
    refine ⟨zD, ?_, rfl⟩
    rw [Function.mem_fixedPoints_iff]
    exact Subtype.ext hz_fixed
  have hdist_p_le_z : ‖(x : H) - p‖ ≤ ‖(x : H) - z‖ := by
    -- The projection point is no farther from `x` than any other fixed point.
    have hdist : dist (x : H) p ≤ dist (x : H) z := by
      rw [hp_best.2]
      exact Metric.infDist_le_dist_of_mem hz_memAmbient
    simpa [dist_eq_norm] using hdist
  have hweak_sub :
      Tendsto (fun n ↦ toWeakSpace ℝ H ((x : H) - (u (ns (ψ n)) : H))) atTop
        (𝓝 (toWeakSpace ℝ H ((x : H) - z))) := by
    -- Weak convergence is stable under subtracting the constant vector `x`.
    have hconst :
        Tendsto (fun _ : ℕ ↦ toWeakSpace ℝ H (x : H)) atTop (𝓝 (toWeakSpace ℝ H (x : H))) :=
      tendsto_const_nhds
    simpa [sub_eq_add_neg] using hconst.sub hweak
  have hlimsup :
      Filter.limsup (fun n ↦ ‖(x : H) - (u (ns (ψ n)) : H)‖) atTop ≤ ‖(x : H) - z‖ := by
    have hp_sq_le_z_sq : ‖(x : H) - p‖ ^ 2 ≤ ‖(x : H) - z‖ ^ 2 := by
      nlinarith [hdist_p_le_z, norm_nonneg ((x : H) - p), norm_nonneg ((x : H) - z)]
    have hboundedBelow :
        atTop.IsCoboundedUnder (· ≤ ·) fun n ↦ ‖(x : H) - (u (ns (ψ n)) : H)‖ := by
      exact isCoboundedUnder_le_of_le atTop (fun n ↦ norm_nonneg ((x : H) - (u (ns (ψ n)) : H)))
    refine Filter.limsup_le_of_le hboundedBelow <| Eventually.of_forall ?_
    intro n
    have hdist_sq :
        ‖(x : H) - (u (ns (ψ n)) : H)‖ ^ 2 ≤ ‖(x : H) - p‖ ^ 2 := by
      nlinarith [hfejer_p (ns (ψ n))]
    have hbound_sq :
        ‖(x : H) - (u (ns (ψ n)) : H)‖ ^ 2 ≤ ‖(x : H) - z‖ ^ 2 :=
      le_trans hdist_sq hp_sq_le_z_sq
    have hbound_abs :
        |‖(x : H) - (u (ns (ψ n)) : H)‖| ≤ |‖(x : H) - z‖| := (sq_le_sq).1 hbound_sq
    simpa [abs_of_nonneg (norm_nonneg ((x : H) - (u (ns (ψ n)) : H))),
      abs_of_nonneg (norm_nonneg ((x : H) - z))] using hbound_abs
  have hstrong_sub :
      Tendsto (fun n ↦ (x : H) - (u (ns (ψ n)) : H)) atTop (𝓝 ((x : H) - z)) := by
    -- Weak convergence plus the sharp norm bound upgrades to strong convergence.
    exact
      (tendsto_iff_tendsto_weakly_and_limsup_norm_le
        (fun n ↦ (x : H) - (u (ns (ψ n)) : H)) ((x : H) - z)).2
        ⟨hweak_sub, hlimsup⟩
  have hu_sub : Tendsto (fun n ↦ (u (ns (ψ n)) : H)) atTop (𝓝 z) := by
    -- Recover strong convergence of the curve points from convergence of the translated sequence.
    have hconst : Tendsto (fun _ : ℕ ↦ (x : H)) atTop (𝓝 (x : H)) := tendsto_const_nhds
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hconst.sub hstrong_sub
  have hsum_tendsto :
      Tendsto
        (fun n ↦ ‖(x : H) - (u (ns (ψ n)) : H)‖ ^ 2 + ‖(u (ns (ψ n)) : H) - p‖ ^ 2)
        atTop (𝓝 (‖(x : H) - z‖ ^ 2 + ‖z - p‖ ^ 2)) := by
    have hleft :
        Tendsto (fun n ↦ ‖(x : H) - (u (ns (ψ n)) : H)‖ ^ 2) atTop
          (𝓝 (‖(x : H) - z‖ ^ 2)) := by
      simpa using hstrong_sub.norm.pow 2
    have hright :
        Tendsto (fun n ↦ ‖(u (ns (ψ n)) : H) - p‖ ^ 2) atTop (𝓝 (‖z - p‖ ^ 2)) := by
      simpa using ((hu_sub.sub tendsto_const_nhds).norm.pow 2)
    simpa using hleft.add hright
  have hsum_le : ‖(x : H) - z‖ ^ 2 + ‖z - p‖ ^ 2 ≤ ‖(x : H) - p‖ ^ 2 := by
    -- Passing the Fejér inequality to the limit isolates the defect term `‖z - p‖²`.
    exact le_of_tendsto_of_tendsto hsum_tendsto tendsto_const_nhds <|
      Eventually.of_forall fun n ↦ hfejer_p (ns (ψ n))
  have hzp : z = p := by
    have hzp_norm_zero : ‖z - p‖ = 0 := by
      nlinarith [hsum_le, hdist_p_le_z, norm_nonneg ((x : H) - p), norm_nonneg ((x : H) - z)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hzp_norm_zero)
  refine ⟨ψ, ?_⟩
  -- The chosen subsubsequence converges strongly to the projection point.
  simpa [u, p, hzp] using hu_sub

-- Proof sketch: otherwise a bounded subnet of the approximating curve would admit a weak cluster
-- point, and the residual identity plus demiclosedness would produce a fixed point of `T`.
/-- Proposition 4.30 (8): if `T` has no fixed point, then the norms `‖x_ε‖` diverge to `+∞` as
`ε ↓ 0`. -/
theorem approximatingCurvePoint_norm_tendsto_atTop_of_fixedPoints_eq_empty {D : Set H}
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (T : D → D)
    (hT : LipschitzWith 1 T) (hfix : Function.fixedPoints T = ∅) (x : D) :
    Tendsto
      (fun ε : Set.Ioo (0 : ℝ) 1 ↦
        ‖(approximatingCurvePoint hD_closed hD_convex T hT ε x : H)‖)
      (Filter.comap (fun ε : Set.Ioo (0 : ℝ) 1 ↦ (ε : ℝ)) (𝓝[>] (0 : ℝ))) atTop := by
  rw [tendsto_atTop]
  intro R
  by_contra hR
  haveI : openUnitIntervalZeroRightFilter.IsCountablyGenerated := by
    dsimp [openUnitIntervalZeroRightFilter]
    infer_instance
  have hfreq :
      ∃ᶠ ε in openUnitIntervalZeroRightFilter,
        ‖(approximatingCurvePoint hD_closed hD_convex T hT ε x : H)‖ < R := by
    have hfreq' :
        ∃ᶠ ε in openUnitIntervalZeroRightFilter,
          ¬R ≤ ‖(approximatingCurvePoint hD_closed hD_convex T hT ε x : H)‖ := by
      simpa only [Filter.Frequently, not_not] using hR
    exact hfreq'.mono fun _ hε ↦ lt_of_not_ge hε
  rcases exists_seq_forall_of_frequently hfreq with ⟨εs, hεs, hεsR⟩
  have hbounded :
      Bornology.IsBounded
        (Set.range fun n ↦
          (approximatingCurvePoint hD_closed hD_convex T hT (εs n) x : H)) := by
    refine isBounded_iff_forall_norm_le.mpr ?_
    refine ⟨max R 0, ?_⟩
    intro z hz
    rcases hz with ⟨n, rfl⟩
    have hle : ‖(approximatingCurvePoint hD_closed hD_convex T hT (εs n) x : H)‖ ≤ max R 0 := by
      have hRle : ‖(approximatingCurvePoint hD_closed hD_convex T hT (εs n) x : H)‖ ≤ R := by
        exact le_of_lt (hεsR n)
      exact le_trans hRle (le_max_left _ _)
    simpa using hle
  have hnonempty :
      (Function.fixedPoints T).Nonempty :=
    fixedPoints_nonempty_of_bounded_approximatingCurve_seq
      hD_closed hD_convex T hT x hεs hbounded
  exact Set.nonempty_iff_ne_empty.mp hnonempty hfix

-- Proof sketch: `y` is also fixed by `T_ε`, and firm nonexpansiveness of `T_ε` yields the
-- Pythagorean inequality after specializing the defining estimate at `x` and `y`.
/-- Proposition 4.30 (9): every fixed point of `T` is Fejér-monotone with respect to the
approximating curve. -/
theorem approximatingCurvePoint_norm_sq_add_norm_sq_le_of_mem_fixedPoints {D : Set H}
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (T : D → D)
    (hT : LipschitzWith 1 T) (ε : Set.Ioo (0 : ℝ) 1) (x : D) :
    ∀ y ∈ Function.fixedPoints T,
      ‖(x : H) - (approximatingCurvePoint hD_closed hD_convex T hT ε x : H)‖ ^ 2 +
          ‖(approximatingCurvePoint hD_closed hD_convex T hT ε x : H) - (y : H)‖ ^ 2 ≤
        ‖(x : H) - (y : H)‖ ^ 2 := by
  intro y hy
  let xe := approximatingCurvePoint hD_closed hD_convex T hT ε x
  have hy_curve : y ∈ Function.fixedPoints (approximatingCurveOperator hD_closed hD_convex T hT ε) := by
    rw [fixedPoints_approximatingCurveOperator_eq hD_closed hD_convex T hT ε]
    exact hy
  have hy_eq : approximatingCurveOperator hD_closed hD_convex T hT ε y = y :=
    Function.mem_fixedPoints_iff.mp hy_curve
  have hfirm :
      ‖(xe : H) - (y : H)‖ ^ 2 ≤ inner ℝ ((x : H) - (y : H)) ((xe : H) - (y : H)) := by
    -- Specialize firm nonexpansiveness of `T_ε` at `x` and the fixed point `y`.
    have hy_eq_point : approximatingCurvePoint hD_closed hD_convex T hT ε y = y := by
      simpa [approximatingCurveOperator] using hy_eq
    simpa [approximatingCurveOperator, xe, hy_eq_point] using
      approximatingCurveOperator_firmlyNonexpansiveOn hD_closed hD_convex T hT ε x y
  let a : H := (x : H) - (xe : H)
  let b : H := (xe : H) - (y : H)
  have hcross_nonneg : 0 ≤ inner ℝ a b := by
    -- Rewrite the firm estimate in the decomposition `(x - y) = (x - x_ε) + (x_ε - y)`.
    have hrewrite :
        inner ℝ ((x : H) - (y : H)) ((xe : H) - (y : H)) =
          inner ℝ a b + ‖b‖ ^ 2 := by
      rw [show ((x : H) - (y : H)) = a + b by
          simp [a, b, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]]
      rw [inner_add_left, real_inner_self_eq_norm_sq]
    rw [hrewrite] at hfirm
    linarith
  have hnorm :
      ‖(x : H) - (y : H)‖ ^ 2 = ‖a‖ ^ 2 + 2 * inner ℝ a b + ‖b‖ ^ 2 := by
    -- Expand the norm of the decomposition `(x - y) = a + b`.
    rw [show ((x : H) - (y : H)) = a + b by
        simp [a, b, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]]
    simpa [a, b] using norm_add_sq_real a b
  have hsum : ‖a‖ ^ 2 + ‖b‖ ^ 2 ≤ ‖(x : H) - (y : H)‖ ^ 2 := by
    rw [hnorm]
    nlinarith
  simpa [a, b, xe] using hsum

-- Proof sketch: use the Fejér estimate to prove boundedness, apply demiclosedness via the
-- residual identity to identify weak cluster points as fixed points, and then use the projection
-- characterization of closed convex sets to identify the limit.
/-- Proposition 4.30 (10): if `T` has a fixed point, then `x_ε` converges to the metric
projection of `x` onto `Fix T` as `ε ↓ 0`. -/
theorem approximatingCurvePoint_tendsto_projection_of_fixedPoints_nonempty {D : Set H}
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (T : D → D)
    (hT : LipschitzWith 1 T) (hfix : (Function.fixedPoints T).Nonempty) (x : D) :
    Tendsto (approximatingCurvePath hD_closed hD_convex T hT x)
      (Filter.comap (fun ε : Set.Ioo (0 : ℝ) 1 ↦ (ε : ℝ)) (𝓝[>] (0 : ℝ)))
      (𝓝 (approximatingCurveLimitPoint hD_closed hD_convex T hT hfix x)) := by
  let p := approximatingCurveLimitPoint hD_closed hD_convex T hT hfix x
  by_contra hconv
  obtain ⟨s, hs, hfreq⟩ :=
    (Filter.not_tendsto_iff_exists_frequently_notMem).1 hconv
  rcases zeroRight_subsequence_of_frequently
      (fun ε ↦ approximatingCurvePath hD_closed hD_convex T hT x ε ∉ s) hfreq with
    ⟨εs, hεs_anti, hεs, hεs_out⟩
  have hseq :
      Tendsto (fun n ↦ (approximatingCurvePoint hD_closed hD_convex T hT (εs n) x : H))
        atTop (𝓝 p) := by
    simpa [p, approximatingCurvePath] using
      approximatingCurvePoint_tendsto_limitPoint_of_antitone_zeroRight_seq
        hD_closed hD_convex T hT hfix hεs_anti.antitone hεs x
  have hmem :
      ∀ᶠ n in atTop, approximatingCurvePath hD_closed hD_convex T hT x (εs n) ∈ s := by
    simpa [p, approximatingCurvePath] using hseq.eventually hs
  rcases hmem.exists with ⟨n, hn⟩
  exact hεs_out n hn

-- Proof sketch: compare the two fixed-point equations for `x_ε` and `x_δ`, use nonexpansiveness
-- of `T`, expand the squared norms, and rearrange.
/-- Proposition 4.30 (11): the two-parameter inequality relating `x_ε` and `x_δ`. -/
theorem approximatingCurvePoint_twoParameter_inequality {D : Set H} (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (T : D → D) (hT : LipschitzWith 1 T)
    (ε δ : Set.Ioo (0 : ℝ) 1) (x : D) :
    (((((ε : ℝ) - (δ : ℝ)) / (1 - (ε : ℝ))) ^ 2) *
          ‖(approximatingCurvePoint hD_closed hD_convex T hT ε x : H) - (x : H)‖ ^ 2) +
        ((δ : ℝ) * (2 - (δ : ℝ)) *
          ‖(approximatingCurvePoint hD_closed hD_convex T hT δ x : H) -
              (approximatingCurvePoint hD_closed hD_convex T hT ε x : H)‖ ^ 2) ≤
      2 * (((ε : ℝ) - (δ : ℝ)) / (1 - (ε : ℝ))) *
        inner ℝ
          ((approximatingCurvePoint hD_closed hD_convex T hT ε x : H) - (x : H))
          ((approximatingCurvePoint hD_closed hD_convex T hT δ x : H) -
            (approximatingCurvePoint hD_closed hD_convex T hT ε x : H)) := by
  let xe := approximatingCurvePoint hD_closed hD_convex T hT ε x
  let xd := approximatingCurvePoint hD_closed hD_convex T hT δ x
  let yε : H := (xe : H) - (x : H)
  let yδ : H := (xd : H) - (x : H)
  let d : H := (xd : H) - (xe : H)
  let c : ℝ := ((ε : ℝ) - (δ : ℝ)) / (1 - (ε : ℝ))
  have hε_ne : 1 - (ε : ℝ) ≠ 0 := sub_ne_zero.mpr (ne_of_gt ε.2.2)
  have hδ_ne : 1 - (δ : ℝ) ≠ 0 := sub_ne_zero.mpr (ne_of_gt δ.2.2)
  have hyδ : yδ = yε + d := by
    -- The two displacement vectors differ exactly by `x_δ - x_ε`.
    simp [yδ, yε, d, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hTxe :
      (T xe : H) = (x : H) + ((1 - (ε : ℝ))⁻¹ : ℝ) • yε := by
    -- Rewrite the affine fixed-point equation for `x_ε` so that only the displacement `y_ε`
    -- remains after cancelling the base point `x`.
    have hmain :
        (1 - (ε : ℝ)) • (T xe : H) = (xe : H) - (ε : ℝ) • (x : H) := by
      calc
        (1 - (ε : ℝ)) • (T xe : H) =
            ((ε : ℝ) • (x : H) + (1 - (ε : ℝ)) • (T xe : H)) - (ε : ℝ) • (x : H) := by
              abel_nf
        _ = (xe : H) - (ε : ℝ) • (x : H) := by
              rw [← approximatingCurvePoint_eq_affine_combination hD_closed hD_convex T hT ε x]
    have hrewrite :
        (xe : H) - (ε : ℝ) • (x : H) = (1 - (ε : ℝ)) • (x : H) + yε := by
      -- `xe - εx` is the base point contribution `(1 - ε)x` plus the displacement `yε`.
      dsimp [yε]
      module
    calc
      (T xe : H) = (1 : ℝ) • (T xe : H) := by rw [one_smul]
      _ = (((1 - (ε : ℝ))⁻¹ * (1 - (ε : ℝ))) : ℝ) • (T xe : H) := by
        rw [inv_mul_cancel₀ hε_ne]
      _ = ((1 - (ε : ℝ))⁻¹ : ℝ) • ((1 - (ε : ℝ)) • (T xe : H)) := by
        rw [smul_smul]
      _ = ((1 - (ε : ℝ))⁻¹ : ℝ) • ((1 - (ε : ℝ)) • (x : H) + yε) := by
        rw [hmain, hrewrite]
      _ = (x : H) + ((1 - (ε : ℝ))⁻¹ : ℝ) • yε := by
        rw [smul_add, smul_smul, inv_mul_cancel₀ hε_ne, one_smul]
  have hTxd :
      (T xd : H) = (x : H) + ((1 - (δ : ℝ))⁻¹ : ℝ) • yδ := by
    -- The same rearrangement gives the explicit formula for `T x_δ`.
    have hmain :
        (1 - (δ : ℝ)) • (T xd : H) = (xd : H) - (δ : ℝ) • (x : H) := by
      calc
        (1 - (δ : ℝ)) • (T xd : H) =
            ((δ : ℝ) • (x : H) + (1 - (δ : ℝ)) • (T xd : H)) - (δ : ℝ) • (x : H) := by
              abel_nf
        _ = (xd : H) - (δ : ℝ) • (x : H) := by
              rw [← approximatingCurvePoint_eq_affine_combination hD_closed hD_convex T hT δ x]
    have hrewrite :
        (xd : H) - (δ : ℝ) • (x : H) = (1 - (δ : ℝ)) • (x : H) + yδ := by
      -- The same decomposition holds for `x_δ`.
      dsimp [yδ]
      module
    calc
      (T xd : H) = (1 : ℝ) • (T xd : H) := by rw [one_smul]
      _ = (((1 - (δ : ℝ))⁻¹ * (1 - (δ : ℝ))) : ℝ) • (T xd : H) := by
        rw [inv_mul_cancel₀ hδ_ne]
      _ = ((1 - (δ : ℝ))⁻¹ : ℝ) • ((1 - (δ : ℝ)) • (T xd : H)) := by
        rw [smul_smul]
      _ = ((1 - (δ : ℝ))⁻¹ : ℝ) • ((1 - (δ : ℝ)) • (x : H) + yδ) := by
        rw [hmain, hrewrite]
      _ = (x : H) + ((1 - (δ : ℝ))⁻¹ : ℝ) • yδ := by
        rw [smul_add, smul_smul, inv_mul_cancel₀ hδ_ne, one_smul]
  have hdiff :
      (T xd : H) - (T xe : H) =
        ((1 - (δ : ℝ))⁻¹ : ℝ) • yδ - ((1 - (ε : ℝ))⁻¹ : ℝ) • yε := by
    -- After subtracting the explicit formulas, the common base point `x` disappears.
    simp [hTxd, hTxe, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hrepack :
      ((1 - (δ : ℝ))⁻¹ : ℝ) • yδ - ((1 - (ε : ℝ))⁻¹ : ℝ) • yε =
        ((1 - (δ : ℝ))⁻¹ : ℝ) • (d - c • yε) := by
    have hscalar :
        ((1 - (δ : ℝ))⁻¹ : ℝ) - (1 - (ε : ℝ))⁻¹ =
          -((1 - (δ : ℝ))⁻¹ : ℝ) * c := by
      dsimp [c]
      field_simp [hδ_ne, hε_ne]
      ring
    calc
      ((1 - (δ : ℝ))⁻¹ : ℝ) • yδ - ((1 - (ε : ℝ))⁻¹ : ℝ) • yε =
          ((((1 - (δ : ℝ))⁻¹ : ℝ) - (1 - (ε : ℝ))⁻¹) : ℝ) • yε +
            ((1 - (δ : ℝ))⁻¹ : ℝ) • d := by
              rw [hyδ]
              module
      _ = -((((1 - (δ : ℝ))⁻¹ : ℝ) * c) • yε) + ((1 - (δ : ℝ))⁻¹ : ℝ) • d := by
            rw [hscalar]
            have hneg :
                (-(1 - (δ : ℝ))⁻¹ * c : ℝ) = -(((1 - (δ : ℝ))⁻¹ : ℝ) * c) := by
              ring
            rw [hneg, neg_smul]
      _ = ((1 - (δ : ℝ))⁻¹ : ℝ) • d - (((1 - (δ : ℝ))⁻¹ : ℝ) * c) • yε := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = ((1 - (δ : ℝ))⁻¹ : ℝ) • d - ((1 - (δ : ℝ))⁻¹ : ℝ) • (c • yε) := by
            rw [smul_smul]
      _ = ((1 - (δ : ℝ))⁻¹ : ℝ) • (d - c • yε) := by
            simp [smul_sub, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hnorm_nonexp :
      ‖((1 - (δ : ℝ))⁻¹ : ℝ) • (d - c • yε)‖ ≤ ‖d‖ := by
    -- Nonexpansiveness of `T` bounds the transformed displacement by `‖x_δ - x_ε‖`.
    have hdist : ‖(T xd : H) - (T xe : H)‖ ≤ ‖(xd : H) - (xe : H)‖ := by
      simpa [Subtype.dist_eq, dist_eq_norm] using hT.dist_le_mul xd xe
    simpa [hdiff, hrepack, d] using hdist
  have hone_sub_pos : 0 < 1 - (δ : ℝ) := sub_pos.mpr δ.2.2
  have hv_le : ‖d - c • yε‖ ≤ (1 - (δ : ℝ)) * ‖d‖ := by
    have hδ_inv_nonneg : 0 ≤ ((1 - (δ : ℝ))⁻¹ : ℝ) := inv_nonneg.mpr (le_of_lt hone_sub_pos)
    rw [norm_smul, Real.norm_of_nonneg hδ_inv_nonneg] at hnorm_nonexp
    have hmul := mul_le_mul_of_nonneg_left hnorm_nonexp (le_of_lt hone_sub_pos)
    simpa [mul_assoc, hδ_ne] using hmul
  have hv_sq :
      ‖d - c • yε‖ ^ 2 ≤ (1 - (δ : ℝ)) ^ 2 * ‖d‖ ^ 2 := by
    have hsq_right : ((1 - (δ : ℝ)) * ‖d‖) ^ 2 = (1 - (δ : ℝ)) ^ 2 * ‖d‖ ^ 2 := by
      ring
    have hsq : ‖d - c • yε‖ ^ 2 ≤ ((1 - (δ : ℝ)) * ‖d‖) ^ 2 := by
      nlinarith [hv_le, norm_nonneg (d - c • yε)]
    rwa [hsq_right] at hsq
  have hexpand :
      ‖d - c • yε‖ ^ 2 = c ^ 2 * ‖yε‖ ^ 2 - 2 * c * inner ℝ yε d + ‖d‖ ^ 2 := by
    -- Expand the squared norm exactly as in the textbook proof.
    have h := norm_sub_sq_real d (c • yε)
    rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs] at h
    rw [real_inner_comm yε d] at h
    have habs : (|c| * ‖yε‖) ^ 2 = c ^ 2 * ‖yε‖ ^ 2 := by
      calc
        (|c| * ‖yε‖) ^ 2 = |c| ^ 2 * ‖yε‖ ^ 2 := by ring
        _ = c ^ 2 * ‖yε‖ ^ 2 := by rw [sq_abs]
    rw [habs] at h
    ring_nf at h ⊢
    exact h
  have hcore :
      c ^ 2 * ‖yε‖ ^ 2 + (δ : ℝ) * (2 - (δ : ℝ)) * ‖d‖ ^ 2 ≤
        2 * c * inner ℝ yε d := by
    -- Rearranging the expanded nonexpansive estimate yields the target inequality.
    rw [hexpand] at hv_sq
    nlinarith [hv_sq]
  -- Replace the abbreviations by the original curve points.
  simpa [xe, xd, yε, d, c, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hcore

-- Proof sketch: when `δ < ε`, the previous inequality implies the relevant inner product is
-- nonnegative, and the norm identity for `x_δ - x` gives the claimed estimate.
/-- Proposition 4.30 (12): for `0 < δ < ε < 1`, the distances from `x` satisfy a
Pythagorean-type inequality. -/
theorem approximatingCurvePoint_norm_sq_add_norm_sq_le_of_lt {D : Set H}
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (T : D → D)
    (hT : LipschitzWith 1 T) (ε δ : Set.Ioo (0 : ℝ) 1) (hδε : (δ : ℝ) < ε) (x : D) :
    ‖(x : H) - (approximatingCurvePoint hD_closed hD_convex T hT ε x : H)‖ ^ 2 +
        ‖(approximatingCurvePoint hD_closed hD_convex T hT ε x : H) -
            (approximatingCurvePoint hD_closed hD_convex T hT δ x : H)‖ ^ 2 ≤
      ‖(x : H) - (approximatingCurvePoint hD_closed hD_convex T hT δ x : H)‖ ^ 2 := by
  let xe := approximatingCurvePoint hD_closed hD_convex T hT ε x
  let xd := approximatingCurvePoint hD_closed hD_convex T hT δ x
  have hineq :=
    approximatingCurvePoint_twoParameter_inequality hD_closed hD_convex T hT ε δ x
  have hcoeff_pos : 0 < ((ε : ℝ) - (δ : ℝ)) / (1 - (ε : ℝ)) := by
    -- The scalar coefficient is positive when `δ < ε`.
    exact div_pos (sub_pos.mpr hδε) (sub_pos.mpr ε.2.2)
  have hinner_nonneg :
      0 ≤ inner ℝ ((xe : H) - (x : H)) ((xd : H) - (xe : H)) := by
    -- The left-hand side of the two-parameter inequality is nonnegative, so the right-hand side is.
    have hrhs_nonneg :
        0 ≤
          2 * (((ε : ℝ) - (δ : ℝ)) / (1 - (ε : ℝ))) *
            inner ℝ ((xe : H) - (x : H)) ((xd : H) - (xe : H)) := by
      have hleft_nonneg :
          0 ≤
            ((((ε : ℝ) - (δ : ℝ)) / (1 - (ε : ℝ))) ^ 2) * ‖(xe : H) - (x : H)‖ ^ 2 +
              (δ : ℝ) * (2 - (δ : ℝ)) * ‖(xd : H) - (xe : H)‖ ^ 2 := by
        have hδ_nonneg : 0 ≤ (δ : ℝ) := le_of_lt δ.2.1
        have hδ_two_nonneg : 0 ≤ 2 - (δ : ℝ) := by linarith [δ.2.2]
        positivity
      linarith
    nlinarith [hrhs_nonneg, hcoeff_pos]
  have hexpand :
      ‖(xd : H) - (x : H)‖ ^ 2 =
        ‖(xe : H) - (x : H)‖ ^ 2 +
          2 * inner ℝ ((xe : H) - (x : H)) ((xd : H) - (xe : H)) +
          ‖(xd : H) - (xe : H)‖ ^ 2 := by
    -- Expand the squared norm of `(x_δ - x)` using `(x_δ - x) = (x_ε - x) + (x_δ - x_ε)`.
    have hsum :
        (xd : H) - (x : H) = ((xe : H) - (x : H)) + ((xd : H) - (xe : H)) := by
      abel_nf
    rw [hsum]
    simpa using norm_add_sq_real ((xe : H) - (x : H)) ((xd : H) - (xe : H))
  have hresult :
      ‖(xe : H) - (x : H)‖ ^ 2 + ‖(xd : H) - (xe : H)‖ ^ 2 ≤ ‖(xd : H) - (x : H)‖ ^ 2 := by
    rw [hexpand]
    nlinarith
  simpa [xe, xd, norm_sub_rev] using hresult

-- Proof sketch: apply the previous inequality to `δ < ε` and read off that the scalar distance
-- to the curve cannot increase as `ε` increases.
/-- Proposition 4.30 (13): the function `ε ↦ ‖x - x_ε‖` is decreasing on `]0,1[`. -/
theorem approximatingCurveDistance_antitone {D : Set H} (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (T : D → D) (hT : LipschitzWith 1 T) (x : D) :
    Antitone (approximatingCurveDistance hD_closed hD_convex T hT x) := by
  intro ε δ hεδ
  by_cases hEq : ε = δ
  · simpa [hEq]
  · have hlt : (ε : ℝ) < δ := lt_of_le_of_ne hεδ (by
        intro hεδ'
        exact hEq (Subtype.ext hεδ'))
    have hsq :
        (approximatingCurveDistance hD_closed hD_convex T hT x δ) ^ 2 ≤
          (approximatingCurveDistance hD_closed hD_convex T hT x ε) ^ 2 := by
      -- Apply the preceding Fejér inequality with the larger parameter `δ`.
      have hmain :=
        approximatingCurvePoint_norm_sq_add_norm_sq_le_of_lt hD_closed hD_convex T hT
          δ ε hlt x
      have hmain' :
          ‖(x : H) - (approximatingCurvePoint hD_closed hD_convex T hT δ x : H)‖ ^ 2 ≤
            ‖(x : H) - (approximatingCurvePoint hD_closed hD_convex T hT ε x : H)‖ ^ 2 := by
        nlinarith
      simpa [approximatingCurveDistance] using hmain'
    have hδ_nonneg : 0 ≤ approximatingCurveDistance hD_closed hD_convex T hT x δ := by
      simp [approximatingCurveDistance]
    have hε_nonneg : 0 ≤ approximatingCurveDistance hD_closed hD_convex T hT x ε := by
      simp [approximatingCurveDistance]
    nlinarith

-- Proof sketch: the two-parameter estimate controls `‖x_δ - x_ε‖` by a quantity that tends to
-- `0` when `δ → ε` from either side, giving left- and right-continuity.
/-- Helper for Proposition 4.30: when `0 < δ < ε < 1`, the gap `‖x_δ - x_ε‖` is controlled by the
distance from `x` to the larger-parameter point `x_ε`. -/
private theorem approximatingCurvePoint_norm_sub_le_of_lt {D : Set H} (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (T : D → D) (hT : LipschitzWith 1 T)
    (ε δ : OpenUnitInterval) (hδε : (δ : ℝ) < ε) (x : D) :
    ‖(approximatingCurvePoint hD_closed hD_convex T hT δ x : H) -
        (approximatingCurvePoint hD_closed hD_convex T hT ε x : H)‖ ≤
      2 * (((ε : ℝ) - (δ : ℝ)) / ((δ : ℝ) * (2 - (δ : ℝ)) * (1 - (ε : ℝ)))) *
        ‖(approximatingCurvePoint hD_closed hD_convex T hT ε x : H) - (x : H)‖ := by
  let xe := approximatingCurvePoint hD_closed hD_convex T hT ε x
  let xd := approximatingCurvePoint hD_closed hD_convex T hT δ x
  let c : ℝ := ((ε : ℝ) - (δ : ℝ)) / (1 - (ε : ℝ))
  have hcoeff_pos : 0 < c := by
    -- The ordered-parameter coefficient is strictly positive.
    exact div_pos (sub_pos.mpr hδε) (sub_pos.mpr ε.2.2)
  have hδfactor_pos : 0 < (δ : ℝ) * (2 - (δ : ℝ)) := by
    -- The quadratic weight stays positive on `]0,1[`.
    nlinarith [δ.2.1, δ.2.2]
  have hmain :=
    approximatingCurvePoint_twoParameter_inequality hD_closed hD_convex T hT ε δ x
  have hinner_bound :
      inner ℝ ((xe : H) - (x : H)) ((xd : H) - (xe : H)) ≤
        ‖(xe : H) - (x : H)‖ * ‖(xd : H) - (xe : H)‖ := by
    -- Cauchy-Schwarz bounds the mixed inner-product term.
    exact real_inner_le_norm _ _
  have haux :
      (δ : ℝ) * (2 - (δ : ℝ)) * ‖(xd : H) - (xe : H)‖ ^ 2 ≤
        2 * c * ‖(xe : H) - (x : H)‖ * ‖(xd : H) - (xe : H)‖ := by
    have hfirst_nonneg :
        0 ≤ c ^ 2 * ‖(xe : H) - (x : H)‖ ^ 2 := by
      positivity
    have hright :
        2 * c * inner ℝ ((xe : H) - (x : H)) ((xd : H) - (xe : H)) ≤
          2 * c * (‖(xe : H) - (x : H)‖ * ‖(xd : H) - (xe : H)‖) := by
      have htwo_c_nonneg : 0 ≤ 2 * c := by positivity
      exact mul_le_mul_of_nonneg_left hinner_bound htwo_c_nonneg
    linarith
  have hestimate :
      ‖(xd : H) - (xe : H)‖ ≤
        (2 * c / ((δ : ℝ) * (2 - (δ : ℝ)))) * ‖(xe : H) - (x : H)‖ := by
    -- Since the quadratic weight is positive, one copy of `‖x_δ - x_ε‖` can be cancelled.
    by_cases hd : ‖(xd : H) - (xe : H)‖ = 0
    · have hrhs_nonneg :
          0 ≤ (2 * c / ((δ : ℝ) * (2 - (δ : ℝ)))) * ‖(xe : H) - (x : H)‖ := by
        have hquot_nonneg : 0 ≤ 2 * c / ((δ : ℝ) * (2 - (δ : ℝ))) := by
          exact div_nonneg (by positivity) hδfactor_pos.le
        exact mul_nonneg hquot_nonneg (norm_nonneg _)
      simpa [hd] using hrhs_nonneg
    · have hd_pos : 0 < ‖(xd : H) - (xe : H)‖ := by
        have hne : 0 ≠ ‖(xd : H) - (xe : H)‖ := by
          simpa [eq_comm] using hd
        exact lt_of_le_of_ne (norm_nonneg _) hne
      have hestimate' :
          ‖(xd : H) - (xe : H)‖ ≤
            (2 * c * ‖(xe : H) - (x : H)‖) / ((δ : ℝ) * (2 - (δ : ℝ))) := by
        refine (le_div_iff₀ hδfactor_pos).2 ?_
        nlinarith [haux, hd_pos]
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hestimate'
  have hδ_ne : (δ : ℝ) ≠ 0 := by linarith [δ.2.1]
  have htwo_sub_ne : 2 - (δ : ℝ) ≠ 0 := by linarith [δ.2.2]
  have hone_sub_ε_ne : 1 - (ε : ℝ) ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_gt ε.2.2)
  have hrewrite :
      (2 * c / ((δ : ℝ) * (2 - (δ : ℝ)))) =
        2 * (((ε : ℝ) - (δ : ℝ)) / ((δ : ℝ) * (2 - (δ : ℝ)) * (1 - (ε : ℝ)))) := by
    -- Rewrite the scalar coefficient into the textbook form.
    dsimp [c]
    field_simp [hδ_ne, htwo_sub_ne, hone_sub_ε_ne]
  simpa [xe, xd, norm_sub_rev, hrewrite] using hestimate

/-- Helper for Proposition 4.30: the ambient distance between two points on the approximating
curve is the norm of their ambient difference. -/
private theorem approximatingCurvePath_dist_eq_norm {D : Set H} (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (T : D → D) (hT : LipschitzWith 1 T) (x : D)
    (ε δ : OpenUnitInterval) :
    dist (approximatingCurvePath hD_closed hD_convex T hT x ε)
        (approximatingCurvePath hD_closed hD_convex T hT x δ) =
      ‖(approximatingCurvePoint hD_closed hD_convex T hT ε x : H) -
          (approximatingCurvePoint hD_closed hD_convex T hT δ x : H)‖ := by
  -- Unfold the path and rewrite the metric distance in the ambient norm.
  simp [approximatingCurvePath, dist_eq_norm]

/-- Helper for Proposition 4.30: the scalar distance from `x` to the approximating curve is always
nonnegative. -/
private theorem approximatingCurveDistance_nonneg {D : Set H} (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (T : D → D) (hT : LipschitzWith 1 T) (x : D)
    (ε : OpenUnitInterval) :
    0 ≤ approximatingCurveDistance hD_closed hD_convex T hT x ε := by
  -- This is immediate from the norm defining the scalar distance.
  simp [approximatingCurveDistance]

/-- Helper for Proposition 4.30: if a positive denominator is bounded below by half of a positive
base, then its reciprocal is bounded by `2 / base`. -/
private theorem one_div_le_two_div_of_half_le {base den : ℝ} (hbase_pos : 0 < base)
    (hden_pos : 0 < den) (hbound : base / 2 ≤ den) :
    1 / den ≤ 2 / base := by
  -- Clear the factor `1 / (base * den)` to compare the reciprocals through the denominator bound.
  have hbd : base ≤ 2 * den := by
    nlinarith
  have hpos : 0 ≤ 1 / (base * den) := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hbd hpos
  have hleft : (1 / (base * den)) * base = 1 / den := by
    field_simp [hbase_pos.ne', hden_pos.ne']
  have hright : (1 / (base * den)) * (2 * den) = 2 / base := by
    field_simp [hbase_pos.ne', hden_pos.ne']
  rw [hleft, hright] at hmul
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Helper for Proposition 4.30: scaling the reciprocal estimate by a nonnegative numerator yields
the coefficient bound used in the continuity argument. -/
private theorem two_mul_div_mul_le {base den a d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hbase_pos : 0 < base) (hden_pos : 0 < den) (hbound : base / 2 ≤ den) :
    2 * (d / den) * a ≤ (4 * a / base) * d := by
  -- Reduce the claim to the reciprocal estimate and then scale by `2 * d * a`.
  have hrecip : 1 / den ≤ 2 / base :=
    one_div_le_two_div_of_half_le hbase_pos hden_pos hbound
  have hnum_nonneg : 0 ≤ 2 * d * a := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hrecip hnum_nonneg
  have hleft : (2 * d * a) * (1 / den) = 2 * (d / den) * a := by
    field_simp [hden_pos.ne']
  have hright : (2 * d * a) * (2 / base) = (4 * a / base) * d := by
    field_simp [hbase_pos.ne']
    ring
  rw [hleft, hright] at hmul
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Helper for Proposition 4.30: near a parameter `ε₀`, the left-hand variation of the
approximating curve is controlled linearly by the parameter distance. -/
private theorem approximatingCurvePath_dist_le_left_near {D : Set H} (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (T : D → D) (hT : LipschitzWith 1 T) (x : D)
    (ε₀ δ : OpenUnitInterval) (hδε₀ : δ ≤ ε₀)
    (hnear : dist δ ε₀ < min ((ε₀ : ℝ) / 2) ((1 - (ε₀ : ℝ)) / 2)) :
    dist (approximatingCurvePath hD_closed hD_convex T hT x δ)
        (approximatingCurvePath hD_closed hD_convex T hT x ε₀) ≤
      (4 * approximatingCurveDistance hD_closed hD_convex T hT x ε₀ /
          ((ε₀ : ℝ) * (1 - (ε₀ : ℝ)))) *
        dist δ ε₀ := by
  by_cases hEq : δ = ε₀
  · -- The equal-parameter case is trivial.
    simp [hEq]
  · -- Route correction: package the ordered-parameter estimate into a uniform local metric bound.
    have hlt : (δ : ℝ) < ε₀ := by
      exact lt_of_le_of_ne hδε₀ fun hcoeeq ↦ hEq (Subtype.ext hcoeeq)
    have hdist_eq : dist δ ε₀ = (ε₀ : ℝ) - (δ : ℝ) := by
      rw [Subtype.dist_eq, Real.dist_eq]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (abs_of_nonpos (sub_nonpos.mpr (show (δ : ℝ) ≤ ε₀ from hδε₀)))
    have hnear_left : dist δ ε₀ < (ε₀ : ℝ) / 2 := by
      exact lt_of_lt_of_le hnear (min_le_left _ _)
    have hδ_lower : (ε₀ : ℝ) / 2 ≤ (δ : ℝ) := by
      rw [hdist_eq] at hnear_left
      linarith
    have hbase_half_le_den :
        ((ε₀ : ℝ) * (1 - (ε₀ : ℝ))) / 2 ≤
          (δ : ℝ) * (2 - (δ : ℝ)) * (1 - (ε₀ : ℝ)) := by
      -- The small neighborhood keeps `δ` away from `0`, so the denominator stays uniformly
      -- bounded below.
      have htwo_ge : 1 ≤ 2 - (δ : ℝ) := by
        linarith [δ.2.2]
      have hone_sub_nonneg : 0 ≤ 1 - (ε₀ : ℝ) := sub_nonneg.mpr (le_of_lt ε₀.2.2)
      have hstep1 :
          ((ε₀ : ℝ) / 2) * (1 - (ε₀ : ℝ)) ≤ (δ : ℝ) * (1 - (ε₀ : ℝ)) :=
        mul_le_mul_of_nonneg_right hδ_lower hone_sub_nonneg
      have hδmul_nonneg : 0 ≤ (δ : ℝ) * (1 - (ε₀ : ℝ)) := by
        exact mul_nonneg (le_of_lt δ.2.1) hone_sub_nonneg
      have hstep2 :
          (δ : ℝ) * (1 - (ε₀ : ℝ)) ≤
            (δ : ℝ) * (2 - (δ : ℝ)) * (1 - (ε₀ : ℝ)) := by
        have hmult := mul_le_mul_of_nonneg_left htwo_ge hδmul_nonneg
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmult
      have hstart :
          ((ε₀ : ℝ) * (1 - (ε₀ : ℝ))) / 2 = ((ε₀ : ℝ) / 2) * (1 - (ε₀ : ℝ)) := by
        ring
      rw [hstart]
      exact le_trans hstep1 hstep2
    have hmain :=
      approximatingCurvePoint_norm_sub_le_of_lt hD_closed hD_convex T hT ε₀ δ hlt x
    have hmain' :
        dist (approximatingCurvePath hD_closed hD_convex T hT x δ)
            (approximatingCurvePath hD_closed hD_convex T hT x ε₀) ≤
          2 * (((ε₀ : ℝ) - (δ : ℝ)) /
                ((δ : ℝ) * (2 - (δ : ℝ)) * (1 - (ε₀ : ℝ)))) *
              approximatingCurveDistance hD_closed hD_convex T hT x ε₀ := by
      -- Rewrite the ordered estimate into the metric language of the path.
      rw [approximatingCurvePath_dist_eq_norm, approximatingCurveDistance]
      simpa [norm_sub_rev, mul_assoc, mul_left_comm, mul_comm] using hmain
    have hdist_nonneg : 0 ≤ dist δ ε₀ := dist_nonneg
    have happrox_nonneg :
        0 ≤ approximatingCurveDistance hD_closed hD_convex T hT x ε₀ :=
      approximatingCurveDistance_nonneg hD_closed hD_convex T hT x ε₀
    have hbase_pos : 0 < (ε₀ : ℝ) * (1 - (ε₀ : ℝ)) := by
      exact mul_pos ε₀.2.1 (sub_pos.mpr ε₀.2.2)
    have hden_pos : 0 < (δ : ℝ) * (2 - (δ : ℝ)) * (1 - (ε₀ : ℝ)) := by
      have htwo_sub_pos : 0 < 2 - (δ : ℝ) := by
        linarith [δ.2.2]
      exact mul_pos (mul_pos δ.2.1 htwo_sub_pos) (sub_pos.mpr ε₀.2.2)
    have hcoef :
        2 * (((ε₀ : ℝ) - (δ : ℝ)) /
              ((δ : ℝ) * (2 - (δ : ℝ)) * (1 - (ε₀ : ℝ)))) *
            approximatingCurveDistance hD_closed hD_convex T hT x ε₀ ≤
          (4 * approximatingCurveDistance hD_closed hD_convex T hT x ε₀ /
              ((ε₀ : ℝ) * (1 - (ε₀ : ℝ)))) *
            ((ε₀ : ℝ) - (δ : ℝ)) := by
      -- Compare the variable denominator with the fixed positive lower bound from the neighborhood
      -- control.
      exact
        two_mul_div_mul_le happrox_nonneg (sub_nonneg.mpr hδε₀) hbase_pos hden_pos
          hbase_half_le_den
    refine le_trans hmain' ?_
    rw [hdist_eq]
    exact hcoef

/-- Helper for Proposition 4.30: near a parameter `ε₀`, the right-hand variation of the
approximating curve is controlled linearly by the parameter distance. -/
private theorem approximatingCurvePath_dist_le_right_near {D : Set H} (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (T : D → D) (hT : LipschitzWith 1 T) (x : D)
    (ε₀ δ : OpenUnitInterval) (hε₀δ : ε₀ ≤ δ)
    (hnear : dist δ ε₀ < min ((ε₀ : ℝ) / 2) ((1 - (ε₀ : ℝ)) / 2)) :
    dist (approximatingCurvePath hD_closed hD_convex T hT x δ)
        (approximatingCurvePath hD_closed hD_convex T hT x ε₀) ≤
      (4 * approximatingCurveDistance hD_closed hD_convex T hT x ε₀ /
          ((ε₀ : ℝ) * (1 - (ε₀ : ℝ)))) *
        dist δ ε₀ := by
  by_cases hEq : ε₀ = δ
  · -- The equal-parameter case is trivial.
    simp [hEq]
  · -- Route correction: use monotonicity of `ε ↦ ‖x - x_ε‖` to freeze the right-hand factor at
    -- `ε₀`.
    have hlt : ε₀ < (δ : ℝ) := by
      exact lt_of_le_of_ne hε₀δ fun hcoeeq ↦ hEq (Subtype.ext hcoeeq)
    have hdist_eq : dist δ ε₀ = (δ : ℝ) - (ε₀ : ℝ) := by
      rw [Subtype.dist_eq, Real.dist_eq]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (abs_of_nonneg (sub_nonneg.mpr (show (ε₀ : ℝ) ≤ δ from hε₀δ)))
    have hnear_right : dist δ ε₀ < (1 - (ε₀ : ℝ)) / 2 := by
      exact lt_of_lt_of_le hnear (min_le_right _ _)
    have hone_sub_lower : (1 - (ε₀ : ℝ)) / 2 ≤ 1 - (δ : ℝ) := by
      rw [hdist_eq] at hnear_right
      linarith
    have hbase_half_le_den :
        ((ε₀ : ℝ) * (1 - (ε₀ : ℝ))) / 2 ≤
          (ε₀ : ℝ) * (2 - (ε₀ : ℝ)) * (1 - (δ : ℝ)) := by
      -- The small neighborhood keeps `δ` away from `1`, so the denominator stays uniformly
      -- bounded below.
      have htwo_ge : 1 ≤ 2 - (ε₀ : ℝ) := by
        linarith [ε₀.2.2]
      have hε₀_nonneg : 0 ≤ (ε₀ : ℝ) := le_of_lt ε₀.2.1
      have hstep1 :
          ((1 - (ε₀ : ℝ)) / 2) * (ε₀ : ℝ) ≤ (1 - (δ : ℝ)) * (ε₀ : ℝ) :=
        mul_le_mul_of_nonneg_right hone_sub_lower hε₀_nonneg
      have hε₀mul_nonneg : 0 ≤ (1 - (δ : ℝ)) * (ε₀ : ℝ) := by
        exact mul_nonneg (sub_nonneg.mpr (le_of_lt δ.2.2)) hε₀_nonneg
      have hstep2 :
          (1 - (δ : ℝ)) * (ε₀ : ℝ) ≤
            (ε₀ : ℝ) * (2 - (ε₀ : ℝ)) * (1 - (δ : ℝ)) := by
        have hmult := mul_le_mul_of_nonneg_left htwo_ge hε₀mul_nonneg
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmult
      have hstart :
          ((ε₀ : ℝ) * (1 - (ε₀ : ℝ))) / 2 = ((1 - (ε₀ : ℝ)) / 2) * (ε₀ : ℝ) := by
        ring
      rw [hstart]
      exact le_trans hstep1 hstep2
    have hmain :=
      approximatingCurvePoint_norm_sub_le_of_lt hD_closed hD_convex T hT δ ε₀ hlt x
    have hmain' :
        dist (approximatingCurvePath hD_closed hD_convex T hT x δ)
            (approximatingCurvePath hD_closed hD_convex T hT x ε₀) ≤
          2 * (((δ : ℝ) - (ε₀ : ℝ)) /
                ((ε₀ : ℝ) * (2 - (ε₀ : ℝ)) * (1 - (δ : ℝ)))) *
              approximatingCurveDistance hD_closed hD_convex T hT x δ := by
      -- Rewrite the ordered estimate into the metric language of the path.
      rw [approximatingCurvePath_dist_eq_norm, approximatingCurveDistance]
      simpa [norm_sub_rev, mul_assoc, mul_left_comm, mul_comm] using hmain
    have hmono :
        approximatingCurveDistance hD_closed hD_convex T hT x δ ≤
          approximatingCurveDistance hD_closed hD_convex T hT x ε₀ :=
      approximatingCurveDistance_antitone hD_closed hD_convex T hT x hε₀δ
    have hcoeff_nonneg :
        0 ≤ 2 * (((δ : ℝ) - (ε₀ : ℝ)) /
            ((ε₀ : ℝ) * (2 - (ε₀ : ℝ)) * (1 - (δ : ℝ)))) := by
      have hden_pos : 0 < (ε₀ : ℝ) * (2 - (ε₀ : ℝ)) * (1 - (δ : ℝ)) := by
        have htwo_sub_pos : 0 < 2 - (ε₀ : ℝ) := by
          linarith [ε₀.2.2]
        exact mul_pos (mul_pos ε₀.2.1 htwo_sub_pos) (sub_pos.mpr δ.2.2)
      have hdiv_nonneg :
          0 ≤ ((δ : ℝ) - (ε₀ : ℝ)) /
            ((ε₀ : ℝ) * (2 - (ε₀ : ℝ)) * (1 - (δ : ℝ))) := by
        exact div_nonneg (sub_nonneg.mpr hε₀δ) hden_pos.le
      nlinarith
    have hmain'' :
        dist (approximatingCurvePath hD_closed hD_convex T hT x δ)
            (approximatingCurvePath hD_closed hD_convex T hT x ε₀) ≤
          2 * (((δ : ℝ) - (ε₀ : ℝ)) /
                ((ε₀ : ℝ) * (2 - (ε₀ : ℝ)) * (1 - (δ : ℝ)))) *
              approximatingCurveDistance hD_closed hD_convex T hT x ε₀ := by
      refine le_trans hmain' ?_
      exact mul_le_mul_of_nonneg_left hmono hcoeff_nonneg
    have happrox_nonneg :
        0 ≤ approximatingCurveDistance hD_closed hD_convex T hT x ε₀ :=
      approximatingCurveDistance_nonneg hD_closed hD_convex T hT x ε₀
    have hbase_pos : 0 < (ε₀ : ℝ) * (1 - (ε₀ : ℝ)) := by
      exact mul_pos ε₀.2.1 (sub_pos.mpr ε₀.2.2)
    have hden_pos : 0 < (ε₀ : ℝ) * (2 - (ε₀ : ℝ)) * (1 - (δ : ℝ)) := by
      have htwo_sub_pos : 0 < 2 - (ε₀ : ℝ) := by
        linarith [ε₀.2.2]
      exact mul_pos (mul_pos ε₀.2.1 htwo_sub_pos) (sub_pos.mpr δ.2.2)
    have hcoef :
        2 * (((δ : ℝ) - (ε₀ : ℝ)) /
              ((ε₀ : ℝ) * (2 - (ε₀ : ℝ)) * (1 - (δ : ℝ)))) *
            approximatingCurveDistance hD_closed hD_convex T hT x ε₀ ≤
          (4 * approximatingCurveDistance hD_closed hD_convex T hT x ε₀ /
              ((ε₀ : ℝ) * (1 - (ε₀ : ℝ)))) *
            ((δ : ℝ) - (ε₀ : ℝ)) := by
      -- Compare the variable denominator with the same fixed lower bound as on the left.
      exact two_mul_div_mul_le happrox_nonneg (sub_nonneg.mpr hε₀δ) hbase_pos hden_pos
        hbase_half_le_den
    refine le_trans hmain'' ?_
    rw [hdist_eq]
    exact hcoef

/-- Helper for Proposition 4.30: the two one-sided local gap bounds imply continuity of the
approximating curve at every parameter. -/
private theorem approximatingCurvePath_continuousAt_of_two_sided_gap_bounds {D : Set H}
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (T : D → D)
    (hT : LipschitzWith 1 T) (x : D) (ε₀ : OpenUnitInterval) :
    ContinuousAt (approximatingCurvePath hD_closed hD_convex T hT x) ε₀ := by
  let C : ℝ :=
    4 * approximatingCurveDistance hD_closed hD_convex T hT x ε₀ /
      ((ε₀ : ℝ) * (1 - (ε₀ : ℝ)))
  let ρ : ℝ := min ((ε₀ : ℝ) / 2) ((1 - (ε₀ : ℝ)) / 2)
  have happrox_nonneg :
      0 ≤ approximatingCurveDistance hD_closed hD_convex T hT x ε₀ :=
    approximatingCurveDistance_nonneg hD_closed hD_convex T hT x ε₀
  have hC_nonneg : 0 ≤ C := by
    -- The local linear coefficient is nonnegative.
    dsimp [C]
    have hden_pos : 0 < (ε₀ : ℝ) * (1 - (ε₀ : ℝ)) := by
      exact mul_pos ε₀.2.1 (sub_pos.mpr ε₀.2.2)
    have hnum_nonneg :
        0 ≤ 4 * approximatingCurveDistance hD_closed hD_convex T hT x ε₀ := by
      nlinarith
    exact div_nonneg hnum_nonneg hden_pos.le
  have hρ_pos : 0 < ρ := by
    -- The center `ε₀` lies strictly inside `(0, 1)`, so both half-radii are positive.
    dsimp [ρ]
    refine lt_min_iff.mpr ?_
    constructor
    · exact div_pos ε₀.2.1 (by norm_num)
    · exact div_pos (sub_pos.mpr ε₀.2.2) (by norm_num)
  rw [Metric.continuousAt_iff]
  intro η hη
  have hCp1_pos : 0 < C + 1 := by
    linarith
  refine ⟨min ρ (η / (C + 1)), ?_, ?_⟩
  · -- The source radius is positive because it is bounded by two positive radii.
    refine lt_min_iff.mpr ?_
    constructor
    · exact hρ_pos
    · exact div_pos hη hCp1_pos
  · intro δ hδ
    have hδρ : dist δ ε₀ < ρ := by
      exact lt_of_lt_of_le hδ (min_le_left _ _)
    have hδη : dist δ ε₀ < η / (C + 1) := by
      exact lt_of_lt_of_le hδ (min_le_right _ _)
    have hbound :
        dist (approximatingCurvePath hD_closed hD_convex T hT x δ)
            (approximatingCurvePath hD_closed hD_convex T hT x ε₀) ≤
          C * dist δ ε₀ := by
      -- Split according to whether `δ` approaches `ε₀` from the left or from the right.
      by_cases hle : δ ≤ ε₀
      · simpa [C] using
          approximatingCurvePath_dist_le_left_near hD_closed hD_convex T hT x ε₀ δ hle hδρ
      · have hle' : ε₀ ≤ δ := le_of_not_ge hle
        simpa [C] using
          approximatingCurvePath_dist_le_right_near hD_closed hD_convex T hT x ε₀ δ hle' hδρ
    have hCdist_le : C * dist δ ε₀ ≤ (C + 1) * dist δ ε₀ := by
      -- Replacing `C` by `C + 1` gives a convenient upper bound compatible with the chosen
      -- radius.
      have hdist_nonneg : 0 ≤ dist δ ε₀ := dist_nonneg
      nlinarith
    have hCp1dist_lt : (C + 1) * dist δ ε₀ < η := by
      -- The radius choice forces the linear upper bound below the target tolerance.
      have hmul := mul_lt_mul_of_pos_left hδη hCp1_pos
      have hcancel : (C + 1) * (η / (C + 1)) = η := by
        field_simp [hCp1_pos.ne']
      rwa [hcancel] at hmul
    exact lt_of_le_of_lt (le_trans hbound hCdist_le) hCp1dist_lt

/-- Proposition 4.30 (14): the curve `ε ↦ x_ε` is continuous on `]0,1[`. -/
theorem approximatingCurvePath_continuous {D : Set H} (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (T : D → D) (hT : LipschitzWith 1 T) (x : D) :
    Continuous (approximatingCurvePath hD_closed hD_convex T hT x) := by
  -- Route correction: package the existing one-sided gap estimates into `ContinuousAt`, then
  -- apply the standard metric-space pointwise continuity criterion.
  rw [continuous_iff_continuousAt]
  intro ε₀
  exact
    approximatingCurvePath_continuousAt_of_two_sided_gap_bounds
      hD_closed hD_convex T hT x ε₀

-- Proof sketch: if `x` is fixed by `T`, then it satisfies the defining equation for every `ε`,
-- so uniqueness identifies each `x_ε` with `x`.
/-- Proposition 4.30 (15): if `x` is a fixed point of `T`, then the approximating curve is
constant and equal to `x`. -/
theorem approximatingCurvePoint_eq_self_of_mem_fixedPoints {D : Set H} (hD_closed : IsClosed D)
    (hD_convex : Convex ℝ D) (T : D → D) (hT : LipschitzWith 1 T)
    {x : D} (hx : x ∈ Function.fixedPoints T) :
    ∀ ε : Set.Ioo (0 : ℝ) 1, approximatingCurvePoint hD_closed hD_convex T hT ε x = x := by
  intro ε
  have hx_curve :
      (x : H) = (ε : ℝ) • (x : H) + (1 - (ε : ℝ)) • (T x : H) := by
    rw [Function.mem_fixedPoints_iff.mp hx]
    simp [add_smul]
  -- Uniqueness of the affine fixed point forces the curve to stay at `x`.
  exact
    (approximatingCurvePoint_existsUnique hD_closed hD_convex T hT ε x).unique
      (approximatingCurvePoint_eq_affine_combination hD_closed hD_convex T hT ε x)
      hx_curve

-- Proof sketch: if `x` is not fixed and `x_ε = x_δ` with `δ < ε`, then the two-parameter
-- inequality collapses to show `x = x_ε`, contradicting the fixed-point characterization.
/-- Proposition 4.30 (16): if `x` is not a fixed point of `T`, then the approximating curve is
injective. -/
theorem approximatingCurvePath_injective_of_not_mem_fixedPoints {D : Set H}
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (T : D → D)
    (hT : LipschitzWith 1 T) {x : D} (hx : x ∉ Function.fixedPoints T) :
    Injective
      (fun ε : Set.Ioo (0 : ℝ) 1 ↦ approximatingCurvePoint hD_closed hD_convex T hT ε x) :=
  by
  intro ε δ hcurve
  by_cases hEq : ε = δ
  · exact hEq
  · have hEq_val :
        (approximatingCurvePoint hD_closed hD_convex T hT ε x : H) =
          (approximatingCurvePoint hD_closed hD_convex T hT δ x : H) :=
      congrArg Subtype.val hcurve
    have hne_real : (ε : ℝ) ≠ (δ : ℝ) := by
      intro hεδ
      exact hEq (Subtype.ext hεδ)
    rcases lt_or_gt_of_ne hne_real with hlt | hgt
    · exfalso
      let xd := approximatingCurvePoint hD_closed hD_convex T hT δ x
      have hineq :=
        approximatingCurvePoint_twoParameter_inequality hD_closed hD_convex T hT δ ε x
      have hcoeff_pos : 0 < ((δ : ℝ) - (ε : ℝ)) / (1 - (δ : ℝ)) := by
        exact div_pos (sub_pos.mpr hlt) (sub_pos.mpr δ.2.2)
      have hnorm_sq_zero :
          ‖(xd : H) - (x : H)‖ ^ 2 = 0 := by
        -- If two distinct parameters yield the same point, the two-parameter inequality collapses.
        have hcollapsed :
            ((((δ : ℝ) - (ε : ℝ)) / (1 - (δ : ℝ))) ^ 2) *
                ‖(xd : H) - (x : H)‖ ^ 2 ≤ 0 := by
          simpa [xd, hEq_val] using hineq
        have hcoeff_sq_pos :
            0 < ((((δ : ℝ) - (ε : ℝ)) / (1 - (δ : ℝ))) ^ 2) := sq_pos_of_pos hcoeff_pos
        have hnorm_sq_nonneg : 0 ≤ ‖(xd : H) - (x : H)‖ ^ 2 := sq_nonneg ‖(xd : H) - (x : H)‖
        nlinarith
      have hxd_eq_x : xd = x := by
        apply Subtype.ext
        exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm_sq_zero))
      have hx_curve : x ∈ Function.fixedPoints (approximatingCurveOperator hD_closed hD_convex T hT δ) := by
        rw [Function.mem_fixedPoints_iff, approximatingCurveOperator]
        simpa [xd] using hxd_eq_x
      have hx_fixed : x ∈ Function.fixedPoints T := by
        rwa [fixedPoints_approximatingCurveOperator_eq hD_closed hD_convex T hT δ] at hx_curve
      exact hx hx_fixed
    · exfalso
      let xe := approximatingCurvePoint hD_closed hD_convex T hT ε x
      have hineq :=
        approximatingCurvePoint_twoParameter_inequality hD_closed hD_convex T hT ε δ x
      have hcoeff_pos : 0 < ((ε : ℝ) - (δ : ℝ)) / (1 - (ε : ℝ)) := by
        exact div_pos (sub_pos.mpr hgt) (sub_pos.mpr ε.2.2)
      have hnorm_sq_zero :
          ‖(xe : H) - (x : H)‖ ^ 2 = 0 := by
        -- The symmetric branch uses the same collapse with the larger parameter `ε`.
        have hcollapsed :
            ((((ε : ℝ) - (δ : ℝ)) / (1 - (ε : ℝ))) ^ 2) *
                ‖(xe : H) - (x : H)‖ ^ 2 ≤ 0 := by
          simpa [xe, hEq_val] using hineq
        have hcoeff_sq_pos :
            0 < ((((ε : ℝ) - (δ : ℝ)) / (1 - (ε : ℝ))) ^ 2) := sq_pos_of_pos hcoeff_pos
        have hnorm_sq_nonneg : 0 ≤ ‖(xe : H) - (x : H)‖ ^ 2 := sq_nonneg ‖(xe : H) - (x : H)‖
        nlinarith
      have hxe_eq_x : xe = x := by
        apply Subtype.ext
        exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm_sq_zero))
      have hx_curve : x ∈ Function.fixedPoints (approximatingCurveOperator hD_closed hD_convex T hT ε) := by
        rw [Function.mem_fixedPoints_iff, approximatingCurveOperator]
        simpa [xe] using hxe_eq_x
      have hx_fixed : x ∈ Function.fixedPoints T := by
        rwa [fixedPoints_approximatingCurveOperator_eq hD_closed hD_convex T hT ε] at hx_curve
      exact hx hx_fixed

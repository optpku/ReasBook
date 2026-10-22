/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section32_part3

open scoped Pointwise

section Chap06
section Section32

/- The pulled-back Euclidean unit ball in `Fin n → ℝ`, using `EuclideanSpace.equiv` to measure
the ambient norm by the genuine `ℓ2` norm. -/
/-- The unit Euclidean ball on `Fin n → ℝ`, measured via the `EuclideanSpace` norm. -/
def euclideanUnitBallFin (n : ℕ) : Set (Fin n → ℝ) :=
  {y | ‖(EuclideanSpace.equiv (Fin n) ℝ).symm y‖ ≤ 1}

-- Proof sketch: unfold the normal-cone inequality for the unit ball and use the supporting
-- hyperplane description of a Euclidean sphere. At a boundary point, any nonzero normal vector
-- must be collinear with the radius vector `x`, and the outward orientation forces the scalar
-- multiple to be positive.
/-- At a boundary point of the unit Euclidean ball, the nonzero Euclidean normal vectors are
exactly the positive scalar multiples of the radius vector. -/
theorem mem_normalConeAt_euclideanUnitBallFin_iff_exists_pos_smul
    {n : ℕ}
    {x xStar : Fin n → ℝ}
    (hxboundary : ‖(EuclideanSpace.equiv (Fin n) ℝ).symm x‖ = 1) :
    xStar ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' normalConeAt (euclideanUnitBallFin n) x) ∧
        xStar ≠ 0 ↔
      ∃ a : ℝ, 0 < a ∧ xStar = a • x := by
  classical
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  let X : EuclideanSpace ℝ (Fin n) := e.symm x
  let S : EuclideanSpace ℝ (Fin n) := e.symm xStar
  have hXnorm : ‖X‖ = 1 := by
    simpa [e, X] using hxboundary
  constructor
  · rintro ⟨hxNormal, hxStar_ne⟩
    have hS_ne : S ≠ 0 := by
      intro hS
      apply hxStar_ne
      have hImage := congrArg e hS
      simpa [S] using hImage
    have hSnorm_pos : 0 < ‖S‖ := norm_pos_iff.mpr hS_ne
    have hNormal :
        (dotProductEquiv ℝ (Fin n)) xStar ∈ normalConeAt (euclideanUnitBallFin n) x :=
      hxNormal
    rcases (mem_normalConeAt_iff.1 hNormal) with ⟨hxBall, hsupport⟩
    let Z : EuclideanSpace ℝ (Fin n) := (‖S‖⁻¹ : ℝ) • S
    let z : Fin n → ℝ := e Z
    have hZnorm : ‖Z‖ = 1 := by
      simp [Z, norm_smul, hSnorm_pos.ne']
    have hzBall : z ∈ euclideanUnitBallFin n := by
      change ‖e.symm z‖ ≤ 1
      simpa [z] using le_of_eq hZnorm
    have hSupportZ := hsupport z hzBall
    have hDotSupport : (xStar ⬝ᵥ (z - x) : ℝ) ≤ 0 := by
      simpa [dotProductEquiv_apply_apply] using hSupportZ
    have hDotEq :
        (xStar ⬝ᵥ (z - x) : ℝ) = inner ℝ S (Z - X) := by
      rw [dotProduct_eq_inner_euclideanSpace]
      change inner ℝ S (e.symm (z - x)) = inner ℝ S (Z - X)
      rw [map_sub]
      have hzSymm : e.symm z = Z := by simp [z]
      rw [hzSymm]
    have hInnerLe : inner ℝ S Z ≤ inner ℝ S X := by
      rw [hDotEq, inner_sub_right] at hDotSupport
      linarith
    have hInnerSZ : inner ℝ S Z = ‖S‖ := by
      simp [Z, real_inner_smul_right]
      field_simp
    have hInnerUpper : inner ℝ S X ≤ ‖S‖ := by
      have hCauchy : inner ℝ S X ≤ ‖S‖ * ‖X‖ := real_inner_le_norm S X
      simpa [hXnorm] using hCauchy
    have hInnerEq : inner ℝ S X = ‖S‖ :=
      le_antisymm hInnerUpper (by simpa [hInnerSZ] using hInnerLe)
    have hCollinear : S = ‖S‖ • X := by
      have hEqMul : inner ℝ S X = ‖S‖ * ‖X‖ := by
        simpa [hXnorm] using hInnerEq
      have hNormRelation : ‖X‖ • S = ‖S‖ • X :=
        (inner_eq_norm_mul_iff_real (x := S) (y := X)).1 hEqMul
      simpa [hXnorm] using hNormRelation
    refine ⟨‖S‖, hSnorm_pos, ?_⟩
    have hImage := congrArg e hCollinear
    simpa [S, X] using hImage
  · rintro ⟨a, ha, rfl⟩
    constructor
    · change (dotProductEquiv ℝ (Fin n)) (a • x) ∈
        normalConeAt (euclideanUnitBallFin n) x
      rw [mem_normalConeAt_iff]
      constructor
      · exact hxboundary.le
      · intro z hz
        have hzNorm : ‖e.symm z‖ ≤ 1 := hz
        have hCauchy : inner ℝ X (e.symm z) ≤ 1 := by
          calc
            inner ℝ X (e.symm z) ≤ ‖X‖ * ‖e.symm z‖ := real_inner_le_norm X (e.symm z)
            _ ≤ 1 * 1 := mul_le_mul (le_of_eq hXnorm) hzNorm (norm_nonneg _) zero_le_one
            _ = 1 := by norm_num
        have hInnerXX : inner ℝ X X = 1 := by
          simpa [real_inner_self_eq_norm_sq, hXnorm]
        have hDiff : inner ℝ X (e.symm z - X) ≤ 0 := by
          rw [inner_sub_right, hInnerXX]
          linarith
        have hEval :
            ((dotProductEquiv ℝ (Fin n)) (a • x)) (z - x) =
              a * inner ℝ X (e.symm z - X) := by
          rw [dotProductEquiv_apply_apply, dotProduct_eq_inner_euclideanSpace]
          change inner ℝ (e.symm (a • x)) (e.symm (z - x)) = _
          rw [map_smul, map_sub]
          change inner ℝ (a • X) (e.symm z - X) = _
          rw [real_inner_smul_left]
        rw [hEval]
        exact mul_nonpos_of_nonneg_of_nonpos ha.le hDiff
    · exact smul_ne_zero ha.ne' (by
        intro hx
        have : ‖X‖ = 0 := by simp [X, e, hx]
        linarith [hXnorm])

-- Proof sketch: apply Theorem 32.4 with the unit Euclidean ball as the constraint set and keep
-- the same standing hypothesis `x ∈ ri (dom f)` explicit. The theorem forces every Euclidean
-- subgradient at a nonconstant maximizer to be a nonzero normal vector to the ball, so the
-- preceding normal-cone characterization identifies that subgradient as a positive multiple of
-- `x`; nonconstancy also forces the maximizer onto the boundary `‖x‖ = 1`.
/-- Text 32.0.4: when the constraint set is the unit Euclidean ball, the normal vectors at a
boundary point are exactly the positive scalar multiples of the radius vector. Hence a
nonconstant maximum of a proper convex function over the unit ball, attained at
`x ∈ ri (dom f)`, satisfies the boundary condition `‖x‖ = 1` together with the
eigenvalue-type relation `a • x ∈ ∂f(x)` for some `a > 0`. Here the Euclidean unit ball on
`Fin n → ℝ` is pulled back along `EuclideanSpace.equiv (Fin n) ℝ`, so finiteness on the ball is
expressed by `euclideanUnitBallFin n ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f`. -/
theorem unitBall_convex_maximizer_has_positive_smul_subgradient
    {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    {x : Fin n → ℝ}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hfiniteOnBall :
      euclideanUnitBallFin n ⊆
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
    (hxri : x ∈ euclideanRelativeInterior_fin n
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))
    (hxBall : x ∈ euclideanUnitBallFin n)
    (hmax : IsMaxOn f (euclideanUnitBallFin n) x)
    (hnot_const :
      ¬ Set.EqOn f (fun _ ↦ f x) (euclideanUnitBallFin n)) :
    ‖(EuclideanSpace.equiv (Fin n) ℝ).symm x‖ = 1 ∧
      ∃ xStar ∈ euclideanSubdifferentialAt f x,
        ∃ a : ℝ, 0 < a ∧ xStar = a • x := by
  classical
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    EuclideanSpace.equiv (Fin n) ℝ
  have hBallConv : Convex ℝ (euclideanUnitBallFin n) := by
    have hClosedBallConv :
        Convex ℝ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
      convex_closedBall 0 1
    have hBallEq :
        euclideanUnitBallFin n =
          e.symm ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      ext y
      change ‖e.symm y‖ ≤ 1 ↔ dist (e.symm y) 0 ≤ 1
      rw [dist_zero_right]
    rw [hBallEq]
    exact Convex.linear_preimage hClosedBallConv e.symm.toLinearMap
  have hSub : Set.Nonempty (subdifferentialAt f x) :=
    (subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
      f hproper x).2.1 hxri |>.1
  rcases hSub with ⟨g, hg⟩
  let xStar : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm g
  have hxStar : xStar ∈ euclideanSubdifferentialAt f x := by
    simpa [xStar, euclideanSubdifferentialAt] using hg
  have hxStarNormal :=
    euclideanSubgradient_mem_normalConeAt_of_convex_maximizer
      hproper hBallConv hfiniteOnBall hxri hxBall hmax hnot_const xStar hxStar
  rcases hxStarNormal with ⟨hxStar_ne, hxStar_normal⟩
  have hxboundary : ‖e.symm x‖ = 1 := by
    let X : EuclideanSpace ℝ (Fin n) := e.symm x
    let S : EuclideanSpace ℝ (Fin n) := e.symm xStar
    have hXnorm_le : ‖X‖ ≤ 1 := by
      simpa [euclideanUnitBallFin, e, X] using hxBall
    have hS_ne : S ≠ 0 := by
      intro hS
      apply hxStar_ne
      have hImage := congrArg e hS
      simpa [S] using hImage
    have hSnorm_pos : 0 < ‖S‖ := norm_pos_iff.mpr hS_ne
    have hNormal :
        (dotProductEquiv ℝ (Fin n)) xStar ∈ normalConeAt (euclideanUnitBallFin n) x :=
      hxStar_normal
    rcases (mem_normalConeAt_iff.1 hNormal) with ⟨_, hsupport⟩
    let Z : EuclideanSpace ℝ (Fin n) := (‖S‖⁻¹ : ℝ) • S
    let z : Fin n → ℝ := e Z
    have hZnorm : ‖Z‖ = 1 := by
      simp [Z, norm_smul, hSnorm_pos.ne']
    have hzBall : z ∈ euclideanUnitBallFin n := by
      change ‖e.symm z‖ ≤ 1
      simpa [z] using le_of_eq hZnorm
    have hSupportZ := hsupport z hzBall
    have hDotSupport : (xStar ⬝ᵥ (z - x) : ℝ) ≤ 0 := by
      simpa [dotProductEquiv_apply_apply] using hSupportZ
    have hDotEq :
        (xStar ⬝ᵥ (z - x) : ℝ) = inner ℝ S (Z - X) := by
      rw [dotProduct_eq_inner_euclideanSpace]
      change inner ℝ S (e.symm (z - x)) = inner ℝ S (Z - X)
      rw [map_sub]
      have hzSymm : e.symm z = Z := by simp [z]
      rw [hzSymm]
    have hInnerLe : inner ℝ S Z ≤ inner ℝ S X := by
      rw [hDotEq, inner_sub_right] at hDotSupport
      linarith
    have hInnerSZ : inner ℝ S Z = ‖S‖ := by
      simp [Z, real_inner_smul_right]
      field_simp
    have hCauchy : inner ℝ S X ≤ ‖S‖ * ‖X‖ := real_inner_le_norm S X
    have hNormMulLe : ‖S‖ * 1 ≤ ‖S‖ * ‖X‖ := by
      calc
        ‖S‖ * 1 = inner ℝ S Z := by simp [hInnerSZ]
        _ ≤ inner ℝ S X := hInnerLe
        _ ≤ ‖S‖ * ‖X‖ := hCauchy
    have hOne_le : 1 ≤ ‖X‖ := by
      nlinarith [hNormMulLe]
    exact le_antisymm hXnorm_le hOne_le
  refine ⟨by simpa [e] using hxboundary, xStar, hxStar, ?_⟩
  exact
    (mem_normalConeAt_euclideanUnitBallFin_iff_exists_pos_smul
      (xStar := xStar) (by simpa [e] using hxboundary)).1 ⟨hxStar_normal, hxStar_ne⟩

end Section32
end Chap06

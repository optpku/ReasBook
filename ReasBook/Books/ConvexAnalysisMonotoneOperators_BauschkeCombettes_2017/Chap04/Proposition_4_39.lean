/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_35

open SubtypeFirmness

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 4.39: scaling `T` by the positive scalar `β` turns cocoercivity into
firm nonexpansiveness. -/
-- Proof sketch: multiply the cocoercive inequality by `β > 0` and simplify the scaled norm and
-- inner-product terms.
private lemma cocoerciveOn_iff_firmlyNonexpansiveOn_smul {D : Set H} {β : ℝ} (hβ : 0 < β)
    (T : D → H) :
    CocoerciveOn β D T ↔ FirmlyNonexpansiveOn D (fun x : D ↦ β • T x) := by
  rw [CocoerciveOn, firmlyNonexpansiveOn_iff]
  constructor
  · intro hT x y
    -- Multiply the cocoercive inequality by `β` so it matches the scaled firm inequality.
    have hscaled :
        β * (β * ‖T x - T y‖ ^ 2) ≤ β * inner ℝ ((x : H) - y) (T x - T y) := by
      exact mul_le_mul_of_nonneg_left (hT.2 x y) hβ.le
    have hnorm :
        ‖β • T x - β • T y‖ ^ 2 = β * (β * ‖T x - T y‖ ^ 2) := by
      calc
        ‖β • T x - β • T y‖ ^ 2 = ‖β • (T x - T y)‖ ^ 2 := by rw [smul_sub]
        _ = (β * ‖T x - T y‖) ^ 2 := by simp [norm_smul, abs_of_nonneg hβ.le]
        _ = β * (β * ‖T x - T y‖ ^ 2) := by
          rw [pow_two]
          ring
    have hinner :
        inner ℝ ((x : H) - y) (β • T x - β • T y) =
          β * inner ℝ ((x : H) - y) (T x - T y) := by
      rw [← smul_sub, real_inner_smul_right]
    rw [hnorm, hinner]
    exact hscaled
  · intro hT
    refine ⟨hβ, ?_⟩
    intro x y
    -- Simplifying the firm inequality for the scaled map leaves the cocoercive inequality.
    have hscaled := hT x y
    have hnorm :
        ‖β • T x - β • T y‖ ^ 2 = β * (β * ‖T x - T y‖ ^ 2) := by
      calc
        ‖β • T x - β • T y‖ ^ 2 = ‖β • (T x - T y)‖ ^ 2 := by rw [smul_sub]
        _ = (β * ‖T x - T y‖) ^ 2 := by simp [norm_smul, abs_of_nonneg hβ.le]
        _ = β * (β * ‖T x - T y‖ ^ 2) := by
          rw [pow_two]
          ring
    have hinner :
        inner ℝ ((x : H) - y) (β • T x - β • T y) =
          β * inner ℝ ((x : H) - y) (T x - T y) := by
      rw [← smul_sub, real_inner_smul_right]
    rw [hnorm, hinner] at hscaled
    nlinarith

/-- Helper for Proposition 4.39: the reflector of the residual map of `β • T` is exactly the
affine transform from Proposition 4.35 applied to `x ↦ x - γ • T x`, with averaging parameter
`α = γ / (2β)`. -/
-- Proof sketch: both maps simplify to `x ↦ x - 2β • T x` after clearing the scalar coefficients.
private lemma reflected_residual_smul_eq_averaging_transform {D : Set H} {β γ α : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (hα : α = γ / (2 * β)) (T : D → H) :
    reflectedMap D (residualMap D (fun x : D ↦ β • T x)) =
      fun x : D ↦ (1 - 1 / α) • (x : H) + (1 / α) • ((x : H) - γ • T x) := by
  ext x
  have hβ0 : β ≠ 0 := ne_of_gt hβ
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  -- First normalize the reflector of the residual map to the textbook expression `Id - 2βT`.
  calc
    reflectedMap D (residualMap D (fun x : D ↦ β • T x)) x
        = (x : H) - (2 * β) • T x := by
          simp [reflectedMap, residualMap, two_smul, smul_smul, sub_eq_add_neg,
            add_assoc, add_left_comm, add_comm]
    _ = (1 - 1 / α) • (x : H) + (1 / α) • ((x : H) - γ • T x) := by
      rw [hα]
      have hsum : (1 - 1 / (γ / (2 * β))) + 1 / (γ / (2 * β)) = (1 : ℝ) := by
        field_simp [hβ0, hγ0]
        ring
      have hcoeff : (1 / (γ / (2 * β))) * γ = 2 * β := by
        field_simp [hβ0, hγ0]
      calc
        (x : H) - (2 * β) • T x
            = (1 : ℝ) • (x : H) - (2 * β) • T x := by simp
        _ =
            ((1 - 1 / (γ / (2 * β))) + 1 / (γ / (2 * β))) • (x : H) -
              ((1 / (γ / (2 * β))) * γ) • T x := by
            rw [hsum, hcoeff]
        _ =
            (1 - 1 / (γ / (2 * β))) • (x : H) +
              (1 / (γ / (2 * β))) • ((x : H) - γ • T x) := by
            simp [sub_eq_add_neg, smul_smul, add_assoc, add_left_comm, add_comm,
              add_smul]

-- Proof sketch: combine the `β`-cocoercive iff `1 / 2`-averaged characterization for
-- `x ↦ β • T x` with the affine characterization of averaged maps. Rewriting the averaging
-- parameter from `1 / 2` to `γ / (2 * β)` identifies the companion map with `fun x ↦ x - γ • T x`.
/-- Proposition 4.39: on a subset `D` of a real inner product space, a map `T : D → H` is
`β`-cocoercive if and only if the map `x ↦ x - γ • T x` is `γ / (2 * β)`-averaged whenever
`0 < β` and `γ ∈ ]0, 2β[`. -/
theorem cocoerciveOn_iff_averagedWith_id_sub_smul
    {D : Set H} {β γ : ℝ} (hβ : 0 < β)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) (2 * β)) (T : D → H) :
    CocoerciveOn β D T ↔
      AveragedWith (γ / (2 * β)) (fun x : D ↦ (x : H) - γ • T x) := by
  let α : ℝ := γ / (2 * β)
  let S : D → H := fun x : D ↦ β • T x
  let R : D → H := residualMap D S
  let U : D → H := fun x : D ↦ (x : H) - γ • T x
  have htwoβ : 0 < 2 * β := by
    nlinarith
  have hαmem : α ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · -- The averaging parameter is positive because both `γ` and `2β` are positive.
      dsimp [α]
      exact div_pos hγ.1 htwoβ
    · -- The upper bound `γ < 2β` is exactly the condition `γ / (2β) < 1`.
      dsimp [α]
      exact (div_lt_one htwoβ).2 hγ.2
  have htransform :
      reflectedMap D R =
        fun x : D ↦ (1 - 1 / α) • (x : H) + (1 / α) • U x := by
    -- This is the affine bridge between Proposition 4.4 and Proposition 4.35.
    have htransform' :
        reflectedMap D R =
          fun x : D ↦
            (1 - 1 / (γ / (2 * β))) • (x : H) + (1 / (γ / (2 * β))) • U x := by
      simpa [S, R, U] using
        reflected_residual_smul_eq_averaging_transform hβ hγ.1 rfl T
    simpa [α] using
      htransform'
  constructor
  · intro hT
    -- The source proof first rescales `T` to a firmly nonexpansive map.
    have hFirmS : FirmlyNonexpansiveOn D S := by
      simpa [S] using
        (cocoerciveOn_iff_firmlyNonexpansiveOn_smul hβ T).mp hT
    -- Proposition 4.4 passes firm nonexpansiveness to the residual map.
    have hFirmR : FirmlyNonexpansiveOn D R := by
      exact (firmlyNonexpansiveOn_residualMap_iff D S).2 hFirmS
    -- Applying Proposition 4.4 again turns the residual into a nonexpansive reflector.
    have hReflect :
        ∀ x y : D, ‖reflectedMap D R x - reflectedMap D R y‖ ≤ ‖(x : H) - y‖ := by
      exact (reflectedMap_nonexpansive_iff_firmlyNonexpansiveOn D R).2 hFirmR
    have hAffinePairwise :
        ∀ x y : D,
          ‖((1 - 1 / α) • (x : H) + (1 / α) • U x) -
              ((1 - 1 / α) • (y : H) + (1 / α) • U y)‖ ≤ ‖(x : H) - y‖ := by
      -- Rewrite the reflector into the affine transform from Proposition 4.35.
      simpa [htransform] using hReflect
    have hAffineLip :
        LipschitzWith 1 (fun x : D ↦ (1 - 1 / α) • (x : H) + (1 / α) • U x) := by
      -- Pairwise nonexpansiveness is the same as `LipschitzWith 1` on the subtype domain.
      refine LipschitzWith.of_dist_le_mul ?_
      intro x y
      simpa [Subtype.dist_eq, dist_eq_norm] using hAffinePairwise x y
    have hAvgWith : AveragedWith α U := by
      -- Proposition 4.35 recognizes this affine transform as the averagedness criterion.
      exact (List.TFAE.out (averagedWith_tfae α hαmem U) 1 0).mp hAffineLip
    exact hAvgWith
  · intro hT
    have hAffineLip :
        LipschitzWith 1 (fun x : D ↦ (1 - 1 / α) • (x : H) + (1 / α) • U x) := by
      -- Proposition 4.35 turns averagedness back into nonexpansiveness of the affine transform.
      exact (List.TFAE.out (averagedWith_tfae α hαmem U) 0 1).mp hT
    have hAffinePairwise :
        ∀ x y : D,
          ‖((1 - 1 / α) • (x : H) + (1 / α) • U x) -
              ((1 - 1 / α) • (y : H) + (1 / α) • U y)‖ ≤ ‖(x : H) - y‖ := by
      intro x y
      simpa [Subtype.dist_eq, dist_eq_norm] using hAffineLip.dist_le_mul x y
    have hReflect :
        ∀ x y : D, ‖reflectedMap D R x - reflectedMap D R y‖ ≤ ‖(x : H) - y‖ := by
      -- Rewrite the affine transform back into the reflector of the residual map.
      simpa [htransform] using hAffinePairwise
    have hFirmR : FirmlyNonexpansiveOn D R := by
      -- Proposition 4.4 recovers firm nonexpansiveness of the residual map.
      exact (reflectedMap_nonexpansive_iff_firmlyNonexpansiveOn D R).1 hReflect
    have hFirmS : FirmlyNonexpansiveOn D S := by
      -- Applying Proposition 4.4 once more returns to the scaled operator `β • T`.
      exact (firmlyNonexpansiveOn_residualMap_iff D S).1 hFirmR
    -- Undo the scaling bridge to recover cocoercivity of `T`.
    simpa [S] using
      (cocoerciveOn_iff_firmlyNonexpansiveOn_smul hβ T).mpr hFirmS

end

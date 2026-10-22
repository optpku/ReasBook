/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.FirmlyNonexpansiveOn
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_33
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_4

open SubtypeFirmness

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Remark 4.34 (1): every averaged map on a subset of a real Hilbert space is nonexpansive. -/
theorem lipschitzWith_one_of_averagedWith {D : Set H} {α : ℝ} {T : D → H}
    (hT : AveragedWith α T) : LipschitzWith 1 T := by
  rcases averagedWith_iff.mp hT with ⟨hα, R, hR, hT_eq⟩
  have hα_nonneg : 0 ≤ α := hα.1.le
  have h_one_sub_nonneg : 0 ≤ 1 - α := sub_nonneg.mpr hα.2.le
  -- Control the averaged companion by the given nonexpansive witness.
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  have hRxy : ‖R x - R y‖ ≤ ‖(x : H) - y‖ := by
    simpa [Subtype.dist_eq, dist_eq_norm] using hR.dist_le_mul x y
  have hxy :
      T x - T y = (1 - α) • ((x : H) - y) + α • (R x - R y) := by
    -- Rewrite the affine representation pointwise and collect the two differences.
    calc
      T x - T y
          = ((1 - α) • (x : H) + α • R x) - ((1 - α) • (y : H) + α • R y) := by
              rw [hT_eq]
      _ = (1 - α) • ((x : H) - y) + α • (R x - R y) := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  -- The triangle inequality and the witness bound collapse the convex combination to `‖x - y‖`.
  simpa [Subtype.dist_eq, dist_eq_norm, one_mul] using
    calc
      ‖T x - T y‖ = ‖(1 - α) • ((x : H) - y) + α • (R x - R y)‖ := by rw [hxy]
      _ ≤ ‖(1 - α) • ((x : H) - y)‖ + ‖α • (R x - R y)‖ := norm_add_le _ _
      _ = (1 - α) * ‖(x : H) - y‖ + α * ‖R x - R y‖ := by
            rw [norm_smul, norm_smul]
            simp [Real.norm_eq_abs, abs_of_nonneg h_one_sub_nonneg, abs_of_nonneg hα_nonneg]
      _ ≤ (1 - α) * ‖(x : H) - y‖ + α * ‖(x : H) - y‖ := by
            nlinarith [hRxy, norm_nonneg ((x : H) - y)]
      _ = ‖(x : H) - y‖ := by ring

/-- Helper for Remark 4.34: `1 / 2`-averagedness is exactly nonexpansiveness of the reflected
map `2T - Id`. -/
private lemma averagedWith_half_iff_reflectedMap_pairwise_nonexpansive {D : Set H} (T : D → H) :
    AveragedWith (1 / 2 : ℝ) T ↔
      ∀ x y : D, ‖reflectedMap D T x - reflectedMap D T y‖ ≤ ‖(x : H) - y‖ := by
  constructor
  · intro hT
    rcases averagedWith_iff.mp hT with ⟨hhalf, R, hR, hT_eq⟩
    intro x y
    have hreflect_eq : reflectedMap D T = R := by
      -- For the special weight `1 / 2`, the averaged companion is exactly the reflector `2T - Id`.
      funext z
      calc
        reflectedMap D T z = (2 : ℝ) • T z - z := rfl
        _ = (2 : ℝ) • ((1 - (1 / 2 : ℝ)) • (z : H) + (1 / 2 : ℝ) • R z) - z := by
              rw [hT_eq]
        _ = R z := by
              have hhalf_eq : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by norm_num
              rw [hhalf_eq, smul_add, smul_smul, smul_smul]
              norm_num
    -- After identifying the reflector with `R`, reuse the original nonexpansive witness.
    simpa [hreflect_eq, Subtype.dist_eq, dist_eq_norm] using hR.dist_le_mul x y
  · intro hT
    have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
      norm_num
    have hR : LipschitzWith 1 (reflectedMap D T) := by
      -- Convert the pairwise norm estimate into the standard Lipschitz form on the subtype domain.
      refine LipschitzWith.of_dist_le_mul ?_
      intro x y
      simpa [Subtype.dist_eq, dist_eq_norm, one_mul] using hT x y
    refine averagedWith_iff.mpr ⟨hhalf, reflectedMap D T, hR, ?_⟩
    -- Reconstruct the averaged decomposition from the explicit reflected map formula.
    funext x
    have hsmul : (1 / 2 : ℝ) • ((2 : ℝ) • T x) = T x := by
      rw [smul_smul]
      norm_num
    calc
      T x = (1 / 2 : ℝ) • ((2 : ℝ) • T x) := by rw [hsmul]
      _ = (1 - (1 / 2 : ℝ)) • (x : H) + (1 / 2 : ℝ) • reflectedMap D T x := by
            rw [reflectedMap, smul_sub, hsmul]
            norm_num

/-- Remark 4.34 (2): a map on a subset of a real Hilbert space is firmly nonexpansive if and
only if it is `1 / 2`-averaged. -/
theorem firmlyNonexpansiveOn_iff_averagedWith_half {D : Set H} (T : D → H) :
    FirmlyNonexpansiveOn D T ↔ AveragedWith (1 / 2 : ℝ) T := by
  -- Route correction: use the earlier reflector criterion from Proposition 4.4 rather than the
  -- later TFAE package for averaged maps.
  calc
    FirmlyNonexpansiveOn D T ↔
        ∀ x y : D, ‖reflectedMap D T x - reflectedMap D T y‖ ≤ ‖(x : H) - y‖ := by
          exact (reflectedMap_nonexpansive_iff_firmlyNonexpansiveOn D T).symm
    _ ↔ AveragedWith (1 / 2 : ℝ) T := by
      exact averagedWith_half_iff_reflectedMap_pairwise_nonexpansive T |>.symm

/-- On the whole space, a self-map is firmly nonexpansive if and only if it is `1 / 2`-averaged. -/
theorem firmlyNonexpansive_iff_averaged_half {T : H → H} :
    FirmlyNonexpansive T ↔ Averaged (1 / 2 : ℝ) T := by
  simpa using
    (firmlyNonexpansiveOn_iff_averagedWith_half (fun x : (Set.univ : Set H) ↦ T x))

/-- Helper for Remark 4.34(3): scaling by a positive scalar turns cocoercivity into firm
nonexpansiveness. -/
private lemma cocoerciveOn_iff_firmlyNonexpansiveOn_smul {D : Set H} {β : ℝ} (hβ : 0 < β)
    (T : D → H) :
    CocoerciveOn β D T ↔ FirmlyNonexpansiveOn D (fun x : D ↦ β • T x) := by
  rw [CocoerciveOn, firmlyNonexpansiveOn_iff]
  constructor
  · rintro ⟨_, hT⟩ x y
    -- Multiply the cocoercive inequality by `β` and rewrite the scaled norm and inner product.
    have hscaled :
        β * (β * ‖T x - T y‖ ^ 2) ≤ β * inner ℝ ((x : H) - y) (T x - T y) := by
      exact mul_le_mul_of_nonneg_left (hT x y) hβ.le
    have hnorm :
        ‖β • T x - β • T y‖ ^ 2 = β * (β * ‖T x - T y‖ ^ 2) := by
      calc
        ‖β • T x - β • T y‖ ^ 2 = ‖β • (T x - T y)‖ ^ 2 := by rw [smul_sub]
        _ = (β * ‖T x - T y‖) ^ 2 := by
              simp [norm_smul, abs_of_nonneg hβ.le]
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
    -- The same identities run backwards, and positivity of `β` lets `nlinarith` divide it out.
    have hscaled := hT x y
    have hnorm :
        ‖β • T x - β • T y‖ ^ 2 = β * (β * ‖T x - T y‖ ^ 2) := by
      calc
        ‖β • T x - β • T y‖ ^ 2 = ‖β • (T x - T y)‖ ^ 2 := by rw [smul_sub]
        _ = (β * ‖T x - T y‖) ^ 2 := by
              simp [norm_smul, abs_of_nonneg hβ.le]
        _ = β * (β * ‖T x - T y‖ ^ 2) := by
              rw [pow_two]
              ring
    have hinner :
        inner ℝ ((x : H) - y) (β • T x - β • T y) =
          β * inner ℝ ((x : H) - y) (T x - T y) := by
      rw [← smul_sub, real_inner_smul_right]
    rw [hnorm, hinner] at hscaled
    nlinarith

/-- Remark 4.34 (3): for `β > 0`, a map on a subset of a real Hilbert space is `β`-cocoercive if
and only if the scaled map `x ↦ β • T x` is `1 / 2`-averaged. -/
theorem cocoerciveOn_iff_smul_averagedWith_half {D : Set H} {β : ℝ} (hβ : 0 < β) (T : D → H) :
    CocoerciveOn β D T ↔ AveragedWith (1 / 2 : ℝ) (fun x : D ↦ β • T x) := by
  -- Normalize to firm nonexpansiveness after scaling, then apply the half-averaged criterion.
  calc
    CocoerciveOn β D T ↔ FirmlyNonexpansiveOn D (fun x : D ↦ β • T x) := by
      exact cocoerciveOn_iff_firmlyNonexpansiveOn_smul hβ T
    _ ↔ AveragedWith (1 / 2 : ℝ) (fun x : D ↦ β • T x) := by
      exact firmlyNonexpansiveOn_iff_averagedWith_half (fun x : D ↦ β • T x)

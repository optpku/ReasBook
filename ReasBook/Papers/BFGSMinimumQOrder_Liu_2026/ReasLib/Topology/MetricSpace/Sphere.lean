module

public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Topology.MetricSpace.HausdorffDistance

public section

universe u v

namespace Metric

/-- The distance from a point to a nonempty sphere in a real normed affine space is the
absolute radial deviation from that sphere. -/
theorem infDist_sphere {V : Type u} {P : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] [Nontrivial V] (x C : P) (R : ℝ) (hR : 0 ≤ R) :
    infDist x (sphere C R) = |dist x C - R| := by
  -- Translate a nonempty sphere in the model vector space to the affine center `C`.
  have sphereNonempty : (sphere C R).Nonempty := by
    have zeroSphereNonempty : (sphere (0 : V) R).Nonempty :=
      NormedSpace.sphere_nonempty.mpr hR
    obtain ⟨v, hv⟩ := zeroSphereNonempty
    have translatedPointMem : v +ᵥ C ∈ sphere C R := by
      rw [mem_sphere, dist_vadd_left]
      simpa only [mem_sphere, dist_zero_right] using hv
    exact ⟨v +ᵥ C, translatedPointMem⟩
  apply le_antisymm
  · -- A radial point realizes the claimed distance; the center is handled separately.
    by_cases hx : x = C
    · subst x
      obtain ⟨y, hy⟩ := sphereNonempty
      calc
        infDist C (sphere C R) ≤ dist C y := infDist_le_dist_of_mem hy
        _ = R := by simpa [dist_comm] using (mem_sphere.mp hy)
        _ = |dist C C - R| := by rw [dist_self, zero_sub, abs_neg, abs_of_nonneg hR]
    · have hdist : 0 < dist C x := dist_pos.mpr (Ne.symm hx)
      have radialPointMem : AffineMap.lineMap C x (R / dist C x) ∈ sphere C R := by
        rw [mem_sphere, dist_lineMap_left, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg hR hdist.le), div_mul_cancel₀ R hdist.ne']
      have radialPointDist :
          dist x (AffineMap.lineMap C x (R / dist C x)) = |dist x C - R| := by
        rw [dist_right_lineMap, Real.norm_eq_abs]
        calc
          |1 - R / dist C x| * dist C x =
              |1 - R / dist C x| * |dist C x| := by rw [abs_of_pos hdist]
          _ = |(1 - R / dist C x) * dist C x| := (abs_mul _ _).symm
          _ = |dist C x - R| := by rw [sub_mul, one_mul, div_mul_cancel₀ R hdist.ne']
          _ = |dist x C - R| := by rw [dist_comm C x]
      calc
        infDist x (sphere C R) ≤
            dist x (AffineMap.lineMap C x (R / dist C x)) :=
          infDist_le_dist_of_mem radialPointMem
        _ = |dist x C - R| := radialPointDist
  · -- The reverse triangle inequality bounds every point of the sphere from below.
    refine (le_infDist sphereNonempty).mpr ?_
    intro y hy
    rw [← mem_sphere.mp hy]
    exact abs_dist_sub_le x y C

/-- The affine image of the unit sphere with center `C` and positive scale `R` is the
metric sphere of radius `R` about `C`. -/
theorem affinity_unitSphere {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : E) (R : ℝ) (hR : 0 < R) :
    (fun v : E ↦ C + R • v) '' sphere 0 1 = sphere C R := by
  -- Factor the affine parametrization into scaling followed by translation.
  have affinityFactorization :
      (fun v : E ↦ C + R • v) = (IsometryEquiv.vaddConst C) ∘ (R • ·) := by
    funext v
    simp only [Function.comp_apply, IsometryEquiv.vaddConst_apply, vadd_eq_add, add_comm]
  -- Scaling sends the unit sphere to radius `R`, and translation moves its center to `C`.
  rw [affinityFactorization, Set.image_comp, Set.image_smul, smul_sphere' hR.ne',
    IsometryEquiv.image_sphere]
  simp only [smul_zero, Real.norm_eq_abs, abs_of_pos hR, mul_one,
    IsometryEquiv.vaddConst_apply, zero_vadd]

/-- The distance from a point to the affine image of a unit sphere with positive scale is
the absolute difference between its distance from the center and the scale. -/
theorem infDist_affinity_unitSphere {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] (x C : E) (R : ℝ) (hR : 0 < R) :
    infDist x ((fun v : E ↦ C + R • v) '' sphere 0 1) = |‖x - C‖ - R| := by
  -- Rewrite the affine image as a metric sphere, then use the radial-distance formula.
  rw [affinity_unitSphere C R hR, infDist_sphere x C R hR.le, dist_eq_norm]

end Metric

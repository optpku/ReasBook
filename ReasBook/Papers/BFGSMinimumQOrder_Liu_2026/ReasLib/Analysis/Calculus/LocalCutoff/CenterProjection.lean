module

public import ReasLib.Analysis.Calculus.Deriv.GlobalDiffeomorph
public import ReasLib.Analysis.Calculus.Deriv.GlobalInverseBounds
public import ReasLib.Analysis.Calculus.LocalCutoff.CenterStable
public import ReasLib.Topology.ContinuousMap.SmallLipschitzGraph
public import Mathlib.Analysis.Calculus.MeanValue

public section

noncomputable section

open scoped NNReal

universe u

namespace LocalCutoff.CenterProjection

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {radius slope : ℝ≥0}

/-- The center coordinate of the cutoff-modified center-stable map along a small graph. -/
def map (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X) (ζ : SmallLipschitzGraph X radius slope) : ℝ → ℝ :=
  fun u ↦ (LocalCutoff.centerStableLinearize χ ρ L N (u, ζ u)).1

/-- The center projection evaluates as the first coordinate of the cutoff-modified
center-stable map along the graph. -/
theorem map_apply (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X) (ζ : SmallLipschitzGraph X radius slope) (u : ℝ) :
    map χ ρ L N ζ u =
      (LocalCutoff.centerStableLinearize χ ρ L N (u, ζ u)).1 := by
  rfl

/-- The deterministic inverse of the center projection selected by `Function.invFun`. -/
def inverse (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X) (ζ : SmallLipschitzGraph X radius slope) : ℝ → ℝ :=
  Function.invFun (map χ ρ L N ζ)

/-- The center-projection inverse is definitionally the inverse selected by
`Function.invFun`. -/
theorem inverse_def (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X) (ζ : SmallLipschitzGraph X radius slope) :
    inverse χ ρ L N ζ = Function.invFun (map χ ρ L N ζ) := by
  rfl

/-- A compactly supported cutoff has a common bounded interval outside which every
center projection along a uniformly bounded small graph is the identity. -/
theorem eq_id_of_abs_ge (χ : ℝ × X → ℝ) (ρ : ℝ) (L : X →L[ℝ] X)
    (N : ℝ × X → ℝ × X) (hρ : ρ ≠ 0) (hχ : HasCompactSupport χ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (ζ : SmallLipschitzGraph X radius slope) u,
      R ≤ |u| → map χ ρ L N ζ u = u := by
  obtain ⟨r, hr_pos, hr⟩ := hχ.isBounded.subset_ball_lt 0 (0 : ℝ × X)
  refine ⟨|ρ| * r, mul_nonneg (abs_nonneg ρ) hr_pos.le, ?_⟩
  intro ζ u hu
  rw [map_apply]
  have hscaled_notMem : ρ⁻¹ • (u, ζ u) ∉ tsupport χ := by
    intro hmem
    have hscaled_mem : ρ⁻¹ • (u, ζ u) ∈ Metric.ball (0 : ℝ × X) r := hr hmem
    have hscaled_norm : ‖ρ⁻¹ • (u, ζ u)‖ < r := by
      simpa only [Metric.mem_ball, dist_zero_right] using hscaled_mem
    have hrho_abs : 0 < |ρ| := abs_pos.mpr hρ
    have hrestore : ρ • (ρ⁻¹ • (u, ζ u)) = (u, ζ u) := by
      rw [smul_smul, mul_inv_cancel₀ hρ, one_smul]
    have hpoint_norm : ‖(u, ζ u)‖ < |ρ| * r := by
      calc
        ‖(u, ζ u)‖ = ‖ρ • (ρ⁻¹ • (u, ζ u))‖ := congrArg norm hrestore.symm
        _ = |ρ| * ‖ρ⁻¹ • (u, ζ u)‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ < |ρ| * r := mul_lt_mul_of_pos_left hscaled_norm hrho_abs
    have hu_lt : |u| < |ρ| * r := by
      calc
        |u| = ‖u‖ := (Real.norm_eq_abs u).symm
        _ ≤ ‖(u, ζ u)‖ := norm_fst_le (u, ζ u)
        _ < |ρ| * r := hpoint_norm
    exact (not_lt_of_ge hu) hu_lt
  have hzero : χ (ρ⁻¹ • (u, ζ u)) = 0 := image_eq_zero_of_notMem_tsupport hscaled_notMem
  rw [LocalCutoff.centerStableLinearize_apply, hzero, zero_smul, add_zero,
    LocalCutoff.centerStable_apply]

end LocalCutoff.CenterProjection

module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import ReasLib.Analysis.Calculus.ContDiff.SupportBounds

public section

noncomputable section

open Set
open scoped ContDiff

universe u

namespace SmoothCutoff

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A smooth cutoff centered at `c`, equal to one on the inner closed ball and supported
in the outer ball. -/
noncomputable def centeredBump (c : E) (rIn rOut : ℝ) (hrIn : 0 < rIn)
    (hr : rIn < rOut) : E → ℝ :=
  (⟨rIn, rOut, hrIn, hr⟩ : ContDiffBump c)

/-- The centered cutoff is infinitely differentiable. -/
theorem contDiff_centeredBump (c : E) (rIn rOut : ℝ) (hrIn : 0 < rIn)
    (hr : rIn < rOut) : ContDiff ℝ ∞ (centeredBump c rIn rOut hrIn hr) := by
  simpa only [centeredBump] using
    (⟨rIn, rOut, hrIn, hr⟩ : ContDiffBump c).contDiff

/-- The centered cutoff equals one on its inner closed ball. -/
theorem centeredBump_eq_one_of_mem_closedBall (c : E) (rIn rOut : ℝ)
    (hrIn : 0 < rIn) (hr : rIn < rOut) {x : E}
    (hx : x ∈ Metric.closedBall c rIn) : centeredBump c rIn rOut hrIn hr x = 1 := by
  simpa only [centeredBump] using
    (⟨rIn, rOut, hrIn, hr⟩ : ContDiffBump c).one_of_mem_closedBall hx

/-- The topological support of the centered cutoff is its outer closed ball. -/
theorem tsupport_centeredBump (c : E) (rIn rOut : ℝ) (hrIn : 0 < rIn)
    (hr : rIn < rOut) :
    tsupport (centeredBump c rIn rOut hrIn hr) = Metric.closedBall c rOut := by
  simpa only [centeredBump] using
    (⟨rIn, rOut, hrIn, hr⟩ : ContDiffBump c).tsupport_eq

/-- The function support of the centered cutoff is its outer open ball. -/
theorem support_centeredBump (c : E) (rIn rOut : ℝ) (hrIn : 0 < rIn)
    (hr : rIn < rOut) :
    Function.support (centeredBump c rIn rOut hrIn hr) = Metric.ball c rOut := by
  simpa only [centeredBump] using
    (⟨rIn, rOut, hrIn, hr⟩ : ContDiffBump c).support_eq

/-- The centered cutoff takes values in the unit interval. -/
theorem centeredBump_nonneg_le_one (c : E) (rIn rOut : ℝ) (hrIn : 0 < rIn)
    (hr : rIn < rOut) (x : E) :
    0 ≤ centeredBump c rIn rOut hrIn hr x ∧ centeredBump c rIn rOut hrIn hr x ≤ 1 := by
  constructor
  · simpa only [centeredBump] using
      (⟨rIn, rOut, hrIn, hr⟩ : ContDiffBump c).nonneg' x
  · simpa only [centeredBump] using
      (⟨rIn, rOut, hrIn, hr⟩ : ContDiffBump c).le_one

/-- In finite-dimensional spaces the centered cutoff has compact support. -/
theorem hasCompactSupport_centeredBump [FiniteDimensional ℝ E] (c : E) (rIn rOut : ℝ)
    (hrIn : 0 < rIn) (hr : rIn < rOut) :
    HasCompactSupport (centeredBump c rIn rOut hrIn hr) := by
  simpa only [centeredBump] using
    (⟨rIn, rOut, hrIn, hr⟩ : ContDiffBump c).hasCompactSupport

/-- Every fixed iterated derivative of a finite-dimensional centered cutoff has a global
nonnegative norm bound. -/
theorem exists_norm_iteratedFDeriv_centeredBump_le [FiniteDimensional ℝ E] (n : ℕ)
    (c : E) (rIn rOut : ℝ) (hrIn : 0 < rIn) (hr : rIn < rOut) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      ‖iteratedFDeriv ℝ n (centeredBump c rIn rOut hrIn hr) x‖ ≤ C := by
  exact HasCompactSupport.exists_norm_iteratedFDeriv_le
    (hasCompactSupport_centeredBump c rIn rOut hrIn hr)
    ((contDiff_centeredBump c rIn rOut hrIn hr).of_le (mod_cast le_top))

/-- The first derivative of a finite-dimensional centered cutoff has a global norm bound. -/
theorem exists_norm_fderiv_centeredBump_le [FiniteDimensional ℝ E] (c : E) (rIn rOut : ℝ)
    (hrIn : 0 < rIn) (hr : rIn < rOut) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖fderiv ℝ (centeredBump c rIn rOut hrIn hr) x‖ ≤ C := by
  exact HasCompactSupport.exists_norm_fderiv_le
    (hasCompactSupport_centeredBump c rIn rOut hrIn hr)
    ((contDiff_centeredBump c rIn rOut hrIn hr).of_le (mod_cast le_top))

/-- The second derivative of a finite-dimensional centered cutoff has a global norm bound. -/
theorem exists_norm_secondFDeriv_centeredBump_le [FiniteDimensional ℝ E] (c : E)
    (rIn rOut : ℝ) (hrIn : 0 < rIn) (hr : rIn < rOut) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      ‖fderiv ℝ (fderiv ℝ (centeredBump c rIn rOut hrIn hr)) x‖ ≤ C := by
  exact HasCompactSupport.exists_norm_secondFDeriv_le
    (hasCompactSupport_centeredBump c rIn rOut hrIn hr)
    ((contDiff_centeredBump c rIn rOut hrIn hr).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))

end SmoothCutoff

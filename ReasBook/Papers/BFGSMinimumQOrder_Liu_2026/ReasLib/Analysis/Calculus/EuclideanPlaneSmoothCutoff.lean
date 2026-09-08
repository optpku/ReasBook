module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

public section

noncomputable section

open Set
open scoped ContDiff

namespace EuclideanPlane

/-- A fixed smooth cutoff on the real Euclidean plane, obtained by evaluating the
canonical bump after dilation by a factor of three. -/
def smoothCutoff : EuclideanSpace ℝ (Fin 2) → ℝ :=
  fun x ↦ (default : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2))) (3 • x)

/-- The natural-number dilation in `smoothCutoff` agrees with dilation by the real scalar three. -/
private lemma smoothCutoff_eq_realDilation : smoothCutoff = fun x ↦
    (default : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2))) ((3 : ℝ) • x) := by
  funext x
  -- Move the elaborated natural scalar multiplication to its canonical real-module spelling.
  unfold smoothCutoff
  exact congrArg (default : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2)))
    (Nat.cast_smul_eq_nsmul ℝ 3 x).symm

/-- The planar cutoff is infinitely differentiable. -/
theorem contDiff_smoothCutoff : ContDiff ℝ ∞ smoothCutoff := by
  -- Compose the smooth canonical bump with the smooth dilation by three.
  exact (default : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2))).contDiff.comp
    (contDiff_const_smul 3)

/-- The planar cutoff has compact topological support. -/
theorem hasCompactSupport_smoothCutoff : HasCompactSupport smoothCutoff := by
  -- A nonzero scalar dilation preserves compact support.
  have hThree : (3 : ℝ) ≠ 0 := by
    norm_num
  rw [smoothCutoff_eq_realDilation]
  exact (default : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2))).hasCompactSupport.comp_smul
    hThree

/-- The topological support of the planar cutoff lies in the open unit ball. -/
theorem tsupport_smoothCutoff_subset : tsupport smoothCutoff ⊆ Metric.ball 0 1 := by
  intro x hx
  -- Transport support through the dilation homeomorphism and use the bump's outer radius two.
  have hThree : (3 : ℝ) ≠ 0 := by
    norm_num
  have hThreeNonneg : (0 : ℝ) ≤ 3 := by
    norm_num
  rw [smoothCutoff_eq_realDilation] at hx
  have hx' : (3 : ℝ) • x ∈
      tsupport (default : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2))) :=
    (Set.ext_iff.mp
      (tsupport_comp_eq_preimage
        (default : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2)))
        (Homeomorph.smulOfNeZero (3 : ℝ) hThree)) x).mp hx
  rw [ContDiffBump.tsupport_eq] at hx'
  have hOuterRadius :
      (default : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2))).rOut = 2 := rfl
  rw [hOuterRadius] at hx'
  -- The resulting estimate `3 * ‖x‖ ≤ 2` is stronger than `‖x‖ < 1`.
  simp only [Metric.mem_closedBall, Metric.mem_ball, dist_zero_right,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hThreeNonneg] at hx' ⊢
  linarith

/-- The planar cutoff equals one on the closed ball of radius one third. -/
theorem smoothCutoff_eq_one (x : EuclideanSpace ℝ (Fin 2))
    (hx : x ∈ Metric.closedBall 0 (1 / 3 : ℝ)) : smoothCutoff x = 1 := by
  -- Dilation carries the one-third ball into the canonical bump's inner unit ball.
  have hThreeNonneg : (0 : ℝ) ≤ 3 := by
    norm_num
  rw [smoothCutoff_eq_realDilation]
  apply (default : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2))).one_of_mem_closedBall
  have hInnerRadius :
      (default : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2))).rIn = 1 := rfl
  rw [hInnerRadius]
  simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hThreeNonneg] at hx ⊢
  norm_num at hx ⊢
  linarith

/-- The supremum of the norms of the values of the `n`-th iterated derivative of
the planar cutoff. -/
def smoothCutoffDerivBound (n : ℕ) : ℝ :=
  sSup (range fun x ↦ ‖iteratedFDeriv ℝ n smoothCutoff x‖)

/-- The range of the norm of each iterated derivative of `smoothCutoff` is bounded above. -/
private lemma smoothCutoffDerivRange_bddAbove (n : ℕ) :
    BddAbove (range fun x ↦ ‖iteratedFDeriv ℝ n smoothCutoff x‖) := by
  -- Smoothness gives continuity, while compact support propagates to every iterated derivative.
  obtain ⟨C, hC⟩ := Continuous.bounded_above_of_compact_support
    (contDiff_smoothCutoff.continuous_iteratedFDeriv (mod_cast le_top))
    (hasCompactSupport_smoothCutoff.iteratedFDeriv n)
  -- The pointwise estimate supplied by compact support is exactly an upper bound on the range.
  refine ⟨C, ?_⟩
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  exact hC x

/-- Every iterated-derivative bound of the planar cutoff is nonnegative. -/
theorem smoothCutoffDerivBound_nonneg (n : ℕ) : 0 ≤ smoothCutoffDerivBound n := by
  rw [smoothCutoffDerivBound]
  -- Compare the supremum with the nonnegative norm attained at the origin.
  calc
    0 ≤ ‖iteratedFDeriv ℝ n smoothCutoff (0 : EuclideanSpace ℝ (Fin 2))‖ := norm_nonneg _
    _ ≤ sSup (range fun x ↦ ‖iteratedFDeriv ℝ n smoothCutoff x‖) :=
      le_csSup (smoothCutoffDerivRange_bddAbove n) (mem_range_self 0)

/-- The `n`-th iterated derivative of the planar cutoff is globally bounded by
its supremum-defined bound. -/
theorem norm_iteratedFDeriv_smoothCutoff_le (n : ℕ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ‖iteratedFDeriv ℝ n smoothCutoff x‖ ≤ smoothCutoffDerivBound n := by
  rw [smoothCutoffDerivBound]
  -- Every value of the derivative-norm function lies below the supremum of its bounded range.
  exact le_csSup (smoothCutoffDerivRange_bddAbove n) (mem_range_self x)

/-- The values of the planar cutoff are globally bounded by its order-zero bound. -/
theorem norm_smoothCutoff_le (x : EuclideanSpace ℝ (Fin 2)) :
    ‖smoothCutoff x‖ ≤ smoothCutoffDerivBound 0 := by
  -- At order zero, the iterated derivative norm is the value norm.
  simpa only [norm_iteratedFDeriv_zero] using norm_iteratedFDeriv_smoothCutoff_le 0 x

/-- The first derivative of the planar cutoff is globally bounded by its order-one bound. -/
theorem norm_fderiv_smoothCutoff_le (x : EuclideanSpace ℝ (Fin 2)) :
    ‖fderiv ℝ smoothCutoff x‖ ≤ smoothCutoffDerivBound 1 := by
  -- At order one, the iterated derivative norm is the Fréchet derivative norm.
  simpa only [norm_iteratedFDeriv_one] using norm_iteratedFDeriv_smoothCutoff_le 1 x

/-- The second derivative of the planar cutoff is globally bounded by its order-two bound. -/
theorem norm_secondFDeriv_smoothCutoff_le (x : EuclideanSpace ℝ (Fin 2)) :
    ‖fderiv ℝ (fderiv ℝ smoothCutoff) x‖ ≤ smoothCutoffDerivBound 2 := by
  -- Identify the ordinary second derivative with the order-two iterated derivative in norm.
  calc
    ‖fderiv ℝ (fderiv ℝ smoothCutoff) x‖ =
        ‖iteratedFDeriv ℝ 1 (fderiv ℝ smoothCutoff) x‖ :=
      (norm_iteratedFDeriv_one (𝕜 := ℝ) (fderiv ℝ smoothCutoff)).symm
    _ = ‖iteratedFDeriv ℝ 2 smoothCutoff x‖ := by
      rw [norm_iteratedFDeriv_fderiv]
    _ ≤ smoothCutoffDerivBound 2 := norm_iteratedFDeriv_smoothCutoff_le 2 x

end EuclideanPlane

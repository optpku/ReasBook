module

public import ReasLib.Analysis.Calculus.ContDiff.AffineCutoffBump.CenterJet
public import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumObjectiveInterpolation
import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumPointwise

public section

open Filter Set Topology
open scoped ContDiff

universe u

namespace AffineBump

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A smooth cutoff gives an order-two smooth family of scaled linear bumps at arbitrary
centers, scales, and linear coefficients. -/
theorem contDiff_two_scaledLinearBump_family
    (chi : E → ℝ) (hchi : ContDiff ℝ ∞ chi) (x : ℕ → E) (rho : ℕ → ℝ)
    (a : ℕ → E) :
    ∀ k, ContDiff ℝ 2 (scaledLinearBump chi (x k) (rho k) (a k)) := by
  have htwo_le : (2 : WithTop ℕ∞) ≤ ∞ := by
    have htwo_nat : (2 : ℕ∞) ≤ ⊤ := le_top
    exact WithTop.coe_le_coe.mpr htwo_nat
  intro k
  exact (contDiff_scaledLinearBump chi hchi (x k) (rho k) (a k)).of_le htwo_le

/-- Unit-ball support of a cutoff gives the corresponding closed-ball support bound for
every positive-scale member of a scaled linear bump family. -/
theorem tsupport_scaledLinearBump_family_subset_closedBall
    (chi : E → ℝ) (hchiSupport : tsupport chi ⊆ Metric.ball 0 1)
    (x : ℕ → E) (rho : ℕ → ℝ) (a : ℕ → E) (hrho : ∀ k, 0 < rho k) :
    ∀ k, tsupport (scaledLinearBump chi (x k) (rho k) (a k)) ⊆
      Metric.closedBall (x k) (rho k) := by
  intro k
  exact tsupport_scaledLinearBump_subset_closedBall
    chi hchiSupport (x k) (rho k) (a k) (hrho k)

/-- The pointwise finsum of a pairwise-disjoint family of scaled linear bumps
vanishes at each designated center. -/
theorem finsum_scaledLinearBump_apply_center
    (chi : E → ℝ) (hchiSupport : tsupport chi ⊆ Metric.ball 0 1)
    (x : ℕ → E) (rho : ℕ → ℝ) (a : ℕ → E) (hrho : ∀ k, 0 < rho k)
    (hballs : Set.univ.PairwiseDisjoint
      (fun k ↦ Metric.closedBall (x k) (rho k))) (k : ℕ) :
    (∑ᶠ n, scaledLinearBump chi (x n) (rho n) (a n) (x k)) = 0 := by
  have hsupport := tsupport_scaledLinearBump_family_subset_closedBall
    chi hchiSupport x rho a hrho
  have hlocal :=
    DisjointFinsum.finsum_eq_eventuallyEq_at_center_of_pairwiseDisjoint_closedBall
      x rho (fun n ↦ scaledLinearBump chi (x n) (rho n) (a n))
      hrho hballs hsupport k
  calc
    (∑ᶠ n, scaledLinearBump chi (x n) (rho n) (a n) (x k)) =
        scaledLinearBump chi (x k) (rho k) (a k) (x k) :=
      hlocal.eq_of_nhds
    _ = 0 := scaledLinearBump_apply_center chi (x k) (rho k) (a k)

/-- If the cutoff equals one at the origin, the pointwise finsum of a
pairwise-disjoint scaled-linear-bump family has the prescribed coefficient as
its gradient at each center. -/
theorem hasGradientAt_finsum_scaledLinearBump_center
    [CompleteSpace E] (chi : E → ℝ) (hchi : ContDiff ℝ ∞ chi)
    (hchi0 : chi 0 = 1) (hchiSupport : tsupport chi ⊆ Metric.ball 0 1)
    (x : ℕ → E) (rho : ℕ → ℝ) (a : ℕ → E) (hrho : ∀ k, 0 < rho k)
    (hballs : Set.univ.PairwiseDisjoint
      (fun k ↦ Metric.closedBall (x k) (rho k))) (k : ℕ) :
    HasGradientAt
      (fun y ↦ ∑ᶠ n, scaledLinearBump chi (x n) (rho n) (a n) y)
      (a k) (x k) := by
  have hsupport := tsupport_scaledLinearBump_family_subset_closedBall
    chi hchiSupport x rho a hrho
  have hgradient : HasGradientAt
      (scaledLinearBump chi (x k) (rho k) (a k)) (a k) (x k) :=
    hasGradientAt_scaledLinearBump_center_of_eq_one
      chi hchi hchi0 (x k) (rho k) (a k) (hrho k)
  exact DisjointFinsum.hasGradientAt_finsum_of_pairwiseDisjoint_closedBall
    x rho (fun n ↦ scaledLinearBump chi (x n) (rho n) (a n))
    hrho hballs hsupport k hgradient

/-- Under the same hypotheses, the canonical gradient of the pointwise
finsum at a center is the coefficient of the centered bump. -/
theorem gradient_finsum_scaledLinearBump_center
    [CompleteSpace E] (chi : E → ℝ) (hchi : ContDiff ℝ ∞ chi)
    (hchi0 : chi 0 = 1) (hchiSupport : tsupport chi ⊆ Metric.ball 0 1)
    (x : ℕ → E) (rho : ℕ → ℝ) (a : ℕ → E) (hrho : ∀ k, 0 < rho k)
    (hballs : Set.univ.PairwiseDisjoint
      (fun k ↦ Metric.closedBall (x k) (rho k))) (k : ℕ) :
    gradient (fun y ↦ ∑ᶠ n, scaledLinearBump chi (x n) (rho n) (a n) y) (x k) =
      a k := by
  exact (hasGradientAt_finsum_scaledLinearBump_center chi hchi hchi0 hchiSupport
    x rho a hrho hballs k).gradient

/-- A translated quadratic plus a zero-extended disjoint family of scaled linear bumps has
the unperturbed quadratic value at every designated center. -/
theorem halfNormSq_sub_add_disjointScaledLinearBump_apply_center
    (chi : E → ℝ) (hchi : ContDiff ℝ ∞ chi)
    (hchiSupport : tsupport chi ⊆ Metric.ball 0 1) (C : E) (Gamma : Set E)
    (x : ℕ → E) (rho : ℕ → ℝ) (a : ℕ → E) (hGamma : IsClosed Gamma)
    (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Gamma) (hrho : ∀ k, 0 < rho k)
    (hrho0 : Tendsto rho atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (rho k)))
    (k : ℕ) (hxk : x k ∈ Gammaᶜ) :
    (1 / 2 : ℝ) * ‖x k - C‖ ^ 2 +
        (∑ᶠ n, scaledLinearBump chi (x n) (rho n) (a n) (x k)) =
      (1 / 2 : ℝ) * ‖x k - C‖ ^ 2 := by
  have hrhoNonneg : ∀ n, 0 ≤ rho n := fun n ↦ (hrho n).le
  have hsupport := tsupport_scaledLinearBump_family_subset_closedBall
    chi hchiSupport x rho a hrho
  have hsmooth := contDiff_two_scaledLinearBump_family chi hchi x rho a
  exact DisjointFinsum.halfNormSq_sub_add_finsum_apply_center_of_disjoint
    C 2 Gamma x rho (fun n ↦ scaledLinearBump chi (x n) (rho n) (a n)) hGamma
      hcluster hrhoNonneg hrho0 hballs hsupport hsmooth k hxk
        (scaledLinearBump_apply_center chi (x k) (rho k) (a k))

/-- If the cutoff equals one at the origin, the translated quadratic plus a zero-extended
disjoint family of scaled linear bumps has the prescribed corrected gradient at each center. -/
theorem hasGradientAt_halfNormSq_sub_add_disjointScaledLinearBump_center
    [CompleteSpace E] (chi : E → ℝ) (hchi : ContDiff ℝ ∞ chi) (hchi0 : chi 0 = 1)
    (hchiSupport : tsupport chi ⊆ Metric.ball 0 1) (C : E) (Gamma : Set E)
    (x : ℕ → E) (rho : ℕ → ℝ) (a : ℕ → E) (hGamma : IsClosed Gamma)
    (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Gamma) (hrho : ∀ k, 0 < rho k)
    (hrho0 : Tendsto rho atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (rho k)))
    (k : ℕ) (hxk : x k ∈ Gammaᶜ) :
    HasGradientAt
      (fun y ↦ (1 / 2 : ℝ) * ‖y - C‖ ^ 2 +
        ∑ᶠ n, scaledLinearBump chi (x n) (rho n) (a n) y)
      (x k - C + a k) (x k) := by
  have hrhoNonneg : ∀ n, 0 ≤ rho n := fun n ↦ (hrho n).le
  have hsupport := tsupport_scaledLinearBump_family_subset_closedBall
    chi hchiSupport x rho a hrho
  have hsmooth := contDiff_two_scaledLinearBump_family chi hchi x rho a
  have hgradient := hasGradientAt_scaledLinearBump_center_of_eq_one
    chi hchi hchi0 (x k) (rho k) (a k) (hrho k)
  have hone_le_two : 1 ≤ 2 := by
    norm_num
  exact DisjointFinsum.hasGradientAt_halfNormSq_sub_add_finsum_center_of_disjoint
    C 2 Gamma x rho (fun n ↦ scaledLinearBump chi (x n) (rho n) (a n)) hGamma
      hcluster hrhoNonneg hrho0 hballs hsupport hsmooth k hxk hone_le_two hgradient

/-- Under the same cutoff normalization, the gradient at each designated center is the
quadratic displacement plus the scaled linear bump coefficient. -/
theorem gradient_halfNormSq_sub_add_disjointScaledLinearBump_center
    [CompleteSpace E] (chi : E → ℝ) (hchi : ContDiff ℝ ∞ chi) (hchi0 : chi 0 = 1)
    (hchiSupport : tsupport chi ⊆ Metric.ball 0 1) (C : E) (Gamma : Set E)
    (x : ℕ → E) (rho : ℕ → ℝ) (a : ℕ → E) (hGamma : IsClosed Gamma)
    (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Gamma) (hrho : ∀ k, 0 < rho k)
    (hrho0 : Tendsto rho atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (rho k)))
    (k : ℕ) (hxk : x k ∈ Gammaᶜ) :
    gradient
      (fun y ↦ (1 / 2 : ℝ) * ‖y - C‖ ^ 2 +
        ∑ᶠ n, scaledLinearBump chi (x n) (rho n) (a n) y)
      (x k) = x k - C + a k := by
  exact (hasGradientAt_halfNormSq_sub_add_disjointScaledLinearBump_center
    chi hchi hchi0 hchiSupport C Gamma x rho a hGamma hcluster hrho hrho0 hballs k hxk).gradient

end AffineBump

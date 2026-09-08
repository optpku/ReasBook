module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Analysis.Calculus.Gradient.Basic

public section

open Filter Set Topology

universe u v w

namespace DisjointFinsum

variable {E : Type u} {F : Type v} {ι : Type w}
  [NormedAddCommGroup E] [AddCommMonoid F]

/-- A point in one member of a pairwise-disjoint support family sees only that summand in the
pointwise finsum. -/
theorem finsum_eq_single_of_pairwiseDisjoint_tsupport
    (ψ : ι → E → F) (B : ι → Set E)
    (hdisjoint : Set.univ.PairwiseDisjoint B)
    (hsupport : ∀ i, tsupport (ψ i) ⊆ B i) (k : ι) {z : E}
    (hz : z ∈ tsupport (ψ k)) :
    (∑ᶠ i, ψ i z) = ψ k z := by
  apply finsum_eq_single
  intro i hik
  have hnot : z ∉ tsupport (ψ i) := by
    intro hzi
    have hik' := hdisjoint.elim_set (Set.mem_univ i) (Set.mem_univ k) z
      (hsupport i hzi) (hsupport k hz)
    exact hik hik'
  exact image_eq_zero_of_notMem_tsupport (f := ψ i) hnot

/-- Near the center of a positive-radius pairwise-disjoint closed ball, a supported finsum is
eventually equal to its centered summand. -/
theorem finsum_eq_eventuallyEq_at_center_of_pairwiseDisjoint_closedBall
    (x : ι → E) (ρ : ι → ℝ) (ψ : ι → E → F)
    (hρ : ∀ i, 0 < ρ i)
    (hdisjoint : Set.univ.PairwiseDisjoint
      (fun i ↦ Metric.closedBall (x i) (ρ i)))
    (hsupport : ∀ i, tsupport (ψ i) ⊆ Metric.closedBall (x i) (ρ i))
    (k : ι) :
    (fun y ↦ ∑ᶠ i, ψ i y) =ᶠ[𝓝 (x k)] ψ k := by
  filter_upwards [Metric.ball_mem_nhds (x k) (hρ k)] with y hy
  have hyk : y ∈ Metric.closedBall (x k) (ρ k) := by
    rw [Metric.mem_closedBall]
    have hdist : dist y (x k) < ρ k := by
      simpa [Metric.mem_ball, dist_comm] using hy
    exact le_of_lt hdist
  apply finsum_eq_single
  intro i hik
  have hnot : y ∉ tsupport (ψ i) := by
    intro hyi
    have hik' := hdisjoint.elim_set (Set.mem_univ i) (Set.mem_univ k) y
      (hsupport i hyi) hyk
    exact hik hik'
  exact image_eq_zero_of_notMem_tsupport (f := ψ i) hnot

/-- A gradient certificate for a centered summand transfers across a pairwise-disjoint
positive-radius closed-ball finsum. -/
theorem hasGradientAt_finsum_of_pairwiseDisjoint_closedBall
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (x : ι → E) (ρ : ι → ℝ) (ψ : ι → E → ℝ)
    (hρ : ∀ i, 0 < ρ i)
    (hdisjoint : Set.univ.PairwiseDisjoint
      (fun i ↦ Metric.closedBall (x i) (ρ i)))
    (hsupport : ∀ i, tsupport (ψ i) ⊆ Metric.closedBall (x i) (ρ i))
    (k : ι) {g : E} (hgradient : HasGradientAt (ψ k) g (x k)) :
    HasGradientAt (fun y ↦ ∑ᶠ i, ψ i y) g (x k) := by
  exact hgradient.congr_of_eventuallyEq
    (finsum_eq_eventuallyEq_at_center_of_pairwiseDisjoint_closedBall x ρ ψ hρ
      hdisjoint hsupport k)

/-- The gradient of a pairwise-disjoint positive-radius closed-ball finsum at a center is the
gradient of its centered summand. -/
theorem gradient_finsum_of_pairwiseDisjoint_closedBall
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (x : ι → E) (ρ : ι → ℝ) (ψ : ι → E → ℝ)
    (hρ : ∀ i, 0 < ρ i)
    (hdisjoint : Set.univ.PairwiseDisjoint
      (fun i ↦ Metric.closedBall (x i) (ρ i)))
    (hsupport : ∀ i, tsupport (ψ i) ⊆ Metric.closedBall (x i) (ρ i))
    (k : ι) {g : E} (hgradient : HasGradientAt (ψ k) g (x k)) :
    gradient (fun y ↦ ∑ᶠ i, ψ i y) (x k) = g := by
  exact (hasGradientAt_finsum_of_pairwiseDisjoint_closedBall x ρ ψ hρ hdisjoint
    hsupport k hgradient).gradient

end DisjointFinsum

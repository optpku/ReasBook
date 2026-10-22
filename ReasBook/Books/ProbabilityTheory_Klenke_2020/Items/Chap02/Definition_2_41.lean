/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Lemma_2_40

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open MeasureTheory

variable {Ω : Type u} [MeasurableSpace Ω] {d : ℕ}

/-- Definition 2.41: percolation occurs for a configuration when some open cluster in `ℤ^d`
is infinite. This is the event whose probability is denoted by `ψ(p)` in the text. -/
def percolationOccurs (cluster : LatticePoint d → Ω → Set (LatticePoint d)) : Set Ω :=
  {ω | ∃ x : LatticePoint d, Set.Infinite (cluster x ω)}

/-- The probability `ψ(p)` that percolation occurs, defined as the probability of the event that
there exists an infinite open cluster. -/
def percolationProbability (μ : ProbabilityMeasure Ω)
    (cluster : LatticePoint d → Ω → Set (LatticePoint d)) : NNReal :=
  μ (percolationOccurs cluster)

/-- The event that the open cluster containing the origin in `ℤ^d` is infinite. -/
def originInInfiniteClusterEvent (cluster : LatticePoint d → Ω → Set (LatticePoint d)) : Set Ω :=
  {ω | Set.Infinite (cluster 0 ω)}

/-- The probability `θ(p)` that the origin belongs to an infinite open cluster. -/
def originPercolationProbability (μ : ProbabilityMeasure Ω)
    (cluster : LatticePoint d → Ω → Set (LatticePoint d)) : NNReal :=
  μ (originInInfiniteClusterEvent cluster)

/-- Translation invariance of the infinite-cluster marginals: the probability that a given site
belongs to an infinite open cluster does not depend on the site. -/
class HasTranslationInvariantInfiniteClusterMarginals
    (μ : ProbabilityMeasure Ω) (cluster : LatticePoint d → Ω → Set (LatticePoint d)) : Prop where
  /-- Every site has the same infinite-cluster marginal as the origin. -/
  site_eq_origin :
    ∀ y : LatticePoint d,
      μ {ω | Set.Infinite (cluster y ω)} = originPercolationProbability μ cluster

/-- Translation invariance of the infinite-cluster marginals means exactly that each site has the
same infinite-cluster marginal as the origin. -/
theorem hasTranslationInvariantInfiniteClusterMarginals_iff
    (μ : ProbabilityMeasure Ω) (cluster : LatticePoint d → Ω → Set (LatticePoint d)) :
    HasTranslationInvariantInfiniteClusterMarginals μ cluster ↔
      ∀ y : LatticePoint d,
        μ {ω | Set.Infinite (cluster y ω)} = originPercolationProbability μ cluster := by
  constructor
  · intro h_translation
    exact h_translation.site_eq_origin
  · intro h_translation
    exact ⟨h_translation⟩

-- Proof sketch: unfold `percolationProbability` and `percolationOccurs`; the statement is the
-- defining equation for `ψ(p)`.
/-- The percolation probability is the probability of the event that some open cluster is
infinite. -/
theorem percolationProbability_eq_probability_of_percolationOccurs
    (μ : ProbabilityMeasure Ω) (cluster : LatticePoint d → Ω → Set (LatticePoint d)) :
    percolationProbability μ cluster =
      μ {ω | ∃ x : LatticePoint d, Set.Infinite (cluster x ω)} := rfl

-- Proof sketch: apply the translation-invariance hypothesis at the site `y`; the right-hand side
-- is exactly the probability appearing in equation (2.13).
/-- Under translation invariance, the probability that the origin lies in an infinite open cluster
agrees with the corresponding probability at any lattice site. -/
theorem originPercolationProbability_eq_site
    (μ : ProbabilityMeasure Ω) (cluster : LatticePoint d → Ω → Set (LatticePoint d))
    [HasTranslationInvariantInfiniteClusterMarginals μ cluster]
    (y : LatticePoint d) :
    originPercolationProbability μ cluster = μ {ω | Set.Infinite (cluster y ω)} := by
  exact (HasTranslationInvariantInfiniteClusterMarginals.site_eq_origin y).symm

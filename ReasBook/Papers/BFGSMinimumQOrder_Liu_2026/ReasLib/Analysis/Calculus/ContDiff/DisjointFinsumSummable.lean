module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumPointwise

/-!
# Summability of pointwise-disjoint families

At a fixed point, pairwise-disjoint topological supports leave at most one
nonzero summand. This file connects that pointwise fact to Mathlib's infinite
sum API. For a general finite function support, the canonical theorem is
`summable_of_hasFiniteSupport`.
-/

public section
noncomputable section
open Set Topology
universe u v w
namespace DisjointFinsum

variable {E : Type u} {F : Type v} {ι : Type w}
  [TopologicalSpace E] [AddCommMonoid F] [TopologicalSpace F]

/-- A family with at most one nonzero term is summable. -/
theorem summable_of_support_subsingleton (f : ι → F)
    (hf : (Function.support f).Subsingleton) : Summable f :=
  summable_of_hasFiniteSupport hf.finite

/-- If a family has at most one nonzero term and its value at `k` is nonzero,
then its infinite sum is that value. -/
theorem tsum_eq_single_of_support_subsingleton (f : ι → F) (k : ι)
    (hk : f k ≠ 0) (hf : (Function.support f).Subsingleton) :
    (∑' i, f i) = f k := by
  apply tsum_eq_single k
  intro i hik
  by_contra hi
  exact hik (hf hi hk)

/-- If every term of a family is zero, then its infinite sum is zero. -/
theorem tsum_eq_zero_of_forall_eq_zero (f : ι → F) (hf : ∀ i, f i = 0) :
    (∑' i, f i) = 0 := by
  simp only [hf, tsum_zero]

/-- A point belongs to the topological support of at most one member of a
pairwise-disjoint family of topological supports. -/
theorem activeIndices_subsingleton_of_pairwiseDisjoint_tsupport
    (ψ : ι → E → F)
    (hdisjoint : Set.univ.PairwiseDisjoint (fun i ↦ tsupport (ψ i))) (z : E) :
    ({i : ι | z ∈ tsupport (ψ i)} : Set ι).Subsingleton := by
  intro i hi j hj
  exact hdisjoint.elim_set (Set.mem_univ i) (Set.mem_univ j) z hi hj

/-- At each point, the values of a family with pairwise-disjoint topological
supports have subsingleton function support. -/
theorem support_apply_subsingleton_of_pairwiseDisjoint_tsupport
    (ψ : ι → E → F)
    (hdisjoint : Set.univ.PairwiseDisjoint (fun i ↦ tsupport (ψ i))) (z : E) :
    (Function.support fun i ↦ ψ i z).Subsingleton := by
  intro i hi j hj
  exact activeIndices_subsingleton_of_pairwiseDisjoint_tsupport ψ hdisjoint z
    (subset_tsupport (ψ i) hi) (subset_tsupport (ψ j) hj)

/-- Pointwise evaluation of a family with pairwise-disjoint topological
supports is summable. -/
theorem summable_apply_of_pairwiseDisjoint_tsupport
    (ψ : ι → E → F)
    (hdisjoint : Set.univ.PairwiseDisjoint (fun i ↦ tsupport (ψ i))) (z : E) :
    Summable (fun i ↦ ψ i z) :=
  summable_of_support_subsingleton _
    (support_apply_subsingleton_of_pairwiseDisjoint_tsupport ψ hdisjoint z)

/-- At a point in one topological support, the pointwise infinite sum of a
pairwise-disjoint support family is the corresponding summand. -/
theorem tsum_apply_eq_single_of_pairwiseDisjoint_tsupport
    (ψ : ι → E → F)
    (hdisjoint : Set.univ.PairwiseDisjoint (fun i ↦ tsupport (ψ i)))
    (k : ι) {z : E} (hz : z ∈ tsupport (ψ k)) :
    (∑' i, ψ i z) = ψ k z := by
  apply tsum_eq_single k
  intro i hik
  have hnot : z ∉ tsupport (ψ i) := by
    intro hzi
    exact hik (hdisjoint.elim_set (Set.mem_univ i) (Set.mem_univ k) z hzi hz)
  exact image_eq_zero_of_notMem_tsupport (f := ψ i) hnot

/-- If a point lies in none of the topological supports, the corresponding
pointwise infinite sum is zero. -/
theorem tsum_apply_eq_zero_of_forall_not_mem_tsupport
    (ψ : ι → E → F) {z : E} (hz : ∀ i, z ∉ tsupport (ψ i)) :
    (∑' i, ψ i z) = 0 := by
  apply tsum_eq_zero_of_forall_eq_zero
  intro i
  exact image_eq_zero_of_notMem_tsupport (f := ψ i) (hz i)

end DisjointFinsum

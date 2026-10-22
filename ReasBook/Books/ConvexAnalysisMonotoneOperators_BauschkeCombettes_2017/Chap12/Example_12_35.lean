/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_34

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

namespace ERealFunction

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {E : Type*} [NormedAddCommGroup E]
variable {p : ENNReal}

/-- The latent group lasso decomposition space consists of families whose `k`-th component is
supported in the coordinate group `groups k`. -/
def latentGroupLassoDecompositionSpace (E : Type*) [NormedAddCommGroup E] (p : ENNReal)
    (groups : κ → Set ι) :=
  {x : κ → PiLp p (fun _ : ι ↦ E) // ∀ k, Function.support (x k) ⊆ groups k}

namespace latentGroupLassoDecompositionSpace

/-- The latent group lasso synthesis map sends an admissible family `(x_k)` to the sum
`∑ k, x_k`. -/
noncomputable def synthesis (E : Type*) [NormedAddCommGroup E] (p : ENNReal)
    (groups : κ → Set ι) : latentGroupLassoDecompositionSpace E p groups → PiLp p (fun _ : ι ↦ E) :=
  fun x ↦ ∑ k, x.1 k

end latentGroupLassoDecompositionSpace

open latentGroupLassoDecompositionSpace

/- The primitive decomposition space and synthesis map make sense for every `p : ENNReal`. The
source-facing penalties of Example 12.35 use the textbook `ℓ^p` regime `1 ≤ p < ∞`. -/

/-- The textbook exponent range for Example 12.35: `1 ≤ p < ∞`. -/
abbrev TextbookExponent := Subtype fun p : ENNReal ↦ 1 ≤ p ∧ p ≠ ⊤

namespace latentGroupLassoDecompositionSpace

/-- The latent group lasso decomposition cost is the sum of the `p`-norms of the components of an
admissible decomposition, in the textbook exponent range `1 ≤ p < ∞`. -/
noncomputable def cost (E : Type*) [NormedAddCommGroup E]
    (p : TextbookExponent) (groups : κ → Set ι) :
    latentGroupLassoDecompositionSpace E p.1 groups → ℝ :=
  fun x ↦ ∑ k, ‖x.1 k‖

end latentGroupLassoDecompositionSpace

/-- Example 12.35: on a finite coordinate `ℓ^p` space with `1 ≤ p < ∞`, the latent group lasso
penalty is the infimal postcomposition of the source-facing real-valued cost
`x ↦ ∑ k, ‖x_k‖_p` by the synthesis map `(x_k) ↦ ∑ k, x_k`. The textbook `ℝ^N` case is
recovered by taking `ι = Fin N` and `E = ℝ`. The nonemptiness and covering hypotheses on the
groups enter later analytic properties, not this defining infimal-postcomposition construction. -/
noncomputable def latentGroupLassoPenalty
    (p : TextbookExponent)
    (groups : κ → Set ι) : PiLp p.1 (fun _ : ι ↦ E) → EReal :=
  synthesis E p.1 groups ▷ (cost E p groups).toEReal

/- Example 12.35: the textbook latent group lasso penalty `‖·‖_{gl}` with parameters `p` and
`groups` is written `‖y‖_gl[p,groups]`. -/
notation "‖" y "‖_gl[" p "," groups "]" => latentGroupLassoPenalty p groups y

/-- Evaluating the latent group lasso penalty at `y` gives the infimum of the sums of the
component norms over all admissible decompositions whose synthesis is `y`. -/
theorem latentGroupLassoPenalty_apply
    (p : TextbookExponent)
    (groups : κ → Set ι) (y : PiLp p.1 (fun _ : ι ↦ E)) :
    ‖y‖_gl[p,groups] =
      sInf ((cost E p groups).toEReal.asEReal '' (synthesis E p.1 groups ⁻¹' {y})) := by
  simpa [latentGroupLassoPenalty] using
    infimalPostcomposition_apply (synthesis E p.1 groups) (cost E p groups).toEReal y

/-- The `k`-th block of `y` supported on `groups k`, obtained by zeroing out the other
coordinates. -/
noncomputable def groupLassoBlock
    (p : TextbookExponent) (groups : κ → Set ι)
    (k : κ) : PiLp p.1 (fun _ : ι ↦ E) → PiLp p.1 (fun _ : ι ↦ E) :=
  fun y ↦
    let _ : DecidablePred fun i : ι ↦ i ∈ groups k := Classical.decPred _
    WithLp.toLp p.1 ((groups k).indicator y)

/-- The blockwise sum of `p`-norms associated with the family `groups`; when the groups are
pairwise disjoint, this is the ordinary group lasso penalty. -/
noncomputable def groupLassoPenalty
    (p : TextbookExponent) (groups : κ → Set ι) :
    PiLp p.1 (fun _ : ι ↦ E) → ℝ :=
  fun y ↦ ∑ k, ‖groupLassoBlock p groups k y‖

/-- If the coordinate groups are pairwise disjoint and cover all coordinates, then the latent group
lasso penalty reduces to the ordinary group lasso penalty. -/
theorem latentGroupLassoPenalty_eq_groupLassoPenalty_of_pairwiseDisjoint
    (p : TextbookExponent) (groups : κ → Set ι)
    (hdisjoint : Pairwise fun i j ↦ Disjoint (groups i) (groups j))
    (hcover : (⋃ k, groups k) = Set.univ) (y : PiLp p.1 (fun _ : ι ↦ E)) :
    ‖y‖_gl[p,groups] = (groupLassoPenalty p groups y : ℝ) :=
  sorry

end ERealFunction

/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {E : Type u} {ι : Type v}
variable [AddCommGroup E] [Module ℝ E]

/-
This item is `source-facing` at the Chapter 3 owner `subdifferential`. Domain sampling for the
weak max-rule API points to the following declarations:

* `is_subgradient_at` in `Definition_3_1` as the primitive predicate.
* `subdifferential` in `Definition_3_2` as the owner set-valued map.
* `convex_subdifferential` in `Definition_3_2` as the owner-level derived convexity needed to pass
  from the active union to its convex hull.
* `directional_derivative_iSup_eq_iSup_active_indices` in `Theorem_3_9` as the matching canonical
  active-index subtype for pointwise suprema.

The primitive data here is only the ambient subdifferential of the pointwise maximum; the active
index collection at `x` is derived data, so the public statement uses the canonical active-index
subtype directly rather than a separate wrapper owner. The theorem stays directly on the owner
declaration from `Definition_3_2` rather than depending on the later strong-dual bridge/view
files. Semantic recall via `lean_leansearch` did not expose a direct mathlib weak-max
subdifferential theorem, so the source-facing owner statement stays chapter-local; the canonical
Lean surface keeps only the genuinely used pointwise upper-bound hypothesis, because the active
index equality already identifies the branch value at `x` and `convex_subdifferential` already
provides the convex target needed for the convex-hull conclusion.
-/
recall subdifferential
recall convex_subdifferential

/-- Helper for Theorem 3.23: a subgradient on an active branch shows that `x` lies in the
effective domain of the ambient upper envelope `F`. -/
lemma activeIndex_memEffectiveDomain_of_subgradient
    (F : E → EReal) (f : ι → E → EReal) (x : E)
    (i : {i : ι // F x = f i x}) (g : Module.Dual ℝ E)
    (hg : g ∈ ∂(f i)(x)) :
    x ∈ effective_domain F := by
  -- Rewrite branch membership to the primitive predicate so the domain witness is explicit.
  rw [mem_subdifferential] at hg
  -- Transport finiteness at `x` from the active branch value to the ambient function value.
  simpa [mem_effective_domain, i.2] using hg.1

/-- Helper for Theorem 3.23: every subgradient of an active branch is a subgradient of the ambient
pointwise upper envelope `F`. -/
lemma activeBranchSubgradient_mem_subdifferential
    (F : E → EReal) (f : ι → E → EReal) (x : E)
    (hupper : ∀ y : E, ∀ i : ι, f i y ≤ F y)
    (i : {i : ι // F x = f i x}) (g : Module.Dual ℝ E)
    (hg : g ∈ ∂(f i)(x)) :
    g ∈ ∂ F(x) := by
  -- Route correction: prove ambient membership directly in the owner API by transporting the
  -- active equality at `x` and composing the branch subgradient inequality with `hupper`.
  rw [mem_subdifferential] at hg ⊢
  refine ⟨activeIndex_memEffectiveDomain_of_subgradient F f x i g hg, ?_⟩
  intro y
  -- First normalize the branch subgradient inequality into `≤` form.
  have hbranch : f i x + (g (y - x) : EReal) ≤ f i y := by
    simpa [ge_iff_le] using hg.2 y
  -- Then rewrite the active value at `x` and compare the branch value against the ambient bound.
  have hambient : F x + (g (y - x) : EReal) ≤ F y := by
    have hbranchToAmbient : f i x + (g (y - x) : EReal) ≤ F y :=
      hbranch.trans (hupper y i)
    simpa [i.2] using hbranchToAmbient
  simpa [ge_iff_le] using hambient

/-- Helper for Theorem 3.23: the union of the active branch subdifferentials is contained in the
ambient subdifferential. -/
lemma iUnion_activeBranchSubdifferential_subset_subdifferential
    (F : E → EReal) (f : ι → E → EReal) (x : E)
    (hupper : ∀ y : E, ∀ i : ι, f i y ≤ F y) :
    (⋃ i : {i : ι // F x = f i x}, ∂(f i)(x)) ⊆ ∂ F(x) := by
  -- Upgrade the pointwise active-branch inclusion to the indexed union with `Set.iUnion_subset`.
  refine Set.iUnion_subset fun i ↦ ?_
  intro g hg
  exact activeBranchSubgradient_mem_subdifferential F f x hupper i g hg

-- Proof sketch: if `g ∈ ∂ fᵢ(x)` and `i` is active at `x`, then for every `y` we have
-- `F y ≥ f i y ≥ f i x + g (y - x) = F x + g (y - x)`, so `g ∈ ∂ F(x)`. Hence the union of the
-- active subdifferentials is contained in the ambient subdifferential. Since `∂ F(x)` is convex
-- by `convex_subdifferential`, the convex hull of that union is contained there as well.
/-- Theorem 3.23: weak maximum rule of subdifferential calculus. If every branch `fᵢ` lies below
`F`, then the convex hull of the subdifferentials of the branches active at `x` is contained in
the subdifferential of `F` at `x`. -/
theorem convexHull_iUnion_active_subdifferential_subset_subdifferential_iSup
    (F : E → EReal) (f : ι → E → EReal) (x : E)
    (hupper : ∀ y : E, ∀ i : ι, f i y ≤ F y) :
    convexHull ℝ (⋃ i : {i : ι // F x = f i x}, ∂(f i)(x)) ⊆ ∂ F(x) := by
  -- First show that every active-branch subgradient already lies in the ambient subdifferential.
  have hsubset :
      (⋃ i : {i : ι // F x = f i x}, ∂(f i)(x)) ⊆ ∂ F(x) :=
    iUnion_activeBranchSubdifferential_subset_subdifferential F f x hupper
  -- Then use convexity of `∂ F(x)` to absorb the convex hull of that active union.
  exact convexHull_min hsubset (convex_subdifferential F x)

end

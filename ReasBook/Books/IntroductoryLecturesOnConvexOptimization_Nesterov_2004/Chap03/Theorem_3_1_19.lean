/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5_4

noncomputable section

open scoped WithTopConvexAnalysis

universe u

variable {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/- Theorem 3.1.19 lies in the same common-subdifferential owner domain as
`Definition_3_1_5` and `Definition_3_1_5_4`.

Relevant owner-style declarations sampled before refinement:
- `IsSubgradientAt` in `Definition_3_1_5`
- `commonRegularSubdifferential` in `Definition_3_1_5_4`
- `mem_commonRegularSubdifferential_iff` in `Definition_3_1_5_4`
- `commonRegularSubdifferentialOn` in `Definition_3_1_5_4`
- `mem_commonRegularSubdifferentialOn_iff` in `Definition_3_1_5_4`
- `mem_subdifferential_coe_real_iff` in `Definition_3_1_5`

Best owner abstraction:
- `commonRegularSubdifferential` on an arbitrary real inner-product space

Primitive data:
- a set `X : Set V`
- a real-valued convex function `f : V → ℝ`
- either a common regular subgradient `g ∈ ∂̂ f(X)` or the nonemptiness of that set

Derived API:
- the affine increment identity induced by a common regular subgradient
- the affine-on-segments consequence when the common regular subdifferential is nonempty

Source/core/bridge triage:
- source-facing: the two textbook consequences of a common regular subgradient
- core/canonical: `commonRegularSubdifferential`
- bridge/view: `commonRegularSubdifferentialOn`

The earlier version fixed the ambient space to `EuclideanSpace ℝ (Fin n)`, but neither statement
uses coordinates, finite indexing, or finite-dimensional structure. Since the owner notion
`commonRegularSubdifferential` already lives on arbitrary real inner-product spaces, the canonical
owner theorems should live there as well, with the textbook Euclidean statement recovered by
specialization. -/

/-- Theorem 3.1.19 (2): every common subgradient `g ∈ ∂̂f(X)` gives the affine increment formula
`f x₁ = f x₀ + ⟪g, x₁ - x₀⟫` for all `x₀, x₁ ∈ X`. -/
-- Proof sketch: apply the subgradient inequality furnished by `hg` at the base point `x₀` and
-- evaluation point `x₁`, then again at the base point `x₁` and evaluation point `x₀`. The two
-- resulting inequalities are reverse bounds on the same quantity, so they collapse to equality.
theorem eq_add_inner_of_mem_commonRegularSubdifferential
    {X : Set V} {f : V → ℝ}
    {g x0 x1 : V} (hg : g ∈ ∂̂ f(X))
    (hx0 : x0 ∈ X) (hx1 : x1 ∈ X) :
    f x1 = f x0 + inner ℝ g (x1 - x0) := by
  have hgX := mem_commonRegularSubdifferentialOn_iff.mp hg
  have hg0 : ∀ y : V, f y ≥ f x0 + inner ℝ g (y - x0) := hgX x0 hx0
  have hg1 : ∀ y : V, f y ≥ f x1 + inner ℝ g (y - x1) := hgX x1 hx1
  have h01 : f x0 + inner ℝ g (x1 - x0) ≤ f x1 := by
    simpa [ge_iff_le] using hg0 x1
  have hinv : inner ℝ g (x0 - x1) = -inner ℝ g (x1 - x0) := by
    rw [show x0 - x1 = -(x1 - x0) by abel, inner_neg_right]
  have h10 : f x1 ≤ f x0 + inner ℝ g (x1 - x0) := by
    have h : f x1 + inner ℝ g (x0 - x1) ≤ f x0 := by
      simpa [ge_iff_le] using hg1 x0
    have h' : f x1 + (-inner ℝ g (x1 - x0)) ≤ f x0 := by
      simpa [hinv] using h
    linarith
  linarith

/-- Theorem 3.1.19 (1): if a convex set `X` admits a common subgradient of a real-valued function
`f`, then `f` is affine on every segment contained in `X`. -/
-- Proof sketch: choose a common subgradient `g` from `hfacet_nonempty`. Convexity of `X` places
-- `(1 - α) • x₀ + α • x₁` back in `X`, so the affine increment identity from part `(2)` applies
-- both to `(x₀, (1 - α) • x₀ + α • x₁)` and to `(x₀, x₁)`, and the two identities combine into
-- the segment formula.
theorem map_segment_eq_of_commonRegularSubdifferential_nonempty
    {X : Set V} {f : V → ℝ}
    (hX_convex : Convex ℝ X)
    (hfacet_nonempty : (∂̂ f(X)).Nonempty)
    {x0 x1 : V} (hx0 : x0 ∈ X) (hx1 : x1 ∈ X) {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    f ((1 - α) • x0 + α • x1) = (1 - α) * f x0 + α * f x1 := by
  rcases hfacet_nonempty with ⟨g, hg⟩
  let z : V := (1 - α) • x0 + α • x1
  have hα0 : 0 ≤ 1 - α := by
    linarith [hα.2]
  have hsum : (1 - α) + α = 1 := by
    ring
  have hz : z ∈ X := by
    dsimp [z]
    exact hX_convex hx0 hx1 hα0 hα.1 hsum
  have hz0 : f z = f x0 + inner ℝ g (z - x0) :=
    eq_add_inner_of_mem_commonRegularSubdifferential hg hx0 hz
  have h10 : f x1 = f x0 + inner ℝ g (x1 - x0) :=
    eq_add_inner_of_mem_commonRegularSubdifferential hg hx0 hx1
  have hzsub : z - x0 = α • (x1 - x0) := by
    dsimp [z]
    calc
      ((1 - α) • x0 + α • x1) - x0 = α • x1 + (-x0 + (1 - α) • x0) := by
        abel
      _ = α • x1 + (((-1 : ℝ) + (1 - α)) • x0) := by
        congr 1
        rw [show -x0 = (-1 : ℝ) • x0 by simp, ← add_smul]
      _ = α • x1 + (-(α • x0)) := by
        congr 1
        ring_nf
        simp
      _ = α • (x1 - x0) := by
        rw [sub_eq_add_neg, smul_add, smul_neg]
  rw [hz0, h10, hzsub, inner_smul_right]
  ring

end

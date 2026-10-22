/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_4
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_13

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace (toDual toDualMap)
open scoped Gradient

universe u

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 3.14 is `source-facing` on the Euclidean/vector side of the chapter API. The owner
subdifferential remains `subdifferentialAt`, but the textbook statement is formulated through the
canonical bridge `euclideanSubdifferentialAt` and the gradient `∇ f x`, not through a strong-dual
`fderiv` surface. -/

-- Proof sketch: Theorem 3.13 already supplies the owner-level pattern for this chapter: the
-- forward direction identifies the unique subgradient with the gradient, while the converse starts
-- from uniqueness of an a priori subgradient and concludes differentiability together with
-- identification of that subgradient. This file states the corresponding Euclidean/vector-side
-- bridge specialized to everywhere-finite convex functions.
/-- Proposition 3.14 (1): if a convex real-valued function on a finite-dimensional inner-product
space is differentiable at `x`, then its Euclidean/vector-side subdifferential at `x` is the
singleton containing the gradient `∇ f x`. -/
theorem euclideanSubdifferentialAt_eq_singleton_gradient_of_differentiableAt
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) {x : E}
    (hdiff : DifferentiableAt ℝ f x) :
    euclideanSubdifferentialAt f x = {∇ f x} := by
  have hconvex : is_convex_function (fun y ↦ (f y : EReal)) := by
    refine (is_convex_function_iff_convexOn_toReal ?_).2 ?_
    · intro y hy
      simp
    · simpa [effective_domain] using hf
  have hdiff' : is_differentiable_at (fun y ↦ (f y : EReal)) x := by
    simpa [is_differentiable_at, finite_domain, effective_domain] using hdiff
  have hstrong :
      subdifferentialAt f x = {toDual ℝ E (∇ f x)} := by
    simpa [subdifferentialAt] using
      subdifferential_eq_singleton_gradient_of_differentiableAt
        (fun y ↦ (f y : EReal)) x hconvex hdiff'
  ext z
  rw [Set.mem_singleton_iff, mem_euclideanSubdifferentialAt_iff, hstrong, Set.mem_singleton_iff]
  constructor
  · intro hz
    apply (toDualMap ℝ E).injective
    simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hz
  · intro hz
    simp [hz, InnerProductSpace.toDual_apply_eq_toDualMap_apply]

/-- Proposition 3.14 (2): if a convex real-valued function on a finite-dimensional inner-product
space has Euclidean/vector-side subdifferential `{g}` at `x`, then the function is differentiable
at `x` and `g` is the gradient `∇ f x`. -/
theorem differentiableAt_and_eq_gradient_of_euclideanSubdifferentialAt_eq_singleton
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) {x g : E}
    (hsub : euclideanSubdifferentialAt f x = {g}) :
    DifferentiableAt ℝ f x ∧ g = ∇ f x := by
  have hconvex : is_convex_function (fun y ↦ (f y : EReal)) := by
    refine (is_convex_function_iff_convexOn_toReal ?_).2 ?_
    · intro y hy
      simp
    · simpa [effective_domain] using hf
  have hsubsingleton : (subdifferentialAt f x).Subsingleton := by
    intro φ hφ ψ hψ
    rcases (toDual ℝ E).surjective φ with ⟨u, rfl⟩
    rcases (toDual ℝ E).surjective ψ with ⟨v, rfl⟩
    have hu : u ∈ euclideanSubdifferentialAt f x := by
      simpa [mem_euclideanSubdifferentialAt_iff, InnerProductSpace.toDual_apply_eq_toDualMap_apply]
        using hφ
    have hv : v ∈ euclideanSubdifferentialAt f x := by
      simpa [mem_euclideanSubdifferentialAt_iff, InnerProductSpace.toDual_apply_eq_toDualMap_apply]
        using hψ
    have hu_eq : u = g := by
      simpa [hsub] using hu
    have hv_eq : v = g := by
      simpa [hsub] using hv
    simp [hu_eq, hv_eq]
  have hx : x ∈ interior (finite_domain (fun y ↦ (f y : EReal))) := by
    simp [finite_domain, effective_domain]
  obtain ⟨hdiff', _⟩ :=
    differentiableAt_and_subdifferential_eq_singleton_gradient_of_unique_subgradient
      (fun y ↦ (f y : EReal)) x hconvex hx (by simpa [subdifferentialAt] using hsubsingleton)
  have hdiff : DifferentiableAt ℝ f x := by
    simpa [is_differentiable_at, finite_domain, effective_domain] using hdiff'
  have hgrad : euclideanSubdifferentialAt f x = {∇ f x} :=
    euclideanSubdifferentialAt_eq_singleton_gradient_of_differentiableAt hf hdiff
  have hg : g ∈ euclideanSubdifferentialAt f x := by
    simp [hsub]
  have hg_eq : g = ∇ f x := by
    simpa [hgrad] using hg
  exact ⟨hdiff, hg_eq⟩

/-- Proposition 3.14 packaged as the Euclidean singleton criterion: for a convex real-valued
function, differentiability at `x` is equivalent to the Euclidean/vector-side subdifferential
being the singleton containing `∇ f x`. -/
theorem euclideanSubdifferentialAt_eq_singleton_gradient_iff_differentiableAt
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) {x : E} :
    euclideanSubdifferentialAt f x = {∇ f x} ↔ DifferentiableAt ℝ f x := by
  constructor
  · intro hsub
    exact
      (differentiableAt_and_eq_gradient_of_euclideanSubdifferentialAt_eq_singleton hf hsub).1
  · intro hdiff
    exact euclideanSubdifferentialAt_eq_singleton_gradient_of_differentiableAt hf hdiff

end

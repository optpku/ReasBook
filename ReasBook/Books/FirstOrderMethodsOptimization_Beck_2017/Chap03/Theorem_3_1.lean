/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Bornology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Theorem 3.1 is a `bridge/view` item in the chapter subdifferential API. The owner declaration
is `subdifferential : Set (Module.Dual ℝ E)` from Definition 3.2, while the closedness statement
in this theorem lives on the topologized continuous-dual view. Owner-level convexity already lives
in `convex_subdifferential`, so the only primitive
data here is the canonical preimage of `subdifferential` along
`StrongDual ℝ E → Module.Dual ℝ E`; membership lemmas are derived API. -/
recall subdifferential
recall convex_subdifferential

/-- The continuous-dual view of `subdifferential f x`, obtained by restricting the chapter's
source-facing subdifferential along the canonical coercion `StrongDual ℝ E → Module.Dual ℝ E`. -/
abbrev strongDualSubdifferential (f : E → EReal) (x : E) : Set (StrongDual ℝ E) :=
  ((↑) : StrongDual ℝ E → Module.Dual ℝ E) ⁻¹' ∂ f(x)

notation "∂ₛ" f "(" x ")" => strongDualSubdifferential f x

/-- Membership in `strongDualSubdifferential f x` means that the underlying algebraic-dual
functional belongs to the owner subdifferential `subdifferential f x`. -/
@[simp] theorem mem_strongDualSubdifferential
    {f : E → EReal} {x : E} {g : StrongDual ℝ E} :
    g ∈ ∂ₛ f(x) ↔ (g : Module.Dual ℝ E) ∈ ∂ f(x) :=
  Iff.rfl

/-- Helper for Theorem 3.1: each pointwise support inequality defines a closed half-space in the
strong dual. -/
private lemma isClosed_subgradientSupportHalfspace
    (f : E → EReal) (x y : E) :
    IsClosed {g : StrongDual ℝ E | f x + (((g (y - x) : ℝ) : EReal)) ≤ f y} := by
  let φ : StrongDual ℝ E → EReal := fun g ↦ f x + (((g (y - x) : ℝ) : EReal))
  have hconst : LowerSemicontinuous (fun _ : StrongDual ℝ E ↦ f x) :=
    continuous_const.lowerSemicontinuous
  have heval : Continuous fun g : StrongDual ℝ E ↦ (((g (y - x) : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp (continuous_eval_const (y - x))
  have hφ : LowerSemicontinuous φ := by
    -- Addition by the constant `f x` is lower semicontinuous because the second term is always a
    -- finite real value, so `EReal` addition is continuous at every evaluation point.
    refine hconst.add' heval.lowerSemicontinuous ?_
    intro g
    simpa [φ] using
      (EReal.continuousAt_add (p := (f x, (((g (y - x) : ℝ) : EReal))))
        (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _)))
  -- Closedness is the standard `Iic` preimage criterion for lower semicontinuous functions.
  simpa [φ] using hφ.isClosed_preimage (f y)

/-- Helper for Theorem 3.1: once `x ∈ effective_domain f`, the strong-dual subdifferential is the
intersection of its pointwise support half-spaces. -/
private lemma strongDualSubdifferential_eq_iInter_supportHalfspaces
    (f : E → EReal) (x : E) (hx : x ∈ effective_domain f) :
    ∂ₛ f(x) = ⋂ y : E, {g : StrongDual ℝ E | f x + (((g (y - x) : ℝ) : EReal)) ≤ f y} := by
  ext g
  -- Rewrite bridge membership back to the owner predicate, then drop the fixed domain conjunct.
  rw [Set.mem_iInter, mem_strongDualSubdifferential, mem_subdifferential]
  simp [is_subgradient_at, hx, ge_iff_le]

/-- Helper for Theorem 3.1: `∂ₛ f(x)` is the linear preimage of the owner subdifferential along
the canonical coercion `StrongDual ℝ E →ₗ[ℝ] Module.Dual ℝ E`. -/
private lemma strongDualSubdifferential_linearPreimage
    (f : E → EReal) (x : E) :
    ∂ₛ f(x) =
      (ContinuousLinearMap.coeLM ℝ : StrongDual ℝ E →ₗ[ℝ] Module.Dual ℝ E) ⁻¹' ∂ f(x) := by
  -- This is only a repackaging of the defining preimage through the coercion linear map.
  rfl

-- Proof sketch: write `∂ₛ f(x)` as the intersection, over `y : E`, of the closed
-- half-spaces cut out by the affine functionals `g ↦ (g (y - x) : EReal)`, together
-- with the constant condition `x ∈ effective_domain f`; arbitrary intersections of closed sets are
-- closed.
/-- Theorem 3.1 (1): for an extended-real-valued function, the continuous-dual subdifferential
`∂ₛ f(x)` is a closed subset of the dual space. -/
theorem isClosed_subdifferential (f : E → EReal) (x : E) :
    IsClosed (∂ₛ f(x)) := by
  by_cases hx : x ∈ effective_domain f
  · -- On the effective domain, the bridge set is an intersection of closed support half-spaces.
    rw [strongDualSubdifferential_eq_iInter_supportHalfspaces f x hx]
    exact isClosed_iInter fun y ↦ isClosed_subgradientSupportHalfspace f x y
  · -- Outside the effective domain, the owner subdifferential is empty, so its strong-dual view
    -- is empty as well.
    rw [strongDualSubdifferential_linearPreimage f x]
    simp [subdifferential_eq_empty_of_not_mem_effective_domain hx]

/-- Theorem 3.1 (2): for an extended-real-valued function, the continuous-dual subdifferential
`∂ₛ f(x)` is a convex subset of the dual space. -/
theorem convex_strongDualSubdifferential (f : E → EReal) (x : E) :
    Convex ℝ (∂ₛ f(x)) := by
  -- Transport owner-level convexity through the canonical coercion linear map.
  rw [strongDualSubdifferential_linearPreimage f x]
  exact
    (convex_subdifferential f x).linear_preimage
      (ContinuousLinearMap.coeLM ℝ : StrongDual ℝ E →ₗ[ℝ] Module.Dual ℝ E)

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- In finite dimensions, every algebraic functional is continuous, so the strong-dual view of
`subdifferential f x` is exactly its image under the canonical equivalence
`LinearMap.toContinuousLinearMap`. -/
theorem strongDualSubdifferential_eq_image_subdifferential
    (f : E → EReal) (x : E) :
    ∂ₛ f(x) =
      (LinearMap.toContinuousLinearMap : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E) ''
        ∂ f(x) := by
  ext g
  constructor
  · intro hg
    refine ⟨(g : Module.Dual ℝ E), ?_, ?_⟩
    · simpa using hg
    · ext y
      rfl
  · rintro ⟨g, hg, rfl⟩
    simpa [mem_strongDualSubdifferential] using hg

end

section

open InnerProductSpace (toDualMap)

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Euclidean/vector-side view of `subdifferential f x`, obtained by transporting the Chapter
3 strong-dual bridge `strongDualSubdifferential f x` back to vectors through the Riesz map. This
is a `bridge/view` API; `subdifferential` remains the owner abstraction. -/
abbrev euclideanSubdifferential (f : E → EReal) (x : E) : Set E :=
  (toDualMap ℝ E) ⁻¹' strongDualSubdifferential f x

/-- Membership in `euclideanSubdifferential f x` is definitionally membership of the corresponding
Riesz functional in `strongDualSubdifferential f x`. -/
@[simp] theorem mem_euclideanSubdifferential_iff
    {f : E → EReal} {x z : E} :
    z ∈ euclideanSubdifferential f x ↔
      toDualMap ℝ E z ∈ strongDualSubdifferential f x :=
  Iff.rfl

end

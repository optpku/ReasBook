/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u}

/-- The finite domain of an extended-real-valued function consists of the points in the owner
`effective_domain` whose value is also not `⊥`. -/
def finite_domain (f : E → EReal) : Set E :=
  {x | x ∈ effective_domain f ∧ f x ≠ ⊥}

/-- Membership in the finite domain means belonging to the owner `effective_domain` and avoiding
`⊥`. -/
@[simp] theorem mem_finite_domain {f : E → EReal} {x : E} :
    x ∈ finite_domain f ↔ x ∈ effective_domain f ∧ f x ≠ ⊥ :=
  Iff.rfl

/-- If `f` never takes the value `⊥`, then its finite domain is exactly its owner
`effective_domain`. -/
theorem finite_domain_eq_effective_domain {f : E → EReal} (h_ne_bot : ∀ x, f x ≠ ⊥) :
    finite_domain f = effective_domain f := by
  ext x
  simp [finite_domain, h_ne_bot x]

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Definition 3.10: an extended-real-valued function is differentiable at `x` when `x` lies in
the interior of its finite domain and the real-valued restriction `y ↦ (f y).toReal` is
differentiable there. -/
def is_differentiable_at (f : E → EReal) (x : E) : Prop :=
  x ∈ interior (finite_domain f) ∧
    DifferentiableAt ℝ (fun y ↦ (f y).toReal) x

-- Proof sketch: Fréchet differentiability of `y ↦ (f y).toReal` is, by definition, existence of a
-- continuous linear derivative. The chapter-specific content is only the common hypothesis
-- `x ∈ interior (finite_domain f)`, so the witness theorem should expose the owner predicate
-- `HasFDerivAt` directly rather than a parallel local wrapper.
/-- A function is differentiable at `x` exactly when its real-valued restriction has a Fréchet
derivative there, together with the finite-domain interior condition from Definition 3.10. -/
theorem is_differentiable_at_iff_exists_hasFDerivAt {f : E → EReal} {x : E} :
    is_differentiable_at f x ↔
      ∃ g : StrongDual ℝ E,
        x ∈ interior (finite_domain f) ∧
          HasFDerivAt (fun y ↦ (f y).toReal) g x := by
  constructor
  · rintro ⟨hx, hdiff⟩
    rcases hdiff with ⟨g, hg⟩
    exact ⟨g, hx, hg⟩
  · rintro ⟨g, hx, hg⟩
    exact ⟨hx, ⟨g, hg⟩⟩

end

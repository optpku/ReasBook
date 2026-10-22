/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Definition_15_6

-- Declarations for this item will be appended below by the statement pipeline.

open Set

noncomputable section

universe u v

section

variable {X : Type u} {Z : Type v}

/- `prompt_add/` is absent in this workspace, so the owner choice is sampled from the nearby
Chapter 10, Chapter 12, and Chapter 15 optimization files.

This item is `source-facing`: it rewrites the linear-composite problem
`min_x (f₁ x + f₂ (A x))` as the split equality-constrained problem on `(x, z)` with constraint
`A x = z`.

Domain sampling identifies the owner stack already present upstream:
- `core/canonical`: `H[f₁, f₂] = admm_objective f₁ f₂` from Definition 15.1 for the product-space
  objective `(x, z) ↦ f₁ x + f₂ z`;
- `core/canonical`: `H_opt[f₁, f₂; A, B, c] = admm_problem_value ...` from Definition 15.1 for
  affine-constrained ADMM values;
- `bridge/view`: `composite_model_objective f₁ (f₂ ∘ A)` from Definition 15.6 for the original
  linear-composite objective;
- `source-facing`: the split graph constraint `A x = z`, represented canonically as `univ.graphOn
  A`.

Primitive data are only `f₁`, `f₂`, and `A`. The bridge is therefore stated directly with the
canonical graph owner `univ.graphOn A` and the existing Chapter 15 value owner `H_opt[...]`,
rather than rebuilding chapter-local wrappers for the same graph and infimum. The first layer
stays over a plain map `A : X → Z`; only the later bridge to `H_opt[f₁, f₂; A, -id, 0]`
reintroduces linearity and additive structure. -/

end

section

variable {X : Type u} {Z : Type v}

-- Proof sketch: identify the graph-feasible set with `univ.graphOn A`; every feasible pair has
-- the form `(x, A x)`, and on that graph `H[f₁, f₂]` agrees with the linear-composite
-- objective, so the two sets of attainable values have the same infimum.
/-- Definition 15.7: the problem `min_x (f₁ x + f₂ (A x))` is equivalently written as minimizing
the ADMM objective `H[f₁, f₂]` over the graph-feasible pairs satisfying `A x = z`, equivalently
`A x - z = 0` when subtraction is available. -/
theorem admm_linear_composite_primal_infimum_eq_split_infimum
    (f₁ : X → EReal) (f₂ : Z → EReal) (A : X → Z) :
    sInf (Set.range (composite_model_objective f₁ (f₂ ∘ A))) =
      sInf (Set.image (H[f₁, f₂]) (univ.graphOn A)) := by
  have himage :
      Set.image (H[f₁, f₂]) (univ.graphOn A) =
        Set.range (composite_model_objective f₁ (f₂ ∘ A)) := by
    ext r
    constructor
    · rintro ⟨⟨x, z⟩, hxz, rfl⟩
      have hz : A x = z := by
        simpa using hxz
      subst z
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨(x, A x), ?_, ?_⟩
      · simp
      · rfl
  exact congrArg sInf himage.symm

end

section

variable {X : Type u} {Z : Type v}
variable {𝕜 : Type*} [Semiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommGroup Z] [Module 𝕜 Z]

/-- Under the additive-group structure needed to write the ADMM affine constraint as
`A x + (-id) z = 0`, the split feasible set is exactly the specialized ADMM feasible set. -/
theorem graphOn_eq_admm_feasible_set
    (A : X →ₗ[𝕜] Z) :
    univ.graphOn A =
      admm_feasible_set A (-LinearMap.id : Z →ₗ[𝕜] Z) 0 := by
  ext xz
  rcases xz with ⟨x, z⟩
  constructor
  · intro hx
    have hAz : A x = z := by
      simpa using hx
    rw [mem_admm_feasible_set]
    simpa [sub_eq_add_neg] using sub_eq_zero.mpr hAz
  · intro hx
    rw [mem_admm_feasible_set] at hx
    have hAz : A x = z := by
      exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hx)
    simp [hAz]

-- Proof sketch: rewrite the feasible set as the specialized ADMM feasible set
-- `A x + (-id) z = 0`. The constrained problem objective contributes only the feasible values
-- `H[f₁, f₂] (x, z)` plus the infeasible value `⊤`, and adding `⊤` to a set of objective values
-- does not change its infimum.
/-- The split infimum over the graph-feasible pairs is the Chapter 15 ADMM primal value
specialized to the split constraint `A x - z = 0`, that is, `B = -id` and `c = 0`. -/
theorem admm_linear_composite_split_infimum_eq_admm_problem_value
    (f₁ : X → EReal) (f₂ : Z → EReal) (A : X →ₗ[𝕜] Z) :
    sInf (Set.image (H[f₁, f₂]) (univ.graphOn A)) =
      H_opt[f₁, f₂; A, (-LinearMap.id : Z →ₗ[𝕜] Z), 0] := by
  rw [admm_problem_value_eq_sInf, ← graphOn_eq_admm_feasible_set A]
  apply le_antisymm
  · apply le_sInf
    rintro r ⟨xz, rfl⟩
    by_cases hxz : xz ∈ univ.graphOn A
    · exact sInf_le ⟨xz, hxz, by
        simpa using (constrained_problem_objective_of_mem (H[f₁, f₂]) hxz).symm⟩
    · simp [constrained_problem_objective_of_not_mem (H[f₁, f₂]) hxz]
  · apply le_sInf
    rintro r ⟨xz, hxz, rfl⟩
    exact sInf_le ⟨xz, by
      simpa using constrained_problem_objective_of_mem (H[f₁, f₂]) hxz⟩

/-- Under additive-group hypotheses on the split variable space, the linear-composite primal
infimum is exactly the Chapter 15 ADMM primal value specialized to `A x - z = 0`. -/
theorem admm_linear_composite_primal_infimum_eq_admm_problem_value
    (f₁ : X → EReal) (f₂ : Z → EReal) (A : X →ₗ[𝕜] Z) :
    sInf (Set.range (composite_model_objective f₁ (f₂ ∘ A))) =
      H_opt[f₁, f₂; A, (-LinearMap.id : Z →ₗ[𝕜] Z), 0] := by
  rw [← admm_linear_composite_split_infimum_eq_admm_problem_value]
  exact admm_linear_composite_primal_infimum_eq_split_infimum f₁ f₂ A

end

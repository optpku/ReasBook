/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Definition 3.2 is `source-facing` in the chapter subgradient API. The primitive mathematical
data already lives in Definition 3.1 as the predicate `is_subgradient_at`; the owner object
introduced here is the set-valued map `subdifferential`. Later normed/real-valued files only build
bridge/view APIs such as `strongDualSubdifferential` and `subdifferentialAt`, so this file keeps
just the owner set and its atomic membership/emptiness lemmas. -/

/-- Definition 3.2: the subdifferential `∂ f(x)` is the set of dual vectors `g ∈ E*` such that
`g` is a subgradient of `f` at `x` in the sense of Definition 3.1. Consequently, when
`x ∉ dom(f)`, this set is empty by definition. -/
def subdifferential (f : E → EReal) (x : E) : Set (Module.Dual ℝ E) :=
  is_subgradient_at f x

notation "∂" f "(" x ")" => subdifferential f x

-- Proof sketch: `subdifferential` is defined by collecting the subgradients from Definition 3.1,
-- so membership is exactly the predicate `is_subgradient_at`.
/-- Membership in the subdifferential means being a subgradient at the given point. -/
@[simp] lemma mem_subdifferential {f : E → EReal} {x : E} {g : Module.Dual ℝ E} :
    g ∈ ∂ f(x) ↔ is_subgradient_at f x g :=
  Iff.rfl

-- Proof sketch: extensionality on `g`; after rewriting membership with `mem_subdifferential`, the
-- hypothesis `x ∉ effective_domain f` makes the defining domain condition in
-- `is_subgradient_at` false, so both sides are empty.
/-- Outside the effective domain, the subdifferential is empty. -/
@[simp] theorem subdifferential_eq_empty_of_not_mem_effective_domain
    {f : E → EReal} {x : E} (hx : x ∉ effective_domain f) :
    ∂ f(x) = ∅ := by
  ext g
  constructor
  · intro hg
    exact (hx hg.1).elim
  · intro hg
    exact False.elim hg

/-- Helper for Definition 3.2: evaluating a convex combination of dual vectors at a point is
bounded by the larger endpoint evaluation. -/
lemma evalConvexCombo_le_max
    {g₁ g₂ : Module.Dual ℝ E} {z : E} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ((a • g₁ + b • g₂) z) ≤ max (g₁ z) (g₂ z) := by
  -- Expand point-evaluation into a scalar convex combination and use the standard real estimate.
  simpa [smul_eq_mul] using (Convex.combo_le_max (g₁ z) (g₂ z) ha hb hab)

-- Proof sketch: if `g₁` and `g₂` satisfy all subgradient inequalities at `x`, then every convex
-- combination `t • g₁ + (1 - t) • g₂` satisfies the same inequalities by taking the same convex
-- combination of the two affine lower bounds; if `x ∉ effective_domain f`, the subdifferential is
-- empty, hence convex.
/-- The subdifferential `∂ f(x)` is a convex subset of the ambient dual space. -/
theorem convex_subdifferential (f : E → EReal) (x : E) :
    Convex ℝ (∂ f(x)) := by
  rw [convex_iff_add_mem]
  intro g₁ hg₁ g₂ hg₂ a b ha hb hab
  rw [mem_subdifferential] at hg₁ hg₂ ⊢
  refine ⟨hg₁.1, ?_⟩
  intro y
  let r₁ : ℝ := g₁ (y - x)
  let r₂ : ℝ := g₂ (y - x)
  -- Rewrite the two membership hypotheses into affine lower bounds at the same point `y`.
  have hy₁ : f x + (r₁ : EReal) ≤ f y := by
    simpa [r₁, ge_iff_le] using hg₁.2 y
  have hy₂ : f x + (r₂ : EReal) ≤ f y := by
    simpa [r₂, ge_iff_le] using hg₂.2 y
  -- The dual evaluation of the convex combination is bounded by the larger endpoint evaluation.
  have hcombo : ((a • g₁ + b • g₂) (y - x)) ≤ max r₁ r₂ := by
    simpa [r₁, r₂] using
      evalConvexCombo_le_max (g₁ := g₁) (g₂ := g₂) (z := y - x) ha hb hab
  -- Compare against the larger of the two known affine lower bounds and conclude by transitivity.
  by_cases hle : r₁ ≤ r₂
  · have hcombo' : ((a • g₁ + b • g₂) (y - x)) ≤ r₂ := by
      simpa [max_eq_right hle] using hcombo
    have hcomboE : (((a • g₁ + b • g₂) (y - x) : ℝ) : EReal) ≤ (r₂ : EReal) :=
      EReal.coe_le_coe hcombo'
    have hsum :
        f x + ((((a • g₁ + b • g₂) (y - x) : ℝ) : EReal)) ≤ f x + (r₂ : EReal) := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hcomboE (f x)
    exact hsum.trans hy₂
  · have hle' : r₂ ≤ r₁ := le_of_not_ge hle
    have hcombo' : ((a • g₁ + b • g₂) (y - x)) ≤ r₁ := by
      simpa [max_eq_left hle'] using hcombo
    have hcomboE : (((a • g₁ + b • g₂) (y - x) : ℝ) : EReal) ≤ (r₁ : EReal) :=
      EReal.coe_le_coe hcombo'
    have hsum :
        f x + ((((a • g₁ + b • g₂) (y - x) : ℝ) : EReal)) ≤ f x + (r₁ : EReal) := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hcomboE (f x)
    exact hsum.trans hy₁

end

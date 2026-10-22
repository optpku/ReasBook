/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Pointwise

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-
Definition 3.3 is `source-facing` in the Chapter 3 convex-analysis API: it introduces the normal
cone of a set at a point. The `core/canonical` owner declaration for this notion in the project is
Chapter 2's `polar_cone`, applied to the translated set `S -ᵥ {x}`. The only primitive data here
is the set-valued map `normal_cone`; membership and the feasible-point identification with
`polar_cone` are derived API.
-/

/-- Definition 3.3: the normal cone of a set `S ⊆ E` at `x` consists of the dual vectors that are
nonpositive on every displacement `z - x` with `z ∈ S`; when `x ∉ S`, the normal cone is empty.
This source-facing cone is the Chapter 2 owner `polar_cone` of the translated set `S -ᵥ {x}`. -/
def normal_cone (S : Set E) (x : E) : Set (Module.Dual ℝ E) :=
  { y | x ∈ S ∧ y ∈ polar_cone (S -ᵥ ({x} : Set E)) }

@[inherit_doc normal_cone] notation:max "N[" S "](" x ")" => normal_cone S x

-- Proof sketch: if `x ∈ S`, the extra feasibility guard in the definition of `normal_cone` is
-- redundant, so the source-facing cone is exactly the owner `polar_cone` of the translated set.
/-- At a feasible point, the normal cone is the polar cone of the translated feasible-displacement
set. -/
@[simp] lemma normal_cone_eq_polar_cone_of_mem (S : Set E) {x : E} (hx : x ∈ S) :
    normal_cone S x = polar_cone (S -ᵥ ({x} : Set E)) := by
  ext y
  simp [normal_cone, hx]

-- Proof sketch: rewrite `normal_cone` to the owner `polar_cone` of the translated set `S -ᵥ {x}`;
-- using `Set.vsub_singleton`, membership in that polar cone is exactly the textbook inequality on
-- the displacements `z - x` with `z ∈ S`.
/-- At a point `x ∈ S`, membership in the normal cone means being nonpositive on every feasible
displacement `z - x` with `z ∈ S`. -/
lemma mem_normal_cone (S : Set E) {x : E} (hx : x ∈ S) (y : Module.Dual ℝ E) :
    y ∈ normal_cone S x ↔ ∀ z ∈ S, y (z - x) ≤ 0 := by
  rw [normal_cone_eq_polar_cone_of_mem S hx]
  change y ∈ polar_cone (S -ᵥ ({x} : Set E)) ↔ ∀ z ∈ S, y (z - x) ≤ 0
  rw [mem_polar_cone, Set.vsub_singleton]
  constructor
  · intro hy z hz
    exact hy (z - x) ⟨z, hz, rfl⟩
  · intro hy
    rintro _ ⟨z, hz, rfl⟩
    exact hy z hz

-- Proof sketch: the owner-derived definition is explicitly empty when `x ∉ S`.
/-- Outside the set, the normal cone is empty. -/
lemma normal_cone_eq_empty_of_not_mem (S : Set E) {x : E} (hx : x ∉ S) :
    normal_cone S x = ∅ := by
  ext y
  simp [normal_cone, hx]

end

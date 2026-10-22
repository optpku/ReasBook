/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_6
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators Gradient

universe u v

/- Definition 11.3 is recall-only in the block-coordinate composite-model setup.

Domain sampling identifies the existing owner abstractions:
- Chapter 10's `composite_model_objective` for the source-facing composite objective `F = f + g`;
- Chapter 6's owner `separableSum`, used on `PiLp 2 E` through the bridge `PiLp.separableSum`,
  for the block-separable term `x ↦ ∑ i, g_i (x_i)`;
- mathlib's `PiLp.single` for the block insertion map `𝒰ᵢ`;
- the ambient gradient `∇` on `PiLp 2 E`, with block coordinates as derived API;
- mathlib's `PiLp.norm_eq_of_L2` for the `L²` product norm formula.

The primitive data are only the smooth term `f`, the block penalties `g_i`, and the ambient
product space `PiLp (2 : ENNReal) E`. The block insertion map is canonical singleton data, while
the block gradients are derived from the ambient gradient rather than primitive fields. The old
local declarations were exact-interface wrappers around these owners, so the file should recall
those owners directly and keep only thin source-facing bridges for the textbook surfaces
`𝒰ᵢ`, `∇ᵢ f`, and `F(x) = f(x) + ∑ i, g_i(x_i)`. -/

/- Definition 11.3: on the block product `PiLp (2 : ENNReal) E`, the objective
`F(x) = f(x) + ∑ i, g_i(x_i)` is the canonical composite objective
`composite_model_objective f (PiLp.separableSum g)`, the block insertion map `𝒰ᵢ` is the canonical
singleton insertion `PiLp.single 2 i`, the block partial gradient `∇ᵢ f(x)` is the `i`-th
coordinate of `∇ f(x)`, and the block norm formula is `PiLp.norm_eq_of_L2`. -/
recall PiLp.separableSum
recall composite_model_objective
recall PiLp.single
recall PiLp.single_eq_same
recall PiLp.single_eq_of_ne
recall PiLp.norm_eq_of_L2

scoped[Gradient] notation "𝒰[" i "]" => @PiLp.single (2 : ENNReal) _ _ (Classical.decEq _) _ i

section

variable {ι : Type v} [Fintype ι]
variable {E : ι → Type u}

/-- Evaluating the Chapter 11 block composite objective means evaluating the Chapter 10 composite
objective with the Chapter 6 block-separable regularizer. -/
@[simp] theorem composite_model_objective_separableSum_apply
    (f : PiLp (2 : ENNReal) E → EReal) (g : ∀ i, E i → EReal) (x : PiLp (2 : ENNReal) E) :
    composite_model_objective f (PiLp.separableSum g) x = f x + ∑ i, g i (x i) := by
  simp

end

section

variable {ι : Type v}
variable {E : ι → Type u}
variable [∀ i, Zero (E i)]

/-- Definition 11.3 uses the canonical block insertion map `𝒰ᵢ : Eᵢ → PiLp 2 E`, implemented by
`PiLp.single`. At the distinguished block it returns the inserted vector. -/
@[simp] theorem block_coordinate_embedding_apply_same
    (i : ι) (d : E i) :
    (𝒰[i] d) i = d := by
  classical
  simp [PiLp.single_eq_same]

/-- Away from the distinguished block, the canonical insertion map `𝒰ᵢ` vanishes. -/
@[simp] theorem block_coordinate_embedding_apply_ne
    {i j : ι} (h : j ≠ i) (d : E i) :
    (𝒰[i] d) j = 0 := by
  classical
  simp [PiLp.single_eq_of_ne, h]

end

section

variable {ι : Type v} [Fintype ι]
variable {E : ι → Type u}
variable [∀ i, NormedAddCommGroup (E i)]
variable [∀ i, InnerProductSpace ℝ (E i)]
variable [∀ i, CompleteSpace (E i)]

/-- Definition 11.3's block partial gradient `∇ᵢ f(x)` is the `i`-th coordinate of the ambient
gradient `∇ f(x)` on `PiLp 2 E`. This bridge only needs the ambient Hilbert-space structure used
to form `∇ f x`, not finite-dimensional block coordinates. -/
abbrev block_partial_gradient
    (i : ι) (f : PiLp (2 : ENNReal) E → ℝ) : PiLp (2 : ENNReal) E → E i :=
  fun x ↦ (∇ f x) i

notation "∇[" i "] " f:arg => block_partial_gradient i f

/-- Evaluating the source-facing block-gradient notation gives the corresponding coordinate of the
ambient gradient. -/
@[simp] theorem block_partial_gradient_eq_gradient
    (f : PiLp (2 : ENNReal) E → ℝ) (x : PiLp (2 : ENNReal) E) (i : ι) :
    (∇[i] f) x = (∇ f x) i :=
  rfl

/-- The full gradient decomposes into its block partial gradients:
`∇ f(x) = (∇₁ f(x), …, ∇ₚ f(x))`. -/
theorem gradient_eq_block_partial_gradient
    (f : PiLp (2 : ENNReal) E → ℝ) (x : PiLp (2 : ENNReal) E) :
    ∇ f x = fun i ↦ (∇[i] f) x :=
  rfl

end

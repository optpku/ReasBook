/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Instances.EReal.Lemmas
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Helper for Lemma 2.7: the primal-space support function obtained by evaluating the chapter
owner `support_function` along the Riesz map `toDualMap`. -/
noncomputable abbrev support_function_primal_lemma_2_7 (C : Set E) : E → EReal :=
  fun x ↦ support_function C (toDualMap ℝ E x)

/-- Textbook notation for the primal-space support function. -/
local notation "σ[" C "]" => support_function_primal_lemma_2_7 C

-- Rewrite the local primal owner back to the chapter owner specialized along `toDualMap`.
/-- Helper for Lemma 2.7: evaluating `σ[C]` at `x` is the same as evaluating
`support_function C` at the dual vector corresponding to `x`. -/
@[simp] theorem support_function_primal_apply_lemma_2_7 (C : Set E) (x : E) :
    σ[C] x = support_function C (toDualMap ℝ E x) :=
  rfl

-- Normalize the primal support function to the `sSup` formula used by both invariance proofs.
/-- Helper for Lemma 2.7: the primal support function equals the supremum of the inner-product
pairings over the underlying set. -/
theorem support_function_eq_sSup_lemma_2_7 (C : Set E) (x : E) :
    σ[C] x = sSup ((fun c : E ↦ (inner ℝ x c : EReal)) '' C) := by
  simp [support_function_primal_lemma_2_7, support_function_apply]

-- Proof sketch: one inequality is immediate from `A ⊆ closure A`. For the reverse inequality,
-- use that every continuous linear functional given by `InnerProductSpace.toDualMap ℝ E x` has the
-- same supremum on `A` and on `closure A`.
/-- Lemma 2.7 (1): replacing a set by its topological closure does not change its primal-space
support function `σ[A]`. -/
lemma support_function_eq_support_function_closure (A : Set E) :
    σ[A] = σ[closure A] := by
  ext x
  rw [support_function_eq_sSup_lemma_2_7, support_function_eq_sSup_lemma_2_7]
  refine le_antisymm ?_ ?_
  · refine sSup_le ?_
    rintro _ ⟨y, hyA, rfl⟩
    exact le_sSup ⟨y, subset_closure hyA, rfl⟩
  · refine sSup_le ?_
    rintro _ ⟨y, hyA, rfl⟩
    let f : E → EReal := fun z ↦ (inner ℝ x z : EReal)
    have hf_cont : Continuous f := by
      simpa [f, InnerProductSpace.toDualMap_apply_apply] using
        (continuous_coe_real_ereal.comp (toDualMap ℝ E x).continuous)
    have hsubset : f '' A ⊆ Set.Iic (sSup (f '' A)) := by
      rintro _ ⟨z, hzA, rfl⟩
      exact le_sSup (Set.mem_image_of_mem f hzA)
    have hclosure :
        closure (f '' A) ⊆ Set.Iic (sSup (f '' A)) :=
      closure_minimal hsubset isClosed_Iic
    have hy_mem : f y ∈ closure (f '' A) := by
      exact (image_closure_subset_closure_image hf_cont) ⟨y, hyA, rfl⟩
    exact hclosure hy_mem

/-- Pointwise rewriting companion for `support_function_eq_support_function_closure`. -/
@[simp] theorem support_function_closure_apply (A : Set E) (x : E) :
    σ[closure A] x = σ[A] x := by
  simpa [closure_closure] using
    congrArg (fun f : E → EReal ↦ f x) (support_function_eq_support_function_closure A).symm

-- Proof sketch: one inequality is immediate from `A ⊆ convexHull ℝ A`. For the reverse
-- inequality, write a point of `convexHull ℝ A` as a convex combination of points of `A`, use the
-- linearity of the dual functional, and bound the resulting convex combination by the supremum
-- over `A`.
/-- Lemma 2.7 (2): replacing a set by its convex hull does not change its primal-space support
function `σ[A]`. -/
lemma support_function_eq_support_function_convexHull (A : Set E) :
    σ[A] = σ[convexHull ℝ A] := by
  ext x
  rw [support_function_eq_sSup_lemma_2_7, support_function_eq_sSup_lemma_2_7]
  refine le_antisymm ?_ ?_
  · refine sSup_le ?_
    rintro _ ⟨y, hyA, rfl⟩
    exact le_sSup ⟨y, subset_convexHull ℝ A hyA, rfl⟩
  · refine sSup_le ?_
    rintro _ ⟨y, hyA, rfl⟩
    have hconv :
        ConvexOn ℝ (Set.univ : Set E) (fun z : E ↦ inner ℝ x z) := by
      simpa [InnerProductSpace.toDualMap_apply_apply] using
        LinearMap.convexOn (toDualMap ℝ E x).toLinearMap
          (convex_univ : Convex ℝ (Set.univ : Set E))
    obtain ⟨z, hzA, hzmax⟩ :=
      hconv.exists_ge_of_mem_convexHull (Set.subset_univ A) hyA
    exact
      (show (inner ℝ x y : EReal) ≤ (inner ℝ x z : EReal) from by
        exact_mod_cast hzmax).trans <|
        le_sSup ⟨z, hzA, rfl⟩

/-- Pointwise rewriting companion for `support_function_eq_support_function_convexHull`. -/
@[simp] theorem support_function_convexHull_apply (A : Set E) (x : E) :
    σ[convexHull ℝ A] x = σ[A] x := by
  simpa [(convex_convexHull ℝ A).convexHull_eq] using
    congrArg (fun f : E → EReal ↦ f x) (support_function_eq_support_function_convexHull A).symm

end

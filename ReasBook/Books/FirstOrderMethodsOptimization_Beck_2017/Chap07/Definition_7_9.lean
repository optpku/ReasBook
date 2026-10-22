/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

namespace Function

noncomputable section

section

variable {n : ℕ}

/- Definition 7.9 is `source-facing`: the textbook notion is a proper function on `ℝ^n` that is
invariant under the signed-permutation symmetries collected in `Λ^G_n`. Since the present item
also gives the canonical normal-form characterization `f x = f (|x|↓)`, the clean owner-level
API keeps that canonical representative visible as a concrete rearrangement operator and models the
property itself as a properness class on functions. -/

/-- The decreasing rearrangement of the coordinates of `x`, obtained by sorting the coordinate
list in weakly decreasing order and reading it back as a vector in `ℝ^n`. -/
def descendingRearrangement (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ (((List.ofFn x).mergeSort (· ≥ ·)).getD i 0)

scoped postfix:max "↓" => Function.descendingRearrangement

open scoped Function

-- Proof sketch: unfold `descendingRearrangement`; evaluation at coordinate `i` is definitionally
-- the `i`-th entry of the decreasingly sorted coordinate list.
/-- Evaluating `descendingRearrangement x` returns the corresponding entry of the decreasingly
sorted coordinate list of `x`. -/
theorem descendingRearrangement_apply (x : Fin n → ℝ) (i : Fin n) :
    descendingRearrangement x i = (((List.ofFn x).mergeSort (· ≥ ·)).getD i 0) := by
  -- Unfolding the rearrangement shows that coordinate evaluation is definitional.
  rfl

/-- Definition 7.9: a proper extended-real-valued function on `ℝ^n` is absolutely permutation
symmetric when it depends only on the decreasing rearrangement `|x|↓` of the absolute coordinate
values, equivalently on the signed-permutation orbit of `x`. -/
class IsAbsolutelyPermutationSymmetric (f : (Fin n → ℝ) → EReal) : Prop
    where
  ne_bot : ∀ x, f x ≠ ⊥
  effective_domain_nonempty : {x | f x < ⊤}.Nonempty
  map_eq_abs_descendingRearrangement (x : Fin n → ℝ) : f x = f (|x|↓)

-- Proof sketch: unfold `Function.IsAbsolutelyPermutationSymmetric`; the only extra datum beyond
-- properness is exactly the normal-form identity `f x = f (|x|↓)` for every `x`.
/-- An extended-real-valued function on `ℝ^n` is absolutely permutation symmetric exactly when it
never takes the value `-∞`, has nonempty effective domain, and is unchanged by replacing `x` with
the decreasing rearrangement of its absolute coordinate values. -/
theorem isAbsolutelyPermutationSymmetric_iff_forall_eq_abs_descendingRearrangement
    (f : (Fin n → ℝ) → EReal) :
    IsAbsolutelyPermutationSymmetric f ↔
      (∀ x, f x ≠ ⊥) ∧ {x | f x < ⊤}.Nonempty ∧
        ∀ x : Fin n → ℝ, f x = f (|x|↓) := by
  constructor
  · intro hf
    -- Read the three required properties directly from the class fields.
    exact ⟨hf.ne_bot, hf.effective_domain_nonempty, hf.map_eq_abs_descendingRearrangement⟩
  · rintro ⟨h_ne_bot, h_nonempty, h_map⟩
    -- Repackage the properness data and the rearrangement invariance into the class.
    exact ⟨h_ne_bot, h_nonempty, h_map⟩

-- Proof sketch: the constant zero function is proper, and the defining identity
-- `f x = f (|x|↓)` is immediate because both sides evaluate to `0`.
/-- The constant zero extended-real-valued function on `ℝ^n` is absolutely permutation
symmetric. -/
instance : IsAbsolutelyPermutationSymmetric (fun _ : Fin n → ℝ ↦ (0 : EReal)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    -- The constant zero function never takes the value `-∞`.
    simp
  · -- The origin lies in the effective domain because `0 < ⊤` in `EReal`.
    refine ⟨0, ?_⟩
    simp
  · intro x
    -- Rearranging the input does not change a constant function.
    simp

end

end

end Function

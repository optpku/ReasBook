/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

namespace Function

section

variable {ι : Type*}

/- Definition 7.3 is `source-facing`: the textbook property is invariance under coordinatewise
absolute value on `ℝ^n`, here expressed on the canonical owner space `ι → ℝ` and specializing to
`ℝ^n` when `ι = Fin n`. The primitive data are just that invariance identity. The canonical
bridge/view toward the nonnegative cone is the coordinatewise map
`nnabs : (ι → ℝ) → (ι → ℝ≥0)`, and factorization through that map is derived API rather than
primitive data. -/

/-- The coordinatewise map from `ι → ℝ` to `ι → ℝ≥0` obtained by taking absolute values. When
`ι = Fin n`, this is the usual map from `ℝ^n` to the nonnegative orthant. -/
def nnabs (x : ι → ℝ) : ι → NNReal :=
  Real.nnabs ∘ x

/-- Definition 7.3: an extended-real-valued function on `ι → ℝ` is absolutely symmetric when it
depends only on the coordinatewise absolute values of its input, equivalently when `f x = f (|x|)`
for every `x`. For `ι = Fin n`, this is the textbook notion on `ℝⁿ`. -/
def IsAbsolutelySymmetric (f : (ι → ℝ) → EReal) : Prop :=
  ∀ x, f x = f (|x|)

@[simp] theorem nnabs_apply (x : ι → ℝ) (i : ι) :
    nnabs x i = Real.nnabs (x i) :=
  rfl

/-- Coercing `nnabs x` back to `ι → ℝ` recovers the coordinatewise absolute-value function `|x|`.
When `ι = Fin n`, this is the absolute-value vector in `ℝ^n`. -/
@[simp] theorem coe_nnabs (x : ι → ℝ) : (fun i ↦ ((nnabs x i : NNReal) : ℝ)) = |x| := by
  funext i
  simp [nnabs, Real.coe_nnabs]

/-- Helper for Definition 7.3: taking coordinatewise absolute values does not change the image of
`nnabs`. -/
@[simp] theorem nnabs_abs (x : ι → ℝ) : nnabs (|x|) = nnabs x := by
  -- Compare the two maps coordinatewise and use `abs_abs` on each coordinate.
  funext i
  simp [nnabs]

-- Proof sketch: if `f` is absolutely symmetric, define `g` on `ι → ℝ≥0` by restricting `f` along
-- the coercion `(ι → NNReal) → (ι → ℝ)`. Conversely, if `f` factors through `nnabs`,
-- then `f x` depends only on `|x|`.
/-- An extended-real-valued function on `ι → ℝ` is absolutely symmetric exactly when it factors
through the coordinatewise absolute-value map into `ι → ℝ≥0`. For `ι = Fin n`, this recovers the
factorization through the nonnegative orthant `ℝ_+^n`. -/
theorem isAbsolutelySymmetric_iff_exists_factor_through_nnabs (f : (ι → ℝ) → EReal) :
    IsAbsolutelySymmetric f ↔ ∃ g : (ι → NNReal) → EReal, f = g ∘ nnabs := by
  constructor
  · intro hf
    -- Restrict `f` to the nonnegative orthant to obtain the factor.
    refine ⟨fun y ↦ f (fun i ↦ ((y i : NNReal) : ℝ)), ?_⟩
    -- Route correction: prove equality of functions by evaluating at an arbitrary `x`.
    funext x
    calc
      f x = f (|x|) := hf x
      _ = f (fun i ↦ ((nnabs x i : NNReal) : ℝ)) := by rw [coe_nnabs]
      _ = (fun y ↦ f (fun i ↦ ((y i : NNReal) : ℝ))) (nnabs x) := rfl
  · rintro ⟨g, rfl⟩ x
    -- After factoring through `nnabs`, invariance is exactly the statement `nnabs (|x|) = nnabs x`.
    simp [Function.comp, nnabs_abs]

end

end Function

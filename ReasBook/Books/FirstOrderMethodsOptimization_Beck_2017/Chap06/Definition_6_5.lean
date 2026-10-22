/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_2
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable {ι : Type*} [Fintype ι]

local notation "E" => PiLp 2 (fun _ : ι ↦ ℝ)

/-
Definition 6.5 is `source-facing` in the thresholding domain. Domain sampling against the scalar
owner `𝒯[·]` from Definition 6.2, the vector owner `T_[·]` from Definition 6.3, mathlib's scalar
interval projection owner `Set.projIcc`, and the coordinatewise `WithLp.map` lift shows that the
primitive data here are a nonnegative lower threshold and an extended nonnegative upper bound. As
in Definition 6.3, the public owner should live on the canonical `PiLp 2` finite product, while
the scalar clipping is derived from the canonical interval projection owner and the constant-
threshold unclipped specialization should bridge directly to `T_[·]`.
-/

/-- Definition 6.5: for a lower-threshold family `ω : ι → NNReal` and an upper-bound family
`α : ι → ENNReal`, the two-sided soft-thresholding operator acts coordinatewise on the canonical
`L²` product `PiLp 2 (fun _ : ι ↦ ℝ)`; its value at `i` is the truncated magnitude obtained from
`|x i|`, lower threshold `ω i`, and upper bound `α i`, multiplied by `Real.sign (x i)`.
Specializing to `EuclideanSpace ℝ ι`, and then to `ι = Fin n`, recovers the textbook operator on
`ℝ^n`, with `α i = ∞` allowed. -/
def twoSidedSoftThreshold (ω : ι → NNReal) (α : ι → ENNReal) : E → E :=
  WithLp.map 2 <|
    Pi.map fun i ↦
      fun t ↦
        (if hα : α i = ⊤ then
           |𝒯[(ω i : ℝ)] t|
         else
           Set.projIcc 0 (α i).toReal (by positivity) |𝒯[(ω i : ℝ)] t|) * Real.sign t

@[inherit_doc] scoped[TwoSidedSoftThreshold] notation "𝓢[" ω ", " α "]" =>
  twoSidedSoftThreshold ω α

open scoped SoftThreshold TwoSidedSoftThreshold

section

omit [Fintype ι]

/-- Helper for Definition 6.5: the `SignType.sign` coercion agrees with `Real.sign` on `ℝ`. -/
private theorem signType_sign_coe_eq_real_sign (t : ℝ) :
    (((SignType.sign t : SignType) : ℝ)) = Real.sign t := by
  -- Compare the three scalar sign regimes directly.
  obtain hneg | rfl | hpos := lt_trichotomy t 0
  · simp [Real.sign_of_neg hneg, SignType.sign, hneg, not_lt.mpr hneg.le]
  · simp [Real.sign_zero]
  · simp [Real.sign_of_pos hpos, SignType.sign, hpos]

/-- Helper for Definition 6.5: the magnitude of scalar soft-thresholding is the positive-part
radius `max (|t| - μ) 0`. -/
private theorem abs_soft_thresholding_eq_posPart_sub
    (μ : NNReal) (t : ℝ) :
    |𝒯[(μ : ℝ)] t| = max (|t| - (μ : ℝ)) 0 := by
  by_cases ht : t = 0
  · -- At the origin the thresholded value is zero, so its magnitude vanishes.
    simp [ht, soft_thresholding_apply]
  · -- Away from the origin, the sign factor contributes absolute value one.
    have hsign : |(((SignType.sign t : SignType) : ℝ))| = 1 := by
      obtain hneg | hpos := lt_or_gt_of_ne ht
      · rw [signType_sign_coe_eq_real_sign]
        simp [Real.sign_of_neg hneg]
      · rw [signType_sign_coe_eq_real_sign]
        simp [Real.sign_of_pos hpos]
    calc
      |𝒯[(μ : ℝ)] t| = |(|t| - (μ : ℝ))⁺ * (((SignType.sign t : SignType) : ℝ))| := by
        simp [soft_thresholding_apply]
      _ = |(|t| - (μ : ℝ))⁺| * |(((SignType.sign t : SignType) : ℝ))| := by
        rw [abs_mul]
      _ = (|t| - (μ : ℝ))⁺ := by
        rw [hsign, mul_one, abs_of_nonneg (by positivity)]
      _ = max (|t| - (μ : ℝ)) 0 := rfl

/-- Helper for Definition 6.5: in the unbounded branch, the magnitude/sign display collapses to
ordinary scalar soft-thresholding. -/
private theorem abs_soft_thresholding_mul_real_sign_eq_soft_threshold
    (μ : NNReal) (t : ℝ) :
    |𝒯[(μ : ℝ)] t| * Real.sign t = 𝒯[(μ : ℝ)] t := by
  -- Rewrite both sides to the same positive-part times sign expression.
  rw [show (Real.sign t : ℝ) = (((SignType.sign t : SignType) : ℝ)) by
    rw [signType_sign_coe_eq_real_sign]]
  rw [abs_soft_thresholding_eq_posPart_sub]
  rw [soft_thresholding_apply]
  rfl

-- Proof sketch: unfold `twoSidedSoftThreshold`; evaluation at coordinate `i` is definitionally
-- the displayed coordinatewise `WithLp.map` formula.
/-- Evaluating `𝓢[ω, α]` at coordinate `i` gives the scalar truncated magnitude times the sign of
the `i`-th coordinate. -/
@[simp] theorem twoSidedSoftThreshold_apply
    (ω : ι → NNReal) (α : ι → ENNReal) (x : E) (i : ι) :
    𝓢[ω, α] x i =
      (if hα : α i = ⊤ then
         |𝒯[(ω i : ℝ)] (x i)|
       else
         Set.projIcc 0 (α i).toReal (by positivity) |𝒯[(ω i : ℝ)] (x i)|) *
        Real.sign (x i) := by
  -- Unfold the coordinatewise `WithLp.map` definition.
  rfl

-- Proof sketch: when `α i = ∞`, the truncation in the coordinate formula disappears, leaving the
-- scalar soft-threshold magnitude `|𝒯[(ω i : ℝ)] (x i)|`; multiplying by `Real.sign (x i)`
-- recovers the scalar soft-thresholding value from Definition 6.2.
/-- With no upper clipping, the two-sided soft-thresholding operator reduces coordinatewise to the
scalar soft-thresholding map from Definition 6.2. -/
@[simp] theorem twoSidedSoftThreshold_top
    (ω : ι → NNReal) (x : E) :
    (fun i ↦ 𝓢[ω, fun _ ↦ (⊤ : ENNReal)] x i) =
      fun i ↦ 𝒯[(ω i : ℝ)] (x i) := by
  funext i
  -- In the `α = ⊤` branch, the coordinate formula becomes the scalar sign/radius display.
  calc
    𝓢[ω, fun _ ↦ (⊤ : ENNReal)] x i = |𝒯[(ω i : ℝ)] (x i)| * Real.sign (x i) := by
      simp [twoSidedSoftThreshold_apply]
    _ = 𝒯[(ω i : ℝ)] (x i) := by
      rw [abs_soft_thresholding_mul_real_sign_eq_soft_threshold]

end

section

omit [Fintype ι]

-- Proof sketch: extensionality in the coordinate `i`; combine
-- `twoSidedSoftThreshold_top` with the upstream owner evaluation formula
-- `softThreshold_apply`.
/-- The unclipped constant-threshold specialization of Definition 6.5 is exactly the vector
soft-thresholding owner `T_[·]` from Definition 6.3. -/
@[simp] theorem twoSidedSoftThreshold_top_const
    (ω : NNReal) :
    𝓢[(fun _ : ι ↦ ω), fun _ ↦ (⊤ : ENNReal)] = T_[(ω : ℝ)] := by
  funext x
  ext i
  -- Specialize the unbounded coordinate identity to the constant threshold family.
  simpa [softThreshold_apply] using
    congrArg (fun f : ι → ℝ ↦ f i) (twoSidedSoftThreshold_top (ω := fun _ : ι ↦ ω) (x := x))

end

end

/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_24
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2

-- Declarations for this item will be appended below by the statement pipeline.

open WithLp
open scoped BigOperators

noncomputable section

section

variable {ι : Type*}

local notation "coord" => WithLp.equiv (2 : ENNReal) (ι → ℝ)
local notation "E" => EuclideanSpace ℝ ι

/-
Definition 6.6 is `source-facing` in the separable finite-product penalty domain. Sampling the
nearby chapter owners `Box[ℓ,u]` from Chapter 1, `extendedIndicator` from Chapter 2,
`softThreshold` from Definition 6.3, and `twoSidedSoftThreshold` from Definition 6.5 shows that
the primitive data are:

- a finite index family of nonnegative weights `ω : ι → NNReal`,
- a finite index family of extended nonnegative box half-widths `α : ι → ENNReal`.

The source-facing owners therefore remain the weighted box-constrained set and its penalty on the
canonical finite Euclidean product `EuclideanSpace ℝ ι`, while the supporting box data should be
reused from the Chapter 1 owner `Box[ℓ,u]` through the canonical coordinate equivalence
`WithLp.equiv`.
-/

private theorem mem_symmetricInterval_iff
    (a : ENNReal) (t : ℝ) :
    (-((a : EReal)) ≤ (t : EReal) ∧ (t : EReal) ≤ (a : EReal)) ↔ ENNReal.ofReal |t| ≤ a := by
  by_cases ha : a = ⊤
  · simp [ha]
  · lift a to NNReal using ha with a
    have hleft : (-((a : NNReal) : EReal) ≤ (t : EReal)) ↔ (-(a : ℝ) ≤ t) := by
      change (((-(a : ℝ)) : EReal) ≤ (t : EReal)) ↔ (-(a : ℝ) ≤ t)
      exact EReal.coe_le_coe_iff
    have hright : ((t : EReal) ≤ ((a : NNReal) : EReal)) ↔ t ≤ (a : ℝ) := by
      change ((t : EReal) ≤ ((a : ℝ) : EReal)) ↔ t ≤ (a : ℝ)
      exact EReal.coe_le_coe_iff
    simp [hleft, hright, abs_le]

private theorem mem_symmetricBox_iff (α : ι → ENNReal) (x : E) :
    x ∈
        (coord ⁻¹'
          Box[fun i ↦ -((α i : EReal)), fun i ↦ (α i : EReal)] : Set E) ↔
      ∀ i, ENNReal.ofReal |x i| ≤ α i := by
  change
    (∀ i, -((α i : EReal)) ≤ (x i : EReal) ∧ (x i : EReal) ≤ (α i : EReal)) ↔
      ∀ i, ENNReal.ofReal |x i| ≤ α i
  constructor
  · intro hx i
    exact (mem_symmetricInterval_iff (α i) (x i)).1 (hx i)
  · intro hx i
    exact (mem_symmetricInterval_iff (α i) (x i)).2 (hx i)

/-- Helper for Definition 6.6: the scalar box `ENNReal.ofReal |t| ≤ a` is closed. -/
private theorem isClosed_scalar_abs_le_ennreal
    (a : ENNReal) :
    IsClosed {t : ℝ | ENNReal.ofReal |t| ≤ a} := by
  -- The scalar box is the preimage of the closed lower interval `(-∞, a]`.
  simpa using
    (isClosed_Iic.preimage
      (ENNReal.continuous_ofReal.comp
        (continuous_norm : Continuous fun t : ℝ => ‖t‖)))

/-- Helper for Definition 6.6: the scalar box `ENNReal.ofReal |t| ≤ a` is convex. -/
private theorem convex_scalar_abs_le_ennreal
    (a : ENNReal) :
    Convex ℝ {t : ℝ | ENNReal.ofReal |t| ≤ a} := by
  by_cases ha : a = ⊤
  · -- At `a = ∞`, the scalar constraint is vacuous.
    simpa [ha] using (convex_univ : Convex ℝ (Set.univ : Set ℝ))
  · -- For finite `a`, the scalar box is the interval `[-a, a]`.
    lift a to NNReal using ha with a
    simpa [abs_le] using
      (convex_Icc (-(a : ℝ)) (a : ℝ) :
        Convex ℝ (Set.Icc (-(a : ℝ)) (a : ℝ)))

/-- Helper for Definition 6.6: the coordinatewise symmetric box is closed. -/
private theorem isClosed_symmetric_abs_box
    (α : ι → ENNReal) :
    IsClosed {x : E | ∀ i, ENNReal.ofReal |x i| ≤ α i} := by
  -- Each coordinate slice is closed by continuity of the evaluation map.
  have hcoord : ∀ i, IsClosed {x : E | ENNReal.ofReal |x i| ≤ α i} := by
    intro i
    simpa using
      (isClosed_scalar_abs_le_ennreal (α i)).preimage
        (PiLp.continuous_apply (2 : ENNReal) (fun _ ↦ ℝ) i)
  -- The full box is the intersection of the coordinate slices.
  simpa [Set.setOf_forall] using (isClosed_iInter hcoord)

/-- Helper for Definition 6.6: the coordinatewise symmetric box is convex. -/
private theorem convex_symmetric_abs_box
    (α : ι → ENNReal) :
    Convex ℝ {x : E | ∀ i, ENNReal.ofReal |x i| ≤ α i} := by
  -- Convexity is checked coordinatewise using the scalar box lemma.
  intro x hx y hy a b ha hb hab i
  exact (convex_scalar_abs_le_ennreal (α i)) (hx i) (hy i) ha hb hab

variable [Fintype ι]

/-- Helper for Definition 6.6: the weighted `ℓ¹` sublevel set is closed. -/
private theorem isClosed_weighted_l1_sublevel
    (ω : ι → NNReal) (β : ℝ) :
    IsClosed {x : E | (∑ i, (ω i : ℝ) * |x i|) ≤ β} := by
  let f : E → ℝ := fun x ↦ ∑ i, (ω i : ℝ) * |x i|
  -- The weighted absolute-value sum is continuous term by term.
  have hf : Continuous f := by
    unfold f
    refine continuous_finset_sum Finset.univ ?_
    intro i hi
    simpa [Real.norm_eq_abs] using
      ((PiLp.continuous_apply (2 : ENNReal) (fun _ ↦ ℝ) i).norm.const_mul
        (ω i : ℝ))
  -- Closedness follows from taking a closed sublevel set of a continuous map.
  simpa [f] using (isClosed_Iic.preimage hf)

/-- Helper for Definition 6.6: the weighted `ℓ¹` sublevel set is convex. -/
private theorem convex_weighted_l1_sublevel
    (ω : ι → NNReal) (β : ℝ) :
    Convex ℝ {x : E | (∑ i, (ω i : ℝ) * |x i|) ≤ β} := by
  intro x hx y hy a b ha hb hab
  change (∑ i, (ω i : ℝ) * |(a • x + b • y) i|) ≤ β
  have hxβ : (∑ i, (ω i : ℝ) * |x i|) ≤ β := by
    simpa using hx
  have hyβ : (∑ i, (ω i : ℝ) * |y i|) ≤ β := by
    simpa using hy
  -- Bound each coordinate of the convex combination by the triangle inequality.
  have hterm :
      ∀ i,
        (ω i : ℝ) * |(a • x + b • y) i| ≤
          (ω i : ℝ) * (a * |x i| + b * |y i|) := by
    intro i
    have habs :
        |(a • x + b • y) i| ≤ a * |x i| + b * |y i| := by
      calc
        |(a • x + b • y) i| = |a * x i + b * y i| := by
          simp [smul_eq_mul]
        _ ≤ |a * x i| + |b * y i| := by
          simpa [Real.norm_eq_abs] using norm_add_le (a * x i) (b * y i)
        _ = a * |x i| + b * |y i| := by
          rw [abs_mul, abs_of_nonneg ha, abs_mul, abs_of_nonneg hb]
    have hω : 0 ≤ (ω i : ℝ) := by
      exact_mod_cast (ω i).2
    exact mul_le_mul_of_nonneg_left habs hω
  have hsum :
      (∑ i, (ω i : ℝ) * |(a • x + b • y) i|) ≤
        ∑ i, (ω i : ℝ) * (a * |x i| + b * |y i|) := by
    exact Finset.sum_le_sum fun i hi ↦ hterm i
  -- Rearrange the bound into the convex combination of the endpoint sums.
  calc
    (∑ i, (ω i : ℝ) * |(a • x + b • y) i|) ≤
        ∑ i, (ω i : ℝ) * (a * |x i| + b * |y i|) := hsum
    _ = a * ∑ i, (ω i : ℝ) * |x i| + b * ∑ i, (ω i : ℝ) * |y i| := by
      calc
        (∑ i, (ω i : ℝ) * (a * |x i| + b * |y i|)) =
            ∑ i, (a * ((ω i : ℝ) * |x i|) + b * ((ω i : ℝ) * |y i|)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
        _ = a * ∑ i, (ω i : ℝ) * |x i| + b * ∑ i, (ω i : ℝ) * |y i| := by
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_add_distrib]
    _ ≤ a * β + b * β := by
      gcongr
    _ = (a + b) * β := by
      ring
    _ = β := by
      rw [hab, one_mul]

/-- Definition 6.6: the weighted `ℓ¹` box-constrained level set consists of the families
`x : EuclideanSpace ℝ ι` such that `∑ i, ω_i |x_i| ≤ β` and `|x_i| ≤ α_i` coordinatewise,
equivalently `-α ≤ x ≤ α`; specializing to `ι = Fin n` recovers the textbook subset of `ℝ^n`. -/
def weighted_l1_box_constraint_set
    (ω : ι → NNReal) (α : ι → ENNReal) (β : ℝ) : Set E :=
  {x |
    (∑ i, (ω i : ℝ) * |x i|) ≤ β ∧
      x ∈
        (coord ⁻¹' Box[fun i ↦ -((α i : EReal)), fun i ↦ (α i : EReal)] : Set E)}

/-- A point lies in the weighted `ℓ¹` box-constrained set exactly when its weighted `ℓ¹` value is
at most `β` and every coordinate satisfies `|x i| ≤ α i`, with `α i = ∞` allowed. -/
theorem mem_weighted_l1_box_constraint_set_iff
    (ω : ι → NNReal) (α : ι → ENNReal) (β : ℝ) (x : E) :
    x ∈ weighted_l1_box_constraint_set ω α β ↔
      (∑ i, (ω i : ℝ) * |x i|) ≤ β ∧ ∀ i, ENNReal.ofReal |x i| ≤ α i := by
  constructor
  · rintro ⟨hβ, hx⟩
    exact ⟨hβ, (mem_symmetricBox_iff α x).1 hx⟩
  · rintro ⟨hβ, hx⟩
    exact ⟨hβ, (mem_symmetricBox_iff α x).2 hx⟩

-- Proof sketch: the zero vector has weighted `ℓ¹` value `0`, so `0 ≤ β` implies the sublevel
-- inequality, and the coordinate box constraints hold trivially because `|0| = 0`.
/-- The weighted `ℓ¹` box-constrained set is nonempty whenever `β ≥ 0`. -/
theorem weighted_l1_box_constraint_set_nonempty_of_nonneg
    (ω : ι → NNReal) (α : ι → ENNReal) (β : ℝ) (hβ : 0 ≤ β) :
    (weighted_l1_box_constraint_set ω α β).Nonempty := by
  -- Use the zero vector, whose weighted `ℓ¹` value is zero and which satisfies the box bounds.
  refine ⟨0, ?_⟩
  rw [mem_weighted_l1_box_constraint_set_iff]
  constructor
  · simpa using hβ
  · intro i
    simp

-- Proof sketch: the weighted `ℓ¹` inequality is a closed sublevel condition for a continuous
-- finite sum of absolute values, and the coordinate box constraints are closed; their
-- intersection is therefore closed.
/-- The weighted `ℓ¹` box-constrained set is closed. -/
theorem weighted_l1_box_constraint_set_isClosed
    (ω : ι → NNReal) (α : ι → ENNReal) (β : ℝ) :
    IsClosed (weighted_l1_box_constraint_set ω α β) := by
  have hset :
      weighted_l1_box_constraint_set ω α β =
        {x : E | (∑ i, (ω i : ℝ) * |x i|) ≤ β} ∩
          {x : E | ∀ i, ENNReal.ofReal |x i| ≤ α i} := by
    -- Rewrite the set as the intersection of the weighted sublevel and the box.
    ext x
    simp [mem_weighted_l1_box_constraint_set_iff]
  -- Closedness follows from the two closed factors.
  rw [hset]
  exact
    (isClosed_weighted_l1_sublevel ω β).inter
      (isClosed_symmetric_abs_box α)

-- Proof sketch: the weighted `ℓ¹` sublevel set is convex, the symmetric coordinate box is convex,
-- and `weighted_l1_box_constraint_set ω α β` is their intersection.
/-- The weighted `ℓ¹` box-constrained set is convex. -/
theorem weighted_l1_box_constraint_set_convex
    (ω : ι → NNReal) (α : ι → ENNReal) (β : ℝ) :
    Convex ℝ (weighted_l1_box_constraint_set ω α β) := by
  have hset :
      weighted_l1_box_constraint_set ω α β =
        {x : E | (∑ i, (ω i : ℝ) * |x i|) ≤ β} ∩
          {x : E | ∀ i, ENNReal.ofReal |x i| ≤ α i} := by
    -- Rewrite the set as the intersection of the weighted sublevel and the box.
    ext x
    simp [mem_weighted_l1_box_constraint_set_iff]
  -- Convexity follows from the two convex factors.
  rw [hset]
  exact
    (convex_weighted_l1_sublevel ω β).inter
      (convex_symmetric_abs_box α)

/-- The extended-real-valued penalty
`x ↦ ωᵀ|x| + δ_{Box(-α, α)}(x)` attached to the weighted box constraint. -/
def weighted_l1_box_penalty
    (ω : ι → NNReal) (α : ι → ENNReal) : E → EReal :=
  fun x ↦
    ((∑ i, (ω i : ℝ) * |x i| : ℝ) : EReal) +
      extendedIndicator
        ((coord ⁻¹' Box[fun i ↦ -((α i : EReal)), fun i ↦ (α i : EReal)] : Set E)) x

-- Proof sketch: unfold `weighted_l1_box_penalty`; the value is by definition the finite weighted
-- absolute-value sum, viewed in `EReal`, plus the indicator of the symmetric box.
/-- Evaluating `weighted_l1_box_penalty` gives the weighted absolute-value sum plus the indicator
of the symmetric box. -/
theorem weighted_l1_box_penalty_apply
    (ω : ι → NNReal) (α : ι → ENNReal) (x : E) :
    weighted_l1_box_penalty ω α x =
      ((∑ i, (ω i : ℝ) * |x i| : ℝ) : EReal) +
        extendedIndicator {y : E | ∀ i, ENNReal.ofReal |y i| ≤ α i} x := by
  have hbox :
      (coord ⁻¹' Box[fun i ↦ -((α i : EReal)), fun i ↦ (α i : EReal)] : Set E) =
        {y : E | ∀ i, ENNReal.ofReal |y i| ≤ α i} := by
    ext y
    exact mem_symmetricBox_iff α y
  simp [weighted_l1_box_penalty, hbox]

-- Proof sketch: extensionality on `x`; unfold `weighted_l1_box_constraint_set`,
-- `weighted_l1_box_penalty`, `symmetricBox`, and `extendedIndicator`. On the box, the indicator
-- term is `0`, so the sublevel condition reduces to `∑ i, ω_i |x_i| ≤ β`; outside the box, the
-- indicator term is `⊤`, so the sublevel condition fails.
/-- The weighted box-constrained set is the `β`-sublevel set of the penalty
`x ↦ ωᵀ|x| + δ_{Box(-α, α)}(x)`. -/
theorem weighted_l1_box_constraint_set_eq_sublevel_weighted_l1_box_penalty
    (ω : ι → NNReal) (α : ι → ENNReal) (β : ℝ) :
    weighted_l1_box_constraint_set ω α β =
      (weighted_l1_box_penalty ω α) ⁻¹' Set.Iic (β : EReal) := by
  have hbox :
      (coord ⁻¹' Box[fun i ↦ -((α i : EReal)), fun i ↦ (α i : EReal)] : Set E) =
        {y : E | ∀ i, ENNReal.ofReal |y i| ≤ α i} := by
    ext y
    exact mem_symmetricBox_iff α y
  ext x
  by_cases hx : ∀ i, ENNReal.ofReal |x i| ≤ α i
  · simp [weighted_l1_box_constraint_set, weighted_l1_box_penalty, extendedIndicator, hbox, hx,
      EReal.coe_le_coe_iff]
  · simp [weighted_l1_box_constraint_set, weighted_l1_box_penalty, extendedIndicator, hbox, hx,
      EReal.add_top_of_ne_bot, EReal.coe_ne_bot]

end

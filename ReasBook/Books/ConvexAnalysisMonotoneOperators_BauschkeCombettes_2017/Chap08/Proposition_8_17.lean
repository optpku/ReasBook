/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Text_8_0_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u}

/-- The canonical positive-real parameter type `ℝ_{++}` used for scalar actions on
`]-∞,+∞]`-valued functions. -/
abbrev PosReal := {x : ℝ // 0 < x}

/-- The multiplicative unit of `ℝ_{++}`. -/
instance : One PosReal := ⟨⟨1, by positivity⟩⟩

/-- Positive reals are closed under multiplication. -/
instance : Mul PosReal := ⟨fun a b ↦ ⟨(a : ℝ) * (b : ℝ), mul_pos a.2 b.2⟩⟩

@[simp] theorem posReal_coe_one : ((1 : PosReal) : ℝ) = 1 := rfl

@[simp] theorem posReal_coe_mul (a b : PosReal) : ((a * b : PosReal) : ℝ) = (a : ℝ) * (b : ℝ) :=
  rfl

instance : Monoid PosReal where
  mul_assoc a b c := by
    apply Subtype.ext
    simp [mul_assoc]
  one_mul a := by
    apply Subtype.ext
    simp
  mul_one a := by
    apply Subtype.ext
    simp

/-- The pointwise sum of two `]-∞,+∞]`-valued functions. -/
noncomputable def pointwiseAdd (f g : H → Set.Ioi (⊥ : EReal)) : H → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    ⟨(f x : EReal) + (g x : EReal),
      EReal.bot_lt_add_iff.2 ⟨(f x).property, (g x).property⟩⟩

/-- Coercing the pointwise sum back to `EReal` recovers ordinary pointwise addition. -/
-- Proof sketch: unfold `pointwiseAdd`; the subtype coercion forgets only the proof that the sum
-- stays in `]-∞,+∞]`.
@[simp] theorem pointwiseAdd_apply (f g : H → Set.Ioi (⊥ : EReal)) (x : H) :
    (pointwiseAdd f g x : EReal) = (f x : EReal) + (g x : EReal) := by
  -- Unfold the subtype-valued definition to expose ordinary extended-real addition.
  rfl

/-- Positive reals act on `]-∞,+∞]` by multiplication. -/
noncomputable instance : SMul PosReal (Set.Ioi (⊥ : EReal)) where
  smul a x := ⟨(a : EReal) * (x : EReal), adjoint_mul_mem_Ioi_bot (a : ℝ) a.2 x⟩

/-- Coercing the positive-real action on `]-∞,+∞]` back to `EReal` recovers ordinary
multiplication by the positive scalar. -/
@[simp] theorem posReal_smul_value_apply (a : PosReal) (x : Set.Ioi (⊥ : EReal)) :
    ((a • x : Set.Ioi (⊥ : EReal)) : EReal) = (a : EReal) * (x : EReal) :=
  rfl

/-- Positive-real scaling defines a multiplicative action on `]-∞,+∞]`. -/
noncomputable instance : MulAction PosReal (Set.Ioi (⊥ : EReal)) where
  one_smul x := by
    apply Subtype.ext
    simp [posReal_smul_value_apply]
  mul_smul a b x := by
    apply Subtype.ext
    simp [mul_assoc, posReal_smul_value_apply]

/-- Coercing the pointwise positive scaling `a • f` back to `EReal` recovers ordinary pointwise
multiplication by `a`. -/
@[simp] theorem posReal_smul_apply (a : PosReal) (f : H → Set.Ioi (⊥ : EReal)) (x : H) :
    ((a • f) x : EReal) = (a : EReal) * (f x : EReal) := by
  simp [Pi.smul_apply, posReal_smul_value_apply]

/-- Helper for Proposition 8.17: the pointwise sum is finite above exactly where both summands are
finite above. -/
private theorem mem_dom_pointwiseAdd_iff (f g : H → Set.Ioi (⊥ : EReal)) (x : H) :
    x ∈ dom (fun y : H ↦ (pointwiseAdd f g y : EReal)) ↔
      x ∈ dom (fun y : H ↦ (f y : EReal)) ∧ x ∈ dom (fun y : H ↦ (g y : EReal)) := by
  -- Rewrite domain membership to non-`⊤` statements and use the extended-real sum criterion.
  rw [mem_dom_iff, mem_dom_iff, mem_dom_iff, pointwiseAdd_apply, lt_top_iff_ne_top,
    lt_top_iff_ne_top, lt_top_iff_ne_top]
  exact EReal.add_ne_top_iff_ne_top₂ (ne_of_gt (f x).property) (ne_of_gt (g x).property)

/-- Helper for Proposition 8.17: multiplying by a strictly positive real preserves the effective
domain. -/
private theorem mem_dom_smul_iff (a : PosReal)
    (f : H → Set.Ioi (⊥ : EReal)) (x : H) :
    x ∈ dom (fun y : H ↦ ((a • f) y : EReal)) ↔
      x ∈ dom (fun y : H ↦ (f y : EReal)) := by
  rw [mem_dom_iff, mem_dom_iff, posReal_smul_apply, lt_top_iff_ne_top, lt_top_iff_ne_top]
  constructor
  · intro hmul htop
    -- If the original value were `⊤`, positive scaling would stay `⊤`, contradicting finiteness.
    exact hmul (by simpa [htop] using EReal.coe_mul_top_of_pos a.2)
  · intro hf
    -- Positive scaling cannot create `⊤` from a value already below `⊤`.
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot (a : ℝ)), Or.inl (EReal.coe_nonneg.mpr a.2.le),
      Or.inl (EReal.coe_ne_top (a : ℝ)), Or.inr hf⟩

section RealVectorSpace

variable [AddCommGroup H] [Module ℝ H]

-- Proof sketch: use Proposition 8.4 to rewrite convexity as Jensen inequalities on effective
-- domains. For points where both `f` and `g` are finite, apply the Jensen inequalities for `f` and
-- `g` separately and add the resulting `EReal` inequalities.
/-- Proposition 8.17 (1): the pointwise sum of two convex `]-∞,+∞]`-valued functions, defined
using the usual extended-real addition convention, is convex. -/
theorem convex_epigraph_pointwiseAdd
    {f g : H → Set.Ioi (⊥ : EReal)}
    (hf : Convex ℝ (epigraph fun x : H ↦ (f x : EReal)))
    (hg : Convex ℝ (epigraph fun x : H ↦ (g x : EReal))) :
    Convex ℝ (epigraph fun x : H ↦ (pointwiseAdd f g x : EReal)) := by
  refine (convex_epigraph_iff_jensen_on_dom _).2 ?_
  intro x y hx hy α hα hα_lt_one
  have hxfg := (mem_dom_pointwiseAdd_iff f g x).1 hx
  have hyfg := (mem_dom_pointwiseAdd_iff f g y).1 hy
  have hα_nonneg : (0 : EReal) ≤ (α : EReal) := EReal.coe_nonneg.mpr hα.le
  have hβ_nonneg : (0 : EReal) ≤ (((1 - α : ℝ) : EReal)) :=
    EReal.coe_nonneg.mpr (sub_nonneg.mpr hα_lt_one.le)
  have hα_ne_top : (α : EReal) ≠ ⊤ := EReal.coe_ne_top α
  have hβ_ne_top : (((1 - α : ℝ) : EReal)) ≠ ⊤ := EReal.coe_ne_top (1 - α)
  have hfJ :=
    (convex_epigraph_iff_jensen_on_dom (fun z : H ↦ (f z : EReal))).1 hf
      hxfg.1 hyfg.1 hα hα_lt_one
  have hgJ :=
    (convex_epigraph_iff_jensen_on_dom (fun z : H ↦ (g z : EReal))).1 hg
      hxfg.2 hyfg.2 hα hα_lt_one
  -- Add the two Jensen bounds and regroup coefficients to recover the sum-function inequality.
  calc
    (pointwiseAdd f g (α • x + (1 - α) • y) : EReal)
        = (f (α • x + (1 - α) • y) : EReal) + (g (α • x + (1 - α) • y) : EReal) := by
            rw [pointwiseAdd_apply]
    _ ≤ (α : EReal) * (f x : EReal) + (((1 - α : ℝ) : EReal) * (f y : EReal)) +
          ((α : EReal) * (g x : EReal) + (((1 - α : ℝ) : EReal) * (g y : EReal))) := by
            exact add_le_add hfJ hgJ
    _ = (α : EReal) * ((f x : EReal) + (g x : EReal)) +
          (((1 - α : ℝ) : EReal) * ((f y : EReal) + (g y : EReal))) := by
            rw [EReal.left_distrib_of_nonneg_of_ne_top hα_nonneg hα_ne_top,
              EReal.left_distrib_of_nonneg_of_ne_top hβ_nonneg hβ_ne_top]
            simp [add_assoc, add_left_comm]
    _ = (α : EReal) * (pointwiseAdd f g x : EReal) +
          (((1 - α : ℝ) : EReal) * (pointwiseAdd f g y : EReal)) := by
            rw [pointwiseAdd_apply, pointwiseAdd_apply]

-- Proof sketch: use Proposition 8.4 to pass to the Jensen inequality on the effective domain, then
-- multiply that inequality by the positive scalar `a`. Proposition 8.4 converts the resulting
-- Jensen inequality back to convexity of the epigraph.
/-- Proposition 8.17 (2): every positive pointwise scalar multiple of a convex
`]-∞,+∞]`-valued function is convex. -/
theorem convex_epigraph_smul
    {f : H → Set.Ioi (⊥ : EReal)}
    (hf : Convex ℝ (epigraph fun x : H ↦ (f x : EReal)))
    (a : PosReal) :
    Convex ℝ (epigraph fun x : H ↦ ((a • f) x : EReal)) := by
  refine (convex_epigraph_iff_jensen_on_dom _).2 ?_
  intro x y hx hy α hα hα_lt_one
  have hx' := (mem_dom_smul_iff a f x).1 hx
  have hy' := (mem_dom_smul_iff a f y).1 hy
  have ha_nonneg : (0 : EReal) ≤ (a : EReal) := EReal.coe_nonneg.mpr a.2.le
  have ha_ne_top : (a : EReal) ≠ ⊤ := EReal.coe_ne_top (a : ℝ)
  have hJ :=
    (convex_epigraph_iff_jensen_on_dom (fun z : H ↦ (f z : EReal))).1 hf
      hx' hy' hα hα_lt_one
  have hscaled :
      (a : EReal) * (f (α • x + (1 - α) • y) : EReal) ≤
        (a : EReal) *
          ((α : EReal) * (f x : EReal) + (((1 - α : ℝ) : EReal) * (f y : EReal))) :=
    mul_le_mul_of_nonneg_left hJ ha_nonneg
  -- Multiply the Jensen inequality by the positive scalar and distribute it across the rhs.
  calc
    ((a • f) (α • x + (1 - α) • y) : EReal)
        = (a : EReal) * (f (α • x + (1 - α) • y) : EReal) := by
            rw [posReal_smul_apply]
    _ ≤ (a : EReal) *
          ((α : EReal) * (f x : EReal) + (((1 - α : ℝ) : EReal) * (f y : EReal))) := hscaled
    _ = (a : EReal) * ((α : EReal) * (f x : EReal)) +
          (a : EReal) * ((((1 - α : ℝ) : EReal) * (f y : EReal))) := by
            rw [EReal.left_distrib_of_nonneg_of_ne_top ha_nonneg ha_ne_top]
    _ = (α : EReal) * ((a • f) x : EReal) +
          (((1 - α : ℝ) : EReal) * ((a • f) y : EReal)) := by
            rw [posReal_smul_apply, posReal_smul_apply]
            simp [mul_assoc, mul_left_comm, mul_comm]

end RealVectorSpace

end ERealFunction

/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_1
import Mathlib.Analysis.Convex.Strong
import Mathlib.Data.EReal.Operations

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Chapter 2 already provides the source-facing helper `effective_domain` recording the finite-
valued domain of an extended-real-valued function, while mathlib's `StrongConvexOn` supplies the
canonical owner abstraction for the real-valued bridge. -/

/-- Source-side predicate for Definition 5.16: an extended-real-valued function is `σ`-strongly
convex if it never takes
the value `-∞` and satisfies the quadratic Jensen inequality on its effective domain for every
weight `t ∈ [0, 1]`; this segment inequality forces the effective domain to be convex. -/
class is_strongly_convex_function (f : E → EReal) (σ : ℝ) : Prop where
  /-- A strongly convex extended-real-valued function never takes the value `-∞`. -/
  ne_bot : ∀ x, f x ≠ ⊥
  /-- The defining quadratic Jensen inequality holds along every segment in the effective domain. -/
  segment_ineq :
    ∀ ⦃x⦄, x ∈ effective_domain f → ∀ ⦃y⦄, y ∈ effective_domain f → ∀ ⦃t : ℝ⦄,
      t ∈ Set.Icc (0 : ℝ) 1 →
        f (t • x + (1 - t) • y) ≤
          (t : EReal) * f x + ((1 - t : ℝ) : EReal) * f y -
            (((σ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal)
  /-- The strong-convexity modulus is strictly positive. -/
  sigma_pos : 0 < σ

-- Proof sketch: use the global `ne_bot` hypothesis to make `(f x).toReal` finite on
-- `effective_domain f`, and use `segment_ineq` to prove segment points stay in
-- `effective_domain f`; this supplies the convexity component required by `StrongConvexOn`.
-- Then translate `segment_ineq` into the defining real-valued strong-convexity inequality. For
-- the converse, extract the set convexity and Jensen inequality from `StrongConvexOn`, coerce them
-- back to `EReal`, and keep the source-side no-`⊥` condition explicit.
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Helper for Definition 5.16: on the effective domain, the weighted extended-real value is the
coercion of the corresponding weighted real combination of `toReal` values. -/
private theorem weightedValue_eq_coe_toRealCombo
    {f : E → EReal} {x y : E} (hx : x ∈ effective_domain f) (hy : y ∈ effective_domain f)
    (h_ne_bot : ∀ z, f z ≠ ⊥) {t : ℝ} :
    (t : EReal) * f x + ((1 - t : ℝ) : EReal) * f y =
      ((t * (f x).toReal + (1 - t) * (f y).toReal : ℝ) : EReal) := by
  have hx_top : f x ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hx)
  have hy_top : f y ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hy)
  -- Replace the finite `EReal` values by their `toReal` coercions, then combine the arithmetic.
  calc
    (t : EReal) * f x + ((1 - t : ℝ) : EReal) * f y =
        (t : EReal) * (((f x).toReal : ℝ) : EReal) +
          ((1 - t : ℝ) : EReal) * (((f y).toReal : ℝ) : EReal) := by
      rw [EReal.coe_toReal hx_top (h_ne_bot x), EReal.coe_toReal hy_top (h_ne_bot y)]
    _ = (((t * (f x).toReal : ℝ) : EReal) +
          (((1 - t) * (f y).toReal : ℝ) : EReal)) := by
      rw [EReal.coe_mul, EReal.coe_mul]
    _ = ((t * (f x).toReal + (1 - t) * (f y).toReal : ℝ) : EReal) := by
      rw [← EReal.coe_add]

omit [NormedSpace ℝ E] in
/-- Helper for Definition 5.16: the strong-convexity right-hand side in `EReal` is the coercion of
the corresponding real-valued expression on the effective domain. -/
private theorem strongConvexSegmentRhs_coe
    {f : E → EReal} {σ : ℝ} {x y : E} (h_ne_bot : ∀ z, f z ≠ ⊥)
    (hx : x ∈ effective_domain f) (hy : y ∈ effective_domain f) {t : ℝ} :
    (t : EReal) * f x + ((1 - t : ℝ) : EReal) * f y -
        (((σ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal) =
      ((t * (f x).toReal + (1 - t) * (f y).toReal -
        ((σ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : ℝ) : EReal) := by
  -- Normalize the weighted values first, then absorb the penalty term into a single real coercion.
  calc
    (t : EReal) * f x + ((1 - t : ℝ) : EReal) * f y -
        (((σ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal) =
      ((t * (f x).toReal + (1 - t) * (f y).toReal : ℝ) : EReal) -
        (((σ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal) := by
      rw [weightedValue_eq_coe_toRealCombo hx hy h_ne_bot]
    _ = ((t * (f x).toReal + (1 - t) * (f y).toReal -
        ((σ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : ℝ) : EReal) := by
      rw [EReal.coe_sub]

/-- Helper for Definition 5.16: the source strong-convexity inequality forces the effective domain
to be convex along segments. -/
private theorem segment_mem_effectiveDomain_of_isStronglyConvex
    {f : E → EReal} {σ : ℝ} (hf : is_strongly_convex_function f σ)
    {x y : E} (hx : x ∈ effective_domain f) (hy : y ∈ effective_domain f)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    t • x + (1 - t) • y ∈ effective_domain f := by
  have hseg :
      f (t • x + (1 - t) • y) ≤
        (t : EReal) * f x + ((1 - t : ℝ) : EReal) * f y -
          (((σ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal) :=
    hf.segment_ineq hx hy ht
  have hweighted_top :
      (t : EReal) * f x + ((1 - t : ℝ) : EReal) * f y -
        (((σ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal) < ⊤ := by
    rw [strongConvexSegmentRhs_coe (f := f) (σ := σ) hf.ne_bot hx hy]
    exact EReal.coe_lt_top _
  -- The right-hand side is finite, so the segment value is finite as well.
  exact mem_effective_domain.mpr (lt_of_le_of_lt hseg hweighted_top)

/-- Helper for Definition 5.16: projecting the source `EReal` segment inequality to `ℝ` yields the
real strong-convexity inequality on the effective domain. -/
private theorem toReal_segmentIneq_of_isStronglyConvex
    {f : E → EReal} {σ : ℝ} (hf : is_strongly_convex_function f σ)
    {x y : E} (hx : x ∈ effective_domain f) (hy : y ∈ effective_domain f)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (f (t • x + (1 - t) • y)).toReal ≤
      t * (f x).toReal + (1 - t) * (f y).toReal -
        ((σ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) : ℝ) := by
  have hseg :
      f (t • x + (1 - t) • y) ≤
        (t : EReal) * f x + ((1 - t : ℝ) : EReal) * f y -
          (((σ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal) :=
    hf.segment_ineq hx hy ht
  have hweighted_ne_top :
      (t : EReal) * f x + ((1 - t : ℝ) : EReal) * f y -
        (((σ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal) ≠ ⊤ := by
    rw [strongConvexSegmentRhs_coe (f := f) (σ := σ) hf.ne_bot hx hy]
    exact (EReal.coe_lt_top _).ne
  have hweighted_toReal :
      ((t : EReal) * f x + ((1 - t : ℝ) : EReal) * f y -
          (((σ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal)).toReal =
        t * (f x).toReal + (1 - t) * (f y).toReal -
          ((σ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) : ℝ) := by
    simpa using congrArg EReal.toReal
      (strongConvexSegmentRhs_coe (f := f) (σ := σ) hf.ne_bot hx hy (t := t))
  -- Convert the finite `EReal` inequality to the real-valued strong-convexity inequality.
  have htoReal :=
    EReal.toReal_le_toReal hseg (hf.ne_bot _) hweighted_ne_top
  rw [hweighted_toReal] at htoReal
  simpa [mul_assoc, mul_left_comm, mul_comm] using htoReal

/-- Helper for Definition 5.16: a real-valued `StrongConvexOn` hypothesis on the effective domain
reconstructs the source extended-real segment inequality. -/
private theorem segmentIneq_of_strongConvexOn_toReal
    {f : E → EReal} {σ : ℝ}
    (h_ne_bot : ∀ z, f z ≠ ⊥)
    (hsc : StrongConvexOn (effective_domain f) σ (fun z ↦ (f z).toReal))
    {x y : E} (hx : x ∈ effective_domain f) (hy : y ∈ effective_domain f)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    f (t • x + (1 - t) • y) ≤
      (t : EReal) * f x + ((1 - t : ℝ) : EReal) * f y -
        (((σ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  change
    UniformConvexOn (effective_domain f) (fun r ↦ σ / (2 : ℝ) * r ^ 2)
      (fun z ↦ (f z).toReal) at hsc
  have hsum : t + (1 - t) = 1 := by
    linarith
  have hz : t • x + (1 - t) • y ∈ effective_domain f :=
    hsc.1 hx hy ht.1 (sub_nonneg.mpr ht.2) hsum
  have htoReal :
      (f (t • x + (1 - t) • y)).toReal ≤
        t * (f x).toReal + (1 - t) * (f y).toReal -
          ((σ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) : ℝ) := by
    -- Rewrite the owner inequality into the source segment form with the same coefficient `t`.
    simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
      hsc.2 hx hy ht.1 (sub_nonneg.mpr ht.2) hsum
  -- Convert the real-valued segment inequality back into the original `EReal` inequality.
  calc
    f (t • x + (1 - t) • y) =
        (((f (t • x + (1 - t) • y)).toReal : ℝ) : EReal) := by
      symm
      exact EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp hz))
        (h_ne_bot _)
    _ ≤ ((t * (f x).toReal + (1 - t) * (f y).toReal -
        ((σ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : ℝ) : EReal) :=
      EReal.coe_le_coe htoReal
    _ = (t : EReal) * f x + ((1 - t : ℝ) : EReal) * f y -
        (((σ / 2) * t * (1 - t) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal) := by
      symm
      exact strongConvexSegmentRhs_coe (f := f) (σ := σ) h_ne_bot hx hy

/-- Definition 5.16: the source strong-convexity predicate is equivalent to strong convexity of the
real-valued
restriction `x ↦ (f x).toReal` on the effective domain, together with the ambient no-`-∞`
condition. -/
theorem is_strongly_convex_function_iff_strongConvexOn_toReal
    {f : E → EReal} {σ : ℝ} :
    is_strongly_convex_function f σ ↔
      0 < σ ∧
        (∀ x, f x ≠ ⊥) ∧
        StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal) := by
  constructor
  · intro hf
    refine ⟨hf.sigma_pos, hf.ne_bot, ?_⟩
    change
      UniformConvexOn (effective_domain f) (fun r ↦ σ / (2 : ℝ) * r ^ 2)
        (fun x ↦ (f x).toReal)
    refine ⟨?_, ?_⟩
    · intro x hx y hy a b ha hb hab
      have hab' : 1 - a = b := by
        linarith
      have ht : a ∈ Set.Icc (0 : ℝ) 1 := by
        refine ⟨ha, ?_⟩
        linarith
      -- The source segment inequality already forces the effective domain to be convex.
      simpa [hab'] using
        segment_mem_effectiveDomain_of_isStronglyConvex (hf := hf) hx hy ht
    · intro x hx y hy a b ha hb hab
      have hab' : 1 - a = b := by
        linarith
      have ht : a ∈ Set.Icc (0 : ℝ) 1 := by
        refine ⟨ha, ?_⟩
        linarith
      -- Reuse the projected segment inequality with `t = a` and rewrite `b` as `1 - a`.
      simpa [smul_eq_mul, hab', mul_assoc, mul_left_comm, mul_comm] using
        toReal_segmentIneq_of_isStronglyConvex (hf := hf) hx hy ht
  · rintro ⟨hσ, h_ne_bot, hsc⟩
    refine ⟨?_, ?_, ?_⟩
    · exact h_ne_bot
    · intro x hx y hy t ht
      -- Route correction: recover the source inequality directly from the real-valued
      -- `StrongConvexOn` owner instead of unfolding larger constructions in place.
      exact segmentIneq_of_strongConvexOn_toReal h_ne_bot hsc hx hy ht
    · exact hσ

/-- The source-facing strong-convexity class exposes the canonical `StrongConvexOn` owner
abstraction on the real-valued restriction to the effective domain. -/
theorem strongConvexOn_toReal_of_is_strongly_convex_function
    {f : E → EReal} {σ : ℝ} (hf : is_strongly_convex_function f σ) :
    StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal) :=
  (is_strongly_convex_function_iff_strongConvexOn_toReal.mp hf).2.2

/-- A strongly convex extended-real-valued function has convex effective domain. -/
theorem is_strongly_convex_function.convex_effective_domain
    {f : E → EReal} {σ : ℝ} (hf : is_strongly_convex_function f σ) :
    Convex ℝ (effective_domain f) :=
  (strongConvexOn_toReal_of_is_strongly_convex_function hf).1

end

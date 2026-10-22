/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The Jensen gap of an `]-∞,+∞]`-valued function at the convex combination with weight `α`. -/
noncomputable def jensenGap (f : H → Set.Ioi (⊥ : EReal)) (α : ℝ) (x y : H) : EReal :=
  (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) -
    (f (α • x + (1 - α) • y) : EReal)

/-- A function is uniformly convex on a nonempty subset `C` of its effective domain with modulus
`φ` when `φ` is increasing, vanishes only at `0`, and the uniform Jensen inequality holds for all
points of `C`. -/
def UniformlyConvexOn
    (f : H → Set.Ioi (⊥ : EReal)) (C : Set H) (φ : NNReal → EReal) : Prop :=
  C.Nonempty ∧
    C ⊆ effectiveDomain f ∧
    Monotone φ ∧
    (∀ r : NNReal, φ r = 0 ↔ r = 0) ∧
    ∀ ⦃x : H⦄, x ∈ C → ∀ ⦃y : H⦄, y ∈ C → ∀ ⦃α : ℝ⦄, 0 < α → α < 1 →
      ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ ≤ jensenGap f α x y

/-- Definition 10.7: a proper `]-∞,+∞]`-valued function is uniformly convex with modulus `φ` when
`φ` is increasing, vanishes only at `0`, and the uniform Jensen inequality holds on the effective
domain of `f`. -/
def UniformlyConvex (f : H → Set.Ioi (⊥ : EReal)) (φ : NNReal → EReal) : Prop :=
  UniformlyConvexOn f (effectiveDomain f) φ

/-- The quadratic modulus attached to strong convexity with constant `β`. -/
noncomputable def strongConvexityModulus (β : ℝ) : NNReal → EReal :=
  fun r ↦ (((β / 2 : ℝ) * (r : ℝ) ^ 2 : ℝ) : EReal)

/-- Definition 10.7: a proper `]-∞,+∞]`-valued function is strongly convex with constant `β` when
its effective domain is nonempty, `β > 0`, and the quadratic Jensen inequality holds on the
effective domain. -/
def StronglyConvex (f : H → Set.Ioi (⊥ : EReal)) (β : ℝ) : Prop :=
  (effectiveDomain f).Nonempty ∧
    0 < β ∧
      ∀ ⦃x : H⦄, x ∈ effectiveDomain f → ∀ ⦃y : H⦄, y ∈ effectiveDomain f →
        ∀ ⦃α : ℝ⦄, 0 < α → α < 1 →
          ((α * (1 - α) : ℝ) : EReal) * strongConvexityModulus β ‖x - y‖₊ ≤
            jensenGap f α x y

omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
private theorem modulus_nonneg {φ : NNReal → EReal} (hφ_mono : Monotone φ)
    (hφ_zero : ∀ r : NNReal, φ r = 0 ↔ r = 0) (r : NNReal) :
    0 ≤ φ r := by
  rw [← (hφ_zero 0).2 rfl]
  exact hφ_mono bot_le

omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
private theorem weightedJensenSum_ne_top {f : H → Set.Ioi (⊥ : EReal)} {x y : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) ≠ ⊤ := by
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hfy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hα_nonneg : 0 ≤ (α : EReal) := by exact_mod_cast hα0.le
  have h1α0 : 0 < 1 - α := by linarith
  have h1α_nonneg : 0 ≤ (1 - α : EReal) := by exact_mod_cast h1α0.le
  have hα_mul_ne_top : (α : EReal) * (f x : EReal) ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot α), Or.inl hα_nonneg, Or.inl (EReal.coe_ne_top α),
      Or.inr hfx_top⟩
  have h1α_mul_ne_top : (1 - α : EReal) * (f y : EReal) ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot (1 - α)), Or.inl h1α_nonneg,
      Or.inl (EReal.coe_ne_top (1 - α)), Or.inr hfy_top⟩
  exact EReal.add_ne_top hα_mul_ne_top h1α_mul_ne_top

/-- A uniformly convex-on set is nonempty. -/
-- Proof sketch: unfold `UniformlyConvexOn` and extract the first conjunct.
theorem UniformlyConvexOn.nonempty
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {φ : NNReal → EReal}
    (hf : UniformlyConvexOn f C φ) :
    C.Nonempty :=
  hf.1

/-- A uniformly convex-on set is contained in the effective domain. -/
-- Proof sketch: unfold `UniformlyConvexOn` and extract the domain-inclusion conjunct.
theorem UniformlyConvexOn.subset_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {φ : NNReal → EReal}
    (hf : UniformlyConvexOn f C φ) :
    C ⊆ effectiveDomain f :=
  hf.2.1

/-- A uniformly convex-on modulus is monotone. -/
-- Proof sketch: unfold `UniformlyConvexOn` and extract the monotonicity conjunct.
theorem UniformlyConvexOn.monotone
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {φ : NNReal → EReal}
    (hf : UniformlyConvexOn f C φ) :
    Monotone φ :=
  hf.2.2.1

/-- A uniformly convex-on modulus vanishes exactly at `0`. -/
-- Proof sketch: unfold `UniformlyConvexOn` and extract the vanishing-at-zero conjunct.
theorem UniformlyConvexOn.modulus_eq_zero_iff
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {φ : NNReal → EReal}
    (hf : UniformlyConvexOn f C φ) (r : NNReal) :
    φ r = 0 ↔ r = 0 :=
  hf.2.2.2.1 r

/-- A function uniformly convex on `C` satisfies the defining Jensen-gap lower bound at every two
points of `C`. -/
theorem UniformlyConvexOn.gap_le
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {φ : NNReal → EReal}
    (hf : UniformlyConvexOn f C φ) {x y : H} (hx : x ∈ C) (hy : y ∈ C)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ ≤ jensenGap f α x y :=
  hf.2.2.2.2 hx hy hα0 hα1

/-- A function uniformly convex on `C` satisfies the defining inequality at every two points of
`C`. -/
-- Proof sketch: unfold `UniformlyConvexOn` and apply the final conjunct.
theorem UniformlyConvexOn.ineq
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {φ : NNReal → EReal}
    (hf : UniformlyConvexOn f C φ) {x y : H} (hx : x ∈ C) (hy : y ∈ C)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (f (α • x + (1 - α) • y) : EReal) +
        ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ ≤
      (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) := by
  have hgap :
      ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ ≤
        (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) -
          (f (α • x + (1 - α) • y) : EReal) := by
    simpa [jensenGap] using hf.gap_le hx hy hα0 hα1
  have hcombo_ne_bot : (f (α • x + (1 - α) • y) : EReal) ≠ ⊥ := ne_of_gt (f _).2
  have hsum_ne_top :
      (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) ≠ ⊤ := by
    exact weightedJensenSum_ne_top (hf.subset_effectiveDomain hx) (hf.subset_effectiveDomain hy)
      hα0 hα1
  simpa [jensenGap, add_comm, add_left_comm, add_assoc] using
    (EReal.le_sub_iff_add_le (Or.inl hcombo_ne_bot) (Or.inr hsum_ne_top)).1 hgap

/-- A uniformly convex-on function is convex on the same set. -/
theorem UniformlyConvexOn.convexOn
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {φ : NNReal → EReal}
    (hf : UniformlyConvexOn f C φ) :
    ConvexOn f C := by
  refine ⟨hf.nonempty, hf.subset_effectiveDomain, ?_⟩
  intro x hx y hy α hα0 hα1
  have hφ_nonneg : (0 : EReal) ≤ φ ‖x - y‖₊ :=
    modulus_nonneg (hf.monotone) (hf.modulus_eq_zero_iff) _
  have hα_nonneg : 0 ≤ α * (1 - α) := by
    nlinarith
  have hterm_nonneg : (0 : EReal) ≤ ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ := by
    exact mul_nonneg (by exact_mod_cast hα_nonneg) hφ_nonneg
  calc
    (f (α • x + (1 - α) • y) : EReal)
        ≤ (f (α • x + (1 - α) • y) : EReal) +
            ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ :=
      le_add_of_nonneg_right hterm_nonneg
    _ ≤ (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) :=
      hf.ineq hx hy hα0 hα1

/-- A uniformly convex `]-∞,+∞]`-valued function is proper. -/
-- Proof sketch: the subtype codomain rules out `-∞`, and `UniformlyConvex` is the
-- `effectiveDomain` specialization of `UniformlyConvexOn`.
theorem UniformlyConvex.isProper
    {f : H → Set.Ioi (⊥ : EReal)} {φ : NNReal → EReal} (hf : UniformlyConvex f φ) :
    IsProper (fun x : H ↦ (f x : EReal)) := by
  refine ⟨fun x ↦ ne_of_gt (f x).2, ?_⟩
  simpa [UniformlyConvex, effectiveDomain, dom] using (UniformlyConvexOn.nonempty hf)

/-- A uniformly convex modulus is monotone. -/
-- Proof sketch: `UniformlyConvex` is the `effectiveDomain` specialization of
-- `UniformlyConvexOn`.
theorem UniformlyConvex.monotone
    {f : H → Set.Ioi (⊥ : EReal)} {φ : NNReal → EReal} (hf : UniformlyConvex f φ) :
    Monotone φ := by
  simpa [UniformlyConvex] using (UniformlyConvexOn.monotone hf)

/-- A uniformly convex modulus vanishes exactly at `0`. -/
-- Proof sketch: `UniformlyConvex` is the `effectiveDomain` specialization of
-- `UniformlyConvexOn`.
theorem UniformlyConvex.modulus_eq_zero_iff
    {f : H → Set.Ioi (⊥ : EReal)} {φ : NNReal → EReal} (hf : UniformlyConvex f φ)
    (r : NNReal) :
    φ r = 0 ↔ r = 0 := by
  simpa [UniformlyConvex] using (UniformlyConvexOn.modulus_eq_zero_iff hf r)

/-- A uniformly convex function satisfies the defining Jensen-gap lower bound on the effective
domain. -/
theorem UniformlyConvex.gap_le
    {f : H → Set.Ioi (⊥ : EReal)} {φ : NNReal → EReal} (hf : UniformlyConvex f φ)
    {x y : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ ≤ jensenGap f α x y := by
  simpa [UniformlyConvex] using (UniformlyConvexOn.gap_le hf hx hy hα0 hα1)

/-- A uniformly convex function satisfies its defining inequality on the effective domain. -/
-- Proof sketch: `UniformlyConvex` is the `effectiveDomain` specialization of
-- `UniformlyConvexOn`.
theorem UniformlyConvex.ineq
    {f : H → Set.Ioi (⊥ : EReal)} {φ : NNReal → EReal} (hf : UniformlyConvex f φ)
    {x y : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (f (α • x + (1 - α) • y) : EReal) +
        ((α * (1 - α) : ℝ) : EReal) * φ ‖x - y‖₊ ≤
      (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) := by
  simpa [UniformlyConvex] using (UniformlyConvexOn.ineq hf hx hy hα0 hα1)

/-- A uniformly convex function is convex on its effective domain. -/
theorem UniformlyConvex.convexOn
    {f : H → Set.Ioi (⊥ : EReal)} {φ : NNReal → EReal} (hf : UniformlyConvex f φ) :
    ConvexOn f (effectiveDomain f) := by
  simpa [UniformlyConvex] using (UniformlyConvexOn.convexOn hf)

/-- A uniformly convex function is strictly convex. -/
theorem UniformlyConvex.strictlyConvex
    {f : H → Set.Ioi (⊥ : EReal)} {φ : NNReal → EReal} (hf : UniformlyConvex f φ) :
    StrictlyConvex f := by
  sorry

/-- A positive strong-convexity constant induces a monotone quadratic modulus. -/
theorem strongConvexityModulus_monotone {β : ℝ} (hβ : 0 < β) :
    Monotone (strongConvexityModulus β) := by
  intro r s hrs
  have hsq : (r : ℝ) ^ 2 ≤ (s : ℝ) ^ 2 := by
    nlinarith [hrs, r.2, s.2]
  have hβ' : 0 ≤ β / 2 := by
    linarith
  exact EReal.coe_le_coe (mul_le_mul_of_nonneg_left hsq hβ')

/-- A positive strong-convexity constant induces a quadratic modulus vanishing exactly at `0`. -/
theorem strongConvexityModulus_eq_zero_iff {β : ℝ} (hβ : 0 < β) (r : NNReal) :
    strongConvexityModulus β r = 0 ↔ r = 0 := by
  constructor
  · intro hr
    have hr' : (β / 2 : ℝ) * (r : ℝ) ^ 2 = 0 := by
      exact EReal.coe_injective (by simpa [strongConvexityModulus] using hr)
    have hr0 : (r : ℝ) = 0 := by
      have hr_sq : (r : ℝ) ^ 2 = 0 := by
        nlinarith [hβ, hr']
      nlinarith
    exact NNReal.coe_inj.mp hr0
  · intro hr
    subst hr
    simp [strongConvexityModulus]

/-- A strongly convex function has nonempty effective domain. -/
theorem StronglyConvex.nonempty {f : H → Set.Ioi (⊥ : EReal)} {β : ℝ}
    (hf : StronglyConvex f β) :
    (effectiveDomain f).Nonempty :=
  hf.1

/-- A strongly convex function has positive convexity constant. -/
-- Proof sketch: unfold `StronglyConvex` and extract the positivity conjunct.
theorem StronglyConvex.pos {f : H → Set.Ioi (⊥ : EReal)} {β : ℝ}
    (hf : StronglyConvex f β) :
    0 < β :=
  hf.2.1

/-- A strongly convex function is proper. -/
theorem StronglyConvex.isProper {f : H → Set.Ioi (⊥ : EReal)} {β : ℝ}
    (hf : StronglyConvex f β) :
    IsProper (fun x : H ↦ (f x : EReal)) := by
  refine ⟨fun x ↦ ne_of_gt (f x).2, ?_⟩
  simpa [effectiveDomain, dom] using hf.nonempty

/-- A strongly convex function satisfies the quadratic Jensen-gap lower bound on its effective
domain. -/
theorem StronglyConvex.gap_le {f : H → Set.Ioi (⊥ : EReal)} {β : ℝ}
    (hf : StronglyConvex f β) {x y : H} (hx : x ∈ effectiveDomain f)
    (hy : y ∈ effectiveDomain f) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ((α * (1 - α) : ℝ) : EReal) * strongConvexityModulus β ‖x - y‖₊ ≤ jensenGap f α x y :=
  hf.2.2 hx hy hα0 hα1

/-- A uniformly convex function with the quadratic modulus coming from a positive constant is
strongly convex with that constant. -/
theorem UniformlyConvex.stronglyConvex
    {f : H → Set.Ioi (⊥ : EReal)} {β : ℝ} (hβ : 0 < β)
    (hf : UniformlyConvex f (strongConvexityModulus β)) :
    StronglyConvex f β := by
  refine ⟨UniformlyConvexOn.nonempty hf, hβ, ?_⟩
  intro x hx y hy α hα0 hα1
  exact hf.gap_le hx hy hα0 hα1

/-- A strongly convex function satisfies the quadratic Jensen inequality on its effective
domain. -/
theorem StronglyConvex.ineq {f : H → Set.Ioi (⊥ : EReal)} {β : ℝ}
    (hf : StronglyConvex f β) {x y : H} (hx : x ∈ effectiveDomain f)
    (hy : y ∈ effectiveDomain f) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (f (α • x + (1 - α) • y) : EReal) +
        ((α * (1 - α) : ℝ) : EReal) * strongConvexityModulus β ‖x - y‖₊ ≤
      (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) := by
  have hgap :
      ((α * (1 - α) : ℝ) : EReal) * strongConvexityModulus β ‖x - y‖₊ ≤
        (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) -
          (f (α • x + (1 - α) • y) : EReal) := by
    simpa [jensenGap] using hf.gap_le hx hy hα0 hα1
  have hcombo_ne_bot : (f (α • x + (1 - α) • y) : EReal) ≠ ⊥ := ne_of_gt (f _).2
  have hsum_ne_top :
      (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) ≠ ⊤ := by
    exact weightedJensenSum_ne_top hx hy hα0 hα1
  simpa [jensenGap, add_comm, add_left_comm, add_assoc] using
    (EReal.le_sub_iff_add_le (Or.inl hcombo_ne_bot) (Or.inr hsum_ne_top)).1 hgap

/-- A strongly convex function is uniformly convex with the associated quadratic modulus. -/
-- Proof sketch: the quadratic modulus is monotone and vanishes only at `0` when `β > 0`, so the
-- defining strong-convexity inequality is exactly the corresponding uniform-convexity inequality.
theorem StronglyConvex.uniformlyConvex
    {f : H → Set.Ioi (⊥ : EReal)} {β : ℝ} (hf : StronglyConvex f β) :
    UniformlyConvex f (strongConvexityModulus β) := by
  refine ⟨hf.nonempty, by intro x hx; exact hx, strongConvexityModulus_monotone hf.pos,
    strongConvexityModulus_eq_zero_iff hf.pos, ?_⟩
  intro x hx y hy α hα0 hα1
  exact hf.gap_le hx hy hα0 hα1

/-- A canonical mathlib uniformly convexity statement on a nonempty set for an everywhere-finite
real-valued function yields the source-facing `EReal` uniformly convexity statement on the same
set with the same modulus. -/
theorem UniformConvexOn.toUniformlyConvexOn
    {g : H → ℝ} {C : Set H} {φ : ℝ → ℝ} (hC_nonempty : C.Nonempty) (hφ_mono : Monotone φ)
    (hφ_zero : ∀ r : NNReal, φ r = 0 ↔ r = 0) (hf : UniformConvexOn C φ g) :
    UniformlyConvexOn g.toEReal C (fun r : NNReal ↦ ((φ r : ℝ) : EReal)) := by
  refine ⟨hC_nonempty, ?_, ?_, ?_, ?_⟩
  · intro x _
    simp [Function.effectiveDomain_toEReal]
  · intro r s hrs
    exact EReal.coe_le_coe (hφ_mono hrs)
  · intro r
    simpa using hφ_zero r
  · intro x hx y hy α hα0 hα1
    have hα_nonneg : 0 ≤ α := hα0.le
    have h1α_nonneg : 0 ≤ 1 - α := sub_nonneg.mpr hα1.le
    have hα_sum : α + (1 - α) = 1 := by ring
    rcases hf with ⟨_, hfineq⟩
    have hbase :
        g (α • x + (1 - α) • y) ≤ α * g x + (1 - α) * g y - α * (1 - α) * φ ‖x - y‖ := by
      simpa using hfineq hx hy hα_nonneg h1α_nonneg hα_sum
    have hineq :
        g (α • x + (1 - α) • y) + α * (1 - α) * φ ‖x - y‖ ≤ α * g x + (1 - α) * g y := by
      linarith
    have hineqE :
        ((((g (α • x + (1 - α) • y) + α * (1 - α) * φ ‖x - y‖ : ℝ) : EReal))) ≤
          (((α * g x + (1 - α) * g y : ℝ) : EReal)) := by
      exact_mod_cast hineq
    have hx_dom : x ∈ effectiveDomain g.toEReal := by
      simp [Function.effectiveDomain_toEReal]
    have hy_dom : y ∈ effectiveDomain g.toEReal := by
      simp [Function.effectiveDomain_toEReal]
    have hcombo_ne_bot : (g.toEReal (α • x + (1 - α) • y) : EReal) ≠ ⊥ :=
      ne_of_gt (g.toEReal _).2
    have hsum_ne_top :
        (α : EReal) * (g.toEReal x : EReal) + (1 - α : EReal) * (g.toEReal y : EReal) ≠ ⊤ :=
      weightedJensenSum_ne_top hx_dom hy_dom hα0 hα1
    have hgap :
        ((α * (1 - α) : ℝ) : EReal) * (((φ ‖x - y‖₊ : ℝ) : EReal)) ≤
          (α : EReal) * (g.toEReal x : EReal) + (1 - α : EReal) * (g.toEReal y : EReal) -
            (g.toEReal (α • x + (1 - α) • y) : EReal) := by
      rw [EReal.le_sub_iff_add_le (Or.inl hcombo_ne_bot) (Or.inr hsum_ne_top)]
      simpa [Function.toEReal_apply, EReal.coe_add, EReal.coe_mul, mul_assoc, mul_left_comm,
        mul_comm, add_assoc, add_left_comm, add_comm] using hineqE
    simpa [jensenGap] using hgap

/-- A canonical mathlib uniform-convexity statement on `Set.univ` for an everywhere-finite
real-valued function yields the source-facing `EReal` uniformly convexity statement with the same
modulus. -/
theorem UniformConvexOn.toUniformlyConvex
    {g : H → ℝ} {φ : ℝ → ℝ} (hφ_mono : Monotone φ)
    (hφ_zero : ∀ r : NNReal, φ r = 0 ↔ r = 0)
    (hf : UniformConvexOn (Set.univ : Set H) φ g) :
    UniformlyConvex g.toEReal (fun r : NNReal ↦ ((φ r : ℝ) : EReal)) := by
  have hf' : UniformlyConvexOn g.toEReal (Set.univ : Set H)
      (fun r : NNReal ↦ ((φ r : ℝ) : EReal)) :=
    UniformConvexOn.toUniformlyConvexOn Set.univ_nonempty hφ_mono hφ_zero hf
  simpa [UniformlyConvex, Function.effectiveDomain_toEReal] using hf'

/-- A canonical mathlib strongly-convexity statement on `Set.univ` for an everywhere-finite
real-valued function yields the source-facing `EReal` strong convexity statement with the same
constant. -/
theorem StrongConvexOn.toStronglyConvex
    {g : H → ℝ} {β : ℝ} (hβ : 0 < β) (hf : StrongConvexOn (Set.univ : Set H) β g) :
    StronglyConvex g.toEReal β := by
  have huniform :
      UniformlyConvexOn g.toEReal (Set.univ : Set H) (strongConvexityModulus β) := by
    refine ⟨Set.univ_nonempty, ?_, strongConvexityModulus_monotone hβ,
      strongConvexityModulus_eq_zero_iff hβ, ?_⟩
    · intro x _
      simp [Function.effectiveDomain_toEReal]
    · intro x _ y _ α hα0 hα1
      have hα_nonneg : 0 ≤ α := hα0.le
      have h1α_nonneg : 0 ≤ 1 - α := sub_nonneg.mpr hα1.le
      have hα_sum : α + (1 - α) = 1 := by ring
      rcases hf with ⟨_, hfineq⟩
      have hbase :
          g (α • x + (1 - α) • y) ≤
            α * g x + (1 - α) * g y - α * (1 - α) * (β / 2 * ‖x - y‖ ^ (2 : ℕ)) := by
        simpa using (hfineq (show x ∈ (Set.univ : Set H) by simp)
          (show y ∈ (Set.univ : Set H) by simp) hα_nonneg h1α_nonneg hα_sum)
      have hineq :
          g (α • x + (1 - α) • y) + α * (1 - α) * (β / 2 * ‖x - y‖ ^ (2 : ℕ)) ≤
            α * g x + (1 - α) * g y := by
        linarith
      have hineqE :
          ((((g (α • x + (1 - α) • y) + α * (1 - α) * (β / 2 * ‖x - y‖ ^ (2 : ℕ)) : ℝ) :
            EReal))) ≤ (((α * g x + (1 - α) * g y : ℝ) : EReal)) := by
        exact_mod_cast hineq
      have hx_dom : x ∈ effectiveDomain g.toEReal := by
        simp [Function.effectiveDomain_toEReal]
      have hy_dom : y ∈ effectiveDomain g.toEReal := by
        simp [Function.effectiveDomain_toEReal]
      have hcombo_ne_bot : (g.toEReal (α • x + (1 - α) • y) : EReal) ≠ ⊥ :=
        ne_of_gt (g.toEReal _).2
      have hsum_ne_top :
          (α : EReal) * (g.toEReal x : EReal) + (1 - α : EReal) * (g.toEReal y : EReal) ≠ ⊤ :=
        weightedJensenSum_ne_top hx_dom hy_dom hα0 hα1
      have hgap :
          ((α * (1 - α) : ℝ) : EReal) * strongConvexityModulus β ‖x - y‖₊ ≤
            (α : EReal) * (g.toEReal x : EReal) + (1 - α : EReal) * (g.toEReal y : EReal) -
              (g.toEReal (α • x + (1 - α) • y) : EReal) := by
        rw [EReal.le_sub_iff_add_le (Or.inl hcombo_ne_bot) (Or.inr hsum_ne_top)]
        simpa [strongConvexityModulus, Function.toEReal_apply, EReal.coe_add, EReal.coe_mul,
          mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using hineqE
      simpa [jensenGap] using hgap
  exact (show UniformlyConvex g.toEReal (strongConvexityModulus β) from
      by simpa [UniformlyConvex, Function.effectiveDomain_toEReal] using huniform).stronglyConvex hβ

/-- An everywhere-finite source-facing uniformly convex function yields the canonical mathlib
uniformly convexity statement on `Set.univ`. -/
theorem UniformlyConvex.toUniformConvexOn
    {g : H → ℝ} {φ : ℝ → ℝ}
    (hf : UniformlyConvex g.toEReal (fun r : NNReal ↦ ((φ r : ℝ) : EReal))) :
    UniformConvexOn (Set.univ : Set H) φ g := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  by_cases ha_zero : a = 0
  · subst ha_zero
    have hb_one : b = 1 := by linarith
    subst hb_one
    simp
  by_cases hb_zero : b = 0
  · subst hb_zero
    have ha_one : a = 1 := by linarith
    subst ha_one
    simp
  have hx_dom : x ∈ effectiveDomain g.toEReal := by
    simp [Function.effectiveDomain_toEReal]
  have hy_dom : y ∈ effectiveDomain g.toEReal := by
    simp [Function.effectiveDomain_toEReal]
  have ha_pos : 0 < a := lt_of_le_of_ne ha <| Ne.symm ha_zero
  have hb_pos : 0 < b := lt_of_le_of_ne hb <| Ne.symm hb_zero
  have ha_lt_one : a < 1 := by
    linarith [hb_pos, hab]
  have hb_eq : b = 1 - a := by linarith
  rw [smul_eq_mul, smul_eq_mul, hb_eq, le_sub_iff_add_le]
  have hgap :
      ((a * (1 - a) : ℝ) : EReal) * (((φ ‖x - y‖ : ℝ) : EReal)) ≤
        (a : EReal) * (g.toEReal x : EReal) + (1 - a : EReal) * (g.toEReal y : EReal) -
          (g.toEReal (a • x + (1 - a) • y) : EReal) := by
    simpa [UniformlyConvex, jensenGap] using
      (show ((a * (1 - a) : ℝ) : EReal) * (((φ ‖x - y‖ : ℝ) : EReal)) ≤
          jensenGap g.toEReal a x y from
        hf.gap_le hx_dom hy_dom ha_pos ha_lt_one)
  have hineqE :
      ((((g (a • x + (1 - a) • y) + a * (1 - a) * φ ‖x - y‖) : ℝ) : EReal)) ≤
        (((a * g x + (1 - a) * g y : ℝ) : EReal)) := by
    have hcombo_ne_bot : (g.toEReal (a • x + (1 - a) • y) : EReal) ≠ ⊥ := ne_of_gt (g.toEReal _).2
    have hsum_ne_top :
        (a : EReal) * (g.toEReal x : EReal) + (1 - a : EReal) * (g.toEReal y : EReal) ≠ ⊤ :=
      weightedJensenSum_ne_top hx_dom hy_dom ha_pos ha_lt_one
    simpa [Function.toEReal_apply, EReal.coe_add, EReal.coe_mul, mul_assoc, mul_left_comm,
      mul_comm, add_assoc, add_left_comm, add_comm] using
      (EReal.le_sub_iff_add_le (Or.inl hcombo_ne_bot) (Or.inr hsum_ne_top)).1 hgap
  exact_mod_cast hineqE

/-- Under an explicit convexity hypothesis on `C`, the source-facing `EReal` notion induces the
canonical mathlib uniformly convexity statement for the finite real-valued model. -/
theorem UniformlyConvexOn.toUniformConvexOn
    {g : H → ℝ} {C : Set H} {φ : ℝ → ℝ} (hC : Convex ℝ C)
    (hf : UniformlyConvexOn g.toEReal C (fun r : NNReal ↦ ((φ r : ℝ) : EReal))) :
    UniformConvexOn C φ g := by
  refine ⟨hC, ?_⟩
  intro x hx y hy a b ha hb hab
  by_cases ha_zero : a = 0
  · subst ha_zero
    have hb_one : b = 1 := by linarith
    subst hb_one
    simp
  by_cases hb_zero : b = 0
  · subst hb_zero
    have ha_one : a = 1 := by linarith
    subst ha_one
    simp
  have ha_pos : 0 < a := lt_of_le_of_ne ha <| Ne.symm ha_zero
  have hb_pos : 0 < b := lt_of_le_of_ne hb <| Ne.symm hb_zero
  have ha_lt_one : a < 1 := by
    linarith [hb_pos, hab]
  have hb_eq : b = 1 - a := by linarith
  rw [smul_eq_mul, smul_eq_mul, hb_eq, le_sub_iff_add_le]
  have hgap :
      ((a * (1 - a) : ℝ) : EReal) * (((φ ‖x - y‖ : ℝ) : EReal)) ≤
        (a : EReal) * (g.toEReal x : EReal) + (1 - a : EReal) * (g.toEReal y : EReal) -
          (g.toEReal (a • x + (1 - a) • y) : EReal) := by
    simpa [jensenGap] using hf.gap_le hx hy ha_pos ha_lt_one
  have hineqE :
      ((((g (a • x + (1 - a) • y) + a * (1 - a) * φ ‖x - y‖) : ℝ) : EReal)) ≤
        (((a * g x + (1 - a) * g y : ℝ) : EReal)) := by
    have hx_dom : x ∈ effectiveDomain g.toEReal := by
      exact hf.2.1 hx
    have hy_dom : y ∈ effectiveDomain g.toEReal := by
      exact hf.2.1 hy
    have hcombo_ne_bot : (g.toEReal (a • x + (1 - a) • y) : EReal) ≠ ⊥ := ne_of_gt (g.toEReal _).2
    have hsum_ne_top :
        (a : EReal) * (g.toEReal x : EReal) + (1 - a : EReal) * (g.toEReal y : EReal) ≠ ⊤ :=
      weightedJensenSum_ne_top hx_dom hy_dom ha_pos ha_lt_one
    simpa [Function.toEReal_apply, EReal.coe_add, EReal.coe_mul, mul_assoc, mul_left_comm,
      mul_comm, add_assoc, add_left_comm, add_comm] using
      (EReal.le_sub_iff_add_le (Or.inl hcombo_ne_bot) (Or.inr hsum_ne_top)).1 hgap
  exact_mod_cast hineqE

/-- A source-facing strongly convex `EReal` function on an everywhere-finite real model yields the
canonical mathlib `StrongConvexOn` statement on `Set.univ`. -/
theorem StronglyConvex.toStrongConvexOn
    {g : H → ℝ} {β : ℝ} (hf : StronglyConvex g.toEReal β) :
    StrongConvexOn (Set.univ : Set H) β g := by
  simpa [StrongConvexOn] using
    (hf.uniformlyConvex.toUniformConvexOn :
      UniformConvexOn (Set.univ : Set H) (fun r ↦ β / 2 * r ^ (2 : ℕ)) g)

end ERealFunction

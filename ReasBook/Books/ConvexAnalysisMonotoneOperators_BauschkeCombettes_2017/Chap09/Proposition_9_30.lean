/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_17
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_28
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_27
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_29

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u v

namespace ERealFunction

section Basic

variable {H : Type u}

/-- The canonical additive identity on `]-∞,+∞]`-valued functions is the constant-zero
function. -/
noncomputable instance : Zero (H → Set.Ioi (⊥ : EReal)) :=
  ⟨fun _ ↦ ⟨0, EReal.bot_lt_zero⟩⟩

/-- The canonical source-facing addition on `]-∞,+∞]`-valued functions is pointwise addition. -/
noncomputable instance : Add (H → Set.Ioi (⊥ : EReal)) :=
  ⟨pointwiseAdd⟩

/-- The canonical source-facing additive structure on `]-∞,+∞]`-valued functions is pointwise
addition. -/
noncomputable instance : AddCommMonoid (H → Set.Ioi (⊥ : EReal)) where
  zero := 0
  add := (· + ·)
  add_assoc f g h := by
    funext x
    apply Subtype.ext
    change ((f x : EReal) + (g x : EReal)) + (h x : EReal) =
      (f x : EReal) + ((g x : EReal) + (h x : EReal))
    simp [add_assoc]
  zero_add f := by
    funext x
    apply Subtype.ext
    change (0 : EReal) + (f x : EReal) = (f x : EReal)
    simp
  add_zero f := by
    funext x
    apply Subtype.ext
    change (f x : EReal) + (0 : EReal) = (f x : EReal)
    simp
  nsmul := nsmulRec
  nsmul_zero := by
    intro f
    rfl
  nsmul_succ := by
    intro n f
    rfl
  add_comm f g := by
    funext x
    apply Subtype.ext
    change (f x : EReal) + (g x : EReal) = (g x : EReal) + (f x : EReal)
    simp [add_comm]

/-- Coercing the additive identity of `]-∞,+∞]`-valued functions to `EReal` recovers the constant
zero function. -/
@[simp] theorem zero_apply (x : H) :
    ((0 : H → Set.Ioi (⊥ : EReal)) x : EReal) = 0 :=
  rfl

/-- Coercing `f + g` to `EReal` recovers ordinary pointwise addition. -/
@[simp] theorem add_apply
    (f g : H → Set.Ioi (⊥ : EReal)) (x : H) :
    ((f + g) x : EReal) = (f x : EReal) + (g x : EReal) :=
  rfl

/-- Coercing a finite pointwise sum of `]-∞,+∞]`-valued functions to `EReal` recovers the ordinary
finite sum of the coerced values. -/
@[simp] theorem sum_apply {ι : Type v} (s : Finset ι)
    (f : ι → H → Set.Ioi (⊥ : EReal)) (x : H) :
    ((∑ i ∈ s, f i) x : EReal) = ∑ i ∈ s, (f i x : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      simp [Finset.sum_insert, hi, ih, add_apply]

/-- The separable sum of `f` and `g` on the product space `H × H`. -/
infixr:65 " ⊕ " => fun f g ↦ pointwiseAdd (f ∘ Prod.fst) (g ∘ Prod.snd)

/-- Coercing `f ⊕ g` to `EReal` recovers the separable sum `(x, y) ↦ f x + g y`. -/
@[simp] theorem separableSum_apply
    (f g : H → Set.Ioi (⊥ : EReal)) (p : H × H) :
    ((f ⊕ g) p : EReal) = (f p.1 : EReal) + (g p.2 : EReal) := by
  simp [pointwiseAdd_apply]

/-- Helper for Proposition 9.30: the effective domain of the pointwise sum is exactly the
intersection of the effective domains of the summands. -/
-- Proof sketch: finiteness of the extended-real sum is equivalent to finiteness of both
-- summands, because neither summand can take the value `⊥`.
theorem mem_effectiveDomain_pointwiseAdd_iff
    (f g : H → Set.Ioi (⊥ : EReal)) (x : H) :
    x ∈ effectiveDomain (f + g) ↔
      x ∈ effectiveDomain f ∧ x ∈ effectiveDomain g := by
  -- Rewrite effective-domain membership to non-`⊤` statements and use the sum criterion.
  rw [mem_effectiveDomain_iff, mem_effectiveDomain_iff, mem_effectiveDomain_iff,
    add_apply, lt_top_iff_ne_top, lt_top_iff_ne_top, lt_top_iff_ne_top]
  exact EReal.add_ne_top_iff_ne_top₂ (ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2))
    (ne_of_gt (show (⊥ : EReal) < (g x : EReal) from (g x).2))

/-- If the effective domains of `f` and `g` meet, then the effective domain of `f + g` is
nonempty. -/
-- Proof sketch: pick a common point of the effective domains; both values are finite there, so
-- their sum is finite as well.
theorem effectiveDomain_add_nonempty_of_inter_nonempty
    (f g : H → Set.Ioi (⊥ : EReal))
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    (effectiveDomain (f + g)).Nonempty := by
  rcases hdom with ⟨x, hx, hgx⟩
  refine ⟨x, ?_⟩
  -- A common effective-domain point is exactly a point of the effective domain of the sum.
  exact (mem_effectiveDomain_pointwiseAdd_iff f g x).2 ⟨hx, hgx⟩

end Basic

section Linear

variable {H : Type u} [TopologicalSpace H] [AddCommGroup H] [Module ℝ H] [SequentialSpace H]
  [IsTopologicalAddGroup H] [ContinuousSMul ℝ H]

/-- Helper for Proposition 9.30: the sum of two lower semicontinuous `EReal`-valued functions is
lower semicontinuous. -/
private theorem lowerSemicontinuous_add_ereal
    {g h : H → EReal} (hg : LowerSemicontinuous g) (hh : LowerSemicontinuous h) :
    LowerSemicontinuous (fun x ↦ g x + h x) := by
  -- Compare the pointwise sum with the liminf of each summand and then use `EReal.le_liminf_add`.
  rw [lowerSemicontinuous_iff_le_liminf]
  intro x
  calc
    g x + h x ≤ Filter.liminf g (nhds x) + Filter.liminf h (nhds x) :=
      add_le_add (hg.le_liminf x) (hh.le_liminf x)
    _ ≤ Filter.liminf (fun y ↦ g y + h y) (nhds x) := by
      simpa using
        (EReal.le_liminf_add :
          Filter.liminf g (nhds x) + Filter.liminf h (nhds x) ≤
            Filter.liminf (g + h) (nhds x))

/-- Helper for Proposition 9.30: translating the argument of a lower semicontinuous function and
subtracting a finite base value preserves lower semicontinuity. -/
private theorem translated_increment_lowerSemicontinuous
    (f : H → Set.Ioi (⊥ : EReal))
    (hf_lsc : LowerSemicontinuous (fun z : H ↦ (f z : EReal)))
    {x : H} (hx : x ∈ effectiveDomain f) :
    LowerSemicontinuous (fun y : H ↦ (f (x + y) : EReal) - (f x : EReal)) := by
  -- Compose lower semicontinuity with translation by `x`.
  have htranslate : Continuous (fun y : H ↦ x + y) := continuous_const.add continuous_id
  have hcomp : LowerSemicontinuous (fun y : H ↦ (f (x + y) : EReal)) :=
    hf_lsc.comp htranslate
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hconst :
      LowerSemicontinuous (fun _ : H ↦ ((-((f x : EReal).toReal) : ℝ) : EReal)) :=
    lowerSemicontinuous_const
  -- Rewrite subtraction by the finite value `f x` as addition of a constant real cast.
  have hadd := lowerSemicontinuous_add_ereal hcomp hconst
  simpa [sub_eq_add_neg, EReal.coe_toReal hx_top hx_bot] using hadd

/-- Helper for Proposition 9.30: the recession function is the indexed supremum of translated
increments over the effective domain. -/
private theorem recessionFunction_eq_iSup_effectiveDomain_increment
    (f : H → Set.Ioi (⊥ : EReal))
    (hdom : (effectiveDomain f).Nonempty) (y : H) :
    (recessionFunction f hdom y : EReal) =
      ⨆ x : effectiveDomain f, ((f ((x : H) + y) : EReal) - (f x : EReal)) := by
  -- Rewrite the defining `sSup` over an image as an `iSup` over the subtype of domain points.
  rw [recessionFunction_apply, sSup_image, iSup_subtype]

/-- The pointwise sum of two members of `Γ₀(H)` again belongs to `Γ₀(H)` as soon as their
effective domains meet. -/
-- Proof sketch: lower semicontinuity is preserved by pointwise addition, and Jensen convexity of
-- the sum is obtained by adding the Jensen inequalities for the two summands after rewriting the
-- effective-domain condition componentwise.
theorem pointwiseAdd_mem_gammaZero
    (f g : H → Set.Ioi (⊥ : EReal))
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    f + g ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff]
  refine ⟨?_, ?_⟩
  · -- Lower semicontinuity is preserved by pointwise addition of the extended-real representatives.
    simpa [pointwiseAdd_apply] using lowerSemicontinuous_add_ereal hf.1 hg.1
  · -- Route correction: prove convexity directly on the effective domain of the sum, rather than
    -- rebuilding a separate epigraph API just for clause (vi).
    refine ⟨effectiveDomain_add_nonempty_of_inter_nonempty f g hdom, subset_rfl, ?_⟩
    intro x hx y hy α hα hα_lt_one
    rcases (mem_effectiveDomain_pointwiseAdd_iff f g x).1 hx with ⟨hx_f, hx_g⟩
    rcases (mem_effectiveDomain_pointwiseAdd_iff f g y).1 hy with ⟨hy_f, hy_g⟩
    calc
      (pointwiseAdd f g (α • x + (1 - α) • y) : EReal)
          = (f (α • x + (1 - α) • y) : EReal) +
              (g (α • x + (1 - α) • y) : EReal) := by
            simpa using pointwiseAdd_apply f g (α • x + (1 - α) • y)
      _ ≤ ((α : EReal) * (f x : EReal) + (((1 - α : ℝ) : EReal) * (f y : EReal))) +
            ((α : EReal) * (g x : EReal) + (((1 - α : ℝ) : EReal) * (g y : EReal))) := by
            exact add_le_add (hf.2.ineq hx_f hy_f hα hα_lt_one) (hg.2.ineq hx_g hy_g hα hα_lt_one)
      _ = (α : EReal) * ((f x : EReal) + (g x : EReal)) +
            (((1 - α : ℝ) : EReal) * ((f y : EReal) + (g y : EReal))) := by
            have hα_nonneg : (0 : EReal) ≤ (α : EReal) := EReal.coe_nonneg.mpr hα.le
            have hβ_nonneg : (0 : EReal) ≤ (((1 - α : ℝ) : EReal)) :=
              EReal.coe_nonneg.mpr (sub_nonneg.mpr hα_lt_one.le)
            have hα_ne_top : (α : EReal) ≠ ⊤ := EReal.coe_ne_top α
            have hβ_ne_top : (((1 - α : ℝ) : EReal)) ≠ ⊤ := EReal.coe_ne_top (1 - α)
            rw [EReal.left_distrib_of_nonneg_of_ne_top hα_nonneg hα_ne_top,
              EReal.left_distrib_of_nonneg_of_ne_top hβ_nonneg hβ_ne_top]
            simp [add_assoc, add_left_comm]
      _ = (α : EReal) * (pointwiseAdd f g x : EReal) +
            (((1 - α : ℝ) : EReal) * (pointwiseAdd f g y : EReal)) := by
            simp [pointwiseAdd_apply]

omit [TopologicalSpace H] [SequentialSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H] in
/-- Helper for Proposition 9.30: the recession cone of a convex set is convex. -/
private theorem recessionCone_convex_of_convex {C : Set H}
    (hC_convex : Convex ℝ C) :
    Convex ℝ (Set.recessionCone C) := by
  -- Unfold the recession-cone condition and use convexity on translated points of `C`.
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  rw [Set.mem_recessionCone_iff] at hx hy ⊢
  intro z hz
  rcases Set.mem_add.1 hz with ⟨w, hw, c, hc, rfl⟩
  have hw' : w = a • x + b • y := by
    simpa using hw
  subst hw'
  have hxz : x + c ∈ C := by
    exact hx (Set.add_mem_add (by simp) hc)
  have hyz : y + c ∈ C := by
    exact hy (Set.add_mem_add (by simp) hc)
  have hcombo : a • (x + c) + b • (y + c) ∈ C := by
    exact (convex_iff_add_mem.1 hC_convex) hxz hyz ha hb hab
  have hrewrite : a • (x + c) + b • (y + c) = a • x + b • y + c := by
    calc
      a • (x + c) + b • (y + c) = (a • x + a • c) + (b • y + b • c) := by
        rw [smul_add, smul_add]
      _ = (a • x + b • y) + (a • c + b • c) := by
        abel
      _ = (a • x + b • y) + (a + b) • c := by
        rw [← add_smul]
      _ = (a • x + b • y) + c := by
        rw [hab, one_smul]
      _ = a • x + b • y + c := by
        rw [add_assoc]
  exact hrewrite ▸ hcombo

/-- Proposition 9.30 (1): clause (i). The recession function of a `Γ₀(H)` function again belongs
to `Γ₀(H)`. -/
-- Proof sketch: combine the epigraph description of the recession function with stability of lower
-- semicontinuity and convexity under the pointwise-supremum formula from the definition.
theorem recessionFunction_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    recessionFunction f hf.2.nonempty ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff]
  refine ⟨?_, ?_⟩
  · -- Lower semicontinuity comes from the `iSup` formula and the translated-increment helper.
    let g : H → EReal :=
      fun y ↦ ⨆ x : effectiveDomain f, ((f ((x : H) + y) : EReal) - (f x : EReal))
    have hg_lsc : LowerSemicontinuous g := by
      -- Each translated increment is lower semicontinuous, so the indexed supremum is too.
      simpa [g] using
        lowerSemicontinuous_iSup
          (fun x : effectiveDomain f ↦ translated_increment_lowerSemicontinuous f hf.1 x.2)
    -- The helper `iSup` formula identifies `g` with the recession function.
    have hg_eq : g = fun y : H ↦ (recessionFunction f hf.2.nonempty y : EReal) := by
      funext y
      simpa [g] using
        (recessionFunction_eq_iSup_effectiveDomain_increment f hf.2.nonempty y).symm
    simpa [hg_eq] using hg_lsc
  · -- Convexity is inherited from the epigraph identification with the recession cone.
    have hconv_epi_f : Convex ℝ (epigraph (fun y : H ↦ (f y : EReal))) := by
      -- Rewrite the stored Jensen inequality into the epigraph criterion.
      refine (convex_epigraph_iff_jensen_on_dom (fun y : H ↦ (f y : EReal))).2 ?_
      intro x y hx hy α hα hα_lt_one
      have hx' : x ∈ effectiveDomain f := by
        simpa [effectiveDomain, dom] using hx
      have hy' : y ∈ effectiveDomain f := by
        simpa [effectiveDomain, dom] using hy
      simpa using hf.2.ineq hx' hy' hα hα_lt_one
    have hconv_epi_rec :
        Convex ℝ (epigraph (fun y : H ↦ (recessionFunction f hf.2.nonempty y : EReal))) := by
      rw [epigraph_recessionFunction_eq_recessionCone_epigraph f hf.2]
      exact recessionCone_convex_of_convex hconv_epi_f
    have hzero_mem :
        (0 : H) ∈ effectiveDomain (recessionFunction f hf.2.nonempty) := by
      -- At `0`, every translated increment is zero, so the recession value is exactly `0`.
      rw [mem_effectiveDomain_iff]
      rcases hf.2.nonempty with ⟨x, hx⟩
      have hzero_image :
          ((fun a : H ↦ (f (a + 0) : EReal) - (f a : EReal)) '' effectiveDomain f) =
            ({0} : Set EReal) := by
        ext t
        constructor
        · rintro ⟨a, ha, rfl⟩
          have ha_top : (f a : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp ha)
          have ha_bot : (f a : EReal) ≠ ⊥ := by
            exact ne_of_gt (show (⊥ : EReal) < (f a : EReal) from (f a).2)
          change ((f (a + 0) : EReal) - (f a : EReal)) = 0
          rw [show a + 0 = a by simp, ← EReal.coe_toReal ha_top ha_bot,
            ← EReal.coe_toReal ha_top ha_bot]
          simpa using sub_self ((((f a : EReal).toReal : ℝ) : EReal))
        · intro ht
          rw [Set.mem_singleton_iff] at ht
          subst ht
          refine ⟨x, hx, ?_⟩
          have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hx)
          have hx_bot : (f x : EReal) ≠ ⊥ := by
            exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
          change ((f (x + 0) : EReal) - (f x : EReal)) = 0
          rw [show x + 0 = x by simp, ← EReal.coe_toReal hx_top hx_bot,
            ← EReal.coe_toReal hx_top hx_bot]
          simpa using sub_self ((((f x : EReal).toReal : ℝ) : EReal))
      rw [recessionFunction_apply, hzero_image]
      simpa using (EReal.coe_lt_top (0 : ℝ))
    have hJ :=
      (convex_epigraph_iff_jensen_on_dom
        (fun y : H ↦ (recessionFunction f hf.2.nonempty y : EReal))).1 hconv_epi_rec
    refine ⟨⟨0, hzero_mem⟩, subset_rfl, ?_⟩
    intro x hx y hy α hα hα_lt_one
    have hx' : x ∈ dom (fun y : H ↦ (recessionFunction f hf.2.nonempty y : EReal)) := by
      simpa [effectiveDomain, dom] using hx
    have hy' : y ∈ dom (fun y : H ↦ (recessionFunction f hf.2.nonempty y : EReal)) := by
      simpa [effectiveDomain, dom] using hy
    exact hJ hx' hy' hα hα_lt_one

/-- Helper for Proposition 9.30: dividing a finite real cast by a positive scalar tends to `0` in
`EReal` along `α → +∞`. -/
-- Proof sketch: first prove the corresponding real limit, then transport it through the real
-- coercion into `EReal`.
private theorem ereal_coe_div_tendsto_zero_atTop
    (c : ℝ) :
    Filter.Tendsto (fun α : Set.Ioi (0 : ℝ) ↦ ((c : EReal) / (α : ℝ)))
      Filter.atTop (nhds (0 : EReal)) := by
  -- The subtype coercion from `ℝ_{++}` to `ℝ` preserves the `atTop` filter.
  have hcoe : Filter.Tendsto (fun α : Set.Ioi (0 : ℝ) ↦ (α : ℝ)) Filter.atTop Filter.atTop := by
    simpa [Filter.Tendsto] using (map_val_Ioi_atTop (0 : ℝ))
  have hreal :
      Filter.Tendsto (fun α : Set.Ioi (0 : ℝ) ↦ c / (α : ℝ)) Filter.atTop (nhds (0 : ℝ)) := by
    -- The real-valued reciprocal tends to `0`, so multiplying by the constant `c` still tends to `0`.
    simpa [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hcoe))
  have hEq :
      (fun α : Set.Ioi (0 : ℝ) ↦ ((c : EReal) / (α : ℝ))) =
        fun α : Set.Ioi (0 : ℝ) ↦ ((c / (α : ℝ) : ℝ) : EReal) := by
    funext α
    rw [← EReal.coe_div]
  -- The `EReal` statement is exactly the coercion of the real-valued limit.
  rw [hEq]
  simpa using (EReal.tendsto_coe.2 hreal)

/-- Helper for Proposition 9.30: the affine perturbation used in the source proof is exactly the
convex combination of `z` and `x + β • y` with coefficient `1 / β`. -/
-- Proof sketch: expand both sides with `smul_add`, use bilinearity, and simplify the scalar
-- coefficients with the identity `(1 / β) * β = 1`.
private theorem translated_increment_argument_eq
    (x z y : H) {β : ℝ} (hβ : β ≠ 0) :
    z + (y + β⁻¹ • (x - z)) =
      (1 - 1 / β) • z + (1 / β) • (x + β • y) := by
  -- Rewrite the right-hand side into the additive form appearing on the left.
  calc
    z + (y + β⁻¹ • (x - z))
        = z + y + β⁻¹ • x - β⁻¹ • z := by
            simp [sub_eq_add_neg, smul_add, add_assoc, add_left_comm, add_comm]
    _ = (1 - 1 / β) • z + (1 / β) • x + y := by
          simp [sub_eq_add_neg, one_div, smul_add, add_smul, add_assoc, add_left_comm, add_comm]
    _ = (1 - 1 / β) • z + (1 / β) • (x + β • y) := by
          rw [smul_add]
          simp [smul_smul, one_div, inv_mul_cancel₀ hβ, add_assoc]

/-- Helper for Proposition 9.30: the directional difference quotient tends to the supremum of its
range because Proposition 9.27 makes it monotone. -/
-- Proof sketch: apply monotone convergence on `EReal` and rewrite the resulting `iSup` as the
-- `sSup` of the range.
private theorem tendsto_directionalDifferenceQuotient_to_sSup
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    {x : H} (hx : x ∈ effectiveDomain f) (y : H) :
    Filter.Tendsto (directionalDifferenceQuotient f x y) Filter.atTop
      (nhds (sSup (Set.range (directionalDifferenceQuotient f x y)))) := by
  -- Monotone convergence identifies the limit with the supremum of the range.
  have hmono := directionalDifferenceQuotient_monotone f hf.2 hx y
  simpa [sSup_range] using tendsto_atTop_ciSup hmono (OrderTop.bddAbove _)

/-- Helper for Proposition 9.30: the scaled ray value splits into the directional difference
quotient and the vanishing base-point correction. -/
-- Proof sketch: if the endpoint value is `⊤`, both sides are `⊤`; otherwise all terms are finite,
-- so rewrite them as real casts and use ordinary field algebra.
private theorem scaled_ray_value_eq_directionalDifferenceQuotient_add_base_div
    (f : H → Set.Ioi (⊥ : EReal)) {x : H} (hx : x ∈ effectiveDomain f) (y : H)
    (α : Set.Ioi (0 : ℝ)) :
    (f (x + (α : ℝ) • y) : EReal) / (α : ℝ) =
      directionalDifferenceQuotient f x y α + ((f x : EReal) / (α : ℝ)) := by
  -- Split on whether the endpoint on the ray is finite.
  by_cases htop : (f (x + (α : ℝ) • y) : EReal) = ⊤
  · rw [directionalDifferenceQuotient, htop]
    have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hα_pos : (0 : EReal) < ((α : ℝ) : EReal) := by
      exact_mod_cast α.2
    have hα_ne_top : ((α : ℝ) : EReal) ≠ ⊤ := ne_of_lt (EReal.coe_lt_top _)
    rw [EReal.top_sub hx_top, EReal.top_div_of_pos_ne_top hα_pos hα_ne_top,
      ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_div]
    simp
  · have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hxy_bot : (f (x + (α : ℝ) • y) : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f (x + (α : ℝ) • y) : EReal) from
        (f (x + (α : ℝ) • y)).2)
    have hα_ne : (α : ℝ) ≠ 0 := ne_of_gt α.2
    rw [directionalDifferenceQuotient, ← EReal.coe_toReal htop hxy_bot,
      ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_div, ← EReal.coe_div, ← EReal.coe_sub,
      ← EReal.coe_div, ← EReal.coe_add]
    congr 1
    field_simp [hα_ne]
    ring

/-- Helper for Proposition 9.30: every translated increment based at an effective-domain point is
bounded above by the recession-function value. -/
-- Proof sketch: this is immediate from the defining supremum formula for the recession function.
private theorem increment_le_recessionFunction_of_mem_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    {z : H} (hz : z ∈ effectiveDomain f) (y : H) :
    ((f (z + y) : EReal) - (f z : EReal)) ≤
      (recessionFunction f hf.2.nonempty y : EReal) := by
  -- The translated increment is one of the image points whose supremum defines the recession value.
  rw [recessionFunction_apply]
  exact (isLUB_sSup _).1 ⟨z, hz, rfl⟩

/-- Helper for Proposition 9.30: once both ray endpoints are finite, the directional difference
quotient is the cast of the corresponding real quotient. -/
-- Proof sketch: rewrite each finite `EReal` endpoint as the cast of its `toReal`, then collapse
-- subtraction and division back to the ordinary real quotient.
private theorem directionalDifferenceQuotient_eq_coe_real_quotient_of_mem_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) {x y : H}
    (hx : x ∈ effectiveDomain f) (a : Set.Ioi (0 : ℝ))
    (ha : x + (a : ℝ) • y ∈ effectiveDomain f) :
    directionalDifferenceQuotient f x y a =
      ((((f (x + (a : ℝ) • y) : EReal).toReal - (f x : EReal).toReal) / (a : ℝ) : ℝ) : EReal) := by
  -- Route correction: make the finite-endpoint coercion bridge explicit here so the integer-ray
  -- proof can stay in `ℝ` after one rewrite.
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hxa_top : (f (x + (a : ℝ) • y) : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp ha)
  have hxa_bot : (f (x + (a : ℝ) • y) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (x + (a : ℝ) • y) : EReal) from
      (f (x + (a : ℝ) • y)).2)
  rw [directionalDifferenceQuotient, ← EReal.coe_toReal hxa_top hxa_bot,
    ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_sub, ← EReal.coe_div]
  simp

/-- Helper for Proposition 9.30: a finite recession value keeps the whole integer ray in the
effective domain and yields the telescoping real estimate along that ray. -/
-- Proof sketch: induct on the integer step, use the recession-function increment bound to keep the
-- next point finite, convert the one-step `EReal` inequality to a real inequality, and telescope.
private theorem integer_ray_mem_effectiveDomain_and_toReal_sub_le_mul_recession_toReal
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    {x : H} (hx : x ∈ effectiveDomain f) (y : H)
    (hrec_top : (recessionFunction f hf.2.nonempty y : EReal) ≠ ⊤) :
    ∀ n : ℕ,
      x + ((n : ℕ) : ℝ) • y ∈ effectiveDomain f ∧
        ((f (x + ((n : ℕ) : ℝ) • y) : EReal).toReal - (f x : EReal).toReal) ≤
          (n : ℝ) * (recessionFunction f hf.2.nonempty y : EReal).toReal := by
  let r : EReal := (recessionFunction f hf.2.nonempty y : EReal)
  have hr_top : r ≠ ⊤ := by
    simpa [r] using hrec_top
  have hr_bot : r ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < r from by simpa [r] using (recessionFunction f hf.2.nonempty y).2)
  intro n
  induction n with
  | zero =>
      constructor
      · simpa using hx
      · simp [r]
  | succ k ih =>
      rcases ih with ⟨hk_dom, hk_bound⟩
      let zk : H := x + ((k : ℕ) : ℝ) • y
      let zk1 : H := x + ((k + 1 : ℕ) : ℝ) • y
      have hk_top : (f zk : EReal) ≠ ⊤ := by
        exact ne_of_lt ((mem_effectiveDomain_iff).mp hk_dom)
      have hk_bot : (f zk : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (f zk : EReal) from (f zk).2)
      have hincr :
          ((f zk1 : EReal) - (f zk : EReal)) ≤ r := by
        -- Reindex the translated increment at the current integer step.
        simpa [r, zk, zk1, Nat.cast_add, add_smul, one_smul, add_assoc, add_left_comm, add_comm]
          using
            (increment_le_recessionFunction_of_mem_effectiveDomain
              (f := f) (hf := hf) (z := zk) hk_dom y)
      have hk1_le_add : (f zk1 : EReal) ≤ r + (f zk : EReal) := by
        exact (EReal.sub_le_iff_le_add (.inl hk_bot) (.inl hk_top)).1 hincr
      have hk1_dom : zk1 ∈ effectiveDomain f := by
        -- Finiteness of the previous point and of the recession value forces finiteness of the
        -- next point on the ray.
        rw [mem_effectiveDomain_iff]
        exact lt_of_le_of_lt hk1_le_add (EReal.add_lt_top hr_top hk_top)
      have hk1_top : (f zk1 : EReal) ≠ ⊤ := by
        exact ne_of_lt ((mem_effectiveDomain_iff).mp hk1_dom)
      have hk1_bot : (f zk1 : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (f zk1 : EReal) from (f zk1).2)
      have hstep_real :
          (f zk1 : EReal).toReal - (f zk : EReal).toReal ≤ r.toReal := by
        -- Once both endpoints are finite, the one-step increment comparison becomes an ordinary
        -- real inequality.
        have hsub_eq :
            ((f zk1 : EReal) - (f zk : EReal)) =
              ((((f zk1 : EReal).toReal - (f zk : EReal).toReal : ℝ)) : EReal) := by
          rw [← EReal.coe_toReal hk1_top hk1_bot, ← EReal.coe_toReal hk_top hk_bot,
            ← EReal.coe_sub]
          simp
        have hincr' :
            ((((f zk1 : EReal).toReal - (f zk : EReal).toReal : ℝ)) : EReal) ≤ r := by
          rw [← hsub_eq]
          exact hincr
        rw [← EReal.coe_toReal hr_top hr_bot] at hincr'
        exact EReal.coe_le_coe_iff.mp hincr'
      constructor
      · simpa [zk1] using hk1_dom
      · -- Add the new one-step estimate to the induction hypothesis and telescope.
        have hk1_bound :
            (f zk1 : EReal).toReal - (f x : EReal).toReal ≤
              (k : ℝ) * r.toReal + r.toReal := by
          linarith [hk_bound, hstep_real]
        have hk1_bound' :
            (f zk1 : EReal).toReal - (f x : EReal).toReal ≤
              ((k + 1 : ℕ) : ℝ) * r.toReal := by
          calc
            (f zk1 : EReal).toReal - (f x : EReal).toReal
                ≤ (k : ℝ) * r.toReal + r.toReal := hk1_bound
            _ = ((k + 1 : ℕ) : ℝ) * r.toReal := by
                norm_num [Nat.cast_add]
                ring
        simpa [r, zk1]
          using hk1_bound'

/-- Helper for Proposition 9.30: the integer-ray telescoping estimate from the source proof. -/
-- Proof sketch: specialize the combined integer-ray induction to the endpoint `x + (n + 1) • y`
-- and keep only the real-valued inequality.
private theorem integer_ray_toReal_sub_le_mul_recession_toReal
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    {x : H} (hx : x ∈ effectiveDomain f) (y : H)
    (hrec_top : (recessionFunction f hf.2.nonempty y : EReal) ≠ ⊤) (n : ℕ) :
    ((f (x + ((n + 1 : ℕ) : ℝ) • y) : EReal).toReal - (f x : EReal).toReal) ≤
      ((n + 1 : ℕ) : ℝ) * (recessionFunction f hf.2.nonempty y : EReal).toReal := by
  -- This is exactly the second component of the combined integer-ray induction at step `n + 1`.
  simpa using
    (integer_ray_mem_effectiveDomain_and_toReal_sub_le_mul_recession_toReal
      (f := f) (hf := hf) (hx := hx) (y := y) hrec_top (n + 1)).2

/-- Helper for Proposition 9.30: the directional difference quotient at positive integers is
bounded above by the recession-function value. -/
-- Proof sketch: in the finite branch for the recession value, every one-step translated increment
-- along the ray is bounded by that finite value, so an induction keeps the whole integer ray inside
-- the effective domain and yields the telescoping estimate from the source proof.
private theorem integer_directionalDifferenceQuotient_le_recessionFunction
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    {x : H} (hx : x ∈ effectiveDomain f) (y : H) (n : ℕ) :
    directionalDifferenceQuotient f x y
      ⟨(n + 1 : ℝ), by
        change (0 : ℝ) < (n + 1 : ℝ)
        exact_mod_cast Nat.succ_pos n⟩ ≤
      (recessionFunction f hf.2.nonempty y : EReal) := by
  let a : Set.Ioi (0 : ℝ) :=
    ⟨(n + 1 : ℝ), by
      change (0 : ℝ) < (n + 1 : ℝ)
      exact_mod_cast Nat.succ_pos n⟩
  let r : EReal := (recessionFunction f hf.2.nonempty y : EReal)
  by_cases hrec_top : r = ⊤
  · -- If the recession value is `⊤`, the comparison is immediate.
    have hrec_top' : (recessionFunction f hf.2.nonempty y : EReal) = ⊤ := by
      simpa [r] using hrec_top
    rw [hrec_top']
    exact le_top
  · have hr_bot : r ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < r from by simpa [r] using (recessionFunction f hf.2.nonempty y).2)
    have hrec_top' : (recessionFunction f hf.2.nonempty y : EReal) ≠ ⊤ := by
      simpa [r] using hrec_top
    have hrec_bot' : (recessionFunction f hf.2.nonempty y : EReal) ≠ ⊥ := by
      simpa [r] using hr_bot
    have ha_dom : x + (a : ℝ) • y ∈ effectiveDomain f := by
      -- The integer-ray induction also supplies finiteness of the endpoint.
      simpa [a] using
        (integer_ray_mem_effectiveDomain_and_toReal_sub_le_mul_recession_toReal
          (f := f) (hf := hf) (hx := hx) (y := y) hrec_top' (n + 1)).1
    have hquot :=
      directionalDifferenceQuotient_eq_coe_real_quotient_of_mem_effectiveDomain
        (f := f) (x := x) (y := y) hx a ha_dom
    rw [hquot, ← EReal.coe_toReal hrec_top' hrec_bot']
    apply EReal.coe_le_coe_iff.mpr
    -- Divide the telescoping estimate by the positive integer parameter.
    refine (div_le_iff₀ a.2).2 ?_
    have htel :
        (f (x + (a : ℝ) • y) : EReal).toReal - (f x : EReal).toReal ≤
          (recessionFunction f hf.2.nonempty y : EReal).toReal * (a : ℝ) := by
      simpa [a, mul_comm] using
        (integer_ray_toReal_sub_le_mul_recession_toReal
          (f := f) (hf := hf) (hx := hx) (y := y) hrec_top' n)
    linarith

/-- Helper for Proposition 9.30: every positive-scalar directional difference quotient is bounded
above by the recession-function value. -/
-- Proof sketch: compare an arbitrary positive scalar with the next larger positive integer and use
-- monotonicity of the directional difference quotient together with the integer-ray estimate.
private theorem directionalDifferenceQuotient_le_recessionFunction
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    {x : H} (hx : x ∈ effectiveDomain f) (y : H) (α : Set.Ioi (0 : ℝ)) :
    directionalDifferenceQuotient f x y α ≤
      (recessionFunction f hf.2.nonempty y : EReal) := by
  let n : ℕ := Nat.ceil (α : ℝ)
  let β : Set.Ioi (0 : ℝ) :=
    ⟨((n + 1 : ℕ) : ℝ), by
      show (0 : ℝ) < ((n + 1 : ℕ) : ℝ)
      positivity⟩
  have hαβ : (α : ℝ) ≤ (β : ℝ) := by
    calc
      (α : ℝ) ≤ (n : ℝ) := Nat.le_ceil (α : ℝ)
      _ ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_succ n
  -- Compare first with the larger integer parameter, then invoke the integer-ray bound there.
  exact le_trans
    ((directionalDifferenceQuotient_monotone f hf.2 hx y) hαβ)
    (by
      simpa [β] using
        (integer_directionalDifferenceQuotient_le_recessionFunction
          (f := f) (hf := hf) (hx := hx) (y := y) n))

/-- Helper for Proposition 9.30: if the endpoint `x + β • y` is not in the effective domain, then
the directional difference quotient at `β` is `⊤`. -/
-- Proof sketch: outside the effective domain the endpoint value is exactly `⊤`, so the quotient
-- definition collapses to `⊤` after subtracting the finite base value and dividing by a positive
-- finite scalar.
private theorem directionalDifferenceQuotient_eq_top_of_not_mem_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) {x : H} (hx : x ∈ effectiveDomain f) (y : H)
    (β : Set.Ioi (0 : ℝ)) (hβ : x + (β : ℝ) • y ∉ effectiveDomain f) :
    directionalDifferenceQuotient f x y β = ⊤ := by
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hx)
  have hxy_top : (f (x + (β : ℝ) • y) : EReal) = ⊤ := by
    refine le_antisymm le_top ?_
    exact not_lt.mp (by simpa [mem_effectiveDomain_iff] using hβ)
  have hβ_pos : (0 : EReal) < ((β : ℝ) : EReal) := by
    exact_mod_cast β.2
  have hβ_ne_top : ((β : ℝ) : EReal) ≠ ⊤ := ne_of_lt (EReal.coe_lt_top _)
  -- Unfold the quotient and collapse the non-finite endpoint branch.
  rw [directionalDifferenceQuotient, hxy_top, EReal.top_sub hx_top,
    EReal.top_div_of_pos_ne_top hβ_pos hβ_ne_top]

/-- Helper for Proposition 9.30: on the finite endpoint branch, the source convexity estimate
rewrites directly into the directional-difference-quotient bound. -/
-- Proof sketch: use Jensen convexity for the combination
-- `(1 - 1 / β) • z + (1 / β) • (x + β • y)`, prove that the combination still lies in the
-- effective domain, and then convert both sides to real quotients using `toReal`.
private theorem convex_combination_directionalDifferenceQuotient_bound_of_mem_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    {x : H} (hx : x ∈ effectiveDomain f) {z : H} (hz : z ∈ effectiveDomain f) (y : H)
    {β : ℝ} (hβ : 1 < β) (hxy : x + β • y ∈ effectiveDomain f) :
    ((f ((1 - 1 / β) • z + (1 / β) • (x + β • y)) : EReal) - (f z : EReal)) ≤
      directionalDifferenceQuotient f x y ⟨β, lt_trans zero_lt_one hβ⟩ +
        (((f x : EReal) - (f z : EReal)) / β) := by
  let w : H := (1 - 1 / β) • z + (1 / β) • (x + β • y)
  have hβ_pos : 0 < β := lt_trans zero_lt_one hβ
  have hβ_ne : β ≠ 0 := ne_of_gt hβ_pos
  have hinv_lt_one : (1 / β : ℝ) < 1 := by
    simpa using (one_div_lt_one_div hβ_pos zero_lt_one).2 hβ
  have hcoeff1 : (1 - 1 / β : EReal) = (((1 - 1 / β : ℝ)) : EReal) := by
    norm_num [div_eq_mul_inv, EReal.coe_inv]
  have hcoeff2 : (1 / β : EReal) = (((1 / β : ℝ)) : EReal) := by
    norm_num [div_eq_mul_inv, EReal.coe_inv]
  have hineq :
      (f w : EReal) ≤
        (1 - 1 / β : EReal) * (f z : EReal) +
          (1 / β : EReal) * (f (x + β • y) : EReal) := by
    -- Apply Jensen convexity at the two finite endpoints from the source proof.
    have hineq0 := hf.2.ineq hxy hz (one_div_pos.mpr hβ_pos) hinv_lt_one
    simpa [w, add_comm, add_left_comm, add_assoc, div_eq_mul_inv, hβ_ne, hcoeff1, hcoeff2]
      using hineq0
  have hz_top : (f z : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hz)
  have hz_bot : (f z : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f z : EReal) from (f z).2)
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hxy_top : (f (x + β • y) : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hxy)
  have hxy_bot : (f (x + β • y) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (x + β • y) : EReal) from
      (f (x + β • y)).2)
  have hterm1_ne_top : (1 - 1 / β : EReal) * (f z : EReal) ≠ ⊤ := by
    rw [hcoeff1, ← EReal.coe_toReal hz_top hz_bot, ← EReal.coe_mul]
    exact ne_of_lt (EReal.coe_lt_top _)
  have hterm1_ne_bot : (1 - 1 / β : EReal) * (f z : EReal) ≠ ⊥ := by
    rw [hcoeff1, ← EReal.coe_toReal hz_top hz_bot, ← EReal.coe_mul]
    exact EReal.coe_ne_bot _
  have hterm2_ne_top : (1 / β : EReal) * (f (x + β • y) : EReal) ≠ ⊤ := by
    rw [hcoeff2, ← EReal.coe_toReal hxy_top hxy_bot, ← EReal.coe_mul]
    exact ne_of_lt (EReal.coe_lt_top _)
  have hterm2_ne_bot : (1 / β : EReal) * (f (x + β • y) : EReal) ≠ ⊥ := by
    rw [hcoeff2, ← EReal.coe_toReal hxy_top hxy_bot, ← EReal.coe_mul]
    exact EReal.coe_ne_bot _
  have hsum_ne_top :
      (1 - 1 / β : EReal) * (f z : EReal) + (1 / β : EReal) * (f (x + β • y) : EReal) ≠ ⊤ :=
    EReal.add_ne_top hterm1_ne_top hterm2_ne_top
  have hw_dom : w ∈ effectiveDomain f := by
    -- The convex bound is finite because both endpoints are finite, so the combination is finite.
    rw [mem_effectiveDomain_iff]
    exact lt_of_le_of_lt hineq (lt_of_le_of_ne le_top hsum_ne_top)
  have hw_top : (f w : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hw_dom)
  have hw_bot : (f w : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f w : EReal) from (f w).2)
  have hsum_toReal :
      (((1 - 1 / β : EReal) * (f z : EReal)) +
          (1 / β : EReal) * (f (x + β • y) : EReal)).toReal =
        (1 - 1 / β) * (f z : EReal).toReal +
          (1 / β) * (f (x + β • y) : EReal).toReal := by
    rw [EReal.toReal_add hterm1_ne_top hterm1_ne_bot hterm2_ne_top hterm2_ne_bot,
      EReal.toReal_mul, EReal.toReal_mul, hcoeff1, hcoeff2, EReal.toReal_coe, EReal.toReal_coe]
  have hineq_real :
      (f w : EReal).toReal ≤
        (1 - 1 / β) * (f z : EReal).toReal +
          (1 / β) * (f (x + β • y) : EReal).toReal := by
    have hineq_toReal := EReal.toReal_le_toReal hineq hw_bot hsum_ne_top
    rw [hsum_toReal] at hineq_toReal
    exact hineq_toReal
  have hreal :
      (f w : EReal).toReal - (f z : EReal).toReal ≤
        (((f (x + β • y) : EReal).toReal - (f z : EReal).toReal) / β) := by
    refine (le_div_iff₀ hβ_pos).2 ?_
    have haux' :
        β * (f w : EReal).toReal ≤
          β * ((1 - 1 / β) * (f z : EReal).toReal +
            (1 / β) * (f (x + β • y) : EReal).toReal) := by
      exact mul_le_mul_of_nonneg_left hineq_real hβ_pos.le
    have hmul :
        β * ((f w : EReal).toReal - (f z : EReal).toReal) ≤
          (f (x + β • y) : EReal).toReal - (f z : EReal).toReal := by
      have haux :
          β * (f w : EReal).toReal ≤
            (β - 1) * (f z : EReal).toReal + (f (x + β • y) : EReal).toReal := by
        calc
          β * (f w : EReal).toReal ≤
              β * ((1 - 1 / β) * (f z : EReal).toReal +
                (1 / β) * (f (x + β • y) : EReal).toReal) := haux'
          _ = (β - 1) * (f z : EReal).toReal + (f (x + β • y) : EReal).toReal := by
              field_simp [hβ_ne]
      nlinarith [haux]
    simpa [mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg] using hmul
  have hbase :
      (((f x : EReal) - (f z : EReal)) / β) =
        ((((f x : EReal).toReal - (f z : EReal).toReal) / β : ℝ) : EReal) := by
    rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_toReal hz_top hz_bot,
      ← EReal.coe_sub, ← EReal.coe_div]
    simp
  have hleft :
      ((f w : EReal) - (f z : EReal)) =
        ((((f w : EReal).toReal - (f z : EReal).toReal : ℝ)) : EReal) := by
    rw [← EReal.coe_toReal hw_top hw_bot, ← EReal.coe_toReal hz_top hz_bot, ← EReal.coe_sub]
    simp
  have hright_real :
      (f w : EReal).toReal - (f z : EReal).toReal ≤
        (((f (x + β • y) : EReal).toReal - (f x : EReal).toReal) / β) +
          (((f x : EReal).toReal - (f z : EReal).toReal) / β) := by
    calc
      (f w : EReal).toReal - (f z : EReal).toReal
          ≤ (((f (x + β • y) : EReal).toReal - (f z : EReal).toReal) / β) := hreal
      _ = (((f (x + β • y) : EReal).toReal - (f x : EReal).toReal) / β) +
            (((f x : EReal).toReal - (f z : EReal).toReal) / β) := by
            field_simp [hβ_ne]
            ring
  -- Rewrite both sides as real casts and close the inequality in `ℝ`.
  rw [hleft,
    directionalDifferenceQuotient_eq_coe_real_quotient_of_mem_effectiveDomain
      (f := f) (x := x) (y := y) hx ⟨β, lt_trans zero_lt_one hβ⟩ hxy,
    hbase, ← EReal.coe_add]
  exact EReal.coe_le_coe_iff.mpr hright_real

/-- Helper for Proposition 9.30: the convexity step from the source proof bounds the translated
increment by a directional difference quotient plus the vanishing base-point error. -/
-- Proof sketch: rewrite the translated point as the convex combination from the source proof, use
-- the Jensen inequality on the finite branch for `x + β • y`, and convert the resulting finite
-- `EReal` inequality into the corresponding real quotient estimate.
private theorem translated_increment_le_directionalDifferenceQuotient_add_base_error
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    {x : H} (hx : x ∈ effectiveDomain f) {z : H} (hz : z ∈ effectiveDomain f) (y : H)
    {β : ℝ} (hβ : 1 < β) :
    ((f (z + (y + β⁻¹ • (x - z))) : EReal) - (f z : EReal)) ≤
      directionalDifferenceQuotient f x y ⟨β, lt_trans zero_lt_one hβ⟩ +
        (((f x : EReal) - (f z : EReal)) / β) := by
  by_cases hxy : x + β • y ∈ effectiveDomain f
  · -- On the finite branch, rewrite the translated point into the convex-combination form from
    -- the source proof and use the dedicated Jensen-to-quotient adapter.
    rw [translated_increment_argument_eq x z y (ne_of_gt (lt_trans zero_lt_one hβ))]
    exact
      convex_combination_directionalDifferenceQuotient_bound_of_mem_effectiveDomain
        (f := f) (hf := hf) (hx := hx) (hz := hz) (y := y) hβ hxy
  · have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hz_top : (f z : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hz)
    have hz_bot : (f z : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f z : EReal) from (f z).2)
    have hbase_ne_bot : (((f x : EReal) - (f z : EReal)) / β) ≠ ⊥ := by
      rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_toReal hz_top hz_bot,
        ← EReal.coe_sub, ← EReal.coe_div]
      exact EReal.coe_ne_bot _
    have hdq_top :
        directionalDifferenceQuotient f x y ⟨β, lt_trans zero_lt_one hβ⟩ = ⊤ := by
      exact
        directionalDifferenceQuotient_eq_top_of_not_mem_effectiveDomain
          (f := f) (x := x) hx y ⟨β, lt_trans zero_lt_one hβ⟩ hxy
    -- Outside the effective domain, the quotient side is `⊤`, so the estimate is immediate.
    rw [hdq_top, EReal.top_add_of_ne_bot hbase_ne_bot]
    exact le_top

/-- Helper for Proposition 9.30: every translated increment is bounded by the supremum of the
directional difference quotients. -/
-- Proof sketch: apply the previous convexity bound along the cofinal sequence `βₙ = n + 2`,
-- compare liminfs using lower semicontinuity at `y`, and let the base-point error vanish.
private theorem increment_le_sSup_directionalDifferenceQuotient
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    {x : H} (hx : x ∈ effectiveDomain f) {z : H} (hz : z ∈ effectiveDomain f) (y : H) :
    ((f (z + y) : EReal) - (f z : EReal)) ≤
      sSup (Set.range (directionalDifferenceQuotient f x y)) := by
  let s : EReal := sSup (Set.range (directionalDifferenceQuotient f x y))
  let u : ℕ → H := fun n ↦ y + ((1 / (n + 2 : ℝ)) : ℝ) • (x - z)
  let e : ℕ → EReal := fun n ↦
    (((((f x : EReal).toReal - (f z : EReal).toReal) / (n + 2 : ℝ) : ℝ)) : EReal)
  let g : H → EReal := fun v ↦ (f (z + v) : EReal) - (f z : EReal)
  have hrecip : Filter.Tendsto (fun n : ℕ ↦ (1 / (n + 2 : ℝ))) Filter.atTop
      (nhds (0 : ℝ)) := by
    have hbase :
        Filter.Tendsto (fun n : ℕ ↦ (1 / (n + 1 : ℝ)) : ℕ → ℝ) Filter.atTop
          (nhds (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hshift : Filter.Tendsto (fun n : ℕ ↦ n + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_add_atTop_nat 1
    convert (hbase.comp hshift) using 1
    ext n
    simp [Function.comp]
    ring
  have hu : Filter.Tendsto u Filter.atTop (nhds y) := by
    have hzero :
        Filter.Tendsto (fun n : ℕ ↦ ((1 / (n + 2 : ℝ)) : ℝ) • (x - z)) Filter.atTop
          (nhds ((0 : ℝ) • (x - z))) := by
      simpa [u] using hrecip.smul_const (x - z)
    have hconst : Filter.Tendsto (fun _ : ℕ ↦ y) Filter.atTop (nhds y) := tendsto_const_nhds
    simpa [u] using hconst.add hzero
  have he : Filter.Tendsto e Filter.atTop (nhds (0 : EReal)) := by
    have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hz_top : (f z : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hz)
    have hz_bot : (f z : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f z : EReal) from (f z).2)
    have hreal :
        Filter.Tendsto
          (fun n : ℕ ↦ (((f x : EReal).toReal - (f z : EReal).toReal) / (n + 2 : ℝ) : ℝ))
          Filter.atTop (nhds (0 : ℝ)) := by
      simpa [div_eq_mul_inv, mul_zero] using
        (tendsto_const_nhds.mul hrecip)
    simpa [e] using (EReal.tendsto_coe.2 hreal)
  have hg_liminf :
      g y ≤ Filter.liminf (fun n : ℕ ↦ g (u n)) Filter.atTop := by
    -- Lower semicontinuity transfers the value at `y` to the liminf along the cofinal sequence.
    calc
      g y ≤ Filter.liminf g (nhds y) := (translated_increment_lowerSemicontinuous f hf.1 hz).le_liminf y
      _ ≤ Filter.liminf g (Filter.map u Filter.atTop) := Filter.liminf_le_liminf_of_le hu
      _ = Filter.liminf (fun n : ℕ ↦ g (u n)) Filter.atTop := rfl
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hz_top : (f z : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hz)
  have hz_bot : (f z : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f z : EReal) from (f z).2)
  have hpointwise :
      ∀ n : ℕ, g (u n) ≤ s + e n := by
    intro n
    have hβ_pos : (0 : ℝ) < (n + 2 : ℝ) := by
      positivity
    have hβ : 1 < (n + 2 : ℝ) := by
      nlinarith
    let βn : Set.Ioi (0 : ℝ) := ⟨(n + 2 : ℝ), hβ_pos⟩
    have hstep :=
      translated_increment_le_directionalDifferenceQuotient_add_base_error
        (f := f) (hf := hf) (hx := hx) (hz := hz) (y := y) (β := n + 2) hβ
    have hbase_eq : (((f x : EReal) - (f z : EReal)) / (n + 2 : ℝ)) = e n := by
      dsimp [e]
      rw [show ((f x : EReal) - (f z : EReal)) =
          ((((f x : EReal).toReal - (f z : EReal).toReal : ℝ)) : EReal) by
            rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_toReal hz_top hz_bot,
              ← EReal.coe_sub]
            simp]
      simpa [Nat.cast_add] using
        (EReal.coe_div
          (((f x : EReal).toReal - (f z : EReal).toReal))
          (((n : ℕ) : ℝ) + 2)).symm
    have hs : directionalDifferenceQuotient f x y βn ≤ s := by
      exact le_sSup ⟨βn, rfl⟩
    -- Each fixed-`βₙ` bound is dominated by the supremum because the quotient is itself a range
    -- point of the family.
    rw [hbase_eq] at hstep
    simpa [g, u, s, βn, sub_eq_add_neg] using le_trans hstep (add_le_add hs le_rfl)
  have hlim_le :
      Filter.liminf (fun n : ℕ ↦ g (u n)) Filter.atTop ≤
        Filter.liminf (fun n : ℕ ↦ s + e n) Filter.atTop := by
    exact Filter.liminf_le_liminf (Filter.Eventually.of_forall hpointwise)
  have hs_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ s + e n) Filter.atTop (nhds (s + 0)) := by
    have hadd :
        ContinuousAt (fun p : EReal × EReal ↦ p.1 + p.2) (s, 0) :=
      EReal.continuousAt_add (.inr (EReal.coe_ne_bot 0)) (.inr (EReal.coe_ne_top 0))
    exact hadd.tendsto.comp
      ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ s) Filter.atTop (nhds s)).prodMk_nhds he)
  -- Taking liminfs and using the vanishing error term gives the target translated-increment bound.
  calc
    ((f (z + y) : EReal) - (f z : EReal)) = g y := rfl
    _ ≤ Filter.liminf (fun n : ℕ ↦ g (u n)) Filter.atTop := hg_liminf
    _ ≤ Filter.liminf (fun n : ℕ ↦ s + e n) Filter.atTop := hlim_le
    _ = s + 0 := hs_tendsto.liminf_eq
    _ = s := by simp [s]

/-- Helper for Proposition 9.30: the recession function equals the supremum of the directional
difference quotients once both source inequalities have been established. -/
-- Proof sketch: the reverse inequality follows from the quotient bounds already proved; the only
-- remaining open step is the forward lower-semicontinuity/cofinal-sequence comparison.
private theorem recessionFunction_eq_sSup_directionalDifferenceQuotient_aux
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    {x : H} (hx : x ∈ effectiveDomain f) (y : H) :
    (recessionFunction f hf.2.nonempty y : EReal) =
      sSup (Set.range (directionalDifferenceQuotient f x y)) := by
  apply le_antisymm
  · -- Route correction: the forward inequality now comes from the lower-semicontinuity/cofinal
    -- sequence argument, applied pointwise to every translated increment in the defining supremum.
    rw [recessionFunction_eq_iSup_effectiveDomain_increment]
    refine iSup_le ?_
    intro z
    -- Each translated increment in the defining supremum is bounded by the common quotient
    -- supremum, so the indexed supremum is as well.
    exact increment_le_sSup_directionalDifferenceQuotient
      (f := f) (hf := hf) (hx := hx) (hz := z.2) y
  · -- The reverse inequality is now reduced to the all-positive-scalar quotient bound.
    rw [sSup_le_iff]
    intro z hz
    rcases hz with ⟨α, rfl⟩
    exact directionalDifferenceQuotient_le_recessionFunction (f := f) (hf := hf) (hx := hx) y α


/-- Proposition 9.30 (2): clause (ii). The recession function is the limit at `+∞` of the
directional difference quotient along the ray `x + α • y`. -/
-- Proof sketch: use the monotonicity of `directionalDifferenceQuotient` from Proposition 9.27 and
-- identify the limit with the recession-function value via the defining supremum.
theorem tendsto_directionalDifferenceQuotient_to_recessionFunction
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    {x : H} (hx : x ∈ effectiveDomain f) (y : H) :
    Filter.Tendsto (directionalDifferenceQuotient f x y) Filter.atTop
      (nhds ((recessionFunction f hf.2.nonempty y : EReal))) := by
  -- Once clause (iv) identifies the limit point, the monotone-convergence statement from
  -- Proposition 9.27 transports directly to the recession-function value.
  rw [recessionFunction_eq_sSup_directionalDifferenceQuotient_aux
    (f := f) (hf := hf) (hx := hx) y]
  exact tendsto_directionalDifferenceQuotient_to_sSup (f := f) (hf := hf) (hx := hx) y

/-- Proposition 9.30 (3): clause (iii). The recession function is also the limit at `+∞` of the
scaled values `f (x + α • y) / α`. -/
-- Proof sketch: rewrite the scaled values as the directional difference quotient plus the constant
-- term `f x / α`, then combine clause (ii) with the fact that `f x / α → 0` as `α → +∞`.
theorem tendsto_scaled_ray_values_to_recessionFunction
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    {x : H} (hx : x ∈ effectiveDomain f) (y : H) :
    Filter.Tendsto
      (fun α : Set.Ioi (0 : ℝ) ↦ (f (x + (α : ℝ) • y) : EReal) / (α : ℝ))
      Filter.atTop (nhds ((recessionFunction f hf.2.nonempty y : EReal))) := by
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff).mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hbase :
      Filter.Tendsto (fun α : Set.Ioi (0 : ℝ) ↦ (f x : EReal) / (α : ℝ))
        Filter.atTop (nhds (0 : EReal)) := by
    -- The fixed base-point term is a finite real cast divided by `α`, so it vanishes at `+∞`.
    simpa [EReal.coe_toReal hx_top hx_bot] using
      ereal_coe_div_tendsto_zero_atTop ((f x : EReal).toReal)
  have hsum :
      Filter.Tendsto
        (fun α : Set.Ioi (0 : ℝ) ↦
          directionalDifferenceQuotient f x y α + (f x : EReal) / (α : ℝ))
        Filter.atTop
        (nhds (((recessionFunction f hf.2.nonempty y : EReal)) + 0)) := by
    have hadd :
        ContinuousAt (fun p : EReal × EReal ↦ p.1 + p.2)
          (((recessionFunction f hf.2.nonempty y : EReal), 0)) :=
      EReal.continuousAt_add (.inr (EReal.coe_ne_bot 0)) (.inr (EReal.coe_ne_top 0))
    -- Clause (ii) controls the quotient part, and the base-point correction tends to zero.
    exact hadd.tendsto.comp
      ((tendsto_directionalDifferenceQuotient_to_recessionFunction
        (f := f) (hf := hf) (hx := hx) y).prodMk_nhds hbase)
  -- Rewrite the scaled ray into the quotient-plus-error form from the source proof.
  rw [funext (fun α : Set.Ioi (0 : ℝ) ↦
    scaled_ray_value_eq_directionalDifferenceQuotient_add_base_div
      (f := f) (hx := hx) y α)]
  simpa using hsum

/-- Proposition 9.30 (4): clause (iv). The recession function equals the supremum of the
directional difference quotient over positive scalars. -/
-- Proof sketch: apply clause (ii) together with the monotonicity of the directional difference
-- quotient, so its limit at `+∞` coincides with the supremum of its range.
theorem recessionFunction_eq_sSup_directionalDifferenceQuotient
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    {x : H} (hx : x ∈ effectiveDomain f) (y : H) :
    (recessionFunction f hf.2.nonempty y : EReal) =
      sSup (Set.range (directionalDifferenceQuotient f x y)) := by
  -- Expose the earlier auxiliary as the public clause-(iv) statement.
  simpa using
    recessionFunction_eq_sSup_directionalDifferenceQuotient_aux
      (f := f) (hf := hf) (hx := hx) y

/-- Proposition 9.30 (5): clause (v). If `f` is bounded below, then its recession function is
pointwise nonnegative. -/
-- Proof sketch: use clause (iii) and compare `f (x + α • y) / α` with a lower bound divided by
-- `α`, whose limit at `+∞` is `0`.
theorem recessionFunction_nonneg_of_bddBelow
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (hbounded : ∃ m : ℝ, ∀ z : H, (m : EReal) ≤ (f z : EReal)) :
    ∀ y : H, 0 ≤ (recessionFunction f hf.2.nonempty y : EReal) := by
  rcases hf.2.nonempty with ⟨x, hx⟩
  rcases hbounded with ⟨m, hm⟩
  intro y
  have hleft :
      Filter.Tendsto (fun α : Set.Ioi (0 : ℝ) ↦ ((m : EReal) / (α : ℝ)))
        Filter.atTop (nhds (0 : EReal)) :=
    ereal_coe_div_tendsto_zero_atTop m
  have hright :
      Filter.Tendsto
        (fun α : Set.Ioi (0 : ℝ) ↦ (f (x + (α : ℝ) • y) : EReal) / (α : ℝ))
        Filter.atTop
        (nhds ((recessionFunction f hf.2.nonempty y : EReal))) :=
    tendsto_scaled_ray_values_to_recessionFunction (f := f) (hf := hf) (hx := hx) y
  have hpointwise :
      ∀ α : Set.Ioi (0 : ℝ),
        ((m : EReal) / (α : ℝ)) ≤ (f (x + (α : ℝ) • y) : EReal) / (α : ℝ) := by
    intro α
    have hα_pos : (0 : EReal) < ((α : ℝ) : EReal) := by
      exact_mod_cast α.2
    have hα_ne_top : ((α : ℝ) : EReal) ≠ ⊤ := ne_of_lt (EReal.coe_lt_top _)
    have hα_ne_bot : ((α : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
    have hα_ne_zero : ((α : ℝ) : EReal) ≠ 0 := by
      exact_mod_cast (ne_of_gt α.2)
    rw [EReal.le_div_iff_mul_le hα_pos hα_ne_top]
    rw [EReal.div_mul_cancel (a := (m : EReal)) hα_ne_bot hα_ne_top hα_ne_zero]
    exact hm _
  exact le_of_tendsto_of_tendsto' hleft hright hpointwise

/-- Proposition 9.30 (6): clause (vi). When the effective domains of `f` and `g` meet, the
recession function of `f + g` is the pointwise sum of the recession functions. -/
-- Proof sketch: evaluate both sides by clause (iii) at a common effective-domain point, then use
-- pointwise additivity of the scaled ray values before passing to the limit.
theorem recessionFunction_add
    (f g : H → Set.Ioi (⊥ : EReal))
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    (fun y : H ↦
      (recessionFunction (pointwiseAdd f g)
        (effectiveDomain_add_nonempty_of_inter_nonempty f g hdom) y :
        EReal)) =
      fun y : H ↦
        (recessionFunction f hf.2.nonempty y : EReal) +
          (recessionFunction g hg.2.nonempty y : EReal) := by
  rcases hdom with ⟨x, hx, hxg⟩
  have hsum_mem : pointwiseAdd f g ∈ Γ₀(H) :=
    pointwiseAdd_mem_gammaZero f g hf hg ⟨x, hx, hxg⟩
  have hx_sum : x ∈ effectiveDomain (pointwiseAdd f g) := by
    exact (mem_effectiveDomain_pointwiseAdd_iff f g x).2 ⟨hx, hxg⟩
  funext y
  have hleft :
      Filter.Tendsto
        (fun α : Set.Ioi (0 : ℝ) ↦
          (pointwiseAdd f g (x + (α : ℝ) • y) : EReal) / (α : ℝ))
        Filter.atTop
        (nhds
          ((recessionFunction (pointwiseAdd f g)
            (effectiveDomain_add_nonempty_of_inter_nonempty f g ⟨x, hx, hxg⟩) y :
            EReal))) := by
    -- Clause (iii) applied to `f + g` gives the left-hand limit.
    exact
      tendsto_scaled_ray_values_to_recessionFunction
        (f := pointwiseAdd f g) (hf := hsum_mem) (hx := hx_sum) y
  have hright :
      Filter.Tendsto
        (fun α : Set.Ioi (0 : ℝ) ↦
          (f (x + (α : ℝ) • y) : EReal) / (α : ℝ) +
            (g (x + (α : ℝ) • y) : EReal) / (α : ℝ))
        Filter.atTop
        (nhds
          ((recessionFunction f hf.2.nonempty y : EReal) +
            (recessionFunction g hg.2.nonempty y : EReal))) := by
    have hrec_f_bot : (recessionFunction f hf.2.nonempty y : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (recessionFunction f hf.2.nonempty y : EReal) from
        (recessionFunction f hf.2.nonempty y).2)
    have hrec_g_bot : (recessionFunction g hg.2.nonempty y : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (recessionFunction g hg.2.nonempty y : EReal) from
        (recessionFunction g hg.2.nonempty y).2)
    have hadd :
        ContinuousAt (fun p : EReal × EReal ↦ p.1 + p.2)
          (((recessionFunction f hf.2.nonempty y : EReal),
            (recessionFunction g hg.2.nonempty y : EReal))) :=
      EReal.continuousAt_add (.inr hrec_g_bot) (.inl hrec_f_bot)
    -- Clause (iii) for each summand identifies the sum limit, and addition is continuous here.
    exact hadd.tendsto.comp <|
      ((tendsto_scaled_ray_values_to_recessionFunction
          (f := f) (hf := hf) (hx := hx) y).prodMk_nhds
        (tendsto_scaled_ray_values_to_recessionFunction
          (f := g) (hf := hg) (hx := hxg) y))
  have hleft' :
      Filter.Tendsto
        (fun α : Set.Ioi (0 : ℝ) ↦
          (pointwiseAdd f g (x + (α : ℝ) • y) : EReal) / (α : ℝ))
        Filter.atTop
        (nhds
          ((recessionFunction f hf.2.nonempty y : EReal) +
            (recessionFunction g hg.2.nonempty y : EReal))) := by
    -- The scaled ray of `f + g` is pointwise the sum of the scaled rays of `f` and `g`.
    have hEq :
        (fun α : Set.Ioi (0 : ℝ) ↦
          (pointwiseAdd f g (x + (α : ℝ) • y) : EReal) / (α : ℝ)) =
          fun α : Set.Ioi (0 : ℝ) ↦
            (f (x + (α : ℝ) • y) : EReal) / (α : ℝ) +
              (g (x + (α : ℝ) • y) : EReal) / (α : ℝ) := by
      funext α
      simp [pointwiseAdd_apply]
      have hα_nonneg : (0 : EReal) ≤ ((α : ℝ) : EReal) := by
        exact_mod_cast α.2.le
      simpa using
        (EReal.add_div_of_nonneg_right
          (a := (f (x + (α : ℝ) • y) : EReal))
          (b := (g (x + (α : ℝ) • y) : EReal))
          (c := ((α : ℝ) : EReal)) hα_nonneg)
    rw [hEq]
    exact hright
  exact tendsto_nhds_unique hleft hleft'

end Linear

section ContinuousLinear

variable {H : Type u} {K : Type v}
variable [SeminormedAddCommGroup H] [NormedSpace ℝ H]
variable [SeminormedAddCommGroup K] [NormedSpace ℝ K]

/-- If the range of `L` meets the effective domain of `g`, then the effective domain of `g ∘ L` is
nonempty. -/
-- Proof sketch: choose `x` with `L x` in the effective domain of `g`; then `x` lies in the
-- effective domain of the composite.
theorem effectiveDomain_comp_nonempty_of_range_inter_nonempty
    (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K)
    (hdom : (Set.range L ∩ effectiveDomain g).Nonempty) :
    (effectiveDomain (g ∘ L)).Nonempty := by
  rcases hdom with ⟨y, hy_range, hy_dom⟩
  rcases hy_range with ⟨x, rfl⟩
  -- A range point of `L` lying in the effective domain of `g` pulls back to a domain point.
  refine ⟨x, ?_⟩
  simpa [mem_effectiveDomain_iff] using hy_dom

/-- Helper for Proposition 9.30: precomposing a `Γ₀(K)` function with a continuous linear map
preserves membership in `Γ₀(H)` when the composite has nonempty effective domain. -/
-- Proof sketch: lower semicontinuity is preserved by composition with the continuous map `L`, and
-- Jensen convexity is preserved because `L` respects affine combinations.
private theorem comp_continuousLinearMap_mem_gammaZero
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K) (hdom : (Set.range L ∩ effectiveDomain g).Nonempty) :
    g ∘ L ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff]
  refine ⟨?_, ?_⟩
  · -- Lower semicontinuity is stable under composition with the continuous linear map.
    simpa using hg.1.comp L.continuous
  · -- The effective domain is nonempty by the range-intersection hypothesis, and Jensen's
    -- inequality transports through linearity of `L`.
    refine ⟨effectiveDomain_comp_nonempty_of_range_inter_nonempty g L hdom, subset_rfl, ?_⟩
    intro x hx y hy α hα hα_lt_one
    have hx' : L x ∈ effectiveDomain g := by
      simpa [mem_effectiveDomain_iff] using hx
    have hy' : L y ∈ effectiveDomain g := by
      simpa [mem_effectiveDomain_iff] using hy
    simpa [Function.comp, map_add, map_smul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using hg.2.ineq hx' hy' hα hα_lt_one

/-- Proposition 9.30 (7): clause (vii). Composing with a continuous linear map commutes with the
recession function when the range of the map meets the effective domain. -/
-- Proof sketch: apply clause (iii) to `g ∘ L`, rewrite `L (x + α • y)` as `L x + α • L y`, and
-- identify the resulting limit with the recession function of `g` evaluated at `L y`.
theorem recessionFunction_comp_continuousLinearMap
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K) (hdom : (Set.range L ∩ effectiveDomain g).Nonempty) :
    (fun y : H ↦
      (recessionFunction (g ∘ L)
        (effectiveDomain_comp_nonempty_of_range_inter_nonempty g L hdom) y : EReal)) =
      fun y : H ↦ (recessionFunction g hg.2.nonempty (L y) : EReal) := by
  funext y
  have hdom' := hdom
  rcases hdom with ⟨z, hz_range, hz_dom⟩
  rcases hz_range with ⟨x, rfl⟩
  have hcomp_mem : g ∘ L ∈ Γ₀(H) :=
    comp_continuousLinearMap_mem_gammaZero g hg L hdom'
  have hx_comp : x ∈ effectiveDomain (g ∘ L) := by
    simpa [Function.comp, mem_effectiveDomain_iff] using hz_dom
  have hleft :
      Filter.Tendsto
        (fun α : Set.Ioi (0 : ℝ) ↦ ((g ∘ L) (x + (α : ℝ) • y) : EReal) / (α : ℝ))
        Filter.atTop
        (nhds
          ((recessionFunction (g ∘ L)
            (effectiveDomain_comp_nonempty_of_range_inter_nonempty g L hdom') y : EReal))) := by
    -- Clause (iii) applied to the composite gives the left-hand limit.
    exact
      tendsto_scaled_ray_values_to_recessionFunction
        (f := g ∘ L) (hf := hcomp_mem) (hx := hx_comp) y
  have hright :
      Filter.Tendsto
        (fun α : Set.Ioi (0 : ℝ) ↦ (g (L x + (α : ℝ) • L y) : EReal) / (α : ℝ))
        Filter.atTop
        (nhds ((recessionFunction g hg.2.nonempty (L y) : EReal))) := by
    -- Clause (iii) applied to `g` at the point `L x` gives the right-hand limit.
    exact
      tendsto_scaled_ray_values_to_recessionFunction
        (f := g) (hf := hg) (hx := hz_dom) (y := L y)
  have hleft' :
      Filter.Tendsto
        (fun α : Set.Ioi (0 : ℝ) ↦ (g (L x + (α : ℝ) • L y) : EReal) / (α : ℝ))
        Filter.atTop
        (nhds
          ((recessionFunction (g ∘ L)
            (effectiveDomain_comp_nonempty_of_range_inter_nonempty g L hdom') y : EReal))) := by
    -- The scaled-ray functions coincide pointwise after rewriting through linearity of `L`.
    simpa [Function.comp, map_add, map_smul] using hleft
  exact tendsto_nhds_unique hleft' hright

end ContinuousLinear

end ERealFunction

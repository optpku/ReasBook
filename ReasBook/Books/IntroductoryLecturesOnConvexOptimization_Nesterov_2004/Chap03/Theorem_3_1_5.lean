/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped WithTopConvexAnalysis

variable {X : Type u} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

/- Theorem 3.1.5 records the textbook closure rules for extended-real-valued functions on
feasible sets.

Semantic recall:
- `ClosedConvexOn` from `Definition_3_1_1_5`
- mathlib `ConvexOn.smul`
- mathlib `ConvexOn.add`
- mathlib `ConvexOn.sup`
- mathlib `LowerSemicontinuousOn.add`
- mathlib `LowerSemicontinuousOn.sup`
- mathlib `lowerSemicontinuousOn_iff_isClosed_epigraph`

Source alignment note:
- part (1) is recorded on the textbook convexity / lower-semicontinuity bridge surface over the
  stated feasible set, because the stronger owner `ClosedConvexOn` is not preserved by zero
  scaling on nonclosed feasible sets;
- parts (2) and (3) remain on the chapter owner surface `ClosedConvexOn` over the stated
  intersection feasible set;
- the stronger owner-level scaling variant therefore remains only as the auxiliary theorem
  `ClosedConvexOn.nonneg_smul_of_isClosed`.
-/

namespace ClosedConvexOn

-- Semantic recall: mathlib provides `ConvexOn.smul`, `ConvexOn.add`, and `ConvexOn.sup` for the
-- convexity half of these closure rules, while the chapter owner `ClosedConvexOn` packages the
-- feasible-domain and constrained-epigraph closedness data.

/-
Theorem 3.1.5 is represented below by three source-facing clause theorems. Nonnegative scaling
uses the textbook bridge surface `ConvexOn ∧ LowerSemicontinuousOn`, because the current chapter
owner `ClosedConvexOn` is strictly stronger than the textbook notion at `β = 0`; the addition and
pointwise-maximum clauses stay on the chapter owner over the intersection feasible set.
-/

/-- Helper for Theorem 3.1.5: the finite real part of a `ClosedConvexOn` function is lower
semicontinuous on its feasible set. -/
theorem lowerSemicontinuousOn_withTopRealPart
    {Q : Set X} {f : X → WithTop ℝ} (hf : ClosedConvexOn Q f) :
    LowerSemicontinuousOn (withTopRealPart f) Q := by
  -- Restrict to the subtype `Q`, where the owner epigraph becomes an ordinary epigraph.
  rw [← lowerSemicontinuous_restrict_iff]
  refine (lowerSemicontinuous_iff_isClosed_epigraph).2 ?_
  let embedding : Q × ℝ → X × ℝ := fun p ↦ ((p.1 : X), p.2)
  have hEmbedding : Continuous embedding := by
    continuity
  -- Compare the subtype epigraph directly with the pulled-back constrained epigraph.
  convert hf.isClosed_constrainedEpigraph.preimage hEmbedding using 1
  ext p
  constructor
  · intro hp
    exact ⟨p.1.2, (withTopRealPart_le_iff (hf.subset_withTopEffectiveDomain p.1.2)).1 hp⟩
  · intro hp
    exact (withTopRealPart_le_iff (hf.subset_withTopEffectiveDomain p.1.2)).2 hp.2

/-- Helper for Theorem 3.1.5: scalar multiplication commutes with taking the finite real part. -/
theorem withTopRealPart_smul_of_mem_feasible
    {f : X → WithTop ℝ} {β : ℝ} {x : X} :
    withTopRealPart (((β : WithTop ℝ) • f)) x = β * withTopRealPart f x := by
  -- `withTopRealPart` is defined via `untop₀`, and `untop₀_mul` records the exact interaction
  -- with multiplication by a finite scalar.
  rw [withTopRealPart]
  simp [Function.comp, Pi.smul_apply, smul_eq_mul, WithTop.untop₀_mul]

/-- Helper for Theorem 3.1.5: on the common feasible set, addition commutes with taking the
finite real part. -/
theorem withTopRealPart_add_of_mem_inter
    {Q₁ Q₂ : Set X} {f₁ f₂ : X → WithTop ℝ} {x : X}
    (hf₁ : ClosedConvexOn Q₁ f₁) (hf₂ : ClosedConvexOn Q₂ f₂) (hx : x ∈ Q₁ ∩ Q₂) :
    withTopRealPart (f₁ + f₂) x = withTopRealPart f₁ x + withTopRealPart f₂ x := by
  have hx₁ : x ∈ dom f₁ := hf₁.subset_withTopEffectiveDomain hx.1
  have hx₂ : x ∈ dom f₂ := hf₂.subset_withTopEffectiveDomain hx.2
  -- On the common feasible set, both summands are finite, so the pointwise `WithTop` sum is the
  -- ordinary real sum.
  rw [withTopRealPart]
  simpa [Function.comp, Pi.add_apply] using
    (WithTop.untop₀_add (ne_of_lt hx₁) (ne_of_lt hx₂))

/-- Helper for Theorem 3.1.5: the constrained epigraph of the pointwise maximum is the
intersection of the constrained epigraphs. -/
theorem constrainedEpigraph_sup_eq_inter
    {Q₁ Q₂ : Set X} {f₁ f₂ : X → WithTop ℝ} :
    constrainedEpigraph (Q₁ ∩ Q₂) (f₁ ⊔ f₂) =
      constrainedEpigraph Q₁ f₁ ∩ constrainedEpigraph Q₂ f₂ := by
  ext p
  constructor
  · rintro ⟨hpQ, hpSup⟩
    refine ⟨?_, ?_⟩
    · exact ⟨hpQ.1, le_trans le_sup_left hpSup⟩
    · exact ⟨hpQ.2, le_trans le_sup_right hpSup⟩
  · rintro ⟨hp₁, hp₂⟩
    exact ⟨⟨hp₁.1, hp₂.1⟩, sup_le_iff.2 ⟨hp₁.2, hp₂.2⟩⟩

section
-- The extension helpers use membership tests on arbitrary sets, so we install the standard
-- classical decidability instance locally within this helper block.
local instance decidableMemSet (Q : Set X) : DecidablePred (fun x => x ∈ Q) :=
  Classical.decPred _

/-- Helper for Theorem 3.1.5: extend `f` to an `EReal`-valued function by keeping its value on
`Q` and setting it to `⊤` outside `Q`. -/
abbrev constrainedERealExtension (Q : Set X) (f : X → WithTop ℝ) : X → EReal :=
  fun x ↦ if x ∈ Q then withTopToEReal (f x) else ⊤

/-- Helper for Theorem 3.1.5: on the effective domain, the `EReal` image of `f` is the coercion
of its finite real part. -/
theorem withTopRealPart_toEReal_eq_of_mem_dom
    {f : X → WithTop ℝ} {x : X} (hx : x ∈ dom f) :
    ((withTopRealPart f x : ℝ) : EReal) = withTopToEReal (f x) := by
  -- Read the finite `WithTop ℝ` value through `coe_withTopRealPart` and then coerce to `EReal`.
  rw [← coe_withTopRealPart (f := f) hx]
  rfl

/-- Helper for Theorem 3.1.5: the global `EReal` extension never takes the value `⊥`. -/
theorem constrainedERealExtension_ne_bot
    {Q : Set X} {f : X → WithTop ℝ} {x : X} :
    constrainedERealExtension Q f x ≠ ⊥ := by
  -- Both branches avoid `⊥`: the in-domain branch is an image of `WithTop ℝ`, and the
  -- off-domain branch is explicitly `⊤`.
  by_cases hx : x ∈ Q
  · rw [constrainedERealExtension, if_pos hx]
    intro h
    cases h
  · rw [constrainedERealExtension, if_neg hx]
    simp

/-- Helper for Theorem 3.1.5: the real slice of the global `EReal` extension is the pullback of
the constrained epigraph at that real height. -/
theorem constrainedERealExtension_preimage_Iic_real
    {Q : Set X} {f : X → WithTop ℝ} {r : ℝ} :
    {x | constrainedERealExtension Q f x ≤ (r : EReal)} =
      (fun x ↦ (x, r)) ⁻¹' constrainedEpigraph Q f := by
  -- Split on membership in `Q`; outside `Q` the extension is `⊤`, while on `Q` the comparison is
  -- exactly the original epigraph inequality at height `r`.
  ext x
  by_cases hx : x ∈ Q
  · unfold constrainedERealExtension
    simp only [Set.mem_setOf_eq, Set.preimage_setOf_eq, constrainedEpigraph, hx, if_true]
    constructor
    · intro h
      exact ⟨trivial, WithBot.coe_le_coe.mp h⟩
    · intro h
      exact WithBot.coe_le_coe.mpr h.2
  · unfold constrainedERealExtension
    simp [constrainedEpigraph, hx]

/-- Helper for Theorem 3.1.5: closedness of the constrained epigraph gives global lower
semicontinuity of the `⊤`-extension in `EReal`. -/
theorem constrainedERealExtension_lowerSemicontinuous
    {Q : Set X} {f : X → WithTop ℝ} (hf : ClosedConvexOn Q f) :
    LowerSemicontinuous (constrainedERealExtension Q f) := by
  -- Read lower semicontinuity through closed sublevel preimages and handle the three `EReal`
  -- height regimes separately: `⊥`, a finite real level, and `⊤`.
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro y
  rcases eq_or_ne y ⊤ with rfl | hyTop
  · simp
  rcases eq_or_ne y ⊥ with rfl | hyBot
  · have hEmpty : constrainedERealExtension Q f ⁻¹' Set.Iic (⊥ : EReal) = ∅ := by
      ext x
      simp [Set.preimage, constrainedERealExtension_ne_bot]
    rw [hEmpty]
    exact isClosed_empty
  · lift y to ℝ using ⟨hyTop, hyBot⟩
    -- Finite real slices are exactly pullbacks of the original constrained epigraph.
    have hCont : Continuous (fun x : X ↦ (x, y)) := by
      continuity
    change IsClosed {x | constrainedERealExtension Q f x ≤ (y : EReal)}
    rw [constrainedERealExtension_preimage_Iic_real (Q := Q) (f := f) (r := y)]
    exact hf.isClosed_constrainedEpigraph.preimage hCont

/-- Helper for Theorem 3.1.5: on the common feasible set, the sum of the two `EReal` extensions
is the `EReal` image of the original `WithTop` sum. -/
theorem constrainedERealExtension_sum_eq_of_mem_inter
    {Q₁ Q₂ : Set X} {f₁ f₂ : X → WithTop ℝ} (hf₁ : ClosedConvexOn Q₁ f₁)
    (hf₂ : ClosedConvexOn Q₂ f₂) {x : X} (hx : x ∈ Q₁ ∩ Q₂) :
    constrainedERealExtension Q₁ f₁ x + constrainedERealExtension Q₂ f₂ x =
      withTopToEReal ((f₁ + f₂) x) := by
  have hx₁ : x ∈ dom f₁ := hf₁.subset_withTopEffectiveDomain hx.1
  have hx₂ : x ∈ dom f₂ := hf₂.subset_withTopEffectiveDomain hx.2
  have hxAdd : x ∈ dom (f₁ + f₂) := by
    -- The common feasible set keeps both summands finite, hence also their pointwise sum.
    rw [mem_withTopEffectiveDomain_iff, Pi.add_apply]
    simpa [WithTop.add_lt_top] using And.intro hx₁ hx₂
  -- Rewrite both extensions to their finite real parts and use the already-proved real-part sum
  -- identity on the intersection.
  calc
    constrainedERealExtension Q₁ f₁ x + constrainedERealExtension Q₂ f₂ x
        = ((withTopRealPart f₁ x : ℝ) : EReal) + ((withTopRealPart f₂ x : ℝ) : EReal) := by
            have h₁ :
                constrainedERealExtension Q₁ f₁ x = ((withTopRealPart f₁ x : ℝ) : EReal) := by
              rw [constrainedERealExtension, if_pos hx.1]
              exact (withTopRealPart_toEReal_eq_of_mem_dom (f := f₁) hx₁).symm
            have h₂ :
                constrainedERealExtension Q₂ f₂ x = ((withTopRealPart f₂ x : ℝ) : EReal) := by
              rw [constrainedERealExtension, if_pos hx.2]
              exact (withTopRealPart_toEReal_eq_of_mem_dom (f := f₂) hx₂).symm
            rw [h₁, h₂]
    _ = (((withTopRealPart f₁ x + withTopRealPart f₂ x : ℝ) : ℝ) : EReal) := by
      rw [EReal.coe_add]
    _ = ((withTopRealPart (f₁ + f₂) x : ℝ) : EReal) := by
      rw [← withTopRealPart_add_of_mem_inter (hf₁ := hf₁) (hf₂ := hf₂) (x := x) hx]
    _ = withTopToEReal ((f₁ + f₂) x) := by
      exact withTopRealPart_toEReal_eq_of_mem_dom (f := f₁ + f₂) hxAdd

/-- Helper for Theorem 3.1.5: the constrained epigraph of the sum is closed on
`Q₁ ∩ Q₂`. -/
theorem isClosed_constrainedEpigraph_add_inter
    {Q₁ Q₂ : Set X} {f₁ f₂ : X → WithTop ℝ} (hf₁ : ClosedConvexOn Q₁ f₁)
    (hf₂ : ClosedConvexOn Q₂ f₂) :
    IsClosed (constrainedEpigraph (Q₁ ∩ Q₂) (f₁ + f₂)) := by
  let g₁ := constrainedERealExtension Q₁ f₁
  let g₂ := constrainedERealExtension Q₂ f₂
  have hAddDom : (Q₁ ∩ Q₂) ⊆ dom (f₁ + f₂) := by
    intro x hx
    have hx₁ : x ∈ dom f₁ := hf₁.subset_withTopEffectiveDomain hx.1
    have hx₂ : x ∈ dom f₂ := hf₂.subset_withTopEffectiveDomain hx.2
    -- Feasible points for both summands keep the pointwise sum finite.
    rw [mem_withTopEffectiveDomain_iff, Pi.add_apply]
    simpa [WithTop.add_lt_top] using And.intro hx₁ hx₂
  have hLsc₁ : LowerSemicontinuous g₁ :=
    constrainedERealExtension_lowerSemicontinuous (Q := Q₁) (f := f₁) hf₁
  have hLsc₂ : LowerSemicontinuous g₂ :=
    constrainedERealExtension_lowerSemicontinuous (Q := Q₂) (f := f₂) hf₂
  have hSumLsc : LowerSemicontinuous (fun x ↦ g₁ x + g₂ x) := by
    -- The sum is lower semicontinuous because both extensions avoid `⊥`, exactly the side
    -- condition needed for continuity of `EReal` addition at each point.
    refine hLsc₁.add' hLsc₂ ?_
    intro x
    refine EReal.continuousAt_add (p := (g₁ x, g₂ x)) ?_ ?_
    · right
      simpa [g₂] using
        (constrainedERealExtension_ne_bot (Q := Q₂) (f := f₂) (x := x))
    · left
      simpa [g₁] using
        (constrainedERealExtension_ne_bot (Q := Q₁) (f := f₁) (x := x))
  have hClosedLift : IsClosed {p : X × ℝ | g₁ p.1 + g₂ p.1 ≤ (p.2 : EReal)} := by
    -- Pull the closed `EReal` epigraph back along the continuous real-to-`EReal` height map.
    have hCont : Continuous (fun p : X × ℝ ↦ (p.1, (p.2 : EReal))) := by
      exact Continuous.prodMk continuous_fst (continuous_coe_real_ereal.comp continuous_snd)
    simpa using
      (hSumLsc.isClosed_epigraph.preimage hCont)
  -- Route correction: the subtype epigraph route only gives closedness inside
  -- `(Q₁ ∩ Q₂) × ℝ`; the global `EReal` extension yields an ambient closed epigraph directly.
  convert hClosedLift using 1
  rw [constrainedEpigraph_eq_epigraph_withTopRealPart hAddDom]
  ext p
  by_cases hp₁ : p.1 ∈ Q₁
  · by_cases hp₂ : p.1 ∈ Q₂
    · have hsum :
          g₁ p.1 + g₂ p.1 = withTopToEReal ((f₁ + f₂) p.1) := by
        simpa [g₁, g₂] using
          constrainedERealExtension_sum_eq_of_mem_inter
            (hf₁ := hf₁) (hf₂ := hf₂) (x := p.1) ⟨hp₁, hp₂⟩
      have hpAdd : p.1 ∈ dom (f₁ + f₂) := hAddDom ⟨hp₁, hp₂⟩
      have hreal :
          g₁ p.1 + g₂ p.1 = ((withTopRealPart (f₁ + f₂) p.1 : ℝ) : EReal) := by
        rw [hsum]
        exact (withTopRealPart_toEReal_eq_of_mem_dom (f := f₁ + f₂) hpAdd).symm
      -- On the common feasible set, the lifted sum is exactly the original sum.
      simp [hp₁, hp₂, hreal]
    · have hg₁_neBot : g₁ p.1 ≠ ⊥ := by
        simpa [g₁] using
          (constrainedERealExtension_ne_bot (Q := Q₁) (f := f₁) (x := p.1))
      have hg₂_top : g₂ p.1 = ⊤ := by
        unfold g₂ constrainedERealExtension
        simp [hp₂]
      have htop : g₁ p.1 + g₂ p.1 = ⊤ := by
        rw [hg₂_top]
        exact EReal.add_top_of_ne_bot hg₁_neBot
      -- If `p.1 ∉ Q₂`, the second extension is `⊤`, so the lifted inequality to a real height
      -- is impossible.
      simp [hp₁, hp₂, htop]
  · by_cases hp₂ : p.1 ∈ Q₂
    · have hg₂_neBot : g₂ p.1 ≠ ⊥ := by
        simpa [g₂] using
          (constrainedERealExtension_ne_bot (Q := Q₂) (f := f₂) (x := p.1))
      have hg₁_top : g₁ p.1 = ⊤ := by
        unfold g₁ constrainedERealExtension
        simp [hp₁]
      have htop : g₁ p.1 + g₂ p.1 = ⊤ := by
        rw [hg₁_top]
        exact EReal.top_add_of_ne_bot hg₂_neBot
      -- Symmetrically, if `p.1 ∉ Q₁`, the first extension is `⊤`, so the inequality is
      -- impossible at a real height.
      simp [hp₁, hp₂, htop]
    · -- Outside both feasible sets, both extensions are `⊤`.
      have htop : g₁ p.1 + g₂ p.1 = ⊤ := by
        unfold g₁ g₂ constrainedERealExtension
        simp [hp₁, hp₂]
      simp [hp₁, hp₂, htop]

end

/-- Source-facing part (1) of Theorem 3.1.5: multiplying a closed convex function on a feasible
set by a
nonnegative scalar preserves textbook closed-convexity on the same feasible set, expressed as
convexity of the finite real part together with lower semicontinuity on `Q`. This is a
source-facing bridge surface rather than the stronger chapter owner `ClosedConvexOn`. -/
-- Proof sketch: `hf` already implies convexity of `withTopRealPart f` on `Q`, and its stronger
-- closed-epigraph hypothesis is enough to recover lower semicontinuity on `Q`. Nonnegative
-- scalar multiplication preserves both conclusions on the restricted function.
theorem nonneg_smul_convexOn_lowerSemicontinuousOn
    {Q : Set X} {f : X → WithTop ℝ} {β : ℝ}
    (hf : ClosedConvexOn Q f) (hβ : 0 ≤ β) :
    ConvexOn ℝ Q (withTopRealPart (((β : WithTop ℝ) • f))) ∧
      LowerSemicontinuousOn (withTopRealPart (((β : WithTop ℝ) • f))) Q := by
  have hConvBase : ConvexOn ℝ Q (fun x ↦ β * withTopRealPart f x) :=
    hf.convexOn_withTopRealPart.smul hβ
  have hLscBase : LowerSemicontinuousOn (fun x ↦ β * withTopRealPart f x) Q :=
    Continuous.comp_lowerSemicontinuousOn (continuous_const_mul β)
      hf.lowerSemicontinuousOn_withTopRealPart (monotone_mul_left_of_nonneg hβ)
  refine ⟨?_, ?_⟩
  · -- Rewrite the scaled finite part to the standard `ConvexOn.smul` surface.
    refine hConvBase.congr ?_
    intro x hx
    exact (withTopRealPart_smul_of_mem_feasible (β := β) (x := x) (f := f)).symm
  · -- The lower-semicontinuity proof uses the same normalization, now pointwise within `Q`.
    intro x hx
    refine (hLscBase x hx).congr_of_eventuallyEq hx ?_
    exact Filter.Eventually.of_forall fun y ↦ by
      simpa [eq_comm] using
        (withTopRealPart_smul_of_mem_feasible (β := β) (x := y) (f := f))

/-- Auxiliary closed-feasible-set variant for Theorem 3.1.5: if the feasible set itself is
closed, then the stronger chapter owner `ClosedConvexOn` is preserved by nonnegative scaling as
well. -/
-- Proof sketch: combine the source-facing convexity / lower-semicontinuity conclusion with the
-- extra ambient closedness of `Q` to recover closedness of the constrained epigraph after
-- scaling.
theorem nonneg_smul_of_isClosed
    {Q : Set X} {f : X → WithTop ℝ} {β : ℝ}
    (hf : ClosedConvexOn Q f) (hβ : 0 ≤ β) (hQ : IsClosed Q) :
    ClosedConvexOn Q ((β : WithTop ℝ) • f) := by
  have hScaled :
      ConvexOn ℝ Q (withTopRealPart (((β : WithTop ℝ) • f))) ∧
        LowerSemicontinuousOn (withTopRealPart (((β : WithTop ℝ) • f))) Q :=
    nonneg_smul_convexOn_lowerSemicontinuousOn (hf := hf) hβ
  have hScaledDom : Q ⊆ dom ((β : WithTop ℝ) • f) := by
    intro x hx
    have hxDom : x ∈ dom f := hf.subset_withTopEffectiveDomain hx
    -- On feasible points, the scaled value is a finite real number inside `WithTop ℝ`.
    rw [mem_withTopEffectiveDomain_iff, Pi.smul_apply, smul_eq_mul,
      ← coe_withTopRealPart (f := f) hxDom, ← WithTop.coe_mul]
    simpa [WithTop.coe_mul] using
      (show (((β * (f x).untop₀ : ℝ) : WithTop ℝ)) < ⊤ from WithTop.coe_lt_top _)
  refine ⟨hScaledDom, ?_, ?_⟩
  · -- The extra closedness of `Q` upgrades the lower-semicontinuity result back to owner
    -- closedness of the constrained epigraph.
    simpa [constrainedEpigraph_eq_epigraph_withTopRealPart hScaledDom] using
      (lowerSemicontinuousOn_iff_isClosed_epigraph hQ).1 hScaled.2
  · -- The convexity half is exactly the epigraph formulation of the first theorem.
    simpa [constrainedEpigraph_eq_epigraph_withTopRealPart hScaledDom] using
      (convexOn_iff_convex_epigraph).1 hScaled.1

/-- Theorem 3.1.5 (2): the sum of two closed convex functions is closed and convex on the
intersection of their feasible sets. -/
-- Proof sketch: the constrained epigraph of the sum over `Q₁ ∩ Q₂` is the image of the product
-- of the two constrained epigraphs under addition in the height variable, so the owner
-- closedness and convexity hypotheses are preserved on the common feasible set.
theorem add_inter
    {Q₁ Q₂ : Set X} {f₁ f₂ : X → WithTop ℝ}
    (hf₁ : ClosedConvexOn Q₁ f₁) (hf₂ : ClosedConvexOn Q₂ f₂) :
    ClosedConvexOn (Q₁ ∩ Q₂) (f₁ + f₂) := by
  have hAddDom : (Q₁ ∩ Q₂) ⊆ dom (f₁ + f₂) := by
    intro x hx
    have hx₁ : x ∈ dom f₁ := hf₁.subset_withTopEffectiveDomain hx.1
    have hx₂ : x ∈ dom f₂ := hf₂.subset_withTopEffectiveDomain hx.2
    -- On the common feasible set, both summands are finite, so the pointwise sum is finite.
    rw [mem_withTopEffectiveDomain_iff, Pi.add_apply]
    simpa [WithTop.add_lt_top] using And.intro hx₁ hx₂
  have hConv₁ : ConvexOn ℝ (Q₁ ∩ Q₂) (withTopRealPart f₁) := by
    refine ⟨hf₁.convex.inter hf₂.convex, ?_⟩
    intro x hx y hy a b ha hb hab
    exact hf₁.convexOn_withTopRealPart.2 hx.1 hy.1 ha hb hab
  have hConv₂ : ConvexOn ℝ (Q₁ ∩ Q₂) (withTopRealPart f₂) := by
    refine ⟨hf₁.convex.inter hf₂.convex, ?_⟩
    intro x hx y hy a b ha hb hab
    exact hf₂.convexOn_withTopRealPart.2 hx.2 hy.2 ha hb hab
  have hConvAdd :
      ConvexOn ℝ (Q₁ ∩ Q₂) (withTopRealPart (f₁ + f₂)) := by
    -- On the common feasible set, the owner sum reduces to the ordinary real sum.
    refine (hConv₁.add hConv₂).congr ?_
    intro x hx
    simpa [eq_comm] using
      (withTopRealPart_add_of_mem_inter (hf₁ := hf₁) (hf₂ := hf₂) (x := x) hx)
  have hConvEpigraph :
      Convex ℝ (constrainedEpigraph (Q₁ ∩ Q₂) (f₁ + f₂)) := by
    simpa [constrainedEpigraph_eq_epigraph_withTopRealPart hAddDom] using
      (convexOn_iff_convex_epigraph).1 hConvAdd
  refine ⟨hAddDom, ?_, hConvEpigraph⟩
  -- Route correction: ambient closedness comes from the global `EReal` extension of each
  -- summand, not from a subtype epigraph argument on `Q₁ ∩ Q₂`.
  exact isClosed_constrainedEpigraph_add_inter (hf₁ := hf₁) (hf₂ := hf₂)

/-- Source-facing part (3) of Theorem 3.1.5: the pointwise maximum of two closed convex
functions is closed and
convex on the intersection of their feasible sets; the canonical pointwise owner is `f₁ ⊔ f₂`.
-/
-- Proof sketch: the constrained epigraph of the pointwise maximum over `Q₁ ∩ Q₂` is the
-- intersection of the constrained epigraphs of `f₁` and `f₂`, so the owner closedness and
-- convexity hypotheses are preserved on the common feasible set.
theorem max_inter
    {Q₁ Q₂ : Set X} {f₁ f₂ : X → WithTop ℝ}
    (hf₁ : ClosedConvexOn Q₁ f₁) (hf₂ : ClosedConvexOn Q₂ f₂) :
    ClosedConvexOn (Q₁ ∩ Q₂) (f₁ ⊔ f₂) := by
  have hSupDom : (Q₁ ∩ Q₂) ⊆ dom (f₁ ⊔ f₂) := by
    intro x hx
    have hx₁ : x ∈ dom f₁ := hf₁.subset_withTopEffectiveDomain hx.1
    have hx₂ : x ∈ dom f₂ := hf₂.subset_withTopEffectiveDomain hx.2
    -- On the common feasible set, both values are finite, so their pointwise maximum is finite.
    rw [mem_withTopEffectiveDomain_iff]
    exact sup_lt_iff.2 ⟨hx₁, hx₂⟩
  refine ⟨hSupDom, ?_, ?_⟩
  · -- The maximum epigraph is literally the intersection of the two constrained epigraphs.
    rw [constrainedEpigraph_sup_eq_inter]
    exact hf₁.isClosed_constrainedEpigraph.inter hf₂.isClosed_constrainedEpigraph
  · -- Convexity is preserved under intersection because the epigraph identity is exact.
    rw [constrainedEpigraph_sup_eq_inter]
    exact hf₁.convex_constrainedEpigraph.inter hf₂.convex_constrainedEpigraph

end ClosedConvexOn

end

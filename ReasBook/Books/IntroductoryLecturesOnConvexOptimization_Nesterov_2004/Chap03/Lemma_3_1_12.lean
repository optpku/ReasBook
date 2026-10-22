/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_1_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Pointwise Topology WithTopConvexAnalysis

universe u

/- Lemma 3.1.12 lies in the chapter's weighted-sum / subdifferential calculus for closed convex
`WithTop ℝ`-valued functions on the intrinsic ambient spaces already used by the chapter owners.

Sampled owner declarations:
- `dom` and `withTopRealPart` from `Definition_3_3`
- `ClosedConvexOn` and `ClosedConvexFunction` from `Definition_3_1_1_5`
- `subdifferential` and the notation `∂ f(x)` from `Definition_3_1_5`
- `ClosedConvexOn.nonneg_smul` and `ClosedConvexOn.add_inter` from `Theorem_3_1_5`

Best owner abstraction:
- the source-facing restricted-domain weighted sum `weightedAdd α₁ α₂ f₁ f₂`, whose effective
  domain is
  `dom f₁ ∩ dom f₂`
- the canonical pointwise weighted sum
  `((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂)` as the positive-weight bridge

Primitive data:
- the scalars `α₁`, `α₂`
- the functions `f₁`, `f₂`

Derived API:
- `withTopEffectiveDomain_weightedAdd_eq_inter`
- `ClosedConvexFunction.weightedAdd`
- `interior_effectiveDomain_weightedAdd_eq_inter`
- `weightedAdd_eq_pointwise_of_pos`
- `withTopEffectiveDomain_nonneg_weighted_add_eq_inter_of_pos`
- `ClosedConvexFunction.nonneg_weighted_add`
- `interior_effectiveDomain_nonneg_weighted_add_eq_of_pos`
- `subdifferential_nonneg_weighted_add_eq_of_pos`

Source/core/bridge triage:
- source-facing: the numbered weighted-sum conclusions of Lemma 3.1.12
- core/canonical:
  `dom`, `ClosedConvexOn`, `ClosedConvexFunction`, `subdifferential`,
  pointwise scalar multiplication, and pointwise addition
- bridge/view: the positive-weight identification of the source-facing weighted sum with the
  canonical pointwise weighted sum

The fallback source text states the theorem for a weighted sum `f` satisfying
`int (dom f) = int (dom f₁) ∩ int (dom f₂)` for all nonnegative weights. The canonical pointwise
`WithTop`-valued sum only has that domain behavior when both weights are strictly positive, so
this file keeps the book-style restricted-domain weighted sum as the main theorem surface and uses
the canonical pointwise sum only in the positive-weight bridge corollaries needed downstream. -/

section WeightedAdd

variable {X : Type u}

/-- The source-facing restricted-domain weighted sum from Lemma 3.1.12: it agrees with the
ordinary weighted real sum on the common effective domain `dom f₁ ∩ dom f₂` and is `⊤`
elsewhere. -/
def weightedAdd (α₁ α₂ : ℝ) (f₁ f₂ : X → WithTop ℝ) : X → WithTop ℝ :=
  fun x ↦
    if x ∈ dom f₁ ∩ dom f₂ then
      ((α₁ * withTopRealPart f₁ x + α₂ * withTopRealPart f₂ x : ℝ) : WithTop ℝ)
    else
      ⊤

section DomainHelpers

variable [TopologicalSpace X]
variable {f : X → WithTop ℝ} {f₁ f₂ : X → WithTop ℝ} {α : ℝ} {α₁ α₂ : ℝ}

/-- The source-facing weighted sum of Lemma 3.1.12 is finite exactly on the common effective
domain of the two summands. -/
theorem withTopEffectiveDomain_weightedAdd_eq_inter :
    dom (weightedAdd α₁ α₂ f₁ f₂) = dom f₁ ∩ dom f₂ := by
  ext x
  -- The definition of `weightedAdd` is already split by the common effective-domain test.
  by_cases hx : x ∈ dom f₁ ∩ dom f₂
  · simp [weightedAdd, hx]
    constructor <;> exact WithTop.coe_lt_top _
  · simp [weightedAdd, hx]

/-- Helper for Lemma 3.1.12: on the common effective domain, the finite real part of
`weightedAdd α₁ α₂ f₁ f₂` is the ordinary weighted real sum of the two finite real parts. -/
lemma withTopRealPart_weightedAdd_eq_on_inter
    (f₁ f₂ : X → WithTop ℝ) {α₁ α₂ : ℝ} {x : X}
    (hx : x ∈ dom f₁ ∩ dom f₂) :
    withTopRealPart (weightedAdd α₁ α₂ f₁ f₂) x =
      α₁ * withTopRealPart f₁ x + α₂ * withTopRealPart f₂ x := by
  have hxWeighted : x ∈ dom (weightedAdd α₁ α₂ f₁ f₂) := by
    rw [withTopEffectiveDomain_weightedAdd_eq_inter]
    exact hx
  -- Compare both sides after coercing back to `WithTop ℝ`, where `weightedAdd` is explicit.
  apply WithTop.coe_injective
  calc
    (((withTopRealPart (weightedAdd α₁ α₂ f₁ f₂) x : ℝ) : WithTop ℝ))
        = weightedAdd α₁ α₂ f₁ f₂ x := by
            rw [coe_withTopRealPart hxWeighted]
    _ = (((α₁ * withTopRealPart f₁ x + α₂ * withTopRealPart f₂ x : ℝ) : WithTop ℝ)) := by
          simp [weightedAdd, hx]

/-- Helper for Lemma 3.1.12: multiplying by a strictly positive scalar preserves effective-domain
membership for `WithTop ℝ`-valued functions. -/
lemma mem_dom_smul_iff_of_pos
    (f : X → WithTop ℝ) {α : ℝ} (hα : 0 < α) {x : X} :
    x ∈ dom ((α : WithTop ℝ) • f) ↔ x ∈ dom f := by
  -- A strictly positive scalar keeps `⊤` at `⊤`, so finiteness is unchanged.
  by_cases hx : x ∈ dom f
  · have hx' : x ∈ dom ((α : WithTop ℝ) • f) := by
      rw [mem_withTopEffectiveDomain_iff, Pi.smul_apply, smul_eq_mul,
        ← coe_withTopRealPart hx]
      simpa using
        (show (((α * withTopRealPart f x : ℝ) : WithTop ℝ) < ⊤) from WithTop.coe_lt_top _)
    simp [hx, hx']
  · have hxtop : f x = ⊤ := by
      exact top_unique (le_of_not_gt hx)
    have hx' : x ∉ dom ((α : WithTop ℝ) • f) := by
      simp [Pi.smul_apply, smul_eq_mul, hxtop, hα.ne']
    simp [hx, hx']

/-- Helper for Lemma 3.1.12: under strictly positive weights, the weighted pointwise sum is
finite exactly where both summands are finite. -/
lemma weightedAddDom_mem_iff_of_pos
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) {x : X} :
    x ∈ dom ((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂) ↔
      x ∈ dom f₁ ∧ x ∈ dom f₂ := by
  -- Finite pointwise sums are exactly the points where both scaled summands stay finite.
  rw [mem_withTopEffectiveDomain_iff, Pi.add_apply, WithTop.add_lt_top]
  simpa [mem_withTopEffectiveDomain_iff] using
    (show x ∈ dom ((α₁ : WithTop ℝ) • f₁) ∧ x ∈ dom ((α₂ : WithTop ℝ) • f₂) ↔
        x ∈ dom f₁ ∧ x ∈ dom f₂ from by
      simp [mem_dom_smul_iff_of_pos f₁ hα₁, mem_dom_smul_iff_of_pos f₂ hα₂])

/-- Under strictly positive weights, the source-facing weighted sum agrees with the canonical
pointwise weighted sum. -/
theorem weightedAdd_eq_pointwise_of_pos
    (f₁ f₂ : X → WithTop ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    weightedAdd α₁ α₂ f₁ f₂ =
      ((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂) := by
  funext x
  by_cases hx : x ∈ dom f₁ ∩ dom f₂
  · rcases hx with ⟨hx₁, hx₂⟩
    have hdom : x ∈ dom f₁ ∩ dom f₂ := ⟨hx₁, hx₂⟩
    -- On the common effective domain, both descriptions reduce to the same real weighted sum.
    calc
      weightedAdd α₁ α₂ f₁ f₂ x
          = (((α₁ * withTopRealPart f₁ x + α₂ * withTopRealPart f₂ x : ℝ) : WithTop ℝ)) := by
              simp [weightedAdd, hdom]
      _ = (((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂) x) := by
            rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
              ← coe_withTopRealPart hx₁, ← coe_withTopRealPart hx₂]
            exact_mod_cast
              (rfl :
                α₁ * withTopRealPart f₁ x + α₂ * withTopRealPart f₂ x =
                  α₁ * withTopRealPart f₁ x + α₂ * withTopRealPart f₂ x)
  · have hcanon : x ∉ dom ((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂) := by
      rw [weightedAddDom_mem_iff_of_pos hα₁ hα₂]
      simpa using hx
    have htop : (((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂) x) = ⊤ := by
      exact top_unique (le_of_not_gt hcanon)
    -- Off the common domain, both functions are forced to `⊤`.
    simp [weightedAdd, hx, htop]

end DomainHelpers

section ClosedConvex

variable [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]
variable {f₁ f₂ : X → WithTop ℝ} {α₁ α₂ : ℝ}

/-- Helper for Lemma 3.1.12: the constant zero `WithTop ℝ`-valued function is closed and convex.
-/
lemma closedConvexFunction_zero :
    ClosedConvexFunction (fun _ : X ↦ (0 : WithTop ℝ)) := by
  have hepigraph :
      constrainedEpigraph (dom (fun _ : X ↦ (0 : WithTop ℝ))) (fun _ : X ↦ (0 : WithTop ℝ)) =
        {p : X × ℝ | 0 ≤ p.2} := by
    ext p
    simp [constrainedEpigraph, withTopEffectiveDomain]
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp
  · -- The zero epigraph is the closed half-space above height `0`.
    rw [hepigraph]
    exact isClosed_le continuous_const continuous_snd
  · have hconv : ConvexOn ℝ (Set.univ : Set X) (fun _ : X ↦ (0 : ℝ)) := by
      refine ⟨convex_univ, ?_⟩
      intro x hx y hy a b ha hb hab
      simp
    -- The same half-space description makes convexity immediate from the real epigraph owner.
    rw [hepigraph]
    simpa using (convexOn_iff_convex_epigraph).1 hconv

/-- Helper for Lemma 3.1.12: multiplying a closed convex function by a strictly positive scalar
preserves the owner `ClosedConvexFunction`. -/
lemma ClosedConvexFunction.pos_smul
    (f : X → WithTop ℝ) (hf : ClosedConvexFunction f) {α : ℝ} (hα : 0 < α) :
    ClosedConvexFunction ((α : WithTop ℝ) • f) := by
  let g : X → WithTop ℝ := ((α : WithTop ℝ) • f)
  have hdom : dom g = dom f := by
    ext x
    simpa [g] using (mem_dom_smul_iff_of_pos f hα : x ∈ dom g ↔ x ∈ dom f)
  have hdomSubset : dom f ⊆ dom g := by
    intro x hx
    rwa [hdom]
  have hConvBase : ConvexOn ℝ (dom f) (fun x ↦ α * withTopRealPart f x) :=
    hf.convexOn_withTopRealPart.smul hα.le
  have hConvScaled : ConvexOn ℝ (dom f) (withTopRealPart g) := by
    -- Normalize the finite real part of the scaled function to the scalar multiple of the
    -- original finite real part.
    refine hConvBase.congr ?_
    intro x hx
    simpa [g, eq_comm] using
      (ClosedConvexOn.withTopRealPart_smul_of_mem_feasible :
        withTopRealPart (((α : WithTop ℝ) • f)) x = α * withTopRealPart f x)
  let rescale : X × ℝ → X × ℝ := fun p ↦ (p.1, p.2 / α)
  have hRescale : Continuous rescale := by
    continuity
  have hClosedScaled : IsClosed (constrainedEpigraph (dom f) g) := by
    -- Positive vertical scaling turns the new epigraph into a continuous preimage of the original
    -- constrained epigraph.
    convert hf.isClosed_constrainedEpigraph.preimage hRescale using 1
    ext p
    constructor
    · rintro ⟨hpDom, hp⟩
      have hpDomScaled : p.1 ∈ dom g := by
        rwa [hdom]
      have hscaled : α * withTopRealPart f p.1 ≤ p.2 := by
        have hreal : withTopRealPart g p.1 ≤ p.2 :=
          (withTopRealPart_le_iff hpDomScaled).2 hp
        simpa [g] using hreal
      have hbase : withTopRealPart f p.1 ≤ p.2 / α := by
        exact (le_div_iff₀ hα).2 (by simpa [mul_comm] using hscaled)
      simpa [rescale] using ⟨hpDom, (withTopRealPart_le_iff hpDom).1 hbase⟩
    · intro hp
      rcases (by simpa [rescale] using hp : p.1 ∈ dom f ∧ f p.1 ≤ (p.2 / α : ℝ)) with
        ⟨hpDom, hpIneq⟩
      have hpDomScaled : p.1 ∈ dom g := by
        rwa [hdom]
      have hbase : withTopRealPart f p.1 ≤ p.2 / α :=
        (withTopRealPart_le_iff hpDom).2 hpIneq
      have hscaled : α * withTopRealPart f p.1 ≤ p.2 := by
        simpa [mul_comm] using (le_div_iff₀ hα).1 hbase
      refine ⟨hpDom, ?_⟩
      exact (withTopRealPart_le_iff hpDomScaled).1 (by simpa [g] using hscaled)
  have hConvEpi : Convex ℝ (constrainedEpigraph (dom f) g) := by
      -- Once the scaled finite real part is normalized, convexity is exactly the usual epigraph
      -- reformulation on `dom f`.
    simpa [constrainedEpigraph_eq_epigraph_withTopRealPart hdomSubset] using
      (convexOn_iff_convex_epigraph).1 hConvScaled
  refine ⟨fun x hx ↦ hx, ?_, ?_⟩
  · change IsClosed (constrainedEpigraph (dom g) g)
    simpa [g, hdom] using hClosedScaled
  · change Convex ℝ (constrainedEpigraph (dom g) g)
    simpa [g, hdom] using hConvEpi

/-- The nonnegative weighted pointwise sum of two closed convex functions is again a closed convex
function. -/
-- Proof sketch: split the zero-weight branches directly, and in the positive branch transport
-- each summand through `ClosedConvexFunction.pos_smul` before applying
-- `ClosedConvexOn.add_inter`.
theorem ClosedConvexFunction.nonneg_weighted_add
    (f₁ f₂ : X → WithTop ℝ)
    (hf₁ : ClosedConvexFunction f₁)
    (hf₂ : ClosedConvexFunction f₂)
    (hα₁ : 0 ≤ α₁)
    (hα₂ : 0 ≤ α₂) :
    ClosedConvexFunction ((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂) := by
  rcases eq_or_lt_of_le hα₁ with rfl | hα₁_pos
  · rcases eq_or_lt_of_le hα₂ with rfl | hα₂_pos
    · -- When both weights vanish, the canonical pointwise sum is the constant zero function.
      simpa using
        (closedConvexFunction_zero : ClosedConvexFunction (fun _ : X ↦ (0 : WithTop ℝ)))
    · -- With one vanishing weight, only the positive-scalar transport of the surviving summand
      -- remains.
      simpa using ClosedConvexFunction.pos_smul f₂ hf₂ hα₂_pos
  · rcases eq_or_lt_of_le hα₂ with rfl | hα₂_pos
    · -- The symmetric one-weight-zero branch reduces to the same positive-scalar transport.
      simpa using ClosedConvexFunction.pos_smul f₁ hf₁ hα₁_pos
    · have hscaled₁ : ClosedConvexFunction ((α₁ : WithTop ℝ) • f₁) :=
        ClosedConvexFunction.pos_smul f₁ hf₁ hα₁_pos
      have hscaled₂ : ClosedConvexFunction ((α₂ : WithTop ℝ) • f₂) :=
        ClosedConvexFunction.pos_smul f₂ hf₂ hα₂_pos
      have hdom₁ : dom ((α₁ : WithTop ℝ) • f₁) = dom f₁ := by
        ext x
        simpa using (mem_dom_smul_iff_of_pos f₁ hα₁_pos : x ∈ dom ((α₁ : WithTop ℝ) • f₁) ↔ x ∈ dom f₁)
      have hdom₂ : dom ((α₂ : WithTop ℝ) • f₂) = dom f₂ := by
        ext x
        simpa using (mem_dom_smul_iff_of_pos f₂ hα₂_pos : x ∈ dom ((α₂ : WithTop ℝ) • f₂) ↔ x ∈ dom f₂)
      have hdomAdd :
          dom (((α₁ : WithTop ℝ) • f₁) + ((α₂ : WithTop ℝ) • f₂)) = dom f₁ ∩ dom f₂ := by
        ext x
        rw [mem_withTopEffectiveDomain_iff, Pi.add_apply, WithTop.add_lt_top]
        simpa using
          (show x ∈ dom ((α₁ : WithTop ℝ) • f₁) ∧ x ∈ dom ((α₂ : WithTop ℝ) • f₂) ↔
              x ∈ dom f₁ ∧ x ∈ dom f₂ from by
            rw [mem_dom_smul_iff_of_pos f₁ hα₁_pos, mem_dom_smul_iff_of_pos f₂ hα₂_pos])
      -- The positive branch is exactly the addition theorem on the common effective domain.
      change
        ClosedConvexOn
          (dom (((α₁ : WithTop ℝ) • f₁) + ((α₂ : WithTop ℝ) • f₂)))
          (((α₁ : WithTop ℝ) • f₁) + ((α₂ : WithTop ℝ) • f₂))
      simpa [hdom₁, hdom₂, hdomAdd] using ClosedConvexOn.add_inter hscaled₁ hscaled₂

/-- Source-facing closed-convex clause of Lemma 3.1.12 for the book-style restricted-domain
weighted sum: for all nonnegative weights, its finite real part is convex and lower
semicontinuous on the common effective domain `dom f₁ ∩ dom f₂`. This is the general
source-faithful closed-convex surface; the stronger owner `ClosedConvexFunction` is only stable on
`weightedAdd` in the strictly positive regime. -/
theorem weightedAdd_nonneg_convexOn_lowerSemicontinuousOn
    (f₁ f₂ : X → WithTop ℝ)
    (hf₁ : ClosedConvexFunction f₁)
    (hf₂ : ClosedConvexFunction f₂)
    (hα₁ : 0 ≤ α₁)
    (hα₂ : 0 ≤ α₂) :
    ConvexOn ℝ (dom f₁ ∩ dom f₂) (withTopRealPart (weightedAdd α₁ α₂ f₁ f₂)) ∧
      LowerSemicontinuousOn (withTopRealPart (weightedAdd α₁ α₂ f₁ f₂)) (dom f₁ ∩ dom f₂) := by
  have hScaled₁ := ClosedConvexOn.nonneg_smul_convexOn_lowerSemicontinuousOn
    (hf := hf₁) hα₁
  have hScaled₂ := ClosedConvexOn.nonneg_smul_convexOn_lowerSemicontinuousOn
    (hf := hf₂) hα₂
  have hConv₁ :
      ConvexOn ℝ (dom f₁ ∩ dom f₂) (withTopRealPart (((α₁ : WithTop ℝ) • f₁))) := by
    -- Restrict the first scaled summand from `dom f₁` to the common effective domain.
    refine ⟨hf₁.convex.inter hf₂.convex, ?_⟩
    intro x hx y hy a b ha hb hab
    exact hScaled₁.1.2 hx.1 hy.1 ha hb hab
  have hConv₂ :
      ConvexOn ℝ (dom f₁ ∩ dom f₂) (withTopRealPart (((α₂ : WithTop ℝ) • f₂))) := by
    -- Restrict the second scaled summand from `dom f₂` to the same common domain.
    refine ⟨hf₁.convex.inter hf₂.convex, ?_⟩
    intro x hx y hy a b ha hb hab
    exact hScaled₂.1.2 hx.2 hy.2 ha hb hab
  have hLsc₁ :
      LowerSemicontinuousOn (withTopRealPart (((α₁ : WithTop ℝ) • f₁))) (dom f₁ ∩ dom f₂) := by
    -- Lower semicontinuity restricts along the smaller common-domain filter.
    intro x hx
    exact (hScaled₁.2 x hx.1).mono fun _ hy ↦ hy.1
  have hLsc₂ :
      LowerSemicontinuousOn (withTopRealPart (((α₂ : WithTop ℝ) • f₂))) (dom f₁ ∩ dom f₂) := by
    -- The same restriction argument applies to the second scaled summand.
    intro x hx
    exact (hScaled₂.2 x hx.2).mono fun _ hy ↦ hy.2
  refine ⟨?_, ?_⟩
  · -- First prove convexity for the canonical scaled sum, then rewrite it back to `weightedAdd`.
    refine (hConv₁.add hConv₂).congr ?_
    intro x hx
    calc
      withTopRealPart (((α₁ : WithTop ℝ) • f₁)) x +
          withTopRealPart (((α₂ : WithTop ℝ) • f₂)) x
          = α₁ * withTopRealPart f₁ x + α₂ * withTopRealPart f₂ x := by
              rw [ClosedConvexOn.withTopRealPart_smul_of_mem_feasible,
                ClosedConvexOn.withTopRealPart_smul_of_mem_feasible]
      _ = withTopRealPart (weightedAdd α₁ α₂ f₁ f₂) x := by
            symm
            exact withTopRealPart_weightedAdd_eq_on_inter f₁ f₂ hx
  · -- The lower-semicontinuity proof uses the same normalization within `𝓝[dom f₁ ∩ dom f₂]`.
    intro x hx
    have hLscWeighted :
        LowerSemicontinuousOn
          (fun y ↦ α₁ * withTopRealPart f₁ y + α₂ * withTopRealPart f₂ y)
          (dom f₁ ∩ dom f₂) := by
      -- The scaled owner functions are globally equal to the explicit real weighted sum.
      simpa [ClosedConvexOn.withTopRealPart_smul_of_mem_feasible] using (hLsc₁.add hLsc₂)
    have hEq :
        ∀ᶠ y in 𝓝[dom f₁ ∩ dom f₂] x,
          ∀ t : ℝ,
            (α₁ * withTopRealPart f₁ y + α₂ * withTopRealPart f₂ y > t) ↔
              withTopRealPart (weightedAdd α₁ α₂ f₁ f₂) y > t := by
      filter_upwards [eventually_mem_nhdsWithin] with y hy t
      rw [withTopRealPart_weightedAdd_eq_on_inter f₁ f₂ hy]
    exact (hLscWeighted x hx).congr_of_eventuallyEq hx hEq

/-- Source-facing closed-convex clause of Lemma 3.1.12 in the positive-weight regime: the
weighted sum with effective domain `dom f₁ ∩ dom f₂` is closed and convex when both weights are
strictly positive. -/
theorem ClosedConvexFunction.weightedAdd
    (f₁ f₂ : X → WithTop ℝ)
    (hf₁ : ClosedConvexFunction f₁)
    (hf₂ : ClosedConvexFunction f₂)
    (hα₁ : 0 < α₁)
    (hα₂ : 0 < α₂) :
    ClosedConvexFunction (weightedAdd α₁ α₂ f₁ f₂) := by
  -- Route correction: the source-facing `weightedAdd` hard-codes the common effective domain, so
  -- the owner-level closed-convex theorem is only stable in the positive-weight branch where it
  -- agrees with the canonical pointwise weighted sum.
  simpa [weightedAdd_eq_pointwise_of_pos f₁ f₂ hα₁ hα₂] using
    ClosedConvexFunction.nonneg_weighted_add f₁ f₂ hf₁ hf₂ hα₁.le hα₂.le

end ClosedConvex

section EffectiveDomainInterior

variable [TopologicalSpace X]
variable {f₁ f₂ : X → WithTop ℝ} {α₁ α₂ : ℝ}

/-- Under strictly positive weights, the effective domain of the canonical weighted pointwise sum
is exactly the common effective domain of the two summands. -/
-- Proof sketch: positivity forces every occurrence of `⊤` in either summand to remain `⊤` after
-- scalar multiplication, so finiteness of the pointwise sum is equivalent to simultaneous
-- finiteness of both summands.
theorem withTopEffectiveDomain_nonneg_weighted_add_eq_inter_of_pos
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    dom ((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂) =
      dom f₁ ∩ dom f₂ := by
  ext x
  rw [weightedAddDom_mem_iff_of_pos hα₁ hα₂]
  rfl

/-- Positive-weight helper for Lemma 3.1.12: the interior of the effective domain of the canonical
weighted pointwise sum equals the intersection of the interiors of the summand domains. -/
-- Proof sketch: rewrite the effective domain using
-- `withTopEffectiveDomain_nonneg_weighted_add_eq_inter_of_pos`, then apply the canonical
-- topological identity `interior (A ∩ B) = interior A ∩ interior B`.
theorem interior_effectiveDomain_nonneg_weighted_add_eq_of_pos
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    interior (dom ((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂)) =
      interior (dom f₁) ∩ interior (dom f₂) := by
  -- Normalize the positive-weight domain first, then use the standard interior-of-intersection rule.
  rw [withTopEffectiveDomain_nonneg_weighted_add_eq_inter_of_pos hα₁ hα₂, interior_inter]

/-- Source-facing domain identity of Lemma 3.1.12: the weighted sum has interior effective domain
equal to the intersection of the interiors of the two summand domains. -/
theorem interior_effectiveDomain_weightedAdd_eq_inter
    :
    interior (dom (weightedAdd α₁ α₂ f₁ f₂)) =
      interior (dom f₁) ∩ interior (dom f₂) := by
  -- The source-facing weighted sum already has the exact domain intersection built into its definition.
  rw [withTopEffectiveDomain_weightedAdd_eq_inter, interior_inter]

end EffectiveDomainInterior

section Subdifferential

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {f₁ f₂ : V → WithTop ℝ} {α₁ α₂ : ℝ}

/-- Helper for Lemma 3.1.12: at strictly positive weights, adding scaled subgradients of the two
summands produces a subgradient of the weighted pointwise sum. -/
lemma weightedSubgradient_mem_subdifferential
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    {x g₁ g₂ : V}
    (hg₁ : g₁ ∈ ∂ f₁(x))
    (hg₂ : g₂ ∈ ∂ f₂(x)) :
    α₁ • g₁ + α₂ • g₂ ∈
      ∂ (((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂))(x) := by
  rw [← weightedAdd_eq_pointwise_of_pos f₁ f₂ hα₁ hα₂]
  rw [mem_subdifferential_iff]
  rw [mem_subdifferential_iff] at hg₁
  rw [mem_subdifferential_iff] at hg₂
  refine ⟨?_, ?_⟩
  · -- The base point is finite for both summands, hence for the source-facing weighted sum.
    rw [withTopEffectiveDomain_weightedAdd_eq_inter]
    exact ⟨hg₁.1, hg₂.1⟩
  · intro y hy
    have hx₁ : x ∈ dom f₁ := hg₁.1
    have hx₂ : x ∈ dom f₂ := hg₂.1
    rw [withTopEffectiveDomain_weightedAdd_eq_inter] at hy
    have hy₁ : y ∈ dom f₁ := hy.1
    have hy₂ : y ∈ dom f₂ := hy.2
    have hxdom : x ∈ dom f₁ ∩ dom f₂ := ⟨hx₁, hx₂⟩
    -- Convert the two subgradient inequalities to real inequalities and add them after scaling.
    have hineq₁ : withTopRealPart f₁ y ≥ withTopRealPart f₁ x + inner ℝ g₁ (y - x) := by
      have hcoe :
          (((withTopRealPart f₁ y : ℝ) : WithTop ℝ)) ≥
            (((withTopRealPart f₁ x + inner ℝ g₁ (y - x) : ℝ) : WithTop ℝ)) := by
        calc
          (((withTopRealPart f₁ y : ℝ) : WithTop ℝ))
              = f₁ y := by rw [coe_withTopRealPart hy₁]
          _ ≥ f₁ x + (inner ℝ g₁ (y - x) : WithTop ℝ) := hg₁.2 hy₁
          _ = (((withTopRealPart f₁ x + inner ℝ g₁ (y - x) : ℝ) : WithTop ℝ)) := by
                rw [← coe_withTopRealPart hx₁, WithTop.coe_add]
      exact_mod_cast hcoe
    have hineq₂ : withTopRealPart f₂ y ≥ withTopRealPart f₂ x + inner ℝ g₂ (y - x) := by
      have hcoe :
          (((withTopRealPart f₂ y : ℝ) : WithTop ℝ)) ≥
            (((withTopRealPart f₂ x + inner ℝ g₂ (y - x) : ℝ) : WithTop ℝ)) := by
        calc
          (((withTopRealPart f₂ y : ℝ) : WithTop ℝ))
              = f₂ y := by rw [coe_withTopRealPart hy₂]
          _ ≥ f₂ x + (inner ℝ g₂ (y - x) : WithTop ℝ) := hg₂.2 hy₂
          _ = (((withTopRealPart f₂ x + inner ℝ g₂ (y - x) : ℝ) : WithTop ℝ)) := by
                rw [← coe_withTopRealPart hx₂, WithTop.coe_add]
      exact_mod_cast hcoe
    have hscaled₁ := mul_le_mul_of_nonneg_left hineq₁ hα₁.le
    have hscaled₂ := mul_le_mul_of_nonneg_left hineq₂ hα₂.le
    have hreal :
        α₁ * withTopRealPart f₁ y + α₂ * withTopRealPart f₂ y ≥
          α₁ * withTopRealPart f₁ x + α₂ * withTopRealPart f₂ x +
            inner ℝ (α₁ • g₁ + α₂ • g₂) (y - x) := by
      simpa [inner_add_left, inner_smul_left, mul_add, add_assoc, add_left_comm, add_comm] using
        add_le_add hscaled₁ hscaled₂
    have hcoe :
        ((((α₁ * withTopRealPart f₁ y + α₂ * withTopRealPart f₂ y : ℝ) : WithTop ℝ))) ≥
          ((((α₁ * withTopRealPart f₁ x + α₂ * withTopRealPart f₂ x +
              inner ℝ (α₁ • g₁ + α₂ • g₂) (y - x) : ℝ) : WithTop ℝ))) := by
      exact_mod_cast hreal
    simpa [weightedAdd, hy, hxdom, WithTop.coe_add] using hcoe

/-- Helper for Lemma 3.1.12: the weighted Minkowski sum of the two pointwise subdifferentials is
contained in the subdifferential of the weighted pointwise sum at an interior domain point. -/
lemma weightedSubdifferential_subset
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    {x : V} :
    α₁ • ∂ f₁(x) + α₂ • ∂ f₂(x) ⊆
      ∂ (((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂))(x) := by
  rintro g ⟨u, hu, v, hv, rfl⟩
  -- Expand the Minkowski-sum witness and reuse the pointwise weighted-subgradient lemma.
  rcases hu with ⟨g₁, hg₁, rfl⟩
  rcases hv with ⟨g₂, hg₂, rfl⟩
  exact weightedSubgradient_mem_subdifferential hα₁ hα₂ hg₁ hg₂

/-- Helper for Lemma 3.1.12: the unconstrained subdifferential is exactly the constrained
subdifferential on the effective domain. -/
lemma mem_subdifferential_iff_mem_constrainedSubdifferential_dom
    {f : V → WithTop ℝ} {x g : V} :
    g ∈ ∂ f(x) ↔ g ∈ ∂[dom f] f(x) := by
  -- The unconstrained and domain-constrained definitions only differ by a duplicated `x ∈ dom f`.
  rw [mem_subdifferential_iff, mem_constrainedSubdifferential_iff, IsSubgradientAt]
  constructor
  · rintro ⟨hx, hsupport⟩
    exact ⟨hx, hx, hsupport⟩
  · rintro ⟨_, hx, hsupport⟩
    exact ⟨hx, hsupport⟩

/-- Helper for Lemma 3.1.12: a directional secant-limit upper bound at an interior point already
forces subgradient membership. -/
lemma mem_subdifferential_of_le_directionalSlopeChoice
    {f : V → WithTop ℝ} (hf : ClosedConvexFunction f) {x : V}
    (hx : x ∈ interior (dom f))
    {d : V → ℝ} {z : V}
    (hsecant :
      ∀ p : V,
        Filter.Tendsto
          (fun α : ℝ ↦
            (withTopRealPart f (x + α • p) - withTopRealPart f x) / α)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (d p)))
    (hpair : ∀ p : V, inner ℝ z p ≤ d p) :
    z ∈ ∂ f(x) := by
  rw [mem_subdifferential_iff_mem_constrainedSubdifferential_dom]
  rw [mem_constrainedSubdifferential_iff]
  refine ⟨interior_subset hx, interior_subset hx, ?_⟩
  intro y hy
  by_cases hyx : y = x
  · subst hyx
    simp
  let p : V := y - x
  let line : ℝ →ᵃ[ℝ] V := AffineMap.lineMap x y
  let S : Set ℝ := line ⁻¹' dom f
  let g : ℝ → ℝ := withTopRealPart f ∘ line
  have hline_apply (α : ℝ) : line α = x + α • p := by
    -- Rewrite the affine line through `x` and `y` in displacement form.
    simpa [line, p, sub_eq_add_neg, add_smul, smul_add, add_assoc, add_left_comm, add_comm] using
      (AffineMap.lineMap_apply_module x y α)
  have hconv : ConvexOn ℝ S g := by
    -- Restrict the finite real part of `f` to the scalar segment joining `x` and `y`.
    simpa [S, g] using hf.convexOn_withTopRealPart.comp_affineMap line
  have hzero_mem : (0 : ℝ) ∈ S := by
    simpa [S, hline_apply] using interior_subset hx
  have hone_mem : (1 : ℝ) ∈ S := by
    simpa [S, hline_apply, p] using hy
  have hderiv_Ioi : HasDerivWithinAt g (d p) (Set.Ioi (0 : ℝ)) 0 := by
    -- Read the secant-limit hypothesis as the right derivative of the scalar slice.
    rw [hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Set.Ioi (0 : ℝ) by simp)]
    simpa [g, hline_apply, slope_fun_def_field] using hsecant p
  have hslope : d p ≤ withTopRealPart f y - withTopRealPart f x := by
    -- Convexity bounds the right derivative by the endpoint secant slope of the slice.
    simpa [g, hline_apply, p, slope_def_field] using
      hconv.le_slope_of_hasDerivWithinAt_Ioi hzero_mem hone_mem zero_lt_one hderiv_Ioi
  have hreal : withTopRealPart f y ≥ withTopRealPart f x + inner ℝ z (y - x) := by
    have hpair' : inner ℝ z (y - x) ≤ d (y - x) := hpair (y - x)
    linarith
  have hxDom : x ∈ dom f := interior_subset hx
  have hcoe :
      (((withTopRealPart f y : ℝ) : WithTop ℝ)) ≥
        (((withTopRealPart f x + inner ℝ z (y - x) : ℝ) : WithTop ℝ)) := by
    exact_mod_cast hreal
  have hfinal :
      f y ≥ (((withTopRealPart f x + inner ℝ z (y - x) : ℝ) : WithTop ℝ)) := by
    rw [← coe_withTopRealPart hy]
    exact hcoe
  calc
    f y ≥ (((withTopRealPart f x + inner ℝ z (y - x) : ℝ) : WithTop ℝ)) := hfinal
    _ = f x + (inner ℝ z (y - x) : WithTop ℝ) := by
          rw [← coe_withTopRealPart hxDom, WithTop.coe_add]

/-- Helper for Lemma 3.1.12: an interior point admits a directional-slope model whose forward
secant quotients converge in every direction. -/
lemma existsDirectionalSlopeChoice_of_mem_interior
    {f : V → WithTop ℝ} (hf : ClosedConvexFunction f) {x : V}
    (hx : x ∈ interior (dom f)) :
    ∃ d : V → ℝ,
      (∀ p : V, ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x + α • p ∈ dom f) ∧
        ∀ p : V,
          Filter.Tendsto
            (fun α : ℝ ↦
              (withTopRealPart f (x + α • p) - withTopRealPart f x) / α)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (d p)) := by
  -- Choose the directional limit supplied by the earlier one-dimensional secant theorem in each
  -- direction.
  choose d hdDom hdSecant using
    fun p : V ↦
      (exists_tendsto_right_directionalSlope_of_convexOn_of_mem_interior_effectiveDomain
        hf.convexOn_withTopRealPart hx :
        ∃ d : ℝ,
          (∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x + α • p ∈ dom f) ∧
            Filter.Tendsto
              (fun α : ℝ ↦
                (withTopRealPart f (x + α • p) - withTopRealPart f x) / α)
              (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds d))
  exact ⟨d, hdDom, hdSecant⟩

/-- Helper for Lemma 3.1.12: the zero direction has zero directional-slope value for every
directional-slope model. -/
lemma directionalSlopeChoice_zero
    {f : V → WithTop ℝ} {x : V}
    {d : V → ℝ}
    (hsecant :
      ∀ p : V,
        Filter.Tendsto
          (fun α : ℝ ↦
            (withTopRealPart f (x + α • p) - withTopRealPart f x) / α)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (d p))) :
    d (0 : V) = 0 := by
  -- The zero direction gives the constant zero secant quotient, so its limit must be `0`.
  have hconst :
      Filter.Tendsto
        (fun α : ℝ ↦
          (withTopRealPart f (x + α • (0 : V)) - withTopRealPart f x) / α)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ)) := by
    simpa using (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ ↦ (0 : ℝ)) _ _)
  exact tendsto_nhds_unique (hsecant 0) hconst

/-- Helper for Lemma 3.1.12: rescaling the direction by a positive scalar rescales the chosen
directional slope by the same factor. -/
lemma directionalSlopeChoice_smul_of_pos
    {f : V → WithTop ℝ} {x : V}
    {d : V → ℝ}
    (hsecant :
      ∀ p : V,
        Filter.Tendsto
          (fun α : ℝ ↦
            (withTopRealPart f (x + α • p) - withTopRealPart f x) / α)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (d p)))
    {c : ℝ} (hc : 0 < c) (p : V) :
    d (c • p) = c * d p := by
  let secant : V → ℝ → ℝ := fun q α ↦
    (withTopRealPart f (x + α • q) - withTopRealPart f x) / α
  have hscale :
      Filter.Tendsto (fun α : ℝ ↦ c * α)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    simpa [zero_mul] using
      Filter.TendstoNhdsWithinIoi.const_mul hc
        (show Filter.Tendsto (fun α : ℝ ↦ α)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) from
            Filter.tendsto_id'.2 le_rfl)
  have hcomp :
      Filter.Tendsto (fun α : ℝ ↦ secant p (c * α))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (d p)) :=
    (hsecant p).comp hscale
  have hpos :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), 0 < α := by
    simpa using
      (eventually_mem_nhdsWithin :
        ∀ᶠ α : ℝ in 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ), α ∈ Set.Ioi (0 : ℝ))
  have heq :
      (fun α : ℝ ↦ secant (c • p) α) =ᶠ[𝓝[>] (0 : ℝ)]
        fun α ↦ c * secant p (c * α) := by
    filter_upwards [hpos] with α hα
    have hαne : α ≠ 0 := ne_of_gt hα
    have hcαne : c * α ≠ 0 := mul_ne_zero hc.ne' hαne
    have hrewrite :
        secant (c • p) α = c * secant p (c * α) := by
      dsimp [secant]
      rw [smul_smul, mul_comm]
      field_simp [hαne, hcαne]
    exact hrewrite
  have hscaled :
      Filter.Tendsto (fun α : ℝ ↦ c * secant p (c * α))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (c * d p)) :=
    hcomp.const_mul c
  exact tendsto_nhds_unique (hsecant (c • p)) (hscaled.congr' heq.symm)

/-- Helper for Lemma 3.1.12: the chosen directional-slope model is subadditive. -/
lemma directionalSlopeChoice_add_le
    {f : V → WithTop ℝ} (hf : ClosedConvexFunction f) {x : V}
    (hx : x ∈ interior (dom f))
    {d : V → ℝ}
    (hdom :
      ∀ p : V,
        ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x + α • p ∈ dom f)
    (hsecant :
      ∀ p : V,
        Filter.Tendsto
          (fun α : ℝ ↦
            (withTopRealPart f (x + α • p) - withTopRealPart f x) / α)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (d p))) :
    ∀ p q : V, d (p + q) ≤ d p + d q := by
  let secant : V → ℝ → ℝ := fun p α ↦
    (withTopRealPart f (x + α • p) - withTopRealPart f x) / α
  have hscaleTwo :
      Filter.Tendsto (fun α : ℝ ↦ (2 : ℝ) * α)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    simpa using
      Filter.TendstoNhdsWithinIoi.const_mul (by norm_num)
        (show Filter.Tendsto (fun α : ℝ ↦ α)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) from
            Filter.tendsto_id'.2 le_rfl)
  have hdomTwo :
      ∀ p : V, ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x + ((2 : ℝ) * α) • p ∈ dom f := by
    intro p
    exact hscaleTwo.eventually (hdom p)
  have hpos :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), 0 < α := by
    simpa using
      (eventually_mem_nhdsWithin :
        ∀ᶠ α : ℝ in 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ), α ∈ Set.Ioi (0 : ℝ))
  intro p q
  have hEventually :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        secant (p + q) α ≤ secant p ((2 : ℝ) * α) + secant q ((2 : ℝ) * α) := by
    filter_upwards [hdom (p + q), hdomTwo p, hdomTwo q, hpos] with α hαpq hαp hαq hα
    have hconv :
        withTopRealPart f (x + α • (p + q)) ≤
          (1 / 2 : ℝ) * withTopRealPart f (x + ((2 : ℝ) * α) • p) +
            (1 / 2 : ℝ) * withTopRealPart f (x + ((2 : ℝ) * α) • q) := by
      have hmid :
          (1 / 2 : ℝ) • (x + ((2 : ℝ) * α) • p) +
              (1 / 2 : ℝ) • (x + ((2 : ℝ) * α) • q) =
            x + α • (p + q) := by
        module
      have hconvOn := hf.convexOn_withTopRealPart
      have :=
        hconvOn.2 hαp hαq
          (show 0 ≤ (1 / 2 : ℝ) by norm_num)
          (show 0 ≤ (1 / 2 : ℝ) by norm_num)
          (show (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 by norm_num)
      rw [hmid] at this
      simpa [smul_add, add_assoc] using this
    have hnum :
        withTopRealPart f (x + α • (p + q)) - withTopRealPart f x ≤
          (withTopRealPart f (x + ((2 : ℝ) * α) • p) - withTopRealPart f x) / 2 +
            (withTopRealPart f (x + ((2 : ℝ) * α) • q) - withTopRealPart f x) / 2 := by
      linarith
    refine (div_le_iff₀ hα).2 ?_
    have hrewrite :
        α * (secant p ((2 : ℝ) * α) + secant q ((2 : ℝ) * α)) =
          (withTopRealPart f (x + ((2 : ℝ) * α) • p) - withTopRealPart f x) / 2 +
            (withTopRealPart f (x + ((2 : ℝ) * α) • q) - withTopRealPart f x) / 2 := by
      dsimp [secant]
      field_simp [hα.ne']
    calc
      withTopRealPart f (x + α • (p + q)) - withTopRealPart f x
          ≤
            (withTopRealPart f (x + ((2 : ℝ) * α) • p) - withTopRealPart f x) / 2 +
              (withTopRealPart f (x + ((2 : ℝ) * α) • q) - withTopRealPart f x) / 2 := hnum
      _ = α * (secant p ((2 : ℝ) * α) + secant q ((2 : ℝ) * α)) := hrewrite.symm
      _ = (secant p ((2 : ℝ) * α) + secant q ((2 : ℝ) * α)) * α := by ring
  have hp :
      Filter.Tendsto (fun α : ℝ ↦ secant p ((2 : ℝ) * α))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (d p)) :=
    (hsecant p).comp hscaleTwo
  have hq :
      Filter.Tendsto (fun α : ℝ ↦ secant q ((2 : ℝ) * α))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (d q)) :=
    (hsecant q).comp hscaleTwo
  exact le_of_tendsto_of_tendsto (hsecant (p + q)) (hp.add hq) hEventually

/-- Helper for Lemma 3.1.12: the directional-slope model chosen at an interior point is sublinear
on the ambient Hilbert space. -/
lemma directionalSlopeChoice_isSublinear
    {f : V → WithTop ℝ} (hf : ClosedConvexFunction f) {x : V}
    (hx : x ∈ interior (dom f))
    {d : V → ℝ}
    (hdom :
      ∀ p : V,
        ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x + α • p ∈ dom f)
    (hsecant :
      ∀ p : V,
        Filter.Tendsto
          (fun α : ℝ ↦
            (withTopRealPart f (x + α • p) - withTopRealPart f x) / α)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (d p))) :
    d (0 : V) = 0 ∧
      (∀ c : ℝ, 0 < c → ∀ p : V, d (c • p) = c * d p) ∧
      ∀ p q : V, d (p + q) ≤ d p + d q := by
  refine ⟨directionalSlopeChoice_zero hsecant, ?_, ?_⟩
  · intro c hc p
    -- Positive homogeneity follows by reparameterizing the secant limit.
    exact directionalSlopeChoice_smul_of_pos hsecant hc p
  · intro p q
    -- Convexity on midpoint secants gives subadditivity after passing to the limit.
    exact directionalSlopeChoice_add_le hf hx hdom hsecant p q

/-- Helper for Lemma 3.1.12: the directional-slope model at an interior point is bounded above by
the secant slope to any other feasible point. -/
lemma directionalSlopeChoice_le_pointDiff
    {f : V → WithTop ℝ} (hf : ClosedConvexFunction f) {x : V}
    (hx : x ∈ interior (dom f))
    {d : V → ℝ}
    (hdom :
      ∀ p : V,
        ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x + α • p ∈ dom f)
    (hsecant :
      ∀ p : V,
        Filter.Tendsto
          (fun α : ℝ ↦
            (withTopRealPart f (x + α • p) - withTopRealPart f x) / α)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (d p)))
    {y : V} (hy : y ∈ dom f) :
    d (y - x) ≤ withTopRealPart f y - withTopRealPart f x := by
  by_cases hyx : y = x
  · subst hyx
    simp [directionalSlopeChoice_zero hsecant]
  let p : V := y - x
  let line : ℝ →ᵃ[ℝ] V := AffineMap.lineMap x y
  let S : Set ℝ := line ⁻¹' dom f
  let g : ℝ → ℝ := withTopRealPart f ∘ line
  have hline_apply (α : ℝ) : line α = x + α • p := by
    -- Rewrite the affine line through `x` and `y` in displacement form.
    simpa [line, p, sub_eq_add_neg, add_smul, smul_add, add_assoc, add_left_comm, add_comm] using
      (AffineMap.lineMap_apply_module x y α)
  have hconv : ConvexOn ℝ S g := by
    -- Restrict the finite real part of `f` to the scalar segment joining `x` and `y`.
    simpa [S, g] using hf.convexOn_withTopRealPart.comp_affineMap line
  have hzero_mem : (0 : ℝ) ∈ S := by
    simpa [S, hline_apply] using interior_subset hx
  have hone_mem : (1 : ℝ) ∈ S := by
    simpa [S, hline_apply, p] using hy
  have hderiv_Ioi : HasDerivWithinAt g (d p) (Set.Ioi (0 : ℝ)) 0 := by
    -- Read the secant-limit hypothesis as the right derivative of the scalar slice.
    rw [hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Set.Ioi (0 : ℝ) by simp)]
    simpa [g, hline_apply, slope_fun_def_field] using hsecant p
  -- Convexity bounds the right derivative by the endpoint secant slope of the slice.
  simpa [g, hline_apply, p, slope_def_field] using
    hconv.le_slope_of_hasDerivWithinAt_Ioi hzero_mem hone_mem zero_lt_one hderiv_Ioi

/-- Helper for Lemma 3.1.12: at the origin of a real-valued full-domain model, subgradient
membership implies the corresponding pairing domination inequality. -/
lemma pairing_le_of_mem_subdifferential_originModel
    {d : V → ℝ} {g : V}
    (hzero : d (0 : V) = 0)
    (hg : g ∈ ∂ (fun p : V ↦ ((d p : ℝ) : WithTop ℝ))(0)) :
    ∀ p : V, inner ℝ g p ≤ d p := by
  -- Unfold the owner inequality at the origin and read it back as a real pairing bound.
  intro p
  rw [mem_subdifferential_iff] at hg
  have hpDom : p ∈ dom (fun q : V ↦ ((d q : ℝ) : WithTop ℝ)) := by
    simp [withTopEffectiveDomain]
  have hineq :
      (((d p : ℝ) : WithTop ℝ)) ≥
        (((d (0 : V) + inner ℝ g (p - (0 : V)) : ℝ) : WithTop ℝ)) := hg.2 hpDom
  have hreal : d p ≥ d (0 : V) + inner ℝ g (p - (0 : V)) := by
    exact_mod_cast hineq
  simpa [hzero] using hreal

/-- Helper for Lemma 3.1.12: at the origin of a real-valued full-domain model, the pairing
domination inequality is exactly the owner subgradient condition. -/
lemma mem_subdifferential_of_pairing_le_originModel
    {d : V → ℝ} {g : V}
    (hzero : d (0 : V) = 0)
    (hpair : ∀ p : V, inner ℝ g p ≤ d p) :
    g ∈ ∂ (fun p : V ↦ ((d p : ℝ) : WithTop ℝ))(0) := by
  -- Repackage the real pairing bound as the owner affine support inequality at the origin.
  rw [mem_subdifferential_iff]
  refine ⟨by simp [withTopEffectiveDomain], ?_⟩
  intro p hp
  have hreal : d p ≥ d (0 : V) + inner ℝ g (p - (0 : V)) := by
    simpa [hzero] using hpair p
  change (((d p : ℝ) : WithTop ℝ)) ≥
    (((d (0 : V) + inner ℝ g (p - (0 : V)) : ℝ) : WithTop ℝ))
  exact_mod_cast hreal

/-- Helper for Lemma 3.1.12: a directional-slope model at an interior point has the same
origin subdifferential as the original function at the base point. -/
lemma subdifferential_directionalSlopeChoice_at_zero_eq_subdifferential
    (f : V → WithTop ℝ) (hf : ClosedConvexFunction f) {x : V}
    (hx : x ∈ interior (dom f))
    {d : V → ℝ}
    (hdom :
      ∀ p : V,
        ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x + α • p ∈ dom f)
    (hsecant :
      ∀ p : V,
        Filter.Tendsto
          (fun α : ℝ ↦
            (withTopRealPart f (x + α • p) - withTopRealPart f x) / α)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (d p))) :
    ∂ (fun p : V ↦ ((d p : ℝ) : WithTop ℝ))(0) = ∂ f(x) := by
  have hzero : d (0 : V) = 0 :=
    directionalSlopeChoice_zero hsecant
  ext g
  constructor
  · intro hg
    rw [mem_subdifferential_iff] at hg
    -- The model subgradient inequality is exactly the pairing bound needed for the original
    -- directional-slope criterion.
    have hpair : ∀ p : V, inner ℝ g p ≤ d p :=
      pairing_le_of_mem_subdifferential_originModel hzero (by
        exact mem_subdifferential_iff.mpr hg)
    exact mem_subdifferential_of_le_directionalSlopeChoice hf hx hsecant hpair
  · intro hg
    rcases (mem_subdifferential_iff.mp hg) with ⟨hxDom, hminorant⟩
    apply mem_subdifferential_of_pairing_le_originModel hzero
    intro p
    -- Feed the original subgradient inequality into the secant model and pass to the limit.
    have hconst :
        Filter.Tendsto (fun _ : ℝ ↦ inner ℝ g p)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (inner ℝ g p)) :=
      tendsto_const_nhds
    have hpos :
        ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), 0 < α := by
      simpa using
        (eventually_mem_nhdsWithin :
          ∀ᶠ α : ℝ in 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ), α ∈ Set.Ioi (0 : ℝ))
    have hquot_bound :
        ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
          inner ℝ g p ≤
            (withTopRealPart f (x + α • p) - withTopRealPart f x) / α := by
      filter_upwards [hdom p, hpos] with α hαDom hαPos
      have hineq :
          f (x + α • p) ≥ f x + (inner ℝ g ((x + α • p) - x) : WithTop ℝ) :=
        hminorant hαDom
      have hreal :
          withTopRealPart f (x + α • p) ≥ withTopRealPart f x + α * inner ℝ g p := by
        rw [← coe_withTopRealPart hαDom, ← coe_withTopRealPart hxDom] at hineq
        have hineqTop :
            (((withTopRealPart f x + α * inner ℝ g p : ℝ) : WithTop ℝ)) ≤
              (((withTopRealPart f (x + α • p) : ℝ) : WithTop ℝ)) := by
          simpa [sub_eq_add_neg, inner_add_right, inner_neg_right, inner_smul_right] using hineq
        exact_mod_cast hineqTop
      have hmul :
          α * inner ℝ g p ≤
            withTopRealPart f (x + α • p) - withTopRealPart f x := by
        linarith
      exact (le_div_iff₀ hαPos).2 (by simpa [mul_comm, sub_eq_add_neg] using hmul)
    have hpair : inner ℝ g p ≤ d p :=
      le_of_tendsto_of_tendsto hconst (hsecant p) hquot_bound
    exact hpair

/-- Helper for Lemma 3.1.12: with a positive surviving weight, the zero-left source-facing weighted
sum is exactly the `⊤`-extension of the scaled second summand off `dom f₁`. -/
lemma weightedAdd_zero_left_eq_topExtension_of_pos
    (f₁ f₂ : V → WithTop ℝ)
    (hα₂ : 0 < α₂) :
    weightedAdd 0 α₂ f₁ f₂ =
      fun y ↦ if y ∈ dom f₁ then ((α₂ : WithTop ℝ) • f₂) y else ⊤ := by
  funext y
  by_cases hy₁ : y ∈ dom f₁
  · by_cases hy₂ : y ∈ dom f₂
    · have hy : y ∈ dom f₁ ∩ dom f₂ := ⟨hy₁, hy₂⟩
      -- On the common domain, both descriptions reduce to the same real scalar multiple.
      rw [weightedAdd, if_pos hy, if_pos hy₁, Pi.smul_apply, smul_eq_mul,
        ← coe_withTopRealPart hy₂, ← WithTop.coe_mul]
      norm_num
    · have hytop : f₂ y = ⊤ := top_unique (le_of_not_gt hy₂)
      -- Off `dom f₂`, positivity keeps the scaled second summand at `⊤`.
      simp [weightedAdd, hy₁, hy₂, hytop, Pi.smul_apply, smul_eq_mul, hα₂.ne']
  · -- Off `dom f₁`, the source-facing weighted sum is `⊤` by definition.
    simp [weightedAdd, hy₁]

/-- Helper for Lemma 3.1.12: with a positive surviving weight, the zero-right source-facing
weighted sum is exactly the `⊤`-extension of the scaled first summand off `dom f₂`. -/
lemma weightedAdd_zero_right_eq_topExtension_of_pos
    (f₁ f₂ : V → WithTop ℝ)
    (hα₁ : 0 < α₁) :
    weightedAdd α₁ 0 f₁ f₂ =
      fun y ↦ if y ∈ dom f₂ then ((α₁ : WithTop ℝ) • f₁) y else ⊤ := by
  funext y
  by_cases hy₂ : y ∈ dom f₂
  · by_cases hy₁ : y ∈ dom f₁
    · have hy : y ∈ dom f₁ ∩ dom f₂ := ⟨hy₁, hy₂⟩
      -- On the common domain, both descriptions reduce to the same real scalar multiple.
      rw [weightedAdd, if_pos hy, if_pos hy₂, Pi.smul_apply, smul_eq_mul,
        ← coe_withTopRealPart hy₁, ← WithTop.coe_mul]
      norm_num
    · have hytop : f₁ y = ⊤ := top_unique (le_of_not_gt hy₁)
      -- Off `dom f₁`, positivity keeps the scaled first summand at `⊤`.
      simp [weightedAdd, hy₁, hy₂, hytop, Pi.smul_apply, smul_eq_mul, hα₁.ne']
  · -- Off `dom f₂`, the source-facing weighted sum is `⊤` by definition.
    simp [weightedAdd, hy₂]

/-- Helper for Lemma 3.1.12: when both weights vanish, the source-facing weighted sum is the
`⊤`-extension of the zero function off the common effective domain. -/
lemma weightedAdd_zero_zero_eq_topExtension_zero :
    weightedAdd 0 0 f₁ f₂ =
      fun y ↦ if y ∈ dom f₁ ∩ dom f₂ then ((0 : ℝ) : WithTop ℝ) else ⊤ := by
  funext y
  by_cases hy : y ∈ dom f₁ ∩ dom f₂
  · -- On the common domain, both weighted coefficients vanish.
    simp [weightedAdd, hy]
  · -- Off the common domain, the source-facing weighted sum is forced to `⊤`.
    simp [weightedAdd, hy]

/-- Helper for Lemma 3.1.12: extending a function by `⊤` off `Q` turns ordinary subgradients into
constrained subgradients on `Q`, and conversely. -/
lemma mem_subdifferential_topExtension_iff_mem_constrainedSubdifferential
    {Q : Set V} [DecidablePred fun y : V ↦ y ∈ Q]
    {f : V → WithTop ℝ} {x g : V} :
    g ∈ ∂ (fun y ↦ if y ∈ Q then f y else ⊤)(x) ↔ g ∈ ∂[Q] f(x) := by
  rw [mem_subdifferential_iff, mem_constrainedSubdifferential_iff]
  constructor
  · rintro ⟨hxExt, hminorant⟩
    by_cases hxQ : x ∈ Q
    · have hxDom : x ∈ dom f := by
        simpa [hxQ] using hxExt
      refine ⟨hxQ, hxDom, ?_⟩
      intro y hyQ
      by_cases hyDom : y ∈ dom f
      · have hyExt : y ∈ dom (fun z ↦ if z ∈ Q then f z else ⊤) := by
          simpa [hyQ] using hyDom
        simpa [hxQ, hyQ] using hminorant hyExt
      · have hytop : f y = ⊤ := top_unique (le_of_not_gt hyDom)
        -- Outside `dom f`, the constrained inequality is automatic because the function is `⊤`.
        simp [hxQ, hyQ, hytop]
    · -- If the extension were finite at `x`, then `x` would have to belong to `Q`.
      exfalso
      simpa [hxQ] using hxExt
  · rintro ⟨hxQ, hxDom, hminorant⟩
    refine ⟨?_, ?_⟩
    · simpa [hxQ] using hxDom
    · intro y hyExt
      have hyQ : y ∈ Q := by
        by_contra hyQ
        exfalso
        simpa [hyQ] using hyExt
      have hyDom : y ∈ dom f := by
        simpa [hyQ] using hyExt
      -- On the effective domain of the extension, the constrained inequality is exactly the
      -- ordinary support inequality.
      simpa [hxQ, hyQ] using hminorant hyQ

/-- Helper for Lemma 3.1.12: the subdifferential of a `⊤`-extension is exactly the corresponding
constrained subdifferential on the underlying feasible set. -/
lemma subdifferential_topExtension_eq_constrainedSubdifferential
    {Q : Set V} [DecidablePred fun y : V ↦ y ∈ Q]
    {f : V → WithTop ℝ} {x : V} :
    ∂ (fun y ↦ if y ∈ Q then f y else ⊤)(x) = ∂[Q] f(x) := by
  ext g
  exact mem_subdifferential_topExtension_iff_mem_constrainedSubdifferential

/-- Helper for Lemma 3.1.12: restricting the support inequality to a feasible set that still
contains an open neighborhood of `x` does not change the subdifferential there. -/
lemma constrainedSubdifferential_eq_subdifferential_of_mem_interior
    (f : V → WithTop ℝ) (hf : ClosedConvexFunction f)
    {Q : Set V} {x : V}
    (hxQ : x ∈ interior Q)
    (hx : x ∈ interior (dom f)) :
    ∂[Q] f(x) = ∂ f(x) := by
  ext g
  constructor
  · intro hg
    rw [mem_subdifferential_iff]
    rcases (mem_constrainedSubdifferential_iff.mp hg) with ⟨_, hxDom, hminorant⟩
    refine ⟨hxDom, ?_⟩
    intro y hy
    by_cases hyx : y = x
    · subst hyx
      simp [hxDom]
    rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hxQ) with ⟨rQ, hrQ, hrQsub⟩
    rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hx) with ⟨rD, hrD, hrDsub⟩
    let r : ℝ := min rQ rD
    have hr : 0 < r := by
      exact lt_min hrQ hrD
    let t : ℝ := min 1 (r / (2 * ‖y - x‖))
    let z : V := (1 - t) • x + t • y
    have hy_sub_ne : y - x ≠ 0 := sub_ne_zero.mpr hyx
    have hnorm_ne : ‖y - x‖ ≠ 0 := by
      intro hnorm
      have hinner : inner ℝ (y - x) (y - x) = 0 := by
        simpa [hnorm] using real_inner_self_eq_norm_sq (y - x)
      have hzero : y - x = 0 := inner_self_eq_zero.mp hinner
      exact hyx (sub_eq_zero.mp hzero)
    have hnorm_pos : 0 < ‖y - x‖ := lt_of_le_of_ne (norm_nonneg (y - x)) hnorm_ne.symm
    have ht_pos : 0 < t := by
      dsimp [t]
      exact lt_min zero_lt_one (div_pos hr (mul_pos zero_lt_two hnorm_pos))
    have ht_le_one : t ≤ 1 := by
      dsimp [t]
      exact min_le_left _ _
    have hz_eq : z - x = t • (y - x) := by
      dsimp [z, t]
      simp [sub_eq_add_neg, add_comm, add_left_comm, smul_add, add_smul]
    have hz_ball : z ∈ Metric.ball x r := by
      rw [Metric.mem_ball, dist_eq_norm, hz_eq, norm_smul, Real.norm_of_nonneg ht_pos.le]
      have hmul :
          t * ‖y - x‖ ≤ (r / (2 * ‖y - x‖)) * ‖y - x‖ := by
        exact mul_le_mul_of_nonneg_right (min_le_right 1 (r / (2 * ‖y - x‖))) hnorm_pos.le
      have hhalf : (r / (2 * ‖y - x‖)) * ‖y - x‖ = r / 2 := by
        field_simp [hnorm_pos.ne']
      have hbound : t * ‖y - x‖ ≤ r / 2 := by
        calc
          t * ‖y - x‖ ≤ (r / (2 * ‖y - x‖)) * ‖y - x‖ := hmul
          _ = r / 2 := hhalf
      linarith
    have hzQ : z ∈ Q := by
      exact interior_subset (hrQsub (Metric.ball_subset_ball (min_le_left _ _) hz_ball))
    have hzDom : z ∈ dom f := by
      exact interior_subset (hrDsub (Metric.ball_subset_ball (min_le_right _ _) hz_ball))
    have hlocal_z : withTopRealPart f x + inner ℝ g (z - x) ≤ withTopRealPart f z := by
      have hineq :
          (((withTopRealPart f z : ℝ) : WithTop ℝ)) ≥
            (((withTopRealPart f x + inner ℝ g (z - x) : ℝ) : WithTop ℝ)) := by
        calc
          (((withTopRealPart f z : ℝ) : WithTop ℝ)) = f z := by
            rw [coe_withTopRealPart hzDom]
          _ ≥ f x + (inner ℝ g (z - x) : WithTop ℝ) := hminorant hzQ
          _ = (((withTopRealPart f x + inner ℝ g (z - x) : ℝ) : WithTop ℝ)) := by
                rw [← coe_withTopRealPart hxDom, WithTop.coe_add]
      exact_mod_cast hineq
    have hconv_z :
        withTopRealPart f z ≤
          (1 - t) * withTopRealPart f x + t * withTopRealPart f y := by
      -- Move the support inequality to a nearby feasible point `z`, then compare `f z` to the
      -- endpoint convex combination along the segment from `x` to `y`.
      simpa [z] using
        hf.convexOn_withTopRealPart.2 hxDom hy (sub_nonneg.mpr ht_le_one) ht_pos.le
          (by linarith)
    have hlocal_y : withTopRealPart f x + t * inner ℝ g (y - x) ≤ withTopRealPart f z := by
      simpa [hz_eq, real_inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using hlocal_z
    have hscaled : t * (withTopRealPart f x + inner ℝ g (y - x)) ≤ t * withTopRealPart f y := by
      nlinarith
    have hreal : withTopRealPart f x + inner ℝ g (y - x) ≤ withTopRealPart f y := by
      nlinarith
    have hcoe :
        (((withTopRealPart f y : ℝ) : WithTop ℝ)) ≥
          (((withTopRealPart f x + inner ℝ g (y - x) : ℝ) : WithTop ℝ)) := by
      exact_mod_cast hreal
    calc
      f y = (((withTopRealPart f y : ℝ) : WithTop ℝ)) := by
        rw [coe_withTopRealPart hy]
      _ ≥ (((withTopRealPart f x + inner ℝ g (y - x) : ℝ) : WithTop ℝ)) := hcoe
      _ = f x + (inner ℝ g (y - x) : WithTop ℝ) := by
            rw [← coe_withTopRealPart hxDom, WithTop.coe_add]
  · intro hg
    rw [mem_subdifferential_iff] at hg
    rw [mem_constrainedSubdifferential_iff]
    rcases hg with ⟨hxDom, hminorant⟩
    refine ⟨interior_subset hxQ, hxDom, ?_⟩
    intro y hyQ
    by_cases hyDom : y ∈ dom f
    · exact hminorant hyDom
    · have hytop : f y = ⊤ := top_unique (le_of_not_gt hyDom)
      simp [hytop]

/-- Helper for Lemma 3.1.12: at an interior feasible point, the constrained subdifferential of
the zero function is the singleton `{0}`. -/
lemma constrainedSubdifferential_zero_eq_singleton_zero
    (Q : Set V) {x : V} (hx : x ∈ interior Q) :
    ∂[Q] (fun _ : V ↦ ((0 : ℝ) : WithTop ℝ))(x) = ({(0 : V)} : Set V) := by
  ext g
  constructor
  · intro hg
    by_cases hg_zero : g = 0
    · simp [hg_zero]
    rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hx) with ⟨r, hr, hrsub⟩
    let α : ℝ := r / (2 * ‖g‖)
    have hnorm_ne : ‖g‖ ≠ 0 := by
      intro hnorm
      have hinner : inner ℝ g g = 0 := by
        simpa [hnorm] using real_inner_self_eq_norm_sq g
      have hzero : g = 0 := inner_self_eq_zero.mp hinner
      exact hg_zero hzero
    have hnorm_pos : 0 < ‖g‖ := lt_of_le_of_ne (norm_nonneg g) hnorm_ne.symm
    have hα : 0 < α := by
      dsimp [α]
      exact div_pos hr (mul_pos zero_lt_two hnorm_pos)
    have hy_norm : ‖x + α • g - x‖ < r := by
      have hnorm_eq : ‖x + α • g - x‖ = α * ‖g‖ := by
        calc
          ‖x + α • g - x‖ = ‖α • g‖ := by
            abel_nf
          _ = α * ‖g‖ := by
            rw [norm_smul, Real.norm_of_nonneg hα.le]
      rw [hnorm_eq]
      dsimp [α]
      have hcalc : (r / (2 * ‖g‖)) * ‖g‖ = r / 2 := by
        field_simp [hnorm_pos.ne']
      rw [hcalc]
      linarith
    have hy_ball : x + α • g ∈ Metric.ball x r := by
      rw [Metric.mem_ball, dist_eq_norm]
      simpa [sub_eq_add_neg, add_assoc] using hy_norm
    have hyQ : x + α • g ∈ Q := interior_subset (hrsub hy_ball)
    rcases (mem_constrainedSubdifferential_iff.mp hg) with ⟨_, _, hminorant⟩
    have hineq :
        (((0 : ℝ) : WithTop ℝ)) ≥
          ((inner ℝ g ((x + α • g) - x) : ℝ) : WithTop ℝ) := by
      simpa using hminorant hyQ
    have hreal : 0 ≥ α * ‖g‖ ^ 2 := by
      have hineq' : (0 : ℝ) ≥ inner ℝ g ((x + α • g) - x) := by
        exact_mod_cast hineq
      simpa [sub_eq_add_neg, real_inner_smul_right, real_inner_self_eq_norm_sq, α,
        mul_assoc] using hineq'
    have hpos : 0 < α * ‖g‖ ^ 2 := by
      positivity
    linarith
  · intro hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    rw [mem_constrainedSubdifferential_iff]
    refine ⟨interior_subset hx, by simp, ?_⟩
    intro y hy
    simp

/-- Helper for Lemma 3.1.12: a strictly positive scalar pulls out of the pointwise
subdifferential. -/
lemma subdifferential_pos_smul_eq
    (f : V → WithTop ℝ) {α : ℝ} (hα : 0 < α) {x : V} :
    ∂ (((α : WithTop ℝ) • f))(x) = α • ∂ f(x) := by
  ext g
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hα.ne']
  constructor
  · intro hg
    rw [mem_subdifferential_iff] at hg ⊢
    rcases hg with ⟨hxScaled, hminorant⟩
    have hx : x ∈ dom f :=
      (mem_dom_smul_iff_of_pos f hα).1 hxScaled
    refine ⟨hx, ?_⟩
    intro y hy
    have hyScaled : y ∈ dom (((α : WithTop ℝ) • f)) :=
      (mem_dom_smul_iff_of_pos f hα).2 hy
    have hineq :
        (((α * withTopRealPart f y : ℝ) : WithTop ℝ)) ≥
          (((α * withTopRealPart f x + inner ℝ g (y - x) : ℝ) : WithTop ℝ)) := by
      calc
        (((α * withTopRealPart f y : ℝ) : WithTop ℝ))
            = (((α : WithTop ℝ) • f) y) := by
                rw [Pi.smul_apply, smul_eq_mul, ← coe_withTopRealPart hy,
                  ← WithTop.coe_mul]
        _ ≥ (((α : WithTop ℝ) • f) x) + (inner ℝ g (y - x) : WithTop ℝ) := hminorant hyScaled
        _ = (((α * withTopRealPart f x + inner ℝ g (y - x) : ℝ) : WithTop ℝ)) := by
              rw [Pi.smul_apply, smul_eq_mul, ← coe_withTopRealPart hx,
                ← WithTop.coe_mul, WithTop.coe_add]
    have hreal : withTopRealPart f y ≥ withTopRealPart f x + inner ℝ (α⁻¹ • g) (y - x) := by
      have hrealScaled :
          α * withTopRealPart f y ≥ α * withTopRealPart f x + inner ℝ g (y - x) := by
        exact_mod_cast hineq
      have hrewrite :
          α * withTopRealPart f x + inner ℝ g (y - x) =
            α * (withTopRealPart f x + inner ℝ (α⁻¹ • g) (y - x)) := by
        rw [real_inner_smul_left]
        field_simp [hα.ne']
      rw [hrewrite] at hrealScaled
      nlinarith
    have hcoe :
        (((withTopRealPart f y : ℝ) : WithTop ℝ)) ≥
          (((withTopRealPart f x + inner ℝ (α⁻¹ • g) (y - x) : ℝ) : WithTop ℝ)) := by
      exact_mod_cast hreal
    calc
      f y = (((withTopRealPart f y : ℝ) : WithTop ℝ)) := by
        rw [coe_withTopRealPart hy]
      _ ≥ (((withTopRealPart f x + inner ℝ (α⁻¹ • g) (y - x) : ℝ) : WithTop ℝ)) := hcoe
      _ = f x + (inner ℝ (α⁻¹ • g) (y - x) : WithTop ℝ) := by
            rw [← coe_withTopRealPart hx, WithTop.coe_add]
  · intro hg
    rw [mem_subdifferential_iff] at hg ⊢
    rcases hg with ⟨hx, hminorant⟩
    have hxScaled : x ∈ dom (((α : WithTop ℝ) • f)) :=
      (mem_dom_smul_iff_of_pos f hα).2 hx
    refine ⟨hxScaled, ?_⟩
    intro y hyScaled
    have hy : y ∈ dom f :=
      (mem_dom_smul_iff_of_pos f hα).1 hyScaled
    have hineq :
        (((withTopRealPart f y : ℝ) : WithTop ℝ)) ≥
          (((withTopRealPart f x + inner ℝ (α⁻¹ • g) (y - x) : ℝ) : WithTop ℝ)) := by
      calc
        (((withTopRealPart f y : ℝ) : WithTop ℝ)) = f y := by
          rw [coe_withTopRealPart hy]
        _ ≥ f x + (inner ℝ (α⁻¹ • g) (y - x) : WithTop ℝ) := hminorant hy
        _ = (((withTopRealPart f x + inner ℝ (α⁻¹ • g) (y - x) : ℝ) : WithTop ℝ)) := by
              rw [← coe_withTopRealPart hx, WithTop.coe_add]
    have hreal :
        α * withTopRealPart f y ≥ α * withTopRealPart f x + inner ℝ g (y - x) := by
      have hrealBase :
          withTopRealPart f y ≥ withTopRealPart f x + inner ℝ (α⁻¹ • g) (y - x) := by
        exact_mod_cast hineq
      have hscaled :
          α * withTopRealPart f y ≥
            α * (withTopRealPart f x + inner ℝ (α⁻¹ • g) (y - x)) := by
        nlinarith
      have hrewrite :
          α * (withTopRealPart f x + inner ℝ (α⁻¹ • g) (y - x)) =
            α * withTopRealPart f x + inner ℝ g (y - x) := by
        rw [real_inner_smul_left]
        field_simp [hα.ne']
      rw [hrewrite] at hscaled
      exact hscaled
    have hcoe :
        (((α * withTopRealPart f y : ℝ) : WithTop ℝ)) ≥
          (((α * withTopRealPart f x + inner ℝ g (y - x) : ℝ) : WithTop ℝ)) := by
      exact_mod_cast hreal
    calc
      (((α : WithTop ℝ) • f) y) = (((α * withTopRealPart f y : ℝ) : WithTop ℝ)) := by
        rw [Pi.smul_apply, smul_eq_mul, ← coe_withTopRealPart hy, ← WithTop.coe_mul]
      _ ≥ (((α * withTopRealPart f x + inner ℝ g (y - x) : ℝ) : WithTop ℝ)) := hcoe
      _ = (((α : WithTop ℝ) • f) x) + (inner ℝ g (y - x) : WithTop ℝ) := by
            rw [Pi.smul_apply, smul_eq_mul, ← coe_withTopRealPart hx,
              ← WithTop.coe_mul, WithTop.coe_add]

/-- Helper for Lemma 3.1.12: a closed convex function is locally bounded above on a ball around
an interior effective-domain point. -/
lemma existsUpperBoundBall_withTopRealPart_of_mem_interior
    {f : V → WithTop ℝ} (hf : ClosedConvexFunction f) {x : V}
    (hx : x ∈ interior (dom f)) :
    ∃ r > 0, Metric.ball x r ⊆ dom f ∧
      ∃ M : ℝ, ∀ y, y ∈ Metric.ball x r → withTopRealPart f y ≤ M := by
  rcases Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.mp hx) with ⟨R, hR, hRsub⟩
  let B : Set V := Metric.ball (0 : V) R
  let C : ℕ → Set V := fun n ↦
    {u : V | f (x + u) ≤ (n : ℝ) ∧ f (x - u) ≤ (n : ℝ)}
  let D : ℕ → Set V := fun n ↦ C n ∪ Bᶜ
  have hclosedC : ∀ n, IsClosed (C n) := by
    intro n
    let Fplus : V → V × ℝ := fun u ↦ (x + u, (n : ℝ))
    let Fminus : V → V × ℝ := fun u ↦ (x - u, (n : ℝ))
    have hplusClosed :
        IsClosed (Fplus ⁻¹' constrainedEpigraph (dom f) f) :=
      hf.isClosed_constrainedEpigraph.preimage (by continuity)
    have hminusClosed :
        IsClosed (Fminus ⁻¹' constrainedEpigraph (dom f) f) :=
      hf.isClosed_constrainedEpigraph.preimage (by continuity)
    have hEq :
        C n =
          (Fplus ⁻¹' constrainedEpigraph (dom f) f) ∩
            (Fminus ⁻¹' constrainedEpigraph (dom f) f) := by
      ext u
      constructor
      · intro hu
        constructor
        · exact mem_constrainedEpigraph_iff.2
            ⟨mem_withTopEffectiveDomain_iff.2
                (lt_of_le_of_lt hu.1 (WithTop.coe_lt_top _)), hu.1⟩
        · exact mem_constrainedEpigraph_iff.2
            ⟨mem_withTopEffectiveDomain_iff.2
                (lt_of_le_of_lt hu.2 (WithTop.coe_lt_top _)), hu.2⟩
      · intro hu
        exact ⟨(mem_constrainedEpigraph_iff.1 hu.1).2, (mem_constrainedEpigraph_iff.1 hu.2).2⟩
    rw [hEq]
    exact hplusClosed.inter hminusClosed
  have hclosedD : ∀ n, IsClosed (D n) := by
    intro n
    exact (hclosedC n).union Metric.isOpen_ball.isClosed_compl
  have hcover : ⋃ n, D n = Set.univ := by
    ext u
    constructor
    · intro _
      simp
    · intro _
      by_cases huB : u ∈ B
      · have hxPlusDom : x + u ∈ dom f := by
          exact hRsub (by simpa [B, Metric.mem_ball, dist_eq_norm] using huB)
        have hxMinusDom : x - u ∈ dom f := by
          exact hRsub (by
            simpa [B, Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_assoc] using huB)
        obtain ⟨n, hn⟩ := exists_nat_gt
          (max (withTopRealPart f (x + u)) (withTopRealPart f (x - u)))
        have hPlusReal : withTopRealPart f (x + u) ≤ n := by
          exact le_of_lt (lt_of_le_of_lt (le_max_left _ _) hn)
        have hMinusReal : withTopRealPart f (x - u) ≤ n := by
          exact le_of_lt (lt_of_le_of_lt (le_max_right _ _) hn)
        have hPlusTop : f (x + u) ≤ (n : ℝ) := by
          rw [← coe_withTopRealPart hxPlusDom]
          exact_mod_cast hPlusReal
        have hMinusTop : f (x - u) ≤ (n : ℝ) := by
          rw [← coe_withTopRealPart hxMinusDom]
          exact_mod_cast hMinusReal
        exact Set.mem_iUnion.2 ⟨n, Or.inl ⟨hPlusTop, hMinusTop⟩⟩
      · exact Set.mem_iUnion.2 ⟨0, Or.inr huB⟩
  have hdense : Dense (⋃ n, interior (D n)) :=
    dense_iUnion_interior_of_closed hclosedD hcover
  obtain ⟨u₀, hu₀Dense, hu₀B⟩ :=
    hdense.exists_mem_open Metric.isOpen_ball ⟨0, Metric.mem_ball_self hR⟩
  rcases Set.mem_iUnion.1 hu₀Dense with ⟨n, hu₀IntD⟩
  have hu₀IntC : u₀ ∈ interior (C n) := by
    refine mem_interior_iff_mem_nhds.mpr ?_
    have hDnhds : D n ∈ 𝓝 u₀ := mem_interior_iff_mem_nhds.mp hu₀IntD
    have hBnhds : B ∈ 𝓝 u₀ := Metric.isOpen_ball.mem_nhds hu₀B
    refine Filter.mem_of_superset (Filter.inter_mem hDnhds hBnhds) ?_
    intro v hv
    rcases hv with ⟨hvD, hvB⟩
    rcases hvD with hvC | hvBc
    · exact hvC
    · exact False.elim (hvBc hvB)
  have hsymmC : ∀ n {u : V}, u ∈ C n → -u ∈ C n := by
    intro n u hu
    simpa [C, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hu.symm
  have hconvC : ∀ n, Convex ℝ (C n) := by
    intro n
    intro u hu v hv a b ha hb hab
    have hxPlusU : x + u ∈ dom f := by
      exact mem_withTopEffectiveDomain_iff.2 (lt_of_le_of_lt hu.1 (WithTop.coe_lt_top _))
    have hxPlusV : x + v ∈ dom f := by
      exact mem_withTopEffectiveDomain_iff.2 (lt_of_le_of_lt hv.1 (WithTop.coe_lt_top _))
    have hxMinusU : x - u ∈ dom f := by
      exact mem_withTopEffectiveDomain_iff.2 (lt_of_le_of_lt hu.2 (WithTop.coe_lt_top _))
    have hxMinusV : x - v ∈ dom f := by
      exact mem_withTopEffectiveDomain_iff.2 (lt_of_le_of_lt hv.2 (WithTop.coe_lt_top _))
    have huPlusTop : f (x + u) ≤ (n : ℝ) := hu.1
    have hvPlusTop : f (x + v) ≤ (n : ℝ) := hv.1
    have huMinusTop : f (x - u) ≤ (n : ℝ) := hu.2
    have hvMinusTop : f (x - v) ≤ (n : ℝ) := hv.2
    have huPlusReal : withTopRealPart f (x + u) ≤ n := by
      rw [← coe_withTopRealPart hxPlusU] at huPlusTop
      exact_mod_cast huPlusTop
    have hvPlusReal : withTopRealPart f (x + v) ≤ n := by
      rw [← coe_withTopRealPart hxPlusV] at hvPlusTop
      exact_mod_cast hvPlusTop
    have huMinusReal : withTopRealPart f (x - u) ≤ n := by
      rw [← coe_withTopRealPart hxMinusU] at huMinusTop
      exact_mod_cast huMinusTop
    have hvMinusReal : withTopRealPart f (x - v) ≤ n := by
      rw [← coe_withTopRealPart hxMinusV] at hvMinusTop
      exact_mod_cast hvMinusTop
    have hplusRewrite0 :
        a • (x + u) + b • (x + v) = (a + b) • x + (a • u + b • v) := by
      module
    have hplusRewrite :
        a • (x + u) + b • (x + v) = x + (a • u + b • v) := by
      calc
        a • (x + u) + b • (x + v) = (a + b) • x + (a • u + b • v) := hplusRewrite0
        _ = x + (a • u + b • v) := by simpa [hab]
    have hminusRewrite0 :
        a • (x - u) + b • (x - v) =
          (a + b) • x + (-1 • a • u + -1 • b • v) := by
      module
    have hminusRewrite :
        a • (x - u) + b • (x - v) = x - (a • u + b • v) := by
      calc
        a • (x - u) + b • (x - v)
            = (a + b) • x + (-1 • a • u + -1 • b • v) := hminusRewrite0
        _ = x - (a • u + b • v) := by
              simp [sub_eq_add_neg, hab, smul_add, add_assoc, add_left_comm, add_comm]
    have hplusReal :
        withTopRealPart f (x + (a • u + b • v)) ≤ n := by
      have hconv := hf.convexOn_withTopRealPart.2 hxPlusU hxPlusV ha hb hab
      rw [hplusRewrite] at hconv
      have hbound :
          a * withTopRealPart f (x + u) + b * withTopRealPart f (x + v) ≤ n := by
        nlinarith
      exact le_trans hconv hbound
    have hminusReal :
        withTopRealPart f (x - (a • u + b • v)) ≤ n := by
      have hconv := hf.convexOn_withTopRealPart.2 hxMinusU hxMinusV ha hb hab
      rw [hminusRewrite] at hconv
      have hbound :
          a * withTopRealPart f (x - u) + b * withTopRealPart f (x - v) ≤ n := by
        nlinarith
      exact le_trans hconv hbound
    have hplusTop' :
        f (x + (a • u + b • v)) ≤ (n : ℝ) := by
      have hxCombo : x + (a • u + b • v) ∈ dom f := by
        rw [← hplusRewrite]
        exact hf.convexOn_withTopRealPart.1 hxPlusU hxPlusV ha hb hab
      rw [← coe_withTopRealPart hxCombo]
      exact_mod_cast hplusReal
    have hminusTop' :
        f (x - (a • u + b • v)) ≤ (n : ℝ) := by
      have hxCombo : x - (a • u + b • v) ∈ dom f := by
        rw [← hminusRewrite]
        exact hf.convexOn_withTopRealPart.1 hxMinusU hxMinusV ha hb hab
      rw [← coe_withTopRealPart hxCombo]
      exact_mod_cast hminusReal
    exact ⟨hplusTop', hminusTop'⟩
  rcases Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.mp hu₀IntC) with ⟨r, hr, hrsub⟩
  have hsmall : Metric.ball (0 : V) r ⊆ C n := by
    intro v hv
    have huv : u₀ + v ∈ C n := by
      apply hrsub
      simpa [Metric.mem_ball, dist_eq_norm] using hv
    have huv' : u₀ - v ∈ C n := by
      apply hrsub
      simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_assoc] using hv
    have hneg : -(u₀ - v) ∈ C n := hsymmC n huv'
    have hmid :
        (1 / 2 : ℝ) • (u₀ + v) + (1 / 2 : ℝ) • (-(u₀ - v)) = v := by
      module
    have hmidMem :
        (1 / 2 : ℝ) • (u₀ + v) + (1 / 2 : ℝ) • (-(u₀ - v)) ∈ C n :=
      hconvC n huv hneg (show 0 ≤ (1 / 2 : ℝ) by norm_num)
        (show 0 ≤ (1 / 2 : ℝ) by norm_num)
        (show (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 by norm_num)
    rwa [hmid] at hmidMem
  refine ⟨r, hr, ?_, n, ?_⟩
  · intro y hy
    have hv : y - x ∈ Metric.ball (0 : V) r := by
      simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg] using hy
    have hCmem : y - x ∈ C n := hsmall hv
    have hyLe : f y ≤ (n : ℝ) := by
      simpa [C] using hCmem.1
    exact mem_withTopEffectiveDomain_iff.2 (lt_of_le_of_lt hyLe (WithTop.coe_lt_top _))
  · intro y hy
    have hv : y - x ∈ Metric.ball (0 : V) r := by
      simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg] using hy
    have hCmem : y - x ∈ C n := hsmall hv
    have hyLe : f y ≤ (n : ℝ) := by
      simpa [C] using hCmem.1
    have hyDom : y ∈ dom f :=
      mem_withTopEffectiveDomain_iff.2 (lt_of_le_of_lt hyLe (WithTop.coe_lt_top _))
    rw [← coe_withTopRealPart hyDom] at hyLe
    exact_mod_cast hyLe

/-- Helper for Lemma 3.1.12: the directional-slope model is uniformly bounded on the unit ball. -/
lemma directionalSlopeChoice_abs_le_on_unitBall
    {f : V → WithTop ℝ} (hf : ClosedConvexFunction f) {x : V}
    (hx : x ∈ interior (dom f))
    {d : V → ℝ}
    (hdom :
      ∀ p : V,
        ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x + α • p ∈ dom f)
    (hsecant :
      ∀ p : V,
        Filter.Tendsto
          (fun α : ℝ ↦
            (withTopRealPart f (x + α • p) - withTopRealPart f x) / α)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (d p))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : V, ‖p‖ ≤ 1 → |d p| ≤ C := by
  rcases existsUpperBoundBall_withTopRealPart_of_mem_interior hf hx with
    ⟨r, hr, hballDom, M, hballBound⟩
  let ρ : ℝ := r / 2
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hxBall : x ∈ Metric.ball x r := by
    simpa [Metric.mem_ball] using hr
  have hxBound : withTopRealPart f x ≤ M := hballBound x hxBall
  let C : ℝ := (M - withTopRealPart f x) / ρ
  refine ⟨C, div_nonneg (sub_nonneg.mpr hxBound) hρ.le, ?_⟩
  intro p hp
  have hzero : d (0 : V) = 0 := directionalSlopeChoice_zero hsecant
  have hadd := directionalSlopeChoice_add_le hf hx hdom hsecant p (-p)
  have hsum : 0 ≤ d p + d (-p) := by
    simpa [hzero] using hadd
  have hbound (q : V) (hq : ‖q‖ ≤ 1) : d q ≤ C := by
    have hyBall : x + ρ • q ∈ Metric.ball x r := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hnorm :
          ‖x + ρ • q - x‖ = ρ * ‖q‖ := by
        have hxq : x + ρ • q - x = ρ • q := by
          abel_nf
        rw [hxq, norm_smul, Real.norm_of_nonneg hρ.le]
      rw [hnorm]
      have hmul : ρ * ‖q‖ ≤ ρ := by
        exact mul_le_of_le_one_right hρ.le hq
      have hlt : ρ < r := by
        dsimp [ρ]
        linarith
      exact lt_of_le_of_lt hmul hlt
    have hyDom : x + ρ • q ∈ dom f := hballDom hyBall
    have hsecantBound :
        d (ρ • q) ≤ withTopRealPart f (x + ρ • q) - withTopRealPart f x := by
      simpa [sub_eq_add_neg, add_assoc] using
        (directionalSlopeChoice_le_pointDiff hf hx hdom hsecant (y := x + ρ • q) hyDom)
    have hscaled : d (ρ • q) = ρ * d q :=
      directionalSlopeChoice_smul_of_pos hsecant hρ q
    have hreal : ρ * d q ≤ M - withTopRealPart f x := by
      calc
        ρ * d q = d (ρ • q) := hscaled.symm
        _ ≤ withTopRealPart f (x + ρ • q) - withTopRealPart f x := hsecantBound
        _ ≤ M - withTopRealPart f x := by linarith [hballBound (x + ρ • q) hyBall]
    exact (le_div_iff₀ hρ).2 (by simpa [C, mul_comm] using hreal)
  have hupper : d p ≤ C := hbound p hp
  have hupperNeg : d (-p) ≤ C := by
    simpa [norm_neg] using hbound (-p) (by simpa [norm_neg] using hp)
  have hlower : -C ≤ d p := by
    linarith
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- Helper for Lemma 3.1.12: a closed convex function on the interior of its effective domain has
at least one subgradient there. -/
lemma subdifferential_nonempty_of_mem_interior
    {f : V → WithTop ℝ} (hf : ClosedConvexFunction f) {x : V}
    (hx : x ∈ interior (dom f)) :
    (∂ f(x)).Nonempty := by
  -- Route correction: the old strict-epigraph separator plan is unnecessary here. The existing
  -- directional-slope model is already sublinear, and the local bounded-ball lemma upgrades the
  -- Hahn-Banach extension to a continuous linear functional that Riesz turns into a vector.
  rcases existsDirectionalSlopeChoice_of_mem_interior hf hx with ⟨d, hdom, hsecant⟩
  rcases directionalSlopeChoice_isSublinear hf hx hdom hsecant with ⟨hzero, hhom, hadd⟩
  rcases directionalSlopeChoice_abs_le_on_unitBall hf hx hdom hsecant with ⟨B, _, hB⟩
  let zeroPMap : V →ₗ.[ℝ] ℝ := ⟨⊥, 0⟩
  obtain ⟨ℓ, _, hℓle⟩ :=
    exists_extension_of_le_sublinear zeroPMap d hhom hadd (by
      intro v
      have hv0 : (v : V) = 0 := by
        have hmem : (v : V) ∈ (⊥ : Submodule ℝ V) := by
          simpa [zeroPMap] using v.2
        rw [Submodule.mem_bot] at hmem
        exact hmem
      simp [zeroPMap, hv0, hzero])
  have hℓBall : ∀ z ∈ Metric.ball (0 : V) 1, ‖ℓ z‖ ≤ B := by
    intro z hz
    have hzNorm : ‖z‖ ≤ 1 := le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
    have hdz : |d z| ≤ B := hB z hzNorm
    have hdzNeg : |d (-z)| ≤ B := by
      simpa [norm_neg] using hB (-z) (by simpa [norm_neg] using hzNorm)
    have hupper : ℓ z ≤ B := le_trans (hℓle z) (abs_le.mp hdz).2
    have hnegUpper : -ℓ z ≤ B := by
      simpa using le_trans (hℓle (-z)) (abs_le.mp hdzNeg).2
    have hlower : -B ≤ ℓ z := by
      linarith
    have habs : |ℓ z| ≤ B := abs_le.mpr ⟨hlower, hupper⟩
    simpa [Real.norm_eq_abs] using habs
  obtain ⟨C, hC⟩ := LinearMap.bound_of_ball_bound zero_lt_one B ℓ hℓBall
  let L : V →L[ℝ] ℝ := ℓ.mkContinuousOfExistsBound ⟨C, hC⟩
  let z : V := (InnerProductSpace.toDual ℝ V).symm L
  have hpair : ∀ p : V, inner ℝ z p ≤ d p := by
    intro p
    calc
      inner ℝ z p = L p := by
        simpa [z] using
          (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := V) (x := p) (y := L))
      _ = ℓ p := by
        simpa [L] using (LinearMap.mkContinuousOfExistsBound_apply (f := ℓ) ⟨C, hC⟩ p)
      _ ≤ d p := hℓle p
  refine ⟨z, ?_⟩
  -- The continuous Hahn-Banach witness now matches the directional-slope criterion already proved.
  exact mem_subdifferential_of_le_directionalSlopeChoice hf hx hsecant hpair

/-- Helper for Lemma 3.1.12: a subgradient of the sum of two positively weighted origin models
splits into positively weighted subgradients of the two summands. -/
lemma mem_weighted_originModel_sum_of_mem_subdifferential
    {d₁ d₂ : V → ℝ} {g : V}
    (hα₁ : 0 < α₁)
    (hα₂ : 0 < α₂)
    (hzero₁ : d₁ (0 : V) = 0)
    (hzero₂ : d₂ (0 : V) = 0)
    (hhom₁ : ∀ c : ℝ, 0 < c → ∀ p : V, d₁ (c • p) = c * d₁ p)
    (hhom₂ : ∀ c : ℝ, 0 < c → ∀ p : V, d₂ (c • p) = c * d₂ p)
    (hadd₁ : ∀ p q : V, d₁ (p + q) ≤ d₁ p + d₁ q)
    (hadd₂ : ∀ p q : V, d₂ (p + q) ≤ d₂ p + d₂ q)
    (hbound₁ : ∃ B₁ : ℝ, 0 ≤ B₁ ∧ ∀ p : V, ‖p‖ ≤ 1 → |d₁ p| ≤ B₁)
    (hbound₂ : ∃ B₂ : ℝ, 0 ≤ B₂ ∧ ∀ p : V, ‖p‖ ≤ 1 → |d₂ p| ≤ B₂)
    (hg :
      g ∈ ∂ (fun p : V ↦ (((α₁ * d₁ p + α₂ * d₂ p : ℝ) : WithTop ℝ)))(0)) :
    g ∈
      α₁ • ∂ (fun p : V ↦ ((d₁ p : ℝ) : WithTop ℝ))(0) +
        α₂ • ∂ (fun p : V ↦ ((d₂ p : ℝ) : WithTop ℝ))(0) := by
  have hpair :
      ∀ p : V, inner ℝ g p ≤ α₁ * d₁ p + α₂ * d₂ p := by
    simpa [hzero₁, hzero₂] using
      pairing_le_of_mem_subdifferential_originModel
        (d := fun p : V ↦ α₁ * d₁ p + α₂ * d₂ p)
        (g := g)
        (by simp [hzero₁, hzero₂]) hg
  rcases hbound₁ with ⟨B₁, hB₁_nonneg, hB₁⟩
  rcases hbound₂ with ⟨B₂, hB₂_nonneg, hB₂⟩
  let N : V × V → ℝ := fun z ↦ α₁ * d₁ z.1 + α₂ * d₂ z.2
  let diagMap : V →ₗ[ℝ] V × V :=
    (LinearMap.id : V →ₗ[ℝ] V).prod (LinearMap.id : V →ₗ[ℝ] V)
  let diag : Submodule ℝ (V × V) := LinearMap.range diagMap
  let diagPMap : V × V →ₗ.[ℝ] ℝ :=
    ⟨diag,
      { toFun := fun z ↦ inner ℝ g z.1.1
        map_add' := by
          intro z w
          simp [inner_add_right]
        map_smul' := by
          intro c z
          simp [real_inner_smul_right] }⟩
  have hdiag_le : ∀ z : diag, diagPMap z ≤ N z := by
    intro z
    rcases z.2 with ⟨p, hp⟩
    have hz_eq : (z : V × V) = (p, p) := by
      simpa [diagMap] using hp.symm
    have hz_fst : (z : V × V).1 = p := by
      simpa using congrArg Prod.fst hz_eq
    have hz_snd : (z : V × V).2 = p := by
      simpa using congrArg Prod.snd hz_eq
    simpa [diagPMap, N, hz_fst, hz_snd] using hpair p
  have hN_hom : ∀ c : ℝ, 0 < c → ∀ z : V × V, N (c • z) = c * N z := by
    intro c hc z
    dsimp [N]
    rw [hhom₁ c hc z.1, hhom₂ c hc z.2]
    ring
  have hN_add : ∀ z w : V × V, N (z + w) ≤ N z + N w := by
    intro z w
    dsimp [N]
    have h₁ := hadd₁ z.1 w.1
    have h₂ := hadd₂ z.2 w.2
    nlinarith [h₁, h₂, hα₁.le, hα₂.le]
  obtain ⟨L, hLdiag, hLle⟩ :=
    exists_extension_of_le_sublinear diagPMap N hN_hom hN_add hdiag_le
  have hLBall :
      ∀ z ∈ Metric.ball (0 : V × V) 1, ‖L z‖ ≤ α₁ * B₁ + α₂ * B₂ := by
    intro z hz
    have hzNorm : ‖z‖ ≤ 1 := le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
    have hz₁ : ‖z.1‖ ≤ 1 := le_trans (norm_fst_le z) hzNorm
    have hz₂ : ‖z.2‖ ≤ 1 := le_trans (norm_snd_le z) hzNorm
    have hz₁_upper : d₁ z.1 ≤ B₁ := (abs_le.mp (hB₁ z.1 hz₁)).2
    have hz₂_upper : d₂ z.2 ≤ B₂ := (abs_le.mp (hB₂ z.2 hz₂)).2
    have hupper : L z ≤ α₁ * B₁ + α₂ * B₂ := by
      calc
        L z ≤ N z := hLle z
        _ ≤ α₁ * B₁ + α₂ * B₂ := by
          dsimp [N]
          nlinarith [hz₁_upper, hz₂_upper, hα₁.le, hα₂.le]
    have hneg₁ : d₁ (-z.1) ≤ B₁ := by
      exact (abs_le.mp (hB₁ (-z.1) (by simpa [norm_neg] using hz₁))).2
    have hneg₂ : d₂ (-z.2) ≤ B₂ := by
      exact (abs_le.mp (hB₂ (-z.2) (by simpa [norm_neg] using hz₂))).2
    have hnegUpper : -L z ≤ α₁ * B₁ + α₂ * B₂ := by
      calc
        -L z = L (-z) := by simpa using (L.map_neg z).symm
        _ ≤ N (-z) := hLle (-z)
        _ ≤ α₁ * B₁ + α₂ * B₂ := by
          dsimp [N]
          nlinarith [hneg₁, hneg₂, hα₁.le, hα₂.le]
    have habs : |L z| ≤ α₁ * B₁ + α₂ * B₂ := abs_le.mpr ⟨by linarith, hupper⟩
    simpa [Real.norm_eq_abs] using habs
  obtain ⟨C, hC⟩ :=
    LinearMap.bound_of_ball_bound zero_lt_one (α₁ * B₁ + α₂ * B₂) L hLBall
  let ℓ₁ : V →ₗ[ℝ] ℝ := L.comp (LinearMap.inl ℝ V V)
  let ℓ₂ : V →ₗ[ℝ] ℝ := L.comp (LinearMap.inr ℝ V V)
  have hℓ₁Ball : ∀ p ∈ Metric.ball (0 : V) 1, ‖ℓ₁ p‖ ≤ α₁ * B₁ := by
    intro p hp
    have hpNorm : ‖p‖ ≤ 1 := le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hp)
    have hpUpper : d₁ p ≤ B₁ := (abs_le.mp (hB₁ p hpNorm)).2
    have hupper : ℓ₁ p ≤ α₁ * B₁ := by
      calc
        ℓ₁ p = L (p, 0) := rfl
        _ ≤ N (p, 0) := hLle (p, (0 : V))
        _ ≤ α₁ * B₁ := by
          dsimp [N]
          nlinarith [hpUpper, hα₁.le]
    have hnegUpper : -ℓ₁ p ≤ α₁ * B₁ := by
      have hneg : d₁ (-p) ≤ B₁ := by
        exact (abs_le.mp (hB₁ (-p) (by simpa [norm_neg] using hpNorm))).2
      calc
        -ℓ₁ p = ℓ₁ (-p) := by simpa [ℓ₁] using (ℓ₁.map_neg p).symm
        _ = L (-p, 0) := rfl
        _ ≤ N (-p, 0) := hLle (-p, (0 : V))
        _ ≤ α₁ * B₁ := by
          dsimp [N]
          nlinarith [hneg, hα₁.le]
    have habs : |ℓ₁ p| ≤ α₁ * B₁ := abs_le.mpr ⟨by linarith, hupper⟩
    simpa [Real.norm_eq_abs] using habs
  have hℓ₂Ball : ∀ p ∈ Metric.ball (0 : V) 1, ‖ℓ₂ p‖ ≤ α₂ * B₂ := by
    intro p hp
    have hpNorm : ‖p‖ ≤ 1 := le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hp)
    have hpUpper : d₂ p ≤ B₂ := (abs_le.mp (hB₂ p hpNorm)).2
    have hupper : ℓ₂ p ≤ α₂ * B₂ := by
      calc
        ℓ₂ p = L (0, p) := rfl
        _ ≤ N (0, p) := hLle ((0 : V), p)
        _ ≤ α₂ * B₂ := by
          dsimp [N]
          nlinarith [hpUpper, hα₂.le]
    have hnegUpper : -ℓ₂ p ≤ α₂ * B₂ := by
      have hneg : d₂ (-p) ≤ B₂ := by
        exact (abs_le.mp (hB₂ (-p) (by simpa [norm_neg] using hpNorm))).2
      calc
        -ℓ₂ p = ℓ₂ (-p) := by simpa [ℓ₂] using (ℓ₂.map_neg p).symm
        _ = L (0, -p) := rfl
        _ ≤ N (0, -p) := hLle ((0 : V), -p)
        _ ≤ α₂ * B₂ := by
          dsimp [N]
          nlinarith [hneg, hα₂.le]
    have habs : |ℓ₂ p| ≤ α₂ * B₂ := abs_le.mpr ⟨by linarith, hupper⟩
    simpa [Real.norm_eq_abs] using habs
  obtain ⟨C₁, hC₁⟩ := LinearMap.bound_of_ball_bound zero_lt_one (α₁ * B₁) ℓ₁ hℓ₁Ball
  obtain ⟨C₂, hC₂⟩ := LinearMap.bound_of_ball_bound zero_lt_one (α₂ * B₂) ℓ₂ hℓ₂Ball
  let L₁ : V →L[ℝ] ℝ := ℓ₁.mkContinuousOfExistsBound ⟨C₁, hC₁⟩
  let L₂ : V →L[ℝ] ℝ := ℓ₂.mkContinuousOfExistsBound ⟨C₂, hC₂⟩
  let u₁ : V := (InnerProductSpace.toDual ℝ V).symm L₁
  let u₂ : V := (InnerProductSpace.toDual ℝ V).symm L₂
  have hu₁_eq : ∀ p : V, inner ℝ u₁ p = L (p, 0) := by
    intro p
    calc
      inner ℝ u₁ p = L₁ p := by
        simpa [u₁] using
          (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := V) (x := p) (y := L₁))
      _ = ℓ₁ p := by
        simpa [L₁] using
          (LinearMap.mkContinuousOfExistsBound_apply (f := ℓ₁) ⟨C₁, hC₁⟩ p)
      _ = L (p, 0) := rfl
  have hu₂_eq : ∀ p : V, inner ℝ u₂ p = L (0, p) := by
    intro p
    calc
      inner ℝ u₂ p = L₂ p := by
        simpa [u₂] using
          (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := V) (x := p) (y := L₂))
      _ = ℓ₂ p := by
        simpa [L₂] using
          (LinearMap.mkContinuousOfExistsBound_apply (f := ℓ₂) ⟨C₂, hC₂⟩ p)
      _ = L (0, p) := rfl
  have hu₁_pair : ∀ p : V, inner ℝ u₁ p ≤ α₁ * d₁ p := by
    intro p
    have hdom : L (p, 0) ≤ α₁ * d₁ p := by
      simpa [N, hzero₂] using hLle (p, (0 : V))
    simpa [hu₁_eq p] using hdom
  have hu₂_pair : ∀ p : V, inner ℝ u₂ p ≤ α₂ * d₂ p := by
    intro p
    have hdom : L (0, p) ≤ α₂ * d₂ p := by
      simpa [N, hzero₁] using hLle ((0 : V), p)
    simpa [hu₂_eq p] using hdom
  have hsum_pair : ∀ p : V, inner ℝ (u₁ + u₂) p = inner ℝ g p := by
    intro p
    have hpdiag : (p, p) ∈ diag := ⟨p, rfl⟩
    have hdiagEq : L (p, p) = inner ℝ g p := by
      simpa [diagPMap] using hLdiag ⟨(p, p), hpdiag⟩
    calc
      inner ℝ (u₁ + u₂) p = inner ℝ u₁ p + inner ℝ u₂ p := by
        rw [inner_add_left]
      _ = L (p, 0) + L (0, p) := by rw [hu₁_eq p, hu₂_eq p]
      _ = L (p, p) := by
        symm
        have hmap := L.map_add (p, (0 : V)) ((0 : V), p)
        simpa using hmap
      _ = inner ℝ g p := hdiagEq
  have hsum : u₁ + u₂ = g := by
    apply ext_inner_right ℝ
    intro p
    exact hsum_pair p
  have hu₁_mem :
      u₁ ∈ α₁ • ∂ (fun p : V ↦ ((d₁ p : ℝ) : WithTop ℝ))(0) := by
    let φ₁ : V → WithTop ℝ := fun p ↦ ((d₁ p : ℝ) : WithTop ℝ)
    have hu₁_base :
        u₁ ∈ ∂ (fun p : V ↦ (((α₁ * d₁ p : ℝ) : WithTop ℝ)))(0) := by
      exact mem_subdifferential_of_pairing_le_originModel
        (d := fun p : V ↦ α₁ * d₁ p)
        (g := u₁)
        (by simp [hzero₁])
        hu₁_pair
    have hu₁_scaled :
        u₁ ∈ ∂ (((α₁ : WithTop ℝ) • φ₁))(0) := by
      simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using hu₁_base
    rw [subdifferential_pos_smul_eq φ₁ hα₁] at hu₁_scaled
    exact hu₁_scaled
  have hu₂_mem :
      u₂ ∈ α₂ • ∂ (fun p : V ↦ ((d₂ p : ℝ) : WithTop ℝ))(0) := by
    let φ₂ : V → WithTop ℝ := fun p ↦ ((d₂ p : ℝ) : WithTop ℝ)
    have hu₂_base :
        u₂ ∈ ∂ (fun p : V ↦ (((α₂ * d₂ p : ℝ) : WithTop ℝ)))(0) := by
      exact mem_subdifferential_of_pairing_le_originModel
        (d := fun p : V ↦ α₂ * d₂ p)
        (g := u₂)
        (by simp [hzero₂])
        hu₂_pair
    have hu₂_scaled :
        u₂ ∈ ∂ (((α₂ : WithTop ℝ) • φ₂))(0) := by
      simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using hu₂_base
    rw [subdifferential_pos_smul_eq φ₂ hα₂] at hu₂_scaled
    exact hu₂_scaled
  exact Set.mem_add.2 ⟨u₁, hu₁_mem, u₂, hu₂_mem, hsum⟩

/-- Helper for Lemma 3.1.12: in the doubly-zero branch, the source-facing weighted sum has
singleton zero subdifferential at every interior domain point. -/
lemma subdifferential_weightedAdd_zero_zero_eq_singleton_zero
    {x : V}
    (hx : x ∈ interior (dom (weightedAdd 0 0 f₁ f₂))) :
    ∂ (weightedAdd 0 0 f₁ f₂)(x) = ({(0 : V)} : Set V) := by
  -- Rewrite the zero-weight sum as a `⊤`-extension of the zero function on the common domain.
  have hxInter : x ∈ interior (dom f₁ ∩ dom f₂) := by
    simpa [interior_effectiveDomain_weightedAdd_eq_inter] using hx
  rw [weightedAdd_zero_zero_eq_topExtension_zero,
    subdifferential_topExtension_eq_constrainedSubdifferential]
  simpa [interior_effectiveDomain_weightedAdd_eq_inter] using
    constrainedSubdifferential_zero_eq_singleton_zero (dom f₁ ∩ dom f₂) hxInter

/-- Helper for Lemma 3.1.12: in the zero-left positive-right branch, the source-facing
subdifferential is the constrained subdifferential of the surviving scaled summand. -/
lemma subdifferential_weightedAdd_zero_left_eq_constrained_of_pos
    (f₁ f₂ : V → WithTop ℝ)
    (hα₂ : 0 < α₂) {x : V} :
    ∂ (weightedAdd 0 α₂ f₁ f₂)(x) =
      ∂[dom f₁] (((α₂ : WithTop ℝ) • f₂))(x) := by
  -- Route correction: rewrite the source-facing branch as a `⊤`-extension first, so the
  -- remaining zero-weight work is a clean constrained-versus-unconstrained comparison.
  rw [weightedAdd_zero_left_eq_topExtension_of_pos f₁ f₂ hα₂,
    subdifferential_topExtension_eq_constrainedSubdifferential]

/-- Helper for Lemma 3.1.12: in the positive-left zero-right branch, the source-facing
subdifferential is the constrained subdifferential of the surviving scaled summand. -/
lemma subdifferential_weightedAdd_zero_right_eq_constrained_of_pos
    (f₁ f₂ : V → WithTop ℝ)
    (hα₁ : 0 < α₁) {x : V} :
    ∂ (weightedAdd α₁ 0 f₁ f₂)(x) =
      ∂[dom f₂] (((α₁ : WithTop ℝ) • f₁))(x) := by
  -- Route correction: rewrite the source-facing branch as a `⊤`-extension first, so the
  -- remaining zero-weight work is a clean constrained-versus-unconstrained comparison.
  rw [weightedAdd_zero_right_eq_topExtension_of_pos f₁ f₂ hα₁,
    subdifferential_topExtension_eq_constrainedSubdifferential]

/-- Helper for Lemma 3.1.12: the reverse weighted-sum subdifferential inclusion is the remaining
separation step once the forward inclusion and interior-domain transport are in place. -/
lemma subdifferential_nonneg_weighted_add_reverse_subset_of_pos
    (hf₁ : ClosedConvexFunction f₁)
    (hf₂ : ClosedConvexFunction f₂)
    (hα₁ : 0 < α₁)
    (hα₂ : 0 < α₂)
    {x : V}
    (hx : x ∈ interior (dom ((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂))) :
    ∂ (((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂))(x) ⊆
      α₁ • ∂ f₁(x) + α₂ • ∂ f₂(x) := by
  have hxInter : x ∈ interior (dom f₁) ∩ interior (dom f₂) := by
    rw [interior_effectiveDomain_nonneg_weighted_add_eq_of_pos hα₁ hα₂] at hx
    exact hx
  rcases existsDirectionalSlopeChoice_of_mem_interior hf₁ hxInter.1 with
    ⟨d₁, hdom₁, hsec₁⟩
  rcases existsDirectionalSlopeChoice_of_mem_interior hf₂ hxInter.2 with
    ⟨d₂, hdom₂, hsec₂⟩
  rcases directionalSlopeChoice_isSublinear hf₁ hxInter.1 hdom₁ hsec₁ with
    ⟨hzero₁, hhom₁, hadd₁⟩
  rcases directionalSlopeChoice_isSublinear hf₂ hxInter.2 hdom₂ hsec₂ with
    ⟨hzero₂, hhom₂, hadd₂⟩
  have hbound₁ :
      ∃ B₁ : ℝ, 0 ≤ B₁ ∧ ∀ p : V, ‖p‖ ≤ 1 → |d₁ p| ≤ B₁ :=
    directionalSlopeChoice_abs_le_on_unitBall hf₁ hxInter.1 hdom₁ hsec₁
  have hbound₂ :
      ∃ B₂ : ℝ, 0 ≤ B₂ ∧ ∀ p : V, ‖p‖ ≤ 1 → |d₂ p| ≤ B₂ :=
    directionalSlopeChoice_abs_le_on_unitBall hf₂ hxInter.2 hdom₂ hsec₂
  let d : V → ℝ := fun p ↦ α₁ * d₁ p + α₂ * d₂ p
  have hdom :
      ∀ p : V,
        ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x + α • p ∈ dom (((α₁ : WithTop ℝ) • f₁) + ((α₂ : WithTop ℝ) • f₂)) := by
    intro p
    filter_upwards [hdom₁ p, hdom₂ p] with α hα₁_dom hα₂_dom
    have hmem : x + α • p ∈ dom (((α₁ : WithTop ℝ) • f₁) + ((α₂ : WithTop ℝ) • f₂)) := by
      rw [withTopEffectiveDomain_nonneg_weighted_add_eq_inter_of_pos hα₁ hα₂]
      exact ⟨hα₁_dom, hα₂_dom⟩
    exact hmem
  have hxScaled₁ : x ∈ dom (((α₁ : WithTop ℝ) • f₁)) := by
    exact (mem_dom_smul_iff_of_pos f₁ hα₁).2 (interior_subset hxInter.1)
  have hxScaled₂ : x ∈ dom (((α₂ : WithTop ℝ) • f₂)) := by
    exact (mem_dom_smul_iff_of_pos f₂ hα₂).2 (interior_subset hxInter.2)
  have hscaled₁ : ClosedConvexFunction (((α₁ : WithTop ℝ) • f₁)) :=
    ClosedConvexFunction.pos_smul f₁ hf₁ hα₁
  have hscaled₂ : ClosedConvexFunction (((α₂ : WithTop ℝ) • f₂)) :=
    ClosedConvexFunction.pos_smul f₂ hf₂ hα₂
  have hxSumReal :
      withTopRealPart (((α₁ : WithTop ℝ) • f₁) + ((α₂ : WithTop ℝ) • f₂)) x =
        α₁ * withTopRealPart f₁ x + α₂ * withTopRealPart f₂ x := by
    calc
      withTopRealPart (((α₁ : WithTop ℝ) • f₁) + ((α₂ : WithTop ℝ) • f₂)) x
          =
            withTopRealPart (((α₁ : WithTop ℝ) • f₁) : V → WithTop ℝ) x +
              withTopRealPart (((α₂ : WithTop ℝ) • f₂) : V → WithTop ℝ) x := by
                simpa using
                  ClosedConvexOn.withTopRealPart_add_of_mem_inter
                    hscaled₁ hscaled₂ ⟨hxScaled₁, hxScaled₂⟩
      _ = α₁ * withTopRealPart f₁ x + α₂ * withTopRealPart f₂ x := by
            rw [ClosedConvexOn.withTopRealPart_smul_of_mem_feasible,
              ClosedConvexOn.withTopRealPart_smul_of_mem_feasible]
  have hsec :
      ∀ p : V,
        Filter.Tendsto
          (fun α : ℝ ↦
            (withTopRealPart
                (((α₁ : WithTop ℝ) • f₁) + ((α₂ : WithTop ℝ) • f₂))
                (x + α • p) -
              withTopRealPart
                (((α₁ : WithTop ℝ) • f₁) + ((α₂ : WithTop ℝ) • f₂)) x) / α)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (d p)) := by
    intro p
    have hscaledSec₁ :
        Filter.Tendsto
          (fun α : ℝ ↦ α₁ *
            ((withTopRealPart f₁ (x + α • p) - withTopRealPart f₁ x) / α))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (α₁ * d₁ p)) :=
      (hsec₁ p).const_mul α₁
    have hscaledSec₂ :
        Filter.Tendsto
          (fun α : ℝ ↦ α₂ *
            ((withTopRealPart f₂ (x + α • p) - withTopRealPart f₂ x) / α))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (α₂ * d₂ p)) :=
      (hsec₂ p).const_mul α₂
    have heq :
        (fun α : ℝ ↦
          (withTopRealPart
              (((α₁ : WithTop ℝ) • f₁) + ((α₂ : WithTop ℝ) • f₂))
              (x + α • p) -
            withTopRealPart
              (((α₁ : WithTop ℝ) • f₁) + ((α₂ : WithTop ℝ) • f₂)) x) / α) =ᶠ[nhdsWithin
                (0 : ℝ) (Set.Ioi 0)]
          fun α : ℝ ↦
            α₁ * ((withTopRealPart f₁ (x + α • p) - withTopRealPart f₁ x) / α) +
              α₂ * ((withTopRealPart f₂ (x + α • p) - withTopRealPart f₂ x) / α) := by
      have hpos :
          ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), 0 < α := by
        simpa using
          (eventually_mem_nhdsWithin :
            ∀ᶠ α : ℝ in 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ), α ∈ Set.Ioi (0 : ℝ))
      filter_upwards [hdom₁ p, hdom₂ p, hpos] with α hα₁_dom hα₂_dom hα_pos
      have hyScaled₁ : x + α • p ∈ dom (((α₁ : WithTop ℝ) • f₁)) := by
        exact (mem_dom_smul_iff_of_pos f₁ hα₁).2 hα₁_dom
      have hyScaled₂ : x + α • p ∈ dom (((α₂ : WithTop ℝ) • f₂)) := by
        exact (mem_dom_smul_iff_of_pos f₂ hα₂).2 hα₂_dom
      have hySumReal :
          withTopRealPart
              (((α₁ : WithTop ℝ) • f₁) + ((α₂ : WithTop ℝ) • f₂))
              (x + α • p) =
            α₁ * withTopRealPart f₁ (x + α • p) +
              α₂ * withTopRealPart f₂ (x + α • p) := by
        calc
          withTopRealPart
              (((α₁ : WithTop ℝ) • f₁) + ((α₂ : WithTop ℝ) • f₂))
              (x + α • p)
              =
                withTopRealPart (((α₁ : WithTop ℝ) • f₁) : V → WithTop ℝ) (x + α • p) +
                  withTopRealPart (((α₂ : WithTop ℝ) • f₂) : V → WithTop ℝ) (x + α • p) := by
                    simpa using
                      ClosedConvexOn.withTopRealPart_add_of_mem_inter
                        hscaled₁ hscaled₂ ⟨hyScaled₁, hyScaled₂⟩
          _ =
              α₁ * withTopRealPart f₁ (x + α • p) +
                α₂ * withTopRealPart f₂ (x + α • p) := by
                  rw [ClosedConvexOn.withTopRealPart_smul_of_mem_feasible,
                    ClosedConvexOn.withTopRealPart_smul_of_mem_feasible]
      rw [hySumReal, hxSumReal]
      field_simp [hα_pos.ne']
      ring
    have hsumScaled :=
      hscaledSec₁.add hscaledSec₂
    simpa [d] using hsumScaled.congr' heq.symm
  intro g hg
  have hgModel : g ∈ ∂ (fun p : V ↦ ((d p : ℝ) : WithTop ℝ))(0) := by
    rw [subdifferential_directionalSlopeChoice_at_zero_eq_subdifferential
        (((α₁ : WithTop ℝ) • f₁) + ((α₂ : WithTop ℝ) • f₂))
        (ClosedConvexFunction.nonneg_weighted_add f₁ f₂ hf₁ hf₂ hα₁.le hα₂.le)
        hx hdom hsec]
    exact hg
  have hgSplit :
      g ∈
        α₁ • ∂ (fun p : V ↦ ((d₁ p : ℝ) : WithTop ℝ))(0) +
          α₂ • ∂ (fun p : V ↦ ((d₂ p : ℝ) : WithTop ℝ))(0) :=
    mem_weighted_originModel_sum_of_mem_subdifferential
      hα₁ hα₂ hzero₁ hzero₂ hhom₁ hhom₂ hadd₁ hadd₂ hbound₁ hbound₂ hgModel
  rw [subdifferential_directionalSlopeChoice_at_zero_eq_subdifferential
      f₁ hf₁ hxInter.1 hdom₁ hsec₁,
    subdifferential_directionalSlopeChoice_at_zero_eq_subdifferential
      f₂ hf₂ hxInter.2 hdom₂ hsec₂] at hgSplit
  exact hgSplit

/-- Lemma 3.1.12: if `f₁` and `f₂` are closed convex and `α₁, α₂ ≥ 0`, then for the
book-style restricted-domain weighted sum `f = weightedAdd α₁ α₂ f₁ f₂` one has
`interior (dom f) = interior (dom f₁) ∩ interior (dom f₂)`, and at every
`x ∈ interior (dom f)` the subdifferential of `f` equals the Minkowski sum of the scaled
pointwise subdifferentials. -/
theorem subdifferential_nonneg_weighted_add_eq
    (hf₁ : ClosedConvexFunction f₁)
    (hf₂ : ClosedConvexFunction f₂)
    (hα₁ : 0 ≤ α₁)
    (hα₂ : 0 ≤ α₂)
    {x : V}
    (hx : x ∈ interior (dom (weightedAdd α₁ α₂ f₁ f₂))) :
    ∂ (weightedAdd α₁ α₂ f₁ f₂)(x) =
      α₁ • ∂ f₁(x) + α₂ • ∂ f₂(x) := by
  -- Route correction: the positive-weight branch is now fully reduced to the canonical pointwise
  -- sum, so the only remaining source-facing work is the zero-weight restriction analysis.
  have hpositive :
      0 < α₁ → 0 < α₂ →
        ∂ (weightedAdd α₁ α₂ f₁ f₂)(x) =
          α₁ • ∂ f₁(x) + α₂ • ∂ f₂(x) := by
    intro hα₁_pos hα₂_pos
    have hx' : x ∈ interior (dom ((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂)) := by
      -- Rewrite both interior-domain descriptions to the same intersection of summand interiors.
      rw [interior_effectiveDomain_nonneg_weighted_add_eq_of_pos hα₁_pos hα₂_pos]
      simpa [interior_effectiveDomain_weightedAdd_eq_inter] using hx
    -- Once the source-facing sum matches the canonical pointwise sum, the positive branch is just
    -- forward plus reverse inclusion on the canonical weighted sum.
    have hcanon :
        ∂ (((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂))(x) =
          α₁ • ∂ f₁(x) + α₂ • ∂ f₂(x) := by
      refine Set.Subset.antisymm ?_ ?_
      · exact
          subdifferential_nonneg_weighted_add_reverse_subset_of_pos
            hf₁ hf₂ hα₁_pos hα₂_pos hx'
      · exact weightedSubdifferential_subset hα₁_pos hα₂_pos
    simpa [weightedAdd_eq_pointwise_of_pos f₁ f₂ hα₁_pos hα₂_pos] using hcanon
  rcases eq_or_lt_of_le hα₁ with rfl | hα₁_pos
  · rcases eq_or_lt_of_le hα₂ with rfl | hα₂_pos
    · have hxInter : x ∈ interior (dom f₁) ∩ interior (dom f₂) := by
        simpa [interior_effectiveDomain_weightedAdd_eq_inter] using hx
      have hnonempty₁ : (∂ f₁(x)).Nonempty :=
        subdifferential_nonempty_of_mem_interior hf₁ hxInter.1
      have hnonempty₂ : (∂ f₂(x)).Nonempty :=
        subdifferential_nonempty_of_mem_interior hf₂ hxInter.2
      -- When both coefficients vanish, every scalar-multiple term collapses to `{0}`.
      rw [subdifferential_weightedAdd_zero_zero_eq_singleton_zero hx,
        Set.zero_smul_set hnonempty₁, Set.zero_smul_set hnonempty₂]
      ext g
      simp
    · have hxInter : x ∈ interior (dom f₁) ∩ interior (dom f₂) := by
        simpa [interior_effectiveDomain_weightedAdd_eq_inter] using hx
      have hxScaled :
          x ∈ interior (dom (((α₂ : WithTop ℝ) • f₂))) := by
        have hdom :
            dom (((α₂ : WithTop ℝ) • f₂)) = dom f₂ := by
          ext y
          simpa using (mem_dom_smul_iff_of_pos f₂ hα₂_pos : y ∈ dom (((α₂ : WithTop ℝ) • f₂)) ↔ y ∈ dom f₂)
        simpa [hdom] using hxInter.2
      have hnonempty₁ : (∂ f₁(x)).Nonempty :=
        subdifferential_nonempty_of_mem_interior hf₁ hxInter.1
      -- Restrict the zero-left branch back to the unconstrained scaled subdifferential.
      rw [subdifferential_weightedAdd_zero_left_eq_constrained_of_pos f₁ f₂ hα₂_pos]
      rw [constrainedSubdifferential_eq_subdifferential_of_mem_interior
          (((α₂ : WithTop ℝ) • f₂))
          (ClosedConvexFunction.pos_smul f₂ hf₂ hα₂_pos)
          hxInter.1 hxScaled]
      rw [subdifferential_pos_smul_eq f₂ hα₂_pos]
      rw [Set.zero_smul_set hnonempty₁]
      simp
  · rcases eq_or_lt_of_le hα₂ with rfl | hα₂_pos
    · have hxInter : x ∈ interior (dom f₁) ∩ interior (dom f₂) := by
        simpa [interior_effectiveDomain_weightedAdd_eq_inter] using hx
      have hxScaled :
          x ∈ interior (dom (((α₁ : WithTop ℝ) • f₁))) := by
        have hdom :
            dom (((α₁ : WithTop ℝ) • f₁)) = dom f₁ := by
          ext y
          simpa using (mem_dom_smul_iff_of_pos f₁ hα₁_pos : y ∈ dom (((α₁ : WithTop ℝ) • f₁)) ↔ y ∈ dom f₁)
        simpa [hdom] using hxInter.1
      have hnonempty₂ : (∂ f₂(x)).Nonempty :=
        subdifferential_nonempty_of_mem_interior hf₂ hxInter.2
      -- Symmetrically, the zero-right branch reduces to the scaled first summand.
      rw [subdifferential_weightedAdd_zero_right_eq_constrained_of_pos f₁ f₂ hα₁_pos]
      rw [constrainedSubdifferential_eq_subdifferential_of_mem_interior
          (((α₁ : WithTop ℝ) • f₁))
          (ClosedConvexFunction.pos_smul f₁ hf₁ hα₁_pos)
          hxInter.2 hxScaled]
      rw [subdifferential_pos_smul_eq f₁ hα₁_pos]
      rw [Set.zero_smul_set hnonempty₂]
      simp
    · exact hpositive hα₁_pos hα₂_pos

/-- Positive-weight corollary of Lemma 3.1.12: when both weights are strictly positive, the
same subdifferential formula can be stated using the interior of the effective domain of the
canonical weighted pointwise sum. -/
-- Proof sketch: combine the already-proved forward inclusion
-- `weightedSubdifferential_subset` with the reverse inclusion
-- `subdifferential_nonneg_weighted_add_reverse_subset_of_pos`.
theorem subdifferential_nonneg_weighted_add_eq_of_pos
    (hf₁ : ClosedConvexFunction f₁)
    (hf₂ : ClosedConvexFunction f₂)
    (hα₁ : 0 < α₁)
    (hα₂ : 0 < α₂)
    {x : V}
    (hx : x ∈ interior (dom ((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂))) :
    ∂ (((α₁ : WithTop ℝ) • f₁ + (α₂ : WithTop ℝ) • f₂))(x) =
      α₁ • ∂ f₁(x) + α₂ • ∂ f₂(x) := by
  -- The positive-weight corollary is exactly the forward inclusion plus the remaining reverse
  -- inclusion proved on the canonical weighted pointwise sum.
  refine Set.Subset.antisymm ?_ ?_
  · exact subdifferential_nonneg_weighted_add_reverse_subset_of_pos hf₁ hf₂ hα₁ hα₂ hx
  · exact weightedSubdifferential_subset hα₁ hα₂

end Subdifferential

end WeightedAdd

end

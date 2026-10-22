/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Lemma_1_24
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Fact_6_13
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12

-- Declarations for this item will be appended below by the statement pipeline.

open Set Topology
open scoped Pointwise

universe u

noncomputable section

namespace ERealFunction

namespace Set

abbrev core {E : Type*} [AddCommGroup E] [Module ℝ E] (C : _root_.Set E) : _root_.Set E :=
  Proposition612Absorbent.Set.core C

theorem mem_core_iff {E : Type*} [AddCommGroup E] [Module ℝ E]
    {C : _root_.Set E} {x : E} :
    x ∈ core C ↔
      ∀ y : E, ∃ ε > (0 : ℝ), ∀ t : ℝ, t ∈ _root_.Set.Icc (0 : ℝ) ε →
        x + t • y ∈ C :=
  Proposition612Absorbent.Set.mem_core_iff

end Set

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Fact 9.17: any prescribed vertical gap can be realized by real epigraph heights
above two effective-domain points. -/
private lemma exists_epigraph_heights_with_prescribed_gap
    {f g : H → Set.Ioi (⊥ : EReal)} {x y : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain g) (t : ℝ) :
    ∃ ξ η : ℝ,
      (x, ξ) ∈ epigraph (fun z : H ↦ (f z : EReal)) ∧
      (y, η) ∈ epigraph (fun z : H ↦ (g z : EReal)) ∧
      ξ - η = t := by
  -- Pick real heights strictly above the two finite values.
  rcases EReal.lt_iff_exists_real_btwn.mp ((mem_effectiveDomain_iff).mp hx) with
    ⟨ξ0, hfx_lt, -⟩
  rcases EReal.lt_iff_exists_real_btwn.mp ((mem_effectiveDomain_iff).mp hy) with
    ⟨η0, hgy_lt, -⟩
  set η : ℝ := max η0 (ξ0 - t)
  set ξ : ℝ := t + η
  have hξ0_le_ξ : ξ0 ≤ ξ := by
    dsimp [ξ, η]
    linarith [le_max_right η0 (ξ0 - t)]
  have hη0_le_η : η0 ≤ η := by
    dsimp [η]
    exact le_max_left _ _
  refine ⟨ξ, η, ?_, ?_, by simp [ξ]⟩
  · -- The first chosen height lies above `f x`.
    rw [mem_epigraph_iff]
    calc
      (f x : EReal) ≤ (ξ0 : EReal) := le_of_lt hfx_lt
      _ ≤ (ξ : EReal) := by
        exact_mod_cast hξ0_le_ξ
  · -- The second chosen height lies above `g y`.
    rw [mem_epigraph_iff]
    calc
      (g y : EReal) ≤ (η0 : EReal) := le_of_lt hgy_lt
      _ ≤ (η : EReal) := by
        exact_mod_cast hη0_le_η

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Fact 9.17: subtracting the real-height epigraphs projects to the difference of the
effective domains with an arbitrary real vertical coordinate. -/
private lemma epigraph_sub_eq_sub_effectiveDomain_prod_univ
    (f g : H → Set.Ioi (⊥ : EReal)) :
    epigraph (fun z : H ↦ (f z : EReal)) - epigraph (fun z : H ↦ (g z : EReal)) =
      (effectiveDomain f - effectiveDomain g) ×ˢ (Set.univ : Set ℝ) := by
  ext p
  rcases p with ⟨z, t⟩
  constructor
  · intro hp
    rcases hp with ⟨a, ha, b, hb, hab⟩
    rcases a with ⟨x, ξ⟩
    rcases b with ⟨y, η⟩
    have hx : x ∈ effectiveDomain f := by
      rw [mem_effectiveDomain_iff]
      rw [mem_epigraph_iff] at ha
      exact lt_of_le_of_lt ha (EReal.coe_lt_top ξ)
    have hy : y ∈ effectiveDomain g := by
      rw [mem_effectiveDomain_iff]
      rw [mem_epigraph_iff] at hb
      exact lt_of_le_of_lt hb (EReal.coe_lt_top η)
    change (x - y, ξ - η) = (z, t) at hab
    injection hab with hz ht
    subst hz ht
    exact ⟨⟨x, hx, y, hy, rfl⟩, by simp⟩
  · intro hp
    simp only [Set.mem_prod, Set.mem_univ, and_true] at hp
    rcases hp with ⟨x, hx, y, hy, rfl⟩
    rcases exists_epigraph_heights_with_prescribed_gap hx hy t with ⟨ξ, η, hξ, hη, hgap⟩
    refine ⟨(x, ξ), hξ, (y, η), hη, ?_⟩
    change (x - y, ξ - η) = (x - y, t)
    simp [hgap]

omit [CompleteSpace H] in
/-- Helper for Fact 9.17: taking the product with the full real line preserves the core in the
first coordinate. -/
private lemma core_prod_univ_eq_prod_core (S : Set H) :
    Set.core (S ×ˢ (Set.univ : Set ℝ)) = Set.core S ×ˢ (Set.univ : Set ℝ) := by
  ext p
  rcases p with ⟨x, r⟩
  constructor
  · intro hp
    simp only [Set.mem_prod, Set.mem_univ, and_true]
    rw [Set.mem_core_iff] at hp ⊢
    intro y
    rcases hp (y, 0) with ⟨ε, hε, hsegment⟩
    refine ⟨ε, hε, ?_⟩
    intro t ht
    have hpair := hsegment t ht
    simpa using hpair
  · intro hp
    simp only [Set.mem_prod, Set.mem_univ, and_true] at hp ⊢
    rw [Set.mem_core_iff] at hp ⊢
    intro y
    rcases y with ⟨hy, s⟩
    rcases hp hy with ⟨ε, hε, hsegment⟩
    refine ⟨ε, hε, ?_⟩
    intro t ht
    exact ⟨hsegment t ht, by simp⟩

/-- Helper for Fact 9.17: a continuous linear equivalence carries set differences to the
differences of the images. -/
private lemma image_sub_eq_sub_image {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (A B : Set E) :
    e '' (A - B) = e '' A - e '' B := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨a, ha, b, hb, rfl⟩
    exact ⟨e a, ⟨a, ha, rfl⟩, e b, ⟨b, hb, rfl⟩, by simp⟩
  · rintro ⟨u, hu, v, hv, huv⟩
    rcases hu with ⟨a, ha, rfl⟩
    rcases hv with ⟨b, hb, rfl⟩
    refine ⟨a - b, ⟨a, ha, b, hb, rfl⟩, ?_⟩
    simpa using huv

/-- Helper for Fact 9.17: the core commutes with the image of a continuous linear equivalence. -/
private lemma core_image_eq_image_core {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (S : Set E) :
    Set.core (e '' S) = e '' Set.core S := by
  ext y
  constructor
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [Set.mem_core_iff] at hy ⊢
    intro x
    rcases hy (e x) with ⟨ε, hε, hsegment⟩
    refine ⟨ε, hε, ?_⟩
    intro t ht
    rcases hsegment t ht with ⟨z, hz, hzEq⟩
    have hzEq' : e.symm y + t • x = z := by
      have := congrArg e.symm hzEq
      simpa using this.symm
    simpa [hzEq'] using hz
  · rintro ⟨x, hx, rfl⟩
    rw [Set.mem_core_iff] at hx ⊢
    intro y
    rcases hx (e.symm y) with ⟨ε, hε, hsegment⟩
    refine ⟨ε, hε, ?_⟩
    intro t ht
    refine ⟨x + t • e.symm y, hsegment t ht, ?_⟩
    simp

-- Proof sketch: move from the generally nonclosed effective domains to the closed convex
-- real-height epigraphs, apply Fact 6.13 there, rewrite the resulting equality as a product-set
-- statement, and then read off the first coordinate at height `0`.
/-- Fact 9.17: for `f, g ∈ Γ₀(H)` on a real Hilbert space, the interior of the difference of
their effective domains coincides with the core of that difference. -/
theorem interior_sub_effectiveDomain_eq_core_sub_effectiveDomain
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    interior (effectiveDomain f - effectiveDomain g) =
      Set.core (effectiveDomain f - effectiveDomain g) := by
  -- Route correction: `Γ₀` does not imply the effective domains are closed, so the proof runs
  -- through the closed convex epigraphs and the `L²` product structure on `H × ℝ`.
  let F : H → EReal := fun x ↦ (f x : EReal)
  let G : H → EReal := fun x ↦ (g x : EReal)
  let e : (H × ℝ) ≃L[ℝ] WithLp 2 (H × ℝ) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ H ℝ).symm
  let S : Set (H × ℝ) := (effectiveDomain f - effectiveDomain g) ×ˢ (Set.univ : Set ℝ)
  have hF_closed : IsClosed (epigraph F) := by
    -- Lower semicontinuity identifies the real-height epigraph as a closed set.
    exact (lowerSemicontinuous_iff_isClosed_epigraph F).1 hf.1
  have hG_closed : IsClosed (epigraph G) := by
    -- The same closed-epigraph characterization applies to `g`.
    exact (lowerSemicontinuous_iff_isClosed_epigraph G).1 hg.1
  have hF_convex : Convex ℝ (epigraph F) := by
    -- Rewrite the `Γ₀` Jensen inequality into the epigraph characterization.
    refine (convex_epigraph_iff_jensen_on_dom F).2 ?_
    intro x y hx hy α hα0 hα1
    have hx' : x ∈ effectiveDomain f := by
      simpa [F, effectiveDomain, dom] using hx
    have hy' : y ∈ effectiveDomain f := by
      simpa [F, effectiveDomain, dom] using hy
    simpa [F] using hf.2.ineq hx' hy' hα0 hα1
  have hG_convex : Convex ℝ (epigraph G) := by
    -- The same Jensen-to-epigraph route yields convexity for `g`.
    refine (convex_epigraph_iff_jensen_on_dom G).2 ?_
    intro x y hx hy α hα0 hα1
    have hx' : x ∈ effectiveDomain g := by
      simpa [G, effectiveDomain, dom] using hx
    have hy' : y ∈ effectiveDomain g := by
      simpa [G, effectiveDomain, dom] using hy
    simpa [G] using hg.2.ineq hx' hy' hα0 hα1
  have hF_closed' : IsClosed (e '' epigraph F) := by
    -- The product-space equivalence turns image-closedness into a preimage statement.
    rw [e.image_eq_preimage_symm]
    exact hF_closed.preimage e.symm.continuous
  have hG_closed' : IsClosed (e '' epigraph G) := by
    -- The same transport argument applies to the epigraph of `g`.
    rw [e.image_eq_preimage_symm]
    exact hG_closed.preimage e.symm.continuous
  have hF_convex' : Convex ℝ (e '' epigraph F) := by
    -- Convexity is preserved by linear images.
    simpa using hF_convex.linear_image e.toLinearMap
  have hG_convex' : Convex ℝ (e '' epigraph G) := by
    -- Convexity is preserved by linear images for `g` as well.
    simpa using hG_convex.linear_image e.toLinearMap
  have himage_sub :
      e '' (epigraph F - epigraph G) = e '' epigraph F - e '' epigraph G :=
    image_sub_eq_sub_image e _ _
  have himage_core :
      interior (e '' S) = Set.core (e '' S) := by
    -- After transporting to the `L²` product, Fact 6.13 applies to the two lifted epigraphs.
    calc
      interior (e '' S) = interior (e '' (epigraph F - epigraph G)) := by
        rw [epigraph_sub_eq_sub_effectiveDomain_prod_univ]
      _ = interior (e '' epigraph F - e '' epigraph G) := by
        rw [himage_sub]
      _ = Set.core (e '' epigraph F - e '' epigraph G) := by
        exact Proposition612Absorbent.interior_sub_eq_core_sub_of_isClosed_of_convex
          hF_closed' hG_closed' hF_convex' hG_convex'
      _ = Set.core (e '' (epigraph F - epigraph G)) := by
        rw [himage_sub]
      _ = Set.core (e '' S) := by
        rw [epigraph_sub_eq_sub_effectiveDomain_prod_univ]
  have himages : e '' interior S = e '' Set.core S := by
    -- The homeomorphism transports interiors, and the linear equivalence transports cores.
    calc
      e '' interior S = interior (e '' S) := by
        simpa using e.toHomeomorph.image_interior S
      _ = Set.core (e '' S) := himage_core
      _ = e '' Set.core S := core_image_eq_image_core e S
  have hS : interior S = Set.core S := by
    -- Injectivity of the transport map lets us read the equality back in the original product.
    ext p
    constructor
    · intro hp
      have hp' : e p ∈ e '' interior S := ⟨p, hp, rfl⟩
      rw [himages] at hp'
      rcases hp' with ⟨q, hq, hpq⟩
      exact e.injective hpq ▸ hq
    · intro hp
      have hp' : e p ∈ e '' Set.core S := ⟨p, hp, rfl⟩
      rw [← himages] at hp'
      rcases hp' with ⟨q, hq, hpq⟩
      exact e.injective hpq ▸ hq
  have hprod :
      interior (effectiveDomain f - effectiveDomain g) ×ˢ (Set.univ : Set ℝ) =
        Set.core (effectiveDomain f - effectiveDomain g) ×ˢ (Set.univ : Set ℝ) := by
    -- Rewrite the transported product equality back to the base-space difference set.
    calc
      interior (effectiveDomain f - effectiveDomain g) ×ˢ (Set.univ : Set ℝ) =
          interior S := by
            rw [interior_prod_eq]
            simp
      _ = Set.core S := hS
      _ = Set.core (effectiveDomain f - effectiveDomain g) ×ˢ (Set.univ : Set ℝ) := by
            simpa [S] using core_prod_univ_eq_prod_core (effectiveDomain f - effectiveDomain g)
  ext x
  constructor
  · intro hx
    -- A base-space interior point gives a product-space point at height `0`.
    have hpair :
        (x, (0 : ℝ)) ∈ interior (effectiveDomain f - effectiveDomain g) ×ˢ
          (Set.univ : Set ℝ) := by
      exact ⟨hx, by simp⟩
    have hpair' :
        (x, (0 : ℝ)) ∈ Set.core (effectiveDomain f - effectiveDomain g) ×ˢ
          (Set.univ : Set ℝ) := by
      rwa [hprod] at hpair
    simpa using hpair'
  · intro hx
    -- Conversely, a core point also lifts to height `0` and comes back through the same product
    -- equality.
    have hpair :
        (x, (0 : ℝ)) ∈ Set.core (effectiveDomain f - effectiveDomain g) ×ˢ
          (Set.univ : Set ℝ) := by
      exact ⟨hx, by simp⟩
    have hpair' :
        (x, (0 : ℝ)) ∈ interior (effectiveDomain f - effectiveDomain g) ×ˢ
          (Set.univ : Set ℝ) := by
      rwa [← hprod] at hpair
    simpa using hpair'

end ERealFunction

/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Topology

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Helper for Proposition 9.16: this is the Proposition 9.14 segment-limit argument packaged
locally so the boundary proof can use it without importing later chapter files. -/
private lemma tendsto_apply_lineMap_right_zero_of_lowerSemicontinuous_epigraph_convex
    {φ : H × ℝ → Set.Ioi (⊥ : EReal)}
    (hφ_lsc : LowerSemicontinuous (fun z : H × ℝ ↦ (φ z : EReal)))
    (hφ_conv : Convex ℝ (epigraph (fun z : H × ℝ ↦ (φ z : EReal))))
    {x y : H × ℝ} (hx : (φ x : EReal) < ⊤) (hy : (φ y : EReal) < ⊤) :
    Filter.Tendsto (fun α : ℝ ↦ (φ (AffineMap.lineMap x y α) : EReal))
      (𝓝[>] (0 : ℝ)) (𝓝 (φ x : EReal)) := by
  let u : ℝ → EReal := fun α ↦ (φ (AffineMap.lineMap x y α) : EReal)
  let v : ℝ → EReal :=
    fun α ↦ (((1 - α : ℝ) : EReal) * (φ x : EReal) + (α : EReal) * (φ y : EReal))
  have hx_dom : x ∈ dom (fun z : H × ℝ ↦ (φ z : EReal)) := by
    simpa [dom] using hx
  have hy_dom : y ∈ dom (fun z : H × ℝ ↦ (φ z : EReal)) := by
    simpa [dom] using hy
  have hJ := (convex_epigraph_iff_jensen_on_dom (fun z : H × ℝ ↦ (φ z : EReal))).1 hφ_conv
  -- Lower semicontinuity along the segment gives the liminf lower bound at the boundary point.
  have hu_lsc : LowerSemicontinuous u := by
    simpa [u, Function.comp] using
      hφ_lsc.comp (AffineMap.lineMap_continuous (p := x) (q := y))
  have h_liminf : (φ x : EReal) ≤ Filter.liminf u (𝓝[>] (0 : ℝ)) := by
    calc
      (φ x : EReal) = u 0 := by
        simp [u]
      _ ≤ Filter.liminf u (𝓝 (0 : ℝ)) := (hu_lsc.lowerSemicontinuousAt 0).le_liminf
      _ ≤ Filter.liminf u (𝓝[>] (0 : ℝ)) :=
        Filter.liminf_le_liminf_of_le
          (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hα_pos : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), 0 < α := by
    simpa using (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))
  have hα_lt_one : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), α < 1 := by
    exact nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have huv : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), u α ≤ v α := by
    -- Jensen's inequality controls the segment values by the affine majorant.
    filter_upwards [hα_pos, hα_lt_one] with α hα_pos hα_lt_one
    simpa [u, v, AffineMap.lineMap_apply_module, add_comm, mul_comm] using
      hJ hy_dom hx_dom hα_pos hα_lt_one
  have hx_ne_top : (φ x : EReal) ≠ ⊤ := ne_of_lt hx
  have hy_ne_top : (φ y : EReal) ≠ ⊤ := ne_of_lt hy
  have hx_ne_bot : (φ x : EReal) ≠ ⊥ :=
    ne_of_gt (show (⊥ : EReal) < (φ x : EReal) from (φ x).2)
  have hy_ne_bot : (φ y : EReal) ≠ ⊥ :=
    ne_of_gt (show (⊥ : EReal) < (φ y : EReal) from (φ y).2)
  -- The affine majorant is an ordinary real line map after passing to `toReal`.
  have hv_real : Filter.Tendsto
      (fun α : ℝ ↦ AffineMap.lineMap (φ x : EReal).toReal (φ y : EReal).toReal α)
      (𝓝[>] (0 : ℝ)) (𝓝 ((φ x : EReal).toReal)) := by
    simpa using
      (((AffineMap.lineMap_continuous (p := (φ x : EReal).toReal)
          (q := (φ y : EReal).toReal)).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds)
  have hv_tendsto_coe : Filter.Tendsto
      (fun α : ℝ ↦ ((AffineMap.lineMap (φ x : EReal).toReal (φ y : EReal).toReal α : ℝ) : EReal))
      (𝓝[>] (0 : ℝ)) (𝓝 (φ x : EReal)) := by
    have hcoe : Filter.Tendsto
        (fun t : ℝ ↦ (t : EReal)) (𝓝 ((φ x : EReal).toReal)) (𝓝 (φ x : EReal)) := by
      simpa [EReal.coe_toReal hx_ne_top hx_ne_bot] using
        (continuous_coe_real_ereal.tendsto ((φ x : EReal).toReal))
    simpa [Function.comp] using hcoe.comp hv_real
  have hv_eq : ∀ α : ℝ,
      v α = ((AffineMap.lineMap (φ x : EReal).toReal (φ y : EReal).toReal α : ℝ) : EReal) := by
    intro α
    simp [v, AffineMap.lineMap_apply_module, smul_eq_mul, EReal.coe_toReal hx_ne_top hx_ne_bot,
      EReal.coe_toReal hy_ne_top hy_ne_bot, add_comm, mul_comm]
  have hv_tendsto : Filter.Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 (φ x : EReal)) := by
    exact Filter.Tendsto.congr (fun α ↦ (hv_eq α).symm) hv_tendsto_coe
  have h_limsup : Filter.limsup u (𝓝[>] (0 : ℝ)) ≤ (φ x : EReal) := by
    calc
      Filter.limsup u (𝓝[>] (0 : ℝ)) ≤ Filter.limsup v (𝓝[>] (0 : ℝ)) :=
        Filter.limsup_le_limsup huv
      _ = (φ x : EReal) := hv_tendsto.limsup_eq
  exact tendsto_of_le_liminf_of_limsup_le h_liminf h_limsup

/-- Helper for Proposition 9.16: a function in `Γ₀(H × ℝ)` has a convex real-height epigraph. -/
private lemma convex_real_epigraph_of_mem_gammaZero
    {φ : H × ℝ → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H × ℝ)) :
    Convex ℝ (epigraph (fun z : H × ℝ ↦ (φ z : EReal))) := by
  -- Translate the stored Jensen inequality on the effective domain into the Chapter 8 epigraph
  -- characterization used by Proposition 9.14.
  refine (convex_epigraph_iff_jensen_on_dom (fun z : H × ℝ ↦ (φ z : EReal))).2 ?_
  intro x y hx hy α hα hα_lt_one
  have hx' : x ∈ effectiveDomain φ := by
    simpa [effectiveDomain, dom] using hx
  have hy' : y ∈ effectiveDomain φ := by
    simpa [effectiveDomain, dom] using hy
  simpa using hφ.2.ineq hx' hy' hα hα_lt_one

omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
/-- Helper for Proposition 9.16: if the effective domain stays in the closed upper half-space, then
the function takes the value `⊤` at every point with negative second coordinate. -/
private lemma value_eq_top_of_neg_snd_of_effectiveDomain_subset_closedUpperHalfSpace
    {φ : H × ℝ → Set.Ioi (⊥ : EReal)}
    (hdomφ : effectiveDomain φ ⊆ Set.univ ×ˢ Set.Ici (0 : ℝ))
    {x : H} {t : ℝ} (ht : t < 0) :
    (φ (x, t) : EReal) = ⊤ := by
  -- A negative height cannot lie in the effective domain, so `⊤` is the only possible value.
  by_contra hφ_ne_top
  have hφ_finite : (φ (x, t) : EReal) < ⊤ := lt_of_le_of_ne le_top hφ_ne_top
  have hmem : (x, t) ∈ effectiveDomain φ := by
    simpa [mem_effectiveDomain_iff] using hφ_finite
  have hmem_closed : (x, t) ∈ Set.univ ×ˢ Set.Ici (0 : ℝ) := hdomφ hmem
  have ht_nonneg : 0 ≤ t := by
    simpa [Set.mem_prod, Set.mem_univ] using hmem_closed
  exact (not_lt_of_ge ht_nonneg) ht

/-- Helper for Proposition 9.16: a positive-domain witness and Proposition 9.14 force equality at
any boundary point of `f` that already lies in the effective domain of `f`. -/
private lemma boundary_value_eq_of_mem_effectiveDomain
    {f g : H × ℝ → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H × ℝ)) (hg : g ∈ Γ₀(H × ℝ))
    (heq : Set.EqOn f g (Set.univ ×ˢ Set.Ioi (0 : ℝ)))
    {x y : H} {η : ℝ}
    (hyf : (y, η) ∈ effectiveDomain f) (hyg : (y, η) ∈ effectiveDomain g) (hη : 0 < η)
    (hx : (x, (0 : ℝ)) ∈ effectiveDomain f) :
    (g (x, 0) : EReal) < ⊤ ∧ (f (x, 0) : EReal) = (g (x, 0) : EReal) := by
  let line : ℝ → H × ℝ := fun α ↦ AffineMap.lineMap (x, (0 : ℝ)) (y, η) α
  have hx_finite : (f (x, 0) : EReal) < ⊤ := mem_effectiveDomain_iff.mp hx
  have hyf_finite : (f (y, η) : EReal) < ⊤ := mem_effectiveDomain_iff.mp hyf
  have hyg_finite : (g (y, η) : EReal) < ⊤ := mem_effectiveDomain_iff.mp hyg
  -- Proposition 9.14 gives the right-limit of `f` along the boundary-to-interior segment.
  have hf_tendsto :
      Filter.Tendsto (fun α : ℝ ↦ (f (line α) : EReal)) (𝓝[>] (0 : ℝ)) (𝓝 (f (x, 0) : EReal)) := by
    simpa [line] using
      (tendsto_apply_lineMap_right_zero_of_lowerSemicontinuous_epigraph_convex
        (φ := f) hf.1 (convex_real_epigraph_of_mem_gammaZero hf)
        (x := (x, (0 : ℝ))) (y := (y, η)) hx_finite hyf_finite)
  have hline_eq :
      Set.EqOn
        (fun α : ℝ ↦ (f (line α) : EReal))
        (fun α : ℝ ↦ (g (line α) : EReal))
        (Set.Ioi (0 : ℝ)) := by
    intro α hα
    have hline_mem : line α ∈ Set.univ ×ˢ Set.Ioi (0 : ℝ) := by
      have hηα : 0 < η * α := mul_pos hη hα
      simp [line, AffineMap.lineMap_apply_module, Set.mem_prod, Set.mem_univ, hηα, mul_comm]
    simpa using congrArg (fun z : Set.Ioi (⊥ : EReal) ↦ (z : EReal)) (heq hline_mem)
  -- On the open upper half-space the two segment traces coincide, so `g` has the same right-limit.
  have hg_to_f_tendsto :
      Filter.Tendsto (fun α : ℝ ↦ (g (line α) : EReal)) (𝓝[>] (0 : ℝ)) (𝓝 (f (x, 0) : EReal)) :=
    Filter.Tendsto.congr' (hline_eq.eventuallyEq_of_mem self_mem_nhdsWithin) hf_tendsto
  have hg_line_lsc : LowerSemicontinuous (fun α : ℝ ↦ (g (line α) : EReal)) := by
    -- Lower semicontinuity is preserved by the continuous line map.
    simpa [line, Function.comp] using
      hg.1.comp (AffineMap.lineMap_continuous (p := (x, (0 : ℝ))) (q := (y, η)))
  have hg_le_liminf :
      (g (x, 0) : EReal) ≤ Filter.liminf (fun α : ℝ ↦ (g (line α) : EReal)) (𝓝[>] (0 : ℝ)) := by
    -- Lower semicontinuity compares the boundary value with the right-hand liminf.
    calc
      (g (x, 0) : EReal) = (fun α : ℝ ↦ (g (line α) : EReal)) 0 := by
        simp [line]
      _ ≤ Filter.liminf (fun α : ℝ ↦ (g (line α) : EReal)) (𝓝 (0 : ℝ)) :=
        (hg_line_lsc.lowerSemicontinuousAt 0).le_liminf
      _ ≤ Filter.liminf (fun α : ℝ ↦ (g (line α) : EReal)) (𝓝[>] (0 : ℝ)) :=
        Filter.liminf_le_liminf_of_le
          (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hgx_le_hfx : (g (x, 0) : EReal) ≤ (f (x, 0) : EReal) := by
    calc
      (g (x, 0) : EReal) ≤ Filter.liminf (fun α : ℝ ↦ (g (line α) : EReal)) (𝓝[>] (0 : ℝ)) :=
        hg_le_liminf
      _ = (f (x, 0) : EReal) := by
        simpa using hg_to_f_tendsto.liminf_eq
  have hxg : (x, (0 : ℝ)) ∈ effectiveDomain g := by
    -- The finite right-limit forces the boundary value of `g` to be finite as well.
    rw [mem_effectiveDomain_iff]
    exact lt_of_le_of_lt hgx_le_hfx hx_finite
  have hg_tendsto :
      Filter.Tendsto (fun α : ℝ ↦ (g (line α) : EReal)) (𝓝[>] (0 : ℝ)) (𝓝 (g (x, 0) : EReal)) := by
    -- Once the boundary point is known to be finite for `g`, Proposition 9.14 applies to `g` too.
    simpa [line] using
      (tendsto_apply_lineMap_right_zero_of_lowerSemicontinuous_epigraph_convex
        (φ := g) hg.1 (convex_real_epigraph_of_mem_gammaZero hg)
        (x := (x, (0 : ℝ))) (y := (y, η))
        (mem_effectiveDomain_iff.mp hxg) hyg_finite)
  have hboundary_eq : (g (x, 0) : EReal) = (f (x, 0) : EReal) :=
    tendsto_nhds_unique hg_tendsto hg_to_f_tendsto
  exact ⟨mem_effectiveDomain_iff.mp hxg, hboundary_eq.symm⟩

/-- Helper for Proposition 9.16: equality on the open upper half-space extends to the boundary
slice `H × {0}`. -/
private lemma eq_on_boundary_of_eqOn_openUpperHalfSpace
    {f g : H × ℝ → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H × ℝ)) (hg : g ∈ Γ₀(H × ℝ))
    (heq : Set.EqOn f g (Set.univ ×ˢ Set.Ioi (0 : ℝ)))
    (hproper :
      (effectiveDomain f ∩ (Set.univ ×ˢ Set.Ioi (0 : ℝ))).Nonempty) :
    ∀ x : H, (f (x, 0) : EReal) = (g (x, 0) : EReal) := by
  rcases hproper with ⟨⟨y, η⟩, hyf, hy_open⟩
  have hη : 0 < η := by
    simpa [Set.mem_prod, Set.mem_univ] using hy_open
  have hy_val_eq : (f (y, η) : EReal) = (g (y, η) : EReal) := by
    simpa using congrArg (fun z : Set.Ioi (⊥ : EReal) ↦ (z : EReal)) (heq hy_open)
  have hyg : (y, η) ∈ effectiveDomain g := by
    -- The positive witness stays finite for `g` because `f` and `g` agree there.
    rw [mem_effectiveDomain_iff]
    simpa [hy_val_eq] using (mem_effectiveDomain_iff.mp hyf)
  intro x
  by_cases hxf : (x, (0 : ℝ)) ∈ effectiveDomain f
  · -- Apply the finite-boundary comparison directly to `f`.
    exact (boundary_value_eq_of_mem_effectiveDomain hf hg heq hyf hyg hη hxf).2
  · by_cases hxg : (x, (0 : ℝ)) ∈ effectiveDomain g
    · -- Symmetry reduces the mixed case to the previous step and contradicts `x ∉ dom f`.
      have hswap :=
        boundary_value_eq_of_mem_effectiveDomain
          (f := g) (g := f) hg hf heq.symm hyg hyf hη hxg
      exact False.elim (hxf (mem_effectiveDomain_iff.mpr hswap.1))
    · -- Outside both effective domains, both extended values must be `⊤`.
      have hf_top : (f (x, 0) : EReal) = ⊤ := by
        by_contra hf_ne_top
        exact hxf (mem_effectiveDomain_iff.mpr (lt_of_le_of_ne le_top hf_ne_top))
      have hg_top : (g (x, 0) : EReal) = ⊤ := by
        by_contra hg_ne_top
        exact hxg (mem_effectiveDomain_iff.mpr (lt_of_le_of_ne le_top hg_ne_top))
      rw [hf_top, hg_top]

-- Proof sketch: choose a point of the common effective domain with strictly positive second
-- coordinate. Apply Proposition 9.14 to the line segment from an arbitrary boundary point `(x, 0)`
-- to that point for both `f` and `g`; along the open upper half-space the segment values agree, so
-- the limits force equality on `H × {0}`. The domain inclusion then shows that both functions take
-- the value `⊤` on the open lower half-space, hence they agree everywhere.
/-- Proposition 9.16: if `f` and `g` belong to `Γ₀(H × ℝ)`, their effective domains are contained
in the closed upper half-space, they agree on the open upper half-space, and their common
restriction there is proper, then `f = g` on all of `H × ℝ`. -/
theorem eq_of_eqOn_openUpperHalfSpace_of_effectiveDomain_union_subset_closedUpperHalfSpace
    {f g : H × ℝ → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H × ℝ)) (hg : g ∈ Γ₀(H × ℝ))
    (hdom :
      effectiveDomain f ∪ effectiveDomain g ⊆ Set.univ ×ˢ Set.Ici (0 : ℝ))
    (heq : Set.EqOn f g (Set.univ ×ˢ Set.Ioi (0 : ℝ)))
    (hproper :
      (effectiveDomain f ∩ (Set.univ ×ˢ Set.Ioi (0 : ℝ))).Nonempty) :
    f = g := by
  have hdomf : effectiveDomain f ⊆ Set.univ ×ˢ Set.Ici (0 : ℝ) := by
    intro p hp
    exact hdom (Or.inl hp)
  have hdomg : effectiveDomain g ⊆ Set.univ ×ˢ Set.Ici (0 : ℝ) := by
    intro p hp
    exact hdom (Or.inr hp)
  have hboundary :
      ∀ x : H, (f (x, 0) : EReal) = (g (x, 0) : EReal) :=
    eq_on_boundary_of_eqOn_openUpperHalfSpace hf hg heq hproper
  funext p
  rcases p with ⟨x, t⟩
  apply Subtype.ext
  by_cases hpos : 0 < t
  · -- The given equality hypothesis already covers the open upper half-space.
    have hp_mem : (x, t) ∈ Set.univ ×ˢ Set.Ioi (0 : ℝ) := by
      simpa [Set.mem_prod, Set.mem_univ] using hpos
    simpa using congrArg (fun z : Set.Ioi (⊥ : EReal) ↦ (z : EReal)) (heq hp_mem)
  · by_cases hzero : t = 0
    · -- The boundary slice was settled by the auxiliary lemma above.
      simpa [hzero] using hboundary x
    · -- Route correction: once `p.2` is neither positive nor zero, the domain hypothesis forces
      -- both values to be `⊤`, so no additional convexity argument is needed here.
      have hneg : t < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hzero
      rw [value_eq_top_of_neg_snd_of_effectiveDomain_subset_closedUpperHalfSpace hdomf hneg,
        value_eq_top_of_neg_snd_of_effectiveDomain_subset_closedUpperHalfSpace hdomg hneg]

end ERealFunction

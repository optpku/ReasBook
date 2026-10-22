/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Topology ENNReal

noncomputable section

local notation "PathSpace" => C(NNReal, ℝ)

/-- Helper for Definition 21.52: the first-variation path `t ↦ V_t^1(G)` of a continuous real-valued
path on `[0, ∞)` is the canonical signed-variation path `variationOnFromTo G univ 0`. -/
def variationProcess (G : PathSpace) : NNReal → ℝ :=
  variationOnFromTo G univ 0

/-- Evaluating `variationProcess G` at time `t` gives the total variation of `G` on `[0, t]`. -/
theorem variationProcess_eq_toReal_eVariationOn_Icc (G : PathSpace) (t : NNReal) :
    variationProcess G t = (eVariationOn G (Icc 0 t)).toReal := by
  -- Unfold the definition once and rewrite the owner interval to `[0, t]`.
  rw [variationProcess, variationOnFromTo.eq_of_le G univ (show (0 : NNReal) ≤ t by exact bot_le)]
  simp

/-- Helper for Definition 21.52: for paths on `[0, ∞)`, the source
condition "locally finite variation" is exactly the canonical owner
property `LocallyBoundedVariationOn G univ`. -/
theorem locallyBoundedVariationOn_univ_iff_forall_boundedVariationOn_Icc_zero (G : PathSpace) :
    LocallyBoundedVariationOn G univ ↔ ∀ t : NNReal, BoundedVariationOn G (Icc 0 t) := by
  constructor
  · intro hG t
    -- Evaluate the owner predicate at the interval endpoints `0` and `t`.
    simpa using hG 0 t (mem_univ _) (mem_univ _)
  · intro hG a b _ _
    -- Any compact interval `[a, b]` sits inside `[0, max a b]` on `NNReal`.
    refine (hG (max a b)).mono ?_
    intro x hx
    exact ⟨by simp, hx.2.2.trans (le_max_right a b)⟩

/- Definition 21.52 (2): the owner property is `LocallyBoundedVariationOn G univ`; continuity of
`variationProcess G` is derived API. -/
/-- For a continuous path of locally bounded variation, the variation process is continuous. -/
theorem _root_.LocallyBoundedVariationOn.continuous_variationProcess {G : PathSpace}
    (hG : LocallyBoundedVariationOn G univ) :
    Continuous (variationProcess G) := by
  -- Prove continuity pointwise from the left and the right.
  rw [continuous_iff_continuousAt]
  intro t
  rw [continuousAt_iff_continuous_left_right]
  let T : NNReal := t + 1
  have hTlt : t < T := by
    dsimp [T]
    exact lt_add_of_pos_right t (zero_lt_one : (0 : NNReal) < 1)
  have hT : BoundedVariationOn G (Icc 0 T) := by
    simpa [T] using hG 0 (t + 1) (mem_univ _) (mem_univ _)
  have hGleft : ContinuousWithinAt G (Icc 0 T ∩ Iic t) t := by
    -- `G` is globally continuous, hence continuous on the left inside the control interval.
    exact (G.continuous.continuousAt.continuousWithinAt).mono (by intro x hx; exact hx.1)
  have hGright : ContinuousWithinAt G (Icc 0 T ∩ Ici t) t := by
    -- The same global continuity gives the right-continuous control needed on `[t, T)`.
    exact (G.continuous.continuousAt.continuousWithinAt).mono (by intro x hx; exact hx.1)
  refine ⟨?_, ?_⟩
  · -- Rewrite the left increment by additivity and use that small left intervals have vanishing
    -- variation for a left-continuous bounded-variation path.
    have hsmall :
        Filter.Tendsto (fun y ↦ eVariationOn G (Icc y t)) (𝓝[Iic t] t) (𝓝 0) := by
      have hsmallT :
          Filter.Tendsto (fun y ↦ eVariationOn G (Icc 0 T ∩ Icc y t)) (𝓝[Icc 0 T] t) (𝓝 0) :=
        hT.tendsto_eVariationOn_Icc_zero_left hGleft
      refine Filter.Tendsto.congr' ?_
        (hsmallT.mono_left (nhdsWithin_mono _ (by
          intro y hy
          exact ⟨by simp, hy.trans hTlt.le⟩)))
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hyT : y ≤ T := hy.trans hTlt.le
      have hset : Icc 0 T ∩ Icc y t = Icc y t := by
        ext x
        constructor
        · intro hx
          exact hx.2
        · intro hx
          exact ⟨⟨by simp, hx.2.trans hTlt.le⟩, hx⟩
      exact congrArg (eVariationOn G) hset
    have hsmallReal :
        ContinuousWithinAt (fun y ↦ (eVariationOn G (Icc y t)).toReal) (Iic t) t := by
      -- Convert the `ENNReal` convergence to an ordinary real-valued continuity statement.
      simpa [ContinuousWithinAt, Icc_self] using
        (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsmall
    have hleftExpr :
        ContinuousWithinAt
          (fun y ↦ variationProcess G t - (eVariationOn G (Icc y t)).toReal) (Iic t) t := by
      simpa [sub_eq_add_neg] using continuousWithinAt_const.add hsmallReal.neg
    have hleftEq :
        (fun y ↦ variationProcess G y) =ᶠ[𝓝[Iic t] t]
          (fun y ↦ variationProcess G t - (eVariationOn G (Icc y t)).toReal) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hadd :
          variationProcess G t = variationProcess G y + (eVariationOn G (Icc y t)).toReal := by
        -- Normalize both `variationProcess` terms to the canonical `[0, •]` variation formula.
        simpa [variationProcess, variationOnFromTo.eq_of_le G univ hy, Set.univ_inter] using
          (variationOnFromTo.add hG (a := 0) (b := y) (c := t)
            (mem_univ _) (mem_univ _) (mem_univ _)).symm
      linarith
    exact hleftExpr.congr_of_eventuallyEq_of_mem hleftEq (by simp)
  · -- On the right, first restrict to the neighborhood `(-∞, T)`, then use the right-interval
    -- variation limit and the additive decomposition of `variationProcess`.
    have hIio : Iio T ∈ 𝓝 t := Iio_mem_nhds hTlt
    have hsmall :
        Filter.Tendsto (fun y ↦ eVariationOn G (Icc t y)) (𝓝[Ici t ∩ Iio T] t) (𝓝 0) := by
      have hsmallT :
          Filter.Tendsto (fun y ↦ eVariationOn G (Icc 0 T ∩ Icc t y)) (𝓝[Icc 0 T] t) (𝓝 0) :=
        hT.tendsto_eVariationOn_Icc_zero_right t hGright
      refine Filter.Tendsto.congr' ?_
        (hsmallT.mono_left (nhdsWithin_mono _ (by intro y hy; exact ⟨by simp, hy.2.le⟩)))
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hset : Icc 0 T ∩ Icc t y = Icc t y := by
        ext x
        constructor
        · intro hx
          exact hx.2
        · intro hx
          exact ⟨⟨by simp, hx.2.trans hy.2.le⟩, hx⟩
      exact congrArg (eVariationOn G) hset
    have hsmallReal :
        ContinuousWithinAt (fun y ↦ (eVariationOn G (Icc t y)).toReal) (Ici t ∩ Iio T) t := by
      -- Again convert the vanishing `ENNReal` variation to a real-valued continuity statement.
      simpa [ContinuousWithinAt, Icc_self] using
        (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsmall
    have hrightExpr :
        ContinuousWithinAt
          (fun y ↦ variationProcess G t + (eVariationOn G (Icc t y)).toReal) (Ici t ∩ Iio T) t := by
      exact continuousWithinAt_const.add hsmallReal
    have hrightEq :
        (fun y ↦ variationProcess G y) =ᶠ[𝓝[Ici t ∩ Iio T] t]
          (fun y ↦ variationProcess G t + (eVariationOn G (Icc t y)).toReal) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hadd :
          variationProcess G y = variationProcess G t + (eVariationOn G (Icc t y)).toReal := by
        -- Normalize the additivity statement without rewriting under binders.
        simpa [variationProcess, variationOnFromTo.eq_of_le G univ hy.1, Set.univ_inter] using
          (variationOnFromTo.add hG (a := 0) (b := t) (c := y)
            (mem_univ _) (mem_univ _) (mem_univ _)).symm
      linarith
    exact (continuousWithinAt_inter hIio).1 <|
      hrightExpr.congr_of_eventuallyEq_of_mem hrightEq (by simp [hTlt])

/-- Helper for Definition 21.52: coordinatewise bounded variation gives bounded variation of the
pair-valued path. -/
private theorem boundedVariationOn_prod {G H : PathSpace} {s : Set NNReal}
    (hG : BoundedVariationOn G s) (hH : BoundedVariationOn H s) :
    BoundedVariationOn (fun t ↦ (G t, H t)) s := by
  -- Bound each partition sum in the product by the sum of the coordinate partition sums.
  rw [BoundedVariationOn] at hG hH ⊢
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hG, hH⟩) ?_
  dsimp [eVariationOn]
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  calc
    ∑ i ∈ Finset.range n, edist ((G (u (i + 1)), H (u (i + 1)))) ((G (u i), H (u i)))
        ≤ ∑ i ∈ Finset.range n,
            (edist (G (u (i + 1))) (G (u i)) + edist (H (u (i + 1))) (H (u i))) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          rw [Prod.edist_eq]
          exact max_le_iff.mpr ⟨le_add_of_nonneg_right bot_le, by simp⟩
    _ = (∑ i ∈ Finset.range n, edist (G (u (i + 1))) (G (u i))) +
          ∑ i ∈ Finset.range n, edist (H (u (i + 1))) (H (u i)) := by
          rw [Finset.sum_add_distrib]
    _ ≤ eVariationOn G s + eVariationOn H s := by
          exact add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)

-- Proof sketch: the zero path has zero variation on every interval, so the finiteness condition
-- is immediate.
private theorem locallyBoundedVariationOn_univ_zero :
    LocallyBoundedVariationOn (0 : PathSpace) univ := by
  intro a b _ _
  -- A constant path has zero total variation on every interval.
  rw [BoundedVariationOn]
  rw [eVariationOn.constant_on (f := (0 : PathSpace)) (s := univ ∩ Icc a b)
    (by
      rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩
      rfl)]
  simp

-- Proof sketch: total variation is subadditive on each interval, giving local finite variation
-- for `G + H`.
private theorem locallyBoundedVariationOn_univ_add {G H : PathSpace}
    (hG : LocallyBoundedVariationOn G univ) (hH : LocallyBoundedVariationOn H univ) :
    LocallyBoundedVariationOn (G + H) univ := by
  intro a b _ _
  -- Package the two coordinates into a single product-valued path and compose with addition.
  have hprod :
      BoundedVariationOn (fun t ↦ (G t, H t)) (univ ∩ Icc a b) :=
    boundedVariationOn_prod
      (hG a b (mem_univ _) (mem_univ _))
      (hH a b (mem_univ _) (mem_univ _))
  simpa [Function.comp] using
    (lipschitzWith_lipschitz_const_add_edist.comp_boundedVariationOn hprod)

-- Proof sketch: variation scales by `|c|` on each interval, so scalar multiplication preserves
-- local finite variation.
private theorem locallyBoundedVariationOn_univ_smul (c : ℝ) {G : PathSpace}
    (hG : LocallyBoundedVariationOn G univ) :
    LocallyBoundedVariationOn (c • G) univ := by
  intro a b _ _
  -- Scalar multiplication is Lipschitz, so it preserves bounded variation on each compact
  -- interval.
  simpa [Function.comp, Pi.smul_apply] using
    (lipschitzWith_smul c).comp_boundedVariationOn (hG a b (mem_univ _) (mem_univ _))

/-- Definition 21.52 (3): `continuousVariationSubmodule` is the textbook vector space `𝒞_v` of
continuous real-valued paths on `[0, ∞)` whose variation process is continuous. -/
def continuousVariationSubmodule : Submodule ℝ PathSpace where
  carrier := {G | LocallyBoundedVariationOn G univ}
  zero_mem' := locallyBoundedVariationOn_univ_zero
  add_mem' := locallyBoundedVariationOn_univ_add
  smul_mem' := locallyBoundedVariationOn_univ_smul

-- Proof sketch: unfold `continuousVariationSubmodule`; membership in its carrier is exactly the
-- predicate used to define the submodule.
/-- A path belongs to `continuousVariationSubmodule` exactly when it has locally bounded
variation on `[0, ∞)`. -/
theorem mem_continuousVariationSubmodule_iff (G : PathSpace) :
    G ∈ continuousVariationSubmodule ↔ LocallyBoundedVariationOn G univ :=
  Iff.rfl

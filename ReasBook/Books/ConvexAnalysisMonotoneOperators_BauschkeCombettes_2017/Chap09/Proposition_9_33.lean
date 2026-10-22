/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Lemma_1_32
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_56_1_36
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_6
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_8

-- Declarations for this item will be appended below by the statement pipeline.

open Set Filter

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

attribute [local instance] Classical.propDecidable

/-- The boundary-liminf extension of a proper convex `]-∞,+∞]`-valued function: it agrees with
`g` on `effectiveDomain g`, takes the neighborhood liminf on the boundary of the effective domain,
and is `+∞` outside the closure of the effective domain. -/
noncomputable def boundaryLiminfExtensionEReal
    (g : H → Set.Ioi (⊥ : EReal)) : H → EReal :=
  fun x ↦
    if x ∈ effectiveDomain g then
      g x
    else if x ∈ frontier (effectiveDomain g) then
      liminfAt (fun y : H ↦ (g y : EReal)) x
    else
      ⊤

/-- Helper for Proposition 9.33: outside the effective domain of an `]-∞,+∞]`-valued function,
the value is necessarily `⊤`. -/
private theorem value_eq_top_of_not_mem_effectiveDomain
    {g : H → Set.Ioi (⊥ : EReal)} {x : H} (hx : x ∉ effectiveDomain g) :
    (g x : EReal) = ⊤ := by
  -- If the value were finite, then `x` would already belong to the effective domain.
  by_contra htop
  exact hx (mem_effectiveDomain_iff.mpr (lt_of_le_of_ne le_top htop))

/-- On the effective domain, the boundary-liminf extension agrees with `g`. -/
-- Proof sketch: unfold `boundaryLiminfExtensionEReal` and evaluate the first branch of the
-- defining `if`.
theorem boundaryLiminfExtensionEReal_of_mem_effectiveDomain
    (g : H → Set.Ioi (⊥ : EReal)) {x : H} (hx : x ∈ effectiveDomain g) :
    boundaryLiminfExtensionEReal g x = g x := by
  -- The first branch of the piecewise definition is active on the effective domain.
  simp [boundaryLiminfExtensionEReal, hx]

/-- Helper for Proposition 9.33: outside the closure of the effective domain, the explicit
boundary extension is on its `+∞` branch. -/
private theorem boundaryLiminfExtensionEReal_of_not_mem_closure_effectiveDomain
    (g : H → Set.Ioi (⊥ : EReal)) {x : H} (hx : x ∉ closure (effectiveDomain g)) :
    boundaryLiminfExtensionEReal g x = ⊤ := by
  have hx_not_mem : x ∉ effectiveDomain g := by
    intro hx_mem
    exact hx (subset_closure hx_mem)
  have hx_not_frontier : x ∉ frontier (effectiveDomain g) := by
    intro hx_frontier
    exact hx hx_frontier.1
  -- Both tests in the definition fail, so only the exterior `⊤` branch remains.
  simp [boundaryLiminfExtensionEReal, hx_not_mem, hx_not_frontier]

/-- The boundary-liminf extension of a frontier point uses the liminf branch whenever the point is
not already in the effective domain. -/
private theorem boundaryLiminfExtensionEReal_of_mem_frontier
    (g : H → Set.Ioi (⊥ : EReal)) {x : H}
    (hx_not_mem : x ∉ effectiveDomain g) (hx_frontier : x ∈ frontier (effectiveDomain g)) :
    boundaryLiminfExtensionEReal g x = liminfAt (fun y : H ↦ (g y : EReal)) x := by
  -- The first branch is excluded and the second branch is exactly the frontier case.
  simp [boundaryLiminfExtensionEReal, hx_not_mem, hx_frontier]

/-- Helper for Proposition 9.33: the `EReal` epigraph of `g` is convex whenever `g` is convex on
its effective domain. -/
private theorem convex_epigraph_coe_of_convexOn_local
    (g : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn g (effectiveDomain g)) :
    Convex ℝ (epigraph (fun x : H ↦ (g x : EReal))) := by
  -- Rewrite the stored `ConvexOn` Jensen inequality into the epigraph criterion.
  refine (convex_epigraph_iff_jensen_on_dom (fun x : H ↦ (g x : EReal))).2 ?_
  intro x y hx hy α hα hα_lt_one
  have hx' : x ∈ effectiveDomain g := by
    simpa [effectiveDomain, dom] using hx
  have hy' : y ∈ effectiveDomain g := by
    simpa [effectiveDomain, dom] using hy
  simpa using hconv.ineq hx' hy' hα hα_lt_one

/-- Helper for Proposition 9.33: on the open effective domain, the `EReal` coercion of `g` is
lower semicontinuous at each interior point. -/
private theorem lowerSemicontinuousAt_coe_of_mem_effectiveDomain_local
    (g : H → Set.Ioi (⊥ : EReal))
    (hopen : IsOpen (effectiveDomain g))
    (hcont : ContinuousOn (fun x : H ↦ (g x : EReal).toReal) (effectiveDomain g))
    {x : H} (hx : x ∈ effectiveDomain g) :
    LowerSemicontinuousAt (fun y : H ↦ (g y : EReal)) x := by
  let G : H → EReal := fun y ↦ (((g y : EReal).toReal : ℝ) : EReal)
  have hGcont : ContinuousOn G (effectiveDomain g) := by
    -- Compose the real-valued continuity hypothesis with the continuous coercion `ℝ → EReal`.
    simpa [G] using (continuous_coe_real_ereal.comp_continuousOn' hcont)
  have hGcontAt : ContinuousAt G x :=
    (hGcont x hx).continuousAt (hopen.mem_nhds hx)
  have hEq :
      G =ᶠ[nhds x] (fun y : H ↦ (g y : EReal)) := by
    -- On a neighborhood inside the open effective domain, `toReal` followed by coercion recovers
    -- the original `EReal` value.
    filter_upwards [hopen.mem_nhds hx] with y hy
    have hy_top : (g y : EReal) ≠ ⊤ :=
      ne_of_lt (mem_effectiveDomain_iff.mp hy)
    have hy_bot : (g y : EReal) ≠ ⊥ :=
      ne_of_gt (show (⊥ : EReal) < (g y : EReal) from (g y).2)
    simpa [G] using (EReal.coe_toReal hy_top hy_bot)
  -- Continuous functions are lower semicontinuous, and eventual equality transfers continuity.
  exact (hGcontAt.congr hEq).lowerSemicontinuousAt

/-- Helper for Proposition 9.33: the piecewise boundary extension is exactly the lower
semicontinuous hull of `x ↦ (g x : EReal)`. -/
private theorem boundaryLiminfExtensionEReal_eq_lowerSemicontinuousHull_local
    (g : H → Set.Ioi (⊥ : EReal))
    (hopen : IsOpen (effectiveDomain g))
    (hcont : ContinuousOn (fun x : H ↦ (g x : EReal).toReal) (effectiveDomain g)) :
    boundaryLiminfExtensionEReal g =
      lowerSemicontinuousEnvelope (fun x : H ↦ (g x : EReal)) := by
  let F : H → EReal := fun x ↦ (g x : EReal)
  funext x
  by_cases hx : x ∈ effectiveDomain g
  · -- On the interior, the hull agrees with `g` because `g` is already lower semicontinuous there.
    have hlsc :
        LowerSemicontinuousAt (fun y : H ↦ (g y : EReal)) x :=
      lowerSemicontinuousAt_coe_of_mem_effectiveDomain_local g hopen hcont hx
    have hhull : lowerSemicontinuousEnvelope F x = F x :=
      (lowerSemicontinuousAt_iff_lowerSemicontinuousHull_eq F x).mp hlsc
    calc
      boundaryLiminfExtensionEReal g x = F x := by
        simpa [F] using boundaryLiminfExtensionEReal_of_mem_effectiveDomain g hx
      _ = lowerSemicontinuousEnvelope F x := hhull.symm
  · by_cases hx_frontier : x ∈ frontier (effectiveDomain g)
    · -- On the boundary, both the explicit extension and the hull are the same liminf.
      calc
        boundaryLiminfExtensionEReal g x = liminfAt F x := by
          simpa [F] using
            boundaryLiminfExtensionEReal_of_mem_frontier g hx hx_frontier
        _ = lowerSemicontinuousEnvelope F x := by
          symm
          exact lowerSemicontinuousHull_eq_liminfAt F x
    · -- Away from the closure, both functions are forced onto the `+∞` branch.
      have hx_not_closure : x ∉ closure (effectiveDomain g) := by
        intro hx_closure
        have hx_not_interior : x ∉ interior (effectiveDomain g) := by
          intro hx_int
          exact hx (interior_subset hx_int)
        exact hx_frontier ⟨hx_closure, hx_not_interior⟩
      have hx_not_dom_hull : x ∉ dom (lowerSemicontinuousEnvelope F) := by
        intro hx_dom_hull
        exact hx_not_closure <| by
          simpa [F, effectiveDomain, dom] using
            (dom_lowerSemicontinuousHull_subset_closure_dom F hx_dom_hull)
      have hhull_top : lowerSemicontinuousEnvelope F x = ⊤ := by
        -- Outside `closure (dom F)`, the lower semicontinuous hull cannot take a finite value.
        apply le_antisymm le_top
        exact le_of_not_gt (by simpa [dom] using hx_not_dom_hull)
      calc
        boundaryLiminfExtensionEReal g x = ⊤ :=
          boundaryLiminfExtensionEReal_of_not_mem_closure_effectiveDomain g hx_not_closure
        _ = lowerSemicontinuousEnvelope F x := hhull_top.symm

/-- Helper for Proposition 9.33: once the epigraph of `x ↦ (g x : EReal)` is convex, its lower
semicontinuous hull already equals its lower semicontinuous convex envelope. -/
private theorem lowerSemicontinuousHull_eq_lowerSemicontinuousConvexEnvelope_local
    (g : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn g (effectiveDomain g)) :
    lowerSemicontinuousEnvelope (fun x : H ↦ (g x : EReal)) =
      lowerSemicontinuousConvexEnvelope (fun x : H ↦ (g x : EReal)) := by
  let F : H → EReal := fun x ↦ (g x : EReal)
  have hF_conv : Convex ℝ (epigraph F) :=
    convex_epigraph_coe_of_convexOn_local g hconv
  have hhull_lsc : LowerSemicontinuous (lowerSemicontinuousEnvelope F) :=
    (lowerSemicontinuousHull_isGreatest F).1.1
  have hhull_le : lowerSemicontinuousEnvelope F ≤ F :=
    (lowerSemicontinuousHull_isGreatest F).1.2
  have hhull_conv : Convex ℝ (epigraph (lowerSemicontinuousEnvelope F)) := by
    -- The hull epigraph is the closure of `epigraph F`, so convexity is preserved.
    rw [epi_lowerSemicontinuousHull_eq_closure_epi]
    exact hF_conv.closure
  have hhull_le_env :
      lowerSemicontinuousEnvelope F ≤ lowerSemicontinuousConvexEnvelope F :=
    le_lowerSemicontinuousConvexEnvelope_of_lowerSemicontinuous_of_convex_epigraph
      hhull_lsc hhull_conv hhull_le
  have henv_le_hull :
      lowerSemicontinuousConvexEnvelope F ≤ lowerSemicontinuousEnvelope F :=
    (lowerSemicontinuousHull_isGreatest F).2
      ⟨lowerSemicontinuous_lowerSemicontinuousConvexEnvelope F,
        lowerSemicontinuousConvexEnvelope_le F⟩
  -- The two maximality principles squeeze the hull and the convex envelope together.
  funext x
  exact le_antisymm (hhull_le_env x) (henv_le_hull x)

/-- Helper for Proposition 9.33: a lower semicontinuous function with convex epigraph cannot take
the value `-∞` at one point and a finite value at another. -/
private theorem eq_bot_or_eq_top_of_lowerSemicontinuous_of_convex_epigraph_of_eq_bot_local
    {f : H → EReal} (hf_lsc : LowerSemicontinuous f) (hf_conv : Convex ℝ (epigraph f))
    {x : H} (hx : f x = ⊥) (y : H) :
    f y = ⊥ ∨ f y = ⊤ := by
  by_cases hytop : f y = ⊤
  · -- Outside the domain, `f y` is already on the `+∞` branch.
    exact Or.inr hytop
  · have hx_dom : x ∈ dom f := by
      rw [mem_dom_iff]
      simpa [hx] using (bot_lt_top : (⊥ : EReal) < ⊤)
    have hy_dom : y ∈ dom f := by
      rw [mem_dom_iff]
      exact lt_of_le_of_ne le_top hytop
    let u : ℕ → H := fun n ↦
      (1 / (n + 2 : ℝ)) • x + (1 - 1 / (n + 2 : ℝ)) • y
    have hu : Tendsto u atTop (nhds y) :=
      tendsto_reciprocal_convex_combination_to_right x y
    have hu_bot : ∀ n : ℕ, f (u n) = ⊥ := by
      intro n
      have hα_pos : 0 < 1 / (n + 2 : ℝ) := by
        exact one_div_pos.mpr (by positivity : (0 : ℝ) < n + 2)
      have hα_lt_one : 1 / (n + 2 : ℝ) < 1 := by
        have h : 1 / (n + 2 : ℝ) < 1 / (1 : ℝ) := by
          refine (one_div_lt_one_div (α := ℝ) ?_ ?_).2 ?_
          · positivity
          · norm_num
          · exact_mod_cast Nat.succ_lt_succ (Nat.succ_pos n)
        simpa using h
      have hineq :
          f (u n) ≤
            ((1 / (n + 2 : ℝ) : ℝ) : EReal) * f x +
              (1 - 1 / (n + 2 : ℝ) : EReal) * f y :=
        (convex_epigraph_iff_jensen_on_dom f).1 hf_conv hx_dom hy_dom hα_pos hα_lt_one
      have hαE : 0 < ((1 / (n + 2 : ℝ) : ℝ) : EReal) :=
        EReal.coe_pos.mpr hα_pos
      have hfirst :
          ((1 / (n + 2 : ℝ) : ℝ) : EReal) * f x = ⊥ := by
        simpa [hx] using (EReal.mul_bot_of_pos hαE)
      have hbot_le : f (u n) ≤ ⊥ := by
        calc
          f (u n) ≤
              ((1 / (n + 2 : ℝ) : ℝ) : EReal) * f x +
                (1 - 1 / (n + 2 : ℝ) : EReal) * f y :=
            hineq
          _ = ⊥ + (1 - 1 / (n + 2 : ℝ) : EReal) * f y := by
            rw [hfirst]
          _ = ⊥ := by
            simp
      exact le_bot_iff.mp hbot_le
    have hseq :
        ∀ ⦃z : H⦄ ⦃v : ℕ → H⦄, Tendsto v atTop (nhds z) → f z ≤ liminf (f ∘ v) atTop :=
      (lowerSemicontinuous_iff_seq_tendsto_le_liminf f).mp hf_lsc
    have hliminf : f y ≤ liminf (f ∘ u) atTop :=
      hseq hu
    have hconst : (f ∘ u) = fun _ : ℕ ↦ (⊥ : EReal) := by
      -- The strict convex combinations stay at `-∞`, so the sequence is constantly `⊥`.
      funext n
      exact hu_bot n
    rw [hconst, Filter.liminf_const] at hliminf
    exact Or.inl (le_bot_iff.mp hliminf)

/-- Helper for Proposition 9.33: the main equality is already available before constructing the
subtype-valued extension. -/
private theorem boundaryLiminfExtensionEReal_eq_lowerSemicontinuousConvexEnvelope_local
    (g : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn g (effectiveDomain g))
    (hopen : IsOpen (effectiveDomain g))
    (hcont : ContinuousOn (fun x : H ↦ (g x : EReal).toReal) (effectiveDomain g)) :
    boundaryLiminfExtensionEReal g =
      lowerSemicontinuousConvexEnvelope (fun x : H ↦ (g x : EReal)) := by
  -- Route correction: identify the piecewise formula first with the lower semicontinuous hull,
  -- then use convexity of the epigraph to upgrade that hull to the convex envelope.
  calc
    boundaryLiminfExtensionEReal g =
        lowerSemicontinuousEnvelope (fun x : H ↦ (g x : EReal)) :=
      boundaryLiminfExtensionEReal_eq_lowerSemicontinuousHull_local g hopen hcont
    _ = lowerSemicontinuousConvexEnvelope (fun x : H ↦ (g x : EReal)) :=
      lowerSemicontinuousHull_eq_lowerSemicontinuousConvexEnvelope_local g hconv

/-- Under the hypotheses of Proposition 9.33, the boundary-liminf extension is strictly above
`-∞`. -/
-- Proof sketch: first identify `boundaryLiminfExtensionEReal g` with the lower semicontinuous
-- convex envelope of `g`; then use lower semicontinuity plus convex epigraph to rule out a single
-- `-∞` value, because the interior witness supplied by the nonempty effective domain has a finite
-- value.
theorem boundaryLiminfExtensionEReal_ne_bot
    (g : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn g (effectiveDomain g))
    (hopen : IsOpen (effectiveDomain g))
    (hcont : ContinuousOn (fun x : H ↦ (g x : EReal).toReal) (effectiveDomain g))
    (x : H) :
    ⊥ < boundaryLiminfExtensionEReal g x := by
  let F : H → EReal := fun y ↦ (g y : EReal)
  have hmain :
      boundaryLiminfExtensionEReal g =
        lowerSemicontinuousConvexEnvelope F :=
    boundaryLiminfExtensionEReal_eq_lowerSemicontinuousConvexEnvelope_local g hconv hopen hcont
  have henv_lsc : LowerSemicontinuous (lowerSemicontinuousConvexEnvelope F) :=
    lowerSemicontinuous_lowerSemicontinuousConvexEnvelope F
  have henv_conv : Convex ℝ (epigraph (lowerSemicontinuousConvexEnvelope F)) :=
    convex_epigraph_lowerSemicontinuousConvexEnvelope F
  rcases hconv.nonempty with ⟨x₀, hx₀⟩
  have hx₀_val :
      lowerSemicontinuousConvexEnvelope F x₀ = g x₀ := by
    -- The interior branch of the boundary extension gives a concrete finite witness.
    calc
      lowerSemicontinuousConvexEnvelope F x₀ = boundaryLiminfExtensionEReal g x₀ := by
        exact (congrFun hmain x₀).symm
      _ = g x₀ := boundaryLiminfExtensionEReal_of_mem_effectiveDomain g hx₀
  have hnot_bot : boundaryLiminfExtensionEReal g x ≠ ⊥ := by
    intro hx_bot
    have henv_bot : lowerSemicontinuousConvexEnvelope F x = ⊥ := by
      rw [← congrFun hmain x]
      exact hx_bot
    have hx₀_split :
        lowerSemicontinuousConvexEnvelope F x₀ = ⊥ ∨
          lowerSemicontinuousConvexEnvelope F x₀ = ⊤ :=
      eq_bot_or_eq_top_of_lowerSemicontinuous_of_convex_epigraph_of_eq_bot_local
        henv_lsc henv_conv henv_bot x₀
    rcases hx₀_split with hx₀_bot | hx₀_top
    · have hx₀_ne_bot : (g x₀ : EReal) ≠ ⊥ :=
        ne_of_gt (show (⊥ : EReal) < (g x₀ : EReal) from (g x₀).2)
      exact hx₀_ne_bot (hx₀_val.symm.trans hx₀_bot)
    · have hx₀_ne_top : (g x₀ : EReal) ≠ ⊤ :=
        ne_of_lt (mem_effectiveDomain_iff.mp hx₀)
      exact hx₀_ne_top (hx₀_val.symm.trans hx₀_top)
  -- Once equality with `⊥` is impossible, the value is automatically strictly above `⊥`.
  exact lt_of_le_of_ne bot_le (Ne.symm hnot_bot)

/-- The subtype-valued boundary-liminf extension associated with Proposition 9.33. -/
noncomputable def boundaryLiminfExtension
    (g : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn g (effectiveDomain g))
    (hopen : IsOpen (effectiveDomain g))
    (hcont : ContinuousOn (fun x : H ↦ (g x : EReal).toReal) (effectiveDomain g)) :
    H → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    ⟨boundaryLiminfExtensionEReal g x,
      boundaryLiminfExtensionEReal_ne_bot g hconv hopen hcont x⟩

/-- Coercing the subtype-valued boundary-liminf extension to `EReal` recovers the explicit
piecewise formula. -/
-- Proof sketch: unfold `boundaryLiminfExtension`.
theorem boundaryLiminfExtension_coe
    (g : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn g (effectiveDomain g))
    (hopen : IsOpen (effectiveDomain g))
    (hcont : ContinuousOn (fun x : H ↦ (g x : EReal).toReal) (effectiveDomain g))
    (x : H) :
    (boundaryLiminfExtension g hconv hopen hcont x : EReal) =
      boundaryLiminfExtensionEReal g x := by
  -- Coercing out of the subtype simply forgets the proof component.
  rfl

-- Proof sketch: compare the three source-defined branches separately. On `effectiveDomain g`,
-- continuity identifies the boundary extension with `g`; on `H \ closure (effectiveDomain g)`,
-- the lower semicontinuous hull must be `+∞`; on the frontier, both descriptions are the same
-- liminf. Convexity of the epigraph then upgrades the hull to the convex envelope.
/-- Proposition 9.33: the piecewise boundary-liminf extension of a proper convex function with open
effective domain and continuous real-valued restriction agrees with its lower semicontinuous convex
envelope. -/
theorem boundaryLiminfExtensionEReal_eq_lowerSemicontinuousConvexEnvelope
    (g : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn g (effectiveDomain g))
    (hopen : IsOpen (effectiveDomain g))
    (hcont : ContinuousOn (fun x : H ↦ (g x : EReal).toReal) (effectiveDomain g)) :
    boundaryLiminfExtensionEReal g =
      lowerSemicontinuousConvexEnvelope (fun x : H ↦ (g x : EReal)) := by
  -- The local helper already implements the hull-first source proof route.
  exact
    boundaryLiminfExtensionEReal_eq_lowerSemicontinuousConvexEnvelope_local
      g hconv hopen hcont

/-- The boundary-liminf extension from Proposition 9.33 belongs to `Γ₀(H)`. -/
-- Proof sketch: rewrite the coercion of the subtype-valued extension as the lower semicontinuous
-- convex envelope, use Proposition 9.8 for lower semicontinuity and epigraph convexity, and then
-- restrict the envelope Jensen inequality to the effective domain of the subtype-valued function.
theorem boundaryLiminfExtension_mem_gammaZero
    (g : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn g (effectiveDomain g))
    (hopen : IsOpen (effectiveDomain g))
    (hcont : ContinuousOn (fun x : H ↦ (g x : EReal).toReal) (effectiveDomain g)) :
    boundaryLiminfExtension g hconv hopen hcont ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff]
  let F : H → EReal := fun x ↦ (g x : EReal)
  have hmain :
      boundaryLiminfExtensionEReal g =
        lowerSemicontinuousConvexEnvelope F :=
    boundaryLiminfExtensionEReal_eq_lowerSemicontinuousConvexEnvelope_local
      g hconv hopen hcont
  have hcoe_eq :
      (fun x : H ↦ (boundaryLiminfExtension g hconv hopen hcont x : EReal)) =
        lowerSemicontinuousConvexEnvelope F := by
    -- The subtype-valued extension is just the `EReal` extension equipped with the non-`⊥` proof.
    funext x
    calc
      (boundaryLiminfExtension g hconv hopen hcont x : EReal) =
          boundaryLiminfExtensionEReal g x :=
        boundaryLiminfExtension_coe g hconv hopen hcont x
      _ = lowerSemicontinuousConvexEnvelope F x :=
        congrFun hmain x
  constructor
  · -- Lower semicontinuity comes directly from Proposition 9.8 after the coercion rewrite.
    simpa [hcoe_eq] using
      (lowerSemicontinuous_lowerSemicontinuousConvexEnvelope F)
  · refine ⟨?_, subset_rfl, ?_⟩
    · rcases hconv.nonempty with ⟨x₀, hx₀⟩
      refine ⟨x₀, ?_⟩
      have hx₀_val :
          (boundaryLiminfExtension g hconv hopen hcont x₀ : EReal) = g x₀ := by
        calc
          (boundaryLiminfExtension g hconv hopen hcont x₀ : EReal) =
              boundaryLiminfExtensionEReal g x₀ :=
            boundaryLiminfExtension_coe g hconv hopen hcont x₀
          _ = g x₀ :=
            boundaryLiminfExtensionEReal_of_mem_effectiveDomain g hx₀
      simpa [effectiveDomain, hx₀_val] using (mem_effectiveDomain_iff.mp hx₀)
    · intro x hx y hy α hα hα_lt_one
      have hx_dom : x ∈ dom (lowerSemicontinuousConvexEnvelope F) := by
        rw [mem_dom_iff]
        exact (congrFun hcoe_eq x).symm ▸ hx
      have hy_dom : y ∈ dom (lowerSemicontinuousConvexEnvelope F) := by
        rw [mem_dom_iff]
        exact (congrFun hcoe_eq y).symm ▸ hy
      -- Restrict the global convex-envelope epigraph inequality to the effective-domain points.
      have hineq_env :
          lowerSemicontinuousConvexEnvelope F (α • x + (1 - α) • y) ≤
            (α : EReal) * lowerSemicontinuousConvexEnvelope F x +
              (1 - α : EReal) * lowerSemicontinuousConvexEnvelope F y :=
        (convex_epigraph_iff_jensen_on_dom (lowerSemicontinuousConvexEnvelope F)).1
          (convex_epigraph_lowerSemicontinuousConvexEnvelope F)
          hx_dom hy_dom hα hα_lt_one
      calc
        (boundaryLiminfExtension g hconv hopen hcont (α • x + (1 - α) • y) : EReal) =
            lowerSemicontinuousConvexEnvelope F (α • x + (1 - α) • y) :=
          congrFun hcoe_eq (α • x + (1 - α) • y)
        _ ≤ (α : EReal) * lowerSemicontinuousConvexEnvelope F x +
              (1 - α : EReal) * lowerSemicontinuousConvexEnvelope F y :=
          hineq_env
        _ = (α : EReal) * (boundaryLiminfExtension g hconv hopen hcont x : EReal) +
              (1 - α : EReal) * (boundaryLiminfExtension g hconv hopen hcont y : EReal) := by
          rw [(congrFun hcoe_eq x).symm, (congrFun hcoe_eq y).symm]

end ERealFunction

/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_21
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_53

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

open scoped Topology Gradient WithTopConvexAnalysis

noncomputable section

universe u

/-
Proposition 7.28 lies in the support-function smoothing / envelope-gradient
domain.

Sampled owner-style declarations:
- `Uβ` and `Argmaxβ` in `Chap07/Definition_7_53`, the Chapter 7 source-facing
  owners of the smoothed value and its canonical argmax set;
- `nesterovSmoothedObjective_hasFDerivAt` in `Chap06/Theorem_6_1`, the canonical
  Chapter 6 derivative owner for smoothed supremum problems;
- `smoothSupportFunctionApproximation_hasFDerivAt_and_omegaStar_upper_bound` in
  `Chap07/Lemma_7_10`, the source-facing derivative theorem already stated on
  the canonical dual owner `U_β`;
- mathlib `HasFDerivAt`, `DifferentiableAt`, `HasGradientAt`, and
  `HasGradientAt.gradient`, which give the dual-owner derivative API and the
  stronger Hilbert-space pullback bridge.

Best owner abstraction:
- source-facing: Proposition 7.28's differentiability theorem for the positive
  support-function approximation `U_β` on `StrongDual ℝ E`;
- core/canonical: `Uβ` and `Argmaxβ`;
- bridge/view: the pullback along `InnerProductSpace.toDual ℝ E` from the dual
  owner on `StrongDual ℝ E` to the Hilbert-space variable `s ∈ E`.

Primitive data:
- the feasible set `hatP`, barrier term `F`, center `x0`, and smoothing
  parameter `β : {β : ℝ // 0 < β}`;
- a point `s : StrongDual ℝ E` and the unique maximizer `u` of the canonical
  argmax set at `s`.

Derived API:
- the canonical support-function value owner `U_β` and argmax owner `Argmaxβ`;
- Fréchet differentiability on the dual owner in the finite-dimensional
  Euclidean setting of the source proposition;
- the Hilbert-space gradient formula for the pulled-back function
  `s ↦ U_β((InnerProductSpace.toDual ℝ E) s)`, which belongs to a stronger
  bridge layer.

Source/core/bridge triage:
- source-facing: the dual-owner derivative theorem below;
- core/canonical: `Uβ` and `Argmaxβ`;
- bridge/view: the pulled-back gradient theorem on `E`.

The previous version generalized Proposition 7.28 beyond the source's Euclidean
setting to arbitrary normed spaces on the dual owner and arbitrary Hilbert-space
pullbacks. That stronger infinite-dimensional statement is false. This repair
restores the source-faithful finite-dimensional Euclidean context for both the
dual-owner derivative theorem and the pulled-back gradient bridge.
-/

section DualOwner

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (hatP : Set E) (F : E → ℝ) (x0 : E) (β : {β : ℝ // 0 < β})

/-- Helper for Proposition 7.28: a convex real-valued function on the whole space is
differentiable at `x₀` once its lifted subdifferential there is the singleton `{g}`. -/
lemma hasGradientAt_of_convexOn_univ_subdifferential_eq_singleton
    {f : E → ℝ} {x0 g : E}
    (hf : ConvexOn ℝ Set.univ f)
    (hsub : ∂ (fun x : E ↦ (f x : WithTop ℝ))(x0) = {g}) :
    HasGradientAt f g x0 := by
  let fLift : E → WithTop ℝ := fun x ↦ (f x : WithTop ℝ)
  have hfWithTop :
      ConvexOn ℝ (dom fLift) (withTopRealPart fLift) := by
    -- Reinterpret the real-valued convexity hypothesis on the lifted owner surface.
    simpa [fLift, withTopEffectiveDomain] using hf
  have hx0 :
      x0 ∈ interior (dom fLift) := by
    -- A real-valued function has full effective domain, so every point is interior.
    simpa [fLift, withTopEffectiveDomain] using (show x0 ∈ interior (Set.univ : Set E) by simp)
  have hline :
      ∀ p : E, HasLineDerivAt ℝ f (inner ℝ g p) x0 p := by
    intro p
    have hright :
        Filter.Tendsto
          (fun α : ℝ ↦ (f (x0 + α • p) - f x0) / α)
          (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ g p)) := by
      have hdir :
          convexDirectionalDerivativeReal fLift hx0 p = inner ℝ g p := by
        -- The singleton subdifferential forces the directional derivative to match one pairing.
        have hgreatest :=
          convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior
            hfWithTop hx0 p
        rw [convexDirectionalDerivativeReal_apply] at hgreatest
        rw [hsub] at hgreatest
        simpa using hgreatest.1
      have hsecant :=
        tendsto_directionalSecantQuotient_of_mem_interior
          hfWithTop hx0 p
      rw [convexDirectionalDerivativeReal_apply] at hsecant
      simpa [hdir] using hsecant
    have hleft :
        Filter.Tendsto
          (fun α : ℝ ↦ (f (x0 + α • p) - f x0) / α)
          (𝓝[<] (0 : ℝ)) (𝓝 (inner ℝ g p)) := by
      have hrightNeg :
          Filter.Tendsto
            (fun α : ℝ ↦ (f (x0 + α • (-p)) - f x0) / α)
            (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ g (-p))) := by
        have hdirNeg :
            convexDirectionalDerivativeReal fLift hx0 (-p) = inner ℝ g (-p) := by
          -- Apply the same singleton-subdifferential identification in the opposite direction.
          have hgreatest :=
            convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior
              hfWithTop hx0 (-p)
          rw [convexDirectionalDerivativeReal_apply] at hgreatest
          rw [hsub] at hgreatest
          simpa using hgreatest.1
        have hsecantNeg :=
          tendsto_directionalSecantQuotient_of_mem_interior
            hfWithTop hx0 (-p)
        rw [convexDirectionalDerivativeReal_apply] at hsecantNeg
        simpa [hdirNeg] using hsecantNeg
      have hleftNeg :
          Filter.Tendsto
            (fun α : ℝ ↦ -((f (x0 + (-α) • (-p)) - f x0) / (-α)))
            (𝓝[<] (0 : ℝ)) (𝓝 (-inner ℝ g (-p))) := by
        have hneg :
            Filter.Tendsto (fun α : ℝ ↦ -α) (𝓝[<] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
          have hneg' :
              Filter.Tendsto Neg.neg (𝓝[<] (0 : ℝ)) (𝓝[>] (-(0 : ℝ))) :=
            tendsto_neg_nhdsLT
          simpa using hneg'
        -- Pull the positive-direction formula for `-p` back to negative times along `p`.
        exact (hrightNeg.comp hneg).neg
      simpa [div_eq_mul_inv, inv_neg, inner_neg_right, smul_smul] using hleftNeg
    -- Combine the left and right secant limits into the two-sided line derivative.
    change HasDerivAt (fun α : ℝ ↦ f (x0 + α • p)) (inner ℝ g p) 0
    rw [hasDerivAt_iff_tendsto_slope_left_right]
    exact ⟨by simpa [slope_fun_def_field] using hleft,
      by simpa [slope_fun_def_field] using hright⟩
  obtain ⟨K, s, hs_nhds, hs_lipschitz⟩ := (ConvexOn.locallyLipschitz hf) x0
  obtain ⟨fExt, hfExt_lipschitz, hEqOn⟩ := hs_lipschitz.extend_finite_dimension
  have hEq : fExt =ᶠ[𝓝 x0] f := by
    -- The finite-dimensional extension agrees with `f` on a whole neighborhood of `x₀`.
    exact Filter.mem_of_superset hs_nhds fun x hx ↦ (hEqOn hx).symm
  have hlineExt :
      ∀ v ∈ (Set.univ : Set E), HasLineDerivAt ℝ fExt (innerSL ℝ g v) x0 v := by
    intro v hv
    -- Transfer the already-known line derivative through eventual equality near `x₀`.
    simpa using (hline v).congr_of_eventuallyEq hEq
  have hsphere :
      Metric.sphere (0 : E) 1 ⊆ closure (Set.univ : Set E) := by
    simpa
  have hfdExt : HasFDerivAt fExt (innerSL ℝ g) x0 := by
    -- The global Lipschitz extension upgrades the line derivatives to a Fréchet derivative.
    exact
      hfExt_lipschitz.hasFDerivAt_of_hasLineDerivAt_of_closure
        hsphere hlineExt
  have hfd : HasFDerivAt f (innerSL ℝ g) x0 := by
    -- Return from the extension to the original function near the base point.
    simpa using hfdExt.congr_of_eventuallyEq hEq.symm
  -- Read the Fréchet derivative back as the gradient vector `g`.
  simpa [hasGradientAt_iff_hasFDerivAt] using hfd

/-- Helper for Proposition 7.28: an argmax point rewrites the owner value `Uβ hatP F x0 β s`
as the corresponding textbook payoff at that point. -/
lemma supportFunctionApproximation_value_eq_of_memArgmax
    {s : StrongDual ℝ E} {u : E}
    (hu : u ∈ Argmaxβ hatP F β s) :
    Uβ hatP F x0 β s = s (u - x0) - β * (F u - F x0) := by
  rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff] at hu
  rcases hu with ⟨hu_mem, hu_max⟩
  have hscore :
      smoothedPrimalObjectiveMaximand
          (ContinuousLinearMap.id ℝ (StrongDual ℝ E))
          0
          F
          (β : ℝ)
          s =
        (fun v : E ↦ s v - β * F v) := by
    -- The specialized Chapter 6 maximand is exactly the unshifted score.
    funext v
    simp [smoothedPrimalObjectiveMaximand]
  have hgreatest :
      IsGreatest ((fun v : E ↦ s v - β * F v) '' hatP) (s u - β * F u) := by
    refine ⟨⟨u, hu_mem, rfl⟩, ?_⟩
    intro y hy
    rcases hy with ⟨v, hv, rfl⟩
    simpa [hscore] using (isMaxOn_iff.mp hu_max) v hv
  -- Expand the owner formula, then replace the conditional supremum by the attained score.
  rw [Uβ_apply, hgreatest.csSup_eq]
  rw [map_sub, mul_sub]
  ring

/-- Helper for Proposition 7.28: if `u` is active at `s` and `v` is active at `t`, then the
secant increment of `Uβ` is trapped between the pairings with `u - x₀` and `v - x₀`. -/
lemma supportFunctionApproximation_secant_bounds_of_memArgmax
    {s t : StrongDual ℝ E} {u v : E}
    (hu : u ∈ Argmaxβ hatP F β s)
    (hv : v ∈ Argmaxβ hatP F β t) :
    (t - s) (u - x0) ≤ Uβ hatP F x0 β t - Uβ hatP F x0 β s ∧
      Uβ hatP F x0 β t - Uβ hatP F x0 β s ≤ (t - s) (v - x0) := by
  rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff] at hu hv
  rcases hu with ⟨hu_mem, hu_max⟩
  rcases hv with ⟨hv_mem, hv_max⟩
  have hscoreS :
      smoothedPrimalObjectiveMaximand
          (ContinuousLinearMap.id ℝ (StrongDual ℝ E))
          0
          F
          (β : ℝ)
          s =
        (fun z : E ↦ s z - β * F z) := by
    -- Rewrite the specialized Chapter 6 maximand at the base slope.
    funext z
    simp [smoothedPrimalObjectiveMaximand]
  have hscoreT :
      smoothedPrimalObjectiveMaximand
          (ContinuousLinearMap.id ℝ (StrongDual ℝ E))
          0
          F
          (β : ℝ)
          t =
        (fun z : E ↦ t z - β * F z) := by
    -- Rewrite the same maximand at the comparison slope.
    funext z
    simp [smoothedPrimalObjectiveMaximand]
  have hs :
      Uβ hatP F x0 β s = s (u - x0) - β * (F u - F x0) := by
    -- Repackage the base-point argmax as the explicit owner value formula.
    exact
      supportFunctionApproximation_value_eq_of_memArgmax
        hatP F x0 β (by
          rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff]
          exact ⟨hu_mem, hu_max⟩)
  have ht :
      Uβ hatP F x0 β t = t (v - x0) - β * (F v - F x0) := by
    -- Do the same at the comparison point `t`.
    exact
      supportFunctionApproximation_value_eq_of_memArgmax
        hatP F x0 β (by
          rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff]
          exact ⟨hv_mem, hv_max⟩)
  have htu : t u - β * F u ≤ t v - β * F v := by
    -- The `t`-active point `v` dominates the score of the base active point `u`.
    simpa [hscoreT] using (isMaxOn_iff.mp hv_max) u hu_mem
  have hsv : s v - β * F v ≤ s u - β * F u := by
    -- The `s`-active point `u` dominates the score of the comparison active point `v`.
    simpa [hscoreS] using (isMaxOn_iff.mp hu_max) v hv_mem
  constructor
  · -- Compare `Uβ t` to the value of the same slice `u` at `t`.
    rw [hs, ht]
    have htu_shifted :
        t (u - x0) - β * (F u - F x0) ≤ t (v - x0) - β * (F v - F x0) := by
      rw [map_sub, map_sub, mul_sub, mul_sub]
      linarith
    have hsecantU :
        (t - s) (u - x0) =
          (t (u - x0) - β * (F u - F x0)) -
            (s (u - x0) - β * (F u - F x0)) := by
      rw [ContinuousLinearMap.sub_apply, mul_sub]
      ring
    calc
      (t - s) (u - x0)
          = (t (u - x0) - β * (F u - F x0)) -
              (s (u - x0) - β * (F u - F x0)) := hsecantU
      _ ≤ (t (v - x0) - β * (F v - F x0)) -
            (s (u - x0) - β * (F u - F x0)) := by
            linarith
  · -- Compare `Uβ s` to the value of the same slice `v` at `s`.
    rw [hs, ht]
    have hsv_shifted :
        s (v - x0) - β * (F v - F x0) ≤ s (u - x0) - β * (F u - F x0) := by
      rw [map_sub, map_sub, mul_sub, mul_sub]
      linarith
    have hsecantV :
        (t - s) (v - x0) =
          (t (v - x0) - β * (F v - F x0)) -
            (s (v - x0) - β * (F v - F x0)) := by
      rw [ContinuousLinearMap.sub_apply, mul_sub]
      ring
    calc
      (t (v - x0) - β * (F v - F x0)) -
          (s (u - x0) - β * (F u - F x0))
          ≤ (t (v - x0) - β * (F v - F x0)) -
              (s (v - x0) - β * (F v - F x0)) := by
              linarith
      _ = (t - s) (v - x0) := hsecantV.symm

-- Proof sketch: pull the owner function back along `InnerProductSpace.toDual`,
-- identify the pulled-back envelope with the shifted convex dual, use the
-- global selector to show the pulled-back subdifferential is singleton, and
-- transport the resulting gradient back to `StrongDual ℝ E`.
/-- Helper for Proposition 7.28: the selected active point at slope `t` is a subgradient of the
pulled-back owner function `y ↦ Uβ ... ((toDual) y)`. -/
lemma supportFunctionApproximation_pullback_subgradient_of_selector
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t : E) :
    uStar ((InnerProductSpace.toDual ℝ E) t) - x0 ∈
      ∂ (fun y : E ↦
          (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y) : WithTop ℝ))(t) := by
  rw [mem_subdifferential_coe_real_iff]
  intro y
  have hsecant :=
    (supportFunctionApproximation_secant_bounds_of_memArgmax
      hatP F x0 β
      (huStar ((InnerProductSpace.toDual ℝ E) t))
      (huStar ((InnerProductSpace.toDual ℝ E) y))).1
  have hpair :
      inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) (y - t) ≤
        Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y) -
          Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) t) := by
    -- Rewrite the dual secant lower bound as the primal-space pairing inequality.
    have hpair' :
        inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) y ≤
          Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y) -
            Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) t) +
              inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) t := by
      simpa [ContinuousLinearMap.sub_apply, InnerProductSpace.toDual_apply_apply,
        real_inner_comm] using hsecant
    rw [inner_sub_right]
    linarith
  linarith

/-- Helper for Proposition 7.28: the selector supplies a nonempty constrained
subdifferential of the pulled-back owner function on `Set.univ` at every point. -/
lemma supportFunctionApproximation_pullback_constrainedSubdifferential_nonempty_of_selector
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s) :
    ∀ t : E,
      (∂[Set.univ] (fun y : E ↦
        (((Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y)) : ℝ) : WithTop ℝ)) (t)).Nonempty := by
  intro t
  refine ⟨uStar ((InnerProductSpace.toDual ℝ E) t) - x0, ?_⟩
  rw [mem_constrainedSubdifferential_iff]
  constructor
  · -- The whole-space constrained subdifferential imposes no feasibility restriction.
    simp
  constructor
  · -- The pulled-back owner is real-valued, so its effective domain is all of `E`.
    constructor <;> simp
  · -- Reuse the whole-space subgradient inequality already proved for the selector.
    intro y hy
    exact_mod_cast
      (mem_subdifferential_coe_real_iff.mp
        (supportFunctionApproximation_pullback_subgradient_of_selector
          hatP F x0 β uStar huStar t)) y

/-- Helper for Proposition 7.28: the pulled-back owner function is convex on
all of `E` once a global argmax selector is available. -/
lemma supportFunctionApproximation_pullback_convexOn_univ_of_selector
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s) :
    ConvexOn ℝ Set.univ
      (fun t : E ↦ Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) t)) := by
  let fLift : E → WithTop ℝ := fun y ↦
    (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y) : WithTop ℝ)
  have hsub_nonempty :
      ∀ t ∈ (Set.univ : Set E), (∂[Set.univ] fLift(t)).Nonempty := by
    intro t ht
    -- The selector produces a concrete constrained subgradient at each base point.
    simpa [fLift] using
      supportFunctionApproximation_pullback_constrainedSubdifferential_nonempty_of_selector
        hatP F x0 β uStar huStar t
  have hconv :
      ConvexOn ℝ Set.univ (withTopRealPart fLift) :=
    convexOn_of_constrainedSubdifferential_nonempty
      Set.univ fLift convex_univ hsub_nonempty
  -- The lifted finite real part is exactly the real-valued pulled-back owner.
  simpa [fLift, withTopRealPart] using hconv

/-- Helper for Proposition 7.28: a pulled-back subgradient is bounded above by the selector
pairings at nearby forward points. -/
lemma inner_le_selectorPairing_of_mem_pullbackSubdifferential
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) {g : E}
    (hg : g ∈
      ∂ (fun y : E ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y) : WithTop ℝ))(t))
    {α : ℝ} (hα : 0 < α) :
    inner ℝ g d ≤ inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + α • d)) - x0) d := by
  have hsub :=
    mem_subdifferential_coe_real_iff.mp hg (t + α • d)
  have hsecant :=
    (supportFunctionApproximation_secant_bounds_of_memArgmax
      hatP F x0 β
      (huStar ((InnerProductSpace.toDual ℝ E) t))
      (huStar ((InnerProductSpace.toDual ℝ E) (t + α • d)))).2
  have hsub' :
      α * inner ℝ g d ≤
        Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) -
          Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) t) := by
    -- Rewrite the subgradient inequality at the forward point as a secant lower bound.
    have hinner :
        inner ℝ g (t + α • d - t) = α * inner ℝ g d := by
      simp [inner_smul_right]
    rw [hinner] at hsub
    linarith
  have hsecant' :
      Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) -
          Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) t) ≤
        α * inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + α • d)) - x0) d := by
    -- The secant upper bound along the pulled-back line is exactly the selector pairing.
    simpa [ContinuousLinearMap.sub_apply, InnerProductSpace.toDual_apply_apply,
      real_inner_comm, inner_add_right, inner_smul_right, sub_eq_add_neg] using hsecant
  have hmul :
      α * inner ℝ g d ≤ α * inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + α • d)) - x0) d :=
    hsub'.trans hsecant'
  nlinarith

/-- Helper for Proposition 7.28: a pulled-back subgradient is bounded below by the selector
pairings at nearby backward points. -/
lemma selectorPairing_le_inner_of_mem_pullbackSubdifferential
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) {g : E}
    (hg : g ∈
      ∂ (fun y : E ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y) : WithTop ℝ))(t))
    {α : ℝ} (hα : 0 < α) :
    inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t - α • d)) - x0) d ≤ inner ℝ g d := by
  -- Apply the forward bound in direction `-d`, then rewrite the same pairing.
  have hforward :=
    inner_le_selectorPairing_of_mem_pullbackSubdifferential
      hatP F x0 β uStar huStar t (-d) hg hα
  simpa [sub_eq_add_neg, inner_neg_right] using hforward

/-- Helper for Proposition 7.28: restricting the pulled-back selector subgradient to any affine
line through `t` yields a scalar subgradient of the corresponding line slice at `0`. -/
lemma supportFunctionApproximation_line_subgradient_of_selector
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) :
    inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d ∈
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) := by
  have hsub :=
    supportFunctionApproximation_pullback_subgradient_of_selector
      hatP F x0 β uStar huStar t
  rw [mem_subdifferential_coe_real_iff] at hsub ⊢
  intro α
  -- Evaluate the ambient support inequality on the affine line `α ↦ t + α • d`.
  have hline := hsub (t + α • d)
  simpa [RCLike.inner_apply, InnerProductSpace.toDual_apply_apply, inner_smul_right,
    sub_eq_add_neg, zero_smul, add_assoc, add_left_comm, add_comm, mul_comm, mul_left_comm,
    mul_assoc] using hline

/-- Helper for Proposition 7.28: the selector slope at the base point is a lower bound for every
forward secant quotient of the scalar line slice. -/
lemma selectorSlope_le_rightSecant_of_unique_argmax
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) {α : ℝ} (hα : 0 < α) :
    inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d ≤
      (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) -
        Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) t)) / α := by
  have hsub :=
    supportFunctionApproximation_line_subgradient_of_selector
      hatP F x0 β uStar huStar t d
  rw [mem_subdifferential_coe_real_iff] at hsub
  have hline :
      Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) ≥
        Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) t) +
          α * inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d := by
    -- Evaluate the selector support line at the forward scalar step `α`.
    simpa [inner_smul_right, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm,
      add_assoc, add_left_comm, add_comm] using hsub α
  -- Divide the forward support inequality by the positive step size.
  exact (le_div_iff₀ hα).2 (by linarith)

/-- Helper for Proposition 7.28: the selector slope at the base point is an upper bound for every
backward secant quotient of the scalar line slice. -/
lemma leftSecant_le_selectorSlope_of_unique_argmax
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) {α : ℝ} (hα : 0 < α) :
    (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) t) -
        Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t - α • d))) / α ≤
      inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d := by
  have hsub :=
    supportFunctionApproximation_line_subgradient_of_selector
      hatP F x0 β uStar huStar t d
  rw [mem_subdifferential_coe_real_iff] at hsub
  have hline :
      Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t - α • d)) ≥
        Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) t) -
          α * inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d := by
    -- Evaluate the same support line at the backward scalar step `-α`.
    simpa [inner_smul_right, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm,
      add_assoc, add_left_comm, add_comm] using hsub (-α)
  -- Rearranging the backward support inequality gives the desired secant upper bound.
  exact (div_le_iff₀ hα).2 (by linarith)

/-- Helper for Proposition 7.28: any pulled-back subgradient restricts to a scalar subgradient on
every affine line through the base point. -/
lemma supportFunctionApproximation_line_subgradient_of_mem_pullbackSubdifferential
    (t d : E) {g : E}
    (hg : g ∈
      ∂ (fun y : E ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y) : WithTop ℝ))(t)) :
    inner ℝ g d ∈
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) := by
  rw [mem_subdifferential_coe_real_iff] at hg ⊢
  intro α
  -- The ambient support inequality specializes directly to the chosen line.
  have hline := hg (t + α • d)
  simpa [RCLike.inner_apply, inner_smul_right, sub_eq_add_neg, zero_smul, add_assoc,
    add_left_comm, add_comm, mul_comm, mul_left_comm, mul_assoc] using hline

/-- Helper for Proposition 7.28: along any affine line, the secant quotient of the pulled-back
owner is squeezed between the selector pairings at the endpoint maximizers. -/
lemma supportFunctionApproximation_line_secantQuotient_bounds_of_unique_argmax
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) {α β' : ℝ} (hαβ : α < β') :
    inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + α • d)) - x0) d ≤
      (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + β' • d)) -
        Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d))) / (β' - α) ∧
      (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + β' • d)) -
        Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d))) / (β' - α) ≤
        inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + β' • d)) - x0) d := by
  let Δ : ℝ :=
    Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + β' • d)) -
      Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d))
  have hden : 0 < β' - α := sub_pos.mpr hαβ
  have hsecant :=
    supportFunctionApproximation_secant_bounds_of_memArgmax
      hatP F x0 β
      (huStar ((InnerProductSpace.toDual ℝ E) (t + α • d)))
      (huStar ((InnerProductSpace.toDual ℝ E) (t + β' • d)))
  constructor
  · -- Divide the lower secant bound by the positive line increment.
    have hleftRaw :
        β' * inner ℝ d (uStar ((InnerProductSpace.toDual ℝ E) (t + α • d)) - x0) ≤
          Δ +
            α * inner ℝ d (uStar ((InnerProductSpace.toDual ℝ E) (t + α • d)) - x0) := by
      -- Normalize the dual secant inequality to the explicit scalar line slice.
      simpa [Δ, ContinuousLinearMap.sub_apply, InnerProductSpace.toDual_apply_apply]
        using hsecant.1
    have hleft :
        (β' - α) * inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + α • d)) - x0) d ≤
          Δ := by
      nlinarith [hleftRaw, real_inner_comm d (uStar ((InnerProductSpace.toDual ℝ E) (t + α • d)) - x0)]
    change inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + α • d)) - x0) d ≤ Δ / (β' - α)
    field_simp [hden.ne']
    simpa [mul_comm] using hleft
  · -- Divide the upper secant bound by the same positive increment.
    have hrightRaw :
        Δ ≤
          β' * inner ℝ d (uStar ((InnerProductSpace.toDual ℝ E) (t + β' • d)) - x0) -
            α * inner ℝ d (uStar ((InnerProductSpace.toDual ℝ E) (t + β' • d)) - x0) := by
      -- Normalize the endpoint-pairing upper bound in the same scalar coordinates.
      simpa [Δ, ContinuousLinearMap.sub_apply, InnerProductSpace.toDual_apply_apply]
        using hsecant.2
    have hright :
        Δ ≤
          (β' - α) * inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + β' • d)) - x0) d := by
      nlinarith [hrightRaw,
        real_inner_comm d (uStar ((InnerProductSpace.toDual ℝ E) (t + β' • d)) - x0)]
    change Δ / (β' - α) ≤ inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + β' • d)) - x0) d
    field_simp [hden.ne']
    simpa [mul_comm] using hright

/-- Helper for Proposition 7.28: the selector pairing along any affine line is monotone in the
line parameter because each secant quotient lies between the endpoint pairings. -/
lemma supportFunctionApproximation_line_selectorPairing_mono_of_unique_argmax
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) {α β' : ℝ} (hαβ : α ≤ β') :
    inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + α • d)) - x0) d ≤
      inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + β' • d)) - x0) d := by
  rcases lt_or_eq_of_le hαβ with hlt | rfl
  · -- The secant quotient bridge bounds the left endpoint pairing by the right endpoint pairing.
    exact
      (supportFunctionApproximation_line_secantQuotient_bounds_of_unique_argmax
        hatP F x0 β uStar huStar t d hlt).1.trans
        (supportFunctionApproximation_line_secantQuotient_bounds_of_unique_argmax
          hatP F x0 β uStar huStar t d hlt).2
  · -- Equal parameters give the same selector pairing.
    rfl

/-- Helper for Proposition 7.28: restricting the pulled-back owner to an affine line in `E`
preserves convexity on all of `ℝ`. -/
lemma supportFunctionApproximation_line_convexOn_univ_of_selector
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) :
    ConvexOn ℝ Set.univ
      (fun α : ℝ ↦
        Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d))) := by
  have hpullback :
      ConvexOn ℝ Set.univ
        (fun y : E ↦ Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y)) :=
    supportFunctionApproximation_pullback_convexOn_univ_of_selector
      hatP F x0 β uStar huStar
  -- Compose the ambient convex owner with the affine line `α ↦ t + α • d`.
  convert hpullback.comp_affineMap (AffineMap.lineMap t (t + d)) using 1
  ext α
  simp [AffineMap.lineMap_apply_module, smoothedPrimalObjectiveMaximand,
    InnerProductSpace.toDual_apply_apply, inner_add_right, inner_smul_right, real_inner_comm,
    add_comm, add_left_comm, add_assoc, smul_add, add_smul, sub_eq_add_neg, mul_comm,
    mul_left_comm, mul_assoc]

/-- Helper for Proposition 7.28: the scalar line slice is real-valued everywhere, so `0` lies in
the interior of its effective domain. -/
lemma supportFunctionApproximation_line_zero_mem_interior_dom
    (t d : E) :
    (0 : ℝ) ∈ interior
      (dom (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))) := by
  -- The pulled-back line slice is real-valued, so its effective domain is all of `ℝ`.
  have hdom :
      dom (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ)) =
        (Set.univ : Set ℝ) := by
    ext α
    change (((Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : ℝ) : WithTop ℝ) < ⊤) ↔ True
    constructor
    · intro _
      trivial
    · intro _
      exact WithTop.coe_lt_top _
  -- Every point of `ℝ`, in particular `0`, lies in the interior of `Set.univ`.
  rw [hdom]
  simp

/-- Helper for Proposition 7.28: along any affine line through `t`, the pulled-back owner is the
attained affine slice corresponding to the active selector, and every feasible slice lies below
that value. -/
lemma supportFunctionApproximation_line_affineSupremumData
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) (α : ℝ) :
    let sα : StrongDual ℝ E := (InnerProductSpace.toDual ℝ E) (t + α • d)
    let a : E → ℝ := fun u ↦ inner ℝ (u - x0) t - β * (F u - F x0)
    let b : E → ℝ := fun u ↦ inner ℝ (u - x0) d
    Uβ hatP F x0 β sα = a (uStar sα) + α * b (uStar sα) ∧
      ∀ u ∈ hatP, a u + α * b u ≤ Uβ hatP F x0 β sα := by
  let sα : StrongDual ℝ E := (InnerProductSpace.toDual ℝ E) (t + α • d)
  let a : E → ℝ := fun u ↦ inner ℝ (u - x0) t - β * (F u - F x0)
  let b : E → ℝ := fun u ↦ inner ℝ (u - x0) d
  have hsα :
      Uβ hatP F x0 β sα = sα (uStar sα - x0) - β * (F (uStar sα) - F x0) :=
    supportFunctionApproximation_value_eq_of_memArgmax
      hatP F x0 β (huStar sα)
  have huStar_max : IsMaxOn
      (smoothedPrimalObjectiveMaximand
        (ContinuousLinearMap.id ℝ (StrongDual ℝ E))
        0
        F
        (β : ℝ)
        sα)
      hatP
      (uStar sα) := by
    -- Unpack the selected point as a maximizer for the raw Chapter 6 score.
    have huStar_sα : uStar sα ∈ Argmaxβ hatP F β sα := huStar sα
    rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff] at huStar_sα
    exact huStar_sα.2
  have hscore :
      smoothedPrimalObjectiveMaximand
          (ContinuousLinearMap.id ℝ (StrongDual ℝ E))
          0
          F
          (β : ℝ)
          sα =
        (fun u : E ↦ sα u - β * F u) := by
    -- The specialized Chapter 6 score is the affine term minus the barrier term.
    funext u
    simp [smoothedPrimalObjectiveMaximand]
  constructor
  · -- Rewrite the owner value at `sα` into the displayed affine slice at the active selector.
    rw [hsα]
    have howner_star :
        inner ℝ t (uStar sα - x0) + α * inner ℝ d (uStar sα - x0) =
          inner ℝ (t + α • d) (uStar sα - x0) := by
      calc
        inner ℝ t (uStar sα - x0) + α * inner ℝ d (uStar sα - x0)
            = inner ℝ t (uStar sα - x0) + inner ℝ (α • d) (uStar sα - x0) := by
                rw [real_inner_smul_left]
        _ = inner ℝ (t + α • d) (uStar sα - x0) := by
              rw [inner_add_left]
    calc
      sα (uStar sα - x0) - β * (F (uStar sα) - F x0)
          = inner ℝ t (uStar sα - x0) + α * inner ℝ d (uStar sα - x0) -
              β * (F (uStar sα) - F x0) := by
              dsimp [sα]
              simp [InnerProductSpace.toDual_apply_apply, inner_add_left, real_inner_smul_left]
      _ = inner ℝ (t + α • d) (uStar sα - x0) - β * (F (uStar sα) - F x0) := by
              exact
                congrArg
                  (fun r : ℝ ↦ r - β * (F (uStar sα) - F x0))
                  howner_star
      _ = inner ℝ t (uStar sα - x0) + α * inner ℝ d (uStar sα - x0) -
            β * (F (uStar sα) - F x0) := by
              exact
                (congrArg
                  (fun r : ℝ ↦ r - β * (F (uStar sα) - F x0))
                  howner_star).symm
      _ = inner ℝ (uStar sα - x0) t + α * inner ℝ (uStar sα - x0) d -
            β * (F (uStar sα) - F x0) := by
              rw [real_inner_comm t (uStar sα - x0), real_inner_comm d (uStar sα - x0)]
      _ = a (uStar sα) + α * b (uStar sα) := by
              simp [a, b]
              ring
  · intro u hu
    have hbound_raw : sα u - β * F u ≤ sα (uStar sα) - β * F (uStar sα) := by
      -- Maximality of `uStar sα` bounds every feasible raw score from above.
      simpa [hscore] using (isMaxOn_iff.mp huStar_max) u hu
    -- Remove the common constant shift `-sα x0 + β * F x0` to recover the affine slice bound.
    have hbound_shifted :
        sα (u - x0) - β * (F u - F x0) ≤
          sα (uStar sα - x0) - β * (F (uStar sα) - F x0) := by
      rw [ContinuousLinearMap.map_sub, ContinuousLinearMap.map_sub, mul_sub, mul_sub]
      linarith
    have howner_u :
        inner ℝ (t + α • d) (u - x0) =
          inner ℝ t (u - x0) + α * inner ℝ d (u - x0) := by
      calc
        inner ℝ (t + α • d) (u - x0)
            = inner ℝ t (u - x0) + inner ℝ (α • d) (u - x0) := by
                rw [inner_add_left]
        _ = inner ℝ t (u - x0) + α * inner ℝ d (u - x0) := by
              rw [real_inner_smul_left]
    calc
      a u + α * b u
          = sα (u - x0) - β * (F u - F x0) := by
              calc
                a u + α * b u
                    = inner ℝ (u - x0) t + α * inner ℝ (u - x0) d -
                        β * (F u - F x0) := by
                          simp [a, b]
                          ring
                _ = inner ℝ t (u - x0) + α * inner ℝ d (u - x0) -
                      β * (F u - F x0) := by
                      rw [real_inner_comm t (u - x0), real_inner_comm d (u - x0)]
                _ = inner ℝ (t + α • d) (u - x0) - β * (F u - F x0) := by
                      exact
                        (congrArg
                          (fun r : ℝ ↦ r - β * (F u - F x0))
                          howner_u).symm
                _ = inner ℝ t (u - x0) + α * inner ℝ d (u - x0) -
                      β * (F u - F x0) := by
                      exact
                        congrArg
                          (fun r : ℝ ↦ r - β * (F u - F x0))
                          howner_u
                _ = sα (u - x0) - β * (F u - F x0) := by
                      dsimp [sα]
                      simp [InnerProductSpace.toDual_apply_apply, inner_add_left, real_inner_smul_left]
      _ ≤ sα (uStar sα - x0) - β * (F (uStar sα) - F x0) := hbound_shifted
      _ = Uβ hatP F x0 β sα := hsα.symm

/-- Helper for Proposition 7.28: a scalar affine slice has singleton subdifferential given by its
displayed slope. -/
lemma supportFunctionApproximation_affineScalarSlice_subdifferential_eq_singleton
    (a slope : ℝ) :
    ∂ (fun α : ℝ ↦ ((a + α * slope : ℝ) : WithTop ℝ))(0) = {slope} := by
  ext g
  rw [Set.mem_singleton_iff, mem_subdifferential_coe_real_iff]
  have hinner (x y : ℝ) : inner ℝ x y = x * y := by
    -- On the real line, the ambient inner product is ordinary multiplication.
    simpa using real_inner_eq_mul x y
  constructor
  · intro hg
    have hpos : a + g ≤ a + slope := by
      -- Test the support inequality at `1` to bound the candidate slope above.
      simpa [hinner, mul_comm] using hg 1
    have hneg : a + -g + slope ≤ a := by
      -- Test the same inequality at `-1` to bound the candidate slope below.
      simpa [hinner, mul_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hg (-1)
    linarith
  · intro hg
    subst hg
    intro y
    -- The displayed slope supports its own affine slice with equality at every point.
    simpa [hinner, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]

/-- Helper for Proposition 7.28: every scalar subgradient of the pulled-back line slice is bounded
above by the selector pairing at each nearby forward point. -/
lemma lineSubgradient_le_selectorPairing_of_unique_argmax
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) {g : ℝ}
    (hg : g ∈
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0))
    {α : ℝ} (hα : 0 < α) :
    g ≤ inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + α • d)) - x0) d := by
  let φ : ℝ → ℝ := fun τ ↦
    Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + τ • d))
  have hinner_y (y : ℝ) : inner ℝ g y = g * y := by
    calc
      inner ℝ g y = inner ℝ g (y • (1 : ℝ)) := by simp
      _ = y * inner ℝ g (1 : ℝ) := by rw [real_inner_smul_right]
      _ = g * y := by
        have hinner_one : inner ℝ g (1 : ℝ) = g := by
          calc
            inner ℝ g (1 : ℝ) = inner ℝ ((g : ℝ) • (1 : ℝ)) (1 : ℝ) := by simp
            _ = g * inner ℝ (1 : ℝ) (1 : ℝ) := by rw [real_inner_smul_left]
            _ = g := by norm_num
        rw [hinner_one]
        ring
  have hsub := mem_subdifferential_coe_real_iff.mp hg α
  have hquot :
      g ≤ (φ α - φ 0) / α := by
    -- The subgradient inequality at the forward point controls the secant quotient from below.
    have hsub' : φ α ≥ φ 0 + g * α := by
      simpa [φ, hinner_y, mul_comm] using hsub
    have hmul : g * α ≤ φ α - φ 0 := by
      linarith
    exact (le_div_iff₀ hα).2 hmul
  have hsecant :=
    (supportFunctionApproximation_line_secantQuotient_bounds_of_unique_argmax
      hatP F x0 β uStar huStar t d (α := 0) (β' := α) hα).2
  -- The selector at the forward endpoint bounds the same secant quotient from above.
  have hsecant' :
      (φ α - φ 0) / α ≤
        inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + α • d)) - x0) d := by
    simpa [φ, zero_smul, sub_eq_add_neg] using hsecant
  exact hquot.trans hsecant'

/-- Helper for Proposition 7.28: every scalar subgradient of the pulled-back line slice is bounded
below by the selector pairing at each nearby backward point. -/
lemma selectorPairing_le_lineSubgradient_of_unique_argmax
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) {g : ℝ}
    (hg : g ∈
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0))
    {α : ℝ} (hα : 0 < α) :
    inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t - α • d)) - x0) d ≤ g := by
  let φ : ℝ → ℝ := fun τ ↦
    Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + τ • d))
  have hinner_y (y : ℝ) : inner ℝ g y = g * y := by
    calc
      inner ℝ g y = inner ℝ g (y • (1 : ℝ)) := by simp
      _ = y * inner ℝ g (1 : ℝ) := by rw [real_inner_smul_right]
      _ = g * y := by
        have hinner_one : inner ℝ g (1 : ℝ) = g := by
          calc
            inner ℝ g (1 : ℝ) = inner ℝ ((g : ℝ) • (1 : ℝ)) (1 : ℝ) := by simp
            _ = g * inner ℝ (1 : ℝ) (1 : ℝ) := by rw [real_inner_smul_left]
            _ = g := by norm_num
        rw [hinner_one]
        ring
  have hsub := mem_subdifferential_coe_real_iff.mp hg (-α)
  have hquot :
      (φ 0 - φ (-α)) / α ≤ g := by
    -- The same subgradient inequality at the backward point bounds the backward secant quotient.
    have hsub' : φ (-α) ≥ φ 0 + g * (-α) := by
      simpa [φ, hinner_y, mul_comm] using hsub
    have hmul : φ 0 - φ (-α) ≤ g * α := by
      linarith
    exact (div_le_iff₀ hα).2 hmul
  have hsecant :=
    (supportFunctionApproximation_line_secantQuotient_bounds_of_unique_argmax
      hatP F x0 β uStar huStar t d (α := -α) (β' := 0) (by linarith)).1
  -- The selector at the backward endpoint bounds the same secant quotient from below.
  have hsecant' :
      inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t - α • d)) - x0) d ≤
        (φ 0 - φ (-α)) / α := by
    simpa [φ, zero_smul, sub_eq_add_neg] using hsecant
  exact hsecant'.trans hquot

/-- Helper for Proposition 7.28: the scalar subgradient at `0` is trapped between the selector
pairings of the nearby backward and forward active slices. -/
lemma selectorSlope_sandwich_of_mem_lineSubdifferential
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) {g : ℝ}
    (hg : g ∈
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0))
    {α : ℝ} (hα : 0 < α) :
    inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t - α • d)) - x0) d ≤ g ∧
      g ≤ inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + α • d)) - x0) d := by
  -- The forward and backward one-sided bounds package into the desired sandwich.
  exact
    ⟨selectorPairing_le_lineSubgradient_of_unique_argmax
        hatP F x0 β uStar huStar t d hg hα,
      lineSubgradient_le_selectorPairing_of_unique_argmax
        hatP F x0 β uStar huStar t d hg hα⟩

/-- Helper for Proposition 7.28: at parameter `0`, the affine-supremum data for the line slice
reduce to the active intercept formula and its universal upper bound on `hatP`. -/
lemma supportFunctionApproximation_line_affineSupremumData_zero
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) :
    let s0 : StrongDual ℝ E := (InnerProductSpace.toDual ℝ E) t
    let a : E → ℝ := fun u ↦ inner ℝ (u - x0) t - β * (F u - F x0)
    Uβ hatP F x0 β s0 = a (uStar s0) ∧
      ∀ u ∈ hatP, a u ≤ Uβ hatP F x0 β s0 := by
  -- Specialize the affine-supremum identity to `α = 0`.
  simpa using
    (supportFunctionApproximation_line_affineSupremumData
      hatP F x0 β uStar huStar t d (0 : ℝ))

/-- Helper for Proposition 7.28: at `α = 0`, any feasible slice with the same affine intercept as
the active selector must have the same displayed slope. -/
lemma lineSlice_zeroActiveSlopeData_of_unique_argmax
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) :
    let s0 : StrongDual ℝ E := (InnerProductSpace.toDual ℝ E) t
    let φ : ℝ → ℝ := fun α ↦
      Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d))
    let a : E → ℝ := fun u ↦ inner ℝ (u - x0) t - β * (F u - F x0)
    let b : E → ℝ := fun u ↦ inner ℝ (u - x0) d
    φ 0 = a (uStar s0) ∧
      (∀ u ∈ hatP, a u ≤ φ 0) ∧
      ∀ u ∈ hatP, a u = φ 0 → b u = b (uStar s0) := by
  let s0 : StrongDual ℝ E := (InnerProductSpace.toDual ℝ E) t
  let φ : ℝ → ℝ := fun α ↦
    Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d))
  let a : E → ℝ := fun u ↦ inner ℝ (u - x0) t - β * (F u - F x0)
  let b : E → ℝ := fun u ↦ inner ℝ (u - x0) d
  have hzero :
      Uβ hatP F x0 β s0 = a (uStar s0) ∧
        ∀ u ∈ hatP, a u ≤ Uβ hatP F x0 β s0 :=
    supportFunctionApproximation_line_affineSupremumData_zero
      hatP F x0 β uStar huStar t d
  refine ⟨?_, ?_, ?_⟩
  · -- The zero parameter value is the active intercept of the selected slice.
    simpa [s0, φ, a] using hzero.1
  · -- Every feasible intercept lies below the active one at `α = 0`.
    simpa [s0, φ, a] using hzero.2
  · intro u hu hu_eq
    have hu_argmax : u ∈ Argmaxβ hatP F β s0 := by
      rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff]
      refine ⟨hu, ?_⟩
      rw [isMaxOn_iff]
      intro v hv
      have hv_le :
          a v ≤ a u := by
        -- Equality with the owner value turns `u` into another active zero slice.
        calc
          a v ≤ Uβ hatP F x0 β s0 := hzero.2 v hv
          _ = φ 0 := by simp [φ, s0]
          _ = a u := hu_eq.symm
      have hscore_eq (z : E) :
          a z = (s0 z - β * F z) - (s0 x0 - β * F x0) := by
        -- The affine intercept differs from the raw score only by the fixed base-point shift.
        calc
          a z = s0 (z - x0) - β * (F z - F x0) := by
            simp [a, s0, InnerProductSpace.toDual_apply_apply, real_inner_comm]
          _ = (s0 z - β * F z) - (s0 x0 - β * F x0) := by
            rw [ContinuousLinearMap.map_sub, mul_sub]
            ring
      have hscore_le :
          s0 v - β * F v ≤ s0 u - β * F u := by
        -- Remove the common shift `-s0 x0 + β * F x0` from the affine intercept comparison.
        have hv_le' :
            (s0 v - β * F v) - (s0 x0 - β * F x0) ≤
              (s0 u - β * F u) - (s0 x0 - β * F x0) := by
          simpa [hscore_eq] using hv_le
        linarith
      -- Repackage the zero-active intercept comparison as raw-score maximality.
      simpa [s0, smoothedPrimalObjectiveMaximand] using hscore_le
    have hu_eq_star : u = uStar s0 := huStar_unique s0 u hu_argmax
    -- Uniqueness of the zero-active argmax identifies the displayed slope.
    simpa [s0, b, hu_eq_star]

/-- Helper for Proposition 7.28: at `α = 0`, the exact pointwise-supremum presentation of the
line slice agrees with the owner value at the base slope. -/
lemma lineSliceAffineSupremumAtZero_eq_owner
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) :
    let s0 : StrongDual ℝ E := (InnerProductSpace.toDual ℝ E) t
    let a : E → ℝ := fun u ↦ inner ℝ (u - x0) t - β * (F u - F x0)
    let slice : ℝ → hatP → WithTop ℝ := fun α u ↦ ((a u.1 + α * inner ℝ (u.1 - x0) d : ℝ) : WithTop ℝ)
    pointwiseSupremumOn (Set.univ : Set hatP) slice 0 =
      ((Uβ hatP F x0 β s0 : ℝ) : WithTop ℝ) := by
  let s0 : StrongDual ℝ E := (InnerProductSpace.toDual ℝ E) t
  let a : E → ℝ := fun u ↦ inner ℝ (u - x0) t - β * (F u - F x0)
  let slice : ℝ → hatP → WithTop ℝ := fun α u ↦ ((a u.1 + α * inner ℝ (u.1 - x0) d : ℝ) : WithTop ℝ)
  have hzero :
      Uβ hatP F x0 β s0 = a (uStar s0) ∧
        ∀ u ∈ hatP, a u ≤ Uβ hatP F x0 β s0 :=
    supportFunctionApproximation_line_affineSupremumData_zero
      hatP F x0 β uStar huStar t d
  have huStar_mem : uStar s0 ∈ hatP := by
    have huStar_s0 : uStar s0 ∈ Argmaxβ hatP F β s0 := huStar s0
    rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff] at huStar_s0
    exact huStar_s0.1
  let u0 : hatP := ⟨uStar s0, huStar_mem⟩
  apply le_antisymm
  · -- Every feasible affine intercept at `0` lies below the same owner value.
    refine ClosedConvexOn.pointwiseSupremumOn_le_of_forall_le ⟨u0, by simp⟩ ?_
    intro u hu
    have hu_le : a u.1 ≤ Uβ hatP F x0 β s0 := hzero.2 u.1 u.2
    change slice 0 u ≤ ((Uβ hatP F x0 β s0 : ℝ) : WithTop ℝ)
    simpa [slice, a] using
      (show (((a u.1 : ℝ) : WithTop ℝ)) ≤
          ((Uβ hatP F x0 β s0 : ℝ) : WithTop ℝ) from by
            exact_mod_cast hu_le)
  · -- The selected zero-parameter affine slice attains that supremum.
    have hvalue :
        ((Uβ hatP F x0 β s0 : ℝ) : WithTop ℝ) = slice 0 u0 := by
      -- The selected zero-slice is exactly the affine intercept from the owner-value identity.
      simpa [slice, u0] using
        congrArg (fun r : ℝ ↦ ((r : ℝ) : WithTop ℝ)) hzero.1
    calc
      ((Uβ hatP F x0 β s0 : ℝ) : WithTop ℝ) = slice 0 u0 := hvalue
      _ ≤ pointwiseSupremumOn (Set.univ : Set hatP) slice 0 :=
        ClosedConvexOn.slice_le_pointwiseSupremumOn (by simp)

/-- Helper for Proposition 7.28: any affine slice active at `0` in the exact line-supremum
presentation is the selected zero-parameter maximizer. -/
lemma lineSliceActiveAffineIndex_eq_selector_at_zero
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) {u : hatP}
    (huActive :
      u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP)
        (fun α v ↦
          ((inner ℝ (v.1 - x0) t - β * (F v.1 - F x0) +
              α * inner ℝ (v.1 - x0) d : ℝ) : WithTop ℝ)) 0) :
    u.1 = uStar ((InnerProductSpace.toDual ℝ E) t) := by
  let s0 : StrongDual ℝ E := (InnerProductSpace.toDual ℝ E) t
  let a : E → ℝ := fun v ↦ inner ℝ (v - x0) t - β * (F v - F x0)
  let slice : ℝ → hatP → WithTop ℝ := fun α v ↦ ((a v.1 + α * inner ℝ (v.1 - x0) d : ℝ) : WithTop ℝ)
  have hsupAtZero :
      pointwiseSupremumOn (Set.univ : Set hatP) slice 0 =
        ((Uβ hatP F x0 β s0 : ℝ) : WithTop ℝ) := by
    -- The exact pointwise-supremum spelling at `0` is already identified with the owner value.
    simpa [s0, a, slice] using
      (lineSliceAffineSupremumAtZero_eq_owner
        hatP F x0 β uStar huStar t d)
  have huValue :
      a u.1 = Uβ hatP F x0 β s0 := by
    rcases mem_activePointwiseSupremumOnIndices_iff.mp huActive with ⟨-, huActiveEq⟩
    apply WithTop.coe_injective
    calc
      (((a u.1 : ℝ)) : WithTop ℝ) = slice 0 u := by simp [slice]
      _ = pointwiseSupremumOn (Set.univ : Set hatP) slice 0 := huActiveEq
      _ = ((Uβ hatP F x0 β s0 : ℝ) : WithTop ℝ) := hsupAtZero
  have hzero :
      Uβ hatP F x0 β s0 = a (uStar s0) ∧
        ∀ v ∈ hatP, a v ≤ Uβ hatP F x0 β s0 :=
    supportFunctionApproximation_line_affineSupremumData_zero
      hatP F x0 β uStar huStar t d
  have hu_argmax : u.1 ∈ Argmaxβ hatP F β s0 := by
    rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff]
    refine ⟨u.2, ?_⟩
    rw [isMaxOn_iff]
    intro v hv
    have hv_le :
        a v ≤ a u.1 := by
      calc
        a v ≤ Uβ hatP F x0 β s0 := hzero.2 v hv
        _ = a u.1 := huValue.symm
    have hscore_eq (z : E) :
        a z = (s0 z - β * F z) - (s0 x0 - β * F x0) := by
      -- The affine intercept differs from the raw score only by the fixed zero-parameter shift.
      calc
        a z = s0 (z - x0) - β * (F z - F x0) := by
          simp [a, s0, InnerProductSpace.toDual_apply_apply, real_inner_comm]
        _ = (s0 z - β * F z) - (s0 x0 - β * F x0) := by
          rw [ContinuousLinearMap.map_sub, mul_sub]
          ring
    have hscore_le :
        s0 v - β * F v ≤ s0 u.1 - β * F u.1 := by
      -- Removing the common shift turns the active-intercept identity into score maximality.
      have hv_le' :
          (s0 v - β * F v) - (s0 x0 - β * F x0) ≤
            (s0 u.1 - β * F u.1) - (s0 x0 - β * F x0) := by
        simpa [hscore_eq] using hv_le
      linarith
    simpa [s0, smoothedPrimalObjectiveMaximand] using hscore_le
  -- Uniqueness at the zero parameter identifies every active affine index with the selector.
  exact huStar_unique s0 u.1 hu_argmax

/-- Helper for Proposition 7.28: the exact lifted line slice has the same convex owner as the
underlying real-valued line slice. -/
lemma lineSliceLiftConvexOn
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) :
    ConvexOn ℝ
      (dom (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ)))
      (withTopRealPart (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))) := by
  have hdom :
      dom (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ)) =
        (Set.univ : Set ℝ) := by
    -- The lifted line slice is finite at every scalar parameter.
    ext α
    change (((Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : ℝ) :
      WithTop ℝ) < ⊤) ↔ True
    constructor
    · intro _
      trivial
    · intro _
      exact WithTop.coe_lt_top _
  rw [hdom]
  -- Replace the lifted owner by its real-valued line slice without unfolding `Uβ`.
  simpa using
    supportFunctionApproximation_line_convexOn_univ_of_selector
      hatP F x0 β uStar huStar t d

/-- Helper for Proposition 7.28: the selector slope is already a subgradient of the exact lifted
line slice at `0`. -/
lemma lineSliceLiftSelectorMemSubdifferential
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) :
    inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d ∈
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) := by
  -- This is exactly the scalar selector-subgradient bridge in the owner spelling needed below.
  exact
    supportFunctionApproximation_line_subgradient_of_selector
      hatP F x0 β uStar huStar t d

/-- Helper for Proposition 7.28: the exact lifted line slice is the pointwise supremum of the
affine slices indexed by feasible points of `hatP`. -/
lemma lineSliceLift_eq_pointwiseSupremumOnAffineSlices
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) :
    (fun α : ℝ ↦
      (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ)) =
      pointwiseSupremumOn (Set.univ : Set hatP)
        (fun α u ↦
          ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
              α * inner ℝ (u.1 - x0) d : ℝ) : WithTop ℝ)) := by
  let affineSlice : ℝ → hatP → WithTop ℝ := fun α u ↦
    ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
        α * inner ℝ (u.1 - x0) d : ℝ) : WithTop ℝ)
  ext α
  let sα : StrongDual ℝ E := (InnerProductSpace.toDual ℝ E) (t + α • d)
  have huStar_mem :
      uStar sα ∈ hatP := by
    have huStar_sα : uStar sα ∈ Argmaxβ hatP F β sα := huStar sα
    rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff] at huStar_sα
    exact huStar_sα.1
  let uα : hatP := ⟨uStar sα, huStar_mem⟩
  have hdata :=
    supportFunctionApproximation_line_affineSupremumData
      hatP F x0 β uStar huStar t d α
  apply le_antisymm
  · -- The active affine slice at `uα` attains the displayed supremum value.
    have hvalue :
        ((Uβ hatP F x0 β sα : ℝ) : WithTop ℝ) = affineSlice α uα := by
      change
        (((Uβ hatP F x0 β sα : ℝ)) : WithTop ℝ) =
          (((inner ℝ (uStar sα - x0) t - β * (F (uStar sα) - F x0) +
              α * inner ℝ (uStar sα - x0) d : ℝ)) : WithTop ℝ)
      exact congrArg (fun r : ℝ ↦ ((r : ℝ) : WithTop ℝ)) hdata.1
    calc
      ((Uβ hatP F x0 β sα : ℝ) : WithTop ℝ) = affineSlice α uα := hvalue
      _ ≤ pointwiseSupremumOn (Set.univ : Set hatP) affineSlice α :=
          ClosedConvexOn.slice_le_pointwiseSupremumOn (by simp)
  · -- Every feasible affine slice lies below the same line-slice value.
    refine ClosedConvexOn.pointwiseSupremumOn_le_of_forall_le ⟨uα, by simp⟩ ?_
    intro u hu
    have hupper := hdata.2 u.1 u.2
    change affineSlice α u ≤ ((Uβ hatP F x0 β sα : ℝ) : WithTop ℝ)
    simpa [affineSlice] using
      (show
        (((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
            α * inner ℝ (u.1 - x0) d : ℝ) : WithTop ℝ)) ≤
          ((Uβ hatP F x0 β sα : ℝ) : WithTop ℝ) from by
            exact_mod_cast hupper)

/-- Helper for Proposition 7.28: shifting every affine slice by `-α * g` rewrites the exact
line-slice supremum to the owner value minus the same affine term. -/
lemma shiftedLineSliceLift_eq_pointwiseSupremumOnAffineSlices
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) (g α : ℝ) :
    pointwiseSupremumOn (Set.univ : Set hatP)
      (fun τ u ↦
        ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
            τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α =
      (((Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) - α * g : ℝ)) : WithTop ℝ) := by
  let sα : StrongDual ℝ E := (InnerProductSpace.toDual ℝ E) (t + α • d)
  let shiftedSlice : ℝ → hatP → WithTop ℝ := fun τ u ↦
    ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
        τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)
  have huStar_mem : uStar sα ∈ hatP := by
    have huStar_sα : uStar sα ∈ Argmaxβ hatP F β sα := huStar sα
    rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff] at huStar_sα
    exact huStar_sα.1
  let uα : hatP := ⟨uStar sα, huStar_mem⟩
  have hdata :=
    supportFunctionApproximation_line_affineSupremumData
      hatP F x0 β uStar huStar t d α
  apply le_antisymm
  · -- Every shifted affine slice lies below the same shifted owner value.
    refine ClosedConvexOn.pointwiseSupremumOn_le_of_forall_le ⟨uα, by simp⟩ ?_
    intro u hu
    have hupper : shiftedSlice α u ≤ (((Uβ hatP F x0 β sα - α * g : ℝ)) : WithTop ℝ) := by
      have hupperReal :
          inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
              α * (inner ℝ (u.1 - x0) d - g) ≤
            Uβ hatP F x0 β sα - α * g := by
        have hunshifted : inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
            α * inner ℝ (u.1 - x0) d ≤ Uβ hatP F x0 β sα := hdata.2 u.1 u.2
        linarith
      change
        (((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
            α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) ≤
          (((Uβ hatP F x0 β sα - α * g : ℝ)) : WithTop ℝ)
      exact_mod_cast hupperReal
    exact hupper
  · -- The shifted affine slice at `uα` still attains the displayed shifted owner value.
    have hvalue :
        (((Uβ hatP F x0 β sα - α * g : ℝ)) : WithTop ℝ) = shiftedSlice α uα := by
      change
        (((Uβ hatP F x0 β sα - α * g : ℝ)) : WithTop ℝ) =
          (((inner ℝ (uStar sα - x0) t - β * (F (uStar sα) - F x0) +
              α * (inner ℝ (uStar sα - x0) d - g) : ℝ)) : WithTop ℝ)
      exact congrArg (fun r : ℝ ↦ ((r : ℝ) : WithTop ℝ)) <| by
        calc
          Uβ hatP F x0 β sα - α * g
              = (inner ℝ (uStar sα - x0) t - β * (F (uStar sα) - F x0) +
                  α * inner ℝ (uStar sα - x0) d) - α * g := by
                    rw [hdata.1]
          _ = inner ℝ (uStar sα - x0) t - β * (F (uStar sα) - F x0) +
                α * (inner ℝ (uStar sα - x0) d - g) := by ring
    calc
      pointwiseSupremumOn (Set.univ : Set hatP) shiftedSlice α
          ≥ shiftedSlice α uα :=
            ClosedConvexOn.slice_le_pointwiseSupremumOn (by simp)
      _ = (((Uβ hatP F x0 β sα - α * g : ℝ)) : WithTop ℝ) := hvalue.symm

/-- Helper for Proposition 7.28: as a function of the scalar line parameter, the shifted owner is
exactly the real-valued line slice tilted by the affine term `α * g`. -/
lemma shiftedLineSlice_owner_eq_affineTilt
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) (g : ℝ) :
    (fun α : ℝ ↦
      pointwiseSupremumOn (Set.univ : Set hatP)
        (fun τ u ↦
          ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
              τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α) =
      fun α : ℝ ↦
        (((Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) - α * g : ℝ)) :
          WithTop ℝ) := by
  funext α
  -- Normalize the shifted pointwise supremum once so later subgradient arguments use the same
  -- real-valued owner spelling.
  simpa using
    shiftedLineSliceLift_eq_pointwiseSupremumOnAffineSlices
      hatP F x0 β uStar huStar t d g α

/-- Helper for Proposition 7.28: the shifted lifted line slice is convex on all of `ℝ` because it
is the exact line slice minus the affine term `α ↦ α * g`. -/
lemma shiftedLineSliceLiftConvexOn
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) (g : ℝ) :
    ConvexOn ℝ
      (dom (fun α : ℝ ↦
        pointwiseSupremumOn (Set.univ : Set hatP)
          (fun τ u ↦
            ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α))
      (withTopRealPart (fun α : ℝ ↦
        pointwiseSupremumOn (Set.univ : Set hatP)
          (fun τ u ↦
            ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α)) := by
  let ψ : ℝ → ℝ := fun α ↦
    Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) - α * g
  have hψ :
      (fun α : ℝ ↦
        pointwiseSupremumOn (Set.univ : Set hatP)
          (fun τ u ↦
            ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α) =
        fun α : ℝ ↦ ((ψ α : ℝ) : WithTop ℝ) := by
    -- Normalize the shifted owner to the exact line slice with one affine tilt removed.
    simpa [ψ] using
      shiftedLineSlice_owner_eq_affineTilt
        hatP F x0 β uStar huStar t d g
  rw [hψ]
  have hdom :
      dom (fun α : ℝ ↦ ((ψ α : ℝ) : WithTop ℝ)) = (Set.univ : Set ℝ) := by
    -- The tilted real-valued owner stays finite at every scalar parameter.
    ext α
    change ((((ψ α : ℝ) : WithTop ℝ) < ⊤)) ↔ True
    constructor
    · intro _
      trivial
    · intro _
      exact WithTop.coe_lt_top _
  have hconvExact :
      ConvexOn ℝ Set.univ
        (fun α : ℝ ↦ Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d))) := by
    -- Reuse the already-packaged convexity of the unshifted scalar owner.
    simpa using
      supportFunctionApproximation_line_convexOn_univ_of_selector
        hatP F x0 β uStar huStar t d
  have hconvTilt : ConvexOn ℝ Set.univ ψ := by
    rw [ConvexOn]
    constructor
    · exact convex_univ
    · intro x hx y hy a b ha hb hab
      have hbase := hconvExact.2 hx hy ha hb hab
      -- Subtract the same affine term from both sides of the unshifted convexity inequality.
      dsimp [ψ] at hbase ⊢
      have hlin : (a * x + b * y) * g = a * (x * g) + b * (y * g) := by
        ring
      linarith
  rw [hdom]
  -- Once the effective domain is `Set.univ`, the lifted convexity is exactly the real convexity.
  simpa [withTopEffectiveDomain] using hconvTilt

/-- Helper for Proposition 7.28: the shifted lifted line slice is finite on all of `ℝ`, so `0`
lies in the interior of its effective domain. -/
lemma shiftedLineSlice_zero_mem_interior_dom
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) (g : ℝ) :
    (0 : ℝ) ∈
      interior
        (dom (fun α : ℝ ↦
          pointwiseSupremumOn (Set.univ : Set hatP)
            (fun τ u ↦
              ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                  τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α)) := by
  have hdom :
      dom (fun α : ℝ ↦
        pointwiseSupremumOn (Set.univ : Set hatP)
          (fun τ u ↦
            ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α) =
        (Set.univ : Set ℝ) := by
    -- Rewrite the shifted owner to the affine-tilted real-valued line slice, whose lifted domain
    -- is visibly all of `ℝ`.
    rw [shiftedLineSlice_owner_eq_affineTilt hatP F x0 β uStar huStar t d g]
    ext α
    change
      (((((Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) - α * g : ℝ)) :
        WithTop ℝ) < ⊤)) ↔ True
    constructor
    · intro _
      trivial
    · intro _
      exact WithTop.coe_lt_top _
  rw [hdom]
  simpa using (show (0 : ℝ) ∈ interior (Set.univ : Set ℝ) by simp)

/-- Helper for Proposition 7.28: subtracting the affine line `α ↦ α * g` shifts every scalar
subgradient of the exact line slice by the same amount. -/
lemma memSubdifferential_shiftedLineSlice_of_memSubdifferential
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) {h g : ℝ}
    (hh : h ∈
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0)) :
    h - g ∈
      ∂ (fun α : ℝ ↦
        pointwiseSupremumOn (Set.univ : Set hatP)
          (fun τ u ↦
            ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α)(0) := by
  let ψ : ℝ → ℝ := fun α ↦
    Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) - α * g
  have hψ :
      (fun α : ℝ ↦
        pointwiseSupremumOn (Set.univ : Set hatP)
          (fun τ u ↦
            ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α) =
        fun α : ℝ ↦ ((ψ α : ℝ) : WithTop ℝ) := by
    -- Keep the shifted owner in the same normalized affine-tilted spelling as above.
    simpa [ψ] using
      shiftedLineSlice_owner_eq_affineTilt
        hatP F x0 β uStar huStar t d g
  rw [hψ]
  rw [mem_subdifferential_coe_real_iff] at hh ⊢
  have hinner (x y : ℝ) : inner ℝ x y = x * y := by
    simpa using real_inner_eq_mul x y
  intro y
  have hsub :
      Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + y • d)) ≥
        Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + 0 • d)) + h * y := by
    simpa [hinner] using (hh y)
  have hshift :
      Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + y • d)) - y * g ≥
        Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + 0 • d)) - 0 * g + (h - g) * y := by
    linarith
  simpa [ψ, hinner] using hshift

/-- Helper for Proposition 7.28: subtracting the affine support line `α ↦ α * g` converts a
scalar subgradient `g ∈ ∂ φ(0)` of the exact line slice into `0 ∈ ∂ ψ_g(0)` for the shifted
affine-supremum owner. -/
lemma zeroMemSubdifferential_shiftedLineSlice_of_memSubdifferential
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) {g : ℝ}
    (hg : g ∈
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0)) :
    0 ∈
      ∂ (fun α : ℝ ↦
        pointwiseSupremumOn (Set.univ : Set hatP)
          (fun τ u ↦
            ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α)(0) := by
  -- Specialize the general affine-tilt transport to the exact scalar subgradient `h = g`.
  simpa using
    memSubdifferential_shiftedLineSlice_of_memSubdifferential
      hatP F x0 β uStar huStar t d (h := g) (g := g) hg

/-- Helper for Proposition 7.28: conversely, if the shifted affine-supremum owner has zero
subgradient at `0`, then the exact line slice has scalar subgradient `g` at the same base point. -/
lemma memSubdifferential_lineSlice_of_zeroMemSubdifferential_shiftedLineSlice
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) {g : ℝ}
    (hg0 :
      0 ∈
        ∂ (fun α : ℝ ↦
          pointwiseSupremumOn (Set.univ : Set hatP)
            (fun τ u ↦
              ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                  τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α)(0)) :
    g ∈
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) := by
  let ψ : ℝ → ℝ := fun α ↦
    Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) - α * g
  have hψ :
      (fun α : ℝ ↦
        pointwiseSupremumOn (Set.univ : Set hatP)
          (fun τ u ↦
            ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α) =
        fun α : ℝ ↦ ((ψ α : ℝ) : WithTop ℝ) := by
    -- Normalize the shifted supremum once so the converse subgradient statement is a direct
    -- rearrangement of the same affine tilt.
    simpa [ψ] using
      shiftedLineSlice_owner_eq_affineTilt
        hatP F x0 β uStar huStar t d g
  rw [hψ] at hg0
  rw [mem_subdifferential_coe_real_iff] at hg0 ⊢
  have hinner (x y : ℝ) : inner ℝ x y = x * y := by
    simpa using real_inner_eq_mul x y
  intro y
  have hmin :
      Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + y • d)) - y * g ≥
        Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + 0 • d)) - 0 * g := by
    -- A zero subgradient of the shifted owner is exactly the scalar minimum inequality at `0`.
    simpa [ψ, hinner] using (hg0 y)
  have hgoal :
      Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + y • d)) ≥
        Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + 0 • d)) + g * y := by
    -- Add back the affine tilt `y * g` to recover the exact line-slice support inequality.
    linarith
  simpa [hinner] using hgoal

/-- Helper for Proposition 7.28: the exact scalar line-slice subgradient `g ∈ ∂ φ(0)` is
equivalent to zero belonging to the shifted owner subdifferential `∂ ψ_g(0)`. -/
lemma memSubdifferential_lineSlice_iff_zeroMemSubdifferential_shiftedLineSlice
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) {g : ℝ} :
    g ∈
        ∂ (fun α : ℝ ↦
          (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) ↔
      0 ∈
        ∂ (fun α : ℝ ↦
          pointwiseSupremumOn (Set.univ : Set hatP)
            (fun τ u ↦
              ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                  τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α)(0) := by
  constructor
  · -- Removing the affine support line turns the exact scalar subgradient into the shifted
    -- zero-subgradient statement.
    intro hg
    exact
      zeroMemSubdifferential_shiftedLineSlice_of_memSubdifferential
        hatP F x0 β uStar huStar t d hg
  · -- Adding the same affine line back recovers the exact scalar subgradient.
    intro hg0
    exact
      memSubdifferential_lineSlice_of_zeroMemSubdifferential_shiftedLineSlice
        hatP F x0 β uStar huStar t d hg0

/-- Helper for Proposition 7.28: any active affine slice at `0` has singleton constrained
subdifferential `{inner ℝ (uStar ((toDual) t) - x0) d}` because zero-active uniqueness forces its
slope to match the selector slope. -/
lemma activeAffineSliceSubgradient_eq_selectorSlope_at_zero
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) {u : hatP} {g : ℝ}
    (huActive :
      u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP)
        (fun α u ↦
          ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
              α * inner ℝ (u.1 - x0) d : ℝ) : WithTop ℝ)) 0)
    (hg :
      g ∈ ∂[Set.univ]
        (fun α : ℝ ↦
          ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
              α * inner ℝ (u.1 - x0) d : ℝ) : WithTop ℝ))(0)) :
    g = inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d := by
  let a : E → ℝ := fun v ↦ inner ℝ (v - x0) t - β * (F v - F x0)
  let b : E → ℝ := fun v ↦ inner ℝ (v - x0) d
  let slice : ℝ → hatP → WithTop ℝ := fun α v ↦ ((a v.1 + α * b v.1 : ℝ) : WithTop ℝ)
  let b0 : ℝ := b (uStar ((InnerProductSpace.toDual ℝ E) t))
  have hlineEq :=
    lineSliceLift_eq_pointwiseSupremumOnAffineSlices
      hatP F x0 β uStar huStar t d
  have huValue :
      a u.1 = Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) t) := by
    rcases mem_activePointwiseSupremumOnIndices_iff.mp huActive with ⟨-, huActiveEq⟩
    have hsupAtZero :
        pointwiseSupremumOn (Set.univ : Set hatP) slice 0 =
          ((Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) t) : ℝ) : WithTop ℝ) := by
      simpa [slice, a, b, zero_smul] using congrArg (fun f : ℝ → WithTop ℝ ↦ f 0) hlineEq.symm
    apply WithTop.coe_injective
    calc
      (((a u.1 : ℝ)) : WithTop ℝ) = slice 0 u := by simp [slice]
      _ = pointwiseSupremumOn (Set.univ : Set hatP) slice 0 := huActiveEq
      _ = ((Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) t) : ℝ) : WithTop ℝ) := hsupAtZero
  have hzeroData :
      Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) t) =
        a (uStar ((InnerProductSpace.toDual ℝ E) t)) ∧
      (∀ v ∈ hatP, a v ≤ Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) t)) ∧
      ∀ v ∈ hatP,
        a v = Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) t) →
          b v = b (uStar ((InnerProductSpace.toDual ℝ E) t)) := by
    -- Specialize the zero-active slope data to the exact `a`/`b` normalization used here.
    simpa [a, b, zero_smul] using
      (lineSlice_zeroActiveSlopeData_of_unique_argmax
        hatP F x0 β uStar huStar huStar_unique t d)
  have huSlope :
      b u.1 = b (uStar ((InnerProductSpace.toDual ℝ E) t)) :=
    hzeroData.2.2 u.1 u.2 huValue
  have hdomSlice :
      dom (fun α : ℝ ↦ ((a u.1 + α * b u.1 : ℝ) : WithTop ℝ)) = Set.univ := by
    ext α
    change ((((a u.1 + α * b u.1 : ℝ) : WithTop ℝ) < ⊤) ↔ True)
    constructor
    · intro _
      trivial
    · intro _
      exact WithTop.coe_lt_top _
  have hg' :
      g ∈ ∂
        (fun α : ℝ ↦
          ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
              α * inner ℝ (u.1 - x0) d : ℝ) : WithTop ℝ))(0) := by
    rw [mem_constrainedSubdifferential_iff] at hg
    rw [mem_subdifferential_iff]
    constructor
    · simpa [a, b, hdomSlice] using hg.2.1
    · intro y hy
      exact hg.2.2 (by simp)
  have hgSingleton :
      g = b u.1 := by
    have hsingleton :=
      supportFunctionApproximation_affineScalarSlice_subdifferential_eq_singleton
        (a u.1) (b u.1)
    rw [hsingleton] at hg'
    exact Set.mem_singleton_iff.mp hg'
  -- The active-slice singleton theorem and zero-active uniqueness identify the slope with `b0`.
  calc
    g = b u.1 := hgSingleton
    _ = b (uStar ((InnerProductSpace.toDual ℝ E) t)) := huSlope
    _ = inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d := rfl

/-- Helper for Proposition 7.28: the convex hull of the constrained subgradients of the affine
slices active at `0` already collapses to the singleton selector slope. -/
lemma activeAffineHullAtZero_eq_singleton_selectorSlope
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) :
    convexHull ℝ
      {g | ∃ u : hatP,
          u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP)
            (fun α u ↦
              ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                  α * inner ℝ (u.1 - x0) d : ℝ) : WithTop ℝ)) 0 ∧
            g ∈ ∂[Set.univ]
              (fun α : ℝ ↦
                ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                    α * inner ℝ (u.1 - x0) d : ℝ) : WithTop ℝ))(0)} =
      {inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d} := by
  let s0 : StrongDual ℝ E := (InnerProductSpace.toDual ℝ E) t
  let a : E → ℝ := fun u ↦ inner ℝ (u - x0) t - β * (F u - F x0)
  let b : E → ℝ := fun u ↦ inner ℝ (u - x0) d
  let slice : ℝ → hatP → WithTop ℝ := fun α u ↦ ((a u.1 + α * b u.1 : ℝ) : WithTop ℝ)
  let b0 : ℝ := b (uStar s0)
  have hzero :
      Uβ hatP F x0 β s0 = a (uStar s0) ∧
        ∀ u ∈ hatP, a u ≤ Uβ hatP F x0 β s0 :=
    supportFunctionApproximation_line_affineSupremumData_zero
      hatP F x0 β uStar huStar t d
  have huStar_mem : uStar s0 ∈ hatP := by
    have huStar_s0 : uStar s0 ∈ Argmaxβ hatP F β s0 := huStar s0
    rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff] at huStar_s0
    exact huStar_s0.1
  let u0 : hatP := ⟨uStar s0, huStar_mem⟩
  have hsupAtZero :
      pointwiseSupremumOn (Set.univ : Set hatP) slice 0 =
        ((Uβ hatP F x0 β s0 : ℝ) : WithTop ℝ) := by
    -- Keep the affine-slice owner in its exact spelling at the base parameter.
    simpa [s0, a, slice] using
      (lineSliceAffineSupremumAtZero_eq_owner
        hatP F x0 β uStar huStar t d)
  have hu0Active :
      u0 ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP) slice 0 := by
    -- The selected zero-parameter affine slice attains the exact pointwise supremum at `0`.
    rw [mem_activePointwiseSupremumOnIndices_iff]
    refine ⟨by simp [u0], ?_⟩
    calc
      slice 0 u0 = (((a (uStar s0) : ℝ)) : WithTop ℝ) := by
        simp [slice, u0]
      _ = ((Uβ hatP F x0 β s0 : ℝ) : WithTop ℝ) := by
        exact congrArg (fun r : ℝ ↦ ((r : ℝ) : WithTop ℝ)) hzero.1.symm
      _ = pointwiseSupremumOn (Set.univ : Set hatP) slice 0 := hsupAtZero.symm
  have hb0Sub :
      b0 ∈ ∂[Set.univ] (fun α : ℝ ↦ slice α u0)(0) := by
    have hb0Sub_unconstrained :
        b0 ∈ ∂ (fun α : ℝ ↦ slice α u0)(0) := by
      -- The selected affine slice is linear in `α`, so its unconstrained subdifferential is `{b0}`.
      simpa [slice, u0, b0, s0, a, b] using
        (show
          b0 ∈
            ∂ (fun α : ℝ ↦
              ((a (uStar s0) + α * b (uStar s0) : ℝ) : WithTop ℝ))(0) from by
            rw [supportFunctionApproximation_affineScalarSlice_subdifferential_eq_singleton]
            exact Set.mem_singleton b0)
    have hsub := mem_subdifferential_iff.mp hb0Sub_unconstrained
    rw [mem_constrainedSubdifferential_iff]
    refine ⟨by simp, ?_, ?_⟩
    · change ((((slice 0 u0 : WithTop ℝ)) < ⊤))
      simpa [slice, u0]
    · intro y hy
      exact hsub.2 (by
        change ((slice y u0 : WithTop ℝ) < ⊤)
        exact WithTop.coe_lt_top _)
  have hgenerator :
      {g | ∃ u : hatP,
          u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP) slice 0 ∧
            g ∈ ∂[Set.univ] (fun α : ℝ ↦ slice α u)(0)} = {b0} := by
    ext g
    constructor
    · intro hg
      rcases hg with ⟨u, huActive, hgSub⟩
      exact Set.mem_singleton_iff.mpr
        (activeAffineSliceSubgradient_eq_selectorSlope_at_zero
          hatP F x0 β uStar huStar huStar_unique t d huActive hgSub)
    · intro hg
      rcases Set.mem_singleton_iff.mp hg with rfl
      exact ⟨u0, hu0Active, hb0Sub⟩
  -- Collapse the active generator set first, then evaluate the convex hull of a singleton.
  rw [hgenerator, convexHull_singleton]

/-- Helper for Proposition 7.28: the exact scalar line slice at the base parameter `0` should have
singleton subdifferential given by the selector slope. -/
lemma lineSliceSubgradient_eq_selectorSlope_at_zero_of_limits
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E)
    (hfuture :
      Tendsto
        (fun τ : ℝ ↦
          inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + τ • d)) - x0) d)
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)))
    (hpast :
      Tendsto
        (fun τ : ℝ ↦
          inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t - τ • d)) - x0) d)
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)))
    {g : ℝ}
    (hg : g ∈
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0)) :
    g = inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d := by
  have hupper :
      g ≤ inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d := by
    -- The forward selector slopes stay above `g`, so their limit bounds `g` from above.
    refine ge_of_tendsto hfuture ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact (selectorSlope_sandwich_of_mem_lineSubdifferential
      hatP F x0 β uStar huStar t d hg hτ).2
  have hlower :
      inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d ≤ g := by
    -- The backward selector slopes stay below `g`, so their limit bounds `g` from below.
    refine le_of_tendsto hpast ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact (selectorSlope_sandwich_of_mem_lineSubdifferential
      hatP F x0 β uStar huStar t d hg hτ).1
  -- The one-sided limit squeeze identifies the scalar subgradient with the base selector slope.
  exact le_antisymm hupper hlower

/-- Helper for Proposition 7.28: once the directional derivatives of a scalar convex line slice at
`0` in directions `1` and `-1` are `b0` and `-b0`, every scalar subgradient at `0` must equal
`b0`. -/
lemma subgradient_eq_of_directionalDerivativeSigns_at_zero
    {φLift : ℝ → WithTop ℝ} {b0 g : ℝ}
    (hconv : ConvexOn ℝ (dom φLift) (withTopRealPart φLift))
    (h0 : (0 : ℝ) ∈ interior (dom φLift))
    (hg : g ∈ ∂ φLift(0))
    (hplus : convexDirectionalDerivativeReal φLift h0 (1 : ℝ) = b0)
    (hminus : convexDirectionalDerivativeReal φLift h0 (-1 : ℝ) = -b0) :
    g = b0 := by
  have hinner (x y : ℝ) : inner ℝ x y = x * y := by
    simpa using real_inner_eq_mul x y
  have hgreatestPlus :=
    convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior hconv h0 (1 : ℝ)
  have hgreatestMinus :=
    convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior hconv h0 (-1 : ℝ)
  rw [convexDirectionalDerivativeReal_apply] at hgreatestPlus hgreatestMinus
  have hgplus :
      g ∈ (fun z : ℝ ↦ inner ℝ z (1 : ℝ)) '' ∂ φLift(0) := by
    -- Package the candidate subgradient as a point in the Chapter 3 pairing image at `p = 1`.
    exact ⟨g, hg, by simpa [hinner]⟩
  have hgminus :
      -g ∈ (fun z : ℝ ↦ inner ℝ z (-1 : ℝ)) '' ∂ φLift(0) := by
    -- Do the same in direction `-1`, where the pairing is just negation on `ℝ`.
    refine ⟨g, hg, ?_⟩
    simpa [hinner]
  have hupper : g ≤ b0 := by
    -- The `p = 1` directional derivative is the greatest subgradient pairing in that direction.
    have hle : g ≤ convexDirectionalDerivativeReal φLift h0 (1 : ℝ) := by
      simpa using hgreatestPlus.2 hgplus
    linarith [hle, hplus]
  have hlower : b0 ≤ g := by
    -- The `p = -1` directional derivative gives the complementary lower bound on `g`.
    have hle : -g ≤ convexDirectionalDerivativeReal φLift h0 (-1 : ℝ) := by
      simpa using hgreatestMinus.2 hgminus
    linarith [hle, hminus]
  -- The two sign directions squeeze the scalar subgradient to the unique selector slope.
  exact le_antisymm hupper hlower

/-- Helper for Proposition 7.28: if the lifted scalar line slice already has singleton
subdifferential `{b0}` at `0`, then the directional derivatives in directions `1` and `-1`
match the corresponding singleton pairings, hence are bounded above by `b0` and `-b0`. -/
lemma directionalDerivativeSigns_le_of_subdifferential_eq_singleton
    {φLift : ℝ → WithTop ℝ} {b0 : ℝ}
    (hconv : ConvexOn ℝ (dom φLift) (withTopRealPart φLift))
    (h0 : (0 : ℝ) ∈ interior (dom φLift))
    (hsub : ∂ φLift(0) = {b0}) :
    convexDirectionalDerivativeReal φLift h0 (1 : ℝ) ≤ b0 ∧
      convexDirectionalDerivativeReal φLift h0 (-1 : ℝ) ≤ -b0 := by
  have hinner (x y : ℝ) : inner ℝ x y = x * y := by
    simpa using real_inner_eq_mul x y
  have hgreatestPlus :=
    convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior
      hconv h0 (1 : ℝ)
  have hgreatestMinus :=
    convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior
      hconv h0 (-1 : ℝ)
  rw [convexDirectionalDerivativeReal_apply] at hgreatestPlus hgreatestMinus
  have hplusEq : convexDirectionalDerivativeReal φLift h0 (1 : ℝ) = b0 := by
    have hmem :
        convexDirectionalDerivativeReal φLift h0 (1 : ℝ) ∈
          (fun z : ℝ ↦ inner ℝ z (1 : ℝ)) '' ({b0} : Set ℝ) := by
      rw [hsub] at hgreatestPlus
      exact hgreatestPlus.1
    rcases hmem with ⟨z, rfl, hzEq⟩
    -- On `ℝ`, pairing with `1` leaves the singleton slope unchanged.
    simpa [hinner] using hzEq.symm
  have hminusEq : convexDirectionalDerivativeReal φLift h0 (-1 : ℝ) = -b0 := by
    have hmem :
        convexDirectionalDerivativeReal φLift h0 (-1 : ℝ) ∈
          (fun z : ℝ ↦ inner ℝ z (-1 : ℝ)) '' ({b0} : Set ℝ) := by
      rw [hsub] at hgreatestMinus
      exact hgreatestMinus.1
    rcases hmem with ⟨z, rfl, hzEq⟩
    -- Pairing the singleton slope with `-1` flips the sign.
    simpa [hinner] using hzEq.symm
  -- Read the exact sign identities back as the weaker upper bounds needed downstream.
  simpa using ⟨le_of_eq hplusEq, le_of_eq hminusEq⟩

/-- Helper for Proposition 7.28: the future selector slopes along the exact line converge to the
positive directional derivative of the lifted line slice at `0`. -/
lemma lineSliceFutureSelectorSlope_tendsto_rightDirectionalDerivative
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) :
    let φLift : ℝ → WithTop ℝ := fun α ↦
      (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ)
    let h0 : (0 : ℝ) ∈ interior (dom φLift) :=
      supportFunctionApproximation_line_zero_mem_interior_dom hatP F x0 β t d
    Tendsto
      (fun τ : ℝ ↦
        inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + τ • d)) - x0) d)
      (𝓝[>] (0 : ℝ))
      (𝓝 (convexDirectionalDerivativeReal φLift h0 (1 : ℝ))) := by
  dsimp
  let φ : ℝ → ℝ := fun α ↦
    Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d))
  let futureSlope : ℝ → ℝ := fun τ ↦
    inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + τ • d)) - x0) d
  let rightSecant : ℝ → ℝ := fun τ ↦ (φ τ - φ 0) / τ
  have hconv :
      ConvexOn ℝ
        (dom (fun α : ℝ ↦ ((φ α : ℝ) : WithTop ℝ)))
        (withTopRealPart (fun α : ℝ ↦ ((φ α : ℝ) : WithTop ℝ))) := by
    -- Keep the exact lifted line-slice owner while invoking the Chapter 3 secant-limit theorem.
    simpa [φ] using lineSliceLiftConvexOn hatP F x0 β uStar huStar t d
  have h0 :
      (0 : ℝ) ∈
        interior (dom (fun α : ℝ ↦ ((φ α : ℝ) : WithTop ℝ))) := by
    -- The lifted line slice is finite on all of `ℝ`, so `0` is an interior point.
    simpa [φ] using
      supportFunctionApproximation_line_zero_mem_interior_dom hatP F x0 β t d
  have hrightSecant :
      Tendsto rightSecant (𝓝[>] (0 : ℝ))
        (𝓝
          (convexDirectionalDerivativeReal
            (fun α : ℝ ↦ ((φ α : ℝ) : WithTop ℝ))
            h0
            (1 : ℝ))) := by
    have hsecant :=
      tendsto_directionalSecantQuotient_of_mem_interior hconv h0 (1 : ℝ)
    rw [convexDirectionalDerivativeReal_apply] at hsecant
    -- Rewrite the canonical secant quotient to the explicit owner spelling `rightSecant`.
    simpa [rightSecant, φ, slope_fun_def_field] using hsecant
  have htwo :
      Tendsto (fun τ : ℝ ↦ (2 : ℝ) * τ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    -- Positive rescaling preserves the right-neighborhood filter at `0`.
    have htwo' :
        Tendsto (fun τ : ℝ ↦ (2 : ℝ) * τ) (𝓝[>] (0 : ℝ))
          (𝓝[>] ((2 : ℝ) * 0)) := by
      exact
        Filter.TendstoNhdsWithinIoi.const_mul
          (b := (2 : ℝ)) (c := (0 : ℝ)) (f := fun τ : ℝ ↦ τ)
          (by norm_num)
          (tendsto_id : Tendsto (fun τ : ℝ ↦ τ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)))
    simpa using htwo'
  have hrightSecantTwo :
      Tendsto (fun τ : ℝ ↦ rightSecant ((2 : ℝ) * τ)) (𝓝[>] (0 : ℝ))
        (𝓝
          (convexDirectionalDerivativeReal
            (fun α : ℝ ↦ ((φ α : ℝ) : WithTop ℝ))
            h0
            (1 : ℝ))) := by
    -- Reindex the same secant family by `τ ↦ 2τ`.
    exact hrightSecant.comp htwo
  have hfutureUpper :
      Tendsto (fun τ : ℝ ↦ 2 * rightSecant (2 * τ) - rightSecant τ) (𝓝[>] (0 : ℝ))
        (𝓝
          (convexDirectionalDerivativeReal
            (fun α : ℝ ↦ ((φ α : ℝ) : WithTop ℝ))
            h0
            (1 : ℝ))) := by
    -- Adjacent right secants share the same limit, so this affine combination does too.
    have htwoConst : Tendsto (fun _ : ℝ ↦ (2 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (2 : ℝ)) :=
      tendsto_const_nhds
    convert (htwoConst.mul hrightSecantTwo).sub hrightSecant using 2 <;> ring
  have hfutureLowerBound :
      ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ), rightSecant τ ≤ futureSlope τ := by
    -- The forward secant over `[0, τ]` is bounded above by the selector slope at its endpoint.
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hsecant :=
      (supportFunctionApproximation_line_secantQuotient_bounds_of_unique_argmax
        hatP F x0 β uStar huStar t d (α := 0) (β' := τ) hτ).2
    simpa [futureSlope, rightSecant, φ, zero_smul, sub_eq_add_neg] using hsecant
  have hfutureUpperBound :
      ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
        futureSlope τ ≤ 2 * rightSecant (2 * τ) - rightSecant τ := by
    -- Compare the selector slope at `τ` with the secant over `[τ, 2τ]`, then rewrite that
    -- secant through the two base-point secants.
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτpos : 0 < τ := hτ
    have hsecantRaw :=
      (supportFunctionApproximation_line_secantQuotient_bounds_of_unique_argmax
        hatP F x0 β uStar huStar t d (α := τ) (β' := 2 * τ) (by linarith [hτpos])).1
    have hsecant :
        futureSlope τ ≤ (φ (2 * τ) - φ τ) / τ := by
      simpa [futureSlope, φ, two_smul, show 2 * τ - τ = τ by ring] using hsecantRaw
    have hrepack :
        (φ (2 * τ) - φ τ) / τ = 2 * rightSecant (2 * τ) - rightSecant τ := by
      dsimp [rightSecant]
      field_simp [hτpos.ne']
      ring
    simpa [hrepack] using hsecant
  -- Squeeze the future selector slopes between the right secants and their adjacent refinement.
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hrightSecant hfutureUpper hfutureLowerBound hfutureUpperBound

/-- Helper for Proposition 7.28: the negated past selector slopes along the exact line converge
to the negative-direction directional derivative of the lifted line slice at `0`. -/
lemma lineSliceNegPastSelectorSlope_tendsto_leftDirectionalDerivative
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) :
    let φLift : ℝ → WithTop ℝ := fun α ↦
      (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ)
    let h0 : (0 : ℝ) ∈ interior (dom φLift) :=
      supportFunctionApproximation_line_zero_mem_interior_dom hatP F x0 β t d
    Tendsto
      (fun τ : ℝ ↦
        -inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t - τ • d)) - x0) d)
      (𝓝[>] (0 : ℝ))
      (𝓝 (convexDirectionalDerivativeReal φLift h0 (-1 : ℝ))) := by
  dsimp
  let φ : ℝ → ℝ := fun α ↦
    Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d))
  let negPastSlope : ℝ → ℝ := fun τ ↦
    -inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t - τ • d)) - x0) d
  let leftSecant : ℝ → ℝ := fun τ ↦ (φ (-τ) - φ 0) / τ
  have hconv :
      ConvexOn ℝ
        (dom (fun α : ℝ ↦ ((φ α : ℝ) : WithTop ℝ)))
        (withTopRealPart (fun α : ℝ ↦ ((φ α : ℝ) : WithTop ℝ))) := by
    -- Keep the exact lifted line-slice owner while invoking the Chapter 3 secant-limit theorem.
    simpa [φ] using lineSliceLiftConvexOn hatP F x0 β uStar huStar t d
  have h0 :
      (0 : ℝ) ∈
        interior (dom (fun α : ℝ ↦ ((φ α : ℝ) : WithTop ℝ))) := by
    -- The lifted line slice is finite on all of `ℝ`, so `0` is an interior point.
    simpa [φ] using
      supportFunctionApproximation_line_zero_mem_interior_dom hatP F x0 β t d
  have hleftSecant :
      Tendsto leftSecant (𝓝[>] (0 : ℝ))
        (𝓝
          (convexDirectionalDerivativeReal
            (fun α : ℝ ↦ ((φ α : ℝ) : WithTop ℝ))
            h0
            (-1 : ℝ))) := by
    have hsecant :=
      tendsto_directionalSecantQuotient_of_mem_interior hconv h0 (-1 : ℝ)
    rw [convexDirectionalDerivativeReal_apply] at hsecant
    -- Normalize the direction `-1` secant by rewriting `0 + α • (-1)` as `-α`.
    simpa [leftSecant, smul_eq_mul, slope_fun_def_field] using hsecant
  have htwo :
      Tendsto (fun τ : ℝ ↦ (2 : ℝ) * τ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    -- Positive rescaling preserves the right-neighborhood filter at `0`.
    have htwo' :
        Tendsto (fun τ : ℝ ↦ (2 : ℝ) * τ) (𝓝[>] (0 : ℝ))
          (𝓝[>] ((2 : ℝ) * 0)) := by
      exact
        Filter.TendstoNhdsWithinIoi.const_mul
          (b := (2 : ℝ)) (c := (0 : ℝ)) (f := fun τ : ℝ ↦ τ)
          (by norm_num)
          (tendsto_id : Tendsto (fun τ : ℝ ↦ τ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)))
    simpa using htwo'
  have hleftSecantTwo :
      Tendsto (fun τ : ℝ ↦ leftSecant ((2 : ℝ) * τ)) (𝓝[>] (0 : ℝ))
        (𝓝
          (convexDirectionalDerivativeReal
            (fun α : ℝ ↦ ((φ α : ℝ) : WithTop ℝ))
            h0
            (-1 : ℝ))) := by
    -- Reindex the same left secant family by `τ ↦ 2τ`.
    exact hleftSecant.comp htwo
  have hnegPastUpper :
      Tendsto (fun τ : ℝ ↦ 2 * leftSecant (2 * τ) - leftSecant τ) (𝓝[>] (0 : ℝ))
        (𝓝
          (convexDirectionalDerivativeReal
            (fun α : ℝ ↦ ((φ α : ℝ) : WithTop ℝ))
            h0
            (-1 : ℝ))) := by
    -- Adjacent left secants share the same limit, so this affine combination does too.
    have htwoConst : Tendsto (fun _ : ℝ ↦ (2 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (2 : ℝ)) :=
      tendsto_const_nhds
    convert (htwoConst.mul hleftSecantTwo).sub hleftSecant using 2 <;> ring
  have hnegPastLowerBound :
      ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ), leftSecant τ ≤ negPastSlope τ := by
    -- The backward secant over `[-τ, 0]` dominates the negated selector slope at `-τ`.
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτne : τ ≠ 0 := ne_of_gt hτ
    have hsecant :=
      (supportFunctionApproximation_line_secantQuotient_bounds_of_unique_argmax
        hatP F x0 β uStar huStar t d (α := -τ) (β' := 0) (by linarith [show 0 < τ from hτ])).1
    have hsecant' :
        inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t - τ • d)) - x0) d ≤
          (φ 0 - φ (-τ)) / τ := by
      simpa [φ, zero_smul, sub_eq_add_neg] using hsecant
    have hbound : leftSecant τ ≤ negPastSlope τ := by
      have hrepack : leftSecant τ = -((φ 0 - φ (-τ)) / τ) := by
        dsimp [leftSecant]
        field_simp [hτne]
        ring
      rw [hrepack]
      dsimp [negPastSlope]
      linarith
    simpa using hbound
  have hnegPastUpperBound :
      ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
        negPastSlope τ ≤ 2 * leftSecant (2 * τ) - leftSecant τ := by
    -- Compare the selector slope at `-τ` with the secant over `[-2τ, -τ]`, then rewrite that
    -- secant through the two base-point left secants.
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτpos : 0 < τ := hτ
    have hsecantRaw :=
      (supportFunctionApproximation_line_secantQuotient_bounds_of_unique_argmax
        hatP F x0 β uStar huStar t d
        (α := -(2 * τ)) (β' := -τ) (by linarith [hτpos])).2
    have hsecant :
        negPastSlope τ ≤ (2 * leftSecant (2 * τ) - leftSecant τ) := by
      have hsecant' :
          (φ (-τ) - φ (-(2 * τ))) / τ ≤
            inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t - τ • d)) - x0) d := by
        simpa [φ, sub_eq_add_neg, two_smul,
          show -τ - -(2 * τ) = τ by ring,
          show -τ + 2 * τ = τ by ring] using hsecantRaw
      have hrepack :
          2 * leftSecant (2 * τ) - leftSecant τ =
            -((φ (-τ) - φ (-(2 * τ))) / τ) := by
        dsimp [leftSecant]
        field_simp [hτpos.ne']
        ring
      rw [hrepack]
      linarith [hsecant']
    simpa using hsecant
  -- Squeeze the negated past selector slopes between the left secants and their adjacent
  -- refinement.
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hleftSecant hnegPastUpper hnegPastLowerBound hnegPastUpperBound

/-- Helper for Proposition 7.28: the exact lifted line slice should have directional derivatives
at `0` in directions `1` and `-1` bounded above by the selector slope and its negative. -/
lemma shiftedActiveAffineSliceSubgradient_eq_shiftedSelectorSlope_at_zero
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) {u : hatP} {g h : ℝ}
    (huActive :
      u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP)
        (fun α u ↦
          ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
              α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) 0)
    (hh :
      h ∈ ∂[Set.univ]
        (fun α : ℝ ↦
          ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
              α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ))(0)) :
    h = inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d - g := by
  let a : E → ℝ := fun v ↦ inner ℝ (v - x0) t - β * (F v - F x0)
  let b : E → ℝ := fun v ↦ inner ℝ (v - x0) d
  let slice : ℝ → hatP → WithTop ℝ := fun α v ↦ ((a v.1 + α * b v.1 : ℝ) : WithTop ℝ)
  let shiftedSlice : ℝ → hatP → WithTop ℝ :=
    fun α v ↦ ((a v.1 + α * (b v.1 - g) : ℝ) : WithTop ℝ)
  have huActive_unshifted :
      u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP) slice 0 := by
    -- At `α = 0`, the shifted and unshifted affine slices have the same value and active set.
    rw [mem_activePointwiseSupremumOnIndices_iff] at huActive ⊢
    rcases huActive with ⟨hu_mem, hu_eq⟩
    refine ⟨hu_mem, ?_⟩
    simpa [slice, shiftedSlice]
      using hu_eq
  have hu_eq_star :
      u.1 = uStar ((InnerProductSpace.toDual ℝ E) t) := by
    -- The zero-parameter active slice is still the unique base selector.
    simpa [a, b, slice] using
      lineSliceActiveAffineIndex_eq_selector_at_zero
        hatP F x0 β uStar huStar huStar_unique t d huActive_unshifted
  have hh_unconstrained :
      h ∈ ∂ (fun α : ℝ ↦ shiftedSlice α u)(0) := by
    -- The ambient domain is all of `ℝ`, so the constrained and unconstrained scalar notions agree.
    rw [mem_constrainedSubdifferential_iff] at hh
    rw [mem_subdifferential_iff]
    constructor
    · simpa [shiftedSlice] using hh.2.1
    · intro y hy
      exact hh.2.2 (by simp)
  have hh_eq :
      h = b u.1 - g := by
    -- Each shifted affine slice has singleton unconstrained subdifferential at its displayed slope.
    rw [supportFunctionApproximation_affineScalarSlice_subdifferential_eq_singleton] at hh_unconstrained
    exact Set.mem_singleton_iff.mp hh_unconstrained
  -- Replace the active index by the selector and read off the shifted slope.
  calc
    h = b u.1 - g := hh_eq
    _ = inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d - g := by
      simpa [b, hu_eq_star]

/-- Helper for Proposition 7.28: the convex hull of the shifted affine-slice subgradients active
at `0` already collapses to the singleton shifted selector slope `{b0 - g}`. -/
lemma shiftedActiveAffineHullAtZero_eq_singleton_shiftedSelectorSlope
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) (g : ℝ) :
    convexHull ℝ
      {h | ∃ u : hatP,
          u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP)
            (fun α u ↦
              ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                  α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) 0 ∧
            h ∈ ∂[Set.univ]
              (fun α : ℝ ↦
                ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                    α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ))(0)} =
      {inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d - g} := by
  let s0 : StrongDual ℝ E := (InnerProductSpace.toDual ℝ E) t
  let a : E → ℝ := fun u ↦ inner ℝ (u - x0) t - β * (F u - F x0)
  let b : E → ℝ := fun u ↦ inner ℝ (u - x0) d
  let shiftedSlice : ℝ → hatP → WithTop ℝ :=
    fun α u ↦ ((a u.1 + α * (b u.1 - g) : ℝ) : WithTop ℝ)
  let b0 : ℝ := b (uStar s0)
  have hzero :
      Uβ hatP F x0 β s0 = a (uStar s0) ∧
        ∀ u ∈ hatP, a u ≤ Uβ hatP F x0 β s0 :=
    supportFunctionApproximation_line_affineSupremumData_zero
      hatP F x0 β uStar huStar t d
  have huStar_mem : uStar s0 ∈ hatP := by
    have huStar_s0 : uStar s0 ∈ Argmaxβ hatP F β s0 := huStar s0
    rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff] at huStar_s0
    exact huStar_s0.1
  let u0 : hatP := ⟨uStar s0, huStar_mem⟩
  have hsupAtZero :
      pointwiseSupremumOn (Set.univ : Set hatP) shiftedSlice 0 =
        ((Uβ hatP F x0 β s0 : ℝ) : WithTop ℝ) := by
    -- Keep the shifted owner in its exact spelling at `α = 0`.
    simpa [s0, a, b, shiftedSlice] using
      (shiftedLineSliceLift_eq_pointwiseSupremumOnAffineSlices
        hatP F x0 β uStar huStar t d g 0)
  have hu0Active :
      u0 ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP) shiftedSlice 0 := by
    -- The selected base slice still attains the shifted owner at the zero parameter.
    rw [mem_activePointwiseSupremumOnIndices_iff]
    refine ⟨by simp [u0], ?_⟩
    calc
      shiftedSlice 0 u0 = (((a (uStar s0) : ℝ)) : WithTop ℝ) := by
        simp [shiftedSlice, u0]
      _ = ((Uβ hatP F x0 β s0 : ℝ) : WithTop ℝ) := by
        exact congrArg (fun r : ℝ ↦ ((r : ℝ) : WithTop ℝ)) hzero.1.symm
      _ = pointwiseSupremumOn (Set.univ : Set hatP) shiftedSlice 0 := hsupAtZero.symm
  have hb0Sub :
      b0 - g ∈ ∂[Set.univ] (fun α : ℝ ↦ shiftedSlice α u0)(0) := by
    have hb0Sub_unconstrained :
        b0 - g ∈ ∂ (fun α : ℝ ↦ shiftedSlice α u0)(0) := by
      -- The selected shifted affine slice has unconstrained subdifferential `{b0 - g}`.
      simpa [shiftedSlice, u0, b0, s0, a, b] using
        (show
          b0 - g ∈
            ∂ (fun α : ℝ ↦
              ((a (uStar s0) + α * (b (uStar s0) - g) : ℝ) : WithTop ℝ))(0) from by
            rw [supportFunctionApproximation_affineScalarSlice_subdifferential_eq_singleton]
            exact Set.mem_singleton (b0 - g))
    have hsub := mem_subdifferential_iff.mp hb0Sub_unconstrained
    rw [mem_constrainedSubdifferential_iff]
    refine ⟨by simp, ?_, ?_⟩
    · change ((shiftedSlice 0 u0 : WithTop ℝ) < ⊤)
      simpa [shiftedSlice, u0]
    · intro y hy
      exact hsub.2 (by
        change ((shiftedSlice y u0 : WithTop ℝ) < ⊤)
        exact WithTop.coe_lt_top _)
  have hgenerator :
      {h | ∃ u : hatP,
          u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP) shiftedSlice 0 ∧
            h ∈ ∂[Set.univ] (fun α : ℝ ↦ shiftedSlice α u)(0)} = {b0 - g} := by
    ext h
    constructor
    · intro hh
      rcases hh with ⟨u, huActive, hhSub⟩
      exact Set.mem_singleton_iff.mpr
        (shiftedActiveAffineSliceSubgradient_eq_shiftedSelectorSlope_at_zero
          hatP F x0 β uStar huStar huStar_unique t d huActive hhSub)
    · intro hh
      rcases Set.mem_singleton_iff.mp hh with rfl
      exact ⟨u0, hu0Active, hb0Sub⟩
  -- Collapse the shifted active generator first, then evaluate the convex hull of a singleton.
  rw [hgenerator, convexHull_singleton]

/-- Helper for Proposition 7.28: if the shifted owner has zero subgradient at `0`, then every
nearby exact selector pairing already straddles the shifted slope `g`. -/
lemma shiftedLineSlice_selectorSlope_sandwich_of_zero_memSubdifferential
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) {g : ℝ}
    (hg0 :
      0 ∈
        ∂ (fun α : ℝ ↦
          pointwiseSupremumOn (Set.univ : Set hatP)
            (fun τ u ↦
              ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                  τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α)(0))
    {α : ℝ} (hα : 0 < α) :
    inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t - α • d)) - x0) d ≤ g ∧
      g ≤ inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + α • d)) - x0) d := by
  have hg :
      g ∈
        ∂ (fun α : ℝ ↦
          (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) := by
    -- Route correction: first move the shifted zero-subgradient back to the exact line slice,
    -- then reuse the already-proved exact sandwich theorem.
    exact
      memSubdifferential_lineSlice_of_zeroMemSubdifferential_shiftedLineSlice
        hatP F x0 β uStar huStar t d hg0
  -- The shifted sandwich is exactly the exact line-slice sandwich after undoing the affine tilt.
  exact
    selectorSlope_sandwich_of_mem_lineSubdifferential
      hatP F x0 β uStar huStar t d hg hα

/-- Helper for Proposition 7.28: after rewriting the shifted supremum to the affine-tilted exact
line slice, a zero scalar subgradient at `0` is exactly the statement that `0` globally minimizes
that shifted real-valued owner. -/
lemma shiftedLineSlice_isMinOn_zero_of_zeroMemSubdifferential
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) {g : ℝ}
    (hg0 :
      0 ∈
        ∂ (fun α : ℝ ↦
          pointwiseSupremumOn (Set.univ : Set hatP)
            (fun τ u ↦
              ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                  τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α)(0)) :
    IsMinOn
      (fun α : ℝ ↦
        Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) - α * g)
      Set.univ
      0 := by
  let ψ : ℝ → ℝ := fun α ↦
    Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) - α * g
  have hψ :
      (fun α : ℝ ↦
        pointwiseSupremumOn (Set.univ : Set hatP)
          (fun τ u ↦
            ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α) =
        fun α : ℝ ↦ ((ψ α : ℝ) : WithTop ℝ) := by
    -- Normalize the shifted owner once so the zero-subgradient condition becomes the ordinary
    -- scalar support inequality for the real-valued owner `ψ`.
    simpa [ψ] using
      shiftedLineSlice_owner_eq_affineTilt
        hatP F x0 β uStar huStar t d g
  rw [hψ] at hg0
  rw [mem_subdifferential_coe_real_iff] at hg0
  rw [isMinOn_univ_iff]
  intro y
  have hinner (x y : ℝ) : inner ℝ x y = x * y := by
    simpa using real_inner_eq_mul x y
  -- With subgradient `0`, the support inequality says exactly `ψ 0 ≤ ψ y` for every `y`.
  simpa [ψ, hinner] using hg0 y

/-- Helper for Proposition 7.28: the base active affine slice already contributes the shifted
selector slope `b0 - g` to the subdifferential of the shifted owner at `0`. -/
lemma shiftedLineSlice_selectorSlope_memSubdifferential_at_zero
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) (g : ℝ) :
    inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d - g ∈
      ∂ (fun α : ℝ ↦
        pointwiseSupremumOn (Set.univ : Set hatP)
          (fun τ u ↦
            ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α)(0) := by
  have hb0 :
      inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d ∈
        ∂ (fun α : ℝ ↦
          (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) := by
    -- Start from the exact owner: the base selector slope is already a scalar subgradient there.
    exact lineSliceLiftSelectorMemSubdifferential hatP F x0 β uStar huStar t d
  -- Subtracting the affine tilt `α ↦ α * g` transports that exact subgradient to the shifted
  -- owner with slope `b0 - g`.
  exact
    memSubdifferential_shiftedLineSlice_of_memSubdifferential
      hatP F x0 β uStar huStar t d (h := inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)
      (g := g) hb0

/-- Helper for Proposition 7.28: adding back the affine tilt `α ↦ α * g` transports an
arbitrary shifted scalar subgradient `h ∈ ∂ ψ_g(0)` to the exact line-slice subgradient
`h + g ∈ ∂ φ(0)`. -/
lemma memSubdifferential_lineSlice_of_memSubdifferential_shiftedLineSlice
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) {h g : ℝ}
    (hh :
      h ∈
        ∂ (fun α : ℝ ↦
          pointwiseSupremumOn (Set.univ : Set hatP)
            (fun τ u ↦
              ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                  τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α)(0)) :
    h + g ∈
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) := by
  let ψ : ℝ → ℝ := fun α ↦
    Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) - α * g
  have hψ :
      (fun α : ℝ ↦
        pointwiseSupremumOn (Set.univ : Set hatP)
          (fun τ u ↦
            ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α) =
        fun α : ℝ ↦ ((ψ α : ℝ) : WithTop ℝ) := by
    -- Normalize the shifted owner to the affine-tilted exact line slice before rearranging the
    -- support inequality.
    simpa [ψ] using
      shiftedLineSlice_owner_eq_affineTilt
        hatP F x0 β uStar huStar t d g
  rw [hψ] at hh
  rw [mem_subdifferential_coe_real_iff] at hh ⊢
  have hinner (x y : ℝ) : inner ℝ x y = x * y := by
    simpa using real_inner_eq_mul x y
  intro y
  have hsub :
      Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + y • d)) - y * g ≥
        Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + 0 • d)) - 0 * g + h * y := by
    simpa [ψ, hinner] using (hh y)
  have hgoal :
      Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + y • d)) ≥
        Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + 0 • d)) + (h + g) * y := by
    -- Add back the common affine term `y * g` to recover the exact line-slice support
    -- inequality with the transported slope `h + g`.
    linarith
  simpa [hinner] using hgoal

/-- Helper for Proposition 7.28: monotonicity of the exact selector pairings forces the right and
left directional derivatives of the lifted line slice at `0` to dominate the base selector slope
`b0` and its negative. -/
lemma lineSliceDirectionalDerivativeAtZero_lowerBounds_exact
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) :
    let φLift : ℝ → WithTop ℝ := fun α ↦
      (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ)
    let b0 : ℝ := inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d
    let h0 : (0 : ℝ) ∈ interior (dom φLift) :=
      supportFunctionApproximation_line_zero_mem_interior_dom hatP F x0 β t d
    b0 ≤ convexDirectionalDerivativeReal φLift h0 (1 : ℝ) ∧
      -b0 ≤ convexDirectionalDerivativeReal φLift h0 (-1 : ℝ) := by
  let φLift : ℝ → WithTop ℝ := fun α ↦
    (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ)
  let b0 : ℝ := inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d
  let futureSlope : ℝ → ℝ := fun τ ↦
    inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + τ • d)) - x0) d
  let pastSlope : ℝ → ℝ := fun τ ↦
    inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t - τ • d)) - x0) d
  let h0 : (0 : ℝ) ∈ interior (dom φLift) :=
    supportFunctionApproximation_line_zero_mem_interior_dom hatP F x0 β t d
  have hfutureDir :
      Tendsto futureSlope (𝓝[>] (0 : ℝ))
        (𝓝 (convexDirectionalDerivativeReal φLift h0 (1 : ℝ))) := by
    -- The exact future selector slopes converge to the positive directional derivative at `0`.
    simpa [futureSlope, φLift] using
      lineSliceFutureSelectorSlope_tendsto_rightDirectionalDerivative
        hatP F x0 β uStar huStar t d
  have hnegPastDir :
      Tendsto (fun τ : ℝ ↦ -pastSlope τ) (𝓝[>] (0 : ℝ))
        (𝓝 (convexDirectionalDerivativeReal φLift h0 (-1 : ℝ))) := by
    -- The negated past selector slopes converge to the negative-direction derivative at `0`.
    simpa [pastSlope, φLift] using
      lineSliceNegPastSelectorSlope_tendsto_leftDirectionalDerivative
        hatP F x0 β uStar huStar t d
  constructor
  · -- Monotonicity keeps every future selector slope above the base slope `b0`.
    refine ge_of_tendsto hfutureDir ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    simpa [futureSlope, b0, zero_smul] using
      supportFunctionApproximation_line_selectorPairing_mono_of_unique_argmax
        hatP F x0 β uStar huStar t d (α := 0) (β' := τ) hτ.le
  · -- The same monotonicity says every past selector slope stays below `b0`.
    refine ge_of_tendsto hnegPastDir ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hmono :
        -b0 ≤ -pastSlope τ := by
      have hτpos : 0 < τ := hτ
      simpa [pastSlope, b0, zero_smul, sub_eq_add_neg] using
        supportFunctionApproximation_line_selectorPairing_mono_of_unique_argmax
          hatP F x0 β uStar huStar t d (α := -τ) (β' := 0) (by linarith)
    exact hmono

/-- Helper for Proposition 7.28: the remaining reverse inclusion is that every scalar subgradient
of the shifted owner at `0` lies in the convex hull of the constrained subgradients of the active
shifted affine slices. -/
lemma shiftedLineSliceSubdifferential_eq_singleton_of_lineSliceSubdifferential_eq_singleton
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) (g : ℝ)
    (hline :
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) =
          {inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d}) :
    ∂ (fun α : ℝ ↦
      pointwiseSupremumOn (Set.univ : Set hatP)
        (fun τ u ↦
          ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
              τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α)(0) =
      {inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d - g} := by
  ext h
  constructor
  · intro hh
    have hhLine :
        h + g ∈
          ∂ (fun α : ℝ ↦
            (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) := by
      -- Add back the affine tilt to convert the shifted scalar subgradient to an exact one.
      exact
        memSubdifferential_lineSlice_of_memSubdifferential_shiftedLineSlice
          hatP F x0 β uStar huStar t d hh
    rw [hline] at hhLine
    rcases Set.mem_singleton_iff.mp hhLine with hhEq
    -- Expanding the transported exact slope identifies the shifted singleton element.
    exact Set.mem_singleton_iff.mpr <| by
      linarith
  · intro hh
    rcases Set.mem_singleton_iff.mp hh with rfl
    -- The shifted selector slope is always a shifted scalar subgradient at the base point.
    exact
      shiftedLineSlice_selectorSlope_memSubdifferential_at_zero
        hatP F x0 β uStar huStar t d g

/-- Helper for Proposition 7.28: once the exact line slice at `0` has singleton subdifferential,
the shifted active-hull reverse inclusion follows by rewriting both sides to the same singleton. -/
lemma shiftedLineSliceSubdifferential_subset_activeAffineHullAtZero_of_lineSliceSubdifferential_eq_singleton
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) (g : ℝ)
    (hline :
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) =
          {inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d}) :
    ∂ (fun α : ℝ ↦
      pointwiseSupremumOn (Set.univ : Set hatP)
        (fun τ u ↦
          ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
              τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α)(0) ⊆
      convexHull ℝ
        {h | ∃ u : hatP,
            u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP)
              (fun α u ↦
                ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                    α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) 0 ∧
              h ∈ ∂[Set.univ]
                (fun α : ℝ ↦
                  ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                      α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ))(0)} := by
  intro h hh
  have hshifted :
      ∂ (fun α : ℝ ↦
        pointwiseSupremumOn (Set.univ : Set hatP)
          (fun τ u ↦
            ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α)(0) =
        {inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d - g} := by
    -- First collapse the shifted scalar subdifferential to the shifted selector slope singleton.
    exact
      shiftedLineSliceSubdifferential_eq_singleton_of_lineSliceSubdifferential_eq_singleton
        hatP F x0 β uStar huStar t d g hline
  let target : ℝ := inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d - g
  have hhSingleton : h ∈ ({target} : Set ℝ) := by
    -- Rewriting the shifted subdifferential by the singleton gives the candidate immediately.
    have hh' := hh
    rw [hshifted] at hh'
    simpa [target] using hh'
  have hHull :
      convexHull ℝ
        {h | ∃ u : hatP,
            u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP)
              (fun α u ↦
                ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                    α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) 0 ∧
              h ∈ ∂[Set.univ]
                (fun α : ℝ ↦
                  ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                      α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ))(0)} =
        {target} := by
    -- The shifted active hull is already the same singleton by the unique active-slope theorem.
    simpa [target] using
      shiftedActiveAffineHullAtZero_eq_singleton_shiftedSelectorSlope
        hatP F x0 β uStar huStar huStar_unique t d g
  -- Rewriting the target hull by the same singleton discharges the inclusion.
  rw [hHull]
  exact hhSingleton

/-- Helper for Proposition 7.28: for the shifted real-valued scalar owner, having zero
subgradient at `0` is equivalent to `0` being a global minimizer. -/
lemma zeroMemSubdifferential_shiftedLineSlice_iff_isMinOn_zero
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) {g : ℝ} :
    0 ∈
      ∂ (fun α : ℝ ↦
        pointwiseSupremumOn (Set.univ : Set hatP)
          (fun τ u ↦
            ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α)(0) ↔
      IsMinOn
        (fun α : ℝ ↦
          Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) - α * g)
        Set.univ
        0 := by
  constructor
  · -- The forward direction is the existing shifted zero-subgradient to minimizer bridge.
    intro hg0
    exact
      shiftedLineSlice_isMinOn_zero_of_zeroMemSubdifferential
        hatP F x0 β uStar huStar t d hg0
  · intro hmin
    let ψ : ℝ → ℝ := fun α ↦
      Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) - α * g
    have hψ :
        (fun α : ℝ ↦
          pointwiseSupremumOn (Set.univ : Set hatP)
            (fun τ u ↦
              ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                  τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α) =
          fun α : ℝ ↦ ((ψ α : ℝ) : WithTop ℝ) := by
      -- Normalize the shifted owner to the affine-tilted real-valued line slice before reading
      -- the minimizer inequality as the zero support inequality.
      simpa [ψ] using
        shiftedLineSlice_owner_eq_affineTilt
          hatP F x0 β uStar huStar t d g
    have hinner (x y : ℝ) : inner ℝ x y = x * y := by
      simpa using real_inner_eq_mul x y
    rw [isMinOn_univ_iff] at hmin
    have hzero :
        0 ∈ ∂ (fun α : ℝ ↦ ((ψ α : ℝ) : WithTop ℝ))(0) := by
      rw [mem_subdifferential_coe_real_iff]
      intro y
      -- A global minimum at `0` is exactly the support inequality with zero slope.
      simpa [ψ, hinner] using hmin y
    rw [hψ]
    exact hzero

/-- Helper for Proposition 7.28: once the shifted subdifferential at `0` is the singleton
`{b0 - g}`, the sign directional-derivative bounds follow immediately. -/
lemma shiftedLineSliceDirectionalDerivativeSigns_le_of_subdifferential_eq_singleton
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) (g : ℝ) :
    let ψLift : ℝ → WithTop ℝ := fun α ↦
      pointwiseSupremumOn (Set.univ : Set hatP)
        (fun τ u ↦
          ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
              τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α
    let b0 : ℝ := inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d - g
    let h0 : (0 : ℝ) ∈ interior (dom ψLift) :=
      shiftedLineSlice_zero_mem_interior_dom hatP F x0 β uStar huStar t d g
    ∂ ψLift(0) = {b0} →
      convexDirectionalDerivativeReal ψLift h0 (1 : ℝ) ≤ b0 ∧
        convexDirectionalDerivativeReal ψLift h0 (-1 : ℝ) ≤ -b0 := by
  dsimp
  let ψLift : ℝ → WithTop ℝ := fun α ↦
    pointwiseSupremumOn (Set.univ : Set hatP)
      (fun τ u ↦
        ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
            τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α
  let b0 : ℝ := inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d - g
  let h0 : (0 : ℝ) ∈ interior (dom ψLift) :=
    shiftedLineSlice_zero_mem_interior_dom hatP F x0 β uStar huStar t d g
  intro hsingleton
  have hconv : ConvexOn ℝ (dom ψLift) (withTopRealPart ψLift) := by
    -- Keep the shifted owner in its lifted spelling before invoking the singleton derivative
    -- comparison theorem.
    simpa [ψLift] using
      shiftedLineSliceLiftConvexOn hatP F x0 β uStar huStar t d g
  have hdir :
      ∂ ψLift(0) = {b0} →
        convexDirectionalDerivativeReal ψLift h0 (1 : ℝ) ≤ b0 ∧
          convexDirectionalDerivativeReal ψLift h0 (-1 : ℝ) ≤ -b0 := by
    exact
      directionalDerivativeSigns_le_of_subdifferential_eq_singleton
        (φLift := ψLift) (b0 := b0) hconv h0
  -- Once the shifted subdifferential is singleton, the generic Chapter 3 scalar theorem closes
  -- both sign bounds.
  exact hdir hsingleton

/-- Helper for Proposition 7.28: once the exact line slice at `0` already has singleton
subdifferential `{b0}`, transporting a zero shifted subgradient back to the exact owner forces the
shifted selector slope `b0 - g` to vanish. -/
lemma zeroShiftedSubgradient_forces_zero_shiftedSelectorSlope_of_lineSliceSubdifferential_eq_singleton
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) {g : ℝ}
    (hline :
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) =
        {inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d})
    (hg0 :
      0 ∈
        ∂ (fun α : ℝ ↦
          pointwiseSupremumOn (Set.univ : Set hatP)
            (fun τ u ↦
              ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                  τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α)(0)) :
    inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d - g = 0 := by
  have hg :
      g ∈
        ∂ (fun α : ℝ ↦
          (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) := by
    -- Add back the affine tilt once so the shifted zero-subgradient becomes an exact one.
    exact
      memSubdifferential_lineSlice_of_zeroMemSubdifferential_shiftedLineSlice
        hatP F x0 β uStar huStar t d hg0
  rw [hline] at hg
  rcases Set.mem_singleton_iff.mp hg with hgEq
  -- Expanding the transported exact singleton identity recovers the vanishing shifted slope.
  linarith

/-- Helper for Proposition 7.28: subtracting the affine tilt `α ↦ α * g` from a scalar line slice
shifts the derivative at `0` by the same slope `g`. -/
lemma subAffineTilt_hasDerivAt_zero
    {φ : ℝ → ℝ} {b0 g : ℝ}
    (hφ : HasDerivAt φ b0 0) :
    HasDerivAt (fun α : ℝ ↦ φ α - α * g) (b0 - g) 0 := by
  have htilt : HasDerivAt (fun α : ℝ ↦ α * g) g 0 := by
    -- The affine tilt has constant derivative `g`.
    simpa using (hasDerivAt_id 0).mul_const g
  -- Subtracting the affine line shifts the derivative by the same scalar.
  simpa using hφ.sub htilt

/-- Helper for Proposition 7.28: in direction `1`, the scalar directional derivative of the
shifted lifted line slice is itself a shifted scalar subgradient at `0`. -/
lemma shiftedLineSliceDirectionalDerivativeAtOne_memSubdifferential
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) (g : ℝ) :
    let ψLift : ℝ → WithTop ℝ := fun α ↦
      pointwiseSupremumOn (Set.univ : Set hatP)
        (fun τ u ↦
          ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
              τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α
    let h0 : (0 : ℝ) ∈ interior (dom ψLift) :=
      shiftedLineSlice_zero_mem_interior_dom hatP F x0 β uStar huStar t d g
    ψLift′[h0] (1 : ℝ) ∈ ∂ ψLift(0) := by
  dsimp
  let ψLift : ℝ → WithTop ℝ := fun α ↦
    pointwiseSupremumOn (Set.univ : Set hatP)
      (fun τ u ↦
        ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
            τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α
  let h0 : (0 : ℝ) ∈ interior (dom ψLift) :=
    shiftedLineSlice_zero_mem_interior_dom hatP F x0 β uStar huStar t d g
  have hconv : ConvexOn ℝ (dom ψLift) (withTopRealPart ψLift) := by
    -- Keep the shifted owner in its lifted spelling before applying the Chapter 3 max formula.
    simpa [ψLift] using
      shiftedLineSliceLiftConvexOn hatP F x0 β uStar huStar t d g
  have hgreatest :=
    convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior
      hconv h0 (1 : ℝ)
  rw [convexDirectionalDerivativeReal_apply] at hgreatest
  rcases hgreatest.1 with ⟨h, hh, hhEq⟩
  have hinner (x y : ℝ) : inner ℝ x y = x * y := by
    simpa using real_inner_eq_mul x y
  have hhVal : h = ψLift′[h0] (1 : ℝ) := by
    simpa [hinner] using hhEq
  -- The maximizing subgradient in direction `1` is exactly the derivative value itself.
  rw [hhVal] at hh
  exact hh

/-- Helper for Proposition 7.28: in direction `-1`, the negated scalar directional derivative of
the shifted lifted line slice is a shifted scalar subgradient at `0`. -/
lemma shiftedLineSliceNegDirectionalDerivativeAtNegOne_memSubdifferential
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) (g : ℝ) :
    let ψLift : ℝ → WithTop ℝ := fun α ↦
      pointwiseSupremumOn (Set.univ : Set hatP)
        (fun τ u ↦
          ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
              τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α
    let h0 : (0 : ℝ) ∈ interior (dom ψLift) :=
      shiftedLineSlice_zero_mem_interior_dom hatP F x0 β uStar huStar t d g
    (-ψLift′[h0] (-1 : ℝ)) ∈ ∂ ψLift(0) := by
  dsimp
  let ψLift : ℝ → WithTop ℝ := fun α ↦
    pointwiseSupremumOn (Set.univ : Set hatP)
      (fun τ u ↦
        ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
            τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α
  let h0 : (0 : ℝ) ∈ interior (dom ψLift) :=
    shiftedLineSlice_zero_mem_interior_dom hatP F x0 β uStar huStar t d g
  have hconv : ConvexOn ℝ (dom ψLift) (withTopRealPart ψLift) := by
    -- Keep the shifted owner in its lifted spelling before applying the Chapter 3 max formula.
    simpa [ψLift] using
      shiftedLineSliceLiftConvexOn hatP F x0 β uStar huStar t d g
  have hgreatest :=
    convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior
      hconv h0 (-1 : ℝ)
  rw [convexDirectionalDerivativeReal_apply] at hgreatest
  rcases hgreatest.1 with ⟨h, hh, hhEq⟩
  have hinner (x y : ℝ) : inner ℝ x y = x * y := by
    simpa using real_inner_eq_mul x y
  have hhVal : h = -ψLift′[h0] (-1 : ℝ) := by
    have hneg : -h = ψLift′[h0] (-1 : ℝ) := by
      simpa [hinner] using hhEq
    linarith
  -- The maximizing subgradient in direction `-1` is the negative of the derivative value there.
  rw [hhVal] at hh
  exact hh

/-- Helper for Proposition 7.28: once a lifted scalar owner `ψLift` is an everywhere-finite convex
real function and its subdifferential at `0` is the singleton `{b0}`, its directional-derivative
owner is the affine map `p ↦ p * b0`. -/
lemma convexDirectionalDerivativeModel_eq_mul_of_owner_eq_coeReal_and_subdifferential_eq_singleton
    {ψLift : ℝ → WithTop ℝ} {ψ : ℝ → ℝ} {b0 : ℝ}
    (hψ : ψLift = fun α : ℝ ↦ ((ψ α : ℝ) : WithTop ℝ))
    (hconv : ConvexOn ℝ (dom ψLift) (withTopRealPart ψLift))
    (h0 : (0 : ℝ) ∈ interior (dom ψLift))
    (hsub : ∂ ψLift(0) = {b0}) :
    ∀ p : ℝ, ψLift′[h0] p = p * b0 := by
  rw [hψ] at hconv h0 hsub
  have hdom :
      dom (fun α : ℝ ↦ ((ψ α : ℝ) : WithTop ℝ)) = (Set.univ : Set ℝ) := by
    -- A lifted real-valued owner is finite at every scalar parameter.
    ext α
    change ((((ψ α : ℝ) : WithTop ℝ) < ⊤)) ↔ True
    constructor
    · intro _
      trivial
    · intro _
      exact WithTop.coe_lt_top _
  rw [hdom] at hconv
  have hconvLift :
      ConvexOn ℝ
        (dom (fun α : ℝ ↦ ((ψ α : ℝ) : WithTop ℝ)))
        (withTopRealPart (fun α : ℝ ↦ ((ψ α : ℝ) : WithTop ℝ))) := by
    -- Keep a lifted-owner convexity view for the Chapter 3 directional-derivative API.
    simpa [hdom] using hconv
  have hconvReal : ConvexOn ℝ Set.univ ψ := by
    -- After normalizing the domain to `Set.univ`, the lifted convexity is ordinary convexity.
    simpa [withTopEffectiveDomain] using hconv
  have hgrad : HasGradientAt ψ b0 0 := by
    -- Convexity plus the singleton subdifferential identifies the scalar gradient at `0`.
    exact
      hasGradientAt_of_convexOn_univ_subdifferential_eq_singleton
        hconvReal hsub
  intro p
  have howner :
      HasDirectionalDerivAt
        (withTopToEReal ∘ fun α : ℝ ↦ ((ψ α : ℝ) : WithTop ℝ))
        0 p
        (convexDirectionalDerivativeReal
          (fun α : ℝ ↦ ((ψ α : ℝ) : WithTop ℝ))
          h0 p) := by
    -- The Chapter 3 owner identifies the directional derivative of the lifted scalar owner.
    exact
      convexDirectionalDerivative_toReal_hasDirectionalDerivAt
        hconvLift h0 p
  have hsliceDeriv :
      HasDerivAt (fun α : ℝ ↦ ψ (α * p)) (p * b0) 0 := by
    have hbase : HasDerivAt ψ b0 (p * 0) := by
      -- Rewrite the scalar derivative so its base point matches the image of `α ↦ α * p`.
      simpa [zero_mul] using hgrad.hasDerivAt
    have hscale : HasDerivAt (fun α : ℝ ↦ p * α) p 0 := by
      -- The direction-scaling map has constant derivative `p`.
      simpa [mul_comm] using (hasDerivAt_id 0).const_mul p
    -- Compose the scalar derivative at `0` with the direction scaling `α ↦ α * p`.
    have hcomp := hbase.comp 0 hscale
    convert hcomp using 1
    · ext α
      simp [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    · ring
  have hmodel :
      HasDirectionalDerivAt
        (withTopToEReal ∘ fun α : ℝ ↦ ((ψ α : ℝ) : WithTop ℝ))
        0 p
        (p * b0) := by
    refine ⟨?_, ?_, ?_⟩
    · -- The lifted scalar owner is finite at the base point `0`.
      exact mem_dom_withTopToEReal_comp_of_mem_dom (by
        change ((((ψ 0 : ℝ) : WithTop ℝ) < ⊤))
        exact WithTop.coe_lt_top _)
    · -- The same finiteness is automatic along the whole real ray in direction `p`.
      filter_upwards with α
      exact mem_dom_withTopToEReal_comp_of_mem_dom (by
        change ((((ψ (0 + α • p) : ℝ) : WithTop ℝ) < ⊤))
        exact WithTop.coe_lt_top _)
    · have hslice :
          (fun α : ℝ ↦
            extendedRealRealPart
              (withTopToEReal ∘ fun a : ℝ ↦ ((ψ a : ℝ) : WithTop ℝ))
              (0 + α • p)) =
            fun α : ℝ ↦ ψ (α * p) := by
        -- Normalize the directional slice of the lifted owner back to the scalar line slice.
        funext α
        calc
          extendedRealRealPart
              (withTopToEReal ∘ fun a : ℝ ↦ ((ψ a : ℝ) : WithTop ℝ))
              (0 + α • p)
              =
              withTopRealPart
                (fun a : ℝ ↦ ((ψ a : ℝ) : WithTop ℝ))
                (0 + α • p) := by
                  simpa [extendedRealRealPart, Function.comp] using
                    (withTopToEReal_toReal_eq_withTopRealPart
                      (f := fun a : ℝ ↦ ((ψ a : ℝ) : WithTop ℝ))
                      (z := 0 + α • p))
          _ = ψ (0 + α • p) := by
                simp [withTopRealPart]
          _ = ψ (α * p) := by
                simp [smul_eq_mul]
      rw [hslice]
      exact hsliceDeriv.hasDerivWithinAt
  -- Uniqueness of the finite directional derivative identifies the owner with the affine model.
  simpa [hψ] using HasDirectionalDerivAt.unique howner hmodel

/-- Helper for Proposition 7.28: once the exact future and past selector slopes both converge
back to the base selector slope, the exact lifted line slice at `0` has singleton subdifferential
given by that selector slope. -/
lemma lineSliceSubdifferential_eq_singleton_of_selectorSlope_limits
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E)
    (hfuture :
      Tendsto
        (fun τ : ℝ ↦
          inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + τ • d)) - x0) d)
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)))
    (hpast :
      Tendsto
        (fun τ : ℝ ↦
          inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t - τ • d)) - x0) d)
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d))) :
    ∂ (fun α : ℝ ↦
      (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) =
      {inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d} := by
  ext g
  constructor
  · intro hg
    -- The one-sided selector-slope limits squeeze every exact subgradient to the base selector
    -- slope.
    exact Set.mem_singleton_iff.mpr <|
      lineSliceSubgradient_eq_selectorSlope_at_zero_of_limits
        hatP F x0 β uStar huStar t d hfuture hpast hg
  · intro hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    -- The selector slope itself is always an exact subgradient of the lifted line slice.
    exact
      lineSliceLiftSelectorMemSubdifferential
        hatP F x0 β uStar huStar t d

/-- Helper for Proposition 7.28: once the exact line slice at `0` has singleton subdifferential
`{inner ℝ (uStar ((toDual) t) - x0) d}`, the shifted owner at the same base point already has the
affine directional-derivative model with slope `inner ℝ (uStar ((toDual) t) - x0) d - g`. -/
lemma shiftedLineSliceDirectionalDerivativeModelAtZero_of_lineSliceSubdifferential_eq_singleton
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) (g : ℝ)
    (hline :
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) =
        {inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d}) :
    let ψLift : ℝ → WithTop ℝ := fun α ↦
      pointwiseSupremumOn (Set.univ : Set hatP)
        (fun τ u ↦
          ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
              τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α
    let h0 : (0 : ℝ) ∈ interior (dom ψLift) :=
      shiftedLineSlice_zero_mem_interior_dom hatP F x0 β uStar huStar t d g
    ∀ p : ℝ,
      ψLift′[h0] p =
        p * (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d - g) := by
  let ψLift : ℝ → WithTop ℝ := fun α ↦
    pointwiseSupremumOn (Set.univ : Set hatP)
      (fun τ u ↦
        ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
            τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α
  let ψ : ℝ → ℝ := fun α ↦
    Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) - α * g
  let b0 : ℝ := inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d - g
  let h0 : (0 : ℝ) ∈ interior (dom ψLift) :=
    shiftedLineSlice_zero_mem_interior_dom hatP F x0 β uStar huStar t d g
  have hψ :
      ψLift = fun α : ℝ ↦ ((ψ α : ℝ) : WithTop ℝ) := by
    -- Normalize the shifted owner to the affine-tilted exact line slice.
    simpa [ψ, ψLift] using
      shiftedLineSlice_owner_eq_affineTilt
        hatP F x0 β uStar huStar t d g
  have hconv :
      ConvexOn ℝ (dom ψLift) (withTopRealPart ψLift) := by
    -- Keep the shifted owner in its lifted spelling before reading off the affine model.
    simpa [ψLift] using
      shiftedLineSliceLiftConvexOn hatP F x0 β uStar huStar t d g
  have hsub : ∂ ψLift(0) = {b0} := by
    -- Transport the exact singleton through the affine tilt `α ↦ α * g`.
    simpa [ψLift, b0] using
      shiftedLineSliceSubdifferential_eq_singleton_of_lineSliceSubdifferential_eq_singleton
        hatP F x0 β uStar huStar t d g hline
  -- The shifted singleton subdifferential identifies the whole directional-derivative owner.
  simpa [ψLift, b0, h0] using
    convexDirectionalDerivativeModel_eq_mul_of_owner_eq_coeReal_and_subdifferential_eq_singleton
      (ψLift := ψLift) (ψ := ψ) (b0 := b0) hψ hconv h0 hsub

/-- Helper for Proposition 7.28: the exact scalar line slice is differentiable at the base
parameter once the singleton subdifferential theorem is available. -/
lemma lineSliceHasDerivAt_zero_support
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) :
    HasDerivAt
      (fun α : ℝ ↦
        Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)))
      (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)
      0 := by
  let φ : ℝ → ℝ := fun α ↦
    Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d))
  let b0 : ℝ := inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d
  have hconv : ConvexOn ℝ Set.univ φ :=
    supportFunctionApproximation_line_convexOn_univ_of_selector
      hatP F x0 β uStar huStar t d
  have hsub : ∂ (fun α : ℝ ↦ (φ α : WithTop ℝ))(0) = {b0} := by
    -- Route correction: the differentiability wrapper is now reduced to the canonical scalar
    -- singleton-subdifferential step.
    -- TODO: close this by proving the noncyclic exact singleton bridge
    -- `lineSliceSubdifferential_eq_singleton_zeroBase_of_directionalDerivativeBounds` earlier in
    -- the dependency graph, then `simpa [φ, b0]`.
    sorry
  have hgrad : HasGradientAt φ b0 0 := by
    -- Convexity plus the singleton subdifferential identifies the scalar gradient at `0`.
    exact hasGradientAt_of_convexOn_univ_subdifferential_eq_singleton hconv hsub
  -- On `ℝ`, the scalar gradient is exactly the ordinary derivative.
  simpa [φ, b0] using hgrad.hasDerivAt

/-- Helper for Proposition 7.28: the future selector slopes along the exact line converge back
to the base selector slope. -/
lemma lineSliceFutureSelectorSlope_tendsto_baseSlope_local
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) :
    Tendsto
      (fun τ : ℝ ↦
        inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + τ • d)) - x0) d)
      (𝓝[>] (0 : ℝ))
      (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)) := by
  let φ : ℝ → ℝ := fun α ↦
    Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d))
  let futureSlope : ℝ → ℝ := fun τ ↦
    inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + τ • d)) - x0) d
  let rightSecant : ℝ → ℝ := fun τ ↦ (φ τ - φ 0) / τ
  have hderiv0 :
      HasDerivAt φ (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d) 0 := by
    -- Reuse the restored scalar derivative at the base point.
    simpa [φ] using
      lineSliceHasDerivAt_zero_support
        hatP F x0 β uStar huStar huStar_unique t d
  have hrightSecant :
      Tendsto rightSecant (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)) := by
    -- The derivative at `0` is exactly the limit of forward secants.
    simpa [rightSecant, div_eq_mul_inv, slope_fun_def_field, mul_comm, mul_left_comm, mul_assoc]
      using hderiv0.tendsto_slope_zero_right
  have htwo :
      Tendsto (fun τ : ℝ ↦ (2 : ℝ) * τ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    -- Positive scaling preserves the right-neighborhood filter at `0`.
    have htwo' :
        Tendsto (fun τ : ℝ ↦ (2 : ℝ) * τ) (𝓝[>] (0 : ℝ))
          (𝓝[>] ((2 : ℝ) * 0)) := by
      exact
        Filter.TendstoNhdsWithinIoi.const_mul
          (b := (2 : ℝ)) (c := (0 : ℝ)) (f := fun τ : ℝ ↦ τ)
          (by norm_num)
          (tendsto_id : Tendsto (fun τ : ℝ ↦ τ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)))
    simpa using htwo'
  have hrightSecantTwo :
      Tendsto (fun τ : ℝ ↦ rightSecant ((2 : ℝ) * τ)) (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)) := by
    -- Reindex the forward secants by `τ ↦ 2τ`.
    exact hrightSecant.comp htwo
  have hfutureUpper :
      Tendsto (fun τ : ℝ ↦ 2 * rightSecant (2 * τ) - rightSecant τ) (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)) := by
    -- Adjacent forward secants collapse to the same base slope.
    have htwoConst : Tendsto (fun _ : ℝ ↦ (2 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (2 : ℝ)) :=
      tendsto_const_nhds
    convert (htwoConst.mul hrightSecantTwo).sub hrightSecant using 2 <;> ring
  have hfutureLowerBound :
      ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
        inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d ≤ futureSlope τ := by
    -- Monotonicity of selector pairings places every future slope above the base slope.
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    simpa [futureSlope, zero_smul] using
      supportFunctionApproximation_line_selectorPairing_mono_of_unique_argmax
        hatP F x0 β uStar huStar t d (α := 0) (β' := τ) hτ.le
  have hfutureUpperBound :
      ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
        futureSlope τ ≤ 2 * rightSecant (2 * τ) - rightSecant τ := by
    -- Compare the active slope at `τ` to the secant over `[τ, 2τ]`, then rewrite that secant
    -- through the two base-point secants.
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτpos : 0 < τ := hτ
    have hsecantRaw :=
      (supportFunctionApproximation_line_secantQuotient_bounds_of_unique_argmax
        hatP F x0 β uStar huStar t d (α := τ) (β' := 2 * τ) (by linarith [hτpos])).1
    have hsecant :
        futureSlope τ ≤ (φ (2 * τ) - φ τ) / τ := by
      simpa [futureSlope, φ, two_smul, show 2 * τ - τ = τ by ring] using hsecantRaw
    have hrepack :
        (φ (2 * τ) - φ τ) / τ = 2 * rightSecant (2 * τ) - rightSecant τ := by
      dsimp [rightSecant]
      field_simp [hτpos.ne']
      ring
    simpa [hrepack] using hsecant
  -- Squeeze the future selector slopes between the constant base slope and the adjacent secants.
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hfutureUpper hfutureLowerBound hfutureUpperBound

/-- Helper for Proposition 7.28: the past selector slopes along the exact line converge back to
the same base selector slope. -/
lemma lineSlicePastSelectorSlope_tendsto_baseSlope_local
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) :
    Tendsto
      (fun τ : ℝ ↦
        inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t - τ • d)) - x0) d)
      (𝓝[>] (0 : ℝ))
      (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)) := by
  let φ : ℝ → ℝ := fun α ↦
    Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d))
  let pastSlope : ℝ → ℝ := fun τ ↦
    inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t - τ • d)) - x0) d
  let leftSecant : ℝ → ℝ := fun τ ↦ (φ (-τ) - φ 0) / (-τ)
  have hderiv0 :
      HasDerivAt φ (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d) 0 := by
    -- Reuse the restored scalar derivative at the base point.
    simpa [φ] using
      lineSliceHasDerivAt_zero_support
        hatP F x0 β uStar huStar huStar_unique t d
  have hleftRaw :
      Tendsto (fun α : ℝ ↦ (φ α - φ 0) / α) (𝓝[<] (0 : ℝ))
        (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)) := by
    -- The same derivative controls the left secants.
    simpa [div_eq_mul_inv, slope_fun_def_field, mul_comm, mul_left_comm, mul_assoc] using
      hderiv0.tendsto_slope_zero_left
  have hneg :
      Tendsto (fun τ : ℝ ↦ -τ) (𝓝[>] (0 : ℝ)) (𝓝[<] (0 : ℝ)) := by
    have hneg' :
        Tendsto Neg.neg (𝓝[>] (0 : ℝ)) (𝓝[<] (-(0 : ℝ))) :=
      tendsto_neg_nhdsGT
    simpa using hneg'
  have hleftSecant :
      Tendsto leftSecant (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)) := by
    -- Pull the left-slope limit back to positive steps by the change of variables `α = -τ`.
    simpa [leftSecant] using hleftRaw.comp hneg
  have htwo :
      Tendsto (fun τ : ℝ ↦ (2 : ℝ) * τ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    -- Positive scaling preserves the right-neighborhood filter at `0`.
    have htwo' :
        Tendsto (fun τ : ℝ ↦ (2 : ℝ) * τ) (𝓝[>] (0 : ℝ))
          (𝓝[>] ((2 : ℝ) * 0)) := by
      exact
        Filter.TendstoNhdsWithinIoi.const_mul
          (b := (2 : ℝ)) (c := (0 : ℝ)) (f := fun τ : ℝ ↦ τ)
          (by norm_num)
          (tendsto_id : Tendsto (fun τ : ℝ ↦ τ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)))
    simpa using htwo'
  have hleftSecantTwo :
      Tendsto (fun τ : ℝ ↦ leftSecant ((2 : ℝ) * τ)) (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)) := by
    -- Reindex the backward secants by `τ ↦ 2τ`.
    exact hleftSecant.comp htwo
  have hpastLower :
      Tendsto (fun τ : ℝ ↦ 2 * leftSecant (2 * τ) - leftSecant τ) (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)) := by
    -- Adjacent backward secants collapse to the same base slope.
    have htwoConst : Tendsto (fun _ : ℝ ↦ (2 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (2 : ℝ)) :=
      tendsto_const_nhds
    convert (htwoConst.mul hleftSecantTwo).sub hleftSecant using 2 <;> ring
  have hpastLowerBound :
      ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
        2 * leftSecant (2 * τ) - leftSecant τ ≤ pastSlope τ := by
    -- Compare the backward active slope to the secant over `[-2τ, -τ]`, then rewrite that secant
    -- by the base-point backward secants.
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτpos : 0 < τ := hτ
    have hsecantRaw :=
      (supportFunctionApproximation_line_secantQuotient_bounds_of_unique_argmax
        hatP F x0 β uStar huStar t d
        (α := -(2 * τ)) (β' := -τ) (by linarith [hτpos])).2
    have hsecant :
        (φ (-τ) - φ (-(2 * τ))) / τ ≤ pastSlope τ := by
      simpa [pastSlope, φ, sub_eq_add_neg, two_smul,
        show -τ - -(2 * τ) = τ by ring,
        show -τ + 2 * τ = τ by ring] using hsecantRaw
    have hrepack :
        (φ (-τ) - φ (-(2 * τ))) / τ = 2 * leftSecant (2 * τ) - leftSecant τ := by
      dsimp [leftSecant]
      field_simp [hτpos.ne']
      ring
    simpa [hrepack] using hsecant
  have hpastUpperBound :
      ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
        pastSlope τ ≤ inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d := by
    -- The past selector slopes stay below the base slope by the same monotonicity.
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτpos : 0 < τ := hτ
    simpa [pastSlope, zero_smul, sub_eq_add_neg] using
      supportFunctionApproximation_line_selectorPairing_mono_of_unique_argmax
        hatP F x0 β uStar huStar t d (α := -τ) (β' := 0) (by linarith [hτpos])
  -- Squeeze the past selector slopes between the adjacent backward secants and the same constant.
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hpastLower tendsto_const_nhds hpastLowerBound hpastUpperBound

/-- Helper for Proposition 7.28: package the two one-sided selector-slope limits in the exact
shape needed for the singleton-subdifferential bridge. -/
lemma lineSliceSelectorSlope_tendsto_baseSlope_local
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) :
    Tendsto
        (fun τ : ℝ ↦
          inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + τ • d)) - x0) d)
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)) ∧
      Tendsto
        (fun τ : ℝ ↦
          inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t - τ • d)) - x0) d)
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)) := by
  constructor
  · -- The right-hand limit is the future-slope support lemma.
    exact
      lineSliceFutureSelectorSlope_tendsto_baseSlope_local
        hatP F x0 β uStar huStar huStar_unique t d
  · -- The left-hand limit is the past-slope support lemma.
    exact
      lineSlicePastSelectorSlope_tendsto_baseSlope_local
        hatP F x0 β uStar huStar huStar_unique t d

/-- Helper for Proposition 7.28: the shifted line slice should have affine directional-derivative
model at `0`, with slope given by the shifted selector pairing. -/
lemma shiftedLineSliceDirectionalDerivativeModelAtZero_of_uniqueArgmax
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) (g : ℝ) :
    let ψLift : ℝ → WithTop ℝ := fun α ↦
      pointwiseSupremumOn (Set.univ : Set hatP)
        (fun τ u ↦
          ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
              τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α
    let h0 : (0 : ℝ) ∈ interior (dom ψLift) :=
      shiftedLineSlice_zero_mem_interior_dom hatP F x0 β uStar huStar t d g
    ∀ p : ℝ,
      ψLift′[h0] p =
        p * (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d - g) := by
  have hline :
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) =
        {inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d} := by
    have hlimits :
        Tendsto
            (fun τ : ℝ ↦
              inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + τ • d)) - x0) d)
            (𝓝[>] (0 : ℝ))
            (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)) ∧
          Tendsto
            (fun τ : ℝ ↦
              inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t - τ • d)) - x0) d)
            (𝓝[>] (0 : ℝ))
            (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)) := by
      -- Route correction: close the remaining frontier by reusing the exact one-sided
      -- selector-slope limit package, instead of reopening the shifted active-hull detour.
      exact
        lineSliceSelectorSlope_tendsto_baseSlope_local
          hatP F x0 β uStar huStar huStar_unique t d
    -- Once the two one-sided selector-slope limits are available, the exact scalar
    -- subdifferential collapses immediately to the singleton selector slope.
    exact
      lineSliceSubdifferential_eq_singleton_of_selectorSlope_limits
        hatP F x0 β uStar huStar t d hlimits.1 hlimits.2
  -- Once the exact singleton is available, the shifted directional-derivative model is routine.
  simpa using
    shiftedLineSliceDirectionalDerivativeModelAtZero_of_lineSliceSubdifferential_eq_singleton
      hatP F x0 β uStar huStar t d g hline
lemma zeroMemSubdifferential_shiftedLineSlice_implies_zero_mem_activeAffineHullAtZero
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) {g : ℝ}
    (hg0 :
      0 ∈
        ∂ (fun α : ℝ ↦
          pointwiseSupremumOn (Set.univ : Set hatP)
            (fun τ u ↦
              ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                  τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α)(0)) :
    0 ∈
      convexHull ℝ
        {h | ∃ u : hatP,
            u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP)
              (fun α u ↦
                ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                    α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) 0 ∧
                h ∈ ∂[Set.univ]
                  (fun α : ℝ ↦
                    ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                        α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ))(0)} := by
  let ψLift : ℝ → WithTop ℝ := fun α ↦
    pointwiseSupremumOn (Set.univ : Set hatP)
      (fun τ u ↦
        ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
            τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α
  let b0 : ℝ := inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d - g
  let h0 : (0 : ℝ) ∈ interior (dom ψLift) :=
    shiftedLineSlice_zero_mem_interior_dom hatP F x0 β uStar huStar t d g
  have hconv :
      ConvexOn ℝ (dom ψLift) (withTopRealPart ψLift) := by
    -- Keep the shifted owner in its lifted spelling before transporting subgradients through
    -- Theorem 3.21.
    simpa [ψLift] using
      shiftedLineSliceLiftConvexOn hatP F x0 β uStar huStar t d g
  have hsub_univ :
      ∂ (fun p : ℝ ↦ ((ψLift′[h0] p : ℝ) : WithTop ℝ))(0) =
        ∂[Set.univ] ψLift′[h0](0) := by
    ext h
    rw [mem_subdifferential_coe_real_iff, mem_subdifferentialWithin_iff]
    constructor
    · intro hh
      refine ⟨by simp, ?_⟩
      intro y hy
      simpa using hh y
    · rintro ⟨_, hh⟩
      intro y
      simpa using hh (show y ∈ Set.univ by simp)
  have hdirSub :
      0 ∈ ∂ (fun p : ℝ ↦ ((ψLift′[h0] p : ℝ) : WithTop ℝ))(0) := by
    -- Route correction: move the original zero-subgradient statement to the directional-derivative
    -- owner at the origin, where the pending blocker is a single affine-model identity.
    rw [hsub_univ, subdifferential_convexDirectionalDerivativeReal_at_zero_eq_subdifferential
      hconv h0]
    exact hg0
  have hmodel :
      ∀ p : ℝ, ψLift′[h0] p = p * b0 := by
    -- The remaining blocker is now isolated to the affine directional-derivative model of the
    -- shifted owner at `0`.
    simpa [ψLift, h0, b0] using
      shiftedLineSliceDirectionalDerivativeModelAtZero_of_uniqueArgmax
        hatP F x0 β uStar huStar huStar_unique t d g
  have hdirSingleton :
      ∂ (fun p : ℝ ↦ ((ψLift′[h0] p : ℝ) : WithTop ℝ))(0) = {b0} := by
    -- Rewrite the directional-derivative owner to the affine line `p ↦ p * b0`, whose
    -- subdifferential at `0` is the singleton `{b0}`.
    simpa [hmodel] using
      supportFunctionApproximation_affineScalarSlice_subdifferential_eq_singleton
        (a := 0) (slope := b0)
  have hb0 :
      0 = b0 := by
    -- Once the directional-derivative owner is affine, its zero subgradient reads off the slope.
    rw [hdirSingleton] at hdirSub
    exact Set.mem_singleton_iff.mp hdirSub
  -- Rewrite the shifted active hull to the same singleton `{b0}` and read off the zero member.
  rw [shiftedActiveAffineHullAtZero_eq_singleton_shiftedSelectorSlope
    hatP F x0 β uStar huStar huStar_unique t d g]
  exact Set.mem_singleton_iff.mpr hb0

/-- Helper for Proposition 7.28: a global minimum of the shifted real-valued line slice at `0`
already places `0` in the convex hull of the constrained subgradients of the affine slices active
at the base parameter. -/
lemma shiftedSelectorSlope_eq_zero_of_isMinOn
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) {g : ℝ}
    (hmin :
      IsMinOn
        (fun α : ℝ ↦
          Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) - α * g)
        Set.univ
        0) :
    inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d - g = 0 := by
  have hg0 :
      0 ∈
        ∂ (fun α : ℝ ↦
          pointwiseSupremumOn (Set.univ : Set hatP)
            (fun τ u ↦
              ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                  τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α)(0) := by
    -- Convert the shifted real-valued minimizer statement back to the zero-subgradient owner.
    exact
      (zeroMemSubdifferential_shiftedLineSlice_iff_isMinOn_zero
        hatP F x0 β uStar huStar t d).2 hmin
  have hhull :
      0 ∈
        convexHull ℝ
          {h | ∃ u : hatP,
              u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP)
                (fun α u ↦
                  ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                      α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) 0 ∧
                h ∈ ∂[Set.univ]
                  (fun α : ℝ ↦
                    ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                        α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ))(0)} := by
    -- Route correction: use the zero-subgradient-to-active-hull bridge directly, not the deleted
    -- exact-derivative detour.
    exact
      zeroMemSubdifferential_shiftedLineSlice_implies_zero_mem_activeAffineHullAtZero
        hatP F x0 β uStar huStar huStar_unique t d hg0
  -- Once the shifted active hull collapses to the singleton `{b0 - g}`, zero membership forces
  -- the shifted selector slope to vanish.
  rw [shiftedActiveAffineHullAtZero_eq_singleton_shiftedSelectorSlope
    hatP F x0 β uStar huStar huStar_unique t d g] at hhull
  simpa [eq_comm] using hhull

/-- Helper for Proposition 7.28: a global minimum of the shifted real-valued line slice at `0`
already places `0` in the convex hull of the constrained subgradients of the affine slices active
at the base parameter. -/
lemma zero_mem_convexHull_shiftedActiveAffineSubgradients_at_zero_of_isMinOn
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) {g : ℝ}
    (hmin :
      IsMinOn
        (fun α : ℝ ↦
          Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) - α * g)
        Set.univ
        0) :
    0 ∈
      convexHull ℝ
        {h | ∃ u : hatP,
            u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP)
              (fun α u ↦
                ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                    α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) 0 ∧
              h ∈ ∂[Set.univ]
                (fun α : ℝ ↦
                  ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                      α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ))(0)} := by
  have hb0g :
      inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d - g = 0 := by
    -- Route correction: isolate the minimizer-to-hull bridge to the smaller scalar statement
    -- that the shifted selector slope vanishes at a global minimizer.
    exact
      shiftedSelectorSlope_eq_zero_of_isMinOn
        hatP F x0 β uStar huStar huStar_unique t d hmin
  -- Once the shifted selector slope is zero, the collapsed shifted active hull contains `0`.
  exact
    zero_mem_convexHull_shiftedActiveAffineSubgradients_at_zero_of_selectorSlope_zero
      hatP F x0 β uStar huStar huStar_unique t d hb0g

lemma zeroShiftedSelectorSlope_of_isMinOn_unique_active
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) {g : ℝ}
    (hmin :
      IsMinOn
        (fun α : ℝ ↦
          Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) - α * g)
        Set.univ
        0) :
    inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d - g = 0 := by
  -- Route correction: this theorem is now the wrapper around the canonical scalar zero-case
  -- identity, instead of routing through the larger shifted active-hull membership statement.
  exact
    shiftedSelectorSlope_eq_zero_of_isMinOn
      hatP F x0 β uStar huStar huStar_unique t d hmin

/-- Helper for Proposition 7.28: if the shifted scalar owner has zero subgradient at `0`, then
the unique active slice at the base parameter should force the shifted selector slope to vanish. -/
lemma shiftedLineSlice_selectorSlope_eq_of_zero_memSubdifferential_unique_active
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) {g : ℝ}
    (hg0 :
      0 ∈
        ∂ (fun α : ℝ ↦
          pointwiseSupremumOn (Set.univ : Set hatP)
            (fun τ u ↦
              ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                  τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α)(0)) :
    g = inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d := by
  have hhull :
      0 ∈
        convexHull ℝ
          {h | ∃ u : hatP,
              u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP)
                (fun α u ↦
                  ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                      α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) 0 ∧
                h ∈ ∂[Set.univ]
                  (fun α : ℝ ↦
                    ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                        α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ))(0)} := by
    -- Route correction: use the direct shifted active-hull bridge, not the deleted derivative
    -- wrapper.
    exact
      zeroMemSubdifferential_shiftedLineSlice_implies_zero_mem_activeAffineHullAtZero
        hatP F x0 β uStar huStar huStar_unique t d hg0
  -- Collapse the shifted active hull to the singleton `{b0 - g}` and read off the slope.
  rw [shiftedActiveAffineHullAtZero_eq_singleton_shiftedSelectorSlope
    hatP F x0 β uStar huStar huStar_unique t d g] at hhull
  have hb0g :
      inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d - g = 0 := by
    simpa [eq_comm] using hhull
  linarith

/-- Helper for Proposition 7.28: the remaining exact-owner step is to bound the directional
derivatives of the unshifted scalar line slice at `0` by the singleton active affine hull. -/
lemma lineSliceDirectionalDerivativeAtZero_upperBounds_of_activeAffineHull
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) :
    let φLift : ℝ → WithTop ℝ := fun α ↦
      (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ)
    let b0 : ℝ := inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d
    let h0 : (0 : ℝ) ∈ interior (dom φLift) :=
      supportFunctionApproximation_line_zero_mem_interior_dom hatP F x0 β t d
    convexDirectionalDerivativeReal φLift h0 (1 : ℝ) ≤ b0 ∧
      convexDirectionalDerivativeReal φLift h0 (-1 : ℝ) ≤ -b0 := by
  let φLift : ℝ → WithTop ℝ := fun α ↦
    (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ)
  let b0 : ℝ := inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d
  let h0 : (0 : ℝ) ∈ interior (dom φLift) :=
    supportFunctionApproximation_line_zero_mem_interior_dom hatP F x0 β t d
  have hconv :
      ConvexOn ℝ (dom φLift) (withTopRealPart φLift) := by
    -- Keep the exact lifted line-slice owner while invoking the Chapter 3 singleton squeeze.
    simpa [φLift] using lineSliceLiftConvexOn hatP F x0 β uStar huStar t d
  have hsub :
      ∂ φLift(0) = {b0} := by
    ext g
    constructor
    · intro hg
      have hzero :
          0 ∈
            ∂ (fun α : ℝ ↦
              pointwiseSupremumOn (Set.univ : Set hatP)
                (fun τ u ↦
                  ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                      τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α)(0) := by
        -- Subtract the affine support line `α ↦ α * g` so the shifted owner has zero
        -- subgradient at the base point.
        exact
          zeroMemSubdifferential_shiftedLineSlice_of_memSubdifferential
            hatP F x0 β uStar huStar t d hg
      -- The unique zero-active slice should identify every exact scalar subgradient with `b0`.
      exact Set.mem_singleton_iff.mpr <| by
        simpa [b0] using
          shiftedLineSlice_selectorSlope_eq_of_zero_memSubdifferential_unique_active
            hatP F x0 β uStar huStar huStar_unique t d hzero
    · intro hg
      rcases Set.mem_singleton_iff.mp hg with rfl
      -- The selector slope is always an exact subgradient of the unshifted lifted line slice.
      simpa [φLift, b0] using
        lineSliceLiftSelectorMemSubdifferential
          hatP F x0 β uStar huStar t d
  -- Once the exact scalar subdifferential is the singleton `{b0}`, both sign directional
  -- derivatives are bounded above by the corresponding singleton pairings.
  simpa [φLift, b0, h0] using
    directionalDerivativeSigns_le_of_subdifferential_eq_singleton hconv h0 hsub

/-- Helper for Proposition 7.28: once the exact owner-level directional derivative bounds are
available, the unshifted scalar line slice at `0` has singleton subdifferential `{b0}`. -/
lemma lineSliceSubdifferential_eq_singleton_zeroBase_of_directionalDerivativeBounds
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) :
    ∂ (fun α : ℝ ↦
      (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) =
      {inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d} := by
  let φLift : ℝ → WithTop ℝ := fun α ↦
    (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ)
  let b0 : ℝ := inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d
  let h0 : (0 : ℝ) ∈ interior (dom φLift) :=
    supportFunctionApproximation_line_zero_mem_interior_dom hatP F x0 β t d
  have hconv :
      ConvexOn ℝ (dom φLift) (withTopRealPart φLift) := by
    -- Keep the exact lifted line-slice owner while invoking the scalar subgradient squeeze.
    simpa [φLift] using lineSliceLiftConvexOn hatP F x0 β uStar huStar t d
  have hlower :
      b0 ≤ convexDirectionalDerivativeReal φLift h0 (1 : ℝ) ∧
        -b0 ≤ convexDirectionalDerivativeReal φLift h0 (-1 : ℝ) := by
    -- The monotone secant route already gives the lower bounds in both sign directions.
    simpa [φLift, b0, h0] using
      lineSliceDirectionalDerivativeAtZero_lowerBounds_exact
        hatP F x0 β uStar huStar t d
  have hupper :
      convexDirectionalDerivativeReal φLift h0 (1 : ℝ) ≤ b0 ∧
        convexDirectionalDerivativeReal φLift h0 (-1 : ℝ) ≤ -b0 := by
    -- The remaining source-faithful active-hull theorem supplies the complementary upper bounds.
    simpa [φLift, b0, h0] using
      lineSliceDirectionalDerivativeAtZero_upperBounds_of_activeAffineHull
        hatP F x0 β uStar huStar huStar_unique t d
  have hplus :
      convexDirectionalDerivativeReal φLift h0 (1 : ℝ) = b0 := by
    -- The two inequalities in direction `1` identify the exact derivative value.
    exact le_antisymm hupper.1 hlower.1
  have hminus :
      convexDirectionalDerivativeReal φLift h0 (-1 : ℝ) = -b0 := by
    -- The same squeeze in direction `-1` identifies the negative derivative.
    exact le_antisymm hupper.2 hlower.2
  have hb0 :
      b0 ∈ ∂ φLift(0) := by
    -- The selector slope always gives the easy singleton inclusion.
    simpa [φLift, b0] using
      lineSliceLiftSelectorMemSubdifferential
        hatP F x0 β uStar huStar t d
  have hsubset :
      ∂ φLift(0) ⊆ {b0} := by
    intro g hg
    -- Any scalar subgradient is squeezed to the same slope by the two exact directional values.
    exact Set.mem_singleton_iff.mpr <| by
      exact
        subgradient_eq_of_directionalDerivativeSigns_at_zero
          hconv h0 hg hplus hminus
  have hsingletonSub : ({b0} : Set ℝ) ⊆ ∂ φLift(0) := by
    intro g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    exact hb0
  -- The exact owner subdifferential is therefore the singleton `{b0}`.
  simpa [φLift, b0] using Set.Subset.antisymm hsubset hsingletonSub

lemma shiftedLineSliceSubdifferential_subset_activeAffineHullAtZero
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) {g : ℝ} :
    ∂ (fun α : ℝ ↦
      pointwiseSupremumOn (Set.univ : Set hatP)
        (fun τ u ↦
          ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
              τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α)(0) ⊆
      convexHull ℝ
        {h | ∃ u : hatP,
            u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP)
              (fun α u ↦
                ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                    α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) 0 ∧
              h ∈ ∂[Set.univ]
                (fun α : ℝ ↦
                  ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                      α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ))(0)} := by
  -- Route correction: the reverse inclusion now factors through a smaller scalar closure fact.
  -- Once the exact line slice at `0` has singleton subdifferential `{b0}`, the shifted owner at
  -- the same base point also has singleton subdifferential `{b0 - g}`, and the shifted active
  -- hull is already the same singleton.
  have hline :
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) =
        {inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d} := by
    -- Route correction: close the exact singleton through the two-sign directional squeeze, so
    -- the shifted reverse inclusion no longer depends on the shifted zero-subgradient loop.
    simpa using
      lineSliceSubdifferential_eq_singleton_zeroBase_of_directionalDerivativeBounds
        hatP F x0 β uStar huStar huStar_unique t d
  exact
    shiftedLineSliceSubdifferential_subset_activeAffineHullAtZero_of_lineSliceSubdifferential_eq_singleton
      hatP F x0 β uStar huStar huStar_unique t d g hline

/-- Helper for Proposition 7.28: the shifted active affine hull contains `0` exactly when the
shifted selector slope `b0 - g` vanishes. -/
lemma zero_mem_shiftedActiveAffineHullAtZero_iff
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) (g : ℝ) :
    0 ∈
      convexHull ℝ
        {h | ∃ u : hatP,
            u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP)
              (fun α u ↦
                ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                    α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) 0 ∧
                h ∈ ∂[Set.univ]
                  (fun α : ℝ ↦
                    ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                        α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ))(0)} ↔
      inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d - g = 0 := by
  -- Rewrite the shifted active hull to its singleton selector-slope form and read off whether
  -- `0` belongs to that singleton.
  rw [shiftedActiveAffineHullAtZero_eq_singleton_shiftedSelectorSlope
    hatP F x0 β uStar huStar huStar_unique t d g]
  constructor
  · intro h
    simpa [eq_comm] using h
  · intro h
    simpa [eq_comm] using h

/-- Helper for Proposition 7.28: once the shifted selector slope vanishes, the collapsed shifted
active affine hull already contains `0`. -/
lemma zero_mem_convexHull_shiftedActiveAffineSubgradients_at_zero_of_selectorSlope_zero
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) {g : ℝ}
    (hb0g :
      inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d - g = 0) :
    0 ∈
      convexHull ℝ
        {h | ∃ u : hatP,
            u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP)
              (fun α u ↦
                ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                    α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) 0 ∧
              h ∈ ∂[Set.univ]
                (fun α : ℝ ↦
                  ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                      α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ))(0)} := by
  -- Collapse the shifted active hull to `{b0 - g}` and rewrite `hb0g` as membership in that
  -- singleton.
  rw [shiftedActiveAffineHullAtZero_eq_singleton_shiftedSelectorSlope
    hatP F x0 β uStar huStar huStar_unique t d g]
  simpa [eq_comm] using hb0g

/-- Helper for Proposition 7.28: once the base parameter has a unique active maximizer, a zero
shifted subgradient at the base point should already lie in the convex hull of the shifted
affine-slice subgradients active at `0`. -/
lemma zero_mem_convexHull_shiftedActiveAffineSubgradients_at_zero
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) {g : ℝ}
    (hg0 :
      0 ∈
        ∂ (fun α : ℝ ↦
          pointwiseSupremumOn (Set.univ : Set hatP)
            (fun τ u ↦
              ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                  τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α)(0)) :
    0 ∈
      convexHull ℝ
        {h | ∃ u : hatP,
            u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP)
              (fun α u ↦
                ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                    α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) 0 ∧
                h ∈ ∂[Set.univ]
                  (fun α : ℝ ↦
                    ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                        α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ))(0)} := by
  have hmin :
      IsMinOn
        (fun α : ℝ ↦
          Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) - α * g)
        Set.univ
        0 := by
    -- First convert the zero shifted subgradient into the equivalent shifted minimizer
    -- certificate at the base point.
    exact
      (zeroMemSubdifferential_shiftedLineSlice_iff_isMinOn_zero
        hatP F x0 β uStar huStar t d).mp hg0
  -- Reuse the zero-case minimizer-to-active-hull bridge without reopening the shifted singleton
  -- corollary.
  exact
    zero_mem_convexHull_shiftedActiveAffineSubgradients_at_zero_of_isMinOn
      hatP F x0 β uStar huStar huStar_unique t d hmin

/-- Helper for Proposition 7.28: once the shifted owner has zero subgradient at `0`, the shifted
selector slope must vanish because that same zero lies in the collapsed shifted active hull. -/
lemma zeroShiftedSelectorSlope_of_zeroMemSubdifferential
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) {g : ℝ}
    (hg0 :
      0 ∈
        ∂ (fun α : ℝ ↦
          pointwiseSupremumOn (Set.univ : Set hatP)
            (fun τ u ↦
              ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                  τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α)(0)) :
    inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d - g = 0 := by
  have hhull :
      0 ∈
        convexHull ℝ
          {h | ∃ u : hatP,
              u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP)
                (fun α u ↦
                  ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                      α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) 0 ∧
                h ∈ ∂[Set.univ]
                  (fun α : ℝ ↦
                    ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                        α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ))(0)} := by
    -- First move the zero subgradient into the shifted active affine hull.
    exact
      zero_mem_convexHull_shiftedActiveAffineSubgradients_at_zero
        hatP F x0 β uStar huStar huStar_unique t d hg0
  -- The shifted active hull is already known to be the singleton `{b0 - g}`.
  rwa [zero_mem_shiftedActiveAffineHullAtZero_iff
    hatP F x0 β uStar huStar huStar_unique t d g] at hhull

/-- Helper for Proposition 7.28: if the shifted owner has zero subgradient at `0`, then the
shifted selector slope must vanish. This auxiliary form isolates the remaining zero-case blocker
before the arbitrary-shift transport step. -/
lemma zeroSubgradientForcesZeroShiftedSelectorSlopeAux
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) {g : ℝ}
    (hg0 :
      0 ∈
        ∂ (fun α : ℝ ↦
          pointwiseSupremumOn (Set.univ : Set hatP)
            (fun τ u ↦
              ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                  τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α)(0)) :
    inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d - g = 0 := by
  -- Reuse the isolated scalar zero-case collapse directly, without routing back through the hull
  -- membership theorem.
  simpa using
    zeroShiftedSelectorSlope_of_zeroMemSubdifferential
      hatP F x0 β uStar huStar huStar_unique t d hg0

/-- Helper for Proposition 7.28: once the base parameter has a unique active maximizer, every
scalar subgradient of the shifted owner at `0` should already equal the shifted selector slope
`b0 - g`. -/
lemma shiftedLineSliceSubgradient_eq_selectorSlope_at_zero
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) {g h : ℝ}
    (hh :
      h ∈
        ∂ (fun α : ℝ ↦
          pointwiseSupremumOn (Set.univ : Set hatP)
            (fun τ u ↦
              ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                  τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α)(0)) :
    h = inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d - g := by
  let k : ℝ := h + g
  have hk :
      k ∈
        ∂ (fun α : ℝ ↦
          (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) := by
    -- Undo the affine tilt so the arbitrary shifted subgradient becomes an exact line-slice
    -- subgradient.
    simpa [k] using
      memSubdifferential_lineSlice_of_memSubdifferential_shiftedLineSlice
        hatP F x0 β uStar huStar t d hh
  have hzero :
      0 ∈
        ∂ (fun α : ℝ ↦
          pointwiseSupremumOn (Set.univ : Set hatP)
            (fun τ u ↦
              ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                  τ * (inner ℝ (u.1 - x0) d - k) : ℝ) : WithTop ℝ)) α)(0) := by
    -- Recenter the exact subgradient `k` so the shifted owner has zero subgradient at `0`.
    simpa [k] using
      zeroMemSubdifferential_shiftedLineSlice_of_memSubdifferential
        hatP F x0 β uStar huStar t d hk
  have hk_eq :
      inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d - k = 0 := by
    -- The remaining blocker is now isolated in the zero-case shifted-owner collapse.
    simpa [k] using
      zeroSubgradientForcesZeroShiftedSelectorSlopeAux
        hatP F x0 β uStar huStar huStar_unique t d hzero
  -- Expand `k = h + g` to recover the desired shifted selector slope formula for `h`.
  linarith

/-- Helper for Proposition 7.28: a zero subgradient of the shifted line-slice owner at `0`
forces the shifted selector slope to vanish. -/
lemma zero_subgradient_of_shifted_line_slice_forces_zero_shifted_selector_slope
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) {g : ℝ}
    (hg0 :
      0 ∈
        ∂ (fun α : ℝ ↦
          pointwiseSupremumOn (Set.univ : Set hatP)
            (fun τ u ↦
              ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                  τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α)(0)) :
    inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d - g = 0 := by
  -- Reuse the isolated zero-case auxiliary theorem so downstream exact-line-slice wrappers no
  -- longer depend on the arbitrary-shift transport theorem.
  simpa using
    zeroSubgradientForcesZeroShiftedSelectorSlopeAux
      hatP F x0 β uStar huStar huStar_unique t d hg0

/-- Helper for Proposition 7.28: the exact lifted line slice should have directional derivatives
at `0` in directions `1` and `-1` bounded above by the selector slope and its negative. -/
lemma shiftedLineSlice_selectorSlope_eq_of_zero_memSubdifferential
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) {g : ℝ}
    (hg0 :
      0 ∈
        ∂ (fun α : ℝ ↦
          pointwiseSupremumOn (Set.univ : Set hatP)
            (fun τ u ↦
              ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                  τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α)(0)) :
    g = inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d := by
  let b0 : ℝ := inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d
  have hb0g :
      b0 - g = 0 := by
    -- Route correction: the closing theorem now uses the smaller scalar shifted-owner collapse
    -- instead of the stronger convex-hull reverse inclusion.
    simpa [b0] using
      zero_subgradient_of_shifted_line_slice_forces_zero_shifted_selector_slope
        hatP F x0 β uStar huStar huStar_unique t d hg0
  linarith

/-- Helper for Proposition 7.28: once the shifted zero-subgradient collapse is known, the exact
lifted line slice already has singleton subdifferential `{b0}` at `0`. -/
lemma lineSliceSubdifferential_eq_singleton_at_zero_via_shifted_saddle
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) :
    let φLift : ℝ → WithTop ℝ := fun α ↦
      (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ)
    let b0 : ℝ := inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d
    ∂ φLift(0) = {b0} := by
  dsimp
  ext g
  constructor
  · intro hg
    have hzero :
        0 ∈
          ∂ (fun α : ℝ ↦
            pointwiseSupremumOn (Set.univ : Set hatP)
              (fun τ u ↦
                ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                    τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α)(0) := by
      -- Subtract the affine support line `α ↦ α * g` so the remaining shifted owner has
      -- zero subgradient at the base point.
      exact
        zeroMemSubdifferential_shiftedLineSlice_of_memSubdifferential
          hatP F x0 β uStar huStar t d hg
    -- The shifted zero-subgradient collapse identifies every exact scalar subgradient with `b0`.
    exact Set.mem_singleton_iff.mpr <| by
      simpa using
        shiftedLineSlice_selectorSlope_eq_of_zero_memSubdifferential
          hatP F x0 β uStar huStar huStar_unique t d hzero
  · intro hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    -- The selector slope is always an exact subgradient of the unshifted lifted line slice.
    exact
      lineSliceLiftSelectorMemSubdifferential
        hatP F x0 β uStar huStar t d

/-- Helper for Proposition 7.28: the shifted-saddle singleton exact subdifferential already gives
 differentiability of the scalar line slice at `0` with derivative equal to the selector slope. -/
lemma lineSliceHasDerivAt_zero_via_shiftedSaddle
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) :
    HasDerivAt
      (fun α : ℝ ↦
        Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)))
      (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)
      0 := by
  let φ : ℝ → ℝ := fun α ↦
    Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d))
  let b0 : ℝ := inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d
  have hconv : ConvexOn ℝ Set.univ φ :=
    supportFunctionApproximation_line_convexOn_univ_of_selector
      hatP F x0 β uStar huStar t d
  have hsub : ∂ (fun α : ℝ ↦ (φ α : WithTop ℝ))(0) = {b0} := by
    -- Reuse the earlier shifted-saddle singleton formula for the exact line slice.
    simpa [φ, b0] using
      lineSliceSubdifferential_eq_singleton_at_zero_via_shifted_saddle
        hatP F x0 β uStar huStar huStar_unique t d
  have hgrad : HasGradientAt φ b0 0 := by
    -- Convexity plus the singleton subdifferential identifies the scalar gradient.
    exact hasGradientAt_of_convexOn_univ_subdifferential_eq_singleton hconv hsub
  -- On `ℝ`, the scalar gradient is the ordinary derivative.
  simpa [φ, b0] using hgrad.hasDerivAt

/-- Helper for Proposition 7.28: the exact lifted line slice should have directional derivatives
at `0` in directions `1` and `-1` bounded above by the selector slope and its negative. -/
lemma lineSliceDirectionalDerivativeAtZero_supportBound
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) :
    let φLift : ℝ → WithTop ℝ := fun α ↦
      (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ)
    let b0 : ℝ := inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d
    let h0 : (0 : ℝ) ∈ interior (dom φLift) :=
      supportFunctionApproximation_line_zero_mem_interior_dom hatP F x0 β t d
    convexDirectionalDerivativeReal φLift h0 (1 : ℝ) ≤ b0 ∧
      convexDirectionalDerivativeReal φLift h0 (-1 : ℝ) ≤ -b0 := by
  let φLift : ℝ → WithTop ℝ := fun α ↦
    (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ)
  let b0 : ℝ := inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d
  let h0 : (0 : ℝ) ∈ interior (dom φLift) :=
    supportFunctionApproximation_line_zero_mem_interior_dom hatP F x0 β t d
  have hconv :
      ConvexOn ℝ (dom φLift) (withTopRealPart φLift) := by
    -- Keep the exact lifted line-slice owner while invoking the Chapter 3 directional-derivative
    -- maximization theorem.
    simpa [φLift] using lineSliceLiftConvexOn hatP F x0 β uStar huStar t d
  have hsub :
      ∂ φLift(0) = {b0} := by
    -- First collapse the exact scalar subdifferential to the singleton selector slope.
    simpa [φLift, b0] using
      lineSliceSubdifferential_eq_singleton_at_zero_via_shifted_saddle
        hatP F x0 β uStar huStar huStar_unique t d
  -- The singleton exact subdifferential immediately identifies the two sign directional
  -- derivatives.
  simpa [φLift, b0, h0] using
    directionalDerivativeSigns_le_of_subdifferential_eq_singleton hconv h0 hsub

/-- Helper for Proposition 7.28: once the singleton exact subdifferential is available, the
earlier exact upper-bound package is just the downstream support-bound theorem. -/
lemma lineSliceDirectionalDerivativeAtZero_upperBounds_exact
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) :
    let φLift : ℝ → WithTop ℝ := fun α ↦
      (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ)
    let b0 : ℝ := inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d
    let h0 : (0 : ℝ) ∈ interior (dom φLift) :=
      supportFunctionApproximation_line_zero_mem_interior_dom hatP F x0 β t d
    convexDirectionalDerivativeReal φLift h0 (1 : ℝ) ≤ b0 ∧
      convexDirectionalDerivativeReal φLift h0 (-1 : ℝ) ≤ -b0 := by
  -- Route correction: this theorem is now the downstream wrapper for the earlier active-hull
  -- upper-bound step, rather than a consequence of the circular shifted-singleton route.
  simpa using
    lineSliceDirectionalDerivativeAtZero_upperBounds_of_activeAffineHull
      hatP F x0 β uStar huStar huStar_unique t d

/-- Helper for Proposition 7.28: every scalar subgradient of the exact lifted line slice at `0`
already equals the selector slope, without routing through the later one-sided limit theorem. -/
lemma lineSliceSubgradient_eq_selectorSlope_at_zero_direct
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) {g : ℝ}
    (hg : g ∈
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0)) :
    g = inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d := by
  let φLift : ℝ → WithTop ℝ := fun α ↦
    (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ)
  let b0 : ℝ := inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d
  have hsub :
      ∂ φLift(0) = {b0} := by
    -- Route correction: the direct scalar collapse now comes from the singleton exact
    -- subdifferential, not from rebuilding the directional-derivative sandwich.
    simpa [φLift, b0] using
      lineSliceSubdifferential_eq_singleton_at_zero_via_shifted_saddle
        hatP F x0 β uStar huStar huStar_unique t d
  -- Rewriting the exact subdifferential by the singleton `{b0}` identifies the candidate.
  rw [hsub] at hg
  exact Set.mem_singleton_iff.mp hg

/-- Helper for Proposition 7.28: the exact scalar line slice at the base parameter `0` should have
singleton subdifferential given by the selector slope. -/
lemma lineSliceSubdifferential_subset_activeAffineHullAtZero
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) :
    ∂ (fun α : ℝ ↦
      (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) ⊆
      convexHull ℝ
        {g | ∃ u : hatP,
            u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP)
              (fun α u ↦
                ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                    α * inner ℝ (u.1 - x0) d : ℝ) : WithTop ℝ)) 0 ∧
              g ∈ ∂[Set.univ]
                (fun α : ℝ ↦
                  ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                      α * inner ℝ (u.1 - x0) d : ℝ) : WithTop ℝ))(0)} := by
  intro g hg
  let b0 : ℝ := inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d
  have hg_eq : g = b0 := by
    -- Collapse the scalar subgradient directly, without routing through the later limit theorem.
    simpa [b0] using
      lineSliceSubgradient_eq_selectorSlope_at_zero_direct
        hatP F x0 β uStar huStar huStar_unique t d hg
  have hactiveHull :
      convexHull ℝ
        {g | ∃ u : hatP,
            u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP)
              (fun α u ↦
                ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                    α * inner ℝ (u.1 - x0) d : ℝ) : WithTop ℝ)) 0 ∧
              g ∈ ∂[Set.univ]
                (fun α : ℝ ↦
                  ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
                      α * inner ℝ (u.1 - x0) d : ℝ) : WithTop ℝ))(0)} = {b0} := by
    -- The active affine-hull package already collapses to the selector slope singleton.
    simpa [b0] using
      activeAffineHullAtZero_eq_singleton_selectorSlope
        hatP F x0 β uStar huStar huStar_unique t d
  -- Rewrite the target hull to the singleton `{b0}` and discharge membership by the collapse.
  rw [hactiveHull]
  exact Set.mem_singleton_iff.mpr hg_eq

/-- Helper for Proposition 7.28: the exact scalar line slice at the base parameter `0` should have
singleton subdifferential given by the selector slope. -/
lemma lineSliceSubdifferential_eq_singleton_zeroBase_of_uniqueArgmax
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) :
    ∂ (fun α : ℝ ↦
      (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) =
      {inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d} := by
  -- Route correction: the canonical zero-base singleton theorem now reuses the earlier
  -- directional-derivative squeeze and no longer closes through the shifted saddle loop.
  simpa using
    lineSliceSubdifferential_eq_singleton_zeroBase_of_directionalDerivativeBounds
      hatP F x0 β uStar huStar huStar_unique t d

/-- Helper for Proposition 7.28: once the exact line slice at `0` has singleton subdifferential,
the shifted directional derivatives there are bounded above by the shifted selector slope and its
negative. -/
-- Route correction: this theorem is now a downstream corollary of the canonical exact singleton
-- theorem `lineSliceSubdifferential_eq_singleton_zeroBase_of_uniqueArgmax`, so it no longer
-- participates in the earlier zero-subgradient cycle.
lemma shiftedLineSliceDirectionalDerivativeSigns_le_shiftedSelectorSlope
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) {g : ℝ} :
    let ψLift : ℝ → WithTop ℝ := fun α ↦
      pointwiseSupremumOn (Set.univ : Set hatP)
        (fun τ u ↦
          ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
              τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α
    let b0 : ℝ := inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d - g
    let h0 : (0 : ℝ) ∈ interior (dom ψLift) :=
      shiftedLineSlice_zero_mem_interior_dom hatP F x0 β uStar huStar t d g
    convexDirectionalDerivativeReal ψLift h0 (1 : ℝ) ≤ b0 ∧
      convexDirectionalDerivativeReal ψLift h0 (-1 : ℝ) ≤ -b0 := by
  let ψLift : ℝ → WithTop ℝ := fun α ↦
    pointwiseSupremumOn (Set.univ : Set hatP)
      (fun τ u ↦
        ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
            τ * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) α
  let b0 : ℝ := inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d - g
  let h0 : (0 : ℝ) ∈ interior (dom ψLift) :=
    shiftedLineSlice_zero_mem_interior_dom hatP F x0 β uStar huStar t d g
  have hline :
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) =
        {inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d} := by
    -- Reuse the canonical exact singleton theorem before transporting across the affine tilt.
    simpa using
      lineSliceSubdifferential_eq_singleton_zeroBase_of_uniqueArgmax
        hatP F x0 β uStar huStar huStar_unique t d
  have hsub :
      ∂ ψLift(0) = {b0} := by
    -- Undo the affine tilt once to transport the exact singleton to the shifted owner.
    exact
      shiftedLineSliceSubdifferential_eq_singleton_of_lineSliceSubdifferential_eq_singleton
        hatP F x0 β uStar huStar t d g hline
  -- The generic singleton-subdifferential theorem now gives the two shifted sign bounds.
  simpa [ψLift, b0, h0] using
    shiftedLineSliceDirectionalDerivativeSigns_le_of_subdifferential_eq_singleton
      hatP F x0 β uStar huStar t d g hsub

/-- Helper for Proposition 7.28: once the exact line-slice subdifferential at `0` is singleton,
the scalar line slice is differentiable there with derivative given by the selector slope. -/
lemma lineSliceHasDerivAt_zero
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) :
    HasDerivAt
      (fun α : ℝ ↦
        Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)))
      (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)
      0 := by
  let φ : ℝ → ℝ := fun α ↦
    Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d))
  let b0 : ℝ := inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d
  have hconv : ConvexOn ℝ Set.univ φ :=
    supportFunctionApproximation_line_convexOn_univ_of_selector
      hatP F x0 β uStar huStar t d
  have hsub : ∂ (fun α : ℝ ↦ (φ α : WithTop ℝ))(0) = {b0} := by
    -- Read the scalar singleton theorem back in the real-valued line-slice spelling.
    simpa [φ, b0] using
      lineSliceSubdifferential_eq_singleton_zeroBase_of_uniqueArgmax
        hatP F x0 β uStar huStar huStar_unique t d
  have hgrad : HasGradientAt φ b0 0 := by
    -- Convexity plus the singleton subdifferential identifies the scalar gradient.
    exact hasGradientAt_of_convexOn_univ_subdifferential_eq_singleton hconv hsub
  -- On `ℝ`, the scalar gradient is the ordinary derivative.
  simpa [φ, b0] using hgrad.hasDerivAt

/-- Helper for Proposition 7.28: the remaining scalar closure is exactly the stability of the
selector slope along the exact line as the parameter returns to `0`. -/
lemma lineSliceFutureSelectorSlope_tendsto_baseSlope
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) :
    Tendsto
      (fun τ : ℝ ↦
        inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + τ • d)) - x0) d)
      (𝓝[>] (0 : ℝ))
      (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)) := by
  let φ : ℝ → ℝ := fun α ↦
    Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d))
  let futureSlope : ℝ → ℝ := fun τ ↦
    inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + τ • d)) - x0) d
  let rightSecant : ℝ → ℝ := fun τ ↦ (φ τ - φ 0) / τ
  have hderiv0 :
      HasDerivAt φ (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d) 0 := by
    -- Reuse the restored scalar derivative at the base point.
    simpa [φ] using
      lineSliceHasDerivAt_zero
        hatP F x0 β uStar huStar huStar_unique t d
  have hrightSecant :
      Tendsto rightSecant (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)) := by
    -- The derivative at `0` is exactly the limit of forward secants.
    simpa [rightSecant, div_eq_mul_inv, slope_fun_def_field, mul_comm, mul_left_comm, mul_assoc]
      using
      hderiv0.tendsto_slope_zero_right
  have htwo :
      Tendsto (fun τ : ℝ ↦ (2 : ℝ) * τ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    -- Positive scaling preserves the right-neighborhood filter at `0`.
    have htwo' :
        Tendsto (fun τ : ℝ ↦ (2 : ℝ) * τ) (𝓝[>] (0 : ℝ))
          (𝓝[>] ((2 : ℝ) * 0)) := by
      exact
        Filter.TendstoNhdsWithinIoi.const_mul
          (b := (2 : ℝ)) (c := (0 : ℝ)) (f := fun τ : ℝ ↦ τ)
          (by norm_num)
          (tendsto_id : Tendsto (fun τ : ℝ ↦ τ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)))
    simpa using htwo'
  have hrightSecantTwo :
      Tendsto (fun τ : ℝ ↦ rightSecant ((2 : ℝ) * τ)) (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)) := by
    -- Reindex the forward secants by `τ ↦ 2τ`.
    exact hrightSecant.comp htwo
  have hfutureUpper :
      Tendsto (fun τ : ℝ ↦ 2 * rightSecant (2 * τ) - rightSecant τ) (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)) := by
    -- Adjacent forward secants collapse to the same base slope.
    have htwoConst : Tendsto (fun _ : ℝ ↦ (2 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (2 : ℝ)) :=
      tendsto_const_nhds
    convert (htwoConst.mul hrightSecantTwo).sub hrightSecant using 2 <;> ring
  have hfutureLowerBound :
      ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
        inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d ≤ futureSlope τ := by
    -- Monotonicity of selector pairings places every future slope above the base slope.
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    simpa [futureSlope, zero_smul] using
      supportFunctionApproximation_line_selectorPairing_mono_of_unique_argmax
        hatP F x0 β uStar huStar t d (α := 0) (β' := τ) hτ.le
  have hfutureUpperBound :
      ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
        futureSlope τ ≤ 2 * rightSecant (2 * τ) - rightSecant τ := by
    -- Compare the active slope at `τ` to the secant over `[τ, 2τ]`, then rewrite that secant
    -- through the two base-point secants.
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτpos : 0 < τ := hτ
    have hsecantRaw :=
      (supportFunctionApproximation_line_secantQuotient_bounds_of_unique_argmax
        hatP F x0 β uStar huStar t d (α := τ) (β' := 2 * τ) (by linarith [hτpos])).1
    have hsecant :
        futureSlope τ ≤ (φ (2 * τ) - φ τ) / τ := by
      simpa [futureSlope, φ, two_smul, show 2 * τ - τ = τ by ring] using hsecantRaw
    have hrepack :
        (φ (2 * τ) - φ τ) / τ = 2 * rightSecant (2 * τ) - rightSecant τ := by
      dsimp [rightSecant]
      field_simp [hτpos.ne']
      ring
    simpa [hrepack] using hsecant
  -- Squeeze the future selector slopes between the constant base slope and the adjacent secants.
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hfutureUpper hfutureLowerBound hfutureUpperBound

/-- Helper for Proposition 7.28: the backward selector slopes along the exact line converge back
to the base selector slope. -/
lemma lineSlicePastSelectorSlope_tendsto_baseSlope
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) :
    Tendsto
      (fun τ : ℝ ↦
        inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t - τ • d)) - x0) d)
      (𝓝[>] (0 : ℝ))
      (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)) := by
  let φ : ℝ → ℝ := fun α ↦
    Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d))
  let pastSlope : ℝ → ℝ := fun τ ↦
    inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t - τ • d)) - x0) d
  let leftSecant : ℝ → ℝ := fun τ ↦ (φ (-τ) - φ 0) / (-τ)
  have hderiv0 :
      HasDerivAt φ (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d) 0 := by
    -- Reuse the restored scalar derivative at the base point.
    simpa [φ] using
      lineSliceHasDerivAt_zero
        hatP F x0 β uStar huStar huStar_unique t d
  have hleftRaw :
      Tendsto (fun α : ℝ ↦ (φ α - φ 0) / α) (𝓝[<] (0 : ℝ))
        (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)) := by
    -- The same derivative controls the left secants.
    simpa [div_eq_mul_inv, slope_fun_def_field, mul_comm, mul_left_comm, mul_assoc] using
      hderiv0.tendsto_slope_zero_left
  have hneg :
      Tendsto (fun τ : ℝ ↦ -τ) (𝓝[>] (0 : ℝ)) (𝓝[<] (0 : ℝ)) := by
    have hneg' :
        Tendsto Neg.neg (𝓝[>] (0 : ℝ)) (𝓝[<] (-(0 : ℝ))) :=
      tendsto_neg_nhdsGT
    simpa using hneg'
  have hleftSecant :
      Tendsto leftSecant (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)) := by
    -- Pull the left-slope limit back to positive steps by the change of variables `α = -τ`.
    simpa [leftSecant] using hleftRaw.comp hneg
  have htwo :
      Tendsto (fun τ : ℝ ↦ (2 : ℝ) * τ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    -- Positive scaling preserves the right-neighborhood filter at `0`.
    have htwo' :
        Tendsto (fun τ : ℝ ↦ (2 : ℝ) * τ) (𝓝[>] (0 : ℝ))
          (𝓝[>] ((2 : ℝ) * 0)) := by
      exact
        Filter.TendstoNhdsWithinIoi.const_mul
          (b := (2 : ℝ)) (c := (0 : ℝ)) (f := fun τ : ℝ ↦ τ)
          (by norm_num)
          (tendsto_id : Tendsto (fun τ : ℝ ↦ τ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)))
    simpa using htwo'
  have hleftSecantTwo :
      Tendsto (fun τ : ℝ ↦ leftSecant ((2 : ℝ) * τ)) (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)) := by
    -- Reindex the backward secants by `τ ↦ 2τ`.
    exact hleftSecant.comp htwo
  have hpastLower :
      Tendsto (fun τ : ℝ ↦ 2 * leftSecant (2 * τ) - leftSecant τ) (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)) := by
    -- Adjacent backward secants collapse to the same base slope.
    have htwoConst : Tendsto (fun _ : ℝ ↦ (2 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (2 : ℝ)) :=
      tendsto_const_nhds
    convert (htwoConst.mul hleftSecantTwo).sub hleftSecant using 2 <;> ring
  have hpastLowerBound :
      ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
        2 * leftSecant (2 * τ) - leftSecant τ ≤ pastSlope τ := by
    -- Compare the backward active slope to the secant over `[-2τ, -τ]`, then rewrite that secant
    -- by the base-point backward secants.
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτpos : 0 < τ := hτ
    have hsecantRaw :=
      (supportFunctionApproximation_line_secantQuotient_bounds_of_unique_argmax
        hatP F x0 β uStar huStar t d
        (α := -(2 * τ)) (β' := -τ) (by linarith [hτpos])).2
    have hsecant :
        (φ (-τ) - φ (-(2 * τ))) / τ ≤ pastSlope τ := by
      simpa [pastSlope, φ, sub_eq_add_neg, two_smul,
        show -τ - -(2 * τ) = τ by ring,
        show -τ + 2 * τ = τ by ring] using hsecantRaw
    have hrepack :
        (φ (-τ) - φ (-(2 * τ))) / τ = 2 * leftSecant (2 * τ) - leftSecant τ := by
      dsimp [leftSecant]
      field_simp [hτpos.ne']
      ring
    simpa [hrepack] using hsecant
  have hpastUpperBound :
      ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
        pastSlope τ ≤ inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d := by
    -- The past selector slopes stay below the base slope by the same monotonicity.
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτpos : 0 < τ := hτ
    simpa [pastSlope, zero_smul, sub_eq_add_neg] using
      supportFunctionApproximation_line_selectorPairing_mono_of_unique_argmax
        hatP F x0 β uStar huStar t d (α := -τ) (β' := 0) (by linarith [hτpos])
  -- Squeeze the past selector slopes between the adjacent backward secants and the same constant.
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hpastLower tendsto_const_nhds hpastLowerBound hpastUpperBound

/-- Helper for Proposition 7.28: the remaining scalar closure is exactly the stability of the
selector slope along the exact line as the parameter returns to `0`. -/
lemma lineSliceSelectorSlope_tendsto_baseSlope
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) :
    let b0 : ℝ := inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d
    Tendsto
        (fun τ : ℝ ↦
          inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + τ • d)) - x0) d)
        (𝓝[>] (0 : ℝ))
        (𝓝 b0) ∧
    Tendsto
        (fun τ : ℝ ↦
          inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t - τ • d)) - x0) d)
        (𝓝[>] (0 : ℝ))
        (𝓝 b0) := by
  dsimp
  constructor
  · simpa using
      lineSliceFutureSelectorSlope_tendsto_baseSlope
        hatP F x0 β uStar huStar huStar_unique t d
  · simpa using
      lineSlicePastSelectorSlope_tendsto_baseSlope
        hatP F x0 β uStar huStar huStar_unique t d

/-- Helper for Proposition 7.28: once the exact scalar line slice is differentiable at `0`, the
earlier duplicated selector-slope limit statement is just a downstream spelling of the canonical
limit theorem. -/
lemma lineSliceSelectorSlope_tendsto_baseSlope_atZero
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) :
    Tendsto
        (fun τ : ℝ ↦
          inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + τ • d)) - x0) d)
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)) ∧
      Tendsto
        (fun τ : ℝ ↦
          inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t - τ • d)) - x0) d)
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)) := by
  -- The duplicated early limit statement is now a direct corollary of the canonical later owner.
  simpa using
    lineSliceSelectorSlope_tendsto_baseSlope
      hatP F x0 β uStar huStar huStar_unique t d

/-- Helper for Proposition 7.28: once the nearby selector slopes converge back to the base slope
from both sides, any scalar subgradient at `0` must equal that base selector slope. -/
lemma lineSliceSubgradient_eq_selectorSlope_of_tendsto
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (t d : E) {g : ℝ}
    (hfuture :
      Tendsto
        (fun τ : ℝ ↦
          inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t + τ • d)) - x0) d)
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)))
    (hpast :
      Tendsto
        (fun τ : ℝ ↦
          inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) (t - τ • d)) - x0) d)
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)))
    (hg : g ∈
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0)) :
    g = inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d := by
  -- Reuse the earlier limit-to-singleton bridge in the same owner spelling.
  exact
    lineSliceSubgradient_eq_selectorSlope_at_zero_of_limits
      hatP F x0 β uStar huStar t d hfuture hpast hg

/-- Helper for Proposition 7.28: the remaining scalar reverse inclusion should identify every
subgradient of the exact lifted line slice at `0` with the selector slope at the base point. -/
lemma lineSliceDirectionalDerivativeOriginModel_eq_affine
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) :
    let φLift : ℝ → WithTop ℝ := fun α ↦
      (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ)
    let b0 : ℝ := inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d
    let h0 : (0 : ℝ) ∈ interior (dom φLift) :=
      supportFunctionApproximation_line_zero_mem_interior_dom hatP F x0 β t d
    ∀ p : ℝ, convexDirectionalDerivativeReal φLift h0 p = p * b0 := by
  dsimp
  let φ : ℝ → ℝ := fun α ↦
    Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d))
  have hconv :
      ConvexOn ℝ
        (dom (fun α : ℝ ↦ ((φ α : ℝ) : WithTop ℝ)))
        (withTopRealPart (fun α : ℝ ↦ ((φ α : ℝ) : WithTop ℝ))) := by
    -- Keep the lifted line slice in the exact owner spelling before invoking Chapter 3.
    simpa [φ] using lineSliceLiftConvexOn hatP F x0 β uStar huStar t d
  intro p
  have howner :
      HasDirectionalDerivAt
        (withTopToEReal ∘ fun α : ℝ ↦ ((φ α : ℝ) : WithTop ℝ))
        0 p
        (convexDirectionalDerivativeReal
          (fun α : ℝ ↦ ((φ α : ℝ) : WithTop ℝ))
          (supportFunctionApproximation_line_zero_mem_interior_dom hatP F x0 β t d) p) := by
    -- The Chapter 3 owner identifies the directional derivative of the lifted scalar slice.
    exact
      convexDirectionalDerivative_toReal_hasDirectionalDerivAt
        hconv
        (supportFunctionApproximation_line_zero_mem_interior_dom hatP F x0 β t d)
        p
  have hsliceDeriv :
      HasDerivAt (fun α : ℝ ↦ φ (α * p))
        (p * inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d) 0 := by
    have hbase :
        HasDerivAt
          (fun α : ℝ ↦
            Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)))
          (inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d)
          (p * 0) := by
      -- Rewrite the zero-base derivative so its base point matches the image of `α ↦ α * p`.
      simpa [zero_mul] using
        lineSliceHasDerivAt_zero hatP F x0 β uStar huStar huStar_unique t d
    have hscale : HasDerivAt (fun α : ℝ ↦ p * α) p 0 := by
      simpa [mul_comm] using (hasDerivAt_id 0).const_mul p
    -- Compose the scalar derivative at `0` with the direction scaling `α ↦ α * p`.
    have hcomp := hbase.comp 0 hscale
    convert hcomp using 1
    · ext α
      simp [φ, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    · ring
  have hmodel :
      HasDirectionalDerivAt
        (withTopToEReal ∘ fun α : ℝ ↦ ((φ α : ℝ) : WithTop ℝ))
        0 p
        (p * inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d) := by
    refine ⟨?_, ?_, ?_⟩
    · -- The lifted scalar slice is finite at the base point `0`.
      exact mem_dom_withTopToEReal_comp_of_mem_dom (by
        change ((((φ 0 : ℝ) : WithTop ℝ) < ⊤))
        exact WithTop.coe_lt_top _)
    · -- The same finiteness is automatic all along the real ray.
      filter_upwards with α
      exact mem_dom_withTopToEReal_comp_of_mem_dom (by
        change ((((φ (0 + α • p) : ℝ) : WithTop ℝ) < ⊤))
        exact WithTop.coe_lt_top _)
    · have hslice :
          (fun α : ℝ ↦
            extendedRealRealPart
              (withTopToEReal ∘ fun a : ℝ ↦ ((φ a : ℝ) : WithTop ℝ))
              (0 + α • p)) =
            fun α : ℝ ↦ φ (α * p) := by
        -- Normalize the directional slice of the lifted owner back to the scalar line slice.
        funext α
        calc
          extendedRealRealPart
              (withTopToEReal ∘ fun a : ℝ ↦ ((φ a : ℝ) : WithTop ℝ))
              (0 + α • p)
              =
              withTopRealPart
                (fun a : ℝ ↦ ((φ a : ℝ) : WithTop ℝ))
                (0 + α • p) := by
                  simpa [extendedRealRealPart, Function.comp] using
                    (withTopToEReal_toReal_eq_withTopRealPart
                      (f := fun a : ℝ ↦ ((φ a : ℝ) : WithTop ℝ))
                      (z := 0 + α • p))
          _ = φ (0 + α • p) := by
                simp [withTopRealPart]
          _ = φ (α * p) := by
                simp [smul_eq_mul]
      rw [hslice]
      exact hsliceDeriv.hasDerivWithinAt
  -- Uniqueness of the finite directional derivative identifies the owner with the affine model.
  exact HasDirectionalDerivAt.unique howner hmodel

/-- Helper for Proposition 7.28: once the exact line-slice directional derivatives are known to
follow the affine model `p ↦ p * b0`, the one-sided upper bounds are immediate by specializing to
`p = 1` and `p = -1`. -/
lemma lineSliceDirectionalDerivativeAtZero_bounds_of_affineModel
    {φLift : ℝ → WithTop ℝ} {b0 : ℝ}
    {h0 : (0 : ℝ) ∈ interior (dom φLift)}
    (hmodel : ∀ p : ℝ, convexDirectionalDerivativeReal φLift h0 p = p * b0) :
    convexDirectionalDerivativeReal φLift h0 (1 : ℝ) ≤ b0 ∧
      convexDirectionalDerivativeReal φLift h0 (-1 : ℝ) ≤ -b0 := by
  constructor
  · -- Specializing the affine model at `p = 1` gives the desired upper bound immediately.
    simpa using (hmodel 1).le
  · -- The same specialization at `p = -1` yields the negative-direction bound.
    simpa using (hmodel (-1)).le

/-- Helper for Proposition 7.28: the remaining scalar reverse inclusion should identify every
subgradient of the exact lifted line slice at `0` with the selector slope at the base point. -/
lemma lineSliceSubgradient_eq_selectorSlope_of_memSubdifferential_owner
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) {g : ℝ}
    (hg : g ∈
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0)) :
    g = inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d := by
  have hsingleton :
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) =
        {inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d} := by
    -- Reuse the earlier zero-base singleton theorem in the exact owner spelling.
    simpa using
      lineSliceSubdifferential_eq_singleton_zeroBase_of_uniqueArgmax
        hatP F x0 β uStar huStar huStar_unique t d
  rw [hsingleton] at hg
  exact Set.mem_singleton_iff.mp hg

/-- Helper for Proposition 7.28: the exact lifted line slice should have directional derivatives
in directions `1` and `-1` bounded above by the selector slope and its negative. -/
lemma lineSliceDirectionalDerivativeAtZero_upperBounds
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) :
    let φLift : ℝ → WithTop ℝ := fun α ↦
      (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ)
    let b0 : ℝ := inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d
    let h0 : (0 : ℝ) ∈ interior (dom φLift) :=
      supportFunctionApproximation_line_zero_mem_interior_dom hatP F x0 β t d
    convexDirectionalDerivativeReal φLift h0 (1 : ℝ) ≤ b0 ∧
      convexDirectionalDerivativeReal φLift h0 (-1 : ℝ) ≤ -b0 := by
  -- Route correction: keep the support-bound wrapper downstream of the affine directional model.
  exact
    lineSliceDirectionalDerivativeAtZero_bounds_of_affineModel
      (lineSliceDirectionalDerivativeOriginModel_eq_affine
        hatP F x0 β uStar huStar huStar_unique t d)

/-- Helper for Proposition 7.28: once the missing directional upper bounds are available, the
exact lifted line slice has directional derivatives `b0` and `-b0` at `0` in directions `1` and
`-1`. -/
lemma lineSliceDirectionalDerivativeAtZero_eq_selectorSlope
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) :
    let φLift : ℝ → WithTop ℝ := fun α ↦
      (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ)
    let b0 : ℝ := inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d
    let h0 : (0 : ℝ) ∈ interior (dom φLift) :=
      supportFunctionApproximation_line_zero_mem_interior_dom hatP F x0 β t d
    convexDirectionalDerivativeReal φLift h0 (1 : ℝ) = b0 ∧
      convexDirectionalDerivativeReal φLift h0 (-1 : ℝ) = -b0 := by
  have hmodel :=
    lineSliceDirectionalDerivativeOriginModel_eq_affine
      hatP F x0 β uStar huStar huStar_unique t d
  constructor
  · -- The restored affine model at direction `1` is exactly the selector slope.
    simpa using hmodel 1
  · -- The same model at direction `-1` gives the negative selector slope.
    simpa using hmodel (-1)

/-- Helper for Proposition 7.28: once the scalar directional derivatives at `0` are identified,
every scalar subgradient of the exact lifted line slice must equal the selector slope. -/
lemma lineSliceReverseInclusion_of_memSubdifferential
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) {g : ℝ}
    (hg : g ∈
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0)) :
    g = inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d := by
  -- Route correction: the reverse inclusion now reuses the restored owner-level scalar collapse.
  exact
    lineSliceSubgradient_eq_selectorSlope_of_memSubdifferential_owner
      hatP F x0 β uStar huStar huStar_unique t d hg

/-- Helper for Proposition 7.28: pointwise argmax uniqueness along the exact line slice should
collapse the scalar subdifferential at `0` to the singleton selector slope. -/
lemma lineSliceSubdifferential_eq_singleton_of_uniqueArgmax
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) :
    ∂ (fun α : ℝ ↦
      (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) =
      {inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d} := by
  -- The zero-base singleton theorem already packages the exact scalar line-slice equality.
  simpa using
    lineSliceSubdifferential_eq_singleton_zeroBase_of_uniqueArgmax
      hatP F x0 β uStar huStar huStar_unique t d

/-- Helper for Proposition 7.28: once the exact line slice has singleton subdifferential at `0`,
any scalar subgradient there is forced to equal the selector slope. -/
lemma lineSliceSubgradient_eq_selectorSlope_of_eq_singleton
    (uStar : StrongDual ℝ E → E)
    (t d : E) {g : ℝ}
    (hsingleton :
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) =
        {inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d})
    (hg : g ∈
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0)) :
    g = inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d := by
  -- Rewrite the scalar subgradient through the singleton owner equality.
  rw [hsingleton] at hg
  exact Set.mem_singleton_iff.mp hg

/-- Helper for Proposition 7.28: every scalar subgradient of the pulled-back line slice at `0`
must coincide with the unique selector slope at the base point. -/
lemma lineSliceSubgradient_eq_selectorSlope_of_uniqueArgmax
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) {g : ℝ}
    (hg : g ∈
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0)) :
    g = inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d := by
  -- Collapse the scalar subgradient through the earlier zero-base singleton theorem.
  exact
    lineSliceSubgradient_eq_selectorSlope_of_eq_singleton
      (hatP := hatP) (F := F) (x0 := x0) (β := β) uStar t d
      (lineSliceSubdifferential_eq_singleton_zeroBase_of_uniqueArgmax
        hatP F x0 β uStar huStar huStar_unique t d)
      hg

/-- Helper for Proposition 7.28: a scalar convex affine supremum whose active slices at `0` all
have the same slope has singleton subdifferential at `0`. -/
lemma subgradient_eq_activeSlope_of_uniqueAffineSupremumAtZero
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E)
    {g : ℝ}
    (hg : g ∈
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0)) :
    g = inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d := by
  -- Route correction: reuse the same limit-plus-sandwich collapse as the other scalar wrappers.
  exact
    lineSliceSubgradient_eq_selectorSlope_of_uniqueArgmax
      hatP F x0 β uStar huStar huStar_unique t d hg

/-- Helper for Proposition 7.28: every scalar subgradient of the pulled-back line slice at `0`
must coincide with the unique active selector slope at the base point. -/
lemma eq_selectorSlope_of_mem_lineSubdifferential
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) {g : ℝ}
    (hg : g ∈
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0)) :
    g = inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d := by
  -- Route correction: the concrete line-slice corollary now follows from the selector-slope limit
  -- bridge instead of the earlier singleton wrapper.
  exact
    lineSliceSubgradient_eq_selectorSlope_of_uniqueArgmax
      hatP F x0 β uStar huStar huStar_unique t d hg

/-- Helper for Proposition 7.28: along any affine line through `t`, pointwise argmax uniqueness
collapses the scalar subdifferential at `0` to the singleton given by the selector pairing. -/
lemma supportFunctionApproximation_lineSubdifferential_eq_singleton_of_unique_argmax
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t d : E) :
      ∂ (fun α : ℝ ↦
      (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) =
      {inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d} := by
  -- The zero-base singleton theorem already states the exact scalar line-slice formula.
  simpa using
    lineSliceSubdifferential_eq_singleton_zeroBase_of_uniqueArgmax
      hatP F x0 β uStar huStar huStar_unique t d

/-- Helper for Proposition 7.28: once the scalar line slice is differentiable, every pulled-back
subgradient has the same pairing with each direction as the selector vector. -/
lemma inner_eq_selectorPairing_of_mem_pullbackSubdifferential
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t : E) {g : E}
    (hg : g ∈
      ∂ (fun y : E ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y) : WithTop ℝ))(t))
    (d : E) :
    inner ℝ g d = inner ℝ (uStar ((InnerProductSpace.toDual ℝ E) t) - x0) d := by
  have hline :
      inner ℝ g d ∈
        ∂ (fun α : ℝ ↦
          (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) :=
    supportFunctionApproximation_line_subgradient_of_mem_pullbackSubdifferential
      hatP F x0 β t d hg
  have hsingleton :=
    supportFunctionApproximation_lineSubdifferential_eq_singleton_of_unique_argmax
      hatP F x0 β uStar huStar huStar_unique t d
  rw [hsingleton] at hline
  exact Set.mem_singleton_iff.mp hline

/-- Helper for Proposition 7.28: every pulled-back subgradient should equal the unique selector
vector at the base slope. -/
lemma eq_selectorVec_of_mem_pullbackSubdifferential
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t : E) {g : E}
    (hg : g ∈
      ∂ (fun y : E ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y) : WithTop ℝ))(t)) :
    g = uStar ((InnerProductSpace.toDual ℝ E) t) - x0 := by
  let target : E := uStar ((InnerProductSpace.toDual ℝ E) t) - x0
  have hpair :
      inner ℝ g (g - target) = inner ℝ target (g - target) :=
    inner_eq_selectorPairing_of_mem_pullbackSubdifferential
      hatP F x0 β uStar huStar huStar_unique t hg (g - target)
  have hself :
      inner ℝ (g - target) (g - target) = 0 := by
    -- Evaluate the pairing identity on the self-difference to isolate its squared norm.
    calc
      inner ℝ (g - target) (g - target)
          = inner ℝ g (g - target) - inner ℝ target (g - target) := by
              rw [inner_sub_left]
      _ = 0 := by linarith
  have hzero : g - target = 0 := inner_self_eq_zero.mp hself
  -- The vanishing self-difference identifies the pulled-back subgradient with the selector.
  exact sub_eq_zero.mp hzero

/-- Helper for Proposition 7.28: pointwise argmax uniqueness turns the pulled
back subdifferential into the singleton `{uStar ((toDual) t) - x₀}`. -/
lemma supportFunctionApproximation_pullback_subdifferential_eq_singleton_of_unique_selector
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (t : E) :
    ∂ (fun y : E ↦
      (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y) : WithTop ℝ))(t) =
      {uStar ((InnerProductSpace.toDual ℝ E) t) - x0} := by
  ext g
  constructor
  · intro hg
    have hg_eq :=
      eq_selectorVec_of_mem_pullbackSubdifferential
        hatP F x0 β uStar huStar huStar_unique t hg
    simpa [hg_eq]
  · intro hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    -- The selector vector already gives a pulled-back subgradient at `t`.
    exact
      supportFunctionApproximation_pullback_subgradient_of_selector
        hatP F x0 β uStar huStar t

/-- Helper for Proposition 7.28: evaluating a dual vector on `x` is the same as pairing `x` with
the inverse-Riesz representative of that dual vector. -/
lemma dual_apply_eq_inner_toDualSymm
    (v : StrongDual ℝ E) (x : E) :
    v x = inner ℝ x ((InnerProductSpace.toDual ℝ E).symm v) := by
  -- Read the dual evaluation through the inverse Riesz map and commute the real inner product.
  calc
    v x = inner ℝ ((InnerProductSpace.toDual ℝ E).symm v) x := by
      simpa [InnerProductSpace.toDual_symm_apply]
    _ = inner ℝ x ((InnerProductSpace.toDual ℝ E).symm v) := by
      rw [real_inner_comm]

/-- Auxiliary Fréchet-derivative bridge for Proposition 7.28: under a global
selector `uStar` for the canonical argmax owner `Argmaxβ`, the derivative of
`U_β` at `s` is evaluation at `uStar s - x₀`. -/
theorem supportFunctionApproximation_hasFDerivAt_of_unique_argmax
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (s : StrongDual ℝ E) :
    HasFDerivAt (Uβ hatP F x0 β) (ContinuousLinearMap.apply ℝ ℝ (uStar s - x0)) s := by
  let t : E := (InnerProductSpace.toDual ℝ E).symm s
  have hconv :
      ConvexOn ℝ Set.univ
        (fun y : E ↦ Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y)) :=
    supportFunctionApproximation_pullback_convexOn_univ_of_selector
      hatP F x0 β uStar huStar
  have hsub :
      ∂ (fun y : E ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y) : WithTop ℝ))(t) =
        {uStar s - x0} := by
    -- Rewrite the pulled-back singleton formula at the Riesz preimage of `s`.
    simpa [t] using
      supportFunctionApproximation_pullback_subdifferential_eq_singleton_of_unique_selector
        hatP F x0 β uStar huStar huStar_unique t
  have hgrad :
      HasGradientAt
        (fun y : E ↦ Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y))
        (uStar s - x0) t := by
    -- Convexity plus the singleton subdifferential identifies the pullback gradient.
    exact hasGradientAt_of_convexOn_univ_subdifferential_eq_singleton hconv hsub
  have hgradF :
      HasFDerivAt
        (fun y : E ↦ Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y))
        (innerSL ℝ (uStar s - x0))
        t := by
    -- Re-express the pullback gradient as its Fréchet derivative on `E`.
    simpa [hasGradientAt_iff_hasFDerivAt] using hgrad
  let rieszSymm : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hpullback :
      HasFDerivAt
        (fun s' : StrongDual ℝ E ↦
          Uβ hatP F x0 β
            ((InnerProductSpace.toDual ℝ E) ((InnerProductSpace.toDual ℝ E).symm s')))
        ((innerSL ℝ (uStar s - x0)).comp rieszSymm)
        s := by
    -- Compose the pullback gradient theorem with the inverse Riesz map.
    exact
      (hgradF.comp s
        (rieszSymm.hasFDerivAt))
  -- Transport the pullback gradient back to the dual owner through the inverse Riesz map.
  convert hpullback using 1
  · ext s'
    simp [rieszSymm]
  · ext v
    -- Rewrite the composed gradient functional by the inverse-Riesz pairing identity.
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply]
    rw [map_sub]
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.apply_apply, dual_apply_eq_inner_toDualSymm,
      dual_apply_eq_inner_toDualSymm, inner_sub_left]
    rfl

/-- Proposition 7.28 [Gradient of `U_β`]: assume `x₀ ∈ hatP` and every dual
point `s` admits a unique canonical maximizer `u^*_β(s)` in `Argmaxβ hatP F β
s`. Then the source-facing owner `Uβ hatP F x0 β : StrongDual ℝ E → ℝ` is
differentiable, and its derivative at `s` is evaluation at `u^*_β(s) - x₀`. -/
theorem supportFunctionApproximation_differentiable_and_hasFDerivAt_of_unique_argmax
    (hx0 : x0 ∈ hatP)
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s) :
    Differentiable ℝ (Uβ hatP F x0 β) ∧
      ∀ s : StrongDual ℝ E,
        HasFDerivAt (Uβ hatP F x0 β)
          (ContinuousLinearMap.apply ℝ ℝ (uStar s - x0)) s := by
  let _ := hx0
  constructor
  · -- The pointwise unique-argmax derivative bridge gives differentiability everywhere.
    intro s
    exact
      (supportFunctionApproximation_hasFDerivAt_of_unique_argmax
        hatP F x0 β uStar huStar huStar_unique s).differentiableAt
  · -- Reuse the same bridge with the chosen selector `uStar`.
    intro s
    exact
      supportFunctionApproximation_hasFDerivAt_of_unique_argmax
        hatP F x0 β uStar huStar huStar_unique s

/-- The positive support-function approximation `U_β` is differentiable when
its canonical argmax set admits a unique selector. -/
-- Proof sketch: apply the source-facing Proposition 7.28 statement and project
-- its differentiability conclusion.
theorem supportFunctionApproximation_differentiable_of_unique_argmax
    (hx0 : x0 ∈ hatP)
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s) :
    Differentiable ℝ (Uβ hatP F x0 β) := by
  -- Project the differentiability component from the source-facing package theorem.
  exact
    (supportFunctionApproximation_differentiable_and_hasFDerivAt_of_unique_argmax
      hatP F x0 β hx0 uStar huStar huStar_unique).1

end DualOwner

section HilbertBridge

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (hatP : Set E) (F : E → ℝ) (x0 : E) (β : {β : ℝ // 0 < β})

-- lean_leansearch recall: `HasFDerivAt.hasGradientAt` is the canonical bridge
-- from Fréchet derivatives to gradients and requires a complete inner-product
-- space; finite-dimensional Euclidean spaces supply that context.
-- Proof sketch: pull the dual-owner derivative back along
-- `InnerProductSpace.toDual ℝ E`; the representing vector remains `u - x₀`.
/-- The Hilbert-space pullback of `U_β` has gradient `u - x₀` at `s` whenever
the canonical argmax owner admits the global unique selector `uStar`. -/
theorem supportFunctionApproximation_hasGradientAt_of_unique_argmax
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (s : E) :
    HasGradientAt
      (fun t : E ↦ Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) t))
      (uStar ((InnerProductSpace.toDual ℝ E) s) - x0)
      s := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hdual :
      HasFDerivAt (Uβ hatP F x0 β)
        (ContinuousLinearMap.apply ℝ ℝ (uStar ((InnerProductSpace.toDual ℝ E) s) - x0))
        ((InnerProductSpace.toDual ℝ E) s) :=
    supportFunctionApproximation_hasFDerivAt_of_unique_argmax
      hatP F x0 β uStar huStar huStar_unique ((InnerProductSpace.toDual ℝ E) s)
  have hpullback :
      HasFDerivAt
        (fun t : E ↦ Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) t))
        ((ContinuousLinearMap.apply ℝ ℝ (uStar ((InnerProductSpace.toDual ℝ E) s) - x0)).comp
          ((InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap))
        s := by
    -- Pull the dual-owner derivative back through the Riesz map `toDual`.
    exact
      (hdual.comp s
        ((InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap).hasFDerivAt)
  -- Identify the pulled-back Fréchet derivative with the gradient vector `u - x₀`.
  convert hpullback using 1
  ext v
  simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    InnerProductSpace.toDual_apply_apply, real_inner_comm]

/-- Hilbert/Riesz bridge: under the unique-argmax hypothesis, the gradient of
the pulled-back support-function approximation is `u^*_β(s) - x₀`. -/
-- Proof sketch: extract the gradient from the pulled-back `HasGradientAt`
-- statement.
theorem gradient_supportFunctionApproximation_eq_of_unique_argmax
    (uStar : StrongDual ℝ E → E)
    (huStar : ∀ s : StrongDual ℝ E, uStar s ∈ Argmaxβ hatP F β s)
    (huStar_unique :
      ∀ s : StrongDual ℝ E, ∀ u : E, u ∈ Argmaxβ hatP F β s → u = uStar s)
    (s : E) :
    ∇ (fun t : E ↦ Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) t)) s =
      uStar ((InnerProductSpace.toDual ℝ E) s) - x0 := by
  simpa using
    (supportFunctionApproximation_hasGradientAt_of_unique_argmax
      hatP F x0 β uStar huStar huStar_unique s).gradient

end HilbertBridge

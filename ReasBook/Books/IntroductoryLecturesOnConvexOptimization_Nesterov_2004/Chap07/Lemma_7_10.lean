/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.PointwiseSupremumOn
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_21
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_21
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_20
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_1_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Lemma_6_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_53

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin Topology Gradient WithTopConvexAnalysis HessianDualLocalNorm
  HessianLocalNorm SelfConcordantAuxiliaryFunction

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Lemma 7.10 lies in the Chapter 7 barrier-smoothed support-function / self-concordant upper-model
domain.

Mandatory domain-style sampling before refinement:
- `Uβ` and `Argmaxβ` in `Chap07/Definition_7_53`, the Chapter 7 source-facing owners of the
  smoothed support-function value and its canonical argmax set;
- `smoothedPrimalObjectiveArgmax_unique` in `Chap06/Proposition_6_24` and
  `supportFunctionApproximation_hasFDerivAt_of_unique_argmax` in `Chap07/Proposition_7_28`, the
  owner-level uniqueness and derivative bridge for the positive support-function smoothing problem;
- `Uβ_apply` in `Chap07/Definition_7_53`, the source-facing expansion theorem for `U_β`;
- `IsSelfConcordantBarrierOnWith` in `Chap05/Definition_5_3_2`, the chapter owner for a
  self-concordant barrier on `interior Q`;
- `HessianDualLocalNorm.ofDetNeZero` in `Chap05/Definition_5_0_20`, the canonical local bridge to
  the source dual local norm `‖g‖_x^*` at an active maximizer with nonzero Hessian determinant;
- `selfConcordant_value_bounds_of_dualLocalNorm_gradient_sub` in `Chap05/Theorem_5_1_12`, the
  owner-level Chapter 5 upper/lower value estimate that actually justifies the `ω_*` remainder;
- `ω_*` in `Chap05/Definition_5_0_21`, the canonical Chapter 5 owner of the self-concordant upper
  remainder term.

Best owner abstraction:
- source-facing: Lemma 7.10's one-step `ω_*` upper model for the specialized support-function
  approximation `U_β`;
- core/canonical: `Uβ`, `Argmaxβ`, the local dual norm `‖g‖*[F; x | hPos; hInv]`, and `ω_*`;
- stronger helper surface: the separate Chapter 7 differentiability bridge
  `supportFunctionApproximation_hasFDerivAt_of_unique_argmax`;
- bridge/view: the determinant-witness reader
  `supportFunctionApproximationDualLocalNormAt`, the positive-definite-domain reader
  `HessianDualLocalNorm.ofPosDefMem`, and the unique-argmax derivative companion.

Primitive data:
- the feasible set `hatP`, ambient barrier set `Q`, barrier `F`, base point `x₀`, and smoothing
  parameter `β`;
- the active maximizer `x` at the dual point `s`;
- the interior-domain membership `x ∈ interior Q`;
- the standard self-concordant owner on `interior Q`;
- the local Hessian determinant witness at the active maximizer, kept only for the determinant,
  invertibility, and positive-definite companion bridges to the Chapter 5 dual local norm;
- the positive-definite Hessian owner on `interior Q`, used only by the domain-level companion
  corollary
  `smoothSupportFunctionApproximation_hasFDerivAt_and_omegaStar_upper_bound_of_posDefMem`.

Derived API:
- the smoothed support-function value owner `Uβ`;
- the argmax predicate owner `Argmaxβ`;
- the source local perturbation size, read through the determinant-witness active-point bridge
  `supportFunctionApproximationDualLocalNormAt`;
- the explicit local Chapter 5 owner `‖g‖*[F; x | hPos; hInv]` at the active maximizer and its
  positive-definite-domain bridge `HessianDualLocalNorm.ofPosDefMem` on `interior Q`;
- the self-concordant remainder `ω_*`.

This lemma stays source-facing: it keeps the one-step support-function upper model on the Chapter 7
owners instead of collapsing it to the more general Chapter 5 bound. Because the repo's owner
`IsStandardSelfConcordantOn` only gives Hessian positivity, the labeled theorem reads the active-
point perturbation condition through the source-facing bridge
`supportFunctionApproximationDualLocalNormLt`, which hides the pointwise determinant witness needed
by the Chapter 5 dual local norm owner. The determinant, invertibility, and positive-definite-
domain readers remain downstream companion bridges for files that already work with those stronger
Hessian witnesses.

Semantic recall checkpoint: `lean_leansearch` did not surface a better ambient owner for this
active-point norm hypothesis, and local repo verification confirmed
`supportFunctionApproximation_hasFDerivAt_of_unique_argmax`,
`supportFunctionApproximationDualLocalNormAt`, `supportFunctionApproximationDualLocalNormLt`,
`HessianDualLocalNorm.ofDetNeZero`, and `HessianDualLocalNorm.ofPosDefMem` as the relevant bridge
API.
-/

section

variable (hatP Q : Set E) (F : E → ℝ) (x0 : E) (β : {β : ℝ // 0 < β})

/-- Helper: an active maximizer belongs to `interior Q` once `hatP` is contained in
`interior Q`. -/
private theorem argmaxBeta_mem_interior_of_subset
    {s : StrongDual ℝ E} {x : E}
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hhatP_int : hatP ⊆ interior Q) :
    x ∈ interior Q := by
  -- Expand the argmax owner once to recover the feasible-set membership of `x`.
  rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff] at hx_argmax
  exact hhatP_int hx_argmax.1

/-- Pointwise Chapter 5 dual local norm at an active maximizer `x`, read through the derived
interior membership of `x`, self-concordant Hessian positivity at `x`, and an explicit
determinant witness for `hessian F x`. -/
abbrev supportFunctionApproximationDualLocalNormAt
    {s : StrongDual ℝ E} {x : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hhatP_int : hatP ⊆ interior Q)
    (hx_det : (hessian F x).det ≠ 0)
    (g : StrongDual ℝ E) : ℝ :=
  let hx_int : x ∈ interior Q := argmaxBeta_mem_interior_of_subset hatP Q F β hx_argmax hhatP_int
  let hPos : (hessian F x).IsPositive :=
    (inferInstance : IsStandardSelfConcordantOn (interior Q) F).hessian_isPositive hx_int
  HessianDualLocalNorm.ofDetNeZero F x hPos hx_det g

/-- Rewriting the local perturbation norm recovers the Chapter 5 determinant-witness dual local
norm owner at the active maximizer `x`. -/
theorem supportFunctionApproximationDualLocalNormAt_eq_ofPosDefMem
    {s : StrongDual ℝ E} {x : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hhatP_int : hatP ⊆ interior Q)
    (hx_det : (hessian F x).det ≠ 0)
    (g : StrongDual ℝ E) :
    supportFunctionApproximationDualLocalNormAt hatP Q F β hx_argmax hhatP_int hx_det g =
      HessianDualLocalNorm.ofDetNeZero F x
        ((inferInstance : IsStandardSelfConcordantOn (interior Q) F).hessian_isPositive
          (argmaxBeta_mem_interior_of_subset hatP Q F β hx_argmax hhatP_int))
        hx_det g := by
  simp [supportFunctionApproximationDualLocalNormAt]

/-- Source-facing perturbation condition `‖g‖_x^* < β` at an active maximizer `x`. Internally the
Chapter 5 dual local norm is read through some determinant witness for `hessian F x`, but that
witness is kept off the labeled Lemma 7.10 surface. -/
def supportFunctionApproximationDualLocalNormLt
    {s : StrongDual ℝ E} {x : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hhatP_int : hatP ⊆ interior Q)
    (g : StrongDual ℝ E) : Prop :=
  ∃ hx_det : (hessian F x).det ≠ 0,
    supportFunctionApproximationDualLocalNormAt hatP Q F β hx_argmax hhatP_int hx_det g < (β : ℝ)

/-- Expanding `supportFunctionApproximationDualLocalNormLt` recovers the underlying
determinant-witness perturbation condition. -/
theorem supportFunctionApproximationDualLocalNormLt_iff
    {s : StrongDual ℝ E} {x : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hhatP_int : hatP ⊆ interior Q)
    (g : StrongDual ℝ E) :
    supportFunctionApproximationDualLocalNormLt hatP Q F β hx_argmax hhatP_int g ↔
      ∃ hx_det : (hessian F x).det ≠ 0,
        supportFunctionApproximationDualLocalNormAt
            hatP Q F β hx_argmax hhatP_int hx_det g <
          (β : ℝ) := by
  -- This is exactly the defining existential hidden by the source-facing predicate.
  rfl

/-- Source-facing `ω_*` remainder term at an active maximizer `x`. -/
abbrev supportFunctionApproximationOmegaStarUpperTermOfDetNeZero
    {s : StrongDual ℝ E} {x : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hhatP_int : hatP ⊆ interior Q)
    (hx_det : (hessian F x).det ≠ 0)
    (g : StrongDual ℝ E)
    (hg :
      supportFunctionApproximationDualLocalNormAt hatP Q F β hx_argmax hhatP_int hx_det g <
        (β : ℝ)) :
    ℝ :=
  (β : ℝ) *
    ω_* (selfConcordantOmegaStarArg (1 : NNReal)
      (supportFunctionApproximationDualLocalNormAt
        hatP Q F β hx_argmax hhatP_int hx_det g / (β : ℝ))
      (by
        simpa [one_mul] using
          (div_lt_iff₀ β.2).2
            (show
                supportFunctionApproximationDualLocalNormAt
                    hatP Q F β hx_argmax hhatP_int hx_det g <
                  1 * (β : ℝ) by
              simpa using hg)))

/-- Source-facing `ω_*` remainder term in Lemma 7.10 for an admissible perturbation `g`, i.e. one
with `‖g‖_x^* < β` encoded by `supportFunctionApproximationDualLocalNormLt`. The determinant
witness needed by the Chapter 5 local-norm reader is hidden inside `hg`. -/
abbrev supportFunctionApproximationOmegaStarUpperTerm
    {s : StrongDual ℝ E} {x : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hhatP_int : hatP ⊆ interior Q)
    (g : StrongDual ℝ E)
    (hg : supportFunctionApproximationDualLocalNormLt hatP Q F β hx_argmax hhatP_int g) :
    ℝ :=
  let hx_det : (hessian F x).det ≠ 0 := Classical.choose hg
  let hg_det :
      supportFunctionApproximationDualLocalNormAt
          hatP Q F β hx_argmax hhatP_int hx_det g <
        (β : ℝ) := Classical.choose_spec hg
  supportFunctionApproximationOmegaStarUpperTermOfDetNeZero
    hatP Q F β hx_argmax hhatP_int hx_det g hg_det

/-- Rewriting the `ω_*` remainder matches the Chapter 5 upper-model term evaluated at the same
active maximizer `x`. -/
theorem supportFunctionApproximationOmegaStarUpperTermOfDetNeZero_eq_ofPosDefMem
    {s : StrongDual ℝ E} {x : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hhatP_int : hatP ⊆ interior Q)
    (hx_det : (hessian F x).det ≠ 0)
    (g : StrongDual ℝ E)
    (hg :
      supportFunctionApproximationDualLocalNormAt hatP Q F β hx_argmax hhatP_int hx_det g <
        (β : ℝ)) :
    supportFunctionApproximationOmegaStarUpperTermOfDetNeZero
        hatP Q F β hx_argmax hhatP_int hx_det g hg =
      (β : ℝ) *
        ω_* (selfConcordantOmegaStarArg (1 : NNReal)
          (HessianDualLocalNorm.ofDetNeZero F x
            ((inferInstance : IsStandardSelfConcordantOn (interior Q) F).hessian_isPositive
              (argmaxBeta_mem_interior_of_subset hatP Q F β hx_argmax hhatP_int))
            hx_det g / (β : ℝ))
          (by
            let hx_int : x ∈ interior Q :=
              argmaxBeta_mem_interior_of_subset hatP Q F β hx_argmax hhatP_int
            let hPos : (hessian F x).IsPositive :=
              (inferInstance : IsStandardSelfConcordantOn (interior Q) F).hessian_isPositive hx_int
            have hg' :
                HessianDualLocalNorm.ofDetNeZero F x hPos hx_det g <
                  (β : ℝ) := by
              simpa [supportFunctionApproximationDualLocalNormAt_eq_ofPosDefMem
                hatP Q F β hx_argmax hhatP_int hx_det g, hx_int, hPos]
                using hg
            simpa [one_mul, hx_int] using
              (div_lt_iff₀ β.2).2
                (show HessianDualLocalNorm.ofDetNeZero F x hPos hx_det g < 1 * (β : ℝ) by
                  simpa using hg'))) := by
  simp [supportFunctionApproximationOmegaStarUpperTermOfDetNeZero,
    supportFunctionApproximationDualLocalNormAt_eq_ofPosDefMem
      hatP Q F β hx_argmax hhatP_int hx_det g]

/-- If the perturbation condition is witnessed by a specific determinant proof, the source-facing
`ω_*` remainder owner rewrites to the corresponding explicit Chapter 5 determinant-witness term. -/
theorem supportFunctionApproximationOmegaStarUpperTerm_eq_of_detNeZero
    {s : StrongDual ℝ E} {x : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hhatP_int : hatP ⊆ interior Q)
    (g : StrongDual ℝ E)
    (hx_det : (hessian F x).det ≠ 0)
    (hg :
      supportFunctionApproximationDualLocalNormAt hatP Q F β hx_argmax hhatP_int hx_det g <
        (β : ℝ)) :
    supportFunctionApproximationOmegaStarUpperTerm
        hatP Q F β hx_argmax hhatP_int g ⟨hx_det, hg⟩ =
      supportFunctionApproximationOmegaStarUpperTermOfDetNeZero
        hatP Q F β hx_argmax hhatP_int hx_det g hg := by
  classical
  -- Unfold the hidden witness owner and simplify the chosen determinant witness.
  simp [supportFunctionApproximationOmegaStarUpperTerm]

/-- Helper for Lemma 7.10: an active maximizer rewrites the owner value `Uβ hatP F x0 β s` as the
corresponding textbook payoff at that point. -/
private theorem supportFunctionApproximation_value_eq_of_fixedArgmax
    {s : StrongDual ℝ E} {x : E}
    (hx_argmax : x ∈ Argmaxβ hatP F β s) :
    Uβ hatP F x0 β s = s (x - x0) - β * (F x - F x0) := by
  rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff] at hx_argmax
  rcases hx_argmax with ⟨hx_hatP, hx_max⟩
  have hgreatest :
      IsGreatest ((fun v : E ↦ s v - (β : ℝ) * F v) '' hatP) (s x - (β : ℝ) * F x) := by
    refine ⟨⟨x, hx_hatP, rfl⟩, ?_⟩
    intro z hz
    rcases hz with ⟨v, hv_hatP, rfl⟩
    simpa [smoothedPrimalObjectiveMaximand] using (isMaxOn_iff.mp hx_max) v hv_hatP
  -- Replace the conditional supremum by the attained active value.
  rw [Uβ_apply, hgreatest.csSup_eq, map_sub, mul_sub]
  ring

/-- Helper for Lemma 7.10: a convex real-valued function on the whole space is differentiable at
`x₀` once its lifted subdifferential there is the singleton `{g}`. -/
private lemma hasGradientAt_of_convexOn_univ_subdifferential_eq_singleton
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

/-- Helper for Lemma 7.10: subtracting the affine scalar support line `α ↦ α * g` turns an exact
scalar subgradient `g ∈ ∂φ(0)` into zero belonging to the subdifferential of the tilted slice
`α ↦ φ(α) - α g`. -/
private theorem zero_mem_subdifferential_sub_affine_of_mem_subdifferential
    {φ : ℝ → ℝ} {g : ℝ}
    (hg :
      g ∈ ∂ (fun α : ℝ ↦ ((φ α : ℝ) : WithTop ℝ))(0)) :
    0 ∈
      ∂ (fun α : ℝ ↦ ((φ α - α * g : ℝ) : WithTop ℝ))(0) := by
  rw [mem_subdifferential_coe_real_iff] at hg ⊢
  intro y
  -- Rewrite the exact scalar support inequality after removing the affine support line `α * g`.
  have hsupport : φ y ≥ φ 0 + y * g := by
    calc
      φ y ≥ φ 0 + inner ℝ g (y - 0) := hg y
      _ = φ 0 + y * g := by
            have hinner : inner ℝ g (y - 0) = g * (y - 0) := by
              simpa using (RCLike.inner_apply' g (y - 0))
            rw [hinner]
            ring
  have hbase : φ y - y * g ≥ φ 0 := by
    linarith
  simpa [RCLike.inner_apply', sub_eq_add_neg, mul_comm, add_comm, add_left_comm, add_assoc] using
    hbase

/-- Helper for Lemma 7.10: if the scalar affine tilt `α ↦ φ(α) - α g` has zero in its
subdifferential at `0`, then adding the same affine line back recovers `g ∈ ∂φ(0)`. -/
private theorem mem_subdifferential_of_zero_mem_subdifferential_sub_affine
    {φ : ℝ → ℝ} {g : ℝ}
    (hzero :
      0 ∈
        ∂ (fun α : ℝ ↦ ((φ α - α * g : ℝ) : WithTop ℝ))(0)) :
    g ∈ ∂ (fun α : ℝ ↦ ((φ α : ℝ) : WithTop ℝ))(0) := by
  rw [mem_subdifferential_coe_real_iff] at hzero ⊢
  intro y
  -- Reinsert the affine term `α * g` into the tilted support inequality.
  have hsupport : φ y - y * g ≥ φ 0 := by
    calc
      φ y - y * g ≥ φ 0 - 0 * g + inner ℝ 0 (y - 0) := hzero y
      _ = φ 0 := by
            have hinner : inner ℝ (0 : ℝ) (y - 0) = 0 * (y - 0) := by
              simpa using (RCLike.inner_apply' (0 : ℝ) (y - 0))
            rw [hinner]
            ring
  have hbase : φ y ≥ φ 0 + y * g := by
    linarith
  calc
    φ y ≥ φ 0 + y * g := hbase
    _ = φ 0 + inner ℝ g (y - 0) := by
          have hinner : inner ℝ g (y - 0) = g * (y - 0) := by
            simpa using (RCLike.inner_apply' g (y - 0))
          rw [hinner]
          ring

/-- Helper for Lemma 7.10: once the directional derivatives of a scalar convex slice at `0` in
directions `1` and `-1` are `b0` and `-b0`, every scalar subgradient at `0` is forced to equal
`b0`. -/
private theorem subgradient_eq_of_directionalDerivativeSigns_at_zero
    {φLift : ℝ → WithTop ℝ} {b0 g : ℝ}
    (hconv : ConvexOn ℝ (dom φLift) (withTopRealPart φLift))
    (h0 : (0 : ℝ) ∈ interior (dom φLift))
    (hg : g ∈ ∂ φLift(0))
    (hplus : convexDirectionalDerivativeReal φLift h0 (1 : ℝ) = b0)
    (hminus : convexDirectionalDerivativeReal φLift h0 (-1 : ℝ) = -b0) :
    g = b0 := by
  have hgreatestPlus :=
    convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior hconv h0 (1 : ℝ)
  have hgreatestMinus :=
    convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior hconv h0 (-1 : ℝ)
  rw [convexDirectionalDerivativeReal_apply] at hgreatestPlus hgreatestMinus
  have hinner (x y : ℝ) : inner ℝ x y = x * y := by
    simpa using (RCLike.inner_apply' x y)
  have hpair_plus : inner ℝ g (1 : ℝ) = g := by
    simpa [hinner]
  have hpair_minus : inner ℝ g (-1 : ℝ) = -g := by
    simpa [hinner]
  have hgplus :
      g ∈ (fun z : ℝ ↦ inner ℝ z (1 : ℝ)) '' ∂ φLift(0) := by
    -- Package the candidate scalar subgradient as a pairing image in direction `1`.
    exact ⟨g, hg, hpair_plus⟩
  have hgminus :
      -g ∈ (fun z : ℝ ↦ inner ℝ z (-1 : ℝ)) '' ∂ φLift(0) := by
    -- The same pairing-image packaging in direction `-1` reads as negation on `ℝ`.
    exact ⟨g, hg, hpair_minus⟩
  have hupper : g ≤ b0 := by
    -- The positive-direction directional derivative is the greatest subgradient pairing at `0`.
    have hle : g ≤ convexDirectionalDerivativeReal φLift h0 (1 : ℝ) := by
      simpa using hgreatestPlus.2 hgplus
    linarith
  have hlower : b0 ≤ g := by
    -- The negative-direction directional derivative gives the complementary lower bound.
    have hle : -g ≤ convexDirectionalDerivativeReal φLift h0 (-1 : ℝ) := by
      simpa using hgreatestMinus.2 hgminus
    linarith
  -- The two sign directions squeeze the scalar subgradient to the unique slope `b0`.
  exact le_antisymm hupper hlower

/-- Helper for Lemma 7.10: if a scalar lifted convex function has singleton subdifferential
`{b0}` at `0`, then its directional derivatives at `0` in directions `1` and `-1` are bounded
above by `b0` and `-b0`. -/
private theorem directionalDerivativeSigns_le_of_subdifferential_eq_singleton
    {φLift : ℝ → WithTop ℝ} {b0 : ℝ}
    (hconv : ConvexOn ℝ (dom φLift) (withTopRealPart φLift))
    (h0 : (0 : ℝ) ∈ interior (dom φLift))
    (hsub : ∂ φLift(0) = {b0}) :
    convexDirectionalDerivativeReal φLift h0 (1 : ℝ) ≤ b0 ∧
      convexDirectionalDerivativeReal φLift h0 (-1 : ℝ) ≤ -b0 := by
  have hinner (x y : ℝ) : inner ℝ x y = x * y := by
    simpa using (RCLike.inner_apply' x y)
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

/-- Helper for Lemma 7.10: a scalar affine slice has singleton subdifferential equal to its
displayed slope. -/
private theorem supportFunctionApproximation_affineScalarSlice_subdifferential_eq_singleton
    (a slope : ℝ) :
    ∂ (fun α : ℝ ↦ ((a + α * slope : ℝ) : WithTop ℝ))(0) = {slope} := by
  ext g
  rw [Set.mem_singleton_iff, mem_subdifferential_coe_real_iff]
  have hinner (x y : ℝ) : inner ℝ x y = x * y := by
    -- On `ℝ`, the ambient inner product is ordinary multiplication.
    simpa using (RCLike.inner_apply' x y)
  constructor
  · intro hg
    have hpos : a + g ≤ a + slope := by
      -- Evaluating the support inequality at `1` gives the upper slope bound.
      simpa [hinner, mul_comm] using hg 1
    have hneg : a + -g + slope ≤ a := by
      -- Evaluating it at `-1` gives the complementary lower slope bound.
      simpa [hinner, mul_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hg (-1)
    linarith
  · intro hg
    subst hg
    intro y
    -- The displayed slope supports its own affine slice with equality at every point.
    simpa [hinner, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]

/-- Helper for Lemma 7.10: evaluating a dual vector on `x` is the same as pairing `x` with the
inverse-Riesz representative of that dual vector. -/
private theorem dual_apply_eq_inner_toDualSymm
    (v : StrongDual ℝ E) (x : E) :
    v x = inner ℝ x ((InnerProductSpace.toDual ℝ E).symm v) := by
  -- Read the dual evaluation through the inverse Riesz map and commute the real inner product.
  calc
    v x = inner ℝ ((InnerProductSpace.toDual ℝ E).symm v) x := by
      simpa [InnerProductSpace.toDual_symm_apply]
    _ = inner ℝ x ((InnerProductSpace.toDual ℝ E).symm v) := by
      rw [real_inner_comm]

/-- Helper for Lemma 7.10: once the pulled-back owner has gradient `g` at the Riesz preimage of
`s`, the original owner `Uβ` has Fréchet derivative `v ↦ v g` at `s`. -/
private theorem supportFunctionApproximationHasFDerivAt_of_pullbackHasGradientAt
    {s : StrongDual ℝ E} {g : E}
    (hgrad :
      HasGradientAt
        (fun y : E ↦ Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y))
        g
        ((InnerProductSpace.toDual ℝ E).symm s)) :
    HasFDerivAt (Uβ hatP F x0 β) (ContinuousLinearMap.apply ℝ ℝ g) s := by
  have hgradF :
      HasFDerivAt
        (fun y : E ↦ Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y))
        (innerSL ℝ g)
        ((InnerProductSpace.toDual ℝ E).symm s) := by
    -- Re-express the pulled-back gradient as its Fréchet derivative on `E`.
    simpa [hasGradientAt_iff_hasFDerivAt] using hgrad
  let rieszSymm : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hpullback :
      HasFDerivAt
        (fun s' : StrongDual ℝ E ↦
          Uβ hatP F x0 β
            ((InnerProductSpace.toDual ℝ E) ((InnerProductSpace.toDual ℝ E).symm s')))
        ((innerSL ℝ g).comp rieszSymm)
        s := by
    -- Compose the pulled-back gradient theorem with the inverse Riesz map.
    exact hgradF.comp s rieszSymm.hasFDerivAt
  -- Transport the pulled-back Fréchet derivative back to the dual owner through the inverse
  -- Riesz map.
  convert hpullback using 1
  · ext s'
    simp [rieszSymm]
  · ext v
    -- Rewrite the composed pullback derivative as ordinary dual evaluation at `g`.
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply]
    rw [ContinuousLinearMap.apply_apply, dual_apply_eq_inner_toDualSymm]
    rfl

/-- Helper for Lemma 7.10: if `u` is active at `s` and `v` is active at `t`, then the secant
increment of `Uβ` is trapped between the pairings with `u - x₀` and `v - x₀`. -/
private theorem supportFunctionApproximation_secant_bounds_of_memArgmax
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
      supportFunctionApproximation_value_eq_of_fixedArgmax
        hatP F x0 β (by
          rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff]
          exact ⟨hu_mem, hu_max⟩)
  have ht :
      Uβ hatP F x0 β t = t (v - x0) - β * (F v - F x0) := by
    -- Do the same at the comparison point `t`.
    exact
      supportFunctionApproximation_value_eq_of_fixedArgmax
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

/-- Helper for Lemma 7.10: the pulled-back scalar line slice of `Uβ` is real-valued, so `0`
lies in the interior of its effective domain. -/
private theorem supportFunctionApproximation_line_zero_mem_interior_dom
    (t d : E) :
    (0 : ℝ) ∈ interior
      (dom (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))) := by
  have hdom :
      dom (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ)) =
        (Set.univ : Set ℝ) := by
    ext α
    change
      ((((Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : ℝ) : WithTop ℝ) < ⊤) ↔
        True)
    constructor
    · intro _
      trivial
    · intro _
      exact WithTop.coe_lt_top _
  -- Every point of `ℝ`, in particular `0`, lies in the interior of `Set.univ`.
  rw [hdom]
  simp

/-- Helper for Lemma 7.10: on `Set.univ`, the within-set gradient notation agrees with the global
gradient notation. -/
private theorem gradientWithin_univ_eq_gradient
    {f : E → ℝ} (u : E) :
    gradientWithin f Set.univ u = ∇ f u := by
  -- The whole-space derivative uses `fderiv`, so the within-gradient and global gradient coincide.
  simp [gradientWithin, gradient, fderivWithin_univ]

/-- Helper for Lemma 7.10: the pulled-back affine base term
`y ↦ -⟪x₀, y⟫ + β * F x₀` has constant gradient `-x₀`. -/
private theorem supportFunctionApproximationPullbackAffineBase_hasGradientAt
    (t : E) :
    HasGradientAt (fun y : E ↦ inner ℝ (-x0) y + (β : ℝ) * F x0) (-x0) t := by
  have hinnerSL :
      innerSL ℝ (-x0) = (InnerProductSpace.toDual ℝ E) (-x0) := by
    ext y
    simp [InnerProductSpace.toDual_apply_apply, real_inner_comm]
  have htoDual :
      (InnerProductSpace.toDual ℝ E).symm (innerSL ℝ (-x0)) = -x0 := by
    -- The inverse Riesz map sends the representing covector back to `-x₀`.
    rw [hinnerSL]
    simp
  have hderiv :
      HasFDerivAt (fun y : E ↦ inner ℝ (-x0) y + (β : ℝ) * F x0) (innerSL ℝ (-x0)) t := by
    -- Differentiate the linear functional and keep the additive constant fixed.
    simpa using
      ((innerSL ℝ (-x0)).hasFDerivAt.add_const ((β : ℝ) * F x0))
  -- Read the Fréchet derivative back as the displayed gradient vector `-x₀`.
  simpa [hasGradientAt_iff_hasFDerivAt, htoDual] using hderiv

/-- Helper for Lemma 7.10: the pulled-back affine base term
`y ↦ -⟪x₀, y⟫ + β * F x₀` is convex on the whole space. -/
private theorem supportFunctionApproximationPullbackAffineBase_convexOn :
    ConvexOn ℝ Set.univ (fun y : E ↦ inner ℝ (-x0) y + (β : ℝ) * F x0) := by
  have hlinear :
      ConvexOn ℝ Set.univ (fun y : E ↦ inner ℝ (-x0) y) := by
    -- Any linear functional is convex on a convex domain.
    exact ((innerSL ℝ (-x0)).toLinearMap.convexOn convex_univ)
  -- Adding the constant shift `β * F x₀` preserves convexity.
  simpa [innerSL_apply_apply] using
    hlinear.add (convexOn_const ((β : ℝ) * F x0) convex_univ)

/-- Helper for Lemma 7.10: once the canonical score image at a comparison slope `t` is bounded
above, every feasible point `u ∈ hatP` gives a lower bound on the source value
`Uβ hatP F x0 β t`. -/
private theorem supportFunctionApproximation_value_le_of_mem_hatP_of_bddAbove
    {t : StrongDual ℝ E} {u : E}
    (hu_hatP : u ∈ hatP)
    (hscore_bddAbove : BddAbove ((fun v : E ↦ t v - β * F v) '' hatP)) :
    t (u - x0) - β * (F u - F x0) ≤ Uβ hatP F x0 β t := by
  -- Expand the owner formula once, then insert the feasible point `u` into the score supremum.
  calc
    t (u - x0) - β * (F u - F x0)
        = (-t x0 + (β : ℝ) * F x0) + (t u - (β : ℝ) * F u) := by
            rw [ContinuousLinearMap.map_sub, mul_sub]
            ring
    _ ≤ (-t x0 + (β : ℝ) * F x0) + sSup ((fun v : E ↦ t v - β * F v) '' hatP) := by
          gcongr
          exact le_csSup hscore_bddAbove ⟨u, hu_hatP, rfl⟩
    _ = Uβ hatP F x0 β t := by
          rw [Uβ_apply]

/-- Helper for Lemma 7.10: if every comparison slope has a bounded canonical score image, then
the active point `x` already yields a pulled-back subgradient of
`y ↦ Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y)` at the base slope. -/
private theorem supportFunctionApproximation_pullback_subgradient_of_fixedArgmax_of_bddAbove
    {s : StrongDual ℝ E} {x : E}
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hscore_bddAbove :
      ∀ t : StrongDual ℝ E, BddAbove ((fun u : E ↦ t u - β * F u) '' hatP)) :
    x - x0 ∈
      ∂ (fun y : E ↦
          (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y) : WithTop ℝ))
        (((InnerProductSpace.toDual ℝ E).symm s)) := by
  let t : E := (InnerProductSpace.toDual ℝ E).symm s
  have hx_hatP : x ∈ hatP := by
    -- Unpack the active-owner membership to recover the feasible point `x ∈ hatP`.
    rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff] at hx_argmax
    exact hx_argmax.1
  have hx_value :
      Uβ hatP F x0 β s = s (x - x0) - β * (F x - F x0) :=
    supportFunctionApproximation_value_eq_of_fixedArgmax hatP F x0 β hx_argmax
  rw [mem_subdifferential_coe_real_iff]
  intro y
  change
    Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y) ≥
      Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) t) +
        inner ℝ (x - x0) (y - t)
  have hy_value_le :
      ((InnerProductSpace.toDual ℝ E) y) (x - x0) - β * (F x - F x0) ≤
        Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y) :=
    supportFunctionApproximation_value_le_of_mem_hatP_of_bddAbove
      hatP F x0 β hx_hatP (hscore_bddAbove ((InnerProductSpace.toDual ℝ E) y))
  have hs_pair :
      s (x - x0) = inner ℝ (x - x0) t := by
    simpa [t] using dual_apply_eq_inner_toDualSymm s (x - x0)
  -- Rewrite the pulled-back support inequality so the active source value at `x` appears.
  calc
    Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y)
        ≥ ((InnerProductSpace.toDual ℝ E) y) (x - x0) - β * (F x - F x0) := hy_value_le
    _ = inner ℝ (x - x0) (y - t) + Uβ hatP F x0 β s := by
          have hy_pair :
              ((InnerProductSpace.toDual ℝ E) y) (x - x0) = inner ℝ (x - x0) y := by
            simpa using
              dual_apply_eq_inner_toDualSymm ((InnerProductSpace.toDual ℝ E) y) (x - x0)
          rw [hy_pair, hx_value, inner_sub_right, hs_pair]
          ring
    _ = Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) t) + inner ℝ (x - x0) (y - t) := by
          simpa [t] using
            (show inner ℝ (x - x0) (y - t) + Uβ hatP F x0 β s =
                Uβ hatP F x0 β s + inner ℝ (x - x0) (y - t) by ring)

/-- Helper for Lemma 7.10: restricting a pulled-back subgradient to any affine line through the
base point turns it into a scalar subgradient of the corresponding line slice at `0`. -/
private theorem supportFunctionApproximationLineSubgradientOfMemPullbackSubdifferential
    (t d : E) {g : E}
    (hg : g ∈
      ∂ (fun y : E ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y) : WithTop ℝ))(t)) :
    inner ℝ g d ∈
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) := by
  rw [mem_subdifferential_coe_real_iff] at hg ⊢
  intro α
  -- Specialize the ambient support inequality to the affine line `α ↦ t + α • d`.
  have hline := hg (t + α • d)
  simpa [RCLike.inner_apply, inner_smul_right, sub_eq_add_neg, zero_smul, add_assoc,
    add_left_comm, add_comm, mul_comm, mul_left_comm, mul_assoc] using hline

/-- Helper for Lemma 7.10: once the pulled-back vector `x - x₀` is known to be an ambient
subgradient at `t`, singleton subdifferentials on every affine line through `t` force the full
pulled-back subdifferential to be exactly `{x - x₀}`. -/
private theorem supportFunctionApproximationPullbackSubdifferential_eq_singleton_of_mem_and_lineSingleton
    (t : E) {x : E}
    (hxSub :
      x - x0 ∈
        ∂ (fun y : E ↦
          (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y) : WithTop ℝ))(t))
    (hline :
      ∀ d : E,
        ∂ (fun α : ℝ ↦
          (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) =
            {inner ℝ (x - x0) d}) :
    ∂ (fun y : E ↦
      (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y) : WithTop ℝ))(t) =
        {x - x0} := by
  ext g
  constructor
  · intro hg
    have hpair :
        ∀ d : E, inner ℝ g d = inner ℝ (x - x0) d := by
      intro d
      -- Restrict the ambient subgradient to the line in direction `d`, then collapse the scalar
      -- subdifferential by the assumed singleton formula.
      have hgLine :
          inner ℝ g d ∈
            ∂ (fun α : ℝ ↦
              (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) :=
        supportFunctionApproximationLineSubgradientOfMemPullbackSubdifferential
          hatP F x0 β t d hg
      rw [hline d] at hgLine
      exact Set.mem_singleton_iff.mp hgLine
    have hself :
        inner ℝ (g - (x - x0)) (g - (x - x0)) = 0 := by
      -- Evaluate the pairing identity on the self-difference to force its norm to vanish.
      calc
        inner ℝ (g - (x - x0)) (g - (x - x0))
            = inner ℝ g (g - (x - x0)) - inner ℝ (x - x0) (g - (x - x0)) := by
                rw [inner_sub_left]
        _ = 0 := by
              have hpairSelf := hpair (g - (x - x0))
              linarith
    have hzero : g - (x - x0) = 0 := inner_self_eq_zero.mp hself
    exact Set.mem_singleton_iff.mpr (sub_eq_zero.mp hzero)
  · intro hg
    -- The designated base subgradient supplies the reverse singleton inclusion.
    rw [Set.mem_singleton_iff] at hg
    simpa [hg] using hxSub

/-
Route correction: the old pulled-back subgradient / secant branch depended on a boundedness-free
singleton-subdifferential route that is not part of the remaining source-faithful proof plan.
The public theorem below only needs the perturbed-gap / owner-upper-model chain, so that abandoned
private branch is removed here to keep the frontier focused on the actual `ω_*` and derivative
blockers.
-/

/-- Helper for Lemma 7.10: every feasible perturbed payoff at slope `s + g` should be controlled
by the fixed active value at `s`, the perturbation pairing at `x`, and the determinant-witness
`ω_*` remainder. -/
private theorem supportFunctionApproximationActiveScoreGapNonposOfFixedArgmax
    {s : StrongDual ℝ E} {x : E}
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    {y : E} (hy_hatP : y ∈ hatP) :
    s (y - x) - β * (F y - F x) ≤ 0 := by
  rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff] at hx_argmax
  rcases hx_argmax with ⟨hx_hatP, hx_max⟩
  have hy_score_le : s y - (β : ℝ) * F y ≤ s x - (β : ℝ) * F x := by
    -- Maximality at the fixed slope makes every feasible score no larger than the active one.
    simpa [smoothedPrimalObjectiveMaximand] using (isMaxOn_iff.mp hx_max) y hy_hatP
  -- Rewrite the difference in shifted score form and cancel the common active value.
  rw [ContinuousLinearMap.map_sub, mul_sub]
  linarith

/-- Helper for Lemma 7.10: the fixed argmax at slope `s` is exactly a minimizer of the
unperturbed tilted objective `z ↦ β * F z - s z` on the feasible set `hatP`. -/
private theorem supportFunctionApproximationUnperturbedTiltedObjective_isMinOn_of_fixedArgmax
    {s : StrongDual ℝ E} {x : E}
    (hx_argmax : x ∈ Argmaxβ hatP F β s) :
    IsMinOn (fun z : E ↦ (β : ℝ) * F z - s z) hatP x := by
  rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff] at hx_argmax
  rcases hx_argmax with ⟨hx_hatP, hx_max⟩
  refine isMinOn_iff.mpr ?_
  intro y hy_hatP
  have hy_score_le : s y - (β : ℝ) * F y ≤ s x - (β : ℝ) * F x := by
    -- The maximizing score at slope `s` becomes the minimizing tilted objective after
    -- moving every term to the opposite side.
    simpa [smoothedPrimalObjectiveMaximand] using (isMaxOn_iff.mp hx_max) y hy_hatP
  have htilted_le : (β : ℝ) * F x - s x ≤ (β : ℝ) * F y - s y := by
    linarith
  exact htilted_le

/-- Helper for Lemma 7.10: scaling the standard self-concordant barrier `F` by the positive
parameter `β` produces the Chapter 5 self-concordant owner with constant `1 / √β` on the same
interior domain. -/
private theorem supportFunctionApproximation_scaledBarrier_isSelfConcordant
    [IsStandardSelfConcordantOn (interior Q) F] :
    let βnn : NNReal := ⟨(β : ℝ), β.2.le⟩
    IsSelfConcordantOnWith (interior Q) (1 / NNReal.sqrt βnn) ((β : ℝ) • F) := by
  let βnn : NNReal := ⟨(β : ℝ), β.2.le⟩
  have hβnn_pos : 0 < βnn := by
    change 0 < (β : ℝ)
    exact β.2
  let βu : NNRealˣ := Units.mk0 βnn (by
    exact ne_of_gt hβnn_pos)
  have hself : IsSelfConcordantOnWith (interior Q) (1 : NNReal) F := inferInstance
  -- Route correction: the Chapter 5 `ω_*` route for the barrier-tilt term should first move to
  -- the scaled objective `(β : ℝ) • F`, where the self-concordance constant is `1 / √β`.
  simpa [βnn, βu, IsStandardSelfConcordantOn] using
    IsSelfConcordantOnWith.pos_smul hself βu

/-- Helper for Lemma 7.10: the pure source barrier-tilt quantity is exactly the objective gap of
the affine tilt `z ↦ β * F z - g z`. -/
private theorem supportFunctionApproximationBarrierTiltGap_eq_objectiveGap
    {g : StrongDual ℝ E} {x y : E} :
    g (y - x) - β * (F y - F x) =
      (((β : ℝ) * F x - g x) - ((β : ℝ) * F y - g y)) := by
  -- Expand both endpoint evaluations of the affine tilt and regroup the shared terms.
  rw [ContinuousLinearMap.map_sub, mul_sub]
  ring

/-- Helper for Lemma 7.10: the full perturbed source gap is exactly the value drop of the
`(s + g)`-tilted objective `z ↦ β * F z - (s + g) z`. -/
private theorem supportFunctionApproximationPerturbedGap_eq_tiltedObjectiveGap
    {s g : StrongDual ℝ E} {x y : E} :
    s (y - x) + g (y - x) - β * (F y - F x) =
      (((β : ℝ) * F x - (s + g) x) - ((β : ℝ) * F y - (s + g) y)) := by
  -- Expand the two endpoint evaluations of the combined tilted objective and regroup the
  -- affine-source terms into the displayed perturbed gap.
  rw [ContinuousLinearMap.map_sub, ContinuousLinearMap.map_sub, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.add_apply, mul_sub]
  ring

/-- Helper for Lemma 7.10: the perturbed tilted objective
`ψsg z = β * F z - (s + g) z` stays on the same scaled-barrier Chapter 5 owner surface, and the
source-facing norm / `ω_*` readers rewrite to the determinant-witness owners at the active point
`x`. -/
private theorem supportFunctionApproximationPsiSg_dualNorm_and_omegaStar_adapter_ofDetNeZero
    {s g : StrongDual ℝ E} {x : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hhatP_int : hatP ⊆ interior Q)
    (hx_det : (hessian F x).det ≠ 0)
    (hg :
      supportFunctionApproximationDualLocalNormAt
          hatP Q F β hx_argmax hhatP_int hx_det g <
        (β : ℝ)) :
    let hx_int : x ∈ interior Q := argmaxBeta_mem_interior_of_subset hatP Q F β hx_argmax hhatP_int
    let hPos : (hessian F x).IsPositive :=
      (inferInstance : IsStandardSelfConcordantOn (interior Q) F).hessian_isPositive hx_int
    IsSelfConcordantOnWith (interior Q)
        (1 / NNReal.sqrt ⟨(β : ℝ), β.2.le⟩)
        (fun z : E ↦ (β : ℝ) * F z - (s + g) z) ∧
      supportFunctionApproximationDualLocalNormAt hatP Q F β hx_argmax hhatP_int hx_det g =
        HessianDualLocalNorm.ofDetNeZero F x hPos hx_det g ∧
      supportFunctionApproximationOmegaStarUpperTermOfDetNeZero
          hatP Q F β hx_argmax hhatP_int hx_det g hg =
        (β : ℝ) *
          ω_* (selfConcordantOmegaStarArg (1 : NNReal)
            (HessianDualLocalNorm.ofDetNeZero F x hPos hx_det g / (β : ℝ))
            (by
              have hg_det :
                  HessianDualLocalNorm.ofDetNeZero F x hPos hx_det g <
                    (β : ℝ) := by
                simpa [supportFunctionApproximationDualLocalNormAt, hx_int, hPos] using hg
              simpa [one_mul] using
                (div_lt_iff₀ β.2).2
                  (show HessianDualLocalNorm.ofDetNeZero F x hPos hx_det g < 1 * (β : ℝ) by
                    simpa using hg_det))) := by
  let hx_int : x ∈ interior Q := argmaxBeta_mem_interior_of_subset hatP Q F β hx_argmax hhatP_int
  let hPos : (hessian F x).IsPositive :=
    (inferInstance : IsStandardSelfConcordantOn (interior Q) F).hessian_isPositive hx_int
  constructor
  · have hscaled :
        IsSelfConcordantOnWith (interior Q)
          (1 / NNReal.sqrt ⟨(β : ℝ), β.2.le⟩) ((β : ℝ) • F) := by
      simpa using
        supportFunctionApproximation_scaledBarrier_isSelfConcordant Q F β
    have hzero_pos : (0 : E →L[ℝ] E).IsPositive := ContinuousLinearMap.isPositive_zero
    have htilt :
        IsSelfConcordantOnWith (interior Q)
          (1 / NNReal.sqrt ⟨(β : ℝ), β.2.le⟩)
          (quadraticAffineObjective 0
            (-((InnerProductSpace.toDual ℝ E).symm (s + g)))
            (0 : E →L[ℝ] E) + ((β : ℝ) • F)) := by
      simpa using
        IsSelfConcordantOnWith.add_quadraticAffineObjective hscaled 0
          (-((InnerProductSpace.toDual ℝ E).symm (s + g)))
          (0 : E →L[ℝ] E) hzero_pos
    -- Route correction: isolate the affine-tilt packaging once so the closing upper-gap proof can
    -- stay on the exact source surface `ψsg z = β * F z - (s + g) z`.
    have hψeq :
        quadraticAffineObjective 0
            (-((InnerProductSpace.toDual ℝ E).symm (s + g)))
            (0 : E →L[ℝ] E) + ((β : ℝ) • F) =
          (fun z : E ↦ (β : ℝ) * F z - (s + g) z) := by
      funext z
      calc
        (quadraticAffineObjective 0
              (-((InnerProductSpace.toDual ℝ E).symm (s + g)))
              (0 : E →L[ℝ] E) + ((β : ℝ) • F)) z
            = inner ℝ (-((InnerProductSpace.toDual ℝ E).symm (s + g))) z +
                (β : ℝ) * F z := by
                  simp [quadraticAffineObjective]
        _ = -(s + g) z + (β : ℝ) * F z := by
              rw [inner_neg_left, real_inner_comm,
                (dual_apply_eq_inner_toDualSymm (s + g) z).symm]
        _ = (β : ℝ) * F z - (s + g) z := by ring
    rw [hψeq] at htilt
    exact htilt
  · constructor
    · simpa [hx_int, hPos] using
        supportFunctionApproximationDualLocalNormAt_eq_ofPosDefMem
          hatP Q F β hx_argmax hhatP_int hx_det g
    · simpa [hx_int, hPos] using
        supportFunctionApproximationOmegaStarUpperTermOfDetNeZero_eq_ofPosDefMem
          hatP Q F β hx_argmax hhatP_int hx_det g hg

/-- Helper for Lemma 7.10: the exact perturbed tilted-objective drop splits into the linear
perturbation pairing minus the unperturbed tilted-objective increment. -/
private theorem supportFunctionApproximationPerturbedTiltedObjectiveDrop_eq_linear_minus_unperturbed
    {s g : StrongDual ℝ E} {x y : E} :
    ((β : ℝ) * F x - (s + g) x) - ((β : ℝ) * F y - (s + g) y) =
      g (y - x) - (((β : ℝ) * F y - s y) - ((β : ℝ) * F x - s x)) := by
  -- Expand both endpoint evaluations and regroup the affine and barrier terms once.
  rw [ContinuousLinearMap.map_sub, ContinuousLinearMap.map_sub, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.add_apply, mul_sub]
  ring

/-- Helper for Lemma 7.10: at the active point `x`, the perturbation pairing against `y - x` is
bounded by the determinant-witness dual local norm times the barrier local norm. -/
private theorem supportFunctionApproximationPerturbationPairing_le_ofDetNeZero
    {s g : StrongDual ℝ E} {x y : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hhatP_int : hatP ⊆ interior Q)
    (hx_det : (hessian F x).det ≠ 0) :
    g (y - x) ≤
      supportFunctionApproximationDualLocalNormAt
          hatP Q F β hx_argmax hhatP_int hx_det g *
        ‖y - x‖[F; x] := by
  let hx_int : x ∈ interior Q :=
    argmaxBeta_mem_interior_of_subset hatP Q F β hx_argmax hhatP_int
  let hPos : (hessian F x).IsPositive :=
    (inferInstance : IsStandardSelfConcordantOn (interior Q) F).hessian_isPositive hx_int
  have habs :
      |inner ℝ ((InnerProductSpace.toDual ℝ E).symm g) (y - x)| ≤
        HessianDualLocalNorm.ofDetNeZero F x hPos hx_det g * ‖y - x‖[F; x] := by
    -- Apply the Chapter 5 dual/local Cauchy inequality at the active point `x`.
    simpa using
      abs_inner_le_hessianDualLocalNorm_mul_hessianLocalNorm_of_detNeZero
        (F := F)
        (x := x)
        (v := (InnerProductSpace.toDual ℝ E).symm g)
        (z := y - x)
        hPos
        hx_det
  have hpair :
      inner ℝ ((InnerProductSpace.toDual ℝ E).symm g) (y - x) = g (y - x) := by
    -- Rewrite the Euclidean pairing back to the dual evaluation spelling used in Lemma 7.10.
    simpa using (dual_apply_eq_inner_toDualSymm g (y - x)).symm
  have hbound :
      |g (y - x)| ≤
        supportFunctionApproximationDualLocalNormAt
            hatP Q F β hx_argmax hhatP_int hx_det g *
          ‖y - x‖[F; x] := by
    -- Replace the determinant-witness norm reader by the source-facing local norm abbreviation.
    simpa [supportFunctionApproximationDualLocalNormAt, hx_int, hPos, hpair] using habs
  -- Drop the absolute value to keep only the upper bound needed by the omega-side route.
  exact le_trans (le_abs_self _) hbound

/-- Helper for Lemma 7.10: evaluating a fixed dual covector is differentiable, and its gradient is
the inverse-Riesz representative of that covector. -/
private theorem supportFunctionApproximationDualApply_hasGradientAt
    (v : StrongDual ℝ E) (x : E) :
    HasGradientAt (fun z : E ↦ v z) ((InnerProductSpace.toDual ℝ E).symm v) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (v.hasFDerivAt : HasFDerivAt (fun z : E ↦ v z) v x) using 1
  ext z
  simpa [InnerProductSpace.toDual_symm_apply, innerSL_apply_apply]

/-- Helper for Lemma 7.10: the perturbed tilt `ψsg z = β * F z - (s + g) z` has the same barrier
gradient as the unperturbed tilt, shifted only by the perturbation covector `g`. -/
private theorem supportFunctionApproximationPerturbedTiltedObjective_gradient_eq
    {s g : StrongDual ℝ E} {x : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_int : x ∈ interior Q) :
    ∇ (fun z : E ↦ (β : ℝ) * F z - (s + g) z) x =
      ∇ (fun z : E ↦ (β : ℝ) * F z - s z) x -
        ((InnerProductSpace.toDual ℝ E).symm g) := by
  have hdiffF : DifferentiableAt ℝ F x := by
    -- Standard self-concordance supplies the ambient differentiability of `F` at interior points.
    exact
      ((inferInstance : IsStandardSelfConcordantOn (interior Q) F).contDiffOn.contDiffAt
        ((inferInstance : IsStandardSelfConcordantOn (interior Q) F).isOpen_domain.mem_nhds
          hx_int)).differentiableAt (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
  have hgradF : HasGradientAt F (∇ F x) x := hdiffF.hasGradientAt
  have hderivF : HasFDerivAt F (innerSL ℝ (∇ F x)) x := hgradF.hasFDerivAt
  have hscaled :
      HasGradientAt (fun z : E ↦ (β : ℝ) * F z) ((β : ℝ) • ∇ F x) x := by
    -- Scale the barrier derivative before subtracting the linear tilts.
    simpa [ContinuousLinearMap.smul_apply, innerSL_apply_apply, real_inner_smul_left,
      smul_eq_mul, hasGradientAt_iff_hasFDerivAt] using
      (hderivF.const_smul (β : ℝ))
  have hs :
      HasGradientAt (fun z : E ↦ s z) ((InnerProductSpace.toDual ℝ E).symm s) x :=
    supportFunctionApproximationDualApply_hasGradientAt s x
  have hsg :
      HasGradientAt (fun z : E ↦ (s + g) z)
        ((InnerProductSpace.toDual ℝ E).symm (s + g)) x :=
    supportFunctionApproximationDualApply_hasGradientAt (s + g) x
  have hunperturbed :
      ∇ (fun z : E ↦ (β : ℝ) * F z - s z) x =
        (β : ℝ) • ∇ F x - ((InnerProductSpace.toDual ℝ E).symm s) := by
    -- First freeze the unperturbed tilt in the same gradient normal form.
    simpa [map_sub] using
      (((hscaled.hasFDerivAt.sub hs.hasFDerivAt).hasGradientAt).gradient)
  have hperturbed :
      ∇ (fun z : E ↦ (β : ℝ) * F z - (s + g) z) x =
        (β : ℝ) • ∇ F x - ((InnerProductSpace.toDual ℝ E).symm (s + g)) := by
    -- Then do the same for the perturbed tilt and compare the two gradients.
    simpa [map_sub] using
      (((hscaled.hasFDerivAt.sub hsg.hasFDerivAt).hasGradientAt).gradient)
  -- Expand the Riesz representative of `s + g` and regroup the perturbation term on the right.
  rw [hperturbed, hunperturbed, map_add]
  abel

/-- Helper for Lemma 7.10: if the unperturbed tilt were stationary at `x`, then the perturbed tilt
would have gradient exactly `-g` there. This isolates the extra premise the stalled Chapter 5
Newton-decrement route would need. -/
private theorem supportFunctionApproximationPerturbedTiltedObjective_gradient_eq_neg_of_stationary
    {s g : StrongDual ℝ E} {x : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_int : x ∈ interior Q)
    (hstationary : ∇ (fun z : E ↦ (β : ℝ) * F z - s z) x = 0) :
    ∇ (fun z : E ↦ (β : ℝ) * F z - (s + g) z) x =
      -((InnerProductSpace.toDual ℝ E).symm g) := by
  -- Substitute the unperturbed stationary equation into the checked gradient-shift identity.
  rw [supportFunctionApproximationPerturbedTiltedObjective_gradient_eq
    Q F β hx_int, hstationary, zero_sub]

/-- Helper for Lemma 7.10: the stationary unperturbed tilt
`z ↦ β * F z - s z` is minimized at the active point `x` on the whole self-concordant domain
`interior Q`. -/
private theorem supportFunctionApproximationStationaryUnperturbedTiltedObjective_isMinOn
    {s : StrongDual ℝ E} {x : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_int : x ∈ interior Q)
    (hstationary : ∇ (fun z : E ↦ (β : ℝ) * F z - s z) x = 0) :
    IsMinOn (fun z : E ↦ (β : ℝ) * F z - s z) (interior Q) x := by
  let βnn : NNReal := ⟨(β : ℝ), β.2.le⟩
  have hscaled :
      IsSelfConcordantOnWith (interior Q) (1 / NNReal.sqrt βnn) ((β : ℝ) • F) := by
    -- First place the scaled barrier on the canonical Chapter 5 owner surface.
    simpa [βnn] using
      supportFunctionApproximation_scaledBarrier_isSelfConcordant Q F β
  have hzero_pos : (0 : E →L[ℝ] E).IsPositive := ContinuousLinearMap.isPositive_zero
  have htilt :
      IsSelfConcordantOnWith (interior Q) (1 / NNReal.sqrt βnn)
        (quadraticAffineObjective 0
          (-((InnerProductSpace.toDual ℝ E).symm s))
          (0 : E →L[ℝ] E) + ((β : ℝ) • F)) := by
    -- Adding the linear tilt `z ↦ -s z` preserves self-concordance on the same open domain.
    simpa using
      IsSelfConcordantOnWith.add_quadraticAffineObjective hscaled 0
        (-((InnerProductSpace.toDual ℝ E).symm s))
        (0 : E →L[ℝ] E) hzero_pos
  have hψeq :
      quadraticAffineObjective 0
          (-((InnerProductSpace.toDual ℝ E).symm s))
          (0 : E →L[ℝ] E) + ((β : ℝ) • F) =
        (fun z : E ↦ (β : ℝ) * F z - s z) := by
    -- Normalize the quadratic-affine packaging back to the exact unperturbed tilt.
    funext z
    calc
      (quadraticAffineObjective 0
            (-((InnerProductSpace.toDual ℝ E).symm s))
            (0 : E →L[ℝ] E) + ((β : ℝ) • F)) z
          = inner ℝ (-((InnerProductSpace.toDual ℝ E).symm s)) z +
              (β : ℝ) * F z := by
                simp [quadraticAffineObjective]
      _ = -s z + (β : ℝ) * F z := by
            rw [inner_neg_left, real_inner_comm, (dual_apply_eq_inner_toDualSymm s z).symm]
      _ = (β : ℝ) * F z - s z := by ring
  have hself :
      IsSelfConcordantOnWith (interior Q) (1 / NNReal.sqrt βnn)
        (fun z : E ↦ (β : ℝ) * F z - s z) := by
    -- Keep the stationary-point convexity step in the exact owner spelling used below.
    simpa [hψeq] using htilt
  have hcontDiff :
      ContDiffAt ℝ 3 (fun z : E ↦ (β : ℝ) * F z - s z) x :=
    hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hx_int)
  have hdiff :
      DifferentiableAt ℝ (fun z : E ↦ (β : ℝ) * F z - s z) x := by
    -- The Chapter 5 owner gives enough smoothness to apply the convex gradient criterion.
    exact hcontDiff.differentiableAt (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
  -- A stationary point of the convex unperturbed tilt is a global minimizer on `interior Q`.
  rw [hself.convexOn.isMinOn_iff_gradient_variational_inequality hx_int hdiff]
  intro y hy
  simp [hstationary]

/-- Helper for Lemma 7.10: the stationary unperturbed tilted-objective gap from `x` to any
interior comparison point is nonnegative. -/
private theorem supportFunctionApproximationStationaryUnperturbedTiltedObjective_gap_nonneg
    {s : StrongDual ℝ E} {x y : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_int : x ∈ interior Q)
    (hy_int : y ∈ interior Q)
    (hstationary : ∇ (fun z : E ↦ (β : ℝ) * F z - s z) x = 0) :
    0 ≤ ((β : ℝ) * F y - s y) - ((β : ℝ) * F x - s x) := by
  have hmin :=
    supportFunctionApproximationStationaryUnperturbedTiltedObjective_isMinOn
      Q F β hx_int hstationary
  -- Read the minimizer statement at `y` as the exact tilted-objective gap inequality.
  simpa [sub_nonneg] using hmin hy_int

/-- Helper for Lemma 7.10: the remaining quantitative input on the omega-side is the exact
base-point lower model for the stationary unperturbed tilt `z ↦ β * F z - s z`. -/
private theorem supportFunctionApproximationStationaryUnperturbedTiltedObjective_gap_ge_omega
    {s : StrongDual ℝ E} {x y : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_int : x ∈ interior Q)
    (hy_int : y ∈ interior Q)
    (hstationary : ∇ (fun z : E ↦ (β : ℝ) * F z - s z) x = 0) :
    ((β : ℝ) * F y - s y) - ((β : ℝ) * F x - s x) ≥
      (β : ℝ) *
        ω (selfConcordantOmegaArg (1 : NNReal)
          ‖y - x‖[F; x]
          (by
            simpa using
              neg_one_lt_selfConcordantUnit_of_nonneg
                (hessianLocalNorm_nonneg F x (y - x)))) := by
  -- TODO: port the Chapter 5 base-distance Taylor-lower-bound proof pattern to
  -- `ψ z = (β : ℝ) * F z - s z`, using `hx_int`, `hy_int`, and `hstationary` to keep the lower
  -- model on the exact stationary unperturbed tilt.
  sorry

/-- Helper for Lemma 7.10: once the exact self-concordant lower model has supplied the
`β * ω(r)` term, the remaining scalar closeout is the scaled Fenchel inequality
`δ r - β ω(r) ≤ β ω_*(δ / β)`. -/
private theorem supportFunctionApproximationFenchelEliminate_baseDistance_beta
    {r δ : ℝ}
    (hr : 0 ≤ r)
    (hδ : 0 ≤ δ)
    (hδβ : δ < (β : ℝ)) :
    δ * r -
        (β : ℝ) *
          ω (selfConcordantOmegaArg (1 : NNReal) r (by
            simpa using neg_one_lt_selfConcordantUnit_of_nonneg hr)) ≤
      (β : ℝ) *
        ω_* (selfConcordantOmegaStarArg (1 : NNReal) (δ / (β : ℝ)) (by
          have hdiv : δ / (β : ℝ) < 1 := by
            simpa [one_mul] using (div_lt_iff₀ β.2).2 hδβ
          simpa [one_mul] using hdiv) := by
  let tω : Set.Ioi (-1 : ℝ) :=
    selfConcordantOmegaArg (1 : NNReal) r (by
      simpa using neg_one_lt_selfConcordantUnit_of_nonneg hr)
  let τω : Set.Iio (1 : ℝ) :=
    selfConcordantOmegaStarArg (1 : NNReal) (δ / (β : ℝ)) (by
      have hdiv : δ / (β : ℝ) < 1 := by
        simpa [one_mul] using (div_lt_iff₀ β.2).2 hδβ
      simpa [one_mul] using hdiv)
  have hcore :
      ω tω + ω_* τω ≥ (δ / (β : ℝ)) * r := by
    -- Apply the unit-scale Fenchel inequality at `t = r` and `τ = δ / β`.
    have hdiv : δ / (β : ℝ) < 1 := by
      simpa [one_mul] using (div_lt_iff₀ β.2).2 hδβ
    simpa [tω, τω] using
      (selfConcordantOmega_add_selfConcordantOmegaStar_ge_mul
        (t := r) (τ := δ / (β : ℝ)) hr hdiv)
  have hscaled :
      (β : ℝ) * ((δ / (β : ℝ)) * r) ≤
        (β : ℝ) * (ω tω + ω_* τω) := by
    -- Scale the unit Fenchel inequality by the positive smoothing parameter `β`.
    exact mul_le_mul_of_nonneg_left hcore β.2.le
  have hrewrite :
      (β : ℝ) * ((δ / (β : ℝ)) * r) = δ * r := by
    field_simp [β.2.ne']
  -- Rearrange the scaled Fenchel inequality into the exact scalar closeout used in Lemma 7.10.
  linarith [hscaled, hrewrite]

/-- Helper for Lemma 7.10: the perturbed score gap splits into the fixed active-score gap plus
the linear perturbation term. -/
private theorem supportFunctionApproximationPerturbedGap_eq_activeScoreGap_add_linearPerturbation
    {s g : StrongDual ℝ E} {x y : E} :
    s (y - x) + g (y - x) - β * (F y - F x) =
      (s (y - x) - β * (F y - F x)) + g (y - x) := by
  -- Expand the common subtraction once so the extra perturbation term separates cleanly.
  rw [sub_eq_add_neg]
  ring

/-- Helper for Lemma 7.10: the scalar left-hand side in the one-dimensional counterexample from the
statement-stage blocker rewrites to `log (11 / 10) - 19 / 200`. -/
private theorem lemma710CounterexamplePerturbedGap_eq :
    (-((24 : ℝ) / 25)) * (((11 : ℝ) / 10) - 1) +
        ((1 : ℝ) / 100) * (((11 : ℝ) / 10) - 1) -
        (((-Real.log ((11 : ℝ) / 10)) : ℝ) - (-Real.log (1 : ℝ))) =
      Real.log ((11 : ℝ) / 10) - 19 / 200 := by
  -- Expand the scalar arithmetic and use `log 1 = 0` to normalize the barrier difference.
  rw [Real.log_one]
  ring_nf

/-- Helper for Lemma 7.10: the scalar `ω_*` term in the same counterexample rewrites to the exact
closed form `-1 / 100 - log (99 / 100)`. -/
private theorem lemma710CounterexampleOmegaStar_eq :
    ω_* (show Set.Iio (1 : ℝ) from ⟨(1 : ℝ) / 100, by norm_num⟩) =
      -((1 : ℝ) / 100) - Real.log ((99 : ℝ) / 100) := by
  -- Unfold the Chapter 5 owner at the concrete subtype argument and simplify the denominator.
  simp [selfConcordantOmegaStar]
  ring_nf

/-- Helper for Lemma 7.10: the one-dimensional counterexample reduces the disputed perturbed-gap
comparison exactly to the scalar inequality
`log (11 / 10) - 19 / 200 ≤ -1 / 100 - log (99 / 100)`. -/
private theorem lemma710CounterexampleGapLeOmega_iff :
    (-((24 : ℝ) / 25)) * (((11 : ℝ) / 10) - 1) +
        ((1 : ℝ) / 100) * (((11 : ℝ) / 10) - 1) -
        (((-Real.log ((11 : ℝ) / 10)) : ℝ) - (-Real.log (1 : ℝ))) ≤
      ω_* (show Set.Iio (1 : ℝ) from ⟨(1 : ℝ) / 100, by norm_num⟩) ↔
        Real.log ((11 : ℝ) / 10) - 19 / 200 ≤
          -((1 : ℝ) / 100) - Real.log ((99 : ℝ) / 100) := by
  -- Normalize the concrete left and right sides once so the defect report can cite the exact
  -- scalar inequality induced by the current theorem surface.
  rw [lemma710CounterexamplePerturbedGap_eq, lemma710CounterexampleOmegaStar_eq]

/-- Helper for Lemma 7.10: the normalized scalar counterexample inequality is strictly reversed,
so the claimed `ω_*` upper bound already fails after reducing to
`log (11 / 10) - 19 / 200 ≤ -1 / 100 - log (99 / 100)`. -/
private theorem lemma710CounterexampleGapGtOmega :
    Real.log ((11 : ℝ) / 10) - 19 / 200 >
      -((1 : ℝ) / 100) - Real.log ((99 : ℝ) / 100) := by
  have hnonneg : (0 : ℝ) ≤ 89 / 1000 := by
    norm_num
  have hlogLower :
      (2 : ℝ) * (89 / 1000) / (89 / 1000 + 2) ≤ Real.log (1 + 89 / 1000) :=
    Real.le_log_one_add_of_nonneg hnonneg
  have hfrac :
      (17 : ℝ) / 200 < (2 : ℝ) * (89 / 1000) / (89 / 1000 + 2) := by
    norm_num
  have hsum :
      (17 : ℝ) / 200 <
        Real.log ((11 : ℝ) / 10) + Real.log ((99 : ℝ) / 100) := by
    have hmain : (17 : ℝ) / 200 < Real.log (1 + 89 / 1000) :=
      lt_of_lt_of_le hfrac hlogLower
    have h11 : ((11 : ℝ) / 10) ≠ 0 := by
      norm_num
    have h99 : ((99 : ℝ) / 100) ≠ 0 := by
      norm_num
    -- Collapse the two logarithms to `log (1089 / 1000) = log (1 + 89 / 1000)`.
    calc
      (17 : ℝ) / 200 < Real.log (1 + 89 / 1000) := hmain
      _ = Real.log (((11 : ℝ) / 10) * ((99 : ℝ) / 100)) := by
            congr 1
            norm_num
      _ = Real.log ((11 : ℝ) / 10) + Real.log ((99 : ℝ) / 100) := by
            rw [Real.log_mul h11 h99]
  -- Rearrange the normalized inequality to the summed-log lower bound proved above.
  linarith

/-- Helper for Lemma 7.10: the exact scalar inequality induced by the current theorem surface is
false in the one-dimensional log-barrier counterexample. -/
private theorem lemma710CounterexampleGapLeOmega_false :
    ¬ ((-((24 : ℝ) / 25)) * (((11 : ℝ) / 10) - 1) +
        ((1 : ℝ) / 100) * (((11 : ℝ) / 10) - 1) -
        (((-Real.log ((11 : ℝ) / 10)) : ℝ) - (-Real.log (1 : ℝ))) ≤
      ω_* (show Set.Iio (1 : ℝ) from ⟨(1 : ℝ) / 100, by norm_num⟩)) := by
  rw [lemma710CounterexampleGapLeOmega_iff]
  linarith [lemma710CounterexampleGapGtOmega]

/-- Helper for Lemma 7.10: the exact perturbed source gap should be controlled directly by the
`(s + g)`-tilted self-concordant objective, rather than by the false pure barrier-tilt surface. -/
private theorem supportFunctionApproximationPerturbedTiltedObjectiveDropUpperBoundOfDetNeZero_of_unperturbedLowerModel
    {s g : StrongDual ℝ E} {x y : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hhatP_int : hatP ⊆ interior Q)
    (hx_det : (hessian F x).det ≠ 0)
    (hg :
      supportFunctionApproximationDualLocalNormAt
          hatP Q F β hx_argmax hhatP_int hx_det g <
        (β : ℝ))
    (homega :
      ((β : ℝ) * F y - s y) - ((β : ℝ) * F x - s x) ≥
        (β : ℝ) *
          ω (selfConcordantOmegaArg (1 : NNReal)
            ‖y - x‖[F; x]
            (by
              simpa using
                neg_one_lt_selfConcordantUnit_of_nonneg
                  (hessianLocalNorm_nonneg F x (y - x))))) :
    ((β : ℝ) * F x - (s + g) x) - ((β : ℝ) * F y - (s + g) y) ≤
      supportFunctionApproximationOmegaStarUpperTermOfDetNeZero
        hatP Q F β hx_argmax hhatP_int hx_det g hg := by
  let hx_int : x ∈ interior Q :=
    argmaxBeta_mem_interior_of_subset hatP Q F β hx_argmax hhatP_int
  let hPos : (hessian F x).IsPositive :=
    (inferInstance : IsStandardSelfConcordantOn (interior Q) F).hessian_isPositive hx_int
  let hInv : (hessian F x).IsInvertible := hessian_isInvertible_of_det_ne_zero hx_det
  have hdecomp :
      ((β : ℝ) * F x - (s + g) x) - ((β : ℝ) * F y - (s + g) y) =
        g (y - x) - (((β : ℝ) * F y - s y) - ((β : ℝ) * F x - s x)) := by
    -- First separate the perturbation pairing from the stationary unperturbed-tilt gap.
    exact
      supportFunctionApproximationPerturbedTiltedObjectiveDrop_eq_linear_minus_unperturbed
        F β
  have hpair :
      g (y - x) ≤
        supportFunctionApproximationDualLocalNormAt
            hatP Q F β hx_argmax hhatP_int hx_det g *
          ‖y - x‖[F; x] := by
    -- The perturbation pairing is controlled by the determinant-witness dual norm at `x`.
    exact
      supportFunctionApproximationPerturbationPairing_le_ofDetNeZero
        hatP Q F β hx_argmax hhatP_int hx_det
  have hr_nonneg : 0 ≤ ‖y - x‖[F; x] := hessianLocalNorm_nonneg F x (y - x)
  have hδ_nonneg :
      0 ≤
        supportFunctionApproximationDualLocalNormAt
          hatP Q F β hx_argmax hhatP_int hx_det g := by
    -- The determinant-witness dual local norm is nonnegative by construction.
    change 0 ≤ HessianDualLocalNorm.ofDetNeZero F x hPos hx_det g
    rw [HessianDualLocalNorm.ofDetNeZero_def]
    simpa [hInv] using dualLocalNorm_nonneg F x hPos hInv g
  have hfenchel :
      supportFunctionApproximationDualLocalNormAt
            hatP Q F β hx_argmax hhatP_int hx_det g *
          ‖y - x‖[F; x] -
        (β : ℝ) *
          ω (selfConcordantOmegaArg (1 : NNReal)
            ‖y - x‖[F; x]
            (by
              simpa using
                neg_one_lt_selfConcordantUnit_of_nonneg
                  (hessianLocalNorm_nonneg F x (y - x)))) ≤
      supportFunctionApproximationOmegaStarUpperTermOfDetNeZero
        hatP Q F β hx_argmax hhatP_int hx_det g hg := by
    -- Eliminate the base local distance in favor of the canonical `ω_*` remainder.
    simpa [supportFunctionApproximationOmegaStarUpperTermOfDetNeZero] using
      supportFunctionApproximationFenchelEliminate_baseDistance_beta
        (β := β)
        hr_nonneg
        hδ_nonneg
        hg
  have hmain :
      ((β : ℝ) * F x - (s + g) x) - ((β : ℝ) * F y - (s + g) y) ≤
        supportFunctionApproximationDualLocalNormAt
            hatP Q F β hx_argmax hhatP_int hx_det g *
          ‖y - x‖[F; x] -
          (β : ℝ) *
            ω (selfConcordantOmegaArg (1 : NNReal)
              ‖y - x‖[F; x]
              (by
                simpa using
                  neg_one_lt_selfConcordantUnit_of_nonneg
                    (hessianLocalNorm_nonneg F x (y - x)))) := by
    -- Combine the exact decomposition with the pairing bound and the supplied lower model.
    rw [hdecomp]
    linarith
  -- The exact closeout is now only the scaled Fenchel inequality for `(δ, r)`.
  exact hmain.trans hfenchel

/-- Helper for Lemma 7.10: the exact perturbed source gap should be controlled directly by the
`(s + g)`-tilted self-concordant objective, rather than by the false pure barrier-tilt surface. -/
private theorem supportFunctionApproximationPerturbedTiltedObjectiveDropUpperBoundOfDetNeZero
    {s g : StrongDual ℝ E} {x y : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hhatP_int : hatP ⊆ interior Q)
    (hstationary : ∇ (fun z : E ↦ (β : ℝ) * F z - s z) x = 0)
    (hx_det : (hessian F x).det ≠ 0)
    (hg :
      supportFunctionApproximationDualLocalNormAt
          hatP Q F β hx_argmax hhatP_int hx_det g <
        (β : ℝ))
    (hy_hatP : y ∈ hatP) :
    ((β : ℝ) * F x - (s + g) x) - ((β : ℝ) * F y - (s + g) y) ≤
      supportFunctionApproximationOmegaStarUpperTermOfDetNeZero
        hatP Q F β hx_argmax hhatP_int hx_det g hg := by
  let hx_int : x ∈ interior Q :=
    argmaxBeta_mem_interior_of_subset hatP Q F β hx_argmax hhatP_int
  have hy_int : y ∈ interior Q := hhatP_int hy_hatP
  have homega :
      ((β : ℝ) * F y - s y) - ((β : ℝ) * F x - s x) ≥
        (β : ℝ) *
          ω (selfConcordantOmegaArg (1 : NNReal)
            ‖y - x‖[F; x]
            (by
              simpa using
                neg_one_lt_selfConcordantUnit_of_nonneg
                  (hessianLocalNorm_nonneg F x (y - x)))) := by
    -- Route correction: the false barrier-only split is gone; the remaining blocker is exactly the
    -- Chapter 5 base-point lower model for the stationary unperturbed tilt.
    exact
      supportFunctionApproximationStationaryUnperturbedTiltedObjective_gap_ge_omega
        Q F β hx_int hy_int hstationary
  -- Once that lower model is supplied, the perturbation pairing and Fenchel closeout finish the
  -- exact `(s + g)`-tilted objective drop.
  exact
    supportFunctionApproximationPerturbedTiltedObjectiveDropUpperBoundOfDetNeZero_of_unperturbedLowerModel
      hatP Q F β hx_argmax hhatP_int hx_det hg homega

/-- Helper for Lemma 7.10: the full perturbed source gap is bounded once the exact
`(s + g)`-tilted objective drop from the active point `x` is bounded by the determinant-witness
`ω_*` term. -/
private theorem supportFunctionApproximationPerturbedObjectiveGapUpperBoundOfDetNeZero
    {s g : StrongDual ℝ E} {x y : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hhatP_int : hatP ⊆ interior Q)
    (hstationary : ∇ (fun z : E ↦ (β : ℝ) * F z - s z) x = 0)
    (hx_det : (hessian F x).det ≠ 0)
    (hg :
      supportFunctionApproximationDualLocalNormAt
          hatP Q F β hx_argmax hhatP_int hx_det g <
        (β : ℝ))
    (hy_hatP : y ∈ hatP) :
    s (y - x) + g (y - x) - β * (F y - F x) ≤
      supportFunctionApproximationOmegaStarUpperTermOfDetNeZero
        hatP Q F β hx_argmax hhatP_int hx_det g hg := by
  -- Rewrite the perturbed source gap onto the exact tilted-objective drop and invoke the
  -- dedicated owner-level Chapter 5 blocker.
  calc
    s (y - x) + g (y - x) - β * (F y - F x)
        = ((β : ℝ) * F x - (s + g) x) - ((β : ℝ) * F y - (s + g) y) := by
            exact supportFunctionApproximationPerturbedGap_eq_tiltedObjectiveGap
              F β
    _ ≤
        supportFunctionApproximationOmegaStarUpperTermOfDetNeZero
          hatP Q F β hx_argmax hhatP_int hx_det g hg := by
            exact
              supportFunctionApproximationPerturbedTiltedObjectiveDropUpperBoundOfDetNeZero
                hatP Q F β hx_argmax hhatP_int hstationary hx_det hg hy_hatP

/-- Helper for Lemma 7.10: after freezing the active value at `x`, the only remaining source-level
perturbed gap is the base-point-free increment
`s (y - x) + g (y - x) - β * (F y - F x)`. -/
private theorem supportFunctionApproximationPerturbedGapUpperBoundOfDetNeZero
    {s g : StrongDual ℝ E} {x : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hhatP_int : hatP ⊆ interior Q)
    (hstationary : ∇ (fun z : E ↦ (β : ℝ) * F z - s z) x = 0)
    (hx_det : (hessian F x).det ≠ 0)
    (hg :
      supportFunctionApproximationDualLocalNormAt
          hatP Q F β hx_argmax hhatP_int hx_det g <
        (β : ℝ))
    {y : E} (hy_hatP : y ∈ hatP) :
    s (y - x) + g (y - x) - β * (F y - F x) ≤
      supportFunctionApproximationOmegaStarUpperTermOfDetNeZero
        hatP Q F β hx_argmax hhatP_int hx_det g hg := by
  -- The repaired owner-level route is now exactly the combined tilted-objective gap theorem.
  simpa using
    supportFunctionApproximationPerturbedObjectiveGapUpperBoundOfDetNeZero
      hatP Q F β hx_argmax hhatP_int hstationary hx_det hg hy_hatP

/-- Helper for Lemma 7.10: every feasible perturbed payoff at slope `s + g` is controlled by the
fixed active value at `s`, the perturbation pairing at `x`, and the determinant-witness
`ω_*` remainder once the exact base-point-free perturbed gap has been paid. -/
private theorem supportFunctionApproximationPerturbedPayoffUpperBoundOfDetNeZero
    {s g : StrongDual ℝ E} {x : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hhatP_int : hatP ⊆ interior Q)
    (hstationary : ∇ (fun z : E ↦ (β : ℝ) * F z - s z) x = 0)
    (hx_det : (hessian F x).det ≠ 0)
    (hg :
      supportFunctionApproximationDualLocalNormAt
          hatP Q F β hx_argmax hhatP_int hx_det g <
        (β : ℝ))
    {y : E} (hy_hatP : y ∈ hatP) :
    (s + g) (y - x0) - β * (F y - F x0) ≤
      Uβ hatP F x0 β s +
        g (x - x0) +
          supportFunctionApproximationOmegaStarUpperTermOfDetNeZero
            hatP Q F β hx_argmax hhatP_int hx_det g hg := by
  have hx_value :
      Uβ hatP F x0 β s = s (x - x0) - β * (F x - F x0) :=
    supportFunctionApproximation_value_eq_of_fixedArgmax hatP F x0 β hx_argmax
  have hgap :=
    supportFunctionApproximationPerturbedGapUpperBoundOfDetNeZero
      hatP Q F β hx_argmax hhatP_int hstationary hx_det hg hy_hatP
  -- Freeze the active owner value at `x`, then pay only the remaining base-point-free perturbed
  -- gap.
  calc
    (s + g) (y - x0) - β * (F y - F x0)
        = Uβ hatP F x0 β s +
            g (x - x0) +
              (s (y - x) + g (y - x) - β * (F y - F x)) := by
                have hsy0 : s (y - x0) = s y - s x0 := by
                  rw [ContinuousLinearMap.map_sub]
                have hgy0 : g (y - x0) = g y - g x0 := by
                  rw [ContinuousLinearMap.map_sub]
                have hsx0 : s (x - x0) = s x - s x0 := by
                  rw [ContinuousLinearMap.map_sub]
                have hgx0 : g (x - x0) = g x - g x0 := by
                  rw [ContinuousLinearMap.map_sub]
                have hsyx : s (y - x) = s y - s x := by
                  rw [ContinuousLinearMap.map_sub]
                have hgyx : g (y - x) = g y - g x := by
                  rw [ContinuousLinearMap.map_sub]
                rw [hx_value, ContinuousLinearMap.add_apply, hsy0, hgy0, hsx0, hgx0, hsyx, hgyx,
                  mul_sub, mul_sub]
                ring
    _ ≤
        Uβ hatP F x0 β s +
          g (x - x0) +
            supportFunctionApproximationOmegaStarUpperTermOfDetNeZero
              hatP Q F β hx_argmax hhatP_int hx_det g hg := by
                linarith

/-- Helper for Lemma 7.10: rewriting the perturbed payoff bound onto the unshifted owner score
surface gives a common upper bound for the exact `Uβ_apply` score image at slope `s + g`. -/
private theorem supportFunctionApproximationPerturbedScoreUpperBoundOfDetNeZero
    {s g : StrongDual ℝ E} {x : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hhatP_int : hatP ⊆ interior Q)
    (hstationary : ∇ (fun z : E ↦ (β : ℝ) * F z - s z) x = 0)
    (hx_det : (hessian F x).det ≠ 0)
    (hg :
      supportFunctionApproximationDualLocalNormAt
          hatP Q F β hx_argmax hhatP_int hx_det g <
        (β : ℝ))
    {y : E} (hy_hatP : y ∈ hatP) :
    (s + g) y - β * F y ≤
      Uβ hatP F x0 β s +
        g (x - x0) +
          supportFunctionApproximationOmegaStarUpperTermOfDetNeZero
            hatP Q F β hx_argmax hhatP_int hx_det g hg +
          ((s + g) x0 - β * F x0) := by
  have hpayoff :=
    supportFunctionApproximationPerturbedPayoffUpperBoundOfDetNeZero
      hatP Q F x0 β hx_argmax hhatP_int hstationary hx_det hg hy_hatP
  -- Expand the shifted payoff once so the owner score matches the `Uβ_apply` image spelling.
  calc
    (s + g) y - β * F y
        = ((s + g) (y - x0) - β * (F y - F x0)) + ((s + g) x0 - β * F x0) := by
            rw [ContinuousLinearMap.map_sub, mul_sub]
            ring
    _ ≤
        (Uβ hatP F x0 β s +
            g (x - x0) +
              supportFunctionApproximationOmegaStarUpperTermOfDetNeZero
                hatP Q F β hx_argmax hhatP_int hx_det g hg) +
          ((s + g) x0 - β * F x0) := by
            gcongr
    _ =
        Uβ hatP F x0 β s +
          g (x - x0) +
            supportFunctionApproximationOmegaStarUpperTermOfDetNeZero
              hatP Q F β hx_argmax hhatP_int hx_det g hg +
            ((s + g) x0 - β * F x0) := by
              ring

/-- Helper for Lemma 7.10: the exact `Uβ_apply` score image at the concrete perturbed slope `s + g`
is bounded above by the constant from the owner-level perturbed-payoff estimate. -/
private theorem supportFunctionApproximationScoreImageBddAboveOfDetNeZero
    (xBase : E)
    {s g : StrongDual ℝ E} {x : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hhatP_int : hatP ⊆ interior Q)
    (hstationary : ∇ (fun z : E ↦ (β : ℝ) * F z - s z) x = 0)
    (hx_det : (hessian F x).det ≠ 0)
    (hg :
      supportFunctionApproximationDualLocalNormAt
          hatP Q F β hx_argmax hhatP_int hx_det g <
        (β : ℝ)) :
    BddAbove ((fun y : E ↦ (s + g) y - β * F y) '' hatP) := by
  refine ⟨Uβ hatP F xBase β s +
      g (x - xBase) +
        supportFunctionApproximationOmegaStarUpperTermOfDetNeZero
          hatP Q F β hx_argmax hhatP_int hx_det g hg +
        ((s + g) xBase - β * F xBase), ?_⟩
  rintro z ⟨y, hy_hatP, rfl⟩
  -- Reuse the normalized pointwise score estimate at the same feasible point `y`.
  exact
    supportFunctionApproximationPerturbedScoreUpperBoundOfDetNeZero
      hatP Q F xBase β hx_argmax hhatP_int hstationary hx_det hg hy_hatP

/-- Helper for Lemma 7.10: once the perturbed score image is bounded above, one `csSup_le` step
closes the owner-level upper model for the concrete perturbation `s + g`. -/
private theorem supportFunctionApproximationUpperModelOfDetNeZero
    {s g : StrongDual ℝ E} {x : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hhatP_int : hatP ⊆ interior Q)
    (hstationary : ∇ (fun z : E ↦ (β : ℝ) * F z - s z) x = 0)
    (hx_det : (hessian F x).det ≠ 0)
    (hg :
      supportFunctionApproximationDualLocalNormAt
          hatP Q F β hx_argmax hhatP_int hx_det g <
        (β : ℝ)) :
    Uβ hatP F x0 β (s + g) ≤
      Uβ hatP F x0 β s +
        g (x - x0) +
          supportFunctionApproximationOmegaStarUpperTermOfDetNeZero
            hatP Q F β hx_argmax hhatP_int hx_det g hg := by
  have hx_hatP : x ∈ hatP := by
    -- Expand the active-owner membership once to recover the feasible witness for `csSup_le`.
    rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff] at hx_argmax
    exact hx_argmax.1
  let scoreSet : Set ℝ := ((fun y : E ↦ (s + g) y - β * F y) '' hatP)
  have hsSup_le :
      sSup scoreSet ≤
        Uβ hatP F x0 β s +
          g (x - x0) +
            supportFunctionApproximationOmegaStarUpperTermOfDetNeZero
              hatP Q F β hx_argmax hhatP_int hx_det g hg +
            ((s + g) x0 - β * F x0) := by
    refine csSup_le ?_ ?_
    · exact ⟨(s + g) x - β * F x, ⟨x, hx_hatP, rfl⟩⟩
    · rintro z ⟨y, hy_hatP, rfl⟩
      simpa [scoreSet] using
        supportFunctionApproximationPerturbedScoreUpperBoundOfDetNeZero
          hatP Q F x0 β hx_argmax hhatP_int hstationary hx_det hg hy_hatP
  rw [Uβ_apply]
  -- Remove the common constant `-(s + g) x0 + β F x0` from the `Uβ_apply` spelling.
  linarith

/-- Helper for Lemma 7.10: at the base parameter `α = 0`, the fixed-slope affine-supremum
presentation already attains the owner value at the unique active point `x`. -/
private theorem supportFunctionApproximationLineSliceAffineSupremumAtZero_eq_owner
    {s : StrongDual ℝ E} {x : E} (d : E)
    (hx_argmax : x ∈ Argmaxβ hatP F β s) :
    let t : E := (InnerProductSpace.toDual ℝ E).symm s
    let a : E → ℝ := fun u ↦ inner ℝ (u - x0) t - β * (F u - F x0)
    let slice : ℝ → hatP → WithTop ℝ := fun α u ↦
      ((a u.1 + α * inner ℝ (u.1 - x0) d : ℝ) : WithTop ℝ)
    pointwiseSupremumOn (Set.univ : Set hatP) slice 0 =
      ((Uβ hatP F x0 β s : ℝ) : WithTop ℝ) := by
  let t : E := (InnerProductSpace.toDual ℝ E).symm s
  let a : E → ℝ := fun u ↦ inner ℝ (u - x0) t - β * (F u - F x0)
  let slice : ℝ → hatP → WithTop ℝ := fun α u ↦
    ((a u.1 + α * inner ℝ (u.1 - x0) d : ℝ) : WithTop ℝ)
  have hx_hatP : x ∈ hatP := by
    -- Unpack the active-owner witness once to recover feasibility of `x`.
    rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff] at hx_argmax
    exact hx_argmax.1
  let u0 : hatP := ⟨x, hx_hatP⟩
  have hx_value :
      Uβ hatP F x0 β s = a x := by
    -- Rewrite the fixed owner value in the exact affine-intercept spelling.
    have hvalue :
        Uβ hatP F x0 β s = s (x - x0) - β * (F x - F x0) :=
      supportFunctionApproximation_value_eq_of_fixedArgmax hatP F x0 β hx_argmax
    have hpair : s (x - x0) = inner ℝ (x - x0) t := by
      simpa [t] using dual_apply_eq_inner_toDualSymm s (x - x0)
    calc
      Uβ hatP F x0 β s = s (x - x0) - β * (F x - F x0) := hvalue
      _ = inner ℝ (x - x0) t - β * (F x - F x0) := by rw [hpair]
      _ = a x := by simp [a]
  apply le_antisymm
  · -- Every feasible zero-slice lies below the owner value at `s`.
    refine ClosedConvexOn.pointwiseSupremumOn_le_of_forall_le ⟨u0, by simp⟩ ?_
    intro u hu
    have hu_score_le :
        s (u.1 - x0) - β * (F u.1 - F x0) ≤
          s (x - x0) - β * (F x - F x0) := by
      -- Maximality at the base slope `s` dominates every feasible affine intercept.
      have hgap :=
        supportFunctionApproximationActiveScoreGapNonposOfFixedArgmax
          hatP F β hx_argmax u.2
      have hsplit :
          s (u.1 - x0) - β * (F u.1 - F x0) =
            (s (x - x0) - β * (F x - F x0)) +
              (s (u.1 - x) - β * (F u.1 - F x)) := by
        rw [ContinuousLinearMap.map_sub, ContinuousLinearMap.map_sub, ContinuousLinearMap.map_sub,
          mul_sub, mul_sub, mul_sub]
        ring
      rw [hsplit]
      linarith
    have hu_value :
        a u.1 ≤ Uβ hatP F x0 β s := by
      have hu_pair : s (u.1 - x0) = inner ℝ (u.1 - x0) t := by
        simpa [t] using dual_apply_eq_inner_toDualSymm s (u.1 - x0)
      have hx_valueScore :
          Uβ hatP F x0 β s = s (x - x0) - β * (F x - F x0) :=
        supportFunctionApproximation_value_eq_of_fixedArgmax hatP F x0 β hx_argmax
      calc
        a u.1 = inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) := by
          simp [a]
        _ = s (u.1 - x0) - β * (F u.1 - F x0) := by
          rw [← hu_pair]
        _ ≤ s (x - x0) - β * (F x - F x0) := hu_score_le
        _ = Uβ hatP F x0 β s := by simpa using hx_valueScore.symm
    change slice 0 u ≤ ((Uβ hatP F x0 β s : ℝ) : WithTop ℝ)
    simpa [slice] using
      (show (((a u.1 : ℝ) : WithTop ℝ)) ≤ ((Uβ hatP F x0 β s : ℝ) : WithTop ℝ) from by
        exact_mod_cast hu_value)
  · -- The active zero-slice at `x` attains the same value as the owner.
    have hvalue :
        ((Uβ hatP F x0 β s : ℝ) : WithTop ℝ) = slice 0 u0 := by
      simpa [slice, u0] using
        congrArg (fun r : ℝ ↦ ((r : ℝ) : WithTop ℝ)) hx_value
    calc
      ((Uβ hatP F x0 β s : ℝ) : WithTop ℝ) = slice 0 u0 := hvalue
      _ ≤ pointwiseSupremumOn (Set.univ : Set hatP) slice 0 :=
        ClosedConvexOn.slice_le_pointwiseSupremumOn (by simp)

/-- Helper for Lemma 7.10: any affine slice active at `α = 0` in the fixed-slope line-supremum
presentation must be the unique argmax `x`. -/
private theorem supportFunctionApproximationLineSliceActiveAffineIndex_eq_fixedArgmaxAtZero
    {s : StrongDual ℝ E} {x : E} (d : E) {u : hatP}
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hx_unique : ∀ v : E, v ∈ Argmaxβ hatP F β s → v = x)
    (huActive :
      u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP)
        (fun α v ↦
          ((inner ℝ (v.1 - x0) ((InnerProductSpace.toDual ℝ E).symm s) -
              β * (F v.1 - F x0) +
              α * inner ℝ (v.1 - x0) d : ℝ) : WithTop ℝ)) 0) :
    u.1 = x := by
  let t : E := (InnerProductSpace.toDual ℝ E).symm s
  let a : E → ℝ := fun v ↦ inner ℝ (v - x0) t - β * (F v - F x0)
  let slice : ℝ → hatP → WithTop ℝ := fun α v ↦
    ((a v.1 + α * inner ℝ (v.1 - x0) d : ℝ) : WithTop ℝ)
  have hsupAtZero :
      pointwiseSupremumOn (Set.univ : Set hatP) slice 0 =
        ((Uβ hatP F x0 β s : ℝ) : WithTop ℝ) := by
    -- Keep the exact fixed-slope affine-supremum spelling at `α = 0`.
    simpa [t, a, slice] using
      (supportFunctionApproximationLineSliceAffineSupremumAtZero_eq_owner
        hatP F x0 β d hx_argmax)
  have huValue :
      a u.1 = Uβ hatP F x0 β s := by
    -- The active zero-slice matches the exact owner value.
    rcases mem_activePointwiseSupremumOnIndices_iff.mp huActive with ⟨-, huActiveEq⟩
    apply WithTop.coe_injective
    calc
      (((a u.1 : ℝ)) : WithTop ℝ) = slice 0 u := by simp [slice]
      _ = pointwiseSupremumOn (Set.univ : Set hatP) slice 0 := huActiveEq
      _ = ((Uβ hatP F x0 β s : ℝ) : WithTop ℝ) := hsupAtZero
  have hu_argmax : u.1 ∈ Argmaxβ hatP F β s := by
    rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff]
    refine ⟨u.2, ?_⟩
    rw [isMaxOn_iff]
    intro v hv
    have hu_pair : s (u.1 - x0) = inner ℝ (u.1 - x0) t := by
      simpa [t] using dual_apply_eq_inner_toDualSymm s (u.1 - x0)
    have huValueScore :
        s (u.1 - x0) - β * (F u.1 - F x0) =
          s (x - x0) - β * (F x - F x0) := by
      have hx_value :
          Uβ hatP F x0 β s = s (x - x0) - β * (F x - F x0) :=
        supportFunctionApproximation_value_eq_of_fixedArgmax hatP F x0 β hx_argmax
      calc
        s (u.1 - x0) - β * (F u.1 - F x0) =
            inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) := by
              rw [hu_pair]
        _ = Uβ hatP F x0 β s := by
              simpa [a] using huValue
        _ = s (x - x0) - β * (F x - F x0) := hx_value
    have hv_score_le :
        s (v - x0) - β * (F v - F x0) ≤
          s (u.1 - x0) - β * (F u.1 - F x0) := by
      -- Equality with the owner value turns the active zero-slice `u` into a second maximizer.
      have hv_gap :=
        supportFunctionApproximationActiveScoreGapNonposOfFixedArgmax
          hatP F β hx_argmax hv
      have hx_value :
          Uβ hatP F x0 β s = s (x - x0) - β * (F x - F x0) :=
        supportFunctionApproximation_value_eq_of_fixedArgmax hatP F x0 β hx_argmax
      rw [hx_value] at huValue
      have hsplit :
          s (v - x0) - β * (F v - F x0) =
            (s (x - x0) - β * (F x - F x0)) +
              (s (v - x) - β * (F v - F x)) := by
        rw [ContinuousLinearMap.map_sub, ContinuousLinearMap.map_sub, ContinuousLinearMap.map_sub,
          mul_sub, mul_sub, mul_sub]
        ring
      calc
        s (v - x0) - β * (F v - F x0) =
            (s (x - x0) - β * (F x - F x0)) +
              (s (v - x) - β * (F v - F x)) := hsplit
        _ ≤ s (x - x0) - β * (F x - F x0) := by
              linarith
        _ = s (u.1 - x0) - β * (F u.1 - F x0) := huValueScore.symm
    have hv_raw_le :
        s v - β * F v ≤ s u.1 - β * F u.1 := by
      -- Remove the common base-point shift from the affine comparison.
      rw [ContinuousLinearMap.map_sub, ContinuousLinearMap.map_sub, mul_sub, mul_sub] at hv_score_le
      linarith
    -- Remove the common base-point shift from the affine-intercept comparison.
    simpa [smoothedPrimalObjectiveMaximand] using hv_raw_le
  exact hx_unique u.1 hu_argmax

/-- Helper for Lemma 7.10: every active affine-slice subgradient at `α = 0` already equals the
fixed slope `⟪x - x₀, d⟫`. -/
private theorem supportFunctionApproximationActiveAffineSliceSubgradient_eq_fixedSlopeAtZero
    {s : StrongDual ℝ E} {x : E} (d : E) {u : hatP} {g : ℝ}
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hx_unique : ∀ v : E, v ∈ Argmaxβ hatP F β s → v = x)
    (huActive :
      u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP)
        (fun α v ↦
          ((inner ℝ (v.1 - x0) ((InnerProductSpace.toDual ℝ E).symm s) -
              β * (F v.1 - F x0) +
              α * inner ℝ (v.1 - x0) d : ℝ) : WithTop ℝ)) 0)
    (hg :
      g ∈ ∂[Set.univ]
        (fun α : ℝ ↦
          ((inner ℝ (u.1 - x0) ((InnerProductSpace.toDual ℝ E).symm s) -
              β * (F u.1 - F x0) +
              α * inner ℝ (u.1 - x0) d : ℝ) : WithTop ℝ))(0)) :
    g = inner ℝ (x - x0) d := by
  have hu_eq : u.1 = x :=
    supportFunctionApproximationLineSliceActiveAffineIndex_eq_fixedArgmaxAtZero
      hatP F x0 β d hx_argmax hx_unique huActive
  have hdomSlice :
      dom (fun α : ℝ ↦
          ((inner ℝ (u.1 - x0) ((InnerProductSpace.toDual ℝ E).symm s) -
              β * (F u.1 - F x0) +
              α * inner ℝ (u.1 - x0) d : ℝ) : WithTop ℝ)) = Set.univ := by
    ext α
    change ((((inner ℝ (u.1 - x0) ((InnerProductSpace.toDual ℝ E).symm s) -
        β * (F u.1 - F x0) +
        α * inner ℝ (u.1 - x0) d : ℝ) : WithTop ℝ) < ⊤) ↔ True)
    constructor
    · intro _
      trivial
    · intro _
      exact WithTop.coe_lt_top _
  have hg' :
      g ∈ ∂
        (fun α : ℝ ↦
          ((inner ℝ (u.1 - x0) ((InnerProductSpace.toDual ℝ E).symm s) -
              β * (F u.1 - F x0) +
              α * inner ℝ (u.1 - x0) d : ℝ) : WithTop ℝ))(0) := by
    -- On `Set.univ`, the constrained and unconstrained scalar subdifferentials coincide.
    rw [mem_constrainedSubdifferential_iff] at hg
    rw [mem_subdifferential_iff]
    constructor
    · simpa [hdomSlice] using hg.2.1
    · intro y hy
      exact hg.2.2 (by simp)
  have hgSingleton :
      g = inner ℝ (u.1 - x0) d := by
    have hsingleton :=
      supportFunctionApproximation_affineScalarSlice_subdifferential_eq_singleton
        (inner ℝ (u.1 - x0) ((InnerProductSpace.toDual ℝ E).symm s) -
          β * (F u.1 - F x0))
        (inner ℝ (u.1 - x0) d)
    rw [hsingleton] at hg'
    exact Set.mem_singleton_iff.mp hg'
  -- Uniqueness of the active zero-slice identifies its slope with the displayed fixed slope.
  simpa [hu_eq] using hgSingleton

/-- Helper for Lemma 7.10: the convex hull of all active affine-slice subgradients at `α = 0`
already collapses to the singleton fixed slope `⟪x - x₀, d⟫`. -/
private theorem supportFunctionApproximationActiveAffineHullAtZero_eq_singletonOfFixedArgmax
    {s : StrongDual ℝ E} {x : E} (d : E)
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hx_unique : ∀ v : E, v ∈ Argmaxβ hatP F β s → v = x) :
    convexHull ℝ
      {g | ∃ u : hatP,
          u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP)
            (fun α v ↦
              ((inner ℝ (v.1 - x0) ((InnerProductSpace.toDual ℝ E).symm s) -
                  β * (F v.1 - F x0) +
                  α * inner ℝ (v.1 - x0) d : ℝ) : WithTop ℝ)) 0 ∧
            g ∈ ∂[Set.univ]
              (fun α : ℝ ↦
                ((inner ℝ (u.1 - x0) ((InnerProductSpace.toDual ℝ E).symm s) -
                    β * (F u.1 - F x0) +
                    α * inner ℝ (u.1 - x0) d : ℝ) : WithTop ℝ))(0)} =
      {inner ℝ (x - x0) d} := by
  let t : E := (InnerProductSpace.toDual ℝ E).symm s
  let slice : ℝ → hatP → WithTop ℝ := fun α u ↦
    ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
        α * inner ℝ (u.1 - x0) d : ℝ) : WithTop ℝ)
  have hx_hatP : x ∈ hatP := by
    rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff] at hx_argmax
    exact hx_argmax.1
  let u0 : hatP := ⟨x, hx_hatP⟩
  have hsupAtZero :
      pointwiseSupremumOn (Set.univ : Set hatP) slice 0 =
        ((Uβ hatP F x0 β s : ℝ) : WithTop ℝ) := by
    -- Freeze the zero-parameter affine supremum at the exact owner value.
    simpa [t, slice] using
      (supportFunctionApproximationLineSliceAffineSupremumAtZero_eq_owner
        hatP F x0 β d hx_argmax)
  have hu0Active :
      u0 ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP) slice 0 := by
    -- The fixed active point `x` attains the zero-parameter affine supremum.
    rw [mem_activePointwiseSupremumOnIndices_iff]
    refine ⟨by simp [u0], ?_⟩
    calc
      slice 0 u0 = (((inner ℝ (x - x0) t - β * (F x - F x0) : ℝ)) : WithTop ℝ) := by
        simp [slice, u0]
      _ = ((Uβ hatP F x0 β s : ℝ) : WithTop ℝ) := by
        have hx_value :
            Uβ hatP F x0 β s = inner ℝ (x - x0) t - β * (F x - F x0) := by
          have hvalue :
              Uβ hatP F x0 β s = s (x - x0) - β * (F x - F x0) :=
            supportFunctionApproximation_value_eq_of_fixedArgmax hatP F x0 β hx_argmax
          have hpair : s (x - x0) = inner ℝ (x - x0) t := by
            simpa [t] using dual_apply_eq_inner_toDualSymm s (x - x0)
          simpa [hpair] using hvalue
        exact congrArg (fun r : ℝ ↦ ((r : ℝ) : WithTop ℝ)) hx_value.symm
      _ = pointwiseSupremumOn (Set.univ : Set hatP) slice 0 := hsupAtZero.symm
  have hb0Sub :
      inner ℝ (x - x0) d ∈ ∂[Set.univ] (fun α : ℝ ↦ slice α u0)(0) := by
    have hb0Sub_unconstrained :
        inner ℝ (x - x0) d ∈ ∂ (fun α : ℝ ↦ slice α u0)(0) := by
      -- The fixed active affine slice is linear in `α`, so its subdifferential is a singleton.
      simpa [slice, u0, t] using
        (show
          inner ℝ (x - x0) d ∈
            ∂ (fun α : ℝ ↦
              ((inner ℝ (x - x0) t - β * (F x - F x0) +
                  α * inner ℝ (x - x0) d : ℝ) : WithTop ℝ))(0) from by
            rw [supportFunctionApproximation_affineScalarSlice_subdifferential_eq_singleton]
            exact Set.mem_singleton _)
    have hsub := mem_subdifferential_iff.mp hb0Sub_unconstrained
    rw [mem_constrainedSubdifferential_iff]
    refine ⟨by simp, ?_, ?_⟩
    · change ((((slice 0 u0 : WithTop ℝ)) < ⊤))
      exact WithTop.coe_lt_top _
    · intro y hy
      exact hsub.2 (by
        change ((slice y u0 : WithTop ℝ) < ⊤)
        exact WithTop.coe_lt_top _)
  have hgenerator :
      {g | ∃ u : hatP,
          u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP) slice 0 ∧
            g ∈ ∂[Set.univ] (fun α : ℝ ↦ slice α u)(0)} =
        {inner ℝ (x - x0) d} := by
    ext g
    constructor
    · intro hg
      rcases hg with ⟨u, huActive, hgSub⟩
      exact Set.mem_singleton_iff.mpr
        (supportFunctionApproximationActiveAffineSliceSubgradient_eq_fixedSlopeAtZero
          hatP F x0 β d hx_argmax hx_unique huActive hgSub)
    · intro hg
      rcases Set.mem_singleton_iff.mp hg with rfl
      exact ⟨u0, hu0Active, hb0Sub⟩
  -- Collapse the active generator set before evaluating the convex hull.
  rw [hgenerator, convexHull_singleton]

/-- Helper for Lemma 7.10: subtracting the affine support line `α ↦ α g` from the exact line
slice turns an exact scalar subgradient `g` at `0` into a zero scalar subgradient of the shifted
line slice. -/
private theorem supportFunctionApproximationZeroMemShiftedLineSlice_of_memSubdifferential
    {s : StrongDual ℝ E} (t d : E) {g : ℝ}
    (hg :
      g ∈
        ∂ (fun α : ℝ ↦
          (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0)) :
    0 ∈
      ∂ (fun α : ℝ ↦
        ((Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) - α * g : ℝ) : WithTop ℝ))
        (0) := by
  -- Convert the exact scalar subgradient into the zero-subgradient statement for the shifted
  -- affine tilt of the same line slice.
  exact zero_mem_subdifferential_sub_affine_of_mem_subdifferential hg

/-- Helper for Lemma 7.10: if the shifted line slice has zero scalar subgradient at `0`, then
adding back the affine support line `α ↦ α g` recovers `g` as an exact scalar subgradient of the
original line slice. -/
private theorem supportFunctionApproximationMemLineSliceSubdifferential_of_zeroMemShifted
    {s : StrongDual ℝ E} (t d : E) {g : ℝ}
    (hzero :
      0 ∈
        ∂ (fun α : ℝ ↦
          ((Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) - α * g : ℝ) : WithTop ℝ))
          (0)) :
    g ∈
      ∂ (fun α : ℝ ↦
        (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) (t + α • d)) : WithTop ℝ))(0) := by
  -- Undo the affine shift to return from the zero-subgradient formulation to the exact line
  -- slice owner.
  exact mem_subdifferential_of_zero_mem_subdifferential_sub_affine hzero

/-- Helper for Lemma 7.10: every active shifted affine-slice subgradient at `α = 0` already
equals the shifted fixed slope `⟪x - x₀, d⟫ - g`. -/
private theorem supportFunctionApproximationShiftedActiveAffineSliceSubgradient_eq_fixedSlopeAtZero
    {s : StrongDual ℝ E} {x : E} (d : E) (g : ℝ) {u : hatP} {h : ℝ}
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hx_unique : ∀ v : E, v ∈ Argmaxβ hatP F β s → v = x)
    (huActive :
      u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP)
        (fun α v ↦
          ((inner ℝ (v.1 - x0) ((InnerProductSpace.toDual ℝ E).symm s) -
              β * (F v.1 - F x0) +
              α * (inner ℝ (v.1 - x0) d - g) : ℝ) : WithTop ℝ)) 0)
    (hh :
      h ∈ ∂[Set.univ]
        (fun α : ℝ ↦
          ((inner ℝ (u.1 - x0) ((InnerProductSpace.toDual ℝ E).symm s) -
              β * (F u.1 - F x0) +
              α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ))(0)) :
    h = inner ℝ (x - x0) d - g := by
  have huActive_unshifted :
      u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP)
        (fun α v ↦
          ((inner ℝ (v.1 - x0) ((InnerProductSpace.toDual ℝ E).symm s) -
              β * (F v.1 - F x0) +
              α * inner ℝ (v.1 - x0) d : ℝ) : WithTop ℝ)) 0 := by
    -- At `α = 0`, subtracting the affine support line does not change the active indices.
    rw [mem_activePointwiseSupremumOnIndices_iff] at huActive ⊢
    rcases huActive with ⟨hu_mem, hu_sup⟩
    refine ⟨hu_mem, ?_⟩
    simpa using hu_sup
  have hu_eq : u.1 = x :=
    supportFunctionApproximationLineSliceActiveAffineIndex_eq_fixedArgmaxAtZero
      hatP F x0 β d hx_argmax hx_unique huActive_unshifted
  have hdomSlice :
      dom (fun α : ℝ ↦
          ((inner ℝ (u.1 - x0) ((InnerProductSpace.toDual ℝ E).symm s) -
              β * (F u.1 - F x0) +
              α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)) = Set.univ := by
    ext α
    change ((((inner ℝ (u.1 - x0) ((InnerProductSpace.toDual ℝ E).symm s) -
        β * (F u.1 - F x0) +
        α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ) < ⊤) ↔ True)
    constructor
    · intro _
      trivial
    · intro _
      exact WithTop.coe_lt_top _
  have hh' :
      h ∈ ∂
        (fun α : ℝ ↦
          ((inner ℝ (u.1 - x0) ((InnerProductSpace.toDual ℝ E).symm s) -
              β * (F u.1 - F x0) +
              α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ))(0) := by
    -- On `Set.univ`, the constrained and unconstrained shifted scalar subdifferentials coincide.
    rw [mem_constrainedSubdifferential_iff] at hh
    rw [mem_subdifferential_iff]
    constructor
    · simpa [hdomSlice] using hh.2.1
    · intro y hy
      exact hh.2.2 (by simp)
  have hhSingleton :
      h = inner ℝ (u.1 - x0) d - g := by
    have hsingleton :=
      supportFunctionApproximation_affineScalarSlice_subdifferential_eq_singleton
        (inner ℝ (u.1 - x0) ((InnerProductSpace.toDual ℝ E).symm s) -
          β * (F u.1 - F x0))
        (inner ℝ (u.1 - x0) d - g)
    rw [hsingleton] at hh'
    exact Set.mem_singleton_iff.mp hh'
  -- The active zero-slice is unchanged by the affine shift, so uniqueness fixes the slope.
  simpa [hu_eq] using hhSingleton

/-- Helper for Lemma 7.10: after subtracting a scalar affine support line of slope `g`, the
active affine-slice subgradient hull at `α = 0` still collapses to the singleton
`{⟪x - x₀, d⟫ - g}`. -/
private theorem supportFunctionApproximationShiftedActiveAffineHullAtZero_eq_singletonOfFixedArgmax
    {s : StrongDual ℝ E} {x : E} (d : E) (g : ℝ)
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hx_unique : ∀ v : E, v ∈ Argmaxβ hatP F β s → v = x) :
    convexHull ℝ
      {h | ∃ u : hatP,
          u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP)
            (fun α v ↦
              ((inner ℝ (v.1 - x0) ((InnerProductSpace.toDual ℝ E).symm s) -
                  β * (F v.1 - F x0) +
                  α * (inner ℝ (v.1 - x0) d - g) : ℝ) : WithTop ℝ)) 0 ∧
            h ∈ ∂[Set.univ]
              (fun α : ℝ ↦
                ((inner ℝ (u.1 - x0) ((InnerProductSpace.toDual ℝ E).symm s) -
                    β * (F u.1 - F x0) +
                    α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ))(0)} =
      {inner ℝ (x - x0) d - g} := by
  let t : E := (InnerProductSpace.toDual ℝ E).symm s
  let slice : ℝ → hatP → WithTop ℝ := fun α u ↦
    ((inner ℝ (u.1 - x0) t - β * (F u.1 - F x0) +
        α * (inner ℝ (u.1 - x0) d - g) : ℝ) : WithTop ℝ)
  have hx_hatP : x ∈ hatP := by
    rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff] at hx_argmax
    exact hx_argmax.1
  let u0 : hatP := ⟨x, hx_hatP⟩
  have hsupAtZero :
      pointwiseSupremumOn (Set.univ : Set hatP) slice 0 =
        ((Uβ hatP F x0 β s : ℝ) : WithTop ℝ) := by
    -- At `α = 0`, the shifted and unshifted affine slices agree with the owner value.
    simpa [t, slice] using
      (supportFunctionApproximationLineSliceAffineSupremumAtZero_eq_owner
        hatP F x0 β d hx_argmax)
  have hu0Active :
      u0 ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP) slice 0 := by
    -- The fixed active point still attains the zero-parameter shifted affine supremum.
    rw [mem_activePointwiseSupremumOnIndices_iff]
    refine ⟨by simp [u0], ?_⟩
    calc
      slice 0 u0 = (((inner ℝ (x - x0) t - β * (F x - F x0) : ℝ)) : WithTop ℝ) := by
        simp [slice, u0]
      _ = ((Uβ hatP F x0 β s : ℝ) : WithTop ℝ) := by
        have hx_value :
            Uβ hatP F x0 β s = inner ℝ (x - x0) t - β * (F x - F x0) := by
          have hvalue :
              Uβ hatP F x0 β s = s (x - x0) - β * (F x - F x0) :=
            supportFunctionApproximation_value_eq_of_fixedArgmax hatP F x0 β hx_argmax
          have hpair : s (x - x0) = inner ℝ (x - x0) t := by
            simpa [t] using dual_apply_eq_inner_toDualSymm s (x - x0)
          simpa [hpair] using hvalue
        exact congrArg (fun r : ℝ ↦ ((r : ℝ) : WithTop ℝ)) hx_value.symm
      _ = pointwiseSupremumOn (Set.univ : Set hatP) slice 0 := hsupAtZero.symm
  have hb0Sub :
      inner ℝ (x - x0) d - g ∈ ∂[Set.univ] (fun α : ℝ ↦ slice α u0)(0) := by
    have hb0Sub_unconstrained :
        inner ℝ (x - x0) d - g ∈ ∂ (fun α : ℝ ↦ slice α u0)(0) := by
      -- The fixed active shifted affine slice is affine in `α`, so its scalar subdifferential
      -- is the singleton consisting of its slope.
      simpa [slice, u0, t] using
        (show
          inner ℝ (x - x0) d - g ∈
            ∂ (fun α : ℝ ↦
              ((inner ℝ (x - x0) t - β * (F x - F x0) +
                  α * (inner ℝ (x - x0) d - g) : ℝ) : WithTop ℝ))(0) from by
            rw [supportFunctionApproximation_affineScalarSlice_subdifferential_eq_singleton]
            exact Set.mem_singleton _)
    have hsub := mem_subdifferential_iff.mp hb0Sub_unconstrained
    rw [mem_constrainedSubdifferential_iff]
    refine ⟨by simp, ?_, ?_⟩
    · change ((((slice 0 u0 : WithTop ℝ)) < ⊤))
      exact WithTop.coe_lt_top _
    · intro y hy
      exact hsub.2 (by
        change ((slice y u0 : WithTop ℝ) < ⊤)
        exact WithTop.coe_lt_top _)
  have hgenerator :
      {h | ∃ u : hatP,
          u ∈ activePointwiseSupremumOnIndices (Set.univ : Set hatP) slice 0 ∧
            h ∈ ∂[Set.univ] (fun α : ℝ ↦ slice α u)(0)} =
        {inner ℝ (x - x0) d - g} := by
    ext h
    constructor
    · intro hh
      rcases hh with ⟨u, huActive, hhSub⟩
      exact Set.mem_singleton_iff.mpr
        (supportFunctionApproximationShiftedActiveAffineSliceSubgradient_eq_fixedSlopeAtZero
          hatP F x0 β d g hx_argmax hx_unique huActive hhSub)
    · intro hh
      rcases Set.mem_singleton_iff.mp hh with rfl
      exact ⟨u0, hu0Active, hb0Sub⟩
  -- Collapse the shifted active generator set before evaluating its convex hull.
  rw [hgenerator, convexHull_singleton]

/-- Helper for Lemma 7.10: unique fixed-argmax data should already determine the derivative of the
support-function approximation at the base slope `s`, independent of any determinant witness used
later for the Chapter 5 local-dual-norm remainder. -/
private theorem supportFunctionApproximationPullbackHasGradientAtOfFixedArgmax
    {s : StrongDual ℝ E} {x : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hx_unique : ∀ u : E, u ∈ Argmaxβ hatP F β s → u = x)
    (hhatP_int : hatP ⊆ interior Q) :
    HasGradientAt
      (fun y : E ↦ Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y))
      (x - x0)
      ((InnerProductSpace.toDual ℝ E).symm s) := by
  let t : E := (InnerProductSpace.toDual ℝ E).symm s
  let _ := t
  let _ := hx_argmax
  let _ := hx_unique
  let _ := hhatP_int
  -- Route correction: isolate the fixed-slope differentiability blocker as a pulled-back
  -- gradient statement. Once the singleton subdifferential theorem at `t` is available, the
  -- existing convex-gradient bridge and inverse-Riesz transport close the public derivative
  -- theorem immediately.
  -- This derivative-side bridge is still mathematically reasonable, but it is now a
  -- post-repair obligation only: the earlier overgeneralized `ω_*` route was refuted in-file by
  -- `lemma710CounterexampleGapLeOmega_false`, so the Chapter 5 perturbed-gap work now lives only
  -- on the repaired stationary-point surface and should not be mixed into this derivative block.
  -- TODO: prove
  -- `∂ (fun y : E ↦ (Uβ hatP F x0 β ((InnerProductSpace.toDual ℝ E) y) : WithTop ℝ)) t =
  --   {x - x0}`
  -- by combining the line-restriction lemma
  -- `supportFunctionApproximationLineSubgradientOfMemPullbackSubdifferential`
  -- with the now-proved zero-active affine-hull collapse
  -- `supportFunctionApproximationActiveAffineHullAtZero_eq_singletonOfFixedArgmax`.
  -- Concrete blocker: the first remaining gap is the reverse inclusion that upgrades that
  -- active-hull singleton to the exact scalar line-slice subdifferential singleton for the
  -- infinite family indexed by `hatP`. The finite-family Chapter 3 equality theorem for
  -- `subdifferential (pointwiseSupremumOn ...)` does not apply here, so this branch still needs a
  -- fixed-slope directional-derivative squeeze on the exact scalar line slice.
  sorry

/-- Helper for Lemma 7.10: unique fixed-argmax data should already determine the derivative of the
support-function approximation at the base slope `s`, independent of any determinant witness used
later for the Chapter 5 local-dual-norm remainder. -/
theorem smoothSupportFunctionApproximation_hasFDerivAt_of_fixedArgmax
    {s : StrongDual ℝ E} {x : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hx_unique : ∀ u : E, u ∈ Argmaxβ hatP F β s → u = x)
    (hhatP_int : hatP ⊆ interior Q) :
    HasFDerivAt (Uβ hatP F x0 β)
      (ContinuousLinearMap.apply ℝ ℝ (x - x0)) s := by
  have hgradPull :=
    supportFunctionApproximationPullbackHasGradientAtOfFixedArgmax
      hatP Q F x0 β hx_argmax hx_unique hhatP_int
  -- The remaining transport back to the original dual owner is now isolated in the dedicated
  -- inverse-Riesz bridge.
  simpa using
    supportFunctionApproximationHasFDerivAt_of_pullbackHasGradientAt
      hatP F x0 β
      hgradPull

/-- Determinant-witness specialization of Lemma 7.10's Chapter 7 `ω_*` upper model on the
Definition 7.53 setup, so `x₀` is the constrained analytic center
`x0 ∈ argmin[hatP ∩ interior Q] F`. This keeps the stronger old surface available as a companion
bridge for downstream files that already work with an explicit witness `(hessian F x).det ≠ 0`,
while the main labeled theorem stays on the canonical active-point norm condition `‖g‖_x^* < β`.
The Chapter 5 `ω_*` step also uses the source-faithful stationarity relation for the unperturbed
tilted objective at the active point `x`. -/
theorem smoothSupportFunctionApproximation_hasFDerivAt_and_omegaStar_upper_bound_of_detNeZero
    {s : StrongDual ℝ E} {x : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hx_unique : ∀ u : E, u ∈ Argmaxβ hatP F β s → u = x)
    (hhatP_int : hatP ⊆ interior Q)
    (hx0 : x0 ∈ argmin[hatP ∩ interior Q] F)
    (hstationary : ∇ (fun z : E ↦ (β : ℝ) * F z - s z) x = 0)
    (hx_det : (hessian F x).det ≠ 0) :
    HasFDerivAt (Uβ hatP F x0 β)
      (ContinuousLinearMap.apply ℝ ℝ (x - x0)) s ∧
      ∀ g : StrongDual ℝ E,
      ∀ hg :
        supportFunctionApproximationDualLocalNormAt
            hatP Q F β hx_argmax hhatP_int hx_det g <
          (β : ℝ),
      Uβ hatP F x0 β (s + g) ≤
        Uβ hatP F x0 β s +
          g (x - x0) +
            supportFunctionApproximationOmegaStarUpperTermOfDetNeZero
              hatP Q F β hx_argmax hhatP_int hx_det g hg := by
  let _ : x0 ∈ argmin[hatP ∩ interior Q] F := hx0
  constructor
  · -- The differentiability component is the determinant-free fixed-argmax bridge isolated above.
    exact
      smoothSupportFunctionApproximation_hasFDerivAt_of_fixedArgmax
        hatP Q F x0 β hx_argmax hx_unique hhatP_int
  · intro g hg
    -- The remaining owner-level upper model is now isolated in the dedicated `csSup_le` helper.
    simpa using
      supportFunctionApproximationUpperModelOfDetNeZero
        hatP Q F x0 β hx_argmax hhatP_int hstationary hx_det hg

/-- Invertibility-witness specialization of Lemma 7.10's Chapter 7 `ω_*` upper model on the
Definition 7.53 setup, where `x₀` is the constrained analytic center of `hatP ∩ interior Q`.
This reads the source dual local norm through the canonical local owner
`‖g‖*[F; x | hPos; hInv]` attached to the active Hessian at `x`. It is kept as a companion bridge
for downstream files that already work with an explicit Hessian invertibility witness, together
with the source-faithful stationary tilted-objective relation at `x`. -/
theorem smoothSupportFunctionApproximation_hasFDerivAt_and_omegaStar_upper_bound_of_isInvertible
    {s : StrongDual ℝ E} {x : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hx_unique : ∀ u : E, u ∈ Argmaxβ hatP F β s → u = x)
    (hhatP_int : hatP ⊆ interior Q)
    (hx0 : x0 ∈ argmin[hatP ∩ interior Q] F)
    (hstationary : ∇ (fun z : E ↦ (β : ℝ) * F z - s z) x = 0)
    (hx_inv : (hessian F x).IsInvertible) :
    let hx_int : x ∈ interior Q := argmaxBeta_mem_interior_of_subset hatP Q F β hx_argmax hhatP_int
    let hx_pos : (hessian F x).IsPositive :=
      (inferInstance : IsStandardSelfConcordantOn (interior Q) F).hessian_isPositive hx_int
    HasFDerivAt (Uβ hatP F x0 β)
      (ContinuousLinearMap.apply ℝ ℝ (x - x0)) s ∧
      ∀ g : StrongDual ℝ E,
      ∀ hg : ‖g‖*[F; x | hx_pos; hx_inv] < (β : ℝ),
      Uβ hatP F x0 β (s + g) ≤
        Uβ hatP F x0 β s +
          g (x - x0) +
            (β : ℝ) *
              ω_* (selfConcordantOmegaStarArg (1 : NNReal)
                (‖g‖*[F; x | hx_pos; hx_inv] / (β : ℝ))
                (by
                  simpa [one_mul] using
                    (div_lt_iff₀ β.2).2
                      (show ‖g‖*[F; x | hx_pos; hx_inv] < 1 * (β : ℝ) by
                        simpa using hg))) := by
  let hx_int : x ∈ interior Q :=
    argmaxBeta_mem_interior_of_subset hatP Q F β hx_argmax hhatP_int
  let hx_pos : (hessian F x).IsPositive :=
    (inferInstance : IsStandardSelfConcordantOn (interior Q) F).hessian_isPositive hx_int
  have hx_det : (hessian F x).det ≠ 0 := by
    -- Read determinant nondegeneracy from the explicit invertibility witness.
    rcases hx_inv with ⟨e, he⟩
    have hdet_e : (e : E →L[ℝ] E).det ≠ 0 := by
      simpa using (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero
    simpa [he] using hdet_e
  have hbase :=
    smoothSupportFunctionApproximation_hasFDerivAt_and_omegaStar_upper_bound_of_detNeZero
      hatP Q F x0 β hx_argmax hx_unique hhatP_int hx0 hstationary hx_det
  -- Transport the determinant-witness theorem to the explicit invertibility reader.
  dsimp [hx_int, hx_pos]
  constructor
  · exact hbase.1
  · intro g hg
    have hg_det :
        supportFunctionApproximationDualLocalNormAt
            hatP Q F β hx_argmax hhatP_int hx_det g <
          (β : ℝ) := by
      -- Rewrite the source-facing norm condition to the determinant-witness owner.
      simpa [supportFunctionApproximationDualLocalNormAt_eq_ofPosDefMem
        hatP Q F β hx_argmax hhatP_int hx_det g, HessianDualLocalNorm.ofDetNeZero,
        dualLocalNorm_def, hx_int, hx_pos] using hg
    have hineq := hbase.2 g hg_det
    -- Rewrite only the Chapter 5 remainder term, keeping the main inequality unchanged.
    simpa [supportFunctionApproximationOmegaStarUpperTermOfDetNeZero_eq_ofPosDefMem
      hatP Q F β hx_argmax hhatP_int hx_det g hg_det,
      HessianDualLocalNorm.ofDetNeZero, dualLocalNorm_def, hx_int, hx_pos] using hineq

/-- Companion corollary: on the Definition 7.53 setup where `x₀` is the constrained analytic
center of `hatP ∩ interior Q`, if the Hessian of `F` is positive definite on `interior Q`, then
the Chapter 7 upper model from Lemma 7.10 can be read through the canonical domain-level dual
local norm bridge `HessianDualLocalNorm.ofPosDefMem` at the active maximizer `x`, still under the
source-faithful stationary tilted-objective relation at `x`. -/
theorem smoothSupportFunctionApproximation_hasFDerivAt_and_omegaStar_upper_bound_of_posDefMem
    {s : StrongDual ℝ E} {x : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    [HasPositiveDefiniteHessianOn (interior Q) F]
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hx_unique : ∀ u : E, u ∈ Argmaxβ hatP F β s → u = x)
    (hhatP_int : hatP ⊆ interior Q)
    (hx0 : x0 ∈ argmin[hatP ∩ interior Q] F)
    (hstationary : ∇ (fun z : E ↦ (β : ℝ) * F z - s z) x = 0) :
    let hx_int : x ∈ interior Q := argmaxBeta_mem_interior_of_subset hatP Q F β hx_argmax hhatP_int
    HasFDerivAt (Uβ hatP F x0 β)
      (ContinuousLinearMap.apply ℝ ℝ (x - x0)) s ∧
      ∀ g : StrongDual ℝ E,
      ∀ hg : HessianDualLocalNorm.ofPosDefMem F hx_int g < (β : ℝ),
      Uβ hatP F x0 β (s + g) ≤
        Uβ hatP F x0 β s +
          g (x - x0) +
            (β : ℝ) *
              ω_* (selfConcordantOmegaStarArg (1 : NNReal)
                (HessianDualLocalNorm.ofPosDefMem F hx_int g / (β : ℝ))
                (by
                  simpa [one_mul] using
                    (div_lt_iff₀ β.2).2
                      (show HessianDualLocalNorm.ofPosDefMem F hx_int g < 1 * (β : ℝ) by
                        simpa using hg))) := by
  let hx_int : x ∈ interior Q :=
    argmaxBeta_mem_interior_of_subset hatP Q F β hx_argmax hhatP_int
  let hx_det : (hessian F x).det ≠ 0 :=
    HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem hx_int
  have hbase :=
    smoothSupportFunctionApproximation_hasFDerivAt_and_omegaStar_upper_bound_of_detNeZero
      hatP Q F x0 β hx_argmax hx_unique hhatP_int hx0 hstationary hx_det
  -- Transport the determinant-witness theorem to the canonical positive-definite domain reader.
  dsimp [hx_int]
  constructor
  · exact hbase.1
  · intro g hg
    have hg_det :
        supportFunctionApproximationDualLocalNormAt
            hatP Q F β hx_argmax hhatP_int hx_det g <
          (β : ℝ) := by
      -- Replace the domain-level norm reader by the determinant-witness reader at `x`.
      simpa [supportFunctionApproximationDualLocalNormAt_eq_ofPosDefMem
        hatP Q F β hx_argmax hhatP_int hx_det g, HessianDualLocalNorm.ofPosDefMem,
        HessianDualLocalNorm.ofDetNeZero, dualLocalNorm_def] using hg
    have hineq := hbase.2 g hg_det
    -- Rewrite the determinant-witness remainder back to the domain-level reader.
    simpa [supportFunctionApproximationOmegaStarUpperTermOfDetNeZero_eq_ofPosDefMem
      hatP Q F β hx_argmax hhatP_int hx_det g hg_det, HessianDualLocalNorm.ofPosDefMem,
      HessianDualLocalNorm.ofDetNeZero, dualLocalNorm_def] using hineq

/-- Lemma 7.10. In the Definition 7.53 setup, assume `x₀` is the constrained analytic center
`x0 ∈ argmin[hatP ∩ interior Q] F`. If `x = u^*_β(s)` is the unique active maximizer in `hatP`,
`hatP ⊆ interior Q`, the unperturbed tilted objective `z ↦ β * F z - s z` is stationary at `x`,
and `F` is standard self-concordant on `interior Q`, then the
support-function approximation is differentiable at `s` with derivative `x - x₀`; moreover, for
perturbations `g` satisfying the source-facing active-point local-dual-norm condition
`‖g‖_x^* < β` encoded by `supportFunctionApproximationDualLocalNormLt`, it satisfies the one-step
`ω_*` upper model. The determinant, invertibility, and positive-definite-domain readers remain
separate companion bridge theorems. -/
theorem smoothSupportFunctionApproximation_hasFDerivAt_and_omegaStar_upper_bound
    {s : StrongDual ℝ E} {x : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hx_unique : ∀ u : E, u ∈ Argmaxβ hatP F β s → u = x)
    (hhatP_int : hatP ⊆ interior Q)
    (hx0 : x0 ∈ argmin[hatP ∩ interior Q] F)
    (hstationary : ∇ (fun z : E ↦ (β : ℝ) * F z - s z) x = 0) :
    HasFDerivAt (Uβ hatP F x0 β)
      (ContinuousLinearMap.apply ℝ ℝ (x - x0)) s ∧
      ∀ g : StrongDual ℝ E,
      ∀ hg : supportFunctionApproximationDualLocalNormLt hatP Q F β hx_argmax hhatP_int g,
      Uβ hatP F x0 β (s + g) ≤
      Uβ hatP F x0 β s +
          g (x - x0) +
            supportFunctionApproximationOmegaStarUpperTerm
              hatP Q F β hx_argmax hhatP_int g hg := by
  classical
  constructor
  · -- The public derivative statement reuses the determinant-free fixed-argmax bridge.
    exact
      smoothSupportFunctionApproximation_hasFDerivAt_of_fixedArgmax
        hatP Q F x0 β hx_argmax hx_unique hhatP_int
  · intro g hg
    let hx_det : (hessian F x).det ≠ 0 := Classical.choose hg
    let hg_det :
        supportFunctionApproximationDualLocalNormAt
            hatP Q F β hx_argmax hhatP_int hx_det g <
          (β : ℝ) := Classical.choose_spec hg
    have hbase :=
      smoothSupportFunctionApproximation_hasFDerivAt_and_omegaStar_upper_bound_of_detNeZero
        hatP Q F x0 β hx_argmax hx_unique hhatP_int hx0 hstationary hx_det
    have hineq := hbase.2 g hg_det
    -- Rewrite only the hidden Chapter 5 remainder witness back to the public owner.
    simpa [supportFunctionApproximationOmegaStarUpperTerm_eq_of_detNeZero
      hatP Q F β hx_argmax hhatP_int g hx_det hg_det,
      hx_det, hg_det] using hineq

/-- Separate differentiability bridge for `U_β` under the same unique-maximizer,
self-concordant, and feasible-domain hypotheses as Lemma 7.10, but without the Definition 7.53
analytic-center premise or the Chapter 5 dual-local-norm upper-model branch, because the
derivative statement itself only needs fixed-argmax data. -/
theorem smoothSupportFunctionApproximation_hasFDerivAt
    {s : StrongDual ℝ E} {x : E}
    [IsStandardSelfConcordantOn (interior Q) F]
    (hx_argmax : x ∈ Argmaxβ hatP F β s)
    (hx_unique : ∀ u : E, u ∈ Argmaxβ hatP F β s → u = x)
    (hhatP_int : hatP ⊆ interior Q) :
    HasFDerivAt (Uβ hatP F x0 β)
      (ContinuousLinearMap.apply ℝ ℝ (x - x0)) s := by
  -- The derivative statement is exactly the determinant-free fixed-argmax bridge.
  exact
    smoothSupportFunctionApproximation_hasFDerivAt_of_fixedArgmax
      hatP Q F x0 β hx_argmax hx_unique hhatP_int

end

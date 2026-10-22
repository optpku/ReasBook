/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_8
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_7_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_3
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_9
import FirstOrderMethodsOptimization_Beck_2017.Chap05.ConjugateFunctionStrongDual
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_16
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Lemma_5_20
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_26
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Topology.Instances.EReal.Lemmas

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

recall effective_domain
recall IsProperExtendedRealFunction
recall is_convex_function
recall infimal_convolution
recall conjugate_function
recall is_l_smooth_on
recall conjugate_function_strongDual
recall infimal_convolution_eq_dual_conjugate_of_sum_conjugates

/- Proposition 5.17 is `source-facing` in the infimal-convolution smoothing calculus. The owner
abstractions already present in the project are:
- `IsProperExtendedRealFunction`, `is_convex_function`, and `infimal_convolution` for the primal
  extended-real objects;
- `conjugate_function` for the algebraic-dual Fenchel conjugate appearing in the exact formula;
- `conjugate_function_strongDual` from the chapter support owner and `is_l_smooth_on` from
  Definition 5.1 for the normed-dual/smoothness bridge;
- `infimal_convolution_eq_dual_conjugate_of_sum_conjugates` from Theorem 4.9 together with the
  Chapter 5 conjugate-side smoothness theorem from Theorem 5.26 for the canonical everywhere-finite
  owner surfaces used by the present proposition.

The item splits naturally into two atomic clauses: the exact conjugacy identity for `f □ ω`, then
the smoothness consequence under strong convexity of the conjugate kernel. The second clause is
stated on the continuous dual, since that is the existing normed owner for strong convexity in the
repo. -/

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Helper for Proposition 5.17: an everywhere finite `EReal`-valued function agrees with the
canonical `toEReal` lift of its real part. -/
private lemma erealFunction_eq_toEReal_toReal_of_realValued
    (g : E → EReal) (hreal : ∀ x, ∃ r : ℝ, g x = (r : EReal)) :
    g = (fun x ↦ (g x).toReal).toEReal := by
  -- Normalize each pointwise value by ruling out both infinite endpoints.
  funext x
  rcases hreal x with ⟨r, hr⟩
  have hx_ne_top : g x ≠ ⊤ := by
    rw [hr]
    exact EReal.coe_ne_top r
  have hx_ne_bot : g x ≠ ⊥ := by
    rw [hr]
    exact EReal.coe_ne_bot r
  -- Finite `EReal` values are unchanged by `toReal` followed by coercion back to `EReal`.
  simpa [Function.toEReal] using (EReal.coe_toReal hx_ne_top hx_ne_bot).symm

omit [FiniteDimensional ℝ E] in
/-- Helper for Proposition 5.17: a convex everywhere finite extended-real-valued function has a
convex real-valued `toReal` model on all of `E`. -/
private lemma convexOn_toReal_of_isConvex_realValued
    (g : E → EReal) (hg_convex : is_convex_function g)
    (hreal : ∀ x, ∃ r : ℝ, g x = (r : EReal)) :
    ConvexOn ℝ Set.univ (fun x ↦ (g x).toReal) := by
  -- The real-valued hypothesis removes `⊥` and identifies the effective domain with `univ`.
  have hg_ne_bot : ∀ x, g x ≠ ⊥ := by
    intro x
    rcases hreal x with ⟨r, hr⟩
    rw [hr]
    exact EReal.coe_ne_bot r
  have hdom : effective_domain g = Set.univ := by
    ext x
    constructor
    · intro hx
      simp
    · intro hx
      refine mem_effective_domain.mpr ?_
      rcases hreal x with ⟨r, hr⟩
      rw [hr]
      exact EReal.coe_lt_top r
  have hg_convex_dom : ConvexOn ℝ (effective_domain g) (fun x ↦ (g x).toReal) := by
    exact convexOn_toReal_of_is_convex_function hg_convex (fun x _ ↦ hg_ne_bot x)
  simpa [hdom] using hg_convex_dom

/-- Helper for Proposition 5.17: in finite dimension, a convex everywhere finite
extended-real-valued function is lower semicontinuous. -/
private lemma lowerSemicontinuous_of_isConvex_realValued
    (g : E → EReal) (hg_convex : is_convex_function g)
    (hreal : ∀ x, ∃ r : ℝ, g x = (r : EReal)) :
    LowerSemicontinuous g := by
  let gReal : E → ℝ := fun x ↦ (g x).toReal
  have hgReal_convex : ConvexOn ℝ Set.univ gReal := by
    simpa [gReal] using convexOn_toReal_of_isConvex_realValued g hg_convex hreal
  have hgReal_cont : Continuous gReal := by
    simpa [gReal, continuousOn_univ] using hgReal_convex.continuousOn
  have hg_eq : g = gReal.toEReal := by
    simpa [gReal] using erealFunction_eq_toEReal_toReal_of_realValued g hreal
  -- Transfer lower semicontinuity through the continuous real-valued model.
  rw [hg_eq]
  exact Function.toEReal_lowerSemicontinuous_of_continuous hgReal_cont

omit [FiniteDimensional ℝ E] in
/-- Helper for Proposition 5.17: the infimal convolution of two convex extended-real-valued
functions is convex once both summands avoid the value `⊥`. -/
private lemma infimalConvolution_isConvex_ofConvexEReal
    (f ω : E → EReal) (hf_convex : is_convex_function f) (hω_convex : is_convex_function ω)
    (hf_ne_bot : ∀ x, f x ≠ ⊥) (hω_ne_bot : ∀ x, ω x ≠ ⊥) :
    is_convex_function (f □ ω) := by
  -- Build the jointly convex slice kernel and then minimize in the second coordinate.
  have hSecond : is_convex_function (fun p : E × E ↦ f p.2) := by
    simpa using
      is_convex_function_precompose_linearMap_add
        hf_convex
        (LinearMap.snd ℝ E E)
        (0 : E)
  have hDifference : is_convex_function (fun p : E × E ↦ ω (p.1 - p.2)) := by
    simpa using
      is_convex_function_precompose_linearMap_add
        hω_convex
        (LinearMap.fst ℝ E E - LinearMap.snd ℝ E E)
        (0 : E)
  have hKernel : is_convex_function (fun p : E × E ↦ f p.2 + ω (p.1 - p.2)) := by
    simpa [Pi.add_apply] using
      is_convex_function_pointwise_add hSecond hDifference
        (fun p ↦ hf_ne_bot p.2)
        (fun p ↦ hω_ne_bot (p.1 - p.2))
  simpa [infimal_convolution_apply] using
    partialIInfOnSecondIsConvex
      (f := fun p : E × E ↦ f p.2 + ω (p.1 - p.2))
      hKernel

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Helper for Proposition 5.17: an everywhere finite infimal convolution is proper. -/
private lemma infimalConvolution_isProper_of_realValued
    (f ω : E → EReal) (h_infimal_real : ∀ x, ∃ r : ℝ, (f □ ω) x = (r : EReal)) :
    IsProperExtendedRealFunction (f □ ω) := by
  -- Normalize the everywhere-finite hypothesis into the owner properness fields.
  refine ⟨?_, ?_⟩
  · intro x
    rcases h_infimal_real x with ⟨r, hr⟩
    rw [hr]
    exact EReal.coe_ne_bot r
  · rcases h_infimal_real 0 with ⟨r, hr⟩
    refine ⟨0, ?_⟩
    rw [mem_effective_domain, hr]
    exact EReal.coe_lt_top r

/-- Helper for Proposition 5.17: the sum of the two continuous-dual conjugates is proper once
`f □ ω` is everywhere finite. -/
private lemma sumConjugatesStrongDual_isProper
    (f ω : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hω_proper : IsProperExtendedRealFunction ω) (hf_convex : is_convex_function f)
    (hω_convex : is_convex_function ω)
    (h_infimal_real : ∀ x, ∃ r : ℝ, (f □ ω) x = (r : EReal)) :
    IsProperExtendedRealFunction
      (fun y : StrongDual ℝ E ↦
        conjugate_function_strongDual f y + conjugate_function_strongDual ω y) := by
  -- Re-express the target as the continuous-dual conjugate of `f □ ω`.
  have h_infimal_convex : is_convex_function (f □ ω) := by
    exact
      infimalConvolution_isConvex_ofConvexEReal
        f ω hf_convex hω_convex hf_proper.ne_bot hω_proper.ne_bot
  have h_infimal_proper : IsProperExtendedRealFunction (f □ ω) := by
    exact infimalConvolution_isProper_of_realValued f ω h_infimal_real
  have hsum_eq :
      (fun y : StrongDual ℝ E ↦
        conjugate_function_strongDual f y + conjugate_function_strongDual ω y) =
      conjugate_function_strongDual (f □ ω) := by
    -- The Chapter 4 conjugate identity remains valid after restricting from `E*` to `StrongDual`.
    funext y
    simpa [conjugate_function_strongDual] using
      congrArg (fun h : Module.Dual ℝ E → EReal ↦ h y)
        (conjugate_function_infimal_convolution_eq_add_of_proper f ω hf_proper hω_proper).symm
  have hconj_proper :
      IsProperExtendedRealFunction (conjugate_function_strongDual (f □ ω)) := by
    -- Build the finite-domain witness from a supporting subgradient of `f □ ω`.
    refine ⟨?_, ?_⟩
    · intro y
      exact conjugate_function_ne_bot_of_proper (f □ ω) h_infimal_proper y
    · rcases
        exists_subdifferentiable_point_in_effective_domain_of_proper_convex
          (f □ ω) h_infimal_proper h_infimal_convex with
          ⟨x, hx, hxsub⟩
      rcases hxsub with ⟨g, hg⟩
      have hfinite : ((g x : EReal) - (f □ ω) x) < ⊤ := by
        lift (f □ ω) x to ℝ using ⟨hx.ne, h_infimal_proper.ne_bot x⟩ with fx hfx
        simpa [hfx, EReal.coe_sub] using EReal.coe_lt_top (g x - fx)
      have hbound :
          conjugate_function (f □ ω) g ≤ (g x : EReal) - (f □ ω) x := by
        have hne_bot :
            ∀ z ∈ effective_domain (f □ ω), (f □ ω) z ≠ ⊥ := fun z _ ↦
              h_infimal_proper.ne_bot z
        -- The supporting inequality bounds every conjugate witness term.
        rw [conjugate_function_apply]
        refine sSup_le ?_
        rintro _ ⟨z, rfl⟩
        by_cases hz : z ∈ effective_domain (f □ ω)
        · have hsub_real :
              g (z - x) ≤ ((f □ ω) z).toReal - ((f □ ω) x).toReal :=
              subgradient_eval_le_toReal_sub (f □ ω) x z hne_bot hx hz hg
          have hpair_real : g z - ((f □ ω) z).toReal ≤ g x - ((f □ ω) x).toReal := by
            have hlin : g (z - x) = g z - g x := by
              simp
            linarith
          have hfx_eq :
              (f □ ω) x = ((((f □ ω) x).toReal : ℝ) : EReal) :=
            (EReal.coe_toReal (ne_of_lt hx) (h_infimal_proper.ne_bot x)).symm
          have hfz_eq :
              (f □ ω) z = ((((f □ ω) z).toReal : ℝ) : EReal) :=
            (EReal.coe_toReal (ne_of_lt hz) (h_infimal_proper.ne_bot z)).symm
          change (g z : EReal) - (f □ ω) z ≤ (g x : EReal) - (f □ ω) x
          rw [hfx_eq, hfz_eq]
          simpa [EReal.coe_sub] using EReal.coe_le_coe hpair_real
        · have hztop : (f □ ω) z = ⊤ := by
            simpa [mem_effective_domain] using hz
          simp [hztop]
      refine ⟨LinearMap.toContinuousLinearMap g, ?_⟩
      -- The supporting point yields the required finite continuous-dual conjugate witness.
      refine mem_effective_domain.mpr ?_
      simpa [conjugate_function_strongDual] using lt_of_le_of_lt hbound hfinite
  simpa [hsum_eq] using hconj_proper

omit [FiniteDimensional ℝ E] in
/-- Helper for Proposition 5.17: adding the convex conjugate of `f` preserves the strong
convexity modulus of the convex conjugate of `ω`. -/
private lemma sumConjugatesStrongDual_strongConvexOn
    (f ω : E → EReal) (L : NNReal) (hL_pos : 0 < L) (hf_proper : IsProperExtendedRealFunction f)
    (hω_proper : IsProperExtendedRealFunction ω) (hf_convex : is_convex_function f)
    (hω_star_strong :
      StrongConvexOn
        (effective_domain (conjugate_function_strongDual ω))
        (1 / (L : ℝ))
        (fun y ↦ (conjugate_function_strongDual ω y).toReal)) :
    StrongConvexOn
      (effective_domain
        (fun y : StrongDual ℝ E ↦
          conjugate_function_strongDual f y + conjugate_function_strongDual ω y))
      (1 / (L : ℝ))
      (fun y ↦
        ((conjugate_function_strongDual f y + conjugate_function_strongDual ω y)).toReal) := by
  -- Convert the source strong-convexity hypothesis into the Chapter 5 owner theorem for sums.
  have hσ_pos : 0 < (1 / (L : ℝ)) := by
    positivity
  have hω_strong :
      is_strongly_convex_function (conjugate_function_strongDual ω) (1 / (L : ℝ)) := by
    refine is_strongly_convex_function_iff_strongConvexOn_toReal.mpr ?_
    refine ⟨hσ_pos, ?_, ?_⟩
    · intro y
      exact conjugate_function_ne_bot_of_proper ω hω_proper y
    · simpa using hω_star_strong
  let _ := hf_convex
  have hf_star_convex : is_convex_function (conjugate_function_strongDual f) :=
    (conjugateFunctionStrongDual_closedConvex f).2
  have hf_star_ne_bot : ∀ y : StrongDual ℝ E, conjugate_function_strongDual f y ≠ ⊥ := by
    intro y
    exact conjugate_function_ne_bot_of_proper f hf_proper y
  have hsum_strong :
      is_strongly_convex_function
        (fun y : StrongDual ℝ E ↦
          conjugate_function_strongDual ω y + conjugate_function_strongDual f y)
        (1 / (L : ℝ)) := by
    exact
      is_strongly_convex_function_add_of_is_convex_function
        hω_strong hf_star_convex hf_star_ne_bot
  simpa [add_comm, add_left_comm, add_assoc] using
    strongConvexOn_toReal_of_is_strongly_convex_function hsum_strong

local instance proposition517DualSeminormedAddCommGroup :
    SeminormedAddCommGroup (StrongDual ℝ E) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

local instance proposition517DualNormedSpace : NormedSpace ℝ (StrongDual ℝ E) :=
  ContinuousLinearMap.toNormedSpace

omit [FiniteDimensional ℝ E] in
/-- Helper for Proposition 5.17: precomposing an `L`-smooth bidual function with the canonical
isometric inclusion `E → E**` preserves the same smoothness constant. -/
private lemma isLSmoothOn_precomposeInclusionInDoubleDual
    (Φ : StrongDual ℝ (StrongDual ℝ E) → ℝ) (L : NNReal)
    (hΦ : is_l_smooth_on Φ Set.univ L) :
    is_l_smooth_on
      (fun x : E ↦ Φ (NormedSpace.inclusionInDoubleDual ℝ E x))
      Set.univ
      L := by
  -- Route correction: use the canonical double-dual linear isometry instead of the old manual
  -- evaluation-map transport chain.
  rw [is_l_smooth_on_iff] at hΦ ⊢
  refine ⟨?_, ?_⟩
  · intro x hx
    -- Differentiability passes through the continuous linear precomposition.
    exact
      (hΦ.1 (NormedSpace.inclusionInDoubleDual ℝ E x) (by simp)).comp x (by fun_prop)
  · intro x hx y hy
    have hx_comp :
        fderiv ℝ
            (fun z : E ↦ Φ (NormedSpace.inclusionInDoubleDual ℝ E z)) x =
          (fderiv ℝ Φ (NormedSpace.inclusionInDoubleDual ℝ E x)).comp
            (NormedSpace.inclusionInDoubleDual ℝ E) := by
      -- The chain rule computes the derivative of the linear-precomposed function explicitly.
      simpa using
        ((hΦ.1 (NormedSpace.inclusionInDoubleDual ℝ E x) (by simp)).hasFDerivAt.comp x
          (by fun_prop :
            HasFDerivAt
              (fun z : E ↦ NormedSpace.inclusionInDoubleDual ℝ E z)
              (NormedSpace.inclusionInDoubleDual ℝ E) x)).fderiv
    have hy_comp :
        fderiv ℝ
            (fun z : E ↦ Φ (NormedSpace.inclusionInDoubleDual ℝ E z)) y =
          (fderiv ℝ Φ (NormedSpace.inclusionInDoubleDual ℝ E y)).comp
            (NormedSpace.inclusionInDoubleDual ℝ E) := by
      -- The same chain rule formula applies at `y`.
      simpa using
        ((hΦ.1 (NormedSpace.inclusionInDoubleDual ℝ E y) (by simp)).hasFDerivAt.comp y
          (by fun_prop :
            HasFDerivAt
              (fun z : E ↦ NormedSpace.inclusionInDoubleDual ℝ E z)
              (NormedSpace.inclusionInDoubleDual ℝ E) y)).fderiv
    have hA_le : ‖NormedSpace.inclusionInDoubleDual ℝ E‖ ≤ 1 := by
      exact NormedSpace.inclusionInDoubleDual_norm_le ℝ E
    have hnorm_map :
        ‖NormedSpace.inclusionInDoubleDual ℝ E x -
            NormedSpace.inclusionInDoubleDual ℝ E y‖ = ‖x - y‖ := by
      -- The inclusion into the double dual is an isometry.
      simpa [map_sub] using
        (NormedSpace.inclusionInDoubleDualLi (𝕜 := ℝ) (E := E)).norm_map (x - y)
    calc
      ‖fderiv ℝ (fun z : E ↦ Φ (NormedSpace.inclusionInDoubleDual ℝ E z)) x -
          fderiv ℝ (fun z : E ↦ Φ (NormedSpace.inclusionInDoubleDual ℝ E z)) y‖ =
          ‖((fderiv ℝ Φ (NormedSpace.inclusionInDoubleDual ℝ E x) -
              fderiv ℝ Φ (NormedSpace.inclusionInDoubleDual ℝ E y)).comp
                (NormedSpace.inclusionInDoubleDual ℝ E))‖ := by
            rw [hx_comp, hy_comp]
            rfl
      _ ≤ ‖fderiv ℝ Φ (NormedSpace.inclusionInDoubleDual ℝ E x) -
            fderiv ℝ Φ (NormedSpace.inclusionInDoubleDual ℝ E y)‖ *
            ‖NormedSpace.inclusionInDoubleDual ℝ E‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℝ Φ (NormedSpace.inclusionInDoubleDual ℝ E x) -
            fderiv ℝ Φ (NormedSpace.inclusionInDoubleDual ℝ E y)‖ := by
            nlinarith [norm_nonneg
              (fderiv ℝ Φ (NormedSpace.inclusionInDoubleDual ℝ E x) -
                fderiv ℝ Φ (NormedSpace.inclusionInDoubleDual ℝ E y))]
      _ ≤ (L : ℝ) *
            ‖NormedSpace.inclusionInDoubleDual ℝ E x -
              NormedSpace.inclusionInDoubleDual ℝ E y‖ :=
          hΦ.2 _ (by simp) _ (by simp)
      _ = (L : ℝ) * ‖x - y‖ := by rw [hnorm_map]

/-- Identity clause for Proposition 5.17: if `f` and `ω` are proper closed convex
extended-real-valued functions,
and `f □ ω` is everywhere finite, then their infimal convolution equals the primal-side conjugate
of the sum of the conjugates. This is the owner-level rendering of the textbook identity
`f □ ω = (f^* + ω^*)^*`, with the bidual conjugate transported back to `E` by the canonical
equivalence `Module.evalEquiv ℝ E`. The explicit finiteness hypothesis keeps the proposition on the
same source-faithful surface as the chapter's canonical owner theorem. -/
theorem proper_closed_convex_infimal_convolution_eq_dual_conjugate_sum_conjugates
    (f ω : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hω_proper : IsProperExtendedRealFunction ω) (hf_closed : LowerSemicontinuous f)
    (hω_closed : LowerSemicontinuous ω) (hf_convex : is_convex_function f)
    (hω_convex : is_convex_function ω)
    (h_infimal_real : ∀ x, ∃ r : ℝ, (f □ ω) x = (r : EReal)) :
    (infimal_convolution f ω : E → EReal) =
      conjugate_function (conjugate_function f + conjugate_function ω) ∘ Module.evalEquiv ℝ E :=
    by
  let _ := hf_closed
  let _ := hω_closed
  -- Route correction: prove the primal infimal convolution is proper, closed, and convex from the
  -- everywhere-finite hypothesis, then identify it with its biconjugate.
  have h_infimal_convex : is_convex_function (f □ ω) := by
    exact
      infimalConvolution_isConvex_ofConvexEReal
        f ω hf_convex hω_convex hf_proper.ne_bot hω_proper.ne_bot
  have h_infimal_closed : LowerSemicontinuous (f □ ω) := by
    exact
      lowerSemicontinuous_of_isConvex_realValued
        (f □ ω) h_infimal_convex h_infimal_real
  have h_infimal_proper : IsProperExtendedRealFunction (f □ ω) := by
    exact infimalConvolution_isProper_of_realValued f ω h_infimal_real
  have h_infimal_biconjugate : (f □ ω) = biconjugate_function (f □ ω) := by
    simpa using
      (biconjugate_function_eq_self_of_proper_closed_convex
        (f □ ω) h_infimal_proper h_infimal_closed h_infimal_convex).symm
  -- Replace the inner conjugate of the biconjugate using the Chapter 4 infimal-convolution rule.
  calc
    (f □ ω) = biconjugate_function (f □ ω) := h_infimal_biconjugate
    _ =
        conjugate_function
          (conjugate_function f + conjugate_function ω)
          ∘ Module.evalEquiv ℝ E := by
            ext x
            rw [biconjugate_function]
            rw [conjugate_function_infimal_convolution_eq_add_of_proper
              f ω hf_proper hω_proper]
            simp [Function.comp]

/-- Pointwise companion to Proposition 5.17 (1), spelling the bidual pullback as evaluation at
`Module.Dual.eval ℝ E x`. -/
theorem proper_closed_convex_infimal_convolution_eq_dual_conjugate_sum_conjugates_apply
    (f ω : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hω_proper : IsProperExtendedRealFunction ω) (hf_closed : LowerSemicontinuous f)
    (hω_closed : LowerSemicontinuous ω) (hf_convex : is_convex_function f)
    (hω_convex : is_convex_function ω)
    (h_infimal_real : ∀ x, ∃ r : ℝ, (f □ ω) x = (r : EReal)) (x : E) :
    (f □ ω) x =
      conjugate_function
        (conjugate_function f + conjugate_function ω)
        (Module.Dual.eval ℝ E x) := by
  simpa using congrArg (fun h : E → EReal ↦ h x)
    (proper_closed_convex_infimal_convolution_eq_dual_conjugate_sum_conjugates
      f ω hf_proper hω_proper hf_closed hω_closed hf_convex hω_convex h_infimal_real)

/-- Helper for Proposition 5.17: evaluating the conjugate of the continuous-dual conjugate sum on
the canonical double-dual image of `x` recovers `(f □ ω) x`. -/
private lemma conjugateSumStrongDual_eval_toReal_eq_infimalConvolution_toReal
    (f ω : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hω_proper : IsProperExtendedRealFunction ω) (hf_closed : LowerSemicontinuous f)
    (hω_closed : LowerSemicontinuous ω) (hf_convex : is_convex_function f)
    (hω_convex : is_convex_function ω)
    (h_infimal_real : ∀ x, ∃ r : ℝ, (f □ ω) x = (r : EReal)) :
    (fun x : E ↦
      (conjugate_function_strongDual
        (fun y : StrongDual ℝ E ↦
          conjugate_function_strongDual f y + conjugate_function_strongDual ω y)
        (NormedSpace.inclusionInDoubleDual ℝ E x)).toReal) =
      fun x ↦ ((f □ ω) x).toReal := by
  -- Rewrite both conjugate surfaces as the same supremum after transporting the domain by
  -- `LinearMap.toContinuousLinearMap`, then invoke clause (1).
  funext x
  have hrange :
      Set.range
        (fun y : StrongDual ℝ E ↦
          ((y x : ℝ) : EReal) -
            (conjugate_function f (y : Module.Dual ℝ E) +
              conjugate_function ω (y : Module.Dual ℝ E))) =
      Set.range
        (fun y : Module.Dual ℝ E ↦
          ((y x : ℝ) : EReal) -
            (conjugate_function f y + conjugate_function ω y)) := by
    ext a
    constructor
    · rintro ⟨y, rfl⟩
      refine
        ⟨((LinearMap.toContinuousLinearMap : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E).symm y), ?_⟩
      simp
    · rintro ⟨y, rfl⟩
      refine ⟨LinearMap.toContinuousLinearMap y, ?_⟩
      simp
  have hvalue :
      conjugate_function_strongDual
          (fun y : StrongDual ℝ E ↦
            conjugate_function_strongDual f y + conjugate_function_strongDual ω y)
          (NormedSpace.inclusionInDoubleDual ℝ E x) =
        conjugate_function
          (conjugate_function f + conjugate_function ω)
          (Module.Dual.eval ℝ E x) := by
    -- The conjugate supremum is unchanged after identifying `E*` with `StrongDual ℝ E`.
    rw [conjugate_function_strongDual_apply, conjugate_function_apply, conjugate_function_apply]
    simpa using congrArg sSup hrange
  -- Finish by rewriting the algebraic-dual conjugate through clause (1).
  rw [hvalue]
  symm
  simpa using
    congrArg EReal.toReal
      (proper_closed_convex_infimal_convolution_eq_dual_conjugate_sum_conjugates_apply
        f ω hf_proper hω_proper hf_closed hω_closed hf_convex hω_convex h_infimal_real x)

/-- Proposition 5.17: if `f` and `ω` are proper closed convex extended-real-valued functions
and the continuous-dual Fenchel conjugate `ω^*` is `(1 / L)`-strongly convex, then the real-valued
infimal convolution `x ↦ ((f □ ω) x).toReal` is globally `L`-smooth, provided `f □ ω` is
everywhere finite. This is the canonical continuous-dual formulation of the textbook clause that
`ω^*` being `(1 / L)`-strongly convex, equivalently `ω` being `L`-smooth, implies `f □ ω` is
`L`-smooth; the explicit finiteness assumption keeps the global `toReal` surface faithful to the
chapter's owner theorem. -/
theorem infimal_convolution_toReal_is_l_smooth_of_conjugate_strongConvex
    (f ω : E → EReal) (L : NNReal) (hL_pos : 0 < L) (hf_proper : IsProperExtendedRealFunction f)
    (hω_proper : IsProperExtendedRealFunction ω) (hf_closed : LowerSemicontinuous f)
    (hω_closed : LowerSemicontinuous ω) (hf_convex : is_convex_function f)
    (hω_convex : is_convex_function ω)
    (h_infimal_real : ∀ x, ∃ r : ℝ, (f □ ω) x = (r : EReal))
    (hω_star_strong :
      StrongConvexOn
        (effective_domain (conjugate_function_strongDual ω))
        (1 / (L : ℝ))
        (fun y ↦ (conjugate_function_strongDual ω y).toReal)) :
    is_l_smooth_on (fun x ↦ ((f □ ω) x).toReal) Set.univ L := by
  -- Keep the proof on the conjugate-sum surface until the final rewrite back to `f □ ω`.
  let g : StrongDual ℝ E → EReal := fun y ↦
    conjugate_function_strongDual f y + conjugate_function_strongDual ω y
  have hσ_pos : 0 < (1 / (L : ℝ)) := by
    positivity
  have hg_proper : IsProperExtendedRealFunction g := by
    -- Properness comes from the already finite infimal convolution side.
    simpa [g] using
      sumConjugatesStrongDual_isProper
        f ω hf_proper hω_proper hf_convex hω_convex h_infimal_real
  have hg_closed : LowerSemicontinuous g := by
    -- Closedness is inherited termwise from the continuous-dual conjugates.
    refine
      ((conjugateFunctionStrongDual_closedConvex f).1).add'
        ((conjugateFunctionStrongDual_closedConvex ω).1) ?_
    intro y
    simpa [g] using
      (EReal.continuousAt_add
        (p := (conjugate_function_strongDual f y, conjugate_function_strongDual ω y))
        (Or.inr (conjugate_function_ne_bot_of_proper ω hω_proper y))
        (Or.inl (conjugate_function_ne_bot_of_proper f hf_proper y)))
  have hg_strong :
      StrongConvexOn
        (effective_domain g)
        (1 / (L : ℝ))
        (fun y ↦ (g y).toReal) := by
    -- Lemma 5.20 preserves the strong-convexity modulus after adding the convex conjugate of `f`.
    simpa [g] using
      sumConjugatesStrongDual_strongConvexOn
        f ω L hL_pos hf_proper hω_proper hf_convex hω_star_strong
  have hsmooth_dual :
      is_l_smooth_on
        (fun z : StrongDual ℝ (StrongDual ℝ E) ↦
          (conjugate_function_strongDual g z).toReal)
        Set.univ
        (Real.toNNReal (1 / (1 / (L : ℝ)))) := by
    -- This is exactly Theorem 5.26 applied to the conjugate sum `g`.
    simpa [g] using
      is_l_smooth_on_toReal_conjugate_function_strongDual_of_proper_closed_strongConvexOn
        (σ := 1 / (L : ℝ)) hσ_pos g hg_proper hg_closed hg_strong
  have hsmooth_primal :
      is_l_smooth_on
        (fun x : E ↦
          (conjugate_function_strongDual g
            (NormedSpace.inclusionInDoubleDual ℝ E x)).toReal)
        Set.univ
        (Real.toNNReal (1 / (1 / (L : ℝ)))) := by
    -- Precompose with the canonical isometric inclusion `E → E**`.
    exact
      isLSmoothOn_precomposeInclusionInDoubleDual
        (Φ := fun z : StrongDual ℝ (StrongDual ℝ E) ↦
          (conjugate_function_strongDual g z).toReal)
        (L := Real.toNNReal (1 / (1 / (L : ℝ))))
        hsmooth_dual
  have hrewrite :
      (fun x : E ↦
        (conjugate_function_strongDual g
          (NormedSpace.inclusionInDoubleDual ℝ E x)).toReal) =
      fun x ↦ ((f □ ω) x).toReal := by
    -- Clause (1) identifies the bidual conjugate surface with the target infimal convolution.
    simpa [g] using
      conjugateSumStrongDual_eval_toReal_eq_infimalConvolution_toReal
        f ω hf_proper hω_proper hf_closed hω_closed hf_convex hω_convex h_infimal_real
  have hL_real_pos : 0 < (L : ℝ) := hL_pos
  have hsmooth_const :
      Real.toNNReal (1 / (1 / (L : ℝ))) = L := by
    apply Subtype.ext
    change max (1 / (1 / (L : ℝ))) 0 = (L : ℝ)
    rw [max_eq_left (le_of_lt (by positivity))]
    field_simp [hL_real_pos.ne']
  simpa [hrewrite, hsmooth_const] using hsmooth_primal

end

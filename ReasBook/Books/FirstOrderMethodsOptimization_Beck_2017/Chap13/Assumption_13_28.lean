/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_2
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_3
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_4
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Assumption_13_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v

section

variable {ι : Type v} [Fintype ι] {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)]
variable [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, CompleteSpace (Ei i)]

local notation "X" => PiLp 2 Ei

/- `prompt_add/` is absent in this workspace, so the declaration shape is sampled from the nearby
Chapter 13 generalized conditional-gradient owners and the Chapter 11 block-gradient owners.

Primary domain sample:
- `IsConditionalGradientProblem` and `IsGeneralizedConditionalGradientProblem` from Chapter 13
  show the chapter style: keep source-facing assumptions directly on the chapter objects, and let
  properness or interior-domain consequences be derived API.
- `IsBlockProximalGradientProblem` from Chapter 11 is the best `core/canonical` owner for the
  shared blockwise penalty, optimizer, and block-Lipschitz data, because it captures exactly the
  blockwise optimization core without the extra randomized convexity package.
- `RandomizedBlockProximalGradientAssumptions` is relevant but too strong as a primitive owner for
  Assumption 13.28: inheriting it would force raw-coordinate packaging and extra Chapter 11 fields
  such as `f_closed` that are not source-facing in this chapter.
- `PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei` is the canonical coordinate equivalence
  between the `PiLp` model and the raw block product.
- Chapter 11's singleton-update notation `x + 𝒰[i] d` and `block_partial_gradient`, notation
  `∇[i] f`, are the canonical source-facing one-block update and block gradient owners on
  `PiLp 2 Ei`.

This item is `source-facing`: the public owner should speak directly about the chapter objects
`f : PiLp 2 Ei → EReal`, the block penalties `g_i`, the canonical `PiLp` block gradient `∇[i]`,
and the singleton-update surface `x + 𝒰[i] d`. The canonical optimizer set and optimal value
already live upstream as
`unconstrained_problem_solutions (composite_model_objective f (PiLp.separableSum g))` and
`generalized_conditional_gradient_optimal_value f (PiLp.separableSum g)`, so Assumption 13.28
should derive those owners instead of storing a parallel `XStar`/`FOpt` wrapper layer. The
Chapter 11 packaged problem owners remain part of the domain sample, but Assumption 13.28 should
not inherit them because that would reintroduce non-source fields such as `f_closed`. The only
retained `bridge/view` data are the induced raw-product block gradient `blockGradient f` and,
under an auxiliary global smoothness witness, the canonical Chapter 13 owner bridge to
`IsGeneralizedConditionalGradientProblem`.
-/

namespace GeneralizedBlockConditionalGradient

/-- The canonical RGBCG block gradient is the Chapter 11 block partial gradient
`∇[i] (fun z ↦ (f z).toReal)`, evaluated at the `PiLp` point corresponding to the raw block tuple
`y`. This is the Chapter 13 `bridge/view` map used when translating the source-facing `PiLp`
problem into the Chapter 11 raw-product owner. -/
abbrev blockGradient (f : X → EReal) :
    (i : ι) → ((j : ι) → Ei j) → Ei i :=
  fun i y ↦
    (∇[i] fun z : X ↦ (f z).toReal)
      ((PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei).symm y)

/-- Evaluating the canonical RGBCG block gradient at `(i, y)` recovers the corresponding block
partial gradient of `x ↦ (f x).toReal` on `PiLp 2 Ei`. -/
@[simp] theorem blockGradient_apply
    (f : X → EReal) (i : ι) (y : (j : ι) → Ei j) :
    blockGradient f i y =
      (∇[i] fun z : X ↦ (f z).toReal)
        ((PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei).symm y) :=
  rfl

/-- Evaluating the RGBCG bridge map at the raw coordinates of `x : PiLp 2 Ei` recovers the
source-facing block partial gradient at `x`. -/
@[simp] theorem blockGradient_coord_apply
    (f : X → EReal) (i : ι) (x : X) :
    blockGradient f i ((PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei) x) =
      (∇[i] fun z : X ↦ (f z).toReal) x := by
  rfl

end GeneralizedBlockConditionalGradient

end

open scoped Gradient

section

variable {ι : Type v} [Fintype ι] {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)]
variable [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, CompleteSpace (Ei i)]

local notation "X" => PiLp 2 Ei
attribute [local instance] Classical.decEq

/-- Assumption 13.28: clauses (A)-(D) for the randomized generalized block conditional-gradient
method are expressed directly on the chapter objects `f : X → EReal`, the block penalties `g_i`,
the canonical `PiLp` block gradient `∇[i] (fun z ↦ (f z).toReal)`. The public owner keeps only
the primitive regularity, domain-compatibility, differentiability, and block-Lipschitz clauses on
the `PiLp` model; the canonical optimizer set
`unconstrained_problem_solutions (composite_model_objective f (PiLp.separableSum g))` and optimal
value `generalized_conditional_gradient_optimal_value f (PiLp.separableSum g)` are derived below
rather than stored as wrapper parameters. The one-block update and slice are written in the
canonical Chapter 11 textbook form `x + 𝒰[i] d`. -/
class IsGeneralizedBlockConditionalGradientProblem
    (f : X → EReal) (g : (i : ι) → Ei i → EReal)
    (Li : (i : ι) → PosReal) : Prop where
  block_g_proper (i : ι) : IsProperExtendedRealFunction (g i)
  block_g_closed (i : ι) : LowerSemicontinuous (g i)
  block_g_convex (i : ι) : is_convex_function (g i)
  g_effective_domain_compact (i : ι) : IsCompact (effective_domain (g i))
  f_ne_bot (x : X) : f x ≠ ⊥
  f_convex : is_convex_function f
  g_effective_domain_subset_f_effective_domain :
    effective_domain (PiLp.separableSum g) ⊆ effective_domain f
  f_effective_domain_open : IsOpen (effective_domain f)
  f_toReal_differentiableOn_effective_domain :
    DifferentiableOn ℝ (fun x ↦ (f x).toReal) (effective_domain f)
  block_partial_gradient_lipschitz
      (i : ι) {x : X} {d : Ei i}
      (hx : x ∈ effective_domain f)
      (hxd : x + (𝒰[i] d : X) ∈ effective_domain f) :
      ‖(∇[i] fun z : X ↦ (f z).toReal) x -
          (∇[i] fun z : X ↦ (f z).toReal) (x + (𝒰[i] d : X))‖ ≤
        (Li i : ℝ) * ‖d‖

namespace IsGeneralizedBlockConditionalGradientProblem

variable {f : X → EReal} {g : (i : ι) → Ei i → EReal} {Li : (i : ι) → PosReal}

local notation "F" => composite_model_objective f (PiLp.separableSum g)
local notation "Fopt" => generalized_conditional_gradient_optimal_value f (PiLp.separableSum g)

/-- The effective domain of the block-separable regularizer is compact, because it is the `PiLp`
transport of the finite product of the compact coordinate domains
`effective_domain (g i)`. -/
theorem separableSum_effective_domain_compact
    (h : IsGeneralizedBlockConditionalGradientProblem f g Li) :
    IsCompact (effective_domain (PiLp.separableSum g)) := by
  let e := PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei
  let he := e.symm.toHomeomorph
  have hproduct :
      IsCompact (Set.pi Set.univ (fun i ↦ effective_domain (g i))) :=
    isCompact_univ_pi (fun i ↦ h.g_effective_domain_compact i)
  have hdomain :
      effective_domain (PiLp.separableSum g) =
        e.symm ⁻¹' Set.pi Set.univ (fun i ↦ effective_domain (g i)) := by
    -- Identify the PiLp feasible core with the preimage of the product of block domains.
    ext x
    simp [mem_effective_domain, PiLp.separableSum_apply]
  -- Transport compactness back through the canonical PiLp/raw-coordinate homeomorphism.
  rw [hdomain]
  simpa using he.isCompact_preimage.mpr hproduct

/-- This owner is more source-facing than the Chapter 13 owner
`IsGeneralizedConditionalGradientProblem`: it keeps the blockwise differentiability and
block-Lipschitz clauses rather than storing a global smoothness constant on `effective_domain f`.
Whenever such a global smoothness witness is available separately, the aggregate regularizer
`PiLp.separableSum g` and the existing Chapter 13 owner should be reused directly instead of
rebuilding its downstream API locally. -/
theorem toIsGeneralizedConditionalGradientProblem
    (h : IsGeneralizedBlockConditionalGradientProblem f g Li)
    {Lf : NNReal}
    (hf_toReal_smooth_on_effective_domain :
      is_l_smooth_on (fun x ↦ (f x).toReal) (effective_domain f) Lf)
    (hLf_pos : 0 < (Lf : ℝ)) :
    IsGeneralizedConditionalGradientProblem f (PiLp.separableSum g) Lf := by
  refine
    { toIsProperExtendedRealFunction := separableSum_proper g h.block_g_proper
      g_closed := separableSum_closed g h.block_g_closed
      g_convex := separableSum_convex g h.block_g_proper h.block_g_convex
      g_effective_domain_compact := h.separableSum_effective_domain_compact
      f_ne_bot := h.f_ne_bot
      f_effective_domain_open := h.f_effective_domain_open
      f_effective_domain_convex := effective_domain_convex_of_is_convex_function h.f_convex
      g_effective_domain_subset_f_effective_domain :=
        h.g_effective_domain_subset_f_effective_domain
      f_toReal_smooth_on_effective_domain := hf_toReal_smooth_on_effective_domain
      Lf_pos := hLf_pos }

/-- On the compact block-feasible core `effective_domain (PiLp.separableSum g)`, the composite
objective `F(x) = f(x) + ∑ i, g_i(x_i)` is lower semicontinuous. -/
theorem composite_model_objective_lowerSemicontinuousOn_effective_domain
    (h : IsGeneralizedBlockConditionalGradientProblem f g Li) :
    LowerSemicontinuousOn F (effective_domain (PiLp.separableSum g)) := by
  have hf_cont : ContinuousOn (fun x ↦ ((f x).toReal : EReal))
      (effective_domain (PiLp.separableSum g)) := by
    -- The smooth term is continuous on the feasible core because it is differentiable on the open
    -- ambient effective domain and the feasible core lies inside that domain.
    refine
      (continuous_coe_real_ereal.continuousOn : ContinuousOn ((↑) : ℝ → EReal) Set.univ).comp
        ?_ ?_
    · intro x hx
      exact
        ((h.f_toReal_differentiableOn_effective_domain x
          (h.g_effective_domain_subset_f_effective_domain hx)).continuousAt).continuousWithinAt
    · intro x hx
      simp
  have hsum :
      LowerSemicontinuousOn
        (fun x ↦ ((f x).toReal : EReal) + PiLp.separableSum g x)
        (effective_domain (PiLp.separableSum g)) := by
    -- Add the continuous finite-valued part to the lower-semicontinuous separable regularizer.
    refine
      hf_cont.lowerSemicontinuousOn.add'
        ((separableSum_closed g h.block_g_closed).lowerSemicontinuousOn _) ?_
    intro x hx
    exact EReal.continuousAt_add (.inl (EReal.coe_ne_top _)) (.inl (EReal.coe_ne_bot _))
  intro x hx
  -- On the feasible core, `f.toReal` agrees with `f`, so the transported sum is the composite
  -- objective itself.
  refine (hsum x hx).congr_of_eventuallyEq hx ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp [F, composite_model_objective_apply, EReal.coe_toReal
    (mem_effective_domain.mp (h.g_effective_domain_subset_f_effective_domain hy)).ne
    (h.f_ne_bot y)]

/-- These hypotheses derive attainment of the minimum on the canonical optimizer set
`unconstrained_problem_solutions (composite_model_objective f (PiLp.separableSum g))`. -/
theorem optimal_set_nonempty
    (h : IsGeneralizedBlockConditionalGradientProblem f g Li) :
    (unconstrained_problem_solutions F).Nonempty := by
  rcases (separableSum_proper g h.block_g_proper).effective_domain_nonempty with ⟨y, hy⟩
  have hyF : y ∈ effective_domain F := by
    -- A feasible point for the separable regularizer is also feasible for the composite objective.
    exact mem_effective_domain.mpr <|
      by
        simpa [F, composite_model_objective_apply] using
          (EReal.add_lt_top
            (mem_effective_domain.mp (h.g_effective_domain_subset_f_effective_domain hy)).ne
            (mem_effective_domain.mp hy).ne)
  obtain ⟨x, _, hxmin⟩ :=
    exists_isMinOn_on_compact
      F
      (effective_domain (PiLp.separableSum g))
      h.composite_model_objective_lowerSemicontinuousOn_effective_domain
      h.separableSum_effective_domain_compact
      ⟨y, ⟨hy, hyF⟩⟩
  have hxmin_univ : IsMinOn F Set.univ x :=
    (isMinOn_composite_model_objective_univ_iff_isMinOn_effective_domain h.f_ne_bot).2 hxmin
  exact ⟨x, mem_unconstrained_problem_solutions_iff.mpr hxmin_univ⟩

/-- The canonical Chapter 13 optimal value `F_opt` is the greatest lower bound of the attainable
composite objective values under these hypotheses. -/
theorem optimal_value_isGLB
    (h : IsGeneralizedBlockConditionalGradientProblem f g Li) :
    IsGLB (Set.range F) Fopt := by
  rw [generalized_conditional_gradient_optimal_value_eq_sInf]
  rcases h.optimal_set_nonempty with ⟨xStar, hxStar⟩
  exact isGLB_csInf ⟨F xStar, ⟨xStar, rfl⟩⟩

/-- Every point of the canonical optimizer set attains the canonical Chapter 13 optimal value
`F_opt`. -/
theorem optimal_value_eq_of_mem_optimal_set
    (h : IsGeneralizedBlockConditionalGradientProblem f g Li)
    {xStar : X} (hxStar : xStar ∈ unconstrained_problem_solutions F) :
    Fopt = F xStar := by
  have hxmin : IsMinOn F Set.univ xStar := by
    simpa using hxStar
  have hglb : IsGLB (Set.range F) (F xStar) := by
    simpa using hxmin.isGLB (by simp : xStar ∈ (Set.univ : Set X))
  rw [generalized_conditional_gradient_optimal_value_eq_sInf]
  exact hglb.csInf_eq ⟨F xStar, ⟨xStar, rfl⟩⟩

/-- Helper: transporting the composite objective through the canonical
PiLp/raw-coordinate equivalence does not change its pointwise value. -/
private theorem transported_composite_model_objective_apply
    (y : (j : ι) → Ei j) :
    composite_model_objective
        (fun z : (j : ι) → Ei j ↦
          f ((PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei).symm z))
        (separableSum g) y =
      F ((PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei).symm y) := by
  -- The coordinate equivalence preserves every block coordinate, hence preserves the separable
  -- regularizer and the whole composite objective.
  simp [F, composite_model_objective_apply, PiLp.separableSum_apply]

/-- Helper: a raw one-block update transports back to the corresponding PiLp
singleton update. -/
private theorem symm_block_coordinate_update_eq_add_single
    (y : (j : ι) → Ei j) (i : ι) (d : Ei i) :
    (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei).symm (block_coordinate_update y i d) =
      ((PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei).symm y) + (𝒰[i] d : X) := by
  -- Compare the two PiLp points coordinatewise: the updated block gains `d` and the others stay
  -- fixed.
  ext j
  by_cases hj : j = i
  · subst j
    simp [block_coordinate_update]
  · simp [block_coordinate_update, hj]

/-- Helper: the one-block PiLp update is Frechet differentiable with the
canonical singleton-insertion derivative. -/
private theorem block_update_hasFDerivAt
    (x : X) (i : ι) :
    HasFDerivAt
      (fun d : Ei i ↦ x + (𝒰[i] d : X))
      (((PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei).symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.single ℝ Ei i))
      0 := by
  have hsingle :
      HasFDerivAt
        (fun d : Ei i ↦ (Pi.single i d : (j : ι) → Ei j))
        (ContinuousLinearMap.single ℝ Ei i)
        0 := by
    simpa using (ContinuousLinearMap.single ℝ Ei i).hasFDerivAt
  have htoLp :
      HasFDerivAt
        (fun z : (j : ι) → Ei j ↦
          (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei).symm z)
        (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei).symm.toContinuousLinearMap
        (Pi.single i (0 : Ei i)) := by
    simpa using
      (((PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei).symm.toContinuousLinearMap).hasFDerivAt :
        HasFDerivAt
          (fun z : (j : ι) → Ei j ↦
            (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei).symm z)
          (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei).symm.toContinuousLinearMap
          (Pi.single i (0 : Ei i)))
  -- Compose the raw singleton insertion with `toLp`, then translate by the base point `x`.
  simpa [block_coordinate_update, PiLp.coe_symm_continuousLinearEquiv, PiLp.toLp_single]
    using (htoLp.comp 0 hsingle).const_add x

/-- Helper: differentiability of `f.toReal` on the open effective domain
gives the Fréchet-derivative formula for the one-block slice `d ↦ f(x + 𝒰[i] d)` at `0`. -/
private theorem block_partial_gradient_hasFDerivAt
    (h : IsGeneralizedBlockConditionalGradientProblem f g Li)
    (i : ι) {x : X}
    (hx : x ∈ effective_domain f) :
    HasFDerivAt (fun d ↦ (f (x + (𝒰[i] d : X))).toReal)
      (InnerProductSpace.toDualMap ℝ (Ei i) ((∇[i] fun z : X ↦ (f z).toReal) x)) 0 := by
  have hdiffAt : DifferentiableAt ℝ (fun z : X ↦ (f z).toReal) x := by
    -- The open-domain hypothesis upgrades within-domain differentiability to ordinary
    -- differentiability at the base point.
    exact
      (h.f_toReal_differentiableOn_effective_domain x hx).differentiableAt
        (h.f_effective_domain_open.mem_nhds hx)
  have hbase :
      HasFDerivAt
        (fun z : X ↦ (f z).toReal)
        (InnerProductSpace.toDualMap ℝ X ((∇ fun z : X ↦ (f z).toReal) x))
        x :=
    hdiffAt.hasGradientAt.hasFDerivAt
  have hcomp := hbase.comp 0 (block_update_hasFDerivAt x i)
  -- Rewrite the composed derivative as the expected block partial gradient functional.
  simpa [block_partial_gradient_eq_gradient, ContinuousLinearMap.comp_apply,
    InnerProductSpace.toDualMap_apply_apply, PiLp.inner_apply]
    using hcomp

/-- The Chapter 13 generalized block conditional-gradient owner is more general than the Chapter
11 raw-product block proximal-gradient owner: it keeps the smooth term on the canonical `PiLp`
model and does not assume closedness of `f`. Under the extra source-faithful regularity hypothesis
that `f` is lower semicontinuous, transport along `PiLp.continuousLinearEquiv` yields the Chapter
11 `core/canonical` owner on raw block coordinates, with `blockGradient f` as the induced block
gradient and the optimizer set carried across by the coordinate equivalence. -/
theorem toIsBlockProximalGradientProblem
    (h : IsGeneralizedBlockConditionalGradientProblem f g Li)
    (hf_closed : LowerSemicontinuous f) :
    IsBlockProximalGradientProblem
      (fun y : (j : ι) → Ei j ↦
        f ((PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei).symm y))
      g
      (GeneralizedBlockConditionalGradient.blockGradient f)
      (((PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei).symm) ⁻¹'
        unconstrained_problem_solutions F)
      (generalized_conditional_gradient_optimal_value f (PiLp.separableSum g)).toReal
      Li := by
  let e := PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei
  have hopen_preimage :
      IsOpen (effective_domain (fun y : (j : ι) → Ei j ↦ f (e.symm y))) := by
    -- The transported smooth-term domain is the preimage of the open PiLp domain.
    simpa [effective_domain, mem_effective_domain] using
      h.f_effective_domain_open.preimage e.symm.continuous
  refine
    { f_ne_bot := fun y ↦ h.f_ne_bot (e.symm y)
      block_g_proper := h.block_g_proper
      block_g_closed := h.block_g_closed
      block_g_convex := h.block_g_convex
      f_closed := by
        -- Lower semicontinuity transports along the coordinate homeomorphism.
        simpa using hf_closed.comp e.symm.continuous
      g_effective_domain_subset_interior_f_effective_domain := by
        intro y hy
        have hy' :
            e.symm y ∈ effective_domain (PiLp.separableSum g) := by
          simpa [effective_domain, mem_effective_domain, PiLp.separableSum_apply] using hy
        have hyf : y ∈ effective_domain (fun z : (j : ι) → Ei j ↦ f (e.symm z)) := by
          simpa [effective_domain, mem_effective_domain] using
            h.g_effective_domain_subset_f_effective_domain hy'
        simpa [hopen_preimage.interior_eq] using hyf
      optimal_set_eq := by
        -- Minimizers are preserved by transporting the objective through the equivalence.
        ext y
        rw [mem_unconstrained_problem_solutions_iff, mem_unconstrained_problem_solutions_iff]
        constructor
        · intro hy
          rw [isMinOn_univ_iff] at hy ⊢
          intro z
          simpa [transported_composite_model_objective_apply]
            using hy (e.symm z) (by simp)
        · intro hy
          rw [isMinOn_univ_iff] at hy ⊢
          intro z
          simpa [transported_composite_model_objective_apply]
            using hy (e z) (by simp)
      optimal_set_nonempty := by
        rcases h.optimal_set_nonempty with ⟨xStar, hxStar⟩
        exact ⟨e xStar, by simpa using hxStar⟩
      optimal_value_isGLB := by
        rcases h.optimal_set_nonempty with ⟨xStar, hxStar⟩
        rcases (separableSum_proper g h.block_g_proper).effective_domain_nonempty with ⟨y, hy⟩
        have hyF : y ∈ effective_domain F := by
          exact mem_effective_domain.mpr <|
            by
              simpa [F, composite_model_objective_apply] using
                (EReal.add_lt_top
                  (mem_effective_domain.mp (h.g_effective_domain_subset_f_effective_domain hy)).ne
                  (mem_effective_domain.mp hy).ne)
        have hxmin : IsMinOn F Set.univ xStar := by
          simpa using hxStar
        have hxStar_top : F xStar < ⊤ := by
          exact lt_of_le_of_lt (hxmin (by simp : y ∈ (Set.univ : Set X))) (mem_effective_domain.mp hyF)
        have hxStar_ne_bot : F xStar ≠ ⊥ := by
          rw [F, composite_model_objective_apply, EReal.add_ne_bot_iff]
          exact ⟨h.f_ne_bot xStar, (separableSum_proper g h.block_g_proper).ne_bot xStar⟩
        have hopt_coe :
            (((generalized_conditional_gradient_optimal_value f (PiLp.separableSum g)).toReal :
                ℝ) : EReal) =
              generalized_conditional_gradient_optimal_value f (PiLp.separableSum g) := by
          rw [h.optimal_value_eq_of_mem_optimal_set hxStar]
          exact EReal.coe_toReal (lt_top_iff_ne_top.mp hxStar_top) hxStar_ne_bot
        have hrange :
            Set.range
              (composite_model_objective
                (fun y : (j : ι) → Ei j ↦ f (e.symm y))
                (separableSum g)) =
              Set.range F := by
          ext u
          constructor
          · rintro ⟨y, rfl⟩
            exact ⟨e.symm y, by
              simpa [transported_composite_model_objective_apply]⟩
          · rintro ⟨x, rfl⟩
            exact ⟨e x, by
              simpa [transported_composite_model_objective_apply]⟩
        rw [hrange]
        simpa [hopt_coe] using h.optimal_value_isGLB
      block_partial_gradient_spec := by
        intro i y hy
        have hy' : e.symm y ∈ effective_domain f := by
          have : y ∈ effective_domain (fun z : (j : ι) → Ei j ↦ f (e.symm z)) := by
            simpa [hopen_preimage.interior_eq] using hy
          simpa [effective_domain, mem_effective_domain] using this
        -- Rewrite the raw one-block slice back to the PiLp slice and reuse the earlier helper.
        simpa [block_coordinate_slice_apply,
          symm_block_coordinate_update_eq_add_single y i,
          GeneralizedBlockConditionalGradient.blockGradient_apply]
          using block_partial_gradient_hasFDerivAt h i hy'
      block_partial_gradient_lipschitz := by
        intro i y d hy hyd
        have hy' : e.symm y ∈ effective_domain f := by
          have : y ∈ effective_domain (fun z : (j : ι) → Ei j ↦ f (e.symm z)) := by
            simpa [hopen_preimage.interior_eq] using hy
          simpa [effective_domain, mem_effective_domain] using this
        have hyd' : e.symm (block_coordinate_update y i d) ∈ effective_domain f := by
          have : block_coordinate_update y i d ∈
              effective_domain (fun z : (j : ι) → Ei j ↦ f (e.symm z)) := by
            simpa [hopen_preimage.interior_eq] using hyd
          simpa [effective_domain, mem_effective_domain] using this
        -- The transported block gradient and transported block update match the PiLp owner data.
        simpa [GeneralizedBlockConditionalGradient.blockGradient_apply,
          symm_block_coordinate_update_eq_add_single y i]
          using h.block_partial_gradient_lipschitz i hy' hyd' }

theorem block_partial_gradient_spec
    (h : IsGeneralizedBlockConditionalGradientProblem f g Li)
    (i : ι) {x : X}
    (hx : x ∈ effective_domain f) :
    HasFDerivAt (fun d ↦ (f (x + (𝒰[i] d : X))).toReal)
      (InnerProductSpace.toDualMap ℝ (Ei i) ((∇[i] fun z : X ↦ (f z).toReal) x)) 0 := by
  -- This is exactly the slice-derivative helper established before the Chapter 11 transport.
  exact block_partial_gradient_hasFDerivAt h i hx

theorem g_effective_domain_subset_interior_f_effective_domain
    (h : IsGeneralizedBlockConditionalGradientProblem f g Li) :
    effective_domain (PiLp.separableSum g) ⊆ interior (effective_domain f) := by
  simpa [h.f_effective_domain_open.interior_eq] using
    h.g_effective_domain_subset_f_effective_domain

private theorem separableSum_effective_domain_nonempty
    (h : IsGeneralizedBlockConditionalGradientProblem f g Li) :
    (effective_domain (PiLp.separableSum g)).Nonempty := by
  classical
  choose y hy using fun i ↦ (h.block_g_proper i).effective_domain_nonempty
  let y0 : X := WithLp.toLp 2 (fun j ↦ y j)
  have hy0 : y0 ∈ effective_domain (PiLp.separableSum g) := by
    rw [mem_effective_domain, PiLp.separableSum_apply]
    exact ereal_sum_lt_top Finset.univ (fun i ↦ g i (y0 i))
      (fun i _ ↦ by simpa [y0, PiLp.toLp_apply] using hy i)
  exact ⟨y0, hy0⟩

theorem f_effective_domain_nonempty
    (h : IsGeneralizedBlockConditionalGradientProblem f g Li) :
    (effective_domain f).Nonempty := by
  rcases h.separableSum_effective_domain_nonempty with ⟨x, hx⟩
  exact ⟨x, h.g_effective_domain_subset_f_effective_domain hx⟩

theorem f_proper
    (h : IsGeneralizedBlockConditionalGradientProblem f g Li) :
    IsProperExtendedRealFunction f where
  ne_bot := h.f_ne_bot
  effective_domain_nonempty := h.f_effective_domain_nonempty

end IsGeneralizedBlockConditionalGradientProblem

/-- A generalized block conditional-gradient problem canonically makes the smooth term `f` a
proper extended-real-valued function. -/
instance instIsProperExtendedRealFunctionSmoothTerm
    {f : X → EReal} {g : (i : ι) → Ei i → EReal}
    {Li : (i : ι) → PosReal}
    (h : IsGeneralizedBlockConditionalGradientProblem f g Li) :
    IsProperExtendedRealFunction f where
  ne_bot := h.f_ne_bot
  effective_domain_nonempty := by
    classical
    choose y hy using fun i ↦ (h.block_g_proper i).effective_domain_nonempty
    let y0 : X := WithLp.toLp 2 (fun j ↦ y j)
    have hy0 : y0 ∈ effective_domain (PiLp.separableSum g) := by
      rw [mem_effective_domain, PiLp.separableSum_apply]
      exact ereal_sum_lt_top Finset.univ (fun i ↦ g i (y0 i))
        (fun i _ ↦ by simpa [y0, PiLp.toLp_apply] using hy i)
    exact ⟨y0, h.g_effective_domain_subset_f_effective_domain hy0⟩

/-- Each block penalty is proper by the source-facing owner field
`block_g_proper`. -/
instance instIsProperExtendedRealFunctionBlockPenalty
    {f : X → EReal} {g : (i : ι) → Ei i → EReal}
    {Li : (i : ι) → PosReal}
    (h : IsGeneralizedBlockConditionalGradientProblem f g Li) (i : ι) :
    IsProperExtendedRealFunction (g i) :=
  h.block_g_proper i

end

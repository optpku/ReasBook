/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_10
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_10
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Lemma_5_20
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_25
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_30
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_6
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Lemma_9_7
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Theorem_9_12.Linearized
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Theorem_9_12
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Theorem_9_24
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_3
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_67

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (f g ω : E → EReal)
variable [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
  [Fact (is_convex_function g)] [IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ)]

/- `prompt_add/` is absent in this workspace, so the nearby Chapter 9 and Chapter 10 files supply
the local API guidance.

Algorithm 10.69 is `source-facing` in the non-Euclidean proximal-gradient API.

Domain sampling against the existing project code identifies:
- `proximal_gradient_backtracking_trial_stepsize` and
  `ProximalGradientBacktrackingGrowthFactor` from Algorithm 10.2 as the canonical owner of the
  geometric trial family `LPrev η^i`;
- `non_euclidean_proximal_gradient_step` from Algorithm 10.67 as the canonical owner of the
  non-Euclidean one-step update predicate;
- `IsBregmanPotentialOn` from Definition 9.2 together with the Chapter 9 minimizer existence API
  as the canonical bridge guaranteeing that the one-step predicate has a witness.

The clean public interface therefore keeps the B5-specific content at the same level as B2, B3,
and B4: the B5 acceptance predicate phrased through an explicit accepted step witness, the local
class saying that an index is the first accepted geometric trial, and the sequence-level rule
recording `L_k = L_{k-1} η^{i_k}` at the current iterate `x^k`. The chapter already owns the
recursion `L_{-1} = s`, `L_prev(k + 1) = L_k` as
`proximal_gradient_backtracking_B2_previous_stepsize`, so this file should reuse that owner
directly instead of threading an extra trajectory witness merely to recover the point `x^k`.

Because Algorithm 10.67 no longer hides the Chapter 3 differentiability hypothesis inside a
totalized set-valued owner, the B5 acceptance data in this file must keep the accepted step
witness explicit on theorem surfaces, rather than reviving a hidden fallback derivative through a
totalized chosen operator. -/

/-- Helper for Algorithm 10.69: positive scaling by the reciprocal curvature leaves the effective
domain of `g` unchanged. -/
lemma scaled_backtracking_penalty_effective_domain_eq
    (g : E → EReal) [IsProperExtendedRealFunction g] (Lk : PosReal) :
    effective_domain ((((1 / Lk : PosReal) : EReal) • g)) = effective_domain g := by
  -- Compare domain membership pointwise through the Chapter 6 positive-scaling equivalence.
  ext x
  exact mem_effective_domain_scaled_function_iff g (1 / Lk : PosReal) inferInstance x

namespace ScaledBacktrackingPenalty

/-- Positive reciprocal scaling preserves properness of the backtracking penalty. -/
instance instIsProper
    (g : E → EReal) [IsProperExtendedRealFunction g] (Lk : PosReal) :
    IsProperExtendedRealFunction ((((1 / Lk : PosReal) : EReal) • g)) :=
  scaled_function_proper_of_pos g (1 / Lk : PosReal) inferInstance

end ScaledBacktrackingPenalty

/-- Helper for Algorithm 10.69: the standing Bregman-potential hypothesis transports to the
scaled penalty domain. -/
instance scaled_backtracking_penalty_isBregmanPotentialOn
    (g ω : E → EReal) [IsProperExtendedRealFunction g]
    [IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ)] (Lk : PosReal) :
    IsBregmanPotentialOn ω
      (effective_domain ((((1 / Lk : PosReal) : EReal) • g))) (1 : ℝ) := by
  let hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ) := inferInstance
  refine
    { toIsProperExtendedRealFunction := hω.toIsProperExtendedRealFunction
      closed := hω.closed
      convex := hω.convex
      differentiableOn_subdifferential_domain := hω.differentiableOn_subdifferential_domain
      subset_effective_domain := ?_
      sigma_pos := hω.sigma_pos
      strongConvexOn := ?_ }
  · rw [scaled_backtracking_penalty_effective_domain_eq g Lk]
    exact hω.subset_effective_domain
  · rw [scaled_backtracking_penalty_effective_domain_eq g Lk]
    exact hω.strongConvexOn

omit [FiniteDimensional ℝ E] in
/-- Helper for Algorithm 10.69: the Algorithm 10.67 step objective is exactly the Chapter 9
Mirror-C objective for the scaled penalty `(1 / Lk) g`. -/
lemma mirror_c_step_objective_eq_scaled_auxiliary_objective
    (f g ω : E → EReal) (xk : E) (Lk : PosReal) :
    mirror_c_update_objective g ω xk
      (fderiv ℝ (fun y ↦ (f y).toReal) xk) ((Lk : ℝ)⁻¹) =
      fun x ↦
        (((mirror_c_problem_functional ω xk
            (fderiv ℝ (fun y ↦ (f y).toReal) xk) ((1 / Lk : PosReal) : ℝ) x : ℝ) : EReal) +
          ((((1 / Lk : PosReal) : EReal) • g) x)) +
          ω x := by
  -- Expand both owner definitions once and normalize the reciprocal curvature spelling.
  funext x
  have hInv : ((Lk : ℝ)⁻¹) = ((1 / Lk : PosReal) : ℝ) := by
    simpa using (PosReal.coe_inv Lk).symm
  rw [mirror_c_update_objective_apply, Pi.smul_apply, smul_eq_mul, hInv]

/-- Helper for Algorithm 10.69: positive scaling by the reciprocal curvature preserves the proper,
closed, and convex hypotheses on `g`. -/
lemma scaled_backtracking_penalty_proper_closed_convex
    (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)] (Lk : PosReal) :
    IsProperExtendedRealFunction ((((1 / Lk : PosReal) : EReal) • g)) ∧
      LowerSemicontinuous ((((1 / Lk : PosReal) : EReal) • g)) ∧
      is_convex_function ((((1 / Lk : PosReal) : EReal) • g)) := by
  -- Package the Chapter 6 positive-scaling transport theorem at the reciprocal curvature.
  let hg_closed : LowerSemicontinuous g := Fact.out
  let hg_convex : is_convex_function g := Fact.out
  simpa using
    scaled_function_proper_closed_convex_of_pos g inferInstance hg_closed hg_convex (1 / Lk)

/-- Helper for Algorithm 10.69: adding a finite linear perturbation does not change the effective
domain of an extended-real penalty. -/
lemma auxiliaryAffinePerturbation_effective_domain_eq
    (ψ : E → EReal) [IsProperExtendedRealFunction ψ] (a : StrongDual ℝ E) :
    effective_domain (fun x ↦ ((a x : ℝ) : EReal) + ψ x) = effective_domain ψ := by
  -- Compare finiteness pointwise; the linear perturbation is finite everywhere.
  ext x
  constructor
  · intro hx
    rw [mem_effective_domain] at hx ⊢
    by_contra hψx
    have hψx_top : ψ x = ⊤ := by
      exact le_antisymm le_top (not_lt.mp hψx)
    have hsum_top : ((a x : ℝ) : EReal) + ψ x = ⊤ := by
      simpa [hψx_top] using EReal.add_top_of_ne_bot (EReal.coe_ne_bot (a x))
    exact (ne_of_lt hx) hsum_top
  · intro hx
    rw [mem_effective_domain] at hx ⊢
    exact EReal.add_lt_top (EReal.coe_ne_top (a x)) hx.ne

/-- Helper for Algorithm 10.69: finite linear perturbations preserve properness. -/
lemma auxiliaryAffinePerturbation_proper
    (ψ : E → EReal) [IsProperExtendedRealFunction ψ] (a : StrongDual ℝ E) :
    IsProperExtendedRealFunction (fun x ↦ ((a x : ℝ) : EReal) + ψ x) := by
  -- Properness is unchanged because the perturbation is finite everywhere.
  refine ⟨?_, ?_⟩
  · intro x
    rw [EReal.add_ne_bot_iff]
    exact ⟨EReal.coe_ne_bot (a x), (inferInstance : IsProperExtendedRealFunction ψ).ne_bot x⟩
  · rcases (inferInstance : IsProperExtendedRealFunction ψ).effective_domain_nonempty with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa [auxiliaryAffinePerturbation_effective_domain_eq ψ a] using hx

/-- Helper for Algorithm 10.69: finite linear perturbations preserve convexity. -/
lemma auxiliaryAffinePerturbation_convex
    (ψ : E → EReal) [IsProperExtendedRealFunction ψ] (a : StrongDual ℝ E)
    (hψ_convex : is_convex_function ψ) :
    is_convex_function (fun x ↦ ((a x : ℝ) : EReal) + ψ x) := by
  -- A continuous linear functional is affine, so its `EReal` lift adds a convex finite term.
  have hlinear_convex : ConvexOn ℝ Set.univ (fun x : E ↦ a x) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ α β hα hβ hαβ
    refine le_of_eq ?_
    simp [smul_eq_mul, map_add]
  have hlinear_convex_ereal :
      is_convex_function (fun x : E ↦ ((a x : ℝ) : EReal)) :=
    Function.toEReal_isConvexFunction hlinear_convex
  simpa [Pi.add_apply] using
    is_convex_function_pointwise_add hlinear_convex_ereal hψ_convex
      (fun x ↦ EReal.coe_ne_bot (a x)) ((inferInstance : IsProperExtendedRealFunction ψ).ne_bot)

/-- Helper for Algorithm 10.69: finite linear perturbations preserve lower semicontinuity. -/
lemma auxiliaryAffinePerturbation_closed
    (ψ : E → EReal) (a : StrongDual ℝ E) (hψ_closed : LowerSemicontinuous ψ) :
    LowerSemicontinuous (fun x ↦ ((a x : ℝ) : EReal) + ψ x) := by
  -- Addition is continuous because the linear perturbation is finite everywhere.
  have hlinear_closed :
      LowerSemicontinuous (fun x : E ↦ ((a x : ℝ) : EReal)) :=
    Function.toEReal_lowerSemicontinuous_of_continuous a.continuous
  have hsum_closed :
      LowerSemicontinuous ((fun x : E ↦ ((a x : ℝ) : EReal)) + ψ) := by
    refine hlinear_closed.add' hψ_closed ?_
    intro x
    exact EReal.continuousAt_add (.inl (EReal.coe_ne_top (a x))) (.inl (EReal.coe_ne_bot (a x)))
  simpa [Pi.add_apply] using hsum_closed

/-- Helper for Algorithm 10.69: the constrained-potential spelling agrees pointwise with the raw
composite objective `x ↦ ψ x + ω x`. -/
lemma backtrackingConstrainedPotentialAdd_eq_compositeObjective
    {ψ ω : E → EReal} {σ : ℝ}
    (hω : IsBregmanPotentialOn ω (effective_domain ψ) σ) :
    (fun x ↦ ω x + (δ_ (effective_domain ψ)) x + ψ x) = (fun x ↦ ψ x + ω x) := by
  -- Outside `effective_domain ψ`, the indicator and `ψ` are both `⊤`.
  -- On feasible points, the indicator vanishes.
  funext x
  by_cases hx : x ∈ effective_domain ψ
  · simp [extendedIndicator_of_mem hx, add_comm]
  · have hψ_top : ψ x = ⊤ := by
      exact le_antisymm le_top (not_lt.mp hx)
    have hright_top : ψ x + ω x = ⊤ := by
      rw [hψ_top]
      simpa using EReal.top_add_of_ne_bot (hω.ne_bot x)
    calc
      ω x + (δ_ (effective_domain ψ)) x + ψ x = ⊤ := by
        simpa [Pi.add_apply, extendedIndicator_of_not_mem hx, hψ_top, add_assoc] using
          EReal.add_top_of_ne_bot (hω.ne_bot x)
      _ = ψ x + ω x := hright_top.symm

/-- Helper for Algorithm 10.69: `x ↦ ψ x + ω x` is strongly convex once `ω` is a Bregman
potential on `effective_domain ψ` and `ψ` is convex. -/
lemma backtrackingCompositeObjectiveStronglyConvex
    {ψ ω : E → EReal} {σ : ℝ}
    (hω : IsBregmanPotentialOn ω (effective_domain ψ) σ)
    (hψ_proper : IsProperExtendedRealFunction ψ) (hψ_convex : is_convex_function ψ) :
    is_strongly_convex_function (fun x ↦ ψ x + ω x) σ := by
  -- Recast the constrained potential as a Chapter 5 strongly convex function, then add `ψ`.
  have hindicator_ne_bot : ∀ x, (δ_ (effective_domain ψ)) x ≠ ⊥ := by
    intro x
    by_cases hx : x ∈ effective_domain ψ
    · simp [extendedIndicator_of_mem hx]
    · simp [extendedIndicator_of_not_mem hx]
  have hconstrained :
      is_strongly_convex_function (fun x ↦ (ω + δ_ (effective_domain ψ)) x) σ := by
    refine (is_strongly_convex_function_iff_strongConvexOn_toReal).mpr ?_
    refine ⟨hω.sigma_pos, ?_, hω.strongConvexOn_add_indicator⟩
    intro x
    rw [Pi.add_apply, EReal.add_ne_bot_iff]
    exact ⟨hω.ne_bot x, hindicator_ne_bot x⟩
  have hsum :
      is_strongly_convex_function
        (fun x ↦ (ω + δ_ (effective_domain ψ)) x + ψ x) σ :=
    is_strongly_convex_function_add_of_is_convex_function
      hconstrained hψ_convex hψ_proper.ne_bot
  simpa [Pi.add_apply, backtrackingConstrainedPotentialAdd_eq_compositeObjective hω] using hsum

/-- Helper for Algorithm 10.69: `x ↦ ψ x + ω x` is proper once `ψ` is proper and `ω` is finite on
`effective_domain ψ`. -/
lemma backtrackingCompositeObjectiveProper
    {ψ ω : E → EReal} {σ : ℝ}
    (hω : IsBregmanPotentialOn ω (effective_domain ψ) σ)
    (hψ_proper : IsProperExtendedRealFunction ψ) :
    IsProperExtendedRealFunction (fun x ↦ ψ x + ω x) := by
  -- Properness comes from the nonempty feasible set and pointwise exclusion of `⊥`.
  refine ⟨?_, ?_⟩
  · intro x
    rw [EReal.add_ne_bot_iff]
    exact ⟨hψ_proper.ne_bot x, hω.ne_bot x⟩
  · rcases hψ_proper.effective_domain_nonempty with ⟨x, hxψ⟩
    have hxω : x ∈ effective_domain ω := hω.subset_effective_domain hxψ
    refine ⟨x, ?_⟩
    exact mem_effective_domain.mpr <|
      EReal.add_lt_top (ne_of_lt (mem_effective_domain.mp hxψ))
        (ne_of_lt (mem_effective_domain.mp hxω))

/-- Helper for Algorithm 10.69: `x ↦ ψ x + ω x` is lower semicontinuous when both summands are. -/
lemma backtrackingCompositeObjectiveClosed
    {ψ ω : E → EReal} {σ : ℝ}
    (hω : IsBregmanPotentialOn ω (effective_domain ψ) σ)
    (hψ_proper : IsProperExtendedRealFunction ψ) (hψ_closed : LowerSemicontinuous ψ) :
    LowerSemicontinuous (fun x ↦ ψ x + ω x) := by
  -- Addition stays lower semicontinuous because neither summand takes the value `⊥`.
  refine hψ_closed.add' hω.closed ?_
  intro x
  exact EReal.continuousAt_add (.inr (hω.ne_bot x)) (.inl (hψ_proper.ne_bot x))

/-- Helper for Algorithm 10.69: every global minimizer of `x ↦ ψ x + ω x` lies in
`effective_domain ψ`. -/
lemma backtrackingCompositeMinimizer_mem_effectiveDomain
    {ψ ω : E → EReal} {σ : ℝ}
    (hω : IsBregmanPotentialOn ω (effective_domain ψ) σ)
    (hψ_proper : IsProperExtendedRealFunction ψ)
    {xStar : E} (hxStar : IsMinOn (fun x ↦ ψ x + ω x) Set.univ xStar) :
    xStar ∈ effective_domain ψ := by
  -- Compare the minimizer with one known feasible point coming from properness of `ψ`.
  rcases hψ_proper.effective_domain_nonempty with ⟨x0, hx0ψ⟩
  have hx0ω : x0 ∈ effective_domain ω := hω.subset_effective_domain hx0ψ
  have hmin : ψ xStar + ω xStar ≤ ψ x0 + ω x0 := by
    simpa using (isMinOn_iff.mp hxStar) x0 (by simp)
  have hsum_rhs : ψ x0 + ω x0 < ⊤ := by
    exact EReal.add_lt_top (ne_of_lt (mem_effective_domain.mp hx0ψ))
      (ne_of_lt (mem_effective_domain.mp hx0ω))
  have hsum_finite : ψ xStar + ω xStar < ⊤ := lt_of_le_of_lt hmin hsum_rhs
  by_contra hxStar_dom
  have hψ_top : ψ xStar = ⊤ := by
    exact le_antisymm le_top (not_lt.mp hxStar_dom)
  have hsum_top : ψ xStar + ω xStar = ⊤ := by
    rw [hψ_top]
    simpa using EReal.top_add_of_ne_bot (hω.ne_bot xStar)
  exact (ne_of_lt hsum_finite) hsum_top

/-- Helper for Algorithm 10.69: the composite objective `x ↦ ψ x + ω x` has a unique global
minimizer, and that minimizer lies in `effective_domain ψ`. -/
lemma existsUnique_backtrackingCompositeMinimizer_mem_effectiveDomain
    {ψ ω : E → EReal} {σ : ℝ}
    (hω : IsBregmanPotentialOn ω (effective_domain ψ) σ)
    (hψ_proper : IsProperExtendedRealFunction ψ) (hψ_closed : LowerSemicontinuous ψ)
    (hψ_convex : is_convex_function ψ) :
    ∃! xStar : E,
      IsMinOn (fun x ↦ ψ x + ω x) Set.univ xStar ∧ xStar ∈ effective_domain ψ := by
  -- Use strong convexity for uniqueness and then record the effective-domain membership separately.
  let hstrong :=
    backtrackingCompositeObjectiveStronglyConvex hω hψ_proper hψ_convex
  let hproper :=
    backtrackingCompositeObjectiveProper hω hψ_proper
  let hclosed :=
    backtrackingCompositeObjectiveClosed hω hψ_proper hψ_closed
  rcases existsUnique_isMinOn_univ_of_closed_strongly_convex
      hstrong hproper.effective_domain_nonempty hclosed with
    ⟨xStar, hxStar, huniq⟩
  refine ⟨xStar, ?_, ?_⟩
  · exact ⟨hxStar, backtrackingCompositeMinimizer_mem_effectiveDomain hω hψ_proper hxStar⟩
  · intro y hy
    exact huniq y hy.1

/-- Helper for Algorithm 10.69: the scaled Chapter 10 auxiliary objective has a unique global
minimizer, and that minimizer lies in `dom(g)`. -/
lemma existsUnique_scaledBacktrackingAuxiliaryMinimizer_mem_effectiveDomain
    (xk : E) (Lk : PosReal)
    (hxk : xk ∈ effective_domain g ∩ subdifferential_domain ω) :
    ∃! xNext : E,
      IsMinOn (scaled_bregman_objective f g ω xk Lk) Set.univ xNext ∧
        xNext ∈ effective_domain g := by
  -- Build the scaled linearized penalty first, then solve the Chapter 9 composite problem.
  let s : StrongDual ℝ E := ((Lk : ℝ)⁻¹) • fderiv ℝ (fun y ↦ (f y).toReal) xk
  let ψ : E → EReal := fun x ↦ ((s x : ℝ) : EReal) + ((((1 / Lk : PosReal) : EReal) • g) x)
  have hscaled_struct :
      IsProperExtendedRealFunction ((((1 / Lk : PosReal) : EReal) • g)) ∧
        LowerSemicontinuous ((((1 / Lk : PosReal) : EReal) • g)) ∧
        is_convex_function ((((1 / Lk : PosReal) : EReal) • g)) :=
    scaled_backtracking_penalty_proper_closed_convex g Lk
  have hψ_dom_scaled :
      effective_domain ψ = effective_domain ((((1 / Lk : PosReal) : EReal) • g)) := by
    -- The scaled derivative term is finite everywhere, so it leaves the domain unchanged.
    simpa [ψ] using auxiliaryAffinePerturbation_effective_domain_eq
      ((((1 / Lk : PosReal) : EReal) • g)) s
  have hψ_dom : effective_domain ψ = effective_domain g := by
    rw [hψ_dom_scaled, scaled_backtracking_penalty_effective_domain_eq g Lk]
  have hψ_proper : IsProperExtendedRealFunction ψ := by
    -- Properness survives the finite linear perturbation.
    simpa [ψ] using auxiliaryAffinePerturbation_proper
      ((((1 / Lk : PosReal) : EReal) • g)) s
  have hψ_closed : LowerSemicontinuous ψ := by
    -- Lower semicontinuity survives the same perturbation.
    simpa [ψ] using auxiliaryAffinePerturbation_closed
      ((((1 / Lk : PosReal) : EReal) • g)) s hscaled_struct.2.1
  have hψ_convex : is_convex_function ψ := by
    -- Convexity also survives finite linear perturbations.
    simpa [ψ] using auxiliaryAffinePerturbation_convex
      ((((1 / Lk : PosReal) : EReal) • g)) s hscaled_struct.2.2
  have hωψ : IsBregmanPotentialOn ω (effective_domain ψ) (1 : ℝ) := by
    -- The Bregman-potential owner only depends on the unchanged effective domain.
    simpa [hψ_dom] using
      (inferInstance : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
  let aω : StrongDual ℝ E := InnerProductSpace.toDual ℝ E (-∇ (fun z ↦ (ω z).toReal) xk)
  have haω_apply : ∀ x : E, (aω x : ℝ) = -inner ℝ (∇ (fun z ↦ (ω z).toReal) xk) x := by
    intro x
    simpa [aω, InnerProductSpace.toDual_apply_apply]
  have hψb_proper :
      IsProperExtendedRealFunction (affinePerturbedPenalty ψ ω xk) := by
    -- This is exactly the normalized affine perturbation from Theorem 9.12.
    exact AffinePerturbedPenalty.proper ψ ω xk hψ_proper
  have hψb_closed :
      LowerSemicontinuous (affinePerturbedPenalty ψ ω xk) := by
    -- Repackage the normalized perturbation as an ordinary finite linear perturbation.
    have hclosed :=
      auxiliaryAffinePerturbation_closed ψ aω hψ_closed
    have hclosed' : LowerSemicontinuous (fun x ↦ ψ x + ((aω x : ℝ) : EReal)) := by
      simpa [Pi.add_apply, add_comm] using hclosed
    simpa [affinePerturbedPenalty, haω_apply, Pi.add_apply] using hclosed'
  have hψb_convex :
      is_convex_function (affinePerturbedPenalty ψ ω xk) := by
    -- The same finite-perturbation route gives convexity.
    have hconvex :=
      auxiliaryAffinePerturbation_convex ψ aω hψ_convex
    have hconvex' : is_convex_function (fun x ↦ ψ x + ((aω x : ℝ) : EReal)) := by
      simpa [Pi.add_apply, add_comm] using hconvex
    simpa [affinePerturbedPenalty, haω_apply, Pi.add_apply] using hconvex'
  have hψb_dom : effective_domain (affinePerturbedPenalty ψ ω xk) = effective_domain ψ := by
    exact AffinePerturbedPenalty.effectiveDomain ψ ω xk
  have hωψb :
      IsBregmanPotentialOn ω (effective_domain (affinePerturbedPenalty ψ ω xk)) (1 : ℝ) := by
    -- The normalized perturbation again leaves the feasible set unchanged.
    simpa [hψb_dom] using hωψ
  rcases existsUnique_backtrackingCompositeMinimizer_mem_effectiveDomain
      hωψb hψb_proper hψb_closed hψb_convex with
    ⟨xStar, hxStar, huniqStar⟩
  have hxStar_lin :
      IsMinOn (linearizedSecondProxObjective ψ ω xk) Set.univ xStar := by
    -- Rewrite the composite objective back to the Chapter 9 linearized owner.
    simpa [LinearizedSecondProxObjective.eq_affinePerturbed_add ψ ω xk hωψ]
      using hxStar.1
  have hxStar_eff_g : xStar ∈ effective_domain g := by
    -- The minimizer lies in the unchanged effective domain of the scaled penalty.
    simpa [hψb_dom, hψ_dom] using hxStar.2
  have hxStar_scaled :
      IsMinOn (scaled_bregman_objective f g ω xk Lk) Set.univ xStar := by
    -- The second-prox objective differs from the linearized one only by a constant shift.
    have hscaled_eq :
        ∀ x,
          scaled_bregman_objective f g ω xk Lk x =
            (((1 : ℝ) : EReal) * linearizedSecondProxObjective ψ ω xk x) +
              (((inner ℝ (∇ (fun z ↦ (ω z).toReal) xk) xk - (ω xk).toReal : ℝ)) : EReal) := by
      intro x
      simpa [ψ, scaled_bregman_objective, Pi.smul_apply, smul_eq_mul, add_assoc, add_left_comm,
        add_comm, one_mul] using SecondProxObjective.eq_linearized_add_const ψ ω xk x
    have hiff :
        IsMinOn (scaled_bregman_objective f g ω xk Lk) Set.univ xStar ↔
          IsMinOn (linearizedSecondProxObjective ψ ω xk) Set.univ xStar :=
      isMinOn_iff_of_pos_mul_add_constant (by norm_num) hscaled_eq
    exact hiff.mpr hxStar_lin
  refine ⟨xStar, ?_, ?_⟩
  · exact ⟨hxStar_scaled, hxStar_eff_g⟩
  · intro y hy
    have hy_lin :
        IsMinOn (linearizedSecondProxObjective ψ ω xk) Set.univ y := by
      -- Transport the competing scaled minimizer through the same constant-shift equivalence.
      have hscaled_eq :
          ∀ x,
            scaled_bregman_objective f g ω xk Lk x =
              (((1 : ℝ) : EReal) * linearizedSecondProxObjective ψ ω xk x) +
                (((inner ℝ (∇ (fun z ↦ (ω z).toReal) xk) xk - (ω xk).toReal : ℝ)) : EReal) := by
        intro x
        simpa [ψ, scaled_bregman_objective, Pi.smul_apply, smul_eq_mul, add_assoc, add_left_comm,
          add_comm, one_mul] using SecondProxObjective.eq_linearized_add_const ψ ω xk x
      have hiff :
          IsMinOn (scaled_bregman_objective f g ω xk Lk) Set.univ y ↔
            IsMinOn (linearizedSecondProxObjective ψ ω xk) Set.univ y :=
        isMinOn_iff_of_pos_mul_add_constant (by norm_num) hscaled_eq
      exact hiff.mp hy.1
    have hy_comp :
        IsMinOn (fun x ↦ affinePerturbedPenalty ψ ω xk x + ω x) Set.univ y := by
      -- Rewrite the competing minimizer back to the same composite owner.
      simpa [LinearizedSecondProxObjective.eq_affinePerturbed_add ψ ω xk hωψ]
        using hy_lin
    exact huniqStar y ⟨hy_comp, by simpa [hψb_dom, hψ_dom] using hy.2⟩

/-- Qualified domain companion for Algorithm 10.69: a minimizer of the scaled auxiliary objective
lies in `dom(∂ ω)` when the intrinsic interiors of `dom(g)` and `dom(ω)` meet. -/
lemma scaledBacktrackingAuxiliaryMinimizer_mem_subdifferentialDomain
    (xk : E) (Lk : PosReal)
    (hxk : xk ∈ effective_domain g ∩ subdifferential_domain ω)
    (hqual : (intrinsicInterior ℝ (effective_domain g) ∩
      intrinsicInterior ℝ (effective_domain ω)).Nonempty)
    {xNext : E} (hmin : IsMinOn (scaled_bregman_objective f g ω xk Lk) Set.univ xNext) :
    xNext ∈ subdifferential_domain ω := by
  let s : StrongDual ℝ E := ((Lk : ℝ)⁻¹) • fderiv ℝ (fun y ↦ (f y).toReal) xk
  let ψ : E → EReal := fun x ↦ ((s x : ℝ) : EReal) + ((((1 / Lk : PosReal) : EReal) • g) x)
  have hscaled_struct :
      IsProperExtendedRealFunction ((((1 / Lk : PosReal) : EReal) • g)) ∧
        LowerSemicontinuous ((((1 / Lk : PosReal) : EReal) • g)) ∧
        is_convex_function ((((1 / Lk : PosReal) : EReal) • g)) :=
    scaled_backtracking_penalty_proper_closed_convex g Lk
  have hψ_dom_scaled :
      effective_domain ψ = effective_domain ((((1 / Lk : PosReal) : EReal) • g)) := by
    simpa [ψ] using auxiliaryAffinePerturbation_effective_domain_eq
      ((((1 / Lk : PosReal) : EReal) • g)) s
  have hψ_dom : effective_domain ψ = effective_domain g := by
    rw [hψ_dom_scaled, scaled_backtracking_penalty_effective_domain_eq g Lk]
  have hψ_proper : IsProperExtendedRealFunction ψ := by
    simpa [ψ] using auxiliaryAffinePerturbation_proper
      ((((1 / Lk : PosReal) : EReal) • g)) s
  have hψ_convex : is_convex_function ψ := by
    simpa [ψ] using auxiliaryAffinePerturbation_convex
      ((((1 / Lk : PosReal) : EReal) • g)) s hscaled_struct.2.2
  have hωψ : IsBregmanPotentialOn ω (effective_domain ψ) (1 : ℝ) := by
    simpa [hψ_dom] using
      (inferInstance : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
  have hqualψ :
      (intrinsicInterior ℝ (effective_domain ψ) ∩
        intrinsicInterior ℝ (effective_domain ω)).Nonempty := by
    simpa [hψ_dom] using hqual
  have hscaled_secondProx :
      secondProxObjective ψ ω xk = scaled_bregman_objective f g ω xk Lk := by
    funext x
    have hInv : ((((Lk : ℝ)⁻¹ : ℝ) : EReal)) = (((1 / Lk : PosReal) : EReal)) := by
      simpa using congrArg (fun t : ℝ ↦ (t : EReal)) (PosReal.coe_inv Lk)
    have hEInv : ((Lk : EReal)⁻¹) = ((((Lk : ℝ)⁻¹ : ℝ) : EReal)) := by
      simpa using (EReal.coe_inv (Lk : ℝ)).symm
    simp [SecondProxObjective.apply, s, ψ, scaled_bregman_objective, Pi.smul_apply,
      smul_eq_mul, EReal.coe_mul, hInv, add_assoc, add_comm]
    rw [← hInv, hEInv]
  have hxNext_secondProx :
      IsMinOn (secondProxObjective ψ ω xk) Set.univ xNext := by
    rw [hscaled_secondProx]
    exact hmin
  exact
    SecondProxObjective.minimizer_mem_subdifferential_domain
      hωψ hψ_proper hψ_convex hxNext_secondProx hqualψ

/-- Qualified companion for Algorithm 10.69: the scaled auxiliary objective has a unique global
minimizer in `dom(g) ∩ dom(∂ ω)` under the intrinsic-interior qualification. -/
lemma existsUnique_scaledBacktrackingAuxiliaryMinimizer
    (xk : E) (Lk : PosReal)
    (hxk : xk ∈ effective_domain g ∩ subdifferential_domain ω)
    (hqual : (intrinsicInterior ℝ (effective_domain g) ∩
      intrinsicInterior ℝ (effective_domain ω)).Nonempty) :
    ∃! xNext : E,
      IsMinOn (scaled_bregman_objective f g ω xk Lk) Set.univ xNext ∧
        xNext ∈ effective_domain g ∩ subdifferential_domain ω := by
  rcases existsUnique_scaledBacktrackingAuxiliaryMinimizer_mem_effectiveDomain
      f g ω xk Lk hxk with ⟨xStar, hxStar, huniqStar⟩
  have hxStar_sub : xStar ∈ subdifferential_domain ω :=
    scaledBacktrackingAuxiliaryMinimizer_mem_subdifferentialDomain
      f g ω xk Lk hxk hqual hxStar.1
  refine ⟨xStar, ⟨hxStar.1, hxStar.2, hxStar_sub⟩, ?_⟩
  intro y hy
  exact huniqStar y ⟨hy.1, hy.2.1⟩

/-- The canonical non-Euclidean proximal-gradient step predicate from Algorithm 10.67 has a unique
realizer in `dom(g)`. -/
theorem existsUnique_non_euclidean_proximal_gradient_step_mem_effectiveDomain
    (xk : E) (Lk : PosReal)
    (hxk : xk ∈ effective_domain g ∩ subdifferential_domain ω)
    (hfxk : is_differentiable_at f xk) :
    ∃! xNext : E,
      non_euclidean_proximal_gradient_step f g ω xk Lk xNext ∧
        xNext ∈ effective_domain g := by
  rcases existsUnique_scaledBacktrackingAuxiliaryMinimizer_mem_effectiveDomain
      f g ω xk Lk hxk with ⟨xStar, hxStar, huniqStar⟩
  refine ⟨xStar, ?_, ?_⟩
  · refine ⟨?_, hxStar.2⟩
    have hstep :
        non_euclidean_proximal_gradient_step f g ω xk Lk xStar ↔
          xStar ∈ effective_domain g ∧
            IsMinOn (scaled_bregman_objective f g ω xk Lk) Set.univ xStar :=
      non_euclidean_proximal_gradient_step_iff_mem_effective_domain_and_isMinOn_scaled_objective_univ
        inferInstance hfxk hxk
    exact hstep.mpr hxStar.symm
  · intro y hy
    apply huniqStar
    refine ⟨?_, hy.2⟩
    have hstep :
        non_euclidean_proximal_gradient_step f g ω xk Lk y ↔
          y ∈ effective_domain g ∧
            IsMinOn (scaled_bregman_objective f g ω xk Lk) Set.univ y :=
      non_euclidean_proximal_gradient_step_iff_mem_effective_domain_and_isMinOn_scaled_objective_univ
        inferInstance hfxk hxk
    exact (hstep.mp hy.1).2

/-- Qualified companion for Algorithm 10.69: the unique non-Euclidean proximal-gradient step
lies in `dom(g) ∩ dom(∂ ω)` when the intrinsic interiors of `dom(g)` and `dom(ω)` meet. -/
theorem existsUnique_non_euclidean_proximal_gradient_step_mem_domains
    (xk : E) (Lk : PosReal)
    (hxk : xk ∈ effective_domain g ∩ subdifferential_domain ω)
    (hqual : (intrinsicInterior ℝ (effective_domain g) ∩
      intrinsicInterior ℝ (effective_domain ω)).Nonempty)
    (hfxk : is_differentiable_at f xk) :
    ∃! xNext : E,
      non_euclidean_proximal_gradient_step f g ω xk Lk xNext ∧
        xNext ∈ effective_domain g ∩ subdifferential_domain ω := by
  rcases existsUnique_scaledBacktrackingAuxiliaryMinimizer
      f g ω xk Lk hxk hqual with ⟨xStar, hxStar, huniqStar⟩
  refine ⟨xStar, ?_, ?_⟩
  · refine ⟨?_, hxStar.2⟩
    have hstep :
        non_euclidean_proximal_gradient_step f g ω xk Lk xStar ↔
          xStar ∈ effective_domain g ∧
            IsMinOn (scaled_bregman_objective f g ω xk Lk) Set.univ xStar :=
      non_euclidean_proximal_gradient_step_iff_mem_effective_domain_and_isMinOn_scaled_objective_univ
        inferInstance hfxk hxk
    exact hstep.mpr ⟨hxStar.2.1, hxStar.1⟩
  · intro y hy
    apply huniqStar
    refine ⟨?_, hy.2⟩
    have hstep :
        non_euclidean_proximal_gradient_step f g ω xk Lk y ↔
          y ∈ effective_domain g ∧
            IsMinOn (scaled_bregman_objective f g ω xk Lk) Set.univ y :=
      non_euclidean_proximal_gradient_step_iff_mem_effective_domain_and_isMinOn_scaled_objective_univ
        inferInstance hfxk hxk
    exact (hstep.mp hy.1).2

/-- The B5 acceptance test accepts a trial curvature `L` at the current iterate `xk` exactly when
there exists an admissible next iterate `x⁺` for Algorithm 10.67 at `(xk, L)` whose value
satisfies the quadratic upper-model inequality from the textbook. -/
def non_euclidean_proximal_gradient_backtracking_B5_accepts
    (f g ω : E → EReal) (L : PosReal) (xk : E) : Prop :=
  ∃ xNext : E,
    non_euclidean_proximal_gradient_step f g ω xk L xNext ∧
      f xNext ≤
        f xk +
          ((inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (xNext - xk) +
            ((L : ℝ) / 2) * ‖xNext - xk‖ ^ (2 : ℕ) : ℝ) : EReal)

/-- The B5 acceptance predicate is exactly the displayed inequality
for some admissible Algorithm 10.67 step `x⁺` at `(xk, L)`. -/
@[simp] theorem non_euclidean_proximal_gradient_backtracking_B5_accepts_iff
    (f g ω : E → EReal) (L : PosReal) (xk : E) :
    non_euclidean_proximal_gradient_backtracking_B5_accepts f g ω L xk ↔
      ∃ xNext : E,
        non_euclidean_proximal_gradient_step f g ω xk L xNext ∧
        f xNext ≤
          f xk +
            ((inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (xNext - xk) +
              ((L : ℝ) / 2) * ‖xNext - xk‖ ^ (2 : ℕ) : ℝ) : EReal) :=
  Iff.rfl

/-- A trial index `i` is valid for B5 at `xk` when the geometric trial `LPrev η^i` is the first
trial curvature satisfying the B5 acceptance inequality. -/
class IsBacktrackingProcedureB5Index
    (f g ω : E → EReal) (LPrev : PosReal)
    (η : ProximalGradientBacktrackingGrowthFactor) (xk : E) (i : ℕ) : Prop where
  accepts :
    non_euclidean_proximal_gradient_backtracking_B5_accepts
      f g ω (proximal_gradient_backtracking_trial_stepsize LPrev η i) xk
  minimal (j : ℕ) (hj : j < i) :
    ¬ non_euclidean_proximal_gradient_backtracking_B5_accepts
        f g ω (proximal_gradient_backtracking_trial_stepsize LPrev η j) xk

namespace IsBacktrackingProcedureB5Index

/-- A valid B5 backtracking index records that `f` is differentiable at the current iterate
`xk`. -/
theorem differentiableAt
    (f g ω : E → EReal) {LPrev : PosReal} {η : ProximalGradientBacktrackingGrowthFactor}
    {xk : E} {i : ℕ} (hi : IsBacktrackingProcedureB5Index f g ω LPrev η xk i) :
    is_differentiable_at f xk := by
  rcases hi.accepts with ⟨xNext, hstep, _⟩
  exact hstep.differentiable_at

/-- A valid B5 backtracking index is minimal among the accepted geometric trials based on
`LPrev`. -/
theorem not_accepts_of_lt
    (f g ω : E → EReal)
    {LPrev : PosReal} {η : ProximalGradientBacktrackingGrowthFactor} {xk : E} {i j : ℕ}
    (hi : IsBacktrackingProcedureB5Index f g ω LPrev η xk i)
    (hj : j < i) :
    ¬ non_euclidean_proximal_gradient_backtracking_B5_accepts
        f g ω (proximal_gradient_backtracking_trial_stepsize LPrev η j) xk :=
  hi.minimal j hj

end IsBacktrackingProcedureB5Index

/-- Algorithm 10.69: a non-Euclidean proximal-gradient run uses backtracking procedure B5 with
parameters `(s, η)` when `L_{-1} = s` and, at every iteration `k`, the accepted curvature
estimate `L_k` is the first geometric trial `L_{k-1} η^{i_k}` for which some admissible
Algorithm 10.67 step `x⁺` from `x^k` satisfies the quadratic upper-model inequality
`f(x⁺) ≤ f(x^k) + ⟪∇ f(x^k), x⁺ - x^k⟫ + (L / 2) ‖x⁺ - x^k‖²`. -/
class UsesNonEuclideanProximalGradientBacktrackingB5Rule
    (f g ω : E → EReal) (x : ℕ → E) (L : ℕ → PosReal)
    (s : PosReal) (η : ProximalGradientBacktrackingGrowthFactor) : Prop where
  existsIndex (k : ℕ) :
    ∃ i : ℕ,
      IsBacktrackingProcedureB5Index
        f g ω (proximal_gradient_backtracking_B2_previous_stepsize s L k) η
        (x k) i ∧
      L k =
        proximal_gradient_backtracking_trial_stepsize
          (proximal_gradient_backtracking_B2_previous_stepsize s L k) η i

namespace UsesNonEuclideanProximalGradientBacktrackingB5Rule

/-- Under B5, the current iterate `x^k` is a differentiability point of `f`. -/
theorem differentiableAt
    (f g ω : E → EReal) {x : ℕ → E} {L : ℕ → PosReal}
    {s : PosReal} {η : ProximalGradientBacktrackingGrowthFactor}
    (hrule : UsesNonEuclideanProximalGradientBacktrackingB5Rule
      f g ω x L s η)
    (k : ℕ) :
    is_differentiable_at f (x k) := by
  rcases hrule.existsIndex k with ⟨i, hi, _⟩
  exact hi.differentiableAt f g ω

/-- Under B5, the chosen curvature estimate `L_k` satisfies the B5 acceptance inequality at
iteration `k`. -/
theorem accepts
    (f g ω : E → EReal) {x : ℕ → E} {L : ℕ → PosReal}
    {s : PosReal} {η : ProximalGradientBacktrackingGrowthFactor}
    (hrule : UsesNonEuclideanProximalGradientBacktrackingB5Rule
      f g ω x L s η)
    (k : ℕ) :
    non_euclidean_proximal_gradient_backtracking_B5_accepts f g ω (L k) (x k) := by
  rcases hrule.existsIndex k with ⟨i, hi, hLk⟩
  simpa [hLk] using hi.accepts

end UsesNonEuclideanProximalGradientBacktrackingB5Rule

end

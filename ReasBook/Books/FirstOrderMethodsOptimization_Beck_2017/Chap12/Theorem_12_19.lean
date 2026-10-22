/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_6
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_33
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_21
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_3
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_4
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_1
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_1_1
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_4
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_15
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_17
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Theorem_12_4
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_25
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Proposition_5_17
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_26
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_2
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_15
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Lemma_2_4
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_16
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Lemma_5_20
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_8
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_2
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Theorem_12_8
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Theorem_12_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped BigOperators
open scoped Gradient

section

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 12.19 is `source-facing`: it is the `p = 2` accelerated primal-distance estimate for
ADBPG.

Domain sampling against the surrounding Chapter 12 owners shows the three-layer split:
- `IsDualBlockProximalGradientProblem` together with
  `dual_block_proximal_gradient_dual_objective` and `Λ*(f, ![g₁, g₂])` is the source-facing
  two-block problem layer;
- `composite_model_objective f g₁` is the canonical owner of the reduced primal term, replacing
  the raw pointwise sum `x ↦ f x + g₁ x`;
- `IsFastDualProximalGradientPrimalTrajectory` from Algorithm 12.4 is the bridge/view layer
  expressing Algorithm 12.16's ADBPG iteration as accelerated dual proximal gradient on the
  reduced problem with primal term `composite_model_objective f g₁`; and
- `dual_based_proximal_gradient_lagrange_dual_objective_primal` together with
  `dual_based_proximal_gradient_lagrange_dual_problem_value` is the `core/canonical` reduced dual
  owner used only to invoke Theorem 12.10 internally.

Primitive data for the public theorem are the reduced accelerated trajectory, a two-block optimal
dual point `y* ∈ Λ*(f, ![g₁, g₂])`, and the pointwise primal argmax selections at the current
dual iterates and at the second optimal block `y₂*`. The reduced dual optimum condition is
derived API and should stay behind a bridge theorem rather than on the theorem surface. -/

section

variable (σ : PosReal) (f g1 g2 : E → EReal)

local notation "F" => composite_model_objective f g1
local notation "A" => (LinearMap.id : E →ₗ[ℝ] E)
local notation "L" =>
  (dual_based_proximal_gradient_identity_stepsize_parameter (E := E) σ :
    DualBasedProximalGradientDualStepsizeParameter (ContinuousLinearMap.id ℝ E) σ)
local notation "pRed" => composite_model_objective F g2
local notation "qRed" => dual_based_proximal_gradient_lagrange_dual_objective_primal F g2 A
local notation "qRedOpt" => dual_based_proximal_gradient_lagrange_dual_problem_value F g2 A
local notation "FRedDual" =>
  fun z : E ↦ dual_based_proximal_gradient_dual_F_term F A (InnerProductSpace.toDualMap ℝ E z)
local notation "GRedDual" =>
  fun z : E ↦ dual_based_proximal_gradient_dual_G_term g2 (InnerProductSpace.toDualMap ℝ E z)
local notation "gradFRed" => fun z : E ↦ ∇ (fun z' : E ↦ EReal.toReal (FRedDual z')) z

namespace IsDualBlockProximalGradientProblem

/-- Helper for Theorem 12.19: intrinsic-interior membership is stable under binary
intersections. -/
private lemma mem_intrinsicInterior_inter
    {S T : Set E} {x : E}
    (hxS : x ∈ intrinsicInterior ℝ S)
    (hxT : x ∈ intrinsicInterior ℝ T) :
    x ∈ intrinsicInterior ℝ (S ∩ T) := by
  rcases (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).1 hxS with
    ⟨_, εS, hεS, hS⟩
  rcases (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).1 hxT with
    ⟨_, εT, hεT, hT⟩
  -- Use the smaller of the two radii so both intrinsic-interior witnesses apply at once.
  refine (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).2 ?_
  refine ⟨subset_affineSpan ℝ (S ∩ T) ⟨intrinsicInterior_subset hxS, intrinsicInterior_subset hxT⟩,
    min εS εT, lt_min hεS hεT, ?_⟩
  intro y hy
  have hySaff : y ∈ affineSpan ℝ S := by
    exact affineSpan_mono ℝ (fun _ hz ↦ hz.1) hy.2
  have hyTaff : y ∈ affineSpan ℝ T := by
    exact affineSpan_mono ℝ (fun _ hz ↦ hz.2) hy.2
  refine ⟨?_, ?_⟩
  · exact hS ⟨Metric.closedBall_subset_closedBall (min_le_left _ _) hy.1, hySaff⟩
  · exact hT ⟨Metric.closedBall_subset_closedBall (min_le_right _ _) hy.1, hyTaff⟩

/-- Helper for Theorem 12.19: the reduced primal term `F = f + g₁` is finite exactly where both
`f` and `g₁` are finite. -/
private lemma reducedEffectiveDomain_eq
    (h_problem : IsDualBlockProximalGradientProblem f ![g1, g2] σ) :
    effective_domain F = effective_domain f ∩ effective_domain g1 := by
  ext x
  constructor
  · intro hx
    constructor
    · refine mem_effective_domain.mpr ?_
      by_contra hfx
      have hfx_top : f x = ⊤ := le_antisymm le_top (not_lt.mp hfx)
      have hsum_top : F x = ⊤ := by
        simpa [composite_model_objective_apply, hfx_top] using
          EReal.top_add_of_ne_bot ((h_problem.g_proper 0).ne_bot x)
      exact (ne_of_lt (mem_effective_domain.mp hx)) hsum_top
    · refine mem_effective_domain.mpr ?_
      by_contra hgx
      have hgx_top : g1 x = ⊤ := le_antisymm le_top (not_lt.mp hgx)
      have hsum_top : F x = ⊤ := by
        simpa [composite_model_objective_apply, hgx_top] using
          EReal.add_top_of_ne_bot (h_problem.ne_bot x)
      exact (ne_of_lt (mem_effective_domain.mp hx)) hsum_top
  · rintro ⟨hx_f, hx_g1⟩
    refine mem_effective_domain.mpr ?_
    simpa [composite_model_objective_apply] using
      EReal.add_lt_top (ne_of_lt (mem_effective_domain.mp hx_f))
        (ne_of_lt (mem_effective_domain.mp hx_g1))

/-- Helper for Theorem 12.19: the qualification witness for `f` and `g₁` already lies in
`ri (dom F)`. -/
private lemma mem_intrinsicInterior_reducedEffectiveDomain
    (h_problem : IsDualBlockProximalGradientProblem f ![g1, g2] σ)
    {x : E}
    (hx_f : x ∈ intrinsicInterior ℝ (effective_domain f))
    (hx_g1 : x ∈ intrinsicInterior ℝ (effective_domain g1)) :
    x ∈ intrinsicInterior ℝ (effective_domain F) := by
  -- First combine the two intrinsic-interior witnesses, then rewrite the reduced effective domain.
  rw [reducedEffectiveDomain_eq (σ := σ) (f := f) (g1 := g1) (g2 := g2) h_problem]
  exact mem_intrinsicInterior_inter hx_f hx_g1

/-- Helper for Theorem 12.19: adding the convex perturbation `g₁` preserves the `σ`-strong
convexity of `f`. -/
private lemma reducedStronglyConvex
    (h_problem : IsDualBlockProximalGradientProblem f ![g1, g2] σ) :
    StrongConvexOn (effective_domain F) (σ : ℝ) (fun x ↦ (F x).toReal) := by
  have hf_strong : is_strongly_convex_function f (σ : ℝ) := by
    -- Repackage the standing strong-convexity owner into the Chapter 5 source-facing predicate.
    refine (is_strongly_convex_function_iff_strongConvexOn_toReal).2 ?_
    exact ⟨σ.2, h_problem.ne_bot, h_problem.f_strongly_convex⟩
  have hg1_convex : is_convex_function g1 := by
    simpa using h_problem.g_convex 0
  have hF_strong : is_strongly_convex_function F (σ : ℝ) := by
    -- The reduced sum inherits the same modulus because `g₁` is convex.
    simpa [composite_model_objective_apply] using
      is_strongly_convex_function_add_of_is_convex_function
        hf_strong
        hg1_convex
        (fun x ↦ (h_problem.g_proper 0).ne_bot x)
  exact strongConvexOn_toReal_of_is_strongly_convex_function hF_strong

/-- Under Assumption 12.14 with two blocks, the reduced problem with primal term `f + g₁`,
nonsmooth term `g₂`, and identity map satisfies the Chapter 12.1 owner assumptions. -/
theorem toReducedProblem
    (h_problem : IsDualBlockProximalGradientProblem f ![g1, g2] σ) :
    IsDualBasedProximalGradientProblem F g2 A σ := by
  -- Populate the reduced Chapter 12.1 owner directly from the two-block assumptions.
  refine
    { toIsProperExtendedRealFunction := ?_
      f_closed := ?_
      f_strongly_convex := reducedStronglyConvex (σ := σ) (f := f) (g1 := g1) (g2 := g2) h_problem
      g_proper := h_problem.g_proper 1
      g_closed := h_problem.g_closed 1
      g_convex := h_problem.g_convex 1
      qualification := ?_ }
  · refine
      { ne_bot := ?_
        effective_domain_nonempty := ?_ }
    · intro x
      -- Neither summand of `F = f + g₁` can take the value `⊥`.
      simpa [composite_model_objective_apply, EReal.add_ne_bot_iff] using
        And.intro (h_problem.ne_bot x) ((h_problem.g_proper 0).ne_bot x)
    · rcases IsDualBlockProximalGradientProblem.exists_mem_intrinsicInterior h_problem with
        ⟨xHat, hxHat_f, hxHat_g⟩
      refine ⟨xHat, ?_⟩
      exact
        intrinsicInterior_subset <|
          mem_intrinsicInterior_reducedEffectiveDomain
            (σ := σ)
            (f := f)
            (g1 := g1)
            (g2 := g2)
            h_problem
            hxHat_f
            (hxHat_g 0)
  · -- Lower semicontinuity is preserved under `EReal` addition once both summands avoid `⊥`.
    simpa [composite_model_objective_apply] using
      h_problem.f_closed.add'
        (h_problem.g_closed 0)
        (fun x ↦ EReal.continuousAt_add
          (Or.inr ((h_problem.g_proper 0).ne_bot x))
          (Or.inl (h_problem.ne_bot x)))
  · rcases IsDualBlockProximalGradientProblem.exists_mem_intrinsicInterior h_problem with
      ⟨xHat, hxHat_f, hxHat_g⟩
    refine ⟨xHat, ?_⟩
    constructor
    · exact
        mem_intrinsicInterior_reducedEffectiveDomain
          (σ := σ)
          (f := f)
          (g1 := g1)
          (g2 := g2)
          h_problem
          hxHat_f
          (hxHat_g 0)
    · -- The second block witness is already a witness for the identity-map qualification.
      change xHat ∈ intrinsicInterior ℝ (effective_domain g2)
      simpa using hxHat_g 1

end IsDualBlockProximalGradientProblem

/-- Helper for Theorem 12.19: conjugating the primal conjugate `h∗` at `toDualMap x` matches the
usual biconjugate evaluation of `h` at `x`. -/
private lemma conjugatePrimalDual_eq_biconjugateEval
    (h : E → EReal) (x : E) :
    conjugate_function (h∗) (InnerProductSpace.toDualMap ℝ E x) =
      conjugate_function (conjugate_function h) (Module.Dual.eval ℝ E x) := by
  -- Rewrite both conjugates as suprema and compare their ranges through the Riesz surjection.
  rw [conjugate_function_apply, conjugate_function_apply]
  have hrange :
      Set.range (fun z : E ↦ (((InnerProductSpace.toDualMap ℝ E x) z : ℝ) : EReal) - (h∗) z) =
        Set.range (fun y : Module.Dual ℝ E ↦ ((y x : ℝ) : EReal) - conjugate_function h y) := by
    ext r
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨InnerProductSpace.toDualMap ℝ E z, ?_⟩
      -- On primal points, the two affine-minus-conjugate integrands are the same pairing.
      dsimp
      simpa [real_inner_comm]
    · rintro ⟨y, rfl⟩
      let yc : StrongDual ℝ E := LinearMap.toContinuousLinearMap y
      rcases (InnerProductSpace.toDual ℝ E).surjective yc with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      have hy : y = InnerProductSpace.toDualMap ℝ E z := by
        ext w
        have hw := congrArg (fun ψ : StrongDual ℝ E ↦ ψ w) hz.symm
        simpa [yc, InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hw
      -- Re-express the arbitrary dual vector through its primal representative.
      dsimp
      simpa [hy, InnerProductSpace.toDualMap_apply_apply, real_inner_comm]
  simpa using congrArg sSup hrange

/-- Helper for Theorem 12.19: a proper closed convex function is recovered by conjugating its
primal conjugate and evaluating at `toDualMap x`. -/
private lemma conjugatePrimalDual_eq_self
    (h : E → EReal)
    (hh_proper : IsProperExtendedRealFunction h)
    (hh_closed : LowerSemicontinuous h)
    (hh_convex : is_convex_function h)
    (x : E) :
    conjugate_function (h∗) (InnerProductSpace.toDualMap ℝ E x) = h x := by
  -- First identify the primal-conjugate conjugate with the standard biconjugate spelling.
  calc
    conjugate_function (h∗) (InnerProductSpace.toDualMap ℝ E x) =
        conjugate_function (conjugate_function h) (Module.Dual.eval ℝ E x) :=
      conjugatePrimalDual_eq_biconjugateEval (h := h) x
    _ = h x := by
      -- Then use the closed/proper/convex owner theorem to collapse the biconjugate.
      simpa [biconjugate_function] using
        congrArg (fun g : E → EReal ↦ g x)
          (biconjugate_function_eq_self_of_proper_closed_convex
            h hh_proper hh_closed hh_convex)

/-- Helper for Theorem 12.19: the dual conjugate of `f∗ + g₁∗`, evaluated at `y`, is exactly the
reduced conjugate `(f + g₁)∗ y`. -/
private lemma conjugateSumOfPrimalConjugates_eq_reducedConjugate
    (h_problem : IsDualBlockProximalGradientProblem f ![g1, g2] σ)
    (y : E) :
    conjugate_function (conjugate_function (f∗) + conjugate_function (g1∗))
        (Module.Dual.eval ℝ E y) =
      (F∗) y := by
  have hf_convex : is_convex_function f := by
    have hf_convex_toReal :
        ConvexOn ℝ (effective_domain f) (fun z : E ↦ (f z).toReal) := by
      -- The standing strong-convexity owner already contains the convexity of `f`.
      exact (h_problem.f_strongly_convex.strictConvexOn σ.2).convexOn
    rw [is_convex_function_iff_convexOn_toReal (fun z _ ↦ h_problem.ne_bot z)]
    exact hf_convex_toReal
  have hf_star_biconj : ∀ x : E,
      conjugate_function (f∗) (InnerProductSpace.toDualMap ℝ E x) = f x :=
    conjugatePrimalDual_eq_self
      (h := f)
      h_problem.toIsProperExtendedRealFunction
      h_problem.f_closed
      hf_convex
  have hg1_star_biconj : ∀ x : E,
      conjugate_function (g1∗) (InnerProductSpace.toDualMap ℝ E x) = g1 x :=
    conjugatePrimalDual_eq_self
      (h := g1)
      (h_problem.g_proper 0)
      (h_problem.g_closed 0)
      (h_problem.g_convex 0)
  have hrange :
      Set.range
        (fun φ : Module.Dual ℝ E ↦
          (((Module.Dual.eval ℝ E y) φ : ℝ) : EReal) -
            (conjugate_function (f∗) φ + conjugate_function (g1∗) φ)) =
        Set.range (fun x : E ↦ (((inner ℝ x y : ℝ) : EReal)) - F x) := by
    ext r
    constructor
    · rintro ⟨φ, rfl⟩
      let φc : StrongDual ℝ E := LinearMap.toContinuousLinearMap φ
      rcases (InnerProductSpace.toDual ℝ E).surjective φc with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      have hφ : φ = InnerProductSpace.toDualMap ℝ E x := by
        ext w
        have hw := congrArg (fun ψ : StrongDual ℝ E ↦ ψ w) hx.symm
        simpa [φc, InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hw
      -- Replace the dual vector by its primal representative and collapse both biconjugates.
      dsimp
      simpa [hφ, hf_star_biconj x, hg1_star_biconj x, composite_model_objective_apply,
        InnerProductSpace.toDualMap_apply_apply, real_inner_comm]
    · rintro ⟨x, rfl⟩
      refine ⟨InnerProductSpace.toDualMap ℝ E x, ?_⟩
      -- The forward Riesz image gives the matching dual integrand immediately.
      dsimp
      simpa [hf_star_biconj x, hg1_star_biconj x, composite_model_objective_apply,
        InnerProductSpace.toDualMap_apply_apply, real_inner_comm]
  -- Compare the two conjugate supremums through the same range identification.
  rw [conjugate_function_apply, conjugate_function_primal_apply, conjugate_function_apply]
  simpa [composite_model_objective_apply, InnerProductSpace.toDualMap_apply_apply,
    real_inner_comm] using congrArg sSup hrange

/-- Helper for Theorem 12.19: strong convexity of the reduced primal term `F = f + g₁` makes its
conjugate finite at every dual point. -/
private lemma reducedConjugateFinite
    (h_problem : IsDualBlockProximalGradientProblem f ![g1, g2] σ)
    (y : E) :
    (F∗) y ≠ ⊥ ∧ (F∗) y < ⊤ := by
  have hRed :=
    IsDualBlockProximalGradientProblem.toReducedProblem
      (σ := σ)
      (f := f)
      (g1 := g1)
      (g2 := g2)
      h_problem
  -- The reduced Chapter 12.1 owner gives the exact hypotheses of Theorem 5.26.
  have hfin :=
    conjugate_function_finite_of_proper_closed_strongConvexOn
      (σ : ℝ)
      σ.2
      F
      hRed.toIsProperExtendedRealFunction
      hRed.f_closed
      hRed.f_strongly_convex
      (InnerProductSpace.toDual ℝ E y)
  simpa [conjugate_function_strongDual, conjugate_function_primal_apply, conjugate_function] using
    hfin

/-- Helper for Theorem 12.19: every first-block slice majorizes the reduced conjugate
`(f + g₁)∗`. -/
private lemma reducedConjugate_le_firstBlockSlice
    (h_problem : IsDualBlockProximalGradientProblem f ![g1, g2] σ)
    (y z : E) :
    (F∗) y ≤ (f∗) (z + y) + (g1∗) (-z) := by
  have hf_conj_ne_bot : (f∗) (z + y) ≠ ⊥ := by
    -- Properness keeps every conjugate evaluation away from `⊥`.
    simpa [conjugate_function_primal_apply] using
      conjugate_function_ne_bot_of_proper
        f
        h_problem.toIsProperExtendedRealFunction
        (InnerProductSpace.toDualMap ℝ E (z + y))
  have hg1_conj_ne_bot : (g1∗) (-z) ≠ ⊥ := by
    -- The same Chapter 4 owner applies to the first nonsmooth block.
    simpa [conjugate_function_primal_apply] using
      conjugate_function_ne_bot_of_proper
        g1
        (h_problem.g_proper 0)
        (InnerProductSpace.toDualMap ℝ E (-z))
  rw [conjugate_function_primal_apply, conjugate_function_apply]
  refine sSup_le ?_
  rintro _ ⟨x, rfl⟩
  have hf :
      (((inner ℝ x z : ℝ) : EReal)) + (((inner ℝ x y : ℝ) : EReal)) ≤
        f x + (f∗) (z + y) := by
    simpa [conjugate_function_primal_apply, InnerProductSpace.toDualMap_apply_apply,
      real_inner_comm, inner_add_right, EReal.coe_add] using
      fenchel_inequality
        f
        x
        (InnerProductSpace.toDualMap ℝ E (z + y))
        h_problem.toIsProperExtendedRealFunction
  have hg :
      (((inner ℝ x (-z) : ℝ) : EReal)) ≤
        g1 x + (g1∗) (-z) := by
    simpa [conjugate_function_primal_apply, InnerProductSpace.toDualMap_apply_apply,
      real_inner_comm] using
      fenchel_inequality
        g1
        x
        (InnerProductSpace.toDualMap ℝ E (-z))
        (h_problem.g_proper 0)
  have hpair :
      ((((inner ℝ x z : ℝ) : EReal)) + (((inner ℝ x y : ℝ) : EReal))) +
          (((inner ℝ x (-z) : ℝ) : EReal)) =
        (((inner ℝ x y : ℝ) : EReal)) := by
    rw [← EReal.coe_add, ← EReal.coe_add]
    congr 1
    rw [inner_neg_right]
    ring
  have hsum :
      (((inner ℝ x y : ℝ) : EReal)) ≤
        F x + ((f∗) (z + y) + (g1∗) (-z)) := by
    calc
      (((inner ℝ x y : ℝ) : EReal)) =
          ((((inner ℝ x z : ℝ) : EReal)) + (((inner ℝ x y : ℝ) : EReal))) +
            (((inner ℝ x (-z) : ℝ) : EReal)) := by
              symm
              exact hpair
      _ ≤ (f x + (f∗) (z + y)) + (g1 x + (g1∗) (-z)) := add_le_add hf hg
      _ = F x + ((f∗) (z + y) + (g1∗) (-z)) := by
            simp [add_assoc, add_left_comm, add_comm]
  have hFx_ne_bot : F x ≠ ⊥ := by
    simpa [composite_model_objective_apply, EReal.add_ne_bot_iff] using
      And.intro (h_problem.ne_bot x) ((h_problem.g_proper 0).ne_bot x)
  have hrhs_ne_bot :
      (f∗) (z + y) + (g1∗) (-z) ≠ ⊥ := by
    simpa using (EReal.add_ne_bot_iff.mpr ⟨hf_conj_ne_bot, hg1_conj_ne_bot⟩)
  have hsub :
      ((((InnerProductSpace.toDualMap ℝ E y) x : ℝ) : EReal) - F x) ≤
        (f∗) (z + y) + (g1∗) (-z) := by
    have hsum' :
        (((inner ℝ y x : ℝ) : EReal)) ≤
          F x + ((f∗) (z + y) + (g1∗) (-z)) := by
      simpa [real_inner_comm] using hsum
    exact
      (EReal.sub_le_iff_le_add
        (a := ((((InnerProductSpace.toDualMap ℝ E y) x : ℝ) : EReal)))
        (b := F x)
        (c := (f∗) (z + y) + (g1∗) (-z))
        (.inl hFx_ne_bot)
        (.inr hrhs_ne_bot)).2 (by
          simpa [InnerProductSpace.toDualMap_apply_apply, add_assoc, add_left_comm, add_comm] using
            hsum')
  simpa [InnerProductSpace.toDualMap_apply_apply] using hsub

/-- Helper for Theorem 12.19: the first-block slice parameterization is the infimal convolution
`(f∗) □ (g₁∗)` after the change of variables `u = z + y`. -/
private lemma firstBlockSlice_sInf_eq_infimalConvolution
    (y : E) :
    sInf (Set.range fun z : E ↦ (f∗) (z + y) + (g1∗) (-z)) = ((f∗) □ (g1∗)) y := by
  have hrange :
      Set.range (fun z : E ↦ (f∗) (z + y) + (g1∗) (-z)) =
        Set.range (fun u : E ↦ (f∗) u + (g1∗) (y - u)) := by
    ext r
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨z + y, ?_⟩
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    · rintro ⟨u, rfl⟩
      refine ⟨u - y, ?_⟩
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  -- Rewrite the `iInf` owner of `□` into the equivalent `sInf` over the translated slice range.
  calc
    sInf (Set.range fun z : E ↦ (f∗) (z + y) + (g1∗) (-z))
        = sInf (Set.range fun u : E ↦ (f∗) u + (g1∗) (y - u)) := by
            rw [hrange]
    _ = ((f∗) □ (g1∗)) y := by
          rw [infimal_convolution_apply, sInf_range]

/-- Helper for Theorem 12.19: the infimal convolution `(f∗) □ (g₁∗)` is finite everywhere. -/
private lemma firstBlockDualInfimalConvolution_realValued
    (h_problem : IsDualBlockProximalGradientProblem f ![g1, g2] σ) :
    ∀ y : E, ∃ r : ℝ, (((f∗) □ (g1∗)) y) = (r : EReal) := by
  intro y
  have hf_strong : is_strongly_convex_function f (σ : ℝ) := by
    -- Repackage the Chapter 12 strong-convexity owner into the Chapter 5 source predicate.
    refine (is_strongly_convex_function_iff_strongConvexOn_toReal).2 ?_
    exact ⟨σ.2, h_problem.ne_bot, h_problem.f_strongly_convex⟩
  have hf_conj_finite :
      ∀ v : E, (f∗) v ≠ ⊥ ∧ (f∗) v < ⊤ := by
    intro v
    have hfin :=
      conjugate_function_finite_of_proper_closed_strongConvexOn
        (σ : ℝ)
        σ.2
        f
        h_problem.toIsProperExtendedRealFunction
        h_problem.f_closed
        h_problem.f_strongly_convex
        (InnerProductSpace.toDual ℝ E v)
    simpa [conjugate_function_strongDual, conjugate_function_primal_apply, conjugate_function] using
      hfin
  have hg1_convex : is_convex_function g1 := h_problem.g_convex 0
  rcases
      conjugate_function_effective_domain_nonempty
        g1
        (h_problem.g_proper 0)
        hg1_convex with
    ⟨v0Dual, hv0Dual_dom⟩
  let v0Strong : StrongDual ℝ E := LinearMap.toContinuousLinearMap v0Dual
  rcases
      (InnerProductSpace.toDual ℝ E).surjective
        v0Strong with
    ⟨v0, hv0⟩
  have hv0_top : (g1∗) v0 ≠ ⊤ := by
    have hv0Strong_top : conjugate_function g1 v0Strong < ⊤ := by
      simpa [v0Strong] using mem_effective_domain.mp hv0Dual_dom
    have hv0_top' : conjugate_function g1 (InnerProductSpace.toDualMap ℝ E v0) < ⊤ := by
      simpa [v0Strong, InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hv0 ▸ hv0Strong_top
    rw [conjugate_function_primal_apply]
    exact ne_of_lt hv0_top'
  have hv0_bot : (g1∗) v0 ≠ ⊥ := by
    have hv0Strong_bot : conjugate_function g1 v0Strong ≠ ⊥ := by
      simpa [v0Strong] using
        conjugate_function_ne_bot_of_proper g1 (h_problem.g_proper 0) v0Dual
    have hv0_bot' : conjugate_function g1 (InnerProductSpace.toDualMap ℝ E v0) ≠ ⊥ := by
      simpa [v0Strong, InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hv0 ▸ hv0Strong_bot
    rw [conjugate_function_primal_apply]
    exact hv0_bot'
  let S : Set EReal := Set.range fun z : E ↦ (f∗) (z + y) + (g1∗) (-z)
  have hS_lt_top : sInf S < ⊤ := by
    refine lt_of_le_of_lt (sInf_le (show (f∗) (-v0 + y) + (g1∗) (-(-v0)) ∈ S by
      exact ⟨-v0, rfl⟩)) ?_
    simpa [S, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      EReal.add_lt_top (ne_of_lt (hf_conj_finite (y - v0)).2) hv0_top
  have hred_fin := reducedConjugateFinite (σ := σ) (f := f) (g1 := g1) (g2 := g2) h_problem y
  have hred_le : (F∗) y ≤ sInf S := by
    refine le_sInf ?_
    rintro _ ⟨z, rfl⟩
    exact reducedConjugate_le_firstBlockSlice (σ := σ) (f := f) (g1 := g1) (g2 := g2) h_problem y z
  have hS_ne_bot : sInf S ≠ ⊥ := by
    intro hS_bot
    have : (F∗) y = ⊥ := le_antisymm (by simpa [hS_bot] using hred_le) bot_le
    exact hred_fin.1 this
  have hinf_ne_bot : ((f∗) □ (g1∗)) y ≠ ⊥ := by
    rw [← firstBlockSlice_sInf_eq_infimalConvolution (f := f) (g1 := g1) y]
    exact hS_ne_bot
  have hinf_lt_top : ((f∗) □ (g1∗)) y < ⊤ := by
    rw [← firstBlockSlice_sInf_eq_infimalConvolution (f := f) (g1 := g1) y]
    exact hS_lt_top
  -- Once both infinite values are excluded, the infimal convolution is an `EReal` coercion.
  refine ⟨(((f∗) □ (g1∗)) y).toReal, ?_⟩
  simpa using (EReal.coe_toReal (ne_of_lt hinf_lt_top) hinf_ne_bot).symm

/-- Helper for Theorem 12.19: the reduced conjugate `(f + g₁)∗` is the first-block infimal
convolution slice of `f∗` and `g₁∗`. -/
private lemma reducedConjugate_eq_infimalConvolutionFirstBlock
    (h_problem : IsDualBlockProximalGradientProblem f ![g1, g2] σ)
    (y : E) :
    (F∗) y = sInf (Set.range fun z : E ↦ (f∗) (z + y) + (g1∗) (-z)) := by
  have hf_convex : is_convex_function f := by
    have hf_convex_toReal :
        ConvexOn ℝ (effective_domain f) (fun z : E ↦ (f z).toReal) := by
      -- Strong convexity implies the convexity needed for primal-conjugate properness.
      exact (h_problem.f_strongly_convex.strictConvexOn σ.2).convexOn
    rw [is_convex_function_iff_convexOn_toReal (fun z _ ↦ h_problem.ne_bot z)]
    exact hf_convex_toReal
  have hf_star_proper : IsProperExtendedRealFunction (f∗) :=
    conjugate_function_primal_proper_of_proper_convex
      f
      h_problem.toIsProperExtendedRealFunction
      hf_convex
  have hg1_star_proper : IsProperExtendedRealFunction (g1∗) :=
    conjugate_function_primal_proper_of_proper_convex
      g1
      (h_problem.g_proper 0)
      (h_problem.g_convex 0)
  -- Route correction: rewrite the Proposition 5.17 right-hand side by an explicit Riesz-range
  -- transport, instead of introducing a new theorem-local dual/primal abstraction.
  calc
    (F∗) y =
        conjugate_function (conjugate_function (f∗) + conjugate_function (g1∗))
          (Module.Dual.eval ℝ E y) := by
            symm
            exact
              conjugateSumOfPrimalConjugates_eq_reducedConjugate
                (σ := σ)
                (f := f)
                (g1 := g1)
                (g2 := g2)
                h_problem
                y
    _ = ((f∗) □ (g1∗)) y := by
          symm
          exact
            proper_closed_convex_infimal_convolution_eq_dual_conjugate_sum_conjugates_apply
              (f∗)
              (g1∗)
              hf_star_proper
              hg1_star_proper
              (conjugate_function_closed_and_convex f).1
              (conjugate_function_closed_and_convex g1).1
              (conjugate_function_closed_and_convex f).2
              (conjugate_function_closed_and_convex g1).2
              (firstBlockDualInfimalConvolution_realValued
                (σ := σ)
                (f := f)
                (g1 := g1)
                (g2 := g2)
                h_problem)
              y
    _ = sInf (Set.range fun z : E ↦ (f∗) (z + y) + (g1∗) (-z)) := by
          rw [← firstBlockSlice_sInf_eq_infimalConvolution (f := f) (g1 := g1) y]

/-- Helper for Theorem 12.19: translating an `EReal` range by a finite scalar translates its
infimum by the same scalar. -/
private theorem ereal_sInf_range_add_finite
    {α : Type*} (φ : α → EReal) (r : ℝ) :
    sInf (Set.range fun a : α ↦ φ a + (r : EReal)) = sInf (Set.range φ) + (r : EReal) := by
  let shift : EReal → EReal := fun t ↦ t + (r : EReal)
  have hmono : Monotone shift := by
    intro a b hab
    simpa [shift, add_assoc, add_left_comm, add_comm] using add_le_add_right hab (r : EReal)
  have hcontAdd :
      ContinuousAt (fun p : EReal × EReal ↦ p.1 + p.2) (sInf (Set.range φ), (r : EReal)) := by
    apply EReal.continuousAt_add <;> simp
  have hcont : ContinuousAt shift (sInf (Set.range φ)) := by
    simpa [shift] using hcontAdd.comp₂ continuousAt_id continuousAt_const
  have htop : shift ⊤ = ⊤ := by
    simp [shift]
  have hmap :
      shift (sInf (Set.range φ)) = sInf (shift '' Set.range φ) :=
    Monotone.map_sInf_of_continuousAt (s := Set.range φ) hcont hmono htop
  have himage :
      shift '' Set.range φ = Set.range fun a : α ↦ φ a + (r : EReal) := by
    ext t
    constructor
    · rintro ⟨u, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨φ a, ⟨a, rfl⟩, rfl⟩
  simpa [shift, himage] using hmap.symm

/-- Helper for Theorem 12.19: fixing the second block, the two-block dual objective is bounded
above by the reduced dual objective at that second component. -/
private lemma blockDualObjective_le_reducedDualObjectiveSecond
    (h_problem : IsDualBlockProximalGradientProblem f ![g1, g2] σ)
    (y : Fin 2 → E) :
    q(f, ![g1, g2]) y ≤ qRed (y 1) := by
  have hf_conj_ne_bot : (f∗) (y 0 + y 1) ≠ ⊥ := by
    -- Properness keeps every conjugate evaluation finite below.
    simpa [conjugate_function_primal_apply] using
      conjugate_function_ne_bot_of_proper
        f
        h_problem.toIsProperExtendedRealFunction
        (InnerProductSpace.toDualMap ℝ E (y 0 + y 1))
  have hg1_conj_ne_bot : (g1∗) (-y 0) ≠ ⊥ := by
    -- The same owner theorem applies to the first block penalty.
    simpa [conjugate_function_primal_apply] using
      conjugate_function_ne_bot_of_proper
        g1
        (h_problem.g_proper 0)
        (InnerProductSpace.toDualMap ℝ E (-y 0))
  have hg2_conj_ne_bot : (g2∗) (-y 1) ≠ ⊥ := by
    -- The second block conjugate stays away from `⊥` as well.
    simpa [conjugate_function_primal_apply] using
      conjugate_function_ne_bot_of_proper
        g2
        (h_problem.g_proper 1)
        (InnerProductSpace.toDualMap ℝ E (-y 1))
  have hconj_le :
      (F∗) (y 1) ≤ (f∗) (y 0 + y 1) + (g1∗) (-y 0) := by
    -- Route correction: bound the reduced conjugate directly by Fenchel on `f` and `g₁`,
    -- instead of importing the broken duplicated-model bridge.
    rw [conjugate_function_primal_apply, conjugate_function_apply]
    refine sSup_le ?_
    rintro _ ⟨x, rfl⟩
    have hf :
        (((inner ℝ x (y 0) : ℝ) : EReal)) +
            (((inner ℝ x (y 1) : ℝ) : EReal)) ≤
          f x + (f∗) (y 0 + y 1) := by
      simpa [conjugate_function_primal_apply, InnerProductSpace.toDualMap_apply_apply,
        real_inner_comm, inner_add_right, EReal.coe_add] using
        fenchel_inequality
          f
          x
          (InnerProductSpace.toDualMap ℝ E (y 0 + y 1))
          h_problem.toIsProperExtendedRealFunction
    have hg :
        (((inner ℝ x (-y 0) : ℝ) : EReal)) ≤
          g1 x + (g1∗) (-y 0) := by
      simpa [conjugate_function_primal_apply, InnerProductSpace.toDualMap_apply_apply,
        real_inner_comm] using
        fenchel_inequality
          g1
          x
          (InnerProductSpace.toDualMap ℝ E (-y 0))
          (h_problem.g_proper 0)
    have hpair :
        ((((inner ℝ x (y 0) : ℝ) : EReal)) +
            (((inner ℝ x (y 1) : ℝ) : EReal))) +
            (((inner ℝ x (-y 0) : ℝ) : EReal)) =
          (((inner ℝ x (y 1) : ℝ) : EReal)) := by
      rw [← EReal.coe_add, ← EReal.coe_add]
      congr 1
      rw [inner_neg_right]
      ring
    have hsum :
        (((inner ℝ x (y 1) : ℝ) : EReal)) ≤
          F x + ((f∗) (y 0 + y 1) + (g1∗) (-y 0)) := by
      calc
        (((inner ℝ x (y 1) : ℝ) : EReal)) =
            ((((inner ℝ x (y 0) : ℝ) : EReal)) +
              (((inner ℝ x (y 1) : ℝ) : EReal))) +
              (((inner ℝ x (-y 0) : ℝ) : EReal)) := by
                symm
                exact hpair
        _ ≤ (f x + (f∗) (y 0 + y 1)) + (g1 x + (g1∗) (-y 0)) := add_le_add hf hg
        _ = F x + ((f∗) (y 0 + y 1) + (g1∗) (-y 0)) := by
              simp [add_assoc, add_left_comm, add_comm]
    have hFx_ne_bot : F x ≠ ⊥ := by
      simpa [composite_model_objective_apply, EReal.add_ne_bot_iff] using
        And.intro (h_problem.ne_bot x) ((h_problem.g_proper 0).ne_bot x)
    have hrhs_ne_bot :
        (f∗) (y 0 + y 1) + (g1∗) (-y 0) ≠ ⊥ := by
      simpa using (EReal.add_ne_bot_iff.mpr ⟨hf_conj_ne_bot, hg1_conj_ne_bot⟩)
    have hsub :
        ((((InnerProductSpace.toDualMap ℝ E (y 1)) x : ℝ) : EReal) - F x) ≤
          (f∗) (y 0 + y 1) + (g1∗) (-y 0) := by
      have hsum' :
          (((inner ℝ (y 1) x : ℝ) : EReal)) ≤
            F x + ((f∗) (y 0 + y 1) + (g1∗) (-y 0)) := by
        simpa [real_inner_comm] using hsum
      exact
        (EReal.sub_le_iff_le_add
          (a := ((((InnerProductSpace.toDualMap ℝ E (y 1)) x : ℝ) : EReal)))
          (b := F x)
          (c := (f∗) (y 0 + y 1) + (g1∗) (-y 0))
          (.inl hFx_ne_bot)
          (.inr hrhs_ne_bot)).2 (by
            simpa [InnerProductSpace.toDualMap_apply_apply, add_assoc, add_left_comm, add_comm] using
              hsum')
    simpa [InnerProductSpace.toDualMap_apply_apply] using hsub
  have hmain :
      -((f∗) (y 0 + y 1)) - (g1∗) (-y 0) ≤ -((F∗) (y 1)) := by
    -- Collapse the two conjugate terms into one negated sum, then reverse the order.
    calc
      -((f∗) (y 0 + y 1)) - (g1∗) (-y 0) =
          -((f∗) (y 0 + y 1) + (g1∗) (-y 0)) := by
            simpa using
              (EReal.neg_add
                (.inl hf_conj_ne_bot)
                (.inr hg1_conj_ne_bot)).symm
      _ ≤ -((F∗) (y 1)) := by
            simpa using (EReal.neg_le_neg_iff.mpr hconj_le)
  -- Rewrite both dual objectives and add the common `g₂` term on the right.
  rw [dual_block_proximal_gradient_dual_objective_apply,
    dual_based_proximal_gradient_lagrange_dual_objective_primal_apply, Fin.sum_univ_two]
  have hsum_blocks :
      ∑ i, (![g1, g2] i)∗ (-y i) = (g1∗) (-y 0) + (g2∗) (-y 1) := by
    simp
  have hsum_conj :
      -(((g1∗) (-y 0)) + ((g2∗) (-y 1))) =
        -(g1∗) (-y 0) - (g2∗) (-y 1) := by
    simpa using
      (EReal.neg_add
        (.inl hg1_conj_ne_bot)
        (.inr hg2_conj_ne_bot))
  rw [hsum_blocks]
  have hleft :
      -((f∗) (y 0 + y 1)) - ((g1∗) (-y 0) + (g2∗) (-y 1)) =
        (-((f∗) (y 0 + y 1)) - (g1∗) (-y 0)) - (g2∗) (-y 1) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      congrArg (fun t : EReal ↦ -((f∗) (y 0 + y 1)) + t) hsum_conj
  rw [hleft, LinearMap.adjoint_id]
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    add_le_add_right hmain (-(g2∗) (-y 1))

/-- Helper for Theorem 12.19: on the literal two-block slice `![z, y]`, the block dual objective
expands to the stable first/second-block normal form used in the reduced dual bridge. -/
private lemma blockDualObjective_firstSecondSlice_apply
    (z y : E) :
    q(f, ![g1, g2]) ![z, y] =
      -((f∗) (z + y)) - ((g1∗) (-z) + (g2∗) (-y)) := by
  -- Normalize the two-block vector literal once so later slice proofs can stay in this spelling.
  rw [dual_block_proximal_gradient_dual_objective_apply, Fin.sum_univ_two]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 12.19: for fixed `y`, the reduced dual objective is the supremum of the
two-block dual objective over all first-block slices `z ↦ (z, y)`. -/
private lemma reducedDualObjective_eq_sSup_blockFirstSlice
    (h_problem : IsDualBlockProximalGradientProblem f ![g1, g2] σ)
    (y : E) :
    qRed y = sSup (Set.range fun z : E ↦ q(f, ![g1, g2]) ![z, y]) := by
  have hg2_conj_ne_bot : (g2∗) (-y) ≠ ⊥ := by
    -- Properness of `g₂` keeps its conjugate away from `⊥` at the current second-block slice.
    simpa [conjugate_function_primal_apply] using
      conjugate_function_ne_bot_of_proper
        g2
        (h_problem.g_proper 1)
        (InnerProductSpace.toDualMap ℝ E (-y))
  by_cases htop : (g2∗) (-y) = ⊤
  · -- If `g₂*(-y) = ⊤`, then both the reduced dual objective and every block slice collapse to `⊥`.
    rw [dual_based_proximal_gradient_lagrange_dual_objective_primal_apply, htop]
    have hsliceTop :
        (fun z : E ↦ q(f, ![g1, g2]) ![z, y]) =
          fun _ : E ↦ (⊥ : EReal) := by
      funext z
      have hg1_conj_ne_bot : (g1∗) (-z) ≠ ⊥ := by
        -- The first-block conjugate is proper at every slice point.
        simpa [conjugate_function_primal_apply] using
          conjugate_function_ne_bot_of_proper
            g1
            (h_problem.g_proper 0)
            (InnerProductSpace.toDualMap ℝ E (-z))
      have hsum_top : (g1∗) (-z) + ⊤ = ⊤ := by
        simpa using EReal.add_top_of_ne_bot hg1_conj_ne_bot
      have hsum_top' :
          conjugate_function g1 (InnerProductSpace.toDualMap ℝ E (-z)) + ⊤ = ⊤ := by
        simpa [conjugate_function_primal_apply] using hsum_top
      rw [blockDualObjective_firstSecondSlice_apply (f := f) (g1 := g1) (g2 := g2) z y, htop]
      rw [hsum_top']
      simp [sub_eq_add_neg]
    rw [hsliceTop]
    simp
  · let r : ℝ := ((g2∗) (-y)).toReal
    have hg2_val : ((r : ℝ) : EReal) = (g2∗) (-y) := by
      -- On the finite branch, recover the second conjugate value from its real part.
      exact EReal.coe_toReal htop hg2_conj_ne_bot
    have hred_fin :=
      reducedConjugateFinite
        (σ := σ)
        (f := f)
        (g1 := g1)
        (g2 := g2)
        h_problem
        y
    have hsInf_eq :
        (F∗) y = sInf (Set.range fun z : E ↦ (f∗) (z + y) + (g1∗) (-z)) :=
      reducedConjugate_eq_infimalConvolutionFirstBlock
        (σ := σ)
        (f := f)
        (g1 := g1)
        (g2 := g2)
        h_problem
        y
    let posSlice : E → EReal := fun z ↦ (f∗) (z + y) + (g1∗) (-z) + ((r : ℝ) : EReal)
    let negSlice : E → EReal := fun z ↦ -(posSlice z)
    have hnegIntegrandRange :
        Set.range negSlice = -Set.range posSlice := by
      -- The normalized slice family is exactly the pointwise negation of the positive slice
      -- range.
      ext t
      constructor
      · rintro ⟨z, rfl⟩
        rw [Set.mem_neg]
        exact ⟨z, by simp [negSlice, posSlice]⟩
      · rw [Set.mem_neg]
        rintro ⟨z, hz⟩
        refine ⟨z, ?_⟩
        simpa [negSlice, posSlice] using congrArg Neg.neg hz
    have hnegRange :
        -Set.range negSlice = Set.range posSlice := by
      -- Negating the normalized slice range removes the outer minus pointwise.
      calc
        -Set.range negSlice = -(-Set.range posSlice) := by
              rw [hnegIntegrandRange]
        _ = Set.range posSlice := by
              ext t
              simp [Set.mem_neg]
    have hsupSlices :
        sSup (Set.range negSlice) = -(sInf (Set.range posSlice)) := by
      -- Convert the supremum of the negated slice family into the negated infimum of the
      -- positive slice family through the standard `EReal` negation bridge.
      have hsInf_neg :
          sInf (Set.range posSlice) = -sSup (Set.range negSlice) := by
        calc
          sInf (Set.range posSlice) = sInf (-Set.range negSlice) := by
                  rw [hnegRange]
          _ = -sSup (Set.range negSlice) := by
                  exact ereal_sInf_neg (Set.range negSlice)
      calc
        sSup (Set.range negSlice) = -(-sSup (Set.range negSlice)) := by
          simp
        _ = -(sInf (Set.range posSlice)) := by
                rw [hsInf_neg]
    have hsliceFun :
        (fun z : E ↦ q(f, ![g1, g2]) ![z, y]) =
          negSlice := by
      -- Freeze the slice integrand in the finite branch using the recovered real scalar `r`.
      funext z
      have hf_conj_ne_bot : (f∗) (z + y) ≠ ⊥ := by
        simpa [conjugate_function_primal_apply] using
          conjugate_function_ne_bot_of_proper
            f
            h_problem.toIsProperExtendedRealFunction
            (InnerProductSpace.toDualMap ℝ E (z + y))
      have hg1_conj_ne_bot : (g1∗) (-z) ≠ ⊥ := by
        simpa [conjugate_function_primal_apply] using
          conjugate_function_ne_bot_of_proper
            g1
            (h_problem.g_proper 0)
            (InnerProductSpace.toDualMap ℝ E (-z))
      have hsum_ne_bot :
          (g2∗) (-y) + (g1∗) (-z) ≠ ⊥ := by
        simpa [add_comm] using
          (EReal.add_ne_bot_iff.mpr ⟨hg2_conj_ne_bot, hg1_conj_ne_bot⟩)
      rw [blockDualObjective_firstSecondSlice_apply (f := f) (g1 := g1) (g2 := g2) z y]
      simpa [negSlice, posSlice, hg2_val, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (EReal.neg_add (.inl hf_conj_ne_bot) (.inr hsum_ne_bot)).symm
    -- Route correction: keep the reduced-owner slice proof entirely in the literal `![z, y]`
    -- normal form, and use `ereal_sInf_neg` only after the constant `(g₂∗)(-y)` is isolated.
    calc
      qRed y = -((F∗) y + ((r : ℝ) : EReal)) := by
        rw [dual_based_proximal_gradient_lagrange_dual_objective_primal_apply, ← hg2_val]
        simpa [sub_eq_add_neg] using
          (EReal.neg_add (.inl hred_fin.1) (.inr (EReal.coe_ne_bot r))).symm
      _ = -(sInf (Set.range fun z : E ↦ (f∗) (z + y) + (g1∗) (-z)) + ((r : ℝ) : EReal)) := by
        rw [hsInf_eq]
      _ = -(sInf
            (Set.range posSlice)) := by
        simpa [posSlice] using
          congrArg Neg.neg
            ((ereal_sInf_range_add_finite
              (φ := fun z : E ↦ (f∗) (z + y) + (g1∗) (-z))
              (r := r)).symm)
      _ = sSup (Set.range negSlice) := by
        rw [hsupSlices]
      _ = sSup (Set.range fun z : E ↦ q(f, ![g1, g2]) ![z, y]) := by
        rw [hsliceFun]

/-- Helper for Theorem 12.19: the reduced Chapter 12 dual problem value is the supremum of the
primal-space reduced dual objective `qRed`. -/
private lemma reducedDualProblemValue_eq_sSup_primal :
    qRedOpt = sSup (Set.range qRed) := by
  -- Compare the canonical dual-owner supremum with the primal-space Riesz model pointwise.
  rw [dual_based_proximal_gradient_lagrange_dual_problem_value_eq_sSup]
  apply le_antisymm
  · refine sSup_le ?_
    rintro z ⟨φ, rfl⟩
    let φc : StrongDual ℝ E := LinearMap.toContinuousLinearMap φ
    rcases (InnerProductSpace.toDual ℝ E).surjective φc with ⟨y, hy⟩
    have hφ : φ = InnerProductSpace.toDualMap ℝ E y := by
      ext w
      have hw := congrArg (fun ψ : StrongDual ℝ E ↦ ψ w) hy.symm
      simpa [φc, InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hw
    rw [hφ]
    have hobj :
        dual_based_proximal_gradient_lagrange_dual_objective F g2 A
            (InnerProductSpace.toDualMap ℝ E y) =
          qRed y := by
      symm
      simpa using (primalDualObjective_eq_dualOwner (f := F) (g := g2) A y).symm
    calc
      dual_based_proximal_gradient_lagrange_dual_objective F g2 A
          (InnerProductSpace.toDualMap ℝ E y) = qRed y := hobj
      _ ≤ sSup (Set.range qRed) := le_sSup ⟨y, rfl⟩
  · refine sSup_le ?_
    rintro z ⟨y, rfl⟩
    have hobj :
        qRed y =
          dual_based_proximal_gradient_lagrange_dual_objective F g2 A
            (InnerProductSpace.toDualMap ℝ E y) := by
      simpa using primalDualObjective_eq_dualOwner (f := F) (g := g2) A y
    calc
      qRed y =
          dual_based_proximal_gradient_lagrange_dual_objective F g2 A
            (InnerProductSpace.toDualMap ℝ E y) := hobj
      _ ≤
          sSup
            (Set.range
              (dual_based_proximal_gradient_lagrange_dual_objective F g2 A)) :=
        le_sSup ⟨InnerProductSpace.toDualMap ℝ E y, rfl⟩

/-- Helper for Theorem 12.19: the reduced and two-block dual problem values coincide once both
models are related through the same primal objective `f + g₁ + g₂`. -/
private lemma reducedDualProblemValue_eq_blockDualProblemValue
    (h_problem : IsDualBlockProximalGradientProblem f ![g1, g2] σ) :
    qRedOpt = q_opt(f, ![g1, g2]) := by
  -- Compare both optimal values as supremums of the same block objective, with the reduced side
  -- first optimizing over the initial block.
  rw [reducedDualProblemValue_eq_sSup_primal, dual_block_proximal_gradient_dual_problem_value_eq_sSup]
  apply le_antisymm
  · refine sSup_le ?_
    rintro _ ⟨y, rfl⟩
    rw [reducedDualObjective_eq_sSup_blockFirstSlice
      (σ := σ) (f := f) (g1 := g1) (g2 := g2) h_problem y]
    refine sSup_le ?_
    rintro _ ⟨z, rfl⟩
    exact le_sSup ⟨![z, y], rfl⟩
  · refine sSup_le ?_
    rintro _ ⟨v, rfl⟩
    exact
      (blockDualObjective_le_reducedDualObjectiveSecond
        (σ := σ)
        (f := f)
        (g1 := g1)
        (g2 := g2)
        h_problem
        v).trans <|
        le_sSup ⟨v 1, rfl⟩

-- Proof sketch: optimize the two-block dual objective first over the first block. The resulting
-- one-variable dual problem is exactly the reduced Chapter 12 owner for `F = f + g₁`, so the
-- second component of any block-dual maximizer attains the reduced dual optimum.
/-- If `y* = (y₁*, y₂*)` is optimal for the two-block dual objective under Assumption 12.14, then
`y₂*` attains the reduced Chapter 12 dual problem value for `F = f + g₁`. -/
theorem reduced_dual_eq_problem_value_of_mem_optimal_set
    (h_problem : IsDualBlockProximalGradientProblem f ![g1, g2] σ)
    {yStar : Fin 2 → E}
    (hyStar : yStar ∈ Λ*(f, ![g1, g2])) :
    qRed (yStar 1) = qRedOpt := by
  -- Compare the reduced value at `yStar₂` with the reduced optimum from both sides.
  have hqle : ∀ y : E, qRed y ≤ qRedOpt := by
    intro y
    simpa using
      (dualObjective_le_dualProblemValue
        (f := F)
        (g := g2)
        A
        y)
  apply le_antisymm
  · exact hqle (yStar 1)
  · calc
      qRedOpt = q_opt(f, ![g1, g2]) := by
        exact
          reducedDualProblemValue_eq_blockDualProblemValue
            (σ := σ)
            (f := f)
            (g1 := g1)
            (g2 := g2)
            h_problem
      _ = q(f, ![g1, g2]) yStar := by
        symm
        exact
          dual_block_proximal_gradient_dual_objective_eq_dual_problem_value_of_mem_optimal_set
            (f := f)
            (g := ![g1, g2])
            hyStar
      _ ≤ qRed (yStar 1) :=
        blockDualObjective_le_reducedDualObjectiveSecond
          (σ := σ)
          (f := f)
          (g1 := g1)
          (g2 := g2)
          h_problem
          yStar

/-- Helper for Theorem 12.19: the reduced primal objective `pRed = f + g₁ + g₂` admits a global
minimizer. -/
private lemma existsReducedPrimalMinimizer
    (h_problem : IsDualBlockProximalGradientProblem f ![g1, g2] σ) :
    ∃ xMin : E, IsMinOn pRed Set.univ xMin := by
  have hRed :=
    IsDualBlockProximalGradientProblem.toReducedProblem
      (σ := σ)
      (f := f)
      (g1 := g1)
      (g2 := g2)
      h_problem
  have hF_strong : is_strongly_convex_function F (σ : ℝ) := by
    -- Repackage the reduced owner into the Chapter 5 strong-convexity predicate.
    refine (is_strongly_convex_function_iff_strongConvexOn_toReal).2 ?_
    exact ⟨σ.2, hRed.ne_bot, hRed.f_strongly_convex⟩
  have hpRed_strong : is_strongly_convex_function pRed (σ : ℝ) := by
    -- Adding the convex second block preserves the strong-convexity modulus.
    simpa [composite_model_objective_apply] using
      is_strongly_convex_function_add_of_is_convex_function
        hF_strong
        hRed.g_convex
        (fun x ↦ hRed.g_proper.ne_bot x)
  have hpRed_closed : LowerSemicontinuous pRed := by
    -- Lower semicontinuity is also preserved under the pointwise sum.
    simpa [composite_model_objective_apply] using
      hRed.f_closed.add'
        hRed.g_closed
        (fun x ↦
          EReal.continuousAt_add
            (Or.inr (hRed.g_proper.ne_bot x))
            (Or.inl (hRed.ne_bot x)))
  rcases IsDualBlockProximalGradientProblem.exists_mem_intrinsicInterior h_problem with
    ⟨xHat, hxHat_f, hxHat_g⟩
  have hF_dom : xHat ∈ effective_domain F := by
    exact
      intrinsicInterior_subset <|
        IsDualBlockProximalGradientProblem.mem_intrinsicInterior_reducedEffectiveDomain
          (σ := σ)
          (f := f)
          (g1 := g1)
          (g2 := g2)
          h_problem
          hxHat_f
          (hxHat_g 0)
  have hg2_dom : xHat ∈ effective_domain g2 := by
    exact intrinsicInterior_subset (hxHat_g 1)
  have hpRed_dom : xHat ∈ effective_domain pRed := by
    refine mem_effective_domain.mpr ?_
    simpa [composite_model_objective_apply] using
      EReal.add_lt_top
        (ne_of_lt (mem_effective_domain.mp hF_dom))
        (ne_of_lt (mem_effective_domain.mp hg2_dom))
  obtain ⟨xMin, hxMin, _⟩ :=
    existsUnique_isMinOn_univ_of_closed_strongly_convex
      hpRed_strong
      ⟨xHat, hpRed_dom⟩
      hpRed_closed
  exact ⟨xMin, hxMin⟩

-- Proof sketch: combine the reduced dual optimality of `y₂*` with the Chapter 12 primal argmax
-- characterization at that dual point. Under the reduced standing assumptions, an argmax point at
-- an optimal dual solution is a primal minimizer of `x ↦ F x + g₂ x`.
/-- For a two-block dual optimum `y*`, any reduced primal argmax point at `y₂*` is a minimizer of
the reduced primal objective. -/
theorem isMinOn_of_mem_reduced_argmax_of_mem_optimal_set
    (h_problem : IsDualBlockProximalGradientProblem f ![g1, g2] σ)
    {yStar : Fin 2 → E}
    (hyStar : yStar ∈ Λ*(f, ![g1, g2]))
    {xStar : E}
    (hxStar : xStar ∈ dual_proximal_gradient_primal_x_argmax F A (yStar 1)) :
    IsMinOn pRed Set.univ xStar := by
  have hRed :=
    IsDualBlockProximalGradientProblem.toReducedProblem
      (σ := σ)
      (f := f)
      (g1 := g1)
      (g2 := g2)
      h_problem
  obtain ⟨xMin, hxMin⟩ :=
    existsReducedPrimalMinimizer
      (σ := σ)
      (f := f)
      (g1 := g1)
      (g2 := g2)
      h_problem
  have hxMinRed : IsMinOn (composite_model_objective F (g2 ∘ A)) Set.univ xMin := by
    -- Rewrite the reduced primal objective to the identity-map owner expected by Lemma 12.7.
    simpa [Function.comp, composite_model_objective_apply, LinearMap.id_apply] using hxMin
  have hqStar :
      qRed (yStar 1) = qRedOpt :=
    reduced_dual_eq_problem_value_of_mem_optimal_set
      (σ := σ)
      (f := f)
      (g1 := g1)
      (g2 := g2)
      h_problem
      hyStar
  have hgap :
      ((((σ : ℝ) / 2) * ‖xStar - xMin‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        qRedOpt - qRed (yStar 1) := by
    -- Apply the reduced-owner dual-gap domination exactly at the optimal second block.
    simpa [Function.comp, composite_model_objective_apply, LinearMap.id_apply] using
      (dualGap_dominates_halfSigmaSqdist_of_primalArgmax
        (f := F)
        (g := g2)
        A
        σ
        hRed
        (yStar 1)
        xStar
        xMin
        hxStar
        hxMinRed)
  have hgap_zero :
      ((((σ : ℝ) / 2) * ‖xStar - xMin‖ ^ (2 : ℕ) : ℝ) : EReal) ≤ 0 := by
    have hself_le : qRedOpt - qRed (yStar 1) ≤ 0 := by
      rw [hqStar]
      exact EReal.sub_self_le_zero
    exact hgap.trans hself_le
  have hsq_le_zero :
      ((σ : ℝ) / 2) * ‖xStar - xMin‖ ^ (2 : ℕ) ≤ 0 := by
    exact EReal.coe_le_coe_iff.mp (by simpa using hgap_zero)
  have hnorm_sq_zero : ‖xStar - xMin‖ ^ (2 : ℕ) = 0 := by
    have hσ_half_pos : 0 < (σ : ℝ) / 2 := by
      exact div_pos σ.2 (by norm_num)
    have hσ_half_nonneg : 0 ≤ (σ : ℝ) / 2 := le_of_lt hσ_half_pos
    have hnorm_sq_nonneg : 0 ≤ ‖xStar - xMin‖ ^ (2 : ℕ) := by
      positivity
    have hmul_nonneg : 0 ≤ ((σ : ℝ) / 2) * ‖xStar - xMin‖ ^ (2 : ℕ) := by
      exact mul_nonneg hσ_half_nonneg hnorm_sq_nonneg
    have hmul_eq_zero : ((σ : ℝ) / 2) * ‖xStar - xMin‖ ^ (2 : ℕ) = 0 := by
      exact le_antisymm hsq_le_zero hmul_nonneg
    have hσ_half_ne : (σ : ℝ) / 2 ≠ 0 := ne_of_gt hσ_half_pos
    exact (mul_eq_zero.mp hmul_eq_zero).resolve_left hσ_half_ne
  have hnorm_zero : ‖xStar - xMin‖ = 0 := by
    have hsq : ‖xStar - xMin‖ * ‖xStar - xMin‖ = 0 := by
      simpa [pow_two] using hnorm_sq_zero
    exact mul_self_eq_zero.mp hsq
  have hx_eq : xStar = xMin := by
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)
  -- Once the reduced gap vanishes, the argmax witness coincides with the global minimizer.
  simpa [hx_eq] using hxMin

/- The reduced accelerated endgame separates into two layers:
1. a reduced dual-gap estimate; and
2. the routine conversion from that gap estimate to the primal squared-distance bound.

The second layer is independent of the missing accelerated reduced-gap API, so we prove it now and
leave only that genuine accelerated-rate premise unresolved. -/
/-- Helper for Theorem 12.19: on the reduced owner, any `O(1 / k^2)` bound on the reduced dual
gap yields the corresponding primal squared-distance estimate. -/
private lemma fastReducedPrimalSqdist_le_of_dualGapRate
    (hRed : IsDualBasedProximalGradientProblem F g2 A σ)
    (y0 : E) (x y : ℕ → E)
    (hx : ∀ k : ℕ, x k ∈ dual_proximal_gradient_primal_x_argmax F A (y k))
    (xStar : E)
    (hxStarRed : IsMinOn (composite_model_objective F (g2 ∘ A)) Set.univ xStar)
    (yStar : E)
    (k : ℕ)
    (hgapRate :
      qRedOpt - qRed (y k) ≤
        ((2 * ((σ : ℝ)⁻¹) * ‖y0 - yStar‖ ^ (2 : ℕ) /
            ((k + 1 : ℝ) ^ (2 : ℕ)) : ℝ) : EReal)) :
    ‖x k - xStar‖ ^ (2 : ℕ) ≤
      4 * ‖y0 - yStar‖ ^ (2 : ℕ) /
        (((σ : ℝ) ^ (2 : ℕ)) * ((k + 1 : ℝ) ^ (2 : ℕ))) := by
  have hhalf_gap :
      ((((σ : ℝ) / 2) * ‖x k - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        qRedOpt - qRed (y k) := by
    -- Apply the reduced Chapter 12 primal-distance-to-gap estimate at the current iterate.
    simpa [Function.comp, composite_model_objective_apply, LinearMap.id_apply] using
      (dualGap_dominates_halfSigmaSqdist_of_primalArgmax
        F
        g2
        A
        σ
        hRed
        (y k)
        (x k)
        xStar
        (hx k)
        hxStarRed)
  have hbound_ereal :
      ((((σ : ℝ) / 2) * ‖x k - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        ((2 * ((σ : ℝ)⁻¹) * ‖y0 - yStar‖ ^ (2 : ℕ) /
            ((k + 1 : ℝ) ^ (2 : ℕ)) : ℝ) : EReal) :=
    le_trans hhalf_gap hgapRate
  have hbound_real :
      ((σ : ℝ) / 2) * ‖x k - xStar‖ ^ (2 : ℕ) ≤
        2 * ((σ : ℝ)⁻¹) * ‖y0 - yStar‖ ^ (2 : ℕ) /
          ((k + 1 : ℝ) ^ (2 : ℕ)) := by
    exact EReal.coe_le_coe_iff.mp hbound_ereal
  have hσ_pos : 0 < (σ : ℝ) := σ.2
  have hden_pos : 0 < ((k + 1 : ℝ) ^ (2 : ℕ)) := by
    positivity
  have hmul :
      (((σ : ℝ) / 2) * ‖x k - xStar‖ ^ (2 : ℕ)) *
          ((k + 1 : ℝ) ^ (2 : ℕ)) ≤
        2 * ((σ : ℝ)⁻¹) * ‖y0 - yStar‖ ^ (2 : ℕ) := by
    -- Clear the positive denominator `(k + 1)^2`.
    exact (le_div_iff₀ hden_pos).mp hbound_real
  have hscaled :
      (σ : ℝ) * ‖x k - xStar‖ ^ (2 : ℕ) * ((k + 1 : ℝ) ^ (2 : ℕ)) ≤
        4 * ((σ : ℝ)⁻¹) * ‖y0 - yStar‖ ^ (2 : ℕ) := by
    -- Normalize the factor `(σ / 2)` on the left.
    nlinarith
  have hσ0 : (σ : ℝ) ≠ 0 := ne_of_gt hσ_pos
  have hscaled' :
      ((σ : ℝ) ^ (2 : ℕ)) * ‖x k - xStar‖ ^ (2 : ℕ) * ((k + 1 : ℝ) ^ (2 : ℕ)) ≤
        4 * ‖y0 - yStar‖ ^ (2 : ℕ) := by
    have hmulσ :
        (σ : ℝ) * ((σ : ℝ) * ‖x k - xStar‖ ^ (2 : ℕ) * ((k + 1 : ℝ) ^ (2 : ℕ))) ≤
          (σ : ℝ) * (4 * ((σ : ℝ)⁻¹) * ‖y0 - yStar‖ ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hscaled hσ_pos.le
    calc
      ((σ : ℝ) ^ (2 : ℕ)) * ‖x k - xStar‖ ^ (2 : ℕ) * ((k + 1 : ℝ) ^ (2 : ℕ))
          = (σ : ℝ) * ((σ : ℝ) * ‖x k - xStar‖ ^ (2 : ℕ) * ((k + 1 : ℝ) ^ (2 : ℕ))) := by
              ring
      _ ≤ (σ : ℝ) * (4 * ((σ : ℝ)⁻¹) * ‖y0 - yStar‖ ^ (2 : ℕ)) := hmulσ
      _ = 4 * ‖y0 - yStar‖ ^ (2 : ℕ) := by
            field_simp [hσ0]
  have htotal_pos :
      0 < ((σ : ℝ) ^ (2 : ℕ)) * ((k + 1 : ℝ) ^ (2 : ℕ)) := by
    positivity
  -- Cancel the positive denominator to recover the reduced primal-distance estimate.
  exact
    (le_div_iff₀ htotal_pos).2 <| by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hscaled'

/-- Helper for Theorem 12.19: the source momentum sequence in the reduced accelerated trajectory
agrees with the canonical FISTA momentum sequence. -/
private lemma fastReducedMomentum_eqCanonical
    {y0 : E} {u : ℕ → E} {y w : ℕ → E} {t : ℕ → ℝ}
    (htraj : IsFastDualProximalGradientPrimalTrajectory F g2 A σ L y0 u y w t) :
    ∀ n : ℕ, t n = fista_momentum_sequence n := by
  intro n
  induction n with
  | zero =>
      -- Both owners initialize the momentum parameter at `1`.
      simpa using htraj.t_zero
  | succ n ih =>
      -- The reduced trajectory stores exactly the canonical FISTA recursion.
      simpa [ih, fista_momentum_sequence_succ] using htraj.acceleration_step n

/-- Helper for Theorem 12.19: the reduced dual smooth term is finite at every dual point. -/
private lemma reducedDualMinimizationViewSmoothTerm_finite
    (hRed : IsDualBasedProximalGradientProblem F g2 A σ)
    (z : E) :
    FRedDual z ≠ ⊥ ∧ FRedDual z < ⊤ := by
  -- This is the standard Chapter 12 finiteness theorem specialized to the reduced owner.
  simpa [LinearMap.adjoint_id] using
    (dual_based_proximal_gradient_dual_F_primal_finite_valued
      σ F (LinearMap.id : E →ₗ[ℝ] E))
      hRed.toIsProperExtendedRealFunction
      hRed.f_closed
      hRed.f_strongly_convex
      z

/-- Helper for Theorem 12.19: coercing the finite reduced smooth term to `ℝ` and back recovers
its original value. -/
private lemma reducedDualMinimizationViewSmoothTerm_coeToReal
    (hRed : IsDualBasedProximalGradientProblem F g2 A σ)
    (z : E) :
    (((FRedDual z).toReal : ℝ) : EReal) = FRedDual z := by
  have hz :=
    reducedDualMinimizationViewSmoothTerm_finite
      (σ := σ)
      (f := f)
      (g1 := g1)
      (g2 := g2)
      hRed
      z
  -- Finiteness of the reduced smooth term justifies the `toReal`/`coe` round-trip.
  exact EReal.coe_toReal (lt_top_iff_ne_top.mp hz.2) hz.1

/-- Helper for Theorem 12.19: replacing the reduced smooth term by its real lift does not change
the minimization-view objective. -/
private lemma reducedDualMinimizationViewObjective_eq_realLift
    (hRed : IsDualBasedProximalGradientProblem F g2 A σ) :
    composite_model_objective (Function.toEReal fun z : E ↦ (FRedDual z).toReal) GRedDual =
      composite_model_objective FRedDual GRedDual := by
  funext z
  -- Pointwise, only the smooth term changes, and that change is exactly the finite-value coercion.
  simpa [Function.toEReal] using
    congrArg
      (fun t : EReal ↦ t + GRedDual z)
      (reducedDualMinimizationViewSmoothTerm_coeToReal
        (σ := σ)
        (f := f)
        (g1 := g1)
        (g2 := g2)
        hRed
        z)

/-- Helper for Theorem 12.19: the reduced dual optimum is finite above once an optimal witness is
fixed. -/
private lemma reducedDualProblemValue_ne_top_of_optimal
    (hRed : IsDualBasedProximalGradientProblem F g2 A σ)
    (yStar : E)
    (hqStar : qRed yStar = qRedOpt) :
    qRedOpt ≠ ⊤ := by
  -- Evaluate the reduced optimal witness itself to rule out `+∞`.
  rw [← hqStar]
  exact
    dualObjective_ne_top
      (f := F)
      (g := g2)
      (LinearMap.id : E →ₗ[ℝ] E)
      σ
      hRed.toIsProperExtendedRealFunction
      hRed.f_closed
      hRed.f_strongly_convex
      hRed.g_proper
      hRed.g_convex
      yStar

/-- Helper for Theorem 12.19: the reduced dual problem value is finite below. -/
private lemma reducedDualProblemValue_ne_bot
    (hRed : IsDualBasedProximalGradientProblem F g2 A σ) :
    qRedOpt ≠ ⊥ := by
  rcases
      exists_dualObjective_ne_bot
        (f := F)
        (g := g2)
        (LinearMap.id : E →ₗ[ℝ] E)
        σ
        hRed.toIsProperExtendedRealFunction
        hRed.f_closed
        hRed.f_strongly_convex
        hRed.g_proper
        hRed.g_convex with
    ⟨yBar, hyBar⟩
  have hyBar_le : qRed yBar ≤ qRedOpt :=
    dualObjective_le_dualProblemValue
      (f := F)
      (g := g2)
      (LinearMap.id : E →ₗ[ℝ] E)
      yBar
  intro hqRedOpt_bot
  rw [hqRedOpt_bot] at hyBar_le
  exact hyBar (le_bot_iff.mp hyBar_le)

/-- Helper for Theorem 12.19: coercing the finite reduced dual optimum to `ℝ` and back gives the
displayed negative optimal value in the minimization view. -/
private lemma reducedNegToRealDualProblemValue_eq
    (hRed : IsDualBasedProximalGradientProblem F g2 A σ)
    (yStar : E)
    (hqStar : qRed yStar = qRedOpt) :
    (((-EReal.toReal qRedOpt : ℝ)) : EReal) = -qRedOpt := by
  have hqRedOpt_ne_top :=
    reducedDualProblemValue_ne_top_of_optimal (σ := σ) (f := f) (g1 := g1) (g2 := g2)
      hRed yStar hqStar
  have hqRedOpt_ne_bot :=
    reducedDualProblemValue_ne_bot (σ := σ) (f := f) (g1 := g1) (g2 := g2) hRed
  -- Coerce the finite reduced optimal value to `ℝ`, then negate the resulting equality.
  simpa using congrArg Neg.neg (EReal.coe_toReal hqRedOpt_ne_top hqRedOpt_ne_bot)

/-- Helper for Theorem 12.19: on the reduced owner, the displayed dual gap is exactly the
minimization-view composite gap. -/
private lemma reducedDualObjectiveGap_eq_compositeGap
    (hRed : IsDualBasedProximalGradientProblem F g2 A σ)
    (y : ℕ → E)
    (yStar : E)
    (hqStar : qRed yStar = qRedOpt)
    (k : ℕ) :
    qRedOpt - qRed (y k) =
      composite_model_objective FRedDual GRedDual (y k) -
        (((-EReal.toReal qRedOpt : ℝ)) : EReal) := by
  have hneg_qRedOpt_coe :=
    reducedNegToRealDualProblemValue_eq
      (σ := σ)
      (f := f)
      (g1 := g1)
      (g2 := g2)
      hRed
      yStar
      hqStar
  -- Rewrite the reduced minimization view to `-qRed` and simplify the resulting subtraction.
  rw [dualCompositeObjective_eq_negDualObjective
      (f := F)
      (g := g2)
      (LinearMap.id : E →ₗ[ℝ] E)
      σ
      hRed.toIsProperExtendedRealFunction
      hRed.f_closed
      hRed.f_strongly_convex
      hRed.g_proper
      hRed.g_convex
      (y k),
    hneg_qRedOpt_coe]
  simp [sub_eq_add_neg, add_comm]

/-- Helper for Theorem 12.19: any reduced minimization-view composite-gap bound immediately
yields the displayed reduced dual-gap bound. -/
private lemma reducedDualObjectiveGapLe_ofCompositeGapLe
    (hRed : IsDualBasedProximalGradientProblem F g2 A σ)
    (y : ℕ → E)
    (yStar : E)
    (hqStar : qRed yStar = qRedOpt)
    (k : ℕ)
    {rhs : EReal}
    (hgap :
      composite_model_objective FRedDual GRedDual (y k) -
          (((-EReal.toReal qRedOpt : ℝ)) : EReal) ≤ rhs) :
    qRedOpt - qRed (y k) ≤ rhs := by
  rw [reducedDualObjectiveGap_eq_compositeGap
      (σ := σ)
      (f := f)
      (g1 := g1)
      (g2 := g2)
      hRed
      y
      yStar
      hqStar
      k]
  exact hgap

/-- Helper for Theorem 12.19: rewrite a reduced real-lift minimization-view gap estimate to the
literal reduced composite objective surface. -/
private lemma reducedCompositeGapLe_ofRealLiftGapLe
    (hRed : IsDualBasedProximalGradientProblem F g2 A σ)
    (y : ℕ → E)
    (k : ℕ)
    {rhs : EReal}
    (hgap :
      composite_model_objective
          (Function.toEReal fun z : E ↦ (FRedDual z).toReal)
          GRedDual
          (y k) -
        (((-EReal.toReal qRedOpt : ℝ)) : EReal) ≤ rhs) :
    composite_model_objective FRedDual GRedDual (y k) -
        (((-EReal.toReal qRedOpt : ℝ)) : EReal) ≤ rhs := by
  -- Rewrite only the objective surface; the rate bound itself is unchanged.
  rw [← reducedDualMinimizationViewObjective_eq_realLift
      (σ := σ)
      (f := f)
      (g1 := g1)
      (g2 := g2)
      hRed]
  exact hgap

/-- Helper for Theorem 12.19: the reduced primal `y`-step is exactly the canonical reduced dual
step once the primal argmax witness is rewritten as the conjugate gradient point. -/
private lemma reducedDualTrajectoryDualStep_ofPrimalStep
    (hRed : IsDualBasedProximalGradientProblem F g2 A σ)
    {y w : ℕ → E} {k : ℕ}
    (hy_step :
      y (k + 1) ∈
        dual_proximal_gradient_primal_y_step
          g2
          A
          (∇ (fun z : E ↦ ((F∗) z).toReal) (w k))
          (w k)
          (L : PosReal)) :
    y (k + 1) ∈
      dual_based_proximal_gradient_dual_step
        (fun z : E ↦ (g2∗) (-z))
        (fun z ↦ ∇ (fun z' : E ↦ ((F∗) z').toReal) z)
        (L : PosReal)
        (w k) := by
  -- Reuse the zero-shift owner equivalence from Theorem 12.8 on the reduced owner.
  simpa using
    (dualBasedDualStep_iff_memDualPrimalYStepZeroShift
      (f := F)
      (g := g2)
      A
      hRed
      (y (k + 1))
      (w k)
      (L : PosReal)).2
      (by simpa [LinearMap.adjoint_id] using hy_step)

/-- Helper for Theorem 12.19: every reduced primal-trajectory dual step is the canonical reduced
dual step at the same extrapolated point. -/
private lemma reducedFastDualTrajectory_dualStep
    (hRed : IsDualBasedProximalGradientProblem F g2 A σ)
    {y0 : E} {u : ℕ → E} {y w : ℕ → E} {t : ℕ → ℝ}
    (htraj : IsFastDualProximalGradientPrimalTrajectory F g2 A σ L y0 u y w t)
    (k : ℕ) :
    y (k + 1) ∈
      dual_based_proximal_gradient_dual_step
        (fun z : E ↦ (g2∗) (-z))
        (fun z ↦ ∇ (fun z' : E ↦ ((F∗) z').toReal) z)
        (L : PosReal)
        (w k) := by
  have huk_eq :
      u k = ∇ (fun z : E ↦ ((F∗) z).toReal) (w k) := by
    -- Rewrite the stored reduced argmax point to the canonical conjugate-gradient owner.
    simpa [LinearMap.adjoint_id] using
      dualPrimalArgmax_eqConjugateGradient
        (f := F)
        (g := g2)
        A
        hRed
        (htraj.primal_step k)
  have hy_step :
      y (k + 1) ∈
        dual_proximal_gradient_primal_y_step
          g2
          A
          (∇ (fun z : E ↦ ((F∗) z).toReal) (w k))
          (w k)
          (L : PosReal) := by
    -- The primal trajectory already stores the correct reduced `y`-step after that rewrite.
    simpa [huk_eq] using htraj.dual_step k
  exact
    reducedDualTrajectoryDualStep_ofPrimalStep
      (σ := σ)
      (f := f)
      (g1 := g1)
      (g2 := g2)
      hRed
      hy_step

/-- Helper for Theorem 12.19: the reduced accelerated primal trajectory canonically induces the
reduced accelerated dual trajectory used by the shifted-owner rate proof. -/
private lemma reducedPrimalTrajectory_toDualTrajectory
    (hRed : IsDualBasedProximalGradientProblem F g2 A σ)
    {y0 : E} {u : ℕ → E} {y w : ℕ → E} {t : ℕ → ℝ}
    (htraj : IsFastDualProximalGradientPrimalTrajectory F g2 A σ L y0 u y w t) :
    IsFastDualProximalGradientDualTrajectory
      ((LinearMap.id : E →ₗ[ℝ] E).toContinuousLinearMap)
      σ
      GRedDual
      gradFRed
      L
      y0
      y
      w := by
  let Gexp : E → EReal := fun z : E ↦ (g2∗) (-z)
  let gradFexp : E → E := fun z ↦ ∇ (fun z' : E ↦ ((F∗) z').toReal) z
  have hG_eq : GRedDual = Gexp := by
    -- The reduced nonsmooth dual term is exactly the negated conjugate owner.
    funext z
    change dual_based_proximal_gradient_dual_G_term g2 (InnerProductSpace.toDualMap ℝ E z) =
      (g2∗) (-z)
    simpa using dual_based_proximal_gradient_dual_G_primal_apply (g := g2) (y := z)
  have hgrad_eq : gradFRed = gradFexp := by
    have hFreal_eq :
        (fun z' : E ↦
          (dual_based_proximal_gradient_dual_F_term F A
            (InnerProductSpace.toDualMap ℝ E z')).toReal) =
          (fun z' : E ↦ ((F∗) z').toReal) := by
      -- The reduced smooth dual term is `F*(Aᵀ z)` pointwise.
      funext z'
      simpa [LinearMap.adjoint_id] using
        congrArg EReal.toReal <|
          dual_based_proximal_gradient_dual_F_primal_apply
            (f := F)
            z'
    -- Apply that pointwise identification under the gradient operator.
    funext z
    exact congrArg (fun φ : E → ℝ ↦ ∇ φ z) hFreal_eq
  have hexp :
      IsFastDualProximalGradientDualTrajectory
        ((LinearMap.id : E →ₗ[ℝ] E).toContinuousLinearMap)
        σ
        Gexp
        gradFexp
        L
        y0
        y
        w := by
    -- Use the Algorithm 12.3 source-form companion so the induced dual trajectory stays on the
    -- canonical public owner.
    exact
      IsFastDualProximalGradientDualTrajectory.ofSourceMomentum
        htraj.y_zero
        htraj.w_zero
        (fun k ↦ by
          change
            y (k + 1) ∈
              dual_based_proximal_gradient_dual_step
                (fun z : E ↦ (g2∗) (-z))
                (fun z ↦ ∇ (fun z' : E ↦ ((F∗) z').toReal) z)
                (L : PosReal)
                (w k)
          exact
            reducedFastDualTrajectory_dualStep
              (σ := σ)
              (f := f)
              (g1 := g1)
              (g2 := g2)
              hRed
              htraj
              k)
        (fun k ↦ by
          -- Normalize the stored momentum sequence to the canonical FISTA owner.
          simpa [fastReducedMomentum_eqCanonical (σ := σ) (f := f) (g1 := g1) (g2 := g2) htraj k,
            fastReducedMomentum_eqCanonical (σ := σ) (f := f) (g1 := g1) (g2 := g2)
              htraj (k + 1)] using
            htraj.momentum_step k)
  rw [hG_eq, hgrad_eq]
  exact hexp



-- Proof sketch: first use Assumption 12.14 with `p = 2` to view ADBPG as accelerated dual
-- proximal gradient on the reduced problem with primal term `F = f + g₁`.
-- Then transport the two-block optimality witness to the reduced minimization view, apply the
-- accelerated reduced dual-gap estimate from Theorem 12.9 at `A = id` and `L = 1 / σ`, and
-- finish with the local reduced gap-to-distance conversion.
/-- Theorem 12.19: under Assumption 12.14 with two blocks, if the reduced accelerated
dual-proximal-gradient trajectory represents the ADBPG iterates and `x^k` is chosen from
`argmax_x {⟪x, y^k⟫ - f(x) - g₁(x)}` for each current dual iterate `y^k`, then for any optimal
two-block dual solution `y* = (y₁*, y₂*) ∈ Λ*(f, ![g₁, g₂])` and any associated reduced primal
argmax point `x* ∈ argmax_x {⟪x, y₂*⟫ - f(x) - g₁(x)}`, every positive iterate satisfies
`‖x^k - x*‖² ≤ 4 ‖y^0 - y₂*‖² / (σ² (k + 1)²)`. -/
theorem accelerated_dual_block_proximal_gradient_primal_sqdist_le
    (h_problem : IsDualBlockProximalGradientProblem f ![g1, g2] σ)
    (y0 : E) (u x : ℕ → E) (y w : ℕ → E) (t : ℕ → ℝ)
    (htraj : IsFastDualProximalGradientPrimalTrajectory F g2 A σ L y0 u y w t)
    (hx : ∀ k : ℕ, x k ∈ dual_proximal_gradient_primal_x_argmax F A (y k))
    (yStar : Fin 2 → E)
    (hyStar : yStar ∈ Λ*(f, ![g1, g2]))
    (xStar : E)
    (hxStar : xStar ∈ dual_proximal_gradient_primal_x_argmax F A (yStar 1))
    (k : ℕ) (hk : 1 ≤ k) :
    ‖x k - xStar‖ ^ (2 : ℕ) ≤
      4 * ‖y0 - yStar 1‖ ^ (2 : ℕ) /
        (((σ : ℝ) ^ (2 : ℕ)) * ((k + 1 : ℝ) ^ (2 : ℕ))) := by
  have hRed :=
    IsDualBlockProximalGradientProblem.toReducedProblem
      (σ := σ)
      (f := f)
      (g1 := g1)
      (g2 := g2)
      h_problem
  have hxStarMin : IsMinOn pRed Set.univ xStar :=
    isMinOn_of_mem_reduced_argmax_of_mem_optimal_set
      (σ := σ)
      (f := f)
      (g1 := g1)
      (g2 := g2)
      h_problem
      hyStar
      hxStar
  have hxStarRed : IsMinOn (composite_model_objective F (g2 ∘ A)) Set.univ xStar := by
    -- Rewrite the reduced owner surface back to the local notation `pRed`.
    simpa [Function.comp, composite_model_objective_apply, LinearMap.id_apply] using hxStarMin
  have hqStar :
      qRed (yStar 1) = qRedOpt :=
    reduced_dual_eq_problem_value_of_mem_optimal_set
      (σ := σ)
      (f := f)
      (g1 := g1)
      (g2 := g2)
      h_problem
      hyStar
  have hgapDual :
      qRedOpt - qRed (y k) ≤
        ((2 * ((σ : ℝ)⁻¹) * ‖y0 - yStar 1‖ ^ (2 : ℕ) /
            ((k + 1 : ℝ) ^ (2 : ℕ) : ℝ) : ℝ) : EReal) := by
    -- Apply the accelerated reduced dual-gap estimate from Theorem 12.9.
    have hgapDual' :
        qRedOpt - qRed (y k) ≤
          ((2 * ((L : PosReal) : ℝ) * ‖y0 - yStar 1‖ ^ (2 : ℕ) /
              ((k + 1 : ℝ) ^ (2 : ℕ) : ℝ) : ℝ) : EReal) :=
      fast_dual_proximal_gradient_dual_objective_gap_le
        F
        g2
        A
        σ
        L
        hRed
        y0
        u
        y
        w
        t
        htraj
        (yStar 1)
        hqStar
        k
        hk
    simpa [dual_based_proximal_gradient_identity_stepsize_parameter] using
      hgapDual'
  exact
    fastReducedPrimalSqdist_le_of_dualGapRate
      (σ := σ)
      (f := f)
      (g1 := g1)
      (g2 := g2)
      hRed
      y0
      x
      y
      hx
      xStar
      hxStarRed
      (yStar 1)
      k
      hgapDual

end

end

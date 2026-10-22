/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_13
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Lemma_5_7
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_5
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_9
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Algorithm_14_8
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Algorithm_14_8.PairBridge

-- Theorem-local helpers for Lemma 14.4.
-- Semantic recall: the valid Chapter 14 route is to descend first to the current-fiber partial
-- infimum and only then pass back to support on the fixed `xStar` fiber. This support file keeps
-- only the source-facing objective-gap owners and leaves that canonical bridge to the existing
-- Chapter 14 partial-infimum/pair-support API.

noncomputable section

universe u

open scoped Gradient
open InnerProductSpace (toDual)

section

variable {E1 : Type u} {E2 : Type u}
variable [NormedAddCommGroup E1] [NormedAddCommGroup E2]

section TrajectoryHelpers

variable (f : E1 × E2 → ℝ) (g1 : E1 → EReal) (g2 : E2 → EReal)
variable (x1 : ℕ → E1) (x2 : ℕ → E2)

local notation "F" => two_block_alternating_minimization_objective f.toEReal g1 g2
local notation "x[" k "]" => (x1 k, x2 k)
local notation "xHalf[" k "]" => two_block_alternating_minimization_half_step x1 x2 k

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: the current second block is always an
exact minimizer of the current `x₂`-subproblem. -/
lemma twoBlockCurrentX2ObjectiveIsMinOn
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (n : ℕ) :
    IsMinOn
      (two_block_alternating_minimization_x2_objective f.toEReal g1 g2 (x1 n))
      Set.univ
      (x2 n) := by
  -- Split off the initialization clause from the recursive update clause.
  cases n with
  | zero =>
      simpa using htraj.initial
  | succ n =>
      simpa [Nat.succ_eq_add_one] using htraj.step_x2 n

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: every outer iterate of the two-block
trajectory remains in `effective_domain F`, and the full objective never exceeds its initial
value. -/
lemma twoBlockIteratesMemEffectiveDomainAndInitialSublevel
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F) :
    ∀ n : ℕ, x[n] ∈ effective_domain F ∧ F x[n] ≤ F x[0] := by
  intro n
  induction n with
  | zero =>
      -- The base iterate is finite by the explicit initialization hypothesis.
      exact ⟨hx0, le_rfl⟩
  | succ n ihn =>
      rcases ihn with ⟨hxn_mem, hxn_le⟩
      have hhalf_step :
          IsMinOn
            (two_block_alternating_minimization_x1_objective f.toEReal g1 g2 (x2 n))
            Set.univ
            (x1 (n + 1)) := htraj.step_x1 n
      have hhalf_le : F xHalf[n] ≤ F x[n] := by
        -- Compare the exact first-block minimizer with the current first block as a candidate.
        simpa [two_block_alternating_minimization_half_step,
          two_block_alternating_minimization_objective_apply] using
          (isMinOn_iff.mp hhalf_step) (x1 n) (by simp)
      have hhalf_mem : xHalf[n] ∈ effective_domain F := by
        -- A value below the finite current iterate is still finite.
        exact mem_effective_domain.mpr <|
          lt_of_le_of_lt hhalf_le (mem_effective_domain.mp hxn_mem)
      have hnext_step :
          IsMinOn
            (two_block_alternating_minimization_x2_objective f.toEReal g1 g2 (x1 (n + 1)))
            Set.univ
            (x2 (n + 1)) := htraj.step_x2 n
      have hnext_le : F x[n + 1] ≤ F xHalf[n] := by
        -- Then compare the exact second-block minimizer with the old second block.
        simpa [two_block_alternating_minimization_half_step,
          two_block_alternating_minimization_objective_apply] using
          (isMinOn_iff.mp hnext_step) (x2 n) (by simp)
      have hnext_mem : x[n + 1] ∈ effective_domain F := by
        -- The same finite-value argument upgrades the half-step to the next iterate.
        exact mem_effective_domain.mpr <|
          lt_of_le_of_lt hnext_le (mem_effective_domain.mp hhalf_mem)
      exact ⟨hnext_mem, le_trans hnext_le (le_trans hhalf_le hxn_le)⟩

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: the intermediate half-step
`x^{k+1/2} = (x₁^{k+1}, x₂^k)` is finite and lies below the initial objective level. -/
lemma twoBlockHalfStepMemEffectiveDomainAndInitialSublevel
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : x[0] ∈ effective_domain F)
    (n : ℕ) :
    xHalf[n] ∈ effective_domain F ∧ F xHalf[n] ≤ F x[0] := by
  have hxn :=
    twoBlockIteratesMemEffectiveDomainAndInitialSublevel
      f g1 g2 x1 x2 htraj hx0 n
  rcases hxn with ⟨hxn_mem, hxn_le⟩
  have hhalf_step :
      IsMinOn
        (two_block_alternating_minimization_x1_objective f.toEReal g1 g2 (x2 n))
        Set.univ
        (x1 (n + 1)) := htraj.step_x1 n
  have hhalf_le : F xHalf[n] ≤ F x[n] := by
    -- Compare the exact first-block minimizer with the current first block once.
    simpa [two_block_alternating_minimization_half_step,
      two_block_alternating_minimization_objective_apply] using
      (isMinOn_iff.mp hhalf_step) (x1 n) (by simp)
  have hhalf_mem : xHalf[n] ∈ effective_domain F := by
    -- The intermediate objective is finite because it is no larger than the current iterate.
    exact mem_effective_domain.mpr <|
      lt_of_le_of_lt hhalf_le (mem_effective_domain.mp hxn_mem)
  exact ⟨hhalf_mem, le_trans hhalf_le hxn_le⟩

end TrajectoryHelpers

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: a convex differentiable real-valued
function on `Set.univ` satisfies the first-order support inequality in `fderiv` form. -/
lemma convexRealSupportUnivFDeriv
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℝ} {x y : E}
    (hφ_convex : ConvexOn ℝ Set.univ φ)
    (hφ_diff : DifferentiableAt ℝ φ x) :
    φ y ≥ φ x + fderiv ℝ φ x (y - x) := by
  let line : ℝ → E := AffineMap.lineMap x y
  let ψ : ℝ → ℝ := fun t ↦ φ (line t)
  have hψ_convex : ConvexOn ℝ Set.univ ψ := by
    -- Restrict the ambient convex function to the affine line through `x` and `y`.
    simpa [ψ, line] using
      hφ_convex.comp_affineMap (AffineMap.lineMap x y)
  have hψ_deriv : HasDerivAt ψ (fderiv ℝ φ x (y - x)) 0 := by
    -- Differentiate the line restriction at the base point and identify the direction `y - x`.
    have hbase : HasFDerivAt φ (fderiv ℝ φ x) (line 0) := by
      simpa [line] using hφ_diff.hasFDerivAt
    have hline : HasDerivAt line (y - x) 0 := by
      simpa [line] using
        (show HasDerivAt (AffineMap.lineMap x y) (y - x) (0 : ℝ) from
          AffineMap.hasDerivAt_lineMap)
    simpa [ψ, line] using HasFDerivAt.comp_hasDerivAt 0 hbase hline
  have hsecant :
      fderiv ℝ φ x (y - x) ≤ slope ψ 0 1 := by
    -- Convexity bounds the derivative at the left endpoint by the secant slope.
    exact hψ_convex.le_slope_of_hasDerivAt (by simp) (by simp) zero_lt_one hψ_deriv
  have hsecant' :
      fderiv ℝ φ x (y - x) ≤ φ y - φ x := by
    simpa [ψ, line, slope] using hsecant
  linarith

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: once a supporting affine lower bound is
known for every point in a fixed target fiber, the same bound descends to the corresponding
partial infimum. -/
lemma partialInfimumSupportAtFixedPointOfAttainedPairSupport
    {E : Type u} {V : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (H : E × V → EReal) (x0 : E) (v0 : V) (y : E) (g : Module.Dual ℝ E)
    (hattained :
      sInf (Set.range (fun v : V ↦ H (x0, v))) = H (x0, v0))
    (hsupport :
      ∀ v : V, H (y, v) ≥ H (x0, v0) + (g (y - x0) : EReal)) :
    sInf (Set.range (fun v : V ↦ H (y, v))) ≥
      sInf (Set.range (fun v : V ↦ H (x0, v))) + (g (y - x0) : EReal) := by
  -- Rewrite the base fiber through its attained minimizer before checking the affine lower bound
  -- pointwise on the fixed competitor fiber.
  rw [hattained]
  refine le_sInf ?_
  rintro _ ⟨v, rfl⟩
  exact hsupport v

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: if a convex extended-real-valued function
is touched from above at `x0` by a convex differentiable real-valued majorant, then the gradient
of that majorant supports the convex function at every comparison point. -/
lemma convexContactSupportAtTouchedConvexMajorant
    {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
    {eta : E → EReal} {chi : E → ℝ} {x0 y : E}
    (heta_convex : is_convex_function eta)
    (hchi_convex : ConvexOn ℝ Set.univ chi)
    (heta_le_chi : ∀ x : E, eta x ≤ (chi x : EReal))
    (hcontact : eta x0 = (chi x0 : EReal))
    (hchi_diff : DifferentiableAt ℝ chi x0) :
    eta y ≥ eta x0 + (inner ℝ (∇ chi x0) (y - x0) : EReal) := by
  let chiE : E → EReal := fun x ↦ (chi x : EReal)
  letI : FiniteDimensional ℝ E := FiniteDimensional.of_locallyCompactSpace ℝ
  have hdom_univ : effective_domain eta = Set.univ := by
    -- A real-valued majorant keeps every point of `eta` finite from above.
    ext x
    constructor
    · intro _
      simp
    · intro _
      refine mem_effective_domain.mpr ?_
      exact lt_of_le_of_lt (heta_le_chi x) (by simp)
  have hx0_int : x0 ∈ interior (effective_domain eta) := by
    -- The majorant finiteness upgrade turns the effective domain into all of `E`.
    simpa [hdom_univ] using (show x0 ∈ interior (Set.univ : Set E) by simp)
  rcases subdifferential_nonempty_at_interior_point eta x0 heta_convex hx0_int with ⟨p, hp_eta⟩
  have hp_chi : p ∈ ∂ chiE(x0) := by
    -- The subgradient of the touched lower function also supports the touching majorant.
    rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain] at hp_eta ⊢
    constructor
    · simp [chiE, effective_domain]
    · intro z hz
      have hz_eta : z ∈ effective_domain eta := by
        simpa [hdom_univ] using hz
      calc
        chiE z ≥ eta z := heta_le_chi z
        _ ≥ eta x0 + (p (z - x0) : EReal) := hp_eta.2 z hz_eta
        _ = chiE x0 + (p (z - x0) : EReal) := by
          rw [hcontact]
  have hchi_convexE : is_convex_function chiE := by
    -- Repackage the real-valued convexity of `chi` through the everywhere-finite coercion.
    refine (is_convex_function_iff_convexOn_toReal (f := chiE) ?_).2 ?_
    · intro x _
      simp [chiE]
    · simpa [chiE, effective_domain] using hchi_convex
  have hchi_diffE : is_differentiable_at chiE x0 := by
    -- Differentiability of the real majorant is exactly the Chapter 3 owner hypothesis.
    simpa [chiE, is_differentiable_at, finite_domain, effective_domain] using hchi_diff
  have hchi_singleton :
      ∂ₛ chiE(x0) = {toDual ℝ E (∇ chi x0)} := by
    simpa [chiE] using
      subdifferential_eq_singleton_gradient_of_differentiableAt
        chiE x0 hchi_convexE hchi_diffE
  have hp_strong : LinearMap.toContinuousLinearMap p ∈ ∂ₛ chiE(x0) := by
    -- Finite dimensionality upgrades the owner subgradient witness to the strong-dual bridge.
    simpa [mem_strongDualSubdifferential] using hp_chi
  have hp_eq :
      LinearMap.toContinuousLinearMap p = toDual ℝ E (∇ chi x0) := by
    -- The convex differentiable majorant has the singleton gradient subdifferential at `x0`.
    simpa [hchi_singleton]
      using hp_strong
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain] at hp_eta
  have hsupport_eta : eta y ≥ eta x0 + (p (y - x0) : EReal) := by
    -- Reuse the original owner-level support inequality for `eta`.
    have hy_eta : y ∈ effective_domain eta := by
      simpa [hdom_univ]
    exact hp_eta.2 y hy_eta
  calc
    eta y ≥ eta x0 + (p (y - x0) : EReal) := hsupport_eta
    _ = eta x0 + (inner ℝ (∇ chi x0) (y - x0) : EReal) := by
      congr 1
      exact
        congrArg (fun t : ℝ ↦ (t : EReal)) <|
          by
            simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using
              congrArg (fun g : StrongDual ℝ E ↦ g (y - x0)) hp_eq

section ObjectiveDomain

variable (f : E1 × E2 → ℝ) (g1 : E1 → EReal) (g2 : E2 → EReal)

local notation "F" => two_block_alternating_minimization_objective f.toEReal g1 g2

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: finiteness of the full objective at a pair
forces finiteness of the first penalty term at the same point. -/
lemma twoBlockFirstPenaltyEqCoeToRealOfMemEffectiveDomain
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    {y : E1 × E2} (hy : y ∈ effective_domain F) :
    (((g1 y.1).toReal : ℝ) : EReal) = g1 y.1 := by
  rcases y with ⟨y1, y2⟩
  have hg1_ne_top : g1 y1 ≠ ⊤ := by
    -- A top-valued first penalty would force the full objective to be `⊤`, contradicting
    -- effective-domain membership.
    intro hg1_top
    have hFy_top : F (y1, y2) = ⊤ := by
      calc
        F (y1, y2) = (((f (y1, y2) : ℝ) : EReal) + ⊤) + g2 y2 := by
          simp [two_block_alternating_minimization_objective_apply, hg1_top]
        _ = ⊤ + g2 y2 := by
          rw [EReal.add_top_of_ne_bot (by simp)]
        _ = ⊤ := by
          rw [EReal.top_add_of_ne_bot (‹IsProperExtendedRealFunction g2›.ne_bot y2)]
    exact (mem_effective_domain.mp hy).ne hFy_top
  exact EReal.coe_toReal hg1_ne_top (‹IsProperExtendedRealFunction g1›.ne_bot y1)

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: finiteness of the full objective at a pair
forces finiteness of the second penalty term at the same point. -/
lemma twoBlockSecondPenaltyEqCoeToRealOfMemEffectiveDomain
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    {y : E1 × E2} (hy : y ∈ effective_domain F) :
    (((g2 y.2).toReal : ℝ) : EReal) = g2 y.2 := by
  rcases y with ⟨y1, y2⟩
  have hg2_ne_top : g2 y2 ≠ ⊤ := by
    -- A top-valued second penalty would also force the full objective to be `⊤`.
    intro hg2_top
    have hFy_top : F (y1, y2) = ⊤ := by
      calc
        F (y1, y2) = (((f (y1, y2) : ℝ) : EReal) + g1 y1) + ⊤ := by
          simp [two_block_alternating_minimization_objective_apply, hg2_top, add_assoc]
        _ = ⊤ := by
          have hleft_ne_bot :
              (((f (y1, y2) : ℝ) : EReal) + g1 y1) ≠ ⊥ := by
            exact (EReal.add_ne_bot_iff).2 ⟨by simp, ‹IsProperExtendedRealFunction g1›.ne_bot y1⟩
          rw [EReal.add_top_of_ne_bot hleft_ne_bot]
    exact (mem_effective_domain.mp hy).ne hFy_top
  exact EReal.coe_toReal hg2_ne_top (‹IsProperExtendedRealFunction g2›.ne_bot y2)

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: finiteness of the full objective at a pair
puts the first penalty term in its effective domain. -/
lemma twoBlockFirstPenaltyMemEffectiveDomainOfObjectiveMem
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    {y : E1 × E2} (hy : y ∈ effective_domain F) :
    y.1 ∈ effective_domain g1 := by
  -- Rewrite `g₁(y₁)` through its finite real value coming from the full objective.
  refine mem_effective_domain.mpr <| lt_top_iff_ne_top.mpr ?_
  rw [← twoBlockFirstPenaltyEqCoeToRealOfMemEffectiveDomain f g1 g2 hy]
  simp

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: finiteness of the full objective at a pair
puts the second penalty term in its effective domain. -/
lemma twoBlockSecondPenaltyMemEffectiveDomainOfObjectiveMem
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    {y : E1 × E2} (hy : y ∈ effective_domain F) :
    y.2 ∈ effective_domain g2 := by
  -- Rewrite `g₂(y₂)` through its finite real value coming from the same objective witness.
  refine mem_effective_domain.mpr <| lt_top_iff_ne_top.mpr ?_
  rw [← twoBlockSecondPenaltyEqCoeToRealOfMemEffectiveDomain f g1 g2 hy]
  simp

end ObjectiveDomain

section X1

variable (f : E1 × E2 → ℝ) (g1 : E1 → EReal) (g2 : E2 → EReal)
variable [InnerProductSpace ℝ E1] [ProperSpace E1]
variable [NormedSpace ℝ E2]
variable (x1 : ℕ → E1) (x2 : ℕ → E2) (k : ℕ)

local notation "F" => two_block_alternating_minimization_objective f.toEReal g1 g2
local notation "xk" => (x1 k, x2 k)
local notation "xHalf" => two_block_alternating_minimization_half_step x1 x2 k
local notation "f1" => fun y1 ↦ f (y1, x2 k)
local notation "Fx2" => two_block_alternating_minimization_x2_objective f.toEReal g1 g2 (x1 k)
local notation "φ1" => twoBlockX1PartialInfimum f g1 g2
local notation "η1" => twoBlockX1InactiveMarginal f g2

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: convexity of the frozen smooth slice gives
its first-order support inequality at the current first block. -/
lemma twoBlockX1FrozenSliceSupportAtCurrentSecondBlock
    (hf_x1_convex : ConvexOn ℝ Set.univ f1)
    (hf_x1_smooth : is_l_smooth_on f1 Set.univ (PosReal.toNNReal L1))
    (y1 : E1) :
    f (y1, x2 k) ≥
      f (x1 k, x2 k) +
        fderiv ℝ f1 (x1 k) (y1 - x1 k) := by
  have hdiff : DifferentiableAt ℝ f1 (x1 k) := by
    -- Global `L₁`-smoothness makes the frozen slice differentiable at every point.
    exact
      ((is_l_smooth_on_iff.mp hf_x1_smooth).1 (x1 k) (by simp)).hasGradientAt.differentiableAt
  -- Apply the generic convex-support lemma on the real-valued frozen slice.
  simpa using convexRealSupportUnivFDeriv hf_x1_convex hdiff

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: exact minimization of the current second
block identifies the first partial infimum `φ₁(x₁^k)` with the current objective value. -/
lemma twoBlockX1PartialInfimumEqCurrentObjective
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2) :
    φ1 (x1 k) = F xk := by
  -- Rewrite the partial infimum through the exact current `x₂^k` minimizer.
  change sInf (Set.range (fun z2 : E2 ↦ F (x1 k, z2))) = F xk
  have hmin :
      IsMinOn
        (two_block_alternating_minimization_x2_objective f.toEReal g1 g2 (x1 k))
        Set.univ
        (x2 k) :=
    twoBlockCurrentX2ObjectiveIsMinOn f g1 g2 x1 x2 htraj k
  apply le_antisymm
  · -- The current second block is one witness in the defining fiber of `φ₁`.
    exact sInf_le ⟨x2 k, by simp⟩
  · -- Exact `x₂`-minimality makes every other point in the fiber no smaller.
    refine le_sInf ?_
    rintro _ ⟨z2, rfl⟩
    simpa using (isMinOn_iff.mp hmin) z2 (by simp)

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: global optimality of `xStar` identifies the
fiber infimum `φ₁(xStar.1)` with the full objective value `F xStar`. -/
lemma twoBlockX1PartialInfimumEqOptimalObjective
    (xStar : E1 × E2)
    (hxStar : IsMinOn F Set.univ xStar) :
    φ1 xStar.1 = F xStar := by
  -- Route correction: normalize the fixed competitor through the full-objective partial infimum
  -- first, so the remaining blocker is only the direct marginal-support bridge.
  change sInf (Set.range (fun z2 : E2 ↦ F (xStar.1, z2))) = F xStar
  apply le_antisymm
  · -- The optimal second block supplies one witness in the `xStar.1` fiber.
    exact sInf_le ⟨xStar.2, by
      cases xStar
      simp⟩
  · -- Global minimality bounds the whole `xStar.1` fiber below by `F xStar`.
    refine le_sInf ?_
    rintro _ ⟨z2, rfl⟩
    have hmin := (isMinOn_iff.mp hxStar) (xStar.1, z2) (by simp)
    simpa using hmin

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: once the current iterate is finite, the
inactive marginal `η₁(y₁) = inf_z₂ (f(y₁, z₂) + g₂(z₂))` is attained at the current second
block. -/
lemma twoBlockX1InactiveMarginalEqCurrentValue
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : (x1 0, x2 0) ∈ effective_domain F) :
    η1 (x1 k) = (((f (x1 k, x2 k) : ℝ) : EReal)) + g2 (x2 k) := by
  change sInf (Set.range (fun z2 : E2 ↦ (((f (x1 k, z2) : ℝ) : EReal)) + g2 z2)) =
    (((f (x1 k, x2 k) : ℝ) : EReal)) + g2 (x2 k)
  have hiter :=
    twoBlockIteratesMemEffectiveDomainAndInitialSublevel f g1 g2 x1 x2 htraj hx0 k
  have hg1_coe :
      (((g1 (x1 k)).toReal : ℝ) : EReal) = g1 (x1 k) :=
    twoBlockFirstPenaltyEqCoeToRealOfMemEffectiveDomain f g1 g2 hiter.1
  have hmin :
      IsMinOn
        (two_block_alternating_minimization_x2_objective f.toEReal g1 g2 (x1 k))
        Set.univ
        (x2 k) :=
    twoBlockCurrentX2ObjectiveIsMinOn f g1 g2 x1 x2 htraj k
  apply le_antisymm
  · -- The current second block is one witness in the marginal fiber.
    exact sInf_le ⟨x2 k, by simp⟩
  · -- Exact `x₂`-minimality lets us cancel the finite active penalty from both slice values.
    refine le_sInf ?_
    rintro _ ⟨z2, rfl⟩
    have hslice : F xk ≤ F (x1 k, z2) := by
      simpa using (isMinOn_iff.mp hmin) z2 (by simp)
    have hcancel :
        ((((f (x1 k, x2 k) : ℝ) : EReal) + g2 (x2 k)) +
            (((g1 (x1 k)).toReal : ℝ) : EReal)) ≤
          ((((f (x1 k, z2) : ℝ) : EReal) + g2 z2) +
            (((g1 (x1 k)).toReal : ℝ) : EReal)) := by
      simpa [two_block_alternating_minimization_objective_apply, hg1_coe,
        add_left_comm, add_comm] using hslice
    exact
      (EReal.addLECancellable_coe ((g1 (x1 k)).toReal)).add_le_add_iff_right.mp hcancel

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: the optimizer's second block is one witness
for the inactive marginal at `xStar.1`. -/
lemma twoBlockX1InactiveMarginalLeOptimalWitness
    (xStar : E1 × E2) :
    η1 xStar.1 ≤ (((f xStar : ℝ) : EReal)) + g2 xStar.2 := by
  -- Insert the optimizer's second block as one candidate in the defining fiber.
  exact sInf_le ⟨xStar.2, by simp⟩

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: reattaching the active penalty to the
current inactive marginal recovers the full current objective value. -/
lemma twoBlockX1InactiveMarginalAddActivePenaltyEqCurrentObjective
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : (x1 0, x2 0) ∈ effective_domain F) :
    η1 (x1 k) + g1 (x1 k) = F xk := by
  have heta :
      η1 (x1 k) = (((f (x1 k, x2 k) : ℝ) : EReal)) + g2 (x2 k) := by
    -- First rewrite the inactive marginal through the attained current second block.
    simpa using
      twoBlockX1InactiveMarginalEqCurrentValue f g1 g2 x1 x2 k htraj hx0
  -- Then add back the active penalty term.
  calc
    η1 (x1 k) + g1 (x1 k)
        = ((((f (x1 k, x2 k) : ℝ) : EReal)) + g2 (x2 k)) + g1 (x1 k) := by
            rw [heta]
    _ = F xk := by
      simp [two_block_alternating_minimization_objective_apply, add_left_comm, add_comm]

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: reattaching the active penalty to the
optimizer witness bounds the inactive marginal by the full objective at `xStar`. -/
lemma twoBlockX1InactiveMarginalAddActivePenaltyLeObjectiveAtStar
    (xStar : E1 × E2) :
    η1 xStar.1 + g1 xStar.1 ≤ F xStar := by
  have heta :
      η1 xStar.1 ≤ (((f xStar : ℝ) : EReal)) + g2 xStar.2 := by
    -- Use the optimizer's second block as one admissible inactive witness.
    simpa using
      twoBlockX1InactiveMarginalLeOptimalWitness f g2 xStar
  -- Add back the active penalty and normalize to the full objective.
  calc
    η1 xStar.1 + g1 xStar.1
        ≤ ((((f xStar : ℝ) : EReal)) + g2 xStar.2) + g1 xStar.1 := by
            simpa [add_assoc, add_left_comm, add_comm] using
              add_le_add_right heta (g1 xStar.1)
    _ = F xStar := by
      rcases xStar with ⟨xStar1, xStar2⟩
      simp [two_block_alternating_minimization_objective_apply, add_left_comm, add_comm]

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: the current second-block fiber is a convex
touching majorant of the first inactive marginal, so `η₁` inherits the frozen-slice first-order
support inequality at `xStar.1`. -/
lemma twoBlockX1InactiveMarginalSupportAtStar
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    [Fact (is_convex_function g2)]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : (x1 0, x2 0) ∈ effective_domain F)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_x1_smooth : is_l_smooth_on f1 Set.univ (PosReal.toNNReal L1))
    (xStar : E1 × E2) :
    η1 xStar.1 ≥
      η1 (x1 k) + (inner ℝ (∇ f1 (x1 k)) (xStar.1 - x1 k) : EReal) := by
  let chi : E1 → ℝ := fun y1 ↦ f (y1, x2 k) + (g2 (x2 k)).toReal
  have hiter :=
    twoBlockIteratesMemEffectiveDomainAndInitialSublevel f g1 g2 x1 x2 htraj hx0 k
  have hg2_coe :
      (((g2 (x2 k)).toReal : ℝ) : EReal) = g2 (x2 k) :=
    twoBlockSecondPenaltyEqCoeToRealOfMemEffectiveDomain f g1 g2 hiter.1
  have heta_convex : is_convex_function η1 := by
    let H : E1 × E2 → EReal := fun p ↦ (((f p : ℝ) : EReal)) + g2 p.2
    have hH_convex : is_convex_function H := by
      -- Freeze the source joint convexity together with the inactive penalty into one owner
      -- before descending to the partial infimum.
      exact
        joint_convex_split_objective_is_convex_function
          (h := f)
          (q := g2)
          hf_convex
          (fun z2 ↦ (‹IsProperExtendedRealFunction g2›.ne_bot z2))
          (Fact.out : is_convex_function g2)
    simpa [H, twoBlockX1InactiveMarginal] using partial_infimum_is_convex_function hH_convex
  have hslice_convex : ConvexOn ℝ Set.univ f1 := by
    let phi : E1 →ᵃ[ℝ] E1 × E2 :=
      (LinearMap.inl ℝ E1 E2).toAffineMap + AffineMap.const ℝ E1 (0, x2 k)
    have hphi : (fun y1 ↦ phi y1) = fun y1 ↦ (y1, x2 k) := by
      funext y1
      simp [phi]
    simpa [Function.comp, hphi] using hf_convex.comp_affineMap phi
  have hchi_convex : ConvexOn ℝ Set.univ chi := by
    -- Adding the frozen inactive penalty value preserves convexity of the real-valued slice.
    simpa [chi] using hslice_convex.add_const ((g2 (x2 k)).toReal)
  have hchi_diff : DifferentiableAt ℝ chi (x1 k) := by
    have hdiff : DifferentiableAt ℝ f1 (x1 k) := by
      -- Global `L₁`-smoothness makes the frozen slice differentiable at the current iterate.
      exact
        ((is_l_smooth_on_iff.mp hf_x1_smooth).1 (x1 k) (by simp)).hasGradientAt.differentiableAt
    -- The frozen inactive penalty is constant on the active slice.
    simpa [chi] using hdiff.add_const ((g2 (x2 k)).toReal)
  have heta_le_chi : ∀ y1 : E1, η1 y1 ≤ (chi y1 : EReal) := by
    intro y1
    -- The current second block is one admissible witness in the defining infimum of `η₁(y₁)`.
    calc
      η1 y1 ≤ (((f (y1, x2 k) : ℝ) : EReal)) + g2 (x2 k) := by
        exact sInf_le ⟨x2 k, by simp⟩
      _ = (chi y1 : EReal) := by
        simp [chi, hg2_coe]
  have hcontact : η1 (x1 k) = (chi (x1 k) : EReal) := by
    -- The current fiber infimum is attained exactly at the current second block.
    simp [chi, hg2_coe,
      twoBlockX1InactiveMarginalEqCurrentValue f g1 g2 x1 x2 k htraj hx0]
  have hgrad_chi : ∇ chi (x1 k) = ∇ (fun y1 ↦ f (y1, x2 k)) (x1 k) := by
    have hbase :
        HasGradientAt (fun y1 ↦ f (y1, x2 k)) (∇ (fun y1 ↦ f (y1, x2 k)) (x1 k)) (x1 k) := by
      exact ((is_l_smooth_on_iff.mp hf_x1_smooth).1 (x1 k) (by simp)).hasGradientAt
    have hchi_grad :
        HasGradientAt chi (∇ (fun y1 ↦ f (y1, x2 k)) (x1 k)) (x1 k) := by
      simpa [chi] using (hbase.hasFDerivAt.add_const ((g2 (x2 k)).toReal)).hasGradientAt
    exact (HasGradientAt.unique hchi_grad hchi_diff.hasGradientAt).symm
  -- Apply the generic touched-majorant bridge to the current inactive marginal and frozen slice.
  simpa [hgrad_chi] using
    convexContactSupportAtTouchedConvexMajorant
      (eta := η1)
      (chi := chi)
      (x0 := x1 k)
      (y := xStar.1)
      heta_convex
      hchi_convex
      heta_le_chi
      hcontact
      hchi_diff

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: the prox-gradient candidate on the current
`x₁`-slice should already satisfy the full optimizer gap bound. This is the remaining x₁-side
structural blocker after the exact-step comparison has been isolated. -/
lemma twoBlockX1ProxCandidateAffineUpperBoundAtStar
    (L1 : PosReal)
    [IsProperExtendedRealFunction g1]
    [Fact (LowerSemicontinuous g1)]
    [Fact (is_convex_function g1)]
    [IsProperExtendedRealFunction g2]
    [Fact (is_convex_function g2)]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : (x1 0, x2 0) ∈ effective_domain F)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_x1_smooth : is_l_smooth_on f1 Set.univ (PosReal.toNNReal L1))
    (xStar : E1 × E2)
    (hxStar : IsMinOn F Set.univ xStar) :
    let xPlus : E1 := T[L1; f1, g1] (x1 k)
    let Gk : E1 := G[L1; f1, g1] (x1 k)
    let quad : ℝ := ((L1 : ℝ) / 2) * ‖xPlus - x1 k‖ ^ (2 : ℕ)
    F (xPlus, x2 k) ≤
      F xStar + (inner ℝ Gk (xPlus - xStar.1) : EReal) + (quad : EReal) := by
  let xPlus : E1 := T[L1; f1, g1] (x1 k)
  let Gk : E1 := G[L1; f1, g1] (x1 k)
  let quad : ℝ := ((L1 : ℝ) / 2) * ‖xPlus - x1 k‖ ^ (2 : ℕ)
  have hxStar_mem : xStar ∈ effective_domain F := by
    have hmin := (isMinOn_iff.mp hxStar) (x1 0, x2 0) (by simp)
    exact mem_effective_domain.mpr <| lt_of_le_of_lt hmin (mem_effective_domain.mp hx0)
  have hxStar_g1 : xStar.1 ∈ effective_domain g1 :=
    twoBlockFirstPenaltyMemEffectiveDomainOfObjectiveMem f g1 g2 hxStar_mem
  rcases gradient_mapping_support_ineq_real
      (Function.toEReal fun y1 ↦ f (y1, x2 k))
      g1
      L1
      (interior_effective_domain_point_of_real (fun y1 ↦ f (y1, x2 k)) (x1 k)) with
    ⟨hxPlus_eff, hprox_raw⟩
  have hsmooth_real :
      f (xPlus, x2 k) ≤ f (x1 k, x2 k) +
        inner ℝ (∇ f1 (x1 k)) (xPlus - x1 k) + quad := by
    simpa [xPlus, quad, norm_sub_rev] using
      is_l_smooth_on_univ_descent_lemma hf_x1_smooth (x1 k) xPlus
  have hsupport_eta :
      η1 xStar.1 ≥
        η1 (x1 k) + (inner ℝ (∇ f1 (x1 k)) (xStar.1 - x1 k) : EReal) := by
    simpa using
      twoBlockX1InactiveMarginalSupportAtStar
        f g1 g2 x1 x2 k htraj hx0 hf_convex hf_x1_smooth xStar
  have hsmooth_ereal :
      (((f (xPlus, x2 k) : ℝ) : EReal)) + g2 (x2 k) ≤
        η1 (x1 k) + (inner ℝ (∇ f1 (x1 k)) (xPlus - x1 k) : EReal) + (quad : EReal) := by
    have hsmooth_cast :
        (((f (xPlus, x2 k) : ℝ) : EReal)) ≤
          (((f (x1 k, x2 k) + inner ℝ (∇ f1 (x1 k)) (xPlus - x1 k) + quad : ℝ) : EReal)) := by
      exact_mod_cast hsmooth_real
    calc
      (((f (xPlus, x2 k) : ℝ) : EReal)) + g2 (x2 k)
          ≤ (((f (x1 k, x2 k) + inner ℝ (∇ f1 (x1 k)) (xPlus - x1 k) + quad : ℝ) : EReal)) +
              g2 (x2 k) := by
                simpa [add_assoc, add_left_comm, add_comm] using
                  add_le_add_right hsmooth_cast (g2 (x2 k))
      _ = η1 (x1 k) + (inner ℝ (∇ f1 (x1 k)) (xPlus - x1 k) : EReal) + (quad : EReal) := by
        rw [twoBlockX1InactiveMarginalEqCurrentValue f g1 g2 x1 x2 k htraj hx0]
        simp [add_assoc, add_comm, quad]
  have hsupport_transport :
      η1 (x1 k) + (inner ℝ (∇ f1 (x1 k)) (xPlus - x1 k) : EReal) ≤
        η1 xStar.1 + (inner ℝ (∇ f1 (x1 k)) (xPlus - xStar.1) : EReal) := by
    have hsplit_real :
        inner ℝ (∇ f1 (x1 k)) (xStar.1 - x1 k) +
            inner ℝ (∇ f1 (x1 k)) (xPlus - xStar.1) =
          inner ℝ (∇ f1 (x1 k)) (xPlus - x1 k) := by
      rw [← inner_add_right]
      abel
    have hadded :=
      add_le_add_right hsupport_eta
        ((inner ℝ (∇ f1 (x1 k)) (xPlus - xStar.1) : ℝ) : EReal)
    have hsplit :
        (inner ℝ (∇ f1 (x1 k)) (xPlus - x1 k) : EReal) =
          (inner ℝ (∇ f1 (x1 k)) (xStar.1 - x1 k) : EReal) +
            (inner ℝ (∇ f1 (x1 k)) (xPlus - xStar.1) : EReal) := by
      exact congrArg (fun t : ℝ ↦ (t : EReal)) hsplit_real.symm
    calc
      η1 (x1 k) + (inner ℝ (∇ f1 (x1 k)) (xPlus - x1 k) : EReal)
          = η1 (x1 k) +
              (inner ℝ (∇ f1 (x1 k)) (xStar.1 - x1 k) : EReal) +
                (inner ℝ (∇ f1 (x1 k)) (xPlus - xStar.1) : EReal) := by
                  rw [hsplit]
                  simp [add_assoc]
      _ ≤ η1 xStar.1 + (inner ℝ (∇ f1 (x1 k)) (xPlus - xStar.1) : EReal) := by
            simpa [add_assoc, add_left_comm, add_comm] using hadded
  have hsmooth_star :
      (((f (xPlus, x2 k) : ℝ) : EReal)) + g2 (x2 k) ≤
        η1 xStar.1 + (inner ℝ (∇ f1 (x1 k)) (xPlus - xStar.1) : EReal) + (quad : EReal) := by
    have hquad := add_le_add_right hsupport_transport (quad : EReal)
    exact le_trans hsmooth_ereal <| by
      simpa [add_assoc, add_left_comm, add_comm] using hquad
  have hg1_xplus_val : (((g1 xPlus).toReal : ℝ) : EReal) = g1 xPlus := by
    exact
      EReal.coe_toReal
        (mem_effective_domain.mp hxPlus_eff).ne
        (‹IsProperExtendedRealFunction g1›.ne_bot xPlus)
  have hg1_xstar_val : (((g1 xStar.1).toReal : ℝ) : EReal) = g1 xStar.1 := by
    exact
      EReal.coe_toReal
        (mem_effective_domain.mp hxStar_g1).ne
        (‹IsProperExtendedRealFunction g1›.ne_bot xStar.1)
  have hprox_real :
      (g1 xPlus).toReal ≤
        (g1 xStar.1).toReal +
          inner ℝ (Gk - ∇ f1 (x1 k)) (xPlus - xStar.1) := by
    have hsupport := hprox_raw xStar.1 hxStar_g1
    have hsupport' :
        inner ℝ (Gk - ∇ f1 (x1 k)) (xStar.1 - xPlus) ≤
          (g1 xStar.1).toReal - (g1 xPlus).toReal := by
      simpa [xPlus, Gk] using hsupport
    have hflip :
        inner ℝ (Gk - ∇ f1 (x1 k)) (xStar.1 - xPlus) =
          -inner ℝ (Gk - ∇ f1 (x1 k)) (xPlus - xStar.1) := by
      have hdisp : xStar.1 - xPlus = -(xPlus - xStar.1) := by
        abel
      rw [hdisp, inner_neg_right]
    rw [hflip] at hsupport'
    linarith
  have hprox_ereal :
      g1 xPlus ≤
        g1 xStar.1 + (inner ℝ (Gk - ∇ f1 (x1 k)) (xPlus - xStar.1) : EReal) := by
    rw [← hg1_xplus_val, ← hg1_xstar_val]
    exact_mod_cast hprox_real
  have hinner_merge :
      (inner ℝ (∇ f1 (x1 k)) (xPlus - xStar.1) : EReal) +
          (inner ℝ (Gk - ∇ f1 (x1 k)) (xPlus - xStar.1) : EReal) =
        (inner ℝ Gk (xPlus - xStar.1) : EReal) := by
    have hinner_merge_real :
        inner ℝ (∇ f1 (x1 k)) (xPlus - xStar.1) +
            inner ℝ (Gk - ∇ f1 (x1 k)) (xPlus - xStar.1) =
          inner ℝ Gk (xPlus - xStar.1) := by
      rw [inner_sub_left]
      linarith
    exact_mod_cast hinner_merge_real
  let linear : EReal := (inner ℝ (∇ f1 (x1 k)) (xPlus - xStar.1) : EReal)
  let residual : EReal :=
    (inner ℝ (Gk - ∇ f1 (x1 k)) (xPlus - xStar.1) : EReal)
  let affine : EReal := (inner ℝ Gk (xPlus - xStar.1) : EReal)
  have hsmooth_star' :
      (((f (xPlus, x2 k) : ℝ) : EReal)) + g2 (x2 k) ≤
        η1 xStar.1 + linear + (quad : EReal) := by
    simpa [linear] using hsmooth_star
  have hprox_ereal' :
      g1 xPlus ≤ g1 xStar.1 + residual := by
    simpa [residual] using hprox_ereal
  have hmerge_eq : linear + residual = affine := by
    simpa [linear, residual, affine] using hinner_merge
  have hcore :
      F (xPlus, x2 k) ≤
        η1 xStar.1 + g1 xStar.1 + affine + (quad : EReal) := by
    have hsum := add_le_add hsmooth_star' hprox_ereal'
    calc
      F (xPlus, x2 k)
          = ((((f (xPlus, x2 k) : ℝ) : EReal)) + g2 (x2 k)) + g1 xPlus := by
              simp [two_block_alternating_minimization_objective_apply, add_left_comm, add_comm]
      _ ≤
          (η1 xStar.1 + linear + (quad : EReal)) +
            (g1 xStar.1 + residual) := hsum
      _ = η1 xStar.1 + g1 xStar.1 + (linear + residual) + (quad : EReal) := by
            abel_nf
      _ = η1 xStar.1 + g1 xStar.1 + affine + (quad : EReal) := by
            rw [hmerge_eq]
  have hstar :=
    add_le_add_right
      (twoBlockX1InactiveMarginalAddActivePenaltyLeObjectiveAtStar f g1 g2 xStar)
      (affine + (quad : EReal))
  have htail :
      η1 xStar.1 + g1 xStar.1 + affine + (quad : EReal) ≤
        F xStar + affine + (quad : EReal) := by
    have htail0 :
        affine + ((quad : EReal) + (η1 xStar.1 + g1 xStar.1)) ≤
          affine + ((quad : EReal) + F xStar) := by
      simpa [add_assoc] using hstar
    calc
      η1 xStar.1 + g1 xStar.1 + affine + (quad : EReal)
          = affine + ((quad : EReal) + (η1 xStar.1 + g1 xStar.1)) := by
              abel_nf
      _ ≤ affine + ((quad : EReal) + F xStar) := htail0
      _ = F xStar + affine + (quad : EReal) := by
            abel_nf
  exact le_trans hcore htail

/-- Lemma 14.4 InactiveBlockSupport helper: the prox-gradient candidate on the current
`x₁`-slice satisfies the optimizer gap bound before comparing the exact alternating-minimization
half-step against that candidate. -/
lemma twoBlockX1ProxCandidateGapLeGradientMapping
    (L1 : PosReal)
    [IsProperExtendedRealFunction g1]
    [Fact (LowerSemicontinuous g1)]
    [Fact (is_convex_function g1)]
    [IsProperExtendedRealFunction g2]
    [Fact (is_convex_function g2)]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : (x1 0, x2 0) ∈ effective_domain F)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_x1_smooth : is_l_smooth_on f1 Set.univ (PosReal.toNNReal L1))
    (xStar : E1 × E2)
    (hxStar : IsMinOn F Set.univ xStar) :
    let xPlus : E1 := T[L1; f1, g1] (x1 k)
    F (xPlus, x2 k) - F xStar ≤
      (((‖G[L1; f1, g1] (x1 k)‖ * ‖xk - xStar‖ : ℝ) : EReal)) := by
  let xPlus : E1 := T[L1; f1, g1] (x1 k)
  let Gk : E1 := G[L1; f1, g1] (x1 k)
  let quad : ℝ := ((L1 : ℝ) / 2) * ‖xPlus - x1 k‖ ^ (2 : ℕ)
  have hcandidate_affine :
      F (xPlus, x2 k) ≤
        F xStar + (inner ℝ Gk (xPlus - xStar.1) : EReal) + (quad : EReal) := by
    simpa [xPlus, Gk, quad] using
      twoBlockX1ProxCandidateAffineUpperBoundAtStar
        f g1 g2 x1 x2 k L1 htraj hx0 hf_convex hf_x1_smooth xStar hxStar
  have hxplus_eq :
      xPlus = x1 k - (1 / (L1 : ℝ)) • Gk := by
    -- Normalize the prox-gradient trial point into the residual spelling used in Chapter 10.
    simpa [xPlus, Gk, prox_gradient_operator_apply, prox_gradient_mapping_apply] using
      (prox_grad_operator_eq_sub_gradient_mapping
        (f := Function.toEReal fun y1 ↦ f (y1, x2 k))
        (g := g1)
        (L := L1)
        (x := interior_effective_domain_point_of_real (fun y1 ↦ f (y1, x2 k)) (x1 k)))
  have hcore_nonpos :
      inner ℝ Gk (xPlus - x1 k) + quad ≤ 0 := by
    have hdisp : xPlus - x1 k = -((1 / (L1 : ℝ)) • Gk) := by
      rw [hxplus_eq]
      abel
    have hL_nonneg : 0 ≤ (1 / (L1 : ℝ)) := by
      exact one_div_nonneg.mpr (le_of_lt L1.2)
    calc
      inner ℝ Gk (xPlus - x1 k) + quad
          = inner ℝ Gk (-((1 / (L1 : ℝ)) • Gk)) +
              ((L1 : ℝ) / 2) * ‖-((1 / (L1 : ℝ)) • Gk)‖ ^ (2 : ℕ) := by
                dsimp [quad]
                rw [hdisp]
      _ = -((1 / (L1 : ℝ)) * ‖Gk‖ ^ (2 : ℕ)) +
            ((L1 : ℝ) / 2) * (((1 / (L1 : ℝ)) ^ (2 : ℕ)) * ‖Gk‖ ^ (2 : ℕ)) := by
              rw [inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq, norm_neg,
                norm_smul, Real.norm_eq_abs, abs_of_nonneg hL_nonneg]
              ring
      _ = -((1 / (2 * (L1 : ℝ))) * ‖Gk‖ ^ (2 : ℕ)) := by
            field_simp [show (L1 : ℝ) ≠ 0 by exact L1.2.ne']
            ring
      _ ≤ 0 := by
            have hsq : 0 ≤ ‖Gk‖ ^ (2 : ℕ) := by positivity
            have hfac : 0 ≤ (1 / (2 * (L1 : ℝ))) := by
              have hden : 0 < 2 * (L1 : ℝ) := by
                have htwo : (0 : ℝ) < 2 := by norm_num
                have hL : (0 : ℝ) < (L1 : ℝ) := L1.2
                nlinarith
              exact one_div_nonneg.mpr hden.le
            nlinarith
  have htrial_real :
      inner ℝ Gk (xPlus - xStar.1) + quad ≤
        inner ℝ Gk (x1 k - xStar.1) := by
    have hsplit :
        inner ℝ Gk (xPlus - xStar.1) =
          inner ℝ Gk (x1 k - xStar.1) + inner ℝ Gk (xPlus - x1 k) := by
      have hdisp : xPlus - xStar.1 = (x1 k - xStar.1) + (xPlus - x1 k) := by
        abel
      rw [hdisp, inner_add_right]
    linarith
  have htrial_ereal :
      (inner ℝ Gk (xPlus - xStar.1) : EReal) + (quad : EReal) ≤
        (inner ℝ Gk (x1 k - xStar.1) : EReal) := by
    exact_mod_cast htrial_real
  have hcandidate_linear :
      F (xPlus, x2 k) ≤ F xStar + (inner ℝ Gk (x1 k - xStar.1) : EReal) := by
    have htrial_add :
        F xStar + (inner ℝ Gk (xPlus - xStar.1) : EReal) + (quad : EReal) ≤
          F xStar + (inner ℝ Gk (x1 k - xStar.1) : EReal) := by
      simpa [add_assoc] using add_le_add_right htrial_ereal (F xStar)
    exact le_trans hcandidate_affine htrial_add
  have hblock :
      ‖x1 k - xStar.1‖ ≤ ‖xk - xStar‖ := by
    -- The product norm dominates the active first-block coordinate norm.
    simpa using
      (norm_fst_le (((x1 k, x2 k) - xStar)))
  have hcs_real :
      inner ℝ Gk (x1 k - xStar.1) ≤ ‖Gk‖ * ‖xk - xStar‖ := by
    exact
      le_trans
        (real_inner_le_norm Gk (x1 k - xStar.1))
        (mul_le_mul_of_nonneg_left hblock (norm_nonneg _))
  have hcs_ereal :
      (inner ℝ Gk (x1 k - xStar.1) : EReal) ≤
        (((‖Gk‖ * ‖xk - xStar‖ : ℝ) : EReal)) := by
    exact_mod_cast hcs_real
  have hfinal :
      F (xPlus, x2 k) ≤
        F xStar + (((‖Gk‖ * ‖xk - xStar‖ : ℝ) : EReal)) := by
    have hcs_add :
        F xStar + (inner ℝ Gk (x1 k - xStar.1) : EReal) ≤
          F xStar + (((‖Gk‖ * ‖xk - xStar‖ : ℝ) : EReal)) := by
      simpa using add_le_add_right hcs_ereal (F xStar)
    exact le_trans hcandidate_linear hcs_add
  exact EReal.sub_le_of_le_add' hfinal

/-- Helper for Lemma 14.4 InactiveBlockSupport helper (1): if `x1` and `x2` are generated by the
two-block
alternating minimization method and the initial pair `(x1 0, x2 0)` lies in `effective_domain F`,
then the half-step objective gap satisfies
`F(x^{k+1/2}) - F(x^*) ≤ ‖G^1_{L₁}(x^k)‖ * ‖x^k - x^*‖`, with
`x^{k+1/2} = (x1 (k + 1), x2 k)`. The intended Chapter 14 proof route is the established
current-fiber partial-infimum support bridge, followed by support on the fixed `xStar.1` fiber. -/
theorem two_block_half_step_objective_gap_le_x1_gradient_mapping
    (L1 : PosReal)
    [IsProperExtendedRealFunction g1]
    [Fact (LowerSemicontinuous g1)]
    [Fact (is_convex_function g1)]
    [IsProperExtendedRealFunction g2]
    [Fact (is_convex_function g2)]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : (x1 0, x2 0) ∈ effective_domain F)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_x1_smooth : is_l_smooth_on f1 Set.univ (PosReal.toNNReal L1))
    (xStar : E1 × E2)
    (hxStar : IsMinOn F Set.univ xStar) :
    F xHalf - F xStar ≤
      (((‖G[L1; f1, g1] (x1 k)‖ * ‖xk - xStar‖ : ℝ) : EReal)) := by
  let xPlus : E1 := T[L1; f1, g1] (x1 k)
  have hhalf_le_candidate : F xHalf ≤ F (xPlus, x2 k) := by
    -- Compare the exact `x₁`-minimizer with the prox-gradient candidate on the same frozen slice.
    have hstep :
        IsMinOn
          (two_block_alternating_minimization_x1_objective f.toEReal g1 g2 (x2 k))
          Set.univ
          (x1 (k + 1)) := htraj.step_x1 k
    simpa [two_block_alternating_minimization_half_step] using
      (isMinOn_iff.mp hstep) xPlus (by simp)
  have hcandidate_gap :
      F (xPlus, x2 k) - F xStar ≤
        (((‖G[L1; f1, g1] (x1 k)‖ * ‖xk - xStar‖ : ℝ) : EReal)) := by
    -- The remaining gap is exactly the prox-candidate-vs-optimizer estimate.
    simpa [xPlus] using
      twoBlockX1ProxCandidateGapLeGradientMapping
        f g1 g2 x1 x2 k L1 htraj hx0 hf_convex hf_x1_smooth xStar hxStar
  have hcandidate_gap' :
      F (xPlus, x2 k) ≤
        F xStar + (((‖G[L1; f1, g1] (x1 k)‖ * ‖xk - xStar‖ : ℝ) : EReal)) := by
    simpa [add_comm] using
      (EReal.sub_le_iff_le_add
        (.inr (EReal.coe_ne_top _))
        (.inr (EReal.coe_ne_bot _))).mp
        hcandidate_gap
  exact EReal.sub_le_of_le_add' (le_trans hhalf_le_candidate hcandidate_gap')

end X1

section X2

variable (f : E1 × E2 → ℝ) (g1 : E1 → EReal) (g2 : E2 → EReal)
variable [InnerProductSpace ℝ E2] [ProperSpace E2]
variable [NormedSpace ℝ E1]
variable (x1 : ℕ → E1) (x2 : ℕ → E2) (k : ℕ)

local notation "F" => two_block_alternating_minimization_objective f.toEReal g1 g2
local notation "xHalf" => two_block_alternating_minimization_half_step x1 x2 k
local notation "xNext" => (x1 (k + 1), x2 (k + 1))
local notation "f2" => fun y2 ↦ f (x1 (k + 1), y2)
local notation "Fx1" => two_block_alternating_minimization_x1_objective f.toEReal g1 g2 (x2 k)
local notation "φ2" => twoBlockX2PartialInfimum f g1 g2
local notation "η2" => twoBlockX2InactiveMarginal f g1

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: convexity of the frozen smooth slice gives
its first-order support inequality at the current second block. -/
lemma twoBlockX2FrozenSliceSupportAtHalfStepFirstBlock
    (hf_x2_convex : ConvexOn ℝ Set.univ f2)
    (hf_x2_smooth : is_l_smooth_on f2 Set.univ (PosReal.toNNReal L2))
    (y2 : E2) :
    f (x1 (k + 1), y2) ≥
      f (x1 (k + 1), x2 k) +
        fderiv ℝ f2 (x2 k) (y2 - x2 k) := by
  have hdiff : DifferentiableAt ℝ f2 (x2 k) := by
    -- Global `L₂`-smoothness makes the frozen slice differentiable at every point.
    exact
      ((is_l_smooth_on_iff.mp hf_x2_smooth).1 (x2 k) (by simp)).hasGradientAt.differentiableAt
  -- Apply the same whole-space convex-support lemma to the second frozen slice.
  simpa using convexRealSupportUnivFDeriv hf_x2_convex hdiff

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: exact minimization of the half-step first
block identifies the second partial infimum `φ₂(x₂^k)` with the half-step objective value. -/
lemma twoBlockX2PartialInfimumEqCurrentObjective
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2) :
    φ2 (x2 k) = F xHalf := by
  -- Rewrite the partial infimum through the exact half-step `x₁^(k+1)` minimizer.
  change sInf (Set.range (fun z1 : E1 ↦ F (z1, x2 k))) = F xHalf
  have hmin :
      IsMinOn
        (two_block_alternating_minimization_x1_objective f.toEReal g1 g2 (x2 k))
        Set.univ
        (x1 (k + 1)) := by
    simpa [Nat.succ_eq_add_one] using htraj.step_x1 k
  apply le_antisymm
  · -- The updated first block is one witness in the defining fiber of `φ₂`.
    exact sInf_le ⟨x1 (k + 1), by simp [two_block_alternating_minimization_half_step]⟩
  · -- Exact `x₁`-minimality makes every other point in the fiber no smaller.
    refine le_sInf ?_
    rintro _ ⟨z1, rfl⟩
    simpa [two_block_alternating_minimization_half_step] using
      (isMinOn_iff.mp hmin) z1 (by simp)

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: global optimality of `xStar` identifies the
fiber infimum `φ₂(xStar.2)` with the full objective value `F xStar`. -/
lemma twoBlockX2PartialInfimumEqOptimalObjective
    (xStar : E1 × E2)
    (hxStar : IsMinOn F Set.univ xStar) :
    φ2 xStar.2 = F xStar := by
  -- Normalize the fixed competitor through the second partial infimum before the remaining bridge.
  change sInf (Set.range (fun z1 : E1 ↦ F (z1, xStar.2))) = F xStar
  apply le_antisymm
  · -- The optimal first block supplies one witness in the `xStar.2` fiber.
    exact sInf_le ⟨xStar.1, by
      cases xStar
      simp⟩
  · -- Global minimality bounds the whole `xStar.2` fiber below by `F xStar`.
    refine le_sInf ?_
    rintro _ ⟨z1, rfl⟩
    have hmin := (isMinOn_iff.mp hxStar) (z1, xStar.2) (by simp)
    simpa using hmin

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: once the half-step is finite, the inactive
marginal `η₂(y₂) = inf_z₁ (f(z₁, y₂) + g₁(z₁))` is attained at the updated first block. -/
lemma twoBlockX2InactiveMarginalEqCurrentValue
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : (x1 0, x2 0) ∈ effective_domain F) :
    η2 (x2 k) = (((f (x1 (k + 1), x2 k) : ℝ) : EReal)) + g1 (x1 (k + 1)) := by
  change sInf (Set.range (fun z1 : E1 ↦ (((f (z1, x2 k) : ℝ) : EReal)) + g1 z1)) =
    (((f (x1 (k + 1), x2 k) : ℝ) : EReal)) + g1 (x1 (k + 1))
  have hhalf :=
    twoBlockHalfStepMemEffectiveDomainAndInitialSublevel f g1 g2 x1 x2 htraj hx0 k
  have hg2_coe :
      (((g2 (x2 k)).toReal : ℝ) : EReal) = g2 (x2 k) := by
    simpa [two_block_alternating_minimization_half_step] using
      twoBlockSecondPenaltyEqCoeToRealOfMemEffectiveDomain f g1 g2 hhalf.1
  have hmin :
      IsMinOn
        (two_block_alternating_minimization_x1_objective f.toEReal g1 g2 (x2 k))
        Set.univ
        (x1 (k + 1)) := by
    simpa [Nat.succ_eq_add_one] using htraj.step_x1 k
  apply le_antisymm
  · -- The updated first block is one witness in the marginal fiber.
    exact sInf_le ⟨x1 (k + 1), by simp⟩
  · -- Exact `x₁`-minimality lets us cancel the finite inactive penalty from both slice values.
    refine le_sInf ?_
    rintro _ ⟨z1, rfl⟩
    have hslice :
        F (x1 (k + 1), x2 k) ≤ F (z1, x2 k) := by
      simpa [Nat.succ_eq_add_one, two_block_alternating_minimization_half_step] using
        (isMinOn_iff.mp hmin) z1 (by simp)
    have hcancel :
        ((((f (x1 (k + 1), x2 k) : ℝ) : EReal) + g1 (x1 (k + 1))) +
            (((g2 (x2 k)).toReal : ℝ) : EReal)) ≤
          ((((f (z1, x2 k) : ℝ) : EReal) + g1 z1) +
            (((g2 (x2 k)).toReal : ℝ) : EReal)) := by
      simpa [two_block_alternating_minimization_objective_apply, hg2_coe,
        add_left_comm, add_comm] using hslice
    exact
      (EReal.addLECancellable_coe ((g2 (x2 k)).toReal)).add_le_add_iff_right.mp hcancel

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: the optimizer's first block is one witness
for the inactive marginal at `xStar.2`. -/
lemma twoBlockX2InactiveMarginalLeOptimalWitness
    (xStar : E1 × E2) :
    η2 xStar.2 ≤ (((f xStar : ℝ) : EReal)) + g1 xStar.1 := by
  -- Insert the optimizer's first block as one candidate in the defining fiber.
  exact sInf_le ⟨xStar.1, by simp⟩

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: reattaching the inactive penalty to the
current second marginal recovers the half-step objective value. -/
lemma twoBlockX2InactiveMarginalAddInactivePenaltyEqHalfStepObjective
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : (x1 0, x2 0) ∈ effective_domain F) :
    η2 (x2 k) + g2 (x2 k) = F xHalf := by
  have heta :
      η2 (x2 k) = (((f (x1 (k + 1), x2 k) : ℝ) : EReal)) + g1 (x1 (k + 1)) := by
    -- First rewrite the inactive marginal through the attained half-step first block.
    simpa using
      twoBlockX2InactiveMarginalEqCurrentValue f g1 g2 x1 x2 k htraj hx0
  -- Then add back the inactive penalty term.
  calc
    η2 (x2 k) + g2 (x2 k)
        = ((((f (x1 (k + 1), x2 k) : ℝ) : EReal)) + g1 (x1 (k + 1))) + g2 (x2 k) := by
            rw [heta]
    _ = F xHalf := by
      simp [two_block_alternating_minimization_objective_apply,
        two_block_alternating_minimization_half_step, add_comm]

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: reattaching the inactive penalty to the
optimizer witness bounds the second inactive marginal by the full objective at `xStar`. -/
lemma twoBlockX2InactiveMarginalAddInactivePenaltyLeObjectiveAtStar
    (xStar : E1 × E2) :
    η2 xStar.2 + g2 xStar.2 ≤ F xStar := by
  have heta :
      η2 xStar.2 ≤ (((f xStar : ℝ) : EReal)) + g1 xStar.1 := by
    -- Use the optimizer's first block as one admissible inactive witness.
    simpa using
      twoBlockX2InactiveMarginalLeOptimalWitness f g1 xStar
  -- Add back the inactive penalty and normalize to the full objective.
  calc
    η2 xStar.2 + g2 xStar.2
        ≤ ((((f xStar : ℝ) : EReal)) + g1 xStar.1) + g2 xStar.2 := by
            simpa [add_assoc, add_left_comm, add_comm] using
              add_le_add_right heta (g2 xStar.2)
    _ = F xStar := by
      rcases xStar with ⟨xStar1, xStar2⟩
      simp [two_block_alternating_minimization_objective_apply, add_left_comm, add_comm]

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: the half-step first-block fiber is a convex
touching majorant of the second inactive marginal, so `η₂` inherits the frozen-slice first-order
support inequality at `xStar.2`. -/
lemma twoBlockX2InactiveMarginalSupportAtStar
    [IsProperExtendedRealFunction g1]
    [IsProperExtendedRealFunction g2]
    [Fact (is_convex_function g1)]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : (x1 0, x2 0) ∈ effective_domain F)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_x2_smooth : is_l_smooth_on f2 Set.univ (PosReal.toNNReal L2))
    (xStar : E1 × E2) :
    η2 xStar.2 ≥
      η2 (x2 k) + (inner ℝ (∇ f2 (x2 k)) (xStar.2 - x2 k) : EReal) := by
  let chi : E2 → ℝ := fun y2 ↦ f (x1 (k + 1), y2) + (g1 (x1 (k + 1))).toReal
  have hhalf :=
    twoBlockHalfStepMemEffectiveDomainAndInitialSublevel f g1 g2 x1 x2 htraj hx0 k
  have hg1_coe :
      (((g1 (x1 (k + 1))).toReal : ℝ) : EReal) = g1 (x1 (k + 1)) := by
    simpa [two_block_alternating_minimization_half_step] using
      twoBlockFirstPenaltyEqCoeToRealOfMemEffectiveDomain f g1 g2 hhalf.1
  have heta_convex : is_convex_function η2 := by
    let H : E2 × E1 → EReal := fun p ↦ (((f (p.2, p.1) : ℝ) : EReal)) + g1 p.2
    have hswap_convex : ConvexOn ℝ Set.univ (fun p : E2 × E1 ↦ f (p.2, p.1)) := by
      let phi : E2 × E1 →ᵃ[ℝ] E1 × E2 :=
        (LinearEquiv.prodComm ℝ E2 E1).toLinearMap.toAffineMap
      simpa [Function.comp, phi] using hf_convex.comp_affineMap phi
    have hH_convex : is_convex_function H := by
      -- Swap the product coordinates so the inactive penalty again lives on the second factor.
      exact
        joint_convex_split_objective_is_convex_function
          (h := fun p : E2 × E1 ↦ f (p.2, p.1))
          (q := g1)
          hswap_convex
          (fun z1 ↦ (‹IsProperExtendedRealFunction g1›.ne_bot z1))
          (Fact.out : is_convex_function g1)
    simpa [H, twoBlockX2InactiveMarginal] using partial_infimum_is_convex_function hH_convex
  have hslice_convex : ConvexOn ℝ Set.univ f2 := by
    let phi : E2 →ᵃ[ℝ] E1 × E2 :=
      (LinearMap.inr ℝ E1 E2).toAffineMap + AffineMap.const ℝ E2 (x1 (k + 1), 0)
    have hphi : (fun y2 ↦ phi y2) = fun y2 ↦ (x1 (k + 1), y2) := by
      funext y2
      simp [phi]
    simpa [Function.comp, hphi] using hf_convex.comp_affineMap phi
  have hchi_convex : ConvexOn ℝ Set.univ chi := by
    -- Adding the frozen active penalty value preserves convexity
    -- of the real-valued half-step slice.
    simpa [chi] using hslice_convex.add_const ((g1 (x1 (k + 1))).toReal)
  have hchi_diff : DifferentiableAt ℝ chi (x2 k) := by
    have hdiff : DifferentiableAt ℝ f2 (x2 k) := by
      -- Global `L₂`-smoothness makes the frozen slice differentiable at the half-step point.
      exact
        ((is_l_smooth_on_iff.mp hf_x2_smooth).1 (x2 k) (by simp)).hasGradientAt.differentiableAt
    -- The frozen active penalty is constant on the inactive slice.
    simpa [chi] using hdiff.add_const ((g1 (x1 (k + 1))).toReal)
  have heta_le_chi : ∀ y2 : E2, η2 y2 ≤ (chi y2 : EReal) := by
    intro y2
    -- The updated first block is one admissible witness in the defining infimum of `η₂(y₂)`.
    calc
      η2 y2 ≤ (((f (x1 (k + 1), y2) : ℝ) : EReal)) + g1 (x1 (k + 1)) := by
        exact sInf_le ⟨x1 (k + 1), by simp⟩
      _ = (chi y2 : EReal) := by
        simp [chi, hg1_coe]
  have hcontact : η2 (x2 k) = (chi (x2 k) : EReal) := by
    -- The half-step fiber infimum is attained exactly at the updated first block.
    simp [chi, hg1_coe,
      twoBlockX2InactiveMarginalEqCurrentValue f g1 g2 x1 x2 k htraj hx0]
  have hgrad_chi : ∇ chi (x2 k) = ∇ (fun y2 ↦ f (x1 (k + 1), y2)) (x2 k) := by
    have hbase :
        HasGradientAt (fun y2 ↦ f (x1 (k + 1), y2))
          (∇ (fun y2 ↦ f (x1 (k + 1), y2)) (x2 k))
          (x2 k) := by
      exact ((is_l_smooth_on_iff.mp hf_x2_smooth).1 (x2 k) (by simp)).hasGradientAt
    have hchi_grad :
        HasGradientAt chi (∇ (fun y2 ↦ f (x1 (k + 1), y2)) (x2 k)) (x2 k) := by
      simpa [chi] using (hbase.hasFDerivAt.add_const ((g1 (x1 (k + 1))).toReal)).hasGradientAt
    exact (HasGradientAt.unique hchi_grad hchi_diff.hasGradientAt).symm
  -- Apply the same touched-majorant bridge to the symmetric inactive marginal.
  simpa [hgrad_chi] using
    convexContactSupportAtTouchedConvexMajorant
      (eta := η2)
      (chi := chi)
      (x0 := x2 k)
      (y := xStar.2)
      heta_convex
      hchi_convex
      heta_le_chi
      hcontact
      hchi_diff

/-- Helper for Lemma 14.4 InactiveBlockSupport helper: the prox-gradient candidate on the current
`x₂`-slice should already satisfy the full optimizer gap bound. This is the remaining x₂-side
structural blocker after the exact-step comparison has been isolated. -/
lemma twoBlockX2ProxCandidateAffineUpperBoundAtStar
    (L2 : PosReal)
    [IsProperExtendedRealFunction g2]
    [Fact (LowerSemicontinuous g2)]
    [Fact (is_convex_function g2)]
    [IsProperExtendedRealFunction g1]
    [Fact (is_convex_function g1)]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : (x1 0, x2 0) ∈ effective_domain F)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_x2_smooth : is_l_smooth_on f2 Set.univ (PosReal.toNNReal L2))
    (xStar : E1 × E2)
    (hxStar : IsMinOn F Set.univ xStar) :
    let xPlus : E2 := T[L2; f2, g2] (x2 k)
    let Gk : E2 := G[L2; f2, g2] (x2 k)
    let quad : ℝ := ((L2 : ℝ) / 2) * ‖xPlus - x2 k‖ ^ (2 : ℕ)
    F (x1 (k + 1), xPlus) ≤
      F xStar + (inner ℝ Gk (xPlus - xStar.2) : EReal) + (quad : EReal) := by
  let xPlus : E2 := T[L2; f2, g2] (x2 k)
  let Gk : E2 := G[L2; f2, g2] (x2 k)
  let quad : ℝ := ((L2 : ℝ) / 2) * ‖xPlus - x2 k‖ ^ (2 : ℕ)
  have hxStar_mem : xStar ∈ effective_domain F := by
    have hmin := (isMinOn_iff.mp hxStar) (x1 0, x2 0) (by simp)
    exact mem_effective_domain.mpr <| lt_of_le_of_lt hmin (mem_effective_domain.mp hx0)
  have hxStar_g2 : xStar.2 ∈ effective_domain g2 :=
    twoBlockSecondPenaltyMemEffectiveDomainOfObjectiveMem f g1 g2 hxStar_mem
  rcases gradient_mapping_support_ineq_real
      (Function.toEReal fun y2 ↦ f (x1 (k + 1), y2))
      g2
      L2
      (interior_effective_domain_point_of_real (fun y2 ↦ f (x1 (k + 1), y2)) (x2 k)) with
    ⟨hxPlus_eff, hprox_raw⟩
  have hsmooth_real :
      f (x1 (k + 1), xPlus) ≤
        f (x1 (k + 1), x2 k) + inner ℝ (∇ f2 (x2 k)) (xPlus - x2 k) + quad := by
    simpa [xPlus, quad, norm_sub_rev] using
      is_l_smooth_on_univ_descent_lemma hf_x2_smooth (x2 k) xPlus
  have hsupport_eta :
      η2 xStar.2 ≥
        η2 (x2 k) + (inner ℝ (∇ f2 (x2 k)) (xStar.2 - x2 k) : EReal) := by
    simpa using
      twoBlockX2InactiveMarginalSupportAtStar
        f g1 g2 x1 x2 k htraj hx0 hf_convex hf_x2_smooth xStar
  have hsmooth_ereal :
      (((f (x1 (k + 1), xPlus) : ℝ) : EReal)) + g1 (x1 (k + 1)) ≤
        η2 (x2 k) + (inner ℝ (∇ f2 (x2 k)) (xPlus - x2 k) : EReal) + (quad : EReal) := by
    have hsmooth_cast :
        (((f (x1 (k + 1), xPlus) : ℝ) : EReal)) ≤
          (((f (x1 (k + 1), x2 k) + inner ℝ (∇ f2 (x2 k)) (xPlus - x2 k) + quad : ℝ) :
              EReal)) := by
      exact_mod_cast hsmooth_real
    calc
      (((f (x1 (k + 1), xPlus) : ℝ) : EReal)) + g1 (x1 (k + 1))
          ≤ (((f (x1 (k + 1), x2 k) + inner ℝ (∇ f2 (x2 k)) (xPlus - x2 k) + quad : ℝ) :
                EReal)) + g1 (x1 (k + 1)) := by
                  simpa [add_assoc, add_left_comm, add_comm] using
                    add_le_add_right hsmooth_cast (g1 (x1 (k + 1)))
      _ = η2 (x2 k) + (inner ℝ (∇ f2 (x2 k)) (xPlus - x2 k) : EReal) + (quad : EReal) := by
        rw [twoBlockX2InactiveMarginalEqCurrentValue f g1 g2 x1 x2 k htraj hx0]
        simp [add_assoc, add_comm, quad]
  have hsupport_transport :
      η2 (x2 k) + (inner ℝ (∇ f2 (x2 k)) (xPlus - x2 k) : EReal) ≤
        η2 xStar.2 + (inner ℝ (∇ f2 (x2 k)) (xPlus - xStar.2) : EReal) := by
    have hsplit_real :
        inner ℝ (∇ f2 (x2 k)) (xStar.2 - x2 k) +
            inner ℝ (∇ f2 (x2 k)) (xPlus - xStar.2) =
          inner ℝ (∇ f2 (x2 k)) (xPlus - x2 k) := by
      rw [← inner_add_right]
      abel
    have hadded :=
      add_le_add_right hsupport_eta
        ((inner ℝ (∇ f2 (x2 k)) (xPlus - xStar.2) : ℝ) : EReal)
    have hsplit :
        (inner ℝ (∇ f2 (x2 k)) (xPlus - x2 k) : EReal) =
          (inner ℝ (∇ f2 (x2 k)) (xStar.2 - x2 k) : EReal) +
            (inner ℝ (∇ f2 (x2 k)) (xPlus - xStar.2) : EReal) := by
      exact congrArg (fun t : ℝ ↦ (t : EReal)) hsplit_real.symm
    calc
      η2 (x2 k) + (inner ℝ (∇ f2 (x2 k)) (xPlus - x2 k) : EReal)
          = η2 (x2 k) +
              (inner ℝ (∇ f2 (x2 k)) (xStar.2 - x2 k) : EReal) +
                (inner ℝ (∇ f2 (x2 k)) (xPlus - xStar.2) : EReal) := by
                  rw [hsplit]
                  simp [add_assoc]
      _ ≤ η2 xStar.2 + (inner ℝ (∇ f2 (x2 k)) (xPlus - xStar.2) : EReal) := by
            have hadded' := hadded
            abel_nf at hadded' ⊢
            exact hadded'
  have hsmooth_star :
      (((f (x1 (k + 1), xPlus) : ℝ) : EReal)) + g1 (x1 (k + 1)) ≤
        η2 xStar.2 + (inner ℝ (∇ f2 (x2 k)) (xPlus - xStar.2) : EReal) + (quad : EReal) := by
    have hquad := add_le_add_right hsupport_transport (quad : EReal)
    exact le_trans hsmooth_ereal <| by
      have hquad' := hquad
      abel_nf at hquad' ⊢
      exact hquad'
  have hg2_xplus_val : (((g2 xPlus).toReal : ℝ) : EReal) = g2 xPlus := by
    exact
      EReal.coe_toReal
        (mem_effective_domain.mp hxPlus_eff).ne
        (‹IsProperExtendedRealFunction g2›.ne_bot xPlus)
  have hg2_xstar_val : (((g2 xStar.2).toReal : ℝ) : EReal) = g2 xStar.2 := by
    exact
      EReal.coe_toReal
        (mem_effective_domain.mp hxStar_g2).ne
        (‹IsProperExtendedRealFunction g2›.ne_bot xStar.2)
  have hprox_real :
      (g2 xPlus).toReal ≤
        (g2 xStar.2).toReal +
          inner ℝ (Gk - ∇ f2 (x2 k)) (xPlus - xStar.2) := by
    have hsupport := hprox_raw xStar.2 hxStar_g2
    have hsupport' :
        inner ℝ (Gk - ∇ f2 (x2 k)) (xStar.2 - xPlus) ≤
          (g2 xStar.2).toReal - (g2 xPlus).toReal := by
      simpa [xPlus, Gk] using hsupport
    have hflip :
        inner ℝ (Gk - ∇ f2 (x2 k)) (xStar.2 - xPlus) =
          -inner ℝ (Gk - ∇ f2 (x2 k)) (xPlus - xStar.2) := by
      have hdisp : xStar.2 - xPlus = -(xPlus - xStar.2) := by
        abel
      rw [hdisp, inner_neg_right]
    rw [hflip] at hsupport'
    linarith
  have hprox_ereal :
      g2 xPlus ≤
        g2 xStar.2 + (inner ℝ (Gk - ∇ f2 (x2 k)) (xPlus - xStar.2) : EReal) := by
    rw [← hg2_xplus_val, ← hg2_xstar_val]
    exact_mod_cast hprox_real
  have hinner_merge :
      (inner ℝ (∇ f2 (x2 k)) (xPlus - xStar.2) : EReal) +
          (inner ℝ (Gk - ∇ f2 (x2 k)) (xPlus - xStar.2) : EReal) =
        (inner ℝ Gk (xPlus - xStar.2) : EReal) := by
    have hinner_merge_real :
        inner ℝ (∇ f2 (x2 k)) (xPlus - xStar.2) +
            inner ℝ (Gk - ∇ f2 (x2 k)) (xPlus - xStar.2) =
          inner ℝ Gk (xPlus - xStar.2) := by
      rw [inner_sub_left]
      linarith
    exact_mod_cast hinner_merge_real
  let linear : EReal := (inner ℝ (∇ f2 (x2 k)) (xPlus - xStar.2) : EReal)
  let residual : EReal :=
    (inner ℝ (Gk - ∇ f2 (x2 k)) (xPlus - xStar.2) : EReal)
  let affine : EReal := (inner ℝ Gk (xPlus - xStar.2) : EReal)
  have hsmooth_star' :
      (((f (x1 (k + 1), xPlus) : ℝ) : EReal)) + g1 (x1 (k + 1)) ≤
        η2 xStar.2 + linear + (quad : EReal) := by
    simpa [linear] using hsmooth_star
  have hprox_ereal' :
      g2 xPlus ≤ g2 xStar.2 + residual := by
    simpa [residual] using hprox_ereal
  have hmerge_eq : linear + residual = affine := by
    simpa [linear, residual, affine] using hinner_merge
  have hcore :
      F (x1 (k + 1), xPlus) ≤
        η2 xStar.2 + g2 xStar.2 + affine + (quad : EReal) := by
    have hsum := add_le_add hsmooth_star' hprox_ereal'
    calc
      F (x1 (k + 1), xPlus)
          = ((((f (x1 (k + 1), xPlus) : ℝ) : EReal)) + g1 (x1 (k + 1))) + g2 xPlus := by
              simp [two_block_alternating_minimization_objective_apply, add_left_comm, add_comm]
      _ ≤
          (η2 xStar.2 + linear + (quad : EReal)) +
            (g2 xStar.2 + residual) := hsum
      _ = η2 xStar.2 + g2 xStar.2 + (linear + residual) + (quad : EReal) := by
            abel_nf
      _ = η2 xStar.2 + g2 xStar.2 + affine + (quad : EReal) := by
            rw [hmerge_eq]
  have htail :
      η2 xStar.2 + g2 xStar.2 + affine + (quad : EReal) ≤
        F xStar + affine + (quad : EReal) := by
    have htail0 :
        η2 xStar.2 + g2 xStar.2 + (affine + (quad : EReal)) ≤
          F xStar + (affine + (quad : EReal)) := by
      have hstar :=
        add_le_add_right
          (twoBlockX2InactiveMarginalAddInactivePenaltyLeObjectiveAtStar f g1 g2 xStar)
          (affine + (quad : EReal))
      abel_nf at hstar ⊢
      exact hstar
    simpa [add_assoc] using htail0
  exact le_trans hcore htail

lemma twoBlockX2ProxCandidateGapLeGradientMapping
    (L2 : PosReal)
    [IsProperExtendedRealFunction g2]
    [Fact (LowerSemicontinuous g2)]
    [Fact (is_convex_function g2)]
    [IsProperExtendedRealFunction g1]
    [Fact (is_convex_function g1)]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : (x1 0, x2 0) ∈ effective_domain F)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_x2_smooth : is_l_smooth_on f2 Set.univ (PosReal.toNNReal L2))
    (xStar : E1 × E2)
    (hxStar : IsMinOn F Set.univ xStar) :
    let xPlus : E2 := T[L2; f2, g2] (x2 k)
    F (x1 (k + 1), xPlus) - F xStar ≤
      (((‖G[L2; f2, g2] (x2 k)‖ * ‖xHalf - xStar‖ : ℝ) : EReal)) := by
  let xPlus : E2 := T[L2; f2, g2] (x2 k)
  let Gk : E2 := G[L2; f2, g2] (x2 k)
  let quad : ℝ := ((L2 : ℝ) / 2) * ‖xPlus - x2 k‖ ^ (2 : ℕ)
  have hcandidate_affine :
      F (x1 (k + 1), xPlus) ≤
        F xStar + (inner ℝ Gk (xPlus - xStar.2) : EReal) + (quad : EReal) := by
    simpa [xPlus, Gk, quad] using
      twoBlockX2ProxCandidateAffineUpperBoundAtStar
        f g1 g2 x1 x2 k L2 htraj hx0 hf_convex hf_x2_smooth xStar hxStar
  have hxplus_eq :
      xPlus = x2 k - (1 / (L2 : ℝ)) • Gk := by
    -- Normalize the second-block prox-gradient trial point into the residual spelling.
    simpa [xPlus, Gk, prox_gradient_operator_apply, prox_gradient_mapping_apply] using
      (prox_grad_operator_eq_sub_gradient_mapping
        (f := Function.toEReal fun y2 ↦ f (x1 (k + 1), y2))
        (g := g2)
        (L := L2)
        (x := interior_effective_domain_point_of_real (fun y2 ↦ f (x1 (k + 1), y2)) (x2 k)))
  have hcore_nonpos :
      inner ℝ Gk (xPlus - x2 k) + quad ≤ 0 := by
    have hdisp : xPlus - x2 k = -((1 / (L2 : ℝ)) • Gk) := by
      rw [hxplus_eq]
      abel
    have hnorm :
        ‖xPlus - x2 k‖ = ‖(1 / (L2 : ℝ)) • Gk‖ := by
      rw [hdisp, norm_neg]
    have hL_nonneg : 0 ≤ (1 / (L2 : ℝ)) := by
      exact one_div_nonneg.mpr (le_of_lt L2.2)
    calc
      inner ℝ Gk (xPlus - x2 k) + quad
          = inner ℝ Gk (-((1 / (L2 : ℝ)) • Gk)) +
              ((L2 : ℝ) / 2) * ‖-((1 / (L2 : ℝ)) • Gk)‖ ^ (2 : ℕ) := by
                dsimp [quad]
                rw [hdisp]
      _ = -((1 / (L2 : ℝ)) * ‖Gk‖ ^ (2 : ℕ)) +
            ((L2 : ℝ) / 2) * (((1 / (L2 : ℝ)) ^ (2 : ℕ)) * ‖Gk‖ ^ (2 : ℕ)) := by
              rw [inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq, norm_neg,
                norm_smul, Real.norm_eq_abs, abs_of_nonneg hL_nonneg]
              ring
      _ = -((1 / (2 * (L2 : ℝ))) * ‖Gk‖ ^ (2 : ℕ)) := by
            field_simp [show (L2 : ℝ) ≠ 0 by exact L2.2.ne']
            ring
      _ ≤ 0 := by
            have hsq : 0 ≤ ‖Gk‖ ^ (2 : ℕ) := by positivity
            have hfac : 0 ≤ (1 / (2 * (L2 : ℝ))) := by
              have hden : 0 < 2 * (L2 : ℝ) := by
                have htwo : (0 : ℝ) < 2 := by norm_num
                have hL : (0 : ℝ) < (L2 : ℝ) := L2.2
                nlinarith
              exact one_div_nonneg.mpr hden.le
            nlinarith
  have htrial_real :
      inner ℝ Gk (xPlus - xStar.2) + quad ≤
        inner ℝ Gk (x2 k - xStar.2) := by
    have hsplit :
        inner ℝ Gk (xPlus - xStar.2) =
          inner ℝ Gk (x2 k - xStar.2) + inner ℝ Gk (xPlus - x2 k) := by
      have hdisp : xPlus - xStar.2 = (x2 k - xStar.2) + (xPlus - x2 k) := by
        abel
      rw [hdisp, inner_add_right]
    linarith
  have htrial_ereal :
      (inner ℝ Gk (xPlus - xStar.2) : EReal) + (quad : EReal) ≤
        (inner ℝ Gk (x2 k - xStar.2) : EReal) := by
    exact_mod_cast htrial_real
  have hcandidate_linear :
      F (x1 (k + 1), xPlus) ≤ F xStar + (inner ℝ Gk (x2 k - xStar.2) : EReal) := by
    exact le_trans hcandidate_affine <|
      by
        simpa [add_assoc, add_left_comm, add_comm] using
          add_le_add_left htrial_ereal (F xStar)
  have hblock :
      ‖x2 k - xStar.2‖ ≤ ‖xHalf - xStar‖ := by
    -- The product norm dominates the active second-block coordinate norm on the half-step pair.
    simpa [two_block_alternating_minimization_half_step] using
      (norm_snd_le ((x1 (k + 1), x2 k) - xStar))
  have hcs_real :
      inner ℝ Gk (x2 k - xStar.2) ≤ ‖Gk‖ * ‖xHalf - xStar‖ := by
    exact
      le_trans
        (real_inner_le_norm Gk (x2 k - xStar.2))
        (mul_le_mul_of_nonneg_left hblock (norm_nonneg _))
  have hcs_ereal :
      (inner ℝ Gk (x2 k - xStar.2) : EReal) ≤
        (((‖Gk‖ * ‖xHalf - xStar‖ : ℝ) : EReal)) := by
    exact_mod_cast hcs_real
  have hfinal :
      F (x1 (k + 1), xPlus) ≤
        F xStar + (((‖Gk‖ * ‖xHalf - xStar‖ : ℝ) : EReal)) := by
    exact le_trans hcandidate_linear <| by
      simpa [add_assoc, add_left_comm, add_comm] using
        add_le_add_left hcs_ereal (F xStar)
  exact EReal.sub_le_of_le_add' hfinal

/-- Helper for Lemma 14.4 InactiveBlockSupport helper (2): if `x1` and `x2` are generated by the
two-block
alternating minimization method and the initial pair `(x1 0, x2 0)` lies in `effective_domain F`,
then the full-step objective gap satisfies
`F(x^{k+1}) - F(x^*) ≤ ‖G^2_{L₂}(x^{k+1/2})‖ * ‖x^{k+1/2} - x^*‖`, with
`x^{k+1} = (x1 (k + 1), x2 (k + 1))` and `x^{k+1/2} = (x1 (k + 1), x2 k)`. Its canonical bridge
is the symmetric partial-infimum support descent on the current half-step fiber. -/
theorem two_block_next_iterate_objective_gap_le_x2_gradient_mapping
    (L2 : PosReal)
    [IsProperExtendedRealFunction g2]
    [Fact (LowerSemicontinuous g2)]
    [Fact (is_convex_function g2)]
    [IsProperExtendedRealFunction g1]
    [Fact (is_convex_function g1)]
    (htraj : is_two_block_alternating_minimization_trajectory f.toEReal g1 g2 x1 x2)
    (hx0 : (x1 0, x2 0) ∈ effective_domain F)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_x2_smooth : is_l_smooth_on f2 Set.univ (PosReal.toNNReal L2))
    (xStar : E1 × E2)
    (hxStar : IsMinOn F Set.univ xStar) :
    F xNext - F xStar ≤
      (((‖G[L2; f2, g2] (x2 k)‖ * ‖xHalf - xStar‖ : ℝ) : EReal)) := by
  let xPlus : E2 := T[L2; f2, g2] (x2 k)
  have hnext_le_candidate : F xNext ≤ F (x1 (k + 1), xPlus) := by
    -- Compare the exact `x₂`-minimizer with the prox-gradient candidate on the half-step slice.
    have hstep :
        IsMinOn
          (two_block_alternating_minimization_x2_objective f.toEReal g1 g2 (x1 (k + 1)))
          Set.univ
          (x2 (k + 1)) := by
      simpa [Nat.succ_eq_add_one] using htraj.step_x2 k
    simpa using (isMinOn_iff.mp hstep) xPlus (by simp)
  have hcandidate_gap :
      F (x1 (k + 1), xPlus) - F xStar ≤
        (((‖G[L2; f2, g2] (x2 k)‖ * ‖xHalf - xStar‖ : ℝ) : EReal)) := by
    -- The remaining gap is exactly the prox-candidate-vs-optimizer estimate.
    simpa [xPlus] using
      twoBlockX2ProxCandidateGapLeGradientMapping
        f g1 g2 x1 x2 k L2 htraj hx0 hf_convex hf_x2_smooth xStar hxStar
  have hcandidate_gap' :
      F (x1 (k + 1), xPlus) ≤
        F xStar + (((‖G[L2; f2, g2] (x2 k)‖ * ‖xHalf - xStar‖ : ℝ) : EReal)) := by
    simpa [add_comm] using
      (EReal.sub_le_iff_le_add
        (.inr (EReal.coe_ne_top _))
        (.inr (EReal.coe_ne_bot _))).mp
        hcandidate_gap
  exact EReal.sub_le_of_le_add' (le_trans hnext_le_candidate hcandidate_gap')

end X2

end

end

/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Trajectory
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ConvexFunction
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ProjectionCycle

@[expose] public section

open scoped RealInnerProductSpace

namespace ConsensusADMM

universe u

namespace ProjectionCycle

/-- A cyclic multiplier family has one positive residual norm at every phase. -/
def HasConstantPositiveResidual {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (γ : ℝ) (ν : ZMod N → E) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ i, ‖residual γ ν i‖ = c

/-- Constant positive residual norm means equality to one positive real at every phase. -/
theorem hasConstantPositiveResidual_iff {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {γ : ℝ} {ν : ZMod N → E} :
    HasConstantPositiveResidual γ ν ↔
      ∃ c : ℝ, 0 < c ∧ ∀ i, ‖residual γ ν i‖ = c := by
  -- Unfolding the predicate exposes exactly the displayed existential condition.
  rfl

/-! A positive common residual norm gives positivity at each individual phase. -/

/-- Every phase of a constant-positive-residual family has positive norm. -/
theorem hasConstantPositiveResidual_pos {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {γ : ℝ} {ν : ZMod N → E}
    (h : HasConstantPositiveResidual γ ν) :
    ∀ i, 0 < ‖residual γ ν i‖ := by
  -- Rewrite each phase norm to the common positive constant.
  rcases h with ⟨c, hc, hconstant⟩
  intro i
  rw [hconstant i]
  exact hc

/-- The `η/ν` Gram blocks are invariant under a simultaneous successor shift. -/
def HasCirculantGram {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (η ν : ZMod N → E) : Prop :=
  (∀ i j, inner ℝ (η (i + 1)) (η (j + 1)) = inner ℝ (η i) (η j)) ∧
    (∀ i j, inner ℝ (η (i + 1)) (ν (j + 1)) = inner ℝ (η i) (ν j)) ∧
    ∀ i j, inner ℝ (ν (i + 1)) (ν (j + 1)) = inner ℝ (ν i) (ν j)

/-- Circulant Gram data consists of the two diagonal blocks and one mixed block. -/
theorem hasCirculantGram_iff {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {η ν : ZMod N → E} :
    HasCirculantGram η ν ↔
      (∀ i j, inner ℝ (η (i + 1)) (η (j + 1)) = inner ℝ (η i) (η j)) ∧
        (∀ i j, inner ℝ (η (i + 1)) (ν (j + 1)) = inner ℝ (η i) (ν j)) ∧
        ∀ i j, inner ℝ (ν (i + 1)) (ν (j + 1)) = inner ℝ (ν i) (ν j) := by
  -- Unfolding the predicate exposes exactly the displayed three Gram conditions.
  rfl

end ProjectionCycle

/-- A projection cycle with constant positive residual norm and circulant Gram blocks. -/
def IsCyclicReduction {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (γ : ℝ) (η ν : ZMod N → E) : Prop :=
  IsProjectionCycle γ η ν ∧
    ProjectionCycle.HasConstantPositiveResidual γ ν ∧
    ProjectionCycle.HasCirculantGram η ν

/-- A cyclic reduction exposes its cycle, residual, and Gram conditions together. -/
theorem isCyclicReduction_iff {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {γ : ℝ} {η ν : ZMod N → E} :
    IsCyclicReduction γ η ν ↔
      IsProjectionCycle γ η ν ∧
        ProjectionCycle.HasConstantPositiveResidual γ ν ∧
        ProjectionCycle.HasCirculantGram η ν := by
  -- Unfolding the predicate exposes the projection, residual, and Gram conjuncts.
  rfl

/-! The product-period hypothesis is consumed componentwise by the reduction
construction.  Keeping these projections named avoids repeating tuple
coercion proofs in the substantive construction. -/

/-- Periodicity of a post-update tuple implies periodicity of its `x` component. -/
private lemma periodicPostUpdate_x {N : ℕ} {E : Type u}
    (x y dual : ℕ → E)
    (hperiodic : Function.Periodic
      (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) N) :
    Function.Periodic (fun k ↦ x (k + 1)) N := by
  intro k
  exact congrArg Prod.fst (hperiodic k)

/-- Periodicity of a post-update tuple implies periodicity of its `y` component. -/
private lemma periodicPostUpdate_y {N : ℕ} {E : Type u}
    (x y dual : ℕ → E)
    (hperiodic : Function.Periodic
      (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) N) :
    Function.Periodic (fun k ↦ y (k + 1)) N := by
  intro k
  exact congrArg (fun z ↦ z.2.1) (hperiodic k)

/-- Periodicity of a post-update tuple implies periodicity of its multiplier component. -/
private lemma periodicPostUpdate_dual {N : ℕ} {E : Type u}
    (x y dual : ℕ → E)
    (hperiodic : Function.Periodic
      (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) N) :
    Function.Periodic (fun k ↦ dual (k + 1)) N := by
  intro k
  exact congrArg (fun z ↦ z.2.2) (hperiodic k)

/-- The post-update primal residual inherits the period of its tuple. -/
private lemma periodicPostUpdate_residual {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y dual : ℕ → E)
    (hperiodic : Function.Periodic
      (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) N) :
    Function.Periodic (fun k ↦ x (k + 1) - y (k + 1)) N := by
  intro k
  simpa only using congrArg₂ (fun a b : E ↦ a - b)
    (periodicPostUpdate_x x y dual hperiodic k)
    (periodicPostUpdate_y x y dual hperiodic k)

/-- A periodic post-update sequence evaluated one step before a phase agrees
with the cyclic predecessor of that phase. -/
private lemma periodicPostUpdate_predecessor {N : ℕ} {E : Type u} [NeZero N]
    (s : ℕ → E) (hperiodic : Function.Periodic (fun k ↦ s (k + 1)) N)
    (i : ZMod N) :
    s (i.val + N) = s ((i - 1).val + 1) := by
  -- Reduce the natural predecessor index modulo the period and identify its
  -- residue with subtraction by one in `ZMod N`.
  have hNpos : 0 < N := NeZero.pos N
  have hcast : ((i.val + N - 1 : ℕ) : ZMod N) = i - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_zmod_val,
      ZMod.natCast_self, add_zero, Nat.cast_one]
  have hindex : (i.val + N - 1) % N = (i - 1).val := by
    simpa only [ZMod.val_natCast] using congrArg ZMod.val hcast
  have hmod := hperiodic.map_mod_nat (i.val + N - 1)
  rw [hindex] at hmod
  have harith : i.val + N - 1 + 1 = i.val + N := by
    omega
  rw [harith] at hmod
  exact hmod.symm

/-- A periodic post-update sequence evaluated one full period after a phase
agrees with that phase. -/
private lemma periodicPostUpdate_current {N : ℕ} {E : Type u}
    (s : ℕ → E) (hperiodic : Function.Periodic (fun k ↦ s (k + 1)) N)
    (i : ZMod N) :
    s (i.val + N + 1) = s (i.val + 1) := by
  -- Apply periodicity to the post-update index represented by the phase.
  simpa only [add_assoc] using hperiodic i.val

/-- The multiplier recurrence of a trajectory holds at every post-update phase. -/
private lemma postUpdate_multiplierRecurrence {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {γ : ℝ} {f g : E → EReal} {x y dual : ℕ → E}
    (htrajectory : IsTrajectory γ f g x y dual) (k : ℕ) :
    dual (k + 1) = dual k + γ • (x (k + 1) - y (k + 1)) := by
  exact ((trajectory_iff.mp htrajectory) k).2.2.2.2

/-- The centered finite product of a post-update sequence at a cyclic phase. -/
noncomputable def centeredProduct {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NeZero N]
    (s : ℕ → E) (i : ZMod N) :
    PiLp 2 (fun _ : ZMod N ↦ E) :=
  WithLp.toLp 2 (fun j : ZMod N ↦
    s ((i + j).val + 1) - (N : ℝ)⁻¹ • ∑ k : ZMod N, s (k.val + 1))

/-- Coordinate evaluation of a centered finite product. -/
private lemma centeredProduct_apply {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NeZero N]
    (s : ℕ → E) (i j : ZMod N) :
    centeredProduct s i j =
      s ((i + j).val + 1) - (N : ℝ)⁻¹ • ∑ k : ZMod N, s (k.val + 1) := by
  rfl

/-- Translation of a finite ZMod-indexed family preserves its additive sum. -/
private lemma phaseSumShift {N : ℕ} {A : Type*} [AddCommMonoid A] [NeZero N]
    (q : ZMod N → A) (i : ZMod N) :
    ∑ j : ZMod N, q (i + j) = ∑ j : ZMod N, q j := by
  -- Addition by a fixed phase is an equivalence of the finite index type.
  change ∑ j : ZMod N, q ((Equiv.addLeft i) j) = ∑ j : ZMod N, q j
  exact Equiv.sum_comp (Equiv.addLeft i) q

/-- Centering a finite cyclic product makes the sum of its phases vanish. -/
private lemma centeredProduct_sum_zero {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NeZero N]
    (s : ℕ → E) :
    ∑ i : ZMod N, centeredProduct s i = 0 := by
  -- Evaluate one product coordinate and reindex the translated first sum.
  apply PiLp.ext
  intro j
  let coordinate : PiLp 2 (fun _ : ZMod N ↦ E) →ₗ[ℝ] E :=
    PiLp.projₗ (p := 2) (𝕜 := ℝ) (β := fun _ : ZMod N ↦ E) j
  change coordinate (∑ i : ZMod N, centeredProduct s i) = coordinate 0
  rw [map_sum]
  change (∑ i : ZMod N, centeredProduct s i j) = 0
  simp only [centeredProduct_apply, Finset.sum_sub_distrib]
  -- The constant centering term occurs once for each of the `N` phases.
  have shifted :
      (∑ k : ZMod N, s ((k + j).val + 1)) = ∑ k : ZMod N, s (k.val + 1) := by
    simpa only [add_comm] using phaseSumShift (fun k : ZMod N ↦ s (k.val + 1)) j
  rw [shifted, Finset.sum_const, Finset.card_univ, ZMod.card,
    ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne N)), one_smul,
    sub_self]

/-- Advancing the phase of a centered product shifts its product coordinate. -/
private lemma centeredProduct_shift {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NeZero N]
    (s : ℕ → E) (i j : ZMod N) :
    centeredProduct s (i + 1) j = centeredProduct s i (j + 1) := by
  -- The two translated coordinates have the same phase by associativity and commutativity.
  rw [centeredProduct_apply, centeredProduct_apply]
  congr 2
  rw [add_assoc, add_comm (1 : ZMod N) j, ← add_assoc]

/-- Iterated phase advance can be moved from the phase index to the product coordinate. -/
private lemma centeredProduct_shift_iterate {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NeZero N]
    (s : ℕ → E) (i j : ZMod N) (n : ℕ) :
    centeredProduct s (i + (n : ZMod N)) j =
      centeredProduct s i (j + (n : ZMod N)) := by
  -- Repeatedly apply the one-step shift interface, then normalize the final
  -- successor addition in `ZMod N`.
  induction n generalizing i j with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ]
      calc
        centeredProduct s (i + ((n : ZMod N) + 1)) j =
            centeredProduct s ((i + (n : ZMod N)) + 1) j := by
              rw [add_assoc]
        _ = centeredProduct s (i + (n : ZMod N)) (j + 1) :=
          centeredProduct_shift s (i + (n : ZMod N)) j
        _ = centeredProduct s i ((j + 1) + (n : ZMod N)) :=
          ih (i := i) (j := j + 1)
        _ = centeredProduct s i (j + ((n : ZMod N) + 1)) := by
          rw [add_assoc, add_comm (1 : ZMod N) (n : ZMod N), ← add_assoc]

/-- Simultaneously translating both phase indices preserves the inner product
of centered cyclic products. -/
private lemma centeredProductInnerShift {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NeZero N]
    (s t : ℕ → E) (i j k : ZMod N) :
    inner ℝ (centeredProduct s (i + k)) (centeredProduct t (j + k)) =
      inner ℝ (centeredProduct s i) (centeredProduct t j) := by
  -- Represent the translating phase by its natural value and move that
  -- iterate into the product coordinate in both factors.
  rw [← ZMod.natCast_zmod_val k, PiLp.inner_apply, PiLp.inner_apply]
  simp_rw [centeredProduct_shift_iterate]
  simpa only [add_comm] using phaseSumShift
    (fun l : ZMod N ↦ inner ℝ (centeredProduct s i l) (centeredProduct t j l))
    (k.val : ZMod N)

/-- The residual of the centered multiplier product is the cyclic product of
the post-update primal residuals. -/
private lemma centeredTrajectoryResidual_apply {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NeZero N]
    {γ : ℝ} {f g : E → EReal} (x y dual : ℕ → E)
    (hperiodic : Function.Periodic
      (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) N)
    (htrajectory : IsTrajectory γ f g x y dual) (hγ : γ ≠ 0)
    (i j : ZMod N) :
    ProjectionCycle.residual γ (centeredProduct dual) i j =
      x ((i + j).val + 1) - y ((i + j).val + 1) := by
  -- Evaluate the multiplier recurrence one full period after the chosen
  -- phase so its predecessor is itself a post-update state.
  have hxperiodic := periodicPostUpdate_x x y dual hperiodic
  have hyperiodic := periodicPostUpdate_y x y dual hperiodic
  have hdualperiodic := periodicPostUpdate_dual x y dual hperiodic
  have hrec := postUpdate_multiplierRecurrence htrajectory ((i + j).val + N)
  rw [periodicPostUpdate_current dual hdualperiodic (i + j),
    periodicPostUpdate_predecessor dual hdualperiodic (i + j),
    periodicPostUpdate_current x hxperiodic (i + j),
    periodicPostUpdate_current y hyperiodic (i + j)] at hrec
  have hphase : i - 1 + j = i + j - 1 := by
    abel
  rw [ProjectionCycle.residual_apply]
  change γ⁻¹ • (centeredProduct dual i j - centeredProduct dual (i - 1) j) = _
  rw [centeredProduct_apply, centeredProduct_apply, hphase, hrec]
  have hcollapse :
      (dual ((i + j - 1).val + 1) +
            γ • (x ((i + j).val + 1) - y ((i + j).val + 1)) -
          (N : ℝ)⁻¹ • ∑ k : ZMod N, dual (k.val + 1)) -
        (dual ((i + j - 1).val + 1) -
          (N : ℝ)⁻¹ • ∑ k : ZMod N, dual (k.val + 1)) =
        γ • (x ((i + j).val + 1) - y ((i + j).val + 1)) := by
    module
  rw [hcollapse, smul_smul, inv_mul_cancel₀ hγ, one_smul]

/-- The first vertex of the centered products is the centered cyclic product
of the first primal block. -/
private lemma centeredTrajectoryXVertex_apply {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NeZero N]
    {γ : ℝ} {f g : E → EReal} (x y dual : ℕ → E)
    (hperiodic : Function.Periodic
      (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) N)
    (htrajectory : IsTrajectory γ f g x y dual) (hγ : γ ≠ 0)
    (i j : ZMod N) :
    ProjectionCycle.xVertex γ (centeredProduct y) (centeredProduct dual) i j =
      x ((i + j).val + 1) -
        (N : ℝ)⁻¹ • ∑ k : ZMod N, y (k.val + 1) := by
  -- Add the centered `y` coordinate to the residual coordinate and cancel
  -- the current `y` value.
  rw [ProjectionCycle.xVertex_apply]
  change centeredProduct y i j +
      ProjectionCycle.residual γ (centeredProduct dual) i j = _
  rw [centeredProduct_apply,
    centeredTrajectoryResidual_apply x y dual hperiodic htrajectory hγ]
  module

/-- The first normal of the centered products is the generated first-block
normal translated by the mean multiplier. -/
private lemma centeredTrajectoryFirstNormal_apply {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NeZero N]
    {γ : ℝ} {f g : E → EReal} (x y dual : ℕ → E)
    (hperiodic : Function.Periodic
      (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) N)
    (htrajectory : IsTrajectory γ f g x y dual) (hγ : γ ≠ 0)
    (i j : ZMod N) :
    ProjectionCycle.firstNormal γ (centeredProduct y) (centeredProduct dual) i j =
      y ((i + j - 1).val + 1) - dual ((i + j - 1).val + 1) -
        x ((i + j).val + 1) +
          (N : ℝ)⁻¹ • ∑ k : ZMod N, dual (k.val + 1) := by
  -- Expand the predecessor products and the centered first vertex, then
  -- cancel the common primal mean.
  have hphase : i - 1 + j = i + j - 1 := by
    abel
  rw [ProjectionCycle.firstNormal_apply]
  change centeredProduct y (i - 1) j - centeredProduct dual (i - 1) j -
      ProjectionCycle.xVertex γ (centeredProduct y) (centeredProduct dual) i j = _
  rw [centeredProduct_apply, centeredProduct_apply, hphase,
    centeredTrajectoryXVertex_apply x y dual hperiodic htrajectory hγ]
  module

/-- The second normal of the centered products is the generated second-block
normal translated by the negative mean multiplier. -/
private lemma centeredTrajectorySecondNormal_apply {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NeZero N]
    {γ : ℝ} {f g : E → EReal} (x y dual : ℕ → E)
    (hperiodic : Function.Periodic
      (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) N)
    (htrajectory : IsTrajectory γ f g x y dual) (hγ : γ ≠ 0)
    (i j : ZMod N) :
    ProjectionCycle.secondNormal γ (centeredProduct dual) i j =
      dual ((i + j - 1).val + 1) +
        (x ((i + j).val + 1) - y ((i + j).val + 1)) -
          (N : ℝ)⁻¹ • ∑ k : ZMod N, dual (k.val + 1) := by
  -- Expand the predecessor multiplier product and insert the residual
  -- coordinate supplied by the multiplier recurrence.
  have hphase : i - 1 + j = i + j - 1 := by
    abel
  rw [ProjectionCycle.secondNormal_apply]
  change centeredProduct dual (i - 1) j +
      ProjectionCycle.residual γ (centeredProduct dual) i j = _
  rw [centeredProduct_apply, hphase,
    centeredTrajectoryResidual_apply x y dual hperiodic htrajectory hγ]
  module

/-- Pairwise support inequalities for a finite zero-sum family also give
support against the origin. -/
private lemma ProjectionCycle.nonselfSupportsOfPairwiseAndSumZero
    {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NeZero N]
    (p n : ZMod N → E) (hsum : ∑ i, p i = 0)
    (hpair : ∀ i j, 0 ≤ inner ℝ (n i) (p i - p j)) :
    ProjectionCycle.NonselfSupports p n := by
  intro i
  refine ⟨?_, ?_⟩
  · -- Average the pairwise inequalities over the second phase.  The zero-sum
    -- hypothesis leaves a positive scalar multiple of the origin support.
    have hsumnonneg : 0 ≤ ∑ j, inner ℝ (n i) (p i - p j) :=
      Finset.sum_nonneg fun j _ ↦ hpair i j
    have hsum_eq :
        (∑ j, inner ℝ (n i) (p i - p j)) =
          (N : ℝ) * inner ℝ (n i) (p i) := by
      rw [← inner_sum, Finset.sum_sub_distrib, Finset.sum_const, hsum, sub_zero,
        ← Nat.cast_smul_eq_nsmul ℝ, real_inner_smul_right, Finset.card_univ, ZMod.card]
    rw [hsum_eq] at hsumnonneg
    have hNreal : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
    nlinarith
  · intro j hj
    exact hpair i j

/-- The post-update primal residuals of a periodic trajectory sum to zero over
one period. -/
private lemma periodicTrajectoryResidual_sum_zero {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NeZero N]
    {γ : ℝ} {f g : E → EReal} (x y dual : ℕ → E)
    (htrajectory : IsTrajectory γ f g x y dual)
    (hperiodic : Function.Periodic
      (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) N)
    (hγ : γ ≠ 0) :
    ∑ i : ZMod N, (x (i.val + 1) - y (i.val + 1)) = 0 := by
  -- Sum the multiplier recurrence over all phases.  Cyclic reindexing makes
  -- the current and predecessor multiplier sums cancel.
  have hxperiodic := periodicPostUpdate_x x y dual hperiodic
  have hyperiodic := periodicPostUpdate_y x y dual hperiodic
  have hdualperiodic := periodicPostUpdate_dual x y dual hperiodic
  have hrec (i : ZMod N) :
      γ • (x (i.val + 1) - y (i.val + 1)) =
        dual (i.val + 1) - dual ((i - 1).val + 1) := by
    have h := postUpdate_multiplierRecurrence htrajectory (i.val + N)
    rw [periodicPostUpdate_current dual hdualperiodic i,
      periodicPostUpdate_predecessor dual hdualperiodic i,
      periodicPostUpdate_current x hxperiodic i,
      periodicPostUpdate_current y hyperiodic i] at h
    rw [h]
    module
  have hpredsum :
      (∑ i : ZMod N, dual ((i - 1).val + 1)) =
        ∑ i : ZMod N, dual (i.val + 1) := by
    simpa only [sub_eq_add_neg, add_comm] using
      phaseSumShift (fun i : ZMod N ↦ dual (i.val + 1)) (-1)
  have hscaled : γ • (∑ i : ZMod N, (x (i.val + 1) - y (i.val + 1))) = 0 := by
    rw [Finset.smul_sum]
    simp_rw [hrec]
    rw [Finset.sum_sub_distrib, hpredsum, sub_self]
  calc
    (∑ i : ZMod N, (x (i.val + 1) - y (i.val + 1))) =
        γ⁻¹ • γ • (∑ i : ZMod N, (x (i.val + 1) - y (i.val + 1))) := by
          rw [inv_smul_smul₀ hγ]
    _ = 0 := by rw [hscaled, smul_zero]

/-- The first-vertex family of the centered trajectory products is exactly the
centered product of the first primal block. -/
private lemma centeredTrajectoryXVertex_eq {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NeZero N]
    {γ : ℝ} {f g : E → EReal} (x y dual : ℕ → E)
    (htrajectory : IsTrajectory γ f g x y dual)
    (hperiodic : Function.Periodic
      (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) N)
    (hγ : γ ≠ 0) (i : ZMod N) :
    ProjectionCycle.xVertex γ (centeredProduct y) (centeredProduct dual) i =
      centeredProduct x i := by
  -- Multiplier closure identifies the `x` and `y` means; the coordinate
  -- formula then becomes the centered `x` product.
  have hresidual :=
    periodicTrajectoryResidual_sum_zero x y dual htrajectory hperiodic hγ
  have hmeans :
      (∑ k : ZMod N, x (k.val + 1)) = ∑ k : ZMod N, y (k.val + 1) := by
    rw [Finset.sum_sub_distrib, sub_eq_zero] at hresidual
    exact hresidual
  apply PiLp.ext
  intro j
  rw [centeredTrajectoryXVertex_apply x y dual hperiodic htrajectory hγ,
    centeredProduct_apply, hmeans]

/-- A pair of finite zero-sum families spans at most twice the index size minus
    two directions. -/
private lemma zeroSumSpanRankBound {K V ι : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [Fintype ι] [Nonempty ι]
    (a b : ι → V) (i0 : ι)
    (ha : ∑ i, a i = 0) (hb : ∑ i, b i = 0) :
    Module.finrank K (Submodule.span K (Set.range a ∪ Set.range b)) ≤
      2 * Fintype.card ι - 2 := by
  classical
  let a' : {i : ι // i ≠ i0} → V := fun i ↦ a i
  let b' : {i : ι // i ≠ i0} → V := fun i ↦ b i
  let sA : Finset V := Finset.univ.image a'
  let sB : Finset V := Finset.univ.image b'
  let s : Finset V := sA ∪ sB
  have hcard_subtype : Fintype.card {i : ι // i ≠ i0} = Fintype.card ι - 1 := by
    simp [Fintype.card_subtype_compl]
  have ha_mem : ∀ i, a i ∈ Submodule.span K (s : Set V) := by
    intro i
    by_cases hi : i = i0
    · subst i
      have hsum : a i0 + ∑ j : {j : ι // j ≠ i0}, a j = 0 := by
        simpa only [Fintype.sum_eq_add_sum_subtype_ne a i0] using ha
      have hsum_mem : (∑ j : {j : ι // j ≠ i0}, a j) ∈
          Submodule.span K (s : Set V) := by
        apply Submodule.sum_mem
        intro j hj
        apply Submodule.subset_span
        have hjA : a j ∈ sA := by
          exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
        have : a j ∈ (sA : Set V) ∪ (sB : Set V) :=
          Set.mem_union_left _ (show a j ∈ (sA : Set V) from hjA)
        simpa [s] using this
      rw [add_eq_zero_iff_eq_neg] at hsum
      rw [hsum]
      exact Submodule.neg_mem _ hsum_mem
    · apply Submodule.subset_span
      have hiA : a i ∈ sA := by
        exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
      have : a i ∈ (sA : Set V) ∪ (sB : Set V) :=
        Set.mem_union_left _ (show a i ∈ (sA : Set V) from hiA)
      simpa [s] using this
  have hb_mem : ∀ i, b i ∈ Submodule.span K (s : Set V) := by
    intro i
    by_cases hi : i = i0
    · subst i
      have hsum : b i0 + ∑ j : {j : ι // j ≠ i0}, b j = 0 := by
        simpa only [Fintype.sum_eq_add_sum_subtype_ne b i0] using hb
      have hsum_mem : (∑ j : {j : ι // j ≠ i0}, b j) ∈
          Submodule.span K (s : Set V) := by
        apply Submodule.sum_mem
        intro j hj
        apply Submodule.subset_span
        have hjB : b j ∈ sB := by
          exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
        have : b j ∈ (sA : Set V) ∪ (sB : Set V) :=
          Set.mem_union_right _ (show b j ∈ (sB : Set V) from hjB)
        simpa [s] using this
      rw [add_eq_zero_iff_eq_neg] at hsum
      rw [hsum]
      exact Submodule.neg_mem _ hsum_mem
    · apply Submodule.subset_span
      have hiB : b i ∈ sB := by
        exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
      have : b i ∈ (sA : Set V) ∪ (sB : Set V) :=
        Set.mem_union_right _ (show b i ∈ (sB : Set V) from hiB)
      simpa [s] using this
  have hspan : Submodule.span K (Set.range a ∪ Set.range b) ≤
      Submodule.span K (s : Set V) := by
    apply Submodule.span_le.mpr
    intro z hz
    rcases hz with hz | hz
    · rcases hz with ⟨i, rfl⟩
      exact ha_mem i
    · rcases hz with ⟨i, rfl⟩
      exact hb_mem i
  have hdim : Module.finrank K (Submodule.span K (s : Set V)) ≤ s.card :=
    finrank_span_finset_le_card s
  have hcardA : sA.card ≤ Fintype.card ι - 1 := by
    calc
      sA.card ≤ Fintype.card {i : ι // i ≠ i0} := by
        simpa [sA] using (Finset.card_image_le :
          (Finset.univ.image a').card ≤ Finset.univ.card)
      _ = Fintype.card ι - 1 := hcard_subtype
  have hcardB : sB.card ≤ Fintype.card ι - 1 := by
    calc
      sB.card ≤ Fintype.card {i : ι // i ≠ i0} := by
        simpa [sB] using (Finset.card_image_le :
          (Finset.univ.image b').card ≤ Finset.univ.card)
      _ = Fintype.card ι - 1 := hcard_subtype
  have hcardS : s.card ≤ 2 * Fintype.card ι - 2 := by
    calc
      s.card = (sA ∪ sB).card := by rfl
      _ ≤ sA.card + sB.card := Finset.card_union_le sA sB
      _ ≤ (Fintype.card ι - 1) + (Fintype.card ι - 1) :=
        Nat.add_le_add hcardA hcardB
      _ = 2 * Fintype.card ι - 2 := by omega
  exact (Submodule.finrank_mono hspan).trans (hdim.trans hcardS)

/-- Cyclic-reduction data is preserved by a real linear isometry. -/
private lemma isCyclicReduction_compLinearIsometry
    {N : ℕ} {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E →ₗᵢ[ℝ] F) (γ : ℝ) (η ν : ZMod N → E)
    (hcycle : IsCyclicReduction γ η ν) :
    IsCyclicReduction γ (fun i ↦ e (η i)) (fun i ↦ e (ν i)) := by
  have residual_map : ∀ i,
      ProjectionCycle.residual γ (fun j ↦ e (ν j)) i =
        e (ProjectionCycle.residual γ ν i) := by
    intro i
    simp only [ProjectionCycle.residual_apply, LinearIsometry.map_smul,
      LinearIsometry.map_sub]
  have vertex_map : ∀ i,
      ProjectionCycle.xVertex γ (fun j ↦ e (η j)) (fun j ↦ e (ν j)) i =
        e (ProjectionCycle.xVertex γ η ν i) := by
    intro i
    rw [ProjectionCycle.xVertex_apply, ProjectionCycle.xVertex_apply,
      residual_map, LinearIsometry.map_add]
  have first_normal_map : ∀ i,
      ProjectionCycle.firstNormal γ (fun j ↦ e (η j)) (fun j ↦ e (ν j)) i =
        e (ProjectionCycle.firstNormal γ η ν i) := by
    intro i
    rw [ProjectionCycle.firstNormal_apply, ProjectionCycle.firstNormal_apply,
      vertex_map, LinearIsometry.map_sub, LinearIsometry.map_sub]
  have second_normal_map : ∀ i,
      ProjectionCycle.secondNormal γ (fun j ↦ e (ν j)) i =
        e (ProjectionCycle.secondNormal γ ν i) := by
    intro i
    rw [ProjectionCycle.secondNormal_apply, ProjectionCycle.secondNormal_apply,
      residual_map, LinearIsometry.map_add]
  rcases hcycle with ⟨hprojection, hresidual, hgram⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro i
      refine ⟨?_, ?_⟩
      · rw [first_normal_map, vertex_map, LinearIsometry.inner_map_map]
        exact (hprojection.1 i).1
      · intro j hj
        rw [first_normal_map, vertex_map, vertex_map, ← LinearIsometry.map_sub,
          LinearIsometry.inner_map_map]
        exact (hprojection.1 i).2 j hj
    · intro i
      refine ⟨?_, ?_⟩
      · rw [second_normal_map, LinearIsometry.inner_map_map]
        exact (hprojection.2 i).1
      · intro j hj
        rw [second_normal_map, ← LinearIsometry.map_sub,
          LinearIsometry.inner_map_map]
        exact (hprojection.2 i).2 j hj
  · rcases hresidual with ⟨c, hc, hconstant⟩
    refine ⟨c, hc, ?_⟩
    intro i
    rw [residual_map, LinearIsometry.norm_map]
    exact hconstant i
  · refine ⟨?_, ?_, ?_⟩
    · intro i j
      simpa only [LinearIsometry.inner_map_map] using hgram.1 i j
    · intro i j
      simpa only [LinearIsometry.inner_map_map] using hgram.2.1 i j
    · intro i j
      simpa only [LinearIsometry.inner_map_map] using hgram.2.2 i j

/-! The next two lemmas expose the finite supporting-plane consequence of a
    proximal block update.  The extended-real cancellation is kept here so
    that the cyclic construction below only sees real inequalities. -/

/-- Convexity bounds the value on a segment between two finite points. -/
private lemma convexEpigraphSegmentBound {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → EReal} (hf : ADMM.IsClosedProperConvex f)
    {p z : E} (hp_top : f p ≠ ⊤) (hz_top : f z ≠ ⊤)
    (hp_bot : f p ≠ ⊥) (hz_bot : f z ≠ ⊥)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    f ((1 - t) • p + t • z) ≤
      (((1 - t) * (f p).toReal + t * (f z).toReal : ℝ) : EReal) := by
  have hp : (p, (f p).toReal) ∈ {q : E × ℝ | f q.1 ≤ (q.2 : EReal)} := by
    simp only [Set.mem_setOf_eq, EReal.coe_toReal hp_top hp_bot, le_refl]
  have hz : (z, (f z).toReal) ∈ {q : E × ℝ | f q.1 ≤ (q.2 : EReal)} := by
    simp only [Set.mem_setOf_eq, EReal.coe_toReal hz_top hz_bot, le_refl]
  have hconv := hf.epigraph_convex hp hz (sub_nonneg.mpr ht1) ht0
    (by linarith)
  simpa only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_mk,
    smul_eq_mul, one_mul, EReal.coe_toReal hp_top hp_bot,
    EReal.coe_toReal hz_top hz_bot] using hconv

/-- A finite global minimizer of a convex proximal objective satisfies its
supporting-plane inequality. -/
private lemma proximalMinimizerSupportingInequality {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : E → EReal} (hF : ADMM.IsClosedProperConvex F)
    {p z v c : E} (hp_top : F p ≠ ⊤) (hz_top : F z ≠ ⊤)
    (hmin : ∀ w,
      F p + ((inner ℝ v (p - c) + ‖p - c‖ ^ 2 / 2 : ℝ) : EReal) ≤
        F w + ((inner ℝ v (w - c) + ‖w - c‖ ^ 2 / 2 : ℝ) : EReal)) :
    (F p).toReal - (F z).toReal ≤ inner ℝ (c - v - p) (p - z) := by
  -- Compare the minimizer with shrinking points on the segment from `p` to
  -- `z`; convexity controls the extended-real function value there.
  have hbound : ∀ n : ℕ,
      (F p).toReal - (F z).toReal ≤
        inner ℝ (c - v - p) (p - z) +
          (1 / ((n : ℝ) + 1)) * (‖z - p‖ ^ 2 / 2) := by
    intro n
    let t : ℝ := 1 / ((n : ℝ) + 1)
    have ht_pos : 0 < t := by
      dsimp [t]
      positivity
    have ht_one : t ≤ 1 := by
      dsimp [t]
      rw [div_le_one (by positivity)]
      norm_num
    let q : E := (1 - t) • p + t • z
    have hsegment : F q ≤
        (((1 - t) * (F p).toReal + t * (F z).toReal : ℝ) : EReal) := by
      exact convexEpigraphSegmentBound hF hp_top hz_top (hF.ne_bot p) (hF.ne_bot z)
        ht_pos.le ht_one
    have hereal := (hmin q).trans (add_le_add_left hsegment _)
    have hreal :
        (F p).toReal + (inner ℝ v (p - c) + ‖p - c‖ ^ 2 / 2) ≤
          ((1 - t) * (F p).toReal + t * (F z).toReal) +
            (inner ℝ v (q - c) + ‖q - c‖ ^ 2 / 2) := by
      have hereal' :
          ((F p).toReal : EReal) +
              ((inner ℝ v (p - c) + ‖p - c‖ ^ 2 / 2 : ℝ) : EReal) ≤
            (((1 - t) * (F p).toReal + t * (F z).toReal : ℝ) : EReal) +
              ((inner ℝ v (q - c) + ‖q - c‖ ^ 2 / 2 : ℝ) : EReal) := by
        calc
          ((F p).toReal : EReal) +
                ((inner ℝ v (p - c) + ‖p - c‖ ^ 2 / 2 : ℝ) : EReal) =
              F p + ((inner ℝ v (p - c) + ‖p - c‖ ^ 2 / 2 : ℝ) : EReal) := by
                rw [EReal.coe_toReal hp_top (hF.ne_bot p)]
          _ ≤ _ := hereal
      apply EReal.coe_le_coe_iff.mp
      simpa only [← EReal.coe_add] using hereal'
    have hq_sub : q - c = (p - c) + t • (z - p) := by
      dsimp [q]
      module
    have hlinear :
        inner ℝ v (z - p) + inner ℝ (p - c) (z - p) =
          inner ℝ (c - v - p) (p - z) := by
      simp only [inner_sub_left, inner_sub_right]
      ring
    have hquadratic :
        inner ℝ v (q - c) + ‖q - c‖ ^ 2 / 2 =
          inner ℝ v (p - c) + ‖p - c‖ ^ 2 / 2 +
            t * inner ℝ (c - v - p) (p - z) +
              t ^ 2 * (‖z - p‖ ^ 2 / 2) := by
      rw [hq_sub, inner_add_right, real_inner_smul_right, norm_add_sq_real,
        real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
      nlinarith [hlinear]
    rw [hquadratic] at hreal
    dsimp [t] at hreal ⊢
    nlinarith
  -- The quadratic remainder tends to zero, leaving the desired support bound.
  have htendsto : Filter.Tendsto
      (fun n : ℕ ↦ inner ℝ (c - v - p) (p - z) +
        (1 / ((n : ℝ) + 1)) * (‖z - p‖ ^ 2 / 2))
      Filter.atTop (nhds (inner ℝ (c - v - p) (p - z))) := by
    have hconst : Filter.Tendsto
        (fun _ : ℕ ↦ inner ℝ (c - v - p) (p - z)) Filter.atTop
        (nhds (inner ℝ (c - v - p) (p - z))) := tendsto_const_nhds
    simpa only [zero_mul, add_zero] using
      hconst.add
        (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (‖z - p‖ ^ 2 / 2))
  exact ge_of_tendsto' htendsto hbound

/-- The first block of a periodic trajectory supplies a support inequality
between any two cyclic phase points. -/
private lemma periodicTrajectoryFirstSupport {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NeZero N]
    {γ : ℝ} {f g : E → EReal} (x y dual : ℕ → E)
    (hf : ADMM.IsClosedProperConvex f)
    (htrajectory : IsTrajectory γ f g x y dual)
    (hperiodic : Function.Periodic
      (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) N)
    (i l : ZMod N) :
    (f (x (i.val + 1))).toReal - (f (x (l.val + 1))).toReal ≤
      inner ℝ
        (y ((i - 1).val + 1) - dual ((i - 1).val + 1) - x (i.val + 1))
        (x (i.val + 1) - x (l.val + 1)) := by
  -- Apply the proximal support lemma at update `i.val + N`; this choice makes
  -- both the current point and its predecessor periodic post-update states.
  have hxperiodic := periodicPostUpdate_x x y dual hperiodic
  have hyperiodic := periodicPostUpdate_y x y dual hperiodic
  have hdualperiodic := periodicPostUpdate_dual x y dual hperiodic
  have hi := (trajectory_iff.mp htrajectory) (i.val + N)
  have hl := (trajectory_iff.mp htrajectory) (l.val + N)
  have hsupport := proximalMinimizerSupportingInequality hf hi.2.2.1 hl.2.2.1 hi.1
  rw [periodicPostUpdate_current x hxperiodic i,
    periodicPostUpdate_current x hxperiodic l,
    periodicPostUpdate_predecessor y hyperiodic i,
    periodicPostUpdate_predecessor dual hdualperiodic i] at hsupport
  exact hsupport

/-- The second block of a periodic trajectory supplies a support inequality
between any two cyclic phase points. -/
private lemma periodicTrajectorySecondSupport {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NeZero N]
    {γ : ℝ} {f g : E → EReal} (x y dual : ℕ → E)
    (hg : ADMM.IsClosedProperConvex g)
    (htrajectory : IsTrajectory γ f g x y dual)
    (hperiodic : Function.Periodic
      (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) N)
    (i l : ZMod N) :
    (g (y (i.val + 1))).toReal - (g (y (l.val + 1))).toReal ≤
      inner ℝ
        (dual ((i - 1).val + 1) + (x (i.val + 1) - y (i.val + 1)))
        (y (i.val + 1) - y (l.val + 1)) := by
  -- Rewrite the second minimization as a proximal objective with linear term
  -- `inner (-dual) (w - x)`, then apply the same support lemma.
  have hxperiodic := periodicPostUpdate_x x y dual hperiodic
  have hyperiodic := periodicPostUpdate_y x y dual hperiodic
  have hdualperiodic := periodicPostUpdate_dual x y dual hperiodic
  have hi := (trajectory_iff.mp htrajectory) (i.val + N)
  have hl := (trajectory_iff.mp htrajectory) (l.val + N)
  have hinner (w : E) :
      inner ℝ (-dual (i.val + N)) (w - x (i.val + N + 1)) =
        inner ℝ (dual (i.val + N)) (x (i.val + N + 1) - w) := by
    simp only [inner_neg_left, inner_sub_right]
    ring
  have hmin : ∀ w,
      g (y (i.val + N + 1)) +
          ((inner ℝ (-dual (i.val + N))
              (y (i.val + N + 1) - x (i.val + N + 1)) +
            ‖y (i.val + N + 1) - x (i.val + N + 1)‖ ^ 2 / 2 : ℝ) : EReal) ≤
        g w +
          ((inner ℝ (-dual (i.val + N)) (w - x (i.val + N + 1)) +
            ‖w - x (i.val + N + 1)‖ ^ 2 / 2 : ℝ) : EReal) := by
    intro w
    simpa only [hinner, norm_sub_rev] using hi.2.1 w
  have hsupport := proximalMinimizerSupportingInequality hg hi.2.2.2.1 hl.2.2.2.1 hmin
  rw [periodicPostUpdate_current y hyperiodic i,
    periodicPostUpdate_current y hyperiodic l,
    periodicPostUpdate_current x hxperiodic i,
    periodicPostUpdate_predecessor dual hdualperiodic i] at hsupport
  simpa only [sub_neg_eq_add, sub_eq_add_neg, neg_neg, add_assoc, add_comm, add_left_comm]
    using hsupport

/-- Centered trajectory products satisfy every pairwise first-block support
inequality. -/
private lemma centeredTrajectoryFirstPairwiseSupport {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NeZero N]
    {γ : ℝ} {f g : E → EReal} (x y dual : ℕ → E)
    (hf : ADMM.IsClosedProperConvex f)
    (htrajectory : IsTrajectory γ f g x y dual)
    (hperiodic : Function.Periodic
      (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) N)
    (hγ : γ ≠ 0) (i l : ZMod N) :
    0 ≤ inner ℝ
      (ProjectionCycle.firstNormal γ (centeredProduct y) (centeredProduct dual) i)
      (ProjectionCycle.xVertex γ (centeredProduct y) (centeredProduct dual) i -
        ProjectionCycle.xVertex γ (centeredProduct y) (centeredProduct dual) l) := by
  -- The cyclic sum of function-value differences vanishes, while the
  -- coordinatewise proximal inequalities bound it by the generated normals.
  have hvalueSum :
      (∑ j : ZMod N,
        ((f (x ((i + j).val + 1))).toReal -
          (f (x ((l + j).val + 1))).toReal)) = 0 := by
    rw [Finset.sum_sub_distrib,
      phaseSumShift (fun r : ZMod N ↦ (f (x (r.val + 1))).toReal) i,
      phaseSumShift (fun r : ZMod N ↦ (f (x (r.val + 1))).toReal) l,
      sub_self]
  have hcoordinateSum :
      (∑ j : ZMod N,
        ((f (x ((i + j).val + 1))).toReal -
          (f (x ((l + j).val + 1))).toReal)) ≤
        ∑ j : ZMod N,
          inner ℝ
            (y ((i + j - 1).val + 1) - dual ((i + j - 1).val + 1) -
              x ((i + j).val + 1))
            (x ((i + j).val + 1) - x ((l + j).val + 1)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact periodicTrajectoryFirstSupport x y dual hf htrajectory hperiodic (i + j) (l + j)
  have hcenteredDiff (j : ZMod N) :
      (x ((i + j).val + 1) -
          (N : ℝ)⁻¹ • ∑ k : ZMod N, y (k.val + 1)) -
        (x ((l + j).val + 1) -
          (N : ℝ)⁻¹ • ∑ k : ZMod N, y (k.val + 1)) =
        x ((i + j).val + 1) - x ((l + j).val + 1) := by
    module
  have hdiffSum :
      (∑ j : ZMod N,
        (x ((i + j).val + 1) - x ((l + j).val + 1))) = 0 := by
    rw [Finset.sum_sub_distrib,
      phaseSumShift (fun r : ZMod N ↦ x (r.val + 1)) i,
      phaseSumShift (fun r : ZMod N ↦ x (r.val + 1)) l,
      sub_self]
  have hinner :
      (∑ j : ZMod N,
        inner ℝ
          (y ((i + j - 1).val + 1) - dual ((i + j - 1).val + 1) -
            x ((i + j).val + 1))
          (x ((i + j).val + 1) - x ((l + j).val + 1))) =
        inner ℝ
          (ProjectionCycle.firstNormal γ (centeredProduct y) (centeredProduct dual) i)
          (ProjectionCycle.xVertex γ (centeredProduct y) (centeredProduct dual) i -
            ProjectionCycle.xVertex γ (centeredProduct y) (centeredProduct dual) l) := by
    rw [PiLp.inner_apply]
    simp_rw [PiLp.sub_apply,
      centeredTrajectoryFirstNormal_apply x y dual hperiodic htrajectory hγ,
      centeredTrajectoryXVertex_apply x y dual hperiodic htrajectory hγ,
      hcenteredDiff, inner_add_left]
    rw [Finset.sum_add_distrib, ← inner_sum, hdiffSum, inner_zero_right, add_zero]
  calc
    0 = ∑ j : ZMod N,
        ((f (x ((i + j).val + 1))).toReal -
          (f (x ((l + j).val + 1))).toReal) := hvalueSum.symm
    _ ≤ ∑ j : ZMod N,
        inner ℝ
          (y ((i + j - 1).val + 1) - dual ((i + j - 1).val + 1) -
            x ((i + j).val + 1))
          (x ((i + j).val + 1) - x ((l + j).val + 1)) := hcoordinateSum
    _ = _ := hinner

/-- Centered trajectory products satisfy every pairwise second-block support
inequality. -/
private lemma centeredTrajectorySecondPairwiseSupport {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NeZero N]
    {γ : ℝ} {f g : E → EReal} (x y dual : ℕ → E)
    (hg : ADMM.IsClosedProperConvex g)
    (htrajectory : IsTrajectory γ f g x y dual)
    (hperiodic : Function.Periodic
      (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) N)
    (hγ : γ ≠ 0) (i l : ZMod N) :
    0 ≤ inner ℝ
      (ProjectionCycle.secondNormal γ (centeredProduct dual) i)
      (centeredProduct y i - centeredProduct y l) := by
  -- Sum the second-block proximal inequalities and cancel the translated
  -- multiplier mean using the zero cyclic sum of phase differences.
  have hvalueSum :
      (∑ j : ZMod N,
        ((g (y ((i + j).val + 1))).toReal -
          (g (y ((l + j).val + 1))).toReal)) = 0 := by
    rw [Finset.sum_sub_distrib,
      phaseSumShift (fun r : ZMod N ↦ (g (y (r.val + 1))).toReal) i,
      phaseSumShift (fun r : ZMod N ↦ (g (y (r.val + 1))).toReal) l,
      sub_self]
  have hcoordinateSum :
      (∑ j : ZMod N,
        ((g (y ((i + j).val + 1))).toReal -
          (g (y ((l + j).val + 1))).toReal)) ≤
        ∑ j : ZMod N,
          inner ℝ
            (dual ((i + j - 1).val + 1) +
              (x ((i + j).val + 1) - y ((i + j).val + 1)))
            (y ((i + j).val + 1) - y ((l + j).val + 1)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact periodicTrajectorySecondSupport x y dual hg htrajectory hperiodic (i + j) (l + j)
  have hcenteredDiff (j : ZMod N) :
      (centeredProduct y i - centeredProduct y l) j =
        y ((i + j).val + 1) - y ((l + j).val + 1) := by
    rw [PiLp.sub_apply, centeredProduct_apply, centeredProduct_apply]
    module
  have hdiffSum :
      (∑ j : ZMod N,
        (y ((i + j).val + 1) - y ((l + j).val + 1))) = 0 := by
    rw [Finset.sum_sub_distrib,
      phaseSumShift (fun r : ZMod N ↦ y (r.val + 1)) i,
      phaseSumShift (fun r : ZMod N ↦ y (r.val + 1)) l,
      sub_self]
  have hinner :
      (∑ j : ZMod N,
        inner ℝ
          (dual ((i + j - 1).val + 1) +
            (x ((i + j).val + 1) - y ((i + j).val + 1)))
          (y ((i + j).val + 1) - y ((l + j).val + 1))) =
        inner ℝ (ProjectionCycle.secondNormal γ (centeredProduct dual) i)
          (centeredProduct y i - centeredProduct y l) := by
    rw [PiLp.inner_apply]
    simp_rw [centeredTrajectorySecondNormal_apply x y dual hperiodic htrajectory hγ,
      hcenteredDiff, inner_sub_left]
    rw [Finset.sum_sub_distrib, ← inner_sum, hdiffSum, inner_zero_right, sub_zero]
  calc
    0 = ∑ j : ZMod N,
        ((g (y ((i + j).val + 1))).toReal -
          (g (y ((l + j).val + 1))).toReal) := hvalueSum.symm
    _ ≤ ∑ j : ZMod N,
        inner ℝ
          (dual ((i + j - 1).val + 1) +
            (x ((i + j).val + 1) - y ((i + j).val + 1)))
          (y ((i + j).val + 1) - y ((l + j).val + 1)) := hcoordinateSum
    _ = _ := hinner

/-- The centered multiplier residual is the centered cyclic product of the
post-update primal residual sequence. -/
private lemma centeredTrajectoryResidual_eq {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NeZero N]
    {γ : ℝ} {f g : E → EReal} (x y dual : ℕ → E)
    (htrajectory : IsTrajectory γ f g x y dual)
    (hperiodic : Function.Periodic
      (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) N)
    (hγ : γ ≠ 0) (i : ZMod N) :
    ProjectionCycle.residual γ (centeredProduct dual) i =
      centeredProduct (fun k ↦ x k - y k) i := by
  -- Compare coordinates and use multiplier closure to eliminate the mean of
  -- the periodic residual sequence.
  have hsum :=
    periodicTrajectoryResidual_sum_zero x y dual htrajectory hperiodic hγ
  apply PiLp.ext
  intro j
  rw [centeredTrajectoryResidual_apply x y dual hperiodic htrajectory hγ,
    centeredProduct_apply, hsum, smul_zero, sub_zero]

/-- Every phase of the centered multiplier product has the same residual
norm. -/
private lemma centeredTrajectoryResidual_norm_eq {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NeZero N]
    {γ : ℝ} {f g : E → EReal} (x y dual : ℕ → E)
    (htrajectory : IsTrajectory γ f g x y dual)
    (hperiodic : Function.Periodic
      (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) N)
    (hγ : γ ≠ 0) (i l : ZMod N) :
    ‖ProjectionCycle.residual γ (centeredProduct dual) i‖ =
      ‖ProjectionCycle.residual γ (centeredProduct dual) l‖ := by
  -- Put both residuals in centered-product normal form, then compare their
  -- squared norms through simultaneous cyclic translation.
  rw [centeredTrajectoryResidual_eq x y dual htrajectory hperiodic hγ,
    centeredTrajectoryResidual_eq x y dual htrajectory hperiodic hγ]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  have hshift := centeredProductInnerShift
    (fun k ↦ x k - y k) (fun k ↦ x k - y k) i i (l - i)
  have hphase : i + (l - i) = l := by
    abel
  rw [hphase] at hshift
  exact hshift.symm

/-- A nonzero periodic primal residual makes the centered multiplier product
have one strictly positive residual norm at every phase. -/
private lemma centeredTrajectoryHasConstantPositiveResidual
    {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NeZero N]
    {γ : ℝ} {f g : E → EReal} (x y dual : ℕ → E)
    (htrajectory : IsTrajectory γ f g x y dual)
    (hperiodic : Function.Periodic
      (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) N)
    (hγ : γ ≠ 0) (hnonzero : ∃ k, x (k + 1) - y (k + 1) ≠ 0) :
    ProjectionCycle.HasConstantPositiveResidual γ (centeredProduct (N := N) dual) := by
  -- Reduce the supplied nonzero natural phase modulo the period and detect it
  -- in coordinate zero of the corresponding product residual.
  rcases hnonzero with ⟨k, hk⟩
  have hresidualPeriodic := periodicPostUpdate_residual x y dual hperiodic
  have hmod := hresidualPeriodic.map_mod_nat k
  have hmodNonzero : x (k % N + 1) - y (k % N + 1) ≠ 0 := by
    intro hzero
    exact hk (hmod.symm.trans hzero)
  have hvectorNonzero :
      ProjectionCycle.residual γ (centeredProduct dual) (k : ZMod N) ≠ 0 := by
    intro hzero
    have hcoordinate := congrArg
      (fun z : PiLp 2 (fun _ : ZMod N ↦ E) ↦ z 0) hzero
    rw [centeredTrajectoryResidual_apply x y dual hperiodic htrajectory hγ] at hcoordinate
    simp only [add_zero, ZMod.val_natCast, PiLp.zero_apply] at hcoordinate
    exact hmodNonzero hcoordinate
  refine ⟨‖ProjectionCycle.residual γ (centeredProduct dual) (k : ZMod N)‖,
    norm_pos_iff.mpr hvectorNonzero, ?_⟩
  intro i
  exact centeredTrajectoryResidual_norm_eq x y dual htrajectory hperiodic hγ i k

/-- Centered products of a nonstationary periodic trajectory form a cyclic
projection reduction before finite-dimensional compression. -/
private lemma centeredTrajectoryIsCyclicReduction {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NeZero N]
    {γ : ℝ} {f g : E → EReal} (x y dual : ℕ → E)
    (hf : ADMM.IsClosedProperConvex f) (hg : ADMM.IsClosedProperConvex g)
    (htrajectory : IsTrajectory γ f g x y dual)
    (hperiodic : Function.Periodic
      (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) N)
    (hγ : γ ≠ 0) (hnonzero : ∃ k, x (k + 1) - y (k + 1) ≠ 0) :
    IsCyclicReduction γ (centeredProduct (N := N) y) (centeredProduct (N := N) dual) := by
  -- Centering supplies the zero sums needed to upgrade the already-proved
  -- pairwise inequalities to support against the origin.
  have hxsum :
      ∑ i : ZMod N,
        ProjectionCycle.xVertex γ (centeredProduct y) (centeredProduct dual) i = 0 := by
    simp_rw [centeredTrajectoryXVertex_eq x y dual htrajectory hperiodic hγ]
    exact centeredProduct_sum_zero x
  have hysum : ∑ i : ZMod N, centeredProduct y i = 0 :=
    centeredProduct_sum_zero y
  have hfirst := ProjectionCycle.nonselfSupportsOfPairwiseAndSumZero
    (ProjectionCycle.xVertex γ (centeredProduct y) (centeredProduct dual))
    (ProjectionCycle.firstNormal γ (centeredProduct y) (centeredProduct dual)) hxsum
    (centeredTrajectoryFirstPairwiseSupport x y dual hf htrajectory hperiodic hγ)
  have hsecond := ProjectionCycle.nonselfSupportsOfPairwiseAndSumZero
    (centeredProduct y) (ProjectionCycle.secondNormal γ (centeredProduct dual)) hysum
    (centeredTrajectorySecondPairwiseSupport x y dual hg htrajectory hperiodic hγ)
  refine ⟨⟨hfirst, hsecond⟩,
    centeredTrajectoryHasConstantPositiveResidual x y dual htrajectory hperiodic hγ hnonzero,
    ?_⟩
  -- A simultaneous coordinate permutation proves all three circulant Gram
  -- identities without expanding the product construction.
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact centeredProductInnerShift y y i j 1
  · intro i j
    exact centeredProductInnerShift y dual i j 1
  · intro i j
    exact centeredProductInnerShift dual dual i j 1

/-- Cyclic-reduction data can be recovered from its image under a real linear
isometric embedding. -/
private lemma isCyclicReduction_of_compLinearIsometry
    {N : ℕ} {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E →ₗᵢ[ℝ] F) (γ : ℝ) (η ν : ZMod N → E)
    (hcycle : IsCyclicReduction γ (fun i ↦ e (η i)) (fun i ↦ e (ν i))) :
    IsCyclicReduction γ η ν := by
  -- Normalize each derived vector after applying the isometry, so every
  -- support, norm, and Gram equality can be read back in the source space.
  have residual_map : ∀ i,
      ProjectionCycle.residual γ (fun j ↦ e (ν j)) i =
        e (ProjectionCycle.residual γ ν i) := by
    intro i
    simp only [ProjectionCycle.residual_apply, LinearIsometry.map_smul,
      LinearIsometry.map_sub]
  have vertex_map : ∀ i,
      ProjectionCycle.xVertex γ (fun j ↦ e (η j)) (fun j ↦ e (ν j)) i =
        e (ProjectionCycle.xVertex γ η ν i) := by
    intro i
    rw [ProjectionCycle.xVertex_apply, ProjectionCycle.xVertex_apply,
      residual_map, LinearIsometry.map_add]
  have first_normal_map : ∀ i,
      ProjectionCycle.firstNormal γ (fun j ↦ e (η j)) (fun j ↦ e (ν j)) i =
        e (ProjectionCycle.firstNormal γ η ν i) := by
    intro i
    rw [ProjectionCycle.firstNormal_apply, ProjectionCycle.firstNormal_apply,
      vertex_map, LinearIsometry.map_sub, LinearIsometry.map_sub]
  have second_normal_map : ∀ i,
      ProjectionCycle.secondNormal γ (fun j ↦ e (ν j)) i =
        e (ProjectionCycle.secondNormal γ ν i) := by
    intro i
    rw [ProjectionCycle.secondNormal_apply, ProjectionCycle.secondNormal_apply,
      residual_map, LinearIsometry.map_add]
  rcases hcycle with ⟨hprojection, hresidual, hgram⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro i
      refine ⟨?_, ?_⟩
      · rw [← LinearIsometry.inner_map_map e, ← first_normal_map, ← vertex_map]
        exact (hprojection.1 i).1
      · intro j hj
        rw [← LinearIsometry.inner_map_map e, LinearIsometry.map_sub,
          ← first_normal_map, ← vertex_map, ← vertex_map]
        exact (hprojection.1 i).2 j hj
    · intro i
      refine ⟨?_, ?_⟩
      · rw [← LinearIsometry.inner_map_map e, ← second_normal_map]
        exact (hprojection.2 i).1
      · intro j hj
        rw [← LinearIsometry.inner_map_map e, LinearIsometry.map_sub,
          ← second_normal_map]
        exact (hprojection.2 i).2 j hj
  · rcases hresidual with ⟨c, hc, hconstant⟩
    refine ⟨c, hc, ?_⟩
    intro i
    rw [← LinearIsometry.norm_map e, ← residual_map]
    exact hconstant i
  · refine ⟨?_, ?_, ?_⟩
    · intro i j
      simpa only [LinearIsometry.inner_map_map] using hgram.1 i j
    · intro i j
      simpa only [LinearIsometry.inner_map_map] using hgram.2.1 i j
    · intro i j
      simpa only [LinearIsometry.inner_map_map] using hgram.2.2 i j

/-- Every nonstationary periodic consensus ADMM trajectory admits a cyclic projection
reduction of dimension at most twice the period minus two. -/
theorem existsCyclicReduction {N : ℕ} {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (γ : ℝ) (f g : E → EReal) (x y dual : ℕ → E)
    (hN : 2 ≤ N) (hγ : 0 < γ)
    (hf : ADMM.IsClosedProperConvex f) (hg : ADMM.IsClosedProperConvex g)
    (htrajectory : IsTrajectory γ f g x y dual)
    (hperiodic : Function.Periodic
      (fun k ↦ (x (k + 1), y (k + 1), dual (k + 1))) N)
    (hnonzero : ∃ k, x (k + 1) - y (k + 1) ≠ 0) :
    ∃ d : ℕ, d ≤ 2 * N - 2 ∧
      ∃ η ν : ZMod N → EuclideanSpace ℝ (Fin d), IsCyclicReduction γ η ν := by
  -- Route correction: the supporting-plane bridge is available above, so the
  -- source proof now proceeds through centered cyclic products and their joint
  -- finite span rather than by expanding the ADMM updates in this theorem.
  classical
  have hNne : N ≠ 0 := by
    omega
  -- Local instance justification (indexing): `ZMod N` must use the nonzero
  -- period supplied by `hN` throughout the centered-product construction.
  letI : NeZero N := ⟨hNne⟩
  have hγne : γ ≠ 0 := ne_of_gt hγ
  let η₀ : ZMod N → PiLp 2 (fun _ : ZMod N ↦ E) := centeredProduct y
  let ν₀ : ZMod N → PiLp 2 (fun _ : ZMod N ↦ E) := centeredProduct dual
  have hambient : IsCyclicReduction γ η₀ ν₀ := by
    exact centeredTrajectoryIsCyclicReduction x y dual hf hg htrajectory hperiodic hγne hnonzero
  let S : Submodule ℝ (PiLp 2 (fun _ : ZMod N ↦ E)) :=
    Submodule.span ℝ (Set.range η₀ ∪ Set.range ν₀)
  have hηsum : ∑ i : ZMod N, η₀ i = 0 := by
    exact centeredProduct_sum_zero y
  have hνsum : ∑ i : ZMod N, ν₀ i = 0 := by
    exact centeredProduct_sum_zero dual
  have hrank : Module.finrank ℝ S ≤ 2 * N - 2 := by
    simpa only [S, ZMod.card] using
      zeroSumSpanRankBound η₀ ν₀ (0 : ZMod N) hηsum hνsum
  -- Restrict both cyclic families to their joint span before choosing
  -- orthonormal coordinates.
  have hηmem (i : ZMod N) : η₀ i ∈ S := by
    apply Submodule.subset_span
    exact Set.mem_union_left _ ⟨i, rfl⟩
  have hνmem (i : ZMod N) : ν₀ i ∈ S := by
    apply Submodule.subset_span
    exact Set.mem_union_right _ ⟨i, rfl⟩
  let ηS : ZMod N → S := fun i ↦ ⟨η₀ i, hηmem i⟩
  let νS : ZMod N → S := fun i ↦ ⟨ν₀ i, hνmem i⟩
  have hspanCycle : IsCyclicReduction γ ηS νS := by
    apply isCyclicReduction_of_compLinearIsometry S.subtypeₗᵢ γ ηS νS
    simpa only [ηS, νS, Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype] using hambient
  have hfinite : Set.Finite (Set.range η₀ ∪ Set.range ν₀) :=
    (Set.finite_range η₀).union (Set.finite_range ν₀)
  -- Local instance justification (finite span): the span is generated by the
  -- union of two finite cyclic ranges, so it has canonical finite dimension.
  letI : FiniteDimensional ℝ S :=
    FiniteDimensional.span_of_finite ℝ hfinite
  -- The orthonormal representation preserves every inner product and norm,
  -- while the rank estimate supplies the requested dimension bound.
  let e : S →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ S)) :=
    (stdOrthonormalBasis ℝ S).repr.toLinearIsometry
  refine ⟨Module.finrank ℝ S, hrank, (fun i ↦ e (ηS i)), (fun i ↦ e (νS i)), ?_⟩
  exact isCyclicReduction_compLinearIsometry
    e γ ηS νS hspanCycle

end ConsensusADMM

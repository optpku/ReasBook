/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Exercise_17_4_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_47
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Remark_14_31
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_42
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_43
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable (p : Kernel E E) [IsMarkovKernel p] [Kernel.IsIrreducible (Measure.count : Measure E) p]

/-- Helper for Theorem 17.49: an irreducible kernel for counting measure can only live on a
countable state space, because every state must lie in the countable union of the positive-mass
singleton supports of the iterated kernel rows from one reference point. -/
private theorem countableOfIrreducibleCountKernel
    (p : Kernel E E) [IsMarkovKernel p] [Kernel.IsIrreducible (Measure.count : Measure E) p] :
    Countable E := by
  classical
  by_cases hE : IsEmpty E
  · letI := hE
    infer_instance
  · letI : Nonempty E := not_isEmpty_iff.mp hE
    let x₀ : E := Classical.choice ‹Nonempty E›
    let reachable : ℕ → Set E := fun n ↦ {y : E | 0 < (p ^ n) x₀ ({y} : Set E)}
    have hreachable_countable : ∀ n, (reachable n).Countable := by
      intro n
      let μ : Measure E := (p ^ n) x₀
      letI : IsMarkovKernel (p ^ n) := by
        induction n with
        | zero =>
            simpa using (inferInstance : IsMarkovKernel (Kernel.id : Kernel E E))
        | succ n ih =>
            simpa [pow_succ] using (inferInstance : IsMarkovKernel ((p ^ n) ∘ₖ p))
      letI : IsProbabilityMeasure μ := inferInstance
      -- Each `n`-step law is a probability measure, so only countably many singletons can carry
      -- positive mass.
      have hμ_countable : {y : E | 0 < μ ({y} : Set E)}.Countable := by
        simpa [μ] using
          (Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ)
            (As_mble := fun y : E ↦ MeasurableSet.singleton y)
            (As_disj := fun y z hyz ↦ Set.disjoint_singleton.2 hyz))
      simpa [reachable, μ] using hμ_countable
    have hcover : (⋃ n : ℕ, reachable n) = Set.univ := by
      ext y
      constructor
      · intro _
        simp
      · intro _
        have hy_pos : (Measure.count : Measure E) ({y} : Set E) > 0 := by
          simp
        -- Irreducibility sends the reference state `x₀` to every singleton in finitely many steps.
        rcases (inferInstance : Kernel.IsIrreducible (Measure.count : Measure E) p).irreducible
            (A := ({y} : Set E)) (MeasurableSet.singleton y) hy_pos x₀ with
          ⟨n, hn⟩
        exact Set.mem_iUnion.mpr ⟨n, by simpa [reachable] using hn⟩
    -- The whole state space is the countable union of these reachable singleton supports.
    have huniv_countable : (Set.univ : Set E).Countable := by
      simpa [hcover] using Set.countable_iUnion hreachable_countable
    exact Set.countable_univ_iff.mp huniv_countable

/-- Helper for Theorem 17.49: on a countable discrete space, a kernel is determined by its
singleton masses, so the kernel agrees with the discrete matrix kernel built from those masses. -/
private theorem discreteMatrixKernel_singletonMass_eq [Countable E]
    (p : Kernel E E) :
    discreteMatrixKernel (fun x y : E ↦ p x ({y} : Set E)) = p := by
  -- Equality of row measures reduces to equality on singleton sets.
  apply Kernel.ext
  intro x
  refine Measure.ext_of_singleton
    (μ := discreteMatrixKernel (fun x y : E ↦ p x ({y} : Set E)) x)
    (ν := p x) fun y ↦ ?_
  rw [discreteMatrixKernel_apply]
  exact Measure.sum_smul_dirac_singleton
    (f := fun z : E ↦ p x ({z} : Set E)) (a := y)

omit [DiscreteMeasurableSpace E] in
/-- Helper for Theorem 17.49: if two probability measures differ only by an ENNReal scalar,
normalizing on `Set.univ` forces that scalar to be `1`. -/
private theorem probabilityMeasure_eq_of_measure_eq_smul
    {μ ν : ProbabilityMeasure E} {c : ℝ≥0∞}
    (hν : (ν : Measure E) = c • (μ : Measure E)) : ν = μ := by
  -- Compare total masses to identify the scalar.
  have hc_one : (1 : ℝ≥0∞) = c := by
    simpa using congrArg (fun ρ : Measure E ↦ ρ Set.univ) hν
  have hc : c = 1 := hc_one.symm
  -- Once the scalar is `1`, equality of underlying measures gives equality of distributions.
  apply ProbabilityMeasure.toMeasure_injective
  simpa [hc] using hν

omit [DiscreteMeasurableSpace E] in
/-- Helper for Theorem 17.49: the scalar-normalization argument is symmetric in the two
probability measures. -/
private theorem probabilityMeasure_eq_of_measure_smul_eq
    {μ ν : ProbabilityMeasure E} {c : ℝ≥0∞}
    (hμ : (μ : Measure E) = c • (ν : Measure E)) : μ = ν := by
  -- Proof comment: swap the roles of `μ` and `ν` in the previous normalization lemma.
  simpa [eq_comm] using
    (probabilityMeasure_eq_of_measure_eq_smul (μ := ν) (ν := μ) (c := c) hμ)

omit [DiscreteMeasurableSpace E] in
/-- Helper for Theorem 17.49: the underlying measure of a probability distribution is nonzero
because its total mass on `Set.univ` is `1`. -/
private theorem probabilityMeasure_toMeasure_ne_zero (μ : ProbabilityMeasure E) :
    (μ : Measure E) ≠ 0 := by
  intro hμ
  have huniv : (μ : Measure E) Set.univ = 0 := by
    simp [hμ]
  simp at huniv

/-- Helper for Theorem 17.49: every singleton has finite mass under a probability measure,
because it is dominated by `Set.univ` whose mass is `1`. -/
private theorem probabilityMeasureSingletonMass_lt_top
    (μ : ProbabilityMeasure E) (x : E) :
    ((μ : Measure E) ({x} : Set E)) < ∞ := by
  have hsubset : ({x} : Set E) ⊆ Set.univ :=
    Set.singleton_subset_iff.mpr (Set.mem_univ x)
  have hone_lt_top : (1 : ℝ≥0∞) < ∞ := by
    simp
  have huniv_lt_top : ((μ : Measure E) Set.univ) < ∞ := by
    simpa using hone_lt_top
  -- Proof comment: a singleton is contained in the whole space, and the total mass is `1`.
  exact lt_of_le_of_lt (measure_mono hsubset) huniv_lt_top

/-- Helper for Theorem 17.49: an invariant measure for `κ` stays invariant under every iterate
`κ ^ n`, so any positive singleton mass at `x` propagates along a positive `n`-step singleton mass
from `x` to `y`. -/
private theorem singletonMass_pos_of_invariant_of_posIterateMass [Countable E]
    {κ : Kernel E E} {ν : Measure E} {x y : E} {n : ℕ}
    (hν : Kernel.Invariant κ ν)
    (hx : 0 < ν ({x} : Set E))
    (hxy : 0 < (κ ^ n) x ({y} : Set E)) :
    0 < ν ({y} : Set E) := by
  have hνpow : ∀ m : ℕ, Kernel.Invariant (κ ^ m) ν := by
    intro m
    induction m with
    | zero =>
        -- Proof comment: the identity kernel fixes every measure.
        change (Kernel.id : Kernel E E) ∘ₘ ν = ν
        exact MeasureTheory.Measure.id_comp (μ := ν)
    | succ m ih =>
        -- Proof comment: compose the one-step invariance with the `n`-step invariance.
        simpa [pow_succ'] using Kernel.Invariant.comp hν ih
  have hyEq :
      ∑' z : E, ν ({z} : Set E) * (κ ^ n) z ({y} : Set E) = ν ({y} : Set E) := by
    -- Proof comment: evaluate the `n`-step invariance identity on the singleton `{y}`.
    have hy :=
      congrArg (fun ρ : Measure E ↦ ρ ({y} : Set E))
        (show (κ ^ n) ∘ₘ ν = ν from hνpow n)
    simpa [Measure.comp_eq_sum_of_countable] using hy
  have hterm_pos :
      0 < ν ({x} : Set E) * (κ ^ n) x ({y} : Set E) :=
    ENNReal.mul_pos hx.ne' hxy.ne'
  have hsum_pos :
      0 < ∑' z : E, ν ({z} : Set E) * (κ ^ n) z ({y} : Set E) := by
    -- Proof comment: the summand indexed by `x` is already strictly positive.
    exact lt_of_lt_of_le hterm_pos (ENNReal.le_tsum x)
  rw [hyEq] at hsum_pos
  exact hsum_pos

/-- Helper for Theorem 17.49: on a countable irreducible discrete state space, every invariant
distribution assigns strictly positive mass to every singleton. -/
private theorem singletonMass_pos_of_invariantDistribution [Countable E]
    (κ : Kernel E E) [IsMarkovKernel κ]
    [Kernel.IsIrreducible (Measure.count : Measure E) κ]
    {μ : ProbabilityMeasure E}
    (hμ : Kernel.Invariant κ (μ : Measure E)) (y : E) :
    0 < (μ : Measure E) ({y} : Set E) := by
  have hsome :
      ∃ x : E, 0 < (μ : Measure E) ({x} : Set E) := by
    by_contra hsome
    have hnone : ∀ x : E, ¬ 0 < (μ : Measure E) ({x} : Set E) := by
      intro x hx
      exact hsome ⟨x, hx⟩
    have hzero : (μ : Measure E) = 0 := by
      -- Proof comment: vanishing on every singleton forces the whole measure to vanish.
      refine Measure.ext_of_singleton fun x ↦ ?_
      exact le_antisymm (le_of_not_gt (hnone x)) bot_le
    exact (probabilityMeasure_toMeasure_ne_zero μ) hzero
  rcases hsome with ⟨x, hx⟩
  have hy_pos : (Measure.count : Measure E) ({y} : Set E) > 0 := by
    simp
  rcases (inferInstance : Kernel.IsIrreducible (Measure.count : Measure E) κ).irreducible
      (A := ({y} : Set E)) (MeasurableSet.singleton y) hy_pos x with
    ⟨n, hn⟩
  -- Proof comment: irreducibility reaches `{y}` from one positive-mass state, and invariance
  -- propagates that positive singleton mass along the positive `n`-step transition.
  exact singletonMass_pos_of_invariant_of_posIterateMass
    (κ := κ) (ν := (μ : Measure E)) hμ hx hn

/-- Helper for Theorem 17.49: the natural history σ-algebra of the canonical coordinate process
on `ℕ → E` up to time `s` is exactly the sigma-algebra generated by the finite prefix map
`Preorder.frestrictLe s`. -/
private theorem generatedFiltrationSpace_eval_eq_frestrictLeComap [Countable E] (s : ℕ) :
    generatedFiltrationSpace (Function.eval : ℕ → (ℕ → E) → E) s =
      MeasurableSpace.comap (Preorder.frestrictLe s) inferInstance := by
  refine le_antisymm ?_ ?_
  · rw [generatedFiltrationSpace]
    refine iSup₂_le fun t ht ↦ ?_
    let i : Finset.Iic s := ⟨t, Finset.mem_Iic.2 ht⟩
    have hCoord :
        Measurable[
          MeasurableSpace.comap (Preorder.frestrictLe s) inferInstance]
          (Function.eval t : (ℕ → E) → E) := by
      -- Proof comment: each history coordinate `eval t` with `t ≤ s` is recovered by reading the
      -- prefix map at the index `⟨t, t ≤ s⟩`.
      simpa [Function.eval, Preorder.frestrictLe_apply, i] using
        (measurable_pi_apply i).comp (comap_measurable (Preorder.frestrictLe s))
    exact hCoord.comap_le
  · have hPrefix :
        Measurable[
          generatedFiltrationSpace (Function.eval : ℕ → (ℕ → E) → E) s]
          (Preorder.frestrictLe s : (ℕ → E) → Finset.Iic s → E) := by
      -- Proof comment: every prefix coordinate is one of the generators `eval t` with `t ≤ s`.
      rw [@measurable_pi_iff]
      intro i
      refine Measurable.of_comap_le ?_
      exact le_iSup_of_le i.1 <| le_iSup_of_le (Finset.mem_Iic.1 i.2) le_rfl
    exact hPrefix.comap_le

/-- Helper for Theorem 17.49: the canonical `trajMeasure` started from `x` has initial
distribution `δ_x` on the zeroth coordinate. -/
private theorem canonicalTrajMeasure_map_eval_zero_eq_dirac [Countable E]
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) :
    let η : (n : ℕ) → Kernel (Π i : Finset.Iic n, E) E :=
      fun n ↦
        Kernel.comap κ
          (fun z : Π i : Finset.Iic n, E ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
          (by fun_prop)
    let μ : Measure (ℕ → E) := Kernel.trajMeasure (X := fun _ : ℕ ↦ E) (Measure.dirac x) η
    μ.map (Function.eval 0) = Measure.dirac x := by
  let η : (n : ℕ) → Kernel (Π i : Finset.Iic n, E) E :=
    fun n ↦
      Kernel.comap κ
        (fun z : Π i : Finset.Iic n, E ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
        (by fun_prop)
  let μ : Measure (ℕ → E) := Kernel.trajMeasure (X := fun _ : ℕ ↦ E) (Measure.dirac x) η
  have hprefix :
      μ.map (Preorder.frestrictLe 0) = Measure.dirac (fun _ : Finset.Iic 0 ↦ x) := by
    -- Proof comment: the zeroth prefix marginal of the trajectory law is exactly the deterministic
    -- starting state.
    simpa [μ, η, Kernel.partialTraj_self] using
      (Kernel.trajMeasure_map_frestrictLe (X := fun _ : ℕ ↦ E)
        (μ₀ := Measure.dirac x) (κ := η) 0)
  calc
    μ.map (Function.eval 0)
      = (μ.map (Preorder.frestrictLe 0)).map
          (fun z : Finset.Iic 0 → E ↦ z ⟨0, Finset.mem_Iic.2 le_rfl⟩) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            rfl
    _ = Measure.dirac x := by
          rw [hprefix]
          simp

/-- Helper for Theorem 17.49: under the canonical trajectory law of a homogeneous Markov kernel,
conditioning the next coordinate on the history up to time `s` yields the one-step kernel applied
to the current state. -/
private theorem canonicalTrajMeasure_oneStepConditionalProb_eq_kernel [Countable E] [Nonempty E]
    (κ : Kernel E E) [IsMarkovKernel κ] (x : E) ⦃A : Set E⦄ (hA : MeasurableSet A) (s : ℕ) :
    let η : (n : ℕ) → Kernel (Π i : Finset.Iic n, E) E :=
      fun n ↦
        Kernel.comap κ
          (fun z : Π i : Finset.Iic n, E ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
          (by fun_prop)
    let μ : Measure (ℕ → E) := Kernel.trajMeasure (X := fun _ : ℕ ↦ E) (Measure.dirac x) η
    μ⟦Function.eval (s + 1) ⁻¹' A | generatedFiltrationSpace Function.eval s⟧ =ᵐ[μ]
      fun ξ ↦ (κ (ξ s)).real A := by
  let η : (n : ℕ) → Kernel (Π i : Finset.Iic n, E) E :=
    fun n ↦
      Kernel.comap κ
        (fun z : Π i : Finset.Iic n, E ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
        (by fun_prop)
  let μ : Measure (ℕ → E) := Kernel.trajMeasure (X := fun _ : ℕ ↦ E) (Measure.dirac x) η
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  let H : (ℕ → E) → Finset.Iic s → E := Preorder.frestrictLe s
  have hH_meas : Measurable H := Preorder.measurable_frestrictLe s
  have hnext_meas : Measurable (Function.eval (s + 1) : (ℕ → E) → E) :=
    measurable_pi_apply (s + 1)
  have hcond :
      condDistrib (Function.eval (s + 1)) H μ =ᵐ[μ.map H] η s := by
    -- Proof comment: `condDistrib_trajMeasure` is the canonical one-step conditional law of the
    -- trajectory measure.
    simpa [μ, H, η] using
      (Kernel.condDistrib_trajMeasure (X := fun _ : ℕ ↦ E)
        (μ₀ := Measure.dirac x) (κ := η) (a := s))
  have hcondexp :
      μ⟦(Function.eval (s + 1)) ⁻¹' A | MeasurableSpace.comap H inferInstance⟧ =ᵐ[μ]
        fun ξ ↦ (condDistrib (Function.eval (s + 1)) H μ (H ξ)).real A := by
    -- Proof comment: identify the conditional expectation with the conditional-distribution
    -- kernel evaluated on the observed prefix.
    simpa using
      (condDistrib_ae_eq_condExp (μ := μ) (X := H) (Y := Function.eval (s + 1))
        hH_meas hnext_meas hA).symm
  have hcond_comp :
      (fun ξ ↦ (condDistrib (Function.eval (s + 1)) H μ (H ξ)).real A) =ᵐ[μ]
        fun ξ ↦ (η s (H ξ)).real A := by
    filter_upwards [ae_eq_comp hH_meas.aemeasurable hcond] with ξ hξ
    simpa [Function.comp] using congrArg (fun ν : Measure E ↦ ν.real A) hξ
  rw [generatedFiltrationSpace_eval_eq_frestrictLeComap (E := E) s]
  exact hcondexp.trans <|
    hcond_comp.trans <|
      Filter.Eventually.of_forall fun ξ ↦ by
        simpa [η, H, Preorder.frestrictLe_apply] using
          congrArg (fun ν : Measure E ↦ ν.real A) rfl

/-- Helper for Theorem 17.49: the canonical history projection to the last available coordinate is
measurable on each finite prefix space `Π i : Finset.Iic n, E`. -/
private theorem measurable_canonicalHistoryProjection [Countable E] (κ : Kernel E E) (n : ℕ) :
    Measurable (fun z : Π i : Finset.Iic n, E ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩) := by
  -- Proof comment: coordinate projections on finite products are measurable.
  fun_prop

/-- Helper for Theorem 17.49: the canonical path construction uses the one-step kernel evaluated
at the most recent state in each finite history. -/
private def canonicalHistoryKernel [Countable E] (κ : Kernel E E) [IsMarkovKernel κ] :
    (n : ℕ) → Kernel (Π i : Finset.Iic n, E) E :=
  fun n ↦
    Kernel.comap κ
      (fun z : Π i : Finset.Iic n, E ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
      (measurable_canonicalHistoryProjection (E := E) κ n)

/-- Helper for Theorem 17.49: each stage of the canonical history kernel family is a Markov
kernel as soon as the underlying one-step kernel is Markov. -/
private theorem canonicalHistoryKernel_isMarkovKernel [Countable E]
    (κ : Kernel E E) [IsMarkovKernel κ] :
    ∀ n : ℕ, IsMarkovKernel (canonicalHistoryKernel (E := E) κ n) := by
  intro n
  dsimp [canonicalHistoryKernel]
  infer_instance

/-- Helper for Theorem 17.49: `canonicalTrajProcess q x` is the canonical path-space law of the
discrete chain with transition matrix `q`, started from the deterministic state `x`. -/
private def canonicalTrajProcess [Countable E] (q : E → E → ℝ≥0∞)
    (hq : IsStochasticMatrix q) (x : E) :
    ProbabilityMeasure (ℕ → E) :=
  letI : IsMarkovKernel (discreteMatrixKernel q) := discreteMatrixKernel_isMarkovKernel q hq
  letI :
      ∀ n : ℕ, IsMarkovKernel (canonicalHistoryKernel (E := E) (discreteMatrixKernel q) n) :=
    canonicalHistoryKernel_isMarkovKernel (E := E) (discreteMatrixKernel q)
  ⟨Kernel.trajMeasure (X := fun _ : ℕ ↦ E) (Measure.dirac x)
      (canonicalHistoryKernel (E := E) (discreteMatrixKernel q)),
    inferInstance⟩

/-- Helper for Theorem 17.49: a canonical coordinate process on `ℕ → E` with deterministic
start law and the correct one-step conditional distribution realizes the Markov chain with
transition matrix `q`. -/
private theorem canonicalProcessRealizationOfStochasticMatrix
    [Countable E] (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q)
    (P : E → ProbabilityMeasure (ℕ → E))
    (hstart : ∀ x : E, (P x : Measure (ℕ → E)).map (Function.eval 0) = Measure.dirac x)
    (hstep :
      ∀ x : E, ∀ ⦃A : Set E⦄, MeasurableSet A → ∀ n : ℕ,
        (P x)⟦Function.eval (n + 1) ⁻¹' A | generatedFiltrationSpace Function.eval n⟧ =ᵐ[
            (P x : Measure (ℕ → E))]
          fun ω ↦ ((discreteMatrixKernel q) (Function.eval n ω)).real A) :
    IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel q ^ n) P Function.eval := by
  let _ : IsMarkovKernel (discreteMatrixKernel q) := discreteMatrixKernel_isMarkovKernel q hq
  -- Proof comment: once `q` is packaged as a one-step Markov kernel, the owner realization
  -- theorem upgrades the start-law and one-step conditional-law identities to the full semigroup.
  refine ProbabilityTheory.isMarkovProcessRealization_of_oneStepKernel
    (κ₁ := discreteMatrixKernel q)
    (P := P)
    (X := Function.eval)
    (hmeas := fun n ↦ measurable_pi_apply n)
    (hstart := hstart)
    (hstep := hstep)

/-- Helper for Theorem 17.49: the canonical coordinate process under `canonicalTrajProcess q`
realizes the discrete Markov chain with one-step kernel `discreteMatrixKernel q`. -/
private theorem canonicalTrajProcess_isMarkovProcessRealization [Countable E]
    (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q) :
    IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel q ^ n)
      (canonicalTrajProcess (E := E) q hq) Function.eval := by
  letI : IsMarkovKernel (discreteMatrixKernel q) := discreteMatrixKernel_isMarkovKernel q hq
  refine canonicalProcessRealizationOfStochasticMatrix (E := E) q hq
    (canonicalTrajProcess (E := E) q hq) ?_ ?_
  · intro x
    -- Proof comment: the canonical trajectory law starts deterministically at the chosen state.
    simpa [canonicalTrajProcess, canonicalHistoryKernel] using
      (canonicalTrajMeasure_map_eval_zero_eq_dirac
        (E := E) (κ := discreteMatrixKernel q) x)
  · intro x A hA n
    letI : Nonempty E := ⟨x⟩
    -- Proof comment: the next-step conditional law of the canonical path process is exactly the
    -- one-step kernel evaluated at the current coordinate.
    simpa [canonicalTrajProcess, canonicalHistoryKernel] using
      (canonicalTrajMeasure_oneStepConditionalProb_eq_kernel
        (E := E) (κ := discreteMatrixKernel q) x hA n)

/-- Helper for Theorem 17.49: an invariant distribution for the irreducible countable kernel
`discreteMatrixKernel q` forces the canonical realization to be recurrent. -/
private theorem canonicalTrajProcess_isRecurrent_ofInvariantDistribution [Countable E]
    (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q)
    [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q)]
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel q) (π : Measure E)) :
    IsRecurrentMarkovChain (canonicalTrajProcess (E := E) q hq) Function.eval := by
  letI : IsMarkovKernel (discreteMatrixKernel q) := discreteMatrixKernel_isMarkovKernel q hq
  letI :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel q ^ n)
        (canonicalTrajProcess (E := E) q hq) Function.eval :=
    canonicalTrajProcess_isMarkovProcessRealization (E := E) q hq
  intro x
  have hπx : 0 < (π : Measure E) ({x} : Set E) :=
    singletonMass_pos_of_invariantDistribution
      (E := E) (κ := discreteMatrixKernel q) hπ x
  have hxPosRec :
      IsPositiveRecurrentState (canonicalTrajProcess (E := E) q hq) Function.eval x := by
    -- Proof comment: a positive invariant singleton mass forces positive recurrence of that
    -- state on the canonical realization.
    simpa [pow_one] using
      (isPositiveRecurrentState_of_invariantDistribution_singleton_pos
        (κ := fun n : ℕ ↦ discreteMatrixKernel q ^ n)
        (P := canonicalTrajProcess (E := E) q hq)
        (X := Function.eval)
        (π := π) (y := x)
        (by simpa [pow_one] using hπ) hπx)
  -- Proof comment: positive recurrence implies recurrence for each state separately.
  exact positiveRecurrentState_isRecurrentStateLocal
    (κ := fun n : ℕ ↦ discreteMatrixKernel q ^ n)
    (P := canonicalTrajProcess (E := E) q hq)
    (X := Function.eval) x hxPosRec

/-- Helper for Theorem 17.49: on a countable discrete space, a nonzero measure must charge some
singleton positively. -/
private theorem existsPositiveSingletonMassOfNeZero [Countable E] {π : Measure E}
    (hπ_ne : π ≠ 0) :
    ∃ x : E, 0 < π ({x} : Set E) := by
  classical
  by_contra hnone
  have hzero : π = 0 := by
    -- Proof comment: if every singleton has zero mass, singleton extensionality forces the whole
    -- measure to vanish.
    refine Measure.ext_of_singleton fun x ↦ ?_
    have hx_not_pos : ¬ 0 < π ({x} : Set E) := by
      intro hx
      exact hnone ⟨x, hx⟩
    exact le_antisymm (le_of_not_gt hx_not_pos) bot_le
  exact hπ_ne hzero

/-- Helper for Theorem 17.49: invariance under `discreteMatrixKernel q` propagates to every
iterate, and evaluating the resulting identity on a singleton gives the countable convolution
formula for that singleton mass. -/
private theorem invariantMeasureApplySingletonEqTsumPow [Countable E]
    (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q) {π : Measure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel q) π) (n : ℕ) (y : E) :
    π ({y} : Set E) =
      ∑' z : E, π ({z} : Set E) * ((discreteMatrixKernel q ^ n) z ({y} : Set E)) := by
  letI : IsMarkovKernel (discreteMatrixKernel q) := discreteMatrixKernel_isMarkovKernel q hq
  have hπn : Kernel.Invariant (discreteMatrixKernel q ^ n) π := by
    induction n with
    | zero =>
        -- Proof comment: the time-zero kernel is the identity kernel.
        simpa using (show Kernel.Invariant (Kernel.id : Kernel E E) π from by
          change (Kernel.id : Kernel E E) ∘ₘ π = π
          exact MeasureTheory.Measure.id_comp (μ := π))
    | succ n ihn =>
        -- Proof comment: compose the one-step invariance with the already-known `n`-step
        -- invariance.
        simpa [pow_succ'] using Kernel.Invariant.comp hπ ihn
  have hy :
      ((discreteMatrixKernel q ^ n) ∘ₘ π) ({y} : Set E) = π ({y} : Set E) :=
    congrArg (fun ρ : Measure E ↦ ρ ({y} : Set E)) hπn.def
  calc
    π ({y} : Set E) = ((discreteMatrixKernel q ^ n) ∘ₘ π) ({y} : Set E) := hy.symm
    _ = ∑' z : E, π ({z} : Set E) * ((discreteMatrixKernel q ^ n) z ({y} : Set E)) := by
          rw [Measure.comp_eq_sum_of_countable, Measure.sum_apply _ (MeasurableSet.singleton y)]
          refine tsum_congr fun z ↦ ?_
          rw [Measure.smul_apply]
          rfl

/-- Helper for Theorem 17.49: on the canonical realization, the return-cycle occupation measure
rooted at `x` gives singleton mass `1` at `x` itself. -/
private theorem canonicalReturnCycle_apply_singleton_self [Countable E]
    (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q) (x : E) :
    (μ[canonicalTrajProcess (E := E) q hq, Function.eval] x) ({x} : Set E) = 1 := by
  let P : E → ProbabilityMeasure (ℕ → E) := canonicalTrajProcess (E := E) q hq
  have hReal :
      IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P Function.eval := by
    simpa [P] using canonicalTrajProcess_isMarkovProcessRealization (E := E) q hq
  have hinit :
      (P x : Measure (ℕ → E)) {ω | Function.eval 0 ω = x} = 1 := by
    have hpreimage :
        {ω | Function.eval 0 ω = x} =
          (Function.eval 0 : (ℕ → E) → E) ⁻¹' ({x} : Set E) := by
      ext ω
      simp
    rw [hpreimage, ← Measure.map_apply (hReal.measurable_process 0) (MeasurableSet.singleton x)]
    rw [hReal.initial_eq x]
    simp
  have hterm0 :
      (P x : Measure (ℕ → E))
        {ω | Function.eval 0 ω = x ∧ (0 : ℕ∞) < (τ_[Function.eval, x]^1) ω} = 1 := by
    have hτpos : ∀ ω : ℕ → E, (0 : ℕ∞) < (τ_[Function.eval, x]^1) ω := by
      intro ω
      have hτge1 : (1 : ℕ∞) ≤ (τ_[Function.eval, x]^1) ω := by
        have h : (1 : ℕ) ≤ MeasureTheory.hittingAfter Function.eval ({x} : Set E) 1 ω :=
          le_hittingAfter ω
        simpa [iteratedEntranceTime_one] using h
      exact lt_of_lt_of_le (by simp) hτge1
    have hEq :
        {ω | Function.eval 0 ω = x ∧ (0 : ℕ∞) < (τ_[Function.eval, x]^1) ω} =
          {ω | Function.eval 0 ω = x} := by
      ext ω
      constructor
      · intro hω
        exact hω.1
      · intro hω
        exact ⟨hω, hτpos ω⟩
    rw [hEq]
    exact hinit
  have htailZero :
      ∀ m : ℕ,
        ite (m = 0) 0
            ((P x : Measure (ℕ → E))
              {ω | Function.eval m ω = x ∧ (m : ℕ∞) < (τ_[Function.eval, x]^1) ω}) = 0 := by
    intro m
    by_cases hm : m = 0
    · simp [hm]
    · rcases Nat.exists_eq_succ_of_ne_zero hm with ⟨n, rfl⟩
      have hempty :
          {ω | Function.eval (n + 1) ω = x ∧
            (((n + 1 : ℕ) : ℕ∞) < (τ_[Function.eval, x]^1) ω)} = ∅ := by
        ext ω
        constructor
        · intro hω
          have hle : (τ_[Function.eval, x]^1) ω ≤ n + 1 := by
            have h :
                MeasureTheory.hittingAfter Function.eval ({x} : Set E) 1 ω ≤ n + 1 :=
              hittingAfter_le_of_mem (by simp)
                (by simpa [Set.mem_singleton_iff] using hω.1)
            simpa [iteratedEntranceTime_one] using h
          exact False.elim <| (not_lt_of_ge hle) hω.2
        · simp
      rw [hempty]
      simp
  have htailTsum :
      (∑' m : ℕ,
        ite (m = 0) 0
            ((P x : Measure (ℕ → E))
              {ω | Function.eval m ω = x ∧ (m : ℕ∞) < (τ_[Function.eval, x]^1) ω})) = 0 := by
    exact ENNReal.tsum_eq_zero.2 htailZero
  have hterm0' :
      (P x : Measure (ℕ → E))
        {ω | Function.eval 0 ω = x ∧ ((0 : ℕ) : ℕ∞) < (τ_[Function.eval, x]^1) ω} = 1 := by
    simpa using hterm0
  have htailTsum' :
      (∑' i : ℕ,
        if i = 0 then 0 else
          (P x : Measure (ℕ → E))
            {ω | Function.eval i ω = x ∧ (i : ℕ∞) < (τ_[Function.eval, x]^1) ω}) = 0 := by
    simpa using htailTsum
  -- Proof comment: only the initial visit contributes to the diagonal return-cycle occupation
  -- mass; any later visit would already be the first positive return.
  rw [show (μ[canonicalTrajProcess (E := E) q hq, Function.eval] x) ({x} : Set E) =
      (μ[P, Function.eval] x) ({x} : Set E) by rfl]
  rw [returnCycleOccupationMeasure_apply_singleton (P := P) (X := Function.eval),
    returnCycleOccupationMass, ENNReal.tsum_eq_add_tsum_ite 0, hterm0']
  have hsum1 :
      1 + (∑' i : ℕ,
        if i = 0 then 0 else
          (P x : Measure (ℕ → E))
            {ω | Function.eval i ω = x ∧ (i : ℕ∞) < (τ_[Function.eval, x]^1) ω}) =
        1 + 0 := congrArg (fun t : ℝ≥0∞ ↦ 1 + t) htailTsum'
  simpa using hsum1

/-- Helper for Theorem 17.49: once a strict singleton gap above the return-cycle reference measure
appears at `y`, invariance transports that gap back to the reference state `x`, contradicting the
fact that the return-cycle occupation measure has diagonal singleton mass `1`. -/
private theorem strictGapAgainstReturnCyclePropagatesToReference [Countable E]
    (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q)
    [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q)]
    {π : Measure E} (hπ : Kernel.Invariant (discreteMatrixKernel q) π)
    {x y : E}
    (hx : IsRecurrentState (canonicalTrajProcess (E := E) q hq) Function.eval x)
    (hπ_finite : ∀ z : E, π ({z} : Set E) < ∞)
    (hπx_pos : 0 < π ({x} : Set E))
    (hLower :
      ∀ z : E, π ({z} : Set E) ≥
        π ({x} : Set E) * (μ[canonicalTrajProcess (E := E) q hq, Function.eval] x) ({z} : Set E))
    (hgap :
      π ({y} : Set E) >
        π ({x} : Set E) * (μ[canonicalTrajProcess (E := E) q hq, Function.eval] x) ({y} : Set E))
    (hstep : ∃ n : ℕ, 0 < n ∧ 0 < (discreteMatrixKernel q ^ n) y ({x} : Set E)) :
    False := by
  let P : E → ProbabilityMeasure (ℕ → E) := canonicalTrajProcess (E := E) q hq
  have hReal :
      IsMarkovProcessRealization (fun m ↦ discreteMatrixKernel q ^ m) P Function.eval := by
    simpa [P] using canonicalTrajProcess_isMarkovProcessRealization (E := E) q hq
  letI : IsMarkovProcessRealization (fun m ↦ discreteMatrixKernel q ^ m) P Function.eval := hReal
  rcases hstep with ⟨n, -, hyx_pos⟩
  letI : IsMarkovKernel (discreteMatrixKernel q ^ n) := hReal.semigroup.isMarkovKernel n
  have hπ_singleton :
      π ({x} : Set E) =
        ∑' z : E, π ({z} : Set E) * ((discreteMatrixKernel q ^ n) z ({x} : Set E)) :=
    invariantMeasureApplySingletonEqTsumPow (E := E) q hq hπ n x
  have hμinv :
      Kernel.Invariant (discreteMatrixKernel q) ((μ[P, Function.eval] x) : Measure E) := by
    simpa using
      (recurrentState_returnCycleOccupationMeasure_comp_eq
        (κ := fun m ↦ discreteMatrixKernel q ^ m) (P := P) (X := Function.eval) hx)
  have hμ_singleton :
      (μ[P, Function.eval] x) ({x} : Set E) =
        ∑' z : E, (μ[P, Function.eval] x) ({z} : Set E) *
          ((discreteMatrixKernel q ^ n) z ({x} : Set E)) :=
    invariantMeasureApplySingletonEqTsumPow
      (E := E) q hq (π := (μ[P, Function.eval] x)) hμinv n x
  let f : E → ℝ≥0∞ :=
    fun z ↦ π ({x} : Set E) *
      ((μ[P, Function.eval] x) ({z} : Set E) * ((discreteMatrixKernel q ^ n) z ({x} : Set E)))
  let g : E → ℝ≥0∞ :=
    fun z ↦ π ({z} : Set E) * ((discreteMatrixKernel q ^ n) z ({x} : Set E))
  have hf_tsum :
      ∑' z : E, f z = π ({x} : Set E) * (μ[P, Function.eval] x) ({x} : Set E) := by
    -- Proof comment: scale the singleton invariance formula for the return-cycle occupation
    -- measure by the positive reference mass `π ({x})`.
    calc
      ∑' z : E, f z =
          π ({x} : Set E) *
            ∑' z : E, (μ[P, Function.eval] x) ({z} : Set E) *
              ((discreteMatrixKernel q ^ n) z ({x} : Set E)) := by
            simp only [f, ENNReal.tsum_mul_left]
      _ = π ({x} : Set E) * (μ[P, Function.eval] x) ({x} : Set E) := by
            rw [← hμ_singleton]
  have hg_tsum : ∑' z : E, g z = π ({x} : Set E) := by
    -- Proof comment: the `n`-step singleton convolution of `π` at `x` is exactly `π ({x})`.
    exact hπ_singleton.symm
  have hf_tsum_ne_top : (∑' z : E, f z) ≠ ⊤ := by
    rw [hf_tsum]
    rw [show (μ[P, Function.eval] x) ({x} : Set E) =
        (μ[canonicalTrajProcess (E := E) q hq, Function.eval] x) ({x} : Set E) by rfl]
    rw [canonicalReturnCycle_apply_singleton_self (E := E) q hq x, mul_one]
    exact (hπ_finite x).ne
  have hfg : ∀ z : E, f z ≤ g z := by
    intro z
    calc
      f z =
          (π ({x} : Set E) * (μ[P, Function.eval] x) ({z} : Set E)) *
            ((discreteMatrixKernel q ^ n) z ({x} : Set E)) := by
            simp only [f, mul_assoc]
      _ ≤ π ({z} : Set E) * ((discreteMatrixKernel q ^ n) z ({x} : Set E)) := by
            exact mul_le_mul_right' (hLower z) ((discreteMatrixKernel q ^ n) z ({x} : Set E))
      _ = g z := by
            simp only [g]
  have hfgy : f y < g y := by
    have hyx_ne_top : ((discreteMatrixKernel q ^ n) y ({x} : Set E)) ≠ ⊤ :=
      measure_ne_top _ _
    calc
      f y =
          (π ({x} : Set E) * (μ[P, Function.eval] x) ({y} : Set E)) *
            ((discreteMatrixKernel q ^ n) y ({x} : Set E)) := by
            simp only [f, mul_assoc]
      _ < π ({y} : Set E) * ((discreteMatrixKernel q ^ n) y ({x} : Set E)) := by
            exact ENNReal.mul_lt_mul_right' hyx_pos.ne' hyx_ne_top hgap
      _ = g y := by
            simp only [g]
  have hsum_lt : (∑' z : E, f z) < ∑' z : E, g z :=
    ENNReal.tsum_lt_tsum hf_tsum_ne_top hfg hfgy
  have hself_lt :
      π ({x} : Set E) * (μ[P, Function.eval] x) ({x} : Set E) < π ({x} : Set E) := by
    calc
      π ({x} : Set E) * (μ[P, Function.eval] x) ({x} : Set E) = ∑' z : E, f z := hf_tsum.symm
      _ < ∑' z : E, g z := hsum_lt
      _ = π ({x} : Set E) := hg_tsum
  rw [show (μ[canonicalTrajProcess (E := E) q hq, Function.eval] x) ({x} : Set E) =
      (μ[P, Function.eval] x) ({x} : Set E) by rfl] at hself_lt
  rw [canonicalReturnCycle_apply_singleton_self (E := E) q hq x, mul_one] at hself_lt
  exact lt_irrefl _ hself_lt

/-- Helper for Theorem 17.49: the weighted start law attached to the singleton masses of `π`
starts from `z` with weight `π ({z})`. -/
private def weightedStartLaw [Countable E] (q : E → E → ℝ≥0∞)
    (hq : IsStochasticMatrix q) (π : Measure E) : Measure (ℕ → E) :=
  Measure.sum fun z : E ↦ π ({z} : Set E) •
    (canonicalTrajProcess (E := E) q hq z : Measure (ℕ → E))

/-- Helper for Theorem 17.49: the weighted start law evaluates the time-`n` state event by the
singleton mass of the invariant measure. -/
private theorem weightedStartLaw_apply_stateEvent [Countable E]
    (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q) {π : Measure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel q) π)
    (n : ℕ) (y : E) :
    weightedStartLaw (E := E) q hq π {ω | Function.eval n ω = y} = π ({y} : Set E) := by
  classical
  let P : E → ProbabilityMeasure (ℕ → E) := canonicalTrajProcess (E := E) q hq
  letI :
      IsMarkovProcessRealization (fun k ↦ discreteMatrixKernel q ^ k) P Function.eval := by
    simpa [P] using canonicalTrajProcess_isMarkovProcessRealization (E := E) q hq
  let hReal :
      IsMarkovProcessRealization (fun k ↦ discreteMatrixKernel q ^ k) P Function.eval :=
    inferInstance
  have hStateMeas : MeasurableSet ({ω : ℕ → E | Function.eval n ω = y} : Set (ℕ → E)) := by
    simpa [Set.preimage] using
      (hReal.measurable_process n) (MeasurableSet.singleton y)
  rw [weightedStartLaw, Measure.sum_apply _ hStateMeas]
  symm
  calc
    π ({y} : Set E) =
        ∑' z : E, π ({z} : Set E) * ((discreteMatrixKernel q ^ n) z ({y} : Set E)) :=
      invariantMeasureApplySingletonEqTsumPow (E := E) q hq hπ n y
    _ = ∑' z : E, π ({z} : Set E) * (P z : Measure (ℕ → E)) {ω | Function.eval n ω = y} := by
          refine tsum_congr fun z ↦ ?_
          have hz :
              (P z : Measure (ℕ → E)) ({ω : ℕ → E | Function.eval n ω = y} : Set (ℕ → E)) =
                ((discreteMatrixKernel q ^ n) z) ({y} : Set E) := by
            have hpreimage :
                ({ω : ℕ → E | Function.eval n ω = y} : Set (ℕ → E)) =
                  (Function.eval n : (ℕ → E) → E) ⁻¹' ({y} : Set E) := by
              ext ω
              simp
            rw [hpreimage]
            rw [← Measure.map_apply (hReal.measurable_process n) (MeasurableSet.singleton y)]
            rw [hReal.transition_eq z n]
          simpa [hz]

/-- Helper for Theorem 17.49: if a time-`n` history event already forces the current state to be
`z`, then intersecting it with the time-`n + m` singleton event factors through the `m`-step
transition mass from `z`. -/
private theorem measure_inter_prefix_stepEvent_eq_mulLocal [Countable E]
    (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q)
    {s z y : E} {A : Set (ℕ → E)} {n m : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace Function.eval n] A)
    (hA_sub : A ⊆ {ω | Function.eval n ω = z}) :
    (canonicalTrajProcess (E := E) q hq s : Measure (ℕ → E))
        (A ∩ {ω | Function.eval (n + m) ω = y}) =
      ((discreteMatrixKernel q ^ m) z ({y} : Set E)) *
        (canonicalTrajProcess (E := E) q hq s : Measure (ℕ → E)) A := by
  let P : E → ProbabilityMeasure (ℕ → E) := canonicalTrajProcess (E := E) q hq
  letI :
      IsMarkovProcessRealization (fun k ↦ discreteMatrixKernel q ^ k) P Function.eval := by
    simpa [P] using canonicalTrajProcess_isMarkovProcessRealization (E := E) q hq
  let μ : Measure (ℕ → E) := P s
  let hReal :
      IsMarkovProcessRealization (fun k ↦ discreteMatrixKernel q ^ k) P Function.eval :=
    inferInstance
  let B : Set (ℕ → E) := Function.eval (n + m) ⁻¹' ({y} : Set E)
  have hB_meas : MeasurableSet B := by
    simpa [B] using (hReal.measurable_process (n + m)) (MeasurableSet.singleton y)
  have hA_measAmbient : MeasurableSet A := by
    exact (generatedFiltrationSpace_le_ambient Function.eval hReal.measurable_process n) _ hA_meas
  have hMarkovGenerated :
      μ⟦B | generatedFiltrationSpace Function.eval n⟧ =ᵐ[μ]
        fun ω ↦ (((discreteMatrixKernel q ^ m) (Function.eval n ω)).real ({y} : Set E)) := by
    simpa [μ, B, add_comm] using
      hReal.markov_property s (A := ({y} : Set E)) (MeasurableSet.singleton y) n m
  have hIndicatorIntegrable : Integrable (B.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hB_meas
  have hstep :
      μ.real (A ∩ {ω | Function.eval (n + m) ω = y}) =
        (((discreteMatrixKernel q ^ m) z ({y} : Set E)).toReal) * μ.real A := by
    -- Proof comment: integrate the Markov conditional-expectation identity over `A`, then freeze
    -- the future row at `z` because `A` already pins down the state at time `n`.
    calc
      μ.real (A ∩ {ω | Function.eval (n + m) ω = y}) =
          ∫ ω in A, (μ⟦B | generatedFiltrationSpace Function.eval n⟧) ω ∂ μ := by
            rw [setIntegral_condExp
              (generatedFiltrationSpace_le_ambient Function.eval hReal.measurable_process n)
              hIndicatorIntegrable hA_meas, ← integral_indicator hA_measAmbient]
            symm
            simpa [B, Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm,
              smul_eq_mul] using integral_indicator_const (1 : ℝ) (hA_measAmbient.inter hB_meas)
      _ = ∫ ω in A, (((discreteMatrixKernel q ^ m) (Function.eval n ω)).real ({y} : Set E)) ∂ μ := by
            exact integral_congr_ae hMarkovGenerated.restrict
      _ = ∫ _ in A, (((discreteMatrixKernel q ^ m) z ({y} : Set E)).toReal) ∂ μ := by
            refine integral_congr_ae ?_
            filter_upwards [self_mem_ae_restrict (μ := μ) (s := A) hA_measAmbient] with ω hω
            have hω : Function.eval n ω = z := hA_sub hω
            rw [hω]
            rfl
      _ = (((discreteMatrixKernel q ^ m) z ({y} : Set E)).toReal) * μ.real A := by
            rw [setIntegral_const, smul_eq_mul, mul_comm]
  have hleft_ne_top :
      (P s : Measure (ℕ → E)) (A ∩ {ω | Function.eval (n + m) ω = y}) ≠ ⊤ :=
    measure_ne_top _ _
  letI : IsMarkovKernel (discreteMatrixKernel q ^ m) := hReal.semigroup.isMarkovKernel m
  have hkernel_ne_top : ((discreteMatrixKernel q ^ m) z) ({y} : Set E) ≠ ⊤ :=
    measure_ne_top _ _
  have hA_ne_top : (P s : Measure (ℕ → E)) A ≠ ⊤ :=
    measure_ne_top _ _
  have hkernel_toReal_nonneg : 0 ≤ (((discreteMatrixKernel q ^ m) z ({y} : Set E)).toReal) :=
    ENNReal.toReal_nonneg
  -- Proof comment: transport the real-valued factorization back to `ℝ≥0∞`.
  calc
    (P s : Measure (ℕ → E)) (A ∩ {ω | Function.eval (n + m) ω = y}) =
        ENNReal.ofReal ((P s : Measure (ℕ → E)).real (A ∩ {ω | Function.eval (n + m) ω = y})) := by
          symm
          exact ENNReal.ofReal_toReal hleft_ne_top
    _ = ENNReal.ofReal
        ((((discreteMatrixKernel q ^ m) z ({y} : Set E)).toReal) * (P s : Measure (ℕ → E)).real A) := by
          rw [hstep]
    _ = ((discreteMatrixKernel q ^ m) z ({y} : Set E)) * (P s : Measure (ℕ → E)) A := by
          rw [ENNReal.ofReal_mul hkernel_toReal_nonneg, ENNReal.ofReal_toReal hkernel_ne_top,
            Measure.real_def, ENNReal.ofReal_toReal hA_ne_top]

/-- Helper for Theorem 17.49: the weighted start law evaluates a start-state event by keeping
only the `x`-row of the weighted sum. -/
private theorem weightedStartLaw_apply_startState_beforeReturn [Countable E]
    (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q) {π : Measure E}
    (x y : E) (k : ℕ) :
    weightedStartLaw (E := E) q hq π
      {ω | Function.eval 0 ω = x ∧ Function.eval k ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω} =
        π ({x} : Set E) *
          (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
            {ω | Function.eval k ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω} := by
  classical
  let P : E → ProbabilityMeasure (ℕ → E) := canonicalTrajProcess (E := E) q hq
  letI :
      IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P Function.eval := by
    simpa [P] using canonicalTrajProcess_isMarkovProcessRealization (E := E) q hq
  let hReal :
      IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P Function.eval :=
    inferInstance
  let A : Set (ℕ → E) :=
    {ω | Function.eval 0 ω = x ∧ Function.eval k ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω}
  let B : Set (ℕ → E) :=
    {ω | Function.eval k ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω}
  have hState0_meas : MeasurableSet ({ω : ℕ → E | Function.eval 0 ω = x} : Set (ℕ → E)) := by
    simpa [Set.preimage] using
      (hReal.measurable_process 0) (MeasurableSet.singleton x)
  have hTail_meas : MeasurableSet {ω | (k : ℕ∞) < (τ_[Function.eval, x]^1) ω} :=
    measurableSet_firstReturnTimeTailLocal
      (κ := fun n ↦ discreteMatrixKernel q ^ n) (P := P) (X := Function.eval) x k
  have hB_meas : MeasurableSet B := by
    have hStateK : MeasurableSet ({ω : ℕ → E | Function.eval k ω = y} : Set (ℕ → E)) := by
      simpa [Set.preimage] using
        (hReal.measurable_process k) (MeasurableSet.singleton y)
    exact hStateK.inter hTail_meas
  have hA_eq : A = {ω | Function.eval 0 ω = x} ∩ B := by
    ext ω
    simp [A, B, and_left_comm, and_assoc]
  have hA_meas : MeasurableSet A := by
    rw [hA_eq]
    exact hState0_meas.inter hB_meas
  rw [weightedStartLaw, Measure.sum_apply _ hA_meas]
  simp_rw [Measure.smul_apply]
  have hPx_stateNe_zero : (P x : Measure (ℕ → E)) {ω | Function.eval 0 ω ≠ x} = 0 := by
    have hpreimage :
        {ω | Function.eval 0 ω ≠ x} =
          (Function.eval 0 : (ℕ → E) → E) ⁻¹' ({x} : Set E)ᶜ := by
      ext ω
      simp
    rw [hpreimage, ← Measure.map_apply (hReal.measurable_process 0) (MeasurableSet.singleton x).compl]
    rw [hReal.initial_eq x]
    simp
  have hAx : (P x : Measure (ℕ → E)) A = (P x : Measure (ℕ → E)) B := by
    have hDecomp : B = A ∪ (B ∩ {ω | Function.eval 0 ω ≠ x}) := by
      ext ω
      by_cases hω : Function.eval 0 ω = x <;> simp [A, B, hω]
    have hDisj : Disjoint A (B ∩ {ω | Function.eval 0 ω ≠ x}) := by
      refine Set.disjoint_left.2 ?_
      intro ω hωA hωB
      exact hωB.2 hωA.1
    have hRest_zero : (P x : Measure (ℕ → E)) (B ∩ {ω | Function.eval 0 ω ≠ x}) = 0 := by
      exact measure_mono_null Set.inter_subset_right hPx_stateNe_zero
    calc
      (P x : Measure (ℕ → E)) A = (P x : Measure (ℕ → E)) A + 0 := by simp
      _ = (P x : Measure (ℕ → E)) A + (P x : Measure (ℕ → E)) (B ∩ {ω | Function.eval 0 ω ≠ x}) := by
            rw [hRest_zero]
      _ = (P x : Measure (ℕ → E)) (A ∪ (B ∩ {ω | Function.eval 0 ω ≠ x})) := by
            rw [measure_union hDisj (hB_meas.inter hState0_meas.compl)]
      _ = (P x : Measure (ℕ → E)) B := by
            simpa using congrArg (fun s : Set (ℕ → E) ↦ (P x : Measure (ℕ → E)) s) hDecomp.symm
  have hz_zero : ∀ z : E, z ≠ x → (P z : Measure (ℕ → E)) A = 0 := by
    intro z hzx
    have hStateZero : (P z : Measure (ℕ → E)) {ω | Function.eval 0 ω = x} = 0 := by
      have hpreimage :
          {ω | Function.eval 0 ω = x} =
            (Function.eval 0 : (ℕ → E) → E) ⁻¹' ({x} : Set E) := by
        ext ω
        simp
      rw [hpreimage, ← Measure.map_apply (hReal.measurable_process 0) (MeasurableSet.singleton x)]
      rw [hReal.initial_eq z]
      simp [hzx]
    have hA_sub : A ⊆ {ω | Function.eval 0 ω = x} := by
      intro ω hω
      exact hω.1
    exact le_antisymm
      (le_trans (measure_mono hA_sub) (by simpa [hStateZero]))
      bot_le
  -- Proof comment: the event already forces `X 0 = x`, so every row except the `x`-row vanishes.
  calc
    ∑' z : E, π ({z} : Set E) * (P z : Measure (ℕ → E)) A
        = π ({x} : Set E) * (P x : Measure (ℕ → E)) A := by
            refine tsum_eq_single x ?_
            intro z hzx
            simp [hz_zero z hzx]
    _ = π ({x} : Set E) * (P x : Measure (ℕ → E)) B := by rw [hAx]

/-- Helper for Theorem 17.49: off the reference diagonal, the time-`k + 1` before-return event
already implies that the chain is still before the first return at time `k + 1`. -/
private theorem beforeReturnStep_offDiag_eq_succTail [Countable E]
    (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q)
    {x y : E} (hyx : y ≠ x) (k : ℕ) :
    (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
      {ω | Function.eval (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω} =
    (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
      {ω | Function.eval (k + 1) ω = y ∧ (((k + 1 : ℕ) : ℕ∞) < (τ_[Function.eval, x]^1) ω)} := by
  have hSet :
      {ω | Function.eval (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω} =
        {ω | Function.eval (k + 1) ω = y ∧ (((k + 1 : ℕ) : ℕ∞) < (τ_[Function.eval, x]^1) ω)} := by
    ext ω
    constructor
    · rintro ⟨hstate, htail⟩
      have hsuccTail : (((k + 1 : ℕ) : ℕ∞) < (τ_[Function.eval, x]^1) ω) := by
        by_contra hnot
        have hle : (τ_[Function.eval, x]^1) ω ≤ k + 1 := le_of_not_gt hnot
        have hlt_top : (τ_[Function.eval, x]^1) ω < ⊤ := lt_of_le_of_lt hle (by simp)
        let m := ENat.lift ((τ_[Function.eval, x]^1) ω) hlt_top
        have hm_eq : (m : ℕ∞) = (τ_[Function.eval, x]^1) ω :=
          ENat.coe_lift ((τ_[Function.eval, x]^1) ω) hlt_top
        have hm_le : m ≤ k + 1 := by
          simpa [m, hm_eq] using hle
        have hk_lt_m : k < m := by
          simpa [m, hm_eq] using htail
        have hm : m = k + 1 := Nat.le_antisymm hm_le (Nat.succ_le_of_lt hk_lt_m)
        have hτeq : (τ_[Function.eval, x]^1) ω = k + 1 := by
          calc
            (τ_[Function.eval, x]^1) ω = (m : ℕ∞) := hm_eq.symm
            _ = k + 1 := by simpa [hm]
        have hxstate : Function.eval (k + 1) ω = x := by
          have hcoene : ((k + 1 : ℕ) : ℕ∞) ≠ ⊤ := ENat.coe_ne_top (k + 1)
          have hne_top : (τ_[Function.eval, x]^1) ω ≠ ⊤ := by simpa [hτeq] using hcoene
          have hmem :
              Function.eval (((τ_[Function.eval, x]^1) ω).untopA) ω = x := by
            have h :
                Function.eval (MeasureTheory.hittingAfter Function.eval ({x} : Set E) 1 ω).untopA ω ∈
                  ({x} : Set E) :=
              hittingAfter_mem_set_of_ne_top (by simpa [iteratedEntranceTime_one] using hne_top)
            simpa [iteratedEntranceTime_one, Set.mem_singleton_iff] using h
          have huntop : ((τ_[Function.eval, x]^1) ω).untopA = k + 1 := by
            rw [WithTop.untopA_eq_untop hne_top]
            simpa [ENat.lift, hτeq] using ENat.lift_coe (k + 1)
          simpa [huntop] using hmem
        exact hyx (hstate.symm.trans hxstate)
      exact ⟨hstate, hsuccTail⟩
    · rintro ⟨hstate, htail⟩
      exact ⟨hstate, lt_trans (by exact_mod_cast Nat.lt_succ_self k) htail⟩
  rw [hSet]

/-- Helper for Theorem 17.49: the remainder term in the textbook induction is the weighted-start
mass of paths that start away from `x`, land at `y` at time `n`, and have not yet returned to
`x`. -/
private def offDiagFirstReturnRemainder [Countable E] (x y : E) (n : ℕ) : Set (ℕ → E) :=
  {ω | Function.eval 0 ω ≠ x ∧ Function.eval n ω = y ∧ (n : ℕ∞) < (τ_[Function.eval, x]^1) ω}

/-- Helper for Theorem 17.49: the off-diagonal remainder event is measurable. -/
private theorem measurableSet_offDiagFirstReturnRemainder [Countable E]
    (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q)
    (x y : E) (n : ℕ) :
    MeasurableSet (offDiagFirstReturnRemainder (E := E) x y n) := by
  let P : E → ProbabilityMeasure (ℕ → E) := canonicalTrajProcess (E := E) q hq
  letI :
      IsMarkovProcessRealization (fun k ↦ discreteMatrixKernel q ^ k) P Function.eval := by
    simpa [P] using canonicalTrajProcess_isMarkovProcessRealization (E := E) q hq
  let hReal :
      IsMarkovProcessRealization (fun k ↦ discreteMatrixKernel q ^ k) P Function.eval :=
    inferInstance
  have hState0 : MeasurableSet ({ω : ℕ → E | Function.eval 0 ω ≠ x} : Set (ℕ → E)) := by
    have hEq :
        ({ω : ℕ → E | Function.eval 0 ω ≠ x} : Set (ℕ → E)) =
          ({ω : ℕ → E | Function.eval 0 ω = x} : Set (ℕ → E))ᶜ := by
      ext ω
      simp [Function.eval]
    rw [hEq]
    exact ((hReal.measurable_process 0) (MeasurableSet.singleton x)).compl
  have hStateN : MeasurableSet ({ω : ℕ → E | Function.eval n ω = y} : Set (ℕ → E)) := by
    simpa [Set.preimage] using
      (hReal.measurable_process n) (MeasurableSet.singleton y)
  have hTail : MeasurableSet {ω | (n : ℕ∞) < (τ_[Function.eval, x]^1) ω} :=
    measurableSet_firstReturnTimeTailLocal
      (κ := fun k ↦ discreteMatrixKernel q ^ k) (P := P) (X := Function.eval) x n
  -- Proof comment: the remainder event is the intersection of one time-zero event, one time-`n`
  -- event, and the first-return tail event.
  exact hState0.inter (hStateN.inter hTail)

/-- Helper for Theorem 17.49: the off-diagonal remainder event is already measurable with
respect to the time-`n` history filtration. -/
private theorem measurableSet_offDiagFirstReturnRemainderInFiltration [Countable E]
    (x y : E) (n : ℕ) :
    MeasurableSet[generatedFiltrationSpace Function.eval n]
      (offDiagFirstReturnRemainder (E := E) x y n) := by
  have hX0_meas :
      Measurable[generatedFiltrationSpace Function.eval n] (Function.eval 0 : (ℕ → E) → E) := by
    refine Measurable.of_comap_le ?_
    exact le_iSup_of_le 0 <| le_iSup_of_le (Nat.zero_le n) le_rfl
  have hXn_meas :
      Measurable[generatedFiltrationSpace Function.eval n] (Function.eval n : (ℕ → E) → E) := by
    refine Measurable.of_comap_le ?_
    exact le_iSup_of_le n <| le_iSup_of_le le_rfl le_rfl
  have hState0 :
      MeasurableSet[generatedFiltrationSpace Function.eval n]
        ({ω : ℕ → E | Function.eval 0 ω ≠ x} : Set (ℕ → E)) := by
    have hEq :
        ({ω : ℕ → E | Function.eval 0 ω ≠ x} : Set (ℕ → E)) =
          (Function.eval 0 : (ℕ → E) → E) ⁻¹' ({x} : Set E)ᶜ := by
      ext ω
      simp [Function.eval]
    rw [hEq]
    exact (hX0_meas (MeasurableSet.singleton x)).compl
  have hStateN :
      MeasurableSet[generatedFiltrationSpace Function.eval n]
        ({ω : ℕ → E | Function.eval n ω = y} : Set (ℕ → E)) := by
    simpa [Set.preimage] using hXn_meas (MeasurableSet.singleton y)
  have hTail :
      MeasurableSet[generatedFiltrationSpace Function.eval n]
        {ω | (n : ℕ∞) < (τ_[Function.eval, x]^1) ω} := by
    have hEq :
        {ω | (n : ℕ∞) < (τ_[Function.eval, x]^1) ω} =
          {ω | (τ_[Function.eval, x]^1) ω ≤ n}ᶜ := by
      ext ω
      simp
    rw [hEq]
    have hLe :
        MeasurableSet[generatedFiltrationSpace Function.eval n]
          {ω | (τ_[Function.eval, x]^1) ω ≤ n} := by
      have hEqLe :
          {ω | (τ_[Function.eval, x]^1) ω ≤ n} =
            ⋃ j ∈ ((Finset.Icc 1 n : Finset ℕ) : Set ℕ), Function.eval j ⁻¹' ({x} : Set E) := by
        ext ω
        simp [firstReturnTime_le_iffLocal, Finset.mem_Icc]
      rw [hEqLe]
      refine MeasurableSet.biUnion (Set.to_countable _) ?_
      intro j hj
      have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
      have hXj :
          Measurable[generatedFiltrationSpace Function.eval n] (Function.eval j : (ℕ → E) → E) := by
        refine Measurable.of_comap_le ?_
        exact le_iSup_of_le j <| le_iSup_of_le hjn le_rfl
      simpa using hXj (MeasurableSet.singleton x)
    exact hLe.compl
  -- Proof comment: the same three ingredients as in the ambient measurability proof all live in
  -- the time-`n` filtration.
  exact hState0.inter (hStateN.inter hTail)

/-- Helper for Theorem 17.49: a filtration-measurable event that already pins down the state at
time `n` factors under the weighted start law through the `m`-step transition mass from that
state. -/
private theorem weightedStartLaw_inter_prefix_stepEvent_eq_mul [Countable E]
    (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q) {π : Measure E}
    {A : Set (ℕ → E)} {z y : E} {n m : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace Function.eval n] A)
    (hA_sub : A ⊆ {ω | Function.eval n ω = z}) :
    weightedStartLaw (E := E) q hq π (A ∩ {ω | Function.eval (n + m) ω = y}) =
      ((discreteMatrixKernel q ^ m) z ({y} : Set E)) *
        weightedStartLaw (E := E) q hq π A := by
  classical
  let P : E → ProbabilityMeasure (ℕ → E) := canonicalTrajProcess (E := E) q hq
  letI :
      IsMarkovProcessRealization (fun k ↦ discreteMatrixKernel q ^ k) P Function.eval := by
    simpa [P] using canonicalTrajProcess_isMarkovProcessRealization (E := E) q hq
  let hReal :
      IsMarkovProcessRealization (fun k ↦ discreteMatrixKernel q ^ k) P Function.eval :=
    inferInstance
  have hA_measAmbient : MeasurableSet A := by
    exact (generatedFiltrationSpace_le_ambient Function.eval hReal.measurable_process n) _ hA_meas
  have hStep_meas :
      MeasurableSet ({ω : ℕ → E | Function.eval (n + m) ω = y} : Set (ℕ → E)) := by
    simpa [Set.preimage] using
      (hReal.measurable_process (n + m)) (MeasurableSet.singleton y)
  -- Proof comment: factor each start-state row through the fixed state `z`, then pull the common
  -- transition mass out of the countable weighted sum.
  calc
    weightedStartLaw (E := E) q hq π (A ∩ {ω | Function.eval (n + m) ω = y})
        = ∑' s : E, π ({s} : Set E) *
            (P s : Measure (ℕ → E)) (A ∩ {ω | Function.eval (n + m) ω = y}) := by
            rw [weightedStartLaw, Measure.sum_apply _ (hA_measAmbient.inter hStep_meas)]
            simpa [P, Measure.smul_apply, smul_eq_mul]
    _ = ∑' s : E, π ({s} : Set E) *
          (((discreteMatrixKernel q ^ m) z ({y} : Set E)) * (P s : Measure (ℕ → E)) A) := by
            refine tsum_congr fun s ↦ ?_
            rw [measure_inter_prefix_stepEvent_eq_mulLocal
              (E := E) q hq (s := s) (z := z) (y := y) (n := n) (m := m) hA_meas hA_sub]
    _ = ∑' s : E, ((discreteMatrixKernel q ^ m) z ({y} : Set E)) *
          (π ({s} : Set E) * (P s : Measure (ℕ → E)) A) := by
            refine tsum_congr fun s ↦ ?_
            simpa [mul_assoc, mul_left_comm, mul_comm]
    _ = ((discreteMatrixKernel q ^ m) z ({y} : Set E)) *
          ∑' s : E, π ({s} : Set E) * (P s : Measure (ℕ → E)) A := by
            rw [ENNReal.tsum_mul_left]
    _ = ((discreteMatrixKernel q ^ m) z ({y} : Set E)) *
          weightedStartLaw (E := E) q hq π A := by
            rw [weightedStartLaw, Measure.sum_apply _ hA_measAmbient]
            simpa [P, Measure.smul_apply, smul_eq_mul]

/-- Helper for Theorem 17.49: the weighted start law sees the one-step `x → y` contribution as
exactly the first before-return excursion term. -/
private theorem weightedStartLaw_startStep_offDiag [Countable E]
    (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q) {π : Measure E}
    {x y : E} (hyx : y ≠ x) :
    π ({x} : Set E) * ((discreteMatrixKernel q ^ 1) x ({y} : Set E)) =
      weightedStartLaw (E := E) q hq π
        {ω | Function.eval 0 ω = x ∧ Function.eval 1 ω = y ∧
          (((1 : ℕ) : ℕ∞) < (τ_[Function.eval, x]^1) ω)} := by
  let P : E → ProbabilityMeasure (ℕ → E) := canonicalTrajProcess (E := E) q hq
  letI :
      IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P Function.eval := by
    simpa [P] using canonicalTrajProcess_isMarkovProcessRealization (E := E) q hq
  let hReal :
      IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P Function.eval :=
    inferInstance
  have hStateOne :
      (P x : Measure (ℕ → E)) {ω | Function.eval 1 ω = y} =
        ((discreteMatrixKernel q ^ 1) x) ({y} : Set E) := by
    have hpreimage :
        {ω | Function.eval 1 ω = y} =
          (Function.eval 1 : (ℕ → E) → E) ⁻¹' ({y} : Set E) := by
      ext ω
      simp
    rw [hpreimage]
    rw [← Measure.map_apply (hReal.measurable_process 1) (MeasurableSet.singleton y)]
    rw [hReal.transition_eq x 1]
  have hTauPos : ∀ ω : ℕ → E, (0 : ℕ∞) < (τ_[Function.eval, x]^1) ω := by
    intro ω
    have hτge1 : (1 : ℕ∞) ≤ (τ_[Function.eval, x]^1) ω := by
      have h : (1 : ℕ) ≤ MeasureTheory.hittingAfter Function.eval ({x} : Set E) 1 ω :=
        le_hittingAfter ω
      simpa [iteratedEntranceTime_one] using h
    exact lt_of_lt_of_le (by simp) hτge1
  have hTailZero :
      {ω | Function.eval 1 ω = y} =
        {ω | Function.eval 1 ω = y ∧ ((0 : ℕ) : ℕ∞) < (τ_[Function.eval, x]^1) ω} := by
    ext ω
    constructor
    · intro hω
      exact ⟨hω, hTauPos ω⟩
    · intro hω
      exact hω.1
  -- Proof comment: first rewrite the one-step kernel row as a path event, then upgrade the
  -- tail condition from `0 < τ_x^1` to `1 < τ_x^1` using the off-diagonal hypothesis.
  calc
    π ({x} : Set E) * ((discreteMatrixKernel q ^ 1) x ({y} : Set E))
        = π ({x} : Set E) * (P x : Measure (ℕ → E)) {ω | Function.eval 1 ω = y} := by
            rw [hStateOne]
    _ = π ({x} : Set E) * (P x : Measure (ℕ → E))
          {ω | Function.eval 1 ω = y ∧ ((0 : ℕ) : ℕ∞) < (τ_[Function.eval, x]^1) ω} := by
            rw [← hTailZero]
    _ = π ({x} : Set E) * (P x : Measure (ℕ → E))
          {ω | Function.eval 1 ω = y ∧ (((1 : ℕ) : ℕ∞) < (τ_[Function.eval, x]^1) ω)} := by
            rw [beforeReturnStep_offDiag_eq_succTail (E := E) q hq hyx 0]
    _ = weightedStartLaw (E := E) q hq π
          {ω | Function.eval 0 ω = x ∧ Function.eval 1 ω = y ∧
            (((1 : ℕ) : ℕ∞) < (τ_[Function.eval, x]^1) ω)} := by
            symm
            simpa using
              weightedStartLaw_apply_startState_beforeReturn (E := E) q hq (π := π) x y 1

/-- Helper for Theorem 17.49: summing the off-diagonal remainder slices over the intermediate
state at time `n` recovers the propagated remainder event at time `n + 1`. -/
private theorem weightedStartLaw_remainderStepSliceSum [Countable E]
    (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q) {π : Measure E}
    {x y : E} (n : ℕ) :
    (∑' z : E,
      weightedStartLaw (E := E) q hq π
        {ω | Function.eval 0 ω ≠ x ∧ Function.eval n ω = z ∧
          (n : ℕ∞) < (τ_[Function.eval, x]^1) ω ∧ Function.eval (n + 1) ω = y}) =
      weightedStartLaw (E := E) q hq π
        {ω | Function.eval 0 ω ≠ x ∧ Function.eval (n + 1) ω = y ∧
          (n : ℕ∞) < (τ_[Function.eval, x]^1) ω} := by
  let A : E → Set (ℕ → E) := fun z ↦
    {ω | Function.eval 0 ω ≠ x ∧ Function.eval n ω = z ∧
      (n : ℕ∞) < (τ_[Function.eval, x]^1) ω ∧ Function.eval (n + 1) ω = y}
  have hPairwise : Pairwise fun z₁ z₂ ↦ Disjoint (A z₁) (A z₂) := by
    intro z₁ z₂ hz
    refine Set.disjoint_left.2 ?_
    intro ω hω₁ hω₂
    exact hz (hω₁.2.1.symm.trans hω₂.2.1)
  have hMeas : ∀ z : E, MeasurableSet (A z) := by
    intro z
    have hBase :
        MeasurableSet (offDiagFirstReturnRemainder (E := E) x z n) :=
      measurableSet_offDiagFirstReturnRemainder (E := E) q hq x z n
    let P : E → ProbabilityMeasure (ℕ → E) := canonicalTrajProcess (E := E) q hq
    letI :
        IsMarkovProcessRealization (fun k ↦ discreteMatrixKernel q ^ k) P Function.eval := by
      simpa [P] using canonicalTrajProcess_isMarkovProcessRealization (E := E) q hq
    let hReal :
        IsMarkovProcessRealization (fun k ↦ discreteMatrixKernel q ^ k) P Function.eval :=
      inferInstance
    have hNext : MeasurableSet ({ω : ℕ → E | Function.eval (n + 1) ω = y} : Set (ℕ → E)) := by
      simpa [Set.preimage] using
        (hReal.measurable_process (n + 1)) (MeasurableSet.singleton y)
    have hEq :
        A z =
          offDiagFirstReturnRemainder (E := E) x z n ∩ {ω | Function.eval (n + 1) ω = y} := by
      ext ω
      simp [A, offDiagFirstReturnRemainder, and_assoc, and_left_comm, and_comm]
    rw [hEq]
    exact hBase.inter hNext
  have hUnion :
      (⋃ z : E, A z) =
        {ω | Function.eval 0 ω ≠ x ∧ Function.eval (n + 1) ω = y ∧
          (n : ℕ∞) < (τ_[Function.eval, x]^1) ω} := by
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨z, hz⟩
      exact ⟨hz.1, hz.2.2.2, hz.2.2.1⟩
    · intro hω
      refine Set.mem_iUnion.2 ⟨Function.eval n ω, ?_⟩
      exact ⟨hω.1, rfl, hω.2.2, hω.2.1⟩
  -- Proof comment: the time-`n` state slices are pairwise disjoint and cover the propagated
  -- remainder event.
  rw [← hUnion]
  symm
  exact measure_iUnion hPairwise hMeas

/-- Helper for Theorem 17.49: summing the time-`k` before-return slices over the intermediate
state recovers the time-`k + 1` before-return event. -/
private theorem beforeReturnStepSliceSum_eq [Countable E]
    (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q)
    {x y : E} (k : ℕ) :
    (∑' z : E,
      (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
        {ω | Function.eval k ω = z ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω ∧
          Function.eval (k + 1) ω = y}) =
      (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
        {ω | Function.eval (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω} := by
  let A : E → Set (ℕ → E) := fun z ↦
    {ω | Function.eval k ω = z ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω ∧
      Function.eval (k + 1) ω = y}
  have hPairwise : Pairwise fun z₁ z₂ ↦ Disjoint (A z₁) (A z₂) := by
    intro z₁ z₂ hz
    refine Set.disjoint_left.2 ?_
    intro ω hω₁ hω₂
    exact hz (hω₁.1.symm.trans hω₂.1)
  have hMeas : ∀ z : E, MeasurableSet (A z) := by
    intro z
    let P : E → ProbabilityMeasure (ℕ → E) := canonicalTrajProcess (E := E) q hq
    letI :
        IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P Function.eval := by
      simpa [P] using canonicalTrajProcess_isMarkovProcessRealization (E := E) q hq
    let hReal :
        IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P Function.eval :=
      inferInstance
    have hXk : MeasurableSet ({ω : ℕ → E | Function.eval k ω = z} : Set (ℕ → E)) := by
      simpa [Set.preimage] using
        (hReal.measurable_process k) (MeasurableSet.singleton z)
    have hTail : MeasurableSet {ω | (k : ℕ∞) < (τ_[Function.eval, x]^1) ω} :=
      measurableSet_firstReturnTimeTailLocal
        (κ := fun n ↦ discreteMatrixKernel q ^ n) (P := P) (X := Function.eval) x k
    have hNext : MeasurableSet ({ω : ℕ → E | Function.eval (k + 1) ω = y} : Set (ℕ → E)) := by
      simpa [Set.preimage] using
        (hReal.measurable_process (k + 1)) (MeasurableSet.singleton y)
    have hEq :
        A z =
          {ω | Function.eval k ω = z} ∩
            ({ω | (k : ℕ∞) < (τ_[Function.eval, x]^1) ω} ∩
              {ω | Function.eval (k + 1) ω = y}) := by
      ext ω
      simp [A, and_assoc]
    rw [hEq]
    exact hXk.inter (hTail.inter hNext)
  have hUnion :
      (⋃ z : E, A z) =
        {ω | Function.eval (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω} := by
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨z, hz⟩
      exact ⟨hz.2.2, hz.2.1⟩
    · intro hω
      refine Set.mem_iUnion.2 ⟨Function.eval k ω, ?_⟩
      exact ⟨rfl, hω.2, hω.1⟩
  -- Proof comment: the state slices at time `k` are pairwise disjoint and cover the target
  -- before-return event.
  rw [← hUnion]
  symm
  exact measure_iUnion hPairwise hMeas

/-- Helper for Theorem 17.49: the event `X n = z` together with the first-return tail is already
measurable in the time-`n` filtration. -/
private theorem measurableSet_beforeReturnStateInFiltration [Countable E]
    (x z : E) (n : ℕ) :
    MeasurableSet[generatedFiltrationSpace Function.eval n]
      {ω | Function.eval n ω = z ∧ (n : ℕ∞) < (τ_[Function.eval, x]^1) ω} := by
  have hXn :
      Measurable[generatedFiltrationSpace Function.eval n] (Function.eval n : (ℕ → E) → E) := by
    refine Measurable.of_comap_le ?_
    exact le_iSup_of_le n <| le_iSup_of_le le_rfl le_rfl
  have hState :
      MeasurableSet[generatedFiltrationSpace Function.eval n]
        ({ω : ℕ → E | Function.eval n ω = z} : Set (ℕ → E)) := by
    simpa [Set.preimage] using hXn (MeasurableSet.singleton z)
  have hTail :
      MeasurableSet[generatedFiltrationSpace Function.eval n]
        {ω | (n : ℕ∞) < (τ_[Function.eval, x]^1) ω} := by
    have hEq :
        {ω | (n : ℕ∞) < (τ_[Function.eval, x]^1) ω} =
          {ω | (τ_[Function.eval, x]^1) ω ≤ n}ᶜ := by
      ext ω
      simp
    rw [hEq]
    have hLe :
        MeasurableSet[generatedFiltrationSpace Function.eval n]
          {ω | (τ_[Function.eval, x]^1) ω ≤ n} := by
      have hEqLe :
          {ω | (τ_[Function.eval, x]^1) ω ≤ n} =
            ⋃ j ∈ ((Finset.Icc 1 n : Finset ℕ) : Set ℕ), Function.eval j ⁻¹' ({x} : Set E) := by
        ext ω
        simp [firstReturnTime_le_iffLocal]
      rw [hEqLe]
      refine MeasurableSet.biUnion (Set.to_countable _) ?_
      intro j hj
      have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
      have hXj :
          Measurable[generatedFiltrationSpace Function.eval n] (Function.eval j : (ℕ → E) → E) := by
        refine Measurable.of_comap_le ?_
        exact le_iSup_of_le j <| le_iSup_of_le hjn le_rfl
      simpa using hXj (MeasurableSet.singleton x)
    exact hLe.compl
  exact hState.inter hTail

/-- Helper for Theorem 17.49: the off-diagonal remainder cannot already be at the reference
state `x` at time `n`. -/
private theorem offDiagFirstReturnRemainder_self_empty [Countable E]
    (x : E) (n : ℕ) :
    offDiagFirstReturnRemainder (E := E) x x n = (∅ : Set (ℕ → E)) := by
  ext ω
  constructor
  · intro hω
    rcases hω with ⟨hStart, hState, hTail⟩
    by_cases hn : n = 0
    · subst hn
      exact hStart hState
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      have hle : (τ_[Function.eval, x]^1) ω ≤ n :=
        (firstReturnTime_le_iffLocal (X := Function.eval) x n ω).2
          ⟨n, ⟨hn_pos, le_rfl⟩, hState⟩
      exact False.elim <| (not_lt_of_ge hle) hTail
  · simp

/-- Helper for Theorem 17.49: starting from `x`, the before-return event cannot be back at `x`
at any positive time. -/
private theorem beforeReturnStateMass_self_eq_zero [Countable E]
    (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q)
    (x : E) {k : ℕ} (hk : 0 < k) :
    (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
      {ω | Function.eval k ω = x ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω} = 0 := by
  have hEmpty :
      {ω | Function.eval k ω = x ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω} =
        (∅ : Set (ℕ → E)) := by
    ext ω
    constructor
    · intro hω
      have hle : (τ_[Function.eval, x]^1) ω ≤ k :=
        (firstReturnTime_le_iffLocal (X := Function.eval) x k ω).2 ⟨k, ⟨hk, le_rfl⟩, hω.1⟩
      exact False.elim <| (not_lt_of_ge hle) hω.2
    · simp
  rw [hEmpty]
  simp

/-- Helper for Theorem 17.49: off the diagonal, the propagated weighted-start remainder event
already forces the stronger tail condition at time `n + 1`. -/
private theorem offDiagRemainderStep_eq_succ [Countable E]
    {x y : E} (hyx : y ≠ x) (n : ℕ) :
    {ω | Function.eval 0 ω ≠ x ∧ Function.eval (n + 1) ω = y ∧
      (n : ℕ∞) < (τ_[Function.eval, x]^1) ω} =
      offDiagFirstReturnRemainder (E := E) x y (n + 1) := by
  ext ω
  constructor
  · rintro ⟨hStart, hState, hTail⟩
    have hSuccTail : (((n + 1 : ℕ) : ℕ∞) < (τ_[Function.eval, x]^1) ω) := by
      by_contra hnot
      have hle : (τ_[Function.eval, x]^1) ω ≤ n + 1 := le_of_not_gt hnot
      have hlt_top : (τ_[Function.eval, x]^1) ω < ⊤ := lt_of_le_of_lt hle (by simp)
      let m := ENat.lift ((τ_[Function.eval, x]^1) ω) hlt_top
      have hm_eq : (m : ℕ∞) = (τ_[Function.eval, x]^1) ω :=
        ENat.coe_lift ((τ_[Function.eval, x]^1) ω) hlt_top
      have hm_le : m ≤ n + 1 := by
        simpa [m, hm_eq] using hle
      have hn_lt_m : n < m := by
        simpa [m, hm_eq] using hTail
      have hm : m = n + 1 := Nat.le_antisymm hm_le (Nat.succ_le_of_lt hn_lt_m)
      have hτeq : (τ_[Function.eval, x]^1) ω = n + 1 := by
        calc
          (τ_[Function.eval, x]^1) ω = (m : ℕ∞) := hm_eq.symm
          _ = n + 1 := by simpa [hm]
      have hxState : Function.eval (n + 1) ω = x := by
        have hcoene : ((n + 1 : ℕ) : ℕ∞) ≠ ⊤ := ENat.coe_ne_top (n + 1)
        have hne_top : (τ_[Function.eval, x]^1) ω ≠ ⊤ := by simpa [hτeq] using hcoene
        have hmem :
            Function.eval (((τ_[Function.eval, x]^1) ω).untopA) ω = x := by
          have h :
              Function.eval (MeasureTheory.hittingAfter Function.eval ({x} : Set E) 1 ω).untopA ω ∈
                ({x} : Set E) :=
            hittingAfter_mem_set_of_ne_top (by simpa [iteratedEntranceTime_one] using hne_top)
          simpa [iteratedEntranceTime_one, Set.mem_singleton_iff] using h
        have huntop : ((τ_[Function.eval, x]^1) ω).untopA = n + 1 := by
          rw [WithTop.untopA_eq_untop hne_top]
          simpa [ENat.lift, hτeq] using ENat.lift_coe (n + 1)
        simpa [huntop] using hmem
      exact False.elim <| hyx (hState.symm.trans hxState)
    exact ⟨hStart, hState, hSuccTail⟩
  · rintro ⟨hStart, hState, hTail⟩
    exact ⟨hStart, hState, lt_trans (by exact_mod_cast Nat.lt_succ_self n) hTail⟩

/-- Helper for Theorem 17.49: the first excursion term together with the shifted before-return
tail over `Finset.Icc 1 n` is exactly the `Finset.Icc 1 (n + 1)` partial sum used in the
textbook decomposition. -/
private theorem sumBeforeReturnShift_eq_IccSucc [Countable E]
    (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q)
    {x y : E} (hyx : y ≠ x) (n : ℕ) :
    (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
      {ω | Function.eval 1 ω = y ∧ (((1 : ℕ) : ℕ∞) < (τ_[Function.eval, x]^1) ω)} +
      Finset.sum (Finset.Icc 1 n)
        (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
          {ω | Function.eval (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω}) =
      Finset.sum (Finset.Icc 1 (n + 1))
        (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
          {ω | Function.eval k ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω}) := by
  have hShift :
      Finset.sum (Finset.Icc 1 n)
        (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
          {ω | Function.eval (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω}) =
      Finset.sum (Finset.Icc 2 (n + 1))
        (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
          {ω | Function.eval k ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω}) := by
    -- Proof comment: first upgrade each tail event from `k < τ_x^1` to `(k + 1) < τ_x^1`,
    -- then reindex the interval by the successor map.
    calc
      Finset.sum (Finset.Icc 1 n)
          (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
            {ω | Function.eval (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω}) =
        Finset.sum (Finset.Icc 1 n)
          (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
            {ω | Function.eval (k + 1) ω = y ∧ (((k + 1 : ℕ) : ℕ∞) < (τ_[Function.eval, x]^1) ω)}) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              exact beforeReturnStep_offDiag_eq_succTail (E := E) q hq hyx k
      _ = Finset.sum ((Finset.Icc 1 n).image (fun k : ℕ ↦ k + 1))
          (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
            {ω | Function.eval k ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω}) := by
            symm
            refine Finset.sum_image ?_
            intro a _ b _ hab
            exact Nat.succ.inj hab
      _ = Finset.sum (Finset.Icc 2 (n + 1))
          (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
            {ω | Function.eval k ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω}) := by
            have hImage :
                (Finset.Icc 1 n).image (fun k : ℕ ↦ k + 1) = Finset.Icc 2 (n + 1) := by
              ext k
              simp [Finset.mem_Icc]
            rw [hImage]
  -- Proof comment: insert the `k = 1` term back into the shifted tail to recover the full
  -- `Finset.Icc 1 (n + 1)` partial sum.
  calc
    (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
        {ω | Function.eval 1 ω = y ∧ (((1 : ℕ) : ℕ∞) < (τ_[Function.eval, x]^1) ω)} +
        Finset.sum (Finset.Icc 1 n)
          (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
            {ω | Function.eval (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω}) =
      (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
        {ω | Function.eval 1 ω = y ∧ (((1 : ℕ) : ℕ∞) < (τ_[Function.eval, x]^1) ω)} +
        Finset.sum (Finset.Icc 2 (n + 1))
          (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
            {ω | Function.eval k ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω}) := by
            rw [hShift]
    _ = Finset.sum (insert 1 (Finset.Icc 2 (n + 1)))
        (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
          {ω | Function.eval k ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω}) := by
          have hnotin : 1 ∉ Finset.Icc 2 (n + 1) := by simp
          rw [Finset.sum_insert hnotin]
    _ = Finset.sum (Finset.Icc 1 (n + 1))
        (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
          {ω | Function.eval k ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω}) := by
          have hInsert : insert 1 (Finset.Icc 2 (n + 1)) = Finset.Icc 1 (n + 1) := by
            ext k
            simp [Finset.mem_Icc]
            omega
          rw [hInsert]

/-- Helper for Theorem 17.49: intersecting the off-diagonal remainder event with the next-state
singleton gives the canonical four-conjunct step slice used in the reassembly lemma. -/
private theorem offDiagFirstReturnRemainder_stepSlice_eq [Countable E]
    (x z y : E) (n : ℕ) :
    offDiagFirstReturnRemainder (E := E) x z n ∩ {ω | Function.eval (n + 1) ω = y} =
      {ω | Function.eval 0 ω ≠ x ∧ Function.eval n ω = z ∧
        (n : ℕ∞) < (τ_[Function.eval, x]^1) ω ∧ Function.eval (n + 1) ω = y} := by
  -- Proof comment: this is the canonical reassociation of the remainder event with the one-step
  -- state event.
  ext ω
  simp [offDiagFirstReturnRemainder, and_assoc, and_left_comm, and_comm]

/-- Helper for Theorem 17.49: intersecting a before-return state slice with the next-state
singleton gives the canonical three-conjunct step slice used in the reassembly lemma. -/
private theorem beforeReturnState_stepSlice_eq [Countable E]
    (x z y : E) (k : ℕ) :
    {ω | Function.eval k ω = z ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω} ∩
        {ω | Function.eval (k + 1) ω = y} =
      {ω | Function.eval k ω = z ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω ∧
        Function.eval (k + 1) ω = y} := by
  -- Proof comment: the before-return slice only needs a single reassociation with the next-step
  -- singleton event.
  ext ω
  simp [and_assoc]

/-- Helper for Theorem 17.49: a time-`k` before-return state slice transports through one more
step to the corresponding canonical step slice. -/
private theorem beforeReturnStepSliceMass_eq [Countable E]
    (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q)
    (x z y : E) (k : ℕ) :
    (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
        {ω | Function.eval k ω = z ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω} *
      ((discreteMatrixKernel q ^ 1) z ({y} : Set E)) =
        (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
          {ω | Function.eval k ω = z ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω ∧
            Function.eval (k + 1) ω = y} := by
  -- Proof comment: first transport the one-step factor through the prefix event, then rewrite
  -- the resulting intersection into the canonical step-slice form.
  calc
    (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
        {ω | Function.eval k ω = z ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω} *
        ((discreteMatrixKernel q ^ 1) z ({y} : Set E)) =
      ((discreteMatrixKernel q ^ 1) z ({y} : Set E)) *
        (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
          {ω | Function.eval k ω = z ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω} := by
            rw [mul_comm]
    _ = (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
          ({ω | Function.eval k ω = z ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω} ∩
            {ω | Function.eval (k + 1) ω = y}) := by
          symm
          exact measure_inter_prefix_stepEvent_eq_mulLocal
            (E := E) q hq (s := x) (z := z) (y := y) (n := k) (m := 1)
            (measurableSet_beforeReturnStateInFiltration (E := E) x z k)
            (by
              intro ω hω
              exact hω.1)
    _ = (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
          {ω | Function.eval k ω = z ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω ∧
            Function.eval (k + 1) ω = y} := by
          rw [beforeReturnState_stepSlice_eq (E := E) x z y k]

/-- Helper for Theorem 17.49: the canonical step slice at time `k` vanishes on the reference
state `x`, because the chain cannot return to `x` before the first positive return time. -/
private theorem beforeReturnSelfStepSliceMass_eq_zero [Countable E]
    (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q)
    (x y : E) {k : ℕ} (hk : 0 < k) :
    (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
      {ω | Function.eval k ω = x ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω ∧
        Function.eval (k + 1) ω = y} = 0 := by
  have hBase :
      (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
        {ω | Function.eval k ω = x ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω} = 0 :=
    beforeReturnStateMass_self_eq_zero (E := E) q hq x hk
  have hSub :
      {ω | Function.eval k ω = x ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω ∧
        Function.eval (k + 1) ω = y} ⊆
        {ω | Function.eval k ω = x ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω} := by
    intro ω hω
    exact ⟨hω.1, hω.2.1⟩
  exact le_antisymm
    (le_trans (measure_mono hSub) (by simpa using hBase))
    bot_le

/-- Helper for Theorem 17.49: after the before-return slices are in canonical step form, the
outer `tsum` over states commutes with the finite sum over `k ∈ Finset.Icc 1 n`. -/
private theorem tsum_beforeReturnStepSlice_comm [Countable E]
    (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q)
    {x y : E} (n : ℕ) :
    (∑' z : E,
      Finset.sum (Finset.Icc 1 n)
        (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
          {ω | Function.eval k ω = z ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω ∧
            Function.eval (k + 1) ω = y})) =
      Finset.sum (Finset.Icc 1 n)
        (fun k ↦ ∑' z : E,
          (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
            {ω | Function.eval k ω = z ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω ∧
              Function.eval (k + 1) ω = y}) := by
  let stepSlice : E → ℕ → ℝ≥0∞ := fun z k ↦
    (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
      {ω | Function.eval k ω = z ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω ∧
        Function.eval (k + 1) ω = y}
  -- Proof comment: rewrite the finite sum as a `tsum` over the finite subtype, swap the two
  -- `tsum`s once, and then return to the `Finset` presentation.
  calc
    (∑' z : E,
      Finset.sum (Finset.Icc 1 n)
        (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
          {ω | Function.eval k ω = z ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω ∧
            Function.eval (k + 1) ω = y})) =
        ∑' z : E, ∑' k : Finset.Icc 1 n, stepSlice z k := by
          refine tsum_congr fun z ↦ ?_
          rw [← Finset.sum_attach, Finset.attach_eq_univ, tsum_fintype]
    _ = ∑' k : Finset.Icc 1 n, ∑' z : E, stepSlice z k := ENNReal.tsum_comm
    _ = Finset.sum (Finset.Icc 1 n)
          (fun k ↦ ∑' z : E,
            (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
              {ω | Function.eval k ω = z ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω ∧
                Function.eval (k + 1) ω = y}) := by
            rw [← Finset.sum_attach, Finset.attach_eq_univ, tsum_fintype]

/-- Helper for Theorem 17.49: propagating the off-diagonal remainder one more step and summing
over the intermediate state yields the next remainder term. -/
private theorem weightedStartLaw_remainderTail_eq [Countable E] [DecidableEq E]
    (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q) {π : Measure E}
    {x y : E} (hyx : y ≠ x) (n : ℕ) :
    (∑' z : E, ite (z = x) 0
      (weightedStartLaw (E := E) q hq π
        (offDiagFirstReturnRemainder (E := E) x z n) *
          ((discreteMatrixKernel q ^ 1) z ({y} : Set E)))) =
      weightedStartLaw (E := E) q hq π
        (offDiagFirstReturnRemainder (E := E) x y (n + 1)) := by
  classical
  -- Proof comment: first rewrite every summand into the canonical step-slice measure, using the
  -- empty `z = x` slice and the one-step transport lemma off the diagonal.
  calc
    (∑' z : E, ite (z = x) 0
      (weightedStartLaw (E := E) q hq π
        (offDiagFirstReturnRemainder (E := E) x z n) *
          ((discreteMatrixKernel q ^ 1) z ({y} : Set E)))) =
        ∑' z : E,
          weightedStartLaw (E := E) q hq π
            {ω | Function.eval 0 ω ≠ x ∧ Function.eval n ω = z ∧
              (n : ℕ∞) < (τ_[Function.eval, x]^1) ω ∧ Function.eval (n + 1) ω = y} := by
              refine tsum_congr fun z ↦ ?_
              by_cases hzx : z = x
              · subst z
                have hZero :
                    weightedStartLaw (E := E) q hq π
                      {ω | Function.eval 0 ω ≠ x ∧ Function.eval n ω = x ∧
                        (n : ℕ∞) < (τ_[Function.eval, x]^1) ω ∧ Function.eval (n + 1) ω = y} = 0 := by
                  rw [← offDiagFirstReturnRemainder_stepSlice_eq (E := E) x x y n,
                    offDiagFirstReturnRemainder_self_empty (E := E) x n]
                  simp
                simpa [hZero]
              · calc
                  ite (z = x) 0
                      (weightedStartLaw (E := E) q hq π
                        (offDiagFirstReturnRemainder (E := E) x z n) *
                          ((discreteMatrixKernel q ^ 1) z ({y} : Set E))) =
                      weightedStartLaw (E := E) q hq π
                        (offDiagFirstReturnRemainder (E := E) x z n) *
                          ((discreteMatrixKernel q ^ 1) z ({y} : Set E)) := by
                            simp [hzx]
                  _ = ((discreteMatrixKernel q ^ 1) z ({y} : Set E)) *
                      weightedStartLaw (E := E) q hq π
                        (offDiagFirstReturnRemainder (E := E) x z n) := by
                          rw [mul_comm]
                  _ = weightedStartLaw (E := E) q hq π
                      (offDiagFirstReturnRemainder (E := E) x z n ∩
                        {ω | Function.eval (n + 1) ω = y}) := by
                          symm
                          exact weightedStartLaw_inter_prefix_stepEvent_eq_mul
                            (E := E) q hq (π := π)
                            (A := offDiagFirstReturnRemainder (E := E) x z n)
                            (z := z) (y := y) (n := n) (m := 1)
                            (measurableSet_offDiagFirstReturnRemainderInFiltration (E := E) x z n)
                            (by
                              intro ω hω
                              exact hω.2.1)
                  _ = weightedStartLaw (E := E) q hq π
                      {ω | Function.eval 0 ω ≠ x ∧ Function.eval n ω = z ∧
                        (n : ℕ∞) < (τ_[Function.eval, x]^1) ω ∧ Function.eval (n + 1) ω = y} := by
                          rw [offDiagFirstReturnRemainder_stepSlice_eq (E := E) x z y n]
    _ = weightedStartLaw (E := E) q hq π
          {ω | Function.eval 0 ω ≠ x ∧ Function.eval (n + 1) ω = y ∧
            (n : ℕ∞) < (τ_[Function.eval, x]^1) ω} := by
            simpa using weightedStartLaw_remainderStepSliceSum (E := E) q hq (π := π) (x := x) (y := y) n
    _ = weightedStartLaw (E := E) q hq π
          (offDiagFirstReturnRemainder (E := E) x y (n + 1)) := by
            rw [offDiagRemainderStep_eq_succ (E := E) hyx n]

/-- Helper for Theorem 17.49: propagating the finite before-return excursion partial sums one
step forward and summing over the intermediate state yields the shifted excursion tail. -/
private theorem beforeReturnExcursionTail_eq [Countable E] [DecidableEq E]
    (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q) {π : Measure E}
    {x y : E} (n : ℕ) :
    (∑' z : E, ite (z = x) 0
      ((π ({x} : Set E) *
        Finset.sum (Finset.Icc 1 n)
          (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
            {ω | Function.eval k ω = z ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω})) *
          ((discreteMatrixKernel q ^ 1) z ({y} : Set E)))) =
      π ({x} : Set E) *
        Finset.sum (Finset.Icc 1 n)
          (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
            {ω | Function.eval (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω}) := by
  classical
  -- Proof comment: rewrite each `z`-summand into a finite sum of canonical step slices, kill the
  -- `z = x` branch via the self-return zero lemma, and only then commute the finite sum with
  -- the outer `tsum`.
  calc
    (∑' z : E, ite (z = x) 0
      ((π ({x} : Set E) *
        Finset.sum (Finset.Icc 1 n)
          (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
            {ω | Function.eval k ω = z ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω})) *
          ((discreteMatrixKernel q ^ 1) z ({y} : Set E)))) =
        ∑' z : E, π ({x} : Set E) *
          Finset.sum (Finset.Icc 1 n)
            (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
              {ω | Function.eval k ω = z ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω ∧
                Function.eval (k + 1) ω = y}) := by
              refine tsum_congr fun z ↦ ?_
              by_cases hzx : z = x
              · subst z
                have hSumZero :
                    Finset.sum (Finset.Icc 1 n)
                      (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
                        {ω | Function.eval k ω = x ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω ∧
                          Function.eval (k + 1) ω = y}) = 0 := by
                  refine Finset.sum_eq_zero ?_
                  intro k hk
                  exact beforeReturnSelfStepSliceMass_eq_zero
                    (E := E) q hq x y ((Finset.mem_Icc.mp hk).1)
                simpa [hSumZero]
              · calc
                  ite (z = x) 0
                      ((π ({x} : Set E) *
                        Finset.sum (Finset.Icc 1 n)
                          (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
                            {ω | Function.eval k ω = z ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω})) *
                        ((discreteMatrixKernel q ^ 1) z ({y} : Set E))) =
                      (π ({x} : Set E) *
                        Finset.sum (Finset.Icc 1 n)
                          (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
                            {ω | Function.eval k ω = z ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω})) *
                        ((discreteMatrixKernel q ^ 1) z ({y} : Set E)) := by
                          simp [hzx]
                  _ = π ({x} : Set E) *
                      (Finset.sum (Finset.Icc 1 n)
                        (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
                          {ω | Function.eval k ω = z ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω}) *
                            ((discreteMatrixKernel q ^ 1) z ({y} : Set E))) := by
                              rw [mul_assoc, Finset.sum_mul]
                  _ = π ({x} : Set E) *
                      Finset.sum (Finset.Icc 1 n)
                        (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
                          {ω | Function.eval k ω = z ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω ∧
                            Function.eval (k + 1) ω = y}) := by
                              refine congrArg (fun t : ℝ≥0∞ ↦ π ({x} : Set E) * t) ?_
                              rw [Finset.sum_mul]
                              refine Finset.sum_congr rfl ?_
                              intro k hk
                              exact beforeReturnStepSliceMass_eq
                                (E := E) q hq x z y k
    _ = π ({x} : Set E) *
          (∑' z : E,
            Finset.sum (Finset.Icc 1 n)
              (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
                {ω | Function.eval k ω = z ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω ∧
                  Function.eval (k + 1) ω = y})) := by
            rw [ENNReal.tsum_mul_left]
    _ = π ({x} : Set E) *
          Finset.sum (Finset.Icc 1 n)
            (fun k ↦ ∑' z : E,
              (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
                {ω | Function.eval k ω = z ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω ∧
                  Function.eval (k + 1) ω = y}) := by
            rw [tsum_beforeReturnStepSlice_comm (E := E) q hq (x := x) (y := y) n]
    _ = π ({x} : Set E) *
          Finset.sum (Finset.Icc 1 n)
            (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
              {ω | Function.eval (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω}) := by
            refine congrArg (fun t : ℝ≥0∞ ↦ π ({x} : Set E) * t) ?_
            refine Finset.sum_congr rfl ?_
            intro k hk
            simpa using beforeReturnStepSliceSum_eq (E := E) q hq (x := x) (y := y) k

/-- Helper for Theorem 17.49: the source induction identifies the singleton mass `π ({y})` with
the weighted-start remainder plus the finite before-return excursion sum. -/
private theorem weightedStartLaw_offDiag_firstReturnDecomposition [Countable E]
    (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q) {π : Measure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel q) π)
    {x y : E} (hyx : y ≠ x) (n : ℕ) :
    π ({y} : Set E) =
      weightedStartLaw (E := E) q hq π (offDiagFirstReturnRemainder (E := E) x y n) +
        π ({x} : Set E) *
          Finset.sum (Finset.Icc 1 n)
            (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
              {ω | Function.eval k ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω}) := by
  -- Route correction: the earlier direct singleton comparison skipped the missing first-return
  -- decomposition. The corrected route uses one-step invariance, splits off the `z = x` term,
  -- and propagates the remainder and excursion pieces separately.
  classical
  induction n generalizing y with
  | zero =>
      have hTauPos : ∀ ω : ℕ → E, (0 : ℕ∞) < (τ_[Function.eval, x]^1) ω := by
        intro ω
        have hτge1 : (1 : ℕ∞) ≤ (τ_[Function.eval, x]^1) ω := by
          have h : (1 : ℕ) ≤ MeasureTheory.hittingAfter Function.eval ({x} : Set E) 1 ω :=
            le_hittingAfter ω
          simpa [iteratedEntranceTime_one] using h
        exact lt_of_lt_of_le (by simp) hτge1
      have hRem0 :
          offDiagFirstReturnRemainder (E := E) x y 0 = {ω | Function.eval 0 ω = y} := by
        ext ω
        constructor
        · intro hω
          exact hω.2.1
        · intro hω
          refine ⟨?_, hω, hTauPos ω⟩
          intro hxω
          exact hyx (hω.symm.trans hxω)
      -- Proof comment: at time `0`, the remainder event is just the singleton state event, and
      -- the excursion sum is empty.
      calc
        π ({y} : Set E) = weightedStartLaw (E := E) q hq π {ω | Function.eval 0 ω = y} := by
          symm
          exact weightedStartLaw_apply_stateEvent (E := E) q hq hπ 0 y
        _ = weightedStartLaw (E := E) q hq π (offDiagFirstReturnRemainder (E := E) x y 0) := by
              rw [hRem0]
        _ = weightedStartLaw (E := E) q hq π (offDiagFirstReturnRemainder (E := E) x y 0) +
            π ({x} : Set E) *
              Finset.sum (Finset.Icc 1 0)
                (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
                  {ω | Function.eval k ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω}) := by
                  simp
  | succ n ih =>
      have hInv1 :
          π ({y} : Set E) =
            π ({x} : Set E) * ((discreteMatrixKernel q ^ 1) x ({y} : Set E)) +
              ∑' z : E, ite (z = x) 0 (π ({z} : Set E) * ((discreteMatrixKernel q ^ 1) z ({y} : Set E))) := by
        rw [invariantMeasureApplySingletonEqTsumPow (E := E) q hq hπ 1 y,
          ENNReal.tsum_eq_add_tsum_ite x]
      have hStart :
          π ({x} : Set E) * ((discreteMatrixKernel q ^ 1) x ({y} : Set E)) =
            π ({x} : Set E) *
              (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
                {ω | Function.eval 1 ω = y ∧ (((1 : ℕ) : ℕ∞) < (τ_[Function.eval, x]^1) ω)} := by
        -- Proof comment: the `z = x` branch is the first excursion term of the decomposition.
        calc
          π ({x} : Set E) * ((discreteMatrixKernel q ^ 1) x ({y} : Set E)) =
              weightedStartLaw (E := E) q hq π
                {ω | Function.eval 0 ω = x ∧ Function.eval 1 ω = y ∧
                  (((1 : ℕ) : ℕ∞) < (τ_[Function.eval, x]^1) ω)} := by
                  exact weightedStartLaw_startStep_offDiag (E := E) q hq (π := π) hyx
          _ = π ({x} : Set E) *
                (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
                  {ω | Function.eval 1 ω = y ∧ (((1 : ℕ) : ℕ∞) < (τ_[Function.eval, x]^1) ω)} := by
                    simpa using
                      weightedStartLaw_apply_startState_beforeReturn (E := E) q hq (π := π) x y 1
      have hTail :
          (∑' z : E, ite (z = x) 0 (π ({z} : Set E) *
              ((discreteMatrixKernel q ^ 1) z ({y} : Set E)))) =
            weightedStartLaw (E := E) q hq π
              (offDiagFirstReturnRemainder (E := E) x y (n + 1)) +
              π ({x} : Set E) *
                Finset.sum (Finset.Icc 1 n)
                  (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
                    {ω | Function.eval (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω}) := by
        have hExpand :
            (∑' z : E, ite (z = x) 0 (π ({z} : Set E) * ((discreteMatrixKernel q ^ 1) z ({y} : Set E)))) =
              (∑' z : E, ite (z = x) 0
                (weightedStartLaw (E := E) q hq π
                  (offDiagFirstReturnRemainder (E := E) x z n) *
                    ((discreteMatrixKernel q ^ 1) z ({y} : Set E)))) +
              (∑' z : E, ite (z = x) 0
                ((π ({x} : Set E) *
                  Finset.sum (Finset.Icc 1 n)
                    (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
                      {ω | Function.eval k ω = z ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω})) *
                    ((discreteMatrixKernel q ^ 1) z ({y} : Set E)))) := by
          rw [← ENNReal.tsum_add]
          refine tsum_congr fun z ↦ ?_
          by_cases hzx : z = x
          · subst z
            simp
          · rw [if_neg hzx, ih hzx, add_mul]
            simp [hzx]
        -- Proof comment: after applying the induction hypothesis to each off-diagonal state,
        -- the remainder slices recombine into the new remainder term and the excursion slices
        -- recombine into the shifted finite before-return sum.
        rw [hExpand,
          weightedStartLaw_remainderTail_eq (E := E) q hq (π := π) (x := x) (y := y) hyx n,
          beforeReturnExcursionTail_eq (E := E) q hq (π := π) (x := x) (y := y) n]
      -- Proof comment: combine the `z = x` contribution with the shifted excursion tail to
      -- recover the `Finset.Icc 1 (n + 1)` partial sum.
      calc
        π ({y} : Set E) =
            π ({x} : Set E) * ((discreteMatrixKernel q ^ 1) x ({y} : Set E)) +
              ∑' z : E, ite (z = x) 0 (π ({z} : Set E) * ((discreteMatrixKernel q ^ 1) z ({y} : Set E))) := hInv1
        _ =
            π ({x} : Set E) *
                (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
                  {ω | Function.eval 1 ω = y ∧ (((1 : ℕ) : ℕ∞) < (τ_[Function.eval, x]^1) ω)} +
              (weightedStartLaw (E := E) q hq π
                (offDiagFirstReturnRemainder (E := E) x y (n + 1)) +
                π ({x} : Set E) *
                  Finset.sum (Finset.Icc 1 n)
                    (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
                      {ω | Function.eval (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω})) := by
                rw [hStart, hTail]
        _ =
            weightedStartLaw (E := E) q hq π
              (offDiagFirstReturnRemainder (E := E) x y (n + 1)) +
                (π ({x} : Set E) *
                  (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
                    {ω | Function.eval 1 ω = y ∧ (((1 : ℕ) : ℕ∞) < (τ_[Function.eval, x]^1) ω)} +
                  π ({x} : Set E) *
                    Finset.sum (Finset.Icc 1 n)
                      (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
                        {ω | Function.eval (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω})) := by
                          simpa [add_assoc, add_left_comm, add_comm]
        _ =
            weightedStartLaw (E := E) q hq π
              (offDiagFirstReturnRemainder (E := E) x y (n + 1)) +
                π ({x} : Set E) *
                  ((canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
                    {ω | Function.eval 1 ω = y ∧ (((1 : ℕ) : ℕ∞) < (τ_[Function.eval, x]^1) ω)} +
                    Finset.sum (Finset.Icc 1 n)
                      (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
                        {ω | Function.eval (k + 1) ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω})) := by
                          rw [← mul_add]
        _ =
            weightedStartLaw (E := E) q hq π
              (offDiagFirstReturnRemainder (E := E) x y (n + 1)) +
                π ({x} : Set E) *
                  Finset.sum (Finset.Icc 1 (n + 1))
                    (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
                      {ω | Function.eval k ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω}) := by
                        rw [sumBeforeReturnShift_eq_IccSucc (E := E) q hq (x := x) (y := y) hyx n]

/-- Helper for Theorem 17.49: the time-zero before-return term vanishes away from the reference
state `x`. -/
private theorem beforeReturnStateMassAtZero_eq_zero [Countable E]
    (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q)
    {x y : E} (hyx : y ≠ x) :
    (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
      {ω | Function.eval 0 ω = y ∧ ((0 : ℕ) : ℕ∞) < (τ_[Function.eval, x]^1) ω} = 0 := by
  let P : E → ProbabilityMeasure (ℕ → E) := canonicalTrajProcess (E := E) q hq
  letI :
      IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P Function.eval := by
    simpa [P] using canonicalTrajProcess_isMarkovProcessRealization (E := E) q hq
  let hReal :
      IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P Function.eval :=
    inferInstance
  have hxy : x ≠ y := by
    simpa [eq_comm] using hyx
  have hStateZero :
      (P x : Measure (ℕ → E)) {ω | Function.eval 0 ω = y} = 0 := by
    have hpreimage :
        {ω | Function.eval 0 ω = y} =
          (Function.eval 0 : (ℕ → E) → E) ⁻¹' ({y} : Set E) := by
      ext ω
      simp
    rw [hpreimage, ← Measure.map_apply (hReal.measurable_process 0) (MeasurableSet.singleton y)]
    rw [hReal.initial_eq x]
    simp [hxy]
  have hSubset :
      {ω | Function.eval 0 ω = y ∧ ((0 : ℕ) : ℕ∞) < (τ_[Function.eval, x]^1) ω} ⊆
        {ω | Function.eval 0 ω = y} := by
    intro ω hω
    exact hω.1
  exact le_antisymm
    (by
      calc
        (P x : Measure (ℕ → E))
            {ω | Function.eval 0 ω = y ∧ ((0 : ℕ) : ℕ∞) < (τ_[Function.eval, x]^1) ω} ≤
          (P x : Measure (ℕ → E)) {ω | Function.eval 0 ω = y} := measure_mono hSubset
        _ = 0 := hStateZero)
    bot_le

/-- Helper for Theorem 17.49: after zeroing the time-zero term, the finite range partial sums
match the `Finset.Icc 1 n` partial sums used in the last-visit decomposition. -/
private theorem sum_range_beforeReturn_eq_sum_Icc [Countable E]
    (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q)
    {x y : E} (hyx : y ≠ x) (n : ℕ) :
    Finset.sum (Finset.range (n + 1))
      (fun i ↦ if i = 0 then 0 else
        (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
          {ω | Function.eval i ω = y ∧ (i : ℕ∞) < (τ_[Function.eval, x]^1) ω}) =
      Finset.sum (Finset.Icc 1 n)
        (fun i ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
          {ω | Function.eval i ω = y ∧ (i : ℕ∞) < (τ_[Function.eval, x]^1) ω}) := by
  let a : ℕ → ℝ≥0∞ := fun i ↦
    (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
      {ω | Function.eval i ω = y ∧ (i : ℕ∞) < (τ_[Function.eval, x]^1) ω}
  rw [Nat.range_succ_eq_Icc_zero]
  have hIcc : Finset.Icc 0 n = insert 0 (Finset.Icc 1 n) := by
    symm
    exact Finset.insert_Icc_succ_left_eq_Icc (Nat.zero_le n)
  have hnotin : 0 ∉ Finset.Icc 1 n := by
    simp
  rw [hIcc, Finset.sum_insert hnotin]
  simp only [a, if_pos rfl, zero_add]
  suffices ∀ i ∈ Finset.Icc 1 n, (if i = 0 then 0 else a i) = a i by
    simpa using Finset.sum_congr rfl this
  intro i hi
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hi0 : i ≠ 0 := Nat.ne_of_gt (Nat.succ_le_iff.mp hi1)
  simp [a, hi0]

/-- Helper for Theorem 17.49: every invariant measure dominates its mass at the recurrent
reference state `x` times the return-cycle occupation measure rooted at `x`. -/
private theorem invariantMeasureSingletonGeReferenceMassMulReturnCycle [Countable E]
    (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q)
    {x : E} {π : Measure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel q) π)
    (hx : IsRecurrentState (canonicalTrajProcess (E := E) q hq) Function.eval x)
    (hπ_finite : ∀ z : E, π ({z} : Set E) < ∞)
    (hπx_pos : 0 < π ({x} : Set E)) :
    ∀ y : E, π ({y} : Set E) ≥
      π ({x} : Set E) * (μ[canonicalTrajProcess (E := E) q hq, Function.eval] x) ({y} : Set E) := by
  intro y
  by_cases hyx : y = x
  · subst y
    -- Proof comment: on the diagonal, the return-cycle occupation measure has singleton mass `1`.
    rw [canonicalReturnCycle_apply_singleton_self (E := E) q hq x, mul_one]
  · have hSeries :
        (μ[canonicalTrajProcess (E := E) q hq, Function.eval] x) ({y} : Set E) =
          ∑' i : ℕ,
            if i = 0 then 0 else
              (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
                {ω | Function.eval i ω = y ∧ (i : ℕ∞) < (τ_[Function.eval, x]^1) ω} := by
      rw [returnCycleOccupationMeasure_apply_singleton (P := canonicalTrajProcess (E := E) q hq)
        (X := Function.eval), returnCycleOccupationMass]
      refine tsum_congr fun i ↦ ?_
      by_cases hi : i = 0
      · subst hi
        simpa using beforeReturnStateMassAtZero_eq_zero (E := E) q hq (x := x) (y := y) hyx
      · simp [hi]
    have hPartial :
        ∀ n : ℕ,
          π ({x} : Set E) *
            Finset.sum (Finset.Icc 1 n)
              (fun k ↦ (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
                {ω | Function.eval k ω = y ∧ (k : ℕ∞) < (τ_[Function.eval, x]^1) ω}) ≤
                  π ({y} : Set E) := by
      intro n
      -- Proof comment: the first-return decomposition expresses `π ({y})` as the partial sum
      -- plus a nonnegative weighted-start remainder term.
      rw [weightedStartLaw_offDiag_firstReturnDecomposition (E := E) q hq (π := π) hπ hyx n]
      exact le_add_of_nonneg_left (zero_le _)
    -- Proof comment: compare each finite excursion partial sum against `π ({y})`, then pass to
    -- the supremum representation of the return-cycle series.
    calc
      π ({x} : Set E) * (μ[canonicalTrajProcess (E := E) q hq, Function.eval] x) ({y} : Set E) =
          π ({x} : Set E) *
            ∑' i : ℕ,
              if i = 0 then 0 else
                (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
                  {ω | Function.eval i ω = y ∧ (i : ℕ∞) < (τ_[Function.eval, x]^1) ω} := by
                    rw [hSeries]
      _ = π ({x} : Set E) *
            ⨆ n : ℕ, Finset.sum (Finset.range n)
              (fun i ↦ if i = 0 then 0 else
                (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
                  {ω | Function.eval i ω = y ∧ (i : ℕ∞) < (τ_[Function.eval, x]^1) ω}) := by
              rw [ENNReal.tsum_eq_iSup_nat]
      _ = ⨆ n : ℕ, π ({x} : Set E) *
            Finset.sum (Finset.range n)
              (fun i ↦ if i = 0 then 0 else
                (canonicalTrajProcess (E := E) q hq x : Measure (ℕ → E))
                  {ω | Function.eval i ω = y ∧ (i : ℕ∞) < (τ_[Function.eval, x]^1) ω}) := by
              rw [ENNReal.mul_iSup]
      _ ≤ π ({y} : Set E) := by
            refine iSup_le fun n ↦ ?_
            cases n with
            | zero =>
                simp
            | succ m =>
                rw [sum_range_beforeReturn_eq_sum_Icc (E := E) q hq (x := x) (y := y) hyx m]
                exact hPartial m

/-- Helper for Theorem 17.49: a nonzero invariant measure with finite singleton masses agrees
singletonwise with its mass at `x` times the return-cycle occupation measure rooted at the
recurrent state `x`. -/
private theorem invariantMeasureSingletonEqReferenceMassMulReturnCycle [Countable E]
    (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q)
    [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q)]
    {x : E} {π : Measure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel q) π)
    (hx : IsRecurrentState (canonicalTrajProcess (E := E) q hq) Function.eval x)
    (hπ_finite : ∀ z : E, π ({z} : Set E) < ∞)
    (hπx_pos : 0 < π ({x} : Set E)) :
    ∀ y : E, π ({y} : Set E) =
      π ({x} : Set E) * (μ[canonicalTrajProcess (E := E) q hq, Function.eval] x) ({y} : Set E) := by
  intro y
  have hLower :
      π ({y} : Set E) ≥
        π ({x} : Set E) * (μ[canonicalTrajProcess (E := E) q hq, Function.eval] x) ({y} : Set E) :=
    invariantMeasureSingletonGeReferenceMassMulReturnCycle
      (E := E) q hq hπ hx hπ_finite hπx_pos y
  have hnot_gt :
      ¬ π ({y} : Set E) >
        π ({x} : Set E) * (μ[canonicalTrajProcess (E := E) q hq, Function.eval] x) ({y} : Set E) := by
    intro hgap
    by_cases hyx : y = x
    · have hgap' := hgap
      rw [hyx, canonicalReturnCycle_apply_singleton_self (E := E) q hq x, mul_one] at hgap'
      exact lt_irrefl _ hgap'
    have hy_pos : (Measure.count : Measure E) ({x} : Set E) > 0 := by
      simp
    rcases (inferInstance : Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q)).irreducible
        (A := ({x} : Set E)) (MeasurableSet.singleton x) hy_pos y with ⟨n, hn⟩
    have hn_pos : 0 < n := by
      by_contra hn_pos
      have hn_zero : n = 0 := Nat.eq_zero_of_not_pos hn_pos
      subst hn_zero
      have hzero : ((discreteMatrixKernel q ^ 0) y) ({x} : Set E) = 0 := by
        change (Kernel.id y) ({x} : Set E) = 0
        simp [Kernel.id_apply, hyx]
      rw [hzero] at hn
      exact lt_irrefl _ hn
    exact strictGapAgainstReturnCyclePropagatesToReference
      (E := E) q hq hπ hx hπ_finite hπx_pos
      (fun z ↦ invariantMeasureSingletonGeReferenceMassMulReturnCycle
        (E := E) q hq hπ hx hπ_finite hπx_pos z)
      hgap ⟨n, hn_pos, hn⟩
  exact le_antisymm (le_of_not_gt hnot_gt) hLower

/-- Helper for Theorem 17.49: on the canonical realization of an irreducible recurrent countable
kernel, any two nonzero invariant measures are proportional. -/
private theorem invariantMeasures_unique_up_to_scale_of_canonicalTrajProcess
    [Countable E] (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q)
    [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q)]
    (hrec : IsRecurrentMarkovChain (canonicalTrajProcess (E := E) q hq) Function.eval)
    {μ ν : Measure E}
    (hμ : Kernel.Invariant (discreteMatrixKernel q) μ)
    (hν : Kernel.Invariant (discreteMatrixKernel q) ν)
    (hμ_finite : ∀ x : E, μ ({x} : Set E) < ∞)
    (hν_finite : ∀ x : E, ν ({x} : Set E) < ∞)
    (hμ_ne : μ ≠ 0) (hν_ne : ν ≠ 0) :
    ∃ c : NNReal, 0 < c ∧ ν = (c : ℝ≥0∞) • μ :=
  by
  letI : IsMarkovKernel (discreteMatrixKernel q) := discreteMatrixKernel_isMarkovKernel q hq
  letI :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel q ^ n)
        (canonicalTrajProcess (E := E) q hq) Function.eval :=
    canonicalTrajProcess_isMarkovProcessRealization (E := E) q hq
  -- Route correction: the chapter-level Exercise 17.6.6 owner import is currently broken, so the
  -- remaining comparison theorem has to be reproved locally from the return-cycle API already set
  -- up above.
  obtain ⟨x, hμx_pos⟩ := existsPositiveSingletonMassOfNeZero (E := E) (π := μ) hμ_ne
  have hx : IsRecurrentState (canonicalTrajProcess (E := E) q hq) Function.eval x := hrec x
  -- Proof comment: first identify both invariant measures through the same return-cycle
  -- occupation measure rooted at the recurrent reference state `x`.
  have hμ_singleton :
      ∀ y : E, μ ({y} : Set E) =
        μ ({x} : Set E) * (μ[canonicalTrajProcess (E := E) q hq, Function.eval] x) ({y} : Set E) :=
    invariantMeasureSingletonEqReferenceMassMulReturnCycle
      (E := E) q hq hμ hx hμ_finite hμx_pos
  obtain ⟨z, hνz_pos⟩ := existsPositiveSingletonMassOfNeZero (E := E) (π := ν) hν_ne
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel q ^ n)
        (canonicalTrajProcess (E := E) q hq) Function.eval := inferInstance
  have hzx_step :
      z ≠ x → ∃ n : ℕ, 0 < n ∧ 0 < (discreteMatrixKernel q ^ n) z ({x} : Set E) := by
    intro hzx
    have hx_pos : 0 < (Measure.count : Measure E) ({x} : Set E) := by
      simp
    rcases (inferInstance : Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q)).irreducible
        (A := ({x} : Set E)) (MeasurableSet.singleton x) hx_pos z with ⟨n, hn⟩
    have hn_pos : 0 < n := by
      by_contra hn_pos
      have hn_zero : n = 0 := Nat.eq_zero_of_not_pos hn_pos
      subst hn_zero
      have hzero : ((discreteMatrixKernel q ^ 0) z) ({x} : Set E) = 0 := by
        change (Kernel.id z) ({x} : Set E) = 0
        simp [Kernel.id_apply, hzx]
      rw [hzero] at hn
      exact lt_irrefl _ hn
    exact ⟨n, hn_pos, hn⟩
  have hνx_pos : 0 < ν ({x} : Set E) := by
    -- Proof comment: irreducibility reaches the chosen reference state `x`, and invariance
    -- transports the positive singleton mass of `ν` along that positive-time step.
    by_cases hzx : z = x
    · simpa [hzx] using hνz_pos
    · exact singletonMass_pos_of_invariant_of_posStepMass
        hReal.semigroup (by simpa using hν) hνz_pos (hzx_step hzx)
  have hν_singleton :
      ∀ y : E, ν ({y} : Set E) =
        ν ({x} : Set E) * (μ[canonicalTrajProcess (E := E) q hq, Function.eval] x) ({y} : Set E) :=
    invariantMeasureSingletonEqReferenceMassMulReturnCycle
      (E := E) q hq hν hx hν_finite hνx_pos
  have hratio_finite : ν ({x} : Set E) / μ ({x} : Set E) < ∞ :=
    ENNReal.div_lt_top (hν_finite x).ne hμx_pos.ne'
  have hratio_pos : 0 < ν ({x} : Set E) / μ ({x} : Set E) := by
    exact (ENNReal.div_pos_iff).2 ⟨hνx_pos.ne', (hμ_finite x).ne⟩
  let c : NNReal := (ν ({x} : Set E) / μ ({x} : Set E)).toNNReal
  have hc_pos : 0 < c := by
    exact ENNReal.toNNReal_pos hratio_pos.ne' (ne_of_lt hratio_finite)
  have hc_coe : (c : ℝ≥0∞) = ν ({x} : Set E) / μ ({x} : Set E) := by
    simpa [c] using (ENNReal.coe_toNNReal (ne_of_lt hratio_finite))
  refine ⟨c, hc_pos, ?_⟩
  refine Measure.ext_of_singleton fun y ↦ ?_
  rw [Measure.smul_apply]
  calc
    ν ({y} : Set E) =
        ν ({x} : Set E) * (μ[canonicalTrajProcess (E := E) q hq, Function.eval] x) ({y} : Set E) :=
      hν_singleton y
    _ = ((ν ({x} : Set E) / μ ({x} : Set E)) * μ ({x} : Set E)) *
          (μ[canonicalTrajProcess (E := E) q hq, Function.eval] x) ({y} : Set E) := by
            rw [ENNReal.div_mul_cancel hμx_pos.ne' (hμ_finite x).ne]
    _ = (ν ({x} : Set E) / μ ({x} : Set E)) *
          (μ ({x} : Set E) * (μ[canonicalTrajProcess (E := E) q hq, Function.eval] x) ({y} : Set E)) := by
          rw [mul_assoc, mul_left_comm]
    _ = (ν ({x} : Set E) / μ ({x} : Set E)) * μ ({y} : Set E) := by
          rw [← hμ_singleton y]
    _ = (c : ℝ≥0∞) * μ ({y} : Set E) := by
          rw [hc_coe]

-- Proof sketch: irreducibility implies that any invariant measures are unique up to a scalar
-- multiple. Since invariant distributions are probability measures of total mass `1`, that scalar
-- must be `1`, so the set of invariant distributions has at most one element.
/-- Theorem 17.49: if a discrete Markov kernel `p` is irreducible with respect to counting measure,
then `p` has at most one invariant distribution. Equivalently, the set of invariant probability
measures of `p` is subsingleton. -/
theorem invariantDistributions_subsingleton_of_irreducible
    : Set.Subsingleton (invariantDistributions p) := by
  letI : Countable E := countableOfIrreducibleCountKernel p
  let q : E → E → ℝ≥0∞ := fun x y ↦ p x ({y} : Set E)
  have hqker : discreteMatrixKernel q = p := discreteMatrixKernel_singletonMass_eq p
  have hqmarkov : IsMarkovKernel (discreteMatrixKernel q) := by
    simpa [hqker] using (inferInstance : IsMarkovKernel p)
  have hqirr : Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q) := by
    simpa [hqker] using
      (inferInstance : Kernel.IsIrreducible (Measure.count : Measure E) p)
  letI : Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q) := hqirr
  have hqstochastic : IsStochasticMatrix q := by
    intro x
    rw [← discreteMatrixKernel_univ q x]
    letI : IsMarkovKernel (discreteMatrixKernel q) := hqmarkov
    simpa using (measure_univ : (discreteMatrixKernel q x) Set.univ = 1)
  intro μ hμ ν hν
  have hμinv :
      Kernel.Invariant (discreteMatrixKernel q) ((μ : ProbabilityMeasure E) : Measure E) := by
    simpa [hqker] using (mem_invariantDistributions_iff p μ).1 hμ
  have hνinv :
      Kernel.Invariant (discreteMatrixKernel q) ((ν : ProbabilityMeasure E) : Measure E) := by
    simpa [hqker] using (mem_invariantDistributions_iff p ν).1 hν
  have hrec :
      IsRecurrentMarkovChain (canonicalTrajProcess (E := E) q hqstochastic) Function.eval :=
    canonicalTrajProcess_isRecurrent_ofInvariantDistribution
      (E := E) q hqstochastic hμinv
  have hμ_ne : ((μ : ProbabilityMeasure E) : Measure E) ≠ 0 :=
    probabilityMeasure_toMeasure_ne_zero μ
  have hν_ne : ((ν : ProbabilityMeasure E) : Measure E) ≠ 0 :=
    probabilityMeasure_toMeasure_ne_zero ν
  have hμ_finite : ∀ x : E, ((μ : ProbabilityMeasure E) : Measure E) ({x} : Set E) < ∞ := by
    intro x
    -- Proof comment: invariant distributions are probability measures, so each singleton mass is
    -- bounded by the total mass `1`.
    exact probabilityMeasureSingletonMass_lt_top μ x
  have hν_finite : ∀ x : E, ((ν : ProbabilityMeasure E) : Measure E) ({x} : Set E) < ∞ := by
    intro x
    -- Proof comment: the same finiteness bound holds for the second invariant distribution.
    exact probabilityMeasureSingletonMass_lt_top ν x
  obtain ⟨c, _hc_pos, hscale⟩ :=
    invariantMeasures_unique_up_to_scale_of_canonicalTrajProcess
      (E := E) q hqstochastic hrec hμinv hνinv hμ_finite hν_finite hμ_ne hν_ne
  -- Proof comment: once the second invariant distribution is a positive scalar multiple of the
  -- first one, normalization on `Set.univ` forces that scalar to be `1`.
  exact (probabilityMeasure_eq_of_measure_eq_smul (μ := μ) (ν := ν) (c := c) hscale).symm

-- Proof sketch: apply `invariantDistributions_subsingleton_of_irreducible` to the invariant
-- distributions `μ` and `ν`; since both belong to `invariantDistributions p`, subsingularity of
-- that set forces `μ = ν`.
/-- Any two invariant distributions of a discrete irreducible Markov kernel are equal. -/
theorem eq_of_isInvariantDistribution_of_irreducible
    {μ ν : ProbabilityMeasure E}
    (hμ : Kernel.Invariant p (μ : Measure E)) (hν : Kernel.Invariant p (ν : Measure E)) :
    μ = ν := by
  have hsub : Set.Subsingleton (invariantDistributions p) :=
    invariantDistributions_subsingleton_of_irreducible p
  have hμ' : μ ∈ invariantDistributions p := (mem_invariantDistributions_iff p μ).2 hμ
  have hν' : ν ∈ invariantDistributions p := (mem_invariantDistributions_iff p ν).2 hν
  exact hsub hμ' hν'

end ProbabilityTheory

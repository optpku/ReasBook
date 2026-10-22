/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Algorithm_1_10_20

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter Set Topology

universe u

variable {α : Type u} [TopologicalSpace α]

variable {Q 𝓕 : Set α}
variable {objective : ↥(Q ∩ interior 𝓕) → ℝ} {F : C(interior 𝓕, ℝ)}
variable [IsBarrierFunctionOn 𝓕 F]

local notation "Q₀" => {x // x ∈ Q ∩ interior 𝓕}
local notation "F₀" =>
  ((F.comp (ContinuousMap.inclusion inter_subset_right)) : Q₀ → ℝ)
local notation "primalProblem" =>
  SetConstrainedMinimizationProblem.unconstrained objective

namespace BarrierFunctionMethod

/-- Helper for Theorem 1.10.23: every auxiliary optimal value is bounded above by the auxiliary
objective at any comparison point in `Q ∩ interior 𝓕`. -/
theorem auxiliaryOptimalValue_le_value_at
    (method : BarrierFunctionMethod Q 𝓕 objective F) (k : ℕ) (x : Q₀) :
    method.auxiliaryOptimalValue k ≤ ((method.auxiliaryObjective k x : ℝ) : EReal) := by
  -- The selected iterate minimizes the `k`-th auxiliary objective over the whole feasible type.
  simpa [BarrierFunctionMethod.auxiliaryOptimalValue, BarrierFunctionMethod.auxiliaryProblem] using
    (method.auxiliaryProblem k).optimalValue_le_of_mem_feasibleSet (by simp)

/-- Helper for Theorem 1.10.23: a global lower bound for the barrier shifts the primal optimal
value below every auxiliary optimal value by the same scaled amount. -/
theorem lower_barrier_shift_le_auxiliaryOptimalValue
    (method : BarrierFunctionMethod Q 𝓕 objective F) {c : ℝ}
    (hc : c ∈ lowerBounds (Set.range F₀)) (k : ℕ) :
    (primalProblem).optimalValue + ((c / method.barrierParameters k : ℝ) : EReal) ≤
      method.auxiliaryOptimalValue k := by
  let Δ : ℝ := -(c / method.barrierParameters k)
  have hcompare :=
    SetConstrainedMinimizationProblem.optimalValue_sub_le_optimalValue_of_forall_sub_le
      primalProblem
      (method.auxiliaryProblem k)
      (Δ := Δ)
      (by
        change Set.univ =
          (method.toSequentialUnconstrainedMinimizationScheme.auxiliaryProblem k.succPNat).feasibleSet
        simp [SequentialUnconstrainedMinimizationScheme.auxiliaryProblem,
          SetConstrainedMinimizationProblem.unconstrained])
      (by
        intro x hx
        -- Compare the barrier term with the global lower bound `c`.
        change objective x - Δ ≤
          method.toSequentialUnconstrainedMinimizationScheme.auxiliaryObjectives k.succPNat x
        simp [BarrierFunctionMethod.toSequentialUnconstrainedMinimizationScheme,
          BarrierFunctionMethod.auxiliaryObjective]
        have hcx : c ≤ F₀ x := hc ⟨x, rfl⟩
        have hinv_nonneg : 0 ≤ 1 / method.barrierParameters k :=
          one_div_nonneg.mpr (method.barrierParameters_pos k).le
        have hdiv : c / method.barrierParameters k ≤
            (1 / method.barrierParameters k) * F₀ x := by
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
            mul_le_mul_of_nonneg_left hcx hinv_nonneg
        simpa [Δ, sub_eq_add_neg, div_eq_mul_inv, add_comm, add_left_comm, add_assoc,
          mul_comm, mul_left_comm, mul_assoc] using add_le_add_left hdiv (objective x))
  -- Re-express the optimal-value comparison in the textbook additive form.
  simpa [BarrierFunctionMethod.auxiliaryOptimalValue, Δ, sub_eq_add_neg, EReal.coe_add,
    EReal.coe_neg, add_assoc, add_left_comm, add_comm] using hcompare

/-- Helper for Theorem 1.10.23: the primal optimal value is finite from above because any iterate
provides a feasible comparison value. -/
theorem primal_optimalValue_ne_top
    (method : BarrierFunctionMethod Q 𝓕 objective F) :
    (primalProblem).optimalValue ≠ ⊤ := by
  -- Any feasible point bounds the optimal value away from `⊤`.
  refine ne_of_lt ?_
  refine lt_of_le_of_lt
    ((primalProblem).optimalValue_le_of_mem_feasibleSet (x := method 0) (by simp))
    (EReal.coe_lt_top _)

/-- Helper for Theorem 1.10.23: if the primal optimal value lies below a real threshold, then
some interior-feasible point already has objective value below that threshold. -/
theorem exists_objective_lt_of_optimalValue_lt
    (method : BarrierFunctionMethod Q 𝓕 objective F) (b : ℝ)
    (hb : (primalProblem).optimalValue < (b : EReal)) :
    ∃ x : Q₀, (objective x : EReal) < (b : EReal) := by
  -- The feasible-value image is nonempty because the method supplies interior-feasible iterates.
  rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image] at hb
  have himage_nonempty :
      ((fun x ↦ (primalProblem x : EReal)) '' (primalProblem).feasibleSet).Nonempty := by
    refine ⟨(objective (method 0) : EReal), ?_⟩
    refine ⟨method 0, by simp, rfl⟩
  rcases exists_lt_of_csInf_lt himage_nonempty hb with ⟨v, hv, hvlt⟩
  rcases hv with ⟨x, hx, rfl⟩
  -- Unpack the image witness to recover the desired feasible point.
  exact ⟨x, by simpa using hvlt⟩

end BarrierFunctionMethod

/- Theorem 1.10.23 lies in the Chapter 1 barrier-method convergence domain.

Sampled owner declarations in this domain:
* `BarrierFunctionMethod` in `Algorithm_1_10_20`, the source-facing owner of the barrier iterates,
  auxiliary objectives, and auxiliary optimal values;
* `SetConstrainedMinimizationProblem.unconstrained` in `Definition_1_3_3`, the canonical owner
  problem attached to an objective on the whole feasible type;
* `SetConstrainedMinimizationProblem.optimalValue` in `Definition_1_3_7`, the canonical optimal
  value attached to that owner;
* `BddBelow (Set.range f)`, the project's canonical lower-boundedness interface when only the
  existence of a lower bound matters;
* `BarrierFunctionMethod.toSequentialUnconstrainedMinimizationScheme`, the bridge to the generic
  sequential-unconstrained owner.

Best owner abstraction:
* source-facing: `BarrierFunctionMethod Q 𝓕 objective F`;
* core/canonical: the owner problems `method.auxiliaryProblem k` and `primalProblem`;
* bridge/view: the lower-boundedness hypothesis on the canonical restriction `F₀ : Q₀ → ℝ`,
  expressed as `BddBelow (Set.range F₀)`.

Primitive data:
* the barrier method `method`;
* the lower-boundedness of the restricted barrier map `F₀ : Q₀ → ℝ`.

Derived API:
* `method.auxiliaryOptimalValue`;
* `primalProblem.optimalValue`;
* the auxiliary-problem optimal-value identities coming from the owner files.

The theorem therefore stays source-facing on `BarrierFunctionMethod`, but uses the owner
lower-boundedness predicate `BddBelow` applied to the canonical restriction `F₀`, and the weakest
ambient topological assumptions already supported by the barrier-method owner, instead of a
Euclidean-only ambient model or a bespoke existential lower-bound package.
-/

/-- Theorem 1.10.23: if the barrier `F` is bounded below on `𝓕₀ = Q ∩ interior 𝓕`, then the
global optimal values `Ψₖ*` of the auxiliary objectives
`x ↦ f₀(x) + (1 / tₖ) F(x)` converge to the optimal value `f*` of `f₀` on `𝓕₀`. -/
-- Proof sketch: for any interior-feasible comparison point `x̄`, the minimizing property gives
-- `Ψₖ* ≤ f₀(x̄) + tₖ⁻¹ F(x̄)`, and `tₖ → ∞` sends the barrier term to `0`, yielding the upper
-- bound by `f*`. A lower bound for `F` on `𝓕₀` gives `Ψₖ* ≥ f* + tₖ⁻¹ F_*`; passing to the
-- limit and squeezing the two bounds proves convergence.
theorem BarrierFunctionMethod.auxiliaryOptimalValue_tendsto_optimalValue
    (method : BarrierFunctionMethod Q 𝓕 objective F)
    (hF : BddBelow (Set.range F₀)) :
    Tendsto method.auxiliaryOptimalValue atTop (nhds (primalProblem).optimalValue) :=
  by
    rcases hF with ⟨c, hc⟩
    -- The source proof is a two-sided squeeze: a global barrier lower bound gives the lower
    -- comparison, and evaluation at a fixed feasible point gives the upper comparison.
    refine tendsto_order.2 ?_
    constructor
    · intro a ha
      by_cases ha_bot : a = ⊥
      · -- Lower neighborhoods of `⊥` are vacuous, so every auxiliary value lies above them.
        subst ha_bot
        filter_upwards [] with k
        rw [method.auxiliaryOptimalValue_eq_iterateValue]
        exact EReal.bot_lt_coe _
      · -- For a finite lower threshold, the scaled lower barrier shift eventually
        -- dominates the gap.
        have hp_ne_bot : (primalProblem).optimalValue ≠ ⊥ := by
          intro hp_bot
          have ha' := ha
          simp [hp_bot] at ha'
        let aReal : ℝ := a.toReal
        let pReal : ℝ := (primalProblem).optimalValue.toReal
        have ha_eq : ((aReal : ℝ) : EReal) = a := by
          exact EReal.coe_toReal (ne_of_lt (ha.trans_le le_top)) ha_bot
        have hp_eq : ((pReal : ℝ) : EReal) = (primalProblem).optimalValue := by
          exact EReal.coe_toReal (method.primal_optimalValue_ne_top) hp_ne_bot
        have haReal_lt : aReal < pReal := by
          have hcoe : ((aReal : ℝ) : EReal) < ((pReal : ℝ) : EReal) := by
            simpa [ha_eq, hp_eq] using ha
          exact (EReal.coe_lt_coe_iff.mp hcoe)
        have hshift_tendsto :
            Tendsto (fun k ↦ c / method.barrierParameters k) atTop (nhds 0) :=
          Filter.Tendsto.const_div_atTop method.barrierParameters_tendsto_atTop c
        have hgap_eventually :
            ∀ᶠ k : ℕ in atTop, aReal - pReal < c / method.barrierParameters k := by
          have hgap : aReal - pReal < 0 := by
            linarith
          exact hshift_tendsto (Ioi_mem_nhds hgap)
        filter_upwards [hgap_eventually] with k hk
        have hk' : aReal < pReal + c / method.barrierParameters k := by
          linarith
        have hlt_shift : a <
            (primalProblem).optimalValue + ((c / method.barrierParameters k : ℝ) : EReal) := by
          have hkE : a < ((pReal + c / method.barrierParameters k : ℝ) : EReal) := by
            rw [← ha_eq]
            exact_mod_cast hk'
          calc
            a < ((pReal + c / method.barrierParameters k : ℝ) : EReal) := hkE
            _ = (primalProblem).optimalValue + ((c / method.barrierParameters k : ℝ) : EReal) := by
              rw [EReal.coe_add, hp_eq]
        exact lt_of_lt_of_le hlt_shift
          (method.lower_barrier_shift_le_auxiliaryOptimalValue hc k)
    · intro a ha
      by_cases htop : a = ⊤
      · -- Every auxiliary optimal value is a realized real value, so it is automatically below `⊤`.
        subst htop
        filter_upwards [] with k
        rw [method.auxiliaryOptimalValue_eq_iterateValue]
        exact EReal.coe_lt_top _
      · -- Choose a feasible comparison point with objective below the target threshold.
        have ha_ne_bot : a ≠ ⊥ := by
          exact (bot_lt_iff_ne_bot.mp (lt_of_le_of_lt bot_le ha))
        let aReal : ℝ := a.toReal
        have ha_eq : ((aReal : ℝ) : EReal) = a := by
          exact EReal.coe_toReal htop ha_ne_bot
        obtain ⟨x, hxlt⟩ := method.exists_objective_lt_of_optimalValue_lt aReal (by
          simpa [ha_eq] using ha)
        have hbarrier_tendsto :
            Tendsto (fun k ↦ F (inclusion inter_subset_right x) / method.barrierParameters k) atTop
              (nhds 0) :=
          Filter.Tendsto.const_div_atTop method.barrierParameters_tendsto_atTop
            (F (inclusion inter_subset_right x))
        have hcomparison_tendsto :
            Tendsto
              (fun k ↦ objective x + F (inclusion inter_subset_right x) / method.barrierParameters k)
              atTop
              (nhds (objective x)) := by
          simpa using (tendsto_const_nhds.add hbarrier_tendsto)
        have hvalue_eventually :
            ∀ᶠ k : ℕ in atTop, method.auxiliaryObjective k x < aReal := by
          have hraw :
              ∀ᶠ k : ℕ in atTop,
                objective x + F (inclusion inter_subset_right x) / method.barrierParameters k <
                  aReal := by
            exact hcomparison_tendsto (Iio_mem_nhds (by simpa using hxlt))
          filter_upwards [hraw] with k hk
          simpa [BarrierFunctionMethod.auxiliaryObjective, div_eq_mul_inv, mul_comm] using hk
        filter_upwards [hvalue_eventually] with k hk
        have haux_lt : ((method.auxiliaryObjective k x : ℝ) : EReal) < a := by
          rw [← ha_eq]
          exact_mod_cast hk
        exact lt_of_le_of_lt (method.auxiliaryOptimalValue_le_value_at k x) haux_lt

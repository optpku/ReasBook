/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_23
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_25
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.MarkovProcessRealization
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_9

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {n m : ℕ}

local notation "State" => Fin n → ℝ
local notation "PathSpace" => EuclideanPathSpace n
local notation "DiffusionCoeff" => NNReal → State → Fin n → Fin m → ℝ
local notation "DriftCoeff" => NNReal → State → Fin n → ℝ

section

variable
    {E' : Type u} [MeasurableSpace E'] {Ω' : Type v} [MeasurableSpace Ω']
    (σ : DiffusionCoeff) (b : DriftCoeff)
    (Q : E' → ProbabilityMeasure Ω') (Y : E' → NNReal → Ω' → E')
    (H : State → E' → ℂ)

local notation "σσᵀ" => diffusionMatrixOfCoefficient σ

/- Source/core/bridge triage for Theorem 26.28:
- source-facing bridge: the duality criterion below;
- core/canonical owners already upstream: `IsLocalMartingaleProblemSolution`,
  `HasDeterministicTimeMarginalUniqueness`, and `LocalMartingaleProblemWellPosed`;
- bridge/view layer reused here: `pathProcess` and `SatisfiesDualityAt`.
The helper lemmas below only use measurability of the slices `H(·, y)`, but the main
source-facing theorem still carries the source-level joint measurability assumption on `H`
and the source-level Markov owner for the dual family. -/

variable
    (hsep :
      IsSeparatingFamilyFor
        {μ : Measure State | IsProbabilityMeasure μ}
        (Set.range (Function.swap H)))
    (hduality :
      ∀ (x : State)
        {Ω : Type _} [MeasurableSpace Ω]
        (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
        (P : ProbabilityMeasure Ω) (X : Ω → PathSpace),
        IsLocalMartingaleProblemSolution
          (Measure.dirac x) σσᵀ b ℱ (P : Measure Ω) X →
        SatisfiesDualityAt (P : Measure Ω) (pathProcess X) x Q Y H)

/-- Helper for Theorem 26.28: an a.e.-measurable path-valued random variable has a.e.-measurable
deterministic-time evaluations. -/
private theorem aemeasurable_stateEval_of_aemeasurable_path
    {Ω : Type _} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → PathSpace}
    (hX : AEMeasurable X μ) (T : NNReal) :
    AEMeasurable (fun ω ↦ X ω T) μ := by
  -- Proof comment: deterministic-time evaluation on path space is measurable, so composition
  -- with an a.e.-measurable path map stays a.e.-measurable.
  exact (continuous_eval_const T).measurable.aemeasurable.comp_aemeasurable hX

/-- Helper for Theorem 26.28: deterministic-time evaluation on canonical path space is
measurable. -/
private theorem measurable_path_eval (T : NNReal) :
    Measurable (fun γ : PathSpace ↦ γ T) := by
  -- Proof comment: evaluation at a fixed time is continuous on `EuclideanPathSpace`.
  simpa using (continuous_eval_const T).measurable

/-- Helper for Theorem 26.28: every observable slice `H(·, y)` is measurable because the
separating family consists of measurable test functions. -/
private theorem measurable_stateObservable_of_separatingFamily
    (hsep :
      IsSeparatingFamilyFor
        {μ : Measure State | IsProbabilityMeasure μ}
        (Set.range (Function.swap H)))
    (y : E') :
    Measurable (fun z : State ↦ H z y) := by
  -- Proof comment: the slice `H(·, y)` lies in the separating family by construction.
  apply IsSeparatingFamilyFor.measurable hsep
  exact ⟨y, rfl⟩

/-- Helper for Theorem 26.28: duality identifies the integral of `H(·, y)` against a
deterministic-time marginal with the common dual expectation. -/
private theorem dualityTimeMarginalIntegral_eq_dualExpectation
    (x : State)
    {Ω : Type _} [MeasurableSpace Ω]
    (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (P : ProbabilityMeasure Ω) (X : Ω → PathSpace)
    (hX :
      IsLocalMartingaleProblemSolution
        (Measure.dirac x) σσᵀ b ℱ (P : Measure Ω) X)
    (y : E') (T : NNReal) :
    ∫ z, H z y ∂((P : Measure Ω).map (fun ω ↦ X ω T)) =
      ∫ ω, H x (Y y T ω) ∂(Q y) := by
  -- Proof comment: first rewrite the time marginal integral as an integral over realizations,
  -- then invoke the fixed-start duality identity.
  have hXT :
      AEMeasurable (fun ω ↦ X ω T) (P : Measure Ω) :=
    aemeasurable_stateEval_of_aemeasurable_path hX.aemeasurable_path T
  have hHy_meas : Measurable (fun z : State ↦ H z y) :=
    measurable_stateObservable_of_separatingFamily
      (H := H) hsep y
  have hdual :
      Integrable (fun ω ↦ H (X ω T) y) (P : Measure Ω) ∧
        Integrable (fun ω ↦ H x (Y y T ω)) (Q y) ∧
          ∫ ω, H (X ω T) y ∂(P : Measure Ω) =
            ∫ ω, H x (Y y T ω) ∂(Q y) := by
    -- Proof comment: the `pathProcess` wrapper is definitionally just deterministic-time
    -- evaluation of the path-valued realization.
    simpa [pathProcess] using hduality x ℱ P X hX y T
  calc
    ∫ z, H z y ∂((P : Measure Ω).map (fun ω ↦ X ω T))
      = ∫ ω, H (X ω T) y ∂(P : Measure Ω) := by
          rw [integral_map hXT hHy_meas.aestronglyMeasurable]
    _ = ∫ ω, H x (Y y T ω) ∂(Q y) := hdual.2.2

-- Proof sketch: for fixed `x`, `T`, and two Dirac-initial solutions `L` and `L'`, apply the
-- duality identity to both solutions. The right-hand side depends only on `x`, `y`, and `T`, so
-- the expectations of `H (·, y)` against the two time-`T` marginals agree for every `y`. Since
-- the family `H(·, y)` is separating on probability measures on `ℝⁿ`, the two marginals coincide.
/-- Duality with a separating class of complex-valued observables implies uniqueness of the
deterministic-time marginals of Dirac-initial solutions of `LMP (σσᵀ, b)`. -/
theorem hasDeterministicTimeMarginalUniqueness_of_duality
    :
    ∀ (x : State)
      {Ω : Type _} [MeasurableSpace Ω]
      (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
      (μ : Measure Ω) (X : Ω → PathSpace)
      {Ω' : Type _} [MeasurableSpace Ω']
      (ℱ' : Filtration NNReal (inferInstance : MeasurableSpace Ω'))
      (μ' : Measure Ω') (X' : Ω' → PathSpace),
      IsLocalMartingaleProblemSolution (Measure.dirac x) σσᵀ b ℱ μ X →
      IsLocalMartingaleProblemSolution (Measure.dirac x) σσᵀ b ℱ' μ' X' →
      ∀ T : NNReal,
        μ.map (fun ω ↦ X ω T) = μ'.map (fun ω ↦ X' ω T) := by
  intro x Ω _ ℱ μ X Ω' _ ℱ' μ' X' hX hX' T
  let P : ProbabilityMeasure Ω := ⟨μ, hX.isProbabilityMeasure⟩
  let P' : ProbabilityMeasure Ω' := ⟨μ', hX'.isProbabilityMeasure⟩
  have hXT :
      AEMeasurable (fun ω ↦ X ω T) (P : Measure Ω) :=
    aemeasurable_stateEval_of_aemeasurable_path hX.aemeasurable_path T
  have hX'T :
      AEMeasurable (fun ω ↦ X' ω T) (P' : Measure Ω') :=
    aemeasurable_stateEval_of_aemeasurable_path hX'.aemeasurable_path T
  have hμT :
      ((P : Measure Ω).map (fun ω ↦ X ω T)) ∈
        {ν : Measure State | IsProbabilityMeasure ν} := by
    -- Proof comment: deterministic-time marginals of probability laws are again probability
    -- measures.
    exact Measure.isProbabilityMeasure_map hXT
  have hμ'T :
      ((P' : Measure Ω').map (fun ω ↦ X' ω T)) ∈
        {ν : Measure State | IsProbabilityMeasure ν} := by
    -- Proof comment: the same pushforward-probability argument applies to the second solution.
    exact Measure.isProbabilityMeasure_map hX'T
  -- Proof comment: equality of all separating observables identifies the two time marginals.
  exact IsSeparatingFamilyFor.eq_of_forall_integral_eq hsep hμT hμ'T <| by
    rintro f ⟨y, rfl⟩ _ _
    calc
      ∫ z, H z y ∂((P : Measure Ω).map (fun ω ↦ X ω T))
        = ∫ ω, H x (Y y T ω) ∂(Q y) :=
            dualityTimeMarginalIntegral_eq_dualExpectation
              σ b Q Y H hsep hduality x ℱ P X hX y T
      _ = ∫ z, H z y ∂((P' : Measure Ω').map (fun ω ↦ X' ω T)) := by
            symm
            exact
              dualityTimeMarginalIntegral_eq_dualExpectation
                σ b Q Y H hsep hduality x ℱ' P' X' hX' y T

/-- Helper for Theorem 26.28: an a.e.-measurable path-valued random variable has a.e.-measurable
finite deterministic-time tuples. -/
private theorem aemeasurable_timeTuple_of_aemeasurable_path
    {Ω : Type _} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → PathSpace} {k : ℕ}
    (hX : AEMeasurable X μ) (times : Fin (k + 1) → NNReal) :
    AEMeasurable (fun ω ↦ fun i : Fin (k + 1) ↦ X ω (times i)) μ := by
  -- Proof comment: finite deterministic-time tuples are assembled coordinatewise from the
  -- corresponding deterministic-time evaluations of the path map.
  exact aemeasurable_pi_lambda _ fun i ↦
    aemeasurable_stateEval_of_aemeasurable_path hX (times i)

/-- Helper for Theorem 26.28: deterministic-time tuple laws can be computed either directly on
the realization space or after first pushing the realization to canonical path space. -/
private theorem map_timeTuple_eq_map_pathLaw
    {Ω : Type _} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → PathSpace} {k : ℕ}
    (hX : AEMeasurable X μ)
    (times : Fin (k + 1) → NNReal) :
    μ.map (fun ω ↦ fun i : Fin (k + 1) ↦ X ω (times i)) =
      (μ.map X).map (fun γ : PathSpace ↦ fun i : Fin (k + 1) ↦ γ (times i)) := by
  let tupleMap : PathSpace → Fin (k + 1) → State := fun γ i ↦ γ (times i)
  let hPathLaw : HasLaw X (μ.map X) μ := ⟨hX, rfl⟩
  let hTupleLaw :
      HasLaw tupleMap ((μ.map X).map tupleMap) (μ.map X) := by
    exact
      ⟨aemeasurable_timeTuple_of_aemeasurable_path
          (μ := μ.map X) measurable_id.aemeasurable times, rfl⟩
  -- Proof comment: compose the canonical law of `X` with the canonical deterministic-time tuple
  -- law on path space, so the tuple-law rewrite is a single `HasLaw.comp` normalization.
  simpa [tupleMap, Function.comp] using (HasLaw.comp hTupleLaw hPathLaw).map_eq

/-- Helper for Theorem 26.28: a one-time marginal equality is the `k = 0` case of finite
deterministic-time tuple equality after identifying `State` with `Fin 1 → State`. -/
private theorem map_singleTimeMarginal_eq_of_eq
    {μ ν : Measure PathSpace} (t : NNReal)
    (h : μ.map (fun ω : PathSpace ↦ ω t) = ν.map (fun ω : PathSpace ↦ ω t)) :
    μ.map (fun ω ↦ fun _ : Fin 1 ↦ ω t) =
      ν.map (fun ω ↦ fun _ : Fin 1 ↦ ω t) := by
  let c : State → Fin 1 → State := fun x _ ↦ x
  have hc : Measurable c := by
    -- Proof comment: turning one state into the unique `Fin 1`-tuple is measurable.
    exact measurable_pi_lambda _ fun _ ↦ measurable_id
  -- Proof comment: both `Fin 1`-valued laws are just the corresponding single-time marginals
  -- pushed forward along the unique-coordinate identification map.
  calc
    μ.map (fun ω ↦ fun _ : Fin 1 ↦ ω t) = (μ.map (fun ω : PathSpace ↦ ω t)).map c := by
      rw [Measure.map_map hc (continuous_eval_const t).measurable]
      rfl
    _ = (ν.map (fun ω : PathSpace ↦ ω t)).map c := by
      exact congrArg (fun m : Measure State ↦ m.map c) h
    _ = ν.map (fun ω ↦ fun _ : Fin 1 ↦ ω t) := by
      rw [Measure.map_map hc (continuous_eval_const t).measurable]
      rfl

/-- Helper for Theorem 26.28: if a deterministic time tuple is monotone, then its prefix tuple
obtained by deleting the last index is still monotone. -/
private theorem monotone_castSucc
    {k : ℕ} {times : Fin (k + 2) → NNReal} (htimes : Monotone times) :
    Monotone (fun i : Fin (k + 1) ↦ times i.castSucc) := by
  intro i j hij
  -- Proof comment: `Fin.castSucc` preserves the order of indices, so monotonicity descends to
  -- the prefix tuple.
  exact htimes (by simpa using hij)

/-- Helper for Theorem 26.28: for a successor tuple of deterministic times, the restart gap is
the difference between the terminal time and the last prefix time. -/
private def lastRestartGap
    {k : ℕ} (times : Fin (k + 2) → NNReal) : NNReal :=
  times (Fin.last (k + 1)) - times (Fin.castSucc (Fin.last k))

/-- Helper for Theorem 26.28: for a sorted deterministic time tuple, the terminal time is the sum
of the last prefix time and the restart gap used in the successor-step comparison. -/
private theorem lastTime_eq_prefixLast_add_lastRestartGap_of_monotone
    {k : ℕ} {times : Fin (k + 2) → NNReal} (htimes : Monotone times) :
    times (Fin.last (k + 1)) =
      times (Fin.castSucc (Fin.last k)) + lastRestartGap times := by
  -- Proof comment: monotonicity makes the last prefix time no larger than the terminal time, so
  -- the latter splits into the prefix endpoint plus the nonnegative restart gap.
  simpa [lastRestartGap, add_comm] using
    (tsub_add_cancel_of_le
      (htimes (le_of_lt (Fin.castSucc_lt_last (Fin.last k))))).symm

/-- Helper for Theorem 26.28: project a sorted prefix tuple to its final coordinate. -/
private def lastPrefixState {k : ℕ} : (Fin (k + 1) → State) → State := fun z ↦ z (Fin.last k)

/-- Helper for Theorem 26.28: the last-prefix projection is measurable. -/
private theorem measurable_lastPrefixState {k : ℕ} :
    Measurable (lastPrefixState (n := n) (k := k)) := by
  -- Proof comment: this is just evaluation at the final coordinate of the prefix tuple.
  simpa [lastPrefixState] using
    (measurable_pi_apply (Fin.last k) :
      Measurable (fun z : Fin (k + 1) → State ↦ z (Fin.last k)))

/-- Helper for Theorem 26.28: projecting the prefix tuple law to its final coordinate recovers
the deterministic-time law at the last prefix time. -/
private theorem map_lastPrefixState_eq_of_prefixTupleLaw
    {Ω : Type _} [MeasurableSpace Ω]
    {k : ℕ} {μ : Measure Ω}
    {X : Ω → PathSpace}
    (times : Fin (k + 2) → NNReal)
    (hPrefixAEMeas :
      AEMeasurable (fun ω ↦ fun i : Fin (k + 1) ↦ X ω (times i.castSucc)) μ) :
    (μ.map (fun ω ↦ fun i : Fin (k + 1) ↦ X ω (times i.castSucc))).map
        (lastPrefixState (k := k)) =
      μ.map (fun ω ↦ X ω (times (Fin.castSucc (Fin.last k)))) := by
  -- Proof comment: composing the prefix tuple with the last-coordinate projection is exactly the
  -- deterministic-time evaluation at the final prefix time.
  rw [AEMeasurable.map_map_of_aemeasurable
    (measurable_lastPrefixState (k := k)).aemeasurable hPrefixAEMeas]
  rfl

/-- Helper for Theorem 26.28: equality of the sorted prefix tuple laws already forces equality of
the current-state laws at the last prefix time, obtained by projecting the tuple to its final
coordinate. -/
private theorem map_lastPrefixState_eq_of_prefixTupleLaw_eq
    {Ω : Type _} [MeasurableSpace Ω]
    {Ω' : Type _} [MeasurableSpace Ω']
    {k : ℕ} {μ : Measure Ω} {μ' : Measure Ω'}
    {X : Ω → PathSpace} {X' : Ω' → PathSpace}
    (times : Fin (k + 2) → NNReal)
    (hPrefixAEMeasX :
      AEMeasurable (fun ω ↦ fun i : Fin (k + 1) ↦ X ω (times i.castSucc)) μ)
    (hPrefixAEMeasX' :
      AEMeasurable (fun ω ↦ fun i : Fin (k + 1) ↦ X' ω (times i.castSucc)) μ')
    (hPrefix :
      μ.map (fun ω ↦ fun i : Fin (k + 1) ↦ X ω (times i.castSucc)) =
        μ'.map (fun ω ↦ fun i : Fin (k + 1) ↦ X' ω (times i.castSucc))) :
    μ.map (fun ω ↦ X ω (times (Fin.castSucc (Fin.last k)))) =
      μ'.map (fun ω ↦ X' ω (times (Fin.castSucc (Fin.last k)))) := by
  -- Proof comment: map the common prefix law through the last-coordinate projection to recover
  -- the current-state law at the restart time on both realization spaces.
  calc
    μ.map (fun ω ↦ X ω (times (Fin.castSucc (Fin.last k))))
        = (μ.map (fun ω ↦ fun i : Fin (k + 1) ↦ X ω (times i.castSucc))).map
            (lastPrefixState (k := k)) := by
            simpa using
              (map_lastPrefixState_eq_of_prefixTupleLaw
                (μ := μ)
                (X := X)
                times
                hPrefixAEMeasX).symm
    _ = (μ'.map (fun ω ↦ fun i : Fin (k + 1) ↦ X' ω (times i.castSucc))).map
          (lastPrefixState (k := k)) := by
          exact
            congrArg
              (fun ν : Measure (Fin (k + 1) → State) ↦ ν.map (lastPrefixState (k := k)))
              hPrefix
    _ = μ'.map (fun ω ↦ X' ω (times (Fin.castSucc (Fin.last k)))) := by
          simpa using
            map_lastPrefixState_eq_of_prefixTupleLaw
              (μ := μ')
              (X := X')
              times
              hPrefixAEMeasX'

/-- Helper for Theorem 26.28: once the underlying path map is a.e.-measurable, the path-space
`(last, prefix)` conditional law transports back to the realization space by `condDistrib_map`. -/
private theorem condDistrib_evalLast_prefixTuple_map_of_aemeasurable_path
    {Ω : Type _} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → PathSpace} {k : ℕ}
    (hX : AEMeasurable X μ) (times : Fin (k + 2) → NNReal) :
    condDistrib
        (fun ω : PathSpace ↦ ω (times (Fin.last (k + 1))))
        (fun ω : PathSpace ↦ fun i : Fin (k + 1) ↦ ω (times i.castSucc))
        (μ.map X)
      =ᵐ[μ.map (fun ω ↦ fun i : Fin (k + 1) ↦ X ω (times i.castSucc))]
        condDistrib
          (fun ω ↦ X ω (times (Fin.last (k + 1))))
          (fun ω ↦ fun i : Fin (k + 1) ↦ X ω (times i.castSucc))
          μ := by
  let evalLast : PathSpace → State := fun ω ↦ ω (times (Fin.last (k + 1)))
  let prefixTuple : PathSpace → Fin (k + 1) → State :=
    fun ω i ↦ ω (times i.castSucc)
  have hEvalLast : AEMeasurable evalLast (μ.map X) :=
    (measurable_path_eval (times (Fin.last (k + 1)))).aemeasurable
  have hPrefixTuple : AEMeasurable prefixTuple (μ.map X) := by
    -- Proof comment: the prefix tuple is measurable because each coordinate is a measurable
    -- deterministic-time evaluation on path space.
    exact
      (measurable_pi_lambda _ fun i ↦ measurable_path_eval (times (Fin.castSucc i))).aemeasurable
  -- Proof comment: apply `condDistrib_map` once to transport the conditional law from canonical
  -- path space back to the original realization space.
  simpa [evalLast, prefixTuple, Function.comp] using
    (condDistrib_map (ν := μ) (f := X) (X := prefixTuple) (Y := evalLast)
      hPrefixTuple hEvalLast hX)

/-- Helper for Theorem 26.28: a common prefix law together with a common conditional law of the
next state determines the joint law of the split pair `(next, prefix)`. -/
private theorem map_lastSplit_eq_of_prefixLaw_and_prefixKernel_eq
    {α : Type _} [MeasurableSpace α]
    {β : Type _} [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]
    {Ω : Type u} [MeasurableSpace Ω]
    {Ω' : Type v} [MeasurableSpace Ω']
    (μ : Measure Ω) (μ' : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    {H : Ω → α} {H' : Ω' → α} {N : Ω → β} {N' : Ω' → β}
    (hH : AEMeasurable H μ) (hH' : AEMeasurable H' μ')
    (hN : AEMeasurable N μ) (hN' : AEMeasurable N' μ')
    (hprefix : μ.map H = μ'.map H')
    (hkernel : condDistrib N H μ =ᵐ[μ.map H] condDistrib N' H' μ') :
    μ.map (fun ω ↦ (N ω, H ω)) = μ'.map (fun ω ↦ (N' ω, H' ω)) := by
  have hPair :
      μ.map (fun ω ↦ (H ω, N ω)) = μ'.map (fun ω ↦ (H' ω, N' ω)) := by
    -- Proof comment: both `(prefix,next)` laws are the same `compProd` of the common prefix law
    -- with the common conditional next-state kernel.
    calc
      μ.map (fun ω ↦ (H ω, N ω)) = μ.map H ⊗ₘ condDistrib N H μ := by
        symm
        exact compProd_map_condDistrib hN
      _ = μ.map H ⊗ₘ condDistrib N' H' μ' := by
        exact Measure.compProd_congr hkernel
      _ = μ'.map H' ⊗ₘ condDistrib N' H' μ' := by
        rw [hprefix]
      _ = μ'.map (fun ω ↦ (H' ω, N' ω)) := by
        exact compProd_map_condDistrib hN'
  have hSwap :
      μ.map (fun ω ↦ (N ω, H ω)) =
        (μ.map (fun ω ↦ (H ω, N ω))).map Prod.swap := by
    -- Proof comment: the target split law only differs by swapping the product coordinates.
    rw [AEMeasurable.map_map_of_aemeasurable measurable_swap.aemeasurable (hH.prodMk hN)]
    rfl
  have hSwap' :
      μ'.map (fun ω ↦ (N' ω, H' ω)) =
        (μ'.map (fun ω ↦ (H' ω, N' ω))).map Prod.swap := by
    -- Proof comment: apply the same swap normalization to the second split law.
    rw [AEMeasurable.map_map_of_aemeasurable measurable_swap.aemeasurable (hH'.prodMk hN')]
    rfl
  calc
    μ.map (fun ω ↦ (N ω, H ω)) = (μ.map (fun ω ↦ (H ω, N ω))).map Prod.swap := hSwap
    _ = (μ'.map (fun ω ↦ (H' ω, N' ω))).map Prod.swap := by
      exact congrArg (fun ν : Measure (α × β) ↦ ν.map Prod.swap) hPair
    _ = μ'.map (fun ω ↦ (N' ω, H' ω)) := hSwap'.symm

/-- Helper for Theorem 26.28: once the split-tuple laws agree on the realization spaces, mapping
both sides through the inverse of `MeasurableEquiv.piFinSuccAbove` recovers the full tuple laws. -/
private theorem map_fullTupleLaw_eq_of_splitTupleLaw_eq
    {α : Type _} [MeasurableSpace α]
    {β : Type _} [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {k : ℕ}
    (splitX : α → State × (Fin (k + 1) → State))
    (splitY : β → State × (Fin (k + 1) → State))
    (hSplitAEMeasX : AEMeasurable splitX μ) (hSplitAEMeasY : AEMeasurable splitY ν)
    (hSplit :
      μ.map splitX = ν.map splitY) :
    μ.map
        (fun x ↦
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 2) ↦ State)
            (Fin.last (k + 1))).symm (splitX x)) =
      ν.map
        (fun y ↦
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 2) ↦ State)
            (Fin.last (k + 1))).symm (splitY y)) := by
  let e :
      State × (Fin (k + 1) → State) ≃ᵐ (Fin (k + 2) → State) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 2) ↦ State) (Fin.last (k + 1))).symm
  calc
    μ.map (fun x ↦ e (splitX x)) = (μ.map splitX).map e := by
      -- Proof comment: map the realization law through the inverse splitting equivalence once,
      -- then use the assumed split-law equality there.
      rw [AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable hSplitAEMeasX]
      rfl
    _ = (ν.map splitY).map e := by
      exact congrArg (fun m : Measure (State × (Fin (k + 1) → State)) ↦ m.map e) hSplit
    _ = ν.map (fun y ↦ e (splitY y)) := by
      rw [AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable hSplitAEMeasY]
      rfl

/-- Helper for Theorem 26.28: pulling back an almost-everywhere equal state kernel along a
measurable map preserves that almost-everywhere equality on the source measure. -/
private theorem Kernel.comap_ae_eq_of_ae_eq_map
    {α : Type _} [MeasurableSpace α]
    {β : Type _} [MeasurableSpace β]
    {γ : Type _} [MeasurableSpace γ]
    {μ : Measure α} {f : α → β}
    (hf : Measurable f)
    {κ κ' : Kernel β γ}
    (hκ : κ =ᵐ[μ.map f] κ') :
    Kernel.comap κ f hf =ᵐ[μ] Kernel.comap κ' f hf := by
  have hκ' : ∀ᵐ x ∂μ, κ (f x) = κ' (f x) := ae_of_ae_map hf.aemeasurable hκ
  -- Proof comment: `Kernel.comap` only reevaluates the source kernel at `f x`, so equality of
  -- the original kernel rows at `f x` immediately yields equality after pullback to `x`.
  filter_upwards [hκ'] with x hx
  simpa [Kernel.comap_apply] using hx

/-- Helper for Theorem 26.28: once the two-time pair laws `(current, next)` agree, the
corresponding conditional next-state kernels agree almost everywhere over the common current-state
law. -/
private theorem condDistrib_eq_of_pairLaw_eq
    {α : Type _} [MeasurableSpace α]
    {β : Type _} [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β]
    {Ω : Type u} [MeasurableSpace Ω]
    {Ω' : Type v} [MeasurableSpace Ω']
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {μ' : Measure Ω'} [IsFiniteMeasure μ']
    {H : Ω → α} {H' : Ω' → α} {N : Ω → β} {N' : Ω' → β}
    (hH : Measurable H) (hN : Measurable N) (hN' : Measurable N')
    (hPair :
      μ.map (fun ω ↦ (H ω, N ω)) = μ'.map (fun ω ↦ (H' ω, N' ω))) :
    condDistrib N H μ =ᵐ[μ.map H] condDistrib N' H' μ' := by
  have hHead : μ.map H = μ'.map H' := by
    calc
      μ.map H = (μ.map (fun ω ↦ (H ω, N ω))).fst := by
        symm
        exact Measure.fst_map_prodMk hN
      _ = (μ'.map (fun ω ↦ (H' ω, N' ω))).fst := by
        rw [hPair]
      _ = μ'.map H' := by
        exact Measure.fst_map_prodMk hN'
  have hComp : μ.map (fun ω ↦ (H ω, N ω)) = μ.map H ⊗ₘ condDistrib N' H' μ' := by
    calc
      μ.map (fun ω ↦ (H ω, N ω)) = μ'.map (fun ω ↦ (H' ω, N' ω)) := hPair
      _ = μ'.map H' ⊗ₘ condDistrib N' H' μ' := by
        symm
        exact compProd_map_condDistrib hN'.aemeasurable
      _ = μ.map H ⊗ₘ condDistrib N' H' μ' := by
        rw [hHead]
  -- Proof comment: the defining `compProd` characterization of conditional distribution pins
  -- down the same next-state kernel once the `(current,next)` pair laws agree.
  exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hH hN hComp

/-- Helper for Theorem 26.28: a two-time pair-law identity on canonical path space transports
back to the original realization spaces by a single `map_map` normalization. -/
private theorem map_twoTimePair_eq_of_pathLaw_eq
    {Ω : Type _} [MeasurableSpace Ω]
    {Ω' : Type _} [MeasurableSpace Ω']
    {μ : Measure Ω} {μ' : Measure Ω'}
    {X : Ω → PathSpace} {X' : Ω' → PathSpace}
    (hX : AEMeasurable X μ) (hX' : AEMeasurable X' μ')
    (s t : NNReal)
    (hPair :
      (μ.map X).map (fun ω : PathSpace ↦ (ω s, ω t)) =
        (μ'.map X').map (fun ω : PathSpace ↦ (ω s, ω t))) :
    μ.map (fun ω ↦ (X ω s, X ω t)) =
      μ'.map (fun ω ↦ (X' ω s, X' ω t)) := by
  let evalPair : PathSpace → State × State := fun ω ↦ (ω s, ω t)
  have hEvalPair : Measurable evalPair := by
    -- Proof comment: the two-time evaluation map is measurable coordinatewise on path space.
    exact (measurable_path_eval s).prodMk (measurable_path_eval t)
  calc
    μ.map (fun ω ↦ (X ω s, X ω t)) = (μ.map X).map evalPair := by
      -- Proof comment: rewrite the first realization-space pair law through the canonical path
      -- law, then insert the path-law pair identity.
      rw [AEMeasurable.map_map_of_aemeasurable hEvalPair.aemeasurable hX]
      rfl
    _ = (μ'.map X').map evalPair := hPair
    _ = μ'.map (fun ω ↦ (X' ω s, X' ω t)) := by
      rw [AEMeasurable.map_map_of_aemeasurable hEvalPair.aemeasurable hX']
      rfl

/-- Helper for Theorem 26.28: the realization-space two-time pair law is the pushforward of the
canonical path-law pair evaluation map `(γ ↦ (γ s, γ t))`. -/
private theorem map_twoTimePair_eq_map_pathLaw
    {Ω : Type _} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → PathSpace}
    (hX : AEMeasurable X μ) (s t : NNReal) :
    μ.map (fun ω ↦ (X ω s, X ω t)) =
      (μ.map X).map (fun ω : PathSpace ↦ (ω s, ω t)) := by
  -- Proof comment: this is the specialization of the previous transport lemma to the reflexive
  -- canonical pair-law identity.
  let evalPair : PathSpace → State × State := fun ω ↦ (ω s, ω t)
  have hEvalPair : Measurable evalPair := by
    exact (measurable_path_eval s).prodMk (measurable_path_eval t)
  rw [AEMeasurable.map_map_of_aemeasurable hEvalPair.aemeasurable hX]
  rfl

/-- Helper for Theorem 26.28: equality of finite deterministic-time tuple laws is invariant under
reindexing the tuple coordinates by a permutation. -/
private theorem map_finiteDimensionalLaw_eq_of_reindex
    {α : Type _} [MeasurableSpace α]
    {β : Type _} [MeasurableSpace β]
    {k : ℕ} {μ : Measure α} {ν : Measure β}
    (f : α → Fin (k + 1) → State) (g : β → Fin (k + 1) → State)
    (σ : Equiv.Perm (Fin (k + 1))) (hf : AEMeasurable f μ) (hg : AEMeasurable g ν)
    (hσ :
      μ.map (fun x ↦ fun i ↦ f x (σ i)) =
        ν.map (fun y ↦ fun i ↦ g y (σ i))) :
    μ.map f = ν.map g := by
  let r : (Fin (k + 1) → State) → Fin (k + 1) → State := fun z i ↦ z (σ.symm i)
  have hr : Measurable r := by
    exact measurable_pi_lambda _ fun i ↦ measurable_pi_apply (σ.symm i)
  have hfσ : AEMeasurable (fun x ↦ fun i ↦ f x (σ i)) μ := by
    exact (measurable_pi_lambda _ fun i ↦ measurable_pi_apply (σ i)).comp_aemeasurable hf
  have hgσ : AEMeasurable (fun y ↦ fun i ↦ g y (σ i)) ν := by
    exact (measurable_pi_lambda _ fun i ↦ measurable_pi_apply (σ i)).comp_aemeasurable hg
  have hrf : (fun z i ↦ r z i) ∘ (fun x ↦ fun i ↦ f x (σ i)) = f := by
    funext x i
    simp [r]
  have hrg : (fun z i ↦ r z i) ∘ (fun y ↦ fun i ↦ g y (σ i)) = g := by
    funext y i
    simp [r]
  have hrfMap :
      μ.map ((fun z i ↦ r z i) ∘ fun x ↦ fun i ↦ f x (σ i)) = μ.map f := by
    simpa [hrf]
  have hrgMap :
      ν.map ((fun z i ↦ r z i) ∘ fun y ↦ fun i ↦ g y (σ i)) = ν.map g := by
    simpa [hrg]
  calc
    μ.map f = (μ.map (fun x ↦ fun i ↦ f x (σ i))).map r := by
      symm
      rw [AEMeasurable.map_map_of_aemeasurable hr.aemeasurable hfσ]
      exact hrfMap
    _ = (ν.map (fun y ↦ fun i ↦ g y (σ i))).map r := by
      exact congrArg (fun m : Measure (Fin (k + 1) → State) ↦ m.map r) hσ
    _ = ν.map g := by
      rw [AEMeasurable.map_map_of_aemeasurable hr.aemeasurable hgσ]
      exact hrgMap

/-- Helper for Theorem 26.28: to prove equality of arbitrary deterministic-time tuple laws it is
enough to prove it after sorting the deterministic times. -/
private theorem map_finiteDimensionalLaw_eq_of_sortedReindex
    {α : Type _} [MeasurableSpace α]
    {β : Type _} [MeasurableSpace β]
    {k : ℕ} {μ : Measure α} {ν : Measure β}
    (f : α → PathSpace) (g : β → PathSpace) (times : Fin (k + 1) → NNReal)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g ν)
    (hsorted :
      μ.map (fun x ↦ fun i ↦ f x ((times ∘ Tuple.sort times) i)) =
        ν.map (fun y ↦ fun i ↦ g y ((times ∘ Tuple.sort times) i))) :
    μ.map (fun x ↦ fun i ↦ f x (times i)) =
      ν.map (fun y ↦ fun i ↦ g y (times i)) := by
  let tupleF : α → Fin (k + 1) → State := fun x i ↦ f x (times i)
  let tupleG : β → Fin (k + 1) → State := fun y i ↦ g y (times i)
  have hTupleF : AEMeasurable tupleF μ := by
    -- Proof comment: the unsorted finite-dimensional tuple is coordinatewise measurable once the
    -- underlying path map is a.e.-measurable.
    simpa [tupleF] using aemeasurable_timeTuple_of_aemeasurable_path (μ := μ) hf times
  have hTupleG : AEMeasurable tupleG ν := by
    -- Proof comment: the same coordinatewise measurability holds for the second realization.
    simpa [tupleG] using aemeasurable_timeTuple_of_aemeasurable_path (μ := ν) hg times
  -- Proof comment: sorting only reindexes the tuple coordinates by the permutation
  -- `Tuple.sort times`, so the generic reindexing lemma removes the sorted normal form.
  simpa [tupleF, tupleG, Function.comp] using
    (map_finiteDimensionalLaw_eq_of_reindex
      (μ := μ) (ν := ν) tupleF tupleG (Tuple.sort times) hTupleF hTupleG hsorted)

/-- Helper for Theorem 26.28: once all deterministic-time tuple laws agree, the full pushed-
forward path laws agree as well. -/
private theorem diracSolution_pathLaw_eq_of_finiteDimensionalMarginals_eq
    (x : State)
    {Ω : Type _} [MeasurableSpace Ω]
    (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (μ : Measure Ω) (X : Ω → PathSpace)
    {Ω' : Type _} [MeasurableSpace Ω']
    (ℱ' : Filtration NNReal (inferInstance : MeasurableSpace Ω'))
    (μ' : Measure Ω') (X' : Ω' → PathSpace)
    (hX : IsLocalMartingaleProblemSolution (Measure.dirac x) σσᵀ b ℱ μ X)
    (hX' : IsLocalMartingaleProblemSolution (Measure.dirac x) σσᵀ b ℱ' μ' X')
    (hFinite :
      ∀ {k : ℕ} (times : Fin (k + 1) → NNReal),
        μ.map (fun ω ↦ fun i : Fin (k + 1) ↦ X ω (times i)) =
          μ'.map (fun ω ↦ fun i : Fin (k + 1) ↦ X' ω (times i))) :
    μ.map X = μ'.map X' := by
  let P : ProbabilityMeasure Ω := ⟨μ, hX.isProbabilityMeasure⟩
  let P' : ProbabilityMeasure Ω' := ⟨μ', hX'.isProbabilityMeasure⟩
  let PX : ProbabilityMeasure PathSpace :=
    ⟨(P : Measure Ω).map X, Measure.isProbabilityMeasure_map hX.aemeasurable_path⟩
  let PX' : ProbabilityMeasure PathSpace :=
    ⟨(P' : Measure Ω').map X', Measure.isProbabilityMeasure_map hX'.aemeasurable_path⟩
  have hFinitePath :
      ∀ {k : ℕ} (times : Fin (k + 1) → NNReal),
        (PX : Measure PathSpace).map (fun γ ↦ fun i : Fin (k + 1) ↦ γ (times i)) =
          (PX' : Measure PathSpace).map (fun γ ↦ fun i : Fin (k + 1) ↦ γ (times i)) := by
    intro k times
    -- Proof comment: rewrite both canonical tuple laws back to the original realization spaces,
    -- apply the assumed finite-dimensional comparison there, and then package the result again on
    -- path space.
    calc
      (PX : Measure PathSpace).map (fun γ ↦ fun i : Fin (k + 1) ↦ γ (times i))
          = μ.map (fun ω ↦ fun i : Fin (k + 1) ↦ X ω (times i)) := by
              rw [show (PX : Measure PathSpace) = (P : Measure Ω).map X by rfl]
              simpa using
                (map_timeTuple_eq_map_pathLaw
                  (μ := (P : Measure Ω)) (X := X) hX.aemeasurable_path times).symm
      _ = μ'.map (fun ω ↦ fun i : Fin (k + 1) ↦ X' ω (times i)) := hFinite times
      _ = (PX' : Measure PathSpace).map (fun γ ↦ fun i : Fin (k + 1) ↦ γ (times i)) := by
            rw [show (PX' : Measure PathSpace) = (P' : Measure Ω').map X' by rfl]
            simpa using
              map_timeTuple_eq_map_pathLaw
                (μ := (P' : Measure Ω')) (X := X') hX'.aemeasurable_path times
  have hPathLaw :
      PX = PX' :=
    probabilityMeasure_eq_of_euclideanPathFiniteDimensionalDistribution_eq hFinitePath
  -- Proof comment: Theorem 26.8 already identifies a probability law on path space by all of its
  -- deterministic-time finite-dimensional distributions.
  simpa [P, P', PX, PX'] using
    congrArg (fun ν : ProbabilityMeasure PathSpace ↦ (ν : Measure PathSpace)) hPathLaw

/-- Helper for Theorem 26.28: time-independent Dirac-start existence together with explicit
deterministic-time marginal uniqueness should imply uniqueness in law at the fixed start `x`. -/
private theorem localMartingaleProblemHasUniqueLaw_of_explicitMarginalUniqueness
    (h26_21 :
      (∀ t₁ t₂ x, σσᵀ t₁ x = σσᵀ t₂ x) ∧
        ∀ t₁ t₂ x, b t₁ x = b t₂ x)
    (hex :
      ∀ x : State,
        ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (ℱ : Filtration NNReal mΩ)
          (P : ProbabilityMeasure Ω) (X : Ω → PathSpace),
          IsLocalMartingaleProblemSolution
            (Measure.dirac x) σσᵀ b ℱ (P : Measure Ω) X)
    (huniq :
      ∀ (x : State)
        {Ω : Type _} [MeasurableSpace Ω]
        (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
        (μ : Measure Ω) (X : Ω → PathSpace)
        {Ω' : Type _} [MeasurableSpace Ω']
        (ℱ' : Filtration NNReal (inferInstance : MeasurableSpace Ω'))
        (μ' : Measure Ω') (X' : Ω' → PathSpace),
        IsLocalMartingaleProblemSolution (Measure.dirac x) σσᵀ b ℱ μ X →
        IsLocalMartingaleProblemSolution (Measure.dirac x) σσᵀ b ℱ' μ' X' →
        ∀ T : NNReal,
          μ.map (fun ω ↦ X ω T) = μ'.map (fun ω ↦ X' ω T))
    (x : State) :
    LocalMartingaleProblemHasUniqueLaw (Measure.dirac x) σσᵀ b := by
  -- Route correction: the deterministic-time-marginal-to-path-law upgrade is already packaged by
  -- the earlier owner theorem from Theorem 26.25, so this file should reuse that canonical
  -- result instead of maintaining a second local restart-step proof.
  have h26_21' : TimeIndependentLocalMartingaleProblemCoefficients σσᵀ b := h26_21
  have huniq' : HasDeterministicTimeMarginalUniqueness σσᵀ b := huniq
  exact
    localMartingaleProblemHasUniqueLaw_of_solutionExistence_of_deterministicTimeMarginalUniqueness
      σσᵀ
      b
      h26_21'
      hex
      huniq'
      x

/-- Helper for Theorem 26.28: after alias-normalizing the time-independence and deterministic-time
marginal uniqueness hypotheses, well-posedness is a direct call to the Theorem 26.25 owner. -/
private theorem localMartingaleProblemWellPosed_of_diracSolutionExistence_of_explicitMarginalUniqueness
    (h26_21 :
      (∀ t₁ t₂ x, σσᵀ t₁ x = σσᵀ t₂ x) ∧
        ∀ t₁ t₂ x, b t₁ x = b t₂ x)
    (hex :
      ∀ x : State,
        ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (ℱ : Filtration NNReal mΩ)
          (P : ProbabilityMeasure Ω) (X : Ω → PathSpace),
          IsLocalMartingaleProblemSolution
            (Measure.dirac x) σσᵀ b ℱ (P : Measure Ω) X)
    (huniq :
      ∀ (x : State)
        {Ω : Type _} [MeasurableSpace Ω]
        (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
        (μ : Measure Ω) (X : Ω → PathSpace)
        {Ω' : Type _} [MeasurableSpace Ω']
        (ℱ' : Filtration NNReal (inferInstance : MeasurableSpace Ω'))
        (μ' : Measure Ω') (X' : Ω' → PathSpace),
        IsLocalMartingaleProblemSolution (Measure.dirac x) σσᵀ b ℱ μ X →
        IsLocalMartingaleProblemSolution (Measure.dirac x) σσᵀ b ℱ' μ' X' →
        ∀ T : NNReal,
          μ.map (fun ω ↦ X ω T) = μ'.map (fun ω ↦ X' ω T)) :
    LocalMartingaleProblemWellPosed σσᵀ b := by
  -- Proof comment: normalize the explicit hypotheses to the chapter-owner predicate aliases so
  -- the final step is a direct reuse of Theorem 26.25 rather than a local reconstruction of
  -- Definition 26.23.
  have h26_21' : TimeIndependentLocalMartingaleProblemCoefficients σσᵀ b := h26_21
  have huniq' : HasDeterministicTimeMarginalUniqueness σσᵀ b := huniq
  exact
    localMartingaleProblemWellPosed_of_diracSolutionExistence_of_marginalUniqueness
      σσᵀ
      b
      h26_21'
      hex
      huniq'

-- Source proof sketch: by Theorem 26.25 it is enough to prove deterministic-time marginal
-- uniqueness, which the duality identity supplies via the separating family hypothesis. The
-- source-facing statement below intentionally follows the source theorem and leaves the proof to a
-- later stage.
/-- Theorem 26.28: if every Dirac initial condition admits a solution of `LMP (σσᵀ, b)`, and
the coefficients `(σσᵀ, b)` are time-independent, and there is a Markov-process realization
`(κ, Q, Y')` of the dual family on `E'`, and `H : State → E' → ℂ` is jointly measurable, and
every such solution is dual to `(Q, fun _ ↦ Y')` through `H` while the slices `H(·, y)` form a
separating family on probability measures on `ℝⁿ`, then the local
martingale problem for `(σσᵀ, b)` is well-posed. -/
theorem localMartingaleProblemWellPosed_of_duality
    (κ : NNReal → Kernel E' E')
    (Y' : NNReal → Ω' → E')
    [IsMarkovProcessRealization κ Q Y']
    (hH_meas : Measurable (Function.uncurry H))
    (hsep :
      IsSeparatingFamilyFor
        {μ : Measure State | IsProbabilityMeasure μ}
        (Set.range (Function.swap H)))
    (hduality :
      ∀ (x : State)
        {Ω : Type _} [MeasurableSpace Ω]
        (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
        (P : ProbabilityMeasure Ω) (X : Ω → PathSpace),
        IsLocalMartingaleProblemSolution
          (Measure.dirac x) σσᵀ b ℱ (P : Measure Ω) X →
        SatisfiesDualityAt (P : Measure Ω) (pathProcess X) x Q (fun _ ↦ Y') H)
    (h26_21 :
      (∀ t₁ t₂ x, σσᵀ t₁ x = σσᵀ t₂ x) ∧
        ∀ t₁ t₂ x, b t₁ x = b t₂ x)
    (hex :
      ∀ x : State,
        ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (ℱ : Filtration NNReal mΩ)
          (P : ProbabilityMeasure Ω) (X : Ω → PathSpace),
          IsLocalMartingaleProblemSolution
            (Measure.dirac x) σσᵀ b ℱ (P : Measure Ω) X) :
    LocalMartingaleProblemWellPosed σσᵀ b := by
  -- Route correction: the source proof closes through the Chapter 26 owner theorem rather than
  -- by unfolding well-posedness in this file. We therefore package the duality bridge into
  -- deterministic-time marginal uniqueness and hand it to Theorem 26.25.
  have huniq :
      ∀ (x : State)
        {Ω : Type _} [MeasurableSpace Ω]
        (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
        (μ : Measure Ω) (X : Ω → PathSpace)
        {Ω' : Type _} [MeasurableSpace Ω']
        (ℱ' : Filtration NNReal (inferInstance : MeasurableSpace Ω'))
        (μ' : Measure Ω') (X' : Ω' → PathSpace),
        IsLocalMartingaleProblemSolution (Measure.dirac x) σσᵀ b ℱ μ X →
        IsLocalMartingaleProblemSolution (Measure.dirac x) σσᵀ b ℱ' μ' X' →
        ∀ T : NNReal,
          μ.map (fun ω ↦ X ω T) = μ'.map (fun ω ↦ X' ω T) := by
    -- Proof comment: the separating family turns the fixed-start duality identity into equality
    -- of every deterministic-time marginal.
    intro x Ω mΩ ℱ μ X Ω' mΩ' ℱ' μ' X' hX hX' T
    exact
      hasDeterministicTimeMarginalUniqueness_of_duality
        (σ := σ) (b := b) (Q := Q) (Y := fun _ ↦ Y') (H := H)
        hsep hduality x ℱ μ X ℱ' μ' X' hX hX' T
  -- Proof comment: the local proof now ends at the explicit uniqueness predicate and leaves the
  -- owner-theorem upgrade as the sole remaining chapter-level blocker.
  exact
    localMartingaleProblemWellPosed_of_diracSolutionExistence_of_explicitMarginalUniqueness
      (σ := σ) (b := b) (Q := Q) (Y := fun _ ↦ Y') (H := H)
      h26_21 hex huniq

end

end ProbabilityTheory

import Mathlib.Data.Set.Finite.Lattice
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_4_2.ch5_sec5_4_2_algorithm_5_4_2_extra_1

section Theorem524

variable {n p : ℕ} (hp : p ≤ n)
variable {StageRow RestrictedRow : ℕ → Type}
variable (execution : specialized_lift_project_execution n p StageRow RestrictedRow)

variable
    (c : Fin n → ℝ)
    (is_optimal_basic_solution_of_stage :
      ∀ k, (Fin n → ℝ) → Matrix (StageRow k) (Fin n) ℝ → (StageRow k → ℝ) →
        (Fin n → ℝ) → Prop)
    (is_optimal_original_solution : (Fin n → ℝ) → Prop)
    (is_restricted_system :
      ∀ k, Fin p → Matrix (StageRow k) (Fin n) ℝ → (StageRow k → ℝ) →
        Matrix (RestrictedRow k) (Fin n) ℝ → (RestrictedRow k → ℝ) → Prop)
    (is_optimal_basic_solution_of_auxiliary_lp :
      ∀ k, Fin p → Matrix (RestrictedRow k) (Fin n) ℝ → (RestrictedRow k → ℝ) →
        lift_project_auxiliary_solution (RestrictedRow k) → Prop)
    (is_j_cut_of_auxiliary_solution :
      ∀ k, Fin p → Matrix (RestrictedRow k) (Fin n) ℝ → (RestrictedRow k → ℝ) →
        lift_project_auxiliary_solution (RestrictedRow k) → lift_project_cut n → Prop)
    (next_stage_adds_cut :
      ∀ k, Matrix (StageRow k) (Fin n) ℝ → (StageRow k → ℝ) → lift_project_cut n →
        Matrix (StageRow (k + 1)) (Fin n) ℝ → (StageRow (k + 1) → ℝ) → Prop)

namespace specialized_lift_project_execution

/-- A specialized lift-and-project run stops at stage `k` when the current basic solution already
satisfies the binary restrictions on the first `p` coordinates. -/
def StopsAt (k : ℕ) : Prop :=
  has_binary_prefix hp (execution.basic_solution k)

/-- A specialized lift-and-project run stops exactly when its current basic solution satisfies the
binary restrictions on the first `p` coordinates. -/
@[simp] theorem stopsAt_iff
    (k : ℕ) :
    execution.StopsAt hp k ↔ has_binary_prefix hp (execution.basic_solution k) :=
  Iff.rfl

/-- The optional selected-index view is `none` exactly at the stages where the specialized
lift-and-project run stops. -/
@[simp] theorem selectedIndexOption_eq_none_iff_stopsAt
    (k : ℕ) :
    execution.selectedIndexOption hp k = none ↔ execution.StopsAt hp k := by
  simpa [StopsAt] using execution.selectedIndexOption_eq_none_iff hp k

end specialized_lift_project_execution

/-- Helper for Theorem 5.24: the nonterminal cuts that appear while the selected index is `j`. -/
def activeCutsAtIndex : Fin p → Set (lift_project_cut n)
  | j =>
      {cut : lift_project_cut n |
        ∃ k : ℕ,
          ¬ has_binary_prefix hp (execution.basic_solution k) ∧
            (execution.selected_index k, execution.generated_cut k) = (j, cut)}

/-- Helper for Theorem 5.24: the active `(selected index, generated cut)` pairs arising at
nonterminal stages. -/
def activeCutPairs : Set (Fin p × lift_project_cut n) :=
  {pair : Fin p × lift_project_cut n |
    ∃ k : ℕ,
      ¬ has_binary_prefix hp (execution.basic_solution k) ∧
        pair = (execution.selected_index k, execution.generated_cut k)}

/-- Helper for Theorem 5.24: a nonstopping stage is exactly a stage whose basic solution still
violates the binary-prefix condition. -/
theorem not_has_binary_prefix_of_not_stopsAt
    {k : ℕ} (hk : ¬ execution.StopsAt hp k) :
    ¬ has_binary_prefix hp (execution.basic_solution k) := by
  -- Unfold the stopping predicate so the contradiction hypothesis matches the active-cut API.
  simpa [specialized_lift_project_execution.StopsAt] using hk

/-- Helper for Theorem 5.24: every nonstopping stage contributes its selected index and generated
cut to the active-pair set. -/
theorem mem_activeCutPairs_of_not_stopsAt
    {k : ℕ} (hk : ¬ execution.StopsAt hp k) :
    (execution.selected_index k, execution.generated_cut k) ∈ activeCutPairs hp execution := by
  -- Package the current stage itself as the witness in the definition of `activeCutPairs`.
  refine ⟨k, not_has_binary_prefix_of_not_stopsAt (hp := hp) (execution := execution) hk, rfl⟩

/-- Helper for Theorem 5.24: the active pairs with a fixed selected index form a finite set. -/
theorem activeCutPairsAtIndexFinite
    (finite_generated_cuts_at_index :
      ∀ j : Fin p, (activeCutsAtIndex hp execution j).Finite)
    (j : Fin p) :
    (Prod.mk j '' activeCutsAtIndex hp execution j).Finite := by
  -- Package each active cut at index `j` with its fixed first coordinate.
  exact (finite_generated_cuts_at_index j).image (Prod.mk j)

/-- Helper for Theorem 5.24: the full set of active `(selected index, generated cut)` pairs is
finite because it is covered by the finite union of the fixed-index active-cut families. -/
theorem activeCutPairsFinite
    (finite_generated_cuts_at_index :
      ∀ j : Fin p, (activeCutsAtIndex hp execution j).Finite) :
    (activeCutPairs hp execution).Finite := by
  -- Cover the active-pair set by the finite union over the finitely many binary indices.
  refine Set.Finite.subset
      (s := ⋃ j : Fin p, Prod.mk j '' activeCutsAtIndex hp execution j)
      (Set.finite_iUnion fun j ↦
        activeCutPairsAtIndexFinite (hp := hp) (execution := execution)
          finite_generated_cuts_at_index j)
      ?_
  intro pair hpair
  rcases hpair with ⟨k, hk, hEq⟩
  rw [hEq]
  -- The witness stage contributes to the branch indexed by its own selected index.
  refine Set.mem_iUnion.2 ⟨execution.selected_index k, ?_⟩
  exact ⟨execution.generated_cut k, ⟨k, hk, rfl⟩, rfl⟩

/-- Helper for Theorem 5.24: if the execution never stops, the stage number injects into the
subtype of active `(selected index, generated cut)` pairs. -/
theorem nonstoppingStageToActivePair_injective
    (active_generated_cut_injective :
      ∀ ⦃k₁ k₂ : ℕ⦄,
        ¬ has_binary_prefix hp (execution.basic_solution k₁) →
        ¬ has_binary_prefix hp (execution.basic_solution k₂) →
        execution.generated_cut k₁ = execution.generated_cut k₂ →
        k₁ = k₂)
    (hnever : ∀ k : ℕ, ¬ execution.StopsAt hp k) :
    Function.Injective
      (fun k : ℕ ↦
        (⟨(execution.selected_index k, execution.generated_cut k),
          mem_activeCutPairs_of_not_stopsAt (hp := hp) (execution := execution) (hnever k)⟩ :
          {pair // pair ∈ activeCutPairs hp execution})) := by
  intro k₁ k₂ hEq
  -- Equality in the subtype first identifies the underlying active pairs.
  have hPair :
      (execution.selected_index k₁, execution.generated_cut k₁) =
        (execution.selected_index k₂, execution.generated_cut k₂) := by
    exact congrArg Subtype.val hEq
  have hk₁ :
      ¬ has_binary_prefix hp (execution.basic_solution k₁) :=
    not_has_binary_prefix_of_not_stopsAt (hp := hp) (execution := execution) (hnever k₁)
  have hk₂ :
      ¬ has_binary_prefix hp (execution.basic_solution k₂) :=
    not_has_binary_prefix_of_not_stopsAt (hp := hp) (execution := execution) (hnever k₂)
  -- Project to the second component to recover equality of generated cuts.
  have hCut : execution.generated_cut k₁ = execution.generated_cut k₂ := by
    simpa using congrArg Prod.snd hPair
  exact active_generated_cut_injective hk₁ hk₂ hCut

-- Semantic recall: `Finite.of_injective` and `Set.Finite.of_injOn` match the intended
-- finite-cut-space plus injectivity termination pattern used by the helper and main theorem.
/-- Helper for Theorem 5.24: under the stagewise algorithm clause together with the cut-separation,
active-cut injectivity, and per-index cut finiteness hypotheses used in the termination argument,
the specialized lift-and-project execution stops after finitely many iterations. -/
theorem
    specialized_lift_project_algorithm_terminates_of_cut_injective_of_finite_generated_cuts
    [execution.IsAlgorithm hp c is_optimal_basic_solution_of_stage
      is_optimal_original_solution is_restricted_system
      is_optimal_basic_solution_of_auxiliary_lp is_j_cut_of_auxiliary_solution
      next_stage_adds_cut]
    (current_solution_violates_generated_cut :
      ∀ k,
        ¬ has_binary_prefix hp (execution.basic_solution k) →
          ¬ (execution.generated_cut k).Satisfied (execution.basic_solution k))
    (active_generated_cut_injective :
      ∀ ⦃k₁ k₂ : ℕ⦄,
        ¬ has_binary_prefix hp (execution.basic_solution k₁) →
        ¬ has_binary_prefix hp (execution.basic_solution k₂) →
        execution.generated_cut k₁ = execution.generated_cut k₂ →
        k₁ = k₂)
    (finite_generated_cuts_at_index :
      ∀ j : Fin p,
        Set.Finite
          {cut : lift_project_cut n |
            ∃ k : ℕ,
              ¬ has_binary_prefix hp (execution.basic_solution k) ∧
                (execution.selected_index k, execution.generated_cut k) = (j, cut)}) :
    ∃ T : ℕ,
      execution.StopsAt hp T := by
  classical
  -- Route correction: this Lean theorem already packages the geometric source proof into
  -- finiteness of active cut families and injectivity of active generated cuts.
  have hfiniteGeneratedCutsAtIndex :
      ∀ j : Fin p, (activeCutsAtIndex hp execution j).Finite := by
    intro j
    -- Re-express the given finiteness hypothesis through the helper definition.
    simpa [activeCutsAtIndex] using finite_generated_cuts_at_index j
  by_contra hNoStop
  have hnever : ∀ k : ℕ, ¬ execution.StopsAt hp k := by
    intro k hStop
    exact hNoStop ⟨k, hStop⟩
  have hActivePairsFinite :
      (activeCutPairs hp execution).Finite :=
    activeCutPairsFinite (hp := hp) (execution := execution) hfiniteGeneratedCutsAtIndex
  let stageToActivePair :
      ℕ → {pair // pair ∈ activeCutPairs hp execution} :=
    fun k ↦
      ⟨(execution.selected_index k, execution.generated_cut k),
        mem_activeCutPairs_of_not_stopsAt (hp := hp) (execution := execution) (hnever k)⟩
  -- The nonstopping hypothesis would inject `ℕ` into the finite active-pair space.
  have hInjective : Function.Injective stageToActivePair := by
    exact nonstoppingStageToActivePair_injective (hp := hp) (execution := execution)
      active_generated_cut_injective hnever
  have hActivePairSubtypeFinite :
      Finite {pair // pair ∈ activeCutPairs hp execution} :=
    hActivePairsFinite.to_subtype
  have hImageFinite : (stageToActivePair '' (Set.univ : Set ℕ)).Finite := by
    -- The image lives inside the finite subtype of active pairs.
    refine (Set.finite_univ_iff.2 hActivePairSubtypeFinite).subset ?_
    intro pair hpair
    simp
  have hNatUnivFinite : (Set.univ : Set ℕ).Finite := by
    -- Injectivity transports finiteness of the image back to the stage set.
    refine Set.Finite.of_finite_image (s := Set.univ) (f := stageToActivePair) hImageFinite ?_
    intro k₁ _ k₂ _ hEq
    exact hInjective hEq
  exact Set.infinite_univ (α := ℕ) hNatUnivFinite

/-- Theorem 5.24. The specialized lift-and-project algorithm terminates after a finite number of
iterations for every mixed `0,1` linear program, formalized here as the existence of a terminal
stage for any specialized lift-and-project execution satisfying the textbook stagewise algorithm
clause together with the finite-cut-space and active-cut nonrepetition hypotheses used in the
termination argument. -/
theorem specialized_lift_project_algorithm_terminates
    [execution.IsAlgorithm hp c is_optimal_basic_solution_of_stage
      is_optimal_original_solution is_restricted_system
      is_optimal_basic_solution_of_auxiliary_lp is_j_cut_of_auxiliary_solution
      next_stage_adds_cut]
    (current_solution_violates_generated_cut :
      ∀ k,
        ¬ has_binary_prefix hp (execution.basic_solution k) →
          ¬ (execution.generated_cut k).Satisfied (execution.basic_solution k))
    (active_generated_cut_injective :
      ∀ ⦃k₁ k₂ : ℕ⦄,
        ¬ has_binary_prefix hp (execution.basic_solution k₁) →
        ¬ has_binary_prefix hp (execution.basic_solution k₂) →
        execution.generated_cut k₁ = execution.generated_cut k₂ →
        k₁ = k₂)
    (finite_generated_cuts_at_index :
      ∀ j : Fin p,
        Set.Finite
          {cut : lift_project_cut n |
            ∃ k : ℕ,
              ¬ has_binary_prefix hp (execution.basic_solution k) ∧
                (execution.selected_index k, execution.generated_cut k) = (j, cut)}) :
    ∃ T : ℕ,
      execution.StopsAt hp T := by
  -- The textbook statement is the abstract helper theorem specialized to the current execution.
  simpa using
    specialized_lift_project_algorithm_terminates_of_cut_injective_of_finite_generated_cuts
      (hp := hp) (execution := execution) (c := c)
      (is_optimal_basic_solution_of_stage := is_optimal_basic_solution_of_stage)
      (is_optimal_original_solution := is_optimal_original_solution)
      (is_restricted_system := is_restricted_system)
      (is_optimal_basic_solution_of_auxiliary_lp := is_optimal_basic_solution_of_auxiliary_lp)
      (is_j_cut_of_auxiliary_solution := is_j_cut_of_auxiliary_solution)
      (next_stage_adds_cut := next_stage_adds_cut)
      current_solution_violates_generated_cut active_generated_cut_injective
      finite_generated_cuts_at_index

end Theorem524

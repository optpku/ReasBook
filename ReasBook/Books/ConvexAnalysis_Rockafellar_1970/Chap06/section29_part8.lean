/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section07_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section13_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section13_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section19_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section14_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section29_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section29_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section29_part5

open scoped Pointwise

section Chap06
section Section29

local notation "ConvexBifunction" => BundledConvexBifunction

/-- Helper for Lemma 6.29.10: when `r = m`, every branch in the constraint set definition is the
inequality branch. -/
lemma helperForLemma_6_29_10_constraintSet_eq_allInequalities
    {m n : ℕ} (P : IndexedOrdinaryConvexProgram m n)
    (hInequalityCount : P.inequalityCount = m) (u : Fin m → ℝ) :
    ordinaryConvexProgramConstraintSet P u =
      {x : Fin n → ℝ | ∀ i : Fin m, P.constraint i x ≤ u i} := by
  ext x
  constructor
  · rintro hx i
    -- Under `r = m`, each coordinate uses the inequality side of the definition.
    simpa [ordinaryConvexProgramConstraintSet, hInequalityCount, i.is_lt] using hx i
  · rintro hx i
    -- The converse is the same simplification read in the reverse direction.
    simpa [ordinaryConvexProgramConstraintSet, hInequalityCount, i.is_lt] using hx i

/-- Helper for Lemma 6.29.10: every metric neighborhood of the origin in `Fin m → ℝ` contains a
constant vector with all coordinates strictly negative. -/
lemma helperForLemma_6_29_10_exists_negativeConstantVector_in_ball
    {m : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ((fun _ : Fin m => -δ) : Fin m → ℝ) ∈ Metric.ball (0 : Fin m → ℝ) ε := by
  let oneVec : Fin m → ℝ := fun _ => 1
  let N : ℝ := ‖oneVec‖
  let δ : ℝ := ε / (2 * (N + 1))
  have hN_nonneg : 0 ≤ N := by
    -- Norms are nonnegative.
    simp [N]
  have hN1_pos : 0 < N + 1 := by
    linarith
  have hdenom_pos : 0 < 2 * (N + 1) := by
    positivity
  have hδ_pos : 0 < δ := by
    -- The chosen constant is a positive fraction of the ball radius.
    exact div_pos hε hdenom_pos
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
  have hN_le : N ≤ N + 1 := by
    linarith
  have hmul_le : δ * N ≤ δ * (N + 1) := by
    exact mul_le_mul_of_nonneg_left hN_le hδ_nonneg
  have hdelta_mul : δ * (N + 1) = ε / 2 := by
    -- Multiplying back by `N + 1` leaves the usual `ε / 2` margin.
    have hN1_ne : N + 1 ≠ 0 := ne_of_gt hN1_pos
    dsimp [δ]
    field_simp [hN1_ne]
  have hhalf_lt : ε / 2 < ε := by
    linarith
  have hnorm_lt : δ * N < ε := by
    have hle : δ * N ≤ ε / 2 := by
      simpa [hdelta_mul] using hmul_le
    exact lt_of_le_of_lt hle hhalf_lt
  have hvec_eq : ((fun _ : Fin m => -δ) : Fin m → ℝ) = (-δ) • oneVec := by
    -- A constant function is the scalar multiple of the all-ones vector.
    ext i
    simp [oneVec]
  have hball :
      ((fun _ : Fin m => -δ) : Fin m → ℝ) ∈ Metric.ball (0 : Fin m → ℝ) ε := by
    -- The norm estimate places the constant negative vector inside the radius-`ε` ball.
    rw [Metric.mem_ball, dist_eq_norm]
    calc
      ‖((fun _ : Fin m => -δ) : Fin m → ℝ) - 0‖
          = ‖((fun _ : Fin m => -δ) : Fin m → ℝ)‖ := by simp
      _ = ‖(-δ : ℝ) • oneVec‖ := by rw [hvec_eq]
      _ = ‖(-δ : ℝ)‖ * ‖oneVec‖ := by rw [norm_smul]
      _ = δ * N := by
        simp [Real.norm_eq_abs, N, abs_of_nonneg hδ_nonneg]
      _ < ε := hnorm_lt
  exact ⟨δ, hδ_pos, hball⟩

/-- Helper for Lemma 6.29.10: a point with all constraints strictly negative certifies an open
upper neighborhood of perturbations inside the effective domain. -/
lemma helperForLemma_6_29_10_strictUpperNeighborhood_subset_effectiveDomain
    {m n : ℕ} (P : IndexedOrdinaryConvexProgram m n)
    (hInequalityCount : P.inequalityCount = m) {x : Fin n → ℝ}
    (hx : x ∈ ordinaryConvexProgramObjectiveDomain P) :
    {u : Fin m → ℝ | ∀ i : Fin m, P.constraint i x < u i} ⊆
      bifunctionEffectiveDomain (ordinaryConvexProgramAssociatedBifunction P) := by
  intro u hu
  -- Rewrite `dom F` as the perturbations whose feasible slice meets the objective domain.
  rw [ordinaryConvexProgramAssociatedBifunction_dom_eq_nonempty_inter_dom_objective]
  refine ⟨x, ?_⟩
  constructor
  · -- The fixed witness `x` satisfies every perturbed inequality because `<` implies `≤`.
    rw [helperForLemma_6_29_10_constraintSet_eq_allInequalities
      (P := P) hInequalityCount u]
    intro i
    exact (hu i).le
  · -- The witness remains in the objective domain by hypothesis.
    exact hx

/-- Lemma 6.29.10: When `(P)` is an ordinary convex program with `r = m`, so that all
constraints are inequalities, `(P)` is strictly consistent if and only if there exists
`x ∈ C`, where `C = dom f₀`, such that `f_i(x) < 0` for every constraint index `i`. -/
theorem ordinaryConvexProgram_strictlyConsistent_iff_exists_point_in_objectiveDomain_of_all_constraints
    {m n : ℕ} (P : IndexedOrdinaryConvexProgram m n) (hInequalityCount : P.inequalityCount = m) :
    ordinaryConvexProgramStrictlyConsistent P ↔
      ∃ x : Fin n → ℝ,
        x ∈ ordinaryConvexProgramObjectiveDomain P ∧
          ∀ i : Fin m, P.constraint i x < 0 := by
  constructor
  · intro hStrict
    have hInterior :
        (0 : Fin m → ℝ) ∈
          interior (bifunctionEffectiveDomain (ordinaryConvexProgramAssociatedBifunction P)) := by
      -- Unfold strict consistency to the interior statement on the perturbation domain.
      simpa [ordinaryConvexProgramStrictlyConsistent] using hStrict
    rcases Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hInterior) with
      ⟨ε, hε, hballSubset⟩
    rcases helperForLemma_6_29_10_exists_negativeConstantVector_in_ball (m := m) hε with
      ⟨δ, hδ, huBall⟩
    let u : Fin m → ℝ := fun _ => -δ
    have huDom :
        u ∈ bifunctionEffectiveDomain (ordinaryConvexProgramAssociatedBifunction P) := by
      -- Choose a small constant negative perturbation inside the interior neighborhood.
      exact hballSubset (by simpa [u] using huBall)
    rw [ordinaryConvexProgramAssociatedBifunction_dom_eq_nonempty_inter_dom_objective] at huDom
    rcases huDom with ⟨x, hxFeasible, hxObjective⟩
    have hxConstraintLe : ∀ i : Fin m, P.constraint i x ≤ u i := by
      -- Under `r = m`, feasibility means every constraint is bounded above by the perturbation.
      rw [helperForLemma_6_29_10_constraintSet_eq_allInequalities
        (P := P) hInequalityCount u] at hxFeasible
      exact hxFeasible
    refine ⟨x, hxObjective, ?_⟩
    intro i
    have hle : P.constraint i x ≤ -δ := by
      simpa [u] using hxConstraintLe i
    have hneg : -δ < 0 := by
      linarith
    -- The negative perturbation bound upgrades the nonstrict feasibility inequality to strict
    -- negativity.
    exact lt_of_le_of_lt hle hneg
  · rintro ⟨x, hxObjective, hxConstraint⟩
    let U : Set (Fin m → ℝ) := {u : Fin m → ℝ | ∀ i : Fin m, P.constraint i x < u i}
    have hUopen : IsOpen U := by
      classical
      -- Coordinatewise strict upper bounds form a finite product of open rays.
      have hUeq :
          U = Set.pi (Set.univ : Set (Fin m)) (fun i => Set.Ioi (P.constraint i x)) := by
        ext u
        simp [U]
      rw [hUeq]
      refine isOpen_set_pi (i := (Set.univ : Set (Fin m)))
        (s := fun i => Set.Ioi (P.constraint i x)) Set.finite_univ ?_
      intro i hi
      simpa using isOpen_Ioi
    have h0U : (0 : Fin m → ℝ) ∈ U := by
      -- The given strict inequalities place the origin in this upper neighborhood.
      intro i
      simpa [U] using hxConstraint i
    have hUsubset :
        U ⊆ bifunctionEffectiveDomain (ordinaryConvexProgramAssociatedBifunction P) :=
      -- The same feasible point works for every perturbation in the upper neighborhood.
      helperForLemma_6_29_10_strictUpperNeighborhood_subset_effectiveDomain
        (P := P) hInequalityCount hxObjective
    have hDomNhds :
        bifunctionEffectiveDomain (ordinaryConvexProgramAssociatedBifunction P) ∈
          nhds (0 : Fin m → ℝ) := by
      exact Filter.mem_of_superset (hUopen.mem_nhds h0U) hUsubset
    have hInterior :
        (0 : Fin m → ℝ) ∈
          interior (bifunctionEffectiveDomain (ordinaryConvexProgramAssociatedBifunction P)) :=
      mem_interior_iff_mem_nhds.2 hDomNhds
    -- Folding back the interior statement gives strict consistency.
    simpa [ordinaryConvexProgramStrictlyConsistent] using hInterior

/-- Helper for Lemma 6.29.11: the effective domain of the bifunction associated with an ordinary
convex program is convex. -/
lemma helperForLemma_6_29_11_associatedBifunctionEffectiveDomain_convex
    {m n : ℕ} (P : IndexedOrdinaryConvexProgram m n) :
    Convex ℝ (bifunctionEffectiveDomain (ordinaryConvexProgramAssociatedBifunction P)) := by
  -- Extract the domain-convexity conclusion from Proposition 6.29.2 applied to the associated
  -- bifunction of the program.
  exact
    (proposition_29_2
      (F := ordinaryConvexProgramAssociatedBifunction P)
      (ordinaryConvexProgramAssociatedBifunction_graphFunction_convex P).1).2.2

/-- Lemma 6.29.11: An ordinary convex program `(P)` is strictly consistent if and only if every
perturbation direction can be scaled by some positive factor into the effective domain of its
associated bifunction. Equivalently, for every `u`, there exists `λ > 0` such that
`F (λ • u)` is not the constant function `+∞`. -/
theorem ordinaryConvexProgram_strictlyConsistent_iff_forall_exists_pos_smul_mem_associatedBifunctionEffectiveDomain
    {m n : ℕ} (P : IndexedOrdinaryConvexProgram m n) :
    ordinaryConvexProgramStrictlyConsistent P ↔
      ∀ u : Fin m → ℝ, ∃ ε : ℝ, 0 < ε ∧
        ε • u ∈ bifunctionEffectiveDomain (ordinaryConvexProgramAssociatedBifunction P) := by
  -- Rewrite strict consistency as the origin lying in the interior of the perturbation domain.
  -- Then apply the earlier finite-dimensional convex-set criterion from Chapter 3.
  simpa [ordinaryConvexProgramStrictlyConsistent] using
    (section14_zero_mem_interior_iff_forall_exists_pos_smul_mem
      (E := Fin m → ℝ)
      (C := bifunctionEffectiveDomain (ordinaryConvexProgramAssociatedBifunction P))
      (helperForLemma_6_29_11_associatedBifunctionEffectiveDomain_convex P))

/-- Helper for Theorem 6.29.3: the generalized-program Lagrangian obtained by minimizing
`u ↦ F(u, x) + ⟪u, u*⟫` over perturbations. -/
noncomputable def helperForTheorem_6_29_3_lagrangianOfGeneralizedConvexProgram {m n : ℕ}
    (F : ConvexBifunction m n) : (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun uStar x =>
    sInf (Set.range fun u : Fin m → ℝ => F.1 u x + (((dotProduct u uStar : ℝ) : EReal)))

/-- Helper for Theorem 6.29.3: the saddle inequalities for the generalized-program Lagrangian. -/
def helperForTheorem_6_29_3_isSaddlePointOfGeneralizedConvexProgramLagrangian
    {m n : ℕ} (F : ConvexBifunction m n) (uStar : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  (∀ uStar' : Fin m → ℝ,
      helperForTheorem_6_29_3_lagrangianOfGeneralizedConvexProgram F uStar' x ≤
        helperForTheorem_6_29_3_lagrangianOfGeneralizedConvexProgram F uStar x) ∧
    ∀ x' : Fin n → ℝ,
      helperForTheorem_6_29_3_lagrangianOfGeneralizedConvexProgram F uStar x ≤
        helperForTheorem_6_29_3_lagrangianOfGeneralizedConvexProgram F uStar x'

/-- Helper for Theorem 6.29.3: keeping the primal variable fixed convex-combines only the
perturbation coordinate. -/
lemma helperForTheorem_6_29_3_samePrimalPoint_convexCombination
    {m n : ℕ} (u v : Fin m → ℝ) (x : Fin n → ℝ) (a b : ℝ) (hab : a + b = 1) :
    a • (u, x) + b • (v, x) = (a • u + b • v, x) := by
  -- The second coordinate stays fixed because the coefficients sum to `1`.
  refine Prod.ext ?_ ?_
  · ext i
    simp
  · ext i
    have hi : (a + b) * x i = x i := by simp [hab]
    simpa [add_mul] using hi

/-- Helper for Theorem 6.29.3: the fixed-`x` section `u ↦ F(u, x)` is convex, lower
semicontinuous, and never equals `-∞`. -/
lemma helperForTheorem_6_29_3_fixedUSection_closedConvex_neBot
    {m n : ℕ} (F : ConvexBifunction m n) (hclosed : IsClosedBifunction F.1)
    (hproper : IsProperBifunction F.1) (x : Fin n → ℝ) :
    ClosedConvexFunction (fun u : Fin m → ℝ => F.1 u x) ∧
      ∀ u : Fin m → ℝ, F.1 u x ≠ (⊥ : EReal) := by
  let fx : (Fin m → ℝ) → EReal := fun u => F.1 u x
  have hconv : ConvexFunction fx := by
    -- Specialize convexity of the graph function to two points with the same primal coordinate.
    rw [ConvexFunction, ConvexFunctionOn]
    intro p hp q hq a b ha hb hab
    have hgraph := F.2 (p.1, x) (q.1, x) a b ha hb hab
    have hp' : F.1 p.1 x ≤ (p.2 : EReal) := by simpa [fx, epigraph] using hp.2
    have hq' : F.1 q.1 x ≤ (q.2 : EReal) := by simpa [fx, epigraph] using hq.2
    have hmulp :
        ((a : ℝ) : EReal) * F.1 p.1 x ≤ ((a : ℝ) : EReal) * (p.2 : EReal) := by
      exact mul_le_mul_of_nonneg_left hp' (by exact_mod_cast ha)
    have hmulq :
        ((b : ℝ) : EReal) * F.1 q.1 x ≤ ((b : ℝ) : EReal) * (q.2 : EReal) := by
      exact mul_le_mul_of_nonneg_left hq' (by exact_mod_cast hb)
    rw [helperForTheorem_6_29_3_samePrimalPoint_convexCombination
      (u := p.1) (v := q.1) (x := x) (a := a) (b := b) hab, graphFunction] at hgraph
    refine ⟨by trivial, ?_⟩
    exact le_trans hgraph (add_le_add hmulp hmulq)
  have hsectionEpigraphClosed :
      IsClosed (epigraph (S := (Set.univ : Set (Fin m → ℝ))) fx) := by
    have hProjectionU : Continuous fun p : (Fin m → ℝ) × ℝ => p.1 := continuous_fst
    have hProjectionR : Continuous fun p : (Fin m → ℝ) × ℝ => p.2 := continuous_snd
    have hLift :
        Continuous fun p : (Fin m → ℝ) × ℝ => ((p.1, x), p.2) :=
      (hProjectionU.prodMk continuous_const).prodMk hProjectionR
    have hPreimage :
        (fun p : (Fin m → ℝ) × ℝ => ((p.1, x), p.2)) ⁻¹'
            {p : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ | graphFunction F.1 p.1 ≤ (p.2 : EReal)} =
          epigraph (S := (Set.univ : Set (Fin m → ℝ))) fx := by
      ext p
      constructor
      · intro hp
        change ((p.1, x), p.2) ∈
          {q : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ | graphFunction F.1 q.1 ≤ (q.2 : EReal)} at hp
        exact (mem_epigraph_univ_iff (f := fx)).2 (by simpa [fx, graphFunction] using hp)
      · intro hp
        change ((p.1, x), p.2) ∈
          {q : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ | graphFunction F.1 q.1 ≤ (q.2 : EReal)}
        exact (mem_epigraph_univ_iff (f := fx)).1 (by simpa [fx] using hp)
    -- Pull the bifunction epigraph back along the section embedding.
    rw [← hPreimage]
    exact hclosed.preimage hLift
  have hlsc : LowerSemicontinuous fx := by
    -- Closedness of the section epigraph is the lower-semicontinuity statement on `ℝ^m`.
    have hsublevel :
        ∀ α : ℝ, IsClosed {u : Fin m → ℝ | fx u ≤ (α : EReal)} :=
      (lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f := fx)).2.2
        hsectionEpigraphClosed
    exact (lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f := fx)).1.2
      hsublevel
  have hneBot : ∀ u : Fin m → ℝ, F.1 u x ≠ (⊥ : EReal) := by
    intro u
    exact helperForProposition_6_29_3_section_ne_bot_of_properBifunction hproper u x
  -- Combine the convex and closed pieces, then record the `≠ ⊥` sectionwise statement.
  exact ⟨⟨hconv, hlsc⟩, hneBot⟩

/-- Helper for Theorem 6.29.3: addition by a real constant commutes with `sInf` on `EReal`. -/
lemma helperForTheorem_6_29_3_sInf_image_add_right (c : ℝ) (s : Set EReal) :
    sInf ((fun z : EReal => z + (c : EReal)) '' s) = sInf s + (c : EReal) := by
  have h1 : sInf s + (c : EReal) = ⨅ a ∈ s, a + (c : EReal) := by
    have h1' := (OrderIso.map_sInf (section13_addRightOrderIso c) s)
    dsimp [section13_addRightOrderIso] at h1'
    simpa using h1'
  have h2 : sInf ((fun z : EReal => z + (c : EReal)) '' s) = ⨅ a ∈ s, a + (c : EReal) := by
    simpa using (sInf_image (f := fun z : EReal => z + (c : EReal)) (s := s))
  calc
    sInf ((fun z : EReal => z + (c : EReal)) '' s) = ⨅ a ∈ s, a + (c : EReal) := h2
    _ = sInf s + (c : EReal) := by simpa using h1.symm

/-- Helper for Theorem 6.29.3: the generalized-program Lagrangian is `-f_x^*(-u*)` for the
fixed-`x` section `f_x(u) = F(u, x)`. -/
lemma helperForTheorem_6_29_3_lagrangian_eq_neg_fenchelConjugate_neg_fixedUSection
    {m n : ℕ} (F : ConvexBifunction m n) (uStar : Fin m → ℝ) (x : Fin n → ℝ) :
    helperForTheorem_6_29_3_lagrangianOfGeneralizedConvexProgram F uStar x =
      -fenchelConjugate m (fun u : Fin m → ℝ => F.1 u x) (-uStar) := by
  -- Unfold the conjugate and rewrite the negated supremum as the corresponding infimum.
  calc
    helperForTheorem_6_29_3_lagrangianOfGeneralizedConvexProgram F uStar x
        = iInf fun u : Fin m → ℝ => F.1 u x + (((dotProduct u uStar : ℝ) : EReal)) := by
          rw [helperForTheorem_6_29_3_lagrangianOfGeneralizedConvexProgram, sInf_range]
    _ =
        -(iSup fun u : Fin m → ℝ =>
          (((dotProduct u (-uStar) : ℝ) : EReal) - F.1 u x)) := by
            calc
              iInf (fun u : Fin m → ℝ => F.1 u x + (((dotProduct u uStar : ℝ) : EReal))) =
                  iInf (fun u : Fin m → ℝ =>
                    -((((dotProduct u (-uStar) : ℝ) : EReal) - F.1 u x))) := by
                      refine iInf_congr ?_
                      intro u
                      have hneg :=
                        EReal.neg_add
                          (x := -(((dotProduct u uStar : ℝ) : EReal)))
                          (y := -F.1 u x)
                          (Or.inl (by simp))
                          (Or.inl (by simp))
                      simpa [sub_eq_add_neg, dotProduct_neg, add_assoc, add_left_comm, add_comm] using
                        hneg.symm
              _ = -(iSup fun u : Fin m → ℝ =>
                    (((dotProduct u (-uStar) : ℝ) : EReal) - F.1 u x)) := by
                      have hneg :
                          (iSup fun u : Fin m → ℝ =>
                            (((dotProduct u (-uStar) : ℝ) : EReal) - F.1 u x)) =
                              -(iInf fun u : Fin m → ℝ =>
                                -((((dotProduct u (-uStar) : ℝ) : EReal) - F.1 u x))) := by
                                    simpa using
                                      (ereal_iSup_neg_eq_neg_iInf
                                        (fun u : Fin m → ℝ =>
                                          -((((dotProduct u (-uStar) : ℝ) : EReal) - F.1 u x))))
                      have hneg' := congrArg Neg.neg hneg
                      simpa using hneg'.symm
    _ = -fenchelConjugate m (fun u : Fin m → ℝ => F.1 u x) (-uStar) := by
          rw [fenchelConjugate_eq_iSup]

/-- Helper for Theorem 6.29.3: taking the supremum of the Lagrangian over multipliers at a fixed
`x` recovers the unperturbed objective value `F(0, x)`. -/
lemma helperForTheorem_6_29_3_sSup_lagrangian_eq_objectiveAtZero
    {m n : ℕ} (F : ConvexBifunction m n) (hclosed : IsClosedBifunction F.1)
    (hproper : IsProperBifunction F.1) (x : Fin n → ℝ) :
    sSup (Set.range fun uStar : Fin m → ℝ =>
      helperForTheorem_6_29_3_lagrangianOfGeneralizedConvexProgram F uStar x) = F.1 0 x := by
  let fx : (Fin m → ℝ) → EReal := fun u : Fin m → ℝ => F.1 u x
  have hclosedFx : ClosedConvexFunction fx := by
    exact (helperForTheorem_6_29_3_fixedUSection_closedConvex_neBot
      (F := F) hclosed hproper x).1
  have hneBotFx : ∀ u : Fin m → ℝ, fx u ≠ (⊥ : EReal) := by
    exact (helperForTheorem_6_29_3_fixedUSection_closedConvex_neBot
      (F := F) hclosed hproper x).2
  have hbiconj : fenchelConjugate m (fenchelConjugate m fx) = fx := by
    simpa [fx] using
      fenchelConjugate_biconjugate_eq_of_closedConvex
        (n := m) (f := fx) hclosedFx.2 hclosedFx.1 hneBotFx
  have hnegRange :
      Set.range (fun uStar : Fin m → ℝ => -fenchelConjugate m fx (-uStar)) =
        Set.range (fun y : Fin m → ℝ => -fenchelConjugate m fx y) := by
    ext z
    constructor
    · rintro ⟨uStar, rfl⟩
      exact ⟨-uStar, by simp⟩
    · rintro ⟨y, rfl⟩
      exact ⟨-y, by simp⟩
  -- Rewrite the multiplier supremum into the zero-value of the biconjugate.
  have hlagRange :
      Set.range (fun uStar : Fin m → ℝ =>
        helperForTheorem_6_29_3_lagrangianOfGeneralizedConvexProgram F uStar x) =
          Set.range (fun uStar : Fin m → ℝ => -fenchelConjugate m fx (-uStar)) := by
    ext z
    constructor
    · rintro ⟨uStar, rfl⟩
      refine ⟨uStar, ?_⟩
      simpa [fx] using
        helperForTheorem_6_29_3_lagrangian_eq_neg_fenchelConjugate_neg_fixedUSection
          (F := F) (uStar := uStar) (x := x) |>.symm
    · rintro ⟨uStar, rfl⟩
      refine ⟨uStar, ?_⟩
      simpa [fx] using
        helperForTheorem_6_29_3_lagrangian_eq_neg_fenchelConjugate_neg_fixedUSection
          (F := F) (uStar := uStar) (x := x)
  calc
    sSup (Set.range fun uStar : Fin m → ℝ =>
      helperForTheorem_6_29_3_lagrangianOfGeneralizedConvexProgram F uStar x)
        = sSup (Set.range fun uStar : Fin m → ℝ => -fenchelConjugate m fx (-uStar)) := by
            rw [hlagRange]
    _ = sSup (Set.range fun y : Fin m → ℝ => -fenchelConjugate m fx y) := by
          rw [hnegRange]
    _ = iSup (fun y : Fin m → ℝ => -fenchelConjugate m fx y) := by
          rw [sSup_range]
    _ = -(iInf fun y : Fin m → ℝ => fenchelConjugate m fx y) := by
          simpa using (ereal_iSup_neg_eq_neg_iInf (fun y : Fin m → ℝ => fenchelConjugate m fx y))
    _ = fenchelConjugate m (fenchelConjugate m fx) 0 := by
          symm
          simp [fenchelConjugate_zero_eq_neg_iInf]
    _ = fx 0 := by simp [hbiconj]
    _ = F.1 0 x := rfl

/-- Theorem 6.29.3: a multiplier `u*` is a Kuhn--Tucker vector for the generalized convex
program associated with `F` and `x` is an optimal solution if and only if `(u*, x)` is a saddle
point of the generalized-program Lagrangian. -/
theorem kuhnTuckerVector_and_optimalSolution_iff_saddlePointOfGeneralizedConvexProgramLagrangian
    {m n : ℕ} (F : ConvexBifunction m n) (hclosed : IsClosedBifunction F.1)
    (hproper : IsProperBifunction F.1) (uStar : Fin m → ℝ) (x : Fin n → ℝ) :
    (IsKuhnTuckerVector F uStar ∧ x ∈ generalizedConvexProgramOptimalSolutionSet F) ↔
      helperForTheorem_6_29_3_isSaddlePointOfGeneralizedConvexProgramLagrangian F uStar x := by
  let L : (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
    helperForTheorem_6_29_3_lagrangianOfGeneralizedConvexProgram F
  let p : (Fin m → ℝ) → EReal := generalizedConvexProgramPerturbationFunction F
  constructor
  · rintro ⟨huKT, hxOpt⟩
    rcases huKT with ⟨hopt_ne_top, hopt_ne_bot, hKTineq⟩
    have hL_lower :
        ∀ x' : Fin n → ℝ, generalizedConvexProgramOptimalValue F ≤ L uStar x' := by
      intro x'
      -- The Kuhn--Tucker inequality bounds every shifted perturbation value below `L(u*, x')`.
      refine le_sInf ?_
      rintro z ⟨u, rfl⟩
      have hp_le : p u ≤ F.1 u x' := by
        exact sInf_le ⟨x', rfl⟩
      exact le_trans (hKTineq u) (by
        simpa [dotProduct_comm, add_assoc, add_left_comm, add_comm] using
          add_le_add_right hp_le (((dotProduct uStar u : ℝ) : EReal)))
    have hL_upper :
        ∀ uStar' : Fin m → ℝ, L uStar' x ≤ generalizedConvexProgramOptimalValue F := by
      intro uStar'
      -- Testing the Lagrangian at `u = 0` collapses it to the primal objective at `x`.
      calc
        L uStar' x ≤ F.1 0 x := by
          exact sInf_le ⟨(0 : Fin m → ℝ), by simp⟩
        _ = generalizedConvexProgramOptimalValue F := by
          simpa [generalizedConvexProgramObjective] using hxOpt.2.1
    have hL_value : L uStar x = generalizedConvexProgramOptimalValue F := by
      -- The saddle value is squeezed between the `u = 0` upper bound and the Kuhn--Tucker lower
      -- bound.
      apply le_antisymm
      · exact hL_upper uStar
      · exact hL_lower x
    refine ⟨?_, ?_⟩
    · intro uStar'
      -- Any other multiplier is bounded above by the same primal optimum at `x`.
      calc
        L uStar' x ≤ generalizedConvexProgramOptimalValue F := hL_upper uStar'
        _ = L uStar x := hL_value.symm
    · intro x'
      -- Every primal point has Lagrangian value at least the optimum under a Kuhn--Tucker vector.
      calc
        L uStar x = generalizedConvexProgramOptimalValue F := hL_value
        _ ≤ L uStar x' := hL_lower x'
  · rintro ⟨hleft, hright⟩
    let c : EReal := L uStar x
    have hc_le_allObjectives : ∀ x' : Fin n → ℝ, c ≤ F.1 0 x' := by
      intro x'
      -- The right saddle inequality plus the `u = 0` test controls the primal objective.
      calc
        c = L uStar x := rfl
        _ ≤ L uStar x' := hright x'
        _ ≤ F.1 0 x' := by
          exact sInf_le ⟨(0 : Fin m → ℝ), by simp⟩
    have hobjective_le_c : F.1 0 x ≤ c := by
      -- The left saddle inequality recovers `F(0, x)` from the multiplier supremum identity.
      calc
        F.1 0 x =
            sSup (Set.range fun uStar' : Fin m → ℝ =>
              helperForTheorem_6_29_3_lagrangianOfGeneralizedConvexProgram F uStar' x) := by
                symm
                exact helperForTheorem_6_29_3_sSup_lagrangian_eq_objectiveAtZero
                  (F := F) hclosed hproper x
        _ ≤ c := by
          refine sSup_le ?_
          rintro z ⟨uStar', rfl⟩
          exact hleft uStar'
    have hc_eq_objective : c = F.1 0 x := by
      exact le_antisymm (hc_le_allObjectives x) hobjective_le_c
    rcases hproper.2 with ⟨p0, hp0_ne_top⟩
    rcases p0 with ⟨u0, x0⟩
    have hpair_lt_top : F.1 u0 x0 < ⊤ := by
      simpa [graphFunction] using lt_top_iff_ne_top.mpr hp0_ne_top
    have hc_lt_top : c < ⊤ := by
      have hle_pair : c ≤ F.1 u0 x0 + (((dotProduct u0 uStar : ℝ) : EReal)) := by
        calc
          c = L uStar x := rfl
          _ ≤ L uStar x0 := hright x0
          _ ≤ F.1 u0 x0 + (((dotProduct u0 uStar : ℝ) : EReal)) := by
            exact sInf_le ⟨u0, rfl⟩
      exact lt_of_le_of_lt hle_pair (by
        simpa using EReal.add_lt_add_right_coe hpair_lt_top (dotProduct u0 uStar))
    have hobjective_eq_optimal :
        F.1 0 x = generalizedConvexProgramOptimalValue F := by
      apply le_antisymm
      · -- Since `c` lies below every objective value, it lies below their infimum.
        have hc_le_opt :
            c ≤ generalizedConvexProgramOptimalValue F := by
          refine le_sInf ?_
          rintro z ⟨x', rfl⟩
          simpa [generalizedConvexProgramObjective] using hc_le_allObjectives x'
        simpa [hc_eq_objective] using hc_le_opt
      · -- The optimal value is always below the displayed objective value.
        have hopt_le :
            generalizedConvexProgramOptimalValue F ≤ F.1 0 x := by
          simpa [generalizedConvexProgramOptimalValue, generalizedConvexProgramObjective] using
            (sInf_le (s := Set.range (generalizedConvexProgramObjective F)) ⟨x, rfl⟩)
        exact hopt_le
    have hx_ne_bot : F.1 0 x ≠ (⊥ : EReal) := by
      exact (helperForTheorem_6_29_3_fixedUSection_closedConvex_neBot
        (F := F) hclosed hproper x).2 0
    have hx_opt : x ∈ generalizedConvexProgramOptimalSolutionSet F := by
      refine ⟨?_, ?_, ?_⟩
      · -- The saddle value is finite above, so the primal objective at `x` is feasible.
        simpa [generalizedConvexProgramFeasibleSet, generalizedConvexProgramObjective,
          hc_eq_objective] using hc_lt_top
      · simpa [generalizedConvexProgramObjective] using hobjective_eq_optimal
      · simpa [generalizedConvexProgramObjective] using hx_ne_bot
    have hshiftObjective :
        ∀ u : Fin m → ℝ,
          sInf (Set.range fun x' : Fin n → ℝ =>
            F.1 u x' + (((dotProduct u uStar : ℝ) : EReal))) =
              generalizedConvexProgramPerturbationFunction F u +
                (((dotProduct u uStar : ℝ) : EReal)) := by
      intro u
      -- Shift the infimum by the constant pairing term.
      let du : ℝ := dotProduct u uStar
      have hImage :
          Set.range (fun x' : Fin n → ℝ => F.1 u x' + (((dotProduct u uStar : ℝ) : EReal))) =
            (fun z : EReal => z + (du : EReal)) '' Set.range (fun x' : Fin n → ℝ => F.1 u x') := by
        ext z
        constructor
        · rintro ⟨x', rfl⟩
          exact ⟨F.1 u x', ⟨x', rfl⟩, rfl⟩
        · rintro ⟨z', ⟨x', rfl⟩, rfl⟩
          exact ⟨x', rfl⟩
      rw [hImage]
      simpa [generalizedConvexProgramPerturbationFunction, du] using
        helperForTheorem_6_29_3_sInf_image_add_right (c := du)
          (s := Set.range fun x' : Fin n → ℝ => F.1 u x')
    have huKT :
        IsKuhnTuckerVector F uStar := by
      refine ⟨?_, ?_, ?_⟩
      · rw [← hobjective_eq_optimal]
        simpa [generalizedConvexProgramObjective, hc_eq_objective] using
          lt_top_iff_ne_top.mp hc_lt_top
      · rw [← hobjective_eq_optimal]
        simpa [generalizedConvexProgramObjective] using hx_ne_bot
      · intro u
        -- Right saddle forces `c` below every shifted slice value, hence below the shifted
        -- perturbation infimum.
        have hc_le_shiftedIInf :
            c ≤ iInf fun x' : Fin n → ℝ =>
              F.1 u x' + (((dotProduct u uStar : ℝ) : EReal)) := by
          refine le_iInf ?_
          intro x'
          calc
            c = L uStar x := rfl
            _ ≤ L uStar x' := hright x'
            _ ≤ F.1 u x' + (((dotProduct u uStar : ℝ) : EReal)) := by
              exact sInf_le ⟨u, rfl⟩
        have hcalc :
            c ≤ generalizedConvexProgramPerturbationFunction F u +
              (((dotProduct u uStar : ℝ) : EReal)) := by
          calc
            c ≤ iInf fun x' : Fin n → ℝ => F.1 u x' + (((dotProduct u uStar : ℝ) : EReal)) :=
              hc_le_shiftedIInf
            _ = sInf (Set.range fun x' : Fin n → ℝ =>
                  F.1 u x' + (((dotProduct u uStar : ℝ) : EReal))) := by
                    rw [sInf_range]
            _ = generalizedConvexProgramPerturbationFunction F u +
                  (((dotProduct u uStar : ℝ) : EReal)) := hshiftObjective u
        simpa [ge_iff_le, dotProduct_comm, hobjective_eq_optimal, hc_eq_objective] using hcalc
    exact ⟨huKT, hx_opt⟩

/-- Helper for Theorem 6.29.4: the Section 29 closure of a convex bifunction, obtained by
closing the graph function and then slicing back to `(u, x)` coordinates. -/
noncomputable abbrev helperForTheorem_6_29_4_coordinateGraphFunction {m n : ℕ}
    (F : ConvexBifunction m n) : (Fin (m + n) → ℝ) → EReal :=
  fun z => F.1 (fun i => z (Fin.castAdd n i)) (fun j => z (Fin.natAdd m j))

/-- Helper for Theorem 6.29.4: the Section 29 closure of a convex bifunction, obtained by
closing the graph function and then slicing back to `(u, x)` coordinates. -/
noncomputable def helperForTheorem_6_29_4_define_section29_bifunctionClosure {m n : ℕ}
    (F : ConvexBifunction m n) : Bifunction m n :=
  fun u x => convexFunctionClosure (helperForTheorem_6_29_4_coordinateGraphFunction F) (Fin.append u x)

/-- Helper for Theorem 6.29.4: the perturbation function of the Section 29 closure. -/
noncomputable def helperForTheorem_6_29_4_closurePerturbationFunction {m n : ℕ}
    (F : ConvexBifunction m n) : (Fin m → ℝ) → EReal :=
  fun u => sInf (Set.range (helperForTheorem_6_29_4_define_section29_bifunctionClosure F u))

/-- Helper for Theorem 6.29.4: the closure perturbation value at `u` is the fiber infimum of the
closed graph function over the first-coordinate fiber above `u`. -/
lemma helperForTheorem_6_29_4_graphClosure_fiberInf_eq_closurePerturbation
    {m n : ℕ} (F : ConvexBifunction m n) (u : Fin m → ℝ) :
    helperForTheorem_6_29_4_closurePerturbationFunction F u =
      sInf {z : EReal | ∃ p : (Fin m → ℝ) × (Fin n → ℝ),
        LinearMap.fst ℝ (Fin m → ℝ) (Fin n → ℝ) p = u ∧
          z = convexFunctionClosure
            (helperForTheorem_6_29_4_coordinateGraphFunction F) (Fin.append p.1 p.2)} := by
  -- Rewrite the slice infimum by packaging every section point as a product point `(u, x)`.
  rw [helperForTheorem_6_29_4_closurePerturbationFunction]
  congr 1
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    -- The section witness `x` gives the product-space witness `(u, x)`.
    exact ⟨(u, x), by simp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    -- Any product-space witness in the `u`-fiber comes from its second coordinate.
    rcases p with ⟨u', x⟩
    simp at hp
    rcases hp with rfl
    exact ⟨x, by
      simp [helperForTheorem_6_29_4_define_section29_bifunctionClosure]⟩

/-- Helper for Theorem 6.29.4: every point of `dom F` remains in the domain of the Section 29
closure because graph closure is pointwise bounded above by the original graph function. -/
lemma helperForTheorem_6_29_4_projection_domain_inclusion_left
    {m n : ℕ} (F : ConvexBifunction m n) :
    bifunctionEffectiveDomain F.1 ⊆
      bifunctionEffectiveDomain
        (helperForTheorem_6_29_4_define_section29_bifunctionClosure F) := by
  intro u hu
  rcases
      (helperForProposition_6_29_2_mem_bifunctionEffectiveDomain_iff_exists_finiteSectionValue
        (F := F.1) (u := u)).1 hu with
    ⟨x, hx⟩
  rw [helperForProposition_6_29_2_mem_bifunctionEffectiveDomain_iff_exists_finiteSectionValue]
  refine ⟨x, ?_⟩
  have hle :
      helperForTheorem_6_29_4_define_section29_bifunctionClosure F u x ≤ F.1 u x := by
    -- Evaluate the universal closure bound at the appended point `(u, x)`.
    simpa [helperForTheorem_6_29_4_define_section29_bifunctionClosure,
      helperForTheorem_6_29_4_coordinateGraphFunction] using
      (convexFunctionClosure_le_self
        (f := helperForTheorem_6_29_4_coordinateGraphFunction F) (Fin.append u x))
  -- Finite values of `F` stay finite after passing to the closure.
  exact lt_of_le_of_lt hle hx

/-- Helper for Theorem 6.29.4: repacking `(u, x)` into `Fin (m + n) → ℝ` preserves convexity of
the graph function. -/
lemma helperForTheorem_6_29_4_coordinateGraphFunction_convex
    {m n : ℕ} (F : ConvexBifunction m n) :
    ConvexFunction (helperForTheorem_6_29_4_coordinateGraphFunction F) := by
  rw [ConvexFunction, ConvexFunctionOn]
  intro p hp q hq a b ha hb hab
  have hgraph :
      helperForTheorem_6_29_4_coordinateGraphFunction F (a • p.1 + b • q.1) ≤
        ((a : ℝ) : EReal) *
            helperForTheorem_6_29_4_coordinateGraphFunction F p.1 +
          ((b : ℝ) : EReal) *
            helperForTheorem_6_29_4_coordinateGraphFunction F q.1 := by
    -- Unpack both packed vectors into `(u, x)` coordinates and apply convexity of `F`.
    simpa [helperForTheorem_6_29_4_coordinateGraphFunction, Pi.add_apply, Pi.smul_apply] using
      F.2
        ((fun i => p.1 (Fin.castAdd n i)), (fun j => p.1 (Fin.natAdd m j)))
        ((fun i => q.1 (Fin.castAdd n i)), (fun j => q.1 (Fin.natAdd m j)))
        a b ha hb hab
  have hp' :
      helperForTheorem_6_29_4_coordinateGraphFunction F p.1 ≤ (p.2 : EReal) := by
    simpa [epigraph] using hp.2
  have hq' :
      helperForTheorem_6_29_4_coordinateGraphFunction F q.1 ≤ (q.2 : EReal) := by
    simpa [epigraph] using hq.2
  have hmulp :
      ((a : ℝ) : EReal) * helperForTheorem_6_29_4_coordinateGraphFunction F p.1 ≤
        ((a : ℝ) : EReal) * (p.2 : EReal) := by
    exact mul_le_mul_of_nonneg_left hp' (by exact_mod_cast ha)
  have hmulq :
      ((b : ℝ) : EReal) * helperForTheorem_6_29_4_coordinateGraphFunction F q.1 ≤
        ((b : ℝ) : EReal) * (q.2 : EReal) := by
    exact mul_le_mul_of_nonneg_left hq' (by exact_mod_cast hb)
  have hsum :
      helperForTheorem_6_29_4_coordinateGraphFunction F (a • p.1 + b • q.1) ≤
        ((a : ℝ) : EReal) * (p.2 : EReal) + ((b : ℝ) : EReal) * (q.2 : EReal) :=
    le_trans hgraph (add_le_add hmulp hmulq)
  refine ⟨by trivial, ?_⟩
  simpa [epigraph, smul_eq_mul, add_assoc, add_left_comm, add_comm] using hsum

/-- Helper for Theorem 6.29.4: properness of the bifunction graph is unchanged by packing the
product coordinates into `Fin (m + n) → ℝ`. -/
lemma helperForTheorem_6_29_4_coordinateGraphFunction_proper
    {m n : ℕ} (F : ConvexBifunction m n) (hproper : IsProperBifunction F.1) :
    ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
      (helperForTheorem_6_29_4_coordinateGraphFunction F) := by
  rw [properConvexFunctionOn_iff_effectiveDomain_nonempty_finite]
  refine ⟨?_, ?_, ?_⟩
  · -- The packed graph function is convex because it is just the original graph function in new
    -- coordinates.
    simpa [ConvexFunction] using
      helperForTheorem_6_29_4_coordinateGraphFunction_convex F
  · rcases hproper.2 with ⟨p, hp⟩
    refine ⟨Fin.append p.1 p.2, ?_⟩
    -- A finite graph witness for `F` becomes a finite witness for the packed graph.
    rw [effectiveDomain_eq]
    refine ⟨by simp, ?_⟩
    exact lt_top_iff_ne_top.mpr (by
      simpa [helperForTheorem_6_29_4_coordinateGraphFunction] using hp)
  · intro z hz
    constructor
    · -- The global `≠ ⊥` branch of properness is coordinate-free.
      have hneBot :
          graphFunction F.1
              ((fun i => z (Fin.castAdd n i)), (fun j => z (Fin.natAdd m j))) ≠
            (⊥ : EReal) :=
        hproper.1 ((fun i => z (Fin.castAdd n i)), (fun j => z (Fin.natAdd m j)))
      simpa [helperForTheorem_6_29_4_coordinateGraphFunction] using hneBot
    · -- Effective-domain membership exactly says the packed graph value is different from `⊤`.
      exact mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin (m + n) → ℝ)))
        (f := helperForTheorem_6_29_4_coordinateGraphFunction F) hz

/-- Helper for Theorem 6.29.4: translating a proper convex function preserves properness. -/
lemma helperForTheorem_6_29_4_translate_properConvexFunctionOn
    {k : ℕ} {g : (Fin k → ℝ) → EReal}
    (hgproper : ProperConvexFunctionOn (Set.univ : Set (Fin k → ℝ)) g)
    (a : Fin k → ℝ) :
    ProperConvexFunctionOn (Set.univ : Set (Fin k → ℝ)) (fun z => g (z + a)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Translate each epigraph witness by the fixed vector `a` and reuse convexity of `g`.
    rw [ConvexFunctionOn]
    have hconv : ConvexFunctionOn (Set.univ : Set (Fin k → ℝ)) g := hgproper.1
    rw [ConvexFunctionOn] at hconv
    intro p hp q hq α β hα hβ hsum
    have hp' : (p.1 + a, p.2) ∈ epigraph (S := (Set.univ : Set (Fin k → ℝ))) g := by
      rw [mem_epigraph_univ_iff]
      rw [mem_epigraph_univ_iff] at hp
      simpa using hp
    have hq' : (q.1 + a, q.2) ∈ epigraph (S := (Set.univ : Set (Fin k → ℝ))) g := by
      rw [mem_epigraph_univ_iff]
      rw [mem_epigraph_univ_iff] at hq
      simpa using hq
    have hmain := hconv hp' hq' hα hβ hsum
    refine ⟨by trivial, ?_⟩
    have happ :
        α • a + (α • p.1 + (β • a + β • q.1)) = a + (α • p.1 + β • q.1) := by
      ext i
      simp [Pi.add_apply, Pi.smul_apply]
      have hcoeff : α * a i + a i * β = a i := by
        calc
          α * a i + a i * β = (α + β) * a i := by ring
          _ = a i := by simp [hsum]
      linarith
    simpa [mem_epigraph_univ_iff, happ, Pi.add_apply, Pi.smul_apply,
      add_assoc, add_left_comm, add_comm] using hmain.2
  · -- Shift a single epigraph witness of `g` back by `a`.
    rcases hgproper.2.1 with ⟨p, hp⟩
    refine ⟨(p.1 - a, p.2), ?_⟩
    rw [mem_epigraph_univ_iff] at hp ⊢
    simpa [sub_eq_add_neg, add_assoc] using hp
  · -- The global `≠ ⊥` part of properness is invariant under translation.
    intro x _
    exact hgproper.2.2 (x + a) (by simp)

/-- Helper for Theorem 6.29.4: translating a proper convex function commutes with convex
closure. -/
lemma helperForTheorem_6_29_4_translate_convexFunctionClosure_eq
    {k : ℕ} {g : (Fin k → ℝ) → EReal}
    (hgproper : ProperConvexFunctionOn (Set.univ : Set (Fin k → ℝ)) g)
    (a : Fin k → ℝ) :
    convexFunctionClosure (fun z => g (z + a)) = fun z => convexFunctionClosure g (z + a) := by
  let clg : (Fin k → ℝ) → EReal := convexFunctionClosure g
  let e : (Fin k → ℝ) × ℝ ≃ᵃ[ℝ] (Fin k → ℝ) × ℝ :=
    (AffineEquiv.constVAdd ℝ (Fin k → ℝ) (-a)).prodCongr (AffineEquiv.refl ℝ ℝ)
  have hTranslateEpigraph :
      epigraph (S := (Set.univ : Set (Fin k → ℝ))) (fun z => g (z + a)) =
        e '' epigraph (S := (Set.univ : Set (Fin k → ℝ))) g := by
    ext p
    constructor
    · intro hp
      rw [mem_epigraph_univ_iff] at hp
      refine ⟨(p.1 + a, p.2), ?_, ?_⟩
      · rw [mem_epigraph_univ_iff]
        simpa using hp
      · ext <;> simp [e]
    · rintro ⟨q, hq, rfl⟩
      rw [mem_epigraph_univ_iff] at hq ⊢
      simpa [e, add_assoc] using hq
  have hclgproper : ProperConvexFunctionOn (Set.univ : Set (Fin k → ℝ)) clg :=
    (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
      (f := g) hgproper).1.2
  have hclgclosed : ClosedConvexFunction clg :=
    (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
      (f := g) hgproper).1.1
  have hTranslateClosureEpigraph :
      epigraph (S := (Set.univ : Set (Fin k → ℝ))) (fun z => clg (z + a)) =
        e '' epigraph (S := (Set.univ : Set (Fin k → ℝ))) clg := by
    ext p
    constructor
    · intro hp
      rw [mem_epigraph_univ_iff] at hp
      refine ⟨(p.1 + a, p.2), ?_, ?_⟩
      · rw [mem_epigraph_univ_iff]
        simpa using hp
      · ext <;> simp [e]
    · rintro ⟨q, hq, rfl⟩
      rw [mem_epigraph_univ_iff] at hq ⊢
      simpa [e, add_assoc] using hq
  have hbot : ∀ x, g x ≠ (⊥ : EReal) := by
    -- Proper convex functions are everywhere strictly above `⊥`.
    intro x
    exact hgproper.2.2 x (by simp)
  have hClosureEpigraph :
      epigraph (S := (Set.univ : Set (Fin k → ℝ))) clg =
        closure (epigraph (S := (Set.univ : Set (Fin k → ℝ))) g) :=
    (epigraph_convexFunctionClosure_eq_closure_epigraph (f := g) hbot).1
  have hClosedEpigraph :
      IsClosed (epigraph (S := (Set.univ : Set (Fin k → ℝ))) clg) := by
    simp [hClosureEpigraph]
  have hEpigraphClosures :
      closure (epigraph (S := (Set.univ : Set (Fin k → ℝ))) (fun z => g (z + a))) =
        closure (epigraph (S := (Set.univ : Set (Fin k → ℝ))) (fun z => clg (z + a))) := by
    calc
      closure (epigraph (S := (Set.univ : Set (Fin k → ℝ))) (fun z => g (z + a))) =
          closure (e '' epigraph (S := (Set.univ : Set (Fin k → ℝ))) g) := by
            rw [hTranslateEpigraph]
      _ = e '' closure (epigraph (S := (Set.univ : Set (Fin k → ℝ))) g) := by
            simpa using
              (Homeomorph.image_closure e.toHomeomorphOfFiniteDimensional
                (epigraph (S := (Set.univ : Set (Fin k → ℝ))) g)).symm
      _ = e '' epigraph (S := (Set.univ : Set (Fin k → ℝ))) clg := by
            congr 1
            symm
            exact hClosureEpigraph
      _ = epigraph (S := (Set.univ : Set (Fin k → ℝ))) (fun z => clg (z + a)) := by
            rw [hTranslateClosureEpigraph]
      _ = closure (epigraph (S := (Set.univ : Set (Fin k → ℝ))) (fun z => clg (z + a))) := by
            symm
            apply IsClosed.closure_eq
            rw [hTranslateClosureEpigraph]
            exact e.toHomeomorphOfFiniteDimensional.isClosedMap _ hClosedEpigraph
  have hNoBotTranslate : ∀ x, (fun z => g (z + a)) x ≠ (⊥ : EReal) := by
    -- Translate the `≠ ⊥` branch of properness along the fixed shift.
    intro x
    exact hgproper.2.2 (x + a) (by simp)
  have hNoBotClosureTranslate : ∀ x, (fun z => clg (z + a)) x ≠ (⊥ : EReal) := by
    -- The translated closure is also proper because `cl g` is proper.
    intro x
    exact hclgproper.2.2 (x + a) (by simp)
  have hClosureEq :
      convexFunctionClosure (fun z => g (z + a)) =
        convexFunctionClosure (fun z => clg (z + a)) :=
    convexFunctionClosure_eq_of_epigraph_closure_eq
      (f := fun z => g (z + a)) (g := fun z => clg (z + a))
      hNoBotTranslate hNoBotClosureTranslate hEpigraphClosures
  have hclgconv : ConvexFunctionOn (Set.univ : Set (Fin k → ℝ)) clg := by
    simpa [ConvexFunction] using hclgclosed.1
  rw [ConvexFunctionOn] at hclgconv
  have hTranslatedClosureConvex : ConvexFunction (fun z => clg (z + a)) := by
    -- Translate convexity of `cl g` along the same fixed vector.
    rw [ConvexFunction, ConvexFunctionOn]
    intro p hp q hq α β hα hβ hsum
    have hp' : (p.1 + a, p.2) ∈ epigraph (S := (Set.univ : Set (Fin k → ℝ))) clg := by
      rw [mem_epigraph_univ_iff]
      rw [mem_epigraph_univ_iff] at hp
      simpa using hp
    have hq' : (q.1 + a, q.2) ∈ epigraph (S := (Set.univ : Set (Fin k → ℝ))) clg := by
      rw [mem_epigraph_univ_iff]
      rw [mem_epigraph_univ_iff] at hq
      simpa using hq
    have hmain := hclgconv hp' hq' hα hβ hsum
    refine ⟨by trivial, ?_⟩
    have happ :
        α • a + (α • p.1 + (β • a + β • q.1)) = a + (α • p.1 + β • q.1) := by
      ext i
      simp [Pi.add_apply, Pi.smul_apply]
      have hcoeff : α * a i + a i * β = a i := by
        calc
          α * a i + a i * β = (α + β) * a i := by ring
          _ = a i := by simp [hsum]
      linarith
    simpa [mem_epigraph_univ_iff, happ, Pi.add_apply, Pi.smul_apply,
      add_assoc, add_left_comm, add_comm] using hmain.2
  have hTranslatedClosureEpigraphClosed :
      IsClosed (epigraph (S := (Set.univ : Set (Fin k → ℝ))) (fun z => clg (z + a))) := by
    rw [hTranslateClosureEpigraph]
    exact e.toHomeomorphOfFiniteDimensional.isClosedMap _ hClosedEpigraph
  have hTranslatedClosureClosed : ClosedConvexFunction (fun z => clg (z + a)) := by
    refine ⟨hTranslatedClosureConvex, ?_⟩
    rw [lowerSemicontinuous_iff_closed_sublevel]
    intro α
    exact closed_sublevel_of_closed_epigraph
      (f := fun z => clg (z + a)) hTranslatedClosureEpigraphClosed α
  calc
    convexFunctionClosure (fun z => g (z + a)) =
        convexFunctionClosure (fun z => clg (z + a)) := hClosureEq
    _ = (fun z => clg (z + a)) :=
      convexFunctionClosure_eq_of_closedConvexFunction
        (f := fun z => clg (z + a)) hTranslatedClosureClosed hNoBotClosureTranslate
    _ = fun z => convexFunctionClosure g (z + a) := by
      rfl

/-- Helper for Theorem 6.29.4: projecting the effective domain of the packed graph function to
its first block recovers `dom F`. -/
lemma helperForTheorem_6_29_4_projection_coordinateGraphEffectiveDomain
    {m n : ℕ} (F : ConvexBifunction m n) :
    (fun z : Fin (m + n) → ℝ => fun i : Fin m => z (Fin.castAdd n i)) ''
        effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ))
          (helperForTheorem_6_29_4_coordinateGraphFunction F) =
      bifunctionEffectiveDomain F.1 := by
  ext u
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [helperForProposition_6_29_2_mem_bifunctionEffectiveDomain_iff_exists_finiteSectionValue]
    refine ⟨fun j => z (Fin.natAdd m j), ?_⟩
    -- The packed witness `z` directly provides the finite section witness of `F`.
    have hz_ne_top :
        helperForTheorem_6_29_4_coordinateGraphFunction F z ≠ (⊤ : EReal) :=
      mem_effectiveDomain_imp_ne_top
        (S := (Set.univ : Set (Fin (m + n) → ℝ)))
        (f := helperForTheorem_6_29_4_coordinateGraphFunction F) hz
    exact lt_top_iff_ne_top.mpr (by
      simpa [helperForTheorem_6_29_4_coordinateGraphFunction] using hz_ne_top)
  · intro hu
    rcases
        (helperForProposition_6_29_2_mem_bifunctionEffectiveDomain_iff_exists_finiteSectionValue
          (F := F.1) (u := u)).1 hu with
      ⟨x, hx⟩
    refine ⟨Fin.append u x, ?_, ?_⟩
    · -- Repacking the finite section witness puts the packed graph point in the effective domain.
      rw [effectiveDomain_eq]
      refine ⟨by simp, ?_⟩
      simpa [helperForTheorem_6_29_4_coordinateGraphFunction] using hx
    · -- The first block of the packed witness is exactly the original perturbation vector.
      ext i
      simp


end Section29
end Chap06

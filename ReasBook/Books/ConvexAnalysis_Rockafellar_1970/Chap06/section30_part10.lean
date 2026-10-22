/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part9

section Chap06
section Section30

-- Proof sketch: combine Corollary 6.30.2 with the general formulas identifying the closure of a
-- convex function at a point with the liminf there, and the closure of a concave function at a
-- point with the limsup there. The exceptional case is exactly when the primal value is `+∞`
-- and the dual value is `-∞`, i.e. when both `(P)` and `(P*)` are inconsistent.
/-- Helper for Corollary 6.30.3: the spike bifunction supported at the origin in the `u`
variable and ignoring the vacuous `x`-variable. -/
noncomputable def helperForCorollary_6_30_3_originSpikeBifunction :
    (Fin 1 → ℝ) → (Fin 0 → ℝ) → EReal :=
  fun u _ => indicatorFunction ({(0 : Fin 1 → ℝ)} : Set (Fin 1 → ℝ)) u

/-- Helper for Corollary 6.30.3: the origin spike is a closed convex bifunction. -/
lemma helperForCorollary_6_30_3_originSpikeBifunction_closedConvex :
    ClosedConvexBifunction helperForCorollary_6_30_3_originSpikeBifunction := by
  have hSingletonNonempty :
      Set.Nonempty ({(0 : Fin 1 → ℝ)} : Set (Fin 1 → ℝ)) := by
    -- The singleton support contains the origin.
    have hMem : (0 : Fin 1 → ℝ) ∈ ({(0 : Fin 1 → ℝ)} : Set (Fin 1 → ℝ)) := by
      simp
    exact ⟨0, hMem⟩
  have hSingletonClosed :
      IsClosed ({(0 : Fin 1 → ℝ)} : Set (Fin 1 → ℝ)) := by
    -- Singletons are closed in Euclidean space.
    exact isClosed_singleton
  have hSingletonConvex :
      Convex ℝ ({(0 : Fin 1 → ℝ)} : Set (Fin 1 → ℝ)) := by
    -- A singleton is convex.
    exact convex_singleton (0 : Fin 1 → ℝ)
  have hClosedIndicator :
      ClosedConvexFunction
        (indicatorFunction ({(0 : Fin 1 → ℝ)} : Set (Fin 1 → ℝ))) := by
    -- The singleton `{0}` is closed, convex, and nonempty, so its indicator is closed convex.
    have hIndicator :=
      closedConvexFunction_indicator_neg (n := 1)
        (C := ({(0 : Fin 1 → ℝ)} : Set (Fin 1 → ℝ)))
        hSingletonNonempty hSingletonClosed hSingletonConvex
    simpa [Set.neg_singleton] using hIndicator.1
  constructor
  · -- Convexity of the bifunction is convexity of its graph function.
    simpa [ConvexBifunction, helperForCorollary_6_30_3_originSpikeBifunction,
      bifunctionGraphFunction] using hClosedIndicator.1
  · -- Closedness is inherited from the same graph-function identification.
    simpa [helperForCorollary_6_30_3_originSpikeBifunction, bifunctionGraphFunction] using
      hClosedIndicator

/-- Helper for Corollary 6.30.3: the primal perturbation function of the origin spike is exactly
the singleton indicator on `ℝ`. -/
lemma helperForCorollary_6_30_3_originSpikeBifunction_primal_eq_indicatorSingleton :
    convexProgramAssociatedWith helperForCorollary_6_30_3_originSpikeBifunction =
      indicatorFunction ({(0 : Fin 1 → ℝ)} : Set (Fin 1 → ℝ)) := by
  -- With no `x`-variables, taking the infimum over `x` leaves the same indicator function.
  funext u
  simp [convexProgramAssociatedWith, helperForCorollary_6_30_3_originSpikeBifunction,
    indicatorFunction_singleton_simp]

/-- Helper for Corollary 6.30.3: the primal value of the origin spike at `u = 0` is `0`. -/
lemma helperForCorollary_6_30_3_originSpikeBifunction_primalZero_eq_zero :
    convexProgramAssociatedWith helperForCorollary_6_30_3_originSpikeBifunction 0 =
      (0 : EReal) := by
  -- With no `x`-variables, the primal slice is exactly the singleton indicator itself.
  rw [helperForCorollary_6_30_3_originSpikeBifunction_primal_eq_indicatorSingleton]
  simp [indicatorFunction_singleton_simp]

/-- Helper for Corollary 6.30.3: on the punctured neighborhood of the origin, the primal
perturbation value of the origin spike is constantly `⊤`. -/
lemma helperForCorollary_6_30_3_originSpikeBifunction_puncturedLiminf_eq_top :
    Filter.liminf (convexProgramAssociatedWith helperForCorollary_6_30_3_originSpikeBifunction)
        (nhdsWithin (0 : Fin 1 → ℝ) ({0}ᶜ)) =
      (⊤ : EReal) := by
  have hNeZero :
      ∀ᶠ u : Fin 1 → ℝ in nhdsWithin (0 : Fin 1 → ℝ) ({0}ᶜ), u ≠ 0 := by
    -- Membership in the punctured neighborhood already records `u ≠ 0`.
    change ({0}ᶜ : Set (Fin 1 → ℝ)) ∈ nhdsWithin (0 : Fin 1 → ℝ) ({0}ᶜ)
    change ({0}ᶜ : Set (Fin 1 → ℝ)) ∈
      nhds (0 : Fin 1 → ℝ) ⊓ Filter.principal ({0}ᶜ : Set (Fin 1 → ℝ))
    rw [Filter.mem_inf_iff]
    refine ⟨Set.univ, Filter.univ_mem, ({0}ᶜ : Set (Fin 1 → ℝ)), by simp, ?_⟩
    simp
  have hEventuallyTop :
      ∀ᶠ u : Fin 1 → ℝ in nhdsWithin (0 : Fin 1 → ℝ) ({0}ᶜ),
        convexProgramAssociatedWith helperForCorollary_6_30_3_originSpikeBifunction u =
          (⊤ : EReal) := by
    -- On the punctured filter, every point is nonzero, so the singleton indicator takes value
    -- `⊤`.
    refine hNeZero.mono ?_
    intro u hu
    rw [helperForCorollary_6_30_3_originSpikeBifunction_primal_eq_indicatorSingleton]
    simp [indicatorFunction_singleton_simp, hu]
  -- Replace the primal slice by the constant `⊤` function along the punctured filter.
  have hlim := Filter.liminf_congr hEventuallyTop
  simpa using hlim

/-- Helper for Corollary 6.30.3: the dual value at `0` for the origin spike is still `0`. -/
lemma helperForCorollary_6_30_3_originSpikeBifunction_dualZero_eq_zero :
    dualPerturbationFunctionOfConvexProgram
        ⟨helperForCorollary_6_30_3_originSpikeBifunction,
          helperForCorollary_6_30_3_originSpikeBifunction_closedConvex.1⟩ 0 =
      (0 : EReal) := by
  have hSingletonNonempty :
      Set.Nonempty ({(0 : Fin 1 → ℝ)} : Set (Fin 1 → ℝ)) := by
    -- The singleton support contains the origin.
    have hMem : (0 : Fin 1 → ℝ) ∈ ({(0 : Fin 1 → ℝ)} : Set (Fin 1 → ℝ)) := by
      simp
    exact ⟨0, hMem⟩
  have hSingletonClosed :
      IsClosed ({(0 : Fin 1 → ℝ)} : Set (Fin 1 → ℝ)) := by
    -- Singletons are closed in Euclidean space.
    exact isClosed_singleton
  have hSingletonConvex :
      Convex ℝ ({(0 : Fin 1 → ℝ)} : Set (Fin 1 → ℝ)) := by
    -- A singleton is convex.
    exact convex_singleton (0 : Fin 1 → ℝ)
  have hClosureEq :
      convexClosure (convexProgramAssociatedWith helperForCorollary_6_30_3_originSpikeBifunction)
          0 =
        convexProgramAssociatedWith helperForCorollary_6_30_3_originSpikeBifunction 0 := by
    have hClosedPrimal :
        ClosedConvexFunction
          (convexProgramAssociatedWith helperForCorollary_6_30_3_originSpikeBifunction) := by
      -- The primal perturbation function is the same singleton indicator on `ℝ`.
      have hIndicator :=
        closedConvexFunction_indicator_neg (n := 1)
          (C := ({(0 : Fin 1 → ℝ)} : Set (Fin 1 → ℝ)))
          hSingletonNonempty hSingletonClosed hSingletonConvex
      rw [helperForCorollary_6_30_3_originSpikeBifunction_primal_eq_indicatorSingleton]
      simpa [Set.neg_singleton] using hIndicator.1
    have hNoBot :
        ∀ u : Fin 1 → ℝ,
          convexProgramAssociatedWith helperForCorollary_6_30_3_originSpikeBifunction u ≠
            (⊥ : EReal) := by
      -- An indicator function only takes the values `0` and `⊤`.
      intro u
      rw [helperForCorollary_6_30_3_originSpikeBifunction_primal_eq_indicatorSingleton]
      by_cases hu : u = 0
      · simp [indicatorFunction_singleton_simp, hu]
      · simp [indicatorFunction_singleton_simp, hu]
    -- Closed convex functions agree with their convex closure.
    simpa [convexClosure] using
      congrFun
        (convexFunctionClosure_eq_of_closedConvexFunction
          (f := convexProgramAssociatedWith helperForCorollary_6_30_3_originSpikeBifunction)
          hClosedPrimal hNoBot)
        (0 : Fin 1 → ℝ)
  have hDualProgram :
      dualProgramOfConvexProgram
          ⟨helperForCorollary_6_30_3_originSpikeBifunction,
            helperForCorollary_6_30_3_originSpikeBifunction_closedConvex.1⟩ =
        convexClosure
          (convexProgramAssociatedWith helperForCorollary_6_30_3_originSpikeBifunction) 0 :=
    helperForCorollary_6_30_1_dualProgram_eq_convexClosure_primalValue_at_zero
      (F := ⟨helperForCorollary_6_30_3_originSpikeBifunction,
        helperForCorollary_6_30_3_originSpikeBifunction_closedConvex⟩)
  -- Corollary 6.30.2 still returns the closed value `0` at the origin.
  calc
    dualPerturbationFunctionOfConvexProgram
        ⟨helperForCorollary_6_30_3_originSpikeBifunction,
          helperForCorollary_6_30_3_originSpikeBifunction_closedConvex.1⟩ 0 =
      convexClosure
        (convexProgramAssociatedWith helperForCorollary_6_30_3_originSpikeBifunction) 0 :=
      hDualProgram
    _ = convexProgramAssociatedWith helperForCorollary_6_30_3_originSpikeBifunction 0 :=
      hClosureEq
    _ = (0 : EReal) :=
      helperForCorollary_6_30_3_originSpikeBifunction_primalZero_eq_zero

/-- Helper for Corollary 6.30.3: the origin spike satisfies the theorem's consistency
hypothesis. -/
lemma helperForCorollary_6_30_3_originSpikeBifunction_not_both_inconsistent :
    ¬ (convexProgramAssociatedWith helperForCorollary_6_30_3_originSpikeBifunction 0 =
          (⊤ : EReal) ∧
        dualProgramOfConvexProgram
            ⟨helperForCorollary_6_30_3_originSpikeBifunction,
              helperForCorollary_6_30_3_originSpikeBifunction_closedConvex.1⟩ =
          (⊥ : EReal)) := by
  -- The primal value at `0` is already finite, so the exceptional case does not occur.
  intro hBoth
  have hPrimalZero :
      convexProgramAssociatedWith helperForCorollary_6_30_3_originSpikeBifunction 0 =
        (0 : EReal) :=
    helperForCorollary_6_30_3_originSpikeBifunction_primalZero_eq_zero
  have hPrimalNotTop :
      convexProgramAssociatedWith helperForCorollary_6_30_3_originSpikeBifunction 0 ≠
        (⊤ : EReal) := by
    rw [hPrimalZero]
    simp
  exact hPrimalNotTop hBoth.1

/-- Helper for Corollary 6.30.3: the first advertised punctured-limit identity already fails
for the explicit origin-spike witness. -/
lemma helperForCorollary_6_30_3_originSpikeBifunction_refutes_firstConjunct :
    Filter.liminf (convexProgramAssociatedWith helperForCorollary_6_30_3_originSpikeBifunction)
        (nhdsWithin (0 : Fin 1 → ℝ) ({0}ᶜ)) ≠
      dualPerturbationFunctionOfConvexProgram
        ⟨helperForCorollary_6_30_3_originSpikeBifunction,
          helperForCorollary_6_30_3_originSpikeBifunction_closedConvex.1⟩ 0 := by
  -- The punctured liminf is `⊤`, while the dual value at `0` remains `0`.
  rw [helperForCorollary_6_30_3_originSpikeBifunction_puncturedLiminf_eq_top,
    helperForCorollary_6_30_3_originSpikeBifunction_dualZero_eq_zero]
  simp

/-- Helper for Corollary 6.30.3: the full theorem conclusion is false for the explicit
origin-spike witness, so the current punctured-filter signature cannot be repaired locally. -/
lemma helperForCorollary_6_30_3_originSpikeBifunction_refutes_targetConclusion :
    ¬ (Filter.liminf (convexProgramAssociatedWith helperForCorollary_6_30_3_originSpikeBifunction)
          (nhdsWithin (0 : Fin 1 → ℝ) ({0}ᶜ)) =
          dualPerturbationFunctionOfConvexProgram
            ⟨helperForCorollary_6_30_3_originSpikeBifunction,
              helperForCorollary_6_30_3_originSpikeBifunction_closedConvex.1⟩ 0 ∧
        Filter.limsup
            (dualPerturbationFunctionOfConvexProgram
              ⟨helperForCorollary_6_30_3_originSpikeBifunction,
                helperForCorollary_6_30_3_originSpikeBifunction_closedConvex.1⟩)
            (nhdsWithin (0 : Fin 0 → ℝ) ({0}ᶜ)) =
          convexProgramAssociatedWith helperForCorollary_6_30_3_originSpikeBifunction 0) := by
  -- The first conjunct already contradicts the explicit `⊤ ≠ 0` computation.
  intro hConclusion
  exact helperForCorollary_6_30_3_originSpikeBifunction_refutes_firstConjunct hConclusion.1

/-- Helper for Corollary 6.30.3: a bundled closed convex bifunction witness already satisfies the
theorem's side hypothesis while refuting its punctured-filter conclusion. -/
lemma helperForCorollary_6_30_3_exists_closedConvex_counterexample_to_targetStatement :
    ∃ (F : {F : (Fin 1 → ℝ) → (Fin 0 → ℝ) → EReal // ClosedConvexBifunction F}),
      ¬ (convexProgramAssociatedWith F.1 0 = (⊤ : EReal) ∧
          dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ = (⊥ : EReal)) ∧
        ¬ (Filter.liminf (convexProgramAssociatedWith F.1)
              (nhdsWithin (0 : Fin 1 → ℝ) ({0}ᶜ)) =
              dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 ∧
            Filter.limsup (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩)
                (nhdsWithin (0 : Fin 0 → ℝ) ({0}ᶜ)) =
              convexProgramAssociatedWith F.1 0) := by
  -- Bundle the explicit origin-spike witness with its already-proved closed-convex structure.
  refine ⟨⟨helperForCorollary_6_30_3_originSpikeBifunction,
      helperForCorollary_6_30_3_originSpikeBifunction_closedConvex⟩, ?_, ?_⟩
  · -- The spike has primal value `0` at the origin, so the exceptional inconsistent case fails.
    simpa using helperForCorollary_6_30_3_originSpikeBifunction_not_both_inconsistent
  · -- The first punctured-limit identity is already false for this witness.
    simpa using helperForCorollary_6_30_3_originSpikeBifunction_refutes_targetConclusion

/-- Helper for Corollary 6.30.3: the exact punctured-filter theorem shape is not universally
valid already in dimensions `(m, n) = (1, 0)`, because the bundled origin-spike witness satisfies
the side hypothesis while refuting the advertised conclusion. -/
lemma helperForCorollary_6_30_3_targetShape_not_universally_valid :
    ¬ ∀ (F : {F : (Fin 1 → ℝ) → (Fin 0 → ℝ) → EReal // ClosedConvexBifunction F}),
        ¬ (convexProgramAssociatedWith F.1 0 = (⊤ : EReal) ∧
            dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ = (⊥ : EReal)) →
          Filter.liminf (convexProgramAssociatedWith F.1)
              (nhdsWithin (0 : Fin 1 → ℝ) ({0}ᶜ)) =
              dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 ∧
            Filter.limsup (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩)
                (nhdsWithin (0 : Fin 0 → ℝ) ({0}ᶜ)) =
              convexProgramAssociatedWith F.1 0 := by
  intro hUniversal
  rcases helperForCorollary_6_30_3_exists_closedConvex_counterexample_to_targetStatement with
    ⟨F, hSide, hRefutes⟩
  -- Specializing the claimed theorem shape to the bundled counterexample contradicts the witness.
  exact hRefutes (hUniversal F hSide)

/-- Helper for Corollary 6.30.3: the same origin-spike witness shows that the fully polymorphic
punctured-filter theorem shape is not dimension-uniformly valid when specialized to `(1, 0)`. -/
lemma helperForCorollary_6_30_3_globalTargetShape_not_universally_valid :
    ¬ ∀ {m n : ℕ}
        (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F}),
          ¬ (convexProgramAssociatedWith F.1 0 = (⊤ : EReal) ∧
              dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ = (⊥ : EReal)) →
            Filter.liminf (convexProgramAssociatedWith F.1)
                (nhdsWithin (0 : Fin m → ℝ) ({0}ᶜ)) =
                dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 ∧
              Filter.limsup (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩)
                  (nhdsWithin (0 : Fin n → ℝ) ({0}ᶜ)) =
                convexProgramAssociatedWith F.1 0 := by
  intro hUniversal
  rcases helperForCorollary_6_30_3_exists_closedConvex_counterexample_to_targetStatement with
    ⟨F, hSide, hRefutes⟩
  -- The dimension-uniform theorem shape already fails at the packaged `(1, 0)` witness.
  exact hRefutes (hUniversal F hSide)

/-- Helper for Corollary 6.30.3: whenever the primal value function has no `⊥` values, the
Chapter 2 closure formula at the full neighborhood filter identifies the closure value at `0`
with the liminf there. -/
lemma helperForCorollary_6_30_3_primalClosure_eq_liminf_nhds
    {m : ℕ}
    (p : (Fin m → ℝ) → EReal)
    (hNoBot : ∀ u : Fin m → ℝ, p u ≠ (⊥ : EReal)) :
    convexClosure p 0 =
      Filter.liminf p (nhds (0 : Fin m → ℝ)) := by
  -- This is exactly the pointwise identity supplied by Text 7.0.10 under the no-`⊥` hypothesis.
  simpa [convexClosure] using
    (epigraph_convexFunctionClosure_eq_closure_epigraph (f := p) hNoBot).2 (0 : Fin m → ℝ)

/-- Helper for Corollary 6.30.3: the canonical convex closure is always lower semicontinuous,
even in the branch where it collapses to the constant `⊥` function. -/
lemma helperForCorollary_6_30_3_convexClosure_lowerSemicontinuous
    {m : ℕ}
    (p : (Fin m → ℝ) → EReal) :
    LowerSemicontinuous (convexClosure p) := by
  -- Unfold the canonical closure and split according to whether `p` ever attains `⊥`.
  rw [convexClosure, convexFunctionClosure]
  by_cases hNoBot : ∀ x : Fin m → ℝ, p x ≠ (⊥ : EReal)
  · -- In the no-`⊥` branch, the convex closure is the lower semicontinuous hull itself.
    simpa [hNoBot, lowerSemicontinuousHull] using
      (Classical.choose_spec (exists_lowerSemicontinuousHull (n := m) p)).1
  · -- Otherwise the closure collapses to the constant `⊥` function, which is lower
    -- semicontinuous.
    simpa [hNoBot] using (closed_improper_const_bot (n := m)).1.2

/-- Helper for Corollary 6.30.3: the canonical concave closure is always upper semicontinuous,
because it is the negative of a lower semicontinuous convex closure. -/
lemma helperForCorollary_6_30_3_concaveClosure_upperSemicontinuous
    {n : ℕ}
    (g : (Fin n → ℝ) → EReal) :
    UpperSemicontinuous (concaveClosure g) := by
  -- Convert upper semicontinuity of `concaveClosure g` to lower semicontinuity of its negation.
  rw [helperForTheorem_6_30_2_upperSemicontinuous_iff_lowerSemicontinuous_neg]
  have hNegEq :
      (fun x => -concaveClosure g x) =
        fun x => convexClosure (fun z : Fin n → ℝ => -g z) x := by
    -- Negating the concave closure gives the convex closure of the negated function.
    funext x
    simp [concaveClosure_eq_neg_convexClosure_neg]
  rw [hNegEq]
  simpa using
    helperForCorollary_6_30_3_convexClosure_lowerSemicontinuous
      (p := fun z : Fin n → ℝ => -g z)

/-- Helper for Corollary 6.30.3: a function is pointwise below its concave closure, since
negating converts the statement to the usual `convexClosure ≤ self` inequality. -/
lemma helperForCorollary_6_30_3_self_le_concaveClosure
    {n : ℕ}
    (g : (Fin n → ℝ) → EReal) :
    g ≤ concaveClosure g := by
  intro x
  -- Negating the convex-closure minorization yields the concave-closure majorization.
  have hclosure_le :
      convexFunctionClosure (fun z : Fin n → ℝ => -g z) x ≤ -g x :=
    convexFunctionClosure_le_self (f := fun z : Fin n → ℝ => -g z) x
  have hmajor : g x ≤ -convexFunctionClosure (fun z : Fin n → ℝ => -g z) x := by
    exact (EReal.le_neg).2 hclosure_le
  simpa [concaveClosure_eq_neg_convexClosure_neg, convexClosure] using hmajor

/-- Helper for Corollary 6.30.3: a convex function satisfies the full-neighborhood closure
formula at `0` as soon as the exceptional pair `(p 0, cl p 0) = (+∞, -∞)` is excluded. -/
lemma helperForCorollary_6_30_3_convexClosure_eq_liminf_nhds_at_zero_nonexceptional
    {m : ℕ}
    (p : (Fin m → ℝ) → EReal)
    (hConvex : ConvexFunction p)
    (hNonExceptional :
      ¬ (p 0 = (⊤ : EReal) ∧ convexClosure p 0 = (⊥ : EReal))) :
    convexClosure p 0 =
      Filter.liminf p (nhds (0 : Fin m → ℝ)) := by
  by_cases hNoBot : ∀ u : Fin m → ℝ, p u ≠ (⊥ : EReal)
  · -- In the no-`⊥` branch, the global Chapter 2 closure formula applies directly.
    exact helperForCorollary_6_30_3_primalClosure_eq_liminf_nhds (p := p) hNoBot
  · -- In the improper branch, exclude `p 0 = ⊤`, then force the liminf down to `⊥`
    -- by approaching `0` along a segment from a relative-interior `⊥` point.
    rcases not_forall.mp hNoBot with ⟨u0, hu0Bot'⟩
    have hu0Bot : p u0 = (⊥ : EReal) := not_ne_iff.mp hu0Bot'
    have hClosureBot :
        convexFunctionClosure p = fun _ => (⊥ : EReal) :=
      convexFunctionClosure_eq_bot_of_exists_bot (f := p) ⟨u0, hu0Bot⟩
    have hClosureZeroBot :
        convexClosure p 0 = (⊥ : EReal) := by
      simpa [convexClosure] using congrFun hClosureBot (0 : Fin m → ℝ)
    have hZeroNeTop : p 0 ≠ (⊤ : EReal) := by
      intro hTop
      exact hNonExceptional ⟨hTop, hClosureZeroBot⟩
    have hImproper :
        ImproperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) p := by
      refine ⟨by simpa [ConvexFunction] using hConvex, ?_⟩
      intro hProper
      have hbot_lt : (⊥ : EReal) < p u0 :=
        properConvexFunctionOn_univ_imp_bot_lt (f := p) hProper u0
      rw [hu0Bot] at hbot_lt
      exact lt_irrefl _ hbot_lt
    have hWitnessLtZero : ∃ x : Fin m → ℝ, p x < (0 : EReal) := by
      refine ⟨u0, ?_⟩
      simpa [hu0Bot]
    obtain ⟨x, hxri, hxltZero⟩ :=
      exists_lt_on_ri_effectiveDomain_of_convexFunction
        (f := p) hConvex (α := 0) hWitnessLtZero
    have hxbot :
        p x = (⊥ : EReal) := by
      -- Relative-interior points of the effective domain of an improper convex function
      -- necessarily take the value `⊥`.
      exact improperConvexFunctionOn_eq_bot_on_ri_effectiveDomain (f := p) hImproper x hxri
    have hZeroMemDomain :
        (0 : EuclideanSpace Real (Fin m)) ∈
          (fun y : EuclideanSpace Real (Fin m) => (y : Fin m → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin m → ℝ)) p := by
      -- Since `p 0 ≠ ⊤`, the origin lies in the effective domain.
      have hZeroDom :
          (0 : Fin m → ℝ) ∈ effectiveDomain (Set.univ : Set (Fin m → ℝ)) p := by
        rw [effectiveDomain_eq]
        exact ⟨by simp, (lt_top_iff_ne_top).2 hZeroNeTop⟩
      simpa using hZeroDom
    have hZeroClosureDomain :
        (0 : EuclideanSpace Real (Fin m)) ∈
          closure
            ((fun y : EuclideanSpace Real (Fin m) => (y : Fin m → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin m → ℝ)) p) :=
      subset_closure hZeroMemDomain
    have hSegmentTendstoClosure :
        Filter.Tendsto
          (fun t : Real => p ((1 - t) • x + t • (0 : EuclideanSpace Real (Fin m))))
          (nhdsWithin (1 : Real) (Set.Iio (1 : Real)))
          (nhds (convexFunctionClosure p 0)) :=
      (convexFunctionClosure_eq_limit_along_segment (f := p) (x := x) hxri).2
        hImproper (0 : EuclideanSpace Real (Fin m)) hZeroClosureDomain
    have hSegmentTendstoBot :
        Filter.Tendsto
          (fun t : Real => p ((1 - t) • x.ofLp))
          (nhdsWithin (1 : Real) (Set.Iio (1 : Real)))
          (nhds (⊥ : EReal)) := by
      simpa [convexClosure, hClosureBot] using hSegmentTendstoClosure
    have hSegmentLiminfBot :
        Filter.liminf
            (fun t : Real => p ((1 - t) • x.ofLp))
            (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) =
          (⊥ : EReal) := by
      simpa using Filter.Tendsto.liminf_eq hSegmentTendstoBot
    have hSegmentMap :
        Filter.Tendsto
          (fun t : Real => (1 - t) • x.ofLp)
          (nhdsWithin (1 : Real) (Set.Iio (1 : Real)))
          (nhds (0 : Fin m → ℝ)) := by
      -- The coordinate-space segment map is continuous and converges to the endpoint `0`.
      have hcont :
          Continuous (fun t : Real => (1 - t) • x.ofLp) := by
        fun_prop
      have hTendsto :
          Filter.Tendsto (fun t : Real => (1 - t) • x.ofLp) (nhds (1 : Real))
            (nhds (((1 : Real) - 1) • x.ofLp)) :=
        hcont.continuousAt.tendsto
      simpa using tendsto_nhdsWithin_of_tendsto_nhds hTendsto
    have hLiminfLeSegment :
        Filter.liminf p (nhds (0 : Fin m → ℝ)) ≤
          Filter.liminf
            (fun t : Real => p ((1 - t) • x.ofLp))
            (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) :=
      Filter.liminf_le_liminf_of_le hSegmentMap
    have hLiminfBot :
        Filter.liminf p (nhds (0 : Fin m → ℝ)) = (⊥ : EReal) := by
      apply le_antisymm
      · exact le_trans hLiminfLeSegment (by simpa using hSegmentLiminfBot)
      · exact bot_le
    calc
      convexClosure p 0 = (⊥ : EReal) := hClosureZeroBot
      _ = Filter.liminf p (nhds (0 : Fin m → ℝ)) := hLiminfBot.symm

/-- Helper for Corollary 6.30.3: negating the dual perturbation of a convex bifunction gives a
convex function on the dual parameter space. -/
lemma helperForCorollary_6_30_3_negDualPerturbation_is_convex
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F}) :
    ConvexFunction
      (fun xStar : Fin n → ℝ =>
        -dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ xStar) := by
  -- The dual perturbation is the perturbation function of the concave adjoint bifunction.
  simpa [dualPerturbationFunctionOfConvexProgram] using
    (perturbationFunction_concave_and_effectiveDomain_eq_bifunctionDomain
      (G := adjointOfConvexBifunctionAsConcave ⟨F.1, F.2.1⟩)).1

/-- Helper for Corollary 6.30.3: the concave closure satisfies the full-neighborhood limsup
formula at `0` once the exceptional pair `(g 0, cl g 0) = (-∞, +∞)` is excluded. -/
lemma helperForCorollary_6_30_3_concaveClosure_eq_limsup_nhds_at_zero_nonexceptional
    {n : ℕ}
    (g : (Fin n → ℝ) → EReal)
    (hConvexNeg : ConvexFunction (fun x : Fin n → ℝ => -g x))
    (hNonExceptional :
      ¬ (g 0 = (⊥ : EReal) ∧ concaveClosure g 0 = (⊤ : EReal))) :
    concaveClosure g 0 =
      Filter.limsup g (nhds (0 : Fin n → ℝ)) := by
  have hNonExceptionalNeg :
      ¬ ((fun x : Fin n → ℝ => -g x) 0 = (⊤ : EReal) ∧
          convexClosure (fun x : Fin n → ℝ => -g x) 0 = (⊥ : EReal)) := by
    intro hBad
    apply hNonExceptional
    constructor
    · simpa using hBad.1
    · simpa [concaveClosure_eq_neg_convexClosure_neg] using hBad.2
  have hConvexClosure :
      convexClosure (fun x : Fin n → ℝ => -g x) 0 =
        Filter.liminf (fun x : Fin n → ℝ => -g x) (nhds (0 : Fin n → ℝ)) :=
    helperForCorollary_6_30_3_convexClosure_eq_liminf_nhds_at_zero_nonexceptional
      (p := fun x : Fin n → ℝ => -g x) hConvexNeg hNonExceptionalNeg
  have hNegLimsup :
      Filter.liminf (fun x : Fin n → ℝ => -g x) (nhds (0 : Fin n → ℝ)) =
        -Filter.limsup g (nhds (0 : Fin n → ℝ)) := by
    simpa using
      (EReal.liminf_neg (f := nhds (0 : Fin n → ℝ)) (v := g))
  calc
    concaveClosure g 0 = -convexClosure (fun x : Fin n → ℝ => -g x) 0 := by
      simpa [concaveClosure_eq_neg_convexClosure_neg]
    _ = -Filter.liminf (fun x : Fin n → ℝ => -g x) (nhds (0 : Fin n → ℝ)) := by
      rw [hConvexClosure]
    _ = Filter.limsup g (nhds (0 : Fin n → ℝ)) := by
      rw [hNegLimsup]
      simp

/-- Helper for Corollary 6.30.3: the value of a function at a point is always bounded above by
the limsup along the full neighborhood filter at that point. -/
lemma helperForCorollary_6_30_3_value_le_limsup_nhds
    {n : ℕ}
    (g : (Fin n → ℝ) → EReal)
    (x : Fin n → ℝ) :
    g x ≤ Filter.limsup g (nhds x) := by
  -- The base-point value appears along the pure filter at `x`, hence also frequently in `𝓝 x`.
  refine Filter.le_limsup_of_frequently_le' ?_
  refine (Filter.frequently_iff).2 ?_
  intro U hU
  exact ⟨x, mem_of_mem_nhds hU, le_rfl⟩

/-- Helper for Corollary 6.30.3: in the closed improper branch, once some graph point of `F`
attains `⊥`, every dual slice is `⊥`, and the side hypothesis forces the primal value at `0`
to be `⊥` rather than `⊤`. -/
lemma helperForCorollary_6_30_3_nonproper_graphBot_branch
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hNotProper : ¬ ProperConvexBifunction F.1)
    (h_not_both_inconsistent :
      ¬ (convexProgramAssociatedWith F.1 0 = (⊤ : EReal) ∧
        dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ = (⊥ : EReal)))
    (hGraphBot : ∃ u : Fin m → ℝ, ∃ x : Fin n → ℝ, F.1 u x = (⊥ : EReal)) :
    (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ =
        fun _ : Fin n → ℝ => (⊥ : EReal)) ∧
      convexProgramAssociatedWith F.1 0 = (⊥ : EReal) := by
  rcases hGraphBot with ⟨u, x, hBot⟩
  have hDualConst :
      dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ =
        fun _ : Fin n → ℝ => (⊥ : EReal) := by
    -- A single graph-level `⊥` witness collapses every dual slice.
    funext xStar
    exact helperForCorollary_6_30_1_graphBot_forces_dualSlice_eq_bot
      (F := F) (u := u) (x := x) hBot xStar
  have hDualProgramBot :
      dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ = (⊥ : EReal) := by
    -- Evaluate the constant-`⊥` dual perturbation at the origin.
    simpa [dualProgramOfConvexProgram] using congrFun hDualConst (0 : Fin n → ℝ)
  have hPrimalNotTop :
      convexProgramAssociatedWith F.1 0 ≠ (⊤ : EReal) := by
    -- The theorem hypothesis excludes the inconsistent pair `(P), (P*)`.
    intro hTop
    exact h_not_both_inconsistent ⟨hTop, hDualProgramBot⟩
  have hPrimalBot :
      convexProgramAssociatedWith F.1 0 = (⊥ : EReal) := by
    by_cases hZeroSliceBot : ∃ x : Fin n → ℝ, F.1 0 x = (⊥ : EReal)
    · rcases hZeroSliceBot with ⟨x0, hx0⟩
      -- A `⊥` value already in the zero slice forces its infimum to be `⊥`.
      apply le_antisymm
      · exact sInf_le ⟨x0, hx0⟩
      · exact bot_le
    · have hAllZeroSliceTop : ∀ x : Fin n → ℝ, F.1 0 x = (⊤ : EReal) := by
        intro x0
        -- In the closed improper branch, every graph value is either `⊤` or `⊥`.
        rcases
            helperForTheorem_6_30_11_convexGraph_values_top_or_bot_of_closed_not_proper
              (F := F.1) F.2 hNotProper (Fin.append 0 x0) with
          hTop | hBotAtZero
        · simpa [bifunctionGraphFunction] using hTop
        · exact False.elim <| hZeroSliceBot ⟨x0, by simpa [bifunctionGraphFunction] using hBotAtZero⟩
      have hPrimalTop :
          convexProgramAssociatedWith F.1 0 = (⊤ : EReal) := by
        -- If every zero-slice value is `⊤`, then their infimum is `⊤`.
        simp [convexProgramAssociatedWith, hAllZeroSliceTop]
      exact False.elim (hPrimalNotTop hPrimalTop)
  exact ⟨hDualConst, hPrimalBot⟩

/-- Helper for Corollary 6.30.3: if the closed improper bifunction never attains `⊥`, the whole
bifunction collapses to the constant `⊤` branch. -/
lemma helperForCorollary_6_30_3_nonproper_noGraphBot_branch
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hNotProper : ¬ ProperConvexBifunction F.1)
    (hNoGraphBot : ∀ u : Fin m → ℝ, ∀ x : Fin n → ℝ, F.1 u x ≠ (⊥ : EReal)) :
    F.1 = fun _ _ => (⊤ : EReal) := by
  -- Reuse the earlier closed-improper classification from Corollary 6.30.1.
  exact
    helperForCorollary_6_30_1_closedNotProper_noGraphBot_eq_const_top
      (F := F) hNotProper hNoGraphBot

/-- Corollary 6.30.3: let `F` be a closed convex bifunction from `ℝ^m` to `ℝ^n`, and let `(P)`
be the associated convex program. Except in the case where both `(P)` and `(P*)` are
inconsistent, the primal perturbation function `u ↦ inf_x F(u, x)` has limit inferior at `0`
equal to `sup F* 0`, and the dual perturbation function `x* ↦ sup_{u*} F*(x*, u*)` has limit
superior at `0` equal to `inf F 0`, both taken with respect to the full neighborhood filter
`𝓝 0` from the closure formulas of Corollary 6.30.2. -/
theorem corollary_6_30_2_3 {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (h_not_both_inconsistent :
      ¬ (convexProgramAssociatedWith F.1 0 = (⊤ : EReal) ∧
        dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ = (⊥ : EReal))) :
    Filter.liminf (convexProgramAssociatedWith F.1)
        (nhds (0 : Fin m → ℝ)) =
        dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 ∧
      Filter.limsup (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩)
          (nhds (0 : Fin n → ℝ)) =
        convexProgramAssociatedWith F.1 0 := by
  -- Route correction: the punctured-neighborhood version is refuted in this file by the
  -- origin-spike witness, whereas the textbook argument uses the ordinary closure identities at
  -- the full neighborhood filter `𝓝 0`. The present signature follows that original route.
  by_cases hProper : ProperConvexBifunction F.1
  · have hCor := corollary_6_30_2_2 (F := F)
    have hClosurePrimal :
        convexClosure (convexProgramAssociatedWith F.1) 0 =
          dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 :=
      hCor.1
    have hClosureDual :
        concaveClosure (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩) 0 =
          convexProgramAssociatedWith F.1 0 :=
      hCor.2.2.1 hProper
    have hPrimalConvex :
        ConvexFunction (convexProgramAssociatedWith F.1) :=
      helperForTheorem_6_30_15_primalValueFunction_is_convex (F := ⟨F.1, F.2.1⟩)
    have hPrimalNonExceptional :
        ¬ (convexProgramAssociatedWith F.1 0 = (⊤ : EReal) ∧
            convexClosure (convexProgramAssociatedWith F.1) 0 = (⊥ : EReal)) := by
      intro hBad
      apply h_not_both_inconsistent
      constructor
      · exact hBad.1
      · calc
          dualProgramOfConvexProgram ⟨F.1, F.2.1⟩
              = dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 := by
                  rfl
          _ = convexClosure (convexProgramAssociatedWith F.1) 0 := by
                exact hClosurePrimal.symm
          _ = (⊥ : EReal) := hBad.2
    have hPrimalLiminf :
        convexClosure (convexProgramAssociatedWith F.1) 0 =
          Filter.liminf (convexProgramAssociatedWith F.1) (nhds (0 : Fin m → ℝ)) :=
      helperForCorollary_6_30_3_convexClosure_eq_liminf_nhds_at_zero_nonexceptional
        (p := convexProgramAssociatedWith F.1) hPrimalConvex hPrimalNonExceptional
    have hNegDualConvex :
        ConvexFunction
          (fun xStar : Fin n → ℝ =>
            -dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ xStar) :=
      helperForCorollary_6_30_3_negDualPerturbation_is_convex (F := F)
    have hDualNonExceptional :
        ¬ (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 = (⊥ : EReal) ∧
            concaveClosure (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩) 0 =
              (⊤ : EReal)) := by
      intro hBad
      apply h_not_both_inconsistent
      constructor
      · calc
          convexProgramAssociatedWith F.1 0 =
              concaveClosure (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩) 0 := by
                exact hClosureDual.symm
          _ = (⊤ : EReal) := hBad.2
      · simpa [dualProgramOfConvexProgram] using hBad.1
    have hDualLimsup :
        concaveClosure (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩) 0 =
          Filter.limsup (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩)
            (nhds (0 : Fin n → ℝ)) :=
      helperForCorollary_6_30_3_concaveClosure_eq_limsup_nhds_at_zero_nonexceptional
        (g := dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩)
        hNegDualConvex hDualNonExceptional
    constructor
    · -- The primal closure identity at `0` becomes the desired liminf formula.
      calc
        Filter.liminf (convexProgramAssociatedWith F.1) (nhds (0 : Fin m → ℝ)) =
            convexClosure (convexProgramAssociatedWith F.1) 0 := hPrimalLiminf.symm
        _ = dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 := hClosurePrimal
    · -- The dual closure identity at `0` becomes the desired limsup formula.
      calc
        Filter.limsup (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩)
            (nhds (0 : Fin n → ℝ)) =
            concaveClosure (dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩) 0 :=
              hDualLimsup.symm
        _ = convexProgramAssociatedWith F.1 0 := hClosureDual
  · by_cases hGraphBot : ∃ u : Fin m → ℝ, ∃ x : Fin n → ℝ, F.1 u x = (⊥ : EReal)
    · rcases
        helperForCorollary_6_30_3_nonproper_graphBot_branch
          (F := F) hProper h_not_both_inconsistent hGraphBot with
        ⟨hDualConst, hPrimalBot⟩
      constructor
      · -- Since the primal value at `0` is already `⊥`, the liminf there is forced to be `⊥`.
        calc
          Filter.liminf (convexProgramAssociatedWith F.1) (nhds (0 : Fin m → ℝ)) =
              (⊥ : EReal) := by
                apply le_antisymm
                · -- The base point belongs to every neighborhood of `0`, so the value `⊥`
                  -- occurs frequently enough to force the liminf down to `⊥`.
                  refine Filter.liminf_le_of_frequently_le' ?_
                  refine (Filter.frequently_iff).2 ?_
                  intro U hU
                  exact ⟨0, mem_of_mem_nhds hU, by simpa [hPrimalBot]⟩
                · -- The reverse inequality is automatic because `⊥` is the least `EReal`
                  -- value.
                  exact bot_le
          _ = dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ 0 := by
                simpa [hDualConst]
      · -- The dual perturbation is the constant `⊥` function in this branch.
        simpa [hDualConst, hPrimalBot]
    · have hNoGraphBot : ∀ u : Fin m → ℝ, ∀ x : Fin n → ℝ, F.1 u x ≠ (⊥ : EReal) := by
        intro u x hBot
        exact hGraphBot ⟨u, x, hBot⟩
      have hConstTop :
          F.1 = fun _ _ => (⊤ : EReal) :=
        helperForCorollary_6_30_3_nonproper_noGraphBot_branch
          (F := F) hProper hNoGraphBot
      have hPrimalConstTop :
          convexProgramAssociatedWith F.1 = fun _ : Fin m → ℝ => (⊤ : EReal) := by
        funext u
        simp [hConstTop, convexProgramAssociatedWith]
      have hDualConstTop :
          dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ =
            fun _ : Fin n → ℝ => (⊤ : EReal) := by
        funext xStar
        have hAdjTop :
            ∀ uStar : Fin m → ℝ,
              adjointOfConvexBifunction ⟨F.1, F.2.1⟩ xStar uStar = (⊤ : EReal) := by
          intro uStar
          simp [hConstTop, adjointOfConvexBifunction]
        simp [dualPerturbationFunctionOfConvexProgram, concaveProgramAssociatedWith, hAdjTop]
      -- Once `F` is the constant `⊤` bifunction, both perturbation families are constant `⊤`.
      constructor
      · simpa [hPrimalConstTop, hDualConstTop]
      · simpa [hPrimalConstTop, hDualConstTop]
end Section30
end Chap06

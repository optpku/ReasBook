/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section28_part7

open scoped BigOperators Pointwise

section Chap06
section Section28

/-- Helper for Theorem 6.28.3: keep a compatibility wrapper for the older Chapter 21 adapter
name, but route it through the genuine missing multiplier-certificate bridge. -/
lemma helperForTheorem_6_28_3_chapter21_adapter_for_nonaffine_strict_and_affine_weak_blocks
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hoptimal_ne_bot : P.optimalValue ≠ (⊥ : EReal))
    (hstrict_feasible : P.HasStrictFeasiblePointOnNonaffineInequalityIndices) :
    ∃ v : ℝ, ∃ lambda : Fin m → ℝ,
      P.optimalValue = (v : EReal) ∧
        (∀ i : Fin r, 0 ≤ P.inequalityMultipliers lambda i) ∧
          (∀ x : Fin n → ℝ, x ∈ P.constraintSet → v ≤ P.kuhnTuckerObjective lambda x) := by
  -- Route correction: this wrapper now points straight at the real missing certificate theorem,
  -- so downstream uses no longer pretend that a Chapter 21 `ri`-based packaging lemma is the
  -- fundamental blocker.
  exact
    helperForTheorem_6_28_3_exists_multiplierLowerBoundCertificate_of_optimalValue_ne_bot_and_nonaffineStrictFeasibility
      P hoptimal_ne_bot hstrict_feasible

/-- Helper for Theorem 6.28.3: once a multiplier vector globally lower-bounds the ordinary
Kuhn--Tucker objective on `P.constraintSet`, the same multiplier is already a generalized
Kuhn--Tucker vector for the direct perturbation bifunction. -/
lemma helperForTheorem_6_28_3_directPerturbationKuhnTuckerVector_of_multiplierLowerBoundCertificate
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {v : ℝ} {lambda : Fin m → ℝ}
    (hoptimal : P.optimalValue = (v : EReal))
    (hlambda_nonneg : ∀ i : Fin r, 0 ≤ P.inequalityMultipliers lambda i)
    (hobjective_lower :
      ∀ x : Fin n → ℝ, x ∈ P.constraintSet → v ≤ P.kuhnTuckerObjective lambda x) :
    IsKuhnTuckerVector (helperForTheorem_6_28_3_directPerturbationConvexBifunction P) lambda := by
  let F := helperForTheorem_6_28_3_directPerturbationConvexBifunction P
  have hKT_P : P.IsKuhnTuckerVector lambda := by
    -- The lower bound makes `v` a common lower bound for all Kuhn--Tucker objective values on
    -- the ambient constraint set.
    have hsinf_lower :
        (v : EReal) ≤
          sInf ((fun x => ((P.kuhnTuckerObjective lambda x : ℝ) : EReal)) '' P.constraintSet) := by
      refine le_sInf ?_
      rintro _ ⟨x, hx, rfl⟩
      exact EReal.coe_le_coe_iff.2 (hobjective_lower x hx)
    -- Feasible points still bound the Kuhn--Tucker objective above by the primal objective.
    have hsinf_upper :
        sInf ((fun x => ((P.kuhnTuckerObjective lambda x : ℝ) : EReal)) '' P.constraintSet) ≤
          P.optimalValue := by
      rw [BookOrdinaryConvexProgram.optimalValue]
      refine le_sInf ?_
      rintro _ ⟨x, hxFeas, rfl⟩
      have hsinf_le_x :
          sInf ((fun y => ((P.kuhnTuckerObjective lambda y : ℝ) : EReal)) '' P.constraintSet) ≤
            ((P.kuhnTuckerObjective lambda x : ℝ) : EReal) := by
        exact sInf_le ⟨x, hxFeas.1, rfl⟩
      have hkuhn_le_obj :
          ((P.kuhnTuckerObjective lambda x : ℝ) : EReal) ≤ ((P.objective x : ℝ) : EReal) := by
        exact_mod_cast
          helperForTheorem_6_28_1_kuhnTuckerObjective_le_objective_of_feasible
            P lambda hxFeas hlambda_nonneg
      exact le_trans hsinf_le_x hkuhn_le_obj
    -- Identifying the infimum with `v = P.optimalValue` gives the ordinary Kuhn--Tucker
    -- certificate.
    have hsinf_eq_v :
        sInf ((fun x => ((P.kuhnTuckerObjective lambda x : ℝ) : EReal)) '' P.constraintSet) =
          (v : EReal) := by
      apply le_antisymm
      · calc
          sInf ((fun x => ((P.kuhnTuckerObjective lambda x : ℝ) : EReal)) '' P.constraintSet) ≤
              P.optimalValue := hsinf_upper
          _ = (v : EReal) := hoptimal
      · exact hsinf_lower
    exact ⟨hlambda_nonneg, v, hsinf_eq_v, hoptimal⟩
  have hp0_finite : ∃ p0 : ℝ, P.perturbationFunction 0 = (p0 : EReal) := by
    -- The certificate identifies the perturbation value at the origin with the same real number
    -- `v`.
    refine ⟨v, ?_⟩
    calc
      P.perturbationFunction 0 = P.optimalValue :=
        helperForTheorem_6_28_2_perturbationFunction_zero_eq_optimalValue P
      _ = (v : EReal) := hoptimal
  have hsupportP :
      ∀ u : Fin m → ℝ,
        P.perturbationFunction u + (((∑ i : Fin m, lambda i * u i) : ℝ) : EReal) ≥
          P.perturbationFunction 0 :=
    (isKuhnTuckerVector_iff_perturbationFunction_lower_bound P lambda hp0_finite).1 hKT_P
  have hperturb :
      generalizedConvexProgramPerturbationFunction F = P.perturbationFunction := by
    simpa [F] using helperForTheorem_6_28_3_generalizedPerturbationFunction_eq_perturbationFunction P
  have hfinite :
      IsFiniteEReal (generalizedConvexProgramOptimalValue F) := by
    have hoptimalF :
        generalizedConvexProgramOptimalValue F = (v : EReal) := by
      calc
        generalizedConvexProgramOptimalValue F = P.optimalValue :=
          helperForTheorem_6_28_3_directPerturbationOptimalValue_eq_optimalValue P
        _ = (v : EReal) := hoptimal
    refine ⟨?_, ?_⟩
    · intro htop
      have : (v : EReal) = (⊤ : EReal) := by
        calc
          (v : EReal) = generalizedConvexProgramOptimalValue F := hoptimalF.symm
          _ = (⊤ : EReal) := htop
      simp at this
    · intro hbot
      have : (v : EReal) = (⊥ : EReal) := by
        calc
          (v : EReal) = generalizedConvexProgramOptimalValue F := hoptimalF.symm
          _ = (⊥ : EReal) := hbot
      simp at this
  have hsupportF :
      ∀ u : Fin m → ℝ,
        generalizedConvexProgramPerturbationFunction F u +
            (((dotProduct lambda u : ℝ)) : EReal) ≥
          generalizedConvexProgramPerturbationFunction F 0 := by
    -- Rewrite the textbook perturbation support inequality for the direct generalized program.
    intro u
    simpa [hperturb, dotProduct] using hsupportP u
  have hsubF :
      -lambda ∈ euclideanSubdifferentialAt
        (generalizedConvexProgramPerturbationFunction F) 0 :=
    (helperForTheorem_6_29_1_neg_mem_euclideanSubdifferentialAt_zero_iff_supporting_inequality
      (h := generalizedConvexProgramPerturbationFunction F) lambda).2 hsupportF
  -- The Section 29 subgradient criterion turns that support inequality into the generalized
  -- Kuhn--Tucker vector for the direct perturbation bifunction.
  exact
    ((generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).2.2
      hfinite lambda).2 hsubF

/-- Helper for Theorem 6.28.3: any generalized Kuhn--Tucker vector for the direct perturbation
bifunction already yields a Euclidean subgradient of the direct perturbation function at the
origin. -/
lemma helperForTheorem_6_28_3_subdifferentialNonemptyAt_directPerturbationFunction_zero_of_directPerturbationKuhnTuckerVector
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hoptimal_ne_bot : P.optimalValue ≠ (⊥ : EReal))
    (hstrict_feasible : P.HasStrictFeasiblePointOnNonaffineInequalityIndices)
    {lambda : Fin m → ℝ}
    (hKT_F :
      IsKuhnTuckerVector (helperForTheorem_6_28_3_directPerturbationConvexBifunction P) lambda) :
    Set.Nonempty
      (euclideanSubdifferentialAt
        (generalizedConvexProgramPerturbationFunction
          (helperForTheorem_6_28_3_directPerturbationConvexBifunction P)) 0) := by
  let F := helperForTheorem_6_28_3_directPerturbationConvexBifunction P
  have hfinite :
      IsFiniteEReal (generalizedConvexProgramOptimalValue F) :=
    helperForTheorem_6_28_3_directPerturbationOptimalValue_finite
      P hoptimal_ne_bot hstrict_feasible
  -- Section 29 identifies generalized Kuhn--Tucker vectors with Euclidean subgradients of the
  -- direct perturbation function at the origin.
  exact
    ⟨-lambda,
      ((generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).2.2 hfinite
        lambda).1 hKT_F⟩

/-- Helper for Theorem 6.28.3: once the blocked multiplier lower-bound certificate is available,
the direct perturbation generalized program already has a Euclidean subgradient at the
origin. -/
lemma helperForTheorem_6_28_3_subdifferentialNonemptyAt_directPerturbationFunction_zero_of_optimalValue_ne_bot_and_nonaffineStrictFeasibility
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hoptimal_ne_bot : P.optimalValue ≠ (⊥ : EReal))
    (hstrict_feasible : P.HasStrictFeasiblePointOnNonaffineInequalityIndices) :
    Set.Nonempty
      (euclideanSubdifferentialAt
        (generalizedConvexProgramPerturbationFunction
          (helperForTheorem_6_28_3_directPerturbationConvexBifunction P)) 0) := by
  let F := helperForTheorem_6_28_3_directPerturbationConvexBifunction P
  have hfinite :
      IsFiniteEReal (generalizedConvexProgramOptimalValue F) :=
    helperForTheorem_6_28_3_directPerturbationOptimalValue_finite
      P hoptimal_ne_bot hstrict_feasible
  rcases
      helperForTheorem_6_28_3_exists_multiplierLowerBoundCertificate_of_optimalValue_ne_bot_and_nonaffineStrictFeasibility
        P hoptimal_ne_bot hstrict_feasible with
    ⟨v, lambda, hoptimal, hlambda_nonneg, hobjective_lower⟩
  have hKT_F : IsKuhnTuckerVector F lambda := by
    -- The blocked ordinary-program certificate is exactly the input for the direct generalized
    -- Kuhn--Tucker construction.
    simpa [F] using
      helperForTheorem_6_28_3_directPerturbationKuhnTuckerVector_of_multiplierLowerBoundCertificate
        P hoptimal hlambda_nonneg hobjective_lower
  -- Once the generalized Kuhn--Tucker vector is available, the direct perturbation subgradient
  -- witness is exactly the Section 29 equivalence packaged above.
  exact
    helperForTheorem_6_28_3_subdifferentialNonemptyAt_directPerturbationFunction_zero_of_directPerturbationKuhnTuckerVector
      P hoptimal_ne_bot hstrict_feasible hKT_F

/-- Helper for Theorem 6.28.3: after discarding the false relative-interior route, the remaining
bridge is to rule out the bilateral `-∞` directional witness from Corollary 6.29.2 for the
direct perturbation bifunction. -/
lemma helperForTheorem_6_28_3_no_bilateralDirectionalDerivative_eq_bot_directPerturbation_of_nonaffineStrictFeasiblePoint
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hoptimal_ne_bot : P.optimalValue ≠ (⊥ : EReal))
    (hstrict_feasible : P.HasStrictFeasiblePointOnNonaffineInequalityIndices) :
    ¬ ∃ u : Fin m → ℝ,
      Filter.Tendsto
          (directionalDifferenceQuotientAt
            (generalizedConvexProgramPerturbationFunction
              (helperForTheorem_6_28_3_directPerturbationConvexBifunction P)) 0 u)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (⊥ : EReal)) ∧
      Filter.Tendsto
          (directionalDifferenceQuotientAt
            (generalizedConvexProgramPerturbationFunction
              (helperForTheorem_6_28_3_directPerturbationConvexBifunction P)) 0 u)
          (nhdsWithin (0 : ℝ) (Set.Iio 0)) (nhds (⊥ : EReal)) := by
  -- Route correction: the previous target `0 ∈ ri (dom p)` is false under Theorem 6.28.3's
  -- hypotheses, so the honest route is to obtain a Kuhn--Tucker certificate from the Chapter 21
  -- mixed strict/affine alternative and then contradict the bilateral `-∞` witness via
  -- Corollary 6.29.2.
  let F := helperForTheorem_6_28_3_directPerturbationConvexBifunction P
  have hfinite :
      IsFiniteEReal (generalizedConvexProgramOptimalValue F) :=
    helperForTheorem_6_28_3_directPerturbationOptimalValue_finite
      P hoptimal_ne_bot hstrict_feasible
  rcases
      helperForTheorem_6_28_3_subdifferentialNonemptyAt_directPerturbationFunction_zero_of_optimalValue_ne_bot_and_nonaffineStrictFeasibility
        P hoptimal_ne_bot hstrict_feasible with
    ⟨g, hg⟩
  have hKT_F : IsKuhnTuckerVector F (-g) := by
    -- The generalized perturbation subgradient witness is equivalent to a generalized
    -- Kuhn--Tucker vector for the same direct bifunction.
    have hg' :
        -(-g) ∈
          euclideanSubdifferentialAt (generalizedConvexProgramPerturbationFunction F) 0 := by
      simpa using hg
    exact
      ((generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).2.2 hfinite
        (-g)).2 hg'
  -- Reuse the generic Corollary 6.29.2 contradiction helper once the direct generalized
  -- Kuhn--Tucker vector has been constructed.
  have hfiniteF : IsFiniteEReal (generalizedConvexProgramOptimalValue
      (helperForTheorem_6_28_3_directPerturbationConvexBifunction P)) := by
    simpa [F] using hfinite
  have hKT_F' :
      IsKuhnTuckerVector (helperForTheorem_6_28_3_directPerturbationConvexBifunction P) (-g) := by
    simpa [F] using hKT_F
  exact
    helperForTheorem_6_28_3_no_bilateralDirectionalDerivative_of_directPerturbationKuhnTuckerVector
      P hfiniteF hKT_F'

/-- Helper for Theorem 6.28.3: once the direct perturbation bifunction has no bilateral
directional-derivative obstruction from Corollary 6.29.2, a generalized Kuhn--Tucker vector
already exists for that bifunction. -/
lemma helperForTheorem_6_28_3_exists_directPerturbationKuhnTuckerVector_of_no_bilateralDirectionalDerivative
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hoptimal_ne_bot : P.optimalValue ≠ (⊥ : EReal))
    (hstrict_feasible : P.HasStrictFeasiblePointOnNonaffineInequalityIndices)
    (hno_bilat :
      ¬ ∃ u : Fin m → ℝ,
        Filter.Tendsto
            (directionalDifferenceQuotientAt
              (generalizedConvexProgramPerturbationFunction
                (helperForTheorem_6_28_3_directPerturbationConvexBifunction P)) 0 u)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (⊥ : EReal)) ∧
        Filter.Tendsto
            (directionalDifferenceQuotientAt
              (generalizedConvexProgramPerturbationFunction
                (helperForTheorem_6_28_3_directPerturbationConvexBifunction P)) 0 u)
            (nhdsWithin (0 : ℝ) (Set.Iio 0)) (nhds (⊥ : EReal))) :
    ∃ uStar : Fin m → ℝ,
      IsKuhnTuckerVector (helperForTheorem_6_28_3_directPerturbationConvexBifunction P) uStar := by
  let F := helperForTheorem_6_28_3_directPerturbationConvexBifunction P
  have hfinite :
      IsFiniteEReal (generalizedConvexProgramOptimalValue F) :=
    helperForTheorem_6_28_3_directPerturbationOptimalValue_finite
      P hoptimal_ne_bot hstrict_feasible
  classical
  by_contra hNoKT
  -- Corollary 6.29.2 converts failure of generalized Kuhn--Tucker existence into exactly the
  -- bilateral directional-derivative obstruction ruled out here.
  exact
    hno_bilat
      ((generalizedConvexProgram_noKuhnTuckerVector_iff_exists_bilateralDirectionalDerivative_eq_bot
        F hfinite).1 hNoKT)

/-- Helper for Theorem 6.28.3: once the bilateral directional-derivative obstruction is ruled
out for the direct perturbation bifunction, the direct perturbation function already has a
Euclidean subgradient at the origin. -/
lemma helperForTheorem_6_28_3_subdifferentialNonemptyAt_directPerturbationFunction_zero_of_no_bilateralDirectionalDerivative
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hoptimal_ne_bot : P.optimalValue ≠ (⊥ : EReal))
    (hstrict_feasible : P.HasStrictFeasiblePointOnNonaffineInequalityIndices)
    (hno_bilat :
      ¬ ∃ u : Fin m → ℝ,
        Filter.Tendsto
            (directionalDifferenceQuotientAt
              (generalizedConvexProgramPerturbationFunction
                (helperForTheorem_6_28_3_directPerturbationConvexBifunction P)) 0 u)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (⊥ : EReal)) ∧
        Filter.Tendsto
            (directionalDifferenceQuotientAt
              (generalizedConvexProgramPerturbationFunction
                (helperForTheorem_6_28_3_directPerturbationConvexBifunction P)) 0 u)
            (nhdsWithin (0 : ℝ) (Set.Iio 0)) (nhds (⊥ : EReal))) :
    Set.Nonempty
      (euclideanSubdifferentialAt
        (generalizedConvexProgramPerturbationFunction
          (helperForTheorem_6_28_3_directPerturbationConvexBifunction P)) 0) := by
  rcases
      helperForTheorem_6_28_3_exists_directPerturbationKuhnTuckerVector_of_no_bilateralDirectionalDerivative
        P hoptimal_ne_bot hstrict_feasible hno_bilat with
    ⟨lambda, hKT_F⟩
  -- Apply the generalized Kuhn--Tucker/subgradient equivalence to the direct perturbation
  -- witness just obtained.
  exact
    helperForTheorem_6_28_3_subdifferentialNonemptyAt_directPerturbationFunction_zero_of_directPerturbationKuhnTuckerVector
      P hoptimal_ne_bot hstrict_feasible hKT_F

/-- Helper for Theorem 6.28.3: once a later Section 29 bridge identifies the perturbation domain
with the effective domain of `P.perturbationFunction`, strong consistency of that bridge gives the
required origin-membership in the relative interior of `dom p`. -/
lemma helperForTheorem_6_28_3_zero_mem_relativeInterior_effectiveDomain_of_stronglyConsistentBridge
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (Q : IndexedOrdinaryConvexProgram m n)
    (hdomain :
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) P.perturbationFunction =
        bifunctionEffectiveDomain (ordinaryConvexProgramAssociatedBifunction Q))
    (hstrong : ordinaryConvexProgramStronglyConsistent Q) :
    (0 : Fin m → ℝ) ∈
      euclideanRelativeInterior_fin m
        (effectiveDomain (Set.univ : Set (Fin m → ℝ)) P.perturbationFunction) := by
  -- Transport the later strong-consistency conclusion across the identified perturbation domains.
  rw [hdomain]
  simpa [ordinaryConvexProgramStronglyConsistent, generalizedConvexProgramStronglyConsistent,
    ordinaryConvexProgramAssociatedConvexBifunction] using hstrong

/-- Helper for Theorem 6.28.3: once `p(0)` is finite, the remaining existence problem is to show
that the perturbation function is subdifferentiable at the origin. -/
lemma helperForTheorem_6_28_3_subdifferentialNonemptyAt_perturbationFunction_zero
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hoptimal_ne_bot : P.optimalValue ≠ (⊥ : EReal))
    (hstrict_feasible : P.HasStrictFeasiblePointOnNonaffineInequalityIndices) :
    Set.Nonempty (euclideanSubdifferentialAt P.perturbationFunction 0) := by
  let F := helperForTheorem_6_28_3_directPerturbationConvexBifunction P
  have hno_bilat :
      ¬ ∃ u : Fin m → ℝ,
        Filter.Tendsto
            (directionalDifferenceQuotientAt
              (generalizedConvexProgramPerturbationFunction F) 0 u)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (⊥ : EReal)) ∧
        Filter.Tendsto
            (directionalDifferenceQuotientAt
              (generalizedConvexProgramPerturbationFunction F) 0 u)
            (nhdsWithin (0 : ℝ) (Set.Iio 0)) (nhds (⊥ : EReal)) :=
    helperForTheorem_6_28_3_no_bilateralDirectionalDerivative_eq_bot_directPerturbation_of_nonaffineStrictFeasiblePoint
      P hoptimal_ne_bot hstrict_feasible
  rcases
      helperForTheorem_6_28_3_subdifferentialNonemptyAt_directPerturbationFunction_zero_of_no_bilateralDirectionalDerivative
        P hoptimal_ne_bot hstrict_feasible hno_bilat with
    ⟨g, hg⟩
  have hperturb :
      generalizedConvexProgramPerturbationFunction F = P.perturbationFunction := by
    simpa [F] using
      helperForTheorem_6_28_3_generalizedPerturbationFunction_eq_perturbationFunction P
  -- Translate the generalized subgradient witness back to the textbook perturbation function.
  have hg' : g ∈ euclideanSubdifferentialAt P.perturbationFunction 0 := by
    rwa [← hperturb]
  exact ⟨g, hg'⟩

/-- Helper for Theorem 6.28.3: once the perturbation function has a Euclidean subgradient at the
origin, the supporting-inequality characterization of Theorem 6.28.2 produces a Kuhn--Tucker
vector by negating that subgradient. -/
lemma helperForTheorem_6_28_3_isKuhnTuckerVector_of_mem_euclideanSubdifferentialAt_perturbationFunction_zero
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (g : Fin m → ℝ)
    (hp0_finite : ∃ p0 : ℝ, P.perturbationFunction 0 = (p0 : EReal))
    (hg : g ∈ euclideanSubdifferentialAt P.perturbationFunction 0) :
    P.IsKuhnTuckerVector (-g) := by
  -- Negating the Euclidean subgradient matches the sign convention used in the perturbation
  -- supporting inequality.
  have hsupport :
      ∀ u : Fin m → ℝ,
        P.perturbationFunction u + (((∑ i : Fin m, (-g) i * u i : ℝ)) : EReal) ≥
          P.perturbationFunction 0 :=
    by
      -- Avoid embedding proofs into terms: name the negated-subgradient membership first.
      have hnegmem : -(-g) ∈ euclideanSubdifferentialAt P.perturbationFunction 0 := by
        simpa using hg
      exact
        (helperForTheorem_6_28_3_neg_mem_euclideanSubdifferentialAt_perturbationFunction_zero_iff
          P (-g)).1 hnegmem
  -- Theorem 6.28.2 turns that global affine lower support into the Kuhn--Tucker conditions.
  exact
    (isKuhnTuckerVector_iff_perturbationFunction_lower_bound P (-g) hp0_finite).2 hsupport

/-- Helper for Theorem 6.28.3: once the perturbation function has some Euclidean subgradient at
the origin, negating that witness already produces the required Kuhn--Tucker vector. -/
lemma helperForTheorem_6_28_3_exists_kuhnTuckerVector_of_subdifferentialNonemptyAt_perturbationFunction_zero
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hp0_finite : ∃ p0 : ℝ, P.perturbationFunction 0 = (p0 : EReal))
    (hsub : Set.Nonempty (euclideanSubdifferentialAt P.perturbationFunction 0)) :
    ∃ lambda : Fin m → ℝ, P.IsKuhnTuckerVector lambda := by
  rcases hsub with ⟨g, hg⟩
  -- The previous lemma converts the chosen perturbation subgradient into a Kuhn--Tucker vector
  -- after the textbook sign change `lambda = -g`.
  exact ⟨-g,
    helperForTheorem_6_28_3_isKuhnTuckerVector_of_mem_euclideanSubdifferentialAt_perturbationFunction_zero
      P g hp0_finite hg⟩

/-- Helper for Theorem 6.28.3: once a multiplier vector gives a pointwise lower bound for the
Kuhn--Tucker objective on the ambient constraint set, it already has the correct infimum value
and is therefore a Kuhn--Tucker vector. -/
lemma helperForTheorem_6_28_3_isKuhnTuckerVector_of_kuhnTuckerObjective_lowerBound_on_constraintSet
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ) (v : ℝ)
    (hlambda_nonneg : ∀ i : Fin r, 0 ≤ P.inequalityMultipliers lambda i)
    (hobjective_lower :
      ∀ x : Fin n → ℝ, x ∈ P.constraintSet → v ≤ P.kuhnTuckerObjective lambda x)
    (hoptimal : P.optimalValue = (v : EReal)) :
    P.IsKuhnTuckerVector lambda := by
  -- The lower bound makes `v` a common lower bound for all Kuhn--Tucker objective values on `C`.
  have hsinf_lower :
      (v : EReal) ≤
        sInf ((fun x => ((P.kuhnTuckerObjective lambda x : ℝ) : EReal)) '' P.constraintSet) := by
    refine le_sInf ?_
    rintro _ ⟨x, hx, rfl⟩
    exact EReal.coe_le_coe_iff.2 (hobjective_lower x hx)
  -- On feasible points, the Kuhn--Tucker objective is bounded above by the primal objective.
  have hsinf_upper :
      sInf ((fun x => ((P.kuhnTuckerObjective lambda x : ℝ) : EReal)) '' P.constraintSet) ≤
        P.optimalValue := by
    rw [BookOrdinaryConvexProgram.optimalValue]
    refine le_sInf ?_
    rintro _ ⟨x, hxFeas, rfl⟩
    have hsinf_le_x :
        sInf ((fun y => ((P.kuhnTuckerObjective lambda y : ℝ) : EReal)) '' P.constraintSet) ≤
          ((P.kuhnTuckerObjective lambda x : ℝ) : EReal) := by
      exact sInf_le ⟨x, hxFeas.1, rfl⟩
    have hkuhn_le_obj :
        ((P.kuhnTuckerObjective lambda x : ℝ) : EReal) ≤ ((P.objective x : ℝ) : EReal) := by
      exact_mod_cast
        helperForTheorem_6_28_1_kuhnTuckerObjective_le_objective_of_feasible
          P lambda hxFeas hlambda_nonneg
    exact le_trans hsinf_le_x hkuhn_le_obj
  -- The two inequalities identify the Kuhn--Tucker infimum with `v = P.optimalValue`.
  have hsinf_eq_v :
      sInf ((fun x => ((P.kuhnTuckerObjective lambda x : ℝ) : EReal)) '' P.constraintSet) =
        (v : EReal) := by
    apply le_antisymm
    · calc
        sInf ((fun x => ((P.kuhnTuckerObjective lambda x : ℝ) : EReal)) '' P.constraintSet) ≤
            P.optimalValue := hsinf_upper
        _ = (v : EReal) := hoptimal
    · exact hsinf_lower
  exact ⟨hlambda_nonneg, v, hsinf_eq_v, hoptimal⟩

/-- Helper for Theorem 6.28.3: the missing direct-certificate bridge asserting that strict
feasibility on the nonaffine inequality constraints yields a multiplier vector whose
Kuhn--Tucker objective is bounded below by the finite primal value on all of the ambient
constraint set. -/
lemma helperForTheorem_6_28_3_exists_multiplier_with_kuhnTuckerObjective_lowerBound_on_constraintSet
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hoptimal_ne_bot : P.optimalValue ≠ (⊥ : EReal))
    (hstrict_feasible : P.HasStrictFeasiblePointOnNonaffineInequalityIndices) :
    ∃ v : ℝ, ∃ lambda : Fin m → ℝ,
      P.optimalValue = (v : EReal) ∧
        (∀ i : Fin r, 0 ≤ P.inequalityMultipliers lambda i) ∧
          (∀ x : Fin n → ℝ, x ∈ P.constraintSet → v ≤ P.kuhnTuckerObjective lambda x) := by
  -- Route correction: this theorem is the semantic blocker the file now exposes explicitly,
  -- rather than another renamed wrapper around the abandoned Chapter 21 `ri` route.
  exact
    helperForTheorem_6_28_3_exists_multiplierLowerBoundCertificate_of_optimalValue_ne_bot_and_nonaffineStrictFeasibility
      P hoptimal_ne_bot hstrict_feasible

-- Proof sketch: let `I = P.nonaffineInequalityIndices`. The hypothesis
-- `P.HasStrictFeasiblePointOnNonaffineInequalityIndices` is exactly the book's requirement that
-- `(P)` has a feasible point that is strict on every nonaffine inequality constraint, while
-- `P.optimalValue ≠ -∞` rules out the degenerate case. The perturbation-function separation
-- argument then yields a Kuhn--Tucker multiplier vector.
/-- Theorem 6.28.3: Let `(P)` be an ordinary convex program, and let
`I = P.nonaffineInequalityIndices` be the set of inequality-constraint indices for which `fᵢ`
is not affine on the ambient constraint set `C`. Assume that the optimal value of `(P)` is not
`-∞`, and that `(P)` has a feasible solution whose inequality constraints are satisfied strictly
for every `i ∈ I`. Then `(P)` admits a Kuhn--Tucker vector. -/
theorem exists_kuhnTuckerVector_of_optimalValue_ne_bot_and_feasiblePoint_strict_on_nonaffineIndices
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hoptimal_ne_bot : P.optimalValue ≠ (⊥ : EReal))
    (hstrict_feasible : P.HasStrictFeasiblePointOnNonaffineInequalityIndices) :
    ∃ lambda : Fin m → ℝ, P.IsKuhnTuckerVector lambda := by
  -- Route correction: once `∂p(0)` is nonempty, the textbook proof can finish directly from the
  -- perturbation-function support inequality, without repackaging an intermediate Chapter 21
  -- multiplier lower bound on `P.kuhnTuckerObjective`.
  have hp0_finite : ∃ p0 : ℝ, P.perturbationFunction 0 = (p0 : EReal) :=
    helperForTheorem_6_28_3_exists_real_perturbationFunction_zero
      P hoptimal_ne_bot hstrict_feasible
  have hsub :
      Set.Nonempty (euclideanSubdifferentialAt P.perturbationFunction 0) :=
    helperForTheorem_6_28_3_subdifferentialNonemptyAt_perturbationFunction_zero
      P hoptimal_ne_bot hstrict_feasible
  -- The nonempty perturbation subdifferential now packages directly into the existential
  -- Kuhn--Tucker conclusion.
  exact
    helperForTheorem_6_28_3_exists_kuhnTuckerVector_of_subdifferentialNonemptyAt_perturbationFunction_zero
      P hp0_finite hsub

/-- Helper for Corollary 6.28.3: strict feasibility for all inequality constraints implies the
strict-feasibility hypothesis of Theorem 6.28.3 (strict only on the nonaffine inequality indices).

This is the only real conversion needed to apply Theorem 6.28.3 when `r = m` (no equality
constraints). -/
lemma helperForCorollary_6_28_3_hasStrictFeasiblePointOnNonaffineInequalityIndices_of_strict_all_inequalities
    {n m : ℕ} (P : BookOrdinaryConvexProgram n m m)
    (hstrict_feasible :
      ∃ x : Fin n → ℝ,
        x ∈ euclideanRelativeInterior_fin n P.constraintSet ∧
          ∀ i : Fin m, P.inequalityConstraint i x < 0) :
    P.HasStrictFeasiblePointOnNonaffineInequalityIndices := by
  -- Start from the given strict-feasible witness on *all* inequality constraints.
  rcases hstrict_feasible with ⟨x, hxri, hxlt⟩
  have hxC : x ∈ P.constraintSet :=
    helperForTheorem_6_28_3_mem_of_mem_euclideanRelativeInterior_fin hxri
  -- Convert strict inequalities into the weak inequalities required for feasibility.
  have hineq : ∀ i : Fin m, P.inequalityConstraint i x ≤ 0 := by
    intro i
    exact le_of_lt (hxlt i)
  -- There are no equality constraints when `r = m`, so that feasibility block is vacuous.
  have heq : ∀ i : Fin (m - m), P.equalityConstraint i x = 0 := by
    intro i
    have hm : m - m = 0 := Nat.sub_self m
    exact (Fin.elim0 (Fin.cast hm i) : P.equalityConstraint i x = 0)
  -- Package the three blocks into membership in `P.feasibleSet`.
  have hxFeasible : x ∈ P.feasibleSet := by
    -- Unfold `feasibleSet` and close the conjunctive goal using `hxC`, `hineq`, and `heq`.
    simp [BookOrdinaryConvexProgram.feasibleSet, hxC, hineq, heq]
  -- The nonaffine strictness is immediate since we are strict on every inequality index.
  have hstrictNonaffine :
      ∀ i ∈ P.nonaffineInequalityIndices, P.inequalityConstraint i x < 0 := by
    intro i _
    exact hxlt i
  -- This is exactly the strict-feasible hypothesis used in Theorem 6.28.3.
  exact ⟨x, hxri, hxFeasible, hstrictNonaffine⟩

-- Proof sketch: specialize Theorem 6.28.3 to the case `r = m`, so there are only inequality
-- constraints. A point in `C = P.constraintSet` with `fᵢ(x) < 0` for every inequality index is,
-- in particular, strict on the subset of nonaffine inequality indices, and the non-bottom
-- optimal-value hypothesis is unchanged. The theorem then yields a Kuhn--Tucker vector.
/-- Corollary 6.28.3: Let `(P)` be an ordinary convex program with only inequality constraints,
so `P : BookOrdinaryConvexProgram n m m`. Assume that the optimal value of `(P)` is not `-∞`, and
that there exists `x ∈ ri C` such that `fᵢ(x) < 0` for every `i = 1, …, m`.
Then `(P)` admits a Kuhn--Tucker vector. -/
theorem exists_kuhnTuckerVector_of_optimalValue_ne_bot_and_strict_feasiblePoint
    {n m : ℕ} (P : BookOrdinaryConvexProgram n m m)
    (hoptimal_ne_bot : P.optimalValue ≠ (⊥ : EReal))
    (hstrict_feasible :
      ∃ x : Fin n → ℝ,
        x ∈ euclideanRelativeInterior_fin n P.constraintSet ∧
          ∀ i : Fin m, P.inequalityConstraint i x < 0) :
    ∃ lambda : Fin m → ℝ, P.IsKuhnTuckerVector lambda := by
  -- Convert the corollary's strict-feasibility hypothesis into the form required by Theorem 6.28.3.
  have hstrictNonaffine : P.HasStrictFeasiblePointOnNonaffineInequalityIndices :=
    helperForCorollary_6_28_3_hasStrictFeasiblePointOnNonaffineInequalityIndices_of_strict_all_inequalities
      P hstrict_feasible
  -- Apply Theorem 6.28.3 (proved just above) to obtain a Kuhn--Tucker vector.
  exact
    exists_kuhnTuckerVector_of_optimalValue_ne_bot_and_feasiblePoint_strict_on_nonaffineIndices
      P hoptimal_ne_bot hstrictNonaffine

/-- All constraint functions of `P` are affine on the ambient space `ℝ^n`. -/
def BookOrdinaryConvexProgram.HasAffineConstraintFunctions {n m r : ℕ}
    (P : BookOrdinaryConvexProgram n m r) : Prop :=
  (∀ i : Fin r, IsAffineOnFiniteDimensional Set.univ (P.inequalityConstraint i)) ∧
  ∀ i : Fin (m - r), IsAffineOnFiniteDimensional Set.univ (P.equalityConstraint i)

/-- Helper for Corollary 6.28.4: an affine-on-`Set.univ` function is affine on
`P.constraintSet`, by restricting the `Set.EqOn` witness. -/
lemma helperForCorollary_6_28_4_isAffineOn_constraintSet_of_isAffineOn_univ
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {f : (Fin n → ℝ) → ℝ}
    (hAffine : IsAffineOnFiniteDimensional (Set.univ : Set (Fin n → ℝ)) f) :
    IsAffineOnFiniteDimensional P.constraintSet f := by
  -- Unpack the global affine representative and reuse it on the smaller domain.
  rcases hAffine with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  intro x hx
  -- Membership in `Set.univ` is automatic, so the original `EqOn` applies.
  exact ha (Set.mem_univ x)

/-- Helper for Corollary 6.28.4: if every inequality constraint is affine on `ℝ^n`, then no
inequality index lies in `P.nonaffineInequalityIndices`. -/
lemma helperForCorollary_6_28_4_not_mem_nonaffineInequalityIndices_of_affineConstraints
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (haffine_constraints : P.HasAffineConstraintFunctions) (i : Fin r) :
    i ∉ P.nonaffineInequalityIndices := by
  -- Unfold membership: being in `nonaffineInequalityIndices` means "not affine on `C`".
  intro hi
  have hi' := hi
  simp [BookOrdinaryConvexProgram.nonaffineInequalityIndices] at hi'
  -- But affineness on `ℝ^n` restricts to affineness on `C = P.constraintSet`.
  have hAffineC :
      IsAffineOnFiniteDimensional P.constraintSet (P.inequalityConstraint i) :=
    helperForCorollary_6_28_4_isAffineOn_constraintSet_of_isAffineOn_univ P
      (haffine_constraints.1 i)
  -- Contradiction.
  exact hi' hAffineC

/-- Helper for Corollary 6.28.4: any feasible point is automatically strict on the (empty)
nonaffine inequality index set when all inequality constraints are affine. -/
lemma helperForCorollary_6_28_4_hasStrictFeasiblePointOnNonaffineInequalityIndices_of_feasiblePoint_of_affineConstraints
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (haffine_constraints : P.HasAffineConstraintFunctions) {x : Fin n → ℝ}
    (hxri : x ∈ euclideanRelativeInterior_fin n P.constraintSet)
    (hxFeasible : x ∈ P.feasibleSet) :
    P.HasStrictFeasiblePointOnNonaffineInequalityIndices := by
  -- Reuse the given feasible point and prove strictness by vacuity of the nonaffine index set.
  refine ⟨x, hxri, hxFeasible, ?_⟩
  intro i hi
  have hnot :
      i ∉ P.nonaffineInequalityIndices :=
    helperForCorollary_6_28_4_not_mem_nonaffineInequalityIndices_of_affineConstraints
      P haffine_constraints i
  -- From `i ∈` and `i ∉` we get `False`, so the strict inequality holds trivially.
  exact False.elim (hnot hi)

-- Proof sketch: if every constraint function is affine on `ℝ^n`, then every inequality
-- constraint is affine on `P.constraintSet`, so the set `P.nonaffineInequalityIndices` from
-- Theorem 6.28.3 is empty and its strict-feasibility hypothesis is vacuous. A feasible point in
-- `ri C`, represented here by `intrinsicInterior ℝ P.constraintSet`, is in particular a feasible
-- point, and together with `P.optimalValue ≠ -∞` Theorem 6.28.3 yields a Kuhn--Tucker vector.
/-- Corollary 6.28.4: Let `(P)` be an ordinary convex program whose constraints are all of the
form `fᵢ(x) = ⟪aᵢ, x⟫ - αᵢ`, encoded here by requiring every inequality and equality constraint
function to be affine on `ℝ^n`. If the optimal value of `(P)` is not `-∞` and `(P)` has a
feasible solution in `ri C`, represented here by `intrinsicInterior ℝ P.constraintSet`, then
`(P)` admits a Kuhn--Tucker vector. -/
theorem exists_kuhnTuckerVector_of_optimalValue_ne_bot_and_feasiblePoint_mem_intrinsicInterior_of_affineConstraints
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (haffine_constraints : P.HasAffineConstraintFunctions)
    (hoptimal_ne_bot : P.optimalValue ≠ (⊥ : EReal))
    (hfeasible_ri :
      ∃ x : Fin n → ℝ, x ∈ P.feasibleSet ∧ x ∈ intrinsicInterior ℝ P.constraintSet) :
    ∃ lambda : Fin m → ℝ, P.IsKuhnTuckerVector lambda := by
  -- Extract a feasible point; the intrinsic-interior information is not needed to make the
  -- strictness hypothesis of Theorem 6.28.3 vacuous under affine constraints.
  rcases hfeasible_ri with ⟨x, hxFeasible, hxII⟩
  have hxri : x ∈ euclideanRelativeInterior_fin n P.constraintSet := by
    rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior]
    exact hxII
  -- Under affine constraints, there are no nonaffine inequality indices, hence any feasible
  -- point is strict on that (empty) index set.
  have hstrict :
      P.HasStrictFeasiblePointOnNonaffineInequalityIndices :=
    helperForCorollary_6_28_4_hasStrictFeasiblePointOnNonaffineInequalityIndices_of_feasiblePoint_of_affineConstraints
      P haffine_constraints hxri hxFeasible
  -- Apply Theorem 6.28.3 to obtain a Kuhn--Tucker vector.
  exact
    exists_kuhnTuckerVector_of_optimalValue_ne_bot_and_feasiblePoint_strict_on_nonaffineIndices
      P hoptimal_ne_bot hstrict

/-- The multiplier vectors for `P` whose inequality components are nonnegative. -/
def BookOrdinaryConvexProgram.lagrangeMultiplierSet {n m r : ℕ}
    (P : BookOrdinaryConvexProgram n m r) : Set (Fin m → ℝ) :=
  {lambda | ∀ i : Fin r, 0 ≤ P.inequalityMultipliers lambda i}

/-- Definition 6.28.6 (Lagrangian): For an ordinary convex program `(P)`, the Lagrangian
`L(lambda, x)` equals `f₀(x) + ∑ᵢ lambdaᵢ fᵢ(x)` when `x ∈ C = P.constraintSet` and the
multiplier vector `lambda` has nonnegative inequality components, equals `-∞` when
`x ∈ C` but `lambda` is not in `P.lagrangeMultiplierSet`, and equals `+∞` when
`x ∉ C`. -/
noncomputable def BookOrdinaryConvexProgram.lagrangian {n m r : ℕ}
    (P : BookOrdinaryConvexProgram n m r) : (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun lambda x =>
    open scoped Classical in
    if x ∈ P.constraintSet then
      if lambda ∈ P.lagrangeMultiplierSet then
        (P.kuhnTuckerObjective lambda x : EReal)
      else
        (⊥ : EReal)
    else
      (⊤ : EReal)

/-- Definition 6.28.7 (Saddle point of the Lagrangian): A pair `(uBar, xBar)` is a saddle
point of the Lagrangian associated with an ordinary convex program `P`, with respect to
maximization in the multiplier variable and minimization in the primal variable, if
`P.lagrangian u xBar ≤ P.lagrangian uBar xBar ≤ P.lagrangian uBar x` for every multiplier
vector `u` and every primal point `x`. -/
def BookOrdinaryConvexProgram.IsLagrangianSaddlePoint {n m r : ℕ}
    (P : BookOrdinaryConvexProgram n m r) (uBar : Fin m → ℝ) (xBar : Fin n → ℝ) : Prop :=
  (∀ u : Fin m → ℝ, P.lagrangian u xBar ≤ P.lagrangian uBar xBar) ∧
    ∀ x : Fin n → ℝ, P.lagrangian uBar xBar ≤ P.lagrangian uBar x

/-- Helper for Theorem 6.28.4: when `P.constraintSet = ∅`, the Lagrangian is constantly `⊤`
because every primal point is outside the constraint set. -/
lemma helperForTheorem_6_28_4_lagrangian_eq_top_of_constraintSet_eq_empty
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r)
    (hconstraint : P.constraintSet = (∅ : Set (Fin n → ℝ)))
    (lambda : Fin m → ℝ) (x : Fin n → ℝ) :
    P.lagrangian lambda x = (⊤ : EReal) := by
  -- With an empty constraint set, the membership test `x ∈ P.constraintSet` is false.
  have hx : x ∉ P.constraintSet := by
    simp [hconstraint]
  -- Unfold the Lagrangian; the outer `if` falls through to the `⊤` branch.
  simp [BookOrdinaryConvexProgram.lagrangian, hx]

/-- Helper for Theorem 6.28.4: if `P.constraintSet = ∅`, then every pair `(uBar, xBar)` is a
Lagrangian saddle point, since all Lagrangian values equal `⊤`. -/
lemma helperForTheorem_6_28_4_isLagrangianSaddlePoint_of_constraintSet_eq_empty
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (uBar : Fin m → ℝ) (xBar : Fin n → ℝ)
    (hconstraint : P.constraintSet = (∅ : Set (Fin n → ℝ))) :
    P.IsLagrangianSaddlePoint uBar xBar := by
  -- Unpack the saddle inequalities; each Lagrangian term rewrites to `⊤`.
  constructor
  · intro u
    simp
      [helperForTheorem_6_28_4_lagrangian_eq_top_of_constraintSet_eq_empty P hconstraint u xBar,
        helperForTheorem_6_28_4_lagrangian_eq_top_of_constraintSet_eq_empty P hconstraint uBar xBar]
  · intro x
    simp
      [helperForTheorem_6_28_4_lagrangian_eq_top_of_constraintSet_eq_empty P hconstraint uBar xBar,
        helperForTheorem_6_28_4_lagrangian_eq_top_of_constraintSet_eq_empty P hconstraint uBar x]

/-- Helper for Theorem 6.28.4: an empty constraint set rules out Kuhn--Tucker vectors, because the
infimum over `P.constraintSet` becomes `sInf ∅ = ⊤`, which cannot equal a real coercion. -/
lemma helperForTheorem_6_28_4_not_isKuhnTuckerVector_of_constraintSet_eq_empty
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (uStar : Fin m → ℝ)
    (hconstraint : P.constraintSet = (∅ : Set (Fin n → ℝ))) :
    ¬ P.IsKuhnTuckerVector uStar := by
  -- Any Kuhn--Tucker vector would identify `sInf (∅)` with a real number, contradicting `sInf ∅ = ⊤`.
  rintro ⟨_hnonneg, v, hv, _hopt⟩
  have htop : (⊤ : EReal) = (v : EReal) := by
    simpa [hconstraint] using hv
  exact (EReal.top_ne_coe v) htop

/-- Helper for Theorem 6.28.4: an empty constraint set forces `P.feasibleSet = ∅`, so no point can
be an optimal solution. -/
lemma helperForTheorem_6_28_4_not_isOptimalSolution_of_constraintSet_eq_empty
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (x : Fin n → ℝ)
    (hconstraint : P.constraintSet = (∅ : Set (Fin n → ℝ))) :
    ¬ P.IsOptimalSolution x := by
  -- An optimal solution must be feasible, but `P.feasibleSet` is empty when `P.constraintSet` is.
  rintro ⟨hxFeasible, _hmin⟩
  -- Unfolding feasibility already yields a contradiction.
  have : False := by
    simpa [BookOrdinaryConvexProgram.feasibleSet, hconstraint] using hxFeasible
  exact this

/-- Helper for Theorem 6.28.4: if `P.constraintSet = ∅`, then the first equivalence in Theorem
6.28.4 cannot hold, since every pair is a saddle point but no Kuhn--Tucker vector exists. -/
lemma helperForTheorem_6_28_4_not_kuhnTuckerVector_and_optimalSolution_iff_lagrangianSaddlePoint_of_constraintSet_eq_empty
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (uStar : Fin m → ℝ) (x : Fin n → ℝ)
    (hconstraint : P.constraintSet = (∅ : Set (Fin n → ℝ))) :
    ¬ ((P.IsKuhnTuckerVector uStar ∧ P.IsOptimalSolution x) ↔
      P.IsLagrangianSaddlePoint uStar x) := by
  intro hiff
  -- Under `P.constraintSet = ∅`, every pair is a Lagrangian saddle point.
  have hsaddle : P.IsLagrangianSaddlePoint uStar x :=
    helperForTheorem_6_28_4_isLagrangianSaddlePoint_of_constraintSet_eq_empty P uStar x hconstraint
  -- The equivalence would then produce a Kuhn--Tucker vector, contradicting emptiness.
  have hleft : P.IsKuhnTuckerVector uStar ∧ P.IsOptimalSolution x :=
    hiff.mpr hsaddle
  exact helperForTheorem_6_28_4_not_isKuhnTuckerVector_of_constraintSet_eq_empty P uStar hconstraint hleft.1

/-- The textbook stationarity set for an ordinary convex program, realized as the subdifferential
at `x` of the indicator-extended Kuhn--Tucker objective `δ_C + f₀ + ∑ᵢ λᵢ fᵢ`, where
`C = P.constraintSet`. This packages the ambient constraint contribution into the
subdifferential and is equivalent to omitting every constraint term with zero multiplier in the
formal sum. -/
noncomputable def BookOrdinaryConvexProgram.textbookKuhnTuckerStationaritySet
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ) (x : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  euclideanSubdifferentialAt (P.extendedKuhnTuckerObjective lambda) x

/-- The explicit Kuhn--Tucker conditions for a candidate saddle point. They consist of primal
feasibility in `P.constraintSet`, complementary slackness and sign conditions for the inequality
constraints, the equality constraints, and the textbook stationarity condition
`0 ∈ ∂(δ_C + f₀ + ∑ᵢ λᵢ fᵢ)(x)` with `C = P.constraintSet`, equivalently the stationarity rule
obtained by omitting every constraint term with zero multiplier from the formal sum. -/
noncomputable def BookOrdinaryConvexProgram.SatisfiesKuhnTuckerPointConditions
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (lambda : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  x ∈ P.constraintSet ∧
    (∀ i : Fin r,
      0 ≤ P.inequalityMultipliers lambda i ∧
        P.inequalityConstraint i x ≤ 0 ∧
        P.inequalityMultipliers lambda i * P.inequalityConstraint i x = 0) ∧
    (∀ i : Fin (m - r), P.equalityConstraint i x = 0) ∧
    (0 : Fin n → ℝ) ∈ P.textbookKuhnTuckerStationaritySet lambda x

/-- Helper for Theorem 6.28.4: if `P.constraintSet = ∅`, then the second equivalence in Theorem
6.28.4 cannot hold, since every pair is a saddle point but the explicit Kuhn--Tucker point
conditions begin with the (impossible) feasibility clause `x ∈ P.constraintSet`. -/
lemma helperForTheorem_6_28_4_not_lagrangianSaddlePoint_iff_kuhnTuckerPointConditions_of_constraintSet_eq_empty
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (uStar : Fin m → ℝ) (x : Fin n → ℝ)
    (hconstraint : P.constraintSet = (∅ : Set (Fin n → ℝ))) :
    ¬ (P.IsLagrangianSaddlePoint uStar x ↔
      P.SatisfiesKuhnTuckerPointConditions uStar x) := by
  intro hiff
  -- Under `P.constraintSet = ∅`, every pair is a Lagrangian saddle point.
  have hsaddle : P.IsLagrangianSaddlePoint uStar x :=
    helperForTheorem_6_28_4_isLagrangianSaddlePoint_of_constraintSet_eq_empty P uStar x hconstraint
  -- The equivalence would then force the explicit Kuhn--Tucker point conditions.
  have hconditions : P.SatisfiesKuhnTuckerPointConditions uStar x :=
    hiff.mp hsaddle
  -- But these conditions start by asserting primal feasibility `x ∈ P.constraintSet`.
  have hx : x ∈ P.constraintSet := hconditions.1
  -- Feasibility is impossible when `P.constraintSet = ∅`.
  have : False := by
    simpa [hconstraint] using hx
  exact this

/-- Helper for Theorem 6.28.4: if `P.constraintSet = ∅`, then the full conjunction of
equivalences in Theorem 6.28.4 fails (already the first equivalence fails). -/
lemma helperForTheorem_6_28_4_not_conclusion_of_constraintSet_eq_empty
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (uStar : Fin m → ℝ) (x : Fin n → ℝ)
    (hconstraint : P.constraintSet = (∅ : Set (Fin n → ℝ))) :
    ¬ (((P.IsKuhnTuckerVector uStar ∧ P.IsOptimalSolution x) ↔
        P.IsLagrangianSaddlePoint uStar x) ∧
      (P.IsLagrangianSaddlePoint uStar x ↔
        P.SatisfiesKuhnTuckerPointConditions uStar x)) := by
  intro hconj
  exact
    helperForTheorem_6_28_4_not_kuhnTuckerVector_and_optimalSolution_iff_lagrangianSaddlePoint_of_constraintSet_eq_empty
      P uStar x hconstraint hconj.1

/-- Helper for Theorem 6.28.4: the empty constraint set is convex, so it satisfies the ambient
convexity requirement in `BookOrdinaryConvexProgram`. -/
lemma helperForTheorem_6_28_4_convex_empty_constraintSet
    {n : ℕ} : Convex ℝ (∅ : Set (Fin n → ℝ)) := by
  -- Convexity is a universal property, and it holds trivially on the empty set.
  simpa using (convex_empty : Convex ℝ (∅ : Set (Fin n → ℝ)))

/-- Helper for Theorem 6.28.4: any real-valued function is convex on the empty set. -/
lemma helperForTheorem_6_28_4_convexOn_empty_constraintSet
    {n : ℕ} (f : (Fin n → ℝ) → ℝ) : ConvexOn ℝ (∅ : Set (Fin n → ℝ)) f := by
  -- There are no points to check on `∅`, so the Jensen inequality condition is vacuous.
  constructor
  · exact helperForTheorem_6_28_4_convex_empty_constraintSet (n := n)
  · intro x hx
    cases hx

/-- Helper for Theorem 6.28.4: an explicit ordinary convex program with empty constraint set.

This program witnesses that the current Lean statement of Theorem 6.28.4 cannot be proved without
extra hypotheses: when `constraintSet = ∅`, the Lagrangian collapses to the constant `⊤`, making
every pair a saddle point while feasibility-based conditions fail. -/
noncomputable def helperForTheorem_6_28_4_counterexampleProgram
    (n : ℕ) : BookOrdinaryConvexProgram n 0 0 where
  constraintSet := (∅ : Set (Fin n → ℝ))
  objective := fun _ => 0
  inequalityConstraint := fun i => Fin.elim0 i
  equalityConstraint := fun i => Fin.elim0 i
  inequalityCount_le_constraintCount := le_rfl
  convex_constraintSet := helperForTheorem_6_28_4_convex_empty_constraintSet (n := n)
  objective_convexOn :=
    helperForTheorem_6_28_4_convexOn_empty_constraintSet (n := n) (fun _ => (0 : ℝ))
  inequalityConstraint_convexOn := fun i => Fin.elim0 i
  equalityConstraint_affineOn := fun i => Fin.elim0 i

/-- Helper for Theorem 6.28.4: a concrete counterexample instance showing the full conjunction of
equivalences from Theorem 6.28.4 is false under the current definitions. -/
lemma helperForTheorem_6_28_4_counterexample_instance :
    ¬ (((((helperForTheorem_6_28_4_counterexampleProgram 1).IsKuhnTuckerVector
            (fun i : Fin 0 => Fin.elim0 i)) ∧
          ((helperForTheorem_6_28_4_counterexampleProgram 1).IsOptimalSolution
            (fun _ : Fin 1 => 0))) ↔
        (helperForTheorem_6_28_4_counterexampleProgram 1).IsLagrangianSaddlePoint
          (fun i : Fin 0 => Fin.elim0 i) (fun _ : Fin 1 => 0)) ∧
      ((helperForTheorem_6_28_4_counterexampleProgram 1).IsLagrangianSaddlePoint
            (fun i : Fin 0 => Fin.elim0 i) (fun _ : Fin 1 => 0) ↔
        (helperForTheorem_6_28_4_counterexampleProgram 1).SatisfiesKuhnTuckerPointConditions
          (fun i : Fin 0 => Fin.elim0 i) (fun _ : Fin 1 => 0))) := by
  -- Reduce to the general refutation lemma for `constraintSet = ∅`.
  simpa using
    (helperForTheorem_6_28_4_not_conclusion_of_constraintSet_eq_empty
      (P := helperForTheorem_6_28_4_counterexampleProgram 1)
      (uStar := fun i : Fin 0 => Fin.elim0 i)
      (x := fun _ : Fin 1 => 0)
      (hconstraint := rfl))

/-- Helper for Theorem 6.28.4: the current unconditional Lean statement of the theorem is false,
as witnessed by `helperForTheorem_6_28_4_counterexampleProgram 1`. -/
lemma helperForTheorem_6_28_4_statement_false :
    ¬ (∀ {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (uStar : Fin m → ℝ) (x : Fin n → ℝ),
        (((P.IsKuhnTuckerVector uStar ∧ P.IsOptimalSolution x) ↔
              P.IsLagrangianSaddlePoint uStar x) ∧
            (P.IsLagrangianSaddlePoint uStar x ↔
              P.SatisfiesKuhnTuckerPointConditions uStar x))) := by
  intro hall
  -- Specialize the alleged universal theorem statement to the in-file counterexample program.
  have hcounter :
      ((((helperForTheorem_6_28_4_counterexampleProgram 1).IsKuhnTuckerVector
              (fun i : Fin 0 => Fin.elim0 i)) ∧
            ((helperForTheorem_6_28_4_counterexampleProgram 1).IsOptimalSolution
              (fun _ : Fin 1 => 0))) ↔
          (helperForTheorem_6_28_4_counterexampleProgram 1).IsLagrangianSaddlePoint
            (fun i : Fin 0 => Fin.elim0 i) (fun _ : Fin 1 => 0)) ∧
        ((helperForTheorem_6_28_4_counterexampleProgram 1).IsLagrangianSaddlePoint
              (fun i : Fin 0 => Fin.elim0 i) (fun _ : Fin 1 => 0) ↔
          (helperForTheorem_6_28_4_counterexampleProgram 1).SatisfiesKuhnTuckerPointConditions
            (fun i : Fin 0 => Fin.elim0 i) (fun _ : Fin 1 => 0)) :=
    hall (P := helperForTheorem_6_28_4_counterexampleProgram 1)
      (uStar := fun i : Fin 0 => Fin.elim0 i) (x := fun _ : Fin 1 => 0)
  -- This contradicts the already-proved counterexample instance.
  exact helperForTheorem_6_28_4_counterexample_instance hcounter

/-- Helper for Theorem 6.28.4: an optimal solution identifies the `EReal` optimal value with the
objective value at that point. -/
lemma helperForTheorem_6_28_4_optimalValue_eq_objective_of_optimalSolution
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) {x : Fin n → ℝ}
    (hx : P.IsOptimalSolution x) :
    P.optimalValue = ((P.objective x : ℝ) : EReal) := by
  -- Expand `optimalValue` as an infimum over the feasible set and use the minimizing property.
  rcases hx with ⟨hxFeasible, hxMin⟩
  apply le_antisymm
  · -- The infimum is bounded above by the value at the minimizing point.
    rw [BookOrdinaryConvexProgram.optimalValue]
    exact sInf_le ⟨x, hxFeasible, rfl⟩
  · -- The minimizing point gives a lower bound for every element of the image set.
    rw [BookOrdinaryConvexProgram.optimalValue]
    refine le_sInf ?_
    rintro _ ⟨y, hyFeasible, rfl⟩
    exact EReal.coe_le_coe_iff.2 (hxMin y hyFeasible)

/-- Helper for Theorem 6.28.4: rewrite the Lagrangian in the three regimes dictated by
membership in the constraint set and multiplier set. -/
lemma helperForTheorem_6_28_4_lagrangian_simp
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (u : Fin m → ℝ) (x : Fin n → ℝ) :
    (x ∉ P.constraintSet → P.lagrangian u x = (⊤ : EReal)) ∧
      (x ∈ P.constraintSet → u ∉ P.lagrangeMultiplierSet → P.lagrangian u x = (⊥ : EReal)) ∧
      (x ∈ P.constraintSet → u ∈ P.lagrangeMultiplierSet →
        P.lagrangian u x = (P.kuhnTuckerObjective u x : EReal)) := by
  -- Each clause follows immediately by unfolding the defining `if`-chain.
  constructor
  · intro hx
    simp [BookOrdinaryConvexProgram.lagrangian, hx]
  constructor
  · intro hx hu
    simp [BookOrdinaryConvexProgram.lagrangian, hx, hu]
  · intro hx hu
    simp [BookOrdinaryConvexProgram.lagrangian, hx, hu]

/-- Helper for Theorem 6.28.4: when the multiplier belongs to `P.lagrangeMultiplierSet`, the
Lagrangian coincides with the indicator-extended Kuhn--Tucker objective. -/
lemma helperForTheorem_6_28_4_lagrangian_eq_extendedKuhnTuckerObjective_of_mem_lagrangeMultiplierSet
    {n m r : ℕ} (P : BookOrdinaryConvexProgram n m r) (u : Fin m → ℝ)
    (hu : u ∈ P.lagrangeMultiplierSet) (x : Fin n → ℝ) :
    P.lagrangian u x = P.extendedKuhnTuckerObjective u x := by
  -- Split on primal feasibility; on `C` both sides reduce to the real Kuhn--Tucker objective,
  -- while outside `C` both sides are `⊤`.
  by_cases hx : x ∈ P.constraintSet
  · simp [BookOrdinaryConvexProgram.lagrangian, BookOrdinaryConvexProgram.extendedKuhnTuckerObjective,
      hx, hu]
  · simp [BookOrdinaryConvexProgram.lagrangian, BookOrdinaryConvexProgram.extendedKuhnTuckerObjective,
      hx, hu]

/-- Helper for Theorem 6.28.4: the zero vector is a Euclidean subgradient exactly when the point
is a global minimizer, i.e. the function value is a pointwise lower bound. -/
lemma helperForTheorem_6_28_4_zero_mem_euclideanSubdifferentialAt_iff_pointwiseLowerBound
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) :
    (0 : Fin n → ℝ) ∈ euclideanSubdifferentialAt f x ↔
      ∀ z : Fin n → ℝ, f x ≤ f z := by
  -- Expand the Euclideanized subdifferential and specialize the subgradient inequality to the
  -- zero dual vector.
  constructor
  · intro h z
    -- Membership unfolds to the subgradient inequality for the zero functional.
    have hz0 :
        f z ≥ f x + (((dotProductEquiv ℝ (Fin n) (0 : Fin n → ℝ)) (z - x) : ℝ) : EReal) := by
      simpa [euclideanSubdifferentialAt, subdifferentialAt, IsSubgradientAt] using h z
    have hz : f z ≥ f x := by
      simpa using hz0
    simpa [ge_iff_le] using hz
  · intro h
    -- Show the corresponding dual vector is a subgradient at `x`.
    intro z
    have hz : f x ≤ f z := h z
    -- Repackage the lower bound into the subgradient inequality for the zero functional.
    have hz' : f z ≥ f x := by simpa [ge_iff_le] using hz
    simpa [euclideanSubdifferentialAt, subdifferentialAt, IsSubgradientAt] using hz'

end Section28
end Chap06

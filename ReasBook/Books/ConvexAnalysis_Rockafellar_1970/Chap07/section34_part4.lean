/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part3

section Chap07
section Section34

open Set

/-- Predicates on coordinate spaces in this section are treated classically when needed in
piecewise definitions. -/
noncomputable local instance classicalDecidablePredPart4 {α : Type*} (p : α → Prop) :
    DecidablePred p :=
  Classical.decPred p

section SaddleAmbient

variable {m n : ℕ}


/-- Helper for Text 34.1.4: once a Rockafellar convex bifunction represents `underline(K)`,
the full-domain branch of Section 33 yields the stronger inner-product equation against the
genuine adjoint pairing. -/


lemma helperForText_34_1_4_hasInnerProductEquation_of_lowerRepresentation
    {K : SaddleFunction m n} {h : IsConcaveConvex K}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hGraph : IsGraphConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    (hLowerNoBot : HasNoBotValuesBifunction (lowerClosureConcaveConvex K h))
    (hLowerRep : lowerClosureConcaveConvex K h = convexBifunctionPairing F) :
    HasInnerProductEquation F := by
  have hParamDom :
      (convexBifunctionDomains F).1 = Set.univ := by
    -- Rewrite the pair-valued Section 33 domain to the parameter-domain identity just proved.
    simpa [convexBifunctionDomains] using
      helperForText_34_1_4_parameterDomain_eq_univ_of_lowerRepresentation
        (K := K) (h := h) hLowerNoBot hLowerRep
  -- The full parameter domain triggers the stronger Section 33 duality package.
  exact
    innerProductEquation_of_fullDomain_or_closed_fullAdjointDomain hGraph hNoBot
      (Or.inl hParamDom)

/-- Helper for Text 34.1.4: any convex bifunction representing `underline(K)` already satisfies
the global closure-side pairing identity `⟪F u, x^*⟫ = ⟪u, F^* x^*⟫`. -/
lemma helperForText_34_1_4_pairingEquality_everywhere_of_lowerRepresentation
    {K : SaddleFunction m n} {h : IsConcaveConvex K}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hGraph : IsGraphConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    (hLowerNoBot : HasNoBotValuesBifunction (lowerClosureConcaveConvex K h))
    (hLowerRep : lowerClosureConcaveConvex K h = convexBifunctionPairing F) :
    ∀ u : Fin m → ℝ, ∀ xStar : Fin n → ℝ,
      convexBifunctionPairing F u xStar =
        convexBifunctionCanonicalAdjointPairing F xStar u := by
  intro u xStar
  have huInterior : u ∈ interior (Set.univ : Set (Fin m → ℝ)) := by
    simpa [interior_univ]
  have huII : u ∈ intrinsicInterior ℝ (Set.univ : Set (Fin m → ℝ)) :=
    (interior_subset_intrinsicInterior (s := (Set.univ : Set (Fin m → ℝ)))) huInterior
  have huDomain :
      u ∈ intrinsicInterior ℝ {u' : Fin m → ℝ | ∃ x : Fin n → ℝ, F u' x < ⊤} := by
    -- The witness representation makes the relative-interior parameter domain all of `ℝ^m`.
    simpa
      [helperForText_34_1_4_strictParameterDomain_eq_univ_of_lowerRepresentation
        (K := K) (h := h) hLowerNoBot hLowerRep] using huII
  -- Corollary 33.2.1 can now be applied at an arbitrary parameter point.
  exact
    ((adjoint_pairing_eq_on_relativeInterior_domains (m := m) (n := n)).1
      (F := F) ⟨hGraph, hNoBot⟩).1 huDomain xStar

/-- Helper for Text 34.1.4: the lower-representation inner-product equation can be derived
directly from a closed-convex witness, without any global no-`⊥` assumption on `underline(K)`. -/
lemma helperForText_34_1_4_hasInnerProductEquation_of_closedConvexLowerRepresentation
    {K : SaddleFunction m n} {h : IsConcaveConvex K}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hRock : IsRockafellarConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    (hClosed : ClosedConvexBifunction F)
    (hLowerRep : lowerClosureConcaveConvex K h = convexBifunctionPairing F)
    (hFiniteSections : ∀ u : Fin m → ℝ, ∃ x : Fin n → ℝ, F u x < (⊤ : EReal)) :
    HasInnerProductEquation F := by
  have hLowerNoBot :
      HasNoBotValuesBifunction (lowerClosureConcaveConvex K h) :=
    helperForText_34_1_4_lowerClosure_hasNoBot_of_closedConvexLowerRepresentation
      (K := K) (h := h) hRock hNoBot hClosed hLowerRep
        hFiniteSections
  have hGraph : IsGraphConvexBifunction F :=
    (helperForCorollary33_3_1_rockafellarConvex_and_graphFunctionClosed_of_closedConvexWitness
      (F := F) hClosed hNoBot).1
  exact
    helperForText_34_1_4_hasInnerProductEquation_of_lowerRepresentation
      (K := K) (h := h) hGraph hNoBot hLowerNoBot hLowerRep

/-- Helper for Text 34.1.4: the lower-representation pairing equality can likewise be derived
from an actual closed-convex witness, without assuming `underline(K)` is globally no-`⊥`. -/
lemma helperForText_34_1_4_pairingEquality_everywhere_of_closedConvexLowerRepresentation
    {K : SaddleFunction m n} {h : IsConcaveConvex K}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hRock : IsRockafellarConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    (hClosed : ClosedConvexBifunction F)
    (hLowerRep : lowerClosureConcaveConvex K h = convexBifunctionPairing F)
    (hFiniteSections : ∀ u : Fin m → ℝ, ∃ x : Fin n → ℝ, F u x < (⊤ : EReal)) :
    ∀ u : Fin m → ℝ, ∀ xStar : Fin n → ℝ,
      convexBifunctionPairing F u xStar =
        convexBifunctionCanonicalAdjointPairing F xStar u := by
  have hLowerNoBot :
      HasNoBotValuesBifunction (lowerClosureConcaveConvex K h) :=
    helperForText_34_1_4_lowerClosure_hasNoBot_of_closedConvexLowerRepresentation
      (K := K) (h := h) hRock hNoBot hClosed hLowerRep
        hFiniteSections
  have hGraph : IsGraphConvexBifunction F :=
    (helperForCorollary33_3_1_rockafellarConvex_and_graphFunctionClosed_of_closedConvexWitness
      (F := F) hClosed hNoBot).1
  exact
    helperForText_34_1_4_pairingEquality_everywhere_of_lowerRepresentation
      (K := K) (h := h) hGraph hNoBot hLowerNoBot hLowerRep

/-- Helper for Text 34.1.4: a closed convex bifunction witness is already graph-convex, because
closedness makes every section fixed by the one-variable convex closure and Rockafellar convexity
then upgrades to joint graph convexity. -/
lemma helperForText_34_1_4_graphConvex_of_closedConvexBifunction
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hRock : IsRockafellarConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    (hClosed : ClosedConvexBifunction F) :
    IsGraphConvexBifunction F := by
  have hGraphClosed :
      IsFunctionConvexClosed (graphFunctionOfBifunction F) :=
    -- Closedness of the graph function is the reusable bridge from the bifunction package to
    -- the raw Section 33 graph-closure operator.
    helperForText_34_1_4_graphFunction_isFunctionConvexClosed_of_closedConvexBifunction hClosed
  have hSectionClosed :
      ∀ u : Fin m → ℝ, IsFunctionConvexClosed (F u) :=
    -- Each primal section inherits convex closedness from the closed graph.
    helperForLemma33_0_22_section_isFunctionConvexClosed hGraphClosed
  have hClosureExact :
      ∀ u x, convexFunctionClosure (F u) x = F u x := by
    intro u x
    -- Rewriting through `functionConvexClosure` exposes the exact fixed-point formula.
    calc
      convexFunctionClosure (F u) x = functionConvexClosure (F u) x := by
        rw [← helperForTheorem33_1_functionConvexClosure_eq_convexFunctionClosure_of_noBot
          (hNoBot := hNoBot u)]
      _ = F u x := helperForLemma33_0_18_functionConvexClosure_eq_self (hSectionClosed u) x
  -- The exact sectionwise closure formulas are exactly the hypotheses of the graph-convexity
  -- theorem from Section 33.
  exact
    helperForLemma33_0_14_graphConvex_of_rockafellar_with_exactSectionwiseClosure
      (F := F) hRock hClosureExact hNoBot

/-- Helper for Text 34.1.4: a genuine lower self-representation already forces equality of the
translated-and-tilted primal and dual optimal values for the fixed witness. -/
lemma helperForText_34_1_4_equalOptimalValues_for_translatedTiltedPrograms_of_genuineLowerSelfRepresentation
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hRock : IsRockafellarConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    (hClosed : ClosedConvexBifunction F)
    (hLowerRep : lowerClosureConcaveConvex K h = convexBifunctionPairing F)
    (hGenuineSelfRep :
      ∀ u : Fin m → ℝ, ∀ xStar : Fin n → ℝ,
        lowerClosureConcaveConvex K h u xStar =
          genuineConvexBifunctionAdjointPairing F u xStar) :
    ∀ u : Fin m → ℝ, ∀ xStar : Fin n → ℝ,
      HasEqualOptimalValuesForTranslatedTiltedPrograms F u xStar := by
  have hGraphConvex : IsGraphConvexBifunction F :=
    -- The fixed witness is graph-convex once its closed-convex package is unpacked.
    helperForText_34_1_4_graphConvex_of_closedConvexBifunction hRock hNoBot hClosed
  intro u xStar
  have hPairingEq :
      convexBifunctionPairing F u xStar =
        genuineConvexBifunctionAdjointPairing F u xStar := by
    -- The lower representation identifies the left-hand pairing with `underline(K)`, and the
    -- genuine self-representation identifies the same point of `underline(K)` with the right
    -- adjoint-side pairing.
    calc
      convexBifunctionPairing F u xStar = lowerClosureConcaveConvex K h u xStar := by
        simpa using congrArg (fun G => G u xStar) hLowerRep.symm
      _ = genuineConvexBifunctionAdjointPairing F u xStar := hGenuineSelfRep u xStar
  -- Section 33 rewrites this pointwise pairing equality as equality of translated-tilted
  -- optimal values.
  exact
    (pairingEquality_iff_equalOptimalValues_for_translatedTiltedPrograms F hGraphConvex u xStar).1
      hPairingEq

/-- Helper for Text 34.1.4: the same genuine lower self-representation makes every
translated-and-tilted program normal for the fixed witness. -/
lemma helperForText_34_1_4_normality_for_translatedTiltedPrograms_of_genuineLowerSelfRepresentation
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hRock : IsRockafellarConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    (hClosed : ClosedConvexBifunction F)
    (hLowerRep : lowerClosureConcaveConvex K h = convexBifunctionPairing F)
    (hGenuineSelfRep :
      ∀ u : Fin m → ℝ, ∀ xStar : Fin n → ℝ,
        lowerClosureConcaveConvex K h u xStar =
          genuineConvexBifunctionAdjointPairing F u xStar) :
    ∀ u : Fin m → ℝ, ∀ xStar : Fin n → ℝ,
      HasNormalityForTranslatedTiltedPrograms F u xStar := by
  intro u xStar
  have hEqualValues :
      HasEqualOptimalValuesForTranslatedTiltedPrograms F u xStar :=
    -- Reuse the translated-tilted optimal-value equality just proved from the witness package.
    helperForText_34_1_4_equalOptimalValues_for_translatedTiltedPrograms_of_genuineLowerSelfRepresentation
      K h hRock hNoBot hClosed hLowerRep hGenuineSelfRep u xStar
  -- Section 33 identifies optimal-value equality with normality for the translated programs.
  exact (normality_iff_equalOptimalValues_for_translatedTiltedPrograms F u xStar).2 hEqualValues

/-- Helper for Text 34.1.4: exact recovery of `cl₂ overline(K)` identifies the textbook upper
closure with the canonical partner `cl₁ underline(K)`. -/
lemma helperForText_34_1_4_firstClosureOfLower_eq_upper_of_secondClosure_eq_lower
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBotK : HasNoBotValuesBifunction K)
    (hRecover :
      partialClosure₂ (upperClosureConcaveConvex K h) = lowerClosureConcaveConvex K h) :
    partialClosure₁ (lowerClosureConcaveConvex K h) = upperClosureConcaveConvex K h := by
  -- First use Corollary 33.3.2 to identify the unique lower partner attached to
  -- `overline(K)`.
  rcases helperForText_34_1_4_upperClosure_uniqueLowerClosedPartner K h hNoBotK with
    ⟨L', hL', -⟩
  have hL'eq : L' = lowerClosureConcaveConvex K h := by
    calc
      L' = partialClosure₂ (upperClosureConcaveConvex K h) := by
        symm
        exact hL'.2.2.2
      _ = lowerClosureConcaveConvex K h := hRecover
  -- Then rewrite the recovered lower partner back into the textbook lower closure.
  calc
    partialClosure₁ (lowerClosureConcaveConvex K h) = partialClosure₁ L' := by
      rw [hL'eq]
    _ = upperClosureConcaveConvex K h := hL'.2.2.1.symm

/-- Helper for Text 34.1.4: once `overline(K)` is identified with the canonical upper partner
`cl₁ underline(K)`, the Section 33 witness for that canonical pair is exactly the desired
witness for the textbook lower and upper closures. -/
lemma helperForText_34_1_4_closedConvexWitness_exists_of_firstClosureOfLower_eq_upper_of_noTopOrBot
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hKNoBot : HasNoBotValuesBifunction K)
    (hLowerNoTopBot :
      HasNoTopOrBotValuesBifunction (lowerClosureConcaveConvex K h))
    (hFirst :
      partialClosure₁ (lowerClosureConcaveConvex K h) = upperClosureConcaveConvex K h)
    (hRealization : Section34CanonicalClosureRealizationQualification m n) :
    ∃ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      IsRockafellarConvexBifunction F ∧
        HasNoBotValuesBifunction F ∧
        ClosedConvexBifunction F ∧
        lowerClosureConcaveConvex K h = convexBifunctionPairing F ∧
        upperClosureConcaveConvex K h =
          helperForText_34_0_1_convexAdjointPairingKernel F := by
  rcases
      helperForText_34_1_4_closedConvexWitness_exists_for_canonicalUpperPartner K h
        hKNoBot hLowerNoTopBot hRealization with
    ⟨F, hClosed, hNoBot, hLowerRep, hCanonicalUpperRep⟩
  have hRock : IsRockafellarConvexBifunction F := by
    have hGraphConvex : IsGraphConvexBifunction F := by
      have hGraphConvexFunction : ConvexFunction (graphFunctionOfBifunction F) := by
        simpa [ClosedConvexBifunction, ConvexBifunction, bifunctionGraphFunction,
          graphFunctionOfBifunction] using hClosed.1
      have hGraphNoBot :
          ∀ z : Fin (m + n) → ℝ, graphFunctionOfBifunction F z ≠ (⊥ : EReal) := by
        intro z
        simpa [graphFunctionOfBifunction] using
          hNoBot (fun i : Fin m => z (Fin.castAdd n i))
            (fun j : Fin n => z (Fin.natAdd m j))
      exact
        helperForLemma33_0_5_convexFunction_to_isERealConvexOn_univ
          (f := graphFunctionOfBifunction F) hGraphConvexFunction hGraphNoBot
    exact helperForLemma33_0_22_graphConvex_gives_rockafellarConvex hGraphConvex
  refine ⟨F, hRock, hNoBot, hClosed, hLowerRep, ?_⟩
  calc
    upperClosureConcaveConvex K h = partialClosure₁ (lowerClosureConcaveConvex K h) :=
      hFirst.symm
    _ = helperForText_34_0_1_convexAdjointPairingKernel F := hCanonicalUpperRep

/-- Corrected interface for Text 34.1.4: under the necessary no-`⊤`/no-`⊥` hypothesis on
`underline(K)`, the exact recovery identity `cl₂ overline(K) = underline(K)` already yields the
closed-convex witness for the textbook pair. -/
lemma helperForText_34_1_4_closedConvexWitness_exists_of_secondClosure_eq_lower_of_noTopOrBot
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBotK : HasNoBotValuesBifunction K)
    (hLowerNoTopBot :
      HasNoTopOrBotValuesBifunction (lowerClosureConcaveConvex K h))
    (hRecover :
      partialClosure₂ (upperClosureConcaveConvex K h) = lowerClosureConcaveConvex K h)
    (hRealization : Section34CanonicalClosureRealizationQualification m n) :
    ∃ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      IsRockafellarConvexBifunction F ∧
        HasNoBotValuesBifunction F ∧
        ClosedConvexBifunction F ∧
        lowerClosureConcaveConvex K h = convexBifunctionPairing F ∧
        upperClosureConcaveConvex K h =
          helperForText_34_0_1_convexAdjointPairingKernel F := by
  exact
    helperForText_34_1_4_closedConvexWitness_exists_of_firstClosureOfLower_eq_upper_of_noTopOrBot
      K h hNoBotK hLowerNoTopBot
      (helperForText_34_1_4_firstClosureOfLower_eq_upper_of_secondClosure_eq_lower
        K h hNoBotK hRecover) hRealization

/-- Corrected interface for Text 34.1.4: under the necessary no-`⊤`/no-`⊥` hypothesis on
`underline(K)`, the textbook witness condition is equivalent to `cl₁ underline(K) = overline(K)`.
-/
lemma helperForText_34_1_4_closedConvexWitness_exists_iff_firstClosureOfLower_eq_upper_of_noTopOrBot
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBotK : HasNoBotValuesBifunction K)
    (hLowerNoTopBot :
      HasNoTopOrBotValuesBifunction (lowerClosureConcaveConvex K h))
    (hRealization : Section34CanonicalClosureRealizationQualification m n) :
    (∃ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      IsRockafellarConvexBifunction F ∧
        HasNoBotValuesBifunction F ∧
        ClosedConvexBifunction F ∧
        lowerClosureConcaveConvex K h = convexBifunctionPairing F ∧
        upperClosureConcaveConvex K h =
          helperForText_34_0_1_convexAdjointPairingKernel F) ↔
      partialClosure₁ (lowerClosureConcaveConvex K h) = upperClosureConcaveConvex K h := by
  constructor
  · intro hWitness
    rcases hWitness with ⟨F, hF, hNoBot, hClosed, hLowerRep, hUpperRep⟩
    exact
      (helperForText_34_0_1_closedConvexWitness_forces_crossClosure_relations_of_function_equalities
        (K := K) (h := h) hF hNoBot hClosed hLowerRep hUpperRep hLowerNoTopBot).1
  · intro hFirst
    exact
      helperForText_34_1_4_closedConvexWitness_exists_of_firstClosureOfLower_eq_upper_of_noTopOrBot
        K h hNoBotK hLowerNoTopBot hFirst hRealization

/-- Corrected interface for Text 34.1.4: under the necessary no-`⊤`/no-`⊥` hypothesis on
`underline(K)`, the textbook witness condition is equivalent to `cl₂ overline(K) = underline(K)`.
-/
lemma helperForText_34_1_4_closedConvexWitness_exists_iff_secondClosure_eq_lower_of_noTopOrBot
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBotK : HasNoBotValuesBifunction K)
    (hLowerNoTopBot :
      HasNoTopOrBotValuesBifunction (lowerClosureConcaveConvex K h))
    (hRealization : Section34CanonicalClosureRealizationQualification m n) :
    (∃ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      IsRockafellarConvexBifunction F ∧
        HasNoBotValuesBifunction F ∧
        ClosedConvexBifunction F ∧
        lowerClosureConcaveConvex K h = convexBifunctionPairing F ∧
        upperClosureConcaveConvex K h =
          helperForText_34_0_1_convexAdjointPairingKernel F) ↔
      partialClosure₂ (upperClosureConcaveConvex K h) = lowerClosureConcaveConvex K h := by
  constructor
  · intro hWitness
    rcases hWitness with ⟨F, hF, hNoBot, hClosed, hLowerRep, hUpperRep⟩
    exact
      (helperForText_34_0_1_closedConvexWitness_forces_crossClosure_relations_of_function_equalities
        (K := K) (h := h) hF hNoBot hClosed hLowerRep hUpperRep hLowerNoTopBot).2
  · intro hRecover
    exact
      helperForText_34_1_4_closedConvexWitness_exists_of_secondClosure_eq_lower_of_noTopOrBot
        K h hNoBotK hLowerNoTopBot hRecover hRealization

/-- Corrected interface for Text 34.1.4: under the necessary no-`⊤`/no-`⊥` hypothesis on
`underline(K)`, the textbook witness condition is equivalent to the raw mixed-order inequality
`cl₂ (cl₁ K) ≤ cl₁ (cl₂ K)`. -/
lemma helperForText_34_1_4_closedConvexWitness_exists_iff_rawMixedClosureOrder_of_noTopOrBot
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBotK : HasNoBotValuesBifunction K)
    (hLowerNoTopBot :
      HasNoTopOrBotValuesBifunction (lowerClosureConcaveConvex K h))
    (hRealization : Section34CanonicalClosureRealizationQualification m n) :
    (∃ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      IsRockafellarConvexBifunction F ∧
        HasNoBotValuesBifunction F ∧
        ClosedConvexBifunction F ∧
        lowerClosureConcaveConvex K h = convexBifunctionPairing F ∧
        upperClosureConcaveConvex K h =
          helperForText_34_0_1_convexAdjointPairingKernel F) ↔
      partialClosure₂ (partialClosure₁ K) ≤ partialClosure₁ (partialClosure₂ K) := by
  constructor
  · intro hWitness
    rcases hWitness with ⟨F, hF, hNoBot, hClosed, hLowerRep, hUpperRep⟩
    have hOrder :
        lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h := by
      calc
        lowerClosureConcaveConvex K h ≤ partialClosure₁ (lowerClosureConcaveConvex K h) :=
          helperForText_34_1_4_lowerClosure_below_canonicalUpperPartner K h
        _ = upperClosureConcaveConvex K h := by
          exact
            (helperForText_34_0_1_closedConvexWitness_forces_crossClosure_relations_of_function_equalities
              (K := K) (h := h) hF hNoBot hClosed hLowerRep hUpperRep hLowerNoTopBot).1
    exact (helperForText_34_1_4_mixedClosure_order_iff_rawMixedClosureOrder K h).1 hOrder
  · intro hRawOrder
    have hOrder :
        lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h :=
      (helperForText_34_1_4_mixedClosure_order_iff_rawMixedClosureOrder K h).2 hRawOrder
    exact
      helperForText_34_1_4_closedConvexWitness_exists_of_firstClosureOfLower_eq_upper_of_noTopOrBot
        K h hNoBotK hLowerNoTopBot
        (helperForText_34_1_4_firstClosureOfLower_eq_upper_of_secondClosure_eq_lower K h
          hNoBotK
          (helperForText_34_1_4_secondClosureOfUpper_eq_lower_of_mixedClosure_order K h
            hNoBotK hOrder)) hRealization

end SaddleAmbient

end Section34
end Chap07

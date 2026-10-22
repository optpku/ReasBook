/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part18

section Chap07
section Section33

attribute [local instance] Classical.propDecidable

/-- Corollary33.0.40 (Sufficient conditions for the global pairing identity):
the primal pairing and genuine-adjoint pairing agree everywhere if either the primal domain
is full, or the graph function is convex-closed and the genuine adjoint domain is full. -/
theorem innerProductEquation_of_fullDomain_or_closed_fullAdjointDomain :
    ∀ {m n : ℕ} {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal},
      IsGraphConvexBifunction F →
        HasNoBotValuesBifunction F →
          ((convexBifunctionDomains F).1 = Set.univ ∨
              IsFunctionConvexClosed (graphFunctionOfBifunction F) ∧
                (convexBifunctionDomains F).2 = Set.univ) →
            HasInnerProductEquation F :=
  fun {m n} {F} hF_convex hF_noBot hcases => by
    intro u xStar
    rcases hcases with hDom | hClosedAdj
    · -- Step 1: in the full primal-domain branch, the fixed-dual pairing section is already
      -- equal to its concave closure everywhere, so the genuine pairing collapses to the
      -- original primal pairing.
      exact
        (helperForCorollary33_0_40_pairing_eq_genuinePairing_of_fullParameterDomain
          (F := F) hF_convex hF_noBot hDom u xStar).symm
    · rcases hClosedAdj with ⟨hGraphClosed, hAdjDom⟩
      -- Step 2: in the closed-graph branch, split into the nontrivial witness case and the
      -- everywhere-`⊤` degeneration; both routes still collapse the genuine pairing.
      exact
        (helperForCorollary33_0_40_pairing_eq_genuinePairing_of_closed_fullGenuineAdjointDomain
          (F := F) hF_convex hF_noBot hGraphClosed hAdjDom u xStar).symm

/-- Helper for Corollary33.0.41: a proper first convex-bifunction domain component omits
some primal parameter. -/
lemma helperForCorollary33_0_41_exists_off_first_domain
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hdom : (convexBifunctionDomains F).1 ≠ Set.univ) :
    ∃ u : Fin m → ℝ, u ∉ (convexBifunctionDomains F).1 := by
  -- Step 1: if every primal parameter lay in the first domain component, that component
  -- would coincide with all of space.
  have hNotAll :
      ¬ ∀ u : Fin m → ℝ, u ∈ (convexBifunctionDomains F).1 := by
    intro hAll
    apply hdom
    ext u
    simp [hAll u]
  -- Step 2: convert the negated universal statement into the required witness.
  exact not_forall.mp hNotAll

/-- Helper for Corollary33.0.41: a proper second convex-bifunction domain component omits
some dual vector. -/
lemma helperForCorollary33_0_41_exists_off_second_domain
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hdomAdj : (convexBifunctionDomains F).2 ≠ Set.univ) :
    ∃ xStar : Fin n → ℝ, xStar ∉ (convexBifunctionDomains F).2 := by
  -- Step 1: if every dual vector lay in the second domain component, that component would
  -- already be all of space.
  have hNotAll :
      ¬ ∀ xStar : Fin n → ℝ, xStar ∈ (convexBifunctionDomains F).2 := by
    intro hAll
    apply hdomAdj
    ext xStar
    simp [hAll xStar]
  -- Step 2: extract the required off-domain witness.
  exact not_forall.mp hNotAll

/-- Helper for Corollary33.0.41: the inner-product equation fails at any point lying outside
both convex-bifunction domain components. -/
lemma helperForCorollary33_0_41_contradiction_at_off_domain_point
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ}
    {xStar : Fin n → ℝ}
    (hInner : HasInnerProductEquation F)
    (huOutside : u ∉ (convexBifunctionDomains F).1)
    (hxOutside : xStar ∉ (convexBifunctionDomains F).2) :
    False := by
  -- Step 1: the obstruction theorem forces the two pairings to take opposite infinite
  -- values at any point off both domain components.
  have hCollapse :=
    oppositeInfinities_off_both_convexBifunctionDomains
      (F := F) (u := u) (xStar := xStar) huOutside hxOutside
  have hPairingBot :
      convexBifunctionPairing F u xStar = ⊥ := hCollapse.2.2.1
  have hAdjointTop :
      genuineConvexBifunctionAdjointPairing F u xStar = ⊤ := hCollapse.2.2.2
  -- Step 2: specializing the claimed global equality at the same point yields `⊥ = ⊤`.
  have hEq :
      convexBifunctionPairing F u xStar =
        genuineConvexBifunctionAdjointPairing F u xStar :=
    hInner u xStar
  rw [hPairingBot, hAdjointTop] at hEq
  exact bot_ne_top hEq

/-- Corollary33.0.41 (Failure when both domains are not full):
if neither the primal domain nor the genuine adjoint domain is all of space, then the
global pairing identity cannot hold. -/
theorem not_hasInnerProductEquation_of_nonfull_domains :
    ∀ {m n : ℕ} {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal},
      (convexBifunctionDomains F).1 ≠ Set.univ →
        (convexBifunctionDomains F).2 ≠ Set.univ → ¬HasInnerProductEquation F :=
  fun {m n} {F} hdom hdomAdj => by
    intro hInner
    -- Step 1: choose witnesses outside the two proper domain components.
    rcases helperForCorollary33_0_41_exists_off_first_domain (F := F) hdom with
      ⟨u, huOutside⟩
    rcases helperForCorollary33_0_41_exists_off_second_domain (F := F) hdomAdj with
      ⟨xStar, hxOutside⟩
    -- Step 2: the global pairing identity now contradicts the opposite-infinities
    -- obstruction at the chosen off-domain point.
    exact
      helperForCorollary33_0_41_contradiction_at_off_domain_point
        (F := F) (u := u) (xStar := xStar) hInner huOutside hxOutside

/-- Helper for Theorem33.0.39: the genuine inner-product equation forces at least one of the
two domain components to be all of space. -/
lemma helperForTheorem33_0_39_domainDichotomy_of_innerProductEquation
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hInner : HasInnerProductEquation F) :
    (convexBifunctionDomains F).1 = Set.univ ∨
      (convexBifunctionDomains F).2 = Set.univ := by
  -- Step 1: split on the first domain component; if it is already full we are done.
  by_cases hDom : (convexBifunctionDomains F).1 = Set.univ
  · exact Or.inl hDom
  -- Step 2: otherwise split on the second component and reuse the obstruction theorem.
  · by_cases hAdjDom : (convexBifunctionDomains F).2 = Set.univ
    · exact Or.inr hAdjDom
    · exfalso
      exact
        not_hasInnerProductEquation_of_nonfull_domains
          (F := F) hDom hAdjDom hInner

-- Route correction: in the current `EReal` formalization, this split file records only the
-- sound witness-to-closure direction of Corollary33.3.1; the raw converse needs the later
-- no-top/no-bot refinement and is not proved here.
/-- Helper for Corollary33.3.1: a closed convex witness with no `⊥` values already supplies
the Rockafellar convexity and graph-closure data needed by the coordinatewise-closure
machinery. -/
lemma helperForCorollary33_3_1_rockafellarConvex_and_graphFunctionClosed_of_closedConvexWitness
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hClosed : ClosedConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F) :
    IsGraphConvexBifunction F ∧
      IsFunctionConvexClosed (graphFunctionOfBifunction F) := by
  -- Step 1: read graph convexity from the closed convex bifunction package and promote it to
  -- the Rockafellar convexity predicate.
  have hGraphConvex : IsGraphConvexBifunction F := by
    have hGraphConvexFunction : ConvexFunction (graphFunctionOfBifunction F) := by
      simpa [ClosedConvexBifunction, ConvexBifunction, bifunctionGraphFunction,
        graphFunctionOfBifunction] using hClosed.1
    have hGraphNeBot :
        ∀ z : Fin (m + n) → ℝ, graphFunctionOfBifunction F z ≠ (⊥ : EReal) := by
      intro z
      simpa [graphFunctionOfBifunction] using
        hNoBot (fun i : Fin m => z (Fin.castAdd n i))
          (fun j : Fin n => z (Fin.natAdd m j))
    exact
      helperForLemma33_0_5_convexFunction_to_isERealConvexOn_univ
        (f := graphFunctionOfBifunction F) hGraphConvexFunction hGraphNeBot
  -- Step 2: extract lower semicontinuity of the graph function from closedness, then turn it
  -- into the fixed-point graph-closure identity required in Section 33.
  have hGraphLsc : LowerSemicontinuous (graphFunctionOfBifunction F) := by
    simpa [bifunctionGraphFunction, graphFunctionOfBifunction] using hClosed.2.2
  have hGraphClosed : IsFunctionConvexClosed (graphFunctionOfBifunction F) :=
    helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous hGraphLsc
  exact ⟨hGraphConvex, hGraphClosed⟩

/-- Canonical Chapter 2 closure in the first (concave) coordinate.  This is kept distinct
from the older ball-based raw closure, which need not agree on improper sections. -/
noncomputable def canonicalConcaveClosureInFirst {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun u xStar => concaveClosure (fun u' => K u' xStar) u

/-- Canonical Chapter 2 closure in the second (convex) coordinate. -/
noncomputable def canonicalConvexClosureInSecond {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun u xStar => convexFunctionClosure (fun y => K u y) xStar

/-- Helper for Corollary33.3.1: a closed convex bifunction witness with no `⊥` values forces
the canonical coordinatewise closure identities for the represented pairing kernels. -/
lemma helperForCorollary33_3_1_coordinatewise_closure_pair_of_closedConvexWitness
    {m n : ℕ}
    {K Kbar : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hClosed : ClosedConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    (hPair : ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
      K u xStar = convexBifunctionPairing F u xStar)
    (hAdj : ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
      Kbar u xStar = convexBifunctionCanonicalAdjointPairing F xStar u) :
    Kbar = canonicalConcaveClosureInFirst K ∧
      canonicalConvexClosureInSecond Kbar = K := by
  -- Step 1: recover the Rockafellar convexity and graph-closure hypotheses from the witness,
  -- then specialize Theorem 33.2 to its two closure identities.
  rcases
      helperForCorollary33_3_1_rockafellarConvex_and_graphFunctionClosed_of_closedConvexWitness
        (F := F) hClosed hNoBot with
    ⟨hGraph, hGraphClosed⟩
  rcases
      (adjoint_pairing_eq_coordinatewise_closures (m := m) (n := n)).1 F
        ⟨hGraph, hNoBot⟩ with
    ⟨hFirst, hSecond⟩
  constructor
  · -- Step 2: rewrite the adjoint pairing through the first coordinatewise closure formula
    -- and then substitute the represented primal pairing kernel.
    funext u
    funext xStar
    calc
      Kbar u xStar = convexBifunctionCanonicalAdjointPairing F xStar u := hAdj u xStar
      _ = concaveClosure (fun u' => convexBifunctionPairing F u' xStar) u :=
        hFirst xStar u
      _ = concaveClosure (fun u' => K u' xStar) u := by
        congr with u'
        exact (hPair u' xStar).symm
      _ = canonicalConcaveClosureInFirst K u xStar := by
        rfl
  · -- Step 3: apply the second coordinatewise closure formula and collapse the graph closure
    -- pairing back to the original witness using the closedness of the graph function.
    funext u
    funext xStar
    calc
      canonicalConvexClosureInSecond Kbar u xStar
          = convexFunctionClosure (fun xStar' => Kbar u xStar') xStar := by
              rfl
      _ =
          convexFunctionClosure
            (fun xStar' => convexBifunctionCanonicalAdjointPairing F xStar' u) xStar := by
              congr with xStar'
              exact hAdj u xStar'
      _ = convexBifunctionPairing (convexBifunctionClosure F) u xStar := hSecond u xStar
      _ = convexBifunctionPairing F u xStar := by
            exact
              helperForCorollary33_2_1_convexClosure_pairing_eq_self_of_closed
                (F := F) hGraph hNoBot hGraphClosed u xStar
      _ = K u xStar := (hPair u xStar).symm

/-- Helper for Corollary33.3.1: the forward implication only uses the packaged closed convex
witness data, so it can be invoked directly from the existential interface used in the
corollary statement. -/
lemma helperForCorollary33_3_1_coordinatewise_closure_pair_of_closedConvexWitnessPackage
    {m n : ℕ}
    {K Kbar : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hWitness :
      ClosedConvexBifunction F ∧
        HasNoBotValuesBifunction F ∧
        (∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
          K u xStar = convexBifunctionPairing F u xStar) ∧
          ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
            Kbar u xStar = convexBifunctionCanonicalAdjointPairing F xStar u) :
    Kbar = canonicalConcaveClosureInFirst K ∧
      canonicalConvexClosureInSecond Kbar = K := by
  -- Step 1: unpack the existential-style witness package into the previously proved data.
  rcases hWitness with ⟨hClosed, hNoBot, hPair, hAdj⟩
  -- Step 2: apply the direct witness-to-closure helper proved just above.
  exact
    helperForCorollary33_3_1_coordinatewise_closure_pair_of_closedConvexWitness
      (F := F) hClosed hNoBot hPair hAdj

/-- Helper for Corollary33.3.1: the unique-existence hypothesis in the corollary statement
still yields the same coordinatewise closure pair after discarding uniqueness. -/
lemma helperForCorollary33_3_1_coordinatewise_closure_pair_of_closedConvexUniqueWitness
    {m n : ℕ}
    {K Kbar : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hExists :
      ∃! F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
        ClosedConvexBifunction F ∧
          HasNoBotValuesBifunction F ∧
          (∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
            K u xStar = convexBifunctionPairing F u xStar) ∧
            ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
              Kbar u xStar = convexBifunctionCanonicalAdjointPairing F xStar u) :
    Kbar = canonicalConcaveClosureInFirst K ∧
      canonicalConvexClosureInSecond Kbar = K := by
  -- Step 1: unique existence still provides a concrete closed convex witness.
  rcases hExists with ⟨F, hF, -⟩
  -- Step 2: uniqueness is irrelevant for the forward implication, so reduce to the
  -- packaged-witness helper.
  exact
    helperForCorollary33_3_1_coordinatewise_closure_pair_of_closedConvexWitnessPackage
      (F := F) hF

-- Route correction: the actual `Corollary33.3.2` theorem is declared in `section33_part23`,
-- but the sectionwise orientation facts it uses are dependency-closed already at this stage.
/-- Helper for Corollary33.3.2: simultaneous concave-convex and convex-concave structure on a
kernel makes every first-variable section simultaneously concave and convex. -/
lemma helperForCorollary33_3_2_firstVariableSection_isConcaveAndConvex_of_simultaneousOrientations
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK : IsConcaveConvexOn Set.univ Set.univ K)
    (hVC : IsConvexConcaveOn Set.univ Set.univ K)
    (xStar : Fin n → ℝ) :
    IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) (fun u => K u xStar) ∧
      IsERealConvexOn (Set.univ : Set (Fin m → ℝ)) (fun u => K u xStar) := by
  -- Step 1: `xStar` belongs to the full second-variable domain, so the concave-convex
  -- hypothesis specializes to concavity of the frozen first-variable section.
  have hxStar_mem : xStar ∈ (Set.univ : Set (Fin n → ℝ)) := by
    simp
  have hConcSection :
      IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) (fun u => K u xStar) :=
    hK.1 xStar hxStar_mem
  -- Step 2: the same full-domain membership lets the convex-concave hypothesis produce
  -- convexity of the frozen first-variable section.
  have hConvSection :
      IsERealConvexOn (Set.univ : Set (Fin m → ℝ)) (fun u => K u xStar) :=
    hVC.1 xStar hxStar_mem
  exact ⟨hConcSection, hConvSection⟩

/-- Helper for Corollary33.3.2: simultaneous concave-convex and convex-concave structure on a
kernel makes every second-variable section simultaneously convex and concave. -/
lemma helperForCorollary33_3_2_secondVariableSection_isConvexAndConcave_of_simultaneousOrientations
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK : IsConcaveConvexOn Set.univ Set.univ K)
    (hVC : IsConvexConcaveOn Set.univ Set.univ K)
    (u : Fin m → ℝ) :
    IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) (fun xStar => K u xStar) ∧
      IsERealConcaveOn (Set.univ : Set (Fin n → ℝ)) (fun xStar => K u xStar) := by
  -- Step 1: `u` belongs to the full first-variable domain, so the concave-convex
  -- hypothesis specializes to convexity of the frozen second-variable section.
  have hu_mem : u ∈ (Set.univ : Set (Fin m → ℝ)) := by
    simp
  have hConvSection :
      IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) (fun xStar => K u xStar) :=
    hK.2 u hu_mem
  -- Step 2: the same full-domain membership lets the convex-concave hypothesis produce
  -- concavity of the frozen second-variable section.
  have hConcSection :
      IsERealConcaveOn (Set.univ : Set (Fin n → ℝ)) (fun xStar => K u xStar) :=
    hVC.2 u hu_mem
  exact ⟨hConvSection, hConcSection⟩

/-- Helper for Corollary33.3.2: the simultaneous orientation hypotheses package the
first-variable section orientations uniformly over all frozen dual vectors. -/
lemma helperForCorollary33_3_2_allFirstVariableSections_areConcaveAndConvex
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK : IsConcaveConvexOn Set.univ Set.univ K)
    (hVC : IsConvexConcaveOn Set.univ Set.univ K) :
    ∀ xStar : Fin n → ℝ,
      IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) (fun u => K u xStar) ∧
        IsERealConvexOn (Set.univ : Set (Fin m → ℝ)) (fun u => K u xStar) := by
  -- Step 1: fix a dual vector and reduce to the one-section orientation lemma already proved.
  intro xStar
  exact
    helperForCorollary33_3_2_firstVariableSection_isConcaveAndConvex_of_simultaneousOrientations
      (K := K) hK hVC xStar

/-- Helper for Corollary33.3.2: the simultaneous orientation hypotheses package the
second-variable section orientations uniformly over all frozen primal vectors. -/
lemma helperForCorollary33_3_2_allSecondVariableSections_areConvexAndConcave
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK : IsConcaveConvexOn Set.univ Set.univ K)
    (hVC : IsConvexConcaveOn Set.univ Set.univ K) :
    ∀ u : Fin m → ℝ,
      IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) (fun xStar => K u xStar) ∧
        IsERealConcaveOn (Set.univ : Set (Fin n → ℝ)) (fun xStar => K u xStar) := by
  -- Step 1: fix a primal vector and reduce to the one-section orientation lemma already proved.
  intro u
  exact
    helperForCorollary33_3_2_secondVariableSection_isConvexAndConcave_of_simultaneousOrientations
      (K := K) hK hVC u

/-- Helper for Corollary33.3.2: simultaneous concave-convex and convex-concave structure on a
kernel packages both first-variable and second-variable section orientations at once. -/
lemma helperForCorollary33_3_2_allSections_have_simultaneousOrientations
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK : IsConcaveConvexOn Set.univ Set.univ K)
    (hVC : IsConvexConcaveOn Set.univ Set.univ K) :
    (∀ xStar : Fin n → ℝ,
      IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) (fun u => K u xStar) ∧
        IsERealConvexOn (Set.univ : Set (Fin m → ℝ)) (fun u => K u xStar)) ∧
      ∀ u : Fin m → ℝ,
        IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) (fun xStar => K u xStar) ∧
          IsERealConcaveOn (Set.univ : Set (Fin n → ℝ)) (fun xStar => K u xStar) := by
  constructor
  · -- Step 1: use the uniform first-variable packaging lemma to obtain all frozen first
    -- sections at once.
    exact
      helperForCorollary33_3_2_allFirstVariableSections_areConcaveAndConvex
        (K := K) hK hVC
  · -- Step 2: use the uniform second-variable packaging lemma to obtain all frozen second
    -- sections at once.
    exact
      helperForCorollary33_3_2_allSecondVariableSections_areConvexAndConcave
        (K := K) hK hVC

-- Route correction: the actual `Corollary33.3.3` theorem is introduced only in the later
-- split file, but the real-kernel finiteness and simple-extension facts it uses are already
-- available from the dependency-closed definitions imported here.
/-- Helper for Corollary33.3.3: a real-valued kernel, viewed in `EReal`, satisfies both
one-sided finiteness conventions required by the saddle-function correspondence. -/
lemma helperForCorollary33_3_3_realKernel_hasNoTopOrBotValues
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ} :
    HasNoTopOrBotValuesBifunction (fun u xStar => (↑(K u xStar) : EReal)) := by
  constructor
  · -- Step 1: coercions from `ℝ` to `EReal` never hit the lower infinite endpoint.
    intro u xStar
    exact EReal.coe_ne_bot (K u xStar)
  · -- Step 2: the same coercions also avoid the upper infinite endpoint.
    intro u xStar
    exact EReal.coe_ne_top (K u xStar)

/-- Helper for Corollary33.3.3: every lower simple extension lies pointwise below the
corresponding upper simple extension. -/
lemma helperForCorollary33_3_3_lowerSimpleExtension_le_upperSimpleExtension
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal} :
    ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
      lowerSimpleExtension C D K u xStar ≤ upperSimpleExtension C D K u xStar := by
  intro u xStar
  -- Step 1: split on the two membership tests controlling the simple-extension formulas.
  by_cases hu : u ∈ C
  · by_cases hxStar : xStar ∈ D
    · -- Step 2: on `C × D`, both extensions reduce to `K`.
      simp [lowerSimpleExtension, upperSimpleExtension, hu, hxStar]
    · -- Step 2: on `C × Dᶜ`, both extensions reduce to `⊤`.
      simp [lowerSimpleExtension, upperSimpleExtension, hu, hxStar]
  · by_cases hxStar : xStar ∈ D
    · -- Step 2: on `Cᶜ × D`, both extensions reduce to `⊥`.
      simp [lowerSimpleExtension, upperSimpleExtension, hu, hxStar]
    · -- Step 2: on `Cᶜ × Dᶜ`, the lower extension is `⊥` and the upper extension is `⊤`.
      simp [lowerSimpleExtension, upperSimpleExtension, hu, hxStar]

/-- Helper for Corollary33.3.3: on `C × D`, the simple extensions of a real-valued kernel
agree with the original kernel after coercion to `EReal`. -/
lemma helperForCorollary33_3_3_simpleExtensions_of_real_agree_on_product
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {u : Fin m → ℝ}
    {xStar : Fin n → ℝ}
    (hu : u ∈ C)
    (hxStar : xStar ∈ D) :
    lowerSimpleExtension C D (fun u' xStar' => (↑(K u' xStar') : EReal)) u xStar =
        ↑(K u xStar) ∧
      upperSimpleExtension C D (fun u' xStar' => (↑(K u' xStar') : EReal)) u xStar =
        ↑(K u xStar) := by
  -- Step 1: this is exactly the general agreement-on-product lemma specialized to the
  -- `EReal` coercion of the real-valued kernel.
  simpa using
    (simpleExtensions_eq_on_product
      (C := C) (D := D) (K := fun u' xStar' => (↑(K u' xStar') : EReal))
      (u := u) (v := xStar) hu hxStar)

/-- Helper for Corollary33.3.3: the `EReal` simple extensions of a real kernel are globally
ordered, and on `C × D` they both reduce to the original real kernel after coercion. -/
lemma helperForCorollary33_3_3_realKernel_simpleExtensions_areOrdered_and_agreeOnProduct
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ} :
    (∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
      lowerSimpleExtension C D (fun u' xStar' => (↑(K u' xStar') : EReal)) u xStar ≤
        upperSimpleExtension C D (fun u' xStar' => (↑(K u' xStar') : EReal)) u xStar) ∧
      ∀ ⦃u : Fin m → ℝ⦄ ⦃xStar : Fin n → ℝ⦄,
        u ∈ C →
          xStar ∈ D →
            lowerSimpleExtension C D (fun u' xStar' => (↑(K u' xStar') : EReal)) u xStar =
                ↑(K u xStar) ∧
              upperSimpleExtension C D (fun u' xStar' => (↑(K u' xStar') : EReal)) u xStar =
                ↑(K u xStar) := by
  constructor
  · -- Step 1: the global order is exactly the general lower-versus-upper comparison
    -- specialized to the coerced real-valued kernel.
    intro u xStar
    exact
      helperForCorollary33_3_3_lowerSimpleExtension_le_upperSimpleExtension
        (C := C) (D := D) (K := fun u' xStar' => (↑(K u' xStar') : EReal)) u xStar
  · -- Step 2: on the product `C × D`, the earlier agreement lemma identifies both simple
    -- extensions with the original real kernel inside `EReal`.
    intro u xStar hu hxStar
    exact
      helperForCorollary33_3_3_simpleExtensions_of_real_agree_on_product
        (C := C) (D := D) (K := K) hu hxStar

structure SaddleClosednessPredicates {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Type where
  lowerClosed : Prop
  upperClosed : Prop

def saddleClosednessPredicates : {m n : ℕ} →
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) → SaddleClosednessPredicates K :=
  fun {_ _} K =>
    {
      lowerClosed :=
        IsConcaveConvexOn Set.univ Set.univ K ∧
            convexClosureInSecond (concaveClosureInFirst K) = K ∨
          IsConvexConcaveOn Set.univ Set.univ K ∧
            convexClosureInFirst (concaveClosureInSecond K) = K,
      upperClosed :=
        IsConcaveConvexOn Set.univ Set.univ K ∧
            concaveClosureInFirst (convexClosureInSecond K) = K ∨
          IsConvexConcaveOn Set.univ Set.univ K ∧
            concaveClosureInSecond (convexClosureInFirst K) = K }

@[reducible] def IsLowerClosedSaddleFunction : {m n : ℕ} →
    ((Fin m → ℝ) → (Fin n → ℝ) → EReal) → Prop :=
  fun {_ _} K => (saddleClosednessPredicates K).lowerClosed

@[reducible] def IsUpperClosedSaddleFunction : {m n : ℕ} →
    ((Fin m → ℝ) → (Fin n → ℝ) → EReal) → Prop :=
  fun {_ _} K => (saddleClosednessPredicates K).upperClosed

/-- Helper for Corollary33.3.3: once the lower and upper simple extensions are identified as
the expected coordinatewise closure pair, their lower-closedness, upper-closedness, and
pointwise order follow formally from the Section 33 closure machinery already available in this
split file. -/
lemma helperForCorollary33_3_3_closurePair_implies_closedness_and_order
    {m n : ℕ}
    {K1 K2 : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK1 : IsConcaveConvexOn Set.univ Set.univ K1)
    (hK2 : IsConcaveConvexOn Set.univ Set.univ K2)
    (hPair : K2 = concaveClosureInFirst K1 ∧ convexClosureInSecond K2 = K1) :
    IsLowerClosedSaddleFunction K1 ∧
      IsUpperClosedSaddleFunction K2 ∧
        ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ), K1 u xStar ≤ K2 u xStar := by
  rcases hPair with ⟨hFirst, hSecond⟩
  -- Step 1: the mixed closure identities already force the aligned lower and upper closure
  -- compositions together with the global comparison `K1 ≤ K2`.
  have hLowerComp :
      convexClosureInSecond (concaveClosureInFirst K1) = K1 :=
    helperForCorollary33_3_1_coordinatewise_closure_pair_implies_lowerClosureComposition
      (K := K1) (Kbar := K2) hFirst hSecond
  have hUpperComp :
      concaveClosureInFirst (convexClosureInSecond K2) = K2 :=
    helperForCorollary33_3_1_coordinatewise_closure_pair_implies_upperClosureComposition
      (K := K1) (Kbar := K2) hFirst hSecond
  have hOrder :
      ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ), K1 u xStar ≤ K2 u xStar :=
    helperForCorollary33_3_1_coordinatewise_closure_pair_implies_pointwise_le
      (K := K1) (Kbar := K2) hFirst hSecond
  -- Step 2: package the aligned lower composition into the concave-convex branch of the
  -- lower-closed predicate.
  have hLower : IsLowerClosedSaddleFunction K1 := by
    dsimp [IsLowerClosedSaddleFunction, saddleClosednessPredicates]
    exact Or.inl ⟨hK1, hLowerComp⟩
  -- Step 3: package the aligned upper composition into the concave-convex branch of the
  -- upper-closed predicate for the upper simple extension.
  have hUpper : IsUpperClosedSaddleFunction K2 := by
    dsimp [IsUpperClosedSaddleFunction, saddleClosednessPredicates]
    exact Or.inl ⟨hK2, hUpperComp⟩
  exact ⟨hLower, hUpper, hOrder⟩

def erealOfRealBifunction : {m n : ℕ} →
    ((Fin m → ℝ) → (Fin n → ℝ) → ℝ) → (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun {_ _} K u xStar => ↑(K u xStar)

@[reducible] noncomputable def lowerSimpleExtensionOfReal : {m n : ℕ} →
    Set (Fin m → ℝ) → Set (Fin n → ℝ) → ((Fin m → ℝ) → (Fin n → ℝ) → ℝ) →
      (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun {_ _} C D K => lowerSimpleExtension C D (erealOfRealBifunction K)

@[reducible] noncomputable def upperSimpleExtensionOfReal : {m n : ℕ} →
    Set (Fin m → ℝ) → Set (Fin n → ℝ) → ((Fin m → ℝ) → (Fin n → ℝ) → ℝ) →
      (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun {_ _} C D K => upperSimpleExtension C D (erealOfRealBifunction K)

/-- Helper for Corollary33.3.3: the lower simple extension of a real-valued kernel has
exactly the original primal constraint set as the locus where some value is not `⊥`. -/
lemma helperForCorollary33_3_3_lowerSimpleExtensionOfReal_nonbotSlice_set_eq
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hD_nonempty : D.Nonempty) :
    {u : Fin m → ℝ | ∃ xStar : Fin n → ℝ, lowerSimpleExtensionOfReal C D K u xStar ≠ ⊥} = C := by
  ext u
  constructor
  · intro hu
    -- Step 1: outside `C`, the lower simple extension is identically `⊥`, so any non-`⊥`
    -- witness forces the parameter back into the constraint set.
    by_contra huNot
    rcases hu with ⟨xStar, hxStar⟩
    have hValue : lowerSimpleExtensionOfReal C D K u xStar = ⊥ := by
      simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, huNot]
    exact hxStar hValue
  · intro hu
    -- Step 2: inside `C`, choose any dual point in `D`; on that product point the lower
    -- simple extension is a finite real value, hence not `⊥`.
    rcases hD_nonempty with ⟨xStar, hxStar⟩
    refine ⟨xStar, ?_⟩
    have hValue :
        lowerSimpleExtensionOfReal C D K u xStar = ↑(K u xStar) := by
      simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, hu, hxStar, erealOfRealBifunction]
    rw [hValue]
    exact EReal.coe_ne_bot (K u xStar)

/-- Helper for Corollary33.3.3: the upper simple extension of a real-valued kernel has exactly
the original dual constraint set as the locus where some value is not `⊤`. -/
lemma helperForCorollary33_3_3_upperSimpleExtensionOfReal_nontopSlice_set_eq
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_nonempty : C.Nonempty) :
    {xStar : Fin n → ℝ | ∃ u : Fin m → ℝ, upperSimpleExtensionOfReal C D K u xStar ≠ ⊤} = D := by
  ext xStar
  constructor
  · intro hxStar_mem
    -- Step 1: outside `D`, the upper simple extension is identically `⊤`, so any non-`⊤`
    -- witness forces the dual point back into the constraint set.
    by_contra hxStar_not_mem
    rcases hxStar_mem with ⟨u, hu⟩
    have hValue : upperSimpleExtensionOfReal C D K u xStar = ⊤ := by
      simp [upperSimpleExtensionOfReal, upperSimpleExtension, hxStar_not_mem]
    exact hu hValue
  · intro hxStar_mem
    -- Step 2: inside `D`, choose any primal point in `C`; on that product point the upper
    -- simple extension is a finite real value, hence not `⊤`.
    rcases hC_nonempty with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    have hValue :
        upperSimpleExtensionOfReal C D K u xStar = ↑(K u xStar) := by
      simp [upperSimpleExtensionOfReal, upperSimpleExtension, hu, hxStar_mem, erealOfRealBifunction]
    rw [hValue]
    exact EReal.coe_ne_top (K u xStar)

/-- Helper for Corollary33.3.3: the two real-valued simple extensions recover exactly the
original primal and dual constraint sets as their non-infinite slice domains. -/
lemma helperForCorollary33_3_3_simpleExtension_sliceDomains_eq_constraints
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_nonempty : C.Nonempty)
    (hD_nonempty : D.Nonempty) :
    ({u : Fin m → ℝ | ∃ xStar : Fin n → ℝ, lowerSimpleExtensionOfReal C D K u xStar ≠ ⊥} = C) ∧
      ({xStar : Fin n → ℝ | ∃ u : Fin m → ℝ, upperSimpleExtensionOfReal C D K u xStar ≠ ⊤} = D) := by
  constructor
  · -- Step 1: the lower simple extension sees exactly the primal constraint set through its
    -- non-`⊥` slices.
    exact
      helperForCorollary33_3_3_lowerSimpleExtensionOfReal_nonbotSlice_set_eq
        (C := C) (D := D) (K := K) hD_nonempty
  · -- Step 2: the upper simple extension likewise sees exactly the dual constraint set
    -- through its non-`⊤` slices.
    exact
      helperForCorollary33_3_3_upperSimpleExtensionOfReal_nontopSlice_set_eq
        (C := C) (D := D) (K := K) hC_nonempty

/-- Helper for Corollary33.3.3: outside the primal constraint set `C`, the upper simple
extension freezes to the top/bottom indicator of the dual constraint set `D`. -/
lemma helperForCorollary33_3_3_upperSimpleExtensionOfReal_offParameterSection
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {u : Fin m → ℝ}
    (hu : u ∉ C) :
    upperSimpleExtensionOfReal C D K u =
      fun xStar : Fin n → ℝ => if xStar ∈ D then (⊥ : EReal) else ⊤ := by
  -- Step 1: once `u` is outside `C`, the real kernel never appears in the upper extension.
  funext xStar
  by_cases hxStar : xStar ∈ D
  · -- Step 2: on `D`, the off-`C` section is constantly `⊥`.
    simp [upperSimpleExtensionOfReal, upperSimpleExtension, hu, hxStar]
  · -- Step 3: off `D`, the same section is constantly `⊤`.
    simp [upperSimpleExtensionOfReal, upperSimpleExtension, hxStar]

/-- Helper for Corollary33.3.3: an off-`C` section of the upper simple extension attains `⊥`
on `D` and `⊤` off `D`. -/
lemma helperForCorollary33_3_3_upperSimpleExtensionOfReal_offParameterSection_mixedValues
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {u : Fin m → ℝ}
    (hu : u ∉ C)
    {xIn xOut : Fin n → ℝ}
    (hxIn : xIn ∈ D)
    (hxOut : xOut ∉ D) :
    upperSimpleExtensionOfReal C D K u xIn = (⊥ : EReal) ∧
      upperSimpleExtensionOfReal C D K u xOut = (⊤ : EReal) := by
  -- Step 1: rewrite the whole off-`C` section by the indicator-shape formula.
  have hSection :=
    helperForCorollary33_3_3_upperSimpleExtensionOfReal_offParameterSection
      (C := C) (D := D) (K := K) hu
  constructor
  · -- Step 2: evaluate the rewritten section on a dual point lying in `D`.
    simpa [hxIn] using congrArg (fun g => g xIn) hSection
  · -- Step 3: evaluate it again on a dual point lying outside `D`.
    simpa [hxOut] using congrArg (fun g => g xOut) hSection

/-- Helper for Corollary33.3.3: if one primal point lies in `C`, another lies outside `C`,
and their midpoint returns to `C`, then freezing the upper simple extension at a dual point of
`D` produces a first-variable section that is not convex on all of `ℝ^m`. -/
lemma helperForCorollary33_3_3_upperSimpleExtensionOfReal_onDualSection_not_convexOn_univ
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {xStar : Fin n → ℝ}
    (hxStar : xStar ∈ D)
    {uIn uOut : Fin m → ℝ}
    (_huIn : uIn ∈ C)
    (huOut : uOut ∉ C)
    (hMidIn : (1 / 2 : ℝ) • uIn + (1 / 2 : ℝ) • uOut ∈ C) :
    ¬ IsERealConvexOn (Set.univ : Set (Fin m → ℝ))
      (fun u => upperSimpleExtensionOfReal C D K u xStar) := by
  intro hConv
  have hMidIn' : ((2⁻¹ : ℝ) • uIn + (2⁻¹ : ℝ) • uOut) ∈ C := by
    simpa using hMidIn
  have hHalfNonneg : 0 ≤ (1 / 2 : ℝ) := by
    norm_num
  have hHalfAdd : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by
    norm_num
  have hJensen :=
    hConv (x := uIn) (y := uOut) (by simp) (by simp)
      hHalfNonneg hHalfNonneg hHalfAdd (by simp)
  have hMidFinite :
      upperSimpleExtensionOfReal C D K ((1 / 2 : ℝ) • uIn + (1 / 2 : ℝ) • uOut) xStar =
        ↑(K ((1 / 2 : ℝ) • uIn + (1 / 2 : ℝ) • uOut) xStar) := by
    -- Step 1: at a midpoint returning to `C`, the frozen section is a finite real value.
    simp [upperSimpleExtensionOfReal, upperSimpleExtension, erealOfRealBifunction, hMidIn', hxStar]
  have hOutBot : upperSimpleExtensionOfReal C D K uOut xStar = (⊥ : EReal) := by
    -- Step 2: the out-of-`C` endpoint collapses to `⊥`.
    simp [upperSimpleExtensionOfReal, upperSimpleExtension, huOut, hxStar]
  have hLeBot :
      (↑(K ((1 / 2 : ℝ) • uIn + (1 / 2 : ℝ) • uOut) xStar) : EReal) ≤ (⊥ : EReal) := by
    -- Step 3: Jensen bounds the finite midpoint value by a right-hand side whose second
    -- term is a positive multiple of `⊥`, so the whole right-hand side collapses to `⊥`.
    have hHalfPos : 0 < (1 / 2 : ℝ) := by
      norm_num
    have hScaledBot : ((1 / 2 : EReal) * (⊥ : EReal)) = (⊥ : EReal) := by
      simpa using (EReal.coe_mul_bot_of_pos hHalfPos :
        (((1 / 2 : ℝ) : EReal) * (⊥ : EReal)) = (⊥ : EReal))
    have hRightBot :
        ((1 / 2 : EReal) * upperSimpleExtensionOfReal C D K uIn xStar +
          (1 / 2 : EReal) * upperSimpleExtensionOfReal C D K uOut xStar) = (⊥ : EReal) := by
      calc
        ((1 / 2 : EReal) * upperSimpleExtensionOfReal C D K uIn xStar +
            (1 / 2 : EReal) * upperSimpleExtensionOfReal C D K uOut xStar)
            = ((1 / 2 : EReal) * upperSimpleExtensionOfReal C D K uIn xStar +
                (1 / 2 : EReal) * (⊥ : EReal)) := by
                  rw [hOutBot]
        _ = ((1 / 2 : EReal) * upperSimpleExtensionOfReal C D K uIn xStar + ⊥) := by
              rw [hScaledBot]
        _ = ⊥ := by
              rw [EReal.add_bot]
    calc
      (↑(K ((1 / 2 : ℝ) • uIn + (1 / 2 : ℝ) • uOut) xStar) : EReal)
          = upperSimpleExtensionOfReal C D K ((1 / 2 : ℝ) • uIn + (1 / 2 : ℝ) • uOut) xStar := by
              exact hMidFinite.symm
      _ ≤
          ((1 / 2 : EReal) * upperSimpleExtensionOfReal C D K uIn xStar +
            (1 / 2 : EReal) * upperSimpleExtensionOfReal C D K uOut xStar) := by
              simpa using hJensen
      _ = ⊥ := hRightBot
  exact EReal.coe_ne_bot _ (le_bot_iff.mp hLeBot)

/-- Helper for Corollary33.3.3: the midpoint witness above already rules out the
convex-concave orientation for the upper simple extension on all of `ℝ^m × ℝ^n`. -/
lemma helperForCorollary33_3_3_upperSimpleExtensionOfReal_not_convexConcaveOn_univ_of_midpoint_witness
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {xStar : Fin n → ℝ}
    (hxStar : xStar ∈ D)
    {uIn uOut : Fin m → ℝ}
    (huIn : uIn ∈ C)
    (huOut : uOut ∉ C)
    (hMidIn : (1 / 2 : ℝ) • uIn + (1 / 2 : ℝ) • uOut ∈ C) :
    ¬ IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
      (upperSimpleExtensionOfReal C D K) := by
  intro hConvexConcave
  exact
    helperForCorollary33_3_3_upperSimpleExtensionOfReal_onDualSection_not_convexOn_univ
      (C := C) (D := D) (K := K) (xStar := xStar) hxStar huIn huOut hMidIn
      (hConvexConcave.1 xStar (by simp))

/-- Helper for Corollary33.3.3: once the midpoint witness rules out the global
convex-concave orientation of the upper simple extension, the right-hand branch in the
definition of `IsUpperClosedSaddleFunction` is impossible as well. -/
lemma helperForCorollary33_3_3_upperSimpleExtensionOfReal_convexConcaveUpperClosedBranch_impossible_of_midpoint_witness
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {xStar : Fin n → ℝ}
    (hxStar : xStar ∈ D)
    {uIn uOut : Fin m → ℝ}
    (huIn : uIn ∈ C)
    (huOut : uOut ∉ C)
    (hMidIn : (1 / 2 : ℝ) • uIn + (1 / 2 : ℝ) • uOut ∈ C) :
    ¬ (IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
          (upperSimpleExtensionOfReal C D K) ∧
        concaveClosureInSecond (convexClosureInFirst (upperSimpleExtensionOfReal C D K)) =
          upperSimpleExtensionOfReal C D K) := by
  intro hUpperBranch
  -- Step 1: the closure identity carried by the right-hand upper-closed branch is irrelevant
  -- once the midpoint witness has already ruled out the required convex-concave shape.
  exact
    helperForCorollary33_3_3_upperSimpleExtensionOfReal_not_convexConcaveOn_univ_of_midpoint_witness
      (C := C) (D := D) (K := K) (xStar := xStar) hxStar huIn huOut hMidIn hUpperBranch.1

/-- Helper for Corollary33.3.3: any proof of upper closedness must choose one of the two
closure branches, so refuting both branches separately refutes upper closedness itself. -/
lemma helperForCorollary33_3_3_not_upperClosed_of_branch_obstructions
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hLeft :
      ¬ (IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K ∧
          concaveClosureInFirst (convexClosureInSecond K) = K))
    (hRight :
      ¬ (IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K ∧
          concaveClosureInSecond (convexClosureInFirst K) = K)) :
    ¬ IsUpperClosedSaddleFunction K := by
  intro hUpperClosed
  -- Step 1: unfold the disjunctive definition of upper closedness and discharge each branch
  -- with the corresponding obstruction hypothesis.
  rcases hUpperClosed with hUpperLeft | hUpperRight
  · exact hLeft hUpperLeft
  · exact hRight hUpperRight

/-- Helper for Corollary33.3.3: the canonical witness is obtained by taking the sectionwise
convex conjugate of the lower simple extension. -/
@[reducible] noncomputable def helperForCorollary33_3_3_canonicalWitness
    {m n : ℕ}
    (C : Set (Fin m → ℝ))
    (D : Set (Fin n → ℝ))
    (K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun u x => convexConjugate (lowerSimpleExtensionOfReal C D K u) x

/-- Helper for Corollary33.3.3: the canonical witness has the textbook primal supremum
formula. -/
lemma helperForCorollary33_3_3_canonicalWitness_primalFormula
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (u : Fin m → ℝ)
    (x : Fin n → ℝ) :
    helperForCorollary33_3_3_canonicalWitness C D K u x =
      if _ : u ∈ C then
        sSup (Set.range fun xStar : D => ↑(x ⬝ᵥ ↑xStar - K u ↑xStar))
      else ⊤ := by
  -- Step 1: outside `C`, the lower simple extension section is constantly `⊥`, so its
  -- convex conjugate is constantly `⊤`.
  by_cases hu : u ∈ C
  · -- Step 2: on `C`, rewrite the lower simple extension section as the finite kernel on `D`
    -- and `⊤` outside, then invoke the Chapter 12 restricted-supremum conjugate formula.
    have hMain :
        helperForCorollary33_3_3_canonicalWitness C D K u x =
          sSup (Set.range fun xStar : D => ↑(x ⬝ᵥ ↑xStar - K u ↑xStar)) := by
      rw [helperForCorollary33_3_3_canonicalWitness]
      rw [helperForTheorem33_1_convexConjugate_eq_fenchelConjugate]
      have hFenchel :=
        fenchelConjugate_if_eq_sSup_image n
          (fun xStar : Fin n → ℝ => (↑(K u xStar) : EReal)) D x
      have hSection :
          lowerSimpleExtensionOfReal C D K u =
            fun xStar : Fin n → ℝ =>
              if xStar ∈ D then (↑(K u xStar) : EReal) else ⊤ := by
        funext xStar
        simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, hu, erealOfRealBifunction]
      have hFenchel' :
          fenchelConjugate n (lowerSimpleExtensionOfReal C D K u) x =
            sSup ((fun xStar : Fin n → ℝ => ((x ⬝ᵥ xStar : ℝ) : EReal) - ↑(K u xStar)) '' D) := by
        simpa [hSection, dotProduct_comm] using hFenchel
      rw [hFenchel']
      have hRangeEq :
          (fun xStar : Fin n → ℝ => ((x ⬝ᵥ xStar : ℝ) : EReal) - ↑(K u xStar)) '' D =
            Set.range fun xStar : D => ↑(x ⬝ᵥ ↑xStar - K u ↑xStar) := by
        ext y
        constructor
        · rintro ⟨xStar, hxStar, rfl⟩
          refine ⟨⟨xStar, hxStar⟩, ?_⟩
          exact (EReal.coe_sub (x ⬝ᵥ xStar) (K u xStar)).symm
        · rintro ⟨xStar, rfl⟩
          refine ⟨↑xStar, xStar.2, ?_⟩
          exact EReal.coe_sub (x ⬝ᵥ ↑xStar) (K u ↑xStar)
      rw [hRangeEq]
    simpa [hu] using hMain
  · -- Step 2: after unfolding the conjugate definition, every term in the defining supremum
    -- is `⊥`, so the whole supremum collapses to `⊤`.
    have hMain : helperForCorollary33_3_3_canonicalWitness C D K u x = ⊤ := by
      rw [helperForCorollary33_3_3_canonicalWitness, convexConjugate, fenchelConjugate_eq_iSup]
      apply top_unique
      have hTerm :
          (((0 : Fin n → ℝ) ⬝ᵥ x : ℝ) : EReal) - lowerSimpleExtensionOfReal C D K u 0 = ⊤ := by
        simp [lowerSimpleExtensionOfReal, lowerSimpleExtension, hu]
      calc
        (⊤ : EReal)
            = (((0 : Fin n → ℝ) ⬝ᵥ x : ℝ) : EReal) - lowerSimpleExtensionOfReal C D K u 0 :=
              hTerm.symm
        _ ≤
            iSup (fun xStar : Fin n → ℝ =>
              (((xStar ⬝ᵥ x : ℝ) : EReal) - lowerSimpleExtensionOfReal C D K u xStar)) := by
                exact
                  le_iSup
                    (fun xStar : Fin n → ℝ =>
                      (((xStar ⬝ᵥ x : ℝ) : EReal) - lowerSimpleExtensionOfReal C D K u xStar))
                    0
    simpa [hu] using hMain

/-- Helper for Corollary33.3.3: outside the primal constraint set `C`, the canonical witness
section is constantly `⊤`. -/
lemma helperForCorollary33_3_3_canonicalWitness_offParameterSection
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {u : Fin m → ℝ}
    (hu : u ∉ C) :
    helperForCorollary33_3_3_canonicalWitness C D K u = fun _ : Fin n → ℝ => (⊤ : EReal) := by
  -- Step 1: evaluate the explicit primal formula pointwise and collapse the off-domain branch.
  funext x
  have hFormula :=
    helperForCorollary33_3_3_canonicalWitness_primalFormula
      (C := C) (D := D) (K := K) u x
  simpa [hu] using hFormula

/-- Helper for Corollary33.3.3: the canonical witness never takes the value `⊥`. -/
lemma helperForCorollary33_3_3_canonicalWitness_hasNoBotValues
    {m n : ℕ}
    {C : Set (Fin m → ℝ)}
    {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hD_nonempty : D.Nonempty) :
    HasNoBotValuesBifunction (helperForCorollary33_3_3_canonicalWitness C D K) := by
  intro u x
  -- Step 1: use the explicit primal formula to split into the on-domain and off-domain
  -- branches for the parameter `u`.
  by_cases hu : u ∈ C
  · have hFormula :=
      helperForCorollary33_3_3_canonicalWitness_primalFormula
        (C := C) (D := D) (K := K) u x
    have hFormula' :
        helperForCorollary33_3_3_canonicalWitness C D K u x =
          sSup (Set.range fun xStar : D => ↑(x ⬝ᵥ ↑xStar - K u ↑xStar)) := by
      simpa [hu] using hFormula
    rw [hFormula']
    rcases hD_nonempty with ⟨xStar, hxStar⟩
    have hMem :
        (↑(x ⬝ᵥ xStar - K u xStar) : EReal) ∈
          Set.range (fun xStar : D => (↑(x ⬝ᵥ ↑xStar - K u ↑xStar) : EReal)) := by
      refine ⟨⟨xStar, hxStar⟩, ?_⟩
      rfl
    intro hBot
    have hLe : (↑(x ⬝ᵥ xStar - K u xStar) : EReal) ≤ (⊥ : EReal) := by
      rw [← hBot]
      exact le_sSup hMem
    exact not_le_of_gt (EReal.bot_lt_coe (x ⬝ᵥ xStar - K u xStar)) hLe
  · -- Step 2: off `C`, the new sectionwise helper shows the witness is constantly `⊤`.
    have hSection :=
      helperForCorollary33_3_3_canonicalWitness_offParameterSection
        (C := C) (D := D) (K := K) hu
    have hFormula' : helperForCorollary33_3_3_canonicalWitness C D K u x = ⊤ := by
      simpa using congrArg (fun g => g x) hSection
    rw [hFormula']
    exact top_ne_bot


end Section33
end Chap07

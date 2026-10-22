/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part14

section Chap07
section Section33

attribute [local instance] classicalSetDecidablePred
attribute [local instance] Classical.propDecidable

/-- The graph-function notion of concavity for a bifunction. -/
def IsGraphConcaveBifunction {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  IsERealConcaveOn (Set.univ : Set (Fin (m + n) → ℝ)) (graphFunctionOfBifunction F)

/-- The canonical pairing attached to the graph adjoint of a convex bifunction.

The current Section 33 adjoint pairing is the parameter-side conjugate of the raw pairing;
the book's closure identity uses its second parameter-side conjugate. -/
noncomputable abbrev convexBifunctionCanonicalAdjointPairing {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (xStar : Fin n → ℝ) (u : Fin m → ℝ) : EReal :=
  concaveConjugate (convexBifunctionAdjointPairing F xStar) u

/-- The canonical pairing attached to the graph adjoint of a concave bifunction. -/
noncomputable abbrev concaveBifunctionCanonicalAdjointPairing {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (xStar : Fin n → ℝ) (u : Fin m → ℝ) : EReal :=
  convexConjugate (concaveBifunctionAdjointPairing F xStar) u

/-- The Section 33 convex adjoint is the Chapter 6 adjoint after the graph-convex
hypothesis is repackaged as a `ConvexBifunction`. -/
lemma helperForTheorem33_2_convexAdjoint_eq_adjointOfConvex
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : ConvexBifunction F)
    (xStar : Fin n → ℝ) (uStar : Fin m → ℝ) :
    convexBifunctionAdjointPairing F xStar uStar =
      adjointOfConvexBifunction ⟨F, hF⟩ xStar uStar := by
  rw [convexBifunctionAdjointPairing,
    helperForTheorem_6_30_4_concaveConjugate_eq_iInf]
  have hPairingSection :
      ∀ u : Fin m → ℝ,
        -convexBifunctionPairing F u xStar =
          iInf (fun x : Fin n → ℝ => F u x - ((dotProduct x xStar : ℝ) : EReal)) := by
    intro u
    have h :=
      helperForCorollary33_1_3_sInf_tiltedFiber_eq_negSup_pairing (F := F) u xStar
    simpa [graphFunctionOfBifunction, sInf_range] using h.symm
  calc
    iInf (fun u : Fin m → ℝ =>
        (((u ⬝ᵥ uStar : ℝ) : EReal)) + -convexBifunctionPairing F u xStar)
        = iInf (fun u : Fin m → ℝ =>
            iInf (fun x : Fin n → ℝ => F u x - (((x ⬝ᵥ xStar : ℝ) : EReal))) +
              (((u ⬝ᵥ uStar : ℝ) : EReal))) := by
            congr with u
            rw [hPairingSection u]
            simpa [add_comm] using
              (helperForTheorem_6_30_15_real_add_iInf (c := (u ⬝ᵥ uStar : ℝ))
                (f := fun x : Fin n → ℝ => F u x - (((x ⬝ᵥ xStar : ℝ) : EReal)))).symm
    _ = iInf (fun u : Fin m → ℝ =>
          iInf (fun x : Fin n → ℝ =>
            F u x - (((x ⬝ᵥ xStar : ℝ) : EReal)) +
              (((u ⬝ᵥ uStar : ℝ) : EReal)))) := by
          congr with u
          simpa [add_comm, add_left_comm, add_assoc] using
            (helperForTheorem_6_30_15_real_add_iInf (c := (u ⬝ᵥ uStar : ℝ))
              (f := fun x : Fin n → ℝ => F u x - (((x ⬝ᵥ xStar : ℝ) : EReal))))
    _ = iInf (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
          F p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) +
            (((p.1 ⬝ᵥ uStar : ℝ) : EReal))) := by
          exact (helperForTheorem_6_30_22_iInf_prod_eq_nested
            (H := fun (u : Fin m → ℝ) (x : Fin n → ℝ) =>
              F u x - (((x ⬝ᵥ xStar : ℝ) : EReal)) +
                (((u ⬝ᵥ uStar : ℝ) : EReal)))).symm
    _ = adjointOfConvexBifunction ⟨F, hF⟩ xStar uStar := by
          simp [adjointOfConvexBifunction, sInf_range]

/-- Conjugating a fixed-parameter concave pairing produces the Chapter 6 adjoint. -/
lemma helperForTheorem33_2_convexConjugate_concavePairing_eq_adjointOfConcave
    {m n : ℕ}
    {G : (Fin n → ℝ) → (Fin m → ℝ) → EReal}
    (hG : ConcaveBifunction G)
    (u : Fin m → ℝ) (x : Fin n → ℝ) :
    convexConjugate
        (fun xStar : Fin n → ℝ => concaveBifunctionPairing G xStar u) x =
      adjointOfConcaveBifunction ⟨G, hG⟩ u x := by
  calc
    convexConjugate
        (fun xStar : Fin n → ℝ => concaveBifunctionPairing G xStar u) x
      = iSup (fun xStar : Fin n → ℝ =>
          (((xStar ⬝ᵥ x : ℝ) : EReal)) - concaveBifunctionPairing G xStar u) := by
            simp [convexConjugate, fenchelConjugate_eq_iSup]
    _ = iSup (fun xStar : Fin n → ℝ =>
          iSup (fun uStar : Fin m → ℝ =>
            G xStar uStar - (((uStar ⬝ᵥ u : ℝ) : EReal)) +
              (((xStar ⬝ᵥ x : ℝ) : EReal)))) := by
          refine iSup_congr ?_
          intro xStar
          simp [concaveBifunctionPairing, bifunctionPairingNotation, conjugatePairingNotation,
            sInf_range, sub_eq_add_neg]
          rw [helperForTheorem_6_30_4_neg_iInf_eq_iSup_neg]
          calc
            (((xStar ⬝ᵥ x : ℝ) : EReal)) +
                iSup (fun uStar : Fin m → ℝ =>
                  -((((uStar ⬝ᵥ u : ℝ) : EReal)) + -G xStar uStar))
              = iSup (fun uStar : Fin m → ℝ =>
                  (((xStar ⬝ᵥ x : ℝ) : EReal)) +
                    -((((uStar ⬝ᵥ u : ℝ) : EReal)) + -G xStar uStar)) := by
                      simpa [add_comm] using
                        (helperForTheorem_6_30_15_real_add_iSup (c := (xStar ⬝ᵥ x : ℝ))
                          (f := fun uStar : Fin m → ℝ =>
                            -((((uStar ⬝ᵥ u : ℝ) : EReal)) + -G xStar uStar)))
            _ = iSup (fun uStar : Fin m → ℝ =>
                  G xStar uStar - (((uStar ⬝ᵥ u : ℝ) : EReal)) +
                    (((xStar ⬝ᵥ x : ℝ) : EReal))) := by
                    refine iSup_congr ?_
                    intro uStar
                    have hdot_bot : ((((uStar ⬝ᵥ u : ℝ) : EReal)) : EReal) ≠ ⊥ := by simp
                    have hdot_top : ((((uStar ⬝ᵥ u : ℝ) : EReal)) : EReal) ≠ ⊤ := by simp
                    rw [EReal.neg_add (x := (((uStar ⬝ᵥ u : ℝ) : EReal)))
                      (y := -G xStar uStar) (Or.inl hdot_bot) (Or.inl hdot_top)]
                    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = iSup (fun p : (Fin n → ℝ) × (Fin m → ℝ) =>
          G p.1 p.2 - (((p.2 ⬝ᵥ u : ℝ) : EReal)) +
            (((p.1 ⬝ᵥ x : ℝ) : EReal))) := by
          simp [iSup_prod']
    _ = adjointOfConcaveBifunction ⟨G, hG⟩ u x := by
          simp [adjointOfConcaveBifunction, sSup_range, sub_eq_add_neg,
            add_comm, add_left_comm, add_assoc]

/-- A Jensen-convex extended-real function which takes `⊥` once is identically `⊥`. -/
lemma helperForTheorem33_2_convex_eq_constBot_of_eq_bot
    {k : ℕ} {f : (Fin k → ℝ) → EReal}
    (hConv : IsERealConvexOn (Set.univ : Set (Fin k → ℝ)) f)
    {x0 : Fin k → ℝ} (hx0 : f x0 = ⊥) :
    f = fun _ => ⊥ := by
  funext y
  apply le_antisymm
  · let z : Fin k → ℝ := 2 • y - x0
    have hycomb : (1 / 2 : ℝ) • x0 + (1 / 2 : ℝ) • z = y := by
      ext i
      simp [z]
      ring
    have hJ := hConv (x := x0) (y := z) (a := 1 / 2) (b := 1 / 2)
      (by simp) (by simp) (by norm_num) (by norm_num) (by norm_num) (by simpa [hycomb])
    rw [hycomb, hx0] at hJ
    simpa [EReal.coe_mul_bot_of_pos] using hJ
  · exact bot_le

/-- On Jensen-convex functions the raw Section 33 closure agrees with the Chapter 2
convex-function closure, including the improper constant-`⊥` case. -/
lemma helperForTheorem33_2_functionConvexClosure_eq_convexFunctionClosure_of_convex
    {k : ℕ} {f : (Fin k → ℝ) → EReal}
    (hConv : IsERealConvexOn (Set.univ : Set (Fin k → ℝ)) f) :
    functionConvexClosure f = convexFunctionClosure f := by
  by_cases hNoBot : ∀ x, f x ≠ ⊥
  · exact helperForTheorem33_1_functionConvexClosure_eq_convexFunctionClosure_of_noBot hNoBot
  · push_neg at hNoBot
    rcases hNoBot with ⟨x0, hx0⟩
    have hf : f = fun _ => ⊥ :=
      helperForTheorem33_2_convex_eq_constBot_of_eq_bot hConv hx0
    subst f
    have hRaw : functionConvexClosure (fun _ : Fin k → ℝ => (⊥ : EReal)) =
        (fun _ => ⊥) := by
      funext x
      unfold functionConvexClosure
      apply le_antisymm
      · apply iSup_le
        intro eps
        exact iInf_le_of_le ⟨x, by simpa using eps.property⟩ le_rfl
      · exact bot_le
    rw [hRaw]
    simp [convexFunctionClosure]

/-- The convex pairing kernel of a graph-convex bifunction is a Chapter 2 concave function
in the parameter variable, including improper sections. -/
lemma helperForTheorem33_2_convexPairingSection_concaveFunction
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hGraph : IsGraphConvexBifunction F)
    (xStar : Fin n → ℝ) :
    ConcaveFunction (fun u : Fin m → ℝ => convexBifunctionPairing F u xStar) := by
  unfold ConcaveFunction
  have hProj := helperForLemma33_0_22_tiltedProjection_isConvexFunction
    (F := F) hGraph xStar
  have hEq :=
    helperForLemma33_0_22_swappedNegatedAdjointSection_eq_projectionImage_tiltedGraph
      (F := F) xStar
  rw [hEq] at hProj
  simpa [convexBifunctionAdjoint] using hProj

/-- Graph concavity and the concave extended-real convention turn sign negation into graph
convexity. -/
lemma helperForTheorem33_2_negatedGraphConvex
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hGraph : IsGraphConcaveBifunction F)
    (hNoTop : HasNoTopValuesBifunction F) :
    IsGraphConvexBifunction (fun u x => -F u x) := by
  have hNoTopGraph : ∀ z : Fin (m + n) → ℝ, graphFunctionOfBifunction F z ≠ ⊤ := by
    intro z
    simpa [graphFunctionOfBifunction] using
      hNoTop (fun i : Fin m => z (Fin.castAdd n i))
        (fun j : Fin n => z (Fin.natAdd m j))
  have hNeg := helperForCorollary33_1_2_concaveNegation_isConvex_of_noTop
    (hConc := hGraph) (hNoTop := hNoTopGraph)
  simpa [IsGraphConcaveBifunction, IsGraphConvexBifunction,
    graphFunctionOfBifunction] using hNeg

/-- The concave pairing kernel of a graph-concave bifunction is a Chapter 2 convex function
in the parameter variable. -/
lemma helperForTheorem33_2_concavePairingSection_convexFunction
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hGraph : IsGraphConcaveBifunction F)
    (hNoTop : HasNoTopValuesBifunction F)
    (xStar : Fin n → ℝ) :
    ConvexFunction (fun u : Fin m → ℝ => concaveBifunctionPairing F u xStar) := by
  let G : (Fin m → ℝ) → (Fin n → ℝ) → EReal := fun u x => -F u x
  have hGraphG : IsGraphConvexBifunction G := by
    simpa [G] using helperForTheorem33_2_negatedGraphConvex hGraph hNoTop
  have hConvNegPair :
      ConvexFunction (fun u : Fin m → ℝ => -convexBifunctionPairing G u (-xStar)) :=
    helperForTheorem33_2_convexPairingSection_concaveFunction hGraphG (-xStar)
  have hEq : (fun u : Fin m → ℝ => concaveBifunctionPairing F u xStar) =
      fun u => -convexBifunctionPairing G u (-xStar) := by
    funext u
    have h := helperForCorollary33_1_2_convexPairing_negated_eq_neg_concavePairing
      (F := F) u (-xStar)
    simpa [G] using (congrArg Neg.neg h).symm
  simpa [hEq] using hConvNegPair

/-- The first coordinatewise-closure identity in the convex branch, with the book's
convex-analytic closure convention for improper functions. -/
lemma helperForTheorem33_2_first_convex
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hGraph : IsGraphConvexBifunction F) :
    ∀ xStar u,
      convexBifunctionCanonicalAdjointPairing F xStar u =
        concaveClosure (fun u' => convexBifunctionPairing F u' xStar) u := by
  intro xStar u
  have hConc := helperForTheorem33_2_convexPairingSection_concaveFunction hGraph xStar
  simpa [convexBifunctionCanonicalAdjointPairing, convexBifunctionAdjointPairing,
    convexBifunctionAdjoint] using
    congrArg (fun g => g u)
      (concaveConjugate_biconjugate_eq_concaveClosure
        (g := fun u' => convexBifunctionPairing F u' xStar) hConc)

/-- The first coordinatewise-closure identity in the concave branch. -/
lemma helperForTheorem33_2_first_concave
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hGraph : IsGraphConcaveBifunction F)
    (hNoTop : HasNoTopValuesBifunction F) :
    ∀ xStar u,
      concaveBifunctionCanonicalAdjointPairing F xStar u =
        convexFunctionClosure (fun u' => concaveBifunctionPairing F u' xStar) u := by
  intro xStar u
  have hConv := helperForTheorem33_2_concavePairingSection_convexFunction hGraph hNoTop xStar
  simpa [concaveBifunctionCanonicalAdjointPairing, concaveBifunctionAdjointPairing,
    concaveBifunctionAdjoint,
    helperForTheorem33_1_convexConjugate_eq_fenchelConjugate] using
    congrArg (fun g => g u)
      (section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure
        (f := fun u' => concaveBifunctionPairing F u' xStar) hConv)

/-- The second convex identity when the graph function has a finite witness. -/
lemma helperForTheorem33_2_second_convex_of_finiteWitness
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hGraph : IsGraphConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    {u0 : Fin m → ℝ} {x0 : Fin n → ℝ} (hFinite : F u0 x0 ≠ ⊤) :
    ∀ u xStar,
      convexFunctionClosure
          (fun xStar' => convexBifunctionCanonicalAdjointPairing F xStar' u) xStar =
        convexBifunctionPairing (convexBifunctionClosure F) u xStar := by
  have hF : ConvexBifunction F := by
    unfold ConvexBifunction
    simpa [IsGraphConvexBifunction, bifunctionGraphFunction, graphFunctionOfBifunction] using
      helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction hGraph
  let G : (Fin n → ℝ) → (Fin m → ℝ) → EReal :=
    adjointOfConvexBifunction ⟨F, hF⟩
  have hGConc : ConcaveBifunction G :=
    (adjointOfConvexBifunction_closedConcave ⟨F, hF⟩).1
  have hGNoTop : HasNoTopValuesBifunction G := by
    intro xStar uStar
    unfold G adjointOfConvexBifunction
    rw [sInf_range]
    apply ne_of_lt
    refine lt_of_le_of_lt (iInf_le (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
      F p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) +
        (((p.1 ⬝ᵥ uStar : ℝ) : EReal))) (u0, x0)) ?_
    have hCoe := EReal.coe_toReal (x := F u0 x0) hFinite (hNoBot u0 x0)
    rw [← hCoe, ← EReal.coe_sub, ← EReal.coe_add]
    exact EReal.coe_lt_top _
  have hGraphG : IsGraphConcaveBifunction G := by
    have hNegNoBot : ∀ z : Fin (n + m) → ℝ,
        -bifunctionGraphFunction G z ≠ (⊥ : EReal) := by
      intro z
      simpa [bifunctionGraphFunction, EReal.neg_eq_bot_iff] using
        hGNoTop (fun i : Fin n => z (Fin.castAdd m i))
          (fun j : Fin m => z (Fin.natAdd n j))
    have hNegLocal := helperForLemma33_0_5_convexFunction_to_isERealConvexOn_univ
      (f := fun z : Fin (n + m) → ℝ => -bifunctionGraphFunction G z) hGConc hNegNoBot
    have hConcLocal := helperForLemma33_0_5_convexNegation_isConcave hNegLocal
    simpa [IsGraphConcaveBifunction, graphFunctionOfBifunction,
      bifunctionGraphFunction] using hConcLocal
  intro u xStar
  let q : (Fin n → ℝ) → EReal :=
    fun xStar' => convexBifunctionCanonicalAdjointPairing F xStar' u
  have hQEq : q = fun xStar' => concaveBifunctionPairing G xStar' u := by
    funext xStar'
    unfold q convexBifunctionCanonicalAdjointPairing
    congr 1
    funext uStar
    exact helperForTheorem33_2_convexAdjoint_eq_adjointOfConvex hF xStar' uStar
  have hQConv : ConvexFunction q := by
    rw [hQEq]
    exact helperForTheorem33_2_concavePairingSection_convexFunction hGraphG hGNoTop u
  have hConj : convexConjugate q = convexBifunctionClosure F u := by
    funext x
    rw [hQEq]
    calc
      convexConjugate (fun xStar' => concaveBifunctionPairing G xStar' u) x =
          adjointOfConcaveBifunction ⟨G, hGConc⟩ u x :=
        helperForTheorem33_2_convexConjugate_concavePairing_eq_adjointOfConcave hGConc u x
      _ = biadjointOfConvexBifunction ⟨F, hF⟩ u x := by rfl
      _ = convexBifunctionClosure F u x := by
        exact congrArg (fun H => H u x)
          (helperForTheorem_6_30_11_biadjointOfConvex_graph_eq_convexBifunctionClosure_via_coordinate_shuffle F hF)
  have hBiconj := section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure
    (f := q) hQConv
  calc
    convexFunctionClosure q xStar = convexConjugate (convexConjugate q) xStar := by
      simpa [helperForTheorem33_1_convexConjugate_eq_fenchelConjugate] using
        congrArg (fun f => f xStar) hBiconj.symm
    _ = convexConjugate (convexBifunctionClosure F u) xStar := by rw [hConj]
    _ = convexBifunctionPairing (convexBifunctionClosure F) u xStar := rfl

/-- The all-`⊤` exceptional branch of the second convex identity. -/
lemma helperForTheorem33_2_second_convex_of_allTop
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hAllTop : ∀ u x, F u x = ⊤) :
    ∀ u xStar,
      convexFunctionClosure
          (fun xStar' => convexBifunctionCanonicalAdjointPairing F xStar' u) xStar =
        convexBifunctionPairing (convexBifunctionClosure F) u xStar := by
  have hPair : ∀ u xStar, convexBifunctionPairing F u xStar = ⊥ := by
    intro u xStar
    rw [convexBifunctionPairing, convexConjugate, fenchelConjugate_eq_iSup]
    simp [hAllTop]
  have hAdj : ∀ xStar uStar, convexBifunctionAdjointPairing F xStar uStar = ⊤ := by
    intro xStar uStar
    rw [convexBifunctionAdjointPairing, helperForTheorem_6_30_4_concaveConjugate_eq_iInf]
    simp [hPair]
  have hAdjPair : ∀ xStar u, convexBifunctionCanonicalAdjointPairing F xStar u = ⊥ := by
    intro xStar u
    rw [convexBifunctionCanonicalAdjointPairing,
      helperForTheorem_6_30_4_concaveConjugate_eq_iInf]
    simp [hAdj]
  have hClosure : convexBifunctionClosure F = fun _ _ => ⊤ := by
    have hGraphEq : bifunctionGraphFunction F =
        (fun _ : Fin (m + n) → ℝ => (⊤ : EReal)) := by
      funext z
      simp [bifunctionGraphFunction, hAllTop]
    funext u x
    rw [convexBifunctionClosure, convexClosure, hGraphEq]
    exact congrFun (convexFunctionClosure_const_top (n := m + n)) (Fin.append u x)
  intro u xStar
  rw [hClosure]
  simp [hAdjPair, convexFunctionClosure, convexBifunctionPairing,
    convexConjugate, fenchelConjugate_eq_iSup]

/-- Every fixed-`u` corrected adjoint-pairing section in the convex branch is a convex
function of `xStar`. -/
lemma helperForTheorem33_2_convexAdjointPairingSection_convexFunction
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hGraph : IsGraphConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    (u : Fin m → ℝ) :
    ConvexFunction (fun xStar => convexBifunctionCanonicalAdjointPairing F xStar u) := by
  by_cases hAllTop : ∀ u' x, F u' x = ⊤
  · have hPair : ∀ u' xStar, convexBifunctionPairing F u' xStar = ⊥ := by
      intro u' xStar
      rw [convexBifunctionPairing, convexConjugate, fenchelConjugate_eq_iSup]
      simp [hAllTop]
    have hAdj : ∀ xStar uStar, convexBifunctionAdjointPairing F xStar uStar = ⊤ := by
      intro xStar uStar
      rw [convexBifunctionAdjointPairing, helperForTheorem_6_30_4_concaveConjugate_eq_iInf]
      simp [hPair]
    have hEq : (fun xStar => convexBifunctionCanonicalAdjointPairing F xStar u) =
        fun _ : Fin n → ℝ => (⊥ : EReal) := by
      funext xStar
      rw [convexBifunctionCanonicalAdjointPairing,
        helperForTheorem_6_30_4_concaveConjugate_eq_iInf]
      simp [hAdj]
    rw [hEq]
    apply helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction
    intro x y hx hy a b ha hb hab hxy
    simp
  · push_neg at hAllTop
    rcases hAllTop with ⟨u0, x0, hFinite⟩
    have hF : ConvexBifunction F := by
      unfold ConvexBifunction
      simpa [IsGraphConvexBifunction, bifunctionGraphFunction, graphFunctionOfBifunction] using
        helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction hGraph
    let G : (Fin n → ℝ) → (Fin m → ℝ) → EReal :=
      adjointOfConvexBifunction ⟨F, hF⟩
    have hGConc : ConcaveBifunction G :=
      (adjointOfConvexBifunction_closedConcave ⟨F, hF⟩).1
    have hGNoTop : HasNoTopValuesBifunction G := by
      intro xStar uStar
      unfold G adjointOfConvexBifunction
      rw [sInf_range]
      apply ne_of_lt
      refine lt_of_le_of_lt (iInf_le (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
        F p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) +
          (((p.1 ⬝ᵥ uStar : ℝ) : EReal))) (u0, x0)) ?_
      have hCoe := EReal.coe_toReal (x := F u0 x0) hFinite (hNoBot u0 x0)
      rw [← hCoe, ← EReal.coe_sub, ← EReal.coe_add]
      exact EReal.coe_lt_top _
    have hGraphG : IsGraphConcaveBifunction G := by
      have hNegNoBot : ∀ z : Fin (n + m) → ℝ,
          -bifunctionGraphFunction G z ≠ (⊥ : EReal) := by
        intro z
        simpa [bifunctionGraphFunction, EReal.neg_eq_bot_iff] using
          hGNoTop (fun i : Fin n => z (Fin.castAdd m i))
            (fun j : Fin m => z (Fin.natAdd n j))
      have hNegLocal := helperForLemma33_0_5_convexFunction_to_isERealConvexOn_univ
        (f := fun z : Fin (n + m) → ℝ => -bifunctionGraphFunction G z) hGConc hNegNoBot
      have hConcLocal := helperForLemma33_0_5_convexNegation_isConcave hNegLocal
      simpa [IsGraphConcaveBifunction, graphFunctionOfBifunction,
        bifunctionGraphFunction] using hConcLocal
    have hEq : (fun xStar => convexBifunctionCanonicalAdjointPairing F xStar u) =
        fun xStar => concaveBifunctionPairing G xStar u := by
      funext xStar
      unfold convexBifunctionCanonicalAdjointPairing
      congr 1
      funext uStar
      exact helperForTheorem33_2_convexAdjoint_eq_adjointOfConvex hF xStar uStar
    rw [hEq]
    exact helperForTheorem33_2_concavePairingSection_convexFunction hGraphG hGNoTop u

/-- The second concave identity when the graph function has a finite witness. -/
lemma helperForTheorem33_2_second_concave_of_finiteWitness
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hGraph : IsGraphConcaveBifunction F)
    (hNoTop : HasNoTopValuesBifunction F)
    {u0 : Fin m → ℝ} {x0 : Fin n → ℝ} (hFinite : F u0 x0 ≠ ⊥) :
    ∀ u xStar,
      concaveClosure
          (fun xStar' => concaveBifunctionCanonicalAdjointPairing F xStar' u) xStar =
        concaveBifunctionPairing (concaveBifunctionClosure F) u xStar := by
  have hF : ConcaveBifunction F := by
    unfold ConcaveBifunction
    have hNoTopGraph : ∀ z : Fin (m + n) → ℝ,
        graphFunctionOfBifunction F z ≠ ⊤ := by
      intro z
      simpa [graphFunctionOfBifunction] using
        hNoTop (fun i : Fin m => z (Fin.castAdd n i))
          (fun j : Fin n => z (Fin.natAdd m j))
    have hNeg := helperForCorollary33_1_2_concaveNegation_isConvex_of_noTop
      (hConc := hGraph) (hNoTop := hNoTopGraph)
    simpa [IsGraphConcaveBifunction, bifunctionGraphFunction,
      graphFunctionOfBifunction] using
      helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction hNeg
  let G : (Fin n → ℝ) → (Fin m → ℝ) → EReal :=
    adjointOfConcaveBifunction ⟨F, hF⟩
  have hGConv : ConvexBifunction G :=
    (adjointOfConcaveBifunction_closedConvex ⟨F, hF⟩).1
  have hGNoBot : HasNoBotValuesBifunction G := by
    intro xStar uStar
    unfold G adjointOfConcaveBifunction
    rw [sSup_range]
    apply ne_of_gt
    refine lt_of_lt_of_le ?_ (le_iSup (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
      F p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) +
        (((p.1 ⬝ᵥ uStar : ℝ) : EReal))) (u0, x0))
    have hCoe := EReal.coe_toReal (x := F u0 x0) (hNoTop u0 x0) hFinite
    rw [← hCoe, ← EReal.coe_sub, ← EReal.coe_add]
    exact EReal.bot_lt_coe _
  have hGraphG : IsGraphConvexBifunction G := by
    have hLocal := helperForLemma33_0_5_convexFunction_to_isERealConvexOn_univ
      (f := bifunctionGraphFunction G) hGConv (by
        intro z
        simpa [bifunctionGraphFunction] using
          hGNoBot (fun i : Fin n => z (Fin.castAdd m i))
            (fun j : Fin m => z (Fin.natAdd n j)))
    simpa [IsGraphConvexBifunction, graphFunctionOfBifunction,
      bifunctionGraphFunction] using hLocal
  intro u xStar
  let q : (Fin n → ℝ) → EReal :=
    fun xStar' => concaveBifunctionCanonicalAdjointPairing F xStar' u
  have hQEq : q = fun xStar' => convexBifunctionPairing G xStar' u := by
    funext xStar'
    unfold q concaveBifunctionCanonicalAdjointPairing
    congr 1
    funext uStar
    exact helperForTheorem33_2_convexConjugate_concavePairing_eq_adjointOfConcave
      hF xStar' uStar
  have hQConc : ConcaveFunction q := by
    rw [hQEq]
    exact helperForTheorem33_2_convexPairingSection_concaveFunction hGraphG u
  have hConj : concaveConjugate q = concaveBifunctionClosure F u := by
    funext x
    rw [hQEq]
    calc
      concaveConjugate (fun xStar' => convexBifunctionPairing G xStar' u) x =
          adjointOfConvexBifunction ⟨G, hGConv⟩ u x :=
        helperForTheorem33_2_convexAdjoint_eq_adjointOfConvex hGConv u x
      _ = biadjointOfConcaveBifunction ⟨F, hF⟩ u x := by rfl
      _ = concaveBifunctionClosure F u x := by
        exact congrArg (fun H => H u x)
          (helperForTheorem_6_30_11_biadjointOfConcave_graph_eq_concaveBifunctionClosure_via_coordinate_shuffle F hF)
  have hBiconj := concaveConjugate_biconjugate_eq_concaveClosure
    (g := q) hQConc
  calc
    concaveClosure q xStar = concaveConjugate (concaveConjugate q) xStar := by
      exact congrArg (fun f => f xStar) hBiconj.symm
    _ = concaveConjugate (concaveBifunctionClosure F u) xStar := by rw [hConj]
    _ = concaveBifunctionPairing (concaveBifunctionClosure F) u xStar := rfl

/-- The all-`⊥` exceptional branch of the second concave identity. -/
lemma helperForTheorem33_2_second_concave_of_allBot
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hAllBot : ∀ u x, F u x = ⊥) :
    ∀ u xStar,
      concaveClosure
          (fun xStar' => concaveBifunctionCanonicalAdjointPairing F xStar' u) xStar =
        concaveBifunctionPairing (concaveBifunctionClosure F) u xStar := by
  have hPair : ∀ u xStar, concaveBifunctionPairing F u xStar = ⊤ := by
    intro u xStar
    simp [concaveBifunctionPairing, bifunctionPairingNotation,
      conjugatePairingNotation, hAllBot]
  have hAdj : ∀ xStar uStar, concaveBifunctionAdjointPairing F xStar uStar = ⊥ := by
    intro xStar uStar
    rw [concaveBifunctionAdjointPairing, convexConjugate, fenchelConjugate_eq_iSup]
    simp [hPair]
  have hAdjPair : ∀ xStar u, concaveBifunctionCanonicalAdjointPairing F xStar u = ⊤ := by
    intro xStar u
    rw [concaveBifunctionCanonicalAdjointPairing, convexConjugate, fenchelConjugate_eq_iSup]
    simp [hAdj]
  have hClosure : concaveBifunctionClosure F = fun _ _ => ⊥ := by
    have hGraphEq : bifunctionGraphFunction F =
        (fun _ : Fin (m + n) → ℝ => (⊥ : EReal)) := by
      funext z
      simp [bifunctionGraphFunction, hAllBot]
    funext u x
    rw [concaveBifunctionClosure, concaveClosure, hGraphEq]
    simp [convexFunctionClosure_const_top]
  intro u xStar
  rw [hClosure]
  simp [hAdjPair, concaveClosure, convexFunctionClosure,
    concaveBifunctionPairing, bifunctionPairingNotation, conjugatePairingNotation]

-- Proof sketch: interpret `⟨u, F^* x^*⟩` via the genuine adjoint section
-- `xStar ↦ convexBifunctionAdjointPairing F xStar` or `xStar ↦ concaveBifunctionAdjointPairing F xStar`,
-- then take the appropriate conjugate in the `u`-variable. The resulting adjoint-pairing
-- kernels are identified with the coordinatewise closures coming from the graph-function
-- closure of `F`. The closure `(cl F)` is the global closure of the graph function on
-- `ℝ^(m + n)`, not merely a sectionwise closure in the second variable.
/-- Theorem33.2: For any convex bifunction `F` satisfying Rockafellar's `ℝ ∪ {+∞}`
convention (modeled here by `HasNoBotValuesBifunction F`), and for any concave bifunction
`F` satisfying the dual `ℝ ∪ {-∞}` convention (modeled by `HasNoTopValuesBifunction F`),
one has
`⟨u, F^* x^*⟩ = cl_u ⟨F u, x^*⟩` and
`cl_{x^*} ⟨u, F^* x^*⟩ = ⟨(cl F) u, x^*⟩`.
Here `⟨u, F^* x^*⟩` is represented by `convexBifunctionCanonicalAdjointPairing` or
`concaveBifunctionCanonicalAdjointPairing`, formed by taking the conjugate in the `u`-variable of the
genuine adjoint section `xStar ↦ F^* xStar`; `cl_u` and `cl_{x^*}` are the coordinatewise
concave/convex closure operators as appropriate to the convex or concave branch, and `(cl F)`
is modeled by the closure of the graph function on `ℝ^(m + n)`. -/
theorem adjoint_pairing_eq_coordinatewise_closures
    {m n : ℕ} :
    (∀ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      (IsGraphConvexBifunction F ∧ HasNoBotValuesBifunction F) →
        (∀ xStar u,
          convexBifunctionCanonicalAdjointPairing F xStar u =
            concaveClosure (fun u' => convexBifunctionPairing F u' xStar) u) ∧
        (∀ u xStar,
          convexFunctionClosure (fun xStar' => convexBifunctionCanonicalAdjointPairing F xStar' u) xStar =
            convexBifunctionPairing (convexBifunctionClosure F) u xStar)) ∧
      (∀ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
        (IsGraphConcaveBifunction F ∧ HasNoTopValuesBifunction F) →
        (∀ xStar u,
          concaveBifunctionCanonicalAdjointPairing F xStar u =
            convexFunctionClosure (fun u' => concaveBifunctionPairing F u' xStar) u) ∧
        (∀ u xStar,
          concaveClosure (fun xStar' => concaveBifunctionCanonicalAdjointPairing F xStar' u) xStar =
            concaveBifunctionPairing (concaveBifunctionClosure F) u xStar)) := by
  constructor
  · intro F hF
    rcases hF with ⟨hGraph, hNoBot⟩
    refine ⟨helperForTheorem33_2_first_convex hGraph, ?_⟩
    by_cases hAllTop : ∀ u x, F u x = ⊤
    · exact helperForTheorem33_2_second_convex_of_allTop hAllTop
    · push_neg at hAllTop
      rcases hAllTop with ⟨u0, x0, hFinite⟩
      exact helperForTheorem33_2_second_convex_of_finiteWitness
        hGraph hNoBot hFinite
  · intro F hF
    rcases hF with ⟨hGraph, hNoTop⟩
    refine ⟨helperForTheorem33_2_first_concave hGraph hNoTop, ?_⟩
    by_cases hAllBot : ∀ u x, F u x = ⊥
    · exact helperForTheorem33_2_second_concave_of_allBot hAllBot
    · push_neg at hAllBot
      rcases hAllBot with ⟨u0, x0, hFinite⟩
      exact helperForTheorem33_2_second_concave_of_finiteWitness
        hGraph hNoTop hFinite

/-- Helper for Corollary33.2.1: sign-flipping turns the Section 33 concave closure into the
Section 33 convex closure of the negated function.

This is the pointwise one-variable identity needed when the convex-side relative-interior route
is eventually repaired via the Chapter 2 convex-closure theorem for `u ↦ -⟪F u, x^*⟫`. -/
lemma helperForCorollary33_2_1_functionConcaveClosure_eq_neg_functionConvexClosure_neg
    {m : ℕ}
    {g : (Fin m → ℝ) → EReal} :
    functionConcaveClosure g = fun u => -functionConvexClosure (fun u' => -g u') u := by
  funext u
  -- Step 1: first prove the equality after negating the left-hand side.
  have hNeg :
      -functionConcaveClosure g u = functionConvexClosure (fun u' => -g u') u := by
    unfold functionConcaveClosure functionConvexClosure
    -- Step 2: transport the outer infimum and inner supremum across the `EReal` negation
    -- order isomorphism.
    change EReal.negOrderIso
        (⨅ (ε : {ε : ℝ // 0 < ε}),
          ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), g w.1) =
        ⨆ (ε : {ε : ℝ // 0 < ε}),
          ⨅ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), -g w.1
    rw [EReal.negOrderIso.map_iInf]
    congr
    funext ε
    rw [EReal.negOrderIso.map_iSup]
    rfl
  -- Step 3: negate the displayed equality to return to the original closure formula.
  simpa using congrArg Neg.neg hNeg

/-- On concave functions the raw Section 33 upper closure agrees with the canonical
concave-function closure, including the improper constant-`⊤` case. -/
lemma helperForTheorem33_2_functionConcaveClosure_eq_concaveClosure_of_concave
    {k : ℕ} {g : (Fin k → ℝ) → EReal}
    (hConc : ConcaveFunction g)
    (hNoTop : ∀ x, g x ≠ ⊤) :
    functionConcaveClosure g = concaveClosure g := by
  have hNegNoBot : ∀ x, -g x ≠ (⊥ : EReal) := by
    intro x
    simpa [EReal.neg_eq_bot_iff] using hNoTop x
  rw [helperForCorollary33_2_1_functionConcaveClosure_eq_neg_functionConvexClosure_neg]
  unfold concaveClosure
  rw [helperForTheorem33_1_functionConvexClosure_eq_convexFunctionClosure_of_noBot hNegNoBot]

/-- Helper for Corollary33.2.1: graph-function closedness upgrades a graph-convex
bifunction to a closed convex bifunction. -/
lemma helperForCorollary33_2_1_closedConvexBifunction_of_graphFunctionClosed
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hGraph : IsGraphConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    (hGraphClosed : IsFunctionConvexClosed (graphFunctionOfBifunction F)) :
    ClosedConvexBifunction F := by
  -- Step 1: freeze the parameter and recover exact sectionwise convex-closedness from the
  -- graph-function fixed-point hypothesis.
  have hSectionClosed :
      ∀ u : Fin m → ℝ, IsFunctionConvexClosed (F u) :=
    helperForLemma33_0_22_section_isFunctionConvexClosed hGraphClosed
  have hSectionClosureExact :
      ∀ u x, convexFunctionClosure (F u) x = F u x := by
    intro u x
    calc
      convexFunctionClosure (F u) x = functionConvexClosure (F u) x := by
        rw [← helperForTheorem33_1_functionConvexClosure_eq_convexFunctionClosure_of_noBot
          (hNoBot := hNoBot u)]
      _ = F u x := helperForLemma33_0_18_functionConvexClosure_eq_self (hSectionClosed u) x
  -- Step 2: retain the graph-convexity hypothesis in the Chapter 6 representation.
  have hGraphConvex :
      IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) (graphFunctionOfBifunction F) :=
    by simpa [IsGraphConvexBifunction] using hGraph
  -- Step 3: the graph function is lower semicontinuous because it is already fixed by the raw
  -- convex closure.
  have hGraphLsc : LowerSemicontinuous (graphFunctionOfBifunction F) := by
    have hClosureLsc :
        LowerSemicontinuous (functionConvexClosure (graphFunctionOfBifunction F)) :=
      helperForLemma33_0_5_functionConvexClosure_lowerSemicontinuous
        (f := graphFunctionOfBifunction F)
    exact hGraphClosed ▸ hClosureLsc
  have hGraphConvexFunctionOn :
      ConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ)) (graphFunctionOfBifunction F) := by
    intro p hp q hq a b ha hb hab
    rcases hp with ⟨-, hpLe⟩
    rcases hq with ⟨-, hqLe⟩
    constructor
    · simpa using
        (show a • p.1 + b • q.1 ∈ (Set.univ : Set (Fin (m + n) → ℝ)) from by trivial)
    · -- Apply Jensen for the graph and then lift the endpoint heights from the epigraph data.
      have hJensen :
          graphFunctionOfBifunction F (a • p.1 + b • q.1) ≤
            (a : EReal) * graphFunctionOfBifunction F p.1 +
              (b : EReal) * graphFunctionOfBifunction F q.1 :=
        hGraphConvex (x := p.1) (y := q.1) (by simp) (by simp) ha hb hab (by simp)
      have hWeightedHeights :
          (a : EReal) * graphFunctionOfBifunction F p.1 +
              (b : EReal) * graphFunctionOfBifunction F q.1 ≤
            (a : EReal) * (p.2 : EReal) + (b : EReal) * (q.2 : EReal) := by
        gcongr
      calc
        graphFunctionOfBifunction F (a • p.1 + b • q.1) ≤
            (a : EReal) * graphFunctionOfBifunction F p.1 +
              (b : EReal) * graphFunctionOfBifunction F q.1 := hJensen
        _ ≤ (a : EReal) * (p.2 : EReal) + (b : EReal) * (q.2 : EReal) := hWeightedHeights
        _ = ((a * p.2 + b * q.2 : ℝ) : EReal) := by
            have hMulA : (a : EReal) * (p.2 : EReal) = ((a * p.2 : ℝ) : EReal) := by
              simpa using (EReal.coe_mul a p.2).symm
            have hMulB : (b : EReal) * (q.2 : EReal) = ((b * q.2 : ℝ) : EReal) := by
              simpa using (EReal.coe_mul b q.2).symm
            rw [hMulA, hMulB, ← EReal.coe_add]
  have hBifConvex : ConvexBifunction F := by
    -- Repackage graph convexity in the Chapter 6 bifunction language.
    unfold ConvexBifunction ConvexFunction
    simpa [bifunctionGraphFunction, graphFunctionOfBifunction] using hGraphConvexFunctionOn
  have hClosedGraph : ClosedConvexFunction (bifunctionGraphFunction F) := by
    -- The graph function is closed because it is convex and lower semicontinuous.
    refine ⟨?_, ?_⟩
    · unfold ConvexFunction
      simpa [bifunctionGraphFunction, graphFunctionOfBifunction] using hGraphConvexFunctionOn
    · simpa [bifunctionGraphFunction, graphFunctionOfBifunction] using hGraphLsc
  exact ⟨hBifConvex, hClosedGraph⟩

/-- Helper for Corollary33.2.1: graph-function convex-closedness also forces closedness of every
slice obtained by freezing the second variable.

This is the exact symmetric counterpart to `helperForLemma33_0_22_section_isFunctionConvexClosed`:
once the graph function is lower semicontinuous on `ℝ^(m+n)`, composing it with
`u ↦ Fin.append u v` preserves lower semicontinuity and therefore fixes the resulting slice by
the one-variable raw convex closure operator. -/
lemma helperForCorollary33_2_1_frozenSecondVariable_isFunctionConvexClosed
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_closed : IsFunctionConvexClosed (graphFunctionOfBifunction F)) :
    ∀ v : Fin n → ℝ, IsFunctionConvexClosed (fun u : Fin m → ℝ => F u v) := by
  intro v
  let freezeSecond : (Fin m → ℝ) → (Fin (m + n) → ℝ) := fun u => Fin.append u v
  have hGraphLsc : LowerSemicontinuous (graphFunctionOfBifunction F) := by
    have hClosureLsc :
        LowerSemicontinuous (functionConvexClosure (graphFunctionOfBifunction F)) :=
      helperForLemma33_0_5_functionConvexClosure_lowerSemicontinuous
        (f := graphFunctionOfBifunction F)
    exact hF_closed ▸ hClosureLsc
  have hFreezeSecondCont : Continuous freezeSecond := by
    simpa [freezeSecond] using
      (Fin.continuous_append m n).comp (continuous_id.prodMk continuous_const)
  have hSliceLsc : LowerSemicontinuous (fun u : Fin m → ℝ => F u v) := by
    have hComposed :
        LowerSemicontinuous
          (fun u : Fin m → ℝ => graphFunctionOfBifunction F (freezeSecond u)) :=
      hGraphLsc.comp_continuous hFreezeSecondCont
    simpa [freezeSecond, graphFunctionOfBifunction] using hComposed
  exact
    helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous
      hSliceLsc

/-- Helper for Corollary33.2.1: once graph-function closedness identifies `F` with its Chapter 6
graph closure, the convex pairing of the closure is the original convex pairing. -/
lemma helperForCorollary33_2_1_convexClosure_pairing_eq_self_of_closed
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hGraph : IsGraphConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    (hGraphClosed : IsFunctionConvexClosed (graphFunctionOfBifunction F))
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) :
    convexBifunctionPairing (convexBifunctionClosure F) u xStar =
      convexBifunctionPairing F u xStar := by
  -- Step 1: package the Section 33 hypotheses into the closed convex bifunction object needed
  -- by Theorem 6.30.11.
  have hClosed :
      ClosedConvexBifunction F :=
    helperForCorollary33_2_1_closedConvexBifunction_of_graphFunctionClosed
      (F := F) hGraph hNoBot hGraphClosed
  have hGraphNeBot :
      ∀ z : Fin (m + n) → ℝ, bifunctionGraphFunction F z ≠ (⊥ : EReal) := by
    intro z
    simpa [bifunctionGraphFunction] using
      hNoBot (fun i : Fin m => z (Fin.castAdd n i)) (fun j : Fin n => z (Fin.natAdd m j))
  -- Step 2: collapse the Chapter 6 graph closure back to `F`, then transport that equality
  -- through the pairing operator.
  have hClosureFixed : convexBifunctionClosure F = F :=
    helperForTheorem_6_30_11_convexBifunctionClosure_eq_self_of_closed
      (F := F) hClosed hGraphNeBot
  simpa using congrArg (fun G => convexBifunctionPairing G u xStar) hClosureFixed

/-- Helper for Corollary33.2.1: the effective domain of the fixed-`u` adjoint-pairing section is
exactly the textbook adjoint domain `{x^* | ∃ u', (F^* x^*)(u') ≠ ⊥}`. -/
lemma helperForCorollary33_2_1_adjointPairingSection_effectiveDomain_eq
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) :
    effectiveDomain (Set.univ : Set (Fin n → ℝ))
      (fun xStar' => convexBifunctionCanonicalAdjointPairing F xStar' u) =
        {xStar' | ∃ u' : Fin m → ℝ, convexBifunctionAdjointPairing F xStar' u' ≠ ⊥} := by
  ext xStar
  rw [effectiveDomain_eq]
  constructor
  · intro hx
    have hx' : convexBifunctionCanonicalAdjointPairing F xStar u < ⊤ := by
      simpa [Set.mem_setOf_eq] using hx.2
    -- If the entire adjoint section were `⊥`, its concave conjugate would be identically `⊤`.
    by_contra hNoWitness
    have hAllBot : ∀ u' : Fin m → ℝ, convexBifunctionAdjointPairing F xStar u' = (⊥ : EReal) := by
      intro u'
      by_contra hu'
      exact hNoWitness ⟨u', hu'⟩
    have hTop : convexBifunctionCanonicalAdjointPairing F xStar u = (⊤ : EReal) := by
      rw [convexBifunctionCanonicalAdjointPairing, helperForTheorem_6_30_4_concaveConjugate_eq_iInf]
      simp [convexBifunctionAdjointPairing, hAllBot]
    exact (lt_top_iff_ne_top.1 hx') hTop
  · intro hx
    rcases hx with ⟨u', hu'⟩
    refine ⟨by simp, ?_⟩
    -- A single adjoint-section value away from `⊥` gives a witness keeping the conjugate away
    -- from `⊤`.
    have hNoBotConj :
        convexConjugate (fun v : Fin m → ℝ => -convexBifunctionAdjointPairing F xStar v) (-u) ≠
          (⊥ : EReal) := by
      simpa using
        helperForTheorem33_1_convexConjugate_ne_bot_of_point
          (f := fun v : Fin m → ℝ => -convexBifunctionAdjointPairing F xStar v)
          (x₀ := u') (by simpa using hu') (-u)
    have hEq :
        convexBifunctionCanonicalAdjointPairing F xStar u =
          -convexConjugate (fun v : Fin m → ℝ => -convexBifunctionAdjointPairing F xStar v) (-u) := by
      simpa [convexBifunctionCanonicalAdjointPairing, convexConjugate] using
        helperForTheorem_6_30_3_concaveConjugate_eq_neg_fenchelConjugate_neg_unrestricted
          (g := convexBifunctionAdjointPairing F xStar) u
    refine lt_top_iff_ne_top.2 ?_
    intro hTop
    have hNegTop :
        -convexConjugate (fun v : Fin m → ℝ => -convexBifunctionAdjointPairing F xStar v) (-u) =
          (⊤ : EReal) :=
      hEq.symm.trans hTop
    have :
        convexConjugate (fun v : Fin m → ℝ => -convexBifunctionAdjointPairing F xStar v) (-u) =
          (⊥ : EReal) := by
      have := congrArg Neg.neg hNegTop
      simpa using this
    exact hNoBotConj this

/-- The concave effective domain of the corrected adjoint-pairing section is the set of
adjoint parameters for which the genuine convex adjoint section is not identically `⊤`. -/
lemma helperForCorollary33_2_1_concaveAdjointPairingSection_concaveEffectiveDomain_eq
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) :
    effectiveDomain (Set.univ : Set (Fin n → ℝ))
        (fun xStar' => -concaveBifunctionCanonicalAdjointPairing F xStar' u) =
      {xStar' | ∃ u' : Fin m → ℝ, concaveBifunctionAdjointPairing F xStar' u' ≠ ⊤} := by
  ext xStar
  rw [effectiveDomain_eq]
  constructor
  · intro hx
    have hPairNeBot :
        concaveBifunctionCanonicalAdjointPairing F xStar u ≠ (⊥ : EReal) := by
      intro hBot
      have hNegTop :
          -concaveBifunctionCanonicalAdjointPairing F xStar u = (⊤ : EReal) := by
        simp [hBot]
      exact (lt_top_iff_ne_top.1 hx.2) hNegTop
    by_contra hNoWitness
    have hAllTop :
        ∀ u' : Fin m → ℝ, concaveBifunctionAdjointPairing F xStar u' = (⊤ : EReal) := by
      intro u'
      by_contra hu'
      exact hNoWitness ⟨u', hu'⟩
    have hBot :
        concaveBifunctionCanonicalAdjointPairing F xStar u = (⊥ : EReal) := by
      rw [concaveBifunctionCanonicalAdjointPairing, convexConjugate, fenchelConjugate_eq_iSup]
      simp [hAllTop]
    exact hPairNeBot hBot
  · rintro ⟨u', hu'⟩
    refine ⟨by simp, ?_⟩
    have hPairNeBot :
        concaveBifunctionCanonicalAdjointPairing F xStar u ≠ (⊥ : EReal) := by
      simpa [concaveBifunctionCanonicalAdjointPairing] using
        helperForTheorem33_1_convexConjugate_ne_bot_of_point
          (f := concaveBifunctionAdjointPairing F xStar) (x₀ := u') hu' u
    refine lt_top_iff_ne_top.2 ?_
    intro hNegTop
    have hBot : concaveBifunctionCanonicalAdjointPairing F xStar u = (⊥ : EReal) := by
      have := congrArg Neg.neg hNegTop
      simpa using this
    exact hPairNeBot hBot

/-- Helper for Corollary33.2.1: a convex function agrees with the Section 33 raw convex closure
on the relative interior of its effective domain. -/
lemma helperForCorollary33_2_1_convexFunctionClosure_eq_self_on_ri_effectiveDomain_fin
    {m : ℕ}
    {f : (Fin m → ℝ) → EReal}
    (hConv : IsERealConvexOn (Set.univ : Set (Fin m → ℝ)) f)
    {u : Fin m → ℝ}
    (hu : u ∈ euclideanRelativeInterior_fin m
      (effectiveDomain (Set.univ : Set (Fin m → ℝ)) f)) :
    convexFunctionClosure f u = f u := by
  let e : EuclideanSpace Real (Fin m) ≃L[Real] (Fin m → ℝ) :=
    EuclideanSpace.equiv (ι := Fin m) (𝕜 := Real)
  have huE : e.symm u ∈ euclideanRelativeInterior m
      (((fun x : EuclideanSpace Real (Fin m) => (x : Fin m → ℝ)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin m → ℝ)) f) : Set (EuclideanSpace Real (Fin m))) := by
    have huImage : u ∈ e '' euclideanRelativeInterior m
        (e.symm '' effectiveDomain (Set.univ : Set (Fin m → ℝ)) f) := by
      simpa [euclideanRelativeInterior_fin, e] using hu
    rcases huImage with ⟨x, hx, hxu⟩
    have hxEq : x = e.symm u := by
      simpa [e] using congrArg e.symm hxu
    simpa [helperForTheorem_23_4_preimage_eq_symmImage, e, hxEq] using hx
  -- Pass to Euclidean coordinates, apply the Chapter 2 theorem there, then transport back.
  simpa [e] using
    helperForLemma33_0_14_convexFunctionClosure_eq_on_ri_effectiveDomain
      (f := f) hConv (e.symm u) huE

/-- Helper for Corollary33.2.1: the same relative-interior closure identity, packaged directly
for a global convex function on `Fin m → ℝ`. -/
lemma helperForCorollary33_2_1_convexFunctionClosure_eq_self_on_ri_effectiveDomain_fin_of_ConvexFunction
    {m : ℕ}
    {f : (Fin m → ℝ) → EReal}
    (hConvFun : ConvexFunction f)
    {u : Fin m → ℝ}
    (hu : u ∈ euclideanRelativeInterior_fin m
      (effectiveDomain (Set.univ : Set (Fin m → ℝ)) f)) :
    convexFunctionClosure f u = f u := by
  let e : EuclideanSpace Real (Fin m) ≃L[Real] (Fin m → ℝ) :=
    EuclideanSpace.equiv (ι := Fin m) (𝕜 := Real)
  have huE : e.symm u ∈ euclideanRelativeInterior m
      (((fun x : EuclideanSpace Real (Fin m) => (x : Fin m → ℝ)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin m → ℝ)) f) : Set (EuclideanSpace Real (Fin m))) := by
    have huImage : u ∈ e '' euclideanRelativeInterior m
        (e.symm '' effectiveDomain (Set.univ : Set (Fin m → ℝ)) f) := by
      simpa [euclideanRelativeInterior_fin, e] using hu
    rcases huImage with ⟨x, hx, hxu⟩
    have hxEq : x = e.symm u := by
      simpa [e] using congrArg e.symm hxu
    simpa [helperForTheorem_23_4_preimage_eq_symmImage, e, hxEq] using hx
  by_cases hproper : ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) f
  · simpa [e] using
      (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
        (f := f) hproper).2 (e.symm u) huE
  · have hConvOn : ConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) f := by
      simpa [ConvexFunction] using hConvFun
    have himproper : ImproperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) f := by
      exact ⟨hConvOn, hproper⟩
    simpa [e] using
      convexFunctionClosure_agrees_on_ri_of_improper
        (f := f) himproper (e.symm u) huE

/-- A concave function agrees with its canonical concave closure on the relative interior
of its concave effective domain. -/
lemma helperForCorollary33_2_1_concaveClosure_eq_self_on_ri_concaveEffectiveDomain_fin
    {m : ℕ}
    {g : (Fin m → ℝ) → EReal}
    (hConc : ConcaveFunction g)
    {u : Fin m → ℝ}
    (hu : u ∈ euclideanRelativeInterior_fin m
      (effectiveDomain (Set.univ : Set (Fin m → ℝ)) (fun v => -g v))) :
    concaveClosure g u = g u := by
  have hNeg :
      convexFunctionClosure (fun v => -g v) u = -g u :=
    helperForCorollary33_2_1_convexFunctionClosure_eq_self_on_ri_effectiveDomain_fin_of_ConvexFunction
      (f := fun v => -g v) hConc hu
  unfold concaveClosure
  rw [hNeg]
  simp

/-- Helper for Corollary33.2.1: an improper convex function is identically `⊥` on the relative
interior of its effective domain, expressed in `Fin m → ℝ` coordinates. -/
lemma helperForCorollary33_2_1_improperConvexFunctionOn_eq_bot_on_ri_effectiveDomain_fin
    {m : ℕ}
    {f : (Fin m → ℝ) → EReal}
    (himproper : ImproperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) f)
    {u : Fin m → ℝ}
    (hu : u ∈ euclideanRelativeInterior_fin m
      (effectiveDomain (Set.univ : Set (Fin m → ℝ)) f)) :
    f u = (⊥ : EReal) := by
  let e : EuclideanSpace Real (Fin m) ≃L[Real] (Fin m → ℝ) :=
    EuclideanSpace.equiv (ι := Fin m) (𝕜 := Real)
  have huE : e.symm u ∈ euclideanRelativeInterior m
      (((fun x : EuclideanSpace Real (Fin m) => (x : Fin m → ℝ)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin m → ℝ)) f) : Set (EuclideanSpace Real (Fin m))) := by
    have huImage : u ∈ e '' euclideanRelativeInterior m
        (e.symm '' effectiveDomain (Set.univ : Set (Fin m → ℝ)) f) := by
      simpa [euclideanRelativeInterior_fin, e] using hu
    rcases huImage with ⟨x, hx, hxu⟩
    have hxEq : x = e.symm u := by
      simpa [e] using congrArg e.symm hxu
    simpa [helperForTheorem_23_4_preimage_eq_symmImage, e, hxEq] using hx
  -- The Chapter 2 improper branch becomes the claimed `⊥` identity after transporting
  -- coordinates back to `Fin m → ℝ`.
  simpa [e] using
    improperConvexFunctionOn_eq_bot_on_ri_effectiveDomain
      (f := f) himproper (e.symm u) huE

/-- Helper for Corollary33.2.1: a convex function agrees with the Section 33 raw convex closure
on the relative interior of its effective domain. -/
lemma helperForCorollary33_2_1_functionConvexClosure_eq_self_of_convex_on_ri_effectiveDomain
    {m : ℕ}
    {f : (Fin m → ℝ) → EReal}
    (hConv : IsERealConvexOn (Set.univ : Set (Fin m → ℝ)) f)
    {u : Fin m → ℝ}
    (hu : u ∈ euclideanRelativeInterior_fin m
      (effectiveDomain (Set.univ : Set (Fin m → ℝ)) f)) :
    functionConvexClosure f u = f u := by
  by_cases hproper : ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) f
  · -- In the proper branch, Theorem33.1 already identifies the raw closure with Chapter 2's
    -- convex closure.
    have hNoBot : ∀ v, f v ≠ (⊥ : EReal) := by
      intro v
      exact hproper.2.2 v (by simp)
    rw [helperForTheorem33_1_functionConvexClosure_eq_convexFunctionClosure_of_noBot
      (f := f) hNoBot]
    exact
      helperForCorollary33_2_1_convexFunctionClosure_eq_self_on_ri_effectiveDomain_fin
        (f := f) hConv hu
  · -- In the improper branch, Chapter 2 forces `f` to be identically `⊥` on `ri (dom f)`.
    have hConvFun : ConvexFunction f :=
      helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction hConv
    have hConvOn : ConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) f := by
      simpa [ConvexFunction] using hConvFun
    have himproper : ImproperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) f :=
      ⟨hConvOn, hproper⟩
    have hBot : f u = (⊥ : EReal) := by
      exact
        helperForCorollary33_2_1_improperConvexFunctionOn_eq_bot_on_ri_effectiveDomain_fin
          (f := f) himproper hu
    apply le_antisymm
    · have hRawLe : functionConvexClosure f u ≤ f u :=
        helperForLemma33_0_5_functionConvexClosure_raw_le_self (f := f) u
      simpa [hBot] using hRawLe
    · simp [hBot]

/-- Helper for Corollary33.2.1: the raw Section 33 convex closure agrees with any global convex
function on `ri (dom f)`, packaged directly from `ConvexFunction`. -/
lemma helperForCorollary33_2_1_functionConvexClosure_eq_self_of_ConvexFunction_on_ri_effectiveDomain
    {m : ℕ}
    {f : (Fin m → ℝ) → EReal}
    (hConvFun : ConvexFunction f)
    {u : Fin m → ℝ}
    (hu : u ∈ euclideanRelativeInterior_fin m
      (effectiveDomain (Set.univ : Set (Fin m → ℝ)) f)) :
    functionConvexClosure f u = f u := by
  by_cases hproper : ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) f
  · have hNoBot : ∀ v, f v ≠ (⊥ : EReal) := by
      intro v
      exact hproper.2.2 v (by simp)
    rw [helperForTheorem33_1_functionConvexClosure_eq_convexFunctionClosure_of_noBot
      (f := f) hNoBot]
    exact
      helperForCorollary33_2_1_convexFunctionClosure_eq_self_on_ri_effectiveDomain_fin_of_ConvexFunction
        (f := f) hConvFun hu
  · have hConvOn : ConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) f := by
      simpa [ConvexFunction] using hConvFun
    have himproper : ImproperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) f := by
      exact ⟨hConvOn, hproper⟩
    have hBot : f u = (⊥ : EReal) := by
      exact
        helperForCorollary33_2_1_improperConvexFunctionOn_eq_bot_on_ri_effectiveDomain_fin
          (f := f) himproper hu
    apply le_antisymm
    · have hRawLe : functionConvexClosure f u ≤ f u :=
        helperForLemma33_0_5_functionConvexClosure_raw_le_self (f := f) u
      simpa [hBot] using hRawLe
    · simp [hBot]

/-- Helper for Corollary33.2.1: negating the convex pairing section produces a convex
one-variable function. -/
lemma helperForCorollary33_2_1_negConvexPairingSection_isERealConvexOn
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hRock : IsRockafellarConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    (xStar : Fin n → ℝ)
    (hPairNoTop : ∀ u' : Fin m → ℝ, convexBifunctionPairing F u' xStar ≠ (⊤ : EReal)) :
    IsERealConvexOn (Set.univ : Set (Fin m → ℝ))
      (fun u' => -convexBifunctionPairing F u' xStar) := by
  rcases (convexBifunction_pairing_correspondence (m := m) (n := n)).1 F hRock hNoBot with
    ⟨hConcConv, _, _⟩
  have hConc :
      IsERealConcaveOn (Set.univ : Set (Fin m → ℝ))
        (fun u' => convexBifunctionPairing F u' xStar) :=
    hConcConv.1 xStar (by simp)
  exact
    helperForCorollary33_1_2_concaveNegation_isConvex_of_noTop
      hConc hPairNoTop


/-- Helper for Corollary33.2.1: even before proving the raw Jensen statement for the negated
pairing section, the same section is already a global convex function in the Chapter 6 epigraph
sense. This is the exact package needed by the relative-interior closure theorem. -/
lemma helperForCorollary33_2_1_negConvexPairingSection_isConvexFunction
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hRock : IsRockafellarConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    (xStar : Fin n → ℝ) :
    ConvexFunction (fun u' => -convexBifunctionPairing F u' xStar) := by
  rcases (convexBifunction_pairing_correspondence (m := m) (n := n)).1 F hRock hNoBot with
    ⟨hConcConv, _, _⟩
  have hConc :
      IsERealConcaveOn (Set.univ : Set (Fin m → ℝ))
        (fun u' => convexBifunctionPairing F u' xStar) :=
    hConcConv.1 xStar (by simp)
  unfold ConvexFunction ConvexFunctionOn epigraph
  intro p hp q hq a b ha hb hab
  rcases hp with ⟨hpUniv, hpHeight⟩
  rcases hq with ⟨hqUniv, hqHeight⟩
  constructor
  · show a • p.1 + b • q.1 ∈ (Set.univ : Set (Fin m → ℝ))
    simp
  · have hpHyp : ((-p.2 : ℝ) : EReal) ≤ convexBifunctionPairing F p.1 xStar := by
      have : -((p.2 : ℝ) : EReal) ≤ -(-convexBifunctionPairing F p.1 xStar) :=
        (EReal.neg_le_neg_iff).2 hpHeight
      simpa using this
    have hqHyp : ((-q.2 : ℝ) : EReal) ≤ convexBifunctionPairing F q.1 xStar := by
      have : -((q.2 : ℝ) : EReal) ≤ -(-convexBifunctionPairing F q.1 xStar) :=
        (EReal.neg_le_neg_iff).2 hqHeight
      simpa using this
    have hWeightedHyp :
        (((-(a * p.2 + b * q.2) : ℝ) : EReal)) ≤
          (a : EReal) * convexBifunctionPairing F p.1 xStar +
            (b : EReal) * convexBifunctionPairing F q.1 xStar := by
      have hCoeffA : (0 : EReal) ≤ (a : EReal) := by
        exact_mod_cast ha
      have hCoeffB : (0 : EReal) ≤ (b : EReal) := by
        exact_mod_cast hb
      have hDecomp :
          (((-(a * p.2 + b * q.2) : ℝ) : EReal)) =
            (a : EReal) * (((-p.2 : ℝ) : EReal)) +
              (b : EReal) * (((-q.2 : ℝ) : EReal)) := by
        have hReal : -(a * p.2 + b * q.2) = a * (-p.2) + b * (-q.2) := by
          ring
        rw [hReal, EReal.coe_add, EReal.coe_mul, EReal.coe_mul]
      rw [hDecomp]
      exact add_le_add
        (mul_le_mul_of_nonneg_left hpHyp hCoeffA)
        (mul_le_mul_of_nonneg_left hqHyp hCoeffB)
    have hJensen :
        (a : EReal) * convexBifunctionPairing F p.1 xStar +
            (b : EReal) * convexBifunctionPairing F q.1 xStar ≤
          convexBifunctionPairing F (a • p.1 + b • q.1) xStar :=
      hConc (x := p.1) (y := q.1) (by simp) (by simp) ha hb hab (by simp)
    have hCombined :
        (((-(a * p.2 + b * q.2) : ℝ) : EReal)) ≤
          convexBifunctionPairing F (a • p.1 + b • q.1) xStar :=
      le_trans hWeightedHyp hJensen
    have hNeg :
        -convexBifunctionPairing F (a • p.1 + b • q.1) xStar ≤
          (((a * p.2 + b * q.2 : ℝ) : EReal)) := by
      have hTmp :
          (((-(a * p.2 + b * q.2) : ℝ) : EReal)) ≤
            -(-convexBifunctionPairing F (a • p.1 + b • q.1) xStar) := by
        simpa using hCombined
      exact (EReal.neg_le_neg_iff).1 hTmp
    simpa [smul_eq_mul, EReal.coe_add, EReal.coe_mul, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using hNeg

/-- Helper for Corollary33.2.1: the effective domain of the negated convex pairing section is
exactly the textbook domain `{u | ∃ x, F u x < ⊤}`. -/
lemma helperForCorollary33_2_1_negConvexPairingSection_effectiveDomain_eq
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (xStar : Fin n → ℝ) :
    effectiveDomain (Set.univ : Set (Fin m → ℝ))
      (fun u' => -convexBifunctionPairing F u' xStar) =
        {u' | ∃ x : Fin n → ℝ, F u' x < ⊤} := by
  ext u
  rw [effectiveDomain_eq]
  constructor
  · intro hu
    have hu' : u ∈ Set.univ ∧ -convexBifunctionPairing F u xStar < ⊤ := by
      simpa [Set.mem_setOf_eq] using hu
    by_contra hDom
    have hAllTop : ∀ x : Fin n → ℝ, F u x = ⊤ := by
      intro x
      by_contra hx
      exact hDom ⟨x, lt_top_iff_ne_top.2 hx⟩
    have hPairBot : convexBifunctionPairing F u xStar = (⊥ : EReal) := by
      rw [convexBifunctionPairing, convexConjugate, fenchelConjugate_eq_iSup]
      apply le_antisymm
      · refine iSup_le ?_
        intro x
        simp [hAllTop]
      · exact bot_le
    have hNegTop : -convexBifunctionPairing F u xStar = (⊤ : EReal) := by
      simpa using congrArg Neg.neg hPairBot
    exact (lt_top_iff_ne_top.1 hu'.2) hNegTop
  · intro hu
    rcases hu with ⟨x, hx⟩
    have hPairNoBot :
        convexBifunctionPairing F u xStar ≠ (⊥ : EReal) := by
      simpa [convexBifunctionPairing, bifunctionPairingNotation, convexConjugate] using
        helperForTheorem33_1_convexConjugate_ne_bot_of_point
          (f := F u) (x₀ := x) (lt_top_iff_ne_top.1 hx) xStar
    -- Step 1: a finite primal witness keeps the pairing away from `⊥`.
    -- Step 2: after negation this is exactly the `lt_top` condition defining the effective
    -- domain of the convex closure theorem.
    refine ⟨by simp, ?_⟩
    exact lt_top_iff_ne_top.2 (by simpa using hPairNoBot)

/-- Helper for Corollary33.2.1: the effective domain of the concave pairing section is exactly
the textbook domain `{u | ∃ x, F u x ≠ ⊥}`. -/
lemma helperForCorollary33_2_1_concavePairingSection_effectiveDomain_eq
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (xStar : Fin n → ℝ) :
    effectiveDomain (Set.univ : Set (Fin m → ℝ))
      (fun u' => concaveBifunctionPairing F u' xStar) =
        {u' | ∃ x : Fin n → ℝ, F u' x ≠ ⊥} := by
  ext u
  rw [effectiveDomain_eq]
  constructor
  · intro hu
    have hu' : u ∈ Set.univ ∧ concaveBifunctionPairing F u xStar < ⊤ := by
      simpa [Set.mem_setOf_eq] using hu
    by_contra hDom
    have hAllBot : ∀ x : Fin n → ℝ, F u x = ⊥ := by
      intro x
      by_contra hx
      exact hDom ⟨x, hx⟩
    have hPairTop : concaveBifunctionPairing F u xStar = (⊤ : EReal) := by
      -- If the whole image section is `⊥`, every term in the concave conjugate infimum is `⊤`.
      simp [concaveBifunctionPairing, bifunctionPairingNotation, conjugatePairingNotation, hAllBot]
    exact (lt_top_iff_ne_top.1 hu'.2) hPairTop
  · intro hu
    rcases hu with ⟨x, hx⟩
    have hConvNoBot : convexConjugate (fun y => -F u y) (-xStar) ≠ (⊥ : EReal) := by
      -- A primal witness away from `⊥` becomes a witness away from `⊤` after negation.
      simpa using
        helperForTheorem33_1_convexConjugate_ne_bot_of_point
          (f := fun y => -F u y) (x₀ := x) (by simpa using hx) (-xStar)
    have hPairEq :
        concaveBifunctionPairing F u xStar =
          -convexConjugate (fun y => -F u y) (-xStar) := by
      -- Rewrite the concave conjugate through the unrestricted sign-flip identity.
      calc
        concaveBifunctionPairing F u xStar
            = -fenchelConjugate n (fun y => -F u y) (-xStar) := by
                simpa [concaveBifunctionPairing] using
                  helperForTheorem_6_30_3_concaveConjugate_eq_neg_fenchelConjugate_neg_unrestricted
                    (g := F u) xStar
        _ = -convexConjugate (fun y => -F u y) (-xStar) := by
              rfl
    have hPairNeTop : concaveBifunctionPairing F u xStar ≠ (⊤ : EReal) := by
      -- Negating a non-`⊥` convex conjugate cannot produce `⊤`.
      rw [hPairEq]
      simpa using hConvNoBot
    exact ⟨by simp, lt_top_iff_ne_top.2 hPairNeTop⟩

/-- Helper for Corollary33.2.1: the negated convex pairing section already agrees with its raw
Section 33 convex closure at points of `ri (dom F)` in the parameter variable. -/
lemma helperForCorollary33_2_1_negConvexPairingSection_functionConvexClosure_eq_self_on_intrinsicInterior
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hGraph : IsGraphConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    {u : Fin m → ℝ}
    (hu : u ∈ intrinsicInterior ℝ {u' | ∃ x : Fin n → ℝ, F u' x < ⊤})
    (xStar : Fin n → ℝ) :
    convexFunctionClosure (fun u' => -convexBifunctionPairing F u' xStar) u =
      -convexBifunctionPairing F u xStar := by
  let q : (Fin m → ℝ) → EReal := fun u' => -convexBifunctionPairing F u' xStar
  have hConvFun : ConvexFunction q := by
    simpa [q, ConcaveFunction] using
      helperForTheorem33_2_convexPairingSection_concaveFunction hGraph xStar
  have huq :
      u ∈ euclideanRelativeInterior_fin m
        (effectiveDomain (Set.univ : Set (Fin m → ℝ)) q) := by
    have hEqDom :
        effectiveDomain (Set.univ : Set (Fin m → ℝ)) q =
          {u' | ∃ x : Fin n → ℝ, F u' x < ⊤} := by
      simpa [q] using
        helperForCorollary33_2_1_negConvexPairingSection_effectiveDomain_eq
          (F := F) xStar
    have hu' :
        u ∈ intrinsicInterior ℝ
          (effectiveDomain (Set.univ : Set (Fin m → ℝ)) q) := by
      rw [hEqDom]
      exact hu
    -- Transport the textbook `ri (dom F)` hypothesis to the effective domain of `q`.
    rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior]
    exact hu'
  -- Route correction: the correct bridge is a proper/improper convex case split on the
  -- negated pairing section, not a pointwise lower-semicontinuity argument.
  exact
    helperForCorollary33_2_1_convexFunctionClosure_eq_self_on_ri_effectiveDomain_fin_of_ConvexFunction
      (f := q) hConvFun huq

/-- Helper for Corollary33.2.1: the fixed-`u` adjoint-pairing section already agrees with its raw
Section 33 convex closure on `ri (dom F^*)`. -/
lemma helperForCorollary33_2_1_adjointPairingSection_functionConvexClosure_eq_self_on_intrinsicInterior
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hGraph : IsGraphConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    (hGraphClosed : IsFunctionConvexClosed (graphFunctionOfBifunction F))
    (u : Fin m → ℝ)
    {xStar : Fin n → ℝ}
    (hxStar : xStar ∈ intrinsicInterior ℝ
      {xStar' | ∃ u' : Fin m → ℝ, convexBifunctionAdjointPairing F xStar' u' ≠ ⊥}) :
    convexFunctionClosure (fun xStar' => convexBifunctionCanonicalAdjointPairing F xStar' u) xStar =
      convexBifunctionCanonicalAdjointPairing F xStar u := by
  let q : (Fin n → ℝ) → EReal := fun xStar' => convexBifunctionCanonicalAdjointPairing F xStar' u
  have hConv : ConvexFunction q := by
    simpa [q] using
      helperForTheorem33_2_convexAdjointPairingSection_convexFunction hGraph hNoBot u
  have hxq :
      xStar ∈ euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) q) := by
    have hEqDom :
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) q =
          {xStar' | ∃ u' : Fin m → ℝ, convexBifunctionAdjointPairing F xStar' u' ≠ ⊥} := by
      simpa [q] using
        helperForCorollary33_2_1_adjointPairingSection_effectiveDomain_eq
          (F := F) u
    have hxq' :
        xStar ∈ intrinsicInterior ℝ
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) q) := by
      rw [hEqDom]
      exact hxStar
    -- Transport the textbook `ri (dom F^*)` hypothesis to the effective domain of `q`.
    rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior]
    exact hxq'
  exact
    helperForCorollary33_2_1_convexFunctionClosure_eq_self_on_ri_effectiveDomain_fin_of_ConvexFunction
      (f := q) hConv hxq

/-- Helper for Corollary33.2.1: on the convex side, the frozen pairing section is already fixed
by the Section 33 concave closure on the intrinsic interior of its effective domain. -/
lemma helperForCorollary33_2_1_convexPairingSection_closure_eq_self_on_intrinsicInterior
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hGraph : IsGraphConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    {u : Fin m → ℝ}
    (hu : u ∈ intrinsicInterior ℝ {u' | ∃ x : Fin n → ℝ, F u' x < ⊤})
    (xStar : Fin n → ℝ) :
    concaveClosure (fun u' => convexBifunctionPairing F u' xStar) u =
      convexBifunctionPairing F u xStar := by
  let q : (Fin m → ℝ) → EReal := fun u' => -convexBifunctionPairing F u' xStar
  have hNegClosure :
      convexFunctionClosure q u = q u :=
    helperForCorollary33_2_1_negConvexPairingSection_functionConvexClosure_eq_self_on_intrinsicInterior
      (F := F) hGraph hNoBot hu xStar
  have hSignFlip :
      concaveClosure (fun u' => convexBifunctionPairing F u' xStar) u =
        -convexFunctionClosure q u := by
    rfl
  -- Step 2: substitute the raw convex-closure fixed-point identity for the negated section.
  calc
    concaveClosure (fun u' => convexBifunctionPairing F u' xStar) u =
        -convexFunctionClosure q u := hSignFlip
    _ = -q u := by rw [hNegClosure]
    _ = convexBifunctionPairing F u xStar := by simp [q]

/-- Helper for Corollary33.2.1: on the concave side, the frozen pairing section is already fixed
by the Section 33 convex closure on the intrinsic interior of its effective domain. -/
lemma helperForCorollary33_2_1_concavePairingSection_closure_eq_self_on_intrinsicInterior
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hGraph : IsGraphConcaveBifunction F)
    (hNoTop : HasNoTopValuesBifunction F)
    {u : Fin m → ℝ}
    (hu : u ∈ intrinsicInterior ℝ {u' | ∃ x : Fin n → ℝ, F u' x ≠ ⊥})
    (xStar : Fin n → ℝ) :
    convexFunctionClosure (fun u' => concaveBifunctionPairing F u' xStar) u =
      concaveBifunctionPairing F u xStar := by
  have hConvFun : ConvexFunction (fun u' : Fin m → ℝ =>
      concaveBifunctionPairing F u' xStar) :=
    helperForTheorem33_2_concavePairingSection_convexFunction hGraph hNoTop xStar
  have hu' :
      u ∈ euclideanRelativeInterior_fin m
        (effectiveDomain (Set.univ : Set (Fin m → ℝ))
          (fun u' : Fin m → ℝ => concaveBifunctionPairing F u' xStar)) := by
    have hEqDom :
        effectiveDomain (Set.univ : Set (Fin m → ℝ))
          (fun u' : Fin m → ℝ => concaveBifunctionPairing F u' xStar) =
            {u' | ∃ x : Fin n → ℝ, F u' x ≠ ⊥} := by
      exact
        helperForCorollary33_2_1_concavePairingSection_effectiveDomain_eq
          (F := F) xStar
    -- Here the effective domain is exactly `{u' | ∃ x, F u' x ≠ ⊥}`.
    have hu'' :
        u ∈ intrinsicInterior ℝ
          (effectiveDomain (Set.univ : Set (Fin m → ℝ))
            (fun u' : Fin m → ℝ => concaveBifunctionPairing F u' xStar)) := by
      rw [hEqDom]
      exact hu
    rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior]
    exact hu''
  exact
    helperForCorollary33_2_1_convexFunctionClosure_eq_self_on_ri_effectiveDomain_fin_of_ConvexFunction
      (f := fun u' : Fin m → ℝ => concaveBifunctionPairing F u' xStar) hConvFun hu'

/-- Helper for Corollary33.2.1: negating `F` converts the concave pairing into the negative of
the corresponding convex pairing. -/
lemma helperForCorollary33_2_1_concavePairing_eq_neg_convexPairing_of_neg
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) :
    concaveBifunctionPairing F u xStar =
      -convexBifunctionPairing (fun u x => -F u x) u (-xStar) := by
  -- Step 1: rewrite the concave pairing by the unrestricted Chapter 6 sign-change formula.
  -- Step 2: recognize the resulting Fenchel conjugate as the convex pairing of `-F`.
  rw [concaveBifunctionPairing]
  simpa [convexBifunctionPairing, convexConjugate, bifunctionPairingNotation] using
    helperForTheorem_6_30_3_concaveConjugate_eq_neg_fenchelConjugate_neg_unrestricted
      (g := F u) xStar

lemma helperForCorollary33_2_1_concaveAdjoint_eq_neg_convexAdjoint_of_neg
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (xStar : Fin n → ℝ) (u : Fin m → ℝ) :
    concaveBifunctionAdjointPairing F xStar u =
      -convexBifunctionAdjointPairing (fun u' x => -F u' x) (-xStar) (-u) := by
  let G : (Fin m → ℝ) → (Fin n → ℝ) → EReal := fun u' x => -F u' x
  let g : (Fin m → ℝ) → EReal := fun u' => convexBifunctionPairing G u' (-xStar)
  have hSection : (fun u' => concaveBifunctionPairing F u' xStar) = fun u' => -g u' := by
    funext u'
    have h := helperForCorollary33_1_2_convexPairing_negated_eq_neg_concavePairing
      (F := F) u' (-xStar)
    simpa [G, g] using (congrArg Neg.neg h).symm
  rw [concaveBifunctionAdjointPairing, convexBifunctionAdjointPairing]
  change convexConjugate (fun u' => concaveBifunctionPairing F u' xStar) u = _
  rw [hSection]
  have h := congrFun
    (helperForTheorem_6_30_3_neg_concaveConjugate_eq_fenchel_precomp_neg (g := g)) (-u)
  simpa [convexConjugate, g] using h.symm

/-- Helper for Corollary33.2.1: negating `F` also converts the adjoint pairing into the negative
of the corresponding convex adjoint pairing, with the expected sign flip in the parameter
variable coming from the Chapter 6 conjugation formula. -/
lemma helperForCorollary33_2_1_concaveAdjointPairing_eq_adjointOfConcaveBifunction
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hConc : ConcaveBifunction F)
    (xStar : Fin n → ℝ) (u : Fin m → ℝ) :
    concaveBifunctionAdjointPairing F xStar u =
      adjointOfConcaveBifunction ⟨F, hConc⟩ xStar u := by
  exact helperForTheorem33_2_convexConjugate_concavePairing_eq_adjointOfConcave
    hConc xStar u

lemma helperForCorollary33_2_1_concaveAdjointPairing_eq_neg_convexAdjointPairing_of_neg
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (xStar : Fin n → ℝ) (u : Fin m → ℝ) :
    concaveBifunctionCanonicalAdjointPairing F xStar u =
      -convexBifunctionCanonicalAdjointPairing (fun u x => -F u x) (-xStar) u := by
  let A : (Fin m → ℝ) → EReal :=
    convexBifunctionAdjointPairing (fun u' x => -F u' x) (-xStar)
  have hSection : concaveBifunctionAdjointPairing F xStar = fun v => -A (-v) := by
    funext v
    exact helperForCorollary33_2_1_concaveAdjoint_eq_neg_convexAdjoint_of_neg
      (F := F) xStar v
  rw [concaveBifunctionCanonicalAdjointPairing, convexBifunctionCanonicalAdjointPairing, hSection]
  have hPre := congrFun
    (helperForTheorem_21_4_fenchelConjugate_precomp_neg
      (n := m) (g := fun v => -A v)) u
  have hNeg := congrFun
    (helperForTheorem_6_30_3_neg_concaveConjugate_eq_fenchel_precomp_neg (g := A)) u
  simpa [convexConjugate, A] using hPre.trans hNeg.symm

lemma helperForCorollary33_2_1_neg_concaveAdjointPairingSection_eq_convexAdjointPairingSection_precomp_neg_of_neg
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) :
    (fun xStar' => -concaveBifunctionCanonicalAdjointPairing F xStar' u) =
      fun xStar' =>
        convexBifunctionCanonicalAdjointPairing (fun u' x => -F u' x) (-xStar') u := by
  funext xStar'
  rw [helperForCorollary33_2_1_concaveAdjointPairing_eq_neg_convexAdjointPairing_of_neg
    (F := F) xStar' u]
  simp

lemma helperForCorollary33_2_1_precompose_neg_isERealConvexOn
    {k : ℕ}
    {f : (Fin k → ℝ) → EReal}
    (hConv : IsERealConvexOn (Set.univ : Set (Fin k → ℝ)) f) :
    IsERealConvexOn (Set.univ : Set (Fin k → ℝ)) (fun x => f (-x)) := by
  intro x y hx hy a b ha hb hab hxy
  have hBase :
      f (a • (-x) + b • (-y)) ≤ (a : EReal) * f (-x) + (b : EReal) * f (-y) :=
    hConv (x := -x) (y := -y) (by simp) (by simp) ha hb hab (by simpa [smul_neg, neg_add] using hxy)
  simpa [smul_neg, neg_add, add_comm, add_left_comm, add_assoc] using hBase


lemma helperForCorollary33_2_1_precompose_neg_isFunctionConvexClosed
    {k : ℕ}
    {f : (Fin k → ℝ) → EReal}
    (hClosed : IsFunctionConvexClosed f) :
    IsFunctionConvexClosed (fun x => f (-x)) := by
  have hLsc : LowerSemicontinuous f := by
    have hClosureLsc : LowerSemicontinuous (functionConvexClosure f) :=
      helperForLemma33_0_5_functionConvexClosure_lowerSemicontinuous (f := f)
    exact hClosed ▸ hClosureLsc
  have hNegCont : Continuous (fun x : Fin k → ℝ => -x) := by
    simpa using (continuous_neg : Continuous fun x : Fin k → ℝ => -x)
  have hPrecompLsc : LowerSemicontinuous (fun x : Fin k → ℝ => f (-x)) :=
    hLsc.comp_continuous hNegCont
  exact helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous hPrecompLsc

lemma helperForCorollary33_2_1_precompose_neg_isFunctionConcaveClosed
    {k : ℕ}
    {f : (Fin k → ℝ) → EReal}
    (hClosed : IsFunctionConcaveClosed f) :
    IsFunctionConcaveClosed (fun x => f (-x)) := by
  have hNegClosed : IsFunctionConvexClosed (fun x : Fin k → ℝ => -f x) :=
    (helperForLemma33_0_22_functionConcaveClosed_iff_neg_isFunctionConvexClosed).mp hClosed
  have hPrecompNegClosed :
      IsFunctionConvexClosed (fun x : Fin k → ℝ => -(f (-x))) := by
    simpa using
      helperForCorollary33_2_1_precompose_neg_isFunctionConvexClosed
        (f := fun x : Fin k → ℝ => -f x) hNegClosed
  exact
    (helperForLemma33_0_22_functionConcaveClosed_iff_neg_isFunctionConvexClosed).mpr <| by
      simpa using hPrecompNegClosed

/-- Helper for Corollary33.2.1: graph-function concave-closedness upgrades a graph-concave
concave bifunction to a Chapter 6 closed concave bifunction. -/
lemma helperForCorollary33_2_1_closedConcaveBifunction_of_graphFunctionClosed
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hGraph : IsGraphConcaveBifunction F)
    (hNoTop : HasNoTopValuesBifunction F)
    (hGraphClosed : IsFunctionConcaveClosed (graphFunctionOfBifunction F)) :
    ClosedConcaveBifunction F := by
  let G : (Fin m → ℝ) → (Fin n → ℝ) → EReal := fun u' x => -F u' x
  have hGraphG : IsGraphConvexBifunction G := by
    simpa [G] using helperForTheorem33_2_negatedGraphConvex hGraph hNoTop
  have hNoBotG : HasNoBotValuesBifunction G := by
    intro u' x
    simpa [G, EReal.neg_eq_bot_iff] using hNoTop u' x
  have hGraphClosedG : IsFunctionConvexClosed (graphFunctionOfBifunction G) := by
    funext z
    -- Evaluate the graph-level concave-closure fixed-point identity pointwise, then flip signs.
    have hClosedPoint :
        graphFunctionOfBifunction F z =
          functionConcaveClosure (graphFunctionOfBifunction F) z :=
      congrArg (fun f => f z) hGraphClosed
    have hClosureRewrite :
        functionConcaveClosure (graphFunctionOfBifunction F) z =
          -functionConvexClosure
            (fun z' : Fin (m + n) → ℝ => -graphFunctionOfBifunction F z') z :=
      congrArg
        (fun f : (Fin (m + n) → ℝ) → EReal => f z)
        (helperForCorollary33_2_1_functionConcaveClosure_eq_neg_functionConvexClosure_neg
          (g := graphFunctionOfBifunction F))
    have hNegClosed :
        -graphFunctionOfBifunction F z =
          functionConvexClosure
            (fun z' : Fin (m + n) → ℝ => -graphFunctionOfBifunction F z') z := by
      have hPoint :
          graphFunctionOfBifunction F z =
            -functionConvexClosure
              (fun z' : Fin (m + n) → ℝ => -graphFunctionOfBifunction F z') z :=
        hClosedPoint.trans hClosureRewrite
      simpa using congrArg Neg.neg hPoint
    simpa [G, graphFunctionOfBifunction] using hNegClosed
  -- Package the negated graph as a closed convex bifunction, then translate back.
  have hClosedG :
      ClosedConvexBifunction G :=
    helperForCorollary33_2_1_closedConvexBifunction_of_graphFunctionClosed
      (F := G) hGraphG hNoBotG hGraphClosedG
  refine ⟨?_, ?_⟩
  · -- Graph convexity of `G = -F` is exactly graph concavity of `F`.
    simpa [ConcaveBifunction, ConvexBifunction, G, bifunctionGraphFunction] using hClosedG.1
  -- Closed concavity of `F` is exactly lower semicontinuity of the negated graph, which is the
  -- closedness field already proved for `G = -F`.
  simpa [ClosedConcaveERealFunction, G, bifunctionGraphFunction, graphFunctionOfBifunction]
    using hClosedG.2.2

/-- Helper for Corollary33.2.1: a closed concave bifunction with no `⊤` values already has
its graph function fixed by the raw concave-closure operator. -/
lemma helperForCorollary33_2_1_graphFunction_isFunctionConcaveClosed_of_closedConcaveBifunction
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hClosed : ClosedConcaveBifunction F)
    (hNoTop : HasNoTopValuesBifunction F) :
    IsFunctionConcaveClosed (graphFunctionOfBifunction F) := by
  have hNegGraphNeBot :
      ∀ z : Fin (m + n) → ℝ, -bifunctionGraphFunction F z ≠ (⊥ : EReal) := by
    intro z
    simpa [bifunctionGraphFunction, EReal.neg_eq_bot_iff] using
      hNoTop (fun i : Fin m => z (Fin.castAdd n i)) (fun j : Fin n => z (Fin.natAdd m j))
  have hClosureFixed : concaveBifunctionClosure F = F :=
    helperForTheorem_6_30_11_concaveBifunctionClosure_eq_self_of_closed hClosed hNegGraphNeBot
  unfold IsFunctionConcaveClosed
  funext z
  let u : Fin m → ℝ := fun i => z (Fin.castAdd n i)
  let x : Fin n → ℝ := fun j => z (Fin.natAdd m j)
  have hPoint : concaveBifunctionClosure F u x = F u x := by
    exact congrArg (fun H => H u x) hClosureFixed
  have hAppend : Fin.append u x = z := by
    funext i
    by_cases hi : i.1 < m
    · let i' : Fin m := ⟨i.1, hi⟩
      have hiEq : Fin.castAdd n i' = i := by
        ext
        simp [i']
      rw [← hiEq]
      simp [u]
    · have hge : m ≤ i.1 := Nat.le_of_not_gt hi
      let j : Fin n := ⟨i.1 - m, by omega⟩
      have hjEq : Fin.natAdd m j = i := by
        ext
        simp [j]
        omega
      rw [← hjEq]
      simp [x]
  have hPoint' :
      -convexFunctionClosure (fun z' : Fin (m + n) → ℝ => -graphFunctionOfBifunction F z') z =
        graphFunctionOfBifunction F z := by
    simpa [concaveBifunctionClosure, concaveClosure, graphFunctionOfBifunction,
      bifunctionGraphFunction, u, x, hAppend] using hPoint
  have hRewrite :
      functionConcaveClosure (graphFunctionOfBifunction F) z =
        -functionConvexClosure (fun z' : Fin (m + n) → ℝ => -graphFunctionOfBifunction F z') z := by
    exact
      congrArg (fun f : (Fin (m + n) → ℝ) → EReal => f z)
        (helperForCorollary33_2_1_functionConcaveClosure_eq_neg_functionConvexClosure_neg
          (g := graphFunctionOfBifunction F))
  have hConvexClosureEq :
      functionConvexClosure
          (fun z' : Fin (m + n) → ℝ => -graphFunctionOfBifunction F z') =
        convexFunctionClosure
          (fun z' : Fin (m + n) → ℝ => -graphFunctionOfBifunction F z') := by
    apply helperForTheorem33_1_functionConvexClosure_eq_convexFunctionClosure_of_noBot
    intro z'
    simpa [bifunctionGraphFunction, EReal.neg_eq_bot_iff] using
      hNoTop (fun i : Fin m => z' (Fin.castAdd n i)) (fun j : Fin n => z' (Fin.natAdd m j))
  calc
    graphFunctionOfBifunction F z =
        -convexFunctionClosure (fun z' : Fin (m + n) → ℝ => -graphFunctionOfBifunction F z') z :=
          hPoint'.symm
    _ =
        -functionConvexClosure (fun z' : Fin (m + n) → ℝ => -graphFunctionOfBifunction F z') z := by
          rw [hConvexClosureEq]
    _ = functionConcaveClosure (graphFunctionOfBifunction F) z := by
          rw [hRewrite]

/-- Helper for Corollary33.2.1: once graph-function concave-closedness identifies `F` with its
Chapter 6 concave closure, the concave pairing of the closure is the original concave pairing. -/
lemma helperForCorollary33_2_1_concaveClosure_pairing_eq_self_of_closed
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hGraph : IsGraphConcaveBifunction F)
    (hNoTop : HasNoTopValuesBifunction F)
    (hGraphClosed : IsFunctionConcaveClosed (graphFunctionOfBifunction F))
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) :
    concaveBifunctionPairing (concaveBifunctionClosure F) u xStar =
      concaveBifunctionPairing F u xStar := by
  -- Step 1: package the Section 33 hypotheses into the closed concave bifunction object needed
  -- by Theorem 6.30.11.
  have hClosed :
      ClosedConcaveBifunction F :=
    helperForCorollary33_2_1_closedConcaveBifunction_of_graphFunctionClosed
      (F := F) hGraph hNoTop hGraphClosed
  have hNegGraphNeBot :
      ∀ z : Fin (m + n) → ℝ, (-bifunctionGraphFunction F z) ≠ (⊥ : EReal) := by
    intro z
    simpa [bifunctionGraphFunction, EReal.neg_eq_bot_iff] using
      hNoTop (fun i : Fin m => z (Fin.castAdd n i)) (fun j : Fin n => z (Fin.natAdd m j))
  -- Step 2: collapse the Chapter 6 graph closure back to `F`, then transport that equality
  -- through the concave pairing operator.
  have hClosureFixed : concaveBifunctionClosure F = F :=
    helperForTheorem_6_30_11_concaveBifunctionClosure_eq_self_of_closed
      (G := F) hClosed hNegGraphNeBot
  simpa using congrArg (fun G => concaveBifunctionPairing G u xStar) hClosureFixed

/-- For fixed `u`, the corrected adjoint pairing of a graph-concave bifunction is concave
in `xStar`.  The all-`⊥` branch is handled explicitly because its adjoint is improper. -/
lemma helperForCorollary33_2_1_concaveAdjointPairingSection_concaveFunction
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hGraph : IsGraphConcaveBifunction F)
    (hNoTop : HasNoTopValuesBifunction F)
    (u : Fin m → ℝ) :
    ConcaveFunction (fun xStar => concaveBifunctionCanonicalAdjointPairing F xStar u) := by
  by_cases hAllBot : ∀ u' x, F u' x = ⊥
  · have hPair : ∀ u' xStar, concaveBifunctionPairing F u' xStar = ⊤ := by
      intro u' xStar
      simp [concaveBifunctionPairing, bifunctionPairingNotation,
        conjugatePairingNotation, hAllBot]
    have hAdj : ∀ xStar uStar, concaveBifunctionAdjointPairing F xStar uStar = ⊥ := by
      intro xStar uStar
      rw [concaveBifunctionAdjointPairing, convexConjugate, fenchelConjugate_eq_iSup]
      simp [hPair]
    have hEq :
        (fun xStar => concaveBifunctionCanonicalAdjointPairing F xStar u) =
          fun _ : Fin n → ℝ => (⊤ : EReal) := by
      funext xStar
      rw [concaveBifunctionCanonicalAdjointPairing, convexConjugate, fenchelConjugate_eq_iSup]
      simp [hAdj]
    rw [hEq]
    unfold ConcaveFunction
    apply helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction
    intro x y hx hy a b ha hb hab hxy
    simp
  · push_neg at hAllBot
    rcases hAllBot with ⟨u₀, x₀, hFinite⟩
    have hF : ConcaveBifunction F := by
      unfold ConcaveBifunction
      have hNoTopGraph : ∀ z : Fin (m + n) → ℝ,
          graphFunctionOfBifunction F z ≠ ⊤ := by
        intro z
        simpa [graphFunctionOfBifunction] using
          hNoTop (fun i : Fin m => z (Fin.castAdd n i))
            (fun j : Fin n => z (Fin.natAdd m j))
      have hNeg := helperForCorollary33_1_2_concaveNegation_isConvex_of_noTop
        (hConc := hGraph) (hNoTop := hNoTopGraph)
      simpa [IsGraphConcaveBifunction, bifunctionGraphFunction,
        graphFunctionOfBifunction] using
        helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction hNeg
    let A : (Fin n → ℝ) → (Fin m → ℝ) → EReal :=
      adjointOfConcaveBifunction ⟨F, hF⟩
    have hAConv : ConvexBifunction A :=
      (adjointOfConcaveBifunction_closedConvex ⟨F, hF⟩).1
    have hANoBot : HasNoBotValuesBifunction A := by
      intro xStar uStar
      unfold A adjointOfConcaveBifunction
      rw [sSup_range]
      apply ne_of_gt
      refine lt_of_lt_of_le ?_ (le_iSup (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
        F p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) +
          (((p.1 ⬝ᵥ uStar : ℝ) : EReal))) (u₀, x₀))
      have hCoe := EReal.coe_toReal (x := F u₀ x₀) (hNoTop u₀ x₀) hFinite
      rw [← hCoe, ← EReal.coe_sub, ← EReal.coe_add]
      exact EReal.bot_lt_coe _
    have hGraphA : IsGraphConvexBifunction A := by
      have hLocal := helperForLemma33_0_5_convexFunction_to_isERealConvexOn_univ
        (f := bifunctionGraphFunction A) hAConv (by
          intro z
          simpa [bifunctionGraphFunction] using
            hANoBot (fun i : Fin n => z (Fin.castAdd m i))
              (fun j : Fin m => z (Fin.natAdd n j)))
      simpa [IsGraphConvexBifunction, graphFunctionOfBifunction,
        bifunctionGraphFunction] using hLocal
    have hEq :
        (fun xStar => concaveBifunctionCanonicalAdjointPairing F xStar u) =
          fun xStar => convexBifunctionPairing A xStar u := by
      funext xStar
      unfold concaveBifunctionCanonicalAdjointPairing
      congr 1
      funext uStar
      exact helperForTheorem33_2_convexConjugate_concavePairing_eq_adjointOfConcave
        hF xStar uStar
    rw [hEq]
    exact helperForTheorem33_2_convexPairingSection_concaveFunction hGraphA u

/-- On `ri (dom F⁺)`, the corrected concave adjoint-pairing section is fixed by the
canonical concave closure appearing in Theorem 33.2. -/
lemma helperForCorollary33_2_1_concaveAdjointPairingSection_concaveClosure_eq_self_on_intrinsicInterior
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hGraph : IsGraphConcaveBifunction F)
    (hNoTop : HasNoTopValuesBifunction F)
    (u : Fin m → ℝ)
    {xStar : Fin n → ℝ}
    (hxStar : xStar ∈ intrinsicInterior ℝ
      {xStar' | ∃ u' : Fin m → ℝ, concaveBifunctionAdjointPairing F xStar' u' ≠ ⊤}) :
    concaveClosure (fun xStar' => concaveBifunctionCanonicalAdjointPairing F xStar' u) xStar =
      concaveBifunctionCanonicalAdjointPairing F xStar u := by
  have hConc :=
    helperForCorollary33_2_1_concaveAdjointPairingSection_concaveFunction
      (F := F) hGraph hNoTop u
  have hxDom :
      xStar ∈ euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (fun xStar' => -concaveBifunctionCanonicalAdjointPairing F xStar' u)) := by
    rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior]
    rw [helperForCorollary33_2_1_concaveAdjointPairingSection_concaveEffectiveDomain_eq
      (F := F) u]
    exact hxStar
  exact
    helperForCorollary33_2_1_concaveClosure_eq_self_on_ri_concaveEffectiveDomain_fin
      (g := fun xStar' => concaveBifunctionCanonicalAdjointPairing F xStar' u) hConc hxDom

/-- Helper for Corollary33.2.1: in the closed convex branch, the pairing identity holds on the
intrinsic interior of the adjoint effective domain. -/
lemma helperForCorollary33_2_1_closedConvex_pairing_eq_on_intrinsicInteriorAdjointDomain
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hGraph : IsGraphConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    (hGraphClosed : IsFunctionConvexClosed (graphFunctionOfBifunction F))
    {xStar : Fin n → ℝ}
    (hxStar : xStar ∈ intrinsicInterior ℝ
      {xStar' | ∃ u : Fin m → ℝ, convexBifunctionAdjointPairing F xStar' u ≠ ⊥}) :
    ∀ u : Fin m → ℝ,
      convexBifunctionPairing F u xStar =
        convexBifunctionCanonicalAdjointPairing F xStar u := by
  intro u
  have hClosed : ClosedConvexBifunction F :=
    helperForCorollary33_2_1_closedConvexBifunction_of_graphFunctionClosed
      (F := F) hGraph hNoBot hGraphClosed
  rcases
      (adjoint_pairing_eq_coordinatewise_closures (m := m) (n := n)).1 F
        ⟨hGraph, hNoBot⟩ with
    ⟨_hFirst, hSecond⟩
  have hClosurePairing :
      convexBifunctionPairing (convexBifunctionClosure F) u xStar =
        convexBifunctionPairing F u xStar :=
    helperForCorollary33_2_1_convexClosure_pairing_eq_self_of_closed
      (F := F) hGraph hNoBot hGraphClosed u xStar
  have hAdjointClosure :
      convexFunctionClosure (fun xStar' => convexBifunctionCanonicalAdjointPairing F xStar' u) xStar =
        convexBifunctionCanonicalAdjointPairing F xStar u :=
    helperForCorollary33_2_1_adjointPairingSection_functionConvexClosure_eq_self_on_intrinsicInterior
      (F := F) hGraph hNoBot hGraphClosed u hxStar
  -- The closure theorem consumes the genuine adjoint effective domain
  -- `ri {xStar' | ∃ u', convexBifunctionAdjointPairing F xStar' u' ≠ ⊥}`.
  calc
    convexBifunctionPairing F u xStar =
        convexBifunctionPairing (convexBifunctionClosure F) u xStar := by
          exact hClosurePairing.symm
    _ =
        convexFunctionClosure (fun xStar' => convexBifunctionCanonicalAdjointPairing F xStar' u) xStar := by
          exact (hSecond u xStar).symm
    _ = convexBifunctionCanonicalAdjointPairing F xStar u := hAdjointClosure

/-- Helper for Corollary33.2.1: in the closed concave branch, the pairing identity follows by
combining Theorem 33.2 with the Chapter 6 closed-adjoint slice theorem. -/
lemma helperForCorollary33_2_1_closedConcave_pairing_eq_on_intrinsicInteriorAdjointDomain
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hGraph : IsGraphConcaveBifunction F)
    (hNoTop : HasNoTopValuesBifunction F)
    (hGraphClosed : IsFunctionConcaveClosed (graphFunctionOfBifunction F))
    {xStar : Fin n → ℝ}
    (hxStar : xStar ∈ intrinsicInterior ℝ
      {xStar' | ∃ u : Fin m → ℝ, concaveBifunctionAdjointPairing F xStar' u ≠ ⊤}) :
    ∀ u : Fin m → ℝ,
      concaveBifunctionPairing F u xStar =
        concaveBifunctionCanonicalAdjointPairing F xStar u := by
  intro u
  rcases
      (adjoint_pairing_eq_coordinatewise_closures (m := m) (n := n)).2 F
        ⟨hGraph, hNoTop⟩ with
    ⟨_hFirst, hSecond⟩
  have hClosurePairing :
      concaveBifunctionPairing (concaveBifunctionClosure F) u xStar =
        concaveBifunctionPairing F u xStar :=
    helperForCorollary33_2_1_concaveClosure_pairing_eq_self_of_closed
      (F := F) hGraph hNoTop hGraphClosed u xStar
  have hAdjointClosure :
      concaveClosure (fun xStar' => concaveBifunctionCanonicalAdjointPairing F xStar' u) xStar =
        concaveBifunctionCanonicalAdjointPairing F xStar u :=
    helperForCorollary33_2_1_concaveAdjointPairingSection_concaveClosure_eq_self_on_intrinsicInterior
      (F := F) hGraph hNoTop u hxStar
  calc
    concaveBifunctionPairing F u xStar =
        concaveBifunctionPairing (concaveBifunctionClosure F) u xStar := by
          exact hClosurePairing.symm
    _ =
        concaveClosure (fun xStar' => concaveBifunctionCanonicalAdjointPairing F xStar' u) xStar := by
          exact (hSecond u xStar).symm
    _ = concaveBifunctionCanonicalAdjointPairing F xStar u := hAdjointClosure

-- Proof sketch: combine Theorem33.2 with the standard fact that a convex or concave closure
-- agrees with the original function on the relative interior of its effective domain. This turns
-- the closure identities from Theorem33.2 into the direct adjoint-pairing identity
-- `⟪F u, x^*⟫ = ⟪u, F^* x^*⟫` on `ri (dom F)`; in the closed case the same argument on
-- `ri (dom F^*)`, interpreted through the genuine adjoint bifunction `xStar ↦ F^* xStar`,
-- yields the corresponding identity for every `u`. The concave branch is dual.
/-- Corollary33.2.1: Let `F : ℝ^m → (ℝ^n → EReal)` be a convex or concave bifunction.
If `u ∈ ri (dom F)` in the parameter variable, modeled here by
`u ∈ intrinsicInterior ℝ {u' | ∃ x, F u' x < ⊤}` on the convex side and by
`u ∈ intrinsicInterior ℝ {u' | ∃ x, F u' x ≠ ⊥}` on the concave side, then
the pairing identity `⟪F u, x^*⟫ = ⟪u, F^* x^*⟫` holds for every `x^*`.

If `F` is closed, modeled by closedness of the graph function, and `x^* ∈ ri (dom F^*)`,
modeled by `x^*` lying in the intrinsic interior of the effective domain of the genuine
adjoint bifunction `xStar ↦ F^* xStar`, then the same pairing identity holds for every
`u`. -/
theorem adjoint_pairing_eq_on_relativeInterior_domains
    {m n : ℕ} :
    (∀ {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal},
      (IsGraphConvexBifunction F ∧ HasNoBotValuesBifunction F) →
        (∀ ⦃u : Fin m → ℝ⦄,
          u ∈ intrinsicInterior ℝ {u' | ∃ x : Fin n → ℝ, F u' x < ⊤} →
            ∀ xStar : Fin n → ℝ,
              convexBifunctionPairing F u xStar =
                convexBifunctionCanonicalAdjointPairing F xStar u) ∧
        (IsFunctionConvexClosed (graphFunctionOfBifunction F) →
          ∀ ⦃xStar : Fin n → ℝ⦄,
            xStar ∈ intrinsicInterior ℝ
                {xStar' | ∃ u : Fin m → ℝ, convexBifunctionAdjointPairing F xStar' u ≠ ⊥} →
              ∀ u : Fin m → ℝ,
                convexBifunctionPairing F u xStar =
                  convexBifunctionCanonicalAdjointPairing F xStar u)) ∧
    (∀ {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal},
      (IsGraphConcaveBifunction F ∧ HasNoTopValuesBifunction F) →
        (∀ ⦃u : Fin m → ℝ⦄,
          u ∈ intrinsicInterior ℝ {u' | ∃ x : Fin n → ℝ, F u' x ≠ ⊥} →
            ∀ xStar : Fin n → ℝ,
              concaveBifunctionPairing F u xStar =
                concaveBifunctionCanonicalAdjointPairing F xStar u) ∧
        (IsFunctionConcaveClosed (graphFunctionOfBifunction F) →
          ∀ ⦃xStar : Fin n → ℝ⦄,
            xStar ∈ intrinsicInterior ℝ
                {xStar' | ∃ u : Fin m → ℝ, concaveBifunctionAdjointPairing F xStar' u ≠ ⊤} →
              ∀ u : Fin m → ℝ,
                concaveBifunctionPairing F u xStar =
                  concaveBifunctionCanonicalAdjointPairing F xStar u)) := by
  -- This is the relative-interior corollary of Theorem 33.2 after realigning the pairing
  -- object with the textbook `u`-variable conjugate of the adjoint section.
  constructor
  · intro F hF
    rcases hF with ⟨hGraph, hNoBot⟩
    refine ⟨?_, ?_⟩
    · intro u hu xStar
      rcases
          (adjoint_pairing_eq_coordinatewise_closures (m := m) (n := n)).1 F
            ⟨hGraph, hNoBot⟩ with
        ⟨hFirst, _hSecond⟩
      have hClosureEq :
          concaveClosure (fun u' => convexBifunctionPairing F u' xStar) u =
            convexBifunctionPairing F u xStar :=
        helperForCorollary33_2_1_convexPairingSection_closure_eq_self_on_intrinsicInterior
          (F := F) hGraph hNoBot hu xStar
      -- Substitute the relative-interior fixed-point identity into the first closure formula.
      calc
        convexBifunctionPairing F u xStar =
            concaveClosure (fun u' => convexBifunctionPairing F u' xStar) u := by
          symm
          exact hClosureEq
        _ = convexBifunctionCanonicalAdjointPairing F xStar u := by
          symm
          exact hFirst xStar u
    · intro hGraphClosed xStar hxStar u
      exact
        helperForCorollary33_2_1_closedConvex_pairing_eq_on_intrinsicInteriorAdjointDomain
          (F := F) hGraph hNoBot hGraphClosed hxStar u
  · intro F hF
    rcases hF with ⟨hGraph, hNoTop⟩
    refine ⟨?_, ?_⟩
    · intro u hu xStar
      rcases
          (adjoint_pairing_eq_coordinatewise_closures (m := m) (n := n)).2 F
            ⟨hGraph, hNoTop⟩ with
        ⟨hFirst, _hSecond⟩
      have hClosureEq :
          convexFunctionClosure (fun u' => concaveBifunctionPairing F u' xStar) u =
            concaveBifunctionPairing F u xStar :=
        helperForCorollary33_2_1_concavePairingSection_closure_eq_self_on_intrinsicInterior
          (F := F) hGraph hNoTop hu xStar
      -- Substitute the relative-interior fixed-point identity into the dual closure formula.
      calc
        concaveBifunctionPairing F u xStar =
            convexFunctionClosure (fun u' => concaveBifunctionPairing F u' xStar) u := by
          symm
          exact hClosureEq
        _ = concaveBifunctionCanonicalAdjointPairing F xStar u := by
          exact (hFirst xStar u).symm
    · intro hGraphClosed xStar hxStar u
      -- Route correction: the closed concave branch will also be handled locally on
      -- `ri (dom F^*)` after transporting to the convex branch for `-F`.
      exact
        helperForCorollary33_2_1_closedConcave_pairing_eq_on_intrinsicInteriorAdjointDomain
          (F := F) hGraph hNoTop hGraphClosed hxStar u

end Section33
end Chap07

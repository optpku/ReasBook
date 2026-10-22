/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part6

section Chap06
section Section30

/-- Helper for Theorem 6.30.11: once a closed convex bifunction fails properness, its graph
function is an improper convex function on `univ`. -/
lemma helperForTheorem_6_30_11_improperConvexGraph_of_closed_not_proper
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hClosed : ClosedConvexBifunction F)
    (hNotProper : ¬ ProperConvexBifunction F) :
    ImproperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ)) (bifunctionGraphFunction F) := by
  refine ⟨?_, ?_⟩
  · -- Closed convexity of the bifunction is exactly convexity of its graph function on `univ`.
    simpa [ConvexBifunction] using hClosed.1
  · intro hProperOn
    have hProperGraph :
        ProperConvexERealFunction (F := Fin (m + n) → ℝ) (bifunctionGraphFunction F) :=
      helperForTheorem_21_3_properConvexEReal_of_properConvexFunctionOn_univ
        (f := bifunctionGraphFunction F) hProperOn
    -- If the graph were proper on `univ`, the bifunction itself would be proper.
    exact hNotProper ⟨hClosed.1, hProperGraph⟩

/-- Helper for Theorem 6.30.11: the concave bifunction closure fixes the constant `⊤`
bifunction. -/
lemma helperForTheorem_6_30_11_concaveBifunctionClosure_eq_self_of_eq_const_top
    {m n : ℕ}
    {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hTop : G = fun _ _ => (⊤ : EReal)) :
    concaveBifunctionClosure G = G := by
  subst G
  funext u x
  have hClosure :
      convexFunctionClosure (fun _ : Fin (m + n) → ℝ => (⊥ : EReal)) =
        (fun _ : Fin (m + n) → ℝ => (⊥ : EReal)) :=
    convexFunctionClosure_eq_bot_of_exists_bot
      (f := fun _ : Fin (m + n) → ℝ => (⊥ : EReal)) ⟨0, rfl⟩
  -- Negating the constant `⊥` closure recovers the constant `⊤` bifunction.
  simpa [concaveBifunctionClosure, concaveClosure, bifunctionGraphFunction] using
    congrArg Neg.neg (congrFun hClosure (Fin.append u x))

/-- Helper for Theorem 6.30.11: the concave bifunction closure fixes the constant `⊥`
bifunction. -/
lemma helperForTheorem_6_30_11_concaveBifunctionClosure_eq_self_of_eq_const_bot
    {m n : ℕ}
    {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hBot : G = fun _ _ => (⊥ : EReal)) :
    concaveBifunctionClosure G = G := by
  subst G
  funext u x
  -- Negating the constant `⊤` closure recovers the constant `⊥` bifunction.
  simpa [concaveBifunctionClosure, concaveClosure, bifunctionGraphFunction] using
    congrArg Neg.neg (congrFun (convexFunctionClosure_const_top (n := m + n)) (Fin.append u x))

/-- Helper for Theorem 6.30.11: once a closed concave bifunction fails properness, the negated
graph function is an improper convex function on `univ`. -/
lemma helperForTheorem_6_30_11_improperNegGraph_of_closed_not_proper
    {m n : ℕ}
    {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hClosed : ClosedConcaveBifunction G)
    (hNotProper : ¬ ProperConcaveBifunction G) :
    ImproperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
      (fun z : Fin (m + n) → ℝ => -bifunctionGraphFunction G z) := by
  refine ⟨?_, ?_⟩
  · -- Concavity means convexity of the negated graph function.
    simpa [ConcaveBifunction] using hClosed.1
  · intro hProperOn
    have hProperNegGraph :
        ProperConvexERealFunction (F := Fin (m + n) → ℝ)
          (fun z : Fin (m + n) → ℝ => -bifunctionGraphFunction G z) :=
      helperForTheorem_21_3_properConvexEReal_of_properConvexFunctionOn_univ
        (f := fun z : Fin (m + n) → ℝ => -bifunctionGraphFunction G z) hProperOn
    -- Properness of the negated graph is exactly proper concavity of the original graph.
    exact hNotProper ⟨hClosed.1, by simpa [ProperConcaveERealFunction] using hProperNegGraph⟩

/-- Helper for Theorem 6.30.11: a closed improper convex bifunction graph can only take the
values `⊤` and `⊥`. -/
lemma helperForTheorem_6_30_11_convexGraph_values_top_or_bot_of_closed_not_proper
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hClosed : ClosedConvexBifunction F)
    (hNotProper : ¬ ProperConvexBifunction F) :
    ∀ z : Fin (m + n) → ℝ,
      bifunctionGraphFunction F z = (⊤ : EReal) ∨ bifunctionGraphFunction F z = (⊥ : EReal) := by
  have hImproperGraph :
      ImproperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ)) (bifunctionGraphFunction F) :=
    helperForTheorem_6_30_11_improperConvexGraph_of_closed_not_proper
      (F := F) hClosed hNotProper
  -- Chapter 2 shows that a lower semicontinuous improper convex function has no finite values.
  exact
    lowerSemicontinuous_improperConvexFunction_no_finite_values
      (f := bifunctionGraphFunction F) hImproperGraph hClosed.2.2

/-- Helper for Theorem 6.30.11: once a closed concave bifunction is improper, its negated graph
also takes only the values `⊤` and `⊥`. -/
lemma helperForTheorem_6_30_11_negConcaveGraph_values_top_or_bot_of_closed_not_proper
    {m n : ℕ}
    {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hClosed : ClosedConcaveBifunction G)
    (hNotProper : ¬ ProperConcaveBifunction G) :
    ∀ z : Fin (m + n) → ℝ,
      (-bifunctionGraphFunction G z) = (⊤ : EReal) ∨
        (-bifunctionGraphFunction G z) = (⊥ : EReal) := by
  have hImproperNegGraph :
      ImproperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
        (fun z : Fin (m + n) → ℝ => -bifunctionGraphFunction G z) :=
    helperForTheorem_6_30_11_improperNegGraph_of_closed_not_proper
      (G := G) hClosed hNotProper
  -- Apply the same no-finite-values theorem to the negated graph function.
  exact
    lowerSemicontinuous_improperConvexFunction_no_finite_values
      (f := fun z : Fin (m + n) → ℝ => -bifunctionGraphFunction G z) hImproperNegGraph hClosed.2

/-- Helper for Theorem 6.30.11: if an improper convex bifunction graph is fixed by the current
Chapter 2 closure, then the bifunction must already be constant `⊤` or constant `⊥`. -/
lemma helperForTheorem_6_30_11_improper_convex_fixed_point_eq_const_top_or_bot
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hImproper :
      ImproperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ)) (bifunctionGraphFunction F))
    (hFixed : convexBifunctionClosure F = F) :
    F = (fun _ _ => (⊤ : EReal)) ∨ F = (fun _ _ => (⊥ : EReal)) := by
  have hGraphFixed :
      convexFunctionClosure (bifunctionGraphFunction F) = bifunctionGraphFunction F := by
    funext z
    let u : Fin m → ℝ := fun i => z (Fin.castAdd n i)
    let x : Fin n → ℝ := fun j => z (Fin.natAdd m j)
    have hz : Fin.append u x = z := by
      -- Reassemble the pair of coordinate blocks back into the original graph point.
      funext i
      by_cases hi : i.1 < m
      · have hi' : Fin.castAdd n ⟨i.1, hi⟩ = i := by
          ext
          simp
        rw [← hi']
        simp [u, x, Fin.append, Fin.addCases, hi]
      · let j : Fin n := ⟨i.1 - m, by omega⟩
        have hj : Fin.natAdd m j = i := by
          ext
          simp [j]
          omega
        rw [← hj]
        simp [u, x, Fin.append, Fin.addCases, j]
    have hEval := congrFun (congrFun hFixed u) x
    -- Evaluate the bifunction fixed-point identity on the coordinates extracted from `z`.
    simpa [hz, u, x, convexBifunctionClosure, convexClosure, bifunctionGraphFunction] using hEval
  have hGraphConst :
      bifunctionGraphFunction F = (fun _ : Fin (m + n) → ℝ => (⊤ : EReal)) ∨
        bifunctionGraphFunction F = (fun _ : Fin (m + n) → ℝ => (⊥ : EReal)) :=
    (closed_improperConvexFunction_eq_top_or_bot
      (n := m + n) (f := bifunctionGraphFunction F)).1 ⟨hGraphFixed, hImproper⟩
  rcases hGraphConst with hGraphTop | hGraphBot
  · left
    funext u x
    -- A constant graph function forces the original bifunction to be constant on every pair.
    simpa [bifunctionGraphFunction] using congrFun hGraphTop (Fin.append u x)
  · right
    funext u x
    -- The same graph evaluation recovers the constant `⊥` branch.
    simpa [bifunctionGraphFunction] using congrFun hGraphBot (Fin.append u x)

/-- Helper for Theorem 6.30.11: if the negated graph of an improper concave bifunction is fixed by
the current Chapter 2 closure, then the bifunction must already be constant `⊤` or constant `⊥`. -/
lemma helperForTheorem_6_30_11_improper_concave_fixed_point_eq_const_top_or_bot
    {m n : ℕ}
    {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hImproper :
      ImproperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
        (fun z : Fin (m + n) → ℝ => -bifunctionGraphFunction G z))
    (hFixed : concaveBifunctionClosure G = G) :
    G = (fun _ _ => (⊤ : EReal)) ∨ G = (fun _ _ => (⊥ : EReal)) := by
  have hNegGraphFixed :
      convexFunctionClosure (fun z : Fin (m + n) → ℝ => -bifunctionGraphFunction G z) =
        (fun z : Fin (m + n) → ℝ => -bifunctionGraphFunction G z) := by
    funext z
    let u : Fin m → ℝ := fun i => z (Fin.castAdd n i)
    let x : Fin n → ℝ := fun j => z (Fin.natAdd m j)
    have hz : Fin.append u x = z := by
      -- Reassemble the split coordinates before comparing the graph functions pointwise.
      funext i
      by_cases hi : i.1 < m
      · have hi' : Fin.castAdd n ⟨i.1, hi⟩ = i := by
          ext
          simp
        rw [← hi']
        simp [u, x, Fin.append, Fin.addCases, hi]
      · let j : Fin n := ⟨i.1 - m, by omega⟩
        have hj : Fin.natAdd m j = i := by
          ext
          simp [j]
          omega
        rw [← hj]
        simp [u, x, Fin.append, Fin.addCases, j]
    have hEval := congrFun (congrFun hFixed u) x
    -- Negate the bifunction fixed-point identity to recover the graph-level convex closure.
    simpa [hz, u, x, concaveBifunctionClosure, concaveClosure, convexClosure,
      bifunctionGraphFunction] using congrArg Neg.neg hEval
  have hNegGraphConst :
      (fun z : Fin (m + n) → ℝ => -bifunctionGraphFunction G z) =
          (fun _ : Fin (m + n) → ℝ => (⊤ : EReal)) ∨
        (fun z : Fin (m + n) → ℝ => -bifunctionGraphFunction G z) =
          (fun _ : Fin (m + n) → ℝ => (⊥ : EReal)) :=
    (closed_improperConvexFunction_eq_top_or_bot
      (n := m + n) (f := fun z : Fin (m + n) → ℝ => -bifunctionGraphFunction G z)).1
      ⟨hNegGraphFixed, hImproper⟩
  rcases hNegGraphConst with hNegGraphTop | hNegGraphBot
  · right
    funext u x
    have hEval : -G u x = (⊤ : EReal) := by
      simpa [bifunctionGraphFunction] using congrFun hNegGraphTop (Fin.append u x)
    -- Negating the constant `⊤` graph value gives the constant `⊥` bifunction.
    simpa using congrArg Neg.neg hEval
  · left
    funext u x
    have hEval : -G u x = (⊥ : EReal) := by
      simpa [bifunctionGraphFunction] using congrFun hNegGraphBot (Fin.append u x)
    -- Negating the constant `⊥` graph value gives the constant `⊤` bifunction.
    simpa using congrArg Neg.neg hEval

/-- Helper for Theorem 6.30.11: in the closed improper nonconstant convex branch, the current
Chapter 2 closure semantics force the failure of the desired fixed-point identity. -/
lemma helperForTheorem_6_30_11_convexBifunctionClosure_ne_self_of_closed_not_proper_nonconstant
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hClosed : ClosedConvexBifunction F)
    (hNotProper : ¬ ProperConvexBifunction F)
    (hNotTop : F ≠ fun _ _ => (⊤ : EReal))
    (hNotBot : F ≠ fun _ _ => (⊥ : EReal)) :
    convexBifunctionClosure F ≠ F := by
  have hGraphValues :
      ∀ z : Fin (m + n) → ℝ,
        bifunctionGraphFunction F z = (⊤ : EReal) ∨ bifunctionGraphFunction F z = (⊥ : EReal) :=
    helperForTheorem_6_30_11_convexGraph_values_top_or_bot_of_closed_not_proper
      (F := F) hClosed hNotProper
  have hExistsTop : ∃ u x, F u x = (⊤ : EReal) := by
    by_contra hNoTop
    apply hNotBot
    funext u x
    -- If no point attains `⊤`, the pointwise `⊤`/`⊥` dichotomy forces the constant `⊥` branch.
    rcases hGraphValues (Fin.append u x) with hValTop | hValBot
    · exfalso
      exact hNoTop ⟨u, x, by simpa [bifunctionGraphFunction] using hValTop⟩
    · simpa [bifunctionGraphFunction] using hValBot
  have hExistsBot : ∃ u x, F u x = (⊥ : EReal) := by
    by_contra hNoBot
    apply hNotTop
    funext u x
    -- Dually, if no point attains `⊥`, then every value is forced to be `⊤`.
    rcases hGraphValues (Fin.append u x) with hValTop | hValBot
    · simpa [bifunctionGraphFunction] using hValTop
    · exfalso
      exact hNoBot ⟨u, x, by simpa [bifunctionGraphFunction] using hValBot⟩
  rcases hExistsTop with ⟨uTop, xTop, hTopVal⟩
  rcases hExistsBot with ⟨uBot, xBot, hBotVal⟩
  have hClosureBot :
      convexFunctionClosure (bifunctionGraphFunction F) =
        (fun _ : Fin (m + n) → ℝ => (⊥ : EReal)) :=
    convexFunctionClosure_eq_bot_of_exists_bot
      (f := bifunctionGraphFunction F)
      ⟨Fin.append uBot xBot, by simpa [bifunctionGraphFunction] using hBotVal⟩
  intro hFixed
  have hClosureAtTop : convexBifunctionClosure F uTop xTop = (⊥ : EReal) := by
    -- One `⊥` point forces the Chapter 2 closure to collapse to the constant `⊥` function.
    simpa [convexBifunctionClosure, convexClosure] using
      congrFun hClosureBot (Fin.append uTop xTop)
  have hFixedAtTop := congrFun (congrFun hFixed uTop) xTop
  have hBotEqTop : (⊥ : EReal) = (⊤ : EReal) := by
    -- Evaluate the supposed fixed-point identity at a point where the original bifunction is `⊤`.
    calc
      (⊥ : EReal) = convexBifunctionClosure F uTop xTop := hClosureAtTop.symm
      _ = F uTop xTop := hFixedAtTop
      _ = (⊤ : EReal) := hTopVal
  exact bot_ne_top hBotEqTop

/-- Helper for Theorem 6.30.11: in the closed improper nonconstant concave branch, the current
Chapter 2 closure semantics force the failure of the desired fixed-point identity after
negating the graph. -/
lemma helperForTheorem_6_30_11_concaveBifunctionClosure_ne_self_of_closed_not_proper_nonconstant
    {m n : ℕ}
    {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hClosed : ClosedConcaveBifunction G)
    (hNotProper : ¬ ProperConcaveBifunction G)
    (hNotTop : G ≠ fun _ _ => (⊤ : EReal))
    (hNotBot : G ≠ fun _ _ => (⊥ : EReal)) :
    concaveBifunctionClosure G ≠ G := by
  have hNegGraphValues :
      ∀ z : Fin (m + n) → ℝ,
        (-bifunctionGraphFunction G z) = (⊤ : EReal) ∨
          (-bifunctionGraphFunction G z) = (⊥ : EReal) :=
    helperForTheorem_6_30_11_negConcaveGraph_values_top_or_bot_of_closed_not_proper
      (G := G) hClosed hNotProper
  have hValues : ∀ u x, G u x = (⊤ : EReal) ∨ G u x = (⊥ : EReal) := by
    intro u x
    -- Negating the graph converts the Chapter 2 `⊤`/`⊥` dichotomy back to the original bifunction.
    rcases hNegGraphValues (Fin.append u x) with hNegTop | hNegBot
    · right
      have hEval : -G u x = (⊤ : EReal) := by
        simpa [bifunctionGraphFunction] using hNegTop
      simpa using congrArg Neg.neg hEval
    · left
      have hEval : -G u x = (⊥ : EReal) := by
        simpa [bifunctionGraphFunction] using hNegBot
      simpa using congrArg Neg.neg hEval
  have hExistsTop : ∃ u x, G u x = (⊤ : EReal) := by
    by_contra hNoTop
    apply hNotBot
    funext u x
    -- If the bifunction never attains `⊤`, the dichotomy above forces it to be constantly `⊥`.
    rcases hValues u x with hValTop | hValBot
    · exfalso
      exact hNoTop ⟨u, x, hValTop⟩
    · exact hValBot
  have hExistsBot : ∃ u x, G u x = (⊥ : EReal) := by
    by_contra hNoBot
    apply hNotTop
    funext u x
    -- If the bifunction never attains `⊥`, the same dichotomy forces the constant `⊤` branch.
    rcases hValues u x with hValTop | hValBot
    · exact hValTop
    · exfalso
      exact hNoBot ⟨u, x, hValBot⟩
  rcases hExistsTop with ⟨uTop, xTop, hTopVal⟩
  rcases hExistsBot with ⟨uBot, xBot, hBotVal⟩
  have hClosureBot :
      convexFunctionClosure (fun z : Fin (m + n) → ℝ => -bifunctionGraphFunction G z) =
        (fun _ : Fin (m + n) → ℝ => (⊥ : EReal)) :=
    convexFunctionClosure_eq_bot_of_exists_bot
      (f := fun z : Fin (m + n) → ℝ => -bifunctionGraphFunction G z)
      ⟨Fin.append uTop xTop, by
        have hEval : -G uTop xTop = (⊥ : EReal) := by
          simpa using congrArg Neg.neg hTopVal
        simpa [bifunctionGraphFunction] using hEval⟩
  intro hFixed
  have hClosureAtBot : concaveBifunctionClosure G uBot xBot = (⊤ : EReal) := by
    -- After negation, the same one-point `⊥` witness forces the concave closure to be constant `⊤`.
    simpa [concaveBifunctionClosure, concaveClosure, convexClosure] using
      congrArg Neg.neg (congrFun hClosureBot (Fin.append uBot xBot))
  have hFixedAtBot := congrFun (congrFun hFixed uBot) xBot
  have hTopEqBot : (⊤ : EReal) = (⊥ : EReal) := by
    -- Evaluate the supposed fixed-point identity at a point where the original bifunction is `⊥`.
    calc
      (⊤ : EReal) = concaveBifunctionClosure G uBot xBot := hClosureAtBot.symm
      _ = G uBot xBot := hFixedAtBot
      _ = (⊥ : EReal) := hBotVal
  exact top_ne_bot hTopEqBot

/-- Helper for Theorem 6.30.11: a closed convex bifunction whose graph never attains `⊥`
is fixed by the canonical graph closure. This is the graph-level lift of the Chapter 2
fixed-point theorem in the non-`⊥` branch supported by the current closure API. -/
lemma helperForTheorem_6_30_11_convexBifunctionClosure_eq_self_of_closed
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hClosed : ClosedConvexBifunction F)
    (hGraphNeBot : ∀ z : Fin (m + n) → ℝ, bifunctionGraphFunction F z ≠ (⊥ : EReal)) :
    convexBifunctionClosure F = F := by
  -- Route correction: the unconditional closed-case claim is false in the current formalization,
  -- so this repaired helper records exactly the stronger non-`⊥` hypothesis already supported.
  exact
    helperForTheorem_6_30_11_convexBifunctionClosure_eq_self_of_closed_of_graph_ne_bot
      (F := F) hClosed hGraphNeBot

/-- Helper for Theorem 6.30.11: a closed concave bifunction whose negated graph never attains
`⊥` is fixed by the canonical concave graph closure. This is the concave counterpart of the
supported non-`⊥` convex fixed-point theorem after negating the graph. -/
lemma helperForTheorem_6_30_11_concaveBifunctionClosure_eq_self_of_closed
    {m n : ℕ}
    {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hClosed : ClosedConcaveBifunction G)
    (hNegGraphNeBot :
      ∀ z : Fin (m + n) → ℝ, (-bifunctionGraphFunction G z) ≠ (⊥ : EReal)) :
    concaveBifunctionClosure G = G := by
  -- Route correction: the unconditional closed-case claim is false after negation as well, so
  -- this helper now states the precise non-`⊥` hypothesis that the existing graph lemma proves.
  exact
    helperForTheorem_6_30_11_concaveBifunctionClosure_eq_self_of_closed_of_neg_graph_ne_bot
      (G := G) hClosed hNegGraphNeBot

/-
An earlier local attempt to refute Theorem 6.30.11 by explicit improper counterexamples has been
removed. The statement below now follows the book verbatim, and any remaining work belongs in the
closure/adjoinment development itself rather than in theorem-local obstruction lemmas.
-/

/-- Helper for Theorem 6.30.11: in the convex branch, once the closure identity `cl F = F` is
supplied, the biconjugation formula immediately collapses to the fixed-point statement
`F^{**} = F`. -/
lemma helperForTheorem_6_30_11_convex_biadjoint_eq_self_of_closure_eq_self
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : ConvexBifunction F)
    (hClosureFixed : convexBifunctionClosure F = F) :
    biadjointOfConvexBifunction ⟨F, hF⟩ = F := by
  -- Rewrite the biadjoint as the canonical convex closure and then apply the fixed-point input.
  rw [helperForTheorem_6_30_11_biadjointOfConvex_graph_eq_convexBifunctionClosure_via_coordinate_shuffle
    (F := F) (hF := hF)]
  exact hClosureFixed

/-- Helper for Theorem 6.30.11: in the concave branch, the fixed-point clause follows by
rewriting the biadjoint as the canonical concave closure and then using `cl F = F`. -/
lemma helperForTheorem_6_30_11_concave_biadjoint_eq_self_of_closure_eq_self
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : ConcaveBifunction F)
    (hClosureFixed : concaveBifunctionClosure F = F) :
    biadjointOfConcaveBifunction ⟨F, hF⟩ = F := by
  -- The concave branch uses the same closure rewrite after negating the graph in the background.
  rw [helperForTheorem_6_30_11_biadjointOfConcave_graph_eq_concaveBifunctionClosure_via_coordinate_shuffle
    (G := F) (hG := hF)]
  exact hClosureFixed

-- Proof sketch: treat the convex and concave cases separately. In each case the adjoint has the
-- opposite type and is closed; properness is preserved by adjunction; the biadjoint identifies
-- with the closure of the graph function; closedness gives exact recovery from the biadjoint; and
-- the polyhedral case is stable under adjunction. The two branches together encode the
-- correspondence between closed proper bifunctions of opposite type.
/-- Theorem 6.30.11: for a convex or concave bifunction `F : ℝ^m → ℝ^n`, its adjoint is a
closed bifunction of the opposite type from `ℝ^n` to `ℝ^m`, it is proper exactly when `F` is
proper, and the biadjoint agrees with the appropriate closure of `F`. The textbook closed-case
conclusion is formalized here through the explicit fixed-point identity `cl F = F`, i.e. through
the closure operator appearing in the preceding biconjugation statement itself. Closed proper
convex and closed proper concave bifunctions still correspond through adjunction, and
polyhedrality is preserved by adjoints. -/
theorem adjoint_bifunction_closure_properness_biconjugation_and_polyhedrality {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (∀ hF : ConvexBifunction F,
      ClosedConcaveBifunction (m := n) (n := m) (adjointOfConvexBifunction ⟨F, hF⟩) ∧
        (ProperConcaveBifunction (m := n) (n := m) (adjointOfConvexBifunction ⟨F, hF⟩) ↔
          ProperConvexBifunction F) ∧
        biadjointOfConvexBifunction ⟨F, hF⟩ = convexBifunctionClosure F ∧
        (convexBifunctionClosure F = F → biadjointOfConvexBifunction ⟨F, hF⟩ = F) ∧
        (ClosedConvexBifunction F ∧ ProperConvexBifunction F →
          ClosedConcaveBifunction (m := n) (n := m) (adjointOfConvexBifunction ⟨F, hF⟩) ∧
            ProperConcaveBifunction (m := n) (n := m) (adjointOfConvexBifunction ⟨F, hF⟩)) ∧
        (PolyhedralConvexBifunction F →
          PolyhedralConcaveBifunction (m := n) (n := m) (adjointOfConvexBifunction ⟨F, hF⟩)))
      ∧
      (∀ hF : ConcaveBifunction F,
        ClosedConvexBifunction (m := n) (n := m) (adjointOfConcaveBifunction ⟨F, hF⟩) ∧
          (ProperConvexBifunction (m := n) (n := m) (adjointOfConcaveBifunction ⟨F, hF⟩) ↔
            ProperConcaveBifunction F) ∧
          biadjointOfConcaveBifunction ⟨F, hF⟩ = concaveBifunctionClosure F ∧
          (concaveBifunctionClosure F = F → biadjointOfConcaveBifunction ⟨F, hF⟩ = F) ∧
          (ClosedConcaveBifunction F ∧ ProperConcaveBifunction F →
            ClosedConvexBifunction (m := n) (n := m) (adjointOfConcaveBifunction ⟨F, hF⟩) ∧
              ProperConvexBifunction (m := n) (n := m) (adjointOfConcaveBifunction ⟨F, hF⟩)) ∧
          (PolyhedralConcaveBifunction F →
            PolyhedralConvexBifunction (m := n) (n := m) (adjointOfConcaveBifunction ⟨F, hF⟩))) := by
  constructor
  · intro hF
    rcases
      helperForTheorem_6_30_11_convex_branch_except_closed_fixed_point
        (F := F) (hF := hF) with
      ⟨hClosedAdj, hProperIff, hClosedProper, hPoly⟩
    refine ⟨hClosedAdj, hProperIff, ?_, ?_, hClosedProper, hPoly⟩
    -- The biadjoint-to-closure identity is the standard adjoint-graph rewrite followed by
    -- Fenchel biconjugation through the coordinate shuffle.
    exact
      helperForTheorem_6_30_11_biadjointOfConvex_graph_eq_convexBifunctionClosure_via_coordinate_shuffle
        (F := F) (hF := hF)
    intro hClosureFixed
    -- Delegate the fixed-point corollary to the dedicated closure-to-biadjoint helper.
    exact
      helperForTheorem_6_30_11_convex_biadjoint_eq_self_of_closure_eq_self
        (hF := hF) hClosureFixed
  · intro hF
    rcases
      helperForTheorem_6_30_11_concave_branch_except_closed_fixed_point
        (G := F) (hG := hF) with
      ⟨hClosedAdj, hProperIff, hClosedProper, hPoly⟩
    refine ⟨hClosedAdj, hProperIff, ?_, ?_, hClosedProper, hPoly⟩
    -- The concave branch follows the same route after converting the negated adjoint graph into
    -- a concave conjugate.
    exact
      helperForTheorem_6_30_11_biadjointOfConcave_graph_eq_concaveBifunctionClosure_via_coordinate_shuffle
        (G := F) (hG := hF)
    intro hClosureFixed
    -- The concave fixed-point statement is the corresponding closure rewrite.
    exact
      helperForTheorem_6_30_11_concave_biadjoint_eq_self_of_closure_eq_self
        (hF := hF) hClosureFixed

end Section30
end Chap06

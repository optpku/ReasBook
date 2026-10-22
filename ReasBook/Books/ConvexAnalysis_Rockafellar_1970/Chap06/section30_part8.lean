/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part7

section Chap06
section Section30

-- Proof sketch: the dual program `(P*)` is the concave program associated with `F*`, so its
-- dual is the convex program associated with `(F*)*`, namely the biadjoint of `F`. Apply
-- Theorem 6.30.11 to a closed proper convex bifunction to identify the biadjoint with `F`,
-- and then the two perturbation families agree pointwise.
/-- Theorem 6.30.12: let `F` be a closed proper convex bifunction from `ℝ^m` to `ℝ^n`, and let
`(P)` be the convex program associated with `F`. Let `(P*)` be the dual program associated with
the adjoint bifunction `F*`. Then the program dual to `(P*)` is precisely `(P)`. In Lean, this
is expressed as equality between the perturbation family of the dual of the concave program
associated with `F*` and the perturbation family `u ↦ inf_x F(u, x)` of the original convex
program. -/
theorem dualOfDualProgram_eq_originalProgram {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal //
      ClosedConvexBifunction F ∧ ProperConvexBifunction F}) :
    dualPerturbationFunctionOfConcaveProgram
        (adjointOfConvexBifunctionAsConcave ⟨F.1, F.2.1.1⟩) =
      convexProgramAssociatedWith F.1 := by
  let hConv : ConvexBifunction F.1 := F.2.1.1
  let hClosed : ClosedConvexBifunction F.1 := F.2.1
  let hProper : ProperConvexBifunction F.1 := F.2.2
  -- Closed proper convex bifunctions are fixed by the canonical convex closure.
  have hClosureFixed : convexBifunctionClosure F.1 = F.1 := by
    exact
      helperForTheorem_6_30_11_convexBifunctionClosure_eq_self_of_closed_proper
        (hClosed := hClosed) (hProper := hProper)
  -- Theorem 6.30.11 then collapses the convex biadjoint back to the original bifunction.
  have hBiadjoint :
      biadjointOfConvexBifunction ⟨F.1, hConv⟩ = F.1 := by
    exact
      helperForTheorem_6_30_11_convex_biadjoint_eq_self_of_closure_eq_self
        (hF := hConv) hClosureFixed
  -- Unfold the dual perturbation family of `F*`; it is the convex program of `F**`.
  simpa [dualPerturbationFunctionOfConcaveProgram, biadjointOfConvexBifunction] using
    congrArg convexProgramAssociatedWith hBiadjoint

-- Proof sketch: identify the slice `u* ↦ F*(0, u*)` with the concave conjugate of the primal
-- perturbation function `u ↦ - inf_x F(u, x)` by unfolding the adjoint definition. For the
-- second conjugacy pair, view `x* ↦ sup_{u*} F*(x*, u*)` as the perturbation family of the dual
-- program, apply biconjugation to the corresponding convex or concave objective slice, and use
-- closedness to replace biconjugates by closures.
-- Theorem 6.30.15 is proved below by first establishing the unconstrained conjugacy identities,
-- then reducing the closed branch to a graph-function biconjugation statement at `(0, x)`.
/-- Helper for Theorem 6.30.15: the projection fiber of the graph function over `u` is exactly
the range of the slice `x ↦ F(u, x)`. -/
lemma helperForTheorem_6_30_15_projectionFiber_eq_sliceRange {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (u : Fin m → ℝ) :
    {z : EReal | ∃ w : Fin (m + n) → ℝ,
      projectionLinearMap (Nat.le_add_right m n) w = u ∧ z = bifunctionGraphFunction F w} =
      Set.range (fun x : Fin n → ℝ => F u x) := by
  ext z
  constructor
  · -- Recover the trailing `x`-coordinates from a graph point in the projection fiber.
    intro hz
    rcases hz with ⟨w, hwproj, rfl⟩
    refine ⟨fun j => w (Fin.natAdd m j), ?_⟩
    have hwproj' := (projectionLinearMap_eq_iff (hmn := Nat.le_add_right m n) w u).1 hwproj
    have hw_eq : w = Fin.append u (fun j => w (Fin.natAdd m j)) := by
      funext i
      cases Nat.lt_or_ge i.1 m with
      | inl hi =>
          have hi' : w i = u ⟨i.1, hi⟩ := hwproj' ⟨i.1, hi⟩
          simpa [Fin.append, Fin.addCases, hi] using hi'
      | inr hi =>
          let j : Fin n := ⟨i.1 - m, by omega⟩
          have hj : Fin.natAdd m j = i := by
            ext
            simp [j]
            omega
          have hji : w (Fin.natAdd m j) = w i := congrArg w hj
          simp [Fin.append, Fin.addCases, hi, hj] at hji ⊢
    rw [hw_eq]
    simp [bifunctionGraphFunction]
  · -- Conversely, append the fixed `u`-coordinates to any slice point.
    intro hz
    rcases hz with ⟨x, rfl⟩
    refine ⟨Fin.append u x, ?_, ?_⟩
    · refine (projectionLinearMap_eq_iff (hmn := Nat.le_add_right m n) _ _).2 ?_
      intro i
      change Fin.append u x ⟨↑i, Nat.lt_of_lt_of_le i.2 (Nat.le_add_right m n)⟩ = u i
      simp [Fin.append, Fin.addCases]
    · simp [bifunctionGraphFunction]

/-- Helper for Theorem 6.30.15: the primal perturbation-value function `u ↦ inf_x F(u, x)` is
convex. -/
lemma helperForTheorem_6_30_15_primalValueFunction_is_convex {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) :
    ConvexFunction (convexProgramAssociatedWith F.1) := by
  -- View the primal value as the infimum of the graph function along the first-coordinate fibers.
  have hconvOn :
      ConvexFunctionOn (S := (Set.univ : Set (Fin m → ℝ)))
        (fun u =>
          sInf { z : EReal | ∃ w : Fin (m + n) → ℝ,
            projectionLinearMap (Nat.le_add_right m n) w = u ∧
              z = bifunctionGraphFunction F.1 w }) := by
    simpa using
      (convexFunctionOn_inf_fiber_linearMap
        (A := projectionLinearMap (Nat.le_add_right m n))
        (h := bifunctionGraphFunction F.1) F.2)
  have hfun :
      (fun u : Fin m → ℝ =>
        sInf { z : EReal | ∃ w : Fin (m + n) → ℝ,
          projectionLinearMap (Nat.le_add_right m n) w = u ∧
            z = bifunctionGraphFunction F.1 w }) =
        convexProgramAssociatedWith F.1 := by
    funext u
    -- Replace the projection fiber by the corresponding slice range.
    simp [convexProgramAssociatedWith,
      helperForTheorem_6_30_15_projectionFiber_eq_sliceRange, sInf_range]
  simpa [ConvexFunction, hfun] using hconvOn

/-- Helper for Theorem 6.30.15: the negated primal value function is concave. -/
lemma helperForTheorem_6_30_15_negPrimalValue_is_concave {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) :
    ConcaveFunction (fun u => -(convexProgramAssociatedWith F.1 u)) := by
  -- Concavity is exactly convexity of the negated function.
  simpa [ConcaveFunction] using
    helperForTheorem_6_30_15_primalValueFunction_is_convex (F := F)

/-- Helper for Theorem 6.30.15: the concave conjugate is the negative Fenchel conjugate of the
negated function, without any properness hypothesis. -/
lemma helperForTheorem_6_30_15_concaveConjugate_eq_neg_fenchelConjugate_neg_unrestricted
    {n : ℕ} (g : (Fin n → ℝ) → EReal) (xStar : Fin n → ℝ) :
    concaveConjugate g xStar = -fenchelConjugate n (fun x => -g x) (-xStar) := by
  -- Route correction: this identity is algebraic, so we unfold the two conjugates directly.
  calc
    concaveConjugate g xStar
        = iInf (fun x : Fin n → ℝ => (((x ⬝ᵥ xStar : ℝ) : EReal) + (-g x))) := by
            simp [concaveConjugate, sInf_range]
    _ = -iSup (fun x : Fin n → ℝ => -((((x ⬝ᵥ xStar : ℝ) : EReal) + (-g x)))) := by
          have hneg :=
            congrArg Neg.neg
              (ereal_iSup_neg_eq_neg_iInf
                (g := fun x : Fin n → ℝ => (((x ⬝ᵥ xStar : ℝ) : EReal) + (-g x))))
          simpa using hneg.symm
    _ = -iSup (fun x : Fin n → ℝ => (((x ⬝ᵥ (-xStar) : ℝ) : EReal) - (fun x => -g x) x)) := by
          congr 1
          refine iSup_congr ?_
          intro x
          have hnegAdd :
              -((((x ⬝ᵥ xStar : ℝ) : EReal) + (-g x))) =
                -(((x ⬝ᵥ xStar : ℝ) : EReal)) - (-g x) := by
            exact
              EReal.neg_add
                (x := (((x ⬝ᵥ xStar : ℝ) : EReal)))
                (y := -g x)
                (Or.inl (by simp))
                (Or.inl (by simp))
          calc
            -((((x ⬝ᵥ xStar : ℝ) : EReal) + (-g x)))
                = -(((x ⬝ᵥ xStar : ℝ) : EReal)) - (-g x) := hnegAdd
            _ = (((x ⬝ᵥ (-xStar) : ℝ) : EReal) - (fun x => -g x) x) := by
              simp [sub_eq_add_neg, dotProduct_neg]
    _ = -fenchelConjugate n (fun x => -g x) (-xStar) := by
          simp [fenchelConjugate_eq_iSup]

/-- Helper for Theorem 6.30.15: negating the concave conjugate rewrites it as a Fenchel
conjugate of the negated function precomposed with `x ↦ -x`. -/
lemma helperForTheorem_6_30_15_neg_concaveConjugate_eq_fenchel_precomp_neg
    {n : ℕ} (g : (Fin n → ℝ) → EReal) :
    (fun y => -(concaveConjugate g y)) = fun y => fenchelConjugate n (fun z => -g z) (-y) := by
  funext y
  -- Use the pointwise sign-change identity and cancel the outer negation.
  have hy :=
    helperForTheorem_6_30_15_concaveConjugate_eq_neg_fenchelConjugate_neg_unrestricted
      (g := g) (xStar := y)
  simpa using congrArg Neg.neg hy

/-- Helper for Theorem 6.30.15: adding a finite real constant commutes with indexed infima in
`EReal`. -/
lemma helperForTheorem_6_30_15_real_add_iInf {α : Sort*} (c : ℝ) (f : α → EReal) :
    ((c : EReal) + iInf f) = iInf (fun a => ((c : EReal) + f a)) := by
  apply le_antisymm
  · refine le_iInf ?_
    intro a
    simpa [add_comm] using add_le_add_right (iInf_le f a) ((c : EReal))
  · have htmp : iInf (fun a => ((c : EReal) + f a)) - c ≤ iInf f := by
      refine le_iInf ?_
      intro a
      exact (EReal.sub_le_iff_le_add (h₁ := Or.inl (by simp)) (h₂ := Or.inl (by simp))).2 <|
        by simpa [add_comm] using (iInf_le (fun a => ((c : EReal) + f a)) a)
    have hfinal : iInf (fun a => ((c : EReal) + f a)) ≤ iInf f + c :=
      (EReal.sub_le_iff_le_add (h₁ := Or.inl (by simp)) (h₂ := Or.inl (by simp))).1 htmp
    simpa [add_comm] using hfinal

/-- Helper for Theorem 6.30.15: adding a finite real constant commutes with indexed suprema in
`EReal`. -/
lemma helperForTheorem_6_30_15_real_add_iSup {α : Sort*} (c : ℝ) (f : α → EReal) :
    ((c : EReal) + iSup f) = iSup (fun a => ((c : EReal) + f a)) := by
  apply le_antisymm
  · have htmp : iSup f ≤ iSup (fun a => ((c : EReal) + f a)) - c := by
      refine iSup_le ?_
      intro a
      exact (EReal.le_sub_iff_add_le (hb := Or.inl (by simp)) (ht := Or.inl (by simp))).2 <|
        by simpa [add_comm] using (le_iSup (fun a => ((c : EReal) + f a)) a)
    have hfinal : iSup f + c ≤ iSup (fun a => ((c : EReal) + f a)) :=
      (EReal.le_sub_iff_add_le (hb := Or.inl (by simp)) (ht := Or.inl (by simp))).1 htmp
    simpa [add_comm] using hfinal
  · refine iSup_le ?_
    intro a
    simpa [add_comm] using add_le_add_right (le_iSup f a) ((c : EReal))

/-- Helper for Theorem 6.30.15: the dual objective slice is the concave conjugate of the negated
primal value function. -/
lemma helperForTheorem_6_30_15_dualObjectiveSlice_eq_concaveConjugate_negPrimalValue
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F})
    (uStar : Fin m → ℝ) :
    concaveConjugate (fun u => -(convexProgramAssociatedWith F.1 u)) uStar =
      adjointOfConvexBifunction F 0 uStar := by
  -- Unfold both sides and commute the finite affine term through the inner infimum.
  calc
    concaveConjugate (fun u => -(convexProgramAssociatedWith F.1 u)) uStar
        = iInf (fun u : Fin m → ℝ =>
            (((u ⬝ᵥ uStar : ℝ) : EReal) + convexProgramAssociatedWith F.1 u)) := by
              simp [concaveConjugate, sInf_range]
    _ = iInf (fun u : Fin m → ℝ =>
          iInf (fun x : Fin n → ℝ => (((u ⬝ᵥ uStar : ℝ) : EReal) + F.1 u x))) := by
          congr 1
          funext u
          rw [convexProgramAssociatedWith, sInf_range]
          simpa using
            helperForTheorem_6_30_15_real_add_iInf (c := (u ⬝ᵥ uStar : ℝ))
              (fun x : Fin n → ℝ => F.1 u x)
    _ = iInf (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
          F.1 p.1 p.2 + (((p.1 ⬝ᵥ uStar : ℝ) : EReal))) := by
          simpa [add_comm, iInf_prod']
    _ = adjointOfConvexBifunction F 0 uStar := by
          simp [adjointOfConvexBifunction, sInf_range, sub_eq_add_neg, add_comm]

/-- Helper for Theorem 6.30.15: rewriting the closure of the negated primal value uses the usual
sign-change relation between concave and convex closure. -/
lemma helperForTheorem_6_30_15_concaveClosure_negPrimalValue_eq_negConvexClosure_primalValue
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) :
    concaveClosure (fun u => -(convexProgramAssociatedWith F.1 u)) =
      (fun u => -(convexClosure (convexProgramAssociatedWith F.1) u)) := by
  -- The argument is a direct specialization of `concaveClosure_eq_neg_convexClosure_neg`.
  funext u
  simp [concaveClosure_eq_neg_convexClosure_neg]

/-- Helper for Theorem 6.30.15: the Fenchel conjugate of the negated dual perturbation reduces to
the graph-function biconjugate evaluated at the point `(0, x)`. -/
lemma helperForTheorem_6_30_15_closed_primalSlice_eq_graphBiconjugate_at_zero
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F})
    (x : Fin n → ℝ) :
    fenchelConjugate n (fun xStar => -(dualPerturbationFunctionOfConvexProgram F xStar)) x =
      fenchelConjugate (m + n) (fenchelConjugate (m + n) (bifunctionGraphFunction F.1))
        (Fin.append 0 x) := by
  have hBiconj :
      fenchelConjugate (m + n) (fenchelConjugate (m + n) (bifunctionGraphFunction F.1)) =
        convexClosure (bifunctionGraphFunction F.1) := by
    -- The graph-function biconjugate is the canonical convex closure of the graph.
    simpa [convexClosure] using
      (section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure
        (n := m + n) (f := bifunctionGraphFunction F.1)
        (by simpa [ConvexBifunction] using F.2))
  have hBiadjoint :
      biadjointOfConvexBifunction F = convexBifunctionClosure F.1 := by
    -- Theorem 6.30.11 already identifies the convex biadjoint with the graph closure.
    exact
      helperForTheorem_6_30_11_biadjointOfConvex_graph_eq_convexBifunctionClosure_via_coordinate_shuffle
        (F := F.1) F.2
  have hAdjointSlice :
      iSup (fun p : (Fin n → ℝ) × (Fin m → ℝ) =>
        adjointOfConvexBifunction F p.1 p.2 + (((p.1 ⬝ᵥ x : ℝ) : EReal))) =
        adjointOfConcaveBifunction (adjointOfConvexBifunctionAsConcave F) 0 x := by
    -- Evaluate the adjoint-of-concave formula at the zero first coordinate and the slice point `x`.
    calc
      iSup (fun p : (Fin n → ℝ) × (Fin m → ℝ) =>
          adjointOfConvexBifunction F p.1 p.2 + (((p.1 ⬝ᵥ x : ℝ) : EReal)))
        = iSup (fun p : (Fin n → ℝ) × (Fin m → ℝ) =>
            (((p.1 ⬝ᵥ x : ℝ) : EReal)) + (adjointOfConvexBifunctionAsConcave F).1 p.1 p.2) := by
              refine iSup_congr ?_
              intro p
              simp [adjointOfConvexBifunctionAsConcave, add_comm]
      _ = adjointOfConcaveBifunction (adjointOfConvexBifunctionAsConcave F) 0 x := by
            simp [adjointOfConcaveBifunction, sSup_range, sub_eq_add_neg, add_comm]
  calc
    fenchelConjugate n (fun xStar => -(dualPerturbationFunctionOfConvexProgram F xStar)) x
      = iSup (fun xStar : Fin n → ℝ =>
          (((xStar ⬝ᵥ x : ℝ) : EReal)) + dualPerturbationFunctionOfConvexProgram F xStar) := by
            -- Expand the outer Fenchel conjugate and cancel the double negation in the integrand.
            simp [fenchelConjugate_eq_iSup, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    _ = iSup (fun xStar : Fin n → ℝ =>
          iSup (fun uStar : Fin m → ℝ =>
            (((xStar ⬝ᵥ x : ℝ) : EReal)) + adjointOfConvexBifunction F xStar uStar)) := by
          -- Unfold the dual perturbation and commute the finite affine term through the supremum.
          congr 1
          funext xStar
          rw [dualPerturbationFunctionOfConvexProgram, concaveProgramAssociatedWith, sSup_range]
          simpa using
            helperForTheorem_6_30_15_real_add_iSup (c := (xStar ⬝ᵥ x : ℝ))
              (fun uStar : Fin m → ℝ => adjointOfConvexBifunction F xStar uStar)
    _ = iSup (fun p : (Fin n → ℝ) × (Fin m → ℝ) =>
          adjointOfConvexBifunction F p.1 p.2 + (((p.1 ⬝ᵥ x : ℝ) : EReal))) := by
          -- Package the iterated supremum over `(x*, u*)` into the product-space supremum.
          simp [iSup_prod', add_comm]
    _ = adjointOfConcaveBifunction (adjointOfConvexBifunctionAsConcave F) 0 x := by
          exact hAdjointSlice
    _ = biadjointOfConvexBifunction F 0 x := by
          rfl
    _ = convexBifunctionClosure F.1 0 x := by
          -- Replace the biadjoint by the graph closure from Theorem 6.30.11.
          simpa using congrFun (congrFun hBiadjoint 0) x
    _ = convexClosure (bifunctionGraphFunction F.1) (Fin.append 0 x) := by
          rfl
    _ = fenchelConjugate (m + n) (fenchelConjugate (m + n) (bifunctionGraphFunction F.1))
          (Fin.append 0 x) := by
          -- Finally rewrite the closure value back as the graph-function biconjugate.
          simpa using (congrFun hBiconj (Fin.append 0 x)).symm

/-- Helper for Theorem 6.30.15: if the graph function attains `⊥`, then the Fenchel conjugate of
the negated dual perturbation collapses to the constant `⊥` function. -/
lemma helperForTheorem_6_30_15_bot_attaining_graph_forces_dualSlice_const_bot
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F})
    (hGraphBot : ∃ z : Fin (m + n) → ℝ, bifunctionGraphFunction F.1 z = (⊥ : EReal)) :
    fenchelConjugate n (fun xStar => -(dualPerturbationFunctionOfConvexProgram F xStar)) =
      fun _ => (⊥ : EReal) := by
  funext x
  have hGraphConvex : ConvexFunction (bifunctionGraphFunction F.1) := by
    -- Convexity of the bifunction is exactly convexity of its graph function.
    simpa [ConvexBifunction] using F.2
  have hBiconj :
      fenchelConjugate (m + n) (fenchelConjugate (m + n) (bifunctionGraphFunction F.1)) =
        convexClosure (bifunctionGraphFunction F.1) := by
    -- The graph-function biconjugate is the canonical convex closure of the graph.
    simpa [convexClosure] using
      (section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure
        (n := m + n) (f := bifunctionGraphFunction F.1) hGraphConvex)
  have hClosureBot :
      convexClosure (bifunctionGraphFunction F.1) =
        (fun _ : Fin (m + n) → ℝ => (⊥ : EReal)) := by
    -- A single `⊥` point forces the Chapter 2 convex closure to collapse to constant `⊥`.
    simpa [convexClosure] using
      convexFunctionClosure_eq_bot_of_exists_bot
        (f := bifunctionGraphFunction F.1) hGraphBot
  calc
    fenchelConjugate n (fun xStar => -(dualPerturbationFunctionOfConvexProgram F xStar)) x
      = fenchelConjugate (m + n) (fenchelConjugate (m + n) (bifunctionGraphFunction F.1))
          (Fin.append 0 x) := by
            -- First reduce the dual slice to the graph-function biconjugate at `(0, x)`.
            exact
              helperForTheorem_6_30_15_closed_primalSlice_eq_graphBiconjugate_at_zero
                (F := F) (x := x)
    _ = convexClosure (bifunctionGraphFunction F.1) (Fin.append 0 x) := by
          -- Rewrite the biconjugate as the convex closure of the graph.
          simpa using congrFun hBiconj (Fin.append 0 x)
    _ = (⊥ : EReal) := by
          -- The closure-collapse lemma now forces the slice value to be `⊥`.
          simpa using congrFun hClosureBot (Fin.append 0 x)

/-- Helper for Theorem 6.30.15: once the graph function never attains `⊥`, closedness lets the
graph-function biconjugate collapse back to the original primal slice. -/
lemma helperForTheorem_6_30_15_closed_primalSlice_eq_fenchelConjugate_negDualPerturbation_of_graph_ne_bot
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F})
    (hClosed : ClosedConvexBifunction F.1)
    (hGraphNeBot : ∀ z : Fin (m + n) → ℝ, bifunctionGraphFunction F.1 z ≠ (⊥ : EReal)) :
    fenchelConjugate n (fun xStar => -(dualPerturbationFunctionOfConvexProgram F xStar)) =
      (fun x => F.1 0 x) := by
  funext x
  have hGraphConvex : ConvexFunction (bifunctionGraphFunction F.1) := by
    simpa [ConvexBifunction] using F.2
  have hGraphBiconj :
      fenchelConjugate (m + n) (fenchelConjugate (m + n) (bifunctionGraphFunction F.1)) =
        convexClosure (bifunctionGraphFunction F.1) := by
    -- The graph-function biconjugate is the canonical convex closure of the graph.
    simpa [convexClosure] using
      (section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure
        (n := m + n) (f := bifunctionGraphFunction F.1) hGraphConvex)
  have hClosureFixed :
      convexBifunctionClosure F.1 = F.1 :=
    helperForTheorem_6_30_11_convexBifunctionClosure_eq_self_of_closed
      (F := F.1) hClosed hGraphNeBot
  -- Reduce first to the graph biconjugate, then use the closed non-`⊥` fixed-point theorem.
  calc
    fenchelConjugate n (fun xStar => -(dualPerturbationFunctionOfConvexProgram F xStar)) x
      = fenchelConjugate (m + n) (fenchelConjugate (m + n) (bifunctionGraphFunction F.1))
          (Fin.append 0 x) := by
            exact
              helperForTheorem_6_30_15_closed_primalSlice_eq_graphBiconjugate_at_zero
                (F := F) (x := x)
    _ = convexClosure (bifunctionGraphFunction F.1) (Fin.append 0 x) := by
          simpa using congrFun hGraphBiconj (Fin.append 0 x)
    _ = convexBifunctionClosure F.1 0 x := by
          rfl
    _ = F.1 0 x := by
          simpa using congrFun (congrFun hClosureFixed 0) x

/-- Helper for Theorem 6.30.15: the half-space bifunction used to diagnose the false improper
closed-graph branch in the current formalization. -/
noncomputable def helperForTheorem_6_30_15_halfSpaceCounterexample :
    (Fin 0 → ℝ) → (Fin 1 → ℝ) → EReal :=
  fun _ x => if x 0 ≤ 0 then (⊥ : EReal) else (⊤ : EReal)

/-- Helper for Theorem 6.30.15: the graph function of the half-space counterexample is exactly
the one-variable `⊥/⊤` half-space profile. -/
lemma helperForTheorem_6_30_15_halfSpaceCounterexample_graph_eq
    (z : Fin (0 + 1) → ℝ) :
    bifunctionGraphFunction helperForTheorem_6_30_15_halfSpaceCounterexample z =
      if z 0 ≤ 0 then (⊥ : EReal) else (⊤ : EReal) := by
  -- Unfold the graph map and collapse the vacuous `Fin 0` block.
  simp [helperForTheorem_6_30_15_halfSpaceCounterexample, bifunctionGraphFunction]

/-- Helper for Theorem 6.30.15: the half-space counterexample graph attains `⊥` at the origin. -/
lemma helperForTheorem_6_30_15_halfSpaceCounterexample_graph_attains_bot :
    ∃ z : Fin (0 + 1) → ℝ,
      bifunctionGraphFunction helperForTheorem_6_30_15_halfSpaceCounterexample z = (⊥ : EReal) := by
  refine ⟨0, ?_⟩
  -- The origin belongs to the closed half-space `z 0 ≤ 0`.
  simp [helperForTheorem_6_30_15_halfSpaceCounterexample_graph_eq]

/-- Helper for Theorem 6.30.15: the primal zero-slice of the half-space counterexample is `⊤`
at a positive point. -/
lemma helperForTheorem_6_30_15_halfSpaceCounterexample_zeroSlice_at_positivePoint :
    helperForTheorem_6_30_15_halfSpaceCounterexample 0 (fun _ : Fin 1 => (1 : ℝ)) = (⊤ : EReal) := by
  -- The test point lies outside the closed half-space `x 0 ≤ 0`.
  simp [helperForTheorem_6_30_15_halfSpaceCounterexample]

/-- Helper for Theorem 6.30.15: the primal zero-slice of the half-space counterexample is not
the constant `⊥` function. -/
lemma helperForTheorem_6_30_15_halfSpaceCounterexample_zeroSlice_ne_const_bot :
    (fun x : Fin 1 → ℝ => helperForTheorem_6_30_15_halfSpaceCounterexample 0 x) ≠
      fun _ => (⊥ : EReal) := by
  intro hEq
  -- Evaluate the claimed function equality at a positive point to reach `⊤ = ⊥`.
  have hAtOne :=
    congrArg (fun g : (Fin 1 → ℝ) → EReal => g (fun _ : Fin 1 => (1 : ℝ))) hEq
  have hImpossible : (⊤ : EReal) = (⊥ : EReal) := by
    simpa [helperForTheorem_6_30_15_halfSpaceCounterexample] using hAtOne
  cases hImpossible

/-- Helper for Theorem 6.30.15: assuming the half-space witness is closed convex, the closed
primal-slice identity claimed in the theorem contradicts the explicit non-`⊥` zero-slice value. -/
lemma helperForTheorem_6_30_15_halfSpaceCounterexample_closed_branch_false
    (hClosed : ClosedConvexBifunction helperForTheorem_6_30_15_halfSpaceCounterexample) :
    fenchelConjugate 1
        (fun xStar =>
          -(dualPerturbationFunctionOfConvexProgram
              ⟨helperForTheorem_6_30_15_halfSpaceCounterexample, hClosed.1⟩ xStar)) ≠
      (fun x : Fin 1 → ℝ => helperForTheorem_6_30_15_halfSpaceCounterexample 0 x) := by
  intro hEq
  let FCvx : {F : (Fin 0 → ℝ) → (Fin 1 → ℝ) → EReal // ConvexBifunction F} :=
    ⟨helperForTheorem_6_30_15_halfSpaceCounterexample, hClosed.1⟩
  have hDualBot :
      fenchelConjugate 1
          (fun xStar => -(dualPerturbationFunctionOfConvexProgram FCvx xStar)) =
        (fun _ => (⊥ : EReal)) := by
    -- The counterexample graph attains `⊥`, so the dual slice collapses to constant `⊥`.
    exact
      helperForTheorem_6_30_15_bot_attaining_graph_forces_dualSlice_const_bot
        (F := FCvx) helperForTheorem_6_30_15_halfSpaceCounterexample_graph_attains_bot
  have hPrimalBot :
      (fun x : Fin 1 → ℝ => helperForTheorem_6_30_15_halfSpaceCounterexample 0 x) =
        fun _ => (⊥ : EReal) := by
    -- Transport the claimed closed-branch equality to the bundled convex witness.
    calc
      (fun x : Fin 1 → ℝ => helperForTheorem_6_30_15_halfSpaceCounterexample 0 x)
          = fenchelConjugate 1
              (fun xStar => -(dualPerturbationFunctionOfConvexProgram FCvx xStar)) := by
                simpa [FCvx] using hEq.symm
      _ = fun _ => (⊥ : EReal) := hDualBot
  -- The positive test point witnesses that the primal zero-slice is not constantly `⊥`.
  exact helperForTheorem_6_30_15_halfSpaceCounterexample_zeroSlice_ne_const_bot hPrimalBot

/-- Helper for Theorem 6.30.15: a closed convex bifunction whose graph function never takes
`⊥` satisfies the closed primal-slice identity. -/
lemma helperForTheorem_6_30_15_closed_primalSlice_eq_fenchelConjugate_negDualPerturbation
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F})
    (hClosed : ClosedConvexBifunction F.1)
    (hGraphNeBot : ∀ z : Fin (m + n) → ℝ,
      bifunctionGraphFunction F.1 z ≠ (⊥ : EReal)) :
    fenchelConjugate n (fun xStar => -(dualPerturbationFunctionOfConvexProgram F xStar)) =
      (fun x => F.1 0 x) := by
  exact
    helperForTheorem_6_30_15_closed_primalSlice_eq_fenchelConjugate_negDualPerturbation_of_graph_ne_bot
      (F := F) hClosed hGraphNeBot

/-- Helper for Theorem 6.30.15: once the closed primal-slice identity is known, Fenchel
biconjugation of the negated dual perturbation yields the closure formula. -/
lemma helperForTheorem_6_30_15_convexClosure_negDualPerturbation_eq_negConcaveClosure_dualPerturbation
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F})
    (hPrimalSlice :
      fenchelConjugate n (fun xStar => -(dualPerturbationFunctionOfConvexProgram F xStar)) =
        (fun x => F.1 0 x)) :
    fenchelConjugate n (fun x => F.1 0 x) =
      (fun xStar => -(concaveClosure (dualPerturbationFunctionOfConvexProgram F) xStar)) := by
  -- Apply Fenchel biconjugation to the convex function `x* ↦ - sup F*(x*)`.
  have hconvNegDual :
      ConvexFunction (fun xStar => -(dualPerturbationFunctionOfConvexProgram F xStar)) := by
    simpa [dualPerturbationFunctionOfConvexProgram] using
      (perturbationFunction_concave_and_effectiveDomain_eq_bifunctionDomain
        (G := adjointOfConvexBifunctionAsConcave F)).1
  have hbiconj :
      fenchelConjugate n
        (fenchelConjugate n (fun xStar => -(dualPerturbationFunctionOfConvexProgram F xStar))) =
          convexClosure (fun xStar => -(dualPerturbationFunctionOfConvexProgram F xStar)) := by
    simpa [convexClosure] using
      (section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure
        (n := n) (f := fun xStar => -(dualPerturbationFunctionOfConvexProgram F xStar))
        hconvNegDual)
  calc
    fenchelConjugate n (fun x => F.1 0 x)
      = fenchelConjugate n
          (fenchelConjugate n (fun xStar => -(dualPerturbationFunctionOfConvexProgram F xStar))) := by
            rw [hPrimalSlice]
    _ = convexClosure (fun xStar => -(dualPerturbationFunctionOfConvexProgram F xStar)) := hbiconj
    _ = (fun xStar => -(concaveClosure (dualPerturbationFunctionOfConvexProgram F) xStar)) := by
          funext xStar
          simp [concaveClosure_eq_neg_convexClosure_neg]

/-- Theorem 6.30.15: for a convex bifunction `F : ℝ^m → ℝ^n`, the dual objective slice
`u* ↦ F*(0, u*)` is the concave conjugate of the concave function
`u ↦ - inf_{x ∈ ℝ^n} F(u, x)`, and its biconjugate is the negative of the closure of the convex
function `u ↦ inf_{x ∈ ℝ^n} F(u, x)`. If `F` is closed, then the primal objective slice
`x ↦ F(0, x)` is the Fenchel conjugate of the convex function
`x* ↦ - sup_{u* ∈ ℝ^m} F*(x*, u*)`, and its Fenchel biconjugate is the negative of the closure of
`x* ↦ sup_{u* ∈ ℝ^m} F*(x*, u*)`. -/
theorem dualObjectiveSlice_and_primalObjectiveSlice_are_conjugates {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) :
    concaveConjugate (fun u => -(convexProgramAssociatedWith F.1 u)) =
        (fun uStar => adjointOfConvexBifunction F 0 uStar) ∧
      concaveConjugate (fun uStar => adjointOfConvexBifunction F 0 uStar) =
        (fun u => -(convexClosure (convexProgramAssociatedWith F.1) u)) ∧
      (ClosedConvexBifunction F.1 ∧ ProperConvexBifunction F.1 →
        fenchelConjugate n (fun xStar => -(dualPerturbationFunctionOfConvexProgram F xStar)) =
            (fun x => F.1 0 x) ∧
          fenchelConjugate n (fun x => F.1 0 x) =
            (fun xStar => -(concaveClosure (dualPerturbationFunctionOfConvexProgram F) xStar))) :=
  by
    constructor
    · -- Identify the dual zero-slice pointwise with the concave conjugate of `- inf F`.
      funext uStar
      exact
        helperForTheorem_6_30_15_dualObjectiveSlice_eq_concaveConjugate_negPrimalValue
          (F := F) uStar
    constructor
    · -- Rewrite the second concave conjugate as a Fenchel biconjugate of the primal value.
      let g : (Fin m → ℝ) → EReal := fun u => -(convexProgramAssociatedWith F.1 u)
      have hdualSlice : concaveConjugate g = (fun uStar => adjointOfConvexBifunction F 0 uStar) := by
        funext uStar
        simpa [g] using
          helperForTheorem_6_30_15_dualObjectiveSlice_eq_concaveConjugate_negPrimalValue
            (F := F) uStar
      have hnegDualSlice :
          (fun y => -(concaveConjugate g y)) =
            fun y => fenchelConjugate m (convexProgramAssociatedWith F.1) (-y) := by
        simpa [g] using
          helperForTheorem_6_30_15_neg_concaveConjugate_eq_fenchel_precomp_neg (g := g)
      have hbiconj :
          fenchelConjugate m (fenchelConjugate m (convexProgramAssociatedWith F.1)) =
            convexClosure (convexProgramAssociatedWith F.1) := by
        simpa [convexClosure] using
          (section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure
            (n := m) (f := convexProgramAssociatedWith F.1)
            (helperForTheorem_6_30_15_primalValueFunction_is_convex (F := F)))
      calc
        concaveConjugate (fun uStar => adjointOfConvexBifunction F 0 uStar)
          = concaveConjugate (concaveConjugate g) := by rw [hdualSlice]
        _ = fun u => -fenchelConjugate m (fun y => -(concaveConjugate g y)) (-u) := by
              funext u
              simpa using
                helperForTheorem_6_30_15_concaveConjugate_eq_neg_fenchelConjugate_neg_unrestricted
                  (g := concaveConjugate g) (xStar := u)
        _ = fun u =>
              -fenchelConjugate m (fun y => fenchelConjugate m (convexProgramAssociatedWith F.1) (-y))
                (-u) := by
                have hrewrite :=
                  congrArg (fun k : (Fin m → ℝ) → EReal =>
                    fun u => -fenchelConjugate m k (-u)) hnegDualSlice
                simpa using hrewrite
        _ = fun u => -(fenchelConjugate m (fenchelConjugate m (convexProgramAssociatedWith F.1)) u) := by
              funext u
              congr 1
              simpa using
                congrFun
                  (helperForTheorem_21_4_fenchelConjugate_precomp_neg
                    (n := m) (g := fenchelConjugate m (convexProgramAssociatedWith F.1)))
                  (-u)
        _ = (fun u => -(convexClosure (convexProgramAssociatedWith F.1) u)) := by
              funext u
              simpa using congrFun hbiconj u
    · rintro ⟨hClosed, hProper⟩
      constructor
      · -- The textbook closed branch is formalized here in the canonical closed proper setting.
        have hGraphNeBot : ∀ z : Fin (m + n) → ℝ, bifunctionGraphFunction F.1 z ≠ (⊥ : EReal) := by
          intro z
          exact hProper.2.1.1 z
        exact
          helperForTheorem_6_30_15_closed_primalSlice_eq_fenchelConjugate_negDualPerturbation_of_graph_ne_bot
            (F := F) hClosed hGraphNeBot
      · -- A second Fenchel conjugation yields the corresponding closure formula.
        have hGraphNeBot : ∀ z : Fin (m + n) → ℝ, bifunctionGraphFunction F.1 z ≠ (⊥ : EReal) := by
          intro z
          exact hProper.2.1.1 z
        exact
          helperForTheorem_6_30_15_convexClosure_negDualPerturbation_eq_negConcaveClosure_dualPerturbation
            (F := F)
            (hPrimalSlice :=
              helperForTheorem_6_30_15_closed_primalSlice_eq_fenchelConjugate_negDualPerturbation_of_graph_ne_bot
                (F := F) hClosed hGraphNeBot)

/-- Theorem 6.30.1: if `g : ℝ^n → [-∞, +∞]` is proper concave, then `g` is closed iff its
closure `cl g` satisfies `cl g = g`. Equivalently, `g` is closed exactly when `-g` is a closed
convex function. -/
theorem theorem_6_30_1 {n : ℕ} {g : (Fin n → ℝ) → EReal}
    (hg : ConcaveFunction g) (hproper : ProperConcaveERealFunction g) :
    ClosedConcaveFunction g ↔ concaveClosure g = g := by
  have hNoBot : ∀ x : Fin n → ℝ, -g x ≠ (⊥ : EReal) := hproper.1.1
  constructor
  · intro hClosed
    have hClosureEq : convexFunctionClosure (fun x => -g x) = fun x => -g x :=
      convexFunctionClosure_eq_of_closedConvexFunction hClosed hNoBot
    funext x
    change -(convexFunctionClosure (fun z => -g z) x) = g x
    rw [hClosureEq]
    simp
  · intro hClosureEq
    have hNegClosureEq : convexFunctionClosure (fun x => -g x) = fun x => -g x := by
      funext x
      have hPoint := congrFun hClosureEq x
      change -(convexFunctionClosure (fun z => -g z) x) = g x at hPoint
      have hNegPoint := congrArg Neg.neg hPoint
      simpa using hNegPoint
    have hHullLowerSemicontinuous :
        LowerSemicontinuous (lowerSemicontinuousHull (fun x : Fin n → ℝ => -g x)) := by
      exact
        (Classical.choose_spec
          (exists_lowerSemicontinuousHull (fun x : Fin n → ℝ => -g x))).1
    have hClosureLowerSemicontinuous :
        LowerSemicontinuous (convexFunctionClosure (fun x : Fin n → ℝ => -g x)) := by
      simpa [convexFunctionClosure, hNoBot] using hHullLowerSemicontinuous
    exact ⟨hg, hNegClosureEq ▸ hClosureLowerSemicontinuous⟩

/-- Helper for Theorem 6.30.3: the Chapter 6 convex closure is the earlier `clConv`. -/
lemma helperForTheorem_6_30_3_convexClosure_eq_clConv {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hf : ConvexFunction f) :
    convexClosure f = clConv n f := by
  have hbiconj_closure :
      fenchelConjugate n (fenchelConjugate n f) = convexClosure f := by
    simpa [convexClosure] using
      (section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure
        (n := n) (f := f) hf)
  have hbiconj_clConv :
      fenchelConjugate n (fenchelConjugate n f) = clConv n f := by
    simpa using (fenchelConjugate_biconjugate_eq_clConv (n := n) (f := f))
  exact hbiconj_closure.symm.trans hbiconj_clConv

/-- Helper for Theorem 6.30.3: the concave conjugate of `g` is the negative Fenchel conjugate of
`-g`, without any properness hypothesis. -/
lemma helperForTheorem_6_30_3_concaveConjugate_eq_neg_fenchelConjugate_neg_unrestricted
    {n : ℕ} (g : (Fin n → ℝ) → EReal) (xStar : Fin n → ℝ) :
    concaveConjugate g xStar = -fenchelConjugate n (fun x => -g x) (-xStar) := by
  classical
  -- Route correction: avoid `concaveConjugate_eq_neg_fenchelConjugate_neg` because that theorem
  -- requires properness, while this algebraic identity only needs the definitions.
  calc
    concaveConjugate g xStar
        = iInf (fun x : Fin n → ℝ => (((x ⬝ᵥ xStar : ℝ) : EReal) + (-g x))) := by
            simp [concaveConjugate, sInf_range]
    _ = -iSup (fun x : Fin n → ℝ => -((((x ⬝ᵥ xStar : ℝ) : EReal) + (-g x)))) := by
          have hneg :=
            congrArg Neg.neg
              (ereal_iSup_neg_eq_neg_iInf
                (g := fun x : Fin n → ℝ => (((x ⬝ᵥ xStar : ℝ) : EReal) + (-g x))))
          simpa using hneg.symm
    _ = -iSup (fun x : Fin n → ℝ => (((x ⬝ᵥ (-xStar) : ℝ) : EReal) - (fun x => -g x) x)) := by
          congr 1
          refine iSup_congr ?_
          intro x
          -- Rewrite the negated affine piece so it matches the Fenchel-conjugate integrand.
          have hnegAdd :
              -((((x ⬝ᵥ xStar : ℝ) : EReal) + (-g x))) =
                -(((x ⬝ᵥ xStar : ℝ) : EReal)) - (-g x) := by
            exact
              EReal.neg_add
                (x := (((x ⬝ᵥ xStar : ℝ) : EReal)))
                (y := -g x)
                (Or.inl (by simp))
                (Or.inl (by simp))
          calc
            -((((x ⬝ᵥ xStar : ℝ) : EReal) + (-g x)))
                = -(((x ⬝ᵥ xStar : ℝ) : EReal)) - (-g x) := hnegAdd
            _ = (((x ⬝ᵥ (-xStar) : ℝ) : EReal) - (fun x => -g x) x) := by
              simp [sub_eq_add_neg, dotProduct_neg]
    _ = -fenchelConjugate n (fun x => -g x) (-xStar) := by
          simp [fenchelConjugate_eq_iSup]

/-- Helper for Theorem 6.30.3: negating the concave conjugate rewrites it as a Fenchel conjugate
of the negated function precomposed with `x ↦ -x`. -/
lemma helperForTheorem_6_30_3_neg_concaveConjugate_eq_fenchel_precomp_neg
    {n : ℕ} (g : (Fin n → ℝ) → EReal) :
    (fun y => -(concaveConjugate g y)) = fun y => fenchelConjugate n (fun z => -g z) (-y) := by
  funext y
  -- Use the pointwise sign-change identity and cancel the outer negation.
  have hy :=
    helperForTheorem_6_30_3_concaveConjugate_eq_neg_fenchelConjugate_neg_unrestricted
      (g := g) (xStar := y)
  simpa using congrArg Neg.neg hy

-- Proof sketch: pass from the concave conjugate of `g` to the Fenchel conjugate of `-g`,
-- identify the double conjugate of `-g` with its convex closure, and then translate back using
-- the sign-change formula for concave closure.
/-- Theorem 6.30.3: if `g : ℝ^n → [-∞, +∞]` is concave, then its biconjugate
`g** = concaveConjugate (concaveConjugate g)` equals its closure `cl g = concaveClosure g`,
where `cl g` is the pointwise infimum of the affine majorants of `g`. -/
theorem concaveConjugate_biconjugate_eq_concaveClosure {n : ℕ}
    {g : (Fin n → ℝ) → EReal} (hg : ConcaveFunction g) :
    concaveConjugate (concaveConjugate g) = concaveClosure g := by
  classical
  let _ := hg
  funext x
  -- Rewrite the concave biconjugate as the negative Fenchel biconjugate of `-g`.
  calc
    concaveConjugate (concaveConjugate g) x
        = -fenchelConjugate n (fun y => -(concaveConjugate g y)) (-x) := by
            simpa using
              helperForTheorem_6_30_3_concaveConjugate_eq_neg_fenchelConjugate_neg_unrestricted
                (g := concaveConjugate g) (xStar := x)
    _ = -fenchelConjugate n (fun y => fenchelConjugate n (fun z => -g z) (-y)) (-x) := by
          have hrewrite :
              fenchelConjugate n (fun y => -(concaveConjugate g y)) (-x) =
                fenchelConjugate n (fun y => fenchelConjugate n (fun z => -g z) (-y)) (-x) := by
            exact
              congrArg
                (fun k : (Fin n → ℝ) → EReal => fenchelConjugate n k (-x))
                (helperForTheorem_6_30_3_neg_concaveConjugate_eq_fenchel_precomp_neg (g := g))
          simpa using congrArg Neg.neg hrewrite
    _ = -fenchelConjugate n (fenchelConjugate n (fun z => -g z)) x := by
          congr 1
          simpa using
            congrFun
              (helperForTheorem_21_4_fenchelConjugate_precomp_neg
                (n := n) (g := fenchelConjugate n (fun z => -g z)))
              (-x)
    _ = -(clConv n (fun z => -g z) x) := by
          congr 1
          simpa using
            congrFun
              (fenchelConjugate_biconjugate_eq_clConv (n := n) (f := fun z => -g z))
              x
    _ = -(convexClosure (fun z => -g z) x) := by
          congr 1
          simpa using
            (congrFun
              (helperForTheorem_6_30_3_convexClosure_eq_clConv (f := fun z => -g z) hg)
              x).symm
    _ = concaveClosure g x := by
          simpa using (congrFun (concaveClosure_eq_neg_convexClosure_neg (g := g)).symm x)

/-- An `EReal`-valued function is bounded above when it admits a real upper bound. -/
def HasRealUpperBound {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  ∃ M : ℝ, ∀ x : Fin n → ℝ, f x ≤ (M : EReal)

/-- Helper for Corollary 6.30.1: the dual program value is the convex closure of the primal
perturbation-value function evaluated at the origin. -/
lemma helperForCorollary_6_30_1_dualProgram_eq_convexClosure_primalValue_at_zero
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F}) :
    dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ =
      convexClosure (convexProgramAssociatedWith F.1) 0 := by
  let FCvx : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F} := ⟨F.1, F.2.1⟩
  have hconj :=
    (dualObjectiveSlice_and_primalObjectiveSlice_are_conjugates (F := FCvx)).2.1
  have hzero := congrFun hconj (0 : Fin m → ℝ)
  dsimp [FCvx] at hzero ⊢
  have hsup :
      dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ =
        -⨅ x, -adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 x := by
    -- Rewrite the dual program at `0` as the negative infimum of the negated dual slice.
    simpa [dualProgramOfConvexProgram, dualPerturbationFunctionOfConvexProgram,
      concaveProgramAssociatedWith, sSup_range] using
      (ereal_iSup_neg_eq_neg_iInf
        (g := fun x : Fin m → ℝ => -adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 x))
  -- Negating the concave-conjugate identity at `0` removes the outer sign.
  calc
    dualProgramOfConvexProgram ⟨F.1, F.2.1⟩
        = -⨅ x, -adjointOfConvexBifunction ⟨F.1, F.2.1⟩ 0 x := hsup
    _ = convexClosure (convexProgramAssociatedWith F.1) 0 := by
          simpa [concaveConjugate, sInf_range] using congrArg Neg.neg hzero

/-- Helper for Corollary 6.30.1: a primal slice takes the value `⊥` exactly when it has no real
lower bound. -/
lemma helperForCorollary_6_30_1_primalSlice_eq_bot_iff_not_HasRealLowerBound
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (u : Fin m → ℝ) :
    convexProgramAssociatedWith F.1 u = (⊥ : EReal) ↔
      ¬ HasRealLowerBound (F.1 u) := by
  constructor
  · intro hBot hLower
    -- Section 27 identifies lower boundedness with the slice infimum avoiding `⊥`.
    exact
      (helperForTheorem_6_27_1_hasRealLowerBound_iff_functionInfimum_ne_bot (F.1 u)).1
        hLower
        (by simpa [convexProgramAssociatedWith, functionInfimumEReal, sInf_range] using hBot)
  · intro hNoLower
    by_contra hNeBot
    -- If the slice infimum were not `⊥`, the same Section 27 criterion would produce a bound.
    exact
      hNoLower
        ((helperForTheorem_6_27_1_hasRealLowerBound_iff_functionInfimum_ne_bot (F.1 u)).2
          (by simpa [convexProgramAssociatedWith, functionInfimumEReal, sInf_range] using hNeBot))

/-- Helper for Corollary 6.30.1: a real upper bound is the same as a real lower bound for the
negated function. -/
lemma helperForCorollary_6_30_1_hasRealUpperBound_iff_neg_hasRealLowerBound
    {n : ℕ} (f : (Fin n → ℝ) → EReal) :
    HasRealUpperBound f ↔ HasRealLowerBound (fun x => -f x) := by
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨-M, ?_⟩
    intro x
    -- Negating the upper-bound inequality gives the required lower bound on `-f`.
    have hx : f x ≤ (M : EReal) := hM x
    simpa using (EReal.neg_le_neg_iff.2 hx)
  · rintro ⟨M, hM⟩
    refine ⟨-M, ?_⟩
    intro x
    -- Reversing the same sign change recovers the original upper bound.
    have hx : -(-((M : ℝ) : EReal)) ≤ -f x := by
      simpa using hM x
    simpa using (EReal.neg_le_neg_iff.1 hx)

/-- Helper for Corollary 6.30.1: the supremum of a slice is `⊤` exactly when the slice has no
real upper bound. -/
lemma helperForCorollary_6_30_1_sSup_range_eq_top_iff_not_HasRealUpperBound
    {n : ℕ} (f : (Fin n → ℝ) → EReal) :
    sSup (Set.range f) = (⊤ : EReal) ↔ ¬ HasRealUpperBound f := by
  constructor
  · intro hTop hUpper
    rcases hUpper with ⟨M, hM⟩
    have hsSup_le : sSup (Set.range f) ≤ (M : EReal) := by
      -- Any real upper bound on the slice dominates its supremum.
      rw [sSup_le_iff]
      intro y hy
      rcases hy with ⟨x, rfl⟩
      exact hM x
    have : (⊤ : EReal) ≤ (M : EReal) := by
      simpa [hTop] using hsSup_le
    simp at this
  · intro hNoUpper
    rw [EReal.eq_top_iff_forall_lt]
    intro M
    by_contra hM
    have hsSup_le : sSup (Set.range f) ≤ (M : EReal) := le_of_not_gt hM
    have hUpper : HasRealUpperBound f := by
      refine ⟨M, ?_⟩
      intro x
      -- Each slice value lies below the supremum, hence below the chosen real bound.
      exact
        le_trans (le_sSup (show f x ∈ Set.range f by exact ⟨x, rfl⟩)) hsSup_le
    exact hNoUpper hUpper

/-- Helper for Corollary 6.30.1: a dual slice takes the value `⊤` exactly when it has no real
upper bound. -/
lemma helperForCorollary_6_30_1_dualSlice_eq_top_iff_not_HasRealUpperBound
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (xStar : Fin n → ℝ) :
    dualPerturbationFunctionOfConvexProgram ⟨F.1, F.2.1⟩ xStar = (⊤ : EReal) ↔
      ¬ HasRealUpperBound (adjointOfConvexBifunction ⟨F.1, F.2.1⟩ xStar) := by
  -- Unfold the dual perturbation value into the supremum of the adjoint slice.
  simpa [dualPerturbationFunctionOfConvexProgram, concaveProgramAssociatedWith] using
    helperForCorollary_6_30_1_sSup_range_eq_top_iff_not_HasRealUpperBound
      (f := adjointOfConvexBifunction ⟨F.1, F.2.1⟩ xStar)

/-- Helper for Corollary 6.30.1: a single `⊥` value on a slice forces the whole slice infimum to
be `⊥`. -/
lemma helperForCorollary_6_30_1_primalSlice_eq_bot_of_sliceValue_eq_bot
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (u : Fin m → ℝ) (x : Fin n → ℝ)
    (hBot : F.1 u x = (⊥ : EReal)) :
    convexProgramAssociatedWith F.1 u = (⊥ : EReal) := by
  apply le_antisymm
  · -- The infimum is bounded above by any point of the slice.
    exact sInf_le ⟨x, hBot⟩
  · -- The reverse inequality is automatic because `⊥` is the least element.
    exact (bot_le : (⊥ : EReal) ≤ convexProgramAssociatedWith F.1 u)

/-- Helper for Corollary 6.30.1: if the primal perturbation function has no `⊥` slice and the
bifunction is closed proper, then the dual program cannot be `⊥`. -/
lemma helperForCorollary_6_30_1_dualProgram_ne_bot_of_closed_proper_no_primalSlice_bot
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hProper : ProperConvexBifunction F.1)
    (hNoBot : ∀ u : Fin m → ℝ, convexProgramAssociatedWith F.1 u ≠ (⊥ : EReal)) :
    dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ ≠ (⊥ : EReal) := by
  let p : (Fin m → ℝ) → EReal := convexProgramAssociatedWith F.1
  have hpConv : ConvexFunction p := by
    -- The primal perturbation function is convex by Theorem 6.30.15's preparatory lemmas.
    simpa [p] using
      helperForTheorem_6_30_15_primalValueFunction_is_convex (F := ⟨F.1, F.2.1⟩)
  rcases hProper.2.1.2 with ⟨z, hzTop⟩
  let u : Fin m → ℝ := fun i => z (Fin.castAdd n i)
  let x : Fin n → ℝ := fun j => z (Fin.natAdd m j)
  have hpNotTop : p u ≠ (⊤ : EReal) := by
    intro hpTop
    have hle : p u ≤ F.1 u x := by
      -- The slice infimum is below the chosen graph value.
      exact sInf_le ⟨x, rfl⟩
    rw [hpTop] at hle
    have hFxTop : F.1 u x = (⊤ : EReal) := top_unique hle
    exact hzTop (by simpa [bifunctionGraphFunction, u, x] using hFxTop)
  have hpProperOn : ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) p := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [ConvexFunction, p] using hpConv
    · -- A finite slice value gives a nonempty effective domain for the perturbation function.
      rw [nonempty_epigraph_iff_nonempty_effectiveDomain]
      refine ⟨u, ?_⟩
      rw [effectiveDomain_eq]
      constructor
      · simp
      · exact lt_top_iff_ne_top.mpr hpNotTop
    · intro u _
      exact hNoBot u
  have hclosureProper :=
    (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri hpProperOn).1.2
  have hclNotBot : convexClosure p 0 ≠ (⊥ : EReal) := by
    -- Properness of the convex closure rules out the value `⊥` at the origin.
    simpa [convexClosure] using hclosureProper.2.2 0 (by simp)
  have hdual :=
    helperForCorollary_6_30_1_dualProgram_eq_convexClosure_primalValue_at_zero (F := F)
  rw [hdual]
  exact hclNotBot

/-- Helper for Corollary 6.30.1: if the primal perturbation function has no `⊥` slice and the
closed bifunction is not proper, then the dual program still cannot be `⊥`. -/
lemma helperForCorollary_6_30_1_dualProgram_ne_bot_of_closed_not_proper_no_primalSlice_bot
    {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F})
    (hNotProper : ¬ ProperConvexBifunction F.1)
    (hNoSliceBot : ∀ u : Fin m → ℝ, convexProgramAssociatedWith F.1 u ≠ (⊥ : EReal)) :
    dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ ≠ (⊥ : EReal) := by
  have hGraphNeBot : ∀ z : Fin (m + n) → ℝ, bifunctionGraphFunction F.1 z ≠ (⊥ : EReal) := by
    intro z hz
    let u : Fin m → ℝ := fun i => z (Fin.castAdd n i)
    let x : Fin n → ℝ := fun j => z (Fin.natAdd m j)
    have hslicebot : convexProgramAssociatedWith F.1 u = (⊥ : EReal) := by
      -- A graph-level `⊥` witness immediately forces the corresponding slice infimum to be `⊥`.
      apply le_antisymm
      · exact sInf_le ⟨x, by simpa [u, x, bifunctionGraphFunction] using hz⟩
      · exact (bot_le : (⊥ : EReal) ≤ convexProgramAssociatedWith F.1 u)
    exact hNoSliceBot u hslicebot
  by_cases hTop : F.1 = fun _ _ => (⊤ : EReal)
  · have hdualTop : dualProgramOfConvexProgram ⟨F.1, F.2.1⟩ = (⊤ : EReal) := by
      -- In the constant `⊤` branch, every adjoint value is `⊤`, so the dual program is `⊤`.
      simp [hTop, dualProgramOfConvexProgram, dualPerturbationFunctionOfConvexProgram,
        concaveProgramAssociatedWith, adjointOfConvexBifunction]
    rw [hdualTop]
    simp
  · have hClosureFixed : convexBifunctionClosure F.1 = F.1 := by
      -- Without graph-level `⊥`, the closed bifunction is fixed by its convex closure.
      exact
        helperForTheorem_6_30_11_convexBifunctionClosure_eq_self_of_closed
          (F := F.1) F.2 hGraphNeBot
    have hNotBot : F.1 ≠ fun _ _ => (⊥ : EReal) := by
      intro hBot
      have : convexProgramAssociatedWith F.1 0 = (⊥ : EReal) := by
        simp [hBot, convexProgramAssociatedWith]
      exact hNoSliceBot 0 this
    -- The remaining nonconstant closed improper branch contradicts the fixed-point identity.
    exfalso
    exact
      (helperForTheorem_6_30_11_convexBifunctionClosure_ne_self_of_closed_not_proper_nonconstant
        (F := F.1) F.2 hNotProper hTop hNotBot)
        hClosureFixed


end Section30
end Chap06

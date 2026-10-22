/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part8

section Chap07
section Section33

attribute [local instance] classicalSetDecidablePred
attribute [local instance] Classical.propDecidable

/-! A convex bifunction in the graph-function sense is one whose associated function on
`ℝ^(m + n)` is convex. -/
/-- The graph-function notion of convexity for a bifunction. -/
def IsGraphConvexBifunction {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) (graphFunctionOfBifunction F)

-- Proof sketch: uncurry a bifunction `F` to its graph function on `ℝ^(m+n)` and curry a
-- function `f` on `ℝ^(m+n)` back along the splitting `ℝ^(m+n) ≃ ℝ^m × ℝ^n`. These
-- operations are inverse to each other, and the graph-function notion of convexity for `F`
-- is exactly convexity of the uncurried function on the whole space.
/-- Lemma33.0.21 (Graph function correspondence): convex bifunctions
`F : ℝ^m → (ℝ^n → EReal)` correspond one-to-one with their graph functions
`f (u, x) = (F u) x`, and these graph functions are precisely the convex functions on
`ℝ^(m + n)`. -/
theorem graphConvexBifunction_graphFunction_correspondence
    {m n : ℕ} :
    (∀ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      IsGraphConvexBifunction F ↔
        IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) (graphFunctionOfBifunction F)) ∧
      (∀ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
        IsGraphConvexBifunction F →
          bifunctionOfGraphFunction (graphFunctionOfBifunction F) = F) ∧
      ∀ f : (Fin (m + n) → ℝ) → EReal,
        IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) f →
          graphFunctionOfBifunction (bifunctionOfGraphFunction f) = f := by
  constructor
  · intro F
    -- The graph-convexity predicate was defined to be convexity of the associated graph
    -- function on the full product space.
    rfl
  constructor
  · intro F _hF
    -- Currying back the uncurried graph function is the formal inverse identity proved
    -- earlier in the section.
    exact helperForLemma33_0_14_bifunctionOfGraphFunction_graphFunctionOfBifunction_eq F
  · intro f _hf
    -- Uncurrying after currying likewise recovers the original graph function.
    exact helperForLemma33_0_14_graphFunctionOfBifunction_bifunctionOfGraphFunction_eq f

/-- The adjoint of a convex bifunction, viewed as the partial conjugate in the `x`-variable. -/
noncomputable abbrev convexBifunctionAdjoint {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (xStar : Fin n → ℝ) : (Fin m → ℝ) → EReal :=
  fun u => convexBifunctionPairing F u xStar

/-- The adjoint of a concave bifunction, viewed as the partial conjugate in the `x`-variable
through the concave pairing convention. -/
noncomputable abbrev concaveBifunctionAdjoint {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (xStar : Fin n → ℝ) : (Fin m → ℝ) → EReal :=
  fun u => concaveBifunctionPairing F u xStar

/-- Helper for Lemma33.0.22: graph-function convexity of `F` implies Rockafellar convexity.

This just curries/uncurries along the `Fin.append` splitting and reuses the already-proved
lemmas that extract sectionwise convexity and concavity of the convex pairing from a convex
graph function. -/
lemma helperForLemma33_0_22_graphConvex_gives_rockafellarConvex
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_convex : IsGraphConvexBifunction F) :
    IsRockafellarConvexBifunction F := by
  classical
  -- Unfold the graph-convexity hypothesis to the underlying convexity statement on `ℝ^(m+n)`.
  have hf :
      IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) (graphFunctionOfBifunction F) := by
    simpa [IsGraphConvexBifunction] using hF_convex
  -- Apply the general extraction lemmas to the graph function, then transport back to `F`
  -- via the curry-uncurry identity.
  have hSection :
      IsRockafellarSectionwiseConvexBifunction
        (bifunctionOfGraphFunction (graphFunctionOfBifunction F)) :=
    helperForLemma33_0_14_sectionwiseConvex_of_graphConvex (f := graphFunctionOfBifunction F) hf
  have hPair :
      HasConcaveParameterConvexPairing
        (bifunctionOfGraphFunction (graphFunctionOfBifunction F)) :=
    helperForLemma33_0_14_concaveParameterPairing_of_graphConvex (f := graphFunctionOfBifunction F) hf
  have hEq :
      bifunctionOfGraphFunction (graphFunctionOfBifunction F) = F :=
    helperForLemma33_0_14_bifunctionOfGraphFunction_graphFunctionOfBifunction_eq F
  -- Rewrite the extracted properties along `hEq`.
  have hSectionF : IsRockafellarSectionwiseConvexBifunction F := by
    simpa [hEq] using hSection
  have hPairF : HasConcaveParameterConvexPairing F := by
    simpa [hEq] using hPair
  exact ⟨hSectionF, hPairF⟩

/-- Helper for Lemma33.0.22: the adjoint kernel `(u, x^*) ↦ (F^* x^*)(u)` is concave-convex.

This is the "easy" part of Lemma33.0.22: once `F` is Rockafellar-convex and avoids `⊥`,
Theorem33.1 (`convexBifunction_pairing_correspondence`) directly yields concave-convexity of
the convex pairing, and the adjoint is definitionally that pairing. -/
lemma helperForLemma33_0_22_adjointKernel_isConcaveConvex
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_convex : IsGraphConvexBifunction F)
    (hF_noBot : HasNoBotValuesBifunction F) :
    IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
      (fun u xStar => convexBifunctionAdjoint F xStar u) := by
  classical
  -- Step 1: upgrade graph convexity to Rockafellar convexity.
  have hRock : IsRockafellarConvexBifunction F :=
    helperForLemma33_0_22_graphConvex_gives_rockafellarConvex (F := F) hF_convex
  -- Step 2: apply Theorem33.1 to get concave-convexity of the pairing kernel.
  have hPairing :=
    (convexBifunction_pairing_correspondence (m := m) (n := n)).1 F hRock hF_noBot
  have hConcConv : IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
      (convexBifunctionPairing F) := hPairing.1
  -- Step 3: the adjoint is definitionally `convexBifunctionPairing`, so we just rewrite.
  simpa [convexBifunctionAdjoint] using hConcConv

/-- Helper for Lemma33.0.22: the adjoint kernel is convex-closed in the dual variable.

This is the second-variable closedness already supplied by Theorem33.1 for the convex
pairing, rewritten through the adjoint notation. -/
lemma helperForLemma33_0_22_adjointKernel_isConvexClosedInSecond
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_convex : IsGraphConvexBifunction F)
    (hF_noBot : HasNoBotValuesBifunction F) :
    IsConvexClosedInSecond (fun u xStar => convexBifunctionAdjoint F xStar u) := by
  classical
  -- Step 1: turn graph convexity into the Rockafellar convexity hypothesis used by
  -- Theorem33.1.
  have hRock : IsRockafellarConvexBifunction F :=
    helperForLemma33_0_22_graphConvex_gives_rockafellarConvex (F := F) hF_convex
  -- Step 2: the forward pairing correspondence gives second-variable convex closedness.
  have hPairing :=
    (convexBifunction_pairing_correspondence (m := m) (n := n)).1 F hRock hF_noBot
  have hClosed : IsConvexClosedInSecond (convexBifunctionPairing F) := hPairing.2.1
  -- Step 3: rewrite the pairing kernel as the adjoint kernel.
  simpa [convexBifunctionAdjoint] using hClosed

/-- Helper for Lemma33.0.22: every adjoint section `u ↦ (F^* x^*)(u)` is concave.

This is the first-variable half of the already-established concave-convexity of the adjoint
kernel. -/
lemma helperForLemma33_0_22_adjointSection_isConcave
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_convex : IsGraphConvexBifunction F)
    (hF_noBot : HasNoBotValuesBifunction F)
    (xStar : Fin n → ℝ) :
    IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) (convexBifunctionAdjoint F xStar) := by
  -- Step 1: obtain the joint concave-convex statement for the whole adjoint kernel.
  have hKernelConcConv :
      IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
        (fun u xStar => convexBifunctionAdjoint F xStar u) :=
    helperForLemma33_0_22_adjointKernel_isConcaveConvex
      (F := F) (hF_convex := hF_convex) (hF_noBot := hF_noBot)
  -- Step 2: freeze the dual variable to extract the parameter-side concavity.
  have hxStar : xStar ∈ (Set.univ : Set (Fin n → ℝ)) := by
    simp
  simpa [convexBifunctionAdjoint] using hKernelConcConv.1 xStar hxStar

/-- Helper for Lemma33.0.22: closedness of the graph function forces closedness of every
primal section `F u`.

This is the dependency-closed sectionwise closedness fact needed by the valid Section 33
route: once the graph function is already fixed by the raw convex-closure operator, freezing
the parameter `u` and composing with `x ↦ Fin.append u x` preserves lower semicontinuity, so
the resulting section is fixed by its own one-variable convex closure. -/
lemma helperForLemma33_0_22_section_isFunctionConvexClosed
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_closed : IsFunctionConvexClosed (graphFunctionOfBifunction F)) :
    ∀ u : Fin m → ℝ, IsFunctionConvexClosed (F u) := by
  intro u
  let freezeSection : (Fin n → ℝ) → (Fin (m + n) → ℝ) := fun x => Fin.append u x
  -- Step 1: graph-function closedness supplies lower semicontinuity of the full graph
  -- function via the raw Section 33 closure operator.
  have hGraphLsc : LowerSemicontinuous (graphFunctionOfBifunction F) := by
    have hClosureLsc :
        LowerSemicontinuous (functionConvexClosure (graphFunctionOfBifunction F)) :=
      helperForLemma33_0_5_functionConvexClosure_lowerSemicontinuous
        (f := graphFunctionOfBifunction F)
    exact hF_closed ▸ hClosureLsc
  -- Step 2: freezing `u` amounts to composing with the continuous map `x ↦ Fin.append u x`.
  have hFreezeSectionCont : Continuous freezeSection := by
    simpa [freezeSection] using
      (Fin.continuous_append m n).comp (continuous_const.prodMk continuous_id)
  have hSectionLsc : LowerSemicontinuous (F u) := by
    have hComposed :
        LowerSemicontinuous
          (fun x : Fin n → ℝ => graphFunctionOfBifunction F (freezeSection x)) :=
      hGraphLsc.comp_continuous hFreezeSectionCont
    simpa [freezeSection, graphFunctionOfBifunction] using hComposed
  -- Step 3: a lower semicontinuous section is fixed by the one-variable convex closure.
  exact
    helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous
      hSectionLsc

/-- Helper for Lemma33.0.22: every fixed-dual pairing section avoids `⊥` whenever each primal
section has a point that avoids `⊤`.

This is the one-function admissibility witness reused from Theorem33.1, now specialized to the
pairing section `u ↦ ⟪F u, x^*⟫`. -/
lemma helperForLemma33_0_22_pairingSection_hasNoBot
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_notTop : ∀ u : Fin m → ℝ, ∃ x : Fin n → ℝ, F u x ≠ ⊤) :
    ∀ xStar : Fin n → ℝ, ∀ u : Fin m → ℝ,
      convexBifunctionPairing F u xStar ≠ (⊥ : EReal) := by
  intro xStar u
  rcases hF_notTop u with ⟨x₀, hx₀⟩
  -- Step 1: freeze the primal parameter `u` and choose a witness where the section is not `⊤`.
  -- Step 2: apply the one-variable convex-conjugate non-`⊥` lemma to the frozen section.
  simpa [convexBifunctionPairing, bifunctionPairingNotation, convexConjugate] using
    helperForTheorem33_1_convexConjugate_ne_bot_of_point
      (f := F u) (x₀ := x₀) hx₀ xStar

/-- Helper for Lemma33.0.22: once a fixed-dual pairing section is known to be a Chapter 6
concave function, its biconjugate is exactly its Chapter 6 concave closure.

This isolates the part of the Section 33 route that really comes from Chapter 6: the only
extra missing ingredient is a dependency-closed way to package the pairing section into the
`ConcaveFunction` predicate required by `concaveConjugate_biconjugate_eq_concaveClosure`. -/
lemma helperForLemma33_0_22_pairingSection_biconjugate_eq_concaveClosure_of_concaveFunction
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {xStar : Fin n → ℝ}
    (hConc :
      ConcaveFunction (fun u' : Fin m → ℝ => convexBifunctionPairing F u' xStar)) :
    ∀ u : Fin m → ℝ,
      concaveConjugate
          (concaveConjugate (fun u' : Fin m → ℝ => convexBifunctionPairing F u' xStar)) u =
        concaveClosure (fun u' : Fin m → ℝ => convexBifunctionPairing F u' xStar) u := by
  intro u
  -- Step 1: apply the Chapter 6 biconjugation theorem to the fixed-dual pairing section.
  simpa using
    congrFun
      (concaveConjugate_biconjugate_eq_concaveClosure
        (g := fun u' : Fin m → ℝ => convexBifunctionPairing F u' xStar) hConc)
      u

/-- Helper for Lemma33.0.22: first-variable closedness of the adjoint kernel specializes to
closedness of each fixed-dual adjoint section.

This isolates the exact remaining issue in Lemma33.0.22: once the kernel
`(u, x^*) ↦ (F^* x^*)(u)` is known to equal its first-variable concave closure, every frozen
section `u ↦ (F^* x^*)(u)` is automatically fixed by the one-variable concave closure. -/
lemma helperForLemma33_0_22_adjointSection_isFunctionConcaveClosed_of_kernelClosedInFirst
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (xStar : Fin n → ℝ)
    (hKernelClosed :
      IsConcaveClosedInFirst (fun u xStar => convexBifunctionAdjoint F xStar u)) :
    IsFunctionConcaveClosed (convexBifunctionAdjoint F xStar) := by
  -- Step 1: unfold one-variable concave-closedness so the goal becomes a fixed-point
  -- identity for the frozen section.
  unfold IsFunctionConcaveClosed
  funext u
  -- Step 2: evaluate the kernel-level first-variable fixed-point identity at `(u, xStar)`.
  have hPoint :
      (fun u xStar => convexBifunctionAdjoint F xStar u) u xStar =
        concaveClosureInFirst (fun u xStar => convexBifunctionAdjoint F xStar u) u xStar :=
    congrArg (fun K => K u xStar) hKernelClosed
  -- Step 3: for a fixed dual parameter, the first-variable kernel closure is exactly the
  -- one-variable concave closure of the resulting section.
  simpa [concaveClosureInFirst, functionConcaveClosure, convexBifunctionAdjoint] using hPoint

/-- Helper for Lemma33.0.22: freezing the second variable of a concave-convex kernel that is
concave-closed in the first variable yields a concave, concave-closed section. -/
lemma helperForLemma33_0_22_frozenSecondVariable_isConcaveAndFunctionConcaveClosed
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hKernelConcConv :
      IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K)
    (hKernelClosed : IsConcaveClosedInFirst K)
    (v : Fin n → ℝ) :
    IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) (fun u => K u v) ∧
      IsFunctionConcaveClosed (fun u => K u v) := by
  -- Step 1: freeze the second variable in the kernel-level concave-convex statement.
  have hv : v ∈ (Set.univ : Set (Fin n → ℝ)) := by
    simp
  have hConc :
      IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) (fun u => K u v) := by
    simpa using hKernelConcConv.1 v hv
  -- Step 2: evaluate the first-variable fixed-point identity at the frozen second variable.
  have hClosed : IsFunctionConcaveClosed (fun u => K u v) := by
    unfold IsFunctionConcaveClosed
    funext u
    have hPoint : K u v = concaveClosureInFirst K u v :=
      congrArg (fun G => G u v) hKernelClosed
    simpa [concaveClosureInFirst, functionConcaveClosure] using hPoint
  exact ⟨hConc, hClosed⟩

/-- Helper for Lemma33.0.22: for each fixed `u`, the adjoint image
`x^* ↦ (F^* x^*)(u)` is convex-closed.

This records the dual-variable closedness that Theorem33.1 provides for the pairing kernel,
specialized to a single parameter value. -/
lemma helperForLemma33_0_22_adjointImage_isFunctionConvexClosed
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_convex : IsGraphConvexBifunction F)
    (hF_noBot : HasNoBotValuesBifunction F)
    (u : Fin m → ℝ) :
    IsFunctionConvexClosed (fun xStar => convexBifunctionAdjoint F xStar u) := by
  -- Step 1: first package the kernel-level second-variable closedness.
  have hKernelClosed :
      IsConvexClosedInSecond (fun u xStar => convexBifunctionAdjoint F xStar u) :=
    helperForLemma33_0_22_adjointKernel_isConvexClosedInSecond
      (F := F) (hF_convex := hF_convex) (hF_noBot := hF_noBot)
  -- Step 2: specialize the kernel fixed-point identity at the chosen parameter `u`.
  unfold IsFunctionConvexClosed
  funext xStar
  have hPoint :
      convexClosureInSecond (fun u xStar => convexBifunctionAdjoint F xStar u) u xStar =
        (fun u xStar => convexBifunctionAdjoint F xStar u) u xStar :=
    helperForLemma33_0_18_convexClosureInSecond_eq_self
      (K := fun u xStar => convexBifunctionAdjoint F xStar u) hKernelClosed u xStar
  -- Step 3: identify the one-variable closure with the second-variable kernel closure.
  simpa [convexClosureInSecond, functionConvexClosure] using hPoint.symm

/-- Helper for Lemma33.0.22: the adjoint kernel never takes the value `⊥` when every primal
section `F u` contains at least one point different from `⊤`.

This is the same admissibility witness used in Theorem33.1 for a single convex conjugate:
freezing `u`, any point `x₀` with `F u x₀ ≠ ⊤` contributes a genuine affine term to the
supremum defining `(F^* x^*)(u)`, so that supremum cannot collapse to `⊥`. -/
lemma helperForLemma33_0_22_adjointKernel_hasNoBotValues
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_notTop : ∀ u : Fin m → ℝ, ∃ x : Fin n → ℝ, F u x ≠ ⊤) :
    HasNoBotValuesBifunction (fun u xStar => convexBifunctionAdjoint F xStar u) := by
  intro u xStar
  -- Step 1: choose a point in the frozen primal section where the value is not `⊤`.
  rcases hF_notTop u with ⟨x₀, hx₀⟩
  -- Step 2: apply the one-function non-`⊥` lemma for convex conjugates.
  simpa [convexBifunctionAdjoint, convexBifunctionPairing, bifunctionPairingNotation] using
    helperForTheorem33_1_convexConjugate_ne_bot_of_point
      (f := F u) (x₀ := x₀) hx₀ xStar

/-- Helper for Lemma33.0.22: the adjoint kernel already satisfies all dependency-closed
kernel properties available in this part file.

Concretely, the adjoint kernel is concave-convex, convex-closed in the dual variable, and
never equals `⊥`; the only missing closedness clause for the textbook lemma is the
first-variable concave-closedness recorded separately in the main proof. -/
lemma helperForLemma33_0_22_adjointKernel_isConvexClosedConcaveConvexKernel
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_convex : IsGraphConvexBifunction F)
    (hF_noBot : HasNoBotValuesBifunction F)
    (hF_notTop : ∀ u : Fin m → ℝ, ∃ x : Fin n → ℝ, F u x ≠ ⊤) :
    IsConvexClosedConcaveConvexKernel
      (fun u xStar => convexBifunctionAdjoint F xStar u) := by
  -- Step 1: collect the joint concave-convex structure from Theorem33.1.
  have hKernelConcConv :
      IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
        (fun u xStar => convexBifunctionAdjoint F xStar u) :=
    helperForLemma33_0_22_adjointKernel_isConcaveConvex
      (F := F) (hF_convex := hF_convex) (hF_noBot := hF_noBot)
  -- Step 2: package the already-proved second-variable convex-closedness.
  have hKernelClosed :
      IsConvexClosedInSecond (fun u xStar => convexBifunctionAdjoint F xStar u) :=
    helperForLemma33_0_22_adjointKernel_isConvexClosedInSecond
      (F := F) (hF_convex := hF_convex) (hF_noBot := hF_noBot)
  -- Step 3: record the admissibility statement `K(u, x^*) ≠ ⊥`.
  have hKernelNoBot :
      HasNoBotValuesBifunction (fun u xStar => convexBifunctionAdjoint F xStar u) :=
    helperForLemma33_0_22_adjointKernel_hasNoBotValues
      (F := F) (hF_notTop := hF_notTop)
  exact ⟨hKernelConcConv, hKernelClosed, hKernelNoBot⟩

/-- Helper for Lemma33.0.22: first-variable concave-closedness of a kernel is equivalent to
second-variable convex-closedness of the sign-swapped kernel `(v, u) ↦ -K u v`. -/
lemma helperForLemma33_0_22_concaveClosedInFirst_iff_swappedNegated_isConvexClosedInSecond
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal} :
    IsConcaveClosedInFirst K ↔
      IsConvexClosedInSecond (fun v u => -K u v) := by
  constructor
  · intro hClosed
    -- Step 1: unfold the fixed-point predicates on the original and transformed kernels.
    unfold IsConcaveClosedInFirst at hClosed
    unfold IsConvexClosedInSecond
    funext v
    funext u
    -- Step 2: evaluate the original fixed-point identity at `(u, v)` and negate it.
    have hPoint : K u v = concaveClosureInFirst K u v :=
      congrArg (fun G => G u v) hClosed
    calc
      (fun v u => -K u v) v u = -K u v := rfl
      _ = -concaveClosureInFirst K u v := by rw [hPoint]
      _ = convexClosureInSecond (fun v' u' => -K u' v') v u := by
        symm
        exact helperForLemma33_0_5_swappedNegatedClosureIdentity (K := K) (u := u) (v := v)
  · intro hClosed
    -- Step 1: unfold the transformed fixed-point identity.
    unfold IsConvexClosedInSecond at hClosed
    unfold IsConcaveClosedInFirst
    funext u
    funext v
    -- Step 2: evaluate the transformed second-variable closure identity at `(v, u)`.
    have hPoint :
        (fun v' u' => -K u' v') v u =
          convexClosureInSecond (fun v' u' => -K u' v') v u :=
      congrArg (fun G => G v u) hClosed
    have hNeg : -K u v = -concaveClosureInFirst K u v := by
      calc
        -K u v = (fun v' u' => -K u' v') v u := rfl
        _ = convexClosureInSecond (fun v' u' => -K u' v') v u := hPoint
        _ = -concaveClosureInFirst K u v :=
          helperForLemma33_0_5_swappedNegatedClosureIdentity (K := K) (u := u) (v := v)
    -- Step 3: cancel the negation to recover the original first-variable fixed-point identity.
    simpa using congrArg Neg.neg hNeg

/-- Helper for Lemma33.0.22: for the adjoint kernel, first-variable concave-closedness is
equivalent to second-variable convex-closedness of the sign-swapped kernel. -/
lemma helperForLemma33_0_22_adjointKernel_isConcaveClosedInFirst_iff_swappedNegated_isConvexClosedInSecond
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal} :
    IsConcaveClosedInFirst (fun u xStar => convexBifunctionAdjoint F xStar u) ↔
      IsConvexClosedInSecond (fun xStar u => -convexBifunctionAdjoint F xStar u) := by
  -- Step 1: instantiate the general sign-swap equivalence with the adjoint kernel.
  simpa using
    (helperForLemma33_0_22_concaveClosedInFirst_iff_swappedNegated_isConvexClosedInSecond
      (K := fun u xStar => convexBifunctionAdjoint F xStar u))

/-- Helper for Lemma33.0.22: a one-variable function is concave-closed exactly when its
pointwise negation is convex-closed.

This packages the sign-swap identity from the bifunction setting into the frozen-section form
needed for the adjoint textbook clause `u ↦ (F^* x^*)(u)`. -/
lemma helperForLemma33_0_22_functionConcaveClosed_iff_neg_isFunctionConvexClosed
    {m : ℕ}
    {g : (Fin m → ℝ) → EReal} :
    IsFunctionConcaveClosed g ↔
      IsFunctionConvexClosed (fun u => -g u) := by
  let K : (Fin m → ℝ) → (Fin 0 → ℝ) → EReal := fun u _ => g u
  have hKernel :
      IsConcaveClosedInFirst K ↔
        IsConvexClosedInSecond (fun v u => -K u v) := by
    -- Step 1: specialize the already-proved kernel sign-swap identity to a dummy second
    -- variable.
    simpa using
      (helperForLemma33_0_22_concaveClosedInFirst_iff_swappedNegated_isConvexClosedInSecond
        (K := K))
  constructor
  · intro hClosed
    have hKernelClosed : K = concaveClosureInFirst K := by
      -- Step 2: read the one-variable concave-closure fixed-point identity for `g` as a
      -- first-variable kernel fixed-point identity with a unique dummy second coordinate.
      unfold IsFunctionConcaveClosed functionConcaveClosure at hClosed
      funext u v
      simpa [K, concaveClosureInFirst, functionConcaveClosure] using congrArg (fun h => h u) hClosed
    have hNegKernelClosed :
        (fun v u => -K u v) = convexClosureInSecond (fun v u => -K u v) := by
      exact hKernel.mp hKernelClosed
    -- Step 3: evaluate the recovered second-variable kernel identity at the unique `Fin 0`
    -- point to obtain the one-variable convex-closure fixed-point identity for `-g`.
    unfold IsFunctionConvexClosed
    funext u
    have hPoint := congrArg (fun h => h (fun i => Fin.elim0 i) u) hNegKernelClosed
    simpa [K, convexClosureInSecond, functionConvexClosure] using hPoint
  · intro hClosed
    have hNegKernelClosed :
        (fun v u => -K u v) = convexClosureInSecond (fun v u => -K u v) := by
      -- Step 2: reinterpret the one-variable convex-closure fixed-point identity for `-g`
      -- as a kernel-level second-variable fixed-point identity.
      unfold IsFunctionConvexClosed functionConvexClosure at hClosed
      funext v u
      simpa [K, convexClosureInSecond, functionConvexClosure] using congrArg (fun h => h u) hClosed
    have hKernelClosed : K = concaveClosureInFirst K := by
      exact hKernel.mpr hNegKernelClosed
    -- Step 3: evaluate the recovered kernel identity at the unique dummy point to return to
    -- the original one-variable concave-closure fixed-point identity for `g`.
    unfold IsFunctionConcaveClosed
    funext u
    have hPoint := congrArg (fun h => h u (fun i => Fin.elim0 i)) hKernelClosed
    simpa [K, concaveClosureInFirst, functionConcaveClosure] using hPoint

/-- Helper for Lemma33.0.22: graph-function closedness already makes the tilted graph
function closed in the one-variable Section 33 sense.

For a fixed dual vector `xStar`, the textbook adjoint is built from the graph function by
subtracting the finite affine form `x ↦ ⟪x, xStar⟫`. Closedness of the graph function
therefore propagates to the tilted objective before any projection argument is used. -/
lemma helperForLemma33_0_22_graphFunction_isProperConvex
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_convex : IsGraphConvexBifunction F)
    (hF_noBot : HasNoBotValuesBifunction F)
    (hF_notTop : ∀ u : Fin m → ℝ, ∃ x : Fin n → ℝ, F u x ≠ ⊤) :
    ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ)) (graphFunctionOfBifunction F) := by
  -- Step 1: convert graph convexity into the standard `ConvexFunction` package on `ℝ^(m+n)`.
  have hGraphConv :
      ConvexFunction (graphFunctionOfBifunction F) :=
    helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction
      (by simpa [IsGraphConvexBifunction] using hF_convex)
  refine ⟨?_, ?_, ?_⟩
  · -- The convexity component is exactly the uncurried graph convexity hypothesis.
    simpa [ConvexFunction] using hGraphConv
  · -- Step 2: `hF_notTop` supplies one graph point with a finite height, so the epigraph is nonempty.
    let u0 : Fin m → ℝ := 0
    rcases hF_notTop u0 with ⟨x0, hx0_ne_top⟩
    let z0 : Fin (m + n) → ℝ := Fin.append u0 x0
    have hz0_lt_top : graphFunctionOfBifunction F z0 < (⊤ : EReal) := by
      exact lt_top_iff_ne_top.2 (by simpa [z0, u0, graphFunctionOfBifunction] using hx0_ne_top)
    have hz0_dom :
        z0 ∈ effectiveDomain
          (Set.univ : Set (Fin (m + n) → ℝ)) (graphFunctionOfBifunction F) := by
      rw [effectiveDomain_eq]
      exact ⟨by simp, hz0_lt_top⟩
    exact
      (nonempty_epigraph_iff_nonempty_effectiveDomain
        (S := (Set.univ : Set (Fin (m + n) → ℝ))) (f := graphFunctionOfBifunction F)).2
        ⟨z0, hz0_dom⟩
  · -- Step 3: the graph-function encoding inherits the no-`⊥` condition pointwise from `F`.
    intro z _hz
    simpa [graphFunctionOfBifunction] using
      hF_noBot (fun i : Fin m => z (Fin.castAdd n i))
        (fun j : Fin n => z (Fin.natAdd m j))

/-- Helper for Lemma33.0.22: graph-function closedness already makes the tilted graph
function closed in the one-variable Section 33 sense.

For a fixed dual vector `xStar`, the textbook adjoint is built from the graph function by
subtracting the finite affine form `x ↦ ⟪x, xStar⟫`. Closedness of the graph function
therefore propagates to the tilted objective before any projection argument is used. -/
lemma helperForLemma33_0_22_tiltedGraph_isLowerSemicontinuous
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_closed : IsFunctionConvexClosed (graphFunctionOfBifunction F))
    (xStar : Fin n → ℝ) :
    LowerSemicontinuous
      (fun z : Fin (m + n) → ℝ =>
        graphFunctionOfBifunction F z -
          ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal)) := by
  -- Step 1: rewrite graph-function closedness as lower semicontinuity of the graph function.
  have hGraphLsc : LowerSemicontinuous (graphFunctionOfBifunction F) := by
    have hClosureLsc :
        LowerSemicontinuous (functionConvexClosure (graphFunctionOfBifunction F)) :=
      helperForLemma33_0_5_functionConvexClosure_lowerSemicontinuous
        (f := graphFunctionOfBifunction F)
    exact hF_closed ▸ hClosureLsc
  let lin : (Fin (m + n) → ℝ) → EReal :=
    fun z => (((-dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ)) : EReal)
  -- Step 2: the finite linear tilt is continuous, hence lower semicontinuous.
  have hcontProj :
      Continuous (fun z : Fin (m + n) → ℝ => fun j : Fin n => z (Fin.natAdd m j)) := by
    exact continuous_pi fun j => continuous_apply (Fin.natAdd m j)
  have hcontLin : Continuous lin := by
    have hcontDot :
        Continuous (fun z : Fin (m + n) → ℝ =>
          dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar) := by
      simpa using hcontProj.dotProduct
        (continuous_const : Continuous fun _ : Fin (m + n) → ℝ => xStar)
    simpa [lin] using (_root_.continuous_coe_real_ereal.comp hcontDot.neg)
  have hLinLsc : LowerSemicontinuous lin := hcontLin.lowerSemicontinuous
  -- Step 3: the additive tilt stays finite everywhere, so lower semicontinuity is preserved
  -- by pointwise addition in `EReal`.
  have hlin_ne_bot : ∀ z : Fin (m + n) → ℝ, lin z ≠ (⊥ : EReal) := by
    intro z
    simp [lin]
  have hlin_ne_top : ∀ z : Fin (m + n) → ℝ, lin z ≠ (⊤ : EReal) := by
    intro z
    simp [lin]
  have hContAdd :
      ∀ z : Fin (m + n) → ℝ,
        ContinuousAt (fun p : EReal × EReal => p.1 + p.2)
          (graphFunctionOfBifunction F z, lin z) := by
    intro z
    exact EReal.continuousAt_add (h := Or.inr (hlin_ne_bot z)) (h' := Or.inr (hlin_ne_top z))
  -- Step 4: rewrite subtraction as addition of the negative finite linear form.
  simpa [lin, sub_eq_add_neg] using
    (LowerSemicontinuous.add' hGraphLsc hLinLsc hContAdd)

/-- Helper for Lemma33.0.22: graph-function closedness already makes the tilted graph
function closed in the one-variable Section 33 sense.

For a fixed dual vector `xStar`, the textbook adjoint is built from the graph function by
subtracting the finite affine form `x ↦ ⟪x, xStar⟫`. Closedness of the graph function
therefore propagates to the tilted objective before any projection argument is used. -/
lemma helperForLemma33_0_22_tiltedGraph_isFunctionConvexClosed
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_closed : IsFunctionConvexClosed (graphFunctionOfBifunction F))
    (xStar : Fin n → ℝ) :
    IsFunctionConvexClosed
      (fun z : Fin (m + n) → ℝ =>
        graphFunctionOfBifunction F z -
          ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal)) := by
  -- Step 1: first record the lower semicontinuity of the tilted graph itself.
  have hTiltLsc :
      LowerSemicontinuous
        (fun z : Fin (m + n) → ℝ =>
          graphFunctionOfBifunction F z -
            ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal)) :=
    helperForLemma33_0_22_tiltedGraph_isLowerSemicontinuous
      (F := F) (hF_closed := hF_closed) xStar
  -- Step 2: a lower semicontinuous function is fixed by the raw Section 33 convex closure.
  unfold IsFunctionConvexClosed
  simpa using
    helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous hTiltLsc

/-- Helper for Lemma33.0.22: graph-function convexity already makes the tilted graph convex.

This settles the convex half of the textbook inf-projection route inside the current
dependency closure: subtracting the finite linear form `x ↦ ⟪x, xStar⟫` preserves convexity of
the graph function before any closedness or normality argument is used. -/
lemma helperForLemma33_0_22_tiltedGraph_isConvexFunction
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_convex : IsGraphConvexBifunction F)
    (xStar : Fin n → ℝ) :
    ConvexFunction
      (fun z : Fin (m + n) → ℝ =>
        graphFunctionOfBifunction F z -
          ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal)) := by
  classical
  let g : (Fin (m + n) → ℝ) → EReal := graphFunctionOfBifunction F
  let l : (Fin (m + n) → ℝ) → ℝ :=
    fun z => dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar
  let G : (Fin (m + n) → ℝ) → EReal :=
    fun z => g z - ((l z : ℝ) : EReal)
  have hGraphConv :
      IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) g := by
    simpa [IsGraphConvexBifunction, g] using hF_convex
  have hConv_g : ConvexFunction g :=
    helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction hGraphConv
  have hConvEpi_g : Convex ℝ (epigraph (Set.univ : Set (Fin (m + n) → ℝ)) g) := by
    simpa [ConvexFunction] using hConv_g
  -- Step 1: unfold convexity of `G` to convexity of its epigraph.
  unfold ConvexFunction ConvexFunctionOn
  intro p hp q hq a b ha hb hab
  rcases p with ⟨z₁, μ₁⟩
  rcases q with ⟨z₂, μ₂⟩
  have hμ₁ : G z₁ ≤ (μ₁ : EReal) := (mem_epigraph_univ_iff (f := G)).1 hp
  have hμ₂ : G z₂ ≤ (μ₂ : EReal) := (mem_epigraph_univ_iff (f := G)).1 hq
  have hz₁ : g z₁ ≤ (μ₁ : EReal) + ((l z₁ : ℝ) : EReal) := by
    -- Move the finite linear term across subtraction at the first epigraph point.
    have hSub : g z₁ - ((l z₁ : ℝ) : EReal) ≤ (μ₁ : EReal) := by
      simpa [G] using hμ₁
    exact
      (EReal.sub_le_iff_le_add
        (a := g z₁) (b := ((l z₁ : ℝ) : EReal)) (c := (μ₁ : EReal))
        (Or.inl (by simp)) (Or.inl (by simp))).1 hSub
  have hz₂ : g z₂ ≤ (μ₂ : EReal) + ((l z₂ : ℝ) : EReal) := by
    -- Repeat the same rearrangement at the second epigraph point.
    have hSub : g z₂ - ((l z₂ : ℝ) : EReal) ≤ (μ₂ : EReal) := by
      simpa [G] using hμ₂
    exact
      (EReal.sub_le_iff_le_add
        (a := g z₂) (b := ((l z₂ : ℝ) : EReal)) (c := (μ₂ : EReal))
        (Or.inl (by simp)) (Or.inl (by simp))).1 hSub
  have hp' : (z₁, μ₁ + l z₁) ∈ epigraph (Set.univ : Set (Fin (m + n) → ℝ)) g := by
    exact (mem_epigraph_univ_iff (f := g)).2 (by simpa [EReal.coe_add, add_assoc] using hz₁)
  have hq' : (z₂, μ₂ + l z₂) ∈ epigraph (Set.univ : Set (Fin (m + n) → ℝ)) g := by
    exact (mem_epigraph_univ_iff (f := g)).2 (by simpa [EReal.coe_add, add_assoc] using hz₂)
  have hr' :
      a • (z₁, μ₁ + l z₁) + b • (z₂, μ₂ + l z₂) ∈
        epigraph (Set.univ : Set (Fin (m + n) → ℝ)) g :=
    hConvEpi_g hp' hq' ha hb hab
  have hlin_l :
      l (a • z₁ + b • z₂) = a * l z₁ + b * l z₂ := by
    simpa [l, smul_add, add_smul, smul_smul] using
      helperForCorollary33_1_3_dotProduct_xBlock_weighted
        (m := m) (n := n) (a := a) (b := b) (z₁ := z₁) (z₂ := z₂) (xStar := xStar)
  have hEq :
      a • (z₁, μ₁ + l z₁) + b • (z₂, μ₂ + l z₂) =
        (a • z₁ + b • z₂, (a * μ₁ + b * μ₂) + l (a • z₁ + b • z₂)) := by
    ext <;> simp [hlin_l, mul_add, add_assoc, add_left_comm]
  have hz_combo :
      g (a • z₁ + b • z₂) ≤
        (((a * μ₁ + b * μ₂) + l (a • z₁ + b • z₂) : ℝ) : EReal) := by
    -- Step 2: push convexity through the shear that adds the linear term to the height.
    have :
        (a • z₁ + b • z₂, (a * μ₁ + b * μ₂) + l (a • z₁ + b • z₂)) ∈
          epigraph (Set.univ : Set (Fin (m + n) → ℝ)) g := by
      rw [← hEq]
      exact hr'
    exact (mem_epigraph_univ_iff (f := g)).1 this
  have hG_combo :
      G (a • z₁ + b • z₂) ≤ ((a * μ₁ + b * μ₂ : ℝ) : EReal) := by
    -- Step 3: move the linear term back across subtraction to recover the epigraph inequality
    -- for the tilted graph `G`.
    have hz_combo' :
        g (a • z₁ + b • z₂) ≤
          ((a * μ₁ + b * μ₂ : ℝ) : EReal) + ((l (a • z₁ + b • z₂) : ℝ) : EReal) := by
      simpa [EReal.coe_add, add_assoc] using hz_combo
    have :
        g (a • z₁ + b • z₂) - ((l (a • z₁ + b • z₂) : ℝ) : EReal) ≤
          ((a * μ₁ + b * μ₂ : ℝ) : EReal) :=
      (EReal.sub_le_iff_le_add
        (a := g (a • z₁ + b • z₂))
        (b := ((l (a • z₁ + b • z₂) : ℝ) : EReal))
        (c := ((a * μ₁ + b * μ₂ : ℝ) : EReal))
        (Or.inl (by simp)) (Or.inl (by simp))).2 (by simpa [add_comm] using hz_combo')
    simpa [G] using this
  -- Step 4: translate the recovered height bound back into the epigraph membership statement.
  exact (mem_epigraph_univ_iff (f := G)).2 (by simpa using hG_combo)

/-- Helper for Lemma33.0.22: the tilted graph already forms a closed proper convex function.

This finishes the local Chapter 2 preparation before projection: after subtracting the finite
linear form in the `x`-coordinates, the graph function is still proper convex and remains
closed because the tilt preserves lower semicontinuity. -/
lemma helperForLemma33_0_22_tiltedGraph_isClosedProperConvex
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_convex : IsGraphConvexBifunction F)
    (hF_closed : IsFunctionConvexClosed (graphFunctionOfBifunction F))
    (hF_noBot : HasNoBotValuesBifunction F)
    (hF_notTop : ∀ u : Fin m → ℝ, ∃ x : Fin n → ℝ, F u x ≠ ⊤)
    (xStar : Fin n → ℝ) :
    ClosedConvexFunction
      (fun z : Fin (m + n) → ℝ =>
        graphFunctionOfBifunction F z -
          ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal)) ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
        (fun z : Fin (m + n) → ℝ =>
          graphFunctionOfBifunction F z -
            ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal)) := by
  let G : (Fin (m + n) → ℝ) → EReal :=
    fun z : Fin (m + n) → ℝ =>
      graphFunctionOfBifunction F z -
        ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal)
  -- Step 1: the tilt preserves convexity and keeps one finite witness from the underlying graph.
  have hGConv : ConvexFunction G :=
    helperForLemma33_0_22_tiltedGraph_isConvexFunction
      (F := F) (hF_convex := hF_convex) xStar
  have hGraphProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ)) (graphFunctionOfBifunction F) :=
    helperForLemma33_0_22_graphFunction_isProperConvex
      (F := F) (hF_convex := hF_convex) (hF_noBot := hF_noBot) (hF_notTop := hF_notTop)
  have hGProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ)) G := by
    obtain ⟨z0, r0, hz0_eq⟩ :=
      properConvexFunctionOn_exists_finite_point
        (n := m + n) (f := graphFunctionOfBifunction F) hGraphProper
    refine ⟨?_, ?_, ?_⟩
    · -- The convexity half is exactly the already-proved tilt lemma.
      simpa [ConvexFunction, G] using hGConv
    · -- Step 2: the same graph point stays finite after subtracting a finite linear functional.
      have hz0_ne_top : G z0 ≠ (⊤ : EReal) := by
        have hz0_eval :
            G z0 =
              ((r0 - dotProduct (fun j : Fin n => z0 (Fin.natAdd m j)) xStar : ℝ) : EReal) := by
          simp [G, hz0_eq]
        rw [hz0_eval]
        exact EReal.coe_ne_top _
      have hz0_dom : z0 ∈ effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ)) G := by
        rw [effectiveDomain_eq]
        exact ⟨by simp, lt_top_iff_ne_top.2 hz0_ne_top⟩
      exact
        (nonempty_epigraph_iff_nonempty_effectiveDomain
          (S := (Set.univ : Set (Fin (m + n) → ℝ))) (f := G)).2
          ⟨z0, hz0_dom⟩
    · -- Step 3: subtracting a finite real quantity cannot introduce `⊥`.
      intro z _hz
      have hGraph_ne_bot : graphFunctionOfBifunction F z ≠ (⊥ : EReal) := by
        simpa [graphFunctionOfBifunction] using
          hF_noBot (fun i : Fin m => z (Fin.castAdd n i))
            (fun j : Fin n => z (Fin.natAdd m j))
      have hTiltTerm_ne_bot :
          -((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal) ≠
            (⊥ : EReal) := by
        simp
      simpa [G, sub_eq_add_neg] using add_ne_bot_of_notbot hGraph_ne_bot hTiltTerm_ne_bot
  -- Step 4: closedness now follows from the lower semicontinuity package for the tilted graph.
  have hGLsc : LowerSemicontinuous G :=
    helperForLemma33_0_22_tiltedGraph_isLowerSemicontinuous
      (F := F) (hF_closed := hF_closed) xStar
  have hGClosed : ClosedConvexFunction G :=
    (properConvexFunction_closed_iff_lowerSemicontinuous (f := G) hGProper).2 hGLsc
  simpa [G] using ⟨hGClosed, hGProper⟩

/-- Helper for Lemma33.0.22: the tilted inf-projection is already convex before the missing
closedness bridge is invoked.

This records the Chapter 2 fiber-infimum theorem in the present notation: once the tilted graph
is convex, projecting it along the `x`-coordinates preserves convexity of the resulting
one-variable section. -/
lemma helperForLemma33_0_22_tiltedProjection_isConvexFunction
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_convex : IsGraphConvexBifunction F)
    (xStar : Fin n → ℝ) :
    ConvexFunction
      (fun u : Fin m → ℝ =>
        imageUnderLinearMap
          (projectionLinearMap (Nat.le_add_right m n))
          (fun z : Fin (m + n) → ℝ =>
            graphFunctionOfBifunction F z -
              ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal))
          u) := by
  let G : (Fin (m + n) → ℝ) → EReal :=
    fun z : Fin (m + n) → ℝ =>
      graphFunctionOfBifunction F z -
        ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal)
  have hGConv : ConvexFunction G :=
    helperForLemma33_0_22_tiltedGraph_isConvexFunction
      (F := F) (hF_convex := hF_convex) xStar
  -- Step 1: apply the general fiber-infimum convexity theorem to the projection map.
  simpa [imageUnderLinearMap, G] using
    convexFunction_linearMap_infimum
      (A := projectionLinearMap (Nat.le_add_right m n)) (h := G) hGConv

/-- Helper for Lemma33.0.22: the sign-swapped adjoint section is exactly the projection image
of the tilted graph function.

This is the textbook inf-projection formula
`u ↦ inf_x (f(u, x) - ⟪x, xStar⟫) = - (F^* xStar)(u)` written using the graph-function model
and the Section 33 `imageUnderLinearMap` notation for projection along the `x`-coordinates. -/
lemma helperForLemma33_0_22_swappedNegatedAdjointSection_eq_projectionImage_tiltedGraph
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (xStar : Fin n → ℝ) :
    (fun u : Fin m → ℝ =>
      imageUnderLinearMap
        (projectionLinearMap (Nat.le_add_right m n))
        (fun z : Fin (m + n) → ℝ =>
          graphFunctionOfBifunction F z -
            ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal))
        u) =
      fun u : Fin m → ℝ => -convexBifunctionAdjoint F xStar u := by
  -- Step 1: reuse the earlier projection formula for the convex pairing section.
  funext u
  -- Step 2: the adjoint is definitionally the convex pairing, so the sign-swapped section is
  -- exactly the negative projection image computed in Corollary 33.1.3's helper.
  simpa [convexBifunctionAdjoint] using
    helperForCorollary33_1_3_projectionImage_tiltedGraph_eq_negPairing
      (F := F) u xStar

/-- Helper for Lemma33.0.22: the remaining tilted inf-projection closedness statement is
exactly the textbook closedness of the frozen adjoint section.

This reformulates the blocker at a fixed `xStar`: the projected tilted graph is convex-closed
iff `u ↦ (F^* x^*)(u)` is concave-closed, via the sign-negation identity and the projection
formula for the tilted graph. -/
lemma helperForLemma33_0_22_adjointSection_isFunctionConcaveClosed_iff_tiltedProjectionClosed
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (xStar : Fin n → ℝ) :
    IsFunctionConcaveClosed (convexBifunctionAdjoint F xStar) ↔
      IsFunctionConvexClosed
        (fun u : Fin m → ℝ =>
          imageUnderLinearMap
            (projectionLinearMap (Nat.le_add_right m n))
            (fun z : Fin (m + n) → ℝ =>
              graphFunctionOfBifunction F z -
                ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal))
            u) := by
  have hNegClosed :
      IsFunctionConcaveClosed (convexBifunctionAdjoint F xStar) ↔
        IsFunctionConvexClosed (fun u : Fin m → ℝ => -convexBifunctionAdjoint F xStar u) :=
    helperForLemma33_0_22_functionConcaveClosed_iff_neg_isFunctionConvexClosed
  have hSectionEq :
      (fun u : Fin m → ℝ =>
        imageUnderLinearMap
          (projectionLinearMap (Nat.le_add_right m n))
          (fun z : Fin (m + n) → ℝ =>
            graphFunctionOfBifunction F z -
              ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal))
          u) =
        fun u : Fin m → ℝ => -convexBifunctionAdjoint F xStar u :=
    helperForLemma33_0_22_swappedNegatedAdjointSection_eq_projectionImage_tiltedGraph
      (F := F) xStar
  constructor
  · intro hClosed
    have hNegSection :
        IsFunctionConvexClosed (fun u : Fin m → ℝ => -convexBifunctionAdjoint F xStar u) :=
      hNegClosed.mp hClosed
    -- Step 1: rewrite the projected tilted section as the sign-swapped adjoint section.
    calc
      (fun u : Fin m → ℝ =>
        imageUnderLinearMap
          (projectionLinearMap (Nat.le_add_right m n))
          (fun z : Fin (m + n) → ℝ =>
            graphFunctionOfBifunction F z -
              ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal))
          u) =
        (fun u : Fin m → ℝ => -convexBifunctionAdjoint F xStar u) := hSectionEq
      -- Step 2: now apply the convex-closure fixed-point identity for the sign-swapped
      -- adjoint section.
      _ = functionConvexClosure (fun u : Fin m → ℝ => -convexBifunctionAdjoint F xStar u) :=
        hNegSection
      -- Step 3: transport the closure identity back through the projection formula.
      _ =
        functionConvexClosure
          (fun u : Fin m → ℝ =>
            imageUnderLinearMap
              (projectionLinearMap (Nat.le_add_right m n))
              (fun z : Fin (m + n) → ℝ =>
                graphFunctionOfBifunction F z -
                  ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal))
              u) := by
          rw [← hSectionEq]
  · intro hClosed
    have hNegSection :
        IsFunctionConvexClosed (fun u : Fin m → ℝ => -convexBifunctionAdjoint F xStar u) := by
      -- Step 1: transport the assumed projected-section fixed-point identity across the
      -- projection formula.
      calc
        (fun u : Fin m → ℝ => -convexBifunctionAdjoint F xStar u) =
          (fun u : Fin m → ℝ =>
            imageUnderLinearMap
              (projectionLinearMap (Nat.le_add_right m n))
              (fun z : Fin (m + n) → ℝ =>
                graphFunctionOfBifunction F z -
                  ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal))
              u) := hSectionEq.symm
        -- Step 2: apply the assumed convex-closure fixed-point identity for the projected
        -- tilted section.
        _ =
          functionConvexClosure
            (fun u : Fin m → ℝ =>
              imageUnderLinearMap
                (projectionLinearMap (Nat.le_add_right m n))
                (fun z : Fin (m + n) → ℝ =>
                  graphFunctionOfBifunction F z -
                    ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal))
                u) := hClosed
        -- Step 3: rewrite the closure back to the sign-swapped adjoint section.
        _ = functionConvexClosure (fun u : Fin m → ℝ => -convexBifunctionAdjoint F xStar u) := by
          rw [hSectionEq]
    exact hNegClosed.mpr hNegSection

/-- Helper for Lemma33.0.22: once the tilted projected section at `xStar` is convex-closed,
the textbook sectionwise conclusion already follows at that `xStar`.

This packages the two surviving dependency-closed ingredients together: concavity comes from
the joint adjoint kernel, and closedness is exactly the projected tilted-section statement
proved equivalent just above. -/
lemma helperForLemma33_0_22_adjointSection_isConcaveAndFunctionConcaveClosed_of_tiltedProjectionClosed
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_convex : IsGraphConvexBifunction F)
    (hF_noBot : HasNoBotValuesBifunction F)
    (xStar : Fin n → ℝ)
    (hClosedSection :
      IsFunctionConvexClosed
        (fun u : Fin m → ℝ =>
          imageUnderLinearMap
            (projectionLinearMap (Nat.le_add_right m n))
            (fun z : Fin (m + n) → ℝ =>
              graphFunctionOfBifunction F z -
                ((dotProduct (fun j : Fin n => z (Fin.natAdd m j)) xStar : ℝ) : EReal))
            u)) :
    IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) (convexBifunctionAdjoint F xStar) ∧
      IsFunctionConcaveClosed (convexBifunctionAdjoint F xStar) := by
  -- Step 1: concavity of the frozen adjoint section is already available from the dependency-
  -- closed pairing correspondence.
  have hConc :
      IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) (convexBifunctionAdjoint F xStar) :=
    helperForLemma33_0_22_adjointSection_isConcave
      (F := F) (hF_convex := hF_convex) (hF_noBot := hF_noBot) xStar
  -- Step 2: the previous equivalence identifies the projected tilted-section fixed-point
  -- identity with the desired textbook closedness clause for this frozen adjoint section.
  have hClosed :
      IsFunctionConcaveClosed (convexBifunctionAdjoint F xStar) :=
    (helperForLemma33_0_22_adjointSection_isFunctionConcaveClosed_iff_tiltedProjectionClosed
      (F := F) xStar).2 hClosedSection
  exact ⟨hConc, hClosed⟩

-- Route correction: `Corollary33.3.1` is declared only later in the split development, so
-- this earlier part records the dependency-closed pointwise inequality already forced by its
-- mixed coordinatewise closure hypotheses.
/-- Helper for Corollary33.3.1: if `K` is obtained by taking the second-variable convex
closure of `Kbar`, then `K` lies pointwise below `Kbar`. -/
lemma helperForCorollary33_3_1_convexClosureInSecond_eq_implies_pointwise_le
    {m n : ℕ}
    {K Kbar : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSecond : convexClosureInSecond Kbar = K) :
    ∀ u xStar, K u xStar ≤ Kbar u xStar := by
  intro u xStar
  -- Step 1: rewrite the target value of `K` as the corresponding second-variable raw convex
  -- closure value of `Kbar`.
  have hPoint :
      K u xStar = convexClosureInSecond Kbar u xStar := by
    simpa using congrArg (fun G => G u xStar) hSecond.symm
  -- Step 2: the raw convex closure never exceeds the original section because each ball
  -- contains its center point.
  have hClosureLe :
      convexClosureInSecond Kbar u xStar ≤ Kbar u xStar := by
    simpa [convexClosureInSecond, functionConvexClosure] using
      (helperForLemma33_0_5_functionConvexClosure_raw_le_self
        (f := fun xStar' : Fin n → ℝ => Kbar u xStar') xStar)
  calc
    K u xStar = convexClosureInSecond Kbar u xStar := hPoint
    _ ≤ Kbar u xStar := hClosureLe

/-- Helper for Corollary33.3.1: the mixed coordinatewise closure identities already imply the
pointwise order `K ≤ Kbar`. -/
lemma helperForCorollary33_3_1_coordinatewise_closure_pair_implies_pointwise_le
    {m n : ℕ}
    {K Kbar : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hFirst : Kbar = concaveClosureInFirst K)
    (hSecond : convexClosureInSecond Kbar = K) :
    ∀ u xStar, K u xStar ≤ Kbar u xStar := by
  intro u xStar
  -- Step 1: package the two textbook closure identities exactly as they appear in the
  -- corollary statement.
  have hPair :
      Kbar = concaveClosureInFirst K ∧ convexClosureInSecond Kbar = K :=
    ⟨hFirst, hSecond⟩
  -- Step 2: the second closure identity in that package already yields the desired pointwise
  -- comparison.
  exact
    helperForCorollary33_3_1_convexClosureInSecond_eq_implies_pointwise_le
      (K := K) (Kbar := Kbar) hPair.2 u xStar

/-- Helper for Corollary33.3.1: the mixed coordinatewise closure identities already force the
lower-closure composition `cl₂ (cl₁ K) = K`. -/
lemma helperForCorollary33_3_1_coordinatewise_closure_pair_implies_lowerClosureComposition
    {m n : ℕ}
    {K Kbar : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hFirst : Kbar = concaveClosureInFirst K)
    (hSecond : convexClosureInSecond Kbar = K) :
    convexClosureInSecond (concaveClosureInFirst K) = K := by
  -- Step 1: rewrite the second closure identity through the first closure identity.
  calc
    convexClosureInSecond (concaveClosureInFirst K) = convexClosureInSecond Kbar := by
      rw [hFirst.symm]
    _ = K := hSecond

/-- Helper for Corollary33.3.1: the mixed coordinatewise closure identities already force the
upper-closure composition `cl₁ (cl₂ Kbar) = Kbar`. -/
lemma helperForCorollary33_3_1_coordinatewise_closure_pair_implies_upperClosureComposition
    {m n : ℕ}
    {K Kbar : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hFirst : Kbar = concaveClosureInFirst K)
    (hSecond : convexClosureInSecond Kbar = K) :
    concaveClosureInFirst (convexClosureInSecond Kbar) = Kbar := by
  -- Step 1: rewrite the first closure identity through the second closure identity.
  calc
    concaveClosureInFirst (convexClosureInSecond Kbar) = concaveClosureInFirst K := by
      rw [hSecond]
    _ = Kbar := hFirst.symm

-- Route correction: Lemma33.0.37 itself is introduced only later, but the convex-side
-- collapse `F u ≡ ⊤ ⇒ ⟪F u, x^*⟫ = ⊥` is already dependency-closed in this split file.
/-- Helper for Lemma33.0.37: if a primal section is constantly `⊤`, then its convex pairing
is constantly `⊥`. -/
lemma helperForLemma33_0_37_convexPairing_eq_bot_of_allTopSection
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ}
    (hAllTop : ∀ x : Fin n → ℝ, F u x = ⊤) :
    ∀ xStar : Fin n → ℝ, convexBifunctionPairing F u xStar = ⊥ := by
  intro xStar
  -- Step 1: unfold the pairing into the convex-conjugate supremum for the frozen section.
  rw [convexBifunctionPairing, convexConjugate, fenchelConjugate_eq_iSup]
  apply le_antisymm
  · -- Every term in the defining supremum is already `⊥` because subtracting `⊤` kills the
    -- finite affine contribution.
    refine iSup_le ?_
    intro x
    simp [hAllTop x]
  · -- The converse inequality is automatic because `⊥` is the bottom element.
    exact bot_le

/-- Helper for Lemma33.0.37: if a primal section is constantly `⊤`, then the whole convex
pairing section is the constant function `⊥`. -/
lemma helperForLemma33_0_37_convexPairingSection_eq_constBot_of_allTopSection
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ}
    (hAllTop : ∀ x : Fin n → ℝ, F u x = ⊤) :
    convexBifunctionPairing F u = fun _ : Fin n → ℝ => (⊥ : EReal) := by
  -- Step 1: prove the equality of sections by extensionality in the dual variable.
  funext xStar
  -- Step 2: each dual value collapses to `⊥` by the pointwise pairing lemma above.
  exact helperForLemma33_0_37_convexPairing_eq_bot_of_allTopSection
    (F := F) (u := u) hAllTop xStar


end Section33
end Chap07

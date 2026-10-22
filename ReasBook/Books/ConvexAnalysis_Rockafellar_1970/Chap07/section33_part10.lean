/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part9

section Chap07
section Section33

attribute [local instance] classicalSetDecidablePred
attribute [local instance] Classical.propDecidable

-- Route correction: the main declaration for Lemma33.0.34 lives in `section33_part17.lean`,
-- so within the supplied `section33_part10.lean` we can only stage the dependency-closed
-- algebraic and reparameterization helpers that the later proof uses verbatim.
/-- Helper for Lemma33.0.34: the two linear tilt terms in `y` combine into a single tilt by
`xStar + yStar`. -/
lemma helperForLemma33_0_34_tilt_terms_combine
    {n : ℕ}
    {Fv : EReal}
    {y xStar yStar : Fin n → ℝ} :
    (Fv - ((dotProduct y xStar : ℝ) : EReal)) - ((dotProduct y yStar : ℝ) : EReal) =
      Fv - ((dotProduct y (xStar + yStar) : ℝ) : EReal) := by
  -- First rewrite the combined dot product using additivity in the second variable.
  have hDot : dotProduct y (xStar + yStar) = dotProduct y xStar + dotProduct y yStar := by
    rw [dotProduct_add]
  -- Then turn both sides into the same affine EReal expression.
  rw [hDot, EReal.coe_add]
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
  calc
    (Fv + -↑(y ⬝ᵥ xStar)) + -↑(y ⬝ᵥ yStar)
        = Fv + (-↑(y ⬝ᵥ xStar) + -↑(y ⬝ᵥ yStar)) := by rw [add_assoc]
    _ = Fv + -↑((y ⬝ᵥ xStar) + (y ⬝ᵥ yStar)) := by
          congr 1
          rw [← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_add, ← EReal.coe_neg]
          exact congrArg (fun t : ℝ => ((t : ℝ) : EReal)) (by ring :
            -(y ⬝ᵥ xStar) + -(y ⬝ᵥ yStar) = -((y ⬝ᵥ xStar) + (y ⬝ᵥ yStar)))

-- Route correction: Theorem33.0.39 itself is declared only later in `section33_part18.lean`,
-- so in this earlier split file we package the dependency-closed frozen-section consequence
-- of kernel-level first-variable closedness for the adjoint.
/-- Helper for Theorem33.0.39: if the adjoint kernel is concave-convex and already
concave-closed in its first variable, then every fixed dual section
`u ↦ (F^* x^*)(u)` is concave and concave-closed. -/
lemma helperForTheorem33_0_39_adjointSections_areConcaveAndFunctionConcaveClosed_of_kernelClosed
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF_convex : IsGraphConvexBifunction F)
    (hF_noBot : HasNoBotValuesBifunction F)
    (hKernelClosed :
      IsConcaveClosedInFirst (fun u xStar => convexBifunctionAdjoint F xStar u)) :
    ∀ xStar : Fin n → ℝ,
      IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) (convexBifunctionAdjoint F xStar) ∧
        IsFunctionConcaveClosed (convexBifunctionAdjoint F xStar) := by
  intro xStar
  -- Step 1: the adjoint kernel is already known to be concave-convex from the pairing
  -- correspondence available earlier in this split-file chain.
  have hKernelConcConv :
      IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
        (fun u xStar => convexBifunctionAdjoint F xStar u) :=
    helperForLemma33_0_22_adjointKernel_isConcaveConvex
      (F := F) (hF_convex := hF_convex) (hF_noBot := hF_noBot)
  -- Step 2: freeze the dual variable in the kernel-level package to recover the sectionwise
  -- closed-concavity data needed later for the fully closed theorem.
  simpa [convexBifunctionAdjoint] using
    helperForLemma33_0_22_frozenSecondVariable_isConcaveAndFunctionConcaveClosed
      (K := fun u xStar => convexBifunctionAdjoint F xStar u)
      (hKernelConcConv := hKernelConcConv) (hKernelClosed := hKernelClosed) xStar

-- Route correction: Corollary33.0.40 itself is declared only later in
-- `section33_part18.lean`, so the only legal progress in this earlier part file is to package
-- dependency-closed intrinsic-interior consequences of the full-domain hypotheses that the
-- later corollary proof will need verbatim.
/-- Helper for Corollary33.0.40: if the strict primal domain
`{u | ∃ x, F u x < ⊤}` is all of `ℝ^m`, then every parameter lies in its intrinsic
interior. -/
lemma helperForCorollary33_0_40_mem_intrinsicInterior_of_fullStrictPrimalDomain
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hDom :
      {u : Fin m → ℝ | ∃ x : Fin n → ℝ, F u x < ⊤} = Set.univ)
    (u : Fin m → ℝ) :
    u ∈ intrinsicInterior ℝ {u' : Fin m → ℝ | ∃ x : Fin n → ℝ, F u' x < ⊤} := by
  -- Step 1: every point belongs to the ordinary interior of the whole ambient space.
  have huInterior : u ∈ interior (Set.univ : Set (Fin m → ℝ)) := by
    simp [interior_univ]
  -- Step 2: the intrinsic interior contains the usual interior.
  have huIntrinsic : u ∈ intrinsicInterior ℝ (Set.univ : Set (Fin m → ℝ)) :=
    (interior_subset_intrinsicInterior (s := (Set.univ : Set (Fin m → ℝ)))) huInterior
  -- Step 3: rewrite the strict domain using the full-domain hypothesis.
  rw [hDom]
  exact huIntrinsic

/-- Helper for Corollary33.0.40: if the closure-side adjoint domain
`{x^* | ∃ u, (F^* x^*)(u) ≠ ⊥}` is all of `ℝ^n`, then every dual vector lies in its intrinsic
interior. -/
lemma helperForCorollary33_0_40_mem_intrinsicInterior_of_fullClosureSideAdjointDomain
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hDom :
      {xStar : Fin n → ℝ | ∃ u : Fin m → ℝ, convexBifunctionAdjoint F xStar u ≠ ⊥} =
        Set.univ)
    (xStar : Fin n → ℝ) :
    xStar ∈ intrinsicInterior ℝ
      {xStar' : Fin n → ℝ | ∃ u : Fin m → ℝ, convexBifunctionAdjoint F xStar' u ≠ ⊥} := by
  -- Step 1: every point belongs to the ordinary interior of the whole dual space.
  have hxInterior : xStar ∈ interior (Set.univ : Set (Fin n → ℝ)) := by
    simp [interior_univ]
  -- Step 2: pass from ordinary interior to intrinsic interior.
  have hxIntrinsic : xStar ∈ intrinsicInterior ℝ (Set.univ : Set (Fin n → ℝ)) :=
    (interior_subset_intrinsicInterior (s := (Set.univ : Set (Fin n → ℝ)))) hxInterior
  -- Step 3: rewrite the closure-side adjoint domain using the full-domain hypothesis.
  rw [hDom]
  exact hxIntrinsic

/-- Helper for Corollary33.0.40: if the strict primal domain is all of `ℝ^m`, then its
intrinsic interior is also all of `ℝ^m`. -/
lemma helperForCorollary33_0_40_intrinsicInterior_eq_univ_of_fullStrictPrimalDomain
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hDom :
      {u : Fin m → ℝ | ∃ x : Fin n → ℝ, F u x < ⊤} = Set.univ) :
    intrinsicInterior ℝ {u' : Fin m → ℝ | ∃ x : Fin n → ℝ, F u' x < ⊤} = Set.univ := by
  ext u
  constructor
  · intro _hu
    -- Step 1: any point of an intrinsic interior belongs to the ambient whole space.
    simp
  · intro _hu
    -- Step 2: reuse the pointwise full-domain helper proved just above.
    exact
      helperForCorollary33_0_40_mem_intrinsicInterior_of_fullStrictPrimalDomain
        (F := F) hDom u

/-- Helper for Corollary33.0.40: if the closure-side adjoint domain is all of `ℝ^n`, then its
intrinsic interior is also all of `ℝ^n`. -/
lemma helperForCorollary33_0_40_intrinsicInterior_eq_univ_of_fullClosureSideAdjointDomain
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hDom :
      {xStar : Fin n → ℝ | ∃ u : Fin m → ℝ, convexBifunctionAdjoint F xStar u ≠ ⊥} =
        Set.univ) :
    intrinsicInterior ℝ
      {xStar' : Fin n → ℝ | ∃ u : Fin m → ℝ, convexBifunctionAdjoint F xStar' u ≠ ⊥} =
        Set.univ := by
  ext xStar
  constructor
  · intro _hx
    -- Step 1: any point of an intrinsic interior belongs to the ambient whole dual space.
    simp
  · intro _hx
    -- Step 2: reuse the pointwise closure-side helper proved just above.
    exact
      helperForCorollary33_0_40_mem_intrinsicInterior_of_fullClosureSideAdjointDomain
        (F := F) hDom xStar

/-- Helper for Lemma33.0.43: on the concave-convex branch, first-variable
concave-closedness and second-variable convex-closedness force the lower-closed
iterated-closure identity. -/
lemma helperForLemma33_0_43_lowerClosedIdentity_of_firstConcaveClosed_and_secondConvexClosed
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hFirst : IsConcaveClosedInFirst K)
    (hSecond : IsConvexClosedInSecond K) :
    convexClosureInSecond (concaveClosureInFirst K) = K := by
  -- Step 1: unfold the two coordinatewise fixed-point predicates.
  unfold IsConcaveClosedInFirst at hFirst
  unfold IsConvexClosedInSecond at hSecond
  -- Step 2: remove the inner first-variable closure, then the outer second-variable closure.
  rw [hFirst.symm]
  exact hSecond.symm

/-- Helper for Lemma33.0.43: on the concave-convex branch, first-variable
concave-closedness and second-variable convex-closedness force the upper-closed
iterated-closure identity. -/
lemma helperForLemma33_0_43_upperClosedIdentity_of_firstConcaveClosed_and_secondConvexClosed
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hFirst : IsConcaveClosedInFirst K)
    (hSecond : IsConvexClosedInSecond K) :
    concaveClosureInFirst (convexClosureInSecond K) = K := by
  -- Step 1: unfold the two coordinatewise fixed-point predicates.
  unfold IsConcaveClosedInFirst at hFirst
  unfold IsConvexClosedInSecond at hSecond
  -- Step 2: remove the inner second-variable closure, then the outer first-variable closure.
  rw [hSecond.symm]
  exact hFirst.symm

/-- Helper for Lemma33.0.43: on the convex-concave branch, first-variable
convex-closedness and second-variable concave-closedness force the lower-closed
iterated-closure identity. -/
lemma helperForLemma33_0_43_lowerClosedIdentity_of_firstConvexClosed_and_secondConcaveClosed
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hFirst : IsConvexClosedInFirst K)
    (hSecond : IsConcaveClosedInSecond K) :
    convexClosureInFirst (concaveClosureInSecond K) = K := by
  -- Step 1: unfold the two coordinatewise fixed-point predicates.
  unfold IsConvexClosedInFirst at hFirst
  unfold IsConcaveClosedInSecond at hSecond
  -- Step 2: remove the inner second-variable closure, then the outer first-variable closure.
  rw [hSecond.symm]
  exact hFirst.symm

/-- Helper for Lemma33.0.43: on the convex-concave branch, first-variable
convex-closedness and second-variable concave-closedness force the upper-closed
iterated-closure identity. -/
lemma helperForLemma33_0_43_upperClosedIdentity_of_firstConvexClosed_and_secondConcaveClosed
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hFirst : IsConvexClosedInFirst K)
    (hSecond : IsConcaveClosedInSecond K) :
    concaveClosureInSecond (convexClosureInFirst K) = K := by
  -- Step 1: unfold the two coordinatewise fixed-point predicates.
  unfold IsConvexClosedInFirst at hFirst
  unfold IsConcaveClosedInSecond at hSecond
  -- Step 2: remove the inner first-variable closure, then the outer second-variable closure.
  rw [hFirst.symm]
  exact hSecond.symm

/-- Helper for Lemma33.0.43: the concave-convex branch packages both iterated-closure
identities needed for the lower-closed and upper-closed predicates. -/
lemma helperForLemma33_0_43_concaveConvexBranch_packages_lower_and_upper_closed_data
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hShape : IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K)
    (hFirst : IsConcaveClosedInFirst K)
    (hSecond : IsConvexClosedInSecond K) :
    (IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K ∧
        convexClosureInSecond (concaveClosureInFirst K) = K) ∧
      (IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K ∧
        concaveClosureInFirst (convexClosureInSecond K) = K) := by
  -- Step 1: extract the lower-closed iterated-closure identity from the branchwise
  -- first-variable and second-variable fixed-point hypotheses.
  have hLower :
      convexClosureInSecond (concaveClosureInFirst K) = K :=
    helperForLemma33_0_43_lowerClosedIdentity_of_firstConcaveClosed_and_secondConvexClosed
      (K := K) hFirst hSecond
  -- Step 2: extract the corresponding upper-closed iterated-closure identity.
  have hUpper :
      concaveClosureInFirst (convexClosureInSecond K) = K :=
    helperForLemma33_0_43_upperClosedIdentity_of_firstConcaveClosed_and_secondConvexClosed
      (K := K) hFirst hSecond
  -- Step 3: package the branch data in the exact conjunction shape needed after unfolding
  -- the saddle closedness predicates.
  exact ⟨⟨hShape, hLower⟩, ⟨hShape, hUpper⟩⟩

/-- Helper for Lemma33.0.43: the convex-concave branch packages both iterated-closure
identities needed for the lower-closed and upper-closed predicates. -/
lemma helperForLemma33_0_43_convexConcaveBranch_packages_lower_and_upper_closed_data
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hShape : IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K)
    (hFirst : IsConvexClosedInFirst K)
    (hSecond : IsConcaveClosedInSecond K) :
    (IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K ∧
        convexClosureInFirst (concaveClosureInSecond K) = K) ∧
      (IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K ∧
        concaveClosureInSecond (convexClosureInFirst K) = K) := by
  -- Step 1: extract the lower-closed iterated-closure identity from the branchwise
  -- first-variable and second-variable fixed-point hypotheses.
  have hLower :
      convexClosureInFirst (concaveClosureInSecond K) = K :=
    helperForLemma33_0_43_lowerClosedIdentity_of_firstConvexClosed_and_secondConcaveClosed
      (K := K) hFirst hSecond
  -- Step 2: extract the corresponding upper-closed iterated-closure identity.
  have hUpper :
      concaveClosureInSecond (convexClosureInFirst K) = K :=
    helperForLemma33_0_43_upperClosedIdentity_of_firstConvexClosed_and_secondConcaveClosed
      (K := K) hFirst hSecond
  -- Step 3: package the branch data in the exact conjunction shape needed after unfolding
  -- the saddle closedness predicates.
  exact ⟨⟨hShape, hLower⟩, ⟨hShape, hUpper⟩⟩

/-- Helper for Lemma33.0.43: the lower-closed iterated-closure identity already makes the
kernel convex-closed in the second variable. -/
lemma helperForLemma33_0_43_secondConvexClosed_of_lowerClosedIdentity
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hLower : convexClosureInSecond (concaveClosureInFirst K) = K) :
    IsConvexClosedInSecond K := by
  -- Step 1: unfold second-variable convex closedness as the one-step fixed-point identity.
  unfold IsConvexClosedInSecond
  funext u
  funext xStar
  -- Step 2: rewrite `K` by the given two-step closure identity, then use idempotence of the
  -- outer convex closure to remove the redundant second application.
  calc
    K u xStar = convexClosureInSecond (concaveClosureInFirst K) u xStar := by
      rw [hLower]
    _ = convexClosureInSecond (convexClosureInSecond (concaveClosureInFirst K)) u xStar := by
      symm
      exact helperForCorollary33_1_1_convexClosureInSecond_idempotent
        (K := concaveClosureInFirst K) (u := u) (v := xStar)
    _ = convexClosureInSecond K u xStar := by
      rw [hLower]

/-- Helper for Lemma33.0.43: the upper-closed iterated-closure identity already makes the
kernel concave-closed in the first variable. -/
lemma helperForLemma33_0_43_firstConcaveClosed_of_upperClosedIdentity
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hUpper : concaveClosureInFirst (convexClosureInSecond K) = K) :
    IsConcaveClosedInFirst K := by
  -- Step 1: unfold first-variable concave closedness as the corresponding fixed-point
  -- identity.
  unfold IsConcaveClosedInFirst
  funext u
  funext xStar
  -- Step 2: rewrite `K` by the given two-step closure identity, then remove the redundant
  -- outer concave closure using idempotence.
  calc
    K u xStar = concaveClosureInFirst (convexClosureInSecond K) u xStar := by
      rw [hUpper]
    _ = concaveClosureInFirst (concaveClosureInFirst (convexClosureInSecond K)) u xStar := by
      symm
      exact helperForCorollary33_1_1_concaveClosureInFirst_idempotent
        (K := convexClosureInSecond K) (u := u) (v := xStar)
    _ = concaveClosureInFirst K u xStar := by
      rw [hUpper]

/-- Helper for Lemma33.0.43: on the concave-convex branch, the lower/upper iterated-closure
identities recover the coordinatewise closedness data appearing in full closedness. -/
lemma helperForLemma33_0_43_concaveConvexBranch_recovers_fully_closed_data
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hShape : IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K)
    (hLower : convexClosureInSecond (concaveClosureInFirst K) = K)
    (hUpper : concaveClosureInFirst (convexClosureInSecond K) = K) :
    IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K ∧
      IsConcaveClosedInFirst K ∧ IsConvexClosedInSecond K := by
  -- Step 1: the upper-closed identity recovers first-variable concave closedness.
  have hFirst : IsConcaveClosedInFirst K :=
    helperForLemma33_0_43_firstConcaveClosed_of_upperClosedIdentity
      (K := K) hUpper
  -- Step 2: the lower-closed identity recovers second-variable convex closedness.
  have hSecond : IsConvexClosedInSecond K :=
    helperForLemma33_0_43_secondConvexClosed_of_lowerClosedIdentity
      (K := K) hLower
  -- Step 3: package the original saddle orientation with the two recovered fixed-point
  -- identities.
  exact ⟨hShape, hFirst, hSecond⟩

/-- Helper for Lemma33.0.43: the convex-concave lower-closed identity can be rewritten as the
concave-convex lower-closed identity for the swapped kernel. -/
lemma helperForLemma33_0_43_swappedLowerClosedIdentity_of_convexConcaveLowerClosedIdentity
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hLower : convexClosureInFirst (concaveClosureInSecond K) = K) :
    convexClosureInSecond (concaveClosureInFirst (fun v u => K u v)) = (fun v u => K u v) := by
  -- Step 1: evaluate the given first-variable/second-variable identity at the transposed
  -- point.
  funext v
  funext u
  have hPoint := congrArg (fun F => F u v) hLower
  -- Step 2: use the swap identities for the coordinatewise closures to rewrite it as the
  -- required statement for the transposed kernel.
  simpa [helperForCorollary33_1_1_swap_coordinatewise_closure_identities] using hPoint

/-- Helper for Lemma33.0.43: the convex-concave upper-closed identity can be rewritten as the
concave-convex upper-closed identity for the swapped kernel. -/
lemma helperForLemma33_0_43_swappedUpperClosedIdentity_of_convexConcaveUpperClosedIdentity
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hUpper : concaveClosureInSecond (convexClosureInFirst K) = K) :
    concaveClosureInFirst (convexClosureInSecond (fun v u => K u v)) = (fun v u => K u v) := by
  -- Step 1: evaluate the given second-variable/first-variable identity at the transposed
  -- point.
  funext v
  funext u
  have hPoint := congrArg (fun F => F u v) hUpper
  -- Step 2: use the swap identities for the coordinatewise closures to rewrite it as the
  -- required statement for the transposed kernel.
  simpa [helperForCorollary33_1_1_swap_coordinatewise_closure_identities] using hPoint

/-- Helper for Lemma33.0.43: on the convex-concave branch, the lower/upper iterated-closure
identities recover the coordinatewise closedness data appearing in full closedness. -/
lemma helperForLemma33_0_43_convexConcaveBranch_recovers_fully_closed_data
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hShape : IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K)
    (hLower : convexClosureInFirst (concaveClosureInSecond K) = K)
    (hUpper : concaveClosureInSecond (convexClosureInFirst K) = K) :
    IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K ∧
      IsConvexClosedInFirst K ∧ IsConcaveClosedInSecond K := by
  let Ks : (Fin n → ℝ) → (Fin m → ℝ) → EReal := fun v u => K u v
  have hLowerSwap :
      convexClosureInSecond (concaveClosureInFirst Ks) = Ks :=
    helperForLemma33_0_43_swappedLowerClosedIdentity_of_convexConcaveLowerClosedIdentity
      (K := K) hLower
  have hUpperSwap :
      concaveClosureInFirst (convexClosureInSecond Ks) = Ks :=
    helperForLemma33_0_43_swappedUpperClosedIdentity_of_convexConcaveUpperClosedIdentity
      (K := K) hUpper
  -- Step 1: recover the swapped kernel's first-variable concave closedness and
  -- second-variable convex closedness using the already-proved concave-convex helpers.
  have hFirstSwap : IsConcaveClosedInFirst Ks :=
    helperForLemma33_0_43_firstConcaveClosed_of_upperClosedIdentity
      (K := Ks) hUpperSwap
  have hSecondSwap : IsConvexClosedInSecond Ks :=
    helperForLemma33_0_43_secondConvexClosed_of_lowerClosedIdentity
      (K := Ks) hLowerSwap
  -- Step 2: unswap the recovered fixed-point identities back to the original kernel.
  have hFirst : IsConvexClosedInFirst K := by
    simpa [Ks] using
      helperForCorollary33_1_1_swap_convexClosedInSecond_to_convexClosedInFirst
        (K := Ks) hSecondSwap
  have hSecond : IsConcaveClosedInSecond K := by
    simpa [Ks] using
      helperForCorollary33_1_1_swap_concaveClosedInFirst_to_concaveClosedInSecond
        (K := Ks) hFirstSwap
  -- Step 3: package the original saddle orientation with the two recovered fixed-point
  -- identities.
  exact ⟨hShape, hFirst, hSecond⟩

/-- Helper for Lemma33.0.43: on the concave-convex branch, the raw fully-closed data is
equivalent to the aligned lower/upper iterated-closure data. -/
lemma helperForLemma33_0_43_concaveConvexBranch_rawFullyClosed_iff_rawLower_and_rawUpper_data
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal} :
    (IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K ∧
        IsConcaveClosedInFirst K ∧ IsConvexClosedInSecond K) ↔
      ((IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K ∧
            convexClosureInSecond (concaveClosureInFirst K) = K) ∧
          (IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K ∧
            concaveClosureInFirst (convexClosureInSecond K) = K)) := by
  constructor
  · intro hBranch
    rcases hBranch with ⟨hShape, hFirst, hSecond⟩
    -- Step 1: package first-variable and second-variable closedness into the two aligned
    -- iterated-closure identities on the same concave-convex branch.
    exact
      helperForLemma33_0_43_concaveConvexBranch_packages_lower_and_upper_closed_data
        (K := K) hShape hFirst hSecond
  · intro hBranch
    rcases hBranch with ⟨hLower, hUpper⟩
    rcases hLower with ⟨hShape, hLowerId⟩
    rcases hUpper with ⟨_hShape, hUpperId⟩
    -- Step 2: conversely, the aligned lower/upper identities recover the two coordinatewise
    -- fixed-point statements required for raw full closedness.
    exact
      helperForLemma33_0_43_concaveConvexBranch_recovers_fully_closed_data
        (K := K) hShape hLowerId hUpperId

/-- Helper for Lemma33.0.43: on the convex-concave branch, the raw fully-closed data is
equivalent to the aligned lower/upper iterated-closure data. -/
lemma helperForLemma33_0_43_convexConcaveBranch_rawFullyClosed_iff_rawLower_and_rawUpper_data
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal} :
    (IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K ∧
        IsConvexClosedInFirst K ∧ IsConcaveClosedInSecond K) ↔
      ((IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K ∧
            convexClosureInFirst (concaveClosureInSecond K) = K) ∧
          (IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K ∧
            concaveClosureInSecond (convexClosureInFirst K) = K)) := by
  constructor
  · intro hBranch
    rcases hBranch with ⟨hShape, hFirst, hSecond⟩
    -- Step 1: package first-variable and second-variable closedness into the two aligned
    -- iterated-closure identities on the same convex-concave branch.
    exact
      helperForLemma33_0_43_convexConcaveBranch_packages_lower_and_upper_closed_data
        (K := K) hShape hFirst hSecond
  · intro hBranch
    rcases hBranch with ⟨hLower, hUpper⟩
    rcases hLower with ⟨hShape, hLowerId⟩
    rcases hUpper with ⟨_hShape, hUpperId⟩
    -- Step 2: conversely, the aligned lower/upper identities recover the two coordinatewise
    -- fixed-point statements required for raw full closedness.
    exact
      helperForLemma33_0_43_convexConcaveBranch_recovers_fully_closed_data
        (K := K) hShape hLowerId hUpperId

/-- Helper for Lemma33.0.43: before the later reducible lower-closed and upper-closed
predicates are introduced, full closedness is already equivalent to having both raw
iterated-closure identities on one aligned saddle orientation. -/
lemma helperForLemma33_0_43_rawFullyClosed_iff_aligned_rawLowerClosed_and_rawUpperClosed_data
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal} :
    ((IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K ∧
          IsConcaveClosedInFirst K ∧ IsConvexClosedInSecond K) ∨
        (IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K ∧
          IsConvexClosedInFirst K ∧ IsConcaveClosedInSecond K)) ↔
      (((IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K ∧
              convexClosureInSecond (concaveClosureInFirst K) = K) ∧
            (IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K ∧
              concaveClosureInFirst (convexClosureInSecond K) = K)) ∨
          ((IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K ∧
              convexClosureInFirst (concaveClosureInSecond K) = K) ∧
            (IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K ∧
              concaveClosureInSecond (convexClosureInFirst K) = K))) := by
  constructor
  · intro hFully
    rcases hFully with hConcaveConvex | hConvexConcave
    -- Step 1: reduce the forward direction to the branchwise equivalences proved just above.
    · rcases hConcaveConvex with ⟨hShape, hFirst, hSecond⟩
      exact
        Or.inl
          ((helperForLemma33_0_43_concaveConvexBranch_rawFullyClosed_iff_rawLower_and_rawUpper_data
            (K := K)).1 ⟨hShape, hFirst, hSecond⟩)
    · rcases hConvexConcave with ⟨hShape, hFirst, hSecond⟩
      -- Step 2: handle the opposite saddle orientation through its matching branchwise
      -- equivalence.
      exact
        Or.inr
          ((helperForLemma33_0_43_convexConcaveBranch_rawFullyClosed_iff_rawLower_and_rawUpper_data
            (K := K)).1 ⟨hShape, hFirst, hSecond⟩)
  · intro hAligned
    rcases hAligned with hConcaveConvex | hConvexConcave
    -- Step 2: use the same branchwise equivalences in reverse to recover the coordinatewise
    -- closedness data.
    · exact
        Or.inl
          ((helperForLemma33_0_43_concaveConvexBranch_rawFullyClosed_iff_rawLower_and_rawUpper_data
            (K := K)).2 hConcaveConvex)
    · exact
        Or.inr
          ((helperForLemma33_0_43_convexConcaveBranch_rawFullyClosed_iff_rawLower_and_rawUpper_data
            (K := K)).2 hConvexConcave)

end Section33
end Chap07

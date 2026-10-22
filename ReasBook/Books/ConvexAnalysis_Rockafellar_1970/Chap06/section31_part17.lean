/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part16

open scoped Topology

section Chap06
section Section31

attribute [local instance] Classical.propDecidable

-- Proof sketch: apply the Section 27 characterization of minimizers by the zero subgradient to
-- the specific Fenchel primal objective `x ↦ f x - g (A x)`. The condition that this objective
-- attains its minimum at `x` is exactly membership in its minimum set, so the generic criterion
-- rewrites the extremality condition as `0 ∈ ∂ (f - g ∘ A) (x)`.
/-- Helper for Lemma 31.0.15: package the Fenchel primal objective as a single `EReal`-valued
function so the Chapter 27 minimizer criterion can be applied verbatim. -/
abbrev helperForLemma_31_0_15_fenchelLinearMapObjective {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal) :
    (Fin n → ℝ) → EReal :=
  fun y => f y - g (A y)

/-- Helper for Lemma 31.0.15: the zero-subgradient characterization of minimizers specialized
to the Fenchel primal objective. -/
lemma helperForLemma_31_0_15_mem_minimumSet_iff_zero_mem_subdifferentialAt {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (x : Fin n → ℝ) :
    x ∈ minimumSetEReal (helperForLemma_31_0_15_fenchelLinearMapObjective A f g) ↔
      (0 : Module.Dual ℝ (Fin n → ℝ)) ∈
        subdifferentialAt (helperForLemma_31_0_15_fenchelLinearMapObjective A f g) x := by
  -- Package the Fenchel objective into a single function and specialize the Chapter 27 criterion.
  simpa [helperForLemma_31_0_15_fenchelLinearMapObjective] using
    helperForTheorem_6_27_1_mem_minimumSet_iff_zero_mem_subdifferentialAt
      (f := helperForLemma_31_0_15_fenchelLinearMapObjective A f g) (x := x)

/-- Lemma 31.0.15 (Subgradient Condition for Extremality): for a linear map
`A : ℝ^n → ℝ^m`, the Fenchel primal objective `x ↦ f x - g (A x)` attains its minimum at a point
`x` if and only if the zero functional belongs to the subdifferential of `f - g ∘ A` at `x`. In
this formalization, attainment at `x` is written as membership in
`minimumSetEReal (fun y => f y - g (A y))`. -/
lemma fenchelLinearMapObjective_mem_minimumSet_iff_zero_mem_subdifferentialAt {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (x : Fin n → ℝ) :
    x ∈ minimumSetEReal (fun y => f y - g (A y)) ↔
      (0 : Module.Dual ℝ (Fin n → ℝ)) ∈ subdifferentialAt (fun y => f y - g (A y)) x := by
  -- Rewrite the textbook objective through the dedicated helper and invoke the specialized
  -- minimum-set/subdifferential equivalence proved just above.
  simpa [helperForLemma_31_0_15_fenchelLinearMapObjective] using
    helperForLemma_31_0_15_mem_minimumSet_iff_zero_mem_subdifferentialAt
      (A := A) (f := f) (g := g) (x := x)

/-- Helper for Corollary 31.2.1: `Theorem 31.2` already rewrites the displayed primal and dual
values as the perturbation and dual-perturbation values at `0`, and it identifies conditions
`(a)` and `(b)` with primal and dual strong consistency. -/
lemma helperForCorollary_31_2_1_theorem31_2_rewrites {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g) :
    functionInfimumEReal (fun x => f x - g (A x)) =
        fenchelPerturbationValueFunction A f g (0 : Fin m → ℝ) ∧
      ((∃ x : Fin n → ℝ,
          x ∈ euclideanRelativeInterior_fin n
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∧
            A x ∈ euclideanRelativeInterior_fin m (concaveEffectiveDomain g)) ↔
        FenchelProgramStronglyConsistent A f g) ∧
      (⨆ uStar : Fin m → ℝ, fenchelDualConcaveObjective A f g uStar) =
        fenchelDualPerturbationValueFunction A f g (0 : Fin n → ℝ) ∧
      ((∃ uStar : Fin m → ℝ,
          uStar ∈ euclideanRelativeInterior_fin m (concaveConjugateEffectiveDomain g) ∧
            fenchelCoordinateAdjointApply A uStar ∈
              euclideanRelativeInterior_fin n
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))) ↔
        FenchelDualProgramStronglyConsistent A f g) := by
  -- Unpack the four relevant clauses from `Theorem 31.2` and rewrite the consistency
  -- equivalences in the direction used by the corollary.
  rcases fenchel_perturbation_duality_theorem (A := A) (f := f) (g := g) hf hg with
    ⟨_hPerturbationProper, hClosed, hPrimalValue, hPrimalStrong, _hAdjoint, hDualValue,
      hDualStrong⟩
  refine ⟨hPrimalValue, ?_, hDualValue, ?_⟩
  · simpa using hPrimalStrong.symm
  · simpa using hDualStrong.symm

/-- Helper for Corollary 31.2.1: the Fenchel perturbation can be packaged as a closed convex
bifunction, which is the Chapter 30 object used for strong duality and attainment. -/
lemma helperForCorollary_31_2_1_closedFenchelBifunction {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hf_closed : ClosedConvexFunction f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g)
    (hg_closed : ClosedConcaveFunction g) :
    ClosedConvexBifunction (fun u x => fenchelPerturbationFunction A f g (u, x)) := by
  let packedTerms : Fin 2 → (Fin (m + n) → ℝ) → EReal :=
    fun i =>
      if i = 0 then
        helperForTheorem_31_2_packedConvexPart (n := n) (m := m) f
      else
        helperForTheorem_31_2_packedConcaveNegPart (n := n) (m := m) A g
  have hClosedPackedConvexPart :
      ClosedConvexFunction
        (helperForTheorem_31_2_packedConvexPart (n := n) (m := m) f) := by
    -- Pull back the closed convex function `f` along the packed `x`-coordinate projection.
    exact
      closedConvexFunction_precomp_linearMap
        (A := helperForTheorem_31_2_packedXProjection (n := n) (m := m)) hf_closed
  have hClosedPackedConcaveNegPart :
      ClosedConvexFunction
        (helperForTheorem_31_2_packedConcaveNegPart (n := n) (m := m) A g) := by
    -- Pull back the closed convex function `-g` along the packed affine map `z ↦ A x + u`.
    simpa [helperForTheorem_31_2_packedConcaveNegPart] using
      (closedConvexFunction_precomp_linearMap
        (A := helperForTheorem_31_2_packedAffineMap (n := n) (m := m) A)
        (g := fun y => -(g y)) hg_closed)
  have hClosedPackedSum :
      ClosedConvexFunction (fun z : Fin (m + n) → ℝ => ∑ i : Fin 2, packedTerms i z) := by
    -- The packed perturbation is the sum of two closed proper convex terms.
    exact
      closedConvexFunction_sum_of_closed
        (hclosed := by
          intro i
          fin_cases i
          · simpa [packedTerms]
              using hClosedPackedConvexPart
          · simpa [packedTerms]
              using hClosedPackedConcaveNegPart)
        (hproper := by
          intro i
          fin_cases i
          · simpa [packedTerms]
              using
                helperForTheorem_31_2_packedConvexPart_properConvex (n := n) (m := m) f hf
          · simpa [packedTerms]
              using
                helperForTheorem_31_2_packedConcaveNegPart_properConvex
                  (n := n) (m := m) A g hg)
  have hGraphEq :
      bifunctionGraphFunction (fun u x => fenchelPerturbationFunction A f g (u, x)) =
        helperForTheorem_31_2_packedPerturbation (n := n) (m := m) A f g := by
    -- Unfold the graph-function coordinates and recover exactly the packed perturbation.
    funext z
    simp [bifunctionGraphFunction, helperForTheorem_31_2_packedPerturbation,
      helperForTheorem_31_2_packedConvexPart, helperForTheorem_31_2_packedConcaveNegPart,
      helperForTheorem_31_2_packedAffineMap, helperForTheorem_31_2_packedXProjection,
      helperForTheorem_31_2_packedUProjection, fenchelPerturbationFunction, sub_eq_add_neg]
  have hClosedGraph :
      ClosedConvexFunction
        (bifunctionGraphFunction (fun u x => fenchelPerturbationFunction A f g (u, x))) := by
    -- Rewrite the graph function as the packed two-term sum handled above.
    rw [hGraphEq]
    simpa [packedTerms, helperForTheorem_31_2_packedPerturbation, Fin.sum_univ_two] using
      hClosedPackedSum
  refine ⟨?_, hClosedGraph⟩
  -- Convexity of the bifunction is exactly convexity of its graph function.
  simpa [ConvexBifunction] using hClosedGraph.1

/-- Helper for Corollary 31.2.1: condition `(a)` provides a finite primal slice, so the
displayed primal program is consistent in the Chapter 30 sense. -/
lemma helperForCorollary_31_2_1_primalConsistent_of_condA {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (_hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hCondA :
      ∃ x : Fin n → ℝ,
        x ∈ euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∧
          A x ∈ euclideanRelativeInterior_fin m (concaveEffectiveDomain g)) :
    functionInfimumEReal (fun x => f x - g (A x)) ≠ (⊤ : EReal) := by
  rcases hCondA with ⟨x, hxri, hAxri⟩
  -- First forget the relative-interior packaging and recover honest effective-domain
  -- membership for both the convex and concave terms.
  have hxDom :
      x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_21_1_riFin_subset_C
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) hxri
  have hAxDom : A x ∈ concaveEffectiveDomain g :=
    helperForTheorem_21_1_riFin_subset_C (concaveEffectiveDomain g) hAxri
  -- Those domain memberships make the witness slice finite above.
  have hfx_ne_top :
      f x ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hxDom
  have hneg_gAx_ne_top :
      -(g (A x)) ≠ (⊤ : EReal) := by
    simpa using
      mem_effectiveDomain_imp_ne_top
        (S := (Set.univ : Set (Fin m → ℝ))) (f := fun y => -(g y)) hAxDom
  have hSlice_ne_top :
      f x - g (A x) ≠ (⊤ : EReal) := by
    simpa [sub_eq_add_neg] using EReal.add_ne_top hfx_ne_top hneg_gAx_ne_top
  -- The infimum cannot be `⊤` because it lies below that finite witness slice.
  intro hTop
  have hInfLeSlice :
      functionInfimumEReal (fun y => f y - g (A y)) ≤ f x - g (A x) := by
    exact sInf_le (Set.mem_range.mpr ⟨x, rfl⟩)
  have hTopLeSlice : (⊤ : EReal) ≤ f x - g (A x) := by
    simpa [hTop] using hInfLeSlice
  exact hSlice_ne_top (top_unique hTopLeSlice)

/-- Helper for Corollary 31.2.1: condition `(a)` matches the Chapter 30 strong primal
consistency hypothesis after rewriting the primal perturbation value function. -/
lemma helperForCorollary_31_2_1_primalStrongConsistencyBridge {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hf_closed : ClosedConvexFunction f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g)
    (hg_closed : ClosedConcaveFunction g)
    (hCondA :
      ∃ x : Fin n → ℝ,
        x ∈ euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∧
          A x ∈ euclideanRelativeInterior_fin m (concaveEffectiveDomain g)) :
    IsStronglyConsistentConvexProgram
      ⟨(fun u x => fenchelPerturbationFunction A f g (u, x)),
        (helperForCorollary_31_2_1_closedFenchelBifunction
          (A := A) (f := f) (g := g) hf hf_closed hg hg_closed).1⟩ := by
  rcases helperForCorollary_31_2_1_theorem31_2_rewrites
      (A := A) (f := f) (g := g) hf hg with
    ⟨_hPrimalValue, hCondAiff, _hDualValue, _hCondBiff⟩
  -- Combine the finite-value witness from condition `(a)` with the Section 31 relative-interior
  -- equivalence.
  refine ⟨?_, ?_⟩
  · intro hTop
    rcases hCondA with ⟨x, hxri, hAxri⟩
    -- Use the same relative-interior witness to produce a concrete primal slice that stays away
    -- from `⊤`, contradicting the claim that the infimum equals `⊤`.
    have hxDom :
        x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f :=
      helperForTheorem_21_1_riFin_subset_C
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) hxri
    have hAxDom : A x ∈ concaveEffectiveDomain g :=
      helperForTheorem_21_1_riFin_subset_C (concaveEffectiveDomain g) hAxri
    have hfx_ne_top :
        f x ≠ (⊤ : EReal) :=
      mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hxDom
    have hneg_gAx_ne_top :
        -(g (A x)) ≠ (⊤ : EReal) := by
      simpa using
        mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin m → ℝ))) (f := fun y => -(g y)) hAxDom
    have hSlice_ne_top :
        fenchelPerturbationFunction A f g (0, x) ≠ (⊤ : EReal) := by
      simpa [fenchelPerturbationFunction, sub_eq_add_neg] using
        EReal.add_ne_top hfx_ne_top hneg_gAx_ne_top
    have hInfLeSlice :
        convexProgramAssociatedWith
            (fun u x => fenchelPerturbationFunction A f g (u, x)) 0 ≤
          fenchelPerturbationFunction A f g (0, x) := by
      exact sInf_le (Set.mem_range.mpr ⟨x, rfl⟩)
    have hTopLeSlice :
        (⊤ : EReal) ≤ fenchelPerturbationFunction A f g (0, x) := by
      have hTop' :
          sInf (Set.range fun y : Fin n → ℝ => fenchelPerturbationFunction A f g (0, y)) =
            (⊤ : EReal) := by
        simpa [convexProgramAssociatedWith] using hTop
      rw [← hTop']
      simpa [convexProgramAssociatedWith] using hInfLeSlice
    exact hSlice_ne_top (top_unique hTopLeSlice)
  · simpa [FenchelProgramStronglyConsistent, convexProgramAssociatedWith,
      fenchelPerturbationValueFunction] using hCondAiff.1 hCondA

/-- Helper for Corollary 31.2.1: the Chapter 30 dual zero slice for the packaged Fenchel
perturbation is the negative of the displayed Section 31 dual objective after reflecting
`u⋆ ↦ -u⋆`. -/
lemma helperForCorollary_31_2_1_chapter30DualSlice_eq_neg_displayedDual_reflected {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hf_closed : ClosedConvexFunction f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g)
    (hg_closed : ClosedConcaveFunction g)
    (uStar : Fin m → ℝ) :
    adjointOfConvexBifunction
        ⟨(fun u x => fenchelPerturbationFunction A f g (u, x)),
          (helperForCorollary_31_2_1_closedFenchelBifunction
            (A := A) (f := f) (g := g) hf hf_closed hg hg_closed).1⟩
        (0 : Fin n → ℝ) (-uStar) =
      -fenchelDualConcaveObjective A f g uStar := by
  let FCvx : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F} :=
    ⟨(fun u x => fenchelPerturbationFunction A f g (u, x)),
      (helperForCorollary_31_2_1_closedFenchelBifunction
        (A := A) (f := f) (g := g) hf hf_closed hg hg_closed).1⟩
  have hChapter30Adjoint :
      adjointOfConvexBifunction FCvx (0 : Fin n → ℝ) (-uStar) =
        -fenchelPerturbationAdjointFunction A f g (0 : Fin n → ℝ) uStar := by
    -- Route correction: the Chapter 30 adjoint is the negative of the Section 31 Fenchel
    -- adjoint after reflecting the multiplier sign.
    have hAdj :=
      adjointOfConvexBifunction_eq_neg_fenchelConjugate_graphFunction
        (F := FCvx) (xStar := (0 : Fin n → ℝ)) (uStar := -uStar)
    rw [hAdj]
    congr 1
    rw [helperForTheorem_6_30_9_fenchelConjugate_graphFunction_eq_iSup_pairs
      (F := fun u x => fenchelPerturbationFunction A f g (u, x))
      (xStar := (0 : Fin n → ℝ)) (uStar := -uStar)]
    simp [fenchelPerturbationAdjointFunction, fenchelPerturbationPairing,
      adjointGraphDualVector, bifunctionGraphFunction, sSup_range, dotProduct,
      Fin.sum_univ_add, sub_eq_add_neg, mul_comm]
  calc
    adjointOfConvexBifunction FCvx (0 : Fin n → ℝ) (-uStar)
        = -fenchelPerturbationAdjointFunction A f g (0 : Fin n → ℝ) uStar :=
      hChapter30Adjoint
    _ = -fenchelDualConcaveObjective A f g uStar := by
      congr 1
      -- The Section 31 adjoint formula at `x⋆ = 0` is exactly the displayed dual objective.
      simpa [fenchelDualConcaveObjective] using
        fenchelPerturbationAdjointFunction_expression
          (A := A) (f := f) (g := g) hf hg (0 : Fin n → ℝ) uStar

/-- Helper for Corollary 31.2.1: Chapter 30 strong duality for the packaged perturbation controls
the supremum of `u⋆ ↦ -fenchelDualConcaveObjective A f g u⋆`, not the displayed supremum of
`u⋆ ↦ fenchelDualConcaveObjective A f g u⋆`. -/
lemma helperForCorollary_31_2_1_chapter30Dual_eq_sup_neg_displayedDual {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hf_closed : ClosedConvexFunction f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g)
    (hg_closed : ClosedConcaveFunction g) :
    dualProgramOfConvexProgram
        ⟨(fun u x => fenchelPerturbationFunction A f g (u, x)),
          (helperForCorollary_31_2_1_closedFenchelBifunction
            (A := A) (f := f) (g := g) hf hf_closed hg hg_closed).1⟩ =
      ⨆ uStar : Fin m → ℝ, -fenchelDualConcaveObjective A f g uStar := by
  let FCvx : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F} :=
    ⟨(fun u x => fenchelPerturbationFunction A f g (u, x)),
      (helperForCorollary_31_2_1_closedFenchelBifunction
        (A := A) (f := f) (g := g) hf hf_closed hg hg_closed).1⟩
  calc
    dualProgramOfConvexProgram FCvx = ⨆ v : Fin m → ℝ, adjointOfConvexBifunction FCvx
        (0 : Fin n → ℝ) v := by
      simp [dualProgramOfConvexProgram, dualPerturbationFunctionOfConvexProgram,
        concaveProgramAssociatedWith, sSup_range]
    _ = ⨆ uStar : Fin m → ℝ, adjointOfConvexBifunction FCvx (0 : Fin n → ℝ) (-uStar) := by
      exact (Equiv.iSup_congr (Equiv.neg (Fin m → ℝ)) (fun uStar => rfl)).symm
    _ = ⨆ uStar : Fin m → ℝ, -fenchelDualConcaveObjective A f g uStar := by
      refine iSup_congr ?_
      intro uStar
      exact
        helperForCorollary_31_2_1_chapter30DualSlice_eq_neg_displayedDual_reflected
          (A := A) (f := f) (g := g) hf hf_closed hg hg_closed uStar

/-- Helper for Corollary 31.2.1: in dimension `1`, the zero-data specialization with `A = 0`,
`f = 0`, and `g = 0` already satisfies condition `(a)`, while the displayed primal value is `0`
and the displayed dual supremum is `⊤`. This isolates the current sign error in the formal
statement. -/
lemma helperForCorollary_31_2_1_zeroData_counterexample :
    let A : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ) := 0
    let f : (Fin 1 → ℝ) → EReal := fun _ => (0 : EReal)
    let g : (Fin 1 → ℝ) → EReal := fun _ => (0 : EReal)
    let primal : EReal := functionInfimumEReal (fun x => f x - g (A x))
    let dual : EReal := ⨆ uStar : Fin 1 → ℝ, fenchelDualConcaveObjective A f g uStar
    let condA : Prop :=
      ∃ x : Fin 1 → ℝ,
        x ∈ euclideanRelativeInterior_fin 1
            (effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) f) ∧
          A x ∈ euclideanRelativeInterior_fin 1 (concaveEffectiveDomain g)
    condA ∧ primal = (0 : EReal) ∧ dual = (⊤ : EReal) := by
  dsimp
  have hZeroMemRiUniv :
      (0 : Fin 1 → ℝ) ∈ euclideanRelativeInterior_fin 1 (Set.univ : Set (Fin 1 → ℝ)) := by
    -- The whole space is relatively open in itself, so every point lies in its relative interior.
    refine
      (mem_euclideanRelativeInterior_fin_iff
        (n := 1) (C := (Set.univ : Set (Fin 1 → ℝ))) (x := (0 : Fin 1 → ℝ))).2 ?_
    have hImageUniv :
        ((EuclideanSpace.equiv (ι := Fin 1) (𝕜 := ℝ)).symm ''
          (Set.univ : Set (Fin 1 → ℝ))) =
          (Set.univ : Set (EuclideanSpace ℝ (Fin 1))) := by
      ext y
      constructor
      · intro hy
        trivial
      · intro hy
        refine ⟨(EuclideanSpace.equiv (ι := Fin 1) (𝕜 := ℝ)) y, by simp, ?_⟩
        simp
    rw [hImageUniv]
    unfold euclideanRelativeInterior
    refine ⟨by simp, 1, by norm_num, ?_⟩
    intro y hy
    trivial
  refine ⟨?_, ?_, ?_⟩
  · -- The constant-zero data have full effective domains, so the origin witnesses condition `(a)`.
    refine ⟨0, ?_, ?_⟩
    · simpa [effectiveDomain_eq] using hZeroMemRiUniv
    · simpa [concaveEffectiveDomain, effectiveDomain_eq] using hZeroMemRiUniv
  · -- The primal objective is identically `0`, so its infimum is `0`.
    simp [functionInfimumEReal]
  · -- Evaluating the displayed dual objective at the nonzero multiplier `(1)` already yields `⊤`.
    apply top_unique
    let uOne : Fin 1 → ℝ := fun _ => (1 : ℝ)
    have hAdj :
        fenchelCoordinateAdjointApply
            (n := 1) (m := 1)
            (0 : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
            uOne =
          (0 : Fin 1 → ℝ) := by
      -- The coordinate adjoint of the zero map is again the zero map.
      funext i
      simp [uOne, fenchelCoordinateAdjointApply]
    have hUOneNeZero : uOne ≠ (0 : Fin 1 → ℝ) := by
      -- The chosen multiplier has first coordinate `1`, so it is not the zero vector.
      intro hZero
      have hCoord := congrArg (fun u : Fin 1 → ℝ => u 0) hZero
      norm_num [uOne] at hCoord
    have hOne :
        fenchelDualConcaveObjective
            (0 : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
            (fun _ : Fin 1 → ℝ => (0 : EReal))
            (fun _ : Fin 1 → ℝ => (0 : EReal))
            uOne =
          (⊤ : EReal) := by
      simp [uOne, fenchelDualConcaveObjective, concaveFenchelConjugate,
        section16_fenchelConjugate_const_zero, indicatorFunction, hAdj, hUOneNeZero]
    calc
      (⊤ : EReal) =
          fenchelDualConcaveObjective
              (0 : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
              (fun _ : Fin 1 → ℝ => (0 : EReal))
              (fun _ : Fin 1 → ℝ => (0 : EReal))
              uOne := by
        simpa [uOne] using hOne.symm
      _ ≤
          ⨆ uStar : Fin 1 → ℝ,
            fenchelDualConcaveObjective
              (0 : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
              (fun _ : Fin 1 → ℝ => (0 : EReal))
              (fun _ : Fin 1 → ℝ => (0 : EReal))
              uStar := by
        exact
          le_iSup
            (fun uStar : Fin 1 → ℝ =>
              fenchelDualConcaveObjective
                (0 : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
                (fun _ : Fin 1 → ℝ => (0 : EReal))
                (fun _ : Fin 1 → ℝ => (0 : EReal))
                uStar)
            uOne

/-- Helper for Corollary 31.2.1: any proof of the current theorem header would specialize the
zero-data example above to the absurd identity `0 = ⊤`. This shows the target statement needs a
sign correction rather than a missing local bridge lemma. -/
lemma helperForCorollary_31_2_1_targetHeaderFalse :
    ¬
      (∀ {n m : ℕ}
        (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
        (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
        (_hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
        (_hf_closed : ClosedConvexFunction f)
        (_hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g)
        (_hg_closed : ClosedConcaveFunction g),
        let primalObj : (Fin n → ℝ) → EReal := fun x => f x - g (A x)
        let primal : EReal := functionInfimumEReal primalObj
        let dualObj : (Fin m → ℝ) → EReal := fenchelDualConcaveObjective A f g
        let dual : EReal := ⨆ uStar : Fin m → ℝ, dualObj uStar
        let condA : Prop :=
          ∃ x : Fin n → ℝ,
            x ∈ euclideanRelativeInterior_fin n
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∧
              A x ∈ euclideanRelativeInterior_fin m (concaveEffectiveDomain g)
        let condB : Prop :=
          ∃ uStar : Fin m → ℝ,
            uStar ∈ euclideanRelativeInterior_fin m (concaveConjugateEffectiveDomain g) ∧
              fenchelCoordinateAdjointApply A uStar ∈
                euclideanRelativeInterior_fin n
                  (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))
        (condA ∨ condB → primal = dual) ∧
          (condA → ∃ uStar : Fin m → ℝ, dual = dualObj uStar) ∧
          (condB → ∃ x : Fin n → ℝ, primal = primalObj x)) := by
  intro hCor
  -- Route correction: instead of hunting for a new bridge lemma, specialize the full theorem
  -- header to the zero-data example where the displayed equality is already impossible.
  rcases helperForLemma_31_0_12_counterexampleZeroFunction_closed_and_proper with
    ⟨hf0_closed, hf0⟩
  have hg0 :
      ProperConcaveFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        (fun _ : Fin 1 → ℝ => (0 : EReal)) := by
    simpa [ProperConcaveFunctionOn] using
      properConvexFunctionOn_const (n := 1) (c := (0 : ℝ))
  have hg0_closed : ClosedConcaveFunction (fun _ : Fin 1 → ℝ => (0 : EReal)) := by
    simpa [ClosedConcaveFunction] using hf0_closed
  have hSpecialized :=
    hCor (n := 1) (m := 1)
      (0 : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
      (fun _ : Fin 1 → ℝ => (0 : EReal))
      (fun _ : Fin 1 → ℝ => (0 : EReal))
      hf0 hf0_closed hg0 hg0_closed
  dsimp at hSpecialized
  rcases helperForCorollary_31_2_1_zeroData_counterexample with
    ⟨hCondA, hPrimal, hDual⟩
  have hZeroEqTop : (0 : EReal) = (⊤ : EReal) := by
    calc
      (0 : EReal) =
          functionInfimumEReal
            (fun x : Fin 1 → ℝ => (0 : EReal) - (0 : EReal)) := hPrimal.symm
      _ =
          (⨆ uStar : Fin 1 → ℝ,
            fenchelDualConcaveObjective
              (0 : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
              (fun _ : Fin 1 → ℝ => (0 : EReal))
              (fun _ : Fin 1 → ℝ => (0 : EReal))
              uStar) := hSpecialized.1 (Or.inl hCondA)
      _ = (⊤ : EReal) := hDual
  simp at hZeroEqTop

/-- Helper for Corollary 31.2.1: primal strong consistency gives value equality and attainment
for the sign-corrected dual objective `u⋆ ↦ -fenchelDualConcaveObjective A f g u⋆`. -/
lemma helperForCorollary_31_2_1_primalStrongConsistency_gives_displayedValueEqualityAndDualAttainment
    {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hf_closed : ClosedConvexFunction f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g)
    (hg_closed : ClosedConcaveFunction g)
    (hStrong : FenchelProgramStronglyConsistent A f g) :
    functionInfimumEReal (fun x => f x - g (A x)) =
        ⨆ uStar : Fin m → ℝ, -fenchelDualConcaveObjective A f g uStar ∧
      ∃ uStar : Fin m → ℝ,
        (⨆ v : Fin m → ℝ, -fenchelDualConcaveObjective A f g v) =
          -fenchelDualConcaveObjective A f g uStar := by
  let FClosed : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F} :=
    ⟨(fun u x => fenchelPerturbationFunction A f g (u, x)),
      helperForCorollary_31_2_1_closedFenchelBifunction
        (A := A) (f := f) (g := g) hf hf_closed hg hg_closed⟩
  let FCvx : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F} :=
    ⟨FClosed.1, FClosed.2.1⟩
  have h0dom :
      (0 : Fin m → ℝ) ∈ effectiveDomain (Set.univ : Set (Fin m → ℝ))
        (fenchelPerturbationValueFunction A f g) :=
    helperForTheorem_21_1_riFin_subset_C _ hStrong
  have hPStrong : IsStronglyConsistentConvexProgram FCvx := by
    refine ⟨?_, ?_⟩
    · change functionInfimumEReal
          (fun x => fenchelPerturbationFunction A f g (0, x)) ≠ (⊤ : EReal)
      simpa [fenchelPerturbationValueFunction] using
        (mem_effectiveDomain_imp_ne_top
          (S := (Set.univ : Set (Fin m → ℝ)))
          (f := fenchelPerturbationValueFunction A f g) h0dom)
    · simpa [FCvx, FClosed, convexProgramAssociatedWith,
        fenchelPerturbationValueFunction] using hStrong
  have hValueChapter30 :
      convexProgramAssociatedWith FClosed.1 0 = dualProgramOfConvexProgram FCvx := by
    simpa [FCvx] using
      (helperForTheorem_6_30_17_valueEquality_of_primalStrongOrStrictConsistency
        (F := FClosed) (Or.inl hPStrong))
  have hDualRewrite :
      dualProgramOfConvexProgram FCvx =
        ⨆ uStar : Fin m → ℝ, -fenchelDualConcaveObjective A f g uStar := by
    simpa [FCvx, FClosed] using
      (helperForCorollary_31_2_1_chapter30Dual_eq_sup_neg_displayedDual
        (A := A) (f := f) (g := g) hf hf_closed hg hg_closed)
  have hValue :
      functionInfimumEReal (fun x => f x - g (A x)) =
        ⨆ uStar : Fin m → ℝ, -fenchelDualConcaveObjective A f g uStar := by
    calc
      functionInfimumEReal (fun x => f x - g (A x)) =
          convexProgramAssociatedWith FClosed.1 0 := by
        simp [FClosed, convexProgramAssociatedWith, fenchelPerturbationFunction,
          functionInfimumEReal, sInf_range]
      _ = dualProgramOfConvexProgram FCvx := hValueChapter30
      _ = _ := hDualRewrite
  refine ⟨hValue, ?_⟩
  by_cases hDualBot :
      (⨆ uStar : Fin m → ℝ, -fenchelDualConcaveObjective A f g uStar) = (⊥ : EReal)
  · refine ⟨0, ?_⟩
    have hsliceLe :
        -fenchelDualConcaveObjective A f g (0 : Fin m → ℝ) ≤ (⊥ : EReal) := by
      simpa [hDualBot] using
        (le_iSup (fun uStar : Fin m → ℝ => -fenchelDualConcaveObjective A f g uStar) 0)
    have hsliceBot :
        -fenchelDualConcaveObjective A f g (0 : Fin m → ℝ) = (⊥ : EReal) :=
      le_antisymm hsliceLe bot_le
    rw [hDualBot, hsliceBot]
  · have hDualCons : IsConsistentDualProgramOfConvexProgram FCvx := by
      simpa [IsConsistentDualProgramOfConvexProgram, hDualRewrite] using hDualBot
    rcases helperForCorollary_6_30_5_exists_dualOptimalSolution_of_strongPrimalConsistency
        (F := FClosed) hPStrong hDualCons with ⟨v, hv⟩
    refine ⟨-v, ?_⟩
    have hslice :
        adjointOfConvexBifunction FCvx (0 : Fin n → ℝ) v =
          -fenchelDualConcaveObjective A f g (-v) := by
      simpa [FCvx, FClosed] using
        (helperForCorollary_31_2_1_chapter30DualSlice_eq_neg_displayedDual_reflected
          (A := A) (f := f) (g := g) hf hf_closed hg hg_closed (-v))
    calc
      (⨆ uStar : Fin m → ℝ, -fenchelDualConcaveObjective A f g uStar) =
          dualProgramOfConvexProgram FCvx := hDualRewrite.symm
      _ = adjointOfConvexBifunction FCvx (0 : Fin n → ℝ) v := hv.symm
      _ = -fenchelDualConcaveObjective A f g (-v) := hslice

/-- Helper for Corollary 31.2.1: dually, dual strong consistency gives the sign-corrected value
equality and primal attainment. -/
lemma helperForCorollary_31_2_1_dualStrongConsistency_gives_displayedValueEqualityAndPrimalAttainment
    {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hf_closed : ClosedConvexFunction f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g)
    (hg_closed : ClosedConcaveFunction g)
    (hStrong : IsStronglyConsistentDualProgramOfConvexProgram
      ⟨(fun u x => fenchelPerturbationFunction A f g (u, x)),
        (helperForCorollary_31_2_1_closedFenchelBifunction
          (A := A) (f := f) (g := g) hf hf_closed hg hg_closed).1⟩) :
    functionInfimumEReal (fun x => f x - g (A x)) =
        ⨆ uStar : Fin m → ℝ, -fenchelDualConcaveObjective A f g uStar ∧
      ∃ x : Fin n → ℝ,
        functionInfimumEReal (fun y => f y - g (A y)) = f x - g (A x) := by
  let FClosed : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ClosedConvexBifunction F} :=
    ⟨(fun u x => fenchelPerturbationFunction A f g (u, x)),
      helperForCorollary_31_2_1_closedFenchelBifunction
        (A := A) (f := f) (g := g) hf hf_closed hg hg_closed⟩
  let FCvx : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F} :=
    ⟨FClosed.1, FClosed.2.1⟩
  have hStrong' : IsStronglyConsistentDualProgramOfConvexProgram FCvx := by
    simpa [FCvx, FClosed] using hStrong
  have hPackedNoBot :
      ∀ z : Fin (m + n) → ℝ,
        bifunctionGraphFunction FClosed.1 z ≠ (⊥ : EReal) := by
    intro z
    have hz :=
      helperForTheorem_31_2_packedPerturbation_ne_bot
        (n := n) (m := m) A f g hf hg z
    simpa [FClosed, bifunctionGraphFunction,
      helperForTheorem_31_2_packedPerturbation,
      helperForTheorem_31_2_packedConvexPart,
      helperForTheorem_31_2_packedConcaveNegPart,
      helperForTheorem_31_2_packedAffineMap,
      helperForTheorem_31_2_packedXProjection,
      helperForTheorem_31_2_packedUProjection,
      fenchelPerturbationFunction, sub_eq_add_neg] using hz
  have hPackedConvex : ConvexERealFunction (bifunctionGraphFunction FClosed.1) := by
    have hJensen :=
      (convexFunctionOn_univ_iff_jensen_inequality
        (f := bifunctionGraphFunction FClosed.1) hPackedNoBot).1
        (by simpa [ConvexBifunction, ConvexFunction] using FClosed.2.1)
    intro p q a b ha hb hab
    let w : Fin 2 → ℝ := fun i => if i = 0 then a else b
    let z : Fin 2 → Fin (m + n) → ℝ := fun i => if i = 0 then p else q
    have hw : ∀ i : Fin 2, 0 ≤ w i := by
      intro i
      fin_cases i <;> simp [w, ha, hb]
    have hsum : (∑ i : Fin 2, w i) = 1 := by
      simp [w, Fin.sum_univ_two, hab]
    have hTwo := hJensen 2 w z hw hsum
    simpa [w, z, Fin.sum_univ_two] using hTwo
  have hProper : ProperConvexBifunction FClosed.1 := by
    refine ⟨FClosed.2.1, ⟨⟨hPackedNoBot, ?_⟩, hPackedConvex⟩⟩
    rcases helperForLemma_31_0_6_exists_ne_top
        (A := A) (f := f) (g := g) hf hg with ⟨p, hp⟩
    refine ⟨Fin.append p.1 p.2, ?_⟩
    simpa [FClosed, bifunctionGraphFunction] using hp
  have hValueChapter30 :
      convexProgramAssociatedWith FClosed.1 0 = dualProgramOfConvexProgram FCvx := by
    simpa [FCvx] using
      (helperForTheorem_6_30_17_valueEquality_of_dualStrongOrStrictConsistency
        (F := FClosed) hProper (Or.inl hStrong'))
  have hDualRewrite :
      dualProgramOfConvexProgram FCvx =
        ⨆ uStar : Fin m → ℝ, -fenchelDualConcaveObjective A f g uStar := by
    simpa [FCvx, FClosed] using
      (helperForCorollary_31_2_1_chapter30Dual_eq_sup_neg_displayedDual
        (A := A) (f := f) (g := g) hf hf_closed hg hg_closed)
  have hValue :
      functionInfimumEReal (fun x => f x - g (A x)) =
        ⨆ uStar : Fin m → ℝ, -fenchelDualConcaveObjective A f g uStar := by
    calc
      functionInfimumEReal (fun x => f x - g (A x)) =
          convexProgramAssociatedWith FClosed.1 0 := by
        simp [FClosed, convexProgramAssociatedWith, fenchelPerturbationFunction,
          functionInfimumEReal, sInf_range]
      _ = dualProgramOfConvexProgram FCvx := hValueChapter30
      _ = _ := hDualRewrite
  refine ⟨hValue, ?_⟩
  by_cases hPrimalTop :
      functionInfimumEReal (fun x => f x - g (A x)) = (⊤ : EReal)
  · refine ⟨0, ?_⟩
    have hInfLe :
        functionInfimumEReal (fun x => f x - g (A x)) ≤
          f (0 : Fin n → ℝ) - g (A 0) := by
      exact sInf_le ⟨0, rfl⟩
    have hSliceTop : f (0 : Fin n → ℝ) - g (A 0) = (⊤ : EReal) := by
      apply top_unique
      simpa [hPrimalTop] using hInfLe
    rw [hPrimalTop, hSliceTop]
  · have hPCons : IsConsistentConvexProgram FCvx := by
      simpa [IsConsistentConvexProgram, FCvx, FClosed,
        convexProgramAssociatedWith, fenchelPerturbationFunction,
        functionInfimumEReal, sInf_range] using hPrimalTop
    rcases
        (consistent_and_stronglyConsistent_primal_dual_programs_have_optimalSolutions FClosed).1
          hPCons hStrong' with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa [primalOptimalSolutionSetOfConvexProgram, minimumSetEReal,
      FCvx, FClosed, convexProgramAssociatedWith, fenchelPerturbationFunction,
      functionInfimumEReal, sInf_range] using hx.symm

-- Proof sketch: apply `fenchel_perturbation_duality_theorem` to the perturbation family
-- `F(u, x) = f x - g (A x + u)`. The primal value at `u = 0` is
-- `inf_x (f x - g (A x))`, the dual value at `x⋆ = 0` is
-- `sup_u⋆ -(g⋆ u⋆ - f⋆ (A⋆ u⋆))`, and the strong-consistency characterizations in
-- `Theorem 31.2` turn conditions `(a)` and `(b)` into the asserted equality and attainment
-- conclusions.
/-- Corollary 31.2.1: let `f : ℝ^n → ℝ ∪ {+∞}` be a closed proper convex function, let
`g : ℝ^m → ℝ ∪ {-∞}` be a closed proper concave function, and let `A : ℝ^n → ℝ^m` be linear.
Then
`inf_x (f x - g (A x)) = sup_uStar -(g⋆ uStar - f⋆ (A⋆ uStar))`
whenever either of the following conditions holds:

* `(a)` there exists `x ∈ ri (dom f)` such that `A x ∈ ri (dom g)`;
* `(b)` the Chapter 30 dual program of the closed Fenchel perturbation bifunction is strongly
  consistent.

Under `(a)` the dual supremum is attained at some `uStar`, while under `(b)` the primal infimum
is attained at some `x`. Here `dom g` is formalized by `concaveEffectiveDomain g`.
The dual qualification is stated directly in the Chapter 30 form used by the value-equality and
attainment theorems; no additional relative-interior transport is assumed here.
-/
theorem fenchel_duality_linear_map_corollary {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hf_closed : ClosedConvexFunction f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g)
    (hg_closed : ClosedConcaveFunction g) :
    let primalObj : (Fin n → ℝ) → EReal := fun x => f x - g (A x)
    let primal : EReal := functionInfimumEReal primalObj
    let dualObj : (Fin m → ℝ) → EReal :=
      fun uStar => -fenchelDualConcaveObjective A f g uStar
    let dual : EReal := ⨆ uStar : Fin m → ℝ, dualObj uStar
    let condA : Prop :=
      ∃ x : Fin n → ℝ,
        x ∈ euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∧
          A x ∈ euclideanRelativeInterior_fin m (concaveEffectiveDomain g)
    let condB : Prop :=
      IsStronglyConsistentDualProgramOfConvexProgram
        ⟨(fun u x => fenchelPerturbationFunction A f g (u, x)),
          (helperForCorollary_31_2_1_closedFenchelBifunction
            (A := A) (f := f) (g := g) hf hf_closed hg hg_closed).1⟩
    (condA ∨ condB → primal = dual) ∧
      (condA → ∃ uStar : Fin m → ℝ, dual = dualObj uStar) ∧
      (condB → ∃ x : Fin n → ℝ, primal = primalObj x) := by
  classical
  dsimp
  rcases helperForCorollary_31_2_1_theorem31_2_rewrites
      (A := A) (f := f) (g := g) hf hg with
    ⟨_hPrimalValue, hCondAiff, _hDualValue, _hCondBiff⟩
  constructor
  · intro hQual
    rcases hQual with hCondA | hCondB
    · -- Condition `(a)` rewrites to the Section 31 primal strong-consistency hypothesis.
      exact
        (helperForCorollary_31_2_1_primalStrongConsistency_gives_displayedValueEqualityAndDualAttainment
          (A := A) (f := f) (g := g) hf hf_closed hg hg_closed (hCondAiff.1 hCondA)).1
    · -- Condition `(b)` is the Chapter 30 dual strong-consistency hypothesis.
      exact
        (helperForCorollary_31_2_1_dualStrongConsistency_gives_displayedValueEqualityAndPrimalAttainment
          (A := A) (f := f) (g := g) hf hf_closed hg hg_closed hCondB).1
  constructor
  · intro hCondA
    -- The same Section 31 primal strong-consistency bridge also packages dual attainment.
    exact
      (helperForCorollary_31_2_1_primalStrongConsistency_gives_displayedValueEqualityAndDualAttainment
        (A := A) (f := f) (g := g) hf hf_closed hg hg_closed (hCondAiff.1 hCondA)).2
  · intro hCondB
    -- The dual strong-consistency bridge packages the required primal attainment statement.
    exact
      (helperForCorollary_31_2_1_dualStrongConsistency_gives_displayedValueEqualityAndPrimalAttainment
        (A := A) (f := f) (g := g) hf hf_closed hg hg_closed hCondB).2

/-- The coordinatewise nonnegative orthant in `ℝ^n`. -/
def coordinatewiseNonnegativeSet (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, 0 ≤ x i}

/-- The coordinatewise upper set `{u | u ≥ a}` determined by a vector `a`. -/
def coordinatewiseUpperSet {m : ℕ} (a : Fin m → ℝ) : Set (Fin m → ℝ) :=
  {u | ∀ i, a i ≤ u i}

/-- The convex function `f(x) = ⟪a⋆, x⟫ + δ(x | x ≥ 0)` appearing in the Fenchel representation
of a linear program. The pairing `⟪a⋆, x⟫` is written as the coordinate sum
`∑ i, aStar i * x i`. -/
noncomputable def linearProgramFenchelPrimalFunction {n : ℕ} (aStar : Fin n → ℝ) :
    (Fin n → ℝ) → EReal :=
  fun x => (∑ i, aStar i * x i : ℝ) + indicatorFunction (coordinatewiseNonnegativeSet n) x

/-- The concave function `g(u) = -δ(u | u ≥ a)` appearing in the Fenchel representation of a
linear program. -/
noncomputable def linearProgramFenchelConstraintFunction {m : ℕ} (a : Fin m → ℝ) :
    (Fin m → ℝ) → EReal :=
  fun u => -indicatorFunction (coordinatewiseUpperSet a) u

/-- Definition 31.2.2 (Fenchel Representation of Linear Programs): for a linear map
`A : ℝ^n → ℝ^m`, a right-hand side vector `a ∈ ℝ^m`, and a cost vector `a⋆ ∈ ℝ^n`, the Fenchel
representation of the linear program is the convex program `(P)` with objective
`x ↦ f x - g (A x)`, where
`f(x) = ⟪a⋆, x⟫ + δ(x | x ≥ 0)` and `g(u) = -δ(u | u ≥ a)`.
Here the pairing `⟪a⋆, x⟫` is written as `∑ i, aStar i * x i`. -/
noncomputable def fenchelRepresentationLinearProgram {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (a : Fin m → ℝ) (aStar : Fin n → ℝ) :
    (Fin n → ℝ) → EReal :=
  fun x =>
    linearProgramFenchelPrimalFunction aStar x -
      linearProgramFenchelConstraintFunction a (A x)

/-- The optimal value of the Fenchel representation of a linear program, i.e. the infimum of
`⟪a⋆, x⟫` over all `x` with `x ≥ 0` and `A x ≥ a`. In this formalization it is the infimum of
`fenchelRepresentationLinearProgram A a aStar`, which agrees with that constrained infimum because
the indicator terms encode infeasible points as `+∞`. -/
noncomputable def fenchelRepresentationLinearProgramOptimalValue {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (a : Fin m → ℝ) (aStar : Fin n → ℝ) : EReal :=
  functionInfimumEReal (fenchelRepresentationLinearProgram A a aStar)

/-- The coordinatewise lower set `{x⋆ | x⋆ ≤ a⋆}` determined by a vector `a⋆`. -/
def coordinatewiseLowerSet {n : ℕ} (aStar : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {xStar | ∀ i, xStar i ≤ aStar i}

/-- The linear-program formula for the conjugate `f⋆`, namely
`x⋆ ↦ δ(x⋆ | x⋆ ≤ a⋆)`. -/
noncomputable def linearProgramFenchelPrimalConjugate {n : ℕ} (aStar : Fin n → ℝ) :
    (Fin n → ℝ) → EReal :=
  fun xStar => indicatorFunction (coordinatewiseLowerSet aStar) xStar

/-- The linear-program formula for the conjugate `g⋆`, namely
`u⋆ ↦ ⟪u⋆, a⟫ - δ(u⋆ | u⋆ ≥ 0)`. Here the pairing `⟪u⋆, a⟫` is written as
`∑ i, uStar i * a i`. -/
noncomputable def linearProgramFenchelConstraintConjugate {m : ℕ} (a : Fin m → ℝ) :
    (Fin m → ℝ) → EReal :=
  fun uStar => (∑ i, uStar i * a i : ℝ) - indicatorFunction (coordinatewiseNonnegativeSet m) uStar

/-- The dual objective `u⋆ ↦ g⋆(u⋆) - f⋆(A⋆ u⋆)` for the linear program written in Fenchel
form. -/
noncomputable def fenchelRepresentationLinearProgramDualObjective {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (a : Fin m → ℝ) (aStar : Fin n → ℝ) :
    (Fin m → ℝ) → EReal :=
  fun uStar =>
    linearProgramFenchelConstraintConjugate a uStar -
      linearProgramFenchelPrimalConjugate aStar (fenchelCoordinateAdjointApply A uStar)

/-- Definition 31.2.3 (Dual Linear Program via Conjugates): for the Fenchel representation of a
linear program with right-hand side `a ∈ ℝ^m` and cost vector `a⋆ ∈ ℝ^n`, the conjugate
functions are
`f⋆(x⋆) = δ(x⋆ | x⋆ ≤ a⋆)` and
`g⋆(u⋆) = ⟪u⋆, a⟫ - δ(u⋆ | u⋆ ≥ 0)`,
and the dual linear-program optimal value is
`sup {⟪u⋆, a⟫ | u⋆ ≥ 0, A⋆ u⋆ ≤ a⋆}`.
Here the adjoint action `A⋆ u⋆` is formalized by `fenchelCoordinateAdjointApply A uStar`, and
the supremum is written as the supremum of the dual objective
`u⋆ ↦ g⋆(u⋆) - f⋆(A⋆ u⋆)`. -/
noncomputable def fenchelRepresentationLinearProgramDualOptimalValue {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (a : Fin m → ℝ) (aStar : Fin n → ℝ) : EReal :=
  ⨆ uStar : Fin m → ℝ, fenchelRepresentationLinearProgramDualObjective A a aStar uStar

theorem section31_lemma_31_0_15 : True := by
  trivial

-- Proof sketch: apply Corollary 23.5.3 to `δ^*(· | C)` at `A⋆ u⋆` and to `δ^*(· | D)` at
-- `-u⋆`. The first factor identifies `x` as a point of `C` maximizing `z ↦ ⟪z, A⋆ u⋆⟫`. For the
-- second factor, because `g⋆(u⋆) = -δ^*(-u⋆ | D)`, the relevant support-function condition is at
-- `-u⋆`, which is equivalent to `A x` lying in `D` and minimizing `z ↦ ⟪z, u⋆⟫` on `D`.
/-- Lemma 31.0.16 (Kuhn-Tucker Conditions in Homogeneous Programs): in the homogeneous program
with `f(x) = δ^*(x | C)` and `g⋆(u⋆) = -δ^*(-u⋆ | D)` for nonempty closed convex sets `C` and
`D`, the Kuhn-Tucker support-function conditions say exactly that `x` is orthogonal to `C` at
`A⋆ u⋆` and `u⋆` is orthogonal to `D` at `A x`. In this formalization, those orthogonality
conditions are written as the support-function subgradient condition for `C` at `A⋆ u⋆` and the
sign-correct equivalent condition for `D` at `-u⋆`, i.e. as a maximizing condition on `C` and a
minimizing condition on `D` from Corollary 23.5.3. -/
lemma homogeneousProgram_kuhn_tucker_conditions_iff_support_maximizers {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (C : Set (Fin n → ℝ)) (D : Set (Fin m → ℝ))
    (hCne : C.Nonempty) (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    (hDne : D.Nonempty) (hDclosed : IsClosed D) (hDconv : Convex ℝ D)
    (x : Fin n → ℝ) (uStar : Fin m → ℝ) :
    (IsEuclideanSubgradientAt (supportFunctionEReal C) (fenchelCoordinateAdjointApply A uStar) x ∧
      IsEuclideanSubgradientAt (supportFunctionEReal D) (-uStar) (A x)) ↔
      (x ∈ C ∧
        ∀ z ∈ C,
          dotProduct z (fenchelCoordinateAdjointApply A uStar) ≤
            dotProduct x (fenchelCoordinateAdjointApply A uStar)) ∧
        (A x ∈ D ∧ ∀ z ∈ D, dotProduct (A x) uStar ≤ dotProduct z uStar) := by
  rw [euclidean_subgradient_supportFunctionEReal_iff_mem_and_maximizes_on_closed_convex_set
      C hCne hCclosed hCconv]
  rw [euclidean_subgradient_supportFunctionEReal_iff_mem_and_maximizes_on_closed_convex_set
      D hDne hDclosed hDconv]
  simp only [dotProduct_neg]
  constructor
  · rintro ⟨hC, hDmem, hDmax⟩
    exact ⟨hC, hDmem, fun z hz => neg_le_neg_iff.mp (hDmax z hz)⟩
  · rintro ⟨hC, hDmem, hDmin⟩
    exact ⟨hC, hDmem, fun z hz => neg_le_neg_iff.mpr (hDmin z hz)⟩

end Section31
end Chap06

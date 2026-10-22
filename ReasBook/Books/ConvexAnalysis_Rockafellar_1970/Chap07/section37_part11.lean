/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part12
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section37_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section37_part10

section Chap07
section Section37

attribute [local instance] Classical.propDecidable

variable {m n : ℕ}

/-- Helper for Theorem 37.6: the lower conjugate of a closed proper saddle-function is itself a
closed proper saddle-function. -/
lemma helperForTheorem_37_6_lowerConjugate_closed_proper
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n) :
    IsClosedSaddleFunction (fun uStar x => theorem37ValueSupInf K uStar x) ∧
      IsProperSaddleFunction (fun uStar x => theorem37ValueSupInf K uStar x) := by
  rcases
      helperForCorollary_37_1_2_closedProperRepresentative
        (K := K) hKclosed hKproper hGlobal with
    ⟨F, hF, hFproper, hKGenerated⟩
  let FStar := bifunctionInverse (section34ConcaveBifunctionAdjoint F)
  have hFStarClosed : IsClosedConvexBifunction FStar :=
    helperForCorollary_37_1_2_dualAdjointInverse_isClosedConvex
      (F := F) (hF := hF) hGlobal
  have hFStarProper : IsProperConvexBifunction FStar :=
    helperForCorollary_37_1_2_dualAdjointInverse_isProperConvex
      (F := F) (hF := hF) (hFproper := hFproper)
  have hLowerRep :
      (fun uStar x => theorem37ValueSupInf K uStar x) = convexBifunctionPairing FStar := by
    -- Corollary 37.1.2 identifies the lower conjugate with the canonical dual pairing.
    funext uStar x
    simpa [FStar, convexBifunctionClosedKernel] using
      helperForCorollary_37_1_2_lowerConjugate_eq_dualLowerKernel
        (F := F) (hF := hF) (K := K) (hK := hKGenerated) (hFStar := hFStarClosed)
        hGlobal uStar x
  have hSection34FStar := section34_theorem34_2 FStar hFStarClosed
  have hQStar := hGlobal.qualification FStar hFStarClosed
  have hKernelInOmega :
      convexBifunctionClosedKernel FStar ∈ omegaClassOfConvexBifunction FStar :=
    hSection34FStar.2.2
  have hPairingInOmega :
      convexBifunctionPairing FStar ∈ omegaClassOfConvexBifunction FStar := by
    simpa [convexBifunctionClosedKernel] using hKernelInOmega
  have hPairingClosed : IsClosedSaddleFunction (convexBifunctionPairing FStar) := by
    -- Every member of the canonical Section 34 omega-class is closed.
    exact (section34_theorem34_2_qualified FStar hFStarClosed hQStar).2.2.2.1
      (convexBifunctionPairing FStar) hPairingInOmega
  have hKernelGenerated :
      convexBifunctionClosedKernel FStar ∈
        EquivalenceClassGeneratedByConvexBifunction ⟨FStar, hFStarClosed⟩ := by
    have hEquivKernel :
        convexBifunctionClosedKernel FStar ∈
          {L | saddleEquivalent L (convexBifunctionClosedKernel FStar)} := by
      rw [← hSection34FStar.2.1]
      exact hKernelInOmega
    -- Rewrite omega-class membership into generated-class membership for the dual representative.
    simpa [EquivalenceClassGeneratedByConvexBifunction, convexBifunctionClosedKernel] using
      hEquivKernel
  have hPairingGenerated :
      convexBifunctionPairing FStar ∈
        EquivalenceClassGeneratedByConvexBifunction ⟨FStar, hFStarClosed⟩ := by
    simpa [convexBifunctionClosedKernel] using hKernelGenerated
  have hPairingProper : IsProperSaddleFunction (convexBifunctionPairing FStar) :=
    proper_convex_bifunction_has_proper_generated_saddle_functions
      FStar hFStarClosed hFStarProper (convexBifunctionPairing FStar) hPairingGenerated hQStar
  -- Replace the canonical dual pairing by the lower conjugate itself.
  exact ⟨by simpa [hLowerRep] using hPairingClosed, by simpa [hLowerRep] using hPairingProper⟩

/-- Helper for Theorem 37.6: flip the first `m` packed coordinates and keep the last `n`
coordinates fixed. -/
def helperForTheorem_37_6_flipFirstPackedBlock :
    (Fin (m + n) → ℝ) → (Fin (m + n) → ℝ) :=
  fun z =>
    Fin.append (fun i : Fin m => -z (Fin.castAdd n i))
      (fun j : Fin n => z (Fin.natAdd m j))

/-- Helper for Theorem 37.6: on a split packed point, the flip simply negates the first block. -/
lemma helperForTheorem_37_6_flipFirstPackedBlock_append
    (u : Fin m → ℝ) (v : Fin n → ℝ) :
    helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) (Fin.append u v) =
      Fin.append (-u) v := by
  -- Check the blockwise formula directly from the definition of the packed flip.
  ext i
  by_cases hi : i.1 < m
  · simp [helperForTheorem_37_6_flipFirstPackedBlock, Fin.append, Fin.addCases, hi]
  · simp [helperForTheorem_37_6_flipFirstPackedBlock, Fin.append, Fin.addCases, hi]

/-- Helper for Theorem 37.6: flipping the first packed block is an involution. -/
lemma helperForTheorem_37_6_flipFirstPackedBlock_involutive :
    Function.Involutive (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n)) := by
  intro z
  cases' hz : (Fin.appendHomeomorph (X := ℝ) m n).symm z with u v
  have hzEq : Fin.append u v = z := by
    simpa [hz] using (Fin.appendHomeomorph (X := ℝ) m n).apply_symm_apply z
  subst z
  -- Negating the first block twice returns the original packed point.
  simp [helperForTheorem_37_6_flipFirstPackedBlock_append]

/-- Helper for Theorem 37.6: the packed first-block flip distributes over subtraction. -/
lemma helperForTheorem_37_6_flipFirstPackedBlock_sub
    (x y : Fin (m + n) → ℝ) :
    helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) (x - y) =
      helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) x -
        helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) y := by
  -- The flip acts coordinatewise, so it commutes with subtraction block by block.
  ext i
  by_cases hi : i.1 < m
  · simp [helperForTheorem_37_6_flipFirstPackedBlock, Fin.append, Fin.addCases, hi,
      sub_eq_add_neg, add_comm]
  · simp [helperForTheorem_37_6_flipFirstPackedBlock, Fin.append, Fin.addCases, hi,
      sub_eq_add_neg, add_comm]

/-- Helper for Theorem 37.6: the packed first-block flip is self-adjoint for the Euclidean dot
product. -/
lemma helperForTheorem_37_6_dotProduct_flipFirstPackedBlock_left
    (x y : Fin (m + n) → ℝ) :
    dotProduct
        (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) x) y =
      dotProduct x
        (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) y) := by
  cases' hx : (Fin.appendHomeomorph (X := ℝ) m n).symm x with x₁ x₂
  cases' hy : (Fin.appendHomeomorph (X := ℝ) m n).symm y with y₁ y₂
  have hxEq : Fin.append x₁ x₂ = x := by
    simpa [hx] using (Fin.appendHomeomorph (X := ℝ) m n).apply_symm_apply x
  have hyEq : Fin.append y₁ y₂ = y := by
    simpa [hy] using (Fin.appendHomeomorph (X := ℝ) m n).apply_symm_apply y
  subst x
  subst y
  -- After splitting the packed vectors into two blocks, both sides become the same sum.
  calc
    dotProduct
        (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n)
          (Fin.append x₁ x₂))
        (Fin.append y₁ y₂) =
      dotProduct (-x₁) y₁ + dotProduct x₂ y₂ := by
        simp [helperForTheorem_37_6_flipFirstPackedBlock_append,
          helperForCorollary33_1_3_dotProduct_append]
    _ = -(dotProduct x₁ y₁) + dotProduct x₂ y₂ := by
        congr 1
        simpa [dotProduct_comm] using (dotProduct_neg y₁ x₁)
    _ = dotProduct x₁ (-y₁) + dotProduct x₂ y₂ := by
        congr 1
        simpa using (dotProduct_neg x₁ y₁).symm
    _ = dotProduct (Fin.append x₁ x₂)
          (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n)
            (Fin.append y₁ y₂)) := by
        rw [helperForTheorem_37_6_flipFirstPackedBlock_append,
          helperForCorollary33_1_3_dotProduct_append]
        have hFirst :
            (fun i => Fin.append (-y₁) y₂ (Fin.castAdd n i)) = -y₁ := by
          funext i
          simp
        have hSecond :
            (fun j => Fin.append (-y₁) y₂ (Fin.natAdd m j)) = y₂ := by
          funext j
          simp
        rw [hSecond, hFirst]

/-- Helper for Theorem 37.6: precomposing a convex graph function with the first-block flip
transports Euclidean subgradients by the same flip on both the base point and the dual vector. -/
lemma helperForTheorem_37_6_euclideanSubgradient_precomp_flipFirstPackedBlock_iff
    (h : (Fin (m + n) → ℝ) → EReal)
    (x y : Fin (m + n) → ℝ) :
    IsEuclideanSubgradientAt
        (fun z =>
          h (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) z)) x y ↔
      IsEuclideanSubgradientAt h
        (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) x)
        (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) y) := by
  rw [IsEuclideanSubgradientAt, mem_subdifferentialAt_iff]
  rw [IsEuclideanSubgradientAt, mem_subdifferentialAt_iff]
  constructor
  · intro hSub z
    have hAtFlip := hSub (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) z)
    have hAffine :
        ((((dotProductEquiv ℝ (Fin (m + n)) y)
            (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) z - x) : ℝ)) :
            EReal) =
          ((((dotProductEquiv ℝ (Fin (m + n))
              (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) y))
              (z -
                helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) x) : ℝ)) :
              EReal) := by
      have hReal :
          ((dotProductEquiv ℝ (Fin (m + n)) y)
              (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) z - x) : ℝ) =
            ((dotProductEquiv ℝ (Fin (m + n))
                (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) y))
                (z -
                  helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) x) : ℝ) := by
        rw [dotProductEquiv_apply_apply, dotProductEquiv_apply_apply]
        rw [show helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) z - x =
            helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n)
              (z - helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) x) by
              rw [helperForTheorem_37_6_flipFirstPackedBlock_sub,
                helperForTheorem_37_6_flipFirstPackedBlock_involutive (m := m) (n := n) x]]
        -- The first-block flip is self-adjoint for the packed Euclidean pairing.
        calc
          y ⬝ᵥ
              helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n)
                (z - helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) x) =
            helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n)
                (z - helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) x) ⬝ᵥ y := by
              simpa [dotProduct_comm]
          _ =
            (z - helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) x) ⬝ᵥ
              helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) y := by
              simpa using
                helperForTheorem_37_6_dotProduct_flipFirstPackedBlock_left
                  (m := m) (n := n)
                  (x := z - helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) x)
                  (y := y)
          _ =
            helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) y ⬝ᵥ
              (z - helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) x) := by
              simpa [dotProduct_comm]
      simpa using congrArg (fun t : ℝ => ((t : EReal))) hReal
    -- Evaluate at the flipped point and rewrite the affine term through the involution.
    calc
      h z = h (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n)
          (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) z)) := by
            rw [helperForTheorem_37_6_flipFirstPackedBlock_involutive (m := m) (n := n) z]
      _ ≥ h (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) x) +
            ((((dotProductEquiv ℝ (Fin (m + n)) y)
                (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) z - x) : ℝ)) :
                EReal) := hAtFlip
      _ = h (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) x) +
            ((((dotProductEquiv ℝ (Fin (m + n))
                (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) y))
                (z -
                  helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) x) : ℝ)) :
                EReal) := by rw [hAffine]
  · intro hSub z
    have hAtFlip := hSub (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) z)
    have hAffine :
        ((((dotProductEquiv ℝ (Fin (m + n))
            (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) y))
            (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) z -
              helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) x) : ℝ)) :
            EReal) =
          ((((dotProductEquiv ℝ (Fin (m + n)) y) (z - x) : ℝ)) : EReal) := by
      have hReal :
          ((dotProductEquiv ℝ (Fin (m + n))
              (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) y))
              (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) z -
                helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) x) : ℝ) =
            ((dotProductEquiv ℝ (Fin (m + n)) y) (z - x) : ℝ) := by
        rw [dotProductEquiv_apply_apply, dotProductEquiv_apply_apply]
        rw [show helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) z -
            helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) x =
              helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) (z - x) by
              rw [← helperForTheorem_37_6_flipFirstPackedBlock_sub]]
        -- Apply the same self-adjointness in reverse and then cancel the involution.
        calc
          helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) y ⬝ᵥ
              helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) (z - x) =
            helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) (z - x) ⬝ᵥ
              helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) y := by
              simpa [dotProduct_comm]
          _ =
            (z - x) ⬝ᵥ
              helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n)
                (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) y) := by
              simpa using
                helperForTheorem_37_6_dotProduct_flipFirstPackedBlock_left
                  (m := m) (n := n) (x := z - x)
                  (y := helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) y)
          _ = y ⬝ᵥ (z - x) := by
              rw [helperForTheorem_37_6_flipFirstPackedBlock_involutive (m := m) (n := n) y]
              simpa [dotProduct_comm]
      simpa using congrArg (fun t : ℝ => ((t : EReal))) hReal
    -- Apply the same involutive rewrite in the reverse direction.
    calc
      h (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) z) ≥
          h (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) x) +
            ((((dotProductEquiv ℝ (Fin (m + n))
                (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) y))
                (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) z -
                  helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) x) : ℝ)) :
                EReal) := hAtFlip
      _ = h (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) x) +
            ((((dotProductEquiv ℝ (Fin (m + n)) y) (z - x) : ℝ)) : EReal) := by rw [hAffine]

/-- Helper for Theorem 37.6: a pair in the origin fiber of the lower conjugate product
subdifferential is exactly a saddle point of the original kernel. -/
lemma helperForTheorem_37_6_origin_productSubdifferentialPair_iff_saddlePoint
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hRepresentative : Section37ClosedRepresentativeQualification K hKclosed)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    (u : Fin m → ℝ) (v : Fin n → ℝ) :
    (u, v) ∈
        productSubdifferentialAt (fun uStar x => theorem37ValueSupInf K uStar x)
          (0 : Fin m → ℝ) (0 : Fin n → ℝ) ↔
      IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K u v := by
  -- Route correction: instead of importing the later Corollary 37.5.3 theorem, rebuild its
  -- canonical lower-conjugate bridge locally from the packed graph and Fenchel-duality argument.
  rcases
      helperForCorollary_37_5_1_closedProperRepresentativeWithClosedWitness
        (K := K) hKclosed hKproper hRepresentative hGlobal with
    ⟨F, hF, hClosedF, hFproper, hKGenerated⟩
  let FStar := bifunctionInverse (section34ConcaveBifunctionAdjoint F)
  have hFStarClosed : IsClosedConvexBifunction FStar :=
    helperForCorollary_37_1_2_dualAdjointInverse_isClosedConvex
      (F := F) (hF := hF) hGlobal
  have hLowerRep :
      (fun uStar x => theorem37ValueSupInf K uStar x) = convexBifunctionPairing FStar := by
    -- Corollary 37.1.2 identifies the lower conjugate with the canonical dual pairing
    -- representative attached to the recovered convex bifunction.
    funext uStar x
    simpa [FStar, convexBifunctionClosedKernel] using
      helperForCorollary_37_1_2_lowerConjugate_eq_dualLowerKernel
        (F := F) (hF := hF) (K := K) (hK := hKGenerated) (hFStar := hFStarClosed)
        hGlobal uStar x
  have hKeq : K = convexBifunctionPairing F :=
    helperForCorollary_37_5_1_generatedRepresentative_eq_pairing
      (K := K) (hF := hF) (hGlobal.qualification F hF) (hKGenerated := hKGenerated)
  have hPairingClosed : IsClosedSaddleFunction (convexBifunctionPairing F) := by
    -- The recovered pairing representative is literally the original closed saddle-function.
    simpa [hKeq] using hKclosed
  have hPairingProper : IsProperSaddleFunction (convexBifunctionPairing F) := by
    -- The same identification transports properness with no extra work.
    simpa [hKeq] using hKproper
  have hGraphData :
      ClosedConvexFunction (graphFunctionOfBifunction F) ∧
        ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
          (graphFunctionOfBifunction F) :=
    helperForCorollary_37_5_1_graphFunction_closedProperConvex
      (hF := hF) (hClosed := hClosedF) (hFproper := hFproper)
  have hDualGraphFunctionEq :
      graphFunctionOfBifunction FStar =
        fun z =>
          fenchelConjugate (m + n) (graphFunctionOfBifunction F)
            (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) z) := by
    funext z
    cases' hz : (Fin.appendHomeomorph (X := ℝ) m n).symm z with uStar x
    have hzEq : Fin.append uStar x = z := by
      simpa [hz] using (Fin.appendHomeomorph (X := ℝ) m n).apply_symm_apply z
    subst z
    have hNegConj :
        -concaveConjugate (fun u => convexBifunctionPairing F u x) uStar =
          fenchelConjugate m (fun u => -convexBifunctionPairing F u x) (-uStar) := by
      -- Rewrite the outer concave conjugate as an ordinary Fenchel conjugate after negation.
      simpa using
        congrArg (fun h : (Fin m → ℝ) → EReal => h uStar)
          (helperForTheorem_6_30_3_neg_concaveConjugate_eq_fenchel_precomp_neg
            (g := fun u => convexBifunctionPairing F u x))
    have hNested :
        fenchelConjugate m (fun u => -convexBifunctionPairing F u x) (-uStar) =
          ⨆ u : Fin m → ℝ, ⨆ y : Fin n → ℝ,
            ((((dotProduct (Fin.append u y) (Fin.append (-uStar) x) : ℝ) : EReal) -
                graphFunctionOfBifunction F (Fin.append u y))) := by
      -- Expand the two Fenchel conjugates, move the finite first-block linear term across the
      -- inner supremum, and then recombine the two blocks into a single packed dot product.
      calc
        fenchelConjugate m (fun u => -convexBifunctionPairing F u x) (-uStar)
            = ⨆ u : Fin m → ℝ,
                ((((dotProduct u (-uStar) : ℝ) : EReal)) +
                  (⨆ y : Fin n → ℝ, (((dotProduct y x : ℝ) : EReal) - F u y))) := by
                rw [fenchelConjugate_eq_iSup]
                simp [convexBifunctionPairing, convexConjugate, fenchelConjugate_eq_iSup,
                  sub_eq_add_neg, add_assoc]
        _ = ⨆ u : Fin m → ℝ, ⨆ y : Fin n → ℝ,
              ((((dotProduct u (-uStar) : ℝ) : EReal)) +
                ((((dotProduct y x : ℝ) : EReal) - F u y))) := by
              congr with u
              simpa using
                (helperForTheorem_6_30_15_real_add_iSup
                  (c := dotProduct u (-uStar))
                  (f := fun y : Fin n → ℝ => (((dotProduct y x : ℝ) : EReal) - F u y)))
        _ = ⨆ u : Fin m → ℝ, ⨆ y : Fin n → ℝ,
              ((((dotProduct (Fin.append u y) (Fin.append (-uStar) x) : ℝ) : EReal) -
                  graphFunctionOfBifunction F (Fin.append u y))) := by
              congr with u
              congr with y
              simp [helperForCorollary33_1_3_dotProduct_append, graphFunctionOfBifunction,
                sub_eq_add_neg, EReal.coe_add]
              have hDotNeg' :
                  (((dotProduct u (fun i => -uStar i) : ℝ) : EReal)) =
                    -(((dotProduct u uStar : ℝ) : EReal)) := by
                change (((dotProduct u (-uStar) : ℝ) : EReal)) =
                  -(((dotProduct u uStar : ℝ) : EReal))
                simpa using
                  congrArg (fun r : ℝ => ((r : EReal))) (dotProduct_neg u uStar)
              rw [hDotNeg']
              ac_rfl
    have hReindex :
        (⨆ u : Fin m → ℝ, ⨆ y : Fin n → ℝ,
            ((((dotProduct (Fin.append u y) (Fin.append (-uStar) x) : ℝ) : EReal) -
                graphFunctionOfBifunction F (Fin.append u y)))) =
          ⨆ z : Fin (m + n) → ℝ,
            ((((dotProduct z (Fin.append (-uStar) x) : ℝ) : EReal) -
                graphFunctionOfBifunction F z)) := by
      -- Reindex the supremum along the coordinate splitting `ℝ^(m+n) ≃ ℝ^m × ℝ^n`.
      apply le_antisymm
      · refine iSup_le ?_
        intro u'
        refine iSup_le ?_
        intro y
        exact
          le_iSup
            (fun z : Fin (m + n) → ℝ =>
              (((dotProduct z (Fin.append (-uStar) x) : ℝ) : EReal) -
                graphFunctionOfBifunction F z))
            (Fin.append u' y)
      · refine iSup_le ?_
        intro z
        rw [← helperForLemma33_0_14_append_split_eq z]
        exact
          le_iSup_of_le (fun i => z (Fin.castAdd n i)) <|
            le_iSup_of_le (fun j => z (Fin.natAdd m j)) le_rfl
    -- After splitting the packed coordinates, the graph of `F_*` is the Fenchel conjugate of
    -- the graph of `F` evaluated at the first-block sign flip.
    calc
      graphFunctionOfBifunction FStar (Fin.append uStar x)
          = -concaveConjugate (fun u => convexBifunctionPairing F u x) uStar := by
              simp [FStar, graphFunctionOfBifunction, section34ConcaveBifunctionAdjoint,
                bifunctionInverse]
      _ = fenchelConjugate m (fun u => -convexBifunctionPairing F u x) (-uStar) := hNegConj
      _ = ⨆ u' : Fin m → ℝ, ⨆ y : Fin n → ℝ,
            ((((dotProduct (Fin.append u' y) (Fin.append (-uStar) x) : ℝ) : EReal) -
                graphFunctionOfBifunction F (Fin.append u' y))) := hNested
      _ = ⨆ z : Fin (m + n) → ℝ,
            ((((dotProduct z (Fin.append (-uStar) x) : ℝ) : EReal) -
                graphFunctionOfBifunction F z)) := hReindex
      _ = fenchelConjugate (m + n) (graphFunctionOfBifunction F) (Fin.append (-uStar) x) := by
            rw [fenchelConjugate_eq_iSup]
      _ = fenchelConjugate (m + n) (graphFunctionOfBifunction F)
            (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n)
              (Fin.append uStar x)) := by
            simp [helperForTheorem_37_6_flipFirstPackedBlock_append]
  constructor
  · intro hp
    have hLowerGraph :
        (((0 : Fin m → ℝ), (0 : Fin n → ℝ)), (u, v)) ∈
          helperForCorollary_37_5_1_productSubdifferentialGraph
            (m := m) (n := n) (convexBifunctionPairing FStar) := by
      -- Rewrite the lower conjugate to the canonical dual pairing before passing to the packed
      -- graph description.
      simpa [helperForCorollary_37_5_1_productSubdifferentialGraph, hLowerRep] using hp
    have hDualPacked :
        helperForCorollary_37_5_1_packGraphCoordinates (m := m) (n := n)
            ((((0 : Fin m → ℝ), (0 : Fin n → ℝ)), (u, v))) ∈
          helperForCorollary_37_5_1_packedSubdifferentialGraph (m := m) (n := n) FStar :=
      (helperForCorollary_37_5_1_pairingGraphPoint_iff_packedSubdifferentialGraphPoint
        (hF := hFStarClosed) (u := (0 : Fin m → ℝ)) (v := (0 : Fin n → ℝ))
        (uStar := u) (vStar := v)).1 hLowerGraph
    have hDualSubgradient :
        IsEuclideanSubgradientAt
            (graphFunctionOfBifunction FStar)
            (Fin.append (0 : Fin m → ℝ) v)
            (Fin.append (-u) (0 : Fin n → ℝ)) := by
      -- The packed graph bridge rewrites the dual origin fiber as an ordinary Euclidean
      -- subgradient statement.
      simpa [helperForCorollary_37_5_1_packGraphCoordinates,
        helperForCorollary_37_5_1_packedSubdifferentialGraph, IsEuclideanSubgradientAt] using
        hDualPacked
    have hDualAsFenchel :
        IsEuclideanSubgradientAt
            (fun z =>
              fenchelConjugate (m + n) (graphFunctionOfBifunction F)
                (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) z))
            (Fin.append (0 : Fin m → ℝ) v)
            (Fin.append (-u) (0 : Fin n → ℝ)) := by
      -- The graph of `F_*` is the Fenchel conjugate of the graph of `F`, with the first block
      -- sign-twisted exactly as in the packed product-subdifferential coordinates.
      simpa [hDualGraphFunctionEq] using hDualSubgradient
    have hFenchelSubgradientRaw :
        IsEuclideanSubgradientAt
            (fenchelConjugate (m + n) (graphFunctionOfBifunction F))
            (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n)
              (Fin.append (0 : Fin m → ℝ) v))
            (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n)
              (Fin.append (-u) (0 : Fin n → ℝ))) :=
      (helperForTheorem_37_6_euclideanSubgradient_precomp_flipFirstPackedBlock_iff
        (m := m) (n := n)
        (h := fenchelConjugate (m + n) (graphFunctionOfBifunction F))
        (x := Fin.append (0 : Fin m → ℝ) v)
        (y := Fin.append (-u) (0 : Fin n → ℝ))).1 hDualAsFenchel
    have hFenchelSubgradient :
        IsEuclideanSubgradientAt
            (fenchelConjugate (m + n) (graphFunctionOfBifunction F))
            (Fin.append (0 : Fin m → ℝ) v)
            (Fin.append u (0 : Fin n → ℝ)) := by
      -- Transport the dual graph statement through the first-block sign flip; the base point is
      -- fixed because its first block is zero, while the dual vector changes sign in that block.
      simpa [helperForTheorem_37_6_flipFirstPackedBlock_append] using hFenchelSubgradientRaw
    have hPrimalSubgradient :
        IsEuclideanSubgradientAt
            (graphFunctionOfBifunction F)
            (Fin.append u (0 : Fin n → ℝ))
            (Fin.append (0 : Fin m → ℝ) v) :=
      (euclidean_subgradient_fenchelConjugate_iff
        (f := graphFunctionOfBifunction F) hGraphData.1 hGraphData.2
        (x := Fin.append u (0 : Fin n → ℝ))
        (xStar := Fin.append (0 : Fin m → ℝ) v)).1 hFenchelSubgradient
    have hPrimalPacked :
        helperForCorollary_37_5_1_packGraphCoordinates (m := m) (n := n)
            (((u, v), ((0 : Fin m → ℝ), (0 : Fin n → ℝ)))) ∈
          helperForCorollary_37_5_1_packedSubdifferentialGraph (m := m) (n := n) F := by
      -- Convert the ordinary Euclidean subgradient of the packed graph function back to the
      -- packed graph statement used in Corollary 37.5.1.
      simpa [helperForCorollary_37_5_1_packGraphCoordinates,
        helperForCorollary_37_5_1_packedSubdifferentialGraph, IsEuclideanSubgradientAt] using
        hPrimalSubgradient
    have hPrimalGraph :
        (((u, v), ((0 : Fin m → ℝ), (0 : Fin n → ℝ))) ∈
          helperForCorollary_37_5_1_productSubdifferentialGraph
            (m := m) (n := n) (convexBifunctionPairing F)) :=
      (helperForCorollary_37_5_1_pairingGraphPoint_iff_packedSubdifferentialGraphPoint
        (hF := hF) (u := u) (v := v)
        (uStar := (0 : Fin m → ℝ)) (vStar := (0 : Fin n → ℝ))).2 hPrimalPacked
    have hPrimalMem :
        ((0 : Fin m → ℝ), (0 : Fin n → ℝ)) ∈
          productSubdifferentialAt (convexBifunctionPairing F) u v := by
      simpa [helperForCorollary_37_5_1_productSubdifferentialGraph] using hPrimalGraph
    have hSaddlePairing :
        IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ))
          (convexBifunctionPairing F) u v := by
      -- Theorem 37.4 specialized at zero tilt identifies the primal zero fiber with the
      -- saddle-point condition of the canonical pairing representative.
      have hTiltSaddle :
          IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ))
            (helperForTheorem_37_4_affineTiltKernel (convexBifunctionPairing F)
              (0 : Fin m → ℝ) (0 : Fin n → ℝ)) u v :=
        (((section37_theorem37_4 (K := convexBifunctionPairing F)
          hPairingClosed hPairingProper hGlobal).1
          u v (0 : Fin m → ℝ) (0 : Fin n → ℝ)).1 hPrimalMem)
      simpa [IsSaddlePoint, helperForTheorem_37_4_affineTiltKernel, finDot] using hTiltSaddle
    -- Replace the canonical pairing representative by the original saddle-function obtained from
    -- the same Section 34 generated class.
    have hSaddleK :
        IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K u v := by
      simpa [hKeq] using hSaddlePairing
    exact hSaddleK
  · intro hSaddle
    have hPrimalMem :
        ((0 : Fin m → ℝ), (0 : Fin n → ℝ)) ∈
          productSubdifferentialAt (convexBifunctionPairing F) u v := by
      have hSaddlePairing :
          IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ))
            (convexBifunctionPairing F) u v := by
        simpa [hKeq] using hSaddle
      -- Theorem 37.4 again converts the saddle-point condition into primal zero-fiber
      -- membership for the canonical pairing representative.
      have hTiltSaddle :
          IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ))
            (helperForTheorem_37_4_affineTiltKernel (convexBifunctionPairing F)
              (0 : Fin m → ℝ) (0 : Fin n → ℝ)) u v := by
        simpa [IsSaddlePoint, helperForTheorem_37_4_affineTiltKernel, finDot] using hSaddlePairing
      exact
        (((section37_theorem37_4 (K := convexBifunctionPairing F)
          hPairingClosed hPairingProper hGlobal).1
          u v (0 : Fin m → ℝ) (0 : Fin n → ℝ)).2 hTiltSaddle)
    have hPrimalGraph :
        (((u, v), ((0 : Fin m → ℝ), (0 : Fin n → ℝ))) ∈
          helperForCorollary_37_5_1_productSubdifferentialGraph
            (m := m) (n := n) (convexBifunctionPairing F)) := by
      simpa [helperForCorollary_37_5_1_productSubdifferentialGraph] using hPrimalMem
    have hPrimalPacked :
        helperForCorollary_37_5_1_packGraphCoordinates (m := m) (n := n)
            (((u, v), ((0 : Fin m → ℝ), (0 : Fin n → ℝ)))) ∈
          helperForCorollary_37_5_1_packedSubdifferentialGraph (m := m) (n := n) F :=
      (helperForCorollary_37_5_1_pairingGraphPoint_iff_packedSubdifferentialGraphPoint
        (hF := hF) (u := u) (v := v)
        (uStar := (0 : Fin m → ℝ)) (vStar := (0 : Fin n → ℝ))).1 hPrimalGraph
    have hPrimalSubgradient :
        IsEuclideanSubgradientAt
            (graphFunctionOfBifunction F)
            (Fin.append u (0 : Fin n → ℝ))
            (Fin.append (0 : Fin m → ℝ) v) := by
      -- Reinterpret the primal packed graph statement as an ordinary Euclidean subgradient of the
      -- packed graph function of `F`.
      simpa [helperForCorollary_37_5_1_packGraphCoordinates,
        helperForCorollary_37_5_1_packedSubdifferentialGraph, IsEuclideanSubgradientAt] using
        hPrimalPacked
    have hFenchelSubgradient :
        IsEuclideanSubgradientAt
            (fenchelConjugate (m + n) (graphFunctionOfBifunction F))
            (Fin.append (0 : Fin m → ℝ) v)
            (Fin.append u (0 : Fin n → ℝ)) :=
      (euclidean_subgradient_fenchelConjugate_iff
        (f := graphFunctionOfBifunction F) hGraphData.1 hGraphData.2
        (x := Fin.append u (0 : Fin n → ℝ))
        (xStar := Fin.append (0 : Fin m → ℝ) v)).2 hPrimalSubgradient
    have hDualAsFenchel :
        IsEuclideanSubgradientAt
            (fun z =>
              fenchelConjugate (m + n) (graphFunctionOfBifunction F)
                (helperForTheorem_37_6_flipFirstPackedBlock (m := m) (n := n) z))
            (Fin.append (0 : Fin m → ℝ) v)
            (Fin.append (-u) (0 : Fin n → ℝ)) := by
      -- Apply the same first-block sign flip in reverse.
      exact
        (helperForTheorem_37_6_euclideanSubgradient_precomp_flipFirstPackedBlock_iff
          (m := m) (n := n)
          (h := fenchelConjugate (m + n) (graphFunctionOfBifunction F))
          (x := Fin.append (0 : Fin m → ℝ) v)
          (y := Fin.append (-u) (0 : Fin n → ℝ))).2
          (by
            simpa [helperForTheorem_37_6_flipFirstPackedBlock_append]
              using hFenchelSubgradient)
    have hDualSubgradient :
        IsEuclideanSubgradientAt
            (graphFunctionOfBifunction FStar)
            (Fin.append (0 : Fin m → ℝ) v)
            (Fin.append (-u) (0 : Fin n → ℝ)) := by
      -- Rewrite the dual graph function back from the flipped Fenchel-conjugate description to
      -- the actual graph of `F_*`.
      simpa [hDualGraphFunctionEq] using hDualAsFenchel
    have hDualPacked :
        helperForCorollary_37_5_1_packGraphCoordinates (m := m) (n := n)
            ((((0 : Fin m → ℝ), (0 : Fin n → ℝ)), (u, v))) ∈
          helperForCorollary_37_5_1_packedSubdifferentialGraph (m := m) (n := n) FStar := by
      -- Repackage the ordinary dual Euclidean subgradient as the packed graph statement used by
      -- Corollary 37.5.1.
      simpa [helperForCorollary_37_5_1_packGraphCoordinates,
        helperForCorollary_37_5_1_packedSubdifferentialGraph, IsEuclideanSubgradientAt] using
        hDualSubgradient
    have hLowerGraph :
        ((((0 : Fin m → ℝ), (0 : Fin n → ℝ)), (u, v)) ∈
          helperForCorollary_37_5_1_productSubdifferentialGraph
            (m := m) (n := n) (convexBifunctionPairing FStar)) :=
      (helperForCorollary_37_5_1_pairingGraphPoint_iff_packedSubdifferentialGraphPoint
        (hF := hFStarClosed) (u := (0 : Fin m → ℝ)) (v := (0 : Fin n → ℝ))
        (uStar := u) (vStar := v)).2 hDualPacked
    -- Replace the canonical dual pairing by the lower Section 37 conjugate.
    simpa [helperForCorollary_37_5_1_productSubdifferentialGraph, hLowerRep] using hLowerGraph

/-- Helper for Theorem 37.6: if both recession-direction hypotheses from Theorem 37.3 hold, then
the origin lies in the relative-interior effective domain of the lower conjugate kernel
`(uStar, x) ↦ theorem37ValueSupInf K uStar x`. -/
lemma helperForTheorem_37_6_origin_mem_saddleKernelDomain_of_bothNoCommonRecessionConditions
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hQ : Section37Theorem37_2Qualification K)
    (hNoCommonSecond :
      ∀ w : Fin n → ℝ, w ≠ 0 →
        ∃ u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)},
          ¬ IsRecessionDirection (K u.1) w)
    (hNoCommonFirst :
      ∀ z : Fin m → ℝ, z ≠ 0 →
        ∃ v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)},
          ¬ IsRecessionDirection (fun u => -K u v.1) z) :
    ((0 : Fin m → ℝ), (0 : Fin n → ℝ)) ∈
      saddleKernelDomain (fun uStar x => theorem37ValueSupInf K uStar x) := by
  -- Route correction: the main Theorem 37.6 skeleton is still absent from this part file, so we
  -- package the dependency-closed dual-kernel-domain step here instead of inventing that theorem.
  have hFirstDual :
      (0 : Fin m → ℝ) ∈ intrinsicInterior ℝ
        (effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x)) :=
    by
      -- Condition (b) from Theorem 37.3 moves the origin into the first dual effective domain.
      exact
        helperForTheorem_37_3_origin_mem_intrinsicInterior_firstDual_of_noCommonFirstRecession
          (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ hNoCommonFirst
  have hSecondDual :
      (0 : Fin n → ℝ) ∈ intrinsicInterior ℝ
        (effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x)) :=
    by
      -- Condition (a) from Theorem 37.3 moves the origin into the second dual effective domain.
      exact
        helperForTheorem_37_3_origin_mem_intrinsicInterior_secondDual_of_noCommonSecondRecession
          (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ hNoCommonSecond
  -- The saddle-kernel domain is exactly the product of these two intrinsic interiors.
  change
    (0 : Fin m → ℝ) ∈ intrinsicInterior ℝ
        (effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x)) ∧
      (0 : Fin n → ℝ) ∈ intrinsicInterior ℝ
        (effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x))
  exact ⟨hFirstDual, hSecondDual⟩

/-- Helper for Theorem 37.6: once the lower conjugate kernel is known to be closed and proper, the
two recession-direction hypotheses force nonemptiness of the origin fiber of its product
subdifferential. -/
lemma helperForTheorem_37_6_origin_mem_productSubdifferentialDomain_of_bothNoCommonRecessionConditions
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hQ : Section37Theorem37_2Qualification K)
    (hKStarclosed : IsClosedSaddleFunction (fun uStar x => theorem37ValueSupInf K uStar x))
    (hKStarproper : IsProperSaddleFunction (fun uStar x => theorem37ValueSupInf K uStar x))
    (hNoCommonSecond :
      ∀ w : Fin n → ℝ, w ≠ 0 →
        ∃ u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)},
          ¬ IsRecessionDirection (K u.1) w)
    (hNoCommonFirst :
      ∀ z : Fin m → ℝ, z ≠ 0 →
        ∃ v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)},
          ¬ IsRecessionDirection (fun u => -K u v.1) z) :
    ((0 : Fin m → ℝ), (0 : Fin n → ℝ)) ∈
      {p : (Fin m → ℝ) × (Fin n → ℝ) |
        Set.Nonempty
          (productSubdifferentialAt (fun uStar x => theorem37ValueSupInf K uStar x) p.1 p.2)} := by
  have hOriginKernel :
      ((0 : Fin m → ℝ), (0 : Fin n → ℝ)) ∈
        saddleKernelDomain (fun uStar x => theorem37ValueSupInf K uStar x) :=
    by
      -- First place the origin in `ri (dom KStar)` using the two Theorem 37.3 hypotheses.
      exact
        helperForTheorem_37_6_origin_mem_saddleKernelDomain_of_bothNoCommonRecessionConditions
          (K := K) (hKclosed := hKclosed) (hKproper := hKproper)
          hQ
          (hNoCommonSecond := hNoCommonSecond) (hNoCommonFirst := hNoCommonFirst)
  -- Theorem 37.4 upgrades origin-membership in `ri (dom KStar)` to nonemptiness of `∂KStar(0,0)`.
  exact
    (section37_theorem37_4 (K := fun uStar x => theorem37ValueSupInf K uStar x)
      hKStarclosed hKStarproper hQ.primalGlobal).2.1 hOriginKernel

/-- Helper for Theorem 37.6: under the two recession hypotheses, the origin fiber of the lower
conjugate product subdifferential is nonempty, closed, and convex. -/
lemma helperForTheorem_37_6_origin_productSubdifferentialFiber_nonempty_closed_convex_of_bothNoCommonRecessionConditions
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hQ : Section37Theorem37_2Qualification K)
    (hKStarclosed : IsClosedSaddleFunction (fun uStar x => theorem37ValueSupInf K uStar x))
    (hKStarproper : IsProperSaddleFunction (fun uStar x => theorem37ValueSupInf K uStar x))
    (hNoCommonSecond :
      ∀ w : Fin n → ℝ, w ≠ 0 →
        ∃ u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)},
          ¬ IsRecessionDirection (K u.1) w)
    (hNoCommonFirst :
      ∀ z : Fin m → ℝ, z ≠ 0 →
        ∃ v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)},
          ¬ IsRecessionDirection (fun u => -K u v.1) z) :
    Set.Nonempty
        (productSubdifferentialAt (fun uStar x => theorem37ValueSupInf K uStar x)
          (0 : Fin m → ℝ) (0 : Fin n → ℝ)) ∧
      IsClosed
        (productSubdifferentialAt (fun uStar x => theorem37ValueSupInf K uStar x)
          (0 : Fin m → ℝ) (0 : Fin n → ℝ)) ∧
      Convex ℝ
        (productSubdifferentialAt (fun uStar x => theorem37ValueSupInf K uStar x)
          (0 : Fin m → ℝ) (0 : Fin n → ℝ)) := by
  have hNonempty :
      Set.Nonempty
        (productSubdifferentialAt (fun uStar x => theorem37ValueSupInf K uStar x)
          (0 : Fin m → ℝ) (0 : Fin n → ℝ)) := by
    -- Read origin-membership in the product-subdifferential domain as nonemptiness of the origin
    -- fiber itself.
    simpa using
      helperForTheorem_37_6_origin_mem_productSubdifferentialDomain_of_bothNoCommonRecessionConditions
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper)
        hQ
        (hKStarclosed := hKStarclosed) (hKStarproper := hKStarproper)
        (hNoCommonSecond := hNoCommonSecond) (hNoCommonFirst := hNoCommonFirst)
  have hClosedConvex :
      IsClosed
          (productSubdifferentialAt (fun uStar x => theorem37ValueSupInf K uStar x)
            (0 : Fin m → ℝ) (0 : Fin n → ℝ)) ∧
        Convex ℝ
          (productSubdifferentialAt (fun uStar x => theorem37ValueSupInf K uStar x)
            (0 : Fin m → ℝ) (0 : Fin n → ℝ)) :=
    by
      -- Closedness and convexity of the origin fiber are the Corollary 37.5.3 geometry package.
      exact
        helperForCorollary_37_5_3_origin_fiber_closed_convex
          (KStar := fun uStar x => theorem37ValueSupInf K uStar x)
  -- Package the three facts in the exact shape needed once the missing theorem skeleton is restored.
  exact ⟨hNonempty, hClosedConvex.1, hClosedConvex.2⟩

/-- Helper for Theorem 37.6: the nonempty origin fiber of the lower conjugate product
subdifferential contains an explicit pair `(u, v)`. -/
lemma helperForTheorem_37_6_exists_origin_productSubdifferentialPair_of_bothNoCommonRecessionConditions
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hQ : Section37Theorem37_2Qualification K)
    (hKStarclosed : IsClosedSaddleFunction (fun uStar x => theorem37ValueSupInf K uStar x))
    (hKStarproper : IsProperSaddleFunction (fun uStar x => theorem37ValueSupInf K uStar x))
    (hNoCommonSecond :
      ∀ w : Fin n → ℝ, w ≠ 0 →
        ∃ u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)},
          ¬ IsRecessionDirection (K u.1) w)
    (hNoCommonFirst :
      ∀ z : Fin m → ℝ, z ≠ 0 →
        ∃ v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)},
          ¬ IsRecessionDirection (fun u => -K u v.1) z) :
    ∃ u v,
      (u, v) ∈
        productSubdifferentialAt (fun uStar x => theorem37ValueSupInf K uStar x)
          (0 : Fin m → ℝ) (0 : Fin n → ℝ) := by
  -- First recover the nonemptiness statement already proved for the origin fiber.
  have hFiber :
      Set.Nonempty
        (productSubdifferentialAt (fun uStar x => theorem37ValueSupInf K uStar x)
          (0 : Fin m → ℝ) (0 : Fin n → ℝ)) := by
    exact
      (helperForTheorem_37_6_origin_productSubdifferentialFiber_nonempty_closed_convex_of_bothNoCommonRecessionConditions
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper)
        hQ
        (hKStarclosed := hKStarclosed) (hKStarproper := hKStarproper)
        (hNoCommonSecond := hNoCommonSecond) (hNoCommonFirst := hNoCommonFirst)).1
  -- Unpack a witness as the coordinate pair that will feed the later saddle-point identification.
  rcases hFiber with ⟨p, hp⟩
  exact ⟨p.1, p.2, hp⟩

/-- Theorem 37.6: a closed proper concave-convex kernel satisfying both recession hypotheses from
Theorem 37.3 has a saddle point. -/
theorem section37_theorem37_6
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hQ : Section37Theorem37_2Qualification K)
    (hRepresentative : Section37ClosedRepresentativeQualification K hKclosed)
    (hNoCommonSecond :
      ∀ w : Fin n → ℝ, w ≠ 0 →
        ∃ u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)},
          ¬ IsRecessionDirection (K u.1) w)
    (hNoCommonFirst :
      ∀ z : Fin m → ℝ, z ≠ 0 →
        ∃ v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)},
          ¬ IsRecessionDirection (fun u => -K u v.1) z) :
    ∃ u v, IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K u v := by
  have hLowerClosedProper :
      IsClosedSaddleFunction (fun uStar x => theorem37ValueSupInf K uStar x) ∧
        IsProperSaddleFunction (fun uStar x => theorem37ValueSupInf K uStar x) :=
    helperForTheorem_37_6_lowerConjugate_closed_proper
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ.primalGlobal
  rcases
      helperForTheorem_37_6_exists_origin_productSubdifferentialPair_of_bothNoCommonRecessionConditions
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper)
        hQ
        (hKStarclosed := hLowerClosedProper.1) (hKStarproper := hLowerClosedProper.2)
        (hNoCommonSecond := hNoCommonSecond) (hNoCommonFirst := hNoCommonFirst) with
    ⟨u, v, huv⟩
  -- Convert the origin-fiber witness for the lower conjugate into an actual saddle point of `K`.
  exact ⟨u, v,
    (helperForTheorem_37_6_origin_productSubdifferentialPair_iff_saddlePoint
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper)
      hRepresentative hQ.primalGlobal
      (u := u) (v := v)).1 huv⟩

end Section37
end Chap07

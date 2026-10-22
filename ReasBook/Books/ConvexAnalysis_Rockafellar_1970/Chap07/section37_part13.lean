/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section37_part11

section Chap07
section Section37

attribute [local instance] Classical.propDecidable

variable {m n : ℕ}

/-- Helper for Corollary 37.5.3: once the origin fiber of `∂KStar` is identified with the
saddle-point set of `K`, origin-membership in `dom ∂KStar` is equivalent to existence of a saddle
point of `K`. -/
lemma helperForCorollary_37_5_3_origin_domain_iff_exists_saddle_point
    {K KStar : SaddleFunction m n}
    (hOriginFiber :
      productSubdifferentialAt KStar (0 : Fin m → ℝ) (0 : Fin n → ℝ) =
        {p : (Fin m → ℝ) × (Fin n → ℝ) |
          IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K p.1 p.2}) :
    (((0 : Fin m → ℝ), (0 : Fin n → ℝ)) ∈
        {p : (Fin m → ℝ) × (Fin n → ℝ) |
          Set.Nonempty (productSubdifferentialAt KStar p.1 p.2)}) ↔
      ∃ u v, IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K u v := by
  -- Rewrite the origin-domain statement to the nonemptiness of the origin product-subdifferential.
  change Set.Nonempty (productSubdifferentialAt KStar (0 : Fin m → ℝ) (0 : Fin n → ℝ)) ↔
    ∃ u v, IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K u v
  constructor
  · rintro ⟨p, hp⟩
    -- Transport an origin-fiber witness across the computed equality with the saddle-point set.
    have hpSaddle :
        IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K p.1 p.2 := by
      simpa [hOriginFiber] using hp
    exact ⟨p.1, p.2, hpSaddle⟩
  · rintro ⟨u, v, hSaddle⟩
    -- Put the saddle-point witness back into the origin fiber of `∂KStar`.
    refine ⟨(u, v), ?_⟩
    simpa [hOriginFiber] using hSaddle

/-- Helper for Corollary 37.5.3: the `ri (dom KStar)` inclusion from Theorem 37.4 yields a saddle
point of `K` as soon as the origin fiber of `∂KStar` has been identified. -/
lemma helperForCorollary_37_5_3_origin_kernelDomain_implies_exists_saddle_point
    {K KStar : SaddleFunction m n}
    (hKStarclosed : IsClosedSaddleFunction KStar)
    (hKStarproper : IsProperSaddleFunction KStar)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    (hOriginFiber :
      productSubdifferentialAt KStar (0 : Fin m → ℝ) (0 : Fin n → ℝ) =
        {p : (Fin m → ℝ) × (Fin n → ℝ) |
          IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K p.1 p.2}) :
    ((0 : Fin m → ℝ), (0 : Fin n → ℝ)) ∈ saddleKernelDomain KStar →
      ∃ u v, IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K u v := by
  intro hOriginKernel
  have hOriginDomain :
      ((0 : Fin m → ℝ), (0 : Fin n → ℝ)) ∈
        {p : (Fin m → ℝ) × (Fin n → ℝ) |
          Set.Nonempty (productSubdifferentialAt KStar p.1 p.2)} :=
    (section37_theorem37_4 (K := KStar) hKStarclosed hKStarproper hGlobal).2.1 hOriginKernel
  -- Theorem 37.4 supplies origin-membership in `dom ∂KStar`; the computed fiber equality turns
  -- that into an actual saddle-point witness for `K`.
  exact
    (helperForCorollary_37_5_3_origin_domain_iff_exists_saddle_point
      (K := K) (KStar := KStar) hOriginFiber).1 hOriginDomain

/-- Helper for Corollary 37.5.3: flip the first `m` packed coordinates and keep the last `n`
coordinates fixed. -/
def helperForCorollary_37_5_3_flipFirstPackedBlock :
    (Fin (m + n) → ℝ) → (Fin (m + n) → ℝ) :=
  fun z =>
    Fin.append (fun i : Fin m => -z (Fin.castAdd n i))
      (fun j : Fin n => z (Fin.natAdd m j))

/-- Helper for Corollary 37.5.3: on a split packed point, the flip simply negates the first
block. -/
lemma helperForCorollary_37_5_3_flipFirstPackedBlock_append
    (u : Fin m → ℝ) (v : Fin n → ℝ) :
    helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) (Fin.append u v) =
      Fin.append (-u) v := by
  -- Check the blockwise formula directly from the definition of the packed flip.
  ext i
  by_cases hi : i.1 < m
  · simp [helperForCorollary_37_5_3_flipFirstPackedBlock, Fin.append, Fin.addCases, hi]
  · simp [helperForCorollary_37_5_3_flipFirstPackedBlock, Fin.append, Fin.addCases, hi]

/-- Helper for Corollary 37.5.3: flipping the first packed block is an involution. -/
lemma helperForCorollary_37_5_3_flipFirstPackedBlock_involutive :
    Function.Involutive (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n)) := by
  intro z
  cases' hz : (Fin.appendHomeomorph (X := ℝ) m n).symm z with u v
  have hzEq : Fin.append u v = z := by
    simpa [hz] using (Fin.appendHomeomorph (X := ℝ) m n).apply_symm_apply z
  subst z
  -- Negating the first block twice returns the original packed point.
  simp [helperForCorollary_37_5_3_flipFirstPackedBlock_append]

/-- Helper for Corollary 37.5.3: the packed first-block flip distributes over subtraction. -/
lemma helperForCorollary_37_5_3_flipFirstPackedBlock_sub
    (x y : Fin (m + n) → ℝ) :
    helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) (x - y) =
      helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) x -
        helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) y := by
  -- The flip acts coordinatewise, so it commutes with subtraction block by block.
  ext i
  by_cases hi : i.1 < m
  · simp [helperForCorollary_37_5_3_flipFirstPackedBlock, Fin.append, Fin.addCases, hi,
      sub_eq_add_neg, add_comm]
  · simp [helperForCorollary_37_5_3_flipFirstPackedBlock, Fin.append, Fin.addCases, hi,
      sub_eq_add_neg, add_comm]

/-- Helper for Corollary 37.5.3: the packed first-block flip is self-adjoint for the Euclidean
dot product. -/
lemma helperForCorollary_37_5_3_dotProduct_flipFirstPackedBlock_left
    (x y : Fin (m + n) → ℝ) :
    dotProduct
        (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) x) y =
      dotProduct x
        (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) y) := by
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
        (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n)
          (Fin.append x₁ x₂))
        (Fin.append y₁ y₂) =
      dotProduct (-x₁) y₁ + dotProduct x₂ y₂ := by
        simp [helperForCorollary_37_5_3_flipFirstPackedBlock_append,
          helperForCorollary33_1_3_dotProduct_append]
    _ = -(dotProduct x₁ y₁) + dotProduct x₂ y₂ := by
        congr 1
        simpa [dotProduct_comm] using (dotProduct_neg y₁ x₁)
    _ = dotProduct x₁ (-y₁) + dotProduct x₂ y₂ := by
        congr 1
        simpa using (dotProduct_neg x₁ y₁).symm
    _ = dotProduct (Fin.append x₁ x₂)
          (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n)
            (Fin.append y₁ y₂)) := by
        rw [helperForCorollary_37_5_3_flipFirstPackedBlock_append,
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

/-- Helper for Corollary 37.5.3: precomposing a convex graph function with the first-block flip
transports Euclidean subgradients by the same flip on both the base point and the dual vector. -/
lemma helperForCorollary_37_5_3_euclideanSubgradient_precomp_flipFirstPackedBlock_iff
    (h : (Fin (m + n) → ℝ) → EReal)
    (x y : Fin (m + n) → ℝ) :
    IsEuclideanSubgradientAt
        (fun z =>
          h (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) z)) x y ↔
      IsEuclideanSubgradientAt h
        (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) x)
        (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) y) := by
  rw [IsEuclideanSubgradientAt, mem_subdifferentialAt_iff]
  rw [IsEuclideanSubgradientAt, mem_subdifferentialAt_iff]
  constructor
  · intro hSub z
    have hAtFlip := hSub (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) z)
    have hAffine :
        ((((dotProductEquiv ℝ (Fin (m + n)) y)
            (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) z - x) : ℝ)) :
            EReal) =
          ((((dotProductEquiv ℝ (Fin (m + n))
              (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) y))
              (z -
                helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) x) : ℝ)) :
              EReal) := by
      have hReal :
          ((dotProductEquiv ℝ (Fin (m + n)) y)
              (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) z - x) : ℝ) =
            ((dotProductEquiv ℝ (Fin (m + n))
                (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) y))
                (z -
                  helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) x) : ℝ) := by
        rw [dotProductEquiv_apply_apply, dotProductEquiv_apply_apply]
        rw [show helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) z - x =
            helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n)
              (z - helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) x) by
              rw [helperForCorollary_37_5_3_flipFirstPackedBlock_sub,
                helperForCorollary_37_5_3_flipFirstPackedBlock_involutive (m := m) (n := n) x]]
        -- The first-block flip is self-adjoint for the packed Euclidean pairing.
        calc
          y ⬝ᵥ
              helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n)
                (z - helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) x) =
            helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n)
                (z - helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) x) ⬝ᵥ y := by
              simpa [dotProduct_comm]
          _ =
            (z - helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) x) ⬝ᵥ
              helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) y := by
              simpa using
                helperForCorollary_37_5_3_dotProduct_flipFirstPackedBlock_left
                  (m := m) (n := n)
                  (x := z - helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) x)
                  (y := y)
          _ =
            helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) y ⬝ᵥ
              (z - helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) x) := by
              simpa [dotProduct_comm]
      simpa using congrArg (fun t : ℝ => ((t : EReal))) hReal
    -- Evaluate at the flipped point and rewrite the affine term through the involution.
    calc
      h z = h (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n)
          (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) z)) := by
            rw [helperForCorollary_37_5_3_flipFirstPackedBlock_involutive (m := m) (n := n) z]
      _ ≥ h (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) x) +
            ((((dotProductEquiv ℝ (Fin (m + n)) y)
                (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) z - x) : ℝ)) :
                EReal) := hAtFlip
      _ = h (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) x) +
            ((((dotProductEquiv ℝ (Fin (m + n))
                (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) y))
                (z -
                  helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) x) : ℝ)) :
                EReal) := by rw [hAffine]
  · intro hSub z
    have hAtFlip := hSub (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) z)
    have hAffine :
        ((((dotProductEquiv ℝ (Fin (m + n))
            (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) y))
            (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) z -
              helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) x) : ℝ)) :
            EReal) =
          ((((dotProductEquiv ℝ (Fin (m + n)) y) (z - x) : ℝ)) : EReal) := by
      have hReal :
          ((dotProductEquiv ℝ (Fin (m + n))
              (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) y))
              (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) z -
                helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) x) : ℝ) =
            ((dotProductEquiv ℝ (Fin (m + n)) y) (z - x) : ℝ) := by
        rw [dotProductEquiv_apply_apply, dotProductEquiv_apply_apply]
        rw [show helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) z -
            helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) x =
              helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) (z - x) by
              rw [← helperForCorollary_37_5_3_flipFirstPackedBlock_sub]]
        -- Apply the same self-adjointness in reverse and then cancel the involution.
        calc
          helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) y ⬝ᵥ
              helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) (z - x) =
            helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) (z - x) ⬝ᵥ
              helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) y := by
              simpa [dotProduct_comm]
          _ =
            (z - x) ⬝ᵥ
              helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n)
                (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) y) := by
              simpa using
                helperForCorollary_37_5_3_dotProduct_flipFirstPackedBlock_left
                  (m := m) (n := n) (x := z - x)
                  (y := helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) y)
          _ = y ⬝ᵥ (z - x) := by
              rw [helperForCorollary_37_5_3_flipFirstPackedBlock_involutive (m := m) (n := n) y]
              simpa [dotProduct_comm]
      simpa using congrArg (fun t : ℝ => ((t : EReal))) hReal
    -- Apply the same involutive rewrite in the reverse direction.
    calc
      h (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) z) ≥
          h (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) x) +
            ((((dotProductEquiv ℝ (Fin (m + n))
                (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) y))
                (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) z -
                  helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) x) : ℝ)) :
                EReal) := hAtFlip
      _ = h (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) x) +
            ((((dotProductEquiv ℝ (Fin (m + n)) y) (z - x) : ℝ)) : EReal) := by rw [hAffine]

/-- Helper for Corollary 37.5.3: the only remaining primal-dual step is the canonical lower
Section 37 conjugate case, where `KStar = theorem37ValueSupInf K`. -/
lemma helperForCorollary_37_5_3_lowerConjugate_origin_productSubdifferential_eq_saddle_points
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hRepresentative : Section37ClosedRepresentativeQualification K hKclosed)
    (hGlobal : Section34Theorem34_2GlobalQualification m n) :
    productSubdifferentialAt (fun uStar x => theorem37ValueSupInf K uStar x)
        (0 : Fin m → ℝ) (0 : Fin n → ℝ) =
      {p : (Fin m → ℝ) × (Fin n → ℝ) |
        IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K p.1 p.2} := by
  -- Route correction: the transport from an arbitrary equivalent `KStar` to the lower conjugate
  -- is already handled by Corollary 37.4.1, so the unresolved work is now only the canonical
  -- lower-conjugate fiber identity.
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
    funext uStar x
    -- Corollary 37.1.2 identifies the lower conjugate with the canonical dual pairing
    -- representative attached to the recovered convex bifunction.
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
            (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) z) := by
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
        intro u
        refine iSup_le ?_
        intro y
        exact
          le_iSup
            (fun z : Fin (m + n) → ℝ =>
              (((dotProduct z (Fin.append (-uStar) x) : ℝ) : EReal) -
                graphFunctionOfBifunction F z))
            (Fin.append u y)
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
      _ = ⨆ u : Fin m → ℝ, ⨆ y : Fin n → ℝ,
            ((((dotProduct (Fin.append u y) (Fin.append (-uStar) x) : ℝ) : EReal) -
                graphFunctionOfBifunction F (Fin.append u y))) := hNested
      _ = ⨆ z : Fin (m + n) → ℝ,
            ((((dotProduct z (Fin.append (-uStar) x) : ℝ) : EReal) -
                graphFunctionOfBifunction F z)) := hReindex
      _ = fenchelConjugate (m + n) (graphFunctionOfBifunction F) (Fin.append (-uStar) x) := by
            rw [fenchelConjugate_eq_iSup]
      _ = fenchelConjugate (m + n) (graphFunctionOfBifunction F)
            (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n)
              (Fin.append uStar x)) := by
            simp [helperForCorollary_37_5_3_flipFirstPackedBlock_append]
  ext p
  rcases p with ⟨u, v⟩
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
                (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) z))
            (Fin.append (0 : Fin m → ℝ) v)
            (Fin.append (-u) (0 : Fin n → ℝ)) := by
      -- The graph of `F_*` is the Fenchel conjugate of the graph of `F`, with the first block
      -- sign-twisted exactly as in the packed product-subdifferential coordinates.
      simpa [hDualGraphFunctionEq] using hDualSubgradient
    have hFenchelSubgradientRaw :
        IsEuclideanSubgradientAt
            (fenchelConjugate (m + n) (graphFunctionOfBifunction F))
            (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n)
              (Fin.append (0 : Fin m → ℝ) v))
            (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n)
              (Fin.append (-u) (0 : Fin n → ℝ))) :=
      (helperForCorollary_37_5_3_euclideanSubgradient_precomp_flipFirstPackedBlock_iff
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
      simpa [helperForCorollary_37_5_3_flipFirstPackedBlock_append] using hFenchelSubgradientRaw
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
    simpa [Set.mem_setOf_eq] using hSaddleK
  · intro hSaddleMem
    have hSaddle :
        IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K u v := by
      simpa [Set.mem_setOf_eq] using hSaddleMem
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
                (helperForCorollary_37_5_3_flipFirstPackedBlock (m := m) (n := n) z))
            (Fin.append (0 : Fin m → ℝ) v)
            (Fin.append (-u) (0 : Fin n → ℝ)) := by
      -- Apply the same first-block sign flip in reverse.
      exact
        (helperForCorollary_37_5_3_euclideanSubgradient_precomp_flipFirstPackedBlock_iff
          (m := m) (n := n)
          (h := fenchelConjugate (m + n) (graphFunctionOfBifunction F))
          (x := Fin.append (0 : Fin m → ℝ) v)
          (y := Fin.append (-u) (0 : Fin n → ℝ))).2
          (by
            simpa [helperForCorollary_37_5_3_flipFirstPackedBlock_append]
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

/-- Corollary 37.5.3: for a closed proper saddle-function `K`, any closed proper conjugate
representative `KStar` equivalent to the lower Section 37 conjugate has origin product
subdifferential equal to the saddle-point set of `K`. -/
theorem corollary37_5_3_conjugate_origin_productSubdifferential_eq_saddle_points
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hRepresentative : Section37ClosedRepresentativeQualification K hKclosed)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    (KStar : SaddleFunction m n)
    (hKStarclosed : IsClosedSaddleFunction KStar)
    (hKStarproper : IsProperSaddleFunction KStar)
    (hKStarConj :
      EquivalentSaddleFunctions KStar (fun uStar x => theorem37ValueSupInf K uStar x)) :
    productSubdifferentialAt KStar (0 : Fin m → ℝ) (0 : Fin n → ℝ) =
      {p : (Fin m → ℝ) × (Fin n → ℝ) |
        IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K p.1 p.2} := by
  let _ := hKStarclosed
  let _ := hKStarproper
  have hCanonical :
      productSubdifferentialAt (fun uStar x => theorem37ValueSupInf K uStar x)
          (0 : Fin m → ℝ) (0 : Fin n → ℝ) =
        {p : (Fin m → ℝ) × (Fin n → ℝ) |
          IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K p.1 p.2} :=
    helperForCorollary_37_5_3_lowerConjugate_origin_productSubdifferential_eq_saddle_points
      (K := K) hKclosed hKproper hRepresentative hGlobal
  have hSubEq :
      ∀ u v,
        productSubdifferentialAt KStar u v =
          productSubdifferentialAt (fun uStar x => theorem37ValueSupInf K uStar x) u v :=
    (corollary37_4_1_equivalentSaddleFunctions_have_same_productSubdifferential
      (K := KStar) (L := fun uStar x => theorem37ValueSupInf K uStar x) hKStarConj).1
  -- Once Corollary 37.4.1 transports the product subdifferential to the lower conjugate, the
  -- theorem is exactly the canonical lower-conjugate statement.
  calc
    productSubdifferentialAt KStar (0 : Fin m → ℝ) (0 : Fin n → ℝ) =
        productSubdifferentialAt (fun uStar x => theorem37ValueSupInf K uStar x)
          (0 : Fin m → ℝ) (0 : Fin n → ℝ) := by
            simpa using hSubEq (0 : Fin m → ℝ) (0 : Fin n → ℝ)
    _ = {p : (Fin m → ℝ) × (Fin n → ℝ) |
          IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ)) K p.1 p.2} :=
      hCanonical

end Section37
end Chap07

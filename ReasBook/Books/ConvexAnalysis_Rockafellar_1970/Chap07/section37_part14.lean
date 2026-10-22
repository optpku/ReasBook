/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part20
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part23
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section37_part11

section Chap07
section Section37

attribute [local instance] Classical.propDecidable

variable {m n : ℕ}

/-- Helper for Corollary 37.5.2: the packed textbook operator
`ρ(u,v) = {(-u*, v*) | (u*, v*) ∈ ∂K(u,v)}` on `ℝ^(m+n)`. -/
def helperForCorollary_37_5_2_packedRho
    (K : SaddleFunction m n) :
    (Fin (m + n) → ℝ) → Set (Fin (m + n) → ℝ) :=
  fun x =>
    let uv := (Fin.appendHomeomorph (X := ℝ) m n).symm x
    {y |
      let yBlocks := (Fin.appendHomeomorph (X := ℝ) m n).symm y
      (-yBlocks.1, yBlocks.2) ∈ productSubdifferentialAt K uv.1 uv.2}

/-- Helper for Corollary 37.5.2: on packed graph coordinates, swap the second primal block with
the second dual block. -/
def helperForCorollary_37_5_2_swapSecondBlocks :
    ((Fin (m + n) → ℝ) × (Fin (m + n) → ℝ)) →
      ((Fin (m + n) → ℝ) × (Fin (m + n) → ℝ)) :=
  fun p =>
    let xBlocks := (Fin.appendHomeomorph (X := ℝ) m n).symm p.1
    let yBlocks := (Fin.appendHomeomorph (X := ℝ) m n).symm p.2
    (Fin.append xBlocks.1 yBlocks.2, Fin.append yBlocks.1 xBlocks.2)

/-- Helper for Corollary 37.5.2: transport a packed set-valued map by the block-swap involution
on graph coordinates. -/
def helperForCorollary_37_5_2_swapSecondBlocksTransport
    (T : (Fin (m + n) → ℝ) → Set (Fin (m + n) → ℝ)) :
    (Fin (m + n) → ℝ) → Set (Fin (m + n) → ℝ) :=
  fun x =>
    {y |
      let q := helperForCorollary_37_5_2_swapSecondBlocks (m := m) (n := n) (x, y)
      q.2 ∈ T q.1}

/-- Helper for Corollary 37.5.2: in the everywhere-differentiable case, the packed signed
gradient map is the singleton-valued realization of `ρ`. -/
noncomputable def helperForCorollary_37_5_2_packedSignedGradient
    (K : SaddleFunction m n)
    (hDiff : ∀ u v, ERealDifferentiableAt (packedSaddleKernel K) (Fin.append u v)) :
    (Fin (m + n) → ℝ) → Set (Fin (m + n) → ℝ) :=
  fun x =>
    let uv := (Fin.appendHomeomorph (X := ℝ) m n).symm x
    let grad :=
      packedSaddleKernelGradientPairAt (K := K) (u := uv.1) (v := uv.2) (hDiff uv.1 uv.2)
    {Fin.append (-grad.1) grad.2}

/-- Helper for Corollary 37.5.2: the block swap is literally involutive on packed graph
coordinates. -/
lemma helperForCorollary_37_5_2_swapSecondBlocks_involutive :
    Function.Involutive (helperForCorollary_37_5_2_swapSecondBlocks (m := m) (n := n)) := by
  rintro ⟨x, y⟩
  cases' hx : (Fin.appendHomeomorph (X := ℝ) m n).symm x with x₁ x₂
  cases' hy : (Fin.appendHomeomorph (X := ℝ) m n).symm y with y₁ y₂
  have hx' : Fin.append x₁ x₂ = x := by
    simpa [hx] using (Fin.appendHomeomorph (X := ℝ) m n).apply_symm_apply x
  have hy' : Fin.append y₁ y₂ = y := by
    simpa [hy] using (Fin.appendHomeomorph (X := ℝ) m n).apply_symm_apply y
  subst x
  subst y
  -- Applying the swap twice restores the original second blocks.
  ext <;> simp [helperForCorollary_37_5_2_swapSecondBlocks]

/-- Helper for Corollary 37.5.2: the block swap preserves the monotonicity pairing
`⟪x - y, u - v⟫`. -/
lemma helperForCorollary_37_5_2_swapSecondBlocks_preserves_pairing
    (p q : ((Fin (m + n) → ℝ) × (Fin (m + n) → ℝ))) :
    dotProduct
        ((helperForCorollary_37_5_2_swapSecondBlocks (m := m) (n := n) p).1 -
          (helperForCorollary_37_5_2_swapSecondBlocks (m := m) (n := n) q).1)
        ((helperForCorollary_37_5_2_swapSecondBlocks (m := m) (n := n) p).2 -
          (helperForCorollary_37_5_2_swapSecondBlocks (m := m) (n := n) q).2) =
      dotProduct (p.1 - q.1) (p.2 - q.2) := by
  rcases p with ⟨x, y⟩
  rcases q with ⟨x', y'⟩
  cases' hx : (Fin.appendHomeomorph (X := ℝ) m n).symm x with x₁ x₂
  cases' hy : (Fin.appendHomeomorph (X := ℝ) m n).symm y with y₁ y₂
  cases' hx' : (Fin.appendHomeomorph (X := ℝ) m n).symm x' with x₁' x₂'
  cases' hy' : (Fin.appendHomeomorph (X := ℝ) m n).symm y' with y₁' y₂'
  have hxEq : Fin.append x₁ x₂ = x := by
    simpa [hx] using (Fin.appendHomeomorph (X := ℝ) m n).apply_symm_apply x
  have hyEq : Fin.append y₁ y₂ = y := by
    simpa [hy] using (Fin.appendHomeomorph (X := ℝ) m n).apply_symm_apply y
  have hxEq' : Fin.append x₁' x₂' = x' := by
    simpa [hx'] using (Fin.appendHomeomorph (X := ℝ) m n).apply_symm_apply x'
  have hyEq' : Fin.append y₁' y₂' = y' := by
    simpa [hy'] using (Fin.appendHomeomorph (X := ℝ) m n).apply_symm_apply y'
  subst x
  subst y
  subst x'
  subst y'
  -- Split both packed pairings into their first and second coordinate blocks.
  simp [helperForCorollary_37_5_2_swapSecondBlocks,
    helperForCorollary33_1_3_dotProduct_append, dotProduct_comm,
    sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Corollary 37.5.2: the graph of `ρ` is exactly the block-swapped graph of the
ordinary packed subdifferential. -/
lemma helperForCorollary_37_5_2_packedRhoGraphPoint_iff_packedSubdifferentialGraphPoint
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsClosedConvexBifunction F)
    (hQ : Section34Theorem34_2Qualification F)
    (hFproper : IsProperConvexBifunction F)
    (hKGenerated : K ∈ EquivalenceClassGeneratedByConvexBifunction ⟨F, hF⟩)
    (u : Fin m → ℝ) (v : Fin n → ℝ) (uStar : Fin m → ℝ) (vStar : Fin n → ℝ) :
    Fin.append (-uStar) vStar ∈
        helperForCorollary_37_5_2_packedRho (m := m) (n := n) K (Fin.append u v) ↔
      helperForCorollary_37_5_1_packGraphCoordinates (m := m) (n := n)
          (((u, v), (uStar, vStar))) ∈
        helperForCorollary_37_5_1_packedSubdifferentialGraph (m := m) (n := n) F := by
  -- Unfold the textbook `ρ` fiber and then apply the Section 37.5.1 graph bridge.
  constructor
  · intro h
    have hMemRaw :
        (-fun i => -uStar i, fun i => vStar i) ∈
          productSubdifferentialAt K (fun i => u i) (fun i => v i) := by
      simpa [helperForCorollary_37_5_2_packedRho, Pi.neg_apply] using h
    have hMem'' :
        (-(-uStar), vStar) ∈ productSubdifferentialAt K u v := by
      exact hMemRaw
    have hMem : (uStar, vStar) ∈ productSubdifferentialAt K u v := by
      simpa using hMem''
    have hGraph :
        (((u, v), (uStar, vStar)) ∈
          helperForCorollary_37_5_1_productSubdifferentialGraph (m := m) (n := n) K) := by
      simpa [helperForCorollary_37_5_1_productSubdifferentialGraph] using hMem
    exact
      (helperForCorollary_37_5_1_originalGraphPoint_iff_packedSubdifferentialGraphPoint
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper)
        (hF := hF) hQ (hFproper := hFproper) (hKGenerated := hKGenerated)
        (u := u) (v := v) (uStar := uStar) (vStar := vStar)).1 hGraph
  · intro h
    have hGraph :
        (((u, v), (uStar, vStar)) ∈
          helperForCorollary_37_5_1_productSubdifferentialGraph (m := m) (n := n) K) :=
      (helperForCorollary_37_5_1_originalGraphPoint_iff_packedSubdifferentialGraphPoint
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper)
        (hF := hF) hQ (hFproper := hFproper) (hKGenerated := hKGenerated)
        (u := u) (v := v) (uStar := uStar) (vStar := vStar)).2 h
    have hMem : (uStar, vStar) ∈ productSubdifferentialAt K u v := by
      simpa [helperForCorollary_37_5_1_productSubdifferentialGraph] using hGraph
    have hMem'' :
        (-fun i => -uStar i, fun i => vStar i) ∈
          productSubdifferentialAt K (fun i => u i) (fun i => v i) := by
      change (-(-uStar), vStar) ∈ productSubdifferentialAt K u v
      simpa using hMem
    simpa [helperForCorollary_37_5_2_packedRho, Pi.neg_apply] using hMem''

/-- Helper for Corollary 37.5.2: transporting a monotone map by the block swap preserves
monotonicity. -/
lemma helperForCorollary_37_5_2_swapSecondBlocks_preserves_monotone
    (T : (Fin (m + n) → ℝ) → Set (Fin (m + n) → ℝ))
    (hT : IsMonotoneEuclideanSetValuedMap T) :
    IsMonotoneEuclideanSetValuedMap
      (helperForCorollary_37_5_2_swapSecondBlocksTransport (m := m) (n := n) T) := by
  intro x y u v hu hv
  -- Read `u` and `v` as graph points of the swapped transport and pull them back to `T`.
  have hPulled :=
    hT (show
        (helperForCorollary_37_5_2_swapSecondBlocks (m := m) (n := n) (x, u)).2 ∈
          T ((helperForCorollary_37_5_2_swapSecondBlocks (m := m) (n := n) (x, u)).1) from hu)
      (show
        (helperForCorollary_37_5_2_swapSecondBlocks (m := m) (n := n) (y, v)).2 ∈
          T ((helperForCorollary_37_5_2_swapSecondBlocks (m := m) (n := n) (y, v)).1) from hv)
  -- The algebraic swap leaves the monotonicity pairing unchanged.
  simpa [helperForCorollary_37_5_2_swapSecondBlocks_preserves_pairing (m := m) (n := n)
    (p := (x, u)) (q := (y, v))] using hPulled

/-- Helper for Corollary 37.5.2: transporting a maximal monotone map by the block swap preserves
maximal monotonicity. -/
lemma helperForCorollary_37_5_2_swapSecondBlocks_preserves_maximalMonotone
    (T : (Fin (m + n) → ℝ) → Set (Fin (m + n) → ℝ))
    (hT : IsMaximalMonotoneEuclideanSetValuedMap T) :
    IsMaximalMonotoneEuclideanSetValuedMap
      (helperForCorollary_37_5_2_swapSecondBlocksTransport (m := m) (n := n) T) := by
  rcases hT with ⟨hTmono, hTmax⟩
  constructor
  · -- Monotonicity transports directly through the pairing-preserving swap.
    exact
      helperForCorollary_37_5_2_swapSecondBlocks_preserves_monotone
        (m := m) (n := n) T hTmono
  · intro S hSmono hSubset x
    let S' :
        (Fin (m + n) → ℝ) → Set (Fin (m + n) → ℝ) :=
      helperForCorollary_37_5_2_swapSecondBlocksTransport (m := m) (n := n) S
    have hS'mono : IsMonotoneEuclideanSetValuedMap S' :=
      helperForCorollary_37_5_2_swapSecondBlocks_preserves_monotone
        (m := m) (n := n) S hSmono
    have hTS' : ∀ z : Fin (m + n) → ℝ, T z ⊆ S' z := by
      intro z u hu
      have hswap :
          helperForCorollary_37_5_2_swapSecondBlocks (m := m) (n := n)
              (helperForCorollary_37_5_2_swapSecondBlocks (m := m) (n := n) (z, u)) =
            (z, u) :=
        helperForCorollary_37_5_2_swapSecondBlocks_involutive (m := m) (n := n) (z, u)
      -- A point of `T` becomes a point of `transport T`, hence of `S`, after one swap.
      have hInTransport :
          (helperForCorollary_37_5_2_swapSecondBlocks (m := m) (n := n) (z, u)).2 ∈
            helperForCorollary_37_5_2_swapSecondBlocksTransport (m := m) (n := n) T
              ((helperForCorollary_37_5_2_swapSecondBlocks (m := m) (n := n) (z, u)).1) := by
        simpa [helperForCorollary_37_5_2_swapSecondBlocksTransport, hswap]
          using hu
      have hInS :
          (helperForCorollary_37_5_2_swapSecondBlocks (m := m) (n := n) (z, u)).2 ∈
            S ((helperForCorollary_37_5_2_swapSecondBlocks (m := m) (n := n) (z, u)).1) :=
        hSubset _ hInTransport
      -- Swap back once more to see that `u` lies in the transported enlargement.
      simpa [S', helperForCorollary_37_5_2_swapSecondBlocksTransport, hswap]
        using hInS
    have hS'LeT : ∀ z : Fin (m + n) → ℝ, S' z ⊆ T z :=
      hTmax S' hS'mono hTS'
    intro u hu
    have hswap :
        helperForCorollary_37_5_2_swapSecondBlocks (m := m) (n := n)
            (helperForCorollary_37_5_2_swapSecondBlocks (m := m) (n := n) (x, u)) =
          (x, u) :=
      helperForCorollary_37_5_2_swapSecondBlocks_involutive (m := m) (n := n) (x, u)
    -- Apply maximality to the swapped enlargement and then transport the conclusion back.
    have hInS' :
        (helperForCorollary_37_5_2_swapSecondBlocks (m := m) (n := n) (x, u)).2 ∈
          S' ((helperForCorollary_37_5_2_swapSecondBlocks (m := m) (n := n) (x, u)).1) := by
      simpa [S', helperForCorollary_37_5_2_swapSecondBlocksTransport, hswap]
        using hu
    have hInT :
        (helperForCorollary_37_5_2_swapSecondBlocks (m := m) (n := n) (x, u)).2 ∈
          T ((helperForCorollary_37_5_2_swapSecondBlocks (m := m) (n := n) (x, u)).1) :=
      hS'LeT _ hInS'
    simpa [helperForCorollary_37_5_2_swapSecondBlocksTransport] using hInT

/-- Corollary 37.5.2: if `K` is a closed proper concave-convex saddle-function, then the packed
textbook saddle-subgradient map `(u, v) ↦ {(-u*, v*) | (u*, v*) ∈ ∂K(u, v)}` is maximal
monotone. -/
theorem corollary37_5_2_saddle_subgradient_is_maximal_monotone
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hRepresentative : Section37ClosedRepresentativeQualification K hKclosed)
    (hGlobal : Section34Theorem34_2GlobalQualification m n) :
    IsMaximalMonotoneEuclideanSetValuedMap
      (helperForCorollary_37_5_2_packedRho (m := m) (n := n) K) := by
  rcases
      helperForCorollary_37_5_1_closedProperRepresentativeWithClosedWitness
        (K := K) hKclosed hKproper hRepresentative hGlobal with
    ⟨F, hF, hClosedF, hFproper, hKGenerated⟩
  have hGraphData :
      ClosedConvexFunction (graphFunctionOfBifunction F) ∧
        ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
          (graphFunctionOfBifunction F) :=
    helperForCorollary_37_5_1_graphFunction_closedProperConvex
      (hF := hF) (hClosed := hClosedF) (hFproper := hFproper)
  let T :
      (Fin (m + n) → ℝ) → Set (Fin (m + n) → ℝ) :=
    fun x => euclideanSubdifferentialAt (n := m + n) (graphFunctionOfBifunction F) x
  have hTmax : IsMaximalMonotoneEuclideanSetValuedMap T :=
    subdifferential_is_maximal_monotone
      (f := graphFunctionOfBifunction F) hGraphData.1 hGraphData.2
  have hEq :
      helperForCorollary_37_5_2_packedRho (m := m) (n := n) K =
        helperForCorollary_37_5_2_swapSecondBlocksTransport (m := m) (n := n) T := by
    ext x y
    cases' hx : (Fin.appendHomeomorph (X := ℝ) m n).symm x with u v
    cases' hy : (Fin.appendHomeomorph (X := ℝ) m n).symm y with y₁ y₂
    have hx' : x = Fin.append u v := by
      simpa [hx] using ((Fin.appendHomeomorph (X := ℝ) m n).apply_symm_apply x).symm
    have hy' : y = Fin.append y₁ y₂ := by
      simpa [hy] using ((Fin.appendHomeomorph (X := ℝ) m n).apply_symm_apply y).symm
    -- Re-express the transported graph point using the unique block decomposition of `x` and `y`.
    rw [hx', hy']
    simpa [T, helperForCorollary_37_5_2_swapSecondBlocksTransport,
      helperForCorollary_37_5_2_swapSecondBlocks, helperForCorollary_37_5_1_packGraphCoordinates]
      using
        (helperForCorollary_37_5_2_packedRhoGraphPoint_iff_packedSubdifferentialGraphPoint
          (K := K) (hKclosed := hKclosed) (hKproper := hKproper)
          (hF := hF) (hGlobal.qualification F hF) (hFproper := hFproper)
          (hKGenerated := hKGenerated)
          (u := u) (v := v) (uStar := -y₁) (vStar := y₂))
  -- Transport Corollary 31.5.2 through the corrected block swap.
  simpa [hEq] using
    helperForCorollary_37_5_2_swapSecondBlocks_preserves_maximalMonotone
      (m := m) (n := n) T hTmax

/-- Helper for Corollary 37.5.2: at a finite differentiability point, the `ρ` fiber is the
singleton determined by the signed packed gradient. -/
lemma helperForCorollary_37_5_2_singletonRho_of_differentiablePoint
    (K : SaddleFunction m n)
    (hK : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hDiff : ERealDifferentiableAt (packedSaddleKernel K) (Fin.append u v)) :
    helperForCorollary_37_5_2_packedRho (m := m) (n := n) K (Fin.append u v) =
      {Fin.append
        (-(packedSaddleKernelGradientPairAt (K := K) (u := u) (v := v) hDiff).1)
        ((packedSaddleKernelGradientPairAt (K := K) (u := u) (v := v) hDiff).2)} := by
  let grad : (Fin m → ℝ) × (Fin n → ℝ) :=
    packedSaddleKernelGradientPairAt (K := K) (u := u) (v := v) hDiff
  have hGradData := (section35_theorem35_8 (K := K) (u := u) (v := v) hK hFinite).1 hDiff
  rcases hGradData with ⟨hGradMem, hGradUnique⟩
  ext y
  constructor
  · intro hy
    cases' hyBlocks : (Fin.appendHomeomorph (X := ℝ) m n).symm y with y₁ y₂
    have hy' : y = Fin.append y₁ y₂ := by
      simpa [hyBlocks] using ((Fin.appendHomeomorph (X := ℝ) m n).apply_symm_apply y).symm
    have hyMem : (-y₁, y₂) ∈ productSubdifferentialAt K u v := by
      simpa [helperForCorollary_37_5_2_packedRho, hy'] using hy
    have hyEq : (-y₁, y₂) = grad := hGradUnique (-y₁, y₂) hyMem
    -- The unique subgradient identifies the packed `ρ` value with the signed gradient vector.
    have hyEq₁ : -y₁ = grad.1 := congrArg Prod.fst hyEq
    have hyEq₂ : y₂ = grad.2 := congrArg Prod.snd hyEq
    have hyEq₁' : y₁ = -grad.1 := by
      simpa using congrArg Neg.neg hyEq₁
    rw [hy']
    simp [grad, hyEq₁', hyEq₂]
  · intro hy
    -- The signed gradient value lies in `ρ` because the gradient pair itself lies in `∂K(u,v)`.
    have hGradRho : Fin.append (-grad.1) grad.2 ∈
        helperForCorollary_37_5_2_packedRho (m := m) (n := n) K (Fin.append u v) := by
      have hMem'' :
          (-fun i => -(grad.1 i), fun i => grad.2 i) ∈
            productSubdifferentialAt K (fun i => u i) (fun i => v i) := by
        change (-(-grad.1), grad.2) ∈ productSubdifferentialAt K u v
        simpa [grad] using hGradMem
      simpa [helperForCorollary_37_5_2_packedRho, grad, Pi.neg_apply] using hMem''
    simpa [grad] using hy ▸ hGradRho

/-- For Corollary 37.5.2: if `K` is finite and differentiable everywhere, then the packed signed
gradient map `(u, v) ↦ (-∇₁K(u, v), ∇₂K(u, v))` is maximal monotone. -/
theorem corollary37_5_2_differentiable_gradient_is_maximal_monotone
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hRepresentative : Section37ClosedRepresentativeQualification K hKclosed)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite : ∀ u v, K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hDiff : ∀ u v, ERealDifferentiableAt (packedSaddleKernel K) (Fin.append u v)) :
    IsMaximalMonotoneEuclideanSetValuedMap
      (helperForCorollary_37_5_2_packedSignedGradient (m := m) (n := n) K hDiff) := by
  have hRho :
      IsMaximalMonotoneEuclideanSetValuedMap
        (helperForCorollary_37_5_2_packedRho (m := m) (n := n) K) :=
    corollary37_5_2_saddle_subgradient_is_maximal_monotone
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper)
      hRepresentative hGlobal
  have hEq :
      helperForCorollary_37_5_2_packedRho (m := m) (n := n) K =
        helperForCorollary_37_5_2_packedSignedGradient (m := m) (n := n) K hDiff := by
    ext x y
    cases' hx : (Fin.appendHomeomorph (X := ℝ) m n).symm x with u v
    have hx' : x = Fin.append u v := by
      simpa [hx] using ((Fin.appendHomeomorph (X := ℝ) m n).apply_symm_apply x).symm
    -- Rewrite the `ρ` fiber to the singleton given by Theorem 35.8 at the unpacked point.
    rw [hx']
    simpa [helperForCorollary_37_5_2_packedSignedGradient, hx'] using
      congrArg (fun s => y ∈ s)
        (helperForCorollary_37_5_2_singletonRho_of_differentiablePoint
          (K := K) (hK := hK) (u := u) (v := v)
          (hFinite := hFinite u v) (hDiff := hDiff u v))
  simpa [hEq] using hRho

end Section37
end Chap07

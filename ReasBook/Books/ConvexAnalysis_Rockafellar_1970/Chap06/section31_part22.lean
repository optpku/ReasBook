/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part21

open scoped Topology

section Chap06
section Section31

attribute [local instance] Classical.propDecidable

/-- Helper for Theorem 31.5: a graph pair `z = x + x⋆` with `x⋆ ∈ ∂f(x)` forces simultaneous
attainment in the primal and dual quadratic Moreau envelopes. -/
lemma helperForTheorem_31_5_graphDecomposition_implies_attainers {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (z x xStar : Fin n → ℝ)
    (hMoreauIdentity :
      quadraticMoreauEnvelope (n := n) f z +
          quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) z =
        moreauQuadraticKernel (n := n) z)
    (hSum : z = x + xStar)
    (hSub :
      dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x) :
    AttainsQuadraticMoreauEnvelopeAt (n := n) f z x ∧
      AttainsQuadraticMoreauEnvelopeAt (n := n) (fenchelConjugate n f) z xStar := by
  let a : EReal := quadraticMoreauEnvelope (n := n) f z
  let b : EReal := quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) z
  let c1 : EReal := f x + moreauQuadraticKernel (n := n) (z - x)
  let c2 : EReal := fenchelConjugate n f xStar + moreauQuadraticKernel (n := n) (z - xStar)
  have hSubE : IsEuclideanSubgradientAt f x xStar := by
    simpa [IsEuclideanSubgradientAt] using hSub
  have hFYEq :
      FenchelYoungEqualityAt f x xStar := by
    exact
      ((helperForTheorem_23_5_fourWayTFAE (f := f) hf_proper x xStar).out 0 3).1 hSubE
  have hSubStar :
      IsEuclideanSubgradientAt (fenchelConjugate n f) xStar x := by
    exact
      (euclidean_subgradient_fenchelConjugate_iff
        (f := f) hf_closed hf_proper x xStar).2 hSubE
  have hfStar_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hf_proper
  have hfxFinite :
      f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) :=
    helperForTheorem_23_5_finiteAt_of_euclideanSubgradient
      (f := f) hf_proper x xStar hSubE
  have hfxStarFinite :
      fenchelConjugate n f xStar ≠ (⊤ : EReal) ∧
        fenchelConjugate n f xStar ≠ (⊥ : EReal) :=
    helperForTheorem_23_5_finiteAt_of_euclideanSubgradient
      (f := fenchelConjugate n f) hfStar_proper xStar x hSubStar
  rcases section14_eq_coe_of_lt_top (z := f x) (lt_top_iff_ne_top.2 hfxFinite.1) hfxFinite.2 with
    ⟨fx, hfx⟩
  rcases
      section14_eq_coe_of_lt_top (z := fenchelConjugate n f xStar)
        (lt_top_iff_ne_top.2 hfxStarFinite.1) hfxStarFinite.2 with
    ⟨fxStar, hfxStar⟩
  have hxsub : z - x = xStar := by
    rw [hSum]
    ext i
    simp
  have hxStarsub : z - xStar = x := by
    rw [hSum]
    ext i
    simp [add_comm]
  -- The Fenchel-Young equality together with `z = x + x⋆` identifies the candidate total value
  -- with the quadratic kernel `w z`.
  have hCandidateTotal :
      c1 + c2 = moreauQuadraticKernel (n := n) z := by
    dsimp [c1, c2]
    rw [hfx, hfxStar, hxsub, hxStarsub]
    have hQuad := helperForTheorem_31_5_moreauQuadraticKernel_add (n := n) x xStar
    have hFYEqReal : fx + fxStar = dotProduct x xStar := by
      rw [FenchelYoungEqualityAt, hfx, hfxStar] at hFYEq
      exact EReal.coe_eq_coe_iff.mp hFYEq
    calc
      (((fx : ℝ) : EReal) + moreauQuadraticKernel (n := n) xStar) +
          (((fxStar : ℝ) : EReal) + moreauQuadraticKernel (n := n) x) =
        (((fx + fxStar : ℝ) : EReal)) +
          (moreauQuadraticKernel (n := n) xStar + moreauQuadraticKernel (n := n) x) := by
            simp [add_assoc, add_left_comm, add_comm]
      _ =
          (((dotProduct x xStar : ℝ) : EReal)) +
            (moreauQuadraticKernel (n := n) x + moreauQuadraticKernel (n := n) xStar) := by
              rw [hFYEqReal]
              simp [add_assoc, add_left_comm, add_comm]
      _ = moreauQuadraticKernel (n := n) z := by
            rw [hSum, helperForTheorem_31_5_moreauQuadraticKernel_add (n := n) x xStar]
            simp [add_assoc, add_left_comm, add_comm]
  have hPrimalLe : a ≤ c1 := by
    dsimp [a, c1]
    rw [quadraticMoreauEnvelope, functionInfimumEReal]
    exact iInf_le _ x
  have hDualLe : b ≤ c2 := by
    dsimp [b, c2]
    rw [quadraticMoreauEnvelope, functionInfimumEReal]
    exact iInf_le _ xStar
  have hc1_ne_top : c1 ≠ (⊤ : EReal) := by
    dsimp [c1]
    rw [hfx]
    change (((fx + dotProduct (z - x) (z - x) / 2 : ℝ) : EReal)) ≠ (⊤ : EReal)
    exact EReal.coe_ne_top _
  have hc1_ne_bot : c1 ≠ (⊥ : EReal) := by
    dsimp [c1]
    rw [hfx]
    change (((fx + dotProduct (z - x) (z - x) / 2 : ℝ) : EReal)) ≠ (⊥ : EReal)
    exact EReal.coe_ne_bot _
  have hc2_ne_top : c2 ≠ (⊤ : EReal) := by
    dsimp [c2]
    rw [hfxStar]
    change (((fxStar + dotProduct (z - xStar) (z - xStar) / 2 : ℝ) : EReal)) ≠ (⊤ : EReal)
    exact EReal.coe_ne_top _
  have hc2_ne_bot : c2 ≠ (⊥ : EReal) := by
    dsimp [c2]
    rw [hfxStar]
    change (((fxStar + dotProduct (z - xStar) (z - xStar) / 2 : ℝ) : EReal)) ≠ (⊥ : EReal)
    exact EReal.coe_ne_bot _
  have ha_ne_top : a ≠ (⊤ : EReal) := by
    intro hTop
    rw [hTop] at hPrimalLe
    simpa [hc1_ne_top] using hPrimalLe
  have hb_ne_top : b ≠ (⊤ : EReal) := by
    intro hTop
    rw [hTop] at hDualLe
    simpa [hc2_ne_top] using hDualLe
  have ha_ne_bot : a ≠ (⊥ : EReal) := by
    intro hBot
    have hEq : (⊥ : EReal) = moreauQuadraticKernel (n := n) z := by
      simpa [a, b, hBot, hb_ne_top] using hMoreauIdentity
    simp [moreauQuadraticKernel] at hEq
  have hb_ne_bot : b ≠ (⊥ : EReal) := by
    intro hBot
    have hEq : (⊥ : EReal) = moreauQuadraticKernel (n := n) z := by
      simpa [a, b, hBot, ha_ne_top, add_comm] using hMoreauIdentity
    simp [moreauQuadraticKernel] at hEq
  rcases section14_eq_coe_of_lt_top (z := a) (lt_top_iff_ne_top.2 ha_ne_top) ha_ne_bot with
    ⟨ra, hra⟩
  rcases section14_eq_coe_of_lt_top (z := b) (lt_top_iff_ne_top.2 hb_ne_top) hb_ne_bot with
    ⟨rb, hrb⟩
  have hPrimalLeReal : ra ≤ fx + dotProduct (z - x) (z - x) / 2 := by
    have hLeE :
        (((ra : ℝ) : EReal)) ≤
          (((fx + dotProduct (z - x) (z - x) / 2 : ℝ) : EReal)) := by
      simpa [a, c1, hra, hfx, moreauQuadraticKernel] using hPrimalLe
    exact EReal.coe_le_coe_iff.mp hLeE
  have hDualLeReal : rb ≤ fxStar + dotProduct (z - xStar) (z - xStar) / 2 := by
    have hLeE :
        (((rb : ℝ) : EReal)) ≤
          (((fxStar + dotProduct (z - xStar) (z - xStar) / 2 : ℝ) : EReal)) := by
      simpa [b, c2, hrb, hfxStar, moreauQuadraticKernel] using hDualLe
    exact EReal.coe_le_coe_iff.mp hLeE
  have hMoreauReal :
      ra + rb = dotProduct z z / 2 := by
    have hEqE :
        ((((ra + rb : ℝ) : EReal))) = (((dotProduct z z / 2 : ℝ) : EReal)) := by
      simpa [a, b, hra, hrb, moreauQuadraticKernel] using hMoreauIdentity
    exact EReal.coe_eq_coe_iff.mp hEqE
  have hCandidateTotalReal :
      (fx + dotProduct (z - x) (z - x) / 2) +
          (fxStar + dotProduct (z - xStar) (z - xStar) / 2) =
        dotProduct z z / 2 := by
    have hEqE :
        ((((fx + dotProduct (z - x) (z - x) / 2 +
            (fxStar + dotProduct (z - xStar) (z - xStar) / 2) : ℝ) : EReal))) =
          (((dotProduct z z / 2 : ℝ) : EReal)) := by
      simpa [c1, c2, hfx, hfxStar, moreauQuadraticKernel, add_assoc, add_left_comm, add_comm]
        using hCandidateTotal
    exact EReal.coe_eq_coe_iff.mp hEqE
  have hPrimalEqReal :
      ra = fx + dotProduct (z - x) (z - x) / 2 := by
    linarith [hPrimalLeReal, hDualLeReal, hMoreauReal, hCandidateTotalReal]
  have hDualEqReal :
      rb = fxStar + dotProduct (z - xStar) (z - xStar) / 2 := by
    linarith [hPrimalLeReal, hDualLeReal, hMoreauReal, hCandidateTotalReal]
  have hPrimalEq :
      a = c1 := by
    have hEqE :
        (((ra : ℝ) : EReal)) =
          (((fx + dotProduct (z - x) (z - x) / 2 : ℝ) : EReal)) := by
      exact_mod_cast hPrimalEqReal
    simpa [a, c1, hra, hfx, moreauQuadraticKernel] using hEqE
  have hDualEq :
      b = c2 := by
    have hEqE :
        (((rb : ℝ) : EReal)) =
          (((fxStar + dotProduct (z - xStar) (z - xStar) / 2 : ℝ) : EReal)) := by
      exact_mod_cast hDualEqReal
    simpa [b, c2, hrb, hfxStar, moreauQuadraticKernel] using hEqE
  exact ⟨by simpa [AttainsQuadraticMoreauEnvelopeAt] using hPrimalEq,
    by simpa [AttainsQuadraticMoreauEnvelopeAt] using hDualEq⟩

/-- Helper for Theorem 31.5: the quadratic kernel is Fenchel self-conjugate. -/
lemma helperForTheorem_31_5_fenchelConjugate_moreauQuadraticKernel {n : ℕ} :
    fenchelConjugate n (moreauQuadraticKernel (n := n)) = moreauQuadraticKernel (n := n) := by
  -- Rewrite to the standard quadratic and apply its self-conjugacy theorem.
  simpa [helperForTheorem_31_5_moreauQuadraticKernel_eq_quadraticHalfInner] using
    (fenchelConjugate_quadraticHalfInner n)

/-- Helper for Theorem 31.5: every quadratic Moreau envelope is convex. -/
lemma helperForTheorem_31_5_convex_quadraticMoreauEnvelope {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    ConvexFunction (quadraticMoreauEnvelope (n := n) f) := by
  -- The envelope is the infimal convolution of two proper convex functions.
  rw [helperForTheorem_31_5_quadraticMoreauEnvelope_eq_infimalConvolution]
  have hconv :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (infimalConvolution f (moreauQuadraticKernel (n := n))) :=
    convexFunctionOn_infimalConvolution_of_proper
      (f := f) (g := moreauQuadraticKernel (n := n)) hf_proper
      (helperForTheorem_31_5_properConvex_moreauQuadraticKernel (n := n))
  simpa [ConvexFunction] using hconv

/-- Helper for Theorem 31.5: the quadratic kernel has its own argument as a Euclidean
subgradient. -/
lemma helperForTheorem_31_5_self_mem_subdifferential_moreauQuadraticKernel {n : ℕ}
    (x : Fin n → ℝ) :
    dotProductEquiv ℝ (Fin n) x ∈ subdifferentialAt (moreauQuadraticKernel (n := n)) x := by
  change IsSubgradientAt (moreauQuadraticKernel (n := n)) x (dotProductEquiv ℝ (Fin n) x)
  intro y
  -- Expand `w y` at `x + (y - x)` and keep only the affine part supported by the nonnegative
  -- quadratic remainder.
  have hExpand :
      moreauQuadraticKernel (n := n) y =
        moreauQuadraticKernel (n := n) x +
          ((dotProduct x (y - x) : ℝ) : EReal) +
            moreauQuadraticKernel (n := n) (y - x) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (helperForTheorem_31_5_moreauQuadraticKernel_add (n := n) x (y - x))
  calc
    moreauQuadraticKernel (n := n) y =
      moreauQuadraticKernel (n := n) x +
        ((dotProduct x (y - x) : ℝ) : EReal) +
          moreauQuadraticKernel (n := n) (y - x) := hExpand
    _ ≥ moreauQuadraticKernel (n := n) x +
        ((dotProductEquiv ℝ (Fin n) x (y - x) : ℝ) : EReal) := by
          have hstep :
              moreauQuadraticKernel (n := n) x +
                  ((dotProduct x (y - x) : ℝ) : EReal) ≤
                moreauQuadraticKernel (n := n) x +
                  ((dotProduct x (y - x) : ℝ) : EReal) +
                    moreauQuadraticKernel (n := n) (y - x) :=
            le_add_of_nonneg_right
              (helperForTheorem_31_5_moreauQuadraticKernel_nonneg (n := n) (y - x))
          simpa [dotProductEquiv_apply_apply] using hstep

/-- Helper for Theorem 31.5: the quadratic kernel has a unique Euclidean subgradient at each
point. -/
lemma helperForTheorem_31_5_eq_of_mem_subdifferential_moreauQuadraticKernel {n : ℕ}
    (x v : Fin n → ℝ)
    (hv : dotProductEquiv ℝ (Fin n) v ∈ subdifferentialAt (moreauQuadraticKernel (n := n)) x) :
    v = x := by
  change IsSubgradientAt (moreauQuadraticKernel (n := n)) x (dotProductEquiv ℝ (Fin n) v) at hv
  have hvAtV :
      moreauQuadraticKernel (n := n) v ≥
        moreauQuadraticKernel (n := n) x +
          ((dotProduct v (v - x) : ℝ) : EReal) := hv v
  -- Rewriting the quadratic inequality at `z = v` forces the squared norm of `v - x` to vanish.
  have hreal :
      dotProduct v v / 2 ≥ dotProduct x x / 2 + dotProduct v (v - x) := by
    unfold moreauQuadraticKernel at hvAtV
    exact_mod_cast hvAtV
  have hExpand :
      dotProduct v v / 2 =
        dotProduct x x / 2 + dotProduct x (v - x) +
          dotProduct (v - x) (v - x) / 2 := by
    have hcross : (∑ i, x i * v i) = ∑ i, v i * x i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      ring
    simp [dotProduct, sub_eq_add_neg, Finset.sum_add_distrib, mul_add, add_mul]
    rw [hcross]
    ring_nf
  have hInner :
      dotProduct v (v - x) =
        dotProduct x (v - x) + dotProduct (v - x) (v - x) := by
    have hcross : (∑ i, x i * v i) = ∑ i, v i * x i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      ring
    simp [dotProduct, sub_eq_add_neg, Finset.sum_add_distrib, mul_add, add_mul]
    rw [hcross]
    ring_nf
  have hsq_le_zero :
      dotProduct (v - x) (v - x) ≤ 0 := by
    rw [hExpand, hInner] at hreal
    nlinarith
  have hsq_zero :
      dotProduct (v - x) (v - x) = 0 := by
    linarith [dotProduct_self_nonneg (v := v - x), hsq_le_zero]
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp hsq_zero)

/-- Helper for Theorem 31.5: a graph pair gives the corresponding primal-envelope Euclidean
subgradient. -/
lemma helperForTheorem_31_5_primalEnvelope_subgradient_of_attainerGraph {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (z x xStar : Fin n → ℝ)
    (hPrimalAttain : AttainsQuadraticMoreauEnvelopeAt (n := n) f z x)
    (hSum : z = x + xStar)
    (hSub : dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x) :
    IsSubgradientAt (quadraticMoreauEnvelope (n := n) f) z (dotProductEquiv ℝ (Fin n) xStar) := by
  change IsSubgradientAt (quadraticMoreauEnvelope (n := n) f) z
    (dotProductEquiv ℝ (Fin n) xStar)
  intro y
  have hzEq :
      quadraticMoreauEnvelope (n := n) f z =
        f x + moreauQuadraticKernel (n := n) xStar := by
    simpa [AttainsQuadraticMoreauEnvelopeAt, hSum] using hPrimalAttain
  rw [hzEq, quadraticMoreauEnvelope, functionInfimumEReal]
  refine le_iInf ?_
  intro u
  have hSubAtU :
      f x + ((dotProduct xStar (u - x) : ℝ) : EReal) ≤ f u := by
    change IsSubgradientAt f x (dotProductEquiv ℝ (Fin n) xStar) at hSub
    simpa [IsSubgradientAt, dotProductEquiv_apply_apply] using hSub u
  have hKernelAtYU :
      moreauQuadraticKernel (n := n) xStar +
          ((dotProduct xStar ((y - u) - xStar) : ℝ) : EReal) ≤
        moreauQuadraticKernel (n := n) (y - u) := by
    have hKernelSub :=
      helperForTheorem_31_5_self_mem_subdifferential_moreauQuadraticKernel (n := n) xStar
    change IsSubgradientAt (moreauQuadraticKernel (n := n)) xStar
      (dotProductEquiv ℝ (Fin n) xStar) at hKernelSub
    simpa [IsSubgradientAt, dotProductEquiv_apply_apply] using hKernelSub (y - u)
  have hInner :
      ((dotProduct xStar (u - x) : ℝ) : EReal) +
          ((dotProduct xStar ((y - u) - xStar) : ℝ) : EReal) =
        ((dotProduct xStar (y - z) : ℝ) : EReal) := by
    have hInnerReal :
        dotProduct xStar (u - x) + dotProduct xStar ((y - u) - xStar) =
          dotProduct xStar (y - z) := by
      rw [hSum]
      simp [dotProduct, sub_eq_add_neg, Finset.sum_add_distrib, mul_add, add_mul]
      ring_nf
    exact_mod_cast hInnerReal
  have hAdd := add_le_add hSubAtU hKernelAtYU
  calc
    f x + moreauQuadraticKernel (n := n) xStar +
        ((dotProductEquiv ℝ (Fin n) xStar (y - z) : ℝ) : EReal)
      =
        (f x + ((dotProduct xStar (u - x) : ℝ) : EReal)) +
          (moreauQuadraticKernel (n := n) xStar +
            ((dotProduct xStar ((y - u) - xStar) : ℝ) : EReal)) := by
            rw [dotProductEquiv_apply_apply, ← hInner]
            simp [add_assoc, add_left_comm, add_comm]
    _ ≤ f u + moreauQuadraticKernel (n := n) (y - u) := by
          simpa [add_assoc, add_left_comm, add_comm] using hAdd

/-- Helper for Theorem 31.5: the dual envelope witness is the primal-envelope witness applied to
`f⋆`. -/
lemma helperForTheorem_31_5_dualEnvelope_subgradient_of_attainerGraph {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (z x xStar : Fin n → ℝ)
    (hDualAttain :
      AttainsQuadraticMoreauEnvelopeAt (n := n) (fenchelConjugate n f) z xStar)
    (hSum : z = x + xStar)
    (hSub : dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x) :
    IsSubgradientAt
      (quadraticMoreauEnvelope (n := n) (fenchelConjugate n f)) z
      (dotProductEquiv ℝ (Fin n) x) := by
  have hSubStar :
      dotProductEquiv ℝ (Fin n) x ∈ subdifferentialAt (fenchelConjugate n f) xStar := by
    have hSubE : IsEuclideanSubgradientAt f x xStar := by
      simpa [IsEuclideanSubgradientAt] using hSub
    have hSubStarE : IsEuclideanSubgradientAt (fenchelConjugate n f) xStar x :=
      (euclidean_subgradient_fenchelConjugate_iff
        (f := f) hf_closed hf_proper x xStar).2 hSubE
    simpa [IsEuclideanSubgradientAt] using hSubStarE
  -- Reuse the primal-envelope proof on `f⋆`, with the graph pair read as `z = x⋆ + x`.
  have hSum' : z = xStar + x := by simpa [add_comm] using hSum
  simpa [add_comm] using
    (helperForTheorem_31_5_primalEnvelope_subgradient_of_attainerGraph
      (f := fenchelConjugate n f) (z := z) (x := xStar) (xStar := x)
      hDualAttain hSum' hSubStar)

-- Proof sketch: apply Theorem 31.1 to the convex pair formed by `f` and the translated
-- quadratic kernel. Since the Fenchel conjugate of `w` is again `w`, the dual problem has the
-- same quadratic form with `f⋆`. Strict convexity of `w` gives unique primal and dual minimizers,
-- Fenchel-Young equality yields `z = x + xStar` and `xStar ∈ ∂ f(x)`, and differentiability of
-- the envelopes identifies those minimizers with the corresponding `erealGradientAt` values.
/-- Theorem 31.5 (Moreau): let `f : ℝ^n → ℝ ∪ {+∞}` be closed proper convex and let
`w(z) = |z|^2 / 2`, formalized here as `moreauQuadraticKernel`. Then for every `z ∈ ℝ^n`,
`(f □ w)(z) + (f⋆ □ w)(z) = w(z)`, where `f □ w` and `f⋆ □ w` are formalized by
`quadraticMoreauEnvelope f` and `quadraticMoreauEnvelope (fenchelConjugate n f)`. Both infima
are finite and uniquely attained. The unique primal-dual minimizer pair `(x, xStar)` is exactly
the unique pair satisfying `z = x + xStar` and `xStar ∈ ∂ f(x)`. Moreover, the two envelopes are
differentiable at `z`, and that same unique pair is given by
`x = ∇(f⋆ □ w)(z)` and `xStar = ∇(f □ w)(z)`, represented here by `erealGradientAt` applied to
the corresponding differentiability witnesses. -/
theorem moreau_decomposition_theorem {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    ∀ z : Fin n → ℝ,
      let primal := quadraticMoreauEnvelope (n := n) f z
      let dual := quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) z
      primal + dual = moreauQuadraticKernel z ∧
        IsFiniteEReal primal ∧
        IsFiniteEReal dual ∧
        (∃! x : Fin n → ℝ, AttainsQuadraticMoreauEnvelopeAt (n := n) f z x) ∧
        (∃! xStar : Fin n → ℝ,
          AttainsQuadraticMoreauEnvelopeAt (n := n) (fenchelConjugate n f) z xStar) ∧
        (∀ x xStar : Fin n → ℝ,
          (AttainsQuadraticMoreauEnvelopeAt (n := n) f z x ∧
              AttainsQuadraticMoreauEnvelopeAt
                (n := n) (fenchelConjugate n f) z xStar) ↔
            (z = x + xStar ∧
              dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x)) ∧
        (∃ hDiffPrimal : ERealDifferentiableAt (quadraticMoreauEnvelope (n := n) f) z,
          ∃ hDiffDual :
            ERealDifferentiableAt
              (quadraticMoreauEnvelope (n := n) (fenchelConjugate n f)) z,
            ∀ x xStar : Fin n → ℝ,
              AttainsQuadraticMoreauEnvelopeAt (n := n) f z x ∧
                  AttainsQuadraticMoreauEnvelopeAt
                    (n := n) (fenchelConjugate n f) z xStar →
                x = erealGradientAt hDiffDual ∧
                  xStar = erealGradientAt hDiffPrimal) := by
  intro z
  dsimp
  let g : (Fin n → ℝ) → EReal := fun x => -moreauQuadraticKernel (n := n) (z - x)
  -- Recast Moreau's theorem as Fenchel duality for the pair `(f, g)`.
  have hg_proper :
      ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g := by
    -- The translated negative quadratic is the proper concave datum required by Theorem 31.1.
    simpa [g] using
      helperForTheorem_31_5_properConcave_negTranslatedQuadratic (n := n) z
  have hg_conj :
      ∀ xStar : Fin n → ℝ,
        concaveFenchelConjugate g xStar =
          moreauQuadraticKernel (n := n) z - moreauQuadraticKernel (n := n) (z - xStar) := by
    -- This is the key algebraic bridge between Fenchel duality and Moreau's identity.
    intro xStar
    simpa [g] using
      helperForTheorem_31_5_concaveConjugate_negTranslatedQuadratic (n := n) z xStar
  have hWitnesses :
      (∃ x0,
        x0 ∈ euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) ∧
        (∃ xStar0,
          xStar0 ∈ euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))) := by
    -- Properness supplies the relative-interior witnesses promised by Corollary 7.3.1.
    exact helperForTheorem_31_5_relativeInteriorWitnesses (n := n) f hf_proper
  have hWitnessA :
      FenchelConditionA (n := n) f g := by
    -- The quadratic datum has full domain, so any relative-interior point of `dom f` witnesses `(a)`.
    rcases hWitnesses.1 with ⟨x0, hx0riF⟩
    have hx0riG :
        x0 ∈ euclideanRelativeInterior_fin n (concaveEffectiveDomain g) := by
      have hdomG :
          concaveEffectiveDomain g = Set.univ := by
        ext x
        simp [g, concaveEffectiveDomain, effectiveDomain_eq, moreauQuadraticKernel]
      rw [hdomG]
      exact helperForTheorem_31_5_mem_euclideanRelativeInterior_univ (n := n) x0
    exact ⟨x0, hx0riF, hx0riG⟩
  have hFenchelA :
      fenchelPrimalInfimum f g = fenchelDualSupremum (n := n) f g ∧
        ∃ xStar : Fin n → ℝ, fenchelDualSupremum (n := n) f g = fenchelDualObjective (n := n) f g xStar :=
    (fenchel_duality_theorem (n := n) f g hf_proper hg_proper).1 hWitnessA
  have hConditionB :
      FenchelConditionB (n := n) f g := by
    -- The negated translated quadratic also satisfies condition `(b)`.
    simpa [g] using
      helperForTheorem_31_5_conditionB_negTranslatedQuadratic
        (n := n) f hf_closed hf_proper z
  have hFenchelB :
      fenchelPrimalInfimum f g = fenchelDualSupremum (n := n) f g ∧
        ∃ x : Fin n → ℝ, fenchelPrimalInfimum f g = commonBookEffectiveDomainDifference f g x :=
    (fenchel_duality_theorem (n := n) f g hf_proper hg_proper).2.1 hConditionB
  have hFinite :
      IsFiniteEReal (fenchelPrimalInfimum f g) ∧
        IsFiniteEReal (fenchelDualSupremum (n := n) f g) :=
    (fenchel_duality_theorem (n := n) f g hf_proper hg_proper).2.2.1
      ⟨hWitnessA, hConditionB⟩
  rcases
      (helperForTheorem_31_5_fenchelObjects_rewrite_as_moreau
        (n := n) f hf_proper z) with
    ⟨hCommon, hPrimal, hDualObj, hDualSup⟩
  have hPrimalAttainer :
      ∃ x : Fin n → ℝ, AttainsQuadraticMoreauEnvelopeAt (n := n) f z x := by
    rcases hFenchelB.2 with ⟨x, hx⟩
    -- The primal attainment clause of Theorem 31.1 is now the Moreau-attainment predicate.
    refine ⟨x, ?_⟩
    have hx' : quadraticMoreauEnvelope (n := n) f z = commonBookEffectiveDomainDifference f g x := by
      simpa [g, hPrimal] using hx
    calc
      quadraticMoreauEnvelope (n := n) f z = commonBookEffectiveDomainDifference f g x := hx'
      _ = f x + moreauQuadraticKernel (n := n) (z - x) := by
            simpa [g, hCommon]
  have hDualObjectiveWitness :
      ∃ xStar : Fin n → ℝ,
        fenchelDualSupremum (n := n) f g =
          moreauQuadraticKernel (n := n) z -
            (fenchelConjugate n f xStar + moreauQuadraticKernel (n := n) (z - xStar)) := by
    rcases hFenchelA.2 with ⟨xStar, hxStar⟩
    -- The dual attainment clause is recorded in the exact displayed Moreau form.
    refine ⟨xStar, ?_⟩
    calc
      fenchelDualSupremum (n := n) f g = fenchelDualObjective (n := n) f g xStar := hxStar
      _ = moreauQuadraticKernel (n := n) z -
            (fenchelConjugate n f xStar + moreauQuadraticKernel (n := n) (z - xStar)) :=
          hDualObj xStar
  have hPrimalFinite : IsFiniteEReal (quadraticMoreauEnvelope (n := n) f z) := by
    -- The Fenchel primal value is already known to be finite, and it is exactly the primal Moreau envelope.
    rw [← hPrimal]
    exact hFinite.1
  have hDualFinite :
      IsFiniteEReal (quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) z) := by
    -- Compare the dual Moreau envelope with the finite Fenchel dual value through the translated quadratic identity.
    constructor
    · intro hDualTop
      have hSupBot : fenchelDualSupremum (n := n) f g = (⊥ : EReal) := by
        simpa [hDualTop] using hDualSup
      exact hFinite.2.2 hSupBot
    · intro hDualBot
      have hSupTop : fenchelDualSupremum (n := n) f g = (⊤ : EReal) := by
        simpa [hDualBot] using hDualSup
      exact hFinite.2.1 hSupTop
  have hMoreauIdentity :
      quadraticMoreauEnvelope (n := n) f z +
          quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) z =
        moreauQuadraticKernel (n := n) z := by
    -- Add the finite dual envelope to both sides of the Fenchel equality rewritten in Moreau form.
    have hFenchelEq :
        quadraticMoreauEnvelope (n := n) f z =
          moreauQuadraticKernel (n := n) z -
            quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) z := by
      calc
        quadraticMoreauEnvelope (n := n) f z = fenchelPrimalInfimum f g := by
          symm
          exact hPrimal
        _ = fenchelDualSupremum (n := n) f g := hFenchelA.1
        _ = moreauQuadraticKernel (n := n) z -
              quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) z := hDualSup
    have hDual_ne_top :
        quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) z ≠ (⊤ : EReal) :=
      hDualFinite.1
    have hDual_ne_bot :
        quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) z ≠ (⊥ : EReal) :=
      hDualFinite.2
    have hAdded :=
      congrArg
        (fun t : EReal =>
          t + quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) z)
        hFenchelEq
    calc
      quadraticMoreauEnvelope (n := n) f z +
          quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) z =
        moreauQuadraticKernel (n := n) z +
          (quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) z +
            -quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) z) := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, hDual_ne_top, hDual_ne_bot]
            using hAdded
      _ = moreauQuadraticKernel (n := n) z + 0 := by
            have hCancel :
                quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) z +
                    -quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) z =
                  0 := by
              simpa [sub_eq_add_neg] using
                EReal.sub_self hDual_ne_top hDual_ne_bot
            rw [hCancel]
      _ = moreauQuadraticKernel (n := n) z := by
            simp
  have hDualAttainer :
      ∃ xStar : Fin n → ℝ,
        AttainsQuadraticMoreauEnvelopeAt (n := n) (fenchelConjugate n f) z xStar := by
    rcases hDualObjectiveWitness with ⟨xStar, hxStar⟩
    refine ⟨xStar, ?_⟩
    -- Compare the witness value with the dual Moreau envelope by cancelling the common finite quadratic term.
    have hSubEq :
        moreauQuadraticKernel (n := n) z -
            quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) z =
          moreauQuadraticKernel (n := n) z -
            (fenchelConjugate n f xStar + moreauQuadraticKernel (n := n) (z - xStar)) := by
      calc
        moreauQuadraticKernel (n := n) z -
            quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) z =
          fenchelDualSupremum (n := n) f g := by
            symm
            exact hDualSup
        _ = moreauQuadraticKernel (n := n) z -
            (fenchelConjugate n f xStar + moreauQuadraticKernel (n := n) (z - xStar)) := hxStar
    have hCancelled :=
      congrArg
        (fun t : EReal => t - moreauQuadraticKernel (n := n) z)
        hSubEq
    have hAttain :
        quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) z =
          fenchelConjugate n f xStar + moreauQuadraticKernel (n := n) (z - xStar) := by
      exact helperForTheorem_31_5_cancel_sub_eq_of_moreauKernel (z := z) hSubEq
    simpa [AttainsQuadraticMoreauEnvelopeAt] using hAttain
  -- Route correction: the previous proof attempt tried to obtain the entire Moreau package from
  -- Theorem 31.1 alone. The stable route is to use Theorem 31.1 only for the displayed equality,
  -- finiteness, and one primal/dual witness, and then finish by the textbook subdifferential route.
  have hRemaining :
      (∃! x : Fin n → ℝ, AttainsQuadraticMoreauEnvelopeAt (n := n) f z x) ∧
        (∃! xStar : Fin n → ℝ,
          AttainsQuadraticMoreauEnvelopeAt (n := n) (fenchelConjugate n f) z xStar) ∧
        (∀ x xStar : Fin n → ℝ,
          (AttainsQuadraticMoreauEnvelopeAt (n := n) f z x ∧
              AttainsQuadraticMoreauEnvelopeAt
                (n := n) (fenchelConjugate n f) z xStar) ↔
            (z = x + xStar ∧
              dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x)) ∧
        (∃ hDiffPrimal : ERealDifferentiableAt (quadraticMoreauEnvelope (n := n) f) z,
          ∃ hDiffDual :
            ERealDifferentiableAt
              (quadraticMoreauEnvelope (n := n) (fenchelConjugate n f)) z,
            ∀ x xStar : Fin n → ℝ,
              AttainsQuadraticMoreauEnvelopeAt (n := n) f z x ∧
                  AttainsQuadraticMoreauEnvelopeAt
                    (n := n) (fenchelConjugate n f) z xStar →
                x = erealGradientAt hDiffDual ∧
                  xStar = erealGradientAt hDiffPrimal) := by
    rcases hPrimalAttainer with ⟨x0, hx0⟩
    rcases hDualAttainer with ⟨xStar0, hxStar0⟩
    have hIff :
        ∀ x xStar : Fin n → ℝ,
          (AttainsQuadraticMoreauEnvelopeAt (n := n) f z x ∧
              AttainsQuadraticMoreauEnvelopeAt
                (n := n) (fenchelConjugate n f) z xStar) ↔
            (z = x + xStar ∧
              dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x) := by
      intro x xStar
      constructor
      · rintro ⟨hx, hxStar⟩
        exact
          helperForTheorem_31_5_attainers_imply_graphDecomposition
            (f := f) hf_proper z x xStar hMoreauIdentity hx hxStar
      · rintro ⟨hSum, hSub⟩
        exact
          helperForTheorem_31_5_graphDecomposition_implies_attainers
            (f := f) hf_closed hf_proper z x xStar hMoreauIdentity hSum hSub
    have hPrimalUnique :
        ∃! x : Fin n → ℝ, AttainsQuadraticMoreauEnvelopeAt (n := n) f z x := by
      refine ⟨x0, hx0, ?_⟩
      intro x hx
      have hGraph0 := (hIff x0 xStar0).1 ⟨hx0, hxStar0⟩
      have hGraph := (hIff x xStar0).1 ⟨hx, hxStar0⟩
      calc
        x = z - xStar0 := by
              rw [hGraph.1]
              ext i
              simp
        _ = x0 := by
              rw [hGraph0.1]
              ext i
              simp
    have hDualUnique :
        ∃! xStar : Fin n → ℝ,
          AttainsQuadraticMoreauEnvelopeAt (n := n) (fenchelConjugate n f) z xStar := by
      refine ⟨xStar0, hxStar0, ?_⟩
      intro xStar hxStar
      have hGraph0 := (hIff x0 xStar0).1 ⟨hx0, hxStar0⟩
      have hGraph := (hIff x0 xStar).1 ⟨hx0, hxStar⟩
      calc
        xStar = z - x0 := by
                  rw [show z - x0 = xStar by
                        rw [hGraph.1]
                        ext i
                        simp]
        _ = xStar0 := by
                  rw [show z - x0 = xStar0 by
                        rw [hGraph0.1]
                        ext i
                        simp]
    have hGraph0 :
        z = x0 + xStar0 ∧
          dotProductEquiv ℝ (Fin n) xStar0 ∈ subdifferentialAt f x0 :=
      (hIff x0 xStar0).1 ⟨hx0, hxStar0⟩
    have hConvPrimal :
        ConvexFunction (quadraticMoreauEnvelope (n := n) f) :=
      helperForTheorem_31_5_convex_quadraticMoreauEnvelope (n := n) f hf_proper
    have hfStar_proper :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
      proper_fenchelConjugate_of_proper (n := n) (f := f) hf_proper
    have hConvDual :
        ConvexFunction (quadraticMoreauEnvelope (n := n) (fenchelConjugate n f)) :=
      helperForTheorem_31_5_convex_quadraticMoreauEnvelope (n := n) (fenchelConjugate n f)
        hfStar_proper
    have hPrimalSub :
        IsSubgradientAt (quadraticMoreauEnvelope (n := n) f) z
          (dotProductEquiv ℝ (Fin n) xStar0) := by
      -- Turn the unique graph pair `(x0, xStar0)` into the corresponding primal-envelope
      -- subgradient.
      exact
        helperForTheorem_31_5_primalEnvelope_subgradient_of_attainerGraph
          (f := f) (z := z) (x := x0) (xStar := xStar0) hx0 hGraph0.1 hGraph0.2
    have hDualSub :
        IsSubgradientAt (quadraticMoreauEnvelope (n := n) (fenchelConjugate n f)) z
          (dotProductEquiv ℝ (Fin n) x0) := by
      -- The same graph pair also gives the dual-envelope subgradient through conjugacy.
      exact
        helperForTheorem_31_5_dualEnvelope_subgradient_of_attainerGraph
          (f := f) hf_closed hf_proper (z := z) (x := x0) (xStar := xStar0) hxStar0
          hGraph0.1 hGraph0.2
    have hGraphSubE0 : IsEuclideanSubgradientAt f x0 xStar0 := by
      simpa [IsEuclideanSubgradientAt] using hGraph0.2
    have hSubStarE0 : IsEuclideanSubgradientAt (fenchelConjugate n f) xStar0 x0 :=
      (euclidean_subgradient_fenchelConjugate_iff
        (f := f) hf_closed hf_proper x0 xStar0).2 hGraphSubE0
    have hfx0Finite :
        f x0 ≠ (⊤ : EReal) ∧ f x0 ≠ (⊥ : EReal) :=
      helperForTheorem_23_5_finiteAt_of_euclideanSubgradient
        (f := f) hf_proper x0 xStar0 hGraphSubE0
    have hfxStar0Finite :
        fenchelConjugate n f xStar0 ≠ (⊤ : EReal) ∧
          fenchelConjugate n f xStar0 ≠ (⊥ : EReal) :=
      helperForTheorem_23_5_finiteAt_of_euclideanSubgradient
        (f := fenchelConjugate n f) hfStar_proper xStar0 x0 hSubStarE0
    rcases
        section14_eq_coe_of_lt_top (z := f x0) (lt_top_iff_ne_top.2 hfx0Finite.1) hfx0Finite.2 with
      ⟨fx0, hfx0⟩
    rcases
        section14_eq_coe_of_lt_top (z := fenchelConjugate n f xStar0)
          (lt_top_iff_ne_top.2 hfxStar0Finite.1) hfxStar0Finite.2 with
      ⟨fxStar0, hfxStar0⟩
    have hPrimalSub_unique :
        ∀ v : Fin n → ℝ,
          IsSubgradientAt (quadraticMoreauEnvelope (n := n) f) z
              (dotProductEquiv ℝ (Fin n) v) →
            v = xStar0 := by
      intro v hv
      let y : Fin n → ℝ := x0 + v
      have hUpper :
          quadraticMoreauEnvelope (n := n) f y ≤
            f x0 + moreauQuadraticKernel (n := n) v := by
        rw [quadraticMoreauEnvelope, functionInfimumEReal]
        simpa [y] using
          (iInf_le (fun u : Fin n → ℝ => f u + moreauQuadraticKernel (n := n) (y - u)) x0)
      have hLower :
          quadraticMoreauEnvelope (n := n) f z +
              ((dotProduct v (y - z) : ℝ) : EReal) ≤
            quadraticMoreauEnvelope (n := n) f y := by
        simpa [IsSubgradientAt, dotProductEquiv_apply_apply] using hv y
      have hz0 :
          quadraticMoreauEnvelope (n := n) f z =
            f x0 + moreauQuadraticKernel (n := n) xStar0 := by
        simpa [AttainsQuadraticMoreauEnvelopeAt, hGraph0.1] using hx0
      have hySub :
          y - z = v - xStar0 := by
        rw [hGraph0.1]
        ext i
        simp [y, add_assoc, add_left_comm, add_comm]
      have hCompare :
          f x0 + moreauQuadraticKernel (n := n) xStar0 +
              ((dotProduct v (v - xStar0) : ℝ) : EReal) ≤
            f x0 + moreauQuadraticKernel (n := n) v := by
        calc
          f x0 + moreauQuadraticKernel (n := n) xStar0 +
              ((dotProduct v (v - xStar0) : ℝ) : EReal)
            = quadraticMoreauEnvelope (n := n) f z +
                ((dotProduct v (y - z) : ℝ) : EReal) := by
                  simp [hz0, hySub, add_assoc, add_left_comm, add_comm]
          _ ≤ quadraticMoreauEnvelope (n := n) f y := hLower
          _ ≤ f x0 + moreauQuadraticKernel (n := n) v := hUpper
      have hCompareReal :
          fx0 + dotProduct xStar0 xStar0 / 2 + dotProduct v (v - xStar0) ≤
            fx0 + dotProduct v v / 2 := by
        rw [hfx0] at hCompare
        unfold moreauQuadraticKernel at hCompare
        exact_mod_cast hCompare
      have hExpand :
          dotProduct v v / 2 =
            dotProduct xStar0 xStar0 / 2 + dotProduct xStar0 (v - xStar0) +
              dotProduct (v - xStar0) (v - xStar0) / 2 := by
        have hcross : (∑ i, xStar0 i * v i) = ∑ i, v i * xStar0 i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
        simp [dotProduct, sub_eq_add_neg, Finset.sum_add_distrib, mul_add, add_mul]
        rw [hcross]
        ring_nf
      have hInner :
          dotProduct v (v - xStar0) =
            dotProduct xStar0 (v - xStar0) + dotProduct (v - xStar0) (v - xStar0) := by
        have hcross : (∑ i, xStar0 i * v i) = ∑ i, v i * xStar0 i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
        simp [dotProduct, sub_eq_add_neg, Finset.sum_add_distrib, mul_add, add_mul]
        rw [hcross]
        ring_nf
      have hsq_le_zero :
          dotProduct (v - xStar0) (v - xStar0) ≤ 0 := by
        rw [hExpand, hInner] at hCompareReal
        nlinarith
      have hsq_zero :
          dotProduct (v - xStar0) (v - xStar0) = 0 := by
        linarith [dotProduct_self_nonneg (v := v - xStar0), hsq_le_zero]
      exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp hsq_zero)
    have hDualSub_unique :
        ∀ u : Fin n → ℝ,
          IsSubgradientAt (quadraticMoreauEnvelope (n := n) (fenchelConjugate n f)) z
              (dotProductEquiv ℝ (Fin n) u) →
            u = x0 := by
      intro u hu
      let y : Fin n → ℝ := xStar0 + u
      have hUpper :
          quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) y ≤
            fenchelConjugate n f xStar0 + moreauQuadraticKernel (n := n) u := by
        rw [quadraticMoreauEnvelope, functionInfimumEReal]
        simpa [y] using
          (iInf_le
            (fun v : Fin n → ℝ => fenchelConjugate n f v + moreauQuadraticKernel (n := n) (y - v))
            xStar0)
      have hLower :
          quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) z +
              ((dotProduct u (y - z) : ℝ) : EReal) ≤
            quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) y := by
        simpa [IsSubgradientAt, dotProductEquiv_apply_apply] using hu y
      have hz0 :
          quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) z =
            fenchelConjugate n f xStar0 + moreauQuadraticKernel (n := n) x0 := by
        simpa [AttainsQuadraticMoreauEnvelopeAt, hGraph0.1, add_comm] using hxStar0
      have hySub :
          y - z = u - x0 := by
        rw [hGraph0.1]
        ext i
        simp [y, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        ring
      have hCompare :
          fenchelConjugate n f xStar0 + moreauQuadraticKernel (n := n) x0 +
              ((dotProduct u (u - x0) : ℝ) : EReal) ≤
            fenchelConjugate n f xStar0 + moreauQuadraticKernel (n := n) u := by
        calc
          fenchelConjugate n f xStar0 + moreauQuadraticKernel (n := n) x0 +
              ((dotProduct u (u - x0) : ℝ) : EReal)
            = quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) z +
                ((dotProduct u (y - z) : ℝ) : EReal) := by
                  simp [hz0, hySub, add_assoc, add_left_comm, add_comm]
          _ ≤ quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) y := hLower
          _ ≤ fenchelConjugate n f xStar0 + moreauQuadraticKernel (n := n) u := hUpper
      have hCompareReal :
          fxStar0 + dotProduct x0 x0 / 2 + dotProduct u (u - x0) ≤
            fxStar0 + dotProduct u u / 2 := by
        rw [hfxStar0] at hCompare
        unfold moreauQuadraticKernel at hCompare
        exact_mod_cast hCompare
      have hExpand :
          dotProduct u u / 2 =
            dotProduct x0 x0 / 2 + dotProduct x0 (u - x0) +
              dotProduct (u - x0) (u - x0) / 2 := by
        have hcross : (∑ i, x0 i * u i) = ∑ i, u i * x0 i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
        simp [dotProduct, sub_eq_add_neg, Finset.sum_add_distrib, mul_add, add_mul]
        rw [hcross]
        ring_nf
      have hInner :
          dotProduct u (u - x0) =
            dotProduct x0 (u - x0) + dotProduct (u - x0) (u - x0) := by
        have hcross : (∑ i, x0 i * u i) = ∑ i, u i * x0 i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
        simp [dotProduct, sub_eq_add_neg, Finset.sum_add_distrib, mul_add, add_mul]
        rw [hcross]
        ring_nf
      have hsq_le_zero :
          dotProduct (u - x0) (u - x0) ≤ 0 := by
        rw [hExpand, hInner] at hCompareReal
        nlinarith
      have hsq_zero :
          dotProduct (u - x0) (u - x0) = 0 := by
        linarith [dotProduct_self_nonneg (v := u - x0), hsq_le_zero]
      exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp hsq_zero)
    have hPrimalUniqueSubgradient :
        ∃! g : Fin n → ℝ,
          IsSubgradientAt (quadraticMoreauEnvelope (n := n) f) z
            (dotProductEquiv ℝ (Fin n) g) := by
      refine ⟨xStar0, hPrimalSub, ?_⟩
      intro g hg
      exact hPrimalSub_unique g hg
    have hDualUniqueSubgradient :
        ∃! g : Fin n → ℝ,
          IsSubgradientAt (quadraticMoreauEnvelope (n := n) (fenchelConjugate n f)) z
            (dotProductEquiv ℝ (Fin n) g) := by
      refine ⟨x0, hDualSub, ?_⟩
      intro g hg
      exact hDualSub_unique g hg
    have hDiffPrimal :
        ERealDifferentiableAt (quadraticMoreauEnvelope (n := n) f) z :=
      (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
        (quadraticMoreauEnvelope (n := n) f) hConvPrimal z hPrimalFinite).2
        hPrimalUniqueSubgradient
    have hDiffDual :
        ERealDifferentiableAt (quadraticMoreauEnvelope (n := n) (fenchelConjugate n f)) z :=
      (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
        (quadraticMoreauEnvelope (n := n) (fenchelConjugate n f)) hConvDual z hDualFinite).2
        hDualUniqueSubgradient
    have hGradPrimal :
        xStar0 = erealGradientAt hDiffPrimal := by
      exact
        (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
          (quadraticMoreauEnvelope (n := n) f) hConvPrimal z hPrimalFinite).1 hDiffPrimal
          |>.2.2 xStar0 hPrimalSub
    have hGradDual :
        x0 = erealGradientAt hDiffDual := by
      exact
        (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
          (quadraticMoreauEnvelope (n := n) (fenchelConjugate n f)) hConvDual z hDualFinite).1
          hDiffDual |>.2.2 x0 hDualSub
    have hPrimalUniqueData := hPrimalUnique
    have hDualUniqueData := hDualUnique
    rcases hPrimalUniqueData with ⟨xPrimal, hxPrimal, hxPrimalUnique⟩
    rcases hDualUniqueData with ⟨xDual, hxDual, hxDualUnique⟩
    -- The singleton subgradient fibers now upgrade to differentiability, and the gradients are
    -- exactly the unique primal-dual attainers.
    refine ⟨hPrimalUnique, hDualUnique, hIff, ⟨hDiffPrimal, hDiffDual, ?_⟩⟩
    intro x xStar hAttains
    have hxEqWitness : x = xPrimal := hxPrimalUnique x hAttains.1
    have hx0EqWitness : x0 = xPrimal := hxPrimalUnique x0 hx0
    have hxEq : x = x0 := by rw [hxEqWitness, ← hx0EqWitness]
    have hxStarEqWitness : xStar = xDual := hxDualUnique xStar hAttains.2
    have hxStar0EqWitness : xStar0 = xDual := hxDualUnique xStar0 hxStar0
    have hxStarEq : xStar = xStar0 := by rw [hxStarEqWitness, ← hxStar0EqWitness]
    exact ⟨by simpa [hxEq] using hGradDual, by simpa [hxStarEq] using hGradPrimal⟩
  refine ⟨hMoreauIdentity, hPrimalFinite, hDualFinite, hRemaining.1, hRemaining.2.1,
    hRemaining.2.2.1, hRemaining.2.2.2⟩

-- Proof sketch: specialize Theorem 31.5 and keep only the clause asserting that the quadratic
-- Moreau envelope of `f` has a minimizer at every `z`.

end Section31
end Chap06

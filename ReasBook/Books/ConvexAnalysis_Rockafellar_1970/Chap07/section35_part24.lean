/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section35_part23

section Chap07
section Section35

attribute [local instance] Classical.propDecidable
open scoped Pointwise
open scoped Topology

/-- Helper for Theorem 35.9: the packed gradient pair varies continuously on the
differentiability locus because nearby saddle subgradients stay close to the singleton base
subgradient. -/
lemma helperForTheorem_35_9_gradientPair_continuousOn_E
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hK : IsRealConcaveConvexOn C D K) :
    let E : Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
      {p | p ∈ C ×ˢ D ∧ DifferentiableAt ℝ (packedRealSaddleKernel K) (Fin.append p.1 p.2)}
    Continuous (fun p : {p // p ∈ E} => packedRealSaddleKernelGradientPair K p.1.1 p.1.2) := by
  intro E
  rw [continuous_iff_continuousAt]
  intro p
  rcases p with ⟨⟨u, v⟩, hpE⟩
  rcases hpE with ⟨huv, hdiff⟩
  have hu : u ∈ C := huv.1
  have hv : v ∈ D := huv.2
  let grad : (Fin m → ℝ) × (Fin n → ℝ) := packedRealSaddleKernelGradientPair K u v
  have hBaseSingleton :
      realSaddleSubdifferentialOn C D K u v = {grad} := by
    -- Identify the base saddle subgradient with the packed Fréchet gradient pair.
    simpa [grad] using
      helperForTheorem_35_9_realSaddleSubdifferential_eq_singleton_of_mem_E
        (C := C) (D := D) (K := K) hC_open hD_open hC_conv hD_conv hK hu hv hdiff
  refine Metric.continuousAt_iff.2 ?_
  intro ε hε
  let η : ℝ := ε / 2
  have hηpos : 0 < η := by
    dsimp [η]
    linarith
  rcases
      helperForTheorem_35_8_nearbyRealSubgradient_close_to_singleton
        (C := C) (D := D) (Kloc := K) (u := u) (v := v)
        (uStar := grad.1) (vStar := grad.2)
        hC_open hu hC_conv hD_open hv hD_conv hK hBaseSingleton η hηpos with
    ⟨δ0, hδ0pos, hNear⟩
  let A : ℝ := ((m + n + 1 : ℕ) : ℝ)
  let δ : ℝ := δ0 / Real.sqrt A
  have hApos : 0 < A := by
    dsimp [A]
    exact_mod_cast (Nat.succ_pos (m + n))
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact div_pos hδ0pos (Real.sqrt_pos.2 hApos)
  have hδnonneg : 0 ≤ δ := le_of_lt hδpos
  have hδIneq : ((m + n : ℕ) : ℝ) * δ ^ (2 : ℕ) ≤ δ0 ^ (2 : ℕ) := by
    have hratio : ((m + n : ℕ) : ℝ) / A ≤ (1 : ℝ) := by
      have hle : ((m + n : ℕ) : ℝ) ≤ A := by
        dsimp [A]
        exact_mod_cast (Nat.le_succ (m + n))
      exact (div_le_one hApos).2 hle
    have hδ0sq : 0 ≤ δ0 ^ (2 : ℕ) := by
      nlinarith
    have hδsq : δ ^ (2 : ℕ) = (δ0 ^ (2 : ℕ)) / A := by
      dsimp [δ]
      have hsqrtSq : (Real.sqrt A) ^ (2 : ℕ) = A := by
        simpa [pow_two] using Real.sq_sqrt (le_of_lt hApos)
      simpa [div_pow, hsqrtSq]
    calc
      ((m + n : ℕ) : ℝ) * δ ^ (2 : ℕ) =
          ((m + n : ℕ) : ℝ) * ((δ0 ^ (2 : ℕ)) / A) := by
            simp [hδsq]
      _ = (δ0 ^ (2 : ℕ)) * (((m + n : ℕ) : ℝ) / A) := by
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ ≤ (δ0 ^ (2 : ℕ)) * 1 := by
            exact mul_le_mul_of_nonneg_left hratio hδ0sq
      _ = δ0 ^ (2 : ℕ) := by simp
  refine ⟨δ, hδpos, ?_⟩
  intro q hqdist
  rcases q with ⟨⟨x, y⟩, hqE⟩
  rcases hqE with ⟨hxy, hqdiff⟩
  have hx : x ∈ C := hxy.1
  have hy : y ∈ D := hxy.2
  have hqdistBase : dist ((x, y) : (Fin m → ℝ) × (Fin n → ℝ)) (u, v) < δ := by
    simpa [δ] using hqdist
  rw [Prod.dist_eq, max_lt_iff] at hqdistBase
  have hxNorm : ‖x - u‖ ≤ δ := by
    exact le_of_lt (by simpa [dist_eq_norm] using hqdistBase.1)
  have hyNorm : ‖y - v‖ ≤ δ := by
    exact le_of_lt (by simpa [dist_eq_norm] using hqdistBase.2)
  have hxySplit :
      ((x - u), (y - v)) ∈ splitEuclideanClosedBall (m := m) (n := n) δ0 := by
    -- Shrink the subtype metric ball so that nearby points also satisfy the split-ball
    -- hypothesis needed by Corollary 35.7.1.
    exact
      helperForTheorem_35_7_splitBall_combine_errors
        (m := m) (n := n) (ε := δ0) (δ := δ) hδnonneg hδIneq hxNorm hyNorm
  have hNearSingleton :
      realSaddleSubdifferentialOn C D K x y = {packedRealSaddleKernelGradientPair K x y} := by
    -- Every nearby point in `E` has the same singleton-saddle-subgradient description.
    exact
      helperForTheorem_35_9_realSaddleSubdifferential_eq_singleton_of_mem_E
        (C := C) (D := D) (K := K) hC_open hD_open hC_conv hD_conv hK hx hy hqdiff
  have hNearMem :
      packedRealSaddleKernelGradientPair K x y ∈ realSaddleSubdifferentialOn C D K x y := by
    simpa [hNearSingleton]
  have hGradSplit :
      (((packedRealSaddleKernelGradientPair K x y).1 - grad.1),
          ((packedRealSaddleKernelGradientPair K x y).2 - grad.2)) ∈
        splitEuclideanClosedBall (m := m) (n := n) η := by
    exact hNear x hx y hy hxySplit hNearMem
  have hGradNorms :
      ‖(packedRealSaddleKernelGradientPair K x y).1 - grad.1‖ ≤ η ∧
        ‖(packedRealSaddleKernelGradientPair K x y).2 - grad.2‖ ≤ η :=
    helperForCorollary_35_7_1_coordinateNormBounds_of_mem_splitBall
      (m := m) (n := n) (r := η) (le_of_lt hηpos) hGradSplit
  have hηlt : η < ε := by
    dsimp [η]
    linarith
  have hGradDist :
      dist (packedRealSaddleKernelGradientPair K x y) grad < ε := by
    rw [Prod.dist_eq, max_lt_iff]
    constructor
    · exact (lt_of_le_of_lt (by simpa [dist_eq_norm] using hGradNorms.1) hηlt)
    · exact (lt_of_le_of_lt (by simpa [dist_eq_norm] using hGradNorms.2) hηlt)
  simpa [grad] using hGradDist

-- Proof sketch: apply the one-variable convex differentiability theorem to the convex slices
-- `v ↦ K(u, v)` and to the convex functions `u ↦ -K(u, v)`. The packed-coordinate formulation
-- turns these slice results into dense differentiability and a null exceptional set for the full
-- saddle kernel, while Corollary 35.7.1 gives the continuity needed to identify the split
-- Fréchet derivative as a continuous gradient mapping on the differentiability set.
/-- Theorem 35.9: let `C × D` be an open convex set in `ℝ^m × ℝ^n`, and let `K` be a
concave-convex real-valued function on `C × D`. If `E` is the subset of `C × D` where `K` is
differentiable, then `E` is dense in `C × D`, the complement `(C × D) \ E` has Lebesgue measure
zero, and the gradient mapping is continuous on `E`. The differentiability and gradient are
expressed below via the packed map `z ↦ K(z₁, z₂)` on `ℝ^(m+n)`, which is equivalent to
differentiability of `K` on the product space. -/
theorem section35_theorem35_9
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hK : IsRealConcaveConvexOn C D K) :
    let E : Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
      {p | p ∈ C ×ˢ D ∧ DifferentiableAt ℝ (packedRealSaddleKernel K) (Fin.append p.1 p.2)}
    C ×ˢ D ⊆ closure E ∧
      MeasureTheory.volume ((C ×ˢ D) \ E) = 0 ∧
      Continuous (fun p : {p // p ∈ E} => packedRealSaddleKernelGradientPair K p.1.1 p.1.2) :=
  by
  intro E
  have hEsub : E ⊆ C ×ˢ D := by
    -- Membership in the differentiability locus remembers membership in the open rectangle.
    intro p hp
    exact hp.1
  have hNull : MeasureTheory.volume ((C ×ˢ D) \ E) = 0 := by
    -- Route correction: instead of introducing a separate packed-coordinate/Fubini development,
    -- use Theorem 35.1 to obtain local Lipschitz control on closed bounded product neighborhoods
    -- and then apply the finite-dimensional Rademacher theorem on a countable ball cover of
    -- `C ×ˢ D`.
    let centers : Nat → ((Fin m → ℝ) × (Fin n → ℝ)) :=
      TopologicalSpace.denseSeq ((Fin m → ℝ) × (Fin n → ℝ))
    let A : Nat × Nat → Set ((Fin m → ℝ) × (Fin n → ℝ)) := fun p =>
      let c := centers p.1
      let r : ℝ := 1 / (p.2 + 1 : ℝ)
      if Metric.closedBall c (2 * r) ⊆ C ×ˢ D then Metric.ball c r else ∅
    have hOpenProd : IsOpen (C ×ˢ D) := hC_open.prod hD_open
    have hCover : C ×ˢ D ⊆ ⋃ p : Nat × Nat, A p := by
      intro x hxCD
      rcases Metric.mem_nhds_iff.mp (hOpenProd.mem_nhds hxCD) with ⟨R, hRpos, hBallSub⟩
      obtain ⟨m0, hm0⟩ := exists_nat_one_div_lt (show 0 < R / 4 by linarith)
      have hr0 : 0 < (1 / (m0 + 1 : ℝ)) := by positivity
      obtain ⟨k, hk⟩ :=
        (TopologicalSpace.denseRange_denseSeq
          (α := (Fin m → ℝ) × (Fin n → ℝ))).exists_dist_lt
            (x := x) (ε := 1 / (m0 + 1 : ℝ)) hr0
      let c : (Fin m → ℝ) × (Fin n → ℝ) := centers k
      let r : ℝ := 1 / (m0 + 1 : ℝ)
      have hxBall : x ∈ Metric.ball c r := by
        simpa [Metric.mem_ball, c, r, dist_comm] using hk
      have hClosedSub : Metric.closedBall c (2 * r) ⊆ C ×ˢ D := by
        intro z hz
        have hzx : dist z x < R := by
          have hzc : dist z c ≤ 2 * r := by
            simpa [c, r] using hz
          have hcx : dist c x < r := by
            simpa [c, r, dist_comm] using hk
          have : dist z x ≤ dist z c + dist c x := dist_triangle _ _ _
          linarith
        exact hBallSub hzx
      refine Set.mem_iUnion.2 ⟨(k, m0), ?_⟩
      have hClosedSub' : Metric.closedBall (centers k) (2 * (1 / (m0 + 1 : ℝ))) ⊆ C ×ˢ D := by
        simpa [c, r] using hClosedSub
      have hxBall' : x ∈ Metric.ball (centers k) (1 / (m0 + 1 : ℝ)) := by
        simpa [c, r] using hxBall
      dsimp [A]
      rw [if_pos hClosedSub']
      exact hxBall'
    have hSubset :
        (C ×ˢ D) \ E ⊆ ⋃ p : Nat × Nat, A p \ E := by
      intro x hx
      rcases Set.mem_iUnion.1 (hCover hx.1) with ⟨p, hpA⟩
      exact Set.mem_iUnion.2 ⟨p, ⟨hpA, hx.2⟩⟩
    have hNullA :
        ∀ p : Nat × Nat, MeasureTheory.volume (A p \ E) = 0 := by
      intro p
      let c : (Fin m → ℝ) × (Fin n → ℝ) := centers p.1
      let r : ℝ := 1 / (p.2 + 1 : ℝ)
      by_cases hA : Metric.closedBall c (2 * r) ⊆ C ×ˢ D
      · have hr : 0 < r := by positivity
        change MeasureTheory.volume
            ((if Metric.closedBall c (2 * r) ⊆ C ×ˢ D then Metric.ball c r else ∅) \ E) = 0
        simp [hA]
        simpa [E] using
          helperForTheorem_35_9_nullExceptionalSet_onBall
            (C := C) (D := D) (K := K) hC_open hD_open hC_conv hD_conv hK c hr hA
      · change MeasureTheory.volume
          ((if Metric.closedBall c (2 * r) ⊆ C ×ˢ D then Metric.ball c r else ∅) \ E) = 0
        simp [hA]
    have hNullUnion :
        MeasureTheory.volume (⋃ p : Nat × Nat, A p \ E) = 0 :=
      MeasureTheory.measure_iUnion_null hNullA
    exact MeasureTheory.measure_mono_null hSubset hNullUnion
  have hDense : C ×ˢ D ⊆ closure E := by
    -- Once the exceptional set is null, intersect the ambient full-measure dense set with any
    -- open neighborhood inside `C ×ˢ D`.
    intro p hpCD
    let bad : Set ((Fin m → ℝ) × (Fin n → ℝ)) := (C ×ˢ D) \ E
    have hBadNull : MeasureTheory.volume bad = 0 := by
      simpa [bad] using hNull
    have hAlmostEverywhere :
        ∀ᵐ q ∂(MeasureTheory.volume :
          MeasureTheory.Measure ((Fin m → ℝ) × (Fin n → ℝ))), q ∉ bad := by
      rw [MeasureTheory.ae_iff]
      simpa using hBadNull
    have hDenseBadCompl :
        Dense (badᶜ) :=
      MeasureTheory.Measure.dense_of_ae (μ := MeasureTheory.volume) hAlmostEverywhere
    rw [mem_closure_iff]
    intro s hs hpS
    rcases hDenseBadCompl.inter_open_nonempty (s ∩ (C ×ˢ D)) (hs.inter (hC_open.prod hD_open))
        ⟨p, hpS, hpCD⟩ with ⟨q, hq⟩
    have hqS : q ∈ s := hq.1.1
    have hqCD : q ∈ C ×ˢ D := hq.1.2
    have hqNotBad : q ∉ bad := hq.2
    have hqE : q ∈ E := by
      by_contra hqE'
      exact hqNotBad ⟨hqCD, hqE'⟩
    exact ⟨q, hqS, hqE⟩
  have hCont :
      Continuous (fun p : {p // p ∈ E} => packedRealSaddleKernelGradientPair K p.1.1 p.1.2) := by
    -- Continuity is isolated from the measure argument by the singleton-subgradient control on
    -- the differentiability locus.
    simpa [E] using
      helperForTheorem_35_9_gradientPair_continuousOn_E
        (C := C) (D := D) (K := K) hC_open hD_open hC_conv hD_conv hK
  exact ⟨hDense, hNull, hCont⟩

-- Proof sketch: apply Theorem 25.7 to the convex slices `v ↦ K(u, v)` and `u ↦ -K(u, v)` for
-- each fixed base point `(u, v)`, using differentiability of `K` and `Kᵢ` to identify the slice
-- gradients with the split gradient of the packed kernel. Then combine the pointwise convergence
-- of the partial gradients with Theorem 35.9, which gives continuity of the gradient maps on the
-- differentiability set, to upgrade the convergence to uniform convergence on every closed bounded
-- subset of `C × D`.
/-- Helper for Theorem 35.10: since `K` is differentiable at every point of `C × D`, Theorem 35.9
identifies the packed gradient pair as a continuous map on the whole product domain. -/
lemma helperForTheorem_35_10_limitGradient_continuousOn_product
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hK : IsRealConcaveConvexOn C D K)
    (hK_diff :
      ∀ u ∈ C, ∀ v ∈ D,
        DifferentiableAt ℝ (packedRealSaddleKernel K) (Fin.append u v)) :
    ContinuousOn
      (fun p : (Fin m → ℝ) × (Fin n → ℝ) => packedRealSaddleKernelGradientPair K p.1 p.2)
      (C ×ˢ D) := by
  let E : Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
    {p | p ∈ C ×ˢ D ∧ DifferentiableAt ℝ (packedRealSaddleKernel K) (Fin.append p.1 p.2)}
  have hEeq : E = C ×ˢ D := by
    -- Global differentiability collapses the exceptional set of Theorem 35.9 to the full product.
    ext p
    constructor
    · intro hp
      exact hp.1
    · intro hp
      exact ⟨hp, hK_diff p.1 hp.1 p.2 hp.2⟩
  have h35_9 :
      C ×ˢ D ⊆ closure E ∧
        MeasureTheory.volume ((C ×ˢ D) \ E) = 0 ∧
        Continuous (fun p : {p // p ∈ E} => packedRealSaddleKernelGradientPair K p.1.1 p.1.2) := by
    -- Specialize Theorem 35.9 with the explicit differentiability locus `E`.
    simpa [E] using
      section35_theorem35_9
        (C := C) (D := D) (K := K) hC_open hD_open hC_conv hD_conv hK
  rw [continuousOn_iff_continuous_restrict]
  let liftToE : {p // p ∈ C ×ˢ D} → {p // p ∈ E} := fun q =>
    ⟨q.1, q.2, hK_diff q.1.1 q.2.1 q.1.2 q.2.2⟩
  have hLiftToE : Continuous liftToE := by
    -- The domain inclusion into `E` is continuous because it only adds the differentiability proof.
    exact
      Continuous.subtype_mk continuous_subtype_val
        (fun q => ⟨q.2, hK_diff q.1.1 q.2.1 q.1.2 q.2.2⟩)
  -- Compose the `E`-continuity from Theorem 35.9 with the inclusion `C × D ↪ E`.
  simpa [liftToE] using h35_9.2.2.comp hLiftToE

/-- Helper for Theorem 35.10: Theorem 35.7 turns moving-point convergence of kernels into
convergence of the corresponding packed gradient pairs. -/
lemma helperForTheorem_35_10_moving_gradientPair_tendsto
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {KSeq : ℕ → (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hK : IsRealConcaveConvexOn C D K)
    (hK_diff :
      ∀ u ∈ C, ∀ v ∈ D,
        DifferentiableAt ℝ (packedRealSaddleKernel K) (Fin.append u v))
    (hKSeq : ∀ i, IsRealConcaveConvexOn C D (KSeq i))
    (hKSeq_diff :
      ∀ i, ∀ u ∈ C, ∀ v ∈ D,
        DifferentiableAt ℝ (packedRealSaddleKernel (KSeq i)) (Fin.append u v))
    (hpointwise :
      ∀ u ∈ C, ∀ v ∈ D,
        Filter.Tendsto (fun i : ℕ => KSeq i u v) Filter.atTop (nhds (K u v)))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D)
    (uSeq : ℕ → Fin m → ℝ) (vSeq : ℕ → Fin n → ℝ)
    (huSeq : ∀ i : ℕ, uSeq i ∈ C) (hvSeq : ∀ i : ℕ, vSeq i ∈ D)
    (huSeq_tendsto : Filter.Tendsto uSeq Filter.atTop (nhds u))
    (hvSeq_tendsto : Filter.Tendsto vSeq Filter.atTop (nhds v)) :
    Filter.Tendsto
      (fun i : ℕ => packedRealSaddleKernelGradientPair (KSeq i) (uSeq i) (vSeq i))
      Filter.atTop
      (nhds (packedRealSaddleKernelGradientPair K u v)) := by
  classical
  have hAsymp :=
    section35_theorem35_7
      (C := C) (D := D) (K := K) (KSeq := KSeq)
      hC_open hD_open hC_conv hD_conv hK hKSeq hpointwise
      hu hv uSeq vSeq huSeq hvSeq huSeq_tendsto hvSeq_tendsto
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  let η : ℝ := ε / 2
  have hηpos : 0 < η := by
    dsimp [η]
    linarith
  rcases hAsymp.2.2 η hηpos with ⟨i0, hi0⟩
  refine Filter.eventually_atTop.2 ⟨i0, ?_⟩
  intro i hi
  let grad : (Fin m → ℝ) × (Fin n → ℝ) := packedRealSaddleKernelGradientPair K u v
  let gradSeq : (Fin m → ℝ) × (Fin n → ℝ) :=
    packedRealSaddleKernelGradientPair (KSeq i) (uSeq i) (vSeq i)
  have hBaseSingleton :
      realSaddleSubdifferentialOn C D K u v = {grad} := by
    -- Differentiability identifies the limit saddle subdifferential with its unique gradient pair.
    simpa [grad] using
      helperForTheorem_35_9_realSaddleSubdifferential_eq_singleton_of_mem_E
        (C := C) (D := D) (K := K) hC_open hD_open hC_conv hD_conv hK hu hv
        (hK_diff u hu v hv)
  have hSeqSingleton :
      realSaddleSubdifferentialOn C D (KSeq i) (uSeq i) (vSeq i) = {gradSeq} := by
    -- The same singleton description holds for each approximating kernel at its moving base point.
    simpa [gradSeq] using
      helperForTheorem_35_9_realSaddleSubdifferential_eq_singleton_of_mem_E
        (C := C) (D := D) (K := KSeq i) hC_open hD_open hC_conv hD_conv (hKSeq i)
        (huSeq i) (hvSeq i) (hKSeq_diff i (uSeq i) (huSeq i) (vSeq i) (hvSeq i))
  have hSeqMem :
      gradSeq ∈ realSaddleSubdifferentialOn C D (KSeq i) (uSeq i) (vSeq i) := by
    -- The approximating singleton contains its own center.
    simpa [hSeqSingleton]
  have hImageMem :
      gradSeq ∈
        Set.image2 (fun p q : (Fin m → ℝ) × (Fin n → ℝ) => p + q)
          (realSaddleSubdifferentialOn C D K u v)
          (splitEuclideanClosedBall (m := m) (n := n) η) :=
    hi0 i hi hSeqMem
  rw [hBaseSingleton] at hImageMem
  rcases hImageMem with ⟨p, hp, q, hq, hpq⟩
  have hp' : p = grad := by simpa using hp
  subst hp'
  have hqNorms :
      ‖q.1‖ ≤ η ∧ ‖q.2‖ ≤ η :=
    helperForCorollary_35_7_1_coordinateNormBounds_of_mem_splitBall
      (m := m) (n := n) (r := η) (le_of_lt hηpos) hq
  have hηlt : η < ε := by
    dsimp [η]
    linarith
  have hClose :
      dist (grad + q) grad < ε := by
    -- Membership in the split error ball controls each coordinate of the gradient error.
    rw [Prod.dist_eq, max_lt_iff]
    constructor
    · exact lt_of_le_of_lt (by simpa [dist_eq_norm] using hqNorms.1) hηlt
    · exact lt_of_le_of_lt (by simpa [dist_eq_norm] using hqNorms.2) hηlt
  simpa [gradSeq, hpq] using hClose

/-- Helper for Theorem 35.10: the fixed-point convergence statement is the constant-sequence
specialization of the moving-point gradient-pair convergence lemma. -/
lemma helperForTheorem_35_10_pointwise_gradientPair_tendsto
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {KSeq : ℕ → (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hK : IsRealConcaveConvexOn C D K)
    (hK_diff :
      ∀ u ∈ C, ∀ v ∈ D,
        DifferentiableAt ℝ (packedRealSaddleKernel K) (Fin.append u v))
    (hKSeq : ∀ i, IsRealConcaveConvexOn C D (KSeq i))
    (hKSeq_diff :
      ∀ i, ∀ u ∈ C, ∀ v ∈ D,
        DifferentiableAt ℝ (packedRealSaddleKernel (KSeq i)) (Fin.append u v))
    (hpointwise :
      ∀ u ∈ C, ∀ v ∈ D,
        Filter.Tendsto (fun i : ℕ => KSeq i u v) Filter.atTop (nhds (K u v)))
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D) :
    Filter.Tendsto
      (fun i : ℕ => packedRealSaddleKernelGradientPair (KSeq i) u v)
      Filter.atTop
      (nhds (packedRealSaddleKernelGradientPair K u v)) := by
  -- Freeze the moving-point lemma to the constant tracks `uSeq i = u` and `vSeq i = v`.
  simpa using
    helperForTheorem_35_10_moving_gradientPair_tendsto
      (C := C) (D := D) (K := K) (KSeq := KSeq)
      hC_open hD_open hC_conv hD_conv hK hK_diff hKSeq hKSeq_diff hpointwise
      hu hv (fun _ : ℕ => u) (fun _ : ℕ => v) (fun _ => hu) (fun _ => hv)
      tendsto_const_nhds tendsto_const_nhds

/-- Theorem 35.10: let `C × D` be an open convex set in `ℝ^m × ℝ^n`, let `K` be a finite
differentiable concave-convex function on `C × D`, and let `K₁, K₂, ...` be finite differentiable
concave-convex functions on `C × D` converging pointwise to `K`. Then the split gradient maps
`∇Kᵢ(u, v)` converge pointwise to `∇K(u, v)` for every `(u, v) ∈ C × D`, and in fact converge
uniformly on every closed bounded subset of `C × D`. -/
theorem section35_theorem35_10
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {KSeq : ℕ → (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hK : IsRealConcaveConvexOn C D K)
    (hK_diff :
      ∀ u ∈ C, ∀ v ∈ D,
        DifferentiableAt ℝ (packedRealSaddleKernel K) (Fin.append u v))
    (hKSeq : ∀ i, IsRealConcaveConvexOn C D (KSeq i))
    (hKSeq_diff :
      ∀ i, ∀ u ∈ C, ∀ v ∈ D,
        DifferentiableAt ℝ (packedRealSaddleKernel (KSeq i)) (Fin.append u v))
    (hpointwise :
      ∀ u ∈ C, ∀ v ∈ D,
        Filter.Tendsto (fun i : ℕ => KSeq i u v) Filter.atTop (nhds (K u v))) :
    (∀ u ∈ C, ∀ v ∈ D,
      Filter.Tendsto
        (fun i : ℕ => packedRealSaddleKernelGradientPair (KSeq i) u v)
        Filter.atTop
        (nhds (packedRealSaddleKernelGradientPair K u v))) ∧
    ∀ S : Set ((Fin m → ℝ) × (Fin n → ℝ)),
      S ⊆ C ×ˢ D → IsClosed S → Bornology.IsBounded S →
        TendstoUniformlyOn
          (fun i p => packedRealSaddleKernelGradientPair (KSeq i) p.1 p.2)
          (fun p => packedRealSaddleKernelGradientPair K p.1 p.2)
          Filter.atTop S := by
  classical
  constructor
  · intro u hu v hv
    -- The pointwise convergence is the constant-sequence case of the moving-point asymptotic theorem.
    exact
      helperForTheorem_35_10_pointwise_gradientPair_tendsto
        (C := C) (D := D) (K := K) (KSeq := KSeq)
        hC_open hD_open hC_conv hD_conv hK hK_diff hKSeq hKSeq_diff hpointwise hu hv
  · intro S hSsub hSclosed hSbdd
    let G : ((Fin m → ℝ) × (Fin n → ℝ)) → ((Fin m → ℝ) × (Fin n → ℝ)) :=
      fun p => packedRealSaddleKernelGradientPair K p.1 p.2
    let GSeq : ℕ → ((Fin m → ℝ) × (Fin n → ℝ)) → ((Fin m → ℝ) × (Fin n → ℝ)) :=
      fun i p => packedRealSaddleKernelGradientPair (KSeq i) p.1 p.2
    have hGcont : ContinuousOn G (C ×ˢ D) := by
      -- The limit gradient map is continuous on the whole open rectangle by Theorem 35.9.
      simpa [G] using
        helperForTheorem_35_10_limitGradient_continuousOn_product
          (C := C) (D := D) (K := K) hC_open hD_open hC_conv hD_conv hK hK_diff
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    by_contra hUniform
    have hfreq :
        ∃ᶠ i : ℕ in Filter.atTop,
          ∃ p ∈ S, ε ≤ dist (G p) (GSeq i p) := by
      simpa [G, GSeq, Filter.Frequently, not_forall, not_lt, dist_comm] using hUniform
    rcases Filter.extraction_of_frequently_atTop hfreq with ⟨φ, hφmono, hφbad⟩
    choose p hpS hpbad using hφbad
    have hScomp : IsCompact S := Metric.isCompact_of_isClosed_isBounded hSclosed hSbdd
    rcases hScomp.tendsto_subseq (x := p) hpS with ⟨z, hzS, ψ, hψmono, hψtend⟩
    let θ : ℕ → ℕ := φ ∘ ψ
    have hθmono : StrictMono θ := hφmono.comp hψmono
    have hθtend : Filter.Tendsto θ Filter.atTop Filter.atTop := hθmono.tendsto_atTop
    have hpSubseq_tendsto :
        Filter.Tendsto (fun k : ℕ => p (ψ k)) Filter.atTop (nhds z) := by
      simpa [Function.comp] using hψtend
    have huSubseq :
        ∀ k : ℕ, (fun k : ℕ => (p (ψ k)).1) k ∈ C := by
      intro k
      exact (hSsub (hpS (ψ k))).1
    have hvSubseq :
        ∀ k : ℕ, (fun k : ℕ => (p (ψ k)).2) k ∈ D := by
      intro k
      exact (hSsub (hpS (ψ k))).2
    have huSubseq_tendsto :
        Filter.Tendsto (fun k : ℕ => (p (ψ k)).1) Filter.atTop (nhds z.1) := by
      simpa [Function.comp] using (continuous_fst.tendsto z).comp hpSubseq_tendsto
    have hvSubseq_tendsto :
        Filter.Tendsto (fun k : ℕ => (p (ψ k)).2) Filter.atTop (nhds z.2) := by
      simpa [Function.comp] using (continuous_snd.tendsto z).comp hpSubseq_tendsto
    have hpointwiseSub :
        ∀ u ∈ C, ∀ v ∈ D,
          Filter.Tendsto (fun k : ℕ => KSeq (θ k) u v) Filter.atTop (nhds (K u v)) := by
      intro u hu v hv
      exact (hpointwise u hu v hv).comp hθtend
    have hMovingGrad :
        Filter.Tendsto
          (fun k : ℕ => GSeq (θ k) (p (ψ k)))
          Filter.atTop
          (nhds (G z)) := by
      -- Apply the moving-point gradient convergence lemma to the extracted bad subsequence.
      simpa [G, GSeq, θ] using
        helperForTheorem_35_10_moving_gradientPair_tendsto
          (C := C) (D := D) (K := K) (KSeq := fun k => KSeq (θ k))
          hC_open hD_open hC_conv hD_conv hK hK_diff
          (fun k => hKSeq (θ k))
          (fun k u hu v hv => hKSeq_diff (θ k) u hu v hv)
          hpointwiseSub
          (hSsub hzS).1 (hSsub hzS).2
          (fun k : ℕ => (p (ψ k)).1) (fun k : ℕ => (p (ψ k)).2)
          huSubseq hvSubseq huSubseq_tendsto hvSubseq_tendsto
    have hpWithin :
        Filter.Tendsto (fun k : ℕ => p (ψ k)) Filter.atTop (nhdsWithin z (C ×ˢ D)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        (fun k : ℕ => p (ψ k)) hpSubseq_tendsto
        (Filter.Eventually.of_forall fun k => hSsub (hpS (ψ k)))
    have hLimitGrad :
        Filter.Tendsto (fun k : ℕ => G (p (ψ k))) Filter.atTop (nhds (G z)) := by
      -- Continuity of the limit gradient turns convergence of the base points into convergence of
      -- the corresponding limit gradients.
      exact (hGcont z (hSsub hzS)).tendsto.comp hpWithin
    have hdist_tend :
        Filter.Tendsto
          (fun k : ℕ => dist (GSeq (θ k) (p (ψ k))) (G (p (ψ k))))
          Filter.atTop
          (nhds 0) := by
      simpa [dist_self] using hMovingGrad.dist hLimitGrad
    have hEventuallySmall :
        ∀ᶠ k : ℕ in Filter.atTop, dist (GSeq (θ k) (p (ψ k))) (G (p (ψ k))) < ε := by
      have hDistToZero :
          ∀ᶠ k : ℕ in Filter.atTop,
            dist (dist (GSeq (θ k) (p (ψ k))) (G (p (ψ k)))) 0 < ε := by
        exact (Metric.tendsto_nhds.1 hdist_tend) ε hε
      filter_upwards [hDistToZero] with k hk
      simpa [Real.dist_eq, abs_of_nonneg (dist_nonneg)] using hk
    have hEventuallyLarge :
        ∀ᶠ k : ℕ in Filter.atTop,
          ε ≤ dist (GSeq (θ k) (p (ψ k))) (G (p (ψ k))) := by
      refine Filter.Eventually.of_forall ?_
      intro k
      simpa [G, GSeq, θ, dist_comm] using hpbad (ψ k)
    have hContr : ∀ᶠ k : ℕ in Filter.atTop, False := by
      filter_upwards [hEventuallyLarge, hEventuallySmall] with k hkLarge hkSmall
      exact (not_lt_of_ge hkLarge) hkSmall
    rcases Filter.eventually_atTop.1 hContr with ⟨N, hN⟩
    exact hN N le_rfl

-- Proof sketch: first use the dense-subset convergence hypothesis together with the finite
-- concave-convex structure and the extension principle of Theorem 35.4 to upgrade convergence of
-- `Kᵢ` from `C' × D'` to all of `C × D`. With this pointwise convergence on the full domain in
-- hand, apply Theorem 35.10 to obtain pointwise convergence of the split gradients and uniform
-- convergence of these gradient maps on every closed bounded subset.
/-- Helper for Text 35.10.1: repackage the dense convergence hypothesis into the existential
limit format required by Theorem 35.4. -/
lemma helperForText_35_10_1_denseWitness_existsLimits
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {C : Set E} {D : Set F}
    {K : E → F → ℝ}
    {KSeq : ℕ → E → F → ℝ}
    (hDense :
      ∃ C' : Set E,
        ∃ D' : Set F,
          C' ⊆ C ∧
          D' ⊆ D ∧
          C ⊆ closure C' ∧
          D ⊆ closure D' ∧
          ∀ u ∈ C', ∀ v ∈ D',
            Filter.Tendsto (fun i : ℕ => KSeq i u v) Filter.atTop (nhds (K u v))) :
    ∃ C' : Set E,
      ∃ D' : Set F,
        C' ⊆ C ∧
        D' ⊆ D ∧
        C ⊆ closure C' ∧
        D ⊆ closure D' ∧
        ∀ u ∈ C', ∀ v ∈ D', ∃ l : ℝ,
          Filter.Tendsto (fun i : ℕ => KSeq i u v) Filter.atTop (nhds l) := by
  rcases hDense with ⟨C', D', hC'sub, hD'sub, hCclosure, hDclosure, hDenseTendsto⟩
  refine ⟨C', D', hC'sub, hD'sub, hCclosure, hDclosure, ?_⟩
  intro u hu v hv
  -- Use the prescribed kernel value `K u v` as the witness limit on the dense product.
  exact ⟨K u v, hDenseTendsto u hu v hv⟩

/-- Helper for Text 35.10.1: two finite concave-convex kernels that agree on a dense product
subset of an open convex rectangle agree on the whole rectangle. -/
lemma helperForText_35_10_1_eqOn_product_of_denseEq
    {m n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin m))} {D : Set (EuclideanSpace ℝ (Fin n))}
    {K L : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ}
    (hC : IsRelativelyOpenConvex C) (hD : IsRelativelyOpenConvex D)
    (hK : IsRealConcaveConvexOn C D K)
    (hL : IsRealConcaveConvexOn C D L)
    {C' : Set (EuclideanSpace ℝ (Fin m))} {D' : Set (EuclideanSpace ℝ (Fin n))}
    (hC'sub : C' ⊆ C) (hD'sub : D' ⊆ D)
    (hCclosure : C ⊆ closure C') (hDclosure : D ⊆ closure D')
    (hEqDense : ∀ u ∈ C', ∀ v ∈ D', L u v = K u v) :
    ∀ u ∈ C, ∀ v ∈ D, L u v = K u v := by
  have hLcont : ContinuousOn (Function.uncurry L) (C ×ˢ D) :=
    (section35_theorem35_1 (m := m) (n := n) (C := C) (D := D) (K := L) hC hD hL).1
  have hKcont : ContinuousOn (Function.uncurry K) (C ×ˢ D) :=
    (section35_theorem35_1 (m := m) (n := n) (C := C) (D := D) (K := K) hC hD hK).1
  have hEqDenseProd :
      Set.EqOn (Function.uncurry L) (Function.uncurry K) (C' ×ˢ D') := by
    intro p hp
    -- On the witness product, the two kernels agree by hypothesis.
    exact hEqDense p.1 hp.1 p.2 hp.2
  have hProdSub : C' ×ˢ D' ⊆ C ×ˢ D := by
    intro p hp
    exact ⟨hC'sub hp.1, hD'sub hp.2⟩
  have hProdClosure : C ×ˢ D ⊆ closure (C' ×ˢ D') := by
    intro p hp
    -- Density in each factor gives density of the product witness set.
    rw [closure_prod_eq]
    exact ⟨hCclosure hp.1, hDclosure hp.2⟩
  have hEqAll :
      Set.EqOn (Function.uncurry L) (Function.uncurry K) (C ×ˢ D) :=
    Set.EqOn.of_subset_closure hEqDenseProd hLcont hKcont hProdSub hProdClosure
  intro u hu v hv
  -- Evaluate the product-level equality at the requested point.
  simpa using (hEqAll (x := (u, v)) ⟨hu, hv⟩)

/-- Helper for Text 35.10.1: the dense convergence hypothesis already forces pointwise
convergence of `Kᵢ` to the prescribed kernel `K` on all of `C × D`. -/
lemma helperForText_35_10_1_pointwiseTendsto_to_prescribedKernel
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {KSeq : ℕ → (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hK : IsRealConcaveConvexOn C D K)
    (hKSeq : ∀ i, IsRealConcaveConvexOn C D (KSeq i))
    (hDense :
      ∃ C' : Set (Fin m → ℝ),
        ∃ D' : Set (Fin n → ℝ),
          C' ⊆ C ∧
          D' ⊆ D ∧
          C ⊆ closure C' ∧
          D ⊆ closure D' ∧
          ∀ u ∈ C', ∀ v ∈ D',
            Filter.Tendsto (fun i : ℕ => KSeq i u v) Filter.atTop (nhds (K u v))) :
    ∀ u ∈ C, ∀ v ∈ D,
      Filter.Tendsto (fun i : ℕ => KSeq i u v) Filter.atTop (nhds (K u v)) := by
  let e_m : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin m)
  let e_n : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)
  have hCrel :
      IsRelativelyOpenConvex C :=
    helperForTheorem_35_7_isRelativelyOpenConvex_of_isOpen
      (hsConv := hC_conv) (hsOpen := hC_open)
  have hDrel :
      IsRelativelyOpenConvex D :=
    helperForTheorem_35_7_isRelativelyOpenConvex_of_isOpen
      (hsConv := hD_conv) (hsOpen := hD_open)
  let C0 : Set (EuclideanSpace ℝ (Fin m)) := e_m.symm '' C
  let D0 : Set (EuclideanSpace ℝ (Fin n)) := e_n.symm '' D
  let K0 : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x y => K (e_m x) (e_n y)
  let KSeq0 : ℕ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun i x y => KSeq i (e_m x) (e_n y)
  have hC0 : IsRelativelyOpenConvex C0 := by
    -- Transport the open convex set `C` into the Euclidean model used by Theorem 35.4.
    simpa [C0] using
      helperForTheorem_35_7_isRelativelyOpenConvex_image_continuousLinearEquiv
        (e := e_m.symm) (s := C) hCrel
  have hD0 : IsRelativelyOpenConvex D0 := by
    -- Transport the open convex set `D` into the Euclidean model used by Theorem 35.4.
    simpa [D0] using
      helperForTheorem_35_7_isRelativelyOpenConvex_image_continuousLinearEquiv
        (e := e_n.symm) (s := D) hDrel
  have hC0_pre : C0 = (e_m ⁻¹' C) := by
    simpa [C0] using (Equiv.image_eq_preimage (e_m.symm.toEquiv) C)
  have hD0_pre : D0 = (e_n ⁻¹' D) := by
    simpa [D0] using (Equiv.image_eq_preimage (e_n.symm.toEquiv) D)
  have hK0 : IsRealConcaveConvexOn C0 D0 K0 := by
    constructor
    · intro y hy
      rcases hy with ⟨v, hv, rfl⟩
      have hConc : ConcaveOn ℝ C (fun x => K x v) := hK.1 v hv
      have hConc' :=
        ConcaveOn.comp_affineMap
          (g := e_m.toLinearEquiv.toAffineEquiv.toAffineMap) (s := C) hConc
      simpa [K0, hC0_pre, Function.comp] using hConc'
    · intro x hx
      rcases hx with ⟨u, hu, rfl⟩
      have hConv : ConvexOn ℝ D (fun y => K u y) := hK.2 u hu
      have hConv' :=
        ConvexOn.comp_affineMap
          (g := e_n.toLinearEquiv.toAffineEquiv.toAffineMap) (s := D) hConv
      simpa [K0, hD0_pre, Function.comp] using hConv'
  have hKSeq0 : ∀ i, IsRealConcaveConvexOn C0 D0 (KSeq0 i) := by
    intro i
    constructor
    · intro y hy
      rcases hy with ⟨v, hv, rfl⟩
      have hConc : ConcaveOn ℝ C (fun x => KSeq i x v) := (hKSeq i).1 v hv
      have hConc' :=
        ConcaveOn.comp_affineMap
          (g := e_m.toLinearEquiv.toAffineEquiv.toAffineMap) (s := C) hConc
      simpa [KSeq0, hC0_pre, Function.comp] using hConc'
    · intro x hx
      rcases hx with ⟨u, hu, rfl⟩
      have hConv : ConvexOn ℝ D (fun y => KSeq i u y) := (hKSeq i).2 u hu
      have hConv' :=
        ConvexOn.comp_affineMap
          (g := e_n.toLinearEquiv.toAffineEquiv.toAffineMap) (s := D) hConv
      simpa [KSeq0, hD0_pre, Function.comp] using hConv'
  rcases hDense with ⟨C', D', hC'sub, hD'sub, hCclosure, hDclosure, hDenseTendsto⟩
  let C0' : Set (EuclideanSpace ℝ (Fin m)) := e_m.symm '' C'
  let D0' : Set (EuclideanSpace ℝ (Fin n)) := e_n.symm '' D'
  have hC0'sub : C0' ⊆ C0 := by
    intro x hx
    rcases hx with ⟨u, hu, rfl⟩
    exact ⟨u, hC'sub hu, rfl⟩
  have hD0'sub : D0' ⊆ D0 := by
    intro y hy
    rcases hy with ⟨v, hv, rfl⟩
    exact ⟨v, hD'sub hv, rfl⟩
  have hC0closure : C0 ⊆ closure C0' := by
    intro x hx
    rcases hx with ⟨u, hu, rfl⟩
    have hClosureImage : e_m.symm '' closure C' = closure C0' := by
      simpa [C0'] using (e_m.symm.toHomeomorph.image_closure C')
    rw [← hClosureImage]
    exact ⟨u, hCclosure hu, rfl⟩
  have hD0closure : D0 ⊆ closure D0' := by
    intro y hy
    rcases hy with ⟨v, hv, rfl⟩
    have hClosureImage : e_n.symm '' closure D' = closure D0' := by
      simpa [D0'] using (e_n.symm.toHomeomorph.image_closure D')
    rw [← hClosureImage]
    exact ⟨v, hDclosure hv, rfl⟩
  have hDense0Prescribed :
      ∃ Cw : Set (EuclideanSpace ℝ (Fin m)),
        ∃ Dw : Set (EuclideanSpace ℝ (Fin n)),
          Cw ⊆ C0 ∧
          Dw ⊆ D0 ∧
          C0 ⊆ closure Cw ∧
          D0 ⊆ closure Dw ∧
          ∀ u ∈ Cw, ∀ v ∈ Dw,
            Filter.Tendsto (fun i : ℕ => KSeq0 i u v) Filter.atTop (nhds (K0 u v)) := by
    refine ⟨C0', D0', hC0'sub, hD0'sub, hC0closure, hD0closure, ?_⟩
    intro u hu v hv
    rcases hu with ⟨u0, hu0, rfl⟩
    rcases hv with ⟨v0, hv0, rfl⟩
    -- On the transported dense product, the original dense convergence hypothesis reads exactly
    -- as convergence of `KSeq0` to `K0`.
    simpa [KSeq0, K0] using hDenseTendsto u0 hu0 v0 hv0
  have hDenseWitness :
      ∃ Cw : Set (EuclideanSpace ℝ (Fin m)),
        ∃ Dw : Set (EuclideanSpace ℝ (Fin n)),
          Cw ⊆ C0 ∧
          Dw ⊆ D0 ∧
          C0 ⊆ closure Cw ∧
          D0 ⊆ closure Dw ∧
          ∀ u ∈ Cw, ∀ v ∈ Dw, ∃ l : ℝ,
            Filter.Tendsto (fun i : ℕ => KSeq0 i u v) Filter.atTop (nhds l) :=
    helperForText_35_10_1_denseWitness_existsLimits
      (K := K0) (KSeq := KSeq0) hDense0Prescribed
  rcases
      section35_theorem35_4
        (m := m) (n := n) (C := C0) (D := D0) (KSeq := KSeq0) hC0 hD0 hKSeq0 hDenseWitness with
    ⟨Kext0, hKext0, hKext0Tendsto, _hUniform⟩
  have hEqDense0 :
      ∀ u ∈ C0', ∀ v ∈ D0', Kext0 u v = K0 u v := by
    intro u hu v hv
    rcases hu with ⟨u0, hu0, rfl⟩
    rcases hv with ⟨v0, hv0, rfl⟩
    -- The transported dense witness still prescribes the limit uniquely.
    exact tendsto_nhds_unique
      (by
        simpa [KSeq0, K0] using
          hKext0Tendsto (e_m.symm u0) ⟨u0, hC'sub hu0, rfl⟩ (e_n.symm v0) ⟨v0, hD'sub hv0, rfl⟩)
      (by simpa [KSeq0, K0] using hDenseTendsto u0 hu0 v0 hv0)
  have hEqAll0 :
      ∀ u ∈ C0, ∀ v ∈ D0, Kext0 u v = K0 u v :=
    helperForText_35_10_1_eqOn_product_of_denseEq
      (C := C0) (D := D0) (K := K0) (L := Kext0)
      hC0 hD0 hK0 hKext0 hC0'sub hD0'sub hC0closure hD0closure hEqDense0
  intro u hu v hv
  have hu0 : e_m.symm u ∈ C0 := ⟨u, hu, rfl⟩
  have hv0 : e_n.symm v ∈ D0 := ⟨v, hv, rfl⟩
  -- Replace the transported auxiliary limit kernel by the transported prescribed kernel, then
  -- simplify back to the original coordinates.
  simpa [KSeq0, K0, hEqAll0 (e_m.symm u) hu0 (e_n.symm v) hv0] using
    hKext0Tendsto (e_m.symm u) hu0 (e_n.symm v) hv0

/-- Text 35.10.1: let `C × D` be a nonempty open convex subset of `ℝ^m × ℝ^n`, let `K` be a
finite differentiable concave-convex function on `C × D`, and let `K₁, K₂, ...` be finite
differentiable concave-convex functions on `C × D`. If there exist dense subsets `C' ⊆ C` and
`D' ⊆ D` such that `(A)` `Kᵢ(u, v) → K(u, v)` for every `(u, v) ∈ C' × D'`, then `(B)`
`Kᵢ(u, v) → K(u, v)` for every `(u, v) ∈ C × D`. Consequently, the conclusion of Theorem 35.10
holds: the split gradient maps converge pointwise on `C × D` and uniformly on each closed bounded
subset of `C × D`. -/
theorem section35_text35_10_1
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {KSeq : ℕ → (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hNonempty : (C ×ˢ D).Nonempty)
    (hC_open : IsOpen C) (hD_open : IsOpen D)
    (hC_conv : Convex ℝ C) (hD_conv : Convex ℝ D)
    (hK : IsRealConcaveConvexOn C D K)
    (hK_diff :
      ∀ u ∈ C, ∀ v ∈ D,
        DifferentiableAt ℝ (packedRealSaddleKernel K) (Fin.append u v))
    (hKSeq : ∀ i, IsRealConcaveConvexOn C D (KSeq i))
    (hKSeq_diff :
      ∀ i, ∀ u ∈ C, ∀ v ∈ D,
        DifferentiableAt ℝ (packedRealSaddleKernel (KSeq i)) (Fin.append u v))
    (hDense :
      ∃ C' : Set (Fin m → ℝ),
        ∃ D' : Set (Fin n → ℝ),
          C' ⊆ C ∧
          D' ⊆ D ∧
          C ⊆ closure C' ∧
          D ⊆ closure D' ∧
          ∀ u ∈ C', ∀ v ∈ D',
            Filter.Tendsto (fun i : ℕ => KSeq i u v) Filter.atTop (nhds (K u v))) :
    (∀ u ∈ C, ∀ v ∈ D,
      Filter.Tendsto (fun i : ℕ => KSeq i u v) Filter.atTop (nhds (K u v))) ∧
    (∀ u ∈ C, ∀ v ∈ D,
      Filter.Tendsto
        (fun i : ℕ => packedRealSaddleKernelGradientPair (KSeq i) u v)
        Filter.atTop
        (nhds (packedRealSaddleKernelGradientPair K u v))) ∧
    ∀ S : Set ((Fin m → ℝ) × (Fin n → ℝ)),
      S ⊆ C ×ˢ D → IsClosed S → Bornology.IsBounded S →
        TendstoUniformlyOn
          (fun i p => packedRealSaddleKernelGradientPair (KSeq i) p.1 p.2)
          (fun p => packedRealSaddleKernelGradientPair K p.1 p.2)
          Filter.atTop S := by
  -- First upgrade convergence from the dense witness product to all of `C × D`.
  have hPointwise :
      ∀ u ∈ C, ∀ v ∈ D,
        Filter.Tendsto (fun i : ℕ => KSeq i u v) Filter.atTop (nhds (K u v)) :=
    helperForText_35_10_1_pointwiseTendsto_to_prescribedKernel
      (C := C) (D := D) (K := K) (KSeq := KSeq)
      hC_open hD_open hC_conv hD_conv hK hKSeq hDense
  -- With full pointwise convergence available, Theorem 35.10 supplies the gradient conclusions.
  rcases
      section35_theorem35_10
        (C := C) (D := D) (K := K) (KSeq := KSeq)
        hC_open hD_open hC_conv hD_conv hK hK_diff hKSeq hKSeq_diff hPointwise with
    ⟨hGradientPointwise, hGradientUniform⟩
  exact ⟨hPointwise, hGradientPointwise, hGradientUniform⟩

end Section35
end Chap07

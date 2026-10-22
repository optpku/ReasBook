/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section35_part21

section Chap07
section Section35

attribute [local instance] Classical.propDecidable
open scoped Pointwise
open scoped Topology

/-- Helper for Theorem 35.8: once the local real rectangle kernel has singleton saddle
subdifferential at `(u, v)`, the remaining analytic task is to turn that local singleton control
into differentiability of the packed real map on the rectangle. -/
lemma helperForTheorem_35_8_puncturedPackedRealRemainder_small
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    {uStar : Fin m → ℝ} {vStar : Fin n → ℝ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (hCopen : IsOpen C) (huC : u ∈ C) (hCconv : Convex ℝ C)
    (hDopen : IsOpen D) (hvD : v ∈ D) (hDconv : Convex ℝ D)
    (hFiniteCD :
      ∀ x ∈ C, ∀ y ∈ D, K x y ≠ (⊤ : EReal) ∧ K x y ≠ (⊥ : EReal))
    (hLocal :
      let Kloc : (Fin m → ℝ) → (Fin n → ℝ) → ℝ := fun x y => (K x y).toReal
      IsRealConcaveConvexOn C D Kloc ∧
        realSaddleSubdifferentialOn C D Kloc u v = {(uStar, vStar)}) :
    let Kloc : (Fin m → ℝ) → (Fin n → ℝ) → ℝ := fun x y => (K x y).toReal
    let fLoc : (Fin (m + n) → ℝ) → ℝ :=
      fun z => Kloc (fun i => z (Fin.castAdd n i)) (fun j => z (Fin.natAdd m j))
    let L : (Fin (m + n) → ℝ) →L[ℝ] ℝ :=
      helperForCorollary_25_5_1_dotProductContinuousLinearMap (Fin.append uStar vStar)
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in 𝓝[≠] (Fin.append u v),
        ‖z - Fin.append u v‖⁻¹ * ‖fLoc z - fLoc (Fin.append u v) - L (z - Fin.append u v)‖ ≤ ε := by
  classical
  dsimp
  intro ε hε
  let Kloc : (Fin m → ℝ) → (Fin n → ℝ) → ℝ := fun x y => (K x y).toReal
  let fLoc : (Fin (m + n) → ℝ) → ℝ :=
    fun z => Kloc (fun i => z (Fin.castAdd n i)) (fun j => z (Fin.natAdd m j))
  let z0 : Fin (m + n) → ℝ := Fin.append u v
  let L : (Fin (m + n) → ℝ) →L[ℝ] ℝ :=
    helperForCorollary_25_5_1_dotProductContinuousLinearMap (Fin.append uStar vStar)
  have hLocal' : IsRealConcaveConvexOn C D Kloc ∧
      realSaddleSubdifferentialOn C D Kloc u v = {(uStar, vStar)} := by
    simpa [Kloc] using hLocal
  rcases hLocal' with ⟨hRealCC, hBase⟩
  rcases Metric.mem_nhds_iff.mp (hCopen.mem_nhds huC) with ⟨rC, hrC, hBallC⟩
  rcases Metric.mem_nhds_iff.mp (hDopen.mem_nhds hvD) with ⟨rD, hrD, hBallD⟩
  let A : ℝ := ((m + n + 1 : ℕ) : ℝ)
  let η : ℝ := ε / A
  have hApos : 0 < A := by
    dsimp [A]
    exact_mod_cast (Nat.succ_pos (m + n))
  have hηpos : 0 < η := by
    dsimp [η]
    exact div_pos hε hApos
  rcases
      helperForTheorem_35_8_nearbyRealSubgradient_close_to_singleton
        (C := C) (D := D) (Kloc := Kloc) (u := u) (v := v)
        (uStar := uStar) (vStar := vStar)
        hCopen huC hCconv hDopen hvD hDconv hRealCC hBase η hηpos with
    ⟨δ0, hδ0pos, hNear⟩
  let δSmall : ℝ := δ0 / Real.sqrt A
  let ρ : ℝ := min rC (min rD δSmall)
  have hδSmallPos : 0 < δSmall := by
    dsimp [δSmall]
    exact div_pos hδ0pos (Real.sqrt_pos.2 hApos)
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    exact lt_min hrC (lt_min hrD hδSmallPos)
  have hρle_rC : ρ ≤ rC := by
    dsimp [ρ]
    exact min_le_left _ _
  have hρle_rD : ρ ≤ rD := by
    dsimp [ρ]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρle_δSmall : ρ ≤ δSmall := by
    dsimp [ρ]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hρnonneg : 0 ≤ ρ := le_of_lt hρpos
  have hδSmall_nonneg : 0 ≤ δSmall := le_of_lt hδSmallPos
  have hδSmallIneq : ((m + n : ℕ) : ℝ) * δSmall ^ (2 : ℕ) ≤ δ0 ^ (2 : ℕ) := by
    have hratio : ((m + n : ℕ) : ℝ) / A ≤ (1 : ℝ) := by
      have hle : ((m + n : ℕ) : ℝ) ≤ A := by
        dsimp [A]
        exact_mod_cast (Nat.le_succ (m + n))
      exact (div_le_one hApos).2 hle
    have hδ0sq : 0 ≤ δ0 ^ (2 : ℕ) := by
      nlinarith
    have hδSmallSq : δSmall ^ (2 : ℕ) = (δ0 ^ (2 : ℕ)) / A := by
      dsimp [δSmall]
      have hsqrtSq : (Real.sqrt A) ^ (2 : ℕ) = A := by
        simpa [pow_two] using Real.sq_sqrt (le_of_lt hApos)
      simpa [div_pow, hsqrtSq]
    calc
      ((m + n : ℕ) : ℝ) * δSmall ^ (2 : ℕ) =
          ((m + n : ℕ) : ℝ) * ((δ0 ^ (2 : ℕ)) / A) := by
            simp [hδSmallSq]
      _ = (δ0 ^ (2 : ℕ)) * (((m + n : ℕ) : ℝ) / A) := by
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ ≤ (δ0 ^ (2 : ℕ)) * 1 := by
            exact mul_le_mul_of_nonneg_left hratio hδ0sq
      _ = δ0 ^ (2 : ℕ) := by simp
  have hρIneq : ((m + n : ℕ) : ℝ) * ρ ^ (2 : ℕ) ≤ δ0 ^ (2 : ℕ) := by
    have hρsq : ρ ^ (2 : ℕ) ≤ δSmall ^ (2 : ℕ) := by
      nlinarith [hρle_δSmall, hρnonneg, hδSmall_nonneg]
    have hNnonneg : 0 ≤ ((m + n : ℕ) : ℝ) := by positivity
    exact le_trans (mul_le_mul_of_nonneg_left hρsq hNnonneg) hδSmallIneq
  have hBallWithin :
      ∀ᶠ z in 𝓝[≠] z0, z ∈ Metric.ball z0 ρ := by
    exact mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z0 hρpos)
  filter_upwards [self_mem_nhdsWithin, hBallWithin] with z hzNe hzBall
  let x : Fin m → ℝ := fun i => z (Fin.castAdd n i)
  let y : Fin n → ℝ := fun j => z (Fin.natAdd m j)
  let dx : Fin m → ℝ := x - u
  let dy : Fin n → ℝ := y - v
  have hzNormLt : ‖z - z0‖ < ρ := by
    simpa [Metric.mem_ball, dist_eq_norm, z0] using hzBall
  have hdx_le : ‖dx‖ ≤ ‖z - z0‖ := by
    -- Each first-block coordinate difference is one coordinate of the packed displacement.
    refine (pi_norm_le_iff_of_nonneg (x := dx) (r := ‖z - z0‖) (norm_nonneg _)).2 ?_
    intro i
    have hi : ‖(z - z0) (Fin.castAdd n i)‖ ≤ ‖z - z0‖ :=
      norm_le_pi_norm (f := z - z0) (i := Fin.castAdd n i)
    simpa [dx, x, z0, Pi.sub_apply] using hi
  have hdy_le : ‖dy‖ ≤ ‖z - z0‖ := by
    -- The same coordinatewise estimate applies to the second block.
    refine (pi_norm_le_iff_of_nonneg (x := dy) (r := ‖z - z0‖) (norm_nonneg _)).2 ?_
    intro j
    have hj : ‖(z - z0) (Fin.natAdd m j)‖ ≤ ‖z - z0‖ :=
      norm_le_pi_norm (f := z - z0) (i := Fin.natAdd m j)
    simpa [dy, y, z0, Pi.sub_apply] using hj
  have hdx_lt_rC : ‖dx‖ < rC := lt_of_le_of_lt hdx_le (lt_of_lt_of_le hzNormLt hρle_rC)
  have hdy_lt_rD : ‖dy‖ < rD := lt_of_le_of_lt hdy_le (lt_of_lt_of_le hzNormLt hρle_rD)
  have hxC : x ∈ C := by
    -- The packed ball was chosen small enough that the first block stays in `C`.
    exact hBallC (by simpa [Metric.mem_ball, dist_eq_norm, dx] using hdx_lt_rC)
  have hyD : y ∈ D := by
    -- And likewise the second block stays in `D`.
    exact hBallD (by simpa [Metric.mem_ball, dist_eq_norm, dy] using hdy_lt_rD)
  have hxySplit :
      ((x - u), (y - v)) ∈ splitEuclideanClosedBall (m := m) (n := n) δ0 := by
    -- The smaller packed radius makes the split displacement small enough for Corollary 35.7.1.
    refine
      helperForTheorem_35_7_splitBall_combine_errors
        (m := m) (n := n) (ε := δ0) (δ := ρ) hρnonneg hρIneq ?_ ?_
    · exact le_of_lt hzNormLt |> fun h => le_trans hdx_le h
    · exact le_of_lt hzNormLt |> fun h => le_trans hdy_le h
  rcases
      helperForTheorem_35_8_nonempty_realSaddleSubdifferentialOn_of_mem_openRectangle
        (C := C) (D := D) (K := Kloc) hCopen hDopen hCconv hDconv hRealCC hxC hyD with
    ⟨pq, hpqMem⟩
  rcases pq with ⟨p, q⟩
  have hpqClose :
      ((p - uStar), (q - vStar)) ∈ splitEuclideanClosedBall (m := m) (n := n) η :=
    hNear x hxC y hyD hxySplit hpqMem
  have hpqNorms :
      ‖p - uStar‖ ≤ η ∧ ‖q - vStar‖ ≤ η :=
    helperForCorollary_35_7_1_coordinateNormBounds_of_mem_splitBall
      (m := m) (n := n) (r := η) (le_of_lt hηpos) hpqClose
  have huCoeffNorm : ‖uStar - p‖ ≤ η := by
    simpa [norm_sub_rev] using hpqNorms.1
  have huCoeff :
      l1Norm (uStar - p) ≤ (m : ℝ) * η := by
    exact
      (helperForTheorem_35_8_l1Norm_le_card_mul_norm (uStar - p)).trans
        (mul_le_mul_of_nonneg_left huCoeffNorm (by positivity))
  have hvCoeff :
      l1Norm (q - vStar) ≤ (n : ℝ) * η := by
    exact
      (helperForTheorem_35_8_l1Norm_le_card_mul_norm (q - vStar)).trans
        (mul_le_mul_of_nonneg_left hpqNorms.2 (by positivity))
  have hCoeffLe :
      l1Norm (uStar - p) + l1Norm (q - vStar) ≤ ε := by
    have hCoeffLeA :
        l1Norm (uStar - p) + l1Norm (q - vStar) ≤ ((m + n : ℕ) : ℝ) * η := by
      have hsum := add_le_add huCoeff hvCoeff
      simpa [Nat.cast_add, add_mul] using hsum
    have hratio : ((m + n : ℕ) : ℝ) / A ≤ (1 : ℝ) := by
      have hle : ((m + n : ℕ) : ℝ) ≤ A := by
        dsimp [A]
        exact_mod_cast (Nat.le_succ (m + n))
      exact (div_le_one hApos).2 hle
    have hεnonneg : 0 ≤ ε := le_of_lt hε
    have hAeta :
        ((m + n : ℕ) : ℝ) * η ≤ ε := by
      calc
        ((m + n : ℕ) : ℝ) * η = ε * (((m + n : ℕ) : ℝ) / A) := by
          simp [η, A, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        _ ≤ ε * 1 := by
          exact mul_le_mul_of_nonneg_left hratio hεnonneg
        _ = ε := by ring
    exact le_trans hCoeffLeA hAeta
  have hzEq :
      z - z0 = Fin.append dx dy := by
    ext i
    cases i using Fin.addCases <;>
      simp [dx, dy, x, y, z0, Fin.append, Pi.sub_apply, Fin.addCases_left, Fin.addCases_right]
  have hLsplit :
      L (z - z0) = dotProduct uStar dx + dotProduct vStar dy := by
    -- The packed linear functional splits over the first and second coordinate blocks.
    calc
      L (z - z0) = dotProduct (Fin.append uStar vStar) (z - z0) := by
        simp [L, helperForCorollary_25_5_1_dotProductContinuousLinearMap]
      _ = dotProduct (Fin.append uStar vStar) (Fin.append dx dy) := by
            simpa [hzEq]
      _ =
          dotProduct uStar (fun i => (Fin.append dx dy) (Fin.castAdd n i)) +
            dotProduct vStar (fun j => (Fin.append dx dy) (Fin.natAdd m j)) := by
              simpa using
                helperForTheorem_35_8_dotProduct_append
                  (m := m) (n := n) uStar vStar (Fin.append dx dy)
      _ = dotProduct uStar dx + dotProduct vStar dy := by
            simp [Fin.append]
  have hAppendNorm : ‖Fin.append dx dy‖ = ‖z - z0‖ := by
    simpa [hzEq] using congrArg norm hzEq.symm
  have hRemainder :
      ‖fLoc z - fLoc z0 - L (z - z0)‖ ≤
        (l1Norm (uStar - p) + l1Norm (q - vStar)) * ‖z - z0‖ := by
    -- The nearby subgradient error bound becomes the packed Fréchet remainder after rewriting.
    simpa [fLoc, Kloc, z0, dx, dy, x, y, hLsplit, hAppendNorm, Real.norm_eq_abs] using
      helperForTheorem_35_8_packedRealErrorBound_of_nearbySingletonSubgradients
        (C := C) (D := D) (Kloc := Kloc) (u := u) (v := v)
        (uStar := uStar) (vStar := vStar) huC hvD hBase hxC hyD hpqMem
  have hzNormNe : ‖z - z0‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzNe)
  have hScale :
      ‖z - z0‖⁻¹ * ‖fLoc z - fLoc z0 - L (z - z0)‖ ≤
        l1Norm (uStar - p) + l1Norm (q - vStar) := by
    have hMul :
        ‖z - z0‖⁻¹ * ‖fLoc z - fLoc z0 - L (z - z0)‖ ≤
          ‖z - z0‖⁻¹ *
            ((l1Norm (uStar - p) + l1Norm (q - vStar)) * ‖z - z0‖) := by
      exact mul_le_mul_of_nonneg_left hRemainder (by positivity)
    calc
      ‖z - z0‖⁻¹ * ‖fLoc z - fLoc z0 - L (z - z0)‖ ≤
          ‖z - z0‖⁻¹ *
            ((l1Norm (uStar - p) + l1Norm (q - vStar)) * ‖z - z0‖) := hMul
      _ =
          l1Norm (uStar - p) + l1Norm (q - vStar) := by
            have hReassoc :
                ‖z - z0‖⁻¹ *
                    ((l1Norm (uStar - p) + l1Norm (q - vStar)) * ‖z - z0‖) =
                  (l1Norm (uStar - p) + l1Norm (q - vStar)) *
                    (‖z - z0‖⁻¹ * ‖z - z0‖) := by
              ac_rfl
            rw [hReassoc]
            simp [hzNormNe]
  exact le_trans hScale hCoeffLe

/-- Helper for Theorem 35.8: once the local real rectangle kernel has singleton saddle
subdifferential at `(u, v)`, the remaining analytic task is to turn that local singleton control
into differentiability of the packed real map on the rectangle. -/
lemma helperForTheorem_35_8_packedRealDifferentiable_of_localSingletonSubgradient
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    {uStar : Fin m → ℝ} {vStar : Fin n → ℝ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (hCopen : IsOpen C) (huC : u ∈ C) (hCconv : Convex ℝ C)
    (hDopen : IsOpen D) (hvD : v ∈ D) (hDconv : Convex ℝ D)
    (hFiniteCD :
      ∀ x ∈ C, ∀ y ∈ D, K x y ≠ (⊤ : EReal) ∧ K x y ≠ (⊥ : EReal))
    (hLocal :
      let Kloc : (Fin m → ℝ) → (Fin n → ℝ) → ℝ := fun x y => (K x y).toReal
      IsRealConcaveConvexOn C D Kloc ∧
        realSaddleSubdifferentialOn C D Kloc u v = {(uStar, vStar)}) :
    let Kloc : (Fin m → ℝ) → (Fin n → ℝ) → ℝ := fun x y => (K x y).toReal
    let fLoc : (Fin (m + n) → ℝ) → ℝ :=
      fun z => Kloc (fun i => z (Fin.castAdd n i)) (fun j => z (Fin.natAdd m j))
    DifferentiableAt ℝ fLoc (Fin.append u v) := by
  let Kloc : (Fin m → ℝ) → (Fin n → ℝ) → ℝ := fun x y => (K x y).toReal
  let fLoc : (Fin (m + n) → ℝ) → ℝ :=
    fun z => Kloc (fun i => z (Fin.castAdd n i)) (fun j => z (Fin.natAdd m j))
  let z0 : Fin (m + n) → ℝ := Fin.append u v
  let L : (Fin (m + n) → ℝ) →L[ℝ] ℝ :=
    helperForCorollary_25_5_1_dotProductContinuousLinearMap (Fin.append uStar vStar)
  have hNormPunctured :
      Filter.Tendsto
        (fun z => ‖z - z0‖⁻¹ * ‖fLoc z - fLoc z0 - L (z - z0)‖)
        (𝓝[≠] z0) (𝓝 0) := by
    refine Metric.tendsto_nhds.2 ?_
    intro ε hε
    have hEventually :=
      helperForTheorem_35_8_puncturedPackedRealRemainder_small
        (K := K) (u := u) (v := v) (uStar := uStar) (vStar := vStar) (C := C) (D := D)
        hCopen huC hCconv hDopen hvD hDconv hFiniteCD hLocal (ε / 2) (by linarith)
    filter_upwards [hEventually] with z hz
    have hz_nonneg :
        0 ≤ ‖z - z0‖⁻¹ * ‖fLoc z - fLoc z0 - L (z - z0)‖ := by
      positivity
    have hz_lt : ‖z - z0‖⁻¹ * ‖fLoc z - fLoc z0 - L (z - z0)‖ < ε := by
      linarith
    simpa [Real.dist_eq, abs_of_nonneg hz_nonneg] using hz_lt
  have hNormAtBase :
      ‖z0 - z0‖⁻¹ * ‖fLoc z0 - fLoc z0 - L (z0 - z0)‖ = 0 := by
    -- At the center, the Fréchet remainder is zero by direct evaluation.
    simp [L, z0]
  have hNorm :
      Filter.Tendsto
        (fun z => ‖z - z0‖⁻¹ * ‖fLoc z - fLoc z0 - L (z - z0)‖)
        (𝓝 z0) (𝓝 0) := by
    have hNormPuncturedAt :
        Filter.Tendsto
          (fun z => ‖z - z0‖⁻¹ * ‖fLoc z - fLoc z0 - L (z - z0)‖)
          (𝓝[≠] z0)
          (𝓝 (‖z0 - z0‖⁻¹ * ‖fLoc z0 - fLoc z0 - L (z0 - z0)‖)) := by
      simpa [hNormAtBase] using hNormPunctured
    rw [← hNormAtBase]
    exact (continuousAt_iff_punctured_nhds).2 hNormPuncturedAt
  have hHasFDeriv : HasFDerivAt fLoc L z0 := by
    -- The punctured error estimate is exactly the `hasFDerivAt_iff_tendsto` criterion.
    exact (hasFDerivAt_iff_tendsto).2 hNorm
  exact hHasFDeriv.differentiableAt

/-- Helper for Theorem 35.8: a real Fréchet differentiability witness can be coerced to an
everywhere-finite `EReal` differentiability witness by taking the trivial `Set.univ` extension. -/
lemma helperForTheorem_35_8_ERealDifferentiableAt_coe_of_realDifferentiableAt
    {k : ℕ}
    {f : (Fin k → ℝ) → ℝ}
    {x : Fin k → ℝ}
    (hdiff : DifferentiableAt ℝ f x) :
    ERealDifferentiableAt (fun z => ((f z : ℝ) : EReal)) x := by
  let fExt : (Fin k → ℝ) → EReal :=
    fun z => ((f z : ℝ) : EReal) + indicatorFunction (Set.univ : Set (Fin k → ℝ)) z
  -- The Chapter 25 extension lemma applied on `Set.univ` produces exactly the desired coercion.
  rcases
      helperForCorollary_25_5_1_extension_differentiableAt_and_gradient_eq
        (hCopen := isOpen_univ) (C := (Set.univ : Set (Fin k → ℝ)))
        (f := f) (x := x) (by simp) hdiff with
    ⟨hExt, _hGradEq⟩
  simpa [fExt, indicatorFunction] using hExt

/-- Helper for Theorem 35.8: `EReal` differentiability transfers across equality on an open
neighborhood once the target function is finite on that neighborhood. -/
lemma helperForTheorem_35_8_ERealDifferentiableAt_of_eqOn_open
    {k : ℕ}
    {f g : (Fin k → ℝ) → EReal}
    {x : Fin k → ℝ}
    {W : Set (Fin k → ℝ)}
    (hWopen : IsOpen W)
    (hxW : x ∈ W)
    (hEqOn : ∀ z ∈ W, f z = g z)
    (hFiniteOn : ∀ z ∈ W, f z ≠ (⊤ : EReal) ∧ f z ≠ (⊥ : EReal))
    (hg : ERealDifferentiableAt g x) :
    ERealDifferentiableAt f x := by
  let grad : Fin k → ℝ := erealGradientAt hg
  have hWnhds : W ∈ nhds x := hWopen.mem_nhds hxW
  have hBaseFinite : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) := hFiniteOn x hxW
  have hWsubset_gDom :
      W ⊆ effectiveDomain (Set.univ : Set (Fin k → ℝ)) g := by
    intro z hzW
    have hzFinite : f z ≠ (⊤ : EReal) ∧ f z ≠ (⊥ : EReal) := hFiniteOn z hzW
    have hzEq : g z = f z := (hEqOn z hzW).symm
    simpa [effectiveDomain_eq, lt_top_iff_ne_top, hzEq] using hzFinite.1
  have hWithinW_f :
      ({z : Fin k → ℝ | z ≠ x} ∩ W) ∈
        nhdsWithin x
          ({z | z ≠ x} ∩ effectiveDomain (Set.univ : Set (Fin k → ℝ)) f) := by
    have hInter :
        (({z : Fin k → ℝ | z ≠ x} ∩ effectiveDomain (Set.univ : Set (Fin k → ℝ)) f) ∩ W) ∈
          nhdsWithin x
            ({z | z ≠ x} ∩ effectiveDomain (Set.univ : Set (Fin k → ℝ)) f) :=
      Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hWnhds)
    -- Intersecting with the neighborhood `W` is enough because points of the within-filter are
    -- already in the effective domain of `f`.
    exact
      Filter.mem_of_superset hInter (by
        intro z hz
        exact ⟨hz.1.1, hz.2⟩)
  have hGradWithinW :
      Filter.Tendsto (erealGradientErrorQuotient g x grad)
        (nhdsWithin x ({z : Fin k → ℝ | z ≠ x} ∩ W))
        (nhds 0) := by
    -- On the neighborhood `W`, the source filter for `g` may be shrunk because `W` consists of
    -- finite-valued points for `g` as well.
    exact
      (ERealDifferentiableAt.hasERealGradientAt hg).2.2.mono_left <|
        nhdsWithin_mono x (by
          intro z hz
          exact ⟨hz.1, hWsubset_gDom hz.2⟩)
  have hGradOn_f :
      Filter.Tendsto (erealGradientErrorQuotient g x grad)
        (nhdsWithin x
          ({z | z ≠ x} ∩ effectiveDomain (Set.univ : Set (Fin k → ℝ)) f))
        (nhds 0) := by
    -- The target punctured filter is eventually contained in `W`, so the within-`W` limit already
    -- controls it.
    exact hGradWithinW.mono_left (nhdsWithin_le_of_mem hWithinW_f)
  have hEventuallyEq :
      (fun z => erealGradientErrorQuotient f x grad z) =ᶠ[nhdsWithin x
        ({z | z ≠ x} ∩ effectiveDomain (Set.univ : Set (Fin k → ℝ)) f)]
        (fun z => erealGradientErrorQuotient g x grad z) := by
    filter_upwards [hWithinW_f] with z hzW
    have hEqBase : f x = g x := hEqOn x hxW
    have hEqz : f z = g z := hEqOn z hzW.2
    -- Inside `W`, both functions agree pointwise, so their error quotients coincide as well.
    simp [erealGradientErrorQuotient, hEqBase, hEqz]
  have hHasGrad_f : HasERealGradientAt f x grad := by
    refine ⟨hBaseFinite.1, hBaseFinite.2, ?_⟩
    -- Transfer the `g`-limit to `f` by eventual equality on the target punctured filter.
    exact Filter.Tendsto.congr' hEventuallyEq.symm hGradOn_f
  have hFiniteEventually_f :
      ∀ᶠ z in nhdsWithin x ({z | z ≠ x}),
        z ∈ effectiveDomain (Set.univ : Set (Fin k → ℝ)) f ∧ f z ≠ (⊥ : EReal) := by
    have hWWithin : W ∈ nhdsWithin x ({z : Fin k → ℝ | z ≠ x}) :=
      mem_nhdsWithin_of_mem_nhds hWnhds
    refine Filter.mem_of_superset hWWithin ?_
    intro z hzW
    have hzFinite : f z ≠ (⊤ : EReal) ∧ f z ≠ (⊥ : EReal) := hFiniteOn z hzW
    constructor
    · simpa [effectiveDomain_eq, lt_top_iff_ne_top] using hzFinite.1
    · exact hzFinite.2
  exact ⟨grad, hHasGrad_f, hFiniteEventually_f⟩

/-- Helper for Theorem 35.8: after the packed real map is differentiable on a finite open
rectangle, the Chapter 25 `+∞` extension principle lifts that local real differentiability back to
`EReal` differentiability of the packed saddle kernel. -/
lemma helperForTheorem_35_8_localPackedExtension_of_realRectangleKernel
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (hCopen : IsOpen C) (huC : u ∈ C)
    (hDopen : IsOpen D) (hvD : v ∈ D)
    (hFiniteCD :
      ∀ x ∈ C, ∀ y ∈ D, K x y ≠ (⊤ : EReal) ∧ K x y ≠ (⊥ : EReal))
    (hPackedDiff :
      let Kloc : (Fin m → ℝ) → (Fin n → ℝ) → ℝ := fun x y => (K x y).toReal
      let fLoc : (Fin (m + n) → ℝ) → ℝ :=
        fun z => Kloc (fun i => z (Fin.castAdd n i)) (fun j => z (Fin.natAdd m j))
      DifferentiableAt ℝ fLoc (Fin.append u v)) :
    ERealDifferentiableAt (packedSaddleKernel K) (Fin.append u v) := by
  let Kloc : (Fin m → ℝ) → (Fin n → ℝ) → ℝ := fun x y => (K x y).toReal
  let fLoc : (Fin (m + n) → ℝ) → ℝ :=
    fun z => Kloc (fun i => z (Fin.castAdd n i)) (fun j => z (Fin.natAdd m j))
  let W : Set (Fin (m + n) → ℝ) :=
    {z |
      (fun i : Fin m => z (Fin.castAdd n i)) ∈ C ∧
        (fun j : Fin n => z (Fin.natAdd m j)) ∈ D}
  have hPackedDiff' : DifferentiableAt ℝ fLoc (Fin.append u v) := by
    -- First unpack the `let`-bound local packed map from the hypothesis.
    simpa [Kloc, fLoc] using hPackedDiff
  have hWopen : IsOpen W := by
    -- The packed rectangle is open because both coordinate projections are continuous.
    have hFirstCont :
        Continuous (fun z : Fin (m + n) → ℝ => fun i : Fin m => z (Fin.castAdd n i)) := by
      fun_prop
    have hSecondCont :
        Continuous (fun z : Fin (m + n) → ℝ => fun j : Fin n => z (Fin.natAdd m j)) := by
      fun_prop
    simpa [W] using (hCopen.preimage hFirstCont).inter (hDopen.preimage hSecondCont)
  have hBaseMem : Fin.append u v ∈ W := by
    -- The base packed point splits back into the original coordinates `(u, v)`.
    refine ⟨?_, ?_⟩
    · simpa [W, Fin.append]
        using huC
    · simpa [W, Fin.append]
        using hvD
  have hLiftDiff :
      ERealDifferentiableAt (fun z : Fin (m + n) → ℝ => ((fLoc z : ℝ) : EReal))
        (Fin.append u v) := by
    -- Coercing the real packed map into `EReal` preserves differentiability on the whole space.
    exact
      helperForTheorem_35_8_ERealDifferentiableAt_coe_of_realDifferentiableAt
        (x := Fin.append u v) hPackedDiff'
  have hEqOn :
      ∀ z ∈ W,
        packedSaddleKernel K z =
          ((fLoc z : ℝ) : EReal) := by
    intro z hzW
    have hzFinite :
        K (fun i : Fin m => z (Fin.castAdd n i))
            (fun j : Fin n => z (Fin.natAdd m j)) ≠ (⊤ : EReal) ∧
          K (fun i : Fin m => z (Fin.castAdd n i))
            (fun j : Fin n => z (Fin.natAdd m j)) ≠ (⊥ : EReal) :=
      hFiniteCD _ hzW.1 _ hzW.2
    -- On the finite packed rectangle, `toReal` followed by coercion recovers the original kernel.
    simpa [packedSaddleKernel, Kloc, fLoc] using
      (EReal.coe_toReal hzFinite.1 hzFinite.2).symm
  have hFiniteOn :
      ∀ z ∈ W,
        packedSaddleKernel K z ≠ (⊤ : EReal) ∧ packedSaddleKernel K z ≠ (⊥ : EReal) := by
    intro z hzW
    -- The rectangle finiteness hypothesis is exactly the finiteness statement for the packed map.
    simpa [packedSaddleKernel] using hFiniteCD _ hzW.1 _ hzW.2
  -- The packed saddle kernel agrees with the finite-valued local packed real map on the open
  -- neighborhood `W`, so the local `EReal` differentiability witness transfers directly.
  exact
    helperForTheorem_35_8_ERealDifferentiableAt_of_eqOn_open
      (f := packedSaddleKernel K)
      (g := fun z : Fin (m + n) → ℝ => ((fLoc z : ℝ) : EReal))
      (x := Fin.append u v) (W := W)
      hWopen hBaseMem hEqOn hFiniteOn hLiftDiff

/-- Helper for Theorem 35.8: a finite local rectangle together with a linear mixed saddle
directional derivative should package into packed `EReal` differentiability. -/
lemma helperForTheorem_35_8_packedDifferentiable_of_linear_saddleDirectionalDerivative
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    {uStar : Fin m → ℝ} {vStar : Fin n → ℝ}
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFiniteRect :
      ∃ C : Set (Fin m → ℝ), ∃ D : Set (Fin n → ℝ),
        IsOpen C ∧ u ∈ C ∧ Convex ℝ C ∧
          IsOpen D ∧ v ∈ D ∧ Convex ℝ D ∧
            ∀ u' ∈ C, ∀ v' ∈ D, K u' v' ≠ (⊤ : EReal) ∧ K u' v' ≠ (⊥ : EReal))
    (hFirstSingleton : partialSubdifferentialInFirstVariable K u v = {uStar})
    (hSecondSingleton : partialSubdifferentialInSecondVariable K u v = {vStar})
    (hDir :
      ∀ u' v',
        IsSaddleDirectionalDerivativeAt K u v u' v'
          (((((∑ i : Fin m, uStar i * u' i) + ∑ j : Fin n, vStar j * v' j) : ℝ) : EReal))) :
    ERealDifferentiableAt (packedSaddleKernel K) (Fin.append u v) := by
  rcases
      helperForTheorem_35_8_localRealSingletonSubgradient_onRectangle
      (K := K) (u := u) (v := v) (uStar := uStar) (vStar := vStar)
      hK hFiniteRect hFirstSingleton hSecondSingleton hDir with
    ⟨C, D, hCopen, huC, hCconv, hDopen, hvD, hDconv, hFiniteCD, hLocal⟩
  have hPackedDiff :=
    helperForTheorem_35_8_packedRealDifferentiable_of_localSingletonSubgradient
      (K := K) (u := u) (v := v) (uStar := uStar) (vStar := vStar)
      (C := C) (D := D)
      hCopen huC hCconv hDopen hvD hDconv hFiniteCD hLocal
  -- Route correction: the converse packaging is now split into a real differentiability step on
  -- the finite rectangle and a separate Chapter 25 extension step.
  exact
    helperForTheorem_35_8_localPackedExtension_of_realRectangleKernel
      (K := K) (u := u) (v := v) (C := C) (D := D)
      hCopen huC hDopen hvD hFiniteCD hPackedDiff

/-- Theorem 35.8, with the local-finiteness qualification made explicit for extended-real
kernels. Differentiability gives a unique saddle subgradient. Conversely, uniqueness gives
differentiability once `K` is finite on an open convex rectangle around the base point.

The qualification is necessary for the present extended-real API: singleton coordinate
subdifferentials alone do not exclude a separately convex-concave `⊤/⊥` checkerboard away
from the two coordinate axes. -/
theorem section35_theorem35_8
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal)) :
    ((hDiff : ERealDifferentiableAt (packedSaddleKernel K) (Fin.append u v)) →
      let grad : (Fin m → ℝ) × (Fin n → ℝ) :=
        packedSaddleKernelGradientPairAt (K := K) (u := u) (v := v) hDiff
      grad ∈ productSubdifferentialAt K u v ∧
        ∀ g : (Fin m → ℝ) × (Fin n → ℝ),
          g ∈ productSubdifferentialAt K u v → g = grad) ∧
    ((hFiniteRect :
        ∃ C : Set (Fin m → ℝ), ∃ D : Set (Fin n → ℝ),
          IsOpen C ∧ u ∈ C ∧ Convex ℝ C ∧
            IsOpen D ∧ v ∈ D ∧ Convex ℝ D ∧
              ∀ u' ∈ C, ∀ v' ∈ D,
                K u' v' ≠ (⊤ : EReal) ∧ K u' v' ≠ (⊥ : EReal)) →
      (∃! g : (Fin m → ℝ) × (Fin n → ℝ),
          g ∈ productSubdifferentialAt K u v) →
        ERealDifferentiableAt (packedSaddleKernel K) (Fin.append u v)) := by
  constructor
  · intro hDiff
    let grad : (Fin m → ℝ) × (Fin n → ℝ) :=
      packedSaddleKernelGradientPairAt (K := K) (u := u) (v := v) hDiff
    -- The forward direction is reduced to uniqueness of the first and second partial
    -- subdifferentials for the split packed gradient.
    have hpartials :=
      helperForTheorem_35_8_forward_unique_partial_subgradients
        (K := K) (u := u) (v := v) hK hDiff
    rcases hpartials with ⟨⟨hFirstMem, hFirstUnique⟩, ⟨hSecondMem, hSecondUnique⟩⟩
    refine ⟨?_, ?_⟩
    · -- Membership in the product subdifferential is just membership in both factors.
      simpa [grad, productSubdifferentialAt] using And.intro hFirstMem hSecondMem
    · intro g hg
      -- Unpack the product membership and compare each component with the unique partial witness.
      rcases g with ⟨gFirst, gSecond⟩
      have hFirstEq : gFirst = grad.1 := hFirstUnique gFirst hg.1
      have hSecondEq : gSecond = grad.2 := hSecondUnique gSecond hg.2
      exact Prod.ext hFirstEq hSecondEq
  · intro hFiniteRect huniq
    rcases
        helperForTheorem_35_8_unique_productSubgradient_gives_unique_partials
          (K := K) (u := u) (v := v) huniq with
      ⟨uStar, vStar, hFirstSingleton, hSecondSingleton⟩
    -- The qualified converse follows the textbook analytic route on the supplied finite
    -- rectangle: Theorem 35.6 gives the linear directional derivative, which is then packaged
    -- back into differentiability of the packed kernel.
    have hLinearDir :=
      helperForTheorem_35_8_linear_saddleDirectionalDerivative_of_singleton_partials
        (K := K) (u := u) (v := v) (uStar := uStar) (vStar := vStar)
        hK hFinite hFiniteRect hFirstSingleton hSecondSingleton
    exact
      helperForTheorem_35_8_packedDifferentiable_of_linear_saddleDirectionalDerivative
        (K := K) (u := u) (v := v) (uStar := uStar) (vStar := vStar)
        hK hFiniteRect hFirstSingleton hSecondSingleton hLinearDir

-- Proof sketch: apply Theorem 35.8 to identify differentiability of the packed saddle kernel with
-- uniqueness of the saddle subgradient at `(u, v)`. On a neighborhood where `K` is finite,
-- Theorem 35.6 produces the real directional-derivative kernel, and Theorem 25.2 applied to the
-- packed map upgrades linearity of this directional derivative, or merely the existence of the
-- `m + n` finite coordinate partial derivatives, to differentiability.
/-- Helper for Corollary 35.8.1: a finite neighborhood around `(u, v)` contains an open convex
product rectangle on which `K` stays finite. -/
lemma helperForCorollary_35_8_1_finiteRectangle_of_neighborhood
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hNeighborhood : SaddleKernelFiniteOnNeighborhoodAt K u v) :
    ∃ C : Set (Fin m → ℝ), ∃ D : Set (Fin n → ℝ),
      IsOpen C ∧ u ∈ C ∧ Convex ℝ C ∧
        IsOpen D ∧ v ∈ D ∧ Convex ℝ D ∧
          ∀ u' ∈ C, ∀ v' ∈ D, K u' v' ≠ (⊤ : EReal) ∧ K u' v' ≠ (⊥ : EReal) := by
  rcases hNeighborhood with ⟨N, hNopen, huvN, hFiniteN⟩
  rcases Metric.isOpen_iff.mp hNopen (u, v) huvN with ⟨ε, hεpos, hBallSubset⟩
  refine ⟨Metric.ball u ε, Metric.ball v ε, Metric.isOpen_ball, ?_, convex_ball u ε,
    Metric.isOpen_ball, ?_, convex_ball v ε, ?_⟩
  · simpa [Metric.mem_ball] using hεpos
  · simpa [Metric.mem_ball] using hεpos
  · intro u' hu' v' hv'
    have hpBall : (u', v') ∈ Metric.ball (u, v) ε := by
      simpa [Metric.mem_ball, Prod.dist_eq, max_lt_iff] using And.intro hu' hv'
    exact hFiniteN (u', v') (hBallSubset hpBall)

/-- Helper for Corollary 35.8.1: first-variable partial subgradients are exactly the subgradients
of the convex slice `x ↦ -K x v` with the expected sign change. -/
lemma helperForCorollary_35_8_1_negFirstSliceSubgradient_iff_partialFirstMem
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (uStar : Fin m → ℝ) :
    IsSubgradientAt (fun x : Fin m → ℝ => -K x v) u (dotProductEquiv ℝ (Fin m) (-uStar)) ↔
      uStar ∈ partialSubdifferentialInFirstVariable K u v := by
  constructor
  · intro hSub
    intro z
    let S : EReal := (((∑ i : Fin m, uStar i * (z i - u i) : ℝ)) : EReal)
    -- Rewrite the subgradient inequality on the negated slice into the original saddle inequality.
    have hPair :
        (((dotProductEquiv ℝ (Fin m) (-uStar)) (z - u) : ℝ) : EReal) = -S := by
      simp [S, dotProductEquiv_apply_apply, dotProduct, sub_eq_add_neg]
    have hSlice :
        -K u v + (((dotProductEquiv ℝ (Fin m) (-uStar)) (z - u) : ℝ) : EReal) ≤ -K z v := by
      simpa using hSub z
    have hSTop : S ≠ (⊤ : EReal) := by simp [S]
    have hSBot : S ≠ (⊥ : EReal) := by simp [S]
    have hRewrite :
        -(K u v + S) = -K u v + (((dotProductEquiv ℝ (Fin m) (-uStar)) (z - u) : ℝ) : EReal) := by
      rw [hPair]
      rw [EReal.neg_add (Or.inl hFinite.2) (Or.inr hSBot)]
      simp [sub_eq_add_neg]
    have hNeg :
        -(K u v + S) ≤ -K z v := by
      simpa [hRewrite] using hSlice
    have hOrig : K z v ≤ K u v + S := (EReal.neg_le_neg_iff).mp hNeg
    simpa [S, helperForTheorem_25_2_coe_finset_sum_real_toEReal] using hOrig
  · intro hMem
    intro z
    let S : EReal := (((∑ i : Fin m, uStar i * (z i - u i) : ℝ)) : EReal)
    -- The saddle inequality is equivalent to the subgradient inequality after negation.
    have hOrig : K z v ≤ K u v + S := by
      simpa [S, helperForTheorem_25_2_coe_finset_sum_real_toEReal] using hMem z
    have hNeg : -(K u v + S) ≤ -K z v := (EReal.neg_le_neg_iff).mpr hOrig
    have hPair :
        (((dotProductEquiv ℝ (Fin m) (-uStar)) (z - u) : ℝ) : EReal) = -S := by
      simp [S, dotProductEquiv_apply_apply, dotProduct, sub_eq_add_neg]
    have hSTop : S ≠ (⊤ : EReal) := by simp [S]
    have hSBot : S ≠ (⊥ : EReal) := by simp [S]
    have hRewrite :
        -(K u v + S) = -K u v + (((dotProductEquiv ℝ (Fin m) (-uStar)) (z - u) : ℝ) : EReal) := by
      rw [hPair]
      rw [EReal.neg_add (Or.inl hFinite.2) (Or.inr hSBot)]
      simp [sub_eq_add_neg]
    simpa [hRewrite] using hNeg

/-- Helper for Corollary 35.8.1: on a finite rectangle, a linear saddle directional derivative
forces both partial subdifferentials to be singletons. -/
lemma helperForCorollary_35_8_1_singletonPartials_of_linearSaddleDirectionalDerivative
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    {uStar : Fin m → ℝ} {vStar : Fin n → ℝ}
    (hK : IsGloballyConcaveConvexERealKernel K)
    (hFiniteRect :
      ∃ C : Set (Fin m → ℝ), ∃ D : Set (Fin n → ℝ),
        IsOpen C ∧ u ∈ C ∧ Convex ℝ C ∧
          IsOpen D ∧ v ∈ D ∧ Convex ℝ D ∧
            ∀ u' ∈ C, ∀ v' ∈ D, K u' v' ≠ (⊤ : EReal) ∧ K u' v' ≠ (⊥ : EReal))
    (hDir :
      ∀ u' v',
        IsSaddleDirectionalDerivativeAt K u v u' v'
          (((((∑ i : Fin m, uStar i * u' i) + ∑ j : Fin n, vStar j * v' j) : ℝ) : EReal))) :
    partialSubdifferentialInFirstVariable K u v = {uStar} ∧
      partialSubdifferentialInSecondVariable K u v = {vStar} := by
  classical
  rcases hFiniteRect with ⟨C, D, hCopen, huC, hCconv, hDopen, hvD, hDconv, hFiniteCD⟩
  have hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal) := hFiniteCD u huC v hvD
  rcases
      helperForTheorem_35_6_splitKernel_structure
        (C := C) (D := D) (K := K)
        hCopen hDopen hCconv hDconv hK hFiniteCD huC hvD with
    ⟨Kdir, hKdirFormula, _hPos, _hCC, _hSplit⟩
  have hAxisDir :=
    helperForTheorem_35_6_axisDirectionalDerivatives_match_splitKernel
      (C := C) (D := D) (K := K)
      hCopen hDopen hK hFiniteCD huC hvD hKdirFormula
  have hAxisFormula :=
    helperForTheorem_35_6_splitKernel_axisFormula
      (C := C) (D := D) (K := K)
      hCopen hDopen hK hFiniteCD huC hvD hKdirFormula
  rcases
      helperForTheorem_35_6_firstSlice_directionalDerivativeData
        (C := C) (D := D) (K := K)
        hCopen hDopen hK hFiniteCD huC hvD with
    ⟨_hfProper, _hDfProper, _hDfPos, _hDfConv, _hDfZero, hDfFinite⟩
  rcases
      helperForTheorem_35_6_secondSlice_directionalDerivativeData
        (C := C) (D := D) (K := K)
        hCopen hDopen hK hFiniteCD huC hvD with
    ⟨_hgProper, _hDgProper, _hDgPos, _hDgConv, _hDgZero, hDgFinite⟩

  have hAxisFirstReal :
      ∀ u' : Fin m → ℝ, Kdir u' 0 = ∑ i : Fin m, uStar i * u' i := by
    intro u'
    have hEq :
        (Kdir u' 0 : EReal) =
          (((((∑ i : Fin m, uStar i * u' i) + ∑ j : Fin n, vStar j * (0 : Fin n → ℝ) j) : ℝ) :
            EReal)) := by
      exact tendsto_nhds_unique (hAxisDir.1 u').2.2 (hDir u' 0).2.2
    simpa using (EReal.coe_eq_coe_iff).mp hEq
  have hAxisSecondReal :
      ∀ v' : Fin n → ℝ, Kdir 0 v' = ∑ j : Fin n, vStar j * v' j := by
    intro v'
    have hEq :
        (Kdir 0 v' : EReal) =
          (((((∑ i : Fin m, uStar i * (0 : Fin m → ℝ) i) + ∑ j : Fin n, vStar j * v' j) : ℝ) :
            EReal)) := by
      exact tendsto_nhds_unique (hAxisDir.2 v').2.2 (hDir 0 v').2.2
    simpa using (EReal.coe_eq_coe_iff).mp hEq

  have hFirstUpper :
      ∀ y : Fin m → ℝ,
      upperDirectionalDerivativeAt (fun x : Fin m → ℝ => -K x v) u y =
          (((((-uStar) ⬝ᵥ y : ℝ) : ℝ) : EReal)) := by
    intro y
    have hReal : Kdir y 0 = -(upperDirectionalDerivativeAt (fun x : Fin m → ℝ => -K x v) u y).toReal :=
      hAxisFormula.1 y
    have hToReal :
        (upperDirectionalDerivativeAt (fun x : Fin m → ℝ => -K x v) u y).toReal =
          -∑ i : Fin m, uStar i * y i := by
      linarith [hReal, hAxisFirstReal y]
    have hFiniteUpper :
        upperDirectionalDerivativeAt (fun x : Fin m → ℝ => -K x v) u y ≠ (⊤ : EReal) ∧
          upperDirectionalDerivativeAt (fun x : Fin m → ℝ => -K x v) u y ≠ (⊥ : EReal) :=
      hDfFinite y
    -- Replace the directional derivative by its finite `toReal` value and then simplify the sign.
    calc
      upperDirectionalDerivativeAt (fun x : Fin m → ℝ => -K x v) u y =
          ((((upperDirectionalDerivativeAt (fun x : Fin m → ℝ => -K x v) u y).toReal : ℝ) :
            EReal)) := by
              symm
              exact EReal.coe_toReal hFiniteUpper.1 hFiniteUpper.2
      _ = ((((-uStar) ⬝ᵥ y : ℝ) : ℝ) : EReal) := by
            simp [hToReal, dotProduct]
  have hSecondUpper :
      ∀ y : Fin n → ℝ,
        upperDirectionalDerivativeAt (K u) v y =
          (((((vStar) ⬝ᵥ y : ℝ) : ℝ) : EReal)) := by
    intro y
    have hReal : Kdir 0 y = (upperDirectionalDerivativeAt (K u) v y).toReal :=
      hAxisFormula.2 y
    have hToReal :
        (upperDirectionalDerivativeAt (K u) v y).toReal =
          ∑ j : Fin n, vStar j * y j := by
      linarith [hReal, hAxisSecondReal y]
    have hFiniteUpper :
        upperDirectionalDerivativeAt (K u) v y ≠ (⊤ : EReal) ∧
          upperDirectionalDerivativeAt (K u) v y ≠ (⊥ : EReal) :=
      hDgFinite y
    -- The second-variable slice derivative is already the dot product with `vStar`.
    calc
      upperDirectionalDerivativeAt (K u) v y =
          ((((upperDirectionalDerivativeAt (K u) v y).toReal : ℝ) : EReal)) := by
            symm
            exact EReal.coe_toReal hFiniteUpper.1 hFiniteUpper.2
      _ = (((((vStar) ⬝ᵥ y : ℝ) : ℝ) : EReal)) := by
            simp [hToReal, dotProduct]

  have hFirstSliceFinite :
      (fun x : Fin m → ℝ => -K x v) u ≠ (⊤ : EReal) ∧
        (fun x : Fin m → ℝ => -K x v) u ≠ (⊥ : EReal) := by
    exact ⟨by simpa using hFinite.2, by simpa using hFinite.1⟩
  have hFirstUnique :
      ∃! w : Fin m → ℝ,
        IsSubgradientAt (fun x : Fin m → ℝ => -K x v) u (dotProductEquiv ℝ (Fin m) w) :=
    helperForTheorem_25_2_uniqueSubgradient_of_linearDirectionalDerivative
      (f := fun x : Fin m → ℝ => -K x v)
      (hf := hK.1 v) (x := u) (hx := hFirstSliceFinite) (g := -uStar) hFirstUpper
  have hSecondUnique :
      ∃! w : Fin n → ℝ,
        IsSubgradientAt (K u) v (dotProductEquiv ℝ (Fin n) w) :=
    helperForTheorem_25_2_uniqueSubgradient_of_linearDirectionalDerivative
      (f := K u) (hf := hK.2 u) (x := v) (hx := hFinite) (g := vStar) hSecondUpper

  have hFirstTarget :
      IsSubgradientAt (fun x : Fin m → ℝ => -K x v) u (dotProductEquiv ℝ (Fin m) (-uStar)) := by
    have hiff :=
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        (fun x : Fin m → ℝ => -K x v) (hK.1 v) u hFirstSliceFinite
        (dotProductEquiv ℝ (Fin m) (-uStar))).1
    apply hiff.mpr
    intro y
    simpa using le_of_eq (hFirstUpper y).symm
  have hSecondTarget :
      IsSubgradientAt (K u) v (dotProductEquiv ℝ (Fin n) vStar) := by
    have hiff :=
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        (K u) (hK.2 u) v hFinite (dotProductEquiv ℝ (Fin n) vStar)).1
    apply hiff.mpr
    intro y
    simpa using le_of_eq (hSecondUpper y).symm

  refine ⟨?_, ?_⟩
  · rcases hFirstUnique with ⟨w0, _hw0, hwuniq⟩
    have hw0Eq : w0 = -uStar := by
      exact (hwuniq (-uStar) hFirstTarget).symm
    -- Translate the unique convex-slice subgradient back to the saddle partial subdifferential.
    ext w
    constructor
    · intro hw
      have hwSub :
          IsSubgradientAt (fun x : Fin m → ℝ => -K x v) u (dotProductEquiv ℝ (Fin m) (-w)) :=
        (helperForCorollary_35_8_1_negFirstSliceSubgradient_iff_partialFirstMem
          (K := K) (u := u) (v := v) hFinite w).2 hw
      have hEqNeg : -w = w0 := hwuniq (-w) hwSub
      have hEqNeg' : -w = -uStar := by simpa [hw0Eq] using hEqNeg
      have hEq : w = uStar := by simpa using congrArg Neg.neg hEqNeg'
      simpa [hEq]
    · intro hw
      have hEq : w = uStar := by simpa using hw
      simpa [hEq] using
        (helperForCorollary_35_8_1_negFirstSliceSubgradient_iff_partialFirstMem
          (K := K) (u := u) (v := v) hFinite uStar).1 hFirstTarget
  · rcases hSecondUnique with ⟨w0, _hw0, hwuniq⟩
    have hw0Eq : w0 = vStar := by
      exact (hwuniq vStar hSecondTarget).symm
    -- The second-variable bridge is the standard slice subgradient equivalence from Text 35.6.7.
    ext w
    constructor
    · intro hw
      have hwSub : IsSubgradientAt (K u) v (dotProductEquiv ℝ (Fin n) w) := by
        have : dotProductEquiv ℝ (Fin n) w ∈ subdifferentialAt (K u) v :=
          (helperForText_35_6_7_secondSliceSubgradient_iff_partialSecondMem
            (K := K) (u := u) (v := v) (vStar := w)).2 hw
        simpa [subdifferentialAt] using this
      have hEq : w = w0 := hwuniq w hwSub
      simpa [hw0Eq] using hEq
    · intro hw
      have hEq : w = vStar := by simpa using hw
      have : dotProductEquiv ℝ (Fin n) vStar ∈ subdifferentialAt (K u) v := by
        simpa [subdifferentialAt] using hSecondTarget
      simpa [hEq] using
        (helperForText_35_6_7_secondSliceSubgradient_iff_partialSecondMem
          (K := K) (u := u) (v := v) (vStar := vStar)).1 this

/-- Helper for Corollary 35.8.1: the reflected first-slice quotient is exactly the negative of the
packed quotient in the matching first-block direction. -/
lemma helperForCorollary_35_8_1_reflectedFirstSliceQuotient_eq_negPackedQuotient
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (uDir : Fin m → ℝ) (t : ℝ) :
    directionalDifferenceQuotientAt (fun x : Fin m → ℝ => -K (-x) v) (-u) uDir t =
      -directionalDifferenceQuotientAt (packedSaddleKernel K) (Fin.append u v)
        (Fin.append (-uDir) (0 : Fin n → ℝ)) t := by
  have harg :
      -((-u) + t • uDir) = u + t • (-uDir) := by
    -- Reflecting the translated point moves the sign onto the direction.
    funext i
    simp [Pi.add_apply, Pi.smul_apply]
    ring
  have hnegNumerator :
      -K (u + -(t • uDir)) v - -K u v =
        -(K (u + -(t • uDir)) v - K u v) := by
    -- Base-point finiteness is enough to rewrite the reflected numerator as a negated quotient
    -- numerator; the shifted value may still be infinite.
    calc
      -K (u + -(t • uDir)) v - -K u v =
          -K (u + -(t • uDir)) v + K u v := by
            rw [sub_eq_add_neg, neg_neg]
      _ = -(K (u + -(t • uDir)) v - K u v) := by
            symm
            exact EReal.neg_sub (Or.inr hFinite.2) (Or.inr hFinite.1)
  have hReflected :
      directionalDifferenceQuotientAt (fun x : Fin m → ℝ => -K (-x) v) (-u) uDir t =
        (-(K (u + -(t • uDir)) v - K u v)) / (t : EReal) := by
    -- Unfold the reflected quotient after rewriting the translated argument explicitly.
    simp [directionalDifferenceQuotientAt, harg, hnegNumerator, Pi.add_apply, Pi.smul_apply]
  have hPacked :
      directionalDifferenceQuotientAt (packedSaddleKernel K) (Fin.append u v)
          (Fin.append (-uDir) (0 : Fin n → ℝ)) t =
        (K (u + -(t • uDir)) v - K u v) / (t : EReal) := by
    -- The packed direction only perturbs the first block, with the second block fixed at `v`.
    have huUpdate : u + -(t • uDir) = (fun i : Fin m => u i + -(t * uDir i)) := by
      funext i
      simp [Pi.add_apply, Pi.smul_apply]
    simp [directionalDifferenceQuotientAt, packedSaddleKernel, huUpdate, Pi.add_apply, Pi.smul_apply]
  -- Both quotients are the same numerator, up to the outer negation.
  rw [hReflected, hPacked]
  simp [div_eq_mul_inv, EReal.neg_mul]

/-- Helper for Corollary 35.8.1: along the positive `i`th first-variable basis vector, the
reflected slice quotient equals the negative packed quotient along the negative packed basis. -/
lemma helperForCorollary_35_8_1_reflectedFirstBasisQuotient_eq_negPackedNegativeBasisQuotient
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (i : Fin m) (t : ℝ) :
    directionalDifferenceQuotientAt (fun x : Fin m → ℝ => -K (-x) v) (-u)
        (Pi.single i (1 : ℝ)) t =
      -directionalDifferenceQuotientAt (packedSaddleKernel K) (Fin.append u v)
        (-(Pi.single (Fin.castAdd n i) (1 : ℝ) : Fin (m + n) → ℝ)) t := by
  have hdir :
      (Fin.append (-(Pi.single i (1 : ℝ) : Fin m → ℝ)) (0 : Fin n → ℝ) :
          Fin (m + n) → ℝ) =
        -(Pi.single (Fin.castAdd n i) (1 : ℝ) : Fin (m + n) → ℝ) := by
    -- Identify the first and second packed blocks with the corresponding coordinates of the
    -- target packed basis vector, then reassemble them via `Fin.append_castAdd_natAdd`.
    calc
      (Fin.append (-(Pi.single i (1 : ℝ) : Fin m → ℝ)) (0 : Fin n → ℝ) :
          Fin (m + n) → ℝ) =
          Fin.append
            (fun i' : Fin m =>
              (-(Pi.single (Fin.castAdd n i) (1 : ℝ) : Fin (m + n) → ℝ)) (Fin.castAdd n i'))
            (fun j : Fin n =>
              (-(Pi.single (Fin.castAdd n i) (1 : ℝ) : Fin (m + n) → ℝ)) (Fin.natAdd m j)) := by
            apply congrArg₂ Fin.append
            · funext x
              simp [Pi.single_apply, Pi.neg_apply]
            · funext x
              have hne : Fin.natAdd m x ≠ Fin.castAdd n i := by
                intro h
                have hval := congrArg Fin.val h
                simp [Fin.natAdd, Fin.castAdd] at hval
                omega
              simp [Pi.single_apply, Pi.neg_apply, hne]
      _ = -(Pi.single (Fin.castAdd n i) (1 : ℝ) : Fin (m + n) → ℝ) := by
            simpa using
              (Fin.append_castAdd_natAdd
                (f := -(Pi.single (Fin.castAdd n i) (1 : ℝ) : Fin (m + n) → ℝ)))
  -- Specialize the reflected quotient identity to the positive first-block basis direction.
  simpa [hdir] using
    (helperForCorollary_35_8_1_reflectedFirstSliceQuotient_eq_negPackedQuotient
      (K := K) (u := u) (v := v) hFinite (Pi.single i (1 : ℝ)) t)

/-- Helper for Corollary 35.8.1: along the negative `i`th first-variable basis vector, the
reflected slice quotient equals the negative packed quotient along the positive packed basis. -/
lemma helperForCorollary_35_8_1_reflectedNegativeBasisQuotient_eq_negPackedPositiveBasisQuotient
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (i : Fin m) (t : ℝ) :
    directionalDifferenceQuotientAt (fun x : Fin m → ℝ => -K (-x) v) (-u)
        (-(Pi.single i (1 : ℝ) : Fin m → ℝ)) t =
      -directionalDifferenceQuotientAt (packedSaddleKernel K) (Fin.append u v)
        (Pi.single (Fin.castAdd n i) (1 : ℝ)) t := by
  have hdir :
      (Fin.append (Pi.single i (1 : ℝ)) (0 : Fin n → ℝ) : Fin (m + n) → ℝ) =
        (Pi.single (Fin.castAdd n i) (1 : ℝ) : Fin (m + n) → ℝ) := by
    -- Flipping the reflected direction turns the packed first block into the positive basis
    -- vector with zero second block.
    calc
      (Fin.append (Pi.single i (1 : ℝ)) (0 : Fin n → ℝ) : Fin (m + n) → ℝ) =
          Fin.append
            (fun i' : Fin m =>
              (Pi.single (Fin.castAdd n i) (1 : ℝ) : Fin (m + n) → ℝ) (Fin.castAdd n i'))
            (fun j : Fin n =>
              (Pi.single (Fin.castAdd n i) (1 : ℝ) : Fin (m + n) → ℝ) (Fin.natAdd m j)) := by
            apply congrArg₂ Fin.append
            · funext x
              simp [Pi.single_apply]
            · funext x
              have hne : Fin.natAdd m x ≠ Fin.castAdd n i := by
                intro h
                have hval := congrArg Fin.val h
                simp [Fin.natAdd, Fin.castAdd] at hval
                omega
              simp [Pi.single_apply, hne]
      _ = (Pi.single (Fin.castAdd n i) (1 : ℝ) : Fin (m + n) → ℝ) := by
            simpa using
              (Fin.append_castAdd_natAdd
                (f := (Pi.single (Fin.castAdd n i) (1 : ℝ) : Fin (m + n) → ℝ)))
  -- Specialize the same identity to the negative first-block basis direction.
  simpa [hdir, neg_neg] using
    (helperForCorollary_35_8_1_reflectedFirstSliceQuotient_eq_negPackedQuotient
      (K := K) (u := u) (v := v) hFinite (-(Pi.single i (1 : ℝ) : Fin m → ℝ)) t)



end Section35
end Chap07

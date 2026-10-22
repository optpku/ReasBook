/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section39_part8

open scoped Pointwise
open scoped RealInnerProductSpace
open scoped BigOperators

section Chap08
section Section39

namespace ConvexProcess

/-- Helper for Theorem 39.4: for a fixed covector `x*`, concavity of the parameter section
`u ↦ K(u,x*)`, together with positive homogeneity and the exclusion of `⊥`, yields the
superadditivity inequality needed for the reconstructed process law. -/
lemma helperForTheorem_39_4_parameterSection_superadditive
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hConc :
      ∀ xStar : Fin n → ℝ,
        IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) (fun u : Fin m → ℝ => K u xStar))
    (hNoBot : HasNoBotValuesBifunction K)
    (hHom : IsNormalizedBihomogeneousERealBifunction (m := m) (n := n) K) :
    ∀ u₁ u₂ : Fin m → ℝ, ∀ xStar : Fin n → ℝ,
      K u₁ xStar + K u₂ xStar ≤ K (u₁ + u₂) xStar := by
  intro u₁ u₂ xStar
  by_cases hTop1 : K u₁ xStar = (⊤ : EReal)
  · have hHalfTop : (((1 / 2 : ℝ) : EReal) * K u₁ xStar) = ⊤ := by
      rw [hTop1]
      simpa using (EReal.coe_mul_top_of_pos (x := (1 / 2 : ℝ)) (by norm_num))
    have hHalf₂_ne_bot : (((1 / 2 : ℝ) : EReal) * K u₂ xStar) ≠ (⊥ : EReal) := by
      exact ereal_mul_ne_bot_of_pos (by norm_num) (hNoBot u₂ xStar)
    have hMid :
        (((1 / 2 : ℝ) : EReal) * K u₁ xStar +
            (((1 / 2 : ℝ) : EReal) * K u₂ xStar)) ≤
          K (((1 / 2 : ℝ) • u₁) + ((1 / 2 : ℝ) • u₂)) xStar :=
      hConc xStar (by simp) (by simp) (show 0 ≤ (1 / 2 : ℝ) by norm_num)
        (show 0 ≤ (1 / 2 : ℝ) by norm_num) (by norm_num) (by simp)
    have hMidTop :
        K (((1 / 2 : ℝ) • u₁) + ((1 / 2 : ℝ) • u₂)) xStar = (⊤ : EReal) := by
      have hLeftTop :
          (((1 / 2 : ℝ) : EReal) * K u₁ xStar +
              (((1 / 2 : ℝ) : EReal) * K u₂ xStar)) = (⊤ : EReal) := by
        rw [hHalfTop]
        exact EReal.top_add_of_ne_bot hHalf₂_ne_bot
      rw [hLeftTop] at hMid
      exact top_le_iff.mp hMid
    have hScale :
        K (u₁ + u₂) xStar =
          ((2 : ℝ) : EReal) * K (((1 / 2 : ℝ) • u₁) + ((1 / 2 : ℝ) • u₂)) xStar := by
      have := (hHom.2 2 zero_lt_two (((1 / 2 : ℝ) • u₁) + ((1 / 2 : ℝ) • u₂)) xStar).1
      simpa [two_smul, add_comm, add_left_comm, add_assoc, smul_add] using this
    have hSumTop : K (u₁ + u₂) xStar = (⊤ : EReal) := by
      rw [hScale, hMidTop]
      simpa using (EReal.coe_mul_top_of_pos (x := (2 : ℝ)) zero_lt_two)
    have hLeftTop : K u₁ xStar + K u₂ xStar = (⊤ : EReal) := by
      simpa [hTop1] using EReal.top_add_of_ne_bot (hNoBot u₂ xStar)
    rw [hLeftTop, hSumTop]
  · by_cases hTop2 : K u₂ xStar = (⊤ : EReal)
    · have hHalfTop : (((1 / 2 : ℝ) : EReal) * K u₂ xStar) = ⊤ := by
        rw [hTop2]
        simpa using (EReal.coe_mul_top_of_pos (x := (1 / 2 : ℝ)) (by norm_num))
      have hHalf₁_ne_bot : (((1 / 2 : ℝ) : EReal) * K u₁ xStar) ≠ (⊥ : EReal) := by
        exact ereal_mul_ne_bot_of_pos (by norm_num) (hNoBot u₁ xStar)
      have hMid :
          (((1 / 2 : ℝ) : EReal) * K u₁ xStar +
              (((1 / 2 : ℝ) : EReal) * K u₂ xStar)) ≤
            K (((1 / 2 : ℝ) • u₁) + ((1 / 2 : ℝ) • u₂)) xStar :=
        hConc xStar (by simp) (by simp) (show 0 ≤ (1 / 2 : ℝ) by norm_num)
          (show 0 ≤ (1 / 2 : ℝ) by norm_num) (by norm_num) (by simp)
      have hMidTop :
          K (((1 / 2 : ℝ) • u₁) + ((1 / 2 : ℝ) • u₂)) xStar = (⊤ : EReal) := by
        have hLeftTop :
            (((1 / 2 : ℝ) : EReal) * K u₁ xStar +
                (((1 / 2 : ℝ) : EReal) * K u₂ xStar)) = (⊤ : EReal) := by
          rw [hHalfTop]
          exact EReal.add_top_of_ne_bot hHalf₁_ne_bot
        rw [hLeftTop] at hMid
        exact top_le_iff.mp hMid
      have hScale :
          K (u₁ + u₂) xStar =
            ((2 : ℝ) : EReal) * K (((1 / 2 : ℝ) • u₁) + ((1 / 2 : ℝ) • u₂)) xStar := by
        have := (hHom.2 2 zero_lt_two (((1 / 2 : ℝ) • u₁) + ((1 / 2 : ℝ) • u₂)) xStar).1
        simpa [two_smul, add_comm, add_left_comm, add_assoc, smul_add] using this
      have hSumTop : K (u₁ + u₂) xStar = (⊤ : EReal) := by
        rw [hScale, hMidTop]
        simpa using (EReal.coe_mul_top_of_pos (x := (2 : ℝ)) zero_lt_two)
      have hLeftTop : K u₁ xStar + K u₂ xStar = (⊤ : EReal) := by
        simpa [hTop2] using EReal.add_top_of_ne_bot (hNoBot u₁ xStar)
      rw [hLeftTop, hSumTop]
    · have hMid :
          (((1 / 2 : ℝ) : EReal) * K u₁ xStar +
              (((1 / 2 : ℝ) : EReal) * K u₂ xStar)) ≤
            K (((1 / 2 : ℝ) • u₁) + ((1 / 2 : ℝ) • u₂)) xStar :=
        hConc xStar (by simp) (by simp) (show 0 ≤ (1 / 2 : ℝ) by norm_num)
          (show 0 ≤ (1 / 2 : ℝ) by norm_num) (by norm_num) (by simp)
      have hScale :
          K (u₁ + u₂) xStar =
            ((2 : ℝ) : EReal) * K (((1 / 2 : ℝ) • u₁) + ((1 / 2 : ℝ) • u₂)) xStar := by
        have := (hHom.2 2 zero_lt_two (((1 / 2 : ℝ) • u₁) + ((1 / 2 : ℝ) • u₂)) xStar).1
        simpa [two_smul, add_comm, add_left_comm, add_assoc, smul_add] using this
      have hScaledMid :
          ((2 : ℝ) : EReal) *
              ((((1 / 2 : ℝ) : EReal) * K u₁ xStar) +
                (((1 / 2 : ℝ) : EReal) * K u₂ xStar)) ≤
            K (u₁ + u₂) xStar := by
        calc
          ((2 : ℝ) : EReal) *
              ((((1 / 2 : ℝ) : EReal) * K u₁ xStar) +
                (((1 / 2 : ℝ) : EReal) * K u₂ xStar))
              ≤ ((2 : ℝ) : EReal) *
                  K (((1 / 2 : ℝ) • u₁) + ((1 / 2 : ℝ) • u₂)) xStar := by
                    gcongr
          _ = K (u₁ + u₂) xStar := by rw [← hScale]
      have h1 :
          ((2 : ℝ) : EReal) * (((1 / 2 : ℝ) : EReal) * K u₁ xStar) = K u₁ xStar := by
        have hcoeff : (((2 : ℝ) : EReal) * ((1 / 2 : ℝ) : EReal)) = (1 : EReal) := by
          change ((((2 : ℝ) * (1 / 2 : ℝ)) : ℝ) : EReal) = (1 : EReal)
          norm_num
        calc
          ((2 : ℝ) : EReal) * (((1 / 2 : ℝ) : EReal) * K u₁ xStar)
              = ((((2 : ℝ) : EReal) * ((1 / 2 : ℝ) : EReal)) * K u₁ xStar) := by
                  rw [mul_assoc]
          _ = (1 : EReal) * K u₁ xStar := by rw [hcoeff]
          _ = K u₁ xStar := by simp
      have h2 :
          ((2 : ℝ) : EReal) * (((1 / 2 : ℝ) : EReal) * K u₂ xStar) = K u₂ xStar := by
        have hcoeff : (((2 : ℝ) : EReal) * ((1 / 2 : ℝ) : EReal)) = (1 : EReal) := by
          change ((((2 : ℝ) * (1 / 2 : ℝ)) : ℝ) : EReal) = (1 : EReal)
          norm_num
        calc
          ((2 : ℝ) : EReal) * (((1 / 2 : ℝ) : EReal) * K u₂ xStar)
              = ((((2 : ℝ) : EReal) * ((1 / 2 : ℝ) : EReal)) * K u₂ xStar) := by
                  rw [mul_assoc]
          _ = (1 : EReal) * K u₂ xStar := by rw [hcoeff]
          _ = K u₂ xStar := by simp
      have hforb :
          ¬ ERealForbiddenSum
            (((2 : ℝ) : EReal) * (((1 / 2 : ℝ) : EReal) * K u₁ xStar))
            (((2 : ℝ) : EReal) * (((1 / 2 : ℝ) : EReal) * K u₂ xStar)) := by
        rw [h1, h2]
        simp [ERealForbiddenSum, hTop1, hTop2, hNoBot u₁ xStar, hNoBot u₂ xStar]
      have hLeft :
          ((2 : ℝ) : EReal) *
              ((((1 / 2 : ℝ) : EReal) * K u₁ xStar) +
                (((1 / 2 : ℝ) : EReal) * K u₂ xStar)) =
            K u₁ xStar + K u₂ xStar := by
        rw [ereal_mul_add_of_no_forbidden
          (α := ((2 : ℝ) : EReal))
          (x1 := (((1 / 2 : ℝ) : EReal) * K u₁ xStar))
          (x2 := (((1 / 2 : ℝ) : EReal) * K u₂ xStar)) hforb]
        have h1 :
            ((2 : ℝ) : EReal) * (((1 / 2 : ℝ) : EReal) * K u₁ xStar) = K u₁ xStar := by
          have hcoeff : (((2 : ℝ) : EReal) * ((1 / 2 : ℝ) : EReal)) = (1 : EReal) := by
            change ((((2 : ℝ) * (1 / 2 : ℝ)) : ℝ) : EReal) = (1 : EReal)
            norm_num
          calc
            ((2 : ℝ) : EReal) * (((1 / 2 : ℝ) : EReal) * K u₁ xStar)
                = ((((2 : ℝ) : EReal) * ((1 / 2 : ℝ) : EReal)) * K u₁ xStar) := by
                    rw [mul_assoc]
            _ = (1 : EReal) * K u₁ xStar := by rw [hcoeff]
            _ = K u₁ xStar := by simp
        have h2 :
            ((2 : ℝ) : EReal) * (((1 / 2 : ℝ) : EReal) * K u₂ xStar) = K u₂ xStar := by
          have hcoeff : (((2 : ℝ) : EReal) * ((1 / 2 : ℝ) : EReal)) = (1 : EReal) := by
            change ((((2 : ℝ) * (1 / 2 : ℝ)) : ℝ) : EReal) = (1 : EReal)
            norm_num
          calc
            ((2 : ℝ) : EReal) * (((1 / 2 : ℝ) : EReal) * K u₂ xStar)
                = ((((2 : ℝ) : EReal) * ((1 / 2 : ℝ) : EReal)) * K u₂ xStar) := by
                    rw [mul_assoc]
            _ = (1 : EReal) * K u₂ xStar := by rw [hcoeff]
            _ = K u₂ xStar := by simp
        rw [h1, h2]
      rw [← hLeft]
      exact hScaledMid

/-- Helper for Theorem 39.4: the half-space reconstruction is superadditive once the parameter
sections of `K` are concave and positively homogeneous. -/
lemma helperForTheorem_39_4_processMapOfBifunction_map_add_superset {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK : IsLowerClosedConcaveConvexPosHomBifunction (m := m) (n := n) K)
    (hNoBot : HasNoBotValuesBifunction K) :
    ∀ u₁ u₂,
      processMapOfBifunction (m := m) (n := n) K u₁ +
        processMapOfBifunction (m := m) (n := n) K u₂ ⊆
          processMapOfBifunction (m := m) (n := n) K (u₁ + u₂) := by
  rcases hK with ⟨hBase, hHom⟩
  have hConcConv :
      IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K :=
    hBase.1
  intro u₁ u₂ x hx
  rcases Set.mem_add.1 hx with ⟨x₁, hx₁, x₂, hx₂, rfl⟩
  intro xStar
  have hx₁' :
      (((finDot x₁ xStar : ℝ) : EReal)) ≤ K u₁ xStar := by
    simpa [processMapOfBifunction] using hx₁ xStar
  have hx₂' :
      (((finDot x₂ xStar : ℝ) : EReal)) ≤ K u₂ xStar := by
    simpa [processMapOfBifunction] using hx₂ xStar
  have hPair :
      (((finDot (x₁ + x₂) xStar : ℝ) : EReal)) =
        (((finDot x₁ xStar : ℝ) : EReal)) + (((finDot x₂ xStar : ℝ) : EReal)) := by
    simp [finDot]
  rw [hPair]
  calc
    (((finDot x₁ xStar : ℝ) : EReal)) + (((finDot x₂ xStar : ℝ) : EReal))
        ≤ K u₁ xStar + K u₂ xStar := add_le_add hx₁' hx₂'
    _ ≤ K (u₁ + u₂) xStar :=
      helperForTheorem_39_4_parameterSection_superadditive
        (m := m) (n := n)
        (hConc := fun xStar => hConcConv.1 xStar (by simp))
        (hNoBot := hNoBot) (hHom := hHom) u₁ u₂ xStar

/-- The reverse reconstruction of Theorem 39.4: from a lower-closed concave-convex bihomogeneous
kernel `K`, build the candidate closed convex process `A_K u = {x | ⟪x,x*⟫ ≤ K(u,x*), ∀ x*}`. -/
noncomputable def processOfLowerClosedConcaveConvexPosHomBifunction {m n : ℕ}
    (hQualification : Section39Theorem39_4GlobalQualification m n)
    (K : LowerClosedConcaveConvexPosHomBifunction m n) : ClosedConvexProcess m n := by
  let Aset : (Fin m → ℝ) → Set (Fin n → ℝ) :=
    processMapOfBifunction (m := m) (n := n) K.1
  have hWorking :
      IsWorkingLowerClosedConcaveConvexPosHomBifunction (m := m) (n := n) K.1 :=
    helperForTheorem_39_4_workingKernel_of_lowerClosedPosHom (m := m) (n := n) K.2
      (hQualification.kernelNoTopOrBot K) (hQualification.conjugateGraphClosed K)
  have hOriginAndClosed :
      (0 : Fin n → ℝ) ∈ Aset (0 : Fin m → ℝ) ∧ _root_.IsClosed (setValuedGraph Aset) := by
    simpa [Aset] using
      helperForTheorem_39_4_processMap_origin_mem_and_graphClosed_of_workingKernel
        (m := m) (n := n) hWorking
  let cp : ConvexProcess m n :=
    { toSetValued := Aset
      map_add_superset :=
        helperForTheorem_39_4_processMapOfBifunction_map_add_superset
          (m := m) (n := n) K.2 (hQualification.kernelNoTopOrBot K).1
      map_smul_pos :=
        helperForTheorem_39_4_processMapOfBifunction_map_smul_pos
          (m := m) (n := n) K.2.2
      zero_mem := hOriginAndClosed.1 }
  exact ⟨cp, (helperForProposition_39_0_13_graphClosed_iff_processClosed cp).1 hOriginAndClosed.2⟩

-- Textbook route: for a closed convex process `A`, set `K_A(u,x*) := ⟪A u, x*⟫` and use
-- Theorem 39.3 (together with the graph-cone duality from Theorem 39.2 and conjugacy results
-- from Chapter 33) to show `K_A` is lower closed concave-convex, normalized, and positively
-- homogeneous. After upgrading "lower closed" to the strong Section 33 notion, the reverse
-- direction now has the structural inputs it needs: the helper
-- `helperForTheorem_39_4_workingKernel_of_lowerClosedPosHom` derives the nonnegative origin
-- section and upper-closed parameter sections from the textbook hypotheses, so
-- `processMapOfBifunction K` has both a nonempty origin fiber and a closed graph. The remaining
-- work is therefore no longer statement repair, but completing the actual reconstruction of the
-- closed convex process and the two inverse-law proofs.
/-- Helper for Theorem 39.4: the canonical reverse reconstruction `K ↦ A_K` followed by the
canonical bracket recovery `A ↦ K_A` returns the original bihomogeneous kernel fiberwise. -/
lemma helperForTheorem_39_4_leftInverse {m n : ℕ}
    (hQualification : Section39Theorem39_4GlobalQualification m n) :
    Function.LeftInverse
      (fun A : ClosedConvexProcess m n =>
        ⟨bracketBifunctionOfProcess (m := m) (n := n) A.1,
          helperForTheorem_39_4_bracketBifunctionOfClosedProcess_memSubtype A⟩)
      (processOfLowerClosedConcaveConvexPosHomBifunction (m := m) (n := n) hQualification) := by
  classical
  let toBifunction : ClosedConvexProcess m n → LowerClosedConcaveConvexPosHomBifunction m n :=
    fun A =>
      ⟨bracketBifunctionOfProcess (m := m) (n := n) A.1,
        helperForTheorem_39_4_bracketBifunctionOfClosedProcess_memSubtype A⟩
  let toProcess : LowerClosedConcaveConvexPosHomBifunction m n → ClosedConvexProcess m n :=
    processOfLowerClosedConcaveConvexPosHomBifunction (m := m) (n := n) hQualification
  change Function.LeftInverse toBifunction toProcess
  intro K
  rcases K with ⟨K, hK⟩
  rcases hK with ⟨hBase, hNormHom⟩
  have hConcConv :
      IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K :=
    hBase.1
  have hNoBotK : HasNoBotValuesBifunction K :=
    (hQualification.kernelNoTopOrBot ⟨K, ⟨hBase, hNormHom⟩⟩).1
  have hKfull : IsLowerClosedConcaveConvexPosHomBifunction (m := m) (n := n) K :=
    ⟨hBase, hNormHom⟩
  let Ksub : LowerClosedConcaveConvexPosHomBifunction m n :=
    ⟨K, hKfull⟩
  change toBifunction (toProcess Ksub) = Ksub
  have hToProcess :
      ∀ K : LowerClosedConcaveConvexPosHomBifunction m n,
        (toProcess K).1.toSetValued = processMapOfBifunction (m := m) (n := n) K.1 := by
    intro K
    rfl
  -- Step 1: identify the reconstructed kernel with the Section 33 reverse pairing model.
  let F : (Fin m → ℝ) → (Fin n → ℝ) → EReal := fun u x => convexConjugate (K u) x
  have hReverse :
      IsImageClosedConvexBifunction F ∧
        (∀ (u : Fin m → ℝ) (x : Fin n → ℝ), F u x = convexConjugate (K u) x) ∧
          ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
            convexBifunctionPairing F u xStar = K u xStar := by
    simpa [F] using
      helperForTheorem_39_4_reverseConvexWitness_of_lowerClosed
        (m := m) (n := n) (K := K) hBase
        (hQualification.kernelNoTopOrBot Ksub)
  have hF_noBot : HasNoBotValuesBifunction F := hReverse.1.2.1
  have hF_notTop : ∀ u : Fin m → ℝ, ∃ x : Fin n → ℝ, F u x ≠ ⊤ := by
    intro u
    by_contra hu
    have huOutside : u ∉ convexBifunctionParameterDomain F := by
      simpa [convexBifunctionParameterDomain] using hu
    have hPairBot : convexBifunctionPairing F u (0 : Fin n → ℝ) = ⊥ :=
      helperForCorollary33_2_2_convex_pairing_eq_bot_of_off_parameterDomain
        (G := F) huOutside (0 : Fin n → ℝ)
    have hKNoBotAtZero : K u (0 : Fin n → ℝ) ≠ (⊥ : EReal) := hNoBotK u 0
    exact hKNoBotAtZero (by simpa [hReverse.2.2 u (0 : Fin n → ℝ)] using hPairBot)
  apply Subtype.ext
  funext u xStar
  have hSliceConv : ConvexFunction (K u) := by
    exact helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction (hConcConv.2 u (by simp))
  have hSlicePos : PositivelyHomogeneous (K u) := by
    intro y t ht
    simpa using (hNormHom.2 t ht u y).2
  have hSliceFenchelEq :
      fenchelConjugate n (F u) = K u := by
    funext y
    calc
      fenchelConjugate n (F u) y = convexConjugate (F u) y := by
        rw [helperForLemma33_0_14_convexConjugate_eq_fenchelConjugate]
      _ = convexBifunctionPairing F u y := by
        rfl
      _ = K u y := hReverse.2.2 u y
  have hF_closed : ClosedConvexFunction (F u) := by
    have h := fenchelConjugate_closedConvex (n := n) (f := K u)
    exact ⟨h.2, h.1⟩
  have hF_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (F u) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [ConvexFunction] using hF_closed.1
    · rcases hF_notTop u with ⟨x0, hx0⟩
      refine ⟨(x0, (F u x0).toReal), ?_⟩
      have hFinite : (((F u x0).toReal : ℝ) : EReal) = F u x0 := by
        exact EReal.coe_toReal hx0 (hF_noBot u x0)
      simpa [mem_epigraph_univ_iff] using (le_of_eq hFinite.symm)
    · intro x _hx
      exact hF_noBot u x
  have hZeroTopF : ∀ x : Fin n → ℝ, F u x = 0 ∨ F u x = ⊤ := by
    have hSliceBiconjPos : PositivelyHomogeneous (fenchelConjugate n (F u)) := by
      simpa [hSliceFenchelEq] using hSlicePos
    exact
      (section13_only_zero_top_iff_fenchelConjugate_posHom
        (n := n) (f := F u) hF_closed hF_proper).2 hSliceBiconjPos
  have hSliceZero : K u (0 : Fin n → ℝ) = (0 : EReal) := by
    rcases hF_notTop u with ⟨x0, hx0⟩
    have hx0_zero : F u x0 = (0 : EReal) := by
      rcases hZeroTopF x0 with hx0' | hx0'
      · exact hx0'
      · exact (hx0 hx0').elim
    have hNonpos :
        ∀ x : Fin n → ℝ,
          ((dotProduct x (0 : Fin n → ℝ) : ℝ) : EReal) - F u x ≤ (0 : EReal) := by
      intro x
      rcases hZeroTopF x with hx | hx
      · simp [hx]
      · simp [hx]
    have hLeZero : fenchelConjugate n (F u) (0 : Fin n → ℝ) ≤ (0 : EReal) := by
      rw [fenchelConjugate_eq_iSup]
      exact iSup_le hNonpos
    have hGeZero : (0 : EReal) ≤ fenchelConjugate n (F u) (0 : Fin n → ℝ) := by
      rw [fenchelConjugate_eq_iSup]
      have hTermZero :
          ((dotProduct x0 (0 : Fin n → ℝ) : ℝ) : EReal) - F u x0 = (0 : EReal) := by
        simp [hx0_zero]
      rw [← hTermZero]
      exact
        le_iSup (fun x : Fin n → ℝ => ((dotProduct x (0 : Fin n → ℝ) : ℝ) : EReal) - F u x) x0
    have hEqZero : fenchelConjugate n (F u) (0 : Fin n → ℝ) = (0 : EReal) :=
      le_antisymm hLeZero hGeZero
    simpa [hSliceFenchelEq] using hEqZero
  have hSliceNotTop : ¬ ∀ y : Fin n → ℝ, K u y = ⊤ := by
    intro hAllTop
    have : K u (0 : Fin n → ℝ) = (⊤ : EReal) := hAllTop 0
    rw [hSliceZero] at this
    simp at this
  obtain ⟨C, _hCclosed, _hCconv, hClConvEq, hCeq⟩ :=
    clConv_eq_supportFunctionEReal_setOf_forall_dotProduct_le
      (n := n) (f := K u) hSlicePos hSliceConv hSliceNotTop
  have hBiconjEq : fenchelConjugate n (fenchelConjugate n (K u)) = K u := by
    funext y
    calc
      fenchelConjugate n (fenchelConjugate n (K u)) y = convexConjugate (convexConjugate (K u)) y := by
        rw [helperForLemma33_0_14_convexConjugate_eq_fenchelConjugate,
          helperForLemma33_0_14_convexConjugate_eq_fenchelConjugate]
      _ = convexConjugate (F u) y := by simp [F]
      _ = convexBifunctionPairing F u y := by
        rfl
      _ = K u y := hReverse.2.2 u y
  have hClConvSelf : clConv n (K u) = K u := by
    calc
      clConv n (K u) = fenchelConjugate n (fenchelConjugate n (K u)) := by
        symm
        simpa using (fenchelConjugate_biconjugate_eq_clConv (n := n) (f := K u))
      _ = K u := hBiconjEq
  have hProcessFiberEq :
      C = processMapOfBifunction (m := m) (n := n) K u := by
    ext x
    constructor
    · intro hx
      rw [hCeq] at hx
      simpa [processMapOfBifunction, finDot, dotProduct_comm] using hx
    · intro hx
      rw [hCeq]
      simpa [processMapOfBifunction, finDot, dotProduct_comm] using hx
  have hBracketEq :
      bracketBifunctionOfProcess (m := m) (n := n) (toProcess Ksub).1 u =
        supportFunctionEReal ((toProcess Ksub).1.toSetValued u) := by
    simpa [bracketBifunctionOfProcess] using
      (helperForTheorem_39_3_supremumBracket_eq_supportFunctionEReal
        (S := (toProcess Ksub).1.toSetValued u))
  -- Step 2: rewrite the reconstructed fiber as the support-set recovered from `K u`.
  calc
    (toBifunction (toProcess Ksub)).1 u xStar
        = bracketBifunctionOfProcess (m := m) (n := n)
            (toProcess Ksub).1 u xStar := by
              rfl
    _ =
        supportFunctionEReal ((toProcess Ksub).1.toSetValued u) xStar := by
          exact congrArg (fun g => g xStar) hBracketEq
    _ = supportFunctionEReal (processMapOfBifunction (m := m) (n := n) K u) xStar := by
          exact congrArg
            (fun A : (Fin m → ℝ) → Set (Fin n → ℝ) => supportFunctionEReal (A u) xStar)
            (hToProcess Ksub)
    _ = supportFunctionEReal C xStar := by
          rw [← hProcessFiberEq]
    _ = clConv n (K u) xStar := by
          exact congrArg (fun g => g xStar) hClConvEq.symm
    _ = K u xStar := by
          exact congrArg (fun g => g xStar) hClConvSelf

/-- Helper for Theorem 39.4: the canonical forward reconstruction `A ↦ K_A ↦ A_{K_A}` recovers
each closed convex fiber, hence the original process. -/
lemma helperForTheorem_39_4_rightInverse {m n : ℕ}
    (hQualification : Section39Theorem39_4GlobalQualification m n) :
    Function.RightInverse
      (fun A : ClosedConvexProcess m n =>
        ⟨bracketBifunctionOfProcess (m := m) (n := n) A.1,
          helperForTheorem_39_4_bracketBifunctionOfClosedProcess_memSubtype A⟩)
      (processOfLowerClosedConcaveConvexPosHomBifunction (m := m) (n := n) hQualification) := by
  classical
  let toBifunction : ClosedConvexProcess m n → LowerClosedConcaveConvexPosHomBifunction m n :=
    fun A =>
      ⟨bracketBifunctionOfProcess (m := m) (n := n) A.1,
        helperForTheorem_39_4_bracketBifunctionOfClosedProcess_memSubtype A⟩
  let toProcess : LowerClosedConcaveConvexPosHomBifunction m n → ClosedConvexProcess m n :=
    processOfLowerClosedConcaveConvexPosHomBifunction (m := m) (n := n) hQualification
  change Function.RightInverse toBifunction toProcess
  intro A
  have hToBifunction :
      ∀ A : ClosedConvexProcess m n,
        (toBifunction A).1 = bracketBifunctionOfProcess (m := m) (n := n) A.1 := by
    intro A
    rfl
  have hToProcess :
      ∀ K : LowerClosedConcaveConvexPosHomBifunction m n,
        (toProcess K).1.toSetValued = processMapOfBifunction (m := m) (n := n) K.1 := by
    intro K
    rfl
  apply Subtype.ext
  -- Step 1: recover each fiber from the support function of the original closed convex fiber.
  have hProcMap :
      (toProcess (toBifunction A)).1.toSetValued = A.1.toSetValued := by
    have hFiberClosed :
        ∀ u : Fin m → ℝ, _root_.IsClosed (A.1.toSetValued u) :=
      (helperForProposition_39_0_6_graphClosed_and_fiberClosed A.1 A.2).2
    funext u
    have hFiberConv : Convex ℝ (A.1.toSetValued u) := (convexProcess_prop_39_0_2 A.1).1 u
    have hBracketEq :
        bracketBifunctionOfProcess (m := m) (n := n) A.1 u =
          supportFunctionEReal (A.1.toSetValued u) := by
      simpa [bracketBifunctionOfProcess] using
        (helperForTheorem_39_3_supremumBracket_eq_supportFunctionEReal
          (S := A.1.toSetValued u))
    have hSetOf :
        {x : Fin n → ℝ |
            ∀ xStar : Fin n → ℝ,
              (((finDot x xStar : ℝ) : EReal) ≤ supportFunctionEReal (A.1.toSetValued u) xStar)} =
          {x : Fin n → ℝ |
            fenchelConjugate n (supportFunctionEReal (A.1.toSetValued u)) x ≤ (0 : EReal)} := by
      ext x
      simpa [finDot, dotProduct_comm] using
        congrArg (fun S : Set (Fin n → ℝ) => x ∈ S)
          (section13_setOf_forall_dotProduct_le_eq_setOf_fenchelConjugate_le_zero
            (n := n) (supportFunctionEReal (A.1.toSetValued u)))
    have hIndicator :
        fenchelConjugate n (supportFunctionEReal (A.1.toSetValued u)) =
          indicatorFunction (A.1.toSetValued u) :=
      (indicatorFunction_conjugate_supportFunctionEReal_of_isClosed
        (C := A.1.toSetValued u) hFiberConv (hFiberClosed u)).2
    have hRecover :
        {x : Fin n → ℝ |
            fenchelConjugate n (supportFunctionEReal (A.1.toSetValued u)) x ≤ (0 : EReal)} =
          A.1.toSetValued u := by
      ext x
      rw [hIndicator]
      by_cases hx : x ∈ A.1.toSetValued u
      · simp [indicatorFunction, hx]
      · simp [indicatorFunction, hx]
    calc
      (toProcess (toBifunction A)).1.toSetValued u
          = processMapOfBifunction (m := m) (n := n)
              (bracketBifunctionOfProcess (m := m) (n := n) A.1) u := by
                rw [hToProcess (toBifunction A), hToBifunction A]
      _ =
          {x : Fin n → ℝ |
            ∀ xStar : Fin n → ℝ,
              (((finDot x xStar : ℝ) : EReal) ≤ supportFunctionEReal (A.1.toSetValued u) xStar)} := by
            rw [processMapOfBifunction]
            simp [hBracketEq]
      _ =
          {x : Fin n → ℝ |
            fenchelConjugate n (supportFunctionEReal (A.1.toSetValued u)) x ≤ (0 : EReal)} :=
            hSetOf
      _ = A.1.toSetValued u := hRecover
  -- Step 2: fiberwise equality upgrades to process equality by graph extensionality.
  have hGraphEq :
      setValuedGraph (toProcess (toBifunction A)).1.toSetValued =
        setValuedGraph A.1.toSetValued := by
    simp [setValuedGraph, hProcMap]
  exact helperForProposition_39_0_13_eq_of_graph_eq hGraphEq

/-- Theorem 39.4: The relations

`K(u, x*) = ⟪A u, x*⟫` and `A u = {x | ⟪x, x*⟫ ≤ K(u, x*), ∀ x*}`

define a one-to-one correspondence between lower closed concave-convex bifunctions
`K : ℝ^m × ℝ^n → [-∞,+∞]` with `K(0,0)=0` and positive homogeneity
`K(r•u,x*) = r K(u,x*) = K(u,r•x*)` for all `r>0`, and supremum-oriented closed convex processes
`A : ℝ^m ⇉ ℝ^n`. (Similarly for upper closed convex-concave functions and infimum oriented convex
processes.) -/
theorem theorem_39_4 {m n : ℕ}
    (hQualification : Section39Theorem39_4GlobalQualification m n) :
    ∃ (toProcess : LowerClosedConcaveConvexPosHomBifunction m n → ClosedConvexProcess m n)
      (toBifunction : ClosedConvexProcess m n → LowerClosedConcaveConvexPosHomBifunction m n),
      (∀ A : ClosedConvexProcess m n,
          (toBifunction A).1 = bracketBifunctionOfProcess (m := m) (n := n) A.1) ∧
        (∀ K : LowerClosedConcaveConvexPosHomBifunction m n,
          (toProcess K).1.toSetValued = processMapOfBifunction (m := m) (n := n) K.1) ∧
        Function.LeftInverse toBifunction toProcess ∧
          Function.RightInverse toBifunction toProcess :=
  by
    classical
    -- Step 1: package the canonical reverse map from the textbook half-space formula.
    refine ⟨processOfLowerClosedConcaveConvexPosHomBifunction
      (m := m) (n := n) hQualification, ?_⟩
    -- Step 2: package the canonical forward map from the closed-process bracket.
    refine ⟨
      (fun A : ClosedConvexProcess m n =>
        ⟨bracketBifunctionOfProcess (m := m) (n := n) A.1,
          helperForTheorem_39_4_bracketBifunctionOfClosedProcess_memSubtype A⟩),
      ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro A
      rfl
    · intro K
      rfl
    · exact helperForTheorem_39_4_leftInverse (m := m) (n := n) hQualification
    · exact helperForTheorem_39_4_rightInverse (m := m) (n := n) hQualification

end ConvexProcess
end Section39
end Chap08

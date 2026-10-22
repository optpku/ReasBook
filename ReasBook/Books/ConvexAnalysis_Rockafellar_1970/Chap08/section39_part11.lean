/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part12
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part13
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section38_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section39_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section39_part9

open scoped Pointwise
open scoped RealInnerProductSpace
open scoped BigOperators

attribute [local instance] Classical.propDecidable

section Chap08
section Section39

namespace ConvexProcess

/-- A chosen Minkowski-sum convex process `A₁ + A₂`, characterized by having underlying
set-valued mapping `u ↦ A₁ u + A₂ u`. -/
noncomputable def addProcess {m n : ℕ} (A₁ A₂ : ConvexProcess m n) : ConvexProcess m n :=
  Classical.choose ((prop_39_0_7 (A := A₁) (B := A₂) (r := (1 : ℝ))).2.1)

/-- A chosen scalar-multiple convex process `r • A`, characterized by having underlying set-valued
mapping `u ↦ r • (A u)`. -/
noncomputable def smulProcess {m n : ℕ} (r : ℝ) (A : ConvexProcess m n) : ConvexProcess m n :=
  Classical.choose ((prop_39_0_7 (A := A) (B := A) (r := r)).1)

/-- Helper for Theorem 39.5: the indicator bifunction satisfies the Chapter 38 properness
requirement when viewed sectionwise in the image variable. -/
lemma helperForTheorem_39_5_indicatorFiberwiseProperConvexBifunction_proper {m n : ℕ}
    (A : ConvexProcess m n) :
    (∀ u x, ConvexProcess.indicatorBifunction A u x ≠ ⊥) ∧
      ∃ u x, ConvexProcess.indicatorBifunction A u x ≠ ⊤ := by
  -- Step 1: unpack the already established properness of the uncurried product indicator.
  constructor
  · intro u x
    exact (prop_39_0_13 A).2.1.1 (u, x)
  · rcases (prop_39_0_13 A).2.1.2 with ⟨p, hp⟩
    exact ⟨p.1, p.2, hp⟩

/-- Helper for Theorem 39.5: each fixed-parameter section of the indicator bifunction is convex in
the image variable. -/
lemma helperForTheorem_39_5_indicatorFiberwiseProperConvexBifunction_convex {m n : ℕ}
    (A : ConvexProcess m n) :
    ∀ u, IsERealConvex (ConvexProcess.indicatorBifunction A u) := by
  -- Step 1: reuse the sectionwise-convex half of the Rockafellar package for indicators.
  intro u
  exact helperForTheorem_39_3_isERealConvexOn_univ_to_IsConvexEReal
    ((indicatorBifunction_rockafellarPackage A).1.1 u)

/-- Helper for Theorem 39.5: the effective domain of the indicator bifunction is exactly the domain
of the underlying convex process. -/
lemma helperForTheorem_39_5_bifunctionDom_indicator_eq_dom {m n : ℕ} (A : ConvexProcess m n) :
    bifunctionDom (ConvexProcess.indicatorBifunction A) = A.dom := by
  ext u
  constructor
  · rintro ⟨x, hx⟩
    by_cases hxMem : x ∈ A.toSetValued u
    · exact ⟨x, hxMem⟩
    · simp [ConvexProcess.indicatorBifunction, indicatorEReal, hxMem] at hx
  · rintro ⟨x, hxMem⟩
    refine ⟨x, ?_⟩
    simp [ConvexProcess.indicatorBifunction, indicatorEReal, hxMem]

/-- Helper for Theorem 39.5: package the indicator bifunction of a convex process as a Chapter 38
fiberwise proper convex bifunction. -/
noncomputable abbrev helperForTheorem_39_5_indicatorFiberwiseProperConvexBifunction {m n : ℕ}
    (A : ConvexProcess m n) : FiberwiseProperConvexBifunction m n :=
  ⟨ConvexProcess.indicatorBifunction A,
    helperForTheorem_39_5_indicatorFiberwiseProperConvexBifunction_proper A,
    helperForTheorem_39_5_indicatorFiberwiseProperConvexBifunction_convex A⟩

/-- Helper for Theorem 39.5: the Chapter 38 infimal convolution of the two indicator bifunctions
is exactly the indicator bifunction of the Minkowski-sum process `A₁ + A₂`. -/
lemma helperForTheorem_39_5_indicatorInfimalConvolution_eq_indicatorAddProcess {m n : ℕ}
    (A₁ A₂ : ConvexProcess m n) :
    bifunctionInfimalConvolution
        (helperForTheorem_39_5_indicatorFiberwiseProperConvexBifunction A₁)
        (helperForTheorem_39_5_indicatorFiberwiseProperConvexBifunction A₂) =
      ConvexProcess.indicatorBifunction (addProcess A₁ A₂) := by
  have hAddProcess :
      (addProcess A₁ A₂).toSetValued = addSetValued A₁ A₂ :=
    Classical.choose_spec ((prop_39_0_7 (A := A₁) (B := A₂) (r := (1 : ℝ))).2.1)
  funext u x
  by_cases hx :
      x ∈ (addProcess A₁ A₂).toSetValued u
  · -- Step 1: a decomposition witness gives one zero-valued summand in the infimal convolution.
    have hxAdd : x ∈ addSetValued A₁ A₂ u := by
      simpa [hAddProcess] using hx
    rcases Set.mem_add.1 hxAdd with ⟨x₁, hx₁, x₂, hx₂, hxEq⟩
    have hxSplit : x - x₂ = x₁ := by
      exact (sub_eq_iff_eq_add).2 (by simpa [add_comm] using hxEq.symm)
    simp [bifunctionInfimalConvolution, helperForTheorem_39_5_indicatorFiberwiseProperConvexBifunction,
      ConvexProcess.indicatorBifunction, indicatorEReal, hx]
    apply le_antisymm
    · calc
        (⨅ y : Fin n → ℝ,
            ConvexProcess.indicatorBifunction A₁ u (x - y) +
              ConvexProcess.indicatorBifunction A₂ u y)
            ≤ ConvexProcess.indicatorBifunction A₁ u (x - x₂) +
                ConvexProcess.indicatorBifunction A₂ u x₂ := by
                  exact iInf_le _ x₂
        _ = 0 := by
          simp [ConvexProcess.indicatorBifunction, indicatorEReal, hx₁, hx₂, hxSplit]
    · refine le_iInf ?_
      intro y
      by_cases hx₁y : x - y ∈ A₁.toSetValued u
      · by_cases hx₂y : y ∈ A₂.toSetValued u
        · simp [ConvexProcess.indicatorBifunction, indicatorEReal, hx₁y, hx₂y]
        · simp [ConvexProcess.indicatorBifunction, indicatorEReal, hx₁y, hx₂y]
      · by_cases hx₂y : y ∈ A₂.toSetValued u
        · simp [ConvexProcess.indicatorBifunction, indicatorEReal, hx₁y, hx₂y]
        · simp [ConvexProcess.indicatorBifunction, indicatorEReal, hx₁y, hx₂y]
  · -- Step 2: without any decomposition, every summand is `⊤`, so the infimum stays `⊤`.
    have hxAdd : x ∉ addSetValued A₁ A₂ u := by
      simpa [hAddProcess] using hx
    simp [bifunctionInfimalConvolution, helperForTheorem_39_5_indicatorFiberwiseProperConvexBifunction,
      ConvexProcess.indicatorBifunction, indicatorEReal, hx]
    intro y
    by_cases hx₁y : x - y ∈ A₁.toSetValued u
    · by_cases hx₂y : y ∈ A₂.toSetValued u
      · exfalso
        apply hxAdd
        refine Set.mem_add.2 ⟨x - y, hx₁y, y, hx₂y, ?_⟩
        ext i
        change (x i - y i) + y i = x i
        ring
      · simp [helperForTheorem_39_5_indicatorFiberwiseProperConvexBifunction,
          ConvexProcess.indicatorBifunction, indicatorEReal, hx₁y, hx₂y]
    · by_cases hx₂y : y ∈ A₂.toSetValued u
      · simp [helperForTheorem_39_5_indicatorFiberwiseProperConvexBifunction,
          ConvexProcess.indicatorBifunction, indicatorEReal, hx₁y, hx₂y]
      · simp [helperForTheorem_39_5_indicatorFiberwiseProperConvexBifunction,
          ConvexProcess.indicatorBifunction, indicatorEReal, hx₁y, hx₂y]

/-- Helper for Theorem 39.5: the primal relative-interior hypothesis on `dom A₁` and `dom A₂`
is exactly the Section 38 qualification for the two indicator bifunctions. -/
lemma helperForTheorem_39_5_indicatorBifunction_riQualification {m n : ℕ}
    (A₁ A₂ : ConvexProcess m n)
    (hri : Set.Nonempty (ri A₁.dom ∩ ri A₂.dom)) :
    (intrinsicInterior ℝ (bifunctionDom (ConvexProcess.indicatorBifunction A₁)) ∩
        intrinsicInterior ℝ (bifunctionDom (ConvexProcess.indicatorBifunction A₂))).Nonempty := by
  -- Step 1: the indicator bifunction has the same parameter domain as the original convex
  -- process, so the two relative-interior formulations are identical.
  simpa [helperForTheorem_39_5_bifunctionDom_indicator_eq_dom] using hri

/-- The indicator bifunction of a convex process is jointly convex in its parameter and image
variables. -/
lemma helperForTheorem_39_5_indicatorConvexBifunction {m n : ℕ}
    (A : ConvexProcess m n) :
    ConvexBifunction (ConvexProcess.indicatorBifunction A) := by
  have hProduct :
      IsERealConvex (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
        ConvexProcess.indicatorBifunction A p.1 p.2) := by
    simpa [IsConvexEReal, eRealEpigraph, IsERealConvex, ERealEpigraph] using
      (prop_39_0_13 A).1
  let pairMap :
      (Fin (m + n) → ℝ) →ₗ[ℝ] ((Fin m → ℝ) × (Fin n → ℝ)) :=
    { toFun := fun z =>
        (fun i => z (Fin.castAdd n i), fun j => z (Fin.natAdd m j))
      map_add' := by intro z w; ext i <;> simp
      map_smul' := by intro c z; ext i <;> simp }
  have hGraph : IsERealConvex
      (bifunctionGraphFunction (ConvexProcess.indicatorBifunction A)) := by
    simpa [pairMap, bifunctionGraphFunction] using
      (helperForTheorem_38_4_isERealConvex_precomp_linearMap
        (A := pairMap)
        (g := fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
          ConvexProcess.indicatorBifunction A p.1 p.2) hProduct)
  simpa [ConvexBifunction, ConvexFunction, ConvexFunctionOn, IsERealConvex,
    helperForTheorem_38_1_epigraph_eq_univ] using hGraph

/-- Helper for Theorem 39.5: after rewriting the primal indicator convolution as the indicator of
`A₁ + A₂`, corrected Theorem 38.2 yields the textbook adjoint identity. -/
lemma helperForTheorem_39_5_indicatorAdjoint_eq_infimalConvolutionInSecond_adjoint {m n : ℕ}
    (A₁ A₂ : ConvexProcess m n)
    (hri : Set.Nonempty (ri A₁.dom ∩ ri A₂.dom)) :
    textbookBifunctionAdjoint (ConvexProcess.indicatorBifunction (addProcess A₁ A₂)) =
      concaveBifunctionInfimalConvolutionInSecond
        (textbookBifunctionAdjoint (ConvexProcess.indicatorBifunction A₁))
        (textbookBifunctionAdjoint (ConvexProcess.indicatorBifunction A₂)) := by
  have hri38 :
      (intrinsicInterior ℝ (bifunctionDom (ConvexProcess.indicatorBifunction A₁)) ∩
          intrinsicInterior ℝ
            (bifunctionDom (ConvexProcess.indicatorBifunction A₂))).Nonempty :=
    helperForTheorem_39_5_indicatorBifunction_riQualification A₁ A₂ hri
  -- Step 1: rewrite the chosen sum process to the Chapter 38 infimal convolution of indicators.
  rw [← helperForTheorem_39_5_indicatorInfimalConvolution_eq_indicatorAddProcess A₁ A₂]
  -- Step 2: apply Theorem 38.2 to the packaged indicator bifunctions.
  exact bifunctionAdjoint_infimalConvolution_eq_infimalConvolution_adjoint
    (helperForTheorem_39_5_indicatorFiberwiseProperConvexBifunction A₁)
    (helperForTheorem_39_5_indicatorFiberwiseProperConvexBifunction A₂)
    (helperForTheorem_39_5_indicatorConvexBifunction A₁)
    (helperForTheorem_39_5_indicatorConvexBifunction A₂) hri38

/-- Helper for Theorem 39.5: lower semicontinuity of the indicator bifunction forces the underlying
convex process to have closed graph, hence to be closed. -/
lemma helperForTheorem_39_5_processClosed_of_indicatorLowerSemicontinuous {m n : ℕ}
    (A : ConvexProcess m n)
    (hA :
      IsProductLowerSemicontinuousBifunction (ConvexProcess.indicatorBifunction A)) :
    A.IsClosed := by
  let F : (Fin m → ℝ) → (Fin n → ℝ) → EReal := ConvexProcess.indicatorBifunction A
  rw [IsProductLowerSemicontinuousBifunction] at hA
  -- Step 1: transfer product lower semicontinuity to the packed graph function on `ℝ^(m+n)`.
  have hSplitCont :
      Continuous
        (fun z : Fin (m + n) → ℝ =>
          ((fun i => z (Fin.castAdd n i)), (fun j => z (Fin.natAdd m j)))) := by
    continuity
  have hGraphLsc : LowerSemicontinuous (graphFunctionOfBifunction F) := by
    simpa [F, graphFunctionOfBifunction] using hA.comp_continuous hSplitCont
  have hGraphClosed : IsClosedEReal (graphFunctionOfBifunction F) :=
    isClosedEReal_of_lowerSemicontinuous hGraphLsc
  -- Step 2: unpack the closed epigraph back to the original product-space indicator function.
  have hPackCont :
      Continuous
        (fun q : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ =>
          (Fin.append q.1.1 q.1.2, q.2)) := by
    have hAppendCont :
        Continuous
          (fun p : (Fin m → ℝ) × (Fin n → ℝ) => Fin.append p.1 p.2) := by
      simpa using
        (continuous_pi fun i => by
          by_cases hi : i.1 < m
          · simpa [Fin.append, Fin.addCases, hi] using
              ((continuous_apply (i := (⟨i.1, hi⟩ : Fin m))).comp continuous_fst)
          · let j : Fin n := ⟨i.1 - m, by omega⟩
            have hjCont : Continuous fun p : (Fin m → ℝ) × (Fin n → ℝ) => p.2 j :=
              (continuous_apply (i := j)).comp continuous_snd
            simpa [Fin.append, Fin.addCases, hi, j] using hjCont)
    exact (hAppendCont.comp continuous_fst).prodMk continuous_snd
  have hEpigraphPreimage :
      (fun q : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ =>
          (Fin.append q.1.1 q.1.2, q.2)) ⁻¹' eRealEpigraph (graphFunctionOfBifunction F) =
        eRealEpigraph (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2) := by
    ext q
    simp [eRealEpigraph, F, graphFunctionOfBifunction]
  have hIndicatorClosed :
      IsClosedEReal (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2) := by
    rw [IsClosedEReal]
    have hClosedPreimage :
        _root_.IsClosed
          ((fun q : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ =>
              (Fin.append q.1.1 q.1.2, q.2)) ⁻¹' eRealEpigraph (graphFunctionOfBifunction F)) :=
      hGraphClosed.preimage hPackCont
    simpa [hEpigraphPreimage] using hClosedPreimage
  -- Step 3: Proposition 39.0.13 identifies closedness of the indicator with closedness of `A`.
  exact ((prop_39_0_13 A).2.2.2).1 (by simpa [F] using hIndicatorClosed)

/-- Helper for Theorem 39.5: infimum-oriented adjoint membership is the negated form of
supremum-oriented adjoint membership. -/
lemma helperForTheorem_39_5_infimumMembership_iff_supremumMembership_neg {m n : ℕ}
    (A : ConvexProcess m n) (xStar : Fin n → ℝ) (uStar : Fin m → ℝ) :
    uStar ∈ (adjointVecOriented ConvexSetOrientation.infimum A).toSetValued xStar ↔
      (-uStar) ∈ (adjointVecOriented ConvexSetOrientation.supremum A).toSetValued (-xStar) := by
  constructor
  · intro hu
    -- Step 1: negate the infimum inequality to recover the supremum inequality at `(-x*, -u*)`.
    intro u x hx
    have hle := hu u x hx
    simpa [adjointVecOriented, adjointVecOrientedSetValued, setValuedAdjointVecInf,
      setValuedAdjointVec, finDot] using neg_le_neg hle
  · intro hu
    -- Step 2: negate the supremum inequality back to the infimum convention.
    intro u x hx
    have hge := hu u x hx
    have hle := neg_le_neg hge
    simpa [adjointVecOriented, adjointVecOrientedSetValued, adjointVec, setValuedAdjointVecInf,
      setValuedAdjointVec, finDot] using hle

/-- Helper for Theorem 39.5: the module-dual adjoint from Definition 39.0.14 matches the
Euclidean supremum-oriented adjoint after transporting both dual variables through
`dotProductEquiv`. -/
lemma helperForTheorem_39_5_moduleAdjointMembership_iff_supremumAdjointMembership {m n : ℕ}
    (A : ConvexProcess m n) (xStar : Fin n → ℝ) (uStar : Fin m → ℝ) :
    dotProductEquiv ℝ (Fin m) uStar ∈
        (adjoint A).toSetValued (dotProductEquiv ℝ (Fin n) xStar) ↔
      uStar ∈ (adjointVecOriented ConvexSetOrientation.supremum A).toSetValued xStar := by
  -- Step 1: both sides are the same graph inequality after rewriting dual evaluation as `finDot`.
  constructor
  · intro hu
    intro u x hx
    have hEval := hu u x hx
    simpa [adjoint, adjointVecOriented, adjointVecOrientedSetValued, setValuedAdjointVec, finDot,
      dotProduct_comm] using hEval
  · intro hu
    intro u x hx
    have hEval := hu u x hx
    simpa [adjoint, adjointVecOriented, adjointVecOrientedSetValued, setValuedAdjointVec, finDot,
      dotProduct_comm] using hEval

/-- Helper for Theorem 39.5: after pulling the Chapter 38 adjoint back through the signed
Euclidean-dual identification, the adjoint of the indicator bifunction is exactly the negative
indicator of the supremum-oriented adjoint fiber. -/
lemma helperForTheorem_39_5_bifunctionAdjoint_indicator_eq_negIndicator_supremumAdjointFiber
    {m n : ℕ} (A : ConvexProcess m n) (xStar : Fin n → ℝ) (uStar : Fin m → ℝ) :
    bifunctionAdjoint (ConvexProcess.indicatorBifunction A)
        (dotProductEquiv ℝ (Fin n) (-xStar))
        (dotProductEquiv ℝ (Fin m) (-uStar)) =
      negIndicatorEReal
        ((adjointVecOriented ConvexSetOrientation.supremum A).toSetValued xStar) uStar := by
  by_cases hu : uStar ∈ (adjointVecOriented ConvexSetOrientation.supremum A).toSetValued xStar
  · -- Step 1: if `uStar` is in the adjoint fiber, the origin graph point gives the value `0`.
    have hNeg :
        negIndicatorEReal
          ((adjointVecOriented ConvexSetOrientation.supremum A).toSetValued xStar) uStar = 0 := by
      simp [negIndicatorEReal, hu]
    rw [hNeg]
    apply le_antisymm
    · refine le_trans (iInf_le _ (0 : Fin m → ℝ)) ?_
      refine le_trans (iInf_le _ (0 : Fin n → ℝ)) ?_
      simp [ConvexProcess.indicatorBifunction, indicatorEReal, A.zero_mem, dotProductEquiv_apply_apply,
        finDot, dotProduct_comm]
    · -- Step 2: every on-graph term is nonnegative by the defining adjoint inequality, while
      -- every off-graph term is `⊤`.
      rw [bifunctionAdjoint]
      refine le_iInf ?_
      intro u
      refine le_iInf ?_
      intro x
      by_cases hx : x ∈ A.toSetValued u
      · have hux := hu u x hx
        have hnonneg : 0 ≤ finDot u uStar - finDot x xStar := sub_nonneg.mpr hux
        have hterm :
            ((dotProductEquiv ℝ (Fin n) (-xStar) x : ℝ) : EReal) +
                -((dotProductEquiv ℝ (Fin m) (-uStar) u : ℝ) : EReal) +
                ConvexProcess.indicatorBifunction A u x =
              ((finDot u uStar - finDot x xStar : ℝ) : EReal) := by
          simp [ConvexProcess.indicatorBifunction, indicatorEReal, hx, dotProductEquiv_apply_apply,
            finDot, dotProduct_comm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        rw [hterm]
        exact_mod_cast hnonneg
      · have htop :
            ((dotProductEquiv ℝ (Fin n) (-xStar) x : ℝ) : EReal) +
                -((dotProductEquiv ℝ (Fin m) (-uStar) u : ℝ) : EReal) +
                ConvexProcess.indicatorBifunction A u x =
              (⊤ : EReal) := by
          simp [ConvexProcess.indicatorBifunction, indicatorEReal, hx]
        rw [htop]
        simp
  · -- Step 3: if `uStar` is off the adjoint fiber, scale one violating graph witness along the
    -- process cone to drive the adjoint infimum down to `⊥`.
    have hNeg :
        negIndicatorEReal
          ((adjointVecOriented ConvexSetOrientation.supremum A).toSetValued xStar) uStar = ⊥ := by
      simp [negIndicatorEReal, hu]
    rw [hNeg]
    apply le_antisymm
    · rw [le_bot_iff, bifunctionAdjoint, iInf₂_eq_bot]
      intro b hb
      have huWitness :
          ¬ ∀ u x, x ∈ A.toSetValued u → finDot u uStar ≥ finDot x xStar := by
        simpa [adjointVecOriented, adjointVecOrientedSetValued, setValuedAdjointVec] using hu
      push_neg at huWitness
      rcases huWitness with ⟨u₀, x₀, hx₀, hlt₀⟩
      rcases EReal.lt_iff_exists_rat_btwn.mp hb with ⟨q, -, hqb⟩
      let c : ℝ := finDot u₀ uStar - finDot x₀ xStar
      let r : ℝ := (q : ℝ) - |(q : ℝ)| - 1
      let t : ℝ := r / c
      have hc : c ≠ 0 := by
        dsimp [c]
        linarith
      have hcneg : c < 0 := by
        dsimp [c]
        linarith [hlt₀]
      have hrneg : r < 0 := by
        dsimp [r]
        have hqabs : (q : ℝ) ≤ |(q : ℝ)| := by
          exact le_abs_self (q : ℝ)
        linarith
      have ht : 0 < t := by
        dsimp [t]
        exact div_pos_of_neg_of_neg hrneg hcneg
      have hrltq : (r : ℝ) < q := by
        dsimp [r]
        nlinarith [abs_nonneg (q : ℝ)]
      have hrltb : ((r : ℝ) : EReal) < b := by
        exact lt_trans (by exact_mod_cast hrltq) hqb
      have hScaledMem : t • x₀ ∈ A.toSetValued (t • u₀) := by
        have hFiber : A.toSetValued (t • u₀) = t • A.toSetValued u₀ :=
          A.map_smul_pos u₀ t ht
        have hxScaled : t • x₀ ∈ t • A.toSetValued u₀ := by
          exact Set.mem_smul_set.mpr ⟨x₀, hx₀, rfl⟩
        simpa [hFiber] using hxScaled
      have hscalar : t * c = r := by
        dsimp [t]
        field_simp [hc]
      have hterm :
          ((dotProductEquiv ℝ (Fin n) (-xStar) (t • x₀) : ℝ) : EReal) +
              -((dotProductEquiv ℝ (Fin m) (-uStar) (t • u₀) : ℝ) : EReal) +
              ConvexProcess.indicatorBifunction A (t • u₀) (t • x₀) =
            ((t * c : ℝ) : EReal) := by
        calc
          ((dotProductEquiv ℝ (Fin n) (-xStar) (t • x₀) : ℝ) : EReal) +
                -((dotProductEquiv ℝ (Fin m) (-uStar) (t • u₀) : ℝ) : EReal) +
                ConvexProcess.indicatorBifunction A (t • u₀) (t • x₀) =
              (((dotProductEquiv ℝ (Fin n) (-xStar) (t • x₀) :
                    ℝ) - (dotProductEquiv ℝ (Fin m) (-uStar) (t • u₀) : ℝ) : ℝ) : EReal) := by
                simp [ConvexProcess.indicatorBifunction, indicatorEReal, hScaledMem, sub_eq_add_neg]
          _ = ((t * c : ℝ) : EReal) := by
                congr 1
                dsimp [c]
                simp [dotProductEquiv_apply_apply, finDot, dotProduct_comm, sub_eq_add_neg]
                ring
      refine ⟨t • u₀, t • x₀, ?_⟩
      calc
        ((dotProductEquiv ℝ (Fin n) (-xStar) (t • x₀) : ℝ) : EReal) +
            -((dotProductEquiv ℝ (Fin m) (-uStar) (t • u₀) : ℝ) : EReal) +
            ConvexProcess.indicatorBifunction A (t • u₀) (t • x₀) =
          ((t * c : ℝ) : EReal) := hterm
        _ = ((r : ℝ) : EReal) := by rw [hscalar]
        _ < b := hrltb
    · exact bot_le

/-- Helper for Theorem 39.5: the current Chapter 38 dual infimal-convolution operator only gives
an upper bound by the negative indicator of the fiberwise Minkowski sum. This is the precise local
obstruction behind the failed exact-equality route for the reverse inclusion. -/
lemma helperForTheorem_39_5_infimalConvolutionInSecond_negIndicator_le_negIndicatorFiberSum
    {m n : ℕ} (S₁ S₂ : (Fin n → ℝ) → Set (Fin m → ℝ)) :
    bifunctionInfimalConvolutionInSecond
        (fun xStar uStar => negIndicatorEReal (S₁ xStar) uStar)
        (fun xStar uStar => negIndicatorEReal (S₂ xStar) uStar) ≤
      fun xStar uStar => negIndicatorEReal (S₁ xStar + S₂ xStar) uStar := by
  intro xStar uStar
  by_cases hu : uStar ∈ S₁ xStar + S₂ xStar
  · -- Step 1: a valid Minkowski decomposition gives one `0` term in the infimum, so the whole
    -- infimal convolution is at most the target value `0`.
    rcases Set.mem_add.1 hu with ⟨uStar₁, huStar₁, uStar₂, huStar₂, huEq⟩
    have hSplit : uStar - uStar₂ = uStar₁ := by
      exact sub_eq_iff_eq_add.2 huEq.symm
    calc
      bifunctionInfimalConvolutionInSecond
          (fun xStar uStar => negIndicatorEReal (S₁ xStar) uStar)
          (fun xStar uStar => negIndicatorEReal (S₂ xStar) uStar)
          xStar uStar
          ≤
            negIndicatorEReal (S₁ xStar) (uStar - uStar₂) +
              negIndicatorEReal (S₂ xStar) uStar₂ := by
                exact iInf_le _ uStar₂
      _ = 0 := by
        simp [negIndicatorEReal, huStar₁, huStar₂, hSplit]
      _ = negIndicatorEReal (S₁ xStar + S₂ xStar) uStar := by
        simp [negIndicatorEReal, hu]
  · -- Step 2: if `uStar` is off the Minkowski sum fiber, then every candidate split already
    -- contributes `⊥`, so the infimal convolution is `⊥` and hence below the target.
    have hTermBot :
        ∀ y : Fin m → ℝ,
          negIndicatorEReal (S₁ xStar) (uStar - y) + negIndicatorEReal (S₂ xStar) y = ⊥ := by
      intro y
      by_cases h₁ : uStar - y ∈ S₁ xStar
      · by_cases h₂ : y ∈ S₂ xStar
        · exfalso
          apply hu
          exact Set.mem_add.2 ⟨uStar - y, h₁, y, h₂, by simp⟩
        · simp [negIndicatorEReal, h₁, h₂]
      · simp [negIndicatorEReal, h₁]
    have hInfEqBot :
        bifunctionInfimalConvolutionInSecond
            (fun xStar uStar => negIndicatorEReal (S₁ xStar) uStar)
            (fun xStar uStar => negIndicatorEReal (S₂ xStar) uStar)
            xStar uStar = ⊥ := by
      rw [bifunctionInfimalConvolutionInSecond]
      apply le_antisymm
      · have hLeTerm :
            (⨅ y : Fin m → ℝ,
                negIndicatorEReal (S₁ xStar) (uStar - y) + negIndicatorEReal (S₂ xStar) y) ≤
              negIndicatorEReal (S₁ xStar) (uStar - 0) + negIndicatorEReal (S₂ xStar) 0 :=
          iInf_le
            (fun y : Fin m → ℝ =>
              negIndicatorEReal (S₁ xStar) (uStar - y) + negIndicatorEReal (S₂ xStar) y)
            (0 : Fin m → ℝ)
        exact le_trans hLeTerm (by simpa using (hTermBot (0 : Fin m → ℝ)).le)
      · exact bot_le
    simpa [negIndicatorEReal, hu] using hInfEqBot.le

/-- Helper for Theorem 39.5: evaluating the Chapter 38 dual infimal convolution at the signed
Euclidean-dual image of `(xStar, uStar)` is exactly the infimal convolution of the negative
indicators of the two supremum-adjoint fibers at `(xStar, uStar)`. -/
lemma helperForTheorem_39_5_indicatorAdjointInfimalConvolution_eval_eq_negIndicatorFiberInfimalConvolution
    {m n : ℕ} (A₁ A₂ : ConvexProcess m n) (xStar : Fin n → ℝ) (uStar : Fin m → ℝ) :
    bifunctionInfimalConvolutionInSecond
        (bifunctionAdjoint (ConvexProcess.indicatorBifunction A₁))
        (bifunctionAdjoint (ConvexProcess.indicatorBifunction A₂))
        (dotProductEquiv ℝ (Fin n) (-xStar))
        (dotProductEquiv ℝ (Fin m) (-uStar)) =
      bifunctionInfimalConvolutionInSecond
        (fun xStar uStar =>
          negIndicatorEReal
            ((adjointVecOriented ConvexSetOrientation.supremum A₁).toSetValued xStar) uStar)
        (fun xStar uStar =>
          negIndicatorEReal
            ((adjointVecOriented ConvexSetOrientation.supremum A₂).toSetValued xStar) uStar)
        xStar uStar := by
  rw [bifunctionInfimalConvolutionInSecond, bifunctionInfimalConvolutionInSecond]
  apply le_antisymm
  · -- Step 1: every vector candidate `v` on the right is represented by the signed dual witness
    -- `dotProductEquiv (-v)` on the left.
    refine le_iInf ?_
    intro v
    refine le_trans (iInf_le _ (dotProductEquiv ℝ (Fin m) (-v))) ?_
    have hFirst :
        bifunctionAdjoint (ConvexProcess.indicatorBifunction A₁)
            (dotProductEquiv ℝ (Fin n) (-xStar))
            (dotProductEquiv ℝ (Fin m) (-uStar) - dotProductEquiv ℝ (Fin m) (-v)) =
          negIndicatorEReal
            ((adjointVecOriented ConvexSetOrientation.supremum A₁).toSetValued xStar)
            (uStar - v) := by
      have hRewrite :
          dotProductEquiv ℝ (Fin m) (-uStar) - dotProductEquiv ℝ (Fin m) (-v) =
            dotProductEquiv ℝ (Fin m) (-(uStar - v)) := by
        ext u
        simp [dotProductEquiv_apply_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      rw [hRewrite]
      simpa using
        helperForTheorem_39_5_bifunctionAdjoint_indicator_eq_negIndicator_supremumAdjointFiber
          A₁ xStar (uStar - v)
    have hSecond :
        bifunctionAdjoint (ConvexProcess.indicatorBifunction A₂)
            (dotProductEquiv ℝ (Fin n) (-xStar))
            (dotProductEquiv ℝ (Fin m) (-v)) =
          negIndicatorEReal
            ((adjointVecOriented ConvexSetOrientation.supremum A₂).toSetValued xStar) v := by
      simpa using
        helperForTheorem_39_5_bifunctionAdjoint_indicator_eq_negIndicator_supremumAdjointFiber
          A₂ xStar v
    rw [hFirst, hSecond]
  · -- Step 2: conversely, every dual witness `y` on the left is pulled back to the vector
    -- `v = -((dotProductEquiv).symm y)` on the right.
    refine le_iInf ?_
    intro y
    refine le_trans (iInf_le _ (-((dotProductEquiv ℝ (Fin m)).symm y))) ?_
    have hy :
        dotProductEquiv ℝ (Fin m) (-(-((dotProductEquiv ℝ (Fin m)).symm y))) = y := by
      simp
    have hFirst :
        negIndicatorEReal
            ((adjointVecOriented ConvexSetOrientation.supremum A₁).toSetValued xStar)
            (uStar - -((dotProductEquiv ℝ (Fin m)).symm y)) =
          bifunctionAdjoint (ConvexProcess.indicatorBifunction A₁)
            (dotProductEquiv ℝ (Fin n) (-xStar))
            (dotProductEquiv ℝ (Fin m) (-uStar) - y) := by
      have hRewrite :
          dotProductEquiv ℝ (Fin m) (-(uStar - -((dotProductEquiv ℝ (Fin m)).symm y))) =
            dotProductEquiv ℝ (Fin m) (-uStar) - y := by
        ext u
        simp [dotProductEquiv_apply_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      calc
        negIndicatorEReal
            ((adjointVecOriented ConvexSetOrientation.supremum A₁).toSetValued xStar)
            (uStar - -((dotProductEquiv ℝ (Fin m)).symm y)) =
          bifunctionAdjoint (ConvexProcess.indicatorBifunction A₁)
            (dotProductEquiv ℝ (Fin n) (-xStar))
            (dotProductEquiv ℝ (Fin m)
              (-(uStar - -((dotProductEquiv ℝ (Fin m)).symm y)))) := by
                symm
                simpa using
                  helperForTheorem_39_5_bifunctionAdjoint_indicator_eq_negIndicator_supremumAdjointFiber
                    A₁ xStar (uStar - -((dotProductEquiv ℝ (Fin m)).symm y))
        _ =
          bifunctionAdjoint (ConvexProcess.indicatorBifunction A₁)
            (dotProductEquiv ℝ (Fin n) (-xStar))
            (dotProductEquiv ℝ (Fin m) (-uStar) - y) := by rw [hRewrite]
    have hSecond :
        negIndicatorEReal
            ((adjointVecOriented ConvexSetOrientation.supremum A₂).toSetValued xStar)
            (-((dotProductEquiv ℝ (Fin m)).symm y)) =
          bifunctionAdjoint (ConvexProcess.indicatorBifunction A₂)
            (dotProductEquiv ℝ (Fin n) (-xStar)) y := by
      calc
        negIndicatorEReal
            ((adjointVecOriented ConvexSetOrientation.supremum A₂).toSetValued xStar)
            (-((dotProductEquiv ℝ (Fin m)).symm y)) =
          bifunctionAdjoint (ConvexProcess.indicatorBifunction A₂)
            (dotProductEquiv ℝ (Fin n) (-xStar))
            (dotProductEquiv ℝ (Fin m) (-(-((dotProductEquiv ℝ (Fin m)).symm y)))) := by
                symm
                simpa using
                  helperForTheorem_39_5_bifunctionAdjoint_indicator_eq_negIndicator_supremumAdjointFiber
                    A₂ xStar (-((dotProductEquiv ℝ (Fin m)).symm y))
        _ =
          bifunctionAdjoint (ConvexProcess.indicatorBifunction A₂)
            (dotProductEquiv ℝ (Fin n) (-xStar)) y := by
              simpa using congrArg
                (bifunctionAdjoint (ConvexProcess.indicatorBifunction A₂)
                  (dotProductEquiv ℝ (Fin n) (-xStar))) hy
    rw [hFirst, hSecond]

/-- Helper for Theorem 39.5: the chosen sum process really has the Minkowski-sum fibers promised by
Proposition 39.0.7. -/
lemma helperForTheorem_39_5_addProcess_toSetValued {m n : ℕ}
    (A₁ A₂ : ConvexProcess m n) :
    (addProcess A₁ A₂).toSetValued = addSetValued A₁ A₂ := by
  -- Step 1: unpack the choice made in the definition of `addProcess`.
  exact Classical.choose_spec ((prop_39_0_7 (A := A₁) (B := A₂) (r := (1 : ℝ))).2.1)

/-- Helper for Theorem 39.5: every sum of oriented adjoint fibers is automatically contained in the
adjoint fiber of the summed process. -/
lemma helperForTheorem_39_5_adjointSum_subset_adjointAddProcess {m n : ℕ}
    (o : ConvexSetOrientation) (A₁ A₂ : ConvexProcess m n) (xStar : Fin n → ℝ) :
    ((adjointVecOriented o A₁).toSetValued xStar +
        (adjointVecOriented o A₂).toSetValued xStar) ⊆
      (adjointVecOriented o (addProcess A₁ A₂)).toSetValued xStar := by
  intro uStar huStar
  rcases Set.mem_add.1 huStar with ⟨uStar₁, huStar₁, uStar₂, huStar₂, rfl⟩
  have hAddProcess :
      (addProcess A₁ A₂).toSetValued = addSetValued A₁ A₂ :=
    helperForTheorem_39_5_addProcess_toSetValued A₁ A₂
  cases o
  · -- Step 1: in supremum orientation, add the two majorant inequalities coming from `A₁*` and
    -- `A₂*`, then rewrite the target fiber through the Minkowski decomposition of `x`.
    intro u x hx
    have hxAdd : x ∈ addSetValued A₁ A₂ u := by
      simpa [hAddProcess] using hx
    rcases Set.mem_add.1 hxAdd with ⟨x₁, hx₁, x₂, hx₂, rfl⟩
    have h₁ := huStar₁ u x₁ hx₁
    have h₂ := huStar₂ u x₂ hx₂
    have hSum :
        finDot u uStar₁ + finDot u uStar₂ ≥ finDot x₁ xStar + finDot x₂ xStar :=
      add_le_add h₁ h₂
    simpa [finDot, dotProduct_add, add_dotProduct, add_comm, add_left_comm, add_assoc] using hSum
  · -- Step 2: the infimum branch is the same bookkeeping with the inequalities reversed.
    intro u x hx
    have hxAdd : x ∈ addSetValued A₁ A₂ u := by
      simpa [hAddProcess] using hx
    rcases Set.mem_add.1 hxAdd with ⟨x₁, hx₁, x₂, hx₂, rfl⟩
    have h₁ := huStar₁ u x₁ hx₁
    have h₂ := huStar₂ u x₂ hx₂
    have hSum :
        finDot u uStar₁ + finDot u uStar₂ ≤ finDot x₁ xStar + finDot x₂ xStar :=
      add_le_add h₁ h₂
    simpa [finDot, dotProduct_add, add_dotProduct, add_comm, add_left_comm, add_assoc] using hSum

/-- Helper for Theorem 39.5: the graph of the raw Minkowski sum of adjoint fibers already sits
inside the graph of the adjoint of `A₁ + A₂`. -/
lemma helperForTheorem_39_5_adjointSum_graph_subset {m n : ℕ}
    (o : ConvexSetOrientation) (A₁ A₂ : ConvexProcess m n) :
    setValuedGraph
        (fun xStar =>
          (adjointVecOriented o A₁).toSetValued xStar +
            (adjointVecOriented o A₂).toSetValued xStar) ⊆
      setValuedGraph ((adjointVecOriented o (addProcess A₁ A₂)).toSetValued) := by
  intro p hp
  -- Step 1: graph membership is fiber membership at the displayed base point.
  simpa [setValuedGraph] using
    helperForTheorem_39_5_adjointSum_subset_adjointAddProcess o A₁ A₂ p.1 hp

/-- Helper for Theorem 39.5: taking closures preserves the already-proved graph inclusion from
the raw adjoint sum into the adjoint of `A₁ + A₂`. -/
lemma helperForTheorem_39_5_adjointSum_graph_closure_subset {m n : ℕ}
    (o : ConvexSetOrientation) (A₁ A₂ : ConvexProcess m n) :
    closure
        (setValuedGraph
          (fun xStar =>
            (adjointVecOriented o A₁).toSetValued xStar +
              (adjointVecOriented o A₂).toSetValued xStar)) ⊆
      closure
        (setValuedGraph ((adjointVecOriented o (addProcess A₁ A₂)).toSetValued)) := by
  -- Step 1: closure is monotone, so the raw graph inclusion upgrades immediately.
  exact closure_mono (helperForTheorem_39_5_adjointSum_graph_subset o A₁ A₂)

/-- Helper for Theorem 39.5: the adjoint graph of the summed process is closed by the graph-closed
conjunct of Theorem 39.2. -/
lemma helperForTheorem_39_5_adjointAddProcess_graphClosed {m n : ℕ}
    (o : ConvexSetOrientation) (A₁ A₂ : ConvexProcess m n) :
    _root_.IsClosed
      (setValuedGraph ((adjointVecOriented o (addProcess A₁ A₂)).toSetValued)) := by
  have hClosed :
      IsClosedSetValuedMap ((adjointVecOriented o (addProcess A₁ A₂)).toSetValued) :=
    (adjointVec_closed_doubleAdjointVec_eq_cl_and_indicatorBifunctionAdjoint
      o (addProcess A₁ A₂)).2.1
  -- Step 1: `IsClosedSetValuedMap` is exactly graph closedness after unfolding the local aliases.
  simpa [IsClosedSetValuedMap, setValuedGraph', setValuedGraph] using hClosed

/-- Helper for Theorem 39.5: once the exact fiber formula is known, the corresponding graph formula
follows by closing the already-proved raw graph inclusion inside the closed adjoint graph. -/
lemma helperForTheorem_39_5_graphClosure_eq_of_exactIdentification {m n : ℕ}
    (o : ConvexSetOrientation) (A₁ A₂ : ConvexProcess m n)
    (hExact :
      (adjointVecOriented o (addProcess A₁ A₂)).toSetValued =
        fun xStar =>
          (adjointVecOriented o A₁).toSetValued xStar +
            (adjointVecOriented o A₂).toSetValued xStar) :
    setValuedGraph ((adjointVecOriented o (addProcess A₁ A₂)).toSetValued) =
      closure
        (setValuedGraph fun xStar =>
          (adjointVecOriented o A₁).toSetValued xStar +
            (adjointVecOriented o A₂).toSetValued xStar) := by
  have hClosed :
      _root_.IsClosed
        (setValuedGraph ((adjointVecOriented o (addProcess A₁ A₂)).toSetValued)) :=
    helperForTheorem_39_5_adjointAddProcess_graphClosed o A₁ A₂
  apply Set.Subset.antisymm
  · -- Step 1: after rewriting by the exact fiber identity, the adjoint graph is the raw sum graph
    -- and therefore lies in its own closure.
    intro p hp
    exact subset_closure (by simpa [setValuedGraph, hExact] using hp)
  · -- Step 2: the adjoint graph is closed, so it contains the closure of the raw sum graph once
    -- that raw graph is already included in it by the same fiber rewrite.
    exact closure_minimal
      (by
        intro p hp
        simpa [setValuedGraph, hExact] using hp)
      hClosed

/-- Helper for Theorem 39.5: if every target fiber is already the closure of the corresponding
raw fiber, then the whole target graph is exactly the closure of the raw graph. -/
lemma helperForTheorem_39_5_setValuedGraph_eq_closure_of_pointwiseFiberClosure
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A B : X → Set Y)
    (hGraphClosed : _root_.IsClosed (setValuedGraph' B))
    (hFiberClosure : ∀ x, closure (A x) = B x) :
    setValuedGraph' B = closure (setValuedGraph' A) := by
  apply Set.Subset.antisymm
  · intro p hp
    -- Step 1: keep the base point fixed and use the pointwise fiber closure to place the target
    -- graph point inside the closure of the corresponding vertical slice of the raw graph.
    have hpFiber : p.2 ∈ closure (A p.1) := by
      rw [hFiberClosure p.1]
      simpa [setValuedGraph'] using hp
    have hImageMem : p ∈ (fun y : Y => (p.1, y)) '' closure (A p.1) := by
      exact ⟨p.2, hpFiber, rfl⟩
    have hImageClosure :
        (fun y : Y => (p.1, y)) '' closure (A p.1) ⊆
          closure ((fun y : Y => (p.1, y)) '' A p.1) := by
      exact image_closure_subset_closure_image (by continuity)
    have hpImage : p ∈ closure ((fun y : Y => (p.1, y)) '' A p.1) :=
      hImageClosure hImageMem
    have hImageSubsetGraph :
        ((fun y : Y => (p.1, y)) '' A p.1) ⊆ setValuedGraph' A := by
      intro q hq
      rcases hq with ⟨y, hy, rfl⟩
      simpa [setValuedGraph'] using hy
    exact closure_mono hImageSubsetGraph hpImage
  · -- Step 2: the raw graph is fiberwise contained in the target graph, so closedness of the
    -- target graph forces it to contain the raw graph closure as well.
    exact closure_minimal
      (by
        intro p hp
        have hpFiber : p.2 ∈ A p.1 := by
          simpa [setValuedGraph'] using hp
        have hpClosure : p.2 ∈ closure (A p.1) := subset_closure hpFiber
        rw [hFiberClosure p.1] at hpClosure
        simpa [setValuedGraph'] using hpClosure)
      hGraphClosed

/-- Helper for Theorem 39.5: a closed convex process is uniquely determined by its bracket
bifunction, via the two-sided reconstruction of Theorem 39.4. -/
lemma helperForTheorem_39_5_closedConvexProcess_eq_of_bracketBifunction_eq {m n : ℕ}
    (hQualification : Section39Theorem39_4GlobalQualification m n)
    (A B : ClosedConvexProcess m n)
    (hBracket :
      bracketBifunctionOfProcess (m := m) (n := n) A.1 =
        bracketBifunctionOfProcess (m := m) (n := n) B.1) :
    A.1.toSetValued = B.1.toSetValued := by
  classical
  obtain ⟨toProcess, toBifunction, hToBifunction, _hToProcess, _hLeftInverse, hRightInverse⟩ :=
    theorem_39_4 (m := m) (n := n) hQualification
  have hBifunctionEq : toBifunction A = toBifunction B := by
    apply Subtype.ext
    -- Step 1: the forward map in Theorem 39.4 records exactly the bracket bifunction.
    calc
      (toBifunction A).1 = bracketBifunctionOfProcess (m := m) (n := n) A.1 := hToBifunction A
      _ = bracketBifunctionOfProcess (m := m) (n := n) B.1 := hBracket
      _ = (toBifunction B).1 := (hToBifunction B).symm
  have hProcessEq : A = B := by
    -- Step 2: right-invertibility transports equality of bracket packages back to the process side.
    calc
      A = toProcess (toBifunction A) := by
        symm
        exact hRightInverse A
      _ = toProcess (toBifunction B) := by rw [hBifunctionEq]
      _ = B := hRightInverse B
  -- Step 3: project the closed-process equality to the underlying set-valued mappings.
  exact congrArg ConvexProcess.toSetValued (congrArg Subtype.val hProcessEq)

/-- Helper for Theorem 39.5: every oriented adjoint fiber is closed and convex, because Theorem
39.2 already packages the adjoint as a closed convex process map. -/
lemma helperForTheorem_39_5_adjointVecOriented_fiber_closed_convex {m n : ℕ}
    (o : ConvexSetOrientation) (A : ConvexProcess m n) (xStar : Fin n → ℝ) :
    _root_.IsClosed ((adjointVecOriented o A).toSetValued xStar) ∧
      Convex ℝ ((adjointVecOriented o A).toSetValued xStar) := by
  let B : ConvexProcess n m :=
    { toSetValued := (adjointVecOriented o A).toSetValued
      map_add_superset :=
        (adjointVec_closed_doubleAdjointVec_eq_cl_and_indicatorBifunctionAdjoint o A).1.1
      map_smul_pos :=
        (adjointVec_closed_doubleAdjointVec_eq_cl_and_indicatorBifunctionAdjoint o A).1.2.1
      zero_mem :=
        (adjointVec_closed_doubleAdjointVec_eq_cl_and_indicatorBifunctionAdjoint o A).1.2.2 }
  have hBClosed : B.IsClosed := by
    -- Step 1: unpack the graph-closed conjunct of Theorem 39.2 into the local closed-process notion.
    apply (helperForProposition_39_0_13_graphClosed_iff_processClosed B).1
    simpa [B, IsClosedSetValuedMap, setValuedGraph', setValuedGraph] using
      (adjointVec_closed_doubleAdjointVec_eq_cl_and_indicatorBifunctionAdjoint o A).2.1
  -- Step 2: closed processes have closed fibers, and convex-process axioms give fiber convexity.
  constructor
  · exact (helperForProposition_39_0_6_graphClosed_and_fiberClosed B hBClosed).2 xStar
  · exact (convexProcess_prop_39_0_2 B).1 xStar

/-- Helper for Theorem 39.5: the support function of a Minkowski sum splits as the sum of the two
support functions. -/
lemma helperForTheorem_39_5_supportFunctionEReal_add {n : ℕ}
    (S T : Set (Fin n → ℝ)) :
    supportFunctionEReal (S + T) =
      fun xStar => supportFunctionEReal S xStar + supportFunctionEReal T xStar := by
  funext xStar
  -- Step 1: rewrite the support-value set of the Minkowski sum as the pairwise sum of the two
  -- support-value sets coming from the summands.
  unfold supportFunctionEReal
  have hImage :
      {z : EReal | ∃ x ∈ S + T, z = ((dotProduct x xStar : ℝ) : EReal)} =
        Set.image2 (· + ·)
          {z : EReal | ∃ x ∈ S, z = ((dotProduct x xStar : ℝ) : EReal)}
          {z : EReal | ∃ y ∈ T, z = ((dotProduct y xStar : ℝ) : EReal)} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases Set.mem_add.1 hx with ⟨x₁, hx₁, x₂, hx₂, rfl⟩
      refine ⟨((dotProduct x₁ xStar : ℝ) : EReal), ?_, ((dotProduct x₂ xStar : ℝ) : EReal), ?_,
        ?_⟩
      · exact ⟨x₁, hx₁, rfl⟩
      · exact ⟨x₂, hx₂, rfl⟩
      · simp [add_dotProduct, EReal.coe_add]
    · rintro ⟨z₁, ⟨x₁, hx₁, rfl⟩, z₂, ⟨x₂, hx₂, rfl⟩, hz⟩
      refine ⟨x₁ + x₂, Set.mem_add.2 ⟨x₁, hx₁, x₂, hx₂, rfl⟩, ?_⟩
      simpa [add_dotProduct, EReal.coe_add] using hz.symm
  -- Step 2: the supremum over pairwise sums splits into the sum of the two suprema.
  rw [hImage, section16_sSup_image2_add_eq_sSup_add]

/-- Helper for Theorem 39.5: a closed convex set is uniquely determined by its support function. -/
lemma helperForTheorem_39_5_fiber_eq_of_supportFunctionEq {n : ℕ}
    (S T : Set (Fin n → ℝ))
    (hSClosed : _root_.IsClosed S) (hSConv : Convex ℝ S)
    (hTClosed : _root_.IsClosed T) (hTConv : Convex ℝ T)
    (hSupport : supportFunctionEReal S = supportFunctionEReal T) :
    S = T := by
  have hIndicatorEq :
      indicatorFunction S = indicatorFunction T := by
    -- Step 1: for closed convex sets, the support function determines the indicator by Theorem
    -- 13.2, so equal support functions force equal indicators.
    calc
      indicatorFunction S = fenchelConjugate n (supportFunctionEReal S) := by
        symm
        exact
          (indicatorFunction_conjugate_supportFunctionEReal_of_isClosed
            (n := n) S hSConv hSClosed).2
      _ = fenchelConjugate n (supportFunctionEReal T) := by
        rw [hSupport]
      _ = indicatorFunction T := by
        exact
          (indicatorFunction_conjugate_supportFunctionEReal_of_isClosed
            (n := n) T hTConv hTClosed).2
  ext x
  constructor
  · intro hx
    -- Step 2: evaluate the indicator equality at `x` to rule out membership mismatches.
    by_contra hxT
    have hPoint := congrArg (fun f : (Fin n → ℝ) → EReal => f x) hIndicatorEq
    simp [indicatorFunction, hx, hxT] at hPoint
  · intro hx
    -- Step 3: the converse inclusion is the same pointwise indicator comparison.
    by_contra hxS
    have hPoint := congrArg (fun f : (Fin n → ℝ) → EReal => f x) hIndicatorEq
    simp [indicatorFunction, hxS, hx] at hPoint

/-- Helper for Theorem 39.5: a closed convex set is uniquely determined by its infimum-oriented
bracket, because that bracket is the negative support function of the negated set. -/
lemma helperForTheorem_39_5_fiber_eq_of_infimumBracketEq {n : ℕ}
    (S T : Set (Fin n → ℝ))
    (hSClosed : _root_.IsClosed S) (hSConv : Convex ℝ S)
    (hTClosed : _root_.IsClosed T) (hTConv : Convex ℝ T)
    (hBracket :
      setBracketVec ConvexSetOrientation.infimum S =
        setBracketVec ConvexSetOrientation.infimum T) :
    S = T := by
  have hNegSClosed : _root_.IsClosed (-S) := by
    -- Step 1: negation is continuous, so closedness transports to the negated fiber.
    have hcont : Continuous fun x : Fin n → ℝ => -x := by
      continuity
    have hpre : _root_.IsClosed ((fun x : Fin n → ℝ => -x) ⁻¹' S) := hSClosed.preimage hcont
    simpa [Set.preimage, Set.neg] using hpre
  have hNegTClosed : _root_.IsClosed (-T) := by
    -- Step 2: the same continuity argument handles the second fiber.
    have hcont : Continuous fun x : Fin n → ℝ => -x := by
      continuity
    have hpre : _root_.IsClosed ((fun x : Fin n → ℝ => -x) ⁻¹' T) := hTClosed.preimage hcont
    simpa [Set.preimage, Set.neg] using hpre
  have hNegSConv : Convex ℝ (-S) := by
    -- Step 3: convexity is preserved by negation.
    simpa using hSConv.neg
  have hNegTConv : Convex ℝ (-T) := by
    -- Step 4: likewise for the second fiber.
    simpa using hTConv.neg
  have hSupportNeg : supportFunctionEReal (-S) = supportFunctionEReal (-T) := by
    funext xStar
    -- Step 5: rewrite the infimum bracket as a negated support function and cancel the negation.
    have hPoint := congrFun hBracket xStar
    rw [helperForTheorem_39_3_infimumBracket_eq_neg_supportFunction_negFiber,
      helperForTheorem_39_3_infimumBracket_eq_neg_supportFunction_negFiber] at hPoint
    simpa using congrArg Neg.neg hPoint
  have hNegEq :
      (-S : Set (Fin n → ℝ)) = -T :=
    helperForTheorem_39_5_fiber_eq_of_supportFunctionEq (-S) (-T)
      hNegSClosed hNegSConv hNegTClosed hNegTConv hSupportNeg
  -- Step 6: cancel negation on both sides to recover equality of the original fibers.
  calc
    S = -(-S : Set (Fin n → ℝ)) := by
      ext x
      simp [Set.mem_neg]
    _ = -(-T : Set (Fin n → ℝ)) := by
      rw [hNegEq]
    _ = T := by
      ext x
      simp [Set.mem_neg]

/-- Helper for Theorem 39.5: if a convex fiber and a closed convex fiber have the same support
function, then the closure of the first fiber is the second fiber. -/
lemma helperForTheorem_39_5_closure_eq_of_supportFunctionEq {n : ℕ}
    (S T : Set (Fin n → ℝ))
    (hSConv : Convex ℝ S)
    (hTClosed : _root_.IsClosed T) (hTConv : Convex ℝ T)
    (hSupport : supportFunctionEReal S = supportFunctionEReal T) :
    closure S = T := by
  have hIndicatorEq :
      indicatorFunction (closure S) = indicatorFunction T := by
    -- Step 1: the support function determines the indicator of the closure on the left, while the
    -- closed-convex hypothesis identifies the right-hand indicator exactly.
    calc
      indicatorFunction (closure S) = fenchelConjugate n (supportFunctionEReal S) := by
        symm
        exact section16_fenchelConjugate_supportFunctionEReal_eq_indicatorFunction_closure S hSConv
      _ = fenchelConjugate n (supportFunctionEReal T) := by
        rw [hSupport]
      _ = indicatorFunction T := by
        exact
          (indicatorFunction_conjugate_supportFunctionEReal_of_isClosed
            (n := n) T hTConv hTClosed).2
  ext x
  constructor
  · intro hx
    -- Step 2: evaluate the indicator equality at `x` to rule out points of `closure S` that are
    -- absent from the closed target fiber.
    by_contra hxT
    have hPoint := congrArg (fun f : (Fin n → ℝ) → EReal => f x) hIndicatorEq
    simp [indicatorFunction, hx, hxT] at hPoint
  · intro hx
    -- Step 3: every point of the target fiber belongs to `closure S`, since otherwise the same
    -- pointwise indicator comparison would separate the two sides.
    by_contra hxClosure
    have hPoint := congrArg (fun f : (Fin n → ℝ) → EReal => f x) hIndicatorEq
    simp [indicatorFunction, hxClosure, hx] at hPoint

/-- Helper for Theorem 39.5: if a convex fiber and a closed convex fiber have the same
infimum-oriented bracket, then the closure of the first fiber is the second fiber. -/
lemma helperForTheorem_39_5_closure_eq_of_infimumBracketEq {n : ℕ}
    (S T : Set (Fin n → ℝ))
    (hSConv : Convex ℝ S)
    (hTClosed : _root_.IsClosed T) (hTConv : Convex ℝ T)
    (hBracket :
      setBracketVec ConvexSetOrientation.infimum S =
        setBracketVec ConvexSetOrientation.infimum T) :
    closure S = T := by
  have hNegSConv : Convex ℝ (-S) := by
    -- Step 1: negate the first fiber so the infimum bracket becomes an ordinary support
    -- function.
    simpa using hSConv.neg
  have hNegTClosed : _root_.IsClosed (-T) := by
    -- Step 2: closedness is preserved by the continuous involution `x ↦ -x`.
    have hcont : Continuous fun x : Fin n → ℝ => -x := by
      continuity
    have hpre : _root_.IsClosed ((fun x : Fin n → ℝ => -x) ⁻¹' T) := hTClosed.preimage hcont
    simpa [Set.preimage, Set.neg] using hpre
  have hNegTConv : Convex ℝ (-T) := by
    -- Step 3: convexity is preserved by negation on the closed target fiber as well.
    simpa using hTConv.neg
  have hSupportNeg : supportFunctionEReal (-S) = supportFunctionEReal (-T) := by
    funext xStar
    -- Step 4: rewrite both infimum brackets as negative support functions of the negated fibers.
    have hPoint := congrFun hBracket xStar
    rw [helperForTheorem_39_3_infimumBracket_eq_neg_supportFunction_negFiber,
      helperForTheorem_39_3_infimumBracket_eq_neg_supportFunction_negFiber] at hPoint
    simpa using congrArg Neg.neg hPoint
  have hClosureNeg : closure (-S : Set (Fin n → ℝ)) = -T :=
    helperForTheorem_39_5_closure_eq_of_supportFunctionEq (-S) (-T)
      hNegSConv hNegTClosed hNegTConv hSupportNeg
  have hNegClosureImage : closure (-S : Set (Fin n → ℝ)) = -closure S := by
    -- Step 5: the negation homeomorphism transports closures exactly.
    calc
      closure (-S : Set (Fin n → ℝ)) = closure ((fun x : Fin n → ℝ => -x) '' S) := by
        rw [Set.image_neg_eq_neg]
      _ = (fun x : Fin n → ℝ => -x) '' closure S := by
        exact
          (Homeomorph.neg (Fin n → ℝ)).isClosedMap.closure_image_eq_of_continuous
            (Homeomorph.neg (Fin n → ℝ)).continuous S
      _ = -closure S := by
        rw [Set.image_neg_eq_neg]
  calc
    closure S = -(-closure S : Set (Fin n → ℝ)) := by
      -- Step 6: introduce a double negation on the closed fiber.
      ext x
      constructor
      · intro hx
        change -x ∈ (-closure S : Set (Fin n → ℝ))
        change -(-x) ∈ closure S
        simpa using hx
      · intro hx
        change -(-x) ∈ closure S at hx
        simpa using hx
    _ = -closure (-S : Set (Fin n → ℝ)) := by
      -- Step 7: replace the inner negated closure using the homeomorphic image formula.
      rw [hNegClosureImage]
    _ = -(-T : Set (Fin n → ℝ)) := by
      -- Step 8: substitute the reconstructed closure of the negated fiber.
      rw [hClosureNeg]
    _ = T := by
      -- Step 9: cancel the double negation to recover the original target fiber.
      ext x
      simp


end ConvexProcess

end Section39
end Chap08

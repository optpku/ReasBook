/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section29_part3

section Chap06
section Section29

local notation "ConvexBifunction" => BundledConvexBifunction

/-- Helper for Corollary 6.29.2: for the perturbation function at the origin, existence of a
Kuhn--Tucker vector is equivalent to nonemptiness of the ordinary subdifferential. -/
lemma helperForCorollary_6_29_2_noKuhnTucker_iff_subdifferentialEmptyAtOrigin
    {m n : ℕ} (F : ConvexBifunction m n)
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F)) :
    let p := generalizedConvexProgramPerturbationFunction F
    (¬ ∃ uStar : Fin m → ℝ, IsKuhnTuckerVector F uStar) ↔
      ¬ Set.Nonempty (subdifferentialAt p 0) := by
  let p : (Fin m → ℝ) → EReal := generalizedConvexProgramPerturbationFunction F
  have hKT :
      ∀ uStar : Fin m → ℝ,
        IsKuhnTuckerVector F uStar ↔ -uStar ∈ euclideanSubdifferentialAt p 0 :=
    (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).2.2 hfinite
  have hExistsKT :
      (∃ uStar : Fin m → ℝ, IsKuhnTuckerVector F uStar) ↔
        Set.Nonempty (subdifferentialAt p 0) := by
    constructor
    · rintro ⟨uStar, huStar⟩
      -- Rewrite the Kuhn--Tucker witness as an ordinary subgradient through `dotProductEquiv`.
      have huSub : -uStar ∈ euclideanSubdifferentialAt p 0 := (hKT uStar).1 huStar
      exact ⟨dotProductEquiv ℝ (Fin m) (-uStar), by
        simpa [euclideanSubdifferentialAt] using huSub⟩
    · rintro ⟨g, hg⟩
      -- Pull an ordinary subgradient back to a vector witness for the Euclidean fiber.
      let uStar : Fin m → ℝ := -((dotProductEquiv ℝ (Fin m)).symm g)
      have huSub : -uStar ∈ euclideanSubdifferentialAt p 0 := by
        have hgVec : (dotProductEquiv ℝ (Fin m)).symm g ∈ euclideanSubdifferentialAt p 0 := by
          simpa [euclideanSubdifferentialAt] using hg
        simpa [uStar] using hgVec
      exact ⟨uStar, (hKT uStar).2 huSub⟩
  -- Negating the existence statements yields the desired emptiness criterion.
  simpa [p] using not_congr hExistsKT

/-- Helper for Corollary 6.29.2: if the perturbation subdifferential at the origin is empty,
Theorem 23.3 produces a direction whose right and left directional quotients both tend to `-∞`. -/
lemma helperForCorollary_6_29_2_exists_bilateralDirectionalDerivative_eq_bot_of_empty_subdifferential
    {m n : ℕ} (F : ConvexBifunction m n)
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F)) :
    let p := generalizedConvexProgramPerturbationFunction F
    ¬ Set.Nonempty (subdifferentialAt p 0) →
      ∃ u : Fin m → ℝ,
        Filter.Tendsto (directionalDifferenceQuotientAt p 0 u)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (⊥ : EReal)) ∧
        Filter.Tendsto (directionalDifferenceQuotientAt p 0 u)
          (nhdsWithin (0 : ℝ) (Set.Iio 0)) (nhds (⊥ : EReal)) := by
  dsimp
  let p : (Fin m → ℝ) → EReal := generalizedConvexProgramPerturbationFunction F
  have hpConv :
      ConvexFunction p :=
    (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).1
  have hpFinite : p 0 ≠ (⊤ : EReal) ∧ p 0 ≠ (⊥ : EReal) :=
    helperForCorollary_6_29_1_perturbationAt_zero_finite F hfinite
  intro hNoSub
  -- Theorem 23.3 provides the direction with `D u = ⊥` and `D (-u) = ⊤`.
  rcases
      (proper_of_subdifferentiableAt_or_infiniteDirectionalDerivative_to_relativeInterior
        p hpConv 0 hpFinite).2 hNoSub with
    ⟨⟨u, huBot, huNegTop⟩, _⟩
  rcases convex_directionalDerivative_monotone_exists_and_sublinear p hpConv 0 hpFinite with
    ⟨hdir, _hpos, _hconv, _hzero, _hsymm⟩
  have hRight :
      Filter.Tendsto (directionalDifferenceQuotientAt p 0 u)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (⊥ : EReal)) := by
    -- The monotone right derivative theorem identifies the right limit with `D u = ⊥`.
    simpa [huBot] using (hdir u).2.1
  have hLeft :
      Filter.Tendsto (directionalDifferenceQuotientAt p 0 u)
        (nhdsWithin (0 : ℝ) (Set.Iio 0)) (nhds (⊥ : EReal)) := by
    -- The left quotient along `u` is the negated right quotient along `-u`.
    have hNegRight :
        Filter.Tendsto (directionalDifferenceQuotientAt p 0 (-u))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (⊤ : EReal)) := by
      simpa [huNegTop] using (hdir (-u)).2.1
    simpa using
      (bilateralDirectionalDerivative_iff_exists_neg_direction
        (f := p) (x := 0) (y := u) hpFinite).1 (⊤ : EReal) hNegRight
  exact ⟨u, hRight, hLeft⟩

/-- Helper for Corollary 6.29.2: the right-hand `-∞` limit identifies the origin directional
derivative with `-∞`. -/
lemma helperForCorollary_6_29_2_originDirectionalDerivative_eq_bot_of_rightLimit
    {m n : ℕ} (F : ConvexBifunction m n)
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F)) (u : Fin m → ℝ) :
    Filter.Tendsto
        (directionalDifferenceQuotientAt (generalizedConvexProgramPerturbationFunction F) 0 u)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (⊥ : EReal)) →
      generalizedConvexProgramOriginDirectionalDerivative F u = (⊥ : EReal) := by
  let p : (Fin m → ℝ) → EReal := generalizedConvexProgramPerturbationFunction F
  have hpConv :
      ConvexFunction p :=
    (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).1
  have hpFinite : p 0 ≠ (⊤ : EReal) ∧ p 0 ≠ (⊥ : EReal) :=
    helperForCorollary_6_29_1_perturbationAt_zero_finite F hfinite
  intro hRight
  -- Uniqueness of limits forces the abstract upper directional derivative to match the given one.
  have hKnown :
      Filter.Tendsto (directionalDifferenceQuotientAt p 0 u)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (upperDirectionalDerivativeAt p 0 u)) :=
    (convex_directionalDerivative_monotone_exists_and_sublinear p hpConv 0 hpFinite).1 u |>.2.1
  have hEq : (⊥ : EReal) = upperDirectionalDerivativeAt p 0 u :=
    tendsto_nhds_unique hRight hKnown
  simpa [p, generalizedConvexProgramOriginDirectionalDerivative] using hEq.symm

/-- Helper for Corollary 6.29.2: a bilateral `-∞` directional quotient rules out every
Kuhn--Tucker vector, because the minorant from Corollary 6.29.1 would compare a finite linear
functional to `-∞`. -/
lemma helperForCorollary_6_29_2_noKuhnTucker_of_bilateralDirectionalDerivative_eq_bot
    {m n : ℕ} (F : ConvexBifunction m n)
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F)) :
    (∃ u : Fin m → ℝ,
      Filter.Tendsto
          (directionalDifferenceQuotientAt (generalizedConvexProgramPerturbationFunction F) 0 u)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (⊥ : EReal)) ∧
      Filter.Tendsto
          (directionalDifferenceQuotientAt (generalizedConvexProgramPerturbationFunction F) 0 u)
          (nhdsWithin (0 : ℝ) (Set.Iio 0)) (nhds (⊥ : EReal))) →
      ¬ ∃ uStar : Fin m → ℝ, IsKuhnTuckerVector F uStar := by
  rintro ⟨u, hRight, _hLeft⟩ ⟨uStar, huStar⟩
  have hDirBot :
      generalizedConvexProgramOriginDirectionalDerivative F u = (⊥ : EReal) :=
    helperForCorollary_6_29_2_originDirectionalDerivative_eq_bot_of_rightLimit
      F hfinite u hRight
  have hMinor :
      (((dotProduct (-u) uStar : ℝ) : EReal)) ≤
        generalizedConvexProgramOriginDirectionalDerivative F (-(-u)) :=
    (helperForCorollary_6_29_1_kuhnTucker_iff_negatedDirectionalDerivative_minorant
      F hfinite uStar).1 huStar (-u)
  have hBotMinor : (((dotProduct (-u) uStar : ℝ) : EReal)) ≤ (⊥ : EReal) := by
    simpa [hDirBot] using hMinor
  exact (not_le_of_gt (EReal.bot_lt_coe (dotProduct (-u) uStar))) hBotMinor

-- Proof sketch: combine Corollary 6.29.1 with Theorem 6.29.1. The finite optimal-value
-- hypothesis identifies Kuhn--Tucker vectors with the negative Euclidean subdifferential of the
-- perturbation function at `0`; then apply the Chapter 23 criterion saying that emptiness of that
-- subdifferential is equivalent to the existence of a direction with bilateral directional
-- derivative `-∞`.
/-- Corollary 6.29.2: let `F` be a convex bifunction from `ℝ^m` to `ℝ^n`, and suppose the
optimal value in the associated generalized convex program `(P)` is finite. Then a Kuhn--Tucker
vector for `(P)` fails to exist if and only if there is a perturbation direction `u ∈ ℝ^m` such
that the two-sided directional derivative of `inf F` at the origin along `u` exists and is
`-∞`. -/
theorem generalizedConvexProgram_noKuhnTuckerVector_iff_exists_bilateralDirectionalDerivative_eq_bot
    {m n : ℕ} (F : ConvexBifunction m n)
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F)) :
    (¬ ∃ uStar : Fin m → ℝ, IsKuhnTuckerVector F uStar) ↔
      ∃ u : Fin m → ℝ,
        Filter.Tendsto
            (directionalDifferenceQuotientAt
              (generalizedConvexProgramPerturbationFunction F) 0 u)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (⊥ : EReal)) ∧
        Filter.Tendsto
            (directionalDifferenceQuotientAt
              (generalizedConvexProgramPerturbationFunction F) 0 u)
            (nhdsWithin (0 : ℝ) (Set.Iio 0)) (nhds (⊥ : EReal)) := by
  -- Rewrite the Kuhn--Tucker failure condition as emptiness of the perturbation subdifferential.
  have hNoKTiff :
      (¬ ∃ uStar : Fin m → ℝ, IsKuhnTuckerVector F uStar) ↔
        ¬ Set.Nonempty
          (subdifferentialAt (generalizedConvexProgramPerturbationFunction F) 0) :=
    helperForCorollary_6_29_2_noKuhnTucker_iff_subdifferentialEmptyAtOrigin F hfinite
  constructor
  · intro hNoKT
    have hNoSub :
        ¬ Set.Nonempty
          (subdifferentialAt (generalizedConvexProgramPerturbationFunction F) 0) :=
      hNoKTiff.1 hNoKT
    -- Empty subdifferential gives the bilateral `-∞` witness promised by Theorem 23.3.
    exact
      helperForCorollary_6_29_2_exists_bilateralDirectionalDerivative_eq_bot_of_empty_subdifferential
        F hfinite hNoSub
  · intro hBilat
    -- A bilateral `-∞` witness contradicts every linear minorant coming from Kuhn--Tucker.
    exact
      helperForCorollary_6_29_2_noKuhnTucker_of_bilateralDirectionalDerivative_eq_bot
        F hfinite hBilat

-- Proof sketch: combine Theorem 6.29.1 with the Chapter 25 differentiability criterion for
-- convex functions. The finite optimal-value hypothesis identifies Kuhn--Tucker vectors with the
-- negatives of the Euclidean subgradients of `inf F` at `0`; uniqueness of that subgradient is
-- equivalent to differentiability at the origin, and the unique Kuhn--Tucker vector is therefore
-- the negative gradient, whose coordinates are the partial derivatives of `inf F` at `0`.
/-- Helper for Corollary 6.29.3: uniqueness of Kuhn--Tucker vectors is equivalent to uniqueness
of Euclidean subgradients of the perturbation function at the origin. -/
lemma helperForCorollary_6_29_3_uniqueKuhnTucker_iff_uniqueEuclideanSubgradientAtOrigin
    {m n : ℕ} (F : ConvexBifunction m n)
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F)) :
    let p := generalizedConvexProgramPerturbationFunction F
    (∃! uStar : Fin m → ℝ, IsKuhnTuckerVector F uStar) ↔
      ∃! g : Fin m → ℝ, g ∈ euclideanSubdifferentialAt p 0 := by
  let p : (Fin m → ℝ) → EReal := generalizedConvexProgramPerturbationFunction F
  have hKT :
      ∀ uStar : Fin m → ℝ,
        IsKuhnTuckerVector F uStar ↔ -uStar ∈ euclideanSubdifferentialAt p 0 :=
    (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).2.2 hfinite
  constructor
  · rintro ⟨uStar, huStar, huniq⟩
    refine ⟨-uStar, ?_, ?_⟩
    · -- Translate the unique Kuhn--Tucker witness through the sign convention of Theorem 6.29.1.
      simpa using (hKT uStar).1 huStar
    · intro g hg
      -- Pull any competing Euclidean subgradient back to a Kuhn--Tucker vector by negation.
      have huKT : IsKuhnTuckerVector F (-g) := by
        have hg' : -(-g) ∈ euclideanSubdifferentialAt p 0 := by
          simpa using hg
        exact (hKT (-g)).2 hg'
      have hEq : -g = uStar := huniq (-g) huKT
      simpa using congrArg Neg.neg hEq
  · rintro ⟨g, hg, huniq⟩
    refine ⟨-g, ?_, ?_⟩
    · -- The distinguished Euclidean subgradient gives the Kuhn--Tucker witness after negation.
      have hg' : -(-g) ∈ euclideanSubdifferentialAt p 0 := by
        simpa using hg
      exact (hKT (-g)).2 hg'
    · intro uStar huStar
      -- Uniqueness on the subgradient side transfers back through the same involution.
      have huSub : -uStar ∈ euclideanSubdifferentialAt p 0 := (hKT uStar).1 huStar
      have hEq : -uStar = g := huniq (-uStar) huSub
      simpa using congrArg Neg.neg hEq

/-- Helper for Corollary 6.29.3: uniqueness of the Euclidean subgradient of the perturbation
function at the origin is equivalent to differentiability there. -/
lemma helperForCorollary_6_29_3_uniqueEuclideanSubgradientAtOrigin_iff_differentiableAtOrigin
    {m n : ℕ} (F : ConvexBifunction m n)
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F)) :
    let p := generalizedConvexProgramPerturbationFunction F
    (∃! g : Fin m → ℝ, g ∈ euclideanSubdifferentialAt p 0) ↔
      ERealDifferentiableAt p 0 := by
  let p : (Fin m → ℝ) → EReal := generalizedConvexProgramPerturbationFunction F
  have hpConv : ConvexFunction p :=
    (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).1
  have hpFinite : p 0 ≠ (⊤ : EReal) ∧ p 0 ≠ (⊥ : EReal) :=
    helperForCorollary_6_29_1_perturbationAt_zero_finite F hfinite
  constructor
  · intro huniq
    -- Rewrite Euclidean subgradient uniqueness into the `IsSubgradientAt` form used by Chapter 25.
    have huniqSub :
        ∃! g : Fin m → ℝ, IsSubgradientAt p 0 (dotProductEquiv ℝ (Fin m) g) := by
      simpa [euclideanSubdifferentialAt, IsEuclideanSubgradientAt, subdifferentialAt] using huniq
    exact
      (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
        p hpConv 0 hpFinite).2 huniqSub
  · intro hDiff
    rcases
        (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
          p hpConv 0 hpFinite).1 hDiff with
      ⟨hsub, _hminorant, huniq⟩
    refine ⟨erealGradientAt hDiff, ?_, ?_⟩
    · -- Differentiability supplies the distinguished Euclidean subgradient, namely the gradient.
      simpa [euclideanSubdifferentialAt, IsEuclideanSubgradientAt, subdifferentialAt] using hsub
    · intro g hg
      -- The Chapter 25 uniqueness clause identifies every Euclidean subgradient with that gradient.
      exact huniq g
        (by
          simpa [euclideanSubdifferentialAt, IsEuclideanSubgradientAt, subdifferentialAt] using hg)

/-- Helper for Corollary 6.29.3: when the perturbation function is differentiable at the origin,
the negative gradient is a Kuhn--Tucker vector. -/
lemma helperForCorollary_6_29_3_isKuhnTuckerVector_negGradient_of_differentiableAtOrigin
    {m n : ℕ} (F : ConvexBifunction m n)
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F))
    (hDiff : ERealDifferentiableAt (generalizedConvexProgramPerturbationFunction F) 0) :
    IsKuhnTuckerVector F (-erealGradientAt hDiff) := by
  let p : (Fin m → ℝ) → EReal := generalizedConvexProgramPerturbationFunction F
  have hpConv : ConvexFunction p :=
    (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).1
  have hpFinite : p 0 ≠ (⊤ : EReal) ∧ p 0 ≠ (⊥ : EReal) :=
    helperForCorollary_6_29_1_perturbationAt_zero_finite F hfinite
  have hKT :
      ∀ uStar : Fin m → ℝ,
        IsKuhnTuckerVector F uStar ↔ -uStar ∈ euclideanSubdifferentialAt p 0 :=
    (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).2.2 hfinite
  rcases
      (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
        p hpConv 0 hpFinite).1 hDiff with
    ⟨hsub, _hminorant, _huniq⟩
  have hgradMem : erealGradientAt hDiff ∈ euclideanSubdifferentialAt p 0 := by
    -- The gradient is the Euclidean subgradient singled out by differentiability.
    simpa [euclideanSubdifferentialAt, IsEuclideanSubgradientAt, subdifferentialAt] using hsub
  -- Apply the Kuhn--Tucker/subgradient equivalence to the candidate `-∇ p(0)`.
  exact (hKT (-erealGradientAt hDiff)).2 (by simpa using hgradMem)

/-- Corollary 6.29.3: Let `F` be a convex bifunction from `ℝ^m` to `ℝ^n`, and suppose the
optimal value in the associated generalized convex program `(P)` is finite. Then `(P)` has a
unique Kuhn--Tucker vector if and only if the perturbation function `inf F` is differentiable at
`u = 0`. In that case the unique Kuhn--Tucker vector `uStar = (v₁*, …, v_m*)` is the negative
gradient of `inf F` at `0`, equivalently `v_i* = -∂(inf F) / ∂v_i |_(u = 0)` for each `i`. -/
theorem generalizedConvexProgram_uniqueKuhnTuckerVector_iff_differentiableAt_zero
    {m n : ℕ} (F : ConvexBifunction m n)
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F)) :
    ((∃! uStar : Fin m → ℝ, IsKuhnTuckerVector F uStar) ↔
      ERealDifferentiableAt (generalizedConvexProgramPerturbationFunction F) 0) ∧
    ∀ hDiff : ERealDifferentiableAt (generalizedConvexProgramPerturbationFunction F) 0,
      ∃! uStar : Fin m → ℝ,
        IsKuhnTuckerVector F uStar ∧
          ∀ i : Fin m, uStar i = -(erealGradientAt hDiff i) := by
  constructor
  · -- Chain the sign-translation helper with the Chapter 25 differentiability criterion.
    exact
      (helperForCorollary_6_29_3_uniqueKuhnTucker_iff_uniqueEuclideanSubgradientAtOrigin
        F hfinite).trans
        (helperForCorollary_6_29_3_uniqueEuclideanSubgradientAtOrigin_iff_differentiableAtOrigin
          F hfinite)
  · intro hDiff
    refine ⟨-erealGradientAt hDiff, ?_, ?_⟩
    · constructor
      · -- The negative gradient is the Kuhn--Tucker vector prescribed by Theorem 6.29.1.
        exact
          helperForCorollary_6_29_3_isKuhnTuckerVector_negGradient_of_differentiableAtOrigin
            F hfinite hDiff
      · -- Its coordinates are definitionally the negatives of the gradient coordinates.
        intro i
        simp
    · intro uStar huStar
      -- The coordinate formula already determines the witness uniquely by extensionality.
      ext i
      exact huStar.2 i

/-- Definition 6.29.20: The convex program `(P)` associated with a convex bifunction `F`
is consistent if it has feasible solutions, equivalently if the zero perturbation belongs
to `dom F`. -/
def generalizedConvexProgramConsistentAtOrigin {m n : ℕ} (F : ConvexBifunction m n) : Prop :=
  (0 : Fin m → ℝ) ∈ bifunctionEffectiveDomain F.1

end Section29
end Chap06

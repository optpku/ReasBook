/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section04_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section07_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section07_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part11
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part11

section Chap05
section Section24

open scoped ConvexAnalysis

attribute [local instance] Classical.propDecidable

-- Proof sketch: follow the textbook proof. Let `J` be the interval where `φ` is finite and define
-- the specific primitive `f(x) = ∫_a^x φ(t) dt`, then prove convexity from the two integral
-- estimates around an intermediate point `z`. Directly from the integral difference quotients,
-- prove `f'_-(x) ≤ φ x ≤ f'_+(x)` and then identify `f'_-(x) = φ_-(x)` and `f'_+(x) = φ_+(x)`.
-- For uniqueness, if another closed proper convex `g` satisfies the same derivative band, then on
-- the common relative interior of the finite interval `J` the difference `h = f - g` has
-- vanishing one-sided derivatives, hence is constant there; closedness extends the same additive
-- constant to all of `ℝ`.
/-- Theorem 5.24.4: if `φ : ℝ → EReal` is nondecreasing and `φ(a)` is finite, then the specific
interval-integral primitive `f(x) = ∫_a^x φ(t) dt`, normalized by `f(a) = 0`, is a closed proper
convex function such that
`f'_-(x) = φ_-(x) ≤ φ(x) ≤ φ_+(x) = f'_+(x)` for every `x`, where `φ_-` and `φ_+` are modeled by
`leftLimitProfile φ` and `rightLimitProfile φ`. Moreover, any other closed proper convex function
`g` with `g'_-(x) ≤ φ(x) ≤ g'_+(x)` for every `x` differs from `f` by an additive real constant.
-/


theorem oneDimensional_monotoneFunction_has_normalized_closedProperConvex_primitive_unique_up_to_constant
    (φ : ℝ → EReal) (a : ℝ) (hmono : Monotone φ)
    (ha_finite : φ a ≠ (⊤ : EReal) ∧ φ a ≠ (⊥ : EReal)) :
    let f : (Fin 1 → ℝ) → EReal := oneDimensionalIntervalIntegralPrimitive φ a
    ClosedConvexFunction f ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f ∧
      (∀ x : ℝ, f (scalarPoint x) = oneDimensionalIntervalIntegralPrimitiveValue φ a x) ∧
      f (scalarPoint a) = 0 ∧
      leftDerivativeExtension f = leftLimitProfile φ ∧
      rightDerivativeExtension f = rightLimitProfile φ ∧
      (∀ x : ℝ, leftLimitProfile φ x ≤ φ x ∧ φ x ≤ rightLimitProfile φ x) ∧
      (∀ g : (Fin 1 → ℝ) → EReal,
        ClosedConvexFunction g →
        ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) g →
        (∀ x : ℝ, leftDerivativeExtension g x ≤ φ x ∧ φ x ≤ rightDerivativeExtension g x) →
        ∃ α : ℝ, ∀ x : ℝ,
          g (scalarPoint x) = f (scalarPoint x) + ((α : ℝ) : EReal)) := by
  dsimp
  let f : (Fin 1 → ℝ) → EReal := oneDimensionalIntervalIntegralPrimitive φ a
  change
    ClosedConvexFunction f ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f ∧
      (∀ x : ℝ, f (scalarPoint x) = oneDimensionalIntervalIntegralPrimitiveValue φ a x) ∧
      f (scalarPoint a) = 0 ∧
      leftDerivativeExtension f = leftLimitProfile φ ∧
      rightDerivativeExtension f = rightLimitProfile φ ∧
      (∀ x : ℝ, leftLimitProfile φ x ≤ φ x ∧ φ x ≤ rightLimitProfile φ x) ∧
      (∀ g : (Fin 1 → ℝ) → EReal,
        ClosedConvexFunction g →
        ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) g →
        (∀ x : ℝ, leftDerivativeExtension g x ≤ φ x ∧ φ x ≤ rightDerivativeExtension g x) →
        ∃ α : ℝ, ∀ x : ℝ,
          g (scalarPoint x) = f (scalarPoint x) + ((α : ℝ) : EReal))
  have hScalarEval :
      ∀ x : ℝ, f (scalarPoint x) = oneDimensionalIntervalIntegralPrimitiveValue φ a x := by
    intro x
    -- The `Fin 1` wrapper around the scalar primitive is purely definitional.
    simpa [f] using helperForTheorem_5_24_4_scalarPoint_primitive_eval φ a x
  have hProfileOrder :
      ∀ x : ℝ, leftLimitProfile φ x ≤ φ x ∧ φ x ≤ rightLimitProfile φ x :=
    helperForTheorem_5_24_4_monotone_profile_between_its_one_sided_limits φ hmono
  -- Route correction: follow the textbook existence route. The order should be:
  -- define the interval-integral primitive, prove convexity and the derivative-band inequalities
  -- directly from the integral formulas, and only then identify the exact left/right limit
  -- profiles.
  have hPrimitive :
      ClosedConvexFunction f ∧
        ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f ∧
        f (scalarPoint a) = 0 ∧
        leftDerivativeExtension f = leftLimitProfile φ ∧
        rightDerivativeExtension f = rightLimitProfile φ := by
    -- TODO: once the upstream primitive package theorem exists, apply the direct integral proof
    -- package here and then read off the exact one-sided profiles.
    simpa [f] using
      helperForTheorem_5_24_4_intervalIntegralPrimitive_closedProper_normalized_derivativeProfiles
        φ a hmono ha_finite
  rcases hPrimitive with ⟨hclosed, hproper, hAtBase, hleft, hright⟩
  refine ⟨hclosed, hproper, hScalarEval, hAtBase, hleft, hright, hProfileOrder, ?_⟩
  -- TODO: once the primitive construction is available, uniqueness should follow by the textbook
  -- `h = f - g` argument on the common relative interior of the finite interval `J`.
  exact
    helperForTheorem_5_24_4_unique_up_to_constant_from_common_scalar_band
      φ f hclosed hproper hleft hright

/-- The scalar graph of the one-dimensional subdifferential, obtained by identifying both the
domain and codomain with `ℝ`. -/
def oneDimensionalSubdifferentialScalarGraph (f : (Fin 1 → ℝ) → EReal) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | dotProductEquiv ℝ (Fin 1) (scalarPoint p.2) ∈ ∂ f (scalarPoint p.1)}

/-- If a monotone profile never takes finite values, then every value is either `⊤` or `⊥`. -/
lemma helperForTheorem_5_24_5_allValues_top_or_bot_of_no_finiteWitness
    (φ : ℝ → EReal)
    (hNoFinite : ¬ ∃ x : ℝ, φ x ≠ (⊤ : EReal) ∧ φ x ≠ (⊥ : EReal)) :
    ∀ x : ℝ, φ x = (⊤ : EReal) ∨ φ x = (⊥ : EReal) := by
  intro x
  by_cases htop : φ x = (⊤ : EReal)
  · exact Or.inl htop
  · by_cases hbot : φ x = (⊥ : EReal)
    · exact Or.inr hbot
    · exfalso
      exact hNoFinite ⟨x, htop, hbot⟩

/-- A nonempty complete-curve band coming from a monotone profile with no finite values is a
single vertical line. -/
lemma helperForTheorem_5_24_5_band_eq_verticalLine_of_no_finiteWitness
    (Γ : Set (ℝ × ℝ)) (φ : ℝ → EReal) (hmono : Monotone φ)
    (hNoFinite : ¬ ∃ x : ℝ, φ x ≠ (⊤ : EReal) ∧ φ x ≠ (⊥ : EReal))
    (hΓnonempty : Γ.Nonempty)
    (hΓdef :
      Γ = {p : ℝ × ℝ |
        leftLimitProfile φ p.1 ≤ (p.2 : EReal) ∧
          (p.2 : EReal) ≤ rightLimitProfile φ p.1}) :
    ∃ a : ℝ, Γ = {p : ℝ × ℝ | p.1 = a} := by
  rcases hΓnonempty with ⟨p0, hp0Γ⟩
  have hTB := helperForTheorem_5_24_5_allValues_top_or_bot_of_no_finiteWitness φ hNoFinite
  have hp0Band :
      leftLimitProfile φ p0.1 ≤ (p0.2 : EReal) ∧
        (p0.2 : EReal) ≤ rightLimitProfile φ p0.1 := by
    simpa [hΓdef] using hp0Γ
  have hleftVal : ∀ z : ℝ, z < p0.1 → φ z = (⊥ : EReal) := by
    intro z hz
    rcases hTB z with htop | hbot
    · have htopLe : (⊤ : EReal) ≤ leftLimitProfile φ p0.1 := by
        simpa [htop] using (le_sSup ⟨z, hz, rfl⟩ :
          φ z ≤ leftLimitProfile φ p0.1)
      have : (⊤ : EReal) ≤ ((p0.2 : ℝ) : EReal) := le_trans htopLe hp0Band.1
      simp at this
    · exact hbot
  have hrightVal : ∀ z : ℝ, p0.1 < z → φ z = (⊤ : EReal) := by
    intro z hz
    rcases hTB z with htop | hbot
    · exact htop
    · have hrightLeBot : rightLimitProfile φ p0.1 ≤ (⊥ : EReal) := by
        simpa [hbot] using (sInf_le ⟨z, hz, rfl⟩ :
          rightLimitProfile φ p0.1 ≤ φ z)
      have : ((p0.2 : ℝ) : EReal) ≤ (⊥ : EReal) := le_trans hp0Band.2 hrightLeBot
      simp at this
  have hleftEq : leftLimitProfile φ p0.1 = (⊥ : EReal) := by
    apply le_antisymm
    · refine sSup_le ?_
      intro y hy
      rcases hy with ⟨z, hz, rfl⟩
      simp [hleftVal z hz]
    · exact bot_le
  have hrightEq : rightLimitProfile φ p0.1 = (⊤ : EReal) := by
    apply le_antisymm
    · exact le_top
    · refine le_sInf ?_
      intro y hy
      rcases hy with ⟨z, hz, rfl⟩
      simp [hrightVal z hz]
  refine ⟨p0.1, ?_⟩
  ext p
  constructor
  · intro hpΓ
    have hpBand :
        leftLimitProfile φ p.1 ≤ (p.2 : EReal) ∧
          (p.2 : EReal) ≤ rightLimitProfile φ p.1 := by
      simpa [hΓdef] using hpΓ
    by_contra hpNe
    rcases lt_or_gt_of_ne hpNe with hpLt | hpGt
    · let z : ℝ := (p.1 + p0.1) / 2
      have hpz : p.1 < z := by
        dsimp [z]
        linarith
      have hz0 : z < p0.1 := by
        dsimp [z]
        linarith
      have hrightLeBot : rightLimitProfile φ p.1 ≤ (⊥ : EReal) := by
        simpa [hleftVal z hz0] using (sInf_le ⟨z, hpz, rfl⟩ :
          rightLimitProfile φ p.1 ≤ φ z)
      have : ((p.2 : ℝ) : EReal) ≤ (⊥ : EReal) := le_trans hpBand.2 hrightLeBot
      simp at this
    · let z : ℝ := (p0.1 + p.1) / 2
      have h0z : p0.1 < z := by
        dsimp [z]
        linarith
      have hzp : z < p.1 := by
        dsimp [z]
        linarith
      have htopLe : (⊤ : EReal) ≤ leftLimitProfile φ p.1 := by
        simpa [hrightVal z h0z] using (le_sSup ⟨z, hzp, rfl⟩ :
          φ z ≤ leftLimitProfile φ p.1)
      have : (⊤ : EReal) ≤ ((p.2 : ℝ) : EReal) := le_trans htopLe hpBand.1
      simp at this
  · intro hp1
    rcases p with ⟨x, y⟩
    have hx : x = p0.1 := by simpa using hp1
    subst hx
    have hpBand :
        leftLimitProfile φ p0.1 ≤ (y : EReal) ∧
          (y : EReal) ≤ rightLimitProfile φ p0.1 := by
      simp [hleftEq, hrightEq]
    simpa [hΓdef]
      using hpBand

/-- The vertical line over `a` is the scalar subdifferential graph of the singleton indicator
function at `a`. -/
lemma helperForTheorem_5_24_5_verticalLine_is_subdifferentialScalarGraph_indicatorSingleton
    (a : ℝ) :
    ∃ f : (Fin 1 → ℝ) → EReal,
      ClosedConvexFunction f ∧
        ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f ∧
        oneDimensionalSubdifferentialScalarGraph f = {p : ℝ × ℝ | p.1 = a} := by
  let C : Set (Fin 1 → ℝ) := {scalarPoint a}
  refine ⟨indicatorFunction C, ?_, ?_, ?_⟩
  · have hclosedProper :=
      closedConvexFunction_indicator_neg (n := 1) (C := {-scalarPoint a})
        (by simp) (by simpa using isClosed_singleton) (by simpa using convex_singleton (-scalarPoint a))
    simpa [C, Set.neg_singleton] using hclosedProper.1
  · have hclosedProper :=
      closedConvexFunction_indicator_neg (n := 1) (C := {-scalarPoint a})
        (by simp) (by simpa using isClosed_singleton) (by simpa using convex_singleton (-scalarPoint a))
    simpa [C, Set.neg_singleton] using hclosedProper.2
  · ext p
    constructor
    · intro hp
      by_cases hp1 : p.1 = a
      · exact hp1
      · have hpNotMem : scalarPoint p.1 ∉ C := by
          intro hpMem
          have : p.1 = a := by
            have hEq0 := congrArg (fun v : Fin 1 → ℝ => v 0) hpMem
            simpa [C, scalarPoint] using hEq0
          exact hp1 this
        have hEmpty :
            subdifferentialAt (indicatorFunction C) (scalarPoint p.1) = ∅ :=
          subdifferential_indicatorFunction_eq_empty_of_not_mem (C := C) (by simp [C]) hpNotMem
        have hpSub :
            dotProductEquiv ℝ (Fin 1) (scalarPoint p.2) ∈
              subdifferentialAt (indicatorFunction C) (scalarPoint p.1) := by
          simpa [oneDimensionalSubdifferentialScalarGraph] using hp
        rw [hEmpty] at hpSub
        have hpEmpty :
            dotProductEquiv ℝ (Fin 1) (scalarPoint p.2) ∈
              (∅ : Set ((Fin 1 → ℝ) →ₗ[ℝ] ℝ)) := hpSub
        simpa using hpEmpty
    · intro hp1
      have hp1' : p.1 = a := by simpa using hp1
      have hxMem : scalarPoint p.1 ∈ C := by simp [C, hp1']
      have hpNormal :
          dotProductEquiv ℝ (Fin 1) (scalarPoint p.2) ∈ normalConeAt C (scalarPoint p.1) := by
        simp [C, hp1', normalConeAt, Set.mem_singleton_iff]
      have hpSub :
          dotProductEquiv ℝ (Fin 1) (scalarPoint p.2) ∈
            ∂ (indicatorFunction C) (scalarPoint p.1) := by
        rw [subdifferential_indicatorFunction_eq_normalConeAt_of_mem (C := C) hxMem]
        exact hpNormal
      simpa [oneDimensionalSubdifferentialScalarGraph] using hpSub

-- Proof sketch: for the forward direction, apply Theorem 5.24.3 to a suitable monotone
-- selection between the left and right derivative extensions of `f` to identify the scalar
-- subdifferential graph with a complete non-decreasing curve. For the reverse direction, unpack
-- `IsCompleteNondecreasingCurve Γ` to obtain a monotone profile `φ`, apply Theorem 5.24.4 to the
-- normalized primitive of `φ`, and then use Theorem 5.24.3 to recover `Γ` as its
-- subdifferential graph. If two closed proper convex functions have the same graph, Theorem
-- 5.24.4 applied to the common profile description shows that they differ by an additive real
-- constant.
/-- Theorem 5.24.5: the scalar graphs of the subdifferential mappings of closed proper convex
functions on `ℝ` are exactly the complete non-decreasing curves in `ℝ²`. Moreover, a closed
proper convex function with scalar subdifferential graph `Γ` is uniquely determined by `Γ` up to
an additive real constant. -/
theorem oneDimensional_subdifferentialGraphs_iff_completeNondecreasingCurves_unique_up_to_constant
    (Γ : Set (ℝ × ℝ)) :
    (IsCompleteNondecreasingCurve Γ ↔
      ∃ f : (Fin 1 → ℝ) → EReal,
        ClosedConvexFunction f ∧
          ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f ∧
          oneDimensionalSubdifferentialScalarGraph f = Γ) ∧
      ∀ f g : (Fin 1 → ℝ) → EReal,
        ClosedConvexFunction f →
        ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f →
        ClosedConvexFunction g →
        ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) g →
        oneDimensionalSubdifferentialScalarGraph f = Γ →
        oneDimensionalSubdifferentialScalarGraph g = Γ →
        ∃ α : ℝ, ∀ x : ℝ,
          g (scalarPoint x) = f (scalarPoint x) + ((α : ℝ) : EReal) := by
  constructor
  · constructor
    · intro hΓ
      rcases hΓ with ⟨φ, hmono, hΓnonempty, hΓdef⟩
      by_cases hfinite : ∃ a : ℝ, φ a ≠ (⊤ : EReal) ∧ φ a ≠ (⊥ : EReal)
      · rcases hfinite with ⟨a, haTop, haBot⟩
        let f : (Fin 1 → ℝ) → EReal := oneDimensionalIntervalIntegralPrimitive φ a
        have hPrimitive :
            ClosedConvexFunction f ∧
              ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f ∧
              (∀ x : ℝ, f (scalarPoint x) = oneDimensionalIntervalIntegralPrimitiveValue φ a x) ∧
              f (scalarPoint a) = 0 ∧
              leftDerivativeExtension f = leftLimitProfile φ ∧
              rightDerivativeExtension f = rightLimitProfile φ ∧
              (∀ x : ℝ, leftLimitProfile φ x ≤ φ x ∧ φ x ≤ rightLimitProfile φ x) ∧
              (∀ g : (Fin 1 → ℝ) → EReal,
                ClosedConvexFunction g →
                ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) g →
                (∀ x : ℝ, leftDerivativeExtension g x ≤ φ x ∧ φ x ≤ rightDerivativeExtension g x) →
                ∃ α : ℝ, ∀ x : ℝ,
                  g (scalarPoint x) = f (scalarPoint x) + ((α : ℝ) : EReal)) := by
          simpa [f] using
            oneDimensional_monotoneFunction_has_normalized_closedProperConvex_primitive_unique_up_to_constant
              φ a hmono ⟨haTop, haBot⟩
        rcases hPrimitive with
          ⟨hclosed, hproper, _hEval, _hAtBase, hleft, hright, _hProfileOrder, _huniq⟩
        refine ⟨f, hclosed, hproper, ?_⟩
        ext p
        have hFiber :
            {xStar : ℝ | dotProductEquiv ℝ (Fin 1) (scalarPoint xStar) ∈ ∂ f (scalarPoint p.1)} =
              {xStar : ℝ |
                leftLimitProfile φ p.1 ≤ ((xStar : ℝ) : EReal) ∧
                  (((xStar : ℝ) : EReal) ≤ rightLimitProfile φ p.1)} := by
          calc
            {xStar : ℝ | dotProductEquiv ℝ (Fin 1) (scalarPoint xStar) ∈ ∂ f (scalarPoint p.1)} =
                {xStar : ℝ |
                  leftDerivativeExtension f p.1 ≤ ((xStar : ℝ) : EReal) ∧
                    (((xStar : ℝ) : EReal) ≤ rightDerivativeExtension f p.1)} := by
                  simpa using
                    oneDimensional_subdifferential_preimage_eq_setOf_leftDerivativeExtension_le_and_le_rightDerivativeExtension
                      f hclosed hproper p.1
            _ = {xStar : ℝ |
                  leftLimitProfile φ p.1 ≤ ((xStar : ℝ) : EReal) ∧
                    (((xStar : ℝ) : EReal) ≤ rightLimitProfile φ p.1)} := by
                  simp [hleft, hright]
        simpa [oneDimensionalSubdifferentialScalarGraph, hΓdef] using
          congrArg (fun S : Set ℝ => p.2 ∈ S) hFiber
      · rcases
          helperForTheorem_5_24_5_band_eq_verticalLine_of_no_finiteWitness
            Γ φ hmono hfinite hΓnonempty hΓdef with
          ⟨a, hVertical⟩
        rcases
          helperForTheorem_5_24_5_verticalLine_is_subdifferentialScalarGraph_indicatorSingleton a with
          ⟨f, hclosed, hproper, hGraph⟩
        exact ⟨f, hclosed, hproper, hGraph.trans hVertical.symm⟩
    · rintro ⟨f, hclosed, hproper, hGraph⟩
      have hCurve :
          IsCompleteNondecreasingCurve (oneDimensionalSubdifferentialScalarGraph f) := by
        simpa [oneDimensionalSubdifferentialScalarGraph] using
          helperForTheorem_5_24_4_scalarSubdifferentialGraph_isCompleteNondecreasingCurve
            f hclosed hproper
      simpa [hGraph] using hCurve
  · intro f g hclosedF hproperF hclosedG hproperG hGraphF hGraphG
    have hCommonGraph :
        {p : ℝ × ℝ | dotProductEquiv ℝ (Fin 1) (scalarPoint p.2) ∈ ∂ g (scalarPoint p.1)} =
          {p : ℝ × ℝ | dotProductEquiv ℝ (Fin 1) (scalarPoint p.2) ∈ ∂ f (scalarPoint p.1)} := by
      simpa [oneDimensionalSubdifferentialScalarGraph] using hGraphG.trans hGraphF.symm
    exact
      oneDimensional_closedProperConvex_eq_up_to_constant_of_common_scalarSubdifferentialGraph
        f g hclosedF hproperF hclosedG hproperG hCommonGraph

-- Proof sketch: by Theorem 5.24.5, realize `Γ` as the scalar subdifferential graph of a closed
-- proper convex function `f`. Theorem 23.5 identifies the inverse subdifferential relation with
-- the subdifferential graph of the Fenchel conjugate `f*`, which is exactly the coordinate swap
-- of the graph of `f`. Applying Theorem 5.24.5 again to that swapped graph yields the claim.
/-- Swapping the coordinates of a complete non-decreasing curve again yields a complete
non-decreasing curve; in Lean this swapped set is `Prod.swap '' Γ`. -/
theorem isCompleteNondecreasingCurve_swap_image {Γ : Set (ℝ × ℝ)}
    (hΓ : IsCompleteNondecreasingCurve Γ) :
    IsCompleteNondecreasingCurve (Prod.swap '' Γ) := by
  have hRealization :
      ∃ f : (Fin 1 → ℝ) → EReal,
        ClosedConvexFunction f ∧
          ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f ∧
          oneDimensionalSubdifferentialScalarGraph f = Γ := by
    exact
      (oneDimensional_subdifferentialGraphs_iff_completeNondecreasingCurves_unique_up_to_constant
        Γ).1.1 hΓ
  rcases hRealization with ⟨f, hclosed, hproper, hGraph⟩
  have hSwapGraph :
      oneDimensionalSubdifferentialScalarGraph (fenchelConjugate 1 f) = Prod.swap '' Γ := by
    ext p
    constructor
    · intro hp
      have hpConj :
          dotProductEquiv ℝ (Fin 1) (scalarPoint p.2) ∈
            ∂ (fenchelConjugate 1 f) (scalarPoint p.1) := by
        simpa [oneDimensionalSubdifferentialScalarGraph] using hp
      have hpPrimal :
          dotProductEquiv ℝ (Fin 1) (scalarPoint p.1) ∈ ∂ f (scalarPoint p.2) := by
        simpa using
          (helperForTheorem_5_24_4_scalarSubgradient_mem_fenchelConjugate_iff
            f hclosed hproper).2 hpConj
      have hmemGraph : (p.2, p.1) ∈ oneDimensionalSubdifferentialScalarGraph f := by
        simpa [oneDimensionalSubdifferentialScalarGraph] using hpPrimal
      have hmemΓ : (p.2, p.1) ∈ Γ := by
        rw [← hGraph]
        exact hmemGraph
      exact ⟨(p.2, p.1), hmemΓ, by simp⟩
    · rintro ⟨q, hqΓ, hswapq⟩
      rcases q with ⟨x, xStar⟩
      simp at hswapq
      rcases hswapq with ⟨rfl, rfl⟩
      have hmemGraph :
          (x, xStar) ∈ oneDimensionalSubdifferentialScalarGraph f := by
        simpa [hGraph] using hqΓ
      have hPrimal :
          dotProductEquiv ℝ (Fin 1) (scalarPoint xStar) ∈ ∂ f (scalarPoint x) := by
        simpa [oneDimensionalSubdifferentialScalarGraph] using hmemGraph
      have hConj :
          dotProductEquiv ℝ (Fin 1) (scalarPoint x) ∈
            ∂ (fenchelConjugate 1 f) (scalarPoint xStar) := by
        simpa using
          (helperForTheorem_5_24_4_scalarSubgradient_mem_fenchelConjugate_iff
            f hclosed hproper).1 hPrimal
      simpa [oneDimensionalSubdifferentialScalarGraph] using hConj
  exact
    (oneDimensional_subdifferentialGraphs_iff_completeNondecreasingCurves_unique_up_to_constant
      (Prod.swap '' Γ)).1.2
      ⟨fenchelConjugate 1 f,
        ⟨(fenchelConjugate_closedConvex (n := 1) (f := f)).2,
          (fenchelConjugate_closedConvex (n := 1) (f := f)).1⟩,
        proper_fenchelConjugate_of_proper (n := 1) (f := f) hproper,
        hSwapGraph⟩

/-- The finite branch `|x| - 2 * sqrt (1 - x)` from the standard one-dimensional convex example.
-/
noncomputable def absMinusTwoSqrtFiniteBranch (x : ℝ) : ℝ :=
  |x| - 2 * Real.sqrt (1 - x)

/-- The one-dimensional convex example that equals `|x| - 2 * sqrt (1 - x)` on `[-3, 1]` and
`+∞` outside that interval, viewed as a function on `Fin 1 → ℝ`. -/
noncomputable def absMinusTwoSqrtExampleFunction (x : Fin 1 → ℝ) : EReal :=
  if -3 ≤ x 0 ∧ x 0 ≤ 1 then
    (absMinusTwoSqrtFiniteBranch (x 0) : EReal)
  else
    (⊤ : EReal)

/-- The piecewise right-derivative profile for `absMinusTwoSqrtExampleFunction`. -/
noncomputable def absMinusTwoSqrtExampleRightDerivative (x : ℝ) : EReal :=
  if 1 ≤ x then
    (⊤ : EReal)
  else if 0 ≤ x then
    ((1 + (Real.sqrt (1 - x))⁻¹ : ℝ) : EReal)
  else if -3 ≤ x then
    ((-1 + (Real.sqrt (1 - x))⁻¹ : ℝ) : EReal)
  else
    (⊥ : EReal)

/-- The piecewise left-derivative profile for `absMinusTwoSqrtExampleFunction`. -/
noncomputable def absMinusTwoSqrtExampleLeftDerivative (x : ℝ) : EReal :=
  if 1 ≤ x then
    (⊤ : EReal)
  else if 0 < x then
    ((1 + (Real.sqrt (1 - x))⁻¹ : ℝ) : EReal)
  else if -3 < x then
    ((-1 + (Real.sqrt (1 - x))⁻¹ : ℝ) : EReal)
  else
    (⊥ : EReal)

/-- The piecewise scalar subdifferential profile for `absMinusTwoSqrtExampleFunction`. -/
noncomputable def absMinusTwoSqrtExampleSubdifferential (x : ℝ) : Set ℝ :=
  if 1 ≤ x then
    ∅
  else if 0 < x then
    {1 + (Real.sqrt (1 - x))⁻¹}
  else if x = 0 then
    Set.Icc 0 2
  else if -3 < x then
    {-1 + (Real.sqrt (1 - x))⁻¹}
  else if x = -3 then
    Set.Iic (-(1 / 2 : ℝ))
  else
    ∅

/-- The Example 5.24.1 function is a closed proper convex function on `ℝ`. -/
lemma helperForExample_5_24_1_closedProperConvex :
    ClosedConvexFunction absMinusTwoSqrtExampleFunction ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) absMinusTwoSqrtExampleFunction := by
  classical
  let C : Set (Fin 1 → ℝ) := {x | -3 ≤ x 0 ∧ x 0 ≤ 1}
  have hCconv : Convex ℝ C := by
    simpa [C, Set.preimage, LinearMap.proj_apply] using
      (convex_Icc (-3 : ℝ) (1 : ℝ)).linear_preimage (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)
  have hCclosed : IsClosed C := by
    simpa [C, Set.preimage] using
      (isClosed_Icc.preimage (continuous_apply 0))
  have hCne : C.Nonempty := by
    refine ⟨scalarPoint 0, ?_⟩
    simp [C, scalarPoint]
  have habsConv : ConvexOn ℝ (Set.Icc (-3 : ℝ) 1) (fun t : ℝ => |t|) := by
    simpa [Real.norm_eq_abs] using
      (convexOn_univ_norm : ConvexOn ℝ (Set.univ : Set ℝ) (fun t : ℝ => ‖t‖)).subset
        (by intro x hx; simp) (convex_Icc (-3 : ℝ) 1)
  have hsqrtConv :
      ConvexOn ℝ (Set.Icc (-3 : ℝ) 1) (fun t : ℝ => -2 * Real.sqrt (1 - t)) := by
    have hbase :
        ConvexOn ℝ (Set.Iic (1 : ℝ)) (fun t : ℝ => -Real.sqrt (1 - t)) := by
      have hconv0 :
          ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun t : ℝ => -Real.sqrt t) :=
        (neg_convexOn_iff).2 (Real.strictConcaveOn_sqrt.concaveOn)
      have h :
          ConvexOn ℝ (Set.Iic (1 : ℝ))
            ((fun t : ℝ => -Real.sqrt t) ∘ (AffineMap.lineMap (1 : ℝ) (0 : ℝ))) := by
        simpa [Set.preimage, Set.Ici, Set.Iic, AffineMap.lineMap_apply_ring] using
          (ConvexOn.comp_affineMap (g := AffineMap.lineMap (1 : ℝ) (0 : ℝ))
            (s := Set.Ici (0 : ℝ)) hconv0)
      refine h.congr ?_
      intro t ht
      simp [Function.comp, AffineMap.lineMap_apply_ring]
    have hscaled := hbase.smul (c := (2 : ℝ)) (by norm_num : 0 ≤ (2 : ℝ))
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      hscaled.subset (by intro x hx; exact hx.2) (convex_Icc (-3 : ℝ) 1)
  have hbranchConv :
      ConvexOn ℝ C (fun x : Fin 1 → ℝ => absMinusTwoSqrtFiniteBranch (x 0)) := by
    have hscalar :
        ConvexOn ℝ (Set.Icc (-3 : ℝ) 1) absMinusTwoSqrtFiniteBranch := by
      simpa [absMinusTwoSqrtFiniteBranch, sub_eq_add_neg] using
        habsConv.add hsqrtConv
    simpa [C] using convexOn_comp_proj (s := Set.Icc (-3 : ℝ) 1) (f := absMinusTwoSqrtFiniteBranch) hscalar
  have hconv :
      ConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) absMinusTwoSqrtExampleFunction := by
    have hconvG :=
      convexFunctionOn_univ_if_top
        (C := C) (g := fun x : Fin 1 → ℝ => absMinusTwoSqrtFiniteBranch (x 0)) hbranchConv
    convert hconvG using 1
    funext x
    by_cases hx : x ∈ C
    · have hx' : -3 ≤ x 0 ∧ x 0 ≤ 1 := by simpa [C] using hx
      simp [absMinusTwoSqrtExampleFunction, hx, hx', C]
    · have hx' : ¬ (-3 ≤ x 0 ∧ x 0 ≤ 1) := by simpa [C] using hx
      simp [absMinusTwoSqrtExampleFunction, hx, hx', C]
  have hnonemptyEpi : Set.Nonempty (epigraph (Set.univ : Set (Fin 1 → ℝ)) absMinusTwoSqrtExampleFunction) := by
    refine ⟨(scalarPoint 0, 0), ?_⟩
    constructor
    · exact Set.mem_univ (scalarPoint 0)
    · norm_num [absMinusTwoSqrtExampleFunction, absMinusTwoSqrtFiniteBranch, scalarPoint]
  have hneBot :
      ∀ x ∈ (Set.univ : Set (Fin 1 → ℝ)), absMinusTwoSqrtExampleFunction x ≠ (⊥ : EReal) := by
    intro x hx
    by_cases hxC : -3 ≤ x 0 ∧ x 0 ≤ 1
    · simp [absMinusTwoSqrtExampleFunction, hxC]
    · simp [absMinusTwoSqrtExampleFunction, hxC]
  have hproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) absMinusTwoSqrtExampleFunction :=
    ⟨hconv, hnonemptyEpi, hneBot⟩
  have hcontBranch : Continuous (fun x : Fin 1 → ℝ => absMinusTwoSqrtFiniteBranch (x 0)) := by
    have habsCont : Continuous (fun t : ℝ => |t|) := by
      simpa [Real.norm_eq_abs] using (continuous_norm : Continuous fun t : ℝ => ‖t‖)
    have hsqrtCont : Continuous (fun t : ℝ => -2 * Real.sqrt (1 - t)) := by
      exact continuous_const.mul (Real.continuous_sqrt.comp (continuous_const.sub continuous_id))
    have hproj : Continuous (fun x : Fin 1 → ℝ => x 0) := continuous_apply 0
    simpa [absMinusTwoSqrtFiniteBranch, sub_eq_add_neg] using
      (habsCont.add hsqrtCont).comp hproj
  have hclosedSublevel :
      ∀ α : ℝ, IsClosed {x : Fin 1 → ℝ | x ∈ C ∧ absMinusTwoSqrtFiniteBranch (x 0) ≤ α} := by
    intro α
    have hpre :
        IsClosed ((fun x : Fin 1 → ℝ => absMinusTwoSqrtFiniteBranch (x 0)) ⁻¹' Set.Iic α) := by
      exact isClosed_Iic.preimage hcontBranch
    simpa [Set.preimage] using hCclosed.inter hpre
  have hlsc : LowerSemicontinuous absMinusTwoSqrtExampleFunction := by
    rw [lowerSemicontinuous_iff_closed_sublevel]
    intro α
    have hSet :
        {x : Fin 1 → ℝ | absMinusTwoSqrtExampleFunction x ≤ (α : EReal)} =
          {x : Fin 1 → ℝ | x ∈ C ∧ absMinusTwoSqrtFiniteBranch (x 0) ≤ α} := by
      ext x
      by_cases hxC : x ∈ C
      · simp [absMinusTwoSqrtExampleFunction, C, hxC, hxC.1, hxC.2]
      · have hxC' : ¬ (-3 ≤ x 0 ∧ x 0 ≤ 1) := by simpa [C] using hxC
        simp [absMinusTwoSqrtExampleFunction, C, hxC, hxC']
    simpa [hSet] using hclosedSublevel α
  exact ⟨(properConvexFunction_closed_iff_lowerSemicontinuous hproper).2 hlsc, hproper⟩

-- Proof sketch: verify directly that the function is finite exactly on `[-3, 1]`, where it is
-- the sum of the convex functions `x ↦ |x|` and `x ↦ -2 * sqrt (1 - x)`. Then compute the two
-- one-sided derivatives on each interval, identify the endpoint values, and apply Theorem 5.24.2
-- to convert the derivative formulas into the stated subdifferential description.
/-- Example 5.24.1: the function
`f(x) = |x| - 2 * sqrt (1 - x)` on `[-3, 1]` and `f(x) = +∞` otherwise is a closed proper convex
function on `ℝ`; its right and left derivative extensions are given by the stated piecewise
formulas, and its scalar subdifferential is `∅` for `x ≥ 1` and `x < -3`, `{1 + (1 - x)^(-1/2)}`
for `0 < x < 1`, `[0, 2]` at `x = 0`, `{-1 + (1 - x)^(-1/2)}` for `-3 < x < 0`, and
`(-∞, -1 / 2]` at `x = -3`. -/
lemma helperForExample_5_24_1_subdifferential_of_derivative_profiles
    (hclosed : ClosedConvexFunction absMinusTwoSqrtExampleFunction)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) absMinusTwoSqrtExampleFunction)
    (hRight : ∀ x : ℝ,
      rightDerivativeExtension absMinusTwoSqrtExampleFunction x =
        absMinusTwoSqrtExampleRightDerivative x)
    (hLeft : ∀ x : ℝ,
      leftDerivativeExtension absMinusTwoSqrtExampleFunction x =
        absMinusTwoSqrtExampleLeftDerivative x) :
    ∀ x : ℝ,
      {xStar : ℝ |
          dotProductEquiv ℝ (Fin 1) (scalarPoint xStar) ∈
            ∂ absMinusTwoSqrtExampleFunction (scalarPoint x)} =
        absMinusTwoSqrtExampleSubdifferential x := by
  intro x
  have hFiber :
      {xStar : ℝ |
          dotProductEquiv ℝ (Fin 1) (scalarPoint xStar) ∈
            ∂ absMinusTwoSqrtExampleFunction (scalarPoint x)} =
        {xStar : ℝ |
          absMinusTwoSqrtExampleLeftDerivative x ≤ ((xStar : ℝ) : EReal) ∧
            (((xStar : ℝ) : EReal) ≤ absMinusTwoSqrtExampleRightDerivative x)} := by
    calc
      {xStar : ℝ |
          dotProductEquiv ℝ (Fin 1) (scalarPoint xStar) ∈
            ∂ absMinusTwoSqrtExampleFunction (scalarPoint x)} =
          {xStar : ℝ |
            leftDerivativeExtension absMinusTwoSqrtExampleFunction x ≤ ((xStar : ℝ) : EReal) ∧
              (((xStar : ℝ) : EReal) ≤ rightDerivativeExtension absMinusTwoSqrtExampleFunction x)} := by
            simpa using
              oneDimensional_subdifferential_preimage_eq_setOf_leftDerivativeExtension_le_and_le_rightDerivativeExtension
                absMinusTwoSqrtExampleFunction hclosed hproper x
      _ = {xStar : ℝ |
            absMinusTwoSqrtExampleLeftDerivative x ≤ ((xStar : ℝ) : EReal) ∧
              (((xStar : ℝ) : EReal) ≤ absMinusTwoSqrtExampleRightDerivative x)} := by
            simp [hLeft x, hRight x]
  rw [hFiber]
  ext xStar
  rcases le_or_gt 1 x with hx1 | hx1
  · simp [absMinusTwoSqrtExampleSubdifferential, absMinusTwoSqrtExampleLeftDerivative,
      absMinusTwoSqrtExampleRightDerivative, hx1]
  · rcases lt_trichotomy x 0 with hx0 | rfl | hx0
    · by_cases hxm3 : -3 < x
      · have hx1nle : ¬ 1 ≤ x := not_le.mpr hx1
        have hx0nlt : ¬ 0 < x := not_lt.mpr (le_of_lt hx0)
        have hx0nle : ¬ 0 ≤ x := not_le.mpr hx0
        have hxm3le : -3 ≤ x := le_of_lt hxm3
        have hxne0 : x ≠ 0 := ne_of_lt hx0
        constructor
        · intro hxMem
          have hLower :
              (((-1 + (Real.sqrt (1 - x))⁻¹ : ℝ) : EReal) ≤ ((xStar : ℝ) : EReal)) := by
            simpa [absMinusTwoSqrtExampleLeftDerivative, absMinusTwoSqrtExampleRightDerivative,
              hx1nle, hx0nlt, hx0nle, hxm3, hxm3le] using hxMem.1
          have hUpper :
              (((xStar : ℝ) : EReal) ≤ ((-1 + (Real.sqrt (1 - x))⁻¹ : ℝ) : EReal)) := by
            simpa [absMinusTwoSqrtExampleLeftDerivative, absMinusTwoSqrtExampleRightDerivative,
              hx1nle, hx0nlt, hx0nle, hxm3, hxm3le] using hxMem.2
          have hLower' : (-1 + (Real.sqrt (1 - x))⁻¹ : ℝ) ≤ xStar := by
            exact_mod_cast hLower
          have hUpper' : xStar ≤ (-1 + (Real.sqrt (1 - x))⁻¹ : ℝ) := by
            exact_mod_cast hUpper
          have hxStarEq : xStar = (-1 + (Real.sqrt (1 - x))⁻¹ : ℝ) :=
            le_antisymm hUpper' hLower'
          simpa [absMinusTwoSqrtExampleSubdifferential, hx1nle, hx0nlt, hx0nle, hxm3, hxm3le,
            hxne0, hxStarEq]
        · intro hxMem
          have hxStarEq : xStar = (-1 + (Real.sqrt (1 - x))⁻¹ : ℝ) := by
            simpa [absMinusTwoSqrtExampleSubdifferential, hx1nle, hx0nlt, hx0nle, hxm3, hxm3le,
              hxne0] using hxMem
          simpa [absMinusTwoSqrtExampleLeftDerivative, absMinusTwoSqrtExampleRightDerivative,
            hx1nle, hx0nlt, hx0nle, hxm3, hxm3le] using
              (show (((-1 + (Real.sqrt (1 - x))⁻¹ : ℝ) : EReal) ≤ ((xStar : ℝ) : EReal)) ∧
                  (((xStar : ℝ) : EReal) ≤ ((-1 + (Real.sqrt (1 - x))⁻¹ : ℝ) : EReal)) from
                ⟨by
                    exact_mod_cast (le_of_eq hxStarEq.symm),
                  by
                    exact_mod_cast (le_of_eq hxStarEq)⟩)
      · have hxle : x ≤ -3 := le_of_not_gt hxm3
        by_cases hxeq : x = -3
        · subst hxeq
          norm_num [absMinusTwoSqrtExampleSubdifferential, absMinusTwoSqrtExampleLeftDerivative,
            absMinusTwoSqrtExampleRightDerivative]
          constructor <;> intro hxMem <;> exact_mod_cast hxMem
        · have hxm3lt : x < -3 := lt_of_le_of_ne hxle hxeq
          have hx1nle : ¬ 1 ≤ x := not_le.mpr hx1
          have hx0nlt : ¬ 0 < x := not_lt.mpr (le_of_lt hx0)
          have hx0nle : ¬ 0 ≤ x := not_le.mpr hx0
          have hxm3nle : ¬ -3 ≤ x := not_le.mpr hxm3lt
          have hxne0 : x ≠ 0 := ne_of_lt hx0
          constructor
          · intro hxMem
            have hBot : (((xStar : ℝ) : EReal) ≤ (⊥ : EReal)) := by
              simpa [absMinusTwoSqrtExampleLeftDerivative, absMinusTwoSqrtExampleRightDerivative,
                hx1nle, hx0nlt, hx0nle, hxm3, hxm3nle] using hxMem.2
            have : False := (not_le_of_gt (EReal.bot_lt_coe xStar)) hBot
            simpa [absMinusTwoSqrtExampleSubdifferential, hx1nle, hx0nlt, hx0nle, hxm3, hxne0,
              hxeq]
              using this
          · intro hxMem
            simpa [absMinusTwoSqrtExampleSubdifferential, absMinusTwoSqrtExampleLeftDerivative,
              absMinusTwoSqrtExampleRightDerivative, hx1nle, hx0nlt, hx0nle, hxm3, hxm3nle, hxne0,
              hxeq]
              using hxMem
    · norm_num [absMinusTwoSqrtExampleSubdifferential, absMinusTwoSqrtExampleLeftDerivative,
        absMinusTwoSqrtExampleRightDerivative]
    · have hxnonneg : 0 ≤ x := le_of_lt hx0
      have hxne0 : x ≠ 0 := ne_of_gt hx0
      have hx1nle : ¬ 1 ≤ x := not_le.mpr hx1
      constructor
      · intro hxMem
        have hLower :
            (((1 + (Real.sqrt (1 - x))⁻¹ : ℝ) : EReal) ≤ ((xStar : ℝ) : EReal)) := by
          simpa [absMinusTwoSqrtExampleLeftDerivative, absMinusTwoSqrtExampleRightDerivative,
            hx1nle, hx0, hxnonneg] using hxMem.1
        have hUpper :
            (((xStar : ℝ) : EReal) ≤ ((1 + (Real.sqrt (1 - x))⁻¹ : ℝ) : EReal)) := by
          simpa [absMinusTwoSqrtExampleLeftDerivative, absMinusTwoSqrtExampleRightDerivative,
            hx1nle, hx0, hxnonneg] using hxMem.2
        have hLower' : (1 + (Real.sqrt (1 - x))⁻¹ : ℝ) ≤ xStar := by
          exact_mod_cast hLower
        have hUpper' : xStar ≤ (1 + (Real.sqrt (1 - x))⁻¹ : ℝ) := by
          exact_mod_cast hUpper
        have hxStarEq : xStar = (1 + (Real.sqrt (1 - x))⁻¹ : ℝ) := le_antisymm hUpper' hLower'
        simpa [absMinusTwoSqrtExampleSubdifferential, hx1nle, hx0, hxnonneg, hxne0, hxStarEq]
      · intro hxMem
        have hxStarEq : xStar = (1 + (Real.sqrt (1 - x))⁻¹ : ℝ) := by
          simpa [absMinusTwoSqrtExampleSubdifferential, hx1nle, hx0, hxnonneg, hxne0] using hxMem
        simpa [absMinusTwoSqrtExampleLeftDerivative, absMinusTwoSqrtExampleRightDerivative,
          hx1nle, hx0, hxnonneg] using
            (show (((1 + (Real.sqrt (1 - x))⁻¹ : ℝ) : EReal) ≤ ((xStar : ℝ) : EReal)) ∧
                (((xStar : ℝ) : EReal) ≤ ((1 + (Real.sqrt (1 - x))⁻¹ : ℝ) : EReal)) from
              ⟨by
                  exact_mod_cast (le_of_eq hxStarEq.symm),
                by
                  exact_mod_cast (le_of_eq hxStarEq)⟩)

lemma helperForExample_5_24_1_rightDerivative_on_Ioo_zero_one
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    rightDerivativeExtension absMinusTwoSqrtExampleFunction x =
      ((1 + (Real.sqrt (1 - x))⁻¹ : ℝ) : EReal) := by
  rcases helperForExample_5_24_1_closedProperConvex with ⟨_hclosed, hproper⟩
  have hDom :
      ∀ u ∈ Set.Ioo (0 : ℝ) 1, u ∈ scalarEffectiveDomain absMinusTwoSqrtExampleFunction := by
    intro u hu
    rw [scalarEffectiveDomain, effectiveDomain_eq]
    constructor
    · simp
    · have huC : -3 ≤ u ∧ u ≤ 1 := by
        constructor
        · nlinarith [hu.1]
        · exact le_of_lt hu.2
      simp [absMinusTwoSqrtExampleFunction, scalarPoint, huC]
  have hDeriv :
      derivWithin (fun v : ℝ => (absMinusTwoSqrtExampleFunction (scalarPoint v)).toReal)
        (Set.Ioi x) x =
        (1 + (Real.sqrt (1 - x))⁻¹ : ℝ) := by
    have hSmooth :
        HasDerivAt (fun t : ℝ => t - 2 * Real.sqrt (1 - t))
          (1 + (Real.sqrt (1 - x))⁻¹) x := by
      have h_id : HasDerivAt (fun t : ℝ => t) 1 x := by
        simpa using hasDerivAt_id x
      have h_inner : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
        simpa using (HasDerivAt.const_sub (1 : ℝ) (hasDerivAt_id x))
      have h_sqrt :
          HasDerivAt (fun t : ℝ => Real.sqrt (1 - t))
            ((-1) / (2 * Real.sqrt (1 - x))) x := by
        simpa using (HasDerivAt.sqrt h_inner (sub_ne_zero.mpr hx.2.ne'))
      have h_two_sqrt :
          HasDerivAt (fun t : ℝ => 2 * Real.sqrt (1 - t))
            (2 * ((-1) / (2 * Real.sqrt (1 - x)))) x := by
        simpa [two_mul] using (HasDerivAt.const_mul (2 : ℝ) h_sqrt)
      have h_sub := h_id.sub h_two_sqrt
      convert h_sub using 1
      ring
    have hSmall : Set.Ioo x 1 ∈ nhdsWithin x (Set.Ioi x) := by
      have hIoi : Set.Ioi x ∈ nhdsWithin x (Set.Ioi x) := self_mem_nhdsWithin
      have hIio : Set.Iio (1 : ℝ) ∈ nhdsWithin x (Set.Ioi x) :=
        nhdsWithin_le_nhds (IsOpen.mem_nhds isOpen_Iio hx.2)
      have hInter : (Set.Ioi x ∩ Set.Iio (1 : ℝ)) ∈ nhdsWithin x (Set.Ioi x) :=
        Filter.inter_mem hIoi hIio
      have hEqSet : Set.Ioo x 1 = Set.Ioi x ∩ Set.Iio (1 : ℝ) := by
        ext y
        simp [Set.Ioo, Set.Ioi, Set.Iio]
      rw [hEqSet]
      exact hInter
    have hEventually :
        (fun v : ℝ => (absMinusTwoSqrtExampleFunction (scalarPoint v)).toReal) =ᶠ[
          nhdsWithin x (Set.Ioi x)] fun t : ℝ => t - 2 * Real.sqrt (1 - t) := by
      filter_upwards [hSmall] with v hv
      have hv' : v ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_trans hx.1 hv.1, hv.2⟩
      have hvC : -3 ≤ v ∧ v ≤ 1 := by
        constructor
        · nlinarith [hv'.1]
        · exact le_of_lt hv'.2
      have hVal :
          absMinusTwoSqrtExampleFunction (scalarPoint v) =
            (absMinusTwoSqrtFiniteBranch v : EReal) := by
        simp [absMinusTwoSqrtExampleFunction, scalarPoint, hvC]
      have hToReal :
          (absMinusTwoSqrtExampleFunction (scalarPoint v)).toReal =
            absMinusTwoSqrtFiniteBranch v := by
        rw [hVal]
        simp
      simpa [absMinusTwoSqrtFiniteBranch, abs_of_pos hv'.1, sub_eq_add_neg] using hToReal
    have hxEq :
        (fun v : ℝ => (absMinusTwoSqrtExampleFunction (scalarPoint v)).toReal) x =
          (fun t : ℝ => t - 2 * Real.sqrt (1 - t)) x := by
      have hxC : -3 ≤ x ∧ x ≤ 1 := by
        constructor
        · nlinarith [hx.1]
        · exact le_of_lt hx.2
      have hVal :
          absMinusTwoSqrtExampleFunction (scalarPoint x) =
            (absMinusTwoSqrtFiniteBranch x : EReal) := by
        simp [absMinusTwoSqrtExampleFunction, scalarPoint, hxC]
      have hToReal :
          (absMinusTwoSqrtExampleFunction (scalarPoint x)).toReal =
            absMinusTwoSqrtFiniteBranch x := by
        rw [hVal]
        simp
      simpa [absMinusTwoSqrtFiniteBranch, abs_of_pos hx.1, sub_eq_add_neg] using hToReal
    exact
      (hSmooth.hasDerivWithinAt.congr_of_eventuallyEq hEventually hxEq).derivWithin
        (uniqueDiffWithinAt_Ioi x)
  have hBridge :=
    helperForTheorem_5_24_4_derivWithin_scalarToReal_eq_rightDerivativeExtension_toReal
      absMinusTwoSqrtExampleFunction hproper hDom hx
  have hxInterior : x ∈ interior (scalarEffectiveDomain absMinusTwoSqrtExampleFunction) := by
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo hx) (by
      intro u hu
      exact hDom u hu)
  have hRightFinite :=
    helperForTheorem_5_24_1_scalarInterior_finiteDirectionalDerivatives
      absMinusTwoSqrtExampleFunction hproper hxInterior
  have hxNot :
      ¬ IsLeftOfScalarEffectiveDomain absMinusTwoSqrtExampleFunction x ∧
        ¬ IsRightOfScalarEffectiveDomain absMinusTwoSqrtExampleFunction x :=
    helperForTheorem_5_24_1_not_left_not_right_of_mem_scalarEffectiveDomain
      absMinusTwoSqrtExampleFunction (hDom x hx)
  have hFiniteTop :
      rightDerivativeExtension absMinusTwoSqrtExampleFunction x ≠ (⊤ : EReal) := by
    simpa [rightDerivativeExtension, hxNot.2, hxNot.1] using hRightFinite.1
  have hFiniteBot :
      rightDerivativeExtension absMinusTwoSqrtExampleFunction x ≠ (⊥ : EReal) := by
    simpa [rightDerivativeExtension, hxNot.2, hxNot.1] using hRightFinite.2.1
  calc
    rightDerivativeExtension absMinusTwoSqrtExampleFunction x =
        (((rightDerivativeExtension absMinusTwoSqrtExampleFunction x).toReal : ℝ) : EReal) := by
          symm
          exact EReal.coe_toReal hFiniteTop hFiniteBot
    _ = ((1 + (Real.sqrt (1 - x))⁻¹ : ℝ) : EReal) := by
          exact_mod_cast (hBridge.symm.trans hDeriv)

lemma helperForExample_5_24_1_rightDerivative_on_Ioo_negThree_zero
    {x : ℝ} (hx : x ∈ Set.Ioo (-3 : ℝ) 0) :
    rightDerivativeExtension absMinusTwoSqrtExampleFunction x =
      ((-1 + (Real.sqrt (1 - x))⁻¹ : ℝ) : EReal) := by
  rcases helperForExample_5_24_1_closedProperConvex with ⟨_hclosed, hproper⟩
  let G : (Fin 1 → ℝ) → EReal := fun y =>
    absMinusTwoSqrtExampleFunction (y - scalarPoint 3)
  have hproperG :
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) G := by
    simpa [G] using
      (properConvexFunctionOn_translate (n := 1) (a := scalarPoint 3) hproper)
  let u : ℝ := x + 3
  have hu : u ∈ Set.Ioo (0 : ℝ) 3 := by
    dsimp [u]
    constructor
    · linarith [hx.1]
    · linarith [hx.2]
  have hDomG :
      ∀ v ∈ Set.Ioo (0 : ℝ) 3, v ∈ scalarEffectiveDomain G := by
    intro v hv
    rw [scalarEffectiveDomain, effectiveDomain_eq]
    constructor
    · simp
    · have hv0 : 0 ≤ v := le_of_lt hv.1
      have hv4 : v ≤ 1 + 3 := by linarith [hv.2]
      simpa [G, absMinusTwoSqrtExampleFunction, scalarPoint, hv0, hv4] using
        (EReal.coe_lt_top (absMinusTwoSqrtFiniteBranch (v - 3)))
  have hDerivG :
      derivWithin (fun v : ℝ => (G (scalarPoint v)).toReal) (Set.Ioi u) u =
        (-1 + (Real.sqrt (4 - u))⁻¹ : ℝ) := by
    have hSmooth :
        HasDerivAt (fun t : ℝ => 3 - t - 2 * Real.sqrt (4 - t))
          (-1 + (Real.sqrt (4 - u))⁻¹) u := by
      have h_linear : HasDerivAt (fun t : ℝ => 3 - t) (-1) u := by
        simpa using ((hasDerivAt_const u 3).sub (hasDerivAt_id u))
      have h_inner : HasDerivAt (fun t : ℝ => 4 - t) (-1) u := by
        simpa using (HasDerivAt.const_sub (4 : ℝ) (hasDerivAt_id u))
      have h_sqrt :
          HasDerivAt (fun t : ℝ => Real.sqrt (4 - t))
            ((-1) / (2 * Real.sqrt (4 - u))) u := by
        have hne : 4 - u ≠ 0 := by
          dsimp [u]
          intro hzero
          linarith [hx.2, hzero]
        simpa using (HasDerivAt.sqrt h_inner hne)
      have h_two_sqrt :
          HasDerivAt (fun t : ℝ => 2 * Real.sqrt (4 - t))
            (2 * ((-1) / (2 * Real.sqrt (4 - u)))) u := by
        simpa [two_mul] using (HasDerivAt.const_mul (2 : ℝ) h_sqrt)
      have h_sub := h_linear.sub h_two_sqrt
      convert h_sub using 1
      ring
    have hSmall : Set.Ioo u 3 ∈ nhdsWithin u (Set.Ioi u) := by
      have hIoi : Set.Ioi u ∈ nhdsWithin u (Set.Ioi u) := self_mem_nhdsWithin
      have hIio : Set.Iio (3 : ℝ) ∈ nhdsWithin u (Set.Ioi u) :=
        nhdsWithin_le_nhds (IsOpen.mem_nhds isOpen_Iio hu.2)
      have hInter : (Set.Ioi u ∩ Set.Iio (3 : ℝ)) ∈ nhdsWithin u (Set.Ioi u) :=
        Filter.inter_mem hIoi hIio
      have hEqSet : Set.Ioo u 3 = Set.Ioi u ∩ Set.Iio (3 : ℝ) := by
        ext y
        simp [Set.Ioo, Set.Ioi, Set.Iio]
      rw [hEqSet]
      exact hInter
    have hEventually :
        (fun v : ℝ => (G (scalarPoint v)).toReal) =ᶠ[nhdsWithin u (Set.Ioi u)]
          fun t : ℝ => 3 - t - 2 * Real.sqrt (4 - t) := by
      filter_upwards [hSmall] with v hv
      have hv' : v ∈ Set.Ioo (0 : ℝ) 3 := ⟨lt_trans hu.1 hv.1, hv.2⟩
      have hv0 : 0 ≤ v := le_of_lt hv'.1
      have hv4 : v ≤ 1 + 3 := by linarith [hv'.2]
      have hVal :
          G (scalarPoint v) = (absMinusTwoSqrtFiniteBranch (v - 3) : EReal) := by
        simp [G, absMinusTwoSqrtExampleFunction, scalarPoint, hv0, hv4]
      have hToReal :
          (G (scalarPoint v)).toReal = absMinusTwoSqrtFiniteBranch (v - 3) := by
        rw [hVal]
        simp
      have hvNeg : v - 3 < 0 := sub_neg.mpr hv.2
      calc
        (G (scalarPoint v)).toReal = absMinusTwoSqrtFiniteBranch (v - 3) := hToReal
        _ = 3 - v - 2 * Real.sqrt (4 - v) := by
          have habs : |v - 3| = -(v - 3) := abs_of_neg hvNeg
          rw [absMinusTwoSqrtFiniteBranch, habs]
          ring_nf
    have huEq :
        (fun v : ℝ => (G (scalarPoint v)).toReal) u =
          (fun t : ℝ => 3 - t - 2 * Real.sqrt (4 - t)) u := by
      have hu0 : 0 ≤ u := le_of_lt hu.1
      have hu4 : u ≤ 1 + 3 := by linarith [hu.2]
      have hVal :
          G (scalarPoint u) = (absMinusTwoSqrtFiniteBranch (u - 3) : EReal) := by
        simp [G, absMinusTwoSqrtExampleFunction, scalarPoint, hu0, hu4]
      have hToReal :
          (G (scalarPoint u)).toReal = absMinusTwoSqrtFiniteBranch (u - 3) := by
        rw [hVal]
        simp
      have huNeg : u - 3 < 0 := sub_neg.mpr hu.2
      calc
        (G (scalarPoint u)).toReal = absMinusTwoSqrtFiniteBranch (u - 3) := hToReal
        _ = 3 - u - 2 * Real.sqrt (4 - u) := by
          have habs : |u - 3| = -(u - 3) := abs_of_neg huNeg
          rw [absMinusTwoSqrtFiniteBranch, habs]
          ring_nf
    exact
      (hSmooth.hasDerivWithinAt.congr_of_eventuallyEq hEventually huEq).derivWithin
        (uniqueDiffWithinAt_Ioi u)
  have hBridgeG :=
    helperForTheorem_5_24_4_derivWithin_scalarToReal_eq_rightDerivativeExtension_toReal_cutoff
      G hproperG (by norm_num : 0 < (3 : ℝ)) hDomG hu
  have huInteriorG : u ∈ interior (scalarEffectiveDomain G) := by
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo hu) (by
      intro v hv
      exact hDomG v hv)
  have hRightFiniteG :=
    helperForTheorem_5_24_1_scalarInterior_finiteDirectionalDerivatives G hproperG huInteriorG
  have huNotG :
      ¬ IsLeftOfScalarEffectiveDomain G u ∧ ¬ IsRightOfScalarEffectiveDomain G u :=
    helperForTheorem_5_24_1_not_left_not_right_of_mem_scalarEffectiveDomain G (hDomG u hu)
  have hFiniteTopG :
      rightDerivativeExtension G u ≠ (⊤ : EReal) := by
    simpa [rightDerivativeExtension, huNotG.2, huNotG.1] using hRightFiniteG.1
  have hFiniteBotG :
      rightDerivativeExtension G u ≠ (⊥ : EReal) := by
    simpa [rightDerivativeExtension, huNotG.2, huNotG.1] using hRightFiniteG.2.1
  have hRightG :
      rightDerivativeExtension G u =
        (((-1 + (Real.sqrt (4 - u))⁻¹ : ℝ) : EReal)) := by
    calc
      rightDerivativeExtension G u =
          (((rightDerivativeExtension G u).toReal : ℝ) : EReal) := by
            symm
            exact EReal.coe_toReal hFiniteTopG hFiniteBotG
      _ = (((-1 + (Real.sqrt (4 - u))⁻¹ : ℝ) : EReal)) := by
            exact_mod_cast (hBridgeG.symm.trans hDerivG)
  have hxDom : x ∈ scalarEffectiveDomain absMinusTwoSqrtExampleFunction := by
    rw [scalarEffectiveDomain, effectiveDomain_eq]
    constructor
    · simp
    · have hxC : -3 ≤ x ∧ x ≤ 1 := by
        constructor
        · exact le_of_lt hx.1
        · linarith [hx.2]
      simp [absMinusTwoSqrtExampleFunction, scalarPoint, hxC]
  have hxNot :
      ¬ IsLeftOfScalarEffectiveDomain absMinusTwoSqrtExampleFunction x ∧
        ¬ IsRightOfScalarEffectiveDomain absMinusTwoSqrtExampleFunction x :=
    helperForTheorem_5_24_1_not_left_not_right_of_mem_scalarEffectiveDomain
      absMinusTwoSqrtExampleFunction hxDom
  have hDQeq :
      ∀ t : ℝ,
        (G (scalarPoint u + t • scalarPoint 1) - G (scalarPoint u)) / (t : EReal) =
          (absMinusTwoSqrtExampleFunction (scalarPoint x + t • scalarPoint 1) -
            absMinusTwoSqrtExampleFunction (scalarPoint x)) / (t : EReal) := by
    intro t
    have harg0 :
        scalarPoint (x + 3) + t • scalarPoint 1 - scalarPoint 3 =
          scalarPoint x + t • scalarPoint 1 := by
      ext i
      simp [scalarPoint]
      ring
    have harg1 :
        scalarPoint (x + 3) - scalarPoint 3 = scalarPoint x := by
      ext i
      simp [scalarPoint]
    -- After rewriting the translated arguments, the quotients are identical.
    dsimp [G, u]
    rw [harg0, harg1]
  have hUdd :
      upperDirectionalDerivativeAt G (scalarPoint u) (scalarPoint 1) =
        upperDirectionalDerivativeAt absMinusTwoSqrtExampleFunction (scalarPoint x) (scalarPoint 1) := by
    unfold upperDirectionalDerivativeAt
    apply congrArg sInf
    ext a
    constructor <;> rintro ⟨b, hb, rfl⟩
    · refine ⟨b, hb, ?_⟩
      apply congrArg sSup
      ext q
      constructor <;> rintro ⟨t, ht0, htb, rfl⟩
      · refine ⟨t, ht0, htb, ?_⟩
        exact (hDQeq t).symm
      · refine ⟨t, ht0, htb, ?_⟩
        exact hDQeq t
    · refine ⟨b, hb, ?_⟩
      apply congrArg sSup
      ext q
      constructor <;> rintro ⟨t, ht0, htb, rfl⟩
      · refine ⟨t, ht0, htb, ?_⟩
        exact hDQeq t
      · refine ⟨t, ht0, htb, ?_⟩
        exact (hDQeq t).symm
  rw [show rightDerivativeExtension absMinusTwoSqrtExampleFunction x =
      upperDirectionalDerivativeAt absMinusTwoSqrtExampleFunction (scalarPoint x) (scalarPoint 1) by
        simp [rightDerivativeExtension, hxNot.2, hxNot.1]]
  rw [← hUdd]
  have hRightG' :
      upperDirectionalDerivativeAt G (scalarPoint u) (scalarPoint 1) =
        (((-1 + (Real.sqrt (4 - u))⁻¹ : ℝ) : EReal)) := by
    simpa [rightDerivativeExtension, huNotG.2, huNotG.1] using hRightG
  rw [hRightG']
  congr 1
  dsimp [u]
  congr 2
  ring_nf

lemma helperForExample_5_24_1_scalarEffectiveDomain_subset_Icc :
    scalarEffectiveDomain absMinusTwoSqrtExampleFunction ⊆ Set.Icc (-3 : ℝ) 1 := by
  intro x hx
  rw [scalarEffectiveDomain, effectiveDomain_eq] at hx
  constructor
  · by_contra hlt
    have hxC : ¬ (-3 ≤ x ∧ x ≤ 1) := by
      intro hxC
      exact hlt hxC.1
    simp [absMinusTwoSqrtExampleFunction, scalarPoint, hxC] at hx
  · by_contra hgt
    have hxC : ¬ (-3 ≤ x ∧ x ≤ 1) := by
      intro hxC
      exact hgt hxC.2
    simp [absMinusTwoSqrtExampleFunction, scalarPoint, hxC] at hx

lemma helperForExample_5_24_1_rightOfDomain_of_one_lt
    {x : ℝ} (hx : 1 < x) :
    IsRightOfScalarEffectiveDomain absMinusTwoSqrtExampleFunction x := by
  intro y hy
  have hyIcc := helperForExample_5_24_1_scalarEffectiveDomain_subset_Icc hy
  exact lt_of_le_of_lt hyIcc.2 hx

lemma helperForExample_5_24_1_leftOfDomain_of_lt_negThree
    {x : ℝ} (hx : x < -3) :
    IsLeftOfScalarEffectiveDomain absMinusTwoSqrtExampleFunction x := by
  intro y hy
  have hyIcc := helperForExample_5_24_1_scalarEffectiveDomain_subset_Icc hy
  exact lt_of_lt_of_le hx hyIcc.1

lemma helperForExample_5_24_1_rightDerivative_eq_top_of_one_lt
    {x : ℝ} (hx : 1 < x) :
    rightDerivativeExtension absMinusTwoSqrtExampleFunction x = (⊤ : EReal) := by
  have hxRight : IsRightOfScalarEffectiveDomain absMinusTwoSqrtExampleFunction x :=
    helperForExample_5_24_1_rightOfDomain_of_one_lt hx
  have hxNotLeft :
      ¬ IsLeftOfScalarEffectiveDomain absMinusTwoSqrtExampleFunction x := by
    rcases helperForExample_5_24_1_closedProperConvex with ⟨_hclosed, hproper⟩
    exact
      helperForTheorem_5_24_1_not_left_of_right
        absMinusTwoSqrtExampleFunction hproper hxRight
  simp [rightDerivativeExtension, hxRight, hxNotLeft]

lemma helperForExample_5_24_1_rightDerivative_eq_bot_of_lt_negThree
    {x : ℝ} (hx : x < -3) :
    rightDerivativeExtension absMinusTwoSqrtExampleFunction x = (⊥ : EReal) := by
  have hxLeft : IsLeftOfScalarEffectiveDomain absMinusTwoSqrtExampleFunction x :=
    helperForExample_5_24_1_leftOfDomain_of_lt_negThree hx
  have hxNotRight :
      ¬ IsRightOfScalarEffectiveDomain absMinusTwoSqrtExampleFunction x := by
    rcases helperForExample_5_24_1_closedProperConvex with ⟨_hclosed, hproper⟩
    exact
      helperForTheorem_5_24_1_not_right_of_left
        absMinusTwoSqrtExampleFunction hproper hxLeft
  simp [rightDerivativeExtension, hxLeft, hxNotRight]

lemma helperForExample_5_24_1_negBranch_continuousAt {x : ℝ} (hx : x < 1) :
    ContinuousAt
      (fun z : ℝ => (((-1 + (Real.sqrt (1 - z))⁻¹ : ℝ)) : EReal)) x := by
  have hOneSub : ContinuousAt (fun z : ℝ => 1 - z) x :=
    continuousAt_const.sub continuousAt_id
  have hSqrt : ContinuousAt (fun z : ℝ => Real.sqrt (1 - z)) x :=
    Real.continuous_sqrt.continuousAt.comp hOneSub
  have hSqrtNe : Real.sqrt (1 - x) ≠ 0 := by
    refine (Real.sqrt_ne_zero').2 ?_
    linarith
  have hInvBase : ContinuousAt (fun y : ℝ => y⁻¹) (Real.sqrt (1 - x)) :=
    continuousAt_inv₀ hSqrtNe
  have hInv : ContinuousAt (fun z : ℝ => (Real.sqrt (1 - z))⁻¹) x :=
    ContinuousAt.comp hInvBase hSqrt
  have hReal : ContinuousAt (fun z : ℝ => (-1 + (Real.sqrt (1 - z))⁻¹ : ℝ)) x :=
    continuousAt_const.add hInv
  exact continuous_coe_real_ereal.continuousAt.comp hReal

lemma helperForExample_5_24_1_posBranch_continuousAt {x : ℝ} (hx : x < 1) :
    ContinuousAt
      (fun z : ℝ => (((1 + (Real.sqrt (1 - z))⁻¹ : ℝ)) : EReal)) x := by
  have hOneSub : ContinuousAt (fun z : ℝ => 1 - z) x :=
    continuousAt_const.sub continuousAt_id
  have hSqrt : ContinuousAt (fun z : ℝ => Real.sqrt (1 - z)) x :=
    Real.continuous_sqrt.continuousAt.comp hOneSub
  have hSqrtNe : Real.sqrt (1 - x) ≠ 0 := by
    refine (Real.sqrt_ne_zero').2 ?_
    linarith
  have hInvBase : ContinuousAt (fun y : ℝ => y⁻¹) (Real.sqrt (1 - x)) :=
    continuousAt_inv₀ hSqrtNe
  have hInv : ContinuousAt (fun z : ℝ => (Real.sqrt (1 - z))⁻¹) x :=
    ContinuousAt.comp hInvBase hSqrt
  have hReal : ContinuousAt (fun z : ℝ => (1 + (Real.sqrt (1 - z))⁻¹ : ℝ)) x :=
    continuousAt_const.add hInv
  exact continuous_coe_real_ereal.continuousAt.comp hReal

lemma helperForExample_5_24_1_posBranch_tendsto_top_at_one :
    Filter.Tendsto
      (fun z : ℝ => (((1 + (Real.sqrt (1 - z))⁻¹ : ℝ)) : EReal))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (⊤ : EReal)) := by
  rw [EReal.tendsto_nhds_top_iff_real]
  intro a
  let K : ℝ := max 1 a
  let A : ℝ := (K⁻¹) ^ 2
  have hKpos : 0 < K := by
    dsimp [K]
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hEvent : Set.Ioo (1 - A) 1 ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) := by
    exact Ioo_mem_nhdsLT (sub_lt_self _ hApos)
  filter_upwards [hEvent] with t ht
  have htlt : t < 1 := ht.2
  have honeSubPos : 0 < 1 - t := sub_pos.mpr htlt
  have honeSubLt : 1 - t < A := by
    have htlower : 1 - A < t := ht.1
    linarith
  have hsqrtLt : Real.sqrt (1 - t) < K⁻¹ := by
    have hsqrtLt' : Real.sqrt (1 - t) < Real.sqrt A := by
      exact Real.sqrt_lt_sqrt (sub_nonneg.mpr htlt.le) honeSubLt
    have hKA : Real.sqrt A = K⁻¹ := by
      dsimp [A]
      have hKinvNonneg : 0 ≤ K⁻¹ := le_of_lt (inv_pos.mpr hKpos)
      rw [Real.sqrt_sq_eq_abs]
      exact abs_of_nonneg hKinvNonneg
    simpa [hKA] using hsqrtLt'
  have hsqrtPos : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 honeSubPos
  have hKsqrt : K * Real.sqrt (1 - t) < 1 := by
    have hmul := mul_lt_mul_of_pos_left hsqrtLt hKpos
    simpa [hKpos.ne', mul_assoc] using hmul
  have hInvGt : K < (Real.sqrt (1 - t))⁻¹ := by
    have hInvGt' : K < 1 / Real.sqrt (1 - t) := (lt_div_iff₀ hsqrtPos).2 hKsqrt
    simpa [one_div] using hInvGt'
  have haLe : a ≤ K := by
    dsimp [K]
    exact le_max_right _ _
  have hreal : a < (1 + (Real.sqrt (1 - t))⁻¹ : ℝ) := by
    have : a < (Real.sqrt (1 - t))⁻¹ := lt_of_le_of_lt haLe hInvGt
    linarith
  exact_mod_cast hreal

theorem absMinusTwoSqrtExample_closedProperConvex_derivatives_and_subdifferential :
    ClosedConvexFunction absMinusTwoSqrtExampleFunction ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) absMinusTwoSqrtExampleFunction ∧
      (∀ x : ℝ,
        rightDerivativeExtension absMinusTwoSqrtExampleFunction x =
          absMinusTwoSqrtExampleRightDerivative x) ∧
      (∀ x : ℝ,
        leftDerivativeExtension absMinusTwoSqrtExampleFunction x =
          absMinusTwoSqrtExampleLeftDerivative x) ∧
      (∀ x : ℝ,
        {xStar : ℝ |
            dotProductEquiv ℝ (Fin 1) (scalarPoint xStar) ∈
              ∂ absMinusTwoSqrtExampleFunction (scalarPoint x)} =
          absMinusTwoSqrtExampleSubdifferential x) := by
  have hMain :
      ClosedConvexFunction absMinusTwoSqrtExampleFunction ∧
        ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) absMinusTwoSqrtExampleFunction ∧
        (∀ x : ℝ,
          rightDerivativeExtension absMinusTwoSqrtExampleFunction x =
            absMinusTwoSqrtExampleRightDerivative x) ∧
        (∀ x : ℝ,
          leftDerivativeExtension absMinusTwoSqrtExampleFunction x =
            absMinusTwoSqrtExampleLeftDerivative x) := by
    rcases helperForExample_5_24_1_closedProperConvex with ⟨hclosed, hproper⟩
    have hRightPos :
        ∀ x ∈ Set.Ioo (0 : ℝ) 1,
          rightDerivativeExtension absMinusTwoSqrtExampleFunction x =
            absMinusTwoSqrtExampleRightDerivative x := by
      intro x hx
      rw [helperForExample_5_24_1_rightDerivative_on_Ioo_zero_one hx]
      simp [absMinusTwoSqrtExampleRightDerivative, not_le.mpr hx.2, le_of_lt hx.1]
    have hRightExteriorTop :
        ∀ x > 1,
          rightDerivativeExtension absMinusTwoSqrtExampleFunction x =
            absMinusTwoSqrtExampleRightDerivative x := by
      intro x hx
      rw [helperForExample_5_24_1_rightDerivative_eq_top_of_one_lt hx]
      simp [absMinusTwoSqrtExampleRightDerivative, le_of_lt hx]
    have hRightExteriorBot :
        ∀ x < -3,
          rightDerivativeExtension absMinusTwoSqrtExampleFunction x =
            absMinusTwoSqrtExampleRightDerivative x := by
      intro x hx
      have hx1 : ¬ 1 ≤ x := not_le.mpr (lt_trans hx (by norm_num : (-3 : ℝ) < 1))
      have hx0 : ¬ 0 ≤ x := not_le.mpr (lt_trans hx (by norm_num : (-3 : ℝ) < 0))
      have hxm3 : ¬ -3 ≤ x := not_le.mpr hx
      rw [helperForExample_5_24_1_rightDerivative_eq_bot_of_lt_negThree hx]
      simp [absMinusTwoSqrtExampleRightDerivative, hx1, hx0, hxm3]
    have hRightNeg :
        ∀ x ∈ Set.Ioo (-3 : ℝ) 0,
          rightDerivativeExtension absMinusTwoSqrtExampleFunction x =
            absMinusTwoSqrtExampleRightDerivative x := by
      intro x hx
      rw [helperForExample_5_24_1_rightDerivative_on_Ioo_negThree_zero hx]
      have hx1 : ¬ 1 ≤ x := not_le.mpr (lt_trans hx.2 (by norm_num : (0 : ℝ) < 1))
      have hx0 : ¬ 0 ≤ x := not_le.mpr hx.2
      simp [absMinusTwoSqrtExampleRightDerivative, hx1, hx0, le_of_lt hx.1]
    rcases
      oneDimensional_derivativeExtensions_monotone_ordered_and_oneSidedContinuous
        absMinusTwoSqrtExampleFunction hclosed hproper with
      ⟨_hmonoRight, _hmonoLeft, _hfiniteInt, _horder, hRightSelf, hRightLeft, _hLeftRight,
        _hLeftSelf⟩
    have hRight :
        ∀ x : ℝ,
          rightDerivativeExtension absMinusTwoSqrtExampleFunction x =
            absMinusTwoSqrtExampleRightDerivative x := by
      intro x
      by_cases hx1 : 1 ≤ x
      · by_cases hEq1 : x = 1
        · subst hEq1
          have hEventuallyTop :
              (fun z : ℝ => rightDerivativeExtension absMinusTwoSqrtExampleFunction z) =ᶠ[
                nhdsWithin (1 : ℝ) (Set.Ioi 1)] fun _ : ℝ => (⊤ : EReal) := by
            filter_upwards [self_mem_nhdsWithin] with z hz
            exact helperForExample_5_24_1_rightDerivative_eq_top_of_one_lt hz
          have hTopLimit :
              Filter.Tendsto
                (fun z : ℝ => rightDerivativeExtension absMinusTwoSqrtExampleFunction z)
                (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (⊤ : EReal)) := by
            exact Filter.Tendsto.congr' hEventuallyTop.symm tendsto_const_nhds
          have hEq :
              rightDerivativeExtension absMinusTwoSqrtExampleFunction 1 = (⊤ : EReal) :=
            tendsto_nhds_unique (hRightSelf 1) hTopLimit
          simpa [absMinusTwoSqrtExampleRightDerivative] using hEq
        · exact hRightExteriorTop x (lt_of_le_of_ne hx1 (Ne.symm hEq1))
      · by_cases hxm3 : x < -3
        · exact hRightExteriorBot x hxm3
        · have hxm3le : -3 ≤ x := by linarith
          by_cases hx0 : 0 ≤ x
          · by_cases hEq0 : x = 0
            · subst hEq0
              have hIoo : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
                exact Ioo_mem_nhdsGT zero_lt_one
              have hEventuallyPos :
                  (fun z : ℝ => rightDerivativeExtension absMinusTwoSqrtExampleFunction z) =ᶠ[
                    nhdsWithin (0 : ℝ) (Set.Ioi 0)]
                    (fun z : ℝ => (((1 + (Real.sqrt (1 - z))⁻¹ : ℝ)) : EReal)) := by
                filter_upwards [hIoo] with z hz
                simpa using helperForExample_5_24_1_rightDerivative_on_Ioo_zero_one hz
              have hPosLimit :
                  Filter.Tendsto
                    (fun z : ℝ => (((1 + (Real.sqrt (1 - z))⁻¹ : ℝ)) : EReal))
                    (nhdsWithin (0 : ℝ) (Set.Ioi 0))
                    (nhds (((1 + (Real.sqrt (1 - (0 : ℝ)))⁻¹ : ℝ)) : EReal)) := by
                exact
                  (helperForExample_5_24_1_posBranch_continuousAt
                    (x := (0 : ℝ)) (by norm_num)).continuousWithinAt.tendsto
              have hEq :
                  rightDerivativeExtension absMinusTwoSqrtExampleFunction 0 =
                    (((1 + (Real.sqrt (1 - (0 : ℝ)))⁻¹ : ℝ)) : EReal) :=
                tendsto_nhds_unique (hRightSelf 0)
                  (Filter.Tendsto.congr' hEventuallyPos.symm hPosLimit)
              norm_num [absMinusTwoSqrtExampleRightDerivative] at hEq ⊢
              exact hEq
            · exact hRightPos x ⟨lt_of_le_of_ne hx0 (Ne.symm hEq0), lt_of_not_ge hx1⟩
          · by_cases hEqm3 : x = -3
            · subst hEqm3
              have hIoo : Set.Ioo (-3 : ℝ) 0 ∈ nhdsWithin (-3 : ℝ) (Set.Ioi (-3)) := by
                exact Ioo_mem_nhdsGT (by norm_num)
              have hEventuallyNeg :
                  (fun z : ℝ => rightDerivativeExtension absMinusTwoSqrtExampleFunction z) =ᶠ[
                    nhdsWithin (-3 : ℝ) (Set.Ioi (-3))]
                    (fun z : ℝ => (((-1 + (Real.sqrt (1 - z))⁻¹ : ℝ)) : EReal)) := by
                filter_upwards [hIoo] with z hz
                simpa using helperForExample_5_24_1_rightDerivative_on_Ioo_negThree_zero hz
              have hNegLimit :
                  Filter.Tendsto
                    (fun z : ℝ => (((-1 + (Real.sqrt (1 - z))⁻¹ : ℝ)) : EReal))
                    (nhdsWithin (-3 : ℝ) (Set.Ioi (-3)))
                    (nhds (((-1 + (Real.sqrt (1 - (-3 : ℝ)))⁻¹ : ℝ)) : EReal)) := by
                exact
                  (helperForExample_5_24_1_negBranch_continuousAt
                    (x := (-3 : ℝ)) (by norm_num)).continuousWithinAt.tendsto
              have hEq :
                  rightDerivativeExtension absMinusTwoSqrtExampleFunction (-3) =
                    (((-1 + (Real.sqrt (1 - (-3 : ℝ)))⁻¹ : ℝ)) : EReal) :=
                tendsto_nhds_unique (hRightSelf (-3))
                  (Filter.Tendsto.congr' hEventuallyNeg.symm hNegLimit)
              norm_num [absMinusTwoSqrtExampleRightDerivative] at hEq ⊢
              exact hEq
            · exact hRightNeg x ⟨lt_of_le_of_ne hxm3le (Ne.symm hEqm3), lt_of_not_ge hx0⟩
    have hLeft :
        ∀ x : ℝ,
          leftDerivativeExtension absMinusTwoSqrtExampleFunction x =
            absMinusTwoSqrtExampleLeftDerivative x := by
      intro x
      by_cases hx1 : 1 ≤ x
      · by_cases hEq1 : x = 1
        · subst hEq1
          have hIoo : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) := by
            exact Ioo_mem_nhdsLT zero_lt_one
          have hEventuallyPos :
              (fun z : ℝ => rightDerivativeExtension absMinusTwoSqrtExampleFunction z) =ᶠ[
                nhdsWithin (1 : ℝ) (Set.Iio 1)]
                (fun z : ℝ => (((1 + (Real.sqrt (1 - z))⁻¹ : ℝ)) : EReal)) := by
            filter_upwards [hIoo] with z hz
            simpa using helperForExample_5_24_1_rightDerivative_on_Ioo_zero_one hz
          have hEq :
              leftDerivativeExtension absMinusTwoSqrtExampleFunction 1 = (⊤ : EReal) :=
            tendsto_nhds_unique (hRightLeft 1)
              (Filter.Tendsto.congr' hEventuallyPos.symm
                helperForExample_5_24_1_posBranch_tendsto_top_at_one)
          simpa [absMinusTwoSqrtExampleLeftDerivative] using hEq
        · have hxgt : 1 < x := lt_of_le_of_ne hx1 (Ne.symm hEq1)
          have hIoo : Set.Ioo (1 : ℝ) x ∈ nhdsWithin x (Set.Iio x) := by
            exact Ioo_mem_nhdsLT hxgt
          have hEventuallyTop :
              (fun z : ℝ => rightDerivativeExtension absMinusTwoSqrtExampleFunction z) =ᶠ[
                nhdsWithin x (Set.Iio x)] fun _ : ℝ => (⊤ : EReal) := by
            filter_upwards [hIoo] with z hz
            exact helperForExample_5_24_1_rightDerivative_eq_top_of_one_lt hz.1
          have hEq :
              leftDerivativeExtension absMinusTwoSqrtExampleFunction x = (⊤ : EReal) :=
            tendsto_nhds_unique (hRightLeft x)
              (Filter.Tendsto.congr' hEventuallyTop.symm tendsto_const_nhds)
          simpa [absMinusTwoSqrtExampleLeftDerivative, hx1] using hEq
      · by_cases hxm3 : -3 < x
        · by_cases hx0 : 0 ≤ x
          · by_cases hEq0 : x = 0
            · subst hEq0
              have hIoo : Set.Ioo (-3 : ℝ) 0 ∈ nhdsWithin (0 : ℝ) (Set.Iio 0) := by
                exact Ioo_mem_nhdsLT (by norm_num)
              have hEventuallyNeg :
                  (fun z : ℝ => rightDerivativeExtension absMinusTwoSqrtExampleFunction z) =ᶠ[
                    nhdsWithin (0 : ℝ) (Set.Iio 0)]
                    (fun z : ℝ => (((-1 + (Real.sqrt (1 - z))⁻¹ : ℝ)) : EReal)) := by
                filter_upwards [hIoo] with z hz
                simpa using helperForExample_5_24_1_rightDerivative_on_Ioo_negThree_zero hz
              have hNegLimit :
                  Filter.Tendsto
                    (fun z : ℝ => (((-1 + (Real.sqrt (1 - z))⁻¹ : ℝ)) : EReal))
                    (nhdsWithin (0 : ℝ) (Set.Iio 0))
                    (nhds (((-1 + (Real.sqrt (1 - (0 : ℝ)))⁻¹ : ℝ)) : EReal)) := by
                exact
                  (helperForExample_5_24_1_negBranch_continuousAt
                    (x := (0 : ℝ)) (by norm_num)).continuousWithinAt.tendsto
              have hEq :
                  leftDerivativeExtension absMinusTwoSqrtExampleFunction 0 =
                    (((-1 + (Real.sqrt (1 - (0 : ℝ)))⁻¹ : ℝ)) : EReal) :=
                tendsto_nhds_unique (hRightLeft 0)
                  (Filter.Tendsto.congr' hEventuallyNeg.symm hNegLimit)
              norm_num [absMinusTwoSqrtExampleLeftDerivative] at hEq ⊢
              exact hEq
            · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hEq0)
              have hx01 : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hxpos, lt_of_not_ge hx1⟩
              have hIoo : Set.Ioo (0 : ℝ) x ∈ nhdsWithin x (Set.Iio x) := by
                exact Ioo_mem_nhdsLT hx01.1
              have hEventuallyPos :
                  (fun z : ℝ => rightDerivativeExtension absMinusTwoSqrtExampleFunction z) =ᶠ[
                    nhdsWithin x (Set.Iio x)]
                    (fun z : ℝ => (((1 + (Real.sqrt (1 - z))⁻¹ : ℝ)) : EReal)) := by
                filter_upwards [hIoo] with z hz
                simpa using helperForExample_5_24_1_rightDerivative_on_Ioo_zero_one
                  ⟨hz.1, lt_trans hz.2 hx01.2⟩
              have hPosLimit :
                  Filter.Tendsto
                    (fun z : ℝ => (((1 + (Real.sqrt (1 - z))⁻¹ : ℝ)) : EReal))
                    (nhdsWithin x (Set.Iio x))
                    (nhds (((1 + (Real.sqrt (1 - x))⁻¹ : ℝ)) : EReal)) := by
                exact
                  (helperForExample_5_24_1_posBranch_continuousAt
                    (x := x) (lt_of_not_ge hx1)).continuousWithinAt.tendsto
              have hEq :
                  leftDerivativeExtension absMinusTwoSqrtExampleFunction x =
                    (((1 + (Real.sqrt (1 - x))⁻¹ : ℝ)) : EReal) :=
                tendsto_nhds_unique (hRightLeft x)
                  (Filter.Tendsto.congr' hEventuallyPos.symm hPosLimit)
              simpa [absMinusTwoSqrtExampleLeftDerivative, hx1, hxpos] using hEq
          · have hxneg : x < 0 := lt_of_not_ge hx0
            have hIoo : Set.Ioo (-3 : ℝ) x ∈ nhdsWithin x (Set.Iio x) := by
              exact Ioo_mem_nhdsLT hxm3
            have hEventuallyNeg :
                (fun z : ℝ => rightDerivativeExtension absMinusTwoSqrtExampleFunction z) =ᶠ[
                  nhdsWithin x (Set.Iio x)]
                  (fun z : ℝ => (((-1 + (Real.sqrt (1 - z))⁻¹ : ℝ)) : EReal)) := by
              filter_upwards [hIoo] with z hz
              simpa using helperForExample_5_24_1_rightDerivative_on_Ioo_negThree_zero
                ⟨hz.1, lt_trans hz.2 hxneg⟩
            have hNegLimit :
                Filter.Tendsto
                  (fun z : ℝ => (((-1 + (Real.sqrt (1 - z))⁻¹ : ℝ)) : EReal))
                  (nhdsWithin x (Set.Iio x))
                  (nhds (((-1 + (Real.sqrt (1 - x))⁻¹ : ℝ)) : EReal)) := by
              exact
                (helperForExample_5_24_1_negBranch_continuousAt
                  (x := x) (lt_of_not_ge hx1)).continuousWithinAt.tendsto
            have hEq :
                leftDerivativeExtension absMinusTwoSqrtExampleFunction x =
                  (((-1 + (Real.sqrt (1 - x))⁻¹ : ℝ)) : EReal) :=
              tendsto_nhds_unique (hRightLeft x)
                (Filter.Tendsto.congr' hEventuallyNeg.symm hNegLimit)
            simpa [absMinusTwoSqrtExampleLeftDerivative, hx1, not_lt.mpr hxneg.le, hxm3] using hEq
        · have hxle : x ≤ -3 := le_of_not_gt hxm3
          have hEventuallyBot :
              (fun z : ℝ => rightDerivativeExtension absMinusTwoSqrtExampleFunction z) =ᶠ[
                nhdsWithin x (Set.Iio x)] fun _ : ℝ => (⊥ : EReal) := by
            filter_upwards [self_mem_nhdsWithin] with z hz
            have hzlt : z < -3 := lt_of_lt_of_le hz hxle
            exact helperForExample_5_24_1_rightDerivative_eq_bot_of_lt_negThree hzlt
          have hEq :
              leftDerivativeExtension absMinusTwoSqrtExampleFunction x = (⊥ : EReal) :=
            tendsto_nhds_unique (hRightLeft x)
              (Filter.Tendsto.congr' hEventuallyBot.symm tendsto_const_nhds)
          have hx1nle : ¬ 1 ≤ x := hx1
          have hx0nlt : ¬ 0 < x := not_lt.mpr (le_trans hxle (by norm_num))
          have hxm3nlt : ¬ -3 < x := hxm3
          simpa [absMinusTwoSqrtExampleLeftDerivative, hx1nle, hx0nlt, hxm3nlt] using hEq
    exact ⟨hclosed, hproper, hRight, hLeft⟩
  rcases hMain with ⟨hclosed, hproper, hRight, hLeft⟩
  refine ⟨hclosed, hproper, hRight, hLeft, ?_⟩
  exact
    helperForExample_5_24_1_subdifferential_of_derivative_profiles
      hclosed hproper hRight hLeft

/-- The one-dimensional nonclosed counterexample with value `0` on `(-∞, 0)`, value `1` at `0`,
and value `+∞` on `(0, ∞)`, viewed as a function on `Fin 1 → ℝ`. -/
noncomputable def zeroJumpCounterexampleFunction (x : Fin 1 → ℝ) : EReal :=
  if x 0 < 0 then
    (0 : EReal)
  else if x 0 = 0 then
    (1 : EReal)
  else
    (⊤ : EReal)

/-- The right-derivative profile for `zeroJumpCounterexampleFunction`: it is `0` on `(-∞, 0)`
and `+∞` on `[0, ∞)`. -/
noncomputable def zeroJumpCounterexampleRightDerivative (x : ℝ) : EReal :=
  if x < 0 then
    (0 : EReal)
  else
    (⊤ : EReal)

-- Proof sketch: verify directly that the function is convex and proper but fails closedness
-- because of the jump at `0`. Then compute the right derivative from the definition of
-- `upperDirectionalDerivativeAt`: for `x < 0` all sufficiently small forward difference
-- quotients vanish, while at `x = 0` and for `x > 0` the domain extension forces the derivative
-- to be `+∞`. The left-hand limit of the right derivative at `0` is therefore `0`, while the
-- extended left derivative at `0` is different; this witnesses failure of the closed-case identity
-- `lim_{z ↑ x} f'_+(z) = f'_-(x)` from Theorem 5.24.1 once closedness is dropped.
/-- Example 5.24.2: for the function `f(x) = 0` if `x < 0`, `f(0) = 1`, and `f(x) = +∞` if
`x > 0`, the right derivative extension satisfies `f'_+(x) = 0` for `x < 0` and
`f'_+(x) = +∞` for `x ≥ 0`; in this proper convex but nonclosed example, the left-limit identity
`lim_{z ↑ 0} f'_+(z) = f'_-(0)` from Theorem 5.24.1 fails. -/
theorem zeroJumpCounterexample_properConvex_notClosed_rightDerivative_and_limitFailure :
    ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) zeroJumpCounterexampleFunction ∧
      ¬ ClosedConvexFunction zeroJumpCounterexampleFunction ∧
      (∀ x : ℝ,
        rightDerivativeExtension zeroJumpCounterexampleFunction x =
          zeroJumpCounterexampleRightDerivative x) ∧
      ¬ Filter.Tendsto (rightDerivativeExtension zeroJumpCounterexampleFunction)
        (nhdsWithin 0 (Set.Iio 0))
        (nhds (leftDerivativeExtension zeroJumpCounterexampleFunction 0)) := by
  have hnotbot :
      ∀ x ∈ (Set.univ : Set (Fin 1 → ℝ)), zeroJumpCounterexampleFunction x ≠ (⊥ : EReal) := by
    intro x hx
    by_cases hxlt : x 0 < 0
    · simp [zeroJumpCounterexampleFunction, hxlt]
    · by_cases hx0 : x 0 = 0
      · simpa [zeroJumpCounterexampleFunction, hx0] using (EReal.coe_ne_bot (1 : ℝ))
      · simp [zeroJumpCounterexampleFunction, hxlt, hx0]
  have hconv :
      ConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) zeroJumpCounterexampleFunction := by
    intro p hp q hq a b ha hb hab
    constructor
    · trivial
    change
      zeroJumpCounterexampleFunction (a • p.1 + b • q.1) ≤
        ((a * p.2 + b * q.2 : ℝ) : EReal)
    have hp_le : zeroJumpCounterexampleFunction p.1 ≤ (p.2 : EReal) := hp.2
    have hq_le : zeroJumpCounterexampleFunction q.1 ≤ (q.2 : EReal) := hq.2
    have hp_nonpos : p.1 0 ≤ 0 := by
      by_contra hp_pos
      have hp_top : zeroJumpCounterexampleFunction p.1 = (⊤ : EReal) := by
        have hp_gt : 0 < p.1 0 := by linarith
        simp [zeroJumpCounterexampleFunction, hp_gt, not_lt.mpr (le_of_lt hp_gt), hp_gt.ne']
      exact not_top_le_coe p.2 (hp_top ▸ hp_le)
    have hq_nonpos : q.1 0 ≤ 0 := by
      by_contra hq_pos
      have hq_top : zeroJumpCounterexampleFunction q.1 = (⊤ : EReal) := by
        have hq_gt : 0 < q.1 0 := by linarith
        simp [zeroJumpCounterexampleFunction, hq_gt, not_lt.mpr (le_of_lt hq_gt), hq_gt.ne']
      exact not_top_le_coe q.2 (hq_top ▸ hq_le)
    have hp_nonneg : (0 : ℝ) ≤ p.2 := by
      by_cases hp_lt : p.1 0 < 0
      · have hp_zero : zeroJumpCounterexampleFunction p.1 = (0 : EReal) := by
          simp [zeroJumpCounterexampleFunction, hp_lt]
        exact_mod_cast (hp_zero ▸ hp_le)
      · have hp_zeroCoord : p.1 0 = 0 := by linarith
        have hp_one : zeroJumpCounterexampleFunction p.1 = (1 : EReal) := by
          simp [zeroJumpCounterexampleFunction, hp_lt, hp_zeroCoord]
        have hp_one_le : (1 : EReal) ≤ (p.2 : EReal) := hp_one ▸ hp_le
        have hp_one_le_real : (1 : ℝ) ≤ p.2 := by
          exact_mod_cast hp_one_le
        linarith
    have hq_nonneg : (0 : ℝ) ≤ q.2 := by
      by_cases hq_lt : q.1 0 < 0
      · have hq_zero : zeroJumpCounterexampleFunction q.1 = (0 : EReal) := by
          simp [zeroJumpCounterexampleFunction, hq_lt]
        exact_mod_cast (hq_zero ▸ hq_le)
      · have hq_zeroCoord : q.1 0 = 0 := by linarith
        have hq_one : zeroJumpCounterexampleFunction q.1 = (1 : EReal) := by
          simp [zeroJumpCounterexampleFunction, hq_lt, hq_zeroCoord]
        have hq_one_le : (1 : EReal) ≤ (q.2 : EReal) := hq_one ▸ hq_le
        have hq_one_le_real : (1 : ℝ) ≤ q.2 := by
          exact_mod_cast hq_one_le
        linarith
    have hcombo_nonpos : (a • p.1 + b • q.1) 0 ≤ 0 := by
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith
    by_cases hcombo_lt : (a • p.1 + b • q.1) 0 < 0
    · have hcombo_zero :
          zeroJumpCounterexampleFunction (a • p.1 + b • q.1) = (0 : EReal) := by
        have hcoord_lt : a * p.1 0 + b * q.1 0 < 0 := by
          simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hcombo_lt
        have hcoord_ne : a * p.1 0 + b * q.1 0 ≠ 0 := ne_of_lt hcoord_lt
        simp [zeroJumpCounterexampleFunction, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          hcoord_lt, hcoord_ne]
      rw [hcombo_zero]
      have hμ_nonneg : (0 : EReal) ≤ ((a * p.2 + b * q.2 : ℝ) : EReal) := by
        exact_mod_cast (show 0 ≤ a * p.2 + b * q.2 by nlinarith)
      simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc] using hμ_nonneg
    · have hcombo_zeroCoord : (a • p.1 + b • q.1) 0 = 0 := by linarith
      have hp_zero_or_a_zero : p.1 0 = 0 ∨ a = 0 := by
        by_cases ha0 : a = 0
        · exact Or.inr ha0
        · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
          have hp_zero : p.1 0 = 0 := by
            by_contra hp_ne_zero
            have hp_lt : p.1 0 < 0 := lt_of_le_of_ne hp_nonpos hp_ne_zero
            have hstrict : (a • p.1 + b • q.1) 0 < 0 := by
              simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              nlinarith
            exact hcombo_lt hstrict
          exact Or.inl hp_zero
      have hq_zero_or_b_zero : q.1 0 = 0 ∨ b = 0 := by
        by_cases hb0 : b = 0
        · exact Or.inr hb0
        · have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
          have hq_zero : q.1 0 = 0 := by
            by_contra hq_ne_zero
            have hq_lt : q.1 0 < 0 := lt_of_le_of_ne hq_nonpos hq_ne_zero
            have hstrict : (a • p.1 + b • q.1) 0 < 0 := by
              simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              nlinarith
            exact hcombo_lt hstrict
          exact Or.inl hq_zero
      have hp_zero_implies_one_le : p.1 0 = 0 → 1 ≤ p.2 := by
        intro hp_zero
        have hp_one : zeroJumpCounterexampleFunction p.1 = (1 : EReal) := by
          have hp_not_lt : ¬ p.1 0 < 0 := by simpa [hp_zero]
          simp [zeroJumpCounterexampleFunction, hp_not_lt, hp_zero]
        have hp_one_le' : (1 : EReal) ≤ (p.2 : EReal) := hp_one ▸ hp_le
        exact_mod_cast hp_one_le'
      have hq_zero_implies_one_le : q.1 0 = 0 → 1 ≤ q.2 := by
        intro hq_zero
        have hq_one : zeroJumpCounterexampleFunction q.1 = (1 : EReal) := by
          have hq_not_lt : ¬ q.1 0 < 0 := by simpa [hq_zero]
          simp [zeroJumpCounterexampleFunction, hq_not_lt, hq_zero]
        have hq_one_le' : (1 : EReal) ≤ (q.2 : EReal) := hq_one ▸ hq_le
        exact_mod_cast hq_one_le'
      have hcombo_one :
          zeroJumpCounterexampleFunction (a • p.1 + b • q.1) = (1 : EReal) := by
        simp [zeroJumpCounterexampleFunction, hcombo_zeroCoord, hcombo_lt]
      have hμ_one : (1 : ℝ) ≤ a * p.2 + b * q.2 := by
        rcases hp_zero_or_a_zero with hp_zero | ha0
        · rcases hq_zero_or_b_zero with hq_zero | hb0
          · have hp1 : 1 ≤ p.2 := hp_zero_implies_one_le hp_zero
            have hq1 : 1 ≤ q.2 := hq_zero_implies_one_le hq_zero
            nlinarith
          · have hp1 : 1 ≤ p.2 := hp_zero_implies_one_le hp_zero
            have ha1 : a = 1 := by linarith
            nlinarith
        · rcases hq_zero_or_b_zero with hq_zero | hb0
          · have hq1 : 1 ≤ q.2 := hq_zero_implies_one_le hq_zero
            have hb1 : b = 1 := by linarith
            nlinarith
          · exfalso
            linarith
      rw [hcombo_one]
      exact_mod_cast hμ_one
  have hproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) zeroJumpCounterexampleFunction := by
    refine ⟨hconv, ?_, hnotbot⟩
    refine ⟨(scalarPoint 0, 1), ?_⟩
    refine (mem_epigraph_univ_iff (f := zeroJumpCounterexampleFunction)).2 ?_
    simp [zeroJumpCounterexampleFunction, scalarPoint]
  have hscalarDom :
      scalarEffectiveDomain zeroJumpCounterexampleFunction = Set.Iic 0 := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨μ, hμ⟩
      by_contra hxPos
      have hxgt : 0 < x := lt_of_not_ge hxPos
      have htop : zeroJumpCounterexampleFunction (scalarPoint x) = (⊤ : EReal) := by
        have hnotlt : ¬ x < 0 := not_lt.mpr (le_of_lt hxgt)
        have hxne : ¬ x = 0 := ne_of_gt hxgt
        simp [zeroJumpCounterexampleFunction, scalarPoint, hxgt, hnotlt, hxne]
      exact not_top_le_coe μ (htop ▸ hμ.2)
    · intro hx
      change scalarPoint x ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
        zeroJumpCounterexampleFunction
      refine ⟨1, ?_⟩
      constructor
      · trivial
      by_cases hx0 : x = 0
      · simp [scalarPoint, zeroJumpCounterexampleFunction, hx0]
      · have hxlt : x < 0 := lt_of_le_of_ne hx hx0
        simp [scalarPoint, zeroJumpCounterexampleFunction, hxlt, hx0]
  have hRight :
      ∀ x : ℝ,
        rightDerivativeExtension zeroJumpCounterexampleFunction x =
          zeroJumpCounterexampleRightDerivative x := by
    intro x
    by_cases hxlt : x < 0
    · have hxDom : x ∈ scalarEffectiveDomain zeroJumpCounterexampleFunction := by
        simpa [hscalarDom] using hxlt.le
      have hxNot :
          ¬ IsLeftOfScalarEffectiveDomain zeroJumpCounterexampleFunction x ∧
            ¬ IsRightOfScalarEffectiveDomain zeroJumpCounterexampleFunction x :=
        helperForTheorem_5_24_1_not_left_not_right_of_mem_scalarEffectiveDomain
          zeroJumpCounterexampleFunction hxDom
      have hxFinite :
          zeroJumpCounterexampleFunction (scalarPoint x) ≠ (⊤ : EReal) ∧
            zeroJumpCounterexampleFunction (scalarPoint x) ≠ (⊥ : EReal) := by
        exact
          ⟨mem_effectiveDomain_imp_ne_top
              (S := (Set.univ : Set (Fin 1 → ℝ))) (f := zeroJumpCounterexampleFunction) hxDom,
            hproper.2.2 (scalarPoint x) (by simp)⟩
      have hf : ConvexFunction zeroJumpCounterexampleFunction := by
        simpa [ConvexFunction] using hproper.1
      rcases convex_directionalDerivative_monotone_exists_and_sublinear
          zeroJumpCounterexampleFunction hf (scalarPoint x) hxFinite with
        ⟨hdirRight, _hposRight, _hconvRight, _hzeroRight, _hsymmRight⟩
      have ht0 : 0 < -x / 2 := by nlinarith
      have hquotZero :
          directionalDifferenceQuotientAt zeroJumpCounterexampleFunction
              (scalarPoint x) (scalarPoint 1) (-x / 2) = (0 : EReal) := by
        rw [helperForTheorem_5_24_1_directionalDifferenceQuotient_dirOne_eq_scalarSecant]
        have hxhalf : x + (-x / 2) < 0 := by nlinarith
        have hxVal :
            zeroJumpCounterexampleFunction (scalarPoint x) = (0 : EReal) := by
          simp [scalarPoint, zeroJumpCounterexampleFunction, hxlt]
        have hstepVal :
            zeroJumpCounterexampleFunction (scalarPoint (x + (-x / 2))) = (0 : EReal) := by
          simp [scalarPoint, zeroJumpCounterexampleFunction, hxhalf]
        simp [hxVal, hstepVal, ht0.ne']
      have hnonempty :
          ((Set.Ioi (0 : ℝ)).image
            fun t : ℝ =>
              directionalDifferenceQuotientAt zeroJumpCounterexampleFunction
                (scalarPoint x) (scalarPoint 1) t).Nonempty := by
        exact ⟨0, ⟨-x / 2, ht0, hquotZero⟩⟩
      have hzero_le :
          (0 : EReal) ≤
            upperDirectionalDerivativeAt zeroJumpCounterexampleFunction
              (scalarPoint x) (scalarPoint 1) := by
        rw [(hdirRight (scalarPoint 1)).2.2]
        refine le_csInf hnonempty ?_
        intro q hq
        rcases hq with ⟨t, ht, rfl⟩
        have ht' : 0 < t := by simpa using ht
        by_cases hxt : x + t < 0
        · change
            (0 : EReal) ≤
              directionalDifferenceQuotientAt zeroJumpCounterexampleFunction
                (scalarPoint x) (scalarPoint 1) t
          rw [helperForTheorem_5_24_1_directionalDifferenceQuotient_dirOne_eq_scalarSecant]
          have hxVal :
              zeroJumpCounterexampleFunction (scalarPoint x) = (0 : EReal) := by
            simp [scalarPoint, zeroJumpCounterexampleFunction, hxlt]
          have hstepVal :
              zeroJumpCounterexampleFunction (scalarPoint (x + t)) = (0 : EReal) := by
            simp [scalarPoint, zeroJumpCounterexampleFunction, hxt]
          simp [hxVal, hstepVal, ht'.ne']
        · by_cases hxeq : x + t = 0
          · change
              (0 : EReal) ≤
                directionalDifferenceQuotientAt zeroJumpCounterexampleFunction
                  (scalarPoint x) (scalarPoint 1) t
            rw [helperForTheorem_5_24_1_directionalDifferenceQuotient_dirOne_eq_scalarSecant]
            have hxVal :
                zeroJumpCounterexampleFunction (scalarPoint x) = (0 : EReal) := by
              simp [scalarPoint, zeroJumpCounterexampleFunction, hxlt]
            have hstepVal :
                zeroJumpCounterexampleFunction (scalarPoint (x + t)) = (1 : EReal) := by
              simp [scalarPoint, zeroJumpCounterexampleFunction, hxeq]
            rw [hstepVal, hxVal]
            have hpos : (0 : EReal) ≤ (((t : ℝ) : EReal)⁻¹) := by
              rw [← EReal.coe_inv t, EReal.coe_nonneg]
              exact inv_nonneg.mpr (le_of_lt ht')
            simpa [div_eq_mul_inv] using hpos
          · have hxle : 0 ≤ x + t := not_lt.mp hxt
            have hne : x + t ≠ 0 := by exact hxeq
            have hne0 : 0 ≠ x + t := by simpa [eq_comm] using hne
            have hxgt : 0 < x + t := lt_of_le_of_ne hxle hne0
            change
              (0 : EReal) ≤
                directionalDifferenceQuotientAt zeroJumpCounterexampleFunction
                  (scalarPoint x) (scalarPoint 1) t
            rw [helperForTheorem_5_24_1_directionalDifferenceQuotient_dirOne_eq_scalarSecant]
            have hstepTop :
                zeroJumpCounterexampleFunction (scalarPoint (x + t)) = (⊤ : EReal) := by
              simp [scalarPoint, zeroJumpCounterexampleFunction, hxgt, not_lt.mpr (le_of_lt hxgt),
                ne_of_gt hxgt]
            have hxVal :
                zeroJumpCounterexampleFunction (scalarPoint x) = (0 : EReal) := by
              simp [scalarPoint, zeroJumpCounterexampleFunction, hxlt]
            have hdivTop : (⊤ : EReal) / (t : EReal) = (⊤ : EReal) := by
              exact EReal.top_div_of_pos_ne_top (by exact_mod_cast ht') (by simp)
            rw [hstepTop, hxVal, sub_zero, hdivTop]
            exact le_top
      have hupper_le_zero :
          upperDirectionalDerivativeAt zeroJumpCounterexampleFunction
              (scalarPoint x) (scalarPoint 1) ≤ (0 : EReal) := by
        rw [(hdirRight (scalarPoint 1)).2.2]
        have hBdd :
            BddBelow
              ((Set.Ioi (0 : ℝ)).image
                fun t : ℝ =>
                  directionalDifferenceQuotientAt zeroJumpCounterexampleFunction
                    (scalarPoint x) (scalarPoint 1) t) := by
          refine ⟨⊥, ?_⟩
          intro q hq
          simp
        exact (csInf_le hBdd ⟨-x / 2, ht0, hquotZero⟩)
      have hUpperZero :
          upperDirectionalDerivativeAt zeroJumpCounterexampleFunction
              (scalarPoint x) (scalarPoint 1) = (0 : EReal) :=
        le_antisymm hupper_le_zero hzero_le
      simpa [rightDerivativeExtension, hxNot.2, hxNot.1, zeroJumpCounterexampleRightDerivative,
        hxlt] using hUpperZero
    · by_cases hx0 : x = 0
      · subst x
        have hxDom : 0 ∈ scalarEffectiveDomain zeroJumpCounterexampleFunction := by
          simpa [hscalarDom]
        have hxNot :
            ¬ IsLeftOfScalarEffectiveDomain zeroJumpCounterexampleFunction 0 ∧
              ¬ IsRightOfScalarEffectiveDomain zeroJumpCounterexampleFunction 0 :=
          helperForTheorem_5_24_1_not_left_not_right_of_mem_scalarEffectiveDomain
            zeroJumpCounterexampleFunction hxDom
        have hxFinite :
            zeroJumpCounterexampleFunction (scalarPoint 0) ≠ (⊤ : EReal) ∧
              zeroJumpCounterexampleFunction (scalarPoint 0) ≠ (⊥ : EReal) := by
          exact
            ⟨mem_effectiveDomain_imp_ne_top
                (S := (Set.univ : Set (Fin 1 → ℝ))) (f := zeroJumpCounterexampleFunction) hxDom,
              hproper.2.2 (scalarPoint 0) (by simp)⟩
        have hf : ConvexFunction zeroJumpCounterexampleFunction := by
          simpa [ConvexFunction] using hproper.1
        rcases convex_directionalDerivative_monotone_exists_and_sublinear
            zeroJumpCounterexampleFunction hf (scalarPoint 0) hxFinite with
          ⟨hdirRight, _hposRight, _hconvRight, _hzeroRight, _hsymmRight⟩
        have hone : 0 < (1 : ℝ) := zero_lt_one
        have hquotTop :
            directionalDifferenceQuotientAt zeroJumpCounterexampleFunction
                (scalarPoint 0) (scalarPoint 1) 1 = (⊤ : EReal) := by
          rw [helperForTheorem_5_24_1_directionalDifferenceQuotient_dirOne_eq_scalarSecant]
          have hstepTop :
              zeroJumpCounterexampleFunction (scalarPoint (0 + 1)) = (⊤ : EReal) := by
            norm_num [scalarPoint, zeroJumpCounterexampleFunction]
          have hxVal :
              zeroJumpCounterexampleFunction (scalarPoint 0) = (1 : EReal) := by
            norm_num [scalarPoint, zeroJumpCounterexampleFunction]
          have hsub : (⊤ : EReal) - (1 : EReal) = (⊤ : EReal) := by
            simpa using EReal.top_sub_coe (1 : ℝ)
          rw [hstepTop, hxVal, hsub]
          simpa using
            (EReal.top_div_of_pos_ne_top (by exact_mod_cast hone) (by simp) :
              (⊤ : EReal) / (1 : EReal) = (⊤ : EReal))
        have hnonempty :
            ((Set.Ioi (0 : ℝ)).image
              fun t : ℝ =>
                directionalDifferenceQuotientAt zeroJumpCounterexampleFunction
                  (scalarPoint 0) (scalarPoint 1) t).Nonempty := by
          exact ⟨⊤, ⟨1, hone, hquotTop⟩⟩
        have htop_le :
            (⊤ : EReal) ≤
              upperDirectionalDerivativeAt zeroJumpCounterexampleFunction
                (scalarPoint 0) (scalarPoint 1) := by
          rw [(hdirRight (scalarPoint 1)).2.2]
          refine le_csInf hnonempty ?_
          intro q hq
          rcases hq with ⟨t, ht, rfl⟩
          have ht' : 0 < t := by simpa using ht
          change
            (⊤ : EReal) ≤
              directionalDifferenceQuotientAt zeroJumpCounterexampleFunction
                (scalarPoint 0) (scalarPoint 1) t
          rw [helperForTheorem_5_24_1_directionalDifferenceQuotient_dirOne_eq_scalarSecant]
          have hstepTop :
              zeroJumpCounterexampleFunction (scalarPoint (0 + t)) = (⊤ : EReal) := by
            have hnotlt : ¬ t < 0 := not_lt.mpr (le_of_lt ht')
            have hne : t ≠ 0 := ne_of_gt ht'
            simp [scalarPoint, zeroJumpCounterexampleFunction, hnotlt, hne]
          have hxVal :
              zeroJumpCounterexampleFunction (scalarPoint 0) = (1 : EReal) := by
            norm_num [scalarPoint, zeroJumpCounterexampleFunction]
          have hsub : (⊤ : EReal) - (1 : EReal) = (⊤ : EReal) := by
            simpa using EReal.top_sub_coe (1 : ℝ)
          have hdivTop : (⊤ : EReal) / (t : EReal) = (⊤ : EReal) := by
            exact EReal.top_div_of_pos_ne_top (by exact_mod_cast ht') (by simp)
          rw [hstepTop, hxVal, hsub, hdivTop]
        have hUpperTop :
            upperDirectionalDerivativeAt zeroJumpCounterexampleFunction
                (scalarPoint 0) (scalarPoint 1) = (⊤ : EReal) :=
          le_antisymm le_top htop_le
        simpa [rightDerivativeExtension, hxNot.2, hxNot.1, zeroJumpCounterexampleRightDerivative]
          using hUpperTop
      · have hxle : 0 ≤ x := le_of_not_lt hxlt
        have hxgt : 0 < x := lt_of_le_of_ne hxle (Ne.symm hx0)
        have hxRight : IsRightOfScalarEffectiveDomain zeroJumpCounterexampleFunction x := by
          intro y hy
          have hyLe : y ≤ 0 := by simpa [hscalarDom] using hy
          linarith
        have hxNotLeft :
            ¬ IsLeftOfScalarEffectiveDomain zeroJumpCounterexampleFunction x :=
          helperForTheorem_5_24_1_not_left_of_right
            zeroJumpCounterexampleFunction hproper hxRight
        simp [rightDerivativeExtension, zeroJumpCounterexampleRightDerivative, hxlt, hxRight,
          hxNotLeft]
  have hTendstoZero :
      Filter.Tendsto (rightDerivativeExtension zeroJumpCounterexampleFunction)
        (nhdsWithin 0 (Set.Iio 0)) (nhds (0 : EReal)) := by
    have hEventually :
        rightDerivativeExtension zeroJumpCounterexampleFunction =ᶠ[nhdsWithin 0 (Set.Iio 0)]
          fun _ => (0 : EReal) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hzlt : z < 0 := hz
      simpa [zeroJumpCounterexampleRightDerivative, hzlt] using hRight z
    have hconst :
        Filter.Tendsto (fun _ : ℝ => (0 : EReal)) (nhdsWithin 0 (Set.Iio 0)) (nhds (0 : EReal)) :=
      tendsto_const_nhds
    simpa using hconst.congr' hEventually.symm
  have hSecantLe :
      (((1 : ℝ) : EReal)) ≤ leftDerivativeExtension zeroJumpCounterexampleFunction 0 := by
    have hxDom : (-1 : ℝ) ∈ scalarEffectiveDomain zeroJumpCounterexampleFunction := by
      norm_num [hscalarDom]
    have hyDom : (0 : ℝ) ∈ scalarEffectiveDomain zeroJumpCounterexampleFunction := by
      simpa [hscalarDom]
    have hsec :=
      (helperForTheorem_5_24_1_secantSlope_between_rightAndLeftDerivatives
        zeroJumpCounterexampleFunction hproper (by norm_num) hxDom hyDom).2
    have hxVal :
        zeroJumpCounterexampleFunction (scalarPoint (-1 : ℝ)) = (0 : EReal) := by
      norm_num [scalarPoint, zeroJumpCounterexampleFunction]
    have hyVal :
        zeroJumpCounterexampleFunction (scalarPoint 0) = (1 : EReal) := by
      norm_num [scalarPoint, zeroJumpCounterexampleFunction]
    have hsec' :
        ((zeroJumpCounterexampleFunction (scalarPoint 0) -
            zeroJumpCounterexampleFunction (scalarPoint (-1 : ℝ))) /
          (((0 - (-1 : ℝ) : ℝ)) : EReal)) ≤
          leftDerivativeExtension zeroJumpCounterexampleFunction 0 := by
      simpa using hsec
    rw [hxVal, hyVal] at hsec'
    simpa using hsec'
  have hleftNeZero :
      leftDerivativeExtension zeroJumpCounterexampleFunction 0 ≠ (0 : EReal) := by
    intro hzero
    have : (((1 : ℝ) : EReal)) ≤ (0 : EReal) := by
      simpa [hzero] using hSecantLe
    have hnot : ¬ (((1 : ℝ) : EReal) ≤ (0 : EReal)) := by norm_num
    exact hnot this
  have hLimitFail :
      ¬ Filter.Tendsto (rightDerivativeExtension zeroJumpCounterexampleFunction)
        (nhdsWithin 0 (Set.Iio 0))
        (nhds (leftDerivativeExtension zeroJumpCounterexampleFunction 0)) := by
    intro hbad
    have hnebot : (nhdsWithin (0 : ℝ) (Set.Iio 0)).NeBot := by
      exact
        (mem_closure_iff_nhdsWithin_neBot).1 (by
          rw [closure_Iio]
          simp)
    letI := hnebot
    have heq : (0 : EReal) = leftDerivativeExtension zeroJumpCounterexampleFunction 0 :=
      tendsto_nhds_unique hTendstoZero hbad
    exact hleftNeZero heq.symm
  have hnotclosed : ¬ ClosedConvexFunction zeroJumpCounterexampleFunction := by
    intro hclosed
    rcases oneDimensional_derivativeExtensions_monotone_ordered_and_oneSidedContinuous
        zeroJumpCounterexampleFunction hclosed hproper with
      ⟨_hRightMono, _hLeftMono, _hfinite, _horder, _hRightSelf, hRightLeft, _hLeftRight,
        _hLeftSelf⟩
    exact hLimitFail (hRightLeft 0)
  exact ⟨hproper, hnotclosed, hRight, hLimitFail⟩

end Section24
end Chap05

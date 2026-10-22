/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section12_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section27_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section25_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section21_part9

section Chap06
section Section27

attribute [local instance] Classical.propDecidable

/-- The infimum of an `EReal`-valued function on `ℝ^n`, written as an infimum over all points. -/
noncomputable def functionInfimumEReal {n : ℕ} (f : (Fin n → ℝ) → EReal) : EReal :=
  ⨅ x : Fin n → ℝ, f x

/-- The minimum set of an `EReal`-valued function on `ℝ^n` is the set of points where the
function attains its infimum. -/
def minimumSetEReal {n : ℕ} (f : (Fin n → ℝ) → EReal) : Set (Fin n → ℝ) :=
  {x | f x = functionInfimumEReal f}

/-- The real `α`-sublevel set of an `EReal`-valued function on `ℝ^n`. -/
def sublevelSetEReal {n : ℕ} (f : (Fin n → ℝ) → EReal) (α : ℝ) : Set (Fin n → ℝ) :=
  {x | f x ≤ (α : EReal)}

/-- The Euclideanized subdifferential consists of the vectors corresponding, via the dot-product
identification, to dual subgradients. -/
def euclideanSubdifferentialAt {n : ℕ} (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)

/-- An extended-real value is finite when it is neither `+∞` nor `-∞`. -/
def IsFiniteEReal (a : EReal) : Prop :=
  a ≠ (⊤ : EReal) ∧ a ≠ (⊥ : EReal)

/-- An `EReal`-valued function is bounded below when it admits a real lower bound. -/
def HasRealLowerBound {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  ∃ m : ℝ, ∀ x : Fin n → ℝ, (m : EReal) ≤ f x

/-- A vector is a recession direction of `f` when the recession function of `f` is nonpositive
in that direction. -/
def IsRecessionDirection {n : ℕ} (f : (Fin n → ℝ) → EReal) (y : Fin n → ℝ) : Prop :=
  recessionFunction f y ≤ (0 : EReal)

-- Route correction: the forward-ray formulation was too weak for part (b). The Chapter 13
-- criterion needed here is symmetric vanishing of the recession function in the directions `y`
-- and `-y`.
/-- A vector is a direction of constancy of `f` when the recession function vanishes in both
directions `y` and `-y`; for closed proper convex functions this is the symmetric-zero criterion
equivalent to constancy along lines parallel to `y`. -/
def IsDirectionOfConstancy {n : ℕ} (f : (Fin n → ℝ) → EReal) (y : Fin n → ℝ) : Prop :=
  recessionFunction f y = 0 ∧ recessionFunction f (-y) = 0

/-- Every recession direction of `f` is a direction of constancy. -/
def EveryRecessionDirectionIsConstant {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  ∀ y : Fin n → ℝ, IsRecessionDirection f y → IsDirectionOfConstancy f y

/-- A convex function has no recession directions when the only recession direction is `0`. -/
def HasNoRecessionDirections {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  ∀ y : Fin n → ℝ, IsRecessionDirection f y → y = 0

/-- Part (a) of Theorem 6.27.1: the infimum is `-f*(0)`, and boundedness below is equivalent to
`0` belonging to the domain of the conjugate. -/
def closedProperConvexMinimumPartA {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  functionInfimumEReal f = -fenchelConjugate n f 0 ∧
    (HasRealLowerBound f ↔
      0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))

/-- Part (b) of Theorem 6.27.1: the minimum set is the subdifferential of the conjugate at `0`,
attainment is equivalent to subdifferentiability there, and the relative-interior criterion is
equivalent to every recession direction being a direction of constancy. -/
def closedProperConvexMinimumPartB {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  minimumSetEReal f = euclideanSubdifferentialAt (fenchelConjugate n f) 0 ∧
    ((minimumSetEReal f).Nonempty ↔
      (euclideanSubdifferentialAt (fenchelConjugate n f) 0).Nonempty) ∧
    ((0 : Fin n → ℝ) ∈
        euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) →
      (euclideanSubdifferentialAt (fenchelConjugate n f) 0).Nonempty) ∧
    ((0 : Fin n → ℝ) ∈
        euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) ↔
      EveryRecessionDirectionIsConstant f)

/-- Part (c) of Theorem 6.27.1: the infimum is finite but unattained exactly when `f*(0)` is
finite and the upper directional derivative of `f*` at `0` takes the value `-∞` in some
direction. -/
def closedProperConvexMinimumPartC {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  (IsFiniteEReal (functionInfimumEReal f) ∧ ¬ (minimumSetEReal f).Nonempty) ↔
    (IsFiniteEReal (fenchelConjugate n f 0) ∧
      ∃ y : Fin n → ℝ,
        upperDirectionalDerivativeAt (fenchelConjugate n f) 0 y = (⊥ : EReal))

/-- Part (d) of Theorem 6.27.1: the minimum set is nonempty and bounded exactly when `0` lies in
the interior of `dom f*`, equivalently when `f` has no recession directions. -/
def closedProperConvexMinimumPartD {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  (((minimumSetEReal f).Nonempty ∧ Bornology.IsBounded (minimumSetEReal f)) ↔
      (0 : Fin n → ℝ) ∈
        interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))) ∧
    (((0 : Fin n → ℝ) ∈
        interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))) ↔
      HasNoRecessionDirections f)

/-- Part (e) of Theorem 6.27.1: the minimum set is a singleton `{x}` exactly when the conjugate
is differentiable at `0` with gradient `x`. -/
def closedProperConvexMinimumPartE {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  ∀ x : Fin n → ℝ,
    minimumSetEReal f = ({x} : Set (Fin n → ℝ)) ↔
      ∃ hDiff : ERealDifferentiableAt (fenchelConjugate n f) 0, x = erealGradientAt hDiff

/-- Part (f) of Theorem 6.27.1: all nonempty sublevel sets, and the minimum set when nonempty,
share the same recession cone; this common cone is the recession cone of `f`, hence also the
Euclidean polar cone of the convex cone generated by `dom f*`. -/
def closedProperConvexMinimumPartF {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  (∀ α β : ℝ,
      (sublevelSetEReal f α).Nonempty →
      (sublevelSetEReal f β).Nonempty →
      Set.recessionCone (sublevelSetEReal f α) = Set.recessionCone (sublevelSetEReal f β)) ∧
    (((minimumSetEReal f).Nonempty →
        ∀ α : ℝ,
          (sublevelSetEReal f α).Nonempty →
          Set.recessionCone (minimumSetEReal f) = Set.recessionCone (sublevelSetEReal f α))) ∧
    (∀ α : ℝ,
      (sublevelSetEReal f α).Nonempty →
      Set.recessionCone (sublevelSetEReal f α) = recessionConeEReal (F := Fin n → ℝ) f) ∧
    recessionConeEReal (F := Fin n → ℝ) f =
      euclideanPolarCone
        (((ConvexCone.hull ℝ
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))) :
            ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ))

/-- Part (g) of Theorem 6.27.1: `0` lies in the closure of `dom f*` exactly when the recession
function of `f` is everywhere nonnegative, and failure of this closure condition is equivalent to
the existence of a strict decreasing ray. -/
def closedProperConvexMinimumPartG {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  (((0 : Fin n → ℝ) ∈
      closure (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))) ↔
    ∀ y : Fin n → ℝ, (0 : EReal) ≤ recessionFunction f y) ∧
    (((0 : Fin n → ℝ) ∉
        closure (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))) ↔
      ∃ y : Fin n → ℝ, y ≠ 0 ∧
        ∃ ε : ℝ, 0 < ε ∧
          ∀ lam : ℝ, 0 ≤ lam →
            ∀ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f,
              f (x + lam • y) ≤ f x - ((lam * ε : ℝ) : EReal))

/-- Part (h) of Theorem 6.27.1: the support function of a level set is the closure of the
positively homogeneous convex function generated by `f* + α`; under a lower-bound hypothesis, the
support function of the minimum set is the closure of the directional derivative of `f*` at `0`.
-/
def closedProperConvexMinimumPartH {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  (∀ α : ℝ,
      supportFunctionEReal (sublevelSetEReal f α) =
        clConv n
          (positivelyHomogeneousConvexFunctionGenerated
            (fun y : Fin n → ℝ => fenchelConjugate n f y + (α : EReal)))) ∧
    (HasRealLowerBound f →
      supportFunctionEReal (minimumSetEReal f) =
        convexFunctionClosure (upperDirectionalDerivativeAt (fenchelConjugate n f) 0))

/-- Part (i) of Theorem 6.27.1: as the level approaches the finite infimum from above, the
support functions of the level sets converge to the directional derivative of `f*` at `0`. -/
def closedProperConvexMinimumPartI {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  IsFiniteEReal (functionInfimumEReal f) →
    ∀ y : Fin n → ℝ,
      Filter.Tendsto
        (fun α : ℝ => supportFunctionEReal (sublevelSetEReal f α) y)
        (nhdsWithin (functionInfimumEReal f).toReal
          (Set.Ioi (functionInfimumEReal f).toReal))
        (nhds (upperDirectionalDerivativeAt (fenchelConjugate n f) 0 y))

-- Proof sketch: combine the standard Fenchel-conjugate formulas for the minimum value,
-- minimizers, recession behavior, level-set support functions, and differentiability of `f*`
-- at the origin into one conjunction, keeping each textbook clause as a separate component.
/-- Helper for Theorem 6.27.1: having a real lower bound is exactly the same as the infimum
avoiding the value `-∞`. -/
lemma helperForTheorem_6_27_1_hasRealLowerBound_iff_functionInfimum_ne_bot {n : ℕ}
    (f : (Fin n → ℝ) → EReal) :
    HasRealLowerBound f ↔ functionInfimumEReal f ≠ (⊥ : EReal) := by
  constructor
  · intro hLower hInfBot
    rcases hLower with ⟨m, hm⟩
    -- A real lower bound stays below the infimum, so the infimum cannot drop to `-∞`.
    have hmInf : (m : EReal) ≤ functionInfimumEReal f := by
      simpa [functionInfimumEReal] using (le_iInf hm)
    simpa [hInfBot] using hmInf
  · intro hInfBot
    by_cases hInfTop : functionInfimumEReal f = (⊤ : EReal)
    · -- If the infimum is `+∞`, any real number is a lower bound.
      refine ⟨0, ?_⟩
      intro x
      calc
        (0 : EReal) ≤ functionInfimumEReal f := by simpa [hInfTop]
        _ ≤ f x := by simpa [functionInfimumEReal] using (iInf_le (fun y => f y) x)
    · -- Otherwise the infimum is finite, so its real part is itself a valid lower bound.
      refine ⟨(functionInfimumEReal f).toReal, ?_⟩
      intro x
      calc
        (((functionInfimumEReal f).toReal : ℝ) : EReal) = functionInfimumEReal f := by
          simpa using
            (EReal.coe_toReal (x := functionInfimumEReal f) hInfTop hInfBot)
        _ ≤ f x := by simpa [functionInfimumEReal] using (iInf_le (fun y => f y) x)

/-- Helper for Theorem 6.27.1: part (a) is the standard conjugate-at-zero formula together with
the resulting lower-bound criterion. -/
lemma helperForTheorem_6_27_1_conjugateAtZero_eq_neg_functionInfimumEReal {n : ℕ}
    (f : (Fin n → ℝ) → EReal) :
    closedProperConvexMinimumPartA f := by
  constructor
  · -- Rewrite the conjugate at `0` as the negative infimum and negate both sides.
    simpa [functionInfimumEReal] using
      (congrArg Neg.neg (fenchelConjugate_zero_eq_neg_iInf n f)).symm
  · -- Membership of `0` in `dom f*` says exactly that `f*(0) ≠ +∞`, hence `inf f ≠ -∞`.
    constructor
    · intro hLower
      have hInfBot :
          functionInfimumEReal f ≠ (⊥ : EReal) :=
        (helperForTheorem_6_27_1_hasRealLowerBound_iff_functionInfimum_ne_bot f).1 hLower
      rw [effectiveDomain_eq]
      constructor
      · simp
      · exact
          lt_top_iff_ne_top.mpr
            (by simpa [fenchelConjugate_zero_eq_neg_iInf, functionInfimumEReal] using hInfBot)
    · intro hZeroDom
      rw [effectiveDomain_eq] at hZeroDom
      have hInfBot :
          functionInfimumEReal f ≠ (⊥ : EReal) := by
        simpa [fenchelConjugate_zero_eq_neg_iInf, functionInfimumEReal] using
          (lt_top_iff_ne_top.mp hZeroDom.2)
      exact
        (helperForTheorem_6_27_1_hasRealLowerBound_iff_functionInfimum_ne_bot f).2 hInfBot

/-- Helper for Theorem 6.27.1: minimizers are exactly the points carrying the zero subgradient. -/
lemma helperForTheorem_6_27_1_mem_minimumSet_iff_zero_mem_subdifferentialAt {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) :
    x ∈ minimumSetEReal f ↔
      (0 : Module.Dual ℝ (Fin n → ℝ)) ∈ subdifferentialAt f x := by
  constructor
  · intro hx
    -- Expand minimum-set membership into the pointwise lower-bound characterization.
    have hxLower : ∀ z : Fin n → ℝ, f x ≤ f z := by
      intro z
      rw [minimumSetEReal] at hx
      rw [hx]
      exact iInf_le (fun y => f y) z
    -- For the zero functional, the subgradient inequality is exactly `f x ≤ f z`.
    intro z
    simpa [subdifferentialAt, IsSubgradientAt] using hxLower z
  · intro hx
    -- A zero subgradient makes `f x` a lower bound for every value, hence equal to the infimum.
    have hxLower : ∀ z : Fin n → ℝ, f x ≤ f z := by
      intro z
      have hz : f z ≥ f x + ((0 : Module.Dual ℝ (Fin n → ℝ)) (z - x) : ℝ) := hx z
      simpa [subdifferentialAt, IsSubgradientAt] using hz
    rw [minimumSetEReal]
    apply le_antisymm
    · exact le_iInf hxLower
    · exact iInf_le (fun y => f y) x

/-- Helper for Theorem 6.27.1: the minimum set is the Euclideanized subdifferential fiber of the
conjugate at the origin. -/
lemma helperForTheorem_6_27_1_minimumSet_eq_euclideanSubdifferentialAt_conjugate_zero {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    minimumSetEReal f = euclideanSubdifferentialAt (fenchelConjugate n f) 0 := by
  ext x
  constructor
  · intro hx
    -- Move from `x ∈ argmin f` to the zero-subgradient condition on `f`.
    have hxSub :
        (0 : Module.Dual ℝ (Fin n → ℝ)) ∈ subdifferentialAt f x :=
      (helperForTheorem_6_27_1_mem_minimumSet_iff_zero_mem_subdifferentialAt f x).1 hx
    have hxEuclidean :
        IsEuclideanSubgradientAt f x (0 : Fin n → ℝ) := by
      simpa [IsEuclideanSubgradientAt] using hxSub
    -- Corollary 23.5.1 transports that zero subgradient to the conjugate fiber at the origin.
    have hxConj :
        IsEuclideanSubgradientAt (fenchelConjugate n f) 0 x :=
      (euclidean_subgradient_fenchelConjugate_iff
        (f := f) hclosed hproper x (0 : Fin n → ℝ)).2 hxEuclidean
    simpa [euclideanSubdifferentialAt, IsEuclideanSubgradientAt] using hxConj
  · intro hx
    -- Read membership in the Euclidean fiber back as a zero subgradient of `f` at `x`.
    have hxConj :
        IsEuclideanSubgradientAt (fenchelConjugate n f) 0 x := by
      simpa [euclideanSubdifferentialAt, IsEuclideanSubgradientAt] using hx
    have hxEuclidean :
        IsEuclideanSubgradientAt f x (0 : Fin n → ℝ) :=
      (euclidean_subgradient_fenchelConjugate_iff
        (f := f) hclosed hproper x (0 : Fin n → ℝ)).1 hxConj
    have hxSub :
        (0 : Module.Dual ℝ (Fin n → ℝ)) ∈ subdifferentialAt f x := by
      simpa [IsEuclideanSubgradientAt] using hxEuclidean
    exact
      (helperForTheorem_6_27_1_mem_minimumSet_iff_zero_mem_subdifferentialAt f x).2 hxSub

/-- Helper for Theorem 6.27.1: relative-interior membership in `dom f*` gives a nonempty
Euclideanized subdifferential fiber at the origin. -/
lemma helperForTheorem_6_27_1_zeroFiber_nonempty_of_mem_relativeInterior {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    (0 : Fin n → ℝ) ∈
        euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) →
      (euclideanSubdifferentialAt f 0).Nonempty := by
  intro hri
  -- Remark 5.24.1 turns relative-interior points into actual subdifferentiability.
  have hSubEff :
      (0 : Fin n → ℝ) ∈ subdifferentialEffectiveDomain f :=
    (relativeInterior_subset_subdifferentialEffectiveDomain_subset_effectiveDomain
      (f := f) hproper).1 hri
  rcases
      (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty f 0).1 hSubEff with
    ⟨g, hg⟩
  refine ⟨(dotProductEquiv ℝ (Fin n)).symm g, ?_⟩
  simpa [euclideanSubdifferentialAt] using hg

/-- Helper for Theorem 6.27.1: the nonempty boundedness criterion in part (d) is exactly the
Chapter 23 interior criterion applied to the conjugate at `0`. -/
lemma helperForTheorem_6_27_1_minimumSet_nonempty_bounded_iff_zero_mem_interior_dom_conjugate
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    (((minimumSetEReal f).Nonempty ∧ Bornology.IsBounded (minimumSetEReal f)) ↔
      (0 : Fin n → ℝ) ∈
        interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))) := by
  let fStar : (Fin n → ℝ) → EReal := fenchelConjugate n f
  have hproperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) fStar :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
  have hMinEq :
      minimumSetEReal f = euclideanSubdifferentialAt fStar 0 :=
    helperForTheorem_6_27_1_minimumSet_eq_euclideanSubdifferentialAt_conjugate_zero
      f hclosed hproper
  have h23_4 :=
    subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
      fStar hproperStar 0
  have hNonemptyEq :
      Set.Nonempty (subdifferentialAt fStar 0) ↔
        (euclideanSubdifferentialAt fStar 0).Nonempty := by
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨(dotProductEquiv ℝ (Fin n)).symm g, by simpa [euclideanSubdifferentialAt] using hg⟩
    · rintro ⟨x, hx⟩
      exact ⟨dotProductEquiv ℝ (Fin n) x, by simpa [euclideanSubdifferentialAt] using hx⟩
  constructor
  · rintro ⟨hMinNonempty, hMinBounded⟩
    have hEuclideanNonempty : (euclideanSubdifferentialAt fStar 0).Nonempty := by
      simpa [hMinEq] using hMinNonempty
    have hFiberNonempty : Set.Nonempty (subdifferentialAt fStar 0) := hNonemptyEq.2 hEuclideanNonempty
    have hFiberBounded :
        Bornology.IsBounded ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt fStar 0) := by
      simpa [euclideanSubdifferentialAt, hMinEq] using hMinBounded
    exact (h23_4.2.2.1).1 ⟨hFiberNonempty, hFiberBounded⟩
  · intro hInt
    rcases (h23_4.2.2.1).2 hInt with ⟨hFiberNonempty, hFiberBounded⟩
    exact ⟨by simpa [hMinEq] using (hNonemptyEq.1 hFiberNonempty), by
      simpa [euclideanSubdifferentialAt, hMinEq] using hFiberBounded⟩

/-- Helper for Theorem 6.27.1: part (c) is the empty-fiber alternative from Theorem 23.3,
applied to the conjugate at the origin and rewritten through parts (a) and (b). -/
lemma helperForTheorem_6_27_1_finite_unattained_iff_conjugate_zero_finite_and_bot_directional
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    closedProperConvexMinimumPartC f := by
  let fStar : (Fin n → ℝ) → EReal := fenchelConjugate n f
  have hA := helperForTheorem_6_27_1_conjugateAtZero_eq_neg_functionInfimumEReal f
  have hMinEq :
      minimumSetEReal f = euclideanSubdifferentialAt fStar 0 :=
    helperForTheorem_6_27_1_minimumSet_eq_euclideanSubdifferentialAt_conjugate_zero
      f hclosed hproper
  have hproperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) fStar :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
  have hconvStar : ConvexFunction fStar := by
    simpa [fStar, ConvexFunction] using hproperStar.1
  have hfiniteIff : IsFiniteEReal (functionInfimumEReal f) ↔ IsFiniteEReal (fStar 0) := by
    -- Negation preserves finiteness, so part (a) converts the two finiteness statements.
    constructor
    · intro hFinite
      exact ⟨by simpa [fStar, hA.1] using hFinite.2, by simpa [fStar, hA.1] using hFinite.1⟩
    · intro hFinite
      exact ⟨by simpa [fStar, hA.1] using hFinite.2, by simpa [fStar, hA.1] using hFinite.1⟩
  have hSubNonempty :
      (minimumSetEReal f).Nonempty ↔ Set.Nonempty (subdifferentialAt fStar 0) := by
    constructor
    · rintro ⟨x, hx⟩
      have hx' : x ∈ euclideanSubdifferentialAt fStar 0 := by simpa [hMinEq] using hx
      exact ⟨dotProductEquiv ℝ (Fin n) x, by simpa [euclideanSubdifferentialAt] using hx'⟩
    · rintro ⟨g, hg⟩
      refine ⟨(dotProductEquiv ℝ (Fin n)).symm g, ?_⟩
      have hg' : (dotProductEquiv ℝ (Fin n)).symm g ∈ euclideanSubdifferentialAt fStar 0 := by
        simpa [euclideanSubdifferentialAt] using hg
      simpa [hMinEq] using hg'
  constructor
  · rintro ⟨hInfFinite, hNoMin⟩
    have hStarFinite : IsFiniteEReal (fStar 0) := hfiniteIff.1 hInfFinite
    have hNoSub : ¬ Set.Nonempty (subdifferentialAt fStar 0) := by
      intro hSub
      exact hNoMin (hSubNonempty.2 hSub)
    -- Theorem 23.3 supplies a `-∞` directional derivative exactly when the fiber is empty.
    rcases
        (proper_of_subdifferentiableAt_or_infiniteDirectionalDerivative_to_relativeInterior
          fStar hconvStar 0 hStarFinite).2 hNoSub with
      ⟨⟨y, hyBot, _hyTop⟩, _⟩
    exact ⟨hStarFinite, y, hyBot⟩
  · rintro ⟨hStarFinite, y, hyBot⟩
    have hNoSub : ¬ Set.Nonempty (subdifferentialAt fStar 0) := by
      intro hSub
      rcases hSub with ⟨g, hg⟩
      have hminor :
          (((g y : ℝ) : EReal)) ≤ upperDirectionalDerivativeAt fStar 0 y :=
        le_upperDirectionalDerivative_of_mem_subdifferential fStar hproperStar g hg y
      have : (((g y : ℝ) : EReal)) ≤ (⊥ : EReal) := by
        rw [hyBot] at hminor
        exact hminor
      exact (EReal.bot_lt_coe (g y)).not_ge this
    exact ⟨hfiniteIff.2 hStarFinite, by
      intro hMin
      exact hNoSub (hSubNonempty.1 hMin)⟩

/-- Helper for Theorem 6.27.1: a singleton minimum set is equivalent to differentiability of the
conjugate at `0` with the singleton point as gradient. -/
lemma helperForTheorem_6_27_1_singleton_minimumSet_iff_differentiableAt_conjugate_zero {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    closedProperConvexMinimumPartE f := by
  intro x
  let fStar : (Fin n → ℝ) → EReal := fenchelConjugate n f
  have hMinEq :
      minimumSetEReal f = euclideanSubdifferentialAt fStar 0 :=
    helperForTheorem_6_27_1_minimumSet_eq_euclideanSubdifferentialAt_conjugate_zero
      f hclosed hproper
  have hproperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) fStar :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
  have hconvStar : ConvexFunction fStar := by
    simpa [fStar, ConvexFunction] using hproperStar.1
  constructor
  · intro hMinSingleton
    -- Rewrite the singleton minimum-set hypothesis as a singleton subgradient fiber at `0`.
    have hxMin : x ∈ minimumSetEReal f := by
      simpa [hMinSingleton]
    have hxFiber : x ∈ euclideanSubdifferentialAt fStar 0 := by
      simpa [hMinEq] using hxMin
    have hxSub : dotProductEquiv ℝ (Fin n) x ∈ subdifferentialAt fStar 0 := by
      simpa [euclideanSubdifferentialAt] using hxFiber
    have h0SubEff : (0 : Fin n → ℝ) ∈ subdifferentialEffectiveDomain fStar := by
      exact
        (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty fStar 0).2
          ⟨dotProductEquiv ℝ (Fin n) x, hxSub⟩
    have h0Dom :
        (0 : Fin n → ℝ) ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar :=
      helperForRemark_5_24_1_mem_effectiveDomain_of_subdifferentiable fStar hproperStar h0SubEff
    have h0Finite : fStar 0 ≠ (⊤ : EReal) ∧ fStar 0 ≠ (⊥ : EReal) := by
      constructor
      · rw [effectiveDomain_eq] at h0Dom
        exact lt_top_iff_ne_top.mp h0Dom.2
      · exact hproperStar.2.2 0 (by simp)
    have hUnique :
        ∃! g : Fin n → ℝ, IsSubgradientAt fStar 0 (dotProductEquiv ℝ (Fin n) g) := by
      refine ⟨x, ?_, ?_⟩
      · simpa using hxSub
      · intro g hg
        have hgFiber : g ∈ euclideanSubdifferentialAt fStar 0 := by
          simpa [euclideanSubdifferentialAt] using hg
        have hgMin : g ∈ minimumSetEReal f := by
          simpa [hMinEq] using hgFiber
        simpa [hMinSingleton] using hgMin
    -- The unique Euclidean subgradient is therefore the gradient supplied by differentiability.
    let hDiff : ERealDifferentiableAt fStar 0 :=
      (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
        fStar hconvStar 0 h0Finite).2 hUnique
    have hGradEq : x = erealGradientAt hDiff := by
      exact
        (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
          fStar hconvStar 0 h0Finite).1 hDiff |>.2.2 x (by simpa using hxSub)
    exact ⟨hDiff, hGradEq⟩
  · rintro ⟨hDiff, hxGrad⟩
    have h0Finite : fStar 0 ≠ (⊤ : EReal) ∧ fStar 0 ≠ (⊥ : EReal) :=
      ERealDifferentiableAt.finiteAt hDiff
    have hDiffPack :=
      (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
        fStar hconvStar 0 h0Finite).1 hDiff
    have hFiberSingleton : euclideanSubdifferentialAt fStar 0 = ({x} : Set (Fin n → ℝ)) := by
      ext z
      constructor
      · intro hz
        have hzSub : IsSubgradientAt fStar 0 (dotProductEquiv ℝ (Fin n) z) := by
          simpa [euclideanSubdifferentialAt] using hz
        have hzEqGrad : z = erealGradientAt hDiff := hDiffPack.2.2 z hzSub
        simpa [hxGrad] using hzEqGrad
      · intro hz
        rcases Set.mem_singleton_iff.1 hz with rfl
        simpa [euclideanSubdifferentialAt, hxGrad] using hDiffPack.1
    simpa [hMinEq] using hFiberSingleton

/-- Helper for Theorem 6.27.1: under a lower-bound hypothesis, the support function of the
minimum set is the closed directional derivative of the conjugate at `0`. -/
lemma helperForTheorem_6_27_1_support_minimumSet_eq_closure_directionalDerivative
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    HasRealLowerBound f →
      supportFunctionEReal (minimumSetEReal f) =
        convexFunctionClosure (upperDirectionalDerivativeAt (fenchelConjugate n f) 0) := by
  intro hLower
  let fStar : (Fin n → ℝ) → EReal := fenchelConjugate n f
  have hA := helperForTheorem_6_27_1_conjugateAtZero_eq_neg_functionInfimumEReal f
  have hMinEq :
      minimumSetEReal f = euclideanSubdifferentialAt fStar 0 :=
    helperForTheorem_6_27_1_minimumSet_eq_euclideanSubdifferentialAt_conjugate_zero
      f hclosed hproper
  have hproperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) fStar :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
  have hconvStar : ConvexFunction fStar := by
    simpa [fStar, ConvexFunction] using hproperStar.1
  have h0Dom :
      (0 : Fin n → ℝ) ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar :=
    hA.2.1 hLower
  have h0Finite : fStar 0 ≠ (⊤ : EReal) ∧ fStar 0 ≠ (⊥ : EReal) := by
    constructor
    · rw [effectiveDomain_eq] at h0Dom
      exact lt_top_iff_ne_top.mp h0Dom.2
    · exact hproperStar.2.2 0 (by simp)
  have h23_2 :=
    subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
      fStar hconvStar 0 h0Finite (0 : Module.Dual ℝ (Fin n → ℝ))
  have hSupportEq :
      supportFunctionEReal (minimumSetEReal f) = subdifferentialSupportAt fStar 0 := by
    funext y
    calc
      supportFunctionEReal (minimumSetEReal f) y =
          supportFunctionEReal (euclideanSubdifferentialAt fStar 0) y := by
            simpa [hMinEq]
      _ = subdifferentialSupportAt fStar 0 y := by
            simpa [euclideanSubdifferentialAt] using
              helperForTheorem_23_2_supportFunctionEReal_preimage_subdifferential_eq fStar 0 y
  -- Theorem 23.2 identifies the support of the `0`-fiber with the closure of the derivative.
  calc
    supportFunctionEReal (minimumSetEReal f) =
        subdifferentialSupportAt fStar 0 := hSupportEq
    _ = convexFunctionClosure (upperDirectionalDerivativeAt fStar 0) := by
        symm
        exact h23_2.2.2.2
    _ = convexFunctionClosure (upperDirectionalDerivativeAt (fenchelConjugate n f) 0) := by
        rfl

/-- Helper for Theorem 6.27.1: symmetric zero recession in directions `y` and `-y` is exactly
the repaired direction-of-constancy predicate. -/
lemma helperForTheorem_6_27_1_constancy_of_symmetric_zero_recession {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (y : Fin n → ℝ)
    (hy : recessionFunction f y = 0)
    (hneg : recessionFunction f (-y) = 0) :
    IsDirectionOfConstancy f y := by
  -- The repaired predicate is the symmetric-zero recession package itself.
  let _ := hclosed
  let _ := hproper
  exact ⟨hy, hneg⟩

/-- Helper for Theorem 6.27.1: a strictly negative recession value can be bounded above by
`-ε` for some positive real `ε`. -/
lemma helperForTheorem_6_27_1_exists_positive_real_below_negative_recession {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (y : Fin n → ℝ)
    (hy : recessionFunction f y < (0 : EReal)) :
    ∃ ε : ℝ, 0 < ε ∧ recessionFunction f y ≤ ((-ε : ℝ) : EReal) := by
  by_cases hbot : recessionFunction f y = (⊥ : EReal)
  · refine ⟨1, by norm_num, ?_⟩
    simpa [hbot]
  · have htop : recessionFunction f y ≠ (⊤ : EReal) :=
      ne_of_lt (lt_trans hy (by simp))
    lift recessionFunction f y to ℝ using ⟨htop, hbot⟩ with r hr
    have hrneg : r < 0 := by
      exact EReal.coe_lt_coe_iff.mp (by simpa [hr] using hy)
    refine ⟨-r, by linarith, ?_⟩
    simpa [hr]

/-- Helper for Theorem 6.27.1: transporting relative interior through
`EuclideanSpace.equiv` identifies `euclideanRelativeInterior_fin` with `intrinsicInterior`
on `Fin n → ℝ`. -/
lemma helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior {n : ℕ}
    (C : Set (Fin n → ℝ)) :
    euclideanRelativeInterior_fin n C = intrinsicInterior ℝ C := by
  classical
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
  let CE : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' C
  have hCe : e '' CE = C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨z, hz, hzy⟩
      have : e y = z := by
        simpa using congrArg e hzy.symm
      simpa [this] using hz
    · intro hx
      exact ⟨e.symm x, by simpa [CE] using hx, by simp⟩
  have hIntrinsic :
      intrinsicInterior ℝ C = e '' intrinsicInterior ℝ CE := by
    -- Move intrinsic interior across the Euclidean linear equivalence.
    simpa [CE, hCe] using (ContinuousLinearEquiv.image_intrinsicInterior (e := e) (s := CE))
  ext x
  constructor
  · intro hx
    -- Convert the transported Euclidean relative-interior witness to intrinsic interior.
    rcases hx with ⟨y, hy, rfl⟩
    have hyIntrinsic : y ∈ intrinsicInterior ℝ CE :=
      euclideanRelativeInterior_subset_intrinsicInterior n CE hy
    have hxIntrinsicImage : e y ∈ e '' intrinsicInterior ℝ CE := ⟨y, hyIntrinsic, rfl⟩
    simpa [euclideanRelativeInterior_fin, e, CE, hIntrinsic] using hxIntrinsicImage
  · intro hx
    -- Convert intrinsic interior back to the transported Euclidean relative interior.
    have hxIntrinsicImage : x ∈ e '' intrinsicInterior ℝ CE := by
      simpa [hIntrinsic] using hx
    rcases hxIntrinsicImage with ⟨y, hyIntrinsic, rfl⟩
    have hy : y ∈ euclideanRelativeInterior n CE :=
      intrinsicInterior_subset_euclideanRelativeInterior n CE hyIntrinsic
    exact ⟨y, hy, rfl⟩

lemma helperForTheorem_6_27_1_relativeInterior_iff_everyRecessionDirectionIsConstant {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    ((0 : Fin n → ℝ) ∈
        euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) ↔
      EveryRecessionDirectionIsConstant f) := by
  let domFstar : Set (Fin n → ℝ) :=
    effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)
  let h13 :=
    mem_closure_ri_interior_affineSpan_effectiveDomain_fenchelConjugate_iff_recessionFunction
      (f := f) hclosed hproper (0 : Fin n → ℝ)
  rcases h13 with ⟨_hclosure, hriIntrinsicRaw, _hinterior, _haff⟩
  have hshift :
      (fun x : Fin n → ℝ => f x - ((dotProduct x (0 : Fin n → ℝ) : ℝ) : EReal)) = f := by
    -- At `xStar = 0`, the translated function in the Chapter 13 criterion is just `f`.
    funext x
    simp
  have hriIntrinsic :
      ((0 : Fin n → ℝ) ∈ intrinsicInterior ℝ domFstar ↔
        ∀ y : Fin n → ℝ,
          (¬ (-(recessionFunction f (-y)) = recessionFunction f y ∧
                recessionFunction f y = 0)) →
            recessionFunction f y > 0) := by
    -- Rewrite the Chapter 13 criterion at the origin so it refers directly to `f`.
    simpa only [domFstar, hshift] using hriIntrinsicRaw
  rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior]
  constructor
  · intro hri y hyRec
    -- A recession direction cannot trigger the strictly-positive alternative, so the
    -- symmetric-zero criterion must hold.
    have hCrit :
        -(recessionFunction f (-y)) = recessionFunction f y ∧ recessionFunction f y = 0 := by
      by_contra hNotCrit
      exact (hriIntrinsic.1 hri y hNotCrit).not_ge hyRec
    have hnegZero : recessionFunction f (-y) = 0 := by
      have hneg : -(recessionFunction f (-y)) = (0 : EReal) := by
        simpa [hCrit.2] using hCrit.1
      have := congrArg Neg.neg hneg
      simpa using this
    exact ⟨hCrit.2, hnegZero⟩
  · intro hConst
    refine hriIntrinsic.2 ?_
    intro y hNotCrit
    by_cases hyPos : recessionFunction f y > 0
    · exact hyPos
    · -- If the recession value is not positive, then `y` is a recession direction and hence,
      -- by hypothesis, a symmetric-zero direction of constancy.
      have hyRec : IsRecessionDirection f y := by
        unfold IsRecessionDirection
        exact le_of_not_gt hyPos
      have hyConst : IsDirectionOfConstancy f y := hConst y hyRec
      have hCrit :
          -(recessionFunction f (-y)) = recessionFunction f y ∧ recessionFunction f y = 0 := by
        refine ⟨?_, hyConst.1⟩
        simpa [hyConst.1, hyConst.2]
      exact False.elim (hNotCrit hCrit)

/-- Helper for Theorem 6.27.1: the remaining no-recession-directions clause in part (d) still
needs the polar/recession cone package from Chapter 14 specialized to `dom f*`. -/
-- TODO: combine the polar description of `recessionConeEReal f` with the `0 ∈ int (dom f*)`
-- criterion to rewrite interior membership as triviality of the recession cone.
lemma helperForTheorem_6_27_1_zero_mem_interior_iff_hasNoRecessionDirections {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    (((0 : Fin n → ℝ) ∈
        interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))) ↔
      HasNoRecessionDirections f) := by
  let domFstar : Set (Fin n → ℝ) :=
    effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)
  have h13 :=
    mem_closure_ri_interior_affineSpan_effectiveDomain_fenchelConjugate_iff_recessionFunction
      (f := f) hclosed hproper (0 : Fin n → ℝ)
  have hinterior :
      ((0 : Fin n → ℝ) ∈ interior domFstar ↔
        ∀ y : Fin n → ℝ, y ≠ 0 → recessionFunction f y > 0) := by
    simpa [domFstar] using h13.2.2.1
  constructor
  · intro hInt y hyRec
    by_contra hyNe
    have hyPos : recessionFunction f y > 0 := (hinterior.1 hInt) y hyNe
    exact hyPos.not_ge hyRec
  · intro hNoRec
    refine hinterior.2 ?_
    intro y hyNe
    by_contra hyNotPos
    have hyRec : IsRecessionDirection f y := by
      unfold IsRecessionDirection
      exact le_of_not_gt hyNotPos
    exact hyNe (hNoRec y hyRec)

/-- Helper for Theorem 6.27.1: when the infimum is attained, the minimum set agrees with the real
sublevel set at the attained infimum value. -/
lemma helperForTheorem_6_27_1_minimumSet_eq_realSublevel_at_infimum_of_attainment {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hMin : (minimumSetEReal f).Nonempty) :
    minimumSetEReal f = sublevelSetEReal f (functionInfimumEReal f).toReal := by
  rcases hMin with ⟨x0, hx0⟩
  have hInf_ne_bot : functionInfimumEReal f ≠ (⊥ : EReal) := by
    -- A minimizing point lies in the effective domain, so the attained infimum is not `-∞`.
    rw [minimumSetEReal] at hx0
    have hx0_ne_bot : f x0 ≠ (⊥ : EReal) := hproper.2.2 x0 (by simp)
    intro hbot
    have : f x0 = (⊥ : EReal) := by
      exact hx0.trans hbot
    exact hx0_ne_bot this
  have hInf_ne_top : functionInfimumEReal f ≠ (⊤ : EReal) := by
    -- Properness supplies one finite value, hence the infimum is below `+∞`.
    rcases hproper.2.1 with ⟨⟨x1, μ1⟩, hx1μ1⟩
    have hInf_le : functionInfimumEReal f ≤ f x1 := by
      simpa [functionInfimumEReal] using (iInf_le (fun y => f y) x1)
    exact lt_top_iff_ne_top.mp (lt_of_le_of_lt hInf_le (lt_of_le_of_lt hx1μ1.2 (by simp)))
  have hInf_coe :
      (((functionInfimumEReal f).toReal : ℝ) : EReal) = functionInfimumEReal f := by
    simpa using (EReal.coe_toReal (x := functionInfimumEReal f) hInf_ne_top hInf_ne_bot)
  ext x
  constructor
  · intro hx
    -- A minimizer automatically belongs to the sublevel at the attained infimum.
    rw [minimumSetEReal] at hx
    rw [sublevelSetEReal]
    change f x ≤ (((functionInfimumEReal f).toReal : ℝ) : EReal)
    rw [hx, hInf_coe]
  · intro hx
    -- The infimum is always a lower bound, so the sublevel inequality forces equality.
    rw [minimumSetEReal]
    have hInf_le_fx : functionInfimumEReal f ≤ f x := by
      simpa [functionInfimumEReal] using (iInf_le (fun y => f y) x)
    exact le_antisymm (by simpa [sublevelSetEReal, hInf_coe] using hx) hInf_le_fx

/-- Helper for Theorem 6.27.1: all nonempty real sublevel sets, and the minimum set when
nonempty, share the common recession cone `recessionConeEReal f`; that cone is the Euclidean
polar cone of the convex cone generated by `dom f*`. -/
lemma helperForTheorem_6_27_1_recessionCone_and_polar_bridges {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    closedProperConvexMinimumPartF f := by
  let domFstar : Set (Fin n → ℝ) :=
    effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)
  have hfProperEReal :
      ProperConvexERealFunction (F := (Fin n → ℝ)) f :=
    helperForTheorem_21_3_properConvexEReal_of_properConvexFunctionOn_univ (f := f) hproper
  have hSublevelRec :
      ∀ α : ℝ,
        (sublevelSetEReal f α).Nonempty →
          Set.recessionCone (sublevelSetEReal f α) = recessionConeEReal (F := Fin n → ℝ) f := by
    intro α hα
    -- Every nonempty real sublevel has the same recession cone, namely `recessionConeEReal f`.
    apply Set.Subset.antisymm
    · simpa [sublevelSetEReal] using
        section14_recessionCone_sublevel_subset_recessionConeEReal
          (E := Fin n → ℝ) (f := f) hfProperEReal hclosed.2 (α := α) hα
    · simpa [sublevelSetEReal] using
        section14_recessionConeEReal_subset_recessionCone_sublevel
          (E := Fin n → ℝ) (f := f) hfProperEReal.2 (α := α)
  have hsupp_eq :
      supportFunctionEReal domFstar = recessionFunction f := by
    simpa [domFstar] using
      section13_supportFunctionEReal_dom_fenchelConjugate_eq_recessionFunction
        (n := n) (f := f) hclosed hproper
  have hPolar :
      recessionConeEReal (F := Fin n → ℝ) f =
        euclideanPolarCone
          (((ConvexCone.hull ℝ domFstar) : ConvexCone ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    ext y
    constructor
    · intro hy
      have hrecE_le : recessionFunctionEReal (F := Fin n → ℝ) f y ≤ (0 : EReal) := by
        simpa [recessionConeEReal] using hy
      have hrec_le : recessionFunction f y ≤ (0 : EReal) := by
        simpa [recessionFunctionEReal, recessionFunction, erealDom, effectiveDomain_eq] using hrecE_le
      have hsupp_le : supportFunctionEReal domFstar y ≤ (0 : EReal) := by
        calc
          supportFunctionEReal domFstar y = recessionFunction f y := congrArg (fun g => g y) hsupp_eq
          _ ≤ (0 : EReal) := hrec_le
      have hdom_nonpos : ∀ x ∈ domFstar, dotProduct x y ≤ 0 := by
        exact (section13_supportFunctionEReal_le_coe_iff (C := domFstar) (y := y) (μ := 0)).1 hsupp_le
      have hHull_le :
          (ConvexCone.hull ℝ domFstar : ConvexCone ℝ (Fin n → ℝ)) ≤
            nonposCone (E := Fin n → ℝ) (dotProductEquiv ℝ (Fin n) y) := by
        refine
          (ConvexCone.hull_le_iff
            (C := nonposCone (E := Fin n → ℝ) (dotProductEquiv ℝ (Fin n) y))
            (s := domFstar)).2 ?_
        intro x hx
        change (dotProductEquiv ℝ (Fin n) y) x ≤ 0
        simpa [dotProduct_comm] using hdom_nonpos x hx
      intro x hx
      have hxNonpos :
          x ∈ (nonposCone (E := Fin n → ℝ) (dotProductEquiv ℝ (Fin n) y) : Set (Fin n → ℝ)) :=
        hHull_le hx
      change (dotProductEquiv ℝ (Fin n) y) x ≤ 0 at hxNonpos
      simpa [dotProduct_comm] using hxNonpos
    · intro hy
      have hdom_nonpos : ∀ x ∈ domFstar, dotProduct x y ≤ 0 := by
        intro x hx
        exact hy x (ConvexCone.subset_hull (R := ℝ) (s := domFstar) hx)
      have hsupp_le : supportFunctionEReal domFstar y ≤ (0 : EReal) := by
        exact
          (section13_supportFunctionEReal_le_coe_iff (C := domFstar) (y := y) (μ := 0)).2
            hdom_nonpos
      have hrec_le : recessionFunction f y ≤ (0 : EReal) := by
        calc
          recessionFunction f y = supportFunctionEReal domFstar y := (congrArg (fun g => g y) hsupp_eq).symm
          _ ≤ (0 : EReal) := hsupp_le
      have hrecE_le : recessionFunctionEReal (F := Fin n → ℝ) f y ≤ (0 : EReal) := by
        simpa [recessionFunctionEReal, recessionFunction, erealDom, effectiveDomain_eq] using hrec_le
      simpa [recessionConeEReal] using hrecE_le
  refine ⟨?_, ?_, ?_, hPolar⟩
  · intro α β hα hβ
    -- Transport both recession cones to `recessionConeEReal f` and compare there.
    rw [hSublevelRec α hα, hSublevelRec β hβ]
  · intro hMin α hα
    -- The minimum set is the sublevel at the attained infimum, so it shares the same cone.
    rw [helperForTheorem_6_27_1_minimumSet_eq_realSublevel_at_infimum_of_attainment
      (f := f) hproper hMin]
    calc
      Set.recessionCone (sublevelSetEReal f (functionInfimumEReal f).toReal)
          = recessionConeEReal (F := Fin n → ℝ) f :=
            hSublevelRec (functionInfimumEReal f).toReal (by
              simpa [helperForTheorem_6_27_1_minimumSet_eq_realSublevel_at_infimum_of_attainment
                (f := f) hproper hMin] using hMin)
      _ = Set.recessionCone (sublevelSetEReal f α) := (hSublevelRec α hα).symm
  · intro α hα
    exact hSublevelRec α hα

/-- Helper for Theorem 6.27.1: a negative recession bound at `y` scales to every positive multiple
of `y`, and that scaled bound yields a uniform strict decrease along the ray `x + λ y`. -/
lemma helperForTheorem_6_27_1_negative_recession_bound_implies_strict_decreasing_ray {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (y : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hy : recessionFunction f y ≤ ((-ε : ℝ) : EReal)) :
    ∀ lam : ℝ, 0 ≤ lam →
      ∀ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f,
        f (x + lam • y) ≤ f x - ((lam * ε : ℝ) : EReal) := by
  let domFstar : Set (Fin n → ℝ) :=
    effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)
  have hproperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
  have hCne : domFstar.Nonempty :=
    section13_effectiveDomain_nonempty_of_proper (n := n) (f := fenchelConjugate n f) hproperStar
  have hCconv : Convex ℝ domFstar := by
    have hconvStar : ConvexFunction (fenchelConjugate n f) :=
      (fenchelConjugate_closedConvex (n := n) (f := f)).2
    have hconvOn :
        ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) := by
      simpa [ConvexFunction] using hconvStar
    simpa [domFstar] using
      (effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ)))
        (f := fenchelConjugate n f) (hf := hconvOn))
  have hsupp_eq :
      supportFunctionEReal domFstar = recessionFunction f := by
    simpa [domFstar] using
      section13_supportFunctionEReal_dom_fenchelConjugate_eq_recessionFunction
        (n := n) (f := f) hclosed hproper
  have hposHom :
      PositivelyHomogeneous (supportFunctionEReal domFstar) :=
    (section13_supportFunctionEReal_closedProperConvex_posHom
      (n := n) (C := domFstar) hCne hCconv).2.2
  intro lam hlam x hx
  by_cases hlam_zero : lam = 0
  · -- At `λ = 0`, the ray inequality is tautological.
    simp [hlam_zero]
  · have hlam_pos : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hlam_zero)
    have hscaled :
        recessionFunction f (lam • y) ≤ ((-(lam * ε) : ℝ) : EReal) := by
      calc
        recessionFunction f (lam • y) = supportFunctionEReal domFstar (lam • y) := by
          exact (congrArg (fun g => g (lam • y)) hsupp_eq).symm
        _ = ((lam : ℝ) : EReal) * supportFunctionEReal domFstar y := by
          simpa using hposHom y lam hlam_pos
        _ = ((lam : ℝ) : EReal) * recessionFunction f y := by
          simp [congrArg (fun g => g y) hsupp_eq]
        _ ≤ ((lam : ℝ) : EReal) * (((-ε : ℝ) : EReal)) := by
          exact mul_le_mul_of_nonneg_left hy (by exact_mod_cast le_of_lt hlam_pos)
        _ = ((-(lam * ε) : ℝ) : EReal) := by
          simp [mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg]
    have hdiff :
        f (x + lam • y) - f x ≤ recessionFunction f (lam • y) := by
      exact le_sSup ⟨x, hx, rfl⟩
    have hx_top_lt : f x < (⊤ : EReal) := by
      simpa [effectiveDomain_eq] using hx
    have hx_top : f x ≠ (⊤ : EReal) := lt_top_iff_ne_top.mp hx_top_lt
    have hx_bot : f x ≠ (⊥ : EReal) := hproper.2.2 x (by simp)
    have hle_add :
        f (x + lam • y) ≤ recessionFunction f (lam • y) + f x :=
      (EReal.sub_le_iff_le_add
        (a := f (x + lam • y)) (b := f x) (c := recessionFunction f (lam • y))
        (Or.inl hx_bot) (Or.inl hx_top)).1 hdiff
    calc
      f (x + lam • y) ≤ recessionFunction f (lam • y) + f x := hle_add
      _ ≤ ((-(lam * ε) : ℝ) : EReal) + f x := by
            simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hscaled (f x)
      _ = f x - ((lam * ε : ℝ) : EReal) := by
            simp [add_comm, sub_eq_add_neg]

lemma helperForTheorem_6_27_1_closure_domainCriteria_and_strict_decreasing_ray {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    closedProperConvexMinimumPartG f := by
  let domFstar : Set (Fin n → ℝ) :=
    effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)
  have h13 :=
    mem_closure_ri_interior_affineSpan_effectiveDomain_fenchelConjugate_iff_recessionFunction
      (f := f) hclosed hproper (0 : Fin n → ℝ)
  have hclosure :
      ((0 : Fin n → ℝ) ∈ closure domFstar ↔
        ∀ y : Fin n → ℝ, (0 : EReal) ≤ recessionFunction f y) := by
    simpa [domFstar] using h13.1
  refine ⟨hclosure, ?_⟩
  constructor
  · intro hNotClosure
    -- Negating the closure criterion produces a direction with strictly negative recession.
    have hExistsNeg : ∃ y : Fin n → ℝ, recessionFunction f y < (0 : EReal) := by
      by_contra hNoNeg
      have hAllNonneg : ∀ y : Fin n → ℝ, (0 : EReal) ≤ recessionFunction f y := by
        intro y
        by_contra hyNonneg
        exact hNoNeg ⟨y, lt_of_not_ge hyNonneg⟩
      exact hNotClosure (hclosure.2 hAllNonneg)
    rcases hExistsNeg with ⟨y, hyNeg⟩
    rcases helperForTheorem_6_27_1_exists_positive_real_below_negative_recession
        (f := f) (y := y) hyNeg with
      ⟨ε, hε, hyBound⟩
    have hproperStar :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
      proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
    have hsupp_eq :
        supportFunctionEReal domFstar = recessionFunction f := by
      simpa [domFstar] using
        section13_supportFunctionEReal_dom_fenchelConjugate_eq_recessionFunction
          (n := n) (f := f) hclosed hproper
    have hzeroRec : recessionFunction f (0 : Fin n → ℝ) = 0 := by
      have hCne : domFstar.Nonempty :=
        section13_effectiveDomain_nonempty_of_proper
          (n := n) (f := fenchelConjugate n f) hproperStar
      have hzeroSupp : supportFunctionEReal domFstar 0 = 0 := by
        apply le_antisymm
        · exact
            (section13_supportFunctionEReal_le_coe_iff (C := domFstar) (y := 0) (μ := 0)).2
              (by intro x hx; simp)
        · rcases hCne with ⟨x0, hx0⟩
          exact le_sSup ⟨x0, hx0, by simp⟩
      calc
        recessionFunction f (0 : Fin n → ℝ) = supportFunctionEReal domFstar 0 := by
          exact (congrArg (fun g => g (0 : Fin n → ℝ)) hsupp_eq).symm
        _ = 0 := hzeroSupp
    have hy_ne : y ≠ 0 := by
      intro hy0
      have : recessionFunction f y = 0 := by simpa [hy0] using hzeroRec
      exact hyNeg.ne this
    refine ⟨y, hy_ne, ε, hε, ?_⟩
    -- The negative recession bound scales linearly and yields the strict ray estimate.
    exact
      helperForTheorem_6_27_1_negative_recession_bound_implies_strict_decreasing_ray
        (f := f) hclosed hproper y hε hyBound
  · rintro ⟨y, hy_ne, ε, hε, hRay⟩
    -- A strict decreasing ray forces a strictly negative recession value, contradicting closure.
    have hyRecLe : recessionFunction f y ≤ ((-ε : ℝ) : EReal) := by
      refine sSup_le ?_
      rintro r ⟨x, hx, rfl⟩
      have hxy :
          f (x + (1 : ℝ) • y) ≤ f x - ((1 * ε : ℝ) : EReal) :=
        hRay 1 (by norm_num) x hx
      have hx_top_lt : f x < (⊤ : EReal) := by
        simpa [effectiveDomain_eq] using hx
      have hx_top : f x ≠ (⊤ : EReal) := lt_top_iff_ne_top.mp hx_top_lt
      have hx_bot : f x ≠ (⊥ : EReal) := hproper.2.2 x (by simp)
      have hdiff :
          f (x + (1 : ℝ) • y) - f x ≤ ((-ε : ℝ) : EReal) := by
        have hxy' : f (x + (1 : ℝ) • y) ≤ ((-ε : ℝ) : EReal) + f x := by
          simpa [one_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hxy
        exact
          (EReal.sub_le_iff_le_add
            (a := f (x + (1 : ℝ) • y)) (b := f x) (c := ((-ε : ℝ) : EReal))
            (Or.inl hx_bot) (Or.inl hx_top)).2 hxy'
      simpa [one_smul] using hdiff
    have hyRecNeg : recessionFunction f y < (0 : EReal) := by
      have hneg_lt_zero : (((-ε : ℝ)) : EReal) < (0 : EReal) := by
        exact_mod_cast (show -ε < 0 by linarith)
      exact lt_of_le_of_lt hyRecLe hneg_lt_zero
    intro hClosure
    exact hyRecNeg.not_ge ((hclosure.1 hClosure) y)

end Section27
end Chap06

/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part4

section Chap05
section Section24

open scoped ConvexAnalysis

attribute [local instance] Classical.propDecidable

/-- The right-hand profile of an extended-real-valued function on `ℝ`, computed as the infimum of
its values strictly to the right of the base point. For a monotone function, this is the
right-hand limit profile. -/
noncomputable def rightLimitProfile (φ : ℝ → EReal) : ℝ → EReal :=
  fun x => sInf (φ '' Set.Ioi x)

/-- The left-hand profile of an extended-real-valued function on `ℝ`, computed as the supremum of
its values strictly to the left of the base point. For a monotone function, this is the left-hand
limit profile. -/
noncomputable def leftLimitProfile (φ : ℝ → EReal) : ℝ → EReal :=
  fun x => sSup (φ '' Set.Iio x)

-- Proof sketch: use Theorem 5.24.1 to compare `φ x` and `φ y` through the inequalities
-- `f'_+(x) ≤ f'_-(y)` for `x < y`, which gives monotonicity of `φ`. For a monotone extended-real
-- function, the infimum of the strict right-hand values and the supremum of the strict left-hand
-- values recover the corresponding one-sided limits. The one-sided continuity statements from
-- Theorem 5.24.1 then identify these profiles with `f'_+` and `f'_-`, and substituting those
-- identities into Theorem 5.24.2 yields the subdifferential interval formula.
/-- Helper for Theorem 5.24.3: any selector squeezed between the one-sided derivative extensions
inherits their monotonicity. -/
lemma helperForTheorem_5_24_3_selection_monotone
    (f : (Fin 1 → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f)
    (φ : ℝ → EReal)
    (hφ : ∀ x : ℝ,
      leftDerivativeExtension f x ≤ φ x ∧ φ x ≤ rightDerivativeExtension f x) :
    Monotone φ := by
  intro x y hxy
  rcases lt_or_eq_of_le hxy with hlt | rfl
  · -- Insert the derivative extensions between `φ x` and `φ y`.
    exact
      le_trans
        (hφ x).2
        (le_trans
          (helperForTheorem_5_24_1_rightDerivativeExtension_le_leftDerivativeExtension_of_lt
            f hproper hlt)
          (hφ y).1)
  · exact le_rfl

/-- Helper for Theorem 5.24.3: on the strict right neighborhood of `x`, the selector converges to
`f'_+(x)` because it is squeezed between `f'_-` and `f'_+`. -/
lemma helperForTheorem_5_24_3_selector_right_tendsto
    (f : (Fin 1 → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f)
    (φ : ℝ → EReal)
    (hφ : ∀ x : ℝ,
      leftDerivativeExtension f x ≤ φ x ∧ φ x ≤ rightDerivativeExtension f x)
    (x : ℝ) :
    Filter.Tendsto φ (nhdsWithin x (Set.Ioi x)) (nhds (rightDerivativeExtension f x)) := by
  rcases oneDimensional_derivativeExtensions_monotone_ordered_and_oneSidedContinuous
      f hclosed hproper with
    ⟨_hRightMono, _hLeftMono, _hfinite, _horder, hRightSelf, _hRightLeft, hLeftRight, _hLeftSelf⟩
  refine tendsto_order.2 ?_
  constructor
  · intro a ha
    have hLowerOrder := tendsto_order.1 (hLeftRight x)
    -- A strict lower bound on `f'_+(x)` is eventually a strict lower bound on `f'_-(z)`.
    filter_upwards [hLowerOrder.1 a ha] with z hz
    exact lt_of_lt_of_le hz (hφ z).1
  · intro b hb
    have hUpperOrder := tendsto_order.1 (hRightSelf x)
    -- A strict upper bound on `f'_+(x)` eventually bounds `φ z` from above via `φ z ≤ f'_+(z)`.
    filter_upwards [hUpperOrder.2 b hb] with z hz
    exact lt_of_le_of_lt (hφ z).2 hz

/-- Helper for Theorem 5.24.3: the strict-right profile of the selector is exactly `f'_+`. -/
lemma helperForTheorem_5_24_3_rightLimitProfile_eq_rightDerivativeExtension
    (f : (Fin 1 → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f)
    (φ : ℝ → EReal)
    (hφ : ∀ x : ℝ,
      leftDerivativeExtension f x ≤ φ x ∧ φ x ≤ rightDerivativeExtension f x)
    (x : ℝ) :
    rightLimitProfile φ x = rightDerivativeExtension f x := by
  have hmono :
      Monotone φ :=
    helperForTheorem_5_24_3_selection_monotone f hproper φ hφ
  have hProfile :
      Filter.Tendsto φ (nhdsWithin x (Set.Ioi x)) (nhds (rightLimitProfile φ x)) := by
    -- A monotone function has a right limit equal to the infimum of its strict-right tail.
    simpa [rightLimitProfile] using hmono.tendsto_nhdsGT x
  have hDerivative :
      Filter.Tendsto φ (nhdsWithin x (Set.Ioi x)) (nhds (rightDerivativeExtension f x)) :=
    helperForTheorem_5_24_3_selector_right_tendsto f hclosed hproper φ hφ x
  -- Uniqueness of limits identifies the two right-hand targets.
  exact tendsto_nhds_unique hProfile hDerivative

/-- Helper for Theorem 5.24.3: on the strict left neighborhood of `x`, the selector converges to
`f'_-(x)` because it is squeezed between `f'_-` and `f'_+`. -/
lemma helperForTheorem_5_24_3_selector_left_tendsto
    (f : (Fin 1 → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f)
    (φ : ℝ → EReal)
    (hφ : ∀ x : ℝ,
      leftDerivativeExtension f x ≤ φ x ∧ φ x ≤ rightDerivativeExtension f x)
    (x : ℝ) :
    Filter.Tendsto φ (nhdsWithin x (Set.Iio x)) (nhds (leftDerivativeExtension f x)) := by
  rcases oneDimensional_derivativeExtensions_monotone_ordered_and_oneSidedContinuous
      f hclosed hproper with
    ⟨_hRightMono, _hLeftMono, _hfinite, _horder, _hRightSelf, hRightLeft, _hLeftRight, hLeftSelf⟩
  refine tendsto_order.2 ?_
  constructor
  · intro a ha
    have hLowerOrder := tendsto_order.1 (hLeftSelf x)
    -- A strict lower bound on `f'_-(x)` is eventually a strict lower bound on `f'_-(z)`.
    filter_upwards [hLowerOrder.1 a ha] with z hz
    exact lt_of_lt_of_le hz (hφ z).1
  · intro b hb
    have hUpperOrder := tendsto_order.1 (hRightLeft x)
    -- A strict upper bound on `f'_-(x)` eventually bounds `f'_+(z)`, hence also `φ z`.
    filter_upwards [hUpperOrder.2 b hb] with z hz
    exact lt_of_le_of_lt (hφ z).2 hz

/-- Helper for Theorem 5.24.3: the strict-left profile of the selector is exactly `f'_-`. -/
lemma helperForTheorem_5_24_3_leftLimitProfile_eq_leftDerivativeExtension
    (f : (Fin 1 → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f)
    (φ : ℝ → EReal)
    (hφ : ∀ x : ℝ,
      leftDerivativeExtension f x ≤ φ x ∧ φ x ≤ rightDerivativeExtension f x)
    (x : ℝ) :
    leftLimitProfile φ x = leftDerivativeExtension f x := by
  have hmono :
      Monotone φ :=
    helperForTheorem_5_24_3_selection_monotone f hproper φ hφ
  have hProfile :
      Filter.Tendsto φ (nhdsWithin x (Set.Iio x)) (nhds (leftLimitProfile φ x)) := by
    -- A monotone function has a left limit equal to the supremum of its strict-left tail.
    simpa [leftLimitProfile] using hmono.tendsto_nhdsLT x
  have hDerivative :
      Filter.Tendsto φ (nhdsWithin x (Set.Iio x)) (nhds (leftDerivativeExtension f x)) :=
    helperForTheorem_5_24_3_selector_left_tendsto f hclosed hproper φ hφ x
  -- Uniqueness of limits identifies the two left-hand targets.
  exact tendsto_nhds_unique hProfile hDerivative

/-- Theorem 5.24.3: if `f` is a closed proper convex function on `ℝ` and `φ` satisfies
`f'_-(x) ≤ φ(x) ≤ f'_+(x)` for every `x`, then `φ` is nondecreasing, its right and left one-sided
profiles agree with `f'_+` and `f'_-`, and consequently
`∂ f(x) = {xStar | φ_-(x) ≤ xStar ≤ φ_+(x)}` for every `x`. -/
theorem oneDimensional_selection_between_derivativeExtensions_monotone_profiles_and_subdifferential
    (f : (Fin 1 → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f) (φ : ℝ → EReal)
    (hφ : ∀ x : ℝ,
      leftDerivativeExtension f x ≤ φ x ∧ φ x ≤ rightDerivativeExtension f x) :
    Monotone φ ∧
      rightLimitProfile φ = rightDerivativeExtension f ∧
      leftLimitProfile φ = leftDerivativeExtension f ∧
      (∀ x : ℝ,
        {xStar : ℝ | dotProductEquiv ℝ (Fin 1) (scalarPoint xStar) ∈ ∂ f (scalarPoint x)} =
          {xStar : ℝ |
            leftLimitProfile φ x ≤ ((xStar : ℝ) : EReal) ∧
              (((xStar : ℝ) : EReal) ≤ rightLimitProfile φ x)}) := by
  have hMonotone :
      Monotone φ :=
    helperForTheorem_5_24_3_selection_monotone f hproper φ hφ
  have hRightProfile :
      rightLimitProfile φ = rightDerivativeExtension f := by
    -- Identify the right profile pointwise using the squeezed one-sided limit.
    funext x
    exact
      helperForTheorem_5_24_3_rightLimitProfile_eq_rightDerivativeExtension
        f hclosed hproper φ hφ x
  have hLeftProfile :
      leftLimitProfile φ = leftDerivativeExtension f := by
    -- Identify the left profile pointwise using the corresponding left squeeze.
    funext x
    exact
      helperForTheorem_5_24_3_leftLimitProfile_eq_leftDerivativeExtension
        f hclosed hproper φ hφ x
  refine ⟨hMonotone, hRightProfile, hLeftProfile, ?_⟩
  intro x
  -- Rewrite Theorem 5.24.2 with the two profile identities.
  simpa [hRightProfile, hLeftProfile] using
    oneDimensional_subdifferential_preimage_eq_setOf_leftDerivativeExtension_le_and_le_rightDerivativeExtension
      f hclosed hproper x

/-- Definition 5.24.4: A complete non-decreasing curve is a subset `Γ ⊆ ℝ²` of the form
`Γ = {(x, xStar) | φ_-(x) ≤ xStar ≤ φ_+(x)}` for some nondecreasing extended-real function
`φ : ℝ → EReal`, provided the resulting band is nonempty. -/
def IsCompleteNondecreasingCurve (Γ : Set (ℝ × ℝ)) : Prop :=
  ∃ φ : ℝ → EReal,
    Monotone φ ∧
      Γ.Nonempty ∧
      Γ = {p | leftLimitProfile φ p.1 ≤ (p.2 : EReal) ∧ (p.2 : EReal) ≤ rightLimitProfile φ p.1}

/-- The cyclic successor index on a finite cycle of length `m + 1`. -/
def cyclicSuccessor {m : ℕ} : Fin (m + 1) → Fin (m + 1) :=
  fun i => ⟨(i.1 + 1) % (m + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

/-- Definition 5.24.5: A multivalued mapping `ρ` from `R^n` to `R^n` is cyclically monotone if,
for every finite family of pairs `(x_i, x_i*)` with `x_i* ∈ ρ(x_i)`, the cyclic sum
`Σ_i ⟨x_{i+1} - x_i, x_i*⟩`, where `x_{m+1} = x_0`, is nonpositive. -/
def IsCyclicallyMonotone {n : ℕ} (ρ : (Fin n → ℝ) → Set (Fin n → ℝ)) : Prop :=
  ∀ m : ℕ,
    ∀ x xStar : Fin (m + 1) → Fin n → ℝ,
      (∀ i : Fin (m + 1), xStar i ∈ ρ (x i)) →
        Finset.univ.sum (fun i : Fin (m + 1) =>
          dotProduct (x (cyclicSuccessor i) - x i) (xStar i)) ≤ 0

-- Proof sketch: for a cyclic family `(x_i, x_i*)` with `x_i* ∈ ∂ f(x_i)`, apply the subgradient
-- inequality at each consecutive pair `(x_i, x_{i+1})`. Summing these inequalities over the cycle
-- telescopes the function values and yields the required nonpositivity of the cyclic sum.
/-- Helper for Proposition 5.24.3: a vector in the Euclidean preimage of the subdifferential
forces the function value at the base point to be finite. -/
lemma helperForProposition_5_24_3_finiteAt_of_mem_preimageSubdifferential {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {x v : Fin n → ℝ}
    (hv : v ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)) :
    f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) := by
  have hvSub : IsEuclideanSubgradientAt f x v := by
    -- Rewrite the preimage hypothesis as Euclidean subgradient membership.
    simpa [IsEuclideanSubgradientAt] using hv
  -- Apply the previously established finiteness criterion for Euclidean subgradients.
  exact helperForTheorem_23_5_finiteAt_of_euclideanSubgradient f hproper x v hvSub

/-- Helper for Proposition 5.24.3: subgradient membership bounds each cycle edge by the
corresponding difference of function values. -/
lemma helperForProposition_5_24_3_edgeBound_of_mem_preimageSubdifferential {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {x y v : Fin n → ℝ}
    (hv : v ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)) :
    (((dotProduct (y - x) v : ℝ) : EReal)) ≤ f y - f x := by
  have hxFinite :=
    helperForProposition_5_24_3_finiteAt_of_mem_preimageSubdifferential f hproper hv
  have hvSub : IsSubgradientAt f x (dotProductEquiv ℝ (Fin n) v) := by
    -- Unpack the preimage condition to the textbook subgradient inequality.
    simpa [mem_subdifferentialAt_iff] using hv
  -- Evaluate the subgradient inequality at `y` and isolate the linear edge term.
  exact
    (EReal.le_sub_iff_add_le
      (a := ((dotProduct (y - x) v : ℝ) : EReal))
      (b := f x) (c := f y)
      (Or.inl hxFinite.2) (Or.inl hxFinite.1)).2
      (by
        simpa [dotProductEquiv_apply_apply, dotProduct_comm, add_comm, add_left_comm, add_assoc]
          using hvSub y)

/-- Helper for Proposition 5.24.3: composing a finite sum with the cyclic successor does not
change the sum. -/
lemma helperForProposition_5_24_3_sum_comp_cyclicSuccessor
    {m : ℕ} {α : Type*} [AddCommMonoid α] (ψ : Fin (m + 1) → α) :
    (∑ i, ψ (cyclicSuccessor i)) = ∑ i, ψ i := by
  have hcyclic : ∀ i : Fin (m + 1), cyclicSuccessor i = (finRotate (m + 1)) i := by
    intro i
    -- Identify `cyclicSuccessor` with the standard rotation permutation of `Fin (m + 1)`.
    calc
      cyclicSuccessor i = i + 1 := by
        by_cases hi : i = Fin.last m
        · subst hi
          ext
          simp [cyclicSuccessor]
        · have hne : (i : ℕ) ≠ m := by
            intro hval
            apply hi
            ext
            simp [Fin.last, hval]
          have hlt : (i : ℕ) + 1 < m + 1 :=
            Nat.succ_lt_succ (lt_of_le_of_ne (Nat.le_of_lt_succ i.is_lt) hne)
          ext
          simp [cyclicSuccessor, Nat.mod_eq_of_lt hlt, Fin.val_add_one_of_lt' hlt]
      _ = (finRotate (m + 1)) i := by
        symm
        exact finRotate_succ_apply i
  -- Reindex the sum by the finite rotation permutation.
  simpa [hcyclic] using
    (Fintype.sum_equiv (finRotate (m + 1))
      (fun i => ψ (cyclicSuccessor i)) ψ
      (fun i => by simp [hcyclic i]))

/-- Helper for Proposition 5.24.3: the sum of finite cyclic function-value differences
telescopes to zero. -/
lemma helperForProposition_5_24_3_sum_finiteDifferences_eq_zero
    {n m : ℕ} (f : (Fin n → ℝ) → EReal)
    (x : Fin (m + 1) → Fin n → ℝ)
    (_hfinite : ∀ i, f (x i) ≠ (⊤ : EReal) ∧ f (x i) ≠ (⊥ : EReal)) :
    (∑ i, (((f (x (cyclicSuccessor i))).toReal - (f (x i)).toReal : ℝ))) = 0 := by
  -- Split the cyclic difference sum into successor and base sums.
  rw [Finset.sum_sub_distrib]
  -- Reindex the successor sum and cancel the two identical totals.
  rw [helperForProposition_5_24_3_sum_comp_cyclicSuccessor (fun i => (f (x i)).toReal)]
  simp

/-- Proposition 5.24.3: If `f` is a proper convex function on `ℝ^n`, then, after identifying
subgradients with vectors in `ℝ^n` via `dotProductEquiv`, its subdifferential mapping is
cyclically monotone. -/
theorem properConvexFunctionOn_isCyclicallyMonotone_subdifferential {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    IsCyclicallyMonotone
      (fun x => ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)) := by
  intro m x xStar hmem
  have hfinite :
      ∀ i : Fin (m + 1), f (x i) ≠ (⊤ : EReal) ∧ f (x i) ≠ (⊥ : EReal) := by
    intro i
    -- Each selected subgradient makes the corresponding function value finite.
    exact
      helperForProposition_5_24_3_finiteAt_of_mem_preimageSubdifferential
        f hproper (hmem i)
  have hedgeReal :
      ∀ i : Fin (m + 1),
        dotProduct (x (cyclicSuccessor i) - x i) (xStar i) ≤
          (f (x (cyclicSuccessor i))).toReal - (f (x i)).toReal := by
    intro i
    have hEdgeEReal :=
      helperForProposition_5_24_3_edgeBound_of_mem_preimageSubdifferential
        (f := f) (hproper := hproper) (x := x i) (y := x (cyclicSuccessor i))
        (v := xStar i) (hmem i)
    have hnextFinite := hfinite (cyclicSuccessor i)
    have hiFinite := hfinite i
    have hEdgeRealEReal :
        (((dotProduct (x (cyclicSuccessor i) - x i) (xStar i) : ℝ) : EReal)) ≤
          ((((f (x (cyclicSuccessor i))).toReal - (f (x i)).toReal : ℝ) : ℝ) : EReal) := by
      -- Rewrite the finite function values as coerced reals to move the inequality into `ℝ`.
      simpa [EReal.coe_sub, EReal.coe_toReal hnextFinite.1 hnextFinite.2,
        EReal.coe_toReal hiFinite.1 hiFinite.2] using hEdgeEReal
    exact_mod_cast hEdgeRealEReal
  have hsum :
      (∑ i : Fin (m + 1), dotProduct (x (cyclicSuccessor i) - x i) (xStar i)) ≤
        ∑ i : Fin (m + 1),
          ((f (x (cyclicSuccessor i))).toReal - (f (x i)).toReal) := by
    -- Sum the edge inequalities around the whole finite cycle.
    exact Finset.sum_le_sum (fun i _ => hedgeReal i)
  -- The function-value differences telescope, leaving the desired nonpositive cyclic sum.
  calc
    (∑ i : Fin (m + 1), dotProduct (x (cyclicSuccessor i) - x i) (xStar i)) ≤
        ∑ i : Fin (m + 1),
          ((f (x (cyclicSuccessor i))).toReal - (f (x i)).toReal) :=
      hsum
    _ = 0 :=
      helperForProposition_5_24_3_sum_finiteDifferences_eq_zero f x hfinite

/-- The graph of a multivalued mapping `ρ : ℝ^n ⇉ ℝ^n`. -/
def multivaluedMappingGraph {n : ℕ} (ρ : (Fin n → ℝ) → Set (Fin n → ℝ)) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p | p.2 ∈ ρ p.1}

/-- Definition 5.24.6: A maximal cyclically monotone mapping is a cyclically monotone mapping
whose graph is not properly contained in the graph of any other cyclically monotone mapping. -/
def IsMaximalCyclicallyMonotone {n : ℕ} (ρ : (Fin n → ℝ) → Set (Fin n → ℝ)) : Prop :=
  IsCyclicallyMonotone ρ ∧
    ∀ ⦃σ : (Fin n → ℝ) → Set (Fin n → ℝ)⦄,
      IsCyclicallyMonotone σ →
      multivaluedMappingGraph ρ ⊆ multivaluedMappingGraph σ →
      multivaluedMappingGraph σ = multivaluedMappingGraph ρ

/-- Definition 5.24.7: A multivalued mapping `ρ` from `R^n` to `R^n` is monotone if
`⟪x₁ - x₀, x₁* - x₀*⟫ ≥ 0` for every two points `(x₀, x₀*)` and `(x₁, x₁*)` in its graph. -/
def IsMonotoneMultivaluedMapping {n : ℕ} (ρ : (Fin n → ℝ) → Set (Fin n → ℝ)) : Prop :=
  ∀ ⦃x0 x1 x0Star x1Star : Fin n → ℝ⦄,
    x0Star ∈ ρ x0 →
    x1Star ∈ ρ x1 →
    0 ≤ dotProduct (x1 - x0) (x1Star - x0Star)

/-- A maximal monotone multivalued mapping is a monotone mapping whose graph is not properly
contained in the graph of any other monotone mapping. -/
def IsMaximalMonotoneMultivaluedMapping {n : ℕ}
    (ρ : (Fin n → ℝ) → Set (Fin n → ℝ)) : Prop :=
  IsMonotoneMultivaluedMapping ρ ∧
    ∀ ⦃σ : (Fin n → ℝ) → Set (Fin n → ℝ)⦄,
      IsMonotoneMultivaluedMapping σ →
      multivaluedMappingGraph ρ ⊆ multivaluedMappingGraph σ →
      multivaluedMappingGraph σ = multivaluedMappingGraph ρ


end Section24
end Chap05

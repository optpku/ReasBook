/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section04_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section13_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section18_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section19_part4

open scoped Topology

section Chap05
section Section23

/-- Definition 23.0.5 (Subgradient Inequality): A dual vector `xStar` is a subgradient of `f` at
`x` if for every `z` one has `f z ≥ f x + ⟪xStar, z - x⟫`, i.e. if it satisfies the subgradient
inequality. -/
def IsSubgradientAt {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) (xStar : Module.Dual ℝ (Fin n → ℝ)) : Prop :=
  ∀ z, f z ≥ f x + ((xStar (z - x) : ℝ) : EReal)

/-- Definition 23.0.6 (Subdifferential): The subdifferential of `f` at the point `x` is the set
of all subgradients of `f` at `x`; equivalently, `x ↦ subdifferentialAt f x` is the set-valued
subdifferential mapping of `f`. -/
def subdifferentialAt {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) : Set (Module.Dual ℝ (Fin n → ℝ)) :=
  {g | IsSubgradientAt f x g}

/-- Scoped notation for the pointwise subdifferential. With `open scoped ConvexAnalysis`,
write `∂ f x` or, more readably, `∂ f (x)` for `subdifferentialAt f x`. -/
scoped[ConvexAnalysis] notation "∂" => subdifferentialAt

open scoped ConvexAnalysis

@[simp] theorem mem_subdifferentialAt_iff {n : ℕ}
    {f : (Fin n → ℝ) → EReal} {x : Fin n → ℝ} {xStar : Module.Dual ℝ (Fin n → ℝ)} :
    xStar ∈ ∂ f x ↔ IsSubgradientAt f x xStar :=
  Iff.rfl

/-- A dual vector `xStar` is an `ε`-subgradient of `f` at `x` when `f` is convex, `f` is finite
at `x`, and `xStar` satisfies the approximate subgradient inequality
`f z ≥ (f x - ε) + ⟪xStar, z - x⟫` for every `z`, with `ε ≥ 0`. -/
def IsApproximateSubgradientAt {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) (ε : NNReal)
    (xStar : Module.Dual ℝ (Fin n → ℝ)) : Prop :=
  ConvexFunction f ∧
    (f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) ∧
    ∀ z, f z ≥ (f x - ((ε : ℝ) : EReal)) + ((xStar (z - x) : ℝ) : EReal)

/-- Definition 23.6 (Approximate Subgradient): For a convex function `f` finite at `x`, the
approximate subdifferential `∂_ε f(x)` is the set of all dual vectors `xStar` such that
`ε ≥ 0`, `f` is convex, `f x` is finite, and `f z ≥ (f x - ε) + ⟪xStar, z - x⟫` for every `z`;
equivalently, its elements are the `ε`-subgradients of `f` at `x`. -/
def approximateSubdifferentialAt {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) (ε : NNReal) :
    Set (Module.Dual ℝ (Fin n → ℝ)) :=
  {xStar | IsApproximateSubgradientAt f x ε xStar}

/-- Scoped notation for the pointwise approximate subdifferential. With
`open scoped ConvexAnalysis`, write `∂[ε] f x` or `∂[ε] f (x)` for
`approximateSubdifferentialAt f x ε`. -/
scoped[ConvexAnalysis] notation "∂[" ε "] " f:max x:max =>
  approximateSubdifferentialAt f x ε

@[simp] theorem mem_approximateSubdifferentialAt_iff {n : ℕ}
    {f : (Fin n → ℝ) → EReal} {x : Fin n → ℝ} {ε : NNReal}
    {xStar : Module.Dual ℝ (Fin n → ℝ)} :
    xStar ∈ ∂[ε] f x ↔ IsApproximateSubgradientAt f x ε xStar :=
  Iff.rfl

/-- The normal cone of a set `C` at `x`, expressed by the supporting-inequality condition. -/
def normalConeAt {n : ℕ} (C : Set (Fin n → ℝ)) (x : Fin n → ℝ) :
    Set (Module.Dual ℝ (Fin n → ℝ)) :=
  {xStar | x ∈ C ∧ ∀ z ∈ C, xStar (z - x) ≤ 0}

@[simp] theorem mem_normalConeAt_iff {n : ℕ}
    {C : Set (Fin n → ℝ)} {x : Fin n → ℝ} {xStar : Module.Dual ℝ (Fin n → ℝ)} :
    xStar ∈ normalConeAt C x ↔ x ∈ C ∧ ∀ z ∈ C, xStar (z - x) ≤ 0 :=
  Iff.rfl

/-- The translated difference function `y ↦ f (x + y) - f x` associated to `f` at `x`. -/
def translatedDifferenceFunctionAt {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) : (Fin n → ℝ) → EReal :=
  fun y => f (x + y) - f x

-- Proof sketch: compute the Fenchel conjugate of the translated difference by the change of
-- variables `z = x + y`, which produces the affine correction `f x - ⟪x, xStar⟫`.
-- The approximate subgradient inequality is then exactly the statement that this conjugate value
-- is at most `ε`. Since Fenchel conjugates are closed convex functions, their sublevel sets are
-- closed and convex; monotonicity in `ε` is immediate from the sublevel-set description, and the
-- exact subdifferential is recovered by intersecting all positive-`ε` sublevel sets.
/-- Helper for Proposition 23.6.1: the Fenchel conjugate of the translated-difference function is
the original conjugate with the expected affine correction term. -/
lemma helperForProposition_23_6_1_translatedDifference_fenchelConjugate
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) (xStar : Fin n → ℝ) :
    fenchelConjugate n (translatedDifferenceFunctionAt f x) xStar =
      fenchelConjugate n f xStar + f x - ((dotProduct x xStar : ℝ) : EReal) := by
  let β : ℝ := (f x).toReal
  have hβ : ((β : ℝ) : EReal) = f x := by
    simp [β, EReal.coe_toReal, hx.1, hx.2]
  have hfun :
      translatedDifferenceFunctionAt f x =
        fun y => f (y - (-x)) - ((β : ℝ) : EReal) := by
    -- Rewrite the translated difference as a translate followed by subtraction of the
    -- finite constant `f x`.
    funext y
    simp [translatedDifferenceFunctionAt, hβ, β, sub_eq_add_neg, add_comm]
  -- Compute the conjugate by applying the translation formula and then the constant-shift formula.
  calc
    fenchelConjugate n (translatedDifferenceFunctionAt f x) xStar =
        fenchelConjugate n (fun y => f (y - (-x)) - ((β : ℝ) : EReal)) xStar := by
          simp [hfun]
    _ = fenchelConjugate n (fun y => f (y - (-x))) xStar + ((β : ℝ) : EReal) := by
          rw [section13_fenchelConjugate_sub_const (g := fun y => f (y - (-x))) (β := β)]
    _ = fenchelConjugate n f xStar + ((dotProduct (-x) xStar : ℝ) : EReal) +
          ((β : ℝ) : EReal) := by
          rw [section16_fenchelConjugate_translate (h := f) (a := -x)]
    _ = fenchelConjugate n f xStar + ((β : ℝ) : EReal) -
          ((dotProduct x xStar : ℝ) : EReal) := by
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = fenchelConjugate n f xStar + f x - ((dotProduct x xStar : ℝ) : EReal) := by
          simp [hβ]

/-- Helper for Proposition 23.6.1: vector membership in the approximate subdifferential is the
translated affine-minorant inequality. -/
lemma helperForProposition_23_6_1_mem_approximateSubdifferential_iff_affine_minorant
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (hf : ConvexFunction f) (x : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) (ε : NNReal) (xStar : Fin n → ℝ) :
    dotProductEquiv ℝ (Fin n) xStar ∈ approximateSubdifferentialAt f x ε ↔
      ∀ y : Fin n → ℝ,
        (((dotProduct y xStar - ε : ℝ) : EReal) ≤ translatedDifferenceFunctionAt f x y) := by
  constructor
  · intro hxApprox
    change IsApproximateSubgradientAt f x ε (dotProductEquiv ℝ (Fin n) xStar) at hxApprox
    intro y
    have hy := hxApprox.2.2 (x + y)
    have hy' : (((dotProduct y xStar - ε : ℝ) : EReal) + f x) ≤ f (x + y) := by
      -- Evaluate the approximate-subgradient inequality at `z = x + y` and simplify the increment.
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, dotProduct_comm] using hy
    exact
      (EReal.le_sub_iff_add_le (a := ((dotProduct y xStar - ε : ℝ) : EReal))
        (b := f x) (c := f (x + y)) (Or.inl hx.2) (Or.inl hx.1)).2 hy'
  · intro hminorant
    change IsApproximateSubgradientAt f x ε (dotProductEquiv ℝ (Fin n) xStar)
    refine ⟨hf, hx, ?_⟩
    intro z
    have hz :=
      hminorant (z - x)
    have hz' : (((dotProduct (z - x) xStar - ε : ℝ) : EReal) + f x) ≤ f z :=
      (EReal.le_sub_iff_add_le (a := ((dotProduct (z - x) xStar - ε : ℝ) : EReal))
        (b := f x) (c := f z) (Or.inl hx.2) (Or.inl hx.1)).1 (by simpa [translatedDifferenceFunctionAt] using hz)
    -- Reassemble the textbook inequality from the translated one.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, dotProduct_comm] using hz'

/-- Helper for Proposition 23.6.1: the translated conjugate sublevel condition is equivalent to
approximate-subgradient membership. -/
lemma helperForProposition_23_6_1_mem_approximateSubdifferential_iff_conjugate_le
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (hf : ConvexFunction f) (x : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) (ε : NNReal) (xStar : Fin n → ℝ) :
    dotProductEquiv ℝ (Fin n) xStar ∈ approximateSubdifferentialAt f x ε ↔
      fenchelConjugate n (translatedDifferenceFunctionAt f x) xStar ≤ ((ε : ℝ) : EReal) := by
  -- Apply the standard conjugate-vs-affine-minorant characterization to the translated function.
  rw [fenchelConjugate_le_coe_iff_affine_le (n := n) (f := translatedDifferenceFunctionAt f x)
    (b := xStar) (μ := ε)]
  exact
    helperForProposition_23_6_1_mem_approximateSubdifferential_iff_affine_minorant
      (f := f) hf x hx ε xStar

/-- Helper for Proposition 23.6.1: after identifying vectors with dual vectors, the
approximate subdifferential is exactly the corresponding translated-conjugate sublevel set. -/
lemma helperForProposition_23_6_1_preimage_eq_conjugateSublevel
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (hf : ConvexFunction f) (x : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) (ε : NNReal) :
    ((dotProductEquiv ℝ (Fin n)) ⁻¹' approximateSubdifferentialAt f x ε) =
      (fenchelConjugate n (translatedDifferenceFunctionAt f x)) ⁻¹' Set.Iic (((ε : ℝ) : EReal)) := by
  -- Route correction: package the sublevel-set identification as a reusable helper so the main
  -- proposition can use a single geometric description in its closedness and convexity branches.
  ext xStar
  -- Membership on either side is the same translated-conjugate inequality.
  simp [Set.mem_preimage, Set.mem_Iic,
    helperForProposition_23_6_1_mem_approximateSubdifferential_iff_conjugate_le
      (f := f) hf x hx ε xStar]

/-- Helper for Proposition 23.6.1: the translated-difference conjugate is always nonnegative. -/
lemma helperForProposition_23_6_1_nonneg_translatedDifferenceConjugate
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) (xStar : Fin n → ℝ) :
    0 ≤ fenchelConjugate n (translatedDifferenceFunctionAt f x) xStar := by
  have hzero : translatedDifferenceFunctionAt f x 0 = 0 := by
    -- The translated difference vanishes at the origin because `f x` is finite.
    simp [translatedDifferenceFunctionAt, EReal.sub_self hx.1 hx.2]
  have hterm :
      ((dotProduct (0 : Fin n → ℝ) xStar : ℝ) : EReal) -
        translatedDifferenceFunctionAt f x 0 ≤
          fenchelConjugate n (translatedDifferenceFunctionAt f x) xStar := by
    -- The `y = 0` term is one of the candidates in the supremum defining the conjugate.
    unfold fenchelConjugate
    exact le_sSup ⟨0, rfl⟩
  simpa [hzero] using hterm

/-- Helper for Proposition 23.6.1: at `ε = 0`, approximate subgradients are exactly ordinary
subgradients. -/
lemma helperForProposition_23_6_1_approximateSubdifferential_zero_eq_subdifferential
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (hf : ConvexFunction f) (x : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) (xStar : Fin n → ℝ) :
    dotProductEquiv ℝ (Fin n) xStar ∈ approximateSubdifferentialAt f x 0 ↔
      dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x := by
  constructor
  · intro hxApprox
    change IsApproximateSubgradientAt f x 0 (dotProductEquiv ℝ (Fin n) xStar) at hxApprox
    change IsSubgradientAt f x (dotProductEquiv ℝ (Fin n) xStar)
    -- Setting `ε = 0` collapses the approximate inequality to the exact subgradient inequality.
    simpa [IsApproximateSubgradientAt, IsSubgradientAt] using hxApprox.2.2
  · intro hxSub
    change IsApproximateSubgradientAt f x 0 (dotProductEquiv ℝ (Fin n) xStar)
    refine ⟨hf, hx, ?_⟩
    -- Conversely, an exact subgradient is automatically a `0`-subgradient.
    simpa [IsSubgradientAt] using hxSub

/-- Helper for Proposition 23.6.1: a nonnegative extended real that is bounded by every positive
real must already be at most zero. -/
lemma helperForProposition_23_6_1_le_zero_of_le_all_positive
    {a : EReal}
    (ha_nonneg : 0 ≤ a)
    (ha_le : ∀ ε : {ε : NNReal // 0 < ε}, a ≤ ((ε.1 : ℝ) : EReal)) :
    a ≤ 0 := by
  by_contra hnot
  have hne : a ≠ 0 := by
    intro ha0
    exact hnot (ha0.le)
  have hlt : (0 : EReal) < a := lt_of_le_of_ne ha_nonneg hne.symm
  obtain ⟨r, hr0, hra⟩ := EReal.exists_between_coe_real hlt
  have hr_pos : 0 < r := by
    exact (EReal.coe_lt_coe_iff).1 hr0
  let ε : {ε : NNReal // 0 < ε} := ⟨⟨r, le_of_lt hr_pos⟩, by simpa using hr_pos⟩
  have hle_r : a ≤ ((r : ℝ) : EReal) := by
    simpa [ε] using ha_le ε
  exact (not_le_of_gt hra) hle_r

/-- Proposition 23.6.1: Let `f` be convex and finite at `x`, and define
`h(y) = f (x + y) - f x`. Then `h^*(xStar) = f^*(xStar) + f x - ⟪x, xStar⟫`.
Under the Euclidean identification of vectors with dual vectors, one has
`xStar ∈ ∂_ε f(x)` if and only if `h^*(xStar) ≤ ε`. In particular,
`∂_ε f(x)` is a closed convex set, it decreases as `ε` decreases, and
`⋂_{ε > 0} ∂_ε f(x) = ∂f(x)`. -/
theorem approximateSubdifferential_iff_translatedDifferenceConjugate_le_and_basic_properties
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (hf : ConvexFunction f) (x : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    (∀ xStar : Fin n → ℝ,
      fenchelConjugate n (translatedDifferenceFunctionAt f x) xStar =
        fenchelConjugate n f xStar + f x - ((dotProduct x xStar : ℝ) : EReal)) ∧
    (∀ (ε : NNReal) (xStar : Fin n → ℝ),
      dotProductEquiv ℝ (Fin n) xStar ∈ approximateSubdifferentialAt f x ε ↔
        fenchelConjugate n (translatedDifferenceFunctionAt f x) xStar ≤ ((ε : ℝ) : EReal)) ∧
    (∀ ε : NNReal,
      IsClosed ((dotProductEquiv ℝ (Fin n)) ⁻¹' approximateSubdifferentialAt f x ε)) ∧
    (∀ ε : NNReal,
      Convex ℝ ((dotProductEquiv ℝ (Fin n)) ⁻¹' approximateSubdifferentialAt f x ε)) ∧
    (∀ eps1 eps2 : NNReal,
      eps1 ≤ eps2 → approximateSubdifferentialAt f x eps1 ⊆ approximateSubdifferentialAt f x eps2) ∧
    (⋂ ε : {ε : NNReal // 0 < ε}, approximateSubdifferentialAt f x ε.1) = subdifferentialAt f x := by
  let h : (Fin n → ℝ) → EReal := translatedDifferenceFunctionAt f x
  have hclosedConvex : LowerSemicontinuous (fenchelConjugate n h) ∧ ConvexFunction (fenchelConjugate n h) :=
    fenchelConjugate_closedConvex (n := n) (f := h)
  have hpreimage_eq :
      ∀ ε : NNReal,
        ((dotProductEquiv ℝ (Fin n)) ⁻¹' approximateSubdifferentialAt f x ε) =
          (fenchelConjugate n h) ⁻¹' Set.Iic (((ε : ℝ) : EReal)) := by
    intro ε
    -- Route correction: reuse the dedicated set-equality helper instead of rebuilding the ext
    -- proof inline in the main theorem.
    simpa [h] using
      helperForProposition_23_6_1_preimage_eq_conjugateSublevel
        (f := f) hf x hx ε
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro xStar
    -- First compute the translated Fenchel conjugate explicitly.
    simpa [h] using
      helperForProposition_23_6_1_translatedDifference_fenchelConjugate
        (f := f) x hx xStar
  · intro ε xStar
    -- Then read approximate subgradients as conjugate sublevel points.
    simpa [h] using
      helperForProposition_23_6_1_mem_approximateSubdifferential_iff_conjugate_le
        (f := f) hf x hx ε xStar
  · intro ε
    -- Closedness follows because Fenchel conjugates are lower semicontinuous.
    rw [hpreimage_eq ε]
    exact
      (lowerSemicontinuous_iff_isClosed_preimage (f := fenchelConjugate n h)).1
        hclosedConvex.1 (((ε : ℝ) : EReal))
  · intro ε
    -- Convexity follows from convexity of Fenchel conjugates and convexity of sublevel sets.
    rw [hpreimage_eq ε]
    simpa [Set.preimage, Set.Iic] using
      (convexFunction_level_sets_convex (f := fenchelConjugate n h) hclosedConvex.2
        (α := (((ε : ℝ) : EReal)))).2
  · intro eps1 eps2 hε xDual hxDual
    let xStar : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm xDual
    have hxDual' : dotProductEquiv ℝ (Fin n) xStar ∈ approximateSubdifferentialAt f x eps1 := by
      simpa [xStar] using hxDual
    have hle1 :
        fenchelConjugate n h xStar ≤ ((eps1 : ℝ) : EReal) :=
      (helperForProposition_23_6_1_mem_approximateSubdifferential_iff_conjugate_le
        (f := f) hf x hx eps1 xStar).1 hxDual'
    have hle2 :
        fenchelConjugate n h xStar ≤ ((eps2 : ℝ) : EReal) :=
      le_trans hle1 (by exact_mod_cast hε)
    have hxDual'' : dotProductEquiv ℝ (Fin n) xStar ∈ approximateSubdifferentialAt f x eps2 :=
      (helperForProposition_23_6_1_mem_approximateSubdifferential_iff_conjugate_le
        (f := f) hf x hx eps2 xStar).2 hle2
    -- Increasing `ε` enlarges the corresponding conjugate sublevel set.
    simpa [xStar] using hxDual''
  · ext xDual
    let xStar : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm xDual
    constructor
    · intro hxInter
      have hle_all :
          ∀ ε : {ε : NNReal // 0 < ε},
            fenchelConjugate n h xStar ≤ ((ε.1 : ℝ) : EReal) := by
        intro ε
        have hxApprox : xDual ∈ approximateSubdifferentialAt f x ε.1 :=
          Set.mem_iInter.mp hxInter ε
        have hxApprox' : dotProductEquiv ℝ (Fin n) xStar ∈ approximateSubdifferentialAt f x ε.1 := by
          simpa [xStar] using hxApprox
        exact
          (helperForProposition_23_6_1_mem_approximateSubdifferential_iff_conjugate_le
            (f := f) hf x hx ε.1 xStar).1 hxApprox'
      have hnonneg :
          0 ≤ fenchelConjugate n h xStar := by
        simpa [h] using
          helperForProposition_23_6_1_nonneg_translatedDifferenceConjugate
            (f := f) x hx xStar
      have hle0 :
          fenchelConjugate n h xStar ≤ (0 : EReal) :=
        helperForProposition_23_6_1_le_zero_of_le_all_positive hnonneg hle_all
      have hxApprox0 : dotProductEquiv ℝ (Fin n) xStar ∈ approximateSubdifferentialAt f x 0 :=
        (helperForProposition_23_6_1_mem_approximateSubdifferential_iff_conjugate_le
          (f := f) hf x hx 0 xStar).2 hle0
      have hxSub : dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x :=
        (helperForProposition_23_6_1_approximateSubdifferential_zero_eq_subdifferential
          (f := f) hf x hx xStar).1 hxApprox0
      -- Being in every positive-`ε` set forces the `ε = 0` condition, hence true subgradient
      -- membership.
      simpa [xStar] using hxSub
    · intro hxSub
      have hxSub' : dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x := by
        simpa [xStar] using hxSub
      have hxApprox0 : dotProductEquiv ℝ (Fin n) xStar ∈ approximateSubdifferentialAt f x 0 :=
        (helperForProposition_23_6_1_approximateSubdifferential_zero_eq_subdifferential
          (f := f) hf x hx xStar).2 hxSub'
      have hle0 :
          fenchelConjugate n h xStar ≤ (0 : EReal) :=
        (helperForProposition_23_6_1_mem_approximateSubdifferential_iff_conjugate_le
          (f := f) hf x hx 0 xStar).1 hxApprox0
      refine Set.mem_iInter.2 ?_
      intro ε
      have hleε : fenchelConjugate n h xStar ≤ ((ε.1 : ℝ) : EReal) :=
        le_trans hle0 (by
          have : (0 : ℝ) ≤ ε.1 := ε.1.2
          exact_mod_cast this)
      have hxApproxε : dotProductEquiv ℝ (Fin n) xStar ∈ approximateSubdifferentialAt f x ε.1 :=
        (helperForProposition_23_6_1_mem_approximateSubdifferential_iff_conjugate_le
          (f := f) hf x hx ε.1 xStar).2 hleε
      -- A true subgradient lies in every positive approximate subdifferential.
      simpa [xStar] using hxApproxε

/-- The upper one-sided directional derivative of `f` at `x` along `d`, written as the
infimum over right neighborhoods of the supremum of the difference quotients. -/
noncomputable def upperDirectionalDerivativeAt {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x d : Fin n → ℝ) : EReal :=
  sInf ((Set.Ioi (0 : ℝ)).image fun a : ℝ =>
    sSup {q : EReal | ∃ t : ℝ, 0 < t ∧ t < a ∧ q = (f (x + t • d) - f x) / (t : EReal)})

/-- The support of the subdifferential of `f` at `x` evaluated on the direction `d`. -/
noncomputable def subdifferentialSupportAt {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x d : Fin n → ℝ) : EReal :=
  sSup ((fun g : Module.Dual ℝ (Fin n → ℝ) => ((g d : ℝ) : EReal)) '' subdifferentialAt f x)

/-- The support function of the approximate subdifferential `∂_ε f(x)` evaluated on the
direction `y`, using the Euclidean identification of `ℝⁿ` with its dual. -/
noncomputable def approximateSubdifferentialSupportAt {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) (ε : NNReal) (y : Fin n → ℝ) : EReal :=
  supportFunctionEReal ((dotProductEquiv ℝ (Fin n)) ⁻¹' approximateSubdifferentialAt f x ε) y

-- Proof sketch: evaluate the subgradient inequality at the displaced point `x + t • d`; after
-- dividing by the positive scalar `t`, every positive-step difference quotient is bounded below by
-- the pairing `⟨g, d⟩`. Taking the supremum over short steps and then the infimum over step
-- radii preserves this lower bound.
/-- Any actual subgradient yields a global linear lower bound on the upper directional derivative:
if `g ∈ ∂f(x)`, then `⟪g, d⟫ ≤ f'(x; d)` for every direction `d`. -/
theorem le_upperDirectionalDerivative_of_mem_subdifferential {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {x : Fin n → ℝ} (g : Module.Dual ℝ (Fin n → ℝ))
    (hg : g ∈ subdifferentialAt f x) (d : Fin n → ℝ) :
    ((g d : ℝ) : EReal) ≤ upperDirectionalDerivativeAt f x d := by
  have hxBot : f x ≠ (⊥ : EReal) := hf.2.2 x (by simp)
  have hxTop : f x ≠ (⊤ : EReal) := by
    rcases section13_effectiveDomain_nonempty_of_proper (n := n) (f := f) hf with ⟨z0, hz0⟩
    intro hxTop
    have hz0_ne_top :
        f z0 ≠ (⊤ : EReal) :=
      mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hz0
    have hineq : f z0 ≥ f x + ((g (z0 - x) : ℝ) : EReal) := hg z0
    have htop_le : (⊤ : EReal) ≤ f z0 := by
      have htop_rhs : f x + ((g (z0 - x) : ℝ) : EReal) = (⊤ : EReal) := by
        rw [hxTop]
        simpa using (EReal.top_add_coe (g (z0 - x)))
      exact htop_rhs ▸ hineq
    exact hz0_ne_top (top_le_iff.mp htop_le)
  have hquot_lower :
      ∀ {t : ℝ}, 0 < t →
        ((g d : ℝ) : EReal) ≤ (f (x + t • d) - f x) / (t : EReal) := by
    intro t ht
    have hsub :
        f (x + t • d) ≥ f x + (((t * g d : ℝ) : ℝ) : EReal) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hg (x + t • d)
    have hnum :
        ((((t * g d : ℝ) : ℝ) : EReal)) ≤ f (x + t • d) - f x := by
      exact
        (EReal.le_sub_iff_add_le
          (a := (((t * g d : ℝ) : ℝ) : EReal))
          (b := f x) (c := f (x + t • d))
          (Or.inl hxBot) (Or.inl hxTop)).2
          (by simpa [add_assoc, add_left_comm, add_comm] using hsub)
    have hdiv :
        ((((t * g d : ℝ) : ℝ) : EReal) / (t : EReal)) ≤
          (f (x + t • d) - f x) / (t : EReal) :=
      EReal.div_le_div_right_of_nonneg
        (by exact_mod_cast (le_of_lt ht) : (0 : EReal) ≤ (t : EReal)) hnum
    have hleft :
        ((((t * g d : ℝ) : ℝ) : EReal) / (t : EReal)) = ((g d : ℝ) : EReal) := by
      rw [← EReal.coe_div]
      field_simp [ne_of_gt ht]
    exact hleft ▸ hdiv
  let A : Set EReal :=
    (Set.Ioi (0 : ℝ)).image fun a : ℝ =>
      sSup {q : EReal | ∃ t : ℝ, 0 < t ∧ t < a ∧ q = (f (x + t • d) - f x) / (t : EReal)}
  have hA_nonempty : A.Nonempty := by
    refine ⟨sSup {q : EReal | ∃ t : ℝ, 0 < t ∧ t < (1 : ℝ) ∧
      q = (f (x + t • d) - f x) / (t : EReal)}, ?_⟩
    exact ⟨1, by norm_num, rfl⟩
  have hleA : ∀ b ∈ A, ((g d : ℝ) : EReal) ≤ b := by
    intro b hb
    rcases hb with ⟨a, ha, rfl⟩
    have ha0 : 0 < a := by simpa using ha
    have hhalf_pos : 0 < a / 2 := by linarith
    have hhalf_lt : a / 2 < a := by linarith
    exact le_trans (hquot_lower hhalf_pos) (le_sSup ⟨a / 2, hhalf_pos, hhalf_lt, rfl⟩)
  change ((g d : ℝ) : EReal) ≤ sInf A
  exact le_csInf hA_nonempty hleA

-- Proof sketch: every subgradient `g ∈ ∂f(x)` contributes the lower bound `⟪g, d⟫ ≤ f'(x; d)`;
-- taking the supremum over all such pairings yields the support-function lower bound.
/-- The support of the subdifferential is always bounded above by the upper directional derivative:
`δ^*(d | ∂f(x)) ≤ f'(x; d)`. -/
theorem subdifferentialSupportAt_le_upperDirectionalDerivative {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {x : Fin n → ℝ} (d : Fin n → ℝ) :
    subdifferentialSupportAt f x d ≤ upperDirectionalDerivativeAt f x d := by
  rw [subdifferentialSupportAt]
  refine sSup_le ?_
  rintro _ ⟨g, hg, rfl⟩
  exact le_upperDirectionalDerivative_of_mem_subdifferential f hf g hg d

/-- The directional difference quotient of `f` at `x` in the direction `y`. -/
noncomputable def directionalDifferenceQuotientAt {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x y : Fin n → ℝ) (t : ℝ) : EReal :=
  (f (x + t • y) - f x) / (t : EReal)

/-- The one-sided directional derivative of `f` at `x` along `y` is bilateral if the right and
left directional difference quotients converge to the same extended real value. -/
def HasBilateralDirectionalDerivativeAt {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x y : Fin n → ℝ) : Prop :=
  ∃ L : EReal,
    Filter.Tendsto (directionalDifferenceQuotientAt f x y) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
    Filter.Tendsto (directionalDifferenceQuotientAt f x y) (𝓝[<] (0 : ℝ)) (𝓝 L)

-- Proof sketch: rewrite the left-sided quotient along `y` by substituting `t = -λ` with
-- `λ > 0`, which identifies it with the negative of the right-sided quotient along `-y`; then
-- compare the existence of matching one-sided limits.
/-- Lemma 23.0.3: For a function `f : ℝⁿ → [-∞, +∞]` finite-valued at `x`, the left directional
difference quotient along `y` is the negative of the right directional difference quotient along
`-y`. Consequently, the right directional derivative along `y` is bilateral if and only if the
right directional derivative along `-y` exists and is the negative of the one along `y`. -/
theorem bilateralDirectionalDerivative_iff_exists_neg_direction {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x y : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    (∀ L : EReal,
      Filter.Tendsto (directionalDifferenceQuotientAt f x (-y)) (𝓝[>] (0 : ℝ)) (𝓝 L) →
        Filter.Tendsto (directionalDifferenceQuotientAt f x y) (𝓝[<] (0 : ℝ)) (𝓝 (-L))) ∧
    (HasBilateralDirectionalDerivativeAt f x y ↔
      ∃ L : EReal,
        Filter.Tendsto (directionalDifferenceQuotientAt f x y) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
        Filter.Tendsto (directionalDifferenceQuotientAt f x (-y)) (𝓝[>] (0 : ℝ)) (𝓝 (-L))) := by
  have hpoint :
      ∀ (z : Fin n → ℝ) {t : ℝ}, t ≠ 0 →
        directionalDifferenceQuotientAt f x z t =
          -directionalDifferenceQuotientAt f x (-z) (-t) := by
    intro z t ht
    simp [directionalDifferenceQuotientAt, div_eq_mul_inv, EReal.inv_neg, ht, neg_smul,
      smul_neg, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hnegArgLeft :
      Filter.Tendsto (fun t : ℝ => -t) (𝓝[<] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (fun t : ℝ => -t) ?_ ?_
    · simpa using
        (show ContinuousWithinAt (fun t : ℝ => -t) (Set.Iio (0 : ℝ)) (0 : ℝ) by fun_prop).tendsto
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using neg_pos.mpr (show t < 0 from ht)
  have hnegArgRight :
      Filter.Tendsto (fun t : ℝ => -t) (𝓝[>] (0 : ℝ)) (𝓝[<] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (fun t : ℝ => -t) ?_ ?_
    · simpa using
        (show ContinuousWithinAt (fun t : ℝ => -t) (Set.Ioi (0 : ℝ)) (0 : ℝ) by fun_prop).tendsto
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : 0 < t := by simpa using ht
      have : -t < (0 : ℝ) := by linarith
      exact this
  have hleft_from_right :
      ∀ L : EReal,
        Filter.Tendsto (directionalDifferenceQuotientAt f x (-y)) (𝓝[>] (0 : ℝ)) (𝓝 L) →
          Filter.Tendsto (directionalDifferenceQuotientAt f x y) (𝓝[<] (0 : ℝ)) (𝓝 (-L)) := by
    intro L hL
    have hcomp :
        Filter.Tendsto
          (fun t : ℝ => directionalDifferenceQuotientAt f x (-y) (-t))
          (𝓝[<] (0 : ℝ)) (𝓝 L) :=
      hL.comp hnegArgLeft
    have hneg :
        Filter.Tendsto
          (fun t : ℝ => -directionalDifferenceQuotientAt f x (-y) (-t))
          (𝓝[<] (0 : ℝ)) (𝓝 (-L)) :=
      hcomp.neg
    refine hneg.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hpoint y (show t ≠ 0 from ht.ne)).symm
  have hright_from_left :
      ∀ L : EReal,
        Filter.Tendsto (directionalDifferenceQuotientAt f x y) (𝓝[<] (0 : ℝ)) (𝓝 L) →
          Filter.Tendsto (directionalDifferenceQuotientAt f x (-y)) (𝓝[>] (0 : ℝ)) (𝓝 (-L)) := by
    intro L hL
    have hcomp :
        Filter.Tendsto
          (fun t : ℝ => directionalDifferenceQuotientAt f x y (-t))
          (𝓝[>] (0 : ℝ)) (𝓝 L) :=
      hL.comp hnegArgRight
    have hneg :
        Filter.Tendsto
          (fun t : ℝ => -directionalDifferenceQuotientAt f x y (-t))
          (𝓝[>] (0 : ℝ)) (𝓝 (-L)) :=
      hcomp.neg
    refine hneg.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simpa using (hpoint (-y) (show t ≠ 0 from ht.ne')).symm
  refine ⟨hleft_from_right, ?_⟩
  constructor
  · rintro ⟨L, hright, hleft⟩
    exact ⟨L, hright, hright_from_left L hleft⟩
  · rintro ⟨L, hright, hnegRight⟩
    exact ⟨L, hright, by simpa using hleft_from_right (-L) hnegRight⟩

/-- The Euclidean gradient vector of a scalar field on `ℝⁿ`, given by the coordinates of its
Fréchet derivative on the standard basis. -/
noncomputable def euclideanGradientAt {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (fderiv ℝ f x) (Pi.single i (1 : ℝ))

-- Proof sketch: compose the differentiability of `f` at `x` with the affine line
-- `t ↦ x + t • y`; the resulting one-variable derivative at `0` is the Fréchet derivative applied
-- to `y`, and for `ℝⁿ` this is the dot product of `y` with the coordinate gradient vector.
/-- Lemma 23.0.4: If `f : ℝⁿ → ℝ` is differentiable at `x`, then for every direction `y` the
directional derivative along the line `t ↦ x + t • y` exists as a finite bilateral derivative, and
its value is the Euclidean pairing `euclideanGradientAt f x ⬝ᵥ y`, i.e. `⟨∇ f(x), y⟩`. -/
theorem directionalDerivative_eq_dot_euclideanGradient_of_differentiableAt {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) {x y : Fin n → ℝ}
    (hfdiff : DifferentiableAt ℝ f x) :
    HasDerivAt (fun t : ℝ => f (x + t • y)) (euclideanGradientAt f x ⬝ᵥ y) 0 := by
  have hline : HasDerivAt (fun t : ℝ => f (x + t • y)) ((fderiv ℝ f x) y) 0 := by
    simpa [HasLineDerivAt] using hfdiff.hasFDerivAt.hasLineDerivAt y
  have hdot :
      (fderiv ℝ f x) y = euclideanGradientAt f x ⬝ᵥ y := by
    have hy :
        y = ∑ i : Fin n, Pi.single (M := fun _ => ℝ) i (y i) := by
      ext j
      simp
    calc
      (fderiv ℝ f x) y =
          (fderiv ℝ f x) (∑ i : Fin n, Pi.single (M := fun _ => ℝ) i (y i)) := by
        exact congrArg (fderiv ℝ f x) hy
      _ = ∑ i : Fin n, (fderiv ℝ f x) (Pi.single (M := fun _ => ℝ) i (y i)) := by
        rw [map_sum]
      _ = ∑ i : Fin n, y i * (fderiv ℝ f x) (Pi.single (M := fun _ => ℝ) i (1 : ℝ)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [show Pi.single (M := fun _ => ℝ) i (y i) =
            y i • Pi.single (M := fun _ => ℝ) i (1 : ℝ) by
              ext j
              by_cases h : j = i
              · subst h
                simp
              · simp [h]]
        rw [map_smul]
        simp [smul_eq_mul]
      _ = euclideanGradientAt f x ⬝ᵥ y := by
        simp [euclideanGradientAt, dotProduct, mul_comm]
  simpa [hdot] using hline

-- Proof sketch: use the secant-slope monotonicity of convex functions along the affine line
-- `λ ↦ x + λ • y` to show that the right difference quotient is monotone on `(0, ∞)` and thus has
-- a limit equal to its infimum; then apply the same convexity argument in the direction variable to
-- obtain convexity and positive homogeneity of the directional derivative, from which the inequality
-- `-f'(x;-y) ≤ f'(x;y)` and the normalization at `0` follow.
/-- Helper for Theorem 23.1: the right directional difference quotient is monotone in the step
length. -/
lemma helperForTheorem_23_1_differenceQuotient_monotone {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hf : ConvexFunction f) (x y : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    MonotoneOn (directionalDifferenceQuotientAt f x y) (Set.Ioi (0 : ℝ)) := by
  -- Route correction: the earlier properness pivot is stronger than the current hypotheses in
  -- this development, so we prove secant-slope monotonicity directly from epigraph convexity.
  change ∀ ⦃l⦄, l ∈ Set.Ioi (0 : ℝ) →
      ∀ ⦃m⦄, m ∈ Set.Ioi (0 : ℝ) →
        l ≤ m → directionalDifferenceQuotientAt f x y l ≤ directionalDifferenceQuotientAt f x y m
  intro l hl m hm hlm
  have hl0 : 0 < l := by simpa using hl
  have hm0 : 0 < m := by simpa using hm
  by_cases hEq : l = m
  · simpa [hEq]
  · have hlt : l < m := lt_of_le_of_ne hlm hEq
    have hratio_nonneg : 0 ≤ l / m := by positivity
    have hratio_le_one : l / m ≤ 1 := (div_le_one hm0).2 hlm
    have hratio_pos : 0 < l / m := by positivity
    -- Rewrite the shorter step as a convex combination of the base point and the longer step.
    have hline :
        x + l • y = (1 - l / m) • x + (l / m) • (x + m • y) := by
      ext i
      have hmne : m ≠ 0 := ne_of_gt hm0
      calc
        (x + l • y) i = x i + l * y i := by simp [smul_eq_mul]
        _ = (1 - l / m) * x i + (l / m) * (x i + m * y i) := by
          field_simp [hmne]
          ring
        _ = ((1 - l / m) • x + (l / m) • (x + m • y)) i := by
          simp [smul_eq_mul, mul_add]
    let vx : ℝ := (f x).toReal
    have hx_epi : (x, vx) ∈ epigraph (Set.univ : Set (Fin n → ℝ)) f := by
      refine epigraph_mem_of_le_aux (S := (Set.univ : Set (Fin n → ℝ))) (x := x) (μ := vx)
        (by simp) ?_
      change f x ≤ ((f x).toReal : EReal)
      rw [EReal.coe_toReal hx.1 hx.2]
    by_cases htop : f (x + m • y) = (⊤ : EReal)
    · -- If the longer-step value is `⊤`, the longer quotient is `⊤`, so the comparison is trivial.
      have hdq_top : directionalDifferenceQuotientAt f x y m = ⊤ := by
        rw [directionalDifferenceQuotientAt, htop]
        simp [hx.1]
        exact EReal.top_div_of_pos_ne_top (by exact_mod_cast hm0) (by simp)
      rw [hdq_top]
      exact le_top
    · by_cases hbot : f (x + m • y) = (⊥ : EReal)
      · -- If the longer-step value is `⊥`, every interior point of the segment lies below every
        -- real epigraph height, hence its value is also `⊥`.
        have hforall : ∀ r : ℝ, f (x + l • y) ≤ (r : EReal) := by
          intro r
          let beta : ℝ := (r - (1 - l / m) * vx) / (l / m)
          have hy_epi : (x + m • y, beta) ∈ epigraph (Set.univ : Set (Fin n → ℝ)) f := by
            refine epigraph_mem_of_le_aux (S := (Set.univ : Set (Fin n → ℝ)))
              (x := x + m • y) (μ := beta) (by simp) ?_
            rw [hbot]
            exact bot_le
          have hcombo :=
            convex_combo_mem_epigraph_aux (S := (Set.univ : Set (Fin n → ℝ)))
              (hconv := by simpa [ConvexFunction] using hf)
              (hx := hx_epi) (hy := hy_epi) hratio_nonneg hratio_le_one
          have hseg :=
            (epigraph_combo_proj_aux (S := (Set.univ : Set (Fin n → ℝ))) (f := f)
              (x := x) (y := x + m • y) (μ := vx) (v := beta) (t := l / m) hcombo).2
          rw [← hline] at hseg
          have hbeta : (1 - l / m) * vx + (l / m) * beta = r := by
            have hratio_ne : l / m ≠ 0 := by positivity
            dsimp [beta]
            field_simp [hratio_ne]
            ring
          simpa [hbeta] using hseg
        have hlbot_val : f (x + l • y) = (⊥ : EReal) := by
          by_cases hltop : f (x + l • y) = (⊤ : EReal)
          · have hzero := hforall 0
            rw [hltop] at hzero
            exact (not_top_le_coe 0 hzero).elim
          · by_cases hlbot : f (x + l • y) = (⊥ : EReal)
            · exact hlbot
            · have hbelow := hforall ((f (x + l • y)).toReal - 1)
              have hbelow' :
                  (((f (x + l • y)).toReal : ℝ) : EReal) ≤
                    (((f (x + l • y)).toReal - 1 : ℝ) : EReal) := by
                simpa [EReal.coe_toReal hltop hlbot] using hbelow
              have hreal : (f (x + l • y)).toReal ≤ (f (x + l • y)).toReal - 1 := by
                exact (EReal.coe_le_coe_iff).1 hbelow'
              linarith
        have hdq_l : directionalDifferenceQuotientAt f x y l = ⊥ := by
          rw [directionalDifferenceQuotientAt, hlbot_val]
          simp
          exact EReal.bot_div_of_pos_ne_top (by exact_mod_cast hl0) (by simp)
        have hdq_m : directionalDifferenceQuotientAt f x y m = ⊥ := by
          rw [directionalDifferenceQuotientAt, hbot]
          simp
          exact EReal.bot_div_of_pos_ne_top (by exact_mod_cast hm0) (by simp)
        rw [hdq_l, hdq_m]
      · -- In the finite longer-step branch, the convex combination gives a finite real upper bound.
        let vm : ℝ := (f (x + m • y)).toReal
        have hm_epi : (x + m • y, vm) ∈ epigraph (Set.univ : Set (Fin n → ℝ)) f := by
          refine epigraph_mem_of_le_aux (S := (Set.univ : Set (Fin n → ℝ)))
            (x := x + m • y) (μ := vm) (by simp) ?_
          change f (x + m • y) ≤ ((f (x + m • y)).toReal : EReal)
          rw [EReal.coe_toReal htop hbot]
        have hcombo :=
          convex_combo_mem_epigraph_aux (S := (Set.univ : Set (Fin n → ℝ)))
            (hconv := by simpa [ConvexFunction] using hf)
            (hx := hx_epi) (hy := hm_epi) hratio_nonneg hratio_le_one
        have hseg :=
          (epigraph_combo_proj_aux (S := (Set.univ : Set (Fin n → ℝ))) (f := f)
            (x := x) (y := x + m • y) (μ := vx) (v := vm) (t := l / m) hcombo).2
        rw [← hline] at hseg
        by_cases hlbot : f (x + l • y) = (⊥ : EReal)
        · -- If the shorter-step value is `⊥`, its quotient is already minimal.
          have hdq_l : directionalDifferenceQuotientAt f x y l = ⊥ := by
            rw [directionalDifferenceQuotientAt, hlbot]
            simp
            exact EReal.bot_div_of_pos_ne_top (by exact_mod_cast hl0) (by simp)
          rw [hdq_l]
          exact bot_le
        · -- Otherwise both endpoint values are finite, so the remaining comparison is real algebra.
          have hltop : f (x + l • y) ≠ (⊤ : EReal) := by
            intro hltop
            rw [hltop] at hseg
            exact (not_top_le_coe (((1 - l / m) * (f x).toReal + (l / m) * (f (x + m • y)).toReal))
              hseg)
          have hseg' :
              (((f (x + l • y)).toReal : ℝ) : EReal) ≤
                (((1 - l / m) * (f x).toReal + (l / m) * (f (x + m • y)).toReal : ℝ) : EReal) := by
            simpa [EReal.coe_toReal hltop hlbot] using hseg
          have hreal :
              (f (x + l • y)).toReal ≤
                (1 - l / m) * (f x).toReal + (l / m) * (f (x + m • y)).toReal := by
            exact_mod_cast hseg'
          have hquot_real :
              (((f (x + l • y)).toReal - (f x).toReal) / l : ℝ) ≤
                (((f (x + m • y)).toReal - (f x).toReal) / m : ℝ) := by
            have hmne : m ≠ 0 := ne_of_gt hm0
            have hlne : l ≠ 0 := ne_of_gt hl0
            field_simp [hmne, hlne] at hreal ⊢
            nlinarith
          have hquot_ereal :
              ((((f (x + l • y)).toReal - (f x).toReal) / l : ℝ) : EReal) ≤
                ((((f (x + m • y)).toReal - (f x).toReal) / m : ℝ) : EReal) := by
            exact_mod_cast hquot_real
          simpa [directionalDifferenceQuotientAt, EReal.coe_div, EReal.coe_sub,
            EReal.coe_toReal hltop hlbot, EReal.coe_toReal htop hbot, EReal.coe_toReal hx.1 hx.2]
            using hquot_ereal

/-- Helper for Theorem 23.1: the upper directional derivative equals the infimum of the positive
difference quotients. -/
lemma helperForTheorem_23_1_upperDerivative_eq_sInf_differenceQuotients {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x y : Fin n → ℝ)
    (hmono : MonotoneOn (directionalDifferenceQuotientAt f x y) (Set.Ioi (0 : ℝ))) :
    upperDirectionalDerivativeAt f x y =
      sInf ((Set.Ioi (0 : ℝ)).image fun t : ℝ => directionalDifferenceQuotientAt f x y t) := by
  let q : ℝ → EReal := directionalDifferenceQuotientAt f x y
  let A : Set EReal :=
    (Set.Ioi (0 : ℝ)).image fun a : ℝ =>
      sSup {r : EReal | ∃ t : ℝ, 0 < t ∧ t < a ∧ r = q t}
  have hQ_bdd :
      BddBelow ((Set.Ioi (0 : ℝ)).image fun t : ℝ => q t) := by
    refine ⟨⊥, ?_⟩
    intro z hz
    simp
  have hQ_nonempty :
      ((Set.Ioi (0 : ℝ)).image fun t : ℝ => q t).Nonempty := by
    refine ⟨q 1, ?_⟩
    refine ⟨1, by simpa, rfl⟩
  have hA_nonempty : A.Nonempty := by
    refine ⟨sSup {r : EReal | ∃ t : ℝ, 0 < t ∧ t < (1 : ℝ) ∧ r = q t}, ?_⟩
    refine ⟨1, by simpa, rfl⟩
  have hupper_le_q :
      ∀ a : ℝ, 0 < a → upperDirectionalDerivativeAt f x y ≤ q a := by
    intro a ha
    have hA_bdd : BddBelow A := ⟨⊥, by intro z hz; simp⟩
    have hsInf_le :
        upperDirectionalDerivativeAt f x y ≤
          sSup {r : EReal | ∃ t : ℝ, 0 < t ∧ t < a ∧ r = q t} := by
      simpa [upperDirectionalDerivativeAt, A] using
        (csInf_le hA_bdd (by exact ⟨a, ha, rfl⟩))
    have hsSup_le_q :
        sSup {r : EReal | ∃ t : ℝ, 0 < t ∧ t < a ∧ r = q t} ≤ q a := by
      refine sSup_le ?_
      intro r hr
      rcases hr with ⟨t, ht0, hta, rfl⟩
      exact hmono ht0 ha (le_of_lt hta)
    exact le_trans hsInf_le hsSup_le_q
  have hq_le_upper :
      sInf ((Set.Ioi (0 : ℝ)).image fun t : ℝ => q t) ≤ upperDirectionalDerivativeAt f x y := by
    have hA_bdd : BddBelow A := ⟨⊥, by intro z hz; simp⟩
    refine le_csInf hA_nonempty ?_
    intro b hb
    rcases hb with ⟨a, ha, rfl⟩
    have ha0 : 0 < a := by
      simpa [Set.mem_Ioi] using ha
    have hhalf_pos : 0 < a / 2 := by
      nlinarith [ha0]
    have hhalf_lt : a / 2 < a := by
      nlinarith [ha0]
    have hqhalf :
        q (a / 2) ∈ {r : EReal | ∃ t : ℝ, 0 < t ∧ t < a ∧ r = q t} := by
      exact ⟨a / 2, hhalf_pos, hhalf_lt, rfl⟩
    have hqhalf_lower :
        sInf ((Set.Ioi (0 : ℝ)).image fun t : ℝ => q t) ≤ q (a / 2) := by
      exact csInf_le hQ_bdd (by exact ⟨a / 2, hhalf_pos, rfl⟩)
    exact le_trans hqhalf_lower (le_sSup hqhalf)
  have hupper_is_lower :
      ∀ b ∈ (Set.Ioi (0 : ℝ)).image fun t : ℝ => q t,
        upperDirectionalDerivativeAt f x y ≤ b := by
    intro b hb
    rcases hb with ⟨a, ha, rfl⟩
    exact hupper_le_q a ha
  have hupper_ge_q :
      upperDirectionalDerivativeAt f x y ≤
        sInf ((Set.Ioi (0 : ℝ)).image fun t : ℝ => q t) := by
    exact le_csInf hQ_nonempty hupper_is_lower
  exact le_antisymm hupper_ge_q hq_le_upper

/-- Helper for Theorem 23.1: monotone right quotients converge to the upper directional
derivative. -/
lemma helperForTheorem_23_1_tendsto_upperDerivative {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x y : Fin n → ℝ)
    (hmono : MonotoneOn (directionalDifferenceQuotientAt f x y) (Set.Ioi (0 : ℝ))) :
    Filter.Tendsto (directionalDifferenceQuotientAt f x y) (𝓝[>] (0 : ℝ))
      (𝓝 (upperDirectionalDerivativeAt f x y)) := by
  have hbdd :
      BddBelow ((directionalDifferenceQuotientAt f x y) '' Set.Ioi (0 : ℝ)) := by
    refine ⟨⊥, ?_⟩
    intro z hz
    simp
  have htend :
      Filter.Tendsto (directionalDifferenceQuotientAt f x y) (𝓝[>] (0 : ℝ))
        (𝓝 (sInf ((directionalDifferenceQuotientAt f x y) '' Set.Ioi (0 : ℝ)))) :=
    MonotoneOn.tendsto_nhdsGT hmono hbdd
  -- The derivative formula identifies this order-theoretic limit with the textbook expression.
  simpa [helperForTheorem_23_1_upperDerivative_eq_sInf_differenceQuotients
      f x y hmono] using htend

/-- Helper for Theorem 23.1: the upper directional derivative vanishes in the zero direction. -/
lemma helperForTheorem_23_1_upperDerivative_zero {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    upperDirectionalDerivativeAt f x 0 = 0 := by
  have hmono :
      MonotoneOn (directionalDifferenceQuotientAt f x 0) (Set.Ioi (0 : ℝ)) := by
    intro s hs t ht hst
    rw [directionalDifferenceQuotientAt, directionalDifferenceQuotientAt]
    simp [EReal.sub_self hx.1 hx.2]
  -- The zero-direction quotient family is constant, so its infimum is zero.
  rw [helperForTheorem_23_1_upperDerivative_eq_sInf_differenceQuotients f x 0 hmono]
  simp [directionalDifferenceQuotientAt, EReal.sub_self hx.1 hx.2]

/-- Helper for Theorem 23.1: rescaling the direction rescales the positive-step quotient. -/
lemma helperForTheorem_23_1_scaledDifferenceQuotient_rescale {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x y : Fin n → ℝ) (a t : ℝ)
    (ha : 0 < a) (ht : 0 < t) :
    directionalDifferenceQuotientAt f x (a • y) t =
      ((a : ℝ) : EReal) * directionalDifferenceQuotientAt f x y (a * t) := by
  -- Rewrite both quotients with the common numerator `f (x + (a * t) • y) - f x`.
  let z : EReal := f (x + (a * t) • y) - f x
  have haE : (0 : EReal) < (a : EReal) := by
    exact_mod_cast ha
  have ha_bot : ((a : ℝ) : EReal) ≠ ⊥ := ne_bot_of_gt haE
  have ha_top : ((a : ℝ) : EReal) ≠ ⊤ := by
    simp
  have ha_zero : ((a : ℝ) : EReal) ≠ 0 := by
    exact_mod_cast (ne_of_gt ha)
  calc
    directionalDifferenceQuotientAt f x (a • y) t = z / (t : EReal) := by
      simp [directionalDifferenceQuotientAt, z, smul_smul, mul_comm]
    _ = z * ((a : ℝ) : EReal) / (((t : ℝ) : EReal) * ((a : ℝ) : EReal)) := by
      -- Insert the cancelling factor `a / a` so the denominator matches the rescaled step.
      nth_rewrite 1 [← EReal.mul_div_mul_cancel
        (a := z) (b := (t : EReal)) (c := ((a : ℝ) : EReal)) ha_bot ha_top ha_zero]
      rw [mul_comm]
    _ = z * ((a : ℝ) : EReal) / (((a : ℝ) : EReal) * ((t : ℝ) : EReal)) := by
      rw [mul_comm ((t : ℝ) : EReal) ((a : ℝ) : EReal)]
    _ = ((a : ℝ) : EReal) * (z / (((a * t : ℝ) : EReal))) := by
      -- Now the denominator is exactly the step `a * t`, so the quotient factors cleanly.
      rw [EReal.mul_div, mul_comm z ((a : ℝ) : EReal), EReal.coe_mul, mul_comm]
    _ = ((a : ℝ) : EReal) * directionalDifferenceQuotientAt f x y (a * t) := by
      simp [directionalDifferenceQuotientAt, z]

/-- Helper for Theorem 23.1: strict real upper bounds for two directional derivatives can be
realized at one common positive step. -/
lemma helperForTheorem_23_1_commonPositiveStep_below_real_bounds {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x y₁ y₂ : Fin n → ℝ)
    (hmono₁ : MonotoneOn (directionalDifferenceQuotientAt f x y₁) (Set.Ioi (0 : ℝ)))
    (hmono₂ : MonotoneOn (directionalDifferenceQuotientAt f x y₂) (Set.Ioi (0 : ℝ)))
    {μ ν : ℝ}
    (hμ : upperDirectionalDerivativeAt f x y₁ < (μ : EReal))
    (hν : upperDirectionalDerivativeAt f x y₂ < (ν : EReal)) :
    ∃ t : ℝ, 0 < t ∧ directionalDifferenceQuotientAt f x y₁ t < (μ : EReal) ∧
      directionalDifferenceQuotientAt f x y₂ t < (ν : EReal) := by
  let Q₁ : Set EReal := (Set.Ioi (0 : ℝ)).image fun t : ℝ => directionalDifferenceQuotientAt f x y₁ t
  let Q₂ : Set EReal := (Set.Ioi (0 : ℝ)).image fun t : ℝ => directionalDifferenceQuotientAt f x y₂ t
  have hQ₁_bdd : BddBelow Q₁ := by
    refine ⟨⊥, ?_⟩
    intro z hz
    simp [Q₁] at hz ⊢
  have hQ₂_bdd : BddBelow Q₂ := by
    refine ⟨⊥, ?_⟩
    intro z hz
    simp [Q₂] at hz ⊢
  have hQ₁_nonempty : Q₁.Nonempty := by
    refine ⟨directionalDifferenceQuotientAt f x y₁ 1, ?_⟩
    exact ⟨1, by simpa, rfl⟩
  have hQ₂_nonempty : Q₂.Nonempty := by
    refine ⟨directionalDifferenceQuotientAt f x y₂ 1, ?_⟩
    exact ⟨1, by simpa, rfl⟩
  have hμ' : sInf Q₁ < (μ : EReal) := by
    simpa [Q₁, helperForTheorem_23_1_upperDerivative_eq_sInf_differenceQuotients f x y₁ hmono₁]
      using hμ
  have hν' : sInf Q₂ < (ν : EReal) := by
    simpa [Q₂, helperForTheorem_23_1_upperDerivative_eq_sInf_differenceQuotients f x y₂ hmono₂]
      using hν
  rcases (csInf_lt_iff hQ₁_bdd hQ₁_nonempty).1 hμ' with ⟨q₁, hq₁mem, hq₁lt⟩
  rcases (csInf_lt_iff hQ₂_bdd hQ₂_nonempty).1 hν' with ⟨q₂, hq₂mem, hq₂lt⟩
  rcases hq₁mem with ⟨t₁, ht₁, rfl⟩
  rcases hq₂mem with ⟨t₂, ht₂, rfl⟩
  refine ⟨min t₁ t₂, lt_min (by simpa using ht₁) (by simpa using ht₂), ?_, ?_⟩
  · -- Monotonicity lets us shrink the first witness down to the common minimum step.
    exact lt_of_le_of_lt
      (hmono₁ (by simpa using lt_min (by simpa using ht₁) (by simpa using ht₂)) ht₁ (min_le_left _ _))
      hq₁lt
  · -- The same shrinking argument works for the second witness.
    exact lt_of_le_of_lt
      (hmono₂ (by simpa using lt_min (by simpa using ht₁) (by simpa using ht₂)) ht₂ (min_le_right _ _))
      hq₂lt

/-- Helper for Theorem 23.1: the upper directional derivative is positively homogeneous in the
direction argument. -/
lemma helperForTheorem_23_1_upperDerivative_posHom_direct {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hf : ConvexFunction f) (x : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    PositivelyHomogeneous (upperDirectionalDerivativeAt f x) := by
  intro y a ha
  let D : (Fin n → ℝ) → EReal := upperDirectionalDerivativeAt f x
  have hscale_le :
      ∀ {c : ℝ}, 0 < c → ∀ z : Fin n → ℝ, ((c : ℝ) : EReal) * D z ≤ D (c • z) := by
    intro c hc z
    let Qz : Set EReal := (Set.Ioi (0 : ℝ)).image fun t : ℝ => directionalDifferenceQuotientAt f x z t
    have hmono_z := helperForTheorem_23_1_differenceQuotient_monotone f hf x z hx
    have hmono_cz := helperForTheorem_23_1_differenceQuotient_monotone f hf x (c • z) hx
    have hQz_bdd : BddBelow Qz := by
      refine ⟨⊥, ?_⟩
      intro q hq
      simp [Qz] at hq ⊢
    have hQc_nonempty :
        ((Set.Ioi (0 : ℝ)).image fun t : ℝ => directionalDifferenceQuotientAt f x (c • z) t).Nonempty := by
      refine ⟨directionalDifferenceQuotientAt f x (c • z) 1, ?_⟩
      exact ⟨1, by simpa, rfl⟩
    -- Compare the derivative with each quotient at the rescaled step `c * t`.
    change ((c : ℝ) : EReal) * D z ≤ upperDirectionalDerivativeAt f x (c • z)
    rw [helperForTheorem_23_1_upperDerivative_eq_sInf_differenceQuotients f x (c • z) hmono_cz]
    refine le_csInf hQc_nonempty ?_
    intro b hb
    rcases hb with ⟨t, ht, rfl⟩
    have ht0 : 0 < t := by
      simpa using ht
    have hDz_le : D z ≤ directionalDifferenceQuotientAt f x z (c * t) := by
      change upperDirectionalDerivativeAt f x z ≤ directionalDifferenceQuotientAt f x z (c * t)
      rw [helperForTheorem_23_1_upperDerivative_eq_sInf_differenceQuotients f x z hmono_z]
      exact csInf_le hQz_bdd (by exact ⟨c * t, mul_pos hc ht0, rfl⟩)
    have hmul :
        ((c : ℝ) : EReal) * D z ≤
          ((c : ℝ) : EReal) * directionalDifferenceQuotientAt f x z (c * t) := by
      exact mul_le_mul_of_nonneg_left hDz_le (by exact_mod_cast (le_of_lt hc) :
        (0 : EReal) ≤ ((c : ℝ) : EReal))
    -- The quotient rescaling identity converts the right-hand side to the target quotient.
    calc
      ((c : ℝ) : EReal) * D z ≤
          ((c : ℝ) : EReal) * directionalDifferenceQuotientAt f x z (c * t) := hmul
      _ = directionalDifferenceQuotientAt f x (c • z) t := by
        symm
        exact helperForTheorem_23_1_scaledDifferenceQuotient_rescale f x z c t hc ht0
  have hforward : ((a : ℝ) : EReal) * D y ≤ D (a • y) := by
    simpa [D] using hscale_le ha y
  have hia : 0 < 1 / a := by
    positivity
  have hback_raw : (((1 / a : ℝ) : EReal) * D (a • y)) ≤ D y := by
    -- Apply the one-sided scaling inequality to the inverse scalar and the already scaled direction.
    simpa [D, smul_smul, inv_mul_cancel₀ (ne_of_gt ha)] using hscale_le hia (a • y)
  have hback_mul :
      ((a : ℝ) : EReal) * ((((1 / a : ℝ) : EReal) * D (a • y))) ≤
        ((a : ℝ) : EReal) * D y := by
    exact mul_le_mul_of_nonneg_left hback_raw (by exact_mod_cast (le_of_lt ha) :
      (0 : EReal) ≤ ((a : ℝ) : EReal))
  have hcoef : ((a : ℝ) : EReal) * (((1 / a : ℝ) : EReal)) = (1 : EReal) := by
    have hcoef_real : a * (1 / a) = (1 : ℝ) := by
      field_simp [ne_of_gt ha]
    simpa [EReal.coe_mul] using congrArg (fun r : ℝ => ((r : ℝ) : EReal)) hcoef_real
  have hcancel :
      ((a : ℝ) : EReal) * ((((1 / a : ℝ) : EReal) * D (a • y))) = D (a • y) := by
    calc
      ((a : ℝ) : EReal) * ((((1 / a : ℝ) : EReal) * D (a • y))) =
          ((((a : ℝ) : EReal) * (((1 / a : ℝ) : EReal))) * D (a • y)) := by
            rw [mul_assoc]
      _ = (1 : EReal) * D (a • y) := by
        rw [hcoef]
      _ = D (a • y) := by
        simp
  have hback : D (a • y) ≤ ((a : ℝ) : EReal) * D y := by
    -- Multiply the inverse-scaling inequality back by `a` and cancel the coefficient.
    calc
      D (a • y) = ((a : ℝ) : EReal) * ((((1 / a : ℝ) : EReal) * D (a • y))) := by
        symm
        exact hcancel
      _ ≤ ((a : ℝ) : EReal) * D y := hback_mul
  exact le_antisymm hback hforward

/-- Helper for Theorem 23.1: a real upper bound on one positive-step quotient gives a real upper
bound on the corresponding function value. -/
lemma helperForTheorem_23_1_valueBound_of_differenceQuotient_le_real {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x y : Fin n → ℝ) (t : ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) (ht : 0 < t) {μ : ℝ}
    (hq : directionalDifferenceQuotientAt f x y t ≤ (μ : EReal)) :
    f (x + t • y) ≤ (((f x).toReal + t * μ : ℝ) : EReal) := by
  -- Convert the quotient bound into a real inequality once the stepped value is finite.
  by_cases hbot : f (x + t • y) = (⊥ : EReal)
  · rw [hbot]
    exact bot_le
  have htop : f (x + t • y) ≠ (⊤ : EReal) := by
    intro htop
    have hqTop : directionalDifferenceQuotientAt f x y t = (⊤ : EReal) := by
      rw [directionalDifferenceQuotientAt, htop]
      simp [hx.1]
      exact EReal.top_div_of_pos_ne_top (by exact_mod_cast ht) (by simp)
    rw [hqTop] at hq
    exact (not_top_le_coe μ hq).elim
  have hqReal :
      ((((f (x + t • y)).toReal - (f x).toReal) / t : ℝ) : EReal) ≤ (μ : EReal) := by
    simpa [directionalDifferenceQuotientAt, EReal.coe_div, EReal.coe_sub,
      EReal.coe_toReal htop hbot, EReal.coe_toReal hx.1 hx.2] using hq
  have hqReal' : ((f (x + t • y)).toReal - (f x).toReal) / t ≤ μ := by
    exact_mod_cast hqReal
  have hvalueReal : (f (x + t • y)).toReal ≤ (f x).toReal + t * μ := by
    have htne : t ≠ 0 := ne_of_gt ht
    field_simp [htne] at hqReal' ⊢
    nlinarith
  -- Route correction: we transport the bound through `toReal` only after ruling out `⊤`/`⊥`.
  rw [← EReal.coe_toReal htop hbot]
  exact_mod_cast hvalueReal

/-- Helper for Theorem 23.1: a real upper bound on the function value at one positive step gives
the same real upper bound on the corresponding difference quotient. -/
lemma helperForTheorem_23_1_differenceQuotient_le_real_of_valueBound {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x y : Fin n → ℝ) (t : ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) (ht : 0 < t) {μ : ℝ}
    (hvalue : f (x + t • y) ≤ (((f x).toReal + t * μ : ℝ) : EReal)) :
    directionalDifferenceQuotientAt f x y t ≤ (μ : EReal) := by
  -- The quotient inequality is the same real inequality after undoing the division by `t > 0`.
  by_cases hbot : f (x + t • y) = (⊥ : EReal)
  · have hqBot : directionalDifferenceQuotientAt f x y t = (⊥ : EReal) := by
      rw [directionalDifferenceQuotientAt, hbot]
      simp [EReal.bot_div_of_pos_ne_top
        (show (0 : EReal) < ((t : ℝ) : EReal) by exact_mod_cast ht)
        (show (((t : ℝ) : EReal)) ≠ (⊤ : EReal) by simp)]
    rw [hqBot]
    exact bot_le
  have htop : f (x + t • y) ≠ (⊤ : EReal) := by
    intro htop
    rw [htop] at hvalue
    exact (not_top_le_coe (((f x).toReal + t * μ : ℝ)) hvalue).elim
  have hvalueReal :
      (((f (x + t • y)).toReal : ℝ) : EReal) ≤
        ((((f x).toReal + t * μ : ℝ) : ℝ) : EReal) := by
    simpa [EReal.coe_toReal htop hbot] using hvalue
  have hvalueReal' : (f (x + t • y)).toReal ≤ (f x).toReal + t * μ := by
    exact_mod_cast hvalueReal
  have hqReal :
      ((f (x + t • y)).toReal - (f x).toReal) / t ≤ μ := by
    have htne : t ≠ 0 := ne_of_gt ht
    field_simp [htne] at hvalueReal' ⊢
    nlinarith
  have hqRealE :
      ((((f (x + t • y)).toReal - (f x).toReal) / t : ℝ) : EReal) ≤ (μ : EReal) := by
    exact_mod_cast hqReal
  simpa [directionalDifferenceQuotientAt, EReal.coe_div, EReal.coe_sub,
    EReal.coe_toReal htop hbot, EReal.coe_toReal hx.1 hx.2] using hqRealE

/-- Helper for Theorem 23.1: one common positive-step real bound on the endpoint quotients yields
the corresponding convex-combination real bound on the mixed quotient. -/
lemma helperForTheorem_23_1_pointwiseDifferenceQuotient_convexCombination_realBound {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hf : ConvexFunction f) (x y₁ y₂ : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    {s t μ ν : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 < t)
    (hq₁ : directionalDifferenceQuotientAt f x y₁ t ≤ (μ : EReal))
    (hq₂ : directionalDifferenceQuotientAt f x y₂ t ≤ (ν : EReal)) :
    directionalDifferenceQuotientAt f x ((1 - s) • y₁ + s • y₂) t ≤
      ((((1 - s) * μ + s * ν : ℝ)) : EReal) := by
  let mix : Fin n → ℝ := (1 - s) • y₁ + s • y₂
  let α : ℝ := (f x).toReal + t * μ
  let β : ℝ := (f x).toReal + t * ν
  have hvalue₁ :
      f (x + t • y₁) ≤ (α : EReal) :=
    helperForTheorem_23_1_valueBound_of_differenceQuotient_le_real f x y₁ t hx ht hq₁
  have hvalue₂ :
      f (x + t • y₂) ≤ (β : EReal) :=
    helperForTheorem_23_1_valueBound_of_differenceQuotient_le_real f x y₂ t hx ht hq₂
  have hline :
      x + t • mix = (1 - s) • (x + t • y₁) + s • (x + t • y₂) := by
    ext i
    simp [mix, smul_eq_mul]
    ring
  have hconv :
      Convex ℝ (epigraph (Set.univ : Set (Fin n → ℝ)) f) := by
    simpa [ConvexFunction] using hf
  have hmixValue :
      f (x + t • mix) ≤ (((1 - s) * α + s * β : ℝ) : EReal) := by
    have hraw :=
      epigraph_combo_ineq_aux (S := (Set.univ : Set (Fin n → ℝ))) (f := f)
        (x := x + t • y₁) (y := x + t • y₂) (μ := α) (v := β) hconv
        (by simp) (by simp) hvalue₁ hvalue₂ hs0 hs1
    simpa [hline] using hraw
  have hcoeff :
      (1 - s) * α + s * β = (f x).toReal + t * (((1 - s) * μ + s * ν)) := by
    dsimp [α, β]
    ring
  have hmixValue' :
      f (x + t • mix) ≤
        (((f x).toReal + t * (((1 - s) * μ + s * ν)) : ℝ) : EReal) := by
    simpa [hcoeff] using hmixValue
  -- The affine value bound is converted back into the desired quotient bound.
  simpa [mix] using
    helperForTheorem_23_1_differenceQuotient_le_real_of_valueBound f x mix t hx ht hmixValue'

end Section23
end Chap05

/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part4

open scoped Topology

section Chap05
section Section23

/-- Membership of `xStar` in the Euclidean subdifferential of `f` at `x`, via the dot-product
identification of `ℝⁿ` with its dual. -/
def IsEuclideanSubgradientAt {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x xStar : Fin n → ℝ) : Prop :=
  dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x

/-- The primal Fenchel expression `z ↦ ⟪z, xStar⟫ - f z` attains its supremum at `z = x`. -/
def PrimalFenchelSupremumAttainedAt {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x xStar : Fin n → ℝ) : Prop :=
  ∀ z : Fin n → ℝ,
    ((dotProduct z xStar : ℝ) : EReal) - f z ≤
      ((dotProduct x xStar : ℝ) : EReal) - f x

/-- The dual Fenchel expression `zStar ↦ ⟪x, zStar⟫ - f^*(zStar)` attains its supremum at
`zStar = xStar`. -/
def DualFenchelSupremumAttainedAt {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x xStar : Fin n → ℝ) : Prop :=
  ∀ zStar : Fin n → ℝ,
    ((dotProduct x zStar : ℝ) : EReal) - fenchelConjugate n f zStar ≤
      ((dotProduct x xStar : ℝ) : EReal) - fenchelConjugate n f xStar

/-- The Fenchel-Young inequality at `(x, xStar)` written as a weak inequality. -/
def FenchelYoungInequalityAt {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x xStar : Fin n → ℝ) : Prop :=
  f x + fenchelConjugate n f xStar ≤ ((dotProduct x xStar : ℝ) : EReal)

/-- The Fenchel-Young equality at `(x, xStar)`. -/
def FenchelYoungEqualityAt {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x xStar : Fin n → ℝ) : Prop :=
  f x + fenchelConjugate n f xStar = ((dotProduct x xStar : ℝ) : EReal)

/-- Helper for Theorem 23.5: a Euclidean subgradient at `x` forces `f x` to be finite. -/
lemma helperForTheorem_23_5_finiteAt_of_euclideanSubgradient {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x xStar : Fin n → ℝ) (ha : IsEuclideanSubgradientAt f x xStar) :
    f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) := by
  -- A proper convex function never takes the value `⊥`, so only `⊤` must be excluded.
  refine ⟨?_, hf.2.2 x (by simp)⟩
  obtain ⟨z0, r0, hz0⟩ := properConvexFunctionOn_exists_finite_point (n := n) (f := f) hf
  intro htop
  -- Evaluate the subgradient inequality at a finite witness to rule out `f x = ⊤`.
  change IsSubgradientAt f x (dotProductEquiv ℝ (Fin n) xStar) at ha
  have hineq := ha z0
  rw [htop, hz0] at hineq
  have htop_le : (⊤ : EReal) ≤ (r0 : EReal) := by
    have haux :
        (⊤ : EReal) + (((dotProductEquiv ℝ (Fin n) xStar) (z0 - x) : ℝ) : EReal) =
          (⊤ : EReal) :=
      EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)
    exact haux ▸ hineq
  simp at htop_le

/-- Helper for Theorem 23.5: Fenchel-Young inequality at `x` also forces `f x` to be finite. -/
lemma helperForTheorem_23_5_finiteAt_of_fenchelYoungInequality {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x xStar : Fin n → ℝ) (hc : FenchelYoungInequalityAt f x xStar) :
    f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) := by
  -- Properness again removes the `⊥` case, so the work is to exclude `⊤`.
  refine ⟨?_, hf.2.2 x (by simp)⟩
  obtain ⟨x0, r0, hx0⟩ := properConvexFunctionOn_exists_finite_point (n := n) (f := f) hf
  have hExists : ∃ z : Fin n → ℝ, f z ≠ (⊤ : EReal) := by
    refine ⟨x0, ?_⟩
    rw [hx0]
    simp
  have hfc_ne_bot : fenchelConjugate n f xStar ≠ (⊥ : EReal) :=
    fenchelConjugate_ne_bot_of_exists_ne_top (n := n) (f := f) hExists xStar
  intro htop
  -- If `f x = ⊤`, the left side of Fenchel-Young is `⊤`, contradicting the finite right side.
  have hxy : f x + fenchelConjugate n f xStar ≤ ((dotProduct x xStar : ℝ) : EReal) := by
    simpa [FenchelYoungInequalityAt] using hc
  rw [htop, EReal.top_add_of_ne_bot hfc_ne_bot] at hxy
  simp at hxy

/-- Helper for Theorem 23.5: subgradient membership is equivalent to the Fenchel-Young inequality
at the same point. -/
lemma helperForTheorem_23_5_euclideanSubgradient_iff_fenchelYoungInequality {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x xStar : Fin n → ℝ) :
    IsEuclideanSubgradientAt f x xStar ↔ FenchelYoungInequalityAt f x xStar := by
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hf.1
  constructor
  · intro ha
    have hx := helperForTheorem_23_5_finiteAt_of_euclideanSubgradient f hf x xStar ha
    -- The translated-difference conjugate characterization converts exact subgradients into a
    -- `≤ 0` statement, which is exactly Fenchel-Young.
    rcases
        approximateSubdifferential_iff_translatedDifferenceConjugate_le_and_basic_properties
          (f := f) hfConv x hx with
      ⟨htrans, happ, _, _, _, _⟩
    have hApprox : dotProductEquiv ℝ (Fin n) xStar ∈ approximateSubdifferentialAt f x 0 := by
      have hSub : IsSubgradientAt f x (dotProductEquiv ℝ (Fin n) xStar) := by
        simpa using ha
      change IsApproximateSubgradientAt f x 0 (dotProductEquiv ℝ (Fin n) xStar)
      refine ⟨hfConv, hx, ?_⟩
      simpa [IsSubgradientAt] using hSub
    have hle0 : fenchelConjugate n (translatedDifferenceFunctionAt f x) xStar ≤ (0 : EReal) :=
      (happ 0 xStar).1 hApprox
    rw [htrans xStar] at hle0
    have hle : fenchelConjugate n f xStar + f x ≤ ((dotProduct x xStar : ℝ) : EReal) :=
      (EReal.sub_nonpos).1 hle0
    simpa [FenchelYoungInequalityAt, add_comm, add_left_comm, add_assoc] using hle
  · intro hc
    have hx := helperForTheorem_23_5_finiteAt_of_fenchelYoungInequality f hf x xStar hc
    -- Run the same translated-difference characterization in reverse.
    rcases
        approximateSubdifferential_iff_translatedDifferenceConjugate_le_and_basic_properties
          (f := f) hfConv x hx with
      ⟨htrans, happ, _, _, _, _⟩
    have hxy : fenchelConjugate n f xStar + f x ≤ ((dotProduct x xStar : ℝ) : EReal) := by
      simpa [FenchelYoungInequalityAt, add_comm, add_left_comm, add_assoc] using hc
    have hle0 : fenchelConjugate n (translatedDifferenceFunctionAt f x) xStar ≤ (0 : EReal) := by
      rw [htrans xStar]
      exact (EReal.sub_nonpos).2 hxy
    have hApprox : dotProductEquiv ℝ (Fin n) xStar ∈ approximateSubdifferentialAt f x 0 :=
      (happ 0 xStar).2 hle0
    have hApprox' : IsApproximateSubgradientAt f x 0 (dotProductEquiv ℝ (Fin n) xStar) := by
      simpa using hApprox
    change IsSubgradientAt f x (dotProductEquiv ℝ (Fin n) xStar)
    simpa [IsApproximateSubgradientAt, IsSubgradientAt] using hApprox'.2.2

/-- Helper for Theorem 23.5: primal supremum attainment is equivalent to the Fenchel-Young weak
inequality. -/
lemma helperForTheorem_23_5_primalSupremumAttainedAt_iff_fenchelYoungInequality {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x xStar : Fin n → ℝ) :
    PrimalFenchelSupremumAttainedAt f x xStar ↔ FenchelYoungInequalityAt f x xStar := by
  constructor
  · intro hb
    -- Bounding every affine piece bounds the supremum defining the conjugate.
    have hsup : fenchelConjugate n f xStar ≤ ((dotProduct x xStar : ℝ) : EReal) - f x := by
      rw [fenchelConjugate_eq_iSup]
      exact iSup_le hb
    have hle :=
      (EReal.le_sub_iff_add_le (a := fenchelConjugate n f xStar) (b := f x)
        (c := ((dotProduct x xStar : ℝ) : EReal)) (Or.inr (by simp)) (Or.inr (by simp))).1 hsup
    simpa [FenchelYoungInequalityAt, add_comm, add_left_comm, add_assoc] using hle
  · intro hc z
    -- Conversely, the supremum property of `f*` gives the pointwise attainment bound.
    have hz : ((dotProduct z xStar : ℝ) : EReal) - f z ≤ fenchelConjugate n f xStar := by
      rw [fenchelConjugate]
      exact le_sSup ⟨z, rfl⟩
    have hsup : fenchelConjugate n f xStar ≤ ((dotProduct x xStar : ℝ) : EReal) - f x := by
      have hxy : f x + fenchelConjugate n f xStar ≤ ((dotProduct x xStar : ℝ) : EReal) := by
        simpa [FenchelYoungInequalityAt, add_comm, add_left_comm, add_assoc] using hc
      exact (EReal.le_sub_iff_add_le (a := fenchelConjugate n f xStar) (b := f x)
        (c := ((dotProduct x xStar : ℝ) : EReal)) (Or.inr (by simp)) (Or.inr (by simp))).2
        (by simpa [add_comm, add_left_comm, add_assoc] using hxy)
    exact le_trans hz hsup

/-- Helper for Theorem 23.5: the four basic conditions are equivalent. -/
theorem helperForTheorem_23_5_fourWayTFAE {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x xStar : Fin n → ℝ) :
    List.TFAE
      [ IsEuclideanSubgradientAt f x xStar
      , PrimalFenchelSupremumAttainedAt f x xStar
      , FenchelYoungInequalityAt f x xStar
      , FenchelYoungEqualityAt f x xStar
      ] := by
  -- The proof is organized around the weak Fenchel-Young inequality as the central condition.
  tfae_have 1 ↔ 3 :=
    helperForTheorem_23_5_euclideanSubgradient_iff_fenchelYoungInequality f hf x xStar
  tfae_have 2 ↔ 3 :=
    helperForTheorem_23_5_primalSupremumAttainedAt_iff_fenchelYoungInequality f x xStar
  tfae_have 3 ↔ 4 := by
    constructor
    · intro hc
      -- Fenchel's general inequality upgrades the weak inequality to equality.
      have hfy : ((dotProduct x xStar : ℝ) : EReal) ≤ f x + fenchelConjugate n f xStar :=
        fenchel_inequality n f hf x xStar
      exact le_antisymm hc hfy
    · intro hd
      exact le_of_eq hd
  tfae_finish

/-- Helper for Theorem 23.5: primal attainment for `f*` is the same statement as dual attainment
for `f`. -/
lemma helperForTheorem_23_5_primalSupremumAttainedAt_conjugate_iff_dualSupremumAttainedAt
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (x xStar : Fin n → ℝ) :
    PrimalFenchelSupremumAttainedAt (fenchelConjugate n f) xStar x ↔
      DualFenchelSupremumAttainedAt f x xStar := by
  -- This is only a reindexing of the variables together with symmetry of the dot product.
  constructor <;> intro h zStar <;>
    simpa [PrimalFenchelSupremumAttainedAt, DualFenchelSupremumAttainedAt, dotProduct_comm] using
      h zStar

/-- Helper for Theorem 23.5: under `(cl f)(x) = f(x)`, Fenchel-Young equality for `f*` is the
same as for `f`. -/
lemma helperForTheorem_23_5_fenchelYoungEqualityAt_conjugate_iff_original {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hfConv : ConvexFunction f)
    (x xStar : Fin n → ℝ) (hclx : convexFunctionClosure f x = f x) :
    FenchelYoungEqualityAt (fenchelConjugate n f) xStar x ↔ FenchelYoungEqualityAt f x xStar := by
  -- Replace the biconjugate by the closure, then use the hypothesis that the closure agrees at
  -- the base point.
  constructor <;> intro h
  · rw [FenchelYoungEqualityAt] at h ⊢
    rw [section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure (n := n) (f := f) hfConv,
      hclx, dotProduct_comm] at h
    simpa [add_comm, add_left_comm, add_assoc] using h
  · rw [FenchelYoungEqualityAt] at h ⊢
    rw [section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure (n := n) (f := f) hfConv,
      hclx, dotProduct_comm]
    simpa [add_comm, add_left_comm, add_assoc] using h

/-- Helper for Theorem 23.5: under `(cl f)(x) = f(x)`, Fenchel-Young equality for `cl f` is the
same as for `f`. -/
lemma helperForTheorem_23_5_fenchelYoungEqualityAt_closure_iff_original {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x xStar : Fin n → ℝ)
    (hclx : convexFunctionClosure f x = f x) :
    FenchelYoungEqualityAt (convexFunctionClosure f) x xStar ↔ FenchelYoungEqualityAt f x xStar := by
  -- The closure and the original function have the same conjugate, so only the value at `x`
  -- needs to be transported.
  constructor <;> intro h
  · rw [FenchelYoungEqualityAt] at h ⊢
    rw [fenchelConjugate_eq_of_convexFunctionClosure (n := n) (f := f), hclx] at h
    simpa [add_comm, add_left_comm, add_assoc] using h
  · rw [FenchelYoungEqualityAt] at h ⊢
    rw [fenchelConjugate_eq_of_convexFunctionClosure (n := n) (f := f), hclx]
    simpa [add_comm, add_left_comm, add_assoc] using h

/-- Theorem 23.5: For a proper convex function `f` and points `x` and `xStar` in `ℝⁿ`, the
following four conditions are equivalent in the `List.TFAE` sense: (a) `xStar ∈ ∂f(x)` under the
Euclidean identification, (b) `z ↦ ⟪z, xStar⟫ - f z` attains its supremum at `z = x`, (c) the
Fenchel-Young inequality `f x + f^*(xStar) ≤ ⟪x, xStar⟫`, and (d) the Fenchel-Young equality
`f x + f^*(xStar) = ⟪x, xStar⟫`. Furthermore, if `(cl f)(x) = f(x)`, then the enlarged list
consisting of these conditions together with (a*) `x ∈ ∂f^*(xStar)`, (b*) `zStar ↦ ⟪x, zStar⟫ -
f^*(zStar)` attains its supremum at `zStar = xStar`, and (a**) `xStar ∈ ∂(cl f)(x)` is again a
`List.TFAE`. -/
theorem euclidean_subgradient_iff_fenchel_supremum_attainment_and_fenchelYoung
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x xStar : Fin n → ℝ) :
    List.TFAE
      [ IsEuclideanSubgradientAt f x xStar
      , PrimalFenchelSupremumAttainedAt f x xStar
      , FenchelYoungInequalityAt f x xStar
      , FenchelYoungEqualityAt f x xStar
      ] ∧
    (convexFunctionClosure f x = f x →
      List.TFAE
        [ IsEuclideanSubgradientAt f x xStar
        , PrimalFenchelSupremumAttainedAt f x xStar
        , FenchelYoungInequalityAt f x xStar
        , FenchelYoungEqualityAt f x xStar
        , IsEuclideanSubgradientAt (fenchelConjugate n f) xStar x
        , DualFenchelSupremumAttainedAt f x xStar
        , IsEuclideanSubgradientAt (convexFunctionClosure f) x xStar
        ]) := by
  have hFour := helperForTheorem_23_5_fourWayTFAE f hf x xStar
  refine ⟨hFour, ?_⟩
  intro hclx
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hf.1
  have hFourConjugate :=
    helperForTheorem_23_5_fourWayTFAE (fenchelConjugate n f)
      (proper_fenchelConjugate_of_proper (n := n) (f := f) hf) xStar x
  have hClosureProper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (convexFunctionClosure f) :=
    (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri (f := f) hf).1.2
  have hFourClosure :=
    helperForTheorem_23_5_fourWayTFAE (convexFunctionClosure f) hClosureProper x xStar
  -- Each extra clause is transported back to the original Fenchel-Young equality.
  tfae_have 1 ↔ 4 := by
    simpa using hFour.out 0 3
  tfae_have 2 ↔ 4 := by
    simpa using hFour.out 1 3
  tfae_have 3 ↔ 4 := by
    simpa using hFour.out 2 3
  tfae_have 5 ↔ 4 := by
    exact (hFourConjugate.out 0 3).trans
      (helperForTheorem_23_5_fenchelYoungEqualityAt_conjugate_iff_original f hfConv x xStar hclx)
  tfae_have 6 ↔ 4 := by
    exact
      (helperForTheorem_23_5_primalSupremumAttainedAt_conjugate_iff_dualSupremumAttainedAt
        f x xStar).symm.trans <|
      (hFourConjugate.out 1 3).trans
        (helperForTheorem_23_5_fenchelYoungEqualityAt_conjugate_iff_original
          f hfConv x xStar hclx)
  tfae_have 7 ↔ 4 := by
    exact (hFourClosure.out 0 3).trans
      (helperForTheorem_23_5_fenchelYoungEqualityAt_closure_iff_original f x xStar hclx)
  tfae_finish

/-- Helper for Corollary 23.5.1: a closed proper convex function agrees pointwise with its
closure. -/
lemma helperForCorollary_23_5_1_closure_eq_at_point
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x : Fin n → ℝ) :
    convexFunctionClosure f x = f x := by
  -- Properness excludes the value `⊥`, which is the missing hypothesis for the closure theorem.
  have hnotbot : ∀ y : Fin n → ℝ, f y ≠ (⊥ : EReal) := by
    intro y
    have hy : y ∈ (Set.univ : Set (Fin n → ℝ)) := by
      simp
    exact hproper.2.2 y hy
  -- Specializing the function equality at `x` gives the pointwise identity needed later.
  exact congrArg (fun g : (Fin n → ℝ) → EReal => g x)
    (convexFunctionClosure_eq_of_closedConvexFunction (f := f) hclosed hnotbot)

/-- Helper for Corollary 23.5.1: Theorem 23.5 identifies the original and conjugate Euclidean
subgradient conditions once closure agrees with the function at the base point. -/
lemma helperForCorollary_23_5_1_extract_tfae_equivalence
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x xStar : Fin n → ℝ) :
    IsEuclideanSubgradientAt (fenchelConjugate n f) xStar x ↔
      IsEuclideanSubgradientAt f x xStar := by
  -- Feed the closure agreement into Theorem 23.5 to obtain the seven-way equivalence.
  have hTFAE :=
    (euclidean_subgradient_iff_fenchel_supremum_attainment_and_fenchelYoung
      f hproper x xStar).2
      (helperForCorollary_23_5_1_closure_eq_at_point f hclosed hproper x)
  -- In that list, condition 5 is the conjugate subgradient statement and condition 1 is the
  -- original subgradient statement.
  simpa using hTFAE.out 4 0

/-- Corollary 23.5.1: If `f` is a closed proper convex function, then the subdifferential of the
Fenchel conjugate is the inverse of the subdifferential of `f` in the sense of set-valued
mapping, i.e. `x ∈ ∂f^*(xStar)` if and only if `xStar ∈ ∂f(x)`. -/
theorem euclidean_subgradient_fenchelConjugate_iff
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x xStar : Fin n → ℝ) :
    IsEuclideanSubgradientAt (fenchelConjugate n f) xStar x ↔
      IsEuclideanSubgradientAt f x xStar := by
  -- This corollary is exactly the `5 ↔ 1` slice of Theorem 23.5 after identifying `cl f` with `f`.
  exact helperForCorollary_23_5_1_extract_tfae_equivalence f hclosed hproper x xStar

/-- Helper for Corollary 23.5.2: one Euclidean subgradient witness already forces the closure to
agree with `f` at the base point. -/
lemma helperForCorollary_23_5_2_closure_eq_at_point_of_euclideanSubgradient
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x xStar : Fin n → ℝ) (hsubE : IsEuclideanSubgradientAt f x xStar) :
    convexFunctionClosure f x = f x := by
  have hfyEq :
      FenchelYoungEqualityAt f x xStar :=
    ((euclidean_subgradient_iff_fenchel_supremum_attainment_and_fenchelYoung
      f hproper x xStar).1.out 0 3).1 hsubE
  have hfyEq' :
      f x + fenchelConjugate n f xStar = ((dotProduct x xStar : ℝ) : EReal) := by
    simpa [FenchelYoungEqualityAt] using hfyEq
  have hxFinite :=
    helperForTheorem_23_5_finiteAt_of_euclideanSubgradient f hproper x xStar hsubE
  have hconj_ne_top : fenchelConjugate n f xStar ≠ (⊤ : EReal) := by
    intro htop
    -- The Fenchel-Young equality has a finite right-hand side, so the conjugate cannot be `⊤`.
    have hsum_top : f x + fenchelConjugate n f xStar = (⊤ : EReal) := by
      rw [htop]
      exact (EReal.add_top_iff_ne_bot).2 hxFinite.2
    exact EReal.coe_ne_top (dotProduct x xStar) (hfyEq'.symm.trans hsum_top)
  have hconj_ne_bot : fenchelConjugate n f xStar ≠ (⊥ : EReal) := by
    intro hbot
    -- The same equality also rules out `⊥` for the conjugate term.
    have hsum_bot : f x + fenchelConjugate n f xStar = (⊥ : EReal) := by
      simp [hbot]
    exact EReal.coe_ne_bot (dotProduct x xStar) (hfyEq'.symm.trans hsum_bot)
  have hclosureProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (convexFunctionClosure f) :=
    (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri (f := f) hproper).1.2
  have hclosureFenchel :
      ((dotProduct x xStar : ℝ) : EReal) ≤
        convexFunctionClosure f x + fenchelConjugate n f xStar := by
    -- Apply Fenchel's inequality to `cl f`, then replace its conjugate by the original one.
    simpa [fenchelConjugate_eq_of_convexFunctionClosure (n := n) (f := f)] using
      (fenchel_inequality n (convexFunctionClosure f) hclosureProper x xStar)
  have hfx_le_hcl : f x ≤ convexFunctionClosure f x := by
    -- Cancel the common finite conjugate term on the right.
    have hsum_le :
        f x + fenchelConjugate n f xStar ≤
          convexFunctionClosure f x + fenchelConjugate n f xStar := by
      rw [hfyEq']
      exact hclosureFenchel
    exact
      (WithBot.add_le_add_iff_right'
        (a := f x) (b := convexFunctionClosure f x) (c := fenchelConjugate n f xStar)
        hconj_ne_bot hconj_ne_top).1 hsum_le
  -- Combine the reverse inequality above with the universal closure bound.
  exact le_antisymm ((convexFunctionClosure_le_self (f := f)) x) hfx_le_hcl

/-- Helper for Corollary 23.5.2: once `cl f` agrees with `f` at `x`, Theorem 23.5 identifies
their Euclidean subgradient conditions at that point. -/
lemma helperForCorollary_23_5_2_euclideanSubgradient_closure_iff_original
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x xStar : Fin n → ℝ) (hclx : convexFunctionClosure f x = f x) :
    IsEuclideanSubgradientAt (convexFunctionClosure f) x xStar ↔
      IsEuclideanSubgradientAt f x xStar := by
  -- Feed the pointwise closure agreement into the seven-way equivalence from Theorem 23.5.
  have hTFAE :=
    (euclidean_subgradient_iff_fenchel_supremum_attainment_and_fenchelYoung
      f hproper x xStar).2 hclx
  -- Item `7` is the closure-subgradient condition, while item `1` is the original one.
  simpa using hTFAE.out 6 0

/-- Helper for Corollary 23.5.2: pointwise equivalence of Euclidean subgradient predicates gives
equality of the corresponding dual-valued subdifferentials. -/
lemma helperForCorollary_23_5_2_subdifferential_eq_of_euclidean_equiv
    {n : ℕ} (f g : (Fin n → ℝ) → EReal) (x : Fin n → ℝ)
    (hEq : ∀ xStar : Fin n → ℝ, IsEuclideanSubgradientAt f x xStar ↔ IsEuclideanSubgradientAt g x xStar) :
    subdifferentialAt f x = subdifferentialAt g x := by
  ext xDual
  -- Transport both membership statements through the Euclidean dot-product equivalence.
  constructor
  · intro hxDual
    have hxDual' :
        IsEuclideanSubgradientAt f x ((dotProductEquiv ℝ (Fin n)).symm xDual) := by
      simpa [IsEuclideanSubgradientAt] using hxDual
    have hxDual'' :
        IsEuclideanSubgradientAt g x ((dotProductEquiv ℝ (Fin n)).symm xDual) :=
      (hEq ((dotProductEquiv ℝ (Fin n)).symm xDual)).1 hxDual'
    simpa [IsEuclideanSubgradientAt] using hxDual''
  · intro hxDual
    have hxDual' :
        IsEuclideanSubgradientAt g x ((dotProductEquiv ℝ (Fin n)).symm xDual) := by
      simpa [IsEuclideanSubgradientAt] using hxDual
    have hxDual'' :
        IsEuclideanSubgradientAt f x ((dotProductEquiv ℝ (Fin n)).symm xDual) :=
      (hEq ((dotProductEquiv ℝ (Fin n)).symm xDual)).2 hxDual'
    simpa [IsEuclideanSubgradientAt] using hxDual''

/-- Corollary 23.5.2: If `f` is a proper convex function and subdifferentiable at `x`, then the
closure of `f` agrees with `f` at `x`, and the subdifferential of the closure agrees with the
subdifferential of `f` at `x`. -/
theorem convexFunctionClosure_eq_at_subdifferentiable_point_and_subdifferential_eq
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x : Fin n → ℝ) (hsub : Set.Nonempty (subdifferentialAt f x)) :
    convexFunctionClosure f x = f x ∧
      subdifferentialAt (convexFunctionClosure f) x = subdifferentialAt f x := by
  rcases hsub with ⟨xDual, hxDual⟩
  let xStar : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm xDual
  have hsubE : IsEuclideanSubgradientAt f x xStar := by
    -- Rewrite the dual witness in Euclidean coordinates.
    change dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x
    simpa [xStar] using hxDual
  have hclx :=
    helperForCorollary_23_5_2_closure_eq_at_point_of_euclideanSubgradient
      f hproper x xStar hsubE
  have hEq :
      ∀ yStar : Fin n → ℝ,
        IsEuclideanSubgradientAt (convexFunctionClosure f) x yStar ↔
          IsEuclideanSubgradientAt f x yStar := by
    intro yStar
    -- The closure and the original function now share the same Euclidean subgradients at `x`.
    exact
      helperForCorollary_23_5_2_euclideanSubgradient_closure_iff_original
        f hproper x yStar hclx
  refine ⟨hclx, ?_⟩
  -- Translate the Euclidean equivalence back to equality of the dual subdifferential sets.
  exact
    helperForCorollary_23_5_2_subdifferential_eq_of_euclidean_equiv
      (f := convexFunctionClosure f) (g := f) x hEq

/-- Helper for Corollary 23.5.3: the support-function subgradient condition transports through the
indicator/support conjugacy of a closed convex set. -/
lemma helperForCorollary_23_5_3_supportSubgradient_iff_indicatorSubgradient
    {n : ℕ} (C : Set (Fin n → ℝ)) (hCne : C.Nonempty) (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C) (xStar x : Fin n → ℝ) :
    IsEuclideanSubgradientAt (supportFunctionEReal C) xStar x ↔
      IsEuclideanSubgradientAt (indicatorFunction C) x xStar := by
  let hSupport :=
    section13_supportFunctionEReal_closedProperConvex_posHom (n := n) (C := C) hCne hCconv
  have hConj :
      fenchelConjugate n (supportFunctionEReal C) = indicatorFunction C :=
    (indicatorFunction_conjugate_supportFunctionEReal_of_isClosed
      (n := n) (C := C) hCconv hCclosed).2
  -- Corollary 23.5.1 turns support-function subgradients into conjugate subgradients.
  calc
    IsEuclideanSubgradientAt (supportFunctionEReal C) xStar x ↔
        IsEuclideanSubgradientAt (fenchelConjugate n (supportFunctionEReal C)) x xStar := by
          exact
            (euclidean_subgradient_fenchelConjugate_iff
              (n := n) (f := supportFunctionEReal C) hSupport.1 hSupport.2.1 xStar x).symm
    _ ↔ IsEuclideanSubgradientAt (indicatorFunction C) x xStar := by
          simp [hConj]

/-- Helper for Corollary 23.5.3: for an indicator function, Theorem 23.5 identifies Euclidean
subgradients with primal Fenchel supremum attainment. -/
lemma helperForCorollary_23_5_3_indicatorSubgradient_iff_primalSupremumAttained
    {n : ℕ} (C : Set (Fin n → ℝ)) (hCne : C.Nonempty) (hCconv : Convex ℝ C)
    (x xStar : Fin n → ℝ) :
    IsEuclideanSubgradientAt (indicatorFunction C) x xStar ↔
      PrimalFenchelSupremumAttainedAt (indicatorFunction C) x xStar := by
  have hIndicatorProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (indicatorFunction C) :=
    properConvexFunctionOn_indicator_of_convex_of_nonempty (C := C) hCconv hCne
  have hTFAE :=
    (euclidean_subgradient_iff_fenchel_supremum_attainment_and_fenchelYoung
      (f := indicatorFunction C) hIndicatorProper x xStar).1
  -- The first two entries of Theorem 23.5 are the desired two conditions.
  simpa using hTFAE.out 0 1

/-- Helper for Corollary 23.5.3: primal attainment for the indicator function says exactly that
`x` lies in `C` and maximizes `z ↦ ⟪z, xStar⟫` over `C`. -/
lemma helperForCorollary_23_5_3_indicatorPrimalSupremumAttained_iff_mem_and_maximizes
    {n : ℕ} (C : Set (Fin n → ℝ)) (hCne : C.Nonempty) (x xStar : Fin n → ℝ) :
    PrimalFenchelSupremumAttainedAt (indicatorFunction C) x xStar ↔
      x ∈ C ∧ ∀ z ∈ C, dotProduct z xStar ≤ dotProduct x xStar := by
  constructor
  · intro hPrimal
    by_cases hxC : x ∈ C
    · refine ⟨hxC, ?_⟩
      intro z hzC
      -- On `C`, the indicator vanishes, so the attainment inequality becomes a real comparison.
      have hzE :
          (((dotProduct z xStar : ℝ) : EReal) ≤ ((dotProduct x xStar : ℝ) : EReal)) := by
        simpa [indicatorFunction, hxC, hzC] using hPrimal z
      exact EReal.coe_le_coe_iff.1 hzE
    · rcases hCne with ⟨c, hcC⟩
      -- If `x ∉ C`, evaluating the attainment inequality at a point of `C` forces a finite
      -- extended real to be `≤ ⊥`, which is impossible.
      have hc : (((dotProduct c xStar : ℝ) : EReal) ≤ (⊥ : EReal)) := by
        simpa [indicatorFunction, hcC, hxC] using hPrimal c
      exfalso
      exact EReal.coe_ne_bot _ ((le_bot_iff.mp hc))
  · rintro ⟨hxC, hMax⟩ z
    by_cases hzC : z ∈ C
    · -- For points of `C`, the primal inequality is exactly the maximality inequality.
      have hzE :
          (((dotProduct z xStar : ℝ) : EReal) ≤ ((dotProduct x xStar : ℝ) : EReal)) := by
        exact_mod_cast hMax z hzC
      simpa [indicatorFunction, hxC, hzC] using hzE
    · -- Off `C`, the indicator is `⊤`, so the left-hand side is `⊥`.
      simp [indicatorFunction, hxC, hzC]

/-- Corollary 23.5.3: Let `C` be a nonempty closed convex set. Then for each vector `xStar`, the
subdifferential of the support function `δ^*(· | C)` at `xStar` consists exactly of the points
`x ∈ C` where the linear function `z ↦ ⟪z, xStar⟫` attains its maximum over `C`. -/
theorem euclidean_subgradient_supportFunctionEReal_iff_mem_and_maximizes_on_closed_convex_set
    {n : ℕ} (C : Set (Fin n → ℝ)) (hCne : C.Nonempty) (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C) (xStar x : Fin n → ℝ) :
    IsEuclideanSubgradientAt (supportFunctionEReal C) xStar x ↔
      x ∈ C ∧ ∀ z ∈ C, dotProduct z xStar ≤ dotProduct x xStar := by
  -- Transport the support-function subgradient to the indicator function, then rewrite the
  -- indicator condition as primal attainment and finally as a maximum principle on `C`.
  calc
    IsEuclideanSubgradientAt (supportFunctionEReal C) xStar x ↔
        IsEuclideanSubgradientAt (indicatorFunction C) x xStar :=
      helperForCorollary_23_5_3_supportSubgradient_iff_indicatorSubgradient
        C hCne hCclosed hCconv xStar x
    _ ↔ PrimalFenchelSupremumAttainedAt (indicatorFunction C) x xStar :=
      helperForCorollary_23_5_3_indicatorSubgradient_iff_primalSupremumAttained
        C hCne hCconv x xStar
    _ ↔ x ∈ C ∧ ∀ z ∈ C, dotProduct z xStar ≤ dotProduct x xStar :=
      helperForCorollary_23_5_3_indicatorPrimalSupremumAttained_iff_mem_and_maximizes
        C hCne x xStar

/-- The Euclidean polar cone of `K`, namely the vectors whose dot product with every point of `K`
is nonpositive. -/
def euclideanPolarCone {n : ℕ} (K : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {xStar | ∀ x ∈ K, dotProduct x xStar ≤ 0}

/-- Helper for Corollary 23.5.4: a maximizer of `z ↦ ⟪z, xStar⟫` on a convex cone is orthogonal
to `xStar`. -/
lemma helperForCorollary_23_5_4_dotProduct_eq_zero_of_mem_and_maximizes_on_cone
    {n : ℕ} (K : ConvexCone ℝ (Fin n → ℝ)) {x xStar : Fin n → ℝ}
    (hxK : x ∈ (K : Set (Fin n → ℝ)))
    (hMax : ∀ z ∈ (K : Set (Fin n → ℝ)), dotProduct z xStar ≤ dotProduct x xStar) :
    dotProduct x xStar = 0 := by
  have hzero_le : 0 ≤ dotProduct x xStar := by
    -- Compare `x` with the smaller positive multiple `(1 / 2) • x`.
    have hhalf :
        dotProduct ((1 / 2 : ℝ) • x) xStar ≤ dotProduct x xStar :=
      hMax ((1 / 2 : ℝ) • x) (K.smul_mem (by norm_num) hxK)
    have hhalf' : (1 / 2 : ℝ) * dotProduct x xStar ≤ dotProduct x xStar := by
      simpa [dotProduct_smul, smul_eq_mul] using hhalf
    linarith
  have hxx_le_zero : dotProduct x xStar ≤ 0 := by
    -- Compare `x` with the larger positive multiple `2 • x`.
    have hdouble :
        dotProduct ((2 : ℝ) • x) xStar ≤ dotProduct x xStar :=
      hMax ((2 : ℝ) • x) (K.smul_mem (by norm_num) hxK)
    have hdouble' : (2 : ℝ) * dotProduct x xStar ≤ dotProduct x xStar := by
      simpa [dotProduct_smul, smul_eq_mul] using hdouble
    linarith
  exact le_antisymm hxx_le_zero hzero_le

/-- Helper for Corollary 23.5.4: once the maximizing point is orthogonal to `xStar`, the same
maximality inequality forces `xStar` into the Euclidean polar cone. -/
lemma helperForCorollary_23_5_4_mem_polar_of_mem_and_maximizes_on_cone
    {n : ℕ} (K : ConvexCone ℝ (Fin n → ℝ)) {x xStar : Fin n → ℝ}
    (hxK : x ∈ (K : Set (Fin n → ℝ)))
    (hMax : ∀ z ∈ (K : Set (Fin n → ℝ)), dotProduct z xStar ≤ dotProduct x xStar)
    (horth : dotProduct x xStar = 0) :
    xStar ∈ euclideanPolarCone (K : Set (Fin n → ℝ)) := by
  intro z hzK
  -- Evaluate maximality at `x + z ∈ K` and then cancel the vanishing `⟪x, xStar⟫` term.
  have hsum :
      dotProduct (x + z) xStar ≤ dotProduct x xStar :=
    hMax (x + z) (K.add_mem hxK hzK)
  have hsum' : dotProduct x xStar + dotProduct z xStar ≤ dotProduct x xStar := by
    simpa [dotProduct_add] using hsum
  simpa [horth] using hsum'

/-- Helper for Corollary 23.5.4: maximality of `z ↦ ⟪z, xStar⟫` on a convex cone is equivalent
to polar membership together with orthogonality at the maximizing point. -/
lemma helperForCorollary_23_5_4_mem_and_maximizes_on_cone_iff_polar_and_orthogonality
    {n : ℕ} (K : ConvexCone ℝ (Fin n → ℝ)) (x xStar : Fin n → ℝ) :
    x ∈ (K : Set (Fin n → ℝ)) ∧
        (∀ z ∈ (K : Set (Fin n → ℝ)), dotProduct z xStar ≤ dotProduct x xStar) ↔
      x ∈ (K : Set (Fin n → ℝ)) ∧
        xStar ∈ euclideanPolarCone (K : Set (Fin n → ℝ)) ∧
          dotProduct x xStar = 0 := by
  constructor
  · rintro ⟨hxK, hMax⟩
    -- First isolate the orthogonality forced by cone scaling.
    have horth :
        dotProduct x xStar = 0 :=
      helperForCorollary_23_5_4_dotProduct_eq_zero_of_mem_and_maximizes_on_cone
        K hxK hMax
    -- Then use the additive cone structure to derive polar membership.
    have hxStarPolar :
        xStar ∈ euclideanPolarCone (K : Set (Fin n → ℝ)) :=
      helperForCorollary_23_5_4_mem_polar_of_mem_and_maximizes_on_cone
        K hxK hMax horth
    exact ⟨hxK, hxStarPolar, horth⟩
  · rintro ⟨hxK, hxStarPolar, horth⟩
    refine ⟨hxK, ?_⟩
    intro z hzK
    -- Polar membership already gives the required upper bound, and orthogonality identifies it
    -- with the value at the maximizing point.
    have hz_nonpos : dotProduct z xStar ≤ 0 := hxStarPolar z hzK
    simpa [horth] using hz_nonpos

/-- Helper for Corollary 23.5.4: the indicator-function subgradient condition for a closed convex
cone is equivalent to primal membership, polar membership, and orthogonality. -/
lemma helperForCorollary_23_5_4_indicatorSubgradient_iff_mem_polar_orthogonal
    {n : ℕ} (K : ConvexCone ℝ (Fin n → ℝ))
    (hKne : (K : Set (Fin n → ℝ)).Nonempty)
    (x xStar : Fin n → ℝ) :
    IsEuclideanSubgradientAt (indicatorFunction (K : Set (Fin n → ℝ))) x xStar ↔
      x ∈ (K : Set (Fin n → ℝ)) ∧
        xStar ∈ euclideanPolarCone (K : Set (Fin n → ℝ)) ∧
          dotProduct x xStar = 0 := by
  have hKconv : Convex ℝ (K : Set (Fin n → ℝ)) := by
    simpa using K.convex
  -- Route correction: use Corollary 23.5.3 to pass through primal attainment, then specialize
  -- the cone geometry in a separate helper lemma.
  calc
    IsEuclideanSubgradientAt (indicatorFunction (K : Set (Fin n → ℝ))) x xStar ↔
        PrimalFenchelSupremumAttainedAt (indicatorFunction (K : Set (Fin n → ℝ))) x xStar :=
      helperForCorollary_23_5_3_indicatorSubgradient_iff_primalSupremumAttained
        (C := (K : Set (Fin n → ℝ))) hKne hKconv x xStar
    _ ↔ x ∈ (K : Set (Fin n → ℝ)) ∧
          ∀ z ∈ (K : Set (Fin n → ℝ)), dotProduct z xStar ≤ dotProduct x xStar :=
      helperForCorollary_23_5_3_indicatorPrimalSupremumAttained_iff_mem_and_maximizes
        (C := (K : Set (Fin n → ℝ))) hKne x xStar
    _ ↔ x ∈ (K : Set (Fin n → ℝ)) ∧
          xStar ∈ euclideanPolarCone (K : Set (Fin n → ℝ)) ∧
            dotProduct x xStar = 0 :=
      helperForCorollary_23_5_4_mem_and_maximizes_on_cone_iff_polar_and_orthogonality
        K x xStar

/-- Helper for Corollary 23.5.4: the indicator-function subgradient condition on the Euclidean
polar cone is equivalent to the same primal/polar orthogonality condition. -/
lemma helperForCorollary_23_5_4_polarIndicatorSubgradient_iff_mem_polar_orthogonal
    {n : ℕ} (K : ConvexCone ℝ (Fin n → ℝ))
    (hKne : (K : Set (Fin n → ℝ)).Nonempty)
    (hKclosed : IsClosed (K : Set (Fin n → ℝ))) (x xStar : Fin n → ℝ) :
    IsEuclideanSubgradientAt
        (indicatorFunction (euclideanPolarCone (K : Set (Fin n → ℝ)))) xStar x ↔
      x ∈ (K : Set (Fin n → ℝ)) ∧
        xStar ∈ euclideanPolarCone (K : Set (Fin n → ℝ)) ∧
          dotProduct x xStar = 0 := by
  have hKconv : Convex ℝ (K : Set (Fin n → ℝ)) := by
    simpa using K.convex
  have hSupport :
      supportFunctionEReal (K : Set (Fin n → ℝ)) =
        indicatorFunction (euclideanPolarCone (K : Set (Fin n → ℝ))) := by
    -- Rewrite the cone support function as the indicator of the Euclidean polar cone.
    simpa [euclideanPolarCone] using
      section16_supportFunctionEReal_convexCone_eq_indicatorFunction_polar
        (K := K) hKne
  -- Corollary 23.5.3 already characterizes support-function subgradients on closed convex sets.
  calc
    IsEuclideanSubgradientAt
        (indicatorFunction (euclideanPolarCone (K : Set (Fin n → ℝ)))) xStar x ↔
      IsEuclideanSubgradientAt (supportFunctionEReal (K : Set (Fin n → ℝ))) xStar x := by
        simp [hSupport]
    _ ↔ x ∈ (K : Set (Fin n → ℝ)) ∧
          ∀ z ∈ (K : Set (Fin n → ℝ)), dotProduct z xStar ≤ dotProduct x xStar :=
      euclidean_subgradient_supportFunctionEReal_iff_mem_and_maximizes_on_closed_convex_set
        (C := (K : Set (Fin n → ℝ))) hKne hKclosed hKconv xStar x
    _ ↔ x ∈ (K : Set (Fin n → ℝ)) ∧
          xStar ∈ euclideanPolarCone (K : Set (Fin n → ℝ)) ∧
            dotProduct x xStar = 0 :=
      helperForCorollary_23_5_4_mem_and_maximizes_on_cone_iff_polar_and_orthogonality
        K x xStar

/-- Helper for Corollary 23.5.4: with the textbook nonemptiness hypothesis restored, the primal
and polar indicator-subgradient conditions are equivalent and both reduce to orthogonality. -/
lemma helperForCorollary_23_5_4_indicatorConvexCone_iff_polar_subgradient_and_orthogonality_of_nonempty
    {n : ℕ} (K : ConvexCone ℝ (Fin n → ℝ))
    (hKne : (K : Set (Fin n → ℝ)).Nonempty)
    (hKclosed : IsClosed (K : Set (Fin n → ℝ))) (x xStar : Fin n → ℝ) :
    (IsEuclideanSubgradientAt (indicatorFunction (K : Set (Fin n → ℝ))) x xStar ↔
      IsEuclideanSubgradientAt
        (indicatorFunction (euclideanPolarCone (K : Set (Fin n → ℝ)))) xStar x) ∧
    (IsEuclideanSubgradientAt (indicatorFunction (K : Set (Fin n → ℝ))) x xStar ↔
      x ∈ (K : Set (Fin n → ℝ)) ∧
        xStar ∈ euclideanPolarCone (K : Set (Fin n → ℝ)) ∧
          dotProduct x xStar = 0) := by
  have hIndicator :
      IsEuclideanSubgradientAt (indicatorFunction (K : Set (Fin n → ℝ))) x xStar ↔
        x ∈ (K : Set (Fin n → ℝ)) ∧
          xStar ∈ euclideanPolarCone (K : Set (Fin n → ℝ)) ∧
            dotProduct x xStar = 0 :=
    helperForCorollary_23_5_4_indicatorSubgradient_iff_mem_polar_orthogonal
      K hKne x xStar
  have hPolar :
      IsEuclideanSubgradientAt
          (indicatorFunction (euclideanPolarCone (K : Set (Fin n → ℝ)))) xStar x ↔
        x ∈ (K : Set (Fin n → ℝ)) ∧
          xStar ∈ euclideanPolarCone (K : Set (Fin n → ℝ)) ∧
            dotProduct x xStar = 0 :=
    helperForCorollary_23_5_4_polarIndicatorSubgradient_iff_mem_polar_orthogonal
      K hKne hKclosed x xStar
  -- Under nonemptiness, both sides of the corollary are the same orthogonality criterion.
  exact ⟨hIndicator.trans hPolar.symm, hIndicator⟩

/-- Helper for Corollary 23.5.4: the indicator of the empty carrier has every Euclidean vector as
a subgradient at every base point. -/
lemma helperForCorollary_23_5_4_empty_indicator_has_universal_subgradient
    {n : ℕ} (x xStar : Fin n → ℝ) :
    IsEuclideanSubgradientAt (indicatorFunction (∅ : Set (Fin n → ℝ))) x xStar := by
  -- Off the empty set the indicator is always `⊤`, so the subgradient inequality is trivial.
  change IsSubgradientAt (indicatorFunction (∅ : Set (Fin n → ℝ))) x
      (dotProductEquiv ℝ (Fin n) xStar)
  intro z
  simp [indicatorFunction]

/-- Helper for Corollary 23.5.4: on the polar of the empty cone, the indicator is the zero
function, so the Euclidean subgradient condition is equivalent to the candidate subgradient vector
vanishing. -/
lemma helperForCorollary_23_5_4_empty_polar_indicator_subgradient_iff_eq_zero
    {n : ℕ} (x xStar : Fin n → ℝ) :
    IsEuclideanSubgradientAt
        (indicatorFunction (euclideanPolarCone (∅ : Set (Fin n → ℝ)))) xStar x ↔
      x = 0 := by
  constructor
  · intro h
    change IsSubgradientAt (indicatorFunction (euclideanPolarCone (∅ : Set (Fin n → ℝ)))) xStar
        (dotProductEquiv ℝ (Fin n) x) at h
    -- Testing the subgradient inequality at `xStar ± x` forces `⟪x, x⟫ = 0`.
    have hplus := h (xStar + x)
    have hminus := h (xStar - x)
    have hle : ((dotProduct x x : ℝ) : EReal) ≤ 0 := by
      simpa [indicatorFunction, euclideanPolarCone] using hplus
    have hge : 0 ≤ dotProduct x x := by
      have hminus' : ((-(dotProduct x x) : ℝ) : EReal) ≤ 0 := by
        simpa [indicatorFunction, euclideanPolarCone, dotProduct_sub, dotProduct_neg] using hminus
      have hminus'' : -(dotProduct x x) ≤ 0 := by
        exact_mod_cast hminus'
      linarith
    have hzero : dotProduct x x = 0 := by
      exact le_antisymm (by exact_mod_cast hle) hge
    exact (dotProduct_self_eq_zero).1 hzero
  · intro hx
    subst hx
    change IsSubgradientAt (indicatorFunction (euclideanPolarCone (∅ : Set (Fin n → ℝ)))) xStar
        (dotProductEquiv ℝ (Fin n) (0 : Fin n → ℝ))
    intro z
    -- With zero slope, the zero function satisfies the subgradient inequality identically.
    simp [indicatorFunction, euclideanPolarCone]

/-- Helper for Corollary 23.5.4: on the empty carrier, the first equivalence in the current
theorem header collapses to the condition `x = 0`. -/
lemma helperForCorollary_23_5_4_empty_subgradient_equivalence_iff_eq_zero
    {n : ℕ} (x xStar : Fin n → ℝ) :
    (IsEuclideanSubgradientAt (indicatorFunction (∅ : Set (Fin n → ℝ))) x xStar ↔
      IsEuclideanSubgradientAt
        (indicatorFunction (euclideanPolarCone (∅ : Set (Fin n → ℝ)))) xStar x) ↔
      x = 0 := by
  constructor
  · intro h
    -- The empty indicator always has a subgradient, so the equivalence forces the polar-side
    -- subgradient condition and hence `x = 0`.
    have hLeft :
        IsEuclideanSubgradientAt (indicatorFunction (∅ : Set (Fin n → ℝ))) x xStar :=
      helperForCorollary_23_5_4_empty_indicator_has_universal_subgradient x xStar
    have hRight :
        IsEuclideanSubgradientAt
          (indicatorFunction (euclideanPolarCone (∅ : Set (Fin n → ℝ)))) xStar x :=
      h.mp hLeft
    exact (helperForCorollary_23_5_4_empty_polar_indicator_subgradient_iff_eq_zero x xStar).1 hRight
  · intro hx0
    -- Conversely, once `x = 0`, the polar-side condition becomes true as well, so both directions
    -- of the equivalence are immediate.
    have hRight :
        IsEuclideanSubgradientAt
          (indicatorFunction (euclideanPolarCone (∅ : Set (Fin n → ℝ)))) xStar x :=
      (helperForCorollary_23_5_4_empty_polar_indicator_subgradient_iff_eq_zero x xStar).2 hx0
    constructor
    · intro _
      exact hRight
    · intro _
      exact helperForCorollary_23_5_4_empty_indicator_has_universal_subgradient x xStar

/-- Helper for Corollary 23.5.4: the orthogonality characterization is impossible on the empty
carrier because it already requires `x ∈ ∅`. -/
lemma helperForCorollary_23_5_4_empty_mem_polar_orthogonal_iff_false
    {n : ℕ} (x xStar : Fin n → ℝ) :
    (x ∈ (∅ : Set (Fin n → ℝ)) ∧
      xStar ∈ euclideanPolarCone (∅ : Set (Fin n → ℝ)) ∧
        dotProduct x xStar = 0) ↔ False := by
  -- The first conjunct kills the entire condition before polar membership matters.
  simp [euclideanPolarCone]

/-- Helper for Corollary 23.5.4: the current orthogonality equivalence fails on the empty carrier,
which is the concrete obstruction behind the missing nonemptiness hypothesis. -/
lemma helperForCorollary_23_5_4_empty_indicatorSubgradient_not_iff_mem_polar_orthogonal
    {n : ℕ} (x xStar : Fin n → ℝ) :
    ¬ (IsEuclideanSubgradientAt (indicatorFunction (∅ : Set (Fin n → ℝ))) x xStar ↔
      x ∈ (∅ : Set (Fin n → ℝ)) ∧
        xStar ∈ euclideanPolarCone (∅ : Set (Fin n → ℝ)) ∧
          dotProduct x xStar = 0) := by
  -- Universal subgradients on `∅` contradict the impossible membership characterization.
  intro h
  have hLeft :
      IsEuclideanSubgradientAt (indicatorFunction (∅ : Set (Fin n → ℝ))) x xStar :=
    helperForCorollary_23_5_4_empty_indicator_has_universal_subgradient x xStar
  have hRight :
      x ∈ (∅ : Set (Fin n → ℝ)) ∧
        xStar ∈ euclideanPolarCone (∅ : Set (Fin n → ℝ)) ∧
          dotProduct x xStar = 0 :=
    h.mp hLeft
  exact (helperForCorollary_23_5_4_empty_mem_polar_orthogonal_iff_false x xStar).1 hRight

/-- Helper for Corollary 23.5.4: on the empty carrier, the full conjunction asserted by the
current theorem header is impossible because its orthogonality component already fails. -/
lemma helperForCorollary_23_5_4_empty_full_conclusion_false
    {n : ℕ} (x xStar : Fin n → ℝ) :
    ¬ ((IsEuclideanSubgradientAt (indicatorFunction (∅ : Set (Fin n → ℝ))) x xStar ↔
        IsEuclideanSubgradientAt
          (indicatorFunction (euclideanPolarCone (∅ : Set (Fin n → ℝ)))) xStar x) ∧
      (IsEuclideanSubgradientAt (indicatorFunction (∅ : Set (Fin n → ℝ))) x xStar ↔
        x ∈ (∅ : Set (Fin n → ℝ)) ∧
          xStar ∈ euclideanPolarCone (∅ : Set (Fin n → ℝ)) ∧
            dotProduct x xStar = 0)) := by
  -- Project to the second equivalence, which is already ruled out by the previous helper.
  intro h
  exact helperForCorollary_23_5_4_empty_indicatorSubgradient_not_iff_mem_polar_orthogonal
    x xStar h.2

/-- Helper for Corollary 23.5.4: the empty carrier already gives an explicit zero-vector
counterexample to the current theorem header, since the first equivalence holds at `x = 0` while
the full conjunction is still false. -/
lemma helperForCorollary_23_5_4_empty_counterexample_at_zero
    {n : ℕ} (xStar : Fin n → ℝ) :
    (IsEuclideanSubgradientAt (indicatorFunction (∅ : Set (Fin n → ℝ))) (0 : Fin n → ℝ) xStar ↔
        IsEuclideanSubgradientAt
          (indicatorFunction (euclideanPolarCone (∅ : Set (Fin n → ℝ)))) xStar (0 : Fin n → ℝ)) ∧
      ¬ ((IsEuclideanSubgradientAt (indicatorFunction (∅ : Set (Fin n → ℝ))) (0 : Fin n → ℝ) xStar ↔
            IsEuclideanSubgradientAt
              (indicatorFunction (euclideanPolarCone (∅ : Set (Fin n → ℝ)))) xStar
                (0 : Fin n → ℝ)) ∧
          (IsEuclideanSubgradientAt (indicatorFunction (∅ : Set (Fin n → ℝ))) (0 : Fin n → ℝ)
              xStar ↔
            (0 : Fin n → ℝ) ∈ (∅ : Set (Fin n → ℝ)) ∧
              xStar ∈ euclideanPolarCone (∅ : Set (Fin n → ℝ)) ∧
                dotProduct (0 : Fin n → ℝ) xStar = 0)) := by
  refine ⟨?_, ?_⟩
  · -- At `x = 0`, the empty-branch equivalence helper simplifies to the first equivalence itself.
    exact
      (helperForCorollary_23_5_4_empty_subgradient_equivalence_iff_eq_zero
        (x := (0 : Fin n → ℝ)) (xStar := xStar)).2 rfl
  · -- The existing empty-carrier contradiction helper rules out the full conjunction for every
    -- `xStar`.
    exact helperForCorollary_23_5_4_empty_full_conclusion_false (x := (0 : Fin n → ℝ)) (xStar := xStar)

/-- Helper for Corollary 23.5.4: if a convex cone has empty carrier, then the full conclusion
appearing in the current theorem header is false. -/
lemma helperForCorollary_23_5_4_full_conclusion_false_of_not_nonempty
    {n : ℕ} (K : ConvexCone ℝ (Fin n → ℝ))
    (hKne : ¬ (K : Set (Fin n → ℝ)).Nonempty) (x xStar : Fin n → ℝ) :
    ¬ ((IsEuclideanSubgradientAt (indicatorFunction (K : Set (Fin n → ℝ))) x xStar ↔
        IsEuclideanSubgradientAt
          (indicatorFunction (euclideanPolarCone (K : Set (Fin n → ℝ)))) xStar x) ∧
      (IsEuclideanSubgradientAt (indicatorFunction (K : Set (Fin n → ℝ))) x xStar ↔
        x ∈ (K : Set (Fin n → ℝ)) ∧
          xStar ∈ euclideanPolarCone (K : Set (Fin n → ℝ)) ∧
            dotProduct x xStar = 0)) := by
  -- Convert the negated nonemptiness assumption into the explicit empty carrier.
  have hKempty : (K : Set (Fin n → ℝ)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro y hy
    exact hKne ⟨y, hy⟩
  -- Rewriting along `hKempty` exposes the previously proved empty-carrier contradiction.
  simpa [hKempty] using helperForCorollary_23_5_4_empty_full_conclusion_false x xStar

/-- Helper for Corollary 23.5.4: any proof of the full conclusion in the current theorem header
already forces the cone carrier to be nonempty. -/
lemma helperForCorollary_23_5_4_nonempty_of_full_conclusion
    {n : ℕ} (K : ConvexCone ℝ (Fin n → ℝ)) (x xStar : Fin n → ℝ) :
    ((IsEuclideanSubgradientAt (indicatorFunction (K : Set (Fin n → ℝ))) x xStar ↔
        IsEuclideanSubgradientAt
          (indicatorFunction (euclideanPolarCone (K : Set (Fin n → ℝ)))) xStar x) ∧
      (IsEuclideanSubgradientAt (indicatorFunction (K : Set (Fin n → ℝ))) x xStar ↔
        x ∈ (K : Set (Fin n → ℝ)) ∧
          xStar ∈ euclideanPolarCone (K : Set (Fin n → ℝ)) ∧
            dotProduct x xStar = 0)) →
      (K : Set (Fin n → ℝ)).Nonempty := by
  intro hFull
  -- Contrapositively, the empty-carrier contradiction helper rules out the whole conjunction.
  by_contra hKne
  exact helperForCorollary_23_5_4_full_conclusion_false_of_not_nonempty K hKne x xStar hFull

/-- Helper for Corollary 23.5.4: if `K` has empty carrier, then the explicit zero-vector
counterexample for `∅` transports directly to `K`. -/
lemma helperForCorollary_23_5_4_counterexample_at_zero_of_not_nonempty
    {n : ℕ} (K : ConvexCone ℝ (Fin n → ℝ))
    (hKne : ¬ (K : Set (Fin n → ℝ)).Nonempty) (xStar : Fin n → ℝ) :
    (IsEuclideanSubgradientAt (indicatorFunction (K : Set (Fin n → ℝ))) (0 : Fin n → ℝ) xStar ↔
        IsEuclideanSubgradientAt
          (indicatorFunction (euclideanPolarCone (K : Set (Fin n → ℝ)))) xStar (0 : Fin n → ℝ)) ∧
      ¬ ((IsEuclideanSubgradientAt (indicatorFunction (K : Set (Fin n → ℝ))) (0 : Fin n → ℝ)
              xStar ↔
            IsEuclideanSubgradientAt
              (indicatorFunction (euclideanPolarCone (K : Set (Fin n → ℝ)))) xStar
                (0 : Fin n → ℝ)) ∧
          (IsEuclideanSubgradientAt (indicatorFunction (K : Set (Fin n → ℝ))) (0 : Fin n → ℝ)
              xStar ↔
            (0 : Fin n → ℝ) ∈ (K : Set (Fin n → ℝ)) ∧
              xStar ∈ euclideanPolarCone (K : Set (Fin n → ℝ)) ∧
                dotProduct (0 : Fin n → ℝ) xStar = 0)) := by
  have hKempty : (K : Set (Fin n → ℝ)) = ∅ := by
    -- Negated nonemptiness is exactly emptiness of the carrier set.
    apply Set.eq_empty_iff_forall_notMem.2
    intro y hy
    exact hKne ⟨y, hy⟩
  -- Rewriting the carrier as `∅` reduces the claim to the already packaged model counterexample.
  simpa [hKempty] using
    helperForCorollary_23_5_4_empty_counterexample_at_zero (n := n) (xStar := xStar)

/-- Helper for Corollary 23.5.4: a theorem of the current universal shape would already force
the cone carrier to be nonempty. -/
lemma helperForCorollary_23_5_4_nonempty_of_universal_header
    {n : ℕ} (K : ConvexCone ℝ (Fin n → ℝ))
    (hAll : ∀ x xStar : Fin n → ℝ,
      (IsEuclideanSubgradientAt (indicatorFunction (K : Set (Fin n → ℝ))) x xStar ↔
        IsEuclideanSubgradientAt
          (indicatorFunction (euclideanPolarCone (K : Set (Fin n → ℝ)))) xStar x) ∧
      (IsEuclideanSubgradientAt (indicatorFunction (K : Set (Fin n → ℝ))) x xStar ↔
        x ∈ (K : Set (Fin n → ℝ)) ∧
          xStar ∈ euclideanPolarCone (K : Set (Fin n → ℝ)) ∧
            dotProduct x xStar = 0)) :
    (K : Set (Fin n → ℝ)).Nonempty := by
  by_contra hKne
  -- The transported zero-vector counterexample contradicts any universal proof of the header.
  exact
    (helperForCorollary_23_5_4_counterexample_at_zero_of_not_nonempty
      (K := K) hKne (xStar := (0 : Fin n → ℝ))).2
      (hAll (0 : Fin n → ℝ) (0 : Fin n → ℝ))

/-- Corollary 23.5.4: Let `K` be a nonempty closed convex cone. Then `xStar ∈ ∂δ(x | K)` if and
only if `x ∈ ∂δ(xStar | Kᵒ)`. These conditions are equivalent to `x ∈ K`, `xStar ∈ Kᵒ`, and
`⟪x, xStar⟫ = 0`. -/
theorem euclidean_subgradient_indicatorConvexCone_iff_polar_subgradient_and_orthogonality
    {n : ℕ} (K : ConvexCone ℝ (Fin n → ℝ))
    (hKne : (K : Set (Fin n → ℝ)).Nonempty)
    (hKclosed : IsClosed (K : Set (Fin n → ℝ))) (x xStar : Fin n → ℝ) :
    (IsEuclideanSubgradientAt (indicatorFunction (K : Set (Fin n → ℝ))) x xStar ↔
      IsEuclideanSubgradientAt (indicatorFunction (euclideanPolarCone (K : Set (Fin n → ℝ)))) xStar x) ∧
    (IsEuclideanSubgradientAt (indicatorFunction (K : Set (Fin n → ℝ))) x xStar ↔
      x ∈ (K : Set (Fin n → ℝ)) ∧
        xStar ∈ euclideanPolarCone (K : Set (Fin n → ℝ)) ∧
          dotProduct x xStar = 0) := by
  exact
    helperForCorollary_23_5_4_indicatorConvexCone_iff_polar_subgradient_and_orthogonality_of_nonempty
      K hKne hKclosed x xStar


end Section23
end Chap05

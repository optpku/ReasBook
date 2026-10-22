/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section12_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section13_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section19_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section26_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30

section Chap07
section Section33

/-!
# Section 33: Saddle-Functions and Minimax Theory

This file provides a Lean scaffold for the statements listed in
`data/section33.json`, prioritizing the material that does not rely on
Section 30.  Theorems after the `Theorem33.24` cutoff are intentionally
left as a later task, pending the `Theorem 30.1` dependency.
-/

/-- Set membership is treated classically in this section. -/
noncomputable local instance classicalSetDecidablePred {α : Type*} (s : Set α) : DecidablePred s :=
  Classical.decPred s

/-- An `EReal`-valued function is convex on `C` when it satisfies Jensen's inequality
whenever the relevant convex combination remains in `C`. -/
def IsERealConvexOn {m : ℕ} (C : Set (Fin m → ℝ)) (f : (Fin m → ℝ) → EReal) : Prop :=
  ∀ ⦃x y : Fin m → ℝ⦄, x ∈ C → y ∈ C →
    ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
      a • x + b • y ∈ C →
        f (a • x + b • y) ≤ (a : EReal) * f x + (b : EReal) * f y

/-- An `EReal`-valued function is concave on `C` when it satisfies the reverse Jensen
inequality whenever the relevant convex combination remains in `C`. -/
def IsERealConcaveOn {m : ℕ} (C : Set (Fin m → ℝ)) (f : (Fin m → ℝ) → EReal) : Prop :=
  ∀ ⦃x y : Fin m → ℝ⦄, x ∈ C → y ∈ C →
    ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
      a • x + b • y ∈ C →
        (a : EReal) * f x + (b : EReal) * f y ≤ f (a • x + b • y)

/-- A bifunction is concave-convex when it is concave in the first variable and convex in the second. -/
def IsConcaveConvexOn {m n : ℕ}
    (C : Set (Fin m → ℝ)) (D : Set (Fin n → ℝ))
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  (∀ v ∈ D, IsERealConcaveOn C (fun u => K u v)) ∧
    ∀ u ∈ C, IsERealConvexOn D (fun v => K u v)

/-- A bifunction is convex-concave when it is convex in the first variable and concave in the second. -/
def IsConvexConcaveOn {m n : ℕ}
    (C : Set (Fin m → ℝ)) (D : Set (Fin n → ℝ))
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  (∀ v ∈ D, IsERealConvexOn C (fun u => K u v)) ∧
    ∀ u ∈ C, IsERealConcaveOn D (fun v => K u v)

/-- Definition33.0.1: A saddle function on `C × D` is a bifunction that is either concave-convex
or convex-concave. -/
def IsSaddleFunctionOn {m n : ℕ}
    (C : Set (Fin m → ℝ)) (D : Set (Fin n → ℝ))
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  IsConcaveConvexOn C D K ∨ IsConvexConcaveOn C D K

/-- The lower simple extension of a bifunction on `C × D` takes the value `⊤` on
`C × Dᶜ` and `⊥` on `Cᶜ × (Fin n → ℝ)`. -/
noncomputable def lowerSimpleExtension {m n : ℕ}
    (C : Set (Fin m → ℝ)) (D : Set (Fin n → ℝ))
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun u v =>
    if u ∈ C then
      if v ∈ D then K u v else ⊤
    else
      ⊥

/-- The upper simple extension of a bifunction on `C × D` takes the value `⊥` on
`Cᶜ × D` and `⊤` on `(Fin m → ℝ) × Dᶜ`. -/
noncomputable def upperSimpleExtension {m n : ℕ}
    (C : Set (Fin m → ℝ)) (D : Set (Fin n → ℝ))
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun u v =>
    if v ∈ D then
      if u ∈ C then K u v else ⊥
    else
      ⊤

/-- Definition33.0.2: The lower/upper simple extensions of `K` are the pair consisting of
its lower simple extension and its upper simple extension. -/
noncomputable abbrev simpleExtensions {m n : ℕ}
    (C : Set (Fin m → ℝ)) (D : Set (Fin n → ℝ))
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    ((Fin m → ℝ) → (Fin n → ℝ) → EReal) ×
      ((Fin m → ℝ) → (Fin n → ℝ) → EReal) :=
  (lowerSimpleExtension C D K, upperSimpleExtension C D K)

/-- Helper for Lemma33.0.3: on `C × D`, the lower simple extension reduces to the original
bifunction value. -/
lemma helperForLemma33_0_3_lowerSimpleExtension_agrees {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D) :
    lowerSimpleExtension C D K u v = K u v := by
  -- Unfold the lower extension and simplify both `if` branches using membership in `C` and `D`.
  simp [lowerSimpleExtension, hu, hv]

/-- Helper for Lemma33.0.3: on `C × D`, the upper simple extension reduces to the original
bifunction value. -/
lemma helperForLemma33_0_3_upperSimpleExtension_agrees {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D) :
    upperSimpleExtension C D K u v = K u v := by
  -- Unfold the upper extension and simplify the nested `if` expressions in the same way.
  simp [upperSimpleExtension, hu, hv]

-- Proof sketch: unfold the lower and upper simple extensions; on `u ∈ C` and `v ∈ D`,
-- both nested `if` expressions reduce to the original bifunction value `K u v`.
/-- Lemma33.0.3: Agreement on `C × D`. If `u ∈ C` and `v ∈ D`, then the lower and upper
simple extensions `K₁` and `K₂` from Definition33.0.2 both agree with `K` at `(u, v)`. -/
lemma simpleExtensions_eq_on_product {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hu : u ∈ C) (hv : v ∈ D) :
    lowerSimpleExtension C D K u v = K u v ∧
      upperSimpleExtension C D K u v = K u v := by
  -- Prove the two agreement statements separately, one for each simple extension.
  constructor
  · exact helperForLemma33_0_3_lowerSimpleExtension_agrees hu hv
  · exact helperForLemma33_0_3_upperSimpleExtension_agrees hu hv

/-- The convex closure in the second variable is the lower semicontinuous
regularization obtained by taking the supremum of local infima over open balls. -/
noncomputable def convexClosureInSecond {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun u v =>
    ⨆ (ε : {ε : ℝ // 0 < ε}),
      ⨅ (w : {w : Fin n → ℝ // ‖w - v‖ < ε.1}), K u w.1

/-- The concave closure in the first variable is the upper semicontinuous
regularization obtained by taking the infimum of local suprema over open balls. -/
noncomputable def concaveClosureInFirst {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun u v =>
    ⨅ (ε : {ε : ℝ // 0 < ε}),
      ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 v

/-- The convex closure in the first variable is the lower semicontinuous
regularization obtained by taking the supremum of local infima over open balls. -/
noncomputable def convexClosureInFirst {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun u v =>
    ⨆ (ε : {ε : ℝ // 0 < ε}),
      ⨅ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 v

/-- A bifunction is convex-closed in the second variable when it agrees with its
convex closure in that variable. -/
def IsConvexClosedInSecond {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  K = convexClosureInSecond K

/-- The concave closure in the second variable is the upper semicontinuous
regularization obtained by taking the infimum of local suprema over open balls. -/
noncomputable def concaveClosureInSecond {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun u v =>
    ⨅ (ε : {ε : ℝ // 0 < ε}),
      ⨆ (w : {w : Fin n → ℝ // ‖w - v‖ < ε.1}), K u w.1

/-- A bifunction is concave-closed in the second variable when it agrees with its
concave closure in that variable. -/
def IsConcaveClosedInSecond {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  K = concaveClosureInSecond K

/-- A bifunction is concave-closed in the first variable when it agrees with its
concave closure in that variable. -/
def IsConcaveClosedInFirst {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  K = concaveClosureInFirst K

/-- A bifunction is convex-closed in the first variable when it agrees with its
convex closure in that variable. -/
def IsConvexClosedInFirst {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  K = convexClosureInFirst K

/-- The closure data attached to a bifunction: the two coordinatewise closures and the
corresponding fixed-point predicates. -/
structure ConvexConcaveClosurePackage (m n : ℕ) where
  cl_v : (Fin m → ℝ) → (Fin n → ℝ) → EReal
  cl_u : (Fin m → ℝ) → (Fin n → ℝ) → EReal
  convexClosedInV : Prop
  concaveClosedInU : Prop

/-- Definition33.0.4: The convex closure in `v`, the concave closure in `u`, and the
corresponding fixed-point predicates canonically attached to an `EReal`-valued bifunction
`K`. -/
noncomputable def convexConcaveClosureData {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : ConvexConcaveClosurePackage m n :=
  let clV := convexClosureInSecond K
  let clU := concaveClosureInFirst K
  { cl_v := clV
    cl_u := clU
    convexClosedInV := K = clV
    concaveClosedInU := K = clU }

/-- Helper for Lemma33.0.5: multiplying by a positive real scalar commutes with `iSup` in
`EReal`. -/
lemma helperForLemma33_0_5_positiveReal_mul_iSup {ι : Sort*}
    {a : ℝ} (ha : 0 < a) (f : ι → EReal) :
    ((a : EReal) * (⨆ i, f i)) = ⨆ i, (a : EReal) * f i := by
  -- Transport the supremum across the order isomorphism given by multiplication by a positive
  -- finite scalar and its inverse.
  let leftMul : EReal →o EReal :=
    { toFun := fun x => (a : EReal) * x
      monotone' := fun _ _ h =>
        mul_le_mul_of_nonneg_left h (show (0 : EReal) ≤ (a : EReal) by exact_mod_cast ha.le) }
  let leftMulInv : EReal →o EReal :=
    { toFun := fun x => (((a⁻¹ : ℝ) : EReal)) * x
      monotone' := fun _ _ h =>
        mul_le_mul_of_nonneg_left h (show (0 : EReal) ≤ (((a⁻¹ : ℝ) : EReal)) by
          exact_mod_cast inv_nonneg.mpr ha.le) }
  have hInvLeft : ((((a⁻¹ : ℝ) : EReal)) * (a : EReal)) = 1 := by
    rw [← EReal.coe_mul, inv_mul_cancel₀ ha.ne', EReal.coe_one]
  have hInvRight : ((a : EReal) * (((a⁻¹ : ℝ) : EReal))) = 1 := by
    rw [← EReal.coe_mul, mul_inv_cancel₀ ha.ne', EReal.coe_one]
  let mulIso : EReal ≃o EReal :=
    OrderIso.ofHomInv leftMul leftMulInv
      (by
        ext x
        simp [leftMul, leftMulInv, hInvRight])
      (by
        ext x
        simp [leftMul, leftMulInv, hInvLeft])
  -- Once the order isomorphism is available, `map_iSup` gives the desired transport formula.
  change mulIso (⨆ i, f i) = ⨆ i, mulIso (f i)
  exact mulIso.map_iSup f

/-- Helper for Lemma33.0.5: multiplying by a positive real scalar commutes with `iInf` in
`EReal`. -/
lemma helperForLemma33_0_5_positiveReal_mul_iInf {ι : Sort*}
    {a : ℝ} (ha : 0 < a) (f : ι → EReal) :
    ((a : EReal) * (⨅ i, f i)) = ⨅ i, (a : EReal) * f i := by
  -- Use the same positive-scalar order isomorphism as in the `iSup` lemma, but transport an
  -- infimum instead.
  let leftMul : EReal →o EReal :=
    { toFun := fun x => (a : EReal) * x
      monotone' := fun _ _ h =>
        mul_le_mul_of_nonneg_left h (show (0 : EReal) ≤ (a : EReal) by exact_mod_cast ha.le) }
  let leftMulInv : EReal →o EReal :=
    { toFun := fun x => (((a⁻¹ : ℝ) : EReal)) * x
      monotone' := fun _ _ h =>
        mul_le_mul_of_nonneg_left h (show (0 : EReal) ≤ (((a⁻¹ : ℝ) : EReal)) by
          exact_mod_cast inv_nonneg.mpr ha.le) }
  have hInvLeft : ((((a⁻¹ : ℝ) : EReal)) * (a : EReal)) = 1 := by
    rw [← EReal.coe_mul, inv_mul_cancel₀ ha.ne', EReal.coe_one]
  have hInvRight : ((a : EReal) * (((a⁻¹ : ℝ) : EReal))) = 1 := by
    rw [← EReal.coe_mul, mul_inv_cancel₀ ha.ne', EReal.coe_one]
  let mulIso : EReal ≃o EReal :=
    OrderIso.ofHomInv leftMul leftMulInv
      (by
        ext x
        simp [leftMul, leftMulInv, hInvRight])
      (by
        ext x
        simp [leftMul, leftMulInv, hInvLeft])
  -- The `iInf` transport is the dual order-theoretic statement.
  change mulIso (⨅ i, f i) = ⨅ i, mulIso (f i)
  exact mulIso.map_iInf f

/-- Helper for Lemma33.0.5: equal-radius balls are stable under the same convex combination as
their centers. -/
lemma helperForLemma33_0_5_convexCombination_mem_ball {n : ℕ}
    {x y w₁ w₂ : Fin n → ℝ} {r a b : ℝ}
    (hw₁ : ‖w₁ - x‖ < r) (hw₂ : ‖w₂ - y‖ < r)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ‖(a • w₁ + b • w₂) - (a • x + b • y)‖ < r := by
  -- Rewrite the displacement around the convex-combination center into the same convex
  -- combination of the two displacements from the original centers.
  have hRewrite :
      (a • w₁ + b • w₂) - (a • x + b • y) = a • (w₁ - x) + b • (w₂ - y) := by
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_add]
  have hWeighted :
      a * ‖w₁ - x‖ + b * ‖w₂ - y‖ < r := by
    -- Reduce the weighted estimate to the strict radius bounds on the two endpoints.
    by_cases hZeroA : a = 0
    · subst hZeroA
      have hBOne : b = 1 := by linarith
      simp [hBOne, hw₂]
    · have hPosA : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using hZeroA)
      by_cases hZeroB : b = 0
      · subst hZeroB
        have hAOne : a = 1 := by linarith
        simp [hAOne, hw₁]
      · have hPosB : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hZeroB)
        have h₁ : a * ‖w₁ - x‖ < a * r := mul_lt_mul_of_pos_left hw₁ hPosA
        have h₂ : b * ‖w₂ - y‖ < b * r := mul_lt_mul_of_pos_left hw₂ hPosB
        have hRadius : a * r + b * r = r := by
          calc
            a * r + b * r = (a + b) * r := by ring
            _ = r := by rw [hab, one_mul]
        have hSum : a * ‖w₁ - x‖ + b * ‖w₂ - y‖ < a * r + b * r := add_lt_add h₁ h₂
        simpa [hRadius] using hSum
  -- The triangle inequality converts the vector estimate into the desired ball inclusion.
  rw [hRewrite]
  calc
    ‖a • (w₁ - x) + b • (w₂ - y)‖ ≤ ‖a • (w₁ - x)‖ + ‖b • (w₂ - y)‖ := norm_add_le _ _
    _ = |a| * ‖w₁ - x‖ + |b| * ‖w₂ - y‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ = a * ‖w₁ - x‖ + b * ‖w₂ - y‖ := by
      simp [abs_of_nonneg ha, abs_of_nonneg hb]
    _ < r := hWeighted

/-- Helper for Lemma33.0.5: shrinking the radius makes the local infimum larger. -/
lemma helperForLemma33_0_5_localInfimum_antitone_radius {n : ℕ}
    {f : (Fin n → ℝ) → EReal} {x : Fin n → ℝ}
    {δ ε : {r : ℝ // 0 < r}} (hδε : δ.1 ≤ ε.1) :
    (⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) ≤
      ⨅ w : {w : Fin n → ℝ // ‖w - x‖ < δ.1}, f w.1 := by
  -- Any witness in the smaller ball is also a witness in the larger ball.
  refine le_iInf ?_
  intro w
  have hwLarge : ‖w.1 - x‖ < ε.1 := lt_of_lt_of_le w.2 hδε
  let wLarge : {w : Fin n → ℝ // ‖w - x‖ < ε.1} := ⟨w.1, hwLarge⟩
  exact iInf_le _ wLarge

/-- Helper for Lemma33.0.5: shrinking the radius makes the local supremum smaller. -/
lemma helperForLemma33_0_5_localSupremum_monotone_radius {n : ℕ}
    {f : (Fin n → ℝ) → EReal} {x : Fin n → ℝ}
    {δ ε : {r : ℝ // 0 < r}} (hδε : δ.1 ≤ ε.1) :
    (⨆ w : {w : Fin n → ℝ // ‖w - x‖ < δ.1}, f w.1) ≤
      ⨆ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1 := by
  -- Each witness in the smaller ball also contributes to the larger-ball supremum.
  refine iSup_le ?_
  intro w
  have hwLarge : ‖w.1 - x‖ < ε.1 := lt_of_lt_of_le w.2 hδε
  let wLarge : {w : Fin n → ℝ // ‖w - x‖ < ε.1} := ⟨w.1, hwLarge⟩
  exact le_iSup (fun q : {q : Fin n → ℝ // ‖q - x‖ < ε.1} => f q.1) wLarge

/-- Helper for Lemma33.0.5: away from the exceptional `⊥/⊤` ambiguity of `EReal`,
the product-indexed infimum is bounded by the sum of the two endpoint infima. -/
lemma helperForLemma33_0_5_productIndexed_iInf_weightedSum_le_of_nonexceptional
    {ι κ : Type*} [Nonempty ι] [Nonempty κ]
    {F : ι → EReal} {G : κ → EReal}
    (h₁ : (⨅ i, F i) ≠ ⊥ ∨ (⨅ j, G j) ≠ ⊤)
    (h₂ : (⨅ i, F i) ≠ ⊤ ∨ (⨅ j, G j) ≠ ⊥) :
    (⨅ p : ι × κ, F p.1 + G p.2) ≤ (⨅ i, F i) + (⨅ j, G j) := by
  -- Reduce the product-indexed infimum to strict upper bounds on each endpoint infimum and
  -- then choose independent near-minimizers from `iInf_lt_iff`.
  refine EReal.le_add_of_forall_gt h₁ h₂ ?_
  intro x hx y hy
  rcases iInf_lt_iff.mp hx with ⟨i, hi⟩
  rcases iInf_lt_iff.mp hy with ⟨j, hj⟩
  exact (iInf_le (fun p : ι × κ => F p.1 + G p.2) (i, j)).trans (EReal.add_lt_add hi hj).le

/-- Helper for Lemma33.0.5: weighted sums of independent endpoint suprema are controlled by
the corresponding product-indexed supremum. -/
lemma helperForLemma33_0_5_weightedSum_le_productIndexed_iSup
    {ι κ : Type*} [Nonempty ι] [Nonempty κ]
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (f : ι → EReal) (g : κ → EReal) :
    ((a : EReal) * (⨆ i, f i)) + ((b : EReal) * (⨆ j, g j)) ≤
      ⨆ p : ι × κ, (a : EReal) * f p.1 + (b : EReal) * g p.2 := by
  -- Move the positive scalars inside the two supremum layers so that `add_le_of_forall_lt`
  -- can compare strict lower bounds termwise.
  rw [helperForLemma33_0_5_positiveReal_mul_iSup ha,
    helperForLemma33_0_5_positiveReal_mul_iSup hb]
  refine EReal.add_le_of_forall_lt ?_
  intro x hx y hy
  rcases lt_iSup_iff.mp hx with ⟨i, hi⟩
  rcases lt_iSup_iff.mp hy with ⟨j, hj⟩
  exact (EReal.add_lt_add hi hj).le.trans
    (le_iSup (fun p : ι × κ => (a : EReal) * f p.1 + (b : EReal) * g p.2) (i, j))

/-- Helper for Lemma33.0.5: negating a supremum of negated values recovers the corresponding
infimum. -/
lemma helperForLemma33_0_5_neg_iSup_neg_eq_iInf {ι : Sort*} (f : ι → EReal) :
    -(⨆ i, -f i) = ⨅ i, f i := by
  -- Compare both sides through the order-reversing equivalence `x ↦ -x` and the defining
  -- universal properties of `iSup` and `iInf`.
  apply le_antisymm
  · refine le_iInf ?_
    intro i
    exact (EReal.neg_le).2 (le_iSup (fun j => -f j) i)
  · refine (EReal.le_neg).2 ?_
    refine iSup_le ?_
    intro i
    simpa using (iInf_le f i)

/-- Helper for Lemma33.0.5: negating an infimum of negated values recovers the corresponding
supremum. -/
lemma helperForLemma33_0_5_neg_iInf_neg_eq_iSup {ι : Sort*} (f : ι → EReal) :
    -(⨅ i, -f i) = ⨆ i, f i := by
  -- Apply the previous identity to the negated family and negate both sides once more.
  have h := helperForLemma33_0_5_neg_iSup_neg_eq_iInf (fun i => -f i)
  simpa [eq_comm] using congrArg Neg.neg h

/-- Helper for Lemma33.0.5: negating a sum is always bounded below by the sum of the negated
terms in `EReal`. -/
lemma helperForLemma33_0_5_neg_sum_upper_bound {x y : EReal} :
    -x + -y ≤ -(x + y) := by
  -- Away from the exceptional `⊥/⊤` branches, this is the usual equality `-(x + y) = -x - y`;
  -- the remaining branches are checked directly from the `EReal` conventions.
  rcases eq_or_ne x ⊥ with rfl | hxBot
  · simp
  rcases eq_or_ne y ⊥ with rfl | hyBot
  · simp
  rcases eq_or_ne x ⊤ with rfl | hxTop
  · simp [hyBot]
  rcases eq_or_ne y ⊤ with rfl | hyTop
  · simp [hxBot]
  rw [EReal.neg_add (.inl hxBot) (.inl hxTop)]
  simp [sub_eq_add_neg]

/-- Helper for Lemma33.0.5: negating a convex `EReal`-valued section produces a concave one. -/
lemma helperForLemma33_0_5_convexNegation_isConcave {n : ℕ}
    {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → EReal}
    (hConv : IsERealConvexOn C f) :
    IsERealConcaveOn C (fun x => -f x) := by
  intro x y hx hy a b ha hb hab hxy
  -- Start from Jensen for `f`, negate it, and then replace the negated weighted sum by the
  -- larger sum of the negated weighted terms.
  have hJensen :
      f (a • x + b • y) ≤ (a : EReal) * f x + (b : EReal) * f y :=
    hConv (x := x) (y := y) hx hy ha hb hab hxy
  have hNegJensen :
      -((a : EReal) * f x + (b : EReal) * f y) ≤ -f (a • x + b • y) := by
    simpa using hJensen
  have hWeighted :
      (a : EReal) * (-f x) + (b : EReal) * (-f y) ≤
        -((a : EReal) * f x + (b : EReal) * f y) := by
    simpa [mul_neg, neg_mul] using
      (helperForLemma33_0_5_neg_sum_upper_bound
        (x := (a : EReal) * f x) (y := (b : EReal) * f y))
  exact le_trans hWeighted hNegJensen

/-- Helper for Lemma33.0.5: the local Jensen predicate on `Set.univ` gives the usual convex
epigraph. -/
lemma helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    (hConv : IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) f) :
    ConvexFunction f := by
  -- Route correction: switch from the stalled exceptional-branch transport to the ambient
  -- epigraph formulation, where finite height witnesses avoid the `⊥/⊤` addition ambiguity.
  unfold ConvexFunction ConvexFunctionOn epigraph
  intro p hp q hq a b ha hb hab
  rcases hp with ⟨hpUniv, hpHeight⟩
  rcases hq with ⟨hqUniv, hqHeight⟩
  constructor
  · show a • p.1 + b • q.1 ∈ (Set.univ : Set (Fin n → ℝ))
    simp
  have hNonnegA : (0 : EReal) ≤ (a : EReal) := by
    exact_mod_cast ha
  have hNonnegB : (0 : EReal) ≤ (b : EReal) := by
    exact_mod_cast hb
  have hJensen :
      f (a • p.1 + b • q.1) ≤ (a : EReal) * f p.1 + (b : EReal) * f q.1 :=
    hConv (x := p.1) (y := q.1)
      (Set.mem_univ p.1) (Set.mem_univ q.1) ha hb hab (Set.mem_univ _)
  have hHeight :
      (a : EReal) * f p.1 + (b : EReal) * f q.1 ≤
        (a : EReal) * (p.2 : EReal) + (b : EReal) * (q.2 : EReal) := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left hpHeight hNonnegA)
      (mul_le_mul_of_nonneg_left hqHeight hNonnegB)
  calc
    f (a • p.1 + b • q.1) ≤ (a : EReal) * f p.1 + (b : EReal) * f q.1 := hJensen
    _ ≤ (a : EReal) * (p.2 : EReal) + (b : EReal) * (q.2 : EReal) := hHeight
    _ = (((a • p + b • q).2 : ℝ) : EReal) := by
      simp [smul_eq_mul, EReal.coe_add, EReal.coe_mul, add_comm, add_left_comm, add_assoc]

/-- Helper for Lemma33.0.5: a global `ConvexFunction` immediately yields the local Jensen
predicate on `Set.univ` as soon as `⊥` never occurs. -/
lemma helperForLemma33_0_5_convexFunction_to_isERealConvexOn_univ {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    (hConv : ConvexFunction f)
    (hNoBot : ∀ x, f x ≠ ⊥) :
    IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) f := by
  -- Route correction: the converse from epigraph convexity to Jensen is only sound once `⊥` is
  -- excluded, so reuse the earlier Jensen theorem with that explicit hypothesis.
  have hConvOn : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := by
    simpa [ConvexFunction] using hConv
  have hJensen :=
    (convexFunctionOn_univ_iff_jensen_inequality (f := f) hNoBot).1 hConvOn
  intro x y hx hy a b ha hb hab hxy
  let w : Fin 2 → ℝ := fun i => if i = 0 then a else b
  let z : Fin 2 → Fin n → ℝ := fun i => if i = 0 then x else y
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    fin_cases i <;> simp [w, ha, hb]
  have hsum : Finset.univ.sum w = 1 := by
    simp [w, hab, Fin.sum_univ_two]
  have hTwoPoint := hJensen 2 w z hw hsum
  simpa [w, z, Fin.sum_univ_two] using hTwoPoint

/-- Helper for Lemma33.0.5: multiplying by a positive real scalar preserves the property of
being different from `⊥`. -/
lemma helperForLemma33_0_5_positiveReal_mul_ne_bot {a : ℝ}
    (ha : 0 < a) {x : EReal} (hx : x ≠ ⊥) :
    (a : EReal) * x ≠ ⊥ := by
  -- The positive finite scalar is neither `⊥` nor `⊤`, so the only way the product could be
  -- `⊥` would be for the second factor itself to be `⊥`.
  refine (EReal.mul_ne_bot (a : EReal) x).2 ?_
  constructor
  · exact Or.inl (by simp)
  constructor
  · exact Or.inr hx
  constructor
  · exact Or.inl (by simp)
  · exact Or.inl (by exact_mod_cast ha.le)

/-- Helper for Lemma33.0.5: multiplying by a positive real scalar preserves the property of
being different from `⊤`. -/
lemma helperForLemma33_0_5_positiveReal_mul_ne_top {a : ℝ}
    (ha : 0 < a) {x : EReal} (hx : x ≠ ⊤) :
    (a : EReal) * x ≠ ⊤ := by
  -- The same positive finite scalar cannot create `⊤`; that would have to come from the second
  -- factor already being `⊤`.
  refine (EReal.mul_ne_top (a : EReal) x).2 ?_
  constructor
  · exact Or.inl (by simp)
  constructor
  · exact Or.inl (by exact_mod_cast ha.le)
  constructor
  · exact Or.inl (by simp)
  · exact Or.inr hx

/-- Helper for Lemma33.0.5: if a local supremum over a ball is `⊥`, then every point in that
ball already has value `⊥`. -/
lemma helperForLemma33_0_5_localSupremum_eq_bot_implies_pointwise_bot {n : ℕ}
    {f : (Fin n → ℝ) → EReal} {x : Fin n → ℝ} {ε : {r : ℝ // 0 < r}}
    (hBot : (⨆ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) = ⊥) :
    ∀ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1 = ⊥ := by
  intro w
  -- Compare the point value to the enclosing local supremum and simplify the `⊥` hypothesis.
  have hwLe :
      f w.1 ≤ ⨆ q : {q : Fin n → ℝ // ‖q - x‖ < ε.1}, f q.1 :=
    le_iSup (fun q : {q : Fin n → ℝ // ‖q - x‖ < ε.1} => f q.1) w
  have hwBot : f w.1 ≤ (⊥ : EReal) := by
    simpa [hBot] using hwLe
  exact le_bot_iff.mp hwBot

/-- Helper for Lemma33.0.5: if a local infimum over a ball is `⊤`, then every point in that
ball already has value `⊤`. -/
lemma helperForLemma33_0_5_localInfimum_eq_top_implies_pointwise_top {n : ℕ}
    {f : (Fin n → ℝ) → EReal} {x : Fin n → ℝ} {ε : {r : ℝ // 0 < r}}
    (hTop : (⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) = ⊤) :
    ∀ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1 = ⊤ := by
  intro w
  -- Compare the point value to the enclosing local infimum and simplify the `⊤` hypothesis.
  have hwGe :
      (⊤ : EReal) ≤ f w.1 := by
    simpa [hTop] using
      (iInf_le (fun q : {q : Fin n → ℝ // ‖q - x‖ < ε.1} => f q.1) w)
  exact top_le_iff.mp hwGe

/-- Helper for Lemma33.0.5: if an `EReal`-indexed infimum equals `⊤`, then every indexed value
already equals `⊤`. -/
lemma helperForLemma33_0_5_iInf_eq_top_implies_pointwise_top {ι : Sort*}
    {F : ι → EReal} (hTop : (⨅ i, F i) = (⊤ : EReal)) :
    ∀ i, F i = (⊤ : EReal) := by
  intro i
  -- Compare each indexed value to the infimum and rewrite the `⊤` hypothesis.
  have hLe : (⊤ : EReal) ≤ F i := by
    simpa [hTop] using (iInf_le F i)
  exact top_le_iff.mp hLe

/-- Helper for Lemma33.0.5: if a local infimum over a ball is `⊥`, then every strict upper bound
on `⊥` is beaten by some point in that ball. -/
lemma helperForLemma33_0_5_localInfimum_eq_bot_implies_exists_ballWitness_lt {n : ℕ}
    (ε : {r : ℝ // 0 < r}) {f : (Fin n → ℝ) → EReal} {x : Fin n → ℝ}
    (hBot : (⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) = ⊥) :
    ∀ {z : EReal}, (⊥ : EReal) < z → ∃ w : Fin n → ℝ, ‖w - x‖ < ε.1 ∧ f w < z := by
  intro z hz
  let wx : {w : Fin n → ℝ // ‖w - x‖ < ε.1} := ⟨x, by simpa using ε.2⟩
  letI : Nonempty {w : Fin n → ℝ // ‖w - x‖ < ε.1} := ⟨wx⟩
  -- Rewrite the `⊥`-valued local infimum as a strict inequality and extract a point from
  -- `iInf_lt_iff`.
  have hlt :
      (⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) < z := by
    simpa [hBot] using hz
  rcases iInf_lt_iff.mp hlt with ⟨w, hw⟩
  exact ⟨w.1, w.2, hw⟩

/-- Helper for Lemma33.0.5: an actual `⊥`-valued witness in the `x`-ball already forces the
target fixed-radius local infimum to be `⊥`. -/
lemma helperForLemma33_0_5_fixedRadiusLocalInfimum_botWitness_forces_targetBot {n : ℕ}
    (ε : {r : ℝ // 0 < r}) {f : (Fin n → ℝ) → EReal}
    {x y w : Fin n → ℝ} {a b : ℝ}
    (hConv : IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) f)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hPosA : 0 < a)
    (hw : ‖w - x‖ < ε.1) (hfwBot : f w = ⊥) :
    (⨅ z : {z : Fin n → ℝ // ‖z - (a • x + b • y)‖ < ε.1}, f z.1) = ⊥ := by
  have hBall :
      ‖(a • w + b • y) - (a • x + b • y)‖ < ε.1 := by
    -- Keep the `y`-endpoint fixed at the center of its ball and move only the `x`-endpoint
    -- witness carrying the value `⊥`.
    simpa using
      helperForLemma33_0_5_convexCombination_mem_ball
        (x := x) (y := y) (w₁ := w) (w₂ := y) (r := ε.1)
        hw (by simpa using ε.2) ha hb hab
  let zCombo : {z : Fin n → ℝ // ‖z - (a • x + b • y)‖ < ε.1} :=
    ⟨a • w + b • y, hBall⟩
  have hPoint :
      (⨅ z : {z : Fin n → ℝ // ‖z - (a • x + b • y)‖ < ε.1}, f z.1) ≤ f zCombo.1 :=
    iInf_le (fun z : {z : Fin n → ℝ // ‖z - (a • x + b • y)‖ < ε.1} => f z.1) zCombo
  have hJensen :
      f (a • w + b • y) ≤ (a : EReal) * f w + (b : EReal) * f y :=
    hConv (x := w) (y := y) (Set.mem_univ _) (Set.mem_univ _) ha hb hab (Set.mem_univ _)
  have hComboBot : f (a • w + b • y) = ⊥ := by
    -- Once one endpoint value is exactly `⊥`, the weighted sum on the right collapses to `⊥`.
    have hLeBot : f (a • w + b • y) ≤ (⊥ : EReal) := by
      calc
        f (a • w + b • y) ≤ (a : EReal) * f w + (b : EReal) * f y := hJensen
        _ = ⊥ := by simp [hfwBot, EReal.coe_mul_bot_of_pos hPosA]
    exact le_bot_iff.mp hLeBot
  have hInfLeBot :
      (⨅ z : {z : Fin n → ℝ // ‖z - (a • x + b • y)‖ < ε.1}, f z.1) ≤ (⊥ : EReal) := by
    exact le_trans hPoint (by simpa [zCombo, hComboBot])
  exact le_antisymm hInfLeBot bot_le

/-- Helper for Lemma33.0.5: extending a convex function by `⊤` outside a convex set preserves
Jensen convexity as soon as the original function never takes the value `⊥` on that set. -/
lemma helperForLemma33_0_5_extendByTopOnConvexSet_preserves_convexity {n : ℕ}
    {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → EReal}
    (hCconv : Convex ℝ C)
    (hConv : IsERealConvexOn C f)
    (hNoBot : ∀ z ∈ C, f z ≠ (⊥ : EReal)) :
    IsERealConvexOn (Set.univ : Set (Fin n → ℝ))
      (fun z => if z ∈ C then f z else ⊤) := by
  intro x y hx hy a b ha hb hab hxy
  by_cases hZeroA : a = 0
  · have hBOne : b = 1 := by linarith
    subst hZeroA
    subst hBOne
    simp
  by_cases hZeroB : b = 0
  · have hAOne : a = 1 := by linarith
    subst hZeroB
    subst hAOne
    simp
  have hPosA : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using hZeroA)
  have hPosB : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hZeroB)
  by_cases hxC : x ∈ C
  · by_cases hyC : y ∈ C
    · have hxyC : a • x + b • y ∈ C := hCconv hxC hyC ha hb hab
      simpa [hxC, hyC, hxyC] using hConv hxC hyC ha hb hab hxyC
    · have hLeftNeBot : (a : EReal) * (if x ∈ C then f x else ⊤) ≠ (⊥ : EReal) := by
        simpa [hxC] using helperForLemma33_0_5_positiveReal_mul_ne_bot hPosA (hNoBot x hxC)
      have hRightTop : (b : EReal) * (if y ∈ C then f y else ⊤) = ⊤ := by
        simpa [hyC] using (EReal.coe_mul_top_of_pos (x := b) hPosB)
      have hRhsTop :
          (a : EReal) * (if x ∈ C then f x else ⊤) +
            (b : EReal) * (if y ∈ C then f y else ⊤) = ⊤ := by
        rw [hRightTop]
        exact EReal.add_top_of_ne_bot hLeftNeBot
      by_cases hxyC : a • x + b • y ∈ C
      · calc
          (if a • x + b • y ∈ C then f (a • x + b • y) else ⊤)
              = f (a • x + b • y) := by simp [hxyC]
          _ ≤ ⊤ := le_top
          _ = (a : EReal) * (if x ∈ C then f x else ⊤) +
                (b : EReal) * (if y ∈ C then f y else ⊤) := hRhsTop.symm
      · simpa [hxyC] using (le_of_eq hRhsTop.symm)
  · by_cases hyC : y ∈ C
    · have hLeftTop : (a : EReal) * (if x ∈ C then f x else ⊤) = ⊤ := by
        simpa [hxC] using (EReal.coe_mul_top_of_pos (x := a) hPosA)
      have hRightNeBot : (b : EReal) * (if y ∈ C then f y else ⊤) ≠ (⊥ : EReal) := by
        simpa [hyC] using helperForLemma33_0_5_positiveReal_mul_ne_bot hPosB (hNoBot y hyC)
      have hRhsTop :
          (a : EReal) * (if x ∈ C then f x else ⊤) +
            (b : EReal) * (if y ∈ C then f y else ⊤) = ⊤ := by
        rw [hLeftTop]
        exact EReal.top_add_of_ne_bot hRightNeBot
      by_cases hxyC : a • x + b • y ∈ C
      · calc
          (if a • x + b • y ∈ C then f (a • x + b • y) else ⊤)
              = f (a • x + b • y) := by simp [hxyC]
          _ ≤ ⊤ := le_top
          _ = (a : EReal) * (if x ∈ C then f x else ⊤) +
                (b : EReal) * (if y ∈ C then f y else ⊤) := hRhsTop.symm
      · simpa [hxyC] using (le_of_eq hRhsTop.symm)
    · have hLeftTop : (a : EReal) * (if x ∈ C then f x else ⊤) = ⊤ := by
        simpa [hxC] using (EReal.coe_mul_top_of_pos (x := a) hPosA)
      have hRightTop : (b : EReal) * (if y ∈ C then f y else ⊤) = ⊤ := by
        simpa [hyC] using (EReal.coe_mul_top_of_pos (x := b) hPosB)
      have hRhsTop :
          (a : EReal) * (if x ∈ C then f x else ⊤) +
            (b : EReal) * (if y ∈ C then f y else ⊤) = ⊤ := by
        rw [hLeftTop]
        exact EReal.top_add_of_ne_bot (by simpa [hRightTop])
      by_cases hxyC : a • x + b • y ∈ C
      · calc
          (if a • x + b • y ∈ C then f (a • x + b • y) else ⊤)
              = f (a • x + b • y) := by simp [hxyC]
          _ ≤ ⊤ := le_top
          _ = (a : EReal) * (if x ∈ C then f x else ⊤) +
                (b : EReal) * (if y ∈ C then f y else ⊤) := hRhsTop.symm
      · simpa [hxyC] using (le_of_eq hRhsTop.symm)

/-- Helper for Lemma33.0.5: an affine lower bound gives a uniform finite lower bound on any open
ball around `x`. -/
lemma helperForLemma33_0_5_ball_uniform_affine_lowerBound {n : ℕ}
    (ε : {r : ℝ // 0 < r}) (x b : Fin n → ℝ) (β : ℝ)
    {w : Fin n → ℝ} (hw : ‖w - x‖ < ε.1) :
    (((-((‖x‖ + ε.1) * (Finset.univ.sum fun i : Fin n => |b i|)) - β : ℝ)) : EReal) ≤
      ((w ⬝ᵥ b - β : ℝ) : EReal) := by
  let S : ℝ := Finset.univ.sum fun i : Fin n => |b i|
  have hnorm : ‖w‖ ≤ ‖x‖ + ε.1 := by
    calc
      ‖w‖ = ‖(w - x) + x‖ := by abel_nf
      _ ≤ ‖w - x‖ + ‖x‖ := norm_add_le _ _
      _ ≤ ε.1 + ‖x‖ := by linarith
      _ = ‖x‖ + ε.1 := by ring
  have hsumNonneg : 0 ≤ S := by
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hmul : ‖w‖ * S ≤ (‖x‖ + ε.1) * S :=
    mul_le_mul_of_nonneg_right hnorm hsumNonneg
  have hdotLower' : -(‖w‖ * S) ≤ w ⬝ᵥ b := by
    have hupper := section13_dotProduct_le_norm_mul_sum_abs (x := -w) (y := b)
    have hupper' : -(w ⬝ᵥ b) ≤ ‖w‖ * S := by
      simpa [dotProduct, S] using hupper
    linarith
  have hdotLower : -((‖x‖ + ε.1) * S) ≤ w ⬝ᵥ b := by
    linarith
  have hReal : -((‖x‖ + ε.1) * S) - β ≤ w ⬝ᵥ b - β := sub_le_sub_right hdotLower β
  exact_mod_cast hReal

/-- Helper for Lemma33.0.5: the true fixed-radius `(⊥, ⊤)` branch is exactly where the direct
local-witness proof stops. -/
lemma helperForLemma33_0_5_fixedRadiusLocalInfimum_mixedBotTop_collapse {n : ℕ}
    (ε : {r : ℝ // 0 < r}) {f : (Fin n → ℝ) → EReal}
    {x y : Fin n → ℝ} {a b : ℝ}
    (hConv : IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) f)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hPosA : 0 < a) (_hPosB : 0 < b)
    (hLocalInfXBot : (⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) = ⊥)
    (_hLocalInfYTop : (⨅ w : {w : Fin n → ℝ // ‖w - y‖ < ε.1}, f w.1) = ⊤) :
    (⨅ w : {w : Fin n → ℝ // ‖w - (a • x + b • y)‖ < ε.1}, f w.1) = ⊥ := by
  have hBotWitness :
      ∃ w : Fin n → ℝ, ‖w - x‖ < ε.1 ∧ f w = (⊥ : EReal) := by
    by_contra hNoWitness
    have hNoBotOnBall : ∀ w : Fin n → ℝ, ‖w - x‖ < ε.1 → f w ≠ (⊥ : EReal) := by
      intro w hw
      exact fun hwBot => hNoWitness ⟨w, hw, hwBot⟩
    let fBall : (Fin n → ℝ) → EReal :=
      fun z => if ‖z - x‖ < ε.1 then f z else ⊤
    have hBallConv :
        IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) fBall :=
      helperForLemma33_0_5_extendByTopOnConvexSet_preserves_convexity
        (C := Metric.ball x ε.1) (f := f)
        (by simpa using convex_ball x ε.1)
        (by
          intro u v hu hv a b ha hb hab huv
          exact hConv (Set.mem_univ u) (Set.mem_univ v) ha hb hab (Set.mem_univ _))
        (by
          intro z hz
          exact hNoBotOnBall z (by simpa [Metric.mem_ball] using hz))
    have hBallProper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) fBall := by
      refine ⟨?_, ?_, ?_⟩
      · simpa [ConvexFunction] using
          helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction hBallConv
      · rcases helperForLemma33_0_5_localInfimum_eq_bot_implies_exists_ballWitness_lt
            (ε := ε) (f := f) (x := x) hLocalInfXBot (z := (0 : EReal))
            (by simp) with ⟨w, hwBall, hwLt⟩
        refine ⟨(w, 0), ?_⟩
        constructor
        · exact Set.mem_univ w
        · have hwLe : f w ≤ (0 : EReal) := le_of_lt hwLt
          simpa [fBall, hwBall] using hwLe
      · intro z hzUniv
        by_cases hzBall : ‖z - x‖ < ε.1
        · simpa [fBall, hzBall] using hNoBotOnBall z hzBall
        · simp [fBall, hzBall]
    rcases properConvexFunctionOn_exists_linear_lowerBound hBallProper with ⟨b, β, hLower⟩
    let m : ℝ := -((‖x‖ + ε.1) * (Finset.univ.sum fun i : Fin n => |b i|)) - β
    have hLocalInfLower : ((m : ℝ) : EReal) ≤
        (⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) := by
      refine le_iInf ?_
      intro w
      have hAffineLower :
          ((w.1 ⬝ᵥ b - β : ℝ) : EReal) ≤ fBall w.1 := by
        simpa using hLower w.1
      have hUniformLower :
          ((m : ℝ) : EReal) ≤ ((w.1 ⬝ᵥ b - β : ℝ) : EReal) :=
        helperForLemma33_0_5_ball_uniform_affine_lowerBound
          (ε := ε) (x := x) (b := b) (β := β) w.2
      have hBallEq : fBall w.1 = f w.1 := by
        simp [fBall, w.2]
      exact le_trans hUniformLower (by simpa [hBallEq] using hAffineLower)
    have hImpossible : ¬ ((m : ℝ) : EReal) ≤ (⊥ : EReal) := by
      simp
    exact hImpossible (by simpa [hLocalInfXBot] using hLocalInfLower)
  rcases hBotWitness with ⟨w, hwBall, hwBot⟩
  exact
    helperForLemma33_0_5_fixedRadiusLocalInfimum_botWitness_forces_targetBot
      (ε := ε) (f := f) (x := x) (y := y) (w := w) hConv ha hb hab hPosA hwBall hwBot

/-- Helper for Lemma33.0.5: the true fixed-radius `(⊥, ⊤)` branch is exactly where the direct
local-witness proof stops. -/
lemma helperForLemma33_0_5_fixedRadiusLocalInfimum_exceptional_branch {n : ℕ}
    (ε : {r : ℝ // 0 < r}) {f : (Fin n → ℝ) → EReal}
    {x y : Fin n → ℝ} {a b : ℝ}
    (hConv : IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) f)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hPosA : 0 < a) (hPosB : 0 < b)
    (hLocalInfXBot : (⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) = ⊥)
    (hLocalInfYTop : (⨅ w : {w : Fin n → ℝ // ‖w - y‖ < ε.1}, f w.1) = ⊤) :
    (⨅ w : {w : Fin n → ℝ // ‖w - (a • x + b • y)‖ < ε.1}, f w.1) ≤
      (a : EReal) * (⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) +
        (b : EReal) * (⨅ w : {w : Fin n → ℝ // ‖w - y‖ < ε.1}, f w.1) := by
  -- Reduce the branch to the exact-collapse theorem, after which the right-hand side simplifies
  -- to `⊥` because the positive `x`-weight multiplies the `⊥` endpoint local infimum.
  have hTargetBot :
      (⨅ w : {w : Fin n → ℝ // ‖w - (a • x + b • y)‖ < ε.1}, f w.1) = ⊥ :=
    helperForLemma33_0_5_fixedRadiusLocalInfimum_mixedBotTop_collapse
      (ε := ε) (f := f) (x := x) (y := y) hConv ha hb hab hPosA hPosB
      hLocalInfXBot hLocalInfYTop
  have hRhsBot :
      (a : EReal) * (⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) +
          (b : EReal) * (⨅ w : {w : Fin n → ℝ // ‖w - y‖ < ε.1}, f w.1) = ⊥ := by
    simp [hLocalInfXBot, hLocalInfYTop, EReal.coe_mul_bot_of_pos hPosA]
  rw [hTargetBot, hRhsBot]

/-- Helper for Lemma33.0.5: the two-layer `sup-inf` closure is the negative of the
corresponding `inf-sup` closure of the negated family. -/
lemma helperForLemma33_0_5_negatedTwoLayerClosureIdentity
    {ι : Sort*} {κ : ι → Sort*} (F : ∀ i, κ i → EReal) :
    (⨆ i, ⨅ j, F i j) = -(⨅ i, ⨆ j, -F i j) := by
  -- Rewrite the inner `iInf` as a negated `iSup`, then rewrite the outer `iSup` in the same
  -- way.
  calc
    (⨆ i, ⨅ j, F i j) = ⨆ i, -(⨆ j, -F i j) := by
      simp [helperForLemma33_0_5_neg_iSup_neg_eq_iInf]
    _ = -(⨅ i, ⨆ j, -F i j) := by
      symm
      simpa using
        helperForLemma33_0_5_neg_iInf_neg_eq_iSup (fun i => -(⨆ j, -F i j))

/-- Helper for Lemma33.0.5: after swapping the variables and negating the bifunction, the
convex closure in the second variable becomes the negative of the original concave closure in
the first variable. -/
lemma helperForLemma33_0_5_swappedNegatedClosureIdentity
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (v : Fin n → ℝ) :
    convexClosureInSecond (fun v' u' => -K u' v') v u = -concaveClosureInFirst K u v := by
  -- Unfold the two coordinatewise closures and apply the generic two-layer identity to the
  -- swapped family of local sections.
  unfold convexClosureInSecond concaveClosureInFirst
  simpa using
    helperForLemma33_0_5_negatedTwoLayerClosureIdentity
      (fun (ε : {ε : ℝ // 0 < ε})
        (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}) => -K w.1 v)

/-- Helper for Lemma33.0.5: at a fixed radius, local suprema preserve concavity. -/
lemma helperForLemma33_0_5_fixedRadiusLocalSupremum_preserves_concavity {n : ℕ}
    (ε : {r : ℝ // 0 < r}) {f : (Fin n → ℝ) → EReal}
    (hConc : IsERealConcaveOn (Set.univ : Set (Fin n → ℝ)) f) :
    IsERealConcaveOn (Set.univ : Set (Fin n → ℝ))
      (fun x => ⨆ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) := by
  intro x y hx hy a b ha hb hab hz
  by_cases hZeroA : a = 0
  · have hBOne : b = 1 := by linarith
    -- When the first weight vanishes, the Jensen inequality reduces to the second endpoint.
    subst hZeroA
    subst hBOne
    simpa using
      (fun w hw =>
        le_iSup
          (fun q : {q : Fin n → ℝ // ‖q - (0 • x + 1 • y)‖ < ε.1} => f q.1)
          ⟨w, by simpa using hw⟩)
  by_cases hZeroB : b = 0
  · have hAOne : a = 1 := by linarith
    -- The symmetric zero-weight case reduces to the first endpoint.
    subst hZeroB
    subst hAOne
    simpa using
      (fun w hw =>
        le_iSup
          (fun q : {q : Fin n → ℝ // ‖q - (1 • x + 0 • y)‖ < ε.1} => f q.1)
          ⟨w, by simpa using hw⟩)
  have hPosA : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using hZeroA)
  have hPosB : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hZeroB)
  let wx : {w : Fin n → ℝ // ‖w - x‖ < ε.1} := ⟨x, by simpa using ε.2⟩
  let wy : {w : Fin n → ℝ // ‖w - y‖ < ε.1} := ⟨y, by simpa using ε.2⟩
  letI : Nonempty {w : Fin n → ℝ // ‖w - x‖ < ε.1} := ⟨wx⟩
  letI : Nonempty {w : Fin n → ℝ // ‖w - y‖ < ε.1} := ⟨wy⟩
  have hProduct :
      ((a : EReal) * (⨆ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1)) +
          ((b : EReal) * (⨆ w : {w : Fin n → ℝ // ‖w - y‖ < ε.1}, f w.1)) ≤
        ⨆ p :
            {w : Fin n → ℝ // ‖w - x‖ < ε.1} ×
              {w : Fin n → ℝ // ‖w - y‖ < ε.1},
          (a : EReal) * f p.1.1 + (b : EReal) * f p.2.1 := by
    -- Combine independent near-maximizers from the two endpoint balls into one product witness.
    simpa using helperForLemma33_0_5_weightedSum_le_productIndexed_iSup hPosA hPosB
      (f := fun w : {w : Fin n → ℝ // ‖w - x‖ < ε.1} => f w.1)
      (g := fun w : {w : Fin n → ℝ // ‖w - y‖ < ε.1} => f w.1)
  have hJensenOnProduct :
      (⨆ p :
          {w : Fin n → ℝ // ‖w - x‖ < ε.1} ×
            {w : Fin n → ℝ // ‖w - y‖ < ε.1},
        (a : EReal) * f p.1.1 + (b : EReal) * f p.2.1) ≤
        ⨆ w : {w : Fin n → ℝ // ‖w - (a • x + b • y)‖ < ε.1}, f w.1 := by
    -- Each pair of endpoint witnesses produces a witness in the target ball by the same
    -- convex combination, and concavity compares the values at those three points.
    refine iSup_le ?_
    intro p
    rcases p with ⟨w₁, w₂⟩
    have hBall :
        ‖(a • w₁.1 + b • w₂.1) - (a • x + b • y)‖ < ε.1 :=
      helperForLemma33_0_5_convexCombination_mem_ball w₁.2 w₂.2 ha hb hab
    let wCombo : {w : Fin n → ℝ // ‖w - (a • x + b • y)‖ < ε.1} :=
      ⟨a • w₁.1 + b • w₂.1, hBall⟩
    have hConcavity :
        (a : EReal) * f w₁.1 + (b : EReal) * f w₂.1 ≤ f (a • w₁.1 + b • w₂.1) :=
      hConc (x := w₁.1) (y := w₂.1) (Set.mem_univ _) (Set.mem_univ _) ha hb hab (Set.mem_univ _)
    exact le_trans hConcavity
      (le_iSup (fun w : {w : Fin n → ℝ // ‖w - (a • x + b • y)‖ < ε.1} => f w.1) wCombo)
  exact le_trans hProduct hJensenOnProduct

/-- Helper for Lemma33.0.5: at a fixed radius, local infima preserve convexity. -/
lemma helperForLemma33_0_5_fixedRadiusLocalInfimum_target_le_productInfimum {n : ℕ}
    (ε : {r : ℝ // 0 < r}) {f : (Fin n → ℝ) → EReal}
    {x y : Fin n → ℝ} {a b : ℝ}
    (hConv : IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) f)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (⨅ w : {w : Fin n → ℝ // ‖w - (a • x + b • y)‖ < ε.1}, f w.1) ≤
      ⨅ p :
          {w : Fin n → ℝ // ‖w - x‖ < ε.1} ×
            {w : Fin n → ℝ // ‖w - y‖ < ε.1},
        (a : EReal) * f p.1.1 + (b : EReal) * f p.2.1 := by
  -- Each pair of endpoint witnesses gives one witness in the target ball, and Jensen compares
  -- the corresponding function values.
  refine le_iInf ?_
  intro p
  rcases p with ⟨w₁, w₂⟩
  have hBall :
      ‖(a • w₁.1 + b • w₂.1) - (a • x + b • y)‖ < ε.1 :=
    helperForLemma33_0_5_convexCombination_mem_ball w₁.2 w₂.2 ha hb hab
  let wCombo : {w : Fin n → ℝ // ‖w - (a • x + b • y)‖ < ε.1} :=
    ⟨a • w₁.1 + b • w₂.1, hBall⟩
  have hPoint :
      (⨅ w : {w : Fin n → ℝ // ‖w - (a • x + b • y)‖ < ε.1}, f w.1) ≤ f wCombo.1 :=
    iInf_le
      (fun w : {w : Fin n → ℝ // ‖w - (a • x + b • y)‖ < ε.1} => f w.1)
      wCombo
  have hJensen :
      f (a • w₁.1 + b • w₂.1) ≤ (a : EReal) * f w₁.1 + (b : EReal) * f w₂.1 :=
    hConv (x := w₁.1) (y := w₂.1) (Set.mem_univ _) (Set.mem_univ _) ha hb hab (Set.mem_univ _)
  exact le_trans hPoint (by simpa [wCombo] using hJensen)


end Section33
end Chap07

/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section38_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part12

open scoped Pointwise

section Chap08
section Section38

/-- The weak topology on the algebraic dual induced by evaluation, used to talk about
lower semicontinuity (and hence "closedness") of functions on dual spaces. -/
noncomputable local instance instTopologicalSpace_moduleDual_weak_part3
    {E : Type*} [AddCommGroup E] [Module ℝ E] :
    TopologicalSpace (Module.Dual ℝ E) :=
  WeakBilin.instTopologicalSpace
    (B := (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)).flip)

-- Proof sketch: `convexIndicatorBifunction A u x` is by definition `0` or `+∞`, hence never `-∞`.
-- It is not identically `+∞` since for any `u`, the value at `x = A u` is `0`.
/-- Properness data for the convex indicator bifunction of a linear map on `ℝ^m` and `ℝ^n`. -/
lemma convexIndicatorBifunction_proper {m n : Nat}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    (∀ u x, convexIndicatorBifunction A u x ≠ ⊥) ∧ ∃ u x, convexIndicatorBifunction A u x ≠ ⊤ :=
  by
    constructor
    · -- Unfold the indicator: every value is either `0` or `⊤`, so `⊥` never occurs.
      intro u x
      by_cases hx : x = A u <;> simp [convexIndicatorBifunction, hx]
    · -- The graph point `x = A 0` already gives the finite value `0`.
      refine ⟨0, A 0, ?_⟩
      simp [convexIndicatorBifunction]

/-- The convex indicator bifunction of a linear map, bundled as a
`FiberwiseProperConvexBifunction`. -/
noncomputable def convexIndicatorFiberwiseProperConvexBifunction {m n : Nat}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    FiberwiseProperConvexBifunction m n :=
  ⟨convexIndicatorBifunction A,
    convexIndicatorBifunction_proper A,
    isFiberwiseConvexBifunction_convexIndicatorBifunction A⟩

/-- Helper for Proposition 38.4.3: at the graph point `x = A u`, the summand in the defining
infimum already equals the convex indicator of the composite map `B ∘ A`. -/
lemma helperForProposition_38_4_3_graphSummand_eq_compositeIndicator {m n p : Nat}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (B : (Fin n → ℝ) →ₗ[ℝ] (Fin p → ℝ))
    (u : Fin m → ℝ) (y : Fin p → ℝ) :
    convexIndicatorBifunction A u (A u) + convexIndicatorBifunction B (A u) y =
      convexIndicatorBifunction (B.comp A) u y := by
  -- Collapse the first indicator at its graph point and rewrite the remaining graph condition.
  simp [convexIndicatorBifunction]

/-- Helper for Proposition 38.4.3: every summand appearing in the composition infimum is
nonnegative, since it is always either `0` or `⊤`. -/
lemma helperForProposition_38_4_3_summand_nonneg {m n p : Nat}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (B : (Fin n → ℝ) →ₗ[ℝ] (Fin p → ℝ))
    (u : Fin m → ℝ) (y : Fin p → ℝ) (x : Fin n → ℝ) :
    0 ≤ convexIndicatorBifunction A u x + convexIndicatorBifunction B x y := by
  -- Split on whether `x` lies on the graph of `A`, then on whether `y` lies on the graph of `B`.
  by_cases hx : x = A u
  · by_cases hy : y = B (A u)
    · simp [convexIndicatorBifunction, hx, hy]
    · simp [convexIndicatorBifunction, hx, hy]
  · by_cases hy : y = B x
    · simp [convexIndicatorBifunction, hx, hy]
    · simp [convexIndicatorBifunction, hx, hy]

/-- Helper for Proposition 38.4.3: away from the composite graph `y = B (A u)`, every summand in
the defining infimum is `⊤`. -/
lemma helperForProposition_38_4_3_summand_eq_top_of_ne_comp_graph {m n p : Nat}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (B : (Fin n → ℝ) →ₗ[ℝ] (Fin p → ℝ))
    (u : Fin m → ℝ) (y : Fin p → ℝ) (x : Fin n → ℝ)
    (hy : y ≠ B (A u)) :
    convexIndicatorBifunction A u x + convexIndicatorBifunction B x y = ⊤ := by
  -- If `x = A u`, the second indicator is already off the graph; otherwise the first one is `⊤`.
  by_cases hx : x = A u
  · subst hx
    simp [convexIndicatorBifunction, hy]
  · by_cases hxy : y = B x
    · simp [convexIndicatorBifunction, hx, hxy]
    · simp [convexIndicatorBifunction, hx, hxy]

-- Proof sketch: Unfold `bifunctionCompose` and the two indicator bifunctions. For fixed `u` and `y`,
-- the infimum over `x` is `0` exactly when `y = B (A u)` (take `x = A u`), and is `+∞` otherwise.
/-- Proposition 38.4.3: Let `F` be the convex indicator bifunction of a linear transformation
`A : ℝ^m → ℝ^n`, and let `G` be the convex indicator bifunction of a linear transformation
`B : ℝ^n → ℝ^p`. Then the composed bifunction `G ⊙ F` is the convex indicator bifunction of the
composition `B ∘ A : ℝ^m → ℝ^p`. -/
theorem bifunctionCompose_convexIndicatorBifunction_eq_convexIndicatorBifunction_comp {m n p : Nat}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (B : (Fin n → ℝ) →ₗ[ℝ] (Fin p → ℝ)) :
    bifunctionCompose (convexIndicatorFiberwiseProperConvexBifunction B)
        (convexIndicatorFiberwiseProperConvexBifunction A) =
      convexIndicatorBifunction (B.comp A) :=
  by
  funext u y
  rw [bifunctionCompose]
  by_cases hy : y = B (A u)
  · -- On the composite graph, choose the witness `x = A u` to get the upper bound `0`.
    have hupper :
        (⨅ x : Fin n → ℝ,
            convexIndicatorBifunction A u x + convexIndicatorBifunction B x y) ≤ 0 := by
      calc
        (⨅ x : Fin n → ℝ,
            convexIndicatorBifunction A u x + convexIndicatorBifunction B x y) ≤
            convexIndicatorBifunction A u (A u) + convexIndicatorBifunction B (A u) y := by
              exact iInf_le _ (A u)
        _ = convexIndicatorBifunction (B.comp A) u y :=
          helperForProposition_38_4_3_graphSummand_eq_compositeIndicator A B u y
        _ = 0 := by
          simp [convexIndicatorBifunction, hy]
    -- Every summand is at least `0`, so the infimum cannot drop below `0`.
    have hlower :
        0 ≤ (⨅ x : Fin n → ℝ,
            convexIndicatorBifunction A u x + convexIndicatorBifunction B x y) := by
      refine le_iInf ?_
      intro x
      exact helperForProposition_38_4_3_summand_nonneg A B u y x
    have hrhs : convexIndicatorBifunction (B.comp A) u y = 0 := by
      simp [convexIndicatorBifunction, hy]
    rw [hrhs]
    exact le_antisymm hupper hlower
  · -- Off the composite graph, every summand is `⊤`, so the infimum is also `⊤`.
    have hsummand :
        ∀ x : Fin n → ℝ,
          convexIndicatorBifunction A u x + convexIndicatorBifunction B x y = ⊤ := by
      intro x
      exact helperForProposition_38_4_3_summand_eq_top_of_ne_comp_graph A B u y x hy
    have hlower :
        (⊤ : EReal) ≤ (⨅ x : Fin n → ℝ,
            convexIndicatorBifunction A u x + convexIndicatorBifunction B x y) := by
      refine le_iInf ?_
      intro x
      rw [hsummand x]
    have hrhs : convexIndicatorBifunction (B.comp A) u y = ⊤ := by
      simp [convexIndicatorBifunction, hy]
    rw [hrhs]
    exact le_antisymm le_top hlower

/-- Supremum-based composition of raw bifunctions on general types:
`(G ⊙ₛ F) u y = sup_x (F u x + G x y)`.

This is the same operation as `bifunctionComposeSup`, but with `Fin k → ℝ` replaced by arbitrary
types. It is used in Theorem 38.5 to express `F^* G^*` on dual spaces. -/
noncomputable def bifunctionComposeSupGeneric
    {U X Y : Type*} (G : X → Y → EReal) (F : U → X → EReal) : U → Y → EReal :=
  fun u y => ⨆ x : X, F u x + G x y

/-- Helper for Theorem 38.5: the left endpoint in the one-dimensional counterexample slice. -/
def helperForTheorem_38_5_zeroVec : Fin 1 → ℝ := 0

/-- Helper for Theorem 38.5: the right endpoint in the one-dimensional counterexample slice. -/
def helperForTheorem_38_5_oneVec : Fin 1 → ℝ := 1

/-- Helper for Theorem 38.5: the negative endpoint used in the actual-hypotheses counterexample. -/
def helperForTheorem_38_5_negOneVec : Fin 1 → ℝ := fun _ => (-1 : ℝ)

/-- Helper for Theorem 38.5: the midpoint used to violate convexity in Theorem 38.5. -/
noncomputable def helperForTheorem_38_5_halfVec : Fin 1 → ℝ := fun _ => (1 : ℝ) / 2

/-- Helper for Theorem 38.5: the raw right-factor counterexample bifunction, whose slices are the
singleton indicators at `0` and `1` on the two distinguished fibers and are otherwise `⊤`. -/
noncomputable def helperForTheorem_38_5_counterexampleSecondRaw
    (x y : Fin 1 → ℝ) : EReal :=
  if x 0 = 0 then
    if y = helperForTheorem_38_5_zeroVec then 0 else ⊤
  else if x 0 = 1 then
    if y = helperForTheorem_38_5_oneVec then 0 else ⊤
  else
    ⊤

/-- Helper for Theorem 38.5: the midpoint differs from the left endpoint. -/
lemma helperForTheorem_38_5_halfVec_ne_zero :
    helperForTheorem_38_5_halfVec ≠ helperForTheorem_38_5_zeroVec := by
  -- Compare the unique coordinate to separate `1 / 2` from `0`.
  intro h
  have h0 := congrArg (fun v : Fin 1 → ℝ => v 0) h
  norm_num [helperForTheorem_38_5_halfVec, helperForTheorem_38_5_zeroVec] at h0

/-- Helper for Theorem 38.5: the midpoint differs from the right endpoint. -/
lemma helperForTheorem_38_5_halfVec_ne_one :
    helperForTheorem_38_5_halfVec ≠ helperForTheorem_38_5_oneVec := by
  -- Compare the unique coordinate to separate `1 / 2` from `1`.
  intro h
  have h0 := congrArg (fun v : Fin 1 → ℝ => v 0) h
  norm_num [helperForTheorem_38_5_halfVec, helperForTheorem_38_5_oneVec] at h0

/-- Helper for Theorem 38.5: the raw right-factor counterexample is globally proper. -/
lemma helperForTheorem_38_5_counterexampleSecondRaw_proper :
    (∀ u x, helperForTheorem_38_5_counterexampleSecondRaw u x ≠ ⊥) ∧
      ∃ u x, helperForTheorem_38_5_counterexampleSecondRaw u x ≠ ⊤ := by
  constructor
  · -- The raw counterexample only takes the values `0` and `⊤`, so `⊥` never appears.
    intro u x
    by_cases hu0 : u 0 = 0
    · by_cases hx : x = helperForTheorem_38_5_zeroVec <;>
        simp [helperForTheorem_38_5_counterexampleSecondRaw, hu0, hx]
    · by_cases hu1 : u 0 = 1
      · by_cases hx : x = helperForTheorem_38_5_oneVec <;>
          simp [helperForTheorem_38_5_counterexampleSecondRaw, hu1, hx]
      · simp [helperForTheorem_38_5_counterexampleSecondRaw, hu0, hu1]
  · -- The point `(0, 0)` already witnesses a finite value.
    refine ⟨helperForTheorem_38_5_zeroVec, helperForTheorem_38_5_zeroVec, ?_⟩
    simp [helperForTheorem_38_5_counterexampleSecondRaw, helperForTheorem_38_5_zeroVec]

/-- Helper for Theorem 38.5: on the `x = 0` fiber, the raw counterexample slice is the singleton
indicator at `0`, hence convex. -/
lemma helperForTheorem_38_5_counterexampleSecondRaw_zeroSlice_convex
    (x : Fin 1 → ℝ) (hx : x 0 = 0) :
    IsERealConvex (helperForTheorem_38_5_counterexampleSecondRaw x) := by
  -- Rewrite the slice as the singleton indicator at `0` and invoke the standard indicator lemma.
  have hconv :
      ConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        (indicatorFunction ({helperForTheorem_38_5_zeroVec} : Set (Fin 1 → ℝ))) :=
    (properConvexFunctionOn_indicator_of_convex_of_nonempty
      (C := ({helperForTheorem_38_5_zeroVec} : Set (Fin 1 → ℝ))) (by simp) (by simp)).1
  have hEq :
      helperForTheorem_38_5_counterexampleSecondRaw x =
        indicatorFunction ({helperForTheorem_38_5_zeroVec} : Set (Fin 1 → ℝ)) := by
    funext y
    by_cases hy : y = helperForTheorem_38_5_zeroVec <;>
      simp [helperForTheorem_38_5_counterexampleSecondRaw, hx, hy, indicatorFunction]
  simpa [IsERealConvex, ConvexFunctionOn, helperForTheorem_38_1_epigraph_eq_univ, hEq] using hconv

/-- Helper for Theorem 38.5: on the `x = 1` fiber, the raw counterexample slice is the singleton
indicator at `1`, hence convex. -/
lemma helperForTheorem_38_5_counterexampleSecondRaw_oneSlice_convex
    (x : Fin 1 → ℝ) (hx1 : x 0 = 1) :
    IsERealConvex (helperForTheorem_38_5_counterexampleSecondRaw x) := by
  -- Rewrite the slice as the singleton indicator at `1` and invoke the standard indicator lemma.
  have hconv :
      ConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        (indicatorFunction ({helperForTheorem_38_5_oneVec} : Set (Fin 1 → ℝ))) :=
    (properConvexFunctionOn_indicator_of_convex_of_nonempty
      (C := ({helperForTheorem_38_5_oneVec} : Set (Fin 1 → ℝ))) (by simp) (by simp)).1
  have hEq :
      helperForTheorem_38_5_counterexampleSecondRaw x =
        indicatorFunction ({helperForTheorem_38_5_oneVec} : Set (Fin 1 → ℝ)) := by
    funext y
    have hx0 : x 0 ≠ 0 := by
      linarith
    by_cases hy : y = helperForTheorem_38_5_oneVec <;>
      simp [helperForTheorem_38_5_counterexampleSecondRaw, hx1, hy, indicatorFunction]
  simpa [IsERealConvex, ConvexFunctionOn, helperForTheorem_38_1_epigraph_eq_univ, hEq] using hconv

/-- Helper for Theorem 38.5: away from the two distinguished fibers, the raw counterexample slice
is constantly `⊤`, hence convex. -/
lemma helperForTheorem_38_5_counterexampleSecondRaw_topSlice_convex
    (x : Fin 1 → ℝ) (hx0 : x 0 ≠ 0) (hx1 : x 0 ≠ 1) :
    IsERealConvex (helperForTheorem_38_5_counterexampleSecondRaw x) := by
  -- Outside `x = 0` and `x = 1`, the slice has empty epigraph.
  have hconv :
      ConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (fun _ => (⊤ : EReal)) :=
    convexFunctionOn_const_top (C := (Set.univ : Set (Fin 1 → ℝ)))
  have hEq :
      helperForTheorem_38_5_counterexampleSecondRaw x = fun _ => (⊤ : EReal) := by
    funext y
    simp [helperForTheorem_38_5_counterexampleSecondRaw, hx0, hx1]
  simpa [IsERealConvex, ConvexFunctionOn, helperForTheorem_38_1_epigraph_eq_univ, hEq] using hconv

/-- Helper for Theorem 38.5: every fiber of the raw right-factor counterexample is convex. -/
lemma helperForTheorem_38_5_counterexampleSecondRaw_convex :
    ∀ x, IsERealConvex (helperForTheorem_38_5_counterexampleSecondRaw x) := by
  intro x
  -- Split according to which distinguished fiber `x` belongs to.
  by_cases hx0 : x 0 = 0
  · exact helperForTheorem_38_5_counterexampleSecondRaw_zeroSlice_convex x hx0
  · by_cases hx1 : x 0 = 1
    · exact helperForTheorem_38_5_counterexampleSecondRaw_oneSlice_convex x hx1
    · exact helperForTheorem_38_5_counterexampleSecondRaw_topSlice_convex x hx0 hx1

/-- Helper for Theorem 38.5: the bundled right-factor counterexample allowed by the current local
formalization. -/
noncomputable def helperForTheorem_38_5_counterexampleSecondBifunction :
    FiberwiseProperConvexBifunction 1 1 :=
  { toFun := helperForTheorem_38_5_counterexampleSecondRaw
    proper := helperForTheorem_38_5_counterexampleSecondRaw_proper
    convex := helperForTheorem_38_5_counterexampleSecondRaw_convex }

/-- Helper for Theorem 38.5: the midpoint is the convex combination of the two endpoints. -/
lemma helperForTheorem_38_5_halfVec_eq_combo :
    ((1 - (1 / 2 : ℝ)) • helperForTheorem_38_5_zeroVec +
        (1 / 2 : ℝ) • helperForTheorem_38_5_oneVec) =
      helperForTheorem_38_5_halfVec := by
  -- Check the unique coordinate directly.
  funext i
  fin_cases i
  norm_num [helperForTheorem_38_5_zeroVec, helperForTheorem_38_5_oneVec,
    helperForTheorem_38_5_halfVec]

/-- Helper for Theorem 38.5: every composition summand in the counterexample is nonnegative. -/
lemma helperForTheorem_38_5_counterexample_summand_nonneg
    (u y x : Fin 1 → ℝ) :
    0 ≤ helperForTheorem_38_1_counterexampleSecondBifunction.toFun u x +
        helperForTheorem_38_5_counterexampleSecondBifunction.toFun x y := by
  -- Every summand is either `0` or `⊤`.
  by_cases hx0 : x 0 = 0
  · by_cases hy0 : y = helperForTheorem_38_5_zeroVec
    · simp [helperForTheorem_38_1_counterexampleSecondBifunction,
        helperForTheorem_38_5_counterexampleSecondBifunction,
        helperForTheorem_38_5_counterexampleSecondRaw, hx0, hy0]
    · simp [helperForTheorem_38_1_counterexampleSecondBifunction,
        helperForTheorem_38_5_counterexampleSecondBifunction,
        helperForTheorem_38_5_counterexampleSecondRaw, hx0, hy0]
  · by_cases hx1 : x 0 = 1
    · by_cases hy1 : y = helperForTheorem_38_5_oneVec
      · simp [helperForTheorem_38_1_counterexampleSecondBifunction,
          helperForTheorem_38_5_counterexampleSecondBifunction,
          helperForTheorem_38_5_counterexampleSecondRaw, hx1, hy1]
      · simp [helperForTheorem_38_1_counterexampleSecondBifunction,
          helperForTheorem_38_5_counterexampleSecondBifunction,
          helperForTheorem_38_5_counterexampleSecondRaw, hx1, hy1]
    · simp [helperForTheorem_38_1_counterexampleSecondBifunction,
        helperForTheorem_38_5_counterexampleSecondBifunction,
        helperForTheorem_38_5_counterexampleSecondRaw, hx0, hx1]

/-- Helper for Theorem 38.5: the counterexample composition vanishes at the left endpoint. -/
lemma helperForTheorem_38_5_counterexample_compose_zero
    (u : Fin 1 → ℝ) :
    bifunctionCompose helperForTheorem_38_5_counterexampleSecondBifunction
        helperForTheorem_38_1_counterexampleSecondBifunction u
        helperForTheorem_38_5_zeroVec = 0 := by
  -- Evaluate the infimum at the witness `x = 0` and bound every summand from below by `0`.
  have hupper :
      (⨅ x : Fin 1 → ℝ,
        helperForTheorem_38_1_counterexampleSecondBifunction.toFun u x +
          helperForTheorem_38_5_counterexampleSecondBifunction.toFun x
            helperForTheorem_38_5_zeroVec) ≤ 0 := by
    refine le_trans (iInf_le _ helperForTheorem_38_5_zeroVec) ?_
    simp [helperForTheorem_38_1_counterexampleSecondBifunction,
      helperForTheorem_38_5_counterexampleSecondBifunction,
      helperForTheorem_38_5_counterexampleSecondRaw,
      helperForTheorem_38_5_zeroVec]
  have hlower :
      0 ≤ (⨅ x : Fin 1 → ℝ,
        helperForTheorem_38_1_counterexampleSecondBifunction.toFun u x +
          helperForTheorem_38_5_counterexampleSecondBifunction.toFun x
            helperForTheorem_38_5_zeroVec) := by
    refine le_iInf ?_
    intro x
    exact helperForTheorem_38_5_counterexample_summand_nonneg u
      helperForTheorem_38_5_zeroVec x
  simpa [bifunctionCompose] using le_antisymm hupper hlower

/-- Helper for Theorem 38.5: the counterexample composition vanishes at the right endpoint. -/
lemma helperForTheorem_38_5_counterexample_compose_one
    (u : Fin 1 → ℝ) :
    bifunctionCompose helperForTheorem_38_5_counterexampleSecondBifunction
        helperForTheorem_38_1_counterexampleSecondBifunction u
        helperForTheorem_38_5_oneVec = 0 := by
  -- Evaluate the infimum at the witness `x = 1` and bound every summand from below by `0`.
  have hupper :
      (⨅ x : Fin 1 → ℝ,
        helperForTheorem_38_1_counterexampleSecondBifunction.toFun u x +
          helperForTheorem_38_5_counterexampleSecondBifunction.toFun x
            helperForTheorem_38_5_oneVec) ≤ 0 := by
    refine le_trans (iInf_le _ helperForTheorem_38_5_oneVec) ?_
    simp [helperForTheorem_38_1_counterexampleSecondBifunction,
      helperForTheorem_38_5_counterexampleSecondBifunction,
      helperForTheorem_38_5_counterexampleSecondRaw,
      helperForTheorem_38_5_oneVec]
  have hlower :
      0 ≤ (⨅ x : Fin 1 → ℝ,
        helperForTheorem_38_1_counterexampleSecondBifunction.toFun u x +
          helperForTheorem_38_5_counterexampleSecondBifunction.toFun x
            helperForTheorem_38_5_oneVec) := by
    refine le_iInf ?_
    intro x
    exact helperForTheorem_38_5_counterexample_summand_nonneg u
      helperForTheorem_38_5_oneVec x
  simpa [bifunctionCompose] using le_antisymm hupper hlower

/-- Helper for Theorem 38.5: at the midpoint, every summand in the counterexample composition is
already `⊤`. -/
lemma helperForTheorem_38_5_counterexample_summand_half_eq_top
    (u x : Fin 1 → ℝ) :
    helperForTheorem_38_1_counterexampleSecondBifunction.toFun u x +
        helperForTheorem_38_5_counterexampleSecondBifunction.toFun x
          helperForTheorem_38_5_halfVec = ⊤ := by
  -- The midpoint misses both singleton fibers, so every branch yields `⊤`.
  by_cases hx0 : x 0 = 0
  · simp [helperForTheorem_38_1_counterexampleSecondBifunction,
      helperForTheorem_38_5_counterexampleSecondBifunction,
      helperForTheorem_38_5_counterexampleSecondRaw, hx0,
      helperForTheorem_38_5_halfVec_ne_zero]
  · by_cases hx1 : x 0 = 1
    · simp [helperForTheorem_38_1_counterexampleSecondBifunction,
        helperForTheorem_38_5_counterexampleSecondBifunction,
        helperForTheorem_38_5_counterexampleSecondRaw, hx1,
        helperForTheorem_38_5_halfVec_ne_one]
    · simp [helperForTheorem_38_1_counterexampleSecondBifunction,
        helperForTheorem_38_5_counterexampleSecondBifunction,
        helperForTheorem_38_5_counterexampleSecondRaw, hx0, hx1]

/-- Helper for Theorem 38.5: the counterexample composition equals `⊤` at the midpoint. -/
lemma helperForTheorem_38_5_counterexample_compose_half
    (u : Fin 1 → ℝ) :
    bifunctionCompose helperForTheorem_38_5_counterexampleSecondBifunction
        helperForTheorem_38_1_counterexampleSecondBifunction u
        helperForTheorem_38_5_halfVec = ⊤ := by
  -- Since every summand is `⊤`, the infimum is also `⊤`.
  have hlower :
      (⊤ : EReal) ≤ (⨅ x : Fin 1 → ℝ,
        helperForTheorem_38_1_counterexampleSecondBifunction.toFun u x +
          helperForTheorem_38_5_counterexampleSecondBifunction.toFun x
            helperForTheorem_38_5_halfVec) := by
    refine le_iInf ?_
    intro x
    rw [helperForTheorem_38_5_counterexample_summand_half_eq_top u x]
  simpa [bifunctionCompose] using le_antisymm le_top hlower

/-- Helper for Theorem 38.5: the explicit one-dimensional specialization already violates the
first conjunct of the theorem. -/
lemma helperForTheorem_38_5_counterexample_compose_not_convex :
    ¬ IsFiberwiseConvexBifunction
      (bifunctionCompose helperForTheorem_38_5_counterexampleSecondBifunction
        helperForTheorem_38_1_counterexampleSecondBifunction) := by
  intro hConv
  let f : (Fin 1 → ℝ) → EReal :=
    fun y =>
      bifunctionCompose helperForTheorem_38_5_counterexampleSecondBifunction
        helperForTheorem_38_1_counterexampleSecondBifunction
        helperForTheorem_38_5_zeroVec y
  -- Convert the advertised slice convexity into convexity of the ordinary epigraph.
  have hEpiConv : Convex ℝ (epigraph (Set.univ : Set (Fin 1 → ℝ)) f) := by
    simpa [f, IsERealConvex, helperForTheorem_38_1_epigraph_eq_univ] using
      hConv helperForTheorem_38_5_zeroVec
  -- Jensen at `t = 1 / 2` forces the midpoint value to be bounded by `0`.
  have hineq' :
      f ((1 - (1 / 2 : ℝ)) • helperForTheorem_38_5_zeroVec +
          (1 / 2 : ℝ) • helperForTheorem_38_5_oneVec) ≤
        ((((1 - (1 / 2 : ℝ)) * 0 + (1 / 2 : ℝ) * 0 : ℝ) : EReal)) := by
    exact epigraph_combo_ineq_aux (f := f) (S := (Set.univ : Set (Fin 1 → ℝ)))
      (x := helperForTheorem_38_5_zeroVec) (y := helperForTheorem_38_5_oneVec)
      (μ := 0) (v := 0) (t := (1 / 2 : ℝ))
      hEpiConv (by trivial) (by trivial)
      (by simpa [f] using (helperForTheorem_38_5_counterexample_compose_zero
        helperForTheorem_38_5_zeroVec).le)
      (by simpa [f] using (helperForTheorem_38_5_counterexample_compose_one
        helperForTheorem_38_5_zeroVec).le)
      (by norm_num) (by norm_num)
  have hineq :
      f ((1 - (1 / 2 : ℝ)) • helperForTheorem_38_5_zeroVec +
          (1 / 2 : ℝ) • helperForTheorem_38_5_oneVec) ≤ (0 : EReal) := by
    simpa using hineq'
  rw [helperForTheorem_38_5_halfVec_eq_combo] at hineq
  have hhalf : f helperForTheorem_38_5_halfVec = ⊤ := by
    simpa [f] using helperForTheorem_38_5_counterexample_compose_half
      helperForTheorem_38_5_zeroVec
  rw [hhalf] at hineq
  simp at hineq

/-- Helper for Theorem 38.5: after specializing to the explicit counterexample, the entire target
conclusion is already false because the first conjunct fails. -/
lemma helperForTheorem_38_5_specializedTargetFalse :
    ¬ (IsFiberwiseConvexBifunction
          (bifunctionCompose helperForTheorem_38_5_counterexampleSecondBifunction
            helperForTheorem_38_1_counterexampleSecondBifunction) ∧
        ((intrinsicInterior ℝ
              (bifunctionDomBot
                (bifunctionInverse helperForTheorem_38_1_counterexampleSecondBifunction.toFun)) ∩
            intrinsicInterior ℝ
              (bifunctionDom helperForTheorem_38_5_counterexampleSecondBifunction.toFun)).Nonempty →
          bifunctionAdjoint
              (bifunctionCompose helperForTheorem_38_5_counterexampleSecondBifunction
                helperForTheorem_38_1_counterexampleSecondBifunction) =
            bifunctionComposeSupGeneric
              (bifunctionAdjoint helperForTheorem_38_1_counterexampleSecondBifunction.toFun)
              (bifunctionAdjoint helperForTheorem_38_5_counterexampleSecondBifunction.toFun) ∧
            ∀ (yStar : Module.Dual ℝ (Fin 1 → ℝ)) (uStar : Module.Dual ℝ (Fin 1 → ℝ)),
              ∃ xStar : Module.Dual ℝ (Fin 1 → ℝ),
                bifunctionComposeSupGeneric
                    (bifunctionAdjoint helperForTheorem_38_1_counterexampleSecondBifunction.toFun)
                    (bifunctionAdjoint helperForTheorem_38_5_counterexampleSecondBifunction.toFun)
                    yStar uStar =
                  (bifunctionAdjoint helperForTheorem_38_5_counterexampleSecondBifunction.toFun)
                    yStar xStar +
                  (bifunctionAdjoint helperForTheorem_38_1_counterexampleSecondBifunction.toFun)
                    xStar uStar)) := by
  intro hTarget
  -- The first conjunct is already contradicted by the explicit midpoint computation.
  exact helperForTheorem_38_5_counterexample_compose_not_convex hTarget.1

/-- Helper for Theorem 38.5: the universal statement asserted by the target theorem header. -/
abbrev helperForTheorem_38_5_universalClaim : Prop :=
  ∀ {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
      (G : FiberwiseProperConvexBifunction n p),
    IsFiberwiseConvexBifunction (bifunctionCompose G F) ∧
      ((intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
            intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty →
        bifunctionAdjoint (bifunctionCompose G F) =
            bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun) ∧
          (∀ (yStar : Module.Dual ℝ (Fin p → ℝ)) (uStar : Module.Dual ℝ (Fin m → ℝ)),
            ∃ xStar : Module.Dual ℝ (Fin n → ℝ),
              bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
                  yStar uStar =
                (bifunctionAdjoint G.toFun) yStar xStar +
                  (bifunctionAdjoint F.toFun) xStar uStar))

/-- Helper for Theorem 38.5: the theorem header is already refuted by specializing the universal
claim to the explicit one-dimensional counterexample. -/
lemma helperForTheorem_38_5_universalClaim_false :
    ¬ helperForTheorem_38_5_universalClaim := by
  intro hUniversal
  -- Specialize the advertised universal claim to the explicit `m = n = p = 1` counterexample.
  have hSpecialized :
      IsFiberwiseConvexBifunction
          (bifunctionCompose helperForTheorem_38_5_counterexampleSecondBifunction
            helperForTheorem_38_1_counterexampleSecondBifunction) ∧
        ((intrinsicInterior ℝ
              (bifunctionDomBot
                (bifunctionInverse helperForTheorem_38_1_counterexampleSecondBifunction.toFun)) ∩
            intrinsicInterior ℝ
              (bifunctionDom helperForTheorem_38_5_counterexampleSecondBifunction.toFun)).Nonempty →
          bifunctionAdjoint
              (bifunctionCompose helperForTheorem_38_5_counterexampleSecondBifunction
                helperForTheorem_38_1_counterexampleSecondBifunction) =
            bifunctionComposeSupGeneric
              (bifunctionAdjoint helperForTheorem_38_1_counterexampleSecondBifunction.toFun)
              (bifunctionAdjoint helperForTheorem_38_5_counterexampleSecondBifunction.toFun) ∧
            ∀ (yStar : Module.Dual ℝ (Fin 1 → ℝ)) (uStar : Module.Dual ℝ (Fin 1 → ℝ)),
              ∃ xStar : Module.Dual ℝ (Fin 1 → ℝ),
                bifunctionComposeSupGeneric
                    (bifunctionAdjoint helperForTheorem_38_1_counterexampleSecondBifunction.toFun)
                    (bifunctionAdjoint helperForTheorem_38_5_counterexampleSecondBifunction.toFun)
                    yStar uStar =
                  (bifunctionAdjoint helperForTheorem_38_5_counterexampleSecondBifunction.toFun)
                    yStar xStar +
                  (bifunctionAdjoint helperForTheorem_38_1_counterexampleSecondBifunction.toFun)
                    xStar uStar) := by
    simpa [helperForTheorem_38_5_universalClaim] using
      hUniversal helperForTheorem_38_1_counterexampleSecondBifunction
        helperForTheorem_38_5_counterexampleSecondBifunction
  -- The midpoint computation already refutes this specialized proposition.
  exact helperForTheorem_38_5_specializedTargetFalse hSpecialized

/-- Helper for Theorem 38.5: the first factor in the actual-hypotheses counterexample, equal to
the indicator of the open half-space `u₁ > 0`. -/
noncomputable def helperForTheorem_38_5_actualCounterexampleFirstRaw
    (u : Fin 1 → ℝ) (_x : Fin 1 → ℝ) : EReal :=
  if 0 < u 0 then 0 else ⊤

/-- Helper for Theorem 38.5: the second factor in the actual-hypotheses counterexample, the linear
functional `x ↦ x₁` viewed as a bifunction independent of `y`. -/
noncomputable def helperForTheorem_38_5_actualCounterexampleSecondRaw
    (x : Fin 1 → ℝ) (_y : Fin 1 → ℝ) : EReal :=
  ((x 0 : ℝ) : EReal)

/-- Helper for Theorem 38.5: the graph-domain half-space used to prove proper convexity of the
first actual-hypotheses counterexample factor. -/
def helperForTheorem_38_5_actualCounterexampleFirstGraphDomain : Set (Fin 2 → ℝ) :=
  {z | 0 < z (Fin.castAdd 1 0)}

/-- Helper for Theorem 38.5: the first actual-hypotheses counterexample factor is globally proper. -/
lemma helperForTheorem_38_5_actualCounterexampleFirst_proper :
    (∀ u x, helperForTheorem_38_5_actualCounterexampleFirstRaw u x ≠ ⊥) ∧
      ∃ u x, helperForTheorem_38_5_actualCounterexampleFirstRaw u x ≠ ⊤ := by
  constructor
  · -- The half-space indicator only takes the values `0` and `⊤`, so `⊥` never appears.
    intro u x
    by_cases hu : 0 < u 0 <;>
      simp [helperForTheorem_38_5_actualCounterexampleFirstRaw, hu]
  · -- Any point with positive first coordinate gives a finite witness.
    refine ⟨helperForTheorem_38_5_oneVec, helperForTheorem_38_5_zeroVec, ?_⟩
    simp [helperForTheorem_38_5_actualCounterexampleFirstRaw, helperForTheorem_38_5_oneVec]

/-- Helper for Theorem 38.5: each fiber of the first actual-hypotheses counterexample factor is
either the constant-zero function or the constant-`⊤` function, hence convex. -/
lemma helperForTheorem_38_5_actualCounterexampleFirst_convex :
    ∀ u, IsERealConvex (helperForTheorem_38_5_actualCounterexampleFirstRaw u) := by
  intro u
  by_cases hu : 0 < u 0
  · -- On the positive half-space the slice is constantly zero.
    have hconv0 :
        ConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (fun _ => (0 : EReal)) :=
      (properConvexFunctionOn_const (n := 1) (c := (0 : ℝ))).1
    have hEq :
        helperForTheorem_38_5_actualCounterexampleFirstRaw u = fun _ => (0 : EReal) := by
      funext x
      simp [helperForTheorem_38_5_actualCounterexampleFirstRaw, hu]
    simpa [IsERealConvex, ConvexFunctionOn, helperForTheorem_38_1_epigraph_eq_univ, hEq] using
      hconv0
  · -- Outside that half-space the slice is constantly `⊤`.
    have hconvTop :
        ConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (fun _ => (⊤ : EReal)) :=
      convexFunctionOn_const_top (C := (Set.univ : Set (Fin 1 → ℝ)))
    have hEq :
        helperForTheorem_38_5_actualCounterexampleFirstRaw u = fun _ => (⊤ : EReal) := by
      funext x
      simp [helperForTheorem_38_5_actualCounterexampleFirstRaw, hu]
    simpa [IsERealConvex, ConvexFunctionOn, helperForTheorem_38_1_epigraph_eq_univ, hEq] using
      hconvTop

/-- Helper for Theorem 38.5: the graph-domain half-space of the first actual-hypotheses
counterexample factor is convex. -/
lemma helperForTheorem_38_5_actualCounterexampleFirstGraphDomain_convex :
    Convex ℝ helperForTheorem_38_5_actualCounterexampleFirstGraphDomain := by
  intro p hp q hq a b ha hb hab
  -- Convex combinations preserve strict positivity of the first coordinate.
  change 0 < (a • p + b • q) (Fin.castAdd 1 0)
  have hp0 : 0 < p (Fin.castAdd 1 0) := hp
  have hq0 : 0 < q (Fin.castAdd 1 0) := hq
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by
      linarith
    simpa [ha0, hb1, Pi.smul_apply, smul_eq_mul] using hq0
  · have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hfirst : 0 < a * p (Fin.castAdd 1 0) := mul_pos haPos hp0
    have hsecond : 0 ≤ b * q (Fin.castAdd 1 0) := mul_nonneg hb (le_of_lt hq0)
    have hpos : 0 < a * p (Fin.castAdd 1 0) + b * q (Fin.castAdd 1 0) := by
      linarith
    simpa [Pi.smul_apply, smul_eq_mul] using hpos

/-- Helper for Theorem 38.5: the graph function of the first actual-hypotheses counterexample
factor is exactly the indicator of the open half-space `u₁ > 0`. -/
lemma helperForTheorem_38_5_actualCounterexampleFirst_graph_eq_indicator :
    bifunctionGraphFunction helperForTheorem_38_5_actualCounterexampleFirstRaw =
      indicatorFunction helperForTheorem_38_5_actualCounterexampleFirstGraphDomain := by
  funext z
  by_cases hz : 0 < z (Fin.castAdd 1 0)
  · -- On the half-space, both descriptions return `0`.
    simp [helperForTheorem_38_5_actualCounterexampleFirstRaw,
      helperForTheorem_38_5_actualCounterexampleFirstGraphDomain, indicatorFunction,
      bifunctionGraphFunction]
  · -- Off the half-space, both descriptions return `⊤`.
    simp [helperForTheorem_38_5_actualCounterexampleFirstRaw,
      helperForTheorem_38_5_actualCounterexampleFirstGraphDomain, indicatorFunction,
      bifunctionGraphFunction]

/-- Helper for Theorem 38.5: the first actual-hypotheses counterexample factor already satisfies
the theorem's `ProperConvexBifunction` hypothesis. -/
lemma helperForTheorem_38_5_actualCounterexampleFirst_properConvexRaw :
    ProperConvexBifunction helperForTheorem_38_5_actualCounterexampleFirstRaw := by
  have hproperOn :
      ProperConvexFunctionOn (Set.univ : Set (Fin 2 → ℝ))
        (indicatorFunction helperForTheorem_38_5_actualCounterexampleFirstGraphDomain) := by
    -- The graph is the indicator of a nonempty convex half-space.
    refine section16_properConvexFunctionOn_indicatorFunction_univ
      helperForTheorem_38_5_actualCounterexampleFirstGraphDomain_convex ?_
    refine ⟨Fin.append helperForTheorem_38_5_oneVec helperForTheorem_38_5_zeroVec, ?_⟩
    change 0 < helperForTheorem_38_5_oneVec 0
    norm_num [helperForTheorem_38_5_oneVec]
  have hproperGraphIndicator :
      ProperConvexERealFunction (F := Fin 2 → ℝ)
        (indicatorFunction helperForTheorem_38_5_actualCounterexampleFirstGraphDomain) :=
    helperForTheorem_21_3_properConvexEReal_of_properConvexFunctionOn_univ
      (f := indicatorFunction helperForTheorem_38_5_actualCounterexampleFirstGraphDomain) hproperOn
  have hproperGraph :
      ProperConvexERealFunction (F := Fin 2 → ℝ)
        (bifunctionGraphFunction helperForTheorem_38_5_actualCounterexampleFirstRaw) := by
    simpa [helperForTheorem_38_5_actualCounterexampleFirst_graph_eq_indicator] using
      hproperGraphIndicator
  have hgraphProperOn :
      ProperConvexFunctionOn (Set.univ : Set (Fin 2 → ℝ))
        (bifunctionGraphFunction helperForTheorem_38_5_actualCounterexampleFirstRaw) :=
    helperForTheorem_6_30_11_properConvexFunctionOn_univ_of_properConvexERealFunction
      (f := bifunctionGraphFunction helperForTheorem_38_5_actualCounterexampleFirstRaw)
      hproperGraph
  refine ⟨?_, hproperGraph⟩
  -- Convert back from the Chapter 1 API to the Chapter 30 graph-convexity predicate.
  simpa [ConvexBifunction, ConvexFunction] using hgraphProperOn.1

/-- Helper for Theorem 38.5: the first actual-hypotheses counterexample factor bundled as a
`FiberwiseProperConvexBifunction`. -/
noncomputable def helperForTheorem_38_5_actualCounterexampleFirstBifunction :
    FiberwiseProperConvexBifunction 1 1 where
  toFun := helperForTheorem_38_5_actualCounterexampleFirstRaw
  proper := helperForTheorem_38_5_actualCounterexampleFirst_proper
  convex := helperForTheorem_38_5_actualCounterexampleFirst_convex

/-- Helper for Theorem 38.5: the bundled first actual-hypotheses counterexample factor still
satisfies the theorem's `ProperConvexBifunction` hypothesis. -/
lemma helperForTheorem_38_5_actualCounterexampleFirst_properConvex :
    ProperConvexBifunction helperForTheorem_38_5_actualCounterexampleFirstBifunction.toFun := by
  simpa [helperForTheorem_38_5_actualCounterexampleFirstBifunction] using
    helperForTheorem_38_5_actualCounterexampleFirst_properConvexRaw

/-- Helper for Theorem 38.5: the second actual-hypotheses counterexample factor is globally
proper. -/
lemma helperForTheorem_38_5_actualCounterexampleSecond_proper :
    (∀ u x, helperForTheorem_38_5_actualCounterexampleSecondRaw u x ≠ ⊥) ∧
      ∃ u x, helperForTheorem_38_5_actualCounterexampleSecondRaw u x ≠ ⊤ := by
  constructor
  · -- Real-valued affine functions never take the value `⊥`.
    intro u x
    exact EReal.coe_ne_bot (u 0)
  · -- The origin gives a finite witness.
    refine ⟨helperForTheorem_38_5_zeroVec, helperForTheorem_38_5_zeroVec, ?_⟩
    simp [helperForTheorem_38_5_actualCounterexampleSecondRaw]

/-- Helper for Theorem 38.5: each fiber of the second actual-hypotheses counterexample factor is
a constant real function, hence convex. -/
lemma helperForTheorem_38_5_actualCounterexampleSecond_convex :
    ∀ x, IsERealConvex (helperForTheorem_38_5_actualCounterexampleSecondRaw x) := by
  intro x
  -- Each slice is the constant function with value `x₁`.
  have hconv :
      ConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (fun _ => ((x 0 : ℝ) : EReal)) :=
    (properConvexFunctionOn_const (n := 1) (c := x 0)).1
  simpa [IsERealConvex, ConvexFunctionOn, helperForTheorem_38_1_epigraph_eq_univ,
    helperForTheorem_38_5_actualCounterexampleSecondRaw] using hconv

/-- Helper for Theorem 38.5: the graph function of the second actual-hypotheses counterexample
factor is a proper convex affine map on `ℝ²`. -/
lemma helperForTheorem_38_5_actualCounterexampleSecond_graph_properConvexRaw :
    ProperConvexERealFunction (F := Fin 2 → ℝ)
      (bifunctionGraphFunction helperForTheorem_38_5_actualCounterexampleSecondRaw) := by
  constructor
  · constructor
    · -- The graph function is real-valued, so `⊥` never appears.
      intro z
      exact EReal.coe_ne_bot (z (Fin.castAdd 1 0))
    · -- The origin witnesses finiteness.
      refine ⟨0, ?_⟩
      simp [bifunctionGraphFunction, helperForTheorem_38_5_actualCounterexampleSecondRaw]
  · -- The first-coordinate functional is affine, so the Jensen inequality holds with equality.
    intro z w a b ha hb hab
    change (((a • z + b • w) (Fin.castAdd 1 0) : ℝ) : EReal) ≤
      ((a : EReal) * ((z (Fin.castAdd 1 0) : ℝ) : EReal) +
        (b : EReal) * ((w (Fin.castAdd 1 0) : ℝ) : EReal))
    simp [Pi.smul_apply]

/-- Helper for Theorem 38.5: the second actual-hypotheses counterexample factor already satisfies
the theorem's `ProperConvexBifunction` hypothesis. -/
lemma helperForTheorem_38_5_actualCounterexampleSecond_properConvexRaw :
    ProperConvexBifunction helperForTheorem_38_5_actualCounterexampleSecondRaw := by
  have hgraphProperOn :
      ProperConvexFunctionOn (Set.univ : Set (Fin 2 → ℝ))
        (bifunctionGraphFunction helperForTheorem_38_5_actualCounterexampleSecondRaw) :=
    helperForTheorem_6_30_11_properConvexFunctionOn_univ_of_properConvexERealFunction
      (f := bifunctionGraphFunction helperForTheorem_38_5_actualCounterexampleSecondRaw)
      helperForTheorem_38_5_actualCounterexampleSecond_graph_properConvexRaw
  refine ⟨?_, helperForTheorem_38_5_actualCounterexampleSecond_graph_properConvexRaw⟩
  simpa [ConvexBifunction, ConvexFunction] using hgraphProperOn.1

/-- Helper for Theorem 38.5: the second actual-hypotheses counterexample factor bundled as a
`FiberwiseProperConvexBifunction`. -/
noncomputable def helperForTheorem_38_5_actualCounterexampleSecondBifunction :
    FiberwiseProperConvexBifunction 1 1 where
  toFun := helperForTheorem_38_5_actualCounterexampleSecondRaw
  proper := helperForTheorem_38_5_actualCounterexampleSecond_proper
  convex := helperForTheorem_38_5_actualCounterexampleSecond_convex

/-- Helper for Theorem 38.5: the bundled second actual-hypotheses counterexample factor still
satisfies the theorem's `ProperConvexBifunction` hypothesis. -/
lemma helperForTheorem_38_5_actualCounterexampleSecond_properConvex :
    ProperConvexBifunction helperForTheorem_38_5_actualCounterexampleSecondBifunction.toFun := by
  simpa [helperForTheorem_38_5_actualCounterexampleSecondBifunction] using
    helperForTheorem_38_5_actualCounterexampleSecond_properConvexRaw

/-- Helper for Theorem 38.5: the midpoint of `1` and `-1` is `0`. -/
lemma helperForTheorem_38_5_one_and_negOne_midpoint_eq_zero :
    ((1 / 2 : ℝ) • helperForTheorem_38_5_oneVec +
        (1 / 2 : ℝ) • helperForTheorem_38_5_negOneVec) =
      helperForTheorem_38_5_zeroVec := by
  -- Check the unique coordinate directly.
  funext i
  fin_cases i
  norm_num [helperForTheorem_38_5_oneVec, helperForTheorem_38_5_negOneVec,
    helperForTheorem_38_5_zeroVec]

/-- Helper for Theorem 38.5: the zero vector does not lie in the positive half-space used by the
first actual-hypotheses counterexample factor. -/
lemma helperForTheorem_38_5_zeroVec_not_pos :
    ¬ 0 < helperForTheorem_38_5_zeroVec 0 := by
  norm_num [helperForTheorem_38_5_zeroVec]

/-- Helper for Theorem 38.5: the negative endpoint also lies outside that half-space. -/
lemma helperForTheorem_38_5_negOneVec_not_pos :
    ¬ 0 < helperForTheorem_38_5_negOneVec 0 := by
  norm_num [helperForTheorem_38_5_negOneVec]

/-- Helper for Theorem 38.5: on the positive half-space, the actual-hypotheses counterexample
composition is `⊥`. -/
lemma helperForTheorem_38_5_actualCounterexample_compose_eq_bot_of_pos
    (u y : Fin 1 → ℝ) (hu : 0 < u 0) :
    bifunctionCompose helperForTheorem_38_5_actualCounterexampleSecondBifunction
        helperForTheorem_38_5_actualCounterexampleFirstBifunction u y = ⊥ := by
  -- Rewrite the infimum and drive the linear second summand to `-∞` along the free `x`-direction.
  rw [bifunctionCompose, iInf_eq_bot]
  intro b hb
  rcases EReal.lt_iff_exists_rat_btwn.mp hb with ⟨q, -, hq⟩
  refine ⟨fun _ => (q - 1 : ℚ), ?_⟩
  have hlt : ((((q - 1 : ℚ) : ℝ) : EReal) < (b : EReal)) := by
    have hq' : ((((q - 1 : ℚ) : ℝ) : EReal) < (((q : ℚ) : ℝ) : EReal)) := by
      exact_mod_cast (show (q - 1 : ℚ) < q by linarith)
    exact lt_trans hq' hq
  simpa [helperForTheorem_38_5_actualCounterexampleFirstBifunction,
    helperForTheorem_38_5_actualCounterexampleSecondBifunction,
    helperForTheorem_38_5_actualCounterexampleFirstRaw,
    helperForTheorem_38_5_actualCounterexampleSecondRaw, hu] using hlt

/-- Helper for Theorem 38.5: outside the positive half-space, every summand in the actual-
hypotheses counterexample composition is already `⊤`, so the composition is `⊤`. -/
lemma helperForTheorem_38_5_actualCounterexample_compose_eq_top_of_not_pos
    (u y : Fin 1 → ℝ) (hu : ¬ 0 < u 0) :
    bifunctionCompose helperForTheorem_38_5_actualCounterexampleSecondBifunction
        helperForTheorem_38_5_actualCounterexampleFirstBifunction u y = ⊤ := by
  -- Every summand has its first factor equal to `⊤`, so the infimum cannot drop below `⊤`.
  have hlower :
      (⊤ : EReal) ≤
        ⨅ x : Fin 1 → ℝ,
          helperForTheorem_38_5_actualCounterexampleFirstBifunction.toFun u x +
            helperForTheorem_38_5_actualCounterexampleSecondBifunction.toFun x y := by
    refine le_iInf ?_
    intro x
    simp [helperForTheorem_38_5_actualCounterexampleFirstBifunction,
      helperForTheorem_38_5_actualCounterexampleSecondBifunction,
      helperForTheorem_38_5_actualCounterexampleFirstRaw,
      helperForTheorem_38_5_actualCounterexampleSecondRaw, hu]
  rw [bifunctionCompose]
  exact le_antisymm le_top hlower

/-- Helper for Theorem 38.5: the actual-hypotheses counterexample composition violates the
stronger Chapter 29 predicate `IsConvexBifunction`, even though the repaired theorem now keeps only
the weaker Chapter 30 graph-convex conclusion. -/
lemma helperForTheorem_38_5_actualCounterexample_compose_not_IsConvexBifunction :
    ¬ IsConvexBifunction
      (bifunctionCompose helperForTheorem_38_5_actualCounterexampleSecondBifunction
        helperForTheorem_38_5_actualCounterexampleFirstBifunction) := by
  intro hConv
  have hIneq :=
      hConv (helperForTheorem_38_5_oneVec, helperForTheorem_38_5_zeroVec)
        (helperForTheorem_38_5_negOneVec, helperForTheorem_38_5_zeroVec)
        (1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  -- Evaluate the midpoint and the two endpoints in the explicit one-dimensional configuration.
  simp [graphFunction] at hIneq
  have hmidU :
      ((2⁻¹ : ℝ) • helperForTheorem_38_5_oneVec +
          (2⁻¹ : ℝ) • helperForTheorem_38_5_negOneVec) =
        helperForTheorem_38_5_zeroVec := by
    simpa using helperForTheorem_38_5_one_and_negOne_midpoint_eq_zero
  have hmidY :
      ((2⁻¹ : ℝ) • helperForTheorem_38_5_zeroVec +
          (2⁻¹ : ℝ) • helperForTheorem_38_5_zeroVec) =
        helperForTheorem_38_5_zeroVec := by
    funext i
    fin_cases i
    norm_num [helperForTheorem_38_5_zeroVec]
  rw [hmidU, hmidY] at hIneq
  have hmid :
      bifunctionCompose helperForTheorem_38_5_actualCounterexampleSecondBifunction
          helperForTheorem_38_5_actualCounterexampleFirstBifunction
          helperForTheorem_38_5_zeroVec helperForTheorem_38_5_zeroVec = ⊤ :=
    helperForTheorem_38_5_actualCounterexample_compose_eq_top_of_not_pos
      helperForTheorem_38_5_zeroVec helperForTheorem_38_5_zeroVec
      helperForTheorem_38_5_zeroVec_not_pos
  have hone :
      bifunctionCompose helperForTheorem_38_5_actualCounterexampleSecondBifunction
          helperForTheorem_38_5_actualCounterexampleFirstBifunction
          helperForTheorem_38_5_oneVec helperForTheorem_38_5_zeroVec = ⊥ :=
    helperForTheorem_38_5_actualCounterexample_compose_eq_bot_of_pos
      helperForTheorem_38_5_oneVec helperForTheorem_38_5_zeroVec (by
        norm_num [helperForTheorem_38_5_oneVec])
  have hneg :
      bifunctionCompose helperForTheorem_38_5_actualCounterexampleSecondBifunction
          helperForTheorem_38_5_actualCounterexampleFirstBifunction
          helperForTheorem_38_5_negOneVec helperForTheorem_38_5_zeroVec = ⊤ :=
    helperForTheorem_38_5_actualCounterexample_compose_eq_top_of_not_pos
      helperForTheorem_38_5_negOneVec helperForTheorem_38_5_zeroVec
      helperForTheorem_38_5_negOneVec_not_pos
  rw [hmid, hone, hneg] at hIneq
  rw [EReal.mul_bot_of_pos (by norm_num), EReal.mul_top_of_pos (by norm_num)] at hIneq
  simp at hIneq

/-- Helper for Theorem 38.5: the theorem header is already refuted even under its actual proper-
convex hypotheses. -/
lemma helperForTheorem_38_5_actualCounterexample_refutesActualHypotheses :
    ProperConvexBifunction helperForTheorem_38_5_actualCounterexampleFirstBifunction.toFun ∧
      ProperConvexBifunction helperForTheorem_38_5_actualCounterexampleSecondBifunction.toFun ∧
      ¬ IsConvexBifunction
        (bifunctionCompose helperForTheorem_38_5_actualCounterexampleSecondBifunction
          helperForTheorem_38_5_actualCounterexampleFirstBifunction) := by
  constructor
  · -- The first counterexample factor satisfies the stated proper-convex hypothesis.
    exact helperForTheorem_38_5_actualCounterexampleFirst_properConvex
  constructor
  · -- The second factor does as well.
    exact helperForTheorem_38_5_actualCounterexampleSecond_properConvex
  · -- But their composition fails the target first conjunct.
    exact helperForTheorem_38_5_actualCounterexample_compose_not_IsConvexBifunction

-- Proof sketch: use product-space proper convexity of the graph functions of `F` and `G` to
-- build a convex triple-objective on `ℝ^m × ℝ^n × ℝ^p`; its partial infimum over the middle
-- variable `x` is exactly the graph function of `G ⊙ F`, giving convexity of the composition as a
-- bifunction on the product space. Under the relative-interior qualification
-- `ri (dom F_*) ∩ ri (dom G) ≠ ∅`, apply Fenchel duality to the same product-space model to obtain
-- `(G ⊙ F)^* = F^* G^*` and attainment of the supremum on the right-hand side.
/-
Theorem 38.5 in this file is formulated using the auxiliary bundled type
`FiberwiseProperConvexBifunction`, but the book's actual premise "proper convex bifunction" is
represented by the additional assumptions `ProperConvexBifunction F.toFun` and
`ProperConvexBifunction G.toFun`. The earlier fiberwise-only version was too weak; the
counterexample helpers below record that discarded route.
-/

end Section38
end Chap08

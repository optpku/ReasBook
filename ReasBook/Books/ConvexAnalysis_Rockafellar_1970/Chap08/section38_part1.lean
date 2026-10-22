/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Mathlib.LinearAlgebra.Dual.Defs
import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section02_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section14_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section26_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part3
import Books.ConvexAnalysis_Rockafellar_1970.bifunction_closure
import Books.ConvexAnalysis_Rockafellar_1970.bifunction_inverse

section Chap08
section Section38

/-- Definition 38.0.1: Let `A : ℝ^m → ℝ^n` be a linear transformation. The *convex indicator
bifunction* of `A` is the bifunction `F : ℝ^m → ℝ^n → EReal` defined by

`F u x = 0` if `x = A u`, and `F u x = +∞` otherwise (i.e. `F u = δ(· | {A u})`). -/
noncomputable def convexIndicatorBifunction {m n : Nat}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun u x => if x = A u then 0 else ⊤

/-- The concave indicator bifunction of a linear map on dual spaces: it is `0` on the graph
`u* = A* x*` and `-∞` off the graph. -/
noncomputable def concaveIndicatorBifunction
    {U X : Type*} [AddCommMonoid U] [Module ℝ U] [AddCommMonoid X] [Module ℝ X]
    (Astar : Module.Dual ℝ X →ₗ[ℝ] Module.Dual ℝ U) :
    Module.Dual ℝ X → Module.Dual ℝ U → EReal :=
  fun xStar uStar =>
    letI : DecidableEq (Module.Dual ℝ U) := Classical.decEq _
    if uStar = Astar xStar then 0 else ⊥

/-- The adjoint of a bifunction `F : U → X → EReal`, defined by
`F* x* u* = inf_{u,x} (⟨x, x*⟩ - ⟨u, u*⟩ + F u x)` (in `EReal`), where the bracket denotes the
canonical pairing between a module and its dual. -/
noncomputable def bifunctionAdjoint
    {U X : Type*} [AddCommMonoid U] [Module ℝ U] [AddCommMonoid X] [Module ℝ X]
    (F : U → X → EReal) :
    Module.Dual ℝ X → Module.Dual ℝ U → EReal :=
  fun xStar uStar =>
    ⨅ (u : U) (x : X),
      ((xStar x : ℝ) : EReal) + (-((uStar u : ℝ) : EReal)) + F u x

/-- The bracket `⟨F u, x*⟩` appearing in the text, interpreted (for a bifunction
`F : U → X → EReal`) as `inf_x (⟨x, x*⟩ + F u x)` in `EReal`. -/
noncomputable def bifunctionLeftPairing
    {U X : Type*} [AddCommMonoid U] [Module ℝ U] [AddCommMonoid X] [Module ℝ X]
    (F : U → X → EReal) (u : U) (xStar : Module.Dual ℝ X) : EReal :=
  ⨅ x : X, ((xStar x : ℝ) : EReal) + F u x

/-- The bracket `⟨u, G x*⟩` appearing in the text, interpreted (for a bifunction on duals
`G : X* → U* → EReal`) as `sup_{u*} (⟨u, u*⟩ + G x* u*)` in `EReal`. -/
noncomputable def bifunctionRightPairing
    {U X : Type*} [AddCommMonoid U] [Module ℝ U] [AddCommMonoid X] [Module ℝ X]
    (G : Module.Dual ℝ X → Module.Dual ℝ U → EReal) (xStar : Module.Dual ℝ X) (u : U) : EReal :=
  ⨆ uStar : Module.Dual ℝ U, ((uStar u : ℝ) : EReal) + G xStar uStar

-- Proof sketch: Unfold `bifunctionAdjoint` and `convexIndicatorBifunction`; the `iInf` reduces to
-- an infimum over `u` because the indicator forces `x = A u`, and the remaining infimum of the
-- linear form `x*(A u) - u*(u)` is `0` if `u* = A.dualMap x*` and `-∞` otherwise. The "Moreover"
-- chain is recorded using `bifunctionLeftPairing`/`bifunctionRightPairing`, and its middle equality
-- is `LinearMap.dualMap_apply`.
/-- Helper for Proposition 38.0.2: the left pairing against the convex indicator bifunction
collapses to evaluation at the graph point `A u`. -/
lemma helperForProposition_38_0_2_leftPairing_convexIndicator {m n : Nat}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (u : Fin m → ℝ) (xStar : Module.Dual ℝ (Fin n → ℝ)) :
    bifunctionLeftPairing (convexIndicatorBifunction A) u xStar = (xStar (A u) : EReal) := by
  apply le_antisymm
  · -- The graph point `x = A u` gives the matching upper bound.
    refine le_trans (iInf_le _ (A u)) ?_
    simp [convexIndicatorBifunction]
  · -- Off the graph the indicator is `+∞`, so every other term is above the graph value.
    rw [bifunctionLeftPairing]
    refine le_iInf ?_
    intro x
    by_cases hx : x = A u
    · rw [convexIndicatorBifunction, if_pos hx]
      simp [hx]
    · have htop : ((xStar x : ℝ) : EReal) + convexIndicatorBifunction A u x = ⊤ := by
        rw [convexIndicatorBifunction, if_neg hx]
        exact EReal.add_top_of_ne_bot (EReal.coe_ne_bot (xStar x))
      rw [htop]
      simp

/-- Helper for Proposition 38.0.2: on the dual graph `u* = A* x*`, the adjoint value is `0`. -/
lemma helperForProposition_38_0_2_adjoint_eq_zero_of_eq {m n : Nat}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (xStar : Module.Dual ℝ (Fin n → ℝ)) (uStar : Module.Dual ℝ (Fin m → ℝ))
    (hEq : uStar = A.dualMap xStar) :
    bifunctionAdjoint (convexIndicatorBifunction A) xStar uStar = 0 := by
  subst hEq
  apply le_antisymm
  · -- Taking `u = 0` and `x = A 0` realizes the value `0`.
    refine le_trans (iInf_le _ (0 : Fin m → ℝ)) ?_
    refine le_trans (iInf_le _ (A 0)) ?_
    simp [convexIndicatorBifunction, LinearMap.dualMap_apply]
  · -- Every summand is either exactly `0` on the graph or `+∞` off the graph.
    rw [bifunctionAdjoint]
    refine le_iInf ?_
    intro u
    refine le_iInf ?_
    intro x
    by_cases hx : x = A u
    · rw [convexIndicatorBifunction, if_pos hx]
      simp only [add_zero, hx, LinearMap.dualMap_apply]
      have hnonneg :
          (0 : EReal) ≤ (((xStar (A u) : ℝ) : EReal) - ((xStar (A u) : ℝ) : EReal)) := by
        rw [EReal.sub_self (EReal.coe_ne_top (xStar (A u))) (EReal.coe_ne_bot (xStar (A u)))]
      rw [sub_eq_add_neg] at hnonneg
      exact hnonneg
    · have hfinite :
          (((xStar x : ℝ) : EReal) + (-(((A.dualMap xStar) u : ℝ) : EReal))) ≠ ⊥ := by
        simp
      have htop :
          ((xStar x : ℝ) : EReal) + (-(((A.dualMap xStar) u : ℝ) : EReal)) +
            convexIndicatorBifunction A u x = ⊤ := by
        rw [convexIndicatorBifunction, if_neg hx]
        exact EReal.add_top_of_ne_bot hfinite
      rw [htop]
      simp

/-- Helper for Proposition 38.0.2: off the dual graph `u* ≠ A* x*`, the adjoint value is
`-∞`. -/
lemma helperForProposition_38_0_2_adjoint_eq_bot_of_ne {m n : Nat}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (xStar : Module.Dual ℝ (Fin n → ℝ)) (uStar : Module.Dual ℝ (Fin m → ℝ))
    (hNe : uStar ≠ A.dualMap xStar) :
    bifunctionAdjoint (convexIndicatorBifunction A) xStar uStar = ⊥ := by
  rw [bifunctionAdjoint, iInf₂_eq_bot]
  intro b hb
  -- Choose a direction where `u*` and `A* x*` disagree.
  have hdiff : ∃ v : Fin m → ℝ, uStar v ≠ (A.dualMap xStar) v := by
    by_contra hdiff
    push_neg at hdiff
    apply hNe
    exact LinearMap.ext fun v => hdiff v
  rcases hdiff with ⟨v, hv⟩
  rcases EReal.lt_iff_exists_rat_btwn.mp hb with ⟨q, -, hqb⟩
  let c : ℝ := (A.dualMap xStar) v - uStar v
  let t : ℝ := (((q : ℝ) - 1) / c)
  have hc : c ≠ 0 := by
    intro hc0
    apply hv
    dsimp [c] at hc0 ⊢
    linarith
  -- Scale the disagreement direction so that the graph term becomes exactly `q - 1`.
  have hgraph :
      ((xStar (A (t • v)) : ℝ) : EReal) + (-((uStar (t • v) : ℝ) : EReal)) +
        convexIndicatorBifunction A (t • v) (A (t • v)) = (((q : ℝ) - 1 : ℝ) : EReal) := by
    have hscalar : t * c = (q : ℝ) - 1 := by
      dsimp [t]
      field_simp [hc]
    have hreal : xStar (A (t • v)) - uStar (t • v) = t * c := by
      dsimp [c]
      rw [show xStar (A (t • v)) = (A.dualMap xStar) (t • v) by rw [LinearMap.dualMap_apply]]
      simp [sub_eq_add_neg, t]
      ring
    calc
      ((xStar (A (t • v)) : ℝ) : EReal) + (-((uStar (t • v) : ℝ) : EReal)) +
          convexIndicatorBifunction A (t • v) (A (t • v))
          = ((xStar (A (t • v)) - uStar (t • v) : ℝ) : EReal) := by
              rw [convexIndicatorBifunction]
              simp [sub_eq_add_neg]
      _ = ((t * c : ℝ) : EReal) := by rw [hreal]
      _ = (((q : ℝ) - 1 : ℝ) : EReal) := by rw [hscalar]
  refine ⟨t • v, A (t • v), ?_⟩
  have hqminus : ((((q : ℝ) - 1 : ℝ) : EReal) < ((q : ℝ) : EReal)) := by
    exact_mod_cast (show (q : ℝ) - 1 < (q : ℝ) by linarith)
  have hgraph_lt_b : ((((q : ℝ) - 1 : ℝ) : EReal) < b) := lt_trans hqminus hqb
  calc
    ((xStar (A (t • v)) : ℝ) : EReal) + (-((uStar (t • v) : ℝ) : EReal)) +
        convexIndicatorBifunction A (t • v) (A (t • v)) = (((q : ℝ) - 1 : ℝ) : EReal) := hgraph
    _ < b := hgraph_lt_b

/-- Helper for Proposition 38.0.2: the right pairing against the concave indicator bifunction
collapses to evaluation by `A* x*`. -/
lemma helperForProposition_38_0_2_rightPairing_concaveIndicator {m n : Nat}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (u : Fin m → ℝ) (xStar : Module.Dual ℝ (Fin n → ℝ)) :
    bifunctionRightPairing (concaveIndicatorBifunction A.dualMap) xStar u =
      ((A.dualMap xStar) u : EReal) := by
  apply le_antisymm
  · -- Every term in the supremum is either the target value or `-∞`.
    rw [bifunctionRightPairing]
    refine iSup_le ?_
    intro uStar
    by_cases hEq : uStar = A.dualMap xStar
    · rw [concaveIndicatorBifunction]
      simp [hEq]
    · rw [concaveIndicatorBifunction]
      simp [hEq, EReal.add_bot]
  · -- The on-graph dual point realizes the required lower bound.
    rw [bifunctionRightPairing]
    refine le_iSup_of_le (A.dualMap xStar) ?_
    rw [concaveIndicatorBifunction]
    simp

/-- Helper for Proposition 38.0.2: pairing `x*` with `A u` agrees with pairing `A* x*` with
`u`. -/
lemma helperForProposition_38_0_2_dualPairing_identity {m n : Nat}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (u : Fin m → ℝ) (xStar : Module.Dual ℝ (Fin n → ℝ)) :
    (xStar (A u) : EReal) = ((A.dualMap xStar) u : EReal) := by
  -- This is exactly the defining compatibility of `LinearMap.dualMap`.
  norm_num [LinearMap.dualMap_apply]

/-- Proposition 38.0.2: Let `F` be the convex indicator bifunction of a linear transformation
`A : ℝ^m → ℝ^n`. Then the adjoint `F*` of `F` is the concave indicator bifunction of the adjoint
linear transformation `A* : (ℝ^n)* → (ℝ^m)*` (here interpreted as `A.dualMap`), namely
`(F* x*)(u*) = 0` if `u* = A* x*` and `-∞` otherwise. Moreover, the bracket identities in the text
are expressed via `bifunctionLeftPairing`/`bifunctionRightPairing`, yielding the chain
`⟨F u, x*⟩ = ⟨A u, x*⟩ = ⟨u, A* x*⟩ = ⟨u, F* x*⟩`. -/
theorem bifunctionAdjoint_convexIndicatorBifunction {m n : Nat}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    bifunctionAdjoint (convexIndicatorBifunction A) = concaveIndicatorBifunction A.dualMap ∧
      (∀ (u : Fin m → ℝ) (xStar : Module.Dual ℝ (Fin n → ℝ)),
        bifunctionLeftPairing (convexIndicatorBifunction A) u xStar = (xStar (A u) : EReal) ∧
          (xStar (A u) : EReal) = ((A.dualMap xStar) u : EReal) ∧
          ((A.dualMap xStar) u : EReal) =
            bifunctionRightPairing (bifunctionAdjoint (convexIndicatorBifunction A)) xStar u) :=
  by
    -- First identify the adjoint pointwise as the concave indicator of the dual map.
    have hadj :
        bifunctionAdjoint (convexIndicatorBifunction A) = concaveIndicatorBifunction A.dualMap := by
      funext xStar uStar
      by_cases hEq : uStar = A.dualMap xStar
      · rw [concaveIndicatorBifunction]
        simp [hEq, helperForProposition_38_0_2_adjoint_eq_zero_of_eq]
      · rw [concaveIndicatorBifunction]
        simp [hEq, helperForProposition_38_0_2_adjoint_eq_bot_of_ne]
    constructor
    · exact hadj
    · intro u xStar
      constructor
      · exact helperForProposition_38_0_2_leftPairing_convexIndicator A u xStar
      constructor
      · -- This is the middle pairing identity `⟨A u, x*⟩ = ⟨u, A* x*⟩`.
        exact helperForProposition_38_0_2_dualPairing_identity A u xStar
      · -- Rewrite the right pairing using the identified adjoint.
        rw [hadj]
        exact (helperForProposition_38_0_2_rightPairing_concaveIndicator A u xStar).symm

/-- A module-generic version of `convexIndicatorBifunction`: the convex indicator bifunction of a
linear map `A : U →ₗ[ℝ] X` is `0` on the graph `x = A u` and `+∞` off the graph. -/
noncomputable def convexIndicatorBifunctionLinear
    {U X : Type*} [AddCommMonoid U] [Module ℝ U] [AddCommMonoid X] [Module ℝ X]
    (A : U →ₗ[ℝ] X) : U → X → EReal :=
  fun u x =>
    letI : DecidableEq X := Classical.decEq _
    if x = A u then 0 else ⊤

/-- The concave indicator bifunction of a linear map `A : X →ₗ[ℝ] U` on primal spaces: it is `0`
on the graph `u = A x` and `-∞` off the graph. -/
noncomputable def concaveIndicatorBifunctionLinear
    {U X : Type*} [AddCommMonoid U] [Module ℝ U] [AddCommMonoid X] [Module ℝ X]
    (A : X →ₗ[ℝ] U) : X → U → EReal :=
  fun x u =>
    letI : DecidableEq U := Classical.decEq _
    if u = A x then 0 else ⊥

/-- Helper for Proposition 38.0.3: the concave indicator bifunction of a linear graph is a
concave bifunction because its negated graph function is the convex indicator of the graph set. -/
lemma helperForProposition_38_0_3_concaveIndicatorLinear_concave {m n : Nat}
    (B : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    ConcaveBifunction (concaveIndicatorBifunctionLinear B) := by
  let graphSet : Set (Fin (n + m) → ℝ) :=
    {z | (fun j => z (Fin.natAdd n j)) = B (fun i => z (Fin.castAdd m i))}
  have hGraphSetConvex : Convex ℝ graphSet := by
    -- The relation `u = B x` is preserved by convex combinations because `B` is linear.
    intro z₁ hz₁ z₂ hz₂ a b ha hb hab
    change
      (fun j => (a • z₁ + b • z₂) (Fin.natAdd n j)) =
        B (fun i => (a • z₁ + b • z₂) (Fin.castAdd m i))
    have hz₁j :
        ∀ j, z₁ (Fin.natAdd n j) = (B (fun i => z₁ (Fin.castAdd m i))) j :=
      congrFun hz₁
    have hz₂j :
        ∀ j, z₂ (Fin.natAdd n j) = (B (fun i => z₂ (Fin.castAdd m i))) j :=
      congrFun hz₂
    ext j
    calc
      (a • z₁ + b • z₂) (Fin.natAdd n j)
          = a * z₁ (Fin.natAdd n j) + b * z₂ (Fin.natAdd n j) := by simp
      _ = a * (B (fun i => z₁ (Fin.castAdd m i))) j +
            b * (B (fun i => z₂ (Fin.castAdd m i))) j := by rw [hz₁j j, hz₂j j]
      _ = (B (a • (fun i => z₁ (Fin.castAdd m i)) +
            b • (fun i => z₂ (Fin.castAdd m i)))) j := by
            simp [map_add, map_smul]
      _ = (B (fun i => (a • z₁ + b • z₂) (Fin.castAdd m i))) j := by
            rfl
  have hIndicatorConvex :
      ConvexFunction (indicatorFunction graphSet) :=
    convexFunction_indicator_of_convex (C := graphSet) hGraphSetConvex
  have hGraphEq :
      (fun z : Fin (n + m) → ℝ =>
        -bifunctionGraphFunction (concaveIndicatorBifunctionLinear B) z) =
      indicatorFunction graphSet := by
    -- The negated graph function is exactly the `0/+∞` indicator of the graph.
    funext z
    by_cases hEq : (fun j => z (Fin.natAdd n j)) = B (fun i => z (Fin.castAdd m i))
    · have hz : z ∈ graphSet := by simpa [graphSet] using hEq
      simp [bifunctionGraphFunction, concaveIndicatorBifunctionLinear, indicatorFunction, graphSet,
        hEq, hz]
    · have hz : z ∉ graphSet := by simpa [graphSet] using hEq
      simp [bifunctionGraphFunction, concaveIndicatorBifunctionLinear, indicatorFunction, graphSet,
        hEq, hz]
  simpa [ConcaveBifunction, hGraphEq] using hIndicatorConvex

/-- The textbook object `F_*^*` from Proposition 38.0.3, formed by taking the Chapter 6 concave
adjoint of the concave indicator bifunction of `A⁻¹`. This is the correct object corresponding to
the TeX statement "`F_*^*` is the convex indicator bifunction of `(A^*)^{-1}`"; it is not the
same as the local `iInf`-based `bifunctionAdjoint` used earlier in this file for convex
bifunctions. Since the chapter works in Euclidean coordinate spaces `ℝ^m` and `ℝ^n`, we model
`(A^*)^{-1} = (A^{-1})^*` via the coordinate adjoint `coordinateAdjointLinearMap` rather than by
the raw `LinearMap.dualMap` on algebraic dual spaces. -/
noncomputable def bifunctionInverseTextbookAdjoint {m n : Nat}
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  adjointOfConcaveBifunction (m := n) (n := m)
    ⟨concaveIndicatorBifunctionLinear A.symm.toLinearMap,
      helperForProposition_38_0_3_concaveIndicatorLinear_concave A.symm.toLinearMap⟩

-- Proof sketch: For `F = convexIndicatorBifunction A`, the inverse `F_*` is `-F` with swapped
-- arguments, hence is a `0/-∞` indicator supported on the same graph `x = A u`, which equals the
-- graph `u = A⁻¹ x` when `A` is nonsingular. Taking adjoints and using Proposition 38.0.2 (applied
-- to the map `A⁻¹`) yields that `F_*^*` is the `0/+∞` convex indicator bifunction of
-- `(A⁻¹)^* = (A^*)⁻¹`.
/-- Helper for Proposition 38.0.3: the graph condition `x = A u` is equivalent to
`u = A⁻¹ x`. -/
lemma helperForProposition_38_0_3_graph_iff_symm_graph {m n : Nat}
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (u : Fin m → ℝ) (x : Fin n → ℝ) :
    x = A u ↔ u = A.symm x := by
  constructor
  · -- Apply `A⁻¹` to move from the graph of `A` to the graph of `A⁻¹`.
    intro hx
    calc
      u = A.symm (A u) := by simp
      _ = A.symm x := by rw [hx]
  · -- Apply `A` to move back from the graph of `A⁻¹` to the graph of `A`.
    intro hu
    calc
      x = A (A.symm x) := by simp
      _ = A u := by rw [hu]

/-- Helper for Proposition 38.0.3: the inverse of the convex indicator bifunction of `A` is the
concave indicator bifunction of `A⁻¹`. -/
lemma helperForProposition_38_0_3_inverse_eq_concaveIndicator {m n : Nat}
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) :
    bifunctionInverse (convexIndicatorBifunction A.toLinearMap) =
      concaveIndicatorBifunctionLinear A.symm.toLinearMap := by
  funext x u
  -- Unfold the inverse and compare the indicator support conditions on the two graphs.
  by_cases hx : x = A u
  · -- On the graph, both bifunctions evaluate to `0`.
    have hu : u = A.symm x :=
      (helperForProposition_38_0_3_graph_iff_symm_graph A u x).mp hx
    have hconv :
        convexIndicatorBifunction A.toLinearMap u x = 0 := by
      simp [convexIndicatorBifunction, hx]
    have hconc :
        concaveIndicatorBifunctionLinear A.symm.toLinearMap x u = 0 := by
      simp [concaveIndicatorBifunctionLinear, hu]
    calc
      bifunctionInverse (convexIndicatorBifunction A.toLinearMap) x u
          = -(convexIndicatorBifunction A.toLinearMap u x) := by
              rfl
      _ = -(0 : EReal) := by rw [hconv]
      _ = 0 := by simp
      _ = concaveIndicatorBifunctionLinear A.symm.toLinearMap x u := by
            rw [hconc]
  · -- Off the graph, negating `+∞` produces `-∞`, matching the concave indicator.
    have hu : u ≠ A.symm x := by
      simpa [helperForProposition_38_0_3_graph_iff_symm_graph A u x] using hx
    have hconv :
        convexIndicatorBifunction A.toLinearMap u x = ⊤ := by
      simp [convexIndicatorBifunction, hx]
    have hconc :
        concaveIndicatorBifunctionLinear A.symm.toLinearMap x u = ⊥ := by
      simp [concaveIndicatorBifunctionLinear, hu]
    calc
      bifunctionInverse (convexIndicatorBifunction A.toLinearMap) x u
          = -(convexIndicatorBifunction A.toLinearMap u x) := by
              rfl
      _ = -⊤ := by rw [hconv]
      _ = ⊥ := by simp
      _ = concaveIndicatorBifunctionLinear A.symm.toLinearMap x u := by
            rw [hconc]

/-- Helper for Proposition 38.0.3: on graph points `(x, B x)`, the textbook concave-adjoint
integrand reduces to the linear form with coefficient `xStar - B* uStar`. -/
lemma helperForProposition_38_0_3_textbookAdjoint_graphTerm {m n : Nat}
    (B : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (uStar : Fin m → ℝ) (xStar x : Fin n → ℝ) :
    concaveIndicatorBifunctionLinear B x (B x) - (((dotProduct (B x) uStar : ℝ) : EReal)) +
        (((dotProduct x xStar : ℝ) : EReal)) =
      (((dotProduct x (xStar - coordinateAdjointLinearMap B uStar) : ℝ) : EReal)) := by
  -- The graph indicator contributes `0`, so only the adjoint-compatible dot-product difference
  -- remains.
  calc
    concaveIndicatorBifunctionLinear B x (B x) - (((dotProduct (B x) uStar : ℝ) : EReal)) +
        (((dotProduct x xStar : ℝ) : EReal))
        = (((dotProduct x xStar : ℝ) - dotProduct (B x) uStar : ℝ) : EReal) := by
            simp [concaveIndicatorBifunctionLinear, sub_eq_add_neg, add_comm]
    _ = (((dotProduct x xStar : ℝ) -
        dotProduct x (coordinateAdjointLinearMap B uStar) : ℝ) : EReal) := by
          rw [helperForCorollary_26_3_3_dotProduct_coordinateAdjoint B x uStar]
    _ = (((dotProduct x (xStar - coordinateAdjointLinearMap B uStar) : ℝ) : EReal)) := by
          rw [dotProduct_sub]

/-- Helper for Proposition 38.0.3: on the dual graph `xStar = B* uStar`, the textbook concave
adjoint of the concave graph indicator takes the value `0`. -/
lemma helperForProposition_38_0_3_textbookAdjoint_eq_zero_on_graph {m n : Nat}
    (B : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (uStar : Fin m → ℝ) (xStar : Fin n → ℝ)
    (hx : xStar = coordinateAdjointLinearMap B uStar) :
    adjointOfConcaveBifunction (m := n) (n := m)
        ⟨concaveIndicatorBifunctionLinear B,
          helperForProposition_38_0_3_concaveIndicatorLinear_concave B⟩ uStar xStar = 0 := by
  subst hx
  apply le_antisymm
  · -- Every on-graph term becomes `0`, while off-graph terms are already `-∞`.
    rw [adjointOfConcaveBifunction]
    refine sSup_le ?_
    intro a ha
    rcases ha with ⟨⟨x, u⟩, rfl⟩
    change
      concaveIndicatorBifunctionLinear B x u - (((dotProduct u uStar : ℝ) : EReal)) +
        (((dotProduct x (coordinateAdjointLinearMap B uStar) : ℝ) : EReal)) ≤ 0
    by_cases hu : u = B x
    · rw [hu]
      have hterm :
          concaveIndicatorBifunctionLinear B x (B x) - (((dotProduct (B x) uStar : ℝ) : EReal)) +
              (((dotProduct x (coordinateAdjointLinearMap B uStar) : ℝ) : EReal)) = 0 := by
        calc
          concaveIndicatorBifunctionLinear B x (B x) - (((dotProduct (B x) uStar : ℝ) : EReal)) +
              (((dotProduct x (coordinateAdjointLinearMap B uStar) : ℝ) : EReal))
              = (((dotProduct x
                    ((coordinateAdjointLinearMap B uStar) - coordinateAdjointLinearMap B uStar) :
                      ℝ) : EReal)) := by
                  simpa using
                    helperForProposition_38_0_3_textbookAdjoint_graphTerm
                      B uStar (coordinateAdjointLinearMap B uStar) x
          _ = 0 := by simp
      rw [hterm]
    · simp [concaveIndicatorBifunctionLinear, hu]
  · -- The graph point `(0, B 0)` realizes the value `0`.
    rw [adjointOfConcaveBifunction]
    refine le_sSup ?_
    refine ⟨(0, B 0), ?_⟩
    simp [concaveIndicatorBifunctionLinear]

/-- Helper for Proposition 38.0.3: off the dual graph `xStar ≠ B* uStar`, the textbook concave
adjoint of the concave graph indicator is unbounded above and hence equals `+∞`. -/
lemma helperForProposition_38_0_3_textbookAdjoint_eq_top_off_graph {m n : Nat}
    (B : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (uStar : Fin m → ℝ) (xStar : Fin n → ℝ)
    (hx : xStar ≠ coordinateAdjointLinearMap B uStar) :
    adjointOfConcaveBifunction (m := n) (n := m)
        ⟨concaveIndicatorBifunctionLinear B,
          helperForProposition_38_0_3_concaveIndicatorLinear_concave B⟩ uStar xStar = ⊤ := by
  let c : Fin n → ℝ := xStar - coordinateAdjointLinearMap B uStar
  have hc : c ≠ 0 := by
    -- If the coefficient vanished, the dual point would lie on the graph after all.
    intro hc0
    apply hx
    exact sub_eq_zero.mp hc0
  apply (EReal.eq_top_iff_forall_lt _).2
  intro q
  rcases exists_dotProduct_eq_of_ne_zero n c (q + 1) hc with ⟨x, hxDot⟩
  have hq :
      (((q : ℝ) : EReal)) < (((q + 1 : ℝ) : EReal)) := by
    exact_mod_cast (show q < q + 1 by linarith)
  refine lt_of_lt_of_le hq (le_sSup ?_)
  refine ⟨(x, B x), ?_⟩
  change
    concaveIndicatorBifunctionLinear B x (B x) - (((dotProduct (B x) uStar : ℝ) : EReal)) +
      (((dotProduct x xStar : ℝ) : EReal)) = (((q + 1 : ℝ) : EReal))
  calc
    concaveIndicatorBifunctionLinear B x (B x) - (((dotProduct (B x) uStar : ℝ) : EReal)) +
        (((dotProduct x xStar : ℝ) : EReal))
        = (((dotProduct x c : ℝ) : EReal)) := by
            simpa [c] using
              helperForProposition_38_0_3_textbookAdjoint_graphTerm B uStar xStar x
    _ = (((q + 1 : ℝ) : EReal)) := by rw [hxDot]

/-- Helper for Proposition 38.0.3: the textbook concave adjoint of the concave graph indicator
of `B` is the convex indicator of the Euclidean adjoint graph `xStar = B* uStar`. -/
lemma helperForProposition_38_0_3_textbookAdjoint_eq_convexIndicator {m n : Nat}
    (B : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    adjointOfConcaveBifunction (m := n) (n := m)
        ⟨concaveIndicatorBifunctionLinear B,
          helperForProposition_38_0_3_concaveIndicatorLinear_concave B⟩ =
      convexIndicatorBifunctionLinear (coordinateAdjointLinearMap B) := by
  funext uStar xStar
  by_cases hx : xStar = coordinateAdjointLinearMap B uStar
  · -- On the dual graph both sides are `0`.
    simpa [convexIndicatorBifunctionLinear, hx] using
      helperForProposition_38_0_3_textbookAdjoint_eq_zero_on_graph B uStar xStar hx
  · -- Off the dual graph both sides are `+∞`.
    simpa [convexIndicatorBifunctionLinear, hx] using
      helperForProposition_38_0_3_textbookAdjoint_eq_top_off_graph B uStar xStar hx

/-- Helper for Proposition 38.0.3: one off-graph point already forces the adjoint of a concave
indicator bifunction to be `⊥` under the current `iInf`-based adjoint definition. -/
lemma helperForProposition_38_0_3_adjoint_eq_bot_of_offGraphPoint
    {U X : Type*} [AddCommMonoid U] [Module ℝ U] [AddCommMonoid X] [Module ℝ X]
    (A : X →ₗ[ℝ] U) (uStar : Module.Dual ℝ U) (xStar : Module.Dual ℝ X)
    {x : X} {u : U} (hoff : u ≠ A x) :
    bifunctionAdjoint (concaveIndicatorBifunctionLinear A) uStar xStar = ⊥ := by
  apply le_antisymm
  · -- Evaluate the defining infimum at the chosen off-graph point.
    refine le_trans (iInf_le _ x) ?_
    refine le_trans (iInf_le _ u) ?_
    rw [concaveIndicatorBifunctionLinear]
    simp [hoff]
  · -- `⊥` is the minimal `EReal` value, so the reverse inequality is automatic.
    exact bot_le

/-- Helper for Proposition 38.0.3: the convex indicator bifunction of a linear map is `0` at each
point of its graph. -/
lemma helperForProposition_38_0_3_convexIndicator_eq_zero_on_graph
    {U X : Type*} [AddCommMonoid U] [Module ℝ U] [AddCommMonoid X] [Module ℝ X]
    (A : U →ₗ[ℝ] X) (u : U) :
    convexIndicatorBifunctionLinear A u (A u) = 0 := by
  -- The graph point satisfies the defining indicator condition by construction.
  simp [convexIndicatorBifunctionLinear]

/-- Helper for Proposition 38.0.3: once the primal graph of `A` misses a point, the current
`iInf`-adjoint of its concave indicator cannot equal the convex indicator of `A*`. -/
lemma helperForProposition_38_0_3_adjoint_ne_convexIndicator_of_offGraphPoint
    {U X : Type*} [AddCommMonoid U] [Module ℝ U] [AddCommMonoid X] [Module ℝ X]
    (A : X →ₗ[ℝ] U) (hoff : ∃ x : X, ∃ u : U, u ≠ A x) :
    bifunctionAdjoint (concaveIndicatorBifunctionLinear A) ≠
      convexIndicatorBifunctionLinear A.dualMap := by
  intro hEq
  rcases hoff with ⟨x, u, hu⟩
  have hbot :
      bifunctionAdjoint (concaveIndicatorBifunctionLinear A)
          (0 : Module.Dual ℝ U) (0 : Module.Dual ℝ X) = ⊥ := by
    -- The chosen off-graph primal pair already collapses the infimum at the zero dual point.
    exact helperForProposition_38_0_3_adjoint_eq_bot_of_offGraphPoint
      A (0 : Module.Dual ℝ U) (0 : Module.Dual ℝ X) hu
  have hzero :
      convexIndicatorBifunctionLinear A.dualMap
          (0 : Module.Dual ℝ U) (0 : Module.Dual ℝ X) = 0 := by
    -- The zero dual pair lies on the graph of `A*` because every linear map sends `0` to `0`.
    simpa using
      (helperForProposition_38_0_3_convexIndicator_eq_zero_on_graph
        A.dualMap (0 : Module.Dual ℝ U))
  have hEqAtZero :
      bifunctionAdjoint (concaveIndicatorBifunctionLinear A)
          (0 : Module.Dual ℝ U) (0 : Module.Dual ℝ X) =
        convexIndicatorBifunctionLinear A.dualMap
          (0 : Module.Dual ℝ U) (0 : Module.Dual ℝ X) := by
    -- Any claimed equality of bifunctions must agree at the zero dual pair.
    exact congrFun (congrFun hEq (0 : Module.Dual ℝ U)) (0 : Module.Dual ℝ X)
  rw [hbot, hzero] at hEqAtZero
  exact (by simp : (⊥ : EReal) ≠ 0) hEqAtZero

/-- Helper for Proposition 38.0.3: if the graph of `A⁻¹` misses one primal point, then the
rewritten second conjunct of the target proposition is already false. -/
lemma helperForProposition_38_0_3_secondConjunctFalse_of_inverseOffGraphPoint
    {m n : Nat} (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hoff : ∃ x : Fin n → ℝ, ∃ u : Fin m → ℝ, u ≠ A.symm x) :
    bifunctionAdjoint (bifunctionInverse (convexIndicatorBifunction A.toLinearMap)) ≠
      convexIndicatorBifunctionLinear (A.symm.toLinearMap.dualMap) := by
  -- Rewrite the inverse term so the generic off-graph obstruction applies to `A⁻¹`.
  rw [helperForProposition_38_0_3_inverse_eq_concaveIndicator A]
  -- The target second conjunct now matches the generic concave-indicator obstruction.
  exact helperForProposition_38_0_3_adjoint_ne_convexIndicator_of_offGraphPoint
    A.symm.toLinearMap hoff

/-- Helper for Proposition 38.0.3: any proof of the rewritten second conjunct, together with an
off-graph witness for `A⁻¹`, forces the impossible equality `⊥ = 0` at the zero dual pair. -/
lemma helperForProposition_38_0_3_secondConjunct_forces_bot_eq_zero_of_inverseOffGraphPoint
    {m n : Nat} (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hoff : ∃ x : Fin n → ℝ, ∃ u : Fin m → ℝ, u ≠ A.symm x)
    (hSecond :
      bifunctionAdjoint (bifunctionInverse (convexIndicatorBifunction A.toLinearMap)) =
        convexIndicatorBifunctionLinear (A.symm.toLinearMap.dualMap)) :
    (⊥ : EReal) = 0 := by
  -- Rewrite the inverse term so the off-graph witness applies directly to the zero dual pair.
  rw [helperForProposition_38_0_3_inverse_eq_concaveIndicator A] at hSecond
  rcases hoff with ⟨x, u, hu⟩
  have hEqAtZero :
      bifunctionAdjoint (concaveIndicatorBifunctionLinear A.symm.toLinearMap)
          (0 : Module.Dual ℝ (Fin m → ℝ)) (0 : Module.Dual ℝ (Fin n → ℝ)) =
        convexIndicatorBifunctionLinear (A.symm.toLinearMap.dualMap)
          (0 : Module.Dual ℝ (Fin m → ℝ)) (0 : Module.Dual ℝ (Fin n → ℝ)) := by
    -- Any equality of bifunctions must agree when evaluated at the zero dual pair.
    exact congrFun (congrFun hSecond (0 : Module.Dual ℝ (Fin m → ℝ)))
      (0 : Module.Dual ℝ (Fin n → ℝ))
  have hbot :
      bifunctionAdjoint (concaveIndicatorBifunctionLinear A.symm.toLinearMap)
          (0 : Module.Dual ℝ (Fin m → ℝ)) (0 : Module.Dual ℝ (Fin n → ℝ)) = ⊥ := by
    -- The chosen off-graph primal pair already collapses the defining infimum at the zero dual
    -- pair.
    exact helperForProposition_38_0_3_adjoint_eq_bot_of_offGraphPoint
      A.symm.toLinearMap (0 : Module.Dual ℝ (Fin m → ℝ))
      (0 : Module.Dual ℝ (Fin n → ℝ)) hu
  have hzero :
      convexIndicatorBifunctionLinear (A.symm.toLinearMap.dualMap)
          (0 : Module.Dual ℝ (Fin m → ℝ)) (0 : Module.Dual ℝ (Fin n → ℝ)) = 0 := by
    -- The zero dual pair lies on the graph of `(A⁻¹)^*`.
    simpa using
      (helperForProposition_38_0_3_convexIndicator_eq_zero_on_graph
        (A.symm.toLinearMap.dualMap)
        (0 : Module.Dual ℝ (Fin m → ℝ)))
  -- The zero-pair evaluation reduces the claimed equality to the contradictory scalar equation.
  rw [hbot, hzero] at hEqAtZero
  exact hEqAtZero

/-- Helper for Proposition 38.0.3: under the current adjoint formalization, any proof of the
second conjunct would force every primal pair `(x, u)` to lie on the inverse graph
`u = A⁻¹ x`. -/
lemma helperForProposition_38_0_3_secondConjunct_forces_inverseGraph_total
    {m n : Nat} (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hSecond :
      bifunctionAdjoint (bifunctionInverse (convexIndicatorBifunction A.toLinearMap)) =
        convexIndicatorBifunctionLinear (A.symm.toLinearMap.dualMap)) :
    ∀ x : Fin n → ℝ, ∀ u : Fin m → ℝ, u = A.symm x := by
  intro x u
  -- Any off-graph primal pair would reduce the second conjunct to the impossible equality
  -- `⊥ = 0`.
  by_contra hu
  have hBotEqZero : (⊥ : EReal) = 0 :=
    helperForProposition_38_0_3_secondConjunct_forces_bot_eq_zero_of_inverseOffGraphPoint
      A ⟨x, u, hu⟩ hSecond
  -- Since `⊥` and `0` are distinct in `EReal`, the off-graph case is impossible.
  exact (by simp : (⊥ : EReal) ≠ 0) hBotEqZero

/-- Helper for Proposition 38.0.3: under the current adjoint formalization, any proof of the
second conjunct would collapse the primal domain to a subsingleton, because every vector would
have to equal `A⁻¹ 0`. -/
lemma helperForProposition_38_0_3_secondConjunct_forces_domainSubsingleton
    {m n : Nat} (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hSecond :
      bifunctionAdjoint (bifunctionInverse (convexIndicatorBifunction A.toLinearMap)) =
        convexIndicatorBifunctionLinear (A.symm.toLinearMap.dualMap)) :
    Subsingleton (Fin m → ℝ) := by
  refine ⟨?_⟩
  intro u v
  -- Applying the previous lemma at the codomain zero vector shows that every primal vector equals
  -- the same value `A⁻¹ 0`.
  have hu :
      u = A.symm (0 : Fin n → ℝ) :=
    helperForProposition_38_0_3_secondConjunct_forces_inverseGraph_total A hSecond
      (0 : Fin n → ℝ) u
  have hv :
      v = A.symm (0 : Fin n → ℝ) :=
    helperForProposition_38_0_3_secondConjunct_forces_inverseGraph_total A hSecond
      (0 : Fin n → ℝ) v
  calc
    u = A.symm (0 : Fin n → ℝ) := hu
    _ = v := hv.symm

/-- Helper for Proposition 38.0.3: in every positive-dimensional domain, the inverse graph of a
linear equivalence misses the point `(0, 1)`. -/
lemma helperForProposition_38_0_3_inverseOffGraphPoint_of_positiveDimension
    {m n : Nat} (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (hm : 0 < m) :
    ∃ x : Fin n → ℝ, ∃ u : Fin m → ℝ, u ≠ A.symm x := by
  let i : Fin m := ⟨0, hm⟩
  let u : Fin m → ℝ := fun _ => (1 : ℝ)
  refine ⟨(0 : Fin n → ℝ), u, ?_⟩
  -- Evaluating at the distinguished coordinate shows that the constant-one vector is not zero.
  intro hEq
  have hOneEqZero : (1 : ℝ) = 0 := by
    simpa [u] using congrFun hEq i
  norm_num at hOneEqZero

/-- Helper for Proposition 38.0.3: in every positive-dimensional case, the rewritten second
conjunct already contradicts the current `iInf`-adjoint formalization. -/
lemma helperForProposition_38_0_3_secondConjunctFalse_of_positiveDimension
    {m n : Nat} (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (hm : 0 < m) :
    bifunctionAdjoint (bifunctionInverse (convexIndicatorBifunction A.toLinearMap)) ≠
      convexIndicatorBifunctionLinear (A.symm.toLinearMap.dualMap) := by
  -- Positive dimension produces an explicit off-graph witness for the inverse graph of `A`.
  apply helperForProposition_38_0_3_secondConjunctFalse_of_inverseOffGraphPoint A
  exact helperForProposition_38_0_3_inverseOffGraphPoint_of_positiveDimension A hm

/-- Helper for Proposition 38.0.3: once the second conjunct is rewritten using the explicit
inverse formula, any proof of that rewritten equality still collapses the primal domain to a
subsingleton. -/
lemma helperForProposition_38_0_3_rewrittenSecondConjunct_forces_domainSubsingleton
    {m n : Nat} (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hSecond :
      bifunctionAdjoint (concaveIndicatorBifunctionLinear A.symm.toLinearMap) =
        convexIndicatorBifunctionLinear (A.symm.toLinearMap.dualMap)) :
    Subsingleton (Fin m → ℝ) := by
  have hOriginal :
      bifunctionAdjoint (bifunctionInverse (convexIndicatorBifunction A.toLinearMap)) =
        convexIndicatorBifunctionLinear (A.symm.toLinearMap.dualMap) := by
    -- Convert the rewritten equality back to the original second conjunct.
    simpa [helperForProposition_38_0_3_inverse_eq_concaveIndicator A] using hSecond
  -- The earlier structural-collapse lemma now applies directly to the unreduced statement.
  exact helperForProposition_38_0_3_secondConjunct_forces_domainSubsingleton A hOriginal

/-- Helper for Proposition 38.0.3: in positive dimension, the rewritten second conjunct would
force the scalar contradiction `0 = 1` by collapsing the zero vector and the constant-one vector
in the primal domain. -/
lemma helperForProposition_38_0_3_rewrittenSecondConjunct_forces_zero_eq_one_of_positiveDimension
    {m n : Nat} (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (hm : 0 < m)
    (hSecond :
      bifunctionAdjoint (concaveIndicatorBifunctionLinear A.symm.toLinearMap) =
        convexIndicatorBifunctionLinear (A.symm.toLinearMap.dualMap)) :
    (0 : ℝ) = 1 := by
  have hSub :
      Subsingleton (Fin m → ℝ) :=
    helperForProposition_38_0_3_rewrittenSecondConjunct_forces_domainSubsingleton A hSecond
  let z : Fin m → ℝ := 0
  let o : Fin m → ℝ := fun _ => (1 : ℝ)
  have hzEq : z = o := hSub.elim z o
  let i : Fin m := ⟨0, hm⟩
  -- Evaluating the forced equality at a distinguished coordinate exposes the impossible scalar
  -- identity.
  simpa [z, o] using congrFun hzEq i

/-- Helper for Proposition 38.0.3: in positive dimension, even the rewritten second conjunct is
impossible, because it would force the zero vector to equal the constant-one vector. -/
lemma helperForProposition_38_0_3_rewrittenSecondConjunctFalse_of_positiveDimension
    {m n : Nat} (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (hm : 0 < m) :
    bifunctionAdjoint (concaveIndicatorBifunctionLinear A.symm.toLinearMap) ≠
      convexIndicatorBifunctionLinear (A.symm.toLinearMap.dualMap) := by
  intro hSecond
  have hZeroEqOne : (0 : ℝ) = 1 := by
    -- The new helper isolates the scalar contradiction hidden in the rewritten equality.
    exact
      helperForProposition_38_0_3_rewrittenSecondConjunct_forces_zero_eq_one_of_positiveDimension
        A hm hSecond
  have hZeroNeOne : (0 : ℝ) ≠ 1 := by
    norm_num
  exact hZeroNeOne hZeroEqOne

/-- Helper for Proposition 38.0.3: any off-graph witness for `A⁻¹` already falsifies the full
conjunction claimed in the proposition, because the second conjunct fails under the current
`iInf`-adjoint formalization. -/
lemma helperForProposition_38_0_3_targetFalse_of_inverseOffGraphPoint
    {m n : Nat} (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hoff : ∃ x : Fin n → ℝ, ∃ u : Fin m → ℝ, u ≠ A.symm x) :
    ¬ (bifunctionInverse (convexIndicatorBifunction A.toLinearMap) =
          concaveIndicatorBifunctionLinear A.symm.toLinearMap ∧
        bifunctionAdjoint (bifunctionInverse (convexIndicatorBifunction A.toLinearMap)) =
          convexIndicatorBifunctionLinear (A.symm.toLinearMap.dualMap)) := by
  intro hTarget
  -- The full conjunction cannot hold once the rewritten second conjunct is known to fail.
  exact (helperForProposition_38_0_3_secondConjunctFalse_of_inverseOffGraphPoint A hoff) hTarget.2

/-- Helper for Proposition 38.0.3: in every positive-dimensional case, the full conjunction
claimed in the proposition is already false. -/
lemma helperForProposition_38_0_3_targetFalse_of_positiveDimension
    {m n : Nat} (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (hm : 0 < m) :
    ¬ (bifunctionInverse (convexIndicatorBifunction A.toLinearMap) =
          concaveIndicatorBifunctionLinear A.symm.toLinearMap ∧
        bifunctionAdjoint (bifunctionInverse (convexIndicatorBifunction A.toLinearMap)) =
          convexIndicatorBifunctionLinear (A.symm.toLinearMap.dualMap)) := by
  -- Positive dimension provides an explicit off-graph witness, so the generic target-failure
  -- lemma applies directly.
  apply helperForProposition_38_0_3_targetFalse_of_inverseOffGraphPoint A
  exact helperForProposition_38_0_3_inverseOffGraphPoint_of_positiveDimension A hm

/-- Helper for Proposition 38.0.3: in positive dimension, any proof of the full target
conjunction would force the scalar contradiction `0 = 1` after rewriting the second conjunct
through the explicit inverse formula. -/
lemma helperForProposition_38_0_3_target_forces_zero_eq_one_of_positiveDimension
    {m n : Nat} (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (hm : 0 < m)
    (hTarget :
      bifunctionInverse (convexIndicatorBifunction A.toLinearMap) =
          concaveIndicatorBifunctionLinear A.symm.toLinearMap ∧
        bifunctionAdjoint (bifunctionInverse (convexIndicatorBifunction A.toLinearMap)) =
          convexIndicatorBifunctionLinear (A.symm.toLinearMap.dualMap)) :
    (0 : ℝ) = 1 := by
  have hRewrittenSecond :
      bifunctionAdjoint (concaveIndicatorBifunctionLinear A.symm.toLinearMap) =
        convexIndicatorBifunctionLinear (A.symm.toLinearMap.dualMap) := by
    -- Rewrite the second conjunct using the explicit inverse formula proved earlier.
    simpa [helperForProposition_38_0_3_inverse_eq_concaveIndicator A] using hTarget.2
  -- The positive-dimensional obstruction then collapses the target conjunction to `0 = 1`.
  exact
    helperForProposition_38_0_3_rewrittenSecondConjunct_forces_zero_eq_one_of_positiveDimension
      A hm hRewrittenSecond

/-- Helper for Proposition 38.0.3: in positive dimension, once the inverse formula is fixed, the
advertised second conjunct is already impossible under the current `iInf`-adjoint
formalization. -/
lemma helperForProposition_38_0_3_secondConjunctFalse_of_positiveDimension_given_inverse
    {m n : Nat} (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (hm : 0 < m)
    (hInverse :
      bifunctionInverse (convexIndicatorBifunction A.toLinearMap) =
        concaveIndicatorBifunctionLinear A.symm.toLinearMap) :
    bifunctionAdjoint (bifunctionInverse (convexIndicatorBifunction A.toLinearMap)) ≠
      convexIndicatorBifunctionLinear (A.symm.toLinearMap.dualMap) := by
  intro hSecond
  have hRewritten :
      bifunctionAdjoint (concaveIndicatorBifunctionLinear A.symm.toLinearMap) =
        convexIndicatorBifunctionLinear (A.symm.toLinearMap.dualMap) := by
    -- The proved inverse formula rewrites the remaining target branch to the exposed
    -- concave-indicator obstruction.
    simpa [hInverse] using hSecond
  -- After the rewrite, the positive-dimensional contradiction lemma applies directly.
  exact
    (helperForProposition_38_0_3_rewrittenSecondConjunctFalse_of_positiveDimension A hm)
      hRewritten

/-- Helper for Proposition 38.0.3: in positive dimension, once the inverse formula is fixed, any
proof of the advertised second conjunct forces the scalar contradiction `0 = 1`. -/
lemma helperForProposition_38_0_3_secondConjunct_forces_zero_eq_one_of_positiveDimension_given_inverse
    {m n : Nat} (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (hm : 0 < m)
    (hInverse :
      bifunctionInverse (convexIndicatorBifunction A.toLinearMap) =
        concaveIndicatorBifunctionLinear A.symm.toLinearMap)
    (hSecond :
      bifunctionAdjoint (bifunctionInverse (convexIndicatorBifunction A.toLinearMap)) =
        convexIndicatorBifunctionLinear (A.symm.toLinearMap.dualMap)) :
    (0 : ℝ) = 1 := by
  have hRewritten :
      bifunctionAdjoint (concaveIndicatorBifunctionLinear A.symm.toLinearMap) =
        convexIndicatorBifunctionLinear (A.symm.toLinearMap.dualMap) := by
    -- Rewrite the original second conjunct using the proved inverse formula.
    simpa [hInverse] using hSecond
  -- The rewritten equality is already known to collapse the positive-dimensional primal space.
  exact
    helperForProposition_38_0_3_rewrittenSecondConjunct_forces_zero_eq_one_of_positiveDimension
      A hm hRewritten

/-- Helper for Proposition 38.0.3: the one-dimensional inverse graph of the identity map already
misses the point `(0, 1)`. -/
lemma helperForProposition_38_0_3_identityOneDim_inverseOffGraphPoint :
    ∃ x : Fin 1 → ℝ, ∃ u : Fin 1 → ℝ,
      u ≠ ((LinearEquiv.refl ℝ (Fin 1 → ℝ)).symm).toLinearMap x := by
  -- This is the positive-dimensional off-graph witness specialized to `m = 1`.
  simpa using
    (helperForProposition_38_0_3_inverseOffGraphPoint_of_positiveDimension
      (A := LinearEquiv.refl ℝ (Fin 1 → ℝ))
      (hm := by decide))

/-- Helper for Proposition 38.0.3: at the zero dual pair, the one-dimensional identity already
forces the adjoint of the concave indicator to take the value `⊥`. -/
lemma helperForProposition_38_0_3_identityOneDim_adjointAtZero_eq_bot :
    bifunctionAdjoint
        (concaveIndicatorBifunctionLinear
          (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)))
        (0 : Module.Dual ℝ (Fin 1 → ℝ))
        (0 : Module.Dual ℝ (Fin 1 → ℝ)) = ⊥ := by
  -- The explicit off-graph primal pair `(0, 1)` contributes `⊥` to the defining infimum.
  have hoff :
      (fun _ => (1 : ℝ)) ≠
        (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)) (0 : Fin 1 → ℝ) := by
    -- Evaluating at the unique coordinate shows that `1` cannot equal `0`.
    intro hEq
    have hAtZero : (fun _ => (1 : ℝ)) 0 = ((LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
        (0 : Fin 1 → ℝ)) 0 := by
      simpa using congrFun hEq 0
    norm_num at hAtZero
  -- Apply the generic off-graph collapse lemma to this explicit one-dimensional witness.
  simpa using
    (helperForProposition_38_0_3_adjoint_eq_bot_of_offGraphPoint
      (A := (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)))
      (uStar := (0 : Module.Dual ℝ (Fin 1 → ℝ)))
      (xStar := (0 : Module.Dual ℝ (Fin 1 → ℝ)))
      (x := (0 : Fin 1 → ℝ))
      (u := (fun _ => (1 : ℝ)))
      hoff)

/-- Helper for Proposition 38.0.3: at the zero dual pair, the convex indicator of the dual
identity map still takes the value `0`. -/
lemma helperForProposition_38_0_3_identityOneDim_convexIndicatorAtZero_eq_zero :
    convexIndicatorBifunctionLinear
        ((LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)).dualMap)
        (0 : Module.Dual ℝ (Fin 1 → ℝ))
        (0 : Module.Dual ℝ (Fin 1 → ℝ)) = 0 := by
  -- The zero dual pair lies on the graph of the dual identity map.
  simpa using
    (helperForProposition_38_0_3_convexIndicator_eq_zero_on_graph
      ((LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)).dualMap)
      (0 : Module.Dual ℝ (Fin 1 → ℝ)))

/-- Helper for Proposition 38.0.3: at the zero dual pair, the one-dimensional identity already
produces incompatible values for the two sides of the rewritten second conjunct. -/
lemma helperForProposition_38_0_3_identityOneDim_zeroPairMismatch :
    bifunctionAdjoint
        (concaveIndicatorBifunctionLinear
          (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)))
        (0 : Module.Dual ℝ (Fin 1 → ℝ))
        (0 : Module.Dual ℝ (Fin 1 → ℝ)) ≠
      convexIndicatorBifunctionLinear
        ((LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)).dualMap)
        (0 : Module.Dual ℝ (Fin 1 → ℝ))
        (0 : Module.Dual ℝ (Fin 1 → ℝ)) := by
  -- Rewrite both zero-pair evaluations to the explicit `⊥` and `0` values computed above.
  rw [helperForProposition_38_0_3_identityOneDim_adjointAtZero_eq_bot,
    helperForProposition_38_0_3_identityOneDim_convexIndicatorAtZero_eq_zero]
  -- The extended-real values `⊥` and `0` are distinct.
  simp

/-- Helper for Proposition 38.0.3: in one dimension, the identity map already exhibits the
failure of the current `iInf`-adjoint formula to reproduce the claimed convex indicator. -/
lemma helperForProposition_38_0_3_identityOneDim_adjoint_ne_convexIndicator :
    bifunctionAdjoint
        (concaveIndicatorBifunctionLinear
          (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))) ≠
      convexIndicatorBifunctionLinear
        ((LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)).dualMap) := by
  intro hEq
  have hEqAtZero :
      bifunctionAdjoint
          (concaveIndicatorBifunctionLinear
            (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)))
          (0 : Module.Dual ℝ (Fin 1 → ℝ))
          (0 : Module.Dual ℝ (Fin 1 → ℝ)) =
        convexIndicatorBifunctionLinear
          ((LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)).dualMap)
          (0 : Module.Dual ℝ (Fin 1 → ℝ))
          (0 : Module.Dual ℝ (Fin 1 → ℝ)) := by
    -- Any equality of bifunctions must agree when evaluated at the zero dual pair.
    exact congrFun (congrFun hEq (0 : Module.Dual ℝ (Fin 1 → ℝ)))
      (0 : Module.Dual ℝ (Fin 1 → ℝ))
  -- The new zero-pair mismatch lemma isolates the concrete contradiction behind this function
  -- inequality.
  exact helperForProposition_38_0_3_identityOneDim_zeroPairMismatch hEqAtZero

/-- Helper for Proposition 38.0.3: any proof of the rewritten second conjunct for the
one-dimensional identity would force the impossible equality `⊥ = 0` at the zero dual pair. -/
lemma helperForProposition_38_0_3_identityOneDim_secondConjunct_forces_bot_eq_zero
    (hSecond :
      bifunctionAdjoint
          (bifunctionInverse
            (convexIndicatorBifunction
              (LinearEquiv.refl ℝ (Fin 1 → ℝ)).toLinearMap)) =
        convexIndicatorBifunctionLinear
          (((LinearEquiv.refl ℝ (Fin 1 → ℝ)).symm).toLinearMap.dualMap)) :
    (⊥ : EReal) = 0 := by
  -- Specialize the generic off-graph contradiction package to the one-dimensional identity.
  exact helperForProposition_38_0_3_secondConjunct_forces_bot_eq_zero_of_inverseOffGraphPoint
    (A := LinearEquiv.refl ℝ (Fin 1 → ℝ))
    helperForProposition_38_0_3_identityOneDim_inverseOffGraphPoint hSecond

/-- Helper for Proposition 38.0.3: for the one-dimensional identity, any proof of the second
conjunct would force all vectors in `ℝ¹` to coincide. -/
lemma helperForProposition_38_0_3_identityOneDim_secondConjunct_forces_domainSubsingleton
    (hSecond :
      bifunctionAdjoint
          (bifunctionInverse
            (convexIndicatorBifunction
              (LinearEquiv.refl ℝ (Fin 1 → ℝ)).toLinearMap)) =
        convexIndicatorBifunctionLinear
          (((LinearEquiv.refl ℝ (Fin 1 → ℝ)).symm).toLinearMap.dualMap)) :
    Subsingleton (Fin 1 → ℝ) := by
  -- This is the generic domain-collapse consequence specialized to the identity map on `ℝ¹`.
  exact helperForProposition_38_0_3_secondConjunct_forces_domainSubsingleton
    (A := LinearEquiv.refl ℝ (Fin 1 → ℝ)) hSecond

/-- Helper for Proposition 38.0.3: after rewriting the inverse term, the second conjunct of the
target proposition is already false for the one-dimensional identity map. -/
lemma helperForProposition_38_0_3_identityOneDim_secondConjunctFalse :
    bifunctionAdjoint
        (bifunctionInverse
          (convexIndicatorBifunction
            (LinearEquiv.refl ℝ (Fin 1 → ℝ)).toLinearMap)) ≠
      convexIndicatorBifunctionLinear
        (((LinearEquiv.refl ℝ (Fin 1 → ℝ)).symm).toLinearMap.dualMap) := by
  intro hSecond
  -- Route correction: instead of only evaluating at the zero dual pair, use the new structural
  -- consequence that the second conjunct would collapse the whole primal space to a subsingleton.
  have hSub :
      Subsingleton (Fin 1 → ℝ) :=
    helperForProposition_38_0_3_identityOneDim_secondConjunct_forces_domainSubsingleton hSecond
  let z : Fin 1 → ℝ := 0
  let o : Fin 1 → ℝ := fun _ => (1 : ℝ)
  have hzEq : z = o := hSub.elim z o
  have hZeroEqOne : (0 : ℝ) = 1 := by
    -- Evaluating the forced equality at the unique coordinate shows `0 = 1`.
    simpa [z, o] using congrFun hzEq 0
  have hZeroNeOne : (0 : ℝ) ≠ 1 := by
    norm_num
  exact hZeroNeOne hZeroEqOne

/-- Helper for Proposition 38.0.3: the full conjunction claimed in the target theorem fails for
the one-dimensional identity map under the current adjoint formalization. -/
lemma helperForProposition_38_0_3_identityOneDim_targetFalse :
    ¬ (bifunctionInverse
          (convexIndicatorBifunction
            (LinearEquiv.refl ℝ (Fin 1 → ℝ)).toLinearMap) =
          concaveIndicatorBifunctionLinear
            ((LinearEquiv.refl ℝ (Fin 1 → ℝ)).symm).toLinearMap ∧
        bifunctionAdjoint
          (bifunctionInverse
            (convexIndicatorBifunction
              (LinearEquiv.refl ℝ (Fin 1 → ℝ)).toLinearMap)) =
          convexIndicatorBifunctionLinear
            (((LinearEquiv.refl ℝ (Fin 1 → ℝ)).symm).toLinearMap.dualMap)) := by
  -- Invoke the positive-dimensional obstruction in the specialized one-dimensional setting.
  simpa using
    (helperForProposition_38_0_3_targetFalse_of_positiveDimension
      (A := LinearEquiv.refl ℝ (Fin 1 → ℝ))
      (hm := by decide))

end Section38
end Chap08

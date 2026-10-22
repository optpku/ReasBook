/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section05_part12
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section36_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section38_part2

section Chap08
section Section38

/-- The weak topology on the algebraic dual induced by evaluation, used to talk about
lower semicontinuity (and hence "closedness") of functions on dual spaces. -/
noncomputable local instance instTopologicalSpace_moduleDual_weak
    {E : Type*} [AddCommGroup E] [Module ℝ E] :
    TopologicalSpace (Module.Dual ℝ E) :=
  WeakBilin.instTopologicalSpace
    (B := (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)).flip)

/-- A bifunction is "closed" when it is lower semicontinuous as a function on the product. -/
def IsProductLowerSemicontinuousBifunction
    {U X : Type*} [TopologicalSpace U] [TopologicalSpace X] (F : U → X → EReal) : Prop :=
  LowerSemicontinuous (fun p : U × X => F p.1 p.2)

-- Proof sketch: The book’s argument uses that when `u ∈ ri (dom (F₁ □ F₂))` the epigraph of the
-- slice `x ↦ (F₁ □ F₂) u x` is the corresponding slice of the epigraph of the bifunction on the
-- product; taking closed convex hulls (lower semicontinuous hulls) commutes with slicing at such
-- `u`, yielding equality of the two closures.
/-- Proposition 38.2.1: We have

`(cl (F₁ □ F₂)) u = cl (F₁ u □ F₂ u)`

for each `u` in the relative interior of `dom (F₁ □ F₂)`, and hence in particular for each
`u ∈ ri (dom F₁) ∩ ri (dom F₂)`.

Here `cl` is modeled by `bifunctionClosure` (closure on the product) on the left-hand side and by
`erealFunctionClosure` (closure on the slice) on the right-hand side, and `ri` is modeled by
`intrinsicInterior`. Because fiberwise convexity alone gives no regularity in `u`, the formal
statement assumes that the infimal convolution itself is proper and lower semicontinuous on the
product. -/
theorem bifunctionClosure_infimalConvolution_apply_eq_closure_apply_infimalConvolution
    {m n : Nat} (F₁ F₂ : FiberwiseProperConvexBifunction m n)
    (hproper :
      IsProperEReal
        (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
          bifunctionInfimalConvolution F₁ F₂ p.1 p.2))
    (hclosed :
      IsProductLowerSemicontinuousBifunction (bifunctionInfimalConvolution F₁ F₂)) :
    (∀ u,
        u ∈ intrinsicInterior ℝ (bifunctionDom (bifunctionInfimalConvolution F₁ F₂)) →
          bifunctionClosure (bifunctionInfimalConvolution F₁ F₂) u =
            erealFunctionClosure (bifunctionInfimalConvolution F₁ F₂ u)) ∧
      (∀ u,
        u ∈ intrinsicInterior ℝ (bifunctionDom F₁.toFun) ∩
              intrinsicInterior ℝ (bifunctionDom F₂.toFun) →
          bifunctionClosure (bifunctionInfimalConvolution F₁ F₂) u =
            erealFunctionClosure (bifunctionInfimalConvolution F₁ F₂ u)) := by
  let K := bifunctionInfimalConvolution F₁ F₂
  have hNoBot : ∀ u x, K u x ≠ (⊥ : EReal) := by
    intro u x
    exact hproper.1 (u, x)
  have hProductClosure : bifunctionClosure K = K := by
    funext u x
    have hProductLsc :
        LowerSemicontinuous
          (fun p : (Fin m → ℝ) × (Fin n → ℝ) => K p.1 p.2) := by
      simpa [K, IsProductLowerSemicontinuousBifunction] using hclosed
    have hHull :
        erealLowerSemicontinuousHull
            (fun p : (Fin m → ℝ) × (Fin n → ℝ) => K p.1 p.2) =
          (fun p : (Fin m → ℝ) × (Fin n → ℝ) => K p.1 p.2) := by
      funext p
      apply le_antisymm
      · rw [erealLowerSemicontinuousHull]
        refine iSup_le ?_
        intro g
        exact g.2.2 p
      · rw [erealLowerSemicontinuousHull]
        exact le_iSup_of_le ⟨_, hProductLsc, le_rfl⟩ le_rfl
    unfold bifunctionClosure erealFunctionClosure
    simp [hNoBot, hHull]
  have hSliceClosed (u : Fin m → ℝ) : LowerSemicontinuous (K u) := by
    simpa [K, Function.comp, IsProductLowerSemicontinuousBifunction] using
      hclosed.comp_continuous
        (continuous_const.prodMk (continuous_id : Continuous (fun x : Fin n → ℝ => x)))
  have hSliceClosure (u : Fin m → ℝ) : erealFunctionClosure (K u) = K u := by
    have hHull : erealLowerSemicontinuousHull (K u) = K u := by
      funext x
      apply le_antisymm
      · rw [erealLowerSemicontinuousHull]
        refine iSup_le ?_
        intro g
        exact g.2.2 x
      · rw [erealLowerSemicontinuousHull]
        exact le_iSup_of_le ⟨K u, hSliceClosed u, le_rfl⟩ le_rfl
    unfold erealFunctionClosure
    simp [hNoBot u, hHull]
  constructor
  · intro u _
    rw [show bifunctionClosure (bifunctionInfimalConvolution F₁ F₂) = K by
          simpa [K] using hProductClosure,
      show erealFunctionClosure (bifunctionInfimalConvolution F₁ F₂ u) = K u by
          simpa [K] using hSliceClosure u]
  · intro u _
    rw [show bifunctionClosure (bifunctionInfimalConvolution F₁ F₂) = K by
          simpa [K] using hProductClosure,
      show erealFunctionClosure (bifunctionInfimalConvolution F₁ F₂ u) = K u by
          simpa [K] using hSliceClosure u]

/-- Helper for Corollary 38.2.1: the first Section 38.1 counterexample bifunction is already
closed in the product sense. -/
lemma helperForCorollary_38_2_1_counterexampleFirst_closed :
    IsProductLowerSemicontinuousBifunction
      helperForTheorem_38_1_counterexampleFirstBifunction.toFun := by
  -- Rewrite the product function as the `⊤`-valued indicator of the open complement of the
  -- closed hyperplane `u 0 = 0`.
  have hopen : IsOpen {p : (Fin 1 → ℝ) × (Fin 1 → ℝ) | p.1 0 ≠ 0} := by
    have hclosed : IsClosed {p : (Fin 1 → ℝ) × (Fin 1 → ℝ) | p.1 0 = 0} := by
      simpa using isClosed_eq ((continuous_apply 0).comp continuous_fst) continuous_const
    simpa [Set.compl_setOf] using hclosed.isOpen_compl
  have hindicator :
      LowerSemicontinuous
        (Set.indicator {p : (Fin 1 → ℝ) × (Fin 1 → ℝ) | p.1 0 ≠ 0} (fun _ => (⊤ : EReal))) := by
    simpa using hopen.lowerSemicontinuous_indicator (show (0 : EReal) ≤ ⊤ by simp)
  have hEq :
      (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
        helperForTheorem_38_1_counterexampleFirstBifunction.toFun p.1 p.2) =
      Set.indicator {p : (Fin 1 → ℝ) × (Fin 1 → ℝ) | p.1 0 ≠ 0} (fun _ => (⊤ : EReal)) := by
    -- The Section 38.1 bifunction is `0` on the hyperplane and `⊤` exactly off it.
    funext p
    by_cases hp : p.1 0 = 0
    · simp [helperForTheorem_38_1_counterexampleFirstBifunction, Set.indicator, hp]
    · simp [helperForTheorem_38_1_counterexampleFirstBifunction, Set.indicator, hp]
  -- Replacing the product function by its indicator form reduces the goal to the standard
  -- lower-semicontinuity theorem for open-set indicators.
  rw [IsProductLowerSemicontinuousBifunction, hEq]
  exact hindicator

/-- Helper for Corollary 38.2.1: the constant-zero Section 38.1 counterexample bifunction is
closed in the product sense. -/
lemma helperForCorollary_38_2_1_counterexampleSecond_closed :
    IsProductLowerSemicontinuousBifunction
      helperForTheorem_38_1_counterexampleSecondBifunction.toFun := by
  -- The product function is constant zero, so lower semicontinuity is immediate.
  simpa [IsProductLowerSemicontinuousBifunction,
    helperForTheorem_38_1_counterexampleSecondBifunction] using
    (lowerSemicontinuous_const :
      LowerSemicontinuous (fun _ : (Fin 1 → ℝ) × (Fin 1 → ℝ) => (0 : EReal)))

/-- Helper for Corollary 38.2.1: the closure of the counterexample right-hand side collapses to
the constant `⊥` bifunction because the raw function already attains `⊥`. -/
lemma helperForCorollary_38_2_1_counterexample_closure_rhs_eq_const_bot :
    bifunctionClosure
      (bifunctionInfimalConvolutionInSecond
        (bifunctionAdjoint helperForTheorem_38_1_counterexampleFirstBifunction.toFun)
        (bifunctionAdjoint helperForTheorem_38_1_counterexampleSecondBifunction.toFun)) =
      fun _ _ => (⊥ : EReal) := by
  let raw := bifunctionInfimalConvolutionInSecond
    (bifunctionAdjoint helperForTheorem_38_1_counterexampleFirstBifunction.toFun)
    (bifunctionAdjoint helperForTheorem_38_1_counterexampleSecondBifunction.toFun)
  have hnot :
      ¬ ∀ p : Module.Dual ℝ (Fin 1 → ℝ) × Module.Dual ℝ (Fin 1 → ℝ),
          raw p.1 p.2 ≠ (⊥ : EReal) := by
    -- The explicit Section 38.2 witness already shows that the raw right-hand side hits `⊥`.
    intro hall
    exact
      (hall (0, helperForTheorem_38_1_counterexampleXStar))
        helperForTheorem_38_2_counterexample_rightValue
  -- Once the product function takes `⊥` somewhere, `erealFunctionClosure` picks its constant
  -- `⊥` branch everywhere.
  funext u x
  unfold bifunctionClosure erealFunctionClosure
  rw [if_neg hnot]

/-- Helper for Corollary 38.2.1: specializing the claimed conclusion to the Section 38.1 witness
pair yields a contradiction. -/
lemma helperForCorollary_38_2_1_counterexample_targetFalse :
    (IsProductLowerSemicontinuousBifunction
        (bifunctionInfimalConvolution
          helperForTheorem_38_1_counterexampleFirstBifunction
          helperForTheorem_38_1_counterexampleSecondBifunction) ∧
      bifunctionAdjoint
          (bifunctionInfimalConvolution
            helperForTheorem_38_1_counterexampleFirstBifunction
            helperForTheorem_38_1_counterexampleSecondBifunction) =
        bifunctionClosure
          (bifunctionInfimalConvolutionInSecond
            (bifunctionAdjoint helperForTheorem_38_1_counterexampleFirstBifunction.toFun)
            (bifunctionAdjoint helperForTheorem_38_1_counterexampleSecondBifunction.toFun))) →
      False := by
  intro hConclusion
  -- Evaluate the advertised equality at the dual witness where Section 38.2 already separates the
  -- raw left-hand side `0` from the raw right-hand side `⊥`.
  have hValue :=
    congrFun (congrFun hConclusion.2 (0 : Module.Dual ℝ (Fin 1 → ℝ)))
      helperForTheorem_38_1_counterexampleXStar
  rw [helperForTheorem_38_2_counterexample_leftValue,
    helperForCorollary_38_2_1_counterexample_closure_rhs_eq_const_bot] at hValue
  exact EReal.zero_ne_bot hValue

/-- Helper for Corollary 38.2.1: the full specialized implication is already false on the
imported Section 38.1 counterexample pair. -/
lemma helperForCorollary_38_2_1_specializedImplicationFalse :
    ¬ (IsProductLowerSemicontinuousBifunction
          helperForTheorem_38_1_counterexampleFirstBifunction.toFun →
        IsProductLowerSemicontinuousBifunction
          helperForTheorem_38_1_counterexampleSecondBifunction.toFun →
        (intrinsicInterior ℝ
              (bifunctionDom helperForTheorem_38_1_counterexampleFirstBifunction.toFun) ∩
            intrinsicInterior ℝ
              (bifunctionDom helperForTheorem_38_1_counterexampleSecondBifunction.toFun)).Nonempty →
        IsProductLowerSemicontinuousBifunction
            (bifunctionInfimalConvolution
              helperForTheorem_38_1_counterexampleFirstBifunction
              helperForTheorem_38_1_counterexampleSecondBifunction) ∧
          bifunctionAdjoint
              (bifunctionInfimalConvolution
                helperForTheorem_38_1_counterexampleFirstBifunction
                helperForTheorem_38_1_counterexampleSecondBifunction) =
            bifunctionClosure
              (bifunctionInfimalConvolutionInSecond
                (bifunctionAdjoint helperForTheorem_38_1_counterexampleFirstBifunction.toFun)
                (bifunctionAdjoint
                  helperForTheorem_38_1_counterexampleSecondBifunction.toFun))) := by
  intro hSpecialized
  -- Feed the proved closedness witnesses and the imported relative-interior witness into the
  -- specialized implication, then contradict its conclusion pointwise.
  have hConclusion :=
    hSpecialized
      helperForCorollary_38_2_1_counterexampleFirst_closed
      helperForCorollary_38_2_1_counterexampleSecond_closed
      helperForTheorem_38_2_counterexample_hri
  exact helperForCorollary_38_2_1_counterexample_targetFalse hConclusion

-- Proof sketch: Apply Theorem 38.2 to get `(F₁ □ F₂)^* = F₁^* □ F₂^*` under the relative interior
-- condition; then use the closedness of `F₁` and `F₂` to deduce closedness of `F₁ □ F₂`, hence the
-- left-hand side is already closed and equals the closure of the right-hand side.
/-- Corollary 38.2.1: Let `F₁` and `F₂` be closed proper convex bifunctions from `ℝ^m` to `ℝ^n`.
If `ri (dom F₁)` and `ri (dom F₂)` have a point in common, then `F₁ □ F₂` is closed and

`(F₁ □ F₂)^* = cl (F₁^* □ F₂^*)`.

Here `cl` is modeled by `bifunctionClosure`, induced from `erealFunctionClosure` on the product, and the
relative interior `ri` is modeled by `intrinsicInterior`. -/
noncomputable def reflectSecondGraphMap {n m : Nat} :
    (Fin (n + m) → ℝ) →ₗ[ℝ] (Fin (n + m) → ℝ) where
  toFun z := Fin.append
    (fun i : Fin n => z (Fin.castAdd m i))
    (fun j : Fin m => -z (Fin.natAdd n j))
  map_add' := by
    intro z w
    ext i
    cases i using Fin.addCases with
    | left i => simp
    | right i => simp [add_comm]
  map_smul' := by
    intro a z
    ext i
    cases i using Fin.addCases with
    | left i => simp
    | right i => simp

lemma reflectSecondGraphMap_surjective {n m : Nat} :
    Function.Surjective (reflectSecondGraphMap (n := n) (m := m)) := by
  intro z
  refine ⟨reflectSecondGraphMap z, ?_⟩
  ext i
  cases i using Fin.addCases with
  | left i => simp [reflectSecondGraphMap]
  | right i => simp [reflectSecondGraphMap]

noncomputable def convexReflectionOfConcave {n m : Nat}
    (G : (Fin n → ℝ) → (Fin m → ℝ) → EReal) :
    (Fin n → ℝ) → (Fin m → ℝ) → EReal :=
  fun x u => -G x (-u)

lemma convexReflectionOfConcave_graph {n m : Nat}
    (G : (Fin n → ℝ) → (Fin m → ℝ) → EReal) :
    bifunctionGraphFunction (convexReflectionOfConcave G) =
      fun z => -bifunctionGraphFunction G (reflectSecondGraphMap z) := by
  funext z
  simp only [bifunctionGraphFunction, convexReflectionOfConcave, reflectSecondGraphMap,
    LinearMap.coe_mk, AddHom.coe_mk, Fin.append_left, Fin.append_right]
  congr 2

lemma convexReflectionOfConcave_properConvexBifunction {n m : Nat}
    (G : (Fin n → ℝ) → (Fin m → ℝ) → EReal)
    (hG : ProperConcaveBifunction G) :
    ProperConvexBifunction (convexReflectionOfConcave G) := by
  have hbase : ProperConvexFunctionOn (Set.univ : Set (Fin (n + m) → ℝ))
      (fun z => -bifunctionGraphFunction G z) :=
    helperForTheorem_6_30_11_properConvexFunctionOn_univ_of_properConvexERealFunction
      (f := fun z => -bifunctionGraphFunction G z) hG.2
  have hpre : ProperConvexFunctionOn (Set.univ : Set (Fin (n + m) → ℝ))
      (fun z => -bifunctionGraphFunction G (reflectSecondGraphMap z)) :=
    properConvexFunctionOn_precomp_linearMap_surjective
      (A := reflectSecondGraphMap) reflectSecondGraphMap_surjective hbase
  refine ⟨?_, ?_⟩
  · rw [ConvexBifunction, convexReflectionOfConcave_graph]
    exact hpre.1
  · rw [convexReflectionOfConcave_graph]
    exact helperForTheorem_21_3_properConvexEReal_of_properConvexFunctionOn_univ _ hpre

lemma fiberwiseProperConvex_of_properConvexBifunction {n m : Nat}
    (F : (Fin n → ℝ) → (Fin m → ℝ) → EReal)
    (hF : ProperConvexBifunction F) :
    ∃ Fpkg : FiberwiseProperConvexBifunction n m, Fpkg.toFun = F := by
  let Fpkg : FiberwiseProperConvexBifunction n m := {
    toFun := F
    proper := by
      constructor
      · intro u x
        simpa [bifunctionGraphFunction] using hF.2.1.1 (Fin.append u x)
      · rcases hF.2.1.2 with ⟨z, hz⟩
        refine ⟨(fun i => z (Fin.castAdd m i)), (fun j => z (Fin.natAdd n j)), ?_⟩
        simpa [bifunctionGraphFunction] using hz
    convex := by
      intro u
      rw [IsERealConvex]
      intro p hp q hq a b ha hb hab
      have hp' :
          (Fin.append u p.1, p.2) ∈ epigraph (Set.univ : Set (Fin (n + m) → ℝ))
            (bifunctionGraphFunction F) := by
        exact ⟨(by simp : Fin.append u p.1 ∈ (Set.univ : Set (Fin (n + m) → ℝ))),
          by simpa [ERealEpigraph, bifunctionGraphFunction] using hp⟩
      have hq' :
          (Fin.append u q.1, q.2) ∈ epigraph (Set.univ : Set (Fin (n + m) → ℝ))
            (bifunctionGraphFunction F) := by
        exact ⟨(by simp : Fin.append u q.1 ∈ (Set.univ : Set (Fin (n + m) → ℝ))),
          by simpa [ERealEpigraph, bifunctionGraphFunction] using hq⟩
      have hcomb := hF.1 hp' hq' ha hb hab
      rcases hcomb with ⟨-, hcomb⟩
      simp only [Prod.smul_mk, Prod.mk_add_mk, bifunctionGraphFunction, Pi.add_apply,
        Pi.smul_apply, Fin.append_left, Fin.append_right, smul_eq_mul] at hcomb
      have hu : (fun i => a * u i + b * u i) = u := by
        ext i
        simp [← add_mul, hab]
      rw [hu] at hcomb
      change F u (a • p.1 + b • q.1) ≤ ((a * p.2 + b * q.2 : ℝ) : EReal)
      simpa [bifunctionGraphFunction, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using hcomb
  }
  exact ⟨Fpkg, rfl⟩

lemma convexReflectionOfConcave_dom {n m : Nat}
    (G : (Fin n → ℝ) → (Fin m → ℝ) → EReal) :
    bifunctionDom (convexReflectionOfConcave G) = bifunctionDomBot G := by
  ext x
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨-u, ?_⟩
    simpa [convexReflectionOfConcave] using hu
  · rintro ⟨u, hu⟩
    refine ⟨-u, ?_⟩
    simpa [convexReflectionOfConcave] using hu

lemma neg_iSup_eq_iInf_neg {A : Sort*} (f : A → EReal) :
    -(⨆ a, f a) = ⨅ a, -f a := by
  have h := congrArg Neg.neg
    (helperForTheorem_6_30_4_neg_iInf_eq_iSup_neg (fun a => -f a))
  simpa using h.symm

lemma iInf_pair_eq_nested {A B : Type*} (f : A × B → EReal) :
    (⨅ p : A × B, f p) = ⨅ a : A, ⨅ b : B, f (a, b) := by
  apply le_antisymm
  · refine le_iInf ?_
    intro a
    refine le_iInf ?_
    intro b
    exact iInf_le f (a, b)
  · refine le_iInf ?_
    rintro ⟨a, b⟩
    exact le_trans (iInf_le _ a) (iInf_le _ b)

lemma textbookBifunctionAdjoint_convexReflection {n m : Nat}
    (G : (Fin n → ℝ) → (Fin m → ℝ) → EReal)
    (hG : ConcaveBifunction G) (u : Fin m → ℝ) (x : Fin n → ℝ) :
    textbookBifunctionAdjoint (convexReflectionOfConcave G) u x =
      -adjointOfConcaveBifunction ⟨G, hG⟩ u (-x) := by
  rw [textbookBifunctionAdjoint, adjointOfConcaveBifunction, sSup_range,
    neg_iSup_eq_iInf_neg, iInf_pair_eq_nested]
  refine iInf_congr ?_
  intro a
  let L : (Fin m → ℝ) → EReal := fun b =>
    convexReflectionOfConcave G a b - (((b ⬝ᵥ u : ℝ)) : EReal) +
      (((a ⬝ᵥ x : ℝ)) : EReal)
  have hreindex : (⨅ b : Fin m → ℝ, L b) = ⨅ v : Fin m → ℝ, L (-v) := by
    apply le_antisymm
    · refine le_iInf ?_
      intro v
      exact iInf_le L (-v)
    · refine le_iInf ?_
      intro b
      simpa using (iInf_le (fun v : Fin m → ℝ => L (-v)) (-b))
  rw [show (⨅ b : Fin m → ℝ,
      convexReflectionOfConcave G a b - (((b ⬝ᵥ u : ℝ)) : EReal) +
        (((a ⬝ᵥ x : ℝ)) : EReal)) = ⨅ v : Fin m → ℝ, L (-v) by
    exact hreindex]
  refine iInf_congr ?_
  intro v
  let r : ℝ := -(v ⬝ᵥ u) - (a ⬝ᵥ x)
  have hneg := EReal.neg_add
    (x := G a v)
    (y := ((r : ℝ) : EReal))
    (Or.inr (by simp)) (Or.inr (by simp))
  have hrneg :
      -((r : ℝ) : EReal) =
        (((v ⬝ᵥ u : ℝ) : EReal)) + (((a ⬝ᵥ x : ℝ) : EReal)) := by
    rw [← EReal.coe_add]
    change (((-r : ℝ) : EReal)) = ((((v ⬝ᵥ u) + (a ⬝ᵥ x) : ℝ)) : EReal)
    congr 1
    dsimp [r]
    ring
  calc
    L (-v) = -G a v +
        ((((v ⬝ᵥ u : ℝ)) : EReal) + (((a ⬝ᵥ x : ℝ)) : EReal)) := by
      simp [L, convexReflectionOfConcave, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    _ = -G a v - ((r : ℝ) : EReal) := by rw [sub_eq_add_neg, hrneg]
    _ = -(G a v + ((r : ℝ) : EReal)) := hneg.symm
    _ = -(G a v - (((v ⬝ᵥ u : ℝ)) : EReal) + (((a ⬝ᵥ (-x) : ℝ)) : EReal)) := by
      simp [r, sub_eq_add_neg, add_assoc]

lemma infimalConvolution_convexReflection {n m : Nat}
    (G₁ G₂ : (Fin n → ℝ) → (Fin m → ℝ) → EReal)
    (x : Fin n → ℝ) (u : Fin m → ℝ) :
    bifunctionInfimalConvolutionInSecond
        (convexReflectionOfConcave G₁) (convexReflectionOfConcave G₂) x u =
      -concaveBifunctionInfimalConvolutionInSecond G₁ G₂ x (-u) := by
  rw [concaveBifunctionInfimalConvolutionInSecond, neg_iSup_eq_iInf_neg,
    bifunctionInfimalConvolutionInSecond]
  let L : (Fin m → ℝ) → EReal := fun y =>
    convexReflectionOfConcave G₁ x (u - y) + convexReflectionOfConcave G₂ x y
  have hreindex : (⨅ y : Fin m → ℝ, L y) = ⨅ v : Fin m → ℝ, L (-v) := by
    apply le_antisymm
    · refine le_iInf ?_
      intro v
      exact iInf_le L (-v)
    · refine le_iInf ?_
      intro y
      simpa using (iInf_le (fun v : Fin m → ℝ => L (-v)) (-y))
  rw [show (⨅ y : Fin m → ℝ,
      convexReflectionOfConcave G₁ x (u - y) + convexReflectionOfConcave G₂ x y) =
      ⨅ v : Fin m → ℝ, L (-v) by exact hreindex]
  refine iInf_congr ?_
  intro v
  simp [L, convexReflectionOfConcave, erealAddConcaveBook, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc]

noncomputable def infimalConvolutionFirstGraphMap {n m : Nat} :
    (Fin ((n + m) + m) → ℝ) →ₗ[ℝ] (Fin (n + m) → ℝ) where
  toFun z :=
    let w := projXLinearMap (n := n + m) (m := m) z
    let y := projLamLinearMap (n := n + m) (m := m) z
    Fin.append (projXLinearMap (n := n) (m := m) w)
      (projLamLinearMap (n := n) (m := m) w - y)
  map_add' := by
    intro z w
    ext i
    cases i using Fin.addCases with
    | left i => simp [projXLinearMap, projLamLinearMap]
    | right i =>
        simp [projXLinearMap, projLamLinearMap]
        ring
  map_smul' := by
    intro a z
    ext i
    cases i using Fin.addCases with
    | left i => simp [projXLinearMap, projLamLinearMap]
    | right i =>
        simp [projXLinearMap, projLamLinearMap]
        ring

noncomputable def infimalConvolutionSecondGraphMap {n m : Nat} :
    (Fin ((n + m) + m) → ℝ) →ₗ[ℝ] (Fin (n + m) → ℝ) where
  toFun z :=
    let w := projXLinearMap (n := n + m) (m := m) z
    let y := projLamLinearMap (n := n + m) (m := m) z
    Fin.append (projXLinearMap (n := n) (m := m) w) y
  map_add' := by
    intro z w
    ext i
    cases i using Fin.addCases with
    | left i => simp [projXLinearMap, projLamLinearMap]
    | right i => simp [projXLinearMap, projLamLinearMap]
  map_smul' := by
    intro a z
    ext i
    cases i using Fin.addCases with
    | left i => simp [projXLinearMap, projLamLinearMap]
    | right i => simp [projXLinearMap, projLamLinearMap]

lemma infimalConvolutionFirstGraphMap_surjective {n m : Nat} :
    Function.Surjective (infimalConvolutionFirstGraphMap (n := n) (m := m)) := by
  intro w
  refine ⟨Fin.append w (0 : Fin m → ℝ), ?_⟩
  ext i
  cases i using Fin.addCases with
  | left i => simp [infimalConvolutionFirstGraphMap, projXLinearMap, projLamLinearMap]
  | right i => simp [infimalConvolutionFirstGraphMap, projXLinearMap, projLamLinearMap]

lemma infimalConvolutionSecondGraphMap_surjective {n m : Nat} :
    Function.Surjective (infimalConvolutionSecondGraphMap (n := n) (m := m)) := by
  intro w
  let x : Fin n → ℝ := fun i => w (Fin.castAdd m i)
  let y : Fin m → ℝ := fun j => w (Fin.natAdd n j)
  refine ⟨Fin.append (Fin.append x (0 : Fin m → ℝ)) y, ?_⟩
  ext i
  cases i using Fin.addCases with
  | left i => simp [infimalConvolutionSecondGraphMap, projXLinearMap, projLamLinearMap, x]
  | right i => simp [infimalConvolutionSecondGraphMap, projXLinearMap, projLamLinearMap, y]

lemma bifunctionInfimalConvolutionInSecond_convexBifunction {n m : Nat}
    (F₁ F₂ : (Fin n → ℝ) → (Fin m → ℝ) → EReal)
    (hF₁ : ProperConvexBifunction F₁) (hF₂ : ProperConvexBifunction F₂) :
    ConvexBifunction (bifunctionInfimalConvolutionInSecond F₁ F₂) := by
  let A₁ := infimalConvolutionFirstGraphMap (n := n) (m := m)
  let A₂ := infimalConvolutionSecondGraphMap (n := n) (m := m)
  let P := projXLinearMap (n := n + m) (m := m)
  let objective : (Fin ((n + m) + m) → ℝ) → EReal := fun z =>
    bifunctionGraphFunction F₁ (A₁ z) + bifunctionGraphFunction F₂ (A₂ z)
  have hbase₁ : ProperConvexFunctionOn (Set.univ : Set (Fin (n + m) → ℝ))
      (bifunctionGraphFunction F₁) :=
    helperForTheorem_6_30_11_properConvexFunctionOn_univ_of_properConvexERealFunction
      (f := bifunctionGraphFunction F₁) hF₁.2
  have hbase₂ : ProperConvexFunctionOn (Set.univ : Set (Fin (n + m) → ℝ))
      (bifunctionGraphFunction F₂) :=
    helperForTheorem_6_30_11_properConvexFunctionOn_univ_of_properConvexERealFunction
      (f := bifunctionGraphFunction F₂) hF₂.2
  have hpre₁ : ProperConvexFunctionOn (Set.univ : Set (Fin ((n + m) + m) → ℝ))
      (fun z => bifunctionGraphFunction F₁ (A₁ z)) := by
    exact properConvexFunctionOn_precomp_linearMap_surjective
      (A := A₁) infimalConvolutionFirstGraphMap_surjective hbase₁
  have hpre₂ : ProperConvexFunctionOn (Set.univ : Set (Fin ((n + m) + m) → ℝ))
      (fun z => bifunctionGraphFunction F₂ (A₂ z)) := by
    exact properConvexFunctionOn_precomp_linearMap_surjective
      (A := A₂) infimalConvolutionSecondGraphMap_surjective hbase₂
  have hobj : ConvexFunctionOn (Set.univ : Set (Fin ((n + m) + m) → ℝ)) objective := by
    simpa [objective] using convexFunctionOn_add_of_proper hpre₁ hpre₂
  have hfiber := convexFunctionOn_inf_fiber_linearMap P objective hobj
  have heq :
      (fun w : Fin (n + m) → ℝ =>
        sInf {r : EReal | ∃ z : Fin ((n + m) + m) → ℝ, P z = w ∧ r = objective z}) =
      bifunctionGraphFunction (bifunctionInfimalConvolutionInSecond F₁ F₂) := by
    funext w
    let x : Fin n → ℝ := fun i => w (Fin.castAdd m i)
    let u : Fin m → ℝ := fun j => w (Fin.natAdd n j)
    have hw : Fin.append x u = w := by
      ext i
      cases i using Fin.addCases with
      | left i => simp [x]
      | right i => simp [u]
    have hset :
        {r : EReal | ∃ z : Fin ((n + m) + m) → ℝ, P z = w ∧ r = objective z} =
          Set.range (fun y : Fin m → ℝ => F₁ x (u - y) + F₂ x y) := by
      ext r
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨projLamLinearMap (n := n + m) (m := m) z, ?_⟩
        simp [objective, A₁, A₂, infimalConvolutionFirstGraphMap,
          infimalConvolutionSecondGraphMap, bifunctionGraphFunction, P, hz, x, u]
        congr 2 <;> funext i <;> rfl
      · rintro ⟨y, rfl⟩
        refine ⟨Fin.append w y, ?_, ?_⟩
        · ext i
          simp [P, projXLinearMap]
        · simp [objective, A₁, A₂, infimalConvolutionFirstGraphMap,
            infimalConvolutionSecondGraphMap, bifunctionGraphFunction, P, x, u,
            projXLinearMap, projLamLinearMap]
          congr 2 <;> funext i <;> rfl
    rw [hset, sInf_range]
    simp [bifunctionGraphFunction, bifunctionInfimalConvolutionInSecond, x, u]
  rw [ConvexBifunction, ← heq]
  exact hfiber

lemma concaveBifunction_of_convexReflection {n m : Nat}
    (G : (Fin n → ℝ) → (Fin m → ℝ) → EReal)
    (hK : ConvexBifunction (convexReflectionOfConcave G)) :
    ConcaveBifunction G := by
  have hpre := convexFunctionOn_precomp_linearMap
    (reflectSecondGraphMap (n := n) (m := m))
    (bifunctionGraphFunction (convexReflectionOfConcave G)) hK
  rw [ConcaveBifunction]
  have heq :
      (fun z : Fin (n + m) → ℝ =>
        bifunctionGraphFunction (convexReflectionOfConcave G) (reflectSecondGraphMap z)) =
      (fun z => -bifunctionGraphFunction G z) := by
    funext z
    simp only [bifunctionGraphFunction, convexReflectionOfConcave, reflectSecondGraphMap,
      LinearMap.coe_mk, AddHom.coe_mk, Fin.append_left, Fin.append_right]
    congr 2
    funext j
    simp
  simpa [heq] using hpre

lemma concaveBifunctionInfimalConvolutionInSecond_concave {n m : Nat}
    (G₁ G₂ : (Fin n → ℝ) → (Fin m → ℝ) → EReal)
    (hG₁ : ProperConcaveBifunction G₁) (hG₂ : ProperConcaveBifunction G₂) :
    ConcaveBifunction (concaveBifunctionInfimalConvolutionInSecond G₁ G₂) := by
  have hK₁ := convexReflectionOfConcave_properConvexBifunction G₁ hG₁
  have hK₂ := convexReflectionOfConcave_properConvexBifunction G₂ hG₂
  have hconv := bifunctionInfimalConvolutionInSecond_convexBifunction
    (convexReflectionOfConcave G₁) (convexReflectionOfConcave G₂) hK₁ hK₂
  have heq :
      convexReflectionOfConcave
          (concaveBifunctionInfimalConvolutionInSecond G₁ G₂) =
        bifunctionInfimalConvolutionInSecond
          (convexReflectionOfConcave G₁) (convexReflectionOfConcave G₂) := by
    funext x u
    exact (infimalConvolution_convexReflection G₁ G₂ x u).symm
  apply concaveBifunction_of_convexReflection
    (concaveBifunctionInfimalConvolutionInSecond G₁ G₂)
  simpa [heq] using hconv

theorem adjointOfConcave_supConvolution_eq_infimalConvolution_adjoint {n m : Nat}
    (G₁ G₂ : (Fin n → ℝ) → (Fin m → ℝ) → EReal)
    (hG₁ : ProperConcaveBifunction G₁) (hG₂ : ProperConcaveBifunction G₂)
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot G₁) ∩
        intrinsicInterior ℝ (bifunctionDomBot G₂)).Nonempty) :
    adjointOfConcaveBifunction
        ⟨concaveBifunctionInfimalConvolutionInSecond G₁ G₂,
          concaveBifunctionInfimalConvolutionInSecond_concave G₁ G₂ hG₁ hG₂⟩ =
      bifunctionInfimalConvolutionInSecond
        (adjointOfConcaveBifunction ⟨G₁, hG₁.1⟩)
        (adjointOfConcaveBifunction ⟨G₂, hG₂.1⟩) := by
  let K₁ := convexReflectionOfConcave G₁
  let K₂ := convexReflectionOfConcave G₂
  have hK₁ : ProperConvexBifunction K₁ :=
    convexReflectionOfConcave_properConvexBifunction G₁ hG₁
  have hK₂ : ProperConvexBifunction K₂ :=
    convexReflectionOfConcave_properConvexBifunction G₂ hG₂
  obtain ⟨K₁pkg, hK₁eq⟩ := fiberwiseProperConvex_of_properConvexBifunction K₁ hK₁
  obtain ⟨K₂pkg, hK₂eq⟩ := fiberwiseProperConvex_of_properConvexBifunction K₂ hK₂
  have hriK :
      (intrinsicInterior ℝ (bifunctionDom K₁pkg.toFun) ∩
        intrinsicInterior ℝ (bifunctionDom K₂pkg.toFun)).Nonempty := by
    simpa [hK₁eq, hK₂eq, K₁, K₂, convexReflectionOfConcave_dom] using hri
  have hthm := bifunctionAdjoint_infimalConvolution_eq_infimalConvolution_adjoint
    K₁pkg K₂pkg (by simpa [hK₁eq] using hK₁.1) (by simpa [hK₂eq] using hK₂.1) hriK
  funext u x
  have hpoint := congrFun (congrFun hthm u) (-x)
  have hKinf :
      bifunctionInfimalConvolution K₁pkg K₂pkg =
        convexReflectionOfConcave
          (concaveBifunctionInfimalConvolutionInSecond G₁ G₂) := by
    funext a b
    change (⨅ y, K₁pkg.toFun a (b - y) + K₂pkg.toFun a y) = _
    rw [hK₁eq, hK₂eq]
    exact infimalConvolution_convexReflection G₁ G₂ a b
  rw [hKinf, textbookBifunctionAdjoint_convexReflection
    (concaveBifunctionInfimalConvolutionInSecond G₁ G₂)
    (concaveBifunctionInfimalConvolutionInSecond_concave G₁ G₂ hG₁ hG₂)] at hpoint
  have hAdj₁ :
      textbookBifunctionAdjoint K₁pkg.toFun =
        convexReflectionOfConcave (adjointOfConcaveBifunction ⟨G₁, hG₁.1⟩) := by
    funext a b
    rw [hK₁eq]
    exact textbookBifunctionAdjoint_convexReflection G₁ hG₁.1 a b
  have hAdj₂ :
      textbookBifunctionAdjoint K₂pkg.toFun =
        convexReflectionOfConcave (adjointOfConcaveBifunction ⟨G₂, hG₂.1⟩) := by
    funext a b
    rw [hK₂eq]
    exact textbookBifunctionAdjoint_convexReflection G₂ hG₂.1 a b
  rw [hAdj₁, hAdj₂] at hpoint
  have hreflect := infimalConvolution_convexReflection
    (convexReflectionOfConcave (adjointOfConcaveBifunction ⟨G₁, hG₁.1⟩))
    (convexReflectionOfConcave (adjointOfConcaveBifunction ⟨G₂, hG₂.1⟩)) u x
  have hdouble₁ :
      convexReflectionOfConcave
          (convexReflectionOfConcave (adjointOfConcaveBifunction ⟨G₁, hG₁.1⟩)) =
        adjointOfConcaveBifunction ⟨G₁, hG₁.1⟩ := by
    funext a b
    simp [convexReflectionOfConcave]
  have hdouble₂ :
      convexReflectionOfConcave
          (convexReflectionOfConcave (adjointOfConcaveBifunction ⟨G₂, hG₂.1⟩)) =
        adjointOfConcaveBifunction ⟨G₂, hG₂.1⟩ := by
    funext a b
    simp [convexReflectionOfConcave]
  rw [hdouble₁, hdouble₂] at hreflect
  have hright :
      concaveBifunctionInfimalConvolutionInSecond
          (convexReflectionOfConcave (adjointOfConcaveBifunction ⟨G₁, hG₁.1⟩))
          (convexReflectionOfConcave (adjointOfConcaveBifunction ⟨G₂, hG₂.1⟩)) u (-x) =
        -bifunctionInfimalConvolutionInSecond
          (adjointOfConcaveBifunction ⟨G₁, hG₁.1⟩)
          (adjointOfConcaveBifunction ⟨G₂, hG₂.1⟩) u x := by
    have h := congrArg Neg.neg hreflect
    simpa using h.symm
  rw [hright] at hpoint
  have h := congrArg Neg.neg hpoint
  simpa using h

/-- The textbook bifunction adjoint agrees with the bundled convex-bifunction adjoint. -/
lemma textbookBifunctionAdjoint_eq_adjointOfConvexBifunction {m n : Nat}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (hF : ConvexBifunction F) :
    textbookBifunctionAdjoint F = adjointOfConvexBifunction ⟨F, hF⟩ := by
  funext x u
  rw [textbookBifunctionAdjoint, adjointOfConvexBifunction, sInf_range,
    iInf_pair_eq_nested]

/-- Corollary 38.2.1: Let `F₁` and `F₂` be closed proper convex bifunctions from `ℝ^m` to
`ℝ^n`. If `ri (dom F₁*)` and `ri (dom F₂*)` have a point in common, then `F₁ □ F₂` is closed
and `(F₁ □ F₂)* = cl (F₁* □ F₂*)`.

The adjoints and the closure on the right are the concave bifunction operations used by the
book, and `ri` is represented by `intrinsicInterior`. -/
theorem bifunctionInfimalConvolution_closed_and_adjoint_eq_closure_infimalConvolution_adjoint
    {m n : Nat} (F₁ F₂ : FiberwiseProperConvexBifunction m n)
    (hproper₁ : ProperConvexBifunction F₁.toFun)
    (hproper₂ : ProperConvexBifunction F₂.toFun)
    (hclosed₁ : ClosedConvexBifunction F₁.toFun)
    (hclosed₂ : ClosedConvexBifunction F₂.toFun)
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (textbookBifunctionAdjoint F₁.toFun)) ∩
        intrinsicInterior ℝ
          (bifunctionDomBot (textbookBifunctionAdjoint F₂.toFun))).Nonempty) :
    ClosedConvexBifunction (bifunctionInfimalConvolution F₁ F₂) ∧
      textbookBifunctionAdjoint (bifunctionInfimalConvolution F₁ F₂) =
        concaveBifunctionClosure
          (concaveBifunctionInfimalConvolutionInSecond
            (textbookBifunctionAdjoint F₁.toFun)
            (textbookBifunctionAdjoint F₂.toFun)) := by
  let G₁ := adjointOfConvexBifunction ⟨F₁.toFun, hproper₁.1⟩
  let G₂ := adjointOfConvexBifunction ⟨F₂.toFun, hproper₂.1⟩
  have hAdj₁ : textbookBifunctionAdjoint F₁.toFun = G₁ :=
    textbookBifunctionAdjoint_eq_adjointOfConvexBifunction F₁.toFun hproper₁.1
  have hAdj₂ : textbookBifunctionAdjoint F₂.toFun = G₂ :=
    textbookBifunctionAdjoint_eq_adjointOfConvexBifunction F₂.toFun hproper₂.1
  have hG₁proper : ProperConcaveBifunction G₁ := by
    exact ((adjoint_bifunction_closure_properness_biconjugation_and_polyhedrality
      (F := F₁.toFun)).1 hproper₁.1).2.1.mpr hproper₁
  have hG₂proper : ProperConcaveBifunction G₂ := by
    exact ((adjoint_bifunction_closure_properness_biconjugation_and_polyhedrality
      (F := F₂.toFun)).1 hproper₂.1).2.1.mpr hproper₂
  have hriG :
      (intrinsicInterior ℝ (bifunctionDomBot G₁) ∩
        intrinsicInterior ℝ (bifunctionDomBot G₂)).Nonempty := by
    simpa [hAdj₁, hAdj₂] using hri
  have hcl₁ := helperForTheorem_6_30_11_convexBifunctionClosure_eq_self_of_closed_proper
    hclosed₁ hproper₁
  have hcl₂ := helperForTheorem_6_30_11_convexBifunctionClosure_eq_self_of_closed_proper
    hclosed₂ hproper₂
  have hBi₁ : biadjointOfConvexBifunction ⟨F₁.toFun, hproper₁.1⟩ = F₁.toFun :=
    ((adjoint_bifunction_closure_properness_biconjugation_and_polyhedrality
      (F := F₁.toFun)).1 hproper₁.1).2.2.2.1 hcl₁
  have hBi₂ : biadjointOfConvexBifunction ⟨F₂.toFun, hproper₂.1⟩ = F₂.toFun :=
    ((adjoint_bifunction_closure_properness_biconjugation_and_polyhedrality
      (F := F₂.toFun)).1 hproper₂.1).2.2.2.1 hcl₂
  let G := concaveBifunctionInfimalConvolutionInSecond G₁ G₂
  have hGconc : ConcaveBifunction G :=
    concaveBifunctionInfimalConvolutionInSecond_concave G₁ G₂ hG₁proper hG₂proper
  have hcore := adjointOfConcave_supConvolution_eq_infimalConvolution_adjoint
    G₁ G₂ hG₁proper hG₂proper hriG
  have hH :
      adjointOfConcaveBifunction ⟨G, hGconc⟩ = bifunctionInfimalConvolution F₁ F₂ := by
    have hAdjBack₁ :
        adjointOfConcaveBifunction ⟨G₁, hG₁proper.1⟩ =
          biadjointOfConvexBifunction ⟨F₁.toFun, hproper₁.1⟩ := by
      rfl
    have hAdjBack₂ :
        adjointOfConcaveBifunction ⟨G₂, hG₂proper.1⟩ =
          biadjointOfConvexBifunction ⟨F₂.toFun, hproper₂.1⟩ := by
      rfl
    rw [hAdjBack₁, hAdjBack₂] at hcore
    rw [hBi₁, hBi₂] at hcore
    simpa [bifunctionInfimalConvolution, bifunctionInfimalConvolutionInSecond, G₁, G₂,
      G, biadjointOfConvexBifunction, adjointOfConvexBifunctionAsConcave] using hcore
  have hclosedH : ClosedConvexBifunction (bifunctionInfimalConvolution F₁ F₂) := by
    have h := adjointOfConcaveBifunction_closedConvex ⟨G, hGconc⟩
    simpa [hH] using h
  refine ⟨hclosedH, ?_⟩
  rw [hAdj₁, hAdj₂]
  rw [textbookBifunctionAdjoint_eq_adjointOfConvexBifunction
    (bifunctionInfimalConvolution F₁ F₂) hclosedH.1]
  have hBiG :=
    ((adjoint_bifunction_closure_properness_biconjugation_and_polyhedrality (F := G)).2
      hGconc).2.2.1
  calc
    adjointOfConvexBifunction ⟨bifunctionInfimalConvolution F₁ F₂, hclosedH.1⟩ =
        biadjointOfConcaveBifunction ⟨G, hGconc⟩ := by
          simpa [biadjointOfConcaveBifunction, adjointOfConcaveBifunctionAsConvex, hH]
    _ = concaveBifunctionClosure G := hBiG
    _ = concaveBifunctionClosure
        (concaveBifunctionInfimalConvolutionInSecond G₁ G₂) := by rfl


/-- A convex bifunction from `ℝ^m` to `ℝ^n`, bundled with the predicate `IsFiberwiseConvexBifunction`. -/
abbrev FiberwiseConvexBifunction (m n : Nat) : Type :=
  {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // IsFiberwiseConvexBifunction F}

/-- Scalar multiplication preserves convexity of bifunctions in the second variable.

-- Proof sketch: Fix `u` and apply convexity of the epigraph of `x ↦ F u x` under the affine change
of variables `x ↦ λ⁻¹ • x` and scaling of function values by the positive scalar `λ`. -/
lemma isFiberwiseConvexBifunction_scalarMultiple {m n : Nat}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (hF : IsFiberwiseConvexBifunction F) (lam : {r : ℝ // 0 < r}) :
    IsFiberwiseConvexBifunction (fun u x => ((lam.1 : ℝ) : EReal) * F u (lam.1⁻¹ • x)) :=
  by
    intro u
    rw [IsERealConvex, ERealEpigraph]
    unfold IsFiberwiseConvexBifunction IsERealConvex at hF
    intro p hp q hq a b ha hb hab
    have hlamE : (0 : EReal) < ((lam.1 : ℝ) : EReal) := by
      exact_mod_cast lam.2
    have hlamTop : ((lam.1 : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
    have hpPre :
        (lam.1⁻¹ • p.1, lam.1⁻¹ * p.2) ∈ ERealEpigraph (F u) := by
      change F u (lam.1⁻¹ • p.1) ≤ ((lam.1⁻¹ * p.2 : ℝ) : EReal)
      rw [EReal.coe_mul, EReal.coe_inv, ← EReal.div_eq_inv_mul]
      rw [EReal.le_div_iff_mul_le hlamE hlamTop]
      simpa [mul_comm] using hp
    have hqPre :
        (lam.1⁻¹ • q.1, lam.1⁻¹ * q.2) ∈ ERealEpigraph (F u) := by
      change F u (lam.1⁻¹ • q.1) ≤ ((lam.1⁻¹ * q.2 : ℝ) : EReal)
      rw [EReal.coe_mul, EReal.coe_inv, ← EReal.div_eq_inv_mul]
      rw [EReal.le_div_iff_mul_le hlamE hlamTop]
      simpa [mul_comm] using hq
    have hcombo := hF u hpPre hqPre ha hb hab
    have hinput :
        a • (lam.1⁻¹ • p.1) + b • (lam.1⁻¹ • q.1) =
          lam.1⁻¹ • (a • p.1 + b • q.1) := by
      ext i
      simp [smul_eq_mul]
      ring
    have hcombo' :
        F u (a • (lam.1⁻¹ • p.1) + b • (lam.1⁻¹ • q.1)) ≤
          ((a * (lam.1⁻¹ * p.2) + b * (lam.1⁻¹ * q.2) : ℝ) : EReal) := by
      simpa [ERealEpigraph, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using hcombo
    have hscaled :=
      mul_le_mul_of_nonneg_left hcombo' (le_of_lt hlamE)
    have hscaleReal :
        lam.1 * (a * (lam.1⁻¹ * p.2) + b * (lam.1⁻¹ * q.2)) =
          a * p.2 + b * q.2 := by
      field_simp [ne_of_gt lam.2]
    have hscaleE :
        ((lam.1 : ℝ) : EReal) *
            ((a * (lam.1⁻¹ * p.2) + b * (lam.1⁻¹ * q.2) : ℝ) : EReal) =
          ((a * p.2 + b * q.2 : ℝ) : EReal) := by
      exact_mod_cast hscaleReal
    change ((lam.1 : ℝ) : EReal) * F u
        (lam.1⁻¹ • (a • p.1 + b • q.1)) ≤
      (((a * p.2 + b * q.2 : ℝ) : EReal))
    rw [← hinput]
    exact hscaled.trans_eq hscaleE

/-- Definition 38.2.2: Let `F` be a convex bifunction from `ℝ^m` to `ℝ^n` (modeled here as a
`FiberwiseConvexBifunction m n`). For any scalar `λ > 0`, the *scalar multiple* `Fλ` is
defined by `(Fλ) u = (F u) λ`, i.e.

`((Fλ) u) x = λ (F u) (λ⁻¹ x)`. -/
noncomputable def bifunctionScalarMultiple {m n : Nat}
    (F : FiberwiseConvexBifunction m n) (lam : {r : ℝ // 0 < r}) :
    FiberwiseConvexBifunction m n :=
  ⟨fun u x => ((lam.1 : ℝ) : EReal) * F.1 u (lam.1⁻¹ • x),
    isFiberwiseConvexBifunction_scalarMultiple F.1 F.2 lam⟩

/-- Convexity of the convex indicator bifunction in its second variable.

-- Proof sketch: For each fixed `u`, the slice `x ↦ convexIndicatorBifunction A u x` is an
indicator of a singleton set, whose epigraph is convex; translate this to the epigraph-based
predicate `IsERealConvex`, and hence to `IsFiberwiseConvexBifunction`. -/
lemma isFiberwiseConvexBifunction_convexIndicatorBifunction {m n : Nat}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    IsFiberwiseConvexBifunction (convexIndicatorBifunction A) :=
  by
    intro u
    rw [IsERealConvex, ERealEpigraph]
    intro p hp q hq a b ha hb hab
    have hpEq : p.1 = A u := by
      by_contra hpNe
      simp [convexIndicatorBifunction, hpNe] at hp
    have hqEq : q.1 = A u := by
      by_contra hqNe
      simp [convexIndicatorBifunction, hqNe] at hq
    have hpHeight : 0 ≤ p.2 := by
      simpa [convexIndicatorBifunction, hpEq] using hp
    have hqHeight : 0 ≤ q.2 := by
      simpa [convexIndicatorBifunction, hqEq] using hq
    have hfirst : a • p.1 + b • q.1 = A u := by
      rw [hpEq, hqEq, ← add_smul, hab, one_smul]
    have hheight : 0 ≤ a * p.2 + b * q.2 := by
      nlinarith
    have hheightE : (0 : EReal) ≤ ((a * p.2 + b * q.2 : ℝ) : EReal) := by
      exact_mod_cast hheight
    simpa [convexIndicatorBifunction, hfirst, Prod.smul_mk, Prod.mk_add_mk,
      smul_eq_mul, EReal.coe_add, EReal.coe_mul] using hheightE

/-- The convex indicator bifunction of a linear map, bundled as a `FiberwiseConvexBifunction`. -/
noncomputable def convexIndicatorFiberwiseConvexBifunction {m n : Nat}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    FiberwiseConvexBifunction m n :=
  ⟨convexIndicatorBifunction A, isFiberwiseConvexBifunction_convexIndicatorBifunction A⟩

/-- Helper for Proposition 38.2.3: the rescaled graph condition is equivalent to membership in
the graph of the scaled linear map. -/
lemma helperForProposition_38_2_3_rescaledGraph_iff {m n : Nat}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (lam : {r : ℝ // 0 < r})
    (u : Fin m → ℝ) (x : Fin n → ℝ) :
    lam.1⁻¹ • x = A u ↔ x = (lam.1 • A) u := by
  constructor
  · intro hx
    -- Multiply the rescaled identity back by `λ` to recover the scaled graph equation.
    have hne : lam.1 ≠ 0 := ne_of_gt lam.2
    calc
      x = lam.1 • (lam.1⁻¹ • x) := (smul_inv_smul₀ hne x).symm
      _ = lam.1 • A u := by rw [hx]
      _ = (lam.1 • A) u := by simp [LinearMap.smul_apply]
  · intro hx
    -- Apply `λ⁻¹` to the scaled graph equation to return to the original graph condition.
    have hne : lam.1 ≠ 0 := ne_of_gt lam.2
    calc
      lam.1⁻¹ • x = lam.1⁻¹ • ((lam.1 • A) u) := by rw [hx]
      _ = lam.1⁻¹ • (lam.1 • A u) := by simp [LinearMap.smul_apply]
      _ = A u := by simpa [smul_smul] using inv_smul_smul₀ hne (A u)

/-- Helper for Proposition 38.2.3: multiplying a `0/⊤`-valued indicator by a positive finite
scalar leaves the indicator unchanged. -/
lemma helperForProposition_38_2_3_positiveScalar_mul_indicator
    (lam : {r : ℝ // 0 < r}) (p : Prop) [Decidable p] :
    ((lam.1 : ℝ) : EReal) * (if p then (0 : EReal) else ⊤) = if p then 0 else ⊤ := by
  by_cases hp : p
  · -- On the true branch the indicator value is `0`, and positive scaling preserves `0`.
    simp [hp]
  · -- On the false branch the indicator value is `⊤`, and a positive finite scalar preserves `⊤`.
    simp [hp, EReal.mul_top_of_pos, lam.2]

/-- Proposition 38.2.3: If `F` is the convex indicator bifunction of a linear transformation
`A : ℝ^m → ℝ^n`, then the scalar multiple `Fλ` (Definition 38.2.2) is the convex indicator
bifunction of the scaled linear transformation `λ A`; equivalently,
`(Fλ) u = δ(· | { (λ A) u })`.

-- Proof sketch: Unfold `bifunctionScalarMultiple` and `convexIndicatorBifunction`. For each `u`,
the expression `x ↦ λ * (if λ⁻¹ • x = A u then 0 else +∞)` is `0` exactly when
`x = (λ • A) u` and `+∞` otherwise; rewrite `λ⁻¹ • x = A u` as `x = λ • A u`. -/
theorem bifunctionScalarMultiple_convexIndicatorBifunction {m n : Nat}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (lam : {r : ℝ // 0 < r}) :
    (bifunctionScalarMultiple (convexIndicatorFiberwiseConvexBifunction A) lam).1 =
      convexIndicatorBifunction (lam.1 • A) :=
  by
    funext u x
    -- Reduce the statement to the pointwise comparison of two `0/⊤`-valued indicator formulas.
    change ((lam.1 : ℝ) : EReal) * (if lam.1⁻¹ • x = A u then (0 : EReal) else ⊤) =
      if x = (lam.1 • A) u then 0 else ⊤
    rw [helperForProposition_38_2_3_positiveScalar_mul_indicator lam (lam.1⁻¹ • x = A u)]
    -- Rewrite the rescaled graph test into the graph condition for the scaled linear map.
    simp [helperForProposition_38_2_3_rescaledGraph_iff A lam u x]

/-- Scalar multiplication of a raw bifunction in its second variable:
`(Fλ) u x = λ * F u (λ⁻¹ • x)` (with `λ > 0` encoded by `lam : {r : ℝ // 0 < r}`). -/
noncomputable def bifunctionScalarMultipleInSecond
    {U X : Type*} [SMul ℝ X] (F : U → X → EReal) (lam : {r : ℝ // 0 < r}) : U → X → EReal :=
  fun u x => ((lam.1 : ℝ) : EReal) * F u (lam.1⁻¹ • x)

/-- Helper for Theorem 38.3: multiplication by a fixed positive finite scalar is continuous on
`EReal`. -/
lemma helperForTheorem_38_3_positiveScalarMul_continuous (lam : {r : ℝ // 0 < r}) :
    Continuous fun z : EReal => ((lam.1 : ℝ) : EReal) * z := by
  -- Reduce continuity of the unary map `z ↦ λ z` to continuity of multiplication on `EReal`.
  refine continuous_iff_continuousAt.2 ?_
  intro z
  have hneZero : ((lam.1 : ℝ) : EReal) ≠ 0 := by
    exact_mod_cast (ne_of_gt lam.2)
  have hneBot : ((lam.1 : ℝ) : EReal) ≠ ⊥ := by
    simp
  have hneTop : ((lam.1 : ℝ) : EReal) ≠ ⊤ := by
    simp
  have hmul :
      ContinuousAt (fun p : EReal × EReal => p.1 * p.2) (((lam.1 : ℝ) : EReal), z) :=
    EReal.continuousAt_mul (p := (((lam.1 : ℝ) : EReal), z))
      (Or.inl hneZero) (Or.inl hneZero) (Or.inl hneBot) (Or.inl hneTop)
  simpa [Function.comp] using
    hmul.comp ((Continuous.prodMk continuous_const continuous_id).continuousAt)

/-- Helper for Theorem 38.3: postcomposing a lower-semicontinuous `EReal`-valued function with
positive scalar multiplication preserves lower semicontinuity. -/
lemma helperForTheorem_38_3_positiveScalarMul_lowerSemicontinuous
    {α : Type*} [TopologicalSpace α] (lam : {r : ℝ // 0 < r}) (f : α → EReal)
    (hf : LowerSemicontinuous f) :
    LowerSemicontinuous (fun x => ((lam.1 : ℝ) : EReal) * f x) := by
  -- Compose the lower-semicontinuous map with the continuous monotone map `z ↦ λ z`.
  have hcont := helperForTheorem_38_3_positiveScalarMul_continuous lam
  have hmono : Monotone fun z : EReal => ((lam.1 : ℝ) : EReal) * z := by
    intro x y hxy
    exact mul_le_mul_of_nonneg_left hxy (by exact_mod_cast lam.2.le)
  simpa [Function.comp] using hcont.comp_lowerSemicontinuous hf hmono

/-- Helper for Theorem 38.3: multiplying a finite real term and an `EReal` term by a positive
scalar distributes over their sum. -/
lemma helperForTheorem_38_3_positiveScalar_mul_finiteAdd (lam : {r : ℝ // 0 < r})
    (r : ℝ) (z : EReal) :
    (((lam.1 * r : ℝ)) : EReal) + ((lam.1 : ℝ) : EReal) * z =
      ((lam.1 : ℝ) : EReal) * (((r : ℝ) : EReal) + z) := by
  -- Split on the extended-real term so the exceptional `⊥/⊤` arithmetic is explicit.
  cases z using EReal.rec with
  | bot =>
      rw [show (((r : ℝ) : EReal) + (⊥ : EReal)) = (⊥ : EReal) by simp]
      have hleft : (((lam.1 * r : ℝ)) : EReal) + (⊥ : EReal) = (⊥ : EReal) := by
        simp
      simpa [EReal.coe_mul_bot_of_pos lam.2] using hleft
  | coe x =>
      exact_mod_cast (show lam.1 * r + lam.1 * x = lam.1 * (r + x) by ring)
  | top =>
      rw [show (((r : ℝ) : EReal) + (⊤ : EReal)) = (⊤ : EReal) by
        exact EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
      rw [EReal.coe_mul_top_of_pos lam.2]
      exact EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)

/-- Helper for Theorem 38.3: multiplying a non-`⊥` `EReal` value by a positive finite scalar
cannot produce `⊥`. -/
lemma helperForTheorem_38_3_positiveScalar_mul_ne_bot (lam : {r : ℝ // 0 < r}) {z : EReal}
    (hz : z ≠ ⊥) :
    ((lam.1 : ℝ) : EReal) * z ≠ ⊥ := by
  intro hbot
  rw [EReal.mul_eq_bot] at hbot
  rcases hbot with hleft | hright | htop | hneg
  · exact (by simp : ((lam.1 : ℝ) : EReal) ≠ ⊥) hleft.1
  · exact hz hright.2
  · exact (by simp : ((lam.1 : ℝ) : EReal) ≠ ⊤) htop.1
  · exact (show ¬ (((lam.1 : ℝ) : EReal) < 0) by
        exact_mod_cast (not_lt_of_gt lam.2)) hneg.1

/-- Helper for Theorem 38.3: multiplying a non-`⊤` `EReal` value by a positive finite scalar
cannot produce `⊤`. -/
lemma helperForTheorem_38_3_positiveScalar_mul_ne_top (lam : {r : ℝ // 0 < r}) {z : EReal}
    (hz : z ≠ ⊤) :
    ((lam.1 : ℝ) : EReal) * z ≠ ⊤ := by
  intro htop
  rw [EReal.mul_eq_top] at htop
  rcases htop with hbot | hneg | hleft | hright
  · exact (by simp : ((lam.1 : ℝ) : EReal) ≠ ⊥) hbot.1
  · exact (show ¬ (((lam.1 : ℝ) : EReal) < 0) by
        exact_mod_cast (not_lt_of_gt lam.2)) hneg.1
  · exact (by simp : ((lam.1 : ℝ) : EReal) ≠ ⊤) hleft.1
  · exact hz hright.2

/-- Helper for Theorem 38.3: multiplying by a fixed positive finite scalar commutes with `iInf`
in `EReal`. -/
lemma helperForTheorem_38_3_positiveScalar_mul_iInf {ι : Sort*}
    (lam : {r : ℝ // 0 < r}) (f : ι → EReal) :
    ((lam.1 : ℝ) : EReal) * (⨅ i, f i) = ⨅ i, ((lam.1 : ℝ) : EReal) * f i := by
  -- Transport the infimum across the order isomorphism `z ↦ λ z`.
  let leftMul : EReal →o EReal :=
    { toFun := fun z => ((lam.1 : ℝ) : EReal) * z
      monotone' := fun _ _ h =>
        mul_le_mul_of_nonneg_left h (by exact_mod_cast lam.2.le) }
  let leftMulInv : EReal →o EReal :=
    { toFun := fun z => (((lam.1⁻¹ : ℝ) : EReal)) * z
      monotone' := fun _ _ h =>
        mul_le_mul_of_nonneg_left h (by exact_mod_cast (inv_nonneg.mpr lam.2.le)) }
  have hInvLeft : ((((lam.1⁻¹ : ℝ) : EReal)) * ((lam.1 : ℝ) : EReal)) = 1 := by
    rw [← EReal.coe_mul, inv_mul_cancel₀ (ne_of_gt lam.2), EReal.coe_one]
  have hInvRight : (((lam.1 : ℝ) : EReal) * (((lam.1⁻¹ : ℝ) : EReal))) = 1 := by
    rw [← EReal.coe_mul, mul_inv_cancel₀ (ne_of_gt lam.2), EReal.coe_one]
  let mulIso : EReal ≃o EReal :=
    OrderIso.ofHomInv leftMul leftMulInv
      (by
        ext z
        calc
          ((lam.1 : ℝ) : EReal) * ((((lam.1⁻¹ : ℝ) : EReal) * z)) =
              ((((lam.1 : ℝ) : EReal) * (((lam.1⁻¹ : ℝ) : EReal))) * z) := by
                rw [mul_assoc]
          _ = z := by rw [hInvRight, one_mul])
      (by
        ext z
        calc
          (((lam.1⁻¹ : ℝ) : EReal) * (((lam.1 : ℝ) : EReal) * z)) =
              (((((lam.1⁻¹ : ℝ) : EReal) * ((lam.1 : ℝ) : EReal))) * z) := by
                rw [← mul_assoc]
          _ = z := by rw [hInvLeft, one_mul])
  change mulIso (⨅ i, f i) = ⨅ i, mulIso (f i)
  exact mulIso.map_iInf f

/-- Helper for Theorem 38.3: scaling by `λ` and then by `λ⁻¹` returns the original bifunction. -/
lemma helperForTheorem_38_3_scalarMultiple_reciprocal_cancel {m n : Nat}
    (F : FiberwiseConvexBifunction m n) (lam : {r : ℝ // 0 < r}) :
    let lamInv : {r : ℝ // 0 < r} := ⟨lam.1⁻¹, inv_pos.mpr lam.2⟩
    (bifunctionScalarMultiple (bifunctionScalarMultiple F lam) lamInv).1 = F.1 := by
  -- Evaluate the double scaling pointwise and cancel both the coefficient and the rescaling.
  let lamInv : {r : ℝ // 0 < r} := ⟨lam.1⁻¹, inv_pos.mpr lam.2⟩
  funext u x
  have hmul :
      (((lam.1⁻¹ : ℝ) : EReal) * (((lam.1 : ℝ) : EReal) * F.1 u x)) = F.1 u x := by
    rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ (ne_of_gt lam.2), EReal.coe_one, one_mul]
  simpa [bifunctionScalarMultiple, lamInv, smul_smul, inv_mul_cancel₀ (ne_of_gt lam.2)] using hmul

/-- Helper for Theorem 38.3: properness on the product is preserved by positive rescaling in the
second variable. -/
lemma helperForTheorem_38_3_proper_scalarMultiple_forward {m n : Nat}
    (F : FiberwiseConvexBifunction m n) (lam : {r : ℝ // 0 < r})
    (hproper : IsProperEReal (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F.1 p.1 p.2)) :
    IsProperEReal
      (fun p : (Fin m → ℝ) × (Fin n → ℝ) => (bifunctionScalarMultiple F lam).1 p.1 p.2) := by
  rcases hproper with ⟨hnoBot, ⟨p, hnotTop⟩⟩
  constructor
  · -- Positive scalar multiplication cannot create a `⊥` value from a non-`⊥` witness.
    intro p
    exact helperForTheorem_38_3_positiveScalar_mul_ne_bot lam
      (hnoBot (p.1, lam.1⁻¹ • p.2))
  · -- The original finite witness survives after rescaling the second argument by `λ`.
    refine ⟨(p.1, lam.1 • p.2), ?_⟩
    simpa [bifunctionScalarMultiple, smul_smul, mul_assoc, inv_mul_cancel₀ (ne_of_gt lam.2)] using
      (helperForTheorem_38_3_positiveScalar_mul_ne_top lam hnotTop)

/-- Helper for Theorem 38.3: product lower semicontinuity is preserved by positive rescaling in
the second variable. -/
lemma helperForTheorem_38_3_productLowerSemicontinuous_scalarMultiple_forward {m n : Nat}
    (F : FiberwiseConvexBifunction m n) (lam : {r : ℝ // 0 < r})
    (hclosed : IsProductLowerSemicontinuousBifunction F.1) :
    IsProductLowerSemicontinuousBifunction (bifunctionScalarMultiple F lam).1 := by
  -- First precompose with the continuous rescaling `(u, x) ↦ (u, λ⁻¹ • x)`.
  have hpre :
      Continuous
        (fun p : (Fin m → ℝ) × (Fin n → ℝ) => (p.1, lam.1⁻¹ • p.2)) := by
    exact continuous_fst.prodMk ((continuous_const_smul (lam.1⁻¹ : ℝ)).comp continuous_snd)
  have hinner :
      LowerSemicontinuous
        (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F.1 p.1 (lam.1⁻¹ • p.2)) := by
    simpa [Function.comp, IsProductLowerSemicontinuousBifunction] using
      hclosed.comp_continuous hpre
  -- Then multiply the resulting lower-semicontinuous product function by the positive scalar `λ`.
  simpa [IsProductLowerSemicontinuousBifunction, bifunctionScalarMultiple] using
    helperForTheorem_38_3_positiveScalarMul_lowerSemicontinuous lam
      (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F.1 p.1 (lam.1⁻¹ • p.2)) hinner

/-- Helper for Theorem 38.3: the `iInf`-based left pairing scales by the same positive factor as
the bifunction itself. -/
lemma helperForTheorem_38_3_leftPairing_scalarMultiple {m n : Nat}
    (F : FiberwiseConvexBifunction m n) (lam : {r : ℝ // 0 < r})
    (u : Fin m → ℝ) (xStar : Module.Dual ℝ (Fin n → ℝ)) :
    bifunctionLeftPairing (bifunctionScalarMultiple F lam).1 u xStar =
      ((lam.1 : ℝ) : EReal) * bifunctionLeftPairing F.1 u xStar := by
  let e : (Fin n → ℝ) ≃ (Fin n → ℝ) :=
    (LinearEquiv.smulOfNeZero ℝ (Fin n → ℝ) lam.1 (ne_of_gt lam.2)).symm.toEquiv
  -- Reindex the infimum by the bijection `x = λ • y`.
  rw [bifunctionLeftPairing]
  calc
    (⨅ x : Fin n → ℝ,
        ((xStar x : ℝ) : EReal) + ((lam.1 : ℝ) : EReal) * F.1 u (lam.1⁻¹ • x)) =
      ⨅ y : Fin n → ℝ,
        ((lam.1 : ℝ) : EReal) * (((xStar y : ℝ) : EReal) + F.1 u y) := by
          refine Equiv.iInf_congr e ?_
          intro x
          have he : e x = lam.1⁻¹ • x := by
            rfl
          have hlin : xStar (e x) = lam.1⁻¹ * xStar x := by
            rw [he]
            simp [smul_eq_mul]
          rw [hlin, he]
          rw [← helperForTheorem_38_3_positiveScalar_mul_finiteAdd lam (lam.1⁻¹ * xStar x)
            (F.1 u (lam.1⁻¹ • x))]
          have hcancel :
              (((lam.1 * (lam.1⁻¹ * xStar x) : ℝ)) : EReal) = ((xStar x : ℝ) : EReal) := by
            exact_mod_cast (show lam.1 * (lam.1⁻¹ * xStar x) = xStar x by
              field_simp [show lam.1 ≠ 0 by exact ne_of_gt lam.2])
          rw [hcancel]
    _ = ((lam.1 : ℝ) : EReal) * (⨅ y : Fin n → ℝ, ((xStar y : ℝ) : EReal) + F.1 u y) := by
          symm
          exact helperForTheorem_38_3_positiveScalar_mul_iInf lam
            (fun y : Fin n → ℝ => ((xStar y : ℝ) : EReal) + F.1 u y)

/-- Helper for Theorem 38.3: the adjoint of the scaled bifunction is the corresponding positive
scalar multiple in the second dual variable. -/
lemma helperForTheorem_38_3_adjoint_scalarMultiple {m n : Nat}
    (F : FiberwiseConvexBifunction m n) (lam : {r : ℝ // 0 < r}) :
    bifunctionAdjoint (bifunctionScalarMultiple F lam).1 =
      bifunctionScalarMultipleInSecond (bifunctionAdjoint F.1) lam := by
  let e : (Fin n → ℝ) ≃ (Fin n → ℝ) :=
    (LinearEquiv.smulOfNeZero ℝ (Fin n → ℝ) lam.1 (ne_of_gt lam.2)).symm.toEquiv
  funext xStar uStar
  rw [bifunctionAdjoint, bifunctionScalarMultipleInSecond, bifunctionAdjoint]
  calc
    (⨅ (u : Fin m → ℝ) (x : Fin n → ℝ),
        ((xStar x : ℝ) : EReal) + (-((uStar u : ℝ) : EReal)) +
          ((lam.1 : ℝ) : EReal) * F.1 u (lam.1⁻¹ • x)) =
      ⨅ (u : Fin m → ℝ) (y : Fin n → ℝ),
        ((lam.1 : ℝ) : EReal) * (((xStar y : ℝ) : EReal) + F.1 u y) +
          (-((uStar u : ℝ) : EReal)) := by
          refine iInf_congr ?_
          intro u
          refine Equiv.iInf_congr e ?_
          intro x
          have he : e x = lam.1⁻¹ • x := by
            rfl
          have hlin : xStar (e x) = lam.1⁻¹ * xStar x := by
            rw [he]
            simp [smul_eq_mul]
          rw [hlin, he]
          rw [← helperForTheorem_38_3_positiveScalar_mul_finiteAdd lam (lam.1⁻¹ * xStar x)
            (F.1 u (lam.1⁻¹ • x))]
          have hcancel :
              (((lam.1 * (lam.1⁻¹ * xStar x) : ℝ)) : EReal) = ((xStar x : ℝ) : EReal) := by
            exact_mod_cast (show lam.1 * (lam.1⁻¹ * xStar x) = xStar x by
              field_simp [show lam.1 ≠ 0 by exact ne_of_gt lam.2])
          rw [hcancel]
          simpa [add_assoc, add_comm, add_left_comm]
    _ = ⨅ (u : Fin m → ℝ) (y : Fin n → ℝ),
          ((lam.1 : ℝ) : EReal) *
            (((xStar y : ℝ) : EReal) + (-((((lam.1⁻¹ • uStar) u)) : EReal)) + F.1 u y) := by
          refine iInf_congr ?_
          intro u
          refine iInf_congr ?_
          intro y
          have hne : lam.1 ≠ 0 := ne_of_gt lam.2
          have hneg : (-((uStar u : ℝ) : EReal)) = (((-(uStar u) : ℝ)) : EReal) := by
            simp
          have hsub :
              (((xStar y - ((lam.1⁻¹ • uStar) u) : ℝ) : ℝ) : EReal) =
                ((xStar y : ℝ) : EReal) + (-((((lam.1⁻¹ • uStar) u)) : EReal)) := by
            exact_mod_cast (sub_eq_add_neg (xStar y) ((lam.1⁻¹ • uStar) u))
          have hreal : xStar (lam.1 • y) - uStar u =
              lam.1 * (xStar y - ((lam.1⁻¹ • uStar) u)) := by
            have hu : ((lam.1⁻¹ • uStar) u) = lam.1⁻¹ * uStar u := by
              simp
            rw [show xStar (lam.1 • y) = lam.1 * xStar y by simp, hu]
            ring_nf
            field_simp [hne]
          have hreal' : xStar (lam.1 • y) + -uStar u =
              lam.1 * (xStar y - ((lam.1⁻¹ • uStar) u)) := by
            simpa [sub_eq_add_neg] using hreal
          have hterm :
              ((lam.1 : ℝ) : EReal) * (((xStar y : ℝ) : EReal) + F.1 u y) +
                  (-((uStar u : ℝ) : EReal)) =
                ((lam.1 : ℝ) : EReal) *
                  (((xStar y : ℝ) : EReal) + (-((((lam.1⁻¹ • uStar) u)) : EReal)) + F.1 u y) := by
            have hu : ((lam.1⁻¹ • uStar) u) = lam.1⁻¹ * uStar u := by
              simp
            have hcoef :
                (((lam.1 * (-( (lam.1⁻¹ • uStar) u)) : ℝ)) : EReal) =
                  (-((uStar u : ℝ) : EReal)) := by
              rw [hu]
              exact_mod_cast (show lam.1 * (-(lam.1⁻¹ * uStar u)) = -uStar u by
                field_simp [show lam.1 ≠ 0 by exact ne_of_gt lam.2])
            have hscaled :=
              helperForTheorem_38_3_positiveScalar_mul_finiteAdd lam
                (-((lam.1⁻¹ • uStar) u))
                ((((xStar y : ℝ) : EReal) + F.1 u y))
            rw [hcoef] at hscaled
            simpa [add_assoc, add_left_comm, add_comm] using hscaled
          exact hterm
    _ = ((lam.1 : ℝ) : EReal) *
          (⨅ (u : Fin m → ℝ) (y : Fin n → ℝ),
            ((xStar y : ℝ) : EReal) + (-((((lam.1⁻¹ • uStar) u)) : EReal)) + F.1 u y) := by
          symm
          rw [helperForTheorem_38_3_positiveScalar_mul_iInf lam
              (fun u : Fin m → ℝ =>
                ⨅ y : Fin n → ℝ,
                  ((xStar y : ℝ) : EReal) + (-((((lam.1⁻¹ • uStar) u)) : EReal)) + F.1 u y)]
          refine iInf_congr ?_
          intro u
          exact helperForTheorem_38_3_positiveScalar_mul_iInf lam
            (fun y : Fin n → ℝ =>
              ((xStar y : ℝ) : EReal) + (-((((lam.1⁻¹ • uStar) u)) : EReal)) + F.1 u y)

-- Proof sketch: Convexity is already bundled into `bifunctionScalarMultiple`. Closedness follows
-- from stability of lower semicontinuity under composition with continuous maps and multiplication
-- by a positive scalar. Properness is preserved because scaling by `λ > 0` and precomposing by a
-- bijective linear rescaling in `x` neither introduces `-∞` nor makes the function identically
-- `+∞`. The pairing identity is a change-of-variables in an `iInf` using linearity of the
-- evaluation `xStar` and positivity of `λ`. The adjoint identity is the standard conjugation rule
-- `(fλ)^* = f^*λ` applied in the bifunction setting via `bifunctionAdjoint`.
/-- Theorem 38.3: Let `F` be a convex bifunction from `ℝ^m` to `ℝ^n`, and let `λ > 0`. Then `Fλ`
is a convex bifunction; it is closed (resp. proper) if and only if `F` is closed (resp. proper);
and for all `u` and `x*` one has `⟨(Fλ) u, x*⟩ = λ ⟨F u, x*⟩`. Moreover `(Fλ)^* = F^*λ`. -/
theorem bifunctionScalarMultiple_closed_iff_and_proper_iff_and_leftPairing_and_adjoint {m n : Nat}
    (F : FiberwiseConvexBifunction m n) (lam : {r : ℝ // 0 < r}) :
    IsFiberwiseConvexBifunction (bifunctionScalarMultiple F lam).1 ∧
      (IsProductLowerSemicontinuousBifunction (bifunctionScalarMultiple F lam).1 ↔
        IsProductLowerSemicontinuousBifunction F.1) ∧
      (IsProperEReal (fun p : (Fin m → ℝ) × (Fin n → ℝ) => (bifunctionScalarMultiple F lam).1 p.1 p.2) ↔
          IsProperEReal (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F.1 p.1 p.2)) ∧
      (∀ (u : Fin m → ℝ) (xStar : Module.Dual ℝ (Fin n → ℝ)),
          bifunctionLeftPairing (bifunctionScalarMultiple F lam).1 u xStar =
            ((lam.1 : ℝ) : EReal) * bifunctionLeftPairing F.1 u xStar) ∧
      bifunctionAdjoint (bifunctionScalarMultiple F lam).1 =
        bifunctionScalarMultipleInSecond (bifunctionAdjoint F.1) lam :=
  by
    let lamInv : {r : ℝ // 0 < r} := ⟨lam.1⁻¹, inv_pos.mpr lam.2⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- Convexity is already bundled into the definition of `bifunctionScalarMultiple`.
      exact (bifunctionScalarMultiple F lam).2
    · -- Closedness is transported forward, and the reverse implication follows by cancelling the
      -- rescaling with `λ⁻¹`.
      constructor
      · intro hscaled
        have hback :
            IsProductLowerSemicontinuousBifunction
              (bifunctionScalarMultiple (bifunctionScalarMultiple F lam) lamInv).1 :=
          helperForTheorem_38_3_productLowerSemicontinuous_scalarMultiple_forward
            (bifunctionScalarMultiple F lam) lamInv hscaled
        have hcancel :
            (bifunctionScalarMultiple (bifunctionScalarMultiple F lam) lamInv).1 = F.1 := by
          simpa [lamInv] using
            helperForTheorem_38_3_scalarMultiple_reciprocal_cancel F lam
        simpa [hcancel] using hback
      · exact
          helperForTheorem_38_3_productLowerSemicontinuous_scalarMultiple_forward F lam
    · -- Properness is handled by the same forward transport and reciprocal cancellation.
      constructor
      · intro hproper
        have hback :
            IsProperEReal
              (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
                (bifunctionScalarMultiple (bifunctionScalarMultiple F lam) lamInv).1 p.1 p.2) :=
          helperForTheorem_38_3_proper_scalarMultiple_forward
            (bifunctionScalarMultiple F lam) lamInv hproper
        have hcancel :
            (bifunctionScalarMultiple (bifunctionScalarMultiple F lam) lamInv).1 = F.1 := by
          simpa [lamInv] using
            helperForTheorem_38_3_scalarMultiple_reciprocal_cancel F lam
        simpa [hcancel] using hback
      · intro hproper
        exact helperForTheorem_38_3_proper_scalarMultiple_forward F lam hproper
    · -- The pairing identity is the reindexed `iInf` computation proved above.
      intro u xStar
      exact helperForTheorem_38_3_leftPairing_scalarMultiple F lam u xStar
    · -- The adjoint identity is the same reindexing argument with the extra dual linear term.
      exact helperForTheorem_38_3_adjoint_scalarMultiple F lam

/-- Definition 38.3.1: Let `F` be a proper convex bifunction from `ℝ^m` to `ℝ^n` (here modeled as
`F : FiberwiseProperConvexBifunction m n`, i.e. an `EReal`-valued bifunction on `Fin m → ℝ` and `Fin n → ℝ`
that is globally proper and convex in the second variable). Given a convex function
`f : ℝ^m → EReal` which never takes the value `-∞`, the *image* `Ff` is the function on `ℝ^n`
defined by

`(Ff) x = inf_u (f u + (F u) x)`,

modeled in Lean as an `iInf` over `u : Fin m → ℝ`. Equivalently, `(Ff) x = inf (f - F_* x)` where
`F_*` is the inverse `bifunctionInverse F.toFun`. -/
noncomputable def bifunctionImage {m n : Nat} (F : FiberwiseProperConvexBifunction m n)
    (f : {f : (Fin m → ℝ) → EReal // IsERealConvex f ∧ (∀ u, f u ≠ (⊥ : EReal))}) :
    (Fin n → ℝ) → EReal :=
  fun x => ⨅ u : (Fin m → ℝ), f.1 u + F.toFun u x

/-- The image of a function `f : ℝ^m → EReal` under a linear map `A : ℝ^m → ℝ^n`, defined by
`(Af)(x) = inf { f(u) | A u = x }`, modeled as an `iInf` with an indicator (`+∞`) for the
constraint `A u = x`. -/
noncomputable def linearMapImage {m n : Nat}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (f : (Fin m → ℝ) → EReal) :
    (Fin n → ℝ) → EReal :=
  fun x =>
    letI : DecidableEq (Fin n → ℝ) := Classical.decEq _
    ⨅ u : (Fin m → ℝ), if A u = x then f u else ⊤

-- Proof sketch: Unfold `bifunctionImage` and rewrite `F.toFun` using the hypothesis that `F` is
-- the convex indicator bifunction of `A`. Then, for each `u`, the summand
-- `f u + (if x = A u then 0 else +∞)` collapses to `f u` when `A u = x` and to `+∞` otherwise;
-- the assumption that `f` never takes the value `-∞` rules out the `(-∞) + (+∞)` convention of
-- `EReal` interfering with this reduction.
/-- Helper for Proposition 38.3.2: the convex-indicator summand collapses to the constrained
linear-image integrand. -/
lemma helperForProposition_38_3_2_convexIndicatorSummand_eq_linearImageTerm {m n : Nat}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (f : (Fin m → ℝ) → EReal)
    (u : Fin m → ℝ) (x : Fin n → ℝ) (hf : f u ≠ (⊥ : EReal)) :
    f u + convexIndicatorBifunction A u x = if A u = x then f u else ⊤ := by
  -- Split according to whether `x` lies on the graph of `A` at `u`.
  by_cases hgraph : A u = x
  · -- On the graph, the indicator contributes `0`, so the summand is just `f u`.
    rw [convexIndicatorBifunction, if_pos hgraph.symm, if_pos hgraph]
    simp
  · -- Off the graph, the indicator contributes `⊤`, and `hf` rules out the undefined `⊥ + ⊤`.
    have hx : x ≠ A u := by simpa [eq_comm] using hgraph
    rw [convexIndicatorBifunction, if_neg hx, if_neg hgraph]
    exact EReal.add_top_of_ne_bot hf

/-- Helper for Proposition 38.3.2: after rewriting by the convex indicator bifunction, the whole
integrand agrees pointwise with the constrained infimum integrand defining `Af`. -/
lemma helperForProposition_38_3_2_integrand_eq {m n : Nat}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (f : {f : (Fin m → ℝ) → EReal // IsERealConvex f ∧ (∀ u, f u ≠ (⊥ : EReal))})
    (x : Fin n → ℝ) :
    (fun u : Fin m → ℝ => f.1 u + convexIndicatorBifunction A u x) =
      fun u => if A u = x then f.1 u else ⊤ := by
  -- Promote the pointwise summand identity to an equality of functions under the infimum.
  funext u
  exact helperForProposition_38_3_2_convexIndicatorSummand_eq_linearImageTerm A f.1 u x (f.2.2 u)

/-- Proposition 38.3.2: If `F` is the convex indicator bifunction of a linear transformation
`A : ℝ^m → ℝ^n`, then for any convex function `f` on `ℝ^m` that does not take on `-∞`, the image
`Ff` coincides with the image `Af` defined by `(Af)(x) = inf { f(u) | A u = x }`. -/
theorem bifunctionImage_convexIndicatorBifunction_eq_linearMapImage {m n : Nat}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (F : FiberwiseProperConvexBifunction m n)
    (hF : F.toFun = convexIndicatorBifunction A)
    (f : {f : (Fin m → ℝ) → EReal // IsERealConvex f ∧ (∀ u, f u ≠ (⊥ : EReal))}) :
    bifunctionImage F f = linearMapImage A f.1 := by
  classical
  -- Compare the two image constructions pointwise in the target variable `x`.
  funext x
  letI : DecidableEq (Fin n → ℝ) := Classical.decEq _
  -- Unfold both definitions so the proof reduces to identifying the infimum integrands.
  rw [bifunctionImage, linearMapImage]
  -- Rewrite `F` by the convex indicator bifunction and collapse each summand pointwise.
  rw [hF]
  -- Show each infimum is bounded by every term of the other integrand, using the summand helper.
  apply le_antisymm
  · refine le_iInf ?_
    intro u
    refine le_trans (iInf_le (fun v : Fin m → ℝ => f.1 v + convexIndicatorBifunction A v x) u) ?_
    rw [helperForProposition_38_3_2_convexIndicatorSummand_eq_linearImageTerm A f.1 u x (f.2.2 u)]
    by_cases hgraph : A u = x
    · simp [hgraph]
    · simp [hgraph]
  · refine le_iInf ?_
    intro u
    refine le_trans (iInf_le (fun v : Fin m → ℝ => if A v = x then f.1 v else ⊤) u) ?_
    -- Resolve the constrained term by the same graph/off-graph split used in the helper lemma.
    by_cases hgraph : A u = x
    · -- On the graph, the indicator term is `0`, so the constrained value matches the summand.
      have hx : x = A u := hgraph.symm
      rw [if_pos hgraph]
      rw [convexIndicatorBifunction, if_pos hx]
      simp
    · -- Off the graph, the constrained value is `⊤`, and the summand is also `⊤`.
      have hx : x ≠ A u := by simpa [eq_comm] using hgraph
      have htop : f.1 u + convexIndicatorBifunction A u x = (⊤ : EReal) := by
        rw [convexIndicatorBifunction, if_neg hx]
        exact EReal.add_top_of_ne_bot (f.2.2 u)
      rw [if_neg hgraph, htop]

/-- The Fenchel conjugate `f*` of an `EReal`-valued function `f : X → EReal`, defined on the
algebraic dual by `f*(x*) = sup_x (⟨x, x*⟩ - f x)` where `⟨x, x*⟩` is evaluation. -/
noncomputable def fenchelConjugateDual
    {X : Type*} [AddCommMonoid X] [Module ℝ X] (f : X → EReal) :
    Module.Dual ℝ X → EReal :=
  fun xStar =>
    sSup (Set.range (fun x : X => ((xStar x : ℝ) : EReal) - f x))

/-- The image `Ff` of a function `f` under a bifunction `F`, defined by
`(Ff)(x) = inf_u (f u + F u x)` (modeled by `iInf`). -/
noncomputable def bifunctionImageRaw
    {U X : Type*} (F : U → X → EReal) (f : U → EReal) : X → EReal :=
  fun x => ⨅ u : U, f u + F u x

/-- Helper for Theorem 38.4: the image of the constant-zero function under the identity graph
indicator bifunction is still the constant-zero function. -/
lemma helperForTheorem_38_4_identityImage_constZero_eq_constZero :
    bifunctionImageRaw
        (convexIndicatorBifunction
          (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)))
        (fun _ : Fin 1 → ℝ => (0 : EReal)) =
      fun _ : Fin 1 → ℝ => (0 : EReal) := by
  funext x
  apply le_antisymm
  · -- The graph point `u = x` realizes the value `0` in the defining infimum.
    refine le_trans (iInf_le _ x) ?_
    simp [bifunctionImageRaw, convexIndicatorBifunction]
  · -- Every summand is either `0` on the graph or `⊤` off the graph, so the infimum stays above `0`.
    rw [bifunctionImageRaw]
    refine le_iInf ?_
    intro u
    by_cases hxu : x = u
    · simp [convexIndicatorBifunction, hxu]
    · simp [convexIndicatorBifunction, hxu]

/-- Helper for Theorem 38.4: the constant-zero function has conjugate value `0` at the dual
origin. -/
lemma helperForTheorem_38_4_constZero_conjugateAtZero_eq_zero :
    fenchelConjugateDual (fun _ : Fin 1 → ℝ => (0 : EReal))
      (0 : Module.Dual ℝ (Fin 1 → ℝ)) = 0 := by
  unfold fenchelConjugateDual
  apply le_antisymm
  · -- Every value in the defining supremum is already `0` at the dual origin.
    refine sSup_le ?_
    rintro _ ⟨x, rfl⟩
    simp
  · -- The primal point `x = 0` contributes the value `0`, so the supremum is at least `0`.
    exact le_sSup ⟨(0 : Fin 1 → ℝ), by simp⟩

/-- Helper for Theorem 38.4: the left-hand side of the advertised conjugacy formula evaluates to
`0` at the dual origin for the identity/constant-zero specialization. -/
lemma helperForTheorem_38_4_identityLeftSideAtZero_eq_zero :
    fenchelConjugateDual
        (bifunctionImageRaw
          (convexIndicatorBifunction
            (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)))
          (fun _ : Fin 1 → ℝ => (0 : EReal)))
        (0 : Module.Dual ℝ (Fin 1 → ℝ)) = 0 := by
  -- Replace the primal image by the constant-zero function and evaluate its conjugate at `0`.
  rw [helperForTheorem_38_4_identityImage_constZero_eq_constZero]
  exact helperForTheorem_38_4_constZero_conjugateAtZero_eq_zero

/-- Helper for Theorem 38.4: the identity/constant-zero specialization satisfies the relative
interior qualification hypothesis appearing in the theorem statement. -/
lemma helperForTheorem_38_4_identityQualification :
    (intrinsicInterior ℝ
          (erealDom (fun _ : Fin 1 → ℝ => (0 : EReal))) ∩
        intrinsicInterior ℝ
          (bifunctionDom
            (convexIndicatorBifunction
              (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))))).Nonempty := by
  have hDomf :
      erealDom (fun _ : Fin 1 → ℝ => (0 : EReal)) = (Set.univ : Set (Fin 1 → ℝ)) := by
    ext u
    simp [erealDom]
  have hDomF :
      bifunctionDom
          (convexIndicatorBifunction
            (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))) =
        (Set.univ : Set (Fin 1 → ℝ)) := by
    ext u
    constructor
    · intro _
      simp
    · intro _
      refine ⟨u, ?_⟩
      simp [convexIndicatorBifunction]
  refine ⟨0, ?_⟩
  constructor
  · -- The constant-zero function is finite everywhere, so any point lies in the intrinsic interior.
    rw [hDomf]
    exact
      interior_subset_intrinsicInterior
        (by simp : (0 : Fin 1 → ℝ) ∈ interior (Set.univ : Set (Fin 1 → ℝ)))
  · -- The identity graph indicator has full `u`-domain because each `u` lies on its own graph point.
    rw [hDomF]
    exact
      interior_subset_intrinsicInterior
        (by simp : (0 : Fin 1 → ℝ) ∈ interior (Set.univ : Set (Fin 1 → ℝ)))

/-- Helper for Theorem 38.4: on the identity/constant-zero specialization, the right-hand side of
the advertised conjugacy formula evaluates to `⊥` at the dual origin. -/
lemma helperForTheorem_38_4_identityRightSideAtZero_eq_bot :
    bifunctionImageRaw
        (bifunctionAdjoint
          (bifunctionInverse
            (convexIndicatorBifunction
              (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)))))
        (fenchelConjugateDual (fun _ : Fin 1 → ℝ => (0 : EReal)))
        (0 : Module.Dual ℝ (Fin 1 → ℝ)) = ⊥ := by
  have hAdjointAtZero :
      bifunctionAdjoint
          (bifunctionInverse
            (convexIndicatorBifunction
              (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))))
          (0 : Module.Dual ℝ (Fin 1 → ℝ))
          (0 : Module.Dual ℝ (Fin 1 → ℝ)) = ⊥ := by
    -- Rewrite the inverse graph indicator to the previously analyzed concave indicator model.
    have hInverse :
        bifunctionInverse
            (convexIndicatorBifunction
              (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))) =
          concaveIndicatorBifunctionLinear
            (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)) := by
      simpa using
        helperForProposition_38_0_3_inverse_eq_concaveIndicator
          (LinearEquiv.refl ℝ (Fin 1 → ℝ))
    rw [hInverse]
    exact helperForProposition_38_0_3_identityOneDim_adjointAtZero_eq_bot
  rw [bifunctionImageRaw]
  apply le_antisymm
  · -- The dual witness `uStar = 0` already contributes `⊥`, forcing the whole infimum to be `⊥`.
    refine le_trans (iInf_le _ (0 : Module.Dual ℝ (Fin 1 → ℝ))) ?_
    rw [helperForTheorem_38_4_constZero_conjugateAtZero_eq_zero, hAdjointAtZero]
    simp
  · -- `⊥` is the global lower bound in `EReal`.
    exact bot_le

/-- Helper for Theorem 38.4: the equality clause in the current theorem statement is already false
for the identity graph indicator and the constant-zero function. -/
lemma helperForTheorem_38_4_identitySpecialization_conjugateClauseFalse :
    ¬ ((intrinsicInterior ℝ
            (erealDom (fun _ : Fin 1 → ℝ => (0 : EReal))) ∩
          intrinsicInterior ℝ
            (bifunctionDom
              (convexIndicatorBifunction
                (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))))).Nonempty →
        fenchelConjugateDual
            (bifunctionImageRaw
              (convexIndicatorBifunction
                (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)))
              (fun _ : Fin 1 → ℝ => (0 : EReal))) =
          bifunctionImageRaw
            (bifunctionAdjoint
              (bifunctionInverse
                (convexIndicatorBifunction
                  (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)))))
            (fenchelConjugateDual (fun _ : Fin 1 → ℝ => (0 : EReal)))) := by
  intro hSpecialized
  -- Evaluate the specialized equality at the dual origin and compare the explicit values `0` and `⊥`.
  have hAtZero :=
    congrFun
      (hSpecialized helperForTheorem_38_4_identityQualification)
      (0 : Module.Dual ℝ (Fin 1 → ℝ))
  rw [helperForTheorem_38_4_identityLeftSideAtZero_eq_zero,
    helperForTheorem_38_4_identityRightSideAtZero_eq_bot] at hAtZero
  exact EReal.zero_ne_bot hAtZero

/-- Helper for Theorem 38.4: the full specialized implication is false because its equality clause
already fails at the dual origin. -/
lemma helperForTheorem_38_4_identitySpecialization_targetFalse :
    ¬ ((intrinsicInterior ℝ
            (erealDom (fun _ : Fin 1 → ℝ => (0 : EReal))) ∩
          intrinsicInterior ℝ
            (bifunctionDom
              (convexIndicatorBifunction
                (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))))).Nonempty →
        fenchelConjugateDual
            (bifunctionImageRaw
              (convexIndicatorBifunction
                (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)))
              (fun _ : Fin 1 → ℝ => (0 : EReal))) =
          bifunctionImageRaw
            (bifunctionAdjoint
              (bifunctionInverse
                (convexIndicatorBifunction
                  (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)))))
            (fenchelConjugateDual (fun _ : Fin 1 → ℝ => (0 : EReal))) ∧
        ∀ xStar : Module.Dual ℝ (Fin 1 → ℝ),
          ∃ uStar : Module.Dual ℝ (Fin 1 → ℝ),
            bifunctionImageRaw
                (bifunctionAdjoint
                  (bifunctionInverse
                    (convexIndicatorBifunction
                      (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)))))
                (fenchelConjugateDual (fun _ : Fin 1 → ℝ => (0 : EReal)))
                xStar =
              fenchelConjugateDual (fun _ : Fin 1 → ℝ => (0 : EReal)) uStar +
                (bifunctionAdjoint
                  (bifunctionInverse
                    (convexIndicatorBifunction
                      (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)))))
                  uStar xStar) := by
  intro hSpecialized
  -- Forget the attainment clause and contradict the equality clause proved impossible above.
  exact
    helperForTheorem_38_4_identitySpecialization_conjugateClauseFalse
      (fun hri => (hSpecialized hri).1)

end Section38
end Chap08

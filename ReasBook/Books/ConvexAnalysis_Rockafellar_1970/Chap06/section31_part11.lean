/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section29_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part10

open scoped Topology

section Chap06
section Section31

attribute [local instance] Classical.propDecidable

/-- Helper for Lemma 31.0.9: at `x⋆ = 0`, each summand in the dual perturbation value function
is exactly the dual concave objective evaluated at the same `u⋆`. -/
lemma helperForLemma_31_0_9_zeroSliceIntegrand_eq_dualObjective {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (uStar : Fin m → ℝ) :
    fenchelConjugate n f ((0 : Fin n → ℝ) - fenchelCoordinateAdjointApply A uStar) -
        concaveFenchelConjugate g (-uStar) =
      fenchelDualConcaveObjective A f g uStar := by
  -- At the zero slice, the shifted argument `0 - A⋆ u⋆` is exactly the argument used by the
  -- dual objective.
  simp [fenchelDualConcaveObjective]

/-- Helper for Lemma 31.0.9: evaluating the dual perturbation value function at `x⋆ = 0`
recovers the displayed supremum of the dual objective. -/
lemma helperForLemma_31_0_9_dualValueAtZero_eq_dualSup {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal) :
    fenchelDualPerturbationValueFunction A f g (0 : Fin n → ℝ) =
      ⨆ uStar : Fin m → ℝ, fenchelDualConcaveObjective A f g uStar := by
  -- Expand the value function at the zero shift.
  rw [fenchelDualPerturbationValueFunction]
  let zeroSlice : (Fin m → ℝ) → EReal := fun uStar =>
    fenchelConjugate n f ((0 : Fin n → ℝ) - fenchelCoordinateAdjointApply A uStar) -
      concaveFenchelConjugate g (-uStar)
  have hZeroSlice :
      zeroSlice = fenchelDualConcaveObjective A f g := by
    -- Identify the whole zero-slice integrand with the dual objective pointwise in `u⋆`.
    funext uStar
    exact helperForLemma_31_0_9_zeroSliceIntegrand_eq_dualObjective
      (A := A) (f := f) (g := g) uStar
  -- Rewrite the supremum after naming the zero-slice function explicitly.
  change (⨆ uStar : Fin m → ℝ, zeroSlice uStar) =
    ⨆ uStar : Fin m → ℝ, fenchelDualConcaveObjective A f g uStar
  rw [hZeroSlice]

/-- Helper for Lemma 31.0.9: strong consistency of `(P*)` is exactly the stated relative-interior
witness condition. -/
lemma helperForLemma_31_0_9_dualStrongConsistency_iff_unfolded {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal) :
    FenchelDualProgramStronglyConsistent A f g ↔
      ∃ uStar : Fin m → ℝ,
        uStar ∈ euclideanRelativeInterior_fin m (concaveConjugateEffectiveDomain g) ∧
          fenchelCoordinateAdjointApply A uStar ∈
            euclideanRelativeInterior_fin n
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) := by
  -- Unfold the program predicate to expose the witness formula verbatim.
  simp [FenchelDualProgramStronglyConsistent]

/-- Helper for Lemma 31.0.9: the full textbook conclusion is already encoded by the Section 31
definitions, so the proof reduces to the two basic definitional rewrites above. -/
lemma helperForLemma_31_0_9_statement_is_definitional {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal) :
    (⨆ uStar : Fin m → ℝ, fenchelDualConcaveObjective A f g uStar) =
        fenchelDualPerturbationValueFunction A f g (0 : Fin n → ℝ) ∧
      (FenchelDualProgramStronglyConsistent A f g ↔
        ∃ uStar : Fin m → ℝ,
          uStar ∈ euclideanRelativeInterior_fin m (concaveConjugateEffectiveDomain g) ∧
            fenchelCoordinateAdjointApply A uStar ∈
              euclideanRelativeInterior_fin n
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))) := by
  -- Split the book statement into the optimal-value identity and the strong-consistency witness
  -- condition.
  constructor
  · -- The optimal dual value is the zero-slice identity from the perturbation value function.
    simpa using
      (helperForLemma_31_0_9_dualValueAtZero_eq_dualSup (A := A) (f := f) (g := g)).symm
  · -- The strong-consistency clause is exactly the predicate unfolded.
    simpa using
      helperForLemma_31_0_9_dualStrongConsistency_iff_unfolded (A := A) (f := f) (g := g)

/-- Lemma 31.0.9 (Optimal Value and Strong Consistency of Dual Concave Program `(P*)`): let
`f : ℝ^n → ℝ ∪ {+∞}` be proper convex, let `g : ℝ^m → ℝ ∪ {-∞}` be proper concave, and let
`A : ℝ^n → ℝ^m` be linear. Then the optimal value of the dual concave program `(P*)` is
`sup F⋆ 0 = sup_uStar φ(uStar)` for the dual objective
`φ(uStar) = f⋆(-A⋆ uStar) - g⋆(-uStar)`, and `(P*)` is strongly consistent iff there
exists `uStar ∈ ri (dom g⋆)` such that `A⋆ uStar ∈ ri (dom f⋆)`. -/
lemma fenchel_dualProgram_optimalValue_and_strongConsistency {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g) :
    (⨆ uStar : Fin m → ℝ, fenchelDualConcaveObjective A f g uStar) =
        fenchelDualPerturbationValueFunction A f g (0 : Fin n → ℝ) ∧
      (FenchelDualProgramStronglyConsistent A f g ↔
        ∃ uStar : Fin m → ℝ,
          uStar ∈ euclideanRelativeInterior_fin m (concaveConjugateEffectiveDomain g) ∧
            fenchelCoordinateAdjointApply A uStar ∈
              euclideanRelativeInterior_fin n
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))) := by
  -- Route correction: the old counterexample route attacked a stale formulation, but the current
  -- imported API makes both conjuncts direct definitional consequences.
  let _ := hf
  let _ := hg
  -- The textbook hypotheses stay in the statement, but the actual Lean content is the packaged
  -- definitional conjunction above.
  simpa using
    helperForLemma_31_0_9_statement_is_definitional (A := A) (f := f) (g := g)

/-- The translated perturbation value function `u ↦ inf_x (f x - g (x + u))`. -/
noncomputable def translatedDifferenceValueFunction {n : ℕ}
    (f g : (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  fun u => functionInfimumEReal (fun x => f x - g (x + u))

/-- Helper for Lemma 31.0.10: a nonnegative scalar distributes across the translated
difference when it is viewed as an `EReal` sum with a negated term. -/
lemma helperForLemma_31_0_10_nonnegScalar_mul_translatedDifference {n : ℕ}
    (f g : (Fin n → ℝ) → EReal) {a : ℝ} (ha : 0 ≤ a)
    (u x : Fin n → ℝ) :
    ((a : ℝ) : EReal) * (f x - g (x + u)) =
      ((a : ℝ) : EReal) * f x + ((a : ℝ) : EReal) * (-(g (x + u))) := by
  -- Convert the translated difference into an `EReal` sum and use left distributivity for a
  -- nonnegative coefficient.
  have haE_nonneg : (0 : EReal) ≤ ((a : ℝ) : EReal) := by
    exact_mod_cast ha
  have haE_ne_top : ((a : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top a
  simpa [sub_eq_add_neg] using
    (EReal.left_distrib_of_nonneg_of_ne_top haE_nonneg haE_ne_top
      (f x) (-(g (x + u))))

/-- Helper for Lemma 31.0.10: convex-combining two translated arguments splits into the
convex combination of the base points plus the convex combination of the translation vectors. -/
lemma helperForLemma_31_0_10_translatedArgument_convexCombination {n : ℕ}
    (p q : (Fin n → ℝ) × (Fin n → ℝ)) (a b : ℝ) :
    a • (p.2 + p.1) + b • (q.2 + q.1) =
      (a • p.2 + b • q.2) + (a • p.1 + b • q.1) := by
  -- Compare coordinates and separate the translated argument into its `x` and `u` pieces.
  ext i
  simp [smul_add]
  ring

/-- Helper for Theorem 31.2: the translated perturbation `(u, x) ↦ f x - g (x + u)` is a convex
bifunction in the Section 29 sense. -/
lemma helperForTheorem_31_2_translatedDifference_isConvexBifunction {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g) :
    IsConvexBifunction (fun u x => f x - g (x + u)) := by
  -- Rewrite convexity of `f` and `-g` as the finite Jensen inequalities used for a bifunction.
  have hfJensen :=
    (convexFunctionOn_univ_iff_jensen_inequality (f := f)
      (hnotbot := by
        intro x
        exact hf.2.2 x (by simp))).1 hf.1
  have hNegJensen :=
    (convexFunctionOn_univ_iff_jensen_inequality (f := fun y : Fin n → ℝ => -(g y))
      (hnotbot := by
        intro y
        exact hg.2.2 y (by simp))).1 hg.1
  intro p q a b ha hb hab
  let w : Fin 2 → ℝ := fun i => if i = 0 then a else b
  let xData : Fin 2 → Fin n → ℝ := fun i => if i = 0 then p.2 else q.2
  let yData : Fin 2 → Fin n → ℝ := fun i => if i = 0 then p.2 + p.1 else q.2 + q.1
  have hw : ∀ i : Fin 2, 0 ≤ w i := by
    intro i
    fin_cases i <;> simp [w, ha, hb]
  have hsumWeights : (∑ i : Fin 2, w i) = 1 := by
    simp [w, Fin.sum_univ_two, hab]
  have hfx :
      f (a • p.2 + b • q.2) ≤
        ((a : ℝ) : EReal) * f p.2 + ((b : ℝ) : EReal) * f q.2 := by
    -- Apply Jensen to the `x`-coordinates of the two graph points.
    simpa [w, xData, Fin.sum_univ_two] using hfJensen 2 w xData hw hsumWeights
  have hnegG :
      -(g (a • (p.2 + p.1) + b • (q.2 + q.1))) ≤
        ((a : ℝ) : EReal) * (-(g (p.2 + p.1))) +
          ((b : ℝ) : EReal) * (-(g (q.2 + q.1))) := by
    -- Apply the same Jensen step to the translated arguments of `g`.
    simpa [w, yData, Fin.sum_univ_two] using hNegJensen 2 w yData hw hsumWeights
  have hdistA :
      ((a : ℝ) : EReal) * (f p.2 - g (p.2 + p.1)) =
        ((a : ℝ) : EReal) * f p.2 + ((a : ℝ) : EReal) * (-(g (p.2 + p.1))) := by
    -- Reuse the translated-difference scalar distribution lemma on the first graph value.
    simpa using
      helperForLemma_31_0_10_nonnegScalar_mul_translatedDifference
        (f := f) (g := g) (a := a) ha p.1 p.2
  have hdistB :
      ((b : ℝ) : EReal) * (f q.2 - g (q.2 + q.1)) =
        ((b : ℝ) : EReal) * f q.2 + ((b : ℝ) : EReal) * (-(g (q.2 + q.1))) := by
    -- The second graph value is handled by the same reusable scalar-distribution lemma.
    simpa using
      helperForLemma_31_0_10_nonnegScalar_mul_translatedDifference
        (f := f) (g := g) (a := b) hb q.1 q.2
  have hsum :
      f (a • p.2 + b • q.2) + -(g (a • (p.2 + p.1) + b • (q.2 + q.1))) ≤
        (((a : ℝ) : EReal) * f p.2 + ((b : ℝ) : EReal) * f q.2) +
          (((a : ℝ) : EReal) * (-(g (p.2 + p.1))) +
            ((b : ℝ) : EReal) * (-(g (q.2 + q.1)))) := by
    -- Summing the two Jensen inequalities gives the required graph-function upper bound.
    exact add_le_add hfx hnegG
  have hsumGrouped :
      f (a • p.2 + b • q.2) + -(g (a • (p.2 + p.1) + b • (q.2 + q.1))) ≤
        (((a : ℝ) : EReal) * f p.2 + ((a : ℝ) : EReal) * (-(g (p.2 + p.1)))) +
          (((b : ℝ) : EReal) * f q.2 + ((b : ℝ) : EReal) * (-(g (q.2 + q.1)))) := by
    -- Reassociate the right-hand side so each coefficient sees one complete graph value.
    simpa [add_assoc, add_left_comm, add_comm] using hsum
  have hsumDistributed :
      f (a • p.2 + b • q.2) + -(g (a • (p.2 + p.1) + b • (q.2 + q.1))) ≤
        ((a : ℝ) : EReal) * (f p.2 - g (p.2 + p.1)) +
          ((b : ℝ) : EReal) * (f q.2 - g (q.2 + q.1)) := by
    -- Replace each grouped pair of terms by the corresponding scaled graph value.
    calc
      f (a • p.2 + b • q.2) + -(g (a • (p.2 + p.1) + b • (q.2 + q.1))) ≤
          (((a : ℝ) : EReal) * f p.2 + ((a : ℝ) : EReal) * (-(g (p.2 + p.1)))) +
            (((b : ℝ) : EReal) * f q.2 + ((b : ℝ) : EReal) * (-(g (q.2 + q.1)))) :=
        hsumGrouped
      _ = ((a : ℝ) : EReal) * (f p.2 - g (p.2 + p.1)) +
            ((b : ℝ) : EReal) * (f q.2 - g (q.2 + q.1)) := by
          rw [← hdistA, ← hdistB]
  have htranslated :
      a • (p.2 + p.1) + b • (q.2 + q.1) =
        (a • p.2 + b • q.2) + (a • p.1 + b • q.1) :=
    helperForLemma_31_0_10_translatedArgument_convexCombination p q a b
  -- Rewrite the translated argument into the graph-function form expected by Section 29.
  rw [htranslated] at hsumDistributed
  -- Simplify the combined inequality back to the displayed bifunction graph convexity statement.
  simpa [graphFunction, sub_eq_add_neg] using
    hsumDistributed

/-- Helper for Theorem 31.2: bundling the translated perturbation lets Section 29 treat
`(u, x) ↦ f x - g (x + u)` as a generalized convex bifunction. -/
noncomputable def helperForTheorem_31_2_translatedDifference_bifunction {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g) :
    BundledConvexBifunction n n :=
  ⟨fun u x => f x - g (x + u),
    helperForTheorem_31_2_translatedDifference_isConvexBifunction f g hf hg⟩

/-- Helper for Lemma 31.0.10: at each parameter `u`, the translated value function agrees
with the Section 29 perturbation value of the bundled translated bifunction. -/
lemma helperForLemma_31_0_10_translatedDifferenceValue_eq_generalizedPerturbation_apply
    {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (u : Fin n → ℝ) :
    translatedDifferenceValueFunction f g u =
      generalizedConvexProgramPerturbationFunction
        (helperForTheorem_31_2_translatedDifference_bifunction f g hf hg) u := by
  -- Unfold both value functions at the same perturbation parameter `u`.
  simp [translatedDifferenceValueFunction, generalizedConvexProgramPerturbationFunction,
    generalizedConvexProgramPerturbation, generalizedConvexProgram,
    helperForTheorem_31_2_translatedDifference_bifunction, functionInfimumEReal, sInf_range]

/-- Helper for Theorem 31.2: the translated value function is exactly the generalized
perturbation function of the bundled translated bifunction. -/
lemma helperForTheorem_31_2_translatedDifferenceValue_eq_generalizedPerturbation {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g) :
    translatedDifferenceValueFunction f g =
      generalizedConvexProgramPerturbationFunction
        (helperForTheorem_31_2_translatedDifference_bifunction f g hf hg) := by
  -- Promote the pointwise perturbation-value identification to a function equality.
  funext u
  simpa using
    helperForLemma_31_0_10_translatedDifferenceValue_eq_generalizedPerturbation_apply
      (f := f) (g := g) (hf := hf) (hg := hg) u

/-- Helper for Lemma 31.0.10: Section 29 gives convexity for the generalized perturbation
attached to the translated bifunction. -/
lemma helperForLemma_31_0_10_generalizedPerturbation_convex {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g) :
    ConvexFunction
      (generalizedConvexProgramPerturbationFunction
        (helperForTheorem_31_2_translatedDifference_bifunction f g hf hg)) := by
  -- The bundled translated bifunction is exactly the kind of object handled by the Section 29
  -- perturbation theorem.
  exact
    (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker
      (helperForTheorem_31_2_translatedDifference_bifunction f g hf hg)).1

/-- Helper for Theorem 31.2: Section 29 already proves convexity of the translated value function
at the epigraph level. -/
lemma helperForTheorem_31_2_translatedDifferenceValue_convexFunction {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g) :
    ConvexFunction (translatedDifferenceValueFunction f g) := by
  -- First obtain convexity of the bundled perturbation from Section 29.
  have hconv := helperForLemma_31_0_10_generalizedPerturbation_convex f g hf hg
  -- Then rewrite that bundled perturbation back to the textbook translated value function.
  simpa [helperForTheorem_31_2_translatedDifferenceValue_eq_generalizedPerturbation f g hf hg]
    using hconv

/-- Lemma 31.0.10: the translated difference value function is convex. -/
lemma translatedDifferenceValueFunction_convex {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g) :
    ConvexFunction (translatedDifferenceValueFunction f g) := by
  -- Route correction: the book's convexity claim is the epigraph-based notion `ConvexFunction`;
  -- the stronger Jensen predicate `ConvexERealFunction` would require an extra no-`⊥`
  -- hypothesis that can fail for perturbation value functions.
  exact helperForTheorem_31_2_translatedDifferenceValue_convexFunction f g hf hg

/-- Helper for Theorem 31.2: the arithmetic needed to recover the tail index in `Fin (m + n)`. -/
lemma helperForTheorem_31_2_sub_lt_of_le
    {m n : ℕ} (i : Fin (m + n)) (hge : m ≤ i.1) :
    i.1 - m < n := by
  -- This is the standard bound `m ≤ i < m + n → i - m < n`.
  omega

/-- Helper for Theorem 31.2: projecting a packed vector onto its `u` block. -/
def helperForTheorem_31_2_packedUProjection {n m : ℕ} :
    (Fin (m + n) → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
  { toFun := fun z i => z (Fin.castAdd n i)
    map_add' := by
      intro z w
      ext i
      rfl
    map_smul' := by
      intro c z
      ext i
      rfl }

/-- Helper for Theorem 31.2: projecting a packed vector onto its `x` block. -/
def helperForTheorem_31_2_packedXProjection {n m : ℕ} :
    (Fin (m + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  { toFun := fun z j => z (Fin.natAdd m j)
    map_add' := by
      intro z w
      ext j
      rfl
    map_smul' := by
      intro c z
      ext j
      rfl }

/-- Helper for Theorem 31.2: the packed affine map `z ↦ A x + u`. -/
def helperForTheorem_31_2_packedAffineMap {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    (Fin (m + n) → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
  A.comp (helperForTheorem_31_2_packedXProjection (n := n) (m := m)) +
    helperForTheorem_31_2_packedUProjection (n := n) (m := m)

/-- Helper for Theorem 31.2: the packed convex part `z ↦ f x`. -/
def helperForTheorem_31_2_packedConvexPart {n m : ℕ}
    (f : (Fin n → ℝ) → EReal) :
    (Fin (m + n) → ℝ) → EReal :=
  fun z => f ((helperForTheorem_31_2_packedXProjection (n := n) (m := m)) z)

/-- Helper for Theorem 31.2: the packed negated concave part `z ↦ -g (A x + u)`. -/
def helperForTheorem_31_2_packedConcaveNegPart {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (g : (Fin m → ℝ) → EReal) :
    (Fin (m + n) → ℝ) → EReal :=
  fun z => -(g ((helperForTheorem_31_2_packedAffineMap (n := n) (m := m) A) z))

/-- Helper for Theorem 31.2: the perturbation viewed on packed coordinates. -/
def helperForTheorem_31_2_packedPerturbation {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal) :
    (Fin (m + n) → ℝ) → EReal :=
  fun z =>
    helperForTheorem_31_2_packedConvexPart (n := n) (m := m) f z +
      helperForTheorem_31_2_packedConcaveNegPart (n := n) (m := m) A g z

/-- Helper for Theorem 31.2: blockwise weighted combinations commute with `Fin.append`. -/
lemma helperForTheorem_31_2_append_weighted
    {m n : ℕ} (a b : ℝ) (u₁ u₂ : Fin m → ℝ) (x₁ x₂ : Fin n → ℝ) :
    a • Fin.append u₁ x₁ + b • Fin.append u₂ x₂ =
      Fin.append (a • u₁ + b • u₂) (a • x₁ + b • x₂) := by
  -- Compare the `u` and `x` coordinate blocks separately.
  funext i
  by_cases hi : i.1 < m
  · let i' : Fin m := ⟨i.1, hi⟩
    have hiCast : Fin.castAdd n i' = i := by
      ext
      simp [i']
    rw [← hiCast]
    simp [Fin.append, Fin.addCases]
  · have hge : m ≤ i.1 := Nat.le_of_not_gt hi
    let j : Fin n := ⟨i.1 - m, helperForTheorem_31_2_sub_lt_of_le (m := m) (n := n) i hge⟩
    have hjNatAdd : Fin.natAdd m j = i := by
      ext
      simp [j]
      omega
    rw [← hjNatAdd]
    simp [Fin.append, Fin.addCases]

/-- Helper for Theorem 31.2: the packed convex part remains proper convex. -/
lemma helperForTheorem_31_2_packedConvexPart_properConvex {n m : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
      (helperForTheorem_31_2_packedConvexPart (n := n) (m := m) f) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Convexity is preserved by the coordinate projection onto the `x` block.
    exact convexFunctionOn_precomp_linearMap
      (A := helperForTheorem_31_2_packedXProjection (n := n) (m := m)) f hf.1
  · rcases hf.2.1 with ⟨p0, hp0⟩
    have hp0' : f p0.1 ≤ (p0.2 : EReal) :=
      (mem_epigraph_univ_iff (f := f)).1 hp0
    have hx0 :
        helperForTheorem_31_2_packedXProjection (n := n) (m := m)
          (Fin.append (0 : Fin m → ℝ) p0.1) = p0.1 := by
      ext j
      simp [helperForTheorem_31_2_packedXProjection]
    -- Appending a zero `u` block preserves the same finite epigraph witness.
    refine ⟨(Fin.append (0 : Fin m → ℝ) p0.1, p0.2), ?_⟩
    exact (mem_epigraph_univ_iff
      (f := helperForTheorem_31_2_packedConvexPart (n := n) (m := m) f)).2
      (by simpa [helperForTheorem_31_2_packedConvexPart, hx0] using hp0')
  · -- Properness excludes `⊥` at every packed point.
    intro z hz
    exact hf.2.2
      ((helperForTheorem_31_2_packedXProjection (n := n) (m := m)) z) (by simp)

/-- Helper for Theorem 31.2: the packed negated concave part is proper convex. -/
lemma helperForTheorem_31_2_packedConcaveNegPart_properConvex {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (g : (Fin m → ℝ) → EReal)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g) :
    ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
      (helperForTheorem_31_2_packedConcaveNegPart (n := n) (m := m) A g) := by
  refine ⟨?_, ?_, ?_⟩
  · -- This is the linear preimage of the proper convex function `-g`.
    exact convexFunctionOn_precomp_linearMap
      (A := helperForTheorem_31_2_packedAffineMap (n := n) (m := m) A)
      (fun y => -(g y)) hg.1
  · rcases hg.2.1 with ⟨p0, hp0⟩
    have hp0' : -(g p0.1) ≤ (p0.2 : EReal) :=
      (mem_epigraph_univ_iff (f := fun y => -(g y))).1 hp0
    have hx0 :
        helperForTheorem_31_2_packedXProjection (n := n) (m := m)
          (Fin.append p0.1 (0 : Fin n → ℝ)) = 0 := by
      ext j
      simp [helperForTheorem_31_2_packedXProjection]
    have hux0 :
        helperForTheorem_31_2_packedAffineMap (n := n) (m := m) A
          (Fin.append p0.1 (0 : Fin n → ℝ)) = p0.1 := by
      -- Choosing `x = 0` and `u = p0.1` hits the same finite value of `-g`.
      calc
        helperForTheorem_31_2_packedAffineMap (n := n) (m := m) A
            (Fin.append p0.1 (0 : Fin n → ℝ))
            = A
                (helperForTheorem_31_2_packedXProjection (n := n) (m := m)
                  (Fin.append p0.1 (0 : Fin n → ℝ))) +
              helperForTheorem_31_2_packedUProjection (n := n) (m := m)
                (Fin.append p0.1 (0 : Fin n → ℝ)) := by
                  rfl
        _ = A 0 + helperForTheorem_31_2_packedUProjection (n := n) (m := m)
              (Fin.append p0.1 (0 : Fin n → ℝ)) := by rw [hx0]
        _ = p0.1 := by
            ext i
            simp [helperForTheorem_31_2_packedUProjection, A.map_zero]
    refine ⟨(Fin.append p0.1 (0 : Fin n → ℝ), p0.2), ?_⟩
    exact (mem_epigraph_univ_iff
      (f := helperForTheorem_31_2_packedConcaveNegPart (n := n) (m := m) A g)).2
      (by simpa [helperForTheorem_31_2_packedConcaveNegPart, hux0] using hp0')
  · -- The pulled-back `-g` term never hits `⊥`.
    intro z hz
    exact hg.2.2
      ((helperForTheorem_31_2_packedAffineMap (n := n) (m := m) A) z) (by simp)

/-- Helper for Theorem 31.2: appending `(u, x)` and then projecting to the `u` block recovers
`u`. -/
lemma helperForTheorem_31_2_packedUProjection_append {n m : ℕ}
    (u : Fin m → ℝ) (x : Fin n → ℝ) :
    helperForTheorem_31_2_packedUProjection (n := n) (m := m) (Fin.append u x) = u := by
  -- The first block of `Fin.append u x` is definitionally the `u`-coordinates.
  ext i
  simp [helperForTheorem_31_2_packedUProjection]

/-- Helper for Theorem 31.2: appending `(u, x)` and then projecting to the `x` block recovers
`x`. -/
lemma helperForTheorem_31_2_packedXProjection_append {n m : ℕ}
    (u : Fin m → ℝ) (x : Fin n → ℝ) :
    helperForTheorem_31_2_packedXProjection (n := n) (m := m) (Fin.append u x) = x := by
  -- The tail block of `Fin.append u x` is definitionally the `x`-coordinates.
  ext j
  simp [helperForTheorem_31_2_packedXProjection]

/-- Helper for Theorem 31.2: the packed affine map evaluated on `Fin.append u x` gives the
textbook argument `A x + u`. -/
lemma helperForTheorem_31_2_packedAffineMap_append {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (u : Fin m → ℝ) (x : Fin n → ℝ) :
    helperForTheorem_31_2_packedAffineMap (n := n) (m := m) A (Fin.append u x) = A x + u := by
  -- Unfold the packed affine map and replace each block projection by its recovered coordinate.
  calc
    helperForTheorem_31_2_packedAffineMap (n := n) (m := m) A (Fin.append u x)
        = A (helperForTheorem_31_2_packedXProjection (n := n) (m := m) (Fin.append u x)) +
            helperForTheorem_31_2_packedUProjection (n := n) (m := m) (Fin.append u x) := by
              rfl
    _ = A x + u := by
          rw [helperForTheorem_31_2_packedXProjection_append (n := n) (m := m) u x,
            helperForTheorem_31_2_packedUProjection_append (n := n) (m := m) u x]

/-- Helper for Theorem 31.2: evaluating the packed perturbation at `Fin.append u x` recovers the
original perturbation value. -/
lemma helperForTheorem_31_2_packedPerturbation_append {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (u : Fin m → ℝ) (x : Fin n → ℝ) :
    helperForTheorem_31_2_packedPerturbation (n := n) (m := m) A f g (Fin.append u x) =
      fenchelPerturbationFunction A f g (u, x) := by
  have hu :=
    helperForTheorem_31_2_packedUProjection_append (n := n) (m := m) u x
  have hx :=
    helperForTheorem_31_2_packedXProjection_append (n := n) (m := m) u x
  have hux :=
    helperForTheorem_31_2_packedAffineMap_append (n := n) (m := m) A u x
  -- Unfold the packed definition and replace the block projections by `u` and `x`.
  simp [helperForTheorem_31_2_packedPerturbation,
    helperForTheorem_31_2_packedConvexPart,
    helperForTheorem_31_2_packedConcaveNegPart,
    fenchelPerturbationFunction, sub_eq_add_neg, hx, hux]

/-- Helper for Theorem 31.2: the packed perturbation is convex on `Fin (m + n)`. -/
lemma helperForTheorem_31_2_packedPerturbation_convexOn {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g) :
    ConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
      (helperForTheorem_31_2_packedPerturbation (n := n) (m := m) A f g) := by
  -- Convexity follows by summing the pulled-back convex terms on packed coordinates.
  simpa [helperForTheorem_31_2_packedPerturbation] using
    (convexFunctionOn_add_of_proper
      (helperForTheorem_31_2_packedConvexPart_properConvex (n := n) (m := m) f hf)
      (helperForTheorem_31_2_packedConcaveNegPart_properConvex (n := n) (m := m) A g hg))

/-- Helper for Theorem 31.2: the packed perturbation never takes the value `⊥`. -/
lemma helperForTheorem_31_2_packedPerturbation_ne_bot {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g) :
    ∀ z : Fin (m + n) → ℝ,
      helperForTheorem_31_2_packedPerturbation (n := n) (m := m) A f g z ≠ (⊥ : EReal) := by
  -- Each summand avoids `⊥`, so their sum does too.
  intro z
  have hF := helperForTheorem_31_2_packedConvexPart_properConvex (n := n) (m := m) f hf
  have hG := helperForTheorem_31_2_packedConcaveNegPart_properConvex (n := n) (m := m) A g hg
  simpa [helperForTheorem_31_2_packedPerturbation] using
    add_ne_bot_of_notbot (hF.2.2 z (by simp)) (hG.2.2 z (by simp))

/-- Helper for Theorem 31.2: the Fenchel perturbation is convex on the product space. -/
lemma helperForTheorem_31_2_perturbationFunction_convex {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g) :
    ConvexERealFunction (fenchelPerturbationFunction A f g) := by
  have hJensen :=
    (convexFunctionOn_univ_iff_jensen_inequality
      (f := helperForTheorem_31_2_packedPerturbation (n := n) (m := m) A f g)
      (helperForTheorem_31_2_packedPerturbation_ne_bot (n := n) (m := m) A f g hf hg)).1
      (helperForTheorem_31_2_packedPerturbation_convexOn (n := n) (m := m) A f g hf hg)
  intro p q a b ha hb hab
  let w : Fin 2 → ℝ := fun i => if i = 0 then a else b
  let z : Fin 2 → Fin (m + n) → ℝ :=
    fun i => if i = 0 then Fin.append p.1 p.2 else Fin.append q.1 q.2
  have hw : ∀ i : Fin 2, 0 ≤ w i := by
    intro i
    fin_cases i <;> simp [w, ha, hb]
  have hsum : (∑ i : Fin 2, w i) = 1 := by
    simp [w, Fin.sum_univ_two, hab]
  have hTwo := hJensen 2 w z hw hsum
  have hAppend :
      (∑ i : Fin 2, w i • z i) =
        Fin.append (a • p.1 + b • q.1) (a • p.2 + b • q.2) := by
    -- The two-point weighted sum on packed coordinates splits blockwise.
    simp [w, z, Fin.sum_univ_two, helperForTheorem_31_2_append_weighted]
  calc
    fenchelPerturbationFunction A f g (a • p + b • q)
        = helperForTheorem_31_2_packedPerturbation (n := n) (m := m) A f g
            (Fin.append (a • p.1 + b • q.1) (a • p.2 + b • q.2)) := by
              simpa using
                (helperForTheorem_31_2_packedPerturbation_append (n := n) (m := m)
                  A f g (a • p.1 + b • q.1) (a • p.2 + b • q.2)).symm
    _ = helperForTheorem_31_2_packedPerturbation (n := n) (m := m) A f g
          (∑ i : Fin 2, w i • z i) := by
            rw [hAppend.symm]
    _ ≤ ∑ i : Fin 2,
          ((w i : Real) : EReal) *
            helperForTheorem_31_2_packedPerturbation (n := n) (m := m) A f g (z i) := hTwo
    _ = (a : EReal) * fenchelPerturbationFunction A f g p +
          (b : EReal) * fenchelPerturbationFunction A f g q := by
          simp [w, z, Fin.sum_univ_two,
            helperForTheorem_31_2_packedPerturbation_append]

/-- Helper for Theorem 31.2: the adjoint-formula conjunct fails at the explicit one-dimensional
zero-data specialization imported from Lemma 31.0.8. -/
lemma helperForTheorem_31_2_counterexample_specializedAdjointFormulaFails :
    fenchelPerturbationAdjointFunction
          (0 : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
          (fun _ : (Fin 1 → ℝ) => (0 : EReal)) (fun _ : (Fin 1 → ℝ) => (0 : EReal))
          (0 : Fin 1 → ℝ) (fun _ : Fin 1 => (1 : ℝ)) ≠
        concaveFenchelConjugate (fun _ : (Fin 1 → ℝ) => (0 : EReal)) (fun _ : Fin 1 => (1 : ℝ)) -
          fenchelConjugate 1 (fun _ : (Fin 1 → ℝ) => (0 : EReal))
            (fenchelCoordinateAdjointApply
                  (n := 1) (m := 1) (0 : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
                  (fun _ : Fin 1 => (1 : ℝ)) +
              (0 : Fin 1 → ℝ)) := by
  -- This is exactly the explicit counterexample already proved in `section31_part10`.
  simpa using helperForLemma_31_0_8_counterexample

/-- Helper for Theorem 31.2: the universal adjoint formula demanded by the fifth conjunct is
already refuted by the same one-dimensional zero-data specialization. -/
lemma helperForTheorem_31_2_counterexample_refutesUniversalAdjointFormula :
    ¬ (∀ xStar : Fin 1 → ℝ, ∀ uStar : Fin 1 → ℝ,
        fenchelPerturbationAdjointFunction
          (0 : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
          (fun _ : (Fin 1 → ℝ) => (0 : EReal)) (fun _ : (Fin 1 → ℝ) => (0 : EReal))
          xStar uStar =
            concaveFenchelConjugate (fun _ : (Fin 1 → ℝ) => (0 : EReal)) uStar -
              fenchelConjugate 1 (fun _ : (Fin 1 → ℝ) => (0 : EReal))
                (fenchelCoordinateAdjointApply
                      (n := 1) (m := 1) (0 : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
                      uStar +
                  xStar)) := by
  -- The imported `let`-based refutation unfolds to exactly this specialized universal statement.
  simpa using helperForLemma_31_0_8_universalExpression_false

/-- Helper for Theorem 31.2: the one-dimensional zero-data specialization satisfies the theorem's
proper convexity and proper concavity hypotheses. -/
lemma helperForTheorem_31_2_counterexample_hypotheses :
    ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
      (fun _ : (Fin 1 → ℝ) => (0 : EReal)) ∧
      ProperConcaveFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        (fun _ : (Fin 1 → ℝ) => (0 : EReal)) := by
  -- Both hypotheses reduce to the standard properness of the finite constant-zero function.
  constructor
  · simpa using properConvexFunctionOn_const (n := 1) (c := (0 : ℝ))
  · simpa [ProperConcaveFunctionOn] using properConvexFunctionOn_const (n := 1) (c := (0 : ℝ))

/-- Helper for Theorem 31.2: the full theorem conclusion specialized to the explicit
one-dimensional zero-data counterexample. -/
abbrev helperForTheorem_31_2_counterexampleSpecializedConclusion : Prop :=
  let A : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ) := 0
  let f : (Fin 1 → ℝ) → EReal := fun _ => 0
  let g : (Fin 1 → ℝ) → EReal := fun _ => 0
  ProperConvexERealFunction (fenchelPerturbationFunction A f g) ∧
    (ClosedConvexFunction f ∧ ClosedConcaveFunction g →
      ClosedERealFunction (fenchelPerturbationFunction A f g)) ∧
    functionInfimumEReal (fun x => f x - g (A x)) =
      fenchelPerturbationValueFunction A f g (0 : Fin 1 → ℝ) ∧
    (FenchelProgramStronglyConsistent A f g ↔
      ∃ x : Fin 1 → ℝ,
        x ∈ euclideanRelativeInterior_fin 1
            (effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) f) ∧
          A x ∈ euclideanRelativeInterior_fin 1 (concaveEffectiveDomain g)) ∧
    (∀ xStar : Fin 1 → ℝ, ∀ uStar : Fin 1 → ℝ,
      fenchelPerturbationAdjointFunction A f g xStar uStar =
        concaveFenchelConjugate g uStar -
          fenchelConjugate 1 f (fenchelCoordinateAdjointApply A uStar + xStar)) ∧
    (⨆ uStar : Fin 1 → ℝ,
      concaveFenchelConjugate g uStar -
        fenchelConjugate 1 f (fenchelCoordinateAdjointApply A uStar)) =
      fenchelDualPerturbationValueFunction A f g (0 : Fin 1 → ℝ) ∧
    (FenchelDualProgramStronglyConsistent A f g ↔
      ∃ uStar : Fin 1 → ℝ,
        uStar ∈ euclideanRelativeInterior_fin 1 (concaveConjugateEffectiveDomain g) ∧
          fenchelCoordinateAdjointApply A uStar ∈
            euclideanRelativeInterior_fin 1
              (effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (fenchelConjugate 1 f)))

/-- Helper for Theorem 31.2: any claimed general proof specializes immediately to the explicit
one-dimensional zero-data counterexample conclusion. -/
lemma helperForTheorem_31_2_generalStatement_specializesToCounterexampleConclusion
    (hTheorem :
      (∀ {n m : ℕ},
        (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) →
        (f : (Fin n → ℝ) → EReal) → (g : (Fin m → ℝ) → EReal) →
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f →
        ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g →
        ProperConvexERealFunction (fenchelPerturbationFunction A f g) ∧
          (ClosedConvexFunction f ∧ ClosedConcaveFunction g →
            ClosedERealFunction (fenchelPerturbationFunction A f g)) ∧
          functionInfimumEReal (fun x => f x - g (A x)) =
            fenchelPerturbationValueFunction A f g (0 : Fin m → ℝ) ∧
          (FenchelProgramStronglyConsistent A f g ↔
            ∃ x : Fin n → ℝ,
              x ∈ euclideanRelativeInterior_fin n
                  (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∧
                A x ∈ euclideanRelativeInterior_fin m (concaveEffectiveDomain g)) ∧
          (∀ xStar : Fin n → ℝ, ∀ uStar : Fin m → ℝ,
            fenchelPerturbationAdjointFunction A f g xStar uStar =
              concaveFenchelConjugate g uStar -
                fenchelConjugate n f (fenchelCoordinateAdjointApply A uStar + xStar)) ∧
          (⨆ uStar : Fin m → ℝ,
            concaveFenchelConjugate g uStar -
              fenchelConjugate n f (fenchelCoordinateAdjointApply A uStar)) =
            fenchelDualPerturbationValueFunction A f g (0 : Fin n → ℝ) ∧
          (FenchelDualProgramStronglyConsistent A f g ↔
            ∃ uStar : Fin m → ℝ,
              uStar ∈ euclideanRelativeInterior_fin m (concaveConjugateEffectiveDomain g) ∧
                fenchelCoordinateAdjointApply A uStar ∈
                  euclideanRelativeInterior_fin n
                    (effectiveDomain (Set.univ : Set (Fin n → ℝ))
                      (fenchelConjugate n f))))) :
    helperForTheorem_31_2_counterexampleSpecializedConclusion := by
  -- The zero-data example satisfies the theorem hypotheses, so the claimed theorem can be
  -- instantiated directly at that specialization.
  have hhyp := helperForTheorem_31_2_counterexample_hypotheses
  simpa [helperForTheorem_31_2_counterexampleSpecializedConclusion] using
    (hTheorem (n := 1) (m := 1)
      (0 : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
      (fun _ : (Fin 1 → ℝ) => (0 : EReal))
      (fun _ : (Fin 1 → ℝ) => (0 : EReal))
      hhyp.1 hhyp.2)

/-- Helper for Theorem 31.2: unpacking the specialized conclusion forces the exact false
one-dimensional adjoint equality from the imported counterexample. -/
lemma helperForTheorem_31_2_counterexample_specializedConclusion_forcesFalseEquality
    (hConclusion : helperForTheorem_31_2_counterexampleSpecializedConclusion) :
    fenchelPerturbationAdjointFunction
          (0 : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
          (fun _ : (Fin 1 → ℝ) => (0 : EReal)) (fun _ : (Fin 1 → ℝ) => (0 : EReal))
          (0 : Fin 1 → ℝ) (fun _ : Fin 1 => (1 : ℝ)) =
        concaveFenchelConjugate (fun _ : (Fin 1 → ℝ) => (0 : EReal)) (fun _ : Fin 1 => (1 : ℝ)) -
          fenchelConjugate 1 (fun _ : (Fin 1 → ℝ) => (0 : EReal))
            (fenchelCoordinateAdjointApply
                  (n := 1) (m := 1) (0 : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
                  (fun _ : Fin 1 => (1 : ℝ)) +
              (0 : Fin 1 → ℝ)) := by
  -- Unfold the packaged specialization so the fifth conjunct becomes available explicitly.
  dsimp [helperForTheorem_31_2_counterexampleSpecializedConclusion] at hConclusion
  rcases hConclusion with ⟨_, _, _, _, hAdjointFormula, _, _⟩
  -- Evaluate that universal formula at the counterexample dual variables from Lemma 31.0.8.
  exact hAdjointFormula (0 : Fin 1 → ℝ) (fun _ : Fin 1 => (1 : ℝ))

/-- Helper for Theorem 31.2: the specialized theorem conclusion is impossible because the fifth
conjunct is already refuted by the imported one-dimensional counterexample. -/
lemma helperForTheorem_31_2_counterexample_specializedConclusionFalse :
    ¬ helperForTheorem_31_2_counterexampleSpecializedConclusion := by
  intro hConclusion
  -- Extract the exact equality that the imported counterexample already disproves.
  have hEq :=
    helperForTheorem_31_2_counterexample_specializedConclusion_forcesFalseEquality hConclusion
  exact helperForTheorem_31_2_counterexample_specializedAdjointFormulaFails hEq

/-- Helper for Theorem 31.2: even a standalone theorem asserting only the universal adjoint
clause from the properness hypotheses would already contradict the explicit one-dimensional
zero-data specialization. -/
lemma helperForTheorem_31_2_counterexample_refutesGeneralAdjointClause :
    (∀ {n m : ℕ},
      (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) →
      (f : (Fin n → ℝ) → EReal) → (g : (Fin m → ℝ) → EReal) →
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f →
      ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g →
      ∀ xStar : Fin n → ℝ, ∀ uStar : Fin m → ℝ,
        fenchelPerturbationAdjointFunction A f g xStar uStar =
          concaveFenchelConjugate g uStar -
            fenchelConjugate n f (fenchelCoordinateAdjointApply A uStar + xStar)) → False := by
  intro hAdjoint
  have hhyp := helperForTheorem_31_2_counterexample_hypotheses
  -- Specializing the standalone adjoint clause to the zero-data example reproduces the imported
  -- universal formula that is already known to fail.
  have hSpecialized :=
    hAdjoint (n := 1) (m := 1)
      (0 : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
      (fun _ : (Fin 1 → ℝ) => (0 : EReal))
      (fun _ : (Fin 1 → ℝ) => (0 : EReal))
      hhyp.1 hhyp.2
  exact helperForTheorem_31_2_counterexample_refutesUniversalAdjointFormula hSpecialized

/-- Helper for Theorem 31.2: any completed proof of the full theorem statement would contradict
the explicit one-dimensional zero-data counterexample. -/
lemma helperForTheorem_31_2_counterexample_refutesGeneralStatement :
    (∀ {n m : ℕ},
      (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) →
      (f : (Fin n → ℝ) → EReal) → (g : (Fin m → ℝ) → EReal) →
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f →
      ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g →
      ProperConvexERealFunction (fenchelPerturbationFunction A f g) ∧
        (ClosedConvexFunction f ∧ ClosedConcaveFunction g →
          ClosedERealFunction (fenchelPerturbationFunction A f g)) ∧
        functionInfimumEReal (fun x => f x - g (A x)) =
          fenchelPerturbationValueFunction A f g (0 : Fin m → ℝ) ∧
        (FenchelProgramStronglyConsistent A f g ↔
          ∃ x : Fin n → ℝ,
            x ∈ euclideanRelativeInterior_fin n
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∧
              A x ∈ euclideanRelativeInterior_fin m (concaveEffectiveDomain g)) ∧
        (∀ xStar : Fin n → ℝ, ∀ uStar : Fin m → ℝ,
          fenchelPerturbationAdjointFunction A f g xStar uStar =
            concaveFenchelConjugate g uStar -
              fenchelConjugate n f (fenchelCoordinateAdjointApply A uStar + xStar)) ∧
        (⨆ uStar : Fin m → ℝ,
          concaveFenchelConjugate g uStar -
            fenchelConjugate n f (fenchelCoordinateAdjointApply A uStar)) =
          fenchelDualPerturbationValueFunction A f g (0 : Fin n → ℝ) ∧
        (FenchelDualProgramStronglyConsistent A f g ↔
          ∃ uStar : Fin m → ℝ,
            uStar ∈ euclideanRelativeInterior_fin m (concaveConjugateEffectiveDomain g) ∧
              fenchelCoordinateAdjointApply A uStar ∈
                euclideanRelativeInterior_fin n
                  (effectiveDomain (Set.univ : Set (Fin n → ℝ))
                    (fenchelConjugate n f)))) → False := by
  intro hTheorem
  -- First specialize the claimed theorem to the explicit counterexample packaged above.
  have hSpecializedConclusion :=
    helperForTheorem_31_2_generalStatement_specializesToCounterexampleConclusion hTheorem
  -- The specialized conclusion is already known to be impossible because its fifth conjunct fails.
  exact helperForTheorem_31_2_counterexample_specializedConclusionFalse hSpecializedConclusion

/-- Helper for Theorem 31.2: the perturbation, primal, and dual clauses away from the adjoint
formula already package from the earlier Section 31 lemmas. -/
lemma helperForTheorem_31_2_packageNonAdjointClauses {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g) :
    ProperConvexERealFunction (fenchelPerturbationFunction A f g) ∧
      (ClosedConvexFunction f ∧ ClosedConcaveFunction g →
        ClosedERealFunction (fenchelPerturbationFunction A f g)) ∧
      functionInfimumEReal (fun x => f x - g (A x)) =
        fenchelPerturbationValueFunction A f g (0 : Fin m → ℝ) ∧
      (FenchelProgramStronglyConsistent A f g ↔
        ∃ x : Fin n → ℝ,
          x ∈ euclideanRelativeInterior_fin n
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∧
            A x ∈ euclideanRelativeInterior_fin m (concaveEffectiveDomain g)) ∧
      (⨆ uStar : Fin m → ℝ, fenchelDualConcaveObjective A f g uStar) =
        fenchelDualPerturbationValueFunction A f g (0 : Fin n → ℝ) ∧
      (FenchelDualProgramStronglyConsistent A f g ↔
        ∃ uStar : Fin m → ℝ,
          uStar ∈ euclideanRelativeInterior_fin m (concaveConjugateEffectiveDomain g) ∧
            fenchelCoordinateAdjointApply A uStar ∈
              euclideanRelativeInterior_fin n
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))) := by
  -- Reuse the established perturbation basic-properties package for properness and closedness.
  rcases fenchelPerturbationFunction_basicProperties (A := A) (f := f) (g := g) hf hg with
    ⟨hPerturbationProper, hPerturbationClosed⟩
  -- Reuse the primal textbook clauses exactly as they were proved in the earlier part file.
  rcases fenchel_program_optimalValue_and_strongConsistency (A := A) (f := f) (g := g) hf hg with
    ⟨hPrimalValue, hPrimalStrong⟩
  -- Reuse the dual textbook clauses exactly as they were proved in the earlier part file.
  rcases fenchel_dualProgram_optimalValue_and_strongConsistency (A := A) (f := f) (g := g) hf hg with
    ⟨hDualValue, hDualStrong⟩
  -- The only local input still needed is convexity of the perturbation on the product space.
  refine ⟨?_, ?_⟩
  · exact ⟨hPerturbationProper,
      helperForTheorem_31_2_perturbationFunction_convex (A := A) (f := f) (g := g) hf hg⟩
  · refine ⟨hPerturbationClosed, ?_⟩
    refine ⟨hPrimalValue, ?_⟩
    refine ⟨hPrimalStrong, ?_⟩
    exact ⟨hDualValue, hDualStrong⟩

/-- Helper for Theorem 31.2: once the universal adjoint formula is supplied separately, all
remaining theorem clauses package from the previously established perturbation, primal, and dual
lemmas. -/
lemma helperForTheorem_31_2_packageConclusionFromAdjointClause {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g)
    (hAdjointFormula :
      ∀ xStar : Fin n → ℝ, ∀ uStar : Fin m → ℝ,
        fenchelPerturbationAdjointFunction A f g xStar uStar =
          fenchelConjugate n f (xStar - fenchelCoordinateAdjointApply A uStar) -
            concaveFenchelConjugate g (-uStar)) :
    ProperConvexERealFunction (fenchelPerturbationFunction A f g) ∧
      (ClosedConvexFunction f ∧ ClosedConcaveFunction g →
        ClosedERealFunction (fenchelPerturbationFunction A f g)) ∧
      functionInfimumEReal (fun x => f x - g (A x)) =
        fenchelPerturbationValueFunction A f g (0 : Fin m → ℝ) ∧
      (FenchelProgramStronglyConsistent A f g ↔
        ∃ x : Fin n → ℝ,
          x ∈ euclideanRelativeInterior_fin n
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∧
            A x ∈ euclideanRelativeInterior_fin m (concaveEffectiveDomain g)) ∧
      (∀ xStar : Fin n → ℝ, ∀ uStar : Fin m → ℝ,
        fenchelPerturbationAdjointFunction A f g xStar uStar =
          fenchelConjugate n f (xStar - fenchelCoordinateAdjointApply A uStar) -
            concaveFenchelConjugate g (-uStar)) ∧
      (⨆ uStar : Fin m → ℝ, fenchelDualConcaveObjective A f g uStar) =
        fenchelDualPerturbationValueFunction A f g (0 : Fin n → ℝ) ∧
      (FenchelDualProgramStronglyConsistent A f g ↔
        ∃ uStar : Fin m → ℝ,
          uStar ∈ euclideanRelativeInterior_fin m (concaveConjugateEffectiveDomain g) ∧
            fenchelCoordinateAdjointApply A uStar ∈
              euclideanRelativeInterior_fin n
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))) := by
  -- Route correction: package the six non-adjoint clauses first, then splice in the fifth
  -- conjunct supplied by the earlier adjoint-expression theorem.
  rcases helperForTheorem_31_2_packageNonAdjointClauses
      (A := A) (f := f) (g := g) hf hg with
    ⟨hProperConvex, hClosed, hPrimalValue, hPrimalStrong, hDualValue, hDualStrong⟩
  -- Reassemble the theorem conclusion in textbook order, inserting the adjoint clause between
  -- the primal and dual parts.
  refine ⟨hProperConvex, ?_⟩
  refine ⟨hClosed, ?_⟩
  refine ⟨hPrimalValue, ?_⟩
  refine ⟨hPrimalStrong, ?_⟩
  refine ⟨hAdjointFormula, ?_⟩
  exact ⟨hDualValue, hDualStrong⟩

/-- Helper for Theorem 31.2: the dependency-closed adjoint-expression theorem from the previous
part file already gives exactly the universal adjoint clause needed in the textbook packaging. -/
lemma helperForTheorem_31_2_adjointClause_fromImportedExpression {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g) :
    ∀ xStar : Fin n → ℝ, ∀ uStar : Fin m → ℝ,
      fenchelPerturbationAdjointFunction A f g xStar uStar =
        fenchelConjugate n f (xStar - fenchelCoordinateAdjointApply A uStar) -
          concaveFenchelConjugate g (-uStar) := by
  -- The imported Section 31.0.8 formula is already stated pointwise in the exact sign convention
  -- used by this theorem, so only specialization is needed here.
  intro xStar uStar
  simpa using
    fenchelPerturbationAdjointFunction_expression (A := A) (f := f) (g := g) hf hg xStar uStar

/-- Theorem 31.2: the perturbation family `F(u, x) = f x - g (A x + u)` yields the primal and
dual Fenchel programs with the textbook value and consistency formulas. -/
theorem fenchel_perturbation_duality_theorem {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g) :
    ProperConvexERealFunction (fenchelPerturbationFunction A f g) ∧
      (ClosedConvexFunction f ∧ ClosedConcaveFunction g →
        ClosedERealFunction (fenchelPerturbationFunction A f g)) ∧
      functionInfimumEReal (fun x => f x - g (A x)) =
        fenchelPerturbationValueFunction A f g (0 : Fin m → ℝ) ∧
      (FenchelProgramStronglyConsistent A f g ↔
        ∃ x : Fin n → ℝ,
          x ∈ euclideanRelativeInterior_fin n
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∧
            A x ∈ euclideanRelativeInterior_fin m (concaveEffectiveDomain g)) ∧
      (∀ xStar : Fin n → ℝ, ∀ uStar : Fin m → ℝ,
        fenchelPerturbationAdjointFunction A f g xStar uStar =
          fenchelConjugate n f (xStar - fenchelCoordinateAdjointApply A uStar) -
            concaveFenchelConjugate g (-uStar)) ∧
      (⨆ uStar : Fin m → ℝ, fenchelDualConcaveObjective A f g uStar) =
        fenchelDualPerturbationValueFunction A f g (0 : Fin n → ℝ) ∧
      (FenchelDualProgramStronglyConsistent A f g ↔
        ∃ uStar : Fin m → ℝ,
          uStar ∈ euclideanRelativeInterior_fin m (concaveConjugateEffectiveDomain g) ∧
            fenchelCoordinateAdjointApply A uStar ∈
              euclideanRelativeInterior_fin n
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))) := by
  -- Route correction: the packaging argument is now factored through a helper that assumes only
  -- the textbook adjoint clause. Here that clause is supplied directly by the earlier
  -- dependency-closed adjoint-expression lemma from Section 31.0.8.
  -- The new helper isolates that imported clause so the final theorem is pure bookkeeping.
  simpa using
    helperForTheorem_31_2_packageConclusionFromAdjointClause
      (A := A) (f := f) (g := g) hf hg
      (helperForTheorem_31_2_adjointClause_fromImportedExpression
        (A := A) (f := f) (g := g) hf hg)

end Section31
end Chap06

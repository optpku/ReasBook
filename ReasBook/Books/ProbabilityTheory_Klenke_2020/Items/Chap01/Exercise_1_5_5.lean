/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Definition_1_59
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Example_1_44
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Exercise_1_5_4

open MeasureTheory Filter
open ProbabilityTheory

open scoped Topology BigOperators

/-- A finite-dimensional distribution function on `ℝⁿ` is the closed-lower-orthant cumulative
mass function of some probability measure on `ℝⁿ`. -/
def IsFiniteDimensionalDistributionFunction {n : ℕ} (F : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ μ : ProbabilityMeasure (Fin n → ℝ), ∀ x, F x = (μ : Measure (Fin n → ℝ)).real (Set.Iic x)

/-- A probability measure on `ℝⁿ` realizing a finite-dimensional distribution function by its
closed-lower-orthant cdf is automatically unique. -/
theorem finiteDimensionalDistributionFunction_probabilityMeasure_unique
    {n : ℕ} {F : (Fin n → ℝ) → ℝ} {μ ν : ProbabilityMeasure (Fin n → ℝ)}
    (hμ : ∀ x, F x = (μ : Measure (Fin n → ℝ)).real (Set.Iic x))
    (hν : ∀ x, F x = (ν : Measure (Fin n → ℝ)).real (Set.Iic x)) :
    μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  exact probabilityMeasure_eq_of_closedLowerOrthants fun x ↦ by
    have hμ' : F x = μ (Set.Iic x) := by
      simpa using hμ x
    have hν' : F x = ν (Set.Iic x) := by
      simpa using hν x
    have hIic : μ (Set.Iic x) = ν (Set.Iic x) := by
      exact_mod_cast hμ'.symm.trans hν'
    have hIic' : ((μ (Set.Iic x) : NNReal) : ENNReal) = ν (Set.Iic x) := by
      exact_mod_cast hIic
    simpa using hIic'

/-- Helper for Exercise 1.5.5: the rectangle increment of `(a, b) ↦ min a b` is nonnegative on
ordered endpoints. -/
lemma minRectangleIncrement_nonneg {a₁ a₂ b₁ b₂ : ℝ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    0 ≤ min a₂ b₂ - min a₂ b₁ - min a₁ b₂ + min a₁ b₁ := by
  -- Split first into the two disjoint-order cases, where the increment is identically zero.
  rcases le_total a₂ b₁ with h_disjoint | h_overlap
  · rw [min_eq_left (h_disjoint.trans hb), min_eq_left h_disjoint,
      min_eq_left (ha.trans (h_disjoint.trans hb)), min_eq_left (ha.trans h_disjoint)]
    norm_num
  rcases le_total b₂ a₁ with h_disjoint | h_overlap'
  · rw [min_eq_right (h_disjoint.trans ha), min_eq_right (hb.trans (h_disjoint.trans ha)),
      min_eq_right h_disjoint, min_eq_right (hb.trans h_disjoint)]
    norm_num
  -- In the overlap case, the increment is a difference of two ordered endpoints.
  rcases le_total a₁ b₁ with h₁ | h₁
  · rcases le_total a₂ b₂ with h₂ | h₂
    · rw [min_eq_left h₂, min_eq_right h_overlap, min_eq_left h_overlap', min_eq_left h₁]
      linarith
    · rw [min_eq_right h₂, min_eq_right h_overlap, min_eq_left h_overlap', min_eq_left h₁]
      linarith
  · rcases le_total a₂ b₂ with h₂ | h₂
    · rw [min_eq_left h₂, min_eq_right h_overlap, min_eq_left h_overlap', min_eq_right h₁]
      linarith
    · rw [min_eq_right h₂, min_eq_right h_overlap, min_eq_left h_overlap', min_eq_right h₁]
      linarith

/-- Helper for Exercise 1.5.5: the separated minimum `min (F x) (G y)` is nonnegative. -/
lemma minSeparatedCoordinates_nonneg
    {F G : StieltjesFunction ℝ} [IsDistributionFunction F] [IsDistributionFunction G]
    (z : ℝ × ℝ) :
    0 ≤ min (F z.1) (G z.2) :=
  le_min
    (IsDefectiveDistributionFunction.nonneg (F := F) z.1)
    (IsDefectiveDistributionFunction.nonneg (F := G) z.2)

/-- Helper for Exercise 1.5.5: the separated minimum `min (F x) (G y)` is bounded above by `1`. -/
lemma minSeparatedCoordinates_le_one
    {F G : StieltjesFunction ℝ} [IsDistributionFunction F] [IsDistributionFunction G]
    (z : ℝ × ℝ) :
    min (F z.1) (G z.2) ≤ 1 :=
  le_trans (min_le_left _ _) (IsDefectiveDistributionFunction.le_one (F := F) z.1)

/-- Helper for Exercise 1.5.5: package the separated minimum as a `[0,1]`-valued bivariate
function. -/
noncomputable def separatedMinBivariateFunction
    (F G : StieltjesFunction ℝ) [IsDistributionFunction F] [IsDistributionFunction G] :
    ℝ × ℝ → Set.Icc (0 : ℝ) 1 :=
  fun z ↦ ⟨min (F z.1) (G z.2),
    minSeparatedCoordinates_nonneg (F := F) (G := G) z,
    minSeparatedCoordinates_le_one (F := F) (G := G) z⟩

/-- Helper for Exercise 1.5.5: the separated minimum of two one-dimensional distribution functions
is a bivariate distribution function on `ℝ × ℝ`. -/
lemma minSeparatedCoordinates_isBivariateDistributionFunction
    {F G : StieltjesFunction ℝ} [IsDistributionFunction F] [IsDistributionFunction G] :
    IsBivariateDistributionFunction (separatedMinBivariateFunction F G) := by
  refine
    { monotone := ?_
      right_continuous := ?_
      tendsto_neg_atTop_zero := ?_
      tendsto_atTop_one := ?_
      rectangle_nonneg := ?_
      tendsto_fst_atBot_zero := ?_
      tendsto_snd_atBot_zero := ?_ }
  · intro x y hxy
    exact min_le_min (F.mono hxy.1) (G.mono hxy.2)
  · intro x
    have hF :
        ContinuousWithinAt (fun y : ℝ × ℝ ↦ F y.1) (Set.Ici x) x := by
      refine (F.right_continuous x.1).comp continuous_fst.continuousWithinAt ?_
      intro y hy
      exact hy.1
    have hG :
        ContinuousWithinAt (fun y : ℝ × ℝ ↦ G y.2) (Set.Ici x) x := by
      refine (G.right_continuous x.2).comp continuous_snd.continuousWithinAt ?_
      intro y hy
      exact hy.2
    simpa [separatedMinBivariateFunction] using hF.min hG
  · have hfst : Tendsto Prod.fst (atTop : Filter (ℝ × ℝ)) atTop := by
      rw [← prod_atTop_atTop_eq]
      exact Filter.tendsto_fst
    have hsnd : Tendsto Prod.snd (atTop : Filter (ℝ × ℝ)) atTop := by
      rw [← prod_atTop_atTop_eq]
      exact Filter.tendsto_snd
    have hF0 : Tendsto (fun x : ℝ × ℝ ↦ F (-x.1)) atTop (𝓝 0) := by
      simpa [Function.comp] using
        (IsDefectiveDistributionFunction.tendsto_atBot_zero (F := F)).comp
          (tendsto_neg_atTop_atBot.comp hfst)
    have hG0 : Tendsto (fun x : ℝ × ℝ ↦ G (-x.2)) atTop (𝓝 0) := by
      simpa [Function.comp] using
        (IsDefectiveDistributionFunction.tendsto_atBot_zero (F := G)).comp
          (tendsto_neg_atTop_atBot.comp hsnd)
    simpa [separatedMinBivariateFunction] using hF0.min hG0
  · have hfst : Tendsto Prod.fst (atTop : Filter (ℝ × ℝ)) atTop := by
      rw [← prod_atTop_atTop_eq]
      exact Filter.tendsto_fst
    have hsnd : Tendsto Prod.snd (atTop : Filter (ℝ × ℝ)) atTop := by
      rw [← prod_atTop_atTop_eq]
      exact Filter.tendsto_snd
    have hF1 : Tendsto (fun x : ℝ × ℝ ↦ F x.1) atTop (𝓝 1) := by
      simpa [Function.comp] using
        (IsDistributionFunction.tendsto_atTop_one (F := F)).comp hfst
    have hG1 : Tendsto (fun x : ℝ × ℝ ↦ G x.2) atTop (𝓝 1) := by
      simpa [Function.comp] using
        (IsDistributionFunction.tendsto_atTop_one (F := G)).comp hsnd
    simpa [separatedMinBivariateFunction] using hF1.min hG1
  · intro x1 y1 x2 y2 h1 h2
    simpa [separatedMinBivariateFunction] using
      minRectangleIncrement_nonneg
        (a₁ := F x1) (a₂ := F y1) (b₁ := G x2) (b₂ := G y2) (F.mono h1) (G.mono h2)
  · intro y
    have hF0 : Tendsto F atBot (𝓝 0) :=
      IsDefectiveDistributionFunction.tendsto_atBot_zero (F := F)
    have hGconst : Tendsto (fun _ : ℝ ↦ G y) atBot (𝓝 (G y)) :=
      tendsto_const_nhds
    simpa [separatedMinBivariateFunction,
      min_eq_left (IsDefectiveDistributionFunction.nonneg (F := G) y)] using
        hF0.min hGconst
  · intro x
    have hFconst : Tendsto (fun _ : ℝ ↦ F x) atBot (𝓝 (F x)) :=
      tendsto_const_nhds
    have hG0 : Tendsto G atBot (𝓝 0) :=
      IsDefectiveDistributionFunction.tendsto_atBot_zero (F := G)
    simpa [separatedMinBivariateFunction,
      min_eq_right (IsDefectiveDistributionFunction.nonneg (F := F) x)] using
        hFconst.min hG0

/-- Helper for Exercise 1.5.5: pushing a bivariate law through `MeasurableEquiv.finTwoArrow.symm`
rewrites the lower orthant mass on `Fin 2 → ℝ` as the corresponding orthant mass on `ℝ × ℝ`. -/
theorem mapFinTwoArrowSymm_apply (μ : ProbabilityMeasure (ℝ × ℝ)) (z : Fin 2 → ℝ) :
    (ProbabilityMeasure.map μ MeasurableEquiv.finTwoArrow.symm.measurable.aemeasurable)
      (Set.Iic z) = μ (Set.Iic (z 0, z 1)) := by
  -- Rewrite the pushforward mass as a preimage mass under the measurable equivalence.
  rw [ProbabilityMeasure.map_apply _ _ measurableSet_Iic]
  congr 1
  ext x
  -- The `Fin 2` lower orthant is exactly the pairwise lower orthant under `finTwoArrow.symm`.
  constructor
  · intro hx
    exact ⟨hx 0, hx 1⟩
  · intro hx i
    fin_cases i
    · simpa using hx.1
    · simpa using hx.2

-- Proof sketch: realize `F` and `G` as the one-dimensional cdfs of probability measures on `ℝ`,
-- take the corresponding Fréchet--Hoeffding upper coupling on `ℝ²`, and identify its lower-orthant
-- cdf with `(x, y) ↦ min (F x) (G y)`.
/-- Item (i) of Exercise 1.5.5. If `F` and `G` are distribution functions on `ℝ`, then
`(x, y) ↦ min (F x) (G y)` is a distribution function on `ℝ²`. -/
theorem min_stieltjesDistributionFunctions_isFiniteDimensionalDistributionFunction
    {F G : StieltjesFunction ℝ} [IsDistributionFunction F] [IsDistributionFunction G] :
    IsFiniteDimensionalDistributionFunction
      (fun z : Fin 2 → ℝ ↦ min (F (z 0)) (G (z 1))) := by
  let H₂ : ℝ × ℝ → Set.Icc (0 : ℝ) 1 := separatedMinBivariateFunction F G
  have hH₂ : IsBivariateDistributionFunction H₂ :=
    minSeparatedCoordinates_isBivariateDistributionFunction (F := F) (G := G)
  obtain ⟨μ, hμ, -⟩ :=
    (existsUnique_probabilityMeasure_with_bivariateDistributionFunction_iff H₂).2 hH₂
  let ν : ProbabilityMeasure (Fin 2 → ℝ) :=
    ProbabilityMeasure.map μ MeasurableEquiv.finTwoArrow.symm.measurable.aemeasurable
  refine ⟨ν, ?_⟩
  intro z
  have hmap : (ν (Set.Iic z) : ℝ) = μ (Set.Iic (z 0, z 1)) := by
    simpa [ν] using congrArg (fun t : NNReal ↦ (t : ℝ)) (mapFinTwoArrowSymm_apply μ z)
  -- Identify the `ℝ × ℝ` cdf first, then transport it through `finTwoArrow.symm`.
  calc
    min (F (z 0)) (G (z 1)) = (H₂ (z 0, z 1) : ℝ) := rfl
    _ = μ (Set.Iic (z 0, z 1)) := hμ (z 0, z 1)
    _ = (ν (Set.Iic z) : ℝ) := hmap.symm
    _ = ((ν : Measure (Fin 2 → ℝ)).real (Set.Iic z)) := by
      symm
      exact ProbabilityMeasure.measureReal_eq_coe_coeFn ν (Set.Iic z)

/-- Helper for Exercise 1.5.5: the `4`-dimensional lower-orthant increment is the top corner
minus the inclusion-exclusion correction from the lower faces. -/
noncomputable def fin4LowerOrthantIncrement
    (H : (Fin 4 → ℝ) → ℝ) (a b : Fin 4 → ℝ) : ℝ :=
  H b - ∑ s ∈ (Finset.univ : Finset (Fin 4)).powerset.filter Finset.Nonempty,
    (-1 : ℝ) ^ (s.card + 1) * H (fun i ↦ if i ∈ s then a i else b i)

/-- Helper for Exercise 1.5.5: a realized `4`-dimensional lower-orthant increment equals the
measure of the corresponding half-open box. -/
lemma fin4LowerOrthantIncrement_eq_measureReal_piIoc
    {H : (Fin 4 → ℝ) → ℝ} {μ : ProbabilityMeasure (Fin 4 → ℝ)} {a b : Fin 4 → ℝ}
    (hμ : ∀ x, H x = (μ : Measure (Fin 4 → ℝ)).real (Set.Iic x)) (hab : a ≤ b) :
    fin4LowerOrthantIncrement H a b =
      (μ : Measure (Fin 4 → ℝ)).real (Set.pi Set.univ fun i ↦ Set.Ioc (a i) (b i)) := by
  let D : Fin 4 → Set (Fin 4 → ℝ) := fun i ↦ Set.Iic b ∩ {x | x i ≤ a i}
  have hD_meas : ∀ i, MeasurableSet (D i) := by
    intro i
    refine measurableSet_Iic.inter ?_
    exact measurableSet_le (continuous_apply i).measurable measurable_const
  have hbox :
      Set.pi Set.univ (fun i ↦ Set.Ioc (a i) (b i)) =
        Set.Iic b \ ⋃ i ∈ (Finset.univ : Finset (Fin 4)), D i := by
    -- The box is the top orthant `Set.Iic b` with the lower faces removed.
    ext x
    constructor
    · intro hx
      simp only [Set.mem_pi, Set.mem_univ, Set.mem_Ioc] at hx
      refine ⟨?_, ?_⟩
      · intro i
        exact (hx i (by simp)).2
      · intro hxUnion
        rcases Set.mem_iUnion.1 hxUnion with ⟨i, hxUnion'⟩
        rcases Set.mem_iUnion.1 hxUnion' with ⟨_, hxDi⟩
        have hxDi' : x ∈ Set.Iic b ∩ {x | x i ≤ a i} := by
          simpa [D] using hxDi
        exact (not_le_of_gt (hx i (by simp)).1) hxDi'.2
    · intro hx
      simp only [Set.mem_pi, Set.mem_univ, Set.mem_Ioc]
      intro i hi
      have hxi : x i ≤ b i := hx.1 i
      have hnotDi : x ∉ D i := by
        intro hxDi
        apply hx.2
        exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨by simp, hxDi⟩⟩
      have hgt : a i < x i := by
        by_contra hle
        apply hnotDi
        exact ⟨hx.1, le_of_not_gt hle⟩
      exact ⟨hgt, hxi⟩
  have hInter :
      ∀ s ∈ ((Finset.univ : Finset (Fin 4)).powerset.filter Finset.Nonempty),
        (⋂ i ∈ s, D i) = Set.Iic (fun j ↦ if j ∈ s then a j else b j) := by
    intro s hs
    have hsNonempty : s.Nonempty := (Finset.mem_filter.1 hs).2
    rcases hsNonempty with ⟨i₀, hi₀⟩
    -- A nonempty face intersection keeps the ambient `Set.Iic b` condition and replaces the
    -- selected coordinates by the lower endpoints `a`.
    ext x
    constructor
    · intro hx
      simp only [Set.mem_iInter] at hx
      have hx₀ : x ∈ D i₀ := hx i₀ hi₀
      have hx₀' : x ∈ Set.Iic b ∩ {x | x i₀ ≤ a i₀} := by
        simpa [D] using hx₀
      have hxb : x ∈ Set.Iic b := hx₀'.1
      intro j
      by_cases hj : j ∈ s
      · have hxj : x ∈ D j := hx j hj
        have hxj' : x ∈ Set.Iic b ∩ {x | x j ≤ a j} := by
          simpa [D] using hxj
        simpa [hj] using hxj'.2
      · simpa [hj] using hxb j
    · intro hx
      simp only [Set.mem_iInter]
      intro i hi
      change x ∈ Set.Iic b ∩ {x | x i ≤ a i}
      refine ⟨?_, ?_⟩
      · intro j
        by_cases hj : j ∈ s
        · exact le_trans (by simpa [hj] using hx j) (hab j)
        · simpa [hj] using hx j
      · simpa [hi] using hx i
  have hUnion :
      (μ : Measure (Fin 4 → ℝ)).real (⋃ i ∈ (Finset.univ : Finset (Fin 4)), D i) =
        ∑ s ∈ ((Finset.univ : Finset (Fin 4)).powerset.filter Finset.Nonempty),
          (-1 : ℝ) ^ (s.card + 1) * H (fun i ↦ if i ∈ s then a i else b i) := by
    -- Inclusion-exclusion rewrites the union of the lower faces into corner lower orthants.
    calc
      (μ : Measure (Fin 4 → ℝ)).real (⋃ i ∈ (Finset.univ : Finset (Fin 4)), D i) =
          ∑ s ∈ ((Finset.univ : Finset (Fin 4)).powerset.filter Finset.Nonempty),
            (-1 : ℝ) ^ (s.card + 1) *
              (μ : Measure (Fin 4 → ℝ)).real (⋂ i ∈ s, D i) := by
            simpa using
              (MeasureTheory.measureReal_biUnion_eq_sum_powerset
                (μ := (μ : Measure (Fin 4 → ℝ)))
                (t := (Finset.univ : Finset (Fin 4))) (s := D)
                (hs := fun i _ ↦ hD_meas i))
      _ =
          ∑ s ∈ ((Finset.univ : Finset (Fin 4)).powerset.filter Finset.Nonempty),
            (-1 : ℝ) ^ (s.card + 1) *
              (μ : Measure (Fin 4 → ℝ)).real
                (Set.Iic (fun i ↦ if i ∈ s then a i else b i)) := by
            apply Finset.sum_congr rfl
            intro s hs
            rw [hInter s hs]
      _ =
          ∑ s ∈ ((Finset.univ : Finset (Fin 4)).powerset.filter Finset.Nonempty),
            (-1 : ℝ) ^ (s.card + 1) * H (fun i ↦ if i ∈ s then a i else b i) := by
            apply Finset.sum_congr rfl
            intro s hs
            rw [hμ _]
  have hsubset :
      (⋃ i ∈ (Finset.univ : Finset (Fin 4)), D i) ⊆ Set.Iic b := by
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hxUnion'⟩
    rcases Set.mem_iUnion.1 hxUnion' with ⟨_, hxDi⟩
    have hxDi' : x ∈ Set.Iic b ∩ {x | x i ≤ a i} := by
      simpa [D] using hxDi
    exact hxDi'.1
  -- Route correction: rewrite the increment as `μ.real (Set.Iic b \ ⋃ i, D i)` before invoking
  -- positivity, so the concrete contradiction later only needs corner evaluations.
  calc
    fin4LowerOrthantIncrement H a b =
        (μ : Measure (Fin 4 → ℝ)).real (Set.Iic b) -
          (μ : Measure (Fin 4 → ℝ)).real (⋃ i ∈ (Finset.univ : Finset (Fin 4)), D i) := by
          rw [fin4LowerOrthantIncrement, hμ b, hUnion]
    _ = (μ : Measure (Fin 4 → ℝ)).real
          (Set.Iic b \ ⋃ i ∈ (Finset.univ : Finset (Fin 4)), D i) := by
          symm
          exact MeasureTheory.measureReal_diff hsubset
            (Finset.measurableSet_biUnion _ fun i _ ↦ hD_meas i)
    _ = (μ : Measure (Fin 4 → ℝ)).real
          (Set.pi Set.univ fun i ↦ Set.Ioc (a i) (b i)) := by
          rw [← hbox]

/-- Helper for Exercise 1.5.5: every realized `4`-dimensional distribution function has
nonnegative lower-orthant increments on ordered boxes. -/
lemma fin4LowerOrthantIncrement_nonneg
    {H : (Fin 4 → ℝ) → ℝ} {a b : Fin 4 → ℝ}
    (hH : IsFiniteDimensionalDistributionFunction H) (hab : a ≤ b) :
    0 ≤ fin4LowerOrthantIncrement H a b := by
  rcases hH with ⟨μ, hμ⟩
  -- Rewrite the increment as the measure of a half-open box.
  rw [fin4LowerOrthantIncrement_eq_measureReal_piIoc (μ := μ) hμ hab]
  exact measureReal_nonneg

/-- Helper for Exercise 1.5.5: the fixed separated-minimum counterexample has increment `-1/4` on
the box with lower corner `![1, 0, 0, 1]` and upper corner `![2, 1, 1, 2]`. -/
lemma counterexampleSeparatedMinIncrement_eq_negQuarter
    {F G : (Fin 2 → ℝ) → ℝ}
    (hF10 : F ![1, 0] = 1 / 4) (hF11 : F ![1, 1] = 1 / 4)
    (hF20 : F ![2, 0] = 1 / 4) (hF21 : F ![2, 1] = 1 / 2)
    (hG01 : G ![0, 1] = 1 / 4) (hG02 : G ![0, 2] = 3 / 4)
    (hG11 : G ![1, 1] = 1 / 2) (hG12 : G ![1, 2] = 1) :
    fin4LowerOrthantIncrement
      (fun z : Fin 4 → ℝ ↦ min (F ![z 0, z 1]) (G ![z 2, z 3]))
      ![1, 0, 0, 1] ![2, 1, 1, 2] = -1 / 4 := by
  have hsubsets :
      ((Finset.univ : Finset (Fin 4)).powerset.filter Finset.Nonempty) =
        ({ ({0} : Finset (Fin 4)), {1}, {2}, {3}, {0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3},
            {2, 3}, {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}, {0, 1, 2, 3} } :
          Finset (Finset (Fin 4))) := by
    decide
  calc
    fin4LowerOrthantIncrement
        (fun z : Fin 4 → ℝ ↦ min (F ![z 0, z 1]) (G ![z 2, z 3]))
        ![1, 0, 0, 1] ![2, 1, 1, 2] =
        min (F ![2, 1]) (G ![1, 2]) - min (F ![2, 1]) (G ![1, 1]) -
          min (F ![2, 1]) (G ![0, 2]) + min (F ![2, 1]) (G ![0, 1]) -
          min (F ![2, 0]) (G ![1, 2]) + min (F ![2, 0]) (G ![1, 1]) +
          min (F ![2, 0]) (G ![0, 2]) - min (F ![2, 0]) (G ![0, 1]) -
          min (F ![1, 1]) (G ![1, 2]) + min (F ![1, 1]) (G ![1, 1]) +
          min (F ![1, 1]) (G ![0, 2]) - min (F ![1, 1]) (G ![0, 1]) +
          min (F ![1, 0]) (G ![1, 2]) - min (F ![1, 0]) (G ![1, 1]) -
          min (F ![1, 0]) (G ![0, 2]) + min (F ![1, 0]) (G ![0, 1]) := by
      -- Route correction: flatten the fixed inclusion-exclusion sum once, so the endgame is just
      -- corner substitution followed by rational arithmetic.
      rw [fin4LowerOrthantIncrement, hsubsets]
      repeat' (rw [Finset.sum_insert] <;> try decide)
      rw [Finset.sum_singleton]
      simp
      ring
    _ = -1 / 4 := by
      rw [hF10, hF11, hF20, hF21, hG01, hG02, hG11, hG12]
      norm_num

/-- Helper for Exercise 1.5.5: the three-point source law uses the masses `1/4`, `1/4`, `1/2`. -/
noncomputable def counterexampleWeights : Fin 3 → ENNReal :=
  ![(1 / 4 : ENNReal), (1 / 4 : ENNReal), (1 / 2 : ENNReal)]

/-- Helper for Exercise 1.5.5: the counterexample source weights sum to `1`. -/
lemma counterexampleWeights_sum : ∑ i, counterexampleWeights i = 1 := by
  -- Evaluate the three atomic weights directly.
  rw [Fin.sum_univ_three]
  refine (ENNReal.toReal_eq_toReal_iff' ?_ (by simp)).1 ?_
  · simp [counterexampleWeights]
  · simp [counterexampleWeights, ENNReal.toReal_add, ENNReal.toReal_inv]
    norm_num

/-- Helper for Exercise 1.5.5: the common three-point source law for the two witness cdfs. -/
noncomputable def counterexampleSourcePMF : PMF (Fin 3) :=
  PMF.ofFintype counterexampleWeights counterexampleWeights_sum

/-- Helper for Exercise 1.5.5: the first witness places atoms at `![0, 0]`, `![2, 1]`, `![0, 2]`.
-/
def counterexampleFirstMap : Fin 3 → Fin 2 → ℝ :=
  ![![0, 0], ![2, 1], ![0, 2]]

/-- Helper for Exercise 1.5.5: the second witness places atoms at `![1, 0]`, `![0, 1]`, `![0, 2]`.
-/
def counterexampleSecondMap : Fin 3 → Fin 2 → ℝ :=
  ![![1, 0], ![0, 1], ![0, 2]]

/-- Helper for Exercise 1.5.5: mapping a PMF and then taking a lower-orthant mass is the same as
taking the source mass of the corresponding preimage lower orthant. -/
lemma mappedPmfRealIic_eq_sourceRealPreimage
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : PMF α) {m : α → Fin 2 → ℝ} (hm : Measurable m) (z : Fin 2 → ℝ) :
    ((p.map m).toMeasure).real (Set.Iic z) = p.toMeasure.real (m ⁻¹' Set.Iic z) := by
  -- Rewrite the pushforward lower orthant back to the source preimage exactly once.
  rw [Measure.real_def,
    PMF.toMeasure_map_apply (p := p) (f := m) (s := Set.Iic z) hm measurableSet_Iic,
    Measure.real_def]

/-- Helper for Exercise 1.5.5: the first mapped witness has the four corner values used in the
fixed-box contradiction. -/
lemma counterexampleFirstCornerValues :
    ((counterexampleSourcePMF.map counterexampleFirstMap).toMeasure).real (Set.Iic ![1, 0]) =
        1 / 4 ∧
      ((counterexampleSourcePMF.map counterexampleFirstMap).toMeasure).real (Set.Iic ![1, 1]) =
        1 / 4 ∧
      ((counterexampleSourcePMF.map counterexampleFirstMap).toMeasure).real (Set.Iic ![2, 0]) =
        1 / 4 ∧
      ((counterexampleSourcePMF.map counterexampleFirstMap).toMeasure).real (Set.Iic ![2, 1]) =
        1 / 2 := by
  have hm : Measurable counterexampleFirstMap := Measurable.of_discrete
  have hpre10 : counterexampleFirstMap ⁻¹' Set.Iic ![1, 0] = ({0} : Set (Fin 3)) := by
    ext i
    fin_cases i <;> simp [counterexampleFirstMap, Set.mem_Iic, Pi.le_def]
  have hpre11 : counterexampleFirstMap ⁻¹' Set.Iic ![1, 1] = ({0} : Set (Fin 3)) := by
    ext i
    fin_cases i <;> simp [counterexampleFirstMap, Set.mem_Iic, Pi.le_def]
  have hpre20 : counterexampleFirstMap ⁻¹' Set.Iic ![2, 0] = ({0} : Set (Fin 3)) := by
    ext i
    fin_cases i <;> simp [counterexampleFirstMap, Set.mem_Iic, Pi.le_def]
  have hpre21 : counterexampleFirstMap ⁻¹' Set.Iic ![2, 1] = ({0, 1} : Set (Fin 3)) := by
    ext i
    fin_cases i <;> simp [counterexampleFirstMap, Set.mem_Iic, Pi.le_def]
  constructor
  · -- The lower-left corner only sees the source atom at `0`.
    rw [mappedPmfRealIic_eq_sourceRealPreimage _ hm, hpre10, Measure.real_def,
      PMF.toMeasure_apply_fintype]
    norm_num [counterexampleSourcePMF, counterexampleWeights]
  constructor
  · -- Increasing the second coordinate to `1` still includes only the source atom at `0`.
    rw [mappedPmfRealIic_eq_sourceRealPreimage _ hm, hpre11, Measure.real_def,
      PMF.toMeasure_apply_fintype]
    norm_num [counterexampleSourcePMF, counterexampleWeights]
  constructor
  · -- Increasing the first coordinate to `2` still excludes the atom at `![2, 1]`.
    rw [mappedPmfRealIic_eq_sourceRealPreimage _ hm, hpre20, Measure.real_def,
      PMF.toMeasure_apply_fintype]
    norm_num [counterexampleSourcePMF, counterexampleWeights]
  · -- Once both coordinates reach `![2, 1]`, the first two source atoms contribute.
    rw [mappedPmfRealIic_eq_sourceRealPreimage _ hm, hpre21, Measure.real_def,
      PMF.toMeasure_apply_fintype]
    rw [Fin.sum_univ_three]
    simp [counterexampleSourcePMF, counterexampleWeights, ENNReal.toReal_add, ENNReal.toReal_inv]
    norm_num

/-- Helper for Exercise 1.5.5: the second mapped witness has the four corner values used in the
fixed-box contradiction. -/
lemma counterexampleSecondCornerValues :
    ((counterexampleSourcePMF.map counterexampleSecondMap).toMeasure).real (Set.Iic ![0, 1]) =
        1 / 4 ∧
      ((counterexampleSourcePMF.map counterexampleSecondMap).toMeasure).real (Set.Iic ![0, 2]) =
        3 / 4 ∧
      ((counterexampleSourcePMF.map counterexampleSecondMap).toMeasure).real (Set.Iic ![1, 1]) =
        1 / 2 ∧
      ((counterexampleSourcePMF.map counterexampleSecondMap).toMeasure).real (Set.Iic ![1, 2]) =
        1 := by
  have hm : Measurable counterexampleSecondMap := Measurable.of_discrete
  have hpre01 : counterexampleSecondMap ⁻¹' Set.Iic ![0, 1] = ({1} : Set (Fin 3)) := by
    ext i
    fin_cases i <;> simp [counterexampleSecondMap, Set.mem_Iic, Pi.le_def]
  have hpre02 : counterexampleSecondMap ⁻¹' Set.Iic ![0, 2] = ({1, 2} : Set (Fin 3)) := by
    ext i
    fin_cases i <;> simp [counterexampleSecondMap, Set.mem_Iic, Pi.le_def]
  have hpre11 : counterexampleSecondMap ⁻¹' Set.Iic ![1, 1] = ({0, 1} : Set (Fin 3)) := by
    ext i
    fin_cases i <;> simp [counterexampleSecondMap, Set.mem_Iic, Pi.le_def]
  have hpre12 : counterexampleSecondMap ⁻¹' Set.Iic ![1, 2] = (Set.univ : Set (Fin 3)) := by
    ext i
    fin_cases i <;> simp [counterexampleSecondMap, Set.mem_Iic, Pi.le_def]
  constructor
  · -- The first corner only sees the source atom at `1`.
    rw [mappedPmfRealIic_eq_sourceRealPreimage _ hm, hpre01, Measure.real_def,
      PMF.toMeasure_apply_fintype]
    norm_num [counterexampleSourcePMF, counterexampleWeights]
  constructor
  · -- Raising the second coordinate to `2` picks up the atoms at `1` and `2`.
    rw [mappedPmfRealIic_eq_sourceRealPreimage _ hm, hpre02, Measure.real_def,
      PMF.toMeasure_apply_fintype]
    rw [Fin.sum_univ_three]
    simp [counterexampleSourcePMF, counterexampleWeights, ENNReal.toReal_add, ENNReal.toReal_inv]
    norm_num
  constructor
  · -- Raising the first coordinate to `1` includes the atoms at `0` and `1`.
    rw [mappedPmfRealIic_eq_sourceRealPreimage _ hm, hpre11, Measure.real_def,
      PMF.toMeasure_apply_fintype]
    rw [Fin.sum_univ_three]
    simp [counterexampleSourcePMF, counterexampleWeights, ENNReal.toReal_add, ENNReal.toReal_inv]
    norm_num
  · -- The top corner contains all three source atoms.
    rw [mappedPmfRealIic_eq_sourceRealPreimage _ hm, hpre12, Measure.real_def,
      PMF.toMeasure_apply_fintype]
    rw [Fin.sum_univ_three]
    simp [counterexampleSourcePMF, counterexampleWeights, ENNReal.toReal_add, ENNReal.toReal_inv]
    norm_num

-- Proof sketch: choose two bivariate distribution functions whose rectangle increments satisfy the
-- two-dimensional positivity criterion, then use the four-dimensional inclusion-exclusion
-- criterion on a suitable box to show that the corresponding minimum fails to be a distribution
-- function on `ℝ⁴`.
/-- Exercise 1.5.5 (2): Item (ii). There exist distribution functions `F` and `G` on `ℝ²` such
that the function `(x, y) ↦ min (F x) (G y)` on `ℝ⁴`, obtained by splitting the four coordinates
into two blocks of length `2`, is not a distribution function on `ℝ⁴`. -/
theorem exists_twoDimensionalDistributionFunctions_whose_min_is_not_distributionFunction :
    ∃ F G : (Fin 2 → ℝ) → ℝ,
      IsFiniteDimensionalDistributionFunction F ∧
      IsFiniteDimensionalDistributionFunction G ∧
      ¬ IsFiniteDimensionalDistributionFunction
        (fun z : Fin 4 → ℝ ↦ min (F ![z 0, z 1]) (G ![z 2, z 3])) := by
  let F : (Fin 2 → ℝ) → ℝ :=
    fun z ↦ ((counterexampleSourcePMF.map counterexampleFirstMap).toMeasure).real (Set.Iic z)
  let G : (Fin 2 → ℝ) → ℝ :=
    fun z ↦ ((counterexampleSourcePMF.map counterexampleSecondMap).toMeasure).real (Set.Iic z)
  refine ⟨F, G, ?_, ?_, ?_⟩
  · -- The first witness is realized directly by the mapped three-atom law.
    refine ⟨⟨(counterexampleSourcePMF.map counterexampleFirstMap).toMeasure, inferInstance⟩, ?_⟩
    intro z
    rfl
  · -- The second witness is realized by the second mapped three-atom law.
    refine ⟨⟨(counterexampleSourcePMF.map counterexampleSecondMap).toMeasure, inferInstance⟩, ?_⟩
    intro z
    rfl
  · intro hMin
    have hFcorners : F ![1, 0] = 1 / 4 ∧ F ![1, 1] = 1 / 4 ∧ F ![2, 0] = 1 / 4 ∧
        F ![2, 1] = 1 / 2 := by
      simpa [F] using counterexampleFirstCornerValues
    have hGcorners : G ![0, 1] = 1 / 4 ∧ G ![0, 2] = 3 / 4 ∧ G ![1, 1] = 1 / 2 ∧
        G ![1, 2] = 1 := by
      simpa [G] using counterexampleSecondCornerValues
    rcases hFcorners with ⟨hF10, hF11, hF20, hF21⟩
    rcases hGcorners with ⟨hG01, hG02, hG11, hG12⟩
    have hab : (![1, 0, 0, 1] : Fin 4 → ℝ) ≤ ![2, 1, 1, 2] := by
      intro i
      fin_cases i <;> norm_num
    have hnonneg :
        0 ≤ fin4LowerOrthantIncrement
          (fun z : Fin 4 → ℝ ↦ min (F ![z 0, z 1]) (G ![z 2, z 3]))
          ![1, 0, 0, 1] ![2, 1, 1, 2] :=
      fin4LowerOrthantIncrement_nonneg (H := fun z : Fin 4 → ℝ ↦
        min (F ![z 0, z 1]) (G ![z 2, z 3])) hMin hab
    have hneg :
        fin4LowerOrthantIncrement
          (fun z : Fin 4 → ℝ ↦ min (F ![z 0, z 1]) (G ![z 2, z 3]))
          ![1, 0, 0, 1] ![2, 1, 1, 2] = -1 / 4 :=
      counterexampleSeparatedMinIncrement_eq_negQuarter
        (F := F) (G := G) hF10 hF11 hF20 hF21 hG01 hG02 hG11 hG12
    linarith

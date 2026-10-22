/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.UniformOn
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_20
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Example_12_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Example_12_22

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

local notation "P23" =>
  (ProbabilityTheory.uniformOn (Set.univ : Set (Fin 2 × Fin 2)) :
    Measure (Fin 2 × Fin 2))

-- Semantic search note: `lean_leansearch` recalls `ProbabilityTheory.CondIndep` as the
-- sigma-algebra-level owner. The chapter's source-facing surface is
-- `IsConditionallyIndependent`, with
-- `ProbabilityTheory.condIndepFun_iff_condIndep` as the random-variable bridge.

-- Proof sketch: the source item uses the concrete Bernoulli coordinate maps on `Fin 2 × Fin 2`
-- to show that conditional independence need not be monotone in the conditioning `σ`-algebra.
/-- Helper for Example 12.23: the first Bernoulli coordinate on `Fin 2 × Fin 2`, viewed as an
`ℝ`-valued random variable. -/
def firstBernoulliCoordinate : Fin 2 × Fin 2 → ℝ :=
  fun ω ↦ ω.1

/-- Helper for Example 12.23: the second Bernoulli coordinate on `Fin 2 × Fin 2`, viewed as an
`ℝ`-valued random variable. -/
def secondBernoulliCoordinate : Fin 2 × Fin 2 → ℝ :=
  fun ω ↦ ω.2

/-- Helper for Example 12.23: the first Bernoulli coordinate is measurable. -/
theorem measurable_firstBernoulliCoordinate : Measurable firstBernoulliCoordinate := by
  -- Proof comment: the domain is a finite discrete space, so every function is measurable.
  simpa [firstBernoulliCoordinate] using
    (Measurable.of_discrete : Measurable firstBernoulliCoordinate)

/-- Helper for Example 12.23: the second Bernoulli coordinate is measurable. -/
theorem measurable_secondBernoulliCoordinate : Measurable secondBernoulliCoordinate := by
  -- Proof comment: the second coordinate is also a function on a discrete finite space.
  simpa [secondBernoulliCoordinate] using
    (Measurable.of_discrete : Measurable secondBernoulliCoordinate)

/-- Helper for Example 12.23: the intermediate conditioning `σ`-algebra `σ(X + Y)` on the
Bernoulli product space. -/
abbrev bernoulliCoordinateSumConditioning : MeasurableSpace (Fin 2 × Fin 2) :=
  MeasurableSpace.comap (firstBernoulliCoordinate + secondBernoulliCoordinate) inferInstance

/-- Helper for Example 12.23: the larger conditioning `σ`-algebra `σ(X, Y)` on the Bernoulli
product space. -/
abbrev bernoulliCoordinatePairConditioning : MeasurableSpace (Fin 2 × Fin 2) :=
  MeasurableSpace.comap
    (fun ω ↦ (firstBernoulliCoordinate ω, secondBernoulliCoordinate ω)) inferInstance

/-- Helper for Example 12.23: every singleton of `Fin 2 × Fin 2` is measurable for `σ(X, Y)`. -/
private theorem measurableSet_singleton_pairConditioning (ω : Fin 2 × Fin 2) :
    MeasurableSet[bernoulliCoordinatePairConditioning] ({ω} : Set (Fin 2 × Fin 2)) := by
  refine ⟨
    {(firstBernoulliCoordinate ω, secondBernoulliCoordinate ω)},
    measurableSet_singleton _,
    ?_
  ⟩
  ext x
  constructor
  · intro hx
    rcases ω with ⟨i, j⟩
    rcases x with ⟨i', j'⟩
    fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
      simp [firstBernoulliCoordinate, secondBernoulliCoordinate] at hx ⊢
  · intro hx
    rcases ω with ⟨i, j⟩
    rcases x with ⟨i', j'⟩
    fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
      simp [firstBernoulliCoordinate, secondBernoulliCoordinate] at hx ⊢

/-- Helper for Example 12.23: on `Fin 2 × Fin 2`, the pair `(X, Y)` is the identity map, so
`σ(X, Y)` is the ambient measurable space. -/
theorem bernoulliCoordinatePairConditioning_eq :
    bernoulliCoordinatePairConditioning =
      (inferInstance : MeasurableSpace (Fin 2 × Fin 2)) := by
  refine le_antisymm ?_ ?_
  · -- Proof comment: the pair map is measurable from `σ(X, Y)` by construction.
    have hPair :
        Measurable (fun ω : Fin 2 × Fin 2 ↦
          (firstBernoulliCoordinate ω, secondBernoulliCoordinate ω)) := by
      fun_prop
    simpa [bernoulliCoordinatePairConditioning] using hPair.comap_le
  · letI : MeasurableSpace (Fin 2 × Fin 2) := bernoulliCoordinatePairConditioning
    letI : MeasurableSingletonClass (Fin 2 × Fin 2) :=
      ⟨fun ω ↦ by simpa using measurableSet_singleton_pairConditioning ω⟩
    intro s hs
    exact (Set.toFinite s).measurableSet

/-- Helper for Example 12.23: the uniform law on `Fin 2 × Fin 2` is unchanged when the ambient
measurable space is identified with `σ(X, Y)`. -/
private theorem pairConditioningUniformOn_eq :
    letI : MeasurableSpace (Fin 2 × Fin 2) := bernoulliCoordinatePairConditioning
    (ProbabilityTheory.uniformOn (Set.univ : Set (Fin 2 × Fin 2)) :
      Measure (Fin 2 × Fin 2)) = P23 := by
  rw [bernoulliCoordinatePairConditioning_eq]

/-- Helper for Example 12.23: `σ(X + Y)` is a sub-`σ`-algebra of `σ(X, Y)`. -/
theorem bernoulliCoordinateSumConditioning_le_pairConditioning :
    bernoulliCoordinateSumConditioning ≤ bernoulliCoordinatePairConditioning := by
  -- Proof comment: `X + Y` is a measurable function of the pair `(X, Y)`.
  have hpair :
      Measurable[bernoulliCoordinatePairConditioning]
        (fun ω ↦ (firstBernoulliCoordinate ω, secondBernoulliCoordinate ω)) :=
    Measurable.of_comap_le le_rfl
  exact ((measurable_fst.add measurable_snd).comp hpair).comap_le

/-- Helper for Example 12.23: `σ(X + Y)` is a sub-`σ`-algebra of the ambient measurable space. -/
theorem bernoulliCoordinateSumConditioning_le :
    bernoulliCoordinateSumConditioning ≤
      (inferInstance : MeasurableSpace (Fin 2 × Fin 2)) := by
  -- Proof comment: the sum map is measurable in the ambient discrete measurable space.
  simpa [bernoulliCoordinateSumConditioning] using
    ((measurable_firstBernoulliCoordinate.add measurable_secondBernoulliCoordinate).comap_le)

/-- Helper for Example 12.23: `σ(X, Y)` is a sub-`σ`-algebra of the ambient measurable space. -/
theorem bernoulliCoordinatePairConditioning_le :
    bernoulliCoordinatePairConditioning ≤
      (inferInstance : MeasurableSpace (Fin 2 × Fin 2)) := by
  -- Proof comment: the pair map is measurable because both coordinate projections are measurable.
  have hPair :
      Measurable (fun ω : Fin 2 × Fin 2 ↦
        (firstBernoulliCoordinate ω, secondBernoulliCoordinate ω)) := by
    fun_prop
  simpa [bernoulliCoordinatePairConditioning] using
    hPair.comap_le

/-- Helper for Example 12.23: the generated `σ`-algebras `σ(X)` and `σ(Y)` indexed by `Bool`. -/
abbrev bernoulliCoordinateGeneratedSubalgebras : Bool → MeasurableSpace (Fin 2 × Fin 2)
  | false => MeasurableSpace.comap firstBernoulliCoordinate inferInstance
  | true => MeasurableSpace.comap secondBernoulliCoordinate inferInstance

/-- Helper for Example 12.23: under `P23`, rectangle events for the two coordinates factor. -/
private theorem p23_preimage_inter_preimage_mul (s t : Set ℝ) :
    P23 (firstBernoulliCoordinate ⁻¹' s ∩ secondBernoulliCoordinate ⁻¹' t) =
      P23 (firstBernoulliCoordinate ⁻¹' s) * P23 (secondBernoulliCoordinate ⁻¹' t) := by
  classical
  let xs : Finset (Fin 2) := Finset.univ.filter fun i ↦ (i : ℝ) ∈ s
  let ys : Finset (Fin 2) := Finset.univ.filter fun j ↦ (j : ℝ) ∈ t
  let xySet : Set (Fin 2 × Fin 2) :=
    ((xs.product ys : Finset (Fin 2 × Fin 2)) : Set (Fin 2 × Fin 2))
  let xSet : Set (Fin 2 × Fin 2) :=
    ((xs.product (Finset.univ : Finset (Fin 2)) : Finset (Fin 2 × Fin 2)) :
      Set (Fin 2 × Fin 2))
  let ySet : Set (Fin 2 × Fin 2) :=
    (((Finset.univ : Finset (Fin 2)).product ys : Finset (Fin 2 × Fin 2)) :
      Set (Fin 2 × Fin 2))
  have hInter :
      firstBernoulliCoordinate ⁻¹' s ∩ secondBernoulliCoordinate ⁻¹' t =
        xySet := by
    ext ω
    simp [xySet, xs, ys, firstBernoulliCoordinate, secondBernoulliCoordinate]
  have hFirst :
      firstBernoulliCoordinate ⁻¹' s =
        xSet := by
    ext ω
    simp [xSet, xs, firstBernoulliCoordinate]
  have hSecond :
      secondBernoulliCoordinate ⁻¹' t =
        ySet := by
    ext ω
    simp [ySet, ys, secondBernoulliCoordinate]
  rw [hInter, hFirst, hSecond]
  change
    ((P23 : Measure (Fin 2 × Fin 2)) xySet) =
      ((P23 : Measure (Fin 2 × Fin 2)) xSet) * ((P23 : Measure (Fin 2 × Fin 2)) ySet)
  have hLeft :
      ((P23 : Measure (Fin 2 × Fin 2)) xySet) =
        (xs.card * ys.card : ENNReal) / (4 : ENNReal) := by
    change ProbabilityTheory.uniformOn (Set.univ : Set (Fin 2 × Fin 2)) xySet =
      (xs.card * ys.card : ENNReal) / (4 : ENNReal)
    simpa [xySet, Finset.card_product] using
      (ProbabilityTheory.uniformOn_apply_finset'
        (Finset.univ.measurableSet) (xs.product ys).measurableSet)
  have hLeftFirst :
      ((P23 : Measure (Fin 2 × Fin 2)) xSet) =
        (xs.card * 2 : ENNReal) / (4 : ENNReal) := by
    change ProbabilityTheory.uniformOn (Set.univ : Set (Fin 2 × Fin 2)) xSet =
      (xs.card * 2 : ENNReal) / (4 : ENNReal)
    simpa [xSet, Finset.card_product] using
      (ProbabilityTheory.uniformOn_apply_finset'
        (Finset.univ.measurableSet) (xs.product (Finset.univ : Finset (Fin 2))).measurableSet)
  have hLeftSecond :
      ((P23 : Measure (Fin 2 × Fin 2)) ySet) =
        (2 * ys.card : ENNReal) / (4 : ENNReal) := by
    change ProbabilityTheory.uniformOn (Set.univ : Set (Fin 2 × Fin 2)) ySet =
      (2 * ys.card : ENNReal) / (4 : ENNReal)
    simpa [ySet, Finset.card_product] using
      (ProbabilityTheory.uniformOn_apply_finset'
        (Finset.univ.measurableSet) ((Finset.univ : Finset (Fin 2)).product ys).measurableSet)
  rw [hLeft, hLeftFirst, hLeftSecond]
  have hxs : xs.card ≤ 2 := by
    simpa [xs] using
      (Finset.card_filter_le (Finset.univ : Finset (Fin 2)) fun i ↦ (i : ℝ) ∈ s)
  have hys : ys.card ≤ 2 := by
    simpa [ys] using
      (Finset.card_filter_le (Finset.univ : Finset (Fin 2)) fun j ↦ (j : ℝ) ∈ t)
  have hxs_cases : xs.card = 0 ∨ xs.card = 1 ∨ xs.card = 2 := by
    omega
  have hys_cases : ys.card = 0 ∨ ys.card = 1 ∨ ys.card = 2 := by
    omega
  rcases hxs_cases with hxs0 | hxs1 | hxs2
  · rw [hxs0]
    rcases hys_cases with hys0 | hys1 | hys2
    · rw [hys0]
      norm_num [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    · rw [hys1]
      norm_num [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    · rw [hys2]
      norm_num [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  · rw [hxs1]
    rcases hys_cases with hys0 | hys1 | hys2
    · rw [hys0]
      norm_num [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    · rw [hys1]
      have hx : (((1 : ENNReal) * 1) / 4) ≠ ⊤ := by
        exact
          (by
            finiteness :
              (((1 : ENNReal) * 1) / 4) < ⊤).ne
      have hy :
          (((1 : ENNReal) * 2) / 4 * (2 * (1 : ENNReal) / 4)) ≠ ⊤ := by
        exact
          (by
            finiteness :
              (((1 : ENNReal) * 2) / 4 * (2 * (1 : ENNReal) / 4)) < ⊤).ne
      simpa using (ENNReal.toReal_eq_toReal_iff' hx hy).mp (by
        norm_num [ENNReal.toReal_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      )
    · rw [hys2]
      have hx : (((1 : ENNReal) * 2) / 4) ≠ ⊤ := by
        exact
          (by
            finiteness :
              (((1 : ENNReal) * 2) / 4) < ⊤).ne
      have hy :
          (((1 : ENNReal) * 2) / 4 * (2 * (2 : ENNReal) / 4)) ≠ ⊤ := by
        exact
          (by
            finiteness :
              (((1 : ENNReal) * 2) / 4 * (2 * (2 : ENNReal) / 4)) < ⊤).ne
      simpa using (ENNReal.toReal_eq_toReal_iff' hx hy).mp (by
        norm_num [ENNReal.toReal_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      )
  · rw [hxs2]
    rcases hys_cases with hys0 | hys1 | hys2
    · rw [hys0]
      norm_num [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    · rw [hys1]
      have hx : (((2 : ENNReal) * 1) / 4) ≠ ⊤ := by
        exact
          (by
            finiteness :
              (((2 : ENNReal) * 1) / 4) < ⊤).ne
      have hy :
          (((2 : ENNReal) * 2) / 4 * (2 * (1 : ENNReal) / 4)) ≠ ⊤ := by
        exact
          (by
            finiteness :
              (((2 : ENNReal) * 2) / 4 * (2 * (1 : ENNReal) / 4)) < ⊤).ne
      simpa using (ENNReal.toReal_eq_toReal_iff' hx hy).mp (by
        norm_num [ENNReal.toReal_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      )
    · rw [hys2]
      have hx : (((2 : ENNReal) * 2) / 4) ≠ ⊤ := by
        exact
          (by
            finiteness :
              (((2 : ENNReal) * 2) / 4) < ⊤).ne
      have hy :
          (((2 : ENNReal) * 2) / 4 * (2 * (2 : ENNReal) / 4)) ≠ ⊤ := by
        exact
          (by
            finiteness :
              (((2 : ENNReal) * 2) / 4 * (2 * (2 : ENNReal) / 4)) < ⊤).ne
      simpa using (ENNReal.toReal_eq_toReal_iff' hx hy).mp (by
        norm_num [ENNReal.toReal_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      )

theorem indepFun_firstBernoulliCoordinate_secondBernoulliCoordinate :
    IndepFun firstBernoulliCoordinate secondBernoulliCoordinate P23 := by
  -- Proof comment: `IndepFun` reduces to factorization on rectangle events, which is exactly the
  -- finite four-point computation proved in `p23_preimage_inter_preimage_mul`.
  rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  exact p23_preimage_inter_preimage_mul s t

/-- Helper for Example 12.23: every singleton of the four-point Bernoulli space has positive
`P23`-mass. -/
private theorem p23_singleton_ne_zero (ω : Fin 2 × Fin 2) :
    P23 ({ω} : Set (Fin 2 × Fin 2)) ≠ 0 := by
  rcases ω with ⟨i, j⟩
  simp [ProbabilityTheory.uniformOn_univ]

/-- Helper for Example 12.23: every singleton of the four-point Bernoulli space has `P23`-mass
`1 / 4`. -/
private theorem p23_singleton_real (ω : Fin 2 × Fin 2) :
    (P23 : Measure (Fin 2 × Fin 2)).real ({ω} : Set (Fin 2 × Fin 2)) = (1 / 4 : ℝ) := by
  rcases ω with ⟨i, j⟩
  simp [Measure.real_def, ProbabilityTheory.uniformOn_univ]

/-- Helper for Example 12.23: an almost-sure equality holds pointwise at every singleton of
positive `P23`-mass. -/
private theorem ae_eq_at_of_singleton_ne_zero {α : Type*} {f g : Fin 2 × Fin 2 → α}
    {ω : Fin 2 × Fin 2} (hfg : f =ᵐ[P23] g)
    (hω : P23 ({ω} : Set (Fin 2 × Fin 2)) ≠ 0) :
    f ω = g ω := by
  by_contra hneq
  have hnull : P23 {x | f x ≠ g x} = 0 := by
    simpa [Filter.EventuallyEq, ae_iff] using hfg
  have hsubset : ({ω} : Set (Fin 2 × Fin 2)) ⊆ {x | f x ≠ g x} := by
    intro x hx
    simp [Set.mem_singleton_iff.mp hx, hneq]
  exact hω (measure_mono_null hsubset hnull)

/-- Helper for Example 12.23: the first Bernoulli coordinate is not almost
everywhere constant for the uniform law on `Fin 2 × Fin 2`. -/
theorem firstBernoulliCoordinate_not_ae_constant :
    ¬ ∃ c : ℝ, firstBernoulliCoordinate =ᵐ[P23] fun _ ↦ c := by
  rintro ⟨c, hc⟩
  have hnull : P23 {ω | firstBernoulliCoordinate ω ≠ c} = 0 := by
    simpa [Filter.EventuallyEq, ae_iff] using hc
  have h00 : firstBernoulliCoordinate ((0 : Fin 2), (0 : Fin 2)) = c := by
    by_contra hneq
    have hsubset :
        ({((0 : Fin 2), (0 : Fin 2))} : Set (Fin 2 × Fin 2)) ⊆
          {ω | firstBernoulliCoordinate ω ≠ c} := by
      intro ω hω
      simp [Set.mem_singleton_iff.mp hω, hneq]
    exact p23_singleton_ne_zero ((0 : Fin 2), (0 : Fin 2)) (measure_mono_null hsubset hnull)
  have h10 : firstBernoulliCoordinate ((1 : Fin 2), (0 : Fin 2)) = c := by
    by_contra hneq
    have hsubset :
        ({((1 : Fin 2), (0 : Fin 2))} : Set (Fin 2 × Fin 2)) ⊆
          {ω | firstBernoulliCoordinate ω ≠ c} := by
      intro ω hω
      simp [Set.mem_singleton_iff.mp hω, hneq]
    exact p23_singleton_ne_zero ((1 : Fin 2), (0 : Fin 2)) (measure_mono_null hsubset hnull)
  -- Proof comment: the two positive-mass points force the putative constant to be both `0` and `1`.
  norm_num [firstBernoulliCoordinate] at h00 h10
  linarith

/-- Helper for Example 12.23: the second Bernoulli coordinate is not almost
everywhere constant for the uniform law on `Fin 2 × Fin 2`. -/
theorem secondBernoulliCoordinate_not_ae_constant :
    ¬ ∃ c : ℝ, secondBernoulliCoordinate =ᵐ[P23] fun _ ↦ c := by
  rintro ⟨c, hc⟩
  have hnull : P23 {ω | secondBernoulliCoordinate ω ≠ c} = 0 := by
    simpa [Filter.EventuallyEq, ae_iff] using hc
  have h00 : secondBernoulliCoordinate ((0 : Fin 2), (0 : Fin 2)) = c := by
    by_contra hneq
    have hsubset :
        ({((0 : Fin 2), (0 : Fin 2))} : Set (Fin 2 × Fin 2)) ⊆
          {ω | secondBernoulliCoordinate ω ≠ c} := by
      intro ω hω
      simp [Set.mem_singleton_iff.mp hω, hneq]
    exact p23_singleton_ne_zero ((0 : Fin 2), (0 : Fin 2)) (measure_mono_null hsubset hnull)
  have h01 : secondBernoulliCoordinate ((0 : Fin 2), (1 : Fin 2)) = c := by
    by_contra hneq
    have hsubset :
        ({((0 : Fin 2), (1 : Fin 2))} : Set (Fin 2 × Fin 2)) ⊆
          {ω | secondBernoulliCoordinate ω ≠ c} := by
      intro ω hω
      simp [Set.mem_singleton_iff.mp hω, hneq]
    exact p23_singleton_ne_zero ((0 : Fin 2), (1 : Fin 2)) (measure_mono_null hsubset hnull)
  -- Proof comment: again two positive-mass points pin the coordinate to incompatible values.
  norm_num [secondBernoulliCoordinate] at h00 h01
  linarith

/-- Helper for Example 12.23: on the Bernoulli product space, the coordinate maps `X` and `Y`
are measurable and independent under the uniform law. -/
theorem bernoulliCoordinate_measurable_indepFun :
    Measurable firstBernoulliCoordinate ∧
      Measurable secondBernoulliCoordinate ∧
      IndepFun firstBernoulliCoordinate secondBernoulliCoordinate P23 := by
  -- Proof comment: package the three setup facts used repeatedly below.
  exact ⟨measurable_firstBernoulliCoordinate, measurable_secondBernoulliCoordinate,
    indepFun_firstBernoulliCoordinate_secondBernoulliCoordinate⟩

/-- Helper for Example 12.23: the Bernoulli coordinate maps `X` and `Y` are both nontrivial. -/
theorem bernoulliCoordinate_nontriviality :
    (¬ ∃ c : ℝ, firstBernoulliCoordinate =ᵐ[P23] fun _ ↦ c) ∧
      (¬ ∃ c : ℝ, secondBernoulliCoordinate =ᵐ[P23] fun _ ↦ c) := by
  -- Proof comment: combine the two one-coordinate nontriviality statements.
  exact ⟨firstBernoulliCoordinate_not_ae_constant, secondBernoulliCoordinate_not_ae_constant⟩

/-- Helper for Example 12.23: the generated `σ`-algebras of the two coordinates are independent
under the uniform law. -/
private theorem iIndep_bernoulliCoordinateGeneratedSubalgebras :
    iIndep bernoulliCoordinateGeneratedSubalgebras P23 := by
  let f : Bool → Fin 2 × Fin 2 → ℝ
    | false => firstBernoulliCoordinate
    | true => secondBernoulliCoordinate
  have hf : iIndepFun f P23 := by
    rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S sets hSets
    have hS : ∀ S : Finset Bool, S = ∅ ∨ S = {false} ∨ S = {true} ∨ S = {false, true} := by
      decide
    rcases hS S with rfl | rfl | rfl | rfl
    · -- Proof comment: the empty intersection and empty product both reduce to `1`.
      simp
    · -- Proof comment: a singleton family is independent for tautological reasons.
      simp
    · -- Proof comment: the other singleton case is identical.
      simp
    · -- Proof comment: the two-element family is the pairwise independence computation above.
      rw [Finset.set_biInter_insert, Finset.set_biInter_singleton, Finset.prod_insert,
        Finset.prod_singleton]
      · simpa [f, Set.inter_comm] using
          p23_preimage_inter_preimage_mul (sets false) (sets true)
      · simp
  -- Proof comment: the generated `σ`-algebras are exactly the comaps of the two coordinate maps.
  change
    iIndep
      (fun b ↦
        match b with
        | false => MeasurableSpace.comap firstBernoulliCoordinate inferInstance
        | true => MeasurableSpace.comap secondBernoulliCoordinate inferInstance)
      P23
  have hSpaces :
      (fun x ↦ MeasurableSpace.comap (f x) inferInstance) =
        (fun b ↦
          match b with
          | false => MeasurableSpace.comap firstBernoulliCoordinate inferInstance
          | true => MeasurableSpace.comap secondBernoulliCoordinate inferInstance) := by
    funext b
    cases b <;> rfl
  simpa [hSpaces] using hf.iIndep

/-- Helper for Example 12.23: each coordinate-generated `σ`-algebra lies below `σ(X, Y)`. -/
private theorem bernoulliCoordinateGeneratedSubalgebras_le_pairConditioning :
    ∀ b, bernoulliCoordinateGeneratedSubalgebras b ≤ bernoulliCoordinatePairConditioning := by
  intro b
  have hpair :
      Measurable[bernoulliCoordinatePairConditioning]
        (fun ω ↦ (firstBernoulliCoordinate ω, secondBernoulliCoordinate ω)) :=
    Measurable.of_comap_le le_rfl
  cases b
  · -- Proof comment: the first coordinate is obtained by composing the pair map with `Prod.fst`.
    simpa [bernoulliCoordinateGeneratedSubalgebras] using (measurable_fst.comp hpair).comap_le
  · -- Proof comment: the second coordinate is obtained by composing the pair map with `Prod.snd`.
    simpa [bernoulliCoordinateGeneratedSubalgebras] using (measurable_snd.comp hpair).comap_le

/-- Helper for Example 12.23: the conditioning `σ`-algebras satisfy
`⊥ ≤ σ(X + Y) ≤ σ(X, Y)`, and the generated `σ`-algebras `σ(X)` and `σ(Y)` are conditionally
independent given `⊥`. -/
theorem bernoulliCoordinate_conditionalIndependence_given_bot :
    ((⊥ : MeasurableSpace (Fin 2 × Fin 2)) ≤ bernoulliCoordinateSumConditioning) ∧
      bernoulliCoordinateSumConditioning ≤ bernoulliCoordinatePairConditioning ∧
      IsConditionallyIndependent (⊥ : MeasurableSpace (Fin 2 × Fin 2))
        bernoulliCoordinateGeneratedSubalgebras P23 := by
  have hAmbient :
      ∀ b, bernoulliCoordinateGeneratedSubalgebras b ≤
        (inferInstance : MeasurableSpace (Fin 2 × Fin 2)) := by
    intro b
    cases b
    · simpa [bernoulliCoordinateGeneratedSubalgebras] using
        measurable_firstBernoulliCoordinate.comap_le
    · simpa [bernoulliCoordinateGeneratedSubalgebras] using
        measurable_secondBernoulliCoordinate.comap_le
  -- Proof comment: Example 12.22 upgrades ordinary independence of the generated `σ`-algebras
  -- to conditional independence given the trivial `σ`-algebra.
  refine ⟨bot_le, bernoulliCoordinateSumConditioning_le_pairConditioning, ?_⟩
  exact
    isConditionallyIndependent_bot_of_iIndep
      hAmbient iIndep_bernoulliCoordinateGeneratedSubalgebras

/-- Helper for Example 12.23: conditioning on `σ(X, Y)` makes the factorization immediate because
both generated coordinate `σ`-algebras lie below `σ(X, Y)`. -/
theorem bernoulliCoordinate_conditionalIndependence_given_pair :
    IsConditionallyIndependent bernoulliCoordinatePairConditioning
      bernoulliCoordinateGeneratedSubalgebras P23 := by
  refine ⟨bernoulliCoordinatePairConditioning_le, ?_, ?_⟩
  · intro b
    exact (bernoulliCoordinateGeneratedSubalgebras_le_pairConditioning b).trans
      bernoulliCoordinatePairConditioning_le
  · intro s A hA
    -- Proof comment: Example 12.21 handles the case where each event is already measurable in the
    -- conditioning `σ`-algebra.
    exact condProb_biInter_eq_prod_of_subalgebras_le
      bernoulliCoordinatePairConditioning_le
      bernoulliCoordinateGeneratedSubalgebras
      bernoulliCoordinateGeneratedSubalgebras_le_pairConditioning
      P23 s hA

/-- Helper for Example 12.23: swapping the two Bernoulli coordinates preserves the uniform law on
the four-point space. -/
private theorem map_swap_p23_eq : Measure.map Prod.swap P23 = P23 := by
  -- Proof comment: `P23` is normalized counting measure on a finite set, and `Prod.swap` is a
  -- bijection, so it preserves the underlying counting measure.
  ext s hs
  rw [Measure.map_apply measurable_swap hs, ProbabilityTheory.uniformOn_univ,
    ProbabilityTheory.uniformOn_univ]
  have hpreimage : Prod.swap ⁻¹' s = Prod.swap '' s := by
    ext ω
    constructor
    · intro hω
      exact ⟨Prod.swap ω, hω, by simp⟩
    · rintro ⟨ω', hω', rfl⟩
      simpa using hω'
  rw [hpreimage]
  have hcount : Measure.count (Prod.swap '' s) = Measure.count s := by
    simpa using Measure.count_injective_image Prod.swap_injective s
  rw [hcount]

/-- Helper for Example 12.23: every `σ(X + Y)`-measurable event is invariant under swapping the
two Bernoulli coordinates. -/
private theorem sumConditioning_measurableSet_swapInvariant {S : Set (Fin 2 × Fin 2)}
    (hS : MeasurableSet[bernoulliCoordinateSumConditioning] S) :
    Prod.swap ⁻¹' S = S := by
  -- Proof comment: a `σ(X + Y)`-measurable set is the preimage of a Borel set under the sum map,
  -- and the sum map is unchanged by swapping the two coordinates.
  rcases hS with ⟨T, hT, rfl⟩
  ext ω
  simp [firstBernoulliCoordinate, secondBernoulliCoordinate, add_comm]

/-- Helper for Example 12.23: the zero-events of the first and second Bernoulli coordinates have
the same `P23`-mass against every `σ(X + Y)`-measurable test event. -/
private theorem measure_inter_firstZero_eq_secondZero_of_sumConditioningMeasurable
    {S : Set (Fin 2 × Fin 2)} (hS : MeasurableSet[bernoulliCoordinateSumConditioning] S) :
    P23 ({ω | firstBernoulliCoordinate ω = 0} ∩ S) =
      P23 ({ω | secondBernoulliCoordinate ω = 0} ∩ S) := by
  -- Proof comment: swapping turns `{X = 0}` into `{Y = 0}` and fixes every
  -- `σ(X + Y)`-measurable test event.
  have hFirstZero :
      Prod.swap ⁻¹' {ω : Fin 2 × Fin 2 | firstBernoulliCoordinate ω = 0} =
        {ω : Fin 2 × Fin 2 | secondBernoulliCoordinate ω = 0} := by
    ext ω
    simp [firstBernoulliCoordinate, secondBernoulliCoordinate]
  have hSwapS : Prod.swap ⁻¹' S = S := sumConditioning_measurableSet_swapInvariant hS
  have hMeas :
      MeasurableSet ({ω : Fin 2 × Fin 2 | firstBernoulliCoordinate ω = 0} ∩ S) := by
    simpa using
      (MeasurableSet.of_discrete :
        MeasurableSet ({ω : Fin 2 × Fin 2 | firstBernoulliCoordinate ω = 0} ∩ S))
  calc
    P23 ({ω | firstBernoulliCoordinate ω = 0} ∩ S) =
        Measure.map Prod.swap P23 ({ω | firstBernoulliCoordinate ω = 0} ∩ S) := by
      rw [map_swap_p23_eq]
    _ = P23 (Prod.swap ⁻¹' ({ω | firstBernoulliCoordinate ω = 0} ∩ S)) := by
      rw [Measure.map_apply measurable_swap hMeas]
    _ = P23 (Prod.swap ⁻¹' {ω | firstBernoulliCoordinate ω = 0} ∩ Prod.swap ⁻¹' S) := by
      rw [Set.preimage_inter]
    _ = P23 ({ω | secondBernoulliCoordinate ω = 0} ∩ S) := by
      rw [hFirstZero, hSwapS]

/-- Helper for Example 12.23: the conditional probabilities of the zero-events `{X = 0}` and
`{Y = 0}` agree almost surely given `σ(X + Y)`. -/
private theorem condProb_zeroEvents_equal_given_sumConditioning :
    P23⟦{ω | firstBernoulliCoordinate ω = 0} | bernoulliCoordinateSumConditioning⟧ =ᵐ[P23]
      P23⟦{ω | secondBernoulliCoordinate ω = 0} | bernoulliCoordinateSumConditioning⟧ := by
  let A : Set (Fin 2 × Fin 2) := {ω | firstBernoulliCoordinate ω = 0}
  let B : Set (Fin 2 × Fin 2) := {ω | secondBernoulliCoordinate ω = 0}
  have hAmeas : MeasurableSet A := by
    simpa [A] using (MeasurableSet.of_discrete : MeasurableSet A)
  have hBmeas : MeasurableSet B := by
    simpa [B] using (MeasurableSet.of_discrete : MeasurableSet B)
  have hAint : Integrable (A.indicator (fun _ ↦ (1 : ℝ))) P23 := by
    -- Proof comment: indicator functions of bounded events are integrable under the probability
    -- measure `P23`.
    exact (integrable_const 1).indicator hAmeas
  have hBint : Integrable (B.indicator (fun _ ↦ (1 : ℝ))) P23 := by
    -- Proof comment: the second zero-event has the same finite-measure integrability property.
    exact (integrable_const 1).indicator hBmeas
  have hEq :
      P23⟦B | bernoulliCoordinateSumConditioning⟧ =ᵐ[P23]
        P23⟦A | bernoulliCoordinateSumConditioning⟧ := by
    -- Proof comment: conditional expectation is characterized by matching integrals on all
    -- `σ(X + Y)`-measurable test events, and the swap symmetry identifies those test integrals.
    refine ae_eq_condExp_of_forall_setIntegral_eq bernoulliCoordinateSumConditioning_le hAint
      (fun s hs hμs ↦ integrable_condExp.integrableOn) ?_
      stronglyMeasurable_condExp.aestronglyMeasurable
    intro s hs hμs
    rw [setIntegral_condExp bernoulliCoordinateSumConditioning_le hBint hs]
    have hEqMeasure :
        P23 (A ∩ s) = P23 (B ∩ s) :=
      measure_inter_firstZero_eq_secondZero_of_sumConditioningMeasurable hs
    have hEqReal :
        (P23 : Measure (Fin 2 × Fin 2)).real (A ∩ s) =
          (P23 : Measure (Fin 2 × Fin 2)).real (B ∩ s) := by
      simpa [Measure.real_def] using congrArg ENNReal.toReal hEqMeasure
    calc
      ∫ x in s, B.indicator (fun _ ↦ (1 : ℝ)) x ∂P23 =
          (P23 : Measure (Fin 2 × Fin 2)).real (B ∩ s) := by
        simp [B, hBmeas, Set.inter_comm]
      _ = (P23 : Measure (Fin 2 × Fin 2)).real (A ∩ s) := hEqReal.symm
      _ = ∫ x in s, A.indicator (fun _ ↦ (1 : ℝ)) x ∂P23 := by
        simp [A, hAmeas, Set.inter_comm]
  -- Proof comment: swap the two sides back into the source-facing order of the theorem.
  simpa [A, B] using hEq.symm

/-- Helper for Example 12.23: a real-valued `σ(X + Y)`-measurable function takes the same value on
the two points of the sum-one fiber. -/
private theorem sumConditioning_measurable_eq_on_sumOneFiber {f : Fin 2 × Fin 2 → ℝ}
    (hf : Measurable[bernoulliCoordinateSumConditioning] f) :
    f ((0 : Fin 2), (1 : Fin 2)) = f ((1 : Fin 2), (0 : Fin 2)) := by
  -- Proof comment: the level set through `(0,1)` is `σ(X + Y)`-measurable, hence swap-invariant.
  let T : Set (Fin 2 × Fin 2) := {ω | f ω = f ((0 : Fin 2), (1 : Fin 2))}
  have hT : MeasurableSet[bernoulliCoordinateSumConditioning] T := by
    exact hf (measurableSet_singleton _)
  have hSwapT : Prod.swap ⁻¹' T = T := sumConditioning_measurableSet_swapInvariant hT
  have hMem : ((0 : Fin 2), (1 : Fin 2)) ∈ T := by
    simp [T]
  have hSwapMem : ((1 : Fin 2), (0 : Fin 2)) ∈ T := by
    have : ((1 : Fin 2), (0 : Fin 2)) ∈ Prod.swap ⁻¹' T := by
      simpa using hMem
    simpa [hSwapT] using this
  simpa [T] using hSwapMem.symm

/-- Helper for Example 12.23: conditional independence fails at the intermediate conditioning
`σ(X + Y)`. -/
theorem bernoulliCoordinate_not_conditionallyIndependent_given_sum :
    ¬ IsConditionallyIndependent bernoulliCoordinateSumConditioning
      bernoulliCoordinateGeneratedSubalgebras P23 := by
  -- Route correction: the negative half is attacked on the atom `{X + Y = 1}` using the swap
  -- symmetry `map_swap_p23_eq`, not by a nonexistent monotonicity theorem.
  intro hCond
  let A : Set (Fin 2 × Fin 2) := {ω | firstBernoulliCoordinate ω = 0}
  let B : Set (Fin 2 × Fin 2) := {ω | secondBernoulliCoordinate ω = 0}
  let C : Set (Fin 2 × Fin 2) := {ω | firstBernoulliCoordinate ω + secondBernoulliCoordinate ω = 1}
  let E : Bool → Set (Fin 2 × Fin 2)
    | false => A
    | true => B
  let pA : Fin 2 × Fin 2 → ℝ := P23⟦A | bernoulliCoordinateSumConditioning⟧
  let pB : Fin 2 × Fin 2 → ℝ := P23⟦B | bernoulliCoordinateSumConditioning⟧
  let pAB : Fin 2 × Fin 2 → ℝ := P23⟦A ∩ B | bernoulliCoordinateSumConditioning⟧
  have hAmeas : MeasurableSet A := by
    simpa [A] using (MeasurableSet.of_discrete : MeasurableSet A)
  have hBmeas : MeasurableSet B := by
    simpa [B] using (MeasurableSet.of_discrete : MeasurableSet B)
  have hABmeas : MeasurableSet (A ∩ B) := hAmeas.inter hBmeas
  have hAσ : MeasurableSet[bernoulliCoordinateGeneratedSubalgebras false] A := by
    refine ⟨{0}, measurableSet_singleton _, ?_⟩
    ext ω
    simp [A, firstBernoulliCoordinate]
  have hBσ : MeasurableSet[bernoulliCoordinateGeneratedSubalgebras true] B := by
    refine ⟨{0}, measurableSet_singleton _, ?_⟩
    ext ω
    simp [B, secondBernoulliCoordinate]
  have hCσ : MeasurableSet[bernoulliCoordinateSumConditioning] C := by
    refine ⟨{1}, measurableSet_singleton _, ?_⟩
    ext ω
    simp [C, firstBernoulliCoordinate, secondBernoulliCoordinate]
  have hCmeas : MeasurableSet C := by
    simpa [C] using (MeasurableSet.of_discrete : MeasurableSet C)
  let cFiber : Finset (Fin 2 × Fin 2) := {((0 : Fin 2), (1 : Fin 2)), ((1 : Fin 2), (0 : Fin 2))}
  have hCFiber : (cFiber : Set (Fin 2 × Fin 2)) = C := by
    ext ω
    rcases ω with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [cFiber, C, firstBernoulliCoordinate,
      secondBernoulliCoordinate]
  have hAint : Integrable (A.indicator (fun _ ↦ (1 : ℝ))) P23 := by
    -- Proof comment: event indicators are integrable under the probability measure `P23`.
    exact (integrable_const 1).indicator hAmeas
  have hBint : Integrable (B.indicator (fun _ ↦ (1 : ℝ))) P23 := by
    -- Proof comment: the second zero-event is handled identically.
    exact (integrable_const 1).indicator hBmeas
  have hABint : Integrable ((A ∩ B).indicator (fun _ ↦ (1 : ℝ))) P23 := by
    -- Proof comment: the intersection event is still bounded on a finite-measure space.
    exact (integrable_const 1).indicator hABmeas
  have hpAmeas : Measurable[bernoulliCoordinateSumConditioning] pA := by
    dsimp [pA]
    exact stronglyMeasurable_condExp.measurable
  have hpBmeas : Measurable[bernoulliCoordinateSumConditioning] pB := by
    dsimp [pB]
    exact stronglyMeasurable_condExp.measurable
  have hpABmeas : Measurable[bernoulliCoordinateSumConditioning] pAB := by
    dsimp [pAB]
    exact stronglyMeasurable_condExp.measurable
  have hpAFiber :
      pA ((0 : Fin 2), (1 : Fin 2)) = pA ((1 : Fin 2), (0 : Fin 2)) :=
    sumConditioning_measurable_eq_on_sumOneFiber hpAmeas
  have hpBFiber :
      pB ((0 : Fin 2), (1 : Fin 2)) = pB ((1 : Fin 2), (0 : Fin 2)) :=
    sumConditioning_measurable_eq_on_sumOneFiber hpBmeas
  have hpABFiber :
      pAB ((0 : Fin 2), (1 : Fin 2)) = pAB ((1 : Fin 2), (0 : Fin 2)) :=
    sumConditioning_measurable_eq_on_sumOneFiber hpABmeas
  have hEqPoint :
      pA ((0 : Fin 2), (1 : Fin 2)) = pB ((0 : Fin 2), (1 : Fin 2)) := by
    exact ae_eq_at_of_singleton_ne_zero
      (by simpa [A, B, pA, pB] using condProb_zeroEvents_equal_given_sumConditioning)
      (p23_singleton_ne_zero ((0 : Fin 2), (1 : Fin 2)))
  have hFactor :
      pAB =ᵐ[P23] fun ω ↦ pA ω * pB ω := by
    have hProd :
        P23⟦⋂ i ∈ ({false, true} : Finset Bool), E i | bernoulliCoordinateSumConditioning⟧ =ᵐ[P23]
          ∏ i ∈ ({false, true} : Finset Bool), P23⟦E i | bernoulliCoordinateSumConditioning⟧ := by
      exact hCond.2.2 ({false, true} : Finset Bool) fun i hi ↦ by
        cases i
        · simpa [E] using hAσ
        · simpa [E] using hBσ
    have hInterE :
        (⋂ i ∈ ({false, true} : Finset Bool), E i) = A ∩ B := by
      ext ω
      simp [E]
    rw [hInterE] at hProd
    have hProd' :
        P23⟦A ∩ B | bernoulliCoordinateSumConditioning⟧ =ᵐ[P23]
          (P23⟦A | bernoulliCoordinateSumConditioning⟧ *
            P23⟦B | bernoulliCoordinateSumConditioning⟧) := by
      simpa [E, Finset.prod_insert, Finset.prod_singleton] using hProd
    simpa [pA, pB, pAB, Pi.mul_apply] using hProd'
  have hFactorPoint :
      pAB ((0 : Fin 2), (1 : Fin 2)) =
        pA ((0 : Fin 2), (1 : Fin 2)) * pB ((0 : Fin 2), (1 : Fin 2)) := by
    exact ae_eq_at_of_singleton_ne_zero hFactor
      (p23_singleton_ne_zero ((0 : Fin 2), (1 : Fin 2)))
  have hIntegralA :
      ∫ x in C, pA x ∂P23 = (1 / 4 : ℝ) := by
    dsimp [pA]
    rw [setIntegral_condExp bernoulliCoordinateSumConditioning_le hAint hCσ]
    rw [← hCFiber, MeasureTheory.setIntegral_finset cFiber hAint.integrableOn]
    simp [cFiber, A, p23_singleton_real, firstBernoulliCoordinate]
  have hpAint : Integrable pA P23 := by
    dsimp [pA]
    exact integrable_condExp
  have hIntegralAConst :
      ∫ x in C, pA x ∂P23 = (1 / 2 : ℝ) * pA ((0 : Fin 2), (1 : Fin 2)) := by
    calc
      ∫ x in C, pA x ∂P23 =
          (1 / 4 : ℝ) * pA ((0 : Fin 2), (1 : Fin 2)) +
            (1 / 4 : ℝ) * pA ((1 : Fin 2), (0 : Fin 2)) := by
        rw [← hCFiber, MeasureTheory.setIntegral_finset cFiber hpAint.integrableOn]
        simp [cFiber, p23_singleton_real]
      _ = (1 / 2 : ℝ) * pA ((0 : Fin 2), (1 : Fin 2)) := by
        linarith [hpAFiber]
  have hpAValue :
      pA ((0 : Fin 2), (1 : Fin 2)) = (1 / 2 : ℝ) := by
    linarith
  have hpBValue :
      pB ((0 : Fin 2), (1 : Fin 2)) = (1 / 2 : ℝ) := by
    linarith
  have hIntegralAB :
      ∫ x in C, pAB x ∂P23 = (0 : ℝ) := by
    dsimp [pAB]
    rw [setIntegral_condExp bernoulliCoordinateSumConditioning_le hABint hCσ]
    rw [← hCFiber, MeasureTheory.setIntegral_finset cFiber hABint.integrableOn]
    simp [cFiber, A, B, p23_singleton_real, firstBernoulliCoordinate, secondBernoulliCoordinate]
  have hpABint : Integrable pAB P23 := by
    dsimp [pAB]
    exact integrable_condExp
  have hIntegralABConst :
      ∫ x in C, pAB x ∂P23 = (1 / 2 : ℝ) * pAB ((0 : Fin 2), (1 : Fin 2)) := by
    calc
      ∫ x in C, pAB x ∂P23 =
          (1 / 4 : ℝ) * pAB ((0 : Fin 2), (1 : Fin 2)) +
            (1 / 4 : ℝ) * pAB ((1 : Fin 2), (0 : Fin 2)) := by
        rw [← hCFiber, MeasureTheory.setIntegral_finset cFiber hpABint.integrableOn]
        simp [cFiber, p23_singleton_real]
      _ = (1 / 2 : ℝ) * pAB ((0 : Fin 2), (1 : Fin 2)) := by
        linarith [hpABFiber]
  have hpABZero :
      pAB ((0 : Fin 2), (1 : Fin 2)) = 0 := by
    linarith
  have hpABQuarter :
      pAB ((0 : Fin 2), (1 : Fin 2)) = (1 / 4 : ℝ) := by
    nlinarith [hFactorPoint, hpAValue, hpBValue]
  linarith

/-- Helper for Example 12.23: bundled witness properties for the failure of monotonicity of
conditional independence. -/
structure ConditionalIndependenceNotMonotoneWitness
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) : Prop where
  measurable_X : Measurable X
  measurable_Y : Measurable Y
  indepFun_X_Y : IndepFun X Y μ
  X_not_ae_constant : ¬ ∃ c : ℝ, X =ᵐ[μ] fun _ ↦ c
  Y_not_ae_constant : ¬ ∃ c : ℝ, Y =ᵐ[μ] fun _ ↦ c
  bot_le_sumConditioning :
    (⊥ : MeasurableSpace Ω) ≤ MeasurableSpace.comap (X + Y) inferInstance
  sumConditioning_le_pairConditioning :
    MeasurableSpace.comap (X + Y) inferInstance ≤
      MeasurableSpace.comap (fun ω ↦ (X ω, Y ω)) inferInstance
  condIndependent_given_bot :
    IsConditionallyIndependent (⊥ : MeasurableSpace Ω)
      (fun
        | false => MeasurableSpace.comap X inferInstance
        | true => MeasurableSpace.comap Y inferInstance) μ
  condIndependent_given_pair :
    IsConditionallyIndependent
      (MeasurableSpace.comap (fun ω ↦ (X ω, Y ω)) inferInstance)
      (fun
        | false => MeasurableSpace.comap X inferInstance
        | true => MeasurableSpace.comap Y inferInstance) μ
  not_condIndependent_given_sum :
    ¬ IsConditionallyIndependent
      (MeasurableSpace.comap (X + Y) inferInstance)
      (fun
        | false => MeasurableSpace.comap X inferInstance
        | true => MeasurableSpace.comap Y inferInstance) μ

/-- Example 12.23: there is no monotonicity for conditional independence with respect to the
conditioning `σ`-algebra. More precisely, there exists a probability space carrying nontrivial
independent real random variables `X` and `Y` such that, with `𝓕₁ = ⊥`,
`𝓕₂ = σ(X + Y)`, and `𝓕₃ = σ(X, Y)`, the generated `σ`-algebras `σ(X)` and `σ(Y)` are
conditionally independent given `𝓕₁` and given `𝓕₃`, but not given `𝓕₂`. -/
theorem bernoulliCoordinate_conditionalIndependence_not_monotone :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X Y : Ω → ℝ), ConditionalIndependenceNotMonotoneWitness Ω μ X Y := by
  refine ⟨Fin 2 × Fin 2, inferInstance, P23, inferInstance,
    firstBernoulliCoordinate, secondBernoulliCoordinate, ?_⟩
  rcases bernoulliCoordinate_measurable_indepFun with ⟨hX, hY, hIndep⟩
  rcases bernoulliCoordinate_nontriviality with ⟨hXnontrivial, hYnontrivial⟩
  rcases bernoulliCoordinate_conditionalIndependence_given_bot with ⟨h12, h23, hBot⟩
  refine
    ⟨hX, hY, hIndep, hXnontrivial, hYnontrivial, h12, h23, hBot,
      bernoulliCoordinate_conditionalIndependence_given_pair,
      bernoulliCoordinate_not_conditionallyIndependent_given_sum⟩

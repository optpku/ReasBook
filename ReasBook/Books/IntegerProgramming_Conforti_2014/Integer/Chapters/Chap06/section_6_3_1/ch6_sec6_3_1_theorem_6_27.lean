/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_14.ch2_sec2_14_exercise_2_23
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_definition_6_3_1_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_theorem_6_22
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_lemma_6_25
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_lemma_6_26

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: no deferred Lean semantic-search tool such as `lean_leansearch` was
-- available in this runner, so this file keeps the source-facing one-dimensional surface while
-- reusing the chapter's canonical `q = 1` pure-integer owners.

section Theorem627

open scoped IntegerVectorNotation

private def realAsR1 : ℝ ≃ (Fin 1 → ℝ) where
  toFun r := fun _ ↦ r
  invFun r := r 0
  left_inv r := rfl
  right_inv r := by
    ext i
    fin_cases i
    rfl

private abbrev scalarIntAssignmentEquiv : (ℝ →₀ ℤ) ≃ ((Fin 1 → ℝ) →₀ ℤ) :=
  Finsupp.equivCongrLeft realAsR1

private theorem scalarIntAssignmentEquiv_sum_apply_zero (x : ℝ →₀ ℤ) :
    (scalarIntAssignmentEquiv x).sum (fun r n ↦ (n : ℝ) * r 0) =
      x.sum (fun r n ↦ (n : ℝ) * r) := by
  rw [scalarIntAssignmentEquiv, Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_eq_mapDomain]
  rw [Finsupp.sum_mapDomain_index]
  · simp [realAsR1]
  · intro r
    simp
  · intro r m₁ m₂
    rw [Int.cast_add, add_mul]

private theorem pureIntegerBalance_scalarIntAssignmentEquiv_apply_zero
    (f : ℝ) (x : ℝ →₀ ℤ) :
    pure_integer_balance (fun _ : Fin 1 ↦ f) (scalarIntAssignmentEquiv x) 0 =
      f + x.sum (fun r n ↦ (n : ℝ) * r) := by
  rw [pure_integer_balance_apply, scalarIntAssignmentEquiv_sum_apply_zero]

/-- The one-dimensional pure integer infinite relaxation `G_f`, consisting of finitely supported
integer families with nonnegative coefficients whose weighted sum with `f` is integral. This is
the `q = 1` specialization of the chapter's canonical feasible-set owner. -/
abbrev pure_integer_feasible_set_on_R (f : ℝ) : Set (ℝ →₀ ℤ) :=
  scalarIntAssignmentEquiv ⁻¹' pure_integer_feasible_set (fun _ : Fin 1 ↦ f)

/-- Membership in `pure_integer_feasible_set_on_R f` is exactly the nonnegativity and
integrality condition from the one-dimensional pure integer infinite relaxation. -/
theorem mem_pure_integer_feasible_set_on_R_iff {f : ℝ} {x : ℝ →₀ ℤ} :
    x ∈ pure_integer_feasible_set_on_R f ↔
      (∀ r, 0 ≤ x r) ∧
        f + x.sum (fun r n ↦ (n : ℝ) * r) ∈ Set.range fun z : ℤ ↦ (z : ℝ) := by
  change scalarIntAssignmentEquiv x ∈ pure_integer_feasible_set (fun _ : Fin 1 ↦ f) ↔ _
  rw [mem_pure_integer_feasible_set_iff]
  constructor
  · intro hx
    rw [mem_integerVectors_iff_forall] at hx
    refine ⟨?_, ?_⟩
    · intro r
      simpa [scalarIntAssignmentEquiv, realAsR1] using hx.1 (realAsR1 r)
    · simpa [pureIntegerBalance_scalarIntAssignmentEquiv_apply_zero] using hx.2 0
  · rintro ⟨h_nonneg, h_lattice⟩
    refine ⟨?_, ?_⟩
    · intro r
      simpa [scalarIntAssignmentEquiv, realAsR1] using h_nonneg (r 0)
    · rw [mem_integerVectors_iff_forall]
      intro i
      fin_cases i
      simpa [pureIntegerBalance_scalarIntAssignmentEquiv_apply_zero] using h_lattice

/-- The one-dimensional valid-function notion is the `q = 1` specialization of the chapter's
canonical pure-integer valid-function owner. -/
abbrev pure_integer_valid_function_on_R (f : ℝ) (π : ℝ → ℝ) : Prop :=
  pure_integer_valid_function (fun _ : Fin 1 ↦ f) (fun r : Fin 1 → ℝ ↦ π (r 0))

/-- The one-dimensional minimal-valid-function notion is the `q = 1` specialization of the
chapter's canonical pure-integer minimal-valid-function owner. -/
abbrev pure_integer_minimal_valid_function_on_R (f : ℝ) (π : ℝ → ℝ) : Prop :=
  pure_integer_minimal_valid_function (fun _ : Fin 1 ↦ f) (fun r : Fin 1 → ℝ ↦ π (r 0))

/-- The one-dimensional extreme-valid-function notion is the `q = 1` specialization of the
chapter's canonical pure-integer extreme-valid-function owner. -/
abbrev pure_integer_extreme_valid_function_on_R (f : ℝ) (π : ℝ → ℝ) : Prop :=
  pure_integer_extreme_valid_function (fun _ : Fin 1 ↦ f) (fun r : Fin 1 → ℝ ↦ π (r 0))

/-- Unfolding the one-dimensional valid-function owner recovers the canonical `q = 1` chapter
owner. -/
theorem pure_integer_valid_function_on_R_iff {f : ℝ} {π : ℝ → ℝ} :
    pure_integer_valid_function_on_R f π ↔
      pure_integer_valid_function (fun _ : Fin 1 ↦ f) (fun r : Fin 1 → ℝ ↦ π (r 0)) :=
  Iff.rfl

/-- Unfolding the one-dimensional minimal-valid-function owner recovers the canonical `q = 1`
chapter owner. -/
theorem pure_integer_minimal_valid_function_on_R_iff {f : ℝ} {π : ℝ → ℝ} :
    pure_integer_minimal_valid_function_on_R f π ↔
      pure_integer_minimal_valid_function (fun _ : Fin 1 ↦ f) (fun r : Fin 1 → ℝ ↦ π (r 0)) :=
  Iff.rfl

/-- Unfolding the one-dimensional extreme-valid-function owner recovers the canonical `q = 1`
chapter owner. -/
theorem pure_integer_extreme_valid_function_on_R_iff {f : ℝ} {π : ℝ → ℝ} :
    pure_integer_extreme_valid_function_on_R f π ↔
      pure_integer_extreme_valid_function (fun _ : Fin 1 ↦ f) (fun r : Fin 1 → ℝ ↦ π (r 0)) :=
  Iff.rfl

/-- A minimal valid function on `ℝ` is valid. -/
instance pure_integer_minimal_valid_function_on_R_to_valid_function_on_R
    {f : ℝ} {π : ℝ → ℝ} [hπ : pure_integer_minimal_valid_function_on_R f π] :
    pure_integer_valid_function_on_R f π :=
  pure_integer_minimal_valid_function_to_valid_function

/-- Minimality on `ℝ` can be used through pointwise domination among valid functions. -/
theorem pure_integer_minimal_valid_function_on_R_eq_of_le
    {f : ℝ} {π π' : ℝ → ℝ} (hπ : pure_integer_minimal_valid_function_on_R f π)
    (hπ' : pure_integer_valid_function_on_R f π') (hle : ∀ r, π' r ≤ π r) :
    π' = π := by
  have hle' : ∀ r : Fin 1 → ℝ, π' (r 0) ≤ π (r 0) := fun r ↦ hle (r 0)
  have hEq :
      (fun r : Fin 1 → ℝ ↦ π' (r 0)) = fun r : Fin 1 → ℝ ↦ π (r 0) :=
    pure_integer_minimal_valid_function_eq_of_le hπ hπ' hle'
  ext r
  exact congrFun hEq (fun _ ↦ r)

/-- An extreme valid function on `ℝ` is valid. -/
instance pure_integer_extreme_valid_function_on_R_to_valid_function_on_R
    {f : ℝ} {π : ℝ → ℝ} [hπ : pure_integer_extreme_valid_function_on_R f π] :
    pure_integer_valid_function_on_R f π :=
  { nonneg := hπ.nonneg
    one_le_sum := hπ.one_le_sum }

namespace PiecewiseLinearOnInterval

/-- The interval breakpoints of a piecewise-linear witness are the piece endpoints that lie in the
ambient interval. -/
noncomputable def breakpoints {l u : ℝ} {π : ℝ → ℝ}
    (hπ : PiecewiseLinearOnInterval l u π) : Finset ℝ :=
  ((Finset.univ.image hπ.lower) ∪ Finset.univ.image hπ.upper).filter
    (fun x ↦ x ∈ Set.Icc l u)

/-- The affine pieces of a piecewise-linear witness use at most two distinct slopes. -/
def HasAtMostTwoSlopes {l u : ℝ} {π : ℝ → ℝ}
    (hπ : PiecewiseLinearOnInterval l u π) : Prop :=
  ∃ slope₁ slope₂ : ℝ, ∀ i, hπ.slope i = slope₁ ∨ hπ.slope i = slope₂

/-- Unfolding `HasAtMostTwoSlopes` exposes the two distinguished slopes. -/
theorem hasAtMostTwoSlopes_iff {l u : ℝ} {π : ℝ → ℝ}
    {hπ : PiecewiseLinearOnInterval l u π} :
    hπ.HasAtMostTwoSlopes ↔
      ∃ slope₁ slope₂ : ℝ, ∀ i, hπ.slope i = slope₁ ∨ hπ.slope i = slope₂ :=
  Iff.rfl

end PiecewiseLinearOnInterval

/-- The restriction of `π` to `[0, 1]` is continuous and piecewise linear with at most two
slopes. This is the source-facing hypothesis in Theorem 6.27, stated over the repository's
canonical interval piecewise-linear owner. -/
def ContinuousTwoSlopePiecewiseLinearOnUnitInterval (π : ℝ → ℝ) : Prop :=
  ContinuousOn π (Set.Icc (0 : ℝ) 1) ∧
    ∃ hpiece : PiecewiseLinearOnInterval 0 1 π, hpiece.HasAtMostTwoSlopes

/-- Unfolding the two-slope piecewise-linear hypothesis on `[0, 1]` recovers continuity together
with an interval piecewise-linear witness having at most two slopes. -/
theorem continuousTwoSlopePiecewiseLinearOnUnitInterval_iff {π : ℝ → ℝ} :
    ContinuousTwoSlopePiecewiseLinearOnUnitInterval π ↔
      ContinuousOn π (Set.Icc (0 : ℝ) 1) ∧
        ∃ hpiece : PiecewiseLinearOnInterval 0 1 π, hpiece.HasAtMostTwoSlopes :=
  Iff.rfl

/-- A continuous two-slope piecewise-linear function on `[0, 1]` is continuous on `[0, 1]`. -/
theorem ContinuousTwoSlopePiecewiseLinearOnUnitInterval.continuous
    {π : ℝ → ℝ} (hπ : ContinuousTwoSlopePiecewiseLinearOnUnitInterval π) :
    ContinuousOn π (Set.Icc (0 : ℝ) 1) :=
  hπ.1

/-- A continuous two-slope piecewise-linear function on `[0, 1]` admits a canonical interval
piecewise-linear witness with at most two slopes. -/
theorem ContinuousTwoSlopePiecewiseLinearOnUnitInterval.exists_piecewiseLinearOnInterval
    {π : ℝ → ℝ} (hπ : ContinuousTwoSlopePiecewiseLinearOnUnitInterval π) :
    ∃ hpiece : PiecewiseLinearOnInterval 0 1 π, hpiece.HasAtMostTwoSlopes :=
  hπ.2

/-- Helper for Theorem 6.27: a one-dimensional minimal valid function is `1`-periodic, has the
standard endpoint values, and is bounded on bounded intervals. -/
theorem pureIntegerMinimalValidFunctionOnR_periodicEndpoints
    {f : ℝ} {π : ℝ → ℝ}
    (hπ : pure_integer_minimal_valid_function_on_R f π) :
    Function.Periodic π 1 ∧
      π 0 = 0 ∧
        π 1 = 0 ∧
          π (1 - f) = 1 ∧
            BoundedOnBoundedIntervals π := by
  -- First package the scalar `1`-periodicity coming from integer periodicity in the canonical
  -- `Fin 1` owner.
  have hperiodicVec :
      integer_periodic_on_rn (fun r : Fin 1 → ℝ ↦ π (r 0)) :=
    pure_integer_minimal_valid_function_periodic hπ
  have hperiodic : Function.Periodic π 1 := by
    intro r
    simpa using (hperiodicVec (fun _ : Fin 1 ↦ r) (fun _ : Fin 1 ↦ (1 : ℤ))).symm
  have hzero : π 0 = 0 := by
    simpa using pure_integer_minimal_valid_function_zero_eq_zero hπ
  -- Read off the remaining distinguished values from periodicity and the `π (-f) = 1` identity.
  have hone : π 1 = 0 := by
    calc
      π 1 = π 0 := by simpa using hperiodic 0
      _ = 0 := hzero
  have hnegf : π (-f) = 1 := by
    simpa using pure_integer_minimal_valid_function_neg_f_eq_one hπ
  have honeMinusF : π (1 - f) = 1 := by
    calc
      π (1 - f) = π (-f) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hperiodic (-f)
      _ = 1 := hnegf
  have hbounded : BoundedOnBoundedIntervals π := by
    -- The scalar bridge inherits the global `[0, 1]` bound enjoyed by every minimal valid
    -- function, so every bounded interval has a uniform absolute-value bound.
    rw [boundedOnBoundedIntervals_iff]
    intro x y _hxy
    refine ⟨1, ?_⟩
    intro z hz
    have hz_nonneg : 0 ≤ π z := by
      simpa using hπ.nonneg (fun _ : Fin 1 ↦ z)
    have hz_le_one : π z ≤ 1 := by
      simpa using pure_integer_minimal_valid_function_le_one hπ (fun _ : Fin 1 ↦ z)
    exact abs_le.mpr ⟨by linarith, hz_le_one⟩
  exact ⟨hperiodic, hzero, hone, honeMinusF, hbounded⟩

/-- Helper for Theorem 6.27: the midpoint components of a one-dimensional minimal valid function
are again minimal valid functions. -/
theorem midpointComponentsAreMinimalValidFunctionOnR
    {f : ℝ} {π π₁ π₂ : ℝ → ℝ}
    (hπ : pure_integer_minimal_valid_function_on_R f π)
    (hπ₁ : pure_integer_valid_function_on_R f π₁)
    (hπ₂ : pure_integer_valid_function_on_R f π₂)
    (hmid : π = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) :
    pure_integer_minimal_valid_function_on_R f π₁ ∧
      pure_integer_minimal_valid_function_on_R f π₂ := by
  -- Transport the scalar midpoint identity once to the canonical `Fin 1` owner.
  have hmidVec :
      (fun r : Fin 1 → ℝ ↦ π (r 0)) =
        (1 / 2 : ℝ) • (fun r : Fin 1 → ℝ ↦ π₁ (r 0)) +
          (1 / 2 : ℝ) • (fun r : Fin 1 → ℝ ↦ π₂ (r 0)) := by
    ext r
    have hpoint := congrFun hmid (r 0)
    simpa [Pi.add_apply, Pi.smul_apply] using hpoint
  constructor
  · -- The left midpoint component stays minimal by Lemma 6.25.
    simpa using
      left_midpoint_component_is_minimal_valid_pure_integer_function hπ hπ₁ hπ₂ hmidVec
  · -- The right midpoint component is the symmetric companion case.
    simpa using
      right_midpoint_component_is_minimal_valid_pure_integer_function hπ hπ₁ hπ₂ hmidVec

/-- Helper for Theorem 6.27: scalar additivity of `π` transfers to both midpoint components once
the decomposition is rewritten in the canonical `Fin 1` owner. -/
theorem scalarMidpointAdditivityTransfer
    {f : ℝ} {π π₁ π₂ : ℝ → ℝ}
    (hπ : pure_integer_minimal_valid_function_on_R f π)
    (hπ₁ : pure_integer_valid_function_on_R f π₁)
    (hπ₂ : pure_integer_valid_function_on_R f π₂)
    (hmid : π = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) :
    ∀ ⦃a b : ℝ⦄, π a + π b = π (a + b) →
      π₁ a + π₁ b = π₁ (a + b) ∧
        π₂ a + π₂ b = π₂ (a + b) := by
  -- Rewrite the scalar midpoint decomposition and its additivity points in the `Fin 1` owner.
  have hmidVec :
      (fun r : Fin 1 → ℝ ↦ π (r 0)) =
        (1 / 2 : ℝ) • (fun r : Fin 1 → ℝ ↦ π₁ (r 0)) +
          (1 / 2 : ℝ) • (fun r : Fin 1 → ℝ ↦ π₂ (r 0)) := by
    ext r
    have hpoint := congrFun hmid (r 0)
    simpa [Pi.add_apply, Pi.smul_apply] using hpoint
  have haddSubset :=
    pure_integer_additivity_set_subset_of_midpoint_decomposition hπ hπ₁ hπ₂ hmidVec
  intro a b hadd
  have haddMem :
      ((fun _ : Fin 1 ↦ a), (fun _ : Fin 1 ↦ b)) ∈
        pure_integer_additivity_set (fun r : Fin 1 → ℝ ↦ π (r 0)) := by
    exact mem_pure_integer_additivity_set_iff.mpr (by simpa using hadd)
  have hcomponents := haddSubset haddMem
  rw [Set.mem_inter_iff] at hcomponents
  constructor
  · -- The first component inherits the same scalar additivity identity.
    simpa using mem_pure_integer_additivity_set_iff.mp hcomponents.1
  · -- The second component inherits the same scalar additivity identity.
    simpa using mem_pure_integer_additivity_set_iff.mp hcomponents.2

/-- Helper for Theorem 6.27: two `1`-periodic scalar functions that agree on `[0, 1]` agree
everywhere on `ℝ`. -/
theorem eq_of_eqOn_unitInterval_of_onePeriodic
    {φ ψ : ℝ → ℝ}
    (hφ : Function.Periodic φ 1)
    (hψ : Function.Periodic ψ 1)
    (heq : Set.EqOn φ ψ (Set.Icc (0 : ℝ) 1)) :
    φ = ψ := by
  -- Reduce every real input to its fractional part, where both functions can be compared inside
  -- the fundamental domain `[0, 1]`.
  ext x
  have hfract_mem : Int.fract x ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact Int.fract_nonneg x
    · exact le_of_lt (Int.fract_lt_one x)
  have hφ_shift : φ x = φ (Int.fract x) := by
    calc
      φ x = φ (Int.fract x + (Int.floor x : ℝ)) := by rw [Int.fract_add_floor]
      _ = φ (Int.fract x) := by
        simpa using (hφ.int_mul (Int.floor x) (Int.fract x))
  have hψ_shift : ψ x = ψ (Int.fract x) := by
    calc
      ψ x = ψ (Int.fract x + (Int.floor x : ℝ)) := by rw [Int.fract_add_floor]
      _ = ψ (Int.fract x) := by
        simpa using (hψ.int_mul (Int.floor x) (Int.fract x))
  calc
    φ x = φ (Int.fract x) := hφ_shift
    _ = ψ (Int.fract x) := heq hfract_mem
    _ = ψ x := hψ_shift.symm

/-- Helper for Theorem 6.27: augment the raw breakpoint set with the distinguished points
`0`, `1 - f`, and `1`. -/
private noncomputable def augmentedBreakpoints {π : ℝ → ℝ}
    (hpiece : PiecewiseLinearOnInterval 0 1 π) (f : ℝ) : Finset ℝ :=
  insert (1 - f) (insert 0 (insert 1 hpiece.breakpoints))

/-- Helper for Theorem 6.27: the augmented breakpoint set always contains the left endpoint. -/
private theorem zero_mem_augmentedBreakpoints
    {π : ℝ → ℝ} {f : ℝ} {hpiece : PiecewiseLinearOnInterval 0 1 π} :
    (0 : ℝ) ∈ augmentedBreakpoints hpiece f := by
  -- Insert the left endpoint explicitly so the ordered partition always starts at `0`.
  simp [augmentedBreakpoints]

/-- Helper for Theorem 6.27: the augmented breakpoint set always contains the right endpoint. -/
private theorem one_mem_augmentedBreakpoints
    {π : ℝ → ℝ} {f : ℝ} {hpiece : PiecewiseLinearOnInterval 0 1 π} :
    (1 : ℝ) ∈ augmentedBreakpoints hpiece f := by
  -- Insert the right endpoint explicitly so the ordered partition always ends at `1`.
  simp [augmentedBreakpoints]

/-- Helper for Theorem 6.27: the augmented breakpoint set contains the distinguished point
`1 - f`. -/
private theorem one_sub_f_mem_augmentedBreakpoints
    {π : ℝ → ℝ} {f : ℝ} {hpiece : PiecewiseLinearOnInterval 0 1 π} :
    1 - f ∈ augmentedBreakpoints hpiece f := by
  -- The split point is inserted explicitly into the augmented breakpoint owner.
  simp [augmentedBreakpoints]

/-- Helper for Theorem 6.27: every augmented breakpoint lies in the unit interval. -/
private theorem mem_augmentedBreakpoints_unitInterval
    {π : ℝ → ℝ} {f x : ℝ} (hf₀ : 0 < f) (hf₁ : f < 1)
    {hpiece : PiecewiseLinearOnInterval 0 1 π}
    (hx : x ∈ augmentedBreakpoints hpiece f) :
    x ∈ Set.Icc (0 : ℝ) 1 := by
  -- Peel off the three inserted distinguished points before falling back to the raw breakpoint
  -- interval-membership witness.
  rcases Finset.mem_insert.mp hx with rfl | hx
  · constructor <;> linarith
  rcases Finset.mem_insert.mp hx with rfl | hx
  · simp
  rcases Finset.mem_insert.mp hx with rfl | hx
  · simp
  exact (Finset.mem_filter.mp hx).2

/-- Helper for Theorem 6.27: the augmented breakpoint set has a canonical increasing
enumeration. -/
private noncomputable def augmentedBreakpointOrderEmb {π : ℝ → ℝ}
    (hpiece : PiecewiseLinearOnInterval 0 1 π) (f : ℝ) :
    Fin (augmentedBreakpoints hpiece f).card ↪o ℝ :=
  (augmentedBreakpoints hpiece f).orderEmbOfFin rfl

/-- Helper for Theorem 6.27: the augmented breakpoint order contains `1 - f`, which is the
combinatorial split point used in the boundary system. -/
private theorem splitIndexOfOneMinusF
    {π : ℝ → ℝ} {f : ℝ}
    {hpiece : PiecewiseLinearOnInterval 0 1 π} :
    ∃ split : Fin (augmentedBreakpoints hpiece f).card,
      augmentedBreakpointOrderEmb hpiece f split = 1 - f := by
  let s := augmentedBreakpoints hpiece f
  have hs_mem : 1 - f ∈ s := by
    simpa [s] using (one_sub_f_mem_augmentedBreakpoints (hpiece := hpiece) (f := f))
  have hs_range : 1 - f ∈ Set.range (augmentedBreakpointOrderEmb hpiece f) := by
    -- The canonical ordering enumerates the augmented breakpoint set exactly once.
    simpa [augmentedBreakpointOrderEmb, s, Finset.range_orderEmbOfFin] using hs_mem
  rcases hs_range with ⟨split, hsplit⟩
  exact ⟨split, hsplit⟩

/-- Helper for Theorem 6.27: the left endpoint of the `i`-th consecutive cell is the `i`-th point
of the ambient ordered breakpoint family. -/
private noncomputable def consecutiveLeft {n : ℕ} (hn : 0 < n) (i : Fin (n - 1)) : Fin n :=
  ⟨i, by omega⟩

/-- Helper for Theorem 6.27: the right endpoint of the `i`-th consecutive cell is the successor
point in the ambient ordered breakpoint family. -/
private noncomputable def consecutiveRight {n : ℕ} (hn : 0 < n) (i : Fin (n - 1)) : Fin n :=
  ⟨i + 1, by omega⟩

/-- Helper for Theorem 6.27: the left endpoint index of a consecutive cell has value `i`. -/
private theorem consecutiveLeft_val {n : ℕ} (hn : 0 < n) (i : Fin (n - 1)) :
    (consecutiveLeft hn i : ℕ) = i := by
  rfl

/-- Helper for Theorem 6.27: the right endpoint index of a consecutive cell has value `i + 1`. -/
private theorem consecutiveRight_val {n : ℕ} (hn : 0 < n) (i : Fin (n - 1)) :
    (consecutiveRight hn i : ℕ) = i + 1 := by
  rfl

/-- Helper for Theorem 6.27: the canonical increasing enumeration of a finite set has no member
strictly between consecutive indices. -/
private theorem no_mem_between_consecutive_orderEmbOfFin
    {s : Finset ℝ} (hs : 0 < s.card) {i : Fin (s.card - 1)} {x : ℝ}
    (hx : x ∈ s)
    (hleft : s.orderEmbOfFin rfl (consecutiveLeft hs i) < x)
    (hright : x < s.orderEmbOfFin rfl (consecutiveRight hs i)) :
    False := by
  -- Rewrite the intermediate point as one of the values of the canonical enumeration.
  have hxRange : x ∈ Set.range (s.orderEmbOfFin rfl) := by
    simpa [Finset.range_orderEmbOfFin] using hx
  rcases hxRange with ⟨j, rfl⟩
  -- Strict monotonicity pushes the interval inequalities back to index inequalities.
  have hij_left : (consecutiveLeft hs i : ℕ) < j := by
    exact (s.orderEmbOfFin rfl).strictMono.lt_iff_lt.mp hleft
  have hij_left' : (i : ℕ) < j := by
    simpa [consecutiveLeft_val] using hij_left
  have hij_right : (j : ℕ) < consecutiveRight hs i := by
    exact (s.orderEmbOfFin rfl).strictMono.lt_iff_lt.mp hright
  rw [consecutiveRight_val] at hij_right
  clear hij_left
  omega

/-- Helper for Theorem 6.27: the split index selecting `1 - f` in the augmented breakpoint
order is strictly between the first and last ordered breakpoints. -/
private theorem splitIndexBoundsOfOneMinusF
    {π : ℝ → ℝ} {f : ℝ} (hf₀ : 0 < f) (hf₁ : f < 1)
    {hpiece : PiecewiseLinearOnInterval 0 1 π}
    {split : Fin (augmentedBreakpoints hpiece f).card}
    (hsplit : augmentedBreakpointOrderEmb hpiece f split = 1 - f) :
    0 < (split : ℕ) ∧
      (split : ℕ) < (augmentedBreakpoints hpiece f).card - 1 := by
  let s := augmentedBreakpoints hpiece f
  let e := augmentedBreakpointOrderEmb hpiece f
  have hs_pos : 0 < s.card := by
    exact Finset.card_pos.mpr ⟨0, by simpa [s] using zero_mem_augmentedBreakpoints (hpiece := hpiece) (f := f)⟩
  have hs_nonempty : s.Nonempty := Finset.card_pos.mp hs_pos
  let first : Fin s.card := ⟨0, hs_pos⟩
  let last : Fin s.card := ⟨s.card - 1, Nat.sub_lt hs_pos (Nat.succ_pos 0)⟩
  have hzero_mem : (0 : ℝ) ∈ s := by
    simpa [s] using zero_mem_augmentedBreakpoints (hpiece := hpiece) (f := f)
  have hone_mem : (1 : ℝ) ∈ s := by
    simpa [s] using one_mem_augmentedBreakpoints (hpiece := hpiece) (f := f)
  have he_first : e first = 0 := by
    -- The first point in the increasing enumeration is the minimum augmented breakpoint.
    change s.orderEmbOfFin rfl first = 0
    rw [Finset.orderEmbOfFin_zero rfl hs_pos]
    apply le_antisymm
    · exact s.min'_le 0 hzero_mem
    · exact (mem_augmentedBreakpoints_unitInterval hf₀ hf₁
        (hpiece := hpiece) (s.min'_mem hs_nonempty)).1
  have he_last : e last = 1 := by
    -- The last point in the increasing enumeration is the maximum augmented breakpoint.
    change s.orderEmbOfFin rfl last = 1
    rw [Finset.orderEmbOfFin_last rfl hs_pos]
    apply le_antisymm
    · exact (mem_augmentedBreakpoints_unitInterval hf₀ hf₁
        (hpiece := hpiece) (s.max'_mem hs_nonempty)).2
    · exact s.le_max' 1 hone_mem
  have hfirst_lt_split : first < split := by
    -- Comparing the ordered values at `0` and `1 - f` shows that the split is not the first
    -- breakpoint.
    apply (e.strictMono.lt_iff_lt).mp
    rw [he_first, hsplit]
    exact sub_pos.mpr hf₁
  have hsplit_lt_last : split < last := by
    -- The split value lies strictly below the right endpoint `1`.
    apply (e.strictMono.lt_iff_lt).mp
    rw [hsplit, he_last]
    linarith
  constructor
  · simpa [first] using hfirst_lt_split
  · simpa [last, s] using hsplit_lt_last

/-- Helper for Theorem 6.27: the first point in the ordered augmented breakpoint family is `0`. -/
private theorem firstOrderedAugmentedBreakpoint_eq_zero
    {π : ℝ → ℝ} {f : ℝ} (hf₀ : 0 < f) (hf₁ : f < 1)
    (hpiece : PiecewiseLinearOnInterval 0 1 π) :
    let s := augmentedBreakpoints hpiece f
    let e := augmentedBreakpointOrderEmb hpiece f
    let hs_pos : 0 < s.card := by
      exact Finset.card_pos.mpr ⟨0, zero_mem_augmentedBreakpoints⟩
    e ⟨0, hs_pos⟩ = 0 := by
  let s := augmentedBreakpoints hpiece f
  let e := augmentedBreakpointOrderEmb hpiece f
  have hs_pos : 0 < s.card := by
    exact Finset.card_pos.mpr ⟨0, by simpa [s] using zero_mem_augmentedBreakpoints (hpiece := hpiece) (f := f)⟩
  have hs_nonempty : s.Nonempty := Finset.card_pos.mp hs_pos
  have hzero_mem : (0 : ℝ) ∈ s := by
    simpa [s] using zero_mem_augmentedBreakpoints (hpiece := hpiece) (f := f)
  -- The ordered enumeration starts at the minimum augmented breakpoint, and every augmented
  -- breakpoint lies in `[0, 1]`.
  change s.orderEmbOfFin rfl ⟨0, hs_pos⟩ = 0
  rw [Finset.orderEmbOfFin_zero rfl hs_pos]
  apply le_antisymm
  · exact s.min'_le 0 hzero_mem
  · exact (mem_augmentedBreakpoints_unitInterval hf₀ hf₁
      (hpiece := hpiece) (s.min'_mem hs_nonempty)).1

/-- Helper for Theorem 6.27: the last point in the ordered augmented breakpoint family is `1`. -/
private theorem lastOrderedAugmentedBreakpoint_eq_one
    {π : ℝ → ℝ} {f : ℝ} (hf₀ : 0 < f) (hf₁ : f < 1)
    (hpiece : PiecewiseLinearOnInterval 0 1 π) :
    let s := augmentedBreakpoints hpiece f
    let e := augmentedBreakpointOrderEmb hpiece f
    let hs_pos : 0 < s.card := by
      exact Finset.card_pos.mpr ⟨0, zero_mem_augmentedBreakpoints⟩
    e ⟨s.card - 1, Nat.sub_lt hs_pos (Nat.succ_pos 0)⟩ = 1 := by
  let s := augmentedBreakpoints hpiece f
  let e := augmentedBreakpointOrderEmb hpiece f
  have hs_pos : 0 < s.card := by
    exact Finset.card_pos.mpr ⟨0, by simpa [s] using zero_mem_augmentedBreakpoints (hpiece := hpiece) (f := f)⟩
  have hs_nonempty : s.Nonempty := Finset.card_pos.mp hs_pos
  have hone_mem : (1 : ℝ) ∈ s := by
    simpa [s] using one_mem_augmentedBreakpoints (hpiece := hpiece) (f := f)
  -- The ordered enumeration ends at the maximum augmented breakpoint, and every augmented
  -- breakpoint stays inside `[0, 1]`.
  change s.orderEmbOfFin rfl ⟨s.card - 1, Nat.sub_lt hs_pos (Nat.succ_pos 0)⟩ = 1
  rw [Finset.orderEmbOfFin_last rfl hs_pos]
  apply le_antisymm
  · exact (mem_augmentedBreakpoints_unitInterval hf₀ hf₁
      (hpiece := hpiece) (s.max'_mem hs_nonempty)).2
  · exact s.le_max' 1 hone_mem

/-- Helper for Theorem 6.27: once `1 - f` is inserted into the augmented breakpoint order, every
consecutive cell lies entirely on one side of the split point. -/
private theorem augmentedCellSideOfSplit
    {π : ℝ → ℝ} {f : ℝ} (hf₀ : 0 < f) (hf₁ : f < 1)
    {hpiece : PiecewiseLinearOnInterval 0 1 π}
    {split : Fin (augmentedBreakpoints hpiece f).card}
    (hsplit : augmentedBreakpointOrderEmb hpiece f split = 1 - f)
    (i : Fin ((augmentedBreakpoints hpiece f).card - 1)) :
    (((i : ℕ) < split →
        Set.Icc ((augmentedBreakpointOrderEmb hpiece f)
            (consecutiveLeft
              (by
                exact Finset.card_pos.mpr ⟨0, zero_mem_augmentedBreakpoints⟩)
              i))
            ((augmentedBreakpointOrderEmb hpiece f)
              (consecutiveRight
                (by
                  exact Finset.card_pos.mpr ⟨0, zero_mem_augmentedBreakpoints⟩)
                i)) ⊆
          Set.Icc (0 : ℝ) (1 - f))) ∧
      (((split : ℕ) ≤ i →
        Set.Icc ((augmentedBreakpointOrderEmb hpiece f)
            (consecutiveLeft
              (by
                exact Finset.card_pos.mpr ⟨0, zero_mem_augmentedBreakpoints⟩)
              i))
            ((augmentedBreakpointOrderEmb hpiece f)
              (consecutiveRight
                (by
                  exact Finset.card_pos.mpr ⟨0, zero_mem_augmentedBreakpoints⟩)
                i)) ⊆
          Set.Icc (1 - f) 1)) := by
  let s := augmentedBreakpoints hpiece f
  let e := augmentedBreakpointOrderEmb hpiece f
  have hs_pos : 0 < s.card := by
    exact Finset.card_pos.mpr ⟨0, by simpa [s] using zero_mem_augmentedBreakpoints (hpiece := hpiece) (f := f)⟩
  have hleft_mem :
      e (consecutiveLeft hs_pos i) ∈ s := by
    simpa [s, e, augmentedBreakpointOrderEmb] using
      Finset.orderEmbOfFin_mem s rfl (consecutiveLeft hs_pos i)
  have hright_mem :
      e (consecutiveRight hs_pos i) ∈ s := by
    simpa [s, e, augmentedBreakpointOrderEmb] using
      Finset.orderEmbOfFin_mem s rfl (consecutiveRight hs_pos i)
  constructor
  · intro hi
    intro x hx
    have hx_left := (mem_augmentedBreakpoints_unitInterval hf₀ hf₁ (hpiece := hpiece) hleft_mem).1
    have hright_le :
        e (consecutiveRight hs_pos i) ≤ 1 - f := by
      have hindex :
          consecutiveRight hs_pos i ≤ split := by
        rw [Fin.le_def, consecutiveRight_val]
        omega
      exact by simpa [e, hsplit] using e.monotone hindex
    exact ⟨hx_left.trans hx.1, hx.2.trans hright_le⟩
  · intro hi
    intro x hx
    have hleft_ge :
        1 - f ≤ e (consecutiveLeft hs_pos i) := by
      have hindex : split ≤ consecutiveLeft hs_pos i := by
        rw [Fin.le_def, consecutiveLeft_val]
        exact hi
      exact by simpa [e, hsplit] using e.monotone hindex
    have hx_right := (mem_augmentedBreakpoints_unitInterval hf₀ hf₁ (hpiece := hpiece) hright_mem).2
    exact ⟨hleft_ge.trans hx.1, hx.2.trans hx_right⟩

/-- Helper for Theorem 6.27: every point of `[0, 1]` lies in some consecutive augmented cell. -/
private theorem point_mem_some_augmentedCell
    {π : ℝ → ℝ} {f : ℝ} (hf₀ : 0 < f) (hf₁ : f < 1)
    (hpiece : PiecewiseLinearOnInterval 0 1 π) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ i : Fin ((augmentedBreakpoints hpiece f).card - 1),
      x ∈ Set.Icc ((augmentedBreakpointOrderEmb hpiece f)
          (consecutiveLeft
            (by
              exact Finset.card_pos.mpr ⟨0, zero_mem_augmentedBreakpoints⟩)
            i))
        ((augmentedBreakpointOrderEmb hpiece f)
          (consecutiveRight
            (by
              exact Finset.card_pos.mpr ⟨0, zero_mem_augmentedBreakpoints⟩)
            i)) := by
  let s := augmentedBreakpoints hpiece f
  let e := augmentedBreakpointOrderEmb hpiece f
  have hs_pos : 0 < s.card := by
    exact Finset.card_pos.mpr ⟨0, by simpa [s] using zero_mem_augmentedBreakpoints (hpiece := hpiece) (f := f)⟩
  have hzero_mem : (0 : ℝ) ∈ s := by
    simpa [s] using zero_mem_augmentedBreakpoints (hpiece := hpiece) (f := f)
  have hone_mem : (1 : ℝ) ∈ s := by
    simpa [s] using one_mem_augmentedBreakpoints (hpiece := hpiece) (f := f)
  have hs_card_gt_one : 1 < s.card := by
    refine Finset.one_lt_card.mpr ?_
    exact ⟨0, hzero_mem, 1, hone_mem, by norm_num⟩
  let first : Fin s.card := ⟨0, hs_pos⟩
  let last : Fin s.card := ⟨s.card - 1, Nat.sub_lt hs_pos (Nat.succ_pos 0)⟩
  have hs_nonempty : s.Nonempty := Finset.card_pos.mp hs_pos
  have he_first : e first = 0 := by
    -- The first ordered augmented breakpoint is the left endpoint.
    change s.orderEmbOfFin rfl first = 0
    rw [Finset.orderEmbOfFin_zero rfl hs_pos]
    apply le_antisymm
    · exact s.min'_le 0 hzero_mem
    · exact (mem_augmentedBreakpoints_unitInterval hf₀ hf₁
        (hpiece := hpiece) (s.min'_mem hs_nonempty)).1
  have he_last : e last = 1 := by
    -- The final ordered augmented breakpoint is the right endpoint.
    change s.orderEmbOfFin rfl last = 1
    rw [Finset.orderEmbOfFin_last rfl hs_pos]
    apply le_antisymm
    · exact (mem_augmentedBreakpoints_unitInterval hf₀ hf₁
        (hpiece := hpiece) (s.max'_mem hs_nonempty)).2
    · exact s.le_max' 1 hone_mem
  let P : ℕ → Prop := fun n ↦ ∃ hn : n < s.card, x ≤ e ⟨n, hn⟩
  have hP : ∃ n, P n := by
    refine ⟨s.card - 1, ?_⟩
    refine ⟨Nat.sub_lt hs_pos (Nat.succ_pos 0), ?_⟩
    simpa [P, e, last, he_last] using hx.2
  let kNat : ℕ := Nat.find hP
  have hkNat_spec : P kNat := Nat.find_spec hP
  rcases hkNat_spec with ⟨hkNat_lt, hk_right⟩
  let k : Fin s.card := ⟨kNat, hkNat_lt⟩
  by_cases hk_zero : kNat = 0
  · let i0 : Fin (s.card - 1) := ⟨0, by omega⟩
    have hleft_index : consecutiveLeft hs_pos i0 = first := by
      apply Fin.ext
      simp [first, i0, consecutiveLeft_val]
    have hleft_eq :
        e (consecutiveLeft hs_pos i0) = 0 := by
      simpa [hleft_index] using he_first
    have hfirst_lt_right : first < consecutiveRight hs_pos i0 := by
      rw [Fin.lt_def, consecutiveRight_val]
      simp [first, i0]
    have hright_pos : 0 < e (consecutiveRight hs_pos i0) := by
      have hmono := e.strictMono hfirst_lt_right
      simpa [he_first] using hmono
    have hx_zero : x = 0 := by
      have hx_le_zero : x ≤ 0 := by
        simpa [kNat, hk_zero, k, first, he_first] using hk_right
      linarith [hx.1, hx_le_zero]
    refine ⟨i0, ?_⟩
    subst hx_zero
    constructor
    · exact hleft_eq.le
    · exact le_of_lt hright_pos
  · let i : Fin (s.card - 1) := ⟨kNat - 1, by omega⟩
    have hk_pos : 0 < kNat := Nat.pos_of_ne_zero hk_zero
    have hright_index : consecutiveRight hs_pos i = k := by
      apply Fin.ext
      simp [i, k, consecutiveRight_val]
      omega
    have hleft_le :
        e (consecutiveLeft hs_pos i) ≤ x := by
      by_contra hleft_gt
      have hk_prev_lt_card : kNat - 1 < s.card := by
        have hk_prev_lt : kNat - 1 < kNat := by
          omega
        exact lt_trans hk_prev_lt hkNat_lt
      have hx_prev : x ≤ e ⟨kNat - 1, hk_prev_lt_card⟩ := by
        have hx_lt_left : x < e (consecutiveLeft hs_pos i) := lt_of_not_ge hleft_gt
        simpa [i, consecutiveLeft_val] using le_of_lt hx_lt_left
      have hk_min : kNat ≤ kNat - 1 := by
        exact Nat.find_min' hP ⟨hk_prev_lt_card, hx_prev⟩
      omega
    have hright_le :
        x ≤ e (consecutiveRight hs_pos i) := by
      simpa [hright_index, k] using hk_right
    exact ⟨i, ⟨hleft_le, hright_le⟩⟩

/-- Helper for Theorem 6.27: each consecutive cell of the augmented breakpoint order sits inside
one raw affine piece of the piecewise-linear witness. -/
private theorem augmentedCell_subset_piece
    {π : ℝ → ℝ} {f : ℝ}
    (hf₀ : 0 < f) (hf₁ : f < 1)
    (hpiece : PiecewiseLinearOnInterval 0 1 π)
    (i : Fin ((augmentedBreakpoints hpiece f).card - 1)) :
    ∃ j : Fin hpiece.pieces,
      Set.Icc ((augmentedBreakpointOrderEmb hpiece f)
          (consecutiveLeft
            (by
              exact Finset.card_pos.mpr ⟨0, zero_mem_augmentedBreakpoints⟩)
            i))
          ((augmentedBreakpointOrderEmb hpiece f)
            (consecutiveRight
              (by
                exact Finset.card_pos.mpr ⟨0, zero_mem_augmentedBreakpoints⟩)
              i)) ⊆
        Set.Icc (hpiece.lower j) (hpiece.upper j) := by
  let s := augmentedBreakpoints hpiece f
  have hs_pos : 0 < s.card := Finset.card_pos.mpr ⟨0, zero_mem_augmentedBreakpoints⟩
  let a : ℝ := (augmentedBreakpointOrderEmb hpiece f) (consecutiveLeft hs_pos i)
  let b : ℝ := (augmentedBreakpointOrderEmb hpiece f) (consecutiveRight hs_pos i)
  have ha_mem : a ∈ s := by
    -- The ordered enumeration only visits augmented breakpoints.
    simp [s, a, augmentedBreakpointOrderEmb]
  have hb_mem : b ∈ s := by
    -- The successor index gives the right endpoint of the current consecutive cell.
    simp [s, b, augmentedBreakpointOrderEmb]
  have ha_unit : a ∈ Set.Icc (0 : ℝ) 1 :=
    mem_augmentedBreakpoints_unitInterval hf₀ hf₁ (hpiece := hpiece) ha_mem
  have hb_unit : b ∈ Set.Icc (0 : ℝ) 1 :=
    mem_augmentedBreakpoints_unitInterval hf₀ hf₁ (hpiece := hpiece) hb_mem
  have hi_consecutive : consecutiveLeft hs_pos i < consecutiveRight hs_pos i := by
    rw [Fin.lt_def, consecutiveLeft_val, consecutiveRight_val]
    omega
  have hab : a < b := by
    -- Consecutive indices in the increasing enumeration produce a genuine open cell.
    simpa [a, b] using (augmentedBreakpointOrderEmb hpiece f).strictMono hi_consecutive
  let m : ℝ := (a + b) / 2
  have ham : a < m := by
    -- The midpoint lies strictly inside the consecutive cell.
    dsimp [m]
    linarith
  have hmb : m < b := by
    -- The same midpoint is also strictly below the right endpoint.
    dsimp [m]
    linarith
  have hm_unit : m ∈ Set.Icc (0 : ℝ) 1 := by
    -- Since both cell endpoints lie in `[0, 1]`, the midpoint stays inside the ambient interval.
    constructor
    · dsimp [m]
      nlinarith [ha_unit.1, hb_unit.1]
    · dsimp [m]
      nlinarith [ha_unit.2, hb_unit.2]
  have hm_cover := hpiece.cover hm_unit
  rw [Set.mem_iUnion] at hm_cover
  rcases hm_cover with ⟨j, hm_piece⟩
  have hlower_le_a : hpiece.lower j ≤ a := by
    by_contra hlower
    have ha_lower : a < hpiece.lower j := lt_of_not_ge hlower
    have hlower_unit : hpiece.lower j ∈ Set.Icc (0 : ℝ) 1 := by
      -- A lower endpoint that sits to the right of `a` must still lie in `[0, 1]` because it is
      -- below the interior midpoint of the cell.
      constructor
      · nlinarith [ha_unit.1, ha_lower]
      · nlinarith [hm_piece.1, hmb, hb_unit.2]
    have hlower_mem_breakpoints : hpiece.lower j ∈ hpiece.breakpoints := by
      -- Raw lower endpoints in `[0, 1]` are part of the breakpoint set by definition.
      refine Finset.mem_filter.mpr ?_
      refine ⟨?_, hlower_unit⟩
      exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_image.mpr ⟨j, by simp, rfl⟩
    have hlower_mem : hpiece.lower j ∈ s := by
      -- The augmented set contains every raw breakpoint in addition to the distinguished points.
      simp [s, augmentedBreakpoints, hlower_mem_breakpoints]
    exact no_mem_between_consecutive_orderEmbOfFin
      (s := s) hs_pos (i := i) (x := hpiece.lower j) hlower_mem
      (by simpa [s, a, augmentedBreakpointOrderEmb, consecutiveLeft] using ha_lower)
      (by exact lt_of_le_of_lt hm_piece.1 hmb)
  have hb_le_upper : b ≤ hpiece.upper j := by
    by_contra hupper
    have hupper_b : hpiece.upper j < b := lt_of_not_ge hupper
    have hupper_unit : hpiece.upper j ∈ Set.Icc (0 : ℝ) 1 := by
      -- A right endpoint that sits to the left of `b` still lies in `[0, 1]` because it is above
      -- the same interior midpoint.
      constructor
      · nlinarith [ha_unit.1, ham, hm_piece.2]
      · nlinarith [hb_unit.2, hupper_b]
    have hupper_mem_breakpoints : hpiece.upper j ∈ hpiece.breakpoints := by
      -- Raw upper endpoints in `[0, 1]` are also part of the breakpoint set by definition.
      refine Finset.mem_filter.mpr ?_
      refine ⟨?_, hupper_unit⟩
      exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_image.mpr ⟨j, by simp, rfl⟩
    have hupper_mem : hpiece.upper j ∈ s := by
      -- Reinsert the raw breakpoint into the augmented owner.
      simp [s, augmentedBreakpoints, hupper_mem_breakpoints]
    exact no_mem_between_consecutive_orderEmbOfFin
      (s := s) hs_pos (i := i) (x := hpiece.upper j) hupper_mem
      (by exact lt_of_lt_of_le ham hm_piece.2)
      (by simpa [s, b, augmentedBreakpointOrderEmb, consecutiveRight] using hupper_b)
  refine ⟨j, ?_⟩
  intro y hy
  -- Once both raw piece endpoints straddle the augmented cell, the whole closed cell sits inside
  -- that raw piece.
  exact ⟨le_trans hlower_le_a hy.1, le_trans hy.2 hb_le_upper⟩

/-- Helper for Theorem 6.27: each consecutive augmented cell inherits one raw affine formula from
the piecewise-linear witness. -/
private theorem cellAffineOfAugmentedPartition
    {π : ℝ → ℝ} {f : ℝ}
    (hf₀ : 0 < f) (hf₁ : f < 1)
    (hpiece : PiecewiseLinearOnInterval 0 1 π)
    (i : Fin ((augmentedBreakpoints hpiece f).card - 1)) :
    ∃ j : Fin hpiece.pieces,
      Set.EqOn π (fun x ↦ hpiece.slope j * x + hpiece.intercept j)
        (Set.Icc ((augmentedBreakpointOrderEmb hpiece f)
            (consecutiveLeft
              (by
                exact Finset.card_pos.mpr ⟨0, zero_mem_augmentedBreakpoints⟩)
              i))
          ((augmentedBreakpointOrderEmb hpiece f)
            (consecutiveRight
              (by
                exact Finset.card_pos.mpr ⟨0, zero_mem_augmentedBreakpoints⟩)
              i))) := by
  rcases augmentedCell_subset_piece hf₀ hf₁ hpiece i with ⟨j, hsubset⟩
  refine ⟨j, ?_⟩
  -- After locating the owning raw piece, read off its affine formula on the whole cell.
  intro x hx
  exact hpiece.eq_affine j x (hsubset hx)

/-- Helper for Theorem 6.27: the boundary two-equation system determines a unique slope pair once
the second row cannot be a nonnegative multiple of the first with opposite right-hand side. -/
private theorem slopePairUniqueOfBoundarySystem
    {LlPlus LlMinus LrPlus LrMinus : ℝ}
    (hLlPlus_pos : 0 < LlPlus)
    (hLrPlus_nonneg : 0 ≤ LrPlus)
    {sigmaPlus sigmaMinus tauPlus tauMinus : ℝ}
    (hsigma_left : LlPlus * sigmaPlus + LlMinus * sigmaMinus = 1)
    (hsigma_right : LrPlus * sigmaPlus + LrMinus * sigmaMinus = -1)
    (htau_left : LlPlus * tauPlus + LlMinus * tauMinus = 1)
    (htau_right : LrPlus * tauPlus + LrMinus * tauMinus = -1) :
    sigmaPlus = tauPlus ∧ sigmaMinus = tauMinus := by
  let det : ℝ := LlPlus * LrMinus - LrPlus * LlMinus
  have hdet_ne : det ≠ 0 := by
    intro hdet
    have hcross : LlPlus * LrMinus = LrPlus * LlMinus := by
      dsimp [det] at hdet
      linarith
    have hrow :
        LrMinus = (LrPlus / LlPlus) * LlMinus := by
      field_simp [hLlPlus_pos.ne']
      linarith
    have hcancel : (LrPlus / LlPlus) * LlPlus = LrPlus := by
      field_simp [hLlPlus_pos.ne']
    have hright_from_left : LrPlus * sigmaPlus + LrMinus * sigmaMinus = (LrPlus / LlPlus) := by
      -- Rewrite the right equation as a nonnegative multiple of the left equation.
      calc
        LrPlus * sigmaPlus + LrMinus * sigmaMinus
            = ((LrPlus / LlPlus) * LlPlus) * sigmaPlus
                + ((LrPlus / LlPlus) * LlMinus) * sigmaMinus := by
                  rw [hrow, hcancel]
        _ = (LrPlus / LlPlus) * (LlPlus * sigmaPlus + LlMinus * sigmaMinus) := by ring
        _ = LrPlus / LlPlus := by simp [hsigma_left]
    have hratio_nonneg : 0 ≤ LrPlus / LlPlus := div_nonneg hLrPlus_nonneg hLlPlus_pos.le
    have hratio_eq : LrPlus / LlPlus = -1 := by
      linarith [hsigma_right, hright_from_left]
    nlinarith [hratio_nonneg, hratio_eq]
  have hsigma_plus_formula : det * sigmaPlus = LrMinus + LlMinus := by
    -- Eliminating `sigmaMinus` leaves a single scalar equation for `sigmaPlus`.
    calc
      det * sigmaPlus
          = LrMinus * (LlPlus * sigmaPlus + LlMinus * sigmaMinus)
              - LlMinus * (LrPlus * sigmaPlus + LrMinus * sigmaMinus) := by
                dsimp [det]
                ring
      _ = LrMinus * 1 - LlMinus * (-1) := by rw [hsigma_left, hsigma_right]
      _ = LrMinus + LlMinus := by ring
  have htau_plus_formula : det * tauPlus = LrMinus + LlMinus := by
    -- The same elimination applies to the second slope pair.
    calc
      det * tauPlus
          = LrMinus * (LlPlus * tauPlus + LlMinus * tauMinus)
              - LlMinus * (LrPlus * tauPlus + LrMinus * tauMinus) := by
                dsimp [det]
                ring
      _ = LrMinus * 1 - LlMinus * (-1) := by rw [htau_left, htau_right]
      _ = LrMinus + LlMinus := by ring
  have hsigma_minus_formula : det * sigmaMinus = -(LlPlus + LrPlus) := by
    -- Eliminating `sigmaPlus` isolates the negative-slope parameter.
    calc
      det * sigmaMinus
          = LlPlus * (LrPlus * sigmaPlus + LrMinus * sigmaMinus)
              - LrPlus * (LlPlus * sigmaPlus + LlMinus * sigmaMinus) := by
                dsimp [det]
                ring
      _ = LlPlus * (-1) - LrPlus * 1 := by rw [hsigma_right, hsigma_left]
      _ = -(LlPlus + LrPlus) := by ring
  have htau_minus_formula : det * tauMinus = -(LlPlus + LrPlus) := by
    -- Apply the same elimination to the second solution.
    calc
      det * tauMinus
          = LlPlus * (LrPlus * tauPlus + LrMinus * tauMinus)
              - LrPlus * (LlPlus * tauPlus + LlMinus * tauMinus) := by
                dsimp [det]
                ring
      _ = LlPlus * (-1) - LrPlus * 1 := by rw [htau_right, htau_left]
      _ = -(LlPlus + LrPlus) := by ring
  have hplus_eq : sigmaPlus = tauPlus := by
    have hmul : det * (sigmaPlus - tauPlus) = 0 := by
      linarith [hsigma_plus_formula, htau_plus_formula]
    have hzero : sigmaPlus - tauPlus = 0 := by
      exact (mul_eq_zero.mp hmul).resolve_left hdet_ne
    linarith
  have hminus_eq : sigmaMinus = tauMinus := by
    have hmul : det * (sigmaMinus - tauMinus) = 0 := by
      linarith [hsigma_minus_formula, htau_minus_formula]
    have hzero : sigmaMinus - tauMinus = 0 := by
      exact (mul_eq_zero.mp hmul).resolve_left hdet_ne
    linarith
  exact ⟨hplus_eq, hminus_eq⟩

/-- Helper for Theorem 6.27: `1`-periodic affine data on `[a, b]` translates to the shifted
interval `[a + 1, b + 1]` with the same slope. -/
private theorem periodicEqOn_translateUnit
    {φ : ℝ → ℝ} (hperiodic : Function.Periodic φ 1)
    {a b sigma d : ℝ}
    (hbase : Set.EqOn φ (fun x ↦ sigma * x + d) (Set.Icc a b)) :
    Set.EqOn φ (fun x ↦ sigma * x + (d - sigma)) (Set.Icc (a + 1) (b + 1)) := by
  intro x hx
  have hx_base : x - 1 ∈ Set.Icc a b := by
    constructor <;> linarith [hx.1, hx.2]
  -- Shift the evaluation back by one period and rewrite the affine formula on the base interval.
  calc
    φ x = φ (x - 1) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hperiodic (x - 1)
    _ = sigma * (x - 1) + d := hbase hx_base
    _ = sigma * x + (d - sigma) := by ring

/-- Helper for Theorem 6.27: affine data on a unit translate descends back to the base interval
for `1`-periodic functions. -/
private theorem periodicEqOn_untranslateUnit
    {φ : ℝ → ℝ} (hperiodic : Function.Periodic φ 1)
    {a b sigma d : ℝ}
    (hshift : Set.EqOn φ (fun x ↦ sigma * x + d) (Set.Icc (a + 1) (b + 1))) :
    Set.EqOn φ (fun x ↦ sigma * x + (sigma + d)) (Set.Icc a b) := by
  intro x hx
  have hx_shift : x + 1 ∈ Set.Icc (a + 1) (b + 1) := by
    constructor <;> linarith [hx.1, hx.2]
  -- Compare the base point with its unit translate and then rewrite the translated affine model.
  calc
    φ x = φ (x + 1) := by simpa using (hperiodic x).symm
    _ = sigma * (x + 1) + d := hshift hx_shift
    _ = sigma * x + (sigma + d) := by ring

/-- Helper for Theorem 6.27: matching affine formulas with a common slope on `[0, ε]`,
`[a, b - ε]`, and `[a, b]` force additivity on the left transport rectangle. -/
private theorem affineAdditivityOnLeftRectangle
    {π : ℝ → ℝ} {a b ε sigma d : ℝ}
    (hε_nonneg : 0 ≤ ε)
    (hanchor : Set.EqOn π (fun x ↦ sigma * x) (Set.Icc (0 : ℝ) ε))
    (htarget : Set.EqOn π (fun x ↦ sigma * x + d) (Set.Icc a b))
    {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) ε)
    (hy : y ∈ Set.Icc a (b - ε)) :
    π x + π y = π (x + y) := by
  have hy_target : y ∈ Set.Icc a b := by
    constructor
    · exact hy.1
    · linarith [hy.2, hε_nonneg]
  have hxy : x + y ∈ Set.Icc a b := by
    constructor
    · linarith [hx.1, hy.1]
    · linarith [hx.2, hy.2]
  -- The common-slope affine formulas cancel to the source additivity identity.
  calc
    π x + π y = sigma * x + (sigma * y + d) := by rw [hanchor hx, htarget hy_target]
    _ = sigma * (x + y) + d := by ring
    _ = π (x + y) := by rw [htarget hxy]

/-- Helper for Theorem 6.27: the left-anchor rectangle plus Lemma 6.26 transport an affine model
of `π` to affine models of both midpoint components on the full target interval. -/
private theorem midpointComponentsAffineOnLeftSlopeInterval
    {f : ℝ} {π π₁ π₂ : ℝ → ℝ} {a b ε sigma d : ℝ}
    (hπ : pure_integer_minimal_valid_function_on_R f π)
    (hπ₁ : pure_integer_valid_function_on_R f π₁)
    (hπ₂ : pure_integer_valid_function_on_R f π₂)
    (hmid : π = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂)
    (hπ₁_bdd : BoundedOnBoundedIntervals π₁)
    (hπ₂_bdd : BoundedOnBoundedIntervals π₂)
    (hε_pos : 0 < ε)
    (hε_lt : ε < b - a)
    (hanchor : Set.EqOn π (fun x ↦ sigma * x) (Set.Icc (0 : ℝ) ε))
    (htarget : Set.EqOn π (fun x ↦ sigma * x + d) (Set.Icc a b)) :
    ∃ sigma₁ d₁ sigma₂ d₂,
      Set.EqOn π₁ (fun x ↦ sigma₁ * x + d₁) (Set.Icc a b) ∧
        Set.EqOn π₂ (fun x ↦ sigma₂ * x + d₂) (Set.Icc a b) := by
  let hadd_transfer := scalarMidpointAdditivityTransfer hπ hπ₁ hπ₂ hmid
  have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
  have hb : a < b - ε := by
    linarith
  have hab_sum :
      Set.Icc ((0 : ℝ) + a) (ε + (b - ε)) = Set.Icc a b := by
    ext x
    constructor
    · intro hx
      constructor <;> linarith [hx.1, hx.2]
    · intro hx
      constructor <;> linarith [hx.1, hx.2]
  have hπ_add :
      ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc (0 : ℝ) ε → y ∈ Set.Icc a (b - ε) →
        π x + π y = π (x + y) := by
    intro x y hx hy
    exact affineAdditivityOnLeftRectangle hε_nonneg hanchor htarget hx hy
  have hπ₁_add :
      ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc (0 : ℝ) ε → y ∈ Set.Icc a (b - ε) →
        π₁ x + π₁ y = π₁ (x + y) := by
    intro x y hx hy
    exact (hadd_transfer (hπ_add hx hy)).1
  have hπ₂_add :
      ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc (0 : ℝ) ε → y ∈ Set.Icc a (b - ε) →
        π₂ x + π₂ y = π₂ (x + y) := by
    intro x y hx hy
    exact (hadd_transfer (hπ_add hx hy)).2
  rcases interval_lemma_affine_with_common_slope hπ₁_bdd hε_pos hb
      (by
        intro x y hx hy
        exact hπ₁_add hx hy) with
    ⟨sigma₁, gA₁, gB₁, gAB₁, hgA₁, hgAeq₁, hgB₁, hgBeq₁, hgAB₁, hgABeq₁⟩
  rcases interval_lemma_affine_with_common_slope hπ₂_bdd hε_pos hb
      (by
        intro x y hx hy
        exact hπ₂_add hx hy) with
    ⟨sigma₂, gA₂, gB₂, gAB₂, hgA₂, hgAeq₂, hgB₂, hgBeq₂, hgAB₂, hgABeq₂⟩
  have hπ₁_affine :
      ∃ g : ℝ →ᵃ[ℝ] ℝ,
        g.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight sigma₁ ∧
          Set.EqOn π₁ g (Set.Icc a b) := by
    refine ⟨gAB₁, hgAB₁, ?_⟩
    simpa [hab_sum] using hgABeq₁
  have hπ₂_affine :
      ∃ g : ℝ →ᵃ[ℝ] ℝ,
        g.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight sigma₂ ∧
          Set.EqOn π₂ g (Set.Icc a b) := by
    refine ⟨gAB₂, hgAB₂, ?_⟩
    simpa [hab_sum] using hgABeq₂
  rcases (exists_affineMap_eqOn_iff (f := π₁) (s := Set.Icc a b) (c := sigma₁)).1 hπ₁_affine with
    ⟨d₁, hd₁⟩
  rcases (exists_affineMap_eqOn_iff (f := π₂) (s := Set.Icc a b) (c := sigma₂)).1 hπ₂_affine with
    ⟨d₂, hd₂⟩
  -- Convert the affine-map output of Lemma 6.26 immediately to intercept form on the target cell.
  exact ⟨sigma₁, d₁, sigma₂, d₂, hd₁, hd₂⟩

/-- Helper for Theorem 6.27: if the left anchor interval already has fixed midpoint-component
slopes, the same slopes propagate to the transported target interval. -/
private theorem midpointComponentsAffineOnLeftSlopeFamily
    {f : ℝ} {π π₁ π₂ : ℝ → ℝ} {a b ε sigma d sigma₁ sigma₂ : ℝ}
    (hπ : pure_integer_minimal_valid_function_on_R f π)
    (hπ₁ : pure_integer_valid_function_on_R f π₁)
    (hπ₂ : pure_integer_valid_function_on_R f π₂)
    (hmid : π = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂)
    (hπ₁_bdd : BoundedOnBoundedIntervals π₁)
    (hπ₂_bdd : BoundedOnBoundedIntervals π₂)
    (hε_pos : 0 < ε)
    (hε_lt : ε < b - a)
    (hanchor : Set.EqOn π (fun x ↦ sigma * x) (Set.Icc (0 : ℝ) ε))
    (htarget : Set.EqOn π (fun x ↦ sigma * x + d) (Set.Icc a b))
    (hπ₁_anchor : Set.EqOn π₁ (fun x ↦ sigma₁ * x) (Set.Icc (0 : ℝ) ε))
    (hπ₂_anchor : Set.EqOn π₂ (fun x ↦ sigma₂ * x) (Set.Icc (0 : ℝ) ε)) :
    ∃ d₁ d₂,
      Set.EqOn π₁ (fun x ↦ sigma₁ * x + d₁) (Set.Icc a b) ∧
        Set.EqOn π₂ (fun x ↦ sigma₂ * x + d₂) (Set.Icc a b) := by
  let hadd_transfer := scalarMidpointAdditivityTransfer hπ hπ₁ hπ₂ hmid
  have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
  have hb : a < b - ε := by
    linarith
  have hab_sum :
      Set.Icc ((0 : ℝ) + a) (ε + (b - ε)) = Set.Icc a b := by
    ext x
    constructor
    · intro hx
      constructor <;> linarith [hx.1, hx.2]
    · intro hx
      constructor <;> linarith [hx.1, hx.2]
  have hπ_add :
      ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc (0 : ℝ) ε → y ∈ Set.Icc a (b - ε) →
        π x + π y = π (x + y) := by
    intro x y hx hy
    exact affineAdditivityOnLeftRectangle hε_nonneg hanchor htarget hx hy
  have hπ₁_add :
      ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc (0 : ℝ) ε → y ∈ Set.Icc a (b - ε) →
        π₁ x + π₁ y = π₁ (x + y) := by
    intro x y hx hy
    exact (hadd_transfer (hπ_add hx hy)).1
  have hπ₂_add :
      ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc (0 : ℝ) ε → y ∈ Set.Icc a (b - ε) →
        π₂ x + π₂ y = π₂ (x + y) := by
    intro x y hx hy
    exact (hadd_transfer (hπ_add hx hy)).2
  rcases interval_lemma_affine_with_common_slope hπ₁_bdd hε_pos hb
      (by
        intro x y hx hy
        exact hπ₁_add hx hy) with
    ⟨tau₁, gA₁, gB₁, gAB₁, hgA₁, hgAeq₁, hgB₁, hgBeq₁, hgAB₁, hgABeq₁⟩
  rcases interval_lemma_affine_with_common_slope hπ₂_bdd hε_pos hb
      (by
        intro x y hx hy
        exact hπ₂_add hx hy) with
    ⟨tau₂, gA₂, gB₂, gAB₂, hgA₂, hgAeq₂, hgB₂, hgBeq₂, hgAB₂, hgABeq₂⟩
  have hπ₁_anchor_affine :
      ∃ g : ℝ →ᵃ[ℝ] ℝ,
        g.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight tau₁ ∧
          Set.EqOn π₁ g (Set.Icc (0 : ℝ) ε) := by
    refine ⟨gA₁, hgA₁, ?_⟩
    simpa using hgAeq₁
  have hπ₂_anchor_affine :
      ∃ g : ℝ →ᵃ[ℝ] ℝ,
        g.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight tau₂ ∧
          Set.EqOn π₂ g (Set.Icc (0 : ℝ) ε) := by
    refine ⟨gA₂, hgA₂, ?_⟩
    simpa using hgAeq₂
  rcases (exists_affineMap_eqOn_iff (f := π₁) (s := Set.Icc (0 : ℝ) ε) (c := tau₁)).1
      hπ₁_anchor_affine with ⟨e₁, he₁⟩
  rcases (exists_affineMap_eqOn_iff (f := π₂) (s := Set.Icc (0 : ℝ) ε) (c := tau₂)).1
      hπ₂_anchor_affine with ⟨e₂, he₂⟩
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) ε := by
    simp [hε_nonneg]
  have hε_mem : ε ∈ Set.Icc (0 : ℝ) ε := by
    simp [hε_nonneg]
  have he₁_zero : e₁ = 0 := by
    -- Comparing the interval-lemma affine model with the fixed anchor formula at `0` kills the
    -- intercept on the anchor interval.
    have hleft := he₁ hzero_mem
    have hright := hπ₁_anchor hzero_mem
    linarith
  have he₂_zero : e₂ = 0 := by
    -- The same anchor-point normalization identifies the second intercept.
    have hleft := he₂ hzero_mem
    have hright := hπ₂_anchor hzero_mem
    linarith
  have htau₁_eq : tau₁ = sigma₁ := by
    -- Evaluating both anchor formulas at `ε > 0` identifies the common slope.
    have hleft := he₁ hε_mem
    have hright := hπ₁_anchor hε_mem
    have hmul : (tau₁ - sigma₁) * ε = 0 := by
      linarith [hleft, hright, he₁_zero]
    have hdiff : tau₁ - sigma₁ = 0 := by
      exact (mul_eq_zero.mp hmul).resolve_right hε_pos.ne'
    linarith
  have htau₂_eq : tau₂ = sigma₂ := by
    -- The second midpoint component has the same rigidity on the left anchor.
    have hleft := he₂ hε_mem
    have hright := hπ₂_anchor hε_mem
    have hmul : (tau₂ - sigma₂) * ε = 0 := by
      linarith [hleft, hright, he₂_zero]
    have hdiff : tau₂ - sigma₂ = 0 := by
      exact (mul_eq_zero.mp hmul).resolve_right hε_pos.ne'
    linarith
  have hπ₁_target_affine :
      ∃ g : ℝ →ᵃ[ℝ] ℝ,
        g.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight tau₁ ∧
          Set.EqOn π₁ g (Set.Icc a b) := by
    refine ⟨gAB₁, hgAB₁, ?_⟩
    simpa [hab_sum] using hgABeq₁
  have hπ₂_target_affine :
      ∃ g : ℝ →ᵃ[ℝ] ℝ,
        g.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight tau₂ ∧
          Set.EqOn π₂ g (Set.Icc a b) := by
    refine ⟨gAB₂, hgAB₂, ?_⟩
    simpa [hab_sum] using hgABeq₂
  rcases (exists_affineMap_eqOn_iff (f := π₁) (s := Set.Icc a b) (c := tau₁)).1
      hπ₁_target_affine with ⟨d₁, hd₁⟩
  rcases (exists_affineMap_eqOn_iff (f := π₂) (s := Set.Icc a b) (c := tau₂)).1
      hπ₂_target_affine with ⟨d₂, hd₂⟩
  refine ⟨d₁, d₂, ?_, ?_⟩
  · -- Replace the anonymous transported slope by the fixed left-anchor slope.
    intro x hx
    simpa [htau₁_eq] using hd₁ hx
  · -- Apply the same slope identification to the second midpoint component.
    intro x hx
    simpa [htau₂_eq] using hd₂ hx

/-- Helper for Theorem 6.27: matching affine formulas on a right anchor interval and a target
cell force additivity after translating the sum back by one period. -/
private theorem affineAdditivityOnRightRectangle
    {π : ℝ → ℝ} (hperiodic : Function.Periodic π 1)
    {a b ε sigma d : ℝ}
    (htarget : Set.EqOn π (fun x ↦ sigma * x + d) (Set.Icc a b))
    (hanchor : Set.EqOn π (fun x ↦ sigma * x - sigma) (Set.Icc (1 - ε) 1))
    {x y : ℝ}
    (hx : x ∈ Set.Icc (a + ε) b)
    (hy : y ∈ Set.Icc (1 - ε) 1) :
    π x + π y = π (x + y) := by
  have hε_nonneg : 0 ≤ ε := by
    linarith [hy.1, hy.2]
  have hx_target : x ∈ Set.Icc a b := by
    constructor
    · linarith [hx.1, hε_nonneg]
    · exact hx.2
  have hxy_target : x + y - 1 ∈ Set.Icc a b := by
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  -- Rewrite the sum point back by one period so both source affine formulas live on base
  -- intervals with the same slope.
  calc
    π x + π y = (sigma * x + d) + (sigma * y - sigma) := by
      rw [htarget hx_target, hanchor hy]
    _ = sigma * (x + y - 1) + d := by ring
    _ = π (x + y - 1) := by rw [htarget hxy_target]
    _ = π (x + y) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (hperiodic (x + y - 1)).symm

/-- Helper for Theorem 6.27: the right-anchor rectangle plus Lemma 6.26 transport an affine
model of `π` to affine models of both midpoint components on the full target interval. -/
private theorem midpointComponentsAffineOnRightSlopeInterval
    {f : ℝ} {π π₁ π₂ : ℝ → ℝ} {a b ε sigma d : ℝ}
    (hπ : pure_integer_minimal_valid_function_on_R f π)
    (hπ₁ : pure_integer_valid_function_on_R f π₁)
    (hπ₂ : pure_integer_valid_function_on_R f π₂)
    (hmid : π = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂)
    (hπ_periodic : Function.Periodic π 1)
    (hπ₁_periodic : Function.Periodic π₁ 1)
    (hπ₂_periodic : Function.Periodic π₂ 1)
    (hπ₁_bdd : BoundedOnBoundedIntervals π₁)
    (hπ₂_bdd : BoundedOnBoundedIntervals π₂)
    (hε_pos : 0 < ε)
    (hε_lt : ε < b - a)
    (htarget : Set.EqOn π (fun x ↦ sigma * x + d) (Set.Icc a b))
    (hanchor : Set.EqOn π (fun x ↦ sigma * x - sigma) (Set.Icc (1 - ε) 1)) :
    ∃ sigma₁ d₁ sigma₂ d₂,
      Set.EqOn π₁ (fun x ↦ sigma₁ * x + d₁) (Set.Icc a b) ∧
        Set.EqOn π₂ (fun x ↦ sigma₂ * x + d₂) (Set.Icc a b) := by
  let hadd_transfer := scalarMidpointAdditivityTransfer hπ hπ₁ hπ₂ hmid
  have hab : a + ε < b := by
    linarith
  have hright_lt : 1 - ε < 1 := by
    linarith [hε_pos]
  have hπ_add :
      ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc (a + ε) b → y ∈ Set.Icc (1 - ε) 1 →
        π x + π y = π (x + y) := by
    intro x y hx hy
    exact affineAdditivityOnRightRectangle hπ_periodic htarget hanchor hx hy
  have hπ₁_add :
      ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc (a + ε) b → y ∈ Set.Icc (1 - ε) 1 →
        π₁ x + π₁ y = π₁ (x + y) := by
    intro x y hx hy
    exact (hadd_transfer (hπ_add hx hy)).1
  have hπ₂_add :
      ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc (a + ε) b → y ∈ Set.Icc (1 - ε) 1 →
        π₂ x + π₂ y = π₂ (x + y) := by
    intro x y hx hy
    exact (hadd_transfer (hπ_add hx hy)).2
  rcases interval_lemma_affine_with_common_slope hπ₁_bdd hab hright_lt
      (by
        intro x y hx hy
        exact hπ₁_add hx hy) with
    ⟨sigma₁, gA₁, gB₁, gAB₁, hgA₁, hgAeq₁, hgB₁, hgBeq₁, hgAB₁, hgABeq₁⟩
  rcases interval_lemma_affine_with_common_slope hπ₂_bdd hab hright_lt
      (by
        intro x y hx hy
        exact hπ₂_add hx hy) with
    ⟨sigma₂, gA₂, gB₂, gAB₂, hgA₂, hgAeq₂, hgB₂, hgBeq₂, hgAB₂, hgABeq₂⟩
  have hπ₁_shift_affine :
      ∃ g : ℝ →ᵃ[ℝ] ℝ,
        g.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight sigma₁ ∧
          Set.EqOn π₁ g (Set.Icc (a + 1) (b + 1)) := by
    refine ⟨gAB₁, hgAB₁, ?_⟩
    simpa [add_assoc, add_left_comm, add_comm] using hgABeq₁
  have hπ₂_shift_affine :
      ∃ g : ℝ →ᵃ[ℝ] ℝ,
        g.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight sigma₂ ∧
          Set.EqOn π₂ g (Set.Icc (a + 1) (b + 1)) := by
    refine ⟨gAB₂, hgAB₂, ?_⟩
    simpa [add_assoc, add_left_comm, add_comm] using hgABeq₂
  rcases (exists_affineMap_eqOn_iff (f := π₁) (s := Set.Icc (a + 1) (b + 1)) (c := sigma₁)).1
      hπ₁_shift_affine with ⟨d₁', hd₁'⟩
  rcases (exists_affineMap_eqOn_iff (f := π₂) (s := Set.Icc (a + 1) (b + 1)) (c := sigma₂)).1
      hπ₂_shift_affine with ⟨d₂', hd₂'⟩
  refine ⟨sigma₁, sigma₁ + d₁', sigma₂, sigma₂ + d₂', ?_, ?_⟩
  · -- Pull the shifted affine model back by one period to recover an intercept form on `[a, b]`.
    intro x hx
    have hbase := periodicEqOn_untranslateUnit hπ₁_periodic hd₁' hx
    simpa [add_assoc, add_left_comm, add_comm] using hbase
  · -- Apply the same untranslation to the second midpoint component.
    intro x hx
    have hbase := periodicEqOn_untranslateUnit hπ₂_periodic hd₂' hx
    simpa [add_assoc, add_left_comm, add_comm] using hbase

/-- Helper for Theorem 6.27: if the right anchor interval already has fixed midpoint-component
slopes, the translated Interval Lemma transport preserves those slopes on the target interval. -/
private theorem midpointComponentsAffineOnRightSlopeFamily
    {f : ℝ} {π π₁ π₂ : ℝ → ℝ} {a b ε sigma d sigma₁ sigma₂ : ℝ}
    (hπ : pure_integer_minimal_valid_function_on_R f π)
    (hπ₁ : pure_integer_valid_function_on_R f π₁)
    (hπ₂ : pure_integer_valid_function_on_R f π₂)
    (hmid : π = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂)
    (hπ_periodic : Function.Periodic π 1)
    (hπ₁_periodic : Function.Periodic π₁ 1)
    (hπ₂_periodic : Function.Periodic π₂ 1)
    (hπ₁_bdd : BoundedOnBoundedIntervals π₁)
    (hπ₂_bdd : BoundedOnBoundedIntervals π₂)
    (hε_pos : 0 < ε)
    (hε_lt : ε < b - a)
    (htarget : Set.EqOn π (fun x ↦ sigma * x + d) (Set.Icc a b))
    (hanchor : Set.EqOn π (fun x ↦ sigma * x - sigma) (Set.Icc (1 - ε) 1))
    (hπ₁_anchor : Set.EqOn π₁ (fun x ↦ sigma₁ * x - sigma₁) (Set.Icc (1 - ε) 1))
    (hπ₂_anchor : Set.EqOn π₂ (fun x ↦ sigma₂ * x - sigma₂) (Set.Icc (1 - ε) 1)) :
    ∃ d₁ d₂,
      Set.EqOn π₁ (fun x ↦ sigma₁ * x + d₁) (Set.Icc a b) ∧
        Set.EqOn π₂ (fun x ↦ sigma₂ * x + d₂) (Set.Icc a b) := by
  let hadd_transfer := scalarMidpointAdditivityTransfer hπ hπ₁ hπ₂ hmid
  have hab : a + ε < b := by
    linarith
  have hright_lt : 1 - ε < 1 := by
    linarith [hε_pos]
  have hπ_add :
      ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc (a + ε) b → y ∈ Set.Icc (1 - ε) 1 →
        π x + π y = π (x + y) := by
    intro x y hx hy
    exact affineAdditivityOnRightRectangle hπ_periodic htarget hanchor hx hy
  have hπ₁_add :
      ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc (a + ε) b → y ∈ Set.Icc (1 - ε) 1 →
        π₁ x + π₁ y = π₁ (x + y) := by
    intro x y hx hy
    exact (hadd_transfer (hπ_add hx hy)).1
  have hπ₂_add :
      ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc (a + ε) b → y ∈ Set.Icc (1 - ε) 1 →
        π₂ x + π₂ y = π₂ (x + y) := by
    intro x y hx hy
    exact (hadd_transfer (hπ_add hx hy)).2
  rcases interval_lemma_affine_with_common_slope hπ₁_bdd hab hright_lt
      (by
        intro x y hx hy
        exact hπ₁_add hx hy) with
    ⟨tau₁, gA₁, gB₁, gAB₁, hgA₁, hgAeq₁, hgB₁, hgBeq₁, hgAB₁, hgABeq₁⟩
  rcases interval_lemma_affine_with_common_slope hπ₂_bdd hab hright_lt
      (by
        intro x y hx hy
        exact hπ₂_add hx hy) with
    ⟨tau₂, gA₂, gB₂, gAB₂, hgA₂, hgAeq₂, hgB₂, hgBeq₂, hgAB₂, hgABeq₂⟩
  have hπ₁_anchor_affine :
      ∃ g : ℝ →ᵃ[ℝ] ℝ,
        g.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight tau₁ ∧
          Set.EqOn π₁ g (Set.Icc (1 - ε) 1) := by
    refine ⟨gB₁, hgB₁, ?_⟩
    simpa using hgBeq₁
  have hπ₂_anchor_affine :
      ∃ g : ℝ →ᵃ[ℝ] ℝ,
        g.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight tau₂ ∧
          Set.EqOn π₂ g (Set.Icc (1 - ε) 1) := by
    refine ⟨gB₂, hgB₂, ?_⟩
    simpa using hgBeq₂
  rcases (exists_affineMap_eqOn_iff (f := π₁) (s := Set.Icc (1 - ε) 1) (c := tau₁)).1
      hπ₁_anchor_affine with ⟨e₁, he₁⟩
  rcases (exists_affineMap_eqOn_iff (f := π₂) (s := Set.Icc (1 - ε) 1) (c := tau₂)).1
      hπ₂_anchor_affine with ⟨e₂, he₂⟩
  have hone_mem : (1 : ℝ) ∈ Set.Icc (1 - ε) 1 := by
    simp [le_of_lt hε_pos]
  have hleft_mem : 1 - ε ∈ Set.Icc (1 - ε) 1 := by
    simp [le_of_lt hε_pos]
  have he₁_eq : e₁ = -tau₁ := by
    -- Evaluating at `1` normalizes the intercept to the stable right-anchor form.
    have hleft := he₁ hone_mem
    have hright := hπ₁_anchor hone_mem
    linarith
  have he₂_eq : e₂ = -tau₂ := by
    -- The same endpoint normalization applies to the second midpoint component.
    have hleft := he₂ hone_mem
    have hright := hπ₂_anchor hone_mem
    linarith
  have htau₁_eq : tau₁ = sigma₁ := by
    -- Comparing both formulas at the left end of the anchor interval identifies the slope.
    have hleft := he₁ hleft_mem
    have hright := hπ₁_anchor hleft_mem
    have hmul : (tau₁ - sigma₁) * ε = 0 := by
      linarith [hleft, hright, he₁_eq]
    have hdiff : tau₁ - sigma₁ = 0 := by
      exact (mul_eq_zero.mp hmul).resolve_right hε_pos.ne'
    linarith
  have htau₂_eq : tau₂ = sigma₂ := by
    -- The second midpoint component has the same right-anchor rigidity.
    have hleft := he₂ hleft_mem
    have hright := hπ₂_anchor hleft_mem
    have hmul : (tau₂ - sigma₂) * ε = 0 := by
      linarith [hleft, hright, he₂_eq]
    have hdiff : tau₂ - sigma₂ = 0 := by
      exact (mul_eq_zero.mp hmul).resolve_right hε_pos.ne'
    linarith
  have hπ₁_shift_affine :
      ∃ g : ℝ →ᵃ[ℝ] ℝ,
        g.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight tau₁ ∧
          Set.EqOn π₁ g (Set.Icc (a + 1) (b + 1)) := by
    refine ⟨gAB₁, hgAB₁, ?_⟩
    simpa [add_assoc, add_left_comm, add_comm] using hgABeq₁
  have hπ₂_shift_affine :
      ∃ g : ℝ →ᵃ[ℝ] ℝ,
        g.linear = (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight tau₂ ∧
          Set.EqOn π₂ g (Set.Icc (a + 1) (b + 1)) := by
    refine ⟨gAB₂, hgAB₂, ?_⟩
    simpa [add_assoc, add_left_comm, add_comm] using hgABeq₂
  rcases (exists_affineMap_eqOn_iff (f := π₁) (s := Set.Icc (a + 1) (b + 1)) (c := tau₁)).1
      hπ₁_shift_affine with ⟨d₁', hd₁'⟩
  rcases (exists_affineMap_eqOn_iff (f := π₂) (s := Set.Icc (a + 1) (b + 1)) (c := tau₂)).1
      hπ₂_shift_affine with ⟨d₂', hd₂'⟩
  refine ⟨tau₁ + d₁', tau₂ + d₂', ?_, ?_⟩
  · -- Pull the shifted affine model back by one period before replacing the anonymous slope.
    intro x hx
    have hbase := periodicEqOn_untranslateUnit hπ₁_periodic hd₁' hx
    simpa [htau₁_eq, add_assoc, add_left_comm, add_comm] using hbase
  · -- Apply the same untranslation and slope identification to the second component.
    intro x hx
    have hbase := periodicEqOn_untranslateUnit hπ₂_periodic hd₂' hx
    simpa [htau₂_eq, add_assoc, add_left_comm, add_comm] using hbase

/-- Helper for Theorem 6.27: an affine formula on a nonempty closed interval turns endpoint
differences into the slope times the interval length. -/
private theorem affineIncrement_eq_smul_sub
    {φ : ℝ → ℝ} {a b sigma d : ℝ} (hab : a ≤ b)
    (hφ : Set.EqOn φ (fun x ↦ sigma * x + d) (Set.Icc a b)) :
    φ b - φ a = sigma * (b - a) := by
  have ha : a ∈ Set.Icc a b := by
    simp [hab]
  have hb : b ∈ Set.Icc a b := by
    simp [hab]
  -- Evaluate the affine model at both endpoints and cancel the intercept.
  have hleft := hφ ha
  have hright := hφ hb
  linarith

/-- Helper for Theorem 6.27: two affine formulas with the same slope agree on an interval as soon
as they agree at one anchor point in that interval. -/
private theorem eqOn_of_sharedAffineSlope_and_pointValue
    {φ ψ : ℝ → ℝ} {a b anchor sigma dφ dψ : ℝ}
    (hanchor : anchor ∈ Set.Icc a b)
    (hφ : Set.EqOn φ (fun x ↦ sigma * x + dφ) (Set.Icc a b))
    (hψ : Set.EqOn ψ (fun x ↦ sigma * x + dψ) (Set.Icc a b))
    (hvalue : φ anchor = ψ anchor) :
    Set.EqOn φ ψ (Set.Icc a b) := by
  have hd : dφ = dψ := by
    -- Matching the two affine formulas at the anchor point identifies the intercept.
    have hφ_anchor := hφ hanchor
    have hψ_anchor := hψ hanchor
    linarith
  intro x hx
  -- Once the intercepts match, both affine descriptions coincide on the whole interval.
  rw [hφ hx, hψ hx, hd]

/-- Helper for Theorem 6.27: consecutive increments along an ordered family telescope over any
shifted finite range. -/
private theorem shiftedConsecutiveIncrements_telescope
    {n : ℕ} (hn : 0 < n) (φ : ℝ → ℝ) (e : Fin n → ℝ)
    (start len : ℕ) (hbound : start + len < n) :
    Finset.sum Finset.univ
        (fun k : Fin len ↦
          (φ (e ⟨start + (k : ℕ) + 1, by omega⟩) -
            φ (e ⟨start + (k : ℕ), by omega⟩))) =
      φ (e ⟨start + len, hbound⟩) - φ (e ⟨start, by omega⟩) := by
  induction len with
  | zero =>
      -- The empty shifted range has no increments, so both endpoint values coincide.
      simp
  | succ len ih =>
      have hprefix : start + len < n := by
        omega
      -- Split off the final increment and telescope the preceding shifted range by induction.
      simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
      rw [ih hprefix]
      ring

/-- Helper for Theorem 6.27: prefix sums of consecutive increments telescope to the value at the
terminal prefix index. -/
private theorem prefixIncrementTelescopesToIndex
    {n : ℕ} (hn : 0 < n) (φ : ℝ → ℝ) (e : Fin n → ℝ) (split : Fin n) :
    Finset.sum Finset.univ
        (fun k : Fin split ↦
          (φ (e ⟨(k : ℕ) + 1, by omega⟩) - φ (e ⟨(k : ℕ), by omega⟩))) =
      φ (e split) - φ (e ⟨0, hn⟩) := by
  -- This is the shifted telescoping identity with starting index `0`.
  simpa using
    shiftedConsecutiveIncrements_telescope hn φ e 0 (split : ℕ) (by simpa using split.is_lt)

/-- Helper for Theorem 6.27: suffix sums of consecutive increments telescope from a chosen split
index to the final ordered breakpoint. -/
private theorem suffixIncrementTelescopesFromIndex
    {n : ℕ} (hn : 0 < n) (φ : ℝ → ℝ) (e : Fin n → ℝ) (split : Fin n) :
    Finset.sum Finset.univ
        (fun k : Fin (n - 1 - (split : ℕ)) ↦
          (φ (e ⟨(split : ℕ) + (k : ℕ) + 1, by omega⟩) -
            φ (e ⟨(split : ℕ) + (k : ℕ), by omega⟩))) =
      φ (e ⟨n - 1, Nat.sub_lt hn (Nat.succ_pos 0)⟩) - φ (e split) := by
  have hbound : (split : ℕ) + (n - 1 - (split : ℕ)) < n := by
    omega
  have hlast :
      (split : ℕ) + (n - 1 - (split : ℕ)) = n - 1 := by
    omega
  -- Recenter the generic telescoping identity at the split index.
  simpa [hlast] using
    shiftedConsecutiveIncrements_telescope hn φ e (split : ℕ) (n - 1 - (split : ℕ)) hbound

/-- Helper for Theorem 6.27: if two scalar functions agree at the first point of an ordered
family and have matching consecutive increments, then they agree at every ordered point. -/
private theorem eqAtOrderedPoints_of_matchingIncrements
    {n : ℕ} (hn : 0 < n) {e : Fin n → ℝ} {φ ψ : ℝ → ℝ}
    (hstart : φ (e ⟨0, hn⟩) = ψ (e ⟨0, hn⟩))
    (hinc :
      ∀ i : Fin (n - 1),
        φ (e (consecutiveRight hn i)) - φ (e (consecutiveLeft hn i)) =
          ψ (e (consecutiveRight hn i)) - ψ (e (consecutiveLeft hn i))) :
    ∀ k : Fin n, φ (e k) = ψ (e k) := by
  intro k
  let sumφ : ℝ :=
    Finset.sum Finset.univ
      (fun i : Fin k ↦
        (φ (e ⟨(i : ℕ) + 1, by omega⟩) - φ (e ⟨(i : ℕ), by omega⟩)))
  let sumψ : ℝ :=
    Finset.sum Finset.univ
      (fun i : Fin k ↦
        (ψ (e ⟨(i : ℕ) + 1, by omega⟩) - ψ (e ⟨(i : ℕ), by omega⟩)))
  have hsum_eq : sumφ = sumψ := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    let j : Fin (n - 1) := ⟨i, by omega⟩
    simpa [sumφ, sumψ, j, consecutiveLeft_val, consecutiveRight_val] using hinc j
  have htelφ : sumφ = φ (e k) - φ (e ⟨0, hn⟩) := by
    simpa [sumφ] using prefixIncrementTelescopesToIndex hn φ e k
  have htelψ : sumψ = ψ (e k) - ψ (e ⟨0, hn⟩) := by
    simpa [sumψ] using prefixIncrementTelescopesToIndex hn ψ e k
  linarith

/-- Helper for Theorem 6.27: consecutive points in a strictly increasing ordered family are
separated by a positive length. -/
private theorem consecutiveCellLength_pos
    {n : ℕ} (hn : 0 < n) {e : Fin n → ℝ} (he : StrictMono e)
    (i : Fin (n - 1)) :
    0 < e (consecutiveRight hn i) - e (consecutiveLeft hn i) := by
  have hindex :
      consecutiveLeft hn i < consecutiveRight hn i := by
    rw [Fin.lt_def, consecutiveLeft_val, consecutiveRight_val]
    omega
  -- Strict monotonicity of the ordered family turns the successor relation into a positive gap.
  have hgap : e (consecutiveLeft hn i) < e (consecutiveRight hn i) := he hindex
  linarith

/-- Helper for Theorem 6.27: the raw affine model on a consecutive augmented cell rewrites the
cell increment of `π` as the owning raw slope times the cell length. -/
private theorem rawCellIncrement_eq_pieceSlopeMulLength
    {f : ℝ} (hf₀ : 0 < f) (hf₁ : f < 1) {π : ℝ → ℝ}
    (hpiece : PiecewiseLinearOnInterval 0 1 π)
    (i : Fin ((augmentedBreakpoints hpiece f).card - 1)) :
    let s := augmentedBreakpoints hpiece f
    let e := augmentedBreakpointOrderEmb hpiece f
    let hs_pos : 0 < s.card := by
      exact Finset.card_pos.mpr ⟨0, zero_mem_augmentedBreakpoints⟩
    ∃ j : Fin hpiece.pieces,
      π (e (consecutiveRight hs_pos i)) - π (e (consecutiveLeft hs_pos i)) =
        hpiece.slope j * (e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i)) := by
  let s := augmentedBreakpoints hpiece f
  let e := augmentedBreakpointOrderEmb hpiece f
  have hs_pos : 0 < s.card := by
    exact Finset.card_pos.mpr ⟨0, by simpa [s] using zero_mem_augmentedBreakpoints (hpiece := hpiece) (f := f)⟩
  rcases cellAffineOfAugmentedPartition hf₀ hf₁ hpiece i with ⟨j, hcell⟩
  have hab :
      e (consecutiveLeft hs_pos i) ≤ e (consecutiveRight hs_pos i) := by
    have hlt :
        e (consecutiveLeft hs_pos i) < e (consecutiveRight hs_pos i) := by
      have hindex :
          consecutiveLeft hs_pos i < consecutiveRight hs_pos i := by
        rw [Fin.lt_def, consecutiveLeft_val, consecutiveRight_val]
        omega
      exact e.strictMono hindex
    exact le_of_lt hlt
  refine ⟨j, ?_⟩
  -- Evaluate the raw affine formula at the two ordered endpoints of the cell.
  exact affineIncrement_eq_smul_sub hab hcell

/-- Helper for Theorem 6.27: the first anchor slope is nonnegative and the last anchor slope is
nonpositive because minimal valid functions stay nonnegative on `[0, 1]`. -/
private theorem endpointAnchorSlopeSigns
    {f : ℝ} {π : ℝ → ℝ}
    (hπ : pure_integer_minimal_valid_function_on_R f π)
    {hpiece : PiecewiseLinearOnInterval 0 1 π}
    {jFirst jLast : Fin hpiece.pieces} {bFirst aLast : ℝ}
    (hbFirst_pos : 0 < bFirst)
    (hπ_first : Set.EqOn π (fun x ↦ hpiece.slope jFirst * x) (Set.Icc (0 : ℝ) bFirst))
    (haLast_lt : aLast < 1)
    (hπ_last : Set.EqOn π (fun x ↦ hpiece.slope jLast * x - hpiece.slope jLast) (Set.Icc aLast 1)) :
    0 ≤ hpiece.slope jFirst ∧ hpiece.slope jLast ≤ 0 := by
  have hb_mem : bFirst ∈ Set.Icc (0 : ℝ) bFirst := by
    simp [le_of_lt hbFirst_pos]
  have hπb_nonneg : 0 ≤ π bFirst := by
    simpa using hπ.nonneg (fun _ : Fin 1 ↦ bFirst)
  have hπb_formula := hπ_first hb_mem
  have hfirst_nonneg : 0 ≤ hpiece.slope jFirst := by
    -- Evaluating the first anchor formula at the positive endpoint `bFirst` identifies its sign.
    by_contra hfirst_neg
    have hpi_neg : π bFirst < 0 := by
      rw [hπb_formula]
      have hneg : hpiece.slope jFirst < 0 := lt_of_not_ge hfirst_neg
      nlinarith
    linarith
  have ha_mem : aLast ∈ Set.Icc aLast 1 := by
    simp [le_of_lt haLast_lt]
  have hπa_nonneg : 0 ≤ π aLast := by
    simpa using hπ.nonneg (fun _ : Fin 1 ↦ aLast)
  have hπa_formula := hπ_last ha_mem
  have hlast_nonpos : hpiece.slope jLast ≤ 0 := by
    -- The right anchor has the form `sigma * (x - 1)`, so nonnegativity forces `sigma ≤ 0`.
    by_contra hlast_pos
    have hpi_neg : π aLast < 0 := by
      rw [hπa_formula]
      have hpos : 0 < hpiece.slope jLast := lt_of_not_ge hlast_pos
      nlinarith
    linarith
  exact ⟨hfirst_nonneg, hlast_nonpos⟩

/-- Helper for Theorem 6.27: the abstract two-slope witness must consist of one positive and one
negative slope because the raw prefix and suffix increments telescope to `1` and `-1`. -/
private theorem abstractTwoSlope_have_oppositeSigns
    {f : ℝ} (hf₀ : 0 < f) (hf₁ : f < 1)
    {π : ℝ → ℝ} (hπ : pure_integer_minimal_valid_function_on_R f π)
    (hpiece : PiecewiseLinearOnInterval 0 1 π)
    {slopeLeft slopeRight : ℝ}
    (hcellSlope : ∀ j, hpiece.slope j = slopeLeft ∨ hpiece.slope j = slopeRight)
    {split : Fin (augmentedBreakpoints hpiece f).card}
    (hsplit : augmentedBreakpointOrderEmb hpiece f split = 1 - f)
    (hπ_zero : π 0 = 0) (hπ_one : π 1 = 0) (hπ_one_sub_f : π (1 - f) = 1) :
    (0 < slopeLeft ∧ slopeRight < 0) ∨ (0 < slopeRight ∧ slopeLeft < 0) := by
  let s := augmentedBreakpoints hpiece f
  let e := augmentedBreakpointOrderEmb hpiece f
  have hs_pos : 0 < s.card := by
    exact Finset.card_pos.mpr ⟨0, by simpa [s] using zero_mem_augmentedBreakpoints (hpiece := hpiece) (f := f)⟩
  have hfirst : e ⟨0, hs_pos⟩ = 0 := by
    -- Normalize the first ordered breakpoint once so the prefix telescope ends at `π 0`.
    simpa [e] using firstOrderedAugmentedBreakpoint_eq_zero hf₀ hf₁ hpiece
  have hlast : e ⟨s.card - 1, Nat.sub_lt hs_pos (Nat.succ_pos 0)⟩ = 1 := by
    -- Normalize the last ordered breakpoint once so the suffix telescope ends at `π 1`.
    simpa [e] using lastOrderedAugmentedBreakpoint_eq_one hf₀ hf₁ hpiece
  have hsplitBounds := splitIndexBoundsOfOneMinusF hf₀ hf₁ (hpiece := hpiece) hsplit
  let prefixCell : Fin split → Fin (s.card - 1) := fun k ↦ ⟨k, lt_trans k.is_lt hsplitBounds.2⟩
  let suffixCell : Fin (s.card - 1 - (split : ℕ)) → Fin (s.card - 1) := fun k ↦
    ⟨(split : ℕ) + (k : ℕ), by
      have hk_lt : (k : ℕ) < s.card - 1 - (split : ℕ) := k.is_lt
      omega⟩
  have hpos : 0 < slopeLeft ∨ 0 < slopeRight := by
    by_contra hnone
    push_neg at hnone
    have hprefix_nonpos :
        ∀ k : Fin split,
          π (e (consecutiveRight hs_pos (prefixCell k))) -
            π (e (consecutiveLeft hs_pos (prefixCell k))) ≤ 0 := by
      intro k
      let i : Fin (s.card - 1) := prefixCell k
      rcases rawCellIncrement_eq_pieceSlopeMulLength hf₀ hf₁ hpiece i with ⟨j, hinc⟩
      have hlen_pos :
          0 < e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i) := by
        simpa [e, i] using consecutiveCellLength_pos hs_pos e.strictMono i
      have hlen_nonneg : 0 ≤ e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i) :=
        hlen_pos.le
      rcases hcellSlope j with hs | hs
      · have hs_nonpos : hpiece.slope j ≤ 0 := by
          simpa [hs] using hnone.1
        calc
          π (e (consecutiveRight hs_pos i)) - π (e (consecutiveLeft hs_pos i))
              = hpiece.slope j * (e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i)) := hinc
          _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs_nonpos hlen_nonneg
      · have hs_nonpos : hpiece.slope j ≤ 0 := by
          simpa [hs] using hnone.2
        calc
          π (e (consecutiveRight hs_pos i)) - π (e (consecutiveLeft hs_pos i))
              = hpiece.slope j * (e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i)) := hinc
          _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs_nonpos hlen_nonneg
    have hprefix_sum_nonpos :
        Finset.sum Finset.univ
            (fun k : Fin split ↦
              (π (e (consecutiveRight hs_pos (prefixCell k))) -
                π (e (consecutiveLeft hs_pos (prefixCell k))))) ≤ 0 := by
      exact Finset.sum_nonpos fun k _hk ↦ hprefix_nonpos k
    have hprefix_sum :
        Finset.sum Finset.univ
            (fun k : Fin split ↦
              (π (e (consecutiveRight hs_pos (prefixCell k))) -
                π (e (consecutiveLeft hs_pos (prefixCell k))))) = 1 := by
      calc
        Finset.sum Finset.univ
            (fun k : Fin split ↦
              (π (e (consecutiveRight hs_pos (prefixCell k))) -
                π (e (consecutiveLeft hs_pos (prefixCell k)))))
            = π (e split) - π (e ⟨0, hs_pos⟩) := by
                simpa [prefixCell, consecutiveLeft_val, consecutiveRight_val] using
                  prefixIncrementTelescopesToIndex hs_pos π e split
        _ = 1 := by
            rw [hsplit, hfirst, hπ_zero, hπ_one_sub_f]
            ring
    linarith
  have hneg : slopeLeft < 0 ∨ slopeRight < 0 := by
    by_contra hnone
    push_neg at hnone
    have hsuffix_nonneg :
        ∀ k : Fin (s.card - 1 - (split : ℕ)),
          0 ≤
            π (e (consecutiveRight hs_pos (suffixCell k))) -
              π (e (consecutiveLeft hs_pos (suffixCell k))) := by
      intro k
      let i : Fin (s.card - 1) := suffixCell k
      rcases rawCellIncrement_eq_pieceSlopeMulLength hf₀ hf₁ hpiece i with ⟨j, hinc⟩
      have hlen_pos :
          0 < e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i) := by
        simpa [e, i] using consecutiveCellLength_pos hs_pos e.strictMono i
      have hlen_nonneg : 0 ≤ e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i) :=
        hlen_pos.le
      rcases hcellSlope j with hs | hs
      · have hs_nonneg : 0 ≤ hpiece.slope j := by
          simpa [hs] using hnone.1
        calc
          0 ≤ hpiece.slope j * (e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i)) :=
            mul_nonneg hs_nonneg hlen_nonneg
          _ = π (e (consecutiveRight hs_pos i)) - π (e (consecutiveLeft hs_pos i)) := by
            rw [hinc]
      · have hs_nonneg : 0 ≤ hpiece.slope j := by
          simpa [hs] using hnone.2
        calc
          0 ≤ hpiece.slope j * (e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i)) :=
            mul_nonneg hs_nonneg hlen_nonneg
          _ = π (e (consecutiveRight hs_pos i)) - π (e (consecutiveLeft hs_pos i)) := by
            rw [hinc]
    have hsuffix_sum_nonneg :
        0 ≤
          Finset.sum Finset.univ
            (fun k : Fin (s.card - 1 - (split : ℕ)) ↦
              (π (e (consecutiveRight hs_pos (suffixCell k))) -
                π (e (consecutiveLeft hs_pos (suffixCell k))))) := by
      exact Finset.sum_nonneg fun k _hk ↦ hsuffix_nonneg k
    have hsuffix_sum :
        Finset.sum Finset.univ
          (fun k : Fin (s.card - 1 - (split : ℕ)) ↦
            (π (e (consecutiveRight hs_pos (suffixCell k))) -
              π (e (consecutiveLeft hs_pos (suffixCell k))))) = -1 := by
      calc
        Finset.sum Finset.univ
          (fun k : Fin (s.card - 1 - (split : ℕ)) ↦
            (π (e (consecutiveRight hs_pos (suffixCell k))) -
              π (e (consecutiveLeft hs_pos (suffixCell k)))))
            = π (e ⟨s.card - 1, Nat.sub_lt hs_pos (Nat.succ_pos 0)⟩) - π (e split) := by
                simpa [suffixCell, consecutiveLeft_val, consecutiveRight_val] using
                  suffixIncrementTelescopesFromIndex hs_pos π e split
        _ = -1 := by
            rw [hlast, hsplit, hπ_one, hπ_one_sub_f]
            ring
    linarith
  rcases hpos with hleft_pos | hright_pos
  · rcases hneg with hleft_neg | hright_neg
    · exfalso
      linarith
    · exact Or.inl ⟨hleft_pos, hright_neg⟩
  · rcases hneg with hleft_neg | hright_neg
    · exact Or.inr ⟨hright_pos, hleft_neg⟩
    · exfalso
      linarith

/-- Helper for Theorem 6.27: the abstract two-slope witness can be reoriented to the concrete
endpoint-realized slopes coming from the first and last augmented cells. -/
private theorem endpointRealizedSlopeOrientation
    {f : ℝ} (hf₀ : 0 < f) (hf₁ : f < 1)
    {π : ℝ → ℝ} (hπ : pure_integer_minimal_valid_function_on_R f π)
    (hpiece : PiecewiseLinearOnInterval 0 1 π)
    {slopeLeft slopeRight : ℝ}
    (hcellSlope : ∀ j, hpiece.slope j = slopeLeft ∨ hpiece.slope j = slopeRight)
    {split : Fin (augmentedBreakpoints hpiece f).card}
    (hsplit : augmentedBreakpointOrderEmb hpiece f split = 1 - f)
    {jFirst jLast : Fin hpiece.pieces} {bFirst aLast : ℝ}
    (hbFirst_pos : 0 < bFirst)
    (hπ_first : Set.EqOn π (fun x ↦ hpiece.slope jFirst * x) (Set.Icc (0 : ℝ) bFirst))
    (haLast_lt : aLast < 1)
    (hπ_last : Set.EqOn π (fun x ↦ hpiece.slope jLast * x - hpiece.slope jLast) (Set.Icc aLast 1))
    (hπ_zero : π 0 = 0) (hπ_one : π 1 = 0) (hπ_one_sub_f : π (1 - f) = 1) :
    0 < hpiece.slope jFirst ∧
      hpiece.slope jLast < 0 ∧
        ∀ j : Fin hpiece.pieces,
          hpiece.slope j = hpiece.slope jFirst ∨ hpiece.slope j = hpiece.slope jLast := by
  rcases endpointAnchorSlopeSigns hπ hbFirst_pos hπ_first haLast_lt hπ_last with
    ⟨hfirst_nonneg, hlast_nonpos⟩
  rcases abstractTwoSlope_have_oppositeSigns hf₀ hf₁ hπ hpiece hcellSlope hsplit
      hπ_zero hπ_one hπ_one_sub_f with hsigns | hsigns
  · rcases hsigns with ⟨hleft_pos, hright_neg⟩
    have hjFirst : hpiece.slope jFirst = slopeLeft := by
      rcases hcellSlope jFirst with hjFirst | hjFirst
      · exact hjFirst
      · exfalso
        linarith [hfirst_nonneg, hright_neg, hjFirst]
    have hjLast : hpiece.slope jLast = slopeRight := by
      rcases hcellSlope jLast with hjLast | hjLast
      · exfalso
        linarith [hlast_nonpos, hleft_pos, hjLast]
      · exact hjLast
    refine ⟨?_, ?_, ?_⟩
    · -- The nonnegative first anchor must coincide with the positive abstract slope.
      simpa [hjFirst] using hleft_pos
    · -- The nonpositive last anchor must coincide with the negative abstract slope.
      simpa [hjLast] using hright_neg
    · intro j
      rcases hcellSlope j with hj | hj
      · left
        simpa [hjFirst] using hj
      · right
        simpa [hjLast] using hj
  · rcases hsigns with ⟨hright_pos, hleft_neg⟩
    have hjFirst : hpiece.slope jFirst = slopeRight := by
      rcases hcellSlope jFirst with hjFirst | hjFirst
      · exfalso
        linarith [hfirst_nonneg, hleft_neg, hjFirst]
      · exact hjFirst
    have hjLast : hpiece.slope jLast = slopeLeft := by
      rcases hcellSlope jLast with hjLast | hjLast
      · exact hjLast
      · exfalso
        linarith [hlast_nonpos, hright_pos, hjLast]
    refine ⟨?_, ?_, ?_⟩
    · -- In the swapped-sign case, the first anchor identifies the positive right abstract slope.
      simpa [hjFirst] using hright_pos
    · -- The last anchor then identifies the negative left abstract slope.
      simpa [hjLast] using hleft_neg
    · intro j
      rcases hcellSlope j with hj | hj
      · right
        simpa [hjLast] using hj
      · left
        simpa [hjFirst] using hj

/-- Helper for Theorem 6.27: the first augmented cell already determines the left-anchor slope
family for `π`, `π₁`, and `π₂`. -/
private theorem firstAugmentedCellAnchorFamily
    {f : ℝ} (hf₀ : 0 < f) (hf₁ : f < 1)
    {π π₁ π₂ : ℝ → ℝ}
    (hπ : pure_integer_minimal_valid_function_on_R f π)
    (hpiece : PiecewiseLinearOnInterval 0 1 π)
    (hπ₁ : pure_integer_valid_function_on_R f π₁)
    (hπ₂ : pure_integer_valid_function_on_R f π₂)
    (hmid : π = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂)
    (hπ_zero : π 0 = 0)
    (hπ₁_zero : π₁ 0 = 0)
    (hπ₂_zero : π₂ 0 = 0)
    (hπ₁_bdd : BoundedOnBoundedIntervals π₁)
    (hπ₂_bdd : BoundedOnBoundedIntervals π₂) :
    ∃ j b sigma₁ sigma₂, 0 < b ∧
      Set.EqOn π (fun x ↦ hpiece.slope j * x) (Set.Icc (0 : ℝ) b) ∧
        Set.EqOn π₁ (fun x ↦ sigma₁ * x) (Set.Icc (0 : ℝ) b) ∧
          Set.EqOn π₂ (fun x ↦ sigma₂ * x) (Set.Icc (0 : ℝ) b) := by
  let s := augmentedBreakpoints hpiece f
  have hs_pos : 0 < s.card := by
    exact Finset.card_pos.mpr ⟨0, by simpa [s] using zero_mem_augmentedBreakpoints (hpiece := hpiece) (f := f)⟩
  rcases splitIndexOfOneMinusF (f := f) (hpiece := hpiece) with ⟨split, hsplit⟩
  have hsplitBounds := splitIndexBoundsOfOneMinusF hf₀ hf₁ (hpiece := hpiece) hsplit
  have hs_card_gt_one : 1 < s.card := by
    have hsplit_pos_nat : 0 < (split : ℕ) := hsplitBounds.1
    have hsplit_lt_card : (split : ℕ) < s.card := by
      simpa [s] using split.is_lt
    omega
  let first : Fin s.card := ⟨0, hs_pos⟩
  let i0 : Fin (s.card - 1) := ⟨0, by omega⟩
  let b : ℝ := (augmentedBreakpointOrderEmb hpiece f)
    (consecutiveRight hs_pos i0)
  have hs_nonempty : s.Nonempty := Finset.card_pos.mp hs_pos
  have hzero_mem : (0 : ℝ) ∈ s := by
    simpa [s] using zero_mem_augmentedBreakpoints (hpiece := hpiece) (f := f)
  have hleft_index :
      consecutiveLeft hs_pos i0 = first := by
    apply Fin.ext
    simp [first, i0, consecutiveLeft_val]
  have he_first : (augmentedBreakpointOrderEmb hpiece f) first = 0 := by
    -- The first ordered augmented breakpoint is the left endpoint `0`.
    change s.orderEmbOfFin rfl first = 0
    rw [Finset.orderEmbOfFin_zero rfl hs_pos]
    apply le_antisymm
    · exact s.min'_le 0 hzero_mem
    · exact (mem_augmentedBreakpoints_unitInterval hf₀ hf₁
        (hpiece := hpiece) (s.min'_mem hs_nonempty)).1
  have hleft_eq : (augmentedBreakpointOrderEmb hpiece f)
      (consecutiveLeft hs_pos i0) = 0 := by
    simpa [hleft_index] using he_first
  have hfirst_lt_right :
      first < consecutiveRight hs_pos i0 := by
    rw [Fin.lt_def, consecutiveRight_val]
    simp [first, i0]
  have hb_pos : 0 < b := by
    -- Consecutive ordered breakpoints form a genuine positive-length first cell.
    have hmono := (augmentedBreakpointOrderEmb hpiece f).strictMono hfirst_lt_right
    simpa [b, he_first] using hmono
  have hcell0 := cellAffineOfAugmentedPartition hf₀ hf₁ hpiece i0
  rcases hcell0 with ⟨j, hcell0⟩
  have hzero_mem_cell :
      (0 : ℝ) ∈ Set.Icc
        ((augmentedBreakpointOrderEmb hpiece f) (consecutiveLeft hs_pos i0))
        ((augmentedBreakpointOrderEmb hpiece f) (consecutiveRight hs_pos i0)) := by
    simpa [hleft_eq, b, le_of_lt hb_pos]
  have hintercept_zero : hpiece.intercept j = 0 := by
    -- Evaluating the raw affine formula at `0` removes the intercept on the first cell.
    have hzero_formula := hcell0 hzero_mem_cell
    rw [hπ_zero] at hzero_formula
    linarith
  have hπ_first : Set.EqOn π (fun x ↦ hpiece.slope j * x) (Set.Icc (0 : ℝ) b) := by
    intro x hx
    have hx_cell :
        x ∈ Set.Icc
          ((augmentedBreakpointOrderEmb hpiece f) (consecutiveLeft hs_pos i0))
          ((augmentedBreakpointOrderEmb hpiece f) (consecutiveRight hs_pos i0)) := by
      simpa [hleft_eq, b] using hx
    -- Reuse the raw cell affine model after normalizing its intercept to `0`.
    simpa [hintercept_zero] using hcell0 hx_cell
  let ε : ℝ := b / 2
  have hε_pos : 0 < ε := by
    dsimp [ε]
    linarith
  have hε_lt : ε < b - 0 := by
    dsimp [ε]
    linarith
  have hanchor : Set.EqOn π (fun x ↦ hpiece.slope j * x) (Set.Icc (0 : ℝ) ε) := by
    intro x hx
    exact hπ_first <| by
      constructor
      · exact hx.1
      · linarith [hx.2, hb_pos]
  rcases midpointComponentsAffineOnLeftSlopeInterval
      (sigma := hpiece.slope j) (d := 0)
      hπ hπ₁ hπ₂ hmid hπ₁_bdd hπ₂_bdd hε_pos hε_lt hanchor
      (by simpa using hπ_first) with
    ⟨sigma₁, d₁, sigma₂, d₂, hπ₁_first, hπ₂_first⟩
  have hzero_mem_target : (0 : ℝ) ∈ Set.Icc (0 : ℝ) b := by
    simp [le_of_lt hb_pos]
  have hd₁_zero : d₁ = 0 := by
    -- The first midpoint component also vanishes at `0`, so its intercept disappears.
    have hzero_formula := hπ₁_first hzero_mem_target
    rw [hπ₁_zero] at hzero_formula
    linarith
  have hd₂_zero : d₂ = 0 := by
    -- The same endpoint normalization applies to the second midpoint component.
    have hzero_formula := hπ₂_first hzero_mem_target
    rw [hπ₂_zero] at hzero_formula
    linarith
  refine ⟨j, b, sigma₁, sigma₂, hb_pos, hπ_first, ?_, ?_⟩
  · -- Replace the anonymous affine intercept by the normalized left-anchor form.
    intro x hx
    simpa [hd₁_zero] using hπ₁_first hx
  · -- Apply the same normalization to the second midpoint component.
    intro x hx
    simpa [hd₂_zero] using hπ₂_first hx

/-- Helper for Theorem 6.27: the last augmented cell already determines the right-anchor slope
family for `π`, `π₁`, and `π₂`. -/
private theorem lastAugmentedCellAnchorFamily
    {f : ℝ} (hf₀ : 0 < f) (hf₁ : f < 1)
    {π π₁ π₂ : ℝ → ℝ}
    (hπ : pure_integer_minimal_valid_function_on_R f π)
    (hpiece : PiecewiseLinearOnInterval 0 1 π)
    (hπ₁ : pure_integer_valid_function_on_R f π₁)
    (hπ₂ : pure_integer_valid_function_on_R f π₂)
    (hmid : π = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂)
    (hπ_periodic : Function.Periodic π 1)
    (hπ₁_periodic : Function.Periodic π₁ 1)
    (hπ₂_periodic : Function.Periodic π₂ 1)
    (hπ_one : π 1 = 0)
    (hπ₁_one : π₁ 1 = 0)
    (hπ₂_one : π₂ 1 = 0)
    (hπ₁_bdd : BoundedOnBoundedIntervals π₁)
    (hπ₂_bdd : BoundedOnBoundedIntervals π₂) :
    ∃ j a sigma₁ sigma₂, a < 1 ∧
      Set.EqOn π (fun x ↦ hpiece.slope j * x - hpiece.slope j) (Set.Icc a 1) ∧
        Set.EqOn π₁ (fun x ↦ sigma₁ * x - sigma₁) (Set.Icc a 1) ∧
          Set.EqOn π₂ (fun x ↦ sigma₂ * x - sigma₂) (Set.Icc a 1) := by
  let s := augmentedBreakpoints hpiece f
  have hs_pos : 0 < s.card := by
    exact Finset.card_pos.mpr ⟨0, by simpa [s] using zero_mem_augmentedBreakpoints (hpiece := hpiece) (f := f)⟩
  rcases splitIndexOfOneMinusF (f := f) (hpiece := hpiece) with ⟨split, hsplit⟩
  have hsplitBounds := splitIndexBoundsOfOneMinusF hf₀ hf₁ (hpiece := hpiece) hsplit
  have hs_card_gt_one : 1 < s.card := by
    have hsplit_pos_nat : 0 < (split : ℕ) := hsplitBounds.1
    have hsplit_lt_card : (split : ℕ) < s.card := by
      simpa [s] using split.is_lt
    omega
  let last : Fin s.card := ⟨s.card - 1, Nat.sub_lt hs_pos (Nat.succ_pos 0)⟩
  let ilast : Fin (s.card - 1) := ⟨s.card - 2, by omega⟩
  let a : ℝ := (augmentedBreakpointOrderEmb hpiece f)
    (consecutiveLeft hs_pos ilast)
  have hs_nonempty : s.Nonempty := Finset.card_pos.mp hs_pos
  have hone_mem : (1 : ℝ) ∈ s := by
    simpa [s] using one_mem_augmentedBreakpoints (hpiece := hpiece) (f := f)
  have hright_index :
      consecutiveRight hs_pos ilast = last := by
    apply Fin.ext
    simp [last, ilast, consecutiveRight_val]
    omega
  have he_last : (augmentedBreakpointOrderEmb hpiece f) last = 1 := by
    -- The last ordered augmented breakpoint is the right endpoint `1`.
    change s.orderEmbOfFin rfl last = 1
    rw [Finset.orderEmbOfFin_last rfl hs_pos]
    apply le_antisymm
    · exact (mem_augmentedBreakpoints_unitInterval hf₀ hf₁
        (hpiece := hpiece) (s.max'_mem hs_nonempty)).2
    · exact s.le_max' 1 hone_mem
  have hright_eq : (augmentedBreakpointOrderEmb hpiece f)
      (consecutiveRight hs_pos ilast) = 1 := by
    simpa [hright_index] using he_last
  have hleft_lt_last :
      consecutiveLeft hs_pos ilast < last := by
    rw [Fin.lt_def, consecutiveLeft_val]
    simp [last, ilast]
    omega
  have ha_lt_one : a < 1 := by
    -- Consecutive ordered breakpoints form a genuine positive-length last cell.
    have hmono := (augmentedBreakpointOrderEmb hpiece f).strictMono hleft_lt_last
    simpa [a, he_last] using hmono
  have hcellLast := cellAffineOfAugmentedPartition hf₀ hf₁ hpiece ilast
  rcases hcellLast with ⟨j, hcellLast⟩
  have hone_mem_cell :
      (1 : ℝ) ∈ Set.Icc
        ((augmentedBreakpointOrderEmb hpiece f) (consecutiveLeft hs_pos ilast))
        ((augmentedBreakpointOrderEmb hpiece f) (consecutiveRight hs_pos ilast)) := by
    simpa [a, hright_eq, le_of_lt ha_lt_one]
  have hintercept_right : hpiece.intercept j = -hpiece.slope j := by
    -- Evaluating the raw affine formula at `1` fixes the right-anchor intercept.
    have hone_formula := hcellLast hone_mem_cell
    rw [hπ_one] at hone_formula
    linarith
  have hπ_last : Set.EqOn π (fun x ↦ hpiece.slope j * x - hpiece.slope j) (Set.Icc a 1) := by
    intro x hx
    have hx_cell :
        x ∈ Set.Icc
          ((augmentedBreakpointOrderEmb hpiece f) (consecutiveLeft hs_pos ilast))
          ((augmentedBreakpointOrderEmb hpiece f) (consecutiveRight hs_pos ilast)) := by
      simpa [a, hright_eq] using hx
    -- Reuse the raw cell affine model after normalizing its intercept at the right endpoint.
    simpa [sub_eq_add_neg, hintercept_right, add_comm, add_left_comm, add_assoc] using
      hcellLast hx_cell
  let ε : ℝ := (1 - a) / 2
  have hε_pos : 0 < ε := by
    dsimp [ε]
    linarith
  have hε_lt : ε < 1 - a := by
    dsimp [ε]
    linarith
  have hanchor : Set.EqOn π (fun x ↦ hpiece.slope j * x - hpiece.slope j)
      (Set.Icc (1 - ε) 1) := by
    intro x hx
    exact hπ_last <| by
      constructor
      · linarith [hx.1, ha_lt_one]
      · exact hx.2
  rcases midpointComponentsAffineOnRightSlopeInterval
      (sigma := hpiece.slope j) (d := -hpiece.slope j)
      hπ hπ₁ hπ₂ hmid hπ_periodic hπ₁_periodic hπ₂_periodic hπ₁_bdd hπ₂_bdd
      hε_pos hε_lt (by simpa [sub_eq_add_neg] using hπ_last) hanchor with
    ⟨sigma₁, d₁, sigma₂, d₂, hπ₁_last, hπ₂_last⟩
  have hone_mem_target : (1 : ℝ) ∈ Set.Icc a 1 := by
    simp [le_of_lt ha_lt_one]
  have hd₁_right : d₁ = -sigma₁ := by
    -- The first midpoint component also vanishes at `1`, so its intercept is `-sigma₁`.
    have hone_formula := hπ₁_last hone_mem_target
    rw [hπ₁_one] at hone_formula
    linarith
  have hd₂_right : d₂ = -sigma₂ := by
    -- The same endpoint normalization applies to the second midpoint component.
    have hone_formula := hπ₂_last hone_mem_target
    rw [hπ₂_one] at hone_formula
    linarith
  refine ⟨j, a, sigma₁, sigma₂, ha_lt_one, hπ_last, ?_, ?_⟩
  · -- Replace the anonymous affine intercept by the normalized right-anchor form.
    intro x hx
    simpa [sub_eq_add_neg, hd₁_right, add_comm, add_left_comm, add_assoc] using hπ₁_last hx
  · -- Apply the same normalization to the second midpoint component.
    intro x hx
    simpa [sub_eq_add_neg, hd₂_right, add_comm, add_left_comm, add_assoc] using hπ₂_last hx

/-- Helper for Theorem 6.27: choose one raw affine piece that owns a fixed augmented cell. -/
private noncomputable def augmentedCellOwner
    {π : ℝ → ℝ} {f : ℝ} (hf₀ : 0 < f) (hf₁ : f < 1)
    (hpiece : PiecewiseLinearOnInterval 0 1 π)
    (i : Fin ((augmentedBreakpoints hpiece f).card - 1)) : Fin hpiece.pieces :=
  Classical.choose (cellAffineOfAugmentedPartition hf₀ hf₁ hpiece i)

/-- Helper for Theorem 6.27: the chosen augmented-cell owner supplies the raw affine formula on
that whole cell. -/
private theorem augmentedCellOwner_spec
    {π : ℝ → ℝ} {f : ℝ} (hf₀ : 0 < f) (hf₁ : f < 1)
    (hpiece : PiecewiseLinearOnInterval 0 1 π)
    (i : Fin ((augmentedBreakpoints hpiece f).card - 1)) :
    Set.EqOn π
      (fun x ↦
        hpiece.slope (augmentedCellOwner hf₀ hf₁ hpiece i) * x +
          hpiece.intercept (augmentedCellOwner hf₀ hf₁ hpiece i))
      (Set.Icc ((augmentedBreakpointOrderEmb hpiece f)
          (consecutiveLeft
            (by
              exact Finset.card_pos.mpr ⟨0, zero_mem_augmentedBreakpoints⟩)
            i))
        ((augmentedBreakpointOrderEmb hpiece f)
          (consecutiveRight
            (by
              exact Finset.card_pos.mpr ⟨0, zero_mem_augmentedBreakpoints⟩)
            i))) := by
  exact Classical.choose_spec (cellAffineOfAugmentedPartition hf₀ hf₁ hpiece i)

/-- Helper for Theorem 6.27: the chosen owner rewrites the raw increment on an augmented cell as
its slope times the cell length. -/
private theorem augmentedCellOwnerIncrement_eq_pieceSlopeMulLength
    {f : ℝ} (hf₀ : 0 < f) (hf₁ : f < 1) {π : ℝ → ℝ}
    (hpiece : PiecewiseLinearOnInterval 0 1 π)
    (i : Fin ((augmentedBreakpoints hpiece f).card - 1)) :
    let s := augmentedBreakpoints hpiece f
    let e := augmentedBreakpointOrderEmb hpiece f
    let hs_pos : 0 < s.card := by
      exact Finset.card_pos.mpr ⟨0, zero_mem_augmentedBreakpoints⟩
    π (e (consecutiveRight hs_pos i)) - π (e (consecutiveLeft hs_pos i)) =
      hpiece.slope (augmentedCellOwner hf₀ hf₁ hpiece i) *
        (e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i)) := by
  let s := augmentedBreakpoints hpiece f
  let e := augmentedBreakpointOrderEmb hpiece f
  have hs_pos : 0 < s.card := by
    exact Finset.card_pos.mpr ⟨0, by simpa [s] using zero_mem_augmentedBreakpoints (hpiece := hpiece) (f := f)⟩
  have hab :
      e (consecutiveLeft hs_pos i) ≤ e (consecutiveRight hs_pos i) := by
    have hlen_pos :
        0 < e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i) := by
      simpa [e] using consecutiveCellLength_pos hs_pos e.strictMono i
    linarith
  exact affineIncrement_eq_smul_sub hab (augmentedCellOwner_spec hf₀ hf₁ hpiece i)

/-- Helper for Theorem 6.27: once the raw owner of an augmented cell is classified into the
positive or negative endpoint slope family, the raw increment on that cell uses the same family
slope. -/
private theorem rawCellIncrementOfSlopeFamily
    {f : ℝ} (hf₀ : 0 < f) (hf₁ : f < 1)
    {π : ℝ → ℝ} (hpiece : PiecewiseLinearOnInterval 0 1 π)
    {jFirst jLast : Fin hpiece.pieces}
    (hrawSlopeClassify :
      ∀ j : Fin hpiece.pieces,
        hpiece.slope j = hpiece.slope jFirst ∨ hpiece.slope j = hpiece.slope jLast)
    (i : Fin ((augmentedBreakpoints hpiece f).card - 1)) :
    let s := augmentedBreakpoints hpiece f
    let e := augmentedBreakpointOrderEmb hpiece f
    let hs_pos : 0 < s.card := by
      exact Finset.card_pos.mpr ⟨0, zero_mem_augmentedBreakpoints⟩
    let owner := augmentedCellOwner hf₀ hf₁ hpiece i
    ((hpiece.slope owner = hpiece.slope jFirst) ∧
        π (e (consecutiveRight hs_pos i)) - π (e (consecutiveLeft hs_pos i)) =
          hpiece.slope jFirst * (e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i)))
      ∨
      ((hpiece.slope owner = hpiece.slope jLast) ∧
        π (e (consecutiveRight hs_pos i)) - π (e (consecutiveLeft hs_pos i)) =
          hpiece.slope jLast * (e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i))) := by
  let s := augmentedBreakpoints hpiece f
  let e := augmentedBreakpointOrderEmb hpiece f
  have hs_pos : 0 < s.card := by
    exact Finset.card_pos.mpr ⟨0, by simpa [s] using zero_mem_augmentedBreakpoints (hpiece := hpiece) (f := f)⟩
  let owner := augmentedCellOwner hf₀ hf₁ hpiece i
  -- First classify the chosen owner, then rewrite the raw increment through that owner.
  rcases hrawSlopeClassify owner with hs | hs
  · exact Or.inl ⟨hs, by simpa [s, e, hs_pos, owner, hs] using
      augmentedCellOwnerIncrement_eq_pieceSlopeMulLength hf₀ hf₁ hpiece i⟩
  · exact Or.inr ⟨hs, by simpa [s, e, hs_pos, owner, hs] using
      augmentedCellOwnerIncrement_eq_pieceSlopeMulLength hf₀ hf₁ hpiece i⟩

/-- Helper for Theorem 6.27: classified prefix cell increments collapse to the left boundary
equation of the two-slope linear system. -/
private theorem classifiedPrefixBoundaryEquation_ofOwnerSums
    {f : ℝ} (hf₀ : 0 < f) (hf₁ : f < 1)
    {π : ℝ → ℝ} (hpiece : PiecewiseLinearOnInterval 0 1 π)
    {split : Fin (augmentedBreakpoints hpiece f).card}
    (hsplit : augmentedBreakpointOrderEmb hpiece f split = 1 - f)
    {jFirst jLast : Fin hpiece.pieces}
    (hjFirst_pos : 0 < hpiece.slope jFirst)
    (hjLast_neg : hpiece.slope jLast < 0)
    (hprefixBound :
      ∀ k : Fin split, (k : ℕ) < (augmentedBreakpoints hpiece f).card - 1)
    {φ : ℝ → ℝ} {sigmaPlus sigmaMinus : ℝ}
    (hinc :
      ∀ k : Fin split,
        let s := augmentedBreakpoints hpiece f
        let e := augmentedBreakpointOrderEmb hpiece f
        let hs_pos : 0 < s.card := by
          exact Finset.card_pos.mpr ⟨0, zero_mem_augmentedBreakpoints⟩
        let i : Fin (s.card - 1) := ⟨k, hprefixBound k⟩
        let owner := augmentedCellOwner hf₀ hf₁ hpiece i
        ((hpiece.slope owner = hpiece.slope jFirst) ∧
            φ (e (consecutiveRight hs_pos i)) - φ (e (consecutiveLeft hs_pos i)) =
              sigmaPlus * (e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i)))
          ∨
          ((hpiece.slope owner = hpiece.slope jLast) ∧
            φ (e (consecutiveRight hs_pos i)) - φ (e (consecutiveLeft hs_pos i)) =
              sigmaMinus * (e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i)))) :
    let s := augmentedBreakpoints hpiece f
    let e := augmentedBreakpointOrderEmb hpiece f
    let hs_pos : 0 < s.card := by
      exact Finset.card_pos.mpr ⟨0, zero_mem_augmentedBreakpoints⟩
    let owner : Fin (s.card - 1) → Fin hpiece.pieces :=
      fun i ↦ augmentedCellOwner hf₀ hf₁ hpiece i
    let cellLen : Fin (s.card - 1) → ℝ :=
      fun i ↦ e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i)
    let prefixCell : Fin split → Fin (s.card - 1) := fun k ↦ ⟨k, hprefixBound k⟩
    let LlPlus : ℝ :=
      Finset.sum Finset.univ
        (fun k : Fin split ↦
          if hpiece.slope (owner (prefixCell k)) = hpiece.slope jFirst then
            cellLen (prefixCell k)
          else 0)
    let LlMinus : ℝ :=
      Finset.sum Finset.univ
        (fun k : Fin split ↦
          if hpiece.slope (owner (prefixCell k)) = hpiece.slope jLast then
            cellLen (prefixCell k)
          else 0)
    LlPlus * sigmaPlus + LlMinus * sigmaMinus = φ (1 - f) - φ 0 := by
  let s := augmentedBreakpoints hpiece f
  let e := augmentedBreakpointOrderEmb hpiece f
  have hs_pos : 0 < s.card := by
    exact Finset.card_pos.mpr ⟨0, by simpa [s] using zero_mem_augmentedBreakpoints (hpiece := hpiece) (f := f)⟩
  let owner : Fin (s.card - 1) → Fin hpiece.pieces := fun i ↦ augmentedCellOwner hf₀ hf₁ hpiece i
  let cellLen : Fin (s.card - 1) → ℝ :=
    fun i ↦ e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i)
  let prefixCell : Fin split → Fin (s.card - 1) := fun k ↦ ⟨k, hprefixBound k⟩
  let LlPlus : ℝ :=
    Finset.sum Finset.univ
      (fun k : Fin split ↦
        if hpiece.slope (owner (prefixCell k)) = hpiece.slope jFirst then
          cellLen (prefixCell k)
        else 0)
  let LlMinus : ℝ :=
    Finset.sum Finset.univ
      (fun k : Fin split ↦
        if hpiece.slope (owner (prefixCell k)) = hpiece.slope jLast then
          cellLen (prefixCell k)
        else 0)
  have hslopes_ne : hpiece.slope jFirst ≠ hpiece.slope jLast := by
    linarith
  have hclassified :
      Finset.sum Finset.univ
        (fun k : Fin split ↦
          (φ (e (consecutiveRight hs_pos (prefixCell k))) -
            φ (e (consecutiveLeft hs_pos (prefixCell k))))) =
        LlPlus * sigmaPlus + LlMinus * sigmaMinus := by
    calc
      Finset.sum Finset.univ
        (fun k : Fin split ↦
          (φ (e (consecutiveRight hs_pos (prefixCell k))) -
            φ (e (consecutiveLeft hs_pos (prefixCell k)))))
          =
            Finset.sum Finset.univ
              (fun k : Fin split ↦
                (if hpiece.slope (owner (prefixCell k)) = hpiece.slope jFirst then
                    cellLen (prefixCell k)
                  else 0) * sigmaPlus +
                  (if hpiece.slope (owner (prefixCell k)) = hpiece.slope jLast then
                    cellLen (prefixCell k)
                  else 0) * sigmaMinus) := by
              refine Finset.sum_congr rfl ?_
              intro k _hk
              rcases hinc k with hleft | hright
              · rcases hleft with ⟨hslope, hφ⟩
                have hnot : ¬ hpiece.slope (owner (prefixCell k)) = hpiece.slope jLast := by
                  intro hcontra
                  exact hslopes_ne (hslope.symm.trans hcontra)
                rw [if_pos hslope, if_neg hnot]
                simpa [cellLen, prefixCell, mul_comm, mul_left_comm, mul_assoc] using hφ
              · rcases hright with ⟨hslope, hφ⟩
                have hnot : ¬ hpiece.slope (owner (prefixCell k)) = hpiece.slope jFirst := by
                  intro hcontra
                  exact hslopes_ne (hcontra.symm.trans hslope)
                rw [if_neg hnot, if_pos hslope]
                simpa [cellLen, prefixCell, mul_comm, mul_left_comm, mul_assoc] using hφ
      _ =
          (Finset.sum Finset.univ
            (fun k : Fin split ↦
              if hpiece.slope (owner (prefixCell k)) = hpiece.slope jFirst then
                cellLen (prefixCell k)
              else 0)) * sigmaPlus +
            (Finset.sum Finset.univ
              (fun k : Fin split ↦
                if hpiece.slope (owner (prefixCell k)) = hpiece.slope jLast then
                  cellLen (prefixCell k)
                else 0)) * sigmaMinus := by
              rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
      _ = LlPlus * sigmaPlus + LlMinus * sigmaMinus := by rfl
  have hprefix_tel :
      Finset.sum Finset.univ
        (fun k : Fin split ↦
          (φ (e (consecutiveRight hs_pos (prefixCell k))) -
            φ (e (consecutiveLeft hs_pos (prefixCell k))))) =
        φ (e split) - φ (e ⟨0, hs_pos⟩) := by
    -- Normalize the prefix cells to the canonical `0, 1, ..., split` telescoping spelling.
    simpa [prefixCell, consecutiveLeft_val, consecutiveRight_val] using
      prefixIncrementTelescopesToIndex hs_pos φ e split
  have hfirst : e ⟨0, hs_pos⟩ = 0 := by
    -- The left boundary equation ends at the first ordered augmented breakpoint `0`.
    simpa [e] using firstOrderedAugmentedBreakpoint_eq_zero hf₀ hf₁ hpiece
  calc
    LlPlus * sigmaPlus + LlMinus * sigmaMinus
        = Finset.sum Finset.univ
            (fun k : Fin split ↦
              (φ (e (consecutiveRight hs_pos (prefixCell k))) -
                φ (e (consecutiveLeft hs_pos (prefixCell k))))) := hclassified.symm
    _ = φ (e split) - φ (e ⟨0, hs_pos⟩) := hprefix_tel
    _ = φ (1 - f) - φ 0 := by rw [hsplit, hfirst]

/-- Helper for Theorem 6.27: classified suffix cell increments collapse to the right boundary
equation of the two-slope linear system. -/
private theorem classifiedSuffixBoundaryEquation_ofOwnerSums
    {f : ℝ} (hf₀ : 0 < f) (hf₁ : f < 1)
    {π : ℝ → ℝ} (hpiece : PiecewiseLinearOnInterval 0 1 π)
    {split : Fin (augmentedBreakpoints hpiece f).card}
    (hsplit : augmentedBreakpointOrderEmb hpiece f split = 1 - f)
    {jFirst jLast : Fin hpiece.pieces}
    (hjFirst_pos : 0 < hpiece.slope jFirst)
    (hjLast_neg : hpiece.slope jLast < 0)
    (hsuffixBound :
      ∀ k : Fin ((augmentedBreakpoints hpiece f).card - 1 - (split : ℕ)),
        (split : ℕ) + (k : ℕ) < (augmentedBreakpoints hpiece f).card - 1)
    {φ : ℝ → ℝ} {sigmaPlus sigmaMinus : ℝ}
    (hinc :
      ∀ k : Fin ((augmentedBreakpoints hpiece f).card - 1 - (split : ℕ)),
        let s := augmentedBreakpoints hpiece f
        let e := augmentedBreakpointOrderEmb hpiece f
        let hs_pos : 0 < s.card := by
          exact Finset.card_pos.mpr ⟨0, zero_mem_augmentedBreakpoints⟩
        let i : Fin (s.card - 1) := ⟨(split : ℕ) + (k : ℕ), hsuffixBound k⟩
        let owner := augmentedCellOwner hf₀ hf₁ hpiece i
        ((hpiece.slope owner = hpiece.slope jFirst) ∧
            φ (e (consecutiveRight hs_pos i)) - φ (e (consecutiveLeft hs_pos i)) =
              sigmaPlus * (e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i)))
          ∨
          ((hpiece.slope owner = hpiece.slope jLast) ∧
            φ (e (consecutiveRight hs_pos i)) - φ (e (consecutiveLeft hs_pos i)) =
              sigmaMinus * (e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i)))) :
    let s := augmentedBreakpoints hpiece f
    let e := augmentedBreakpointOrderEmb hpiece f
    let hs_pos : 0 < s.card := by
      exact Finset.card_pos.mpr ⟨0, zero_mem_augmentedBreakpoints⟩
    let owner : Fin (s.card - 1) → Fin hpiece.pieces :=
      fun i ↦ augmentedCellOwner hf₀ hf₁ hpiece i
    let cellLen : Fin (s.card - 1) → ℝ :=
      fun i ↦ e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i)
    let suffixCell : Fin (s.card - 1 - (split : ℕ)) → Fin (s.card - 1) :=
      fun k ↦ ⟨(split : ℕ) + (k : ℕ), hsuffixBound k⟩
    let LrPlus : ℝ :=
      Finset.sum Finset.univ
        (fun k : Fin (s.card - 1 - (split : ℕ)) ↦
          if hpiece.slope (owner (suffixCell k)) = hpiece.slope jFirst then
            cellLen (suffixCell k)
          else 0)
    let LrMinus : ℝ :=
      Finset.sum Finset.univ
        (fun k : Fin (s.card - 1 - (split : ℕ)) ↦
          if hpiece.slope (owner (suffixCell k)) = hpiece.slope jLast then
            cellLen (suffixCell k)
          else 0)
    LrPlus * sigmaPlus + LrMinus * sigmaMinus = φ 1 - φ (1 - f) := by
  let s := augmentedBreakpoints hpiece f
  let e := augmentedBreakpointOrderEmb hpiece f
  have hs_pos : 0 < s.card := by
    exact Finset.card_pos.mpr ⟨0, by simpa [s] using zero_mem_augmentedBreakpoints (hpiece := hpiece) (f := f)⟩
  let owner : Fin (s.card - 1) → Fin hpiece.pieces := fun i ↦ augmentedCellOwner hf₀ hf₁ hpiece i
  let cellLen : Fin (s.card - 1) → ℝ :=
    fun i ↦ e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i)
  let suffixCell : Fin (s.card - 1 - (split : ℕ)) → Fin (s.card - 1) :=
    fun k ↦ ⟨(split : ℕ) + (k : ℕ), hsuffixBound k⟩
  let LrPlus : ℝ :=
    Finset.sum Finset.univ
      (fun k : Fin (s.card - 1 - (split : ℕ)) ↦
        if hpiece.slope (owner (suffixCell k)) = hpiece.slope jFirst then
          cellLen (suffixCell k)
        else 0)
  let LrMinus : ℝ :=
    Finset.sum Finset.univ
      (fun k : Fin (s.card - 1 - (split : ℕ)) ↦
        if hpiece.slope (owner (suffixCell k)) = hpiece.slope jLast then
          cellLen (suffixCell k)
        else 0)
  have hslopes_ne : hpiece.slope jFirst ≠ hpiece.slope jLast := by
    linarith
  have hclassified :
      Finset.sum Finset.univ
        (fun k : Fin (s.card - 1 - (split : ℕ)) ↦
          (φ (e (consecutiveRight hs_pos (suffixCell k))) -
            φ (e (consecutiveLeft hs_pos (suffixCell k))))) =
        LrPlus * sigmaPlus + LrMinus * sigmaMinus := by
    calc
      Finset.sum Finset.univ
        (fun k : Fin (s.card - 1 - (split : ℕ)) ↦
          (φ (e (consecutiveRight hs_pos (suffixCell k))) -
            φ (e (consecutiveLeft hs_pos (suffixCell k)))))
          =
            Finset.sum Finset.univ
              (fun k : Fin (s.card - 1 - (split : ℕ)) ↦
                (if hpiece.slope (owner (suffixCell k)) = hpiece.slope jFirst then
                    cellLen (suffixCell k)
                  else 0) * sigmaPlus +
                  (if hpiece.slope (owner (suffixCell k)) = hpiece.slope jLast then
                    cellLen (suffixCell k)
                  else 0) * sigmaMinus) := by
              refine Finset.sum_congr rfl ?_
              intro k _hk
              rcases hinc k with hleft | hright
              · rcases hleft with ⟨hslope, hφ⟩
                have hnot : ¬ hpiece.slope (owner (suffixCell k)) = hpiece.slope jLast := by
                  intro hcontra
                  exact hslopes_ne (hslope.symm.trans hcontra)
                rw [if_pos hslope, if_neg hnot]
                simpa [cellLen, suffixCell, mul_comm, mul_left_comm, mul_assoc] using hφ
              · rcases hright with ⟨hslope, hφ⟩
                have hnot : ¬ hpiece.slope (owner (suffixCell k)) = hpiece.slope jFirst := by
                  intro hcontra
                  exact hslopes_ne (hcontra.symm.trans hslope)
                rw [if_neg hnot, if_pos hslope]
                simpa [cellLen, suffixCell, mul_comm, mul_left_comm, mul_assoc] using hφ
      _ =
          (Finset.sum Finset.univ
            (fun k : Fin (s.card - 1 - (split : ℕ)) ↦
              if hpiece.slope (owner (suffixCell k)) = hpiece.slope jFirst then
                cellLen (suffixCell k)
              else 0)) * sigmaPlus +
            (Finset.sum Finset.univ
              (fun k : Fin (s.card - 1 - (split : ℕ)) ↦
                if hpiece.slope (owner (suffixCell k)) = hpiece.slope jLast then
                  cellLen (suffixCell k)
                else 0)) * sigmaMinus := by
              rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
      _ = LrPlus * sigmaPlus + LrMinus * sigmaMinus := by rfl
  have hsuffix_tel :
      Finset.sum Finset.univ
        (fun k : Fin (s.card - 1 - (split : ℕ)) ↦
          (φ (e (consecutiveRight hs_pos (suffixCell k))) -
            φ (e (consecutiveLeft hs_pos (suffixCell k))))) =
        φ (e ⟨s.card - 1, Nat.sub_lt hs_pos (Nat.succ_pos 0)⟩) - φ (e split) := by
    -- Normalize the suffix cells to the canonical `split, split + 1, ..., last` telescoping
    -- spelling.
    simpa [suffixCell, consecutiveLeft_val, consecutiveRight_val] using
      suffixIncrementTelescopesFromIndex hs_pos φ e split
  have hlast : e ⟨s.card - 1, Nat.sub_lt hs_pos (Nat.succ_pos 0)⟩ = 1 := by
    -- The right boundary equation ends at the last ordered augmented breakpoint `1`.
    simpa [e] using lastOrderedAugmentedBreakpoint_eq_one hf₀ hf₁ hpiece
  calc
    LrPlus * sigmaPlus + LrMinus * sigmaMinus
        = Finset.sum Finset.univ
            (fun k : Fin (s.card - 1 - (split : ℕ)) ↦
              (φ (e (consecutiveRight hs_pos (suffixCell k))) -
                φ (e (consecutiveLeft hs_pos (suffixCell k))))) := hclassified.symm
    _ = φ (e ⟨s.card - 1, Nat.sub_lt hs_pos (Nat.succ_pos 0)⟩) - φ (e split) := hsuffix_tel
    _ = φ 1 - φ (1 - f) := by rw [hlast, hsplit]

/-- Helper for Theorem 6.27: once the owner-cell coefficients are frozen, the prefix and suffix
classification lemmas package into the full two-equation boundary system. -/
private theorem slopeFamilyBoundarySystem_ofOwnerClassification
    {f : ℝ} (hf₀ : 0 < f) (hf₁ : f < 1)
    {π : ℝ → ℝ} (hpiece : PiecewiseLinearOnInterval 0 1 π)
    {split : Fin (augmentedBreakpoints hpiece f).card}
    (hsplit : augmentedBreakpointOrderEmb hpiece f split = 1 - f)
    {jFirst jLast : Fin hpiece.pieces}
    (hjFirst_pos : 0 < hpiece.slope jFirst)
    (hjLast_neg : hpiece.slope jLast < 0)
    (hprefixBound :
      ∀ k : Fin split, (k : ℕ) < (augmentedBreakpoints hpiece f).card - 1)
    (hsuffixBound :
      ∀ k : Fin ((augmentedBreakpoints hpiece f).card - 1 - (split : ℕ)),
        (split : ℕ) + (k : ℕ) < (augmentedBreakpoints hpiece f).card - 1)
    {φ : ℝ → ℝ} {sigmaPlus sigmaMinus : ℝ}
    (hprefix :
      ∀ k : Fin split,
        let s := augmentedBreakpoints hpiece f
        let e := augmentedBreakpointOrderEmb hpiece f
        let hs_pos : 0 < s.card := by
          exact Finset.card_pos.mpr ⟨0, zero_mem_augmentedBreakpoints⟩
        let i : Fin (s.card - 1) := ⟨k, hprefixBound k⟩
        let owner := augmentedCellOwner hf₀ hf₁ hpiece i
        ((hpiece.slope owner = hpiece.slope jFirst) ∧
            φ (e (consecutiveRight hs_pos i)) - φ (e (consecutiveLeft hs_pos i)) =
              sigmaPlus * (e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i)))
          ∨
          ((hpiece.slope owner = hpiece.slope jLast) ∧
            φ (e (consecutiveRight hs_pos i)) - φ (e (consecutiveLeft hs_pos i)) =
              sigmaMinus * (e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i))))
    (hsuffix :
      ∀ k : Fin ((augmentedBreakpoints hpiece f).card - 1 - (split : ℕ)),
        let s := augmentedBreakpoints hpiece f
        let e := augmentedBreakpointOrderEmb hpiece f
        let hs_pos : 0 < s.card := by
          exact Finset.card_pos.mpr ⟨0, zero_mem_augmentedBreakpoints⟩
        let i : Fin (s.card - 1) := ⟨(split : ℕ) + (k : ℕ), hsuffixBound k⟩
        let owner := augmentedCellOwner hf₀ hf₁ hpiece i
        ((hpiece.slope owner = hpiece.slope jFirst) ∧
            φ (e (consecutiveRight hs_pos i)) - φ (e (consecutiveLeft hs_pos i)) =
              sigmaPlus * (e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i)))
          ∨
          ((hpiece.slope owner = hpiece.slope jLast) ∧
            φ (e (consecutiveRight hs_pos i)) - φ (e (consecutiveLeft hs_pos i)) =
              sigmaMinus * (e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i)))) :
    let s := augmentedBreakpoints hpiece f
    let e := augmentedBreakpointOrderEmb hpiece f
    let hs_pos : 0 < s.card := by
      exact Finset.card_pos.mpr ⟨0, zero_mem_augmentedBreakpoints⟩
    let owner : Fin (s.card - 1) → Fin hpiece.pieces :=
      fun i ↦ augmentedCellOwner hf₀ hf₁ hpiece i
    let cellLen : Fin (s.card - 1) → ℝ :=
      fun i ↦ e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i)
    let prefixCell : Fin split → Fin (s.card - 1) := fun k ↦ ⟨k, hprefixBound k⟩
    let suffixCell : Fin (s.card - 1 - (split : ℕ)) → Fin (s.card - 1) :=
      fun k ↦ ⟨(split : ℕ) + (k : ℕ), hsuffixBound k⟩
    let LlPlus : ℝ :=
      Finset.sum Finset.univ
        (fun k : Fin split ↦
          if hpiece.slope (owner (prefixCell k)) = hpiece.slope jFirst then
            cellLen (prefixCell k)
          else 0)
    let LlMinus : ℝ :=
      Finset.sum Finset.univ
        (fun k : Fin split ↦
          if hpiece.slope (owner (prefixCell k)) = hpiece.slope jLast then
            cellLen (prefixCell k)
          else 0)
    let LrPlus : ℝ :=
      Finset.sum Finset.univ
        (fun k : Fin (s.card - 1 - (split : ℕ)) ↦
          if hpiece.slope (owner (suffixCell k)) = hpiece.slope jFirst then
            cellLen (suffixCell k)
          else 0)
    let LrMinus : ℝ :=
      Finset.sum Finset.univ
        (fun k : Fin (s.card - 1 - (split : ℕ)) ↦
          if hpiece.slope (owner (suffixCell k)) = hpiece.slope jLast then
            cellLen (suffixCell k)
          else 0)
    (LlPlus * sigmaPlus + LlMinus * sigmaMinus = φ (1 - f) - φ 0) ∧
      (LrPlus * sigmaPlus + LrMinus * sigmaMinus = φ 1 - φ (1 - f)) := by
  let s := augmentedBreakpoints hpiece f
  let e := augmentedBreakpointOrderEmb hpiece f
  let hs_pos : 0 < s.card := by
    exact Finset.card_pos.mpr ⟨0, zero_mem_augmentedBreakpoints⟩
  let owner : Fin (s.card - 1) → Fin hpiece.pieces := fun i ↦ augmentedCellOwner hf₀ hf₁ hpiece i
  let cellLen : Fin (s.card - 1) → ℝ :=
    fun i ↦ e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i)
  let prefixCell : Fin split → Fin (s.card - 1) := fun k ↦ ⟨k, hprefixBound k⟩
  let suffixCell : Fin (s.card - 1 - (split : ℕ)) → Fin (s.card - 1) :=
    fun k ↦ ⟨(split : ℕ) + (k : ℕ), hsuffixBound k⟩
  let LlPlus : ℝ :=
    Finset.sum Finset.univ
      (fun k : Fin split ↦
        if hpiece.slope (owner (prefixCell k)) = hpiece.slope jFirst then
          cellLen (prefixCell k)
        else 0)
  let LlMinus : ℝ :=
    Finset.sum Finset.univ
      (fun k : Fin split ↦
        if hpiece.slope (owner (prefixCell k)) = hpiece.slope jLast then
          cellLen (prefixCell k)
        else 0)
  let LrPlus : ℝ :=
    Finset.sum Finset.univ
      (fun k : Fin (s.card - 1 - (split : ℕ)) ↦
        if hpiece.slope (owner (suffixCell k)) = hpiece.slope jFirst then
          cellLen (suffixCell k)
        else 0)
  let LrMinus : ℝ :=
    Finset.sum Finset.univ
      (fun k : Fin (s.card - 1 - (split : ℕ)) ↦
        if hpiece.slope (owner (suffixCell k)) = hpiece.slope jLast then
          cellLen (suffixCell k)
        else 0)
  constructor
  · -- Reuse the prefix classification lemma in the frozen owner/cell-length normal form.
    simpa [s, e, hs_pos, owner, cellLen, prefixCell, LlPlus, LlMinus] using
      classifiedPrefixBoundaryEquation_ofOwnerSums hf₀ hf₁ hpiece hsplit hjFirst_pos hjLast_neg
        hprefixBound
        (φ := φ) (sigmaPlus := sigmaPlus) (sigmaMinus := sigmaMinus) hprefix
  · -- Apply the same normal form to the suffix side of the split.
    simpa [s, e, hs_pos, owner, cellLen, suffixCell, LrPlus, LrMinus] using
      classifiedSuffixBoundaryEquation_ofOwnerSums hf₀ hf₁ hpiece hsplit hjFirst_pos hjLast_neg
        hsuffixBound
        (φ := φ) (sigmaPlus := sigmaPlus) (sigmaMinus := sigmaMinus) hsuffix

/-- Helper for Theorem 6.27: once a cell is classified by the concrete endpoint slope families,
both midpoint components have the corresponding classified increment on that cell. -/
private theorem midpointComponentsCellIncrementOfSlopeFamily
    {f : ℝ} (hf₀ : 0 < f) (hf₁ : f < 1)
    {π π₁ π₂ : ℝ → ℝ}
    (hπ : pure_integer_minimal_valid_function_on_R f π)
    (hpiece : PiecewiseLinearOnInterval 0 1 π)
    (hπ₁ : pure_integer_valid_function_on_R f π₁)
    (hπ₂ : pure_integer_valid_function_on_R f π₂)
    (hmid : π = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂)
    (hπ_periodic : Function.Periodic π 1)
    (hπ₁_periodic : Function.Periodic π₁ 1)
    (hπ₂_periodic : Function.Periodic π₂ 1)
    (hπ₁_bdd : BoundedOnBoundedIntervals π₁)
    (hπ₂_bdd : BoundedOnBoundedIntervals π₂)
    {jFirst jLast : Fin hpiece.pieces}
    {bFirst aLast sigma₁Left sigma₂Left sigma₁Right sigma₂Right : ℝ}
    (hbFirst_pos : 0 < bFirst)
    (hπ_first : Set.EqOn π (fun x ↦ hpiece.slope jFirst * x) (Set.Icc (0 : ℝ) bFirst))
    (hπ₁_first : Set.EqOn π₁ (fun x ↦ sigma₁Left * x) (Set.Icc (0 : ℝ) bFirst))
    (hπ₂_first : Set.EqOn π₂ (fun x ↦ sigma₂Left * x) (Set.Icc (0 : ℝ) bFirst))
    (haLast_lt : aLast < 1)
    (hπ_last : Set.EqOn π (fun x ↦ hpiece.slope jLast * x - hpiece.slope jLast) (Set.Icc aLast 1))
    (hπ₁_last : Set.EqOn π₁ (fun x ↦ sigma₁Right * x - sigma₁Right) (Set.Icc aLast 1))
    (hπ₂_last : Set.EqOn π₂ (fun x ↦ sigma₂Right * x - sigma₂Right) (Set.Icc aLast 1))
    (hrawSlopeClassify :
      ∀ j : Fin hpiece.pieces,
        hpiece.slope j = hpiece.slope jFirst ∨ hpiece.slope j = hpiece.slope jLast)
    (i : Fin ((augmentedBreakpoints hpiece f).card - 1)) :
    let s := augmentedBreakpoints hpiece f
    let e := augmentedBreakpointOrderEmb hpiece f
    let hs_pos : 0 < s.card := by
      exact Finset.card_pos.mpr ⟨0, zero_mem_augmentedBreakpoints⟩
    let owner := augmentedCellOwner hf₀ hf₁ hpiece i
    ((hpiece.slope owner = hpiece.slope jFirst) ∧
        π₁ (e (consecutiveRight hs_pos i)) - π₁ (e (consecutiveLeft hs_pos i)) =
          sigma₁Left * (e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i)) ∧
        π₂ (e (consecutiveRight hs_pos i)) - π₂ (e (consecutiveLeft hs_pos i)) =
          sigma₂Left * (e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i)))
      ∨
      ((hpiece.slope owner = hpiece.slope jLast) ∧
        π₁ (e (consecutiveRight hs_pos i)) - π₁ (e (consecutiveLeft hs_pos i)) =
          sigma₁Right * (e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i)) ∧
        π₂ (e (consecutiveRight hs_pos i)) - π₂ (e (consecutiveLeft hs_pos i)) =
          sigma₂Right * (e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i))) := by
  let s := augmentedBreakpoints hpiece f
  let e := augmentedBreakpointOrderEmb hpiece f
  have hs_pos : 0 < s.card := by
    exact Finset.card_pos.mpr ⟨0, by simpa [s] using zero_mem_augmentedBreakpoints (hpiece := hpiece) (f := f)⟩
  let owner := augmentedCellOwner hf₀ hf₁ hpiece i
  let a : ℝ := e (consecutiveLeft hs_pos i)
  let b : ℝ := e (consecutiveRight hs_pos i)
  have hlen_pos : 0 < b - a := by
    simpa [a, b] using consecutiveCellLength_pos hs_pos e.strictMono i
  have hab : a ≤ b := by
    linarith
  have hcell :
      Set.EqOn π (fun x ↦ hpiece.slope owner * x + hpiece.intercept owner) (Set.Icc a b) := by
    simpa [a, b, owner] using augmentedCellOwner_spec hf₀ hf₁ hpiece i
  rcases hrawSlopeClassify owner with hs | hs
  · let ε : ℝ := min (bFirst / 2) ((b - a) / 2)
    have hε_pos : 0 < ε := by
      dsimp [ε]
      apply lt_min
      · linarith
      · linarith
    have hε_lt : ε < b - a := by
      have hmin_le : ε ≤ (b - a) / 2 := min_le_right _ _
      have hhalf_lt : (b - a) / 2 < b - a := by
        linarith
      exact lt_of_le_of_lt hmin_le hhalf_lt
    have hε_le_bFirst : ε ≤ bFirst := by
      have hmin_le : ε ≤ bFirst / 2 := min_le_left _ _
      linarith
    have hπ_anchor : Set.EqOn π (fun x ↦ hpiece.slope jFirst * x) (Set.Icc (0 : ℝ) ε) := by
      intro x hx
      exact hπ_first ⟨hx.1, le_trans hx.2 hε_le_bFirst⟩
    have hπ₁_anchor : Set.EqOn π₁ (fun x ↦ sigma₁Left * x) (Set.Icc (0 : ℝ) ε) := by
      intro x hx
      exact hπ₁_first ⟨hx.1, le_trans hx.2 hε_le_bFirst⟩
    have hπ₂_anchor : Set.EqOn π₂ (fun x ↦ sigma₂Left * x) (Set.Icc (0 : ℝ) ε) := by
      intro x hx
      exact hπ₂_first ⟨hx.1, le_trans hx.2 hε_le_bFirst⟩
    have htarget :
        Set.EqOn π (fun x ↦ hpiece.slope jFirst * x + hpiece.intercept owner) (Set.Icc a b) := by
      simpa [hs] using hcell
    rcases midpointComponentsAffineOnLeftSlopeFamily
        hπ hπ₁ hπ₂ hmid hπ₁_bdd hπ₂_bdd hε_pos hε_lt
        hπ_anchor htarget hπ₁_anchor hπ₂_anchor with
      ⟨d₁, d₂, hφ₁, hφ₂⟩
    have hinc₁ := affineIncrement_eq_smul_sub hab hφ₁
    have hinc₂ := affineIncrement_eq_smul_sub hab hφ₂
    exact Or.inl ⟨hs, by simpa [a, b] using hinc₁, by simpa [a, b] using hinc₂⟩
  · let ε : ℝ := min ((1 - aLast) / 2) ((b - a) / 2)
    have hε_pos : 0 < ε := by
      dsimp [ε]
      apply lt_min
      · linarith
      · linarith
    have hε_lt : ε < b - a := by
      have hmin_le : ε ≤ (b - a) / 2 := min_le_right _ _
      have hhalf_lt : (b - a) / 2 < b - a := by
        linarith
      exact lt_of_le_of_lt hmin_le hhalf_lt
    have hε_le_right : ε ≤ 1 - aLast := by
      have hmin_le : ε ≤ (1 - aLast) / 2 := min_le_left _ _
      linarith
    have haLast_le : aLast ≤ 1 - ε := by
      linarith
    have hπ_anchor :
        Set.EqOn π (fun x ↦ hpiece.slope jLast * x - hpiece.slope jLast) (Set.Icc (1 - ε) 1) := by
      intro x hx
      exact hπ_last ⟨le_trans haLast_le hx.1, hx.2⟩
    have hπ₁_anchor :
        Set.EqOn π₁ (fun x ↦ sigma₁Right * x - sigma₁Right) (Set.Icc (1 - ε) 1) := by
      intro x hx
      exact hπ₁_last ⟨le_trans haLast_le hx.1, hx.2⟩
    have hπ₂_anchor :
        Set.EqOn π₂ (fun x ↦ sigma₂Right * x - sigma₂Right) (Set.Icc (1 - ε) 1) := by
      intro x hx
      exact hπ₂_last ⟨le_trans haLast_le hx.1, hx.2⟩
    have htarget :
        Set.EqOn π (fun x ↦ hpiece.slope jLast * x + hpiece.intercept owner) (Set.Icc a b) := by
      simpa [hs, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hcell
    rcases midpointComponentsAffineOnRightSlopeFamily
        hπ hπ₁ hπ₂ hmid hπ_periodic hπ₁_periodic hπ₂_periodic hπ₁_bdd hπ₂_bdd
        hε_pos hε_lt htarget hπ_anchor hπ₁_anchor hπ₂_anchor with
      ⟨d₁, d₂, hφ₁, hφ₂⟩
    have hinc₁ := affineIncrement_eq_smul_sub hab hφ₁
    have hinc₂ := affineIncrement_eq_smul_sub hab hφ₂
    exact Or.inr ⟨hs, by simpa [a, b] using hinc₁, by simpa [a, b] using hinc₂⟩

/-- Helper for Theorem 6.27: the boundary equations coming from the ordered augmented cells force
the midpoint-component slope pairs to match the raw slopes. -/
private theorem midpointComponentSlopePairs_eq_rawSlopes
    {f : ℝ} (hf₀ : 0 < f) (hf₁ : f < 1)
    {π π₁ π₂ : ℝ → ℝ}
    (hπ : pure_integer_minimal_valid_function_on_R f π)
    (hpiece : PiecewiseLinearOnInterval 0 1 π)
    (hπ₁ : pure_integer_valid_function_on_R f π₁)
    (hπ₂ : pure_integer_valid_function_on_R f π₂)
    (hmid : π = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂)
    (hπ_periodic : Function.Periodic π 1)
    (hπ₁_periodic : Function.Periodic π₁ 1)
    (hπ₂_periodic : Function.Periodic π₂ 1)
    (hπ_zero : π 0 = 0)
    (hπ_one : π 1 = 0)
    (hπ_one_sub_f : π (1 - f) = 1)
    (hπ₁_zero : π₁ 0 = 0)
    (hπ₁_one : π₁ 1 = 0)
    (hπ₁_one_sub_f : π₁ (1 - f) = 1)
    (hπ₂_zero : π₂ 0 = 0)
    (hπ₂_one : π₂ 1 = 0)
    (hπ₂_one_sub_f : π₂ (1 - f) = 1)
    (hπ₁_bdd : BoundedOnBoundedIntervals π₁)
    (hπ₂_bdd : BoundedOnBoundedIntervals π₂)
    {split : Fin (augmentedBreakpoints hpiece f).card}
    (hsplit : augmentedBreakpointOrderEmb hpiece f split = 1 - f)
    {jFirst jLast : Fin hpiece.pieces}
    (hjFirst_pos : 0 < hpiece.slope jFirst)
    (hjLast_neg : hpiece.slope jLast < 0)
    {bFirst sigma₁Left sigma₂Left : ℝ}
    (hbFirst_pos : 0 < bFirst)
    (hπ_first : Set.EqOn π (fun x ↦ hpiece.slope jFirst * x) (Set.Icc (0 : ℝ) bFirst))
    (hπ₁_first : Set.EqOn π₁ (fun x ↦ sigma₁Left * x) (Set.Icc (0 : ℝ) bFirst))
    (hπ₂_first : Set.EqOn π₂ (fun x ↦ sigma₂Left * x) (Set.Icc (0 : ℝ) bFirst))
    {aLast sigma₁Right sigma₂Right : ℝ}
    (haLast_lt : aLast < 1)
    (hπ_last : Set.EqOn π (fun x ↦ hpiece.slope jLast * x - hpiece.slope jLast) (Set.Icc aLast 1))
    (hπ₁_last : Set.EqOn π₁ (fun x ↦ sigma₁Right * x - sigma₁Right) (Set.Icc aLast 1))
    (hπ₂_last : Set.EqOn π₂ (fun x ↦ sigma₂Right * x - sigma₂Right) (Set.Icc aLast 1))
    (hrawSlopeClassify :
      ∀ j : Fin hpiece.pieces,
        hpiece.slope j = hpiece.slope jFirst ∨ hpiece.slope j = hpiece.slope jLast) :
    sigma₁Left = hpiece.slope jFirst ∧
      sigma₁Right = hpiece.slope jLast ∧
        sigma₂Left = hpiece.slope jFirst ∧
          sigma₂Right = hpiece.slope jLast := by
  let s := augmentedBreakpoints hpiece f
  let e := augmentedBreakpointOrderEmb hpiece f
  have hs_pos : 0 < s.card := by
    exact Finset.card_pos.mpr ⟨0, by simpa [s] using zero_mem_augmentedBreakpoints (hpiece := hpiece) (f := f)⟩
  have hsplitBounds := splitIndexBoundsOfOneMinusF hf₀ hf₁ (hpiece := hpiece) hsplit
  let owner : Fin (s.card - 1) → Fin hpiece.pieces := fun i ↦ augmentedCellOwner hf₀ hf₁ hpiece i
  let cellLen : Fin (s.card - 1) → ℝ :=
    fun i ↦ e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i)
  let prefixCell : Fin split → Fin (s.card - 1) := fun k ↦ ⟨k, lt_trans k.is_lt hsplitBounds.2⟩
  let suffixCell : Fin (s.card - 1 - (split : ℕ)) → Fin (s.card - 1) :=
    fun k ↦ ⟨(split : ℕ) + (k : ℕ), by
      have hk_lt : (k : ℕ) < s.card - 1 - (split : ℕ) := k.is_lt
      omega⟩
  let LlPlus : ℝ :=
    Finset.sum Finset.univ
      (fun k : Fin split ↦
        if hpiece.slope (owner (prefixCell k)) = hpiece.slope jFirst then
          cellLen (prefixCell k)
        else 0)
  let LlMinus : ℝ :=
    Finset.sum Finset.univ
      (fun k : Fin split ↦
        if hpiece.slope (owner (prefixCell k)) = hpiece.slope jLast then
          cellLen (prefixCell k)
        else 0)
  let LrPlus : ℝ :=
    Finset.sum Finset.univ
      (fun k : Fin (s.card - 1 - (split : ℕ)) ↦
        if hpiece.slope (owner (suffixCell k)) = hpiece.slope jFirst then
          cellLen (suffixCell k)
        else 0)
  let LrMinus : ℝ :=
    Finset.sum Finset.univ
      (fun k : Fin (s.card - 1 - (split : ℕ)) ↦
        if hpiece.slope (owner (suffixCell k)) = hpiece.slope jLast then
          cellLen (suffixCell k)
        else 0)
  have hrawPrefix :
      ∀ k : Fin split,
        let i : Fin (s.card - 1) := prefixCell k
        let ownerCell := owner i
        ((hpiece.slope ownerCell = hpiece.slope jFirst) ∧
            π (e (consecutiveRight hs_pos i)) - π (e (consecutiveLeft hs_pos i)) =
              hpiece.slope jFirst * cellLen i)
          ∨
          ((hpiece.slope ownerCell = hpiece.slope jLast) ∧
            π (e (consecutiveRight hs_pos i)) - π (e (consecutiveLeft hs_pos i)) =
              hpiece.slope jLast * cellLen i) := by
    intro k
    let i : Fin (s.card - 1) := prefixCell k
    simpa [s, e, hs_pos, owner, cellLen, prefixCell, i] using
      rawCellIncrementOfSlopeFamily hf₀ hf₁ hpiece hrawSlopeClassify i
  have hrawSuffix :
      ∀ k : Fin (s.card - 1 - (split : ℕ)),
        let i : Fin (s.card - 1) := suffixCell k
        let ownerCell := owner i
        ((hpiece.slope ownerCell = hpiece.slope jFirst) ∧
            π (e (consecutiveRight hs_pos i)) - π (e (consecutiveLeft hs_pos i)) =
              hpiece.slope jFirst * cellLen i)
          ∨
          ((hpiece.slope ownerCell = hpiece.slope jLast) ∧
            π (e (consecutiveRight hs_pos i)) - π (e (consecutiveLeft hs_pos i)) =
              hpiece.slope jLast * cellLen i) := by
    intro k
    let i : Fin (s.card - 1) := suffixCell k
    simpa [s, e, hs_pos, owner, cellLen, suffixCell, i] using
      rawCellIncrementOfSlopeFamily hf₀ hf₁ hpiece hrawSlopeClassify i
  have hπ₁Prefix :
      ∀ k : Fin split,
        let i : Fin (s.card - 1) := prefixCell k
        let ownerCell := owner i
        ((hpiece.slope ownerCell = hpiece.slope jFirst) ∧
            π₁ (e (consecutiveRight hs_pos i)) - π₁ (e (consecutiveLeft hs_pos i)) =
              sigma₁Left * cellLen i)
          ∨
          ((hpiece.slope ownerCell = hpiece.slope jLast) ∧
            π₁ (e (consecutiveRight hs_pos i)) - π₁ (e (consecutiveLeft hs_pos i)) =
              sigma₁Right * cellLen i) := by
    intro k
    let i : Fin (s.card - 1) := prefixCell k
    rcases midpointComponentsCellIncrementOfSlopeFamily
        hf₀ hf₁ hπ hpiece hπ₁ hπ₂ hmid hπ_periodic hπ₁_periodic hπ₂_periodic hπ₁_bdd hπ₂_bdd
        hbFirst_pos hπ_first hπ₁_first hπ₂_first haLast_lt hπ_last hπ₁_last hπ₂_last
        hrawSlopeClassify i with hleft | hright
    · exact Or.inl ⟨hleft.1, by simpa [s, e, hs_pos, owner, cellLen, prefixCell, i] using hleft.2.1⟩
    · exact Or.inr ⟨hright.1, by simpa [s, e, hs_pos, owner, cellLen, prefixCell, i] using hright.2.1⟩
  have hπ₁Suffix :
      ∀ k : Fin (s.card - 1 - (split : ℕ)),
        let i : Fin (s.card - 1) := suffixCell k
        let ownerCell := owner i
        ((hpiece.slope ownerCell = hpiece.slope jFirst) ∧
            π₁ (e (consecutiveRight hs_pos i)) - π₁ (e (consecutiveLeft hs_pos i)) =
              sigma₁Left * cellLen i)
          ∨
          ((hpiece.slope ownerCell = hpiece.slope jLast) ∧
            π₁ (e (consecutiveRight hs_pos i)) - π₁ (e (consecutiveLeft hs_pos i)) =
              sigma₁Right * cellLen i) := by
    intro k
    let i : Fin (s.card - 1) := suffixCell k
    rcases midpointComponentsCellIncrementOfSlopeFamily
        hf₀ hf₁ hπ hpiece hπ₁ hπ₂ hmid hπ_periodic hπ₁_periodic hπ₂_periodic hπ₁_bdd hπ₂_bdd
        hbFirst_pos hπ_first hπ₁_first hπ₂_first haLast_lt hπ_last hπ₁_last hπ₂_last
        hrawSlopeClassify i with hleft | hright
    · exact Or.inl ⟨hleft.1, by simpa [s, e, hs_pos, owner, cellLen, suffixCell, i] using hleft.2.1⟩
    · exact Or.inr ⟨hright.1, by simpa [s, e, hs_pos, owner, cellLen, suffixCell, i] using hright.2.1⟩
  have hπ₂Prefix :
      ∀ k : Fin split,
        let i : Fin (s.card - 1) := prefixCell k
        let ownerCell := owner i
        ((hpiece.slope ownerCell = hpiece.slope jFirst) ∧
            π₂ (e (consecutiveRight hs_pos i)) - π₂ (e (consecutiveLeft hs_pos i)) =
              sigma₂Left * cellLen i)
          ∨
          ((hpiece.slope ownerCell = hpiece.slope jLast) ∧
            π₂ (e (consecutiveRight hs_pos i)) - π₂ (e (consecutiveLeft hs_pos i)) =
              sigma₂Right * cellLen i) := by
    intro k
    let i : Fin (s.card - 1) := prefixCell k
    rcases midpointComponentsCellIncrementOfSlopeFamily
        hf₀ hf₁ hπ hpiece hπ₁ hπ₂ hmid hπ_periodic hπ₁_periodic hπ₂_periodic hπ₁_bdd hπ₂_bdd
        hbFirst_pos hπ_first hπ₁_first hπ₂_first haLast_lt hπ_last hπ₁_last hπ₂_last
        hrawSlopeClassify i with hleft | hright
    · exact Or.inl ⟨hleft.1, by simpa [s, e, hs_pos, owner, cellLen, prefixCell, i] using hleft.2.2⟩
    · exact Or.inr ⟨hright.1, by simpa [s, e, hs_pos, owner, cellLen, prefixCell, i] using hright.2.2⟩
  have hπ₂Suffix :
      ∀ k : Fin (s.card - 1 - (split : ℕ)),
        let i : Fin (s.card - 1) := suffixCell k
        let ownerCell := owner i
        ((hpiece.slope ownerCell = hpiece.slope jFirst) ∧
            π₂ (e (consecutiveRight hs_pos i)) - π₂ (e (consecutiveLeft hs_pos i)) =
              sigma₂Left * cellLen i)
          ∨
          ((hpiece.slope ownerCell = hpiece.slope jLast) ∧
            π₂ (e (consecutiveRight hs_pos i)) - π₂ (e (consecutiveLeft hs_pos i)) =
              sigma₂Right * cellLen i) := by
    intro k
    let i : Fin (s.card - 1) := suffixCell k
    rcases midpointComponentsCellIncrementOfSlopeFamily
        hf₀ hf₁ hπ hpiece hπ₁ hπ₂ hmid hπ_periodic hπ₁_periodic hπ₂_periodic hπ₁_bdd hπ₂_bdd
        hbFirst_pos hπ_first hπ₁_first hπ₂_first haLast_lt hπ_last hπ₁_last hπ₂_last
        hrawSlopeClassify i with hleft | hright
    · exact Or.inl ⟨hleft.1, by simpa [s, e, hs_pos, owner, cellLen, suffixCell, i] using hleft.2.2⟩
    · exact Or.inr ⟨hright.1, by simpa [s, e, hs_pos, owner, cellLen, suffixCell, i] using hright.2.2⟩
  have hrawSystem :
      LlPlus * hpiece.slope jFirst + LlMinus * hpiece.slope jLast = π (1 - f) - π 0 ∧
        LrPlus * hpiece.slope jFirst + LrMinus * hpiece.slope jLast = π 1 - π (1 - f) := by
    simpa [s, e, hs_pos, owner, cellLen, prefixCell, suffixCell, LlPlus, LlMinus, LrPlus, LrMinus] using
      slopeFamilyBoundarySystem_ofOwnerClassification hf₀ hf₁ hpiece hsplit hjFirst_pos hjLast_neg
        (fun k ↦ lt_trans k.is_lt hsplitBounds.2)
        (fun k ↦ by
          have hk_lt : (k : ℕ) < s.card - 1 - (split : ℕ) := k.is_lt
          omega)
        (φ := π) (sigmaPlus := hpiece.slope jFirst) (sigmaMinus := hpiece.slope jLast)
        hrawPrefix hrawSuffix
  have hπ₁System :
      LlPlus * sigma₁Left + LlMinus * sigma₁Right = π₁ (1 - f) - π₁ 0 ∧
        LrPlus * sigma₁Left + LrMinus * sigma₁Right = π₁ 1 - π₁ (1 - f) := by
    simpa [s, e, hs_pos, owner, cellLen, prefixCell, suffixCell, LlPlus, LlMinus, LrPlus, LrMinus] using
      slopeFamilyBoundarySystem_ofOwnerClassification hf₀ hf₁ hpiece hsplit hjFirst_pos hjLast_neg
        (fun k ↦ lt_trans k.is_lt hsplitBounds.2)
        (fun k ↦ by
          have hk_lt : (k : ℕ) < s.card - 1 - (split : ℕ) := k.is_lt
          omega)
        (φ := π₁) (sigmaPlus := sigma₁Left) (sigmaMinus := sigma₁Right)
        hπ₁Prefix hπ₁Suffix
  have hπ₂System :
      LlPlus * sigma₂Left + LlMinus * sigma₂Right = π₂ (1 - f) - π₂ 0 ∧
        LrPlus * sigma₂Left + LrMinus * sigma₂Right = π₂ 1 - π₂ (1 - f) := by
    simpa [s, e, hs_pos, owner, cellLen, prefixCell, suffixCell, LlPlus, LlMinus, LrPlus, LrMinus] using
      slopeFamilyBoundarySystem_ofOwnerClassification hf₀ hf₁ hpiece hsplit hjFirst_pos hjLast_neg
        (fun k ↦ lt_trans k.is_lt hsplitBounds.2)
        (fun k ↦ by
          have hk_lt : (k : ℕ) < s.card - 1 - (split : ℕ) := k.is_lt
          omega)
        (φ := π₂) (sigmaPlus := sigma₂Left) (sigmaMinus := sigma₂Right)
        hπ₂Prefix hπ₂Suffix
  have hrawLeft : LlPlus * hpiece.slope jFirst + LlMinus * hpiece.slope jLast = 1 := by
    simpa [hπ_zero, hπ_one_sub_f] using hrawSystem.1
  have hrawRight : LrPlus * hpiece.slope jFirst + LrMinus * hpiece.slope jLast = -1 := by
    simpa [hπ_one, hπ_one_sub_f] using hrawSystem.2
  have hπ₁Left : LlPlus * sigma₁Left + LlMinus * sigma₁Right = 1 := by
    simpa [hπ₁_zero, hπ₁_one_sub_f] using hπ₁System.1
  have hπ₁Right : LrPlus * sigma₁Left + LrMinus * sigma₁Right = -1 := by
    simpa [hπ₁_one, hπ₁_one_sub_f] using hπ₁System.2
  have hπ₂Left : LlPlus * sigma₂Left + LlMinus * sigma₂Right = 1 := by
    simpa [hπ₂_zero, hπ₂_one_sub_f] using hπ₂System.1
  have hπ₂Right : LrPlus * sigma₂Left + LrMinus * sigma₂Right = -1 := by
    simpa [hπ₂_one, hπ₂_one_sub_f] using hπ₂System.2
  have hLlMinus_nonneg : 0 ≤ LlMinus := by
    -- Every classified coefficient is either a cell length or `0`, hence nonnegative.
    refine Finset.sum_nonneg ?_
    intro k _hk
    by_cases hclass : hpiece.slope (owner (prefixCell k)) = hpiece.slope jLast
    · have hlen_pos : 0 < cellLen (prefixCell k) := by
        simpa [cellLen] using consecutiveCellLength_pos hs_pos e.strictMono (prefixCell k)
      simp [hclass, hlen_pos.le]
    · simp [hclass]
  have hLrPlus_nonneg : 0 ≤ LrPlus := by
    -- The suffix positive-family coefficient is the same kind of length sum.
    refine Finset.sum_nonneg ?_
    intro k _hk
    by_cases hclass : hpiece.slope (owner (suffixCell k)) = hpiece.slope jFirst
    · have hlen_pos : 0 < cellLen (suffixCell k) := by
        simpa [cellLen] using consecutiveCellLength_pos hs_pos e.strictMono (suffixCell k)
      simp [hclass, hlen_pos.le]
    · simp [hclass]
  have hLlPlus_pos : 0 < LlPlus := by
    -- The raw left boundary equation is positive, so the positive-slope coefficient cannot vanish.
    by_contra hnonpos
    have hLlPlus_nonpos : LlPlus ≤ 0 := le_of_not_gt hnonpos
    have htermPlus : LlPlus * hpiece.slope jFirst ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg hLlPlus_nonpos hjFirst_pos.le
    have htermMinus : LlMinus * hpiece.slope jLast ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos hLlMinus_nonneg hjLast_neg.le
    linarith [hrawLeft, htermPlus, htermMinus]
  have hσ₁ :
      sigma₁Left = hpiece.slope jFirst ∧ sigma₁Right = hpiece.slope jLast := by
    -- The first midpoint component solves the same boundary system as the raw slope pair.
    exact slopePairUniqueOfBoundarySystem hLlPlus_pos hLrPlus_nonneg
      hπ₁Left hπ₁Right hrawLeft hrawRight
  have hσ₂ :
      sigma₂Left = hpiece.slope jFirst ∧ sigma₂Right = hpiece.slope jLast := by
    -- The second midpoint component is forced by the same uniqueness argument.
    exact slopePairUniqueOfBoundarySystem hLlPlus_pos hLrPlus_nonneg
      hπ₂Left hπ₂Right hrawLeft hrawRight
  exact ⟨hσ₁.1, hσ₁.2, hσ₂.1, hσ₂.2⟩

/-- Helper for Theorem 6.27: once the interval-lemma partition argument is carried out, the
midpoint components must agree with `π` on the full unit interval. -/
theorem midpointComponents_eqOn_unitInterval_of_twoSlope
    {f : ℝ} (hf₀ : 0 < f) (hf₁ : f < 1) {π π₁ π₂ : ℝ → ℝ}
    (hπ : pure_integer_minimal_valid_function_on_R f π)
    (hpiece : ContinuousTwoSlopePiecewiseLinearOnUnitInterval π)
    (hπ₁ : pure_integer_valid_function_on_R f π₁)
    (hπ₂ : pure_integer_valid_function_on_R f π₂)
    (hmid : π = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂) :
    Set.EqOn π π₁ (Set.Icc (0 : ℝ) 1) ∧
      Set.EqOn π π₂ (Set.Icc (0 : ℝ) 1) := by
  rcases midpointComponentsAreMinimalValidFunctionOnR hπ hπ₁ hπ₂ hmid with ⟨hπ₁_min, hπ₂_min⟩
  rcases ContinuousTwoSlopePiecewiseLinearOnUnitInterval.exists_piecewiseLinearOnInterval hpiece with
    ⟨hpwl, htwoSlope⟩
  rcases PiecewiseLinearOnInterval.hasAtMostTwoSlopes_iff.mp htwoSlope with
    ⟨slopeLeft, slopeRight, hcellSlope⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ with
    ⟨hπ_periodic, hπ_zero, hπ_one, hπ_one_sub_f, _hπ_bdd⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₁_min with
    ⟨hπ₁_periodic, hπ₁_zero, hπ₁_one, hπ₁_one_sub_f, hπ₁_bdd⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₂_min with
    ⟨hπ₂_periodic, hπ₂_zero, hπ₂_one, hπ₂_one_sub_f, hπ₂_bdd⟩
  rcases splitIndexOfOneMinusF (f := f) (hpiece := hpwl) with ⟨split, hsplit⟩
  rcases firstAugmentedCellAnchorFamily
      hf₀ hf₁ hπ hpwl hπ₁ hπ₂ hmid hπ_zero hπ₁_zero hπ₂_zero hπ₁_bdd hπ₂_bdd with
    ⟨jFirst, bFirst, sigma₁Left, sigma₂Left, hbFirst_pos, hπ_first, hπ₁_first, hπ₂_first⟩
  rcases lastAugmentedCellAnchorFamily
      hf₀ hf₁ hπ hpwl hπ₁ hπ₂ hmid hπ_periodic hπ₁_periodic hπ₂_periodic
      hπ_one hπ₁_one hπ₂_one hπ₁_bdd hπ₂_bdd with
    ⟨jLast, aLast, sigma₁Right, sigma₂Right, haLast_lt, hπ_last, hπ₁_last, hπ₂_last⟩
  rcases endpointRealizedSlopeOrientation
      hf₀ hf₁ hπ hpwl hcellSlope hsplit hbFirst_pos hπ_first haLast_lt hπ_last
      hπ_zero hπ_one hπ_one_sub_f with
    ⟨hjFirst_pos, hjLast_neg, hrawSlopeClassify⟩
  rcases midpointComponentSlopePairs_eq_rawSlopes
      hf₀ hf₁ hπ hpwl hπ₁ hπ₂ hmid hπ_periodic hπ₁_periodic hπ₂_periodic
      hπ_zero hπ_one hπ_one_sub_f hπ₁_zero hπ₁_one hπ₁_one_sub_f
      hπ₂_zero hπ₂_one hπ₂_one_sub_f hπ₁_bdd hπ₂_bdd hsplit hjFirst_pos hjLast_neg
      hbFirst_pos hπ_first hπ₁_first hπ₂_first haLast_lt hπ_last hπ₁_last hπ₂_last
      hrawSlopeClassify with
    ⟨hsigma₁Left, hsigma₁Right, hsigma₂Left, hsigma₂Right⟩
  let s := augmentedBreakpoints hpwl f
  let e := augmentedBreakpointOrderEmb hpwl f
  have hs_pos : 0 < s.card := by
    exact Finset.card_pos.mpr ⟨0, by simpa [s] using zero_mem_augmentedBreakpoints (hpiece := hpwl) (f := f)⟩
  let owner : Fin (s.card - 1) → Fin hpwl.pieces := fun i ↦ augmentedCellOwner hf₀ hf₁ hpwl i
  let cellLen : Fin (s.card - 1) → ℝ :=
    fun i ↦ e (consecutiveRight hs_pos i) - e (consecutiveLeft hs_pos i)
  have hfirst : e ⟨0, hs_pos⟩ = 0 := by
    -- Normalize the first ordered breakpoint before transporting equality along the chain.
    simpa [e] using firstOrderedAugmentedBreakpoint_eq_zero hf₀ hf₁ hpwl
  have hmatching₁ :
      ∀ i : Fin (s.card - 1),
        π (e (consecutiveRight hs_pos i)) - π (e (consecutiveLeft hs_pos i)) =
          π₁ (e (consecutiveRight hs_pos i)) - π₁ (e (consecutiveLeft hs_pos i)) := by
    intro i
    have hraw :
        π (e (consecutiveRight hs_pos i)) - π (e (consecutiveLeft hs_pos i)) =
          hpwl.slope (owner i) * cellLen i := by
      simpa [s, e, hs_pos, owner, cellLen] using
        augmentedCellOwnerIncrement_eq_pieceSlopeMulLength hf₀ hf₁ hpwl i
    rcases midpointComponentsCellIncrementOfSlopeFamily
        hf₀ hf₁ hπ hpwl hπ₁ hπ₂ hmid hπ_periodic hπ₁_periodic hπ₂_periodic hπ₁_bdd hπ₂_bdd
        hbFirst_pos hπ_first hπ₁_first hπ₂_first haLast_lt hπ_last hπ₁_last hπ₂_last
        hrawSlopeClassify i with hleft | hright
    · -- On a positive-family cell, both raw and midpoint-component increments use the left slope.
      calc
        π (e (consecutiveRight hs_pos i)) - π (e (consecutiveLeft hs_pos i))
            = hpwl.slope (owner i) * cellLen i := hraw
        _ = hpwl.slope jFirst * cellLen i := by rw [hleft.1]
        _ = sigma₁Left * cellLen i := by rw [hsigma₁Left]
        _ = π₁ (e (consecutiveRight hs_pos i)) - π₁ (e (consecutiveLeft hs_pos i)) := by
            symm
            exact hleft.2.1
    · -- The negative-family cells are handled by the right-slope companion data.
      calc
        π (e (consecutiveRight hs_pos i)) - π (e (consecutiveLeft hs_pos i))
            = hpwl.slope (owner i) * cellLen i := hraw
        _ = hpwl.slope jLast * cellLen i := by rw [hright.1]
        _ = sigma₁Right * cellLen i := by rw [hsigma₁Right]
        _ = π₁ (e (consecutiveRight hs_pos i)) - π₁ (e (consecutiveLeft hs_pos i)) := by
            symm
            exact hright.2.1
  have hmatching₂ :
      ∀ i : Fin (s.card - 1),
        π (e (consecutiveRight hs_pos i)) - π (e (consecutiveLeft hs_pos i)) =
          π₂ (e (consecutiveRight hs_pos i)) - π₂ (e (consecutiveLeft hs_pos i)) := by
    intro i
    have hraw :
        π (e (consecutiveRight hs_pos i)) - π (e (consecutiveLeft hs_pos i)) =
          hpwl.slope (owner i) * cellLen i := by
      simpa [s, e, hs_pos, owner, cellLen] using
        augmentedCellOwnerIncrement_eq_pieceSlopeMulLength hf₀ hf₁ hpwl i
    rcases midpointComponentsCellIncrementOfSlopeFamily
        hf₀ hf₁ hπ hpwl hπ₁ hπ₂ hmid hπ_periodic hπ₁_periodic hπ₂_periodic hπ₁_bdd hπ₂_bdd
        hbFirst_pos hπ_first hπ₁_first hπ₂_first haLast_lt hπ_last hπ₁_last hπ₂_last
        hrawSlopeClassify i with hleft | hright
    · -- The second midpoint component shares the same left-family increment after slope
      -- identification.
      calc
        π (e (consecutiveRight hs_pos i)) - π (e (consecutiveLeft hs_pos i))
            = hpwl.slope (owner i) * cellLen i := hraw
        _ = hpwl.slope jFirst * cellLen i := by rw [hleft.1]
        _ = sigma₂Left * cellLen i := by rw [hsigma₂Left]
        _ = π₂ (e (consecutiveRight hs_pos i)) - π₂ (e (consecutiveLeft hs_pos i)) := by
            symm
            exact hleft.2.2
    · -- The same argument works on negative-family cells with the right slope.
      calc
        π (e (consecutiveRight hs_pos i)) - π (e (consecutiveLeft hs_pos i))
            = hpwl.slope (owner i) * cellLen i := hraw
        _ = hpwl.slope jLast * cellLen i := by rw [hright.1]
        _ = sigma₂Right * cellLen i := by rw [hsigma₂Right]
        _ = π₂ (e (consecutiveRight hs_pos i)) - π₂ (e (consecutiveLeft hs_pos i)) := by
            symm
            exact hright.2.2
  have hstart₁ : π (e ⟨0, hs_pos⟩) = π₁ (e ⟨0, hs_pos⟩) := by
    simpa [hfirst, hπ_zero, hπ₁_zero]
  have hstart₂ : π (e ⟨0, hs_pos⟩) = π₂ (e ⟨0, hs_pos⟩) := by
    simpa [hfirst, hπ_zero, hπ₂_zero]
  have horderedEq₁ : ∀ k : Fin s.card, π (e k) = π₁ (e k) :=
    eqAtOrderedPoints_of_matchingIncrements hs_pos hstart₁ hmatching₁
  have horderedEq₂ : ∀ k : Fin s.card, π (e k) = π₂ (e k) :=
    eqAtOrderedPoints_of_matchingIncrements hs_pos hstart₂ hmatching₂
  have hcellAgreement :
      ∀ i : Fin (s.card - 1),
        let a := e (consecutiveLeft hs_pos i)
        let b := e (consecutiveRight hs_pos i)
        Set.EqOn π π₁ (Set.Icc a b) ∧ Set.EqOn π π₂ (Set.Icc a b) := by
    intro i
    let a : ℝ := e (consecutiveLeft hs_pos i)
    let b : ℝ := e (consecutiveRight hs_pos i)
    let ownerCell : Fin hpwl.pieces := owner i
    have hlen_pos : 0 < b - a := by
      simpa [a, b, cellLen] using consecutiveCellLength_pos hs_pos e.strictMono i
    have hab : a ≤ b := by
      linarith
    have ha_mem : a ∈ Set.Icc a b := by
      simp [hab]
    have hrawCell :
        Set.EqOn π (fun x ↦ hpwl.slope ownerCell * x + hpwl.intercept ownerCell) (Set.Icc a b) := by
      simpa [a, b, ownerCell, owner] using augmentedCellOwner_spec hf₀ hf₁ hpwl i
    have hanchor₁ : π a = π₁ a := by
      simpa [a] using horderedEq₁ (consecutiveLeft hs_pos i)
    have hanchor₂ : π a = π₂ a := by
      simpa [a] using horderedEq₂ (consecutiveLeft hs_pos i)
    rcases hrawSlopeClassify ownerCell with hownerFirst | hownerLast
    · let ε : ℝ := min (bFirst / 2) ((b - a) / 2)
      have hε_pos : 0 < ε := by
        dsimp [ε]
        apply lt_min <;> linarith
      have hε_lt : ε < b - a := by
        have hmin_le : ε ≤ (b - a) / 2 := min_le_right _ _
        have hhalf_lt : (b - a) / 2 < b - a := by
          linarith
        exact lt_of_le_of_lt hmin_le hhalf_lt
      have hε_le_bFirst : ε ≤ bFirst := by
        have hmin_le : ε ≤ bFirst / 2 := min_le_left _ _
        linarith
      have hπ_anchor : Set.EqOn π (fun x ↦ hpwl.slope jFirst * x) (Set.Icc (0 : ℝ) ε) := by
        intro x hx
        exact hπ_first ⟨hx.1, le_trans hx.2 hε_le_bFirst⟩
      have hπ₁_anchor_fixed :
          Set.EqOn π₁ (fun x ↦ hpwl.slope jFirst * x) (Set.Icc (0 : ℝ) ε) := by
        intro x hx
        have hbase := hπ₁_first ⟨hx.1, le_trans hx.2 hε_le_bFirst⟩
        simpa [hsigma₁Left] using hbase
      have hπ₂_anchor_fixed :
          Set.EqOn π₂ (fun x ↦ hpwl.slope jFirst * x) (Set.Icc (0 : ℝ) ε) := by
        intro x hx
        have hbase := hπ₂_first ⟨hx.1, le_trans hx.2 hε_le_bFirst⟩
        simpa [hsigma₂Left] using hbase
      have htarget :
          Set.EqOn π (fun x ↦ hpwl.slope jFirst * x + hpwl.intercept ownerCell) (Set.Icc a b) := by
        simpa [ownerCell, hownerFirst] using hrawCell
      rcases midpointComponentsAffineOnLeftSlopeFamily
          hπ hπ₁ hπ₂ hmid hπ₁_bdd hπ₂_bdd hε_pos hε_lt hπ_anchor htarget
          hπ₁_anchor_fixed hπ₂_anchor_fixed with
        ⟨d₁, d₂, hπ₁_cell_raw, hπ₂_cell_raw⟩
      have hπ₁_cell :
          Set.EqOn π₁ (fun x ↦ hpwl.slope ownerCell * x + d₁) (Set.Icc a b) := by
        simpa [ownerCell, hownerFirst] using hπ₁_cell_raw
      have hπ₂_cell :
          Set.EqOn π₂ (fun x ↦ hpwl.slope ownerCell * x + d₂) (Set.Icc a b) := by
        simpa [ownerCell, hownerFirst] using hπ₂_cell_raw
      refine ⟨?_, ?_⟩
      · -- Agreement at the left breakpoint and a shared affine slope force equality on the cell.
        exact eqOn_of_sharedAffineSlope_and_pointValue ha_mem hrawCell hπ₁_cell hanchor₁
      · -- The same left-breakpoint argument applies to the second midpoint component.
        exact eqOn_of_sharedAffineSlope_and_pointValue ha_mem hrawCell hπ₂_cell hanchor₂
    · let ε : ℝ := min ((1 - aLast) / 2) ((b - a) / 2)
      have hε_pos : 0 < ε := by
        dsimp [ε]
        apply lt_min <;> linarith
      have hε_lt : ε < b - a := by
        have hmin_le : ε ≤ (b - a) / 2 := min_le_right _ _
        have hhalf_lt : (b - a) / 2 < b - a := by
          linarith
        exact lt_of_le_of_lt hmin_le hhalf_lt
      have hε_le_right : ε ≤ 1 - aLast := by
        have hmin_le : ε ≤ (1 - aLast) / 2 := min_le_left _ _
        linarith
      have haLast_le : aLast ≤ 1 - ε := by
        linarith
      have hπ_anchor :
          Set.EqOn π (fun x ↦ hpwl.slope jLast * x - hpwl.slope jLast) (Set.Icc (1 - ε) 1) := by
        intro x hx
        exact hπ_last ⟨le_trans haLast_le hx.1, hx.2⟩
      have hπ₁_anchor_fixed :
          Set.EqOn π₁ (fun x ↦ hpwl.slope jLast * x - hpwl.slope jLast) (Set.Icc (1 - ε) 1) := by
        intro x hx
        have hbase := hπ₁_last ⟨le_trans haLast_le hx.1, hx.2⟩
        simpa [hsigma₁Right] using hbase
      have hπ₂_anchor_fixed :
          Set.EqOn π₂ (fun x ↦ hpwl.slope jLast * x - hpwl.slope jLast) (Set.Icc (1 - ε) 1) := by
        intro x hx
        have hbase := hπ₂_last ⟨le_trans haLast_le hx.1, hx.2⟩
        simpa [hsigma₂Right] using hbase
      have htarget :
          Set.EqOn π (fun x ↦ hpwl.slope jLast * x + hpwl.intercept ownerCell) (Set.Icc a b) := by
        simpa [ownerCell, hownerLast] using hrawCell
      rcases midpointComponentsAffineOnRightSlopeFamily
          hπ hπ₁ hπ₂ hmid hπ_periodic hπ₁_periodic hπ₂_periodic hπ₁_bdd hπ₂_bdd
          hε_pos hε_lt htarget hπ_anchor hπ₁_anchor_fixed hπ₂_anchor_fixed with
        ⟨d₁, d₂, hπ₁_cell_raw, hπ₂_cell_raw⟩
      have hπ₁_cell :
          Set.EqOn π₁ (fun x ↦ hpwl.slope ownerCell * x + d₁) (Set.Icc a b) := by
        simpa [ownerCell, hownerLast] using hπ₁_cell_raw
      have hπ₂_cell :
          Set.EqOn π₂ (fun x ↦ hpwl.slope ownerCell * x + d₂) (Set.Icc a b) := by
        simpa [ownerCell, hownerLast] using hπ₂_cell_raw
      refine ⟨?_, ?_⟩
      · -- The breakpoint value already matches, so the common right-family slope glues the cell.
        exact eqOn_of_sharedAffineSlope_and_pointValue ha_mem hrawCell hπ₁_cell hanchor₁
      · -- Apply the same shared-slope argument to the second midpoint component.
        exact eqOn_of_sharedAffineSlope_and_pointValue ha_mem hrawCell hπ₂_cell hanchor₂
  constructor
  · intro x hx
    rcases point_mem_some_augmentedCell hf₀ hf₁ hpwl hx with ⟨i, hx_cell⟩
    exact (hcellAgreement i).1 hx_cell
  · intro x hx
    rcases point_mem_some_augmentedCell hf₀ hf₁ hpwl hx with ⟨i, hx_cell⟩
    exact (hcellAgreement i).2 hx_cell

/-- Theorem 6.27 (Two-Slope Theorem). Let `π : ℝ → ℝ` be a minimal valid function for the
one-dimensional pure integer infinite relaxation with `0 < f < 1`. If the restriction of `π` to
`[0, 1]` is a continuous piecewise-linear function with only two slopes, then `π` is extreme. -/
theorem two_slope_minimal_valid_function_on_R_is_extreme
    {f : ℝ} (hf₀ : 0 < f) (hf₁ : f < 1) {π : ℝ → ℝ}
    (hπ : pure_integer_minimal_valid_function_on_R f π)
    (hpiece : ContinuousTwoSlopePiecewiseLinearOnUnitInterval π) :
    pure_integer_extreme_valid_function_on_R f π := by
  refine
    { nonneg := hπ.nonneg
      one_le_sum := hπ.one_le_sum
      eq_of_eq_midpoint := ?_ }
  intro π₁Vec π₂Vec hπ₁Vec hπ₂Vec hmidVec
  let π₁ : ℝ → ℝ := fun r ↦ π₁Vec (fun _ : Fin 1 ↦ r)
  let π₂ : ℝ → ℝ := fun r ↦ π₂Vec (fun _ : Fin 1 ↦ r)
  have hπ₁_vec_eq : π₁Vec = fun r : Fin 1 → ℝ ↦ π₁ (r 0) := by
    -- In dimension `1`, every vector is determined by its `0`-th coordinate.
    ext r
    change π₁Vec r = π₁Vec (fun _ : Fin 1 ↦ r 0)
    have hr : r = fun _ : Fin 1 ↦ r 0 := by
      ext i
      fin_cases i
      rfl
    rw [hr]
  have hπ₂_vec_eq : π₂Vec = fun r : Fin 1 → ℝ ↦ π₂ (r 0) := by
    -- The same scalarization identity applies to the second midpoint component.
    ext r
    change π₂Vec r = π₂Vec (fun _ : Fin 1 ↦ r 0)
    have hr : r = fun _ : Fin 1 ↦ r 0 := by
      ext i
      fin_cases i
      rfl
    rw [hr]
  have hπ₁ : pure_integer_valid_function_on_R f π₁ := by
    -- Rewrite the canonical valid-function owner along the scalarization identity.
    change pure_integer_valid_function (fun _ : Fin 1 ↦ f) (fun r : Fin 1 → ℝ ↦ π₁ (r 0))
    simpa [hπ₁_vec_eq] using hπ₁Vec
  have hπ₂ : pure_integer_valid_function_on_R f π₂ := by
    -- Apply the same bridge to the right midpoint component.
    change pure_integer_valid_function (fun _ : Fin 1 ↦ f) (fun r : Fin 1 → ℝ ↦ π₂ (r 0))
    simpa [hπ₂_vec_eq] using hπ₂Vec
  have hmid : π = (1 / 2 : ℝ) • π₁ + (1 / 2 : ℝ) • π₂ := by
    -- Evaluate the canonical midpoint identity on constant `Fin 1` vectors.
    ext r
    have hpoint := congrFun hmidVec (fun _ : Fin 1 ↦ r)
    simpa [π₁, π₂, Pi.add_apply, Pi.smul_apply] using hpoint
  have hcomponentsEq :=
    midpointComponents_eqOn_unitInterval_of_twoSlope hf₀ hf₁ hπ hpiece hπ₁ hπ₂ hmid
  rcases midpointComponentsAreMinimalValidFunctionOnR hπ hπ₁ hπ₂ hmid with ⟨hπ₁_min, hπ₂_min⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ with
    ⟨hπ_periodic, _, _, _, _⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₁_min with
    ⟨hπ₁_periodic, _, _, _, _⟩
  rcases pureIntegerMinimalValidFunctionOnR_periodicEndpoints hπ₂_min with
    ⟨hπ₂_periodic, _, _, _, _⟩
  rcases hcomponentsEq with ⟨hEq₁_unit, hEq₂_unit⟩
  have hEq₁ : π = π₁ := eq_of_eqOn_unitInterval_of_onePeriodic hπ_periodic hπ₁_periodic hEq₁_unit
  have hEq₂ : π = π₂ := eq_of_eqOn_unitInterval_of_onePeriodic hπ_periodic hπ₂_periodic hEq₂_unit
  constructor
  · ext r
    simpa [hπ₁_vec_eq] using congrFun hEq₁ (r 0)
  · ext r
    simpa [hπ₂_vec_eq] using congrFun hEq₂ (r 0)

/-- Under the source hypotheses of Theorem 6.27, a two-slope minimal valid function on `ℝ` is
available through typeclass inference as an extreme valid function. -/
instance instTwoSlopeMinimalValidFunctionOnRIsExtreme
    {f : ℝ} [Fact (0 < f)] [Fact (f < 1)] {π : ℝ → ℝ}
    [pure_integer_minimal_valid_function_on_R f π]
    [Fact (ContinuousTwoSlopePiecewiseLinearOnUnitInterval π)] :
    pure_integer_extreme_valid_function_on_R f π :=
  two_slope_minimal_valid_function_on_R_is_extreme
    ‹Fact (0 < f)›.out
    ‹Fact (f < 1)›.out
    inferInstance
    ‹Fact (ContinuousTwoSlopePiecewiseLinearOnUnitInterval π)›.out

end Theorem627

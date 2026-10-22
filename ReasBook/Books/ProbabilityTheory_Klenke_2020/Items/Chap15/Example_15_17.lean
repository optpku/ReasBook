/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Example_15_16

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

attribute [local instance] Classical.propDecidable

/- Reuse the odd-square atomic law from Example 15.16 via its owner `PMF` presentation. -/
local notation "μodd" => oddSquarePMF.toMeasure.map fun x : ℤ ↦ (x : ℝ)

/-- The measure `ν = 1/2 δ_0 + 1/2 (x ↦ 2x)_* μ`, equivalently
`ν (A) = 1/2 * δ_0(A) + 1/2 * μ (A / 2)`, that appears in the tent-function characteristic
function example. -/
noncomputable def halfDiracPlusDoubleMapMeasure (μ : Measure ℝ) : Measure ℝ :=
  (1 / 2 : ENNReal) • Measure.dirac 0 + (1 / 2 : ENNReal) • μ.map (fun x ↦ (2 : ℝ) * x)

/-- The predicate that a real number is an odd integer. -/
def IsOddIntegerReal (x : ℝ) : Prop :=
  ∃ k : ℤ, Odd k ∧ x = k

/-- Helper for Example 15.17: the Fourier kernel `x ↦ exp (t * x * I)` is integrable against any
finite real measure. -/
private theorem integrableFourierKernel (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    Integrable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I)) μ := by
  -- Proof comment: the kernel has constant norm `1`, so boundedness over a finite measure gives
  -- integrability.
  refine Integrable.of_bound (by fun_prop) 1 ?_
  filter_upwards with x
  have hnorm : ‖Complex.exp (t * x * Complex.I)‖ = 1 := by
    simpa [mul_assoc] using Complex.norm_exp_ofReal_mul_I (t * x)
  exact le_of_eq hnorm

/-- Helper for Example 15.17: oddness of an integer cast to `ℝ` is exactly oddness of the original
integer. -/
private theorem isOddIntegerReal_intCast_iff (k : ℤ) :
    IsOddIntegerReal (k : ℝ) ↔ Odd k := by
  constructor
  · rintro ⟨m, hmOdd, hm⟩
    have hmk : m = k := Int.cast_injective <| by simpa using hm.symm
    simpa [hmk] using hmOdd
  · intro hkOdd
    exact ⟨k, hkOdd, rfl⟩

/-- Helper for Example 15.17: the singleton `{(k : ℝ)}` pulls back through the cast `ℤ → ℝ` to
the singleton `{k}`. -/
private theorem intCast_preimage_singleton (k : ℤ) :
    (fun z : ℤ ↦ (z : ℝ)) ⁻¹' ({(k : ℝ)} : Set ℝ) = {k} := by
  -- Proof comment: integer casts into `ℝ` are injective, so only the original integer lands in
  -- the target singleton.
  ext z
  simp [Int.cast_injective.eq_iff]

/-- Helper for Example 15.17: the odd-square law on `ℤ` induces the expected singleton masses on
`ℝ` after pushing forward by the integer cast. -/
private theorem oddSquareMapMeasure_real_singleton_eq (y : ℝ) :
    (μodd).real ({y} : Set ℝ) = if IsOddIntegerReal y then 4 / (Real.pi ^ 2 * y ^ 2) else 0 := by
  by_cases hyInt : ∃ k : ℤ, y = k
  · rcases hyInt with ⟨k, rfl⟩
    -- Proof comment: on integer atoms we pull the singleton back to `ℤ` and read off the PMF
    -- mass from `oddSquarePMF_apply`.
    rw [Measure.real_def]
    rw [Measure.map_apply (measurable_of_countable ((↑) : ℤ → ℝ)) (measurableSet_singleton (k : ℝ))]
    rw [intCast_preimage_singleton]
    rw [oddSquarePMF.toMeasure_apply_singleton k (measurableSet_singleton k), oddSquarePMF_apply]
    have hnonneg : 0 ≤ if Odd k then 4 / (Real.pi ^ 2 * (k : ℝ) ^ 2) else 0 := by
      by_cases hkOdd : Odd k
      · rw [if_pos hkOdd]
        positivity
      · rw [if_neg hkOdd]
    rw [ENNReal.toReal_ofReal hnonneg]
    simp [isOddIntegerReal_intCast_iff]
  · -- Proof comment: if `y` is not an integer, its singleton has empty preimage under the cast
    -- map, so the pushed-forward measure assigns it mass `0`.
    have hpreimage :
        (fun z : ℤ ↦ (z : ℝ)) ⁻¹' ({y} : Set ℝ) = (∅ : Set ℤ) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false]
      constructor
      · intro hz
        exact (hyInt ⟨z, hz.symm⟩).elim
      · intro hz
        exact hz.elim
    rw [Measure.real_def]
    rw [Measure.map_apply (measurable_of_countable ((↑) : ℤ → ℝ)) (measurableSet_singleton y)]
    rw [hpreimage]
    have hnotOdd : ¬ IsOddIntegerReal y := by
      rintro ⟨k, _, hk⟩
      exact hyInt ⟨k, hk⟩
    simp [hnotOdd]

/-- Helper for Example 15.17: the singleton `{x}` pulls back through the doubling map to
`{x / 2}`. -/
private theorem double_preimage_singleton (x : ℝ) :
    (fun y : ℝ ↦ (2 : ℝ) * y) ⁻¹' ({x} : Set ℝ) = {x / 2} := by
  -- Proof comment: solving `2 * y = x` over `ℝ` gives the unique solution `y = x / 2`.
  ext y
  simp [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0), mul_comm]

/-- Helper for Example 15.17: after doubling, the odd-square singleton masses are read at `x / 2`.
-/
private theorem doubleMapOddSquare_real_singleton_eq (x : ℝ) :
    ((μodd).map (fun y ↦ (2 : ℝ) * y)).real ({x} : Set ℝ) =
      if IsOddIntegerReal (x / 2) then 4 / (Real.pi ^ 2 * (x / 2) ^ 2) else 0 := by
  -- Proof comment: rewrite the doubled singleton as the preimage singleton `{x / 2}` and reuse
  -- the already computed masses for `μodd`.
  rw [Measure.real_def]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton x), double_preimage_singleton]
  simpa [Measure.real_def] using oddSquareMapMeasure_real_singleton_eq (x / 2)

-- Proof sketch: expand `halfDiracPlusDoubleMapMeasure`, use linearity of the integral defining
-- `MeasureTheory.charFun`, rewrite the Dirac term with `MeasureTheory.charFun_dirac`, and rewrite
-- the pushforward term with `MeasureTheory.charFun_map_mul`.
/-- The characteristic function of `halfDiracPlusDoubleMapMeasure μ` is
`t ↦ 1 / 2 + (1 / 2) * φ_μ(2 t)`. -/
theorem charFun_halfDiracPlusDoubleMapMeasure_eq (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    charFun (halfDiracPlusDoubleMapMeasure μ) t =
      (1 / 2 : ℂ) + (1 / 2 : ℂ) * charFun μ ((2 : ℝ) * t) := by
  -- Proof comment: expand the defining convex combination and use linearity of the integral
  -- defining `charFun`.
  have hDirac :
      Integrable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I))
        ((1 / 2 : ENNReal) • Measure.dirac 0) := by
    exact (integrableFourierKernel (Measure.dirac 0) t).smul_measure (by simp)
  have hMap :
      Integrable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I))
        ((1 / 2 : ENNReal) • μ.map (fun x ↦ (2 : ℝ) * x)) := by
    exact (integrableFourierKernel (μ.map (fun x ↦ (2 : ℝ) * x)) t).smul_measure (by simp)
  rw [halfDiracPlusDoubleMapMeasure, MeasureTheory.charFun_apply_real]
  rw [integral_add_measure hDirac hMap, integral_smul_measure, integral_smul_measure]
  rw [← MeasureTheory.charFun_apply_real (μ := Measure.dirac 0) t]
  rw [← MeasureTheory.charFun_apply_real (μ := μ.map (fun x ↦ (2 : ℝ) * x)) t]
  rw [MeasureTheory.charFun_dirac, MeasureTheory.charFun_map_mul]
  simp
  change ((2 : ℝ)⁻¹) • (1 : ℂ) + ((2 : ℝ)⁻¹) • charFun μ ((2 : ℝ) * t) =
    ((2 : ℂ)⁻¹) + ((2 : ℂ)⁻¹) * charFun μ ((2 : ℝ) * t)
  have hfinal :
      ((2 : ℝ)⁻¹) • (1 : ℂ) + ((2 : ℝ)⁻¹) • charFun μ ((2 : ℝ) * t) =
        ((2 : ℂ)⁻¹) + ((2 : ℂ)⁻¹) * charFun μ ((2 : ℝ) * t) := by
    simp [Algebra.smul_def]
  exact hfinal

-- Proof sketch: evaluate `halfDiracPlusDoubleMapMeasure μodd` on the singleton `{x}`, use
-- `Measure.map_apply` for the doubling map and the odd-square singleton formula coming from
-- `μodd`, then split into the cases `x = 0`,
-- `x / 2` odd, and the remaining case.
/-- Example 15.17: for `μ = μodd`, the measure
`ν = 1/2 δ_0 + 1/2 (x ↦ 2x)_* μ` satisfies `ν({0}) = 1/2`, `ν({x}) = 8 / (π^2 x^2)` when
`x / 2` is an odd integer, and `ν({x}) = 0` otherwise. -/
theorem halfDiracPlusDoubleMapMeasure_real_singleton_eq (x : ℝ) :
    (halfDiracPlusDoubleMapMeasure μodd).real ({x} : Set ℝ) =
      if x = 0 then
        1 / 2
      else if IsOddIntegerReal (x / 2) then
        8 / (Real.pi ^ 2 * x ^ 2)
      else
        0 := by
  -- Proof comment: expand the measure on the singleton `{x}`, then evaluate the doubled
  -- pushforward mass using the transport lemma above.
  rw [halfDiracPlusDoubleMapMeasure]
  have hsmulDirac : (((1 / 2 : ENNReal) • Measure.dirac 0) ({x} : Set ℝ)) ≠ ⊤ := by
    simpa [Measure.smul_apply] using
      ENNReal.mul_ne_top (by simp : (1 / 2 : ENNReal) ≠ ⊤)
        (measure_ne_top (Measure.dirac 0) ({x} : Set ℝ))
  have hsmulMap : (((1 / 2 : ENNReal) • (μodd).map (fun y ↦ (2 : ℝ) * y)) ({x} : Set ℝ)) ≠ ⊤ := by
    simpa [Measure.smul_apply] using
      ENNReal.mul_ne_top (by simp : (1 / 2 : ENNReal) ≠ ⊤)
        (measure_ne_top ((μodd).map (fun y ↦ (2 : ℝ) * y)) ({x} : Set ℝ))
  have hAdd :
      (((1 / 2 : ENNReal) • Measure.dirac 0 +
          (1 / 2 : ENNReal) • (μodd).map (fun y ↦ (2 : ℝ) * y)).real ({x} : Set ℝ)) =
        (((1 / 2 : ENNReal) • Measure.dirac 0).real ({x} : Set ℝ)) +
          (((1 / 2 : ENNReal) • (μodd).map (fun y ↦ (2 : ℝ) * y)).real ({x} : Set ℝ)) :=
    MeasureTheory.measureReal_add_apply (μ₁ := ((1 / 2 : ENNReal) • Measure.dirac 0))
      (μ₂ := ((1 / 2 : ENNReal) • (μodd).map (fun y ↦ (2 : ℝ) * y))) (s := ({x} : Set ℝ))
      hsmulDirac hsmulMap
  rw [hAdd, MeasureTheory.measureReal_ennreal_smul_apply,
    MeasureTheory.measureReal_ennreal_smul_apply]
  rw [doubleMapOddSquare_real_singleton_eq]
  by_cases hx : x = 0
  · -- Proof comment: the Dirac part contributes all of the mass at `0`, and the doubled
    -- odd-square law contributes none because `0` is not an odd integer.
    subst x
    simp [Measure.real_def, IsOddIntegerReal]
  · -- Proof comment: away from `0`, the Dirac contribution vanishes, so only the doubled odd
    -- atom remains.
    rw [if_neg hx]
    have hDiracZero : (Measure.dirac 0 : Measure ℝ).real ({x} : Set ℝ) = 0 := by
      simp [Measure.real_def, hx]
    rw [hDiracZero, mul_zero, zero_add]
    by_cases hOdd : IsOddIntegerReal (x / 2)
    · rw [if_pos hOdd, if_pos hOdd]
      have hx2 : x / 2 ≠ 0 := by
        exact div_ne_zero hx (by norm_num)
      -- Proof comment: simplify the rescaled denominator `(x / 2)^2` to recover the textbook
      -- coefficient `8 / (π^2 x^2)`.
      field_simp [hx, hx2, Real.pi_ne_zero]
      norm_num
    · rw [if_neg hOdd, if_neg hOdd]
      simp

/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

public section

noncomputable section

open scoped BigOperators ENNReal ProbabilityTheory unitInterval

namespace FairCoin

/-- The real number `1 / 2` lies in the unit interval. -/
theorem half_mem_unitInterval : (1 / 2 : ℝ) ∈ I := by
  change (1 / 2 : ℝ) ∈ Set.Icc 0 1
  constructor <;> norm_num

/-- The fair-coin success probability `1 / 2` as an element of the unit interval. -/
def fairProb : I :=
  ⟨(1 / 2 : ℝ), half_mem_unitInterval⟩

/-- The total mass of the fair-coin outcome law on `Bool` is `1`. -/
theorem pmf_sum_eq_one :
    (∑ _ : Bool, (1 / 2 : ℝ≥0∞)) = 1 := by
  rw [Fintype.sum_bool, ← two_mul]
  simpa [one_div] using ENNReal.mul_inv_cancel (show (2 : ℝ≥0∞) ≠ 0 by norm_num)
    (show (2 : ℝ≥0∞) ≠ ∞ by norm_num)

/-- The fair-coin outcome law on `Bool`, with `false = tails` and `true = heads`. -/
@[expose]
def pmf : PMF Bool :=
  PMF.ofFintype
    (fun _ ↦ (1 / 2 : ℝ≥0∞))
    pmf_sum_eq_one

/-- The `0/1` value map on fair-coin outcomes, with `false = tails` and `true = heads`. -/
@[expose]
def value : Bool → ℝ
  | false => 0
  | true => 1

/-- Each fair-coin outcome has probability `1 / 2`. -/
@[simp] theorem pmf_apply (b : Bool) :
    pmf b = (1 / 2 : ℝ≥0∞) := by
  cases b <;> rfl

/-- The fair-coin `0/1` value at `false` is `0`. -/
@[simp] theorem value_false :
    value false = 0 := rfl

/-- The fair-coin `0/1` value at `true` is `1`. -/
@[simp] theorem value_true :
    value true = 1 := rfl

/-- The induced `PMF ℝ` of the fair-coin `0/1` random variable. -/
@[expose]
def valuePmf : PMF ℝ :=
  PMF.map value pmf

/-- The fair-coin `0/1` random variable takes the value `0` with probability `1 / 2`. -/
@[simp] theorem valuePmf_zero :
    valuePmf 0 = (1 / 2 : ℝ≥0∞) := by
  simp [valuePmf, PMF.map_apply]

/-- The fair-coin `0/1` random variable takes the value `1` with probability `1 / 2`. -/
@[simp] theorem valuePmf_one :
    valuePmf 1 = (1 / 2 : ℝ≥0∞) := by
  simp [valuePmf, PMF.map_apply]

/-- Away from `0` and `1`, the fair-coin `0/1` random variable has zero mass. -/
theorem valuePmf_eq_zero_of_ne_zero_ne_one {x : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    valuePmf x = 0 := by
  simp [valuePmf, PMF.map_apply, hx0, hx1]

/-- The map `value` has law `valuePmf.toMeasure` under the fair-coin outcome law `pmf.toMeasure`.
-/
theorem hasLaw_value :
    ProbabilityTheory.HasLaw value valuePmf.toMeasure pmf.toMeasure where
  aemeasurable := (measurable_of_finite value).aemeasurable
  map_eq := by
    -- `valuePmf` is the pushforward of `pmf` along the measurable map `value`.
    simpa [valuePmf] using (PMF.toMeasure_map value pmf (measurable_of_finite value))

/-- The measure associated to `valuePmf` is the Bernoulli law `Ber(1, 0, fairProb)`. -/
theorem valuePmf_toMeasure_eq :
    valuePmf.toMeasure = Ber(1, 0, fairProb) := by
  have hpmf : pmf.toMeasure = Ber(true, false, fairProb) := by
    have hfair : (unitInterval.toNNReal fairProb : NNReal) = (1 / 2 : NNReal) := by
      ext
      change ((1 / 2 : ℝ)) = (1 / 2 : ℝ)
      rfl
    have hsymm : (unitInterval.toNNReal (σ fairProb) : NNReal) = (1 / 2 : NNReal) := by
      ext
      change ((1 - (1 / 2 : ℝ))) = (1 / 2 : ℝ)
      norm_num
    rw [PMF.toMeasure_eq_iff_eq_toPMF]
    ext b
    cases b
    · rw [MeasureTheory.Measure.toPMF_apply]
      simp [pmf_apply, hsymm]
    · rw [MeasureTheory.Measure.toPMF_apply]
      simp [pmf_apply, hfair]
  -- Push the Bernoulli law on `Bool` through the `0/1` value map.
  change (PMF.map value pmf).toMeasure = Ber(1, 0, fairProb)
  rw [← PMF.toMeasure_map value pmf (measurable_of_finite value)]
  rw [hpmf]
  simp [value]

end FairCoin

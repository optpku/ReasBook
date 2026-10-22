/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Gamma
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Exercise_24_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace ProbabilityTheory

/- Layering for Definition 24.26:
- `dirichletDistribution` on `dirichletSimplex n` is the source-facing owner for `n ≥ 2`.
- `dirichletDensity` together with `dirichletSimplexVolume` gives the textbook simplex-density
  presentation via the first `n - 1` simplex coordinates `dx₁ ... dx_{n-1}`.
- `dirichletNormalize` and `dirichletGammaProduct` form the normalized-Gamma bridge/view used by
  later chapter items. -/

/-- The simplex `Δ_n` underlying the Dirichlet law. This is the canonical mathlib simplex
`stdSimplex ℝ (Fin n)` under the chapter vocabulary. -/
abbrev dirichletSimplex (n : ℕ) : Type :=
  stdSimplex ℝ (Fin n)

/-- The standard simplex is measurable as a subset of `Fin n → ℝ`. -/
theorem measurableSet_dirichletSimplex (n : ℕ) : MeasurableSet (stdSimplex ℝ (Fin n)) :=
  (isClosed_stdSimplex ℝ (Fin n)).measurableSet

/-- The distinguished simplex vertex used when a normalization denominator vanishes. -/
def dirichletSimplexVertexFun (n : ℕ) (hn : 2 ≤ n) : Fin n → ℝ :=
  fun i ↦ if i = ⟨0, Nat.lt_of_lt_of_le (Nat.succ_pos 1) hn⟩ then 1 else 0

-- Proof sketch: exactly one coordinate of the distinguished vertex is `1` and all others are `0`,
-- so every coordinate is nonnegative and the total sum is `1`.
/-- The fallback vertex belongs to the simplex. -/
theorem dirichletSimplexVertexFun_property (n : ℕ) (hn : 2 ≤ n) :
    (∀ i, 0 ≤ dirichletSimplexVertexFun n hn i) ∧
      (∑ i, dirichletSimplexVertexFun n hn i = 1) := by
  -- Proof comment: this is exactly the standard simplex vertex with a single `1` entry.
  change dirichletSimplexVertexFun n hn ∈ stdSimplex ℝ (Fin n)
  have hEq :
      (fun x : Fin n ↦
        if (⟨0, Nat.lt_of_lt_of_le (Nat.succ_pos 1) hn⟩ : Fin n) = x then (1 : ℝ) else 0) =
      dirichletSimplexVertexFun n hn := by
    funext i
    simp [dirichletSimplexVertexFun, eq_comm]
  rw [← hEq]
  exact ite_eq_mem_stdSimplex (𝕜 := ℝ)
    (ι := Fin n) (⟨0, Nat.lt_of_lt_of_le (Nat.succ_pos 1) hn⟩ : Fin n)

/-- A canonical simplex vertex, used as the zero-denominator branch of the normalization map. -/
def dirichletSimplexVertex (n : ℕ) (hn : 2 ≤ n) : dirichletSimplex n :=
  ⟨dirichletSimplexVertexFun n hn, dirichletSimplexVertexFun_property n hn⟩

/-- The coordinate chart domain for `Δ_n`, using the first `n - 1` coordinates and recovering the
last one from the sum-to-one constraint. -/
def dirichletChart (n : ℕ) : Set (Fin (n - 1) → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

/-- Membership in the Dirichlet chart means nonnegative first coordinates with total sum at most
`1`. -/
theorem mem_dirichletChart {n : ℕ} {x : Fin (n - 1) → ℝ} :
    x ∈ dirichletChart n ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1 :=
  Iff.rfl

/-- Helper for Definition 24.26: the Dirichlet chart domain is measurable. -/
theorem measurableSet_dirichletChart (n : ℕ) :
    MeasurableSet (dirichletChart n) := by
  classical
  -- Proof comment: the chart is the intersection of coordinate half-spaces and one sum half-space.
  have hnonneg :
      MeasurableSet {x : Fin (n - 1) → ℝ | ∀ i, 0 ≤ x i} := by
    have hclosed :
        IsClosed (⋂ i : Fin (n - 1), {x : Fin (n - 1) → ℝ | 0 ≤ x i}) := by
      refine isClosed_iInter fun i ↦ ?_
      simpa using (isClosed_le continuous_const (continuous_apply i))
    simpa [Set.iInter_setOf] using hclosed.measurableSet
  have hsum :
      MeasurableSet {x : Fin (n - 1) → ℝ | ∑ i, x i ≤ (1 : ℝ)} := by
    have hcont : Continuous fun x : Fin (n - 1) → ℝ ↦ ∑ i, x i := by
      exact continuous_finset_sum _ fun i _ ↦ continuous_apply i
    simpa using (isClosed_le hcont continuous_const).measurableSet
  change MeasurableSet
    ({x : Fin (n - 1) → ℝ | ∀ i, 0 ≤ x i} ∩ {x : Fin (n - 1) → ℝ | ∑ i, x i ≤ 1})
  exact hnonneg.inter hsum

/-- Appending the recovered last coordinate gives the ambient vector in `ℝ^n`. -/
def dirichletCoordVector (n : ℕ) (_hn : 2 ≤ n) (x : Fin (n - 1) → ℝ) : Fin n → ℝ :=
  fun i ↦ if h : i.1 < n - 1 then x ⟨i.1, h⟩ else 1 - ∑ j, x j

-- Route correction: expose `dirichletCoordVector` through the canonical `Fin ((n - 1) + 1)`
-- decomposition, so `lastCases` and `sum_univ_castSucc` can be used without fragile transport.
/-- Helper for Definition 24.26: away from the last coordinate, the chart vector recovers the
given chart coordinates. -/
theorem dirichletCoordVector_castSucc {n : ℕ} (hn : 2 ≤ n) (x : Fin (n - 1) → ℝ)
    (i : Fin (n - 1)) :
    dirichletCoordVector n hn x (Fin.cast (by omega) i.castSucc) = x i := by
  -- Proof comment: after casting from `Fin ((n - 1) + 1)` to `Fin n`, the `castSucc` index still
  -- lands in the first `n - 1` coordinates, so the defining `if` uses the chart coordinate.
  simp [dirichletCoordVector]

/-- Helper for Definition 24.26: the last coordinate of the chart vector is recovered from the
sum-to-one constraint. -/
theorem dirichletCoordVector_last {n : ℕ} (hn : 2 ≤ n) (x : Fin (n - 1) → ℝ) :
    dirichletCoordVector n hn x (Fin.cast (by omega) (Fin.last (n - 1))) = 1 - ∑ i, x i := by
  -- Proof comment: the casted last index is exactly the recovered final coordinate, so the
  -- definition takes the second branch.
  simp [dirichletCoordVector]

-- Proof sketch: the chart hypothesis gives nonnegative first coordinates and `∑ i, x i ≤ 1`,
-- hence the recovered last coordinate is also nonnegative; summing the first `n - 1` coordinates
-- together with `1 - ∑ i, x i` gives `1`.
/-- Points in the chart domain determine points of the simplex `Δ_n`. -/
theorem dirichletCoordVector_property (n : ℕ) (hn : 2 ≤ n)
    {x : Fin (n - 1) → ℝ} (hx : x ∈ dirichletChart n) :
    (∀ i, 0 ≤ dirichletCoordVector n hn x i) ∧
      (∑ i, dirichletCoordVector n hn x i = 1) := by
  rcases hx with ⟨hx_nonneg, hx_sum_le⟩
  have hEq : (n - 1) + 1 = n := by
    omega
  constructor
  · -- Proof comment: the first `n - 1` coordinates stay nonnegative, and the last one is
    -- `1 - ∑ i, x i`, which is nonnegative by the chart inequality.
    have hnonnegCast :
        ∀ i : Fin ((n - 1) + 1), 0 ≤ dirichletCoordVector n hn x (Fin.cast hEq i) := by
      intro i
      cases i using Fin.lastCases with
      | last =>
          rw [dirichletCoordVector_last]
          linarith
      | cast j =>
          rw [dirichletCoordVector_castSucc]
          exact hx_nonneg j
    intro i
    simpa [hEq] using hnonnegCast (Fin.cast hEq.symm i)
  · -- Proof comment: sum the first `n - 1` coordinates and the recovered last coordinate.
    have hsumCast :
        ∑ i : Fin ((n - 1) + 1), dirichletCoordVector n hn x (Fin.cast hEq i) = 1 := by
      rw [Fin.sum_univ_castSucc, dirichletCoordVector_last]
      simp_rw [dirichletCoordVector_castSucc]
      ring
    have hsumReindex :
        ∑ i : Fin ((n - 1) + 1), dirichletCoordVector n hn x (Fin.cast hEq i) =
          ∑ i : Fin n, dirichletCoordVector n hn x i := by
      have hbij : Function.Bijective (Fin.cast hEq : Fin ((n - 1) + 1) → Fin n) := by
        refine ⟨?_, ?_⟩
        · intro i j hij
          exact Fin.ext <| by simpa using congrArg Fin.val hij
        · intro i
          refine ⟨Fin.cast hEq.symm i, ?_⟩
          simp
      exact Function.Bijective.sum_comp hbij (fun i : Fin n ↦ dirichletCoordVector n hn x i)
    exact hsumReindex.symm.trans hsumCast

/-- The chart map from the first `n - 1` coordinates to the simplex `Δ_n`. Outside the chart
domain, the value is irrelevant for the restricted measure and is fixed at the distinguished
vertex. -/
def dirichletCoordsToSimplex (n : ℕ) (hn : 2 ≤ n) (x : Fin (n - 1) → ℝ) :
    dirichletSimplex n := by
  classical
  exact if hx : x ∈ dirichletChart n then
    ⟨dirichletCoordVector n hn x, dirichletCoordVector_property n hn hx⟩
  else
    dirichletSimplexVertex n hn

/-- On the chart domain, `dirichletCoordsToSimplex` appends the recovered last coordinate. -/
theorem dirichletCoordsToSimplex_of_mem {n : ℕ} (hn : 2 ≤ n) {x : Fin (n - 1) → ℝ}
    (hx : x ∈ dirichletChart n) :
    dirichletCoordsToSimplex n hn x =
      ⟨dirichletCoordVector n hn x, dirichletCoordVector_property n hn hx⟩ := by
  classical
  rw [dirichletCoordsToSimplex]
  simp only [dif_pos hx]

/-- Helper for Definition 24.26: the chart map is almost everywhere measurable for restricted
Lebesgue measure on the chart domain. -/
theorem measurable_dirichletCoordVector {n : ℕ} (hn : 2 ≤ n) :
    Measurable (dirichletCoordVector n hn) := by
  -- Proof comment: each ambient coordinate is either an evaluation map or the recovered last
  -- coordinate `1 - ∑ i, x i`.
  classical
  have hsum_meas : Measurable fun x : Fin (n - 1) → ℝ ↦ ∑ j, x j := by
    exact Finset.measurable_sum Finset.univ fun j _ ↦ measurable_pi_apply j
  refine measurable_pi_lambda _ fun i ↦ ?_
  by_cases hi : i.1 < n - 1
  · rw [show (fun x : Fin (n - 1) → ℝ ↦ dirichletCoordVector n hn x i) =
        fun x : Fin (n - 1) → ℝ ↦ x (⟨i.1, hi⟩ : Fin (n - 1)) by
        funext x
        simp [dirichletCoordVector, hi]]
    exact measurable_pi_apply (⟨i.1, hi⟩ : Fin (n - 1))
  · rw [show (fun x : Fin (n - 1) → ℝ ↦ dirichletCoordVector n hn x i) =
        fun x : Fin (n - 1) → ℝ ↦ 1 - ∑ j, x j by
        funext x
        simp [dirichletCoordVector, hi]]
    exact measurable_const.sub hsum_meas

/-- Helper for Definition 24.26: on the chart subtype, the chart map is the measurable subtype
lift of the ambient coordinate vector. -/
theorem aemeasurable_dirichletCoordsToSimplex_restrict {n : ℕ} (hn : 2 ≤ n) :
    AEMeasurable (dirichletCoordsToSimplex n hn)
      (((volume : Measure (Fin (n - 1) → ℝ)).restrict (dirichletChart n))) := by
  let chartLift : {x // x ∈ dirichletChart n} → dirichletSimplex n :=
    fun x ↦ ⟨dirichletCoordVector n hn x.1, dirichletCoordVector_property n hn x.2⟩
  have hchartLift_meas : Measurable chartLift := by
    -- Proof comment: the subtype lift is measurable because the ambient chart vector already is.
    exact ((measurable_dirichletCoordVector hn).comp measurable_subtype_coe).subtype_mk
  have hchartLift_eq :
      (fun x : {x // x ∈ dirichletChart n} ↦ dirichletCoordsToSimplex n hn x.1) = chartLift := by
    -- Proof comment: inside the chart subtype, the `if`-branch in `dirichletCoordsToSimplex`
    -- is always the explicit chart embedding.
    funext x
    simpa [chartLift] using dirichletCoordsToSimplex_of_mem hn x.2
  refine aemeasurable_restrict_of_measurable_subtype (measurableSet_dirichletChart n) ?_
  rw [hchartLift_eq]
  exact hchartLift_meas

/-- Helper for Definition 24.26: the chart map is globally measurable as a simplex-valued
function. -/
theorem measurable_dirichletCoordsToSimplex {n : ℕ} (hn : 2 ≤ n) :
    Measurable (dirichletCoordsToSimplex n hn) := by
  classical
  let raw : (Fin (n - 1) → ℝ) → Fin n → ℝ :=
    fun x ↦ if hx : x ∈ dirichletChart n then dirichletCoordVector n hn x else dirichletSimplexVertexFun n hn
  have hraw_meas : Measurable raw := by
    -- Proof comment: on the chart domain we use the measurable coordinate vector, and outside it
    -- we fall back to the constant distinguished vertex.
    exact Measurable.ite (measurableSet_dirichletChart n)
      (measurable_dirichletCoordVector hn) measurable_const
  have hraw_mem : ∀ x, raw x ∈ stdSimplex ℝ (Fin n) := by
    intro x
    by_cases hx : x ∈ dirichletChart n
    · -- Proof comment: on the chart domain the raw map is the explicit simplex point.
      simpa [raw, hx, dirichletSimplex] using
        dirichletCoordVector_property n hn hx
    · -- Proof comment: off the chart domain the raw map is the fallback simplex vertex.
      simpa [raw, hx, dirichletSimplex] using
        dirichletSimplexVertexFun_property n hn
  have hEq :
      dirichletCoordsToSimplex n hn =
        fun x ↦ ((⟨raw x, hraw_mem x⟩ : dirichletSimplex n)) := by
    funext x
    by_cases hx : x ∈ dirichletChart n
    · ext i
      simp [dirichletCoordsToSimplex, raw, hx]
    · ext i
      simp [dirichletCoordsToSimplex, raw, hx, dirichletSimplexVertex]
  rw [hEq]
  exact hraw_meas.subtype_mk

/-- The simplex measure from Definition 24.26, obtained by integrating in the first `n - 1`
coordinates and transporting that measure to the simplex `Δ_n`. -/
noncomputable def dirichletSimplexVolume (n : ℕ) (hn : 2 ≤ n) : Measure (dirichletSimplex n) :=
  (((volume : Measure (Fin (n - 1) → ℝ)).restrict (dirichletChart n))).map
    (dirichletCoordsToSimplex n hn)

/-- Evaluating the simplex chart measure amounts to evaluating restricted Lebesgue measure on the
preimage under the coordinate chart map. -/
theorem dirichletSimplexVolume_apply {n : ℕ} (hn : 2 ≤ n) {A : Set (dirichletSimplex n)}
    (hA : MeasurableSet A) :
    dirichletSimplexVolume n hn A =
      ((volume : Measure (Fin (n - 1) → ℝ)).restrict (dirichletChart n))
        ((dirichletCoordsToSimplex n hn) ⁻¹' A) := by
  -- Proof comment: `dirichletSimplexVolume` is the pushforward of the restricted ambient volume.
  simpa [dirichletSimplexVolume] using
    Measure.map_apply_of_aemeasurable (aemeasurable_dirichletCoordsToSimplex_restrict hn) hA

/-- The positive-part sum used to normalize a vector into the simplex. -/
def dirichletPositivePartSum {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, max (x i) 0

/-- Helper for Definition 24.26: on coordinatewise nonnegative input, the positive-part sum is the
ordinary coordinate sum. -/
private theorem dirichletPositivePartSum_eq_sum_of_nonneg {n : ℕ} {x : Fin n → ℝ}
    (hx_nonneg : ∀ i, 0 ≤ x i) :
    dirichletPositivePartSum x = ∑ i, x i := by
  -- Proof comment: each positive part collapses to the original coordinate on the nonnegative
  -- region.
  simp [dirichletPositivePartSum, hx_nonneg]

/-- Helper for Definition 24.26: nonnegative coordinates with positive total mass have strictly
positive positive-part sum. -/
private theorem dirichletPositivePartSum_pos_of_nonneg {n : ℕ} {x : Fin n → ℝ}
    (hx_nonneg : ∀ i, 0 ≤ x i) (hs : 0 < ∑ i, x i) :
    0 < dirichletPositivePartSum x := by
  -- Proof comment: after rewriting the positive-part sum to the ordinary sum, the claim is the
  -- assumed positivity of that sum.
  rw [dirichletPositivePartSum_eq_sum_of_nonneg hx_nonneg]
  exact hs

/-- Coordinatewise positive-part normalization of a vector in `ℝ^n`. -/
def dirichletNormalizedCoords {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ max (x i) 0 / dirichletPositivePartSum x

-- Proof sketch: under a nonzero normalization denominator, each positive-part coordinate remains
-- nonnegative and the normalized coordinates sum to `1` by construction.
/-- Positive-part normalization lands in the simplex when the normalizing sum is nonzero. -/
theorem dirichletNormalizedCoords_property {n : ℕ} (x : Fin n → ℝ)
    (hs : dirichletPositivePartSum x ≠ 0) :
    (∀ i, 0 ≤ dirichletNormalizedCoords x i) ∧
      (∑ i, dirichletNormalizedCoords x i = 1) := by
  have hsum_nonneg : 0 ≤ dirichletPositivePartSum x := by
    exact Finset.sum_nonneg fun i _ ↦ le_max_right _ _
  constructor
  · -- Proof comment: each coordinate is a nonnegative positive part divided by a nonnegative sum.
    intro i
    exact div_nonneg (le_max_right _ _) hsum_nonneg
  · -- Proof comment: the total normalized mass is the positive-part sum divided by itself.
    calc
      ∑ i, dirichletNormalizedCoords x i
          = (∑ i, max (x i) 0) / dirichletPositivePartSum x := by
              simp [dirichletNormalizedCoords, Finset.sum_div]
      _ = dirichletPositivePartSum x / dirichletPositivePartSum x := by
            simp [dirichletPositivePartSum]
      _ = 1 := by
            exact div_self hs

/-- The normalization map from `ℝ^n` to the simplex `Δ_n`. -/
def dirichletNormalize (n : ℕ) (hn : 2 ≤ n) (x : Fin n → ℝ) : dirichletSimplex n :=
  if hs : dirichletPositivePartSum x = 0 then
    dirichletSimplexVertex n hn
  else
    ⟨dirichletNormalizedCoords x, dirichletNormalizedCoords_property x hs⟩

-- Proof sketch: measurability follows from the measurability of coordinatewise `max`, finite sums,
-- scalar division on the nonzero branch, and the piecewise definition at the zero branch.
/-- The normalization map to the simplex is measurable. -/
theorem measurable_dirichletNormalize (n : ℕ) (hn : 2 ≤ n) :
    Measurable (dirichletNormalize n hn) := by
  classical
  let normalizeFun : (Fin n → ℝ) → Fin n → ℝ :=
    fun x i ↦
      if hs : dirichletPositivePartSum x = 0 then dirichletSimplexVertexFun n hn i
      else dirichletNormalizedCoords x i
  have hsum_meas : Measurable (dirichletPositivePartSum (n := n)) := by
    -- Proof comment: the denominator is a finite sum of measurable coordinatewise maxima.
    simpa [dirichletPositivePartSum] using
      (Finset.measurable_sum Finset.univ
        (fun i _ ↦ (measurable_pi_apply i).max measurable_const))
  have hnormalize_meas : Measurable normalizeFun := by
    -- Proof comment: each coordinate is a measurable branch between the vertex and normalized map.
    refine measurable_pi_lambda _ fun i ↦ ?_
    have hcoord_meas : Measurable fun x : Fin n → ℝ ↦ dirichletNormalizedCoords x i := by
      simpa [dirichletNormalizedCoords] using
        (((measurable_pi_apply i).max measurable_const).div hsum_meas)
    exact Measurable.ite (hsum_meas (measurableSet_singleton (0 : ℝ))) measurable_const
      hcoord_meas
  have hnormalize_mem :
      ∀ x, normalizeFun x ∈ (stdSimplex ℝ (Fin n) : Set (Fin n → ℝ)) := by
    intro x
    by_cases hs : dirichletPositivePartSum x = 0
    · -- Proof comment: the zero-denominator branch is the distinguished simplex vertex.
      simpa [normalizeFun, hs, dirichletSimplex] using dirichletSimplexVertexFun_property n hn
    · -- Proof comment: the nonzero branch is the positive-part normalization.
      simpa [normalizeFun, hs, dirichletSimplex] using dirichletNormalizedCoords_property x hs
  have hmeas :
      Measurable fun x : Fin n → ℝ ↦
        ((⟨normalizeFun x, hnormalize_mem x⟩ : dirichletSimplex n)) := by
    exact hnormalize_meas.subtype_mk
  have hEq :
      dirichletNormalize n hn =
        fun x : Fin n → ℝ ↦
          ((⟨normalizeFun x, hnormalize_mem x⟩ : dirichletSimplex n)) := by
    funext x
    by_cases hs : dirichletPositivePartSum x = 0
    · ext i
      simp [dirichletNormalize, normalizeFun, hs, dirichletSimplexVertex]
    · ext i
      simp [dirichletNormalize, normalizeFun, hs]
  rw [hEq]
  exact hmeas

/-- Helper for Definition 24.26: on nonnegative input with positive total mass, the normalization
map is the usual division by the coordinate sum. -/
private theorem dirichletNormalize_apply_eq_div_sum_of_nonneg {n : ℕ} (hn : 2 ≤ n)
    {x : Fin n → ℝ} (hx_nonneg : ∀ i, 0 ≤ x i) (hs : 0 < ∑ j, x j) (i : Fin n) :
    dirichletNormalize n hn x i = x i / (∑ j, x j) := by
  have hsum_nonzero : dirichletPositivePartSum x ≠ 0 := by
    rw [dirichletPositivePartSum]
    simp [hx_nonneg, hs.ne']
  have hsum_eq : dirichletPositivePartSum x = ∑ j, x j := by
    rw [dirichletPositivePartSum]
    simp [hx_nonneg]
  -- Proof comment: on the Gamma-support region, the normalization takes the nonzero branch and the
  -- positive part of each coordinate is the coordinate itself.
  rw [dirichletNormalize, dif_neg hsum_nonzero]
  change dirichletNormalizedCoords x i = x i / (∑ j, x j)
  rw [dirichletNormalizedCoords, hsum_eq, max_eq_left (hx_nonneg i)]

/-- The Dirichlet density
`Γ(∑ᵢ θᵢ) / (∏ᵢ Γ(θᵢ)) * ∏ᵢ xᵢ^(θᵢ - 1)` on the simplex `Δ_n`. -/
noncomputable def dirichletDensity {n : ℕ} (θ : Fin n → ℝ) (x : dirichletSimplex n) : ℝ :=
  (Real.Gamma (∑ i, θ i) / ∏ i, Real.Gamma (θ i)) *
    ∏ i, Real.rpow (x i) (θ i - 1)

/-- Helper for Definition 24.26: the simplex density is measurable as an `ℝ≥0∞`-valued weight on
the simplex owner. -/
theorem measurable_dirichletDensity {n : ℕ} (θ : Fin n → ℝ) :
    Measurable (fun x : dirichletSimplex n ↦ ENNReal.ofReal (dirichletDensity θ x)) := by
  have hprod :
      Measurable (fun x : dirichletSimplex n ↦ ∏ i, (x i) ^ (θ i - 1)) := by
    -- Proof comment: each simplex coordinate is measurable, so the finite product of the
    -- coordinate powers is measurable as well.
    refine Finset.measurable_prod Finset.univ fun i _ ↦ ?_
    simpa [Real.rpow_eq_pow] using
      ((measurable_pi_apply i).comp measurable_subtype_coe).pow_const (θ i - 1)
  have hreal : Measurable (fun x : dirichletSimplex n ↦ dirichletDensity θ x) := by
    -- Proof comment: the Gamma-factor is constant, so measurability reduces to the product term.
    simpa [dirichletDensity, Real.rpow_eq_pow] using (measurable_const.mul hprod)
  exact ENNReal.continuous_ofReal.measurable.comp hreal

/-- Helper for Definition 24.26: pulling the simplex density back along the chart map stays
almost everywhere measurable on restricted Lebesgue measure. -/
theorem aemeasurable_dirichletDensity_comp_dirichletCoordsToSimplex_restrict {n : ℕ}
    (hn : 2 ≤ n) (θ : Fin n → ℝ) :
    AEMeasurable
      (fun x : Fin (n - 1) → ℝ ↦
        ENNReal.ofReal (dirichletDensity θ (dirichletCoordsToSimplex n hn x)))
      (((volume : Measure (Fin (n - 1) → ℝ)).restrict (dirichletChart n))) := by
  -- Proof comment: compose the owner-level density measurability with the existing restricted
  -- chart map.
  exact (measurable_dirichletDensity θ).comp_aemeasurable
    (aemeasurable_dirichletCoordsToSimplex_restrict hn)

/-- Helper for Definition 24.26: pushing the chart-side Dirichlet density through
`dirichletCoordsToSimplex` recovers the simplex-density measure. -/
private theorem map_dirichletCoordsToSimplex_chartWithDensity_eq_dirichletDensityMeasure
    {n : ℕ} (hn : 2 ≤ n) (θ : Fin n → ℝ) :
    Measure.map (dirichletCoordsToSimplex n hn)
      ((((volume : Measure (Fin (n - 1) → ℝ)).restrict (dirichletChart n)).withDensity
          (fun x ↦ ENNReal.ofReal (dirichletDensity θ (dirichletCoordsToSimplex n hn x))))) =
      (((dirichletSimplexVolume n hn).withDensity
          (fun x ↦ ENNReal.ofReal (dirichletDensity θ x))) :
        Measure (dirichletSimplex n)) := by
  let μ : Measure (Fin (n - 1) → ℝ) :=
    ((volume : Measure (Fin (n - 1) → ℝ)).restrict (dirichletChart n))
  let chart : (Fin (n - 1) → ℝ) → dirichletSimplex n := dirichletCoordsToSimplex n hn
  let F : dirichletSimplex n → ENNReal := fun x ↦ ENNReal.ofReal (dirichletDensity θ x)
  have hchart_aemeas_μ : AEMeasurable chart μ := by
    simpa [μ, chart] using aemeasurable_dirichletCoordsToSimplex_restrict (n := n) hn
  have hchart_aemeas_weighted :
      AEMeasurable chart (μ.withDensity fun x ↦ F (chart x)) := by
    -- Proof comment: absolute continuity of `withDensity` preserves the restricted chart
    -- measurability needed for the pushforward formula.
    exact hchart_aemeas_μ.mono_ac (withDensity_absolutelyContinuous _ _)
  ext A hA
  have hpreimage :
      NullMeasurableSet (chart ⁻¹' A) μ := hchart_aemeas_μ.nullMeasurableSet_preimage hA
  have hindicator :
      (fun x : Fin (n - 1) → ℝ ↦ A.indicator F (chart x)) =
        (chart ⁻¹' A).indicator (fun x ↦ F (chart x)) := by
    -- Proof comment: precomposing the simplex indicator by the chart map turns it into the
    -- ambient indicator of the chart preimage.
    funext x
    by_cases hx : chart x ∈ A <;> simp [F, hx]
  calc
    Measure.map chart (μ.withDensity fun x ↦ F (chart x)) A
        = (μ.withDensity fun x ↦ F (chart x)) (chart ⁻¹' A) := by
            simpa using Measure.map_apply_of_aemeasurable hchart_aemeas_weighted hA
    _ = ∫⁻ x in chart ⁻¹' A, F (chart x) ∂ μ := by
          rw [withDensity_apply' _ (chart ⁻¹' A)]
    _ = ((dirichletSimplexVolume n hn).withDensity F) A := by
          rw [withDensity_apply F hA]
          rw [show dirichletSimplexVolume n hn = Measure.map chart μ by rfl]
          rw [← lintegral_indicator hA]
          rw [lintegral_map' ((measurable_dirichletDensity θ).indicator hA).aemeasurable
            hchart_aemeas_μ]
          rw [hindicator]
          simpa [μ, F] using
            (MeasureTheory.lintegral_indicator₀ hpreimage
              (fun x : Fin (n - 1) → ℝ ↦ F (chart x))).symm

-- Semantic recall note: no reusable mathlib Dirichlet-law owner surfaced in semantic search, so
-- this file keeps the source-facing `ProbabilityMeasure (dirichletSimplex n)` API.
/-- Helper for Definition 24.26: the canonical product probability measure of the independent
Gamma coordinates with shapes `θ i` and unit rate. -/
private noncomputable abbrev dirichletGammaProductCore {n : ℕ} (θ : Fin n → ℝ)
    (hθ : ∀ i, 0 < θ i) : ProbabilityMeasure (Fin n → ℝ) :=
  ProbabilityMeasure.pi fun i ↦
    ⟨gammaMeasure (θ i) 1, isProbabilityMeasure_gammaMeasure (hθ i) zero_lt_one⟩

/-- Helper for Definition 24.26: under the independent Gamma-product source, every coordinate is
almost surely strictly positive. -/
private theorem ae_dirichletGammaProductCore_pos {n : ℕ} (θ : Fin n → ℝ)
    (hθ : ∀ i, 0 < θ i) :
    ∀ᵐ y ∂ (dirichletGammaProductCore θ hθ : Measure (Fin n → ℝ)), ∀ i, 0 < y i := by
  let μ : Measure (Fin n → ℝ) := (dirichletGammaProductCore θ hθ : Measure (Fin n → ℝ))
  letI : ∀ i : Fin n, IsProbabilityMeasure (gammaMeasure (θ i) 1) := fun i ↦
    isProbabilityMeasure_gammaMeasure (hθ i) zero_lt_one
  have hcoord_pos : ∀ i : Fin n, ∀ᵐ y ∂ μ, 0 < y i := by
    intro i
    have hEval :
        HasLaw (Function.eval i) (gammaMeasure (θ i) 1) μ := by
      -- Proof comment: each coordinate projection of the finite product source has the
      -- corresponding Gamma marginal.
      simpa [μ, dirichletGammaProductCore, ProbabilityMeasure.toMeasure_pi] using
        (measurePreserving_eval (fun j : Fin n ↦ gammaMeasure (θ j) 1) i).hasLaw
    exact (hEval.ae_iff (by fun_prop)).2 (ae_pos_gammaMeasure_unitRate (θ i) (hθ i))
  -- Proof comment: `Fin n` is finite, so the coordinatewise almost-sure positivity can be
  -- assembled into simultaneous positivity of all coordinates.
  exact ae_all_iff.2 hcoord_pos

/-- Helper for Definition 24.26: on the Gamma-product source, the positive-part sum agrees almost
everywhere with the ordinary coordinate sum. -/
private theorem dirichletPositivePartSum_ae_eq_sum {n : ℕ} (θ : Fin n → ℝ)
    (hθ : ∀ i, 0 < θ i) :
    (fun y : Fin n → ℝ ↦ dirichletPositivePartSum y) =ᵐ[
      (dirichletGammaProductCore θ hθ : Measure (Fin n → ℝ))] fun y ↦ ∑ i, y i := by
  -- Proof comment: the Gamma-product source is supported on the positive orthant, so each
  -- positive part collapses to the original coordinate.
  filter_upwards [ae_dirichletGammaProductCore_pos θ hθ] with y hy
  exact dirichletPositivePartSum_eq_sum_of_nonneg fun i ↦ le_of_lt (hy i)

/-- Helper for Definition 24.26: splitting off the last Gamma coordinate factors the finite
product source measure into prefix and last-coordinate laws. -/
private theorem map_dirichletGammaProductSplitLast_eq_prod {m : ℕ}
    (θ : Fin (m + 1) → ℝ) (hθ : ∀ i, 0 < θ i) :
    ((dirichletGammaProductCore θ hθ : Measure (Fin (m + 1) → ℝ)).map
      (fun x ↦ ((fun i : Fin m ↦ x i.castSucc), x (Fin.last m)))) =
      ((dirichletGammaProductCore (fun i : Fin m ↦ θ i.castSucc)
          (fun i ↦ hθ i.castSucc) : Measure (Fin m → ℝ)).prod
        (gammaMeasure (θ (Fin.last m)) 1)) := by
  let μ : Fin (m + 1) → Measure ℝ := fun i ↦ gammaMeasure (θ i) 1
  let splitLast : (Fin (m + 1) → ℝ) → (Fin m → ℝ) × ℝ :=
    fun x ↦ ((fun i : Fin m ↦ x i.castSucc), x (Fin.last m))
  letI : ∀ i, IsProbabilityMeasure (μ i) := fun i ↦ by
    dsimp [μ]
    exact isProbabilityMeasure_gammaMeasure (hθ i) zero_lt_one
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) (Fin.last m)
  have hMapEq :
      (Measure.pi μ).map e =
        (μ (Fin.last m)).prod (Measure.pi fun i : Fin m ↦ μ ((Fin.last m).succAbove i)) :=
    (measurePreserving_piFinSuccAbove μ (Fin.last m)).map_eq
  have hSplitLast : splitLast = Prod.swap ∘ e := by
    -- Proof comment: for `Fin.last`, `succAbove` is exactly `castSucc`, so the measurable
    -- equivalence exposes the prefix coordinates followed by the last coordinate.
    funext x
    ext i
    · simp [splitLast, Function.comp, e, Fin.init]
    · simp [splitLast, Function.comp, e]
  -- Proof comment: use the standard `piFinSuccAbove` factorization, then swap the product
  -- components to put the prefix block first.
  calc
    ((dirichletGammaProductCore θ hθ : Measure (Fin (m + 1) → ℝ)).map splitLast)
        = ((Measure.pi μ).map e).map Prod.swap := by
            rw [ProbabilityMeasure.toMeasure_pi, hSplitLast, Measure.map_map]
            · rfl
            · exact measurable_swap
            · exact e.measurable
    _ = ((μ (Fin.last m)).prod (Measure.pi fun i : Fin m ↦ μ ((Fin.last m).succAbove i))).map
          Prod.swap := by rw [hMapEq]
    _ = (Measure.pi fun i : Fin m ↦ μ ((Fin.last m).succAbove i)).prod (μ (Fin.last m)) := by
          rw [Measure.prod_swap]
    _ = ((dirichletGammaProductCore (fun i : Fin m ↦ θ i.castSucc)
          (fun i ↦ hθ i.castSucc) : Measure (Fin m → ℝ)).prod
        (gammaMeasure (θ (Fin.last m)) 1)) := by
          simp [μ, ProbabilityMeasure.toMeasure_pi, Fin.succAbove_last]

/-- Helper for Definition 24.26: reassemble a simplex point on the prefix coordinates with a last
coordinate share into a vector on `Fin (m + 2)`. -/
private def splitLastReassembledCoords {m : ℕ} (share : ℝ) (x : dirichletSimplex (m + 1)) :
    Fin (m + 2) → ℝ :=
  fun i ↦ Fin.lastCases (1 - share) (fun j : Fin (m + 1) ↦ share * x j) i

/-- Helper for Definition 24.26: if `share ∈ [0, 1]`, reassembling a simplex point on the prefix
coordinates with last-coordinate share `1 - share` still lands in the simplex. -/
private theorem splitLastReassembledCoords_property {m : ℕ}
    (x : dirichletSimplex (m + 1)) {share : ℝ} (hshare : 0 ≤ share ∧ share ≤ 1) :
    (∀ i, 0 ≤ splitLastReassembledCoords share x i) ∧
      (∑ i, splitLastReassembledCoords share x i = 1) := by
  rcases x.property with ⟨hx_nonneg, hx_sum⟩
  rcases hshare with ⟨hshare_nonneg, hshare_le_one⟩
  constructor
  · -- Proof comment: the prefix coordinates are scaled by the nonnegative share, and the last
    -- coordinate is `1 - share`.
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp [splitLastReassembledCoords, hshare_nonneg, mul_nonneg]
    · simp [splitLastReassembledCoords, sub_nonneg, hshare_le_one]
  · -- Proof comment: the prefix block contributes `share * ∑ j, x j = share`, and the final
    -- coordinate contributes `1 - share`.
    rw [Fin.sum_univ_castSucc]
    simp only [splitLastReassembledCoords, Fin.lastCases_castSucc, Fin.lastCases_last]
    rw [← Finset.mul_sum]
    have hx_sum' : ∑ i, x i = 1 := hx_sum
    rw [hx_sum']
    ring

/-- Helper for Definition 24.26: the split-last chart coordinates keep the first `m` prefix
coordinates scaled by `share` and recover the last prefix coordinate from the simplex constraint. -/
private def splitLastChartCoords {m : ℕ} (u : Fin m → ℝ) (share : ℝ) : Fin (m + 1) → ℝ :=
  fun i ↦ Fin.lastCases (share * (1 - ∑ j, u j)) (fun j : Fin m ↦ share * u j) i

/-- Helper for Definition 24.26: on the nonterminal prefix coordinates, `splitLastChartCoords`
is just coordinatewise scaling by `share`. -/
private theorem splitLastChartCoords_castSucc {m : ℕ} (u : Fin m → ℝ) (share : ℝ)
    (i : Fin m) :
    splitLastChartCoords (m := m) u share i.castSucc = share * u i := by
  -- Proof comment: the `castSucc` indices are exactly the prefix coordinates of the target
  -- chart, so the definition uses the scaled prefix branch.
  simp [splitLastChartCoords]

/-- Helper for Definition 24.26: the last target-chart coordinate is the scaled recovered prefix
mass `share * (1 - ∑ i, u i)`. -/
private theorem splitLastChartCoords_last {m : ℕ} (u : Fin m → ℝ) (share : ℝ) :
    splitLastChartCoords (m := m) u share (Fin.last m) = share * (1 - ∑ i, u i) := by
  -- Proof comment: the `lastCases` definition sends the terminal chart coordinate to the
  -- recovered prefix remainder.
  simp [splitLastChartCoords]

/-- Helper for Definition 24.26: the target-chart coordinates produced by `splitLastChartCoords`
sum to `share`. -/
private theorem sum_splitLastChartCoords {m : ℕ} (u : Fin m → ℝ) (share : ℝ) :
    ∑ i, splitLastChartCoords (m := m) u share i = share := by
  -- Proof comment: the scaled prefix sum and the scaled recovered remainder collapse back to the
  -- total share.
  rw [Fin.sum_univ_castSucc]
  simp_rw [splitLastChartCoords_castSucc, splitLastChartCoords_last]
  rw [← Finset.mul_sum]
  ring

/-- Helper for Definition 24.26: if `u` is in the prefix chart and `share ∈ [0, 1]`, then
`splitLastChartCoords u share` lies in the next Dirichlet chart. -/
private theorem splitLastChartCoords_mem_dirichletChart {m : ℕ} {u : Fin m → ℝ}
    {share : ℝ} (hu : u ∈ dirichletChart (m + 1)) (hshare : 0 ≤ share ∧ share ≤ 1) :
    splitLastChartCoords (m := m) u share ∈ dirichletChart (m + 2) := by
  rcases hu with ⟨hu_nonneg, hu_sum_le⟩
  rcases hshare with ⟨hshare_nonneg, hshare_le_one⟩
  constructor
  · -- Proof comment: every target-chart coordinate is a nonnegative factor `share` times a
    -- nonnegative prefix coordinate or the nonnegative recovered remainder.
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [splitLastChartCoords_castSucc]
      exact mul_nonneg hshare_nonneg (hu_nonneg j)
    · rw [splitLastChartCoords_last]
      have hrest_nonneg : 0 ≤ 1 - ∑ j, u j := by
        exact sub_nonneg.mpr hu_sum_le
      exact mul_nonneg hshare_nonneg hrest_nonneg
  · -- Proof comment: the chart sum is exactly `share`, so the target-chart inequality is the
    -- upper bound `share ≤ 1`.
    change ∑ i : Fin (m + 1), splitLastChartCoords (m := m) u share i ≤ 1
    rw [sum_splitLastChartCoords]
    exact hshare_le_one

/-- Helper for Definition 24.26: when the split-last share is nonzero, dividing a nonterminal
target-chart coordinate by the total target-chart sum recovers the original prefix coordinate. -/
private theorem splitLastChartCoords_div_sum_eq_prefix {m : ℕ} {u : Fin m → ℝ}
    {share : ℝ} (hshare : share ≠ 0) (i : Fin m) :
    splitLastChartCoords (m := m) u share i.castSucc /
        (∑ j, splitLastChartCoords (m := m) u share j) = u i := by
  -- Proof comment: the numerator is `share * u i`, while the denominator is the recovered share.
  rw [splitLastChartCoords_castSucc, sum_splitLastChartCoords]
  exact mul_div_cancel_left₀ (u i) hshare

/-- Helper for Definition 24.26: on the open strip
`dirichletChart (m + 1) × Set.Ioo 0 1`, the split-last chart map is injective. -/
private theorem splitLastChartMap_injOn_openStrip {m : ℕ} :
    Set.InjOn
      (fun p : (Fin m → ℝ) × ℝ ↦ splitLastChartCoords (m := m) p.1 p.2)
      {p : (Fin m → ℝ) × ℝ | p.1 ∈ dirichletChart (m + 1) ∧ p.2 ∈ Set.Ioo (0 : ℝ) 1} := by
  intro p hp q hq hpq
  have hshare :
      p.2 = q.2 := by
    -- Proof comment: summing the target-chart coordinates recovers the share parameter.
    calc
      p.2 = ∑ i, splitLastChartCoords (m := m) p.1 p.2 i := by
        symm
        exact sum_splitLastChartCoords p.1 p.2
      _ = ∑ i, splitLastChartCoords (m := m) q.1 q.2 i := by
        simpa using congrArg (fun v : Fin (m + 1) → ℝ ↦ ∑ i, v i) hpq
      _ = q.2 := sum_splitLastChartCoords q.1 q.2
  refine Prod.ext ?_ hshare
  funext i
  have hp2_pos : 0 < p.2 := hp.2.1
  have hcoord :
      p.2 * p.1 i = p.2 * q.1 i := by
    -- Proof comment: after identifying the shares, equality of target-chart coordinates reduces
    -- to equality of the scaled prefix coordinates.
    have hcoord' := congrArg (fun v : Fin (m + 1) → ℝ ↦ v i.castSucc) hpq
    simpa [splitLastChartCoords_castSucc, hshare] using hcoord'
  nlinarith

/-- Helper for Definition 24.26: on the positive strip
`dirichletChart (m + 1) × Set.Ioc 0 1`, the split-last chart map is injective. -/
private theorem splitLastChartMap_injOn_positiveStrip {m : ℕ} :
    Set.InjOn
      (fun p : (Fin m → ℝ) × ℝ ↦ splitLastChartCoords (m := m) p.1 p.2)
      {p : (Fin m → ℝ) × ℝ | p.1 ∈ dirichletChart (m + 1) ∧ p.2 ∈ Set.Ioc (0 : ℝ) 1} := by
  intro p hp q hq hpq
  have hshare :
      p.2 = q.2 := by
    -- Proof comment: summing the target-chart coordinates still recovers the share parameter on
    -- the positive strip, so equality of images forces equality of shares.
    calc
      p.2 = ∑ i, splitLastChartCoords (m := m) p.1 p.2 i := by
        symm
        exact sum_splitLastChartCoords p.1 p.2
      _ = ∑ i, splitLastChartCoords (m := m) q.1 q.2 i := by
        simpa using congrArg (fun v : Fin (m + 1) → ℝ ↦ ∑ i, v i) hpq
      _ = q.2 := sum_splitLastChartCoords q.1 q.2
  refine Prod.ext ?_ hshare
  funext i
  have hp2_pos : 0 < p.2 := hp.2.1
  have hcoord :
      p.2 * p.1 i = p.2 * q.1 i := by
    -- Proof comment: after identifying the share, equality of the `castSucc` coordinates reduces
    -- to equality of the scaled prefix coordinates.
    have hcoord' := congrArg (fun v : Fin (m + 1) → ℝ ↦ v i.castSucc) hpq
    simpa [splitLastChartCoords_castSucc, hshare] using hcoord'
  nlinarith

/-- Helper for Definition 24.26: every target-chart point with positive total mass comes from
split-last coordinates with share equal to that total mass. -/
private theorem exists_splitLastChartCoords_of_mem_dirichletChart_pos_sum {m : ℕ}
    {v : Fin (m + 1) → ℝ} (hv : v ∈ dirichletChart (m + 2)) (hs : 0 < ∑ i, v i) :
    ∃ u : Fin m → ℝ,
      u ∈ dirichletChart (m + 1) ∧
        splitLastChartCoords (m := m) u (∑ i, v i) = v := by
  rcases hv with ⟨hv_nonneg, hv_sum_le_one⟩
  let share : ℝ := ∑ i, v i
  let u : Fin m → ℝ := fun i ↦ v i.castSucc / share
  have hshare_pos : 0 < share := by
    simpa [share] using hs
  have hshare_ne : share ≠ 0 := hshare_pos.ne'
  have hu_mem : u ∈ dirichletChart (m + 1) := by
    constructor
    · -- Proof comment: dividing nonnegative target prefix coordinates by the positive total mass
      -- keeps every recovered prefix coordinate nonnegative.
      intro i
      exact div_nonneg (hv_nonneg i.castSucc) (le_of_lt hshare_pos)
    · -- Proof comment: the recovered prefix coordinates sum to the target prefix mass divided by
      -- the positive total mass, hence at most `1`.
      have hprefix_le : ∑ i : Fin m, v i.castSucc ≤ share := by
        have hsum_split :
            (∑ i : Fin m, v i.castSucc) + v (Fin.last m) = share := by
          simpa [share] using
            (Fin.sum_univ_castSucc (f := fun i : Fin (m + 1) ↦ v i)).symm
        linarith [hv_nonneg (Fin.last m)]
      have hsum_u :
          ∑ i : Fin m, u i = (∑ i : Fin m, v i.castSucc) / share := by
        dsimp [u]
        rw [Finset.sum_div]
      calc
        ∑ i : Fin m, u i = (∑ i : Fin m, v i.castSucc) / share := hsum_u
        _ ≤ 1 := (div_le_one hshare_pos).2 hprefix_le
  refine ⟨u, hu_mem, ?_⟩
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · -- Proof comment: on the nonterminal coordinates, the positive total mass cancels against the
    -- denominator used to recover the prefix chart point.
    rw [splitLastChartCoords_castSucc]
    dsimp [u, share]
    exact mul_div_cancel₀ _ hshare_ne
  · -- Proof comment: on the last coordinate, the recovered remainder is the total mass minus the
    -- recovered prefix block, which is exactly the original last coordinate.
    rw [splitLastChartCoords_last]
    have hsum_u :
        ∑ j : Fin m, u j = (∑ j : Fin m, v j.castSucc) / share := by
      dsimp [u]
      rw [Finset.sum_div]
    rw [hsum_u]
    have hsum_split :
        (∑ j : Fin m, v j.castSucc) + v (Fin.last m) = share := by
      simpa [share] using
        (Fin.sum_univ_castSucc (f := fun i : Fin (m + 1) ↦ v i)).symm
    calc
      share * (1 - (∑ j : Fin m, v j.castSucc) / share)
          = share - ∑ j : Fin m, v j.castSucc := by
              rw [mul_sub, mul_one, mul_div_cancel₀ _ hshare_ne]
      _ = v (Fin.last m) := by
            linarith

/-- Helper for Definition 24.26: the split-last chart map sends the positive strip exactly onto
the target chart points with positive total mass. -/
private theorem splitLastChartImage_positiveStrip {m : ℕ} :
    (fun p : (Fin m → ℝ) × ℝ ↦ splitLastChartCoords (m := m) p.1 p.2) ''
        {p : (Fin m → ℝ) × ℝ | p.1 ∈ dirichletChart (m + 1) ∧ p.2 ∈ Set.Ioc (0 : ℝ) 1} =
      {v : Fin (m + 1) → ℝ | v ∈ dirichletChart (m + 2) ∧ 0 < ∑ i, v i} := by
  ext v
  constructor
  · rintro ⟨p, hp, rfl⟩
    constructor
    · -- Proof comment: the positive-strip source already lands in the next chart by the
      -- previously established chart-membership lemma.
      exact splitLastChartCoords_mem_dirichletChart (m := m) hp.1 ⟨hp.2.1.le, hp.2.2⟩
    · -- Proof comment: the total target mass is exactly the split-last share, which is positive
      -- on the positive strip.
      rw [sum_splitLastChartCoords]
      exact hp.2.1
  · intro hv
    rcases hv with ⟨hv_chart, hv_sum_pos⟩
    rcases exists_splitLastChartCoords_of_mem_dirichletChart_pos_sum
      (m := m) hv_chart hv_sum_pos with ⟨u, hu_mem, hu_eq⟩
    refine ⟨(u, ∑ i, v i), ?_, ?_⟩
    · constructor
      · exact hu_mem
      · exact ⟨hv_sum_pos, hv_chart.2⟩
    · simpa using hu_eq

/-- Helper for Definition 24.26: the raw split-last owner assembly is a measurable ambient vector,
using the distinguished simplex vertex outside the admissible share range. -/
private def ownerSplitLastNormalizeAssemblyRaw {m : ℕ}
    (p : dirichletSimplex (m + 1) × ℝ) : Fin (m + 2) → ℝ :=
  if hshare : p.2 ∈ Set.Icc (0 : ℝ) 1 then
    splitLastReassembledCoords p.2 p.1
  else
    dirichletSimplexVertexFun (m + 2) (by omega)

/-- Helper for Definition 24.26: the raw split-last owner assembly always lands in the simplex,
either by the explicit reassembly on `[0, 1]` or by the fallback vertex. -/
private theorem ownerSplitLastNormalizeAssemblyRaw_property {m : ℕ}
    (p : dirichletSimplex (m + 1) × ℝ) :
    (∀ i, 0 ≤ ownerSplitLastNormalizeAssemblyRaw (m := m) p i) ∧
      (∑ i, ownerSplitLastNormalizeAssemblyRaw (m := m) p i = 1) := by
  by_cases hshare : p.2 ∈ Set.Icc (0 : ℝ) 1
  · -- Proof comment: on the admissible share range, the raw assembly is the split-last simplex
    -- reassembly.
    simpa [ownerSplitLastNormalizeAssemblyRaw, hshare] using
      splitLastReassembledCoords_property p.1 hshare
  · -- Proof comment: outside the admissible share range, the raw assembly is the distinguished
    -- simplex vertex.
    simpa [ownerSplitLastNormalizeAssemblyRaw, hshare] using
      dirichletSimplexVertexFun_property (m + 2) (by omega)

/-- Helper for Definition 24.26: the owner-valued split-last assembly packages the raw reassembly
map as a simplex point. -/
private def ownerSplitLastNormalizeAssembly {m : ℕ}
    (p : dirichletSimplex (m + 1) × ℝ) : dirichletSimplex (m + 2) :=
  ⟨ownerSplitLastNormalizeAssemblyRaw (m := m) p,
    ownerSplitLastNormalizeAssemblyRaw_property (m := m) p⟩

/-- Helper for Definition 24.26: the raw split-last owner assembly is measurable. -/
private theorem measurable_ownerSplitLastNormalizeAssemblyRaw {m : ℕ} :
    Measurable (ownerSplitLastNormalizeAssemblyRaw (m := m)) := by
  have hcond :
      MeasurableSet {p : dirichletSimplex (m + 1) × ℝ | p.2 ∈ Set.Icc (0 : ℝ) 1} :=
    measurable_snd measurableSet_Icc
  -- Proof comment: each coordinate is a measurable `if` between the explicit split-last
  -- reassembly and the constant fallback vertex.
  refine measurable_pi_lambda _ ?_
  intro i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · have hcoord :
        Measurable
          (fun p : dirichletSimplex (m + 1) × ℝ ↦
            splitLastReassembledCoords p.2 p.1 (Fin.castSucc j)) := by
        simpa [splitLastReassembledCoords] using
          measurable_snd.mul
            ((((measurable_pi_apply j).comp measurable_subtype_coe).comp measurable_fst))
    have hconst :
        Measurable
          (fun _ : dirichletSimplex (m + 1) × ℝ ↦
            dirichletSimplexVertexFun (m + 2) (by omega) (Fin.castSucc j)) := measurable_const
    have hEq :
        (fun c : dirichletSimplex (m + 1) × ℝ ↦
          ownerSplitLastNormalizeAssemblyRaw (m := m) c (Fin.castSucc j)) =
          (fun c : dirichletSimplex (m + 1) × ℝ ↦
            if c.2 ∈ Set.Icc (0 : ℝ) 1 then
              splitLastReassembledCoords c.2 c.1 (Fin.castSucc j)
            else
              dirichletSimplexVertexFun (m + 2) (by omega) (Fin.castSucc j)) := by
      funext c
      by_cases h : c.2 ∈ Set.Icc (0 : ℝ) 1 <;> simp [ownerSplitLastNormalizeAssemblyRaw, h]
    rw [hEq]
    exact Measurable.ite hcond hcoord hconst
  · have hcoord :
        Measurable
          (fun p : dirichletSimplex (m + 1) × ℝ ↦
            splitLastReassembledCoords p.2 p.1 (Fin.last (m + 1))) := by
        simpa [splitLastReassembledCoords] using measurable_const.sub measurable_snd
    have hconst :
        Measurable
          (fun _ : dirichletSimplex (m + 1) × ℝ ↦
            dirichletSimplexVertexFun (m + 2) (by omega) (Fin.last (m + 1))) := measurable_const
    have hEq :
        (fun c : dirichletSimplex (m + 1) × ℝ ↦
          ownerSplitLastNormalizeAssemblyRaw (m := m) c (Fin.last (m + 1))) =
          (fun c : dirichletSimplex (m + 1) × ℝ ↦
            if c.2 ∈ Set.Icc (0 : ℝ) 1 then
              splitLastReassembledCoords c.2 c.1 (Fin.last (m + 1))
            else
              dirichletSimplexVertexFun (m + 2) (by omega) (Fin.last (m + 1))) := by
      funext c
      by_cases h : c.2 ∈ Set.Icc (0 : ℝ) 1 <;> simp [ownerSplitLastNormalizeAssemblyRaw, h]
    rw [hEq]
    exact Measurable.ite hcond hcoord hconst

/-- Helper for Definition 24.26: the owner-valued split-last assembly is measurable. -/
private theorem measurable_ownerSplitLastNormalizeAssembly {m : ℕ} :
    Measurable (ownerSplitLastNormalizeAssembly (m := m)) := by
  -- Proof comment: measurability of the owner-valued map follows from the measurable ambient raw
  -- assembly together with its pointwise simplex-membership witness.
  exact (measurable_ownerSplitLastNormalizeAssemblyRaw (m := m)).subtype_mk

/-- Helper for Definition 24.26: on an admissible share, the owner-valued split-last assembly is
the explicit simplex point built from `splitLastReassembledCoords`. -/
private theorem ownerSplitLastNormalizeAssembly_of_mem {m : ℕ}
    {x : dirichletSimplex (m + 1)} {share : ℝ} (hshare : 0 ≤ share ∧ share ≤ 1) :
    ownerSplitLastNormalizeAssembly (m := m) (x, share) =
      ⟨splitLastReassembledCoords share x, splitLastReassembledCoords_property x hshare⟩ := by
  -- Proof comment: under the share constraint, the `if` in the raw assembly takes the explicit
  -- split-last branch.
  have hshare_mem : share ∈ Set.Icc (0 : ℝ) 1 := hshare
  ext i
  simp [ownerSplitLastNormalizeAssembly, ownerSplitLastNormalizeAssemblyRaw, hshare_mem]

/-- Helper for Definition 24.26: on admissible chart coordinates and `share ∈ [0, 1]`, the
owner-valued split-last assembly agrees with the target simplex chart map. -/
private theorem ownerSplitLastNormalizeAssembly_chartSpec {m : ℕ} (hm : 1 ≤ m)
    {u : Fin m → ℝ} (hu : u ∈ dirichletChart (m + 1)) {share : ℝ}
    (hshare : 0 ≤ share ∧ share ≤ 1) :
    ownerSplitLastNormalizeAssembly (m := m)
      (dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) u, share) =
        dirichletCoordsToSimplex (m + 2) (by omega) (splitLastChartCoords (m := m) u share) := by
  have hsplit :
      splitLastChartCoords (m := m) u share ∈ dirichletChart (m + 2) :=
    splitLastChartCoords_mem_dirichletChart (m := m) hu hshare
  -- Proof comment: both sides are explicit chart embeddings of the same ambient coordinate
  -- vector, so it suffices to compare coordinates after taking the admissible branches.
  rw [ownerSplitLastNormalizeAssembly_of_mem
    (m := m) (x := dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) u) hshare]
  rw [dirichletCoordsToSimplex_of_mem (n := m + 2) (hn := by omega) hsplit]
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · change
      splitLastReassembledCoords share
          (dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) u)
          (Fin.cast (by omega) j.castSucc) =
        dirichletCoordVector (m + 2) (by omega)
          (splitLastChartCoords (m := m) u share) (Fin.cast (by omega) j.castSucc)
    have htarget :
        dirichletCoordVector (m + 2) (by omega)
            (splitLastChartCoords (m := m) u share) (Fin.cast (by omega) j.castSucc) =
          splitLastChartCoords (m := m) u share j := by
      simpa using dirichletCoordVector_castSucc (n := m + 2) (hn := by omega)
        (x := splitLastChartCoords (m := m) u share) (i := j)
    rw [htarget]
    have hsplitCoord :
        splitLastReassembledCoords share
            (dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) u)
            (Fin.cast (by omega) j.castSucc) =
          share * (dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) u) j := by
      simpa [splitLastReassembledCoords]
    rw [hsplitCoord]
    rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
    · rw [dirichletCoordsToSimplex_of_mem (n := m + 1) (hn := Nat.succ_le_succ hm) hu]
      have hprefix :
          (⟨dirichletCoordVector (m + 1) (Nat.succ_le_succ hm) u,
              dirichletCoordVector_property (m + 1) (Nat.succ_le_succ hm) hu⟩ :
              dirichletSimplex (m + 1)) k.castSucc = u k := by
        simpa using dirichletCoordVector_castSucc (n := m + 1) (hn := Nat.succ_le_succ hm)
          (x := u) (i := k)
      rw [hprefix]
      rw [splitLastChartCoords_castSucc]
    · rw [dirichletCoordsToSimplex_of_mem (n := m + 1) (hn := Nat.succ_le_succ hm) hu]
      have hprefix :
          (⟨dirichletCoordVector (m + 1) (Nat.succ_le_succ hm) u,
              dirichletCoordVector_property (m + 1) (Nat.succ_le_succ hm) hu⟩ :
              dirichletSimplex (m + 1)) (Fin.last m) =
            1 - ∑ i, u i := by
        simpa using dirichletCoordVector_last (n := m + 1) (hn := Nat.succ_le_succ hm) (x := u)
      rw [hprefix]
      rw [splitLastChartCoords_last]
  · change
      splitLastReassembledCoords share
          (dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) u)
          (Fin.cast (by omega) (Fin.last (m + 1))) =
        dirichletCoordVector (m + 2) (by omega)
          (splitLastChartCoords (m := m) u share) (Fin.cast (by omega) (Fin.last (m + 1)))
    have htarget :
        dirichletCoordVector (m + 2) (by omega)
            (splitLastChartCoords (m := m) u share)
            (Fin.cast (by omega) (Fin.last (m + 1))) =
          1 - ∑ i, splitLastChartCoords (m := m) u share i := by
      simpa using dirichletCoordVector_last (n := m + 2) (hn := by omega)
        (x := splitLastChartCoords (m := m) u share)
    rw [htarget]
    have hlastCoord :
        splitLastReassembledCoords share
            (dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) u)
            (Fin.cast (by omega) (Fin.last (m + 1))) =
          1 - share := by
      simpa [splitLastReassembledCoords]
    rw [hlastCoord]
    rw [sum_splitLastChartCoords]

/-- Helper for Definition 24.26: on coordinatewise nonnegative input, the split-last reassembly of
the normalized prefix block, the Beta share, and the total mass recovers the simplex
normalization map together with the positive-part sum. -/
private theorem assembleDirichletNormalizeWithSum_splitLast {m : ℕ}
    (hm : 1 ≤ m) (y : Fin (m + 2) → ℝ) (hy_nonneg : ∀ i, 0 ≤ y i)
    (hprefix : 0 < ∑ i : Fin (m + 1), y i.castSucc)
    (hlast : 0 < y (Fin.last (m + 1))) :
    (splitLastReassembledCoords
        ((∑ k : Fin (m + 1), y k.castSucc) /
          ((∑ k : Fin (m + 1), y k.castSucc) + y (Fin.last (m + 1))))
        (dirichletNormalize (m + 1) (by omega) (fun k : Fin (m + 1) ↦ y k.castSucc)),
      (∑ i : Fin (m + 1), y i.castSucc) + y (Fin.last (m + 1))) =
      ((dirichletNormalize (m + 2) (by omega) y : Fin (m + 2) → ℝ), dirichletPositivePartSum y) := by
  -- Proof comment: rewrite the positive-part normalization to ordinary division by the total sum
  -- on the nonnegative region, then compare the reassembled coordinates one by one.
  have hprefix_nonneg : ∀ i : Fin (m + 1), 0 ≤ y i.castSucc := fun i ↦ hy_nonneg i.castSucc
  have hsum :
      ∑ j : Fin (m + 2), y j =
        (∑ i : Fin (m + 1), y i.castSucc) + y (Fin.last (m + 1)) := by
    simpa using (Fin.sum_univ_castSucc (f := fun i : Fin (m + 2) ↦ y i))
  have htotal_pos : 0 < ∑ j : Fin (m + 2), y j := by
    rw [hsum]
    exact add_pos hprefix hlast
  have hshare_den_ne :
      (∑ i : Fin (m + 1), y i.castSucc) + y (Fin.last (m + 1)) ≠ 0 := (add_pos hprefix hlast).ne'
  have hprefix_ne : (∑ i : Fin (m + 1), y i.castSucc) ≠ 0 := hprefix.ne'
  refine Prod.ext ?_ ?_
  · funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · -- Proof comment: on prefix coordinates, the split-last assembly is the Beta share times the
      -- normalized prefix block, which simplifies to the global normalization.
      simp [splitLastReassembledCoords]
      rw [dirichletNormalize_apply_eq_div_sum_of_nonneg (n := m + 2) (hn := by omega)
        hy_nonneg htotal_pos]
      rw [hsum]
      rw [dirichletNormalize_apply_eq_div_sum_of_nonneg (n := m + 1) (hn := by omega)
        hprefix_nonneg hprefix]
      field_simp [hshare_den_ne, hprefix_ne]
    · -- Proof comment: on the last coordinate, the complementary share is exactly the remaining
      -- mass divided by the total sum.
      simp only
      rw [dirichletNormalize_apply_eq_div_sum_of_nonneg (n := m + 2) (hn := by omega)
        hy_nonneg htotal_pos]
      rw [hsum]
      simp [splitLastReassembledCoords, Fin.lastCases]
      field_simp [hshare_den_ne]
      ring
  · rw [dirichletPositivePartSum_eq_sum_of_nonneg hy_nonneg]
    exact hsum.symm

/-- Helper for Definition 24.26: on the positive Gamma-support region, the staged owner assembly
recovers the full simplex normalization together with the carried total mass. -/
private theorem ownerSplitLastNormalizeAssembly_spec {m : ℕ} (hm : 1 ≤ m)
    (y : Fin (m + 2) → ℝ) (hy_nonneg : ∀ i, 0 ≤ y i)
    (hprefix : 0 < ∑ i : Fin (m + 1), y i.castSucc)
    (hlast : 0 < y (Fin.last (m + 1))) :
    (ownerSplitLastNormalizeAssembly (m := m)
        (dirichletNormalize (m + 1) (by omega) (fun k : Fin (m + 1) ↦ y k.castSucc),
          (∑ k : Fin (m + 1), y k.castSucc) /
            ((∑ k : Fin (m + 1), y k.castSucc) + y (Fin.last (m + 1)))),
      (∑ k : Fin (m + 1), y k.castSucc) + y (Fin.last (m + 1))) =
      (dirichletNormalize (m + 2) (by omega) y, dirichletPositivePartSum y) := by
  have hshare :
      0 ≤ (∑ k : Fin (m + 1), y k.castSucc) /
            ((∑ k : Fin (m + 1), y k.castSucc) + y (Fin.last (m + 1))) ∧
        (∑ k : Fin (m + 1), y k.castSucc) /
            ((∑ k : Fin (m + 1), y k.castSucc) + y (Fin.last (m + 1))) ≤ 1 := by
    constructor
    · exact div_nonneg (Finset.sum_nonneg fun i _ ↦ hy_nonneg i.castSucc)
        (le_of_lt (add_pos hprefix hlast))
    · have hden_pos :
          0 < (∑ k : Fin (m + 1), y k.castSucc) + y (Fin.last (m + 1)) := add_pos hprefix hlast
      have hnum_le :
          ∑ k : Fin (m + 1), y k.castSucc ≤
            (∑ k : Fin (m + 1), y k.castSucc) + y (Fin.last (m + 1)) :=
        le_add_of_nonneg_right (hy_nonneg (Fin.last (m + 1)))
      exact (div_le_one hden_pos).2 hnum_le
  have hassemble :=
    assembleDirichletNormalizeWithSum_splitLast (m := m) hm y hy_nonneg
      hprefix hlast
  refine Prod.ext ?_ ?_
  · -- Proof comment: after taking the admissible branch of the owner assembly, the first
    -- component is exactly the ambient split-last reassembly already identified with the full
    -- normalization map.
    ext i
    have hfirst :
        (ownerSplitLastNormalizeAssembly (m := m)
            (dirichletNormalize (m + 1) (by omega) (fun k : Fin (m + 1) ↦ y k.castSucc),
              (∑ k : Fin (m + 1), y k.castSucc) /
                ((∑ k : Fin (m + 1), y k.castSucc) + y (Fin.last (m + 1))))) i =
          splitLastReassembledCoords
            ((∑ k : Fin (m + 1), y k.castSucc) /
              ((∑ k : Fin (m + 1), y k.castSucc) + y (Fin.last (m + 1))))
            (dirichletNormalize (m + 1) (by omega) (fun k : Fin (m + 1) ↦ y k.castSucc)) i := by
      simpa using congrArg (fun z : dirichletSimplex (m + 2) ↦ z i)
        (ownerSplitLastNormalizeAssembly_of_mem (m := m) (x := dirichletNormalize (m + 1) (by omega)
          (fun k : Fin (m + 1) ↦ y k.castSucc)) (share :=
            (∑ k : Fin (m + 1), y k.castSucc) /
              ((∑ k : Fin (m + 1), y k.castSucc) + y (Fin.last (m + 1)))) hshare)
    rw [hfirst]
    simpa using congrArg (fun p : (Fin (m + 2) → ℝ) × ℝ ↦ p.1 i) hassemble
  · -- Proof comment: the carried total mass is the second component of the already verified
    -- split-last normalization theorem.
    simpa using congrArg Prod.snd hassemble

/-- Helper for Definition 24.26: the Beta law is almost surely supported on `[0, 1]`. -/
private theorem ae_mem_Icc_betaMeasure (r s : ℝ) :
    ∀ᵐ x ∂ betaMeasure r s, 0 ≤ x ∧ x ≤ 1 := by
  rw [betaMeasure, ae_withDensity_iff (by
    simpa [betaPDF] using ENNReal.measurable_ofReal.comp (measurable_betaPDFReal r s))]
  filter_upwards with x hx
  have hx_nonneg : 0 ≤ x := by
    -- Proof comment: the Beta density vanishes on the negative half-line.
    by_contra hx_neg
    exact hx (betaPDF_eq_zero_of_nonpos (le_of_not_ge hx_neg))
  have hx_le_one : x ≤ 1 := by
    -- Proof comment: the Beta density also vanishes on `(1, ∞)`.
    by_contra hx_gt
    exact hx (betaPDF_eq_zero_of_one_le (le_of_lt (not_le.mp hx_gt)))
  exact ⟨hx_nonneg, hx_le_one⟩

/-- Helper for Definition 24.26: the Beta law is almost surely supported on the open interval
`(0, 1)`. -/
private theorem ae_mem_Ioo_betaMeasure (r s : ℝ) :
    ∀ᵐ x ∂ betaMeasure r s, 0 < x ∧ x < 1 := by
  rw [betaMeasure, ae_withDensity_iff (by
    simpa [betaPDF] using ENNReal.measurable_ofReal.comp (measurable_betaPDFReal r s))]
  filter_upwards with x hx
  constructor
  · -- Proof comment: the Beta density vanishes at and to the left of `0`.
    by_contra hx_nonpos
    exact hx (betaPDF_eq_zero_of_nonpos (le_of_not_gt hx_nonpos))
  · -- Proof comment: the Beta density also vanishes at and to the right of `1`.
    by_contra hx_not_lt
    exact hx (betaPDF_eq_zero_of_one_le (le_of_not_gt hx_not_lt))

/-- Helper for Definition 24.26: the unit-rate Gamma law is almost surely nonnegative. -/
private theorem ae_nonneg_gammaMeasure_unitRate (a : ℝ) :
    ∀ᵐ x ∂ gammaMeasure a 1, 0 ≤ x := by
  rw [gammaMeasure, ae_withDensity_iff (by
    simpa [gammaPDF] using ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal a 1))]
  filter_upwards with x hx
  -- Proof comment: the Gamma density vanishes on the negative half-line.
  by_contra hx_neg
  exact hx (gammaPDF_of_neg (lt_of_not_ge hx_neg))

/-- Helper for Definition 24.26: the canonical Beta/Gamma splitting map sends the product
`betaMeasure r s × gammaMeasure (r + s) 1` to the independent Gamma product. -/
private theorem map_betaGammaToGammaPair_eq_prod_gamma
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    (((betaMeasure r s).prod (gammaMeasure (r + s) 1)).map
      (fun p : ℝ × ℝ ↦ (p.1 * p.2, (1 - p.1) * p.2))) =
      (gammaMeasure r 1).prod (gammaMeasure s 1) := by
  -- Proof comment: reuse the earlier Chapter 24 Beta/Gamma split theorem rather than duplicating
  -- the local Jacobian proof in this owner file.
  simpa using ProbabilityTheory.map_betaGammaSplit_eq_prod_gamma r s hr hs

/-- Helper for Definition 24.26: the ratio/sum map is the converse of the Beta/Gamma split on the
canonical Gamma-product source measure. -/
private theorem map_gammaPair_toRatioAndSum_eq_prod_beta_gamma
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    (((gammaMeasure r 1).prod (gammaMeasure s 1)).map
      (fun p : ℝ × ℝ ↦ (p.1 / (p.1 + p.2), p.1 + p.2))) =
      (betaMeasure r s).prod (gammaMeasure (r + s) 1) := by
  -- Proof comment: the converse ratio/sum transport is already proved in Exercise 24.3.1, so the
  -- local owner file only keeps this thin wrapper under its existing name.
  simpa using ProbabilityTheory.map_gammaPair_toRatioSum_eq_prod_beta_gamma r s hr hs

/-- Helper for Definition 24.26: inside the open Beta chart, the two-dimensional simplex density
pulls back to the standard Beta density. -/
private theorem dirichletDensity_comp_dirichletCoordsToSimplex_two_eq_betaPDF_of_pos_lt_one
    (θ : Fin 2 → ℝ) (hθ : ∀ i, 0 < θ i) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    ENNReal.ofReal (dirichletDensity θ (dirichletCoordsToSimplex 2 (by omega) ![b])) =
      betaPDF (θ 0) (θ 1) b := by
  have hmem : (![b] : Fin 1 → ℝ) ∈ dirichletChart 2 := by
    constructor
    · intro i
      fin_cases i
      simpa using hb0.le
    · simpa using hb1.le
  have hcoord0 : (dirichletCoordsToSimplex 2 (by omega) ![b]) 0 = b := by
    rw [dirichletCoordsToSimplex_of_mem (hn := by omega) hmem]
    simpa using dirichletCoordVector_castSucc (n := 2) (hn := by omega) (x := ![b]) (i := 0)
  have hcoord1 : (dirichletCoordsToSimplex 2 (by omega) ![b]) 1 = 1 - b := by
    rw [dirichletCoordsToSimplex_of_mem (hn := by omega) hmem]
    simpa using dirichletCoordVector_last (n := 2) (hn := by omega) (x := ![b])
  -- Proof comment: on the interior chart, the simplex density is exactly the Beta density after
  -- rewriting the two simplex coordinates as `b` and `1 - b`.
  rw [betaPDF_of_pos_lt_one hb0 hb1]
  have hprod :
      ∏ i, ((dirichletCoordsToSimplex 2 (by omega) ![b]) i).rpow (θ i - 1) =
        b ^ (θ 0 - 1) * (1 - b) ^ (θ 1 - 1) := by
    simp [Fin.prod_univ_two, hcoord0, hcoord1]
  rw [dirichletDensity, Fin.sum_univ_two, hprod]
  rw [beta]
  congr 1
  rw [Fin.prod_univ_two, div_eq_mul_inv]
  have hGamma0 : Real.Gamma (θ 0) ≠ 0 := (Real.Gamma_pos_of_pos (hθ 0)).ne'
  have hGamma1 : Real.Gamma (θ 1) ≠ 0 := (Real.Gamma_pos_of_pos (hθ 1)).ne'
  have hGammaSum : Real.Gamma (θ 0 + θ 1) ≠ 0 := by
    exact (Real.Gamma_pos_of_pos (add_pos (hθ 0) (hθ 1))).ne'
  field_simp [hGamma0, hGamma1, hGammaSum]

/-- Helper for Definition 24.26: in dimension `2`, the simplex chart measure is the pushforward of
restricted Lebesgue measure on `[0, 1]`. -/
private theorem dirichletSimplexVolume_two_eq_map_intervalChart :
    dirichletSimplexVolume 2 (by omega) =
      Measure.map (fun b : ℝ ↦ dirichletCoordsToSimplex 2 (by omega) ![b])
        ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)) := by
  let e : (Fin 1 → ℝ) ≃ᵐ ℝ := MeasurableEquiv.funUnique (Fin 1) ℝ
  let μI : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)
  have hchart :
      e ⁻¹' Set.Icc (0 : ℝ) 1 = dirichletChart 2 := by
    -- Proof comment: the unique coordinate on `Fin 1` is exactly the interval parameter.
    ext x
    change (0 ≤ x 0 ∧ x 0 ≤ 1) ↔ x ∈ dirichletChart 2
    simp [dirichletChart]
  have hsource :
      ((volume : Measure (Fin 1 → ℝ)).restrict (dirichletChart 2)) = Measure.map e.symm μI := by
    have hmap :
        Measure.map e ((volume : Measure (Fin 1 → ℝ)).restrict (dirichletChart 2)) = μI := by
      -- Proof comment: transport the restricted chart source through `funUnique`, then use that
      -- `volume` is preserved by the singleton-coordinate measurable equivalence.
      rw [← hchart, ← e.restrict_map (volume : Measure (Fin 1 → ℝ)) (Set.Icc (0 : ℝ) 1)]
      have hvol :
          Measure.map e (volume : Measure (Fin 1 → ℝ)) = (volume : Measure ℝ) := by
        simpa [e] using (volume_preserving_funUnique (Fin 1) ℝ).map_eq
      simpa [μI] using congrArg
        (fun ν : Measure ℝ ↦ ν.restrict (Set.Icc (0 : ℝ) 1)) hvol
    calc
      ((volume : Measure (Fin 1 → ℝ)).restrict (dirichletChart 2))
          = Measure.map e.symm (Measure.map e ((volume : Measure (Fin 1 → ℝ)).restrict (dirichletChart 2))) := by
              rw [Measure.map_map e.symm.measurable e.measurable]
              simp
      _ = Measure.map e.symm μI := by rw [hmap]
  have hcoords :
      AEMeasurable (dirichletCoordsToSimplex 2 (by omega)) (Measure.map e.symm μI) := by
    -- Proof comment: after rewriting the source measure back to the chart-restricted measure, the
    -- existing restricted a.e. measurability theorem applies directly.
    rw [← hsource]
    simpa using aemeasurable_dirichletCoordsToSimplex_restrict (n := 2) (hn := by omega)
  calc
    dirichletSimplexVolume 2 (by omega)
        = Measure.map (dirichletCoordsToSimplex 2 (by omega)) (Measure.map e.symm μI) := by
            simp [dirichletSimplexVolume, hsource]
    _ = Measure.map ((dirichletCoordsToSimplex 2 (by omega)) ∘ e.symm) μI := by
          -- Proof comment: compose the singleton-coordinate equivalence with the chart map.
          rw [AEMeasurable.map_map_of_aemeasurable hcoords e.symm.measurable.aemeasurable]
    _ = Measure.map (fun b : ℝ ↦ dirichletCoordsToSimplex 2 (by omega) ![b]) μI := by
          refine Measure.map_congr <| Filter.EventuallyEq.of_eq ?_
          funext b
          change dirichletCoordsToSimplex 2 (by omega) (e.symm b) =
            dirichletCoordsToSimplex 2 (by omega) ![b]
          have hs : e.symm b = (![b] : Fin 1 → ℝ) := by
            funext i
            fin_cases i
            simp [e]
          rw [hs]

/-- Helper for Definition 24.26: on `[0, 1]`, the two-dimensional simplex density agrees almost
everywhere with the Beta density pulled back along the interval chart. -/
private theorem dirichletDensity_comp_dirichletCoordsToSimplex_two_ae_eq_betaPDF_restrict
    (θ : Fin 2 → ℝ) (hθ : ∀ i, 0 < θ i) :
    (fun b : ℝ ↦ ENNReal.ofReal (dirichletDensity θ (dirichletCoordsToSimplex 2 (by omega) ![b]))) =ᵐ[((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1))]
      betaPDF (θ 0) (θ 1) := by
  refine (ae_restrict_iff' measurableSet_Icc).2 ?_
  have hboundary_ae : ∀ᵐ b ∂ (volume : Measure ℝ), b ≠ 0 ∧ b ≠ 1 := by
    -- Proof comment: the only points in `[0, 1]` outside the open Beta chart are the two
    -- boundary atoms, which are null for Lebesgue measure.
    rw [ae_iff]
    change (volume : Measure ℝ) {b : ℝ | ¬ (b ≠ 0 ∧ b ≠ 1)} = 0
    have hset : {b : ℝ | ¬ (b ≠ 0 ∧ b ≠ 1)} = ({0} ∪ {1} : Set ℝ) := by
      ext b
      by_cases h0 : b = 0 <;> by_cases h1 : b = 1 <;> simp [h0, h1]
    rw [hset]
    simpa using
      (by simp : Set.Finite (({0} ∪ {1}) : Set ℝ)).measure_zero (μ := (volume : Measure ℝ))
  filter_upwards [hboundary_ae] with b hb
  intro hIcc
  have hb0 : 0 < b := lt_of_le_of_ne hIcc.1 (Ne.symm hb.1)
  have hb1 : b < 1 := lt_of_le_of_ne hIcc.2 hb.2
  -- Proof comment: away from the null boundary set, the interval point lies in the open Beta
  -- chart and the explicit interior density computation applies.
  exact dirichletDensity_comp_dirichletCoordsToSimplex_two_eq_betaPDF_of_pos_lt_one θ hθ hb0 hb1

/-- Helper for Definition 24.26: restricting Lebesgue measure to `[0, 1]` before weighting by the
Beta density does not change the resulting Beta law. -/
private theorem withDensity_restrict_Icc_betaPDF_eq_betaMeasure (θ : Fin 2 → ℝ) :
    (((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)).withDensity
      (betaPDF (θ 0) (θ 1))) = betaMeasure (θ 0) (θ 1) := by
  have hindicator :
      (Set.Icc (0 : ℝ) 1).indicator (betaPDF (θ 0) (θ 1)) = betaPDF (θ 0) (θ 1) := by
    -- Proof comment: outside `[0, 1]`, the Beta density is already zero, so the interval
    -- indicator does not change the density.
    funext b
    by_cases hb : b ∈ Set.Icc (0 : ℝ) 1
    · simp [hb]
    · have hout : b ≤ 0 ∨ 1 ≤ b := by
        by_cases hb0 : b < 0
        · exact Or.inl hb0.le
        · right
          have hb0' : 0 ≤ b := le_of_not_gt hb0
          have hb1 : ¬ b ≤ 1 := by
            intro hb1
            exact hb ⟨hb0', hb1⟩
          exact le_of_lt (lt_of_not_ge hb1)
      cases hout with
      | inl hb0 =>
          simp [Set.indicator_of_notMem, hb, betaPDF_eq_zero_of_nonpos hb0]
      | inr hb1 =>
          simp [Set.indicator_of_notMem, hb, betaPDF_eq_zero_of_one_le hb1]
  calc
    (((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)).withDensity (betaPDF (θ 0) (θ 1)))
        = (volume : Measure ℝ).withDensity ((Set.Icc (0 : ℝ) 1).indicator (betaPDF (θ 0) (θ 1))) := by
            -- Proof comment: `withDensity_indicator` packages the support restriction as a single
            -- canonical rewrite.
            symm
            simpa using
              (withDensity_indicator (μ := (volume : Measure ℝ)) measurableSet_Icc
                (betaPDF (θ 0) (θ 1)))
    _ = (volume : Measure ℝ).withDensity (betaPDF (θ 0) (θ 1)) := by
          rw [hindicator]
    _ = betaMeasure (θ 0) (θ 1) := by
          rw [betaMeasure]

/-- Helper for Definition 24.26: restricting Lebesgue measure to `Set.Ioc (0 : ℝ) 1` before
weighting by the Beta density does not change the resulting Beta law. -/
private theorem withDensity_restrict_Ioc_betaPDF_eq_betaMeasure (a b : ℝ) :
    (((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)).withDensity
      (betaPDF a b)) = betaMeasure a b := by
  have hindicator :
      (Set.Ioc (0 : ℝ) 1).indicator (betaPDF a b) = betaPDF a b := by
    -- Proof comment: outside `Set.Ioc (0, 1]`, the Beta density is already zero, so the support
    -- restriction does not change the density.
    funext x
    by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
    · simp [hx]
    · have hout : x ≤ 0 ∨ 1 ≤ x := by
        by_cases hx0 : 0 < x
        · right
          have hx1 : ¬ x ≤ 1 := by
            intro hx1
            exact hx ⟨hx0, hx1⟩
          exact le_of_lt (lt_of_not_ge hx1)
        · left
          exact le_of_not_gt hx0
      cases hout with
      | inl hx0 =>
          simp [Set.indicator_of_notMem, hx, betaPDF_eq_zero_of_nonpos hx0]
      | inr hx1 =>
          simp [Set.indicator_of_notMem, hx, betaPDF_eq_zero_of_one_le hx1]
  calc
    (((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)).withDensity (betaPDF a b))
        = (volume : Measure ℝ).withDensity
            ((Set.Ioc (0 : ℝ) 1).indicator (betaPDF a b)) := by
            -- Proof comment: `withDensity_indicator` packages the restriction as an ambient
            -- density with an explicit indicator.
            symm
            simpa using
              (withDensity_indicator (μ := (volume : Measure ℝ)) measurableSet_Ioc
                (betaPDF a b))
    _ = (volume : Measure ℝ).withDensity (betaPDF a b) := by
          rw [hindicator]
    _ = betaMeasure a b := by
          rw [betaMeasure]

/-- Helper for Definition 24.26: the interval chart for `Δ₂` is a.e. measurable for the
restricted Lebesgue source on `[0, 1]`. -/
private theorem aemeasurable_dirichletCoordsToSimplex_two_intervalChart :
    AEMeasurable (fun b : ℝ ↦ dirichletCoordsToSimplex 2 (by omega) ![b])
      (((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1))) := by
  let e : (Fin 1 → ℝ) ≃ᵐ ℝ := MeasurableEquiv.funUnique (Fin 1) ℝ
  let μI : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)
  have hchart :
      e ⁻¹' Set.Icc (0 : ℝ) 1 = dirichletChart 2 := by
    -- Proof comment: the unique `Fin 1` coordinate is exactly the interval parameter.
    ext x
    change (0 ≤ x 0 ∧ x 0 ≤ 1) ↔ x ∈ dirichletChart 2
    simp [dirichletChart]
  have hsource :
      ((volume : Measure (Fin 1 → ℝ)).restrict (dirichletChart 2)) = Measure.map e.symm μI := by
    have hmap :
        Measure.map e ((volume : Measure (Fin 1 → ℝ)).restrict (dirichletChart 2)) = μI := by
      -- Proof comment: transport the chart source to the interval through `funUnique`.
      rw [← hchart, ← e.restrict_map (volume : Measure (Fin 1 → ℝ)) (Set.Icc (0 : ℝ) 1)]
      have hvol :
          Measure.map e (volume : Measure (Fin 1 → ℝ)) = (volume : Measure ℝ) := by
        simpa [e] using (volume_preserving_funUnique (Fin 1) ℝ).map_eq
      simpa [μI] using congrArg
        (fun ν : Measure ℝ ↦ ν.restrict (Set.Icc (0 : ℝ) 1)) hvol
    calc
      ((volume : Measure (Fin 1 → ℝ)).restrict (dirichletChart 2))
          = Measure.map e.symm
              (Measure.map e ((volume : Measure (Fin 1 → ℝ)).restrict (dirichletChart 2))) := by
              rw [Measure.map_map e.symm.measurable e.measurable]
              simp
      _ = Measure.map e.symm μI := by rw [hmap]
  have hcoords :
      AEMeasurable (dirichletCoordsToSimplex 2 (by omega)) (Measure.map e.symm μI) := by
    -- Proof comment: after rewriting back to the chart source, the existing restricted
    -- a.e.-measurability theorem applies directly.
    rw [← hsource]
    simpa using aemeasurable_dirichletCoordsToSimplex_restrict (n := 2) (hn := by omega)
  have hchartEq :
      (fun b : ℝ ↦ dirichletCoordsToSimplex 2 (by omega) ![b]) =
        (dirichletCoordsToSimplex 2 (by omega)) ∘ e.symm := by
    -- Proof comment: `e.symm` reconstructs the unique `Fin 1` vector from its sole coordinate.
    funext b
    change dirichletCoordsToSimplex 2 (by omega) ![b] =
      dirichletCoordsToSimplex 2 (by omega) (e.symm b)
    congr 1
    funext i
    fin_cases i
    simp [e]
  rw [hchartEq]
  exact hcoords.comp_measurable e.symm.measurable

/-- Helper for Definition 24.26: the interval chart for `Δ₂` stays a.e. measurable for the
Beta source, because the Beta law is absolutely continuous with respect to restricted Lebesgue
measure on `[0, 1]`. -/
private theorem aemeasurable_dirichletCoordsToSimplex_two_beta (θ : Fin 2 → ℝ) :
    AEMeasurable (fun b : ℝ ↦ dirichletCoordsToSimplex 2 (by omega) ![b])
      (betaMeasure (θ 0) (θ 1)) := by
  -- Proof comment: transfer the restricted-Lebesgue a.e. measurability along absolute
  -- continuity of the Beta measure.
  rw [← withDensity_restrict_Icc_betaPDF_eq_betaMeasure θ]
  exact aemeasurable_dirichletCoordsToSimplex_two_intervalChart.mono_ac
    (withDensity_absolutelyContinuous _ _)

/-- Helper for Definition 24.26: in dimension `2`, pushing the Beta share through the interval
chart recovers the simplex-density owner measure. -/
private theorem map_intervalChart_betaMeasure_to_dirichletDensityMeasure_two
    (θ : Fin 2 → ℝ) (hθ : ∀ i, 0 < θ i) :
    Measure.map (fun b : ℝ ↦ dirichletCoordsToSimplex 2 (by omega) ![b])
      (betaMeasure (θ 0) (θ 1)) =
      (((dirichletSimplexVolume 2 (by omega)).withDensity
        (fun x ↦ ENNReal.ofReal (dirichletDensity θ x))) : Measure (dirichletSimplex 2)) := by
  let μI : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)
  let chart : ℝ → dirichletSimplex 2 := fun b ↦ dirichletCoordsToSimplex 2 (by omega) ![b]
  let F : dirichletSimplex 2 → ENNReal := fun x ↦ ENNReal.ofReal (dirichletDensity θ x)
  have hchart_aemeas_Icc :
      AEMeasurable chart μI := aemeasurable_dirichletCoordsToSimplex_two_intervalChart
  have hchart_aemeas_beta :
      AEMeasurable chart (betaMeasure (θ 0) (θ 1)) :=
    aemeasurable_dirichletCoordsToSimplex_two_beta θ
  ext A hA
  have hpreimage :
      NullMeasurableSet (chart ⁻¹' A) μI :=
    hchart_aemeas_Icc.nullMeasurableSet_preimage hA
  have hpreimage_restrict :
      NullMeasurableSet (chart ⁻¹' A) (μI.restrict (chart ⁻¹' A)) := by
    rw [MeasureTheory.nullMeasurableSet_restrict hpreimage]
    simpa using hpreimage
  have hindicator :
      (fun b : ℝ ↦ A.indicator F (chart b)) =
        (chart ⁻¹' A).indicator (fun b ↦ F (chart b)) := by
    -- Proof comment: after precomposing by the chart map, the simplex indicator becomes the
    -- ambient indicator of the preimage set.
    funext b
    by_cases hb : chart b ∈ A <;> simp [F, hb]
  calc
    Measure.map chart (betaMeasure (θ 0) (θ 1)) A
        = betaMeasure (θ 0) (θ 1) (chart ⁻¹' A) := by
            simpa using Measure.map_apply_of_aemeasurable hchart_aemeas_beta hA
    _ = ∫⁻ b in chart ⁻¹' A, betaPDF (θ 0) (θ 1) b ∂μI := by
          rw [← withDensity_restrict_Icc_betaPDF_eq_betaMeasure θ]
          rw [withDensity_apply' _ (chart ⁻¹' A)]
    _ = ∫⁻ b in chart ⁻¹' A, F (chart b) ∂μI := by
          refine lintegral_congr_ae ?_
          filter_upwards [ae_mono (Measure.restrict_le_self (s := chart ⁻¹' A))
            (dirichletDensity_comp_dirichletCoordsToSimplex_two_ae_eq_betaPDF_restrict θ hθ)]
            with b hb
          exact hb.symm
    _ = ((dirichletSimplexVolume 2 (by omega)).withDensity F) A := by
          rw [withDensity_apply F hA]
          rw [dirichletSimplexVolume_two_eq_map_intervalChart]
          rw [← lintegral_indicator hA]
          symm
          change
            ∫⁻ x, A.indicator F x ∂Measure.map chart μI =
              ∫⁻ b in chart ⁻¹' A, F (chart b) ∂μI
          rw [lintegral_map' ((measurable_dirichletDensity θ).indicator hA).aemeasurable
            hchart_aemeas_Icc]
          rw [hindicator]
          simpa [F] using
            (MeasureTheory.lintegral_indicator₀ hpreimage (fun b : ℝ ↦ F (chart b)))

/-- Helper for Definition 24.26: on strictly positive pairs, the owner normalization map is the
interval-chart ratio coordinate together with the ordinary total mass. -/
private theorem dirichletNormalize_two_eq_coordsToSimplex_ratioSum_of_pos
    {y : Fin 2 → ℝ} (hy : ∀ i, 0 < y i) :
    (dirichletNormalize 2 (by omega) y, dirichletPositivePartSum y) =
      (dirichletCoordsToSimplex 2 (by omega) ![y 0 / (y 0 + y 1)], y 0 + y 1) := by
  have hy_nonneg : ∀ i, 0 ≤ y i := fun i ↦ (hy i).le
  have hsum_pos : 0 < ∑ i : Fin 2, y i := by
    simpa [Fin.sum_univ_two] using add_pos (hy 0) (hy 1)
  have hsum_ne : y 0 + y 1 ≠ 0 := (add_pos (hy 0) (hy 1)).ne'
  have hmem : (![y 0 / (y 0 + y 1)] : Fin 1 → ℝ) ∈ dirichletChart 2 := by
    constructor
    · intro i
      fin_cases i
      exact div_nonneg (hy_nonneg 0) (le_of_lt (add_pos (hy 0) (hy 1)))
    · simpa using
        (div_le_one (add_pos (hy 0) (hy 1))).2 (le_add_of_nonneg_right (hy_nonneg 1))
  refine Prod.ext ?_ ?_
  · -- Proof comment: the first coordinate is the Beta share, and the second simplex coordinate is
    -- the complementary share.
    ext i
    fin_cases i
    · rw [dirichletNormalize_apply_eq_div_sum_of_nonneg (n := 2) (hn := by omega) hy_nonneg
        hsum_pos]
      rw [dirichletCoordsToSimplex_of_mem (hn := by omega) hmem]
      simpa [Fin.sum_univ_two] using
        dirichletCoordVector_castSucc (n := 2) (hn := by omega)
          (x := ![y 0 / (y 0 + y 1)]) (i := 0)
    · rw [dirichletNormalize_apply_eq_div_sum_of_nonneg (n := 2) (hn := by omega) hy_nonneg
        hsum_pos]
      rw [dirichletCoordsToSimplex_of_mem (hn := by omega) hmem]
      change y 1 / ∑ j, y j =
        dirichletCoordVector 2 (by omega) ![y 0 / (y 0 + y 1)] 1
      have hlast :
          dirichletCoordVector 2 (by omega) ![y 0 / (y 0 + y 1)] 1 =
            1 - y 0 / (y 0 + y 1) := by
        simpa using dirichletCoordVector_last (n := 2) (hn := by omega)
          (x := ![y 0 / (y 0 + y 1)])
      rw [hlast]
      simp only [Fin.sum_univ_two]
      field_simp [hsum_ne]
      ring
  · -- Proof comment: on the positive Gamma-support region, the positive-part sum is the ordinary
    -- coordinate sum.
    rw [dirichletPositivePartSum_eq_sum_of_nonneg hy_nonneg]
    simp [Fin.sum_univ_two]

/-- Helper for Definition 24.26: in dimension `2`, the Gamma pair maps to the joint law of the
Dirichlet owner and its carried total mass. -/
private theorem map_dirichletGammaProduct_to_densityProdGammaSum_two
    (θ : Fin 2 → ℝ) (hθ : ∀ i, 0 < θ i) :
    Measure.map (fun y : Fin 2 → ℝ ↦
        (dirichletNormalize 2 (by omega) y, dirichletPositivePartSum y))
      (dirichletGammaProductCore θ hθ : Measure (Fin 2 → ℝ)) =
      ((((dirichletSimplexVolume 2 (by omega)).withDensity
          (fun x ↦ ENNReal.ofReal (dirichletDensity θ x))) : Measure (dirichletSimplex 2)).prod
        (gammaMeasure (∑ i : Fin 2, θ i) 1)) := by
  let μ : Measure (Fin 2 → ℝ) := (dirichletGammaProductCore θ hθ : Measure (Fin 2 → ℝ))
  let μPair : Measure (ℝ × ℝ) := (gammaMeasure (θ 0) 1).prod (gammaMeasure (θ 1) 1)
  let β : Measure ℝ := betaMeasure (θ 0) (θ 1)
  let γ : Measure ℝ := gammaMeasure (∑ i : Fin 2, θ i) 1
  let chart : ℝ → dirichletSimplex 2 := fun b ↦ dirichletCoordsToSimplex 2 (by omega) ![b]
  let normalizeWithSum : (Fin 2 → ℝ) → dirichletSimplex 2 × ℝ :=
    fun y ↦ (dirichletNormalize 2 (by omega) y, dirichletPositivePartSum y)
  let stage : ℝ × ℝ → dirichletSimplex 2 × ℝ := fun p ↦ (chart p.1, p.2)
  let pairNormalizeWithSum : ℝ × ℝ → dirichletSimplex 2 × ℝ :=
    fun p ↦ (chart (p.1 / (p.1 + p.2)), p.1 + p.2)
  letI : IsProbabilityMeasure (gammaMeasure (θ 0) 1) :=
    isProbabilityMeasure_gammaMeasure (hθ 0) zero_lt_one
  letI : IsProbabilityMeasure (gammaMeasure (θ 1) 1) :=
    isProbabilityMeasure_gammaMeasure (hθ 1) zero_lt_one
  letI : SFinite (gammaMeasure (θ 0) 1) := by infer_instance
  letI : SFinite (gammaMeasure (θ 1) 1) := by infer_instance
  letI : IsProbabilityMeasure β := isProbabilityMeasureBeta (hθ 0) (hθ 1)
  letI : IsProbabilityMeasure γ := by
    simpa [γ, Fin.sum_univ_two] using
      isProbabilityMeasure_gammaMeasure (add_pos (hθ 0) (hθ 1)) zero_lt_one
  letI : SFinite β := by infer_instance
  letI : SFinite γ := by infer_instance
  have hnormalize_meas : Measurable normalizeWithSum := by
    -- Proof comment: both the owner normalization and the carried positive-part sum are
    -- measurable functions of the Gamma pair.
    have hsum_meas : Measurable (dirichletPositivePartSum (n := 2)) := by
      simpa [dirichletPositivePartSum] using
        (Finset.measurable_sum Finset.univ
          (fun i _ ↦ (measurable_pi_apply i).max measurable_const))
    exact (measurable_dirichletNormalize 2 (by omega)).prodMk hsum_meas
  have hstage_aemeas : AEMeasurable stage (β.prod γ) := by
    -- Proof comment: the first coordinate is a.e. measurable for the Beta source, while the
    -- second coordinate is measurable by projection.
    exact (aemeasurable_dirichletCoordsToSimplex_two_beta θ).comp_fst.prodMk
      measurable_snd.aemeasurable
  have hsource :
      μ = Measure.map MeasurableEquiv.finTwoArrow.symm μPair := by
    have hmap :
        Measure.map MeasurableEquiv.finTwoArrow μ = μPair := by
      -- Proof comment: the `Fin 2` Gamma-product source is the canonical pair product under
      -- `finTwoArrow`.
      have hpi :
          Measure.pi (fun i : Fin 2 ↦ gammaMeasure (θ i) 1) =
            Measure.pi ![gammaMeasure (θ 0) 1, gammaMeasure (θ 1) 1] := by
        congr 1
        ext i
        fin_cases i <;> rfl
      change Measure.map MeasurableEquiv.finTwoArrow
          (Measure.pi fun i : Fin 2 ↦ gammaMeasure (θ i) 1) = μPair
      rw [hpi]
      simpa [μPair, dirichletGammaProductCore, ProbabilityMeasure.toMeasure_pi] using
        (measurePreserving_finTwoArrow_vec (gammaMeasure (θ 0) 1)
          (gammaMeasure (θ 1) 1)).map_eq
    calc
      μ = Measure.map MeasurableEquiv.finTwoArrow.symm (Measure.map MeasurableEquiv.finTwoArrow μ) := by
            simpa using (MeasurableEquiv.map_symm_map (μ := μ) MeasurableEquiv.finTwoArrow).symm
      _ = Measure.map MeasurableEquiv.finTwoArrow.symm μPair := by rw [hmap]
  have hpairPosFst : ∀ᵐ p ∂ μPair, 0 < p.1 := by
    have hfstLaw :
        HasLaw Prod.fst (gammaMeasure (θ 0) 1) μPair :=
      (measurePreserving_fst (μ := gammaMeasure (θ 0) 1) (ν := gammaMeasure (θ 1) 1)).hasLaw
    -- Proof comment: the first Gamma coordinate stays strictly positive almost surely.
    exact (hfstLaw.ae_iff (by fun_prop)).2
      (ae_pos_gammaMeasure_unitRate (θ 0) (hθ 0))
  have hpairPosSnd : ∀ᵐ p ∂ μPair, 0 < p.2 := by
    have hsndLaw :
        HasLaw Prod.snd (gammaMeasure (θ 1) 1) μPair :=
      (measurePreserving_snd (μ := gammaMeasure (θ 0) 1) (ν := gammaMeasure (θ 1) 1)).hasLaw
    -- Proof comment: the second Gamma coordinate is likewise strictly positive almost surely.
    exact (hsndLaw.ae_iff (by fun_prop)).2
      (ae_pos_gammaMeasure_unitRate (θ 1) (hθ 1))
  have hnormalize_eq :
      (normalizeWithSum ∘ MeasurableEquiv.finTwoArrow.symm) =ᵐ[μPair] pairNormalizeWithSum := by
    -- Proof comment: on the positive Gamma support, the owner normalization becomes the usual
    -- ratio/sum chart from Exercise 24.3.1.
    filter_upwards [hpairPosFst, hpairPosSnd] with p hp1 hp2
    have hpos : ∀ i : Fin 2, 0 < (MeasurableEquiv.finTwoArrow.symm p) i := by
      intro i
      fin_cases i
      · simpa [MeasurableEquiv.finTwoArrow] using hp1
      · simpa [MeasurableEquiv.finTwoArrow] using hp2
    simpa [normalizeWithSum, pairNormalizeWithSum, chart, MeasurableEquiv.finTwoArrow] using
      dirichletNormalize_two_eq_coordsToSimplex_ratioSum_of_pos hpos
  have hratio :
      Measure.map (fun p : ℝ × ℝ ↦ (p.1 / (p.1 + p.2), p.1 + p.2)) μPair = β.prod γ := by
    -- Proof comment: the pair source factors through the classical Beta/Gamma ratio-sum law.
    simpa [μPair, β, γ, Fin.sum_univ_two] using
      map_gammaPair_toRatioAndSum_eq_prod_beta_gamma (θ 0) (θ 1) (hθ 0) (hθ 1)
  have hstage :
      Measure.map stage (β.prod γ) = (Measure.map chart β).prod γ := by
    have hindep :
        IndepFun (fun p : ℝ × ℝ ↦ chart p.1) (fun p : ℝ × ℝ ↦ p.2) (β.prod γ) := by
      simpa [chart] using indepFun_prod₀
        (aemeasurable_dirichletCoordsToSimplex_two_beta θ) measurable_id.aemeasurable
    have hmap :
        Measure.map stage (β.prod γ) =
          (Measure.map (fun p : ℝ × ℝ ↦ chart p.1) (β.prod γ)).prod
            (Measure.map (fun p : ℝ × ℝ ↦ p.2) (β.prod γ)) := by
      -- Proof comment: the two product coordinates remain independent after applying the chart
      -- map to the Beta share and keeping the Gamma total mass unchanged.
      exact (indepFun_iff_map_prod_eq_prod_map_map
        ((aemeasurable_dirichletCoordsToSimplex_two_beta θ).comp_fst)
        measurable_snd.aemeasurable).1 hindep
    have hfst :
        Measure.map (fun p : ℝ × ℝ ↦ chart p.1) (β.prod γ) = Measure.map chart β := by
      have hchart_fst :
          AEMeasurable chart (Measure.map Prod.fst (β.prod γ)) := by
        rw [(measurePreserving_fst (μ := β) (ν := γ)).map_eq]
        exact aemeasurable_dirichletCoordsToSimplex_two_beta θ
      calc
        Measure.map (fun p : ℝ × ℝ ↦ chart p.1) (β.prod γ)
            = Measure.map chart (Measure.map Prod.fst (β.prod γ)) := by
                symm
                exact AEMeasurable.map_map_of_aemeasurable
                  hchart_fst measurable_fst.aemeasurable
        _ = Measure.map chart β := by rw [(measurePreserving_fst (μ := β) (ν := γ)).map_eq]
    have hsnd :
        Measure.map (fun p : ℝ × ℝ ↦ p.2) (β.prod γ) = γ := by
      exact (measurePreserving_snd (μ := β) (ν := γ)).map_eq
    rw [hmap, hfst, hsnd]
  calc
    Measure.map normalizeWithSum μ
        = Measure.map (normalizeWithSum ∘ MeasurableEquiv.finTwoArrow.symm) μPair := by
            rw [hsource, Measure.map_map hnormalize_meas MeasurableEquiv.finTwoArrow.symm.measurable]
    _ = Measure.map pairNormalizeWithSum μPair := by
          exact Measure.map_congr hnormalize_eq
    _ = Measure.map stage (Measure.map (fun p : ℝ × ℝ ↦ (p.1 / (p.1 + p.2), p.1 + p.2)) μPair) := by
          rw [show pairNormalizeWithSum = stage ∘
              (fun p : ℝ × ℝ ↦ (p.1 / (p.1 + p.2), p.1 + p.2)) by
                funext p
                rfl]
          have hstage_ratio :
              AEMeasurable stage
                (Measure.map (fun p : ℝ × ℝ ↦ (p.1 / (p.1 + p.2), p.1 + p.2)) μPair) := by
            rw [hratio]
            exact hstage_aemeas
          rw [AEMeasurable.map_map_of_aemeasurable hstage_ratio
            (by fun_prop : AEMeasurable (fun p : ℝ × ℝ ↦ (p.1 / (p.1 + p.2), p.1 + p.2)) μPair)]
    _ = Measure.map stage (β.prod γ) := by rw [hratio]
    _ = (Measure.map chart β).prod γ := hstage
    _ = ((((dirichletSimplexVolume 2 (by omega)).withDensity
            (fun x ↦ ENNReal.ofReal (dirichletDensity θ x))) : Measure (dirichletSimplex 2)).prod γ) := by
          rw [map_intervalChart_betaMeasure_to_dirichletDensityMeasure_two θ hθ]

/-- Helper for Definition 24.26: rewrite the split-last owner assembly in the carried-mass normal
form produced by the induction hypothesis. -/
private theorem ownerSplitLastNormalizeAssembly_spec_of_prefixCarriedMass {m : ℕ}
    (hm : 1 ≤ m) (y : Fin (m + 2) → ℝ) (hy_nonneg : ∀ i, 0 ≤ y i)
    (hprefix : 0 < ∑ i : Fin (m + 1), y i.castSucc)
    (hlast : 0 < y (Fin.last (m + 1))) :
    (ownerSplitLastNormalizeAssembly (m := m)
        (dirichletNormalize (m + 1) (by omega) (fun k : Fin (m + 1) ↦ y k.castSucc),
          dirichletPositivePartSum (fun k : Fin (m + 1) ↦ y k.castSucc) /
            (dirichletPositivePartSum (fun k : Fin (m + 1) ↦ y k.castSucc) +
              y (Fin.last (m + 1)))),
      dirichletPositivePartSum (fun k : Fin (m + 1) ↦ y k.castSucc) +
        y (Fin.last (m + 1))) =
      (dirichletNormalize (m + 2) (by omega) y, dirichletPositivePartSum y) := by
  have hprefixMass :
      dirichletPositivePartSum (fun k : Fin (m + 1) ↦ y k.castSucc) =
        ∑ i : Fin (m + 1), y i.castSucc := by
    -- Proof comment: on the positive Gamma-support region, the prefix carried mass is the
    -- ordinary prefix sum.
    rw [dirichletPositivePartSum_eq_sum_of_nonneg]
    intro i
    exact hy_nonneg i.castSucc
  -- Proof comment: after normalizing the carried mass spelling, this is the existing split-last
  -- source-side assembly identity.
  simpa [hprefixMass] using
    ownerSplitLastNormalizeAssembly_spec (m := m) hm y hy_nonneg hprefix hlast

/-- Helper for Definition 24.26: on a point of the `(m + 2)`-chart, the simplex density rewrites
to the explicit chart kernel in the first `m + 1` coordinates and the recovered last coordinate.
-/
private theorem dirichletDensity_comp_dirichletCoordsToSimplex_eq_of_mem_chart {m : ℕ}
    (θ : Fin (m + 2) → ℝ) {x : Fin (m + 1) → ℝ} (hx : x ∈ dirichletChart (m + 2)) :
    dirichletDensity θ (dirichletCoordsToSimplex (m + 2) (by omega) x) =
      (Real.Gamma (∑ i, θ i) / ∏ i, Real.Gamma (θ i)) *
        ((∏ i : Fin (m + 1), Real.rpow (x i) (θ i.castSucc - 1)) *
          Real.rpow (1 - ∑ i, x i) (θ (Fin.last (m + 1)) - 1)) := by
  have hprod :
      ∏ i : Fin (m + 2), Real.rpow (dirichletCoordVector (m + 2) (by omega) x i) (θ i - 1) =
        (∏ i : Fin (m + 1), Real.rpow (x i) (θ i.castSucc - 1)) *
          Real.rpow (1 - ∑ i, x i) (θ (Fin.last (m + 1)) - 1) := by
    -- Proof comment: splitting the product off at the terminal coordinate leaves exactly the
    -- `castSucc` chart coordinates together with the recovered last coordinate.
    rw [Fin.prod_univ_castSucc]
    congr 1
    · refine Finset.prod_congr rfl ?_
      intro i hi
      have hcoord :
          dirichletCoordVector (m + 2) (by omega) x i.castSucc = x i := by
        simpa using
          dirichletCoordVector_castSucc (n := m + 2) (hn := by omega) (x := x) (i := i)
      rw [hcoord]
    · have hlast :
          dirichletCoordVector (m + 2) (by omega) x (Fin.last (m + 1)) = 1 - ∑ i, x i := by
        simpa using dirichletCoordVector_last (n := m + 2) (hn := by omega) (x := x)
      rw [hlast]
  -- Proof comment: on the chart domain, `dirichletCoordsToSimplex` is the explicit chart
  -- embedding, so the density becomes the Gamma factor times the chart coordinates and the
  -- recovered last coordinate.
  rw [dirichletCoordsToSimplex_of_mem (n := m + 2) (hn := by omega) hx, dirichletDensity]
  simpa using congrArg
    (fun t ↦ (Real.Gamma (∑ i, θ i) / ∏ i, Real.Gamma (θ i)) * t) hprod

/-- Helper for Definition 24.26: specializing the generic chart-density rewrite to the split-last
chart on the positive strip leaves only the target chart product and the terminal factor
`1 - share`. -/
private theorem splitLastTargetKernel_eq_of_mem_openStrip {m : ℕ}
    (θ : Fin (m + 2) → ℝ) {u : Fin m → ℝ} (hu : u ∈ dirichletChart (m + 1))
    {share : ℝ} (hshare : share ∈ Set.Ioc (0 : ℝ) 1) :
    dirichletDensity θ
        (dirichletCoordsToSimplex (m + 2) (by omega) (splitLastChartCoords (m := m) u share)) =
      (Real.Gamma (∑ i, θ i) / ∏ i, Real.Gamma (θ i)) *
        ((∏ i : Fin (m + 1),
            Real.rpow (splitLastChartCoords (m := m) u share i) (θ i.castSucc - 1)) *
          Real.rpow (1 - share) (θ (Fin.last (m + 1)) - 1)) := by
  have hmem :
      splitLastChartCoords (m := m) u share ∈ dirichletChart (m + 2) :=
    splitLastChartCoords_mem_dirichletChart (m := m) hu ⟨hshare.1.le, hshare.2⟩
  -- Proof comment: the generic chart-density companion applies directly, and the split-last chart
  -- sum is exactly the share parameter.
  rw [dirichletDensity_comp_dirichletCoordsToSimplex_eq_of_mem_chart (m := m) θ hmem]
  rw [sum_splitLastChartCoords]

/-- Helper for Definition 24.26: view a pair `(u, share)` as one ambient vector whose `castSucc`
coordinates are `u` and whose last coordinate is `share`. -/
private def splitLastAmbientOfPair {m : ℕ} (p : (Fin m → ℝ) × ℝ) : Fin (m + 1) → ℝ :=
  fun i ↦ Fin.lastCases p.2 p.1 i

/-- Helper for Definition 24.26: the ambient pair encoding recovers the prefix coordinates on
`castSucc`. -/
private theorem splitLastAmbientOfPair_castSucc {m : ℕ} (p : (Fin m → ℝ) × ℝ) (i : Fin m) :
    splitLastAmbientOfPair (m := m) p i.castSucc = p.1 i := by
  -- Proof comment: the ambient encoding stores the prefix function on the nonterminal
  -- coordinates.
  simp [splitLastAmbientOfPair]

/-- Helper for Definition 24.26: the ambient pair encoding recovers the share on the terminal
coordinate. -/
private theorem splitLastAmbientOfPair_last {m : ℕ} (p : (Fin m → ℝ) × ℝ) :
    splitLastAmbientOfPair (m := m) p (Fin.last m) = p.2 := by
  -- Proof comment: the last ambient coordinate is exactly the carried split-last share.
  simp [splitLastAmbientOfPair]

/-- Helper for Definition 24.26: the ambient pair encoding is measurable. -/
private theorem measurable_splitLastAmbientOfPair {m : ℕ} :
    Measurable (splitLastAmbientOfPair (m := m)) := by
  -- Proof comment: each ambient coordinate is either a prefix projection from the first factor or
  -- the carried last coordinate from the second factor.
  refine measurable_pi_lambda _ fun i ↦ ?_
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simpa [splitLastAmbientOfPair] using
      ((measurable_pi_apply j).comp measurable_fst)
  · simpa [splitLastAmbientOfPair] using measurable_snd

/-- Helper for Definition 24.26: splitting off the last coordinate gives a measurable equivalence
between pair space and the ambient `Fin (m + 1)` chart space. -/
private def splitLastPairEquiv (m : ℕ) : ((Fin m → ℝ) × ℝ) ≃ᵐ (Fin (m + 1) → ℝ) where
  toFun := splitLastAmbientOfPair (m := m)
  invFun := fun x ↦ ((fun i : Fin m ↦ x i.castSucc), x (Fin.last m))
  left_inv := by
    intro p
    ext i
    · simp [splitLastAmbientOfPair]
    · simp [splitLastAmbientOfPair]
  right_inv := by
    intro x
    ext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp [splitLastAmbientOfPair]
    · simp [splitLastAmbientOfPair]
  measurable_toFun := by
    -- Proof comment: each ambient coordinate is either a prefix projection or the carried last
    -- coordinate.
    simpa using measurable_splitLastAmbientOfPair (m := m)
  measurable_invFun := by
    -- Proof comment: the inverse simply projects the ambient vector to the prefix block and the
    -- last coordinate.
    simpa using
      (show Measurable (fun x : Fin (m + 1) → ℝ ↦
          ((fun i : Fin m ↦ x i.castSucc), x (Fin.last m))) by fun_prop)

/-- Helper for Definition 24.26: summing the ambient coordinates corresponding to a pair adds the
prefix block and the carried last coordinate. -/
private theorem sum_splitLastAmbientOfPair {m : ℕ} (p : (Fin m → ℝ) × ℝ) :
    ∑ i, splitLastPairEquiv m p i = (∑ i : Fin m, p.1 i) + p.2 := by
  -- Proof comment: `splitLastPairEquiv` stores the prefix block on `castSucc` and the carried
  -- scalar on the last coordinate, so the ambient sum splits accordingly.
  rw [Fin.sum_univ_castSucc]
  simp [splitLastPairEquiv, splitLastAmbientOfPair, add_comm, add_left_comm, add_assoc]

/-- Helper for Definition 24.26: transporting ambient volume through the inverse pair splitting
map yields the product volume on prefix coordinates and the last coordinate. -/
private theorem map_splitLastPairEquiv_symm_volume_eq_prod {m : ℕ} :
    Measure.map (splitLastPairEquiv m).symm (volume : Measure (Fin (m + 1) → ℝ)) =
      ((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) (Fin.last m)
  have hsplit :
      (splitLastPairEquiv m).symm = Prod.swap ∘ e := by
    -- Proof comment: `piFinSuccAbove` exposes the last coordinate first, and swapping the product
    -- factors puts the prefix block before the carried scalar.
    funext x
    ext i
    · simp [splitLastPairEquiv, Function.comp, e, Fin.init]
    · simp [splitLastPairEquiv, Function.comp, e]
  calc
    Measure.map (splitLastPairEquiv m).symm (volume : Measure (Fin (m + 1) → ℝ))
        = Measure.map Prod.swap (Measure.map e (volume : Measure (Fin (m + 1) → ℝ))) := by
            rw [hsplit, Measure.map_map measurable_swap e.measurable]
    _ = Measure.map Prod.swap (volume : Measure (ℝ × (Fin m → ℝ))) := by
            rw [(volume_preserving_piFinSuccAbove
              (fun _ : Fin (m + 1) ↦ ℝ) (Fin.last m)).map_eq]
    _ = Measure.map Prod.swap
          ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) := by
            rw [Measure.volume_eq_prod]
    _ = ((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)) := by
          simpa using
            (Measure.prod_swap (μ := (volume : Measure ℝ))
              (ν := (volume : Measure (Fin m → ℝ))))

/-- Helper for Definition 24.26: transporting product volume back through the pair equivalence
recovers ambient volume on the target chart coordinates. -/
private theorem map_splitLastPairEquiv_volume_prod_eq_volume {m : ℕ} :
    Measure.map (splitLastPairEquiv m)
      (((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ))) =
        (volume : Measure (Fin (m + 1) → ℝ)) := by
  calc
    Measure.map (splitLastPairEquiv m)
        (((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)))
        = Measure.map (splitLastPairEquiv m)
            (Measure.map (splitLastPairEquiv m).symm
              (volume : Measure (Fin (m + 1) → ℝ))) := by
                rw [map_splitLastPairEquiv_symm_volume_eq_prod]
    _ = Measure.map id (volume : Measure (Fin (m + 1) → ℝ)) := by
          rw [Measure.map_map (splitLastPairEquiv m).measurable
            (splitLastPairEquiv m).symm.measurable]
          simp [Function.comp]
    _ = (volume : Measure (Fin (m + 1) → ℝ)) := by simp

/-- Helper for Definition 24.26: the ambient scaling map multiplies the prefix coordinates by the
carried last coordinate and leaves the last coordinate unchanged. -/
private def splitLastScaleAmbient {m : ℕ} (x : Fin (m + 1) → ℝ) : Fin (m + 1) → ℝ :=
  fun i ↦ Fin.lastCases (x (Fin.last m)) (fun j : Fin m ↦ x j.castSucc * x (Fin.last m)) i

/-- Helper for Definition 24.26: `splitLastScaleAmbient` multiplies each prefix coordinate by the
ambient last coordinate. -/
private theorem splitLastScaleAmbient_castSucc {m : ℕ} (x : Fin (m + 1) → ℝ) (i : Fin m) :
    splitLastScaleAmbient (m := m) x i.castSucc = x i.castSucc * x (Fin.last m) := by
  -- Proof comment: by construction, the prefix part of the scaling map is just the product with
  -- the carried last coordinate.
  simp [splitLastScaleAmbient]

/-- Helper for Definition 24.26: `splitLastScaleAmbient` fixes the ambient last coordinate. -/
private theorem splitLastScaleAmbient_last {m : ℕ} (x : Fin (m + 1) → ℝ) :
    splitLastScaleAmbient (m := m) x (Fin.last m) = x (Fin.last m) := by
  -- Proof comment: the last coordinate is carried through unchanged by the scale step.
  simp [splitLastScaleAmbient]

/-- Helper for Definition 24.26: summing the scaled prefix block factors out the carried last
coordinate. -/
private theorem sum_splitLastScaleAmbient_castSucc {m : ℕ} (x : Fin (m + 1) → ℝ) :
    ∑ i : Fin m, splitLastScaleAmbient (m := m) x i.castSucc =
      x (Fin.last m) * ∑ i : Fin m, x i.castSucc := by
  -- Proof comment: every prefix term is the same scalar `x_last` times the original prefix
  -- coordinate, so the factor pulls out of the finite sum.
  simp_rw [splitLastScaleAmbient_castSucc]
  calc
    ∑ i : Fin m, x i.castSucc * x (Fin.last m)
        = (∑ i : Fin m, x i.castSucc) * x (Fin.last m) := by
            rw [Finset.sum_mul]
    _ = x (Fin.last m) * ∑ i : Fin m, x i.castSucc := by
          ring

/-- Helper for Definition 24.26: the ambient assembly step keeps the prefix coordinates and
rebuilds the last coordinate as the carried remainder. -/
private def splitLastAssembleAmbient {m : ℕ} (z : Fin (m + 1) → ℝ) : Fin (m + 1) → ℝ :=
  fun i ↦ Fin.lastCases (z (Fin.last m) - ∑ j : Fin m, z j.castSucc) (fun j : Fin m ↦ z j.castSucc) i

/-- Helper for Definition 24.26: the ambient assembly step leaves the prefix coordinates
unchanged. -/
private theorem splitLastAssembleAmbient_castSucc {m : ℕ} (z : Fin (m + 1) → ℝ) (i : Fin m) :
    splitLastAssembleAmbient (m := m) z i.castSucc = z i.castSucc := by
  -- Proof comment: the assembly map only modifies the terminal coordinate, not the prefix block.
  simp [splitLastAssembleAmbient]

/-- Helper for Definition 24.26: the ambient assembly step rebuilds the last coordinate by
subtracting the scaled prefix mass from the carried total mass. -/
private theorem splitLastAssembleAmbient_last {m : ℕ} (z : Fin (m + 1) → ℝ) :
    splitLastAssembleAmbient (m := m) z (Fin.last m) =
      z (Fin.last m) - ∑ i : Fin m, z i.castSucc := by
  -- Proof comment: the terminal coordinate stores the carried total after removing the prefix
  -- contribution.
  simp [splitLastAssembleAmbient]

-- Route correction: package `splitLastChartCoords` as one ambient same-space map before the
-- Jacobian step, so later change-of-variables lemmas do not have to mix pair transport with
-- derivative normalization.
/-- Helper for Definition 24.26: `splitLastChartCoords` factors as the ambient scale step followed
by the ambient assembly step. -/
private theorem splitLastChartAmbientFactorization {m : ℕ} (u : Fin m → ℝ) (share : ℝ) :
    splitLastAssembleAmbient (m := m)
        (splitLastScaleAmbient (m := m) (splitLastAmbientOfPair (m := m) (u, share))) =
      splitLastChartCoords (m := m) u share := by
  -- Proof comment: compare the two ambient vectors coordinatewise; on `castSucc` both give the
  -- scaled prefix block, and on the last coordinate both give the remaining share.
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [splitLastAssembleAmbient_castSucc, splitLastScaleAmbient_castSucc,
      splitLastChartCoords_castSucc, splitLastAmbientOfPair_castSucc,
      splitLastAmbientOfPair_last]
    ring
  · rw [splitLastAssembleAmbient_last, splitLastScaleAmbient_last,
      sum_splitLastScaleAmbient_castSucc, splitLastChartCoords_last,
      splitLastAmbientOfPair_last]
    simp_rw [splitLastAmbientOfPair_castSucc]
    ring

/-- Helper for Definition 24.26: the same split-last chart map on the transported pair space keeps
the scaled prefix block in the first factor and the scaled recovered remainder in the second
factor. -/
private def splitLastPairMap {m : ℕ} (p : (Fin m → ℝ) × ℝ) : (Fin m → ℝ) × ℝ :=
  ((fun i ↦ p.2 * p.1 i), p.2 * (1 - ∑ i, p.1 i))

/-- Helper for Definition 24.26: the pair-space scale step multiplies the prefix block by the
carried share and leaves the share itself unchanged. -/
private def splitLastPairScale {m : ℕ} (p : (Fin m → ℝ) × ℝ) : (Fin m → ℝ) × ℝ :=
  ((fun i ↦ p.2 * p.1 i), p.2)

/-- Helper for Definition 24.26: the pair-space assembly step subtracts the scaled prefix mass
from the carried total to rebuild the final chart coordinate. -/
private def splitLastPairAssemble {m : ℕ} (q : (Fin m → ℝ) × ℝ) : (Fin m → ℝ) × ℝ :=
  (q.1, q.2 - ∑ i, q.1 i)

/-- Helper for Definition 24.26: the transported pair map and the ambient chart coordinates agree
under `splitLastAmbientOfPair`. -/
private theorem splitLastPairMap_ambient_eq {m : ℕ} (p : (Fin m → ℝ) × ℝ) :
    splitLastAmbientOfPair (m := m) (splitLastPairMap (m := m) p) =
      splitLastChartCoords (m := m) p.1 p.2 := by
  -- Proof comment: compare the ambient coordinates after transporting the pair map; the prefix
  -- block and the recovered last coordinate are exactly the chart formulas.
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp [splitLastPairMap, splitLastAmbientOfPair, splitLastChartCoords]
  · simp [splitLastPairMap, splitLastAmbientOfPair, splitLastChartCoords]

/-- Helper for Definition 24.26: the transported pair map factors as the pair-space assembly step
after the pair-space scale step. -/
private theorem splitLastPairMap_factorization {m : ℕ} (p : (Fin m → ℝ) × ℝ) :
    splitLastPairAssemble (m := m) (splitLastPairScale (m := m) p) =
      splitLastPairMap (m := m) p := by
  -- Proof comment: the pair-space factorization records the same two-stage chart computation as
  -- the ambient factorization, but in `prefix × last-coordinate` form.
  ext i
  · simp [splitLastPairMap, splitLastPairScale, splitLastPairAssemble]
  · simp [splitLastPairMap, splitLastPairScale, splitLastPairAssemble]
    rw [← Finset.mul_sum]
    ring

/-- Helper for Definition 24.26: summing the prefix coordinates is a continuous linear map. -/
private def splitLastPrefixSumCLM {m : ℕ} : (Fin m → ℝ) →L[ℝ] ℝ :=
  ∑ i, ContinuousLinearMap.proj i

/-- Helper for Definition 24.26: the pair-space assembly step is linear. -/
private def splitLastPairAssembleLinear {m : ℕ} :
    ((Fin m → ℝ) × ℝ) →L[ℝ] ((Fin m → ℝ) × ℝ) :=
  ContinuousLinearMap.prod
    (ContinuousLinearMap.fst ℝ (Fin m → ℝ) ℝ)
    (ContinuousLinearMap.snd ℝ (Fin m → ℝ) ℝ -
      (splitLastPrefixSumCLM (m := m)).comp (ContinuousLinearMap.fst ℝ (Fin m → ℝ) ℝ))

/-- Helper for Definition 24.26: the derivative of the pair-space scale step is the upper
triangular map given by the product rule on `share • prefix`. -/
private def splitLastPairScaleFDeriv {m : ℕ} (p : (Fin m → ℝ) × ℝ) :
    ((Fin m → ℝ) × ℝ) →L[ℝ] ((Fin m → ℝ) × ℝ) :=
  ContinuousLinearMap.prod
    (p.2 • ContinuousLinearMap.fst ℝ (Fin m → ℝ) ℝ +
      (ContinuousLinearMap.snd ℝ (Fin m → ℝ) ℝ).smulRight p.1)
    (ContinuousLinearMap.snd ℝ (Fin m → ℝ) ℝ)

/-- Helper for Definition 24.26: the pair-space scale step has the expected derivative everywhere.
-/
private theorem splitLastPairScale_hasFDerivAt {m : ℕ} (p : (Fin m → ℝ) × ℝ) :
    HasFDerivAt (splitLastPairScale (m := m)) (splitLastPairScaleFDeriv (m := m) p) p := by
  have hfst :
      HasFDerivAt (fun q : (Fin m → ℝ) × ℝ ↦ q.1)
        (ContinuousLinearMap.fst ℝ (Fin m → ℝ) ℝ) p :=
    hasFDerivAt_fst (p := p)
  have hsnd :
      HasFDerivAt (fun q : (Fin m → ℝ) × ℝ ↦ q.2)
        (ContinuousLinearMap.snd ℝ (Fin m → ℝ) ℝ) p :=
    hasFDerivAt_snd (p := p)
  have hscale :
      HasFDerivAt (fun q : (Fin m → ℝ) × ℝ ↦ q.2 • q.1)
        (p.2 • ContinuousLinearMap.fst ℝ (Fin m → ℝ) ℝ +
          (ContinuousLinearMap.snd ℝ (Fin m → ℝ) ℝ).smulRight p.1) p := by
    -- Proof comment: differentiate `share • prefix` by the product rule, treating the second
    -- coordinate as the scalar factor and the first coordinate as the vector factor.
    simpa using hsnd.smul hfst
  -- Proof comment: package the vector derivative and the scalar derivative into the product map.
  simpa [splitLastPairScale, splitLastPairScaleFDeriv] using hscale.prodMk hsnd

/-- Helper for Definition 24.26: the pair-space assembly step is differentiated by its underlying
constant linear map. -/
private theorem splitLastPairAssemble_hasFDerivAt {m : ℕ} (q : (Fin m → ℝ) × ℝ) :
    HasFDerivAt (splitLastPairAssemble (m := m)) (splitLastPairAssembleLinear (m := m)) q := by
  -- Proof comment: the assembly step is itself linear, so its derivative is constant and equal to
  -- the defining linear map.
  have hEq :
      splitLastPairAssemble (m := m) = splitLastPairAssembleLinear (m := m) := by
    funext z
    ext i
    · rfl
    · simp [splitLastPairAssemble, splitLastPairAssembleLinear, splitLastPrefixSumCLM,
        ContinuousLinearMap.comp_apply]
  simpa [hEq] using (splitLastPairAssembleLinear (m := m)).hasFDerivAt

/-- Helper for Definition 24.26: the standard product basis on `(Fin m → ℝ) × ℝ`, with the last
coordinate isolated as a `Unit` block, is convenient for block-determinant calculations. -/
private def splitLastPairBasis (m : ℕ) : Module.Basis (Fin m ⊕ Unit) ℝ ((Fin m → ℝ) × ℝ) :=
  (Pi.basisFun ℝ (Fin m)).prod (Module.Basis.singleton Unit ℝ)

/-- Helper for Definition 24.26: in the product basis, the derivative of the pair-space scale step
is the block upper-triangular matrix with diagonal blocks `share • 1` and `1`. -/
private theorem splitLastPairScaleFDeriv_matrix {m : ℕ} (p : (Fin m → ℝ) × ℝ) :
    LinearMap.toMatrix (splitLastPairBasis m) (splitLastPairBasis m)
      (splitLastPairScaleFDeriv (m := m) p).toLinearMap =
      Matrix.fromBlocks
        (p.2 • (1 : Matrix (Fin m) (Fin m) ℝ))
        (Matrix.of fun i (_ : Unit) ↦ p.1 i)
        0
        (1 : Matrix Unit Unit ℝ) := by
  -- Proof comment: the first block is `share • id` on the prefix coordinates, the upper-right
  -- column records the `dq_last • prefix` term, and the lower-left block vanishes because the
  -- scale step keeps the share coordinate unchanged.
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          by_cases h : i = j
          · subst h
            simp [splitLastPairBasis, splitLastPairScaleFDeriv, LinearMap.toMatrix_apply]
          · simp [splitLastPairBasis, splitLastPairScaleFDeriv, LinearMap.toMatrix_apply,
              Matrix.one_apply, h]
      | inr j =>
          simp [splitLastPairBasis, splitLastPairScaleFDeriv, LinearMap.toMatrix_apply]
  | inr i =>
      cases j with
      | inl j =>
          simp [splitLastPairBasis, splitLastPairScaleFDeriv, LinearMap.toMatrix_apply]
      | inr j =>
          simp [splitLastPairBasis, splitLastPairScaleFDeriv, LinearMap.toMatrix_apply]

/-- Helper for Definition 24.26: the pair-space scale derivative has determinant `share ^ m`. -/
private theorem splitLastPairScaleFDeriv_det {m : ℕ} (p : (Fin m → ℝ) × ℝ) :
    (splitLastPairScaleFDeriv (m := m) p).det = p.2 ^ m := by
  -- Proof comment: once the derivative is in block upper-triangular form, only the diagonal block
  -- `share • 1` contributes to the determinant.
  change LinearMap.det (splitLastPairScaleFDeriv (m := m) p).toLinearMap = p.2 ^ m
  rw [← LinearMap.det_toMatrix (splitLastPairBasis m), splitLastPairScaleFDeriv_matrix,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_one]
  simp

/-- Helper for Definition 24.26: in the product basis, the pair-space assembly map is block lower
triangular with identity diagonal blocks. -/
private theorem splitLastPairAssembleLinear_matrix {m : ℕ} :
    LinearMap.toMatrix (splitLastPairBasis m) (splitLastPairBasis m)
      (splitLastPairAssembleLinear (m := m)).toLinearMap =
      Matrix.fromBlocks
        (1 : Matrix (Fin m) (Fin m) ℝ)
        0
        (Matrix.of fun (_ : Unit) _ ↦ (-1 : ℝ))
        (1 : Matrix Unit Unit ℝ) := by
  -- Proof comment: the assembly map fixes the prefix block, subtracts their sum from the last
  -- coordinate, and therefore has only a lower-left correction row.
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          by_cases h : i = j
          · subst h
            simp [splitLastPairBasis, splitLastPairAssembleLinear, splitLastPrefixSumCLM,
              LinearMap.toMatrix_apply]
          · simp [splitLastPairBasis, splitLastPairAssembleLinear, splitLastPrefixSumCLM,
              LinearMap.toMatrix_apply, Matrix.one_apply, h]
      | inr j =>
          simp [splitLastPairBasis, splitLastPairAssembleLinear, splitLastPrefixSumCLM,
            LinearMap.toMatrix_apply]
  | inr i =>
      cases j with
      | inl j =>
          simp [splitLastPairBasis, splitLastPairAssembleLinear, splitLastPrefixSumCLM,
            LinearMap.toMatrix_apply]
      | inr j =>
          simp [splitLastPairBasis, splitLastPairAssembleLinear, splitLastPrefixSumCLM,
            LinearMap.toMatrix_apply]

/-- Helper for Definition 24.26: the pair-space assembly map has determinant `1`. -/
private theorem splitLastPairAssembleLinear_det {m : ℕ} :
    (splitLastPairAssembleLinear (m := m)).det = 1 := by
  -- Proof comment: the assembly map is block lower triangular with identity diagonal blocks, so
  -- it preserves Lebesgue volume.
  change LinearMap.det (splitLastPairAssembleLinear (m := m)).toLinearMap = 1
  rw [← LinearMap.det_toMatrix (splitLastPairBasis m), splitLastPairAssembleLinear_matrix,
    Matrix.det_fromBlocks_zero₁₂]
  simp

/-- Helper for Definition 24.26: the pair-space split-last chart map has derivative given by the
composition of the constant assembly map with the scale derivative. -/
private theorem splitLastPairMap_hasFDerivAt {m : ℕ} (p : (Fin m → ℝ) × ℝ) :
    HasFDerivAt (splitLastPairMap (m := m))
      ((splitLastPairAssembleLinear (m := m)).comp (splitLastPairScaleFDeriv (m := m) p)) p := by
  -- Proof comment: differentiate the factored map `assemble ∘ scale` by the chain rule; the
  -- assembly stage is linear and the scale stage carries the only point-dependent derivative.
  have hfac :
      splitLastPairAssemble (m := m) ∘ splitLastPairScale (m := m) = splitLastPairMap (m := m) := by
    funext q
    simpa [Function.comp] using splitLastPairMap_factorization (m := m) q
  simpa [hfac, Function.comp] using
    (splitLastPairAssemble_hasFDerivAt (m := m) (splitLastPairScale (m := m) p)).comp p
      (splitLastPairScale_hasFDerivAt (m := m) p)

/-- Helper for Definition 24.26: on the positive strip, the pair-space split-last chart map uses
the same Jacobian as its ambient derivative. -/
private theorem splitLastPairMap_hasFDerivWithinAt_positiveStrip {m : ℕ} {p : (Fin m → ℝ) × ℝ}
    (_hp : p.1 ∈ dirichletChart (m + 1) ∧ p.2 ∈ Set.Ioc (0 : ℝ) 1) :
    HasFDerivWithinAt (splitLastPairMap (m := m))
      ((splitLastPairAssembleLinear (m := m)).comp (splitLastPairScaleFDeriv (m := m) p))
      {q : (Fin m → ℝ) × ℝ | q.1 ∈ dirichletChart (m + 1) ∧ q.2 ∈ Set.Ioc (0 : ℝ) 1} p := by
  -- Proof comment: the ambient derivative from the chain rule restricts immediately to the
  -- positive strip.
  exact (splitLastPairMap_hasFDerivAt (m := m) p).hasFDerivWithinAt

/-- Helper for Definition 24.26: on the positive strip, the Jacobian determinant of the pair-space
split-last chart map is `share ^ m`. -/
private theorem splitLastPairMap_abs_det_fderiv {m : ℕ} {p : (Fin m → ℝ) × ℝ}
    (hp : p.2 ∈ Set.Ioc (0 : ℝ) 1) :
    |(((splitLastPairAssembleLinear (m := m)).comp
        (splitLastPairScaleFDeriv (m := m) p)).det)| = p.2 ^ m := by
  have hp_nonneg : 0 ≤ p.2 := hp.1.le
  change
    |LinearMap.det
        ((splitLastPairAssembleLinear (m := m)).toLinearMap.comp
          (splitLastPairScaleFDeriv (m := m) p).toLinearMap)| = p.2 ^ m
  rw [LinearMap.det_comp]
  simp [splitLastPairAssembleLinear_det, splitLastPairScaleFDeriv_det, hp_nonneg,
    abs_of_nonneg, pow_nonneg]

/-- Helper for Definition 24.26: in the target chart, a nonnegative vector with zero total mass
must be the zero vector. -/
private theorem zero_of_mem_dirichletChart_sum_eq_zero {m : ℕ} {v : Fin (m + 1) → ℝ}
    (hv : v ∈ dirichletChart (m + 2)) (hs : ∑ i, v i = 0) :
    v = 0 := by
  -- Proof comment: every coordinate is nonnegative and bounded above by the total sum, so when
  -- that total sum is `0`, each coordinate must vanish.
  ext i
  have hle : v i ≤ ∑ j : Fin (m + 1), v j := by
    exact Finset.single_le_sum (f := fun j : Fin (m + 1) ↦ v j)
      (fun j _ ↦ hv.1 j) (by simp)
  have hnonpos : v i ≤ 0 := by
    simpa [hs] using hle
  exact le_antisymm hnonpos (hv.1 i)

/-- Helper for Definition 24.26: transporting the target chart-side density through the pair
equivalence and then through `dirichletCoordsToSimplex` recovers the owner-side density measure.
-/
private theorem map_splitLastPairChartWithDensity_eq_dirichletDensityMeasure {m : ℕ}
    (θ : Fin (m + 2) → ℝ) :
    Measure.map (dirichletCoordsToSimplex (m + 2) (by omega) ∘ splitLastPairEquiv m)
      (((((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)).restrict
          ((splitLastPairEquiv m) ⁻¹' dirichletChart (m + 2))).withDensity
          (fun p ↦ ENNReal.ofReal
            (dirichletDensity θ
              (dirichletCoordsToSimplex (m + 2) (by omega) (splitLastPairEquiv m p)))))) =
      (((dirichletSimplexVolume (m + 2) (by omega)).withDensity
          (fun x ↦ ENNReal.ofReal (dirichletDensity θ x))) :
        Measure (dirichletSimplex (m + 2))) := by
  let e := splitLastPairEquiv m
  let μpair : Measure ((Fin m → ℝ) × ℝ) :=
    (((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)).restrict
      (e ⁻¹' dirichletChart (m + 2)))
  let chart : (Fin (m + 1) → ℝ) → dirichletSimplex (m + 2) :=
    dirichletCoordsToSimplex (m + 2) (by omega)
  let F : dirichletSimplex (m + 2) → ENNReal :=
    fun x ↦ ENNReal.ofReal (dirichletDensity θ x)
  have hbase :
      Measure.map e μpair =
        ((volume : Measure (Fin (m + 1) → ℝ)).restrict (dirichletChart (m + 2))) := by
    -- Proof comment: `splitLastPairEquiv` is a measurable equivalence whose pushforward sends the
    -- restricted pair volume exactly to the restricted target chart volume.
    rw [show μpair =
      (((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)).restrict
        (e ⁻¹' dirichletChart (m + 2))) by rfl]
    rw [← e.restrict_map (((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)))
      (dirichletChart (m + 2))]
    rw [map_splitLastPairEquiv_volume_prod_eq_volume (m := m)]
  have htarget_aemeas :
      AEMeasurable (fun x : Fin (m + 1) → ℝ ↦ F (chart x)) (Measure.map e μpair) := by
    -- Proof comment: after transporting to the ambient chart space, the target density is exactly
    -- the existing pulled-back Dirichlet density on the restricted chart measure.
    rw [hbase]
    simpa [F, chart] using
      aemeasurable_dirichletDensity_comp_dirichletCoordsToSimplex_restrict
        (n := m + 2) (hn := by omega) θ
  have hchart_aemeas_weighted :
      AEMeasurable chart
        ((((volume : Measure (Fin (m + 1) → ℝ)).restrict (dirichletChart (m + 2))).withDensity
          fun x ↦ F (chart x))) := by
    have hchart_aemeas :
        AEMeasurable chart
          (((volume : Measure (Fin (m + 1) → ℝ)).restrict (dirichletChart (m + 2)))) := by
      simpa [chart] using
        aemeasurable_dirichletCoordsToSimplex_restrict (n := m + 2) (hn := by omega)
    -- Proof comment: the chart map remains a.e.-measurable after inserting the target density.
    exact hchart_aemeas.mono_ac (withDensity_absolutelyContinuous _ _)
  have hmapWeighted :
      Measure.map e
        (μpair.withDensity fun p ↦ F (chart (e p))) =
        (((volume : Measure (Fin (m + 1) → ℝ)).restrict (dirichletChart (m + 2))).withDensity
          fun x ↦ F (chart x)) := by
    ext A hA
    have hindicator :
        (fun p : (Fin m → ℝ) × ℝ ↦ A.indicator (fun x ↦ F (chart x)) (e p)) =
          (e ⁻¹' A).indicator (fun p ↦ F (chart (e p))) := by
      -- Proof comment: after precomposing the target indicator by the pair equivalence, the set
      -- restriction is exactly the ambient preimage `e ⁻¹' A`.
      funext p
      by_cases hp : e p ∈ A <;> simp [hp]
    rw [Measure.map_apply e.measurable hA, withDensity_apply' _ (e ⁻¹' A), withDensity_apply' _ A]
    rw [← hbase, ← lintegral_indicator hA]
    rw [lintegral_map' (htarget_aemeas.indicator hA) e.measurable.aemeasurable]
    rw [hindicator, lintegral_indicator (hA.preimage e.measurable)]
  have hchart_aemeas_map :
      AEMeasurable chart
        (Measure.map e (μpair.withDensity fun p ↦ F (chart (e p)))) := by
    rw [hmapWeighted]
    exact hchart_aemeas_weighted
  -- Proof comment: first move the weighted target chart measure from pair space to ambient chart
  -- coordinates, then invoke the generic chart-pushforward theorem.
  calc
    Measure.map (chart ∘ e) (μpair.withDensity fun p ↦ F (chart (e p)))
        = Measure.map chart (Measure.map e (μpair.withDensity fun p ↦ F (chart (e p)))) := by
            symm
            exact AEMeasurable.map_map_of_aemeasurable hchart_aemeas_map
              e.measurable.aemeasurable
    _ = Measure.map chart
          ((((volume : Measure (Fin (m + 1) → ℝ)).restrict (dirichletChart (m + 2))).withDensity
            fun x ↦ F (chart x))) := by
            rw [hmapWeighted]
    _ = (((dirichletSimplexVolume (m + 2) (by omega)).withDensity
            (fun x ↦ ENNReal.ofReal (dirichletDensity θ x))) :
          Measure (dirichletSimplex (m + 2))) := by
            simpa [F, chart] using
              map_dirichletCoordsToSimplex_chartWithDensity_eq_dirichletDensityMeasure
                (n := m + 2) (hn := by omega) θ

/-- Helper for Definition 24.26: the transported positive strip in pair space consists of chart
points for `Δ_(m+2)` with strictly positive total chart mass. -/
private def splitLastPositiveStrip (m : ℕ) : Set ((Fin m → ℝ) × ℝ) :=
  {p | p.1 ∈ dirichletChart (m + 1) ∧ p.2 ∈ Set.Ioc (0 : ℝ) 1}

/-- Helper for Definition 24.26: on the positive strip, the owner split-last assembly agrees with
the target chart map written in the transported pair coordinates. -/
private theorem
    ownerSplitLastNormalizeAssembly_prefixPair_eq_targetPairChart_of_mem_positiveStrip {m : ℕ}
    (hm : 1 ≤ m) {p : (Fin m → ℝ) × ℝ} (hp : p ∈ splitLastPositiveStrip m) :
    ownerSplitLastNormalizeAssembly (m := m)
      (dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) p.1, p.2) =
        dirichletCoordsToSimplex (m + 2) (by omega)
          (splitLastPairEquiv m (splitLastPairMap (m := m) p)) := by
  -- Proof comment: the existing owner-level chart companion already identifies the left-hand side
  -- with the ambient split-last chart; `splitLastPairMap_ambient_eq` is exactly the transport to
  -- pair-space spelling.
  have hchart :
      ownerSplitLastNormalizeAssembly (m := m)
        (dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) p.1, p.2) =
          dirichletCoordsToSimplex (m + 2) (by omega)
            (splitLastChartCoords (m := m) p.1 p.2) := by
    exact ownerSplitLastNormalizeAssembly_chartSpec (m := m) hm hp.1 ⟨hp.2.1.le, hp.2.2⟩
  simpa [splitLastPairEquiv] using hchart.trans <| by rw [splitLastPairMap_ambient_eq]

/-- Helper for Definition 24.26: the transported pair map sends the positive strip exactly to the
target chart points with positive total mass. -/
private theorem splitLastPairMap_image_positiveStrip {m : ℕ} :
    splitLastPairMap '' splitLastPositiveStrip m =
      {q : (Fin m → ℝ) × ℝ |
        splitLastPairEquiv m q ∈ dirichletChart (m + 2) ∧
          0 < ∑ i, splitLastPairEquiv m q i} := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hchart :
        splitLastChartCoords (m := m) p.1 p.2 ∈ dirichletChart (m + 2) ∧
          0 < ∑ i, splitLastChartCoords (m := m) p.1 p.2 i := by
      have himageSet :
          (fun z : (Fin m → ℝ) × ℝ ↦ splitLastChartCoords (m := m) z.1 z.2) ''
              splitLastPositiveStrip m =
            {v : Fin (m + 1) → ℝ | v ∈ dirichletChart (m + 2) ∧ 0 < ∑ i, v i} := by
        simpa [splitLastPositiveStrip] using splitLastChartImage_positiveStrip (m := m)
      have himage :
          splitLastChartCoords (m := m) p.1 p.2 ∈
            (fun z : (Fin m → ℝ) × ℝ ↦ splitLastChartCoords (m := m) z.1 z.2) ''
              splitLastPositiveStrip m := ⟨p, hp, rfl⟩
      rw [himageSet] at himage
      exact himage
    simpa [splitLastPairEquiv, splitLastPairMap_ambient_eq] using hchart
  · intro hq
    have himageSet :
        (fun z : (Fin m → ℝ) × ℝ ↦ splitLastChartCoords (m := m) z.1 z.2) ''
            splitLastPositiveStrip m =
          {v : Fin (m + 1) → ℝ | v ∈ dirichletChart (m + 2) ∧ 0 < ∑ i, v i} := by
      simpa [splitLastPositiveStrip] using splitLastChartImage_positiveStrip (m := m)
    have hchart :
        splitLastPairEquiv m q ∈
          (fun z : (Fin m → ℝ) × ℝ ↦ splitLastChartCoords (m := m) z.1 z.2) ''
            splitLastPositiveStrip m := by
      rw [himageSet]
      exact hq
    rcases hchart with ⟨p, hp, hpq⟩
    refine ⟨p, hp, ?_⟩
    apply (splitLastPairEquiv m).injective
    simpa [splitLastPairEquiv, splitLastPairMap_ambient_eq] using hpq

/-- Helper for Definition 24.26: restricting product volume to the positive strip is exactly the
product of the two coordinate restrictions. -/
private theorem volumeProd_restrict_splitLastPositiveStrip {m : ℕ} :
    ((((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)).restrict
        (splitLastPositiveStrip m))) =
      (((volume : Measure (Fin m → ℝ)).restrict (dirichletChart (m + 1))).prod
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))) := by
  -- Proof comment: the positive strip is the product of the prefix chart and the Beta support,
  -- so the restricted ambient product measure is the product of the two restricted factors.
  symm
  simpa [splitLastPositiveStrip] using
    (Measure.prod_restrict (μ := (volume : Measure (Fin m → ℝ))) (ν := (volume : Measure ℝ))
      (dirichletChart (m + 1)) (Set.Ioc (0 : ℝ) 1))

/-- Helper for Definition 24.26: the prefix Dirichlet chart source times the split-last Beta law
is one positive-strip `withDensity` measure in pair space. -/
private theorem prodPrefixDirichletChartBeta_eq_positiveStripWithDensity {m : ℕ}
    (hm : 1 ≤ m) (θ : Fin (m + 2) → ℝ) :
    ((((volume : Measure (Fin m → ℝ)).restrict (dirichletChart (m + 1))).withDensity
        (fun u ↦ ENNReal.ofReal
          (dirichletDensity (fun i : Fin (m + 1) ↦ θ i.castSucc)
            (dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) u)))).prod
      (((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)).withDensity
        (betaPDF (∑ i : Fin (m + 1), θ i.castSucc) (θ (Fin.last (m + 1)))))) =
      (((((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)).restrict
          (splitLastPositiveStrip m)).withDensity
        (fun p ↦ ENNReal.ofReal
          (dirichletDensity (fun i : Fin (m + 1) ↦ θ i.castSucc)
            (dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) p.1)) *
          betaPDF (∑ i : Fin (m + 1), θ i.castSucc) (θ (Fin.last (m + 1))) p.2))) := by
  have hprefix_aemeas :
      AEMeasurable
        (fun u : Fin m → ℝ ↦ ENNReal.ofReal
          (dirichletDensity (fun i : Fin (m + 1) ↦ θ i.castSucc)
            (dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) u)))
        (((volume : Measure (Fin m → ℝ)).restrict (dirichletChart (m + 1)))) := by
    -- Proof comment: the prefix Dirichlet chart density is already available as the restricted
    -- chart-side pullback of the simplex density.
    simpa using
      aemeasurable_dirichletDensity_comp_dirichletCoordsToSimplex_restrict
        (n := m + 1) (hn := Nat.succ_le_succ hm) (fun i : Fin (m + 1) ↦ θ i.castSucc)
  have hbeta_meas :
      Measurable (betaPDF (∑ i : Fin (m + 1), θ i.castSucc) (θ (Fin.last (m + 1)))) := by
    -- Proof comment: the Beta density is the standard measurable `ℝ≥0∞` weight on `(0, 1]`.
    simpa [betaPDF] using
      ENNReal.measurable_ofReal.comp
        (measurable_betaPDFReal (∑ i : Fin (m + 1), θ i.castSucc) (θ (Fin.last (m + 1))))
  calc
    ((((volume : Measure (Fin m → ℝ)).restrict (dirichletChart (m + 1))).withDensity
          (fun u ↦ ENNReal.ofReal
            (dirichletDensity (fun i : Fin (m + 1) ↦ θ i.castSucc)
              (dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) u)))).prod
        (((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)).withDensity
          (betaPDF (∑ i : Fin (m + 1), θ i.castSucc) (θ (Fin.last (m + 1))))))
        =
        ((((volume : Measure (Fin m → ℝ)).restrict (dirichletChart (m + 1))).prod
            ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))).withDensity
          (fun p ↦ ENNReal.ofReal
            (dirichletDensity (fun i : Fin (m + 1) ↦ θ i.castSucc)
              (dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) p.1)) *
            betaPDF (∑ i : Fin (m + 1), θ i.castSucc) (θ (Fin.last (m + 1))) p.2)) := by
          rw [prod_withDensity₀ hprefix_aemeas hbeta_meas.aemeasurable]
    _ = (((((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)).restrict
            (splitLastPositiveStrip m)).withDensity
          (fun p ↦ ENNReal.ofReal
            (dirichletDensity (fun i : Fin (m + 1) ↦ θ i.castSucc)
              (dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) p.1)) *
            betaPDF (∑ i : Fin (m + 1), θ i.castSucc) (θ (Fin.last (m + 1))) p.2))) := by
          rw [← volumeProd_restrict_splitLastPositiveStrip]

/-- Helper for Definition 24.26: mapping the normalized positive-strip source through the prefix
chart recovers the owner-side `Dirichlet(prefix) × Beta` source. -/
private theorem mapPrefixPairChart_positiveStripSource_eq_dirichletPrefixBetaProd {m : ℕ}
    (hm : 1 ≤ m) (θ : Fin (m + 2) → ℝ) :
    Measure.map
      (fun p : (Fin m → ℝ) × ℝ ↦
        (dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) p.1, p.2))
      (((((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)).restrict
          (splitLastPositiveStrip m)).withDensity
        (fun p ↦ ENNReal.ofReal
          (dirichletDensity (fun i : Fin (m + 1) ↦ θ i.castSucc)
            (dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) p.1)) *
          betaPDF (∑ i : Fin (m + 1), θ i.castSucc) (θ (Fin.last (m + 1))) p.2))) =
      ((((dirichletSimplexVolume (m + 1) (Nat.succ_le_succ hm)).withDensity
          (fun x ↦ ENNReal.ofReal
            (dirichletDensity (fun i : Fin (m + 1) ↦ θ i.castSucc) x)) :
          Measure (dirichletSimplex (m + 1)))).prod
        (betaMeasure (∑ i : Fin (m + 1), θ i.castSucc) (θ (Fin.last (m + 1))))) := by
  let μPrefix : Measure (Fin m → ℝ) :=
    (((volume : Measure (Fin m → ℝ)).restrict (dirichletChart (m + 1))).withDensity
      (fun u ↦ ENNReal.ofReal
        (dirichletDensity (fun i : Fin (m + 1) ↦ θ i.castSucc)
          (dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) u))))
  let μShare : Measure ℝ :=
    (((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)).withDensity
      (betaPDF (∑ i : Fin (m + 1), θ i.castSucc) (θ (Fin.last (m + 1)))))
  let prefixChart : (Fin m → ℝ) → dirichletSimplex (m + 1) :=
    dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm)
  let pairChart : (Fin m → ℝ) × ℝ → dirichletSimplex (m + 1) × ℝ :=
    fun p ↦ (prefixChart p.1, p.2)
  have hsource :
      μPrefix.prod μShare =
        (((((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)).restrict
            (splitLastPositiveStrip m)).withDensity
          (fun p ↦ ENNReal.ofReal
            (dirichletDensity (fun i : Fin (m + 1) ↦ θ i.castSucc)
              (dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) p.1)) *
            betaPDF (∑ i : Fin (m + 1), θ i.castSucc) (θ (Fin.last (m + 1))) p.2))) := by
    -- Proof comment: this is exactly the packaged positive-strip source normalization.
    simpa [μPrefix, μShare] using
      prodPrefixDirichletChartBeta_eq_positiveStripWithDensity (m := m) hm θ
  -- Proof comment: once the strip source is packaged as a product, push the first factor through
  -- the prefix chart and leave the Beta share unchanged.
  calc
    Measure.map pairChart
        (((((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)).restrict
            (splitLastPositiveStrip m)).withDensity
          (fun p ↦ ENNReal.ofReal
            (dirichletDensity (fun i : Fin (m + 1) ↦ θ i.castSucc)
              (dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) p.1)) *
            betaPDF (∑ i : Fin (m + 1), θ i.castSucc) (θ (Fin.last (m + 1))) p.2)))
        = Measure.map pairChart (μPrefix.prod μShare) := by rw [hsource]
    _ = (Measure.map prefixChart μPrefix).prod (Measure.map id μShare) := by
          simpa [pairChart, prefixChart, Prod.map] using
            (Measure.map_prod_map (μa := μPrefix) (μc := μShare)
              (f := prefixChart) (g := id)
              (measurable_dirichletCoordsToSimplex (Nat.succ_le_succ hm))
              measurable_id).symm
    _ = (Measure.map prefixChart μPrefix).prod μShare := by rw [Measure.map_id]
    _ = ((((dirichletSimplexVolume (m + 1) (Nat.succ_le_succ hm)).withDensity
            (fun x ↦ ENNReal.ofReal
              (dirichletDensity (fun i : Fin (m + 1) ↦ θ i.castSucc) x))) :
            Measure (dirichletSimplex (m + 1))).prod μShare) := by
            -- Proof comment: unfold the local source names and rewrite the first factor by the
            -- established chart-pushforward theorem.
            congr 1
            simpa [μPrefix, prefixChart] using
              map_dirichletCoordsToSimplex_chartWithDensity_eq_dirichletDensityMeasure
                (n := m + 1) (hn := Nat.succ_le_succ hm)
                (fun i : Fin (m + 1) ↦ θ i.castSucc)
    _ = ((((dirichletSimplexVolume (m + 1) (Nat.succ_le_succ hm)).withDensity
            (fun x ↦ ENNReal.ofReal
              (dirichletDensity (fun i : Fin (m + 1) ↦ θ i.castSucc) x))) :
            Measure (dirichletSimplex (m + 1))).prod
          (betaMeasure (∑ i : Fin (m + 1), θ i.castSucc) (θ (Fin.last (m + 1))))) := by
            -- Proof comment: the second factor is just the Beta law written as a restricted
            -- `withDensity`.
            congr 1
            simpa [μShare] using
              withDensity_restrict_Ioc_betaPDF_eq_betaMeasure
                (∑ i : Fin (m + 1), θ i.castSucc) (θ (Fin.last (m + 1)))

/-- Helper for Definition 24.26: the boundary slice `share = 1` has zero restricted pair-volume on
the positive strip. -/
private theorem measure_restrict_splitLastPositiveStrip_share_eq_one_zero {m : ℕ} :
    ((((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)).restrict
        (splitLastPositiveStrip m)) {p : (Fin m → ℝ) × ℝ | p.2 = (1 : ℝ)}) = 0 := by
  have hmeas :
      MeasurableSet {p : (Fin m → ℝ) × ℝ | p.2 = (1 : ℝ)} := by
    exact measurableSet_eq_fun measurable_snd measurable_const
  have hnull :
      (((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ))
        (Set.univ ×ˢ ({1} : Set ℝ))) = 0 := by
    rw [Measure.prod_prod]
    simp
  rw [Measure.restrict_apply hmeas]
  exact measure_mono_null
    (fun p hp ↦ by
      exact ⟨by simp, hp.1⟩)
    hnull

/-- Helper for Definition 24.26: on the prefix chart, the split-last chart coordinates are the
carried share times the prefix simplex coordinates. -/
private theorem splitLastChartCoords_eq_share_mul_prefixCoords {m : ℕ}
    (hm : 1 ≤ m) {u : Fin m → ℝ} (hu : u ∈ dirichletChart (m + 1)) (share : ℝ)
    (i : Fin (m + 1)) :
    splitLastChartCoords (m := m) u share i =
      share * ((dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) u) i) := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · -- Proof comment: on the nonterminal coordinates, the chart map keeps the prefix coordinates,
    -- and `splitLastChartCoords` just multiplies them by the carried share.
    have hprefix :
        (dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) u) j.castSucc = u j := by
      rw [dirichletCoordsToSimplex_of_mem (n := m + 1) (hn := Nat.succ_le_succ hm) hu]
      simpa using dirichletCoordVector_castSucc (n := m + 1) (hn := Nat.succ_le_succ hm)
        (x := u) (i := j)
    rw [hprefix, splitLastChartCoords_castSucc]
  · -- Proof comment: on the last prefix coordinate, the chart map recovers the remainder
    -- `1 - ∑ u`, which is again scaled by the carried share.
    have hprefix :
        (dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) u) (Fin.last m) =
          1 - ∑ j, u j := by
      rw [dirichletCoordsToSimplex_of_mem (n := m + 1) (hn := Nat.succ_le_succ hm) hu]
      simpa using dirichletCoordVector_last (n := m + 1) (hn := Nat.succ_le_succ hm) (x := u)
    rw [hprefix, splitLastChartCoords_last]

/-- Helper for Definition 24.26: on the open strip, the split-last chart product factors into one
shared `share` power and the prefix Dirichlet chart product. -/
private theorem splitLastChartProduct_factor_of_mem_openStrip {m : ℕ}
    (hm : 1 ≤ m) (θ : Fin (m + 2) → ℝ) {u : Fin m → ℝ}
    (hu : u ∈ dirichletChart (m + 1)) {share : ℝ} (hshare : share ∈ Set.Ioo (0 : ℝ) 1) :
    ∏ i : Fin (m + 1), Real.rpow (splitLastChartCoords (m := m) u share i) (θ i.castSucc - 1) =
      Real.rpow share ((∑ i : Fin (m + 1), θ i.castSucc) - (m + 1 : ℝ)) *
        ∏ i : Fin (m + 1),
          Real.rpow ((dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) u) i)
            (θ i.castSucc - 1) := by
  have hfactor :
      ∀ i : Fin (m + 1),
        Real.rpow (splitLastChartCoords (m := m) u share i) (θ i.castSucc - 1) =
          Real.rpow share (θ i.castSucc - 1) *
            Real.rpow ((dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) u) i)
              (θ i.castSucc - 1) := by
    intro i
    -- Proof comment: each split-last chart coordinate is `share` times the corresponding prefix
    -- simplex coordinate, so `Real.mul_rpow` splits the factor pointwise.
    rw [splitLastChartCoords_eq_share_mul_prefixCoords hm hu share i]
    simpa using
      (Real.mul_rpow hshare.1.le ((dirichletCoordsToSimplex
        (m + 1) (Nat.succ_le_succ hm) u).2.1 i) (z := θ i.castSucc - 1))
  have hshare_prod :
      ∏ i : Fin (m + 1), Real.rpow share (θ i.castSucc - 1) =
        Real.rpow share (∑ i : Fin (m + 1), (θ i.castSucc - 1)) := by
    -- Proof comment: the repeated `share` factors combine into one power by iterating
    -- `Real.rpow_add` over the finite product.
    classical
    refine Finset.induction_on (s := (Finset.univ : Finset (Fin (m + 1)))) ?_ ?_
    · simp
    · intro i s hi hs
      rw [Finset.prod_insert hi, Finset.sum_insert hi, hs]
      simpa using
        (Real.rpow_add hshare.1 (θ i.castSucc - 1) (∑ x ∈ s, (θ x.castSucc - 1))).symm
  have hexp :
      (∑ i : Fin (m + 1), (θ i.castSucc - 1)) =
        (∑ i : Fin (m + 1), θ i.castSucc) - (m + 1 : ℝ) := by
    -- Proof comment: summing the shifted exponents subtracts one contribution for each of the
    -- `m + 1` prefix coordinates.
    rw [Finset.sum_sub_distrib]
    simp
  -- Proof comment: after the pointwise split, the two products separate and the `share` factors
  -- collapse to the combined exponent.
  calc
    ∏ i : Fin (m + 1), Real.rpow (splitLastChartCoords (m := m) u share i) (θ i.castSucc - 1)
      = ∏ i : Fin (m + 1),
          (Real.rpow share (θ i.castSucc - 1) *
            Real.rpow ((dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) u) i)
              (θ i.castSucc - 1)) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            exact hfactor i
    _ = (∏ i : Fin (m + 1), Real.rpow share (θ i.castSucc - 1)) *
          ∏ i : Fin (m + 1),
            Real.rpow ((dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) u) i)
              (θ i.castSucc - 1) := by
            rw [Finset.prod_mul_distrib]
    _ = Real.rpow share (∑ i : Fin (m + 1), (θ i.castSucc - 1)) *
          ∏ i : Fin (m + 1),
            Real.rpow ((dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) u) i)
              (θ i.castSucc - 1) := by
            rw [hshare_prod]
    _ = Real.rpow share ((∑ i : Fin (m + 1), θ i.castSucc) - (m + 1 : ℝ)) *
          ∏ i : Fin (m + 1),
            Real.rpow ((dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) u) i)
              (θ i.castSucc - 1) := by
            rw [hexp]

/-- Helper for Definition 24.26: on the open strip, the Jacobian-weighted target chart density
factors as the prefix Dirichlet density times the Beta kernel. -/
private theorem splitLastChartKernel_factor_withPrefixDensity {m : ℕ}
    (hm : 1 ≤ m) (θ : Fin (m + 2) → ℝ) (hθ : ∀ i, 0 < θ i)
    {u : Fin m → ℝ} (hu : u ∈ dirichletChart (m + 1))
    {share : ℝ} (hshare : share ∈ Set.Ioo (0 : ℝ) 1) :
    (share ^ m) *
        dirichletDensity θ
          (dirichletCoordsToSimplex (m + 2) (by omega) (splitLastChartCoords (m := m) u share)) =
      dirichletDensity (fun i : Fin (m + 1) ↦ θ i.castSucc)
          (dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) u) *
        ((Real.Gamma ((∑ i : Fin (m + 1), θ i.castSucc) + θ (Fin.last (m + 1))) /
            (Real.Gamma (∑ i : Fin (m + 1), θ i.castSucc) * Real.Gamma (θ (Fin.last (m + 1))))) *
          Real.rpow share ((∑ i : Fin (m + 1), θ i.castSucc) - 1) *
          Real.rpow (1 - share) (θ (Fin.last (m + 1)) - 1)) := by
  have hprefixThetaPos : 0 < ∑ i : Fin (m + 1), θ i.castSucc := by
    let i0 : Fin (m + 1) := 0
    have hi0 : 0 < θ i0.castSucc := hθ i0.castSucc
    have hle : θ i0.castSucc ≤ ∑ i : Fin (m + 1), θ i.castSucc := by
      exact Finset.single_le_sum (f := fun i : Fin (m + 1) ↦ θ i.castSucc)
        (by
          intro i hi
          exact (hθ i.castSucc).le)
        (by simp [i0])
    exact lt_of_lt_of_le hi0 hle
  have hGammaPrefix_ne : Real.Gamma (∑ i : Fin (m + 1), θ i.castSucc) ≠ 0 :=
    (Real.Gamma_pos_of_pos hprefixThetaPos).ne'
  have hGammaLast_ne : Real.Gamma (θ (Fin.last (m + 1))) ≠ 0 :=
    (Real.Gamma_pos_of_pos (hθ (Fin.last (m + 1)))).ne'
  have hGammaPrefixProd_ne :
      ∏ i : Fin (m + 1), Real.Gamma (θ i.castSucc) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro i hi
    exact (Real.Gamma_pos_of_pos (hθ i.castSucc)).ne'
  have hsumTheta :
      ∑ i : Fin (m + 2), θ i =
        (∑ i : Fin (m + 1), θ i.castSucc) + θ (Fin.last (m + 1)) := by
    simpa using Fin.sum_univ_castSucc (f := fun i : Fin (m + 2) ↦ θ i)
  have hprodGamma :
      ∏ i : Fin (m + 2), Real.Gamma (θ i) =
        (∏ i : Fin (m + 1), Real.Gamma (θ i.castSucc)) *
          Real.Gamma (θ (Fin.last (m + 1))) := by
    simpa using
      Fin.prod_univ_castSucc (f := fun i : Fin (m + 2) ↦ Real.Gamma (θ i))
  have hsharePow :
      (share : ℝ) ^ m *
          Real.rpow share ((∑ i : Fin (m + 1), θ i.castSucc) - (m + 1 : ℝ)) =
        Real.rpow share ((∑ i : Fin (m + 1), θ i.castSucc) - 1) := by
    -- Proof comment: convert the Jacobian factor `share ^ m` into an `rpow`, then merge the two
    -- `share` exponents into the Beta exponent.
    calc
      (share : ℝ) ^ m * Real.rpow share ((∑ i : Fin (m + 1), θ i.castSucc) - (m + 1 : ℝ))
          = share ^ (m : ℝ) *
              Real.rpow share ((∑ i : Fin (m + 1), θ i.castSucc) - (m + 1 : ℝ)) := by
                rw [Real.rpow_natCast]
      _ = Real.rpow share ((m : ℝ) + ((∑ i : Fin (m + 1), θ i.castSucc) - (m + 1 : ℝ))) := by
            simpa using
              (Real.rpow_add hshare.1 (m : ℝ)
                ((∑ i : Fin (m + 1), θ i.castSucc) - (m + 1 : ℝ))).symm
      _ = Real.rpow share ((∑ i : Fin (m + 1), θ i.castSucc) - 1) := by
            congr 1
            ring
  have hconst :
      Real.Gamma ((∑ i : Fin (m + 1), θ i.castSucc) + θ (Fin.last (m + 1))) /
          ((∏ i : Fin (m + 1), Real.Gamma (θ i.castSucc)) *
            Real.Gamma (θ (Fin.last (m + 1)))) =
        (Real.Gamma (∑ i : Fin (m + 1), θ i.castSucc) /
            ∏ i : Fin (m + 1), Real.Gamma (θ i.castSucc)) *
          (Real.Gamma ((∑ i : Fin (m + 1), θ i.castSucc) + θ (Fin.last (m + 1))) /
            (Real.Gamma (∑ i : Fin (m + 1), θ i.castSucc) *
              Real.Gamma (θ (Fin.last (m + 1))))) := by
    -- Proof comment: split the total Gamma normalization constant into the prefix Dirichlet
    -- constant and the remaining Beta normalizing factor.
    field_simp [hGammaPrefix_ne, hGammaLast_ne, hGammaPrefixProd_ne]
  -- Proof comment: rewrite the target density in split-last chart coordinates, factor the
  -- prefix chart product, and then normalize the Gamma and `share` factors.
  rw [splitLastTargetKernel_eq_of_mem_openStrip θ hu ⟨hshare.1, hshare.2.le⟩,
    splitLastChartProduct_factor_of_mem_openStrip hm θ hu hshare, dirichletDensity, hsumTheta,
    hprodGamma, hconst]
  let prefixConst : ℝ :=
    Real.Gamma (∑ i : Fin (m + 1), θ i.castSucc) /
      ∏ i : Fin (m + 1), Real.Gamma (θ i.castSucc)
  let betaConst : ℝ :=
    Real.Gamma ((∑ i : Fin (m + 1), θ i.castSucc) + θ (Fin.last (m + 1))) /
      (Real.Gamma (∑ i : Fin (m + 1), θ i.castSucc) * Real.Gamma (θ (Fin.last (m + 1))))
  let prefixProd : ℝ :=
    ∏ i : Fin (m + 1),
      Real.rpow ((dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) u) i)
        (θ i.castSucc - 1)
  let lastPow : ℝ := Real.rpow (1 - share) (θ (Fin.last (m + 1)) - 1)
  let shareProd : ℝ :=
    Real.rpow share ((∑ i : Fin (m + 1), θ i.castSucc) - (m + 1 : ℝ))
  let shareBeta : ℝ := Real.rpow share ((∑ i : Fin (m + 1), θ i.castSucc) - 1)
  have hscaled :
      prefixConst * prefixProd * betaConst * ((share : ℝ) ^ m * shareProd) * lastPow =
        prefixConst * prefixProd * betaConst * shareBeta * lastPow := by
    exact congrArg (fun t : ℝ ↦ prefixConst * prefixProd * betaConst * t * lastPow) hsharePow
  simpa [prefixConst, betaConst, prefixProd, lastPow, shareProd, shareBeta,
    mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- Helper for Definition 24.26: on the open strip, the Jacobian-weighted target pair density
matches the packaged prefix-Dirichlet/Beta source density exactly. -/
private theorem splitLastPairWeightedTarget_eq_source_of_mem_openStrip {m : ℕ}
    (hm : 1 ≤ m) (θ : Fin (m + 2) → ℝ) (hθ : ∀ i, 0 < θ i)
    {p : (Fin m → ℝ) × ℝ} (hp : p ∈ splitLastPositiveStrip m) (hp_lt : p.2 < 1) :
    ENNReal.ofReal
        |(((splitLastPairAssembleLinear (m := m)).comp
            (splitLastPairScaleFDeriv (m := m) p)).det)| *
      ENNReal.ofReal
        (dirichletDensity θ
          (dirichletCoordsToSimplex (m + 2) (by omega)
            (splitLastPairEquiv m (splitLastPairMap (m := m) p)))) =
    ENNReal.ofReal
        (dirichletDensity (fun i : Fin (m + 1) ↦ θ i.castSucc)
          (dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) p.1)) *
      betaPDF (∑ i : Fin (m + 1), θ i.castSucc) (θ (Fin.last (m + 1))) p.2 := by
  have hpIoc : p.2 ∈ Set.Ioc (0 : ℝ) 1 := ⟨hp.2.1, hp_lt.le⟩
  have hprefixThetaPos : 0 < ∑ i : Fin (m + 1), θ i.castSucc := by
    let i0 : Fin (m + 1) := 0
    have hi0 : 0 < θ i0.castSucc := hθ i0.castSucc
    have hle : θ i0.castSucc ≤ ∑ i : Fin (m + 1), θ i.castSucc := by
      exact Finset.single_le_sum (f := fun i : Fin (m + 1) ↦ θ i.castSucc)
        (by
          intro i hi
          exact (hθ i.castSucc).le)
        (by simp [i0])
    exact lt_of_lt_of_le hi0 hle
  have hbetaKernel_nonneg :
      0 ≤
        ((Real.Gamma ((∑ i : Fin (m + 1), θ i.castSucc) + θ (Fin.last (m + 1))) /
            (Real.Gamma (∑ i : Fin (m + 1), θ i.castSucc) * Real.Gamma (θ (Fin.last (m + 1))))) *
          Real.rpow p.2 ((∑ i : Fin (m + 1), θ i.castSucc) - 1) *
          Real.rpow (1 - p.2) (θ (Fin.last (m + 1)) - 1)) := by
    have hconst_nonneg :
        0 ≤
          Real.Gamma ((∑ i : Fin (m + 1), θ i.castSucc) + θ (Fin.last (m + 1))) /
            (Real.Gamma (∑ i : Fin (m + 1), θ i.castSucc) *
              Real.Gamma (θ (Fin.last (m + 1)))) := by
      exact div_nonneg
        ((Real.Gamma_pos_of_pos
          (add_pos hprefixThetaPos (hθ (Fin.last (m + 1))))).le)
        (mul_nonneg
          (Real.Gamma_pos_of_pos hprefixThetaPos).le
          (Real.Gamma_pos_of_pos (hθ (Fin.last (m + 1)))).le)
    have hshare_nonneg :
        0 ≤ Real.rpow p.2 ((∑ i : Fin (m + 1), θ i.castSucc) - 1) := by
      exact Real.rpow_nonneg (le_of_lt hp.2.1) _
    have hlast_nonneg :
        0 ≤ Real.rpow (1 - p.2) (θ (Fin.last (m + 1)) - 1) := by
      exact Real.rpow_nonneg (sub_nonneg.mpr hp_lt.le) _
    exact mul_nonneg (mul_nonneg hconst_nonneg hshare_nonneg) hlast_nonneg
  have hambient :
      splitLastPairEquiv m (splitLastPairMap (m := m) p) =
        splitLastChartCoords (m := m) p.1 p.2 := by
    -- Proof comment: the transported pair map is exactly the ambient split-last chart vector.
    simpa [splitLastPairEquiv] using splitLastPairMap_ambient_eq (m := m) p
  -- Proof comment: rewrite the Jacobian and the transported chart coordinates, then collapse the
  -- weighted target integrand through the established factorization theorem.
  rw [splitLastPairMap_abs_det_fderiv hpIoc, hambient, ← ENNReal.ofReal_mul
    (pow_nonneg hp.2.1.le m)]
  rw [splitLastChartKernel_factor_withPrefixDensity hm θ hθ hp.1 ⟨hp.2.1, hp_lt⟩]
  -- Proof comment: the remaining real-valued kernel is exactly the Beta density on the open strip.
  have hGammaPrefix_ne : Real.Gamma (∑ i : Fin (m + 1), θ i.castSucc) ≠ 0 :=
    (Real.Gamma_pos_of_pos hprefixThetaPos).ne'
  have hGammaLast_ne : Real.Gamma (θ (Fin.last (m + 1))) ≠ 0 :=
    (Real.Gamma_pos_of_pos (hθ (Fin.last (m + 1)))).ne'
  have hGammaTotal_ne :
      Real.Gamma ((∑ i : Fin (m + 1), θ i.castSucc) + θ (Fin.last (m + 1))) ≠ 0 := by
    exact (Real.Gamma_pos_of_pos
      (add_pos hprefixThetaPos (hθ (Fin.last (m + 1))))).ne'
  have hbetaPDF :
      betaPDF (∑ i : Fin (m + 1), θ i.castSucc) (θ (Fin.last (m + 1))) p.2 =
        ENNReal.ofReal
          ((Real.Gamma ((∑ i : Fin (m + 1), θ i.castSucc) + θ (Fin.last (m + 1))) /
              (Real.Gamma (∑ i : Fin (m + 1), θ i.castSucc) *
                Real.Gamma (θ (Fin.last (m + 1))))) *
            Real.rpow p.2 ((∑ i : Fin (m + 1), θ i.castSucc) - 1) *
            Real.rpow (1 - p.2) (θ (Fin.last (m + 1)) - 1)) := by
    rw [betaPDF_of_pos_lt_one hp.2.1 hp_lt]
    congr 1
    rw [beta]
    field_simp [hGammaPrefix_ne, hGammaLast_ne, hGammaTotal_ne]
    rfl
  rw [hbetaPDF, ← ENNReal.ofReal_mul' hbetaKernel_nonneg]

/-- Helper for Definition 24.26: under the strip-restricted pair volume, the `share = 1` boundary
is negligible, so almost every strip point lies in the open strip. -/
private theorem splitLastPositiveStrip_ae_lt_one {m : ℕ} :
    ∀ᵐ p ∂ ((((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)).restrict
      (splitLastPositiveStrip m))), p.2 < (1 : ℝ) := by
  let μ : Measure ((Fin m → ℝ) × ℝ) :=
    (((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)).restrict
      (splitLastPositiveStrip m))
  have hstrip_meas : MeasurableSet (splitLastPositiveStrip m) := by
    -- Proof comment: the strip is the intersection of the measurable prefix-chart condition with
    -- the measurable half-open interval condition on the carried share.
    change MeasurableSet
      ({p : (Fin m → ℝ) × ℝ | p.1 ∈ dirichletChart (m + 1)} ∩
        {p : (Fin m → ℝ) × ℝ | p.2 ∈ Set.Ioc (0 : ℝ) 1})
    exact ((measurableSet_dirichletChart (m + 1)).preimage measurable_fst).inter
      ((measurableSet_Ioc : MeasurableSet (Set.Ioc (0 : ℝ) 1)).preimage measurable_snd)
  have hneq_one : ∀ᵐ p ∂ μ, p.2 ≠ (1 : ℝ) := by
    -- Proof comment: the only strip points not already in the open strip are those with
    -- `share = 1`, and that boundary slice has zero restricted pair-volume.
    rw [ae_iff]
    simpa [μ] using measure_restrict_splitLastPositiveStrip_share_eq_one_zero (m := m)
  filter_upwards [ae_restrict_mem hstrip_meas, hneq_one] with p hp hp_ne
  -- Proof comment: strip membership gives `p.2 ≤ 1`, and the null-boundary lemma removes the
  -- endpoint `p.2 = 1`, leaving the strict inequality.
  exact lt_of_le_of_ne hp.2.2 hp_ne

/-- Helper for Definition 24.26: the Jacobian-weighted target density and the normalized strip
source density are almost everywhere equal on the positive strip. -/
private theorem splitLastPairWeightedTarget_ae_eq_source_onPositiveStrip {m : ℕ}
    (hm : 1 ≤ m) (θ : Fin (m + 2) → ℝ) (hθ : ∀ i, 0 < θ i) :
    ∀ᵐ p ∂ ((((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)).restrict
      (splitLastPositiveStrip m))),
      ENNReal.ofReal
          |(((splitLastPairAssembleLinear (m := m)).comp
              (splitLastPairScaleFDeriv (m := m) p)).det)| *
        ENNReal.ofReal
          (dirichletDensity θ
            (dirichletCoordsToSimplex (m + 2) (by omega)
              (splitLastPairEquiv m (splitLastPairMap (m := m) p)))) =
      ENNReal.ofReal
          (dirichletDensity (fun i : Fin (m + 1) ↦ θ i.castSucc)
            (dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) p.1)) *
        betaPDF (∑ i : Fin (m + 1), θ i.castSucc) (θ (Fin.last (m + 1))) p.2 := by
  have hstrip_meas : MeasurableSet (splitLastPositiveStrip m) := by
    -- Proof comment: the positive strip is the same measurable intersection used in the boundary
    -- lemma above.
    change MeasurableSet
      ({p : (Fin m → ℝ) × ℝ | p.1 ∈ dirichletChart (m + 1)} ∩
        {p : (Fin m → ℝ) × ℝ | p.2 ∈ Set.Ioc (0 : ℝ) 1})
    exact ((measurableSet_dirichletChart (m + 1)).preimage measurable_fst).inter
      ((measurableSet_Ioc : MeasurableSet (Set.Ioc (0 : ℝ) 1)).preimage measurable_snd)
  -- Proof comment: almost every point of the restricted source measure lies in the strip and away
  -- from the null boundary `share = 1`, so the pointwise open-strip identity applies.
  filter_upwards [ae_restrict_mem hstrip_meas, splitLastPositiveStrip_ae_lt_one (m := m)]
    with p hp hp_lt
  exact splitLastPairWeightedTarget_eq_source_of_mem_openStrip hm θ hθ hp hp_lt

/-- Helper for Definition 24.26: the transported pair-space split-last chart map is injective on
the positive strip. -/
private theorem splitLastPairMap_injOn_positiveStrip {m : ℕ} :
    Set.InjOn (splitLastPairMap (m := m)) (splitLastPositiveStrip m) := by
  intro p hp q hq hpq
  -- Proof comment: transport the equality through `splitLastPairEquiv`, where the split-last
  -- chart map is already known to be injective on the same strip.
  have hambient :
      splitLastChartCoords (m := m) p.1 p.2 =
        splitLastChartCoords (m := m) q.1 q.2 := by
    simpa [splitLastPairEquiv, splitLastPairMap_ambient_eq] using
      congrArg (splitLastPairEquiv m) hpq
  exact splitLastChartMap_injOn_positiveStrip hp hq hambient

/-- Helper for Definition 24.26: reassembling the prefix Dirichlet owner with the Beta split-last
share recovers the full simplex-density owner. -/
private theorem map_dirichletDensityPrefixBeta_to_dirichletDensityMeasure {m : ℕ}
    (hm : 1 ≤ m) (θ : Fin (m + 2) → ℝ) (hθ : ∀ i, 0 < θ i) :
    Measure.map (ownerSplitLastNormalizeAssembly (m := m))
      ((((dirichletSimplexVolume (m + 1) (Nat.succ_le_succ hm)).withDensity
          (fun x ↦ ENNReal.ofReal
            (dirichletDensity (fun i : Fin (m + 1) ↦ θ i.castSucc) x))) :
          Measure (dirichletSimplex (m + 1))).prod
        (betaMeasure (∑ i : Fin (m + 1), θ i.castSucc) (θ (Fin.last (m + 1))))) =
      (((dirichletSimplexVolume (m + 2) (by omega)).withDensity
          (fun x ↦ ENNReal.ofReal (dirichletDensity θ x))) :
        Measure (dirichletSimplex (m + 2))) := by
  let μ : Measure ((Fin m → ℝ) × ℝ) :=
    ((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ))
  let strip : Set ((Fin m → ℝ) × ℝ) := splitLastPositiveStrip m
  let image : Set ((Fin m → ℝ) × ℝ) := splitLastPairMap '' strip
  let chartSet : Set ((Fin m → ℝ) × ℝ) :=
    (splitLastPairEquiv m) ⁻¹' dirichletChart (m + 2)
  let zeroSlice : Set ((Fin m → ℝ) × ℝ) :=
    {q | splitLastPairEquiv m q ∈ dirichletChart (m + 2) ∧
        ∑ i, splitLastPairEquiv m q i = 0}
  let pairChart : ((Fin m → ℝ) × ℝ) → dirichletSimplex (m + 1) × ℝ :=
    fun p ↦ (dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) p.1, p.2)
  let targetPairChart : ((Fin m → ℝ) × ℝ) → dirichletSimplex (m + 2) :=
    dirichletCoordsToSimplex (m + 2) (by omega) ∘ splitLastPairEquiv m
  let sourceWeight : ((Fin m → ℝ) × ℝ) → ENNReal :=
    fun p ↦
      (ENNReal.ofReal
        (dirichletDensity (fun i : Fin (m + 1) ↦ θ i.castSucc)
          (dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) p.1))) *
      betaPDF (∑ i : Fin (m + 1), θ i.castSucc) (θ (Fin.last (m + 1))) p.2
  let targetWeight : ((Fin m → ℝ) × ℝ) → ENNReal :=
    fun q ↦ ENNReal.ofReal
      (dirichletDensity θ
        (dirichletCoordsToSimplex (m + 2) (by omega) (splitLastPairEquiv m q)))
  let targetSourceWeight : ((Fin m → ℝ) × ℝ) → ENNReal :=
    fun p ↦
      ENNReal.ofReal
          |(((splitLastPairAssembleLinear (m := m)).comp
              (splitLastPairScaleFDeriv (m := m) p)).det)| *
        targetWeight (splitLastPairMap (m := m) p)
  have hstrip_meas : MeasurableSet strip := by
    -- Proof comment: the positive strip is the measurable intersection of the prefix chart with
    -- the split-last share interval `(0, 1]`.
    change MeasurableSet
      ({p : (Fin m → ℝ) × ℝ | p.1 ∈ dirichletChart (m + 1)} ∩
        {p : (Fin m → ℝ) × ℝ | p.2 ∈ Set.Ioc (0 : ℝ) 1})
    exact ((measurableSet_dirichletChart (m + 1)).preimage measurable_fst).inter
      ((measurableSet_Ioc : MeasurableSet (Set.Ioc (0 : ℝ) 1)).preimage measurable_snd)
  have hpairChartMeas : Measurable pairChart := by
    -- Proof comment: the pair chart is the measurable prefix simplex chart together with the
    -- carried split-last share.
    change Measurable
      (fun p : (Fin m → ℝ) × ℝ ↦
        (dirichletCoordsToSimplex (m + 1) (Nat.succ_le_succ hm) p.1, p.2))
    exact ((measurable_dirichletCoordsToSimplex (Nat.succ_le_succ hm)).comp measurable_fst).prodMk
      measurable_snd
  have hsplitLastPairMapMeas : Measurable (splitLastPairMap (m := m)) := by
    -- Proof comment: the transported split-last chart map is built from measurable arithmetic on
    -- the prefix block and the carried share.
    change Measurable
      (fun p : (Fin m → ℝ) × ℝ ↦ ((fun i ↦ p.2 * p.1 i), p.2 * (1 - ∑ i, p.1 i)))
    fun_prop
  have htargetPairChartMeas : Measurable targetPairChart := by
    -- Proof comment: the target pair chart is the measurable pair equivalence followed by the
    -- measurable simplex chart map.
    exact (measurable_dirichletCoordsToSimplex (by omega)).comp (splitLastPairEquiv m).measurable
  have hchartSet_meas : MeasurableSet chartSet := by
    -- Proof comment: `chartSet` is the pullback of the target Dirichlet chart under the pair
    -- equivalence.
    exact (measurableSet_dirichletChart (m + 2)).preimage (splitLastPairEquiv m).measurable
  have hsum_meas :
      Measurable fun q : (Fin m → ℝ) × ℝ ↦ ∑ i, splitLastPairEquiv m q i := by
    -- Proof comment: the total chart mass is a finite sum of measurable ambient coordinates.
    exact Finset.measurable_sum Finset.univ fun i _ ↦
      (measurable_pi_apply i).comp (splitLastPairEquiv m).measurable
  have himage_eq :
      image =
        {q : (Fin m → ℝ) × ℝ |
          splitLastPairEquiv m q ∈ dirichletChart (m + 2) ∧
            0 < ∑ i, splitLastPairEquiv m q i} := by
    simpa [image, strip] using splitLastPairMap_image_positiveStrip (m := m)
  have himage_meas : MeasurableSet image := by
    -- Proof comment: the Jacobian image is the target chart intersected with the positive total
    -- mass region.
    rw [himage_eq]
    exact hchartSet_meas.inter (measurableSet_lt measurable_const hsum_meas)
  have hsourceChart :
      Measure.map pairChart (((μ.restrict strip).withDensity sourceWeight)) =
        ((((dirichletSimplexVolume (m + 1) (Nat.succ_le_succ hm)).withDensity
            (fun x ↦ ENNReal.ofReal
              (dirichletDensity (fun i : Fin (m + 1) ↦ θ i.castSucc) x))) :
            Measure (dirichletSimplex (m + 1))).prod
          (betaMeasure (∑ i : Fin (m + 1), θ i.castSucc) (θ (Fin.last (m + 1))))) := by
    -- Proof comment: the packaged positive-strip source is exactly the chart-side
    -- `Dirichlet(prefix) × Beta` measure.
    simpa [μ, strip, pairChart, sourceWeight] using
      mapPrefixPairChart_positiveStripSource_eq_dirichletPrefixBetaProd (m := m) hm θ
  have hbridge_base :
      (fun p ↦ ownerSplitLastNormalizeAssembly (m := m) (pairChart p)) =ᵐ[μ.restrict strip]
        fun p ↦ targetPairChart (splitLastPairMap (m := m) p) := by
    filter_upwards [ae_restrict_mem hstrip_meas] with p hp
    -- Proof comment: on the positive strip, the owner assembly and the target pair chart are
    -- already identified by the split-last chart companion.
    simpa [pairChart, targetPairChart] using
      ownerSplitLastNormalizeAssembly_prefixPair_eq_targetPairChart_of_mem_positiveStrip
        (m := m) hm hp
  have hbridge :
      (fun p ↦ ownerSplitLastNormalizeAssembly (m := m) (pairChart p)) =ᵐ[
        ((μ.restrict strip).withDensity sourceWeight)]
        fun p ↦ targetPairChart (splitLastPairMap (m := m) p) := by
    exact hbridge_base.filter_mono <|
      Measure.ae_le_iff_absolutelyContinuous.mpr (withDensity_absolutelyContinuous _ _)
  have hweighted_source :
      sourceWeight =ᵐ[μ.restrict strip] targetSourceWeight := by
    -- Proof comment: the already established strip-side density identity rewrites the packaged
    -- source density into the Jacobian-weighted target density.
    filter_upwards [splitLastPairWeightedTarget_ae_eq_source_onPositiveStrip (m := m) hm θ hθ]
      with p hp
    simpa [sourceWeight, targetSourceWeight, targetWeight] using hp.symm
  have hsourceRestrict :
      ((μ.restrict strip).withDensity sourceWeight) =
        (μ.restrict strip).withDensity targetSourceWeight := by
    rw [MeasureTheory.withDensity_congr_ae hweighted_source]
  have hsourceIndicator :
      ((μ.restrict strip).withDensity targetSourceWeight) =
        μ.withDensity (strip.indicator targetSourceWeight) := by
    -- Proof comment: expose the strip restriction as one indicator-weighted ambient measure so
    -- the Jacobian change-of-variables theorem applies directly.
    symm
    simpa [μ, strip] using
      (MeasureTheory.withDensity_indicator (μ := μ) hstrip_meas targetSourceWeight)
  have hchange :
      ∀ s : Set ((Fin m → ℝ) × ℝ),
        ∫⁻ y in image, Set.indicator s targetWeight y ∂ μ =
          ∫⁻ x in strip,
            ENNReal.ofReal
                |(((splitLastPairAssembleLinear (m := m)).comp
                    (splitLastPairScaleFDeriv (m := m) x)).det)| *
              Set.indicator s targetWeight (splitLastPairMap (m := m) x) ∂ μ := by
    intro s
    -- Proof comment: apply the standard Jacobian theorem to the split-last pair chart map on the
    -- positive strip, where injectivity and the derivative are already established.
    simpa [μ, strip, image, targetWeight, targetSourceWeight] using
      MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
        (μ := μ) (s := strip) (f := splitLastPairMap (m := m))
        (f' := fun x ↦
          (splitLastPairAssembleLinear (m := m)).comp (splitLastPairScaleFDeriv (m := m) x))
        hstrip_meas
        (fun x hx ↦ splitLastPairMap_hasFDerivWithinAt_positiveStrip (m := m) (p := x) hx)
        (splitLastPairMap_injOn_positiveStrip (m := m))
        (Set.indicator s targetWeight)
  have hmapTargetOnImage :
      Measure.map (splitLastPairMap (m := m))
          (μ.withDensity (strip.indicator targetSourceWeight)) =
        μ.withDensity (image.indicator targetWeight) := by
    apply Measure.ext
    intro s hs
    rw [Measure.map_apply hsplitLastPairMapMeas hs,
      withDensity_apply _ (hs.preimage hsplitLastPairMapMeas), withDensity_apply _ hs]
    calc
      ∫⁻ x in splitLastPairMap (m := m) ⁻¹' s, strip.indicator targetSourceWeight x ∂ μ
          = ∫⁻ x in strip,
              ENNReal.ofReal
                  |(((splitLastPairAssembleLinear (m := m)).comp
                      (splitLastPairScaleFDeriv (m := m) x)).det)| *
                Set.indicator s targetWeight (splitLastPairMap (m := m) x) ∂ μ := by
              rw [← lintegral_indicator (hs.preimage hsplitLastPairMapMeas),
                ← lintegral_indicator hstrip_meas]
              refine lintegral_congr_ae (Filter.Eventually.of_forall ?_)
              intro x
              by_cases hx : x ∈ strip
              · by_cases hxs : splitLastPairMap (m := m) x ∈ s
                · simp [strip, targetSourceWeight, hx, hxs]
                · simp [strip, targetSourceWeight, hx, hxs]
              · simp [strip, hx]
      _ = ∫⁻ y in image, Set.indicator s targetWeight y ∂ μ := by
            simpa using (hchange s).symm
      _ = ∫⁻ y in s, image.indicator targetWeight y ∂ μ := by
            rw [← lintegral_indicator himage_meas, ← lintegral_indicator hs]
            congr 1
            ext y
            by_cases hyi : y ∈ image <;> by_cases hys : y ∈ s <;> simp [hyi, hys]
  have hpairEquiv_zero :
      splitLastPairEquiv m ((0 : Fin m → ℝ), (0 : ℝ)) = 0 := by
    ext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp [splitLastPairEquiv, splitLastAmbientOfPair]
    · simp [splitLastPairEquiv, splitLastAmbientOfPair]
  have hzeroSlice_subset : zeroSlice ⊆ {((0 : Fin m → ℝ), (0 : ℝ))} := by
    intro q hq
    have hq_zero :
        splitLastPairEquiv m q = 0 := by
      exact zero_of_mem_dirichletChart_sum_eq_zero hq.1 hq.2
    have hq_eq :
        q = ((0 : Fin m → ℝ), (0 : ℝ)) := by
      apply (splitLastPairEquiv m).injective
      rw [hpairEquiv_zero]
      exact hq_zero
    simpa [hq_eq]
  have hzero_null : μ zeroSlice = 0 := by
    -- Proof comment: the chart boundary removed by the Jacobian image is the single zero vector
    -- in pair coordinates, so it is null for ambient product volume.
    refine measure_mono_null hzeroSlice_subset ?_
    simp [μ]
  have hzero_ae : ∀ᵐ q ∂ μ, q ∉ zeroSlice := by
    rw [ae_iff]
    simpa [zeroSlice] using hzero_null
  have hindicator_chart :
      image.indicator targetWeight =ᵐ[μ] chartSet.indicator targetWeight := by
    filter_upwards [hzero_ae] with q hq
    by_cases hchart : q ∈ chartSet
    · have hchart' : splitLastPairEquiv m q ∈ dirichletChart (m + 2) := hchart
      have hsum_nonneg : 0 ≤ ∑ i, splitLastPairEquiv m q i := by
        exact Finset.sum_nonneg fun i _ ↦ hchart'.1 i
      have himage : q ∈ image := by
        rw [himage_eq]
        have hsum_ne : ∑ i, splitLastPairEquiv m q i ≠ 0 := by
          intro hsum_zero
          exact hq ⟨hchart', hsum_zero⟩
        exact ⟨hchart', lt_of_le_of_ne hsum_nonneg hsum_ne.symm⟩
      simp [image, chartSet, himage, hchart]
    · have himage_not : q ∉ image := by
        intro himage
        rw [himage_eq] at himage
        exact hchart himage.1
      simp [image, chartSet, himage_not, hchart]
  have htargetChartIndicator :
      μ.withDensity (image.indicator targetWeight) =
        μ.withDensity (chartSet.indicator targetWeight) := by
    rw [MeasureTheory.withDensity_congr_ae hindicator_chart]
  -- Proof comment: push the source to pair space, rewrite the owner map on the strip, apply the
  -- Jacobian pushforward, and then enlarge the image from positive-mass chart points to the full
  -- chart because the removed zero-mass slice is null.
  rw [← hsourceChart]
  calc
    Measure.map (ownerSplitLastNormalizeAssembly (m := m))
        (Measure.map pairChart (((μ.restrict strip).withDensity sourceWeight)))
        = Measure.map (ownerSplitLastNormalizeAssembly (m := m) ∘ pairChart)
            (((μ.restrict strip).withDensity sourceWeight)) := by
              rw [Measure.map_map measurable_ownerSplitLastNormalizeAssembly hpairChartMeas]
    _ = Measure.map (targetPairChart ∘ splitLastPairMap (m := m))
          (((μ.restrict strip).withDensity sourceWeight)) := by
            exact Measure.map_congr hbridge
    _ = Measure.map targetPairChart
          (Measure.map (splitLastPairMap (m := m))
            (((μ.restrict strip).withDensity sourceWeight))) := by
              symm
              rw [Measure.map_map htargetPairChartMeas hsplitLastPairMapMeas]
    _ = Measure.map targetPairChart (μ.withDensity (image.indicator targetWeight)) := by
          rw [hsourceRestrict, hsourceIndicator, hmapTargetOnImage]
    _ = Measure.map targetPairChart (μ.withDensity (chartSet.indicator targetWeight)) := by
          rw [htargetChartIndicator]
    _ = Measure.map targetPairChart ((μ.restrict chartSet).withDensity targetWeight) := by
          rw [MeasureTheory.withDensity_indicator hchartSet_meas]
    _ = (((dirichletSimplexVolume (m + 2) (by omega)).withDensity
            (fun x ↦ ENNReal.ofReal (dirichletDensity θ x))) :
          Measure (dirichletSimplex (m + 2))) := by
            simpa [μ, chartSet, targetWeight, targetPairChart] using
              map_splitLastPairChartWithDensity_eq_dirichletDensityMeasure (m := m) θ

/-- Helper for Definition 24.26: the Gamma-product source pushes forward to the joint law of the
Dirichlet owner and its carried total mass. -/
private theorem map_dirichletGammaProduct_to_densityProdGammaSum {m : ℕ}
    (θ : Fin (m + 2) → ℝ) (hθ : ∀ i, 0 < θ i) :
    Measure.map (fun y : Fin (m + 2) → ℝ ↦
        (dirichletNormalize (m + 2) (by omega) y, dirichletPositivePartSum y))
      (dirichletGammaProductCore θ hθ : Measure (Fin (m + 2) → ℝ)) =
      ((((dirichletSimplexVolume (m + 2) (by omega)).withDensity
          (fun x ↦ ENNReal.ofReal (dirichletDensity θ x))) : Measure (dirichletSimplex (m + 2))).prod
        (gammaMeasure (∑ i : Fin (m + 2), θ i) 1)) := by
  induction m with
  | zero =>
      -- Proof comment: the carried `Fin 2` law is the already verified Beta/Gamma base case.
      simpa using map_dirichletGammaProduct_to_densityProdGammaSum_two θ hθ
  | succ m ih =>
      let μ : Measure (Fin (m + 3) → ℝ) := (dirichletGammaProductCore θ hθ : Measure (Fin (m + 3) → ℝ))
      let μPrefix : Measure (Fin (m + 2) → ℝ) :=
        (dirichletGammaProductCore (fun i : Fin (m + 2) ↦ θ i.castSucc)
          (fun i ↦ hθ i.castSucc) : Measure (Fin (m + 2) → ℝ))
      let μLast : Measure ℝ := gammaMeasure (θ (Fin.last (m + 2))) 1
      let νPrefix : Measure (dirichletSimplex (m + 2)) :=
        (((dirichletSimplexVolume (m + 2) (by omega)).withDensity
          (fun x ↦ ENNReal.ofReal
            (dirichletDensity (fun i : Fin (m + 2) ↦ θ i.castSucc) x))) :
          Measure (dirichletSimplex (m + 2)))
      let βLast : Measure ℝ :=
        betaMeasure (∑ i : Fin (m + 2), θ i.castSucc) (θ (Fin.last (m + 2)))
      let γPrefix : Measure ℝ := gammaMeasure (∑ i : Fin (m + 2), θ i.castSucc) 1
      let γTotal : Measure ℝ := gammaMeasure (∑ i : Fin (m + 3), θ i) 1
      let splitLast : (Fin (m + 3) → ℝ) → (Fin (m + 2) → ℝ) × ℝ :=
        fun y ↦ ((fun i : Fin (m + 2) ↦ y i.castSucc), y (Fin.last (m + 2)))
      let prefixNormalizeWithSum : (Fin (m + 2) → ℝ) → dirichletSimplex (m + 2) × ℝ :=
        fun y ↦ (dirichletNormalize (m + 2) (by omega) y, dirichletPositivePartSum y)
      let liftPrefix :
          ((Fin (m + 2) → ℝ) × ℝ) → (dirichletSimplex (m + 2) × ℝ) × ℝ :=
        fun p ↦ (prefixNormalizeWithSum p.1, p.2)
      let assocToPair :
          ((dirichletSimplex (m + 2) × ℝ) × ℝ) → dirichletSimplex (m + 2) × (ℝ × ℝ) :=
        fun p ↦ (p.1.1, (p.1.2, p.2))
      let liftRatio :
          (dirichletSimplex (m + 2) × (ℝ × ℝ)) → dirichletSimplex (m + 2) × (ℝ × ℝ) :=
        fun p ↦ (p.1, (p.2.1 / (p.2.1 + p.2.2), p.2.1 + p.2.2))
      let assocToAssemble :
          (dirichletSimplex (m + 2) × (ℝ × ℝ)) → ((dirichletSimplex (m + 2) × ℝ) × ℝ) :=
        fun p ↦ ((p.1, p.2.1), p.2.2)
      let liftAssemble :
          ((dirichletSimplex (m + 2) × ℝ) × ℝ) → dirichletSimplex (m + 3) × ℝ :=
        fun p ↦ (ownerSplitLastNormalizeAssembly (m := m + 1) p.1, p.2)
      let normalizeWithSum : (Fin (m + 3) → ℝ) → dirichletSimplex (m + 3) × ℝ :=
        fun y ↦ (dirichletNormalize (m + 3) (by omega) y, dirichletPositivePartSum y)
      have hPrefixThetaPos : 0 < ∑ i : Fin (m + 2), θ i.castSucc := by
        let i0 : Fin (m + 2) := 0
        have hi0 : 0 < θ i0.castSucc := hθ i0.castSucc
        have hle : θ i0.castSucc ≤ ∑ i : Fin (m + 2), θ i.castSucc := by
          exact Finset.single_le_sum (f := fun i : Fin (m + 2) ↦ θ i.castSucc)
            (by
              intro i hi
              exact le_of_lt (hθ i.castSucc))
            (by simp [i0])
        exact lt_of_lt_of_le hi0 hle
      have hTotalTheta :
          (∑ i : Fin (m + 2), θ i.castSucc) + θ (Fin.last (m + 2)) =
            ∑ i : Fin (m + 3), θ i := by
        simpa using (Fin.sum_univ_castSucc (f := fun i : Fin (m + 3) ↦ θ i)).symm
      letI : IsProbabilityMeasure μLast := by
        dsimp [μLast]
        exact isProbabilityMeasure_gammaMeasure (hθ (Fin.last (m + 2))) zero_lt_one
      letI : IsProbabilityMeasure βLast := by
        dsimp [βLast]
        exact isProbabilityMeasureBeta hPrefixThetaPos (hθ (Fin.last (m + 2)))
      letI : IsProbabilityMeasure γPrefix := by
        dsimp [γPrefix]
        exact isProbabilityMeasure_gammaMeasure hPrefixThetaPos zero_lt_one
      letI : IsProbabilityMeasure γTotal := by
        dsimp [γTotal]
        rw [← hTotalTheta]
        exact isProbabilityMeasure_gammaMeasure
          (add_pos hPrefixThetaPos (hθ (Fin.last (m + 2)))) zero_lt_one
      letI : SFinite μLast := by infer_instance
      letI : SFinite βLast := by infer_instance
      letI : SFinite γPrefix := by infer_instance
      letI : SFinite γTotal := by infer_instance
      have hpositivePartSum_meas :
          Measurable (dirichletPositivePartSum (n := m + 3)) := by
        simpa [dirichletPositivePartSum] using
          (Finset.measurable_sum Finset.univ
            (fun i _ ↦ (measurable_pi_apply i).max measurable_const))
      have hprefixPositivePartSum_meas :
          Measurable (dirichletPositivePartSum (n := m + 2)) := by
        simpa [dirichletPositivePartSum] using
          (Finset.measurable_sum Finset.univ
            (fun i _ ↦ (measurable_pi_apply i).max measurable_const))
      have hprefixNormalizeWithSum_meas : Measurable prefixNormalizeWithSum := by
        -- Proof comment: the prefix carried map is the product of the prefix owner normalization
        -- and the carried prefix mass.
        exact (measurable_dirichletNormalize (m + 2) (by omega)).prodMk
          hprefixPositivePartSum_meas
      have hnormalizeWithSum_meas : Measurable normalizeWithSum := by
        -- Proof comment: the target carried map is the product of the owner normalization and the
        -- total carried mass.
        exact (measurable_dirichletNormalize (m + 3) (by omega)).prodMk
          hpositivePartSum_meas
      have hliftPrefix_meas : Measurable liftPrefix := by
        -- Proof comment: `liftPrefix` applies the carried prefix map on the first factor and
        -- keeps the last Gamma coordinate unchanged.
        exact hprefixNormalizeWithSum_meas.comp measurable_fst |>.prodMk measurable_snd
      have hliftAssemble_meas : Measurable liftAssemble := by
        -- Proof comment: the final stage reassembles the owner part and carries the total mass
        -- through unchanged.
        exact (measurable_ownerSplitLastNormalizeAssembly (m := m + 1)).comp measurable_fst |>.prodMk
          measurable_snd
      have hExpanded :
          normalizeWithSum =ᵐ[μ]
            liftAssemble ∘ assocToAssemble ∘ liftRatio ∘ assocToPair ∘ liftPrefix ∘ splitLast := by
        -- Proof comment: on the positive Gamma-support region, the staged split-last pipeline
        -- agrees pointwise with `(dirichletNormalize, dirichletPositivePartSum)`.
        filter_upwards [ae_dirichletGammaProductCore_pos θ hθ] with y hy
        have hy_nonneg : ∀ i, 0 ≤ y i := fun i ↦ (hy i).le
        have hprefix : 0 < ∑ i : Fin (m + 2), y i.castSucc := by
          let i0 : Fin (m + 2) := 0
          have hi0 : 0 < y i0.castSucc := hy i0.castSucc
          have hle : y i0.castSucc ≤ ∑ i : Fin (m + 2), y i.castSucc := by
            exact Finset.single_le_sum (f := fun i : Fin (m + 2) ↦ y i.castSucc)
              (by
                intro i hi
                exact (hy i.castSucc).le)
              (by simp [i0])
          exact lt_of_lt_of_le hi0 hle
        have hlast : 0 < y (Fin.last (m + 2)) := hy (Fin.last (m + 2))
        simpa [normalizeWithSum, splitLast, prefixNormalizeWithSum, liftPrefix, assocToPair,
          liftRatio, assocToAssemble, liftAssemble, Function.comp] using
          ownerSplitLastNormalizeAssembly_spec_of_prefixCarriedMass
            (m := m + 1) (by omega) y hy_nonneg hprefix hlast |>.symm
      have hLiftPrefix :
          Measure.map liftPrefix (μPrefix.prod μLast) = ((νPrefix.prod γPrefix).prod μLast) := by
        -- Proof comment: transport only the prefix block by the induction hypothesis and keep the
        -- last Gamma coordinate untouched.
        calc
          Measure.map liftPrefix (μPrefix.prod μLast)
              = (Measure.map prefixNormalizeWithSum μPrefix).prod (Measure.map id μLast) := by
                  simpa [liftPrefix, prefixNormalizeWithSum] using
                    (Measure.map_prod_map (μa := μPrefix) (μc := μLast)
                      (f := prefixNormalizeWithSum) (g := id)
                      hprefixNormalizeWithSum_meas measurable_id).symm
          _ = (Measure.map prefixNormalizeWithSum μPrefix).prod μLast := by
                rw [Measure.map_id]
          _ = ((νPrefix.prod γPrefix).prod μLast) := by
                rw [ih (fun i : Fin (m + 2) ↦ θ i.castSucc) (fun i ↦ hθ i.castSucc)]
      have hPrefixOwner :
          Measure.map (dirichletNormalize (m + 2) (by omega)) μPrefix = νPrefix := by
        have hPrefixCarried :
            Measure.map prefixNormalizeWithSum μPrefix = νPrefix.prod γPrefix := by
          rw [ih (fun i : Fin (m + 2) ↦ θ i.castSucc) (fun i ↦ hθ i.castSucc)]
        have hProjected :
            Measure.map Prod.fst (Measure.map prefixNormalizeWithSum μPrefix) =
              Measure.map Prod.fst (νPrefix.prod γPrefix) := by
          exact congrArg (Measure.map Prod.fst) hPrefixCarried
        rw [Measure.map_map measurable_fst hprefixNormalizeWithSum_meas] at hProjected
        rw [(measurePreserving_fst (μ := νPrefix) (ν := γPrefix)).map_eq] at hProjected
        simpa [μPrefix, prefixNormalizeWithSum] using hProjected
      letI : IsFiniteMeasure νPrefix := by
        rw [← hPrefixOwner]
        infer_instance
      letI : SFinite νPrefix := by infer_instance
      have hAssocToPair :
          Measure.map assocToPair ((νPrefix.prod γPrefix).prod μLast) =
            νPrefix.prod (γPrefix.prod μLast) := by
        -- Proof comment: fix the factor order to `prefixOwner × (prefixMass × last)` before the
        -- ratio/sum step.
        simpa [assocToPair] using
          (measurePreserving_prodAssoc νPrefix γPrefix μLast).map_eq
      have hLiftRatio :
          Measure.map liftRatio (νPrefix.prod (γPrefix.prod μLast)) =
            νPrefix.prod (βLast.prod γTotal) := by
        have hRatio :
            Measure.map (fun p : ℝ × ℝ ↦ (p.1 / (p.1 + p.2), p.1 + p.2))
              (γPrefix.prod μLast) = βLast.prod γTotal := by
          simpa [βLast, γPrefix, γTotal, μLast, hTotalTheta] using
            map_gammaPair_toRatioAndSum_eq_prod_beta_gamma
              (∑ i : Fin (m + 2), θ i.castSucc) (θ (Fin.last (m + 2)))
              hPrefixThetaPos (hθ (Fin.last (m + 2)))
        -- Proof comment: the ratio/sum theorem only changes the `(prefixMass, last)` pair.
        calc
          Measure.map liftRatio (νPrefix.prod (γPrefix.prod μLast))
              = (Measure.map id νPrefix).prod
                  (Measure.map (fun p : ℝ × ℝ ↦ (p.1 / (p.1 + p.2), p.1 + p.2))
                    (γPrefix.prod μLast)) := by
                    simpa [liftRatio, Prod.map] using
                      (Measure.map_prod_map (μa := νPrefix) (μc := γPrefix.prod μLast)
                        (f := id)
                        (g := fun p : ℝ × ℝ ↦ (p.1 / (p.1 + p.2), p.1 + p.2))
                        measurable_id (by fun_prop)).symm
          _ = νPrefix.prod (Measure.map (fun p : ℝ × ℝ ↦ (p.1 / (p.1 + p.2), p.1 + p.2))
                (γPrefix.prod μLast)) := by
                rw [Measure.map_id]
          _ = νPrefix.prod (βLast.prod γTotal) := by
                rw [hRatio]
      have hAssocToAssemble :
          Measure.map assocToAssemble (νPrefix.prod (βLast.prod γTotal)) =
            ((νPrefix.prod βLast).prod γTotal) := by
        -- Proof comment: reassociate back to `((prefixOwner, share), total)` for the final
        -- owner assembly.
        simpa [assocToAssemble] using
          (measurePreserving_prodAssoc νPrefix βLast γTotal).symm.map_eq
      have hLiftAssemble :
          Measure.map liftAssemble ((νPrefix.prod βLast).prod γTotal) =
            ((((dirichletSimplexVolume (m + 3) (by omega)).withDensity
                (fun x ↦ ENNReal.ofReal (dirichletDensity θ x))) :
                Measure (dirichletSimplex (m + 3))).prod γTotal) := by
        -- Proof comment: reassemble the prefix Dirichlet owner with the Beta share, carrying the
        -- total Gamma mass through untouched.
        calc
          Measure.map liftAssemble ((νPrefix.prod βLast).prod γTotal)
              = (Measure.map (ownerSplitLastNormalizeAssembly (m := m + 1))
                  (νPrefix.prod βLast)).prod (Measure.map id γTotal) := by
                    simpa [liftAssemble] using
                      (Measure.map_prod_map (μa := νPrefix.prod βLast) (μc := γTotal)
                        (f := ownerSplitLastNormalizeAssembly (m := m + 1)) (g := id)
                        (measurable_ownerSplitLastNormalizeAssembly (m := m + 1))
                        measurable_id).symm
          _ = (Measure.map (ownerSplitLastNormalizeAssembly (m := m + 1))
                (νPrefix.prod βLast)).prod γTotal := by
                rw [Measure.map_id]
          _ = ((((dirichletSimplexVolume (m + 3) (by omega)).withDensity
                  (fun x ↦ ENNReal.ofReal (dirichletDensity θ x))) :
                  Measure (dirichletSimplex (m + 3))).prod γTotal) := by
                rw [map_dirichletDensityPrefixBeta_to_dirichletDensityMeasure
                  (m := m + 1) (by omega) θ hθ]
      calc
        Measure.map normalizeWithSum μ
            = Measure.map
                (liftAssemble ∘ assocToAssemble ∘ liftRatio ∘ assocToPair ∘ liftPrefix ∘ splitLast)
                μ := by
                  rw [Measure.map_congr hExpanded]
        _ = Measure.map liftAssemble
              (Measure.map assocToAssemble
                (Measure.map liftRatio
                  (Measure.map assocToPair
                    (Measure.map liftPrefix
                      (Measure.map splitLast μ))))) := by
                rw [← Measure.map_map hliftAssemble_meas (by fun_prop)]
                rw [← Measure.map_map (by fun_prop) (by fun_prop)]
                rw [← Measure.map_map (by fun_prop) (by fun_prop)]
                rw [← Measure.map_map (by fun_prop) (by fun_prop)]
                rw [← Measure.map_map hliftPrefix_meas (by fun_prop)]
        _ = Measure.map liftAssemble
              (Measure.map assocToAssemble
                (Measure.map liftRatio
                  (Measure.map assocToPair
                    (Measure.map liftPrefix (μPrefix.prod μLast))))) := by
                rw [map_dirichletGammaProductSplitLast_eq_prod (m := m + 2) θ hθ]
        _ = Measure.map liftAssemble
              (Measure.map assocToAssemble
                (Measure.map liftRatio
                  (Measure.map assocToPair ((νPrefix.prod γPrefix).prod μLast)))) := by
                rw [hLiftPrefix]
        _ = Measure.map liftAssemble
              (Measure.map assocToAssemble
                (Measure.map liftRatio (νPrefix.prod (γPrefix.prod μLast)))) := by
                rw [hAssocToPair]
        _ = Measure.map liftAssemble
              (Measure.map assocToAssemble (νPrefix.prod (βLast.prod γTotal))) := by
                rw [hLiftRatio]
        _ = Measure.map liftAssemble (((νPrefix.prod βLast).prod γTotal)) := by
                rw [hAssocToAssemble]
        _ = ((((dirichletSimplexVolume (m + 3) (by omega)).withDensity
                (fun x ↦ ENNReal.ofReal (dirichletDensity θ x))) :
                Measure (dirichletSimplex (m + 3))).prod γTotal) := by
                rw [hLiftAssemble]

/-- Helper for Definition 24.26: the simplex-density measure is the pushforward of the product
Gamma law under the normalization map. -/
private theorem dirichletDensityMeasure_eq_gammaProductMap {n : ℕ} (hn : 2 ≤ n)
    (θ : Fin n → ℝ) (hθ : ∀ i, 0 < θ i) :
    ((dirichletSimplexVolume n hn).withDensity
      (fun x ↦ ENNReal.ofReal (dirichletDensity θ x)) : Measure (dirichletSimplex n)) =
      (ProbabilityMeasure.map (dirichletGammaProductCore θ hθ)
        (measurable_dirichletNormalize n hn).aemeasurable : Measure (dirichletSimplex n)) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
  have hm' : n = m + 2 := by
    simpa [Nat.add_comm] using hm
  clear hm
  subst n
  let μ : Measure (Fin (m + 2) → ℝ) := (dirichletGammaProductCore θ hθ : Measure (Fin (m + 2) → ℝ))
  let ν : Measure (dirichletSimplex (m + 2)) :=
    (((dirichletSimplexVolume (m + 2) (by omega)).withDensity
      (fun x ↦ ENNReal.ofReal (dirichletDensity θ x))) :
      Measure (dirichletSimplex (m + 2)))
  let γ : Measure ℝ := gammaMeasure (∑ i : Fin (m + 2), θ i) 1
  let normalizeWithSum : (Fin (m + 2) → ℝ) → dirichletSimplex (m + 2) × ℝ :=
    fun y ↦ (dirichletNormalize (m + 2) (by omega) y, dirichletPositivePartSum y)
  have hThetaSumPos : 0 < ∑ i : Fin (m + 2), θ i := by
    let i0 : Fin (m + 2) := 0
    have hi0 : 0 < θ i0 := hθ i0
    have hle : θ i0 ≤ ∑ i : Fin (m + 2), θ i := by
      exact Finset.single_le_sum (f := fun i : Fin (m + 2) ↦ θ i)
        (by
          intro i hi
          exact le_of_lt (hθ i))
        (by simp [i0])
    exact lt_of_lt_of_le hi0 hle
  letI : IsProbabilityMeasure γ := by
    dsimp [γ]
    exact isProbabilityMeasure_gammaMeasure hThetaSumPos zero_lt_one
  letI : SFinite γ := by infer_instance
  have hnormalizeWithSum_meas : Measurable normalizeWithSum := by
    have hsum_meas : Measurable (dirichletPositivePartSum (n := m + 2)) := by
      simpa [dirichletPositivePartSum] using
        (Finset.measurable_sum Finset.univ
          (fun i _ ↦ (measurable_pi_apply i).max measurable_const))
    -- Proof comment: package the owner normalization and carried total mass as one measurable map.
    exact (measurable_dirichletNormalize (m + 2) (by omega)).prodMk hsum_meas
  have hcarried :
      Measure.map normalizeWithSum μ = ν.prod γ := by
    -- Proof comment: invoke the carried-law theorem and keep the projection to the owner for the
    -- final step only.
    simpa [μ, ν, γ, normalizeWithSum] using
      map_dirichletGammaProduct_to_densityProdGammaSum (m := m) θ hθ
  have hprojected : Measure.map Prod.fst (Measure.map normalizeWithSum μ) = Measure.map Prod.fst (ν.prod γ) := by
    exact congrArg (Measure.map Prod.fst) hcarried
  -- Proof comment: projecting the carried law to the first coordinate recovers the owner-valued
  -- Dirichlet pushforward, while `Prod.fst` of the product measure is the target density owner.
  rw [Measure.map_map measurable_fst hnormalizeWithSum_meas] at hprojected
  have hfst_map : Measure.map Prod.fst (ν.prod γ) = ν := by
    simpa using (measurePreserving_fst (μ := ν) (ν := γ)).map_eq
  rw [hfst_map] at hprojected
  simpa [μ, normalizeWithSum]
    using hprojected.symm

/-- Internal explicit-bound construction of the Dirichlet law, used to keep the public owner on the
canonical `[Fact (2 ≤ n)]` interface from Definition 24.26. -/
private noncomputable abbrev dirichletDistributionWithBound {n : ℕ} (hn : 2 ≤ n)
    (θ : Fin n → ℝ) (hθ : ∀ i, 0 < θ i) : ProbabilityMeasure (dirichletSimplex n) :=
  ⟨(dirichletSimplexVolume n hn).withDensity
      (fun x ↦ ENNReal.ofReal (dirichletDensity θ x)),
    by
      -- Proof comment: transfer `measure_univ = 1` from the normalized-Gamma probability law via
      -- the single bridge theorem above.
      rw [dirichletDensityMeasure_eq_gammaProductMap hn θ hθ]
      simpa using
        (ProbabilityMeasure.map (dirichletGammaProductCore θ hθ)
          (measurable_dirichletNormalize n hn).aemeasurable).property⟩

/-- Definition 24.26: the Dirichlet distribution on `Δ_n` for `n ≥ 2`, presented in source-facing
form by its simplex density against the chart measure `dx₁ ... dx_{n-1}`. -/
noncomputable def dirichletDistribution {n : ℕ} [Fact (2 ≤ n)] (θ : Fin n → ℝ)
    (hθ : ∀ i, 0 < θ i) :
    ProbabilityMeasure (dirichletSimplex n) :=
  dirichletDistributionWithBound (Fact.out : 2 ≤ n) θ hθ

/-- The Dirichlet law evaluates measurable simplex sets by integrating the textbook density over
the induced simplex chart measure. -/
theorem dirichletDistribution_apply {n : ℕ} [Fact (2 ≤ n)] (θ : Fin n → ℝ)
    (hθ : ∀ i, 0 < θ i)
    {A : Set (dirichletSimplex n)} (hA : MeasurableSet A) :
    (dirichletDistribution θ hθ : Measure (dirichletSimplex n)) A =
      ∫⁻ x in A, ENNReal.ofReal (dirichletDensity θ x)
        ∂dirichletSimplexVolume n (Fact.out : 2 ≤ n) := by
  change ((dirichletSimplexVolume n (Fact.out : 2 ≤ n)).withDensity
      fun x ↦ ENNReal.ofReal (dirichletDensity θ x)) A =
    ∫⁻ x in A, ENNReal.ofReal (dirichletDensity θ x)
      ∂dirichletSimplexVolume n (Fact.out : 2 ≤ n)
  simpa using withDensity_apply (fun x ↦ ENNReal.ofReal (dirichletDensity θ x)) hA

/-- In textbook chart coordinates, for measurable `A ⊆ Δ_n`, the Dirichlet law
integrates the density over the first `n - 1` coordinates with respect to `dx₁ ... dx_{n-1}` on
the chart domain. -/
theorem dirichletDistribution_apply_chart {n : ℕ} [Fact (2 ≤ n)] (θ : Fin n → ℝ)
    (hθ : ∀ i, 0 < θ i)
    {A : Set (dirichletSimplex n)} (hA : MeasurableSet A) :
    (dirichletDistribution θ hθ : Measure (dirichletSimplex n)) A =
      ∫⁻ x in dirichletChart n ∩
          (dirichletCoordsToSimplex n (Fact.out : 2 ≤ n)) ⁻¹' A,
        ENNReal.ofReal
          (dirichletDensity θ (dirichletCoordsToSimplex n (Fact.out : 2 ≤ n) x))
          ∂(volume : Measure (Fin (n - 1) → ℝ)) := by
  let hn : 2 ≤ n := Fact.out
  let μ : Measure (Fin (n - 1) → ℝ) :=
    ((volume : Measure (Fin (n - 1) → ℝ)).restrict (dirichletChart n))
  let F : dirichletSimplex n → ENNReal := fun x ↦ ENNReal.ofReal (dirichletDensity θ x)
  have h_preimage :
      NullMeasurableSet ((dirichletCoordsToSimplex n hn) ⁻¹' A) μ := by
    -- Proof comment: the restricted chart map is a.e.-measurable, so measurable simplex sets pull
    -- back to null-measurable ambient sets under the restricted measure.
    exact (aemeasurable_dirichletCoordsToSimplex_restrict hn).nullMeasurableSet_preimage hA
  -- Proof comment: rewrite the set integral over the simplex-density measure through the chart
  -- pushforward, then collapse the indicator on the pulled-back measurable set.
  rw [dirichletDistribution_apply θ hθ hA, ← lintegral_indicator hA]
  change
    ∫⁻ x, A.indicator F x ∂Measure.map (dirichletCoordsToSimplex n hn) μ =
      ∫⁻ x in dirichletChart n ∩ (dirichletCoordsToSimplex n hn) ⁻¹' A,
        F (dirichletCoordsToSimplex n hn x) ∂(volume : Measure (Fin (n - 1) → ℝ))
  rw [lintegral_map' ((measurable_dirichletDensity θ).indicator hA).aemeasurable
    (aemeasurable_dirichletCoordsToSimplex_restrict hn)]
  change
    ∫⁻ x in dirichletChart n,
      A.indicator F (dirichletCoordsToSimplex n hn x) ∂(volume : Measure (Fin (n - 1) → ℝ)) =
      ∫⁻ x in dirichletChart n ∩ (dirichletCoordsToSimplex n hn) ⁻¹' A,
        F (dirichletCoordsToSimplex n hn x) ∂(volume : Measure (Fin (n - 1) → ℝ))
  have h_indicator :
      (fun x : Fin (n - 1) → ℝ ↦ A.indicator F (dirichletCoordsToSimplex n hn x)) =
        ((dirichletCoordsToSimplex n hn) ⁻¹' A).indicator
          (fun x ↦ F (dirichletCoordsToSimplex n hn x)) := by
    -- Proof comment: after precomposing by the chart map, the simplex indicator becomes the
    -- ambient indicator of the preimage set.
    funext x
    by_cases hx : dirichletCoordsToSimplex n hn x ∈ A <;> simp [F, hx]
  rw [h_indicator]
  rw [MeasureTheory.setLIntegral_indicator₀
    (μ := (volume : Measure (Fin (n - 1) → ℝ)))
    (f := fun x : Fin (n - 1) → ℝ ↦ F (dirichletCoordsToSimplex n hn x))
    (t := dirichletChart n) h_preimage]
  simp [F, Set.inter_comm]

/-- The product law of independent gamma coordinates used to build the Dirichlet law. -/
noncomputable def dirichletGammaProduct {n : ℕ} (θ : Fin n → ℝ) (hθ : ∀ i, 0 < θ i) :
    ProbabilityMeasure (Fin n → ℝ) :=
  dirichletGammaProductCore θ hθ

/-- The normalized-Gamma construction recovers the source-facing Dirichlet law. This is a bridge
from the canonical owner to the later chapter realization. -/
theorem dirichletDistribution_eq_map_dirichletGammaProduct {n : ℕ} [Fact (2 ≤ n)]
    (θ : Fin n → ℝ) (hθ : ∀ i, 0 < θ i) :
    dirichletDistribution θ hθ =
      ProbabilityMeasure.map (dirichletGammaProduct θ hθ)
        (measurable_dirichletNormalize n (Fact.out : 2 ≤ n)).aemeasurable := by
  -- Proof comment: after factoring out the owner-level bridge theorem, the public equality is just
  -- equality of probability measures with the same underlying measure.
  apply Subtype.ext
  simpa [dirichletDistribution, dirichletDistributionWithBound, dirichletGammaProduct,
    dirichletGammaProductCore] using
    dirichletDensityMeasure_eq_gammaProductMap (Fact.out : 2 ≤ n) θ hθ

end ProbabilityTheory

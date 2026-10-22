/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Exercise_5_1_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Corollary_15_32
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Exercise_15_4_5
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_4

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

universe u v

namespace ProbabilityTheory

local instance : TopologicalSpace (ℕ → ℝ) := inferInstance
local instance : MeasurableSpace (ℕ → ℝ) := inferInstance
local instance : OpensMeasurableSpace (ℕ → ℝ) := inferInstance

/-- A finite stick-breaking input vector extended by the terminal value `1`. -/
def gemExtendWithTerminalOne {n : ℕ} (v : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.lastCases (1 : ℝ) v

-- Proof sketch: unfold `gemExtendWithTerminalOne`; it is defined by `Fin.lastCases`, so it agrees
-- with `v` on the nonterminal coordinates and takes the value `1` at the terminal coordinate.
/-- The extension used for finite GEM stick breaking is obtained by adjoining the terminal value
`1` to the input vector. -/
theorem gemExtendWithTerminalOne_def {n : ℕ} (v : Fin n → ℝ) :
    gemExtendWithTerminalOne v = Fin.lastCases (1 : ℝ) v := by
  -- This is exactly the defining equation of `gemExtendWithTerminalOne`.
  rfl

/-- The finite stick-breaking map sending break proportions, with a terminal factor already
included, to the associated mass vector. -/
def finiteGemStickBreakingMap {n : ℕ} (v : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun i ↦ (∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) ↦ j < i), (1 - v j)) * v i

-- Proof sketch: unfold `finiteGemStickBreakingMap`; the `i`th mass is defined as the product of
-- the earlier residual factors `1 - v j` multiplied by the `i`th break proportion.
/-- The finite stick-breaking mass at coordinate `i` is the product of all previous residual
factors times the `i`th break proportion. -/
theorem finiteGemStickBreakingMap_apply {n : ℕ} (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    finiteGemStickBreakingMap v i =
      (∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) ↦ j < i), (1 - v j)) * v i := by
  -- The coordinate formula is the definition of `finiteGemStickBreakingMap`.
  rfl

/-- The infinite stick-breaking map associated with a sequence of break proportions on `[0,1]`. -/
def gemStickBreaking (v : ℕ → ℝ) : ℕ → ℝ :=
  fun k ↦ (Finset.prod (Finset.range k) fun i ↦ (1 - v i)) * v k

-- Proof sketch: unfold `gemStickBreaking`; the `k`th coordinate is defined by multiplying the
-- residual factors from the previous breaks and then taking the `k`th break proportion.
/-- The `k`th GEM stick-breaking mass is the product of the previous residual factors times the
`k`th break proportion. -/
theorem gemStickBreaking_apply (v : ℕ → ℝ) (k : ℕ) :
    gemStickBreaking v k = (Finset.prod (Finset.range k) fun i ↦ (1 - v i)) * v k := by
  -- The infinite stick-breaking coordinates are defined by this product formula.
  rfl

/-- The canonical `GEM_θ` law, obtained by mapping an i.i.d. `Beta(1, θ)` sequence through the
infinite stick-breaking map. -/
def gemMeasure (θ : ℝ) : Measure (ℕ → ℝ) :=
  Measure.map gemStickBreaking (Measure.infinitePi fun _ : ℕ ↦ betaMeasure 1 θ)

-- Proof sketch: unfold `gemMeasure`; by definition it is the pushforward of the i.i.d.
-- `Beta(1, θ)` product law under `gemStickBreaking`.
/-- The `GEM_θ` law is the pushforward of the product `Beta(1, θ)` measure by the infinite
stick-breaking map. -/
theorem gemMeasure_def (θ : ℝ) :
    gemMeasure θ =
      Measure.map gemStickBreaking (Measure.infinitePi fun _ : ℕ ↦ betaMeasure 1 θ) := by
  -- This is the defining pushforward formula for `gemMeasure`.
  rfl

/-- The finite Beta product measure appearing in the size-biased stick-breaking representation of
the symmetric Dirichlet law with parameter `θ / (n + 1)` on `n + 1` coordinates. -/
def finiteSizeBiasedDirichletInputMeasure (θ : ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun i : Fin n ↦
    betaMeasure (1 + θ / (n + 1 : ℝ)) (θ * ((n - i.1 : ℝ) / (n + 1 : ℝ)))

-- Proof sketch: unfold `finiteSizeBiasedDirichletInputMeasure`; it is exactly the product of the
-- Beta laws with parameters `1 + θ/(n+1)` and `θ (n-i)/(n+1)`.
/-- The finite size-biased Dirichlet input law is the product of the Beta measures from the
stick-breaking representation of `Dir_{θ/(n+1);\,n+1}`. -/
theorem finiteSizeBiasedDirichletInputMeasure_def (θ : ℝ) (n : ℕ) :
    finiteSizeBiasedDirichletInputMeasure θ n =
      Measure.pi fun i : Fin n ↦
        betaMeasure (1 + θ / (n + 1 : ℝ)) (θ * ((n - i.1 : ℝ) / (n + 1 : ℝ))) := by
  -- The finite input law is defined as this product measure.
  rfl

/-- The finite stick-breaking sequence built from the Beta inputs for the size-biased order of the
symmetric Dirichlet law on `n + 1` coordinates, extended by zeros after coordinate `n`. -/
def finiteSizeBiasedDirichletStickBreaking (n : ℕ) (v : Fin n → ℝ) : ℕ → ℝ :=
  fun k ↦
    if hk : k < n + 1 then
      finiteGemStickBreakingMap (gemExtendWithTerminalOne v) ⟨k, hk⟩
    else
      0

-- Proof sketch: unfold `finiteSizeBiasedDirichletStickBreaking`; below the cutoff `n + 1` it is
-- the finite stick-breaking map with terminal value `1`, and afterwards it is zero.
/-- The finite size-biased Dirichlet stick-breaking sequence agrees with the finite
stick-breaking map on the first `n + 1` coordinates and vanishes afterwards. -/
theorem finiteSizeBiasedDirichletStickBreaking_apply
    (n : ℕ) (v : Fin n → ℝ) (k : ℕ) :
    finiteSizeBiasedDirichletStickBreaking n v k =
      if hk : k < n + 1 then
        finiteGemStickBreakingMap (gemExtendWithTerminalOne v) ⟨k, hk⟩
      else
        0 := by
  -- The finite stick-breaking sequence is defined by this cutoff at `n + 1`.
  rfl

/-- The law on `ℕ → ℝ` obtained by applying the finite size-biased Dirichlet stick-breaking map to
its Beta input measure. -/
def finiteSizeBiasedDirichletLaw (θ : ℝ) (n : ℕ) : Measure (ℕ → ℝ) :=
  Measure.map (finiteSizeBiasedDirichletStickBreaking n) (finiteSizeBiasedDirichletInputMeasure θ n)

-- Proof sketch: unfold `finiteSizeBiasedDirichletLaw`; by definition it is the pushforward of the
-- finite Beta input law under `finiteSizeBiasedDirichletStickBreaking`.
/-- The finite size-biased Dirichlet law is the pushforward of the corresponding finite Beta input
measure under the finite stick-breaking map. -/
theorem finiteSizeBiasedDirichletLaw_def (θ : ℝ) (n : ℕ) :
    finiteSizeBiasedDirichletLaw θ n =
      Measure.map (finiteSizeBiasedDirichletStickBreaking n)
        (finiteSizeBiasedDirichletInputMeasure θ n) := by
  -- This law is defined as the pushforward of the finite input measure.
  rfl

/-- Helper for Theorem 24.33: adjoining the terminal value `1` is measurable on the finite
product space. -/
theorem measurable_gemExtendWithTerminalOne {n : ℕ} :
    Measurable (gemExtendWithTerminalOne : (Fin n → ℝ) → Fin (n + 1) → ℝ) := by
  rw [measurable_pi_iff]
  intro i
  -- Check the terminal coordinate and the inherited coordinates separately.
  refine Fin.lastCases ?_ ?_ i
  · simp [gemExtendWithTerminalOne_def]
  · intro j
    simpa [gemExtendWithTerminalOne_def] using
      (measurable_pi_apply j : Measurable fun v : Fin n → ℝ ↦ v j)

/-- Helper for Theorem 24.33: the finite size-biased stick-breaking map is measurable. -/
theorem measurable_finiteSizeBiasedDirichletStickBreaking (n : ℕ) :
    Measurable (finiteSizeBiasedDirichletStickBreaking n : (Fin n → ℝ) → ℕ → ℝ) := by
  rw [measurable_pi_iff]
  intro k
  by_cases hk : k < n + 1
  · have hBranch :
        Measurable fun v : Fin n → ℝ ↦
          finiteGemStickBreakingMap (gemExtendWithTerminalOne v) ⟨k, hk⟩ := by
      -- Expand one coordinate into a finite product of measurable coordinate evaluations.
      simpa [finiteGemStickBreakingMap_apply] using
        ((Finset.measurable_prod _ fun j _ ↦
            measurable_const.sub
              ((measurable_pi_apply j).comp measurable_gemExtendWithTerminalOne)).mul
          ((measurable_pi_apply ⟨k, hk⟩).comp measurable_gemExtendWithTerminalOne))
    -- Below the cutoff the map is exactly the finite stick-breaking coordinate.
    simpa [finiteSizeBiasedDirichletStickBreaking_apply, hk] using hBranch
  · -- Above the cutoff the coordinate is constantly zero.
    simpa [finiteSizeBiasedDirichletStickBreaking_apply, hk] using
      (measurable_const : Measurable fun _ : Fin n → ℝ ↦ (0 : ℝ))

/-- Helper for Theorem 24.33: the infinite GEM stick-breaking map is measurable. -/
theorem measurable_gemStickBreakingMap : Measurable (gemStickBreaking : (ℕ → ℝ) → ℕ → ℝ) := by
  rw [measurable_pi_iff]
  intro k
  -- Each GEM coordinate is a finite product of measurable evaluations.
  simpa [gemStickBreaking_apply] using
    ((Finset.measurable_prod _ fun i _ ↦ measurable_const.sub (measurable_pi_apply i)).mul
      (measurable_pi_apply k))

/-- Helper for Theorem 24.33: embed the finite Beta input vector into the fixed sequence space
`ℕ → ℝ` by keeping the first `n` coordinates, inserting the terminal value `1` at coordinate `n`,
and setting the tail to `0`. -/
def finiteSizeBiasedDirichletInputEmbedding (n : ℕ) : (Fin n → ℝ) → ℕ → ℝ :=
  fun v k ↦
    if hk : k < n then
      v ⟨k, hk⟩
    else if hkn : k = n then
      1
    else
      0

/-- Helper for Theorem 24.33: the embedded input agrees with the original finite coordinate below
the cutoff `n`. -/
theorem finiteSizeBiasedDirichletInputEmbedding_apply_lt
    {n : ℕ} (v : Fin n → ℝ) {k : ℕ} (hk : k < n) :
    finiteSizeBiasedDirichletInputEmbedding n v k = v ⟨k, hk⟩ := by
  -- Proof comment: below the cutoff the embedding simply reads off the original finite coordinate.
  simp [finiteSizeBiasedDirichletInputEmbedding, hk]

/-- Helper for Theorem 24.33: the embedded input takes the terminal value `1` at coordinate `n`. -/
theorem finiteSizeBiasedDirichletInputEmbedding_apply_eq
    {n : ℕ} (v : Fin n → ℝ) :
    finiteSizeBiasedDirichletInputEmbedding n v n = 1 := by
  -- Proof comment: the middle branch of the embedding inserts the terminal value `1`.
  simp [finiteSizeBiasedDirichletInputEmbedding]

/-- Helper for Theorem 24.33: the embedded input vanishes strictly after coordinate `n`. -/
theorem finiteSizeBiasedDirichletInputEmbedding_apply_gt
    {n : ℕ} (v : Fin n → ℝ) {k : ℕ} (hk : n < k) :
    finiteSizeBiasedDirichletInputEmbedding n v k = 0 := by
  -- Proof comment: once the finite stick-breaking coordinates are exhausted, the embedding pads
  -- the remaining tail with zeros.
  have hkn : ¬ k = n := by omega
  simp [finiteSizeBiasedDirichletInputEmbedding, Nat.not_lt.mpr hk.le, hkn]

/-- Helper for Theorem 24.33: the finite input embedding is measurable. -/
theorem measurable_finiteSizeBiasedDirichletInputEmbedding (n : ℕ) :
    Measurable (finiteSizeBiasedDirichletInputEmbedding n : (Fin n → ℝ) → ℕ → ℝ) := by
  rw [measurable_pi_iff]
  intro k
  by_cases hk : k < n
  · -- Proof comment: below the cutoff the coordinate map is just projection to `⟨k, hk⟩`.
    have hcoord : Measurable fun v : Fin n → ℝ ↦ v (⟨k, hk⟩ : Fin n) :=
      measurable_pi_apply (⟨k, hk⟩ : Fin n)
    simpa [finiteSizeBiasedDirichletInputEmbedding, hk] using hcoord
  · by_cases hkn : k = n
    · -- Proof comment: the terminal coordinate is the constant `1`.
      simpa [finiteSizeBiasedDirichletInputEmbedding, hk, hkn] using
        (measurable_const : Measurable fun _ : Fin n → ℝ ↦ (1 : ℝ))
    · -- Proof comment: the tail coordinates are constantly `0`.
      simpa [finiteSizeBiasedDirichletInputEmbedding, hk, hkn] using
        (measurable_const : Measurable fun _ : Fin n → ℝ ↦ (0 : ℝ))

/-- Helper for Theorem 24.33: every Beta law is almost surely supported on
`Set.Icc (0 : ℝ) 1`. -/
theorem ae_mem_Icc_betaMeasure {a b : ℝ} :
    ∀ᵐ x ∂ betaMeasure a b, x ∈ Set.Icc (0 : ℝ) 1 := by
  rw [betaMeasure, ae_withDensity_iff (by
    simpa [betaPDF] using ENNReal.measurable_ofReal.comp (measurable_betaPDFReal a b))]
  filter_upwards with x hx
  -- Proof comment: outside `[0,1]` the beta density is zero, so any point with nonzero density
  -- must lie in the support interval.
  have hx_nonneg : 0 ≤ x := by
    by_contra hx_neg
    exact hx (betaPDF_eq_zero_of_nonpos (le_of_not_ge hx_neg))
  have hx_le_one : x ≤ 1 := by
    by_contra hx_gt
    exact hx (betaPDF_eq_zero_of_one_le (le_of_lt (not_le.mp hx_gt)))
  exact ⟨hx_nonneg, hx_le_one⟩

/-- Helper for Theorem 24.33: if every finite input coordinate lies in `[0,1]`, then the embedded
sequence lies in the compact cube `Set.pi Set.univ (fun _ : ℕ ↦ Set.Icc (0 : ℝ) 1)`. -/
theorem finiteSizeBiasedDirichletInputEmbedding_mem_unitCube
    {n : ℕ} {v : Fin n → ℝ}
    (hv : ∀ i, v i ∈ Set.Icc (0 : ℝ) 1) :
    finiteSizeBiasedDirichletInputEmbedding n v ∈
      Set.pi Set.univ (fun _ : ℕ ↦ Set.Icc (0 : ℝ) 1) := by
  -- Proof comment: the embedding preserves the original `[0,1]` coordinates, inserts `1`, and
  -- pads the tail with `0`, so every coordinate still lies in the unit interval.
  intro k hk
  by_cases hlt : k < n
  · simpa [finiteSizeBiasedDirichletInputEmbedding, hlt] using hv ⟨k, hlt⟩
  · by_cases hkn : k = n
    · simpa [finiteSizeBiasedDirichletInputEmbedding, hlt, hkn]
    · simpa [finiteSizeBiasedDirichletInputEmbedding, hlt, hkn]

/-- Helper for Theorem 24.33: the GEM stick-breaking map is continuous on the fixed sequence
space. -/
theorem continuous_gemStickBreaking : Continuous (gemStickBreaking : (ℕ → ℝ) → ℕ → ℝ) := by
  -- Proof comment: prove continuity coordinatewise, then combine the coordinate maps by the
  -- product-topology characterization of continuity into a pi space.
  refine continuous_pi fun k ↦ ?_
  -- Proof comment: the `k`th coordinate is a finite algebraic combination of coordinate
  -- evaluations.
  simpa [gemStickBreaking_apply] using
    ((continuous_finset_prod _ fun i _ ↦ continuous_const.sub (continuous_apply i)).mul
      (continuous_apply k))

/-- Helper for Theorem 24.33: the finite size-biased stick-breaking sequence is the GEM
stick-breaking map applied to the fixed-space embedded input sequence. -/
theorem finiteSizeBiasedDirichletStickBreaking_eq_gemStickBreaking
    (n : ℕ) (v : Fin n → ℝ) :
    finiteSizeBiasedDirichletStickBreaking n v =
      gemStickBreaking (finiteSizeBiasedDirichletInputEmbedding n v) := by
  -- Route correction: normalize the finite predecessor product first, then compare the coordinate
  -- and predecessor factors with the fixed-space embedding one by one.
  funext k
  by_cases hk : k < n + 1
  · simp only [finiteSizeBiasedDirichletStickBreaking_apply, hk, gemStickBreaking_apply,
      finiteGemStickBreakingMap_apply]
    have hk_le : k ≤ n := by omega
    have hprod :
        (∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) ↦ j < ⟨k, hk⟩),
            (1 - gemExtendWithTerminalOne v j)) =
          Finset.prod (Finset.range k) fun i ↦
            (1 - finiteSizeBiasedDirichletInputEmbedding n v i) := by
      -- Proof comment: reindex the predecessor product by the underlying natural value
      -- `j.1 : ℕ`, which bijects the predecessors of `⟨k, hk⟩` with `range k`.
      refine Finset.prod_bij (fun j _ ↦ j.1) ?_ ?_ ?_ ?_
      · intro j hj
        rw [Finset.mem_filter] at hj
        exact Finset.mem_range.mpr (by simpa [Fin.lt_def] using hj.2)
      · intro j hj j' hj' hij
        apply Fin.ext
        exact hij
      · intro i hi
        refine ⟨⟨i, Nat.lt_of_lt_of_le (Finset.mem_range.mp hi) (Nat.le_succ_of_le hk_le)⟩, ?_, rfl⟩
        rw [Finset.mem_filter]
        constructor
        · exact Finset.mem_univ _
        · simpa [Fin.lt_def] using Finset.mem_range.mp hi
      · intro j hj
        rw [Finset.mem_filter] at hj
        change 1 - gemExtendWithTerminalOne v j =
          1 - finiteSizeBiasedDirichletInputEmbedding n v j.1
        have hjn : j.1 < n := Nat.lt_of_lt_of_le (by simpa [Fin.lt_def] using hj.2) hk_le
        have hcast : j = (⟨j.1, hjn⟩ : Fin n).castSucc := by
          apply Fin.ext
          rfl
        rw [hcast]
        simp only [Fin.coe_castSucc]
        rw [finiteSizeBiasedDirichletInputEmbedding_apply_lt (v := v) hjn]
        simp only [gemExtendWithTerminalOne_def, Fin.lastCases_castSucc]
    have hcoord :
        gemExtendWithTerminalOne v ⟨k, hk⟩ =
          finiteSizeBiasedDirichletInputEmbedding n v k := by
      by_cases hkn : k < n
      · have hcast : (⟨k, hk⟩ : Fin (n + 1)) = (⟨k, hkn⟩ : Fin n).castSucc := by
          apply Fin.ext
          rfl
        rw [hcast, finiteSizeBiasedDirichletInputEmbedding_apply_lt (v := v) hkn]
        simp only [gemExtendWithTerminalOne_def, Fin.lastCases_castSucc]
      · have hkeq : k = n := by omega
        subst k
        have hlast : (⟨n, hk⟩ : Fin (n + 1)) = Fin.last n := by
          apply Fin.ext
          rfl
        simpa [hlast, gemExtendWithTerminalOne_def,
          finiteSizeBiasedDirichletInputEmbedding_apply_eq (v := v)]
    simpa [hprod, hcoord]
  · have hgt : n < k := by omega
    simp only [finiteSizeBiasedDirichletStickBreaking_apply, hk, gemStickBreaking_apply,
      finiteSizeBiasedDirichletInputEmbedding_apply_gt (v := v) hgt]
    simp

-- Proof sketch: each factor in the product measure is a Beta probability measure when `θ > 0`,
-- and products of probability measures are probability measures.
/-- The finite Beta input measure for the size-biased Dirichlet stick-breaking construction is a
probability measure when `θ > 0`. -/
instance instIsProbabilityMeasureFiniteSizeBiasedDirichletInputMeasure
    (θ : ℝ) (hθ : 0 < θ) (n : ℕ) :
    IsProbabilityMeasure (finiteSizeBiasedDirichletInputMeasure θ n) := by
  classical
  -- Each coordinate Beta law is a probability measure for positive parameters.
  letI :
      ∀ i : Fin n,
        IsProbabilityMeasure
          (betaMeasure (1 + θ / (n + 1 : ℝ)) (θ * ((n - i.1 : ℝ) / (n + 1 : ℝ)))) := fun i ↦ by
    have hi : 0 < (n - i.1 : ℝ) := by
      have hi' : (i.1 : ℝ) < n := by
        exact_mod_cast i.2
      linarith
    have hleft : 0 < 1 + θ / (n + 1 : ℝ) := by
      positivity
    have hright : 0 < θ * ((n - i.1 : ℝ) / (n + 1 : ℝ)) := by
      positivity
    exact isProbabilityMeasureBeta hleft hright
  -- The finite product of probability measures is again a probability measure.
  simpa [finiteSizeBiasedDirichletInputMeasure] using
    (inferInstance :
      IsProbabilityMeasure
        (Measure.pi fun i : Fin n ↦
          betaMeasure (1 + θ / (n + 1 : ℝ)) (θ * ((n - i.1 : ℝ) / (n + 1 : ℝ)))))

-- Proof sketch: `finiteSizeBiasedDirichletLaw θ n` is a pushforward of the finite Beta input
-- probability measure, and pushforwards preserve total mass.
/-- The finite size-biased Dirichlet stick-breaking law is a probability measure when `θ > 0`. -/
instance instIsProbabilityMeasureFiniteSizeBiasedDirichletLaw
    (θ : ℝ) (hθ : 0 < θ) (n : ℕ) :
    IsProbabilityMeasure (finiteSizeBiasedDirichletLaw θ n) := by
  letI : IsProbabilityMeasure (finiteSizeBiasedDirichletInputMeasure θ n) :=
    instIsProbabilityMeasureFiniteSizeBiasedDirichletInputMeasure θ hθ n
  -- Pushforwards of probability measures remain probability measures.
  simpa [finiteSizeBiasedDirichletLaw] using
    (Measure.isProbabilityMeasure_map
      (μ := finiteSizeBiasedDirichletInputMeasure θ n)
      (f := finiteSizeBiasedDirichletStickBreaking n)
      (measurable_finiteSizeBiasedDirichletStickBreaking (n := n)).aemeasurable)

-- Proof sketch: `gemMeasure θ` is the pushforward of a countable product of `Beta(1, θ)`
-- probability measures, hence it is again a probability measure when `θ > 0`.
/-- The `GEM_θ` law is a probability measure for `θ > 0`. -/
instance instIsProbabilityMeasureGemMeasure (θ : ℝ) (hθ : 0 < θ) :
    IsProbabilityMeasure (gemMeasure θ) := by
  letI : ∀ _i : ℕ, IsProbabilityMeasure (betaMeasure 1 θ) := fun _ ↦
    isProbabilityMeasureBeta zero_lt_one hθ
  -- The i.i.d. Beta product law is probabilistic, and so is its pushforward.
  simpa [gemMeasure] using
    (Measure.isProbabilityMeasure_map
      (μ := Measure.infinitePi fun _ : ℕ ↦ betaMeasure 1 θ)
      (f := gemStickBreaking)
      measurable_gemStickBreakingMap.aemeasurable)

/-- The canonical `GEM_θ` law viewed as a probability measure. -/
def gemProbabilityMeasure (θ : ℝ) (hθ : 0 < θ) : ProbabilityMeasure (ℕ → ℝ) :=
  ⟨gemMeasure θ, instIsProbabilityMeasureGemMeasure θ hθ⟩

-- Proof sketch: unfold `gemProbabilityMeasure`; it is the probability-measure packaging of
-- `gemMeasure θ` using the canonical probability instance.
/-- The underlying measure of `gemProbabilityMeasure θ hθ` is `gemMeasure θ`. -/
theorem gemProbabilityMeasure_toMeasure (θ : ℝ) (hθ : 0 < θ) :
    (gemProbabilityMeasure θ hθ : Measure (ℕ → ℝ)) = gemMeasure θ := by
  -- The coercion from `ProbabilityMeasure` forgets only the bundled proof.
  rfl

/-- The finite size-biased Dirichlet stick-breaking law viewed as a probability measure. -/
def finiteSizeBiasedDirichletProbabilityMeasure
    (θ : ℝ) (hθ : 0 < θ) (n : ℕ) : ProbabilityMeasure (ℕ → ℝ) :=
  ⟨finiteSizeBiasedDirichletLaw θ n, instIsProbabilityMeasureFiniteSizeBiasedDirichletLaw θ hθ n⟩

-- Proof sketch: unfold `finiteSizeBiasedDirichletProbabilityMeasure`; it is the
-- probability-measure packaging of `finiteSizeBiasedDirichletLaw θ n`.
/-- The underlying measure of `finiteSizeBiasedDirichletProbabilityMeasure θ hθ n` is the finite
size-biased Dirichlet stick-breaking law. -/
theorem finiteSizeBiasedDirichletProbabilityMeasure_toMeasure
    (θ : ℝ) (hθ : 0 < θ) (n : ℕ) :
    (finiteSizeBiasedDirichletProbabilityMeasure θ hθ n : Measure (ℕ → ℝ)) =
      finiteSizeBiasedDirichletLaw θ n := by
  -- This coercion also forgets only the probability-measure proof.
  rfl

variable {Ω : Type u} [MeasurableSpace Ω]
variable {Ω' : Type v} [MeasurableSpace Ω']

/-- Helper for Theorem 24.33: on a finite window below `n`, restricting the fixed-space
embedding is just the corresponding `piCongrLeft` reindexing of the selected `Fin n`
coordinates. -/
private theorem restrict_finiteInputEmbedding_eq_piCongrLeft_comp
    {n : ℕ} (I : Finset ℕ) (hI : ∀ i : I, (i : ℕ) < n) :
    let e : Fin I.card ≃ I :=
      (Fintype.equivFinOfCardEq (show Fintype.card I = I.card by simp)).symm
    let es : (Fin I.card → ℝ) ≃ᵐ (I → ℝ) :=
      MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℝ) e
    es ∘ (fun v : Fin n → ℝ ↦ fun j : Fin I.card ↦ v ⟨((e j : I) : ℕ), hI (e j)⟩) =
      fun v : Fin n → ℝ ↦ I.restrict (finiteSizeBiasedDirichletInputEmbedding n v) := by
  classical
  let e : Fin I.card ≃ I :=
    (Fintype.equivFinOfCardEq (show Fintype.card I = I.card by simp)).symm
  let es : (Fin I.card → ℝ) ≃ᵐ (I → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℝ) e
  have hcomp :
      es ∘ (fun v : Fin n → ℝ ↦ fun j : Fin I.card ↦ v ⟨((e j : I) : ℕ), hI (e j)⟩) =
        fun v : Fin n → ℝ ↦ I.restrict (finiteSizeBiasedDirichletInputEmbedding n v) := by
    funext v
    ext i
    -- Proof comment: `piCongrLeft` only reindexes the same finite tuple of embedded coordinates.
    have hcoord :
        es (fun j : Fin I.card ↦ v ⟨((e j : I) : ℕ), hI (e j)⟩) i =
          (fun j : Fin I.card ↦ v ⟨((e j : I) : ℕ), hI (e j)⟩) (e.symm i) := by
      simpa [es] using
        (Equiv.piCongrLeft_apply_apply
          (fun _ : I ↦ ℝ)
          e
          (fun j : Fin I.card ↦ v ⟨((e j : I) : ℕ), hI (e j)⟩)
          (e.symm i))
    -- Proof comment: on the chosen window every embedded coordinate uses the `< n` branch.
    have hi : ((i : I) : ℕ) < n := hI i
    simpa [Finset.restrict, finiteSizeBiasedDirichletInputEmbedding_apply_lt (v := v) hi] using
      hcoord
  simpa [e, es] using hcomp

/-- Helper for Theorem 24.33: after restricting to a finite window below `n`, the embedded input
law is the `piCongrLeft` image of the selected finite coordinate tuple from the original
`Fin n`-indexed Beta product law. -/
private theorem map_restrict_finiteSizeBiasedDirichletInputEmbedding_eq_piCongrLeft_map
    (θ : ℝ) {n : ℕ} (I : Finset ℕ) (hI : ∀ i : I, (i : ℕ) < n) :
    let e : Fin I.card ≃ I :=
      (Fintype.equivFinOfCardEq (show Fintype.card I = I.card by simp)).symm
    let es : (Fin I.card → ℝ) ≃ᵐ (I → ℝ) :=
      MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℝ) e
    Measure.map (fun v : Fin n → ℝ ↦ I.restrict (finiteSizeBiasedDirichletInputEmbedding n v))
      (finiteSizeBiasedDirichletInputMeasure θ n) =
      Measure.map es
        (Measure.map
          (fun v : Fin n → ℝ ↦ fun j : Fin I.card ↦ v ⟨((e j : I) : ℕ), hI (e j)⟩)
          (finiteSizeBiasedDirichletInputMeasure θ n)) := by
  classical
  let e : Fin I.card ≃ I :=
    (Fintype.equivFinOfCardEq (show Fintype.card I = I.card by simp)).symm
  let es : (Fin I.card → ℝ) ≃ᵐ (I → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℝ) e
  have htupleMeas :
      Measurable (fun v : Fin n → ℝ ↦ fun j : Fin I.card ↦ v ⟨((e j : I) : ℕ), hI (e j)⟩) := by
    rw [measurable_pi_iff]
    intro j
    simpa using (measurable_pi_apply (⟨((e j : I) : ℕ), hI (e j)⟩ : Fin n))
  have hmap :
      Measure.map
          (fun v : Fin n → ℝ ↦ es (fun j : Fin I.card ↦ v ⟨((e j : I) : ℕ), hI (e j)⟩))
          (finiteSizeBiasedDirichletInputMeasure θ n) =
        Measure.map es
          (Measure.map
            (fun v : Fin n → ℝ ↦ fun j : Fin I.card ↦ v ⟨((e j : I) : ℕ), hI (e j)⟩)
            (finiteSizeBiasedDirichletInputMeasure θ n)) := by
    -- Proof comment: this is the standard `Measure.map_map` factorization through the
    -- coordinate-selection tuple.
    simpa [Function.comp] using (Measure.map_map es.measurable htupleMeas).symm
  -- Proof comment: replace the restricted embedding by the transported tuple map, then apply the
  -- generic pushforward factorization through `Measure.map_map`.
  calc
    Measure.map (fun v : Fin n → ℝ ↦ I.restrict (finiteSizeBiasedDirichletInputEmbedding n v))
        (finiteSizeBiasedDirichletInputMeasure θ n) =
      Measure.map
        (fun v : Fin n → ℝ ↦ es (fun j : Fin I.card ↦ v ⟨((e j : I) : ℕ), hI (e j)⟩))
        (finiteSizeBiasedDirichletInputMeasure θ n) := by
          congr 1
          funext v
          simpa [Function.comp, e, es] using
          (congrFun (restrict_finiteInputEmbedding_eq_piCongrLeft_comp (n := n) I hI) v).symm
    _ = Measure.map es
          (Measure.map
            (fun v : Fin n → ℝ ↦ fun j : Fin I.card ↦ v ⟨((e j : I) : ℕ), hI (e j)⟩)
            (finiteSizeBiasedDirichletInputMeasure θ n)) := hmap

/-- Helper for Theorem 24.33: once a finite window lies below `n`, the restricted embedded input
law is exactly the finite product of the selected Beta marginals. -/
private theorem map_restrict_finiteSizeBiasedDirichletInputEmbedding_eq_pi
    (θ : ℝ) (hθ : 0 < θ) {n : ℕ} (I : Finset ℕ) (hI : ∀ i : I, (i : ℕ) < n) :
    Measure.map (fun v : Fin n → ℝ ↦ I.restrict (finiteSizeBiasedDirichletInputEmbedding n v))
      (finiteSizeBiasedDirichletInputMeasure θ n) =
      Measure.pi (fun i : I ↦
        betaMeasure (1 + θ / (n + 1 : ℝ))
          (θ * ((n - ((i : I) : ℕ) : ℝ) / (n + 1 : ℝ)))) := by
  classical
  let μ : Fin n → Measure ℝ := fun i ↦
    betaMeasure (1 + θ / (n + 1 : ℝ))
      (θ * ((n - i.1 : ℝ) / (n + 1 : ℝ)))
  letI : ∀ i : Fin n, IsProbabilityMeasure (μ i) := fun i ↦ by
    have hi : 0 < (n - i.1 : ℝ) := by
      have hi' : (i.1 : ℝ) < n := by
        exact_mod_cast i.2
      linarith
    have hleft : 0 < 1 + θ / (n + 1 : ℝ) := by
      positivity
    have hright : 0 < θ * ((n - i.1 : ℝ) / (n + 1 : ℝ)) := by
      positivity
    exact isProbabilityMeasureBeta hleft hright
  let g : I → Fin n := fun i ↦ ⟨((i : I) : ℕ), hI i⟩
  have hg_inj : Function.Injective g := by
    intro i j hij
    apply Subtype.ext
    exact congrArg Fin.val hij
  have hrestrict :
      (fun v : Fin n → ℝ ↦ I.restrict (finiteSizeBiasedDirichletInputEmbedding n v)) =
        fun v : Fin n → ℝ ↦ fun i : I => v (g i) := by
    funext v
    ext i
    -- Proof comment: on a window below `n`, the restriction only reads the `< n` branch of the
    -- fixed-space embedding, so it is just coordinate evaluation at the selected index.
    simpa [Finset.restrict, g] using
      (finiteSizeBiasedDirichletInputEmbedding_apply_lt (v := v) (hk := hI i))
  have hbase :
      iIndepFun (fun j : Fin n ↦ fun v : Fin n → ℝ ↦ v j) (Measure.pi μ) := by
    -- Proof comment: the canonical coordinate projections are independent under a product law.
    simpa using
      (iIndepFun_pi (μ := μ) (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id))
  have hselected :
      iIndepFun (fun i : I ↦ fun v : Fin n → ℝ ↦ v (g i)) (Measure.pi μ) :=
    hbase.precomp hg_inj
  have hmap :
      (Measure.pi μ).map (fun v : Fin n → ℝ ↦ fun i : I => v (g i)) =
        Measure.pi (fun i : I ↦ (Measure.pi μ).map (fun v : Fin n → ℝ ↦ v (g i))) := by
    -- Proof comment: finite independence upgrades the joint selected-coordinate law to the
    -- product of its one-dimensional marginals.
    exact (iIndepFun_iff_map_fun_eq_pi_map
      (μ := Measure.pi μ)
      (f := fun i : I ↦ fun v : Fin n → ℝ ↦ v (g i))
      (fun i ↦ (measurable_pi_apply (g i)).aemeasurable)).1 hselected
  have hcoord :
      ∀ i : I, (Measure.pi μ).map (fun v : Fin n → ℝ ↦ v (g i)) = μ (g i) := by
    intro i
    -- Proof comment: each selected coordinate marginal is the corresponding Beta factor.
    simpa [g] using (measurePreserving_eval μ (g i)).map_eq
  change Measure.map (fun v : Fin n → ℝ ↦ I.restrict (finiteSizeBiasedDirichletInputEmbedding n v))
      (Measure.pi μ) =
    Measure.pi (fun i : I ↦
      betaMeasure (1 + θ / (n + 1 : ℝ))
        (θ * ((n - ((i : I) : ℕ) : ℝ) / (n + 1 : ℝ))))
  calc
    Measure.map (fun v : Fin n → ℝ ↦ I.restrict (finiteSizeBiasedDirichletInputEmbedding n v))
        (Measure.pi μ) =
      (Measure.pi μ).map (fun v : Fin n → ℝ ↦ fun i : I => v (g i)) := by
        simpa [hrestrict]
    _ = Measure.pi (fun i : I ↦ (Measure.pi μ).map (fun v : Fin n → ℝ ↦ v (g i))) := hmap
    _ = Measure.pi (fun i : I ↦ μ (g i)) := by
        congr 1
        funext i
        exact hcoord i
    _ = Measure.pi (fun i : I ↦
          betaMeasure (1 + θ / (n + 1 : ℝ))
            (θ * ((n - ((i : I) : ℕ) : ℝ) / (n + 1 : ℝ)))) := by
        rfl

/-- Helper for Theorem 24.33: every embedded finite input law is carried by the compact unit cube
in `ℕ → ℝ`. -/
private theorem finiteSizeBiasedDirichletInputEmbeddingLaw_support_unitCube
    (θ : ℝ) (hθ : 0 < θ) (n : ℕ) :
    Measure.map (finiteSizeBiasedDirichletInputEmbedding n)
        (finiteSizeBiasedDirichletInputMeasure θ n)
      (Set.pi Set.univ (fun _ : ℕ ↦ Set.Icc (0 : ℝ) 1))ᶜ = 0 := by
  let μ : Fin n → Measure ℝ := fun i ↦
    betaMeasure (1 + θ / (n + 1 : ℝ))
      (θ * ((n - i.1 : ℝ) / (n + 1 : ℝ)))
  letI : ∀ i : Fin n, IsProbabilityMeasure (μ i) := fun i ↦ by
    have hi : 0 < (n - i.1 : ℝ) := by
      have hi' : (i.1 : ℝ) < n := by
        exact_mod_cast i.2
      linarith
    have hleft : 0 < 1 + θ / (n + 1 : ℝ) := by
      positivity
    have hright : 0 < θ * ((n - i.1 : ℝ) / (n + 1 : ℝ)) := by
      positivity
    exact isProbabilityMeasureBeta hleft hright
  let KFin : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1)
  let KNat : Set (ℕ → ℝ) := Set.pi Set.univ (fun _ : ℕ ↦ Set.Icc (0 : ℝ) 1)
  have hcoord : ∀ i : Fin n, Set.univ ≤ᶠ[ae (μ i)] Set.Icc (0 : ℝ) 1 := by
    intro i
    have hmem : ∀ᵐ x ∂ μ i, x ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [μ] using
        (ae_mem_Icc_betaMeasure
          (a := 1 + θ / (n + 1 : ℝ))
          (b := θ * ((n - i.1 : ℝ) / (n + 1 : ℝ))))
    exact hmem.mono fun x hx _ => hx
  have hKFin :
      KFin ∈ ae (Measure.pi μ) := by
    -- Proof comment: the finite Beta product law is almost surely inside the finite unit cube,
    -- because every coordinate Beta factor is supported on `[0,1]`.
    have hKFin' : Set.univ ≤ᶠ[ae (Measure.pi μ)] KFin := by
      simpa [KFin] using
      (Measure.ae_le_set_pi (μ := μ) (I := Set.univ)
        (s := fun _ : Fin n ↦ Set.univ)
        (t := fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1) fun i _ ↦ hcoord i
      )
    exact hKFin'.mono fun v hv => hv (by trivial)
  have hKNat_preimage :
      {v : Fin n → ℝ | finiteSizeBiasedDirichletInputEmbedding n v ∈ KNat} ∈ ae (Measure.pi μ) := by
    -- Proof comment: once all finite coordinates lie in `[0,1]`, the embedding preserves this
    -- support by keeping those coordinates, inserting `1`, and padding with `0`.
    filter_upwards [hKFin] with v hv
    exact finiteSizeBiasedDirichletInputEmbedding_mem_unitCube (v := v) fun i ↦ hv i (by simp)
  have hKNat :
      KNat ∈ ae (Measure.map (finiteSizeBiasedDirichletInputEmbedding n) (Measure.pi μ)) := by
    -- Proof comment: push the almost-sure unit-cube support through the measurable embedding map.
    exact (mem_ae_map_iff
      (measurable_finiteSizeBiasedDirichletInputEmbedding n).aemeasurable
      (MeasurableSet.univ_pi fun _ ↦ isClosed_Icc.measurableSet)).2 hKNat_preimage
  simpa [finiteSizeBiasedDirichletInputMeasure, KNat, mem_ae_iff] using hKNat

/-- Helper for Theorem 24.33: restricting a sequence to a fixed finite window is continuous. -/
private theorem continuous_restrict (I : Finset ℕ) :
    Continuous (Finset.restrict I : (ℕ → ℝ) → I → ℝ) := by
  -- Proof comment: each restricted coordinate is just evaluation at the corresponding natural
  -- index.
  refine continuous_pi fun i ↦ ?_
  simpa [Finset.restrict] using
    (continuous_apply (((i : I) : ℕ)))

/-- Helper for Theorem 24.33: positive-parameter Beta laws have finite absolute moments of every
order. -/
private theorem integrableAbsPow_id_betaMeasure_of_pos
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (p : ℕ) :
    Integrable (fun x : ℝ ↦ |x| ^ (p : ℝ)) (betaMeasure a b) := by
  letI : IsProbabilityMeasure (betaMeasure a b) := isProbabilityMeasureBeta ha hb
  refine Integrable.of_bound ?_ 1 ?_
  · simpa [Real.rpow_natCast] using
      ((continuous_abs.pow p).aestronglyMeasurable :
        AEStronglyMeasurable (fun x : ℝ ↦ |x| ^ p) (betaMeasure a b))
  · filter_upwards [ae_mem_Icc_betaMeasure (a := a) (b := b)] with x hx
    have hxpow : x ^ p ≤ 1 := pow_le_one₀ hx.1 hx.2
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · simpa [Real.rpow_natCast, abs_of_nonneg hx.1] using hxpow
    · positivity

/-- Helper for Theorem 24.33: positive-parameter Beta laws have an exponential `|x|`-moment on
`[0,1]`. -/
private theorem integrableExpAbs_id_betaMeasure_of_pos
    {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) :
    Integrable (fun x : ℝ ↦ Real.exp (t * |x|)) (betaMeasure a b) := by
  letI : IsProbabilityMeasure (betaMeasure a b) := isProbabilityMeasureBeta ha hb
  refine Integrable.of_bound ?_ (Real.exp t) ?_
  · fun_prop
  · filter_upwards [ae_mem_Icc_betaMeasure (a := a) (b := b)] with x hx
    have hxabs_le : |x| ≤ 1 := by
      simpa [abs_of_nonneg hx.1] using hx.2
    have hmul : t * |x| ≤ t * 1 := mul_le_mul_of_nonneg_left hxabs_le ht.le
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    simpa [mul_one] using Real.exp_le_exp.mpr hmul

/-- Helper for Theorem 24.33: a bounded continuous version of `x ↦ x^p` that agrees with
`x ^ p` on `[0,1]`. -/
private def unitIntervalClampPow (p : ℕ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : ℝ ↦ (max 0 (min x 1)) ^ p)
    ((continuous_const.max (continuous_id.min continuous_const)).pow p)
    1
    (fun x ↦ by
      have hclamp_nonneg : 0 ≤ max (0 : ℝ) (min x 1) := le_max_left _ _
      have hclamp_le_one : max (0 : ℝ) (min x 1) ≤ 1 := by
        refine max_le ?_ (min_le_right _ _)
        norm_num
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · simpa using pow_le_one₀ hclamp_nonneg hclamp_le_one
      · positivity)

/-- Helper for Theorem 24.33: the clamped power test equals the raw moment function on
`[0,1]`. -/
private theorem unitIntervalClampPow_apply_of_mem_Icc
    (p : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    unitIntervalClampPow p x = x ^ p := by
  -- Proof comment: on `[0,1]` the clamp collapses to the identity, so the bounded test becomes
  -- the ordinary power function.
  simp [unitIntervalClampPow, hx.1, hx.2, max_eq_right hx.1, min_eq_left hx.2]

/-- Helper for Theorem 24.33: every finite measure supported on `[0,1]` has finite absolute
natural moments. -/
private theorem integrableAbsNatPow_of_ae_mem_Icc
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) (p : ℕ) :
    Integrable (fun x : ℝ ↦ |x| ^ p) μ := by
  -- Proof comment: on `[0,1]`, the function `x ↦ |x| ^ p` is nonnegative and bounded by `1`,
  -- so finite measure already gives integrability.
  refine Integrable.of_bound ?_ 1 ?_
  · simpa using
      ((continuous_abs.pow p).aestronglyMeasurable :
        AEStronglyMeasurable (fun x : ℝ ↦ |x| ^ p) μ)
  · filter_upwards [hμ] with x hx
    have hxpow : x ^ p ≤ 1 := pow_le_one₀ hx.1 hx.2
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · simpa [abs_of_nonneg hx.1] using hxpow
    · positivity

/-- Helper for Theorem 24.33: on measures supported in `[0,1]`, the bounded clamped power test
computes the raw moment. -/
private theorem integral_unitIntervalClampPow_eq_moment_of_ae_mem_Icc
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc (0 : ℝ) 1) (p : ℕ) :
    ∫ x, (unitIntervalClampPow p : ℝ → ℝ) x ∂μ = moment id p μ := by
  -- Proof comment: under the support hypothesis, the bounded clamped test agrees almost
  -- everywhere with the raw moment integrand.
  rw [moment]
  refine integral_congr_ae ?_
  filter_upwards [hμ] with x hx
  simpa [Function.comp, unitIntervalClampPow_apply_of_mem_Icc p hx]

/-- Helper for Theorem 24.33: for a fixed selected coordinate, the shifted Beta tail ratio tends
to `1`. -/
private theorem shiftedSelectedBetaRatio_tendsto_one
    {k N : ℕ} (hkN : k < N) :
    Tendsto
      (fun m : ℕ ↦ (((m + N) - k : ℝ) / (m + N + 1 : ℝ)))
      atTop
      (nhds 1) := by
  have hkNle : k ≤ N := Nat.le_of_lt hkN
  have hrewrite :
      (fun m : ℕ ↦ (((m + N) - k : ℝ) / (m + N + 1 : ℝ))) =
        fun m : ℕ ↦
          ((((N - k : ℕ) : ℝ) + 1 * m) / (((N + 1 : ℕ) : ℝ) + 1 * m)) := by
    funext m
    have hNk : (((N - k : ℕ) : ℝ)) = (N : ℝ) - k := by
      rw [Nat.cast_sub hkNle]
    calc
      (↑m + ↑N - ↑k) / (↑m + ↑N + 1)
          = (↑m + (((N - k : ℕ) : ℝ))) / (↑m + (((N + 1 : ℕ) : ℝ))) := by
              rw [hNk]
              have hden : (↑m + ↑N + 1 : ℝ) = ↑m + (((N + 1 : ℕ) : ℝ)) := by
                simp [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm]
              rw [hden]
              ring
      _ = ((((N - k : ℕ) : ℝ) + 1 * m) / (((N + 1 : ℕ) : ℝ) + 1 * m)) := by
              ring
  rw [hrewrite]
  -- Proof comment: once the numerator and denominator are frozen in the same affine `m`-normal
  -- form, the standard quotient limit applies directly.
  simpa using
    (tendsto_add_mul_div_add_mul_atTop_nhds
      (((N - k : ℕ) : ℝ))
      (((N + 1 : ℕ) : ℝ))
      (1 : ℝ)
      (d := (1 : ℝ))
      one_ne_zero)

/-- Helper for Theorem 24.33: the moments of the shifted selected Beta factor converge to the
moments of `Beta(1, θ)`. -/
private theorem tendsto_shiftedSelectedBetaMoment
    (θ : ℝ) (hθ : 0 < θ) {k N : ℕ} (hkN : k < N) (p : ℕ) :
    Tendsto
      (fun m : ℕ ↦
        moment id p
          (betaMeasure
            (1 + θ / (m + N + 1 : ℝ))
            (θ * (((m + N) - k : ℝ) / (m + N + 1 : ℝ))))
      )
      atTop
      (nhds (moment id p (betaMeasure 1 θ))) := by
  have hthetaDiv :
      Tendsto (fun m : ℕ ↦ θ / (m + N + 1 : ℝ)) atTop (nhds 0) := by
    -- Proof comment: the additive shift in the denominator does not affect the reciprocal limit.
    convert
      (tendsto_const_div_atTop_nhds_zero_nat θ).comp (tendsto_add_atTop_nat (N + 1)) using 1
    ext m
    simp [Nat.cast_add, add_assoc, add_left_comm, add_comm]
  have hratio :
      Tendsto
        (fun m : ℕ ↦ (((m + N) - k : ℝ) / (m + N + 1 : ℝ)))
        atTop
        (nhds 1) :=
    shiftedSelectedBetaRatio_tendsto_one (k := k) (N := N) hkN
  have hmoment_expand :
      (fun m : ℕ ↦
        moment id p
          (betaMeasure
            (1 + θ / (m + N + 1 : ℝ))
            (θ * (((m + N) - k : ℝ) / (m + N + 1 : ℝ))))) =
        fun m : ℕ ↦
          ∏ j ∈ Finset.range p,
            (1 + θ / (m + N + 1 : ℝ) + j) /
              (1 + θ / (m + N + 1 : ℝ) +
                θ * (((m + N) - k : ℝ) / (m + N + 1 : ℝ)) + j) := by
    funext m
    have hleft : 0 < 1 + θ / (m + N + 1 : ℝ) := by
      positivity
    have hnum : 0 < (((m + N) - k : ℕ) : ℝ) := by
      have hklt : k < m + N := by
        omega
      exact_mod_cast Nat.sub_pos_of_lt hklt
    have hright :
        0 < θ * (((m + N) - k : ℝ) / (m + N + 1 : ℝ)) := by
      have hden : 0 < (m + N + 1 : ℝ) := by
        positivity
      have hnum' : 0 < (m + N : ℝ) - k := by
        have hklt : (k : ℝ) < m + N := by
          exact_mod_cast (show k < m + N by omega)
        linarith
      exact mul_pos hθ (div_pos hnum' hden)
    -- Proof comment: specialize the Beta moment product formula to the identity random variable
    -- under the shifted Beta law.
    simpa [moment, add_assoc, add_left_comm, add_comm] using
      (beta_moment_formula
        (1 + θ / (m + N + 1 : ℝ))
        (θ * (((m + N) - k : ℝ) / (m + N + 1 : ℝ)))
        hleft
        hright
        (ProbabilityTheory.HasLaw.id
          (μ := betaMeasure
            (1 + θ / (m + N + 1 : ℝ))
            (θ * (((m + N) - k : ℝ) / (m + N + 1 : ℝ)))))
        p)
  have htarget :
      moment id p (betaMeasure 1 θ) =
        ∏ j ∈ Finset.range p, ((1 : ℝ) + j) / ((1 : ℝ) + θ + j) := by
    -- Proof comment: the limit moments are the textbook Beta moments at parameters `(1, θ)`.
    simpa [moment, add_assoc, add_left_comm, add_comm] using
      (beta_moment_formula
        (1 : ℝ)
        θ
        zero_lt_one
        hθ
        (ProbabilityTheory.HasLaw.id (μ := betaMeasure 1 θ))
        p)
  rw [hmoment_expand, htarget]
  refine tendsto_finset_prod _ ?_
  intro j hj
  have hnum :
      Tendsto
        (fun m : ℕ ↦ 1 + θ / (m + N + 1 : ℝ) + j)
        atTop
        (nhds ((1 : ℝ) + j)) := by
    -- Proof comment: the numerator tends to `1 + j` because the shifted `θ/(m+N+1)` term vanishes.
    simpa [add_assoc] using ((hthetaDiv.const_add (1 : ℝ)).add_const (j : ℝ))
  have hscaledRatio :
      Tendsto
        (fun m : ℕ ↦ θ * (((m + N) - k : ℝ) / (m + N + 1 : ℝ)))
        atTop
        (nhds (θ * 1)) := by
    -- Proof comment: multiply the stabilized ratio limit by the fixed parameter `θ`.
    simpa using (tendsto_const_nhds.mul hratio)
  have hden :
      Tendsto
        (fun m : ℕ ↦
          1 + θ / (m + N + 1 : ℝ) +
            θ * (((m + N) - k : ℝ) / (m + N + 1 : ℝ)) + j)
        atTop
        (nhds ((1 : ℝ) + θ + j)) := by
    -- Proof comment: the denominator is the sum of the vanishing shift, the limiting `θ`, and
    -- the fixed offset `1 + j`.
    simpa [add_assoc, add_left_comm, add_comm] using
      (((hthetaDiv.const_add (1 : ℝ)).add hscaledRatio).add_const (j : ℝ))
  have hden_ne : ((1 : ℝ) + θ + j) ≠ 0 := by
    positivity
  exact hnum.div hden hden_ne

/-- Helper for Theorem 24.33: the shifted selected Beta factor has total mass `1`. -/
private theorem isProbabilityMeasure_shiftedSelectedBetaFactor
    (θ : ℝ) (hθ : 0 < θ) (k N m : ℕ) (hkN : k < N) :
    IsProbabilityMeasure
      (betaMeasure
        (1 + θ / (m + N + 1 : ℝ))
        (θ * (((m + N) - k : ℝ) / (m + N + 1 : ℝ)))) := by
  -- Proof comment: the first parameter is always strictly positive, and the second one is
  -- positive because `k < N ≤ m + N`.
  have hleft : 0 < 1 + θ / (m + N + 1 : ℝ) := by
    positivity
  have hnum : 0 < (((m + N) - k : ℕ) : ℝ) := by
    have hklt : k < m + N := by
      omega
    exact_mod_cast Nat.sub_pos_of_lt hklt
  have hright : 0 < θ * (((m + N) - k : ℝ) / (m + N + 1 : ℝ)) := by
    have hden : 0 < (m + N + 1 : ℝ) := by
      positivity
    have hnum' : 0 < (m + N : ℝ) - k := by
      have hklt : (k : ℝ) < m + N := by
        exact_mod_cast (show k < m + N by omega)
      exact sub_pos.mpr hklt
    have hfrac : 0 < (((m + N) - k : ℝ) / (m + N + 1 : ℝ)) := by
      exact div_pos hnum' hden
    positivity
  exact isProbabilityMeasureBeta hleft hright

/-- Helper for Theorem 24.33: the shifted selected Beta factor packaged as a probability measure. -/
private noncomputable def shiftedSelectedBetaFactorProbabilityMeasure
    (θ : ℝ) (hθ : 0 < θ) (k N m : ℕ) (hkN : k < N) : ProbabilityMeasure ℝ :=
  ⟨betaMeasure
      (1 + θ / (m + N + 1 : ℝ))
      (θ * (((m + N) - k : ℝ) / (m + N + 1 : ℝ))),
    isProbabilityMeasure_shiftedSelectedBetaFactor θ hθ k N m hkN⟩

/-- Helper for Theorem 24.33: the shifted selected Beta factor converges weakly to
`Beta(1, θ)`. -/
private theorem tendsto_shiftedSelectedBetaFactor
    (θ : ℝ) (hθ : 0 < θ) {k N : ℕ} (hkN : k < N) :
    Tendsto
      (fun m ↦ shiftedSelectedBetaFactorProbabilityMeasure θ hθ k N m hkN)
      atTop
      (nhds
        (⟨betaMeasure 1 θ, isProbabilityMeasureBeta zero_lt_one hθ⟩ :
          ProbabilityMeasure ℝ)) := by
  let ν : ℕ → ProbabilityMeasure ℝ :=
    fun m ↦ shiftedSelectedBetaFactorProbabilityMeasure θ hθ k N m hkN
  let μ : ProbabilityMeasure ℝ :=
    ⟨betaMeasure 1 θ, isProbabilityMeasureBeta zero_lt_one hθ⟩
  have hfinite :
      ∀ p : ℕ, ∀ᶠ m in atTop, Integrable (fun x : ℝ ↦ |x| ^ (p : ℝ)) (ν m : Measure ℝ) := by
    intro p
    refine Filter.Eventually.of_forall ?_
    intro m
    have hleft : 0 < 1 + θ / (m + N + 1 : ℝ) := by
      positivity
    have hnum : 0 < (((m + N) - k : ℕ) : ℝ) := by
      have hklt : k < m + N := by
        omega
      exact_mod_cast Nat.sub_pos_of_lt hklt
    have hright :
        0 < θ * (((m + N) - k : ℝ) / (m + N + 1 : ℝ)) := by
      have hden : 0 < (m + N + 1 : ℝ) := by
        positivity
      have hnum' : 0 < (m + N : ℝ) - k := by
        have hklt : (k : ℝ) < m + N := by
          exact_mod_cast (show k < m + N by omega)
        linarith
      exact mul_pos hθ (div_pos hnum' hden)
    -- Proof comment: every shifted Beta factor is still supported on `[0,1]`, so all absolute
    -- moments are finite.
    simpa [ν] using integrableAbsPow_id_betaMeasure_of_pos hleft hright p
  have hm :
      ∀ p : ℕ,
        Tendsto (fun m ↦ moment id p (ν m : Measure ℝ)) atTop
          (nhds (moment id p (μ : Measure ℝ))) := by
    intro p
    -- Proof comment: the one-dimensional moments converge by the scalar Beta computation above.
    simpa [ν, μ] using tendsto_shiftedSelectedBetaMoment θ hθ (k := k) (N := N) hkN p
  have hExp :
      Integrable (fun x : ℝ ↦ Real.exp ((1 : ℝ) * |x|)) (betaMeasure 1 θ) :=
    integrableExpAbs_id_betaMeasure_of_pos zero_lt_one hθ zero_lt_one
  have hdet : Measure.IsMomentDeterminate (μ : Measure ℝ) := by
    -- Proof comment: one exponential moment is enough for the Chapter 15 moment-determinacy
    -- criterion.
    letI : IsProbabilityMeasure (betaMeasure 1 θ) := isProbabilityMeasureBeta zero_lt_one hθ
    simpa [μ] using
      (method_of_moments_of_integrable_exp_abs
        (μ := betaMeasure 1 θ) zero_lt_one hExp).2
  exact tendsto_probabilityMeasure_of_moments_tendsto_of_moment_determinate hfinite hm hdet

/-- Helper for Theorem 24.33: once the whole finite window lies below the shifted index `N`, the
restricted embedded input law at time `m + N` is exactly the product of the shifted Beta factors.
-/
private theorem windowInputLaw_eq_shiftedSelectedBetaFactorPi
    (θ : ℝ) (hθ : 0 < θ) (I : Finset ℕ) {N : ℕ}
    (hI : ∀ i : I, (i : ℕ) < N) (m : ℕ) :
    ProbabilityMeasure.map
      (ProbabilityMeasure.map
        (⟨finiteSizeBiasedDirichletInputMeasure θ (m + N),
          instIsProbabilityMeasureFiniteSizeBiasedDirichletInputMeasure θ hθ (m + N)⟩ :
            ProbabilityMeasure (Fin (m + N) → ℝ))
        (measurable_finiteSizeBiasedDirichletInputEmbedding (m + N)).aemeasurable)
      (Finset.measurable_restrict I).aemeasurable
    =
      ProbabilityMeasure.pi (fun i : I ↦
        shiftedSelectedBetaFactorProbabilityMeasure θ hθ (i : ℕ) N m (hI i)) := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map]
  rw [AEMeasurable.map_map_of_aemeasurable
      (Finset.measurable_restrict I).aemeasurable
      (measurable_finiteSizeBiasedDirichletInputEmbedding (m + N)).aemeasurable]
  have hI' : ∀ i : I, (i : ℕ) < m + N := by
    intro i
    exact lt_of_lt_of_le (hI i) (Nat.le_add_left N m)
  -- Proof comment: the earlier finite-window transport lemma already gives the required product
  -- law once the shifted index `m + N` is frozen.
  simpa [ProbabilityMeasure.toMeasure_pi, shiftedSelectedBetaFactorProbabilityMeasure,
    add_assoc, add_left_comm, add_comm] using
    (map_restrict_finiteSizeBiasedDirichletInputEmbedding_eq_pi θ hθ (n := m + N) I hI')

/-- Helper for Theorem 24.33: every fixed finite restriction of the embedded input law should
converge to the corresponding finite `Beta(1, θ)` product law. -/
private theorem tendsto_finiteWindow_inputEmbeddingLaw
    (θ : ℝ) (hθ : 0 < θ) (I : Finset ℕ) :
    Tendsto
      (fun n ↦
        ProbabilityMeasure.map
          (ProbabilityMeasure.map
            (⟨finiteSizeBiasedDirichletInputMeasure θ n,
              instIsProbabilityMeasureFiniteSizeBiasedDirichletInputMeasure θ hθ n⟩ :
                ProbabilityMeasure (Fin n → ℝ))
            (measurable_finiteSizeBiasedDirichletInputEmbedding n).aemeasurable)
          (Finset.measurable_restrict I).aemeasurable)
      atTop
      (nhds
        (ProbabilityMeasure.pi fun _ : I ↦
          (⟨betaMeasure 1 θ, isProbabilityMeasureBeta zero_lt_one hθ⟩ :
            ProbabilityMeasure ℝ))) := by
  classical
  let N : ℕ := I.sup id + 1
  have hI : ∀ i : I, (i : ℕ) < N := by
    intro i
    have hi_le : (i : ℕ) ≤ I.sup id := by
      exact Finset.le_sup (f := id) i.2
    exact Nat.lt_succ_of_le hi_le
  rw [← tendsto_add_atTop_iff_nat N]
  have hcoords :
      Tendsto
        (fun m : ℕ ↦ fun i : I ↦
          shiftedSelectedBetaFactorProbabilityMeasure θ hθ (i : ℕ) N m (hI i))
        atTop
        (nhds
          (fun _ : I ↦
            (⟨betaMeasure 1 θ, isProbabilityMeasureBeta zero_lt_one hθ⟩ :
              ProbabilityMeasure ℝ))) := by
    rw [tendsto_pi_nhds]
    intro i
    -- Proof comment: each fixed coordinate of the finite window converges by the one-dimensional
    -- weak convergence theorem for the shifted Beta factors.
    simpa using
      (tendsto_shiftedSelectedBetaFactor θ hθ (k := (i : ℕ)) (N := N) (hI i))
  have hpi :
      Tendsto
        (fun m : ℕ ↦
          ProbabilityMeasure.pi (fun i : I ↦
            shiftedSelectedBetaFactorProbabilityMeasure θ hθ (i : ℕ) N m (hI i)))
        atTop
        (nhds
          (ProbabilityMeasure.pi fun _ : I ↦
            (⟨betaMeasure 1 θ, isProbabilityMeasureBeta zero_lt_one hθ⟩ :
              ProbabilityMeasure ℝ))) := by
    -- Proof comment: the finite product map on probability measures is continuous, so
    -- coordinatewise convergence upgrades to convergence of the whole window law.
    exact (ProbabilityMeasure.continuous_pi.tendsto _).comp hcoords
  have hrewrite :
      (fun m : ℕ ↦
        ProbabilityMeasure.map
          (ProbabilityMeasure.map
            (⟨finiteSizeBiasedDirichletInputMeasure θ (m + N),
              instIsProbabilityMeasureFiniteSizeBiasedDirichletInputMeasure θ hθ (m + N)⟩ :
                ProbabilityMeasure (Fin (m + N) → ℝ))
            (measurable_finiteSizeBiasedDirichletInputEmbedding (m + N)).aemeasurable)
          (Finset.measurable_restrict I).aemeasurable) =
        (fun m : ℕ ↦
          ProbabilityMeasure.pi (fun i : I ↦
            shiftedSelectedBetaFactorProbabilityMeasure θ hθ (i : ℕ) N m (hI i))) := by
    funext m
    -- Proof comment: shifting by `N` makes the window law exactly equal to the product of the
    -- shifted scalar factors.
    simpa [N] using windowInputLaw_eq_shiftedSelectedBetaFactorPi θ hθ I hI m
  rw [hrewrite]
  exact hpi

/-- Helper for Theorem 24.33: a cluster point of the embedded finite input laws is determined by
the limiting finite-window product laws. -/
private theorem inputEmbeddingLawClusterPt_eq_of_finiteWindow_tendsto
    (θ : ℝ) (hθ : 0 < θ)
    {Q : ProbabilityMeasure (ℕ → ℝ)}
    (hQ : MapClusterPt Q atTop
      (fun n ↦
        ProbabilityMeasure.map
          (⟨finiteSizeBiasedDirichletInputMeasure θ n,
            instIsProbabilityMeasureFiniteSizeBiasedDirichletInputMeasure θ hθ n⟩ :
              ProbabilityMeasure (Fin n → ℝ))
          (measurable_finiteSizeBiasedDirichletInputEmbedding n).aemeasurable))
    (hfd :
      ∀ I : Finset ℕ,
        Tendsto
          (fun n ↦
            ProbabilityMeasure.map
              (ProbabilityMeasure.map
                (⟨finiteSizeBiasedDirichletInputMeasure θ n,
                  instIsProbabilityMeasureFiniteSizeBiasedDirichletInputMeasure θ hθ n⟩ :
                    ProbabilityMeasure (Fin n → ℝ))
                (measurable_finiteSizeBiasedDirichletInputEmbedding n).aemeasurable)
              (Finset.measurable_restrict I).aemeasurable)
          atTop
          (nhds
            (ProbabilityMeasure.pi fun _ : I ↦
              (⟨betaMeasure 1 θ, isProbabilityMeasureBeta zero_lt_one hθ⟩ :
                ProbabilityMeasure ℝ)))) :
    Q =
      (⟨Measure.infinitePi fun _ : ℕ ↦ betaMeasure 1 θ,
        by
          letI : ∀ _i : ℕ, IsProbabilityMeasure (betaMeasure 1 θ) := fun _ ↦
            isProbabilityMeasureBeta zero_lt_one hθ
          infer_instance⟩ : ProbabilityMeasure (ℕ → ℝ)) := by
  let nu : ℕ → ProbabilityMeasure (ℕ → ℝ) := fun n ↦
    ProbabilityMeasure.map
      (⟨finiteSizeBiasedDirichletInputMeasure θ n,
        instIsProbabilityMeasureFiniteSizeBiasedDirichletInputMeasure θ hθ n⟩ :
          ProbabilityMeasure (Fin n → ℝ))
      (measurable_finiteSizeBiasedDirichletInputEmbedding n).aemeasurable
  let nuLimit : ProbabilityMeasure (ℕ → ℝ) :=
    ⟨Measure.infinitePi fun _ : ℕ ↦ betaMeasure 1 θ,
      by
        letI : ∀ _i : ℕ, IsProbabilityMeasure (betaMeasure 1 θ) := fun _ ↦
          isProbabilityMeasureBeta zero_lt_one hθ
        infer_instance⟩
  obtain ⟨ψ, hψmono, hψtendsto⟩ :=
    TopologicalSpace.FirstCountableTopology.tendsto_subseq hQ
  have hrestrictQ :
      ∀ I : Finset ℕ,
        ProbabilityMeasure.map Q (Finset.measurable_restrict I).aemeasurable =
          ProbabilityMeasure.pi fun _ : I ↦
            (⟨betaMeasure 1 θ, isProbabilityMeasureBeta zero_lt_one hθ⟩ :
              ProbabilityMeasure ℝ) := by
    intro I
    have hQI :
        Tendsto
          (fun k ↦ ProbabilityMeasure.map (nu (ψ k)) (Finset.measurable_restrict I).aemeasurable)
          atTop
          (nhds (ProbabilityMeasure.map Q (Finset.measurable_restrict I).aemeasurable)) :=
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        (fun k ↦ nu (ψ k)) Q hψtendsto (continuous_restrict I)
    have hPI :
        Tendsto
          (fun k ↦ ProbabilityMeasure.map (nu (ψ k)) (Finset.measurable_restrict I).aemeasurable)
          atTop
          (nhds
            (ProbabilityMeasure.pi fun _ : I ↦
              (⟨betaMeasure 1 θ, isProbabilityMeasureBeta zero_lt_one hθ⟩ :
                ProbabilityMeasure ℝ))) :=
      (hfd I).comp hψmono.tendsto_atTop
    -- Proof comment: the restricted subsequence has the same limit seen from the cluster point and
    -- from the already-proved finite-window convergence, so the two limits coincide.
    exact tendsto_nhds_unique hQI hPI
  have hfamily :
      (fun I : Finset ℕ ↦ Measure.map (fun ω : ℕ → ℝ ↦ I.restrict ω) (Q : Measure (ℕ → ℝ))) =
        (fun I : Finset ℕ ↦
          Measure.map (fun ω : ℕ → ℝ ↦ I.restrict ω) (nuLimit : Measure (ℕ → ℝ))) := by
    letI : ∀ i : ℕ, IsProbabilityMeasure ((fun _ : ℕ ↦ betaMeasure 1 θ) i) := fun _ ↦
      isProbabilityMeasureBeta zero_lt_one hθ
    funext I
    have hQI :
        Measure.map (fun ω : ℕ → ℝ ↦ I.restrict ω) (Q : Measure (ℕ → ℝ)) =
          Measure.pi (fun _ : I ↦ betaMeasure 1 θ) := by
      simpa [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_pi] using
        congrArg (fun μ : ProbabilityMeasure (I → ℝ) => (μ : Measure (I → ℝ))) (hrestrictQ I)
    have hnuLimitI :
        Measure.map (fun ω : ℕ → ℝ ↦ I.restrict ω) (nuLimit : Measure (ℕ → ℝ)) =
          Measure.pi (fun _ : I ↦ betaMeasure 1 θ) := by
      let betaPM : ℕ → ProbabilityMeasure ℝ := fun _ ↦
        ⟨betaMeasure 1 θ, isProbabilityMeasureBeta zero_lt_one hθ⟩
      have hmap :
          Measure.map (fun ω : ℕ → ℝ ↦ I.restrict ω) (nuLimit : Measure (ℕ → ℝ)) =
            Measure.pi (fun i : I ↦ (betaPM i : Measure ℝ)) := by
        simpa [nuLimit, betaPM] using
          (Measure.infinitePi_map_restrict (μ := fun i : ℕ ↦ (betaPM i : Measure ℝ)) (I := I))
      simpa [betaPM] using hmap
    exact hQI.trans hnuLimitI.symm
  have hprojQ :
      IsProjectiveLimit
        (Q : Measure (ℕ → ℝ))
        (fun I : Finset ℕ ↦ Measure.map (fun ω : ℕ → ℝ ↦ I.restrict ω) (Q : Measure (ℕ → ℝ))) := by
    simpa using
      (ProbabilityTheory.isProjectiveLimit_map
        (P := (Q : Measure (ℕ → ℝ)))
        (X := fun i (ω : ℕ → ℝ) ↦ ω i)
        (hX := (aemeasurable_id :
          AEMeasurable (fun ω : ℕ → ℝ ↦ ω) (Q : Measure (ℕ → ℝ)))))
  have hprojNuLimit :
      IsProjectiveLimit
        (nuLimit : Measure (ℕ → ℝ))
        (fun I : Finset ℕ ↦
          Measure.map (fun ω : ℕ → ℝ ↦ I.restrict ω) (nuLimit : Measure (ℕ → ℝ))) := by
    simpa [nuLimit] using
      (ProbabilityTheory.isProjectiveLimit_map
        (P := (nuLimit : Measure (ℕ → ℝ)))
        (X := fun i (ω : ℕ → ℝ) ↦ ω i)
        (hX := (aemeasurable_id :
          AEMeasurable (fun ω : ℕ → ℝ ↦ ω) (nuLimit : Measure (ℕ → ℝ)))))
  -- Proof comment: equality of all finite restrictions identifies the full law by uniqueness of
  -- projective limits.
  have hQeq : Q = nuLimit := by
    apply ProbabilityMeasure.toMeasure_injective
    refine hprojQ.unique ?_
    simpa [hfamily] using hprojNuLimit
  simpa [nuLimit] using hQeq

/-- Helper for Theorem 24.33: the embedded finite Beta input laws should converge to the i.i.d.
`Beta(1, θ)` product law on the fixed sequence space `ℕ → ℝ`. -/
theorem tendsto_finiteSizeBiasedDirichletInputEmbeddingLaw
    (θ : ℝ) (hθ : 0 < θ) :
    Tendsto
      (fun n ↦
        ProbabilityMeasure.map
          (⟨finiteSizeBiasedDirichletInputMeasure θ n,
            instIsProbabilityMeasureFiniteSizeBiasedDirichletInputMeasure θ hθ n⟩ :
              ProbabilityMeasure (Fin n → ℝ))
          (measurable_finiteSizeBiasedDirichletInputEmbedding n).aemeasurable)
      atTop
      (nhds
        (⟨Measure.infinitePi fun _ : ℕ ↦ betaMeasure 1 θ,
          by
            letI : ∀ _i : ℕ, IsProbabilityMeasure (betaMeasure 1 θ) := fun _ ↦
              isProbabilityMeasureBeta zero_lt_one hθ
            infer_instance⟩ : ProbabilityMeasure (ℕ → ℝ))) := by
  let nu : ℕ → ProbabilityMeasure (ℕ → ℝ) := fun n ↦
    ProbabilityMeasure.map
      (⟨finiteSizeBiasedDirichletInputMeasure θ n,
        instIsProbabilityMeasureFiniteSizeBiasedDirichletInputMeasure θ hθ n⟩ :
          ProbabilityMeasure (Fin n → ℝ))
      (measurable_finiteSizeBiasedDirichletInputEmbedding n).aemeasurable
  let nuLimit : ProbabilityMeasure (ℕ → ℝ) :=
    ⟨Measure.infinitePi fun _ : ℕ ↦ betaMeasure 1 θ,
      by
        letI : ∀ _i : ℕ, IsProbabilityMeasure (betaMeasure 1 θ) := fun _ ↦
          isProbabilityMeasureBeta zero_lt_one hθ
        infer_instance⟩
  have hfd :
      ∀ I : Finset ℕ,
        Tendsto
          (fun n ↦ ProbabilityMeasure.map (nu n) (Finset.measurable_restrict I).aemeasurable)
          atTop
          (nhds
            (ProbabilityMeasure.pi fun _ : I ↦
              (⟨betaMeasure 1 θ, isProbabilityMeasureBeta zero_lt_one hθ⟩ :
                ProbabilityMeasure ℝ))) := by
    intro I
    simpa [nu] using tendsto_finiteWindow_inputEmbeddingLaw θ hθ I
  have hTightImage :
      IsTightMeasureSet (((↑) : ProbabilityMeasure (ℕ → ℝ) → Measure (ℕ → ℝ)) '' Set.range nu) := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    let K : Set (ℕ → ℝ) := Set.pi Set.univ (fun _ : ℕ ↦ Set.Icc (0 : ℝ) 1)
    refine ⟨K, ?_, ?_⟩
    · -- Proof comment: the common support set is the compact product cube `[0,1]^ℕ`.
      simpa [K] using
        (isCompact_univ_pi fun _ : ℕ ↦ (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)))
    · intro μ hμ
      rcases hμ with ⟨ρ, ⟨n, rfl⟩, rfl⟩
      have hzero : (nu n : Measure (ℕ → ℝ)) Kᶜ = 0 := by
        simpa [nu, K, ProbabilityMeasure.toMeasure_map] using
          finiteSizeBiasedDirichletInputEmbeddingLaw_support_unitCube θ hθ n
      rw [hzero]
      exact bot_le
  have hcompact : IsCompact (closure (Set.range nu)) :=
    isCompact_closure_of_isTightMeasureSet (S := Set.range nu) hTightImage
  have hnu :
      Tendsto nu atTop (nhds nuLimit) := by
    refine hcompact.tendsto_nhds_of_unique_mapClusterPt ?_ ?_
    · exact Filter.Eventually.of_forall fun n ↦ subset_closure ⟨n, rfl⟩
    · intro Q hQmem hQcluster
      exact inputEmbeddingLawClusterPt_eq_of_finiteWindow_tendsto θ hθ hQcluster hfd
  simpa [nu, nuLimit] using hnu

-- Proof sketch: use the convergence of the Beta parameters
-- `Beta(1 + θ/(n+1), θ (n-i)/(n+1)) ⇒ Beta(1, θ)` for each fixed coordinate, combine this with
-- independence of the product input laws, and then apply the continuous mapping theorem to the
-- finite and infinite stick-breaking maps.
/-- Theorem 24.33 (1): the laws of the explicit Beta stick-breaking sequences for the size-biased
order of `Dir_{θ/(n+1);\,n+1}` converge to the limiting `GEM_θ` law; equivalently, the
size-biased reorderings `\widehat X^{\,n}` converge in distribution to the size-biased order of
a `PD_θ` sample once that limit is identified. -/
theorem sizeBiasedSymmetricDirichletLaw_tendsto_gemMeasure
    (θ : ℝ) (hθ : 0 < θ) :
    Tendsto
      (fun n ↦ finiteSizeBiasedDirichletProbabilityMeasure θ hθ n)
      atTop
      (nhds (gemProbabilityMeasure θ hθ)) := by
  let nuLimit : ProbabilityMeasure (ℕ → ℝ) :=
    ⟨Measure.infinitePi fun _ : ℕ ↦ betaMeasure 1 θ,
      by
        letI : ∀ _i : ℕ, IsProbabilityMeasure (betaMeasure 1 θ) := fun _ ↦
          isProbabilityMeasureBeta zero_lt_one hθ
        infer_instance⟩
  have hν :
      Tendsto
        (fun n ↦
          ProbabilityMeasure.map
            (⟨finiteSizeBiasedDirichletInputMeasure θ n,
              instIsProbabilityMeasureFiniteSizeBiasedDirichletInputMeasure θ hθ n⟩ :
                ProbabilityMeasure (Fin n → ℝ))
            (measurable_finiteSizeBiasedDirichletInputEmbedding n).aemeasurable)
        atTop
        (nhds nuLimit) := by
    simpa [nuLimit] using tendsto_finiteSizeBiasedDirichletInputEmbeddingLaw θ hθ
  have hmap :
      Tendsto
        (fun n ↦
          ProbabilityMeasure.map
            (ProbabilityMeasure.map
              (⟨finiteSizeBiasedDirichletInputMeasure θ n,
                instIsProbabilityMeasureFiniteSizeBiasedDirichletInputMeasure θ hθ n⟩ :
                ProbabilityMeasure (Fin n → ℝ))
              (measurable_finiteSizeBiasedDirichletInputEmbedding n).aemeasurable)
            continuous_gemStickBreaking.measurable.aemeasurable)
        atTop
        (nhds
          (ProbabilityMeasure.map nuLimit continuous_gemStickBreaking.measurable.aemeasurable)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n ↦
        ProbabilityMeasure.map
          (⟨finiteSizeBiasedDirichletInputMeasure θ n,
            instIsProbabilityMeasureFiniteSizeBiasedDirichletInputMeasure θ hθ n⟩ :
              ProbabilityMeasure (Fin n → ℝ))
          (measurable_finiteSizeBiasedDirichletInputEmbedding n).aemeasurable)
      nuLimit hν continuous_gemStickBreaking
  have hfinite :
      (fun n ↦
        ProbabilityMeasure.map
          (ProbabilityMeasure.map
            (⟨finiteSizeBiasedDirichletInputMeasure θ n,
              instIsProbabilityMeasureFiniteSizeBiasedDirichletInputMeasure θ hθ n⟩ :
                ProbabilityMeasure (Fin n → ℝ))
            (measurable_finiteSizeBiasedDirichletInputEmbedding n).aemeasurable)
          continuous_gemStickBreaking.measurable.aemeasurable) =
        (fun n ↦ finiteSizeBiasedDirichletProbabilityMeasure θ hθ n) := by
    funext n
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
      finiteSizeBiasedDirichletProbabilityMeasure_toMeasure]
    rw [finiteSizeBiasedDirichletLaw_def]
    rw [AEMeasurable.map_map_of_aemeasurable
      continuous_gemStickBreaking.measurable.aemeasurable
      (measurable_finiteSizeBiasedDirichletInputEmbedding n).aemeasurable]
    congr 1
    funext v
    simpa [Function.comp] using
      (finiteSizeBiasedDirichletStickBreaking_eq_gemStickBreaking n v).symm
  have hlimit :
      ProbabilityMeasure.map nuLimit continuous_gemStickBreaking.measurable.aemeasurable =
        gemProbabilityMeasure θ hθ := by
    apply ProbabilityMeasure.toMeasure_injective
    simp [nuLimit, gemProbabilityMeasure, gemMeasure]
  -- Proof comment: once the input laws live on the fixed sequence space, the continuous-mapping
  -- theorem transfers their convergence through the GEM stick-breaking map.
  simpa [hfinite, hlimit] using hmap

-- Proof sketch: identify the law of the whole Beta input sequence `(V i)_i` with the infinite
-- product `Beta(1, θ)` measure using independence and the coordinate laws, then compose with the
-- measurable stick-breaking map.
/-- An i.i.d. family of `Beta(1, θ)` random variables has the `GEM_θ` law after applying the
infinite stick-breaking map. -/
theorem hasLaw_gemStickBreaking_of_iid_beta
    (θ : ℝ)
    {P : Measure Ω'} [IsProbabilityMeasure P]
    {V : ℕ → Ω' → ℝ}
    (hV_indep : iIndepFun V P)
    (hV_law : ∀ i : ℕ, HasLaw (V i) (betaMeasure 1 θ) P) :
    HasLaw (fun ω ↦ gemStickBreaking (fun i ↦ V i ω)) (gemMeasure θ) P := by
  have hInput :
      HasLaw (fun ω ↦ fun i ↦ V i ω) (Measure.infinitePi fun _ : ℕ ↦ betaMeasure 1 θ) P := by
    refine ⟨?_, ?_⟩
    · -- Coordinatewise laws provide coordinatewise a.e.-measurability of the whole input sequence.
      exact aemeasurable_pi_iff.2 fun i ↦ (hV_law i).aemeasurable
    · -- Independence identifies the joint law with the infinite product of the coordinate laws.
      rw [(iIndepFun_iff_map_fun_eq_infinitePi_map₀' (P := P) (X := V)
        (fun i ↦ (hV_law i).aemeasurable)).1 hV_indep]
      congr 1
      funext i
      exact (hV_law i).map_eq
  refine ⟨?_, ?_⟩
  · -- Composing the measurable GEM map with the input sequence keeps a.e.-measurability.
    exact measurable_gemStickBreakingMap.aemeasurable.comp_aemeasurable hInput.aemeasurable
  · -- Push the joint input law through `gemStickBreaking`, which is exactly the definition of GEM.
    have hcomp :
        (fun ω ↦ gemStickBreaking (fun i ↦ V i ω)) =
          gemStickBreaking ∘ fun ω ↦ fun i ↦ V i ω := rfl
    rw [hcomp, ← AEMeasurable.map_map_of_aemeasurable measurable_gemStickBreakingMap.aemeasurable
      hInput.aemeasurable,
      hInput.map_eq, gemMeasure_def]

-- Proof sketch: first show that the stick-breaking sequence built from the i.i.d. Beta family has
-- law `gemMeasure θ` by identifying the law of the whole input sequence with the product
-- `Beta(1, θ)` measure; then use `HasLaw.identDistrib` to compare it with `Xhat`.
/-- Theorem 24.33 (2): if `X̂` has the limiting `GEM_θ` law and `Z` is the stick-breaking
sequence built from i.i.d. `Beta(1, θ)` variables, then `X̂` and `Z` are identically
distributed; this is the distributional identification `X̂ \overset{\mathcal D}= Z`. -/
theorem identDistrib_gemStickBreaking_of_hasLaw_gemMeasure
    (θ : ℝ)
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {P : Measure Ω'} [IsProbabilityMeasure P]
    {Xhat : Ω → ℕ → ℝ} {V : ℕ → Ω' → ℝ}
    (hXhat : HasLaw Xhat (gemMeasure θ) μ)
    (hV_indep : iIndepFun V P)
    (hV_law : ∀ i : ℕ, HasLaw (V i) (betaMeasure 1 θ) P) :
    IdentDistrib Xhat (fun ω ↦ gemStickBreaking (fun i ↦ V i ω)) μ P := by
  -- Both processes have the same `gemMeasure θ` law, so they are identically distributed.
  exact hXhat.identDistrib (hasLaw_gemStickBreaking_of_iid_beta θ hV_indep hV_law)

end ProbabilityTheory

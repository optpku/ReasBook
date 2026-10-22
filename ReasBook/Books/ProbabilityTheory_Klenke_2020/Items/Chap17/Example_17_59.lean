/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Example_3_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Example_5_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Exercise_7_4_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_53
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory unitInterval

noncomputable section

namespace ProbabilityTheory

/-- Helper for Example 17.59: the product unit-interval law on `Fin n → I`. -/
abbrev uniformCube (n : ℕ) : Measure (Fin n → I) :=
  (ProbabilityMeasure.pi
    (fun _ : Fin n ↦ (⟨(volume : Measure I), inferInstance⟩ : ProbabilityMeasure I)) :
      Measure (Fin n → I))

/-- Helper for Example 17.59: the one-trial threshold count on the unit interval. -/
abbrev thresholdIndicator (p : I) : I → ℕ :=
  fun u ↦ if u ≤ p then 1 else 0

/-- Helper for Example 17.59: on `ℕ`, the initial segment `Set.Iio 1` is the singleton `{0}`. -/
lemma setIioOne_eq_singleton : (Set.Iio 1 : Set ℕ) = {0} := by
  -- Proof comment: `0` is the only natural number strictly below `1`.
  ext x
  simp [Set.mem_Iio]

/-- Helper for Example 17.59: a subset of `Set.Iio 1` is either empty or `{0}`. -/
lemma eq_empty_or_singleton_zero_of_subset_Iio_one {s : Set ℕ} (hs : s ⊆ Set.Iio 1) :
    s = ∅ ∨ s = {0} := by
  -- Proof comment: after rewriting `Set.Iio 1` as `{0}`, only the two obvious subsets remain.
  have hs' : s ⊆ ({0} : Set ℕ) := by
    simpa [setIioOne_eq_singleton] using hs
  by_cases h0 : 0 ∈ s
  · right
    ext x
    constructor
    · intro hx
      have : x = 0 := by
        simpa using hs' hx
      simp [this]
    · intro hx
      have : x = 0 := by simpa using hx
      simpa [this] using h0
  · left
    ext x
    constructor
    · intro hx
      have : x = 0 := by
        simpa using hs' hx
      exact h0 (this ▸ hx)
    · intro hx
      simp at hx

/-- Helper for Example 17.59: the one-trial threshold map is measurable. -/
theorem measurable_thresholdIndicator (p : I) :
    Measurable (thresholdIndicator p) := by
  -- Proof comment: the codomain `ℕ` is discrete, so every nat-valued map is measurable.
  simpa [thresholdIndicator] using
    Measurable.piecewise (s := Set.Iic p) measurableSet_Iic measurable_const measurable_const

/-- Helper for Example 17.59: the one-trial threshold count has the one-trial binomial law. -/
theorem thresholdIndicator_hasLaw_binomialOne (p : I) :
    HasLaw (thresholdIndicator p) (Bin(1, p)) (volume : Measure I) := by
  refine ⟨measurable_thresholdIndicator p |>.aemeasurable, ?_⟩
  -- Proof comment: compare the pushforward law and `Bin(1, p)` on singleton atoms.
  refine Measure.ext_of_singleton fun k ↦ ?_
  by_cases hk0 : k = 0
  · subst hk0
    rw [Measure.map_apply (measurable_thresholdIndicator p) (measurableSet_singleton 0)]
    have hpreimage : thresholdIndicator p ⁻¹' ({0} : Set ℕ) = Set.Ioi p := by
      ext u
      simp [thresholdIndicator]
    rw [hpreimage]
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    rw [unitInterval.volume_Ioi, binomial_apply_singleton_toReal 1 0 p]
    simp [p.2.2]
  · by_cases hk1 : k = 1
    · subst hk1
      rw [Measure.map_apply (measurable_thresholdIndicator p) (measurableSet_singleton 1)]
      have hpreimage : thresholdIndicator p ⁻¹' ({1} : Set ℕ) = Set.Iic p := by
        ext u
        simp [thresholdIndicator]
      rw [hpreimage]
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
      rw [unitInterval.volume_Iic, binomial_apply_singleton_toReal 1 1 p]
      simp [p.2.1]
    · have hk2 : 1 < k := by
        omega
      rw [Measure.map_apply (measurable_thresholdIndicator p) (measurableSet_singleton k)]
      have hpreimage : thresholdIndicator p ⁻¹' ({k} : Set ℕ) = (∅ : Set I) := by
        ext u
        by_cases hu : u ≤ p <;> simp [thresholdIndicator, hu, hk0, hk1, eq_comm]
      rw [hpreimage, measure_empty]
      rw [← ENNReal.ofReal_zero]
      rw [← ENNReal.toReal_eq_toReal_iff' ENNReal.ofReal_ne_top (measure_ne_top _ _)]
      rw [binomial_apply_singleton_toReal 1 k p]
      have hchoose : Nat.choose 1 k = 0 := Nat.choose_eq_zero_of_lt hk2
      simp [hchoose]

/-- Helper for Example 17.59: the tail component of
`MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ I) 0` is the usual successor tail. -/
lemma piFinSuccAboveZeroSndEqSuccTailI (n : ℕ) :
    Prod.snd ∘ MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ I) 0 =
      fun y : Fin (n + 1) → I ↦ fun i : Fin n ↦ y i.succ := by
  -- Proof comment: the standard split equivalence removes the zero coordinate and leaves the
  -- remaining coordinates in successor order.
  funext y
  funext i
  simp [Fin.tail]

/-- Helper for Example 17.59: splitting off the zero coordinate sends `uniformCube (n + 1)` to the
product law of the head coordinate and the successor tail. -/
lemma uniformCube_map_piFinSuccAboveZero (n : ℕ) :
    (uniformCube (n + 1)).map (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ I) 0) =
      (volume : Measure I).prod (uniformCube n) := by
  -- Proof comment: this is the canonical `piFinSuccAbove` measure-preserving split specialized to
  -- the unit-interval product law.
  simpa [uniformCube, Fin.zero_succAbove] using
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ (volume : Measure I)) 0).map_eq

/-- The number of coordinates among `n` unit-interval samples that fall below the threshold `p`. -/
def binomialUniformCount (n : ℕ) (p : I) : (Fin n → I) → ℕ :=
  fun y ↦ ∑ i, if y i ≤ p then 1 else 0

-- Proof sketch: each summand `y ↦ if y i ≤ p then 1 else 0` is measurable because evaluation at a
-- coordinate is measurable and `ℕ` carries the discrete measurable space; finite sums preserve
-- measurability.
/-- The threshold-count map is measurable on the finite unit cube `I^n`. -/
theorem measurable_binomialUniformCount (n : ℕ) (p : I) :
    Measurable (binomialUniformCount n p) := by
  -- Proof comment: each `0/1` summand is measurable, and finite sums preserve measurability.
  classical
  simpa [binomialUniformCount] using
    Finset.measurable_sum Finset.univ fun i _ ↦
      Measurable.piecewise
        (measurableSet_setOf.2 <| by fun_prop)
        measurable_const
        measurable_const

/-- Helper for Example 17.59: separating the first coordinate turns the `(n + 1)`-count into a
one-trial count plus the tail `n`-count. -/
theorem binomialUniformCount_succ (n : ℕ) (p : I) (y : Fin (n + 1) → I) :
    binomialUniformCount (n + 1) p y =
      thresholdIndicator p (y 0) + binomialUniformCount n p (fun i ↦ y (Fin.succ i)) := by
  -- Proof comment: split the finite sum into the zero coordinate and the remaining tail.
  rw [binomialUniformCount, Fin.sum_univ_succ]
  simp [thresholdIndicator, binomialUniformCount]

/-- Helper for Example 17.59: after rebuilding from the `piFinSuccAbove` split, the threshold count
is the head indicator plus the tail count. -/
theorem binomialUniformCountSplitSymm (n : ℕ) (p : I) (u : I) (y : Fin n → I) :
    binomialUniformCount (n + 1) p
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ I) 0).symm (u, y)) =
      thresholdIndicator p u + binomialUniformCount n p y := by
  let split : (Fin (n + 1) → I) ≃ᵐ I × (Fin n → I) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ I) 0
  have hfst : (split.symm (u, y)) 0 = u := by
    simp [split]
  have hsnd : (fun i : Fin n ↦ (split.symm (u, y)) i.succ) = y := by
    calc
      (fun i : Fin n ↦ (split.symm (u, y)) i.succ)
        = Prod.snd (split (split.symm (u, y))) := by
            symm
            simpa [Function.comp] using
              congrFun (piFinSuccAboveZeroSndEqSuccTailI n) (split.symm (u, y))
      _ = y := by
            exact congrArg Prod.snd (split.apply_symm_apply (u, y))
  -- Proof comment: the split equivalence restores the zero coordinate as `u` and the successor
  -- tail as `y`.
  change
    binomialUniformCount (n + 1) p (split.symm (u, y)) =
      thresholdIndicator p u + binomialUniformCount n p y
  calc
    binomialUniformCount (n + 1) p (split.symm (u, y))
      = thresholdIndicator p ((split.symm (u, y)) 0) +
          binomialUniformCount n p (fun i : Fin n ↦ (split.symm (u, y)) i.succ) :=
            binomialUniformCount_succ n p (split.symm (u, y))
    _ = thresholdIndicator p u + binomialUniformCount n p y := by
          rw [hfst, hsnd]

/-- Helper for Example 17.59: if the `n`-coordinate threshold count has law `Bin(n, p)`, then the
`(n + 1)`-coordinate threshold count has law `Bin(n + 1, p)`. -/
theorem hasLaw_binomialUniformCount_succ (n : ℕ) (p : I)
    (ih : HasLaw (binomialUniformCount n p) (Bin(n, p)) (uniformCube n)) :
    HasLaw (binomialUniformCount (n + 1) p) (Bin(n + 1, p))
      (uniformCube (n + 1)) := by
  let split : (Fin (n + 1) → I) ≃ᵐ I × (Fin n → I) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ I) 0
  have hSplit :
      HasLaw split ((volume : Measure I).prod (uniformCube n)) (uniformCube (n + 1)) := by
    -- Proof comment: cache the split law once so later compositions stay in product form.
    refine ⟨split.measurable.aemeasurable, uniformCube_map_piFinSuccAboveZero n⟩
  have hHead :
      HasLaw (fun z : I × (Fin n → I) ↦ thresholdIndicator p z.1) (Bin(1, p))
        ((volume : Measure I).prod (uniformCube n)) := by
    -- Proof comment: the first coordinate under the product law is uniform on `I`.
    simpa [Function.comp] using
      HasLaw.comp (thresholdIndicator_hasLaw_binomialOne p)
        ((measurePreserving_fst (μ := (volume : Measure I)) (ν := uniformCube n)).hasLaw)
  have hTail :
      HasLaw (fun z : I × (Fin n → I) ↦ binomialUniformCount n p z.2) (Bin(n, p))
        ((volume : Measure I).prod (uniformCube n)) := by
    -- Proof comment: the tail coordinates still follow the `n`-dimensional uniform cube law.
    simpa [Function.comp] using
      HasLaw.comp ih
        ((measurePreserving_snd (μ := (volume : Measure I)) (ν := uniformCube n)).hasLaw)
  have hIndep :
      (fun z : I × (Fin n → I) ↦ thresholdIndicator p z.1) ⟂ᵢ[(volume : Measure I).prod
        (uniformCube n)] (fun z : I × (Fin n → I) ↦ binomialUniformCount n p z.2) := by
    -- Proof comment: on a product space, the head coordinate and the successor tail are
    -- independent.
    exact indepFun_prod (measurable_thresholdIndicator p) (measurable_binomialUniformCount n p)
  have hSum :
      HasLaw
        (fun z : I × (Fin n → I) ↦ thresholdIndicator p z.1 + binomialUniformCount n p z.2)
        (Bin(1, p) ∗ Bin(n, p))
        ((volume : Measure I).prod (uniformCube n)) :=
    hIndep.hasLaw_add hHead hTail
  have hSplitCount :
      HasLaw
        (fun y : Fin (n + 1) → I ↦
          thresholdIndicator p (split y).1 + binomialUniformCount n p (split y).2)
        (Bin(1, p) ∗ Bin(n, p))
        (uniformCube (n + 1)) :=
    HasLaw.comp hSum hSplit
  have hCountEq :
      (fun y : Fin (n + 1) → I ↦ binomialUniformCount (n + 1) p y) =ᵐ[uniformCube (n + 1)]
        (fun y : Fin (n + 1) → I ↦
          thresholdIndicator p (split y).1 + binomialUniformCount n p (split y).2) := by
    -- Proof comment: after rewriting through `split`, the successor count is literally the head
    -- indicator plus the tail count.
    refine Filter.Eventually.of_forall fun y ↦ ?_
    calc
      binomialUniformCount (n + 1) p y
        = binomialUniformCount (n + 1) p (split.symm (split y)) := by
            rw [split.symm_apply_apply y]
      _ = thresholdIndicator p (split y).1 + binomialUniformCount n p (split y).2 := by
            simpa [split] using binomialUniformCountSplitSymm n p (split y).1 (split y).2
  have hCountConv :
      HasLaw (binomialUniformCount (n + 1) p) (Bin(1, p) ∗ Bin(n, p))
        (uniformCube (n + 1)) :=
    hSplitCount.congr hCountEq
  refine ⟨hCountConv.aemeasurable, ?_⟩
  -- Proof comment: the one-trial and `n`-trial binomial laws convolve to `Bin(n + 1, p)`.
  simpa [Nat.add_comm] using
    hCountConv.map_eq.trans (example_3_4_binomial_conv 1 n p)

-- Proof sketch: the random set `{i < n | Y_i ≤ p}` is `p`-Bernoulli on `Set.Iio n` under the
-- product unit-interval law, and its cardinality is exactly `binomialUniformCount n p`; mapping by
-- the cardinality recovers the canonical binomial law `Bin(n, p)`.
/-- Counting i.i.d. unit-interval uniforms below a threshold `p` gives the binomial law
`Bin(n, p)`. -/
theorem hasLaw_binomialUniformCount (n : ℕ) (p : I) :
    HasLaw (binomialUniformCount n p) (Bin(n, p))
      (uniformCube n) := by
  induction n with
  | zero =>
      have hZero : HasLaw (fun _ : Fin 0 → I ↦ (0 : ℕ)) (Measure.dirac 0) (uniformCube 0) := by
        refine ⟨measurable_const.aemeasurable, ?_⟩
        -- Proof comment: the empty product measure and the zero-trial binomial law are both
        -- supported on their unique point.
        simp [uniformCube]
      simpa [binomialUniformCount, binomial_zero_left (p := p)] using hZero
  | succ n ih =>
      -- Proof comment: hand the full successor-step transport to a separate helper to keep the
      -- induction theorem small and stable.
      simpa using hasLaw_binomialUniformCount_succ n p ih

/-- Helper for Example 17.59: independent threshold counts on two blocks of sizes `m` and `d`
add up to `Bin(m + d, p)`. -/
lemma hasLaw_binomialUniformCountAdd (m d : ℕ) (p : I) :
    HasLaw
      (fun yz : (Fin m → I) × (Fin d → I) ↦
        binomialUniformCount m p yz.1 + binomialUniformCount d p yz.2)
      (Bin(m + d, p))
      ((uniformCube m).prod (uniformCube d)) := by
  have hLeft :
      HasLaw (fun yz : (Fin m → I) × (Fin d → I) ↦ binomialUniformCount m p yz.1) (Bin(m, p))
        ((uniformCube m).prod (uniformCube d)) := by
    -- Proof comment: the left block keeps its original `m`-trial binomial law under `Prod.fst`.
    simpa [Function.comp] using
      HasLaw.comp (hasLaw_binomialUniformCount m p)
        ((measurePreserving_fst (μ := uniformCube m) (ν := uniformCube d)).hasLaw)
  have hRight :
      HasLaw (fun yz : (Fin m → I) × (Fin d → I) ↦ binomialUniformCount d p yz.2) (Bin(d, p))
        ((uniformCube m).prod (uniformCube d)) := by
    -- Proof comment: the right block keeps its original `d`-trial binomial law under `Prod.snd`.
    simpa [Function.comp] using
      HasLaw.comp (hasLaw_binomialUniformCount d p)
        ((measurePreserving_snd (μ := uniformCube m) (ν := uniformCube d)).hasLaw)
  have hIndep :
      (fun yz : (Fin m → I) × (Fin d → I) ↦ binomialUniformCount m p yz.1) ⟂ᵢ[
        (uniformCube m).prod (uniformCube d)]
        (fun yz : (Fin m → I) × (Fin d → I) ↦ binomialUniformCount d p yz.2) := by
    -- Proof comment: the two blocks live on different coordinates of the product cube.
    exact indepFun_prod (measurable_binomialUniformCount m p)
      (measurable_binomialUniformCount d p)
  have hSum :
      HasLaw
        (fun yz : (Fin m → I) × (Fin d → I) ↦
          binomialUniformCount m p yz.1 + binomialUniformCount d p yz.2)
        (Bin(m, p) ∗ Bin(d, p))
        ((uniformCube m).prod (uniformCube d)) :=
    hIndep.hasLaw_add hLeft hRight
  refine ⟨hSum.aemeasurable, ?_⟩
  -- Proof comment: collapse the convolution of the two block laws to the larger binomial law.
  simpa using hSum.map_eq.trans (example_3_4_binomial_conv m d p)

-- Proof sketch: if `p₁ ≤ p₂`, then every coordinate contributing to the count at threshold `p₁`
-- also contributes at threshold `p₂`; comparing the summands termwise yields the inequality of the
-- total counts.
/-- Raising the threshold from `p₁` to `p₂` can only increase the threshold count. -/
theorem binomialUniformCount_mono (n : ℕ) {p₁ p₂ : I} (hp : p₁ ≤ p₂) (y : Fin n → I) :
    binomialUniformCount n p₁ y ≤ binomialUniformCount n p₂ y := by
  -- Proof comment: compare the `0/1` summands coordinatewise and sum the inequalities.
  refine Finset.sum_le_sum fun i _ ↦ ?_
  by_cases h1 : y i ≤ p₁
  · have h2 : y i ≤ p₂ := le_trans h1 hp
    simp [h1, h2]
  · by_cases h2 : y i ≤ p₂
    · simp [h1, h2]
    · simp [h1, h2]

-- Proof sketch: pair the two measurable count maps `binomialUniformCount n p₁` and
-- `binomialUniformCount n p₂`; measurability is preserved under products.
/-- The simultaneous threshold-count map is measurable on the finite unit cube `I^n`. -/
theorem measurable_binomialUniformCountPair (n : ℕ) (p₁ p₂ : I) :
    Measurable
      (fun y : Fin n → I ↦ (binomialUniformCount n p₁ y, binomialUniformCount n p₂ y)) := by
  -- Proof comment: both coordinate count maps are measurable, so their product is measurable.
  exact (measurable_binomialUniformCount n p₁).prodMk (measurable_binomialUniformCount n p₂)

/-- The canonical coupling of `Bin(n, p₁)` and `Bin(n, p₂)` obtained by counting the same
independent unit-interval uniforms below the two thresholds. -/
def binomialSuccessParameterCoupling (n : ℕ) (p₁ p₂ : I) : ProbabilityMeasure (ℕ × ℕ) :=
  ProbabilityMeasure.map
    (ProbabilityMeasure.pi
      (fun _ : Fin n ↦ (⟨(volume : Measure I), inferInstance⟩ : ProbabilityMeasure I)))
    (measurable_binomialUniformCountPair n p₁ p₂).aemeasurable

-- Proof sketch: push forward the product unit-interval law by the paired count map
-- `fun y ↦ (binomialUniformCount n p₁ y, binomialUniformCount n p₂ y)`; the two marginals are
-- identified using
-- `hasLaw_binomialUniformCount`, and the almost-sure order follows from the pointwise monotonicity
-- `binomialUniformCount_mono`.
/-- Example 17.59: if `0 ≤ p₁ ≤ p₂ ≤ 1`, then counting the same independent uniform random
variables below the two thresholds produces a coupling of `Bin(n, p₁)` and `Bin(n, p₂)` supported
on the order relation `x₁ ≤ x₂`; hence `Bin(n, p₁)` is stochastically dominated by
`Bin(n, p₂)`. -/
theorem binomial_success_parameter_coupling (n : ℕ) {p₁ p₂ : I} (hp : p₁ ≤ p₂) :
    IsCoupling (binomialSuccessParameterCoupling n p₁ p₂)
      ⟨Bin(n, p₁), inferInstance⟩
      ⟨Bin(n, p₂), inferInstance⟩ ∧
    ∀ᵐ z ∂ (binomialSuccessParameterCoupling n p₁ p₂ : Measure (ℕ × ℕ)), z.1 ≤ z.2 := by
  let pairCount : (Fin n → I) → ℕ × ℕ :=
    fun y ↦ (binomialUniformCount n p₁ y, binomialUniformCount n p₂ y)
  have hPairCountLaw :
      HasLaw pairCount (binomialSuccessParameterCoupling n p₁ p₂ : Measure (ℕ × ℕ))
        (uniformCube n) := by
    refine ⟨(measurable_binomialUniformCountPair n p₁ p₂).aemeasurable, ?_⟩
    rw [binomialSuccessParameterCoupling, ProbabilityMeasure.toMeasure_map]
  have hLeMeas : Measurable (fun z : ℕ × ℕ ↦ z.1 ≤ z.2) := by
    fun_prop
  constructor
  · refine (ProbabilityTheory.isCoupling_iff _ _ _).2 ?_
    constructor
    · apply ProbabilityMeasure.toMeasure_injective
      -- Proof comment: the first marginal is the `p₁` threshold count law.
      calc
        Measure.map Prod.fst (binomialSuccessParameterCoupling n p₁ p₂ : Measure (ℕ × ℕ))
            = Measure.map (Prod.fst ∘ pairCount) (uniformCube n) := by
                rw [← hPairCountLaw.map_eq]
                rw [Measure.map_map measurable_fst
                  (measurable_binomialUniformCountPair n p₁ p₂)]
        _ = Bin(n, p₁) := by
            simpa [pairCount, Function.comp] using (hasLaw_binomialUniformCount n p₁).map_eq
    · apply ProbabilityMeasure.toMeasure_injective
      -- Proof comment: the second marginal is the `p₂` threshold count law.
      calc
        Measure.map Prod.snd (binomialSuccessParameterCoupling n p₁ p₂ : Measure (ℕ × ℕ))
            = Measure.map (Prod.snd ∘ pairCount) (uniformCube n) := by
                rw [← hPairCountLaw.map_eq]
                rw [Measure.map_map measurable_snd
                  (measurable_binomialUniformCountPair n p₁ p₂)]
        _ = Bin(n, p₂) := by
            simpa [pairCount, Function.comp] using (hasLaw_binomialUniformCount n p₂).map_eq
  · -- Proof comment: the support condition is transported from the pointwise monotonicity of the
    -- two counts on the common sample `y`.
    exact (hPairCountLaw.ae_iff hLeMeas).mp <|
      Filter.Eventually.of_forall fun y ↦ binomialUniformCount_mono n hp y

-- Proof sketch: realize `Bin(n, p)` by counting threshold hits in `n` common unit-interval
-- samples and `Bin(m, p)` by counting only the first `m` of those same samples; the first count
-- is pointwise bounded by the second, so the induced laws admit an increasing coupling.
/-- For fixed success parameter `p`, binomial laws are stochastically monotone in the number of
trials: if `m ≤ n`, then `Bin(m, p)` admits an increasing coupling with `Bin(n, p)`. -/
theorem binomial_monotone_in_number_of_trials {m n : ℕ} (hmn : m ≤ n) (p : I) :
    ∃ μ : ProbabilityMeasure (ℕ × ℕ),
      IsCoupling μ ⟨Bin(m, p), inferInstance⟩ ⟨Bin(n, p), inferInstance⟩ ∧
        ∀ᵐ z ∂ (μ : Measure (ℕ × ℕ)), z.1 ≤ z.2 := by
  let pairCount : (Fin m → I) × (Fin (n - m) → I) → ℕ × ℕ :=
    fun yz ↦
      (binomialUniformCount m p yz.1,
        binomialUniformCount m p yz.1 + binomialUniformCount (n - m) p yz.2)
  have hPairCountMeas : Measurable pairCount := by
    -- Proof comment: both block counts are measurable, and so is their paired sum.
    refine ((measurable_binomialUniformCount m p).comp measurable_fst).prodMk ?_
    exact ((measurable_binomialUniformCount m p).comp measurable_fst).add
      ((measurable_binomialUniformCount (n - m) p).comp measurable_snd)
  let μ : ProbabilityMeasure (ℕ × ℕ) :=
    ProbabilityMeasure.map
      (⟨(uniformCube m).prod (uniformCube (n - m)), inferInstance⟩ :
        ProbabilityMeasure ((Fin m → I) × (Fin (n - m) → I)))
      hPairCountMeas.aemeasurable
  have hPairCountLaw :
      HasLaw pairCount (μ : Measure (ℕ × ℕ))
        ((uniformCube m).prod (uniformCube (n - m))) := by
    refine ⟨hPairCountMeas.aemeasurable, ?_⟩
    exact
      (ProbabilityMeasure.toMeasure_map
        (⟨(uniformCube m).prod (uniformCube (n - m)), inferInstance⟩ :
          ProbabilityMeasure ((Fin m → I) × (Fin (n - m) → I)))
        hPairCountMeas.aemeasurable).symm
  have hLeft :
      HasLaw (fun yz : (Fin m → I) × (Fin (n - m) → I) ↦ binomialUniformCount m p yz.1)
        (Bin(m, p))
        ((uniformCube m).prod (uniformCube (n - m))) := by
    -- Proof comment: the first block alone still has the `m`-trial binomial law.
    simpa [Function.comp] using
      HasLaw.comp (hasLaw_binomialUniformCount m p)
        ((measurePreserving_fst (μ := uniformCube m)
          (ν := uniformCube (n - m))).hasLaw)
  have hRight :
      HasLaw
        (fun yz : (Fin m → I) × (Fin (n - m) → I) ↦
          binomialUniformCount m p yz.1 + binomialUniformCount (n - m) p yz.2)
        (Bin(m + (n - m), p))
        ((uniformCube m).prod (uniformCube (n - m))) := by
    -- Proof comment: counting both blocks gives the binomial law for the total number of trials.
    simpa using hasLaw_binomialUniformCountAdd m (n - m) p
  have hLeMeas : Measurable (fun z : ℕ × ℕ ↦ z.1 ≤ z.2) := by
    fun_prop
  refine ⟨μ, ?_⟩
  constructor
  · refine (ProbabilityTheory.isCoupling_iff _ _ _).2 ?_
    constructor
    · apply ProbabilityMeasure.toMeasure_injective
      -- Proof comment: the first marginal forgets the second block and keeps the `m`-trial law.
      calc
        Measure.map Prod.fst (μ : Measure (ℕ × ℕ))
            = Measure.map (Prod.fst ∘ pairCount) ((uniformCube m).prod (uniformCube (n - m))) := by
                rw [← hPairCountLaw.map_eq]
                rw [Measure.map_map measurable_fst hPairCountMeas]
        _ = Bin(m, p) := by
            simpa [pairCount, Function.comp] using hLeft.map_eq
    · apply ProbabilityMeasure.toMeasure_injective
      -- Proof comment: the second marginal counts both blocks, hence has the `n`-trial law.
      calc
        Measure.map Prod.snd (μ : Measure (ℕ × ℕ))
            = Measure.map (Prod.snd ∘ pairCount) ((uniformCube m).prod (uniformCube (n - m))) := by
                rw [← hPairCountLaw.map_eq]
                rw [Measure.map_map measurable_snd hPairCountMeas]
        _ = Bin(n, p) := by
            simpa [pairCount, Function.comp, Nat.add_sub_of_le hmn] using hRight.map_eq
  · -- Proof comment: the first block count is pointwise bounded by the sum of the two block
    -- counts.
    exact (hPairCountLaw.ae_iff hLeMeas).mp <|
      Filter.Eventually.of_forall fun yz ↦ by
        have :
            binomialUniformCount m p yz.1 ≤
              binomialUniformCount m p yz.1 + binomialUniformCount (n - m) p yz.2 := by
          omega
        simp [pairCount] at this ⊢

end ProbabilityTheory

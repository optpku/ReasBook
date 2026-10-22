/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Probability.Distributions.Beta

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

noncomputable section

namespace ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The cylinder event that the first `n` weighted-urn draws match the prescribed Boolean prefix
`x`, with `true` encoding black and `false` encoding red. -/
def weightedUrnPrefixEvent (X : ℕ → Ω → Bool) {n : ℕ} (x : Fin n → Bool) : Set Ω :=
  {ω | ∀ i : Fin n, X i ω = x i}

/-- The number of black draws in the Boolean prefix `x`. -/
def blackPrefixCount {n : ℕ} (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i : Fin n ↦ x i = true).card

/-- Helper for Exercise 17.3.2: a prefix cylinder is measurable once each coordinate of the
underlying Boolean process is measurable. -/
theorem measurableSet_weightedUrnPrefixEvent
    {X : ℕ → Ω → Bool} (hX : ∀ n : ℕ, Measurable (X n)) {n : ℕ} (x : Fin n → Bool) :
    MeasurableSet (weightedUrnPrefixEvent X x) := by
  -- Proof comment: rewrite the prefix cylinder as the intersection of the measurable coordinate
  -- fibers `{ω | X i ω = x i}`.
  have hset :
      {ω | ∀ i : Fin n, X i ω = x i} = ⋂ i : Fin n, {ω | X i ω = x i} := by
    ext ω
    simp
  rw [weightedUrnPrefixEvent, hset]
  exact MeasurableSet.iInter fun i : Fin n ↦
    (hX i) (measurableSet_singleton (x i))

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 17.3.2: adjoining one last Boolean value to a prefix cylinder means
intersecting with the corresponding next-coordinate event. -/
theorem weightedUrnPrefixEvent_snoc
    {X : ℕ → Ω → Bool} {n : ℕ} (x : Fin n → Bool) (b : Bool) :
    weightedUrnPrefixEvent X (Fin.snoc x b) =
      weightedUrnPrefixEvent X x ∩ {ω | X n ω = b} := by
  -- Proof comment: split the `Fin (n + 1)` quantifier into the old prefix coordinates and the
  -- last coordinate.
  ext ω
  simp [weightedUrnPrefixEvent, Fin.forall_iff_castSucc, and_comm]

/-- Helper for Exercise 17.3.2: the black-prefix count is the sum of the `0/1` indicators of the
black entries in the prefix. -/
theorem blackPrefixCount_eq_sum_indicator
    {n : ℕ} (x : Fin n → Bool) :
    blackPrefixCount x = ∑ i : Fin n, if x i = true then 1 else 0 := by
  classical
  -- Proof comment: filtering `Finset.univ` by the black coordinates is equivalent to summing the
  -- associated indicator function.
  simp [blackPrefixCount]

/-- Helper for Exercise 17.3.2: appending a black draw increments the black-prefix count by `1`. -/
theorem blackPrefixCount_snoc_true
    {n : ℕ} (x : Fin n → Bool) :
    blackPrefixCount (Fin.snoc x true) = blackPrefixCount x + 1 := by
  -- Proof comment: split the successor-index sum into the old coordinates and the last one.
  rw [blackPrefixCount_eq_sum_indicator, blackPrefixCount_eq_sum_indicator, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last, add_comm]

/-- Helper for Exercise 17.3.2: appending a red draw leaves the black-prefix count unchanged. -/
theorem blackPrefixCount_snoc_false
    {n : ℕ} (x : Fin n → Bool) :
    blackPrefixCount (Fin.snoc x false) = blackPrefixCount x := by
  -- Proof comment: the last Boolean indicator vanishes when the appended color is red.
  rw [blackPrefixCount_eq_sum_indicator, blackPrefixCount_eq_sum_indicator, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last, add_comm]

/-- Helper for Exercise 17.3.2: a Boolean prefix can contain at most `n` black entries. -/
theorem blackPrefixCount_le
    {n : ℕ} (x : Fin n → Bool) :
    blackPrefixCount x ≤ n := by
  classical
  -- Proof comment: the filtered set of black indices is a subset of the full `Fin n`.
  simpa [blackPrefixCount] using
    (Finset.card_filter_le (s := Finset.univ) (p := fun i : Fin n ↦ x i = true))

/-- The source-facing owner predicate for the generalized two-color weighted Pólya urn: every
coordinate is measurable, and each one-step black-cylinder probability is the textbook weight ratio
determined by the current number of black draws. -/
def IsGeneralizedPolyaUrnWithWeights
    (μ : Measure Ω) (w : ℕ → NNReal) (X : ℕ → Ω → Bool) : Prop :=
  (∀ n : ℕ, Measurable (X n)) ∧
    ∀ ⦃n : ℕ⦄ (x : Fin n → Bool),
      let ℓ := blackPrefixCount x
      μ (weightedUrnPrefixEvent X x ∩ {ω | X n ω = true}) =
        (((w ℓ) / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞) * μ (weightedUrnPrefixEvent X x)

namespace IsGeneralizedPolyaUrnWithWeights

variable {μ : Measure Ω} {w : ℕ → NNReal} {X : ℕ → Ω → Bool}

/-- Every coordinate of a generalized weighted Pólya-urn draw sequence is measurable. -/
theorem measurable
    (hX : IsGeneralizedPolyaUrnWithWeights μ w X) (n : ℕ) :
    Measurable (X n) :=
  hX.1 n

/-- The defining one-step black-cylinder formula of a generalized weighted Pólya urn. -/
theorem prefixEvent_inter_true_eq
    (hX : IsGeneralizedPolyaUrnWithWeights μ w X) {n : ℕ} (x : Fin n → Bool) :
    let ℓ := blackPrefixCount x
    μ (weightedUrnPrefixEvent X x ∩ {ω | X n ω = true}) =
      (((w ℓ) / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞) * μ (weightedUrnPrefixEvent X x) :=
  hX.2 x

/-- Helper for Exercise 17.3.2: the complementary one-step red-cylinder probability has the
expected symmetric weight ratio. -/
theorem prefixEvent_inter_false_eq
    [IsFiniteMeasure μ] (hX : IsGeneralizedPolyaUrnWithWeights μ w X) (hw_pos : ∀ n : ℕ, 0 < w n)
    {n : ℕ} (x : Fin n → Bool) :
    μ (weightedUrnPrefixEvent X x ∩ {ω | X n ω = false}) =
      (((w (n - blackPrefixCount x)) /
          (w (blackPrefixCount x) + w (n - blackPrefixCount x)) : NNReal) : ℝ≥0∞) *
        μ (weightedUrnPrefixEvent X x) := by
  set ℓ : ℕ := blackPrefixCount x
  set prefixEvent : Set Ω := weightedUrnPrefixEvent X x
  set truePart : Set Ω := prefixEvent ∩ {ω | X n ω = true}
  set falsePart : Set Ω := prefixEvent ∩ {ω | X n ω = false}
  have hprefix_meas : MeasurableSet prefixEvent :=
    measurableSet_weightedUrnPrefixEvent hX.measurable x
  have hfalse_meas : MeasurableSet falsePart := by
    -- Proof comment: the red branch is the prefix cylinder intersected with the measurable
    -- one-step fiber `{ω | X n ω = false}`.
    exact hprefix_meas.inter ((hX.measurable n) (measurableSet_singleton false))
  have hUnion : truePart ∪ falsePart = prefixEvent := by
    -- Proof comment: on the next draw, the Boolean-valued process must choose either `true`
    -- or `false`.
    ext ω
    by_cases hω : X n ω = true
    · simp [truePart, falsePart, prefixEvent, hω]
    · have hω' : X n ω = false := by
        cases hXn : X n ω <;> simp_all
      simp [truePart, falsePart, prefixEvent, hω]
  have hDisj : Disjoint truePart falsePart := by
    -- Proof comment: the next draw cannot simultaneously be `true` and `false`.
    refine Set.disjoint_left.2 ?_
    intro ω hω_true hω_false
    have htf : true = false := hω_true.2.symm.trans hω_false.2
    cases htf
  have hsum :
      μ prefixEvent = μ truePart + μ falsePart := by
    -- Proof comment: the prefix mass splits as the sum of the two disjoint next-step branches.
    simpa [hUnion, truePart, falsePart, prefixEvent] using (measure_union hDisj hfalse_meas)
  have hle : ℓ ≤ n := by
    simpa [ℓ] using blackPrefixCount_le x
  have htrue :
      μ truePart =
        (((w ℓ) / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞) * μ prefixEvent := by
    -- Proof comment: the `true` branch is the defining owner formula.
    simpa [truePart, prefixEvent, ℓ] using hX.prefixEvent_inter_true_eq x
  have hden_pos : 0 < w ℓ + w (n - ℓ) := by
    exact add_pos (hw_pos ℓ) (hw_pos (n - ℓ))
  have hden_ne : w ℓ + w (n - ℓ) ≠ 0 := ne_of_gt hden_pos
  have hratio_nn :
      w ℓ / (w ℓ + w (n - ℓ)) + w (n - ℓ) / (w ℓ + w (n - ℓ)) = 1 := by
    -- Proof comment: the two complementary branch ratios add up to `1`.
    rw [← add_div]
    simp [hden_ne]
  have hratio :
      (((w ℓ / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞) +
          ((w (n - ℓ) / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞)) = 1 := by
    exact_mod_cast hratio_nn
  have hfactor :
      μ prefixEvent =
        (((w ℓ / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞) * μ prefixEvent +
          ((w (n - ℓ) / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞) * μ prefixEvent) := by
    -- Proof comment: multiplying the ratio identity by the common prefix mass reconstructs the
    -- total cylinder measure.
    calc
      μ prefixEvent = (1 : ℝ≥0∞) * μ prefixEvent := by simp
      _ =
          ((((w ℓ / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞) +
              ((w (n - ℓ) / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞)) * μ prefixEvent) := by
            rw [hratio]
      _ =
          (((w ℓ / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞) * μ prefixEvent +
            ((w (n - ℓ) / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞) * μ prefixEvent) := by
            rw [add_mul]
  have hcancel :
      μ falsePart =
        ((w (n - ℓ) / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞) * μ prefixEvent := by
    have hsum' :
        ((w ℓ / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞) * μ prefixEvent + μ falsePart =
          ((w ℓ / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞) * μ prefixEvent +
            ((w (n - ℓ) / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞) * μ prefixEvent := by
      -- Proof comment: rewrite the branch decomposition using the defining `true`-branch
      -- formula, then compare it with the factorized ratio decomposition.
      calc
        ((w ℓ / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞) * μ prefixEvent + μ falsePart =
            μ prefixEvent := by
          simpa [htrue] using hsum.symm
        _ =
            ((w ℓ / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞) * μ prefixEvent +
              ((w (n - ℓ) / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞) * μ prefixEvent := hfactor
    have hcoeff_ne_top :
        (((w ℓ / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞)) ≠ ∞ := by
      simp
    have hprefix_ne_top : μ prefixEvent ≠ ∞ := measure_ne_top μ prefixEvent
    have hleft_ne_top :
        ((w ℓ / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞) * μ prefixEvent ≠ ∞ :=
      ENNReal.mul_ne_top hcoeff_ne_top hprefix_ne_top
    exact (ENNReal.add_right_inj hleft_ne_top).1 hsum'
  simpa [falsePart, prefixEvent, ℓ] using hcancel

end IsGeneralizedPolyaUrnWithWeights

/-- Helper for Exercise 17.3.2: from time `N` onward, drawing only the fixed color `b`. -/
def eventualColorFrom (X : ℕ → Ω → Bool) (N : ℕ) (b : Bool) : Set Ω :=
  {ω | ∀ m : ℕ, X (N + m) ω = b}

/-- Helper for Exercise 17.3.2: the event that eventually only the fixed color `b` is drawn. -/
def eventualColorEvent (X : ℕ → Ω → Bool) (b : Bool) : Set Ω :=
  ⋃ N : ℕ, eventualColorFrom X N b

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 17.3.2: a monochromatic run of length `m + 1` splits into its first draw
and the shifted tail run. -/
lemma monochromaticRunEvent_succ
    {X : ℕ → Ω → Bool} {n m : ℕ} (b : Bool) :
    {ω | ∀ j : Fin (m + 1), X (n + j) ω = b} =
      {ω | X n ω = b} ∩ {ω | ∀ j : Fin m, X (n + 1 + j) ω = b} := by
  -- Proof comment: split the `Fin (m + 1)` quantifier into the first coordinate and the shifted
  -- tail coordinates.
  ext ω
  simp [Fin.forall_iff_succ, Nat.add_left_comm, Nat.add_comm]

/-- Helper for Exercise 17.3.2: a fixed prefix followed by `m` consecutive black draws has the
expected multiplicative cylinder probability. -/
theorem prefixEvent_inter_monochromaticRunEvent_true_eq_mul_prod
    {μ : Measure Ω} {w : ℕ → NNReal} {X : ℕ → Ω → Bool}
    (hX : IsGeneralizedPolyaUrnWithWeights μ w X) {n m : ℕ} (x : Fin n → Bool) :
    μ (weightedUrnPrefixEvent X x ∩ {ω | ∀ j : Fin m, X (n + j) ω = true}) =
      (Finset.prod (Finset.range m) fun j ↦
        (((w (blackPrefixCount x + j)) /
            (w (blackPrefixCount x + j) + w (n - blackPrefixCount x)) : NNReal) : ℝ≥0∞)) *
        μ (weightedUrnPrefixEvent X x) := by
  induction m generalizing n with
  | zero =>
      -- Proof comment: the empty monochromatic run imposes no extra condition beyond the prefix.
      simp
  | succ m ih =>
      set ℓ : ℕ := blackPrefixCount x
      have hden_nat : n + 1 - (ℓ + 1) = n - ℓ := by
        dsimp [ℓ]
        omega
      -- Route correction: split off the first black draw, rewrite it as an appended prefix, and
      -- then apply the induction hypothesis to the shifted tail.
      calc
        μ (weightedUrnPrefixEvent X x ∩ {ω | ∀ j : Fin (m + 1), X (n + j) ω = true}) =
            μ (weightedUrnPrefixEvent X (Fin.snoc x true) ∩
              {ω | ∀ j : Fin m, X (n + 1 + j) ω = true}) := by
              -- Proof comment: the first black draw extends the prefix by one `true` entry.
              rw [monochromaticRunEvent_succ (X := X) (n := n) (m := m) true,
                ← Set.inter_assoc, ← weightedUrnPrefixEvent_snoc]
        _ =
            (Finset.prod (Finset.range m) fun j ↦
              (((w (ℓ + 1 + j)) / (w (ℓ + 1 + j) + w (n - ℓ)) : NNReal) : ℝ≥0∞)) *
              μ (weightedUrnPrefixEvent X (Fin.snoc x true)) := by
              -- Proof comment: the tail run is the same theorem applied to the longer prefix.
              simpa [ℓ, blackPrefixCount_snoc_true, hden_nat, Nat.add_assoc] using
                ih (n := n + 1) (x := Fin.snoc x true)
        _ =
            (Finset.prod (Finset.range m) fun j ↦
              (((w (ℓ + 1 + j)) / (w (ℓ + 1 + j) + w (n - ℓ)) : NNReal) : ℝ≥0∞)) *
              ((((w ℓ) / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞) *
                μ (weightedUrnPrefixEvent X x)) := by
              -- Proof comment: rewrite the extended prefix mass by the one-step black-branch
              -- urn formula.
              rw [weightedUrnPrefixEvent_snoc]
              exact congrArg
                (fun t ↦
                  (Finset.prod (Finset.range m) fun j ↦
                    (((w (ℓ + 1 + j)) / (w (ℓ + 1 + j) + w (n - ℓ)) : NNReal) : ℝ≥0∞)) * t)
                (by simpa [ℓ] using hX.prefixEvent_inter_true_eq x)
        _ =
            ((Finset.prod (Finset.range m) fun j ↦
              (((w (ℓ + 1 + j)) / (w (ℓ + 1 + j) + w (n - ℓ)) : NNReal) : ℝ≥0∞)) *
              (((w ℓ) / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞)) *
              μ (weightedUrnPrefixEvent X x) := by
              rw [mul_assoc]
        _ =
            (Finset.prod (Finset.range (m + 1)) fun j ↦
              (((w (ℓ + j)) / (w (ℓ + j) + w (n - ℓ)) : NNReal) : ℝ≥0∞)) *
              μ (weightedUrnPrefixEvent X x) := by
              -- Proof comment: the peeled first factor is exactly the `j = 0` term of the full
              -- product.
              rw [Finset.prod_range_succ']
              simp [Nat.add_assoc, Nat.add_comm, ℓ]

/-- Helper for Exercise 17.3.2: a fixed prefix followed by `m` consecutive red draws has the
expected multiplicative cylinder probability. -/
theorem prefixEvent_inter_monochromaticRunEvent_false_eq_mul_prod
    {μ : Measure Ω} {w : ℕ → NNReal} {X : ℕ → Ω → Bool}
    [IsFiniteMeasure μ] (hX : IsGeneralizedPolyaUrnWithWeights μ w X) (hw_pos : ∀ n : ℕ, 0 < w n)
    {n m : ℕ} (x : Fin n → Bool) :
    μ (weightedUrnPrefixEvent X x ∩ {ω | ∀ j : Fin m, X (n + j) ω = false}) =
      (Finset.prod (Finset.range m) fun j ↦
        (((w (n - blackPrefixCount x + j)) /
            (w (blackPrefixCount x) + w (n - blackPrefixCount x + j)) : NNReal) : ℝ≥0∞)) *
        μ (weightedUrnPrefixEvent X x) := by
  induction m generalizing n with
  | zero =>
      -- Proof comment: the empty red run is again the unchanged prefix cylinder.
      simp
  | succ m ih =>
      set ℓ : ℕ := blackPrefixCount x
      have hcount_le : ℓ ≤ n := by
        simpa [ℓ] using blackPrefixCount_le x
      have hshift_nat : n + 1 - ℓ = n - ℓ + 1 := by
        omega
      -- Route correction: split off the first red draw, rewrite it as an appended prefix, and
      -- then invoke the induction hypothesis for the shifted tail.
      calc
        μ (weightedUrnPrefixEvent X x ∩ {ω | ∀ j : Fin (m + 1), X (n + j) ω = false}) =
            μ (weightedUrnPrefixEvent X (Fin.snoc x false) ∩
              {ω | ∀ j : Fin m, X (n + 1 + j) ω = false}) := by
              -- Proof comment: the first red draw extends the prefix by one `false` entry.
              rw [monochromaticRunEvent_succ (X := X) (n := n) (m := m) false,
                ← Set.inter_assoc, ← weightedUrnPrefixEvent_snoc]
        _ =
            (Finset.prod (Finset.range m) fun j ↦
              (((w (n - ℓ + 1 + j)) / (w ℓ + w (n - ℓ + 1 + j)) : NNReal) : ℝ≥0∞)) *
              μ (weightedUrnPrefixEvent X (Fin.snoc x false)) := by
              -- Proof comment: after one red draw, the black count is unchanged and the red count
              -- is shifted by one.
              simpa [ℓ, blackPrefixCount_snoc_false, hshift_nat, Nat.add_assoc, Nat.add_left_comm,
                Nat.add_comm] using ih (n := n + 1) (x := Fin.snoc x false)
        _ =
            (Finset.prod (Finset.range m) fun j ↦
              (((w (n - ℓ + 1 + j)) / (w ℓ + w (n - ℓ + 1 + j)) : NNReal) : ℝ≥0∞)) *
              ((((w (n - ℓ)) / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞) *
                μ (weightedUrnPrefixEvent X x)) := by
              -- Proof comment: rewrite the extended prefix mass by the one-step red-branch
              -- urn formula.
              rw [weightedUrnPrefixEvent_snoc]
              exact congrArg
                (fun t ↦
                  (Finset.prod (Finset.range m) fun j ↦
                    (((w (n - ℓ + 1 + j)) / (w ℓ + w (n - ℓ + 1 + j)) : NNReal) : ℝ≥0∞)) * t)
                (by simpa [ℓ] using hX.prefixEvent_inter_false_eq hw_pos x)
        _ =
            ((Finset.prod (Finset.range m) fun j ↦
              (((w (n - ℓ + 1 + j)) / (w ℓ + w (n - ℓ + 1 + j)) : NNReal) : ℝ≥0∞)) *
              (((w (n - ℓ)) / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞)) *
              μ (weightedUrnPrefixEvent X x) := by
              rw [mul_assoc]
        _ =
            (Finset.prod (Finset.range (m + 1)) fun j ↦
              (((w (n - ℓ + j)) / (w ℓ + w (n - ℓ + j)) : NNReal) : ℝ≥0∞)) *
              μ (weightedUrnPrefixEvent X x) := by
              -- Proof comment: the peeled first red factor is exactly the `j = 0` term of the
              -- full product.
              rw [Finset.prod_range_succ']
              simp [Nat.add_assoc, Nat.add_comm, ℓ]

/-- Helper for Exercise 17.3.2: one more branch-ratio factor is absorbed by adding the
corresponding reciprocal term inside the inverse bound. -/
lemma ratioMulInvOneAdd_le_invOneAdd
    (a c : NNReal) (s : ℝ≥0∞) :
    (((a / (a + c) : NNReal) : ℝ≥0∞) * (1 + (c : ℝ≥0∞) * s)⁻¹) ≤
      (1 + (c : ℝ≥0∞) * (s + (a : ℝ≥0∞)⁻¹))⁻¹ := by
  let A : ℝ≥0∞ := a
  let C : ℝ≥0∞ := c
  let u : ℝ≥0∞ := 1 + C * s
  let v : ℝ≥0∞ := 1 + C * A⁻¹
  have hden_le : 1 + C * (s + A⁻¹) ≤ u * v := by
    have htail :
        C * A⁻¹ ≤ C * A⁻¹ + (C * s) * (C * A⁻¹) := by
      exact le_add_of_nonneg_right bot_le
    calc
      1 + C * (s + A⁻¹) = 1 + C * s + C * A⁻¹ := by
        rw [mul_add, add_assoc]
      _ ≤ 1 + C * s + (C * A⁻¹ + (C * s) * (C * A⁻¹)) := by
        simpa [add_assoc, add_left_comm, add_comm] using add_le_add_left htail (1 + C * s)
      _ = u * v := by
        simp [u, v, mul_add, add_assoc, add_left_comm, add_comm, mul_assoc,
          mul_left_comm, mul_comm]
  have hratio_mul : (((a / (a + c) : NNReal) : ℝ≥0∞) * v) ≤ 1 := by
    by_cases ha : a = 0
    · -- Proof comment: if `a = 0`, then the branch ratio already vanishes.
      subst ha
      simp [v]
    · have hden_nn_pos : 0 < a + c := by
        exact lt_of_lt_of_le (pos_iff_ne_zero.mpr ha) (le_add_of_nonneg_right c.2)
      have hden_nn_ne : a + c ≠ 0 := ne_of_gt hden_nn_pos
      have hden_ne : A + C ≠ 0 := by
        simpa [A, C] using hden_nn_ne
      have hA_ne_zero : A ≠ 0 := by
        simpa [A] using ha
      have hcore :
          (A / (A + C)) * v ≤ 1 := by
        rw [show (A / (A + C)) * v = (A * v) * (A + C)⁻¹ by
              rw [ENNReal.div_eq_inv_mul]
              ac_rfl]
        rw [ENNReal.mul_inv_le_iff hden_ne (by simp [A, C])]
        calc
          A * v = A + C := by
            calc
              A * v = A * (1 + C * A⁻¹) := by rfl
              _ = A + C * (A * A⁻¹) := by
                rw [mul_add, mul_one]
                ac_rfl
              _ = A + C * 1 := by
                rw [ENNReal.mul_inv_cancel hA_ne_zero ENNReal.coe_ne_top]
              _ = A + C := by simp
          _ ≤ 1 * (A + C) := by simp
      have hratio_eq : ((a / (a + c) : NNReal) : ℝ≥0∞) = A / (A + C) := by
        simpa [A, C] using (ENNReal.coe_div hden_nn_ne)
      simpa [hratio_eq] using hcore
  rw [ENNReal.le_inv_iff_mul_le]
  calc
    (((a / (a + c) : NNReal) : ℝ≥0∞) * u⁻¹) * (1 + C * (s + A⁻¹)) ≤
        (((a / (a + c) : NNReal) : ℝ≥0∞) * u⁻¹) * (u * v) := by
          exact mul_le_mul_right hden_le _
    _ = (((a / (a + c) : NNReal) : ℝ≥0∞) * (u⁻¹ * u)) * v := by
          ac_rfl
    _ ≤ ((((a / (a + c) : NNReal) : ℝ≥0∞) * 1) : ℝ≥0∞) * v := by
          gcongr
          exact ENNReal.inv_mul_le_one u
    _ = (((a / (a + c) : NNReal) : ℝ≥0∞) * v) := by
          simp
    _ ≤ 1 := hratio_mul

/-- Helper for Exercise 17.3.2: the finite product of successive branch ratios is bounded by the
inverse of `1 + c` times the corresponding reciprocal partial sum. -/
lemma monochromaticRunProduct_le_invOneAddMulSumInv
    (a : ℕ → NNReal) (c : NNReal) (m : ℕ) :
    Finset.prod (Finset.range m) (fun j ↦ (((a j) / (a j + c) : NNReal) : ℝ≥0∞)) ≤
      (1 + (c : ℝ≥0∞) * (Finset.sum (Finset.range m) fun j ↦ ((a j : ℝ≥0∞)⁻¹)))⁻¹ := by
  induction m generalizing a with
  | zero =>
      -- Proof comment: the empty product is `1`, and the empty reciprocal sum is `0`.
      simp
  | succ m ih =>
      let shiftedSum : ℝ≥0∞ := Finset.sum (Finset.range m) fun j ↦ ((a (j + 1) : ℝ≥0∞)⁻¹)
      have hsum :
          shiftedSum + ((a 0 : ℝ≥0∞)⁻¹) =
            Finset.sum (Finset.range (m + 1)) fun j ↦ ((a j : ℝ≥0∞)⁻¹) := by
        simpa [shiftedSum] using
          (Finset.sum_range_succ' (fun j ↦ ((a j : ℝ≥0∞)⁻¹)) m).symm
      -- Route correction: peel off the first ratio factor, bound the shifted tail by the
      -- induction hypothesis, and absorb the new reciprocal term with the one-step inequality.
      calc
        (Finset.prod (Finset.range (m + 1)) fun j ↦ (((a j) / (a j + c) : NNReal) : ℝ≥0∞)) =
            (Finset.prod (Finset.range m) fun j ↦
              (((a (j + 1)) / (a (j + 1) + c) : NNReal) : ℝ≥0∞)) *
              (((a 0) / (a 0 + c) : NNReal) : ℝ≥0∞) := by
              -- Proof comment: separate the first branch-ratio factor from the shifted tail.
              rw [Finset.prod_range_succ']
        _ ≤ (1 + (c : ℝ≥0∞) * shiftedSum)⁻¹ *
              (((a 0) / (a 0 + c) : NNReal) : ℝ≥0∞) := by
              -- Proof comment: the induction hypothesis controls the shifted tail product.
              gcongr
              simpa [shiftedSum] using ih (a := fun j ↦ a (j + 1))
        _ = (((a 0) / (a 0 + c) : NNReal) : ℝ≥0∞) * (1 + (c : ℝ≥0∞) * shiftedSum)⁻¹ := by
              rw [mul_comm]
        _ ≤ (1 + (c : ℝ≥0∞) * (shiftedSum + ((a 0 : ℝ≥0∞)⁻¹)))⁻¹ := by
              -- Proof comment: absorb the peeled factor into the inverse bound.
              simpa [shiftedSum, add_assoc, add_left_comm, add_comm] using
                ratioMulInvOneAdd_le_invOneAdd (a := a 0) (c := c) (s := shiftedSum)
        _ = (1 + (c : ℝ≥0∞) *
              (Finset.sum (Finset.range (m + 1)) fun j ↦ ((a j : ℝ≥0∞)⁻¹)))⁻¹ := by
              -- Proof comment: restore the shifted reciprocal sum to the standard initial segment.
              rw [hsum]

/-- Helper for Exercise 17.3.2: shifting the divergent reciprocal series by a finite amount keeps
the `ℝ≥0∞` sum equal to `∞`. -/
lemma tsum_inv_weights_tail_eq_top
    {w : ℕ → NNReal} (hw_pos : ∀ n : ℕ, 0 < w n)
    (hw_div : (∑' n, ((w n : ℝ≥0∞)⁻¹)) = ∞) (k : ℕ) :
    (∑' n, ((w (n + k) : ℝ≥0∞)⁻¹)) = ∞ := by
  set f : ℕ → ℝ≥0∞ := fun n ↦ (w n : ℝ≥0∞)⁻¹
  set prefixSum : ℝ≥0∞ := Finset.sum (Finset.range k) fun i ↦ f i
  have hfull :
      Tendsto (fun n : ℕ ↦ Finset.sum (Finset.range (n + k)) fun i ↦ f i) atTop (𝓝 ∞) := by
    simpa [f, hw_div] using (ENNReal.tendsto_nat_tsum f).comp (tendsto_add_atTop_nat k)
  by_contra htail
  have hprefix_ne_top : prefixSum ≠ ∞ := by
    -- Proof comment: a finite prefix sum of `ℝ≥0∞` reciprocals is still finite.
    dsimp [prefixSum]
    exact ENNReal.sum_ne_top.2 fun i hi ↦ by
      have hwi : w i ≠ 0 := ne_of_gt (hw_pos i)
      simpa [f] using hwi
  have htail_tendsto :
      Tendsto
        (fun n : ℕ ↦ Finset.sum (Finset.range n) fun i ↦ f (i + k))
        atTop
        (𝓝 ((∑' i : ℕ, f (i + k)))) := by
    simpa using ENNReal.tendsto_nat_tsum (fun i ↦ f (i + k))
  have hshift :
      Tendsto
        (fun n : ℕ ↦ prefixSum + Finset.sum (Finset.range n) (fun i ↦ f (i + k)))
        atTop
        (𝓝 (prefixSum + (∑' i : ℕ, f (i + k)))) := by
    exact tendsto_const_nhds.add htail_tendsto
  have hshift' :
      Tendsto
        (fun n : ℕ ↦ Finset.sum (Finset.range (n + k)) fun i ↦ f i)
        atTop
        (𝓝 (prefixSum + (∑' i : ℕ, f (i + k)))) := by
    convert hshift using 1
    funext n
    dsimp [prefixSum]
    rw [← Finset.sum_range_add_sum_Ico _ (Nat.le_add_left k n), Finset.sum_Ico_eq_sum_range]
    simp [Nat.add_comm]
  have hsum_eq : prefixSum + (∑' i : ℕ, f (i + k)) = ∞ :=
    tendsto_nhds_unique hshift' hfull
  have hsum_ne_top : prefixSum + (∑' i : ℕ, f (i + k)) ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨hprefix_ne_top, htail⟩
  exact hsum_ne_top hsum_eq

omit [MeasurableSpace Ω] in
/-- Helper for Exercise 17.3.2: an eventual monochromatic tail is contained in every finite
monochromatic run cylinder starting at the same cutoff. -/
lemma prefixEvent_inter_eventualColorFrom_subset_run
    {X : ℕ → Ω → Bool} {n m : ℕ} (x : Fin n → Bool) (b : Bool) :
    weightedUrnPrefixEvent X x ∩ eventualColorFrom X n b ⊆
      weightedUrnPrefixEvent X x ∩ {ω | ∀ j : Fin m, X (n + j) ω = b} := by
  -- Proof comment: an eventually constant tail is, in particular, constant on every finite
  -- initial segment of that tail.
  intro ω hω
  refine ⟨hω.1, ?_⟩
  intro j
  exact hω.2 j

/-- Helper for Exercise 17.3.2: multiplying divergent `ℝ≥0∞` partial sums by a positive finite
constant and then adding `1` still tends to `∞`. -/
lemma oneAddMulPartialSum_tendsto_top_of_tsum_eq_top
    {f : ℕ → ℝ≥0∞} {c : NNReal} (hc : c ≠ 0) (hf : (∑' n, f n) = ∞) :
      Tendsto
      (fun m : ℕ ↦ 1 + (c : ℝ≥0∞) * (Finset.sum (Finset.range m) f))
      atTop
      (𝓝 ∞) := by
  have hpartial :
      Tendsto (fun m : ℕ ↦ Finset.sum (Finset.range m) f) atTop (𝓝 ∞) := by
    simpa [hf] using (ENNReal.tendsto_nat_tsum f)
  have hscaled :
      Tendsto
        (fun m : ℕ ↦ (c : ℝ≥0∞) * (Finset.sum (Finset.range m) f))
        atTop
        (𝓝 ∞) := by
    -- Proof comment: finite nonzero scaling preserves divergence to `∞`.
    simpa [hc] using
      (ENNReal.Tendsto.const_mul (a := (c : ℝ≥0∞)) hpartial (Or.inr ENNReal.coe_ne_top))
  -- Proof comment: adding a fixed constant does not change a limit of `∞`.
  simpa [add_comm] using hscaled.const_add (1 : ℝ≥0∞)

/-- Helper for Exercise 17.3.2: the reciprocal of the shifted divergent partial-sum bound tends to
`0` in `ℝ≥0∞`. -/
lemma invOneAddMulPartialSum_tendsto_zero_of_tsum_eq_top
    {f : ℕ → ℝ≥0∞} {c : NNReal} (hc : c ≠ 0) (hf : (∑' n, f n) = ∞) :
    Tendsto
      (fun m : ℕ ↦ (1 + (c : ℝ≥0∞) * (Finset.sum (Finset.range m) f))⁻¹)
      atTop
      (𝓝 0) := by
  have htop := oneAddMulPartialSum_tendsto_top_of_tsum_eq_top (f := f) hc hf
  -- Proof comment: `1 / t` converges to `0` once the denominator tends to `∞`.
  simpa [one_div] using
    (ENNReal.Tendsto.const_div (a := (1 : ℝ≥0∞)) htop (Or.inr ENNReal.one_ne_top))

/-- Helper for Exercise 17.3.2: after fixing a prefix `x`, the event that all later draws have one
fixed color has measure zero under the divergence hypothesis. -/
lemma measure_prefixEvent_eventually_color_tail_eq_zero
    {μ : Measure Ω} [IsProbabilityMeasure μ] {w : ℕ → NNReal} {X : ℕ → Ω → Bool}
    (hX : IsGeneralizedPolyaUrnWithWeights μ w X) (hw_pos : ∀ n : ℕ, 0 < w n)
    (hw_div : (∑' n, ((w n : ℝ≥0∞)⁻¹)) = ∞)
    {n : ℕ} (x : Fin n → Bool) (b : Bool) :
    μ (weightedUrnPrefixEvent X x ∩ {ω | ∀ m : ℕ, X (n + m) ω = b}) = 0 := by
  set prefixEvent : Set Ω := weightedUrnPrefixEvent X x
  have hprefix_le_one : μ prefixEvent ≤ 1 := by
    -- Proof comment: every prefix cylinder is contained in the whole sample space.
    calc
      μ prefixEvent ≤ μ Set.univ := measure_mono (by intro ω _; simp)
      _ = 1 := by simp
  -- Route correction: separate the set-theoretic containment from the ENNReal limit argument, and
  -- then compare the constant tail measure to an inverse-bound sequence that tends to `0`.
  cases b with
  | false =>
      change μ (prefixEvent ∩ eventualColorFrom X n false) = 0
      set ℓ : ℕ := blackPrefixCount x
      set tail : Set Ω := prefixEvent ∩ eventualColorFrom X n false
      set c : NNReal := w ℓ
      set f : ℕ → ℝ≥0∞ := fun j ↦ ((w (n - ℓ + j) : ℝ≥0∞)⁻¹)
      set invBound : ℕ → ℝ≥0∞ := fun m ↦
        (1 + (c : ℝ≥0∞) * (Finset.sum (Finset.range m) f))⁻¹
      have hc : c ≠ 0 := by
        exact ne_of_gt (hw_pos ℓ)
      have hf : (∑' j, f j) = ∞ := by
        -- Proof comment: shifting the divergent reciprocal series by the red count keeps its sum
        -- equal to `∞`.
        simpa [f, ℓ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (tsum_inv_weights_tail_eq_top (w := w) hw_pos hw_div (n - ℓ))
      have hInvBound :
          Tendsto invBound atTop (𝓝 0) := by
        -- Proof comment: the inverse bound vanishes because its denominator diverges to `∞`.
        simpa [invBound] using
          (invOneAddMulPartialSum_tendsto_zero_of_tsum_eq_top (f := f) (c := c) hc hf)
      have hbound : ∀ m : ℕ, μ tail ≤ invBound m := by
        intro m
        have hsubset :
            tail ⊆ prefixEvent ∩ {ω | ∀ j : Fin m, X (n + j) ω = false} := by
          simpa [tail] using
            (prefixEvent_inter_eventualColorFrom_subset_run (X := X) (n := n) (m := m) x false)
        have hprod :
            (Finset.prod (Finset.range m) fun j ↦
              (((w (n - ℓ + j)) / (w ℓ + w (n - ℓ + j)) : NNReal) : ℝ≥0∞)) ≤
              invBound m := by
          -- Proof comment: the finite red-run product is controlled by the reciprocal-sum bound.
          simpa [invBound, f, c, ℓ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, add_comm] using
            (monochromaticRunProduct_le_invOneAddMulSumInv
              (a := fun j ↦ w (n - ℓ + j)) (c := w ℓ) m)
        calc
          μ tail ≤ μ (prefixEvent ∩ {ω | ∀ j : Fin m, X (n + j) ω = false}) := measure_mono hsubset
          _ =
              (Finset.prod (Finset.range m) fun j ↦
                (((w (n - ℓ + j)) / (w ℓ + w (n - ℓ + j)) : NNReal) : ℝ≥0∞)) * μ prefixEvent := by
                -- Proof comment: use the already established finite red-cylinder formula.
                simpa [prefixEvent, ℓ] using
                  (prefixEvent_inter_monochromaticRunEvent_false_eq_mul_prod
                    (hX := hX) (hw_pos := hw_pos) (n := n) (m := m) x)
          _ ≤ invBound m * μ prefixEvent := by
                simpa [mul_comm, mul_left_comm, mul_assoc] using
                  mul_le_mul_right hprod (μ prefixEvent)
          _ ≤ invBound m * 1 := by
                simpa [mul_comm, mul_left_comm, mul_assoc] using
                  mul_le_mul_left hprefix_le_one (invBound m)
          _ = invBound m := by simp
      have htail_le_zero : μ tail ≤ 0 :=
        le_of_tendsto_of_tendsto' tendsto_const_nhds hInvBound hbound
      exact le_antisymm htail_le_zero bot_le
  | true =>
      change μ (prefixEvent ∩ eventualColorFrom X n true) = 0
      set ℓ : ℕ := blackPrefixCount x
      set tail : Set Ω := prefixEvent ∩ eventualColorFrom X n true
      set c : NNReal := w (n - ℓ)
      set f : ℕ → ℝ≥0∞ := fun j ↦ ((w (ℓ + j) : ℝ≥0∞)⁻¹)
      set invBound : ℕ → ℝ≥0∞ := fun m ↦
        (1 + (c : ℝ≥0∞) * (Finset.sum (Finset.range m) f))⁻¹
      have hc : c ≠ 0 := by
        exact ne_of_gt (hw_pos (n - ℓ))
      have hf : (∑' j, f j) = ∞ := by
        -- Proof comment: shifting the divergent reciprocal series by the black count preserves
        -- divergence.
        simpa [f, ℓ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (tsum_inv_weights_tail_eq_top (w := w) hw_pos hw_div ℓ)
      have hInvBound :
          Tendsto invBound atTop (𝓝 0) := by
        -- Proof comment: the inverse black-tail bound also tends to `0`.
        simpa [invBound] using
          (invOneAddMulPartialSum_tendsto_zero_of_tsum_eq_top (f := f) (c := c) hc hf)
      have hbound : ∀ m : ℕ, μ tail ≤ invBound m := by
        intro m
        have hsubset :
            tail ⊆ prefixEvent ∩ {ω | ∀ j : Fin m, X (n + j) ω = true} := by
          simpa [tail] using
            (prefixEvent_inter_eventualColorFrom_subset_run (X := X) (n := n) (m := m) x true)
        have hprod :
            (Finset.prod (Finset.range m) fun j ↦
              (((w (ℓ + j)) / (w (ℓ + j) + w (n - ℓ)) : NNReal) : ℝ≥0∞)) ≤
              invBound m := by
          -- Proof comment: the finite black-run product satisfies the same inverse bound.
          simpa [invBound, f, c, ℓ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            (monochromaticRunProduct_le_invOneAddMulSumInv
              (a := fun j ↦ w (ℓ + j)) (c := w (n - ℓ)) m)
        calc
          μ tail ≤ μ (prefixEvent ∩ {ω | ∀ j : Fin m, X (n + j) ω = true}) := measure_mono hsubset
          _ =
              (Finset.prod (Finset.range m) fun j ↦
                (((w (ℓ + j)) / (w (ℓ + j) + w (n - ℓ)) : NNReal) : ℝ≥0∞)) * μ prefixEvent := by
                -- Proof comment: use the finite black-cylinder formula from the earlier helper.
                simpa [prefixEvent, ℓ] using
                  (prefixEvent_inter_monochromaticRunEvent_true_eq_mul_prod
                    (hX := hX) (n := n) (m := m) x)
          _ ≤ invBound m * μ prefixEvent := by
                simpa [mul_comm, mul_left_comm, mul_assoc] using
                  mul_le_mul_right hprod (μ prefixEvent)
          _ ≤ invBound m * 1 := by
                simpa [mul_comm, mul_left_comm, mul_assoc] using
                  mul_le_mul_left hprefix_le_one (invBound m)
          _ = invBound m := by simp
      have htail_le_zero : μ tail ≤ 0 :=
        le_of_tendsto_of_tendsto' tendsto_const_nhds hInvBound hbound
      exact le_antisymm htail_le_zero bot_le

/-- Helper for Exercise 17.3.2: each fixed-cutoff eventual-color event has measure zero. -/
lemma measure_eventualColorFrom_eq_zero
    {μ : Measure Ω} [IsProbabilityMeasure μ] {w : ℕ → NNReal} {X : ℕ → Ω → Bool}
    (hX : IsGeneralizedPolyaUrnWithWeights μ w X) (hw_pos : ∀ n : ℕ, 0 < w n)
    (hw_div : (∑' n, ((w n : ℝ≥0∞)⁻¹)) = ∞)
    (N : ℕ) (b : Bool) :
    μ (eventualColorFrom X N b) = 0 := by
  classical
  have hUnion :
      eventualColorFrom X N b =
        ⋃ x : Fin N → Bool, weightedUrnPrefixEvent X x ∩ {ω | ∀ m : ℕ, X (N + m) ω = b} := by
    -- Proof comment: every sample in the cutoff event has a unique Boolean prefix of length `N`,
    -- namely the realized first `N` draws.
    ext ω
    constructor
    · intro hω
      refine Set.mem_iUnion.2 ⟨fun i : Fin N ↦ X i ω, ?_⟩
      constructor
      · intro i
        rfl
      · exact hω
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨x, hx⟩
      exact hx.2
  rw [hUnion]
  refine le_antisymm ?_ bot_le
  calc
    μ (⋃ x : Fin N → Bool, weightedUrnPrefixEvent X x ∩ {ω | ∀ m : ℕ, X (N + m) ω = b})
      ≤ ∑ x : Fin N → Bool, μ (weightedUrnPrefixEvent X x ∩ {ω | ∀ m : ℕ, X (N + m) ω = b}) :=
        MeasureTheory.measure_iUnion_fintype_le μ
          (fun x : Fin N → Bool ↦
            weightedUrnPrefixEvent X x ∩ {ω | ∀ m : ℕ, X (N + m) ω = b})
    _ = 0 := by
      -- Proof comment: each fixed-prefix tail event is null by the prefix-level estimate.
      refine Finset.sum_eq_zero ?_
      intro x hx
      simpa using measure_prefixEvent_eventually_color_tail_eq_zero hX hw_pos hw_div (x := x) b

/-- Helper for Exercise 17.3.2: the full eventual-single-color event has measure zero for each
fixed color. -/
lemma measure_eventualColorEvent_eq_zero
    {μ : Measure Ω} [IsProbabilityMeasure μ] {w : ℕ → NNReal} {X : ℕ → Ω → Bool}
    (hX : IsGeneralizedPolyaUrnWithWeights μ w X) (hw_pos : ∀ n : ℕ, 0 < w n)
    (hw_div : (∑' n, ((w n : ℝ≥0∞)⁻¹)) = ∞)
    (b : Bool) :
    μ (eventualColorEvent X b) = 0 := by
  -- Proof comment: the full eventual-color event is the countable union over all cutoff times.
  rw [eventualColorEvent]
  refine measure_iUnion_null fun N ↦ ?_
  exact measure_eventualColorFrom_eq_zero hX hw_pos hw_div N b

/-- Exercise 17.3.2: if `∑ 1 / w n = ∞`, then almost surely the generalized weighted Pólya urn
draws infinitely many balls of each color. -/
theorem ae_infinitely_many_draws_each_color_of_tsum_inv_weights_eq_top
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → Bool} {w : ℕ → NNReal}
    (hX : IsGeneralizedPolyaUrnWithWeights μ w X) (hw_pos : ∀ n : ℕ, 0 < w n)
    (hw_div : (∑' n, ((w n : ℝ≥0∞)⁻¹)) = ∞) :
    ∀ᵐ ω ∂μ, {n : ℕ | X n ω = true}.Infinite ∧ {n : ℕ | X n ω = false}.Infinite := by
  have htrue_zero : μ (eventualColorEvent X true) = 0 :=
    measure_eventualColorEvent_eq_zero hX hw_pos hw_div true
  have hfalse_zero : μ (eventualColorEvent X false) = 0 :=
    measure_eventualColorEvent_eq_zero hX hw_pos hw_div false
  rw [ae_iff]
  refine measure_mono_null ?_ (measure_union_null htrue_zero hfalse_zero)
  intro ω hω
  by_cases htrueInf : {n : ℕ | X n ω = true}.Infinite
  · have hfalseNotInf : ¬ {n : ℕ | X n ω = false}.Infinite := by
      exact fun hfalseInf ↦ hω ⟨htrueInf, hfalseInf⟩
    have hfalseFinite : ({n : ℕ | X n ω = false} : Set ℕ).Finite :=
      Set.not_infinite.mp hfalseNotInf
    have hcofinite :
        ({n : ℕ | X n ω = false} : Set ℕ)ᶜ ∈ (Filter.cofinite : Filter ℕ) :=
      hfalseFinite.compl_mem_cofinite
    have hatTop :
        ({n : ℕ | X n ω = false} : Set ℕ)ᶜ ∈ (atTop : Filter ℕ) := by
      simpa [Nat.cofinite_eq_atTop] using hcofinite
    rcases Filter.mem_atTop_sets.mp hatTop with ⟨N, hN⟩
    left
    refine Set.mem_iUnion.2 ⟨N, ?_⟩
    show ω ∈ eventualColorFrom X N true
    change ∀ m : ℕ, X (N + m) ω = true
    intro m
    have hmem :
        N + m ∈ ({n : ℕ | X n ω = false} : Set ℕ)ᶜ :=
      hN (N + m) (Nat.le_add_right N m)
    have hnotFalse : X (N + m) ω ≠ false := by
      simpa using hmem
    cases hdraw : X (N + m) ω <;> simp_all
  · have htrueFinite : ({n : ℕ | X n ω = true} : Set ℕ).Finite :=
      Set.not_infinite.mp htrueInf
    have hcofinite :
        ({n : ℕ | X n ω = true} : Set ℕ)ᶜ ∈ (Filter.cofinite : Filter ℕ) :=
      htrueFinite.compl_mem_cofinite
    have hatTop :
        ({n : ℕ | X n ω = true} : Set ℕ)ᶜ ∈ (atTop : Filter ℕ) := by
      simpa [Nat.cofinite_eq_atTop] using hcofinite
    rcases Filter.mem_atTop_sets.mp hatTop with ⟨N, hN⟩
    right
    refine Set.mem_iUnion.2 ⟨N, ?_⟩
    show ω ∈ eventualColorFrom X N false
    change ∀ m : ℕ, X (N + m) ω = false
    intro m
    have hmem :
        N + m ∈ ({n : ℕ | X n ω = true} : Set ℕ)ᶜ :=
      hN (N + m) (Nat.le_add_right N m)
    have hnotTrue : X (N + m) ω ≠ true := by
      simpa using hmem
    cases hdraw : X (N + m) ω <;> simp_all

end ProbabilityTheory

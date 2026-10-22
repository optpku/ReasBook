/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Probability.Distributions.Beta
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Exercise_5_1_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_20
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_25
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Example_12_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Example_12_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Remark_12_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Remark_12_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Theorem_12_24
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_4

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators BoundedContinuousFunction ENNReal ProbabilityTheory Topology unitInterval

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]

/- Domain-style sampling for the generalized Pólya-urn item:
- `weightedUrnPrefixEvent` and `blackPrefixCount` are localized here as the primitive prefix-event
  and black-count API for Boolean-valued urn words, so this file does not depend on the later item
  `Exercise_17_3_2`.
- `IsConditionallyBernoulliIID` in `Example_12_3` is the canonical Chapter 12 bridge for a
  Bernoulli directing parameter.

Best owner abstraction:
- this file remains `source-facing`: the public owner is the constant-reinforcement generalized
  two-color urn with initial red/black counts `R`,`S` and reinforcement parameters `r`,`s`,
  encoded by the actual next-draw law coming from the current urn counts;
- `weightedUrnPrefixEvent` and `blackPrefixCount` are kept as small local support definitions for
  the primitive prefix API;
- `IsConditionallyBernoulliIID` is a downstream `bridge/view` consequence of this owner, not a
  replacement for it.

Primitive data:
- the measure `μ`, the initial red and black counts `R`,`S`, the constant reinforcement
  parameters `r`,`s`, and the `{0,1}`-valued draw process `X`.

Derived API:
- coordinate measurability and the one-step cylinder-probability formula are accessors of the
  owner abstraction;
- the fraction of black balls is the literal urn fraction
  `(S + s * L_n) / (R + S + r * (n - L_n) + s * L_n)`, where `L_n` is the black draw count in the
  first `n` draws;
- the Beta-law, conditional Bernoulli description, and almost-sure convergence statements are kept
  as source-facing exercise conclusions over that owner.

Semantic recall note:
- `lean_leansearch` did not surface a relevant existing generalized-Pólya-urn owner, so this item
  keeps the local source-facing urn API and treats the balanced Beta/de Finetti route as a helper.
-/

namespace ProbabilityTheory

/-- Helper for the generalized Pólya-urn item: the cylinder event that the first `n` draws of `X` match the
prescribed Boolean prefix `x`, with `true` encoding a black draw. -/
def weightedUrnPrefixEvent (X : ℕ → Ω → Bool) {n : ℕ} (x : Fin n → Bool) : Set Ω :=
  {ω | ∀ i : Fin n, X i ω = x i}

/-- Helper for the generalized Pólya-urn item: the number of black draws in the finite Boolean prefix `x`. -/
def blackPrefixCount {n : ℕ} (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i : Fin n ↦ x i = true).card

/-- Helper for Exercise 17.3.1: a prefix cylinder is measurable once every urn draw coordinate is
measurable. -/
theorem measurableSet_weightedUrnPrefixEvent
    {X : ℕ → Ω → Bool} (hX : ∀ n : ℕ, Measurable (X n)) {n : ℕ} (x : Fin n → Bool) :
    MeasurableSet (weightedUrnPrefixEvent X x) := by
  -- Proof comment: rewrite the cylinder event as the finite intersection of the coordinate fibers
  -- `{ω | X i ω = x i}`.
  have hset :
      {ω | ∀ i : Fin n, X i ω = x i} = ⋂ i : Fin n, {ω | X i ω = x i} := by
    ext ω
    simp
  rw [weightedUrnPrefixEvent, hset]
  exact MeasurableSet.iInter fun i : Fin n ↦
    (hX i) (measurableSet_singleton (x i))

/-- Helper for Exercise 17.3.1: appending one last color to a prefix cylinder is the same as
intersecting the old prefix cylinder with the corresponding next-draw event. -/
theorem weightedUrnPrefixEvent_snoc
    {X : ℕ → Ω → Bool} {n : ℕ} (x : Fin n → Bool) (b : Bool) :
    weightedUrnPrefixEvent X (Fin.snoc x b) =
      weightedUrnPrefixEvent X x ∩ {ω | X n ω = b} := by
  -- Proof comment: split the `Fin (n + 1)` quantifier into the old coordinates and the final
  -- coordinate.
  ext ω
  simp [weightedUrnPrefixEvent, Fin.forall_iff_castSucc, and_comm]

/-- Helper for Exercise 17.3.1: the black-prefix count is the sum of the `0/1` indicators of the
black entries. -/
theorem blackPrefixCount_eq_sum_indicator
    {n : ℕ} (x : Fin n → Bool) :
    blackPrefixCount x = ∑ i : Fin n, if x i = true then 1 else 0 := by
  classical
  -- Proof comment: the filtered cardinality of the black positions is exactly the finite sum of
  -- the Boolean indicators.
  simp [blackPrefixCount]

/-- Helper for Exercise 17.3.1: appending a black draw increases the black-prefix count by `1`. -/
theorem blackPrefixCount_snoc_true
    {n : ℕ} (x : Fin n → Bool) :
    blackPrefixCount (Fin.snoc x true) = blackPrefixCount x + 1 := by
  -- Proof comment: split the successor-index sum into the original prefix sum and the final
  -- indicator contribution.
  rw [blackPrefixCount_eq_sum_indicator, blackPrefixCount_eq_sum_indicator, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last, add_comm]

/-- Helper for Exercise 17.3.1: appending a red draw leaves the black-prefix count unchanged. -/
theorem blackPrefixCount_snoc_false
    {n : ℕ} (x : Fin n → Bool) :
    blackPrefixCount (Fin.snoc x false) = blackPrefixCount x := by
  -- Proof comment: the last indicator term is `0` when the appended draw is red.
  rw [blackPrefixCount_eq_sum_indicator, blackPrefixCount_eq_sum_indicator, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last, add_comm]

/-- Helper for Exercise 17.3.1: a Boolean prefix of length `n` can contain at most `n` black
entries. -/
theorem blackPrefixCount_le
    {n : ℕ} (x : Fin n → Bool) :
    blackPrefixCount x ≤ n := by
  classical
  -- Proof comment: the filtered set of black indices is a subset of the full `Fin n`.
  simpa [blackPrefixCount] using
    (Finset.card_le_univ (Finset.univ.filter fun i : Fin n ↦ x i = true))

end ProbabilityTheory

/-- The source-facing fraction of black balls in the urn after the first `n` draws. If
`L_n(ω)` is the number of black draws among `X 0 ω, …, X (n - 1) ω`, then the urn contains
`S + s * L_n(ω)` black balls and `R + r * (n - L_n(ω))` red balls. -/
noncomputable def generalizedPolyaUrnBlackBallFraction
    (R S r s : ℕ) (X : ℕ → Ω → Bool) (n : ℕ) (ω : Ω) : ℝ :=
  let ℓ := blackPrefixCount (fun i : Fin n ↦ X i ω)
  (((S + s * ℓ : ℕ) : ℝ) / ((R + S + r * (n - ℓ) + s * ℓ : ℕ) : ℝ))

/-- A `{0,1}`-valued process is the constant-reinforcement generalized two-color Pólya urn with
initial red/black counts `R`,`S` and reinforcement parameters `r`,`s` if every coordinate is
measurable and, after a prefix `x` of length `n` with `ℓ` black draws, the next draw is black
with probability equal to the actual fraction of black balls currently present in the urn,
namely `(S + s * ℓ) / (R + S + r * (n - ℓ) + s * ℓ)`. -/
def IsGeneralizedPolyaUrn
    (μ : Measure Ω) (R S r s : ℕ) (X : ℕ → Ω → Bool) : Prop :=
  (∀ n : ℕ, Measurable (X n)) ∧
    ∀ ⦃n : ℕ⦄ (x : Fin n → Bool),
      let ℓ := blackPrefixCount x
      μ (weightedUrnPrefixEvent X x ∩ {ω | X n ω = true}) =
        ((((S + s * ℓ : ℕ) : NNReal) /
            ((R + S + r * (n - ℓ) + s * ℓ : ℕ) : NNReal)) : ℝ≥0∞) *
          μ (weightedUrnPrefixEvent X x)

namespace IsGeneralizedPolyaUrn

variable {μ : Measure Ω} {R S r s : ℕ} {X : ℕ → Ω → Bool}

/-- Every coordinate of a constant-reinforcement generalized Pólya urn is measurable. -/
theorem measurable
    (hX : IsGeneralizedPolyaUrn μ R S r s X) (n : ℕ) :
    Measurable (X n) :=
by
  -- Proof comment: coordinate measurability is the first field of `IsGeneralizedPolyaUrn`.
  exact hX.1 n

/-- The defining one-step cylinder probability formula of the literal generalized Pólya urn. -/
theorem prefixEvent_inter_true_eq
    (hX : IsGeneralizedPolyaUrn μ R S r s X) {n : ℕ} (x : Fin n → Bool) :
    let ℓ := blackPrefixCount x
    μ (weightedUrnPrefixEvent X x ∩ {ω | X n ω = true}) =
      ((((S + s * ℓ : ℕ) : NNReal) /
          ((R + S + r * (n - ℓ) + s * ℓ : ℕ) : NNReal)) : ℝ≥0∞) *
        μ (weightedUrnPrefixEvent X x) :=
by
  -- Proof comment: the one-step cylinder identity is the second field of the owner predicate.
  exact hX.2 x

/-- Helper for Exercise 17.3.1: with positive initial mass, the complementary one-step red-cylinder
probability is the expected balanced red ratio times the prefix mass. -/
theorem prefixEvent_inter_false_eq
    [IsFiniteMeasure μ]
    (hX : IsGeneralizedPolyaUrn μ R S r s X) (hrs : r = s) (hRS : 0 < R + S)
    {n : ℕ} (x : Fin n → Bool) :
    μ (weightedUrnPrefixEvent X x ∩ {ω | X n ω = false}) =
      ((((R + s * (n - blackPrefixCount x) : ℕ) : NNReal) /
          ((R + S + s * n : ℕ) : NNReal)) : ℝ≥0∞) *
        μ (weightedUrnPrefixEvent X x) := by
  -- Route correction: instead of repeatedly normalizing the red branch inline, split the prefix
  -- mass into the disjoint `true/false` branches and cancel the common balanced `true` branch.
  set ℓ : ℕ := blackPrefixCount x
  set prefixEvent : Set Ω := weightedUrnPrefixEvent X x
  set truePart : Set Ω := prefixEvent ∩ {ω | X n ω = true}
  set falsePart : Set Ω := prefixEvent ∩ {ω | X n ω = false}
  have hprefix_meas : MeasurableSet prefixEvent :=
    measurableSet_weightedUrnPrefixEvent hX.measurable x
  have hfalse_meas : MeasurableSet falsePart := by
    -- Proof comment: the red branch is the measurable next-draw fiber inside the prefix cylinder.
    exact hprefix_meas.inter ((hX.measurable n) (measurableSet_singleton false))
  have hUnion : truePart ∪ falsePart = prefixEvent := by
    -- Proof comment: the next Boolean draw is either `true` or `false`, so the two branches
    -- partition the prefix cylinder.
    ext ω
    by_cases hω : X n ω = true
    · simp [truePart, falsePart, prefixEvent, hω]
    · have hω' : X n ω = false := by
        cases hXn : X n ω <;> simp_all
      simp [truePart, falsePart, prefixEvent, hω, hω']
  have hDisj : Disjoint truePart falsePart := by
    -- Proof comment: the next draw cannot simultaneously be `true` and `false`.
    refine Set.disjoint_left.2 ?_
    intro ω hω_true hω_false
    have htf : true = false := hω_true.2.symm.trans hω_false.2
    cases htf
  have hsum :
      μ prefixEvent = μ truePart + μ falsePart := by
    -- Proof comment: the prefix mass is the sum of the two disjoint one-step continuations.
    simpa [hUnion, truePart, falsePart, prefixEvent] using (measure_union hDisj hfalse_meas)
  have hle : ℓ ≤ n := by
    simpa [ℓ] using blackPrefixCount_le x
  have hbalancedMul :
      s * (n - ℓ) + s * ℓ = s * n := by
    -- Proof comment: factor `s` through `(n - ℓ) + ℓ = n`.
    simpa [Nat.mul_add, add_comm, add_left_comm, add_assoc] using
      congrArg (fun t : ℕ ↦ s * t) (Nat.sub_add_cancel hle)
  have hbalancedDen :
      R + S + r * (n - ℓ) + s * ℓ = R + S + s * n := by
    calc
      R + S + r * (n - ℓ) + s * ℓ = R + S + (s * (n - ℓ) + s * ℓ) := by
        simp [hrs, add_assoc, add_left_comm, add_comm]
      _ = R + S + s * n := by rw [hbalancedMul]
  have htrue :
      μ truePart =
        ((((S + s * ℓ : ℕ) : NNReal) / ((R + S + s * n : ℕ) : NNReal)) : ℝ≥0∞) *
          μ prefixEvent := by
    -- Proof comment: after balancing the denominator, the black branch is exactly the owner
    -- recursion formula.
    simpa [truePart, prefixEvent, ℓ, hbalancedDen] using hX.prefixEvent_inter_true_eq x
  have hden_pos : 0 < R + S + s * n := by
    omega
  have hden_ne : ((R + S + s * n : ℕ) : NNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hden_pos)
  have hratio_nn :
      ((S + s * ℓ : ℕ) : NNReal) / ((R + S + s * n : ℕ) : NNReal) +
          ((R + s * (n - ℓ) : ℕ) : NNReal) / ((R + S + s * n : ℕ) : NNReal) = 1 := by
    -- Proof comment: in the balanced urn, the black and red one-step ratios add up to `1`.
    rw [← add_div]
    have hnum :
        ((S + s * ℓ : ℕ) : NNReal) + ((R + s * (n - ℓ) : ℕ) : NNReal) =
          ((R + S + s * n : ℕ) : NNReal) := by
      exact_mod_cast (show S + s * ℓ + (R + s * (n - ℓ)) = R + S + s * n by omega)
    rw [hnum]
    exact div_self hden_ne
  have hratio :
      (((((S + s * ℓ : ℕ) : NNReal) / ((R + S + s * n : ℕ) : NNReal)) : ℝ≥0∞) +
          ((((R + s * (n - ℓ) : ℕ) : NNReal) / ((R + S + s * n : ℕ) : NNReal)) : ℝ≥0∞)) = 1 := by
    exact_mod_cast hratio_nn
  have hfactor :
      μ prefixEvent =
        ((((S + s * ℓ : ℕ) : NNReal) / ((R + S + s * n : ℕ) : NNReal)) : ℝ≥0∞) *
            μ prefixEvent +
          ((((R + s * (n - ℓ) : ℕ) : NNReal) / ((R + S + s * n : ℕ) : NNReal)) : ℝ≥0∞) *
            μ prefixEvent := by
    -- Proof comment: multiply the ratio decomposition of `1` by the common prefix mass.
    calc
      μ prefixEvent = (1 : ℝ≥0∞) * μ prefixEvent := by simp
      _ =
          ((((((S + s * ℓ : ℕ) : NNReal) / ((R + S + s * n : ℕ) : NNReal)) : ℝ≥0∞) +
                ((((R + s * (n - ℓ) : ℕ) : NNReal) / ((R + S + s * n : ℕ) : NNReal)) :
                  ℝ≥0∞)) *
              μ prefixEvent) := by
            rw [hratio]
      _ =
          ((((S + s * ℓ : ℕ) : NNReal) / ((R + S + s * n : ℕ) : NNReal)) : ℝ≥0∞) *
              μ prefixEvent +
            ((((R + s * (n - ℓ) : ℕ) : NNReal) / ((R + S + s * n : ℕ) : NNReal)) : ℝ≥0∞) *
              μ prefixEvent := by
            rw [add_mul]
  have hcancel :
      μ falsePart =
        ((((R + s * (n - ℓ) : ℕ) : NNReal) / ((R + S + s * n : ℕ) : NNReal)) : ℝ≥0∞) *
          μ prefixEvent := by
    have hsum' :
        ((((S + s * ℓ : ℕ) : NNReal) / ((R + S + s * n : ℕ) : NNReal)) : ℝ≥0∞) *
            μ prefixEvent +
          μ falsePart =
        ((((S + s * ℓ : ℕ) : NNReal) / ((R + S + s * n : ℕ) : NNReal)) : ℝ≥0∞) *
            μ prefixEvent +
          ((((R + s * (n - ℓ) : ℕ) : NNReal) / ((R + S + s * n : ℕ) : NNReal)) : ℝ≥0∞) *
            μ prefixEvent := by
      -- Proof comment: compare the branch decomposition with the factorized ratio decomposition.
      calc
        ((((S + s * ℓ : ℕ) : NNReal) / ((R + S + s * n : ℕ) : NNReal)) : ℝ≥0∞) *
              μ prefixEvent +
            μ falsePart =
            μ prefixEvent := by
          simpa [htrue] using hsum.symm
        _ =
            ((((S + s * ℓ : ℕ) : NNReal) / ((R + S + s * n : ℕ) : NNReal)) : ℝ≥0∞) *
                μ prefixEvent +
              ((((R + s * (n - ℓ) : ℕ) : NNReal) / ((R + S + s * n : ℕ) : NNReal)) :
                ℝ≥0∞) *
                μ prefixEvent := hfactor
    have hcoeff_ne_top :
        ((((S + s * ℓ : ℕ) : NNReal) / ((R + S + s * n : ℕ) : NNReal)) : ℝ≥0∞) ≠ ∞ := by
      exact ENNReal.div_ne_top ENNReal.coe_ne_top (by simpa using hden_ne)
    have hprefix_ne_top : μ prefixEvent ≠ ∞ := measure_ne_top μ prefixEvent
    have hleft_ne_top :
        (((((S + s * ℓ : ℕ) : NNReal) / ((R + S + s * n : ℕ) : NNReal)) : ℝ≥0∞) *
            μ prefixEvent) ≠ ∞ :=
      ENNReal.mul_ne_top hcoeff_ne_top hprefix_ne_top
    exact (ENNReal.add_right_inj hleft_ne_top).1 hsum'
  simpa [falsePart, prefixEvent, ℓ] using hcancel

/-- Helper for Exercise 17.3.1: the balanced closed-form mass attached to a Boolean word of
length `n` with `k` black entries. -/
noncomputable def balancedPrefixMass (R S s n k : ℕ) : ℝ≥0∞ :=
  (((Finset.prod (Finset.range k) fun j ↦ ((S + s * j : ℕ) : NNReal)) *
      (Finset.prod (Finset.range (n - k)) fun j ↦ ((R + s * j : ℕ) : NNReal))) /
    (Finset.prod (Finset.range n) fun j ↦ ((R + S + s * j : ℕ) : NNReal)) : NNReal)

/-- Helper for Exercise 17.3.1: once `R + S > 0`, every denominator factor in the balanced prefix
mass is nonzero. -/
private theorem balancedPrefixMass_denominator_ne_zero
    (hRS : 0 < R + S) (n : ℕ) :
    (Finset.prod (Finset.range n) fun j ↦ ((R + S + s * j : ℕ) : NNReal)) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 ?_
  intro j hj
  exact_mod_cast (Nat.ne_of_gt (by omega : 0 < R + S + s * j))

/-- Helper for Exercise 17.3.1: splitting off one successor factor from a balanced prefix-mass
ratio separates that factor from the remaining closed-form mass. -/
private theorem balancedPrefixMassSuccRatio
    (A B c D e : NNReal) :
    (((A * c) * B) / (D * e) : NNReal) = (c / e) * ((A * B) / D) := by
  -- Proof comment: commute the new successor factor next to the denominator factor and then use
  -- the standard quotient-of-products identity in `NNReal`.
  calc
    (((A * c) * B) / (D * e) : NNReal) = ((A * B) * c) / (D * e) := by
      ac_rfl
    _ = ((A * B) / D) * (c / e) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using (mul_div_mul_comm (A * B) c D e)
    _ = (c / e) * ((A * B) / D) := by
      rw [mul_comm]

/-- Helper for Exercise 17.3.1: appending a black draw multiplies the balanced closed-form prefix
mass by the expected balanced black ratio. -/
theorem balancedPrefixMass_step_true
    (hRS : 0 < R + S) {n k : ℕ} (hk : k ≤ n) :
    balancedPrefixMass R S s (n + 1) (k + 1) =
      ((((S + s * k : ℕ) : NNReal) / ((R + S + s * n : ℕ) : NNReal)) : ℝ≥0∞) *
        balancedPrefixMass R S s n k := by
  -- Proof comment: isolate the new black numerator factor and the new denominator factor, then
  -- split their ratio from the old balanced prefix mass with the dedicated `NNReal` bridge.
  rw [balancedPrefixMass, balancedPrefixMass]
  rw [show n + 1 - (k + 1) = n - k by omega]
  simp only [Finset.prod_range_succ]
  set A : NNReal := Finset.prod (Finset.range k) fun j ↦ ((S + s * j : ℕ) : NNReal)
  set B : NNReal := Finset.prod (Finset.range (n - k)) fun j ↦ ((R + s * j : ℕ) : NNReal)
  set D : NNReal := Finset.prod (Finset.range n) fun j ↦ ((R + S + s * j : ℕ) : NNReal)
  have hden_ne : ((R + S + s * n : ℕ) : NNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < R + S + s * n))
  have hratio :
      (((A * ((S + s * k : ℕ) : NNReal)) * B) /
          (D * ((R + S + s * n : ℕ) : NNReal)) : NNReal) =
        (((((S + s * k : ℕ) : NNReal) / ((R + S + s * n : ℕ) : NNReal)) *
            ((A * B) / D)) : NNReal) :=
    balancedPrefixMassSuccRatio A B ((S + s * k : ℕ) : NNReal) D
      ((R + S + s * n : ℕ) : NNReal)
  have hratio' :
      ((((A * ((S + s * k : ℕ) : NNReal)) * B) /
            (D * ((R + S + s * n : ℕ) : NNReal)) : NNReal) : ℝ≥0∞) =
        (((((((S + s * k : ℕ) : NNReal) / ((R + S + s * n : ℕ) : NNReal)) *
              ((A * B) / D)) : NNReal) : ℝ≥0∞)) :=
    congrArg (fun x : NNReal ↦ (x : ℝ≥0∞)) hratio
  rw [ENNReal.coe_mul, ENNReal.coe_div hden_ne] at hratio'
  simpa using hratio'

/-- Helper for Exercise 17.3.1: appending a red draw multiplies the balanced closed-form prefix
mass by the expected balanced red ratio. -/
theorem balancedPrefixMass_step_false
    (hRS : 0 < R + S) {n k : ℕ} (hk : k ≤ n) :
    balancedPrefixMass R S s (n + 1) k =
      ((((R + s * (n - k) : ℕ) : NNReal) / ((R + S + s * n : ℕ) : NNReal)) : ℝ≥0∞) *
        balancedPrefixMass R S s n k := by
  -- Route correction: split the successor red factor out of the second product first, then reuse
  -- the same `NNReal` quotient bridge as in the black-step recursion.
  rw [balancedPrefixMass, balancedPrefixMass]
  rw [show n + 1 - k = n - k + 1 by omega]
  simp only [Finset.prod_range_succ]
  set A : NNReal := Finset.prod (Finset.range k) fun j ↦ ((S + s * j : ℕ) : NNReal)
  set B : NNReal := Finset.prod (Finset.range (n - k)) fun j ↦ ((R + s * j : ℕ) : NNReal)
  set D : NNReal := Finset.prod (Finset.range n) fun j ↦ ((R + S + s * j : ℕ) : NNReal)
  have hden_ne : ((R + S + s * n : ℕ) : NNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < R + S + s * n))
  have hratio :
      ((A * (B * ((R + s * (n - k) : ℕ) : NNReal))) /
          (D * ((R + S + s * n : ℕ) : NNReal)) : NNReal) =
        (((((R + s * (n - k) : ℕ) : NNReal) / ((R + S + s * n : ℕ) : NNReal)) *
            ((A * B) / D)) : NNReal) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      balancedPrefixMassSuccRatio A B ((R + s * (n - k) : ℕ) : NNReal) D
        ((R + S + s * n : ℕ) : NNReal)
  have hratio' :
      ((((A * (B * ((R + s * (n - k) : ℕ) : NNReal))) /
            (D * ((R + S + s * n : ℕ) : NNReal)) : NNReal) : ℝ≥0∞)) =
        (((((((R + s * (n - k) : ℕ) : NNReal) / ((R + S + s * n : ℕ) : NNReal)) *
              ((A * B) / D)) : NNReal) : ℝ≥0∞)) :=
    congrArg (fun x : NNReal ↦ (x : ℝ≥0∞)) hratio
  rw [ENNReal.coe_mul, ENNReal.coe_div hden_ne] at hratio'
  simpa using hratio'

/-- Helper for Exercise 17.3.1: every full prefix cylinder has the balanced closed-form mass
determined only by its length and its number of black draws. -/
theorem balancedPrefixEventProb_eq_mass
    [IsProbabilityMeasure μ]
    (hX : IsGeneralizedPolyaUrn μ R S r s X) (hrs : r = s) (hRS : 0 < R + S)
    {n : ℕ} (x : Fin n → Bool) :
    μ (weightedUrnPrefixEvent X x) = balancedPrefixMass R S s n (blackPrefixCount x) := by
  -- Route correction: prove the full-prefix mass formula by `Fin.snocInduction`, consuming the
  -- repaired one-step branch identities instead of trying to normalize the whole product at once.
  refine Fin.snocInduction ?_ ?_ x
  · -- Proof comment: the empty prefix cylinder is the whole space, and the empty balanced mass
    -- is the empty product ratio `1`.
    calc
      μ (weightedUrnPrefixEvent X (Fin.elim0 : Fin 0 → Bool)) = μ Set.univ := by
        simp [weightedUrnPrefixEvent]
      _ = 1 := by simpa using (measure_univ : μ Set.univ = 1)
      _ = balancedPrefixMass R S s 0 (blackPrefixCount (Fin.elim0 : Fin 0 → Bool)) := by
        simp [balancedPrefixMass, blackPrefixCount]
  · intro n x b ih
    cases b
    · have hk : blackPrefixCount x ≤ n := blackPrefixCount_le x
      -- Proof comment: the red successor branch uses the complementary branch formula together
      -- with the closed-form red-step mass recursion.
      calc
        μ (weightedUrnPrefixEvent X (Fin.snoc x false)) =
            μ (weightedUrnPrefixEvent X x ∩ {ω | X n ω = false}) := by
              rw [weightedUrnPrefixEvent_snoc]
        _ =
            ((((R + s * (n - blackPrefixCount x) : ℕ) : NNReal) /
                ((R + S + s * n : ℕ) : NNReal)) : ℝ≥0∞) *
              μ (weightedUrnPrefixEvent X x) := by
                simpa using hX.prefixEvent_inter_false_eq hrs hRS x
        _ =
            ((((R + s * (n - blackPrefixCount x) : ℕ) : NNReal) /
                ((R + S + s * n : ℕ) : NNReal)) : ℝ≥0∞) *
              balancedPrefixMass R S s n (blackPrefixCount x) := by
                rw [ih]
        _ = balancedPrefixMass R S s (n + 1) (blackPrefixCount x) := by
              symm
              exact balancedPrefixMass_step_false hRS hk
        _ = balancedPrefixMass R S s (n + 1) (blackPrefixCount (Fin.snoc x false)) := by
              rw [blackPrefixCount_snoc_false]
    · have hk : blackPrefixCount x ≤ n := blackPrefixCount_le x
      have hbalancedMul :
          s * (n - blackPrefixCount x) + s * blackPrefixCount x = s * n := by
        -- Proof comment: factor `s` through the partition of the prefix into red and black draws.
        simpa [Nat.mul_add, add_comm, add_left_comm, add_assoc] using
          congrArg (fun t : ℕ ↦ s * t) (Nat.sub_add_cancel hk)
      have hbalancedDen :
          R + S + r * (n - blackPrefixCount x) + s * blackPrefixCount x = R + S + s * n := by
        calc
          R + S + r * (n - blackPrefixCount x) + s * blackPrefixCount x =
              R + S + (s * (n - blackPrefixCount x) + s * blackPrefixCount x) := by
                simp [hrs, add_assoc, add_left_comm, add_comm]
          _ = R + S + s * n := by rw [hbalancedMul]
      -- Proof comment: the black successor branch is the defining urn recursion plus the
      -- balanced black-step closed form.
      calc
        μ (weightedUrnPrefixEvent X (Fin.snoc x true)) =
            μ (weightedUrnPrefixEvent X x ∩ {ω | X n ω = true}) := by
              rw [weightedUrnPrefixEvent_snoc]
        _ =
            ((((S + s * blackPrefixCount x : ℕ) : NNReal) /
                ((R + S + s * n : ℕ) : NNReal)) : ℝ≥0∞) *
              μ (weightedUrnPrefixEvent X x) := by
                simpa [hbalancedDen] using hX.prefixEvent_inter_true_eq x
        _ =
            ((((S + s * blackPrefixCount x : ℕ) : NNReal) /
                ((R + S + s * n : ℕ) : NNReal)) : ℝ≥0∞) *
              balancedPrefixMass R S s n (blackPrefixCount x) := by
                rw [ih]
        _ = balancedPrefixMass R S s (n + 1) (blackPrefixCount x + 1) := by
              symm
              exact balancedPrefixMass_step_true hRS hk
        _ = balancedPrefixMass R S s (n + 1) (blackPrefixCount (Fin.snoc x true)) := by
              rw [blackPrefixCount_snoc_true]

/-- Helper for Exercise 17.3.1: permuting a Boolean word does not change its number of black
entries. -/
theorem blackPrefixCount_comp_perm
    {m : ℕ} (x : Fin m → Bool) (perm : Equiv.Perm (Fin m)) :
    blackPrefixCount (x ∘ perm) = blackPrefixCount x := by
  classical
  -- Proof comment: rewrite the black-count as a finite indicator sum and reindex that sum along
  -- the permutation of `Fin m`.
  rw [blackPrefixCount_eq_sum_indicator, blackPrefixCount_eq_sum_indicator]
  calc
    (∑ i : Fin m, if (x ∘ perm) i = true then 1 else 0)
        = ∑ i : Fin m, if x (perm i) = true then 1 else 0 := by
            rfl
    _ = ∑ i : Fin m, if x i = true then 1 else 0 := by
          exact Fintype.sum_bijective perm perm.bijective _ _ (fun i ↦ rfl)

/-- Helper for Exercise 17.3.1: the law of the full initial `m`-tuple is invariant under every
permutation of its coordinates. -/
theorem fullPrefix_identDistrib_perm
    [IsProbabilityMeasure μ]
    (hX : IsGeneralizedPolyaUrn μ R S r s X) (hrs : r = s) (hRS : 0 < R + S)
    {m : ℕ} (perm : Equiv.Perm (Fin m)) :
    IdentDistrib (fun ω i ↦ X (perm i) ω) (fun ω i ↦ X i ω) μ μ := by
  let Tσ : Ω → Fin m → Bool := fun ω i ↦ X (perm i) ω
  let T : Ω → Fin m → Bool := fun ω i ↦ X i ω
  have hTσ_meas : Measurable Tσ := by
    refine measurable_pi_lambda _ fun i ↦ ?_
    simpa [Tσ] using hX.measurable (perm i)
  have hT_meas : Measurable T := by
    refine measurable_pi_lambda _ fun i ↦ ?_
    simpa [T] using hX.measurable i
  refine ⟨hTσ_meas.aemeasurable, hT_meas.aemeasurable, ?_⟩
  apply (MeasureTheory.ext_iff_measureReal_singleton).2
  intro x
  have hTσ_preimage :
      Tσ ⁻¹' ({x} : Set (Fin m → Bool)) = weightedUrnPrefixEvent X (x ∘ perm.symm) := by
    ext ω
    constructor
    · intro hω i
      have hi := congrArg (fun f : Fin m → Bool ↦ f (perm.symm i)) hω
      simpa [Tσ, Function.comp] using hi
    · intro hω
      ext i
      simpa [Tσ, Function.comp] using hω (perm i)
  have hT_preimage :
      T ⁻¹' ({x} : Set (Fin m → Bool)) = weightedUrnPrefixEvent X x := by
    ext ω
    constructor
    · intro hω i
      have hi := congrArg (fun f : Fin m → Bool ↦ f i) hω
      simpa [T] using hi
    · intro hω
      ext i
      simpa [T] using hω i
  calc
    (Measure.map Tσ μ).real ({x} : Set (Fin m → Bool))
        = μ.real (weightedUrnPrefixEvent X (x ∘ perm.symm)) := by
            simpa [Measure.real_def, hTσ_preimage] using congrArg ENNReal.toReal
              (Measure.map_apply hTσ_meas (measurableSet_singleton x))
    _ = (balancedPrefixMass R S s m (blackPrefixCount (x ∘ perm.symm))).toReal := by
          rw [Measure.real_def, hX.balancedPrefixEventProb_eq_mass hrs hRS]
    _ = (balancedPrefixMass R S s m (blackPrefixCount x)).toReal := by
          rw [blackPrefixCount_comp_perm x perm.symm]
    _ = μ.real (weightedUrnPrefixEvent X x) := by
          rw [Measure.real_def, hX.balancedPrefixEventProb_eq_mass hrs hRS]
    _ = (Measure.map T μ).real ({x} : Set (Fin m → Bool)) := by
          symm
          simpa [Measure.real_def, hT_preimage] using congrArg ENNReal.toReal
            (Measure.map_apply hT_meas (measurableSet_singleton x))

/-- Helper for Exercise 17.3.1: permutations of a finite prefix act transitively on embeddings
into that prefix. -/
private theorem existsPermApplyEqOfEmbedding {m n : ℕ} (a b : Fin n ↪ Fin m) :
    ∃ ρ : Equiv.Perm (Fin m), ∀ i, ρ (b i) = a i := by
  classical
  let e : Set.range b ≃ Set.range a :=
    { toFun := fun x ↦ ⟨a (b.invOfMemRange x), Set.mem_range_self _⟩
      invFun := fun x ↦ ⟨b (a.invOfMemRange x), Set.mem_range_self _⟩
      left_inv := by
        intro x
        apply Subtype.ext
        simp
      right_inv := by
        intro x
        apply Subtype.ext
        simp }
  -- Proof comment: extend the permutation of the two finite ranges to all of the ambient prefix.
  refine ⟨e.extendSubtype, ?_⟩
  intro i
  rw [Equiv.extendSubtype_apply_of_mem e (b i) (Set.mem_range_self i)]
  simp [e]

/-- Helper for Exercise 17.3.1: restricting an ambient finite tuple law along an embedding
preserves identical distribution. -/
private theorem identDistribRestrictTuple {m n : ℕ} {F G : Ω → Fin m → Bool}
    (hFG : IdentDistrib F G μ μ) (a : Fin n ↪ Fin m) :
    IdentDistrib (fun ω i ↦ F ω (a i)) (fun ω i ↦ G ω (a i)) μ μ := by
  have hrestrict : Measurable (fun z : Fin m → Bool ↦ fun i ↦ z (a i)) := by
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact measurable_pi_apply (a i)
  -- Proof comment: compose the ambient tuple law with the measurable restriction map.
  simpa [Function.comp] using hFG.comp hrestrict

/-- Helper for Exercise 17.3.1: with zero initial mass, every all-red prefix cylinder has
probability `1`. -/
private theorem zeroInitialMass_allFalsePrefix_prob_one
    [IsProbabilityMeasure μ] (hX : IsGeneralizedPolyaUrn μ 0 0 r s X) :
    ∀ n : ℕ, μ (weightedUrnPrefixEvent X (fun _ : Fin n ↦ false)) = 1 := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: the empty prefix cylinder is the whole probability space.
      simp [weightedUrnPrefixEvent]
  | succ n ih =>
      let x : Fin n → Bool := fun _ ↦ false
      let A : Set Ω := weightedUrnPrefixEvent X x ∩ {ω | X n ω = false}
      let B : Set Ω := weightedUrnPrefixEvent X x ∩ {ω | X n ω = true}
      have hsnoc : weightedUrnPrefixEvent X (Fin.snoc x false) = A := by
        simp [A, weightedUrnPrefixEvent_snoc]
      have htrue_zero :
          μ B = 0 := by
        -- Proof comment: with zero initial black mass and an all-red prefix, the next black
        -- branch has probability zero by the defining urn recursion.
        simpa [B, x, blackPrefixCount_eq_sum_indicator] using hX.prefixEvent_inter_true_eq x
      have hunion :
          weightedUrnPrefixEvent X x = A ∪ B := by
        -- Proof comment: the next draw is either red or black, so the old prefix cylinder
        -- splits into the two one-step extensions.
        ext ω
        by_cases hω : X n ω
        · simp [A, B, hω]
        · simp [A, B, hω]
      have hdisj : Disjoint A B := by
        -- Proof comment: the red and black one-step extensions are disjoint.
        refine Set.disjoint_left.2 ?_
        intro ω hfalse htrue
        exact Bool.false_ne_true (hfalse.2.symm.trans htrue.2)
      have hmeas_B : MeasurableSet B :=
        (measurableSet_weightedUrnPrefixEvent hX.measurable x).inter
          ((hX.measurable n) (measurableSet_singleton true))
      have hstep :
          μ (weightedUrnPrefixEvent X (Fin.snoc x false)) = 1 := by
        calc
          μ (weightedUrnPrefixEvent X (Fin.snoc x false))
              = μ A := by rw [hsnoc]
          _ = μ A + μ B := by rw [htrue_zero, add_zero]
          _ = μ (A ∪ B) := by rw [measure_union hdisj hmeas_B]
          _ = μ (weightedUrnPrefixEvent X x) := by rw [hunion]
          _ = 1 := ih
      -- Proof comment: the all-red prefix of length `n + 1` is exactly the one-step red
      -- extension of the all-red prefix of length `n`.
      have hword : Fin.snoc x false = (fun _ : Fin (n + 1) ↦ false) := by
        ext i
        simp [x, Fin.snoc]
      simpa [hword] using hstep

/-- Helper for Exercise 17.3.1: with zero initial mass, every coordinate draw is almost surely
red. -/
private theorem zeroInitialMass_draw_false_ae
    [IsProbabilityMeasure μ] (hX : IsGeneralizedPolyaUrn μ 0 0 r s X) (n : ℕ) :
    ∀ᵐ ω ∂μ, X n ω = false := by
  let A : Set Ω := {ω | X n ω = false}
  have hA : MeasurableSet A := (hX.measurable n) (measurableSet_singleton false)
  have hprefix_one :
      μ (weightedUrnPrefixEvent X (Fin.snoc (fun _ : Fin n ↦ false) false)) = 1 := by
    -- Proof comment: apply the full-prefix result to the all-red word of length `n + 1`.
    have hword :
        Fin.snoc (fun _ : Fin n ↦ false) false = (fun _ : Fin (n + 1) ↦ false) := by
      ext i
      simp [Fin.snoc]
    simpa [hword] using zeroInitialMass_allFalsePrefix_prob_one hX (n + 1)
  have hsubset :
      weightedUrnPrefixEvent X (Fin.snoc (fun _ : Fin n ↦ false) false) ⊆ A := by
    -- Proof comment: every sample in the all-red prefix cylinder has its last coordinate equal
    -- to `false`.
    intro ω hω
    simpa [A] using hω (Fin.last n)
  have hprob : μ A = 1 := by
    have hlower : 1 ≤ μ A := by
      calc
        1 = μ (weightedUrnPrefixEvent X (Fin.snoc (fun _ : Fin n ↦ false) false)) := hprefix_one.symm
        _ ≤ μ A := measure_mono hsubset
    have hupper : μ A ≤ 1 := by
      calc
        μ A ≤ μ Set.univ := measure_mono (Set.subset_univ A)
        _ = 1 := measure_univ
    exact le_antisymm hupper hlower
  -- Proof comment: convert the full-mass event into the corresponding almost-sure statement.
  exact (mem_ae_iff_prob_eq_one hA).2 hprob

/-- Helper for Exercise 17.3.1: two distinct full-prefix cylinders of the same length are
disjoint. -/
private theorem weightedUrnPrefixEvent_disjoint_of_ne
    {X : ℕ → Ω → Bool} {n : ℕ} {x y : Fin n → Bool} (hxy : x ≠ y) :
    Disjoint (weightedUrnPrefixEvent X x) (weightedUrnPrefixEvent X y) := by
  -- Proof comment: a sample point lying in both cylinders would force equality of the two
  -- prescribed Boolean words coordinatewise.
  refine Set.disjoint_left.2 ?_
  intro ω hx hy
  apply hxy
  ext i
  exact (hx i).symm.trans (hy i)

/-- Helper for Exercise 17.3.1: a sparse cylinder inside a fixed prefix is the disjoint union of
its full-prefix completions. -/
private theorem sparseTupleEvent_eq_biUnion_completionPrefix
    {X : ℕ → Ω → Bool} {N n : ℕ} (u : Fin n ↪ Fin N) (x : Fin n → Bool) :
    {ω | ∀ i : Fin n, X (u i) ω = x i} =
      ⋃ y ∈ Finset.univ.filter (fun y : Fin N → Bool ↦ y ∘ u = x),
        weightedUrnPrefixEvent X y := by
  -- Proof comment: membership in the sparse cylinder is equivalent to the existence of a full
  -- prefix word `y` extending `x` and matching the realized first `N` draws.
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    weightedUrnPrefixEvent]
  constructor
  · intro hω
    refine ⟨fun j ↦ X j ω, ?_, ?_⟩
    · funext i
      exact hω i
    · intro j
      rfl
  · rintro ⟨y, hy, hprefix⟩ i
    have hcoord := hprefix (u i)
    have hyi : y (u i) = x i := by
      exact congrArg (fun f : Fin n → Bool ↦ f i) hy
    exact hcoord.trans hyi

/-- Helper for Exercise 17.3.1: the measure of a sparse cylinder is the finite sum of the measures
of its full-prefix completions. -/
private theorem sparseTupleMeasure_eq_completionCylinderSum
    {X : ℕ → Ω → Bool} (hX : ∀ n : ℕ, Measurable (X n))
    {N n : ℕ} (u : Fin n ↪ Fin N) (x : Fin n → Bool) :
    μ {ω | ∀ i : Fin n, X (u i) ω = x i} =
      Finset.sum (Finset.univ.filter (fun y : Fin N → Bool ↦ y ∘ u = x))
        (fun y ↦ μ (weightedUrnPrefixEvent X y)) := by
  -- Proof comment: the completion cylinders are pairwise disjoint, so the measure of the sparse
  -- cylinder is the finite sum of the measures of all compatible full-prefix completions.
  rw [sparseTupleEvent_eq_biUnion_completionPrefix]
  exact measure_biUnion_finset
    (fun y hy z hz hyz ↦ weightedUrnPrefixEvent_disjoint_of_ne hyz)
    (fun y hy ↦ measurableSet_weightedUrnPrefixEvent hX y)

/-- Helper for Exercise 17.3.1: inside a fixed initial segment, the probability of a sparse
Boolean cylinder is the sum of the balanced masses of its full-prefix completions. -/
private theorem sparseTupleProb_eq_completionSum
    [IsProbabilityMeasure μ]
    (hX : IsGeneralizedPolyaUrn μ R S r s X) (hrs : r = s) (hRS : 0 < R + S)
    {N n : ℕ} (u : Fin n ↪ Fin N) (x : Fin n → Bool) :
    μ {ω | ∀ i : Fin n, X (u i) ω = x i} =
      Finset.sum (Finset.univ.filter (fun y : Fin N → Bool ↦ y ∘ u = x))
        (fun y ↦ balancedPrefixMass R S s N (blackPrefixCount y)) := by
  -- Proof comment: rewrite the sparse-cylinder measure as the completion-cylinder sum and then
  -- replace each completion-cylinder probability by its balanced closed form.
  calc
    μ {ω | ∀ i : Fin n, X (u i) ω = x i} =
        Finset.sum (Finset.univ.filter (fun y : Fin N → Bool ↦ y ∘ u = x))
          (fun y ↦ μ (weightedUrnPrefixEvent X y)) := by
            exact sparseTupleMeasure_eq_completionCylinderSum hX.measurable u x
    _ =
        Finset.sum (Finset.univ.filter (fun y : Fin N → Bool ↦ y ∘ u = x))
          (fun y ↦ balancedPrefixMass R S s N (blackPrefixCount y)) := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            rw [hX.balancedPrefixEventProb_eq_mass hrs hRS]

/-- Helper for Exercise 17.3.1: within a fixed prefix `Fin N`, the law of an injective `n`-tuple
depends only on the prescribed Boolean word and not on the embedding. -/
private theorem sparseTupleIdentDistribWithinPrefix
    [IsProbabilityMeasure μ]
    (hX : IsGeneralizedPolyaUrn μ R S r s X) (hrs : r = s) (hRS : 0 < R + S)
    {N n : ℕ} (u v : Fin n ↪ Fin N) :
    IdentDistrib (fun ω i ↦ X (u i) ω) (fun ω i ↦ X (v i) ω) μ μ := by
  obtain ⟨ρ, hρ⟩ := existsPermApplyEqOfEmbedding u v
  -- Proof comment: first permute the ambient `Fin N`-prefix so that the image of `v` moves onto
  -- the image of `u`, then restrict the ambient tuple law back along `v`.
  have hambient : IdentDistrib (fun ω i ↦ X (ρ i) ω) (fun ω i ↦ X i ω) μ μ :=
    hX.fullPrefix_identDistrib_perm hrs hRS ρ
  have hrestricted :
      IdentDistrib (fun ω i ↦ X (ρ (v i)) ω) (fun ω i ↦ X (v i) ω) μ μ :=
    identDistribRestrictTuple hambient v
  simpa [hρ] using hrestricted

/-- Helper for Exercise 17.3.1: if the urn starts with zero mass, every sparse tuple is almost
surely the constant-red tuple. -/
private theorem sparseTuple_ae_eq_constFalse_of_zeroInitialMass
    [IsProbabilityMeasure μ] (hX : IsGeneralizedPolyaUrn μ 0 0 r s X)
    {n : ℕ} (u : Fin n ↪ ℕ) :
    (fun ω i ↦ X (u i) ω) =ᵐ[μ] fun _ _ ↦ false := by
  have hcoords : ∀ᵐ ω ∂μ, ∀ i : Fin n, X (u i) ω = false := by
    exact ae_all_iff.2 fun i ↦ zeroInitialMass_draw_false_ae hX (u i)
  filter_upwards [hcoords] with ω hω
  ext i
  exact hω i

/-- Helper for Exercise 17.3.1: two finite injective index tuples in `ℕ` fit into a common
initial segment `Fin N` without changing their coordinate values. -/
private theorem commonPrefixLiftOfEmbeddings
    {n : ℕ} (u v : Fin n ↪ ℕ) :
    ∃ N : ℕ, ∃ uN vN : Fin n ↪ Fin N,
      (∀ i, ((uN i : Fin N) : ℕ) = u i) ∧
        ∀ i, ((vN i : Fin N) : ℕ) = v i := by
  classical
  let s : Finset ℕ := (Finset.univ.image u) ∪ (Finset.univ.image v)
  let N : ℕ := s.sup id + 1
  have hu_lt : ∀ i : Fin n, u i < N := by
    intro i
    have hmem : u i ∈ s := by
      refine Finset.mem_union.mpr (Or.inl ?_)
      exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩
    -- Proof comment: every value of `u` lies below the maximum of the finite support union.
    exact Nat.lt_succ_of_le (by simpa using (show id (u i) ≤ s.sup id from Finset.le_sup hmem))
  have hv_lt : ∀ i : Fin n, v i < N := by
    intro i
    have hmem : v i ∈ s := by
      refine Finset.mem_union.mpr (Or.inr ?_)
      exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩
    -- Proof comment: the same finite-support bound works for the values of `v`.
    exact Nat.lt_succ_of_le (by simpa using (show id (v i) ≤ s.sup id from Finset.le_sup hmem))
  let uN : Fin n ↪ Fin N :=
    ⟨fun i ↦ ⟨u i, hu_lt i⟩, fun i j hij ↦ u.injective (congrArg Fin.val hij)⟩
  let vN : Fin n ↪ Fin N :=
    ⟨fun i ↦ ⟨v i, hv_lt i⟩, fun i j hij ↦ v.injective (congrArg Fin.val hij)⟩
  refine ⟨N, uN, vN, ?_, ?_⟩
  · intro i
    rfl
  · intro i
    rfl

/-- Helper for Exercise 17.3.1: with positive initial mass, the law of a sparse tuple depends
only on the chosen Boolean word, not on the injective index tuple in `ℕ`. -/
private theorem sparseTupleIdentDistrib
    [IsProbabilityMeasure μ]
    (hX : IsGeneralizedPolyaUrn μ R S r s X) (hrs : r = s) (hRS : 0 < R + S)
    {n : ℕ} (u v : Fin n ↪ ℕ) :
    IdentDistrib (fun ω i ↦ X (u i) ω) (fun ω i ↦ X (v i) ω) μ μ := by
  obtain ⟨N, uN, vN, huN, hvN⟩ := commonPrefixLiftOfEmbeddings u v
  have hprefix :
      IdentDistrib (fun ω i ↦ X (uN i) ω) (fun ω i ↦ X (vN i) ω) μ μ :=
    sparseTupleIdentDistribWithinPrefix hX hrs hRS uN vN
  -- Proof comment: once both tuples live in the same initial segment, the within-prefix law
  -- bridge applies directly and the coercions back to `ℕ` are definitionally stable.
  simpa [huN, hvN] using hprefix

/-- Helper for Exercise 17.3.1: balanced constant-reinforcement generalized Pólya urns are
exchangeable. -/
theorem balancedUrn_isExchangeable
    [IsProbabilityMeasure μ]
    (hX : IsGeneralizedPolyaUrn μ R S r s X) (hrs : r = s) :
    IsExchangeable X μ := by
  refine (isExchangeable_iff_identDistrib_of_pairwise_distinct X μ).2 ?_
  intro n u v
  by_cases hRS : 0 < R + S
  · -- Proof comment: the positive-mass branch is exactly the sparse-tuple law transported from a
    -- common finite prefix.
    exact sparseTupleIdentDistrib hX hrs hRS u v
  · have hzero : R = 0 ∧ S = 0 := by
      omega
    rcases hzero with ⟨rfl, rfl⟩
    have hu :
        (fun ω i ↦ X (u i) ω) =ᵐ[μ] fun _ _ ↦ false :=
      sparseTuple_ae_eq_constFalse_of_zeroInitialMass hX u
    have hv :
        (fun ω i ↦ X (v i) ω) =ᵐ[μ] fun _ _ ↦ false :=
      sparseTuple_ae_eq_constFalse_of_zeroInitialMass hX v
    have hTu_meas :
        AEMeasurable (fun ω i ↦ X (u i) ω) μ := by
      exact (measurable_pi_lambda _ fun i ↦ hX.measurable (u i)).aemeasurable
    have hTv_meas :
        AEMeasurable (fun ω i ↦ X (v i) ω) μ := by
      exact (measurable_pi_lambda _ fun i ↦ hX.measurable (v i)).aemeasurable
    -- Proof comment: when the urn starts with zero total mass, both tuples collapse almost surely
    -- to the constant-red word, so their laws coincide by `IdentDistrib.of_ae_eq`.
    exact (IdentDistrib.of_ae_eq hTu_meas hu).trans (IdentDistrib.of_ae_eq hTv_meas hv).symm

/-- Corollary for Exercise 17.3.1: under balanced reinforcement, the generalized urn admits a
directing random parameter `Z ∈ [0,1]` such that, conditionally on `Z`, the draws are i.i.d.
Bernoulli with parameter `Z`. -/
theorem exists_conditionalBernoulliParameter
    [IsProbabilityMeasure μ] [StandardBorelSpace Ω]
    (hX : IsGeneralizedPolyaUrn μ R S r s X) (hrs : r = s) :
    ∃ Z : Ω → unitInterval,
      IsConditionallyBernoulliIID Z X μ := by
  -- Proof comment: the balanced generalized urn is exchangeable, so the chapter Bernoulli
  -- de Finetti theorem produces the required directing parameter.
  exact exists_conditionalBernoulliParameter_of_isExchangeable
    (hX.balancedUrn_isExchangeable hrs) hX.measurable

end IsGeneralizedPolyaUrn

/-- Helper for Exercise 17.3.1: the `NNReal` Bernoulli parameter attached to a `unitInterval`
parameter is bounded by `1`, so the Bernoulli pmf is well-formed. -/
private theorem unitInterval_toNNReal_le_one (y : unitInterval) : unitInterval.toNNReal y ≤ 1 := by
  -- Proof comment: unwrap the `unitInterval` bound and rewrite the coercion into `NNReal`.
  simpa [unitInterval.toNNReal] using y.2.2

/-- Helper for Exercise 17.3.1: the `Bool`-valued Bernoulli probability measure attached to a
`unitInterval` parameter. -/
private noncomputable def boolBernoulliProbabilityMeasure (y : unitInterval) :
    ProbabilityMeasure Bool :=
  ⟨(PMF.bernoulli (unitInterval.toNNReal y) (unitInterval_toNNReal_le_one y)).toMeasure,
    inferInstance⟩

/-- Helper for Exercise 17.3.1: taking the `{true}` mass of a `Bool`-valued probability law is a
measurable map into `unitInterval`. -/
private noncomputable def boolProbabilityParameter (ξ : ProbabilityMeasure Bool) : unitInterval :=
  ⟨(ξ : Measure Bool).real {true}, ⟨measureReal_nonneg, measureReal_le_one⟩⟩

/-- Helper for Exercise 17.3.1: taking the `{true}` mass of a `Bool` law is measurable. -/
private theorem measurable_boolProbabilityParameter : Measurable boolProbabilityParameter := by
  -- Proof comment: the parameter is just the measurable singleton-mass evaluation map with values
  -- bundled into the unit interval.
  refine Measurable.subtype_mk ?_
  exact (((Measure.measurable_coe (measurableSet_singleton true)).ennreal_toReal).comp
    measurable_subtype_coe)

/-- Helper for Exercise 17.3.1: the real singleton masses of the Bernoulli law on `Bool` have the
expected `y`/`1 - y` form. -/
private theorem boolBernoulliProbabilityMeasure_real_singleton (y : unitInterval) (b : Bool) :
    (boolBernoulliProbabilityMeasure y : Measure Bool).real ({b} : Set Bool) =
      if b then (y : ℝ) else 1 - (y : ℝ) := by
  have hy : unitInterval.toNNReal y ≤ 1 := unitInterval_toNNReal_le_one y
  cases b
  · simp [boolBernoulliProbabilityMeasure, Measure.real_def, hy]
  · simp [boolBernoulliProbabilityMeasure, Measure.real_def]

/-- Helper for Exercise 17.3.1: the Bernoulli law recovers its own parameter from the `{true}`
mass. -/
private theorem boolProbabilityParameter_boolBernoulliProbabilityMeasure (y : unitInterval) :
    boolProbabilityParameter (boolBernoulliProbabilityMeasure y) = y := by
  -- Proof comment: the `unitInterval` value is determined by its real coercion, and the `{true}`
  -- mass of the Bernoulli law is exactly the Bernoulli parameter.
  apply Subtype.ext
  change (boolBernoulliProbabilityMeasure y : Measure Bool).real ({true} : Set Bool) = (y : ℝ)
  simpa using boolBernoulliProbabilityMeasure_real_singleton y true

/-- Helper for Exercise 17.3.1: the Bernoulli-law map from `[0,1]` into `ProbabilityMeasure Bool`
is measurable. -/
private theorem measurable_boolBernoulliProbabilityMeasure :
    Measurable boolBernoulliProbabilityMeasure := by
  -- Proof comment: on the finite space `Bool`, every measurable set is a union of singleton
  -- atoms, so singleton masses determine measurability of the law-valued map.
  refine Measurable.subtype_mk ?_
  refine Measure.measurable_of_measurable_coe _ fun s _ ↦ ?_
  by_cases hfalse : false ∈ s
  · by_cases htrue : true ∈ s
    · have hs : s = Set.univ := by
        ext b
        cases b <;> simp [hfalse, htrue]
      subst hs
      change Measurable fun y : unitInterval ↦ (boolBernoulliProbabilityMeasure y : Measure Bool) Set.univ
      convert measurable_const using 1
      funext y
      exact measure_univ
    · have hs : s = ({false} : Set Bool) := by
        ext b
        cases b <;> simp [hfalse, htrue]
      subst hs
      change Measurable fun y : unitInterval ↦
        (boolBernoulliProbabilityMeasure y : Measure Bool) ({false} : Set Bool)
      have hfalseMass :
          (fun y : unitInterval ↦
            (boolBernoulliProbabilityMeasure y : Measure Bool) ({false} : Set Bool)) =
            fun y : unitInterval ↦ ENNReal.ofReal (1 - (y : ℝ)) := by
        funext y
        rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
        rw [← Measure.real_def, boolBernoulliProbabilityMeasure_real_singleton]
        simp
      rw [hfalseMass]
      exact (measurable_const.sub measurable_subtype_coe).ennreal_ofReal
  · by_cases htrue : true ∈ s
    · have hs : s = ({true} : Set Bool) := by
        ext b
        cases b <;> simp [hfalse, htrue]
      subst hs
      change Measurable fun y : unitInterval ↦
        (boolBernoulliProbabilityMeasure y : Measure Bool) ({true} : Set Bool)
      have htrueMass :
          (fun y : unitInterval ↦
            (boolBernoulliProbabilityMeasure y : Measure Bool) ({true} : Set Bool)) =
            fun y : unitInterval ↦ ENNReal.ofReal (y : ℝ) := by
        funext y
        rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
        rw [← Measure.real_def, boolBernoulliProbabilityMeasure_real_singleton]
        simp
      rw [htrueMass]
      exact measurable_subtype_coe.ennreal_ofReal
    · have hs : s = (∅ : Set Bool) := by
        ext b
        cases b <;> simp [hfalse, htrue]
      subst hs
      change Measurable fun y : unitInterval ↦ (boolBernoulliProbabilityMeasure y : Measure Bool) ∅
      convert measurable_const using 1
      funext y
      exact measure_empty

/-- Helper for Exercise 17.3.1: a probability measure on `Bool` is exactly the Bernoulli law with
parameter equal to its `{true}` mass. -/
private theorem boolBernoulliProbabilityMeasure_boolProbabilityParameter
    (ξ : ProbabilityMeasure Bool) :
    boolBernoulliProbabilityMeasure (boolProbabilityParameter ξ) = ξ := by
  -- Proof comment: two probability laws on `Bool` are determined by the masses of `{true}` and
  -- `{false}`; the second mass is forced by the complement identity.
  let μ1 : Measure Bool := boolBernoulliProbabilityMeasure (boolProbabilityParameter ξ)
  let μ2 : Measure Bool := ξ
  apply Subtype.ext
  change μ1 = μ2
  letI : SigmaFinite μ1 := by infer_instance
  letI : SigmaFinite μ2 := by infer_instance
  apply (MeasureTheory.ext_iff_measureReal_singleton).2
  intro b
  cases b
  · have hcompl : ({true} : Set Bool)ᶜ = ({false} : Set Bool) := by
      ext x
      cases x <;> simp
    have hprob_compl :
        (ξ : Measure Bool).real ({true} : Set Bool) +
          (ξ : Measure Bool).real ({true} : Set Bool)ᶜ = 1 := by
      exact
        (probReal_add_probReal_compl (measurableSet_singleton true) :
          (ξ : Measure Bool).real ({true} : Set Bool) +
            (ξ : Measure Bool).real ({true} : Set Bool)ᶜ = 1)
    have hprob :
        (ξ : Measure Bool).real ({true} : Set Bool) +
          (ξ : Measure Bool).real ({false} : Set Bool) = 1 := by
      simpa [hcompl] using hprob_compl
    have hfalse :
        (ξ : Measure Bool).real ({false} : Set Bool) =
          1 - (ξ : Measure Bool).real ({true} : Set Bool) := by
      linarith
    -- Proof comment: the `{false}` mass is the complement of the parameter mass.
    simpa [μ1, μ2, boolProbabilityParameter, hfalse] using
      (boolBernoulliProbabilityMeasure_real_singleton (boolProbabilityParameter ξ) false)
  · -- Proof comment: the Bernoulli parameter was defined to be the `{true}` mass itself.
    simpa [μ1, μ2, boolProbabilityParameter] using
      (boolBernoulliProbabilityMeasure_real_singleton (boolProbabilityParameter ξ) true)

/-- Helper for Exercise 17.3.1: the directing `Bool` law and its Bernoulli parameter induce the
same conditioning `σ`-algebra. -/
private theorem comap_boolProbabilityParameter_eq
    {xiInf : Ω → ProbabilityMeasure Bool} :
    MeasurableSpace.comap (fun ω ↦ boolProbabilityParameter (xiInf ω)) inferInstance =
      MeasurableSpace.comap xiInf inferInstance := by
  apply le_antisymm
  · -- Proof comment: `ξ ↦ ξ{true}` is measurable, so the parameter is measurable with respect to
    -- the directing law.
    have hparam :
        Measurable[MeasurableSpace.comap xiInf inferInstance]
          (fun ω ↦ boolProbabilityParameter (xiInf ω)) :=
      measurable_boolProbabilityParameter.comp (Measurable.of_comap_le le_rfl)
    exact hparam.comap_le
  · have hback :
        Measurable[MeasurableSpace.comap
            (fun ω ↦ boolProbabilityParameter (xiInf ω)) inferInstance]
          (fun ω ↦ boolBernoulliProbabilityMeasure (boolProbabilityParameter (xiInf ω))) :=
      measurable_boolBernoulliProbabilityMeasure.comp (Measurable.of_comap_le le_rfl)
    have hrepr :
        (fun ω ↦ boolBernoulliProbabilityMeasure (boolProbabilityParameter (xiInf ω))) = xiInf := by
      funext ω
      exact boolBernoulliProbabilityMeasure_boolProbabilityParameter (xiInf ω)
    -- Proof comment: conversely, the full `Bool` law is recovered measurably from the parameter.
    have hxi :
        Measurable[MeasurableSpace.comap
            (fun ω ↦ boolProbabilityParameter (xiInf ω)) inferInstance] xiInf := by
      simpa [hrepr] using hback
    exact hxi.comap_le

/-- Helper for Exercise 17.3.1: the Bernoulli-law map and its parameter map induce the same
conditioning `σ`-algebra. -/
private theorem comap_boolBernoulliProbabilityMeasure_eq
    {Z : Ω → unitInterval} :
    MeasurableSpace.comap (fun ω ↦ boolBernoulliProbabilityMeasure (Z ω)) inferInstance =
      MeasurableSpace.comap Z inferInstance := by
  apply le_antisymm
  · have hlaw :
        Measurable[MeasurableSpace.comap Z inferInstance]
          (fun ω ↦ boolBernoulliProbabilityMeasure (Z ω)) :=
      measurable_boolBernoulliProbabilityMeasure.comp (Measurable.of_comap_le le_rfl)
    -- Proof comment: the Bernoulli law is a measurable function of its parameter.
    exact hlaw.comap_le
  · have hparam :
        Measurable[MeasurableSpace.comap
            (fun ω ↦ boolBernoulliProbabilityMeasure (Z ω)) inferInstance]
          (fun ω ↦ boolProbabilityParameter (boolBernoulliProbabilityMeasure (Z ω))) :=
      measurable_boolProbabilityParameter.comp (Measurable.of_comap_le le_rfl)
    have hrepr :
        (fun ω ↦ boolProbabilityParameter (boolBernoulliProbabilityMeasure (Z ω))) = Z := by
      funext ω
      exact boolProbabilityParameter_boolBernoulliProbabilityMeasure (Z ω)
    -- Proof comment: conversely, the parameter is recovered measurably from the Bernoulli law.
    have hZ :
        Measurable[MeasurableSpace.comap
            (fun ω ↦ boolBernoulliProbabilityMeasure (Z ω)) inferInstance] Z := by
      simpa [hrepr] using hparam
    exact hZ.comap_le

/-- Helper for Exercise 17.3.1: the coercion of a `unitInterval`-valued random variable has range
contained in the bounded interval `[0,1]`. -/
private theorem isBounded_range_coe_unitInterval (Z : Ω → unitInterval) :
    Bornology.IsBounded (Set.range fun ω ↦ (Z ω : ℝ)) := by
  -- Proof comment: every value of `Z` already lies in the compact interval `[0,1]`.
  refine (Metric.isBounded_Icc (0 : ℝ) 1).subset ?_
  rintro _ ⟨ω, rfl⟩
  exact ⟨(Z ω).2.1, (Z ω).2.2⟩


/-- Helper for Exercise 17.3.1: the event that the first `n` draws are all black is the full
`true`-valued prefix cylinder. -/
private theorem allBlackPrefixEvent_eq_iInter
    {X : ℕ → Ω → Bool} {n : ℕ} :
    weightedUrnPrefixEvent X (fun _ : Fin n ↦ true) =
      ⋂ i : Fin n, X i ⁻¹' ({true} : Set Bool) := by
  -- Proof comment: unfold the prefix cylinder and rewrite the pointwise universal quantifier as
  -- an intersection of singleton fibers.
  ext ω
  simp [weightedUrnPrefixEvent]

/-- Helper for Exercise 17.3.1: the singleton conditional probability of one Bernoulli coordinate
is the Bernoulli mass determined by the directing parameter. -/
private theorem condProbBoolSingleton_eq_bernoulliMass_ae
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → unitInterval} {X : ℕ → Ω → Bool}
    (hX : IsConditionallyBernoulliIID Z X μ) (i : ℕ) (b : Bool) :
    μ⟦X i ⁻¹' ({b} : Set Bool) | MeasurableSpace.comap Z inferInstance⟧ =ᵐ[μ]
      fun ω ↦ if b then (Z ω : ℝ) else 1 - (Z ω : ℝ) := by
  have hcond :
      μ⟦X i ⁻¹' ({b} : Set Bool) | MeasurableSpace.comap Z inferInstance⟧ =ᵐ[μ]
        fun ω ↦ (condDistrib (X i) Z μ (Z ω)).real ({b} : Set Bool) := by
    -- Proof comment: rewrite the conditional probability through the regular conditional
    -- distribution of the coordinate `X i` given `Z`.
    simpa using
      (condDistrib_ae_eq_condExp hX.measurable
        ((IsConditionallyBernoulliIID.isConditionallyIID hX).1.1 i)
        (measurableSet_singleton b)).symm
  have hbernoulli_map :
      ∀ᵐ y ∂μ.map Z,
        (condDistrib (X i) Z μ y).real ({b} : Set Bool) =
          if b then (y : ℝ) else 1 - (y : ℝ) := by
    filter_upwards [hX.condDistrib_ae_eq_bernoulli i] with y hy
    -- Proof comment: after identifying the conditional law as Bernoulli, singleton masses are an
    -- explicit two-point computation.
    rw [hy]
    simpa [boolBernoulliProbabilityMeasure] using
      boolBernoulliProbabilityMeasure_real_singleton y b
  have hbernoulli :
      (fun ω ↦ (condDistrib (X i) Z μ (Z ω)).real ({b} : Set Bool)) =ᵐ[μ]
        fun ω ↦ if b then (Z ω : ℝ) else 1 - (Z ω : ℝ) := by
    -- Proof comment: pull the Bernoulli singleton-mass formula back along the parameter map `Z`.
    exact MeasureTheory.ae_of_ae_map hX.measurable.aemeasurable hbernoulli_map
  exact hcond.trans hbernoulli

/-- Helper for Exercise 17.3.1: conditioned on the Bernoulli parameter `Z`, the probability that
the first `n` draws are all black is `(Z ω)^n`. -/
private theorem allBlackPrefixCondProb_eq_pow_ae
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → Bool} {Z : Ω → unitInterval}
    (hX : IsConditionallyBernoulliIID Z X μ) (n : ℕ) :
    μ⟦weightedUrnPrefixEvent X (fun _ : Fin n ↦ true)
        | MeasurableSpace.comap Z inferInstance⟧ =ᵐ[μ]
      fun ω ↦ (Z ω : ℝ) ^ n := by
  let hIID : IsConditionallyIID (MeasurableSpace.comap Z inferInstance) X μ :=
    hX.isConditionallyIID
  have hfactor :
      μ⟦weightedUrnPrefixEvent X (fun _ : Fin n ↦ true)
          | MeasurableSpace.comap Z inferInstance⟧ =ᵐ[μ]
        ∏ i ∈ Finset.range n,
          μ⟦X i ⁻¹' ({true} : Set Bool) | MeasurableSpace.comap Z inferInstance⟧ := by
    -- Proof comment: conditional independence factors the all-black prefix event into the
    -- product of the coordinate conditional probabilities.
    have hset :
        weightedUrnPrefixEvent X (fun _ : Fin n ↦ true) =
          ⋂ i ∈ Finset.range n, X i ⁻¹' ({true} : Set Bool) := by
      ext ω
      simp only [weightedUrnPrefixEvent, Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range,
        Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hω i hi
        exact hω ⟨i, hi⟩
      · intro hω i
        exact hω i i.is_lt
    rw [hset]
    simpa using
      hIID.1.2.2.2 (Finset.range n)
        (fun i _ ↦ ⟨({true} : Set Bool), measurableSet_singleton true, rfl⟩)
  have hcoords :
      ∀ᵐ ω ∂μ, ∀ i : ℕ,
        (μ⟦X i ⁻¹' ({true} : Set Bool) | MeasurableSpace.comap Z inferInstance⟧) ω =
          (Z ω : ℝ) := by
    exact ae_all_iff.2 fun i ↦ by
      simpa using condProbBoolSingleton_eq_bernoulliMass_ae hX i true
  have hprod :
      (∏ i ∈ Finset.range n,
          μ⟦X i ⁻¹' ({true} : Set Bool) | MeasurableSpace.comap Z inferInstance⟧) =ᵐ[μ]
        fun ω ↦ (Z ω : ℝ) ^ n := by
    filter_upwards [hcoords] with ω hω
    -- Proof comment: once every factor equals `Z ω`, the finite product is the `n`th power.
    simp [hω]
  exact hfactor.trans hprod

/-- Helper for Exercise 17.3.1: the `n`th moment of the Bernoulli directing parameter equals the
probability that the first `n` draws are all black. -/
private theorem bernoulliParameterMoment_eq_allBlackPrefixProb
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → Bool} {Z : Ω → unitInterval}
    (hX : IsConditionallyBernoulliIID Z X μ) (n : ℕ) :
    μ[fun ω ↦ (Z ω : ℝ) ^ n] =
      (μ (weightedUrnPrefixEvent X (fun _ : Fin n ↦ true))).toReal := by
  let A : Set Ω := weightedUrnPrefixEvent X (fun _ : Fin n ↦ true)
  have hA : MeasurableSet A :=
    measurableSet_weightedUrnPrefixEvent hX.isConditionallyIID.1.1 (fun _ : Fin n ↦ true)
  calc
    μ[fun ω ↦ (Z ω : ℝ) ^ n] =
        ∫ ω, (μ⟦A | MeasurableSpace.comap Z inferInstance⟧) ω ∂μ := by
      -- Proof comment: replace the moment integrand by the conditional probability of the
      -- all-black prefix event.
      refine integral_congr_ae ?_
      simpa [A] using (allBlackPrefixCondProb_eq_pow_ae hX n).symm
    _ = μ.real A := by
      -- Proof comment: integrating the conditional probability recovers the original event
      -- probability.
      simpa [A] using MeasureTheory.integral_condExp_indicator hX.measurable hA
    _ = (μ A).toReal := by
      rw [Measure.real_def]

/-- Helper for Exercise 17.3.1: the balanced urn one-step black ratio is the same real number as
the corresponding Beta-moment factor. -/
private theorem balancedBlackRatio_real_eq_betaFactor
    {R S s k : ℕ} (hs : 0 < s) :
    (((S + s * k : ℕ) : ℝ) / ((R + S + s * k : ℕ) : ℝ)) =
      (((S : ℝ) / (s : ℝ)) + k) /
        (((S : ℝ) / (s : ℝ)) + ((R : ℝ) / (s : ℝ)) + k) := by
  have hs_ne : (s : ℝ) ≠ 0 := by
    positivity
  -- Proof comment: clear the positive reinforcement denominator once and normalize both sides to
  -- the same polynomial identity in `R`, `S`, `s`, and `k`.
  field_simp [hs_ne]
  norm_num [Nat.cast_add, Nat.cast_mul]
  ring

/-- Helper for Exercise 17.3.1: the all-black prefix probabilities satisfy the Beta-moment product
formula determined by the balanced urn parameters. -/
private theorem allBlackPrefixProb_eq_betaMomentProduct
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → Bool}
    {R S r s : ℕ} (hX : IsGeneralizedPolyaUrn μ R S r s X) (hrs : r = s)
    (hR : 0 < R) (hS : 0 < S) (hs : 0 < s) :
    ∀ n : ℕ,
      (μ (weightedUrnPrefixEvent X (fun _ : Fin n ↦ true))).toReal =
        Finset.prod (Finset.range n) fun k ↦
          (((S : ℝ) / (s : ℝ)) + k) /
            (((S : ℝ) / (s : ℝ)) + ((R : ℝ) / (s : ℝ)) + k) := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: the empty all-black prefix is the whole space, and the empty Beta product
      -- is `1`.
      simp [weightedUrnPrefixEvent]
  | succ n ih =>
      have hRS : 0 < R + S := by
        omega
      have hcount :
          blackPrefixCount (fun _ : Fin (n + 1) ↦ true) = n + 1 := by
        -- Proof comment: every coordinate of the all-`true` word contributes one black count.
        rw [blackPrefixCount_eq_sum_indicator]
        simp
      have hmass :
          μ (weightedUrnPrefixEvent X (fun _ : Fin (n + 1) ↦ true)) =
            IsGeneralizedPolyaUrn.balancedPrefixMass R S s (n + 1) (n + 1) := by
        -- Proof comment: specialize the balanced prefix-mass formula to the all-black word.
        simpa [hcount] using
          (hX.balancedPrefixEventProb_eq_mass hrs hRS (fun _ : Fin (n + 1) ↦ true))
      have hden_ne : ((R + S + s * n : ℕ) : NNReal) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (by omega : 0 < R + S + s * n))
      have hstepReal :
          (IsGeneralizedPolyaUrn.balancedPrefixMass R S s (n + 1) (n + 1)).toReal =
            ((((S + s * n : ℕ) : ℝ) / ((R + S + s * n : ℕ) : ℝ)) *
              (IsGeneralizedPolyaUrn.balancedPrefixMass R S s n n).toReal) := by
        -- Proof comment: push the balanced successor recursion through `ENNReal.toReal` in one
        -- step, keeping the coefficient on the cheap `ℝ` side.
        simpa [ENNReal.toReal_mul, NNReal.coe_div, hden_ne] using
          congrArg ENNReal.toReal
            (IsGeneralizedPolyaUrn.balancedPrefixMass_step_true
              hRS (Nat.le_refl n))
      have hmass_n :
          (IsGeneralizedPolyaUrn.balancedPrefixMass R S s n n).toReal =
            ∏ k ∈ Finset.range n,
              (((S : ℝ) / (s : ℝ)) + k) /
                (((S : ℝ) / (s : ℝ)) + ((R : ℝ) / (s : ℝ)) + k) := by
        have hcount_n :
            blackPrefixCount (fun _ : Fin n ↦ true) = n := by
          rw [blackPrefixCount_eq_sum_indicator]
          simp
        have hmass_n' :
            μ (weightedUrnPrefixEvent X (fun _ : Fin n ↦ true)) =
              IsGeneralizedPolyaUrn.balancedPrefixMass R S s n n := by
          simpa [hcount_n] using
            (hX.balancedPrefixEventProb_eq_mass hrs hRS (fun _ : Fin n ↦ true))
        calc
          (IsGeneralizedPolyaUrn.balancedPrefixMass R S s n n).toReal =
              (μ (weightedUrnPrefixEvent X (fun _ : Fin n ↦ true))).toReal := by
                rw [hmass_n']
          _ = _ := ih
      calc
        (μ (weightedUrnPrefixEvent X (fun _ : Fin (n + 1) ↦ true))).toReal
            = (IsGeneralizedPolyaUrn.balancedPrefixMass R S s (n + 1) (n + 1)).toReal := by
                rw [hmass]
        _ =
            ((((S + s * n : ℕ) : ℝ) / ((R + S + s * n : ℕ) : ℝ)) *
                (IsGeneralizedPolyaUrn.balancedPrefixMass R S s n n).toReal) := hstepReal
        _ =
            ((((S : ℝ) / (s : ℝ)) + n) /
                (((S : ℝ) / (s : ℝ)) + ((R : ℝ) / (s : ℝ)) + n)) *
              (∏ k ∈ Finset.range n,
                (((S : ℝ) / (s : ℝ)) + k) /
                  (((S : ℝ) / (s : ℝ)) + ((R : ℝ) / (s : ℝ)) + k)) := by
                    rw [balancedBlackRatio_real_eq_betaFactor hs,
                      hmass_n]
        _ =
            Finset.prod (Finset.range (n + 1)) fun k ↦
              (((S : ℝ) / (s : ℝ)) + k) /
                (((S : ℝ) / (s : ℝ)) + ((R : ℝ) / (s : ℝ)) + k) := by
                  rw [Finset.prod_range_succ]
                  ring

/-- Helper for Exercise 17.3.1: every Beta law is almost surely supported on `[0, 1]`. -/
private theorem ae_mem_Icc_betaMeasure
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∀ᵐ x ∂betaMeasure a b, 0 ≤ x ∧ x ≤ 1 := by
  rw [betaMeasure, ae_withDensity_iff (by
    simpa [betaPDF] using ENNReal.measurable_ofReal.comp (measurable_betaPDFReal a b))]
  filter_upwards with x hx
  -- Proof comment: the Beta density vanishes outside `[0,1]`, so every point with nonzero
  -- density lies in that interval.
  have hx_nonneg : 0 ≤ x := by
    by_contra hx_neg
    exact hx (betaPDF_eq_zero_of_nonpos (le_of_not_ge hx_neg))
  have hx_le_one : x ≤ 1 := by
    by_contra hx_gt
    exact hx (betaPDF_eq_zero_of_one_le (le_of_lt (not_le.mp hx_gt)))
  exact ⟨hx_nonneg, hx_le_one⟩

/-- Helper for Exercise 17.3.1: every absolute power is integrable under the Beta law with
positive real parameters. -/
private theorem integrableAbsPow_id_betaMeasure
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) (betaMeasure a b)
  | n => by
      letI : IsProbabilityMeasure (betaMeasure a b) := isProbabilityMeasureBeta ha hb
      refine Integrable.of_bound
        ((by fun_prop : Measurable fun x : ℝ ↦ |x| ^ n).aestronglyMeasurable) 1 ?_
      filter_upwards [ae_mem_Icc_betaMeasure ha hb] with x hx
      have hx_abs_le : |x| ≤ 1 := by
        simpa [abs_of_nonneg hx.1] using hx.2
      have hx_pow_le : |x| ^ n ≤ 1 := by
        simpa using pow_le_pow_left₀ (abs_nonneg x) hx_abs_le n
      -- Proof comment: on the almost-sure support `[0,1]`, every absolute natural power is
      -- bounded by `1`.
      simpa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg x) n)] using hx_pow_le

/-- Helper for Exercise 17.3.1: under balanced reinforcement, the directing parameter of the
generalized Pólya urn has Beta law with the parameters determined by the initial counts and
constant reinforcement. -/
private theorem hasLaw_beta_of_conditionallyBernoulliParameter
    {μ : Measure Ω} [IsProbabilityMeasure μ] [StandardBorelSpace Ω]
    {X : ℕ → Ω → Bool} {Z : Ω → unitInterval}
    {R S r s : ℕ} (hX : IsGeneralizedPolyaUrn μ R S r s X)
    (hZ : IsConditionallyBernoulliIID Z X μ)
    (hrs : r = s)
    (hR : 0 < R) (hS : 0 < S) (hs : 0 < s) :
    HasLaw (fun ω ↦ (Z ω : ℝ))
      (betaMeasure ((S : ℝ) / (s : ℝ)) ((R : ℝ) / (s : ℝ))) μ := by
  let a : ℝ := (S : ℝ) / (s : ℝ)
  let b : ℝ := (R : ℝ) / (s : ℝ)
  have ha : 0 < a := by
    -- Proof comment: the first Beta parameter is the positive initial black mass divided by the
    -- positive reinforcement size.
    positivity
  have hb : 0 < b := by
    -- Proof comment: the second Beta parameter is the positive initial red mass divided by the
    -- positive reinforcement size.
    positivity
  have hBounded : Bornology.IsBounded (Set.range fun ω ↦ (Z ω : ℝ)) :=
    isBounded_range_coe_unitInterval Z
  letI : IsProbabilityMeasure (betaMeasure a b) := isProbabilityMeasureBeta ha hb
  have hIntBeta :
      ∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) (betaMeasure a b) :=
    integrableAbsPow_id_betaMeasure ha hb
  have hMoments :
      ∀ n : ℕ, moment (fun ω ↦ (Z ω : ℝ)) n μ = moment (id : ℝ → ℝ) n (betaMeasure a b) := by
    intro n
    calc
      moment (fun ω ↦ (Z ω : ℝ)) n μ = μ[fun ω ↦ (Z ω : ℝ) ^ n] := by
        rfl
      _ = (μ (weightedUrnPrefixEvent X (fun _ : Fin n ↦ true))).toReal := by
        exact bernoulliParameterMoment_eq_allBlackPrefixProb hZ n
      _ =
          ∏ k ∈ Finset.range n,
            (a + k) / (a + b + k) := by
              simpa [a, b] using allBlackPrefixProb_eq_betaMomentProduct hX hrs hR hS hs n
      _ = moment (id : ℝ → ℝ) n (betaMeasure a b) := by
            symm
            simpa [a, b, moment] using
              (beta_moment_formula a b ha hb
                ProbabilityTheory.HasLaw.id n)
  have hIdent :
      IdentDistrib (fun ω ↦ (Z ω : ℝ)) (id : ℝ → ℝ) μ (betaMeasure a b) :=
    identDistrib_of_forall_moment_eq_of_isBounded_range
      (measurable_subtype_coe.comp hZ.measurable) measurable_id hBounded hIntBeta hMoments
  -- Proof comment: bounded-support moment determinacy upgrades the moment identities to the
  -- claimed Beta law.
  exact hIdent.symm.hasLaw ProbabilityTheory.HasLaw.id

/-- Under balanced reinforcement `r = s`, the generalized Pólya urn admits a directing
parameter `Z` with Beta law and with respect to which the draw sequence is conditionally i.i.d.
Bernoulli. -/
theorem generalizedPolyaUrn_limit_hasLaw_beta
    {μ : Measure Ω} [IsProbabilityMeasure μ] [StandardBorelSpace Ω]
    {X : ℕ → Ω → Bool}
    {R S r s : ℕ} (hX : IsGeneralizedPolyaUrn μ R S r s X)
    (hrs : r = s) (hR : 0 < R) (hS : 0 < S) (hs : 0 < s) :
    ∃ Z : Ω → unitInterval,
      IsConditionallyBernoulliIID Z X μ ∧
        HasLaw (fun ω ↦ (Z ω : ℝ))
          (betaMeasure ((S : ℝ) / (s : ℝ)) ((R : ℝ) / (s : ℝ))) μ := by
  -- Proof comment: once the Bernoulli directing parameter exists, the Beta-law theorem applies
  -- directly to that same parameter.
  rcases hX.exists_conditionalBernoulliParameter hrs with ⟨Z, hZ⟩
  exact ⟨Z, hZ, hasLaw_beta_of_conditionallyBernoulliParameter hX hZ hrs hR hS hs⟩

/-- Helper for Exercise 17.3.1: the black-indicator test function on `Bool` as a bounded
continuous function. -/
private noncomputable def blackIndicatorBCF : Bool →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    { toFun := fun b : Bool ↦ if b then (1 : ℝ) else 0
      continuous_toFun := by fun_prop }

/-- Helper for Exercise 17.3.1: the black-indicator bounded continuous function is the `0/1`
indicator of the black state. -/
@[simp] private theorem blackIndicatorBCF_apply (b : Bool) :
    blackIndicatorBCF b = if b then (1 : ℝ) else 0 := rfl

/-- Helper for Exercise 17.3.1: the Bernoulli law integrates the black indicator to its
parameter. -/
private theorem integral_blackIndicator_boolBernoulliProbabilityMeasure (y : unitInterval) :
    ∫ b, blackIndicatorBCF b ∂(boolBernoulliProbabilityMeasure y : Measure Bool) = (y : ℝ) := by
  -- Proof comment: this is the standard expectation of a Bernoulli random variable on `Bool`.
  have hfun : (fun b : Bool ↦ blackIndicatorBCF b) = fun b : Bool ↦ cond b (1 : ℝ) 0 := by
    funext b
    cases b <;> rfl
  rw [hfun]
  simpa [boolBernoulliProbabilityMeasure, unitInterval.toNNReal] using
    (PMF.bernoulli_expectation (unitInterval_toNNReal_le_one y))

/-- Helper for Exercise 17.3.1: integrating the black-indicator test function against the
empirical law of the first `n + 1` draws gives the prefix black average. -/
private theorem empiricalBlackIndicatorIntegral_eq_prefixAverage
    {X : ℕ → Ω → Bool} (n : ℕ) (ω : Ω) :
    ∫ b, blackIndicatorBCF b
      ∂(empiricalDistribution (Nat.succPNat n) (fun i ↦ X i) ω : Measure Bool) =
        ((n + 1 : ℝ)⁻¹) * ∑ i ∈ Finset.range (n + 1), if X i ω then (1 : ℝ) else 0 := by
  -- Proof comment: rewrite the empirical distribution as the uniform average of the Dirac masses
  -- at the first `n + 1` samples and evaluate the indicator integral pointwise.
  rw [empiricalDistribution_toMeasure]
  rw [integral_smul_measure, integral_finset_sum_measure]
  · simp only [integral_dirac, smul_eq_mul, blackIndicatorBCF_apply]
    have hcard : (((Nat.succPNat n : ℕ+) : ℝ≥0∞)) = (n + 1 : ℝ≥0∞) := by
      norm_num [Nat.succPNat_coe, Nat.succ_eq_add_one]
    have hcoeff :
        ((((Nat.succPNat n : ℕ+) : ℝ≥0∞)⁻¹).toReal) = ((n + 1 : ℝ)⁻¹) := by
      rw [hcard, ENNReal.toReal_inv]
      rfl
    have hsum :
        ∑ i : Fin (Nat.succPNat n), (if X i ω then (1 : ℝ) else 0) =
          ∑ i ∈ Finset.range (n + 1), if X i ω then (1 : ℝ) else 0 := by
      simpa [Nat.succPNat_coe, Nat.succ_eq_add_one] using
        (Fin.sum_univ_eq_sum_range
          (fun i : ℕ ↦ if X i ω then (1 : ℝ) else 0) (n + 1))
    rw [hcoeff, hsum]
  · intro i hi
    simpa using
      (integrable_dirac (by simp) : Integrable blackIndicatorBCF (Measure.dirac (X i ω)))

/-- Helper for Exercise 17.3.1: the exchangeable average of the first-coordinate black indicator
is the empirical black average of the first `n + 1` draws. -/
private theorem exchangeableAverage_blackIndicator_comp_swap_eq_prefixAverage
    {X : ℕ → Ω → Bool} (n : ℕ) (ω : Ω) :
    exchangeableAverage (n + 1) (fun x : ℕ → Bool ↦ blackIndicatorBCF (x 0))
        (Function.swap X ω) =
      ((n + 1 : ℝ)⁻¹) * ∑ i ∈ Finset.range (n + 1), if X i ω then (1 : ℝ) else 0 := by
  let x : ℕ → ℝ := fun i ↦ blackIndicatorBCF (X i ω)
  have h_average :=
    congrArg (fun f ↦ f x)
      (exchangeableAverage_apply_zero ⟨n + 1, Nat.succ_pos n⟩)
  have h_sum :
      (∑ i : Fin (n + 1), x i) =
        ∑ i ∈ Finset.range (n + 1), if X i ω then (1 : ℝ) else 0 := by
    -- Proof comment: convert the finite `Fin` sum from the exchangeable-average formula into the
    -- standard `Finset.range` prefix sum and unfold the black indicator pointwise.
    calc
      (∑ i : Fin (n + 1), x i) = ∑ i ∈ Finset.range (n + 1), x i := by
        simpa using (Fin.sum_univ_eq_sum_range x (n + 1))
      _ = ∑ i ∈ Finset.range (n + 1), if X i ω then (1 : ℝ) else 0 := by
        simp [x, blackIndicatorBCF_apply]
  calc
    exchangeableAverage (n + 1) (fun y : ℕ → Bool ↦ blackIndicatorBCF (y 0))
        (Function.swap X ω) =
      (∑ i : Fin (n + 1), x i) / ((n + 1 : ℕ) : ℝ) := by
        -- Proof comment: apply the generic first-coordinate exchangeable-average formula to the
        -- real sequence obtained by evaluating the black indicator along the sample path.
        simpa [x, Function.swap] using h_average
    _ = (∑ i : Fin (n + 1), x i) / ((n + 1 : ℕ) : ℝ) := by
          rfl
    _ = ((n + 1 : ℝ)⁻¹) * ∑ i ∈ Finset.range (n + 1), if X i ω then (1 : ℝ) else 0 := by
          rw [h_sum, div_eq_mul_inv, mul_comm]
          norm_num

/-- Helper for Exercise 17.3.1: the real coercion of the black-prefix count matches the
`Finset.range` black-indicator sum used in the empirical-average limit. -/
private theorem blackPrefixCount_prefixReal_eq_sumRangeIndicator
    {X : ℕ → Ω → Bool} (n : ℕ) (ω : Ω) :
    ((blackPrefixCount (fun i : Fin (n + 1) ↦ X i ω) : ℕ) : ℝ) =
      Finset.sum (Finset.range (n + 1)) fun i ↦ if X i ω then (1 : ℝ) else 0 := by
  -- Proof comment: first rewrite the black count as the finite `0/1` indicator sum over
  -- `Fin (n + 1)`, then convert that sum to the standard `Finset.range` form.
  calc
    ((blackPrefixCount (fun i : Fin (n + 1) ↦ X i ω) : ℕ) : ℝ)
        = ∑ i : Fin (n + 1), ((if X i ω = true then 1 else 0 : ℕ) : ℝ) := by
            rw [blackPrefixCount_eq_sum_indicator]
            norm_num
    _ = ∑ i : Fin (n + 1), if X i ω then (1 : ℝ) else 0 := by
          simp
    _ = ∑ i ∈ Finset.range (n + 1), if X i ω then (1 : ℝ) else 0 := by
          simpa using
            (Fin.sum_univ_eq_sum_range
              (fun i : ℕ ↦ if X i ω then (1 : ℝ) else 0) (n + 1))

/-- Helper for Exercise 17.3.1: under balanced reinforcement, the black-ball fraction at time
`n + 1` is an affine function of the empirical black average of the first `n + 1` draws. -/
private theorem generalizedPolyaUrnBlackBallFraction_succ_eq_affineBlackAverage
    {R S r s : ℕ} {X : ℕ → Ω → Bool} (hrs : r = s) (n : ℕ) (ω : Ω) :
    generalizedPolyaUrnBlackBallFraction R S r s X (n + 1) ω =
      ((((s * (n + 1) : ℕ) : ℝ) / ((R + S + s * (n + 1) : ℕ) : ℝ))) *
          (((n + 1 : ℝ)⁻¹) *
            ∑ i ∈ Finset.range (n + 1), if X i ω then (1 : ℝ) else 0) +
        (S : ℝ) / ((R + S + s * (n + 1) : ℕ) : ℝ) := by
  set ℓ : ℕ := blackPrefixCount (fun i : Fin (n + 1) ↦ X i ω)
  set D : ℝ := ((R + S + s * (n + 1) : ℕ) : ℝ)
  have hℓ_le : ℓ ≤ n + 1 := by
    simpa [ℓ] using blackPrefixCount_le (fun i : Fin (n + 1) ↦ X i ω)
  have hbalancedMul :
      r * (n + 1 - ℓ) + s * ℓ = s * (n + 1) := by
    -- Proof comment: in the balanced case the red and black reinforcement contributions combine
    -- into the common balanced reinforcement factor.
    calc
      r * (n + 1 - ℓ) + s * ℓ = s * (n + 1 - ℓ) + s * ℓ := by simp [hrs]
      _ = s * (n + 1) := by
            simpa [Nat.mul_add, add_comm, add_left_comm, add_assoc] using
              congrArg (fun t : ℕ ↦ s * t) (Nat.sub_add_cancel hℓ_le)
  have hbalancedDen :
      R + S + r * (n + 1 - ℓ) + s * ℓ = R + S + s * (n + 1) := by
    calc
      R + S + r * (n + 1 - ℓ) + s * ℓ = R + S + (r * (n + 1 - ℓ) + s * ℓ) := by
        ac_rfl
      _ = R + S + s * (n + 1) := by rw [hbalancedMul]
  have hcount :
      ((ℓ : ℕ) : ℝ) =
        ∑ i ∈ Finset.range (n + 1), if X i ω then (1 : ℝ) else 0 := by
    simpa [ℓ] using blackPrefixCount_prefixReal_eq_sumRangeIndicator n ω
  by_cases hD : D = 0
  · have hD_real : ((R + S + s * (n + 1) : ℕ) : ℝ) = 0 := by
      simpa [D] using hD
    have hD_nat : R + S + s * (n + 1) = 0 := by
      exact_mod_cast hD_real
    have hR_zero : R = 0 := by
      omega
    have hS_zero : S = 0 := by
      omega
    subst hR_zero
    subst hS_zero
    have hs_mul_zero : s * (n + 1) = 0 := by
      simpa using hD_nat
    have hs_zero_real : (s : ℝ) = 0 := by
      have hs_mul_zero_real : (s : ℝ) * (n + 1) = 0 := by
        exact_mod_cast hs_mul_zero
      nlinarith [hs_mul_zero_real, (show (0 : ℝ) < n + 1 by positivity)]
    have hs_zero : s = 0 := by
      exact_mod_cast hs_zero_real
    subst hs_zero
    -- Proof comment: if the balanced denominator vanishes then all urn parameters are zero, so
    -- both sides reduce to the `0 / 0 = 0` convention in `ℝ`.
    simp [generalizedPolyaUrnBlackBallFraction, D, ℓ]
  · have hsucc_ne : (n + 1 : ℝ) ≠ 0 := by
      positivity
    calc
      generalizedPolyaUrnBlackBallFraction R S r s X (n + 1) ω =
          (((S + s * ℓ : ℕ) : ℝ) / D) := by
            -- Proof comment: first rewrite the balanced denominator to the simplified balanced
            -- form `R + S + s * (n + 1)`.
            simp [generalizedPolyaUrnBlackBallFraction, ℓ, D, hbalancedDen]
      _ =
          ((((s * (n + 1) : ℕ) : ℝ) / D) *
              (((n + 1 : ℝ)⁻¹) *
                ∑ i ∈ Finset.range (n + 1), if X i ω then (1 : ℝ) else 0)) +
            (S : ℝ) / D := by
              -- Proof comment: convert the black-count numerator to the empirical black average
              -- times the balanced reinforcement coefficient.
              rw [← hcount]
              field_simp [D, hD, hsucc_ne]
              norm_num [Nat.cast_add, Nat.cast_mul]
              ring
      _ =
          ((((s * (n + 1) : ℕ) : ℝ) / ((R + S + s * (n + 1) : ℕ) : ℝ)) *
              (((n + 1 : ℝ)⁻¹) *
                ∑ i ∈ Finset.range (n + 1), if X i ω then (1 : ℝ) else 0)) +
            (S : ℝ) / ((R + S + s * (n + 1) : ℕ) : ℝ) := by
              simp [D]

/-- Helper for Exercise 17.3.1: the coefficient of the empirical black average in the balanced
black-fraction tail is a direct quotient in the empirical black average. -/
private theorem generalizedPolyaUrnBlackBallFraction_succ_sub_empiricalBlackAverage_eq
    {R S r s : ℕ} {X : ℕ → Ω → Bool} (hrs : r = s) (hs : 0 < s) (n : ℕ) (ω : Ω) :
    generalizedPolyaUrnBlackBallFraction R S r s X (n + 1) ω -
        (((n + 1 : ℝ)⁻¹) *
          Finset.sum (Finset.range (n + 1)) (fun i ↦ if X i ω then (1 : ℝ) else 0)) =
      ((S : ℝ) -
          (((R + S : ℕ) : ℝ) *
          (((n + 1 : ℝ)⁻¹) *
              Finset.sum (Finset.range (n + 1)) (fun i ↦ if X i ω then (1 : ℝ) else 0)))) /
        (((R + S + s * (n + 1) : ℕ) : ℝ)) := by
  let avg : ℝ :=
    ((n + 1 : ℝ)⁻¹) *
      Finset.sum (Finset.range (n + 1)) (fun i ↦ if X i ω then (1 : ℝ) else 0)
  let D : ℝ := ((R + S + s * (n + 1) : ℕ) : ℝ)
  have hD_pos : 0 < D := by
    dsimp [D]
    positivity
  have hD_ne : D ≠ 0 := by
    exact ne_of_gt hD_pos
  calc
    generalizedPolyaUrnBlackBallFraction R S r s X (n + 1) ω - avg =
        ((((s * (n + 1) : ℕ) : ℝ) / D) * avg + (S : ℝ) / D) - avg := by
          -- Proof comment: first rewrite the successor-time urn fraction into its affine
          -- empirical-average form.
          simpa [avg, D] using
            generalizedPolyaUrnBlackBallFraction_succ_eq_affineBlackAverage hrs n ω
    _ = ((S : ℝ) - (((R + S : ℕ) : ℝ) * avg)) / D := by
          -- Proof comment: collecting the `avg` terms over the common positive denominator yields
          -- the explicit successor-minus-average identity.
          have hs_cast : (((s * (n + 1) : ℕ) : ℝ)) = (s : ℝ) * (n + 1) := by
            norm_num
          rw [hs_cast]
          dsimp [D]
          field_simp [D, hD_ne]
          norm_num [Nat.cast_add, Nat.cast_mul]
          ring_nf
    _ =
        ((S : ℝ) -
            (((R + S : ℕ) : ℝ) *
              (((n + 1 : ℝ)⁻¹) *
                Finset.sum (Finset.range (n + 1)) (fun i ↦ if X i ω then (1 : ℝ) else 0)))) /
          (((R + S + s * (n + 1) : ℕ) : ℝ)) := by
            simp [avg, D]

/-- Helper for Exercise 17.3.1: under balanced reinforcement, the successor-time urn fraction is a
vanishing perturbation of the empirical black average. -/
private theorem generalizedPolyaUrnBlackBallFraction_succ_error_le
    {R S r s : ℕ} {X : ℕ → Ω → Bool} (hrs : r = s) (hs : 0 < s) (n : ℕ) (ω : Ω) :
    |generalizedPolyaUrnBlackBallFraction R S r s X (n + 1) ω -
        (((n + 1 : ℝ)⁻¹) *
          Finset.sum (Finset.range (n + 1)) (fun i ↦ if X i ω then (1 : ℝ) else 0))| ≤
      ((R + S : ℕ) : ℝ) / (n + 1) := by
  let avg : ℝ :=
    ((n + 1 : ℝ)⁻¹) *
      Finset.sum (Finset.range (n + 1)) (fun i ↦ if X i ω then (1 : ℝ) else 0)
  let D : ℝ := ((R + S + s * (n + 1) : ℕ) : ℝ)
  have hD_pos : 0 < D := by
    dsimp [D]
    positivity
  have havg_nonneg : 0 ≤ avg := by
    -- Proof comment: the empirical average is a positive scalar times a sum of `0/1` terms.
    dsimp [avg]
    positivity
  have havg_le_one : avg ≤ 1 := by
    have hsum_le :
        Finset.sum (Finset.range (n + 1)) (fun i ↦ if X i ω then (1 : ℝ) else 0) ≤ n + 1 := by
      calc
        Finset.sum (Finset.range (n + 1)) (fun i ↦ if X i ω then (1 : ℝ) else 0)
            ≤ Finset.sum (Finset.range (n + 1)) (fun _ ↦ (1 : ℝ)) := by
                refine Finset.sum_le_sum ?_
                intro i hi
                by_cases hXi : X i ω <;> simp [hXi]
        _ = n + 1 := by
              simp
    -- Proof comment: the prefix sum is bounded by the number of summands, so dividing by
    -- `n + 1` gives a quantity at most `1`.
    dsimp [avg]
    have hsucc_pos : 0 < (n + 1 : ℝ) := by
      positivity
    have hscaled := mul_le_mul_of_nonneg_left hsum_le (show 0 ≤ (n + 1 : ℝ)⁻¹ by positivity)
    simpa [hsucc_pos.ne', inv_mul_cancel₀] using hscaled
  have hnum_bound :
      |(S : ℝ) - (((R + S : ℕ) : ℝ) * avg)| ≤ ((R + S : ℕ) : ℝ) := by
    have hRS_nonneg : 0 ≤ ((R + S : ℕ) : ℝ) := by
      exact_mod_cast (Nat.zero_le (R + S))
    have hS_le : (S : ℝ) ≤ ((R + S : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_add_left S R)
    have hR_le : (R : ℝ) ≤ ((R + S : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_add_right R S)
    have hS_nonneg : 0 ≤ (S : ℝ) := by
      exact_mod_cast (Nat.zero_le S)
    have hone_sub_nonneg : 0 ≤ 1 - avg := by
      linarith
    have hS_term_nonneg : 0 ≤ (S : ℝ) * (1 - avg) := by
      positivity
    apply abs_le.mpr
    constructor
    · calc
        -((R + S : ℕ) : ℝ) ≤ -(R : ℝ) := by linarith
        _ ≤ -((R : ℝ) * avg) := by nlinarith
        _ ≤ (S : ℝ) * (1 - avg) - (R : ℝ) * avg := by linarith
        _ = (S : ℝ) - (((R + S : ℕ) : ℝ) * avg) := by
              norm_num [Nat.cast_add, Nat.cast_mul]
              ring
    · have hupp : (S : ℝ) - (((R + S : ℕ) : ℝ) * avg) ≤ (S : ℝ) := by
        nlinarith [havg_nonneg, hRS_nonneg]
      linarith
  have hden_ge :
      (n + 1 : ℝ) ≤ D := by
    have hs_one : 1 ≤ s := Nat.succ_le_of_lt hs
    have hnat : n + 1 ≤ R + S + s * (n + 1) := by
      nlinarith [hs_one]
    simpa [D] using (show ((n + 1 : ℕ) : ℝ) ≤ ((R + S + s * (n + 1) : ℕ) : ℝ) by
      exact_mod_cast hnat)
  calc
    |generalizedPolyaUrnBlackBallFraction R S r s X (n + 1) ω -
        (((n + 1 : ℝ)⁻¹) *
          Finset.sum (Finset.range (n + 1)) (fun i ↦ if X i ω then (1 : ℝ) else 0))|
        =
      |((S : ℝ) - (((R + S : ℕ) : ℝ) * avg)) / D| := by
          -- Proof comment: rewrite the difference using the explicit balanced successor-minus-
          -- average identity proved just above.
          simpa [avg, D] using congrArg abs
            (generalizedPolyaUrnBlackBallFraction_succ_sub_empiricalBlackAverage_eq hrs hs n ω)
    _ = |(S : ℝ) - (((R + S : ℕ) : ℝ) * avg)| / D := by
          rw [abs_div, abs_of_pos hD_pos]
    _ ≤ ((R + S : ℕ) : ℝ) / D := by
          exact div_le_div_of_nonneg_right hnum_bound hD_pos.le
    _ ≤ ((R + S : ℕ) : ℝ) / (n + 1) := by
          have hRS_nonneg : 0 ≤ ((R + S : ℕ) : ℝ) := by
            exact_mod_cast (Nat.zero_le (R + S))
          have hsucc_pos : 0 < (n + 1 : ℝ) := by
            positivity
          exact div_le_div_of_nonneg_left hRS_nonneg hsucc_pos hden_ge

/-- Helper for Exercise 17.3.1: once the empirical black average converges, the balanced urn's
actual black-ball fraction converges to the same limit. -/
private theorem tendsto_generalizedPolyaUrnBlackBallFraction_of_empiricalBlackAverage
    {R S r s : ℕ} {X : ℕ → Ω → Bool} (hrs : r = s) (hs : 0 < s) {ω : Ω} {z : ℝ}
    (havg :
      Tendsto
        (fun n : ℕ ↦ ((n + 1 : ℝ)⁻¹) * ∑ i ∈ Finset.range (n + 1), if X i ω then (1 : ℝ) else 0)
        atTop (𝓝 z)) :
    Tendsto (fun n ↦ generalizedPolyaUrnBlackBallFraction R S r s X n ω) atTop (𝓝 z) := by
  have hbound :
      Tendsto (fun n : ℕ ↦ (((R + S : ℕ) : ℝ) / (n + 1 : ℝ))) atTop (𝓝 0) :=
    by
      convert
        (tendsto_const_div_atTop_nhds_zero_nat (((R + S : ℕ) : ℝ))).comp
          (tendsto_add_atTop_nat 1) using 1
      funext n
      norm_num
  have hdiff_abs :
      Tendsto
        (fun n : ℕ ↦
          |generalizedPolyaUrnBlackBallFraction R S r s X (n + 1) ω -
              (((n + 1 : ℝ)⁻¹) *
                ∑ i ∈ Finset.range (n + 1), if X i ω then (1 : ℝ) else 0)|)
        atTop (𝓝 0) := by
    refine squeeze_zero (fun n ↦ abs_nonneg _) ?_ hbound
    intro n
    exact generalizedPolyaUrnBlackBallFraction_succ_error_le hrs hs n ω
  have hdiff :
      Tendsto
        (fun n : ℕ ↦
          generalizedPolyaUrnBlackBallFraction R S r s X (n + 1) ω -
            (((n + 1 : ℝ)⁻¹) *
              ∑ i ∈ Finset.range (n + 1), if X i ω then (1 : ℝ) else 0))
        atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Real.norm_eq_abs] using hdiff_abs
  have hsucc :
      Tendsto (fun n ↦ generalizedPolyaUrnBlackBallFraction R S r s X (n + 1) ω) atTop (𝓝 z) := by
    have hadd := hdiff.add havg
    simpa [sub_add_cancel] using hadd
  -- Proof comment: once the successor-time subsequence has the target limit, the standard
  -- `atTop` shift equivalence removes the index offset.
  exact (tendsto_add_atTop_iff_nat 1).1 (by simpa using hsucc)

/-- Helper for Exercise 17.3.1: a `{0,1}`-valued process that is conditionally i.i.d. Bernoulli
with parameter `Z` has empirical black averages converging almost surely to `Z`. -/
private theorem empiricalBlackAverage_tendsto_ae_of_conditionallyBernoulliIID
    {μ : Measure Ω} [IsProbabilityMeasure μ] [StandardBorelSpace Ω]
    {X : ℕ → Ω → Bool} {Z : Ω → unitInterval}
    (hX : IsConditionallyBernoulliIID Z X μ) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ ↦
          ((n + 1 : ℝ)⁻¹) * ∑ i ∈ Finset.range (n + 1), if X i ω then (1 : ℝ) else 0)
        atTop (𝓝 (Z ω : ℝ)) := by
  let xiInf : Ω → ProbabilityMeasure Bool := fun ω ↦ boolBernoulliProbabilityMeasure (Z ω)
  have hxiInf_meas : Measurable xiInf :=
    measurable_boolBernoulliProbabilityMeasure.comp hX.measurable
  have hIIDxiInf : IsConditionallyIID (MeasurableSpace.comap xiInf inferInstance) X μ := by
    -- Proof comment: the Bernoulli-law-valued directing variable and its scalar parameter carry
    -- the same conditioning `σ`-algebra.
    rw [comap_boolBernoulliProbabilityMeasure_eq]
    exact hX.isConditionallyIID
  have hcondComp :
      (fun ω ↦ condDistrib (X 0) xiInf μ (xiInf ω)) =ᵐ[μ]
        fun ω ↦ condDistrib (X 0) Z μ (Z ω) := by
    have hmass (b : Bool) :
        (fun ω ↦ (condDistrib (X 0) xiInf μ (xiInf ω)).real ({b} : Set Bool)) =ᵐ[μ]
          fun ω ↦ (condDistrib (X 0) Z μ (Z ω)).real ({b} : Set Bool) := by
      have hcondXiInf :
          (fun ω ↦ (condDistrib (X 0) xiInf μ (xiInf ω)).real ({b} : Set Bool)) =ᵐ[μ]
            μ⟦X 0 ⁻¹' ({b} : Set Bool) | MeasurableSpace.comap xiInf inferInstance⟧ := by
        simpa using
          (condDistrib_ae_eq_condExp (μ := μ) (X := xiInf) (Y := X 0)
            hxiInf_meas (hX.isConditionallyIID.1.1 0) (measurableSet_singleton b))
      have hcondZ :
          μ⟦X 0 ⁻¹' ({b} : Set Bool) | MeasurableSpace.comap Z inferInstance⟧ =ᵐ[μ]
            fun ω ↦ (condDistrib (X 0) Z μ (Z ω)).real ({b} : Set Bool) := by
        simpa using
          (condDistrib_ae_eq_condExp (μ := μ) (X := Z) (Y := X 0)
            hX.measurable (hX.isConditionallyIID.1.1 0) (measurableSet_singleton b)).symm
      calc
        (fun ω ↦ (condDistrib (X 0) xiInf μ (xiInf ω)).real ({b} : Set Bool))
            =ᵐ[μ] μ⟦X 0 ⁻¹' ({b} : Set Bool) | MeasurableSpace.comap xiInf inferInstance⟧ :=
              hcondXiInf
        _ =ᵐ[μ] μ⟦X 0 ⁻¹' ({b} : Set Bool) | MeasurableSpace.comap Z inferInstance⟧ := by
              rw [comap_boolBernoulliProbabilityMeasure_eq]
        _ =ᵐ[μ] (fun ω ↦ (condDistrib (X 0) Z μ (Z ω)).real ({b} : Set Bool)) := hcondZ
    filter_upwards [hmass false, hmass true] with ω hfalse htrue
    apply (MeasureTheory.ext_iff_measureReal_singleton
      (μ1 := condDistrib (X 0) xiInf μ (xiInf ω))
      (μ2 := condDistrib (X 0) Z μ (Z ω))).2
    intro b
    cases b
    · simpa using hfalse
    · simpa using htrue
  have hbernoulliComp :
      (fun ω ↦ condDistrib (X 0) xiInf μ (xiInf ω)) =ᵐ[μ]
        fun ω ↦ (xiInf ω : Measure Bool) := by
    have hbernoulli :
        (fun ω ↦ condDistrib (X 0) Z μ (Z ω)) =ᵐ[μ]
          fun ω ↦ (boolBernoulliProbabilityMeasure (Z ω) : Measure Bool) := by
      have hmap :
          ∀ᵐ y ∂μ.map Z,
            condDistrib (X 0) Z μ y =
              (boolBernoulliProbabilityMeasure y : Measure Bool) := by
        simpa [boolBernoulliProbabilityMeasure] using hX.condDistrib_ae_eq_bernoulli 0
      exact MeasureTheory.ae_of_ae_map hX.measurable.aemeasurable hmap
    simpa [xiInf] using hcondComp.trans hbernoulli
  have hmapMass (b : Bool) :
      ∀ᵐ ξ ∂μ.map xiInf,
        (condDistrib (X 0) xiInf μ ξ).real ({b} : Set Bool) = (ξ : Measure Bool).real ({b} : Set Bool) := by
    have hcompMass :
        (fun ω ↦ (condDistrib (X 0) xiInf μ (xiInf ω)).real ({b} : Set Bool)) =ᵐ[μ]
          fun ω ↦ (xiInf ω : Measure Bool).real ({b} : Set Bool) := by
      filter_upwards [hbernoulliComp] with ω hω
      simpa [hω]
    have hEqSet :
        MeasurableSet
          {ξ |
            (condDistrib (X 0) xiInf μ ξ).real ({b} : Set Bool) =
              (ξ : Measure Bool).real ({b} : Set Bool)} :=
      measurableSet_eq_fun
        ((Kernel.measurable_coe _ (measurableSet_singleton b)).ennreal_toReal)
        ((((Measure.measurable_coe (measurableSet_singleton b)).ennreal_toReal).comp
          measurable_subtype_coe))
    exact (ae_map_iff hxiInf_meas.aemeasurable hEqSet).2 (by simpa [xiInf] using hcompMass)
  have hxiInf : IsDirectingProbabilityMeasure xiInf X μ := by
    refine ⟨hIIDxiInf, ?_⟩
    filter_upwards [hmapMass false, hmapMass true] with ξ hfalse htrue
    apply (MeasureTheory.ext_iff_measureReal_singleton
      (μ1 := condDistrib (X 0) xiInf μ ξ)
      (μ2 := (ξ : Measure Bool))).2
    intro b
    cases b
    · simpa using hfalse
    · simpa using htrue
  have hlimit :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n ↦ ∫ b, blackIndicatorBCF b
            ∂(empiricalDistribution (Nat.succPNat n) (fun i ↦ X i) ω : Measure Bool))
          atTop
          (𝓝 (∫ b, blackIndicatorBCF b ∂(xiInf ω : Measure Bool))) := by
    simpa [xiInf] using deFinetti_empiricalDistribution_testFunction_tendsto_ae
      (X := X) (xiInf := xiInf) hxiInf blackIndicatorBCF
  filter_upwards [hlimit] with ω hω
  have hxiInfIntegral :
      ∫ b, blackIndicatorBCF b ∂(xiInf ω : Measure Bool) = (Z ω : ℝ) := by
    -- Proof comment: the directing law is Bernoulli with parameter `Z ω`, so the black-indicator
    -- integral is exactly that parameter.
    simpa [xiInf] using integral_blackIndicator_boolBernoulliProbabilityMeasure (Z ω)
  have hxiInfIntegral' :
      ∫ b, (if b then (1 : ℝ) else 0) ∂(xiInf ω : Measure Bool) = (Z ω : ℝ) := by
    simpa [blackIndicatorBCF_apply] using hxiInfIntegral
  have hAverage :
      Tendsto
        (fun n : ℕ ↦
          ((n + 1 : ℝ)⁻¹) * ∑ i ∈ Finset.range (n + 1), if X i ω then (1 : ℝ) else 0)
        atTop (𝓝 (∫ b, blackIndicatorBCF b ∂(xiInf ω : Measure Bool))) := by
    have hω' := hω
    rw [show
        (fun n ↦ ∫ b, blackIndicatorBCF b
          ∂(empiricalDistribution (Nat.succPNat n) (fun i ↦ X i) ω : Measure Bool)) =
          (fun n : ℕ ↦
            ((n + 1 : ℝ)⁻¹) *
              ∑ i ∈ Finset.range (n + 1), if X i ω then (1 : ℝ) else 0) by
          funext n
          exact empiricalBlackIndicatorIntegral_eq_prefixAverage n ω] at hω'
    exact hω'
  simpa [hxiInfIntegral'] using hAverage

/-- Exercise 17.3.1: for a generalized Pólya urn with constant reinforcements `r_k = r` and
`s_k = s` under balanced reinforcement `r = s`, initial red and black counts `R`,`S`, and draw
process `X`, the black-ball fraction has a random limit `Z`; conditionally on `Z` the draw
sequence is i.i.d. Bernoulli with parameter `Z`, and `Z` has the Beta law with parameters
`S / s` and `R / s`. -/
theorem generalizedPolyaUrn_blackBallFraction_ae_tendsto_limit_of_eq
    {μ : Measure Ω} [IsProbabilityMeasure μ] [StandardBorelSpace Ω]
    {X : ℕ → Ω → Bool}
    {R S r s : ℕ} (hX : IsGeneralizedPolyaUrn μ R S r s X)
    (hrs : r = s) (hR : 0 < R) (hS : 0 < S) (hs : 0 < s) :
    ∃ Z : Ω → unitInterval,
      IsConditionallyBernoulliIID Z X μ ∧
        HasLaw (fun ω ↦ (Z ω : ℝ))
          (betaMeasure ((S : ℝ) / (s : ℝ)) ((R : ℝ) / (s : ℝ))) μ ∧
        ∀ᵐ ω ∂μ,
          Tendsto (fun n ↦ generalizedPolyaUrnBlackBallFraction R S r s X n ω) atTop
            (𝓝 (Z ω : ℝ)) := by
  -- Proof comment: first produce the Bernoulli directing parameter and its Beta law, then pass
  -- from the empirical black averages to the actual urn fractions via the deterministic error
  -- estimate proved above.
  rcases generalizedPolyaUrn_limit_hasLaw_beta hX hrs hR hS hs with ⟨Z, hZ, hLaw⟩
  have hEmpirical : ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ ↦
          ((n + 1 : ℝ)⁻¹) * ∑ i ∈ Finset.range (n + 1), if X i ω then (1 : ℝ) else 0)
        atTop (𝓝 (Z ω : ℝ)) :=
    empiricalBlackAverage_tendsto_ae_of_conditionallyBernoulliIID hZ
  have hFraction :
      ∀ᵐ ω ∂μ,
        Tendsto (fun n ↦ generalizedPolyaUrnBlackBallFraction R S r s X n ω) atTop
          (𝓝 (Z ω : ℝ)) := by
    filter_upwards [hEmpirical] with ω hω
    exact tendsto_generalizedPolyaUrnBlackBallFraction_of_empiricalBlackAverage hrs hs hω
  exact ⟨Z, hZ, hLaw, hFraction⟩

/-- At time `0`, the black-ball fraction is the initial proportion `S / (R + S)`. -/
@[simp] theorem generalizedPolyaUrnBlackBallFraction_zero
    {Ω' : Type u} [MeasurableSpace Ω']
    (R S r s : ℕ) (X : ℕ → Ω' → Bool) (ω : Ω') :
    generalizedPolyaUrnBlackBallFraction R S r s X 0 ω =
      (S : ℝ) / ((R + S : ℕ) : ℝ) := by
  -- Proof comment: at time `0`, the initial prefix is empty, so the black draw count is `0` and
  -- the urn contains exactly the initial `S` black and `R` red balls.
  simp [generalizedPolyaUrnBlackBallFraction, blackPrefixCount]

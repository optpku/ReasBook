/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Remark_23_2

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Theorem 23.1: the Boolean sign map `true ↦ 1`, `false ↦ -1` is measurable. -/
private theorem measurable_boolSign :
    Measurable (fun b : Bool ↦ if b then (1 : ℝ) else -1) :=
  measurable_of_countable _

/-- The Rademacher Cramér rate function from Theorem 23.1: it is the Bernoulli Cramér rate on
`[-1, 1]` and `∞` outside that interval. -/
def rademacherCramerRateFunction (x : ℝ) : EReal :=
  if |x| ≤ 1 then (bernoulliCramerRateFunction x : EReal) else ⊤

-- Proof sketch: under `|x| ≤ 1`, the defining `if` takes the finite Bernoulli branch from
-- `Remark 23.2`.
/-- On `[-1, 1]`, the Rademacher Cramér rate function agrees with the Bernoulli Cramér branch from
`Remark 23.2`. -/
theorem rademacherCramerRateFunction_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) :
    rademacherCramerRateFunction x = bernoulliCramerRateFunction x := by
  simp [rademacherCramerRateFunction, hx]

-- Proof sketch: combine `rademacherCramerRateFunction_of_abs_le_one` with the defining equation of
-- `bernoulliCramerRateFunction` and rewrite the division by `2` into the textbook entropy
-- expression on `[-1,1]`.
/-- On `[-1, 1]`, the rate in Theorem 23.1 is given by the explicit entropy formula from
`Remark 23.2`. -/
theorem rademacher_largeDeviationRate_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) :
    rademacherCramerRateFunction x =
      ((1 + x) / 2) * Real.log (1 + x) + ((1 - x) / 2) * Real.log (1 - x) := by
  -- Proof comment: first replace the `EReal`-valued rate by the Bernoulli branch, then rewrite
  -- the factor `1 / 2` into the textbook affine weights.
  rw [rademacherCramerRateFunction_of_abs_le_one hx, bernoulliCramerRateFunction]
  have hReal :
      ((1 + x) * Real.log (1 + x) + (1 - x) * Real.log (1 - x)) / 2 =
        ((1 + x) / 2) * Real.log (1 + x) + ((1 - x) / 2) * Real.log (1 - x) := by
    ring
  change
    ((((1 + x) * Real.log (1 + x) + (1 - x) * Real.log (1 - x)) / 2 : ℝ) : EReal) =
      ((((1 + x) / 2) * Real.log (1 + x) + ((1 - x) / 2) * Real.log (1 - x) : ℝ) : EReal)
  exact_mod_cast hReal

/-- Helper for Theorem 23.1: the symmetric two-point law on `ℝ` concentrated on `{-1, 1}`. -/
private abbrev rademacherTwoPointLaw : Measure ℝ :=
  Measure.map (fun b : Bool ↦ if b then (1 : ℝ) else -1)
    ((PMF.uniformOfFintype Bool).toMeasure)

/-- Helper for Theorem 23.1: the symmetric two-point law on `ℝ` is a probability measure. -/
private theorem rademacherTwoPointLaw_isProbabilityMeasure :
    IsProbabilityMeasure rademacherTwoPointLaw := by
  -- Proof comment: pushforward preserves the probability-mass normalization of the uniform Bool
  -- law.
  exact Measure.isProbabilityMeasure_map measurable_boolSign.aemeasurable

private instance : IsProbabilityMeasure rademacherTwoPointLaw :=
  rademacherTwoPointLaw_isProbabilityMeasure

variable {P : Measure Ω} {X : ℕ → Ω → ℝ}

/-- Helper for Theorem 23.1: every coordinate of the i.i.d. family has the same symmetric
two-point law as `X 0`. -/
private theorem rademacherCoordinate_hasLaw
    (hX_iid : IsIID X P)
    (hX0_law : HasLaw (X 0) rademacherTwoPointLaw P)
    (n : ℕ) :
    HasLaw (X n) rademacherTwoPointLaw P := by
  -- Proof comment: identical distribution transports the reference law of `X 0` to the `n`-th
  -- coordinate without changing the ambient measure.
  exact (hX_iid.identDistrib 0 n).hasLaw hX0_law

/-- Helper for Theorem 23.1: the first `n` Rademacher coordinates have the `n`-fold product law
of the symmetric two-point measure on `ℝ`. -/
private theorem rademacherPrefix_hasLawPi
    (hX_iid : IsIID X P)
    (hX0_law : HasLaw (X 0) rademacherTwoPointLaw P)
    (n : ℕ) :
    HasLaw (fun ω : Ω ↦ fun i : Fin n ↦ X i.1 ω)
      (Measure.pi fun _ : Fin n ↦ rademacherTwoPointLaw) P := by
  letI : IsProbabilityMeasure P := hX0_law.isProbabilityMeasure
  have hPrefixIndep : iIndepFun (fun i : Fin n ↦ X i.1) P := by
    -- Proof comment: independence of the full family restricts along the coordinate embedding
    -- `Fin n ↪ ℕ`.
    simpa using hX_iid.iIndepFun.precomp Fin.val_injective
  have hPrefixLaw : ∀ i : Fin n, HasLaw (fun ω ↦ X i.1 ω) rademacherTwoPointLaw P := by
    -- Proof comment: each finite-prefix coordinate inherits the common Rademacher law.
    intro i
    simpa using rademacherCoordinate_hasLaw (P := P) (X := X) hX_iid hX0_law i.1
  refine ⟨aemeasurable_pi_lambda _ fun i ↦ (hPrefixLaw i).aemeasurable, ?_⟩
  -- Proof comment: for finite independent families, the joint pushforward is exactly the product
  -- of the one-coordinate pushforwards.
  rw [(iIndepFun_iff_map_fun_eq_pi_map fun i ↦ (hPrefixLaw i).aemeasurable).1 hPrefixIndep]
  congr 1
  funext i
  exact (hPrefixLaw i).map_eq

/-- Helper for Theorem 23.1: each Rademacher coordinate is almost surely supported on `{-1, 1}`.
-/
private theorem rademacherCoordinate_ae_eq_pm_one
    (hX_iid : IsIID X P)
    (hX0_law : HasLaw (X 0) rademacherTwoPointLaw P)
    (n : ℕ) :
    ∀ᵐ ω ∂P, X n ω = -1 ∨ X n ω = 1 := by
  have hLaw := rademacherCoordinate_hasLaw (P := P) (X := X) hX_iid hX0_law n
  have hSupport :
      {ω | ¬(X n ω = -1 ∨ X n ω = 1)} =
        X n ⁻¹' (({(-1 : ℝ), (1 : ℝ)} : Set ℝ)ᶜ) := by
    -- Proof comment: rewrite the support event as the preimage of the complement of the two-point
    -- set in the codomain.
    ext ω
    by_cases hneg : X n ω = -1
    · by_cases hpos : X n ω = 1
      · simp [hneg, Set.mem_insert_iff, Set.mem_singleton_iff]
      · simp [hneg, Set.mem_insert_iff, Set.mem_singleton_iff]
    · by_cases hpos : X n ω = 1
      · simp [hpos, Set.mem_insert_iff, Set.mem_singleton_iff]
      · simp [hneg, hpos, Set.mem_insert_iff, Set.mem_singleton_iff]
  -- Proof comment: transport the support statement of the two-point law back along the `n`-th
  -- coordinate map.
  rw [ae_iff]
  rw [hSupport]
  rw [← Measure.map_apply_of_aemeasurable hLaw.aemeasurable]
  · rw [hLaw.map_eq]
    rw [Measure.map_apply measurable_boolSign]
    · simp [Set.mem_insert_iff, Set.mem_singleton_iff]
    · simp
  · simp

/-- Helper for Theorem 23.1: once `k` is on the upper half of the Pascal row, the next binomial
coefficient is no larger. -/
private theorem chooseSucc_le_of_half_le {n k : ℕ} (hhalf : n ≤ 2 * k) :
    Nat.choose n (k + 1) ≤ Nat.choose n k := by
  -- Proof comment: reflect the row around its midpoint and apply the standard monotonicity of
  -- `Nat.choose` on the increasing half.
  by_cases hkn : n < k + 1
  · rw [Nat.choose_eq_zero_of_lt hkn]
    exact Nat.zero_le _
  · have hk1 : k + 1 ≤ n := Nat.not_lt.mp hkn
    have hk : k ≤ n := Nat.le_trans (Nat.le_succ k) hk1
    have hleft : n - (k + 1) < n / 2 := by
      omega
    have hmono :
        Nat.choose n (n - (k + 1)) ≤ Nat.choose n (n - (k + 1) + 1) := by
      exact Nat.choose_le_succ_of_lt_half_left hleft
    have hstep : Nat.choose n (n - (k + 1)) ≤ Nat.choose n (n - k) := by
      simpa [show n - (k + 1) + 1 = n - k by omega] using hmono
    rw [Nat.choose_symm hk1, Nat.choose_symm hk] at hstep
    exact hstep

/-- Helper for Theorem 23.1: the symmetric two-point law on `ℝ` is the pushforward of the uniform
Boolean law under the sign map `true ↦ 1`, `false ↦ -1`. -/
private theorem rademacherTwoPointLaw_eq_uniformBoolMap :
    rademacherTwoPointLaw =
    Measure.map (fun b : Bool ↦ if b then (1 : ℝ) else -1)
        ((PMF.uniformOfFintype Bool).toMeasure) := by
  -- Proof comment: the helper law was defined as this Bool pushforward.
  rfl

/-- Helper for Theorem 23.1: the `n`-fold Rademacher product law is the pushforward of the
uniform Boolean cube under the coordinatewise sign map. -/
private theorem rademacherPrefix_eq_uniformBoolCube (n : ℕ) :
    Measure.pi (fun _ : Fin n ↦ rademacherTwoPointLaw) =
      Measure.map (fun b : Fin n → Bool ↦ fun i : Fin n ↦ if b i then (1 : ℝ) else -1)
        (Measure.pi fun _ : Fin n ↦ ((PMF.uniformOfFintype Bool).toMeasure)) := by
  -- Proof comment: each coordinate marginal is already the Bool-sign pushforward, so the whole
  -- product is the coordinatewise pushforward of the uniform Boolean cube.
  simpa [rademacherTwoPointLaw] using
    (Measure.pi_map_pi
      (μ := fun _ : Fin n ↦ ((PMF.uniformOfFintype Bool).toMeasure))
      (f := fun _ : Fin n ↦ fun b : Bool ↦ if b then (1 : ℝ) else -1)
      (fun _ : Fin n ↦ measurable_boolSign.aemeasurable)).symm

/-- Helper for Theorem 23.1: the Boolean-cube product measure is the uniform measure on
`Fin n → Bool`. -/
private theorem uniformBoolCube_eq_uniformMeasure (n : ℕ) :
    Measure.pi (fun _ : Fin n ↦ ((PMF.uniformOfFintype Bool).toMeasure)) =
      (PMF.uniformOfFintype (Fin n → Bool)).toMeasure := by
  -- Proof comment: both finite measures assign the same mass `2^{-n}` to every singleton Boolean
  -- word.
  refine Measure.ext_of_singleton ?_
  intro b
  rw [Measure.pi_singleton]
  simp [PMF.uniformOfFintype_apply, ENNReal.inv_pow]

/-- Helper for Theorem 23.1: the `true` coordinates of a Boolean word. -/
private def trueCoordinates {n : ℕ} (b : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ b i

/-- Helper for Theorem 23.1: the characteristic word of a finite subset recovers that subset as
its `true` coordinates. -/
private theorem trueCoordinates_characteristic {n : ℕ} (s : Finset (Fin n)) :
    trueCoordinates (fun i ↦ decide (i ∈ s)) = s := by
  -- Proof comment: a coordinate is marked `true` exactly when it belongs to the chosen subset.
  ext i
  simp [trueCoordinates]

/-- Helper for Theorem 23.1: Boolean words with exactly `k` true coordinates are counted by
`Nat.choose n k`. -/
private theorem card_boolWords_trueCount_eq_choose (n k : ℕ) :
    Fintype.card {b : Fin n → Bool // (trueCoordinates b).card = k} = Nat.choose n k := by
  classical
  -- Proof comment: identify a Boolean word with the finite subset of its `true` coordinates.
  calc
    Fintype.card {b : Fin n → Bool // (trueCoordinates b).card = k}
        = Fintype.card {s : Finset (Fin n) // s.card = k} := by
            refine Fintype.card_congr ?_
            refine
              { toFun := fun b ↦ ⟨trueCoordinates b.1, b.2⟩
                invFun := fun s ↦ ⟨fun i ↦ decide (i ∈ s.1), ?_⟩
                left_inv := ?_
                right_inv := ?_ }
            · simpa [trueCoordinates_characteristic] using s.2
            · intro b
              apply Subtype.ext
              funext i
              by_cases hbi : b.1 i
              · simp [trueCoordinates, hbi]
              · simp [trueCoordinates, hbi]
            · intro s
              apply Subtype.ext
              exact trueCoordinates_characteristic s.1
    _ = Nat.choose n k := by
          simpa using (Fintype.card_finset_len (α := Fin n) k)

/-- Helper for Theorem 23.1: the Boolean sign sum equals `2 * (# true coordinates) - n`. -/
private theorem boolSignSum_eq_two_mul_card_trueCoordinates_sub {n : ℕ} (b : Fin n → Bool) :
    (∑ i : Fin n, (if b i then (1 : ℝ) else -1)) = 2 * (trueCoordinates b).card - n := by
  -- Proof comment: rewrite each sign as `(if b i then 2 else 0) - 1`, then sum the indicator part
  -- over the `true` coordinates.
  calc
    (∑ i : Fin n, (if b i then (1 : ℝ) else -1))
        = ∑ i : Fin n, ((if b i then (2 : ℝ) else 0) - 1) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases hbi : b i <;> norm_num [hbi]
    _ = (∑ i : Fin n, (if b i then (2 : ℝ) else 0)) - ∑ i : Fin n, (1 : ℝ) := by
          rw [Finset.sum_sub_distrib]
    _ = 2 * (trueCoordinates b).card - n := by
          have hTwo :
              (∑ i : Fin n, (if b i then (2 : ℝ) else 0)) =
                2 * ∑ i : Fin n, (if b i then (1 : ℝ) else 0) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases hbi : b i <;> simp [hbi]
          rw [hTwo]
          simp [trueCoordinates, Finset.sum_boole, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg]

/-- Helper for Theorem 23.1: the Boolean-sign upper-tail event is equivalent to a lower bound on
the number of `true` coordinates. -/
private theorem boolSignSum_ge_iff_ceil_le_trueCount {n : ℕ} {x : ℝ} (b : Fin n → Bool) :
    x * n ≤ ∑ i : Fin n, (if b i then (1 : ℝ) else -1) ↔
      Nat.ceil (((n : ℝ) * (1 + x)) / 2) ≤ (trueCoordinates b).card := by
  -- Proof comment: substitute the sign-sum identity and solve the remaining affine inequality for
  -- the integer count `# {i | b i = true}`.
  rw [boolSignSum_eq_two_mul_card_trueCoordinates_sub]
  constructor
  · intro h
    refine Nat.ceil_le.2 ?_
    nlinarith
  · intro h
    have h' : (((n : ℝ) * (1 + x)) / 2) ≤ (trueCoordinates b).card := Nat.ceil_le.mp h
    nlinarith

/-- Helper for Theorem 23.1: the partial sum of the first `n` Rademacher coordinates has the same
law as the Boolean-cube sign sum. -/
private theorem rademacherPartialSum_hasLaw_boolSignSum
    (hX_iid : IsIID X P)
    (hX0_law : HasLaw (X 0) rademacherTwoPointLaw P)
    (n : ℕ) :
    HasLaw (partialSum X n)
      (Measure.map (fun b : Fin n → Bool ↦ ∑ i : Fin n, (if b i then (1 : ℝ) else -1))
        (Measure.pi fun _ : Fin n ↦ ((PMF.uniformOfFintype Bool).toMeasure))) P := by
  let cube : Measure (Fin n → Bool) :=
    Measure.pi fun _ : Fin n ↦ ((PMF.uniformOfFintype Bool).toMeasure)
  let signVec : (Fin n → Bool) → Fin n → ℝ := fun b i ↦ if b i then (1 : ℝ) else -1
  let sumVec : (Fin n → ℝ) → ℝ := fun z ↦ ∑ i : Fin n, z i
  let prefixVec : Ω → Fin n → ℝ := fun ω i ↦ X i.1 ω
  have hPrefix :=
    rademacherPrefix_hasLawPi (P := P) (X := X) hX_iid hX0_law n
  have hSumLaw :
      HasLaw sumVec
        (Measure.map sumVec (Measure.pi fun _ : Fin n ↦ rademacherTwoPointLaw))
        (Measure.pi fun _ : Fin n ↦ rademacherTwoPointLaw) := by
    -- Proof comment: the finite sum map has the pushforward law attached to the product measure by
    -- definition.
    exact ⟨by fun_prop, rfl⟩
  have hComposite :
      HasLaw (sumVec ∘ prefixVec)
        (Measure.map sumVec (Measure.pi fun _ : Fin n ↦ rademacherTwoPointLaw)) P :=
    HasLaw.comp hSumLaw hPrefix
  have hPartialEq : partialSum X n =ᵐ[P] sumVec ∘ prefixVec := by
    -- Proof comment: the abstract composite `sumVec ∘ prefixVec` is exactly the textbook partial
    -- sum.
    refine Filter.EventuallyEq.of_eq ?_
    funext ω
    simp [sumVec, prefixVec, partialSum_apply, ← Fin.sum_univ_eq_sum_range]
  have hTarget :
      Measure.map sumVec (Measure.pi fun _ : Fin n ↦ rademacherTwoPointLaw) =
        Measure.map (fun b : Fin n → Bool ↦ ∑ i : Fin n, (if b i then (1 : ℝ) else -1)) cube := by
    -- Proof comment: rewrite the product Rademacher law through the Boolean cube and collapse the
    -- successive pushforwards.
    rw [rademacherPrefix_eq_uniformBoolCube (n := n)]
    rw [AEMeasurable.map_map_of_aemeasurable (μ := cube) (by fun_prop)
      (measurable_of_countable signVec).aemeasurable]
    rfl
  let hPartialLaw := hComposite.congr hPartialEq
  exact
    { aemeasurable := hPartialLaw.aemeasurable
      map_eq := by
        rw [hPartialLaw.map_eq, hTarget] }

/-- Helper for Theorem 23.1: the upper-tail event can be rewritten as a Boolean-cube mass before
the counting step. -/
private theorem rademacherUpperTail_eq_boolCubeMass
    (hX_iid : IsIID X P)
    (hX0_law : HasLaw (X 0) rademacherTwoPointLaw P)
    (n : ℕ) (x : ℝ) :
    P {ω | x * n ≤ partialSum X n ω} =
      (Measure.pi fun _ : Fin n ↦ ((PMF.uniformOfFintype Bool).toMeasure))
        {b : Fin n → Bool | x * n ≤ ∑ i : Fin n, (if b i then (1 : ℝ) else -1)} := by
  let cube : Measure (Fin n → Bool) :=
    Measure.pi fun _ : Fin n ↦ ((PMF.uniformOfFintype Bool).toMeasure)
  let signSum : (Fin n → Bool) → ℝ := fun b ↦ ∑ i : Fin n, (if b i then (1 : ℝ) else -1)
  have hLaw :=
    rademacherPartialSum_hasLaw_boolSignSum (P := P) (X := X) hX_iid hX0_law n
  have hsignSum_meas : Measurable signSum := measurable_of_countable signSum
  have hThresholdMeas : MeasurableSet (Set.Ici (x * n)) := measurableSet_Ici
  -- Proof comment: transport the partial-sum law to the Boolean cube and read the threshold event
  -- as a preimage under the explicit sign-sum map.
  calc
    P {ω | x * n ≤ partialSum X n ω}
        = P.map (partialSum X n) (Set.Ici (x * n)) := by
            change P ((partialSum X n) ⁻¹' Set.Ici (x * n)) =
              P.map (partialSum X n) (Set.Ici (x * n))
            rw [← Measure.map_apply_of_aemeasurable hLaw.aemeasurable hThresholdMeas]
    _ = Measure.map signSum cube (Set.Ici (x * n)) := by
          exact congrArg (fun ν : Measure ℝ ↦ ν (Set.Ici (x * n))) hLaw.map_eq
    _ = cube {b : Fin n → Bool | x * n ≤ ∑ i : Fin n, (if b i then (1 : ℝ) else -1)} := by
          rw [Measure.map_apply hsignSum_meas hThresholdMeas]
          rfl

/-- Helper for Theorem 23.1: the Boolean-cube upper-tail event is exactly the corresponding
binomial choose tail. -/
private theorem boolCubeMass_eq_chooseTail {x : ℝ} (n : ℕ) (hx : 0 ≤ x) :
    (Measure.pi fun _ : Fin n ↦ ((PMF.uniformOfFintype Bool).toMeasure))
      {b : Fin n → Bool | x * n ≤ ∑ i : Fin n, (if b i then (1 : ℝ) else -1)} =
      ((2 : ENNReal) ^ n)⁻¹ *
        Finset.sum (Finset.Icc (Nat.ceil (((n : ℝ) * (1 + x)) / 2)) n)
          (fun k ↦ (Nat.choose n k : ENNReal)) := by
  -- Proof comment: the remaining step is the exact finite-counting partition of the Boolean cube
  -- by the number of `true` coordinates.
  classical
  let a : ℕ := Nat.ceil (((n : ℝ) * (1 + x)) / 2)
  let event : Set (Fin n → Bool) :=
    {b : Fin n → Bool | x * n ≤ ∑ i : Fin n, (if b i then (1 : ℝ) else -1)}
  let words : Finset (Fin n → Bool) := Finset.univ.filter fun b ↦ a ≤ (trueCoordinates b).card
  have hwords : ∀ b : Fin n → Bool, b ∈ words ↔ b ∈ event := by
    intro b
    simp [words, event, a, boolSignSum_ge_iff_ceil_le_trueCount, hx]
  have hMapsTo :
      (words : Set (Fin n → Bool)).MapsTo
        (fun b ↦ (trueCoordinates b).card) (Finset.Icc a n : Set ℕ) := by
    intro b hb
    have hb' : a ≤ (trueCoordinates b).card := by
      simpa [words] using hb
    exact Finset.mem_Icc.mpr ⟨hb', by simpa using (Finset.card_le_univ (trueCoordinates b))⟩
  rw [uniformBoolCube_eq_uniformMeasure]
  rw [PMF.toMeasure_uniformOfFintype_apply (s := event) event.toFinite.measurableSet]
  have hcardWords : (Fintype.card event : ENNReal) = words.card := by
    exact_mod_cast Fintype.card_of_finset' words hwords
  have hcount :
      (words.card : ENNReal) =
        Finset.sum (Finset.Icc a n)
          (fun k ↦ ((words.filter fun b ↦ (trueCoordinates b).card = k).card : ENNReal)) := by
    exact_mod_cast
      (Finset.card_eq_sum_card_fiberwise (s := words) (t := Finset.Icc a n)
        (f := fun b : Fin n → Bool ↦ (trueCoordinates b).card) hMapsTo)
  have hcardBool : (Fintype.card (Fin n → Bool) : ENNReal) = 2 ^ n := by
    simp
  rw [hcardWords, hcardBool, div_eq_mul_inv, hcount, mul_comm]
  refine congrArg (((2 : ENNReal) ^ n)⁻¹ * ·) ?_
  refine Finset.sum_congr rfl ?_
  intro k hk
  rcases Finset.mem_Icc.mp hk with ⟨hk_left, hk_right⟩
  have hfilter :
      words.filter fun b ↦ (trueCoordinates b).card = k =
        Finset.univ.filter fun b : Fin n → Bool ↦ (trueCoordinates b).card = k := by
    ext b
    by_cases hbk : (trueCoordinates b).card = k
    · have hmem : a ≤ (trueCoordinates b).card := by
        rw [hbk]
        exact hk_left
      constructor
      · intro hb
        have hb' : a ≤ (trueCoordinates b).card ∧ (trueCoordinates b).card = k := by
          simpa [Finset.mem_filter, words] using hb
        simpa [Finset.mem_filter] using hb'.2
      · intro hb
        have hb' : a ≤ (trueCoordinates b).card ∧ (trueCoordinates b).card = k := ⟨hmem, hbk⟩
        simpa [Finset.mem_filter, words] using hb'
    · constructor <;> intro hb <;> simp [Finset.mem_filter, words, hbk] at hb ⊢
  rw [hfilter]
  have hcardk :
      Fintype.card {b : Fin n → Bool // (trueCoordinates b).card = k} =
        (Finset.univ.filter fun b : Fin n → Bool ↦ (trueCoordinates b).card = k).card :=
    Fintype.card_ofFinset
      (p := {b : Fin n → Bool | (trueCoordinates b).card = k})
      (Finset.univ.filter fun b : Fin n → Bool ↦ (trueCoordinates b).card = k)
      (by intro b; simp)
  rw [← hcardk]
  exact_mod_cast card_boolWords_trueCount_eq_choose n k

/-- Helper for Theorem 23.1: the Rademacher upper-tail event is exactly the corresponding
binomial choose tail. -/
private theorem rademacherUpperTail_eq_chooseTail
    (hX_iid : IsIID X P)
    (hX0_law : HasLaw (X 0) rademacherTwoPointLaw P)
    (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    P {ω | x * n ≤ partialSum X n ω} =
      ((2 : ENNReal) ^ n)⁻¹ *
        Finset.sum (Finset.Icc (Nat.ceil (((n : ℝ) * (1 + x)) / 2)) n)
          (fun k ↦ (Nat.choose n k : ENNReal)) := by
  -- Proof comment: after transporting the event to the Boolean cube, the exact counting formula
  -- from `boolCubeMass_eq_chooseTail` finishes the rewrite.
  rw [rademacherUpperTail_eq_boolCubeMass (P := P) (X := X) hX_iid hX0_law n x]
  exact boolCubeMass_eq_chooseTail n hx

/-- Helper for Theorem 23.1: the affine threshold index `ceil(n (1 + x) / 2)` lies on or beyond
the midpoint when `x ≥ 0`. -/
private theorem prefixLength_le_two_mul_upperTailIndex {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    n ≤ 2 * Nat.ceil (((n : ℝ) * (1 + x)) / 2) := by
  -- Proof comment: compare `n / 2` with the affine threshold in `ℝ`, then pass to the integer
  -- ceiling.
  have hCeil :
      (((n : ℝ) * (1 + x)) / 2 : ℝ) ≤ Nat.ceil (((n : ℝ) * (1 + x)) / 2) := by
    exact_mod_cast (Nat.le_ceil (((n : ℝ) * (1 + x)) / 2))
  have hReal : (n : ℝ) ≤ 2 * Nat.ceil (((n : ℝ) * (1 + x)) / 2) := by
    have hBase : (n : ℝ) ≤ 2 * ((((n : ℝ) * (1 + x)) / 2 : ℝ)) := by
      nlinarith
    nlinarith
  exact_mod_cast hReal

/-- Helper for Theorem 23.1: once the starting index is on the upper half of the Pascal row, every
later binomial coefficient is bounded by the first one. -/
private theorem choose_le_choose_of_upperHalf {n a k : ℕ}
    (hhalf : n ≤ 2 * a) (hak : a ≤ k) :
    Nat.choose n k ≤ Nat.choose n a := by
  -- Proof comment: iterate the one-step upper-half monotonicity from `a` up to `k`.
  let d := k - a
  have hd :
      Nat.choose n (a + d) ≤ Nat.choose n a := by
    induction d with
    | zero =>
        simp
    | succ d ih =>
        have hstep :
            Nat.choose n (a + d + 1) ≤ Nat.choose n (a + d) := by
          refine chooseSucc_le_of_half_le ?_
          omega
        exact hstep.trans ih
  simpa [d, Nat.add_sub_of_le hak] using hd

/-- Helper for Theorem 23.1: the upper binomial tail is squeezed between its first term and
`(n + 1)` times that first term. -/
private theorem binomialTailFirstTerm_bounds {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (Nat.choose n (Nat.ceil (((n : ℝ) * (1 + x)) / 2)) : ENNReal) ≤
        Finset.sum (Finset.Icc (Nat.ceil (((n : ℝ) * (1 + x)) / 2)) n)
          (fun k ↦ (Nat.choose n k : ENNReal)) ∧
      Finset.sum (Finset.Icc (Nat.ceil (((n : ℝ) * (1 + x)) / 2)) n)
          (fun k ↦ (Nat.choose n k : ENNReal)) ≤
        (n + 1 : ENNReal) * (Nat.choose n (Nat.ceil (((n : ℝ) * (1 + x)) / 2)) : ENNReal) := by
  -- Proof comment: the upper-half monotonicity of the Pascal row reduces the whole tail to its
  -- first term up to the interval cardinality.
  let a : ℕ := Nat.ceil (((n : ℝ) * (1 + x)) / 2)
  have hhalf : n ≤ 2 * a := prefixLength_le_two_mul_upperTailIndex hx n
  constructor
  · by_cases ha : a ≤ n
    · have ha_mem : a ∈ Finset.Icc a n := Finset.mem_Icc.mpr ⟨le_rfl, ha⟩
      have hsingle :
          (Nat.choose n a : ENNReal) ≤
            Finset.sum (Finset.Icc a n) (fun k ↦ (Nat.choose n k : ENNReal)) := by
        exact Finset.single_le_sum
          (s := Finset.Icc a n)
          (a := a)
          (f := fun k ↦ (Nat.choose n k : ENNReal))
          (fun k hk ↦ by positivity)
          ha_mem
      simpa [a] using hsingle
    · have hchoose_zero : Nat.choose n a = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge ha)
      have hIcc_empty : Finset.Icc a n = ∅ := Finset.Icc_eq_empty_of_lt (Nat.lt_of_not_ge ha)
      have hsum_zero :
          Finset.sum (Finset.Icc a n) (fun k ↦ (Nat.choose n k : ENNReal)) = 0 := by
        simp [hIcc_empty]
      simpa [a, hchoose_zero, hsum_zero]
  · have hsumBound :
        Finset.sum (Finset.Icc a n) (fun k ↦ (Nat.choose n k : ENNReal)) ≤
          (n + 1 : ENNReal) * (Nat.choose n a : ENNReal) := by
      calc
        Finset.sum (Finset.Icc a n) (fun k ↦ (Nat.choose n k : ENNReal))
            ≤ Finset.sum (Finset.Icc a n) (fun _ ↦ (Nat.choose n a : ENNReal)) := by
                refine Finset.sum_le_sum ?_
                intro k hk
                exact_mod_cast
                  choose_le_choose_of_upperHalf (n := n) (a := a) (k := k) hhalf
                    (Finset.mem_Icc.mp hk).1
        _ = ((Finset.Icc a n).card : ENNReal) * (Nat.choose n a : ENNReal) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (n + 1 : ENNReal) * (Nat.choose n a : ENNReal) := by
              refine mul_le_mul_right' ?_ (Nat.choose n a : ENNReal)
              exact_mod_cast (show (Finset.Icc a n).card ≤ n + 1 by
                rw [Nat.card_Icc]
                omega)
    simpa [a] using hsumBound

/-- Helper for Theorem 23.1: every partial sum is pathwise bounded above by its length because
each summand is almost surely either `-1` or `1`. -/
private theorem partialSum_le_prefixLength_ae
    (hSigns : ∀ n : ℕ, ∀ᵐ ω ∂P, X n ω = -1 ∨ X n ω = 1) :
    ∀ n : ℕ, ∀ᵐ ω ∂P, partialSum X n ω ≤ n := by
  -- Proof comment: this is the pathwise induction `S_{n+1} = S_n + X_n` with the increment bound
  -- `X_n ≤ 1`.
  intro n
  induction n with
  | zero =>
      exact Filter.Eventually.of_forall fun ω ↦ by simp [partialSum_apply]
  | succ n ih =>
      filter_upwards [ih, hSigns n] with ω hprefix hsign
      have hstep : X n ω ≤ 1 := by
        rcases hsign with hneg | hpos
        · linarith
        · linarith
      rw [partialSum_apply] at hprefix
      rw [partialSum_apply]
      rw [Finset.sum_range_succ]
      have hbound : (∑ i ∈ Finset.range n, X i ω) + X n ω ≤ (n : ℝ) + 1 := by
        linarith
      simpa [Nat.cast_add] using hbound

/-- Helper for Theorem 23.1: if `x ≤ 1`, then the affine ceiling index for the upper tail never
exceeds the prefix length. -/
private theorem upperTailIndex_le_self {x : ℝ} (hx : x ≤ 1) (n : ℕ) :
    Nat.ceil (((n : ℝ) * (1 + x)) / 2) ≤ n := by
  -- Proof comment: compare the affine threshold with `n` already in `ℝ`, and then pass to the
  -- natural ceiling.
  refine Nat.ceil_le.2 ?_
  have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  nlinarith

/-- Helper for Theorem 23.1: in the strict interior regime `0 ≤ x < 1`, the affine ceiling index
is eventually strictly between `0` and `n`. -/
private theorem upperTailIndex_eventually_strictInterior {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∀ᶠ n : ℕ in atTop,
      0 < Nat.ceil (((n : ℝ) * (1 + x)) / 2) ∧
        Nat.ceil (((n : ℝ) * (1 + x)) / 2) < n := by
  -- Proof comment: the threshold eventually sits strictly inside `(0, n)` because `(1 + x) / 2`
  -- lies strictly between `0` and `1`.
  let N : ℕ := Nat.ceil (2 / (1 - x))
  have hN_pos : 0 < N := by
    refine Nat.ceil_pos.2 ?_
    have hx_pos : 0 < 1 - x := sub_pos.mpr hx1
    positivity
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hn_pos : 0 < n := lt_of_lt_of_le hN_pos hn
  constructor
  · have hExpr_pos : 0 < (((n : ℝ) * (1 + x)) / 2) := by
      have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn_pos
      nlinarith
    exact Nat.ceil_pos.mpr hExpr_pos
  · have hN_le : (2 / (1 - x) : ℝ) ≤ n := by
      have hceil_le : (Nat.ceil (2 / (1 - x)) : ℝ) ≤ n := by
        exact_mod_cast hn
      have hbase : (2 / (1 - x) : ℝ) ≤ Nat.ceil (2 / (1 - x)) := by
        exact_mod_cast Nat.le_ceil (2 / (1 - x))
      exact hbase.trans hceil_le
    have hx_gap : 0 < 1 - x := sub_pos.mpr hx1
    have hGap' : 2 ≤ (n : ℝ) * (1 - x) := by
      exact (div_le_iff₀ hx_gap).mp (by simpa [mul_comm] using hN_le)
    have hGap : 1 ≤ (n : ℝ) * (1 - x) / 2 := by
      nlinarith
    have hCeilLt :
        (Nat.ceil (((n : ℝ) * (1 + x)) / 2) : ℝ) <
          (((n : ℝ) * (1 + x)) / 2) + 1 := by
      refine Nat.ceil_lt_add_one ?_
      positivity
    have hUpper :
        (((n : ℝ) * (1 + x)) / 2) + 1 ≤ n := by
      nlinarith
    have hlt_real : (Nat.ceil (((n : ℝ) * (1 + x)) / 2) : ℝ) < n :=
      lt_of_lt_of_le hCeilLt hUpper
    exact_mod_cast hlt_real

/-- Helper for Theorem 23.1: the normalized affine ceiling index converges to the magnetization
parameter `x`. -/
private theorem upperTailIndexMagnetization_tendsto {x : ℝ} (hx0 : 0 ≤ x) :
    Tendsto
      (fun n : ℕ ↦ ((2 * Nat.ceil (((n : ℝ) * (1 + x)) / 2) : ℝ) / n - 1))
      atTop
      (𝓝 x) := by
  -- Proof comment: this is the affine rewrite of the standard ceiling asymptotic for
  -- `((1 + x) / 2) n`.
  have hHalf : 0 ≤ (1 + x) / 2 := by
    nlinarith
  have hCeil :
      Tendsto
        (fun n : ℕ ↦ ((Nat.ceil (((n : ℝ) * (1 + x)) / 2) : ℝ) / n))
        atTop
        (𝓝 ((1 + x) / 2)) := by
    -- Proof comment: rewrite the threshold as the ceiling of `((1 + x) / 2) * n` and apply the
    -- standard ceiling-over-`n` limit.
    simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using
      (tendsto_nat_ceil_mul_div_atTop (R := ℝ) (a := (1 + x) / 2) hHalf).comp
        tendsto_natCast_atTop_atTop
  -- Proof comment: the magnetization expression is the affine image `u ↦ 2u - 1` of the
  -- normalized threshold index.
  have hAffineRaw :
      Tendsto
        (fun n : ℕ ↦ (2 : ℝ) * (((Nat.ceil (((n : ℝ) * (1 + x)) / 2) : ℝ) / n)) - 1)
        atTop
        (𝓝 ((2 : ℝ) * ((1 + x) / 2) - 1)) :=
    (tendsto_const_nhds.mul hCeil).sub tendsto_const_nhds
  have hAffine :
      Tendsto
        (fun n : ℕ ↦ (2 : ℝ) * (((Nat.ceil (((n : ℝ) * (1 + x)) / 2) : ℝ) / n)) - 1)
        atTop
        (𝓝 x) := by
    convert hAffineRaw using 2
    ring
  have hRewrite :
      (fun n : ℕ ↦ ((2 * Nat.ceil (((n : ℝ) * (1 + x)) / 2) : ℝ) / n - 1)) =
        (fun n : ℕ ↦ (2 : ℝ) * (((Nat.ceil (((n : ℝ) * (1 + x)) / 2) : ℝ) / n)) - 1) := by
    funext n
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  simpa [hRewrite] using hAffine

/-- Helper for Theorem 23.1: the affine ceiling index and its complement both have the expected
strict-interior proportions. -/
private theorem upperTailIndexHalves_tendsto {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Tendsto
        (fun n : ℕ ↦ ((Nat.ceil (((n : ℝ) * (1 + x)) / 2) : ℝ) / n))
        atTop
        (𝓝 ((1 + x) / 2)) ∧
      Tendsto
        (fun n : ℕ ↦ ((n - Nat.ceil (((n : ℝ) * (1 + x)) / 2) : ℝ) / n))
        atTop
        (𝓝 ((1 - x) / 2)) := by
  have hHalfNonneg : 0 ≤ (1 + x) / 2 := by
    nlinarith
  have hFirst :
      Tendsto
        (fun n : ℕ ↦ ((Nat.ceil (((n : ℝ) * (1 + x)) / 2) : ℝ) / n))
        atTop
        (𝓝 ((1 + x) / 2)) := by
    -- Proof comment: rewrite the threshold as the ceiling of `((1 + x) / 2) * n` and apply the
    -- standard ceiling-over-`n` limit.
    simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using
      (tendsto_nat_ceil_mul_div_atTop (R := ℝ) (a := (1 + x) / 2) hHalfNonneg).comp
        tendsto_natCast_atTop_atTop
  have hRewrite :
      (fun n : ℕ ↦ ((n - Nat.ceil (((n : ℝ) * (1 + x)) / 2) : ℝ) / n)) =ᶠ[atTop]
        fun n : ℕ ↦ 1 - ((Nat.ceil (((n : ℝ) * (1 + x)) / 2) : ℝ) / n) := by
    -- Proof comment: once `n ≥ 1`, the complement ratio is the affine transform `u ↦ 1 - u` of
    -- the threshold ratio.
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hle : Nat.ceil (((n : ℝ) * (1 + x)) / 2) ≤ n := upperTailIndex_le_self (le_of_lt hx1) n
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (Nat.succ_le_iff.mp hn)
    rw [sub_div]
    field_simp [hn0]
  have hSecondRaw :
      Tendsto
        (fun n : ℕ ↦ 1 - ((Nat.ceil (((n : ℝ) * (1 + x)) / 2) : ℝ) / n))
        atTop
        (𝓝 (1 - (1 + x) / 2)) :=
    tendsto_const_nhds.sub hFirst
  have hSecond :
      Tendsto
        (fun n : ℕ ↦ ((n - Nat.ceil (((n : ℝ) * (1 + x)) / 2) : ℝ) / n))
        atTop
        (𝓝 ((1 - x) / 2)) := by
    -- Proof comment: the complement proportion is the affine image of the first ratio.
    convert hSecondRaw.congr' hRewrite.symm using 1
    ring
  exact ⟨hFirst, hSecond⟩

/-- Helper for Theorem 23.1: an eventually bounded real sequence divided by `n` tends to `0`. -/
private theorem eventuallyBounded_div_nat_tendsto_zero {u : ℕ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hu : ∀ᶠ n : ℕ in atTop, |u n| ≤ C) :
    Tendsto (fun n : ℕ ↦ u n / n) atTop (𝓝 0) := by
  -- Proof comment: control the norm of `u n / n` by the deterministic bound `C / n`, whose limit
  -- is the standard `0`.
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n ↦ by positivity) ?_
    (tendsto_const_div_atTop_nhds_zero_nat C)
  · filter_upwards [hu] with n hn
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (show 0 ≤ (n : ℝ) by positivity)]
    exact div_le_div_of_nonneg_right hn (show 0 ≤ (n : ℝ) by positivity)

/-- Helper for Theorem 23.1: a convergent real sequence divided by `n` tends to `0`. -/
private theorem tendsto_div_nat_tendsto_zero_of_tendsto {u : ℕ → ℝ} {l : ℝ}
    (hu : Tendsto u atTop (𝓝 l)) :
    Tendsto (fun n : ℕ ↦ u n / n) atTop (𝓝 0) := by
  have hBound :
      ∀ᶠ n : ℕ in atTop, |u n| ≤ |l| + 1 := by
    -- Proof comment: every convergent real sequence is eventually trapped in a unit ball around
    -- its limit, hence eventually bounded.
    filter_upwards [hu (Metric.ball_mem_nhds _ zero_lt_one)] with n hn
    have hdist : |u n - l| < 1 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hn
    calc
      |u n| = |(u n - l) + l| := by ring_nf
      _ ≤ |u n - l| + |l| := abs_add_le _ _
      _ ≤ |l| + 1 := by linarith
  exact eventuallyBounded_div_nat_tendsto_zero (show 0 ≤ |l| + 1 by positivity) hBound

/-- Helper for Theorem 23.1: after normalizing by an external scale `n`, the Stirling expansion of
`log (m n)!` retains only the entropy term `p * log p`. -/
private theorem logFactorialAgainstScale_tendsto
    (m : ℕ → ℕ) {p : ℝ}
    (hm : Tendsto (fun n : ℕ ↦ ((m n : ℝ) / n)) atTop (𝓝 p))
    (hp : 0 < p) :
    Tendsto
      (fun n : ℕ ↦ (Real.log (Nat.factorial (m n)) - ((m n : ℝ) * Real.log n - (m n : ℝ))) / n)
      atTop
      (𝓝 (p * Real.log p)) := by
  have hmPos :
      ∀ᶠ n : ℕ in atTop, 0 < m n := by
    -- Proof comment: a positive limiting proportion forces the integer sequence `m n` to be
    -- eventually positive as well.
    filter_upwards [hm (Ioi_mem_nhds (by linarith : p / 2 < p)), Filter.eventually_ge_atTop 1]
      with n hn hn1
    have hratio : p / 2 < (m n : ℝ) / n := by
      simpa using hn
    have hnReal : 0 < (n : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mp hn1
    have hmReal : 0 < (m n : ℝ) := by
      have hratioPos : 0 < (m n : ℝ) / n := by
        have hpHalf : 0 < p / 2 := by positivity
        exact lt_trans hpHalf hratio
      exact (div_pos_iff_of_pos_right hnReal).1 hratioPos
    exact_mod_cast hmReal
  have hMain :
      Tendsto
        (fun n : ℕ ↦ ((m n : ℝ) / n) * Real.log ((m n : ℝ) / n))
        atTop
        (𝓝 (p * Real.log p)) := by
    -- Proof comment: the entropy contribution is the product of the convergent proportion and its
    -- logarithm.
    refine hm.mul ?_
    exact ((Real.continuousAt_log (by positivity : p ≠ 0)).tendsto).comp hm
  have hStirlingDiv :
      Tendsto (fun n : ℕ ↦ Real.log (Stirling.stirlingSeq (m n)) / n) atTop (𝓝 0) := by
    have hBound :
        ∀ᶠ n : ℕ in atTop,
          |Real.log (Stirling.stirlingSeq (m n))| ≤
            max |Real.log (Stirling.stirlingSeq 1)| |Real.log (Real.sqrt Real.pi)| := by
      -- Proof comment: the positive Stirling sequence stays between its first value and its
      -- limiting lower bound `√π`, so its logarithm is uniformly bounded.
      filter_upwards [hmPos] with n hn
      rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨k, hk⟩
      rw [hk]
      have hLower :
          Real.log (Real.sqrt Real.pi) ≤ Real.log (Stirling.stirlingSeq (k + 1)) := by
        exact Real.log_le_log (by positivity) (Stirling.sqrt_pi_le_stirlingSeq (Nat.succ_ne_zero k))
      have hUpperSeq : Stirling.stirlingSeq (k + 1) ≤ Stirling.stirlingSeq 1 := by
        simpa using Stirling.stirlingSeq'_antitone (show 0 ≤ k by exact Nat.zero_le k)
      have hUpper :
          Real.log (Stirling.stirlingSeq (k + 1)) ≤ Real.log (Stirling.stirlingSeq 1) := by
        exact Real.log_le_log (Stirling.stirlingSeq'_pos k) hUpperSeq
      simpa [max_comm] using (abs_le_max_abs_abs hLower hUpper)
    exact
      eventuallyBounded_div_nat_tendsto_zero
        (show
          0 ≤ max |Real.log (Stirling.stirlingSeq 1)| |Real.log (Real.sqrt Real.pi)| by positivity)
        hBound
  have hLogNatDiv :
      Tendsto (fun n : ℕ ↦ Real.log n / n) atTop (𝓝 0) := by
    -- Proof comment: logarithmic growth is negligible compared with the linear scale `n`.
    simpa [pow_one] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
  have hScaledLogDiv :
      Tendsto (fun n : ℕ ↦ Real.log (2 * ((m n : ℝ) / n)) / n) atTop (𝓝 0) := by
    -- Proof comment: after removing the ambient scale `n`, the logarithm of the bounded ratio term
    -- contributes only a vanishing `1 / n` factor.
    refine tendsto_div_nat_tendsto_zero_of_tendsto (l := Real.log (2 * p)) ?_
    have hScaled :
        Tendsto (fun n : ℕ ↦ 2 * ((m n : ℝ) / n)) atTop (𝓝 (2 * p)) :=
      tendsto_const_nhds.mul hm
    exact ((Real.continuousAt_log (by positivity : 2 * p ≠ 0)).tendsto).comp hScaled
  have hHalfLogDiv :
      Tendsto
        (fun n : ℕ ↦ (1 / 2 : ℝ) * (Real.log (2 * (m n : ℝ)) / n))
        atTop
        (𝓝 0) := by
    have hRewrite :
        (fun n : ℕ ↦ (1 / 2 : ℝ) * (Real.log (2 * (m n : ℝ)) / n)) =ᶠ[atTop]
          fun n : ℕ ↦
            (1 / 2 : ℝ) * (Real.log n / n) +
              (1 / 2 : ℝ) * (Real.log (2 * ((m n : ℝ) / n)) / n) := by
      -- Proof comment: split `log (2 * m n)` into the ambient scale `log n` and the normalized
      -- ratio `log (2 * (m n / n))`.
      filter_upwards [hmPos, Filter.eventually_ge_atTop 1] with n hmPosN hn
      have hnReal : 0 < (n : ℝ) := by
        exact_mod_cast Nat.succ_le_iff.mp hn
      have hmReal : 0 < (m n : ℝ) := by
        exact_mod_cast hmPosN
      have hMul :
          (n : ℝ) * (2 * ((m n : ℝ) / n)) = 2 * (m n : ℝ) := by
        field_simp [hnReal.ne']
      rw [← hMul, Real.log_mul hnReal.ne' (by positivity), add_div, mul_add]
    have hLeft :
        Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) * (Real.log n / n)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hLogNatDiv : Tendsto
        (fun n : ℕ ↦ (1 / 2 : ℝ) * (Real.log n / n)) atTop (𝓝 ((1 / 2 : ℝ) * 0)))
    have hRight :
        Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) * (Real.log (2 * ((m n : ℝ) / n)) / n)) atTop (𝓝 0) :=
      by
        simpa using (tendsto_const_nhds.mul hScaledLogDiv : Tendsto
          (fun n : ℕ ↦ (1 / 2 : ℝ) * (Real.log (2 * ((m n : ℝ) / n)) / n))
          atTop (𝓝 ((1 / 2 : ℝ) * 0)))
    have hSum :
        Tendsto
          (fun n : ℕ ↦
            (1 / 2 : ℝ) * (Real.log n / n) +
              (1 / 2 : ℝ) * (Real.log (2 * ((m n : ℝ) / n)) / n))
          atTop
          (𝓝 0) := by
      simpa using
        (hLeft.add hRight : Tendsto
          (fun n : ℕ ↦
            (1 / 2 : ℝ) * (Real.log n / n) +
              (1 / 2 : ℝ) * (Real.log (2 * ((m n : ℝ) / n)) / n))
          atTop
          (𝓝 (0 + 0)))
    exact hSum.congr' hRewrite.symm
  have hEventually :
      (fun n : ℕ ↦
        (Real.log (Nat.factorial (m n)) - ((m n : ℝ) * Real.log n - (m n : ℝ))) / n) =ᶠ[atTop]
        fun n : ℕ ↦
          Real.log (Stirling.stirlingSeq (m n)) / n +
            (1 / 2 : ℝ) * (Real.log (2 * (m n : ℝ)) / n) +
              ((m n : ℝ) / n) * Real.log ((m n : ℝ) / n) := by
    -- Proof comment: rewrite the logarithmic factorial through Stirling's identity, then isolate
    -- the three terms whose limits are already known.
    filter_upwards [hmPos, Filter.eventually_ge_atTop 1] with n hmPosN hn
    have hmReal : 0 < (m n : ℝ) := by
      exact_mod_cast hmPosN
    have hnReal : 0 < (n : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mp hn
    have hLogExp :
        Real.log ((m n : ℝ) / Real.exp 1) = Real.log (m n : ℝ) - 1 := by
      rw [Real.log_div hmReal.ne' (Real.exp_ne_zero _), Real.log_exp]
    have hLogSplit :
        Real.log (m n : ℝ) = Real.log ((m n : ℝ) / n) + Real.log n := by
      have hDiv :
          Real.log ((m n : ℝ) / n) = Real.log (m n : ℝ) - Real.log n := by
        rw [Real.log_div hmReal.ne' hnReal.ne']
      linarith
    have hFormula := Stirling.log_stirlingSeq_formula (m n)
    rw [hLogExp, hLogSplit] at hFormula
    have hMainEq :
        Real.log (Nat.factorial (m n)) - ((m n : ℝ) * Real.log n - (m n : ℝ)) =
          Real.log (Stirling.stirlingSeq (m n)) +
            1 / 2 * Real.log (2 * (m n : ℝ)) +
              (m n : ℝ) * Real.log ((m n : ℝ) / n) := by
      linarith
    have hn0 : (n : ℝ) ≠ 0 := hnReal.ne'
    rw [hMainEq, add_div, add_div]
    congr 1
    field_simp [hn0]
    ring
  -- Proof comment: after the exact decomposition, the bounded Stirling term and the logarithmic
  -- scale term vanish, leaving only the entropy contribution.
  simpa [add_assoc] using (hStirlingDiv.add hHalfLogDiv).add hMain |>.congr' hEventually.symm

/-- Helper for Theorem 23.1: the first term of the strict-interior binomial tail has the entropy
asymptotic from Stirling's formula. -/
private theorem upperTailLogChoose_tendstoEntropy {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Tendsto
      (fun n : ℕ ↦ Real.log (Nat.choose n (Nat.ceil (((n : ℝ) * (1 + x)) / 2))) / n)
      atTop
      (𝓝 (Real.log 2 - bernoulliCramerRateFunction x)) := by
  let a : ℕ → ℕ := fun n ↦ Nat.ceil (((n : ℝ) * (1 + x)) / 2)
  let b : ℕ → ℕ := fun n ↦ n - a n
  obtain ⟨ha, hb⟩ := upperTailIndexHalves_tendsto hx0 hx1
  have hp : 0 < (1 + x) / 2 := by
    nlinarith
  have hq : 0 < (1 - x) / 2 := by
    nlinarith
  have hnRatio :
      Tendsto (fun n : ℕ ↦ ((n : ℝ) / n)) atTop (𝓝 (1 : ℝ)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (Nat.succ_le_iff.mp hn)
    field_simp [hn0]
  have hFactorialN :
      Tendsto
        (fun n : ℕ ↦ (Real.log (Nat.factorial n) - ((n : ℝ) * Real.log n - (n : ℝ))) / n)
        atTop
        (𝓝 (0 : ℝ)) := by
    simpa using logFactorialAgainstScale_tendsto (m := fun n ↦ n) hnRatio zero_lt_one
  have hFactorialA :
      Tendsto
        (fun n : ℕ ↦ (Real.log (Nat.factorial (a n)) - ((a n : ℝ) * Real.log n - (a n : ℝ))) / n)
        atTop
        (𝓝 (((1 + x) / 2) * Real.log ((1 + x) / 2))) := by
    exact logFactorialAgainstScale_tendsto (m := a) ha hp
  have hFactorialB :
      Tendsto
        (fun n : ℕ ↦ (Real.log (Nat.factorial (b n)) - ((b n : ℝ) * Real.log n - (b n : ℝ))) / n)
        atTop
        (𝓝 (((1 - x) / 2) * Real.log ((1 - x) / 2))) := by
    have hb' : Tendsto (fun n : ℕ ↦ ((b n : ℝ) / n)) atTop (𝓝 ((1 - x) / 2)) := by
      refine hb.congr' ?_
      filter_upwards with n
      have haLe : a n ≤ n := upperTailIndex_le_self (le_of_lt hx1) n
      simp [b, a, haLe, Nat.cast_sub haLe]
    simpa using logFactorialAgainstScale_tendsto (m := b) hb' hq
  have hRewrite :
      (fun n : ℕ ↦ Real.log (Nat.choose n (a n)) / n) =ᶠ[atTop]
        fun n : ℕ ↦
          ((Real.log (Nat.factorial n) - ((n : ℝ) * Real.log n - (n : ℝ))) / n) -
            ((Real.log (Nat.factorial (a n)) - ((a n : ℝ) * Real.log n - (a n : ℝ))) / n) -
              ((Real.log (Nat.factorial (b n)) - ((b n : ℝ) * Real.log n - (b n : ℝ))) / n) := by
    filter_upwards [upperTailIndex_eventually_strictInterior hx0 hx1] with n hn
    have haLe : a n ≤ n := Nat.le_of_lt hn.2
    have hbEq : a n + b n = n := by
      simp [b, a, haLe, Nat.add_sub_of_le haLe]
    have hChoose :
        Nat.choose n (a n) * (a n).factorial * (b n).factorial = n.factorial := by
      simpa [b, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        (Nat.choose_mul_factorial_mul_factorial haLe)
    have hChooseReal :
        (Nat.choose n (a n) : ℝ) * (((a n).factorial : ℝ) * ((b n).factorial : ℝ)) =
          (n.factorial : ℝ) := by
      exact_mod_cast (by simpa [mul_assoc] using hChoose)
    have hChoosePos : 0 < Nat.choose n (a n) := Nat.choose_pos haLe
    have hLogFactors :
        Real.log (((a n).factorial : ℝ) * ((b n).factorial : ℝ)) =
          Real.log ((a n).factorial : ℝ) + Real.log ((b n).factorial : ℝ) := by
      rw [Real.log_mul (by positivity) (by positivity)]
    have hLogChoose :
        Real.log (Nat.choose n (a n)) =
          Real.log (n.factorial : ℝ) -
            Real.log ((a n).factorial : ℝ) - Real.log ((b n).factorial : ℝ) := by
      have hLogProd :
          Real.log (n.factorial : ℝ) =
            Real.log (Nat.choose n (a n) : ℝ) +
              Real.log (((a n).factorial : ℝ) * ((b n).factorial : ℝ)) := by
        rw [← hChooseReal, Real.log_mul (by exact_mod_cast Nat.ne_of_gt hChoosePos) (by positivity)]
      rw [hLogFactors] at hLogProd
      linarith
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (lt_trans hn.1 hn.2)
    have hbReal : (a n : ℝ) + (b n : ℝ) = (n : ℝ) := by
      exact_mod_cast hbEq
    have hNum :
        Real.log (n.factorial : ℝ) - Real.log ((a n).factorial : ℝ) - Real.log ((b n).factorial : ℝ) =
          (Real.log (Nat.factorial n) - ((n : ℝ) * Real.log n - (n : ℝ))) -
            (Real.log (Nat.factorial (a n)) - ((a n : ℝ) * Real.log n - (a n : ℝ))) -
            (Real.log (Nat.factorial (b n)) - ((b n : ℝ) * Real.log n - (b n : ℝ))) := by
      -- Proof comment: the factorial logarithms are unchanged; only the linear `n`, `a n`, `b n`
      -- terms need the identity `a n + b n = n`.
      have hLinear :
          ((n : ℝ) * Real.log n - (n : ℝ)) =
            ((a n : ℝ) * Real.log n - (a n : ℝ)) +
              ((b n : ℝ) * Real.log n - (b n : ℝ)) := by
        calc
          ((n : ℝ) * Real.log n - (n : ℝ))
              = (((a n : ℝ) + (b n : ℝ)) * Real.log n - ((a n : ℝ) + (b n : ℝ))) := by
                  rw [hbReal]
          _ = ((a n : ℝ) * Real.log n - (a n : ℝ)) +
                ((b n : ℝ) * Real.log n - (b n : ℝ)) := by
                  ring
      rw [hLinear]
      ring
    calc
      Real.log (Nat.choose n (a n)) / n =
          (Real.log (n.factorial : ℝ) -
            Real.log ((a n).factorial : ℝ) - Real.log ((b n).factorial : ℝ)) / n := by
              rw [hLogChoose]
      _ =
          ((Real.log (Nat.factorial n) - ((n : ℝ) * Real.log n - (n : ℝ))) -
            (Real.log (Nat.factorial (a n)) - ((a n : ℝ) * Real.log n - (a n : ℝ))) -
            (Real.log (Nat.factorial (b n)) - ((b n : ℝ) * Real.log n - (b n : ℝ)))) / n := by
              rw [hNum]
      _ =
          ((Real.log (Nat.factorial n) - ((n : ℝ) * Real.log n - (n : ℝ))) / n) -
            ((Real.log (Nat.factorial (a n)) - ((a n : ℝ) * Real.log n - (a n : ℝ))) / n) -
              ((Real.log (Nat.factorial (b n)) - ((b n : ℝ) * Real.log n - (b n : ℝ))) / n) := by
                field_simp [hn0]
  have hRaw :
      Tendsto
        (fun n : ℕ ↦
          ((Real.log (Nat.factorial n) - ((n : ℝ) * Real.log n - (n : ℝ))) / n) -
            ((Real.log (Nat.factorial (a n)) - ((a n : ℝ) * Real.log n - (a n : ℝ))) / n) -
              ((Real.log (Nat.factorial (b n)) - ((b n : ℝ) * Real.log n - (b n : ℝ))) / n))
        atTop
        (𝓝
          ((0 : ℝ) - (((1 + x) / 2) * Real.log ((1 + x) / 2)) -
            (((1 - x) / 2) * Real.log ((1 - x) / 2)))) := by
    exact (hFactorialN.sub hFactorialA).sub hFactorialB
  have hEntropy :
      (0 : ℝ) - (((1 + x) / 2) * Real.log ((1 + x) / 2)) -
          (((1 - x) / 2) * Real.log ((1 - x) / 2)) =
        Real.log 2 - bernoulliCramerRateFunction x := by
    -- Proof comment: rewrite the normalized probabilities `((1 ± x) / 2)` by extracting the
    -- common `log 2` contribution.
    have hLogP : Real.log ((1 + x) / 2) = Real.log (1 + x) - Real.log 2 := by
      rw [Real.log_div (by linarith) (by norm_num : (2 : ℝ) ≠ 0)]
    have hLogQ : Real.log ((1 - x) / 2) = Real.log (1 - x) - Real.log 2 := by
      rw [Real.log_div (by linarith) (by norm_num : (2 : ℝ) ≠ 0)]
    rw [hLogP, hLogQ, bernoulliCramerRateFunction]
    ring
  have hEntropy' :
      -(((1 + x) / 2) * Real.log ((1 + x) / 2)) -
          (((1 - x) / 2) * Real.log ((1 - x) / 2)) =
        Real.log 2 - bernoulliCramerRateFunction x := by
    simpa using hEntropy
  simpa [hEntropy'] using hRaw.congr' hRewrite.symm

/-- Helper for Theorem 23.1: after isolating the endpoint `x = 1`, the strict-interior choose-tail
logarithm is the only remaining asymptotic input. -/
private theorem upperTailChooseTailLog_tendstoRate {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Tendsto
      (fun n : ℕ ↦
        ENNReal.log
            (((2 : ENNReal) ^ n)⁻¹ *
              Finset.sum (Finset.Icc (Nat.ceil (((n : ℝ) * (1 + x)) / 2)) n)
                (fun k ↦ (Nat.choose n k : ENNReal))) /
          n)
      atTop
      (𝓝 (-rademacherCramerRateFunction x)) := by
  let a : ℕ → ℕ := fun n ↦ Nat.ceil (((n : ℝ) * (1 + x)) / 2)
  let first : ℕ → ENNReal := fun n ↦ (Nat.choose n (a n) : ENNReal)
  let tail : ℕ → ENNReal := fun n ↦
    Finset.sum (Finset.Icc (a n) n) (fun k ↦ (Nat.choose n k : ENNReal))
  let lowerE : ℕ → EReal := fun n ↦ ENNReal.log (((2 : ENNReal) ^ n)⁻¹ * first n) / n
  let upperE : ℕ → EReal := fun n ↦
    ENNReal.log (((2 : ENNReal) ^ n)⁻¹ * ((n + 1 : ENNReal) * first n)) / n
  have hInterior :
      ∀ᶠ n : ℕ in atTop, 0 < a n ∧ a n < n := by
    simpa [a] using upperTailIndex_eventually_strictInterior hx0 hx1
  have hChooseLimit :
      Tendsto (fun n : ℕ ↦ Real.log (Nat.choose n (a n)) / n) atTop
        (𝓝 (Real.log 2 - bernoulliCramerRateFunction x)) := by
    simpa [a] using upperTailLogChoose_tendstoEntropy hx0 hx1
  have hErrorLimit :
      Tendsto (fun n : ℕ ↦ Real.log (n + 1) / n) atTop (𝓝 0) := by
    have hBase :
        Tendsto (fun n : ℕ ↦ Real.log n / n) atTop (𝓝 0) := by
      -- Proof comment: logarithmic growth is negligible compared with the linear scale `n`.
      simpa [pow_one] using
        (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
          tendsto_natCast_atTop_atTop
    have hMain :
        Tendsto (fun n : ℕ ↦ Real.log (n + 1) / (n + 1 : ℝ)) atTop (𝓝 0) := by
      -- Proof comment: `log (n + 1)` is still sublinear, even after shifting the index by one.
      refine (hBase.comp (tendsto_add_atTop_nat 1)).congr' ?_
      filter_upwards with n
      simp [Function.comp, Nat.cast_add]
    have hRatio :
        Tendsto (fun n : ℕ ↦ ((n + 1 : ℝ) / n)) atTop (𝓝 (1 : ℝ)) := by
      have hRatioEq :
          (fun n : ℕ ↦ ((n + 1 : ℝ) / n)) =ᶠ[atTop] fun n : ℕ ↦ 1 + 1 / (n : ℝ) := by
        filter_upwards [Filter.eventually_ge_atTop 1] with n hn
        have hn0 : (n : ℝ) ≠ 0 := by
          exact_mod_cast Nat.ne_of_gt (Nat.succ_le_iff.mp hn)
        field_simp [hn0]
      have hSum :
          Tendsto (fun n : ℕ ↦ (1 : ℝ) + 1 / (n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
        simpa using
          (tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)) :
            Tendsto (fun n : ℕ ↦ (1 : ℝ) + 1 / (n : ℝ)) atTop (𝓝 ((1 : ℝ) + 0)))
      exact hSum.congr' hRatioEq.symm
    have hRewrite :
        (fun n : ℕ ↦ Real.log (n + 1) / n) =
          fun n : ℕ ↦ (Real.log (n + 1) / (n + 1 : ℝ)) * ((n + 1 : ℝ) / n) := by
      funext n
      by_cases hn : n = 0
      · subst hn
        norm_num
      · have hn0 : (n : ℝ) ≠ 0 := by
          exact_mod_cast Nat.ne_of_gt (Nat.pos_iff_ne_zero.mpr hn)
        field_simp [hn0]
    simpa [hRewrite] using hMain.mul hRatio
  have hlogTwo : ENNReal.log (2 : ENNReal) = (Real.log 2 : EReal) := by
    rw [ENNReal.log_pos_real]
    · norm_num
    · norm_num
    · simp
  have hLowerEq :
      lowerE =ᶠ[atTop]
        fun n : ℕ ↦ ((-Real.log 2 + Real.log (Nat.choose n (a n)) / n : ℝ) : EReal) := by
    -- Proof comment: once the first binomial coefficient is strictly positive, the logarithm of
    -- the `2^{-n}`-weighted first term is exactly `-log 2 + log choose / n`.
    filter_upwards [hInterior] with n hn
    have hnPos : 0 < n := lt_trans hn.1 hn.2
    have hnNonneg : (0 : EReal) ≤ n := by
      exact_mod_cast Nat.zero_le n
    have hnBot : (n : EReal) ≠ ⊥ := by
      simpa using (EReal.coe_ne_bot (n : ℝ))
    have hnTop : (n : EReal) ≠ ⊤ := by
      simpa using (EReal.coe_ne_top (n : ℝ))
    have hnZero : (n : EReal) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hnPos
    have hChoosePos : 0 < Nat.choose n (a n) := Nat.choose_pos (Nat.le_of_lt hn.2)
    have hChooseLog :
        ENNReal.log (first n) = (Real.log (Nat.choose n (a n)) : EReal) := by
      calc
        ENNReal.log (first n) = (Real.log (ENNReal.toReal (first n)) : EReal) := by
          exact ENNReal.log_pos_real
            (by simpa [first] using
              (show ((Nat.choose n (a n) : ENNReal) ≠ 0) from by
                exact_mod_cast Nat.ne_of_gt hChoosePos))
            (by simp [first])
        _ = (Real.log (Nat.choose n (a n)) : EReal) := by
          simp [first]
    have hNegMul :
        -((n : EReal) * (Real.log 2 : EReal)) = (-(Real.log 2 : EReal)) * n := by
      rw [neg_mul, mul_comm]
    have hDivCast :
        ((Real.log (Nat.choose n (a n)) : EReal) / n) =
          ((Real.log (Nat.choose n (a n)) / n : ℝ) : EReal) := by
      rfl
    dsimp [lowerE, first]
    rw [ENNReal.log_mul_add, ENNReal.log_inv, ENNReal.log_pow, hlogTwo, hChooseLog,
      EReal.add_div_of_nonneg_right hnNonneg, hNegMul,
      ← EReal.mul_div (-(Real.log 2 : EReal)) (n : EReal) (n : EReal),
      EReal.div_self hnBot hnTop hnZero, mul_one, hDivCast]
  have hUpperEq :
      upperE =ᶠ[atTop]
        fun n : ℕ ↦
          ((-Real.log 2 + Real.log (Nat.choose n (a n)) / n + Real.log (n + 1) / n : ℝ) : EReal) :=
      by
    -- Proof comment: the logarithm of the upper squeeze term contributes one extra factor
    -- `log (n + 1) / n`.
    filter_upwards [hInterior] with n hn
    have hnPos : 0 < n := lt_trans hn.1 hn.2
    have hnNonneg : (0 : EReal) ≤ n := by
      exact_mod_cast Nat.zero_le n
    have hnBot : (n : EReal) ≠ ⊥ := by
      simpa using (EReal.coe_ne_bot (n : ℝ))
    have hnTop : (n : EReal) ≠ ⊤ := by
      simpa using (EReal.coe_ne_top (n : ℝ))
    have hnZero : (n : EReal) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hnPos
    have hChoosePos : 0 < Nat.choose n (a n) := Nat.choose_pos (Nat.le_of_lt hn.2)
    have hChooseLog :
        ENNReal.log (first n) = (Real.log (Nat.choose n (a n)) : EReal) := by
      calc
        ENNReal.log (first n) = (Real.log (ENNReal.toReal (first n)) : EReal) := by
          exact ENNReal.log_pos_real
            (by simpa [first] using
              (show ((Nat.choose n (a n) : ENNReal) ≠ 0) from by
                exact_mod_cast Nat.ne_of_gt hChoosePos))
            (by simp [first])
        _ = (Real.log (Nat.choose n (a n)) : EReal) := by
          simp [first]
    have hLenLog :
        ENNReal.log (n + 1 : ENNReal) = (Real.log (((n + 1 : ℕ) : ℝ)) : EReal) := by
      have hLenToReal : ENNReal.toReal (n + 1 : ENNReal) = ((n + 1 : ℕ) : ℝ) := by
        simpa using (ENNReal.toReal_natCast (n + 1))
      calc
        ENNReal.log (n + 1 : ENNReal) = (Real.log (ENNReal.toReal (n + 1 : ENNReal)) : EReal) := by
          exact ENNReal.log_pos_real (by simp) (by simp)
        _ = (Real.log (((n + 1 : ℕ) : ℝ)) : EReal) := by
          rw [hLenToReal]
    have hNegMul :
        -((n : EReal) * (Real.log 2 : EReal)) = (-(Real.log 2 : EReal)) * n := by
      rw [neg_mul, mul_comm]
    have hDivChoose :
        ((Real.log (Nat.choose n (a n)) : EReal) / n) =
          ((Real.log (Nat.choose n (a n)) / n : ℝ) : EReal) := by
      rfl
    have hDivLen :
        ((Real.log (((n + 1 : ℕ) : ℝ)) : EReal) / n) =
          ((Real.log (((n + 1 : ℕ) : ℝ)) / n : ℝ) : EReal) := by
      rfl
    dsimp [upperE, first]
    rw [ENNReal.log_mul_add, ENNReal.log_inv, ENNReal.log_pow, hlogTwo, ENNReal.log_mul_add,
      hLenLog, hChooseLog, EReal.add_div_of_nonneg_right hnNonneg,
      EReal.add_div_of_nonneg_right hnNonneg, hNegMul,
      ← EReal.mul_div (-(Real.log 2 : EReal)) (n : EReal) (n : EReal),
      EReal.div_self hnBot hnTop hnZero, mul_one, hDivLen, hDivChoose]
    simp [add_assoc, add_left_comm, add_comm]
  have hLowerLimit :
      Tendsto lowerE atTop (𝓝 ((-bernoulliCramerRateFunction x : ℝ) : EReal)) := by
    have hLowerReal :
        Tendsto
          (fun n : ℕ ↦ -Real.log 2 + Real.log (Nat.choose n (a n)) / n)
          atTop
          (𝓝 (-bernoulliCramerRateFunction x)) := by
      convert tendsto_const_nhds.add hChooseLimit using 1 <;> ring
    exact (EReal.tendsto_coe.2 hLowerReal).congr' hLowerEq.symm
  have hUpperLimit :
      Tendsto upperE atTop (𝓝 ((-bernoulliCramerRateFunction x : ℝ) : EReal)) := by
    have hUpperReal :
        Tendsto
          (fun n : ℕ ↦ -Real.log 2 + Real.log (Nat.choose n (a n)) / n + Real.log (n + 1) / n)
          atTop
          (𝓝 (-bernoulliCramerRateFunction x)) := by
      convert (tendsto_const_nhds.add hChooseLimit).add hErrorLimit using 1 <;> ring
    exact (EReal.tendsto_coe.2 hUpperReal).congr' hUpperEq.symm
  have hLowerLe :
      ∀ᶠ n : ℕ in atTop,
        lowerE n ≤
          ENNReal.log (((2 : ENNReal) ^ n)⁻¹ * tail n) / n := by
    -- Proof comment: the first term of the tail is a lower bound for the whole tail.
    filter_upwards with n
    have hFirstLe : first n ≤ tail n := (binomialTailFirstTerm_bounds hx0 n).1
    have hScaled :
        ((2 : ENNReal) ^ n)⁻¹ * first n ≤ ((2 : ENNReal) ^ n)⁻¹ * tail n :=
      mul_le_mul_left' hFirstLe (((2 : ENNReal) ^ n)⁻¹)
    exact EReal.div_le_div_right_of_nonneg (by positivity) (ENNReal.log_le_log hScaled)
  have hUpperLe :
      ∀ᶠ n : ℕ in atTop,
        ENNReal.log (((2 : ENNReal) ^ n)⁻¹ * tail n) / n ≤ upperE n := by
    -- Proof comment: the full tail is bounded above by `(n + 1)` times its first term.
    filter_upwards with n
    have hTailLe :
        tail n ≤ (n + 1 : ENNReal) * first n := (binomialTailFirstTerm_bounds hx0 n).2
    have hScaled :
        ((2 : ENNReal) ^ n)⁻¹ * tail n ≤ ((2 : ENNReal) ^ n)⁻¹ * ((n + 1 : ENNReal) * first n) :=
      mul_le_mul_left' hTailLe (((2 : ENNReal) ^ n)⁻¹)
    exact EReal.div_le_div_right_of_nonneg (by positivity) (ENNReal.log_le_log hScaled)
  have hCore :
      Tendsto
        (fun n : ℕ ↦ ENNReal.log (((2 : ENNReal) ^ n)⁻¹ * tail n) / n)
        atTop
        (𝓝 ((-bernoulliCramerRateFunction x : ℝ) : EReal)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hLowerLimit hUpperLimit hLowerLe hUpperLe
  have hRate :
      ((-bernoulliCramerRateFunction x : ℝ) : EReal) = -rademacherCramerRateFunction x := by
    have habs : |x| ≤ 1 := by
      rw [abs_of_nonneg hx0]
      linarith
    simpa using congrArg Neg.neg (rademacherCramerRateFunction_of_abs_le_one habs).symm
  simpa [tail, a, hRate] using hCore

-- Proof sketch: combine the i.i.d. Rademacher hypotheses with the exact binomial-tail formula for
-- `partialSum X n`, estimate the tail by the maximal binomial coefficient, and then apply
-- Stirling's formula to identify the exponential rate as `rademacherCramerRateFunction`.
/-- Theorem 23.1: for an i.i.d. Rademacher sequence, the upper-tail probabilities of the partial
sums satisfy Cramér's theorem. Using the `0`-based partial sums `partialSum X n = X₀ + ⋯ + Xₙ₋₁`,
the logarithmic asymptotic of `P[Sₙ ≥ x n]` converges in `EReal` to the negative of the
Rademacher Cramér rate function. -/
theorem rademacher_partialSum_largeDeviation_upperTail
    (hX_iid : IsIID X P)
    (hX0_law :
      HasLaw (X 0) rademacherTwoPointLaw P)
    {x : ℝ} (hx : 0 ≤ x) :
    Tendsto
      (fun n : ℕ ↦ ENNReal.log (P {ω | x * n ≤ partialSum X n ω}) / n)
      atTop
      (𝓝 (-rademacherCramerRateFunction x)) := by
  letI : IsProbabilityMeasure P := hX0_law.isProbabilityMeasure
  have hSigns :
      ∀ n : ℕ, ∀ᵐ ω ∂P, X n ω = -1 ∨ X n ω = 1 := by
    -- Proof comment: every coordinate is supported on `{-1, 1}`, which is the pathwise input
    -- needed for the trivial `x > 1` branch and for the later Boolean-cube counting step.
    intro n
    exact rademacherCoordinate_ae_eq_pm_one (P := P) (X := X) hX_iid hX0_law n
  have hPartialUpper :
      ∀ n : ℕ, ∀ᵐ ω ∂P, partialSum X n ω ≤ n := by
    -- Proof comment: the coordinatewise support control upgrades inductively to a bound on every
    -- finite partial sum.
    exact partialSum_le_prefixLength_ae (P := P) (X := X) hSigns
  have hChooseTail :
      ∀ n : ℕ,
        P {ω | x * n ≤ partialSum X n ω} =
          ((2 : ENNReal) ^ n)⁻¹ *
            Finset.sum (Finset.Icc (Nat.ceil (((n : ℝ) * (1 + x)) / 2)) n)
              (fun k ↦ (Nat.choose n k : ENNReal)) := by
    -- Proof comment: this is the exact discrete source formula after transporting the event to the
    -- uniform Boolean cube.
    intro n
    exact rademacherUpperTail_eq_chooseTail (P := P) (X := X) hX_iid hX0_law n hx
  by_cases hx1 : x ≤ 1
  · by_cases hxeq : x = 1
    · subst hxeq
      -- Proof comment: at the endpoint `x = 1`, only the single all-ones path contributes, so the
      -- probability is exactly `2^{-n}`.
      have hRateOne : -rademacherCramerRateFunction (1 : ℝ) = (-(Real.log 2 : EReal)) := by
        rw [rademacherCramerRateFunction_of_abs_le_one (x := (1 : ℝ)) (by norm_num),
          bernoulliCramerRateFunction_one]
      have hEventually :
          (fun n : ℕ ↦ ENNReal.log (P {ω | (1 : ℝ) * n ≤ partialSum X n ω}) / n) =ᶠ[atTop]
            fun _ : ℕ ↦ (-(Real.log 2 : EReal)) := by
        filter_upwards [Filter.eventually_ge_atTop 1] with n hn
        have hn_pos : 0 < n := Nat.succ_le_iff.mp hn
        have hceilReal : ((((n : ℝ) * (1 + (1 : ℝ))) / 2 : ℝ)) = n := by
          ring
        have hceil : Nat.ceil (((n : ℝ) * (1 + (1 : ℝ))) / 2) = n := by
          simpa [hceilReal] using (Nat.ceil_natCast n)
        have hlogTwo : ENNReal.log (2 : ENNReal) = (Real.log 2 : EReal) := by
          rw [ENNReal.log_pos_real]
          · norm_num
          · norm_num
          · simp
        have hn_bot : (n : EReal) ≠ ⊥ := by
          simpa using (EReal.coe_ne_bot (n : ℝ))
        have hn_top : (n : EReal) ≠ ⊤ := by
          simpa using (EReal.coe_ne_top (n : ℝ))
        have hn_zero : (n : EReal) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt hn_pos)
        have hnegMul :
            -((n : EReal) * (Real.log 2 : EReal)) = (-(Real.log 2 : EReal)) * n := by
          rw [neg_mul, mul_comm]
        -- Proof comment: once the choose tail collapses to the singleton coefficient
        -- `Nat.choose n n = 1`, the logarithm is exactly `-n * log 2`, and dividing by `n`
        -- cancels the prefactor.
        rw [hChooseTail n, hceil, Finset.Icc_self, Finset.sum_singleton, Nat.choose_self]
        simp only [Nat.cast_one, ENNReal.coe_one, mul_one]
        rw [ENNReal.log_inv, ENNReal.log_pow, hlogTwo, hnegMul,
          ← EReal.mul_div (-(Real.log 2 : EReal)) (n : EReal) (n : EReal),
          EReal.div_self hn_bot hn_top hn_zero, mul_one]
      exact
        (show Tendsto (fun _ : ℕ ↦ (-(Real.log 2 : EReal))) atTop
            (𝓝 (-rademacherCramerRateFunction (1 : ℝ))) by
          simpa [hRateOne] using
            (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (-(Real.log 2 : EReal))) atTop
              (𝓝 (-(Real.log 2 : EReal))))).congr' hEventually.symm
    · have hxlt1 : x < 1 := lt_of_le_of_ne hx1 hxeq
      refine (upperTailChooseTailLog_tendstoRate (x := x) hx hxlt1).congr' ?_
      filter_upwards with n
      rw [hChooseTail n]
  · have hx_gt_one : 1 < x := lt_of_not_ge hx1
    -- Proof comment: for `x > 1`, the pathwise bound `partialSum X n ≤ n` makes the upper-tail
    -- event eventually empty, so the logarithmic scale is `⊥`.
    have hRateAboveOne : -rademacherCramerRateFunction x = (⊥ : EReal) := by
      have habs : ¬ |x| ≤ 1 := by
        rw [abs_of_nonneg hx]
        linarith
      simp [rademacherCramerRateFunction, habs]
    have hEventually :
        (fun n : ℕ ↦ ENNReal.log (P {ω | x * n ≤ partialSum X n ω}) / n) =ᶠ[atTop]
          fun _ : ℕ ↦ (⊥ : EReal) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hn_pos : 0 < n := Nat.succ_le_iff.mp hn
      have hStrict : (n : ℝ) < x * n := by
        have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn_pos
        nlinarith
      have hUpperAe : ∀ᵐ ω ∂P, ¬ (n : ℝ) < partialSum X n ω := by
        filter_upwards [hPartialUpper n] with ω hω
        linarith
      have hUpperNull : P {ω | (n : ℝ) < partialSum X n ω} = 0 := by
        simpa using (ae_iff.1 hUpperAe)
      have hSubset :
          {ω | x * n ≤ partialSum X n ω} ⊆ {ω | (n : ℝ) < partialSum X n ω} := by
        intro ω hω
        exact lt_of_lt_of_le hStrict hω
      have hProbZero : P {ω | x * n ≤ partialSum X n ω} = 0 :=
        measure_mono_null hSubset hUpperNull
      -- Proof comment: after the event measure is zero, the logarithm is `⊥`, and division by the
      -- positive length `n` leaves `⊥`.
      rw [hProbZero, ENNReal.log_zero]
      exact EReal.bot_div_of_pos_ne_top
        (by exact_mod_cast hn_pos)
        (by simpa using (EReal.coe_ne_top (n : ℝ)))
    exact
      (show Tendsto (fun _ : ℕ ↦ (⊥ : EReal)) atTop (𝓝 (-rademacherCramerRateFunction x)) by
        simpa [hRateAboveOne] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (⊥ : EReal)) atTop (𝓝 (⊥ : EReal)))).congr'
        hEventually.symm

end ProbabilityTheory

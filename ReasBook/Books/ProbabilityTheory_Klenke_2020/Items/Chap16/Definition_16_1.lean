/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_32

open scoped MeasureTheory
open MeasureTheory ProbabilityTheory
open MeasureTheory.ProbabilityMeasure

noncomputable section

universe u v

/- Definition 16.1 is organized around a canonical owner and two source-facing views.

- `IsCFP` is the source-facing notion of a characteristic function on `ℝ`.
- `MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible` is the `core/canonical` owner
  predicate on laws in an additive measurable space.
- `IsInfinitelyDivisibleCFP` and `IsInfinitelyDivisibleRandomVariable` are the two
  `bridge/view` formulations used in the chapter.

The refinements below keep the source-facing bridge notions, but route their owner-side API
through canonical `ProbabilityMeasure` constructions instead of parallel local wrappers.
-/

/-- A complex-valued function on `ℝ` is a characteristic function of a probability law when it is
the Fourier transform of some probability measure on `ℝ`. -/
def IsCFP (φ : ℝ → ℂ) : Prop :=
  ∃ μ : ProbabilityMeasure ℝ, charFun μ = φ

/-- A characteristic function on `ℝ` is infinitely divisible if every positive integer root can
again be realized as the characteristic function of a probability law on `ℝ`. -/
def IsInfinitelyDivisibleCFP (φ : ℝ → ℂ) : Prop :=
  ∀ n : ℕ+, ∃ φn : ℝ → ℂ,
    IsCFP φn ∧ φ = fun t ↦ φn t ^ (n : ℕ)

namespace MeasureTheory.ProbabilityMeasure

/-- The characteristic function of a probability law on `ℝ` is a CFP. -/
theorem isCFP_charFun (μ : ProbabilityMeasure ℝ) :
    IsCFP (charFun μ) :=
  ⟨μ, rfl⟩

/-- The characteristic function of the `n`th convolution power is the `n`th power of the
underlying characteristic function. -/
theorem charFun_pow (μ : ProbabilityMeasure ℝ) (n : ℕ) :
    charFun ((μ ^ n : ProbabilityMeasure ℝ) : Measure ℝ) = fun t ↦ charFun μ t ^ n := by
  induction n with
  | zero =>
      -- Proof comment: the zeroth convolution power is `δ₀`, whose characteristic function is `1`.
      funext t
      simp [ProbabilityMeasure.one_eq_diracProba, MeasureTheory.diracProba]
  | succ n ih =>
      -- Proof comment: one more convolution factor contributes one more multiplicative
      -- characteristic-function factor.
      funext t
      calc
        charFun ((μ ^ (n + 1) : ProbabilityMeasure ℝ) : Measure ℝ) t
            = charFun ((((μ ^ n : ProbabilityMeasure ℝ) : Measure ℝ)) ∗ (μ : Measure ℝ)) t := by
                simp [pow_succ]
        _ = charFun (((μ ^ n : ProbabilityMeasure ℝ) : Measure ℝ)) t *
              charFun (μ : Measure ℝ) t := by
              simpa using
                (MeasureTheory.charFun_conv
                  (μ := (((μ ^ n : ProbabilityMeasure ℝ) : Measure ℝ)))
                  (ν := (μ : Measure ℝ)) t)
        _ = charFun (μ : Measure ℝ) t ^ n * charFun (μ : Measure ℝ) t := by
              rw [ih]
        _ = charFun (μ : Measure ℝ) t ^ (n + 1) := by
              simp [pow_succ]

variable {E : Type u} [AddMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]

/-- Definition 16.1: a probability law on an additive measurable space is infinitely divisible if,
for every positive integer `n`, it admits an `n`th additive convolution root. The source-facing
characteristic-function and random-variable formulations below specialize this owner notion to
laws on `ℝ`. -/
class IsInfinitelyDivisible (μ : ProbabilityMeasure E) : Prop where
  /-- For each positive integer `n`, there is a probability law whose `n`th convolution power is
  `μ`. -/
  exists_root : ∀ n : ℕ+, ∃ ν : ProbabilityMeasure E, ν ^ (n : ℕ) = μ

/-- Helper for Definition 16.1: the `n`th additive convolution power of `diracProba a` on `ℝ`
is the Dirac law at the `n`-fold sum `n • a`. -/
private lemma diracProbaPowEqReal (a : ℝ) :
    ∀ m : ℕ, (diracProba a : ProbabilityMeasure ℝ) ^ m = diracProba (m • a)
  | 0 => by
      -- Proof comment: the zeroth convolution power is the convolution unit `δ₀`.
      simp
  | m + 1 => by
      -- Proof comment: convolving once more with `δ_a` adds one more copy of `a`.
      rw [pow_succ, diracProbaPowEqReal a m]
      apply ProbabilityMeasure.toMeasure_injective
      have hdirac :
          (Measure.dirac (m • a) : Measure ℝ) ∗ Measure.dirac a =
            Measure.dirac ((m • a) + a) :=
        Measure.dirac_conv_dirac (m • a) a
      calc
        (diracProba (m • a) : Measure ℝ) ∗ (diracProba a : Measure ℝ)
            = Measure.dirac ((m • a) + a) := by
                rw [MeasureTheory.diracProba, MeasureTheory.diracProba]
                exact hdirac
        _ = (diracProba ((m + 1) • a) : Measure ℝ) := by
              rw [MeasureTheory.diracProba]
              have hmul : (m • a) + a = (m + 1) • a := by
                rw [nsmul_eq_mul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
                ring_nf
              exact congrArg Measure.dirac hmul

-- Proof sketch: for `δ_x`, take the `n`th root `δ_(x / n)` and use the convolution-monoid power
-- together with the behavior of convolution on Dirac masses.
/-- Every Dirac probability measure on `ℝ` is infinitely divisible. -/
instance diracProba_isInfinitelyDivisible (x : ℝ) :
    IsInfinitelyDivisible (diracProba x) where
  exists_root n := by
    refine ⟨diracProba (x / (n : ℝ)), ?_⟩
    have hn : (n : ℝ) ≠ 0 := by
      exact_mod_cast n.ne_zero
    -- Proof comment: the explicit root `δ_(x / n)` collapses to `δ_x` after `n` convolutions.
    rw [diracProbaPowEqReal]
    congr 1
    simp [nsmul_eq_mul, div_eq_mul_inv, hn, mul_left_comm]

-- Proof sketch: choose an `n`th convolution root from `exists_root`, then identify the
-- characteristic function of its convolution power with the `n`th pointwise power of the root
-- characteristic function using `charFun_pow`.
/-- The characteristic function of an infinitely divisible probability law is infinitely divisible
in the characteristic-function sense. -/
theorem charFun_isInfinitelyDivisible {μ : ProbabilityMeasure ℝ} (hμ : IsInfinitelyDivisible μ) :
    IsInfinitelyDivisibleCFP (charFun μ) := by
  intro n
  rcases hμ.exists_root n with ⟨ν, hν⟩
  refine ⟨charFun ν, isCFP_charFun ν, ?_⟩
  -- Proof comment: pass the chosen convolution root through `charFun_pow`.
  calc
    charFun μ = charFun (((ν ^ (n : ℕ) : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ) :
      Measure ℝ) := by
        rw [← hν]
    _ = fun t ↦ charFun ν t ^ (n : ℕ) := charFun_pow ν (n : ℕ)

end MeasureTheory.ProbabilityMeasure

section RandomVariable

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [AddCommMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]
variable (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → E)

/-- Helper for Definition 16.1: the law of a finite sum of independent copies of a law `ν`
is the corresponding convolution power `ν ^ s.card`. -/
private lemma hasLaw_finsetSumPow
    {ι : Type*} {Ω' : Type*} [MeasurableSpace Ω']
    (P' : ProbabilityMeasure Ω') (ν : ProbabilityMeasure E)
    (Y : ι → Ω' → E) (hY_meas : ∀ i, Measurable (Y i))
    (hY_law : ∀ i, HasLaw (Y i) (ν : Measure E) P') (hY_indep : iIndepFun Y P') :
    ∀ s : Finset ι,
      HasLaw (fun ω ↦ ∑ i ∈ s, Y i ω)
        (((ν ^ s.card : ProbabilityMeasure E) : ProbabilityMeasure E) : Measure E) P' := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      -- Proof comment: the empty sum is constantly `0`, whose law is the convolution unit `δ₀`.
      refine ProbabilityTheory.HasLaw.mk aemeasurable_const ?_
      simp [ProbabilityMeasure.one_eq_diracProba, MeasureTheory.diracProba]
  | @insert i s hi ih =>
      let S : Ω' → E := fun ω ↦ ∑ j ∈ s, Y j ω
      have hSumEqS : (∑ j ∈ s, Y j) = S := by
        funext ω
        simp [S, Finset.sum_apply]
      have hsum :
          HasLaw S
            (((ν ^ s.card : ProbabilityMeasure E) : ProbabilityMeasure E) : Measure E) P' := by
        simpa [S] using ih
      have hindepSum :
          IndepFun (∑ j ∈ s, Y j) (Y i) P' := by
        simpa using hY_indep.indepFun_finset_sum_of_notMem hY_meas hi
      have hindep :
          IndepFun S (Y i) P' := by
        exact hSumEqS ▸ hindepSum
      have hstep :
          HasLaw
            (fun ω ↦ S ω + Y i ω)
            ((((ν ^ s.card : ProbabilityMeasure E) : ProbabilityMeasure E) : Measure E).conv
              (ν : Measure E))
            P' := by
        simpa [S, Pi.add_apply] using hindep.hasLaw_add hsum (hY_law i)
      -- Proof comment: the inserted summand contributes one more convolution factor.
      simpa [S, Finset.sum_insert hi, Finset.sum_apply, Pi.add_apply, pow_succ,
        Finset.card_insert_of_notMem hi, add_comm] using hstep

/-- Helper for Definition 16.1: the sum of `n` i.i.d. copies of a law `ν` has law `ν ^ n`. -/
private lemma iidSum_hasLawPow
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : ProbabilityMeasure Ω')
    (ν : ProbabilityMeasure E) (n : ℕ+) (Y : Fin n → Ω' → E)
    (hY_meas : ∀ i, Measurable (Y i))
    (hY_law : ∀ i, HasLaw (Y i) (ν : Measure E) P') (hY_indep : iIndepFun Y P') :
    HasLaw (fun ω ↦ ∑ i, Y i ω) (((ν ^ (n : ℕ) : ProbabilityMeasure E) : Measure E)) P' := by
  -- Proof comment: specialize the finite-set convolution-power lemma to `Finset.univ`.
  simpa using hasLaw_finsetSumPow P' ν Y hY_meas hY_law hY_indep Finset.univ

/-- An additive measurable-space-valued random variable is infinitely divisible if, for every
positive integer `n`, its law is the law of a sum of `n` i.i.d. random variables on some
probability space. -/
def IsInfinitelyDivisibleRandomVariable : Prop :=
  ∀ n : ℕ+, ∃ Ω' : Type (max u v), ∃ _ : MeasurableSpace Ω',
    ∃ P' : ProbabilityMeasure Ω', ∃ ν : ProbabilityMeasure E,
      ∃ Y : Fin n → Ω' → E,
        (∀ i, Measurable (Y i)) ∧
          (∀ i, HasLaw (Y i) ν P') ∧
          iIndepFun Y P' ∧
          IdentDistrib X (fun ω ↦ ∑ i, Y i ω) P P'

-- Proof sketch: one direction pushes the i.i.d. decomposition to the law of `X`; the other
-- direction uses `ProbabilityTheory.exists_iid` to realize each convolution root on a probability
-- space and then sums the coordinate family.
/-- Infinite divisibility of an additive measurable-space-valued random variable is equivalent to
infinite divisibility of its law as a probability measure on its value space. -/
theorem isInfinitelyDivisibleRandomVariable_iff_law_isInfinitelyDivisible
    (hX : Measurable X) :
    IsInfinitelyDivisibleRandomVariable P X ↔
      IsInfinitelyDivisible (ProbabilityMeasure.map ⟨P, inferInstance⟩ hX.aemeasurable) := by
  let μX : ProbabilityMeasure E := ProbabilityMeasure.map ⟨P, inferInstance⟩ hX.aemeasurable
  constructor
  · intro hInfDivX
    refine (show IsInfinitelyDivisible μX from ?_)
    constructor
    intro n
    rcases hInfDivX n with ⟨Ω', _, P', ν, Y, hY_meas, hY_law, hY_indep, hIdent⟩
    refine ⟨ν, ?_⟩
    let hSumLaw := iidSum_hasLawPow (P' := P') (ν := ν) n Y hY_meas hY_law hY_indep
    -- Proof comment: the prescribed i.i.d. decomposition identifies the law of `X` with `ν ^ n`.
    apply ProbabilityMeasure.toMeasure_injective
    calc
      ((ν ^ (n : ℕ) : ProbabilityMeasure E) : Measure E)
          = Measure.map (fun ω ↦ ∑ i, Y i ω) P' := by
              symm
              exact hSumLaw.map_eq
      _ = Measure.map X P := by
            symm
            exact hIdent.map_eq
      _ = (μX : Measure E) := by
            simp [μX, ProbabilityMeasure.toMeasure_map]
  · intro hμ
    have hμ' : IsInfinitelyDivisible μX := by
      simpa [μX] using hμ
    intro n
    rcases hμ'.exists_root n with ⟨ν, hpow⟩
    rcases ProbabilityTheory.exists_iid (ULift.{u} (Fin n)) ((ν : Measure E)) with
      ⟨Ω', _, P', Ylift, hYlift_meas, hYlift_law, hYlift_indep, hPprob⟩
    let P'' : ProbabilityMeasure Ω' := ⟨P', hPprob⟩
    let Y : Fin n → Ω' → E := fun i ω ↦ Ylift ⟨i⟩ ω
    have hY_meas : ∀ i, Measurable (Y i) := by
      intro i
      simpa [Y] using hYlift_meas ⟨i⟩
    have hY_law' : ∀ i, HasLaw (Y i) (ν : Measure E) P'' := by
      intro i
      simpa [P'', Y] using hYlift_law ⟨i⟩
    have hY_indep' : iIndepFun Y P'' := by
      simpa [P'', Y] using
        hYlift_indep.precomp (g := fun i : Fin n ↦ (⟨i⟩ : ULift.{u} (Fin n)))
          (fun _ _ hij => by simpa using hij)
    refine ⟨Ω', inferInstance, P'', ν, Y, hY_meas, ?_, ?_, ?_⟩
    · -- Proof comment: the realized coordinate family has the requested common law.
      exact hY_law'
    · -- Proof comment: the i.i.d. structure survives bundling the ambient measure as a probability
      -- measure.
      exact hY_indep'
    · have hX_law : HasLaw X (μX : Measure E) P := by
        refine ProbabilityTheory.HasLaw.mk hX.aemeasurable ?_
        simp [μX, ProbabilityMeasure.toMeasure_map]
      let hSumPowLaw := iidSum_hasLawPow (P' := P'') (ν := ν) n Y hY_meas hY_law' hY_indep'
      have hSumLaw : HasLaw (fun ω ↦ ∑ i, Y i ω) (μX : Measure E) P'' := by
        refine ProbabilityTheory.HasLaw.mk (by fun_prop) ?_
        calc
          Measure.map (fun ω ↦ ∑ i, Y i ω) P''
              = ((ν ^ (n : ℕ) : ProbabilityMeasure E) : Measure E) := hSumPowLaw.map_eq
          _ = (μX : Measure E) := by
                simpa [μX, ProbabilityMeasure.toMeasure_map] using
                  congrArg (fun η : ProbabilityMeasure E ↦ (η : Measure E)) hpow
      -- Proof comment: both sides now have the same law `μX`, so they are identically
      -- distributed.
      exact ProbabilityTheory.HasLaw.identDistrib hX_law hSumLaw

end RandomVariable

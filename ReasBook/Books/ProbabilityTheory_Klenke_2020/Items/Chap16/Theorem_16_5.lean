/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Corollary_16_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Theorem_16_6

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

section

/-- Helper for Theorem 16.5: restrict a finite measure on `R \ {0}` to the punctured line. -/
noncomputable def puncturedIntensity (ν : FiniteMeasure ℝ) :
    FiniteMeasure {x : ℝ // x ≠ 0} :=
  (ν.restrict ({0}ᶜ : Set ℝ)).comap Subtype.val

/-- Helper for Theorem 16.5: mapping the punctured restriction back along `Subtype.val`
recovers the original finite measure restricted away from `0`. -/
theorem puncturedIntensity_map_subtypeVal (ν : FiniteMeasure ℝ) :
    (puncturedIntensity ν).map Subtype.val = ν.restrict ({0}ᶜ : Set ℝ) := by
  apply FiniteMeasure.toMeasure_injective
  -- Proof comment: `map` after `comap` along the subtype inclusion recovers the restricted
  -- measure.
  simpa [puncturedIntensity] using
    (map_comap_subtype_coe (s := ({0}ᶜ : Set ℝ)) (measurableSet_singleton (0 : ℝ)).compl
      (((ν : Measure ℝ).restrict ({0}ᶜ : Set ℝ))))

/-- Helper for Theorem 16.5: removing the atom at `0` from the intensity does not change the
compound-Poisson law. -/
theorem compoundPoissonMeasure_ignoreZeroAtom (ν : FiniteMeasure ℝ) :
    compoundPoissonMeasure ((puncturedIntensity ν).map Subtype.val) = compoundPoissonMeasure ν := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  let f : ℝ → ℂ := fun x ↦ Complex.exp (t * x * Complex.I) - 1
  have hfInt : Integrable f (μ := (ν : Measure ℝ)) := by
    refine Integrable.of_bound (by fun_prop) 2 ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      have hnormExp : ‖Complex.exp (t * x * Complex.I)‖ = 1 := by
        simpa using Complex.norm_exp_ofReal_mul_I (t * x)
      calc
        ‖f x‖ = ‖Complex.exp (t * x * Complex.I) - 1‖ := rfl
        _ ≤ ‖Complex.exp (t * x * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by
          rw [hnormExp]
          norm_num
  have hfIntCompl : Integrable f (μ := ((ν : Measure ℝ).restrict ({0}ᶜ : Set ℝ))) :=
    hfInt.mono_measure Measure.restrict_le_self
  have hfIntZero : Integrable f (μ := ((ν : Measure ℝ).restrict ({0} : Set ℝ))) :=
    hfInt.mono_measure Measure.restrict_le_self
  have hsplit :
      ((ν : Measure ℝ).restrict ({0}ᶜ : Set ℝ)) + ((ν : Measure ℝ).restrict ({0} : Set ℝ)) =
        (ν : Measure ℝ) := by
    simpa using
      (Measure.restrict_add_restrict_compl (μ := (ν : Measure ℝ))
        (s := ({0}ᶜ : Set ℝ)) ((measurableSet_singleton (0 : ℝ)).compl))
  have hsingleton :
      ∫ x, f x ∂((ν : Measure ℝ).restrict ({0} : Set ℝ)) = 0 := by
    rw [Measure.restrict_singleton, integral_smul_measure, integral_dirac]
    simp [f]
  rw [charFun_compoundPoissonMeasure, charFun_compoundPoissonMeasure,
    puncturedIntensity_map_subtypeVal]
  congr 1
  -- Proof comment: the Lévy exponent is unchanged because the integrand vanishes at the deleted
  -- atom.
  calc
    ∫ x, f x ∂((ν : Measure ℝ).restrict ({0}ᶜ : Set ℝ))
        = ∫ x, f x ∂((ν : Measure ℝ).restrict ({0}ᶜ : Set ℝ)) + 0 := by
            rw [add_zero]
    _ = ∫ x, f x ∂((ν : Measure ℝ).restrict ({0}ᶜ : Set ℝ)) +
          ∫ x, f x ∂((ν : Measure ℝ).restrict ({0} : Set ℝ)) := by
            rw [hsingleton]
    _ = ∫ x, f x ∂(((ν : Measure ℝ).restrict ({0}ᶜ : Set ℝ)) +
          ((ν : Measure ℝ).restrict ({0} : Set ℝ))) := by
            symm
            exact integral_add_measure hfIntCompl hfIntZero
    _ = ∫ x, f x ∂(ν : Measure ℝ) := by rw [hsplit]

/-- Helper for Theorem 16.5: scaling a probability law by `n` in the compound-Poisson intensity
turns its characteristic function into the centered exponential form. -/
theorem charFun_compoundPoissonMeasure_natSmulProbability
    (ρ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    charFun (compoundPoissonMeasure ((((n : NNReal) • ρ.toFiniteMeasure) : FiniteMeasure ℝ)) :
      Measure ℝ) t =
      Complex.exp ((n : ℂ) * (charFun (ρ : Measure ℝ) t - 1)) := by
  have hintegrable :
      Integrable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I)) (μ := (ρ : Measure ℝ)) := by
    refine Integrable.of_bound (by fun_prop) 1 ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      exact le_of_eq (by simpa using (Complex.norm_exp_ofReal_mul_I (t * x)))
  have hcentered :
      ∫ x, (Complex.exp (t * x * Complex.I) - 1) ∂(ρ : Measure ℝ) =
        charFun (ρ : Measure ℝ) t - 1 := by
    -- Proof comment: the nonconstant part is the characteristic function, and the constant part
    -- contributes the total mass `1`.
    rw [integral_sub hintegrable (integrable_const (1 : ℂ)), MeasureTheory.charFun_apply_real]
    simp
  rw [charFun_compoundPoissonMeasure]
  congr 1
  let c : ENNReal := (n : NNReal)
  change
    (∫ x, (Complex.exp (t * x * Complex.I) - 1) ∂
      (((((n : NNReal) • ρ.toFiniteMeasure) : FiniteMeasure ℝ) : Measure ℝ))) =
        (n : ℂ) * (charFun (ρ : Measure ℝ) t - 1)
  have hscaledMeasure :
      (((((n : NNReal) • ρ.toFiniteMeasure) : FiniteMeasure ℝ) : Measure ℝ)) = c •
        (ρ : Measure ℝ) := by
    rfl
  rw [hscaledMeasure, integral_smul_measure, hcentered]
  change ((c.toReal : ℂ) * (charFun (ρ : Measure ℝ) t - 1)) =
      (n : ℂ) * (charFun (ρ : Measure ℝ) t - 1)
  simp [c]

/-- Helper for Theorem 16.5: reindexing a `ℕ+`-sequence along `Nat.succPNat` preserves its
`atTop` limit. -/
private theorem tendstoPnatAtTopIffSuccPNat {β : Type*} [TopologicalSpace β]
    {f : ℕ+ → β} {l : Filter β} :
    Tendsto f atTop l ↔ Tendsto (fun n : ℕ ↦ f (Nat.succPNat n)) atTop l := by
  constructor
  · intro hf
    -- Proof comment: compose the `ℕ+`-indexed limit with the order isomorphism `ℕ ≃o ℕ+`.
    simpa [OrderIso.pnatIsoNat_symm_apply] using hf.comp OrderIso.pnatIsoNat.symm.tendsto_atTop
  · intro hf
    -- Proof comment: compose back with `PNat.natPred` to recover the original `ℕ+` indexing.
    have hcomp := hf.comp OrderIso.pnatIsoNat.tendsto_atTop
    convert hcomp using 1
    ext n
    simp [OrderIso.pnatIsoNat_apply]

/-- Helper for Theorem 16.5: a `ℕ+`-indexed CFP power approximation can be reindexed along
`Nat.toPNat'` to match the nat-indexed API used by Theorem 16.6. -/
private theorem existsNatIndexedCfpPowerApproximation
    {φ : ℝ → ℂ} {φs : ℕ+ → ℝ → ℂ}
    (hφs : ∀ n : ℕ+, IsCFP (φs n))
    (hpow : ∀ t, Tendsto (fun n : ℕ+ ↦ (φs n t) ^ (n : ℕ)) atTop (𝓝 (φ t))) :
    ∃ ψs : ℕ → ℝ → ℂ,
      (∀ n : ℕ, IsCFP (ψs n)) ∧
        ∀ t, Tendsto (fun n : ℕ ↦ (ψs n t) ^ n) atTop (𝓝 (φ t)) := by
  let ψs : ℕ → ℝ → ℂ := fun n ↦ φs (Nat.toPNat' n)
  refine ⟨ψs, ?_, ?_⟩
  · intro n
    -- Proof comment: the reindexing keeps the same positive-index witness at every nat index.
    simpa [ψs] using hφs (Nat.toPNat' n)
  · intro t
    have hshiftPNat :
        Tendsto
          (fun n : ℕ ↦ (φs (Nat.succPNat n) t) ^ ((Nat.succPNat n : ℕ+) : ℕ))
          atTop
          (𝓝 (φ t)) :=
      (tendstoPnatAtTopIffSuccPNat).1 (hpow t)
    have hshiftNat :
        Tendsto (fun n : ℕ ↦ (ψs (n + 1) t) ^ (n + 1)) atTop (𝓝 (φ t)) := by
      -- Proof comment: after shifting by one, `Nat.toPNat'` becomes exactly `Nat.succPNat`.
      simpa [ψs, PNat.toPNat'_coe (Nat.succ_pos _), Nat.succPNat_coe] using hshiftPNat
    -- Proof comment: a finite shift of a nat-indexed sequence does not change its `atTop` limit.
    exact (Filter.tendsto_add_atTop_iff_nat 1).1 hshiftNat

/-- Helper for Theorem 16.5: an infinitely divisible law on `R` is the weak limit of
compound-Poisson laws built from punctured finite intensities. -/
theorem exists_compoundPoissonApproximation_of_isInfinitelyDivisible
    {μ : ProbabilityMeasure ℝ} (hμ : ProbabilityMeasure.IsInfinitelyDivisible μ) :
    ∃ νs : ℕ → FiniteMeasure {x : ℝ // x ≠ 0},
      Tendsto (fun n ↦ compoundPoissonMeasure ((νs n).map Subtype.val)) atTop (𝓝 μ) := by
  classical
  have hchar0 : ContinuousAt (charFun (μ : Measure ℝ)) 0 := by
    simpa using (MeasureTheory.continuous_charFun (μ := (μ : Measure ℝ))).continuousAt
  rcases
      (isInfinitelyDivisibleCFP_iff_exists_charFun_pow_tendsto hchar0).1
        (ProbabilityMeasure.charFun_isInfinitelyDivisible hμ) with
    ⟨φsP, hφsP, hpowP⟩
  rcases existsNatIndexedCfpPowerApproximation hφsP hpowP with ⟨φs, hφs, hpow⟩
  rcases
      (cfp_power_limit_iff_linearized_limit (φs := φs) (hφs := hφs)).1
        ⟨charFun (μ : Measure ℝ), hpow, hchar0⟩ with
    ⟨ψ, hlin, _⟩
  have hchar_eq :
      charFun (μ : Measure ℝ) = fun t : ℝ ↦ Complex.exp (ψ t) :=
    cfp_power_limit_eq_cexp_linearized_limit
      (φs := φs)
      (φ := charFun (μ : Measure ℝ))
      (ψ := ψ)
      (hφs := hφs)
      (hpow := hpow)
      (hφ0 := hchar0)
      (hlin := hlin)
  let rootLaw : ℕ → ProbabilityMeasure ℝ := fun n ↦ Classical.choose (hφs n)
  have hrootLawChar : ∀ n : ℕ, charFun (rootLaw n : Measure ℝ) = φs n := by
    intro n
    exact Classical.choose_spec (hφs n)
  let fullIntensity : ℕ → FiniteMeasure ℝ := fun n ↦
    (((n : NNReal) • (rootLaw n).toFiniteMeasure) : FiniteMeasure ℝ)
  let μs : ℕ → ProbabilityMeasure ℝ := fun n ↦ compoundPoissonMeasure (fullIntensity n)
  have hμs_char :
      ∀ t : ℝ,
        Tendsto (fun n : ℕ ↦ charFun (μs n : Measure ℝ) t) atTop
          (𝓝 (charFun (μ : Measure ℝ) t)) := by
    intro t
    have htarget : charFun (μ : Measure ℝ) t = Complex.exp (ψ t) := by
      simpa using congrArg (fun f : ℝ → ℂ ↦ f t) hchar_eq
    have hrewrite :
        (fun n : ℕ ↦ charFun (μs n : Measure ℝ) t) =
          fun n : ℕ ↦ Complex.exp ((n : ℂ) * (φs n t - 1)) := by
      funext n
      calc
        charFun (μs n : Measure ℝ) t
            = Complex.exp ((n : ℂ) * (charFun (rootLaw n : Measure ℝ) t - 1)) := by
                simpa [μs, fullIntensity] using
                  (charFun_compoundPoissonMeasure_natSmulProbability (ρ := rootLaw n) (n := n) t)
        _ = Complex.exp ((n : ℂ) * (φs n t - 1)) := by rw [hrootLawChar n]
    rw [hrewrite]
    -- Proof comment: Theorem 16.6 turns the CFP power limit into the required linearized limit,
    -- and exponentiation preserves convergence.
    simpa [htarget] using
      (Complex.continuous_exp.continuousAt.tendsto.comp (hlin t))
  have hμs : Tendsto μs atTop (𝓝 μ) :=
    ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 hμs_char
  let νs : ℕ → FiniteMeasure {x : ℝ // x ≠ 0} := fun n ↦ puncturedIntensity (fullIntensity n)
  refine ⟨νs, ?_⟩
  -- Proof comment: deleting the zero atom from each intensity leaves the compound-Poisson law
  -- unchanged.
  refine Tendsto.congr' ?_ hμs
  exact Filter.Eventually.of_forall fun n ↦ by
    simpa [νs, μs] using (compoundPoissonMeasure_ignoreZeroAtom (ν := fullIntensity n)).symm

/-- Helper for Theorem 16.5: weak limits of punctured compound-Poisson approximations remain
infinitely divisible. -/
theorem isInfinitelyDivisible_of_exists_compoundPoissonApproximation
    {μ : ProbabilityMeasure ℝ}
    (hμ :
      ∃ νs : ℕ → FiniteMeasure {x : ℝ // x ≠ 0},
        Tendsto (fun n ↦ compoundPoissonMeasure ((νs n).map Subtype.val)) atTop (𝓝 μ)) :
    ProbabilityMeasure.IsInfinitelyDivisible μ := by
  rcases hμ with ⟨νs, hνs⟩
  let μs : ℕ → ProbabilityMeasure ℝ := fun n ↦ compoundPoissonMeasure ((νs n).map Subtype.val)
  have hμsInfinitelyDivisible : ∀ n : ℕ, ProbabilityMeasure.IsInfinitelyDivisible (μs n) := by
    intro n
    -- Proof comment: each compound-Poisson law is infinitely divisible by the owner API.
    simpa [μs] using
      (compoundPoissonMeasure_infinitelyDivisible
        ((((νs n).map Subtype.val : FiniteMeasure ℝ) : Measure ℝ)))
  -- Proof comment: infinite divisibility is stable under weak convergence.
  exact MeasureTheory.ProbabilityMeasure.isInfinitelyDivisible_of_tendsto hμsInfinitelyDivisible
    (by simpa [μs] using hνs)

-- Proof sketch: exact convolution roots of an infinitely divisible law give a CFP power limit of
-- characteristic functions; Theorem 16.6 converts this to a linearized limit, whose
-- exponentials are the compound-Poisson approximants. Conversely, compound-Poisson laws are
-- infinitely divisible and the property is closed under weak limits.
/-- Theorem 16.5: a probability measure on `R` is infinitely divisible if and only if there is a
sequence of finite jump measures on `R \ {0}` whose canonical compound-Poisson laws converge
weakly to it. -/
theorem isInfinitelyDivisible_iff_exists_compoundPoissonApproximation
    (μ : ProbabilityMeasure ℝ) :
    ProbabilityMeasure.IsInfinitelyDivisible μ ↔
      ∃ νs : ℕ → FiniteMeasure {x : ℝ // x ≠ 0},
        Tendsto (fun n ↦ compoundPoissonMeasure ((νs n).map Subtype.val)) atTop (𝓝 μ) := by
  constructor
  · intro hμ
    exact exists_compoundPoissonApproximation_of_isInfinitelyDivisible hμ
  · intro hμ
    exact isInfinitelyDivisible_of_exists_compoundPoissonApproximation hμ

end

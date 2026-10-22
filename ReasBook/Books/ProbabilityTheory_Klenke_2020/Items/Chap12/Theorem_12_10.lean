/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Remark_12_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Remark_12_7

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
-- `IsExchangeable` is defined through finite-dimensional tuple laws; passing from that to
-- permutation-invariance of the full sequence law uses a finite-measure bridge in mathlib, so
-- Theorem 12.10 keeps the source-faithful probability-space and random-variable hypotheses
-- explicit.
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

section

variable {X : ℕ → Ω → E}
variable {φ : (ℕ → E) → ℝ}

/-- Helper for Theorem 12.10: `permutePrefix n ρ` is measurable on sequence space. -/
private theorem measurable_permutePrefix (n : ℕ) (ρ : Equiv.Perm (Fin n)) :
    Measurable (permutePrefix n ρ : (ℕ → E) → ℕ → E) := by
  -- Each output coordinate is evaluation at the corresponding extended permutation index.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [permutePrefix, Function.comp] using
    (measurable_pi_apply ((ρ.extendDomain Fin.equivSubtype) i) :
      Measurable fun x : ℕ → E ↦ x ((ρ.extendDomain Fin.equivSubtype) i))

/-- Helper for Theorem 12.10: exchangeability gives almost-everywhere measurability of the full
sample-sequence map `Function.swap X`. -/
private theorem aemeasurableProcessSwap_of_isExchangeable (hX : IsExchangeable X μ) :
    AEMeasurable (Function.swap X) μ := by
  -- Each coordinate has the law of `X 0`, so every coordinate map is a.e.-measurable.
  refine aemeasurable_pi_lambda _ fun i ↦ ?_
  simpa [Function.swap] using (hX.identDistrib 0 i).aemeasurable_snd

/-- Helper for Theorem 12.10: an exchangeable process has the same full sequence law after
permuting the first `n` coordinates. -/
private theorem identDistrib_process_permutePrefix_of_isExchangeable
    (hX : IsExchangeable X μ) (n : ℕ) (ρ : Equiv.Perm (Fin n)) :
    IdentDistrib (Function.swap X) (permutePrefix n ρ ∘ Function.swap X) μ μ := by
  let σ : ℕ ≃ ℕ := ρ.extendDomain Fin.equivSubtype
  have hswap_ae := aemeasurableProcessSwap_of_isExchangeable hX
  have hperm_swap_ae :
      AEMeasurable (permutePrefix n ρ ∘ Function.swap X) μ := by
    exact (measurable_permutePrefix n ρ).comp_aemeasurable hswap_ae
  rw [ProbabilityTheory.identDistrib_iff_forall_finset_identDistrib hswap_ae hperm_swap_ae]
  intro s
  let e := s.orderIsoOfFin rfl
  let u : Fin s.card ↪ ℕ := (s.orderEmbOfFin rfl).toEmbedding
  let v : Fin s.card ↪ ℕ := ⟨fun i ↦ σ (u i), σ.injective.comp u.injective⟩
  have htuple :
      IdentDistrib
        (fun ω ↦ fun i : Fin s.card ↦ X (u i) ω)
        (fun ω ↦ fun i : Fin s.card ↦ X (v i) ω) μ μ :=
    (isExchangeable_iff_identDistrib_of_pairwise_distinct X μ).mp hX _ u v
  let es : (Fin s.card → E) ≃ᵐ (s → E) := MeasurableEquiv.piCongrLeft (fun _ : s ↦ E) e
  have hrestrict := htuple.comp es.measurable
  have hleft :
      es ∘ (fun ω ↦ fun i : Fin s.card ↦ X (u i) ω) =
        fun ω ↦ s.restrict (Function.swap X ω) := by
    funext ω
    ext j
    let xu : (i : Fin s.card) → (fun _ : s ↦ E) (e i) := fun i ↦ X (u i) ω
    have h := Equiv.piCongrLeft_apply_apply (fun _ : s ↦ E) e xu (e.symm j)
    have hindex : u (e.symm j) = (j : ℕ) := by
      change (s.orderEmbOfFin rfl) ((s.orderIsoOfFin rfl).symm j) = (j : ℕ)
      rw [← Finset.coe_orderIsoOfFin_apply]
      simp
    simpa [xu, es, MeasurableEquiv.piCongrLeft, e, Function.swap, Finset.restrict, hindex] using h
  have hright :
      es ∘ (fun ω ↦ fun i : Fin s.card ↦ X (v i) ω) =
        fun ω ↦ s.restrict (permutePrefix n ρ (Function.swap X ω)) := by
    funext ω
    ext j
    let xv : (i : Fin s.card) → (fun _ : s ↦ E) (e i) := fun i ↦ X (v i) ω
    have h := Equiv.piCongrLeft_apply_apply (fun _ : s ↦ E) e xv (e.symm j)
    have hindex : v (e.symm j) = σ j := by
      change σ ((s.orderEmbOfFin rfl) ((s.orderIsoOfFin rfl).symm j)) = σ j
      rw [← Finset.coe_orderIsoOfFin_apply]
      simp
    simpa [xv, es, MeasurableEquiv.piCongrLeft, e, Function.swap, Finset.restrict,
      permutePrefix, Function.comp, σ, hindex] using h
  simpa [hleft, hright] using hrestrict

/-- Helper for Theorem 12.10: the sequence-space average `exchangeableAverage n φ` is measurable
with respect to the pulled-back `n`-exchangeable sigma-algebra along `Function.swap X`. -/
private theorem exchangeableAverage_measurable_nExchangeableSigmaAlgebra
    (hφ_meas : Measurable φ) (n : ℕ) :
    Measurable[nExchangeableSigmaAlgebra (Function.swap X) n]
      (exchangeableAverage n φ ∘ Function.swap X) := by
  -- First place the average itself among the generators of the owner `n`-symmetric sigma-algebra.
  have havg_meas :
      Measurable (exchangeableAverage n φ : (ℕ → E) → ℝ) := by
    have hsum :
        Measurable (fun x : ℕ → E ↦
          (∑ ρ : Equiv.Perm (Fin n), φ (permutePrefix n ρ x) : ℝ)) := by
      simpa using
        (Finset.measurable_sum (Finset.univ : Finset (Equiv.Perm (Fin n)))
          fun ρ hρ ↦ hφ_meas.comp (measurable_permutePrefix n ρ))
    simpa [exchangeableAverage] using hsum.div_const (Nat.factorial n : ℝ)
  have havg_exchangeable :
      Measurable[nSymmetricSequenceSigmaAlgebra n] (exchangeableAverage n φ) := by
    let f : {f : (ℕ → E) → ℝ // Measurable f ∧ IsNSymmetricSequenceMap n f} :=
      ⟨exchangeableAverage n φ, havg_meas, exchangeableAverage_isNSymmetric n φ⟩
    -- The generator defining the sigma-algebra is measurable by construction.
    rw [measurable_iff_comap_le]
    exact le_iSup_of_le f le_rfl
  -- Then pull that measurability back along the sample-sequence map.
  exact havg_exchangeable.comp (comap_measurable (Function.swap X))

/-- Helper for Theorem 12.10: on every event from the `n`-exchangeable sigma-algebra, the original
and permuted sequence functionals have the same set integral. -/
private theorem setIntegral_eq_on_nExchangeable_event_of_isExchangeable
    (hX : IsExchangeable X μ) (hswap_meas : Measurable (Function.swap X)) (hφ_meas : Measurable φ)
    (hφ_int : Integrable (φ ∘ Function.swap X) μ) (n : ℕ) (ρ : Equiv.Perm (Fin n))
    {A : Set Ω} (hA : MeasurableSet[nExchangeableSigmaAlgebra (Function.swap X) n] A) :
    ∫ ω in A, φ (Function.swap X ω) ∂μ =
      ∫ ω in A, φ (permutePrefix n ρ (Function.swap X ω)) ∂μ := by
  rcases (measurableSet_nExchangeableSigmaAlgebra_iff n (Function.swap X) A).1 hA with
    ⟨B, hB_meas, hB_symm, hA_eq⟩
  have hA_meas : MeasurableSet A := (nExchangeableSigmaAlgebra_le hswap_meas n) _ hA
  let ψ : (ℕ → E) → ℝ := B.indicator φ
  have hψ_meas : Measurable ψ := hφ_meas.indicator hB_meas
  have hψ_int :
      ∫ ω, ψ (Function.swap X ω) ∂μ =
        ∫ ω, ψ (permutePrefix n ρ (Function.swap X ω)) ∂μ := by
    -- Compare the two integrals through equality in law of the full sequence maps.
    exact
      (identDistrib_process_permutePrefix_of_isExchangeable hX n ρ).comp hψ_meas |>.integral_eq
  have hleft :
      (fun ω ↦ ψ (Function.swap X ω)) = A.indicator (fun ω ↦ φ (Function.swap X ω)) := by
    funext ω
    by_cases hω : Function.swap X ω ∈ B
    · simp [ψ, hA_eq, hω]
    · simp [ψ, hA_eq, hω]
  have hright :
      (fun ω ↦ ψ (permutePrefix n ρ (Function.swap X ω))) =
        A.indicator (fun ω ↦ φ (permutePrefix n ρ (Function.swap X ω))) := by
    funext ω
    have hmem : permutePrefix n ρ (Function.swap X ω) ∈ B ↔ Function.swap X ω ∈ B := by
      exact Set.ext_iff.mp (hB_symm ρ) (Function.swap X ω)
    by_cases hω : Function.swap X ω ∈ B
    · have hperm : permutePrefix n ρ (Function.swap X ω) ∈ B := hmem.mpr hω
      simp [ψ, hA_eq, hω, hperm]
    · have hperm : permutePrefix n ρ (Function.swap X ω) ∉ B := fun h ↦ hω (hmem.mp h)
      simp [ψ, hA_eq, hω, hperm]
  -- Rewrite the whole-space indicator integrals as the desired set integrals on `A`.
  calc
    ∫ ω in A, φ (Function.swap X ω) ∂μ = ∫ ω, ψ (Function.swap X ω) ∂μ := by
      rw [hleft, MeasureTheory.integral_indicator hA_meas]
    _ = ∫ ω, ψ (permutePrefix n ρ (Function.swap X ω)) ∂μ := hψ_int
    _ = ∫ ω in A, φ (permutePrefix n ρ (Function.swap X ω)) ∂μ := by
      rw [hright, MeasureTheory.integral_indicator hA_meas]

/-- Theorem 12.10: for an exchangeable sequence of random variables on a probability space, the
conditional expectation of a measurable integrable sequence functional with respect to the finite
exchangeable `σ`-algebra is unchanged by permuting the first `n` coordinates. -/
theorem condExp_eq_condExp_permuteFirst_of_isExchangeable
    (hX : IsExchangeable X μ) (hX_meas : ∀ n, Measurable (X n)) (hφ_meas : Measurable φ)
    (hφ_int : Integrable (φ ∘ Function.swap X) μ) (n : ℕ)
    (ρ : Equiv.Perm (Fin n)) :
    μ[φ ∘ Function.swap X | nExchangeableSigmaAlgebra (Function.swap X) n] =ᵐ[μ]
      μ[φ ∘ permutePrefix n ρ ∘ Function.swap X |
        nExchangeableSigmaAlgebra (Function.swap X) n] := by
  have hswap_meas : Measurable (Function.swap X) := by
    -- Measurability into the countable product is coordinatewise measurability.
    rw [measurable_pi_iff]
    intro i
    simpa [Function.swap] using hX_meas i
  have hm :
      nExchangeableSigmaAlgebra (Function.swap X) n ≤ (inferInstance : MeasurableSpace Ω) :=
    nExchangeableSigmaAlgebra_le hswap_meas n
  have hperm_int :
      Integrable (φ ∘ permutePrefix n ρ ∘ Function.swap X) μ := by
    -- The permuted functional has the same law as the original one.
    exact
      (identDistrib_process_permutePrefix_of_isExchangeable hX n ρ).comp hφ_meas |>.integrable_snd
        hφ_int
  -- Route correction: prove equality of the two conditional expectations by uniqueness, using the
  -- eventwise integral identity on `m`-measurable sets.
  refine
    (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hm hφ_int
      (fun s hs hs_fin ↦ by
        exact
          (MeasureTheory.integrable_condExp
            : Integrable
                (μ[φ ∘ permutePrefix n ρ ∘ Function.swap X |
                  nExchangeableSigmaAlgebra (Function.swap X) n])
                μ).integrableOn)
      (fun s hs hs_fin ↦ by
        calc
          ∫ ω in s,
              μ[φ ∘ permutePrefix n ρ ∘ Function.swap X |
                nExchangeableSigmaAlgebra (Function.swap X) n] ω ∂μ =
              ∫ ω in s, φ (permutePrefix n ρ (Function.swap X ω)) ∂μ := by
                simpa [Function.comp] using
                  (MeasureTheory.setIntegral_condExp
                    hm hperm_int hs)
          _ = ∫ ω in s, φ (Function.swap X ω) ∂μ := by
                symm
                exact setIntegral_eq_on_nExchangeable_event_of_isExchangeable
                  hX hswap_meas hφ_meas hφ_int n ρ hs
      ) (MeasureTheory.stronglyMeasurable_condExp
          : StronglyMeasurable[nExchangeableSigmaAlgebra (Function.swap X) n]
              (μ[φ ∘ permutePrefix n ρ ∘ Function.swap X |
                nExchangeableSigmaAlgebra (Function.swap X) n])).aestronglyMeasurable).symm

/-- Companion corollary to Theorem 12.10: averaging the permutation identities over `S(n)` gives
the exchangeable-average formula `A_n(φ)(X) = (1 / n!) ∑_{ρ ∈ S(n)} φ(X^ρ)`. -/
theorem condExp_eq_exchangeableAverage_of_isExchangeable
    (hX : IsExchangeable X μ) (hX_meas : ∀ n, Measurable (X n)) (hφ_meas : Measurable φ)
    (hφ_int : Integrable (φ ∘ Function.swap X) μ) (n : ℕ) :
    μ[φ ∘ Function.swap X | nExchangeableSigmaAlgebra (Function.swap X) n] =ᵐ[μ]
      exchangeableAverage n φ ∘ Function.swap X := by
  have hswap_meas : Measurable (Function.swap X) := by
    -- Measurability into the countable product is coordinatewise measurability.
    rw [measurable_pi_iff]
    intro i
    simpa [Function.swap] using hX_meas i
  have hm :
      nExchangeableSigmaAlgebra (Function.swap X) n ≤ (inferInstance : MeasurableSpace Ω) :=
    nExchangeableSigmaAlgebra_le hswap_meas n
  let g : Equiv.Perm (Fin n) → Ω → ℝ :=
    fun ρ ω ↦ φ (permutePrefix n ρ (Function.swap X ω))
  have hg_int : ∀ ρ : Equiv.Perm (Fin n), Integrable (g ρ) μ := by
    intro ρ
    -- Every permutation summand has the same distribution as the original functional.
    exact
      (identDistrib_process_permutePrefix_of_isExchangeable hX n ρ).comp hφ_meas |>.integrable_snd
        hφ_int
  have hsum_int : Integrable (fun ω ↦ ∑ ρ : Equiv.Perm (Fin n), g ρ ω) μ := by
    simpa [g] using
      (MeasureTheory.integrable_finset_sum
        (Finset.univ : Finset (Equiv.Perm (Fin n))) fun ρ hρ ↦ hg_int ρ)
  have havg_int : Integrable (exchangeableAverage n φ ∘ Function.swap X) μ := by
    simpa [exchangeableAverage, Function.comp, g] using
      hsum_int.div_const (Nat.factorial n : ℝ)
  have havg_meas :
      AEStronglyMeasurable[nExchangeableSigmaAlgebra (Function.swap X) n]
        (exchangeableAverage n φ ∘ Function.swap X) μ :=
    (exchangeableAverage_measurable_nExchangeableSigmaAlgebra hφ_meas n).aestronglyMeasurable
  have hfactorial_ne_zero : (Nat.factorial n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  refine
    (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hm hφ_int
      (fun s hs hs_fin ↦ havg_int.integrableOn)
      (fun s hs hs_fin ↦ by
        have hsum_eq :
            ∫ ω in s, (∑ ρ : Equiv.Perm (Fin n), g ρ ω : ℝ) ∂μ =
              ∑ ρ : Equiv.Perm (Fin n), ∫ ω in s, g ρ ω ∂μ := by
          simpa [g] using
            (MeasureTheory.integral_finset_sum
              (Finset.univ : Finset (Equiv.Perm (Fin n)))
              fun ρ hρ ↦ (hg_int ρ).integrableOn)
        have hperm_sum :
            (∑ ρ : Equiv.Perm (Fin n), ∫ ω in s, g ρ ω ∂μ) =
              ∑ ρ : Equiv.Perm (Fin n), ∫ ω in s, φ (Function.swap X ω) ∂μ := by
          refine Finset.sum_congr rfl ?_
          intro ρ hρ
          exact
            (setIntegral_eq_on_nExchangeable_event_of_isExchangeable
              hX hswap_meas hφ_meas hφ_int n ρ hs).symm
        calc
          ∫ ω in s, exchangeableAverage n φ (Function.swap X ω) ∂μ =
              ∫ ω in s, ((∑ ρ : Equiv.Perm (Fin n), g ρ ω : ℝ) / Nat.factorial n) ∂μ := by
                simp [exchangeableAverage, g]
          _ = (∫ ω in s, (∑ ρ : Equiv.Perm (Fin n), g ρ ω : ℝ) ∂μ) / Nat.factorial n := by
                simpa [MeasureTheory.integral, g] using
                  (MeasureTheory.integral_div (Nat.factorial n : ℝ)
                    (fun ω ↦ ∑ ρ : Equiv.Perm (Fin n), g ρ ω))
          _ = (∑ ρ : Equiv.Perm (Fin n), ∫ ω in s, g ρ ω ∂μ) / Nat.factorial n := by
                rw [hsum_eq]
          _ = (∑ ρ : Equiv.Perm (Fin n), ∫ ω in s, φ (Function.swap X ω) ∂μ) /
                Nat.factorial n := by
                rw [hperm_sum]
          _ = ∫ ω in s, φ (Function.swap X ω) ∂μ := by
                simp [hfactorial_ne_zero, Fintype.card_perm])
      havg_meas).symm

end

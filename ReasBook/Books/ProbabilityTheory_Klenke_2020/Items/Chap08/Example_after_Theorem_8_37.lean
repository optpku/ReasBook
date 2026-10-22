/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Example_14_30

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
open unitInterval

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

section

variable (n : ℕ) (P : Measure Ω) {X : Ω → ↑I} {Y : Ω → Fin n → Bool}

/-- Example after Theorem 8.37: if `X` is uniformly distributed on `[0,1]` and, for `P.map X`-
almost every `x`, the regular conditional law of the Boolean vector `Y` given `X = x` has
independent coordinates with one-coordinate Bernoulli law on `Bool` of parameter `x`, then the
whole conditional law is the canonical Bernoulli product kernel `coinTossingKernel n`. -/
theorem condDistrib_coinTossVector_given_uniform_ae_eq_coinTossingKernel
    (hX_law : HasLaw X volume P) :
    letI : IsProbabilityMeasure P := hX_law.isProbabilityMeasure
    ∀ (hcond_indep : Kernel.iIndepFun Function.eval (condDistrib Y X P) (P.map X))
      (hcond_marg :
        ∀ i : Fin n,
          (condDistrib Y X P).map (Function.eval i) =ᵐ[P.map X]
            fun x ↦ (PMF.bernoulli (toNNReal x) (by simpa using x.2.2)).toMeasure),
      condDistrib Y X P =ᵐ[volume] coinTossingKernel n := by
  letI : IsProbabilityMeasure P := hX_law.isProbabilityMeasure
  intro hcond_indep hcond_marg
  classical
  let κ : Kernel ↑I (Fin n → Bool) := condDistrib Y X P
  have hκ_map :
      κ =ᵐ[P.map X] coinTossingKernel n := by
    have hsingleton :
        ∀ᵐ x ∂P.map X,
          ∀ y : Fin n → Bool,
            κ x ({y} : Set (Fin n → Bool)) =
              (coinTossingKernel n x) ({y} : Set (Fin n → Bool)) := by
      refine ae_all_iff.2 fun y : Fin n → Bool ↦ ?_
      have hfactor :
          ∀ᵐ x ∂P.map X,
            κ x ({y} : Set (Fin n → Bool)) =
              ∏ i : Fin n, (κ.map (Function.eval i) x) ({y i} : Set Bool) := by
        -- Specialize conditional independence to the singleton cylinder cutting out the word `y`.
        have hcond_formula :=
          (Kernel.iIndepFun_iff_measure_inter_preimage_eq_mul
            (m := fun _ : Fin n ↦ inferInstance) (f := Function.eval)).1 hcond_indep
        have hraw :=
          hcond_formula (Finset.univ : Finset (Fin n)) (sets := fun i ↦ ({y i} : Set Bool))
            (fun i _ ↦ measurableSet_singleton (y i))
        filter_upwards [hraw] with x hx
        have hinter :
            (⋂ i ∈ (Finset.univ : Finset (Fin n)),
                Function.eval i ⁻¹' ({y i} : Set Bool)) =
              ({y} : Set (Fin n → Bool)) := by
          ext z
          simp [funext_iff]
        have hprod :
            (∏ i ∈ (Finset.univ : Finset (Fin n)),
                κ x (Function.eval i ⁻¹' ({y i} : Set Bool))) =
              ∏ i : Fin n, (κ.map (Function.eval i) x) ({y i} : Set Bool) := by
          rw [show
            (∏ i ∈ (Finset.univ : Finset (Fin n)),
                κ x (Function.eval i ⁻¹' ({y i} : Set Bool))) =
              ∏ i : Fin n, κ x (Function.eval i ⁻¹' ({y i} : Set Bool)) by
            rfl]
          refine Finset.prod_congr rfl ?_
          intro i hi
          symm
          exact Kernel.map_apply' κ (by fun_prop) x (measurableSet_singleton (y i))
        rw [hinter, hprod] at hx
        exact hx
      have hmarg :
          ∀ᵐ x ∂P.map X,
            ∀ i : Fin n,
              (κ.map (Function.eval i) x) ({y i} : Set Bool) =
                ((PMF.bernoulli (toNNReal x) (by simpa using x.2.2)).toMeasure)
                  ({y i} : Set Bool) := by
        refine ae_all_iff.2 fun i ↦ ?_
        exact (hcond_marg i).mono fun x hx ↦
          congrArg (fun μ : Measure Bool ↦ μ ({y i} : Set Bool)) hx
      -- Rewrite the singleton mass using the coordinate marginals and identify it with the
      -- Bernoulli product mass at `y`.
      filter_upwards [hfactor, hmarg] with x hx_factor hx_marg
      have hprod :
          (∏ i : Fin n, (κ.map (Function.eval i) x) ({y i} : Set Bool)) =
            ∏ i : Fin n,
              ((PMF.bernoulli (toNNReal x) (by simpa using x.2.2)).toMeasure)
                ({y i} : Set Bool) := by
        refine Finset.prod_congr rfl ?_
        intro i hi
        exact hx_marg i
      have hcoin :
          (coinTossingKernel n x) ({y} : Set (Fin n → Bool)) =
            ∏ i : Fin n,
              ((PMF.bernoulli (toNNReal x) (by simpa using x.2.2)).toMeasure)
                ({y i} : Set Bool) := by
        rw [coinTossingKernel_apply, Measure.pi_singleton]
      calc
        κ x ({y} : Set (Fin n → Bool)) =
            ∏ i : Fin n, (κ.map (Function.eval i) x) ({y i} : Set Bool) := hx_factor
        _ =
            ∏ i : Fin n,
              ((PMF.bernoulli (toNNReal x) (by simpa using x.2.2)).toMeasure)
                ({y i} : Set Bool) := hprod
        _ = (coinTossingKernel n x) ({y} : Set (Fin n → Bool)) := hcoin.symm
    filter_upwards [hsingleton] with x hx
    -- On the finite codomain `Fin n → Bool`, equality of all singleton masses determines the
    -- entire conditional fiber measure.
    exact Measure.ext_of_singleton (μ := κ x) (ν := coinTossingKernel n x) (fun y ↦ hx y)
  -- Transport the almost-everywhere equality from `P.map X` to `volume` using the law of `X`.
  simpa [κ, hX_law.map_eq] using hκ_map

/-- Pointwise form of
`condDistrib_coinTossVector_given_uniform_ae_eq_coinTossingKernel`. For `volume`-almost every
`x : ↑I`, the regular conditional distribution of `Y` given `X = x` is the Bernoulli product law
`coinTossingKernel n x` on `Fin n → Bool`. -/
theorem condDistrib_coinTossVector_given_uniform_ae_eq_coinTossingKernel_apply
    (hX_law : HasLaw X volume P) :
    letI : IsProbabilityMeasure P := hX_law.isProbabilityMeasure
    ∀ (hcond_indep : Kernel.iIndepFun Function.eval (condDistrib Y X P) (P.map X))
      (hcond_marg :
        ∀ i : Fin n,
          (condDistrib Y X P).map (Function.eval i) =ᵐ[P.map X]
            fun x ↦ (PMF.bernoulli (toNNReal x) (by simpa using x.2.2)).toMeasure),
      ∀ᵐ x ∂volume, condDistrib Y X P x = coinTossingKernel n x := by
  letI : IsProbabilityMeasure P := hX_law.isProbabilityMeasure
  intro hcond_indep hcond_marg
  simpa using
    condDistrib_coinTossVector_given_uniform_ae_eq_coinTossingKernel n P hX_law hcond_indep
      hcond_marg

end

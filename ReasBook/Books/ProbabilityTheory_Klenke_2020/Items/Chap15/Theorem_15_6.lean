/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Corollary_15_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory ProbabilityTheory
open BoundedContinuousFunction
open scoped Topology

namespace MeasureTheory.FiniteMeasure

/-
Theorem 15.6 is `source-facing`: its public content is uniqueness of finite measures on `[0, ∞)`
from their Laplace transforms.

The owner abstractions are:
* `ProbabilityTheory.mgf` for the transform itself;
* `finiteMeasure_eq_of_forall_mem_integral_eq_of_separating_boundedContinuousFamily` from
  Chapter 15 for uniqueness from a separating bounded-continuous family.

Accordingly, the local API stays thin: `laplaceTransform_def` is only the bridge from the textbook
kernel `x ↦ exp (-t x)` to `mgf`, while the main theorem remains the source statement.
-/

/-- The canonical owner `ProbabilityTheory.mgf ((↑) : NNReal → ℝ)` at the parameter `-(t : ℝ)` is
the textbook Laplace-transform integral against `x ↦ exp (-t x)` on `[0, ∞)`. -/
theorem laplaceTransform_def (μ : FiniteMeasure NNReal) (t : NNReal) :
    mgf ((↑) : NNReal → ℝ) (μ : Measure NNReal) (-(t : ℝ)) =
      ∫ x, Real.exp (-((t : ℝ) * (x : ℝ))) ∂(μ : Measure NNReal) := by
  simp [ProbabilityTheory.mgf, neg_mul]

/-- Helper for Theorem 15.6: the map `x ↦ exp (-x)` lands in `[0,1]`. -/
private theorem expNeg_mem_unitInterval (x : NNReal) :
    Real.exp (-(x : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact (Real.exp_pos _).le
  · -- Proof comment: the exponent is nonpositive because `x` lies in `[0, ∞)`.
    have hnonpos : -((x : ℝ)) ≤ 0 := by
      linarith [show (0 : ℝ) ≤ (x : ℝ) from x.2]
    exact Real.exp_le_one_iff.mpr hnonpos

/-- Helper for Theorem 15.6: `x ↦ exp (-x)` viewed as a map into `[0,1]`. -/
private def expNegUnitIntervalMap (x : NNReal) : Set.Icc (0 : ℝ) 1 :=
  ⟨Real.exp (-(x : ℝ)), expNeg_mem_unitInterval x⟩

/-- Helper for Theorem 15.6: the compactifying map `x ↦ exp (-x)` is continuous. -/
private theorem continuous_expNegUnitIntervalMap :
    Continuous expNegUnitIntervalMap := by
  -- Proof comment: the subtype-valued map is continuous because its real-valued coordinate is.
  refine Continuous.subtype_mk ?_ fun x ↦ expNeg_mem_unitInterval x
  simpa using (Real.continuous_exp.comp NNReal.continuous_coe.neg)

/-- Helper for Theorem 15.6: the compactifying map `x ↦ exp (-x)` is injective. -/
private theorem expNegUnitIntervalMap_injective :
    Function.Injective expNegUnitIntervalMap := by
  intro x y hxy
  -- Proof comment: `Real.exp` is injective, so equality of images forces equality of exponents.
  have hExp : Real.exp (-(x : ℝ)) = Real.exp (-(y : ℝ)) := congrArg Subtype.val hxy
  have hNeg : -((x : ℝ)) = -((y : ℝ)) := Real.exp_injective hExp
  apply NNReal.coe_injective
  linarith

/-- Helper for Theorem 15.6: the compactifying map is a measurable embedding. -/
private theorem measurableEmbedding_expNegUnitIntervalMap :
    MeasurableEmbedding expNegUnitIntervalMap :=
  continuous_expNegUnitIntervalMap.measurableEmbedding expNegUnitIntervalMap_injective

/-- Helper for Theorem 15.6: the pushforward of a finite measure along `x ↦ exp (-x)`. -/
private def expNegPushforward (μ : FiniteMeasure NNReal) : FiniteMeasure (Set.Icc (0 : ℝ) 1) :=
  μ.map expNegUnitIntervalMap

/-- Helper for Theorem 15.6: the monomial `y ↦ y ^ n` on `[0,1]` is continuous. -/
private theorem continuous_unitIntervalMonomialFun (n : ℕ) :
    Continuous (fun x : Set.Icc (0 : ℝ) 1 ↦ (x : ℝ) ^ n) := by
  -- Proof comment: monomials are continuous on `ℝ`, hence on the compact interval subtype.
  simpa using continuous_subtype_val.pow n

/-- Helper for Theorem 15.6: the degree-`n` monomial on `[0,1]` as a bounded continuous function. -/
private def unitIntervalMonomial (n : ℕ) : BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    { toFun := fun x ↦ (x : ℝ) ^ n
      continuous_toFun := continuous_unitIntervalMonomialFun n }

/-- Helper for Theorem 15.6: the monomial family on `[0,1]`. -/
private def unitIntervalMonomialFamily :
    Set (BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ) :=
  Set.range unitIntervalMonomial

/-- Helper for Theorem 15.6: monomials on `[0,1]` separate points. -/
private theorem unitIntervalMonomialsSeparatePoints :
    Set.SeparatesPoints
      ((fun f : BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ ↦
          (f : Set.Icc (0 : ℝ) 1 → ℝ)) '' unitIntervalMonomialFamily) := by
  intro x y hxy
  -- Proof comment: the degree-`1` monomial is the identity function on `[0,1]`.
  refine ⟨(unitIntervalMonomial 1 : Set.Icc (0 : ℝ) 1 → ℝ), ?_, ?_⟩
  · exact ⟨unitIntervalMonomial 1, ⟨1, rfl⟩, rfl⟩
  · intro hEval
    apply hxy
    apply Subtype.ext
    simpa [unitIntervalMonomial] using hEval

/-- Helper for Theorem 15.6: pushing forward along `x ↦ exp (-x)` turns the `n`th monomial moment
into the Laplace transform at the parameter `n`. -/
private theorem integral_monomial_expNegMap_eq_laplace
    (μ : FiniteMeasure NNReal) (n : ℕ) :
    ∫ y, unitIntervalMonomial n y
        ∂((expNegPushforward μ : FiniteMeasure (Set.Icc (0 : ℝ) 1)) :
          Measure (Set.Icc (0 : ℝ) 1)) =
      mgf ((↑) : NNReal → ℝ) (μ : Measure NNReal) (-(n : ℝ)) := by
  -- Proof comment: transport the monomial integral across the pushforward and simplify pointwise.
  calc
    ∫ y, unitIntervalMonomial n y
        ∂((expNegPushforward μ : FiniteMeasure (Set.Icc (0 : ℝ) 1)) :
          Measure (Set.Icc (0 : ℝ) 1)) =
      ∫ x, unitIntervalMonomial n (expNegUnitIntervalMap x) ∂(μ : Measure NNReal) := by
        rw [expNegPushforward]
        -- Proof comment: `integral_map` transports the bounded continuous integrand across the embedding.
        simpa using
          (measurableEmbedding_expNegUnitIntervalMap.integral_map
            (μ := (μ : Measure NNReal)) (g := unitIntervalMonomial n))
    _ = ∫ x, Real.exp (-((n : ℝ) * (x : ℝ))) ∂(μ : Measure NNReal) := by
      congr with x
      calc
        unitIntervalMonomial n (expNegUnitIntervalMap x)
            = (Real.exp (-(x : ℝ))) ^ n := by
              simp [unitIntervalMonomial, expNegUnitIntervalMap]
        _ = Real.exp ((n : ℝ) * (-(x : ℝ))) := by
              simpa [mul_comm] using (Real.exp_nat_mul (-(x : ℝ)) n).symm
        _ = Real.exp (-((n : ℝ) * (x : ℝ))) := by ring_nf
    _ = mgf ((↑) : NNReal → ℝ) (μ : Measure NNReal) (-(n : ℝ)) := by
      -- Proof comment: this is exactly the Laplace-transform normalization at the integer parameter `n`.
      simpa using (laplaceTransform_def μ (n : NNReal)).symm

/-- Helper for Theorem 15.6: equality of the pushforwards under `x ↦ exp (-x)` implies equality
of the original finite measures. -/
private theorem eq_of_expNegPushforward_eq {μ ν : FiniteMeasure NNReal}
    (hmap :
      expNegPushforward μ =
        expNegPushforward ν) :
    μ = ν := by
  -- Proof comment: pushforward along a measurable embedding is injective on measures.
  apply FiniteMeasure.toMeasure_injective
  exact measurableEmbedding_expNegUnitIntervalMap.map_injective <|
    congrArg (fun ρ : FiniteMeasure (Set.Icc (0 : ℝ) 1) ↦ (ρ : Measure (Set.Icc (0 : ℝ) 1))) hmap

/-- Helper for Theorem 15.6: the monomial family on `[0,1]` is multiplicatively closed. -/
private theorem unitIntervalMonomialFamily_mul_mem
    ⦃f g : BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ⦄
    (hf : f ∈ unitIntervalMonomialFamily)
    (hg : g ∈ unitIntervalMonomialFamily) :
    f * g ∈ unitIntervalMonomialFamily := by
  rcases hf with ⟨m, rfl⟩
  rcases hg with ⟨n, rfl⟩
  refine ⟨m + n, ?_⟩
  ext x
  -- Proof comment: multiplying two monomials adds their exponents.
  simp [unitIntervalMonomial, pow_add]

/-- Helper for Theorem 15.6: the monomial family on `[0,1]` contains `1`. -/
private theorem one_mem_unitIntervalMonomialFamily :
    (1 : BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ) ∈ unitIntervalMonomialFamily := by
  refine ⟨0, ?_⟩
  ext x
  simp [unitIntervalMonomial]

/-- Helper for Theorem 15.6: equality of Laplace transforms yields equality of all monomial
integrals for the pushforwards along `x ↦ exp (-x)`. -/
private theorem expNegPushforward_integral_eq_of_mem_unitIntervalMonomialFamily
    {μ ν : FiniteMeasure NNReal}
    (hLaplace :
      ∀ t : NNReal,
        mgf ((↑) : NNReal → ℝ) (μ : Measure NNReal) (-(t : ℝ)) =
          mgf ((↑) : NNReal → ℝ) (ν : Measure NNReal) (-(t : ℝ))) :
    ∀ ⦃f : BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ⦄,
      f ∈ unitIntervalMonomialFamily →
        ∫ x, (f : Set.Icc (0 : ℝ) 1 → ℝ) x
            ∂((expNegPushforward μ : FiniteMeasure (Set.Icc (0 : ℝ) 1)) :
              Measure (Set.Icc (0 : ℝ) 1)) =
          ∫ x, (f : Set.Icc (0 : ℝ) 1 → ℝ) x
            ∂((expNegPushforward ν : FiniteMeasure (Set.Icc (0 : ℝ) 1)) :
              Measure (Set.Icc (0 : ℝ) 1)) := by
  intro f hf
  rcases hf with ⟨n, rfl⟩
  -- Proof comment: the pushforward moments coincide because they are Laplace values at `n`.
  calc
    ∫ x, (unitIntervalMonomial n : Set.Icc (0 : ℝ) 1 → ℝ) x
        ∂((expNegPushforward μ : FiniteMeasure (Set.Icc (0 : ℝ) 1)) :
          Measure (Set.Icc (0 : ℝ) 1)) =
      mgf ((↑) : NNReal → ℝ) (μ : Measure NNReal) (-(n : ℝ)) := by
        simpa using integral_monomial_expNegMap_eq_laplace μ n
    _ = mgf ((↑) : NNReal → ℝ) (ν : Measure NNReal) (-(n : ℝ)) := by
        simpa using hLaplace (n : NNReal)
    _ =
      ∫ x, (unitIntervalMonomial n : Set.Icc (0 : ℝ) 1 → ℝ) x
          ∂((expNegPushforward ν : FiniteMeasure (Set.Icc (0 : ℝ) 1)) :
            Measure (Set.Icc (0 : ℝ) 1)) := by
        simpa using (integral_monomial_expNegMap_eq_laplace ν n).symm

-- Proof sketch: the forward direction is immediate from equality of measures. For the converse,
-- pass to the one-point compactification of `[0, ∞)`, observe that the functions
-- `x ↦ exp (-λ x)` for `λ ≥ 0` form a multiplicatively closed separating class containing the
-- constants, and apply the separating-class uniqueness theorem from Corollary 15.3.
/-- Theorem 15.6: two finite measures on `[0, ∞)` are equal exactly when their Laplace transforms
agree at every nonnegative parameter. -/
theorem ext_iff_laplaceTransform_eq (μ ν : FiniteMeasure NNReal) :
    μ = ν ↔
      ∀ t : NNReal,
        mgf ((↑) : NNReal → ℝ) (μ : Measure NNReal) (-(t : ℝ)) =
          mgf ((↑) : NNReal → ℝ) (ν : Measure NNReal) (-(t : ℝ)) := by
  constructor
  · intro hμν t
    -- Proof comment: equality of measures immediately identifies all Laplace transforms.
    simpa [hμν]
  · intro hLaplace
    -- Route correction: rather than work on the one-point compactification directly in Lean,
    -- push both measures to `[0,1]` via `x ↦ exp (-x)` and apply Corollary 15.3 there.
    have hmul :
        ∀ ⦃f g : BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ⦄,
          f ∈ unitIntervalMonomialFamily →
            g ∈ unitIntervalMonomialFamily →
              f * g ∈ unitIntervalMonomialFamily := by
      intro f g hf hg
      exact unitIntervalMonomialFamily_mul_mem hf hg
    have hone :
        (1 : BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ) ∈
          unitIntervalMonomialFamily := by
      exact one_mem_unitIntervalMonomialFamily
    have hint :
        ∀ ⦃f : BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ⦄,
          f ∈ unitIntervalMonomialFamily →
            ∫ x, (f : Set.Icc (0 : ℝ) 1 → ℝ) x
                ∂((expNegPushforward μ : FiniteMeasure (Set.Icc (0 : ℝ) 1)) :
                  Measure (Set.Icc (0 : ℝ) 1)) =
              ∫ x, (f : Set.Icc (0 : ℝ) 1 → ℝ) x
                ∂((expNegPushforward ν : FiniteMeasure (Set.Icc (0 : ℝ) 1)) :
                  Measure (Set.Icc (0 : ℝ) 1)) := by
      exact expNegPushforward_integral_eq_of_mem_unitIntervalMonomialFamily hLaplace
    have hpush :
        expNegPushforward μ =
          expNegPushforward ν :=
      finiteMeasure_eq_of_forall_mem_integral_eq_of_separating_boundedContinuousFamily
        unitIntervalMonomialsSeparatePoints hmul hone hint
    exact eq_of_expNegPushforward_eq hpush

end MeasureTheory.FiniteMeasure

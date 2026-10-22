/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Corollary_15_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators BoundedContinuousFunction Topology

noncomputable section

variable {d : ℕ}
variable {μ ν : Measure (EuclideanSpace ℝ (Fin d))}
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- Helper for Exercise 15.1.2: the compact cube used to encode the nonnegative orthant by the
coordinate map `x ↦ exp (-x)`. -/
abbrev OrthantCube (d : ℕ) := Fin d → Set.Icc (0 : ℝ) 1

/-- Helper for Exercise 15.1.2: the coordinatewise compactification kernel takes values in
`[0, 1]`. -/
lemma compactifyOrthant_mem (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    Real.exp (-max (x i) 0) ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨Real.exp_pos _ |>.le, ?_⟩
  rw [Real.exp_le_one_iff]
  exact neg_nonpos.mpr (le_max_right _ _)

/-- Helper for Exercise 15.1.2: the compactification sends `x` to the cube point with coordinates
`exp (-max (x i) 0)`. -/
def compactifyOrthant (x : EuclideanSpace ℝ (Fin d)) : OrthantCube d :=
  fun i ↦ ⟨Real.exp (-max (x i) 0), compactifyOrthant_mem x i⟩

/-- Helper for Exercise 15.1.2: a natural exponent vector viewed as an element of `ℝ^d`. -/
def natExponentVector (n : Fin d → ℕ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i ↦ (n i : ℝ))

/-- Helper for Exercise 15.1.2: the `i`-th coordinate of `natExponentVector n` is `n i`. -/
lemma natExponentVector_apply (n : Fin d → ℕ) (i : Fin d) :
    natExponentVector (d := d) n i = (n i : ℝ) := by
  simp [natExponentVector, PiLp.toLp_apply]

/-- Helper for Exercise 15.1.2: the natural exponent vector is coordinatewise nonnegative. -/
lemma natExponentVector_nonneg (n : Fin d → ℕ) (i : Fin d) :
    0 ≤ natExponentVector (d := d) n i := by
  rw [natExponentVector_apply]
  exact Nat.cast_nonneg (n i)

/-- Helper for Exercise 15.1.2: applying `-log` coordinatewise recovers the orthant variable from a
cube point. -/
def recoverOrthant (y : OrthantCube d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i ↦ -Real.log (y i))

/-- Helper for Exercise 15.1.2: the cube monomial with exponent vector `n`. -/
def cubeMonomial (n : Fin d → ℕ) : BoundedContinuousFunction (OrthantCube d) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    { toFun := fun y ↦ ∏ i, ((y i : Set.Icc (0 : ℝ) 1) : ℝ) ^ (n i)
      continuous_toFun := by
        refine continuous_finset_prod Finset.univ fun i _ ↦ ?_
        exact (continuous_apply i).subtype_val.pow (n i) }

/-- Helper for Exercise 15.1.2: the compactification map is continuous, hence measurable. -/
lemma continuous_compactifyOrthant : Continuous (compactifyOrthant (d := d)) := by
  refine continuous_pi fun i ↦ ?_
  refine Continuous.subtype_mk ?_ fun x ↦ compactifyOrthant_mem x i
  exact Real.continuous_exp.comp
    (((PiLp.continuous_apply (p := 2) (β := fun _ : Fin d ↦ ℝ) i).max continuous_const).neg)

/-- Helper for Exercise 15.1.2: the recovery map is measurable coordinatewise. -/
lemma measurable_recoverOrthant : Measurable (recoverOrthant (d := d)) := by
  let g : OrthantCube d → Fin d → ℝ := fun y i ↦ -Real.log (y i)
  have hg : Measurable g := by
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact Real.measurable_log.neg.comp (measurable_pi_apply i).subtype_val
  simpa [recoverOrthant, g] using
    ((PiLp.continuous_toLp (p := 2) (β := fun _ : Fin d ↦ ℝ)).measurable.comp hg)

/-- Helper for Exercise 15.1.2: after applying `-log` to the compactification, one recovers
`max (x i) 0` in each coordinate. -/
lemma recoverOrthant_compactifyOrthant_apply (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    recoverOrthant (compactifyOrthant x) i = max (x i) 0 := by
  change -Real.log (Real.exp (-max (x i) 0)) = max (x i) 0
  rw [Real.log_exp]
  ring

/-- Helper for Exercise 15.1.2: the negative inner product with a natural exponent vector is the
coordinate sum of the corresponding negative monomial exponents. -/
lemma negInner_natCast_eq_sum (n : Fin d → ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    -inner ℝ (natExponentVector (d := d) n) x = ∑ i, -((n i : ℝ) * x i) := by
  rw [PiLp.inner_apply]
  have hterm :
      ∀ i : Fin d, inner ℝ (natExponentVector (d := d) n i) (x i) = (n i : ℝ) * x i := by
    intro i
    rw [natExponentVector_apply]
    -- Normalize the scalar inner product directly in `ℝ` to avoid extra `inner ℝ 1 _` terms.
    simpa using (RCLike.inner_apply' (n i : ℝ) (x i))
  calc
    -- Replace each coordinatewise inner product by the corresponding scalar product.
    -∑ i, inner ℝ (natExponentVector (d := d) n i) (x i)
        = -∑ i, ((n i : ℝ) * x i) := by
            congr 1
            exact Finset.sum_congr rfl fun i _ ↦ hterm i
    _ = ∑ i, -((n i : ℝ) * x i) := by rw [Finset.sum_neg_distrib]

/-- Helper for Exercise 15.1.2: on the nonnegative orthant, mapping into the cube and then
recovering by `-log` leaves the measure unchanged. -/
lemma map_recoverOrthant_map_compactifyOrthant_eq_self_of_ae_nonneg
    {ρ : Measure (EuclideanSpace ℝ (Fin d))} (hρ_nonneg : ∀ᵐ x ∂ρ, ∀ i, 0 ≤ x i) :
    Measure.map recoverOrthant (Measure.map compactifyOrthant ρ) = ρ := by
  -- First collapse the double pushforward to the composition `recoverOrthant ∘ compactifyOrthant`.
  rw [AEMeasurable.map_map_of_aemeasurable measurable_recoverOrthant.aemeasurable
    continuous_compactifyOrthant.measurable.aemeasurable]
  -- Then use the orthant support to replace `max (x i) 0` by `x i` almost everywhere.
  calc
    Measure.map (recoverOrthant ∘ compactifyOrthant) ρ
        = Measure.map (fun x : EuclideanSpace ℝ (Fin d) ↦ x) ρ := by
            refine Measure.map_congr <| hρ_nonneg.mono fun x hx ↦ ?_
            ext i
            change recoverOrthant (compactifyOrthant x) i = x i
            rw [recoverOrthant_compactifyOrthant_apply]
            exact max_eq_left (hx i)
    _ = ρ := Measure.map_id'

/-- Helper for Exercise 15.1.2: integrating a cube monomial against the compactified law rewrites
to the Laplace transform at the corresponding natural vector. -/
lemma integral_cubeMonomial_map_compactifyOrthant_eq_mgf
    {ρ : Measure (EuclideanSpace ℝ (Fin d))} [IsFiniteMeasure ρ]
    (hρ_nonneg : ∀ᵐ x ∂ρ, ∀ i, 0 ≤ x i) (n : Fin d → ℕ) :
    ∫ y, cubeMonomial (d := d) n y ∂Measure.map compactifyOrthant ρ =
      mgf (fun x ↦ -inner ℝ (natExponentVector (d := d) n) x) ρ 1 := by
  rw [ProbabilityTheory.mgf]
  -- Pull the bounded cube monomial back along the compactification map.
  rw [MeasureTheory.integral_map
    continuous_compactifyOrthant.measurable.aemeasurable
    (cubeMonomial (d := d) n).continuous.aestronglyMeasurable]
  -- On the orthant support, the pulled-back monomial is exactly the Laplace kernel.
  refine integral_congr_ae <| hρ_nonneg.mono fun x hx ↦ ?_
  calc
    cubeMonomial (d := d) n (compactifyOrthant x)
        = ∏ i, (Real.exp (-max (x i) 0)) ^ n i := by
            simp [cubeMonomial, compactifyOrthant]
    _ = ∏ i, (Real.exp (-x i)) ^ n i := by
          refine Finset.prod_congr rfl fun i _ ↦ ?_
          congr 2
          rw [max_eq_left (hx i)]
    _ = ∏ i, Real.exp (-((n i : ℝ) * x i)) := by
          refine Finset.prod_congr rfl fun i _ ↦ ?_
          rw [← Real.exp_nat_mul]
          congr 1
          ring
    _ = Real.exp (∑ i, -((n i : ℝ) * x i)) := by
          rw [← Real.exp_sum]
    _ = Real.exp (-inner ℝ (natExponentVector (d := d) n) x) := by
          rw [negInner_natCast_eq_sum]
    _ = (fun ω ↦ Real.exp (1 * -inner ℝ (natExponentVector (d := d) n) ω)) x := by
          simp

/-- Helper for Exercise 15.1.2: equality of Laplace transforms implies equality of the compactified
pushforward measures on the cube. -/
lemma map_compactifyOrthant_eq_of_laplace_eq
    (hμ_nonneg : ∀ᵐ x ∂μ, ∀ i, 0 ≤ x i)
    (hν_nonneg : ∀ᵐ x ∂ν, ∀ i, 0 ≤ x i)
    (hL :
      ∀ t : EuclideanSpace ℝ (Fin d),
        (∀ i, 0 ≤ t i) → mgf (fun x ↦ -inner ℝ t x) μ 1 = mgf (fun x ↦ -inner ℝ t x) ν 1) :
    Measure.map compactifyOrthant μ = Measure.map compactifyOrthant ν := by
  let μc : FiniteMeasure (OrthantCube d) := ⟨Measure.map compactifyOrthant μ, inferInstance⟩
  let νc : FiniteMeasure (OrthantCube d) := ⟨Measure.map compactifyOrthant ν, inferInstance⟩
  let 𝒞 : Set (BoundedContinuousFunction (OrthantCube d) ℝ) := Set.range (cubeMonomial (d := d))
  have hsep :
      Set.SeparatesPoints
        ((fun f : BoundedContinuousFunction (OrthantCube d) ℝ ↦ (f : OrthantCube d → ℝ)) '' 𝒞) := by
    intro y z hyz
    have hcoord : ∃ i, (y i : ℝ) ≠ (z i : ℝ) := by
      by_contra hcoord
      apply hyz
      ext i
      simpa using not_exists.mp hcoord i
    rcases hcoord with ⟨i, hi⟩
    refine ⟨cubeMonomial (d := d) (Pi.single i 1), ?_, ?_⟩
    · exact ⟨cubeMonomial (d := d) (Pi.single i 1), ⟨Pi.single i 1, rfl⟩, rfl⟩
    · simpa [cubeMonomial, Pi.single_apply] using hi
  have hmul :
      ∀ ⦃f g : BoundedContinuousFunction (OrthantCube d) ℝ⦄,
        f ∈ 𝒞 → g ∈ 𝒞 → f * g ∈ 𝒞 := by
    intro f g hf hg
    rcases hf with ⟨m, rfl⟩
    rcases hg with ⟨n, rfl⟩
    refine ⟨fun i ↦ m i + n i, ?_⟩
    ext y
    simp [cubeMonomial, pow_add, Finset.prod_mul_distrib]
  have hone : (1 : BoundedContinuousFunction (OrthantCube d) ℝ) ∈ 𝒞 := by
    refine ⟨0, ?_⟩
    ext y
    simp [cubeMonomial]
  have hint :
      ∀ ⦃f : BoundedContinuousFunction (OrthantCube d) ℝ⦄,
        f ∈ 𝒞 →
          ∫ y, (f : OrthantCube d → ℝ) y ∂(μc : Measure (OrthantCube d)) =
            ∫ y, (f : OrthantCube d → ℝ) y ∂(νc : Measure (OrthantCube d)) := by
    intro f hf
    rcases hf with ⟨n, rfl⟩
    -- Rewrite both cube integrals back to the Laplace transform hypothesis at the natural vector.
    calc
      ∫ y, cubeMonomial (d := d) n y ∂(μc : Measure (OrthantCube d))
          = mgf (fun x ↦ -inner ℝ (natExponentVector (d := d) n) x) μ 1 := by
              simpa [μc] using
                integral_cubeMonomial_map_compactifyOrthant_eq_mgf (d := d) (ρ := μ) hμ_nonneg n
      _ = mgf (fun x ↦ -inner ℝ (natExponentVector (d := d) n) x) ν 1 := by
            exact hL (natExponentVector (d := d) n)
              (natExponentVector_nonneg (d := d) n)
      _ = ∫ y, cubeMonomial (d := d) n y ∂(νc : Measure (OrthantCube d)) := by
            simpa [νc] using
              (integral_cubeMonomial_map_compactifyOrthant_eq_mgf
                (d := d) (ρ := ν) hν_nonneg n).symm
  have hμcνc : μc = νc :=
    finiteMeasure_eq_of_forall_mem_integral_eq_of_separating_boundedContinuousFamily
      hsep hmul hone hint
  exact congrArg (fun ξ : FiniteMeasure (OrthantCube d) ↦ (ξ : Measure (OrthantCube d))) hμcνc

-- Route correction: the initial characteristic-function sketch does not cover mixed-sign
-- frequencies. Instead, compactify `[0, ∞)^d` into `[0, 1]^d`, use monomials as a separating
-- class there, and recover the original measure by `-log`.
/-- Exercise 15.1.2: finite measures on `[0, ∞)^d` are determined by their Laplace transforms. If
two finite measures on `ℝ^d` are supported on the nonnegative orthant and have the same Laplace
transform at every nonnegative vector `t`, then the measures are equal. -/
theorem eq_of_laplaceTransform_eq_on_nonnegativeOrthant
    (hμ_nonneg : ∀ᵐ x ∂μ, ∀ i, 0 ≤ x i)
    (hν_nonneg : ∀ᵐ x ∂ν, ∀ i, 0 ≤ x i)
    (hL :
      ∀ t : EuclideanSpace ℝ (Fin d),
        (∀ i, 0 ≤ t i) → mgf (fun x ↦ -inner ℝ t x) μ 1 = mgf (fun x ↦ -inner ℝ t x) ν 1) :
    μ = ν := by
  -- Compare the compactified laws on the cube via the separating monomial family.
  have hmap :
      Measure.map compactifyOrthant μ = Measure.map compactifyOrthant ν :=
    map_compactifyOrthant_eq_of_laplace_eq (d := d) hμ_nonneg hν_nonneg hL
  -- Then map back with `-log`; the orthant support shows this recovers the original measures.
  calc
    μ = Measure.map recoverOrthant (Measure.map compactifyOrthant μ) := by
          symm
          exact map_recoverOrthant_map_compactifyOrthant_eq_self_of_ae_nonneg
            (d := d) (ρ := μ) hμ_nonneg
    _ = Measure.map recoverOrthant (Measure.map compactifyOrthant ν) := by rw [hmap]
    _ = ν := map_recoverOrthant_map_compactifyOrthant_eq_self_of_ae_nonneg
          (d := d) (ρ := ν) hν_nonneg

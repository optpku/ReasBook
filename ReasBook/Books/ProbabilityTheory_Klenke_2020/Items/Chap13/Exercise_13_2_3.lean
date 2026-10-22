/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_25
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_12
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.MeasureTheory.Order.UpperLower

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Bornology
open Submodule Pointwise
open scoped BigOperators Topology NNReal ENNReal Pointwise

noncomputable section

/-- The finite measure obtained by restricting Lebesgue measure to the unit interval. -/
def unit_interval_restrict_volume : FiniteMeasure ℝ :=
  ⟨volume.restrict (Set.Icc (0 : ℝ) 1), inferInstance⟩

/-- The canonical uniform empirical distribution on the mesh
`{k / (n + 1) | 0 ≤ k ≤ n + 1}`. -/
noncomputable def unit_interval_mesh_distribution (n : ℕ) : ProbabilityMeasure ℝ :=
  empiricalDistributionTuple (fun k : Fin (Nat.succPNat (n + 1)) ↦ (k : ℝ) / (n + 1 : ℝ))

/-- The empirical finite-measure sequence on the uniform mesh `{k / (n + 1) | 0 ≤ k ≤ n + 1}`.
This keeps the textbook weights `1 / (n + 1)` while deriving the mesh data from the Chapter 12
owner abstraction `empiricalDistributionTuple`. -/
def unit_interval_dirac_riemann_sequence (n : ℕ) : FiniteMeasure ℝ :=
  ((n + 2 : ℝ≥0) / (n + 1 : ℝ≥0)) • (unit_interval_mesh_distribution n).toFiniteMeasure

/-- Helper for Exercise 13.2.3: integrating a bounded continuous test function against the mesh
measure gives the explicit endpoint Riemann sum with denominator `n + 1`. -/
lemma integral_unitIntervalDiracRiemannSequence_eq_sum (f : BoundedContinuousFunction ℝ ℝ) (n : ℕ) :
    ∫ x, f x ∂(unit_interval_dirac_riemann_sequence n : Measure ℝ) =
      (1 / (n + 1 : ℝ)) * ∑ k : Fin (n + 2), f ((k : ℝ) / (n + 1 : ℝ)) := by
  -- Route correction: unfold the finite measure directly instead of relying on a fragile
  -- definitional `change` through the coercion `FiniteMeasure ℝ → Measure ℝ`.
  rw [unit_interval_dirac_riemann_sequence]
  rw [FiniteMeasure.toMeasure_smul]
  have hsmulMeasure :
      (((n + 2 : ℝ≥0) / (n + 1 : ℝ≥0)) •
          ((unit_interval_mesh_distribution n).toFiniteMeasure : Measure ℝ)) =
        ((((n + 2 : ℝ≥0) / (n + 1 : ℝ≥0) : ℝ≥0∞) •
          ((unit_interval_mesh_distribution n).toFiniteMeasure : Measure ℝ))) := by
    ext s hs
    simp [smul_eq_mul]
  rw [hsmulMeasure]
  rw [integral_smul_measure]
  rw [unit_interval_mesh_distribution]
  rw [ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure]
  rw [empiricalDistributionTuple, empiricalDistribution_toMeasure]
  rw [integral_smul_measure]
  rw [integral_finset_sum_measure]
  · simp only [integral_dirac, smul_eq_mul]
    have hcoeff :
        (((((n + 2 : ℝ≥0) / (n + 1 : ℝ≥0)) : ℝ≥0∞).toReal) *
            ((((Nat.succPNat (n + 1) : ℕ+) : ℝ≥0∞)⁻¹).toReal)) =
          (1 / (n + 1 : ℝ)) := by
      have hTwo : (n + 2 : ℝ) ≠ 0 := by positivity
      have hOne : (n + 1 : ℝ) ≠ 0 := by positivity
      have hnum :
          ((((n + 2 : ℝ≥0) / (n + 1 : ℝ≥0)) : ℝ≥0∞).toReal) =
            ((n + 2 : ℝ) / (n + 1 : ℝ)) := by
        rw [ENNReal.toReal_div]
        rfl
      have hcard :
          (((Nat.succPNat (n + 1) : ℕ+) : ℝ≥0∞)) = (n + 2 : ℝ≥0∞) := by
        have hcardNat : (((Nat.succPNat (n + 1) : ℕ+) : ℕ)) = n + 2 := by
          simp [Nat.succPNat_coe, Nat.succ_eq_add_one, add_assoc]
        exact_mod_cast hcardNat
      have hden :
          ((((Nat.succPNat (n + 1) : ℕ+) : ℝ≥0∞)⁻¹).toReal) = ((n + 2 : ℝ)⁻¹) := by
        rw [hcard, ENNReal.toReal_inv]
        rfl
      -- Proof comment: convert the NNReal/ENNReal coefficients to real numbers first, then close
      -- the remaining scalar identity in `ℝ`.
      calc
        (((((n + 2 : ℝ≥0) / (n + 1 : ℝ≥0)) : ℝ≥0∞).toReal) *
            ((((Nat.succPNat (n + 1) : ℕ+) : ℝ≥0∞)⁻¹).toReal))
            = (((n + 2 : ℝ) / (n + 1 : ℝ)) * ((n + 2 : ℝ)⁻¹)) := by
                rw [hnum, hden]
        _ = (1 / (n + 1 : ℝ)) := by
          field_simp [hTwo, hOne]
    rw [← mul_assoc, hcoeff]
    rfl
  · intro k hk
    exact f.integrable _

/-- Helper for Exercise 13.2.3: transport the one-dimensional box integral from `Fin 1 → ℝ` to the
ordinary interval integral on `ℝ`. -/
lemma liftedUnitIntervalIntegral_eq_restrictVolumeIntegral (f : BoundedContinuousFunction ℝ ℝ) :
    (∫ y in Set.Icc ![(0 : ℝ)] ![1], f (y 0) ∂volume) = ∫ x in Set.Icc (0 : ℝ) 1, f x ∂volume := by
  let g : (Fin 1 → ℝ) → ℝ := fun y ↦ f (y 0)
  have h_transport : ∀ (u v : Fin 1 → ℝ) (h : (Fin 1 → ℝ) → ℝ),
      ∫ y in Set.Icc u v, h y ∂volume = ∫ x in Set.Icc (u 0) (v 0), h (fun _ ↦ x) ∂volume :=
    fun u v h ↦ by
      -- The unique coordinate measurable equivalence preserves volume and sends the box interval to
      -- the corresponding real interval.
      convert
        (((MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm _).setIntegral_preimage_emb
          (MeasurableEquiv.measurableEmbedding _) h _).symm
      exact ((OrderIso.funUnique (Fin 1) ℝ).symm.preimage_Icc u v).symm
  simpa [g] using h_transport ![(0 : ℝ)] ![1] g

/-- Helper for Exercise 13.2.3: the lattice points of the one-dimensional unit box with mesh
`1 / m` are exactly the points `k / m` for `k : Fin (m + 1)`. -/
lemma tsum_liftedUnitInterval_eq_sum (f : BoundedContinuousFunction ℝ ℝ) (m : ℕ) [NeZero m] :
    (∑' y : ↑(Set.Icc ![(0 : ℝ)] ![1] ∩
        ((m : ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 1))))), f (y.1 0)) =
      ∑ k : Fin (m + 1), f ((k : ℝ) / (m : ℝ)) := by
  let s : Set (Fin 1 → ℝ) :=
    Set.Icc ![(0 : ℝ)] ![1] ∩
      ((m : ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 1))))
  let meshPoint : Fin (m + 1) → s := fun k ↦
    ⟨fun _ ↦ (k : ℝ) / (m : ℝ), by
      constructor
      · -- Proof comment: the point `k / m` lies in `[0,1]` because `0 ≤ k ≤ m`.
        constructor <;> intro i <;> fin_cases i
        · exact div_nonneg (by positivity) (by positivity)
        · have hk_le : (k : ℝ) ≤ m := by
            exact_mod_cast Nat.le_of_lt_succ k.2
          have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_neZero m)
          have hdiv : (k : ℝ) / (m : ℝ) ≤ 1 := by
            refine (div_le_iff₀ hm_pos).2 ?_
            simpa using hk_le
          simpa using hdiv
      · -- Proof comment: multiplying the unique coordinate by `m` recovers the integer `k`.
        simpa using
          (BoxIntegral.unitPartition.mem_smul_span_iff
            (n := m) (v := fun _ : Fin 1 ↦ (k : ℝ) / (m : ℝ))).2
            (by
              intro i
              fin_cases i
              refine ⟨(k : ℤ), ?_⟩
              change ((k : ℤ) : ℝ) = (m : ℝ) * ((k : ℝ) / (m : ℝ))
              field_simp [Nat.cast_ne_zero.mpr (NeZero.ne m)]
              norm_num)⟩
  have hmesh_injective : Function.Injective meshPoint := by
    intro k₁ k₂ hk
    apply Fin.ext
    have hcoord := congrArg (fun y : s ↦ y.1 0) hk
    simpa [meshPoint] using (div_left_inj' (Nat.cast_ne_zero.mpr (NeZero.ne m))).mp hcoord
  have hmesh_surjective : Function.Surjective meshPoint := by
    intro y
    have hyIcc : y.1 ∈ Set.Icc ![(0 : ℝ)] ![1] := y.2.1
    have hySpan :
        y.1 ∈ ((m : ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 1)))) := y.2.2
    let a : ℤ := BoxIntegral.unitPartition.index m y.1 0 + 1
    have hcoord :
        ((a : ℝ) / (m : ℝ)) = y.1 0 := by
      have htag :=
        congrArg (fun x : Fin 1 → ℝ ↦ x 0)
          (BoxIntegral.unitPartition.tag_index_eq_self_of_mem_smul_span (n := m) hySpan)
      simpa [a, BoxIntegral.unitPartition.tag_apply] using htag
    have hy0_nonneg : 0 ≤ y.1 0 := by
      simpa [Set.mem_Icc, Pi.le_def] using hyIcc.1 0
    have hy0_le_one : y.1 0 ≤ 1 := by
      simpa [Set.mem_Icc, Pi.le_def] using hyIcc.2 0
    have hmul : (a : ℝ) = y.1 0 * (m : ℝ) := by
      exact (div_eq_iff (Nat.cast_ne_zero.mpr (NeZero.ne m))).mp (by simpa [mul_comm] using hcoord)
    have ha_nonneg : 0 ≤ a := by
      have hreal : (0 : ℝ) ≤ a := by
        nlinarith [hmul, hy0_nonneg]
      exact_mod_cast hreal
    have ha_le : a ≤ m := by
      have hreal : (a : ℝ) ≤ m := by
        nlinarith [hmul, hy0_le_one]
      exact_mod_cast hreal
    have hk_int : (Int.toNat a : ℤ) ≤ m := by
      rw [Int.toNat_of_nonneg ha_nonneg]
      exact ha_le
    have hk_le : Int.toNat a ≤ m := by
      exact_mod_cast hk_int
    have hk_lt : Int.toNat a < m + 1 := lt_of_le_of_lt hk_le (Nat.lt_succ_self m)
    have htoNat_cast : ((Int.toNat a : ℕ) : ℝ) = a := by
      exact_mod_cast (Int.toNat_of_nonneg ha_nonneg)
    refine ⟨⟨Int.toNat a, hk_lt⟩, ?_⟩
    apply Subtype.ext
    ext i
    fin_cases i
    calc
      ((Int.toNat a : ℕ) : ℝ) / (m : ℝ) = (a : ℝ) / (m : ℝ) := by
        rw [htoNat_cast]
      _ = y.1 0 := hcoord
  let e : Fin (m + 1) ≃ s := Equiv.ofBijective meshPoint ⟨hmesh_injective, hmesh_surjective⟩
  letI : Fintype s := Fintype.ofEquiv (Fin (m + 1)) e
  -- Proof comment: after identifying the lattice subtype with `Fin (m + 1)`, the infinite sum is
  -- just the corresponding finite sum over the mesh points `k / m`.
  calc
    ∑' y : s, f (y.1 0) = ∑ y : s, f (y.1 0) := by simp
    _ = ∑ k : Fin (m + 1), f ((e k).1 0) := by
      simpa using (e.sum_comp fun y : s ↦ f (y.1 0)).symm
    _ = ∑ k : Fin (m + 1), f ((k : ℝ) / (m : ℝ)) := by
      simp [e, meshPoint]

/-- Helper for Exercise 13.2.3: the endpoint Riemann sums on the mesh `{k / (n + 1)}` converge to
the Lebesgue integral on `[0,1]`. -/
lemma tendsto_unitIntervalLatticeSums (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun n : ℕ ↦ (1 / (n + 1 : ℝ)) * ∑ k : Fin (n + 2), f ((k : ℝ) / (n + 1 : ℝ)))
      atTop (𝓝 (∫ x in Set.Icc (0 : ℝ) 1, f x ∂volume)) := by
  let g : (Fin 1 → ℝ) → ℝ := fun y ↦ f (y 0)
  have hg : Continuous g := by
    -- Proof comment: the lifted test function is continuous because it is the composition of `f`
    -- with the unique-coordinate evaluation map.
    simpa [g] using f.continuous.comp (continuous_apply 0)
  have hbox :
      Tendsto
        (fun m : ℕ ↦
          (∑' y : ↑(Set.Icc ![(0 : ℝ)] ![1] ∩
              ((m : ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 1))))), g y) /
            m ^ Fintype.card (Fin 1))
        atTop (𝓝 (∫ y in Set.Icc ![(0 : ℝ)] ![1], g y ∂volume)) := by
    -- Proof comment: this is the one-dimensional specialization of the unit-partition lattice
    -- convergence theorem on `Fin 1 → ℝ`.
    refine tendsto_tsum_div_pow_atTop_integral
      (s := Set.Icc ![(0 : ℝ)] ![1]) (F := g) hg ?_ ?_ ?_
    · simpa using (isCompact_Icc : IsCompact (Set.Icc ![(0 : ℝ)] ![1])).isBounded
    · simp only [measurableSet_Icc]
    · simpa using
        (Set.OrdConnected.null_frontier
          (Set.ordConnected_Icc :
            Set.OrdConnected (Set.Icc ![(0 : ℝ)] ![1] : Set (Fin 1 → ℝ))))
  have hshift := hbox.comp (tendsto_add_atTop_nat 1)
  -- Proof comment: shifting from `m` to `n + 1` avoids the singular denominator at `m = 0` and
  -- matches the textbook indexing of the mesh measures.
  convert hshift using 1
  · ext n
    simp [Function.comp, g, pow_one, div_eq_mul_inv, mul_comm, tsum_liftedUnitInterval_eq_sum]
  · simpa [g] using (liftedUnitIntervalIntegral_eq_restrictVolumeIntegral f).symm

-- Proof sketch: use `FiniteMeasure.tendsto_iff_forall_integral_tendsto` to test weak convergence
-- against bounded continuous real-valued functions. The resulting integrals are the Riemann sums
-- `(1 / (n + 1)) * ∑_{k=0}^{n+1} f (k / (n + 1))`, which converge to `∫_[0,1] f dλ`; the extra
-- endpoint term is of order `(n + 1)⁻¹` and therefore does not change the limit.
/-- Exercise 13.2.3: after the harmless reindexing `n ↦ n + 1` needed to avoid the undefined term
`1 / 0`, the empirical measures `μₙ = (1 / n) ∑_{k=0}^n δ_{k / n}` converge weakly to Lebesgue
measure restricted to `[0,1]`. -/
theorem unit_interval_dirac_riemann_sequence_tendsto_restrict_volume :
    Tendsto unit_interval_dirac_riemann_sequence atTop (𝓝 unit_interval_restrict_volume) := by
  rw [FiniteMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  -- Proof comment: weak convergence of finite measures is equivalent to convergence of all bounded
  -- continuous real-valued test integrals, and the previous helpers identify those integrals with
  -- the endpoint Riemann sums from the exercise.
  simpa [integral_unitIntervalDiracRiemannSequence_eq_sum, unit_interval_restrict_volume] using
    tendsto_unitIntervalLatticeSums f

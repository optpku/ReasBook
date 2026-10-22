/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Helper for Exercise 8.2.7: reindexing the finite total sum by a transposition does not change
its value. -/
lemma swap_sum_apply_eq_sum_apply {n : ℕ} {X : Fin n → Ω → ℝ} (i j : Fin n) (ω : Ω) :
    ∑ k : Fin n, X (Equiv.swap i j k) ω = ∑ k : Fin n, X k ω := by
  -- Reindex the finite sum along the permutation `swap i j`.
  simpa using (Equiv.sum_comp (Equiv.swap i j) (fun k : Fin n ↦ X k ω))

/-- Helper for Exercise 8.2.7: swapping two coordinates in a finite i.i.d. family preserves the
joint law of one chosen coordinate together with the total sum. -/
lemma coordinateWithSum_identDistrib_of_isIID {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX_iid : IsIID X P) (i j : Fin n) :
    IdentDistrib (fun ω ↦ (X i ω, ∑ k : Fin n, X k ω))
      (fun ω ↦ (X j ω, ∑ k : Fin n, X k ω)) P P := by
  let ρ : Fin n ≃ Fin n := Equiv.swap i j
  -- Push the i.i.d. vector law through the coordinate permutation `ρ`.
  have hvec :
      IdentDistrib (fun ω ↦ fun k : Fin n => X k ω)
        (fun ω ↦ fun k : Fin n => X (ρ k) ω) P P := by
    refine IdentDistrib.pi (μ := P) (ν := P)
      (X := fun k : Fin n ↦ X k) (Y := fun k : Fin n ↦ X (ρ k)) ?_ hX_iid.iIndepFun ?_
    · intro k
      simpa [ρ] using hX_iid.identDistrib k (ρ k)
    · simpa [ρ] using hX_iid.iIndepFun.precomp (g := ρ) ρ.injective
  have hextract_meas : Measurable (fun v : Fin n → ℝ ↦ (v i, ∑ k : Fin n, v k)) := by
    -- The extractor keeps one coordinate and the finite total sum.
    refine measurable_pi_apply i |>.prodMk ?_
    exact Finset.measurable_sum Finset.univ fun k _ ↦ measurable_pi_apply k
  let extract : (Fin n → ℝ) → ℝ × ℝ := fun v ↦ (v i, ∑ k : Fin n, v k)
  have hpair_perm :
      IdentDistrib (extract ∘ fun ω ↦ fun k : Fin n => X k ω)
        (extract ∘ fun ω ↦ fun k : Fin n => X (ρ k) ω) P P := by
    simpa [extract] using hvec.comp hextract_meas
  have hleft :
      (extract ∘ fun ω ↦ fun k : Fin n => X k ω) =
        fun ω ↦ (X i ω, ∑ k : Fin n, X k ω) := by
    funext ω
    simp [extract]
  have hright :
      (extract ∘ fun ω ↦ fun k : Fin n => X (ρ k) ω) =
        fun ω ↦ (X j ω, ∑ k : Fin n, X k ω) := by
    funext ω
    simp [extract, ρ, swap_sum_apply_eq_sum_apply]
  -- Route correction: normalize the second component with the explicit swapped-sum bridge before
  -- comparing against the theorem's target spelling.
  simpa [hleft, hright] using hpair_perm

/-- Helper for Exercise 8.2.7: coordinates have the same set integral on every
`σ(∑ j, X j)`-measurable set. -/
lemma coordinate_setIntegral_eq_of_sumMeasurableSet {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX_meas : ∀ i, Measurable (X i)) (hX_iid : IsIID X P) (i j : Fin n)
    {s : Set Ω}
    (hs :
      MeasurableSet[MeasurableSpace.comap (fun ω ↦ ∑ k : Fin n, X k ω) inferInstance] s) :
    ∫ ω in s, X i ω ∂P = ∫ ω in s, X j ω ∂P := by
  let sumX : Ω → ℝ := fun ω ↦ ∑ k : Fin n, X k ω
  have hsumX_meas : Measurable sumX := by
    -- The total sum is measurable as a finite sum of measurable coordinates.
    refine Finset.measurable_sum Finset.univ fun k _ ↦ hX_meas k
  rcases MeasurableSpace.measurableSet_comap.mp hs with ⟨t, ht, rfl⟩
  classical
  let φ : ℝ × ℝ → ℝ := fun p ↦ p.1 * Set.indicator t (fun _ ↦ (1 : ℝ)) p.2
  have hφ_meas : Measurable φ := by
    -- The test function multiplies the coordinate by the measurable indicator of the sum event.
    refine measurable_fst.mul ?_
    exact (measurable_const.indicator ht).comp measurable_snd
  have hφ_int :
      ∫ ω, φ (X i ω, sumX ω) ∂P = ∫ ω, φ (X j ω, sumX ω) ∂P := by
    -- Identical distribution of the pairs transfers equality of these test integrals.
    simpa [sumX] using
      ((coordinateWithSum_identDistrib_of_isIID hX_iid i j).comp hφ_meas).integral_eq
  have hpre : MeasurableSet (sumX ⁻¹' t) := hsumX_meas ht
  have hφ_i : (fun ω ↦ φ (X i ω, sumX ω)) = Set.indicator (sumX ⁻¹' t) (X i) := by
    funext ω
    by_cases hω : sumX ω ∈ t <;> simp [φ, hω, sumX]
  have hφ_j : (fun ω ↦ φ (X j ω, sumX ω)) = Set.indicator (sumX ⁻¹' t) (X j) := by
    funext ω
    by_cases hω : sumX ω ∈ t <;> simp [φ, hω, sumX]
  -- Rewrite the indicator-test integrals as the requested set integrals.
  calc
    ∫ ω in sumX ⁻¹' t, X i ω ∂P = ∫ ω, φ (X i ω, sumX ω) ∂P := by
      rw [hφ_i]
      symm
      exact integral_indicator hpre
    _ = ∫ ω, φ (X j ω, sumX ω) ∂P := hφ_int
    _ = ∫ ω in sumX ⁻¹' t, X j ω ∂P := by
      rw [hφ_j]
      exact integral_indicator hpre

/-- Helper for Exercise 8.2.7: all coordinate conditional expectations with respect to the total
sum agree almost surely. -/
lemma condExp_coordinate_ae_eq_of_sumSigma {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX_meas : ∀ i, Measurable (X i)) (hX_iid : IsIID X P) (i j : Fin n)
    (hXi_int : Integrable (X i) P) :
    P[X j | MeasurableSpace.comap (fun ω ↦ ∑ k : Fin n, X k ω) inferInstance] =ᵐ[P]
      P[X i | MeasurableSpace.comap (fun ω ↦ ∑ k : Fin n, X k ω) inferInstance] := by
  let sumX : Ω → ℝ := fun ω ↦ ∑ k : Fin n, X k ω
  have hsumX_meas : Measurable sumX := by
    -- The conditioning variable is the measurable total sum.
    refine Finset.measurable_sum Finset.univ fun k _ ↦ hX_meas k
  have hXj_int : Integrable (X j) P := by
    -- Integrability propagates across identical distribution of the coordinates.
    simpa using (hX_iid.identDistrib i j).integrable_snd hXi_int
  have hm : MeasurableSpace.comap sumX inferInstance ≤ mΩ := hsumX_meas.comap_le
  -- Uniqueness of conditional expectation reduces the goal to equality of all measurable set
  -- integrals on `σ(sumX)`.
  simpa [sumX] using
    (ae_eq_condExp_of_forall_setIntegral_eq (μ := P)
      (m := MeasurableSpace.comap sumX inferInstance) (m₀ := mΩ)
      (f := X i) (g := P[X j | MeasurableSpace.comap sumX inferInstance]) hm hXi_int
      (fun s hs hPs ↦ integrable_condExp.integrableOn)
      (fun s hs hPs ↦ by
        calc
          ∫ ω in s, P[X j | MeasurableSpace.comap sumX inferInstance] ω ∂P =
              ∫ ω in s, X j ω ∂P := by
            exact setIntegral_condExp hm hXj_int hs
          _ = ∫ ω in s, X i ω ∂P := by
            symm
            exact coordinate_setIntegral_eq_of_sumMeasurableSet hX_meas hX_iid i j hs)
      (stronglyMeasurable_condExp (m := MeasurableSpace.comap sumX inferInstance)
        (μ := P) (f := X j)).aestronglyMeasurable)

-- Proof sketch: by exchangeability of an i.i.d. finite family, the pairs
-- `(X i, fun ω ↦ ∑ j : Fin n, X j ω)` and `(X j, fun ω ↦ ∑ j : Fin n, X j ω)` have the same law,
-- so the conditional expectations of the coordinates given the total sum agree almost surely.
-- Use identical distribution to propagate integrability from the chosen coordinate `X i` to every
-- other coordinate. Summing the equal conditional expectations over all coordinates and using
-- `condExp_finset_sum` together with `condExp_of_measurable_ae_eq` for the total sum yields
-- `n * P[X i | σ(S_n)] = S_n`, hence `P[X i | σ(S_n)] = S_n / n`.
/-- Exercise 8.2.7: for a measurable i.i.d. family `X : Fin n → Ω → ℝ`, the conditional
expectation of any integrable coordinate given the total sum is almost surely the sample mean. -/
theorem condExp_coordinate_given_sum_ae_eq_average {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX_meas : ∀ i, Measurable (X i)) (hX_iid : IsIID X P) (i : Fin n)
    (hXi_int : Integrable (X i) P) :
    P[X i | MeasurableSpace.comap (fun ω ↦ ∑ j : Fin n, X j ω) inferInstance] =ᵐ[P]
      fun ω ↦ (∑ j : Fin n, X j ω) / n := by
  let sumX : Ω → ℝ := fun ω ↦ ∑ j : Fin n, X j ω
  have hsum_fun_eq : (sumX : Ω → ℝ) = ∑ j : Fin n, X j := by
    funext ω
    simp [sumX]
  have hsumX_meas : Measurable sumX := by
    -- The total sum is measurable as a finite sum of measurable coordinates.
    refine Finset.measurable_sum Finset.univ fun j _ ↦ hX_meas j
  have hX_int : ∀ j : Fin n, Integrable (X j) P := by
    intro j
    -- Every coordinate inherits integrability from the chosen one by identical distribution.
    simpa using (hX_iid.identDistrib i j).integrable_snd hXi_int
  have hsumX_int : Integrable sumX P := by
    -- The total sum stays integrable because it is a finite sum of integrable terms.
    simpa [sumX] using integrable_finset_sum Finset.univ fun j _ ↦ hX_int j
  have hsum_fun_eq_ae : (sumX : Ω → ℝ) =ᵐ[P] ∑ j : Fin n, X j :=
    Filter.EventuallyEq.of_eq (l := ae P) hsum_fun_eq
  have hcoords_sum :
      (∑ j : Fin n, P[X j | MeasurableSpace.comap sumX inferInstance]) =ᵐ[P]
        fun ω ↦ (n : ℝ) * P[X i | MeasurableSpace.comap sumX inferInstance] ω := by
    have hall :
        ∀ᵐ ω ∂P, ∀ j : Fin n,
          P[X j | MeasurableSpace.comap sumX inferInstance] ω =
            P[X i | MeasurableSpace.comap sumX inferInstance] ω := by
      rw [ae_all_iff]
      intro j
      exact condExp_coordinate_ae_eq_of_sumSigma hX_meas hX_iid i j hXi_int
    -- Sum the coordinatewise a.e.-equal conditional expectations pointwise.
    filter_upwards [hall] with ω hω
    simp [hω, nsmul_eq_mul]
  have hcond_sum' :
      P[∑ j : Fin n, X j | MeasurableSpace.comap sumX inferInstance] =ᵐ[P]
        ∑ j : Fin n, P[X j | MeasurableSpace.comap sumX inferInstance] := by
    -- Conditional expectation is linear over finite sums.
    exact condExp_finset_sum (μ := P) (s := Finset.univ) (f := X)
      (fun j _ ↦ hX_int j) (MeasurableSpace.comap sumX inferInstance)
  have hcond_sum_self :
      P[∑ j : Fin n, X j | MeasurableSpace.comap sumX inferInstance] =ᵐ[P]
        ∑ j : Fin n, X j := by
    -- Conditioning a measurable integrable function on its generated σ-algebra returns itself.
    have hsum_meas' : Measurable[MeasurableSpace.comap sumX inferInstance] (∑ j : Fin n, X j) := by
      rw [← hsum_fun_eq]
      exact comap_measurable sumX
    have hsum_int' : Integrable (∑ j : Fin n, X j) P := by
      convert hsumX_int using 1
      ext ω
      simp [sumX]
    exact Filter.EventuallyEq.of_eq (l := ae P) <|
      condExp_of_stronglyMeasurable hsumX_meas.comap_le hsum_meas'.stronglyMeasurable hsum_int'
  have hmul_eq_sum :
      (fun ω ↦ (n : ℝ) * P[X i | MeasurableSpace.comap sumX inferInstance] ω) =ᵐ[P]
        sumX := by
    -- Replace the conditional expectation of the sum by the sum of the coordinate conditionals and
    -- then collapse the latter to `n` identical summands.
    calc
      (fun ω ↦ (n : ℝ) * P[X i | MeasurableSpace.comap sumX inferInstance] ω) =ᵐ[P]
          ∑ j : Fin n, P[X j | MeasurableSpace.comap sumX inferInstance] :=
        hcoords_sum.symm
      _ =ᵐ[P] P[∑ j : Fin n, X j | MeasurableSpace.comap sumX inferInstance] := hcond_sum'.symm
      _ =ᵐ[P] ∑ j : Fin n, X j := hcond_sum_self
      _ =ᵐ[P] sumX := hsum_fun_eq_ae.symm
  have hn_pos : 0 < n := lt_of_le_of_lt (Nat.zero_le i.1) i.2
  have hn_ne_zero : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn_pos)
  -- Divide the identity `n * P[X i | σ(sumX)] = sumX` by the nonzero scalar `n`.
  filter_upwards [hmul_eq_sum] with ω hω
  calc
    P[X i | MeasurableSpace.comap sumX inferInstance] ω =
        ((n : ℝ) * P[X i | MeasurableSpace.comap sumX inferInstance] ω) / n := by
      have hcancel :
          (P[X i | MeasurableSpace.comap sumX inferInstance] ω * (n : ℝ)) / n =
            P[X i | MeasurableSpace.comap sumX inferInstance] ω :=
        mul_div_cancel_right₀ _ hn_ne_zero
      simpa [mul_comm] using hcancel.symm
    _ = sumX ω / n := by rw [hω]
